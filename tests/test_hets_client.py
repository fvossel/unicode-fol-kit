"""Tests for the ``unicode_fol_kit.hets`` REST-against-Docker HETS binding.

Two tiers, mirroring ``tests/test_isabelle_runner_live.py``'s split between
runner-unit tests and the ``isabelle_live`` battery:

OFFLINE (default run, no server needed) — pure unit tests against
:mod:`unicode_fol_kit.hets.client` and :mod:`unicode_fol_kit.hets.docker`:
IRI percent-encoding, exact ``/prove`` JSON-body construction, goal
extraction from a canned response fixture (a real captured fragment),
``/translations`` XML parsing, and :func:`discover_hets_url`'s precedence —
all with the actual network probe monkeypatched away so these tests are
deterministic REGARDLESS of whether a real HETS container happens to be
running on localhost:8000 on the machine executing them (it may well be —
see the live tier below).

LIVE (``@pytest.mark.hets_live`` on ``TestHetsLive``, gated by
:func:`~unicode_fol_kit.hets.docker.hets_available` exactly the way
``test_isabelle_runner_live.py`` gates on ``isabelle_available()``) — runs
real HTTP calls against a real HETS server. Run them explicitly and
SERIALLY::

    pytest -m hets_live tests/test_hets_client.py

The everyday loop (``pytest -n auto -m "not isabelle_live"``) does not
exclude ``hets_live`` by name, but every test in ``TestHetsLive`` is also
individually gated by the module-level ``skipif`` below, so a machine with
no reachable HETS server (the common case) just skips them instead of
failing — never a silent pass, always a visible "skipped: <reason>" line
naming what was missing, matching this kit's "loud failures, never a silent
skip" convention (the skip reason itself is the loud part: it says exactly
what to start / where to point ``$UFK_HETS_URL``).
"""

import json

import pytest

from unicode_fol_kit.atp.protocol import BackendUnavailable
from unicode_fol_kit.hets.client import (
    HetsClient, _encode_iri, _extract_goal_objects, _normalize_goal,
)
from unicode_fol_kit.hets import docker as hets_docker
from unicode_fol_kit.hets.docker import discover_hets_url, hets_available


# =============================================================================
# OFFLINE: unit tests, no network.
# =============================================================================

# --- IRI percent-encoding ---------------------------------------------------

def test_encode_iri_percent_encodes_slashes():
    # Verified wire fact: HETS's IRI convention encodes path separators too
    # (safe="" ), not just the usual reserved characters — the stdlib
    # urllib.parse.quote default (safe="/") would leave slashes bare and
    # every endpoint that takes an iri would 404 against a real server.
    stored_path = "/tmp/hetsUserFolder_zvNMsf/probe.casl"
    assert _encode_iri(stored_path) == "%2Ftmp%2FhetsUserFolder_zvNMsf%2Fprobe.casl"


def test_encode_iri_round_trips_through_unquote():
    import urllib.parse
    stored_path = "/tmp/hetsUserFolder_zvNMsf/probe.casl"
    assert urllib.parse.unquote(_encode_iri(stored_path)) == stored_path


# --- /prove JSON body construction ------------------------------------------
#
# _prove_body returns the FULL request envelope (not just the inner goal
# dict) — {"format":"json","goals":[<goal>]} exactly as the verified wire
# protocol specifies — so callers (and tests) never juggle a separate
# wrap-in-envelope step.

def test_prove_body_omits_translation_when_none():
    body = HetsClient._prove_body("Test", reasoner="SPASS", translation=None,
                                   time_limit=10)
    assert body == {
        "format": "json",
        "goals": [{
            "node": "Test",
            "reasonerConfiguration": {"timeLimit": 10, "reasoner": "SPASS"},
        }],
    }
    assert "translation" not in body["goals"][0]


def test_prove_body_includes_translation_when_given():
    body = HetsClient._prove_body("Test", reasoner="darwin",
                                   translation="CASL2TPTP_FOF", time_limit=30)
    assert body == {
        "format": "json",
        "goals": [{
            "node": "Test",
            "translation": "CASL2TPTP_FOF",
            "reasonerConfiguration": {"timeLimit": 30, "reasoner": "darwin"},
        }],
    }


def test_prove_body_omits_reasoner_when_none():
    # HetsClient.prove() defaults reasoner=None (let HETS pick), unlike
    # consistency_check()'s reasoner="darwin-non-fd" default — the body
    # builder itself must honor whatever it is handed either way.
    body = HetsClient._prove_body("Test", reasoner=None, translation=None,
                                   time_limit=10)
    assert body == {
        "format": "json",
        "goals": [{"node": "Test", "reasonerConfiguration": {"timeLimit": 10}}],
    }


def test_prove_body_is_json_serializable_and_round_trips():
    # Must be JSON-serializable as-is (this is exactly what _run_goal_endpoint
    # hands to json.dumps before POSTing).
    body = HetsClient._prove_body("Test", reasoner="SPASS", translation=None,
                                   time_limit=10)
    assert json.loads(json.dumps(body)) == body


# --- goal extraction from a canned response fixture -------------------------

# A real captured fragment of a /prove response (see the task's verified wire
# protocol notes) — deliberately kept EXACTLY as captured, including the
# trailing "\n" inside "result" and the double-nested ProofGoal list, since
# that double-nesting (list of lists) is precisely the shape the recursive
# walk in _extract_goal_objects must not choke on.
_PROVE_RESPONSE_FIXTURE = {
    "dgraph": {
        "DGraph": {
            "DGNode": [{
                "name": "Test",
                "ProofGoal": [[{
                    "name": "Ax3",
                    "result": "Proved\n",
                    "details": "",
                    "used_prover": {"identifier": "SPASS", "name": "SPASS"},
                    "used_translation": "CASL2TPTP_FOF",
                    "tactic_script": {"time_limit": 10, "extra_options": []},
                    "proof_tree": "",
                    "used_time": {"seconds": "0.02"},
                    "used_axioms": [],
                    "prover_output": "...SPASS-STOP...",
                }]],
            }],
        },
    },
}


def test_extract_goal_objects_finds_the_nested_goal():
    goals = _extract_goal_objects(_PROVE_RESPONSE_FIXTURE)
    assert len(goals) == 1
    assert goals[0]["name"] == "Ax3"
    assert goals[0]["result"] == "Proved\n"          # raw, not yet stripped
    assert goals[0]["used_prover"] == {"identifier": "SPASS", "name": "SPASS"}


def test_extract_goal_objects_walk_is_order_and_depth_agnostic():
    # Wrap the same goal one extra list/dict layer deeper (simulating a HETS
    # response shape that nests differently than the fixture above) — the
    # structural (has "result" AND "used_prover") walk must still find it,
    # since this client explicitly does not hard-code a JSON path.
    goal = _PROVE_RESPONSE_FIXTURE["dgraph"]["DGraph"]["DGNode"][0]["ProofGoal"][0][0]
    wrapped = {"outer": {"deeper": [{"still_deeper": [goal]}]}}
    goals = _extract_goal_objects(wrapped)
    assert len(goals) == 1
    assert goals[0] is goal


def test_extract_goal_objects_ignores_non_goal_dicts():
    # A dict with only ONE of the two signature keys is metadata, not a goal
    # — e.g. "used_prover" alone (a goal's own sub-object) must not itself be
    # picked up as a second, spurious goal.
    goal = _PROVE_RESPONSE_FIXTURE["dgraph"]["DGraph"]["DGNode"][0]["ProofGoal"][0][0]
    goals = _extract_goal_objects({"a": {"used_prover": {"identifier": "SPASS"}},
                                    "b": goal})
    assert len(goals) == 1
    assert goals[0]["name"] == "Ax3"


def test_normalize_goal_strips_result_whitespace_and_projects_fields():
    raw = _PROVE_RESPONSE_FIXTURE["dgraph"]["DGraph"]["DGNode"][0]["ProofGoal"][0][0]
    normalized = _normalize_goal(raw)
    assert normalized == {
        "name": "Ax3",
        "result": "Proved",                              # stripped
        "used_prover": {"identifier": "SPASS", "name": "SPASS"},
        "used_translation": "CASL2TPTP_FOF",
        "prover_output": "...SPASS-STOP...",
        "used_time": {"seconds": "0.02"},
        "tactic_script": {"time_limit": 10, "extra_options": []},
    }
    # used_axioms/details/proof_tree are NOT in the projected field set —
    # confirms _normalize_goal really projects onto _GOAL_FIELDS rather than
    # passing the raw dict through.
    assert "used_axioms" not in normalized
    assert "details" not in normalized


def test_normalize_goal_defaults_missing_fields_to_none():
    normalized = _normalize_goal({"name": "Ax1", "result": "Open\n",
                                   "used_prover": {"identifier": "eprover"}})
    assert normalized["result"] == "Open"
    assert normalized["used_translation"] is None
    assert normalized["prover_output"] is None


def test_prove_end_to_end_against_monkeypatched_transport(monkeypatch):
    # Exercises HetsClient.prove() all the way through: body construction,
    # IRI encoding in the request path, JSON parsing, and goal extraction —
    # with the actual HTTP call replaced so no server is needed.
    seen = {}

    def fake_post(self, path, data, content_type):
        seen["path"] = path
        seen["data"] = json.loads(data.decode("utf-8"))
        seen["content_type"] = content_type
        return json.dumps(_PROVE_RESPONSE_FIXTURE)

    monkeypatch.setattr(HetsClient, "_post", fake_post)
    client = HetsClient("http://localhost:8000")
    goals = client.prove("/tmp/x/probe.casl", "Test", reasoner="SPASS")

    assert seen["path"] == f"/prove/{_encode_iri('/tmp/x/probe.casl')}"
    assert seen["content_type"] == "application/json"
    assert seen["data"] == {
        "format": "json",
        "goals": [{"node": "Test",
                    "reasonerConfiguration": {"timeLimit": 10, "reasoner": "SPASS"}}],
    }
    assert len(goals) == 1
    assert goals[0]["result"] == "Proved"


# --- error-body / bad-JSON handling -----------------------------------------

def test_get_raises_runtime_error_on_hets_error_body(monkeypatch):
    def fake_urlopen(req, timeout=None):
        class _Resp:
            status = 200
            def read(self_inner):
                return b"*** Error:\nfile does not exist: /tmp/nope.casl"
            def __enter__(self_inner):
                return self_inner
            def __exit__(self_inner, *a):
                return False
        return _Resp()

    import urllib.request
    monkeypatch.setattr(urllib.request, "urlopen", fake_urlopen)
    client = HetsClient("http://localhost:8000")
    with pytest.raises(RuntimeError, match=r"\*\*\* Error"):
        client.dg("/tmp/nope.casl")


def test_dg_raises_runtime_error_on_invalid_json(monkeypatch):
    def fake_get(self, path):
        return "not json at all"

    monkeypatch.setattr(HetsClient, "_get", fake_get)
    client = HetsClient("http://localhost:8000")
    with pytest.raises(RuntimeError, match="not valid JSON"):
        client.dg("/tmp/x/probe.casl")


# --- /translations XML parsing ----------------------------------------------

# The verified wire-protocol fixture string, composed comorphisms included.
_TRANSLATIONS_XML_FIXTURE = (
    "<Translations><translations>"
    "<li>CASL2SoftFOL</li>"
    "<li>CASL2NNF:CASL2SoftFOL</li>"
    "<li>CASL2PCFOL</li>"
    "</translations></Translations>"
)


def test_translations_parses_li_entries_from_xml(monkeypatch):
    monkeypatch.setattr(HetsClient, "_get", lambda self, path: _TRANSLATIONS_XML_FIXTURE)
    client = HetsClient("http://localhost:8000")
    names = client.translations("/tmp/x/probe.casl")
    assert names == ["CASL2SoftFOL", "CASL2NNF:CASL2SoftFOL", "CASL2PCFOL"]


def test_translations_raises_runtime_error_on_malformed_xml(monkeypatch):
    monkeypatch.setattr(HetsClient, "_get", lambda self, path: "<not><valid")
    client = HetsClient("http://localhost:8000")
    with pytest.raises(RuntimeError, match="not valid XML"):
        client.translations("/tmp/x/probe.casl")


# =============================================================================
# OFFLINE: discovery precedence (docker.py), network probing monkeypatched.
# =============================================================================

def test_discover_prefers_healthy_env_var(monkeypatch):
    monkeypatch.setenv("UFK_HETS_URL", "http://example-hets:9999")
    monkeypatch.setattr(hets_docker, "_probe_health",
                        lambda url, timeout=hets_docker._HEALTH_TIMEOUT: url == "http://example-hets:9999")
    url, container = discover_hets_url(start_container=False)
    assert url == "http://example-hets:9999"
    assert container is None


def test_discover_raises_on_unhealthy_env_var_without_falling_through(monkeypatch):
    # Even though localhost WOULD be healthy here, an explicitly-set but dead
    # $UFK_HETS_URL must raise rather than silently trying localhost next —
    # the caller pointed at a specific server and deserves to know it's down.
    monkeypatch.setenv("UFK_HETS_URL", "http://dead-hets:9999")
    monkeypatch.setattr(hets_docker, "_probe_health",
                        lambda url, timeout=hets_docker._HEALTH_TIMEOUT: url != "http://dead-hets:9999")
    with pytest.raises(BackendUnavailable, match="UFK_HETS_URL"):
        discover_hets_url(start_container=False)


def test_discover_falls_back_to_localhost_when_no_env_var(monkeypatch):
    monkeypatch.delenv("UFK_HETS_URL", raising=False)
    monkeypatch.setattr(hets_docker, "_probe_health",
                        lambda url, timeout=hets_docker._HEALTH_TIMEOUT: url == "http://localhost:8000")
    url, container = discover_hets_url(start_container=False)
    assert url == "http://localhost:8000"
    assert container is None


def test_discover_raises_backend_unavailable_when_nothing_reachable(monkeypatch):
    # Deterministic regardless of whether a real HETS happens to be running
    # on this machine's localhost:8000 (it may well be, per the live tier) —
    # _probe_health is monkeypatched to always report unhealthy, so this
    # exercises the pure "nothing reachable" branch without depending on
    # actual machine state.
    monkeypatch.delenv("UFK_HETS_URL", raising=False)
    monkeypatch.setattr(hets_docker, "_probe_health", lambda url, timeout=hets_docker._HEALTH_TIMEOUT: False)
    with pytest.raises(BackendUnavailable) as excinfo:
        discover_hets_url(start_container=False)
    msg = str(excinfo.value)
    # Loud failure, not a skip: the message must name every option tried.
    assert "UFK_HETS_URL" in msg
    assert "localhost:8000" in msg
    assert "docker" in msg.lower()


def test_hets_available_is_false_when_nothing_reachable(monkeypatch):
    monkeypatch.delenv("UFK_HETS_URL", raising=False)
    monkeypatch.setattr(hets_docker, "_probe_health", lambda url, timeout=hets_docker._HEALTH_TIMEOUT: False)
    assert hets_available() is False


def test_hets_available_is_true_when_localhost_reachable(monkeypatch):
    monkeypatch.delenv("UFK_HETS_URL", raising=False)
    monkeypatch.setattr(hets_docker, "_probe_health",
                        lambda url, timeout=hets_docker._HEALTH_TIMEOUT: url == "http://localhost:8000")
    assert hets_available() is True


def test_discover_never_starts_a_container_when_start_container_false(monkeypatch):
    # hets_available()'s docstring promises this never has the side effect of
    # spinning up Docker; verify by making HetsContainer.start() itself raise
    # if it is ever called while start_container=False.
    monkeypatch.delenv("UFK_HETS_URL", raising=False)
    monkeypatch.setattr(hets_docker, "_probe_health", lambda url, timeout=hets_docker._HEALTH_TIMEOUT: False)

    def fail(self):
        raise AssertionError("HetsContainer.start() must not be called")

    monkeypatch.setattr(hets_docker.HetsContainer, "start", fail)
    with pytest.raises(BackendUnavailable):
        discover_hets_url(start_container=False)


# --- HetsContainer stderr classification (pure string matching, no docker) --

@pytest.mark.parametrize("stderr", [
    "Cannot connect to the Docker daemon at unix:///var/run/docker.sock. "
    "Is the docker daemon running?",
    "error during connect: this error may indicate that the docker daemon "
    "is not running: open //./pipe/dockerDesktopLinuxEngine",
])
def test_daemon_down_regex_matches_known_docker_stderr(stderr):
    assert hets_docker._DAEMON_DOWN_RE.search(stderr)


@pytest.mark.parametrize("stderr", [
    "pull access denied for spechub2/hets, repository does not exist or "
    "may require 'docker login'",
    "manifest unknown",
])
def test_image_missing_regex_matches_known_docker_stderr(stderr):
    assert hets_docker._IMAGE_MISSING_RE.search(stderr)


def test_daemon_down_regex_does_not_match_unrelated_stderr():
    assert not hets_docker._DAEMON_DOWN_RE.search("docker: 'run' requires at least 1 argument")


# =============================================================================
# LIVE: real HTTP calls against a real HETS server.
# =============================================================================

# The exact CASL spec given in the task's verified wire-protocol notes —
# forall x. P(x) => Q(x), P(c) classically entail Q(c), so Q(c) %implied is
# a genuine theorem (universal instantiation + modus ponens).
CASL_TEST_SPEC = """spec Test =
  sort Thing
  preds P : Thing;
        Q : Thing
  op c : Thing
  . forall x : Thing . (P(x) => Q(x))
  . P(c)
  . Q(c) %implied
end
"""

# A second spec whose implied goal does NOT follow: P(c) alone says nothing
# about Q, so the one-element model {c} with P(c) true and Q(c) false is a
# genuine countermodel — Q(c) is NOT a theorem here.
CASL_UNPROVABLE_SPEC = """spec Unprovable =
  sort Thing
  preds P : Thing;
        Q : Thing
  op c : Thing
  . P(c)
  . Q(c) %implied
end
"""


@pytest.mark.hets_live
@pytest.mark.skipif(
    not hets_available(),
    reason="no reachable HETS server (set $UFK_HETS_URL, or run "
           "`docker run -d --rm -p 8000:8000 spechub2/hets:latest`)")
class TestHetsLive:
    """Real calls against a real HETS server. Run serially: -m hets_live (no -n)."""

    @pytest.fixture(scope="class")
    def hets(self):
        url, container = discover_hets_url(start_container=False)
        client = HetsClient(url)
        test_iri = client.upload(CASL_TEST_SPEC, "ufk_test.casl")
        unprovable_iri = client.upload(CASL_UNPROVABLE_SPEC, "ufk_unprovable.casl")
        try:
            yield {"client": client, "test_iri": test_iri,
                   "unprovable_iri": unprovable_iri}
        finally:
            if container is not None:
                container.stop()

    def test_version_reports_hets(self, hets):
        assert "Heterogeneous Tool Set" in hets["client"].version()

    def test_upload_and_dg_report_the_test_node(self, hets):
        dgraph = hets["client"].dg(hets["test_iri"])["DGraph"]
        assert dgraph["libname"]
        nodes = {n["name"]: n for n in dgraph["DGNode"]}
        assert "Test" in nodes
        assert nodes["Test"]["logic"] == "CASL"

    def test_translations_lists_casl2softfol(self, hets):
        assert "CASL2SoftFOL" in hets["client"].translations(hets["test_iri"])

    def test_prove_with_spass_proves_the_implied_goal(self, hets):
        goals = hets["client"].prove(hets["test_iri"], "Test", reasoner="SPASS")
        assert len(goals) == 1
        assert goals[0]["result"] == "Proved"
        assert goals[0]["used_translation"] == "CASL2TPTP_FOF"

    def test_prove_with_darwin_proves_the_implied_goal(self, hets):
        goals = hets["client"].prove(hets["test_iri"], "Test", reasoner="darwin")
        assert len(goals) == 1
        assert goals[0]["result"] == "Proved"

    def test_prove_with_darwin_non_fd_disproves_the_unprovable_goal(self, hets):
        goals = hets["client"].prove(hets["unprovable_iri"], "Unprovable",
                                      reasoner="darwin-non-fd")
        assert len(goals) == 1
        assert goals[0]["result"] == "Disproved"

    def test_consistency_check_on_test_is_consistent(self, hets):
        goals = hets["client"].consistency_check(hets["test_iri"], "Test",
                                                   reasoner="darwin-non-fd")
        assert len(goals) == 1
        assert goals[0]["result"] == "Consistent"


# ---------------------------------------------------------------------------
# Adversarial-review regressions (2026-08-12)
# ---------------------------------------------------------------------------

class TestReviewRegressions:
    def test_upload_percent_encodes_the_filename(self, monkeypatch):
        """An unencoded '#' was parsed as a URL fragment and silently
        truncated the stored filename (live-confirmed). Both path segments
        are now percent-encoded like every IRI."""
        client = HetsClient("http://fake:8000")
        calls = {}
        monkeypatch.setattr(client, "_get", lambda path: "/tmp/hetsUserFolder_x")
        def _post(path, data, content_type):
            calls["path"] = path
            return "/tmp/hetsUserFolder_x/probe%23hash.casl"
        monkeypatch.setattr(client, "_post", _post)
        client.upload("spec X = end", "probe#hash.casl")
        assert calls["path"] == "/uploadFile/hetsUserFolder_x/probe%23hash.casl"

    def test_nothing_to_prove_is_the_legitimate_empty_goal_list(self, monkeypatch):
        """A node with zero %implied goals answers the plain-text 'nothing
        to prove' (not JSON) — that is zero attempted goals, not a protocol
        error (live-confirmed wire shape)."""
        client = HetsClient("http://fake:8000")
        monkeypatch.setattr(client, "_post",
                            lambda path, data, content_type: "nothing to prove")
        assert client.prove("/tmp/x.casl", "Test") == []

    def test_http_client_exceptions_become_runtime_errors(self, monkeypatch):
        """http.client.InvalidURL (a sibling of URLError, previously leaking
        raw) now honours the RuntimeError contract."""
        import http.client as _hc

        client = HetsClient("http://fake:8000")
        def _boom(*a, **kw):
            raise _hc.InvalidURL("URL can't contain control characters")
        monkeypatch.setattr("urllib.request.urlopen", _boom)
        with pytest.raises(RuntimeError, match="InvalidURL"):
            client.version()
