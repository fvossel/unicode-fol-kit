"""Tests for solver-version provenance (K1): ``Verdict.solver_version``,
``ProverBackend.solver_version()``, and the memoized lookups that back it.

Hand-checked contracts, each pinned to why the expected value is correct:

* ``Verdict.solver_version`` defaults to ``None`` and round-trips through
  ``to_dict()`` — the kit's own internal backends (Z3/tableau/resolution/
  modelfinder/QML/…) never set it, since they have no external tool version
  to report (see ``ProverBackend.solver_version``'s base-class docstring).
* ``atp.protocol._binary_version`` — the shared ``<binary> --version``
  primitive Vampire/Prover9/E/Zipperposition all call through — spawns a
  subprocess AT MOST ONCE per ``(command, use_wsl)`` pair for the life of
  the process, exactly mirroring ``atp.eprover_backend._DISCOVERY_CACHE``'s
  own memoization test (``test_discovery_miss_is_cached_and_unavailable``);
  a FAILED lookup is cached too (never retried).
* Each external backend's own ``solver_version()`` override is wired to the
  right ``(binary, use_wsl)``/URL/package, and ``decide()`` reports the
  SAME string in ``Verdict.solver_version`` (stubbed subprocess/HTTP calls,
  since most of these tools are not installed everywhere).
* Where a real tool genuinely IS reachable in this environment (WSL
  ``vampire``/``eprover``, the pip ``cvc5`` package), a LIVE test asserts
  the real version string is non-empty and lands in a real ``decide()``'s
  ``Verdict`` unchanged — the strongest evidence this suite can offer,
  exactly like ``test_eprover_zipperposition.py``'s own live classes.
* The HETS image is pinned by DIGEST, not a movable ``:latest`` tag — see
  ``unicode_fol_kit/hets/docker.py`` for how the digest was verified to be
  the exact build (HETS 0.108.0) the module docstring already claims.
"""

import subprocess

import pytest

from unicode_fol_kit import MSFLParser, Verdict
from unicode_fol_kit import hets as hets_pkg
from unicode_fol_kit.atp import cvc5_backend as cvc5b
from unicode_fol_kit.atp import eprover_backend as eb
from unicode_fol_kit.atp import hets_backend as hb
from unicode_fol_kit.atp import protocol as proto
from unicode_fol_kit.atp.protocol import ProverBackend, get_backend
from unicode_fol_kit.hets import docker as hets_docker

_PARSE = MSFLParser().parse
_PREMISES = [_PARSE("P(alice)"), _PARSE("∀x (P(x) → Q(x))")]
_GOAL = _PARSE("Q(alice)")


# ---------------------------------------------------------------------------
# Verdict / ProverBackend base contract
# ---------------------------------------------------------------------------

def test_verdict_solver_version_defaults_to_none_and_round_trips():
    v = Verdict("proved", "z3")
    assert v.solver_version is None
    assert v.to_dict()["solver_version"] is None

    v2 = Verdict("proved", "vampire", solver_version="Vampire 5.0.1")
    assert v2.solver_version == "Vampire 5.0.1"
    assert v2.to_dict()["solver_version"] == "Vampire 5.0.1"


def test_internal_backends_never_report_a_solver_version():
    """The kit's own calculi/searches have no external tool to version —
    ProverBackend's base implementation returns None, and none of these five
    override it (see the base docstring's explicit exclusion list)."""
    for name in ("z3", "tableau", "resolution", "modelfinder",
                 "modal-tableau", "qml"):
        assert get_backend(name).solver_version() is None


def test_base_class_default_is_none_for_a_fresh_backend():
    class _Bare(ProverBackend):
        name = "bare-for-test"
        logics = frozenset({"fol"})

        def available(self):
            return True

        def decide(self, formula, premises=(), timeout=10000, **options):
            raise AssertionError("not exercised")

    assert _Bare().solver_version() is None    # inherited, not overridden


# ---------------------------------------------------------------------------
# atp.protocol._binary_version: the shared subprocess-spawning primitive
# ---------------------------------------------------------------------------

class _FakeRun:
    """``subprocess.run`` stand-in: canned (stdout, stderr) per exact argv,
    with a call counter so memoization can be checked directly (mirrors
    ``atp.eprover_backend``'s own discovery-cache tests)."""

    def __init__(self, canned: dict):
        self.canned = canned
        self.calls = []

    def __call__(self, cmd, capture_output=True, text=True, timeout=None):
        self.calls.append(tuple(cmd))
        key = tuple(cmd)
        if key not in self.canned:
            raise AssertionError(f"unexpected subprocess.run call: {cmd}")
        action = self.canned[key]
        if isinstance(action, Exception):
            raise action
        if len(action) == 3:
            stdout, stderr, returncode = action
        else:
            stdout, stderr = action
            returncode = 0
        return subprocess.CompletedProcess(cmd, returncode, stdout=stdout, stderr=stderr)


@pytest.fixture()
def fresh_version_cache(monkeypatch):
    """Reset atp.protocol's process-local version cache for test isolation
    (mirrors test_eprover_zipperposition.py's ``monkeypatch.setattr(eb,
    "_DISCOVERY_CACHE", {})`` — a different cache answering a different
    question, see _binary_version's own docstring for why they are kept
    separate, but the same "start every test from empty" discipline)."""
    monkeypatch.setattr(proto, "_VERSION_CACHE", {})


def test_binary_version_reads_first_stdout_line_and_strips_it(fresh_version_cache, monkeypatch):
    fake = _FakeRun({("myprover", "--version"):
                     ("MyProver 1.2.3 (build xyz)\nsome other line\n", "")})
    monkeypatch.setattr(subprocess, "run", fake)
    assert proto._binary_version("myprover", False) == "MyProver 1.2.3 (build xyz)"
    assert len(fake.calls) == 1


def test_binary_version_falls_back_to_stderr_when_stdout_is_blank(fresh_version_cache, monkeypatch):
    fake = _FakeRun({("noisytool", "--version"): ("", "NoisyTool 0.9\n")})
    monkeypatch.setattr(subprocess, "run", fake)
    assert proto._binary_version("noisytool", False) == "NoisyTool 0.9"


def test_binary_version_is_memoized_per_command_use_wsl_pair(fresh_version_cache, monkeypatch):
    """Called N times for the SAME (command, use_wsl) key -> exactly ONE
    subprocess spawn (item 5's "never spawn a subprocess per decide() call
    after the first"); a DIFFERENT use_wsl for the SAME command name is a
    genuinely different binary and gets its own probe."""
    fake = _FakeRun({
        ("memoprover", "--version"): ("Memo 1.0\n", ""),
        ("wsl.exe", "memoprover", "--version"): ("Memo 1.0 (linux)\n", ""),
    })
    monkeypatch.setattr(subprocess, "run", fake)

    for _ in range(5):
        assert proto._binary_version("memoprover", False) == "Memo 1.0"
    assert len(fake.calls) == 1                       # 5 calls, 1 real spawn

    assert proto._binary_version("memoprover", True) == "Memo 1.0 (linux)"
    assert len(fake.calls) == 2                        # a distinct key, one more spawn
    assert proto._binary_version("memoprover", True) == "Memo 1.0 (linux)"
    assert len(fake.calls) == 2                        # and THAT is now memoized too


def test_binary_version_missing_binary_returns_none_and_is_not_retried(fresh_version_cache, monkeypatch):
    fake = _FakeRun({("ghost", "--version"): FileNotFoundError("no such file")})
    monkeypatch.setattr(subprocess, "run", fake)
    assert proto._binary_version("ghost", False) is None
    assert proto._binary_version("ghost", False) is None      # still None
    assert len(fake.calls) == 1                                 # a MISS is cached too


def test_binary_version_timeout_returns_none(fresh_version_cache, monkeypatch):
    fake = _FakeRun({("slowtool", "--version"):
                     subprocess.TimeoutExpired(cmd="slowtool", timeout=10)})
    monkeypatch.setattr(subprocess, "run", fake)
    assert proto._binary_version("slowtool", False) is None


def test_binary_version_nonzero_exit_returns_none_even_with_text(
        fresh_version_cache, monkeypatch):
    """review-confirmed regression: a tool that does not recognize
    ``--version`` commonly prints an error/usage line and exits non-zero
    rather than printing nothing — that text must NOT be accepted as a
    version string (it is not one), so a non-zero returncode must force
    None regardless of how plausible stdout/stderr looks."""
    fake = _FakeRun({("fake-prover9", "--version"):
                     ("", "prover9: unrecognized option '--version'\n"
                          "Usage: prover9 -f <file>\n", 1)})
    monkeypatch.setattr(subprocess, "run", fake)
    assert proto._binary_version("fake-prover9", False) is None
    assert len(fake.calls) == 1
    # and the miss is cached like any other failure
    assert proto._binary_version("fake-prover9", False) is None
    assert len(fake.calls) == 1


def test_binary_version_decode_error_returns_none_instead_of_raising(
        fresh_version_cache, monkeypatch):
    """review-confirmed regression: with ``text=True``,
    ``subprocess.run`` decodes the child's stdout/stderr under the
    process's default text encoding and raises ``UnicodeDecodeError`` (a
    ``ValueError`` subclass) when a tool's ``--version`` banner contains
    bytes that are not valid under it — e.g. a build that writes its
    banner in a locale-specific 8-bit encoding. Before this fix that
    exception propagated straight out of ``_binary_version`` and then out
    of ``decide()`` (see the decide()-level regression tests below),
    contradicting this function's own "nothing here ever raises" contract
    -- it must degrade to None exactly like any other lookup failure."""
    fake = _FakeRun({("fake-tool", "--version"):
                     UnicodeDecodeError("utf-8", b"\xff\xfe", 0, 1,
                                        "invalid start byte")})
    monkeypatch.setattr(subprocess, "run", fake)
    assert proto._binary_version("fake-tool", False) is None
    assert len(fake.calls) == 1
    # and the miss is cached like any other failure
    assert proto._binary_version("fake-tool", False) is None
    assert len(fake.calls) == 1


# ---------------------------------------------------------------------------
# Prover9Backend / VampireBackend wiring (offline: no real binary needed)
# ---------------------------------------------------------------------------

def test_prover9_solver_version_wired_to_binary_version(fresh_version_cache, monkeypatch):
    monkeypatch.setenv("UFK_PROVER9", "fake-prover9")
    fake = _FakeRun({("fake-prover9", "--version"): ("Prover9 (64) 2009-11A\n", "")})
    monkeypatch.setattr(subprocess, "run", fake)
    assert get_backend("prover9").solver_version() == "Prover9 (64) 2009-11A"


def test_prover9_solver_version_none_without_a_binary(fresh_version_cache, monkeypatch):
    monkeypatch.delenv("UFK_PROVER9", raising=False)
    monkeypatch.setattr(proto.shutil, "which", lambda name: None)
    assert get_backend("prover9").solver_version() is None


def test_prover9_decide_carries_solver_version_into_the_verdict(fresh_version_cache, monkeypatch):
    """Stub subprocess.run's version banner AND check_logical_entailment
    itself (no real prover9 binary in this environment) — the fixed
    version string must land UNCHANGED in Verdict.solver_version and in
    Verdict.to_dict()['solver_version'] (test_oracle item 1)."""
    monkeypatch.setenv("UFK_PROVER9", "fake-prover9")
    fake = _FakeRun({("fake-prover9", "--version"): ("Prover9 (64) 2009-11A\n", "")})
    monkeypatch.setattr(subprocess, "run", fake)
    import unicode_fol_kit.atp.prover9_entailment as p9
    monkeypatch.setattr(p9, "check_logical_entailment", lambda *a, **kw: True)

    v = get_backend("prover9").decide(_GOAL, _PREMISES)
    assert v.status == "proved"
    assert v.solver_version == "Prover9 (64) 2009-11A"
    assert v.to_dict()["solver_version"] == "Prover9 (64) 2009-11A"
    assert len(fake.calls) == 1


def test_prover9_decide_survives_a_version_probe_decode_error(fresh_version_cache, monkeypatch):
    """Same review-confirmed regression as Vampire's/E's, for Prover9Backend's
    own ``solver_version = _binary_version(path, False)`` call right before
    its try/except: a ``UnicodeDecodeError`` out of the ``--version`` probe
    must not propagate out of ``decide()``."""
    monkeypatch.setenv("UFK_PROVER9", "fake-prover9-b")
    fake = _FakeRun({("fake-prover9-b", "--version"):
                     UnicodeDecodeError("utf-8", b"\xff\xfe", 0, 1,
                                        "invalid start byte")})
    monkeypatch.setattr(subprocess, "run", fake)
    import unicode_fol_kit.atp.prover9_entailment as p9
    monkeypatch.setattr(p9, "check_logical_entailment", lambda *a, **kw: True)

    v = get_backend("prover9").decide(_GOAL, _PREMISES)   # must not raise
    assert v.status == "proved"
    assert v.solver_version is None


def test_vampire_solver_version_wired_to_binary_version_and_wsl_flag(fresh_version_cache, monkeypatch):
    monkeypatch.setenv("UFK_VAMPIRE", "fake-vampire")
    monkeypatch.setenv("UFK_VAMPIRE_WSL", "1")
    fake = _FakeRun({("wsl.exe", "fake-vampire", "--version"):
                     ("Vampire 4.8 (commit deadbeef)\n", "")})
    monkeypatch.setattr(subprocess, "run", fake)
    assert get_backend("vampire").solver_version() == "Vampire 4.8 (commit deadbeef)"


def test_vampire_decide_carries_solver_version_into_the_verdict(fresh_version_cache, monkeypatch):
    monkeypatch.setenv("UFK_VAMPIRE", "fake-vampire2")
    monkeypatch.delenv("UFK_VAMPIRE_WSL", raising=False)
    fake = _FakeRun({("fake-vampire2", "--version"): ("Vampire 4.8\n", "")})
    monkeypatch.setattr(subprocess, "run", fake)

    canned = {"status": "proved", "reason": None, "szs_status": "Theorem",
              "derivation": None}
    monkeypatch.setattr(
        "unicode_fol_kit.atp.vampire_entailment.check_entailment_vampire_detailed",
        lambda *a, **kw: canned)

    v = get_backend("vampire").decide(_GOAL, _PREMISES)
    assert v.status == "proved"
    assert v.solver_version == "Vampire 4.8"
    assert v.to_dict()["solver_version"] == "Vampire 4.8"


def test_vampire_decide_survives_a_version_probe_decode_error(
        fresh_version_cache, monkeypatch):
    """review-confirmed regression, reproduced end-to-end: before the
    ``_binary_version`` fix above, a ``UnicodeDecodeError`` out of the
    ``--version`` subprocess call propagated straight out of
    ``VampireBackend.decide()`` (the lookup runs BEFORE decide()'s own
    try/except), crashing a call that should have produced a definitive
    Verdict. A genuinely valid entailment must still come back PROVED,
    with solver_version degraded to None rather than the call raising."""
    monkeypatch.setenv("UFK_VAMPIRE", "fake-vampire3")
    monkeypatch.delenv("UFK_VAMPIRE_WSL", raising=False)
    fake = _FakeRun({("fake-vampire3", "--version"):
                     UnicodeDecodeError("utf-8", b"\xff\xfe", 0, 1,
                                        "invalid start byte")})
    monkeypatch.setattr(subprocess, "run", fake)

    canned = {"status": "proved", "reason": None, "szs_status": "Theorem",
              "derivation": None}
    monkeypatch.setattr(
        "unicode_fol_kit.atp.vampire_entailment.check_entailment_vampire_detailed",
        lambda *a, **kw: canned)

    v = get_backend("vampire").decide(_GOAL, _PREMISES)   # must not raise
    assert v.status == "proved"
    assert v.solver_version is None


# ---------------------------------------------------------------------------
# E / Zipperposition (_TptpSzsBackend, atp.eprover_backend)
# ---------------------------------------------------------------------------

@pytest.fixture()
def fresh_discovery_and_version_caches(monkeypatch):
    monkeypatch.setattr(eb, "_DISCOVERY_CACHE", {})
    monkeypatch.setattr(proto, "_VERSION_CACHE", {})


def test_eprover_solver_version_wired_through_discover(
        fresh_discovery_and_version_caches, monkeypatch):
    monkeypatch.setenv("UFK_EPROVER_CMD", "fake-eprover")
    fake = _FakeRun({("fake-eprover", "--version"): ("E 3.5.1 Countess Grey\n", "")})
    monkeypatch.setattr(subprocess, "run", fake)
    assert get_backend("eprover").solver_version() == "E 3.5.1 Countess Grey"


def test_zipperposition_solver_version_none_without_a_binary(
        fresh_discovery_and_version_caches, monkeypatch):
    monkeypatch.delenv("UFK_ZIPPERPOSITION_CMD", raising=False)
    monkeypatch.setattr(eb.shutil, "which", lambda name: None)

    def _no_wsl(*a, **kw):
        raise OSError("no wsl")
    monkeypatch.setattr(eb.subprocess, "run", _no_wsl)
    assert get_backend("zipperposition").solver_version() is None


def test_eprover_decide_carries_solver_version_into_the_verdict(
        fresh_discovery_and_version_caches, monkeypatch):
    monkeypatch.setenv("UFK_EPROVER_CMD", "fake-eprover2")
    fake = _FakeRun({("fake-eprover2", "--version"): ("E 3.5.1 Countess Grey\n", "")})
    monkeypatch.setattr(subprocess, "run", fake)
    monkeypatch.setattr(
        eb, "_run_tptp_prover",
        lambda problem, command, args, use_wsl, timeout_s:
            ("# SZS status Theorem\n", False))

    v = get_backend("eprover").decide(_GOAL, _PREMISES)
    assert v.status == "proved"
    assert v.solver_version == "E 3.5.1 Countess Grey"
    assert v.to_dict()["solver_version"] == "E 3.5.1 Countess Grey"


def test_eprover_decide_survives_a_version_probe_decode_error(
        fresh_discovery_and_version_caches, monkeypatch):
    """Same review-confirmed regression as Vampire's, for the shared
    ``_TptpSzsBackend.decide()`` path E/Zipperposition go through: a
    ``UnicodeDecodeError`` out of the ``--version`` probe must not
    propagate out of ``decide()``."""
    monkeypatch.setenv("UFK_EPROVER_CMD", "fake-eprover4")
    fake = _FakeRun({("fake-eprover4", "--version"):
                     UnicodeDecodeError("utf-8", b"\xff\xfe", 0, 1,
                                        "invalid start byte")})
    monkeypatch.setattr(subprocess, "run", fake)
    monkeypatch.setattr(
        eb, "_run_tptp_prover",
        lambda problem, command, args, use_wsl, timeout_s:
            ("# SZS status Theorem\n", False))

    v = get_backend("eprover").decide(_GOAL, _PREMISES)   # must not raise
    assert v.status == "proved"
    assert v.solver_version is None


def test_eprover_version_probe_is_memoized_across_repeated_calls(
        fresh_discovery_and_version_caches, monkeypatch):
    """solver_version() is keyed by the resolved (command, use_wsl) pair in
    atp.protocol._binary_version, not recomputed per call — asking the SAME
    backend's version repeatedly never spawns a second subprocess."""
    monkeypatch.setenv("UFK_EPROVER_CMD", "fake-eprover3")
    fake = _FakeRun({("fake-eprover3", "--version"): ("E 3.5.1\n", "")})
    monkeypatch.setattr(subprocess, "run", fake)

    assert get_backend("eprover").solver_version() == "E 3.5.1"
    assert get_backend("eprover").solver_version() == "E 3.5.1"
    assert len(fake.calls) == 1


# ---------------------------------------------------------------------------
# cvc5 (a pip binding, not a spawned binary) — genuinely installed here
# ---------------------------------------------------------------------------

@pytest.fixture()
def fresh_cvc5_version_cache(monkeypatch):
    monkeypatch.setattr(cvc5b, "_VERSION_CACHE", {})


def test_cvc5_solver_version_matches_importlib_metadata_independently(fresh_cvc5_version_cache):
    """Independent second route (test_oracle): read the SAME package's
    version directly via importlib.metadata in the test itself and compare —
    not derived from reading Cvc5Backend's own code."""
    import importlib.metadata
    backend = get_backend("cvc5")
    if not backend.available():
        pytest.skip("cvc5 package not installed")
    expected = importlib.metadata.version("cvc5")
    assert backend.solver_version() == expected
    assert expected                                   # sanity: non-empty


def test_cvc5_solver_version_is_memoized(fresh_cvc5_version_cache, monkeypatch):
    calls = []
    real_version = cvc5b.importlib.metadata.version

    def _counting_version(name):
        calls.append(name)
        return real_version(name)

    monkeypatch.setattr(cvc5b.importlib.metadata, "version", _counting_version)
    backend = get_backend("cvc5")
    if not backend.available():
        pytest.skip("cvc5 package not installed")
    for _ in range(3):
        backend.solver_version()
    assert len(calls) == 1


def test_cvc5_decide_carries_solver_version_into_the_verdict(fresh_cvc5_version_cache):
    """A REAL cvc5 decide() (the package is installed here) on a ground
    tautology — P(alice) -> P(alice) is a classical propositional tautology,
    trivially UNSAT to negate, so this is fast and needs no mocking."""
    backend = get_backend("cvc5")
    if not backend.available():
        pytest.skip("cvc5 package not installed")
    tautology = _PARSE("P(alice) → P(alice)")
    v = backend.decide(tautology)
    assert v.status == "proved"
    assert v.solver_version                             # non-empty
    assert v.solver_version == backend.solver_version()
    assert v.to_dict()["solver_version"] == v.solver_version


# ---------------------------------------------------------------------------
# HETS (an HTTP server, not a spawned binary) — offline, stubbed client
# ---------------------------------------------------------------------------

class _FakeHetsClient:
    """HetsClient stand-in with a version() counter (test_hets_backend.py's
    own _FakeClient has no version() method, so this is a local, narrower
    double — same upload/prove shape, plus the one method this item adds)."""

    version_calls = 0
    version_text = "The Heterogeneous Tool Set, version 0.108.0"

    def __init__(self, base_url, *, timeout=30.0):
        self.base_url = base_url

    def version(self):
        _FakeHetsClient.version_calls += 1
        return _FakeHetsClient.version_text

    def upload(self, text, filename):
        return "/tmp/fake/kit_problem.casl"

    def prove(self, iri, node, *, reasoner=None, translation=None, time_limit=10):
        return [{"name": "Ax1", "result": "Proved",
                "used_prover": {"identifier": reasoner or "SPASS"},
                "used_translation": "CASL2TPTP_FOF", "prover_output": "",
                "used_time": None, "tactic_script": None}]


@pytest.fixture()
def stubbed_hets(monkeypatch):
    _FakeHetsClient.version_calls = 0
    _FakeHetsClient.version_text = "The Heterogeneous Tool Set, version 0.108.0"
    monkeypatch.setattr(hb, "_VERSION_CACHE", {})
    monkeypatch.setattr(hets_pkg, "HetsClient", _FakeHetsClient)
    monkeypatch.setattr(hets_pkg, "discover_hets_url",
                        lambda **kw: ("http://fake-hets:8000", None))
    return _FakeHetsClient


def test_hets_solver_version_reads_the_version_endpoint(stubbed_hets):
    assert get_backend("hets").solver_version() == \
        "The Heterogeneous Tool Set, version 0.108.0"


def test_hets_solver_version_none_when_unreachable(monkeypatch):
    monkeypatch.setattr(hb, "_VERSION_CACHE", {})

    def _unreachable(**kw):
        raise proto.BackendUnavailable("hets: no server discovered")
    monkeypatch.setattr(hets_pkg, "discover_hets_url", _unreachable)
    assert get_backend("hets").solver_version() is None


def test_hets_decide_carries_solver_version_into_the_verdict(stubbed_hets):
    v = get_backend("hets").decide(_PARSE("P(alice)"))
    assert v.status == "proved"
    assert v.solver_version == "The Heterogeneous Tool Set, version 0.108.0"
    assert v.to_dict()["solver_version"] == v.solver_version


def test_hets_version_is_memoized_per_base_url(stubbed_hets):
    """Two decide() calls against the SAME (stubbed) server -> exactly ONE
    GET /version, matching item 5's "never spawn ... after the first" for
    the HTTP route (there is no subprocess here, but the same discipline
    applies to the HTTP round trip)."""
    get_backend("hets").decide(_PARSE("P(alice)"))
    get_backend("hets").decide(_PARSE("P(bob)"))
    assert _FakeHetsClient.version_calls == 1


def test_hets_unsupported_formula_with_explicit_url_carries_solver_version(monkeypatch):
    """review-confirmed regression: an out-of-fragment formula (modal node,
    outside CASL FOL/MSFOL) used to drop solver_version unconditionally on
    its UNKNOWN/"unsupported" verdict, even when the caller passed an
    explicit `url=` override -- i.e. already opted into contacting THAT
    specific server (see the module docstring's `url=` CAVEAT), so nothing
    stops resolving its version before the fragment check. discover_hets_url
    is stubbed to explode, proving the explicit-`url=` path never calls it
    (the version comes from `url=` directly, not from discovery)."""
    monkeypatch.setattr(hb, "_VERSION_CACHE", {})
    monkeypatch.setattr(hets_pkg, "HetsClient", _FakeHetsClient)

    def _boom(**kw):
        raise AssertionError("discover_hets_url must not run when url= is given")
    monkeypatch.setattr(hets_pkg, "discover_hets_url", _boom)

    modal = MSFLParser(modal=True).parse("□P → P")
    v = get_backend("hets").decide(modal, url="http://fake-hets:8000")
    assert v.status == "unknown"
    assert v.reason == "unsupported"
    assert v.solver_version == "The Heterogeneous Tool Set, version 0.108.0"


def test_hets_unsupported_formula_without_url_never_touches_discovery(monkeypatch):
    """Companion to the case above: WITHOUT an explicit `url=`, resolving
    solver_version for an out-of-fragment formula would require running
    discover_hets_url()'s own network health probe -- forbidden, mirroring
    test_out_of_fragment_is_unsupported_before_any_network in the unowned
    tests/test_hets_backend.py (discovery must never run before the
    fragment check in the default-discovery path). solver_version simply
    stays None on this verdict rather than the backend reaching for it."""
    monkeypatch.setattr(hb, "_VERSION_CACHE", {})

    def _boom(**kw):
        raise AssertionError("discover_hets_url must not run before the fragment check")
    monkeypatch.setattr(hets_pkg, "discover_hets_url", _boom)

    modal = MSFLParser(modal=True).parse("□P → P")
    v = get_backend("hets").decide(modal)
    assert v.status == "unknown"
    assert v.reason == "unsupported"
    assert v.solver_version is None


# ---------------------------------------------------------------------------
# HETS_IMAGE: digest-pinned, not a movable tag (no live Docker required)
# ---------------------------------------------------------------------------

def test_hets_image_is_digest_pinned_not_a_bare_tag():
    """A bare ``:latest`` (or any other mutable tag) can silently swap the
    image out from under this kit; the reference must carry a sha256
    digest — see hets/docker.py's module-level comment for how THIS exact
    digest was verified (two independent registry-API sources, live) to be
    HETS 0.108.0."""
    assert "@sha256:" in hets_docker.HETS_IMAGE
    repo, _, digest = hets_docker.HETS_IMAGE.partition("@sha256:")
    assert repo == "spechub2/hets"
    assert len(digest) == 64
    assert all(c in "0123456789abcdef" for c in digest)


@pytest.mark.hets_live
@pytest.mark.skipif(not hets_docker.hets_available(), reason="no running hets-server")
class TestHetsSolverVersionLive:
    """Serial, against a real container (see hets_live convention) — the
    verified live banner is "The Heterogeneous Tool Set, version 0.108.0"
    (matched exactly when the running server is the digest-pinned image;
    a differently-configured $UFK_HETS_URL server only needs to be
    non-empty, so this only pins the SUBSTRING every HETS server prints)."""

    def test_real_server_reports_a_nonempty_version(self):
        # Modus ponens (P(alice), forall x (P(x) -> Q(x)) |= Q(alice)) --
        # genuinely valid, same fixture the live subprocess backends below
        # use, unlike a bare atomic P(alice) (not a theorem on its own).
        v = get_backend("hets").decide(_GOAL, _PREMISES, reasoner="SPASS")
        assert v.status == "proved", (v.status, v.reason, v.detail)
        assert v.solver_version
        assert "Heterogeneous Tool Set" in v.solver_version


# ---------------------------------------------------------------------------
# Live: Vampire / E, when genuinely reachable in THIS environment (native
# PATH or WSL — VampireBackend itself only auto-discovers native PATH, so a
# WSL-only install is forced on via $UFK_VAMPIRE_WSL by the test itself;
# EProverBackend's own _discover() already tries both, so no forcing needed).
# ---------------------------------------------------------------------------

def _reachable_binary_route(name: str):
    """``"native"``/``"wsl"``/``None`` — cheap collection-time probe (mirrors
    ``eprover_available()``'s own two-step discovery, local to this test
    file since ``VampireBackend``/``Prover9Backend`` have no WSL
    auto-discovery of their own — see ``protocol.py``)."""
    import shutil as _shutil

    if _shutil.which(name):
        return "native"
    try:
        r = subprocess.run(["wsl.exe", "which", name],
                           capture_output=True, text=True, timeout=10)
        if r.returncode == 0 and r.stdout.strip():
            return "wsl"
    except (OSError, subprocess.TimeoutExpired):
        pass
    return None


_VAMPIRE_ROUTE = _reachable_binary_route("vampire")


@pytest.mark.skipif(_VAMPIRE_ROUTE is None,
                    reason="no vampire binary reachable (native PATH or WSL)")
class TestVampireSolverVersionLive:
    def _force_discovery(self, monkeypatch):
        monkeypatch.setenv("UFK_VAMPIRE", "vampire")
        if _VAMPIRE_ROUTE == "wsl":
            monkeypatch.setenv("UFK_VAMPIRE_WSL", "1")
        else:
            monkeypatch.delenv("UFK_VAMPIRE_WSL", raising=False)

    def test_real_vampire_version_is_nonempty_and_starts_with_vampire(self, monkeypatch):
        self._force_discovery(monkeypatch)
        version = get_backend("vampire").solver_version()
        assert version
        assert version.startswith("Vampire")            # e.g. "Vampire 5.0.1 (...)"

    def test_real_decide_carries_the_same_version(self, monkeypatch):
        self._force_discovery(monkeypatch)
        v = get_backend("vampire").decide(_GOAL, _PREMISES, timeout=15000)
        assert v.status == "proved", (v.status, v.reason, v.detail)
        assert v.solver_version
        assert v.solver_version == get_backend("vampire").solver_version()


@pytest.mark.skipif(not eb.eprover_available(), reason="no eprover binary found")
class TestEProverSolverVersionLive:
    def test_real_eprover_version_is_nonempty_and_starts_with_e(self):
        version = get_backend("eprover").solver_version()
        assert version
        assert version.startswith("E ")                  # e.g. "E 3.5.1 Countess Grey (...)"

    def test_real_decide_carries_the_same_version(self):
        v = get_backend("eprover").decide(_GOAL, _PREMISES, timeout=15000)
        if v.status == "error" and v.reason == "infra" and "Assertion" in (v.detail or ""):
            pytest.skip("the eprover binary aborted (see test_eprover_zipperposition.py)")
        assert v.status == "proved", (v.status, v.reason, v.detail)
        assert v.solver_version
        assert v.solver_version == get_backend("eprover").solver_version()


def test_verdict_positional_fields_keep_their_0_27_order():
    # solver_version is new: it must not shift the positional slots callers of
    # 0.27.0 used (status, backend, logic, reason, szs_status, wall_time,
    # countermodel, proof, detail, agreement).
    from dataclasses import fields
    from unicode_fol_kit.atp.protocol import Verdict
    names = [f.name for f in fields(Verdict)]
    assert names[:10] == ["status", "backend", "logic", "reason", "szs_status",
                          "wall_time", "countermodel", "proof", "detail", "agreement"]
    assert names[-1] == "solver_version"
    v = Verdict("refuted", "z3", "fol", None, None, 0.5, {"kind": "z3"})
    assert v.countermodel == {"kind": "z3"} and v.solver_version is None
