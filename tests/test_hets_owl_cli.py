r"""C1 (Docker half): ``hets.owl_to_tptp``, the lossy command-line route.

There is no Hets server and no Docker on the machine this was written on, so
every assertion here is argv-shaped or console-shaped: ``subprocess.run`` is
monkeypatched and fed HETS' real console output, verbatim from
``commands.md``'s eleven recorded runs. That is enough to pin the things that
actually go wrong — the command line, the two comorphism spellings that fail
silently, EXIT 0 that is not success, and the three refusals — but it is NOT
an end-to-end confirmation. The one ``hets_live`` test at the bottom is, and
it needs a machine with Docker.

The console strings below are the measured ones:

* success: ``Translated using comorphism OWL22CASL;CASL2TPTP_FOF : OWL -> TPTP``
  (note the ``;`` — HETS prints the composition that way even though the
  command line takes ``:``);
* sublogic refusal, which appears ONLY in the run WITHOUT ``-Y``:
  ``### Warning:`` / ``for '...' expected sublogic '...'`` /
  ``but found sublogic '...'`` / ``Keeping untranslated theory``, with EXIT 0
  and no ``.tptp`` written;
* the ``;`` spelling as INPUT: ``### Warning: Cannot find logic comorphism
  OWL22CASL;CASL2TPTP_FOF``, EXIT 0, no ``.tptp``;
* SoftFOL: ``SuleCFOL2SoftFOL.transOPSYMB: unknown op: Qual_op_name 1 ...``,
  EXIT 1.
"""

import posixpath

import pytest

from unicode_fol_kit.atp.protocol import BackendUnavailable
from unicode_fol_kit.hets import (
    HetsOwlNormalizationError,
    HetsSublogicError,
    hets_available,
    owl_to_tptp,
)
from unicode_fol_kit.hets import owl_cli

NODE = "https://openenergyplatform.org/ontology/oeo/"
ENCODED_NODE = "https%3A%2F%2Fopenenergyplatform.org%2Fontology%2Foeo%2F"
TPTP_FILE = f"oeo-hets_{ENCODED_NODE}.tptp"
TH_FILE = f"oeo-hets_{ENCODED_NODE}.th"

TRANSLATED = ("Translated using comorphism OWL22CASL;CASL2TPTP_FOF : "
              "OWL -> TPTP\n")
SUBLOGIC_WARNING = (
    "### Warning:\n"
    "for 'OWL22CASL;CASL2TPTP_FOF' expected sublogic 'NP-sROIQux-D|-|'\n"
    "but found sublogic 'NP-sROIQ-D|Literal|dateTime|decimal|integer|string|'"
    " with signature sublogic 'ELQLRL-ALC'\n"
    "Keeping untranslated theory\n"
)
NO_COMORPHISM = ("### Warning: Cannot find logic comorphism "
                 "OWL22CASL;CASL2TPTP_FOF\nKeeping untranslated theory\n")
UNDECLARED = (
    "*** Error:\nIncorrect AnnotationAssertion axiom. Axiom subject is not "
    "declared: 'obo:BFO_0000134'\n"
    "Incorrect AnnotationAssertion axiom. Axiom subject is not declared: "
    "'http://example.com/bfo-spec-label'\n")

PP_DOL_FILE = "oeo-hets.pp.dol"

TPTP_TEXT = "fof(ax_ax1, axiom, pred_a(c)).\n"
# The TRANSLATED theory of a TPTP chain carries NO Prefix: lines -- measured
# on the real ontology: 0 in oeo_tptpchain_full_lossy.th against 15 in
# oeo-hets.pp.dol. That is why pp.dol is requested at all.
TH_TEXT = "%{\n\npredicates:  pred_a: $i > $o\n\n}%\n"
PP_DOL_TEXT = ("spec oeo =\n"
               "     Prefix: : <http://example.org/>\n"
               "     Prefix: obo: <http://purl.obolibrary.org/obo/>\n")


class _Proc:
    def __init__(self, returncode=0, stdout="", stderr=""):
        self.returncode = returncode
        self.stdout = stdout
        self.stderr = stderr


class FakeDocker:
    """Stands in for ``subprocess.run``: records argv, serves canned output.

    ``probe_console``/``lossy_console`` are HETS' console for the run without
    and with ``-Y``; ``probe_files``/``lossy_files`` are what each run left in
    its output directory.
    """

    def __init__(self, *, probe_console="", lossy_console=None,
                 probe_files=None, lossy_files=None,
                 probe_code=0, lossy_code=0, cp_code=0):
        self.probe_console = probe_console
        self.lossy_console = lossy_console
        self.probe_files = probe_files or {}
        self.lossy_files = lossy_files or {}
        self.probe_code = probe_code
        self.lossy_code = lossy_code
        self.cp_code = cp_code
        self.hets_argvs = []
        self.all_argvs = []

    def __call__(self, argv, **kwargs):
        self.all_argvs.append(list(argv))
        if argv[1] == "cp":
            return _Proc(self.cp_code, stderr="cp failed" if self.cp_code else "")
        command = argv[-1]
        # Which run's output directory this command concerns, decided by the
        # DIRECTORY NAME -- an `ls`/`cat` for the lossy run carries no -Y.
        lossy = "out_lossy" in command
        files = self.lossy_files if lossy else self.probe_files
        if "hets-server" in command:
            self.hets_argvs.append(list(argv))
            console = (self.lossy_console if lossy and
                       self.lossy_console is not None else self.probe_console)
            code = self.lossy_code if lossy else self.probe_code
            return _Proc(code, stdout=console)
        if command.startswith("ls -1"):
            return _Proc(0, stdout="\n".join(files) + "\n" if files else "")
        if command.startswith("cat "):
            name = posixpath.basename(command[4:].strip())
            if name in files:
                return _Proc(0, stdout=files[name])
            return _Proc(1, stderr="no such file")
        return _Proc(0)


@pytest.fixture
def ontology(tmp_path):
    path = tmp_path / "oeo-hets.owl"
    path.write_text("Ontology(<http://x/>)\n", encoding="utf-8")
    return str(path)


@pytest.fixture(autouse=True)
def _a_docker_binary_exists(request, monkeypatch):
    """A fake `docker` on PATH for the offline tests -- and NOT for the live one.

    The live test must reach the real binary; an autouse fixture that faked it
    there would make the one end-to-end confirmation in this file fail with
    FileNotFoundError and prove nothing. (It did, once.)
    """
    if "hets_live" in request.keywords:
        return
    monkeypatch.setattr(owl_cli.shutil, "which", lambda name: "/usr/bin/docker")


def _install(monkeypatch, fake):
    monkeypatch.setattr(owl_cli.subprocess, "run", fake)
    monkeypatch.setenv("UFK_HETS_CONTAINER", "ufk-hets-oeo")
    return fake


# =============================================================================
# The command line.
# =============================================================================

def test_the_successful_probe_run_carries_no_minus_Y(monkeypatch, ontology):
    fake = _install(monkeypatch, FakeDocker(
        probe_console=TRANSLATED,
        probe_files={TPTP_FILE: TPTP_TEXT, TH_FILE: TH_TEXT,
                     PP_DOL_FILE: PP_DOL_TEXT}))
    result = owl_to_tptp(ontology)
    assert len(fake.hets_argvs) == 1
    command = fake.hets_argvs[0][-1]
    assert " -Y " not in f" {command} "
    assert result.lossy is False
    assert result.sublogic_mismatch is None
    assert result.tptp == TPTP_TEXT
    assert result.theory == TH_TEXT
    assert result.pretty == PP_DOL_TEXT
    assert result.comorphism == "OWL22CASL;CASL2TPTP_FOF"
    # All three outputs come from ONE hets-server run.
    assert "-o th,tptp,pp.dol" in command


def test_the_lossy_run_is_the_exact_recorded_command_line(monkeypatch, ontology):
    fake = _install(monkeypatch, FakeDocker(
        probe_console=SUBLOGIC_WARNING,
        lossy_console=TRANSLATED,
        probe_files={},
        lossy_files={TPTP_FILE: TPTP_TEXT, TH_FILE: TH_TEXT,
                     PP_DOL_FILE: PP_DOL_TEXT}))
    result = owl_to_tptp(ontology)
    assert len(fake.hets_argvs) == 2           # probe, then -Y
    argv = fake.hets_argvs[1]
    assert argv[:5] == ["/usr/bin/docker", "exec", "ufk-hets-oeo", "sh", "-c"]
    command = argv[-1]
    assert ("hets-server -v2 -a none -Y -t OWL22CASL:CASL2TPTP_FOF "
            "-o th,tptp,pp.dol -O ") in command
    assert command.rstrip().endswith("oeo-hets.owl")
    assert result.lossy is True


def test_the_lossy_result_reports_which_sublogic_gap_forced_it(monkeypatch, ontology):
    """-Y is SILENT, so the probe run is the only place the loss is visible."""
    _install(monkeypatch, FakeDocker(
        probe_console=SUBLOGIC_WARNING,
        lossy_console=TRANSLATED,
        lossy_files={TPTP_FILE: TPTP_TEXT, TH_FILE: TH_TEXT,
                     PP_DOL_FILE: PP_DOL_TEXT}))
    mismatch = owl_to_tptp(ontology).sublogic_mismatch
    assert mismatch is not None
    assert mismatch.comorphism == "OWL22CASL;CASL2TPTP_FOF"
    assert mismatch.expected == "NP-sROIQux-D|-|"
    assert mismatch.found == (
        "NP-sROIQ-D|Literal|dateTime|decimal|integer|string|")


def test_lossy_false_raises_the_typed_sublogic_error(monkeypatch, ontology):
    _install(monkeypatch, FakeDocker(probe_console=SUBLOGIC_WARNING))
    with pytest.raises(HetsSublogicError) as caught:
        owl_to_tptp(ontology, lossy=False)
    error = caught.value
    assert error.comorphism == "OWL22CASL;CASL2TPTP_FOF"
    assert error.expected == "NP-sROIQux-D|-|"
    assert error.found.startswith("NP-sROIQ-D|Literal|")
    assert "lossy=True" in str(error)
    assert ".omitted_axioms" in str(error)


def test_lossy_false_never_runs_hets_twice(monkeypatch, ontology):
    fake = _install(monkeypatch, FakeDocker(probe_console=SUBLOGIC_WARNING))
    with pytest.raises(HetsSublogicError):
        owl_to_tptp(ontology, lossy=False)
    assert len(fake.hets_argvs) == 1


# =============================================================================
# The refusals.
# =============================================================================

def test_the_semicolon_spelling_is_refused_before_any_subprocess(monkeypatch, ontology):
    """It exits 0 and writes nothing, so it must never reach HETS."""
    fake = _install(monkeypatch, FakeDocker(probe_console=TRANSLATED))
    with pytest.raises(RuntimeError) as caught:
        owl_to_tptp(ontology, comorphism="OWL22CASL;CASL2TPTP_FOF")
    message = str(caught.value)
    assert "the composition separator is ':'" in message
    assert "OWL22CASL:CASL2TPTP_FOF" in message
    assert fake.all_argvs == []


def test_softfol_is_refused_by_name(monkeypatch, ontology):
    fake = _install(monkeypatch, FakeDocker(probe_console=TRANSLATED))
    with pytest.raises(RuntimeError) as caught:
        owl_to_tptp(ontology, comorphism="OWL22CASL:CASL2SoftFOL")
    message = str(caught.value)
    assert "SuleCFOL2SoftFOL" in message
    assert "OWL22CASL:CASL2TPTP_FOF" in message
    assert fake.all_argvs == []


def test_exit_zero_with_no_tptp_is_not_success(monkeypatch, ontology):
    """Both non-lossy runs exit 0 and keep the UNTRANSLATED theory."""
    _install(monkeypatch, FakeDocker(
        probe_console="some unrelated chatter\n",
        lossy_console="more chatter\n",
        probe_files={}, lossy_files={}))
    with pytest.raises(RuntimeError) as caught:
        owl_to_tptp(ontology)
    message = str(caught.value)
    assert "exited 0 but wrote no .tptp" in message
    assert "Translated using comorphism" in message
    assert "more chatter" in message            # quotes HETS' console


def test_hets_reporting_no_comorphism_is_refused_by_name(monkeypatch, ontology):
    _install(monkeypatch, FakeDocker(probe_console=NO_COMORPHISM))
    with pytest.raises(RuntimeError, match="Cannot find logic comorphism"):
        owl_to_tptp(ontology)


def test_an_undeclared_annotation_subject_lists_every_iri_and_refuses_to_guess(
        monkeypatch, ontology):
    _install(monkeypatch, FakeDocker(probe_console=UNDECLARED))
    with pytest.raises(HetsOwlNormalizationError) as caught:
        owl_to_tptp(ontology)
    error = caught.value
    assert error.undeclared == (
        "obo:BFO_0000134", "http://example.com/bfo-spec-label")
    message = str(error)
    assert "Declaration(" in message
    assert "will NOT choose the Kind" in message
    assert "may report only the FIRST" in message
    assert "no OWL writer" in message


def test_no_container_lists_every_option_tried(monkeypatch, ontology):
    monkeypatch.delenv("UFK_HETS_CONTAINER", raising=False)
    monkeypatch.setattr(owl_cli.subprocess, "run",
                        FakeDocker(probe_console=TRANSLATED))
    with pytest.raises(BackendUnavailable) as caught:
        owl_to_tptp(ontology)
    message = str(caught.value)
    assert "1. container= — not given" in message
    assert "$UFK_HETS_CONTAINER — not set" in message
    assert "start_container=True" in message
    assert "$UFK_HETS_URL cannot be used instead" in message
    assert "-Y) exists only on the command line" in message


def test_no_docker_binary_says_a_url_cannot_substitute(monkeypatch, ontology):
    monkeypatch.setattr(owl_cli.shutil, "which", lambda name: None)
    with pytest.raises(BackendUnavailable) as caught:
        owl_to_tptp(ontology)
    assert "docker exec" in str(caught.value)
    assert "REST route has no equivalent" in str(caught.value)


def test_a_failed_docker_cp_is_reported(monkeypatch, ontology):
    _install(monkeypatch, FakeDocker(probe_console=TRANSLATED, cp_code=1))
    with pytest.raises(RuntimeError, match="docker cp"):
        owl_to_tptp(ontology)


# =============================================================================
# Output discovery.
# =============================================================================

def test_the_node_is_recovered_from_the_output_file_name(monkeypatch, ontology):
    _install(monkeypatch, FakeDocker(
        probe_console=TRANSLATED,
        probe_files={TPTP_FILE: TPTP_TEXT, TH_FILE: TH_TEXT,
                     PP_DOL_FILE: PP_DOL_TEXT}))
    assert owl_to_tptp(ontology).node == NODE


def test_two_tptp_files_are_refused_rather_than_picked(monkeypatch, ontology):
    _install(monkeypatch, FakeDocker(
        probe_console=TRANSLATED,
        probe_files={TPTP_FILE: TPTP_TEXT,
                     "other_x.tptp": "fof(b, axiom, q).\n"}))
    with pytest.raises(RuntimeError) as caught:
        owl_to_tptp(ontology)
    message = str(caught.value)
    assert "will not pick between them" in message
    assert TPTP_FILE in message and "other_x.tptp" in message


def test_a_missing_theory_file_does_not_fail_the_call(monkeypatch, ontology):
    """The .th carries the Prefix: lines but is not load-bearing."""
    _install(monkeypatch, FakeDocker(
        probe_console=TRANSLATED, probe_files={TPTP_FILE: TPTP_TEXT}))
    result = owl_to_tptp(ontology)
    assert result.tptp == TPTP_TEXT
    assert result.theory == ""


def test_symbols_and_omitted_axioms_are_none_without_a_client(monkeypatch, ontology):
    """None means NOT COMPUTED — never an empty table that reads as 'nothing'."""
    _install(monkeypatch, FakeDocker(
        probe_console=TRANSLATED,
        probe_files={TPTP_FILE: TPTP_TEXT, TH_FILE: TH_TEXT,
                     PP_DOL_FILE: PP_DOL_TEXT}))
    result = owl_to_tptp(ontology)
    assert result.symbols is None
    assert result.omitted_axioms is None


def test_a_client_fills_the_symbol_table_and_the_omitted_axioms(
        monkeypatch, ontology):
    """The prefix map comes from pp.dol, NOT from the translated theory.

    Measured live on the real ontology: the `.th` of a TPTP chain has zero
    `Prefix:` lines, so reading them from there left every CURIE unexpanded
    with nothing saying so. The `.th` here deliberately carries none, so this
    test fails if the prefixes are read from the wrong output.
    """
    _install(monkeypatch, FakeDocker(
        probe_console=TRANSLATED,
        probe_files={TPTP_FILE: "fof(ax_ax1, axiom, pred_obo_uA(c)).\n",
                     TH_FILE: "%{\n\npredicates: pred_obo_uA: $i > $o\n\n}%\n",
                     PP_DOL_FILE:
                         "     Prefix: obo: "
                         "<http://purl.obolibrary.org/obo/>\n"}))

    class FakeClient:
        def upload(self, text, filename):
            return "/tmp/f/" + filename

        def dg(self, iri):
            return {"DGraph": {"DGNode": [{
                "name": "n",
                "Declarations": [{"kind": "Class", "name": "A",
                                  "iri": "obo:A"}],
                "Axioms": [
                    {"name": "Ax1", "Axiom": "SubClassOf( obo:A obo:B )"},
                    {"name": "Ax2",
                     "Axiom": "DataPropertyRange( obo:d rdfs:Literal )"},
                ],
            }]}}

    result = owl_to_tptp(ontology, client=FakeClient())
    assert result.symbols is not None
    row = result.symbols.by_printed("obo:A")
    assert row.tptp_name == "pred_obo_uA"
    assert row.in_tptp is True
    assert row.iri == "http://purl.obolibrary.org/obo/A"
    assert result.symbols.prefixes == {"obo": "http://purl.obolibrary.org/obo/"}
    assert result.symbols.unexpanded_prefixes == ()
    assert [a.name for a in result.omitted_axioms] == ["Ax2"]


def test_the_scratch_directory_is_removed_and_lives_under_tmp(
        monkeypatch, ontology):
    fake = _install(monkeypatch, FakeDocker(
        probe_console=TRANSLATED,
        probe_files={TPTP_FILE: TPTP_TEXT, TH_FILE: TH_TEXT,
                     PP_DOL_FILE: PP_DOL_TEXT}))
    owl_to_tptp(ontology)
    made = [argv[-1] for argv in fake.all_argvs if argv[-1].startswith("mkdir")]
    removed = [argv[-1] for argv in fake.all_argvs if argv[-1].startswith("rm -rf")]
    assert made and removed
    assert all("/tmp/ufk_owl_to_tptp_" in command for command in made + removed)


# =============================================================================
# LIVE: the one end-to-end confirmation. Needs Docker; run serially.
# =============================================================================

# Two axioms are enough: `sublogic_probe_result.txt` records that
# DataPropertyRange(:d rdfs:Literal) alone pushes a theory out of
# OWL22CASL's sublogic ('ELQLRL-ALC-D|Literal|' against the expected
# 'NP-sROIQux-D|-|'), so this reproduces the mismatch without OEO.
LIVE_ONTOLOGY = """Prefix(:=<http://example.org/t#>)
Prefix(rdfs:=<http://www.w3.org/2000/01/rdf-schema#>)
Ontology(<http://example.org/t>
  Declaration(Class(:A))
  Declaration(Class(:B))
  Declaration(DataProperty(:d))
  SubClassOf(:A :B)
  DataPropertyRange(:d rdfs:Literal)
)
"""


@pytest.mark.hets_live
@pytest.mark.skipif(
    not hets_available(),
    reason="no reachable HETS server (set $UFK_HETS_URL, or run "
           "`docker run -d --rm -p 8000:8000 spechub2/hets:latest`); "
           "owl_to_tptp additionally needs $UFK_HETS_CONTAINER naming that "
           "container, because -Y exists only on the command line")
def test_owl_to_tptp_reports_the_loss_on_a_real_hets(tmp_path):
    import os

    from unicode_fol_kit.fol.tptp_input import parse_tptp

    if not os.environ.get("UFK_HETS_CONTAINER"):
        pytest.skip("set $UFK_HETS_CONTAINER to the running container's name")
    path = tmp_path / "d_rdfsLiteral.ofn"
    path.write_text(LIVE_ONTOLOGY, encoding="utf-8")
    result = owl_to_tptp(str(path))
    assert result.lossy is True
    assert result.sublogic_mismatch is not None
    assert "Literal" in result.sublogic_mismatch.found
    assert parse_tptp(result.tptp)
