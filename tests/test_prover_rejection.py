r"""A prover that REFUSES a problem is an error, not a timeout.

An external prover that cannot read its input prints no verdict. Before this
file's change every subprocess backend but E read that silence as "did not get
there in time": Vampire's backend returned ``UNKNOWN`` / ``incomplete`` and threw
the prover's own message away, Twee's returned ``UNKNOWN`` / ``incomplete``
("twee status: Unknown"), Prover9's returned ``UNKNOWN`` / ``incomplete`` ("found
no proof"), and ``api.prove`` then flattened whatever error did surface into
``vampire:error/infra`` inside an ``unknown`` chain verdict. Forty-odd
comparisons in a downstream run read "undecided" for exactly this reason.

The rule these tests pin, derived from the verdict vocabulary rather than from
what the code prints:

* every SZS-speaking prover (Vampire, E, Zipperposition) prints its
  ``SZS status`` line whenever it HAS a verdict -- ``Theorem``,
  ``CounterSatisfiable``, but also ``GaveUp``, ``ResourceOut``, ``Timeout`` and
  ``Unknown``. So a run that ended by itself (our own timeout did not fire) with
  no such line and no refutation has no verdict at all: ``ERROR`` / ``infra``,
  with the prover's own text in ``detail``;
* Twee prints ``RESULT: <status>`` the same way (``GaveUp`` included), so no
  ``RESULT`` line without a timeout is the same failure;
* Prover9's manual gives its exit code 1 as the FATAL exit (a syntax error in
  the input, or its own bug) and 2-7 as ordinary ends of a search, so exit 1
  without ``THEOREM PROVED`` is a refusal, and the others stay "found no proof";
* a genuine timeout, and the prover's OWN ``GaveUp`` / ``ResourceOut`` /
  ``Unknown``, stay exactly what they were;
* Vampire does not always print an SZS line when it gives up: a non-theorem of a
  typed-arithmetic problem ends ``Termination reason: Refutation not found,
  incomplete strategy`` and nothing else (recorded below). A run that SHOWS how
  its search ended is an honest ``UNKNOWN``, never a refusal: the three outcomes
  (refused / gave up / timed out) are three different (status, reason) pairs;
* the kit's own wall-clock budget is honoured by Prover9 too, and a run it cuts
  off is ``UNKNOWN`` / ``timeout`` like the other backends'.

Where the prover's wording matters, the fixtures are RECORDED, not typed from
memory: Vampire 5.0.1, E 3.5.1 and Twee 2.6.1 were run on this very problem
shape (see each fixture's comment); Prover9 is not installed on the machine this
was written on, so its fixtures are stand-ins built from the manual's exit-code
table and say so. The live tests at the bottom run the real binaries where they
are reachable and skip, visibly, where they are not.
"""

import shutil
import subprocess

import pytest

from unicode_logic_kit import MSFLParser, api
from unicode_logic_kit.atp import eprover_backend as eb
from unicode_logic_kit.atp import prover9_entailment as p9
from unicode_logic_kit.atp import protocol as proto
from unicode_logic_kit.atp import twee_entailment as te
from unicode_logic_kit.atp import vampire_entailment as ve
from unicode_logic_kit.atp._tptp_problem import generate_tptp_problem_with_mapping
from unicode_logic_kit.atp.portfolio import portfolio_prove
from unicode_logic_kit.atp.protocol import (
    ERROR, PROVED, REFUTED, UNKNOWN, ProverBackend, Verdict, get_backend,
)
from unicode_logic_kit.atp.twee_backend import TweeBackend
from unicode_logic_kit.atp.vampire_entailment import check_entailment_vampire_detailed

_FOL = MSFLParser()
_PREMISES = [_FOL.parse("∀x (Human(x) → Mortal(x))"), _FOL.parse("Human(socrates)")]
_GOAL = _FOL.parse("Mortal(socrates)")

#: The wording every backend shares; a reader of a benchmark table greps for it.
_NOT_A_TIMEOUT = "not a timeout"


# ---------------------------------------------------------------------------
# The prover's own refusals, as recorded.
# ---------------------------------------------------------------------------

# Vampire 5.0.1 (release build, 2026-01-18), run live through WSL on the
# cross-kind clash `fof(premise_1, axiom, (![E]: agent(agent(E)))).` -- the
# predicate `agent` used as a function. Exit code 4, nothing on stderr, NO SZS
# line. The first complaint (after "Trying TPTP") is the real one; the SMTLIB2
# fallback's "Unexpected end of list" is Vampire retrying a file that was never
# SMT-LIB.
_VAMPIRE_REFUSAL = (
    "% Running in auto input_syntax mode. Trying TPTP\n"
    "% Failed with\n"
    "% User error: Non-boolean term agent(agent(X0)) of sort $i is used in a "
    "formula context (detected at or around line 1)\n"
    "% Trying SMTLIB2\n"
    "User error: Unexpected end of list at line 1 col 2\n"
    "fof\n"
    "^^^\n"
)

# Vampire 5.0.1 on a plain syntax error (a missing closing parenthesis).
_VAMPIRE_PARSE_ERROR = (
    "% Running in auto input_syntax mode. Trying TPTP\n"
    "% Failed with\n"
    "% parse error in \"\", line 3: ) not found (text: <eof>)\n"
    "% Trying SMTLIB2\n"
    "Parser exception: unmatched left parenthesis in line 2 at \n"
)

# Vampire 5.0.1, run live through WSL (``vampire --proof tptp``, the kit's own
# command line) on a TFA problem whose conjecture is not entailed:
# tff(...,type,theta: $int > $o). tff(premise_1,axiom,theta(human(car))).
# tff(goal,conjecture,theta(human(agent_term))). Exit code 1, NO SZS line: the
# search ended on its own and Vampire says so only in its statistics block.
_VAMPIRE_GAVE_UP = (
    "% Running in auto input_syntax mode. Trying TPTP\n"
    "% Refutation not found, incomplete strategy\n"
    "% ------------------------------\n"
    "% Version: Vampire 5.0.1 (Release build, commit 1b13eaf on 2026-01-18 12:14:50 +0000)\n"
    "% Linked with Z3 4.14.0.0 3c47fd96cf5645d0c42b2c819d9e9a84380aa721 NOTFOUND\n"
    "% CaDiCaL version: 2.1.3\n"
    "% Termination reason: Refutation not found, incomplete strategy\n"
    "% Time elapsed: 0.005 s\n"
    "% Peak memory usage: 12 MB\n"
    "% ------------------------------\n"
    "% ------------------------------\n"
)

# Vampire 5.0.1 stopped by its OWN ``--time_limit 1`` on a group-theory problem
# (non-commutativity, no proof, saturation never ends): exit code 1, no SZS line.
_VAMPIRE_TIME_LIMIT = (
    "% Running in auto input_syntax mode. Trying TPTP\n"
    "% Time limit reached! \n"
    "% ------------------------------\n"
    "% Version: Vampire 5.0.1 (Release build, commit 1b13eaf on 2026-01-18 12:14:50 +0000)\n"
    "% Linked with Z3 4.14.0.0 3c47fd96cf5645d0c42b2c819d9e9a84380aa721 NOTFOUND\n"
    "% CaDiCaL version: 2.1.3\n"
    "% Termination reason: Time limit\n"
    "% Termination phase: Saturation\n"
    "% Time elapsed: 1.0000 s\n"
    "% Peak memory usage: 66 MB\n"
)

# The same problem under ``--activation_limit 5``: exit code 1, no SZS line.
_VAMPIRE_ACTIVATION_LIMIT = (
    "% Running in auto input_syntax mode. Trying TPTP\n"
    "% Activation limit reached!\n"
    "% ------------------------------\n"
    "% Version: Vampire 5.0.1 (Release build, commit 1b13eaf on 2026-01-18 12:14:50 +0000)\n"
    "% Linked with Z3 4.14.0.0 3c47fd96cf5645d0c42b2c819d9e9a84380aa721 NOTFOUND\n"
    "% CaDiCaL version: 2.1.3\n"
    "% Termination reason: Activation limit\n"
    "% Time elapsed: 0.007 s\n"
    "% Peak memory usage: 13 MB\n"
    "% ------------------------------\n"
    "% ------------------------------\n"
)

# E 3.5.1, run live through WSL on the same clash. Exit code 3, EMPTY stdout:
# E complains on stderr only, and prints no SZS line. The temp-file path is
# shortened. Note the trailing space E prints.
_E_REFUSAL = (
    "eprover: /tmp/problem.p:1:(Column 45):(just read ')'): Equal Predicate/Sign "
    "('=') or Negated Equal Predicate ('!=') expected, but Closing bracket (')') "
    "read \n"
)

# Twee 2.6.1, run live through WSL on a problem with a missing parenthesis.
# Exit code 1, EMPTY stdout, the complaint on stderr, no RESULT line.
_TWEE_REFUSAL = (
    "Error in /tmp/problem.p (line 2, column 1):\n"
    "Unexpected fof\n"
    "Unknown error\n"
)

# Twee 2.6.1 on a non-Horn clause: the same shape (exit 1, stderr only).
_TWEE_NON_HORN = (
    "Expected a Horn problem, but the input file contained\n"
    "the following non-Horn clause:\n"
    "  tcf(premise_1, axiom, ![X: $i]: (p(X)=true | q(X)=true)).\n"
)

# Prover9: NOT installed here, so this is a STAND-IN for the wording, not a
# recording. What the test relies on is only the documented part: exit code 1
# is Prover9's FATAL_EXIT.
_PROVER9_FATAL_STANDIN = "Fatal error:  stand-in message for an input Prover9 refused\n"


# ---------------------------------------------------------------------------
# A subprocess.run stand-in
# ---------------------------------------------------------------------------

class _FakeRun:
    """``subprocess.run`` that answers a ``--version`` probe quietly and every
    other call with ONE canned outcome: a ``CompletedProcess`` built from
    ``(returncode, stdout, stderr)``, or an exception to raise."""

    def __init__(self):
        self.outcome = None
        self.calls = []
        self.timeouts = []          # the ``timeout=`` of every non-version call

    def respond(self, returncode=0, stdout="", stderr=""):
        self.outcome = (returncode, stdout, stderr)

    def raise_(self, exc):
        self.outcome = exc

    def __call__(self, cmd, *args, **kwargs):
        cmd = list(cmd)
        self.calls.append(cmd)
        if cmd and cmd[-1] == "--version":
            return subprocess.CompletedProcess(cmd, 0, stdout="fake-prover 1.0\n", stderr="")
        if cmd and cmd[-1] == "-h":
            # Prover9 has no --version: its banner line comes with -h.
            return subprocess.CompletedProcess(
                cmd, 0, stdout="=== Prover9 ===\nProver9 (64) version 1.0, fake.\n", stderr="")
        self.timeouts.append(kwargs.get("timeout"))
        if isinstance(self.outcome, BaseException):
            raise self.outcome
        returncode, stdout, stderr = self.outcome
        return subprocess.CompletedProcess(cmd, returncode, stdout=stdout, stderr=stderr)


@pytest.fixture()
def run(monkeypatch):
    """Every prover binary is fake: the env points discovery at fake names and
    ``subprocess.run`` answers for all of them."""
    monkeypatch.setattr(proto, "_VERSION_CACHE", {})
    monkeypatch.setattr(eb, "_DISCOVERY_CACHE", {})
    monkeypatch.setenv("UFK_VAMPIRE", "fake-vampire")
    monkeypatch.delenv("UFK_VAMPIRE_WSL", raising=False)
    monkeypatch.setenv("UFK_EPROVER_CMD", "fake-eprover")
    monkeypatch.setenv("UFK_ZIPPERPOSITION_CMD", "fake-zipperposition")
    monkeypatch.setenv("UFK_PROVER9", "fake-prover9")
    monkeypatch.delenv("UFK_PROVER9_WSL", raising=False)
    fake = _FakeRun()
    monkeypatch.setattr(subprocess, "run", fake)
    return fake


def _decide(name, **options):
    return get_backend(name).decide(_GOAL, _PREMISES, **options)


def _assert_refusal(verdict, *, quoted, szs="Error"):
    """The one shape a refusal must have, whichever prover it came from.

    ``szs`` is ``"Error"`` (the protocol's image of ERROR/infra) unless the
    prover itself printed an error-naming status, which is kept verbatim.
    """
    assert verdict.status == ERROR, (verdict.status, verdict.detail)
    assert verdict.reason == "infra"
    assert verdict.szs_status == szs
    assert not verdict.is_definitive
    assert _NOT_A_TIMEOUT in verdict.detail
    for fragment in quoted:
        assert fragment in verdict.detail, (fragment, verdict.detail)


# ---------------------------------------------------------------------------
# The shared wording
# ---------------------------------------------------------------------------

def test_the_detail_quotes_a_short_output_line_by_line():
    # Hand-derived from the template: "<prover> produced no verdict (<evidence>);
    # this is a failure, not a timeout. Its own output: <lines joined by ' | '>",
    # with blank lines and surrounding whitespace dropped.
    detail = proto._rejection_detail("vampire", "line one\n\n  line two  \n",
                                     "no SZS status line in its output")
    assert detail == ("vampire produced no verdict (no SZS status line in its "
                      "output); this is a failure, not a timeout. Its own "
                      "output: line one | line two")


@pytest.mark.parametrize("output", ["", "   \n\n  \t\n"])
def test_an_empty_output_is_said_to_be_empty(output):
    detail = proto._rejection_detail("twee", output, "no RESULT line in its output")
    assert detail.endswith("Its own output: (it printed nothing)")


def test_nul_bytes_of_a_utf16_launcher_message_are_dropped():
    # wsl.exe writes its own diagnostics UTF-16; read as 8-bit text every other
    # byte is NUL. Without dropping them the quoted message is unreadable.
    wide = "".join(ch + "\x00" for ch in "no such command")
    detail = proto._rejection_detail("vampire", wide, "no SZS status line in its output")
    assert detail.endswith("Its own output: no such command")


def test_a_long_output_is_quoted_from_its_first_failure_looking_line():
    # 200 lines of statistics (none of them failure-looking), then the crash.
    # The explanation is at the END of a crash, so quoting the HEAD would bury it.
    filler = [f"% statistics line {i}" for i in range(200)]
    output = "\n".join(filler + ["eprover: Assertion 'status' failed.",
                                 "Aborted (core dumped)"])
    detail = proto._rejection_detail("eprover", output, "no SZS status line in its output")
    assert detail.endswith("Its own output: eprover: Assertion 'status' failed. | "
                           "Aborted (core dumped)")
    assert "statistics line" not in detail


def test_a_long_output_that_starts_with_the_failure_is_cut_at_the_cap():
    output = "\n".join(["Fatal error: the reason"] + [f"filler {i}" for i in range(200)])
    detail = proto._rejection_detail("prover9", output, "exit code 1")
    message = detail.split("Its own output: ", 1)[1]
    assert message.startswith("Fatal error: the reason | filler 0")
    assert message.endswith(" ...")
    assert len(message) == proto._REJECTION_QUOTE_CHARS + len(" ...")


def test_a_long_output_with_no_failure_looking_line_is_quoted_from_its_tail():
    lines = [f"progress {i}" for i in range(300)]
    detail = proto._rejection_detail("eprover", "\n".join(lines), "no SZS status line")
    message = detail.split("Its own output: ", 1)[1]
    assert message == "... " + " | ".join(lines)[-proto._REJECTION_QUOTE_CHARS:]


# ---------------------------------------------------------------------------
# Vampire
# ---------------------------------------------------------------------------

def test_vampire_refusal_is_an_error_carrying_vampires_message(run):
    run.respond(returncode=4, stdout=_VAMPIRE_REFUSAL)
    verdict = _decide("vampire")
    _assert_refusal(verdict, quoted=[
        "User error: Non-boolean term agent(agent(X0)) of sort $i is used in a "
        "formula context",
        "no SZS status line in its output",
    ])
    assert verdict.solver_version == "fake-prover 1.0"      # provenance survives


def test_vampire_syntax_error_is_an_error_carrying_vampires_message(run):
    run.respond(returncode=4, stdout=_VAMPIRE_PARSE_ERROR)
    _assert_refusal(_decide("vampire"), quoted=["parse error", ") not found"])


def test_vampire_detailed_route_reports_error_and_keeps_the_excerpt(run):
    run.respond(returncode=4, stdout=_VAMPIRE_REFUSAL)
    result = check_entailment_vampire_detailed(_PREMISES, _GOAL, "fake-vampire")
    assert result["status"] == ERROR
    assert result["reason"] == "infra"
    assert result["szs_status"] is None
    assert "User error: Non-boolean term" in result["output_excerpt"]
    assert result["derivation"] is None


def test_vampires_stderr_is_not_lost(run):
    # A launcher failure or a crash speaks on stderr; stdout is empty.
    run.respond(returncode=127, stdout="", stderr="vampire: error while loading shared libraries\n")
    _assert_refusal(_decide("vampire"), quoted=["error while loading shared libraries"])


def test_vampire_szs_status_that_names_an_error_quotes_the_message(run):
    run.respond(returncode=1, stdout="% SZS status SyntaxError for problem\n"
                                     "% parse error in \"\", line 3\n")
    verdict = _decide("vampire")
    _assert_refusal(verdict, quoted=["SZS status SyntaxError", "parse error"],
                    szs="SyntaxError")


@pytest.mark.parametrize("stdout, status, reason, szs", [
    # The prover's OWN verdicts are not refusals: each stays what it was.
    ("% SZS status GaveUp for problem\n", UNKNOWN, "incomplete", "GaveUp"),
    ("% SZS status ResourceOut for problem\n", UNKNOWN, "bound_hit", "ResourceOut"),
    ("% SZS status Timeout for problem\n", UNKNOWN, "timeout", "Timeout"),
    ("% SZS status Unknown for problem\n", UNKNOWN, None, "Unknown"),
    ("% SZS status CounterSatisfiable for problem\n", REFUTED, None, "CounterSatisfiable"),
    # No SZS line but a refutation: the documented fallback, still a proof.
    ("% Refutation found. Thanks to Tanya!\n", PROVED, None, None),
], ids=["gaveup", "resourceout", "timeout-status", "unknown-status",
        "countersatisfiable", "refutation-without-status-line"])
def test_vampires_own_verdicts_are_unchanged(run, stdout, status, reason, szs):
    run.respond(returncode=0, stdout=stdout)
    verdict = _decide("vampire")
    assert (verdict.status, verdict.reason) == (status, reason)
    assert verdict.status != ERROR


def test_a_vampire_that_hits_our_timeout_is_still_an_unknown_timeout(run):
    run.raise_(subprocess.TimeoutExpired(cmd="fake-vampire", timeout=1))
    verdict = _decide("vampire", timeout=1000)
    assert (verdict.status, verdict.reason) == (UNKNOWN, "timeout")


@pytest.mark.parametrize("stdout, reason, szs, said", [
    # Recorded runs. The protocol's own table gives the SZS image of each pair:
    # unknown/incomplete is GaveUp, unknown/timeout Timeout, unknown/bound_hit
    # ResourceOut. Vampire's wording of the limit decides the reason: a time
    # limit is a timeout, any other limit a bound that was hit, everything else
    # the prover giving up.
    (_VAMPIRE_GAVE_UP, "incomplete", "GaveUp", "Refutation not found, incomplete strategy"),
    (_VAMPIRE_TIME_LIMIT, "timeout", "Timeout", "Time limit"),
    (_VAMPIRE_ACTIVATION_LIMIT, "bound_hit", "ResourceOut", "Activation limit"),
    # The same give-up with the statistics block cut away: the line that says
    # "Refutation not found" is enough.
    ("% Refutation not found, incomplete strategy\n", "incomplete", "GaveUp",
     "Refutation not found"),
], ids=["gave-up", "own-time-limit", "own-activation-limit", "refutation-not-found-alone"])
def test_a_vampire_that_ended_its_search_without_an_szs_line_is_an_honest_unknown(
        run, stdout, reason, szs, said):
    # Vampire read the problem and searched; the missing SZS line is its habit on
    # typed-arithmetic problems, not a refusal. ERROR/infra here told the caller
    # "a failure, not a timeout" while quoting "Refutation not found".
    run.respond(returncode=1, stdout=stdout)
    verdict = _decide("vampire")
    assert (verdict.status, verdict.reason) == (UNKNOWN, reason)
    assert verdict.szs_status == szs
    assert not verdict.is_definitive
    assert _NOT_A_TIMEOUT not in verdict.detail          # it is not the failure wording
    assert said in verdict.detail
    detailed = check_entailment_vampire_detailed(_PREMISES, _GOAL, "fake-vampire")
    assert (detailed["status"], detailed["reason"], detailed["szs_status"]) == (UNKNOWN, reason, None)


def test_the_verdict_keeps_refused_gave_up_and_timed_out_apart(run):
    # One prover, three ways to end without a proof, three DIFFERENT readings.
    outcomes = {}
    run.respond(returncode=4, stdout=_VAMPIRE_REFUSAL)
    verdict = _decide("vampire")
    outcomes["refused"] = (verdict.status, verdict.reason)
    run.respond(returncode=1, stdout=_VAMPIRE_GAVE_UP)
    verdict = _decide("vampire")
    outcomes["gave up"] = (verdict.status, verdict.reason)
    run.raise_(subprocess.TimeoutExpired(cmd="fake-vampire", timeout=1))
    verdict = _decide("vampire", timeout=1000)
    outcomes["timed out"] = (verdict.status, verdict.reason)
    assert outcomes == {"refused": (ERROR, "infra"),
                        "gave up": (UNKNOWN, "incomplete"),
                        "timed out": (UNKNOWN, "timeout")}
    assert len(set(outcomes.values())) == 3


def test_an_error_next_to_a_termination_line_is_still_a_refusal(run):
    # CONSTRUCTED (not recorded): the refusal text of a real run followed by a
    # termination line. Text of a failure rules the "ended by itself" reading
    # out, so a refusal can never be filed as an honest give-up.
    run.respond(returncode=4, stdout=_VAMPIRE_REFUSAL + "% Termination reason: Unknown\n")
    _assert_refusal(_decide("vampire"), quoted=["User error: Non-boolean term"])


def test_a_run_that_printed_no_account_of_a_search_is_still_a_refusal(run):
    # No SZS line, no refutation, no termination line: nothing says a search
    # happened. Unchanged: ERROR/infra with the prover's words.
    run.respond(returncode=1, stdout="% Running in auto input_syntax mode. Trying TPTP\n")
    _assert_refusal(_decide("vampire"), quoted=["Trying TPTP", "no SZS status line"])


def test_the_bool_route_keeps_its_documented_contract(run):
    # check_logical_entailment_vampire documents that a rejected problem is
    # False, "not raised"; the detailed route is where the refusal is reported.
    run.respond(returncode=4, stdout=_VAMPIRE_REFUSAL)
    assert ve.check_logical_entailment_vampire(_PREMISES, _GOAL, "fake-vampire") is False


# ---------------------------------------------------------------------------
# E and Zipperposition (one shared class)
# ---------------------------------------------------------------------------

def test_e_refusal_is_an_error_carrying_es_message(run):
    run.respond(returncode=3, stdout="", stderr=_E_REFUSAL)
    _assert_refusal(_decide("eprover"), quoted=[
        "Closing bracket (')') read", "(Column 45)",
        "no SZS status line in its output"])


def test_zipperposition_refusal_is_an_error_with_the_same_wording(run):
    # Zipperposition is not installed here: the text is a stand-in; what the
    # test relies on is only that there is no SZS line and nothing cut it off.
    run.respond(returncode=1, stdout="Error: parse error at line 1\n")
    verdict = _decide("zipperposition")
    _assert_refusal(verdict, quoted=["Error: parse error at line 1"])
    assert verdict.detail.startswith("zipperposition produced no verdict")


def test_e_szs_status_that_names_an_error_quotes_the_message(run):
    run.respond(returncode=3, stdout="# SZS status InputError\n# bad token near 'agent'\n")
    _assert_refusal(_decide("eprover"), quoted=["SZS status InputError", "bad token"],
                    szs="InputError")


@pytest.mark.parametrize("stdout, status, reason", [
    ("# SZS status GaveUp\n", UNKNOWN, "incomplete"),
    ("# SZS status ResourceOut\n", UNKNOWN, "bound_hit"),
    ("# SZS status CounterSatisfiable\n", REFUTED, None),
], ids=["gaveup", "resourceout", "countersatisfiable"])
def test_es_own_verdicts_are_unchanged(run, stdout, status, reason):
    run.respond(returncode=0, stdout=stdout)
    verdict = _decide("eprover")
    assert (verdict.status, verdict.reason) == (status, reason)


def test_an_e_that_hits_our_timeout_is_still_an_unknown_timeout(run):
    run.raise_(subprocess.TimeoutExpired(cmd="fake-eprover", timeout=1))
    verdict = _decide("eprover", timeout=1000)
    assert (verdict.status, verdict.reason) == (UNKNOWN, "timeout")


# ---------------------------------------------------------------------------
# Twee
# ---------------------------------------------------------------------------

_TWEE_PREMISES = [_FOL.parse("∀x (f(f(x)) = x)")]
_TWEE_GOAL = _FOL.parse("f(f(f(f(anna)))) = anna")


def _twee(run, **kw):
    return TweeBackend().decide(_TWEE_GOAL, _TWEE_PREMISES, use_wsl=False,
                                twee_cmd="fake-twee", **kw)


@pytest.mark.parametrize("stderr, quoted", [
    (_TWEE_REFUSAL, ["Unexpected fof", "line 2, column 1"]),
    (_TWEE_NON_HORN, ["Expected a Horn problem", "non-Horn clause"]),
], ids=["syntax-error", "non-horn"])
def test_twee_refusal_is_an_error_carrying_twees_message(run, stderr, quoted):
    run.respond(returncode=1, stdout="", stderr=stderr)
    verdict = _twee(run)
    _assert_refusal(verdict, quoted=quoted + ["no RESULT line in its output"])
    assert verdict.detail.startswith("twee produced no verdict")


@pytest.mark.parametrize("stdout, status, reason", [
    # Twee's own words: GaveUp is its resource budget, CounterSatisfiable a
    # genuine refutation. Neither is a refusal.
    ("RESULT: GaveUp (couldn't solve the problem).\n", UNKNOWN, "incomplete"),
    ("RESULT: CounterSatisfiable (the conjecture is false).\n", REFUTED, None),
], ids=["gaveup", "countersatisfiable"])
def test_twees_own_results_are_unchanged(run, stdout, status, reason):
    run.respond(returncode=0, stdout=stdout)
    verdict = _twee(run)
    assert (verdict.status, verdict.reason) == (status, reason)


def test_a_twee_that_hits_our_timeout_is_still_an_unknown_timeout(run):
    run.raise_(subprocess.TimeoutExpired(cmd="fake-twee", timeout=1))
    verdict = _twee(run, timeout=1000)
    assert (verdict.status, verdict.reason) == (UNKNOWN, "timeout")


# ---------------------------------------------------------------------------
# Prover9
# ---------------------------------------------------------------------------

def test_prover9_fatal_exit_is_an_error_carrying_its_message(run):
    run.respond(returncode=1, stdout="", stderr=_PROVER9_FATAL_STANDIN)
    verdict = _decide("prover9")
    _assert_refusal(verdict, quoted=["Fatal error:  stand-in message", "exit code 1"])
    assert verdict.detail.startswith("prover9 produced no verdict")


def test_prover9_fatal_exit_with_its_message_on_stdout_is_quoted_too(run):
    run.respond(returncode=1, stdout="Prover9 banner\n" + _PROVER9_FATAL_STANDIN)
    _assert_refusal(_decide("prover9"), quoted=["Fatal error:  stand-in message"])


@pytest.mark.parametrize("returncode", [2, 3, 4, 5, 6, 7], ids=lambda c: f"exit{c}")
def test_prover9_ordinary_search_ends_still_find_no_proof(run, returncode):
    # The manual's exit codes 2-7 are ends of a SEARCH (sos list empty, a
    # memory/time/given/kept limit, an action): "found no proof", as before.
    run.respond(returncode=returncode, stdout="SEARCH FAILED\n")
    verdict = _decide("prover9")
    assert (verdict.status, verdict.reason) == (UNKNOWN, "incomplete")
    assert "found no proof" in verdict.detail


def test_prover9_theorem_proved_is_proved(run):
    run.respond(returncode=0, stdout="THEOREM PROVED\n")
    assert _decide("prover9").status == PROVED


def test_prover9_our_timeout_is_an_unknown_timeout(run):
    # A run the KIT cut off because its budget ran out is a timeout, said as one
    # (like Vampire, E and Twee) -- not Prover9 "finding no proof".
    run.raise_(subprocess.TimeoutExpired(cmd="fake-prover9", timeout=1))
    verdict = _decide("prover9", timeout=1000)
    assert (verdict.status, verdict.reason) == (UNKNOWN, "timeout")
    assert verdict.szs_status == "Timeout"
    assert verdict.solver_version == "Prover9 (64) version 1.0, fake."      # its banner, read with -h
    assert "found no proof" not in verdict.detail
    assert "1-second budget" in verdict.detail


@pytest.mark.parametrize("budget_ms, seconds", [
    (10000, 10),    # the backend's default: 10 000 ms = 10 s (it used to be a hard-coded 30)
    (7000, 7),
    (1500, 1),      # whole seconds, rounded down, as for Vampire and E
    (200, 1),       # and never below one
], ids=["default", "seven", "one-and-a-half", "below-one"])
def test_prover9_is_given_the_budget_the_caller_asked_for(run, budget_ms, seconds):
    # ms // 1000, at least 1 -- the rule the Vampire and E backends use.
    run.respond(returncode=0, stdout="THEOREM PROVED\n")
    _decide("prover9", timeout=budget_ms)
    assert run.timeouts == [seconds]


def test_prover9_bool_route_budget_and_timeout_contract(run):
    run.raise_(subprocess.TimeoutExpired(cmd="fake-prover9", timeout=5))
    # Default: the historic bool, a cut-off run is simply "no proof".
    assert p9.check_logical_entailment(_PREMISES, _GOAL, "fake-prover9", timeout=5) is False
    assert run.timeouts == [5]
    # Asked: it is separated, and carries the budget.
    with pytest.raises(p9.Prover9TimedOut) as caught:
        p9.check_logical_entailment(_PREMISES, _GOAL, "fake-prover9", timeout=5,
                                    raise_on_timeout=True)
    assert caught.value.timeout == 5
    # Not given: the module's own default (30 s) as before.
    run.respond(returncode=0, stdout="THEOREM PROVED\n")
    assert p9.check_logical_entailment(_PREMISES, _GOAL, "fake-prover9") is True
    assert run.timeouts[-1] == 30


def test_prover9_that_hangs_is_stopped_at_the_budget_and_reported_as_a_timeout(monkeypatch):
    """The REAL ``subprocess.run`` timeout machinery (kill, collect, raise
    ``TimeoutExpired``) on a REAL process that hangs for 60 s. No Prover9 binary
    exists on the machine this was written on, so the hanging process is a
    Python interpreter; only the command line is swapped for it, everything the
    runner does around the call is the production code."""
    import sys
    import time

    real_run = subprocess.run
    monkeypatch.setattr(proto, "_VERSION_CACHE", {})
    monkeypatch.delenv("UFK_PROVER9_WSL", raising=False)     # the fake binary is a native command
    hang = [sys.executable, "-c", "import time; time.sleep(60)"]

    def run_hanging(cmd, *args, **kwargs):
        if list(cmd)[-1] == "-h":
            return subprocess.CompletedProcess(
                cmd, 0, stdout="=== Prover9 ===\nProver9 (64) version 1.0, fake.\n", stderr="")
        return real_run(hang, *args, **kwargs)

    monkeypatch.setattr(subprocess, "run", run_hanging)
    start = time.perf_counter()
    verdict = get_backend("prover9").decide(_GOAL, _PREMISES, timeout=1000,
                                            prover9_path="fake-prover9")
    elapsed = time.perf_counter() - start
    assert (verdict.status, verdict.reason) == (UNKNOWN, "timeout")
    assert verdict.solver_version == "Prover9 (64) version 1.0, fake."
    # The 1000 ms budget was honoured: the process would have run for 60 s, and
    # the runner's own hard-coded 30 s default is not what stopped it.
    # the runner reads its limit on another clock than this one, which on Windows is coarser
    # by some milliseconds: 0.9996 s was measured for the limit of one second
    assert 0.9 <= elapsed < 10, elapsed
    assert verdict.wall_time >= 0.9


# ---------------------------------------------------------------------------
# The two public surfaces: api.prove and the MCP prove tool
# ---------------------------------------------------------------------------

class _HonestUnknown(ProverBackend):
    """A backend that really did run out of time -- the thing a refusal must
    not be mistaken for."""

    name = "tptpc-honest-unknown"
    logics = frozenset({"fol"})
    external = False

    def available(self):
        return True

    def decide(self, formula, premises=(), timeout=10000, **options):
        return Verdict(UNKNOWN, self.name, reason="timeout")


def test_api_prove_reports_a_refusal_as_an_error_with_the_message(run):
    run.respond(returncode=4, stdout=_VAMPIRE_REFUSAL)
    verdict = api.prove(_GOAL, _PREMISES, backends=["vampire"])
    # Nothing was asked and answered: the chain's verdict is itself an error,
    # not an "unknown" that reads like a timeout.
    assert verdict.backend == "chain"
    assert verdict.status == ERROR
    assert verdict.reason == "infra"
    assert "vampire:error/infra" in verdict.detail
    assert "User error: Non-boolean term" in verdict.detail
    assert _NOT_A_TIMEOUT in verdict.detail


def test_api_prove_keeps_a_chain_with_one_honest_unknown_unknown(run, monkeypatch):
    monkeypatch.setitem(proto._REGISTRY, _HonestUnknown.name, _HonestUnknown())
    run.respond(returncode=4, stdout=_VAMPIRE_REFUSAL)
    verdict = api.prove(_GOAL, _PREMISES, backends=[_HonestUnknown.name, "vampire"])
    assert verdict.status == UNKNOWN
    assert verdict.backend == "chain"
    # ... and says, in so many words, which member timed out and which refused.
    assert "tptpc-honest-unknown:unknown/timeout" in verdict.detail
    assert "vampire:error/infra" in verdict.detail
    assert "User error: Non-boolean term" in verdict.detail


class _InfraUnknown(ProverBackend):
    """A backend that reports an infrastructure failure as UNKNOWN / infra --
    the shape the Isabelle adapter uses (``reason = "infra"`` on an UNKNOWN)."""

    name = "tptpc-infra-unknown"
    logics = frozenset({"fol"})
    external = False

    def available(self):
        return True

    def decide(self, formula, premises=(), timeout=10000, **options):
        return Verdict(UNKNOWN, self.name, reason="infra", detail="theory rejected: line 3")


def test_api_prove_quotes_an_infra_failure_reported_as_unknown(monkeypatch):
    monkeypatch.setitem(proto._REGISTRY, _InfraUnknown.name, _InfraUnknown())
    verdict = api.prove(_GOAL, _PREMISES, backends=[_InfraUnknown.name])
    # Its status is UNKNOWN, so the chain is not an ERROR -- but the reason it
    # failed is in the detail rather than lost.
    assert verdict.status == UNKNOWN
    assert verdict.detail == ("no definitive verdict — "
                              "tptpc-infra-unknown:unknown/infra (theory rejected: line 3)")


def test_api_prove_chain_without_any_failure_is_worded_as_before(monkeypatch):
    monkeypatch.setitem(proto._REGISTRY, _HonestUnknown.name, _HonestUnknown())
    verdict = api.prove(_GOAL, _PREMISES, backends=[_HonestUnknown.name])
    assert verdict.status == UNKNOWN
    assert verdict.detail == "no definitive verdict — tptpc-honest-unknown:unknown/timeout"


def test_portfolio_answers_like_the_chain(run, monkeypatch):
    # Two routes must not answer one question two ways.
    monkeypatch.setitem(proto._REGISTRY, _HonestUnknown.name, _HonestUnknown())
    run.respond(returncode=4, stdout=_VAMPIRE_REFUSAL)
    alone = portfolio_prove(_GOAL, _PREMISES, backends=["vampire"], jobs=1)
    assert (alone.backend, alone.status, alone.reason) == ("portfolio", ERROR, "infra")
    assert "User error: Non-boolean term" in alone.detail
    mixed = portfolio_prove(_GOAL, _PREMISES,
                            backends=[_HonestUnknown.name, "vampire"], jobs=1)
    assert (mixed.backend, mixed.status) == ("portfolio", UNKNOWN)
    assert "User error: Non-boolean term" in mixed.detail


def test_the_mcp_prove_tool_carries_the_error_and_its_detail(run):
    server = pytest.importorskip("unicode_logic_kit.mcp.server",
                                 reason="optional [mcp] extra not installed")
    run.respond(returncode=4, stdout=_VAMPIRE_REFUSAL)
    result = server.prove("Mortal(socrates)",
                          ["∀x (Human(x) → Mortal(x))", "Human(socrates)"],
                          backends=["vampire"])
    assert result["status"] == "error"
    assert result["reason"] == "infra"
    assert result["szs_status"] == "Error"
    assert "User error: Non-boolean term" in result["detail"]
    assert _NOT_A_TIMEOUT in result["detail"]


# ---------------------------------------------------------------------------
# Live: the real binaries, where they are reachable
#
# The problem text that is refused is written BY HAND here and handed to the
# runner in place of the kit's own writer's output, so these tests keep meaning
# the same thing once the writer stops producing the cross-kind clash.
# ---------------------------------------------------------------------------

_CLASH = ("fof(premise_1, axiom, (![E]: agent(agent(E)))).\n"
          "fof(goal, conjecture, (?[X]: agent(X))).\n")
_MISSING_PAREN = ("fof(premise_1, axiom, (![X]: f(X) = X).\n"
                  "fof(goal, conjecture, f(a) = a).\n")


def _bad_writer(text):
    """A drop-in for ``generate_tptp_problem_with_mapping`` returning ``text``."""
    def writer(premises, conclusion):
        return text, generate_tptp_problem_with_mapping(premises, conclusion)[1]
    return writer


def _live_vampire():
    path = shutil.which("vampire")
    if path:
        return path, False
    try:
        probe = subprocess.run(["wsl.exe", "vampire", "--version"],
                               capture_output=True, text=True, timeout=20)
        if probe.returncode == 0 and "Vampire" in probe.stdout:
            return "vampire", True
    except Exception:    # noqa: BLE001 -- any failure means "not available"
        pass
    return None


_LIVE_VAMPIRE = _live_vampire()


@pytest.mark.skipif(_LIVE_VAMPIRE is None, reason="no Vampire reachable (PATH or WSL)")
def test_live_vampire_refusal_reaches_the_verdict(monkeypatch):
    path, use_wsl = _LIVE_VAMPIRE
    # Control first: the same live path, a well-formed problem, is PROVED --
    # so the ERROR below is the refusal and not a broken harness.
    control = get_backend("vampire").decide(_GOAL, _PREMISES, vampire_path=path,
                                            use_wsl=use_wsl)
    assert control.status == PROVED, (control.status, control.detail)
    monkeypatch.setattr(ve, "generate_tptp_problem_with_mapping", _bad_writer(_CLASH))
    verdict = get_backend("vampire").decide(_GOAL, _PREMISES, vampire_path=path,
                                            use_wsl=use_wsl)
    _assert_refusal(verdict, quoted=["User error"])
    # And the public surface: api.prove discovers the binary through the env.
    monkeypatch.setenv("UFK_VAMPIRE", path)
    monkeypatch.setenv("UFK_VAMPIRE_WSL", "1" if use_wsl else "0")
    surfaced = api.prove(_GOAL, _PREMISES, backends=["vampire"])
    assert surfaced.status == ERROR and "User error" in surfaced.detail


@pytest.mark.skipif(_LIVE_VAMPIRE is None, reason="no Vampire reachable (PATH or WSL)")
def test_live_vampire_giving_up_on_a_typed_arithmetic_non_theorem_is_not_an_error():
    path, use_wsl = _LIVE_VAMPIRE
    # Hand-derived: P is uninterpreted and car, alice are unconstrained integers, so
    # P(car) does NOT entail P(alice). Vampire 5.0.1 cannot prove it and ends with
    # "Refutation not found, incomplete strategy" and no SZS line. Whatever the
    # build prints, it read the problem: the answer must not be an error (a build
    # that does print CounterSatisfiable is a correct REFUTED).
    result = check_entailment_vampire_detailed(
        [_FOL.parse("P(car)")], _FOL.parse("P(alice)"), path, use_wsl=use_wsl,
        timeout=60, sort="int")
    assert result["status"] in (UNKNOWN, REFUTED), result
    if result["status"] == UNKNOWN:
        assert result["reason"] == "incomplete"


@pytest.mark.skipif(not eb.eprover_available(), reason="no eprover binary found")
def test_live_eprover_refusal_reaches_the_verdict(monkeypatch):
    # A build that ABORTS on every problem (Ubuntu's 3.0.03) is ALSO a verdict
    # of this shape -- an error with the prover's own text -- so this holds for
    # a crash and for a refusal alike; only the quoted text differs.
    monkeypatch.setattr(eb, "generate_tptp_problem_with_mapping", _bad_writer(_CLASH))
    verdict = get_backend("eprover").decide(_GOAL, _PREMISES)
    assert verdict.status == ERROR, (verdict.status, verdict.detail)
    assert verdict.reason == "infra"
    assert _NOT_A_TIMEOUT in verdict.detail
    assert not verdict.detail.endswith("Its own output: (it printed nothing)")


_LIVE_TWEE = te.twee_available()


@pytest.mark.skipif(not _LIVE_TWEE, reason="no Twee binary reachable via WSL")
def test_live_twee_refusal_reaches_the_verdict(monkeypatch):
    control = TweeBackend().decide(_TWEE_GOAL, _TWEE_PREMISES, timeout=30000)
    assert control.status == PROVED, (control.status, control.detail)
    monkeypatch.setattr(te, "generate_tptp_problem_with_mapping", _bad_writer(_MISSING_PAREN))
    verdict = TweeBackend().decide(_TWEE_GOAL, _TWEE_PREMISES, timeout=30000)
    _assert_refusal(verdict, quoted=["no RESULT line in its output"])
    assert not verdict.detail.endswith("Its own output: (it printed nothing)")
