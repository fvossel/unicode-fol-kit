"""Tests for Vampire-backed entailment checking.

Most tests need no Vampire binary: they exercise the TPTP problem generation and
the stdout result parser directly, and the error contracts (bad path, non-FOL
input). A final integration test runs a real Vampire only when one is resolvable,
and is skipped otherwise.
"""

import re
import shutil
import subprocess

import pytest

from unicode_fol_kit import MSFLParser, check_logical_entailment_vampire
from unicode_fol_kit.atp.vampire_entailment import (
    _generate_vampire_input, _is_entailed_output, check_entailment_vampire_detailed,
)
from unicode_fol_kit.atp import vampire_entailment as _ve

_FOL = MSFLParser()
_MODUS_PONENS_PREMISES = [
    _FOL.parse("∀x (Human(x) → Mortal(x))"),
    _FOL.parse("Human(socrates)"),
]
_MORTAL = _FOL.parse("Mortal(socrates)")

# A many-sorted problem whose TF0 text has a CROSS-KIND clash: the predicate
# ``Agent`` and the function ``agent`` both render as the TPTP word ``agent``, so
# the TF0 writer renames the function to ``agent_term`` and records it.
#
# The goal is ``∃y Agent(y)``, with an UNSORTED ``y``. The goal these tests used to
# have, ``∃x:Thing Agent(x)``, is not entailed by the premise in the kit's reading
# of a sort: the premise says that every Thing's agent is an Agent, nothing says
# that agent(a) is itself a Thing (a function has no declared result sort), and the
# structure U={0,1}, Thing={0}, agent(0)=1, Agent={1} makes the premise true and the
# goal false. The typed text proved it only because the TF0 inference typed
# ``agent`` as ``thing > thing``, which is the stronger reading the writer now
# refuses. The new goal IS entailed: Thing is not empty, so take a Thing a; agent(a)
# is an Agent, and ``y = agent(a)`` witnesses the unsorted existential. The writer
# accepts it (``agent: thing > $i``; no sort meets the value of ``agent``), so the
# tests below still run the TF0 route they are about.
_MSFOL = MSFLParser(many_sorted=True)
_CLASH_PREMISES = [_MSFOL.parse("∀x:Thing Agent(agent(x))")]
_CLASH_GOAL = _FOL.parse("∃y Agent(y)")        # the many-sorted parser takes only sorted binders


# ---------------------------------------------------------------------------
# TPTP problem generation (no binary)
# ---------------------------------------------------------------------------

def test_generate_vampire_input_shape():
    """Premises become numbered axioms; the conclusion becomes the conjecture.

    The bodies are exactly each node's ``to_tptp()`` — this pins the fof wrapping,
    role assignment, and naming without re-asserting the TPTP rendering itself.
    """
    text = _generate_vampire_input(_MODUS_PONENS_PREMISES, _MORTAL)
    lines = [ln for ln in text.splitlines() if ln.strip()]
    assert lines == [
        f"fof(premise_1, axiom, {_MODUS_PONENS_PREMISES[0].to_tptp()}).",
        f"fof(premise_2, axiom, {_MODUS_PONENS_PREMISES[1].to_tptp()}).",
        f"fof(goal, conjecture, {_MORTAL.to_tptp()}).",
    ]
    # Exactly one conjecture; one axiom per premise.
    assert text.count(", conjecture, ") == 1
    assert text.count(", axiom, ") == len(_MODUS_PONENS_PREMISES)


def test_generate_vampire_input_no_premises():
    """A conclusion with no premises is just the conjecture (validity check)."""
    conclusion = _FOL.parse("P(socrates) ∨ ¬P(socrates)")
    text = _generate_vampire_input([], conclusion)
    lines = [ln for ln in text.splitlines() if ln.strip()]
    assert lines == [f"fof(goal, conjecture, {conclusion.to_tptp()})."]


# ---------------------------------------------------------------------------
# stdout parsing (no binary)
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("stdout, expected", [
    ("% SZS status Theorem for problem\nRefutation found. Thanks to Tanya!", True),
    ("Refutation found. Thanks to Tanya!", True),
    ("% SZS status Theorem for x", True),
    ("% SZS status CounterSatisfiable for x", False),
    ("% SZS status Satisfiable for x", False),
    ("% SZS status Timeout for x", False),
    ("Termination reason: Time limit", False),
    ("", False),
])
def test_is_entailed_output_parser(stdout, expected):
    """The success signal is SZS-Theorem or a found refutation; nothing else."""
    assert _is_entailed_output(stdout) is expected


# ---------------------------------------------------------------------------
# Error contracts (no real Vampire needed)
# ---------------------------------------------------------------------------

def test_bad_vampire_path_raises_file_not_found():
    """A wrong vampire_path surfaces as FileNotFoundError (as for Prover9)."""
    with pytest.raises(FileNotFoundError):
        check_logical_entailment_vampire(
            _MODUS_PONENS_PREMISES, _MORTAL,
            vampire_path="definitely_not_a_real_vampire_binary_xyz",
        )


def test_non_first_order_input_is_rejected_before_running():
    """A modal premise has no TPTP form, so to_tptp's NotImplementedError
    propagates before any subprocess is spawned (path is never consulted)."""
    modal_premise = MSFLParser(modal=True).parse("□Human(socrates)")
    with pytest.raises(NotImplementedError):
        check_logical_entailment_vampire(
            [modal_premise], _MORTAL, vampire_path="vampire",
        )


# ---------------------------------------------------------------------------
# Rückweg: reverse-mapping a (simulated) Vampire proof — no binary needed.
#
# No real Vampire binary is reachable in this environment (neither natively
# nor via WSL — see _wsl_vampire_ok below), so this exercises
# check_entailment_vampire_detailed's ASCII-sanitisation Rückweg against a
# FAKE _spawn_vampire that echoes the problem's OWN (already-sanitised) fof
# lines back as a trivial "proof" — built entirely from the real problem
# text this module generated, never a hand-typed identifier, so the test
# cannot pass by a typo accidentally matching a typo. Where a live external
# tool IS available (E via WSL, Twee via WSL), the equivalent live round
# trip is tested in test_eprover_zipperposition.py / test_twee.py instead.
# ---------------------------------------------------------------------------

def test_check_entailment_vampire_detailed_reverse_maps_derivation(monkeypatch):
    def fake_spawn(input_str, vampire_path, timeout=30, use_wsl=False, extra_args=()):
        lines = [ln for ln in input_str.splitlines() if ln.strip()]
        proof_lines = list(lines)  # already "fof(name, role, formula)." shaped
        proof_lines.append("fof(refutation, plain, $false, inference(x,[status(thm)],[])).")
        stdout = "% SZS status Theorem for problem\n" + "\n".join(proof_lines) + "\n"
        return stdout, False

    monkeypatch.setattr(_ve, "_spawn_vampire", fake_spawn)

    premise = _FOL.parse("∀x (LostTo(x, świątek) → P(x))")
    conclusion = _FOL.parse("P(dani_Shapiro)")
    result = check_entailment_vampire_detailed([premise], conclusion, vampire_path="unused")

    assert result["status"] == "proved"
    steps = result["derivation"]["steps"]
    formula_dicts = [s["formula"] for s in steps if s["formula"] is not None]
    assert any("świątek" in str(d) for d in formula_dicts)
    # the sanitised u-escape token must not leak through anywhere.
    assert not any("u015b" in str(d) for d in formula_dicts)
    # the free-text excerpt is reverse-mapped too (R3's "Erklärungstexte").
    assert "świątek" in result["output_excerpt"]
    assert "u015b" not in result["output_excerpt"]


def test_check_entailment_vampire_detailed_reverse_maps_predicate_names(monkeypatch):
    """R3's free-text Rückweg must restore PREDICATE names too, not only
    constants -- ``Node.to_tptp`` folds only a name's first character
    (``tptp_fold_first_letter``), so even an already ASCII-legal,
    uppercase-initial predicate like 'Human' appears in the exported
    problem (and therefore in anything Vampire echoes back verbatim) as
    'human'. Regression: ``TptpNameMap.reverse()``'s predicate dict used to
    be keyed by the un-folded token, so it never matched the folded text
    this fake echo (built from the REAL generated problem text, not
    hand-typed) puts in stdout.
    """
    def fake_spawn(input_str, vampire_path, timeout=30, use_wsl=False, extra_args=()):
        lines = [ln for ln in input_str.splitlines() if ln.strip()]
        proof_lines = list(lines)
        proof_lines.append("fof(refutation, plain, $false, inference(x,[status(thm)],[])).")
        stdout = "% SZS status Theorem for problem\n" + "\n".join(proof_lines) + "\n"
        return stdout, False

    monkeypatch.setattr(_ve, "_spawn_vampire", fake_spawn)

    result = check_entailment_vampire_detailed(
        _MODUS_PONENS_PREMISES, _MORTAL, vampire_path="unused")

    assert result["status"] == "proved"
    assert "Human" in result["output_excerpt"]
    assert "Mortal" in result["output_excerpt"]
    assert "human(" not in result["output_excerpt"]
    assert "mortal(" not in result["output_excerpt"]


def test_check_entailment_vampire_detailed_prover_introduced_symbol_is_untouched(monkeypatch):
    """A prover-introduced name (a Skolem constant, say) was never one of
    ours, so apply_reverse_tptp must leave it exactly as printed."""
    def fake_spawn(input_str, vampire_path, timeout=30, use_wsl=False, extra_args=()):
        stdout = ("% SZS status Theorem for problem\n"
                  "fof(sk, plain, p(sk1), inference(skolemize,[status(thm)],[])).\n")
        return stdout, False

    monkeypatch.setattr(_ve, "_spawn_vampire", fake_spawn)
    result = check_entailment_vampire_detailed(
        [_FOL.parse("∃x P(x)")], _FOL.parse("∃x P(x)"), vampire_path="unused")
    [step] = result["derivation"]["steps"]
    assert step["formula"]["args"][0]["name"] == "sk1"


# ---------------------------------------------------------------------------
# The TF0 route reverses the writer's renames like the fof route does.
#
# Hand-derived from the writer: in TF0 the predicate Agent renders ``agent`` and
# the function agent renders ``agent`` too, so the function is written
# ``agent_term`` (recorded in the name map). Text a prover echoes from that
# problem, ``agent(agent_term(X))``, therefore reads ``Agent(agent(X))`` in
# kit-level names: the outer word is the predicate, the inner one the function.
# ---------------------------------------------------------------------------

def test_tf0_route_excerpt_is_reverse_mapped_across_a_cross_kind_clash(monkeypatch):
    seen = {}

    def fake_spawn(input_str, vampire_path, timeout=30, use_wsl=False, extra_args=()):
        seen["problem"] = input_str
        # Echo the problem's own lines, as a prover printing its input back would.
        return "% SZS status Theorem for problem\n" + input_str, False

    monkeypatch.setattr(_ve, "_spawn_vampire", fake_spawn)
    result = check_entailment_vampire_detailed(_CLASH_PREMISES, _CLASH_GOAL,
                                               vampire_path="unused")
    assert "tff(" in seen["problem"] and "agent_term" in seen["problem"]   # the clash is real
    assert result["status"] == "proved"
    assert "Agent(agent(X))" in result["output_excerpt"]
    assert "agent_term" not in result["output_excerpt"]


def test_tf0_route_excerpt_is_reverse_mapped_for_a_non_ascii_constant(monkeypatch):
    """The same Rückweg for a name TF0 cannot spell: the writer transliterates the
    constant ``θ`` to the ASCII ``theta`` (``constant_name_to_ascii``'s Greek
    table), a prover echoes ``mortal(theta)``, and the excerpt must read
    ``Mortal(θ)`` again -- the predicate by the first-letter fold, the constant by
    the recorded rename. (Before the TF0 route kept its name map this excerpt was
    left as the prover printed it, ``theta`` included.)"""
    def fake_spawn(input_str, vampire_path, timeout=30, use_wsl=False, extra_args=()):
        assert "tff(" in input_str and "theta" in input_str
        return ("tff(f2,conjecture,(mortal(theta))).\n"
                "% SZS status Theorem for problem\n"), False

    monkeypatch.setattr(_ve, "_spawn_vampire", fake_spawn)
    from unicode_fol_kit.fol._msfl_nodes import SortedConstant
    from unicode_fol_kit.fol.nodes import Atom
    result = check_entailment_vampire_detailed(
        [_MSFOL.parse("∀x:Human Mortal(x)")], Atom("Mortal", [SortedConstant("θ", "Human")]),
        vampire_path="unused")
    assert result["status"] == "proved"
    assert "Mortal(θ)" in result["output_excerpt"]
    assert "theta" not in result["output_excerpt"]


def test_tf0_route_refusal_text_is_reverse_mapped_in_the_backend_detail(monkeypatch):
    # A rejection quotes the prover's words; they must name the caller's symbols.
    from unicode_fol_kit.atp.protocol import get_backend

    seen = {}

    def fake_spawn(input_str, vampire_path, timeout=30, use_wsl=False, extra_args=()):
        seen["problem"] = input_str
        return "User error: ill-typed term agent_term(X0) in a formula context\n", False

    monkeypatch.setattr(_ve, "_spawn_vampire", fake_spawn)
    verdict = get_backend("vampire").decide(_CLASH_GOAL, _CLASH_PREMISES,
                                            vampire_path="no-such-vampire")
    assert seen["problem"].startswith("tff(")           # the TF0 route, not a fof fallback
    assert (verdict.status, verdict.reason) == ("error", "infra")
    assert "ill-typed term agent(X0)" in verdict.detail
    assert "agent_term" not in verdict.detail


# ---------------------------------------------------------------------------
# Integration — only when a Vampire binary is actually present
# ---------------------------------------------------------------------------

_VAMPIRE = shutil.which("vampire")


@pytest.mark.skipif(_VAMPIRE is None, reason="no Vampire binary on PATH")
def test_vampire_decides_entailment_when_installed():
    """Modus ponens is entailed; a missing premise leaves it underivable."""
    assert check_logical_entailment_vampire(
        _MODUS_PONENS_PREMISES, _MORTAL, vampire_path=_VAMPIRE) is True
    assert check_logical_entailment_vampire(
        [_FOL.parse("Human(socrates)")], _MORTAL, vampire_path=_VAMPIRE) is False


def _wsl_vampire_ok():
    """True iff a Vampire is reachable through ``wsl vampire`` (Windows + WSL)."""
    try:
        result = subprocess.run(["wsl.exe", "vampire", "--version"],
                                capture_output=True, text=True, timeout=20)
        return result.returncode == 0 and "Vampire" in result.stdout
    except Exception:  # noqa: BLE001 — any failure means "not available"
        return False


_WSL_VAMPIRE = _wsl_vampire_ok()


@pytest.mark.skipif(not _WSL_VAMPIRE,
                    reason="no Vampire reachable via 'wsl vampire'")
def test_vampire_via_wsl_decides_entailment():
    """Drive a Linux Vampire under WSL from Windows (use_wsl=True).

    Exercises the full path: TPTP generation -> Windows temp file -> wslpath
    translation -> wsl.exe vampire -> SZS parsing. Uses multi-character constants
    (NAME tokens), since single lowercase letters are VARIABLEs and Vampire
    rejects unquantified variables.
    """
    kw = dict(vampire_path="vampire", use_wsl=True)
    # Modus ponens holds; dropping the rule leaves it underivable.
    assert check_logical_entailment_vampire(_MODUS_PONENS_PREMISES, _MORTAL, **kw) is True
    assert check_logical_entailment_vampire(
        [_FOL.parse("Human(socrates)")], _MORTAL, **kw) is False
    # A transitive chain over a real constant is entailed.
    chain = [_FOL.parse("∀x (A(x) → B(x))"), _FOL.parse("∀x (B(x) → C(x))"),
             _FOL.parse("A(dave)")]
    assert check_logical_entailment_vampire(chain, _FOL.parse("C(dave)"), **kw) is True
    # A different individual is not reached by that chain.
    assert check_logical_entailment_vampire(chain, _FOL.parse("C(erin)"), **kw) is False


@pytest.mark.skipif(not _WSL_VAMPIRE,
                    reason="no Vampire reachable via 'wsl vampire'")
def test_vampire_via_wsl_tf0_proof_text_names_the_callers_symbols():
    """A REAL Vampire on the TF0 route of a problem with a cross-kind clash.

    Hand-derived: ``∀x:Thing Agent(agent(x))`` over a non-empty sort entails
    ``∃y Agent(y)`` (take any Thing a; agent(a) satisfies Agent, so y = agent(a)
    witnesses the unsorted existential). It does NOT entail ``∃x:Thing Agent(x)``,
    the goal this test used to prove: agent(a) is not said to be a Thing. Vampire
    prints the problem's formulas inside its proof; they must read
    ``Agent(agent(...))``, not the writer's ``agent(agent_term(...))``.
    """
    result = check_entailment_vampire_detailed(
        _CLASH_PREMISES, _CLASH_GOAL, vampire_path="vampire", use_wsl=True, timeout=60)
    assert result["dialect"] == "tff", result       # the TF0 text, not a fof fallback
    assert result["status"] == "proved", result
    assert "agent_term" not in result["output_excerpt"]
    assert re.search(r"Agent\(agent\(", result["output_excerpt"]), result["output_excerpt"]


# ---------------------------------------------------------------------------
# VampireBackend.decide forwards ``tff`` and ``sort`` to the runner.
#
# The E / Zipperposition backend pops both options and hands them to its
# problem writer; the Vampire backend used to pop only ``vampire_path`` /
# ``use_wsl``, so ``api.prove(..., backends=["vampire"], sort="int")`` could
# never reach the typed-arithmetic route and ``tff=False`` could never force
# the fof route -- the options were silently dropped, and the two backends read
# one option two ways. A fake runner records what it was called with.
# ---------------------------------------------------------------------------

def _recording_runner(monkeypatch):
    """Replace the runner decide() calls with one that records its keyword
    arguments and answers with a canned PROVED result."""
    from unicode_fol_kit.atp import protocol as _protocol

    calls = []

    # The signature is the runner's own: the backend also hands it the names of the
    # premises and whether to read the axiom names of the proof (what the premises
    # a proof used are read from), which these tests do not look at.
    def fake_runner(premises, conclusion, vampire_path, timeout=30, use_wsl=False,
                    tff=None, sort=None, premise_names=None, axiom_names=False):
        calls.append({"vampire_path": vampire_path, "timeout": timeout,
                      "use_wsl": use_wsl, "tff": tff, "sort": sort})
        return {"status": "proved", "reason": None, "szs_status": "Theorem",
                "derivation": None, "output_excerpt": ""}

    monkeypatch.setattr(_ve, "check_entailment_vampire_detailed", fake_runner)
    monkeypatch.setattr(_protocol, "_binary_version", lambda *a, **k: None)
    return calls


def test_vampire_backend_forwards_tff_and_sort_to_the_runner(monkeypatch):
    from unicode_fol_kit.atp.protocol import get_backend
    calls = _recording_runner(monkeypatch)
    verdict = get_backend("vampire").decide(
        _MORTAL, _MODUS_PONENS_PREMISES, timeout=7000, vampire_path="v", use_wsl=False,
        tff=False, sort="int")
    assert verdict.status == "proved"
    assert calls == [{"vampire_path": "v", "timeout": 7, "use_wsl": False,
                      "tff": False, "sort": "int"}]


def test_vampire_backend_forwards_each_value_it_is_given(monkeypatch):
    from unicode_fol_kit.atp.protocol import get_backend
    calls = _recording_runner(monkeypatch)
    backend = get_backend("vampire")
    for tff, sort in [(True, None), (False, None), (None, "real"), (None, "int"),
                      (True, "real")]:
        backend.decide(_MORTAL, _MODUS_PONENS_PREMISES, vampire_path="v",
                       use_wsl=False, tff=tff, sort=sort)
    assert [(c["tff"], c["sort"]) for c in calls] == [
        (True, None), (False, None), (None, "real"), (None, "int"), (True, "real")]


def test_vampire_backend_without_the_options_leaves_the_routing_to_the_runner(monkeypatch):
    # The default is unchanged: ``None`` for both, which is "auto-select".
    from unicode_fol_kit.atp.protocol import get_backend
    calls = _recording_runner(monkeypatch)
    get_backend("vampire").decide(_MORTAL, _MODUS_PONENS_PREMISES, vampire_path="v",
                                  use_wsl=False)
    assert [(c["tff"], c["sort"]) for c in calls] == [(None, None)]


def test_api_prove_with_the_vampire_backend_carries_sort_to_the_runner(monkeypatch):
    # The public entry: options given to api.prove reach the backend, which
    # reaches the runner.
    from unicode_fol_kit import api
    calls = _recording_runner(monkeypatch)
    monkeypatch.setenv("UFK_VAMPIRE", "a-vampire-that-is-never-run")
    verdict = api.prove(_MORTAL, _MODUS_PONENS_PREMISES, backends=["vampire"],
                        sort="int", tff=False, use_wsl=False)
    assert verdict.status == "proved"
    assert [(c["tff"], c["sort"]) for c in calls] == [(False, "int")]


@pytest.mark.skipif(not _WSL_VAMPIRE,
                    reason="no Vampire reachable via 'wsl vampire'")
def test_live_vampire_backend_sort_int_changes_the_verdict_of_an_arithmetic_problem():
    """A REAL Vampire, through the backend. Hand-derived: ``∀x (x > 0 → x ≥ 1)``
    is valid over the INTEGERS (no integer lies strictly between 0 and 1) and
    that is what the typed route asserts with ``sort='int'`` -- Vampire proves it.
    Without ``sort`` arithmetic was not asked for, and the kit reads ``>`` and ``≥``
    as uninterpreted binary predicates and ``0`` and ``1`` as constants: the formula
    is then NOT valid (hand-derived countermodel: a universe {a, b}, ``>`` the full
    relation, ``≥`` empty, so ``x > 0`` holds of every ``x`` and ``x ≥ 1`` of none),
    and Vampire says so (``CounterSatisfiable``). The option therefore decides the
    verdict, and a backend that dropped it would answer the second one twice.

    This test used to expect Vampire's own type error for the untyped route (the
    ``fof`` text carried the interpreted ``$greater`` applied to an individual); the
    problem writers no longer write ``$greater`` unless arithmetic is asked for."""
    from unicode_fol_kit.atp.protocol import get_backend, PROVED
    goal = _FOL.parse("∀x (x > 0 → x ≥ 1)")
    backend = get_backend("vampire")
    typed = backend.decide(goal, [], timeout=60000, vampire_path="vampire",
                           use_wsl=True, sort="int")
    assert typed.status == PROVED, (typed.status, typed.reason, typed.detail)
    assert typed.szs_status == "Theorem"
    untyped = backend.decide(goal, [], timeout=60000, vampire_path="vampire",
                             use_wsl=True)
    assert untyped.status != PROVED
    assert untyped.status == "refuted" and untyped.szs_status == "CounterSatisfiable", \
        (untyped.status, untyped.reason, untyped.detail)
    # ... and ``tff`` reaches the runner too: forced onto the many-sorted typed
    # route the numerals are constants of ``$i`` and the comparisons uninterpreted
    # predicates over it, so the typed text asks the same question and Vampire
    # answers it the same way.
    forced = backend.decide(goal, [], timeout=60000, vampire_path="vampire",
                            use_wsl=True, tff=True)
    assert forced.status == "refuted" and forced.szs_status == "CounterSatisfiable", \
        (forced.status, forced.reason, forced.detail)
