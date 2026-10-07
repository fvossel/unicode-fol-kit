"""Differential tests for roadmap item S1 (soundness): every classical
decision route that reduces many-sorted (MSFOL) input through
``fol.nodes.to_fol`` must assume every sort is non-empty — the same
convention :mod:`unicode_logic_kit.semantics.modelfinder` already enforces
(``_nonempty_subsets``: a sort's universe is always a NON-EMPTY subset of
the domain) and TPTP TF0 guarantees natively (see
:mod:`unicode_logic_kit.atp.tptp_tff`).

Reproduction (observed 2026-09-16, the exact case S1 was opened against):
with ``S = MSFLParser(many_sorted=True)`` and
``f = S.parse('(∀x:Human Mortal(x)) → ∃x:Human Mortal(x))')``,
``atp.z3_models.is_valid(f)`` used to be ``False`` and ``api.prove(f)`` used
to return REFUTED — both wrong, because ``fol.nodes.to_fol``'s relativisation
(``∀x:S φ`` → ``∀x (S(x) → φ)``, ``∃x:S φ`` → ``∃x (S(x) ∧ φ)``) is
polarity-blind and carries no non-emptiness guarantee by itself, so Z3 was
free to make ``Human`` empty and vacuously satisfy the antecedent while
falsifying the consequent — a "countermodel"
``semantics.modelfinder.find_countermodel`` never even considers a legal
MSFOL structure.

The fix: ``unicode_logic_kit.fol._msfl_nodes.nonempty_sort_axioms`` — one
``∃x (S(x))`` sentence per distinct sort name in a problem — added by every
affected route as an extra, UNCONDITIONAL, never-negated sentence (premise
side for validity/entailment, an extra asserted conjunct for satisfiability/
model-finding), never folded inside ``to_fol``/``to_z3``/``to_prover9``/
``to_tptp`` themselves. Routes fixed here: ``atp.z3_models``,
``atp.protocol.Z3Backend`` (+ ``z3_relevant_premises``), ``atp.cvc5_backend``,
``atp.prover9_entailment``, ``atp._tptp_problem`` (the shared ``fof`` builder
underneath ``vampire_entailment``/``eprover_backend``/``twee_entailment``),
``atp.z3_arith``, and ``eval.equivalence``'s classical solver level.
``atp.finite_domain.lower_msfol`` (the ASP/CP backends' own many-sorted front
door) already built exactly these sentences before this fix and now reuses
the shared helper too — see ``tests/test_sorted_finite_domain.py`` for its
own, unchanged-behaviour regression coverage.

Known routes this file cannot fix (outside this item's file ownership —
recorded as open issues in the accompanying report, not silently left
wrong): ``atp.z3_equivalence.formulas_are_equivalent`` has the identical
soundness bug (see ``test_z3_equivalence_reference_has_the_same_bug_not_fixed_here``
below); ``atp.resolution.prove``/``atp.tableau`` are sound but INCOMPLETE on
many-sorted input needing the non-emptiness fact (refutation-only backends
that never emit a wrong PROVED verdict, only a missed one — see
``test_resolution_reference_is_incomplete_not_unsound_not_fixed_here``).
"""

import shutil
import subprocess

import pytest

from unicode_logic_kit.fol.msflparser import MSFLParser
from unicode_logic_kit.fol.nodes import And, Implies, Not, SortedConstant
from unicode_logic_kit.fol._msfl_nodes import nonempty_sort_axioms
from unicode_logic_kit import api
from unicode_logic_kit.semantics import modelfinder
from unicode_logic_kit.atp.z3_models import is_valid, is_satisfiable, get_model
from unicode_logic_kit.atp.z3_arith import is_valid_arith, is_satisfiable_arith, get_model_arith
from unicode_logic_kit.atp.protocol import (
    PROVED, REFUTED, get_backend, z3_relevant_premises,
)
from unicode_logic_kit.atp.cvc5_backend import Cvc5Backend
from unicode_logic_kit.atp.prover9_entailment import (
    _generate_prover9_input, generate_prover9_input_with_mapping,
)
from unicode_logic_kit.atp._tptp_problem import (
    generate_tptp_problem, generate_tptp_problem_with_mapping,
)
from unicode_logic_kit.atp.vampire_entailment import check_logical_entailment_vampire
from unicode_logic_kit.atp.eprover_backend import (
    check_entailment_eprover_detailed, eprover_available,
)
from unicode_logic_kit.eval.equivalence import equivalent

MSFOL = MSFLParser(many_sorted=True).parse
FOL = MSFLParser().parse
Z3 = get_backend("z3")


# ---------------------------------------------------------------------------
# The exact reproduction case
# ---------------------------------------------------------------------------

def test_reproduction_universal_to_existential_is_valid_and_proved():
    """Hand-checked: under the MSFOL convention that every sort is
    non-empty, "(all x:Human, Mortal(x)) -> (some x:Human, Mortal(x))" is a
    tautology (an implication whose consequent is a strictly weaker reading
    of the same premise). Before S1's fix this was reported invalid/
    REFUTED; semantics.modelfinder, which never considers an empty-sort
    structure legal, never found a countermodel either way.
    """
    f = MSFOL("(∀x:Human Mortal(x)) → ∃x:Human Mortal(x)")
    assert is_valid(f) is True
    verdict = Z3.decide(f)
    assert verdict.status == PROVED
    assert api.prove(f, backends=["z3"]).status == PROVED
    assert modelfinder.find_countermodel([], f, max_size=4) is None
    assert modelfinder.is_valid_finite(f, max_size=4) is True


# ---------------------------------------------------------------------------
# test_oracle case 2: universal + its negation is unsatisfiable
# ---------------------------------------------------------------------------

def test_universal_and_its_negation_is_unsatisfiable():
    """Hand-checked: "every S is P" and "every S is not-P" together are
    unsatisfiable, PROVIDED S is non-empty (a witness element would have to
    be both P and not-P). Before S1's fix this was reported SATISFIABLE —
    S=empty makes both universals vacuously true — exactly the loophole
    this item closes.
    """
    conj = And(MSFOL("∀x:S P(x)"), MSFOL("∀x:S ¬P(x)"))
    assert is_satisfiable(conj) is False
    assert is_satisfiable_arith(conj) is False
    assert modelfinder.find_model([conj], max_size=4) is None
    assert modelfinder.is_satisfiable_finite(conj, max_size=4) is False


# ---------------------------------------------------------------------------
# test_oracle case 3: universal negation alone is satisfiable (no
# over-constraining)
# ---------------------------------------------------------------------------

def test_universal_negation_alone_is_satisfiable():
    """Sanity check that the fix does not OVER-constrain: "every S is
    not-P" is perfectly satisfiable on its own (S non-empty, P false
    everywhere on it) — hand-checked against a direct finite structure.
    """
    g = MSFOL("∀x:S ¬P(x)")
    assert is_satisfiable(g) is True
    assert is_satisfiable_arith(g) is True

    model = get_model(g)
    assert model is not None

    struct = modelfinder.find_model([g], max_size=3)
    assert struct is not None
    assert len(struct.sorts["S"]) >= 1                # S is genuinely non-empty
    assert struct.predicates.get(("P", 1), set()) == set()  # P holds nowhere


# ---------------------------------------------------------------------------
# test_oracle case 4: an invalid sorted entailment whose countermodel needs
# a one-element sort stays REFUTED, with a model where S is non-empty
# ---------------------------------------------------------------------------

def test_invalid_entailment_refuted_with_a_nonempty_one_element_countermodel():
    """Hand-checked: "every S is (P or Q)" does NOT entail "every S is P"
    — a single S-element with Q true and P false already refutes it, so
    the minimal legal (non-empty-S) countermodel has exactly ONE element.
    (An empty-S "model" would NOT refute this particular entailment at all
    — both sides are vacuously true there — so this is the natural minimal
    witness the fix must keep finding, not a case the old bug happened to
    get right by accident.)
    """
    premise = MSFOL("∀x:S (P(x) ∨ Q(x))")
    conclusion = MSFOL("∀x:S P(x)")
    goal = Implies(premise, conclusion)

    assert is_valid(goal) is False

    # The finite model finder's minimal countermodel is exactly 1 element.
    fm_cm = modelfinder.find_countermodel([premise], conclusion, max_size=1)
    assert fm_cm is not None
    assert len(fm_cm.sorts["S"]) == 1

    # Z3's own witness for Not(goal) must satisfy "S is non-empty" directly
    # (checked by evaluating the exact nonempty_sort_axioms sentence against
    # the model Z3 returns — not by string-parsing get_model's repr).
    from z3 import Solver, sat

    solver = Solver()
    solver.add(Not(goal).to_z3())
    axioms = nonempty_sort_axioms(goal)
    assert len(axioms) == 1
    for axiom in axioms:
        solver.add(axiom.to_z3())
    assert solver.check() == sat
    model = solver.model()
    assert bool(model.eval(axioms[0].to_z3(), model_completion=True)) is True

    # api.prove / api.countermodel agree: REFUTED, with a witness.
    verdict = api.prove(conclusion, [premise], backends=["z3"])
    assert verdict.status == REFUTED
    assert verdict.countermodel is not None
    cm = api.countermodel(conclusion, [premise], backends=["z3"])
    assert cm.found is True


# ---------------------------------------------------------------------------
# test_oracle case 5: unsorted controls are byte-identical
# ---------------------------------------------------------------------------

_UNSORTED_PREMISES = [FOL("∀x (Human(x) → Mortal(x))"), FOL("Human(socrates)")]
_UNSORTED_CONCLUSION = FOL("Mortal(socrates)")

_EXPECTED_PROVER9_TEXT = (
    "set(prolog_style_variables).\n"
    "set(auto_denials).\n"
    "clear(print_initial_clauses).\n"
    "clear(print_kept).\n"
    "clear(print_given).\n"
    "\n"
    "formulas(assumptions).\n"
    "  (all X (Human(X) -> Mortal(X))).\n"
    "  Human(socrates).\n"
    "end_of_list.\n"
    "\n"
    "formulas(goals).\n"
    "  Mortal(socrates).\n"
    "end_of_list."
)

_EXPECTED_TPTP_TEXT = (
    "fof(premise_1, axiom, (![X]: (human(X) => mortal(X)))).\n"
    "fof(premise_2, axiom, human(socrates)).\n"
    "fof(goal, conjecture, mortal(socrates)).\n"
)


def test_unsorted_prover9_text_byte_identical():
    text = _generate_prover9_input(_UNSORTED_PREMISES, _UNSORTED_CONCLUSION)
    assert text == _EXPECTED_PROVER9_TEXT
    text2, _mapping = generate_prover9_input_with_mapping(
        _UNSORTED_PREMISES, _UNSORTED_CONCLUSION)
    assert text2 == _EXPECTED_PROVER9_TEXT


def test_unsorted_tptp_fof_text_byte_identical():
    text = generate_tptp_problem(_UNSORTED_PREMISES, _UNSORTED_CONCLUSION)
    assert text == _EXPECTED_TPTP_TEXT
    text2, _mapping = generate_tptp_problem_with_mapping(
        _UNSORTED_PREMISES, _UNSORTED_CONCLUSION)
    assert text2 == _EXPECTED_TPTP_TEXT


def test_unsorted_z3_and_arith_routes_unaffected():
    """nonempty_sort_axioms is empty for every unsorted sentence, so the
    Z3/arith query for an unsorted formula is exactly what it was before
    this fix — pinned against hand-worked, independent expectations.
    """
    assert nonempty_sort_axioms(*_UNSORTED_PREMISES, _UNSORTED_CONCLUSION) == ()

    goal = Implies(And(*_UNSORTED_PREMISES), _UNSORTED_CONCLUSION)
    assert is_valid(goal) is True                 # modus ponens, hand-checked
    assert is_valid_arith(goal) is True
    assert is_satisfiable(FOL("P ∧ ¬P")) is False  # classic contradiction
    assert is_satisfiable_arith(FOL("P ∧ ¬P")) is False


def test_unsorted_equivalence_route_unaffected():
    f1 = FOL("¬(P(x) ∧ Q(x))")
    f2 = FOL("¬P(x) ∨ ¬Q(x)")                       # De Morgan, hand-checked
    result = equivalent(f1, f2, method="solver")
    assert result.equivalent is True
    assert result.counterexample is None


# ---------------------------------------------------------------------------
# The shared helper itself
# ---------------------------------------------------------------------------

def test_nonempty_sort_axioms_dedups_and_orders_by_first_occurrence():
    f1 = MSFOL("∀x:B P(x)")
    f2 = MSFOL("∀x:A Q(x) ∧ ∃y:B R(y)")             # B repeated, A new
    axioms = nonempty_sort_axioms(f1, f2)
    sorts_seen = [a.formula.predicate for a in axioms]  # Atom(sort, [x])
    assert sorts_seen == ["B", "A"]                  # first-occurrence order, deduped


def test_nonempty_sort_axioms_covers_all_four_sorted_node_types():
    from unicode_logic_kit.fol.nodes import SortedCount, SortedCardinality, Number, Variable

    quantifier = MSFOL("∀x:Q1 P(x)")
    constant = SortedConstant("c", "Q2")
    count = SortedCount("ge", Number(1), Variable("x"), "Q3", FOL("R(x)"))
    cardinality = SortedCardinality(Variable("y"), "Q4", FOL("R(y)"))
    axioms = nonempty_sort_axioms(quantifier, constant, count, cardinality)
    sorts_seen = {a.formula.predicate for a in axioms}
    assert sorts_seen == {"Q1", "Q2", "Q3", "Q4"}


def test_nonempty_sort_axioms_empty_for_plain_fol():
    assert nonempty_sort_axioms(*_UNSORTED_PREMISES, _UNSORTED_CONCLUSION) == ()
    assert nonempty_sort_axioms() == ()


# ---------------------------------------------------------------------------
# atp.protocol: Z3Backend and z3_relevant_premises must agree
# ---------------------------------------------------------------------------

def test_z3_relevant_premises_agrees_with_z3_backend_on_sorted_entailment():
    """z3_relevant_premises must reach the SAME verdict as Z3Backend.decide
    on many-sorted input — both must add the identical non-emptiness axioms
    (see _z3_track_and_check's z3_sort_axioms parameter), or the
    two could silently disagree about whether the entailment even holds.
    """
    premise = MSFOL("∀x:Human Mortal(x)")
    conclusion = MSFOL("∃x:Human Mortal(x)")
    verdict = Z3.decide(conclusion, [premise])
    assert verdict.status == PROVED
    indices = z3_relevant_premises(conclusion, [premise])
    assert indices == (0,)


# ---------------------------------------------------------------------------
# cvc5 — a second, independent SMT decision procedure (skipif-gated)
# ---------------------------------------------------------------------------

@pytest.mark.skipif(not Cvc5Backend().available(), reason="cvc5 package not installed")
def test_cvc5_agrees_on_the_reproduction_case():
    f = MSFOL("(∀x:Human Mortal(x)) → ∃x:Human Mortal(x)")
    verdict = Cvc5Backend().decide(f)
    assert verdict.status == PROVED

    conj = And(MSFOL("∀x:S P(x)"), MSFOL("∀x:S ¬P(x)"))
    # decide(conj) asks "does {} entail conj" i.e. is conj VALID; conj is
    # not valid (it is actually unsatisfiable), so this must NOT be PROVED.
    # Check unsatisfiability directly instead, entailment-style: conj ⊨ ⊥
    # is the same question as "¬conj is valid".
    refuted_conj = Cvc5Backend().decide(Not(conj))
    assert refuted_conj.status == PROVED           # ¬(P∧¬P over non-empty S) is valid


# ---------------------------------------------------------------------------
# WSL Vampire / E — the TF0 route as an independent oracle (skipif-gated,
# exactly like tests/test_tptp_tff.py's own live tests)
# ---------------------------------------------------------------------------

def _wsl_vampire_ok() -> bool:
    try:
        result = subprocess.run(["wsl.exe", "vampire", "--version"],
                                capture_output=True, text=True, timeout=20)
        return result.returncode == 0 and "Vampire" in result.stdout
    except Exception:  # noqa: BLE001 -- any failure means "not available"
        return False


_VAMPIRE = shutil.which("vampire")
_WSL_VAMPIRE = _wsl_vampire_ok()
_HAVE_VAMPIRE = _VAMPIRE is not None or _WSL_VAMPIRE


def _vampire_kwargs():
    if _VAMPIRE is not None:
        return dict(vampire_path=_VAMPIRE, use_wsl=False)
    return dict(vampire_path="vampire", use_wsl=True)


@pytest.mark.skipif(not _HAVE_VAMPIRE, reason="no Vampire binary reachable (native or WSL)")
def test_fof_and_tff_routes_agree_via_vampire_on_the_reproduction_case():
    """The fof (atp._tptp_problem, S1's fix) and tff (native TPTP TF0,
    already correct) routes must now agree — see
    tests/test_tptp_tff.py::test_tff_and_fof_routes_agree_on_non_emptiness_via_vampire
    for the same check against the Ghost battery this item's own report
    documents in detail; this is the exact reproduction case, checked here
    directly rather than via that module's own fixtures.
    """
    premise = MSFOL("∀x:Human Mortal(x)")
    conclusion = MSFOL("∃x:Human Mortal(x)")
    kwargs = _vampire_kwargs()
    assert check_logical_entailment_vampire([premise], conclusion, tff=False, **kwargs) is True
    assert check_logical_entailment_vampire([premise], conclusion, tff=True, **kwargs) is True


@pytest.mark.skipif(not eprover_available(), reason="no eprover binary found")
def test_fof_and_tff_routes_agree_via_eprover_on_the_reproduction_case():
    premise = MSFOL("∀x:Human Mortal(x)")
    conclusion = MSFOL("∃x:Human Mortal(x)")
    fof = check_entailment_eprover_detailed([premise], conclusion, tff=False)
    tff = check_entailment_eprover_detailed([premise], conclusion, tff=True)
    assert fof["status"] == "proved"
    assert tff["status"] == "proved"


# ---------------------------------------------------------------------------
# atp.z3_equivalence, and the one route left incomplete (not unsound).
# ---------------------------------------------------------------------------

def test_z3_equivalence_assumes_non_empty_sorts():
    """Both formulas are tautologies under non-empty sorts (f1 is the
    reproduction case, f2 a propositional tautology), so they are equivalent.
    Without the non-emptiness assertion Z3 makes Human empty and says no."""
    from unicode_logic_kit.atp.z3_equivalence import formulas_are_equivalent

    f1 = MSFOL("(∀x:Human Mortal(x)) → ∃x:Human Mortal(x)")
    f2 = FOL("P ∨ ¬P")
    assert formulas_are_equivalent(f1, f2) is True
    # A genuine difference is still found: ∀x:Human Mortal(x) is not a tautology.
    assert formulas_are_equivalent(MSFOL("∀x:Human Mortal(x)"), f2) is False


def test_resolution_gets_the_non_emptiness_of_a_sort_as_a_premise():
    """atp.resolution.prove clausifies each formula through
    fol.normalforms.skolemize's own to_fol call, which drops the fact that a
    sort is non-empty, exactly like the Z3/cvc5/TPTP routes' reductions do.
    ``∀x:Ghost P(x) ⊢ ∃x:Ghost P(x)`` is valid in the many-sorted semantics
    (Ghost has an element, and it is a P) and was NOT proved here: resolution
    is refutation-only, so dropping the non-emptiness axiom never made it
    prove something false, but it made this valid entailment unprovable.
    The old expectation (``False``, "INCOMPLETE, not wrong") pinned that gap
    as if it were intended. ``prove`` now adds ``sort_axioms`` (non-emptiness
    of every sort, membership of every sorted constant) as premise clauses,
    so the proof is found; the soundness side is pinned next to it.
    """
    from unicode_logic_kit.atp.resolution import prove

    premise = MSFOL("∀x:Ghost P(x)")
    conclusion = MSFOL("∃x:Ghost P(x)")
    assert prove([premise], conclusion, max_steps=2000) is True
    # and the fact is a PREMISE, not part of the negated conclusion: a sort that
    # is merely non-empty proves nothing about P
    assert prove([], MSFOL("∃x:Ghost P(x)"), max_steps=2000) is False
