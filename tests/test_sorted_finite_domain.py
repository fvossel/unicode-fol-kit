"""Tests for ``unicode_fol_kit.atp.finite_domain.lower_msfol`` — the
many-sorted-to-classical front door both :class:`ClingoBackend
<unicode_fol_kit.atp.clingo_backend.ClingoBackend>` and :class:`MinizincBackend
<unicode_fol_kit.atp.minizinc_backend.MinizincBackend>` now run their
refutation-goal sentences through before ``fragment_check`` (or, for
MiniZinc, ``Signature.from_formulas``) ever sees them.

Five things, five sections below:

* ``TestLowerMsfolUnit`` — the function's own contract, exercised in
  isolation: the fast-path no-op (byte-identical output, not even
  round-tripped through ``to_fol``, for every sentence batch with no sorted
  node), and the exact hand-derived shape of what it produces when a sorted
  node IS present (relativised body, sort facts, one non-emptiness sentence
  per DISTINCT sort name in first-occurrence order, ``TypeError`` on a
  non-``Node`` member).
* ``TestNonemptinessAxiomNecessity`` — pins the ONE soundness argument this
  whole feature exists to protect, structurally: a hand-built structure that
  would be a (WRONG) countermodel of the bare ``to_fol`` relativisation
  alone is shown, by direct construction (no solver needed), to violate the
  non-emptiness sentence ``lower_msfol`` adds — so it can never survive as
  an ASP/CP countermodel once that sentence is conjoined in.
* ``TestClingoSortedDifferential`` — the required independent-route
  differential: :class:`ClingoBackend` (``clingo`` 5.8.1 is installed, so
  this drives the real solver) against
  :func:`~unicode_fol_kit.semantics.modelfinder.find_countermodel`, the
  kit's OWN from-scratch many-sorted brute-force finder, over a hand-picked
  corpus covering every shape the build spec names: two disjoint sorts with
  a cross-sort relation, a sort-restricted ``∀`` that is vacuously true only
  if its sort could be empty, and a ``SortedCount``. Every REFUTED verdict
  is additionally re-verified independently against the LOWERED sentences
  with :func:`~unicode_fol_kit.atp.finite_domain.verify_model`. A textbook
  sorted syllogism is cross-checked a THIRD way, against Z3's own
  ``to_fol``-based route (``SortedQuantifier.to_z3`` auto-reduces through
  :func:`~unicode_fol_kit.fol.nodes.to_fol`, matching
  :mod:`~unicode_fol_kit.atp.z3_arith`'s documented pattern).
* ``TestSortedCardinalityComparison`` — a ``SortedCardinality`` comparison
  against a numeral, differentially tested against ``modelfinder`` in both
  directions, plus the unsorted analogue. Building this corpus exposed a
  bug in :mod:`~unicode_fol_kit.semantics.tarski`: a numeral next to a
  cardinality was read through ``structure.constants``, so the model finder
  could reinterpret the ``1`` in ``|{…}| > 1`` as another individual and
  report a countermodel to a valid entailment. The evaluator now reads such
  a numeral as the number itself; these tests pin that.
* ``TestMinizincSortedWiring`` — :class:`MinizincBackend` gets the identical
  ``lower_msfol`` call in its own ``decide()``; MiniZinc itself is not
  installed in this environment (see ``tests/test_minizinc_backend.py``'s
  own docstring), so this is exercised OFFLINE via the established
  ``minizinc_path=`` + monkeypatched ``_run_minizinc`` technique that
  file's own ``decide()`` tests use, confirming the sorted goal is rendered,
  solved (by the fake), reconstructed, and independently re-verified against
  the LOWERED sentences end to end.

Every expected value below is worked out from the input by hand (see each
test's own comment for the derivation), never captured from a run of the
module under test.
"""

import pathlib
import re

import pytest

clingo = pytest.importorskip("clingo")

import z3

from unicode_fol_kit import MSFLParser
from unicode_fol_kit.fol.nodes import (
    Variable, Constant, Number, Atom, And, Implies, Not, Quantifier,
    SortedQuantifier, SortedConstant, Count, to_fol,
)
from unicode_fol_kit.semantics import (
    FiniteStructure, structure_from_dict, evaluate_in_structure,
)
from unicode_fol_kit.semantics.modelfinder import find_countermodel
from unicode_fol_kit.atp.finite_domain import (
    FiniteDomainProblem, fragment_check, lower_msfol, verify_model,
)
from unicode_fol_kit.atp.clingo_backend import ClingoBackend, _universal_closure, to_asp
from unicode_fol_kit.atp import minizinc_backend as mb
from unicode_fol_kit.atp.protocol import ERROR, REFUTED, UNKNOWN

_S = MSFLParser(many_sorted=True)   # every quantifier/constant must carry a sort
_F = MSFLParser()                    # plain, unsorted FOL
_backend = ClingoBackend()

# Generous but fast: every corpus formula below is small, and every
# hand-derived countermodel fits well inside this bound.
_MAX_SIZE = 5


# =============================================================================
# lower_msfol -- the function's own contract, in isolation
# =============================================================================

class TestLowerMsfolUnit:
    def test_fast_path_returns_unsorted_sentences_untouched(self):
        # No SortedQuantifier/SortedConstant/SortedCount/SortedCardinality
        # anywhere -- the module docstring's "no-op guarantee". Compared by
        # structural equality (Node is a frozen dataclass) AND by rendering
        # both through to_asp, pinning that the ENCODED program text is
        # byte-identical too, not merely that the AST happens to compare
        # equal. The sentences are closed (``alpha`` is a constant; a single letter would be
        # a free variable, which the writer refuses).
        sentences = (_F.parse("∀x (P(x) → Q(x))"), _F.parse("P(alpha)"))
        result = lower_msfol(sentences)
        assert result == sentences
        assert to_asp(FiniteDomainProblem(result, 2)) == to_asp(FiniteDomainProblem(sentences, 2))

    def test_fast_path_coerces_a_list_to_a_tuple(self):
        sentences = [_F.parse("P(a)")]
        result = lower_msfol(sentences)
        assert result == (sentences[0],)
        assert type(result) is tuple

    def test_fast_path_is_a_true_no_op_even_with_count_and_contrast(self):
        # Count/Contrast are ALSO touched by to_fol's own _reduce_nl_nodes
        # step (Count is expanded, Contrast collapsed to And) -- the fast
        # path must never let that machinery run at all when nothing is
        # sorted, or these two node types would change shape for every
        # PRE-EXISTING unsorted test that uses them.
        count_sentence = _F.parse("∃≥2 x P(x)")
        contrast_sentence = _F.parse("P(a) Ⓒ Q(a)")
        result = lower_msfol((count_sentence, contrast_sentence))
        assert result == (count_sentence, contrast_sentence)
        assert type(result[0]).__name__ == "Count"
        assert type(result[1]).__name__ == "Contrast"

    def test_mixed_batch_leaves_an_unrelated_count_sentence_completely_untouched(self):
        # A batch with ONE sorted sentence and one UNRELATED Count sentence:
        # only the sorted sentence may be routed through to_fol. to_fol's
        # own third phase (_reduce_nl_nodes) would otherwise expand the
        # Count node into a nested-quantifier distinct-witnesses tree (and,
        # for n > 500, raise NotImplementedError outright) even though this
        # Count sentence has nothing to do with sorting -- exactly the
        # regression a batch-wide (rather than per-sentence) to_fol call
        # would silently reintroduce. Checked by identity, not just
        # structural equality, since an untouched sentence must be the SAME
        # object, never merely an equal rebuild.
        count_sentence = _F.parse("∃≥2 x P(x)")
        sorted_sentence = SortedQuantifier("∀", Variable("x"), "Human",
                                            Atom("Mortal", [Variable("x")]))
        result = lower_msfol((count_sentence, sorted_sentence))
        assert len(result) == 3   # unrelated Count + relativised sorted sentence + 1 nonempty
        assert result[0] is count_sentence
        assert type(result[0]).__name__ == "Count"

    def test_mixed_batch_does_not_crash_on_a_count_past_to_fols_own_expansion_bound(self):
        # to_fol's Count expansion (_reduce_nl_nodes -> Count._expand) raises
        # NotImplementedError above n=500 (unicode_fol_kit/fol/_fol_nodes.py,
        # _COUNT_EXPAND_MAX). n=600 here is unrelated to sorting -- it is
        # only reachable through the batch-wide bug this regression test
        # guards against: routing EVERY sentence through to_fol as soon as
        # ANY sentence anywhere is sorted, which would make an otherwise
        # perfectly fine (clingo encodes Count natively, with no such bound)
        # large-n Count premise crash decide() outright instead of returning
        # a Verdict. lower_msfol itself must not raise here, and the
        # unrelated Count sentence must come back completely untouched.
        count_sentence = Count("ge", Number(600), Variable("x"), Atom("P", [Variable("x")]))
        sorted_sentence = SortedQuantifier("∀", Variable("y"), "Dummy", Atom("Q", [Variable("y")]))
        result = lower_msfol((count_sentence, sorted_sentence))
        assert result[0] is count_sentence

    def test_clingo_decide_does_not_crash_on_a_mixed_batch_past_the_expansion_bound(self):
        # End-to-end regression for the same scenario through the real
        # backend entry point: decide() must return a Verdict, never let
        # NotImplementedError propagate out uncaught (both backends already
        # catch NotImplementedError elsewhere in this same method for other
        # reasons, confirming a Verdict-only contract this call site must
        # also honour).
        count_premise = Count("ge", Number(600), Variable("x"), Atom("P", [Variable("x")]))
        sorted_premise = SortedQuantifier("∀", Variable("y"), "Dummy", Atom("Q", [Variable("y")]))
        v = _backend.decide(Atom("Z", []), [count_premise, sorted_premise], max_size=2)
        # Any real Verdict status is acceptable here -- the point of this
        # test is solely that decide() returns one at all instead of
        # letting NotImplementedError propagate. PROVED is omitted: for
        # this corpus entry decide() cannot conclude validity from a bound
        # search that never exhausts the Count premise's own >=600 bound,
        # so it is not a status this scenario can actually produce.
        assert v.status in (UNKNOWN, REFUTED, ERROR)

    def test_forall_relativised_with_nonempty_sentence_appended(self):
        # ∀x:Human Mortal(x), negated as a refutation goal would be, is the
        # ONLY sorted sentence -- hand-derived shape: the relativised
        # Implies-guarded universal, plus exactly one extra ∃x (Human(x))
        # sentence.
        f = SortedQuantifier("∀", Variable("x"), "Human",
                             Atom("Mortal", [Variable("x")]))
        result = lower_msfol((f,))
        assert len(result) == 2

        relativised = result[0]
        assert relativised == Quantifier(
            "∀", Variable("x"),
            Implies(Atom("Human", [Variable("x")]), Atom("Mortal", [Variable("x")])),
        )

        nonempty = result[1]
        assert type(nonempty) is Quantifier and nonempty.type == "∃"
        assert type(nonempty.variable) is Variable
        assert nonempty.formula == Atom("Human", [nonempty.variable])

    def test_sorted_constant_fact_is_asserted_not_merely_used_as_a_guard(self):
        # include_sort_facts=True is load-bearing: without it, alice's
        # membership in Human would be silently lost by relativisation (she
        # becomes a bare Constant with no trace of her sort), which would
        # break e.g. "alice:Human, ∀x:Human Mortal(x) |- Mortal(alice)".
        f = Atom("P", [SortedConstant("alice", "Human")])
        result = lower_msfol((f,))
        assert len(result) == 2
        assert result[0] == And(Atom("Human", [Constant("alice")]), Atom("P", [Constant("alice")]))

    def test_distinct_sorts_get_one_nonempty_sentence_each_in_first_occurrence_order(self):
        # Sort "B" is referenced (inside the SECOND sentence) before sort
        # "A"'s own second occurrence -- first-occurrence order across the
        # WHOLE batch is: A (sentence 1), B (sentence 2).
        s1 = SortedQuantifier("∀", Variable("x"), "A", Atom("P", [Variable("x")]))
        s2 = And(SortedQuantifier("∃", Variable("y"), "B", Atom("Q", [Variable("y")])),
                SortedQuantifier("∀", Variable("z"), "A", Atom("R", [Variable("z")])))
        result = lower_msfol((s1, s2))
        # 2 relativised sentences + 2 nonempty sentences (one per distinct sort).
        assert len(result) == 4
        nonempty_sorts = [n.formula.predicate for n in result[2:]]
        assert nonempty_sorts == ["A", "B"]

    def test_duplicate_sort_reference_collapses_to_one_nonempty_sentence(self):
        # "Human" is referenced by TWO different sentences -- still exactly
        # one non-emptiness sentence for it, not two (a redundant duplicate
        # constraint would be sound but is not what the docstring promises:
        # "one extra sentence PER DISTINCT sort name").
        s1 = SortedQuantifier("∀", Variable("x"), "Human", Atom("P", [Variable("x")]))
        s2 = SortedQuantifier("∃", Variable("y"), "Human", Atom("Q", [Variable("y")]))
        result = lower_msfol((s1, s2))
        assert len(result) == 3   # 2 relativised + exactly 1 nonempty
        assert result[2].formula.predicate == "Human"

    def test_purity_does_not_mutate_the_input(self):
        f = SortedQuantifier("∀", Variable("x"), "Human", Atom("P", [Variable("x")]))
        _ = lower_msfol((f,))
        assert type(f) is SortedQuantifier and f.sort == "Human"

    def test_non_node_member_raises_type_error(self):
        with pytest.raises(TypeError, match="Node"):
            lower_msfol(["not a formula"])

    def test_fragment_check_accepts_the_lowered_output(self):
        # The whole point: fragment_check itself is untouched and never
        # sees a Sorted* node once lower_msfol has run.
        f = SortedQuantifier("∀", Variable("x"), "Human", Atom("Mortal", [Variable("x")]))
        assert fragment_check(lower_msfol((f,))) is None

    def test_fragment_check_still_refuses_a_raw_sorted_node_directly(self):
        # Defense in depth (module docstring): a caller that builds a
        # FiniteDomainProblem WITHOUT going through lower_msfol first still
        # gets refused, by name, exactly as before this change.
        f = SortedQuantifier("∀", Variable("x"), "Human", Atom("P", [Variable("x")]))
        msg = fragment_check([f])
        assert msg is not None and msg.startswith("SortedQuantifier is not encodable:")


# =============================================================================
# The non-emptiness sentence: why it is required, shown by direct
# construction (no solver -- this is the semantic argument itself).
# =============================================================================

class TestNonemptinessAxiomNecessity:
    def test_bare_relativisation_alone_admits_a_spurious_countermodel(self):
        # (∀x:S P(x)) -> (∃x:S P(x)) is a textbook MSFOL validity -- valid
        # ONLY because a sort's universe is, by convention, never empty
        # (mirrors "existential import" in unsorted FOL with a mandatory
        # non-empty domain). Hand-derivation: a 1-element structure with
        # S=∅ makes the antecedent vacuously TRUE and the consequent FALSE,
        # so the whole implication is FALSE there -- its NEGATION is
        # satisfied, i.e. this structure is a (WRONG, since S must not be
        # empty) countermodel of the bare relativisation.
        conclusion = _S.parse("(∀x:S P(x)) → (∃x:S P(x))")
        goal = Not(conclusion)   # no free variables; closure is a no-op here
        bare = to_fol(goal, include_sort_facts=True)

        spurious = FiniteStructure(
            domain=("0",),
            extensions={("S", 1): frozenset(), ("P", 1): frozenset()},
            constants={},
        )
        assert evaluate_in_structure(bare, spurious) is True

    def test_lower_msfol_adds_a_sentence_that_sentence_violates(self):
        # The SAME spurious structure above must FAIL the extra non-emptiness
        # sentence lower_msfol conjoins in -- so once every lowered sentence
        # must hold SIMULTANEOUSLY (as FiniteDomainProblem requires), that
        # structure is no longer a candidate model at all.
        conclusion = _S.parse("(∀x:S P(x)) → (∃x:S P(x))")
        goal = Not(conclusion)
        lowered = lower_msfol((goal,))
        assert len(lowered) == 2   # the relativised goal + one nonempty sentence

        spurious = FiniteStructure(
            domain=("0",),
            extensions={("S", 1): frozenset(), ("P", 1): frozenset()},
            constants={},
        )
        nonempty_sentence = lowered[1]
        assert evaluate_in_structure(nonempty_sentence, spurious) is False

    def test_clingo_agrees_the_entailment_is_valid_up_to_the_bound(self):
        # End-to-end confirmation through the real pipeline: with the
        # non-emptiness sentence actually wired in via ClingoBackend.decide,
        # no countermodel is found up to max_size -- UNKNOWN/"bound_hit",
        # matching the hand-derived validity above (and matching
        # modelfinder's OWN non-empty-sort convention, since
        # find_countermodel enumerates only non-empty sort universes).
        conclusion = _S.parse("(∀x:S P(x)) → (∃x:S P(x))")
        v = _backend.decide(conclusion, [], max_size=_MAX_SIZE)
        assert v.status == UNKNOWN
        assert v.reason == "bound_hit"

        mf = find_countermodel([], conclusion, max_size=_MAX_SIZE)
        assert mf is None


# =============================================================================
# Differential vs. semantics.modelfinder.find_countermodel (many-sorted)
# =============================================================================

# (name, premise strings, conclusion string, expect_refuted) -- expect_refuted
# is hand-derived from the entailment's classical (many-sorted) validity,
# independent of either implementation under test.
_SORTED_DIFFERENTIAL_CORPUS = [
    # Two disjoint sorts (Dog, Person) with a cross-sort relation. The
    # classic quantifier-swap fallacy, sorted: "every dog has SOME owner"
    # does NOT entail "some person owns EVERY dog" -- countermodel: two
    # dogs, two owners, each dog owned by a DIFFERENT person.
    ("cross_sort_quantifier_swap_fallacy",
     ["∀x:Dog ∃y:Person Owns(y,x)"], "∃y:Person ∀x:Dog Owns(y,x)", True),
    # The same two sorts, a VALID entailment: instantiating the universal
    # at a named Dog and modus-ponens-ing through the existential.
    ("cross_sort_modus_ponens",
     ["∀x:Dog ∃y:Person Owns(y,x)", "Dog(rex:Dog)"],
     "∃y:Person Owns(y, rex:Dog)", False),
    # SortedCount: one witness does not entail "at least two".
    ("sorted_count_not_entailed_by_a_single_witness",
     ["Ripe(apple:Fruit)"], "∃≥2 x:Fruit Ripe(x)", True),
    # SortedCount: two NAMED, PROVABLY DISTINCT witnesses do entail it.
    ("sorted_count_entailed_by_two_distinct_witnesses",
     ["Ripe(apple:Fruit)", "Ripe(pear:Fruit)", "apple:Fruit ≠ pear:Fruit"],
     "∃≥2 x:Fruit Ripe(x)", False),
    # Textbook sorted syllogism (Human/Mortal/Socrates).
    ("textbook_sorted_syllogism",
     ["∀x:Human Mortal(x)"], "Mortal(socrates:Human)", False),
]


def test_clingo_sorted_differential_agrees_with_modelfinder():
    """The required independent-route check: over the corpus above,
    :class:`ClingoBackend` (via :func:`lower_msfol`) and
    :func:`~unicode_fol_kit.semantics.modelfinder.find_countermodel` (the
    kit's OWN, unrelated many-sorted brute-force search — see that module's
    own MSFOL enumeration, ``_sorted_interpretations``) must agree on
    REFUTED-vs-not at the same ``max_size``. A disagreement names the entry.
    """
    mismatches = []
    for name, premise_strs, conclusion_str, expect_refuted in _SORTED_DIFFERENTIAL_CORPUS:
        premises = [_S.parse(s) for s in premise_strs]
        conclusion = _S.parse(conclusion_str)

        mf_countermodel = find_countermodel(premises, conclusion, max_size=_MAX_SIZE)
        mf_refuted = mf_countermodel is not None

        v = _backend.decide(conclusion, premises, max_size=_MAX_SIZE)
        clingo_refuted = v.status == REFUTED

        if mf_refuted != clingo_refuted or clingo_refuted != expect_refuted:
            mismatches.append(
                f"{name!r}: modelfinder_refuted={mf_refuted}, "
                f"clingo_status={v.status}/{v.reason}, expected_refuted={expect_refuted}"
            )

    assert not mismatches, "differential disagreement(s): " + "; ".join(mismatches)


def test_clingo_sorted_refutations_independently_reverify_against_lowered_sentences():
    """Every REFUTED entry's countermodel is re-checked a SECOND independent
    way: reconstructing the exact ``lower_msfol``-lowered refutation goal
    (not trusting ``ClingoBackend``'s own internal ``verify_model`` call —
    an oracle this test builds itself) and re-evaluating it with
    ``evaluate_in_structure``.
    """
    for name, premise_strs, conclusion_str, expect_refuted in _SORTED_DIFFERENTIAL_CORPUS:
        if not expect_refuted:
            continue
        premises = [_S.parse(s) for s in premise_strs]
        conclusion = _S.parse(conclusion_str)

        v = _backend.decide(conclusion, premises, max_size=_MAX_SIZE)
        assert v.status == REFUTED, name
        structure = structure_from_dict(v.countermodel["data"])

        goal = Not(_universal_closure(conclusion))
        sentences = tuple(_universal_closure(p) for p in premises) + (goal,)
        lowered = lower_msfol(sentences)
        assert verify_model(structure, lowered) is None, name


def test_textbook_sorted_syllogism_has_no_countermodel_cross_checked_with_z3():
    """(∀x:Human Mortal(x)) ∧ socrates:Human ⊨ Mortal(socrates) — the
    textbook syllogism, sorted. Three independent routes must all agree it
    is VALID:

    1. :class:`ClingoBackend`: UNKNOWN/``"bound_hit"`` up to ``max_size``
       (never PROVED — first-order logic has no finite model property, so
       this is the strongest a refutation-only search can honestly say).
    2. :func:`~unicode_fol_kit.semantics.modelfinder.find_countermodel`:
       ``None`` (its own, from-scratch many-sorted enumeration finds
       nothing either).
    3. Z3, via the SAME lowering this backend uses
       (:meth:`SortedQuantifier.to_z3` auto-reduces through
       :func:`~unicode_fol_kit.fol.nodes.to_fol` — see
       :mod:`~unicode_fol_kit.atp.z3_arith`'s documented pattern): the
       negation of the implication is UNSAT.
    """
    premise = _S.parse("∀x:Human Mortal(x)")
    socrates_is_human = _S.parse("Human(socrates:Human)")
    conclusion = _S.parse("Mortal(socrates:Human)")

    v = _backend.decide(conclusion, [premise, socrates_is_human], max_size=_MAX_SIZE)
    assert v.status == UNKNOWN and v.reason == "bound_hit"

    assert find_countermodel([premise, socrates_is_human], conclusion, max_size=_MAX_SIZE) is None

    implication = Implies(And(premise, socrates_is_human), conclusion)
    solver = z3.Solver()
    solver.add(z3.Not(implication.to_z3()))
    assert solver.check() == z3.unsat


# =============================================================================
# A SortedCardinality comparison against a numeral.
# =============================================================================

class TestSortedCardinalityComparison:
    """``|{x:Student : Pass(x)}| > 1`` against the model finder, in both
    directions. The model finder enumerates an interpretation for every numeral
    it scans, including the ``1`` here; the evaluator must still read that ``1``
    as the number one next to a count, or it reports a spurious countermodel to
    the valid direction (it did, before the fix in ``semantics.tarski``)."""

    def test_the_unsorted_valid_entailment_has_no_countermodel(self):
        # Two named, distinct passers entail "more than one passer": any model
        # of the premises has ann and bob in Pass with ann ≠ bob, so the count
        # is at least 2.
        premises = [_F.parse(s) for s in ["Pass(ann)", "Pass(bob)", "ann ≠ bob"]]
        conclusion = _F.parse("|{x : Pass(x)}| > 1")
        assert find_countermodel(premises, conclusion, max_size=_MAX_SIZE) is None

    def test_sorted_cardinality_valid_entailment_agrees_with_modelfinder(self):
        # |{x:Student : Pass(x)}| > 1 is entailed by two named, distinct passing
        # students: any model of the premises has ann and bob, both Student and
        # Pass, with ann ≠ bob, so the guarded count has at least 2 members.
        # Neither route may find a countermodel up to the bound.
        premises = [_S.parse(s) for s in
                   ["Pass(ann:Student)", "Pass(bob:Student)", "ann:Student ≠ bob:Student"]]
        conclusion = _S.parse("|{x:Student : Pass(x)}| > 1")

        v = _backend.decide(conclusion, premises, max_size=_MAX_SIZE)
        assert v.status == UNKNOWN and v.reason == "bound_hit"
        assert find_countermodel(premises, conclusion, max_size=_MAX_SIZE) is None

    def test_sorted_cardinality_invalid_entailment_agrees_with_modelfinder(self):
        # One passing student does not entail more than one: a structure with
        # ann as the only Student is a countermodel, and both routes find one.
        premises = [_S.parse("Pass(ann:Student)")]
        conclusion = _S.parse("|{x:Student : Pass(x)}| > 1")

        mf = find_countermodel(premises, conclusion, max_size=_MAX_SIZE)
        v = _backend.decide(conclusion, premises, max_size=_MAX_SIZE)
        assert mf is not None
        assert v.status == REFUTED

        structure = structure_from_dict(v.countermodel["data"])
        goal = Not(_universal_closure(conclusion))
        sentences = tuple(_universal_closure(p) for p in premises) + (goal,)
        assert verify_model(structure, lower_msfol(sentences)) is None


# =============================================================================
# MinizincBackend -- the identical wiring, exercised offline (MiniZinc is
# not installed in this environment; see tests/test_minizinc_backend.py's
# own docstring for the established gating/mocking pattern this reuses).
# =============================================================================

def _size_of(model_path: str) -> int:
    text = pathlib.Path(model_path).read_text(encoding="utf-8")
    match = re.search(r"int: n = (\d+);", text)
    assert match is not None
    return int(match.group(1))


def _fake_run_at_size(target_size: int, stdout_at_target: str):
    """Answers UNSAT below ``target_size`` and ``stdout_at_target`` exactly
    at it — the same technique ``tests/test_minizinc_backend.py``'s own
    ``_fake_run_at_size`` fixture uses, reproduced locally so this file does
    not import test internals from a sibling test module."""
    def fake_run(model_path, binary, solver, time_limit_ms):
        if _size_of(model_path) == target_size:
            return stdout_at_target, "", False
        return "=====UNSATISFIABLE=====\n", "", False
    return fake_run


class TestMinizincSortedWiring:
    def test_decide_lowers_sorted_input_and_independently_reverifies(self, monkeypatch):
        # ∀x:Human Mortal(x), given alice:Human, is being asked as the goal
        # -- NOT entailed by nothing (no premise ties alice to Mortal), so a
        # countermodel exists: hand-picked structure {0, 1}, Human={0,1},
        # Mortal={1} (alice=0 is Human but not Mortal, violating the goal),
        # 0 witnesses the non-emptiness sentence too. Encoded to the exact
        # "UFK ..." wire format to_minizinc/_atoms_from_solution use.
        formula = _S.parse("∀x:Human Mortal(x)")
        premises = [_S.parse("Human(alice:Human)")]
        stdout_at_2 = (
            "UFK-SOLUTION-BEGIN\n"
            "UFK p_Human 1 [true, true]\n"
            "UFK p_Mortal 1 [false, true]\n"
            "UFK k_alice 0 0\n"
            "UFK-SOLUTION-END\n----------\n"
        )
        monkeypatch.setattr(mb, "_run_minizinc", _fake_run_at_size(2, stdout_at_2))

        backend = mb.MinizincBackend()
        v = backend.decide(formula, premises, max_size=2, minizinc_path="FAKE")
        assert v.status == REFUTED
        assert v.reason is None

        structure = structure_from_dict(v.countermodel["data"])
        assert structure.domain == ("0", "1")
        assert structure.extensions[("Human", 1)] == frozenset({("0",), ("1",)})
        assert structure.extensions[("Mortal", 1)] == frozenset({("1",)})
        assert structure.constants["alice"] == "0"

        # Independent re-verification against the LOWERED sentences (not
        # trusting decide()'s own internal verify_model call).
        sentences = tuple(premises) + (Not(formula),)
        lowered = lower_msfol(sentences)
        assert verify_model(structure, lowered) is None

    def test_decide_bound_hit_for_a_valid_sorted_entailment(self, monkeypatch):
        # (∀x:Human Mortal(x)) ∧ socrates:Human ⊨ Mortal(socrates) is valid
        # (see the Z3/modelfinder/clingo triple-check above) -- MiniZinc
        # (fake) reports UNSATISFIABLE at every size, so no countermodel is
        # found up to max_size.
        monkeypatch.setattr(
            mb, "_run_minizinc",
            lambda *a, **k: ("=====UNSATISFIABLE=====\n", "", False))
        premise = _S.parse("∀x:Human Mortal(x)")
        human = _S.parse("Human(socrates:Human)")
        conclusion = _S.parse("Mortal(socrates:Human)")

        backend = mb.MinizincBackend()
        v = backend.decide(conclusion, [premise, human], max_size=2, minizinc_path="FAKE")
        assert v.status == UNKNOWN
        assert v.reason == "bound_hit"


# =============================================================================
# Sorted function symbols -- the explicit C26 decision: admitted by node
# TYPE (Function is now generally encodable), refused by DECLARATION (a
# FunctionDecl carrying arg_sorts/result_sort). There is no `SortedFunction`
# AST node -- the many-sorted family above (SortedQuantifier/SortedConstant/
# SortedCount/SortedCardinality) does not cover function symbols at all --
# so this is a Signature-level refusal in FiniteDomainProblem itself, not
# something lower_msfol or fragment_check can catch by walking `sentences`.
# =============================================================================

class TestSortedFunctionSymbolsRefused:
    def test_arg_sorts_is_refused(self):
        from unicode_fol_kit.fol.signature import Signature, FunctionDecl
        sig = Signature(functions={"f": FunctionDecl("f", 1, arg_sorts=("Human",))})
        with pytest.raises(ValueError, match="sorted function symbol"):
            FiniteDomainProblem((Atom("P", [Variable("x")]),), 2, signature=sig)

    def test_result_sort_is_refused(self):
        from unicode_fol_kit.fol.signature import Signature, FunctionDecl
        sig = Signature(functions={"f": FunctionDecl("f", 1, result_sort="Human")})
        with pytest.raises(ValueError, match="sorted function symbol"):
            FiniteDomainProblem((Atom("P", [Variable("x")]),), 2, signature=sig)

    def test_unsorted_function_declaration_is_unaffected(self):
        # arg_sorts=None, result_sort=None (the default) -- the ordinary
        # case, must not trip the refusal.
        from unicode_fol_kit.fol.signature import Signature, FunctionDecl
        sig = Signature(functions={"f": FunctionDecl("f", 1)})
        problem = FiniteDomainProblem((Atom("P", [Variable("x")]),), 2, signature=sig)
        assert problem.signature is sig

    def test_lower_msfol_never_produces_a_sorted_function_declaration(self):
        """The many-sorted front door this file otherwise tests
        (``lower_msfol``) relativises ``SortedQuantifier``/``SortedConstant``
        AWAY before ``Signature.from_formulas`` ever runs — so even a
        genuinely many-sorted sentence mentioning a plain (unsorted)
        ``Function`` reaches ``ClingoBackend.decide``/``MinizincBackend.decide``
        with an ordinary, unsorted ``FunctionDecl``: this refusal is defense
        in depth for a hand-built ``FiniteDomainProblem``, never triggered on
        the live many-sorted path either backend actually takes."""
        from unicode_fol_kit.fol.nodes import Function
        from unicode_fol_kit.fol.signature import Signature
        x = Variable("x")
        sentence = SortedQuantifier(
            "∀", x, "Human", Atom("=", [Function("f", [x]), x]))
        lowered = lower_msfol((sentence,))
        signature = Signature.from_formulas(lowered)
        assert signature.functions["f"].arg_sorts is None
        assert signature.functions["f"].result_sort is None
        # And building a real problem from this lowered+inferred signature
        # does not trip the sorted-function refusal.
        problem = FiniteDomainProblem(lowered, 2, signature=signature)
        assert problem.signature is signature
