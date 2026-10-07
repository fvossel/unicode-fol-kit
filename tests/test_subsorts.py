"""Cross-cutting differential tests for the subsort relation (roadmap C4).

A subsort edge ``S < T`` declared on a :class:`~unicode_logic_kit.fol.signature.Signature`
means the plain SUBSET reading: ``ext(S) ⊆ ext(T)``. Four independent routes are
GIVEN a ``Signature`` with subsorts and must honour that reading IDENTICALLY:

* :meth:`Signature.validate` (unit-tested per-route in ``tests/test_signature.py``;
  this file only re-derives the same example through the OTHER routes for the
  cross-check).
* :func:`unicode_logic_kit.fol.nodes.to_fol` plus
  :func:`~unicode_logic_kit.fol.nodes.subsort_axioms` as separate premises, decided
  by the existing, independent Z3 backend -- and the same through ``api.prove``.
* :func:`unicode_logic_kit.semantics.modelfinder.find_model` /
  :func:`~unicode_logic_kit.semantics.modelfinder.find_countermodel` (with
  ``subsorts=``), the kit's own from-scratch finite-structure search.
* :func:`unicode_logic_kit.fol.casl_import.parse_casl_spec` /
  :func:`~unicode_logic_kit.fol.casl_export.to_casl_spec` (the CASL round trip).

No snapshot tests: every expected verdict below (valid/invalid, sat/unsat) is
worked out BY HAND in each test's own comment from the textbook subset-semantics
reading, never captured from a run of the code under test.

A REAL, review-confirmed bug this file's differential methodology caught while
being written (see ``test_transitive_chain_through_an_unmentioned_intermediate_sort``
and :func:`unicode_logic_kit.semantics.modelfinder._subsort_closure`'s own
docstring): the finite model finder's signature scan only gives a sort its own
universe when that sort is actually USED by a sorted binder somewhere in the
theory, so a naive "check only DIRECT edges" filter silently missed the
transitive consequence of a chain ``A < B < C`` whenever the theory never
otherwise mentions the intermediate sort ``B`` — a real semantic disagreement
with the ``to_fol`` + Z3 route, caught here before it shipped. The fix computes
the full transitive closure inside the filter; this file pins the regression.

WHY THE AXIOMS ARE SEPARATE PREMISES: an earlier version of this item folded
the subsort axioms into ``to_fol(node, signature=sig)``'s own output. For a
VALIDITY check that is a trap -- ``api.prove(to_fol(f, signature=sig))`` then
has to prove ``∀x (S(x) → T(x)) ∧ f'``, and the axiom is not valid, so
``(∀x:Animal P(x)) → ∀y:Human P(y)`` came back REFUTED under ``Human < Animal``.
:func:`subsort_axioms` follows :func:`nonempty_sort_axioms`'s contract instead:
the caller adds them as extra, never-negated premises
(``test_api_prove_with_subsort_axioms_as_premises`` pins both the recipe and
its agreement with the model finder).
"""

import z3

from unicode_logic_kit import MSFLParser
from unicode_logic_kit.fol.nodes import (
    Atom, Constant, Not, to_fol, nonempty_sort_axioms, subsort_axioms,
)
from unicode_logic_kit.fol.signature import Signature
from unicode_logic_kit.fol.casl_export import to_casl_spec
from unicode_logic_kit.fol.casl_import import parse_casl_spec
from unicode_logic_kit.semantics.modelfinder import find_model, find_countermodel
from unicode_logic_kit.semantics.tarski import models

MSFOL = MSFLParser(many_sorted=True)


# =============================================================================
# Shared helpers
# =============================================================================

def _z3_valid(premises, conclusion, sig: Signature) -> bool:
    """``premises ⊨ conclusion`` valid, via ``to_fol`` + Z3, with the subsort
    axioms asserted as their own never-negated premises."""
    solver = z3.Solver()
    for axiom in subsort_axioms(sig):
        solver.add(axiom.to_z3())
    for p in premises:
        solver.add(to_fol(p).to_z3())
    solver.add(to_fol(Not(conclusion)).to_z3())
    return solver.check() == z3.unsat


def _z3_sat(formulas, sig: Signature, include_sort_facts: bool = True) -> bool:
    """``formulas`` jointly satisfiable, via ``to_fol`` + Z3, with the subsort
    axioms asserted alongside as extra conjuncts."""
    solver = z3.Solver()
    for axiom in subsort_axioms(sig):
        solver.add(axiom.to_z3())
    for f in formulas:
        solver.add(to_fol(f, include_sort_facts=include_sort_facts).to_z3())
    return solver.check() == z3.sat


def _assert_structure_honours_signature(structure, formulas, sig: Signature) -> None:
    """(test_oracle a/batch-note (1)) A structure :func:`find_model` returns
    must, RE-CHECKED independently:

    1. actually satisfy every formula, per :mod:`~unicode_logic_kit.semantics.tarski`'s
       OWN evaluator (:func:`models`) — a second pass over the same
       structure, not just trusting the search loop that built it;
    2. satisfy every declared subsort inclusion STRUCTURALLY — for every
       ``(child, parent)`` edge where BOTH sorts are present in the
       structure, ``set(structure.sorts[child]) <= set(structure.sorts[parent])``.
    """
    for f in formulas:
        assert models(f, structure), f"tarski re-check failed for {f.to_unicode_str()}"
    for child, parents in sig.subsorts.items():
        if child not in structure.sorts:
            continue
        child_universe = set(structure.sorts[child])
        for parent in parents:
            if parent not in structure.sorts:
                continue
            assert child_universe <= set(structure.sorts[parent]), (
                f"structure violates {child} < {parent}: "
                f"{structure.sorts[child]} not subset of {structure.sorts[parent]}"
            )


# =============================================================================
# The decisive example: validity depends on the edge
# =============================================================================

def test_valid_iff_human_subsort_of_animal():
    """(∀x:Animal P(x)) → ∀y:Human P(y) — HAND-DERIVED: valid iff Human <
    Animal.

    If Human ⊆ Animal: assume every Animal is P. Every Human is an Animal
    (subset), so every Human is P too — the implication holds in EVERY
    structure, i.e. it's valid.

    If Human and Animal are UNRELATED (no edge): a structure with Animal and
    Human DISJOINT, P true on Animal's one element and false on Human's one
    element, satisfies the antecedent (∀x:Animal P(x), vacuously scoped to
    Animal's element) but falsifies the consequent (∀y:Human P(y)) — a
    genuine countermodel, so NOT valid.

    Both independent routes (to_fol + Z3, and the finite model finder) must
    agree, in BOTH directions (with the edge, and without it).
    """
    premise = MSFOL.parse("∀x:Animal P(x)")
    conclusion = MSFOL.parse("∀y:Human P(y)")

    with_edge = Signature(sorts=frozenset({"Human", "Animal"}),
                          subsorts={"Human": frozenset({"Animal"})})
    assert _z3_valid([premise], conclusion, with_edge) is True
    cm = find_countermodel([premise], conclusion, max_size=4, subsorts=with_edge.subsorts)
    assert cm is None

    without_edge = Signature(sorts=frozenset({"Human", "Animal"}))
    assert _z3_valid([premise], conclusion, without_edge) is False
    cm2 = find_countermodel([premise], conclusion, max_size=4, subsorts=without_edge.subsorts)
    assert cm2 is not None
    _assert_structure_honours_signature(cm2, [premise, Not(conclusion)], without_edge)


# =============================================================================
# A two-level chain — transitivity from direct edges only
# =============================================================================

def test_transitive_chain_direct_edges_only():
    """A < B < C (only the two DIRECT edges declared, never A < C): HAND-
    DERIVED, 'some A is not any C' — ∃x:A ∀y:C (x ≠ y) — must be UNSAT/find
    no model, because A ⊆ B ⊆ C forces A ⊆ C transitively, even though that
    edge is never declared directly (to_fol emits only the two DIRECT
    implications; chaining them together entails the third)."""
    sig = Signature(sorts=frozenset({"A", "B", "C"}),
                    subsorts={"A": frozenset({"B"}), "B": frozenset({"C"})})
    bad = MSFOL.parse("∃x:A ∀y:C (x ≠ y)")

    assert _z3_sat([bad], sig) is False
    assert find_model([bad], max_size=4, subsorts=sig.subsorts) is None

    # Without the edges: A and C can be disjoint -- both routes must find a
    # witness (hand-derived: domain {0,1}, A={0}, C={1}).
    no_edges = Signature(sorts=frozenset({"A", "B", "C"}))
    assert _z3_sat([bad], no_edges) is True
    m = find_model([bad], max_size=4, subsorts=no_edges.subsorts)
    assert m is not None
    _assert_structure_honours_signature(m, [bad], no_edges)


def test_transitive_chain_through_an_unmentioned_intermediate_sort():
    """REGRESSION PIN (see the module docstring): the SAME chain as above,
    but confirmed to hold even though sort 'B' never gets its own universe
    in the searched Structure (it is declared in the Signature's subsorts
    but never used by any SortedQuantifier/SortedConstant/SortedCount/
    SortedCardinality in 'bad' itself) -- find_model must still refuse a
    model, proving the filter checks the TRANSITIVE closure, not merely
    edges whose both ends happen to be structurally present."""
    sig = Signature(sorts=frozenset({"A", "B", "C"}),
                    subsorts={"A": frozenset({"B"}), "B": frozenset({"C"})})
    bad = MSFOL.parse("∃x:A ∀y:C (x ≠ y)")
    m = find_model([bad], max_size=4, subsorts=sig.subsorts)
    assert m is None
    # If it HAD found one, 'B' would be absent from its own sorts dict --
    # confirming the theory genuinely never mentions B (the scenario this
    # regression is about), via a clean run WITHOUT the subsort filter.
    unfiltered = find_model([bad], max_size=4)
    assert unfiltered is not None
    assert "B" not in unfiltered.sorts


# =============================================================================
# A diamond hierarchy
# =============================================================================

def test_diamond_hierarchy():
    """A < B, A < C, B < D, C < D (A reaches D by two independent paths):
    HAND-DERIVED, 'some A is not any D' must be UNSAT/find no model, exactly
    like the linear chain -- either path alone already forces A ⊆ D."""
    sig = Signature(
        sorts=frozenset({"A", "B", "C", "D"}),
        subsorts={"A": frozenset({"B", "C"}), "B": frozenset({"D"}), "C": frozenset({"D"})},
    )
    bad = MSFOL.parse("∃x:A ∀y:D (x ≠ y)")
    assert _z3_sat([bad], sig) is False
    assert find_model([bad], max_size=4, subsorts=sig.subsorts) is None

    # Siblings B and C are NOT themselves related -- 'some B is not any C'
    # remains satisfiable (the diamond says nothing about B vs C directly).
    sibling_claim = MSFOL.parse("∃x:B ∀y:C (x ≠ y)")
    assert _z3_sat([sibling_claim], sig) is True
    m = find_model([sibling_claim], max_size=4, subsorts=sig.subsorts)
    assert m is not None
    _assert_structure_honours_signature(m, [sibling_claim], sig)


# =============================================================================
# A constant of a subsort
# =============================================================================

def test_constant_of_a_subsort_forces_membership_in_the_parent():
    """HAND-DERIVED: 'alice' declared/used as a Human-sorted constant, with
    Human < Animal declared -- Animal(alice) (the parent's guard predicate)
    must hold in EVERY model, i.e. 'Q(alice:Human) ∧ ¬Animal(alice)' is
    UNSAT. to_fol's own SortedConstant._relativize contributes the
    'Human(alice)' fact (via include_sort_facts=True); the subsort axiom
    ∀x(Human(x)→Animal(x)) then forces Animal(alice)."""
    sig = Signature(sorts=frozenset({"Human", "Animal"}),
                    subsorts={"Human": frozenset({"Animal"})})
    fact = MSFOL.parse("Q(alice:Human)")
    bad_negation = Not(Atom("Animal", [Constant("alice")]))
    assert _z3_sat([fact, bad_negation], sig) is False

    # Without the edge, 'alice' being Human says nothing about Animal --
    # SAT (hand-derived: alice simply isn't in Animal's universe).
    no_edge = Signature(sorts=frozenset({"Human", "Animal"}))
    assert _z3_sat([fact, bad_negation], no_edge) is True


# =============================================================================
# Equality across sorts
# =============================================================================

def test_equality_across_sorts_forces_a_witness():
    """HAND-DERIVED: ∀x:Human ∃y:Animal (x = y) -- valid iff Human < Animal
    (every Human element must equal SOME Animal element; with the edge, y=x
    always works since x is then itself in Animal's universe too; without
    it, Human and Animal can be disjoint, giving no such y)."""
    with_edge = Signature(sorts=frozenset({"Human", "Animal"}),
                          subsorts={"Human": frozenset({"Animal"})})
    claim = MSFOL.parse("∀x:Human ∃y:Animal (x = y)")
    assert _z3_valid([], claim, with_edge) is True
    assert find_countermodel([], claim, max_size=4, subsorts=with_edge.subsorts) is None

    without_edge = Signature(sorts=frozenset({"Human", "Animal"}))
    assert _z3_valid([], claim, without_edge) is False
    cm = find_countermodel([], claim, max_size=4, subsorts=without_edge.subsorts)
    assert cm is not None
    _assert_structure_honours_signature(cm, [Not(claim)], without_edge)


# =============================================================================
# Sort non-emptiness stays compatible with subsorting
# =============================================================================

def test_nonempty_sort_axioms_combine_with_subsorts_without_contradiction():
    """fol.nonempty_sort_axioms (added by the classical routes as separate
    premises) stays PER SORT; declaring every sort in a subsort hierarchy
    non-empty simultaneously is always consistent with the hierarchy itself
    (a non-empty subset of a non-empty superset's universe is not a
    contradiction -- trivially witnessed by Human = Animal = a single shared
    element). Both mentioned sorts get their own nonempty witness since both
    appear via SortedQuantifier in the same sentence."""
    sig = Signature(sorts=frozenset({"Human", "Animal"}),
                    subsorts={"Human": frozenset({"Animal"})})
    f = MSFOL.parse("(∀x:Human Mortal(x)) ∧ (∀y:Animal Mortal(y))")
    axioms = nonempty_sort_axioms(f)
    assert len(axioms) == 2   # one per distinct sort name: Human, Animal
    assert _z3_sat([f, *axioms], sig) is True


# =============================================================================
# symmetry_breaking True/False agree with subsorts (semantics.modelfinder)
# =============================================================================

def test_symmetry_breaking_flag_does_not_change_the_sorted_verdict():
    """MSFOL (sorted) search always uses the unbroken _sorted_interpretations
    regardless of symmetry_breaking (see modelfinder's own docstring) -- so
    with subsorts declared, both flag settings must agree, across every
    domain size 1..3, on both a VALID and an INVALID case."""
    sig = Signature(sorts=frozenset({"Human", "Animal"}),
                    subsorts={"Human": frozenset({"Animal"})})
    premise = MSFOL.parse("∀x:Animal P(x)")
    conclusion = MSFOL.parse("∀y:Human P(y)")   # valid, given the edge
    bad_claim = MSFOL.parse("∃x:Human ∀y:Animal (x ≠ y)")  # unsatisfiable, given the edge

    for size in (1, 2, 3):
        cm_true = find_countermodel([premise], conclusion, max_size=size,
                                    subsorts=sig.subsorts, symmetry_breaking=True)
        cm_false = find_countermodel([premise], conclusion, max_size=size,
                                     subsorts=sig.subsorts, symmetry_breaking=False)
        assert cm_true is None and cm_false is None, size

        m_true = find_model([bad_claim], max_size=size,
                            subsorts=sig.subsorts, symmetry_breaking=True)
        m_false = find_model([bad_claim], max_size=size,
                             subsorts=sig.subsorts, symmetry_breaking=False)
        assert m_true is None and m_false is None, size


def test_max_candidates_skip_never_reported_as_no_model_with_subsorts():
    """The 'skip this size, not searched' honesty contract (max_candidates)
    is untouched by the subsort filter -- it is a pure post-hoc filter over
    an UNCHANGED enumeration, so a caller passing subsorts alongside a tiny
    max_candidates still gets the SAME 'None means not found within the
    (size, budget) bounds, never a positive unsatisfiability claim' answer,
    and it must MATCH the unfiltered (no subsorts) run's skip behaviour
    exactly, size for size."""
    sig = Signature(sorts=frozenset({"Human", "Animal"}),
                    subsorts={"Human": frozenset({"Animal"})})
    claim = MSFOL.parse("∃x:Human ∀y:Animal (x ≠ y)")   # unsatisfiable, given the edge
    with_budget = find_model([claim], max_size=3, max_candidates=0, subsorts=sig.subsorts)
    without_subsorts_same_budget = find_model([claim], max_size=3, max_candidates=0)
    assert with_budget is None and without_subsorts_same_budget is None
    # A real (non-zero) budget still finds the genuine answer (None, since
    # the claim is unsatisfiable given the edge) -- the tiny-budget run
    # above was a vacuous 'everything skipped', not a meaningful decision.
    assert find_model([claim], max_size=3, subsorts=sig.subsorts) is None


# =============================================================================
# The full pipeline through CASL text
# =============================================================================

def test_casl_round_trip_signature_agrees_with_to_fol_and_modelfinder():
    """The Signature parsed BACK from CASL text (not the one used to BUILD
    the text) must independently agree with both decision routes -- closing
    the loop: hand-write CASL declaring 'sort Human < Animal', parse it,
    and confirm the SAME valid-iff-subsort example from the top of this
    file is decided identically through the round-tripped Signature."""
    text = (
        "spec Bio =\n"
        "  sorts Human, Animal\n"
        "  sort Human < Animal\n"
        "  preds P : Animal; Q : Human\n"
        "  . forall x : Animal . P(x)\n"
        "end"
    )
    spec = parse_casl_spec(text)
    sig = spec.signature
    assert sig.subsorts == {"Human": frozenset({"Animal"})}
    assert sig.is_subsort("Human", "Animal") is True

    premise = MSFOL.parse("∀x:Animal P(x)")
    conclusion = MSFOL.parse("∀y:Human P(y)")
    assert _z3_valid([premise], conclusion, sig) is True
    assert find_countermodel([premise], conclusion, max_size=4, subsorts=sig.subsorts) is None

    # And the round trip back out reproduces the same edge (already pinned
    # in detail by tests/test_casl_import.py; re-asserted here as the
    # closing link of THIS file's specific example).
    reexported = to_casl_spec(spec.axioms, spec_name="Bio", subsorts=sig.subsorts)
    assert "sort Human < Animal" in reexported
    assert parse_casl_spec(reexported).signature.subsorts == sig.subsorts


def test_validate_agrees_with_the_decision_routes_on_the_same_example():
    """Signature.validate's own verdict (clean vs. reporting a violation) on
    a term typed at the CHILD sort where the PARENT is declared matches
    what the decision routes above independently confirm is semantically
    sound -- P declared to expect 'Animal', called with a Human-sorted
    term, Human < Animal declared: validate() reports nothing, exactly
    because (per test_valid_iff_human_subsort_of_animal above) every model
    honouring the edge makes that substitution safe."""
    from unicode_logic_kit.fol.signature import PredicateDecl
    sig = Signature(predicates={"P": PredicateDecl("P", 1, ("Animal",))},
                    sorts=frozenset({"Human", "Animal"}),
                    subsorts={"Human": frozenset({"Animal"})})
    f = MSFOL.parse("∀x:Human P(x)")
    assert sig.validate(f) == []


# =============================================================================
# subsort_axioms as premises: the one-call validity route
# =============================================================================

def test_subsort_axioms_are_one_implication_per_direct_edge():
    sig = Signature(sorts=frozenset({"A", "B", "C"}),
                    subsorts={"A": frozenset({"B"}), "B": frozenset({"C"})})
    assert [a.to_unicode_str() for a in subsort_axioms(sig)] == [
        "∀x (A(x) → B(x))", "∀x (B(x) → C(x))"]
    assert subsort_axioms(Signature()) == ()


def test_api_prove_with_subsort_axioms_as_premises():
    """Each verdict worked out by hand from the subset reading, and each one
    must match the finite model finder given the same edges. The sorted goal
    goes to api.prove UNtranslated, so api.prove also adds its own sort
    non-emptiness premises, exactly as for any other sorted formula.

    - Human < Animal: every Animal is P, so every Human is P -- valid;
      without the edge Human and Animal are unrelated -- invalid.
    - A < B < C: C's property reaches A through the unmentioned B -- valid;
      the other direction does not hold -- invalid.
    - Human < Animal: some Human is P, so some Animal is P -- valid.
    - every Animal equals some Human fails once there are more Animals than
      Humans -- invalid; every Human equals some Animal (itself) -- valid.
    - with Human non-empty and inside Animal, a universal fact about Humans
      yields an Animal witness -- valid.
    """
    from unicode_logic_kit import api
    from unicode_logic_kit.semantics.modelfinder import is_valid_finite
    cases = [
        ("(∀x:Animal P(x)) → ∀y:Human P(y)", {"Human": {"Animal"}}, "proved"),
        ("(∀x:Animal P(x)) → ∀y:Human P(y)", {}, "refuted"),
        ("(∀x:C P(x)) → ∀y:A P(y)", {"A": {"B"}, "B": {"C"}}, "proved"),
        ("(∀x:A P(x)) → ∀y:C P(y)", {"A": {"B"}, "B": {"C"}}, "refuted"),
        ("(∃x:Human P(x)) → ∃y:Animal P(y)", {"Human": {"Animal"}}, "proved"),
        ("∀x:Animal ∃y:Human (x = y)", {"Human": {"Animal"}}, "refuted"),
        ("∀x:Human ∃y:Animal (x = y)", {"Human": {"Animal"}}, "proved"),
        ("(∀x:Human P(x)) → ∃y:Animal P(y)", {"Human": {"Animal"}}, "proved"),
    ]
    for text, edges, expected in cases:
        subsorts = {k: frozenset(v) for k, v in edges.items()}
        sig = Signature(sorts=frozenset(), subsorts=subsorts)
        goal = MSFOL.parse(text)
        assert api.prove(goal, list(subsort_axioms(sig))).status == expected, text
        assert is_valid_finite(goal, max_size=3, subsorts=subsorts) is (expected == "proved"), text
