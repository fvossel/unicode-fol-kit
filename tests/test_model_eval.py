"""Tests for unicode_fol_kit.semantics.model_eval — direct structural evaluation.

Every hand-derived test fixes a concrete :class:`FiniteStructure` and asserts
a truth value worked out by hand in the comment next to the assertion (never
copied from a program run). The one deliberate exception is
``TestDifferentialVsTarski``: a differential/property-based test is, by
construction, checked against an INDEPENDENT existing implementation
(:func:`unicode_fol_kit.semantics.tarski.satisfies`, a full-domain-iteration
evaluator with none of model_eval's indexing) rather than a per-case hand
derivation — that is the whole point of the technique, and it is what the
task asked for ("Differentialtest gegen den bestehenden Kit-Modelchecker").

Fixture: ``ETHANOL`` is the standard worked example — the smallest molecule
that still exercises unary atom types, per-atom property predicates, a
symmetric bond relation and nullary charge globals at once:

    D(M) = {c1, c2, o1}
    M(atom) = {c1, c2, o1}; M(c) = {c1, c2}; M(o) = {o1}
    M(charge0) = {c1, c2, o1}
    M(has3Hs) = {c1}; M(has2Hs) = {c2}; M(has1H) = {o1}
    M(singleBond) = M(bond) = {(c1,c2), (c2,c1), (c2,o1), (o1,c2)}
    NetChargePositive=False, NetChargeNeutral=True, NetChargeNegative=False

The predicate names used here follow the ChemLog TPTP convention instead
(``has_3_hs``/``has_2_hs``/``has_1_hs`` and ``bSINGLE`` rather than the
prose spellings ``has3Hs``/``has2Hs``/``has1H``/``singleBond`` above) — one
consistent scheme, chosen and stated explicitly rather than silently mixed;
see the CHEMLOG-SIGNATUR note for the two spellings this maps between, and
https://github.com/sfluegel05/chemlog-peptides for the vocabulary itself. A
kit-wide alias table between the two conventions is out of scope for this
module (it is a chemistry front-end concern, not a structural evaluator
concern).
"""

import random
import time

import pytest

from unicode_fol_kit.semantics.structures import FiniteStructure, graph_to_structure
from unicode_fol_kit.semantics import tarski
from unicode_fol_kit.semantics.model_eval import (
    BudgetExhausted, UninterpretedSymbol, UnsupportedNode,
    evaluate, evaluate_detailed,
)
from unicode_fol_kit.fol.nodes import (
    Variable, Constant, Number, Function,
    Atom, Not, And, Or, Xor, Implies, Iff, Quantifier, Count,
    Box, WeakConjunction,
)

X, Y, C, O = Variable("x"), Variable("y"), Variable("c"), Variable("o")


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

ETHANOL = graph_to_structure(
    nodes={
        "c1": ["atom", "c", "charge0", "has_3_hs"],
        "c2": ["atom", "c", "charge0", "has_2_hs"],
        "o1": ["atom", "o", "charge0", "has_1_hs"],
    },
    edges={
        "bSINGLE": [("c1", "c2"), ("c2", "c1"), ("c2", "o1"), ("o1", "c2")],
        "bond": [("c1", "c2"), ("c2", "c1"), ("c2", "o1"), ("o1", "c2")],
    },
    globals_={
        "net_charge_neutral": True,
        "NetChargePositive": False,
        "NetChargeNegative": False,
    },
)


def _one_carbon() -> FiniteStructure:
    """A one-individual structure: domain={a}, a is a carbon. Used for the
    all_different demo, where a singleton domain makes the semantic switch
    observable (two SEPARATE existentials can only ever be forced onto the
    same lone individual)."""
    return graph_to_structure(nodes={"a": ["c"]}, edges={})


# ---------------------------------------------------------------------------
# Connectives (Atom / Not / And / Or / Xor / Implies / Iff), on ETHANOL
# ---------------------------------------------------------------------------

class TestConnectives:
    def test_atom_true_and_false(self):
        # c(c1): c1 is in M(c) = {c1,c2} -> True. c(o1): o1 not in M(c) -> False.
        assert evaluate(Atom("c", [X]), ETHANOL, assignment={"x": "c1"}) is True
        assert evaluate(Atom("c", [X]), ETHANOL, assignment={"x": "o1"}) is False

    def test_nullary_atom(self):
        # net_charge_neutral is a declared 0-ary True fact; NetChargePositive False.
        assert evaluate(Atom("net_charge_neutral", []), ETHANOL) is True
        assert evaluate(Atom("NetChargePositive", []), ETHANOL) is False

    def test_not(self):
        # ¬o(c1): o(c1) is False (c1 is a carbon, not the oxygen) -> ¬False = True.
        assert evaluate(Not(Atom("o", [X])), ETHANOL, assignment={"x": "c1"}) is True
        assert evaluate(Not(Atom("c", [X])), ETHANOL, assignment={"x": "c1"}) is False

    def test_and(self):
        # c(c1) ∧ has_3_hs(c1): both True (c1 is a carbon with 3 H's) -> True.
        f = And(Atom("c", [X]), Atom("has_3_hs", [X]))
        assert evaluate(f, ETHANOL, assignment={"x": "c1"}) is True
        # c(c2) ∧ has_3_hs(c2): c2 has 2 H's, not 3 -> False.
        assert evaluate(f, ETHANOL, assignment={"x": "c2"}) is False

    def test_or(self):
        # o(c2) ∨ has_2_hs(c2): o(c2) False, has_2_hs(c2) True -> True.
        f = Or(Atom("o", [X]), Atom("has_2_hs", [X]))
        assert evaluate(f, ETHANOL, assignment={"x": "c2"}) is True
        # o(c1) ∨ has_2_hs(c1): both False (c1 is a carbon with 3 H's) -> False.
        assert evaluate(f, ETHANOL, assignment={"x": "c1"}) is False

    def test_xor(self):
        # c(c1) ⊕ o(c1): exactly one True (c(c1)=True, o(c1)=False) -> True.
        f = Xor(Atom("c", [X]), Atom("o", [X]))
        assert evaluate(f, ETHANOL, assignment={"x": "c1"}) is True
        # c(c1) ⊕ atom(c1): both True -> False.
        assert evaluate(Xor(Atom("c", [X]), Atom("atom", [X])), ETHANOL,
                         assignment={"x": "c1"}) is False

    def test_implies(self):
        # o(c1) → c(c1): antecedent False -> vacuously True.
        assert evaluate(Implies(Atom("o", [X]), Atom("c", [X])), ETHANOL,
                         assignment={"x": "c1"}) is True
        # c(c1) → atom(c1): True → True -> True.
        assert evaluate(Implies(Atom("c", [X]), Atom("atom", [X])), ETHANOL,
                         assignment={"x": "c1"}) is True
        # atom(o1) → c(o1): True → False -> False.
        assert evaluate(Implies(Atom("atom", [X]), Atom("c", [X])), ETHANOL,
                         assignment={"x": "o1"}) is False

    def test_iff(self):
        # c(c1) ↔ atom(c1): True ↔ True -> True.
        assert evaluate(Iff(Atom("c", [X]), Atom("atom", [X])), ETHANOL,
                         assignment={"x": "c1"}) is True
        # c(o1) ↔ atom(o1): False ↔ True -> False.
        assert evaluate(Iff(Atom("c", [X]), Atom("atom", [X])), ETHANOL,
                         assignment={"x": "o1"}) is False

    def test_equality_and_disequality_are_term_identity(self):
        # x=y with x,y both bound to "c1": True. x≠y with the same binding: False.
        assert evaluate(Atom("=", [X, Y]), ETHANOL, assignment={"x": "c1", "y": "c1"}) is True
        assert evaluate(Atom("≠", [X, Y]), ETHANOL, assignment={"x": "c1", "y": "c1"}) is False
        assert evaluate(Atom("≠", [X, Y]), ETHANOL, assignment={"x": "c1", "y": "o1"}) is True

    def test_constant_term(self):
        # A structure constant "c2" naming c2; c(c2)=True via the constant, not assignment.
        s = FiniteStructure(
            domain=ETHANOL.domain, extensions=dict(ETHANOL.extensions),
            constants={"anchor": "c2"},
        )
        assert evaluate(Atom("c", [Constant("anchor")]), s) is True
        assert evaluate(Atom("o", [Constant("anchor")]), s) is False


# ---------------------------------------------------------------------------
# Quantifiers — including the "no ∀ detour" / short-circuit design claims
# ---------------------------------------------------------------------------

class TestQuantifiers:
    def test_exists_true_and_false(self):
        # ∃x (o(x) ∧ bSINGLE(c2,x)): o1 is bonded to c2 by a single bond -> True.
        f = Quantifier("exists", X, And(Atom("o", [X]), Atom("bSINGLE", [C, X])))
        assert evaluate(f, ETHANOL, assignment={"c": "c2"}) is True
        # ∃x (o(x) ∧ bSINGLE(c1,x)): c1's only bond is to c2, not to any oxygen -> False.
        assert evaluate(f, ETHANOL, assignment={"c": "c1"}) is False

    def test_forall(self):
        # ∀x (atom(x) → (c(x) ∨ o(x))): every atom in the molecule is a C or an O -> True.
        f = Quantifier("forall", X, Implies(Atom("atom", [X]), Or(Atom("c", [X]), Atom("o", [X]))))
        assert evaluate(f, ETHANOL) is True
        # ∀x (atom(x) → c(x)): false of o1 -> False.
        assert evaluate(Quantifier("forall", X, Implies(Atom("atom", [X]), Atom("c", [X]))),
                         ETHANOL) is False

    def test_nested_exists_chain(self):
        # ∃x∃y (c(x) ∧ o(y) ∧ bSINGLE(x,y)): c2 is single-bonded to o1 -> True.
        f = Quantifier("exists", X, Quantifier("exists", Y,
            And(And(Atom("c", [X]), Atom("o", [Y])), Atom("bSINGLE", [X, Y]))))
        assert evaluate(f, ETHANOL) is True

    def test_negated_exists_is_correct_and_short_circuits_without_forall(self):
        # ¬∃x (o(x) ∧ bSINGLE(c,x)) evaluated directly must (a) give the right
        # answer and (b) NOT visit anywhere near the whole domain — proving it
        # is NOT rewritten to ∀x (¬o(x) ∨ ¬bSINGLE(c,x)) and scanned. Structure:
        # 200 unrelated "filler" atoms plus the real c1/o1 pair bonded together.
        # Candidate generation narrows x to individuals_with("o") = {"o1"}
        # ALONE, so evaluation needs only a handful of steps regardless of how
        # many fillers exist — a genuine ∀-over-everything approach would need
        # on the order of 200+ steps here.
        nodes = {f"filler{i}": ["atom"] for i in range(200)}
        nodes.update({"c1": ["atom", "c"], "o1": ["atom", "o"]})
        s = graph_to_structure(nodes=nodes, edges={"bSINGLE": [("c1", "o1"), ("o1", "c1")]})
        f = Not(Quantifier("exists", X, And(Atom("o", [X]), Atom("bSINGLE", [C, X]))))

        # correctness: a witness (o1) exists, so the negation is False.
        result = evaluate_detailed(f, s, assignment={"c": "c1"})
        assert result.holds is False
        # short-circuit proof: nowhere near the 200 fillers were touched.
        assert result.steps < 20

        # sanity: bonding c1 to only a filler (no oxygen at all) makes it True.
        s_no_o = graph_to_structure(
            nodes={f"filler{i}": ["atom"] for i in range(5)}, edges={})
        f_no_witness = Not(Quantifier("exists", X, Atom("atom", [X])))
        # (trivial witness case retained for contrast — every filler is an atom)
        assert evaluate(f_no_witness, s_no_o) is False

    def test_or_short_circuits_the_untaken_branch(self):
        # p(a) ∨ ∀x p(x), with p(a) already True: Or must short-circuit and
        # never touch the expensive ∀ over 1000 individuals only 1 of which
        # satisfies p. Proven the same way: step count stays tiny.
        nodes = {f"filler{i}": ["atom"] for i in range(1000)}
        nodes["a"] = ["atom", "p"]
        s = graph_to_structure(nodes=nodes, edges={})
        f = Or(Atom("p", [Variable("a")]),
               Quantifier("forall", X, Atom("p", [X])))
        result = evaluate_detailed(f, s, assignment={"a": "a"})
        assert result.holds is True
        assert result.steps < 20  # a full ∀ scan alone would need >= 1000 steps


# ---------------------------------------------------------------------------
# Count — native evaluation, including boundary cases
# ---------------------------------------------------------------------------

class TestCount:
    # ETHANOL has exactly 2 carbons (c1, c2) and 1 oxygen (o1).

    def test_ge(self):
        assert evaluate(Count("ge", Number(2), X, Atom("c", [X])), ETHANOL) is True
        assert evaluate(Count("ge", Number(3), X, Atom("c", [X])), ETHANOL) is False

    def test_le(self):
        assert evaluate(Count("le", Number(2), X, Atom("c", [X])), ETHANOL) is True
        assert evaluate(Count("le", Number(1), X, Atom("c", [X])), ETHANOL) is False

    def test_eq(self):
        assert evaluate(Count("eq", Number(2), X, Atom("c", [X])), ETHANOL) is True
        assert evaluate(Count("eq", Number(1), X, Atom("c", [X])), ETHANOL) is False

    def test_n_zero(self):
        # ∃≥0: vacuously True regardless of the predicate (standard Count semantics).
        assert evaluate(Count("ge", Number(0), X, Atom("c", [X])), ETHANOL) is True
        # ∃≤0 x c(x): False, since 2 carbons exist (need exactly none).
        assert evaluate(Count("le", Number(0), X, Atom("c", [X])), ETHANOL) is False
        # ∃=0 x c(x): False, same reason.
        assert evaluate(Count("eq", Number(0), X, Atom("c", [X])), ETHANOL) is False

    def test_n_larger_than_domain(self):
        # ∃≥5 x c(x): only 2 carbons exist in a 3-individual domain -> False.
        assert evaluate(Count("ge", Number(5), X, Atom("c", [X])), ETHANOL) is False
        # ∃≤5 x c(x): trivially True, at most 3 individuals total exist anyway.
        assert evaluate(Count("le", Number(5), X, Atom("c", [X])), ETHANOL) is True

    def test_count_short_circuits_on_ge(self):
        # 100 carbons, ∃≥3 x c(x): must stop scanning after the 3rd hit, not
        # examine all 100 — proven by a tight step budget succeeding.
        s = graph_to_structure(nodes={f"c{i}": ["c"] for i in range(100)}, edges={})
        f = Count("ge", Number(3), X, Atom("c", [X]))
        result = evaluate_detailed(f, s, budget=30)
        assert result.exhausted is False
        assert result.holds is True
        assert result.steps < 30


# ---------------------------------------------------------------------------
# all_different — the ChemLog convention, a semantics switch
# ---------------------------------------------------------------------------

class TestAllDifferent:
    def test_singleton_domain_forces_the_distinction(self):
        # ∃x∃y (c(x) ∧ c(y)) on a ONE-carbon domain {a}:
        #  - all_different=False (plain FOL): x=y=a is a legal witness -> True.
        #  - all_different=True (ChemLog convention): x and y must be DIFFERENT
        #    individuals, but only one exists -> no valid witness -> False.
        s = _one_carbon()
        f = Quantifier("exists", X, Quantifier("exists", Y,
            And(Atom("c", [X]), Atom("c", [Y]))))
        assert evaluate(f, s, all_different=False) is True
        assert evaluate(f, s, all_different=True) is False

    def test_two_carbons_all_different_succeeds(self):
        # With two DISTINCT carbons available, all_different=True can still
        # find a witness (x=c1, y=c2 or vice versa).
        f = Quantifier("exists", X, Quantifier("exists", Y,
            And(Atom("c", [X]), Atom("c", [Y]))))
        assert evaluate(f, ETHANOL, all_different=True) is True

    def test_all_different_does_not_reach_into_forall_or_count(self):
        # ∀ is untouched: ∀x c(x) is False either way on ETHANOL (o1 isn't a
        # carbon) regardless of all_different. Count's own witnesses are
        # already pairwise-distinct by definition, also regardless of the flag.
        forall_f = Quantifier("forall", X, Atom("c", [X]))
        assert evaluate(forall_f, ETHANOL, all_different=False) is False
        assert evaluate(forall_f, ETHANOL, all_different=True) is False
        count_f = Count("eq", Number(2), X, Atom("c", [X]))
        assert evaluate(count_f, ETHANOL, all_different=False) is True
        assert evaluate(count_f, ETHANOL, all_different=True) is True

    # -- regression: reused variable NAME across a peeled ∃-chain -----------
    #
    # _peel_exists_chain collects the bound-variable NAME at every layer of
    # an adjacent ∃∃∃… run into a (possibly-repeating) list, e.g. peeling
    # `∃x∃x∃x φ` gives names=['x','x','x']. _search_exists/_search_exists_
    # witness used to strip a just-picked variable out of `remaining` with
    # `[n for n in remaining if n != name]` — VALUE-based removal, which
    # deletes EVERY 'x' at once instead of the one just bound. That
    # collapsed an N-layer chain of same-named ∃ into effectively ONE ∃
    # after the very first pick (`remaining` went straight from ['x','x','x']
    # to [] instead of ['x','x']), so `all_different=True` ended up requiring
    # only 1 witness where the docstring promises N pairwise-distinct ones.
    # Fixed by removing exactly one (positional/first) occurrence instead
    # (`rest = list(remaining); rest.remove(name)`).

    def test_reused_name_exists_chain_requires_n_distinct_witnesses(self):
        # ∃x∃x∃x c(x) -- a 3-deep chain reusing the name "x" at every layer
        # (peels to names=['x','x','x'], matrix=c(x)). Hand-derivation for
        # all_different=True against a domain with exactly 2 carbons:
        #   layer 1 binds x to a candidate from {c1,c2}          (2 options)
        #   layer 2 must bind a DIFFERENT candidate from {c1,c2} (1 option left)
        #   layer 3 must bind a THIRD, still-different candidate -- but only
        #     2 carbons exist in total, so the candidate set is EMPTY here,
        #     and every branch of the search dead-ends.
        # -> holds must be False (3 pairwise-distinct witnesses demanded, only
        # 2 individuals available). Before the fix, the buggy value-based
        # `rest = [n for n in remaining if n != name]` wiped all three 'x'
        # entries after the FIRST pick, so `_search_exists` treated this as a
        # single ∃x and returned True as soon as layer 1's first candidate
        # (c1, itself a carbon) was tried -- silently requiring only 1
        # witness instead of 3.
        two_carbons = graph_to_structure(nodes={"c1": ["c"], "c2": ["c"]}, edges={})
        chain3 = Quantifier("exists", X, Quantifier("exists", X,
            Quantifier("exists", X, Atom("c", [X]))))
        assert evaluate(chain3, two_carbons, all_different=True) is False

        # With a THIRD carbon added, 3 pairwise-distinct witnesses (c1,c2,c3)
        # do exist -> holds is True, and (hand-traced through
        # _pick_most_constrained's deterministic domain-order candidate
        # selection and _search_exists_witness's binding merge -- see the
        # module docstring, later layers overwrite earlier ones under a
        # reused name since the FINAL value of "x" is what the matrix sees)
        # the witness collapses to the INNERMOST (3rd-layer) binding, "c3".
        three_carbons = graph_to_structure(
            nodes={"c1": ["c"], "c2": ["c"], "c3": ["c"]}, edges={})
        result = evaluate_detailed(chain3, three_carbons, all_different=True)
        assert result.holds is True
        assert result.witness == {"x": "c3"}

    def test_reused_name_exists_chain_unaffected_when_all_different_is_false(self):
        # Under PLAIN FOL semantics (all_different=False, the default), a
        # reused-name chain ∃x∃x∃x c(x) is just ordinary quantifier
        # shadowing -- semantically identical to a single ∃x c(x) -- so even
        # a ONE-carbon domain (which the all_different=True case above
        # requires at least 3 individuals for) already satisfies it. This
        # pins that the fix (positional `rest` removal) did not change
        # anything about the all_different=False path, only the
        # all_different=True candidate-pruning path.
        one_carbon = _one_carbon()
        chain3 = Quantifier("exists", X, Quantifier("exists", X,
            Quantifier("exists", X, Atom("c", [X]))))
        assert evaluate(chain3, one_carbon, all_different=False) is True

    # -- documented scope boundary: SIBLING ∃, not ancestor/descendant ------
    #
    # bound_existentials is only ever EXTENDED inside _search_exists /
    # _search_exists_witness, and _eval threads it through every connective
    # UNCHANGED to both sub-calls (see the "And"/"Or"/etc. cases in _eval) --
    # it is never updated in the caller after a nested call returns. So two
    # ∃ in an ANCESTOR/DESCENDANT relationship (one's matrix syntactically
    # contains the other, however deep) correctly exclude each other's
    # witnesses, but two SIBLING ∃ -- e.g. joined directly by ∧, where
    # neither is nested inside the other's matrix -- do NOT: the left ∃'s
    # search runs to completion (and is discarded) before the right ∃'s
    # search even starts, each starting from the SAME bound_existentials the
    # And received on entry. This is a deliberate scope reading of "every
    # individual bound to an ACTIVE ∃" (module docstring), not an omission
    # to fix here -- pinned explicitly so a future change cannot silently
    # narrow or widen it without this test noticing.

    def test_all_different_does_not_reach_across_sibling_exists(self):
        # (∃x c(x)) ∧ (∃y c(y)) -- x and y are SIBLING existentials (joined
        # by a top-level And), not one nested inside the other's matrix.
        # Contrast with test_singleton_domain_forces_the_distinction's
        # ∃x∃y (c(x) ∧ c(y)) (a genuinely NESTED chain), which correctly
        # returns False on this same one-carbon domain. Here, on a domain
        # with only ONE carbon "a", each ∃ independently finds x=a / y=a --
        # all_different=True does NOT force x != y across the sibling
        # boundary, so the conjunction still holds True even though both
        # variables denote the very same individual.
        s = _one_carbon()
        sibling_f = And(Quantifier("exists", X, Atom("c", [X])),
                         Quantifier("exists", Y, Atom("c", [Y])))
        assert evaluate(sibling_f, s, all_different=True) is True

        # The nested form on the identical structure DOES catch it (already
        # covered by test_singleton_domain_forces_the_distinction; repeated
        # here for a direct side-by-side contrast in one place).
        nested_f = Quantifier("exists", X, Quantifier("exists", Y,
            And(Atom("c", [X]), Atom("c", [Y]))))
        assert evaluate(nested_f, s, all_different=True) is False


# ---------------------------------------------------------------------------
# Errors: uninterpreted symbols, unsupported nodes, free variables, Function terms
# ---------------------------------------------------------------------------

class TestErrors:
    def test_uninterpreted_predicate(self):
        with pytest.raises(UninterpretedSymbol) as exc_info:
            evaluate(Atom("halogen", [X]), ETHANOL, assignment={"x": "c1"})
        assert exc_info.value.symbol == "halogen"
        assert exc_info.value.arity == 1

    def test_uninterpreted_constant(self):
        with pytest.raises(UninterpretedSymbol):
            evaluate(Atom("c", [Constant("nope")]), ETHANOL)

    def test_uninterpreted_binary_predicate_in_candidate_generation(self):
        # The uninterpreted symbol must surface even when it is only found
        # while HARVESTING candidates for a quantified variable (not just
        # during the final atom check).
        f = Quantifier("exists", X, And(Atom("o", [X]), Atom("bDOUBLE", [C, X])))
        with pytest.raises(UninterpretedSymbol):
            evaluate(f, ETHANOL, assignment={"c": "c1"})

    def test_modal_operator_is_refused(self):
        with pytest.raises(UnsupportedNode):
            evaluate(Box(Atom("p", [])), ETHANOL)

    def test_fuzzy_operator_is_refused(self):
        with pytest.raises(UnsupportedNode):
            evaluate(WeakConjunction(Atom("c", [X]), Atom("c", [X])), ETHANOL,
                     assignment={"x": "c1"})

    def test_function_term_is_refused(self):
        with pytest.raises(UnsupportedNode):
            evaluate(Atom("c", [Function("f", [Constant("c1")])]), ETHANOL)

    def test_free_variable_raises(self):
        with pytest.raises(ValueError):
            evaluate(Atom("c", [Y]), ETHANOL, assignment={"x": "c1"})  # y is unbound


# ---------------------------------------------------------------------------
# Budget: the honest three-valued contract
# ---------------------------------------------------------------------------

class TestBudget:
    def test_evaluate_detailed_exhaustion_is_unknown_not_false(self):
        # A ∀ over the whole 3-individual ETHANOL domain needs several steps
        # per individual; budget=1 cannot possibly finish it.
        f = Quantifier("forall", X, Atom("c", [X]))
        result = evaluate_detailed(f, ETHANOL, budget=1)
        assert result.exhausted is True
        assert result.holds is None
        assert result.witness is None
        assert result.failing_conjunct is None

    def test_evaluate_raises_budget_exhausted(self):
        f = Quantifier("forall", X, Atom("c", [X]))
        with pytest.raises(BudgetExhausted) as exc_info:
            evaluate(f, ETHANOL, budget=1)
        assert exc_info.value.steps >= 1

    def test_exact_boundary_and_graceful_explanation_degradation(self):
        # ∃x (o(x) ∧ bSINGLE(c2,x)) on ETHANOL: hand-traced step counts (see
        # the manual trace this test pins) are: the core answer is decided at
        # step 6 (budget=5 exhausts, budget=6 does not); the FULL witness
        # trace additionally needs steps up to 15.
        f = Quantifier("exists", X, And(Atom("o", [X]), Atom("bSINGLE", [C, X])))
        too_tight = evaluate_detailed(f, ETHANOL, assignment={"c": "c2"}, budget=5)
        assert too_tight.exhausted is True
        assert too_tight.holds is None

        core_only = evaluate_detailed(f, ETHANOL, assignment={"c": "c2"}, budget=6)
        assert core_only.exhausted is False           # the core answer WAS decided
        assert core_only.holds is True
        assert core_only.witness is None               # but too tight for the explanation

        ample = evaluate_detailed(f, ETHANOL, assignment={"c": "c2"}, budget=100)
        assert ample.exhausted is False
        assert ample.holds is True
        assert ample.witness == {"x": "o1"}             # explanation fits comfortably now

    def test_no_budget_means_unbounded(self):
        f = Quantifier("forall", X, Or(Atom("c", [X]), Atom("o", [X])))
        result = evaluate_detailed(f, ETHANOL, budget=None)
        assert result.exhausted is False
        assert result.holds is True


# ---------------------------------------------------------------------------
# Explanations: witness / failing_conjunct
# ---------------------------------------------------------------------------

class TestExplanations:
    def test_witness_for_exists(self):
        # ∃x (o(x) ∧ bSINGLE(c2,x)): the only witness in ETHANOL is o1.
        f = Quantifier("exists", X, And(Atom("o", [X]), Atom("bSINGLE", [C, X])))
        result = evaluate_detailed(f, ETHANOL, assignment={"c": "c2"})
        assert result.holds is True
        assert result.witness == {"x": "o1"}

    def test_witness_merges_across_and(self):
        # (∃x c(x)) ∧ (∃y o(y)): both conjuncts contribute their own binding;
        # the merged witness names both x and y.
        f = And(Quantifier("exists", X, Atom("c", [X])),
                Quantifier("exists", Y, Atom("o", [Y])))
        result = evaluate_detailed(f, ETHANOL)
        assert result.holds is True
        assert result.witness == {"x": "c1", "y": "o1"}  # c1/o1: first domain-order hits

    def test_failing_conjunct_drills_into_and_chain(self):
        # atom(c1) ∧ (o(c1) ∧ has_3_hs(c1)): atom(c1)=True, o(c1)=False,
        # has_3_hs(c1)=True (never reached) -> the false conjunct is o(c1) itself.
        culprit = Atom("o", [X])
        f = And(Atom("atom", [X]), And(culprit, Atom("has_3_hs", [X])))
        result = evaluate_detailed(f, ETHANOL, assignment={"x": "c1"})
        assert result.holds is False
        assert result.failing_conjunct == culprit

    def test_failing_conjunct_stops_at_non_and_node(self):
        # A false top-level Or is reported as itself, not decomposed.
        f = Or(Atom("o", [X]), Atom("has_1_hs", [X]))  # both False for c1
        result = evaluate_detailed(f, ETHANOL, assignment={"x": "c1"})
        assert result.holds is False
        assert result.failing_conjunct == f


# ---------------------------------------------------------------------------
# Differential test vs. the kit's existing (independent) Tarski evaluator
# ---------------------------------------------------------------------------

_UNARY = ("p", "q")
_BINARY = ("r",)


def _to_tarski_structure(fs: FiniteStructure) -> tarski.Structure:
    """Adapt a (stored-extension-only) FiniteStructure into a tarski.Structure
    with the SAME domain and predicate extensions, for cross-checking. No new
    evaluation logic here — just a data adapter between two existing,
    independently implemented structure representations."""
    predicates = {key: set(rows) for key, rows in fs.extensions.items()}
    return tarski.Structure(domain=fs.domain, constants=dict(fs.constants),
                             predicates=predicates)


def _random_structure(rng: random.Random, domain) -> FiniteStructure:
    ext = {}
    for u in _UNARY:
        ext[(u, 1)] = {(d,) for d in domain if rng.random() < 0.5}
    for b in _BINARY:
        ext[(b, 2)] = {(a, c) for a in domain for c in domain if rng.random() < 0.3}
    return FiniteStructure(domain=domain, extensions=ext)


def _random_formula(rng: random.Random, bound_vars, depth, fresh_counter):
    """A random closed formula over _UNARY/_BINARY predicates and the
    connectives/quantifiers/Count this module supports. ``fresh_counter`` is
    a 1-element list used as a mutable int to keep bound-variable names
    globally unique (avoids incidental shadowing, which both evaluators
    handle correctly but which would complicate reasoning about the test)."""
    if bound_vars and (depth <= 0 or rng.random() < 0.35):
        if rng.random() < 0.6:
            return Atom(rng.choice(_UNARY), [Variable(rng.choice(bound_vars))])
        v1, v2 = rng.choice(bound_vars), rng.choice(bound_vars)
        return Atom(rng.choice(_BINARY), [Variable(v1), Variable(v2)])

    kinds = (["forall", "exists", "count"] if not bound_vars else
             ["not", "and", "or", "implies", "iff", "xor", "forall", "exists", "count"])
    kind = rng.choice(kinds)
    if kind == "not":
        return Not(_random_formula(rng, bound_vars, depth - 1, fresh_counter))
    if kind in ("and", "or", "implies", "iff", "xor"):
        left = _random_formula(rng, bound_vars, depth - 1, fresh_counter)
        right = _random_formula(rng, bound_vars, depth - 1, fresh_counter)
        return {"and": And, "or": Or, "implies": Implies,
                "iff": Iff, "xor": Xor}[kind](left, right)

    fresh_counter[0] += 1
    fresh = f"v{fresh_counter[0]}"
    body = _random_formula(rng, bound_vars + [fresh], depth - 1, fresh_counter)
    if kind == "count":
        n = rng.randint(0, 3)
        op = rng.choice(["ge", "le", "eq"])
        return Count(op, Number(n), Variable(fresh), body)
    return Quantifier("forall" if kind == "forall" else "exists", Variable(fresh), body)


class TestDifferentialVsTarski:
    def test_random_small_structures_agree_with_tarski(self):
        # Fixed seed: deterministic, non-flaky. 25 random (structure, closed
        # formula) pairs over a 4-individual domain, each checked against
        # tarski.satisfies — an independent, full-domain-iteration evaluator
        # this module does not share any evaluation code with.
        rng = random.Random(20260813)
        domain = ("a", "b", "c", "d")
        fresh_counter = [0]
        for i in range(25):
            fs = _random_structure(rng, domain)
            formula = _random_formula(rng, [], 4, fresh_counter)
            expected = tarski.satisfies(formula, _to_tarski_structure(fs), {})
            actual = evaluate(formula, fs)
            assert actual == expected, (
                f"case {i}: model_eval={actual} tarski={expected} "
                f"formula={formula.to_unicode_str()!r}"
            )


# ---------------------------------------------------------------------------
# Performance: the hasAtLeast40Carbons claim
# ---------------------------------------------------------------------------

class TestPerformance:
    def test_count_ge_40_of_50_carbons_is_fast(self):
        # The motivating case: "at least 40 carbons" against a molecule
        # with ~50 carbons (plus a few non-carbon atoms, so the candidate-
        # narrowing actually has to do something). As a native Count>=40,
        # this should take milliseconds, not the exponential-ish blowup the
        # 40-nested-∃-with-780-pairwise-≠ encoding produces.
        nodes = {f"c{i}": ["c"] for i in range(50)}
        nodes.update({f"o{i}": ["o"] for i in range(5)})
        s = graph_to_structure(nodes=nodes, edges={})
        f = Count("ge", Number(40), Variable("x"), Atom("c", [Variable("x")]))

        start = time.perf_counter()
        result = evaluate(f, s)
        elapsed = time.perf_counter() - start

        assert result is True  # 50 >= 40, by construction
        assert elapsed < 0.5   # generously pinned per the task's own example bound

    def test_count_vs_expanded_nested_exists_ratio(self):
        # Same shape as above but scaled down (n=6 distinct witnesses needed,
        # out of 8 candidates) so the SLOW baseline still finishes quickly in
        # a test suite: the naive nested-∃-with-pairwise-≠ encoding (obtained
        # by calling Count._expand(), the same lowering to_z3/to_prover9/
        # to_tptp already use) gets NONE of the native Count short-circuit,
        # since ≠ atoms carry no membership information for candidate
        # generation (see the module docstring's design decision #3) — so it
        # degrades to unindexed backtracking, which is measurably, and
        # generously-margined, slower. The ratio is pinned loosely (>=20x,
        # observed empirically around 5000x) to avoid CI-speed flakiness.
        s = graph_to_structure(nodes={f"c{i}": ["c"] for i in range(8)}, edges={})
        native = Count("ge", Number(6), Variable("x"), Atom("c", [Variable("x")]))
        expanded = native._expand()  # standard distinct-witnesses lowering

        t0 = time.perf_counter()
        native_result = evaluate(native, s)
        t1 = time.perf_counter()
        expanded_result = evaluate(expanded, s)
        t2 = time.perf_counter()

        native_time = t1 - t0
        expanded_time = t2 - t1

        assert native_result is True    # 8 carbons >= 6, by construction
        assert expanded_result is True  # logically equivalent formula
        assert native_time < 0.05                       # generous absolute bound
        assert expanded_time > native_time * 20          # generous relative bound
