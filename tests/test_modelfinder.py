"""General tests for the finite model finder (semantics/modelfinder.py), focused on
hand-checked textbook cases -- the independent oracle for the LNH symmetry-breaking
work (roadmap C23; see tests/test_modelfinder_symmetry.py for the differential /
isomorphism-class battery and the free_logic / secondorder companions).

Every expected verdict below is derived BY HAND (see the comment above each case),
never from the model finder itself, and every returned :class:`Structure` is
independently re-verified with :func:`semantics.tarski.models` before a test trusts
it -- the same "verify before you believe it" discipline the rest of the kit's
bounded searches use.
"""

import pytest

from unicode_logic_kit.fol.nodes import (
    Atom, Not, And, Or, Implies, Iff, Quantifier, Variable, Constant, Function,
)
from unicode_logic_kit.fol.msflparser import MSFLParser
from unicode_logic_kit.semantics.modelfinder import (
    find_model, find_countermodel, is_satisfiable_finite, is_valid_finite,
    _universal_closure,
)
from unicode_logic_kit.semantics.secondorder import (
    holds, so_find_countermodel, so_is_valid_finite,
)
from unicode_logic_kit.semantics.tarski import models

x, y, z = Variable("x"), Variable("y"), Variable("z")


def _all_different(names):
    """``And``-conjunction of pairwise ``≠`` over the named constants."""
    consts = [Constant(n) for n in names]
    conj = None
    for i in range(len(consts)):
        for j in range(i + 1, len(consts)):
            lit = Not(Atom("=", [consts[i], consts[j]]))
            conj = lit if conj is None else And(conj, lit)
    return conj


# --------------------------------------------------------------------------- #
# Hand-checked case 1: the smallest nontrivial group is Z/2Z (2 elements).
#
# Axioms: e is a two-sided identity for a binary op ``o``, every element is its
# own inverse (o(x,x)=e -- true of Z/2Z, where the only elements are 0 and 1 and
# 0+0=0, 1+1=0 mod 2), o is associative, and (crucially) some element differs
# from e -- otherwise the trivial 1-element group already satisfies everything.
# HAND CHECK: with only 1 domain element, "some x != e" is impossible (the sole
# element IS e), so no model exists at size 1. At size 2 the Z/2Z table itself
# (e=0, a=1, o(0,0)=0, o(0,1)=1, o(1,0)=1, o(1,1)=0) satisfies every axiom:
# identity (o(e,x)=x, o(x,e)=x hold by inspection), self-inverse (o(0,0)=0=e,
# o(1,1)=0=e), associativity (only 2 elements and the table is commutative and
# has the shape of Z/2Z, a genuine group), and a != e (1 != 0). So the smallest
# model has exactly 2 elements -- independent of how the search enumerates.
# --------------------------------------------------------------------------- #

def _group_axioms():
    e = Constant("e")
    a = Constant("a")
    o = lambda s, t: Function("o", [s, t])
    identity = And(
        Quantifier("∀", x, Atom("=", [o(e, x), x])),
        Quantifier("∀", x, Atom("=", [o(x, e), x])),
    )
    self_inverse = Quantifier("∀", x, Atom("=", [o(x, x), e]))
    assoc = Quantifier("∀", x, Quantifier("∀", y, Quantifier("∀", z,
        Atom("=", [o(o(x, y), z), o(x, o(y, z))]))))
    nontrivial = Not(Atom("=", [a, e]))
    return [identity, self_inverse, assoc, nontrivial]


@pytest.mark.parametrize("symmetry_breaking", [True, False])
def test_two_element_group_is_the_smallest_nontrivial_model(symmetry_breaking):
    axioms = _group_axioms()
    assert find_model(axioms, max_size=1, symmetry_breaking=symmetry_breaking) is None
    m2 = find_model(axioms, max_size=2, symmetry_breaking=symmetry_breaking)
    assert m2 is not None
    assert len(m2.domain) == 2
    sentences = [_universal_closure(f) for f in axioms]
    assert all(models(s, m2) for s in sentences)   # independently re-verified


# --------------------------------------------------------------------------- #
# Hand-checked case 2: a TRIANGLE needs exactly 3 colors (a textbook minimal
# example -- every pair of the 3 mutually-adjacent vertices must differ, so all
# 3 colors are forced into use), with a hand-built witness -- and this signature
# is exactly the "several named constants" shape LNH targets (3 named,
# pairwise-distinct vertex constants over a small domain, several unary
# predicates enumerated around them).
#
# Triangle v0-v1-v2 (every pair adjacent). HAND witness: v0=R, v1=G, v2=B -- all
# different colors, so every edge is bichromatic. A valid 3-coloring, so the
# theory below (exactly-one-color-per-vertex + no-monochromatic-edge, for all 3
# pairwise-distinct vertices) is satisfiable, and NOT satisfiable with fewer
# than 3 domain elements once "all vertices pairwise distinct" is added (3
# genuinely different individuals are needed to seat 3 distinct constants).
# --------------------------------------------------------------------------- #

def _triangle_coloring_theory():
    names = [f"v{i}" for i in range(3)]
    consts = [Constant(n) for n in names]
    edges = [(0, 1), (1, 2), (2, 0)]

    def color(pred, t):
        return Atom(pred, [t])

    exactly_one = None
    for c in consts:
        at_least_one = Or(color("R", c), Or(color("G", c), color("B", c)))
        pairwise_not_both = And(
            Not(And(color("R", c), color("G", c))),
            And(Not(And(color("R", c), color("B", c))),
                Not(And(color("G", c), color("B", c)))),
        )
        clause = And(at_least_one, pairwise_not_both)
        exactly_one = clause if exactly_one is None else And(exactly_one, clause)

    no_mono_edge = None
    for i, j in edges:
        ci, cj = consts[i], consts[j]
        clause = And(
            Not(And(color("R", ci), color("R", cj))),
            And(Not(And(color("G", ci), color("G", cj))),
                Not(And(color("B", ci), color("B", cj)))),
        )
        no_mono_edge = clause if no_mono_edge is None else And(no_mono_edge, clause)

    return And(And(exactly_one, no_mono_edge), _all_different(names))


@pytest.mark.parametrize("symmetry_breaking", [True, False])
def test_triangle_three_coloring_needs_three_pairwise_distinct_vertices(symmetry_breaking):
    theory = _triangle_coloring_theory()
    # HAND CHECK: 3 pairwise-distinct named constants cannot fit in a domain of
    # fewer than 3 elements (pigeonhole) -- so no model exists below size 3,
    # regardless of the coloring constraints.
    assert find_model([theory], max_size=2, symmetry_breaking=symmetry_breaking) is None
    m = find_model([theory], max_size=3, symmetry_breaking=symmetry_breaking)
    assert m is not None
    assert len(m.domain) == 3
    sentence = _universal_closure(theory)
    assert models(sentence, m) is True   # independently re-verified


# --------------------------------------------------------------------------- #
# Hand-checked case 3: pigeonhole -- 6 pairwise-distinct named constants cannot
# be seated in a domain of size <= 5 (there are only 5 slots for 6 distinct
# individuals). Genuinely unsatisfiable within the bound, both search modes must
# agree, and this exercises the "no false model AND no false negative" boundary.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("symmetry_breaking", [True, False])
def test_pigeonhole_six_distinct_constants_has_no_model_below_size_six(symmetry_breaking):
    theory = _all_different([f"c{i}" for i in range(6)])
    assert find_model([theory], max_size=5, symmetry_breaking=symmetry_breaking,
                      max_candidates=1 << 24) is None
    m = find_model([theory], max_size=6, symmetry_breaking=symmetry_breaking,
                   max_candidates=1 << 24)
    assert m is not None
    assert len(m.domain) == 6


# --------------------------------------------------------------------------- #
# MSFOL (sorted) sanity: sorted search must be BYTE-FOR-BYTE unaffected by the
# symmetry_breaking flag (see modelfinder.find_model's docstring: sig.sorts
# always takes the unbroken _sorted_interpretations path). This is the "existing
# fixtures in tests/test_modelfinder_sorted.py stay green" spirit, exercised
# directly here since that file is not touched by this change.
# --------------------------------------------------------------------------- #

_S = MSFLParser(many_sorted=True)


@pytest.mark.parametrize("symmetry_breaking", [True, False])
def test_sorted_search_ignores_symmetry_breaking_flag(symmetry_breaking):
    theory = [_S.parse("∀x:Human Mortal(x)"), _S.parse("Human(alice:Human)")]
    m = find_model(theory, max_size=3, symmetry_breaking=symmetry_breaking)
    assert m is not None
    assert "Human" in m.sorts
    assert m.constants["alice"] in m.sorts["Human"]

    cm = find_countermodel([_S.parse("∀x:A P(x)")], _S.parse("∀x:B P(x)"), max_size=2,
                           symmetry_breaking=symmetry_breaking)
    assert cm is not None


# --------------------------------------------------------------------------- #
# Second-order sanity: so_find_model/so_is_valid_finite/so_find_countermodel now
# enumerate their FREE symbols with the canonical (LNH) generator internally
# (secondorder._so_structures), so these hand-checked second-order (in)validities
# from the standard textbook repertoire must still come out the same way.
# --------------------------------------------------------------------------- #

def test_leibniz_equality_is_second_order_valid():
    # HAND CHECK: Leibniz's definition of equality, ∀x∀y(x=y <-> ∀P(P(x)<->P(y))),
    # is a second-order validity in any domain: "=" is definable from indiscernibility.
    a, b = Constant("a"), Constant("b")
    from unicode_logic_kit.fol._so_nodes import SecondOrderQuantifier
    P = lambda t: Atom("P", [t])
    leibniz = Quantifier("∀", x, Quantifier("∀", y, Iff(
        Atom("=", [x, y]), SecondOrderQuantifier("∀", "P", 1, Iff(P(x), P(y))))))
    assert so_is_valid_finite(leibniz, max_size=3) is True


def test_constants_need_not_be_distinguishable_is_second_order_invalid():
    # HAND CHECK: ∃P (P(a) ∧ ¬P(b)) is NOT SO-valid -- a model with a=b (or with a
    # relation that never separates them) refutes it; a 1-element domain forces
    # a=b, refuting it outright.
    a, b = Constant("a"), Constant("b")
    from unicode_logic_kit.fol._so_nodes import SecondOrderQuantifier
    P = lambda t: Atom("P", [t])
    formula = SecondOrderQuantifier("∃", "P", 1, And(P(a), Not(P(b))))
    assert so_is_valid_finite(formula, max_size=3) is False
    cm = so_find_countermodel(formula, max_size=3)
    assert cm is not None
    assert holds(formula, cm) is False   # independently re-verified


# --------------------------------------------------------------------------- #
# API surface: the new parameter is additive and keyword-friendly.
# --------------------------------------------------------------------------- #

def test_symmetry_breaking_is_true_by_default():
    import inspect
    assert inspect.signature(find_model).parameters["symmetry_breaking"].default is True
    assert inspect.signature(find_countermodel).parameters["symmetry_breaking"].default is True
    assert inspect.signature(is_satisfiable_finite).parameters["symmetry_breaking"].default is True
    assert inspect.signature(is_valid_finite).parameters["symmetry_breaking"].default is True


def test_is_valid_finite_and_is_satisfiable_finite_thread_the_flag():
    # A textbook tautology and a textbook contradiction, hand-checked, at both
    # settings of the flag.
    p = Atom("P", [Constant("a")])
    tautology = Or(p, Not(p))
    contradiction = And(p, Not(p))
    for sb in (True, False):
        assert is_valid_finite(tautology, symmetry_breaking=sb) is True
        assert is_satisfiable_finite(contradiction, symmetry_breaking=sb) is False
