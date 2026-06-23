"""Tests for Robinson first-order unification (unicode_fol_kit.fol.unification)."""

from unicode_fol_kit.fol.nodes import Variable, Constant, Number, Function, Atom
from unicode_fol_kit.fol.unification import unify, apply_subst


def test_unify_function_two_vars():
    """unify(f(x,a), f(b,y)) -> {x: b, y: a}; substitution equalises both sides."""
    t1 = Function("f", [Variable("x"), Constant("a")])
    t2 = Function("f", [Constant("b"), Variable("y")])

    subst = unify(t1, t2)

    assert subst is not None
    assert subst == {"x": Constant("b"), "y": Constant("a")}
    # Applying the MGU makes the two terms structurally equal.
    assert apply_subst(t1, subst) == apply_subst(t2, subst)
    assert apply_subst(t1, subst) == Function("f", [Constant("b"), Constant("a")])


def test_occurs_check_fails():
    """unify(x, f(x)) -> None by the occurs-check (would build an infinite term)."""
    assert unify(Variable("x"), Function("f", [Variable("x")])) is None
    # Symmetric direction also fails.
    assert unify(Function("f", [Variable("x")]), Variable("x")) is None


def test_distinct_constants_fail():
    """unify(a, b) for distinct constants -> None."""
    assert unify(Constant("a"), Constant("b")) is None


def test_same_constant_succeeds():
    """unify(a, a) -> {} (already equal, empty MGU)."""
    assert unify(Constant("a"), Constant("a")) == {}


def test_var_with_itself_is_identity():
    """unify(x, x) -> {} (identity / empty substitution)."""
    assert unify(Variable("x"), Variable("x")) == {}


def test_var_binds_to_term():
    """unify(x, f(a)) binds x to f(a)."""
    term = Function("f", [Constant("a")])
    subst = unify(Variable("x"), term)
    assert subst == {"x": term}
    assert apply_subst(Variable("x"), subst) == term


def test_numbers():
    """Numbers unify iff equal; a variable binds to a number."""
    assert unify(Number(3), Number(3)) == {}
    assert unify(Number(3), Number(4)) is None
    assert unify(Variable("x"), Number(7)) == {"x": Number(7)}


def test_atoms_unify():
    """P(x, a) and P(b, y) unify to {x: b, y: a}; applying it equalises them."""
    a1 = Atom("P", [Variable("x"), Constant("a")])
    a2 = Atom("P", [Constant("b"), Variable("y")])

    subst = unify(a1, a2)

    assert subst == {"x": Constant("b"), "y": Constant("a")}
    assert apply_subst(a1, subst) == apply_subst(a2, subst)


def test_atoms_different_predicate_fail():
    """P(x) vs Q(x) -> None (different predicate)."""
    assert unify(Atom("P", [Variable("x")]), Atom("Q", [Variable("x")])) is None


def test_atoms_different_arity_fail():
    """P(x) vs P(x, y) -> None (different arity)."""
    a1 = Atom("P", [Variable("x")])
    a2 = Atom("P", [Variable("x"), Variable("y")])
    assert unify(a1, a2) is None


def test_function_name_mismatch_fail():
    """f(x) vs g(x) -> None (different function symbol)."""
    assert unify(Function("f", [Variable("x")]), Function("g", [Variable("x")])) is None


def test_function_arity_mismatch_fail():
    """f(x) vs f(x, y) -> None (different arity)."""
    a1 = Function("f", [Variable("x")])
    a2 = Function("f", [Variable("x"), Variable("y")])
    assert unify(a1, a2) is None


def test_shared_variable_chains():
    """unify(f(x, x), f(a, y)) binds x to a then forces y to a too."""
    t1 = Function("f", [Variable("x"), Variable("x")])
    t2 = Function("f", [Constant("a"), Variable("y")])

    subst = unify(t1, t2)

    assert subst is not None
    # x ↦ a, and the second pair (x, y) then unifies a with y, so y ↦ a.
    assert apply_subst(Variable("x"), subst) == Constant("a")
    assert apply_subst(Variable("y"), subst) == Constant("a")
    assert apply_subst(t1, subst) == apply_subst(t2, subst)


def test_nested_occurs_check():
    """unify(x, g(f(x))) -> None: the variable occurs nested inside."""
    assert unify(Variable("x"), Function("g", [Function("f", [Variable("x")])])) is None


def test_var_to_var_then_constant():
    """unify(g(x, y), g(y, a)) propagates x = y = a through the chain."""
    t1 = Function("g", [Variable("x"), Variable("y")])
    t2 = Function("g", [Variable("y"), Constant("a")])

    subst = unify(t1, t2)

    assert subst is not None
    assert apply_subst(Variable("x"), subst) == Constant("a")
    assert apply_subst(Variable("y"), subst) == Constant("a")
    assert apply_subst(t1, subst) == apply_subst(t2, subst)


def test_constant_vs_function_fail():
    """A constant does not unify with a compound term."""
    assert unify(Constant("a"), Function("f", [Variable("x")])) is None


def test_input_subst_not_mutated():
    """Passing in a substitution does not mutate the caller's dict."""
    given = {"z": Constant("c")}
    snapshot = dict(given)
    result = unify(Variable("x"), Constant("a"), given)
    assert given == snapshot          # caller's dict untouched
    assert result == {"z": Constant("c"), "x": Constant("a")}


def test_atoms_via_parser():
    """Atoms produced by the parser unify identically to hand-built ones."""
    from unicode_fol_kit.fol.msflparser import MSFLParser

    parser = MSFLParser()
    a1 = parser.parse("P(x, a)")
    a2 = parser.parse("P(b, y)")

    subst = unify(a1, a2)
    assert subst is not None
    assert apply_subst(a1, subst) == apply_subst(a2, subst)


def test_atom_does_not_unify_with_function():
    """An Atom and a Function sharing name+arity are different categories -> None.

    Robinson unification is over a single term/literal language; a literal P(x)
    and a term f(x) are syntactically distinct kinds of node even if the symbol
    string matched, so they must not unify.
    """
    assert unify(Atom("f", [Variable("x")]), Function("f", [Variable("x")])) is None
    assert unify(Function("f", [Variable("x")]), Atom("f", [Variable("x")])) is None


def test_variable_swap_produces_acyclic_resolvable_mgu():
    """unify(f(x,y), f(y,x)) must yield a terminating, equalising MGU.

    A naive composer can build a cyclic substitution {x: y, y: x} here, which
    makes apply_subst loop forever. The correct unifier binds x to y once and
    leaves y free, so applying the MGU drives both sides to f(y, y) and never
    recurses without bound.
    """
    t1 = Function("f", [Variable("x"), Variable("y")])
    t2 = Function("f", [Variable("y"), Variable("x")])

    subst = unify(t1, t2)
    assert subst is not None
    # apply_subst must terminate (would raise RecursionError on a cyclic dict).
    left = apply_subst(t1, subst)
    right = apply_subst(t2, subst)
    assert left == right
    # Both x and y collapse to the same single variable.
    assert apply_subst(Variable("x"), subst) == apply_subst(Variable("y"), subst)


def test_chained_mgu_propagates_through_apply_subst():
    """unify(f(x, y), f(y, a)) yields an MGU under which x resolves to a.

    The binding y -> a is discovered after x -> y, so the returned substitution
    is triangular ({x: y, y: a}); apply_subst must follow the chain so that x
    ends up at the constant a, equalising both terms.
    """
    t1 = Function("f", [Variable("x"), Variable("y")])
    t2 = Function("f", [Variable("y"), Constant("a")])

    subst = unify(t1, t2)
    assert subst is not None
    assert apply_subst(Variable("x"), subst) == Constant("a")
    assert apply_subst(Variable("y"), subst) == Constant("a")
    assert apply_subst(t1, subst) == apply_subst(t2, subst)


def test_deeply_nested_function_unification():
    """unify(f(g(x), y), f(g(a), h(x))) binds x->a and y->h(a)."""
    t1 = Function("f", [Function("g", [Variable("x")]), Variable("y")])
    t2 = Function("f", [Function("g", [Constant("a")]), Function("h", [Variable("x")])])

    subst = unify(t1, t2)
    assert subst is not None
    assert apply_subst(Variable("x"), subst) == Constant("a")
    assert apply_subst(Variable("y"), subst) == Function("h", [Constant("a")])
    assert apply_subst(t1, subst) == apply_subst(t2, subst)
