"""Tests for the second-order -> HOL/THF export (unicode_fol_kit.hol.secondorder).

Structural assertions (the predicate quantifier and its inferred arity render as
a native higher-order binder; free vs bound predicates are handled; equality is
the uninterpreted feq/fneq alias; balanced syntax) plus faithfulness checks
against the finite-model evaluator semantics.secondorder.satisfies_so on small
hand-checked structures.
"""

import re

import pytest

from unicode_fol_kit import MSFLParser
from unicode_fol_kit.fol.nodes import (
    Variable, Constant, Number, Function,
    Atom, Not, Or, And, Iff, Quantifier, SecondOrderQuantifier,
)
from unicode_fol_kit.hol.secondorder import to_thf_so, to_isabelle_so
from unicode_fol_kit.semantics.tarski import Structure
from unicode_fol_kit.semantics.secondorder import satisfies_so


# --------------------------------------------------------------------------- #
# helpers
# --------------------------------------------------------------------------- #

def _parse(text):
    return MSFLParser(second_order=True).parse(text)


def _balanced(s):
    return s.count("(") == s.count(")")


def _thf_decls(thf):
    """Parse ``thf(<name>_decl, type, ( <functor> : <type> )).`` lines.

    Returns ``functor -> type`` and asserts the toolkit invariants any
    well-formed THF problem must satisfy: the declaration name matches its
    functor and each functor is declared at most once (a UNIQUE type per
    functor). Raises ``AssertionError`` on a duplicate / conflicting decl.
    """
    types = {}
    for declname, fn, typ in re.findall(
        r"thf\((\w+)_decl, type, \( (\w+) : (.+?) \)\)\.", thf
    ):
        assert declname == fn, (declname, fn)
        assert fn not in types, ("duplicate decl for functor", fn)
        types[fn] = typ
    return types


def _thf_goal(thf):
    """Return the single ``thf(goal, ...)`` line."""
    for ln in thf.splitlines():
        if ln.startswith("thf(goal,"):
            return ln
    raise AssertionError("no goal line in THF output")


def _thf_binders(goal):
    """The bound-variable tokens introduced by ``! [..]`` / ``? [..]`` in order."""
    return re.findall(r"[!?] \[(\w+):", goal)


def _assert_well_formed_thf(thf):
    """Every THF invariant the export must keep: unique-typed functors, balanced,
    no two binders sharing a token (no shadowing), every lowercase functor used in
    the goal declared in the signature."""
    types = _thf_decls(thf)
    assert _balanced(thf)
    goal = _thf_goal(thf)
    binders = _thf_binders(goal)
    assert len(binders) == len(set(binders)), ("shadowing binders", binders)
    used = set(re.findall(r"(?<![\w$])([a-z]\w*)", goal))
    used -= {"thf", "goal", "conjecture", "axiom"}
    assert used <= set(types), ("undeclared functors", used - set(types))
    return types, binders


EXCLUDED_MIDDLE = "∀P (P(a) ∨ ¬P(a))"
LEIBNIZ = "∀x ∀y (x = y ↔ ∀P (P(x) ↔ P(y)))"


# --------------------------------------------------------------------------- #
# THF structural
# --------------------------------------------------------------------------- #

def test_thf_monadic_predicate_quantifier_native_binder():
    thf = to_thf_so(_parse(EXCLUDED_MIDDLE))
    # ∀P maps DIRECTLY to a THF quantifier over a predicate-typed variable, with
    # the inferred arity-1 type $i > $o.
    assert "! [P: ( $i > $o )]" in thf
    # bound predicate variable applied to the free constant 'a'.
    assert "( P @ a )" in thf
    assert _balanced(thf)


def test_thf_bound_predicate_not_declared_free_individual_is():
    thf = to_thf_so(_parse(EXCLUDED_MIDDLE))
    # The second-order-bound P is a THF variable, not a problem symbol.
    assert "p_decl" not in thf
    # The free object variable 'a' is emitted as an $i constant.
    assert "thf(a_decl, type, ( a : $i ))." in thf


def test_thf_binary_predicate_variable_arity_two():
    thf = to_thf_so(_parse("∃R ∀x R(x, x)"))
    assert "? [R: ( $i > $i > $o )]" in thf
    assert "( R @ X @ X )" in thf
    assert _balanced(thf)


def test_thf_propositional_predicate_variable_arity_zero():
    thf = to_thf_so(_parse("∃P (P ∨ ¬P)"))
    assert "? [P: ( $o )]" in thf
    assert _balanced(thf)


def test_thf_leibniz_equality_is_uninterpreted_feq():
    thf = to_thf_so(_parse(LEIBNIZ))
    assert "! [X: $i]" in thf and "! [Y: $i]" in thf
    assert "! [P: ( $i > $o )]" in thf
    # `=` is the uninterpreted feq predicate, NOT primitive THF identity.
    assert "( feq @ X @ Y )" in thf
    assert "thf(feq_decl, type, ( feq : ( $i > $i > $o ) ))." in thf
    assert "( P @ X )" in thf and "( P @ Y )" in thf
    assert _balanced(thf)


def test_thf_free_predicate_declared():
    thf = to_thf_so(_parse("∃P ∀x (P(x) ↔ Q(x))"))
    # Q is free -> declared; P is bound -> not.
    assert "thf(q_decl, type, ( q : ( $i > $o ) ))." in thf
    assert "( P @ X )" in thf and "( q @ X )" in thf
    assert _balanced(thf)


def test_thf_conjecture_vs_axiom_role():
    f = _parse(EXCLUDED_MIDDLE)
    assert "thf(goal, conjecture," in to_thf_so(f, conjecture=True)
    assert "thf(goal, axiom," in to_thf_so(f, conjecture=False)


def test_thf_inequality_alias_fneq():
    thf = to_thf_so(_parse("∀x ∀y (x ≠ y ∨ ∀P (P(x) ↔ P(y)))"))
    assert "( fneq @ X @ Y )" in thf
    assert "fneq_decl" in thf
    assert _balanced(thf)


# --------------------------------------------------------------------------- #
# Isabelle structural
# --------------------------------------------------------------------------- #

def test_isabelle_monadic_predicate_quantifier_native():
    isa = to_isabelle_so(_parse(EXCLUDED_MIDDLE))
    assert "\\<forall>P::i \\<Rightarrow> bool." in isa
    assert "consts a :: \"i\"" in isa
    assert isa.lstrip().startswith("(*")
    assert "lemma" in isa
    assert isa.strip().endswith("end")
    assert _balanced(isa)


def test_isabelle_binary_predicate_variable_type():
    isa = to_isabelle_so(_parse("∃R ∀x R(x, x)"))
    assert "\\<exists>R::i \\<Rightarrow> i \\<Rightarrow> bool." in isa
    assert "(R x x)" in isa
    assert _balanced(isa)


def test_isabelle_propositional_predicate_variable_bool():
    isa = to_isabelle_so(_parse("∃P (P ∨ ¬P)"))
    assert "\\<exists>P::bool." in isa
    assert _balanced(isa)


def test_isabelle_leibniz_equality_uninterpreted():
    isa = to_isabelle_so(_parse(LEIBNIZ))
    assert "\\<forall>P::i \\<Rightarrow> bool." in isa
    assert "(feq x y)" in isa
    assert "consts feq :: \"i \\<Rightarrow> i \\<Rightarrow> bool\"" in isa
    assert _balanced(isa)


def test_isabelle_theory_name_used():
    isa = to_isabelle_so(_parse(EXCLUDED_MIDDLE), name="MyTheory")
    assert "theory MyTheory" in isa


# --------------------------------------------------------------------------- #
# faithfulness to satisfies_so (the finite-model evaluator)
# --------------------------------------------------------------------------- #

def test_faithful_excluded_middle_is_so_valid():
    # ∀P (P(a) ∨ ¬P(a)) holds in every structure (here a 2-element domain).
    struct = Structure(domain=(0, 1), constants={"a": 0}, predicates={})
    assert satisfies_so(_parse(EXCLUDED_MIDDLE), struct, {"a": 0}) is True


def test_faithful_universal_predicate_is_false():
    # ∀P P(a) is FALSE: take P empty. The export still renders the native binder.
    f = _parse("∀P P(a)")
    struct = Structure(domain=(0, 1), constants={"a": 0}, predicates={})
    assert satisfies_so(f, struct, {"a": 0}) is False
    assert "! [P: ( $i > $o )]" in to_thf_so(f)


def test_faithful_reflexive_relation_exists():
    # ∃R ∀x R(x,x): true (take R the full or identity relation).
    f = _parse("∃R ∀x R(x, x)")
    struct = Structure(domain=(0, 1), constants={}, predicates={})
    assert satisfies_so(f, struct) is True


def test_faithful_comprehension_holds():
    # ∃P ∀x (P(x) ↔ Q(x)) is always true (comprehension on Q).
    f = _parse("∃P ∀x (P(x) ↔ Q(x))")
    struct = Structure(domain=(0, 1), constants={}, predicates={"Q": {(0,)}})
    assert satisfies_so(f, struct) is True


def test_faithful_leibniz_holds_with_identity():
    # Leibniz: x=y ↔ (P(x)↔P(y)) for all P. The evaluator reads = as identity,
    # so over any finite structure this is true.
    struct = Structure(domain=(0, 1), constants={}, predicates={})
    assert satisfies_so(_parse(LEIBNIZ), struct) is True


def test_faithful_arity0_existential_true():
    struct = Structure(domain=(0, 1), constants={}, predicates={})
    assert satisfies_so(_parse("∃P (P ∨ ¬P)"), struct) is True


# --------------------------------------------------------------------------- #
# constructed (non-parser) nodes round-trip too
# --------------------------------------------------------------------------- #

def test_constructed_node_renders():
    # ∀P ∃x P(x) built directly from AST nodes.
    f = SecondOrderQuantifier(
        "∀", "P", 1,
        Quantifier("∃", Variable("x"), Atom("P", [Variable("x")])),
    )
    thf = to_thf_so(f)
    assert "! [P: ( $i > $o )]" in thf
    assert "? [X: $i]" in thf
    assert "( P @ X )" in thf
    assert _balanced(thf)
    isa = to_isabelle_so(f)
    assert "\\<forall>P::i \\<Rightarrow> bool." in isa
    assert "\\<exists>x::i." in isa


# --------------------------------------------------------------------------- #
# REGRESSION: bound predicate-var / bound object-var capture (faithfulness)
# --------------------------------------------------------------------------- #

def test_regression_capture_predicate_then_object_same_name():
    # ∃P ∀p P(p): predicate binder P then object binder p (case-folding equal).
    # Pre-fix this emitted '? [P:($i>$o)] : ! [P:$i] : ( P @ P )': the object
    # binder shadowed the predicate binder and P@P is ill-typed. The two binders
    # MUST now carry distinct uppercase tokens, and the application is well-typed
    # (predicate-typed head @ individual-typed argument).
    f = SecondOrderQuantifier(
        "∃", "P", 1,
        Quantifier("∀", Variable("p"), Atom("P", [Variable("p")])),
    )
    thf = to_thf_so(f)
    types, binders = _assert_well_formed_thf(thf)
    pred_tok, obj_tok = binders
    assert pred_tok != obj_tok, "predicate and object binders must not collide"
    assert f"? [{pred_tok}: ( $i > $o )]" in thf
    assert f"! [{obj_tok}: $i]" in thf
    assert f"( {pred_tok} @ {obj_tok} )" in thf
    # No problem-level decls: both symbols are bound variables.
    assert types == {}
    # Oracle: true (witness P = the full domain).
    s = Structure(domain=(0, 1), constants={}, predicates={})
    assert satisfies_so(f, s) is True


def test_regression_capture_object_then_predicate_same_name():
    # ∀Q ∃q Q(q): symmetric case, universal predicate then existential object.
    f = SecondOrderQuantifier(
        "∀", "Q", 1,
        Quantifier("∃", Variable("q"), Atom("Q", [Variable("q")])),
    )
    thf = to_thf_so(f)
    types, binders = _assert_well_formed_thf(thf)
    pred_tok, obj_tok = binders
    assert pred_tok != obj_tok
    assert f"! [{pred_tok}: ( $i > $o )]" in thf
    assert f"? [{obj_tok}: $i]" in thf
    assert f"( {pred_tok} @ {obj_tok} )" in thf
    assert types == {}
    # Oracle: false (counterexample Q = empty relation).
    s = Structure(domain=(0, 1), constants={}, predicates={})
    assert satisfies_so(f, s) is False


def test_regression_capture_uses_native_binder_and_arity():
    # The capture fix must not disturb the native-binder / inferred-arity render.
    f = _parse("∃P ∀p P(p)")
    thf = to_thf_so(f)
    _assert_well_formed_thf(thf)
    # arity-1 predicate type survives; exactly one predicate binder + one object.
    assert "( $i > $o )" in thf
    assert len(_thf_binders(_thf_goal(thf))) == 2


# --------------------------------------------------------------------------- #
# REGRESSION: free predicate / free individual functor collapse (soundness)
# --------------------------------------------------------------------------- #

def test_regression_free_predicate_and_free_individual_collapse():
    # P(p): free predicate P and free individual p both naively lower-case to the
    # functor 'p'. Pre-fix this emitted a duplicate 'p_decl' with CONFLICTING
    # types (p:($i>$o) and p:$i) plus an ill-typed '( p @ p )'. The two free
    # symbols MUST get distinct, single-typed functors.
    f = Atom("P", [Variable("p")])
    thf = to_thf_so(f)
    types, binders = _assert_well_formed_thf(thf)
    assert binders == []           # nothing bound
    # exactly two functors, one predicate-typed, one individual-typed, distinct.
    pred_fns = [fn for fn, t in types.items() if t == "( $i > $o )"]
    ind_fns = [fn for fn, t in types.items() if t == "$i"]
    assert len(pred_fns) == 1 and len(ind_fns) == 1
    assert pred_fns[0] != ind_fns[0]
    # the goal applies the predicate functor to the individual functor.
    assert f"( {pred_fns[0]} @ {ind_fns[0]} )" in _thf_goal(thf)


def test_regression_isabelle_free_predicate_and_individual_distinct_consts():
    # The Isabelle path must also de-collide: P(p) (free predicate P + free
    # individual p) previously emitted TWO `consts p` (i and i⇒bool) — which
    # Isabelle rejects as a duplicate constant declaration.
    isa = to_isabelle_so(Atom("P", [Variable("p")]))
    consts = [ln.split()[1] for ln in isa.splitlines() if ln.strip().startswith("consts")]
    assert len(consts) == 2 and len(set(consts)) == 2   # two distinct const names
    # Foo + foo case folds the same way and must also stay distinct.
    isa2 = to_isabelle_so(And(Atom("Foo", [Constant("c")]), Atom("Q", [Constant("foo")])))
    names2 = [ln.split()[1] for ln in isa2.splitlines() if ln.strip().startswith("consts")]
    assert len(names2) == len(set(names2))              # no duplicate consts


def test_regression_free_predicate_and_constant_case_collapse():
    # Foo(c) ∧ Q(foo): free predicate 'Foo' lower-cases to 'foo', clashing with
    # the individual constant 'foo'. They MUST de-collide to distinct functors,
    # each declared once with its own type.
    f = And(Atom("Foo", [Constant("c")]), Atom("Q", [Constant("foo")]))
    thf = to_thf_so(f)
    types, _ = _assert_well_formed_thf(thf)
    # 'Foo' (predicate) and 'foo' (individual) -> two functors, distinct, with the
    # predicate one typed ($i>$o) and the individual one typed $i.
    pred_typed = sorted(fn for fn, t in types.items() if t == "( $i > $o )")
    ind_typed = sorted(fn for fn, t in types.items() if t == "$i")
    assert len(set(pred_typed) & set(ind_typed)) == 0
    assert "foo" in (pred_typed + ind_typed)
    # no functor is declared twice (already enforced) and at least 4 symbols.
    assert len(types) == 4   # Foo, Q (preds) + c, foo (individuals)


def test_regression_free_collapse_usage_matches_declaration():
    # Every functor used in the goal of P(p) is backed by exactly one declaration
    # of the right type (no usage referring to an undeclared / mistyped functor).
    thf = to_thf_so(Atom("P", [Variable("p")]))
    types = _thf_decls(thf)
    goal = _thf_goal(thf)
    for fn in re.findall(r"(?<![\w$])([a-z]\w*)", goal):
        if fn in ("thf", "goal", "conjecture", "axiom"):
            continue
        assert fn in types, (fn, "used but not declared")


def test_regression_distinct_free_individuals_not_overmerged():
    # De-collision must not accidentally merge symbols that were already distinct:
    # constant 'a', free var 'b', number 7 -> three distinct individual functors.
    f = And(Atom("R", [Constant("a"), Variable("b")]), Atom("S", [Number(7)]))
    thf = to_thf_so(f)
    types, _ = _assert_well_formed_thf(thf)
    ind_fns = [fn for fn, t in types.items() if t == "$i"]
    assert len(ind_fns) == len(set(ind_fns)) == 3
