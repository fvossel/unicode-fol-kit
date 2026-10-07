r"""``Node.to_tptp()`` of ONE formula must never write two kit symbols as one word.

``to_tptp`` folds the first character of a predicate / function / constant name
to lower-case, so ``gaseous`` and ``Gaseous`` are both written ``gaseous``. The
problem writers refuse that across a whole problem; the single-formula render had
no guard, and::

    Iff(P(gaseous), P(Gaseous)).to_tptp()   ->   (p(gaseous) <=> p(gaseous))

was a tautology written out of a non-theorem. The OUTERMOST ``to_tptp`` call now
checks the formula it renders (``fol/_tptp_symbols.py``), through the same check
the writers run.

SEMANTICS the cases below are derived from (never from what the code prints):

* two DISTINCT constants / predicates / functions are two symbols; in
  ``P(a) <-> P(b)`` with ``a != b`` there is a model where ``P`` holds of one and
  not of the other, so the formula is satisfiable and NOT valid, while its merged
  image ``p(a) <=> p(a)`` is valid;
* a predicate and a function/constant are different KINDS of symbol: ``Agent(x)``
  and ``agent(x)`` never interact, and a TPTP reader that resolves a bare
  identifier by position reads ``agent(agent(X))`` back as ``Agent(agent(x))``;
* the same name repeating is one symbol, whatever its arity or position.

Decisions under test: D1 same-kind collision of two legal names is REFUSED (no
renaming); D3 a cross-kind clash is NOT refused for one formula; D4 the asymmetry
is documented where a user will find it.
"""

import gc
import inspect
import pydoc
import random
import threading
from contextlib import contextmanager
from dataclasses import dataclass
from typing import Iterable, List

import pytest

import unicode_logic_kit
import unicode_logic_kit.dl  # noqa: F401  (import every package that may define a Node)
import unicode_logic_kit.drt  # noqa: F401
from unicode_logic_kit.atp import _tptp_problem
from unicode_logic_kit.atp._tptp_problem import (
    generate_tptp_problem, generate_tptp_problem_with_mapping,
)
from unicode_logic_kit.fol import _tptp_symbols as symbols
from unicode_logic_kit.fol._fol_nodes import constant_name_to_ascii
from unicode_logic_kit.fol.nodes import (
    And, Atom, Box, Constant, Contrast, Count, Function, Iff, Implies, Measure,
    Node, Not, Number, Or, Quantifier, SortedConstant, SortedCount,
    SortedQuantifier, Variable, Xor, to_fol,
)
from unicode_logic_kit.fol.tptp_input import parse_tptp_formula
from unicode_logic_kit.mcp import server

X, Y, Z = Variable("x"), Variable("y"), Variable("z")
A, B = Constant("a"), Constant("b")


def refusal(node: Node) -> str:
    """The message of the NotImplementedError ``node.to_tptp()`` raises."""
    with pytest.raises(NotImplementedError) as excinfo:
        node.to_tptp()
    return str(excinfo.value)


@contextmanager
def unguarded():
    """Render with a render 'already in progress': every call nests, none scans.

    This is exactly what ``to_tptp`` did before the guard existed (the nested
    path returns the original bound methods), so it is the reference for
    'byte-identical output'."""
    token = symbols._RENDERING.set(symbols._RenderLog())
    try:
        yield
    finally:
        symbols._RENDERING.reset(token)


def unguarded_text(node: Node) -> str:
    with unguarded():
        return node.to_tptp()


def all_node_classes() -> List[type]:
    gc.collect()                      # a class whose creation failed is garbage, not a node class
    seen, stack = set(), [Node]
    while stack:
        for sub in stack.pop().__subclasses__():
            if sub not in seen:
                seen.add(sub)
                stack.append(sub)
    return sorted(seen, key=lambda c: (c.__module__, c.__qualname__))


# ---------------------------------------------------------------------------
# The three reported holes, and what the refusal says.
# ---------------------------------------------------------------------------

def test_two_constants_that_fold_together_are_refused():
    # P(gaseous) <-> P(Gaseous): two constants, NOT valid; merged: a tautology.
    formula = Iff(Atom("P", (Constant("gaseous"),)), Atom("P", (Constant("Gaseous"),)))
    message = refusal(formula)
    assert "'gaseous'" in message and "'Gaseous'" in message
    assert "TPTP identifier 'gaseous'" in message
    assert "constant/function" in message


def test_two_predicates_that_fold_together_are_refused():
    formula = Iff(Atom("Foo", (A,)), Atom("foo", (A,)))
    message = refusal(formula)
    assert "predicate names 'Foo' and 'foo'" in message
    assert "TPTP identifier 'foo'" in message


def test_two_functions_that_fold_together_are_refused():
    formula = Atom("=", [Function("Bar", (A,)), Function("bar", (A,))])
    message = refusal(formula)
    assert "function names 'Bar' and 'bar'" in message
    assert "TPTP identifier 'bar'" in message


def test_a_function_and_a_constant_share_one_namespace():
    # f(a) and a constant spelled 'Bar' vs 'bar' still fold together.
    formula = And(Atom("P", (Function("Bar", (A,)),)), Atom("P", (Constant("bar"),)))
    message = refusal(formula)
    assert "'Bar' and 'bar'" in message
    assert "constant/function" in message          # the second name met is a constant


def test_the_message_names_the_remedy():
    message = refusal(Iff(Atom("Foo", (A,)), Atom("foo", (A,))))
    assert "rename one of them" in message
    assert "refusing to silently merge" in message


def test_transliteration_makes_two_constants_collide():
    # θ is written 'theta' (constant_name_to_ascii), so θ and theta are one word.
    assert constant_name_to_ascii("θ") == "theta"
    message = refusal(Iff(Atom("P", (Constant("θ"),)), Atom("P", (Constant("theta"),))))
    assert "'θ' and 'theta'" in message and "'theta'" in message


# ---------------------------------------------------------------------------
# What is NOT refused.
# ---------------------------------------------------------------------------

def test_the_same_name_repeating_is_one_symbol():
    formula = And(Atom("Foo", (A,)), Atom("Foo", (B, A)))      # Foo at two arities
    assert formula.to_tptp() == "(foo(a) & foo(b,a))"


def test_names_with_different_words_are_not_refused():
    assert Iff(Atom("Foo", (A,)), Atom("Bar", (A,))).to_tptp() == "(foo(a) <=> bar(a))"


def test_a_name_used_as_constant_and_as_function_is_one_name():
    # same kit name 'f' in the term namespace twice: one symbol, not a collision
    formula = Atom("=", [Constant("f"), Function("f", (A,))])
    assert formula.to_tptp() == "(f = f(a))"


def test_equality_and_arithmetic_tokens_never_collide():
    formula = And(Atom("=", [A, B]), And(Atom("≠", [A, B]), Atom("<", [A, B])))
    assert formula.to_tptp() == "((a = b) & ((a != b) & $less(a,b)))"
    arith = Atom("=", [Function("+", (A, B)), Function("*", (A, B))])
    assert arith.to_tptp() == "($sum(a,b) = $product(a,b))"


def test_cross_kind_clash_is_not_refused_for_one_formula():
    # D3. Agent(agent(e)) — the class Agent and the role function agent.
    formula = Atom("Agent", (Function("agent", (Variable("e"),)),))
    assert formula.to_tptp() == "agent(agent(E))"


def test_cross_kind_text_reads_back_as_the_same_formula():
    """The premise of D3, verified rather than trusted: the kit's own TPTP reader
    resolves a bare identifier by position, so the text of ONE formula is
    unambiguous and reads back as the formula it was written from.

    Hand-derived reading: an identifier immediately applied inside an argument
    list (or an equality operand) is a function/constant; one in formula position
    is a predicate, whose first letter the reader capitalises (``agent`` ->
    ``Agent``); variables are upper-case words, read back lower-case."""
    cases = [
        Atom("Agent", (Function("agent", (Variable("e"),)),)),
        Quantifier("∀", Variable("e"), Atom("Agent", (Function("agent", (Variable("e"),)),))),
        Atom("Car", (Constant("car"),)),
        And(Atom("Price", (X,)), Atom("Q", (Function("price", (X, Y)),))),   # two arities
        And(Atom("P", ()), Atom("Q", (Constant("p"),))),                     # nullary vs constant
        Atom("=", [Constant("car"), Function("car", (A,))]),
        And(Atom("Car", (X,)), Atom("=", [Constant("car"), X])),
    ]
    for formula in cases:
        text = formula.to_tptp()                        # not refused
        assert parse_tptp_formula(text) == formula, text


def test_cross_kind_read_back_over_a_random_battery():
    words = ["agent", "car", "price", "p", "q", "human", "theme"]
    variables = [X, Y, Z]
    rng = random.Random(7)

    def term(depth):
        if depth <= 0 or rng.random() < 0.3:
            return rng.choice(variables) if rng.random() < 0.5 else Constant(rng.choice(words))
        return Function(rng.choice(words), [term(depth - 1) for _ in range(rng.randint(1, 3))])

    def formula(depth):
        roll = rng.random()
        if depth <= 0 or roll < 0.35:
            word = rng.choice(words)
            return Atom(word[0].upper() + word[1:], [term(2) for _ in range(rng.randint(0, 3))])
        if roll < 0.45:
            return Not(formula(depth - 1))
        if roll < 0.55:
            return Quantifier(rng.choice("∀∃"), rng.choice(variables), formula(depth - 1))
        if roll < 0.6:
            return Atom("=", [term(2), term(2)])
        return rng.choice([And, Or, Implies, Iff, Xor])(formula(depth - 1), formula(depth - 1))

    clashes = 0
    for _ in range(400):
        f = formula(4)
        text = f.to_tptp()          # predicates are Capitalised, terms lower-case: never same-kind
        assert parse_tptp_formula(text) == f, text
        predicate_words = {a.predicate.lower() for a in f.atoms() if a.predicate != "="}
        term_words = {n.name for n in f.walk() if isinstance(n, (Function, Constant))}
        clashes += bool(predicate_words & term_words)
    assert clashes > 100            # the battery really exercises cross-kind clashes


# ---------------------------------------------------------------------------
# Exact text of collision-free formulas (hand-derived from the grammar).
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("formula, expected", [
    (Quantifier("∀", X, Implies(Atom("Human", (X,)), Atom("Mortal", (X,)))),
     "(![X]: (human(X) => mortal(X)))"),
    (Not(Atom("Raining", ())), "~(raining)"),
    (And(Atom("P", (A, B)), Atom("=", [A, Function("f", (B,))])), "(p(a,b) & (a = f(b)))"),
    (Atom("≤", [Function("+", (X, Number(1))), Number(3)]), "$lesseq($sum(X,1),3)"),
    (Quantifier("∃", Y, Xor(Atom("Q", (Y,)), Atom("R", (Y,)))), "(?[Y]: (q(Y) <~> r(Y)))"),
    (Atom("BDouble", (Variable("a"),)), "bDouble(A)"),
    (Atom("P", (Constant("θ"),)), "p(theta)"),
    (Contrast(Atom("P", ()), Atom("Q", ())), "(p & q)"),
    (Or(Atom("P", ()), Not(Atom("P", ()))), "(p | ~(p))"),
    (SortedQuantifier("∀", X, "Human", Atom("Mortal", (X,))), "(![X]: (human(X) => mortal(X)))"),
    (SortedQuantifier("∃", X, "Human", Atom("Mortal", (X,))), "(?[X]: (human(X) & mortal(X)))"),
    (Atom("P", (SortedConstant("alice", "Human"),)), "p(alice)"),
    (Atom("P", (Measure(A, Constant("d")),)), "p(measure(a,d))"),
])
def test_collision_free_text_is_exactly_the_text_it_always_was(formula, expected):
    assert formula.to_tptp() == expected
    assert unguarded_text(formula) == expected


def test_a_sort_named_like_a_predicate_is_one_symbol_not_a_collision():
    # Relativising x:Human to Human(x) makes the sort and the predicate Human the
    # SAME symbol by construction; only DIFFERENT spellings are distinct. (This is
    # the kit's definition of a sort: z3, this render and the Prover9 writer read it
    # so. TF0 cannot say it, so the TF0 writer REFUSES a sort and a predicate that
    # share a word: tests/test_tptp_writer_names.py.)
    formula = SortedQuantifier("∀", X, "Human", Atom("Human", (X,)))
    assert formula.to_tptp() == "(![X]: (human(X) => human(X)))"


# ---------------------------------------------------------------------------
# (e) The scan reads what is RENDERED, so names a reduction introduces count.
# ---------------------------------------------------------------------------

def test_sorted_quantifier_guard_predicate_collides_with_a_user_predicate():
    # ∀x:Foo foo(x) means "every Foo is foo": satisfiable, not valid. It reduces
    # to ∀x (Foo(x) -> foo(x)), written (![X]: (foo(X) => foo(X))) — valid.
    formula = SortedQuantifier("∀", X, "Foo", Atom("foo", (X,)))
    assert {a.predicate for a in formula.atoms()} == {"foo"}    # the SOURCE has one name
    assert {a.predicate for a in to_fol(formula).atoms()} == {"Foo", "foo"}
    message = refusal(formula)
    assert "predicate names 'Foo' and 'foo'" in message
    assert unguarded_text(formula) == "(![X]: (foo(X) => foo(X)))"      # what used to be written


def test_sorted_count_guard_predicate_collides_with_a_user_predicate():
    formula = SortedCount("ge", Number(2), X, "Foo", Atom("foo", (X,)))
    assert {a.predicate for a in formula.atoms()} == {"foo"}
    assert "predicate names 'Foo' and 'foo'" in refusal(formula)


def test_sorted_constant_collides_with_a_constant_of_the_other_spelling():
    formula = Iff(Atom("P", (SortedConstant("gaseous", "S"),)), Atom("P", (Constant("Gaseous"),)))
    message = refusal(formula)
    assert "'gaseous' and 'Gaseous'" in message
    # two sorted constants too
    two = Iff(Atom("P", (SortedConstant("gaseous", "S"),)), Atom("P", (SortedConstant("Gaseous", "S"),)))
    assert "'gaseous' and 'Gaseous'" in refusal(two)


def test_count_expansion_is_scanned_too():
    formula = Count("ge", Number(2), X, And(Atom("Foo", (X,)), Atom("foo", (X,))))
    assert "predicate names 'Foo' and 'foo'" in refusal(formula)
    clean = Count("ge", Number(2), X, And(Atom("Foo", (X,)), Atom("Bar", (X,))))
    assert "foo(" in clean.to_tptp() and "bar(" in clean.to_tptp()


def test_measure_writes_the_function_measure():
    # Measure(a, d) IS the function `measure` (Measure.to_z3 declares exactly
    # that), so it collides with a differently spelled Function('Measure') ...
    clash = Atom("P", (Measure(A, Constant("d")), Function("Measure", (A,))))
    message = refusal(clash)
    assert "function names 'measure' and 'Measure'" in message
    # ... and is one symbol with Function('measure'), spelled the same.
    same = Atom("P", (Measure(A, Constant("d")), Function("measure", (A, Constant("d")))))
    assert same.to_tptp() == "p(measure(a,d),measure(a,d))"


# ---------------------------------------------------------------------------
# (a) Every node class is covered, and a future one is covered without edits.
# ---------------------------------------------------------------------------

def unguarded_classes(classes: Iterable[type]) -> List[type]:
    return [cls for cls in classes if not symbols.is_guarded(cls)]


def test_every_node_class_has_a_guarded_to_tptp():
    classes = all_node_classes()
    assert len(classes) >= 60, "the subclass walk found too few node classes"
    assert unguarded_classes(classes + [Node]) == []
    # the families are really in the walk (factory-built Lambek / linear classes too)
    names = {cls.__name__ for cls in classes}
    assert {"Atom", "Box", "SortedQuantifier", "WeakConjunction", "Lambda", "Tensor",
            "Dependence", "At", "Always"} <= names


def test_the_meta_test_fails_for_a_class_that_escaped_the_guard():
    @dataclass(frozen=True)
    class Escaped(Node):
        def to_tptp(self):
            return "x"

    assert unguarded_classes([Escaped]) == []
    Escaped.to_tptp = lambda self: "x"          # a later monkeypatch bypasses __init_subclass__
    assert unguarded_classes([Escaped]) == [Escaped]
    assert unguarded_classes(all_node_classes()) == [Escaped]
    symbols.guard_class(Escaped)                # repaired: nothing is left behind for other tests
    assert unguarded_classes(all_node_classes()) == []


@dataclass(frozen=True)
class _Pair(Node):
    """A future node family: renders two formulas side by side, defining its own to_tptp."""

    left: Node
    right: Node

    def to_tptp(self) -> str:
        return f"[{self.left.to_tptp()} ~ {self.right.to_tptp()}]"


class _RenderMixin:
    def to_tptp(self) -> str:
        return f"<{self.left.to_tptp()} ~ {self.right.to_tptp()}>"


@dataclass(frozen=True)
class _MixedPair(_RenderMixin, Node):
    """A future node whose to_tptp comes from a mixin placed BEFORE Node in the MRO."""

    left: Node
    right: Node


@dataclass(frozen=True)
class _Plain(Node):
    """A future node that defines no to_tptp at all (inherits the raising base)."""

    left: Node


def test_a_future_subclass_with_its_own_to_tptp_is_covered():
    assert symbols.is_guarded(_Pair)
    assert _Pair(Atom("P", (A,)), Atom("Q", (A,))).to_tptp() == "[p(a) ~ q(a)]"
    clash = _Pair(Atom("Foo", (A,)), Atom("foo", (A,)))
    assert "predicate names 'Foo' and 'foo'" in refusal(clash)


def test_a_future_subclass_getting_to_tptp_from_a_mixin_is_covered():
    assert symbols.is_guarded(_MixedPair)
    assert _MixedPair(Atom("P", (A,)), Atom("Q", (A,))).to_tptp() == "<p(a) ~ q(a)>"
    assert "constant/function names" in refusal(_MixedPair(Atom("P", (Constant("x1"),)),
                                                          Atom("P", (Constant("X1"),))))


def test_a_future_subclass_without_to_tptp_inherits_a_guarded_refusal():
    assert symbols.is_guarded(_Plain)
    with pytest.raises(NotImplementedError):
        _Plain(A).to_tptp()


def test_a_to_tptp_that_cannot_be_wrapped_is_refused_rather_than_left_as_a_hole():
    # guard_class is what Node.__init_subclass__ calls; a class that is not a Node
    # stands in, so no half-created class lingers in Node.__subclasses__().
    class Static:
        @staticmethod
        def to_tptp():
            return "x"

    with pytest.raises(TypeError, match="plain method"):
        symbols.guard_class(Static)


def test_node_init_subclass_is_what_installs_the_guard():
    class Fresh(Node):
        def to_tptp(self):
            return "fresh"

    assert isinstance(inspect.getattr_static(Fresh, "to_tptp"), symbols.GuardedToTptp)
    assert Fresh.__dict__["to_tptp"].__wrapped__.__name__ == "to_tptp"


def test_class_access_is_the_guarded_function_and_documented():
    assert Atom.to_tptp.__doc__ and "TPTP" in Atom.to_tptp.__doc__
    assert Atom.to_tptp.__name__ == "to_tptp"
    assert str(inspect.signature(Atom.to_tptp)) == "(self) -> str"        # follows __wrapped__
    assert "to_tptp" in pydoc.render_doc(Atom)                             # help() / pydoc still work
    assert "to_tptp" in dict(inspect.getmembers(Atom))
    # unbound use on an instance is guarded as well
    with pytest.raises(NotImplementedError):
        Iff.to_tptp(Iff(Atom("Foo", (A,)), Atom("foo", (A,))))


# ---------------------------------------------------------------------------
# (b) one scan per outermost call, (c) exception safety, (d) threads / re-entrancy
# ---------------------------------------------------------------------------

@pytest.fixture
def scans(monkeypatch):
    calls: List[int] = []
    real = symbols._scan_rendered_symbols

    def counting(log):
        calls.append(len(log.symbols))
        return real(log)

    monkeypatch.setattr(symbols, "_scan_rendered_symbols", counting)
    return calls


def deep_conjunction(depth: int) -> Node:
    formula: Node = Atom("P", (A,))
    for _ in range(depth):
        formula = And(formula, Atom("Q", (B,)))
    return formula


def test_exactly_one_scan_per_outermost_call(scans):
    big = deep_conjunction(60)                      # 120 nested to_tptp calls
    big.to_tptp()
    assert len(scans) == 1
    big.to_tptp()
    Atom("P", (A,)).to_tptp()
    assert len(scans) == 3
    assert scans[0] == 4                            # P, a, Q, b — each name once


def test_a_reducing_family_is_still_one_scan(scans):
    SortedQuantifier("∀", X, "Human", Atom("Mortal", (X,))).to_tptp()
    Count("ge", Number(3), X, Atom("P", (X,))).to_tptp()
    assert len(scans) == 2


def test_a_refused_collision_is_one_scan_and_a_family_refusal_is_none(scans):
    with pytest.raises(NotImplementedError):
        Iff(Atom("Foo", (A,)), Atom("foo", (A,))).to_tptp()
    assert len(scans) == 1
    with pytest.raises(NotImplementedError):
        Box(Atom("P", ())).to_tptp()               # the family's own refusal: never reaches a scan
    assert len(scans) == 1


def test_the_render_state_is_clean_after_every_kind_of_exit():
    assert symbols._RENDERING.get() is None
    collision = Iff(Atom("Foo", (A,)), Atom("foo", (A,)))
    with pytest.raises(NotImplementedError):
        collision.to_tptp()
    assert symbols._RENDERING.get() is None
    with pytest.raises(NotImplementedError):
        And(Atom("P", ()), Box(Atom("Q", ()))).to_tptp()       # raised from deep inside
    assert symbols._RENDERING.get() is None
    with pytest.raises(ValueError):
        Quantifier("bogus", X, Atom("P", (X,))).to_tptp()      # an unrelated error type
    assert symbols._RENDERING.get() is None


def test_refusal_then_valid_then_refusal_again():
    collision = Iff(Atom("Foo", (A,)), Atom("foo", (A,)))
    valid = Iff(Atom("Foo", (A,)), Atom("Bar", (A,)))
    refusal(collision)
    assert valid.to_tptp() == "(foo(a) <=> bar(a))"
    refusal(collision)                              # still guarded: not skipped after a refusal


def test_family_refusal_then_collision_then_valid():
    collision = Iff(Atom("Foo", (A,)), Atom("foo", (A,)))
    with pytest.raises(NotImplementedError, match="modal|Modal|Box|□"):
        And(Atom("Foo", (A,)), Box(Atom("foo", (A,)))).to_tptp()
    refusal(collision)                              # guarded again after a family's own error
    assert Atom("Foo", (A,)).to_tptp() == "foo(a)"
    # and the other order: valid, family refusal, valid
    assert Atom("Baz", ()).to_tptp() == "baz"
    with pytest.raises(NotImplementedError):
        Box(Atom("Baz", ())).to_tptp()
    assert Atom("Baz", ()).to_tptp() == "baz"


def test_a_nested_family_error_does_not_hide_the_collision_after_it():
    # The family's refusal wins over a collision it never got to scan; it must
    # not leave a half-built log behind that poisons the next render.
    with pytest.raises(NotImplementedError):
        And(Iff(Atom("Foo", (A,)), Atom("foo", (A,))), Box(Atom("P", ()))).to_tptp()
    assert Atom("Foo", (A,)).to_tptp() == "foo(a)"          # NOT contaminated by 'foo' seen before
    assert Atom("foo", (A,)).to_tptp() == "foo(a)"


def test_nested_reentrant_render_is_one_scan_and_its_names_join_the_outer_one(scans):
    @dataclass(frozen=True)
    class Reentrant(Node):
        inner: Node

        def to_tptp(self) -> str:
            return "{" + self.inner.to_tptp() + "}"

    inner_clash = Iff(Atom("Foo", (A,)), Atom("foo", (A,)))
    outer = And(Reentrant(Atom("Foo", (A,))), Atom("foo", (B,)))      # clash only across the two
    assert "predicate names 'Foo' and 'foo'" in refusal(outer)
    assert len(scans) == 1
    scans.clear()
    assert "predicate names" in refusal(Reentrant(inner_clash))
    assert len(scans) == 1


def test_a_render_in_another_thread_is_still_guarded():
    """A contextvar, not a module flag: while thread A is INSIDE a render, thread
    B's outermost call is its own outermost call and scans."""
    inside, release = threading.Event(), threading.Event()
    outcome = {}

    class Held(Node):
        def to_tptp(self) -> str:
            inside.set()
            assert release.wait(10)
            return "held"

    def hold():
        outcome["held"] = Held().to_tptp()

    thread = threading.Thread(target=hold)
    thread.start()
    try:
        assert inside.wait(10)
        # thread A is mid-render. If 'in progress' were a global, this would nest and skip the scan.
        assert "predicate names 'Foo' and 'foo'" in refusal(Iff(Atom("Foo", (A,)), Atom("foo", (A,))))
        assert Atom("Foo", (A,)).to_tptp() == "foo(a)"
    finally:
        release.set()
        thread.join(10)
    assert outcome["held"] == "held"


def test_many_threads_each_get_their_own_verdict():
    clash = Iff(Atom("Foo", (A,)), Atom("foo", (A,)))
    fine = Iff(Atom("Foo", (A,)), Atom("Bar", (A,)))
    results: List[object] = [None] * 16
    start = threading.Barrier(16)

    def work(index: int):
        start.wait(10)
        for _ in range(200):
            try:
                text = (clash if index % 2 else fine).to_tptp()
            except NotImplementedError:
                text = "refused"
            if results[index] not in (None, text):
                results[index] = "inconsistent"
                return
            results[index] = text

    threads = [threading.Thread(target=work, args=(i,)) for i in range(16)]
    for t in threads:
        t.start()
    for t in threads:
        t.join(30)
    assert results == ["(foo(a) <=> bar(a))" if i % 2 == 0 else "refused" for i in range(16)]


# ---------------------------------------------------------------------------
# (f) Byte-identical output without a collision — against the unguarded render.
# ---------------------------------------------------------------------------

_PREDICATES = ["P", "Q", "Human", "Mortal", "Foo", "foo", "Bar", "BAR", "Agent", "agent", "Raining"]
_FUNCTIONS = ["f", "g", "agent", "Bar", "bar", "Car", "measure"]
_CONSTANTS = ["a", "b", "alice", "Alice", "car", "gaseous", "Gaseous", "θ", "theta", "x1", "X1"]
_SORTS = ["Human", "Foo", "S", "foo"]


def random_formula(rng: random.Random, depth: int = 4) -> Node:
    """A random formula over small name pools in which case-pairs are common, so
    roughly half of the battery collides and half does not."""
    predicates = rng.sample(_PREDICATES, rng.randint(1, 3))
    functions = rng.sample(_FUNCTIONS, rng.randint(1, 2))
    constants = rng.sample(_CONSTANTS, rng.randint(1, 3))
    sorts = rng.sample(_SORTS, 2)
    variables = [X, Y, Z]

    def term(d):
        roll = rng.random()
        if d <= 0 or roll < 0.35:
            pick = rng.random()
            if pick < 0.45:
                return rng.choice(variables)
            if pick < 0.9:
                return Constant(rng.choice(constants))
            if pick < 0.95:
                return Number(rng.randint(0, 9))
            return SortedConstant(rng.choice(constants), rng.choice(sorts))
        if roll < 0.45:
            return Measure(term(d - 1), term(d - 1))
        if roll < 0.55:
            return Function(rng.choice(["+", "-", "*", "/"]), [term(d - 1), term(d - 1)])
        return Function(rng.choice(functions), [term(d - 1) for _ in range(rng.randint(1, 3))])

    def form(d):
        roll = rng.random()
        if d <= 0 or roll < 0.3:
            pick = rng.random()
            if pick < 0.15:
                return Atom(rng.choice(["=", "≠", "<", ">", "≤", "≥"]), [term(2), term(2)])
            return Atom(rng.choice(predicates), [term(2) for _ in range(rng.randint(0, 3))])
        if roll < 0.38:
            return Not(form(d - 1))
        if roll < 0.5:
            return Quantifier(rng.choice("∀∃"), rng.choice(variables), form(d - 1))
        if roll < 0.56:
            return SortedQuantifier(rng.choice("∀∃"), rng.choice(variables), rng.choice(sorts), form(d - 1))
        if roll < 0.60:
            return Count(rng.choice(["ge", "le", "eq"]), Number(rng.randint(1, 3)),
                         rng.choice(variables), form(d - 1))
        if roll < 0.63:
            return SortedCount(rng.choice(["ge", "le", "eq"]), Number(rng.randint(1, 2)),
                               rng.choice(variables), rng.choice(sorts), form(d - 1))
        op = rng.choice([And, Or, Xor, Implies, Iff, Contrast])
        return op(form(d - 1), form(d - 1))

    return form(depth)


def oracle_has_same_kind_collision(formula: Node) -> bool:
    """An independent restatement of the rule, written from the semantics: two
    DISTINCT names of one namespace are one word iff their first-letter-lowered
    spellings are equal. Walks the FOL image (what is actually rendered)."""
    def word(name):
        return name[:1].lower() + name[1:]

    seen = {"predicate": {}, "term": {}}
    arithmetic = {"+", "-", "*", "/"}
    operators = {"=", "≠", "<", ">", "≤", "≥"}
    for node in to_fol(formula).walk():
        if isinstance(node, Atom) and node.predicate not in operators:
            key, name, w = "predicate", node.predicate, word(node.predicate)
        elif isinstance(node, Function) and node.name not in arithmetic:
            key, name, w = "term", node.name, word(node.name)
        elif isinstance(node, Constant):
            key, name, w = "term", node.name, word(constant_name_to_ascii(node.name))
        elif isinstance(node, Measure):
            key, name, w = "term", "measure", "measure"
        else:
            continue
        if seen[key].setdefault(w, name) != name:
            return True
    return False


def test_battery_guarded_equals_unguarded_without_collision_and_refuses_with_one():
    rng = random.Random(20260930)
    clean = colliding = 0
    families = set()
    for _ in range(1500):
        formula = random_formula(rng)
        families.update(type(n).__name__ for n in formula.walk())
        expected = unguarded_text(formula)
        if oracle_has_same_kind_collision(formula):
            colliding += 1
            with pytest.raises(NotImplementedError, match="would both render as the TPTP identifier"):
                formula.to_tptp()
        else:
            clean += 1
            assert formula.to_tptp() == expected               # byte-identical
    assert clean > 400 and colliding > 150
    assert {"SortedQuantifier", "SortedCount", "SortedConstant", "Count", "Measure",
            "Contrast", "Number"} <= families


def test_a_deep_formula_renders_with_the_depth_it_had_before_the_guard():
    """A nested call costs no extra stack frame (the descriptor hands back the
    ORIGINAL bound method), so a left-nested conjunction deeper than half the
    interpreter's limit — impossible with a wrapper function on every level —
    still renders, and to the same text."""
    import sys
    depth = max(200, (sys.getrecursionlimit() * 8) // 10 - 150)
    formula = deep_conjunction(depth)
    text = formula.to_tptp()
    assert text.count("&") == depth
    assert text == unguarded_text(formula)


# ---------------------------------------------------------------------------
# (g) The writers: one check, same words, premise-by-premise rendering unchanged.
# ---------------------------------------------------------------------------

def test_the_writers_same_kind_refusal_is_word_for_word_what_it_was():
    with pytest.raises(NotImplementedError) as excinfo:
        generate_tptp_problem([Atom("Foo", (A,))], Atom("foo", (A,)))
    assert str(excinfo.value) == (
        "generate_tptp_problem: distinct predicate names 'Foo' and 'foo' would both "
        "render as the TPTP identifier 'foo' (Node.to_tptp folds only the first "
        "character to lower-case, so it cannot tell these two apart) — refusing to "
        "silently merge two distinct symbols into one; rename one of them before "
        "exporting this problem.")


@pytest.mark.parametrize("formula", [
    Iff(Atom("Foo", (A,)), Atom("foo", (A,))),
    Atom("=", [Function("Bar", (A,)), Function("bar", (A,))]),
    And(Atom("P", (Function("Bar", (A,)),)), Atom("P", (Constant("bar"),))),
    Iff(Atom("P", (Constant("gaseous"),)), Atom("P", (Constant("Gaseous"),))),
])
def test_writer_and_single_formula_refusals_come_from_one_implementation(formula):
    single = refusal(formula)
    with pytest.raises(NotImplementedError) as excinfo:
        generate_tptp_problem([formula], formula)
    written = str(excinfo.value)
    assert written.startswith("generate_tptp_problem: ") and single.startswith("Node.to_tptp: ")
    assert single.replace("Node.to_tptp: ", "", 1).replace("this formula", "this problem") == \
        written.replace("generate_tptp_problem: ", "", 1)


def test_the_writers_still_render_premise_by_premise_after_their_own_check(scans):
    premises = [Quantifier("∀", X, Implies(Atom("Human", (X,)), Atom("Mortal", (X,)))),
                Atom("Human", (Constant("socrates"),))]
    conclusion = Atom("Mortal", (Constant("socrates"),))
    text = generate_tptp_problem(premises, conclusion)
    assert text == (
        "fof(premise_1, axiom, (![X]: (human(X) => mortal(X)))).\n"
        "fof(premise_2, axiom, human(socrates)).\n"
        "fof(goal, conjecture, mortal(socrates)).\n")
    assert len(scans) == 3                          # one outermost call per rendered formula


def test_the_writers_cross_kind_rename_is_unchanged():
    premise = Quantifier("∀", X, Atom("Agent", (Function("agent", (X,)),)))
    text, name_map = generate_tptp_problem_with_mapping([premise], Quantifier("∃", X, Atom("Agent", (X,))))
    assert text == ("fof(premise_1, axiom, (![X]: agent(agent_term(X)))).\n"
                    "fof(goal, conjecture, (?[X]: agent(X))).\n")
    assert name_map.term == {"agent": "agent_term"}


def test_the_writer_check_reads_the_same_hook_as_the_guard():
    # whole-problem check sees SortedConstant and Measure exactly like the guard does
    with pytest.raises(NotImplementedError, match="'gaseous' and 'Gaseous'"):
        generate_tptp_problem([Atom("P", (SortedConstant("gaseous", "S"),))], Atom("P", (SortedConstant("Gaseous", "S"),)))
    with pytest.raises(NotImplementedError, match="'measure' and 'Measure'"):
        generate_tptp_problem([Atom("P", (Measure(A, B),))], Atom("P", (Function("Measure", (A,)),)))
    assert _tptp_problem._check_no_symbol_collisions([Atom("P", (A,)), Atom("Q", (A,))]) is None


# ---------------------------------------------------------------------------
# The MCP tool and the CLI render ONE formula, so both are guarded for free.
# ---------------------------------------------------------------------------

def test_mcp_render_turns_the_refusal_into_a_structured_error_that_says_what_to_do():
    # θ and theta are two constants (not valid: P(θ) <-> P(theta)) written one word.
    result = server.render("P(θ) ↔ P(theta)", to="tptp")
    assert "rendered" not in result and result.get("ok") is not True
    assert result["error"]["type"] == "NotImplementedError"
    message = result["error"]["message"]
    assert "'θ'" in message and "'theta'" in message
    assert "rename one of them" in message


def test_mcp_render_refuses_the_reported_gaseous_input_from_tptp_text():
    result = server.render("fof(a, axiom, p(gaseous) <=> p('Gaseous')).", to="tptp", dialect="tptp")
    assert result["error"]["type"] == "NotImplementedError"
    assert "'gaseous' and 'Gaseous'" in result["error"]["message"]


def test_mcp_render_of_a_clean_formula_is_unchanged():
    assert server.render("∀x (P(x) → Q(x))", to="tptp") == {
        "ok": True, "to": "tptp", "rendered": "(![X]: (p(X) => q(X)))"}
    # a cross-kind clash is rendered, not refused (D3)
    assert server.render("∀e Agent(agent(e))", to="tptp")["rendered"] == "(![E]: agent(agent(E)))"


def test_cli_render_helper_is_guarded():
    from unicode_logic_kit.__main__ import _render
    node = Iff(Atom("P", (Constant("θ"),)), Atom("P", (Constant("theta"),)))
    with pytest.raises(NotImplementedError, match="'θ' and 'theta'"):
        _render(node, "tptp")
    assert _render(Atom("P", (A,)), "tptp") == "p(a)"
