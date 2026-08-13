"""Tests for the shared TPTP problem generator (atp._tptp_problem) and its use
by the three external-prover backends.

Two things pinned here:

1. :func:`atp._tptp_problem.generate_tptp_problem` produces the exact same
   text the three backends' own (pre-refactor) hand-written generators did —
   the unification behind ``_generate_vampire_input`` /
   ``eprover_backend._generate_tptp_problem`` / ``_generate_twee_input`` must
   be a pure refactor, not a behaviour change.
2. The cross-formula symbol-collision guard: two distinct kit-level
   predicate (or function/constant) names that would fold to the SAME TPTP
   identifier (``Node.to_tptp`` folds only a name's first character —
   ``Foo``/``foo`` both fold to ``foo``) must be refused with
   ``NotImplementedError`` naming both, from every one of the three
   backends' generator functions, not merely the shared helper.

Reproduces the reported bug directly: the concrete example from the task —
``_generate_vampire_input([Atom('Foo',[a]), Not(Atom('FOO',[a]))],
Atom('foo',[a]))`` — used to silently produce the self-contradictory axiom
set ``{foo(A), ~foo(A)}`` (from two semantically independent predicates
merged into one TPTP symbol), which any prover proves anything from via ex
falso quodlibet. It must now raise instead.
"""

import pytest

from unicode_fol_kit.fol.nodes import Atom, Constant, Function, Implies, Not, Variable
from unicode_fol_kit.atp._tptp_problem import generate_tptp_problem
from unicode_fol_kit.atp.vampire_entailment import _generate_vampire_input
from unicode_fol_kit.atp.eprover_backend import _generate_tptp_problem as _eprover_generate
from unicode_fol_kit.atp.twee_entailment import _generate_twee_input

_A = Variable("a")


# ---------------------------------------------------------------------------
# Pure refactor: shared helper matches each backend's own wrapper exactly.
# ---------------------------------------------------------------------------

_PREMISES = [Atom("Human", [Constant("socrates")]),
             Atom("Loves", [Constant("alice"), Constant("bob")])]
_CONCLUSION = Atom("Mortal", [Constant("socrates")])


@pytest.mark.parametrize("wrapper", [_generate_vampire_input, _eprover_generate, _generate_twee_input])
def test_backend_wrapper_matches_shared_helper(wrapper):
    assert wrapper(_PREMISES, _CONCLUSION) == generate_tptp_problem(_PREMISES, _CONCLUSION)


def test_shared_helper_shape():
    text = generate_tptp_problem(_PREMISES, _CONCLUSION)
    lines = [ln for ln in text.splitlines() if ln.strip()]
    assert lines == [
        "fof(premise_1, axiom, human(socrates)).",
        "fof(premise_2, axiom, loves(alice,bob)).",
        "fof(goal, conjecture, mortal(socrates)).",
    ]


def test_shared_helper_no_premises():
    text = generate_tptp_problem([], _CONCLUSION)
    lines = [ln for ln in text.splitlines() if ln.strip()]
    assert lines == ["fof(goal, conjecture, mortal(socrates))."]


# ---------------------------------------------------------------------------
# Collision guard — the reported bug, reproduced and refused.
# ---------------------------------------------------------------------------

def test_reported_bug_is_now_refused():
    """The exact repro from the task: Atom('Foo',...) / Atom('FOO',...) /
    Atom('foo',...) would all fold to the TPTP symbol 'foo' under the old
    whole-string .lower() — silently building a self-contradictory,
    ex-falso-quodlibet axiom set. Must raise instead of emitting a problem.
    """
    with pytest.raises(NotImplementedError, match="Foo.*foo|foo.*Foo"):
        generate_tptp_problem([Atom("Foo", [_A]), Not(Atom("FOO", [_A]))], Atom("foo", [_A]))


def test_collision_error_names_both_symbols():
    with pytest.raises(NotImplementedError) as exc_info:
        generate_tptp_problem([Atom("Foo", [_A])], Atom("foo", [_A]))
    message = str(exc_info.value)
    assert "'Foo'" in message and "'foo'" in message  # both original kit names named


def test_no_false_positive_for_the_same_predicate_reused():
    """Using the SAME predicate name more than once (the ordinary case) must
    never be flagged — only two DIFFERENT original names colliding are."""
    text = generate_tptp_problem([Atom("Foo", [_A]), Atom("Foo", [_A])], Atom("Foo", [_A]))
    assert text.count("foo(A)") == 3


def test_no_collision_between_predicate_and_function_namespaces():
    """A predicate and a function/constant folding to the same identifier are
    NOT a collision — they occupy separate TPTP syntactic namespaces (formula
    position vs. term position), unlike two predicates or two functions."""
    # Atom "Foo" -> predicate 'foo'; Constant "foo" -> term 'foo'. Different
    # namespaces, so no collision, even though the rendered strings match.
    text = generate_tptp_problem([Atom("Foo", [Constant("foo")])], Atom("Foo", [Constant("foo")]))
    assert "foo(foo)" in text


@pytest.mark.parametrize("generate", [generate_tptp_problem, _generate_vampire_input,
                                      _eprover_generate, _generate_twee_input])
def test_collision_guard_covers_every_external_backend(generate):
    """The guard must fire identically through EVERY one of the three
    external-prover generator functions (they all delegate to the shared
    helper), not just generate_tptp_problem itself."""
    with pytest.raises(NotImplementedError):
        generate([Atom("Foo", [_A])], Atom("foo", [_A]))


def test_function_name_collision_is_refused():
    # 'Bar' and 'bar' differ ONLY in the case of the first letter, so both
    # still fold to 'bar' under the first-letter-only fold (unlike e.g.
    # 'Bar'/'BAR', which no longer collide now that the fold is fixed).
    left = Atom("=", [Function("Bar", [_A]), Constant("c")])
    right = Atom("=", [Function("bar", [_A]), Constant("c")])
    with pytest.raises(NotImplementedError, match="function"):
        generate_tptp_problem([left], right)


def test_constant_name_collision_is_refused():
    left = Atom("=", [Constant("Alice"), Constant("Alice")])
    right = Atom("=", [Constant("alice"), Constant("alice")])
    with pytest.raises(NotImplementedError):
        generate_tptp_problem([left], right)


def test_collision_across_premises_and_conclusion_together():
    """The guard must see premises AND the conclusion as one problem — a
    collision split across the two must still be caught."""
    premise = Atom("Foo", [_A])
    conclusion = Atom("foo", [_A])
    with pytest.raises(NotImplementedError):
        generate_tptp_problem([premise], conclusion)


def test_no_collision_when_predicates_genuinely_distinct():
    """Two predicates whose folded forms differ (first letters 'F' and 'B',
    say) must never be flagged — only an actual identifier collision is."""
    text = generate_tptp_problem([Atom("Foo", [_A])], Atom("Bar", [_A]))
    assert "foo(A)" in text and "bar(A)" in text


def test_equality_and_arithmetic_predicates_never_participate_in_collisions():
    """'=', '<', '>', etc. map to fixed TPTP tokens outside the name-folding
    path, so they can never collide with a folded predicate name — even one
    that happens to render identically to a dollar-word by coincidence is
    out of this guard's scope (a separate, much narrower concern)."""
    text = generate_tptp_problem(
        [Atom("=", [Constant("a"), Constant("a")])],
        Atom("<", [Constant("a"), Constant("b")]),
    )
    assert "(a = a)" in text
    assert "$less(a,b)" in text
