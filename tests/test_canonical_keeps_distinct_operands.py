"""Two operands of a commutative connective are merged only when they are the same
formula up to the names of their bound variables.

The operands of ∧ and ∨ are sorted by a key, and operands with one key are taken for
duplicates and reduced to one. The key has to hold everything that tells two operands
apart: the name of a constant, the value of a numeral, the sort of a sorted constant,
a nominal, an agent, a group of agents, the type of a second-order quantifier. Without
that, ``P(alice) ∧ P(bob)`` was reduced to ``P(alice)`` and matched ``P(alice)``.

Every expected value below is worked out by hand from that one rule, and every case is
also checked for idempotence (``canonicalize(canonicalize(f)) == canonicalize(f)``)
through the helper ``canon``.
"""

import itertools
import random

import pytest

from unicode_logic_kit.eval import canonical
from unicode_logic_kit.eval.canonical import canonicalize, exact_match
from unicode_logic_kit.eval.equivalence import equivalent
from unicode_logic_kit.eval.metric_hf import compute_fol_metrics
from unicode_logic_kit.eval.predicate_match import aligned_exact_match
from unicode_logic_kit.fol.msflparser import MSFLParser
from unicode_logic_kit.fol.nodes import (
    And, At, Atom, Believes, CommonKnowledge, Constant, Count, DistributedKnowledge,
    Down, EverybodyKnows, Function, Iff, Implies, Knows, Lambda, LambdaVar, Nominal, Not,
    Number, Or, PredicateTerm, Quantifier, SecondOrderQuantifier, Says,
    SortedConstant, StrongConjunction, StrongDisjunction, Variable, Wants,
    WeakConjunction, WeakDisjunction, Xor,
)

FOL = MSFLParser()
MODAL = MSFLParser(modal=True)

alice, bob, carol = Constant("alice"), Constant("bob"), Constant("carol")
x, y = Variable("x"), Variable("y")


def P(*args):
    """The unary or binary atom ``P`` over the given terms."""
    return Atom("P", list(args))


def canon(formula):
    """Canonical form of ``formula``, after checking that it is a fixed point."""
    result = canonicalize(formula)
    assert canonicalize(result) == result
    return result


def chain(node, cls):
    """The operands of a maximal chain of ``cls`` (a lone non-``cls`` node is one operand)."""
    if isinstance(node, cls):
        return chain(node.left, cls) + chain(node.right, cls)
    return [node]


# ---------------------------------------------------------------------------
# The cases measured on the release: one operand used to be dropped
# ---------------------------------------------------------------------------

_MEASURED = [
    ("P(alice)", "P(bob)"),
    ("P(1)", "P(2)"),
    ("R(alice, bob)", "R(bob, alice)"),
    ("P(f(alice))", "P(f(bob))"),
    ("P(x)", "P(y)"),
]


class TestMeasuredCases:
    @pytest.mark.parametrize("cls,glyph", [(And, "∧"), (Or, "∨")])
    @pytest.mark.parametrize("left,right", _MEASURED)
    def test_both_operands_are_kept(self, cls, glyph, left, right):
        a, b = FOL.parse(left), FOL.parse(right)
        c = canon(FOL.parse(f"{left} {glyph} {right}"))
        assert len(chain(c, cls)) == 2
        assert set(chain(c, cls)) == {a, b}
        assert c != canon(a)
        assert c != canon(b)

    @pytest.mark.parametrize("glyph", ["∧", "∨"])
    @pytest.mark.parametrize("left,right", _MEASURED)
    def test_order_of_the_operands_does_not_matter(self, glyph, left, right):
        # Before, the operand that came first won, so the two orders gave two forms.
        one = canon(FOL.parse(f"{left} {glyph} {right}"))
        other = canon(FOL.parse(f"{right} {glyph} {left}"))
        assert one == other

    @pytest.mark.parametrize("left,right", _MEASURED)
    def test_exact_match_does_not_equal_a_conjunction_to_one_conjunct(self, left, right):
        both = FOL.parse(f"{left} ∧ {right}")
        assert exact_match(both, FOL.parse(left)) is False
        assert exact_match(both, FOL.parse(right)) is False
        assert exact_match(FOL.parse(left), both) is False

    def test_the_conjunction_of_alice_and_bob_is_sorted_by_name(self):
        assert canon(FOL.parse("P(bob) ∧ P(alice)")) == And(P(alice), P(bob))
        assert canon(FOL.parse("P(alice) ∨ P(bob)")) == Or(P(alice), P(bob))

    def test_two_different_conjunctions_are_not_one_after_the_dropped_operand(self):
        # Both used to canonicalize to P(alice), so they matched each other.
        assert exact_match(FOL.parse("P(alice) ∧ P(bob)"),
                           FOL.parse("P(alice) ∧ P(carol)")) is False

    def test_the_operands_stay_apart_below_a_quantifier_and_a_negation(self):
        under_all = canon(FOL.parse("∀z (R(alice, z) ∧ R(bob, z))"))
        assert under_all == Quantifier(
            "∀", Variable("q0"),
            And(Atom("R", [alice, Variable("q0")]), Atom("R", [bob, Variable("q0")])))
        assert canon(Not(And(P(alice), P(bob)))) == Not(And(P(alice), P(bob)))
        assert (canon(Implies(Or(P(bob), P(alice)), P(carol)))
                == Implies(Or(P(alice), P(bob)), P(carol)))


# ---------------------------------------------------------------------------
# Every field that is no child node is part of the key
# ---------------------------------------------------------------------------

def _knowledge_pairs():
    phi = P(carol)
    pairs = {}
    for cls in (Knows, Believes, Says, Wants):
        pairs[f"{cls.__name__} agent"] = (cls(alice, phi), cls(bob, phi))
    for cls in (EverybodyKnows, CommonKnowledge, DistributedKnowledge):
        pairs[f"{cls.__name__} group"] = (cls((alice, bob), phi), cls((alice, carol), phi))
    return pairs


_DIFFER_IN_ONE_FIELD = {
    "constant name": (P(alice), P(bob)),
    "constant in second place": (Atom("R", [carol, alice]), Atom("R", [carol, bob])),
    "swapped arguments": (Atom("R", [alice, bob]), Atom("R", [bob, alice])),
    "numeral": (P(Number(1)), P(Number(2))),
    "fractional numeral": (P(Number(0.25)), P(Number(0.5))),
    "function argument": (P(Function("f", [alice])), P(Function("f", [bob]))),
    "function name": (P(Function("f", [alice])), P(Function("g", [alice]))),
    "constant inside two functions": (
        P(Function("f", [Function("g", [alice])])),
        P(Function("f", [Function("g", [bob])]))),
    "sorted constant name": (P(SortedConstant("alice", "Human")),
                             P(SortedConstant("bob", "Human"))),
    "sorted constant sort only": (P(SortedConstant("alice", "Human")),
                                  P(SortedConstant("alice", "Animal"))),
    "nominal": (Nominal("i"), Nominal("j")),
    "nominal under @": (At(Nominal("i"), P(carol)), At(Nominal("j"), P(carol))),
    "predicate term": (Atom("Q", [PredicateTerm("Red")]), Atom("Q", [PredicateTerm("Blue")])),
    "second-order quantifier type": (
        SecondOrderQuantifier("∀", "X", 1, Atom("X", [alice])),
        SecondOrderQuantifier("∃", "X", 1, Atom("X", [alice]))),
    "second-order bound name": (
        SecondOrderQuantifier("∀", "X", 1, Atom("X", [alice])),
        SecondOrderQuantifier("∀", "Y", 1, Atom("Y", [alice]))),
    "second-order arity": (
        SecondOrderQuantifier("∀", "X", 1, Atom("X", [alice])),
        SecondOrderQuantifier("∀", "X", 2, Atom("X", [alice]))),
    "hybrid binder body": (Down(Nominal("i"), P(alice)), Down(Nominal("i"), P(bob))),
    "constant against a variable of the same spelling": (P(Constant("x")), P(Variable("x"))),
    "variable against a lambda variable of the same spelling": (P(Variable("x")),
                                                               P(LambdaVar("x"))),
    **_knowledge_pairs(),
}


class TestEveryFieldCounts:
    @pytest.mark.parametrize("cls", [And, Or])
    @pytest.mark.parametrize("name", sorted(_DIFFER_IN_ONE_FIELD))
    def test_operands_that_differ_in_one_field_are_two_operands(self, cls, name):
        first, second = _DIFFER_IN_ONE_FIELD[name]
        c = canon(cls(first, second))
        assert set(chain(c, cls)) == {first, second}
        assert len(chain(c, cls)) == 2

    @pytest.mark.parametrize("cls", [And, Or])
    @pytest.mark.parametrize("name", sorted(_DIFFER_IN_ONE_FIELD))
    def test_the_order_of_such_operands_does_not_matter(self, cls, name):
        first, second = _DIFFER_IN_ONE_FIELD[name]
        assert canon(cls(first, second)) == canon(cls(second, first))

    @pytest.mark.parametrize("name", sorted(_DIFFER_IN_ONE_FIELD))
    def test_exact_match_tells_them_apart(self, name):
        first, second = _DIFFER_IN_ONE_FIELD[name]
        assert exact_match(first, second) is False
        assert exact_match(And(first, second), first) is False
        assert exact_match(Or(first, second), second) is False

    def test_operands_with_a_binder_that_differ_in_one_field_stay_two_operands(self):
        # The bound variable of each operand is renamed by the pass over the whole
        # group: the first binder met is q0, the second q1. The operands are sorted
        # by the field in which they differ: ∀ before ∃ (U+2200 < U+2203), the
        # bound 2 before the bound 3, "ge" before "le", alice before bob.
        q0, q1 = Variable("q0"), Variable("q1")
        cases = [
            (Quantifier("∀", x, P(x, alice)), Quantifier("∃", x, P(x, alice)),
             Quantifier("∀", q0, P(q0, alice)), Quantifier("∃", q1, P(q1, alice))),
            (Quantifier("∀", x, P(x, alice)), Quantifier("∀", x, P(x, bob)),
             Quantifier("∀", q0, P(q0, alice)), Quantifier("∀", q1, P(q1, bob))),
            (Count("ge", Number(2), x, P(x, alice)), Count("ge", Number(3), x, P(x, alice)),
             Count("ge", Number(2), q0, P(q0, alice)), Count("ge", Number(3), q1, P(q1, alice))),
            (Count("ge", Number(2), x, P(x, alice)), Count("le", Number(2), x, P(x, alice)),
             Count("ge", Number(2), q0, P(q0, alice)), Count("le", Number(2), q1, P(q1, alice))),
        ]
        for first, second, want_first, want_second in cases:
            for cls in (And, Or):
                assert canon(cls(first, second)) == cls(want_first, want_second)
                assert canon(cls(second, first)) == cls(want_first, want_second)
            assert exact_match(first, second) is False

    def test_a_three_operand_chain_keeps_all_three(self):
        f = And(And(P(carol), P(alice)), P(bob))
        assert canon(f) == And(And(P(alice), P(bob)), P(carol))

    def test_the_fuzzy_idempotent_connectives_keep_distinct_operands_too(self):
        for cls in (WeakConjunction, WeakDisjunction):
            assert canon(cls(P(bob), P(alice))) == cls(P(alice), P(bob))


class TestTwoNameSpaces:
    """A logical variable and a lambda variable of one spelling are different things."""

    def test_a_quantifier_does_not_bind_the_lambda_variable_of_its_name(self):
        # In each conjunct the lambda variable refers to a parameter of the enclosing
        # lambdas, not to the quantifier: λx λy (∀x P(x̂) ∧ ∀y P(ŷ)) with x̂, ŷ lambda
        # variables. The two conjuncts refer to different parameters.
        lx, ly = LambdaVar("x"), LambdaVar("y")
        f = Lambda(lx, Lambda(ly, And(Quantifier("∀", x, P(lx)),
                                      Quantifier("∀", y, P(ly)))))
        q0, q1, q2, q3 = LambdaVar("q0"), LambdaVar("q1"), Variable("q2"), Variable("q3")
        assert canon(f) == Lambda(q0, Lambda(q1, And(Quantifier("∀", q2, P(q0)),
                                                     Quantifier("∀", q3, P(q1)))))

    def test_a_lambda_parameter_does_not_bind_the_variable_of_its_name(self):
        # Under λx the variable x is free: P(x) with x a variable and P(x̂) with x̂ the
        # parameter are two operands.
        lx = LambdaVar("x")
        f = Lambda(lx, And(P(x), P(lx)))
        c = canon(f)
        assert set(chain(c.body, And)) == {P(x), P(LambdaVar("q0"))}


# ---------------------------------------------------------------------------
# Agents: a quantified variable by position, a constant by name
# ---------------------------------------------------------------------------

class TestAgents:
    phi = P(carol)

    def test_agents_that_are_constants_are_told_apart_by_name(self):
        f = Quantifier("∀", x, And(Knows(alice, self.phi), Knows(bob, self.phi)))
        assert canon(f) == Quantifier(
            "∀", Variable("q0"), And(Knows(alice, self.phi), Knows(bob, self.phi)))

    def test_an_agent_bound_by_the_enclosing_quantifier_is_one_operand_when_repeated(self):
        f = Quantifier("∀", x, And(Knows(x, self.phi), Knows(x, self.phi)))
        assert canon(f) == Quantifier("∀", Variable("q0"), Knows(Variable("q0"), self.phi))

    def test_agents_bound_by_two_enclosing_quantifiers_are_two_operands(self):
        # The outer binder has the smaller level, so its operand comes first.
        expected = Quantifier("∀", Variable("q0"), Quantifier(
            "∀", Variable("q1"),
            And(Knows(Variable("q0"), self.phi), Knows(Variable("q1"), self.phi))))
        for outer, inner, left, right in [("x", "y", "x", "y"), ("x", "y", "y", "x"),
                                          ("a", "b", "b", "a")]:
            f = Quantifier("∀", Variable(outer), Quantifier(
                "∀", Variable(inner),
                And(Knows(Variable(left), self.phi), Knows(Variable(right), self.phi))))
            assert canon(f) == expected

    def test_a_variable_agent_is_not_a_constant_agent_of_the_same_spelling(self):
        f = Quantifier("∀", x, And(Knows(x, self.phi), Knows(Constant("x"), self.phi)))
        c = canon(f)
        assert c == Quantifier("∀", Variable("q0"), And(
            Knows(Constant("x"), self.phi), Knows(Variable("q0"), self.phi)))

    def test_a_free_agent_variable_is_told_apart_by_its_name(self):
        f = And(Knows(x, self.phi), Knows(y, self.phi))
        assert len(chain(canon(f), And)) == 2

    def test_a_group_member_bound_by_the_enclosing_quantifier_is_encoded_by_position(self):
        f = Quantifier("∀", x, And(EverybodyKnows((x, alice), self.phi),
                                   EverybodyKnows((x, bob), self.phi)))
        c = canon(f)
        assert len(chain(c.formula, And)) == 2
        renamed = Quantifier("∀", y, And(EverybodyKnows((y, bob), self.phi),
                                         EverybodyKnows((y, alice), self.phi)))
        assert canon(renamed) == c

    def test_a_string_agent_is_the_constant_of_that_name(self):
        assert Knows("alice", self.phi) == Knows(alice, self.phi)
        assert canon(And(Knows("alice", self.phi), Knows(alice, self.phi))) == Knows(
            alice, self.phi)
        assert len(chain(canon(And(Knows("alice", self.phi), Knows("bob", self.phi))),
                         And)) == 2

    def test_parsed_modal_formulas(self):
        both = MODAL.parse("K_alice P(carol) ∧ K_bob P(carol)")
        assert len(chain(canon(both), And)) == 2
        assert exact_match(both, MODAL.parse("K_alice P(carol)")) is False
        assert exact_match(both, MODAL.parse("K_bob P(carol) ∧ K_alice P(carol)")) is True
        named = MODAL.parse("@i P(carol) ∧ @j P(carol)")
        assert len(chain(canon(named), And)) == 2


# ---------------------------------------------------------------------------
# What must still merge: the same formula up to the names of bound variables
# ---------------------------------------------------------------------------

class TestWhatStillMerges:
    def test_the_same_atom_twice_is_one(self):
        assert canon(And(P(alice), P(alice))) == P(alice)
        assert canon(Or(P(alice), P(alice))) == P(alice)

    def test_two_conjuncts_that_differ_only_in_a_bound_name_are_one(self):
        f = And(Quantifier("∀", x, P(x)), Quantifier("∀", y, P(y)))
        assert canon(f) == Quantifier("∀", Variable("q0"), P(Variable("q0")))

    def test_the_same_constant_beside_a_bound_name_is_still_one(self):
        f = And(Quantifier("∀", x, P(x, alice)), Quantifier("∀", y, P(y, alice)))
        assert canon(f) == Quantifier("∀", Variable("q0"), P(Variable("q0"), alice))
        g = And(Quantifier("∀", x, P(x, alice)), Quantifier("∀", y, P(y, bob)))
        assert len(chain(canon(g), And)) == 2

    def test_a_double_negation_is_removed_before_the_comparison(self):
        assert canon(And(Not(Not(P(alice))), P(alice))) == P(alice)
        assert canon(Or(P(alice), Not(Not(P(alice))))) == P(alice)

    def test_one_numeral_has_one_value(self):
        # Number(1.0) is stored as Number(1): one numeral, so one operand.
        assert Number(1.0) == Number(1)
        assert canon(And(P(Number(1)), P(Number(1.0)))) == P(Number(1))
        assert canon(And(P(Number(0.5)), P(Number(0.5)))) == P(Number(0.5))

    def test_a_sorted_constant_twice_is_one(self):
        f = Or(P(SortedConstant("alice", "Human")), P(SortedConstant("alice", "Human")))
        assert canon(f) == P(SortedConstant("alice", "Human"))

    def test_a_second_order_quantifier_twice_is_one(self):
        q = SecondOrderQuantifier("∀", "X", 1, Atom("X", [alice]))
        assert canon(And(q, q)) == q

    def test_parsed_text_that_differs_in_order_and_names_still_matches(self):
        assert exact_match(FOL.parse("(∃y Q(y, bob)) ∧ (∀x P(x, alice))"),
                           FOL.parse("(∀a P(a, alice)) ∧ (∃b Q(b, bob))")) is True
        assert exact_match(FOL.parse("P(bob) ∧ P(alice) ∧ P(bob)"),
                           FOL.parse("P(alice) ∧ P(bob)")) is True


# ---------------------------------------------------------------------------
# Binders the key does not rename: kept apart (a missed match, never a wrong one)
# ---------------------------------------------------------------------------

class TestBindersKeyedByName:
    def test_second_order_binders_with_other_names_are_two_operands(self):
        forall_x = SecondOrderQuantifier("∀", "X", 1, Atom("X", [alice]))
        forall_y = SecondOrderQuantifier("∀", "Y", 1, Atom("Y", [alice]))
        assert len(chain(canon(And(forall_x, forall_y)), And)) == 2
        assert exact_match(forall_x, forall_y) is False

    def test_hybrid_binders_with_other_names_are_two_operands(self):
        down_x = Down(Nominal("x"), P(alice))
        down_y = Down(Nominal("y"), P(alice))
        assert len(chain(canon(Or(down_x, down_y)), Or)) == 2
        assert canon(Or(down_x, down_x)) == down_x

    def test_the_bound_quantifier_variable_is_still_renamed(self):
        assert exact_match(Quantifier("∀", x, P(x)), Quantifier("∀", y, P(y))) is True


# ---------------------------------------------------------------------------
# The connectives that are not idempotent keep repeated operands
# ---------------------------------------------------------------------------

class TestNonIdempotentConnectives:
    @pytest.mark.parametrize("cls", [Xor, Iff, StrongConjunction, StrongDisjunction])
    def test_a_repeated_operand_is_kept(self, cls):
        # P ⊕ P is false, P ↔ P is true, x ⊗ x = max(0, 2x - 1): none of them is P.
        f = cls(P(alice), P(alice))
        assert canon(f) == cls(P(alice), P(alice))
        assert canon(f) != canon(P(alice))

    @pytest.mark.parametrize("cls", [Xor, Iff, StrongConjunction, StrongDisjunction])
    def test_distinct_operands_are_sorted_whatever_their_order(self, cls):
        assert canon(cls(P(bob), P(alice))) == cls(P(alice), P(bob))
        assert canon(cls(P(alice), P(bob))) == cls(P(alice), P(bob))

    @pytest.mark.parametrize("cls", [Xor, Iff, StrongConjunction, StrongDisjunction])
    def test_a_repeated_operand_among_others_keeps_its_count(self, cls):
        f = cls(cls(P(bob), P(alice)), P(bob))
        assert chain(canon(f), cls) == [P(alice), P(bob), P(bob)]


# ---------------------------------------------------------------------------
# P1 on ground formulas, by truth table
# ---------------------------------------------------------------------------

_GROUND_ATOMS = [
    P(alice), P(bob), Atom("Q", [alice]), Atom("Q", [bob]),
    Atom("R", [alice, bob]), Atom("R", [bob, alice]),
]


def _ground_formula(rng, depth):
    """A random formula over the six ground atoms with ∧ ∨ ¬ →."""
    if depth <= 0 or rng.random() < 0.2:
        return rng.choice(_GROUND_ATOMS)
    r = rng.random()
    if r < 0.15:
        return Not(_ground_formula(rng, depth - 1))
    cls = rng.choice([And, And, Or, Or, Implies])
    return cls(_ground_formula(rng, depth - 1), _ground_formula(rng, depth - 1))


def _wide_chain(rng):
    """A chain of 3 to 5 ground atoms under one connective: many operands that differ
    only in their constants."""
    cls = rng.choice([And, Or])
    atoms = [rng.choice(_GROUND_ATOMS) for _ in range(rng.randint(3, 5))]
    result = atoms[0]
    for atom in atoms[1:]:
        result = cls(result, atom)
    return result


def _letter(atom):
    return (atom.predicate, tuple(arg.name for arg in atom.args))


def _truth(node, assignment):
    """Value of a ground formula under an assignment of one truth value per distinct atom."""
    if isinstance(node, Atom):
        return assignment[_letter(node)]
    if isinstance(node, Not):
        return not _truth(node.formula, assignment)
    if isinstance(node, And):
        return _truth(node.left, assignment) and _truth(node.right, assignment)
    if isinstance(node, Or):
        return _truth(node.left, assignment) or _truth(node.right, assignment)
    if isinstance(node, Implies):
        return (not _truth(node.left, assignment)) or _truth(node.right, assignment)
    raise AssertionError(f"not a ground propositional formula: {node!r}")


def _letters(node):
    return {_letter(atom) for atom in node.atoms()}


def _same_truth_table(f, g):
    letters = sorted(_letters(f) | _letters(g))
    for values in itertools.product([False, True], repeat=len(letters)):
        assignment = dict(zip(letters, values))
        if _truth(f, assignment) != _truth(g, assignment):
            return False
    return True


def _sample(seed=20261007, count=300):
    rng = random.Random(seed)
    formulas = [_ground_formula(rng, 4) for _ in range(count)]
    formulas += [_wide_chain(rng) for _ in range(count // 3)]
    return formulas


def _shuffled(node, rng):
    """Commute and reassociate every ∧ and ∨ group at random (meaning-preserving)."""
    if isinstance(node, (And, Or)):
        cls = type(node)
        operands = [_shuffled(op, rng) for op in chain(node, cls)]
        rng.shuffle(operands)
        result = operands[0]
        for operand in operands[1:]:
            result = cls(result, operand)
        return result
    return node.map_children(lambda child: _shuffled(child, rng))


def _counterexamples():
    """The sample formulas whose canonical form is not equivalent to them."""
    return [f for f in _sample() if not _same_truth_table(f, canonicalize(f))]


class TestTruthTableEquivalence:
    def test_the_canonical_form_of_a_ground_formula_is_equivalent_to_it(self):
        sample = _sample()
        assert len(sample) >= 400
        assert _counterexamples() == []

    def test_the_canonical_form_is_a_fixed_point_and_ignores_the_operand_order(self):
        rng = random.Random(77)
        for f in _sample():
            c = canon(f)
            assert canonicalize(_shuffled(f, rng)) == c

    def test_the_canonical_form_reads_back_as_itself(self):
        for f in _sample(seed=5, count=60):
            c = canonicalize(f)
            assert FOL.parse(c.to_unicode_str()) == c

    def test_the_truth_table_check_itself_tells_a_wrong_form_from_a_right_one(self):
        assert _same_truth_table(And(P(alice), P(bob)), And(P(bob), P(alice)))
        assert not _same_truth_table(And(P(alice), P(bob)), P(alice))
        assert not _same_truth_table(Or(P(alice), P(bob)), P(bob))
        assert _same_truth_table(Implies(P(alice), P(bob)), Or(Not(P(alice)), P(bob)))

    def test_control_the_old_key_fails_the_same_check(self, monkeypatch):
        # The old key recorded only the class of a constant, never its name: the
        # detail of a node (its fields that are no child) is left out here.
        monkeypatch.setattr(canonical, "_loose_fields", lambda node, skip=(): [])
        assert canonicalize(And(P(alice), P(bob))) == P(alice)
        assert exact_match(And(P(alice), P(bob)), P(alice)) is True
        assert canonicalize(And(P(alice), P(bob))) != canonicalize(And(P(bob), P(alice)))
        assert exact_match(FOL.parse("P(alice) ∧ P(bob)"),
                           FOL.parse("P(alice) ∧ P(carol)")) is True
        assert len(_counterexamples()) > 0


# ---------------------------------------------------------------------------
# The entry points that used the wrong "equal"
# ---------------------------------------------------------------------------

class TestEntryPoints:
    both = FOL.parse("P(alice) ∧ P(bob)")
    one = FOL.parse("P(alice)")

    def test_exact_match(self):
        assert exact_match(self.both, self.one) is False
        assert exact_match(self.one, self.both) is False
        assert exact_match(self.both, FOL.parse("P(bob) ∧ P(alice)")) is True

    def test_aligned_exact_match(self):
        # The only reference constant, alice, is taken by the identical constant of the
        # prediction, so bob has nothing to be aligned to and the conjunct stays.
        assert aligned_exact_match(self.both, self.one) is False
        assert aligned_exact_match(self.one, self.both) is False
        assert aligned_exact_match(self.both, FOL.parse("P(alice) ∧ P(carol)")) is False

    def test_aligned_exact_match_still_aligns_a_misspelt_constant(self):
        assert aligned_exact_match(FOL.parse("P(alise) ∧ P(bob)"),
                                   FOL.parse("P(bob) ∧ P(alice)")) is True

    def test_equivalent_with_the_canonical_level(self):
        result = equivalent(self.both, self.one, method="canonical")
        assert result.equivalent is None
        assert result.structurally_equal is False

    def test_equivalent_with_the_predicate_align_level(self):
        result = equivalent(self.both, self.one, method="predicate_align")
        assert result.equivalent is None
        assert result.aligned_equal is False

    def test_equivalent_auto_reaches_the_solver_and_refutes(self):
        # P(alice) ∧ P(bob) is false where P(bob) is false and P(alice) is true.
        result = equivalent(self.both, self.one, method="auto")
        assert result.equivalent is False
        assert result.method_used == "solver"
        assert result.structurally_equal is False
        assert result.aligned_equal is False
        assert result.counterexample is not None

    def test_the_partial_credit_of_a_refuted_pair(self):
        # s1: both formulas are closed and well-formed. s2: the constant bob is no
        # constant of the reference. s3: not aligned-equal. s4: not equivalent.
        for method in ("auto", "solver"):
            result = equivalent(self.both, self.one, method=method)
            assert result.partial_credit == 0.25
            assert result.partial_credit_components == {
                "s1": True, "s2": False, "s3": False, "s4": False}

    def test_equivalent_still_finds_the_right_equal_pairs(self):
        flipped = equivalent(self.both, FOL.parse("P(bob) ∧ P(alice)"), method="auto")
        assert (flipped.equivalent, flipped.method_used) == (True, "canonical")
        repeated = equivalent(FOL.parse("P(alice) ∧ P(alice)"), self.one, method="auto")
        assert (repeated.equivalent, repeated.method_used) == (True, "canonical")

    def test_the_metrics_of_a_refuted_pair(self):
        metrics = compute_fol_metrics(["P(alice) ∧ P(bob)"], ["P(alice)"])
        assert metrics["equivalence_accuracy"] == 0.0
        assert metrics["mean_partial_credit"] == 0.25
        assert metrics["exact_match"] == 0.0
