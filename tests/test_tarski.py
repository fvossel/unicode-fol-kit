"""Tests for classical Tarskian model theory (unicode_fol_kit.semantics.tarski).

Each test fixes a concrete world (domain + symbol interpretations) and asserts
hand-checked truth values, exercising both the True and False branches.
"""

import pytest

from unicode_fol_kit.fol.msflparser import MSFLParser
from unicode_fol_kit.fol.nodes import (
    Variable, Constant, Number, Function,
    Atom, Not, And, Or, Implies, Quantifier,
    SortedQuantifier, SortedConstant, Lambda, LambdaVar,
    WeakConjunction,
)
from unicode_fol_kit.semantics.tarski import (
    Structure, term_value, satisfies, models,
)

FOL = MSFLParser()
MSFOL = MSFLParser(many_sorted=True)


# ---------------------------------------------------------------------------
# Loves world: domain {alice, bob}, Loves = {(alice,bob), (bob,alice)}
# ---------------------------------------------------------------------------

LOVES_WORLD = Structure(
    domain={"alice", "bob"},
    predicates={("Loves", 2): {("alice", "bob"), ("bob", "alice")}},
)


class TestLovesWorld:
    def test_everyone_loves_someone(self):
        # ∀x∃y Loves(x,y): alice loves bob, bob loves alice → True.
        assert models(FOL.parse("∀x ∃y Loves(x, y)"), LOVES_WORLD) is True

    def test_nobody_loves_themselves(self):
        # ∃x Loves(x,x): no reflexive pair in the relation → False.
        assert models(FOL.parse("∃x Loves(x, x)"), LOVES_WORLD) is False

    def test_loves_is_symmetric(self):
        # ∀x∀y (Loves(x,y) → Loves(y,x)): the relation is symmetric → True.
        f = FOL.parse("∀x ∀y (Loves(x, y) → Loves(y, x))")
        assert models(f, LOVES_WORLD) is True

    def test_not_everyone_loves_everyone(self):
        # Clearly FALSE sentence: alice does not love alice.
        assert models(FOL.parse("∀x ∀y Loves(x, y)"), LOVES_WORLD) is False

    def test_free_variable_assignment(self):
        # Loves(x,y) with x:=alice, y:=bob is True; with x:=alice, y:=alice False.
        f = FOL.parse("Loves(x, y)")
        assert satisfies(f, LOVES_WORLD, {"x": "alice", "y": "bob"}) is True
        assert satisfies(f, LOVES_WORLD, {"x": "alice", "y": "alice"}) is False


# ---------------------------------------------------------------------------
# Equality world: domain {0, 1}
# ---------------------------------------------------------------------------

EQ_WORLD = Structure(domain={0, 1})


class TestEquality:
    def test_reflexivity(self):
        # ∀x (x = x) → True.
        assert models(FOL.parse("∀x (x = x)"), EQ_WORLD) is True

    def test_distinct_individuals_exist(self):
        # ∃x∃y (x ≠ y): 0 ≠ 1 → True.
        assert models(FOL.parse("∃x ∃y (x ≠ y)"), EQ_WORLD) is True

    def test_not_all_equal(self):
        # ∀x∀y (x = y): 0 ≠ 1 makes this False.
        assert models(FOL.parse("∀x ∀y (x = y)"), EQ_WORLD) is False

    def test_singleton_domain_all_equal(self):
        # On a one-element domain, ∀x∀y (x = y) is True (contrasts the above).
        one = Structure(domain={42})
        assert models(FOL.parse("∀x ∀y (x = y)"), one) is True


# ---------------------------------------------------------------------------
# Function world: domain {0,1}; succ: 0->1, 1->0; zero->0; P = {(1,)}
# ---------------------------------------------------------------------------

def _succ(x):
    return 1 - x


FUNC_WORLD = Structure(
    domain={0, 1},
    constants={"zero": 0},
    functions={("succ", 1): _succ},
    predicates={("P", 1): {(1,)}},
)


class TestFunctions:
    def test_p_of_succ_zero(self):
        # P(succ(zero)) = P(succ(0)) = P(1) → True.
        f = Atom("P", [Function("succ", [Constant("zero")])])
        assert models(f, FUNC_WORLD) is True

    def test_p_of_zero(self):
        # P(zero) = P(0) → 0 not in {1} → False.
        f = Atom("P", [Constant("zero")])
        assert models(f, FUNC_WORLD) is False

    def test_term_value_succ(self):
        # term_value of succ(zero) is the individual 1.
        t = Function("succ", [Constant("zero")])
        assert term_value(t, FUNC_WORLD, {}) == 1

    def test_dict_function_interpretation(self):
        # A function given as {arg_tuple: value} dict instead of a callable.
        world = Structure(
            domain={0, 1},
            functions={("f", 1): {(0,): 1, (1,): 0}},
        )
        assert term_value(Function("f", [Number(0)]), world, {}) == 1
        assert term_value(Function("f", [Number(1)]), world, {}) == 0


# ---------------------------------------------------------------------------
# Number default: Number(n) -> n unless overridden by constants[str(n)]
# ---------------------------------------------------------------------------

class TestNumbers:
    def test_number_defaults_to_itself(self):
        world = Structure(domain={0, 1}, predicates={("P", 1): {(1,)}})
        assert models(Atom("P", [Number(1)]), world) is True
        assert models(Atom("P", [Number(0)]), world) is False

    def test_number_override_via_constants(self):
        # constants["1"] = 0 redirects Number(1) to the individual 0.
        world = Structure(
            domain={0, 1},
            constants={"1": 0},
            predicates={("P", 1): {(1,)}},
        )
        assert models(Atom("P", [Number(1)]), world) is False


# ---------------------------------------------------------------------------
# Nullary predicates (propositional atoms)
# ---------------------------------------------------------------------------

class TestNullaryPredicates:
    def test_true_proposition(self):
        world = Structure(domain={0}, predicates={("Rains", 0): True})
        assert models(FOL.parse("Rains"), world) is True

    def test_false_or_missing_proposition(self):
        world = Structure(domain={0}, predicates={("Rains", 0): False})
        assert models(FOL.parse("Rains"), world) is False
        # A predicate with no extension at all is also false.
        empty = Structure(domain={0})
        assert models(FOL.parse("Rains"), empty) is False

    def test_connectives_on_propositions(self):
        world = Structure(
            domain={0},
            predicates={("P", 0): True, ("Q", 0): False},
        )
        assert models(FOL.parse("P ∧ ¬Q"), world) is True
        assert models(FOL.parse("P ∧ Q"), world) is False
        assert models(FOL.parse("P ∨ Q"), world) is True
        assert models(FOL.parse("Q → P"), world) is True
        assert models(FOL.parse("P → Q"), world) is False
        assert models(FOL.parse("P ⊕ Q"), world) is True  # Xor: True/False


# ---------------------------------------------------------------------------
# MSFOL sorts: domain {alice, rex}; Human={alice}, Dog={rex}; Barks={(rex,)}
# ---------------------------------------------------------------------------

SORT_WORLD = Structure(
    domain={"alice", "rex"},
    constants={"alice": "alice", "rex": "rex"},
    predicates={("Barks", 1): {("rex",)}},
    sorts={"Human": {"alice"}, "Dog": {"rex"}},
)


class TestSorts:
    def test_all_dogs_bark(self):
        # ∀x:Dog Barks(x): the only dog is rex, who barks → True.
        f = SortedQuantifier("∀", Variable("x"), "Dog", Atom("Barks", [Variable("x")]))
        assert models(f, SORT_WORLD) is True

    def test_no_human_barks(self):
        # ∀x:Human Barks(x): the only human is alice, who does not bark → False.
        f = SortedQuantifier("∀", Variable("x"), "Human", Atom("Barks", [Variable("x")]))
        assert models(f, SORT_WORLD) is False

    def test_some_human_is_self_identical(self):
        # ∃x:Human (x = x): alice exists → True.
        f = SortedQuantifier(
            "∃", Variable("x"), "Human",
            Atom("=", [Variable("x"), Variable("x")]),
        )
        assert models(f, SORT_WORLD) is True

    def test_sorted_constant_works(self):
        # SortedConstant alice:Human evaluates via constants["alice"]; Barks false.
        sc = SortedConstant("alice", "Human")
        assert term_value(sc, SORT_WORLD, {}) == "alice"
        assert models(Atom("Barks", [sc]), SORT_WORLD) is False
        # rex:Dog does bark.
        assert models(Atom("Barks", [SortedConstant("rex", "Dog")]), SORT_WORLD) is True

    def test_exists_dog_barks(self):
        f = SortedQuantifier("∃", Variable("x"), "Dog", Atom("Barks", [Variable("x")]))
        assert models(f, SORT_WORLD) is True

    def test_parsed_sorted_quantifier(self):
        # Round-trip through the MSFOL parser for the same two sentences.
        assert models(MSFOL.parse("∀x:Dog Barks(x)"), SORT_WORLD) is True
        assert models(MSFOL.parse("∀x:Human Barks(x)"), SORT_WORLD) is False

    def test_undeclared_sort_raises(self):
        f = SortedQuantifier("∀", Variable("x"), "Alien", Atom("Barks", [Variable("x")]))
        with pytest.raises(KeyError):
            models(f, SORT_WORLD)


# ---------------------------------------------------------------------------
# Quantifier type-string variants ("forall"/"exists")
# ---------------------------------------------------------------------------

class TestQuantifierTypeSpellings:
    def test_word_forall(self):
        f = Quantifier("forall", Variable("x"), Atom("=", [Variable("x"), Variable("x")]))
        assert models(f, EQ_WORLD) is True

    def test_word_exists(self):
        f = Quantifier(
            "exists", Variable("x"),
            Atom("≠", [Variable("x"), Constant("c")]),
        )
        world = Structure(domain={0, 1}, constants={"c": 0})
        # ∃x (x ≠ c) with c=0: x=1 works → True.
        assert models(f, world) is True


# ---------------------------------------------------------------------------
# Order comparisons via predicate extensions
# ---------------------------------------------------------------------------

class TestOrderComparisons:
    def test_less_than_extension(self):
        # Domain {0,1,2}; supply the < relation explicitly as an extension.
        world = Structure(
            domain={0, 1, 2},
            predicates={("<", 2): {(0, 1), (0, 2), (1, 2)}},
        )
        assert satisfies(FOL.parse("x < y"), world, {"x": 0, "y": 1}) is True
        assert satisfies(FOL.parse("x < y"), world, {"x": 1, "y": 0}) is False
        # ∃x∃y (x < y) → True; ∀x∀y (x < y) → False (e.g. 1<1 absent).
        assert models(FOL.parse("∃x ∃y (x < y)"), world) is True
        assert models(FOL.parse("∀x ∀y (x < y)"), world) is False


# ---------------------------------------------------------------------------
# Counting quantifiers, cardinality terms, and measure terms
# ---------------------------------------------------------------------------

class TestCountingAndCardinality:
    # Domain {0,1,2} with P = {0,1}: exactly two P's, one non-P.
    WORLD = Structure(domain=[0, 1, 2], predicates={("P", 1): {(0,), (1,)}})

    @pytest.mark.parametrize("src,expected", [
        ("∃=2 x (P(x))", True), ("∃=3 x (P(x))", False),
        ("∃≥2 x (P(x))", True), ("∃≥3 x (P(x))", False),
        ("∃≤2 x (P(x))", True), ("∃≤1 x (P(x))", False),
        ("∃=0 x (Q(x))", True),               # an uninterpreted predicate is empty
        ("∃≥1 x (Q(x))", False),
    ])
    def test_counting_quantifier(self, src, expected):
        assert models(FOL.parse(src), self.WORLD) is expected

    @pytest.mark.parametrize("src,expected", [
        ("|{x : P(x)}| = 2", True), ("|{x : P(x)}| = 3", False),
        ("|{x : ¬P(x)}| = 1", True),          # the complement within the domain
        ("|{x : Q(x)}| = 0", True),           # empty extension counts to zero
    ])
    def test_cardinality_term(self, src, expected):
        assert models(FOL.parse(src), self.WORLD) is expected

    @pytest.mark.parametrize("src,expected", [
        ("|{x : P(x)}| > |{x : ¬P(x)}|", True),      # 2 > 1
        ("|{x : ¬P(x)}| > |{x : P(x)}|", False),
        ("|{x : Q(x)}| < |{x : P(x)}|", True),       # 0 < 2
        ("|{x : P(x)}| ≥ 2", True), ("|{x : P(x)}| < 2", False),
        ("|{x : P(x)}| ≤ |{x : P(x)}|", True),
    ])
    def test_cardinality_comparison_is_numeric(self, src, expected):
        # A cardinality is a NUMBER, not a domain individual, so < > ≤ ≥ compare the
        # counts. Without this the atom would fall through to the (empty) extension
        # lookup and every such comparison would silently be False.
        assert models(FOL.parse(src), self.WORLD) is expected

    def test_order_comparison_on_plain_terms_still_uses_the_extension(self):
        # A DECLARED extension is the interpretation of the order symbol, and it wins
        # over any numeric reading — a structure may interpret < over its domain
        # however it likes, which is also what the first-order exports assume.
        world = Structure(domain={0, 1, 2}, predicates={("<", 2): {(0, 1)}})
        assert satisfies(FOL.parse("x < y"), world, {"x": 0, "y": 1}) is True
        assert satisfies(FOL.parse("x < y"), world, {"x": 1, "y": 2}) is False  # absent

    def test_sorted_variants_range_over_their_sort(self):
        # Person = {0,1} but P holds of all three individuals: the sort must cut the
        # third one away, so both the sorted count and the sorted cardinality see 2.
        sorted_parser = MSFLParser(many_sorted=True)
        world = Structure(domain=[0, 1, 2], sorts={"Person": {0, 1}},
                          predicates={("P", 1): {(0,), (1,), (2,)}})
        assert models(sorted_parser.parse("∃=2 x:Person (P(x))"), world) is True
        assert models(sorted_parser.parse("∃=3 x:Person (P(x))"), world) is False
        assert models(sorted_parser.parse("|{v:Person : P(v)}| = 2"), world) is True

    def test_counting_binder_does_not_leak_its_variable(self):
        # The bound x is local: an outer x keeps its assignment across the count.
        world = Structure(domain=[0, 1, 2], predicates={("P", 1): {(0,), (1,)}})
        f = FOL.parse("P(x) ∧ ∃=2 x (P(x))")
        assert satisfies(f, world, {"x": 0}) is True     # outer x = 0 is a P
        assert satisfies(f, world, {"x": 2}) is False    # outer x = 2 is not

    def test_measure_is_the_binary_function_the_provers_see(self):
        # μ(entity, dimension) reads the function ``measure``/2 — the same symbol
        # Measure.to_z3 and Measure.to_prover9 emit.
        world = Structure(domain=[0, 1, 5], constants={"alice": 0, "height": 1},
                          functions={("measure", 2): {(0, 1): 5}})
        assert models(FOL.parse("μ(alice, height) = 5"), world) is True
        assert models(FOL.parse("μ(alice, height) = 1"), world) is False

    def test_measure_without_an_interpretation_raises(self):
        world = Structure(domain=[0, 1], constants={"alice": 0, "height": 1})
        with pytest.raises(ValueError, match="measure"):
            models(FOL.parse("μ(alice, height) = 1"), world)


# ---------------------------------------------------------------------------
# The three readings of an order comparison < > ≤ ≥
# ---------------------------------------------------------------------------

class TestOrderComparisonReadings:
    """Precedence: a cardinality operand forces numeric > a declared extension
    wins > numeric operands fall back to arithmetic > empty relation."""

    # rex measures 10 on height, fido 5. ``measure``/2 is the symbol the provers see.
    MEASURED = dict(
        domain=[5, 10, "rex", "fido", "height"],
        constants={"rex": "rex", "fido": "fido", "height": "height"},
        functions={("measure", 2): {("rex", "height"): 10, ("fido", "height"): 5}},
    )

    def test_measure_comparison_is_numeric_when_no_extension_is_declared(self):
        # μ is an uninterpreted function, so a structure is free to map it to
        # numbers without also axiomatising ≥ over them. Before the fallback such a
        # comparison fell through to the empty relation and was SILENTLY False —
        # the same failure mode the cardinality reading exists to prevent.
        world = Structure(predicates={}, **self.MEASURED)
        assert models(FOL.parse("μ(rex, height) ≥ μ(fido, height)"), world) is True
        assert models(FOL.parse("μ(fido, height) ≥ μ(rex, height)"), world) is False
        assert models(FOL.parse("μ(rex, height) > μ(fido, height)"), world) is True
        assert models(FOL.parse("μ(rex, height) ≤ μ(fido, height)"), world) is False

    def test_a_declared_extension_wins_over_the_numeric_reading(self):
        # The extension deliberately CONTRADICTS arithmetic (it holds of (5, 10) but
        # not of (10, 5)), so these assertions can only pass if the declared
        # interpretation takes precedence — the first-order reading is preserved.
        world = Structure(predicates={("≥", 2): {(5, 10)}}, **self.MEASURED)
        assert models(FOL.parse("μ(fido, height) ≥ μ(rex, height)"), world) is True
        assert models(FOL.parse("μ(rex, height) ≥ μ(fido, height)"), world) is False

    def test_a_declared_but_empty_extension_is_still_the_empty_relation(self):
        # This is the model finder's path: it declares EVERY scanned predicate, with
        # the empty set among the enumerated extensions. Declared-but-empty must
        # therefore stay false, or the fallback would silently rewrite the search
        # space and make enumerated structures disagree with the evaluator.
        world = Structure(predicates={("≥", 2): set()}, **self.MEASURED)
        assert models(FOL.parse("μ(rex, height) ≥ μ(fido, height)"), world) is False

    def test_non_numeric_operands_without_an_extension_stay_false(self):
        # Nothing to compare arithmetically and no interpretation given: the order
        # symbol is just an uninterpreted predicate, hence the empty relation. This
        # stays FALSE rather than raising — an absent extension is not an error.
        world = Structure(
            domain=["rex", "fido", "height", "tall"],
            constants={"rex": "rex", "fido": "fido", "height": "height"},
            functions={("measure", 2): {("rex", "height"): "tall",
                                        ("fido", "height"): "tall"}},
        )
        assert models(FOL.parse("μ(rex, height) ≥ μ(fido, height)"), world) is False

    def test_booleans_do_not_count_as_numbers(self):
        # bool is an int subclass in Python, but a truth value is not a position on
        # a scale: True ≥ False must NOT quietly succeed as 1 ≥ 0.
        world = Structure(
            domain=[True, False, "rex", "fido", "height"],
            constants={"rex": "rex", "fido": "fido", "height": "height"},
            functions={("measure", 2): {("rex", "height"): True,
                                        ("fido", "height"): False}},
        )
        assert models(FOL.parse("μ(rex, height) ≥ μ(fido, height)"), world) is False

    def test_a_cardinality_ignores_a_declared_extension(self):
        # The asymmetry with the measure case is deliberate: a cardinality IS a
        # number this evaluator computes, so no structure may reinterpret it. Here
        # the declared extension is empty and the comparison is still true.
        world = Structure(domain=[0, 1, 2],
                          predicates={("P", 1): {(0,), (1,)}, (">", 2): set()})
        assert models(FOL.parse("|{x : P(x)}| > |{x : ¬P(x)}|"), world) is True

    def test_the_suitability_rule_runs_without_a_hand_built_order(self):
        # End-to-end payoff: a threshold rule comparing what a breed brings against
        # what a service demands on the same dimension. Collie clears both services,
        # pug only the lapdog one — and no ≥ extension has to be spelled out.
        rule = MSFOL.parse(
            "∀x:Breed ∀y:Service ("
            "(μ(x, temperament:Attribute) ≥ μ(y, temperament:Attribute) "
            "∧ μ(x, physique:Attribute) ≥ μ(y, physique:Attribute)) "
            "→ Suitable(x, y))"
        )
        measure = {
            ("collie", "temperament"): 9, ("collie", "physique"): 8,
            ("pug", "temperament"): 4, ("pug", "physique"): 2,
            ("herding", "temperament"): 7, ("herding", "physique"): 6,
            ("lapdog", "temperament"): 2, ("lapdog", "physique"): 1,
        }
        base = dict(
            domain=["collie", "pug", "herding", "lapdog",
                    "temperament", "physique", 1, 2, 4, 6, 7, 8, 9],
            sorts={"Breed": ["collie", "pug"], "Service": ["herding", "lapdog"],
                   "Attribute": ["temperament", "physique"]},
            constants={"temperament": "temperament", "physique": "physique"},
            functions={("measure", 2): measure},
        )
        qualifying = {("collie", "herding"), ("collie", "lapdog"), ("pug", "lapdog")}
        assert models(rule, Structure(predicates={("Suitable", 2): qualifying},
                                      **base)) is True
        # Drop the one pair the thresholds force, and the rule fails.
        assert models(rule, Structure(
            predicates={("Suitable", 2): qualifying - {("collie", "herding")}},
            **base)) is False


# ---------------------------------------------------------------------------
# Error handling: fuzzy nodes and lambda nodes are rejected
# ---------------------------------------------------------------------------

class TestErrors:
    def test_fuzzy_node_rejected(self):
        f = WeakConjunction(Atom("P", []), Atom("Q", []))
        world = Structure(domain={0}, predicates={("P", 0): True, ("Q", 0): True})
        with pytest.raises(ValueError):
            satisfies(f, world)

    def test_lambda_node_rejected(self):
        f = Lambda(LambdaVar("x"), Atom("P", [LambdaVar("x")]))
        world = Structure(domain={0})
        with pytest.raises(ValueError):
            satisfies(f, world)

    def test_empty_domain_rejected(self):
        with pytest.raises(ValueError):
            Structure(domain=[])

    def test_unbound_variable_raises(self):
        with pytest.raises(KeyError):
            satisfies(FOL.parse("P(x)"),
                      Structure(domain={0}, predicates={("P", 1): {(0,)}}))

    def test_uninterpreted_constant_raises(self):
        with pytest.raises(KeyError):
            term_value(Constant("ghost"), Structure(domain={0}), {})

    def test_uninterpreted_function_raises(self):
        with pytest.raises(ValueError):
            term_value(Function("f", [Number(0)]), Structure(domain={0}), {})


# ---------------------------------------------------------------------------
# Functional style: the assignment dict is never mutated
# ---------------------------------------------------------------------------

class TestNoMutation:
    def test_assignment_not_mutated(self):
        assignment = {"z": "alice"}
        f = FOL.parse("∀x ∃y Loves(x, y)")
        satisfies(f, LOVES_WORLD, assignment)
        # The quantifiers bound x and y, but the caller's dict is untouched.
        assert assignment == {"z": "alice"}


# ---------------------------------------------------------------------------
# Reviewer-added edge cases (vacuous truth, shadowing, native-vs-extension =)
# ---------------------------------------------------------------------------

class TestReviewerEdgeCases:
    def test_empty_declared_sort_is_vacuous(self):
        # A *declared but empty* sort (distinct from an undeclared one, which
        # raises): ∀ ranges over nothing → vacuously True; ∃ → False.
        world = Structure(domain={0, 1}, sorts={"Nothing": set()})
        forall = SortedQuantifier(
            "∀", Variable("x"), "Nothing", Atom("P", [Variable("x")])
        )
        exists = SortedQuantifier(
            "∃", Variable("x"), "Nothing", Atom("P", [Variable("x")])
        )
        assert models(forall, world) is True
        assert models(exists, world) is False

    def test_inner_quantifier_shadows_outer(self):
        # ∀x (∃x P(x)): the inner ∃ rebinds x, so the body's value is the same
        # for every outer x. P = {(1,)} makes ∃x P(x) True → the whole is True.
        # This also pins down that binding a fresh COPY of the assignment lets
        # the inner binder override the outer one without corrupting it.
        world = Structure(domain={0, 1}, predicates={("P", 1): {(1,)}})
        f = Quantifier(
            "∀", Variable("x"),
            Quantifier("∃", Variable("x"), Atom("P", [Variable("x")])),
        )
        assert models(f, world) is True

    def test_equality_is_native_not_an_extension(self):
        # '=' is interpreted as identity even with NO ("=", 2) entry supplied,
        # and a bogus ("=", 2) extension must NOT override that native handling.
        world = Structure(
            domain={0, 1},
            predicates={("=", 2): {(0, 1)}},  # deliberately wrong extension
        )
        # 0 = 0 holds by identity despite (0,0) being absent from the extension.
        assert satisfies(
            Atom("=", [Variable("x"), Variable("y")]), world, {"x": 0, "y": 0}
        ) is True
        # 0 = 1 is False by identity despite (0,1) being IN the bogus extension.
        assert satisfies(
            Atom("=", [Variable("x"), Variable("y")]), world, {"x": 0, "y": 1}
        ) is False

    def test_float_number_matches_int_individual(self):
        # Number(1.0) evaluates to the literal 1.0, which equals the individual
        # 1 (1.0 == 1 in Python), so membership in P = {(1,)} holds.
        world = Structure(domain={0, 1}, predicates={("P", 1): {(1,)}})
        assert models(Atom("P", [Number(1.0)]), world) is True
