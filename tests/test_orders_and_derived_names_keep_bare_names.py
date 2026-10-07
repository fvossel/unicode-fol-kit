"""A quoted constant changes the text of a formula, not an order, a name or a table key.

The text of a formula writes a constant in quotes when its bare name would read as something
else: ``Constant("a")`` is ``'a'`` there (``P('a')``), because the bare letter reads back as a
variable. The routes below do not show that text to anybody. They sort terms by it, derive the
identifier of an Isabelle, Lean or THF constant from it, or return a model whose keys are typed by
the user as ``"P(a)"``. For those the kit writes every constant by its bare name
(``key_text``), exactly as it did before a constant could be written in quotes, so a proof
search visits its terms in the same order, an exported theory has the same identifiers, and a
countermodel has the same keys.

Every expected value is worked out by hand from the rule of the route and written as a literal:

* an order compares ``(weight, text)`` pairs, the weight being the size of the term and the text
  the term with every constant written by its bare name, as plain strings; two constants of
  one weight are ordered by their names;
* the Isabelle / THF / Lean names are the lower-case-initial ASCII stems of the key of the atom
  in which every character other than a letter, a digit or an underscore is an underscore, so
  the key ``P(a)`` gives ``p_a_`` (a quote in the text, ``P('a')``, would give ``p__a__``);
* a countermodel has one key per atom, the text of the atom with its constants bare.

Where a name must tell the bare reading from the quoted one it is a name for which the two orders
differ: the constant ``b`` (quoted in the text of a formula, ``'b'``, and the quote sorts before
every letter) next to the constant ``ab`` (bare). Every group of tests has a control that shows
the check can fail: the text of a formula holds the quote, and ordering or naming by it gives the
other answer.
"""

import itertools

import pytest

from unicode_logic_kit.atp import resolution as prover
from unicode_logic_kit.atp import resolution_check as checker
from unicode_logic_kit.atp.fitch_search import _Search
from unicode_logic_kit.atp.kripke_enum import _agent_key as enum_operator_key, modal_enum_search
from unicode_logic_kit.atp.linear import check_ill_proof, ill_prove
from unicode_logic_kit.atp.ltl_tableau import ltl_countermodel, ltl_trace_satisfies
from unicode_logic_kit.atp.modal_tableau import modal_countermodel
from unicode_logic_kit.atp.resolution_check import (
    ResolutionDerivation, ResolutionStep, verify_resolution_proof,
)
from unicode_logic_kit.atp.tableau import _terms_of, tableau_model
from unicode_logic_kit.fol._linear_nodes import _ill_sort_key, render_ill_formula
from unicode_logic_kit.fol._msfl_nodes import key_text
from unicode_logic_kit.fol.nodes import (
    And, Atom, Box, Constant, Eventually, Function, Implies, Not, Number, SortedConstant,
    Tensor, Would,
)
from unicode_logic_kit.fol.qml import _OBJECT, _signature_typing_facts
from unicode_logic_kit.hol.classical import _sanitize
from unicode_logic_kit.hol.deepshallow._common import AtomConsts, sanitize_atom
from unicode_logic_kit.hol.deepshallow.modal import modal_to_deep
from unicode_logic_kit.hol.deepshallow.relevant import rel_to_deep
from unicode_logic_kit.hol.isabelle_conditional import to_isabelle_conditional, to_thf_conditional
from unicode_logic_kit.hol.isabelle_relevant import to_isabelle_relevant
from unicode_logic_kit.hol.isabelle_runner import _find_alethic_countermodel
from unicode_logic_kit.hol.isabelle_substructural import to_isabelle_ill, to_isabelle_lambek
from unicode_logic_kit.hol.lean import to_lean_modal_k
from unicode_logic_kit.hol.manyvalued import to_isabelle_matrix, to_thf_k3lp
from unicode_logic_kit.semantics.matrix import K3_MATRIX

a, b, c = Constant("a"), Constant("b"), Constant("c")
ab = Constant("ab")


def P(term):
    return Atom("P", [term])


def Q(term):
    return Atom("Q", [term])


def eq(left, right):
    return Atom("=", [left, right])


# ---------------------------------------------------------------------------
# The controls: the text of a formula has the quote, the key has not
# ---------------------------------------------------------------------------

class TestTheTwoTextsDiffer:
    """What every test below relies on: for ``Constant("a")`` the two texts are not one string."""

    def test_the_text_of_a_formula_quotes_a_constant_that_reads_as_a_variable(self):
        assert P(a).to_unicode_str() == "P('a')"
        assert P(Constant("k2")).to_unicode_str() == "P('k2')"

    def test_the_key_writes_the_bare_name(self):
        assert key_text(P(a)) == "P(a)"
        assert key_text(P(Constant("k2"))) == "P(k2)"

    def test_a_constant_that_reads_back_bare_has_one_text(self):
        # ``ab`` is one whole NAME token, so nothing needs quoting
        assert P(ab).to_unicode_str() == "P(ab)"
        assert key_text(P(ab)) == "P(ab)"

    def test_the_two_texts_order_the_constants_b_and_ab_in_opposite_ways(self):
        # as text of a formula: "'b'" < "ab" because "'" (U+0027) sorts before "a" (U+0061);
        # as keys: "ab" < "b" because "a" sorts before "b"
        assert b.to_unicode_str() < ab.to_unicode_str()
        assert key_text(ab) < key_text(b)


# ---------------------------------------------------------------------------
# Resolution: the term order and the literal order, in the prover and in its checker
# ---------------------------------------------------------------------------

class TestResolutionOrder:
    NAMES = ["a", "b", "c", "ab", "k2", "K2", "1", "x1", "a b", "_sk0", "Alice", "zz"]

    @pytest.mark.parametrize("module", [prover, checker], ids=["prover", "checker"])
    def test_two_constants_are_ordered_by_their_names(self, module):
        # one weight (1, a leaf), so the order is the order of the names as plain strings:
        # 'b' > 'a', 'bb' > 'aa'
        assert module._term_gt(Constant("b"), Constant("a")) is True
        assert module._term_gt(Constant("a"), Constant("b")) is False
        assert module._term_gt(Constant("bb"), Constant("aa")) is True
        assert module._term_gt(Constant("aa"), Constant("bb")) is False

    @pytest.mark.parametrize("module", [prover, checker], ids=["prover", "checker"])
    def test_quotes_play_no_part_in_the_order(self, module):
        # the pair (b, ab): "b" > "ab" as names, so b is the greater term. In the text of a
        # formula the quoted b sorts BEFORE ab (see TestTheTwoTextsDiffer): the order must not
        # follow that text
        assert module._term_gt(b, ab) is True
        assert module._term_gt(ab, b) is False

    @pytest.mark.parametrize("module", [prover, checker], ids=["prover", "checker"])
    def test_the_order_of_compound_terms_follows_the_bare_names_too(self, module):
        # f(b) and f(ab) weigh 2 each; the keys are "f(b)" and "f(ab)", and "b" > "ab" at the
        # third character, so f(b) is the greater term
        assert module._term_gt(Function("f", [b]), Function("f", [ab])) is True
        assert module._term_gt(Function("f", [ab]), Function("f", [b])) is False

    def test_prover_and_checker_agree_on_every_pair_and_follow_the_names(self):
        for left, right in itertools.permutations(self.NAMES, 2):
            s, t = Constant(left), Constant(right)
            expected = left > right
            assert prover._term_gt(s, t) is expected, (left, right)
            assert checker._term_gt(s, t) is expected, (left, right)

    def test_a_heavier_term_is_greater_whatever_the_names(self):
        # f(a) weighs 2, the constant zz weighs 1
        for module in (prover, checker):
            assert module._term_gt(Function("f", [a]), Constant("zz")) is True
            assert module._term_gt(Constant("zz"), Function("f", [a])) is False

    def test_the_order_key_is_the_weight_and_the_bare_text(self):
        for module in (prover, checker):
            assert module._term_order_key(Constant("k2")) == (1, "k2")
            assert module._term_order_key(Function("f", [Constant("k2")])) == (2, "f(k2)")

    def test_the_order_by_the_text_of_a_formula_would_be_another_one(self):
        # the control: with the quoted text the pair (b, ab) is ordered the other way
        quoted = (1, b.to_unicode_str()), (1, ab.to_unicode_str())
        assert (quoted[0] > quoted[1]) is False
        assert prover._term_gt(b, ab) is True

    @pytest.mark.parametrize("module", [prover, checker], ids=["prover", "checker"])
    def test_a_literal_is_sorted_by_its_bare_text(self, module):
        assert module._lit_key(Not(P(Constant("k2")))) == "¬P(k2)"
        assert module._lit_key(P(b)) == "P(b)"
        assert sorted([P(b), P(ab)], key=module._lit_key) == [P(ab), P(b)]

    def test_a_clause_is_shown_with_quotes_in_the_order_of_the_bare_texts(self):
        # sorted by "P(ab)" < "P(b)", shown as the text of a formula: P(ab) ∨ P('b')
        assert checker._render_clause(frozenset({P(b), P(ab)})) == "P(ab) ∨ P('b')"

    def test_the_rewrite_rule_of_an_equation_points_from_the_greater_term_to_the_smaller(self):
        # ab = b is read as the rule b -> ab, because b is the greater term
        assert prover._unit_rewrite_rules([frozenset({eq(ab, b)})]) == [(b, ab)]
        assert prover._unit_rewrite_rules([frozenset({eq(b, a)})]) == [(b, a)]
        assert prover._unit_rewrite_rules([frozenset({eq(Constant("aa"), Constant("bb"))})]) == [
            (Constant("bb"), Constant("aa"))]


class TestResolutionProves:
    def test_a_problem_over_the_constants_a_b_c_is_proved(self):
        # a = b, b = c, P(a) entail P(c) by two rewrites
        assert prover.prove([eq(a, b), eq(b, c), P(a)], P(c)) is True

    def test_a_problem_that_does_not_follow_is_not_proved(self):
        # P(a) and a = b say nothing about c
        assert prover.prove([eq(a, b), P(a)], P(c)) is False

    def test_a_problem_whose_orientation_depends_on_the_bare_names_is_proved(self):
        # ab = b with P(b) entails P(ab); the rule used is b -> ab
        assert prover.prove([eq(ab, b), P(b)], P(ab)) is True

    def test_a_proof_by_rewriting_passes_the_independent_checker(self):
        # inputs: 1. {b = a}  2. {P(b)}  3. {¬P(a)}
        # 4. {P(a)} by demodulating 2 with 1: left side b matches the subterm b at position (0,),
        #    the right side is a, and b > a as names (equal weight, "b" > "a")
        # 5. {} by resolving 3 with 4
        equation = eq(b, a)
        inputs = (frozenset({equation}), frozenset({P(b)}), frozenset({Not(P(a))}))
        steps = (
            ResolutionStep(1, frozenset({equation}), "input"),
            ResolutionStep(2, frozenset({P(b)}), "input"),
            ResolutionStep(3, frozenset({Not(P(a))}), "input"),
            ResolutionStep(4, frozenset({P(a)}), "demodulate", (2, 1), eq_literal=equation,
                           target_literal=P(b), direction="lr", position=(0,)),
            ResolutionStep(5, frozenset(), "resolve", (3, 4)),
        )
        result = verify_resolution_proof(ResolutionDerivation(inputs, steps))
        assert result.ok, result.error
        assert result.refuted is True

    def test_a_rewrite_against_the_order_is_refused_by_the_checker(self):
        # inputs: 1. {a = b}  2. {¬P(a)}; rewriting a to b with the direction left to right
        # goes from the smaller term (a) to the greater one (b), which is not a simplification
        equation = eq(a, b)
        inputs = (frozenset({equation}), frozenset({Not(P(a))}))
        steps = (
            ResolutionStep(1, frozenset({equation}), "input"),
            ResolutionStep(2, frozenset({Not(P(a))}), "input"),
            ResolutionStep(3, frozenset({Not(P(b))}), "demodulate", (2, 1), eq_literal=equation,
                           target_literal=Not(P(a)), direction="lr", position=(0,)),
        )
        result = verify_resolution_proof(ResolutionDerivation(inputs, steps))
        assert result.ok is False
        assert result.error_index == 3
        assert "does not strictly decrease" in result.error

    def test_a_rewrite_that_is_a_simplification_only_by_the_bare_names_is_accepted(self):
        # inputs: 1. {ab = b}  2. {P(b)}  3. {¬P(ab)}
        # 4. {P(ab)} by demodulating 2 with 1 from right to left: the source is b, the result
        #    ab, and b > ab as names ("b" > "ab"). By the text of a formula ('b' < ab) the
        #    checker would call this rewrite an increase and refuse it.
        equation = eq(ab, b)
        inputs = (frozenset({equation}), frozenset({P(b)}), frozenset({Not(P(ab))}))
        steps = (
            ResolutionStep(1, frozenset({equation}), "input"),
            ResolutionStep(2, frozenset({P(b)}), "input"),
            ResolutionStep(3, frozenset({Not(P(ab))}), "input"),
            ResolutionStep(4, frozenset({P(ab)}), "demodulate", (2, 1), eq_literal=equation,
                           target_literal=P(b), direction="rl", position=(0,)),
            ResolutionStep(5, frozenset(), "resolve", (3, 4)),
        )
        result = verify_resolution_proof(ResolutionDerivation(inputs, steps))
        assert result.ok, result.error


# ---------------------------------------------------------------------------
# The other orders: tableau, natural-deduction search, linear logic, quantified modal logic
# ---------------------------------------------------------------------------

class TestOtherOrders:
    def test_tableau_tries_the_terms_in_the_order_of_their_bare_names(self):
        # ground terms b and ab: "ab" < "b"
        assert _terms_of(And(P(b), P(ab)), (), 8) == (ab, b)

    def test_tableau_keeps_the_terms_it_was_given_in_front(self):
        assert _terms_of(And(P(b), P(ab)), (c,), 8) == (c, ab, b)

    def test_the_search_for_a_natural_deduction_proof_orders_its_terms_by_their_bare_names(self):
        search = _Search([And(P(b), P(ab))], P(b), 3)
        assert search.base_terms == [ab, b]

    def test_the_sort_key_of_a_linear_formula_has_the_bare_names(self):
        # fully parenthesised, then NUL, then the repr; the part before NUL is the text
        assert _ill_sort_key(Tensor(P(b), P(ab))).split("\x00")[0] == "(P(b) ⊗ P(ab))"
        assert sorted([P(b), P(ab)], key=_ill_sort_key) == [P(ab), P(b)]

    def test_the_linear_text_of_a_formula_has_the_quotes(self):
        assert render_ill_formula(Tensor(P(b), P(ab))) == "(P('b') ⊗ P(ab))"

    def test_a_linear_sequent_over_such_constants_is_proved_and_checked(self):
        # P(b) ⊗ P(ab) ⊢ P(ab) ⊗ P(b) by commutativity
        derivation = ill_prove([Tensor(P(b), P(ab))], Tensor(P(ab), P(b)))
        assert derivation is not None
        assert check_ill_proof(derivation) is True

    def test_the_typing_facts_of_a_quantified_modal_formula_are_in_the_order_of_the_bare_names(self):
        facts = _signature_typing_facts(And(P(b), P(ab)))
        assert facts == [Atom(_OBJECT, (ab,)), Atom(_OBJECT, (b,))]

    def test_a_numeral_and_a_constant_spelled_like_it_share_one_typing_fact_as_before(self):
        # the dictionary of constants is keyed by the bare text, so Constant("1") and Number(1)
        # are one entry; this is how the route has always behaved
        facts = _signature_typing_facts(And(P(Constant("1")), P(Number(1))))
        assert len(facts) == 1


# ---------------------------------------------------------------------------
# Identifiers of a target language derived from the text of an atom
# ---------------------------------------------------------------------------

class TestDerivedNames:
    def test_the_control_the_quoted_text_would_give_another_identifier(self):
        # key P(a): P_a_ -> p_a_ ; text P('a'): P__a__ -> p__a__
        assert _sanitize("P(a)") == "p_a_"
        assert _sanitize(P(a).to_unicode_str()) == "p__a__"
        assert sanitize_atom("P(a)") == "p_P_a_"
        assert sanitize_atom(P(a).to_unicode_str()) == "p_P__a__"

    def test_an_isabelle_conditional_term_names_its_atoms_by_the_bare_key(self):
        atoms = AtomConsts()
        term = to_isabelle_conditional(Would(P(a), Q(a)), atoms)
        assert term == "(CondC p_P_a_ p_Q_a_)"
        assert atoms.decls() == ['consts p_P_a_ :: "s"', 'consts p_Q_a_ :: "s"']

    def test_a_thf_conditional_problem_names_its_atoms_by_the_bare_key(self):
        text = to_thf_conditional(Would(P(a), Q(a)))
        assert "thf(p_a__type, type, ( p_a_ : w > $o ))." in text
        assert "thf(q_a__type, type, ( q_a_ : w > $o ))." in text
        assert "( p_a_ @ U0 )" in text
        assert "p__a__" not in text

    def test_a_deep_modal_term_names_its_atoms_by_the_bare_key(self):
        atoms = AtomConsts()
        assert modal_to_deep(Box(P(a)), atoms) == "(BoxD (Atm p_P_a_))"
        assert atoms.decls() == ['consts p_P_a_ :: "s"']

    def test_a_deep_relevant_term_names_its_atoms_by_the_bare_key(self):
        atoms = AtomConsts()
        assert rel_to_deep(P(a), atoms) == "(Atm p_P_a_)"
        assert atoms.decls() == ['consts p_P_a_ :: "s"']

    def test_the_relevant_exports_still_take_nullary_atoms_only(self):
        # an atom with a constant never reaches a name, so its refusal is the only thing to see;
        # the refusal shows the formula, in its own text
        assert 'consts p_p :: "w \\<Rightarrow> bool"' in to_isabelle_relevant(Atom("p", []))
        with pytest.raises(TypeError, match=r"P\('a'\)"):
            to_isabelle_relevant(P(a))

    def test_a_lean_modal_embedding_names_its_atoms_by_the_bare_key(self):
        text = to_lean_modal_k(Box(P(a)))
        assert "axiom p_a_ : World → Prop" in text
        assert "theorem goal : ∀ w0 : World, (∀ w1 : World, R w0 w1 → (p_a_ w1)) := by" in text
        assert "p__a__" not in text

    def test_a_many_valued_thf_problem_names_its_valuation_variable_by_the_bare_key(self):
        # key P(a) -> P_a_ -> V_P_a_ -> upper-cased V_P_A_
        text = to_thf_k3lp(Not(P(a)))
        assert "thf(goal, conjecture, ( ! [V_P_A_: tv] : ( des @ ( kneg @ V_P_A_ ) ) ))." in text
        assert "V_P__A__" not in text

    def test_a_many_valued_isabelle_theory_names_its_valuation_variable_by_the_bare_key(self):
        text = to_isabelle_matrix(Not(P(a)), K3_MATRIX)
        assert r"\<exists>v_p_a_. \<not> des ((mv_neg v_p_a_))" in text
        assert "v_p__a__" not in text

    def test_the_formula_shown_in_a_comment_keeps_the_text_of_a_formula(self):
        # a comment line is for a reader, so it shows the quote
        assert "% Formula: ¬P('a')" in to_thf_k3lp(Not(P(a)))


class TestSubstructuralExports:
    def test_a_derivation_over_a_constant_that_needs_quotes_exports_with_the_bare_key(self):
        atom = P(Constant("k2"))
        theory = to_isabelle_ill([atom], atom)
        assert ('lemma ill_goal: "derivable [(IAtom \'\'P(k2)\'\')] (IAtom \'\'P(k2)\'\')"'
                in theory.splitlines())
        # the sequent in the comment is the text of a formula, with its quotes
        assert "(* Sequent: P('k2') ⊢ P('k2') *)" in theory.splitlines()

    def test_the_same_holds_for_the_lambek_export(self):
        atom = P(Constant("k2"))
        theory = to_isabelle_lambek([atom], atom)
        assert ('lemma lambek_goal: "derivable [(LAtom \'\'P(k2)\'\')] (LAtom \'\'P(k2)\'\')"'
                in theory.splitlines())
        assert "(* Sequent: P('k2') ⊢ P('k2') *)" in theory.splitlines()

    def test_no_string_literal_of_the_theory_holds_a_quote_of_a_constant(self):
        atom = P(Constant("k2"))
        for theory in (to_isabelle_ill([atom], atom), to_isabelle_lambek([atom], atom)):
            code = [line for line in theory.splitlines() if not line.startswith("(*")]
            assert not any("'k2'" in line for line in code)

    def test_a_constant_whose_name_holds_a_quote_is_still_refused_by_name(self):
        atom = P(Constant("it's"))
        with pytest.raises(NotImplementedError, match="single quote"):
            to_isabelle_ill([atom], atom)


# ---------------------------------------------------------------------------
# Countermodels returned as tables keyed by the text of an atom
# ---------------------------------------------------------------------------

class TestCountermodelKeys:
    def test_an_enumerated_countermodel_has_the_bare_key(self):
        # ¬P(a) is false in a one-world model in which P(a) holds; there is one atom
        result = modal_enum_search(Not(P(a)))
        assert result.model is not None
        assert result.model.worlds == {0}
        assert result.model.valuation == {0: {"P(a)"}}

    def test_an_enumerated_countermodel_of_a_sorted_constant_has_the_bare_keys(self):
        # Mortal(a:Human) is read as Mortal(a); the guard Human(a) holds at every world
        result = modal_enum_search(Not(Atom("Mortal", [SortedConstant("a", "Human")])))
        assert result.model is not None
        assert result.model.valuation == {0: {"Human(a)", "Mortal(a)"}}

    def test_the_relation_name_of_an_operator_with_an_unnamed_index_is_empty_as_before(self):
        # the empty name has no text of a formula (it is refused there); as a name it is ""
        assert enum_operator_key(Constant("")) == ""

    def test_a_tableau_countermodel_has_the_bare_keys(self):
        # P(b) true, Q(ab) false
        model = tableau_model([P(b), Not(Q(ab))])
        assert model == {"P(b)": True, "Q(ab)": False}

    def test_a_modal_tableau_countermodel_has_the_bare_key(self):
        # P(a) → □P(a) fails at world 0 with P(a) true and a successor 1 where it is false
        model = modal_countermodel(Implies(P(a), Box(P(a))))
        assert model is not None
        assert model.valuation == {0: {"P(a)"}, 1: set()}
        assert model.relations == {"alethic": {(0, 1)}}

    def test_a_linear_time_countermodel_has_the_bare_key(self):
        # ¬P(a) is false at position 0, so P(a) is among the atoms of the trace, and no other
        # key can be there
        trace = ltl_countermodel(Not(P(a)))
        assert trace is not None
        assert trace.witness_position == 0
        assert set().union(*trace.prefix, *trace.cycle) == {"P(a)"}
        assert ltl_trace_satisfies(P(a), trace) is True

    def test_a_linear_time_countermodel_of_an_unfulfilled_eventuality_has_no_key(self):
        trace = ltl_countermodel(Eventually(P(a)))
        assert trace is not None
        assert set().union(*trace.prefix, *trace.cycle) == set()

    def test_the_countermodel_the_isabelle_runner_shows_has_the_bare_key(self):
        text = _find_alethic_countermodel(Not(P(a)), "K")
        assert text == ("Kripke counter-model (frame K, 1 world(s)): worlds={0}, r={}, "
                        "valuation=[0:{P(a)}]; formula is false at world 0")

    def test_the_control_the_text_of_a_formula_would_be_another_key(self):
        assert P(a).to_unicode_str() != key_text(P(a))
        assert "P('a')" not in repr(modal_enum_search(Not(P(a))).model)
