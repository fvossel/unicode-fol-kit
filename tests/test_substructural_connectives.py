"""Intuitionistic linear logic and the Lambek calculus read the connectives they have rules for, and refuse every other node.

"No derivation" is a statement about a sequent the calculus can state. Each calculus has rules for a
fixed set of connectives:

* intuitionistic linear logic: ``⊗`` (Tensor), ``&`` (With), ``⊕`` (OPlus), ``⊸`` (LinearImplies), ``!``
  (OfCourse) and the units ``𝟙`` (One), ``⊤`` (Top), ``𝟘`` (Zero);
* the Lambek calculus: ``•`` (Product), ``\\`` (Under), ``/`` (Over).

Both read an atom over terms as one category. A node of ANY other logic has no rule, and reading it as one
more opaque category answers about another formula. By hand: ``A ∧ B ⊢ A`` is conjunction elimination, valid
in every classical reading, and between the two categories ``A ∧ B`` and ``A`` there is no derivation, so the
category reading says "refuted" about a valid sequent; ``A⊗B ⊢ B⊗A`` is derivable in linear logic (⊗L, then ⊗R
with two axioms) and between the categories ``A⊗B`` and ``B⊗A`` of the OTHER calculus there is none;
``(λx. P(x))(a) ⊢ P(a)`` holds by beta reduction and has no derivation between the category of an application
and the category ``P(a)``. The direct functions raise ``NotImplementedError`` naming the node, the calculus and
the connectives the calculus has; the backends answer UNKNOWN / ``unsupported`` with the same text.
"""

import random

import pytest

from unicode_fol_kit import api
from unicode_fol_kit.atp.lambek import (
    LambekDerivation, LambekSequent, lambek_derivable, lambek_prove, verify_lambek_proof,
)
from unicode_fol_kit.atp.linear import (
    ILLDerivation, ILLSequent, check_ill_proof, ill_derivable, ill_prove, verify_ill_proof,
)
from unicode_fol_kit.atp.protocol import PROVED, REFUTED, UNKNOWN, get_backend
from unicode_fol_kit.fol._linear_nodes import render_ill_formula
from unicode_fol_kit.fol.msflparser import MSFLParser
from unicode_fol_kit.fol.nodes import (
    And, At, Atom, Box, Constant, Diamond, Function, Iff, Implies, Knows, LinearImplies, LukImplication,
    LukNegation, Next, Nominal, Not, Number, Obligatory, OfCourse, One, OPlus, Or, Over, Product,
    Quantifier, StrongConjunction, Tensor, Top, Under, Until, Variable, With, Xor, Zero,
)
from unicode_fol_kit.hol.isabelle_substructural import to_isabelle_ill, to_isabelle_lambek

A, B, C = Atom("A", []), Atom("B", []), Atom("C", [])
X = Variable("x")
ALPHA = Constant("alpha")

CALCULI = {
    "ill": dict(prove=ill_prove, derivable=ill_derivable, name="intuitionistic linear logic",
                route="ill_prove", glyphs="⊗ & ⊕ ⊸ ! 𝟙 ⊤ 𝟘", fuse=Tensor, mode="linear"),
    "lambek": dict(prove=lambek_prove, derivable=lambek_derivable, name="the Lambek calculus",
                   route="lambek_prove", glyphs="• \\ /", fuse=Product, mode="lambek"),
}

#: A node of another logic, one per family: classical, modal, temporal, deontic, epistemic, hybrid, fuzzy.
FOREIGN = {
    "And": And(A, B), "Or": Or(A, B), "Not": Not(A), "Implies": Implies(A, B), "Iff": Iff(A, B),
    "Xor": Xor(A, B),
    "Box": Box(A), "Diamond": Diamond(A), "Next": Next(A), "Until": Until(A, B), "Obligatory": Obligatory(A),
    "Knows": Knows(Constant("a"), A),
    "Nominal": Nominal("i"), "At": At(Nominal("i"), A),
    "StrongConjunction": StrongConjunction(A, B), "LukImplication": LukImplication(A, B),
    "LukNegation": LukNegation(A),
}

#: The connectives of the OTHER calculus are nodes of another logic too.
OTHER_CALCULUS = {
    "ill": {"Product": Product(A, B), "Under": Under(A, B), "Over": Over(A, B)},
    "lambek": {"Tensor": Tensor(A, B), "With": With(A, B), "OPlus": OPlus(A, B),
               "LinearImplies": LinearImplies(A, B), "OfCourse": OfCourse(A), "One": One(),
               "Top": Top(), "Zero": Zero()},
}


def _refusals():
    for calculus in CALCULI:
        for kind, node in {**FOREIGN, **OTHER_CALCULUS[calculus]}.items():
            yield pytest.param(calculus, kind, node, id=f"{calculus}-{kind}")


# ---------------------------------------------------------------------------
# The two allow-lists
# ---------------------------------------------------------------------------

def test_each_calculus_reads_exactly_the_connectives_of_its_grammar():
    from unicode_fol_kit.atp._substructural_input import ILL, LAMBEK
    from unicode_fol_kit.fol._fol_nodes import parser_ops_for_mode

    ill_by_hand = {Tensor, With, OPlus, LinearImplies, OfCourse, One, Top, Zero}
    lambek_by_hand = {Product, Under, Over}
    assert set(ILL.connectives) == ill_by_hand
    assert set(LAMBEK.connectives) == lambek_by_hand
    # ... and these are the node classes the two grammars register, no more and no fewer
    assert {op.node_class for op in parser_ops_for_mode("linear")} == ill_by_hand
    assert {op.node_class for op in parser_ops_for_mode("lambek")} == lambek_by_hand
    assert ILL.glyphs == "⊗ & ⊕ ⊸ ! 𝟙 ⊤ 𝟘" and LAMBEK.glyphs == "• \\ /"


# ---------------------------------------------------------------------------
# A node of another logic is refused by name, never read as a letter
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("calculus, kind, node", list(_refusals()))
def test_the_direct_functions_refuse_a_node_of_another_logic_by_name(calculus, kind, node):
    calc = CALCULI[calculus]
    for call in (calc["prove"], calc["derivable"]):
        for antecedent, goal in (([node], A), ([A], node), ([A, B], calc["fuse"](A, node))):
            with pytest.raises(NotImplementedError) as raised:
                call(antecedent, goal)
            message = str(raised.value)
            assert message.startswith(calc["route"] + ":")
            assert f"({kind})" in message                  # the class of the refused node
            assert calc["name"] in message
            assert calc["glyphs"] in message               # which connectives the calculus has


@pytest.mark.parametrize("calculus, kind, node", list(_refusals()))
def test_the_backends_answer_unsupported_and_not_refuted_for_a_node_of_another_logic(calculus, kind, node):
    for premises, goal in (([node], A), ([A], node)):
        verdict = get_backend(calculus).decide(goal, premises)
        assert verdict.status == UNKNOWN and verdict.reason == "unsupported"
        assert verdict.status != REFUTED and verdict.countermodel is None
        assert f"({kind})" in verdict.detail and CALCULI[calculus]["name"] in verdict.detail
        assert CALCULI[calculus]["glyphs"] in verdict.detail


@pytest.mark.parametrize("calculus", sorted(CALCULI))
def test_conjunction_elimination_is_refused_and_not_answered_refuted(calculus):
    # A ∧ B ⊢ A is valid in every classical reading; the category reading answered "refuted".
    with pytest.raises(NotImplementedError, match="And"):
        CALCULI[calculus]["derivable"]([And(A, B)], A)
    verdict = api.prove(A, [And(A, B)], logic=calculus, backends=[calculus])
    assert verdict.status == UNKNOWN
    assert "And" in verdict.detail and "unsupported" in verdict.detail


def test_the_other_calculus_connectives_are_not_letters():
    # A⊗B ⊢ B⊗A holds in linear logic (⊗L, then ⊗R with the axioms B ⊢ B and A ⊢ A) ...
    assert ill_derivable([Tensor(A, B)], Tensor(B, A))
    # ... and the Lambek calculus, which has no ⊗, must not decide it as two unrelated letters:
    with pytest.raises(NotImplementedError, match="Tensor"):
        lambek_derivable([Tensor(A, B)], Tensor(B, A))
    # A•B ⊢ A•B is the axiom in L; linear logic has no •.
    assert lambek_derivable([Product(A, B)], Product(A, B))
    with pytest.raises(NotImplementedError, match="Product"):
        ill_derivable([Product(A, B)], Product(A, B))


def test_a_refused_node_inside_an_allowed_connective_or_an_atom_is_found():
    nested = Tensor(A, Tensor(B, Or(A, C)))
    with pytest.raises(NotImplementedError, match=r"\(Or\)"):
        ill_prove([nested], A)
    deep = Under(A, Over(B, Not(C)))
    with pytest.raises(NotImplementedError, match=r"\(Not\)"):
        lambek_prove([A], deep)


def test_a_quantifier_around_a_classical_connective_is_reported_as_the_quantifier():
    body = Quantifier("∀", X, And(Atom("P", [X]), Atom("Q", [X])))
    for calculus in sorted(CALCULI):
        with pytest.raises(NotImplementedError) as raised:
            CALCULI[calculus]["derivable"]([body], A)
        assert "(Quantifier)" in str(raised.value) and "(And)" not in str(raised.value)


@pytest.mark.parametrize("calculus", sorted(CALCULI))
@pytest.mark.parametrize("term", [X, ALPHA, Number(1), Function("f", [X])], ids=["variable", "constant", "numeral",
                                                                              "function"])
def test_a_term_where_a_formula_stands_is_refused(calculus, term):
    # Only an atom is a category: `x` alone is a term, and `P(x)` is the category over it.
    with pytest.raises(NotImplementedError, match="term where a formula stands"):
        CALCULI[calculus]["derivable"]([term], A)
    with pytest.raises(NotImplementedError, match="term where a formula stands"):
        CALCULI[calculus]["derivable"]([A], CALCULI[calculus]["fuse"](A, term))
    verdict = get_backend(calculus).decide(A, [term])
    assert verdict.status == UNKNOWN and verdict.reason == "unsupported"


@pytest.mark.parametrize("calculus", sorted(CALCULI))
def test_the_terms_of_an_atom_are_read_where_they_stand(calculus):
    # A variable, a constant, a numeral and a function term inside an atom are the category's own terms.
    category = Atom("R", [X, ALPHA, Number(2), Function("f", [Function("g", [X]), Number(1)])])
    assert CALCULI[calculus]["derivable"]([category], category)


# ---------------------------------------------------------------------------
# The lambda layer the two grammars share is refused as well
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("calculus", sorted(CALCULI))
def test_an_application_the_grammar_writes_is_refused_and_not_read_as_a_letter(calculus):
    # (λx. P(x))(a) is P(a) by beta reduction, so (λx. P(x))(a) ⊢ P(a) holds; as one letter it has no derivation.
    parser = MSFLParser(**{CALCULI[calculus]["mode"]: True})
    application = parser.parse("(λx. P(x))(a)")
    assert type(application).__name__ == "Application"       # the grammar does write it
    p_of_a = Atom("P", [Constant("a")])
    with pytest.raises(NotImplementedError, match="Application"):
        CALCULI[calculus]["derivable"]([application], p_of_a)
    verdict = get_backend(calculus).decide(p_of_a, [application])
    assert verdict.status == UNKNOWN and verdict.reason == "unsupported" and "Application" in verdict.detail


@pytest.mark.parametrize("calculus", sorted(CALCULI))
def test_a_lambda_in_an_argument_position_is_refused(calculus):
    abstraction = MSFLParser(**{CALCULI[calculus]["mode"]: True}).parse("λx. Q(x)")
    assert type(abstraction).__name__ == "Lambda"
    holding = Atom("P", [abstraction])
    with pytest.raises(NotImplementedError, match="Lambda"):
        CALCULI[calculus]["derivable"]([holding], A)


# ---------------------------------------------------------------------------
# What the calculus has rules for is read, and decided as before
# ---------------------------------------------------------------------------

#: (antecedent, goal, derivable), each derived by hand with the rules of the calculus.
ILL_SEQUENTS = [
    ([Tensor(A, B)], Tensor(B, A), True),            # ⊗L, ⊗R with A ⊢ A and B ⊢ B
    ([With(A, B)], A, True),                          # &L1
    ([A], OPlus(A, B), True),                         # ⊕R1
    ([A], Top(), True),                               # ⊤R, any context
    ([Zero()], C, True),                              # 0L
    ([], One(), True),                                # 1R
    ([OfCourse(A)], A, True),                         # dereliction
    ([LinearImplies(A, B), A], B, True),              # ⊸L with two axioms
    ([A], Tensor(A, A), False),                       # no contraction: ⊗R splits the single A, ⊢ A fails
    ([Tensor(A, B)], A, False),                       # B is left over and weakening is not available
    ([Top()], A, False),                              # there is no ⊤L: ⊤ carries nothing
    ([A], With(A, B), False),                         # &R needs A ⊢ B too
]
LAMBEK_SEQUENTS = [
    ([A, Under(A, B)], B, True),                      # \L
    ([Under(A, B), A], B, False),                     # no exchange
    ([Over(B, A), A], B, True),                       # /L
    ([A, Over(B, A)], B, False),                      # no exchange
    ([Product(A, B)], Product(A, B), True),           # the axiom (and •L, •R)
    ([A, B], Product(A, B), True),                    # •R
    ([B, A], Product(A, B), False),                   # order matters
]


@pytest.mark.parametrize("antecedent, goal, expected", ILL_SEQUENTS)
def test_the_connectives_of_ill_are_read_and_decided(antecedent, goal, expected):
    assert ill_derivable(antecedent, goal) is expected
    verdict = get_backend("ill").decide(goal, antecedent)
    assert verdict.status == (PROVED if expected else REFUTED)


@pytest.mark.parametrize("antecedent, goal, expected", LAMBEK_SEQUENTS)
def test_the_connectives_of_lambek_are_read_and_decided(antecedent, goal, expected):
    assert lambek_derivable(antecedent, goal) is expected
    verdict = get_backend("lambek").decide(goal, antecedent)
    assert verdict.status == (PROVED if expected else REFUTED)


# ---------------------------------------------------------------------------
# Everything the grammars write, over atoms with terms, is accepted
# ---------------------------------------------------------------------------

ATOMS = [
    Atom("P", []), Atom("Q", [ALPHA]), Atom("R", [Function("f", [X]), Number(1)]),
    Atom("<", [X, Number(2)]),
]


def _random_ill(rng, depth):
    if depth == 0 or rng.random() < 0.2:
        return rng.choice(ATOMS + [One(), Top(), Zero()])
    kind = rng.choice(["!", "⊗", "&", "⊕", "⊸"])
    if kind == "!":
        return OfCourse(_random_ill(rng, depth - 1))
    node = {"⊗": Tensor, "&": With, "⊕": OPlus, "⊸": LinearImplies}[kind]
    return node(_random_ill(rng, depth - 1), _random_ill(rng, depth - 1))


def _random_lambek(rng, depth):
    if depth == 0 or rng.random() < 0.2:
        return rng.choice(ATOMS)
    node = rng.choice([Product, Under, Over])
    return node(_random_lambek(rng, depth - 1), _random_lambek(rng, depth - 1))


def _lambek_text(node):
    if isinstance(node, Product):
        return f"({_lambek_text(node.left)} • {_lambek_text(node.right)})"
    if isinstance(node, Under):
        return f"({_lambek_text(node.left)} \\ {_lambek_text(node.right)})"
    if isinstance(node, Over):
        return f"({_lambek_text(node.left)} / {_lambek_text(node.right)})"
    if node.predicate == "<":
        # `x < 2 / P` reads the slash as the division of the comparison's right term
        return f"({node.to_unicode_str()})"
    return node.to_unicode_str()


def test_every_formula_the_linear_grammar_writes_over_atoms_is_accepted():
    rng = random.Random(20261005)
    parser = MSFLParser(linear=True)
    for _ in range(300):
        node = _random_ill(rng, 3)
        assert parser.parse(render_ill_formula(node)) == node          # the grammar writes exactly this node
        assert ill_derivable([node], node)                              # the axiom: no refusal, an answer
        assert get_backend("ill").decide(node, [node]).status == PROVED


def test_every_formula_the_lambek_grammar_writes_over_atoms_is_accepted():
    rng = random.Random(20261006)
    parser = MSFLParser(lambek=True)
    for _ in range(300):
        node = _random_lambek(rng, 3)
        assert parser.parse(_lambek_text(node)) == node
        assert lambek_derivable([node], node)
        assert get_backend("lambek").decide(node, [node]).status == PROVED


# ---------------------------------------------------------------------------
# The checker and the Isabelle export
# ---------------------------------------------------------------------------

def test_the_ill_checker_does_not_accept_a_derivation_over_a_node_of_another_logic():
    over_atoms = ILLDerivation(ILLSequent((A,), A), "Ax")
    assert verify_ill_proof(over_atoms).ok and check_ill_proof(over_atoms)
    over_and = ILLDerivation(ILLSequent((And(A, B),), And(A, B)), "Ax")
    result = verify_ill_proof(over_and)
    assert not result and result.error_rule == "formula" and "And" in result.error
    assert not check_ill_proof(over_and)
    # a node of another logic deep in a premise is found as well
    deep = ILLDerivation(ILLSequent((Tensor(A, Not(B)),), Tensor(A, Not(B))), "Ax")
    assert not check_ill_proof(deep)


def test_the_lambek_checker_does_not_accept_a_derivation_over_a_node_of_another_logic():
    over_atoms = LambekDerivation(LambekSequent((A,), A), "Ax")
    assert verify_lambek_proof(over_atoms).ok
    over_box = LambekDerivation(LambekSequent((Box(A),), Box(A)), "Ax")
    result = verify_lambek_proof(over_box)
    assert not result and result.error_rule == "formula" and "Box" in result.error


def test_the_isabelle_export_refuses_a_node_of_another_logic_by_name():
    # The text export (nothing is run): the proof search is asked first, and it refuses the node.
    with pytest.raises(NotImplementedError, match=r"\(And\)"):
        to_isabelle_ill([And(A, B)], A)
    with pytest.raises(NotImplementedError, match=r"\(Or\)"):
        to_isabelle_lambek([A, Or(A, B)], A)
