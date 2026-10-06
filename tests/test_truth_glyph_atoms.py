"""The atoms named like the two truth glyphs are the truth constants.

``Atom('⊥', ())`` prints as ``⊥`` exactly like ``Atom('$false', ())`` does, and the printed
glyph reads back as ``$false``: one glyph has one meaning. The nullary atom NAMED ``⊥`` is
therefore falsity and the one named ``⊤`` is truth, on every route, and a route that has
no reading of the constants refuses these atoms by name like it refuses ``$true`` and
``$false``. The same name WITH arguments is an ordinary predicate and is neither constant.

Four questions, each answered by hand from what the two constants mean (``⊤`` holds in every
interpretation, ``⊥`` in none):

1. ``⊥ ⊢ Q`` is valid: no interpretation makes the premise true, so every interpretation
   that does satisfies ``Q``, vacuously.
2. ``⊢ ⊤`` is valid: the goal holds everywhere.
3. ``⊢ ¬⊥`` is valid: the negation of a constant that holds nowhere holds everywhere.
4. ``⊤ ⊢ Q`` is NOT valid: ``Q`` false and the premise (true everywhere) is a counterexample.
"""

from itertools import product

import pytest
import z3

from unicode_fol_kit.fol.nodes import Atom, And, Constant, Implies, Not, Or
from unicode_fol_kit.fol._truth_constants import (
    is_false_constant, is_true_constant, is_truth_constant, refuse_truth_constants,
    truth_constants_in, truth_value,
)
from unicode_fol_kit.api import prove
from unicode_fol_kit.atp.protocol import _REGISTRY
from unicode_fol_kit.atp.sequent import axiom, check_sequent_proof, derive, sequent
from unicode_fol_kit.atp.lj import check_lj_proof
from unicode_fol_kit.atp.fitch import Proof, check_proof, line, premise, verify_proof
from unicode_fol_kit.atp.tableau import prove_tableau_detailed
from unicode_fol_kit.atp.tableau_check import check_tableau_proof
from unicode_fol_kit.atp.resolution_check import (
    ResolutionDerivation, ResolutionStep, verify_resolution_proof,
)
from test_truth_constants_routes import BACKENDS, DIRECT_ROUTES

TOP = Atom("⊤", ())
BOT = Atom("⊥", ())
TRUE = Atom("$true", ())
FALSE = Atom("$false", ())
P = Atom("P", ())
Q = Atom("Q", ())

#: (premises, goal, valid?)
PROBLEMS = {
    "bot_entails_anything": ([BOT], Q, True),
    "top_is_valid": ([], TOP, True),
    "not_bot_is_valid": ([], Not(BOT), True),
    "top_does_not_entail": ([TOP], Q, False),
}


# ---------------------------------------------------------------------------
# The recognisers
# ---------------------------------------------------------------------------

def truth_constant_word(atom):
    """The TPTP word of a truth constant (``$true`` / ``$false``), or ``None``."""
    from unicode_fol_kit.fol._tptp_symbols import truth_constant_word as word
    return word(atom)


def is_tptp_boolean_atom(atom):
    from unicode_fol_kit.fol._tptp_symbols import is_tptp_boolean_atom as is_boolean
    return is_boolean(atom)


def test_the_atoms_named_like_the_glyphs_are_the_constants():
    assert truth_value(TOP) is True and truth_value(BOT) is False
    assert is_true_constant(TOP) and not is_true_constant(BOT)
    assert is_false_constant(BOT) and not is_false_constant(TOP)
    assert is_truth_constant(TOP) and is_truth_constant(BOT)
    assert is_tptp_boolean_atom(TOP) and is_tptp_boolean_atom(BOT)
    assert truth_constant_word(TOP) == "$true" and truth_constant_word(BOT) == "$false"
    # the TPTP spellings are the same two constants
    assert truth_constant_word(TRUE) == "$true" and truth_constant_word(FALSE) == "$false"


def test_a_glyph_name_with_arguments_is_an_ordinary_predicate():
    for name in ("⊤", "⊥"):
        odd = Atom(name, [Constant("a")])
        assert truth_value(odd) is None
        assert not is_truth_constant(odd)
        assert not is_tptp_boolean_atom(odd)
        assert truth_constant_word(odd) is None


def test_one_constant_is_listed_once_whatever_its_spelling():
    # `$false` and `⊥` are ONE constant: a formula that holds both lists the first
    both = And(Or(FALSE, BOT), Or(TOP, TRUE))
    assert truth_constants_in([both]) == (FALSE, TOP)
    assert truth_constants_in([Or(BOT, FALSE)]) == (BOT,)


def test_a_refusal_names_the_glyph_the_formula_was_written_with():
    with pytest.raises(NotImplementedError) as info:
        refuse_truth_constants([Implies(P, BOT)], "some_route", "no reading of it")
    assert "⊥" in str(info.value) and "some_route" in str(info.value)


# ---------------------------------------------------------------------------
# The four questions, on every route that decides
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("problem", list(PROBLEMS))
@pytest.mark.parametrize("route", sorted(DIRECT_ROUTES))
def test_four_problems_in_every_direct_route(route, problem):
    premises, goal, valid = PROBLEMS[problem]
    assert bool(DIRECT_ROUTES[route](list(premises), goal)) is valid


@pytest.mark.parametrize("problem", list(PROBLEMS))
@pytest.mark.parametrize("name", sorted(BACKENDS))
def test_four_problems_in_every_registered_backend(name, problem):
    backend = _REGISTRY[name]
    if not backend.available():
        pytest.skip(f"{name} is not installed here")
    logic, ability = BACKENDS[name]
    premises, goal, valid = PROBLEMS[problem]
    verdict = prove(goal, premises, backends=[name], logic=logic, timeout=20000)
    if valid:
        if ability == "refutes":
            assert verdict.status != "refuted"
        else:
            assert verdict.status == "proved"
    else:
        if ability == "proves":
            assert verdict.status != "proved"
        else:
            assert verdict.status == "refuted"


def test_a_countermodel_of_top_entails_q_reads_no_symbol_for_the_glyph():
    # ⊤ ⊢ Q has the countermodel with Q false; the constant is no entry of it
    from unicode_fol_kit.semantics.modelfinder import find_countermodel
    model = find_countermodel([TOP], Q)
    assert model is not None
    assert "⊤" not in str(model)
    verdict = prove(Q, [TOP], backends=["z3"])
    assert verdict.status == "refuted"
    assert "⊤" not in str(verdict.countermodel)


@pytest.mark.parametrize("name", ["ill", "lambek", "relevant"])
def test_a_logic_with_no_reading_refuses_the_glyph_like_the_dollar_word(name):
    # `lambek` has no empty antecedent, so the question carries a premise. A single-member
    # chain summarises the member's own answer in its detail: ``<name>:unknown/unsupported``
    # followed by the refusal, which names the constant the formula was written with.
    for constant in (BOT, TOP):
        glyph = prove(Q, [constant], backends=[name], logic=name, timeout=5000)
        word = prove(Q, [truth_word_atom(constant)], backends=[name], logic=name, timeout=5000)
        assert glyph.status == "unknown" and word.status == "unknown"
        assert f"{name}:unknown/unsupported" in glyph.detail
        assert f"the truth constant {constant.predicate} has no agreed reading" in glyph.detail
        # the same refusal as for the TPTP word, with the glyph for its name
        said = f"the truth constant {constant.predicate} has"
        meant = f"the truth constant {truth_constant_word(constant)} has"
        assert glyph.detail.replace(said, meant) == word.detail


def truth_word_atom(glyph_atom):
    return Atom("$true" if glyph_atom.predicate == "⊤" else "$false", ())


# ---------------------------------------------------------------------------
# What each writer writes for them
# ---------------------------------------------------------------------------

#: (P ∧ ⊤) → ¬⊥
CLASSICAL = Implies(And(P, TOP), Not(BOT))
#: □⊤ → ◇¬⊥
def _modal():
    from unicode_fol_kit.fol.nodes import Box, Diamond
    return Implies(Box(TOP), Diamond(Not(BOT)))


def test_the_single_formula_renderers_write_the_constants_words():
    assert TOP.to_tptp() == "$true" and BOT.to_tptp() == "$false"
    assert TOP.to_prover9() == "$T" and BOT.to_prover9() == "$F"
    assert CLASSICAL.to_tptp() == "((p & $true) => ~($false))"
    assert CLASSICAL.to_prover9() == '(("P" & $T) -> -($F))'
    assert z3.is_true(TOP.to_z3()) and z3.is_false(BOT.to_z3())
    assert TOP.to_unicode_str() == "⊤" and BOT.to_unicode_str() == "⊥"
    assert TOP.to_latex() == r"\top" and BOT.to_latex() == r"\bot"


def test_the_smtlib_and_casl_writers_write_the_constants_words():
    from unicode_fol_kit.atp.z3_input import to_smtlib
    from unicode_fol_kit.fol.casl_export import formula_to_casl
    assert "(=> (and P true) (not false))" in to_smtlib(CLASSICAL)
    assert formula_to_casl(CLASSICAL) == "(P /\\ true) => not false"
    assert formula_to_casl(TOP) == "true" and formula_to_casl(BOT) == "false"


def test_the_higher_order_writers_write_the_constants_and_declare_nothing_for_them():
    from unicode_fol_kit.hol.classical import to_isabelle_fol, to_thf_fol
    from unicode_fol_kit.hol.lean import to_lean_fol
    thf = to_thf_fol(CLASSICAL)
    assert "( ( p & $true ) => ( ~ $false ) )" in thf
    assert [ln for ln in thf.splitlines() if "_decl" in ln] == [ln for ln in thf.splitlines() if "p_decl" in ln]
    isabelle = to_isabelle_fol(CLASSICAL)
    assert r"((p \<and> True) \<longrightarrow> (\<not> False))" in isabelle
    assert [ln for ln in isabelle.splitlines() if ln.startswith("consts ")] == ['consts p :: "bool"']
    lean = to_lean_fol(CLASSICAL)
    assert "((p ∧ True) → (¬ False))" in lean
    assert [ln.split(" : ")[0] for ln in lean.splitlines() if ln.startswith("axiom")] == [
        "axiom Ind", "axiom Ind_nonempty", "axiom p"]


def test_the_modal_writers_lift_the_constants_to_world_independent_propositions():
    from unicode_fol_kit.fol.qml import to_isabelle_modal, to_thf_modal
    thf = to_thf_modal(_modal())
    assert "( ^ [W: mu] : $true )" in thf and "( ^ [W: mu] : $false )" in thf
    assert "⊤" not in thf and "⊥" not in thf
    isabelle = to_isabelle_modal(_modal())
    assert r"(mbox (\<lambda>_. True))" in isabelle and r"(mnot (\<lambda>_. False))" in isabelle


def test_the_nxf_writer_declares_no_symbol_for_the_glyph_atoms():
    from unicode_fol_kit.atp.tptp_ncl import to_tptp_ncl
    text = to_tptp_ncl(_modal())
    assert "([.] $true => <.> ~($false))" in text
    assert "_decl" not in text and "⊤" not in text and "⊥" not in text


@pytest.mark.parametrize("name", ["fof", "tff", "tfa"])
def test_the_problem_writers_write_the_constants_words(name):
    from unicode_fol_kit.atp._tff_problem import generate_tff_arith_problem
    from unicode_fol_kit.atp._tptp_problem import generate_tptp_problem
    from unicode_fol_kit.atp.tptp_tff import generate_tff_problem
    writer = {"fof": generate_tptp_problem, "tff": generate_tff_problem,
              "tfa": lambda prem, goal: generate_tff_arith_problem(prem, goal, sort="int")[0]}[name]
    text = writer([BOT, P], And(P, TOP))
    assert "$false" in text and "$true" in text
    assert "⊤" not in text and "⊥" not in text
    # the same problem with the TPTP words is the same text
    assert text == writer([FALSE, P], And(P, TRUE))
    # and nothing is declared for a constant
    assert all("$true" not in ln and "$false" not in ln for ln in text.splitlines() if "type" in ln)


def test_the_prover9_problem_writer_writes_the_constants_words():
    from unicode_fol_kit.atp.prover9_entailment import generate_prover9_input_with_mapping
    text = generate_prover9_input_with_mapping([BOT], Q)[0]
    assert "$F." in text and "⊥" not in text
    assert text == generate_prover9_input_with_mapping([FALSE], Q)[0]


# ---------------------------------------------------------------------------
# The checkers take the glyph atoms for the constants
# ---------------------------------------------------------------------------

ATOMS = (P, TOP, BOT)


def _subsets(items):
    out = [()]
    for item in items:
        out += [s + (item,) for s in out]
    return out


def _holds(sequent_, p_value):
    """Whether ``⋀antecedent → ⋁succedent`` holds when ``P`` has ``p_value``."""
    def value(atom):
        return {"P": p_value, "⊤": True, "⊥": False}[atom.predicate]
    return (not all(value(a) for a in sequent_.antecedent)
            or any(value(a) for a in sequent_.succedent))


def test_the_sequent_axiom_accepts_exactly_the_valid_sequents_over_the_atoms():
    # 64 sequents with each side a subset of {P, ⊤, ⊥}. Worked by hand: P on both sides is
    # the identity axiom, ⊤ on the right and ⊥ on the left are the constant axioms, and every
    # other sequent has a countermodel (P true only on the left, P false only on the right,
    # ⊤ on the left and ⊥ on the right with nothing else true / false).
    for left, right in product(_subsets(ATOMS), _subsets(ATOMS)):
        s = sequent(list(left), list(right))
        valid = all(_holds(s, p_value) for p_value in (False, True))
        assert check_sequent_proof(axiom(s)) == valid, s


def test_the_lj_axiom_accepts_exactly_the_valid_single_succedent_sequents():
    for left, right in product(_subsets(ATOMS), [(), (P,), (TOP,), (BOT,)]):
        s = sequent(list(left), list(right))
        valid = all(_holds(s, p_value) for p_value in (False, True))
        assert check_lj_proof(axiom(s)) == valid, s


def test_sequent_derivations_through_the_glyph_axioms():
    # ⊢ ¬⊥: ¬R from the axiom `⊥ ⊢`
    assert check_sequent_proof(derive(sequent([], [Not(BOT)]), "¬R", axiom(sequent([BOT], []))))
    # P ⊢ ⊤ ∧ P: ∧R from `P ⊢ ⊤` and `P ⊢ P`
    assert check_sequent_proof(derive(sequent([P], [And(TOP, P)]), "∧R",
                                      axiom(sequent([P], [TOP])), axiom(sequent([P], [P]))))
    # the same ∧R with `P ⊢ ⊥` as its left leaf is no derivation: ⊥ on the right is no axiom
    assert not check_sequent_proof(derive(sequent([P], [And(BOT, P)]), "∧R",
                                          axiom(sequent([P], [BOT])), axiom(sequent([P], [P]))))


def test_fitch_introduces_the_glyph_truth_and_eliminates_the_glyph_falsity():
    assert check_proof(Proof(steps=[line(1, TOP, "⊤I")]))
    # ⊤I concludes the truth constant and nothing else
    for wrong in (P, BOT, Not(TOP)):
        assert not verify_proof(Proof(steps=[line(1, wrong, "⊤I")])).ok, wrong
    # ⊥ ⊢ P by ⊥E, and ⊤ is no falsum
    assert check_proof(Proof(premises=[premise(1, BOT)], steps=[line(2, P, "⊥E", 1)]))
    assert not check_proof(Proof(premises=[premise(1, TOP)], steps=[line(2, P, "⊥E", 1)]))


def test_the_tableau_proves_with_the_glyph_atoms_and_its_checker_accepts():
    # ¬⊤ closes the branch on its own, and so does ⊥
    proof = prove_tableau_detailed([], TOP)
    assert proof is not None
    check_tableau_proof(proof, [], TOP)
    assert [c.literal for c in proof.closures] == [Not(TOP)]
    proof = prove_tableau_detailed([BOT], P)
    assert proof is not None
    check_tableau_proof(proof, [BOT], P)
    # nothing else closes: ⊥ is not provable, ⊤ proves no letter
    assert prove_tableau_detailed([], BOT) is None
    assert prove_tableau_detailed([TOP], P) is None


def _derivation(inputs, *steps):
    return ResolutionDerivation(inputs=inputs, steps=steps)


@pytest.mark.parametrize("dropped", [BOT, Not(TOP)])
def test_the_resolution_checker_drops_a_glyph_literal_that_is_false(dropped):
    d = _derivation([{P, dropped}],
                    ResolutionStep(1, {P, dropped}, "input"),
                    ResolutionStep(2, {P}, "truth_constants", (1,)))
    assert verify_resolution_proof(d).ok


@pytest.mark.parametrize("kept", [TOP, Not(BOT)])
def test_the_resolution_checker_keeps_a_glyph_literal_that_is_true(kept):
    d = _derivation([{P, kept}],
                    ResolutionStep(1, {P, kept}, "input"),
                    ResolutionStep(2, {P}, "truth_constants", (1,)))
    assert not verify_resolution_proof(d).ok
