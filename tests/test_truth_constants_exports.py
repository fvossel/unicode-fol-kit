"""What the exporters write for the truth constants.

A route whose target language has the constants writes its own spelling and
declares no symbol for them: THF ``$true`` / ``$false``, Isabelle ``True`` /
``False``, Lean ``True`` / ``False``, CASL ``true`` / ``false``, SMT-LIB ``true`` /
``false``, Prover9 ``$T`` / ``$F``. A target with no such constant refuses by name
(a deep embedding, relevant and substructural logic, Prolog, nanoCoP). Nothing is
declared as a predicate called ``$true``.
"""

import pytest

from unicode_fol_kit.fol.nodes import (
    Atom, Not, And, Or, Implies, Box, Diamond, Variable, Quantifier, Would,
)

T = Atom("$true", ())
F = Atom("$false", ())
P = Atom("P", ())

#: (P ∧ $true) → ¬$false
CLASSICAL = Implies(And(P, T), Not(F))
#: □$true → ◇¬$false
MODAL = Implies(Box(T), Diamond(Not(F)))


def _declared_names(text):
    """The names on ``thf(NAME_decl, type, ...)`` lines, as a set of lines' heads."""
    return [ln for ln in text.splitlines() if "_decl" in ln or ln.startswith("consts ")
            or ln.startswith("axiom ")]


# ---------------------------------------------------------------------------
# First-order, second-order, third-order, free logic
# ---------------------------------------------------------------------------

def test_thf_fol():
    from unicode_fol_kit.hol.classical import to_thf_fol
    text = to_thf_fol(CLASSICAL)
    assert "( ( p & $true ) => ( ~ $false ) )" in text
    assert all("$true" not in ln and "$false" not in ln for ln in _declared_names(text))
    assert "p_decl" in text and len(_declared_names(text)) == 1


def test_isabelle_fol():
    from unicode_fol_kit.hol.classical import to_isabelle_fol
    text = to_isabelle_fol(CLASSICAL)
    assert r"((p \<and> True) \<longrightarrow> (\<not> False))" in text
    assert [ln for ln in text.splitlines() if ln.startswith("consts ")] == ['consts p :: "bool"']


def test_lean_fol():
    from unicode_fol_kit.hol.lean import to_lean_fol
    text = to_lean_fol(CLASSICAL)
    assert "((p ∧ True) → (¬ False))" in text
    assert [ln for ln in text.splitlines() if ln.startswith("axiom p")] == ["axiom p : Prop"]
    # the only axioms are the individual type, its non-emptiness, and the letter p
    assert [ln.split(" : ")[0] for ln in text.splitlines() if ln.startswith("axiom")] == [
        "axiom Ind", "axiom Ind_nonempty", "axiom p"]


def test_second_order_exports():
    from unicode_fol_kit.hol import secondorder
    thf = secondorder.to_thf_so(CLASSICAL)
    assert "( ( p & $true ) => ( ~ $false ) )" in thf
    assert [ln for ln in thf.splitlines() if "_decl" in ln] == ["thf(p_decl, type, ( p : ( $o ) ))."]
    isabelle = secondorder.to_isabelle_so(CLASSICAL)
    assert r"((p \<and> True) \<longrightarrow> (\<not> False))" in isabelle
    assert [ln for ln in isabelle.splitlines() if ln.startswith("consts ")] == ['consts p :: "bool"']


def test_third_order_exports():
    from unicode_fol_kit.hol import thirdorder
    thf = thirdorder.to_thf_to(CLASSICAL)
    assert "( ( p & $true ) => ( ~ $false ) )" in thf
    isabelle = thirdorder.to_isabelle_to(CLASSICAL)
    assert r"((P \<and> True) \<longrightarrow> (\<not> False))" in isabelle
    assert [ln for ln in isabelle.splitlines() if ln.startswith("consts ")] == ['consts P :: "bool"']


def test_free_logic_exports_do_not_guard_the_constants():
    from unicode_fol_kit.hol import free
    thf = free.to_thf_free(CLASSICAL)
    # the constants are propositions: no denotation guard is wrapped round them
    assert "( ( p & $true ) => ( ~ $false ) )" in thf
    isabelle = free.to_isabelle_free(CLASSICAL)
    assert r"((p \<and> True) \<longrightarrow> (\<not> False))" in isabelle


# ---------------------------------------------------------------------------
# Modal
# ---------------------------------------------------------------------------

def test_thf_modal_lifts_the_constants_to_world_independent_propositions():
    from unicode_fol_kit.fol.qml import to_thf_modal
    text = to_thf_modal(MODAL)
    assert "( ^ [W: mu] : $true )" in text
    assert "( ^ [W: mu] : $false )" in text
    assert "mbox @ ( ^ [W: mu] : $true )" in text


def test_isabelle_modal_lifts_the_constants():
    from unicode_fol_kit.fol.qml import to_isabelle_modal
    from unicode_fol_kit.hol.isabelle_modal import isabelle_modal_theory
    for text in (to_isabelle_modal(MODAL), isabelle_modal_theory(MODAL)):
        assert r"(mbox (\<lambda>_. True))" in text
        assert r"(mnot (\<lambda>_. False))" in text


def test_third_order_modal_exports():
    from unicode_fol_kit.hol import ho_modal, thf_modal
    assert "( ^ [W: mu] : $true )" in ho_modal.to_thf_ho_modal(MODAL)
    assert r"(mbox (\<lambda>_. True))" in ho_modal.to_isabelle_ho_modal(MODAL)
    assert "( ^ [W: mu] : $true )" in thf_modal.to_thf_modal_full(MODAL)


def test_lean_modal_k():
    from unicode_fol_kit.hol.lean import to_lean_modal_k
    text = to_lean_modal_k(MODAL)
    assert "(∀ w1 : World, R w0 w1 → True)" in text
    assert "(¬ False)" in text
    # no valuation axiom for either constant
    assert [ln for ln in text.splitlines() if ln.startswith("axiom") and "→ Prop" in ln
            and ln != "axiom R : World → World → Prop"] == []


def test_goedel_embedding_of_intuitionistic_logic():
    from unicode_fol_kit.hol.intuitionistic import to_thf_intuitionistic, to_isabelle_intuitionistic
    thf = to_thf_intuitionistic(Implies(F, P))
    assert "( ^ [W: mu] : $false )" in thf
    isabelle = to_isabelle_intuitionistic(Implies(F, P))
    assert r"(\<lambda>_. False)" in isabelle
    # the constant is not declared as a proposition of the theory
    assert [ln for ln in isabelle.splitlines() if ln.startswith("consts ") and "False" in ln] == []


def test_conditional_exports():
    from unicode_fol_kit.hol.isabelle_conditional import to_isabelle_conditional, to_thf_conditional
    formula = Would(F, P)
    assert "$false" in to_thf_conditional(formula)
    assert "False" in to_isabelle_conditional(formula)


def test_tptp_ncl_writes_the_tptp_constants():
    from unicode_fol_kit.atp.tptp_ncl import to_tptp_ncl
    assert "([.] $true => <.> ~($false))" in to_tptp_ncl(MODAL)


# ---------------------------------------------------------------------------
# First-order interchange formats
# ---------------------------------------------------------------------------

def test_smtlib_and_prover9_and_tptp():
    from unicode_fol_kit.atp.z3_input import to_smtlib
    assert "(=> (and P true) (not false))" in to_smtlib(CLASSICAL)
    assert CLASSICAL.to_prover9() == '(("P" & $T) -> -($F))'
    assert CLASSICAL.to_tptp() == "((p & $true) => ~($false))"


def test_casl_writes_its_own_constants_and_declares_nothing_for_them():
    from unicode_fol_kit.fol.casl_export import formula_to_casl, to_casl_spec
    # a binary connective's left operand that is itself a connective is wrapped, a
    # `not` of an atom is bare: (P /\ true) => not false
    assert formula_to_casl(CLASSICAL) == "(P /\\ true) => not false"
    spec = to_casl_spec([CLASSICAL])
    assert "preds P : ()" in spec
    assert "$true" not in spec and "$false" not in spec
    assert "true" in spec and "false" in spec


def test_casl_constant_alone():
    from unicode_fol_kit.fol.casl_export import formula_to_casl
    assert formula_to_casl(T) == "true"
    assert formula_to_casl(F) == "false"


# ---------------------------------------------------------------------------
# Targets that refuse
# ---------------------------------------------------------------------------

def test_prolog_export_refuses_the_constants():
    from unicode_fol_kit.fol.prolog_export import formula_to_prolog_clause, PrologExportError
    with pytest.raises(PrologExportError) as info:
        formula_to_prolog_clause(Implies(And(P, T), Atom("Q", ())))
    assert "$true" in str(info.value)
    with pytest.raises(PrologExportError):
        formula_to_prolog_clause(Implies(P, F))
    # an ordinary clause is unchanged
    assert formula_to_prolog_clause(Implies(P, Atom("Q", ()))) == "q :- p."


def test_nanocop_export_refuses_the_constants():
    from unicode_fol_kit.atp.nanocop_backend import to_nanocop
    with pytest.raises(NotImplementedError) as info:
        to_nanocop(MODAL)
    assert "nanocop" in str(info.value) and "$true" in str(info.value)
    assert to_nanocop(Implies(P, P)) == "f( (p => p) ).\n"


def test_deep_embeddings_refuse_the_constants():
    from unicode_fol_kit.hol.deepshallow._common import AtomConsts
    from unicode_fol_kit.hol.deepshallow.modal import modal_to_deep
    from unicode_fol_kit.hol.deepshallow.intuitionistic import int_to_deep
    from unicode_fol_kit.hol.deepshallow.relevant import rel_to_deep
    from unicode_fol_kit.hol.deepshallow.qml import qml_to_deep
    for convert in (modal_to_deep, int_to_deep, rel_to_deep):
        for constant in (T, F):
            with pytest.raises(NotImplementedError) as info:
                convert(Implies(P, constant), AtomConsts())
            message = str(info.value)
            assert constant.predicate in message
            assert "no agreed reading" in message
            assert "constructors" in message
    with pytest.raises(NotImplementedError) as info:
        qml_to_deep(Implies(P, T), AtomConsts(), AtomConsts())
    assert "$true" in str(info.value)


def test_deep_embedding_of_ordinary_letters_is_unchanged():
    from unicode_fol_kit.hol.deepshallow._common import AtomConsts
    from unicode_fol_kit.hol.deepshallow.intuitionistic import int_to_deep
    assert int_to_deep(Implies(P, P), AtomConsts()).startswith("(ImpD")


def test_relevant_isabelle_and_thf_exports_refuse_the_constants():
    from unicode_fol_kit.hol.isabelle_relevant import to_isabelle_relevant, to_thf_relevant
    for export in (to_isabelle_relevant, to_thf_relevant):
        with pytest.raises(TypeError) as info:
            export(Implies(P, T))
        assert "$true" in str(info.value)
        assert "additive" in str(info.value)


def test_substructural_isabelle_exports_refuse_the_constants():
    from unicode_fol_kit.hol.isabelle_substructural import to_isabelle_ill, to_isabelle_lambek
    with pytest.raises(NotImplementedError) as info:
        to_isabelle_ill([P], T)
    assert "$true" in str(info.value) and "linear" in str(info.value)
    with pytest.raises(NotImplementedError) as info:
        to_isabelle_lambek([P], T)
    assert "$true" in str(info.value) and "Lambek" in str(info.value)


# ---------------------------------------------------------------------------
# The bounded finite-domain encodings keep refusing by name
# ---------------------------------------------------------------------------

def test_the_answer_set_encoding_refuses_the_constants_by_name():
    from unicode_fol_kit.api import prove
    from unicode_fol_kit.atp.protocol import _REGISTRY
    if not _REGISTRY["clingo"].available():
        pytest.skip("clingo is not installed here")
    verdict = prove(T, [], backends=["clingo"], logic="fol")
    assert verdict.status == "unknown"
    assert "$true" in str(verdict.detail)
