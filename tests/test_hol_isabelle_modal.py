"""Hand-checked structural + faithfulness tests for the Isabelle modal emitter.

These assert the emitted Isabelle/HOL theory is structurally well-formed (balanced
parens / quotes / cartouches, a *real* uncommented lemma), that every lifted
operator is defined exactly as the corresponding Kripke clause in
``unicode_fol_kit.semantics.kripke.satisfies_modal`` (box = universal over the
right relation, diamond = existential, agent-indexed rk/rb, existsAt-guarded
quantifiers), and that the agent-indexed epistemic relation shows up for K_x.

The import path assumes the module lands at ``unicode_fol_kit.hol.isabelle_modal``;
adjust the import if the parent integrates it elsewhere.
"""

import re
import pytest

from unicode_fol_kit.hol.isabelle_modal import (
    to_isabelle_modal, isabelle_modal_theory, ISABELLE_TACTICS,
)

from unicode_fol_kit.fol.nodes import (
    Variable, Constant, Atom, Not, And, Or, Implies, Iff, Xor, Quantifier,
    Box, Diamond, Knows, Believes, Obligatory, Permitted,
    Always, Eventually, Next, Until, SortedQuantifier,
)


def _balanced(s: str, op: str, cl: str) -> bool:
    depth = 0
    for ch in s:
        if ch == op:
            depth += 1
        elif ch == cl:
            depth -= 1
            if depth < 0:
                return False
    return depth == 0


def _quotes_balanced(s: str) -> bool:
    # Isabelle inner terms are wrapped in double quotes; count must be even.
    return s.count('"') % 2 == 0


# Common formulas.
P = Atom("P", [])
Q = Atom("Q", [])
x = Variable("x")
alice = Constant("alice")
BOX_P_IMP_P = Implies(Box(P), P)           # T axiom
BARCAN = Implies(Diamond(Quantifier("∃", x, Atom("A", [x]))),
                 Quantifier("∃", x, Diamond(Atom("A", [x]))))
# ∀x (Student(x) → K_x φ): agent-indexed knowledge with a bound object agent.
STUDENT_KNOWS = Quantifier("∀", x,
                           Implies(Atom("Student", [x]),
                                   Knows(x, Atom("Smart", [x]))))


# --------------------------------------------------------------------------- #
# Structural skeleton.
# --------------------------------------------------------------------------- #

def test_theory_skeleton_present():
    thy = to_isabelle_modal(BOX_P_IMP_P, frame="T")
    assert thy.startswith("theory ModalEmbedding")
    assert "imports Main" in thy
    assert "\nbegin\n" in thy
    assert thy.rstrip().endswith("end")
    assert "typedecl i" in thy


def test_real_lemma_not_a_comment():
    thy = to_isabelle_modal(BOX_P_IMP_P, frame="T")
    # A genuine lemma line exists, not commented out.
    m = re.search(r'^lemma\s+modal_goal:\s+"\\<lfloor>.*\\<rfloor>"$', thy, re.M)
    assert m is not None, thy
    # The lemma line is not inside an Isabelle (* ... *) comment.
    lemma_line = m.group(0)
    assert "(*" not in lemma_line and "*)" not in lemma_line
    # And it is NOT a to_unicode_str dump: the box of the source uses □, the
    # emitted body must use the lifted operator mbox/mimp, never the raw glyph.
    body = lemma_line
    assert "mbox" in body and "mimp" in body
    assert "□" not in body and "→" not in body


def test_balanced_parens_and_quotes_all_examples():
    for f, kw in [
        (BOX_P_IMP_P, dict(frame="T")),
        (BARCAN, dict(mode="increasing", frame="S5")),
        (STUDENT_KNOWS, dict()),
        (Believes(alice, P), dict()),
        (And(Obligatory(P), Permitted(Q)), dict(frame="KD")),
        (Always(Implies(P, Eventually(Q))), dict()),
        (Next(P), dict()),
        (Xor(P, Q), dict()),
    ]:
        thy = to_isabelle_modal(f, **kw)
        assert _balanced(thy, "(", ")"), f
        assert _quotes_balanced(thy), f
        # angle-bracket cartouches \<open> ... \<close> count balanced
        assert thy.count("\\<open>") == thy.count("\\<close>")


# --------------------------------------------------------------------------- #
# Operator definitions appear iff used.
# --------------------------------------------------------------------------- #

def test_core_operators_always_defined():
    thy = to_isabelle_modal(P)
    for op in ["mnot", "mand", "mor", "mimp", "miff", "mvalid"]:
        assert f"abbreviation {op}" in thy, op


def test_alethic_block():
    thy = to_isabelle_modal(Box(P), frame="S4")
    assert 'consts r ::' in thy
    assert "abbreviation mbox" in thy
    assert "abbreviation mdia" in thy
    # S4 = refl + trans frame axioms.
    assert "r_refl:" in thy
    assert "r_trans:" in thy
    assert "r_sym:" not in thy


def test_agent_indexed_epistemic_relation():
    thy = to_isabelle_modal(STUDENT_KNOWS)
    # Agent-indexed relation rk : 'a => i => i => bool must be present.
    assert re.search(r"consts rk :: \"'a \\<Rightarrow> i \\<Rightarrow> i \\<Rightarrow> bool\"", thy), thy
    assert "abbreviation knows" in thy
    # knows is applied with the agent term x in the lifted body.
    assert "(knows x " in thy
    # mforall is used for the object quantifier (existsAt-guarded).
    assert "abbreviation mforall" in thy
    assert "existsAt x w" in thy


def test_doxastic_agent_indexed():
    thy = to_isabelle_modal(Believes(alice, P))
    assert re.search(r"consts rb :: \"'a \\<Rightarrow> i \\<Rightarrow> i \\<Rightarrow> bool\"", thy), thy
    assert "abbreviation believes" in thy
    assert "(believes alice " in thy


def test_deontic_block_and_serial_axiom():
    thy = to_isabelle_modal(And(Obligatory(P), Permitted(Q)), frame="KD")
    assert "abbreviation obl" in thy
    assert "abbreviation perm" in thy
    assert "d_serial:" in thy
    assert "(obl " in thy and "(perm " in thy


def test_temporal_block_closure_axioms():
    thy = to_isabelle_modal(Always(Eventually(P)))
    assert "abbreviation malways" in thy
    assert "abbreviation meventually" in thy
    # henceforth closure: t reflexive + transitive.
    assert "t_refl:" in thy
    assert "t_trans:" in thy


def test_temporal_closure_toggle_off():
    thy = isabelle_modal_theory(Always(P), temporal_closure=False)
    assert "abbreviation malways" in thy
    assert "t_refl:" not in thy
    assert "t_trans:" not in thy


def test_next_one_step_relation():
    thy = to_isabelle_modal(Next(P))
    assert 'consts n ::' in thy
    assert "abbreviation mnext" in thy
    assert "(mnext " in thy
    # Next does not pull in the temporal closure relation t.
    assert "consts t ::" not in thy


def test_unused_blocks_absent():
    thy = to_isabelle_modal(Box(P))  # purely alethic propositional
    assert "consts rk" not in thy
    assert "consts rb" not in thy
    assert "consts d ::" not in thy
    assert "consts t ::" not in thy
    assert "mforall" not in thy  # no quantifier


# --------------------------------------------------------------------------- #
# Domain regimes.
# --------------------------------------------------------------------------- #

def test_constant_domain_axiom():
    thy = to_isabelle_modal(Quantifier("∀", x, Atom("A", [x])), mode="constant")
    assert "const_dom:" in thy
    assert "existsAt" in thy


def test_increasing_domain_axiom():
    thy = to_isabelle_modal(Quantifier("∀", x, Atom("A", [x])), mode="increasing")
    assert "cumul_dom:" in thy
    assert "nonempty_dom:" in thy


def test_decreasing_domain_axiom():
    thy = to_isabelle_modal(BARCAN, mode="decreasing", frame="K")
    assert "decr_dom:" in thy


# --------------------------------------------------------------------------- #
# Signature.
# --------------------------------------------------------------------------- #

def test_predicate_signature_typing():
    thy = to_isabelle_modal(Atom("Likes", [alice, Variable("y")]))
    # binary predicate -> 'a => 'a => i => bool
    assert re.search(r"consts likes :: \"'a \\<Rightarrow> 'a \\<Rightarrow> i \\<Rightarrow> bool\"", thy), thy
    # the constant alice is typed 'a
    assert re.search(r"consts alice :: \"'a\"", thy), thy


def test_equality_uninterpreted_alias():
    thy = to_isabelle_modal(Atom("=", [alice, Constant("bob")]))
    assert "feq" in thy
    # not primitive HOL equality lifted as identity; feq is a declared const.
    assert re.search(r"consts feq ::", thy), thy


# --------------------------------------------------------------------------- #
# Tactics.
# --------------------------------------------------------------------------- #

def test_tactic_metis():
    thy = to_isabelle_modal(BOX_P_IMP_P, frame="T", tactic="metis")
    assert "by (metis" in thy


def test_tactic_sledgehammer_default_loads_with_oops():
    thy = to_isabelle_modal(BOX_P_IMP_P, frame="T")
    assert "sledgehammer" in thy
    assert "oops" in thy


def test_all_tactics_emit():
    for t in ISABELLE_TACTICS:
        thy = to_isabelle_modal(P, tactic=t)
        assert thy.rstrip().endswith("end")


# --------------------------------------------------------------------------- #
# Errors / unsupported.
# --------------------------------------------------------------------------- #

def test_until_rejected():
    with pytest.raises(NotImplementedError):
        to_isabelle_modal(Until(P, Q))


def test_sorted_quantifier_rejected():
    with pytest.raises(NotImplementedError):
        to_isabelle_modal(SortedQuantifier("∀", x, "Nat", Atom("A", [x])))


def test_bad_frame():
    with pytest.raises(ValueError):
        to_isabelle_modal(P, frame="Z9")


def test_bad_mode():
    with pytest.raises(ValueError):
        to_isabelle_modal(P, mode="weird")


def test_bad_tactic():
    with pytest.raises(ValueError):
        to_isabelle_modal(P, tactic="hammertime")


# --------------------------------------------------------------------------- #
# Faithfulness to satisfies_modal: structural shape of each operator matches the
# Kripke clause (universal box over the right relation, existential diamond, etc.)
# --------------------------------------------------------------------------- #

def test_box_is_universal_over_r():
    thy = to_isabelle_modal(Box(P))
    assert "mbox \\<phi> \\<equiv> \\<lambda>w. \\<forall>v. r w v \\<longrightarrow> \\<phi> v" in thy


def test_diamond_is_existential_over_r():
    thy = to_isabelle_modal(Diamond(P))
    assert "mdia \\<phi> \\<equiv> \\<lambda>w. \\<exists>v. r w v \\<and> \\<phi> v" in thy


def test_knows_universal_agent_indexed():
    thy = to_isabelle_modal(Knows(alice, P))
    assert "knows a \\<phi> \\<equiv> \\<lambda>w. \\<forall>v. rk a w v \\<longrightarrow> \\<phi> v" in thy


def test_permitted_existential_over_d():
    thy = to_isabelle_modal(Permitted(P))
    assert "perm \\<phi> \\<equiv> \\<lambda>w. \\<exists>v. d w v \\<and> \\<phi> v" in thy


def test_mvalid_truth_at_every_world():
    thy = to_isabelle_modal(P)
    assert "\\<lfloor>\\<phi>\\<rfloor> \\<equiv> \\<forall>w. \\<phi> w" in thy


# --------------------------------------------------------------------------- #
# Faithfulness regression: Always(P) -> Next(P) is VALID for satisfies_modal
# (Next reads the one-step "temporal" relation; Always closes over its
# reflexive-transitive closure, so every one-step successor is henceforth-
# reachable). The emitted theory decouples n (Next) and t (Always) unless the
# linking axiom n_in_t : "n w v ==> t w v" is present. Without it,
# Implies(Always(P), Next(P)) is FALSE in a model of the emitted theory,
# violating the docstring's faithfulness guarantee.
# --------------------------------------------------------------------------- #

ALWAYS_IMP_NEXT = Implies(Always(P), Next(P))


def test_n_in_t_axiom_present_when_next_cooccurs_with_always():
    thy = to_isabelle_modal(ALWAYS_IMP_NEXT)
    # Both relations are declared...
    assert "consts t ::" in thy
    assert "consts n ::" in thy
    # ...and the linking axiom couples them (one-step => henceforth-reachable).
    assert re.search(
        r'axiomatization where n_in_t: "n w v \\<Longrightarrow> t w v"', thy), thy


def test_n_in_t_axiom_present_with_eventually():
    # Eventually also declares t; n_in_t must still link them.
    thy = to_isabelle_modal(Implies(Eventually(P), Next(P)))
    assert "consts t ::" in thy
    assert "consts n ::" in thy
    assert "n_in_t:" in thy


def test_n_in_t_axiom_present_even_without_temporal_closure():
    # The relation t is declared whenever Always/Eventually occur, independently
    # of temporal_closure; the linking axiom must fire on the relations being
    # declared, not on the refl+trans closure axioms.
    thy = isabelle_modal_theory(ALWAYS_IMP_NEXT, temporal_closure=False)
    assert "t_refl:" not in thy and "t_trans:" not in thy
    assert "n_in_t:" in thy


def test_n_in_t_absent_when_next_alone():
    # Pure Next: no temporal relation t, so nothing to link.
    thy = to_isabelle_modal(Next(P))
    assert "consts t ::" not in thy
    assert "n_in_t:" not in thy


def test_n_in_t_absent_when_always_alone():
    # Pure Always: no one-step relation n, so nothing to link.
    thy = to_isabelle_modal(Always(P))
    assert "consts n ::" not in thy
    assert "n_in_t:" not in thy


def test_n_in_t_theory_still_structurally_wellformed():
    # The linking axiom must not break loadability invariants.
    thy = to_isabelle_modal(ALWAYS_IMP_NEXT)
    assert _balanced(thy, "(", ")")
    assert _quotes_balanced(thy)
    assert thy.count("\\<open>") == thy.count("\\<close>")
    assert thy.rstrip().endswith("end")
    # Exactly one declaration of n and of t (no duplicate consts).
    assert thy.count("consts n ::") == 1
    assert thy.count("consts t ::") == 1


def test_t_in_nstar_axiom_pins_closure_when_next_cooccurs_with_always():
    # t must be the reflexive-transitive CLOSURE of n (t = n**), not merely a refl-trans
    # superset — else satisfies_modal-valid temporal induction is spuriously refutable
    # (a false INVALID under the runner). The closure-pinning axiom t ⊆ rtranclp n is
    # emitted when Always/Eventually co-occur with Next under temporal_closure. Audit
    # regression for the false-INVALID-from-too-weak-axioms finding.
    thy = to_isabelle_modal(ALWAYS_IMP_NEXT)
    assert ('axiomatization where t_in_nstar: "t w v \\<Longrightarrow> rtranclp n w v"'
            in thy), thy
    from unicode_fol_kit.hol.isabelle_modal import modal_axiom_names
    assert "t_in_nstar" in modal_axiom_names(ALWAYS_IMP_NEXT)


def test_t_in_nstar_absent_without_temporal_closure():
    # temporal_closure=False opts out of the closure reading, so t is not pinned.
    thy = isabelle_modal_theory(ALWAYS_IMP_NEXT, temporal_closure=False)
    assert "t_in_nstar" not in thy


def test_t_in_nstar_absent_when_no_next():
    # Pure Always (no one-step n): nothing to take the closure of.
    assert "t_in_nstar" not in to_isabelle_modal(Always(P))


def test_distinct_predicates_not_collapsed():
    # Ab / ab sanitise to the same name; they MUST get distinct consts, else the
    # non-valid □Ab → □ab collapses to the tautology □ab → □ab (soundness) and Isabelle
    # would also reject the duplicate consts declaration. Regression.
    thy = to_isabelle_modal(Implies(Box(Atom("Ab", [])), Box(Atom("ab", []))))
    consts = [ln.split()[1] for ln in thy.splitlines()
              if ln.strip().startswith("consts") and "::" in ln]
    assert len(consts) == len(set(consts))                 # no duplicate consts
    ab_family = sorted(c for c in consts if c == "ab" or c.startswith("ab_"))
    assert ab_family == ["ab", "ab_2"]                     # two distinct ab-symbols
    assert thy.count("(mbox ab)") < 2                      # not collapsed to a tautology
