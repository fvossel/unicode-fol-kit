"""Hand-checked structural + faithfulness tests for the Isabelle modal emitter.

These assert the emitted Isabelle/HOL theory is structurally well-formed (balanced
parens / quotes / cartouches, a *real* uncommented lemma), that every lifted
operator is defined exactly as the corresponding Kripke clause in
``unicode_logic_kit.semantics.kripke.satisfies_modal`` (box = universal over the
right relation, diamond = existential, agent-indexed rk/rb, existsAt-guarded
quantifiers), and that the agent-indexed epistemic relation shows up for K_x.

The import path assumes the module lands at ``unicode_logic_kit.hol.isabelle_modal``;
adjust the import if the parent integrates it elsewhere.
"""

import re
import uuid

import pytest

from unicode_logic_kit.hol.isabelle_modal import (
    to_isabelle_modal, isabelle_modal_theory, ISABELLE_TACTICS, modal_axiom_names,
)

from unicode_logic_kit.fol.nodes import (
    Variable, Constant, Function, Atom, Not, And, Or, Implies, Iff, Xor, Quantifier,
    Box, Diamond, Knows, Believes, Obligatory, Permitted,
    Always, Eventually, Next, Until, Since, SortedQuantifier,
)

from unicode_logic_kit.fol.qml import qml_is_valid
from unicode_logic_kit.hol.isabelle_runner import isabelle_available
from unicode_logic_kit.hol.isabelle_runner import check_theory


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
    # Agent-indexed relation rk : e => i => i => bool must be present (the
    # entity type is MONOMORPHIC: a polymorphic 'a would give every occurrence
    # its own type instance and falsify the agent-K axiom).
    assert re.search(r"consts rk :: \"e \\<Rightarrow> i \\<Rightarrow> i \\<Rightarrow> bool\"", thy), thy
    assert "abbreviation knows" in thy
    # knows is applied with the agent term x in the lifted body.
    assert "(knows x " in thy
    # mforall is used for the object quantifier (existsAt-guarded).
    assert "abbreviation mforall" in thy
    assert "existsAt x w" in thy


def test_doxastic_agent_indexed():
    thy = to_isabelle_modal(Believes(alice, P))
    assert re.search(r"consts rb :: \"e \\<Rightarrow> i \\<Rightarrow> i \\<Rightarrow> bool\"", thy), thy
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
    # binary predicate -> e => e => i => bool
    assert re.search(r"consts likes :: \"e \\<Rightarrow> e \\<Rightarrow> i \\<Rightarrow> bool\"", thy), thy
    # the constant alice is typed e
    assert re.search(r"consts alice :: \"e\"", thy), thy


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
# Binary interval operators Until / Since (inductive least fixpoints over n).
# --------------------------------------------------------------------------- #

def test_until_emits_inductive_muntil():
    thy = to_isabelle_modal(Until(P, Q))
    # Inductive predicate, not a box/diamond abbreviation, with both defining clauses.
    assert 'inductive muntil ::' in thy
    assert 'muntil_base: "psi w \\<Longrightarrow> muntil phi psi w"' in thy
    assert '| muntil_step: "phi w \\<Longrightarrow> n w v \\<Longrightarrow> muntil phi psi v' in thy
    # The lemma body uses the lifted predicate on the two operands.
    assert '(muntil p q)' in thy
    # Until reads the one-step relation n, so n is declared even without Next.
    assert 'consts n ::' in thy
    # ...but the mnext abbreviation is only for Next, which is absent here.
    assert 'mnext' not in thy
    assert thy.rstrip().endswith("end")


def test_since_emits_inductive_msince_converse_step():
    thy = to_isabelle_modal(Since(P, Q))
    assert 'inductive msince ::' in thy
    assert 'msince_base: "psi w \\<Longrightarrow> msince phi psi w"' in thy
    # Since steps over the CONVERSE of n: the step premise is `n v w`, not `n w v`.
    assert '| msince_step: "phi w \\<Longrightarrow> n v w \\<Longrightarrow> msince phi psi v' in thy
    assert '(msince p q)' in thy
    assert 'consts n ::' in thy
    assert thy.rstrip().endswith("end")


def test_until_with_temporal_links_n_into_t():
    # Until (reads n) mixed with Always/Eventually (read the henceforth t): the n_in_t
    # link axiom must be emitted so t denotes the closure of the SAME one-step relation
    # the path-search Until reads (faithfulness of the Always/Until interplay).
    thy = to_isabelle_modal(Implies(Until(P, Q), Eventually(Q)))
    assert 'inductive muntil ::' in thy
    assert 'consts t ::' in thy
    assert 'n_in_t' in thy
    assert 't_in_nstar' in thy  # temporal_closure default pins t = n** exactly
    assert thy.rstrip().endswith("end")


def test_until_no_longer_rejected():
    # Regression: Until / Since used to raise NotImplementedError; now they emit.
    to_isabelle_modal(Until(P, Q))
    to_isabelle_modal(Since(P, Q))
    to_isabelle_modal(And(Until(P, Q), Next(Since(Q, P))))


@pytest.mark.isabelle_live
@pytest.mark.skipif(
    not isabelle_available(),
    reason="no Isabelle installation found (set UFK_ISABELLE_HOME / ISABELLE_HOME)")
def test_until_since_theory_loads_and_proves_live():
    """The emitted Until/Since theory LOADS in real Isabelle, and the strong-Until
    base case Q -> (P U Q) is provable through the emitted inductive scaffold."""
    # (1) A mixed temporal theory (Until + Since + Next + Always + Diamond) loads.
    mixed = And(Until(P, Q), And(Since(P, Q), And(Next(P), And(Always(P), Diamond(Q)))))
    thy = isabelle_modal_theory(mixed, frame="S4", theory_name="MixedTemporalLoad")
    r = check_theory(thy, "MixedTemporalLoad", session_timeout=300)
    assert r.ok, r.output[-2000:]
    # (2) Q -> (P U Q) is valid (Until base clause) and proves via muntil.intros.
    thy2 = isabelle_modal_theory(
        Implies(Q, Until(P, Q)), theory_name="UntilBaseValid",
        proof="  using muntil.intros by blast")
    r2 = check_theory(thy2, "UntilBaseValid", session_timeout=300)
    assert r2.ok, r2.output[-2000:]


@pytest.mark.isabelle_live
@pytest.mark.skipif(
    not isabelle_available(),
    reason="no Isabelle installation found (set UFK_ISABELLE_HOME / ISABELLE_HOME)")
def test_non_empty_sort_axiom_is_what_closes_the_sorted_schema_live():
    """Real Isabelle confirms the sort non-emptiness axiom is load-bearing.

    ``∀x:Human P(x) → ∃x:Human P(x)`` is what ``api.prove`` calls valid, so the
    emitted theory has to close it too or this route disagrees with the
    classical one on a modal-free sorted formula. Relativization alone does not
    get there -- the guard is just an atom, and nothing says it holds of
    anything -- so both directions are checked: WITH the axiom in scope blast
    closes the lemma, WITHOUT it blast fails. The second half is the part that
    would silently rot if the axiom were ever dropped again.
    """
    f = SortedQuantifier("∀", x, "Human", Atom("P", [x]))
    g = SortedQuantifier("∃", x, "Human", Atom("P", [x]))
    schema = Implies(f, g)

    names = modal_axiom_names(schema)
    assert "nonempty_sort0" in names, names
    with_axiom = isabelle_modal_theory(
        schema, theory_name="SortedNonEmptyLive",
        proof="  using " + " ".join(names) + " by blast")
    r = check_theory(with_axiom, "SortedNonEmptyLive", session_timeout=300)
    assert r.ok, r.output[-2000:]

    without_axiom = isabelle_modal_theory(
        schema, theory_name="SortedNoAxiomLive", proof="  by blast")
    r2 = check_theory(without_axiom, "SortedNoAxiomLive", session_timeout=300)
    assert not r2.ok, "blast closed the schema without the axiom — it is not load-bearing"


# --------------------------------------------------------------------------- #
# Errors / unsupported.
# --------------------------------------------------------------------------- #

def test_sorted_quantifier_is_relativized_with_a_non_empty_sort():
    """A sorted quantifier is no longer refused: it is relativized to a guard atom.

    ∀x:Nat A(x) becomes the guarded ∀x (Nat(x) → A(x)) — an ordinary unary
    predicate ``nat`` in the emitted signature — and the sort gets the same
    non-emptiness convention the classical many-sorted routes use
    (``fol._msfl_nodes.nonempty_sort_axioms``), stated per world here because the
    guard is world-relative. Without that axiom the theory would not prove
    ∀x:S P(x) → ∃x:S P(x), which ``api.prove`` calls valid.
    """
    thy = to_isabelle_modal(SortedQuantifier("∀", x, "Nat", Atom("A", [x])))
    assert 'consts nat :: "e \\<Rightarrow> i \\<Rightarrow> bool"' in thy
    assert "mforall (\\<lambda>x. (mimp (nat x) (a x)))" in thy
    assert 'axiomatization where nonempty_sort0: "\\<exists>x. nat x w"' in thy
    assert "nonempty_sort0" in modal_axiom_names(
        SortedQuantifier("∀", x, "Nat", Atom("A", [x])))
    # an unsorted formula gains no such axiom.
    assert "nonempty_sort" not in to_isabelle_modal(Quantifier("∀", x, Atom("A", [x])))


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
    from unicode_logic_kit.hol.isabelle_modal import modal_axiom_names
    assert "t_in_nstar" in modal_axiom_names(ALWAYS_IMP_NEXT)


def test_t_in_nstar_absent_without_temporal_closure():
    # temporal_closure=False opts out of the closure reading, so t is not pinned.
    thy = isabelle_modal_theory(ALWAYS_IMP_NEXT, temporal_closure=False)
    assert "t_in_nstar" not in thy


def test_t_in_nstar_absent_when_no_next():
    # Pure Always (no one-step n): nothing to take the closure of.
    assert "t_in_nstar" not in to_isabelle_modal(Always(P))


def test_temporal_def_form_defines_t_as_rtranclp():
    # temporal_def=True (the runner's refute form): t is DEFINED as rtranclp n and the
    # closure axioms are dropped (they become theorems), so nitpick can build the
    # closure and refute. Audit follow-up #2.
    thy = isabelle_modal_theory(ALWAYS_IMP_NEXT, temporal_def=True)
    assert 'definition t :: "i \\<Rightarrow> i \\<Rightarrow> bool" where "t = rtranclp n"' in thy
    assert "consts t ::" not in thy
    for ax in ("t_refl:", "t_trans:", "n_in_t:", "t_in_nstar"):
        assert ax not in thy, ax


def test_temporal_def_form_is_off_by_default():
    # Default (temporal_def=False, the public exporter + the prove theory): the axiom
    # form is unchanged — consts t pinned to the closure by axioms.
    thy = to_isabelle_modal(ALWAYS_IMP_NEXT)
    assert "consts t ::" in thy and "t_in_nstar" in thy
    assert "definition t ::" not in thy


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


# --------------------------------------------------------------------------- #
# Non-ASCII / digit-leading identifiers (the widened FOL-parser identifier
# grammar's reach into _safe_name/_var_name/_IsaNames.variable). Until this
# regression suite existed, no test anywhere exercised a non-ASCII or
# digit-leading predicate/constant/variable name through this exporter.
# --------------------------------------------------------------------------- #

def test_non_ascii_predicate_and_constants_are_ascii_legal_and_transliterated():
    f = Box(Atom("Świątek", [Constant("świątek"), Constant("2008SummerOlympics")]))
    thy = to_isabelle_modal(f)
    consts_lines = [ln for ln in thy.splitlines() if ln.strip().startswith("consts")]
    lemma_lines = [ln for ln in thy.splitlines() if ln.strip().startswith("lemma")]
    assert all(ln.isascii() for ln in consts_lines + lemma_lines)
    assert _balanced(thy, "(", ")") and _quotes_balanced(thy)
    # hand-computed via constant_name_to_ascii("Świątek")/("świątek") plus the
    # digit-leading 'c_' guard _safe_name applies (no reversible escape scheme
    # for constant_name_to_ascii's own name -- see fol._fol_nodes).
    assert re.search(r"consts u015awiu0105tek ::", thy), thy    # Świątek (predicate)
    assert re.search(r"consts u015bwiu0105tek :: \"e\"", thy), thy  # świątek (constant)
    assert re.search(r"consts c_2008SummerOlympics :: \"e\"", thy), thy  # digit-leading
    assert "u015awiu0105tek u015bwiu0105tek c_2008SummerOlympics" in thy  # the lemma goal
    assert not any("Świątek" in ln or "świątek" in ln for ln in consts_lines + lemma_lines)


def test_non_ascii_variable_is_ascii_legal_and_deduped():
    # A bound variable whose name is itself non-ASCII must come out as an
    # ASCII Isabelle term-variable token (_IsaNames.variable / _var_name),
    # not the raw Unicode letter passed straight through.
    v = Variable("świątek")
    f = Quantifier("∀", v, Atom("Above", [v]))
    thy = to_isabelle_modal(f)
    assert thy.isascii() or all(
        ln.isascii() for ln in thy.splitlines() if ln.strip().startswith("lemma"))
    assert "u015bwiu0105tek" in thy
    assert "świątek" not in thy


# --------------------------------------------------------------------------- #
# Rigid identity.
#
# `=` is Isabelle's own polymorphic `=` over the entity type `e`, lifted under a world
# binder it never uses -- `(\<lambda>_. a = b)` -- so it takes no world argument and cannot
# vary by world; `≠` is `¬(=)`. This is the reading of fol.qml.qml_is_valid. The static
# tests pin the emitted text against hand-derived expected output; the live battery
# (isabelle_live) asks a real Isabelle the same questions qml_is_valid answers.
# --------------------------------------------------------------------------- #

_ea, _eb, _ec = Constant("a"), Constant("b"), Constant("c")


def _id(s, t):
    return Atom("=", [s, t])


def _nid(s, t):
    return Atom("≠", [s, t])


def _Pa(t):
    return Atom("P", [t])


_ef = lambda t: Function("f", [t])           # noqa: E731

_L = "\\<lambda>_."                           # the unused world binder, as emitted
_IALL = {"K": True, "T": True, "S4": True, "S5": True, "KD": True, "KD45": True}
_IBOX_BACK = {"K": False, "T": True, "S4": True, "S5": True, "KD": True, "KD45": True}
_INEVER = {k: False for k in _IALL}

# (id, formula, hand-derived lemma body, validity per frame, the reason)
_ISA_IDENTITY_BATTERY = [
    ("refl", _id(_ea, _ea), f"({_L} a = a)", _IALL, "reflexivity"),
    ("sym", Implies(_id(_ea, _eb), _id(_eb, _ea)),
     f"(mimp ({_L} a = b) ({_L} b = a))", _IALL, "symmetry"),
    ("trans", Implies(And(_id(_ea, _eb), _id(_eb, _ec)), _id(_ea, _ec)),
     f"(mimp (mand ({_L} a = b) ({_L} b = c)) ({_L} a = c))", _IALL, "transitivity"),
    ("necessity", Implies(_id(_ea, _eb), Box(_id(_ea, _eb))),
     f"(mimp ({_L} a = b) (mbox ({_L} a = b)))", _IALL,
     "rigid: no world argument, so it holds at every successor"),
    ("distinctness", Implies(_nid(_ea, _eb), Box(_nid(_ea, _eb))),
     f"(mimp (mnot ({_L} a = b)) (mbox (mnot ({_L} a = b))))", _IALL,
     "≠ is ¬(=), rigid too"),
    ("possible_identity", Implies(Diamond(_id(_ea, _eb)), _id(_ea, _eb)),
     f"(mimp (mdia ({_L} a = b)) ({_L} a = b))", _IALL,
     "a = b does not depend on the world the diamond's witness lives at"),
    ("box_back", Implies(Box(_id(_ea, _eb)), _id(_ea, _eb)),
     f"(mimp (mbox ({_L} a = b)) ({_L} a = b))", _IBOX_BACK,
     "needs a successor-or-self; in K a dead-end world makes the box vacuous"),
    ("leibniz", Implies(_id(_ea, _eb), Iff(_Pa(_ea), _Pa(_eb))),
     f"(mimp ({_L} a = b) (miff (p a) (p b)))", _IALL, "substitutivity"),
    ("leibniz_box", Implies(_id(_ea, _eb), Iff(Box(_Pa(_ea)), Box(_Pa(_eb)))),
     f"(mimp ({_L} a = b) (miff (mbox (p a)) (mbox (p b))))", _IALL,
     "the same two objects, so the same boxed predicate"),
    ("contingent", _id(_ea, _eb), f"({_L} a = b)", _INEVER,
     "two constants may denote two objects"),
    ("contingent_neg", Not(_id(_ea, _eb)), f"(mnot ({_L} a = b))", _INEVER,
     "two constants may denote one object"),
    ("congruence", Implies(_id(_ea, _eb), _id(_ef(_ea), _ef(_eb))),
     f"(mimp ({_L} a = b) ({_L} (f a) = (f b)))", _IALL, "functions respect identity"),
]
_ISA_IDS = [row[0] for row in _ISA_IDENTITY_BATTERY]


def _lemma_body(thy: str) -> str:
    m = re.search(r'lemma modal_goal: "\\<lfloor> (.*) \\<rfloor>"', thy)
    assert m, thy
    return m.group(1)


def test_identity_is_native_hol_equality_not_a_declared_predicate():
    thy = to_isabelle_modal(Atom("=", [alice, Constant("bob")]))
    assert _lemma_body(thy) == "(\\<lambda>_. alice = bob)"
    assert "feq" not in thy and "fneq" not in thy
    # the two entities and nothing else: identity declares no predicate constant
    assert sorted(re.findall(r"^consts (\w+) ::", thy, re.M)) == ["alice", "bob"]
    assert _balanced(thy, "(", ")") and _quotes_balanced(thy)


@pytest.mark.parametrize("name, formula, body, validity, why", _ISA_IDENTITY_BATTERY,
                         ids=_ISA_IDS)
def test_identity_lemma_text_is_pinned(name, formula, body, validity, why):
    thy = to_isabelle_modal(formula)
    assert _lemma_body(thy) == body
    assert "feq" not in thy and "fneq" not in thy
    # exactly the constants, function symbols and (non-identity) predicates it uses
    declared = set(re.findall(r"^consts (\w+) ::", thy, re.M)) - {"r"}
    used = {n.name for n in formula.walk() if isinstance(n, (Constant, Function))}
    used |= {n.predicate.lower() for n in formula.walk()
             if isinstance(n, Atom) and n.predicate not in ("=", "≠")}
    assert declared == used, (name, declared, used)
    # ... and the axioms in scope for the proof are the frame's, identity adds none
    assert modal_axiom_names(formula, frame="S4") == (
        ["r_refl", "r_trans"]
        if any(isinstance(n, (Box, Diamond)) for n in formula.walk()) else [])


def test_identity_and_the_thf_export_lower_the_same_atoms_the_same_way():
    # Agreement between the two HOL exporters, atom for atom: one world-free equality
    # per identity atom after lowering ≠ to ¬(=) in both, none where there is none.
    from unicode_logic_kit.hol.thf_modal import to_thf_modal_full
    for name, formula, body, validity, why in _ISA_IDENTITY_BATTERY:
        thy, thf = to_isabelle_modal(formula), to_thf_modal_full(formula)
        goal = [ln for ln in thf.splitlines() if ln.startswith("thf(goal,")][0]
        assert thy.count(_L) == goal.count("( meq @"), name
    plain = Implies(Box(_Pa(_ea)), _Pa(_ea))
    assert _L not in to_isabelle_modal(plain)
    assert "( meq @" not in to_thf_modal_full(plain)


def test_inequality_is_lowered_to_negated_identity():
    thy = to_isabelle_modal(_nid(_ea, _eb))
    assert _lemma_body(thy) == f"(mnot ({_L} a = b))"
    assert "noteq" not in thy and "fneq" not in thy
    assert thy == to_isabelle_modal(Not(_id(_ea, _eb)))      # literally ¬(a = b)


def test_identity_world_binder_is_anonymous_so_a_variable_called_w_is_not_captured():
    w = Variable("w")
    thy = to_isabelle_modal(Quantifier("∀", w, _id(w, w)))
    assert _lemma_body(thy) == f"(mforall (\\<lambda>w. ({_L} w = w)))"
    thy2 = to_isabelle_modal(Quantifier("∀", w, Quantifier("∃", x, _id(w, x))))
    assert _lemma_body(thy2) == (
        f"(mforall (\\<lambda>w. (mexists (\\<lambda>x. ({_L} w = x)))))")


def test_user_predicate_called_feq_stays_unique_next_to_identity():
    f = And(Atom("feq", [_ea]), And(Atom("fneq", [_ea, _eb]), _id(_ea, _eb)))
    thy = to_isabelle_modal(f)
    consts = re.findall(r"^consts (\w+) ::", thy, re.M)
    assert len(consts) == len(set(consts))
    assert f"({_L} a = b)" in thy
    assert sum(c.startswith("feq") for c in consts) == 1
    assert sum(c.startswith("fneq") for c in consts) == 1


def test_non_binary_identity_is_refused_like_qml_refuses_it():
    for atom in (Atom("=", [_ea]), Atom("=", [_ea, _eb, _ec]), Atom("≠", [_ea])):
        with pytest.raises(ValueError, match="exactly two terms"):
            to_isabelle_modal(Box(atom))
        with pytest.raises(ValueError, match="exactly two terms"):
            modal_axiom_names(Box(atom))


def test_identity_adds_no_axioms_and_needs_no_quantifier_block():
    assert modal_axiom_names(Implies(_id(_ea, _eb), Box(_id(_ea, _eb))), frame="T") == ["r_refl"]
    assert modal_axiom_names(_id(_ea, _ea)) == []
    # the existence predicate appears only under a quantifier, identity or not
    assert "existsAt" not in to_isabelle_modal(Implies(_id(_ea, _eb), Box(_id(_ea, _eb))))
    assert "existsAt" in to_isabelle_modal(Quantifier("∃", x, _id(x, _ea)))


# --- live: a real Isabelle answers the same questions qml_is_valid answers --------

_LIVE_SKIP = pytest.mark.skipif(
    not isabelle_available(),
    reason="no Isabelle installation found (set UFK_ISABELLE_HOME / ISABELLE_HOME)")


def _isabelle_verdict(formula, frame="K", mode="constant") -> str:
    """'valid' if a proof battery closes the lemma; 'invalid' if nitpick finds a genuine
    countermodel; 'quasi-invalid' if the countermodel is only quasi-genuine; else
    'unknown'. The runner's own two steps (isabelle_decide_modal) without its Kripke-
    witness step, which cannot evaluate an identity atom (and without its
    ``expect = genuine`` being the last word: under a varying domain nitpick reports
    EVERY refutation as quasi-genuine -- Barcan's formula included -- because it cannot
    use the ``nonempty_dom`` axiom, so a genuine-only runner answers 'unknown' there)."""
    axioms = modal_axiom_names(formula, mode=mode, frame=frame)
    tok = "G" + uuid.uuid4().hex[:8]
    using = ("  using " + " ".join(axioms) + "\n") if axioms else ""
    proof = using + "  by (blast | force | fastforce | auto)"
    thy = isabelle_modal_theory(formula, mode=mode, frame=frame, tactic="oops",
                                theory_name=tok, proof=proof)
    if check_theory(thy, tok, session_timeout=90).ok:
        return "valid"
    for expect, verdict in (("genuine", "invalid"), ("quasi_genuine", "quasi-invalid")):
        tok = "G" + uuid.uuid4().hex[:8]
        nit = f"  nitpick[card i = 1-3, timeout = 40, expect = {expect}]\n  oops"
        thy = isabelle_modal_theory(formula, mode=mode, frame=frame, tactic="oops",
                                    theory_name=tok, proof=nit)
        if check_theory(thy, tok, session_timeout=90, wall_timeout=300).ok:
            return verdict
    return "unknown"


def _live_cases():
    """The battery on K, plus the one formula whose verdict depends on the frame."""
    for name, formula, body, validity, why in _ISA_IDENTITY_BATTERY:
        yield pytest.param(formula, "K", validity["K"], id=f"{name}-K")
    for frame in ("T", "S4", "S5"):
        yield pytest.param(_ISA_IDENTITY_BATTERY[6][1], frame, True, id=f"box_back-{frame}")


@pytest.mark.isabelle_live
@_LIVE_SKIP
@pytest.mark.parametrize("formula, frame, expected_valid", list(_live_cases()))
def test_rigid_identity_battery_live_matches_qml_is_valid(formula, frame, expected_valid):
    assert qml_is_valid(formula, frame=frame) is expected_valid       # hand == qml
    assert _isabelle_verdict(formula, frame=frame) == (
        "valid" if expected_valid else "invalid")                     # ... == Isabelle


@pytest.mark.isabelle_live
@_LIVE_SKIP
@pytest.mark.parametrize("mode, exists_valid", [("constant", True), ("varying", False)])
def test_identity_is_not_existence_guarded_live(mode, exists_valid):
    """`a = a` is a theorem even where `a` does not exist; `∃x (x = a)` is one only when
    every object exists everywhere (qml's documented choice for varying domains).
    Under ``varying`` nitpick's countermodel to the second is quasi-genuine (see
    :func:`_isabelle_verdict`); it is also what the proof battery fails to prove."""
    exists = Quantifier("∃", x, _id(x, _ea))
    assert qml_is_valid(_id(_ea, _ea), mode=mode) is True
    assert _isabelle_verdict(_id(_ea, _ea), mode=mode) == "valid"
    assert qml_is_valid(exists, mode=mode) is exists_valid
    got = _isabelle_verdict(exists, mode=mode)
    if exists_valid:
        assert got == "valid"
    else:
        assert got in ("invalid", "quasi-invalid"), got
