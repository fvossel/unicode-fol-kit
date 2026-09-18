"""The two third-order HOL exporters: classical, and the shallow modal embedding.

Both take a predicate whose argument is a property and hand a HOL prover the
same thing one type higher — so these tests are about the TYPES more than the
syntax. What each argument slot holds is inferred, and getting it wrong would
produce a theory that typechecks and means something else, which is the failure
mode worth pinning.

The proof-level checks live in ``test_goedel.py``; here nothing runs a prover.
"""

import pytest

from unicode_fol_kit import MSFLParser
from unicode_fol_kit.fol.frames import UnsupportedFrameCondition
from unicode_fol_kit.hol.ho_modal import (
    HoAxiom, HoGoal, ho_modal_definitions, isabelle_ho_modal_theory,
    to_isabelle_ho_modal, to_thf_ho_modal,
)
from unicode_fol_kit.hol._ho_common import UnsupportedHigherOrderNode, rename_apart
from unicode_fol_kit.hol.thirdorder import to_isabelle_to, to_thf_to

TO = MSFLParser(third_order=True)
TOM = MSFLParser(third_order=True, modal=True)


# --- classical: the types ---------------------------------------------------

def test_a_predicate_of_properties_gets_a_predicate_type():
    theory = to_isabelle_to(TO.parse("Pos(G) ∧ G(a)"))
    assert 'consts Pos :: "(i \\<Rightarrow> bool) \\<Rightarrow> bool"' in theory
    assert 'consts G :: "i \\<Rightarrow> bool"' in theory
    assert 'consts a :: "i"' in theory


def test_a_mixed_slot_signature_keeps_the_positions_apart():
    """``Essence(P, x)`` takes a property THEN an individual, in that order."""
    theory = to_isabelle_to(TO.parse("∀P ∀x (Ess(P, x) → P(x))"))
    assert ('consts Ess :: "(i \\<Rightarrow> bool) \\<Rightarrow> i '
            '\\<Rightarrow> bool"') in theory


def test_thf_types_match_the_isabelle_ones():
    problem = to_thf_to(TO.parse("∀P ∀x (Ess(P, x) → P(x))"))
    # THF constants are lower words (an upper-case initial is a variable).
    assert "thf(ess_type, type, ( ess : ( $i > $o ) > $i > $o ))." in problem
    assert "! [P_P: $i > $o]" in problem


def test_assumptions_are_typed_together_with_the_goal():
    """A symbol whose arity only an ASSUMPTION fixes is still typed correctly."""
    theory = to_isabelle_to(TO.parse("Pos(G)"),
                            assumptions=[TO.parse("∀x ∀y G(x, y)")])
    assert 'consts Pos :: "(i \\<Rightarrow> i \\<Rightarrow> bool) \\<Rightarrow> bool"' in theory


def test_an_undetermined_property_arity_is_reported_not_hidden():
    theory = to_isabelle_to(TO.parse("Pos(G)"))
    assert "arity defaulted to 1" in theory and "Pos[0]" in theory


def test_the_classical_export_refuses_modal_operators_by_name():
    with pytest.raises(UnsupportedHigherOrderNode, match="ho_modal"):
        to_isabelle_to(TOM.parse("□Pos(G)"))


def test_a_goal_without_a_proof_is_left_open():
    assert "oops" in to_isabelle_to(TO.parse("Pos(G)"))
    assert "by blast" in to_isabelle_to(TO.parse("Pos(G)"), proof="by blast")


# --- modal: the embedding ---------------------------------------------------

def test_the_lifted_vocabulary_is_abbreviations_not_definitions():
    """An abbreviation unfolds at parse time, so the automation sees through it.

    With ``definition`` every proof would first have to unfold the embedding,
    which is the difference between a proof that takes ten seconds and one that
    does not finish -- measured, not assumed (see test_goedel.py).
    """
    definitions = ho_modal_definitions()
    for name in ("mnot", "mand", "mor", "mimp", "miff", "mbox", "mdia",
                 "mall", "mex", "mvalid"):
        assert f"abbreviation {name} ::" in definitions
    assert "definition " not in definitions


def test_one_polymorphic_binder_serves_both_orders():
    """``mall`` at type ``('a => sigma) => sigma`` binds individuals AND properties."""
    assert "abbreviation mall :: \"('a \\<Rightarrow> sigma) \\<Rightarrow> sigma\"" \
        in ho_modal_definitions()
    theory = isabelle_ho_modal_theory(
        "T", (), [HoGoal("g", TOM.parse("∀P ∀x (Pos(P) → P(x))"))])
    assert "mall (\\<lambda>P::i \\<Rightarrow> sigma." in theory
    assert "mall (\\<lambda>x::i." in theory


def test_a_property_is_world_indexed_in_the_modal_embedding():
    theory = isabelle_ho_modal_theory("T", (), [HoGoal("g", TOM.parse("Pos(G)"))])
    assert 'consts Pos :: "(i \\<Rightarrow> sigma) \\<Rightarrow> sigma"' in theory
    assert 'type_synonym sigma = "world \\<Rightarrow> bool"' in theory


def test_axioms_are_asserted_valid_at_every_world():
    theory = isabelle_ho_modal_theory(
        "T", [HoAxiom("A", TOM.parse("Pos(G)"))],
        [HoGoal("g", TOM.parse("□Pos(G)"))])
    assert 'axiomatization where A: "mvalid (Pos G)"' in theory
    assert 'theorem g: "mvalid (mbox (Pos G))"' in theory


def test_frame_conditions_come_from_the_shared_registry():
    theory = isabelle_ho_modal_theory("T", (), [HoGoal("g", TOM.parse("Pos(G)"))],
                                      frame="S5")
    for condition in ("R_refl", "R_sym", "R_trans"):
        assert f"axiomatization where {condition}:" in theory
    assert "R_refl" not in isabelle_ho_modal_theory(
        "T", (), [HoGoal("g", TOM.parse("Pos(G)"))], frame="K")


def test_gl_states_the_loeb_schema_with_an_explicit_binder():
    """GL = trans + loeb: Löb's schema is stated directly, P bound explicitly.

    ``GL`` used to be refused outright (loeb/mckinsey/grz have no first-order
    correspondence over ``R``) -- it now states each as a schema over
    propositions, exactly like ``hol.isabelle_modal``'s ``r_loeb`` does at
    first order, but with the schema variable ``P`` bound by an explicit
    ``\\<forall>P::sigma.`` rather than left free, as defense-in-depth against
    the frame-axiom/signature emission order in ``isabelle_ho_modal_theory``
    ever changing (see the comment above ``_FRAME_AXIOMS`` in ho_modal.py and
    ``test_a_declared_p_cannot_capture_the_bound_schema_variable`` below).
    """
    theory = isabelle_ho_modal_theory("T", (), [HoGoal("g", TOM.parse("Pos(G)"))],
                                      frame="GL")
    assert "axiomatization where R_trans:" in theory
    assert '\\<forall>P::sigma. \\<forall>x.' in theory
    assert "axiomatization where R_loeb:" in theory
    # GL is irreflexive: reflexivity must not sneak in.
    assert "R_refl" not in theory


def test_s4_1_states_the_mckinsey_schema():
    """S4.1 = refl + trans + mckinsey (box-diamond -> diamond-box)."""
    theory = isabelle_ho_modal_theory("T", (), [HoGoal("g", TOM.parse("Pos(G)"))],
                                      frame="S4.1")
    for condition in ("R_refl", "R_trans", "R_mckinsey"):
        assert f"axiomatization where {condition}:" in theory
    assert "R_loeb" not in theory and "R_grz" not in theory


def test_grz_states_the_grzegorczyk_schema():
    """Grz = refl + trans + grz (the Grzegorczyk schema)."""
    theory = isabelle_ho_modal_theory("T", (), [HoGoal("g", TOM.parse("Pos(G)"))],
                                      frame="Grz")
    for condition in ("R_refl", "R_trans", "R_grz"):
        assert f"axiomatization where {condition}:" in theory
    assert "R_loeb" not in theory and "R_mckinsey" not in theory


def test_thf_states_the_three_schemas_with_an_explicit_binder():
    for frame, thf_name in (("GL", "frame_loeb"), ("S4.1", "frame_mckinsey"),
                            ("Grz", "frame_grz")):
        problem = to_thf_ho_modal(TOM.parse("Pos(G)"), frame=frame)
        assert f"thf({thf_name}, axiom," in problem
        assert "! [P: mu > $o] :" in problem


def test_a_declared_p_cannot_capture_the_bound_schema_variable():
    """A capture-safety regression, kept as defense-in-depth rather than a live fix.

    A user axiom that declares a property literally named ``P`` (entirely
    plausible in Gödel's-argument settings, where ``P``/``Q`` are common
    property names) must not let the Löb schema's schema variable resolve to
    that constant -- that would silently validate the schema for one property
    only rather than generalising it. ``isabelle_ho_modal_theory`` already
    emits the frame axiom (this dict's ``R_loeb``) BEFORE the signature's
    ``consts P``, so even a free/unbound schema variable would never actually
    resolve to a not-yet-declared user constant through the current public
    API -- verified live against Isabelle: a free ``R_loeb`` in that same real
    order still discharges the schema for an unrelated proposition ``Q`` just
    as fast as the explicit-binder version below. The explicit
    ``\\<forall>P::sigma.`` binder is kept anyway so the schema's universal
    scope is visible in the source text and stays safe if that emission
    order ever changes; this test pins that the two ``P``\\ s are textually
    and semantically distinct, not that omitting the binder would break.
    """
    axiom = HoAxiom("A", TOM.parse("P"))
    theory = isabelle_ho_modal_theory("T", [axiom], [HoGoal("g", TOM.parse("P"))],
                                      frame="GL")
    # The user's own nullary proposition P is declared as a plain constant...
    assert 'consts P :: "sigma"' in theory
    # ...while the Löb schema's P is a SEPARATE, explicitly bound variable of
    # the same name -- distinct textually (its own quantifier) and distinct
    # in what it ranges over (a schema, not the one declared constant).
    assert '\\<forall>P::sigma. \\<forall>x.' in theory
    loeb_line = next(l for l in theory.splitlines() if l.startswith("axiomatization where R_loeb"))
    assert '\\<forall>P::sigma.' in loeb_line
    # The user's axiom uses the constant directly, unquantified -- so the two
    # P's are never confused for each other in the emitted text.
    assert 'axiomatization where A: "mvalid P"' in theory


def test_thf_declared_p_cannot_capture_the_bound_schema_variable():
    """The THF counterpart of the capture-safety regression above.

    The frame clause binds its schema variable explicitly (`! [P: mu > $o]`),
    and the user's own ``P`` is a constant, which THF spells as the lower word
    ``p``: the two cannot meet, whatever the user calls the symbol.
    """
    axiom = HoAxiom("A", TOM.parse("P"))
    problem = to_thf_ho_modal(TOM.parse("P"), frame="GL", axioms=[axiom])
    assert "thf(p_type, type, ( p : mu > $o ))." in problem
    frame_line = next(l for l in problem.splitlines() if l.startswith("thf(frame_loeb"))
    assert "! [P: mu > $o] :" in frame_line
    assert "thf(a, axiom, ( mvalid @ p ))." in problem


def test_a_frame_condition_missing_from_frame_axioms_is_still_refused(monkeypatch):
    """Every ``FRAME_CONDITIONS`` entry now has a ``_FRAME_AXIOMS`` counterpart

    (loeb/mckinsey/grz included), so ``UnsupportedFrameCondition`` has no live
    trigger left through any registered system name -- but it stays a defence
    against ``_FRAME_AXIOMS``/``fol.frames.FRAME_CONDITIONS`` drifting apart,
    not dead code, which this pins by simulating exactly that drift.
    """
    import unicode_fol_kit.hol.ho_modal as ho_modal
    monkeypatch.delitem(ho_modal._FRAME_AXIOMS, "loeb")
    with pytest.raises(UnsupportedFrameCondition, match="loeb"):
        isabelle_ho_modal_theory("T", (), [HoGoal("g", TOM.parse("Pos(G)"))],
                                 frame="GL")


def test_an_unknown_frame_is_refused():
    with pytest.raises(ValueError, match="unknown frame"):
        isabelle_ho_modal_theory("T", (), [HoGoal("g", TOM.parse("Pos(G)"))],
                                 frame="S99")


def test_epistemic_and_the_rest_of_the_family_are_now_carried():
    """C18: K_a/B_a/Say_a/Want_a, O/P, temporal, hybrid all get a real reading now.

    Was ``test_the_non_alethic_modal_families_are_refused_by_name`` -- the
    parser always accepted the whole family (same AST); this embedding used
    to refuse everything but □/◇ by name. It now carries the whole
    non-counterfactual family (see the module docstring), so this formula
    TYPE-CHECKS and the widened Isabelle text contains a real ``mknows``
    application rather than a refusal.
    """
    theory = to_isabelle_ho_modal(TOM.parse("∀P (Pos(P) → K_a P(x))"))
    assert "mknows a" in theory


def test_the_counterfactuals_are_still_refused_by_name():
    """Would/Might read a similarity ordering, not an accessibility relation."""
    with pytest.raises(UnsupportedHigherOrderNode, match="similarity ordering"):
        to_isabelle_ho_modal(TOM.parse("Pos(G) □→ Pos(G)"))
    with pytest.raises(UnsupportedHigherOrderNode, match="similarity ordering"):
        to_thf_ho_modal(TOM.parse("Pos(G) □→ Pos(G)"))


def test_group_epistemic_operators_are_still_refused_by_name():
    """E_G/D_G/C_G are not implemented (C_G would need a transitive closure)."""
    with pytest.raises(UnsupportedHigherOrderNode, match="EverybodyKnows"):
        to_isabelle_ho_modal(TOM.parse("E_{a,b} Pos(G)"))
    with pytest.raises(UnsupportedHigherOrderNode, match="EverybodyKnows"):
        to_thf_ho_modal(TOM.parse("E_{a,b} Pos(G)"))


def test_thf_and_isabelle_agree_about_the_signature():
    formula = TOM.parse("∀P ∀x (Ess(P, x) → □P(x))")
    assert 'consts Ess :: "(i \\<Rightarrow> sigma) \\<Rightarrow> i \\<Rightarrow> sigma"' \
        in isabelle_ho_modal_theory("T", (), [HoGoal("g", formula)])
    assert "thf(ess_type, type, ( ess : ( $i > mu > $o ) > $i > mu > $o ))." \
        in to_thf_ho_modal(formula)


def test_thf_world_binders_are_numbered_rather_than_shadowed():
    problem = to_thf_ho_modal(TOM.parse("∀x ◇∃y G(x)"))
    assert "W0: mu" in problem and "W1: mu" in problem


# --- renaming apart ---------------------------------------------------------

def test_two_axioms_binding_the_same_name_at_different_arities_do_not_collide():
    """A bound name is scoped to its formula; merging them would be a false conflict."""
    unary = TO.parse("∀P (Pos(P) → P(x))")
    binary = TO.parse("∀P (Rel(P) → P(x, y))")
    theory = to_isabelle_to(binary, assumptions=[unary])
    assert 'consts Pos :: "(i \\<Rightarrow> bool) \\<Rightarrow> bool"' in theory
    assert ('consts Rel :: "(i \\<Rightarrow> i \\<Rightarrow> bool) '
            '\\<Rightarrow> bool"') in theory


def test_the_renaming_is_invisible_in_the_emitted_text():
    """It exists for the ANALYSIS; what is printed is what the caller wrote."""
    theory = to_isabelle_to(TO.parse("∀P (Pos(P) → P(x))"))
    assert "Bound1" not in theory
    assert "\\<forall>P::i \\<Rightarrow> bool." in theory


def test_rename_apart_reports_what_each_fresh_name_stood_for():
    renamed, original = rename_apart([TO.parse("∀P (Pos(P) → P(x))")])
    assert set(original.values()) == {"P"}
    assert all(name.startswith("Bound") for name in original)


# --- goal shapes ------------------------------------------------------------

def test_a_goal_is_either_a_formula_or_a_raw_statement_never_both():
    with pytest.raises(ValueError, match="exactly one"):
        HoGoal("g", TOM.parse("Pos(G)"), statement="False")
    with pytest.raises(ValueError, match="exactly one"):
        HoGoal("g")


def test_a_raw_statement_is_emitted_verbatim_and_needs_no_typing():
    """"These axioms prove falsity" is a claim ABOUT the theory, not in it."""
    theory = isabelle_ho_modal_theory(
        "T", [HoAxiom("A", TOM.parse("Pos(G)"))],
        [HoGoal("bad", statement="False", proof="by blast")])
    assert 'theorem bad: "False"' in theory


# --- C18: the widened modal family (Package 2/3), structural coverage ------
#
# One structural test per new node type, both exporters, over a THIRD-order
# formula (a PredicateTerm argument in scope) -- confirming each new family
# type-checks through the SAME third-order signature machinery the alethic
# fragment already used, not a special case. Live proof/refutation coverage
# for these families lives in test_ho_modal_frames.py (this file stays
# proof-free, per its own docstring).

@pytest.mark.parametrize("text,isa_macro,thf_macro", [
    ("K_a Pos(G)", "mknows", "mknows"),
    ("B_a Pos(G)", "mbelieves", "mbelieves"),
    ("Say_a Pos(G)", "msays", "msays"),
    ("Want_a Pos(G)", "mwants", "mwants"),
    ("Ⓞ Pos(G)", "mobl", "mobl"),
    ("Ⓟ Pos(G)", "mperm", "mperm"),
    ("Ⓖ Pos(G)", "malways", "malways"),
    ("Ⓕ Pos(G)", "meventually", "meventually"),
    ("Ⓝ Pos(G)", "mnext", "mnext"),
    ("⒣ Pos(G)", "mhistorically", "mhistorically"),
    ("⒫ Pos(G)", "monce", "monce"),
    ("⒴ Pos(G)", "mprevious", "mprevious"),
])
def test_every_new_family_node_gets_a_reading(text, isa_macro, thf_macro):
    formula = TOM.parse(text)
    theory = isabelle_ho_modal_theory("T", (), [HoGoal("g", formula)])
    assert f"({isa_macro} " in theory
    problem = to_thf_ho_modal(formula)
    assert f"( {thf_macro} @ " in problem


def test_until_and_since_use_the_inductive_least_fixpoint():
    """Strong Until/Since are ``inductive``, not ``abbreviation`` -- a genuine
    recursive definition, exactly mirroring hol.isabelle_modal's own muntil."""
    until = TOM.parse("Pos(G) Ⓤ Pos(H)")
    theory = isabelle_ho_modal_theory("T", (), [HoGoal("g", until)])
    assert "inductive muntil ::" in theory
    assert "muntil_base:" in theory and "muntil_step:" in theory
    assert "(muntil (Pos G) (Pos H))" in theory
    problem = to_thf_ho_modal(until)
    assert "thf(muntil_def, definition," in problem

    since = TOM.parse("Pos(G) ⒮ Pos(H)")
    theory2 = isabelle_ho_modal_theory("T", (), [HoGoal("g", since)])
    assert "inductive msince ::" in theory2
    assert "(msince (Pos G) (Pos H))" in theory2


def test_hybrid_nominal_and_at_get_world_constants():
    formula = TOM.parse("@i Pos(G)")
    theory = isabelle_ho_modal_theory("T", (), [HoGoal("g", formula)])
    assert 'consts nom_i :: "world"' in theory
    assert "nom_i" in theory
    problem = to_thf_ho_modal(formula)
    assert "thf(i_type, type, ( i : mu ))." in problem
    assert "@ i )" in problem  # `( body @ i )` -- evaluated AT the named world


def test_a_bound_agent_variable_quantifies_over_agents():
    """``∀x (Student(x) → K_x Pos(G))`` -- the agent is the SAME bound ``x``."""
    formula = TOM.parse("∀x (Student(x) → K_x Pos(G))")
    theory = isabelle_ho_modal_theory("T", (), [HoGoal("g", formula)])
    assert "(mknows x (Pos G))" in theory
    problem = to_thf_ho_modal(formula)
    assert "mknows @ X_V @" in problem


def test_systems_constrains_one_agent_indexed_family():
    formula = TOM.parse("K_a Pos(G)")
    theory = isabelle_ho_modal_theory("T", (), [HoGoal("g", formula)],
                                      systems={"epistemic": "S5"})
    for axiom in ("Rk_refl", "Rk_trans", "Rk_sym"):
        assert f"axiomatization where {axiom}:" in theory
    # Untouched by default: no doxastic relation at all when B_a never occurs.
    assert "Rb" not in theory


def test_systems_naming_an_unused_family_is_refused():
    formula = TOM.parse("K_a Pos(G)")
    with pytest.raises(ValueError, match="doxastic"):
        isabelle_ho_modal_theory("T", (), [HoGoal("g", formula)],
                                 systems={"doxastic": "S5"})
    with pytest.raises(ValueError, match="doxastic"):
        to_thf_ho_modal(formula, systems={"doxastic": "S5"})


def test_systems_naming_an_unknown_family_is_refused():
    formula = TOM.parse("K_a Pos(G)")
    with pytest.raises(ValueError, match="unknown systems"):
        isabelle_ho_modal_theory("T", (), [HoGoal("g", formula)],
                                 systems={"epistemc": "S5"})


def test_systems_naming_a_system_with_no_per_agent_schema_is_refused():
    """GL needs Löb, which has no per-agent Horn schema (only refl/trans/sym/
    serial/eucl do) -- refused rather than silently emitting a weaker logic."""
    formula = TOM.parse("K_a Pos(G)")
    with pytest.raises(NotImplementedError, match="loeb"):
        isabelle_ho_modal_theory("T", (), [HoGoal("g", formula)],
                                 systems={"epistemic": "GL"})


def test_the_euclidean_per_agent_axiom_keeps_the_agent_in_its_conclusion():
    """Regression: an earlier draft of the K5/KD45/K45 euclidean schema

    dropped the agent argument from its CONCLUSION (``Rb v u`` instead of
    ``Rb a v u``), which is well-typed nonsense as soon as a SECOND
    agent-indexed relation is also declared (a genuine type clash --
    ``v``/``u`` get unified with the OTHER relation's world-only slots --
    caught live while writing test_hol_isabelle_actualist's/frames' battery
    with two systems= families at once). K5 alone (only "eucl") is enough to
    pin the axiom text itself, both exporters.
    """
    formula = TOM.parse("K_a Pos(G)")
    theory = isabelle_ho_modal_theory("T", (), [HoGoal("g", formula)],
                                      systems={"epistemic": "K5"})
    assert 'axiomatization where Rk_eucl: "\\<forall>a w v u. Rk a w v ' \
           '\\<longrightarrow> Rk a w u \\<longrightarrow> Rk a v u"' in theory
    problem = to_thf_ho_modal(formula, systems={"epistemic": "K5"})
    assert ("thf(rk_eucl, axiom, ( ! [A: $i, W: mu, V: mu, U: mu] : "
           "( ( ( rk @ A @ W @ V ) & ( rk @ A @ W @ U ) ) "
           "=> ( rk @ A @ V @ U ) ) )).") in problem
