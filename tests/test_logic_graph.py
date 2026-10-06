"""The translation graph's contract: guarantees, side axioms, option routing.

Two things are being pinned here.

1. A translation's SIDE CONDITIONS travel with its result. The motivating case
   is the one 0.28.0 shipped a bug for: ``(∀x:Human M(x)) → ∃x:Human M(x)`` is
   valid in the kit's many-sorted semantics, its unsorted image is NOT valid,
   and the difference is the sort-non-emptiness axiom. An edge now produces that
   axiom (never conjoined onto the image — that would ask a prover to prove the
   axiom too), ``TranslationResult.axioms`` carries it, and a
   :class:`~unicode_fol_kit.logic.Sentence` keeps the two together so
   ``api.prove`` cannot be handed the term without them by accident.

2. Two routes of the kit must not contradict each other. Until 0.28.1 the
   standard translation asserted frame conditions for the ALETHIC relation only,
   while it emits ``T``/``N``/``D`` as well, so ``hybrid_is_valid(Ⓖφ → φ, "S5")``
   answered False — a bare "not valid" about a formula the kit's own Kripke
   evaluator and ``qml_is_valid`` both validate. The agreement table below is
   the regression test; every expected verdict is hand-derived, with the reason
   written next to it.

Every expectation here is hand-worked: no value was read off the code under
test.
"""

import pytest

from unicode_fol_kit import MSFLParser, api
from unicode_fol_kit.comorphism import (
    Comorphism, ComorphismRegistry, DEFAULT_REGISTRY, GUARANTEES,
    weakest_guarantee,
)
from unicode_fol_kit.fol.frames import UnsupportedFrameCondition
from unicode_fol_kit.fol.modal_translation import (
    frame_axioms, hybrid_is_valid, relations_used, standard_translation,
)
from unicode_fol_kit.fol.nodes import (
    Always, Atom, Believes, Box, Constant, Diamond, Eventually, Historically,
    Implies, Knows, Next, Obligatory, Once, Or, Permitted, Previous, Says,
    Wants,
)
from unicode_fol_kit.fol.qml import qml_is_valid
from unicode_fol_kit.logic import ALC, FOL, MODAL, MSFOL, Logic, Sentence

FOLP = MSFLParser()
MODALP = MSFLParser(modal=True)
SORTED = MSFLParser(many_sorted=True)

P = Atom("P", ())
Q = Atom("Q", ())


# ---------------------------------------------------------------------------
# The contract on an edge
# ---------------------------------------------------------------------------

def test_an_edge_may_not_disagree_with_itself_about_being_lossy():
    with pytest.raises(ValueError, match="preserves nothing"):
        Comorphism(name="e", source="a", target="b", apply=lambda t: t,
                   lossy=True, guarantee="faithful")
    with pytest.raises(ValueError, match="guarantee='lossy' but lossy=False"):
        Comorphism(name="e", source="a", target="b", apply=lambda t: t,
                   guarantee="lossy")
    with pytest.raises(ValueError, match="is not one of"):
        Comorphism(name="e", source="a", target="b", apply=lambda t: t,
                   guarantee="mostly")


def test_weakest_guarantee_is_the_order_of_the_vocabulary():
    assert GUARANTEES == ("faithful", "validity", "satisfiability", "lossy")
    # A faithful edge after a satisfiability-only one does not repair it.
    assert weakest_guarantee(["faithful", "satisfiability"]) == "satisfiability"
    assert weakest_guarantee(["validity", "faithful"]) == "validity"
    assert weakest_guarantee(["faithful", "faithful"]) == "faithful"
    # One undeclared edge makes the whole path undeclared — not "faithful".
    assert weakest_guarantee(["faithful", None]) is None
    assert weakest_guarantee([]) is None


def test_the_identity_translation_is_faithful_and_carries_nothing():
    result = DEFAULT_REGISTRY.translate(P, "fol", "fol")
    assert result.path == () and result.axioms == ()
    assert result.guarantee == "faithful" and result.lossy is False


#: The kit's own nine edges, by name. Written out rather than derived from the
#: registry, because the registry is PROCESS-GLOBAL and a third party may have
#: added to it — ``hets.bridge.register_hets_comorphisms`` does exactly that, and
#: its edges deliberately declare no guarantee. A test that asked "does every
#: edge in the registry declare one" therefore passed or failed depending on
#: which test file ran first in the same worker, which is how this list got
#: written: it went red in a full ``-n 8`` run and green on its own.
_KIT_EDGES = frozenset({
    "standard_translation", "qml_translate", "to_fol", "to_msfol",
    "fol_to_drs", "drs_to_fol", "concept_to_fol", "concept_to_modal",
    "dependence_to_eso",
})


def test_every_edge_of_the_kits_own_nine_declares_a_guarantee():
    edges = {e.name: e for e in DEFAULT_REGISTRY.edges()}
    assert _KIT_EDGES <= set(edges), sorted(_KIT_EDGES - set(edges))
    undeclared = [name for name in sorted(_KIT_EDGES)
                  if edges[name].guarantee is None]
    assert undeclared == []
    # and each one is a value from the vocabulary, not free text
    assert all(edges[name].guarantee in GUARANTEES for name in _KIT_EDGES)


def test_an_edge_registered_by_someone_else_may_leave_it_undeclared():
    # The complement of the test above, and the reason it is scoped: not
    # declaring a guarantee is a legal state for an edge this kit did not write
    # and has not verified (hets.bridge's server edges are the real case).
    registry = ComorphismRegistry()
    registry.register(Comorphism(
        name="third_party", source="fol", target="mystery",
        apply=lambda term: term))
    assert registry.edges()[0].guarantee is None
    result = registry.translate(FOLP.parse("P(a)"), "fol", "mystery")
    assert result.guarantee is None


# ---------------------------------------------------------------------------
# Side axioms: produced, propagated, never folded in
# ---------------------------------------------------------------------------

_SORTED_VALID = "(∀x:Human M(x)) → ∃x:Human M(x)"


def test_the_sorted_image_needs_its_non_emptiness_axiom_to_be_valid():
    # Hand-derived: with Human possibly EMPTY the unsorted image is falsified by
    # the empty-Human structure (antecedent vacuously true, consequent false);
    # the kit's MSFOL semantics has no empty sorts, which is what the axiom says.
    sentence = FOL(MSFOL(SORTED.parse(_SORTED_VALID)))
    assert len(sentence.axioms) == 1
    assert api.prove(sentence.term, backends=["z3"]).status == "refuted"
    assert api.prove(sentence.term, list(sentence.axioms),
                     backends=["z3"]).status == "proved"
    # and the same through the Sentence, which is the point of carrying them
    assert api.prove(sentence, backends=["z3"]).status == "proved"


def test_the_axioms_are_not_conjoined_onto_the_image():
    result = DEFAULT_REGISTRY.translate(SORTED.parse(_SORTED_VALID),
                                        "msfol", "fol")
    # The image is exactly the guarded formula — the axiom is NOT inside it.
    assert result.result.to_unicode_str() == (
        "∀x (Human(x) → M(x)) → ∃x (Human(x) ∧ M(x))")
    assert [a.to_unicode_str() for a in result.axioms] == ["∃x0 Human(x0)"]
    # and the axiom is text this kit reads back — it used to be
    # "∃_msfol_Human_witness Human(…)", which its own parser rejects
    assert api.parse_any(result.axioms[0].to_unicode_str()).ok


def test_a_subsort_hierarchy_comes_from_the_signature_option():
    from unicode_fol_kit.fol.signature import Signature
    signature = Signature(sorts=("Animal", "Human"),
                          subsorts={"Human": frozenset({"Animal"})})
    goal = SORTED.parse("(∀x:Animal P(x)) → ∀y:Human P(y)")
    plain = DEFAULT_REGISTRY.translate(goal, "msfol", "fol")
    with_sig = DEFAULT_REGISTRY.translate(goal, "msfol", "fol",
                                          signature=signature)
    # Hand-derived: Human ⊑ Animal is what makes the goal valid; without the
    # edge axiom the image has a countermodel (a Human outside Animal).
    assert api.prove(plain.result, list(plain.axioms),
                     backends=["z3"]).status == "refuted"
    assert api.prove(with_sig.result, list(with_sig.axioms),
                     backends=["z3"]).status == "proved"
    assert len(with_sig.axioms) == len(plain.axioms) + 1


def test_an_upstream_axiom_is_carried_through_the_remaining_edges():
    # A throwaway registry: edge one produces an axiom in logic "b", edge two
    # maps b → c by tagging. The axiom must arrive TAGGED, i.e. translated.
    registry = ComorphismRegistry()
    registry.register(Comorphism(
        name="a_to_b", source="a", target="b", apply=lambda t: f"b({t})",
        guarantee="validity", axioms=lambda t: (f"ax({t})",)))
    registry.register(Comorphism(
        name="b_to_c", source="b", target="c", apply=lambda t: f"c({t})",
        guarantee="faithful", axioms=lambda t: (f"cx({t})",)))
    result = registry.translate("f", "a", "c")
    assert result.result == "c(b(f))"
    # ax(f) was produced in b and must be mapped by b_to_c; cx is produced by
    # the second edge from the term IT was handed.
    assert result.axioms == ("c(ax(f))", "cx(b(f))")
    assert result.guarantee == "validity"          # the weaker of the two
    assert result.path == ("a_to_b", "b_to_c")


def test_carry_translates_a_term_without_collecting_axioms_again():
    # Used when the term IS an axiom: its edge's axioms were collected once.
    assert DEFAULT_REGISTRY.carry(SORTED.parse("∀x:Human M(x)"), "msfol", "fol"
                                  ).to_unicode_str() == "∀x (Human(x) → M(x))"


# ---------------------------------------------------------------------------
# Options are routed, never ignored
# ---------------------------------------------------------------------------

def test_an_option_no_edge_accepts_is_refused_by_name():
    with pytest.raises(ValueError, match=r"option\(s\) \['speed'\]"):
        DEFAULT_REGISTRY.translate(Box(P), "modal", "fol", speed="fast")
    with pytest.raises(ValueError, match=r"option\(s\) \['frame'\]"):
        # the sorted edge has nothing to do with frames
        DEFAULT_REGISTRY.translate(SORTED.parse("∀x:Human M(x)"), "msfol",
                                   "fol", frame="S4")


def test_an_option_reaches_the_axioms_and_leaves_the_image_alone():
    k = DEFAULT_REGISTRY.translate(Box(P), "modal", "fol")
    s4 = DEFAULT_REGISTRY.translate(Box(P), "modal", "fol", frame="S4")
    assert k.result == s4.result                      # the translation is the same
    assert k.axioms == ()                             # K constrains nothing
    assert [a.to_unicode_str() for a in s4.axioms] == [
        "∀v0 R(v0, v0)",
        "∀v0 ∀v1 ∀v2 (R(v0, v1) ∧ R(v1, v2) → R(v0, v2))"]


def test_a_logic_value_refuses_options_when_it_only_wraps():
    with pytest.raises(TypeError, match="apply to a CONVERSION"):
        MODAL(Box(P), frame="S4")


# ---------------------------------------------------------------------------
# frame_axioms: every relation the translation emits
# ---------------------------------------------------------------------------

def test_relations_used_names_the_relation_of_every_family():
    assert relations_used(Box(P)) == {"R"}
    assert relations_used(Diamond(P)) == {"R"}
    assert relations_used(Knows("alice", P)) == {"Rk_alice"}
    assert relations_used(Believes("bob", P)) == {"Rb_bob"}
    assert relations_used(Says("carol", P)) == {"Rs_carol"}
    assert relations_used(Wants("dave", P)) == {"Rw_dave"}
    assert relations_used(Obligatory(P)) == {"D"}
    assert relations_used(Permitted(P)) == {"D"}
    assert relations_used(Always(P)) == {"T"}
    assert relations_used(Eventually(P)) == {"T"}
    assert relations_used(Historically(P)) == {"T"}
    assert relations_used(Once(P)) == {"T"}
    assert relations_used(Next(P)) == {"N"}
    assert relations_used(Previous(P)) == {"N"}
    assert relations_used(Implies(P, Q)) == frozenset()


def test_an_alethic_formula_gets_exactly_the_alethic_axioms():
    # Gating matters: a condition on a relation the formula never mentions is
    # noise on a route whose False is read as a countermodel.
    axioms = frame_axioms(Box(P), "S5")
    assert all("R(" in a.to_unicode_str() for a in axioms)
    assert frame_axioms(Implies(P, Q), "S5") == []       # no modality at all


def test_the_temporal_and_deontic_conditions_are_on_by_default():
    temporal = [a.to_unicode_str() for a in frame_axioms(Always(Next(P)), "K")]
    assert temporal == [
        "∀v0 T(v0, v0)",
        "∀v0 ∀v1 ∀v2 (T(v0, v1) ∧ T(v1, v2) → T(v0, v2))",
        "∀v0 ∀v1 (N(v0, v1) → T(v0, v1))",
        "∀v0 ∀v1 (T(v0, v1) → v0 = v1 ∨ "
        "∃v2 (N(v0, v2) ∧ T(v2, v1)))",
    ]
    assert [a.to_unicode_str() for a in frame_axioms(Obligatory(P), "K")] == [
        "∀v0 ∃v1 D(v0, v1)"]
    # the link is only asserted when BOTH relations occur
    assert all("N(" not in a.to_unicode_str()
               for a in frame_axioms(Always(P), "K"))


def test_temporal_closure_off_drops_the_closure_conditions():
    axioms = [a.to_unicode_str()
              for a in frame_axioms(Always(Next(P)), "K", temporal_closure=False)]
    assert axioms == ["∀v0 ∀v1 (N(v0, v1) → T(v0, v1))"]


def test_an_agent_family_is_constrained_only_when_asked():
    f = Implies(Knows("alice", P), P)
    assert frame_axioms(f, "S5") == []                  # S5 is about R, not Rk_
    asked = [a.to_unicode_str() for a in
             frame_axioms(f, "K", systems={"epistemic": "T"})]
    assert asked == ["∀v0 Rk_alice(v0, v0)"]
    with pytest.raises(ValueError, match="unknown modal family"):
        frame_axioms(f, "K", systems={"telepathic": "S5"})


def test_a_frame_without_a_first_order_condition_is_refused_by_name():
    with pytest.raises(UnsupportedFrameCondition):
        frame_axioms(Box(P), "GL")
    with pytest.raises(ValueError, match="unknown frame"):
        frame_axioms(Box(P), "nonsense")


# ---------------------------------------------------------------------------
# The two routes agree (the regression this release is about)
# ---------------------------------------------------------------------------

# (formula, expected verdict, why — hand-derived)
_AGREEMENT = [
    (Implies(Always(P), P), True,
     "T is reflexive: henceforth includes now"),
    (Implies(Always(P), Next(P)), True,
     "N ⊆ T: the next step is a step"),
    (Implies(Always(P), Eventually(P)), True,
     "T reflexive, so Gφ gives φ at the current world, hence Fφ"),
    (Implies(P, Eventually(P)), True,
     "T reflexive: now is a reachable moment"),
    (Implies(Historically(P), P), True,
     "the past mirror of reflexivity"),
    (Implies(Obligatory(P), Permitted(P)), True,
     "D is serial (Standard Deontic Logic): some acceptable world exists"),
    (Implies(Permitted(P), Obligatory(P)), False,
     "seriality does not make a permission an obligation"),
    (Implies(Always(P), Always(Always(P))), True,
     "T is transitive"),
    (Implies(Next(P), Always(P)), False,
     "one step says nothing about all steps"),
    (Implies(Knows("alice", P), P), False,
     "the epistemic relation is K unless systems= asks for more"),
]


@pytest.mark.parametrize("formula,expected,why", _AGREEMENT)
def test_the_hybrid_and_qml_routes_give_the_hand_derived_verdict(formula, expected, why):
    assert hybrid_is_valid(formula, "S5") is expected, why
    assert qml_is_valid(formula) is expected, why


def test_asking_for_a_factive_epistemic_system_makes_knowledge_factive():
    f = Implies(Knows("alice", P), P)
    assert hybrid_is_valid(f, "K", systems={"epistemic": "S5"}) is True
    assert qml_is_valid(f, systems={"epistemic": "S5"}) is True


# ---------------------------------------------------------------------------
# Equality is not an ordinary atom in the propositional modal layer
# ---------------------------------------------------------------------------

def test_an_equality_atom_is_refused_by_the_propositional_translation():
    # Before 0.30.0 '=' got the world appended like any predicate, which made
    # identity a world-varying uninterpreted relation and 'a = a' not valid.
    equality = FOLP.parse("a = a")
    with pytest.raises(NotImplementedError, match="equality atom"):
        standard_translation(equality)
    with pytest.raises(NotImplementedError, match="fol.qml"):
        hybrid_is_valid(Box(equality), "S5")


def test_the_disequality_spelling_is_refused_by_the_same_name_check():
    # The first version of the refusal compared the predicate against "=" only,
    # so 'a ≠ b' still got the world appended: '≠(a, b, w0)', a ternary relation
    # with no link to the '=' one, under which 'a = b ∨ a ≠ b' is not valid.
    # Both spellings are now refused by the one shared check.
    disequality = Atom("≠", (Constant("a"), Constant("b")))
    with pytest.raises(NotImplementedError, match="disequality atom"):
        standard_translation(disequality)
    with pytest.raises(NotImplementedError, match="disequality atom"):
        hybrid_is_valid(Box(disequality), "S5")
    excluded_middle = Or(FOLP.parse("a = b"), disequality)
    with pytest.raises(NotImplementedError, match="refused by name"):
        standard_translation(excluded_middle)


def test_the_propositional_routes_all_refuse_from_one_shared_check():
    # Four routes read an atom without interpreting a term: the translation, the
    # Kripke evaluator, the modal tableau and the GMT embedding. They used to
    # keep their own copies of the refusal (or none at all); the wording now
    # comes from semantics._modal_reject, so they cannot drift apart.
    from unicode_fol_kit.semantics import _modal_reject
    from unicode_fol_kit.semantics import kripke
    from unicode_fol_kit.atp import modal_tableau
    from unicode_fol_kit.hol import intuitionistic
    assert kripke.reject_equality is _modal_reject.reject_equality
    assert kripke.reject_equality_in is _modal_reject.reject_equality_in
    assert modal_tableau.reject_equality_in is _modal_reject.reject_equality_in
    assert intuitionistic.reject_equality is _modal_reject.reject_equality
    # and each one says, by name, which construct it is refusing
    equality = FOLP.parse("a = b")
    for call in (lambda: standard_translation(equality),
                 lambda: kripke.satisfies_modal(
                     equality,
                     kripke.KripkeModel({"w"}, {"alethic": set()}, {"w": set()}),
                     "w"),
                 lambda: modal_tableau.is_modal_valid(equality),
                 lambda: intuitionistic.gmt_translate(equality)):
        with pytest.raises(NotImplementedError, match="refused by name"):
            call()


# ---------------------------------------------------------------------------
# The typed surface
# ---------------------------------------------------------------------------

def test_a_logic_value_wraps_a_term_and_converts_a_sentence():
    wrapped = MODAL(Box(P))
    assert wrapped.logic == "modal" and wrapped.axioms == ()
    converted = FOL(wrapped)
    assert converted.logic == "fol" and converted.path == ("standard_translation",)
    assert converted.term.to_unicode_str() == "∀w0 (R(w, w0) → P(w0))"
    assert FOL(converted) is converted                 # same logic: a no-op


def test_a_sentence_refuses_to_wrap_a_sentence():
    with pytest.raises(TypeError, match="already a Sentence"):
        Sentence(term=MODAL(Box(P)), logic="fol")


def test_building_a_formula_out_of_sentences_is_refused_not_guessed():
    # Not only across logics: within one logic the axioms would simply be
    # dropped, so no operator is defined on a Sentence at all.
    for bad in (lambda: MODAL(Box(P)) & FOL(P),
                lambda: FOL(P) & FOL(Q),
                lambda: FOL(P) | FOL(Q),
                lambda: ~MODAL(Box(P))):
        with pytest.raises(TypeError, match="not defined on a Sentence"):
            bad()


def test_prove_refuses_a_sentence_in_a_logic_it_does_not_decide():
    with pytest.raises(ValueError, match="Sentence in logic 'modal'"):
        api.prove(MODAL(Box(P)))


def test_a_lossy_edge_says_so_on_the_result():
    fuzzy = MSFLParser().parse("P(a)")                 # crisp, but via the edge
    result = DEFAULT_REGISTRY.translate(fuzzy, "fuzzy", "msfol")
    assert result.lossy is True and result.guarantee == "lossy"
    assert "TWO-VALUED PROJECTION" in result.note


def test_a_concept_reaches_fol_and_the_path_is_named():
    from unicode_fol_kit.dl import Atomic, Exists, And as CAnd
    concept = CAnd(Atomic("Human"), Exists("hasChild", Atomic("Doctor")))
    sentence = FOL(ALC(concept))
    assert sentence.path == ("concept_to_fol",)
    assert sentence.term.to_unicode_str() == (
        "Human(x) ∧ ∃x0 (hasChild(x, x0) ∧ Doctor(x0))")
    # The MINTED variable is a name this kit reads back (it used to be "x_1",
    # which its own parser rejects). The ROLE name is the caller's and is
    # printed unchanged, so an OWL-style lower-case role still makes the whole
    # rendering unparsable — a predicate must start upper-case here. That is a
    # property of the caller's vocabulary, not of this translation.
    upper = CAnd(Atomic("Human"), Exists("HasChild", Atomic("Doctor")))
    assert api.parse_any(FOL(ALC(upper)).term.to_unicode_str()).ok
    assert not api.parse_any(sentence.term.to_unicode_str()).ok


def test_a_concept_with_a_data_restriction_is_refused_by_the_alc_edge():
    # The edge declares `faithful` and carries no side axioms, which is true of a
    # concept WITHOUT a data layer. The image of a data restriction is a guarded
    # ONE-sorted theory whose sorts and datatype lattice are side axioms of a
    # KNOWLEDGE BASE: closed existentially on its own,
    # ∃HasV.xsd:integer ⊓ ∀HasV.xsd:string is satisfiable (a data value satisfies
    # it), where OWL 2 makes it unsatisfiable (the two datatypes are disjoint).
    # So the edge refuses it by name and points at kb_to_fol(..., query=[concept]);
    # RED before: it translated it and declared the result faithful.
    from unicode_fol_kit import dl
    integer, string = dl.Datatype("xsd:integer"), dl.Datatype("xsd:string")
    refused = [
        dl.DataExists("HasV", integer), dl.DataForAll("HasV", string),
        dl.DataHasValue("HasV", dl.Literal("1", "xsd:integer")),
        dl.DataAtLeast(2, "HasV", integer), dl.DataAtMost(1, "HasV", integer),
        dl.And(dl.DataExists("HasV", integer), dl.DataForAll("HasV", string)),
        dl.Exists("r", dl.DataExists("HasV", integer)),
        dl.Not(dl.DataExists("HasV", integer)),
    ]
    for concept in refused:
        with pytest.raises(dl.UnsupportedDatatypeError) as info:
            api.translate(concept, "alc", "fol")
        message = str(info.value)
        assert "HasV" in message and "query=[concept]" in message
        assert "kb.unsatisfiability_goal(concept)" in message
        with pytest.raises(dl.UnsupportedDatatypeError):
            FOL(ALC(concept))
    # what the edge is for is untouched: a concept without a data restriction is
    # still faithful, with no axioms, byte-for-byte the image it always had
    t = api.translate(dl.And(dl.Atomic("Human"), dl.Exists("HasChild", dl.Atomic("Doctor"))),
                      "alc", "fol")
    assert t.guarantee == "faithful" and t.axioms == ()
    assert t.result.to_unicode_str() == "Human(x) ∧ ∃x0 (HasChild(x, x0) ∧ Doctor(x0))"
    # and the knowledge-base route the refusal names answers it
    concept = refused[5]
    kb = dl.kb_to_fol(dl.TBox(), query=[concept])
    assert api.prove(kb.unsatisfiability_goal(concept), list(kb.tbox_premises),
                     timeout=30000).status == "proved"


def test_logics_are_values_with_labels():
    assert str(FOL) == "fol" and isinstance(FOL, Logic)
    assert MSFOL.label == "msfol" and "non-empty" in MSFOL.description
