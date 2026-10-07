"""Many-sorted quantification under modal, second-order, and intuitionistic logic (C3).

``MSFLParser(modal=True, many_sorted=True)`` ("modal_sorted") and
``MSFLParser(second_order=True, many_sorted=True)`` ("so_sorted") both delegate to
:class:`~unicode_logic_kit.fol._msfl_nodes.SortedQuantifier`'s existing ``_relativize``
reduction (``∀x:S φ`` -> ``∀x (S(x) -> φ)``, ``∃x:S φ`` -> ``∃x (S(x) ∧ φ)``) in every
consumer -- the Kripke evaluator (``semantics.kripke.satisfies_modal``), the QML
first-order shallow embedding (``fol.qml``), the HOL exporters
(``hol.isabelle_modal``/``hol.thf_modal``), and the intuitionistic Kripke search
(``semantics.intuitionistic``) -- rather than inventing new per-consumer semantics. Two
SEMANTIC DECISIONS the delegation itself does not make, made and pinned here:

- **Sorts are world/stage-RELATIVE, not rigid.** A sort guard ``S(x)`` becomes an
  ordinary atom once relativized, so it is looked up exactly like any other atom --
  world-relative in Kripke semantics, stage-relative (and hence monotone/up-closed,
  same as every atom in that module) in the intuitionistic search. An individual can be
  ``S`` at one world/stage and not at another. This mirrors the SAME "actualist" choice
  this kit already makes for the bare (unsorted) per-world domain ``D_w``.
- **Non-emptiness is NOT assumed by the evaluator of ONE model; every route that decides
  validity assumes it.** The classical many-sorted routes (``api.prove`` et al.) ALWAYS
  assume every sort is non-empty (``fol.nonempty_sort_axioms``, added as extra premises) -- a
  bare relativisation alone would make ``∀x:S P(x) → ∃x:S P(x)`` classically valid but
  NOT modally/intuitionistically valid, an inconsistency across routes. So:
    * ``satisfies_modal`` never assumes it -- the caller builds a model where each
      sort's guard is true of an individual wherever that matters (documented in
      kripke.py).
    * ``fol.qml`` DOES thread the same non-emptiness assumption in automatically, per
      world (``qml_axioms``), because it already does the analogous thing for the bare
      object domain (``nonempty_dom``).
    * ``semantics.intuitionistic`` DOES thread it in too, as an extra premise
      (``⋀sort-axioms → relativised-formula``), for the same reason.
- **A sorted constant is an element of its sort at EVERY world.** ``c:S`` denotes an element
  of ``S`` and a constant is a rigid designator, so the guard atom ``S(c)`` is true at every
  world of a legal model. ``fol.qml`` (``∀w (World(w) → S(c, w))``), the Isabelle and THF
  exports (an axiom with a free / bound world), ``semantics.intuitionistic`` (an antecedent)
  and ``atp.kripke_enum`` (a fixed atom) assert it; ``satisfies_modal`` evaluates ONE model
  and cannot, so a model that leaves ``S(c)`` out of a world's valuation is illegal --
  ``sorted_constant_violations`` names the worlds. The differential tests below build their
  models that way; ``tests/test_sorted_membership_modal.py`` pins the membership itself.
  This file's differential batteries are built to make this design pinned and visible,
  not just "does it crash".

Four independent-route checks run through this file, matching the test_oracle:
    1. Parser round-trips (to_unicode_str / to_dict, structural AST checks).
    2. Kripke evaluator: hand-built models, hand-checked truth values, PLUS the
       "delegates to its own relativisation" wiring pin.
    3. QML (``qml_is_valid``) cross-checked against ``satisfies_modal`` on matching
       hand-built Kripke models, and against ``api.prove`` on modal-free formulas.
    4. Intuitionistic (``int_valid``/``int_countermodel``) cross-checked against
       ``api.prove`` (every formula both fragments decide, they must agree on --
       intuitionistic validity implies classical validity, and the non-emptiness
       wrapping keeps the two conventions aligned on the battery below).
    5. Second-order+many-sorted cross-checked against
       ``semantics.secondorder.satisfies_so``'s brute-force finite evaluator.
    6. HOL export smoke tests (sort predicate appears correctly in the signature).
    7. Refusal battery: what STILL does not combine (fuzzy; third_order+many_sorted).
"""

import pytest

from unicode_logic_kit import api
from unicode_logic_kit.fol.msflparser import MSFLParser
from unicode_logic_kit.fol.nodes import (
    Node, Atom, Implies, And, Or, Not, Quantifier, SortedQuantifier,
    Variable, Constant, SortedConstant, Box, Knows,
)
from unicode_logic_kit.semantics.kripke import KripkeModel, satisfies_modal
from unicode_logic_kit.semantics.intuitionistic import int_valid, int_countermodel
from unicode_logic_kit.semantics.tarski import IllegalStructureError, Structure
from unicode_logic_kit.semantics.secondorder import satisfies_so
from unicode_logic_kit.fol.qml import qml_is_valid, qml_translate
from unicode_logic_kit.hol.isabelle_modal import to_isabelle_modal, modal_axiom_names
from unicode_logic_kit.hol.thf_modal import to_thf_modal_full


# =============================================================================
# 1. Parser: modal + many_sorted ("modal_sorted")
# =============================================================================

class TestModalSortedParser:
    def test_box_over_sorted_universal(self):
        """□∀x:Human Mortal(x) -- textbook sorted-necessity sentence."""
        p = MSFLParser(modal=True, many_sorted=True)
        f = p.parse("□∀x:Human (Mortal(x))")
        assert isinstance(f, Box)
        assert isinstance(f.formula, SortedQuantifier)
        assert f.formula.sort == "Human"
        assert f.to_unicode_str() == "□∀x:Human Mortal(x)"

    def test_epistemic_over_sorted_existential_and_agent(self):
        """K_a ∃x:Human Likes(x, a) -- typed agent under an epistemic operator,
        the worked example the roadmap batch note asks for."""
        p = MSFLParser(modal=True, many_sorted=True)
        f = p.parse("K_a ∃x:Human Likes(x, a)")
        assert isinstance(f, Knows)
        assert f.agent == Constant("a")   # free agent variable demoted (resolve_agent_variables)
        assert isinstance(f.formula, SortedQuantifier)

    def test_two_sorts_disjoint_domain(self):
        """A two-sort example: quantifier alternation across Human/Animal."""
        p = MSFLParser(modal=True, many_sorted=True)
        f = p.parse("∀x:Human ◇∃y:Animal (Likes(x, y))")
        assert isinstance(f, SortedQuantifier) and f.sort == "Human"

    def test_sorted_constant_of_a_sort(self):
        p = MSFLParser(modal=True, many_sorted=True)
        f = p.parse("□Mortal(alice:Human)")
        assert f.to_unicode_str() == "□Mortal(alice:Human)"

    def test_unsorted_quantifier_still_refused(self):
        """many_sorted's own invariant (every binder needs a sort) still holds
        combined with modal -- the parser must not silently widen to accept
        ∀x with no annotation."""
        p = MSFLParser(modal=True, many_sorted=True)
        with pytest.raises(Exception):
            p.parse("□∀x (Mortal(x))")

    def test_round_trip_dict_and_unicode(self):
        p = MSFLParser(modal=True, many_sorted=True)
        f = p.parse("□∀x:Human (Mortal(x) → ◇∃y:Animal Likes(x, y))")
        assert Node.from_dict(f.to_dict()) == f
        assert p.parse(f.to_unicode_str()) == f

    def test_earley_fallback_shape_matches_plain_modal(self):
        """The documented LALR/Earley bracket-nominal ambiguity (_HYBRID_MODES)
        is inherited unchanged by modal_sorted: same shape, same AST as plain
        modal mode gets for the identical propositional core (see
        tests/test_modal_lalr_fallback.py's SORTED_ADVERSARIAL_CORPUS for the
        systematic version of this check)."""
        p_modal = MSFLParser(modal=True)
        p_sorted = MSFLParser(modal=True, many_sorted=True)
        assert repr(p_modal.parse("◇(p∧q)")) == repr(p_sorted.parse("◇(p∧q)"))


# =============================================================================
# 1b. Parser: second_order + many_sorted ("so_sorted")
# =============================================================================

class TestSoSortedParser:
    def test_predicate_quantifier_over_sorted_individuals(self):
        p = MSFLParser(second_order=True, many_sorted=True)
        f = p.parse("∀P (∀x:Human P(x) → ∃x:Human P(x))")
        assert f.to_unicode_str() == "∀P (∀x:Human P(x) → ∃x:Human P(x))"

    def test_round_trip(self):
        p = MSFLParser(second_order=True, many_sorted=True)
        f = p.parse("∃P (∀x:Human (P(x) ↔ Mortal(x)))")
        assert Node.from_dict(f.to_dict()) == f
        assert p.parse(f.to_unicode_str()) == f

    def test_second_order_quantifier_itself_stays_unsorted(self):
        """The bound PREDICATE variable P has no sort annotation slot in the
        grammar (only the individual binders ∀x/∃x do) -- ∀P: is a syntax
        error, matching plain "so" mode."""
        p = MSFLParser(second_order=True, many_sorted=True)
        with pytest.raises(Exception):
            p.parse("∀P:Human (P(alice:Human))")


# =============================================================================
# 2. Kripke evaluator: hand-built models, hand-checked
# =============================================================================

class TestKripkeSorted:
    def test_universal_sorted_true_and_false(self):
        """Hand-checked: {socrates, plato} both Human; Mortal(socrates) but
        NOT Mortal(plato) -- ∀x:Human Mortal(x) must be False."""
        p = MSFLParser(modal=True, many_sorted=True)
        f = p.parse("∀x:Human Mortal(x)")
        m_true = KripkeModel(
            worlds={0}, domain=["socrates", "plato"],
            valuation={0: {"Human(socrates)", "Human(plato)",
                          "Mortal(socrates)", "Mortal(plato)"}})
        assert satisfies_modal(f, m_true, 0) is True
        m_false = KripkeModel(
            worlds={0}, domain=["socrates", "plato"],
            valuation={0: {"Human(socrates)", "Human(plato)", "Mortal(socrates)"}})
        assert satisfies_modal(f, m_false, 0) is False

    def test_empty_sort_is_vacuously_true_not_assumed_nonempty(self):
        """Pins the "non-emptiness is NOT assumed" design decision directly:
        an empty Human sort makes the universal vacuously True here, unlike
        the classical route (see test_qml_agrees_with_classical_nonempty)."""
        p = MSFLParser(modal=True, many_sorted=True)
        f = p.parse("∀x:Human Mortal(x)")
        m = KripkeModel(worlds={0}, domain=["a"], valuation={0: set()})
        assert satisfies_modal(f, m, 0) is True

    def test_sorts_are_world_relative_not_rigid(self):
        """Hand-checked: alice is Human (and Mortal) at w0, but NOT Human at
        w1 -- □∀x:Human Mortal(x) still holds at w0, because the ONLY witness
        the sort guard has to satisfy at w1 is vacuous (Human is empty
        there)."""
        p = MSFLParser(modal=True, many_sorted=True)
        f = p.parse("□∀x:Human Mortal(x)")
        m = KripkeModel(
            worlds={0, 1}, relations={"alethic": {(0, 0), (0, 1)}},
            domain=["alice"],
            valuation={0: {"Human(alice)", "Mortal(alice)"}, 1: set()})
        assert satisfies_modal(f, m, 0) is True
        # Break it: alice IS Human at w1 there but not Mortal -- now the box fails.
        m2 = KripkeModel(
            worlds={0, 1}, relations={"alethic": {(0, 0), (0, 1)}},
            domain=["alice"],
            valuation={0: {"Human(alice)", "Mortal(alice)"}, 1: {"Human(alice)"}})
        assert satisfies_modal(f, m2, 0) is False

    def test_constant_domain_does_not_make_sort_rigid(self):
        """Hand-checked countermodel: SAME individual d exists at both worlds
        (constant domain), d is Human & P only at the world ◇ reaches -- so
        ◇∃x:Human P(x) is true at w0 but ∃x:Human ◇P(x) is FALSE at w0 (d is
        not Human AT w0, the world the outer existential is evaluated at).
        This is the sorted analogue of the Barcan pattern, and shows sorts
        stay non-rigid even when the OBJECT domain is constant."""
        p = MSFLParser(modal=True, many_sorted=True)
        f = p.parse("◇∃x:Human P(x) → ∃x:Human ◇P(x)")
        m = KripkeModel(
            worlds={0, 1}, relations={"alethic": {(0, 1)}}, domain=["d"],
            valuation={0: set(), 1: {"Human(d)", "P(d)"}})
        assert satisfies_modal(f, m, 0) is False

    def test_delegates_to_its_own_relativization(self):
        """Wiring pin (test_oracle route 1): evaluating a SortedQuantifier
        formula directly must agree with manually relativizing it first and
        evaluating the plain-FOL result -- pins that satisfies_modal really
        does delegate, not reimplement."""
        p = MSFLParser(modal=True, many_sorted=True)
        for text in ("∀x:Human Mortal(x)", "□∃x:Human Likes(x, x)",
                    "K_a ∀x:Human (Mortal(x) → ¬Robot(x))"):
            f = p.parse(text)
            m = KripkeModel(
                worlds={0, 1}, relations={"alethic": {(0, 1)}, "K:a": {(0, 1)}},
                domain=["h1", "h2"],
                valuation={0: {"Human(h1)", "Mortal(h1)", "Likes(h1, h1)"},
                          1: {"Human(h1)", "Human(h2)", "Mortal(h1)", "Mortal(h2)",
                              "Likes(h1, h1)", "Likes(h2, h2)"}})
            direct = satisfies_modal(f, m, 0)
            via_relativize = satisfies_modal(f._relativize([]), m, 0)
            assert direct == via_relativize

    def test_bare_sorted_constant_relativized_not_just_under_a_quantifier(self):
        """A SortedConstant with NO enclosing SortedQuantifier at all (a
        ground fact like "Socrates is Human and Mortal", not a quantified
        claim) must still be relativized -- satisfies_modal relativizes the
        WHOLE formula once, up front, not only when the recursive descent
        happens to walk into a SortedQuantifier node (see the module
        docstring). Hand-checked: the model's valuation has plain
        (non-suffixed) keys "Mortal(alice)"/"Robot(alice)"; if the ":Human"
        suffix were not stripped before the lookup, Atom.to_unicode_str()
        would render "Mortal(alice:Human)", which can never match either
        key -- so BOTH atoms would come out False, not just the Robot one.
        Two different predicates over the same sorted constant is what makes
        this non-tautological (unlike P(alice:Human) <-> P(alice:Human))."""
        p = MSFLParser(modal=True, many_sorted=True)
        f_true = p.parse("Mortal(alice:Human)")
        f_false = p.parse("Robot(alice:Human)")
        m = KripkeModel(worlds={0}, domain=["alice"],
                        valuation={0: {"Human(alice)", "Mortal(alice)"}})
        assert satisfies_modal(f_true, m, 0) is True
        assert satisfies_modal(f_false, m, 0) is False
        # Same pin one level down, under a Box, to confirm relativizing the
        # whole tree also reaches a sorted constant that is NOT the top node.
        m2 = KripkeModel(worlds={0, 1}, relations={"alethic": {(0, 1)}},
                         domain=["alice"],
                         valuation={0: {"Human(alice)"},
                                    1: {"Human(alice)", "Mortal(alice)"}})
        assert satisfies_modal(Box(f_true), m2, 0) is True
        assert satisfies_modal(Box(f_false), m2, 0) is False


# =============================================================================
# 3. QML: differential against satisfies_modal, and against api.prove
# =============================================================================

class TestQmlSorted:
    def test_qml_agrees_with_kripke_barcan_style_countermodel(self):
        """The exact countermodel from test_constant_domain_does_not_make_sort_rigid,
        cross-checked from the OTHER route (Z3-decided validity, constant mode)."""
        p = MSFLParser(modal=True, many_sorted=True)
        f = p.parse("◇∃x:Human P(x) → ∃x:Human ◇P(x)")
        assert qml_is_valid(f, mode="constant") is False

    def test_qml_agrees_with_classical_nonempty_convention(self):
        """qml_axioms' per-world sort non-emptiness makes this schema valid
        here, matching the classical route -- unlike the bare Kripke
        evaluator (test_empty_sort_is_vacuously_true_not_assumed_nonempty),
        which makes NO such assumption by itself."""
        p = MSFLParser(modal=True, many_sorted=True)
        f = p.parse("∀x:Human P(x) → ∃x:Human P(x)")
        assert qml_is_valid(f, mode="constant") is True
        assert qml_is_valid(f, mode="varying") is True
        assert api.prove(f).status == "proved"

    def test_qml_k_axiom_under_sorts(self):
        """□∀x:Human (P(x)→Q(x)) → (□∀x:Human P(x) → □∀x:Human Q(x)) -- the K
        axiom schema, sorted; valid in every normal modal logic."""
        p = MSFLParser(modal=True, many_sorted=True)
        f = p.parse(
            "□∀x:Human (P(x) → Q(x)) → (□∀x:Human P(x) → □∀x:Human Q(x))")
        assert qml_is_valid(f, mode="constant") is True

    def test_qml_translation_sort_guard_is_world_relative(self):
        """The sort guard gets the SAME world-argument-append treatment ST
        gives every other atom (module docstring's "Many-sorted formulas")."""
        p = MSFLParser(modal=True, many_sorted=True)
        f = p.parse("∀x:Human P(x)")
        t = qml_translate(f, mode="constant", world="w")
        assert "Human(x, w)" in t.to_unicode_str()

    def test_qml_sorted_constant_typed_as_object(self):
        """A bare SortedConstant (alice:Human), used with no enclosing
        SortedQuantifier at all, must still be typed Object -- the reason
        _validity_formula relativizes the WHOLE formula once, before
        _signature_typing_facts scans it, rather than scanning the
        original (unrelativized) formula (see qml.py's module docstring
        and _validity_formula's own docstring).

        NOT a self-implication: ``∀x P(x) → P(alice:Human)`` genuinely
        NEEDS ``Object(alice)`` among the axioms to be provable, because
        _st's own Quantifier case guards EVERY object quantifier -- even in
        "constant" mode -- with an ``Object(x)`` premise (qml.py, the
        Quantifier branch of _st). Confirmed directly: calling
        _signature_typing_facts on the UNRELATIVIZED formula (what a
        lazy-relativize bug would hand it) returns no fact for alice at
        all, so this schema would come out spuriously INVALID without the
        fix -- unlike a self-implication f -> f, which needs no witness for
        alice regardless of typing and would stay trivially valid either
        way (the bug this replaces the old test)."""
        x = Variable("x")
        alice = SortedConstant("alice", "Human")
        f = Implies(Quantifier("∀", x, Atom("P", [x])), Atom("P", [alice]))
        assert qml_is_valid(f, mode="constant") is True


# =============================================================================
# 4. Intuitionistic search: cross-checked against api.prove (classical)
# =============================================================================

class TestIntuitionisticSorted:
    def test_sorted_lem_not_intuitionistically_valid(self):
        """Textbook: LEM fails intuitionistically even for a sorted atom --
        classically valid, intuitionistically not."""
        p = MSFLParser(many_sorted=True)
        f = p.parse("P(alice:Human) ∨ ¬P(alice:Human)")
        assert int_valid(f) is False
        assert api.prove(f).status == "proved"
        model, world = int_countermodel(f)
        # int_countermodel's own contract is that ITS returned (model, world)
        # falsifies the WRAPPED/relativized formula it actually searched --
        # the model's valuation is keyed by "P(alice)" (SortedConstant
        # relativized away), not the surface "P(alice:Human)" this test's
        # own `f` still carries, so the equivalent check re-relativizes `f`
        # here (see _prepare_many_sorted's docstring: relativizing an
        # already-plain formula is a no-op, so this is the SAME node the
        # search decided).
        assert model.forces(world, f._relativize([])) is False

    def test_sorted_double_negation_of_lem_is_valid(self):
        """¬¬(P ∨ ¬P) IS intuitionistically valid (only LEM itself, not its
        double negation, fails) -- and classically valid too."""
        p = MSFLParser(many_sorted=True)
        f = p.parse("¬¬(P(alice:Human) ∨ ¬P(alice:Human))")
        assert int_valid(f) is True
        assert api.prove(f).status == "proved"

    def test_nonempty_sort_schema_agrees_with_classical(self):
        """∀x:S P(x) → ∃x:S P(x): a BARE relativisation would find an
        empty-S countermodel here and wrongly return False; the
        non-emptiness premise this module folds in keeps it aligned with
        the classical verdict (see module docstring)."""
        p = MSFLParser(many_sorted=True)
        f = p.parse("∀x:Human P(x) → ∃x:Human P(x)")
        assert int_valid(f) is True
        assert api.prove(f).status == "proved"

    def test_trivial_sorted_tautology(self):
        p = MSFLParser(many_sorted=True)
        f = p.parse("∀x:Human (P(x) → P(x))")
        assert int_valid(f) is True

    def test_two_sort_quantifier_alternation_countermodel(self):
        """∀x:Human ∃y:Animal Likes(x,y) has an obvious countermodel (a Human
        with no Animal it Likes) -- found within a small bound."""
        p = MSFLParser(many_sorted=True)
        f = p.parse("∀x:Human ∃y:Animal Likes(x, y)")
        assert int_countermodel(f, max_worlds=2, domain_elements=1) is not None

    def test_sorted_constant_relativized_everywhere_not_just_under_binder(self):
        """A SortedConstant with no enclosing SortedQuantifier is still
        picked up correctly (relativized once, at the top -- see
        _prepare_many_sorted's docstring).

        Uses TWO DIFFERENT predicates over the same sorted constant
        (``P(alice:Human) → Q(alice:Human)``), not ``P(alice:Human) →
        P(alice:Human)``: the self-implication form holds no matter what
        the two (identical) occurrences reduce to -- even if relativizing
        silently no-op'd, ``A → A`` still holds -- so it has no power to
        detect a regression in the actual relativize-and-type logic. This
        version does: it is genuinely NOT valid (P doesn't entail Q), so
        the search must find a real countermodel, and that countermodel's
        valuation must be keyed by the PLAIN (non-suffixed) atoms
        "P(alice)"/"Q(alice)" -- proving the SortedConstant really was
        stripped before the search ever saw it, not merely that the search
        didn't crash."""
        p = MSFLParser(many_sorted=True)
        f = p.parse("P(alice:Human) → Q(alice:Human)")
        assert int_valid(f) is False
        model, world = int_countermodel(f)
        assert "P(alice)" in model.valuation
        assert "Q(alice)" in model.valuation
        # The countermodel must actually falsify P(alice:Human) → Q(alice:Human):
        # P holds, Q does not, at the returned world.
        assert world in model.valuation["P(alice)"]
        assert world not in model.valuation["Q(alice)"]


# =============================================================================
# 5. second_order + many_sorted: differential against semantics.secondorder
# =============================================================================

class TestSecondOrderSorted:
    def test_agrees_with_brute_force_evaluator_nonempty_sort(self):
        p = MSFLParser(second_order=True, many_sorted=True)
        f = p.parse("∀P (∀x:Human P(x) → ∃x:Human P(x))")
        s = Structure(domain=["h1", "h2", "d1"],
                     sorts={"Human": ["h1", "h2"], "Dog": ["d1"]})
        assert satisfies_so(f, s) is True

    def test_an_empty_sort_is_refused_by_the_brute_force_evaluator(self):
        """Same schema, but Robot is empty. This test used to pin FALSE ("no assumed non-emptiness at
        the raw evaluator level either"), but that answered a question about a structure the
        definition does not have: a sort is the extension of a unary predicate and is never empty, so
        a structure with an empty sort is not a structure of it, and evaluating a formula in it is an
        error naming the sort, not a truth value. (Over the legal structure above the schema is
        TRUE; its falsity needs the empty sort, which no structure of the definition has.)"""
        p = MSFLParser(second_order=True, many_sorted=True)
        f = p.parse("∀P (∀x:Robot P(x) → ∃x:Robot P(x))")
        s = Structure(domain=["h1", "h2"], sorts={"Human": ["h1", "h2"], "Robot": []})
        with pytest.raises(IllegalStructureError, match="'Robot' is empty"):
            satisfies_so(f, s)

    def test_typed_predicate_quantifier_over_two_sorts(self):
        """∃P (∀x:Human P(x) ∧ ∀y:Dog ¬P(y)) -- P separates the two sorts;
        satisfiable on a structure with both sorts present, hand-verified: P
        = {h1, h2} witnesses it."""
        p = MSFLParser(second_order=True, many_sorted=True)
        f = p.parse("∃P (∀x:Human P(x) ∧ ∀y:Dog ¬P(y))")
        s = Structure(domain=["h1", "h2", "d1"],
                     sorts={"Human": ["h1", "h2"], "Dog": ["d1"]})
        assert satisfies_so(f, s) is True


# =============================================================================
# 6. HOL export smoke tests: the sort predicate appears in the signature
# =============================================================================

class TestHolExportsSorted:
    def test_isabelle_declares_the_sort_predicate(self):
        p = MSFLParser(modal=True, many_sorted=True)
        f = p.parse("□∀x:Human (Mortal(x))")
        theory = to_isabelle_modal(f, mode="constant")
        assert 'consts human :: "e' in theory
        assert 'consts mortal :: "e' in theory
        assert "lemma modal_goal:" in theory

    def test_thf_declares_the_sort_predicate(self):
        p = MSFLParser(modal=True, many_sorted=True)
        f = p.parse("□∀x:Human (Mortal(x))")
        thf = to_thf_modal_full(f, mode="constant")
        assert "thf(human_decl, type, ( human : ( $i > mu > $o ) ))." in thf
        assert "thf(mortal_decl, type, ( mortal : ( $i > mu > $o ) ))." in thf

    def test_isabelle_bare_sorted_constant_typed(self):
        """A SortedConstant outside any SortedQuantifier still gets scanned
        correctly (relativized once at the top -- see isabelle_modal_theory's
        comment): it becomes a plain Isabelle constant of type e (SAME
        treatment an ordinary Constant gets) rather than crashing. Its sort
        MEMBERSHIP fact IS asserted: ``alice:Human`` denotes an element of
        ``Human``, so the theory states ``human alice w`` as an axiom (the
        guard declared even though no quantifier ranges over ``Human``).
        The earlier reading of this test -- that a bare sorted constant's
        membership is a fact ``_relativize([])`` collects into a discarded
        list and no route asserts -- made ``∀x:Human Mortal(x) →
        Mortal(alice:Human)`` unprovable here while the classical routes and
        the finite model finder call it valid; a sorted constant that is in
        no sort is just an unsorted one (``tests/test_sorted_membership_modal.py``
        pins the membership on every route)."""
        p = MSFLParser(modal=True, many_sorted=True)
        f = p.parse("□Mortal(alice:Human)")
        theory = to_isabelle_modal(f, mode="constant")
        assert 'consts alice :: "e"' in theory
        assert 'consts mortal :: "e' in theory
        assert "mortal alice" in theory
        assert 'consts human :: "e' in theory
        assert 'axiomatization where sort_member0: "human alice w"' in theory

    def test_hol_exports_state_the_sort_is_non_empty(self):
        """Both HOL exports carry the SAME non-emptiness convention as the rest.

        ``fol._msfl_nodes.nonempty_sort_axioms`` makes every sort non-empty for
        the classical routes, and ``fol.qml.qml_axioms`` /
        ``semantics.intuitionistic`` state the per-world version. Relativization
        leaves the sort guard an ordinary world-relative atom, so WITHOUT a
        matching axiom the emitted problems would not prove
        ``∀x:S P(x) → ∃x:S P(x)``, which ``api.prove`` calls valid -- a route
        disagreeing with the classical verdict on a MODAL-FREE sorted formula.
        ``w`` is free in the Isabelle line (implicitly universally quantified
        over worlds) and explicitly bound in the THF one, so the sort is
        non-empty at every world, not just somewhere.
        """
        p = MSFLParser(many_sorted=True)
        f = p.parse("∀x:Human P(x) → ∃x:Human P(x)")
        assert api.prove(f).status == "proved"          # the verdict to match

        theory = to_isabelle_modal(f, mode="constant")
        assert (r'axiomatization where nonempty_sort0: "\<exists>x. human x w"'
                in theory)
        assert "nonempty_sort0" in modal_axiom_names(f)
        thf = to_thf_modal_full(f, mode="constant")
        assert ("thf(nonempty_sort0, axiom, ( ! [W: mu] : ? [X: $i] : "
                "( human @ X @ W ) )).") in thf

    def test_actualist_mode_sort_witness_must_exist_at_the_world(self):
        """Under a varying domain the witness is ``existsAt``-guarded too.

        ``mexists`` only ranges over the local domain, so a sort witness
        outside it could not instantiate the existential and the axiom would
        not restore the entailment -- the same reason ``fol.qml.qml_axioms``
        conjoins ``E(x, w)`` into its own per-world sort witness.
        """
        p = MSFLParser(many_sorted=True)
        f = p.parse("∀x:Human P(x) → ∃x:Human P(x)")
        theory = to_isabelle_modal(f, mode="varying")
        assert (r'axiomatization where nonempty_sort0: '
                r'"\<exists>x. existsAt x w \<and> human x w"') in theory
        thf = to_thf_modal_full(f, mode="varying")
        assert ("thf(nonempty_sort0, axiom, ( ! [W: mu] : ? [X: $i] : "
                "( ( existsAt @ X @ W ) & ( human @ X @ W ) ) )).") in thf

    def test_two_sorts_get_one_axiom_each_and_unsorted_gets_none(self):
        p = MSFLParser(modal=True, many_sorted=True)
        f = p.parse("∀x:Human ∃y:Animal Likes(x, y)")
        names = modal_axiom_names(f)
        assert [n for n in names if n.startswith("nonempty_sort")] == [
            "nonempty_sort0", "nonempty_sort1"]
        plain = MSFLParser(modal=True).parse("□∀x (P(x))")
        assert "nonempty_sort" not in to_isabelle_modal(plain)
        assert "nonempty_sort" not in to_thf_modal_full(plain)

    def test_identity_under_sorted_quantifiers_stays_rigid_identity(self):
        """Relativization turns the sort into a WORLD-RELATIVE guard atom and leaves the
        identity atom alone: ``x = y`` stays rigid (HOL's own ``=``, no world argument,
        nothing declared for it) next to the world-relative ``human`` guards, in both
        exports -- the reading ``qml_is_valid`` has, which judges this schema valid
        (the sort is non-empty at every world, and ``y := x`` witnesses it)."""
        p = MSFLParser(modal=True, many_sorted=True)
        f = p.parse("∀x:Human ∃y:Human (x = y)")
        assert qml_is_valid(f, mode="constant") is True

        theory = to_isabelle_modal(f, mode="constant")
        assert (r"(mforall (\<lambda>x. (mimp (human x) (mexists (\<lambda>y. "
                r"(mand (human y) (\<lambda>_. x = y)))))))") in theory
        assert "feq" not in theory

        thf = to_thf_modal_full(f, mode="constant")
        assert ("( mforall @ ( ^ [X: $i] : ( mimplies @ ( human @ X ) @ "
                "( mexists @ ( ^ [Y: $i] : ( mand @ ( human @ Y ) @ "
                "( meq @ X @ Y ) ) ) ) ) )") in thf
        assert "feq" not in thf and "thf(feq_decl" not in thf


# =============================================================================
# 7. Refusal battery: what still does NOT combine
# =============================================================================

class TestRefusals:
    def test_modal_fuzzy_still_refused(self):
        with pytest.raises(ValueError, match="fuzzy"):
            MSFLParser(modal=True, fuzzy=True)

    def test_modal_sorted_fuzzy_still_refused(self):
        with pytest.raises(ValueError, match="fuzzy"):
            MSFLParser(modal=True, many_sorted=True, fuzzy=True)

    def test_second_order_fuzzy_still_refused(self):
        with pytest.raises(ValueError, match="fuzzy"):
            MSFLParser(second_order=True, fuzzy=True)

    def test_second_order_modal_still_refused(self):
        """The one combination C3 explicitly does not add: second_order and
        modal TOGETHER (with or without many_sorted) -- use third_order for
        that, unaffected by this change."""
        with pytest.raises(ValueError, match="modal"):
            MSFLParser(second_order=True, modal=True)
        with pytest.raises(ValueError, match="modal"):
            MSFLParser(second_order=True, modal=True, many_sorted=True)

    def test_third_order_many_sorted_still_refused(self):
        """Explicitly out of C3's scope -- third-order's slot inference vs.
        sorts needs its own design pass."""
        with pytest.raises(ValueError, match="many_sorted"):
            MSFLParser(third_order=True, many_sorted=True)
        with pytest.raises(ValueError, match="many_sorted"):
            MSFLParser(third_order=True, modal=True, many_sorted=True)
