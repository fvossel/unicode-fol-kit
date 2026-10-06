"""A sorted constant is an element of its sort, on the modal, intuitionistic and higher-order routes.

The reading every many-sorted route of the kit shares: there is ONE universe; a sort ``S`` is the
extension of the unary predicate ``S`` (the sort and the predicate of that name are one symbol) and is
never empty; a sorted constant ``c:S`` denotes an element of ``S``; an UNSORTED constant, an unsorted
variable and the value of a function may be any element. On a modal route a constant is a rigid
designator, so ``S(c)`` holds at EVERY world, and it is not guarded by existence (a constant may lie
outside the domain of a world; that is the modal reading of constants this kit documents).

The three formulas used throughout, with ``socrates`` sorted::

    P1  ∀x:Human Mortal(x) → Mortal(socrates:Human)
    M1  □∀x:Human Mortal(x) → □Mortal(socrates:Human)
    M2  ∀x:Human □Mortal(x) → □Mortal(socrates:Human)

and their two weakenings: the TWIN (``∀x Mortal(x) → Mortal(socrates)``, no annotation anywhere) and the
formula with the sorted quantifier but an UNSORTED ``socrates`` (``∀x:Human Mortal(x) →
Mortal(socrates)``). By the reading above:

* P1 is valid exactly where its twin is: with a constant domain every object exists everywhere,
  ``socrates`` is a ``Human`` at every world, so every ``Human`` being ``Mortal`` makes it ``Mortal``;
  with a varying domain ``socrates`` may lie outside the world's domain and the instance is not
  available (the twin has the same countermodel). The same for M1 and M2.
* with an unsorted ``socrates`` nothing says it is a ``Human``: the universe ``{socrates, d}`` with
  ``Human = {d}``, ``Mortal = {d}`` is a countermodel in every frame and every domain regime.
"""

import itertools
import re

import pytest

from unicode_fol_kit.atp.kripke_enum import KripkeEnumBackend, modal_enum_search
from unicode_fol_kit.atp.lj import int_decide, int_prove
from unicode_fol_kit.atp.modal_tableau import (
    is_modal_valid, modal_countermodel, modal_decide, modal_prove, modal_tableau_closed,
)
from unicode_fol_kit.atp.protocol import REFUTED
from unicode_fol_kit.comorphism import DEFAULT_REGISTRY
from unicode_fol_kit.fol.msflparser import MSFLParser
from unicode_fol_kit.fol.nodes import (
    Atom, Constant, Implies, Not, Or, Quantifier, SortedConstant, SortedQuantifier,
    Variable, Box, Diamond, And, to_fol,
)
from unicode_fol_kit.fol.qml import qml_axioms, qml_is_valid
from unicode_fol_kit.hol import lean
from unicode_fol_kit.hol.classical import to_thf_fol, to_thf_msfol, to_isabelle_msfol
from unicode_fol_kit.hol.intuitionistic import gmt_is_s4_valid, gmt_validity_matches_int_valid
from unicode_fol_kit.hol.isabelle_modal import isabelle_modal_theory, modal_axiom_names
from unicode_fol_kit.hol.thf_modal import to_thf_modal_full
from unicode_fol_kit.semantics.intuitionistic import int_countermodel, int_valid
from unicode_fol_kit.semantics.kripke import (
    KripkeModel, satisfies_modal, sorted_constant_violations,
)
_SORTED = MSFLParser(modal=True, many_sorted=True)

_TEXT = {
    "P1": "∀x:Human Mortal(x) → Mortal(socrates:Human)",
    "M1": "□∀x:Human Mortal(x) → □Mortal(socrates:Human)",
    "M2": "∀x:Human □Mortal(x) → □Mortal(socrates:Human)",
}
FORMULAS = sorted(_TEXT)
FRAMES = ("K", "T", "S4", "S5")
MODES = ("constant", "varying", "increasing", "decreasing")


def _drop_annotations(node, quantifiers):
    """``node`` with every sorted constant plain; with ``quantifiers`` every sorted quantifier plain too."""
    if isinstance(node, SortedConstant):
        return Constant(node.name)
    if quantifiers and isinstance(node, SortedQuantifier):
        return Quantifier(node.type, node.variable,
                          _drop_annotations(node.formula, quantifiers))
    return node.map_children(lambda child: _drop_annotations(child, quantifiers))


def sorted_formula(name):
    return _SORTED.parse(_TEXT[name])


def twin(name):
    """The formula with no annotation at all."""
    return _drop_annotations(sorted_formula(name), True)


def unsorted_socrates(name):
    """The sorted quantifier, but ``socrates`` carries no sort."""
    return _drop_annotations(sorted_formula(name), False)


def mortal_of(term):
    return Atom("Mortal", [term])


# =============================================================================
# fol.qml: the membership axiom
# =============================================================================

class TestQmlMembershipAxiom:
    @pytest.mark.parametrize("name", FORMULAS)
    def test_a_sorted_constant_is_decided_like_its_unsorted_twin_in_every_frame_and_mode(self, name):
        """Hand-derived (module docstring): valid with a constant domain, not valid with a varying one.

        Varying / increasing / decreasing: one reflexive world ``w``, domain ``{d}``, ``Human = {socrates,
        d}`` (so ``socrates`` IS a Human, and the sort is non-empty at ``w`` through ``d``), ``Mortal =
        {d}``. ``∀x:Human Mortal(x)`` holds at ``w`` (the only existing Human is ``d``), ``Mortal(socrates)``
        does not, so P1 fails; ``□`` and the quantifier-then-box shape of M1 / M2 fail the same way, and the
        frame is reflexive, so the model is a K, T, S4 and S5 model alike. The twin has the same
        countermodel with the annotations dropped, which is why the verdicts must be equal.
        """
        for frame in FRAMES:
            for mode in MODES:
                expected = mode == "constant"
                assert qml_is_valid(twin(name), mode=mode, frame=frame) is expected, (name, frame, mode)
                assert qml_is_valid(sorted_formula(name), mode=mode, frame=frame) is expected, (
                    name, frame, mode)

    @pytest.mark.parametrize("name", FORMULAS)
    def test_an_unsorted_socrates_stays_invalid_in_every_frame_and_mode(self, name):
        """Countermodel (module docstring): the universe ``{socrates, d}``, one reflexive world whose
        domain is the whole universe, ``Human = {d}``, ``Mortal = {d}``: every Human is Mortal, and
        ``socrates`` is no Human and not Mortal. Nothing in the formula puts ``socrates`` in Human."""
        for frame in FRAMES:
            for mode in MODES:
                assert qml_is_valid(unsorted_socrates(name), mode=mode, frame=frame) is False, (
                    name, frame, mode)

    def test_possibilist_and_cumulative_are_the_constant_and_the_increasing_regime(self):
        f = sorted_formula("P1")
        assert qml_is_valid(f, mode="possibilist") is True
        assert qml_is_valid(f, mode="cumulative") is False

    def test_the_axiom_is_rigid_and_not_guarded_by_existence(self):
        """``∀w (World(w) → Human(socrates, w))``, in the constant AND in the actualist regime.

        An existence-guarded form (``E(socrates, w) → Human(socrates, w)``) would change no verdict in
        the constant regime (``E`` is not forced there) and would make the actualist verdicts depend on
        where the constant exists; the rigid one is what the unsorted twin's behaviour requires.
        """
        w = Variable("w")
        expected = Quantifier("∀", w, Implies(
            Atom("World", [w]), Atom("Human", [Constant("socrates"), w])))
        for mode in ("constant", "varying", "increasing", "decreasing"):
            axioms = qml_axioms(mode, "K", formula=sorted_formula("P1"))
            assert axioms.count(expected) == 1, mode
        # no sorted constant, no membership axiom: the list is what it was
        none = qml_axioms("constant", "K", formula=twin("P1"))
        assert not any("socrates" in a.to_unicode_str() for a in none)

    def test_membership_holds_at_every_world_whatever_the_domain_regime(self):
        """``Human(socrates:Human)`` is valid in every regime, and so is ``□Human(socrates:Human)`` in K:
        the membership is a fact about the constant, not about any world's domain."""
        atom = Atom("Human", [SortedConstant("socrates", "Human")])
        for mode in MODES:
            assert qml_is_valid(atom, mode=mode) is True, mode
            assert qml_is_valid(Box(atom), mode=mode) is True, mode
        # ... and it is a fact about THAT constant only: a plain one is no Human
        assert qml_is_valid(Atom("Human", [Constant("socrates")]), mode="constant") is False

    def test_a_constant_with_two_sorts_lies_in_both(self):
        """``P(carl:A) ∧ Q(carl:B) → ∃x:A Q(x)``: carl is in A and Q(carl), so some A is Q. Valid with a
        constant domain (carl exists at every world); with a varying domain carl may lie outside the
        world's domain, so the existential has no witness there."""
        f = _SORTED.parse("P(carl:A) ∧ Q(carl:B) → ∃x:A Q(x)")
        assert qml_is_valid(f, mode="constant") is True
        assert qml_is_valid(f, mode="varying") is False

    def test_a_sort_named_like_an_internal_predicate_keeps_its_membership_axiom(self):
        """The guard of a sort named ``E`` (the existence predicate) is renamed like every user predicate
        of that name, and the membership axiom is stated over the renamed guard: the instance of the
        universal at the constant is available in the constant regime."""
        f = _SORTED.parse("∀x:E Mortal(x) → Mortal(socrates:E)")
        assert qml_is_valid(f, mode="constant") is True
        assert qml_is_valid(_drop_annotations(f, False), mode="constant") is False

    def test_a_sort_and_the_predicate_of_that_name_are_one_symbol(self):
        """``Mortal(socrates:Human) → Human(socrates)``: ``socrates`` is in Human, and ``Human`` the
        predicate is the very set ``Human`` the sort names. Valid; with an UNSORTED ``socrates`` it is not."""
        sorted_f = Implies(mortal_of(SortedConstant("socrates", "Human")),
                           Atom("Human", [Constant("socrates")]))
        assert qml_is_valid(sorted_f, mode="constant") is True
        assert qml_is_valid(_drop_annotations(sorted_f, False), mode="constant") is False

    def test_the_qml_edge_of_the_comorphism_registry_carries_the_membership_axiom(self):
        result = DEFAULT_REGISTRY.translate(sorted_formula("P1"), "qml", "fol", mode="constant")
        texts = [axiom.to_unicode_str() for axiom in result.axioms]
        assert "∀w (World(w) → Human(socrates, w))" in texts


# =============================================================================
# semantics.kripke: membership is a property of the model
# =============================================================================

_DOMAIN = frozenset({"socrates", "d"})


def _valuations(fixed=()):
    """Every assignment of the four ground atoms to one world, with the atoms of ``fixed`` true."""
    atoms = ("Human(socrates)", "Human(d)", "Mortal(socrates)", "Mortal(d)")
    free = [a for a in atoms if a not in fixed]
    for bits in itertools.product((False, True), repeat=len(free)):
        yield frozenset(a for a, bit in zip(free, bits) if bit) | frozenset(fixed)


def _two_world_models(fixed=()):
    """Every two-world model over the constant domain ``{socrates, d}``: 16 alethic relations times
    every valuation of the four ground atoms at each world (the atoms of ``fixed`` true everywhere)."""
    edges = [(0, 0), (0, 1), (1, 0), (1, 1)]
    for mask in range(16):
        relation = {e for i, e in enumerate(edges) if (mask >> i) & 1}
        for v0 in _valuations(fixed):
            for v1 in _valuations(fixed):
                yield KripkeModel(worlds={0, 1}, relations={"alethic": relation},
                                  valuation={0: v0, 1: v1}, domain=_DOMAIN)


def _one_world_model(true_atoms, domain):
    return KripkeModel(worlds={0}, relations={"alethic": {(0, 0)}},
                       valuation={0: set(true_atoms)}, domains={0: set(domain)})


class TestKripkeLegalModels:
    @pytest.mark.parametrize("name", FORMULAS)
    def test_the_formula_holds_in_every_legal_two_world_constant_domain_model(self, name):
        """Hand-derived: ``Human(socrates)`` at every world and ``socrates`` in every domain. P1: if every
        existing Human is Mortal then so is ``socrates``, a Human that exists. M1: the same at every
        successor, where ``∀x:Human Mortal(x)`` holds. M2: the instance of the outer quantifier at
        ``socrates`` (a Human at this world, existing here) is ``□Mortal(socrates)``. All 1024 models."""
        f = sorted_formula(name)
        count = 0
        for model in _two_world_models(fixed=("Human(socrates)",)):
            assert sorted_constant_violations(f, model) == []
            assert all(satisfies_modal(f, model, w) for w in (0, 1))
            count += 1
        assert count == 1024      # 16 relations x 8 x 8 valuations

    @pytest.mark.parametrize("name", FORMULAS)
    def test_an_illegal_model_is_the_only_kind_that_refutes_it(self, name):
        """The model with ``Human`` and ``Mortal`` empty at its one reflexive world falsifies each
        formula: the premise is vacuous and ``Mortal(socrates)`` is false. It is no model of the
        many-sorted reading: ``socrates`` is not in ``Human`` there."""
        f = sorted_formula(name)
        model = _one_world_model((), _DOMAIN)
        assert satisfies_modal(f, model, 0) is False
        assert sorted_constant_violations(f, model) == [("socrates", "Human", 0)]

    @pytest.mark.parametrize("name", FORMULAS)
    def test_a_legal_model_with_the_constant_outside_the_domain_refutes_it(self, name):
        """The actualist side: one reflexive world with domain ``{d}``, ``Human = {socrates, d}`` (legal:
        socrates is a Human; the sort is non-empty at the world through ``d``), ``Mortal = {d}``. Every
        existing Human is Mortal; ``Mortal(socrates)`` is false. The unsorted twin has this very
        countermodel, so the model finder, ``qml_is_valid`` and this evaluator agree."""
        f = sorted_formula(name)
        model = _one_world_model(("Human(socrates)", "Human(d)", "Mortal(d)"), {"d"})
        assert sorted_constant_violations(f, model) == []
        assert satisfies_modal(f, model, 0) is False

    @pytest.mark.parametrize("name", FORMULAS)
    def test_an_unsorted_socrates_has_a_legal_countermodel_over_the_constant_domain(self, name):
        """No sorted constant, so every model is legal. ``Human = {d}``, ``Mortal = {d}``, domain
        ``{socrates, d}``: every Human is Mortal, ``socrates`` is not."""
        f = unsorted_socrates(name)
        model = _one_world_model(("Human(d)", "Mortal(d)"), _DOMAIN)
        assert sorted_constant_violations(f, model) == []
        assert satisfies_modal(f, model, 0) is False


class TestSortedConstantViolations:
    def test_it_lists_the_worlds_that_lack_the_guard_atom(self):
        f = _SORTED.parse("□Mortal(socrates:Human)")
        model = KripkeModel(worlds={0, 1, 2}, relations={"alethic": {(0, 1), (0, 2)}},
                            valuation={0: {"Human(socrates)"}, 1: set(), 2: {"Mortal(socrates)"}})
        assert sorted_constant_violations(f, model) == [
            ("socrates", "Human", 1), ("socrates", "Human", 2)]

    def test_it_reports_one_entry_per_constant_and_sort_in_first_occurrence_order(self):
        """``carl`` in two sorts is two facts; the same ``c:S`` written twice is one."""
        f = _SORTED.parse("P(carl:A) ∧ Q(carl:B) ∧ P(carl:A)")
        model = KripkeModel(worlds={0}, valuation={0: set()})
        assert sorted_constant_violations(f, model) == [("carl", "A", 0), ("carl", "B", 0)]

    def test_a_legal_model_and_a_formula_without_sorted_constants_have_none(self):
        f = _SORTED.parse("□Mortal(socrates:Human)")
        legal = KripkeModel(worlds={0, 1}, valuation={0: {"Human(socrates)"}, 1: {"Human(socrates)"}})
        assert sorted_constant_violations(f, legal) == []
        # a sorted QUANTIFIER alone asserts nothing about any constant
        quantified = _SORTED.parse("∀x:Human Mortal(x)")
        assert sorted_constant_violations(quantified, KripkeModel(worlds={0})) == []
        assert sorted_constant_violations(mortal_of(Constant("socrates")), KripkeModel(worlds={0})) == []


# =============================================================================
# atp.kripke_enum: the atoms varied are the atoms the evaluator reads
# =============================================================================

class TestKripkeEnumSortedConstants:
    def test_a_satisfiable_sorted_atom_is_refuted_instead_of_exhausted(self):
        """``¬Mortal(socrates:Human)`` is not valid: one world where ``socrates`` is a Human and Mortal.
        The search used to key the atom ``Mortal(socrates:Human)`` while the evaluator reads
        ``Mortal(socrates)``, never varied the one it read, and claimed an exhausted search."""
        f = Not(mortal_of(SortedConstant("socrates", "Human")))
        result = modal_enum_search(f, frame="K", max_worlds=2)
        assert result.model is not None and result.exhausted is False
        assert satisfies_modal(f, result.model, 0) is False
        assert "Mortal(socrates)" in result.model.valuation[0]
        assert sorted_constant_violations(f, result.model) == []

    def test_the_membership_atom_is_true_at_every_world_of_every_candidate(self):
        """``◇Mortal(carl:Human) → Mortal(carl:Human)`` has the two-world countermodel 0 -> 1 with
        ``Mortal(carl)`` only at 1; ``Human(carl)`` is at both worlds, never varied."""
        carl = SortedConstant("carl", "Human")
        f = Implies(Diamond(mortal_of(carl)), mortal_of(carl))
        result = modal_enum_search(f, frame="K", max_worlds=3)
        model = result.model
        assert model is not None
        assert satisfies_modal(f, model, 0) is False
        assert sorted_constant_violations(f, model) == []
        assert all("Human(carl)" in model.valuation[w] for w in model.worlds)

    def test_a_valid_sorted_formula_is_exhausted_without_a_countermodel(self):
        """``Human(carl:Human)`` is valid (membership), ``Mortal(carl:Human) → Mortal(carl)`` is valid
        (one atom). Both searches run to the end and find nothing."""
        carl = SortedConstant("carl", "Human")
        for valid in (Atom("Human", [carl]),
                      Implies(mortal_of(carl), mortal_of(Constant("carl")))):
            result = modal_enum_search(valid, frame="K", max_worlds=2)
            assert result.model is None and result.exhausted is True
            assert result.checked > 0

    def test_a_box_of_a_sorted_atom_needs_a_reflexive_frame_to_be_valid(self):
        """``□Mortal(c:Human) → Mortal(c:Human)``: refuted in K (a dead-end world makes the box vacuous,
        ``Mortal`` false), valid in T (every enumerated frame is reflexive)."""
        carl = SortedConstant("carl", "Human")
        f = Implies(Box(mortal_of(carl)), mortal_of(carl))
        assert modal_enum_search(f, frame="K", max_worlds=2).model is not None
        t = modal_enum_search(f, frame="T", max_worlds=2)
        assert t.model is None and t.exhausted is True

    def test_the_backend_refutes_a_satisfiable_sorted_atom(self):
        f = Not(mortal_of(SortedConstant("socrates", "Human")))
        verdict = KripkeEnumBackend().decide(f)
        assert verdict.status == REFUTED

    def test_a_sorted_quantifier_is_still_reported_unsupported(self):
        """The enumerated models carry no object domains, so a quantifier is out of scope, sorted or not."""
        result = modal_enum_search(_SORTED.parse("∀x:Human Mortal(x)"), max_worlds=2)
        assert result.model is None and result.unsupported is not None

    def test_an_unsorted_formula_is_searched_as_before(self):
        """The control: with a plain ``socrates`` the first candidates are the same as ever."""
        result = modal_enum_search(Not(mortal_of(Constant("socrates"))), frame="K", max_worlds=2)
        assert result.model is not None and result.checked == 2
        assert result.model.valuation[0] == {"Mortal(socrates)"}


# =============================================================================
# semantics.intuitionistic and atp.lj
# =============================================================================

class TestIntuitionisticMembership:
    def test_the_instance_at_a_sorted_constant_is_valid_and_at_a_plain_one_is_not(self):
        """P1 is intuitionistically valid: at any stage that forces ``∀x(Human(x) → Mortal(x))`` and
        ``Human(socrates)`` (forced at every stage, being monotone), the instance at ``socrates`` gives
        ``Mortal(socrates)``. With a plain ``socrates`` the stage forcing ``Human(d)``, ``Mortal(d)`` and
        neither atom of ``socrates`` refutes it. Bounded search: no countermodel up to two stages and two
        elements is the verdict ``True`` here (the bounds the default of three stages repeats)."""
        p1 = sorted_formula("P1")
        assert int_valid(p1, max_worlds=2, domain_elements=2) is True
        assert int_valid(_drop_annotations(p1, True), max_worlds=2, domain_elements=2) is True
        assert int_valid(unsorted_socrates("P1"), max_worlds=2, domain_elements=2) is False

    def test_membership_is_valid_and_a_sorted_atom_alone_is_not(self):
        socrates = SortedConstant("socrates", "Human")
        assert int_valid(Atom("Human", [socrates])) is True
        assert int_valid(mortal_of(socrates)) is False

    def test_the_godel_translation_into_s4_agrees_on_sorted_ground_atoms(self):
        """Hand-derived: ``Human(s:Human)`` and ``Mortal(s:Human) → Human(s:Human)`` are valid (membership
        holds at every stage); ``Mortal(s:Human)`` and ``Human(s)`` with a plain ``s`` are not. The Z3 route
        over S4 reads the same membership as an axiom, so the two sides of the cross-check agree."""
        s, plain = SortedConstant("socrates", "Human"), Constant("socrates")
        expected = [(_human(s), True), (Implies(mortal_of(s), _human(s)), True),
                    (Implies(mortal_of(s), mortal_of(plain)), True),
                    (mortal_of(s), False), (_human(plain), False)]
        for formula, valid in expected:
            assert int_valid(formula, max_worlds=2) is valid, formula.to_unicode_str()
            assert gmt_is_s4_valid(formula) is valid, formula.to_unicode_str()
        assert gmt_validity_matches_int_valid(_human(s), max_worlds=2) is True

    def test_the_countermodel_of_a_sorted_ground_atom_is_a_model_of_the_membership(self):
        """``Mortal(c:S) → Q(c:S)`` is not valid; the refuting stage is one where ``S(c)`` holds."""
        carl = SortedConstant("carl", "S")
        f = Implies(mortal_of(carl), Atom("Q", [carl]))
        model, world = int_countermodel(f)
        assert world in model.valuation["S(carl)"]
        assert world in model.valuation["Mortal(carl)"] and world not in model.valuation.get("Q(carl)", set())


class TestG4ipSortedConstants:
    def test_the_annotation_does_not_make_a_second_letter(self):
        """``Mortal(socrates:Human)`` and ``Mortal(socrates)`` are one atom; ``int_valid`` always read
        them so, ``int_prove`` used to read two letters."""
        sorted_atom = mortal_of(SortedConstant("socrates", "Human"))
        plain_atom = mortal_of(Constant("socrates"))
        assert int_prove([], Implies(sorted_atom, plain_atom)) is True
        assert int_prove([], Implies(plain_atom, sorted_atom)) is True
        assert int_prove([plain_atom], sorted_atom) is True
        assert int_prove([sorted_atom], plain_atom) is True
        assert int_valid(Implies(sorted_atom, plain_atom)) is True      # the Kripke search agrees

    def test_membership_is_a_hypothesis_of_the_sequent(self):
        socrates = SortedConstant("socrates", "Human")
        assert int_prove([], Atom("Human", [socrates])) is True
        assert int_decide(Atom("Human", [socrates])) is True
        # ... and it is the ONLY thing that is a hypothesis
        assert int_prove([], mortal_of(socrates)) is False
        assert int_prove([], Atom("Human", [Constant("socrates")])) is False

    def test_excluded_middle_of_a_sorted_atom_is_still_not_provable_and_its_double_negation_is(self):
        atom = mortal_of(SortedConstant("socrates", "Human"))
        assert int_prove([], Or(atom, Not(atom))) is False
        assert int_prove([], Not(Not(Or(atom, Not(atom))))) is True

    def test_a_sorted_quantifier_is_refused_by_name(self):
        with pytest.raises(NotImplementedError, match="quantified"):
            int_prove([], _SORTED.parse("∀x:Human Mortal(x)"))


# =============================================================================
# atp.modal_tableau
# =============================================================================

def _human(term):
    return Atom("Human", [term])


class TestModalTableauSortedConstants:
    CARL = SortedConstant("carl", "Human")
    PLAIN = Constant("carl")

    def test_membership_is_valid_and_so_is_everything_that_forgets_the_annotation(self):
        """Hand-derived: ``carl:Human`` is a Human at every world, so ``Human(carl:Human)`` and
        ``□Human(carl:Human)`` are valid in K, ``Mortal(carl:Human) → Human(carl:Human)`` is valid, and
        ``Mortal(carl:Human)`` and ``Mortal(carl)`` are one letter. The branch for the negation of
        ``Human(carl:Human)`` holds ``¬Human(carl)``, which contradicts the membership letter."""
        carl, plain = self.CARL, self.PLAIN
        for valid in (_human(carl),
                      Box(_human(carl)),
                      Implies(mortal_of(carl), _human(carl)),
                      Implies(Diamond(mortal_of(carl)), Diamond(mortal_of(plain)))):
            assert modal_decide(valid) == "valid", valid.to_unicode_str()
            assert is_modal_valid(valid) is True
            assert modal_countermodel(valid) is None

    def test_a_plain_constant_is_in_no_sort(self):
        """The control: ``Human(carl)`` with an unannotated ``carl`` is falsified by the one-world model with
        an empty valuation. Nothing in the formula says ``carl`` is a Human."""
        assert modal_decide(_human(self.PLAIN)) == "invalid"
        assert modal_prove([], _human(self.PLAIN)) is False
        assert modal_prove([], _human(self.CARL)) is True

    def test_a_satisfiable_sorted_atom_gets_a_countermodel_in_which_the_constant_is_in_its_sort(self):
        """``¬Mortal(carl:Human)`` is false at a world where ``carl`` is a Mortal Human, so it is invalid and
        its countermodel must make ``Human(carl)`` true too: a model without it is not a model of the formula."""
        f = Not(mortal_of(self.CARL))
        assert modal_decide(f) == "invalid"
        model = modal_countermodel(f)
        assert model is not None and satisfies_modal(f, model, 0) is False
        assert sorted_constant_violations(f, model) == []
        assert model.valuation[0] == {"Human(carl)", "Mortal(carl)"}

    def test_the_membership_letter_is_true_at_every_world_of_the_countermodel(self):
        """``◇Mortal(carl:Human) → Mortal(carl:Human)`` fails in K at 0 -> 1 with ``Mortal(carl)`` only at 1;
        ``Human(carl)`` holds at both worlds (a constant is rigid), including the one the branch left bare."""
        f = Implies(Diamond(mortal_of(self.CARL)), mortal_of(self.CARL))
        model = modal_countermodel(f)
        assert model is not None
        assert satisfies_modal(f, model, 0) is False
        assert sorted_constant_violations(f, model) == []
        assert all("Human(carl)" in model.valuation[w] for w in model.worlds)
        assert len(model.worlds) == 2

    def test_a_constant_stays_in_its_sort_at_a_world_reached_by_a_diamond(self):
        """``◇¬Human(carl)`` is unsatisfiable once ``carl:Human`` occurs next to it (the constant is rigid, so
        no world leaves its sort) and satisfiable without that occurrence."""
        carl, plain = self.CARL, self.PLAIN
        assert modal_tableau_closed([Diamond(Not(_human(plain))), mortal_of(carl)]) is True
        assert modal_tableau_closed([Diamond(Not(_human(plain))), mortal_of(plain)]) is False

    def test_frame_conditions_still_apply_to_sorted_atoms(self):
        """``□Mortal(c:Human) → Mortal(c:Human)`` is the T axiom: invalid in K (a dead-end world), valid in T."""
        f = Implies(Box(mortal_of(self.CARL)), mortal_of(self.CARL))
        assert modal_decide(f, frame="K") == "invalid"
        assert modal_decide(f, frame="T") == "valid"

    def test_a_formula_without_a_sorted_constant_is_searched_as_before(self):
        p = Atom("P", [])
        assert modal_decide(Implies(Box(p), p)) == "invalid"
        assert modal_decide(Implies(Box(p), p), frame="T") == "valid"

    @pytest.mark.parametrize("make", [
        lambda c, p: _human(c),
        lambda c, p: mortal_of(c),
        lambda c, p: Not(mortal_of(c)),
        lambda c, p: Implies(mortal_of(c), _human(c)),
        lambda c, p: Box(_human(c)),
        lambda c, p: Diamond(_human(c)),
        lambda c, p: Diamond(Not(_human(c))),
        lambda c, p: Implies(Diamond(mortal_of(c)), Diamond(mortal_of(p))),
        lambda c, p: Implies(Box(mortal_of(c)), Diamond(mortal_of(c))),
        lambda c, p: Implies(Diamond(mortal_of(c)), mortal_of(c)),
        lambda c, p: Or(mortal_of(c), Not(mortal_of(p))),
        lambda c, p: And(_human(c), Not(mortal_of(c))),
        lambda c, p: Implies(Diamond(And(_human(c), mortal_of(c))), Diamond(mortal_of(c))),
    ])
    def test_the_tableau_agrees_with_the_enumerator_of_legal_models(self, make):
        """The labelled tableau says ``valid`` exactly when a search over every K-model with up to three worlds
        and the membership fixed at every world finds no countermodel; and every countermodel the search
        finds is a legal model of the formula."""
        f = make(self.CARL, self.PLAIN)
        result = modal_enum_search(f, frame="K", max_worlds=3)
        tableau = modal_decide(f)
        if result.model is None:
            assert result.exhausted is True and tableau == "valid", f.to_unicode_str()
        else:
            assert sorted_constant_violations(f, result.model) == []
            assert tableau == "invalid", f.to_unicode_str()

    def test_a_sorted_quantifier_is_still_an_opaque_literal(self):
        """Out of scope, as before: the verdict for a quantified formula is ``unknown``, never a wrong one."""
        assert modal_decide(_SORTED.parse("∀x:Human Mortal(x)")) == "unknown"
        assert modal_decide(sorted_formula("P1")) == "unknown"


# =============================================================================
# hol.isabelle_modal and hol.thf_modal
# =============================================================================

def _isabelle_lines(theory):
    return theory.splitlines()


class TestModalHolMembership:
    @pytest.mark.parametrize("name", FORMULAS)
    def test_the_theories_state_the_membership_next_to_the_non_emptiness(self, name):
        f = sorted_formula(name)
        isabelle = isabelle_modal_theory(f, mode="constant")
        assert 'axiomatization where sort_member0: "human socrates w"' in isabelle
        lines = _isabelle_lines(isabelle)
        assert (lines.index('axiomatization where nonempty_sort0: "\\<exists>x. human x w"')
                < lines.index('axiomatization where sort_member0: "human socrates w"'))
        thf = to_thf_modal_full(f, mode="constant")
        assert "thf(sort_member0, axiom, ( ! [W: mu] : ( human @ socrates @ W ) ))." in thf
        # unguarded by existence in the actualist regime too
        assert 'axiomatization where sort_member0: "human socrates w"' in isabelle_modal_theory(
            f, mode="varying")
        assert "thf(sort_member0, axiom, ( ! [W: mu] : ( human @ socrates @ W ) ))." in to_thf_modal_full(
            f, mode="varying")

    @pytest.mark.parametrize("name", FORMULAS)
    def test_the_unannotated_formulas_state_no_membership(self, name):
        for f in (twin(name), unsorted_socrates(name)):
            assert "sort_member" not in isabelle_modal_theory(f)
            assert "sort_member" not in to_thf_modal_full(f)
        assert "sort_member" not in "".join(modal_axiom_names(twin(name)))

    def test_the_fact_names_do_not_collide_with_the_non_emptiness_family(self):
        names = modal_axiom_names(sorted_formula("P1"))
        assert names == ["const_dom", "nonempty_sort0", "sort_member0"]
        assert [n for n in names if n.startswith("nonempty_sort")] == ["nonempty_sort0"]
        assert modal_axiom_names(sorted_formula("P1"), mode="varying") == [
            "nonempty_dom", "nonempty_sort0", "sort_member0"]

    def test_a_sort_that_occurs_only_through_a_constant_gets_its_guard_declared(self):
        """``□Mortal(socrates:Human)``: no quantifier ranges over ``Human``, yet the guard is a symbol of
        the theory (the membership is stated about it), so it is declared and made non-empty."""
        f = _SORTED.parse("□Mortal(socrates:Human)")
        theory = isabelle_modal_theory(f, mode="constant")
        assert 'consts human :: "e \\<Rightarrow> i \\<Rightarrow> bool"' in theory
        assert 'axiomatization where nonempty_sort0: "\\<exists>x. human x w"' in theory
        assert 'axiomatization where sort_member0: "human socrates w"' in theory
        assert modal_axiom_names(f) == ["nonempty_sort0", "sort_member0"]
        thf = to_thf_modal_full(f, mode="constant")
        assert "thf(human_decl, type, ( human : ( $i > mu > $o ) ))." in thf
        assert "thf(nonempty_sort0, axiom, ( ! [W: mu] : ? [X: $i] : ( human @ X @ W ) ))." in thf
        assert "thf(sort_member0, axiom, ( ! [W: mu] : ( human @ socrates @ W ) ))." in thf

    def test_an_actualist_sort_witness_without_a_quantifier_has_existsAt_declared(self):
        """The non-emptiness of a sort that occurs only through a constant names ``existsAt`` in an
        actualist regime; a formula without a quantifier has no quantifier block to declare it."""
        f = _SORTED.parse("□Mortal(socrates:Human)")
        theory = isabelle_modal_theory(f, mode="varying")
        assert 'axiomatization where nonempty_sort0: "\\<exists>x. existsAt x w \\<and> human x w"' in theory
        declared = [i for i, ln in enumerate(_isabelle_lines(theory)) if ln.startswith("consts existsAt")]
        used = [i for i, ln in enumerate(_isabelle_lines(theory)) if "existsAt x w" in ln]
        assert len(declared) == 1 and declared[0] < min(used)
        # a formula with a quantifier declares it once, through the quantifier block
        assert isabelle_modal_theory(sorted_formula("P1"), mode="varying").count("consts existsAt") == 1
        # the constant regime needs none
        assert "existsAt" not in isabelle_modal_theory(f, mode="constant")

    def test_a_constant_of_two_sorts_gets_one_fact_per_sort_in_first_occurrence_order(self):
        f = _SORTED.parse("P(carl:A) ∧ Q(carl:B)")
        theory = isabelle_modal_theory(f)
        assert theory.index('sort_member0: "a carl w"') < theory.index('sort_member1: "b carl w"')
        assert modal_axiom_names(f) == ["nonempty_sort0", "nonempty_sort1", "sort_member0", "sort_member1"]
        thf = to_thf_modal_full(f)
        assert "thf(sort_member0, axiom, ( ! [W: mu] : ( a @ carl @ W ) ))." in thf
        assert "thf(sort_member1, axiom, ( ! [W: mu] : ( b @ carl @ W ) ))." in thf

    def test_the_membership_names_the_functors_the_goal_uses(self):
        """A constant whose name is transliterated (``sókrates``) and a user predicate that sanitises like
        the sort (``human`` next to ``Human``): the fact is about the sort's guard and the constant the
        goal mentions, not about their lookalikes."""
        socrates = SortedConstant("sókrates", "Human")
        x = Variable("x")
        f = And(And(SortedQuantifier("∀", x, "Human", mortal_of(x)), mortal_of(socrates)),
                Atom("human", [Constant("plato")]))
        theory = isabelle_modal_theory(f)
        guard, constant = re.search(
            r'axiomatization where sort_member0: "(\w+) (\w+) w"', theory).groups()
        assert constant.isascii() and f'consts {constant} :: "e"' in theory
        assert f"(mortal {constant})" in theory                # the constant the goal's atom mentions
        # the sort's guard is the functor the sorted quantifier uses in the goal ...
        goal_guard = re.search(r"mforall \(\\<lambda>x\. \(mimp \((\w+) x\)", theory).group(1)
        assert guard == goal_guard
        # ... and the user predicate that sanitises like it is a DIFFERENT functor
        assert "human_2" in theory and guard != "human_2"
        thf = to_thf_modal_full(f)
        thf_member = re.search(r"thf\(sort_member0, axiom, \( ! \[W: mu\] : \( (\w+) @ (\w+) @ W \) \)\)\.", thf)
        thf_guard = re.search(r"mforall @ \( \^ \[X: \$i\] : \( mimplies @ \( (\w+) @ X \)", thf).group(1)
        assert thf_member.group(1) == thf_guard
        assert f"thf({thf_member.group(2)}_decl, type, ( {thf_member.group(2)} : $i ))." in thf


# =============================================================================
# hol.classical and hol.lean: the facts are beside the conjecture, not in it
# =============================================================================

_SOCRATES = SortedConstant("socrates", "Human")


def _conjecture_body(thf):
    return thf.split("thf(goal, conjecture,")[1]


class TestClassicalHolExportsStateTheSortFacts:
    def test_thf_states_the_facts_as_axioms_and_the_goal_is_the_bare_relativisation(self):
        thf = to_thf_msfol(sorted_formula("P1"))
        assert "thf(nonempty_sort_0, axiom, ( ? [X0: $i] : ( human @ X0 ) ))." in thf
        assert "thf(sort_member_0, axiom, ( human @ socrates ))." in thf
        body = _conjecture_body(thf)
        assert "( human @ socrates )" not in body and "&" not in body
        assert body.strip() == ("( ( ! [X: $i] : ( ( human @ X ) => ( mortal @ X ) ) ) "
                                "=> ( mortal @ socrates ) )).")

    def test_a_tautology_about_a_sorted_constant_is_a_goal_without_the_guard(self):
        """``Mortal(c) ∨ ¬Mortal(c)`` is valid for any ``c``. A goal ``Human(c) ∧ (…)`` could never be
        proved, the guard being an uninterpreted predicate; the goal here is the tautology itself."""
        f = Or(mortal_of(_SOCRATES), Not(mortal_of(_SOCRATES)))
        thf_body = _conjecture_body(to_thf_msfol(f))
        assert "human" not in thf_body
        isabelle_statement = re.search(r'lemma goal: "(.*)"', to_isabelle_msfol(f)).group(1)
        assert isabelle_statement.endswith("\\<Longrightarrow> ((mortal socrates) \\<or> (\\<not> (mortal socrates)))")
        lean_theorem = re.search(r"theorem goal(.*) := by", lean.to_lean_msfol(f)).group(1)
        assert lean_theorem.endswith(": ((mortal socrates) ∨ (¬ (mortal socrates)))")

    def test_isabelle_states_the_facts_as_premises_of_the_lemma(self):
        theory = to_isabelle_msfol(sorted_formula("P1"))
        statement = re.search(r'lemma goal: "(.*)"', theory).group(1)
        assert statement == (
            "\\<lbrakk>(\\<exists> x0. (human x0)); (human socrates)\\<rbrakk> \\<Longrightarrow> "
            "((\\<forall> x. ((human x) \\<longrightarrow> (mortal x))) \\<longrightarrow> (mortal socrates))")
        assert "axiomatization" not in theory      # a premise needs no `using` clause
        assert 'consts human :: "i \\<Rightarrow> bool"' in theory

    def test_lean_states_the_facts_as_hypotheses_of_the_theorem(self):
        source = lean.to_lean_msfol(sorted_formula("P1"))
        assert ("theorem goal (sort_nonempty_0 : (∃ x0 : Ind, (human x0))) "
                "(sort_member_0 : (human socrates)) : "
                "((∀ x : Ind, ((human x) → (mortal x))) → (mortal socrates)) := by") in source
        assert source.count("Nonempty") == 2      # only the pair for Ind itself

    def test_an_asserted_formula_keeps_the_membership_as_a_conjunct(self):
        """What a formula asserts includes the membership of its constants; the non-emptiness is a
        separate fact, as it is for a conjecture."""
        thf = to_thf_msfol(sorted_formula("P1"), conjecture=False)
        assert "thf(goal, axiom, ( ( human @ socrates ) & " in thf
        assert "thf(nonempty_sort_0, axiom, ( ? [X0: $i] : ( human @ X0 ) ))." in thf
        assert "sort_member_0" not in thf
        source = lean.to_lean_msfol(sorted_formula("P1"), conjecture=False)
        assert "axiom sort_nonempty_0 : (∃ x0 : Ind, (human x0))" in source
        assert "axiom goal : ((human socrates) ∧ " in source

    def test_without_sort_facts_the_export_is_the_bare_relativisation(self):
        f = sorted_formula("P1")
        assert to_thf_msfol(f, include_sort_facts=False) == to_thf_fol(to_fol(f))
        assert "sort_member" not in to_thf_msfol(f, include_sort_facts=False)
        assert "theorem goal :" in lean.to_lean_msfol(f, include_sort_facts=False)
        assert "Longrightarrow" not in to_isabelle_msfol(f, include_sort_facts=False)

    def test_a_formula_without_a_sorted_node_is_emitted_as_the_plain_formula(self):
        plain = Implies(Quantifier("∀", Variable("x"), mortal_of(Variable("x"))),
                        mortal_of(Constant("socrates")))
        assert to_thf_msfol(plain) == to_thf_fol(plain)
        assert "Longrightarrow" not in to_isabelle_msfol(plain)
        assert lean.to_lean_msfol(plain) == lean.to_lean_fol(plain)

    def test_a_sort_that_occurs_only_through_a_constant_is_declared(self):
        thf = to_thf_msfol(mortal_of(_SOCRATES))
        assert "thf(human_decl, type, ( human : ( $i > $o ) ))." in thf
        assert 'consts human :: "i \\<Rightarrow> bool"' in to_isabelle_msfol(mortal_of(_SOCRATES))
        assert "axiom human : Ind → Prop" in lean.to_lean_msfol(mortal_of(_SOCRATES))


@pytest.mark.lean_live
@pytest.mark.skipif(not lean.lean_available(), reason="no Lean 4 toolchain found")
class TestLeanKernelChecksTheSortedProblems:
    def test_the_sorted_instance_is_provable_from_the_hypotheses(self):
        """``(∀x. Human x → Mortal x) → Mortal socrates`` from ``Human socrates``: instantiate."""
        source = lean.to_lean_msfol(sorted_formula("P1"), proof="intro h\nexact h socrates sort_member_0")
        result = lean.check_theory(source, "sorted_instance")
        assert result.ok and not result.uses_sorry and result.proved

    def test_the_tautology_is_provable_with_the_facts_beside_it(self):
        f = Or(mortal_of(_SOCRATES), Not(mortal_of(_SOCRATES)))
        result = lean.check_theory(lean.to_lean_msfol(f, proof="exact Classical.em _"), "sorted_lem")
        assert result.ok and not result.uses_sorry and result.proved

    def test_the_sort_nonemptiness_closes_the_schema(self):
        """``(∀x:Human Mortal x) → ∃x:Human Mortal x``: the witness is the sort's non-emptiness."""
        f = _SORTED.parse("∀x:Human Mortal(x) → ∃x:Human Mortal(x)")
        proof = "intro h\nobtain ⟨w, hw⟩ := sort_nonempty_0\nexact ⟨w, hw, h w hw⟩"
        result = lean.check_theory(lean.to_lean_msfol(f, proof=proof), "sorted_nonempty")
        assert result.ok and not result.uses_sorry and result.proved
