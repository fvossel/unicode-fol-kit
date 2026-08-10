# -*- coding: utf-8 -*-
"""Centering for the Lewis counterfactual: cf_valid / cf_countermodel and the
matching Isabelle premise.

Nesting alone (Lewis's V) lets a world have spheres that do not contain it — in
the limit, no sphere at all — and then ``A □→ B`` is vacuously true even where
``A`` actually holds. That made ``(P ∧ (P □→ Q)) → Q`` and ``(P □→ Q) → (P → Q)``
come back INVALID, which is not what anyone writing a counterfactual means. The
fix is a ``centering`` level, defaulting to VW.

These tests pin four things that could silently drift apart:

1. the truth table — which schema is valid at which level, all ten rows, so that a
   future change to the enumeration cannot quietly move a cell;
2. the enumeration itself — the generator is cross-checked against an independently
   written predicate in BOTH directions (sound: every emitted chain is admissible;
   complete: every admissible chain is emitted — that is the direction whose failure
   yields spurious VALID verdicts), and the class chain ``strong ⊆ weak ⊆ none`` is
   asserted as sets of chains rather than assumed;
3. the world bound — two worlds is structurally too few at the centered levels, so
   ``DEFAULT_MAX_WORLDS`` is level-dependent; the two schemas that expose it
   (conditional excluded middle at VC, importation at VW) are pinned at both bounds;
4. the Isabelle emitter — the premise and the ``unfolding`` list per level, since a
   premise the battery cannot see through is a silent proof-failure generator.
"""

import pytest

from unicode_fol_kit.fol.msflparser import MSFLParser
from unicode_fol_kit.hol.isabelle_conditional import (
    isabelle_conditional_theory, battery_proof, nitpick_proof,
)
from unicode_fol_kit.semantics.conditional import (
    CENTERING_LEVELS, DEFAULT_MAX_WORLDS, check_centering, cf_valid,
    cf_countermodel, cf_satisfies, _sphere_chains, _centering_ok,
)

MODAL = MSFLParser(modal=True)

#: The counterfactual schema battery, keyed by name so a failure says which law
#: moved. Values: source, then the expected verdict at none / weak / strong.
#: Measured at the shipped default bound, and identical at max_worlds=2 for all ten
#: rows and all three levels — no battery row is bound-sensitive, which is exactly
#: why the two schemas that ARE need their own class below.
TABLE = [
    # name,                 source,                                         none,  weak,  strong
    ("identity",            "A □→ A",                                       True,  True,  True),
    ("agglomeration",       "((A □→ B) ∧ (A □→ C)) → (A □→ (B ∧ C))",       True,  True,  True),
    ("weakened consequent", "(A □→ B) → (A □→ (B ∨ C))",                    True,  True,  True),
    ("duality",             "(A ◇→ B) → ¬(A □→ ¬B)",                        True,  True,  True),
    ("ant strengthening",   "(A □→ B) → ((A ∧ C) □→ B)",                    False, False, False),
    ("contraposition",      "(A □→ B) → (¬B □→ ¬A)",                        False, False, False),
    ("transitivity",        "((A □→ B) ∧ (B □→ C)) → (A □→ C)",             False, False, False),
    ("modus ponens",        "(P ∧ (P □→ Q)) → Q",                           False, True,  True),
    ("weak centering",      "(P □→ Q) → (P → Q)",                           False, True,  True),
    ("strong centering",    "(P ∧ Q) → (P □→ Q)",                           False, False, True),
]

_CELLS = [(name, src, level, expect)
          for name, src, *verdicts in TABLE
          for level, expect in zip(CENTERING_LEVELS, verdicts)]

MP = "(P ∧ (P □→ Q)) → Q"
WEAK_CENTERING = "(P □→ Q) → (P → Q)"


# --------------------------------------------------------------------------- #
# The truth table.
# --------------------------------------------------------------------------- #

class TestTruthTable:
    @pytest.mark.parametrize(
        "name,src,level,expect", _CELLS,
        ids=[f"{n}-{lv}" for n, _s, lv, _e in _CELLS])
    def test_cell(self, name, src, level, expect):
        assert cf_valid(MODAL.parse(src), centering=level) is expect

    def test_the_default_is_weak(self):
        # The default is what every existing caller (and the Isabelle route) gets.
        # Pinned on the two schemas that SEPARATE the levels rather than by re-running
        # the whole table at the default bound: modus ponens separates V from VW,
        # strong centering separates VW from VC, so agreeing with "weak" on both is
        # what "the default is weak" means — and it costs two searches instead of ten.
        for src in (MP, "(P ∧ Q) → (P □→ Q)"):
            f = MODAL.parse(src)
            assert cf_valid(f) is cf_valid(f, centering="weak"), src
        assert cf_valid(MODAL.parse(MP)) is True                       # ≠ "none"
        assert cf_valid(MODAL.parse("(P ∧ Q) → (P □→ Q)")) is False    # ≠ "strong"

    @pytest.mark.parametrize("name,src,none,weak,strong", TABLE,
                             ids=[t[0] for t in TABLE])
    def test_validity_propagates_down_the_class_chain(self, name, src, none, weak, strong):
        # strong ⊆ weak ⊆ none as classes of models, so validity propagates
        # none ⇒ weak ⇒ strong (and refutation the other way). An executable
        # statement of the inclusion the enumeration is built to respect.
        assert not (none and not weak)
        assert not (weak and not strong)


# --------------------------------------------------------------------------- #
# The headline regression: the two schemas the empty sphere system refuted.
# --------------------------------------------------------------------------- #

class TestCenteringRegression:
    @pytest.mark.parametrize("src", [MP, WEAK_CENTERING])
    def test_valid_once_centered_invalid_in_bare_V(self, src):
        f = MODAL.parse(src)
        assert cf_valid(f) is True                          # default VW
        assert cf_valid(f, centering="weak") is True
        assert cf_valid(f, centering="strong") is True
        assert cf_valid(f, centering="none") is False       # Lewis V really does refute it

    @pytest.mark.parametrize("src", [MP, WEAK_CENTERING])
    def test_the_V_countermodel_is_the_empty_sphere_system(self, src):
        # Pin the exact shape of the old bug: the witness is the world with NO
        # sphere at all, where every □→ is vacuously true. If a refactor ever
        # reintroduces that system into a centered class, this fails loudly
        # instead of the truth table quietly changing.
        f = MODAL.parse(src)
        found = cf_countermodel(f, centering="none")
        assert found is not None
        model, world = found
        assert cf_satisfies(f, model, world) is False       # verified by construction
        assert model.sphere_system(world) == []

    def test_strong_centering_separates_VC_from_VW(self):
        # (P ∧ Q) → (P □→ Q) is the schema that distinguishes the two centered
        # classes; its VW countermodel is verified the same way.
        f = MODAL.parse("(P ∧ Q) → (P □→ Q)")
        assert cf_valid(f, centering="strong") is True
        for level in ("none", "weak"):
            found = cf_countermodel(f, centering=level)
            assert found is not None, level
            model, world = found
            assert cf_satisfies(f, model, world) is False

    @pytest.mark.parametrize("src", [
        "(A □→ B) → ((A ∧ C) □→ B)",                        # ant. strengthening
        "(A □→ B) → (¬B □→ ¬A)",                            # contraposition
        "((A □→ B) ∧ (B □→ C)) → (A □→ C)",                 # transitivity
    ])
    def test_the_classical_laws_stay_refuted_at_every_level(self, src):
        # Centering must not smuggle in the laws whose failure is the whole point
        # of the connective. Each refutation is an explicit verified countermodel,
        # found inside the default max_worlds=2 even at VC.
        f = MODAL.parse(src)
        for level in CENTERING_LEVELS:
            found = cf_countermodel(f, centering=level)
            assert found is not None, f"{src} @ {level}"
            model, world = found
            assert cf_satisfies(f, model, world) is False


# --------------------------------------------------------------------------- #
# The world bound: two worlds is structurally too few at the centered levels.
# --------------------------------------------------------------------------- #

#: Stalnaker's conditional excluded middle. VC leaves it INVALID, but a VC
#: countermodel needs w to falsify the antecedent plus two antecedent-worlds that
#: disagree on the consequent — three worlds — because VC pins {w} as the innermost
#: sphere. At |W| ≤ 2 it is reported valid.
CEM = "(A □→ B) ∨ (A □→ ¬B)"

#: Importation. Invalid in VW, and the *only* countermodels are nested-counterfactual
#: ones needing three worlds: before centering existed the empty sphere system refuted
#: it at |W| = 1, so excluding that system without raising the bound turned a correct
#: INVALID into a spurious VALID.
IMPORTATION = "(A □→ (B □→ C)) → ((A ∧ B) □→ C)"


class TestWorldBound:
    @pytest.mark.parametrize("src,level", [(CEM, "strong"), (IMPORTATION, "weak"),
                                           (IMPORTATION, "strong")])
    def test_two_worlds_is_not_enough_but_the_default_is(self, src, level):
        # The honest contract's failure mode, made visible: True at a too-small bound
        # is not validity. Both halves are asserted, so a future default that quietly
        # drops back to 2 fails here rather than in a user's verdict.
        f = MODAL.parse(src)
        assert cf_valid(f, 2, centering=level) is True          # spurious
        assert cf_valid(f, centering=level) is False            # at the default bound

    @pytest.mark.parametrize("src,level", [(CEM, "strong"), (IMPORTATION, "weak")])
    def test_the_three_world_countermodel_is_verified(self, src, level):
        f = MODAL.parse(src)
        found = cf_countermodel(f, centering=level)
        assert found is not None
        model, world = found
        assert cf_satisfies(f, model, world) is False           # verified refutation
        assert len(model.worlds) == 3
        assert _centering_ok(model.sphere_system(world), world, level)

    def test_the_default_bound_is_level_dependent_and_documented(self):
        # Three at the centered levels (see above); two at "none", whose per-world
        # chain count is 26 against VW's 11 — the same schema runs for minutes there.
        assert DEFAULT_MAX_WORLDS == {"none": 2, "weak": 3, "strong": 3}
        assert set(DEFAULT_MAX_WORLDS) == set(CENTERING_LEVELS)

    def test_max_worlds_none_means_the_level_default(self):
        # cf_valid(f, None) and cf_valid(f) must agree, and both must agree with the
        # explicit bound the table names — the sentinel is a lookup, not a second policy.
        f = MODAL.parse(CEM)
        for level in CENTERING_LEVELS:
            explicit = cf_valid(f, DEFAULT_MAX_WORLDS[level], centering=level)
            assert cf_valid(f, None, centering=level) is explicit, level
            assert cf_valid(f, centering=level) is explicit, level


# --------------------------------------------------------------------------- #
# Argument validation and call-compatibility.
# --------------------------------------------------------------------------- #

class TestLevelValidation:
    @pytest.mark.parametrize("bad", ["weakly", "WEAK", "", "centered", None])
    def test_unknown_levels_are_rejected_by_both_entry_points(self, bad):
        f = MODAL.parse("A □→ A")
        for call in (lambda: cf_valid(f, centering=bad),
                     lambda: cf_countermodel(f, centering=bad),
                     lambda: check_centering(bad)):
            with pytest.raises(ValueError, match="centering must be one of"):
                call()

    def test_the_error_names_all_three_legal_levels(self):
        with pytest.raises(ValueError) as exc:
            cf_valid(MODAL.parse("A □→ A"), centering="weakly")
        for level in CENTERING_LEVELS:
            assert level in str(exc.value)

    def test_max_worlds_stays_positional(self):
        # centering is keyword-only precisely so existing positional calls keep
        # working; that is a compatibility promise, so test it.
        f = MODAL.parse("A □→ A")
        assert cf_valid(f, 2) is True
        assert cf_countermodel(f, 2) is None

    def test_levels_are_exactly_the_three_lewis_systems(self):
        assert CENTERING_LEVELS == ("none", "weak", "strong")
        assert all(check_centering(lv) == lv for lv in CENTERING_LEVELS)


# --------------------------------------------------------------------------- #
# The enumeration: generator vs. independently written predicate.
# --------------------------------------------------------------------------- #

class TestSphereEnumeration:
    #: Measured chain counts per world, |W| = 1..3 — the enumeration cost, and the
    #: reason "none" at max_worlds=3 is a deliberate choice.
    COUNTS = {"none": [2, 6, 26], "weak": [1, 3, 11], "strong": [1, 2, 6]}

    @pytest.mark.parametrize("level", CENTERING_LEVELS)
    def test_chain_counts(self, level):
        for n in (1, 2, 3):
            worlds = tuple(range(n))
            got = len(list(_sphere_chains(0, worlds, level)))
            assert got == self.COUNTS[level][n - 1], (level, n)

    @pytest.mark.parametrize("level", CENTERING_LEVELS)
    def test_every_emitted_chain_satisfies_the_predicate(self, level):
        # The generator builds admissible systems by construction; _centering_ok
        # decides admissibility from the level's definition. Cross-checking them
        # is what makes "by construction" more than an assertion.
        for n in (1, 2, 3):
            worlds = tuple(range(n))
            for world in worlds:
                for chain in _sphere_chains(world, worlds, level):
                    assert _centering_ok(chain, world, level), (level, world, chain)
                    assert all(chain[i] < chain[i + 1] for i in range(len(chain) - 1))
                    assert all(s for s in chain)        # ∅ is never a member

    @pytest.mark.parametrize("level", CENTERING_LEVELS)
    def test_every_admissible_family_is_emitted(self, level):
        # The OTHER direction, and the one that matters for verdicts: soundness of the
        # generator only says no inadmissible model is searched, while COMPLETENESS is
        # what stops a missed admissible model from becoming a spurious VALID. Built
        # from the definition — every nested family of subsets, ∅ deleted (it is
        # truth-value inert, so the generator omits it) — not from the generator.
        from itertools import combinations
        for n in (1, 2, 3):
            worlds = tuple(range(n))
            subsets = [frozenset(c) for r in range(n + 1)
                       for c in combinations(worlds, r)]
            families = []
            for r in range(len(subsets) + 1):
                for fam in combinations(subsets, r):
                    if all(a <= b or b <= a for a in fam for b in fam):   # nested
                        families.append(fam)
            for world in worlds:
                admissible = {frozenset(f - {frozenset()})
                              for f in map(frozenset, families)
                              if _centering_ok(f, world, level)}
                emitted = {frozenset(c) for c in _sphere_chains(world, worlds, level)}
                assert admissible == emitted, (level, n, world)

    def test_the_classes_are_nested_as_sets_of_chains(self):
        for n in (1, 2, 3):
            worlds = tuple(range(n))
            sets = {lv: {tuple(c) for c in _sphere_chains(0, worlds, lv)}
                    for lv in CENTERING_LEVELS}
            assert sets["strong"] <= sets["weak"] <= sets["none"]
            assert sets["strong"] < sets["none"]        # strictly, at every size

    def test_only_V_admits_the_empty_sphere_system(self):
        # The one chain that separates V from VW at a single world, and the direct
        # cause of the modus-ponens failure.
        for n in (1, 2, 3):
            worlds = tuple(range(n))
            chains = {lv: [tuple(c) for c in _sphere_chains(0, worlds, lv)]
                      for lv in CENTERING_LEVELS}
            assert () in chains["none"]
            assert () not in chains["weak"]
            assert () not in chains["strong"]

    def test_the_predicate_rejects_the_systems_each_level_excludes(self):
        w = 0
        assert _centering_ok([], w, "none") is True
        assert _centering_ok([], w, "weak") is False            # no sphere at all
        assert _centering_ok([frozenset({1})], w, "weak") is False   # w in none of them
        assert _centering_ok([frozenset({0, 1})], w, "weak") is True
        assert _centering_ok([frozenset({0, 1})], w, "strong") is False  # {w} missing
        assert _centering_ok([frozenset({0}), frozenset({0, 1})], w, "strong") is True
        # ∅-tolerant, as Lewis is: the empty sphere is truth-value inert.
        assert _centering_ok([frozenset(), frozenset({0})], w, "weak") is True

    def test_the_predicate_validates_its_level_too(self):
        with pytest.raises(ValueError, match="centering must be one of"):
            _centering_ok([], 0, "weakly")


# --------------------------------------------------------------------------- #
# The Isabelle emitter: one premise per level, and an unfold list that matches it.
# --------------------------------------------------------------------------- #

PREMISE = {
    "none": None,
    "weak": "weakly_centered Sel",
    "strong": "strongly_centered Sel",
}


class TestIsabellePremise:
    @pytest.mark.parametrize("level", CENTERING_LEVELS)
    def test_the_lemma_carries_exactly_this_level_premise(self, level):
        thy = isabelle_conditional_theory(MODAL.parse("A □→ A"), centering=level)
        arrow = "\\<Longrightarrow>"
        expected = " ".join(
            ["nested Sel", arrow]
            + ([PREMISE[level], arrow] if PREMISE[level] else []))
        assert f'lemma goal: "{expected} ' in thy, thy
        for other, prem in PREMISE.items():
            if prem and other != level:
                assert prem not in thy.split("lemma goal:")[1]

    @pytest.mark.parametrize("level", CENTERING_LEVELS)
    def test_both_predicates_are_defined_at_every_level(self, level):
        # The preamble is one constant string; an unused definition is inert. That
        # keeps the emitted theories comparable and the emitter free of branching.
        thy = isabelle_conditional_theory(MODAL.parse("A □→ A"), centering=level)
        assert "definition weakly_centered" in thy
        assert "definition strongly_centered" in thy

    @pytest.mark.parametrize("level", CENTERING_LEVELS)
    def test_the_theory_records_which_class_it_decided(self, level):
        # At centering="none" the lemma line is byte-identical to a pre-centering
        # one, so provenance is the only way to read the level off the artefact.
        thy = isabelle_conditional_theory(MODAL.parse("A □→ A"), centering=level)
        system = {"none": "V", "weak": "VW", "strong": "VC"}[level]
        assert f"centering = {level} (Lewis {system})" in thy

    @pytest.mark.parametrize("level,unfolded,absent", [
        ("none", (), ("weakly_centered_def", "strongly_centered_def")),
        ("weak", ("weakly_centered_def",), ("strongly_centered_def",)),
        ("strong", ("strongly_centered_def",), ("weakly_centered_def",)),
    ])
    def test_the_battery_unfolds_this_level_definition_only(self, level, unfolded, absent):
        # The unfold list is what lets the battery see through the premise. A
        # mismatch does not yield a wrong verdict, it yields a failed proof — i.e.
        # a spurious UNKNOWN/INVALID — so premise and unfold list are pinned together.
        line = battery_proof(centering=level).splitlines()[0]
        assert line.lstrip().startswith("unfolding nested_def")
        for name in unfolded:
            assert name in line
        for name in absent:
            assert name not in line

    def test_the_emitter_default_matches_cf_valid_default(self):
        # Both routes must decide the same question unless told otherwise.
        thy = isabelle_conditional_theory(MODAL.parse("A □→ A"))
        assert "weakly_centered Sel \\<Longrightarrow>" in thy
        assert battery_proof() == battery_proof(centering="weak")

    def test_centering_is_still_a_premise_not_an_axiom(self):
        # nitpick downgrades to quasi_genuine while axiomatised constants are in
        # play, which would cost us the refutation half of the decision procedure.
        for level in CENTERING_LEVELS:
            thy = isabelle_conditional_theory(
                MODAL.parse("A □→ B"), centering=level,
                proof=nitpick_proof(card="1-3"))
            assert "axiomatization" not in thy
            assert "expect = genuine" in thy

    @pytest.mark.parametrize("bad", ["weakly", "VW", ""])
    def test_unknown_levels_are_rejected_by_the_emitter(self, bad):
        with pytest.raises(ValueError, match="centering must be one of"):
            isabelle_conditional_theory(MODAL.parse("A □→ A"), centering=bad)
        with pytest.raises(ValueError, match="centering must be one of"):
            battery_proof(centering=bad)

    def test_methods_stay_positional(self):
        proof = battery_proof(["blast"])
        assert proof.splitlines()[-1].strip() == "by (blast)"
        with pytest.raises(ValueError, match="at least one proof method"):
            battery_proof([])
