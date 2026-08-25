"""The shared frame registry: correspondence, and one table for six routes.

Two claims are pinned here, and the first is the reason the module exists.

**Correspondence, brute-forced.** For every first-order condition in
:mod:`unicode_fol_kit.fol.frames`, over EVERY frame on up to three worlds and
EVERY valuation, "the corresponding axiom is valid on this frame" and "the
frame satisfies the condition" must agree. That is what turns the registry
from a table of claims into a table of checked facts: a wrong condition, a
wrong Geach coordinate or a mistyped axiom fails here rather than quietly
teaching one route a different modal logic than its neighbour. (Three worlds
is exhaustive over 512 frames per size; the whole sweep takes a couple of
seconds.)

**One table, six routes.** ``fol.qml``, ``atp.modal_tableau``,
``atp.kripke_enum``, ``atp.fitch``, ``fol.modal_translation`` and
``hol.isabelle_modal`` each used to carry their own copy, which is how they
drifted apart — the tableau knew ``K45`` and ``qml`` did not, ``qml`` knew
``S4.2`` and the tableau did not. They now read the same dict, and what a
route cannot express it REFUSES by name instead of ignoring: silently
dropping ``directed`` from ``S4.2`` would answer about a larger frame class
than the caller asked for, which is a soundness bug, not a gap.
"""

import itertools

import pytest

from unicode_fol_kit.fol.frames import (
    AXIOM_ALIASES, FRAME_CONDITIONS, FRAMES, GeachSpec,
    UnsupportedFrameCondition, resolve_frame, geach_axiom,
    holds_on_finite_frame, modal_axiom, parse_geach, unguarded_frame_axiom,
)
from unicode_fol_kit.semantics.kripke import KripkeModel, satisfies_modal

_FIRST_ORDER = [name for name, spec in FRAME_CONDITIONS.items()
                if spec.first_order]
_NOT_FIRST_ORDER = [name for name, spec in FRAME_CONDITIONS.items()
                    if not spec.first_order]


# ---------------------------------------------------------------------------
# The brute-force correspondence
# ---------------------------------------------------------------------------

def _frames(n):
    """Every frame on ``n`` worlds — all 2^(n²) edge sets."""
    pairs = [(a, b) for a in range(n) for b in range(n)]
    for size in range(len(pairs) + 1):
        for combo in itertools.combinations(pairs, size):
            yield frozenset(combo)


def _valid_on(axiom, edges, n, atoms):
    """Is ``axiom`` valid on this frame — true at every world under every
    valuation of its propositional letters?"""
    worlds = list(range(n))
    for bits in itertools.product((False, True), repeat=len(atoms) * n):
        valuation, i = {}, 0
        for w in worlds:
            here = set()
            for atom in atoms:
                if bits[i]:
                    here.add(atom)
                i += 1
            valuation[w] = here
        model = KripkeModel(worlds, {"alethic": edges}, valuation)
        if not all(satisfies_modal(axiom, model, w) for w in worlds):
            return False
    return True


def _disagreements(condition, axiom, atoms, max_worlds=3):
    out = []
    for n in range(1, max_worlds + 1):
        for edges in _frames(n):
            if _valid_on(axiom, edges, n, atoms) != holds_on_finite_frame(
                    condition, edges, n):
                out.append((n, sorted(edges)))
                if len(out) >= 3:
                    return out
    return out


@pytest.mark.parametrize("condition", _FIRST_ORDER)
def test_each_condition_corresponds_to_its_axiom(condition):
    """Axiom valid on the frame ⟺ frame satisfies the condition, on every
    frame up to three worlds. This is the registry's correctness argument."""
    spec = FRAME_CONDITIONS[condition]
    atoms = ("P", "Q") if spec.axiom == ".3" else ("P",)
    bad = _disagreements(condition, modal_axiom(spec.axiom), atoms)
    assert not bad, (
        f"{condition} ({spec.axiom}) disagrees with its axiom on {bad}")


@pytest.mark.parametrize("condition", [
    name for name in _FIRST_ORDER if FRAME_CONDITIONS[name].geach is not None])
def test_the_geach_coordinates_reproduce_the_named_axiom(condition):
    """Every Geach coordinate in the registry generates a schema with the
    SAME frame class as the hand-written axiom — the unification the module
    docstring claims, checked instead of asserted."""
    spec = FRAME_CONDITIONS[condition]
    assert not _disagreements(condition, geach_axiom(spec.geach), ("P",))


def test_the_correspondence_check_can_still_see_a_difference():
    """Non-vacuity: the same machinery must REJECT a wrong pairing, or every
    green above means nothing. Transitivity is not what T corresponds to."""
    assert _disagreements("trans", modal_axiom("T"), ("P",))


@pytest.mark.parametrize("spec,expected", [
    # The correspondences the Scott–Lemmon table is usually quoted with —
    # recomputed here, because a coordinate is easy to transpose.
    (GeachSpec(0, 1, 0, 0), "refl"),
    (GeachSpec(0, 1, 2, 0), "trans"),
    (GeachSpec(0, 0, 1, 1), "sym"),
    (GeachSpec(0, 1, 0, 1), "serial"),
    (GeachSpec(1, 0, 1, 1), "eucl"),
    (GeachSpec(1, 1, 1, 1), "directed"),
    (GeachSpec(1, 0, 1, 0), "functional"),
    (GeachSpec(0, 2, 1, 0), "dense"),
])
def test_a_geach_spec_and_its_named_condition_pick_the_same_frames(spec,
                                                                   expected):
    for n in range(1, 4):
        for edges in _frames(n):
            assert (holds_on_finite_frame(f"geach:{spec.m},{spec.n},"
                                          f"{spec.r},{spec.s}", edges, n)
                    == holds_on_finite_frame(expected, edges, n))


# ---------------------------------------------------------------------------
# Non-first-order conditions are refused, not approximated
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("condition", _NOT_FIRST_ORDER)
def test_a_non_first_order_condition_has_no_finite_check_and_no_axiom(
        condition):
    assert set(_NOT_FIRST_ORDER) == {"loeb", "mckinsey", "grz"}
    with pytest.raises(UnsupportedFrameCondition):
        holds_on_finite_frame(condition, frozenset(), 1)
    with pytest.raises(UnsupportedFrameCondition):
        unguarded_frame_axiom(condition)


# ---------------------------------------------------------------------------
# Aliases: the same axiom under the names the literature uses
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("alias,canonical", sorted(AXIOM_ALIASES.items()))
def test_every_alias_builds_the_canonical_axiom(alias, canonical):
    assert modal_axiom(alias) == modal_axiom(canonical)


def test_the_names_that_denote_one_axiom_really_do():
    # C, G1, .2 and G(1,1,1,1) are four spellings of ◇□p → □◇p; Q is C4;
    # W is Löb; Alt1/Alt3 are CD; Alt2 is the shift-reflexivity axiom.
    assert modal_axiom("C") == modal_axiom(".2") == geach_axiom(
        GeachSpec(1, 1, 1, 1))
    assert modal_axiom("Q") == modal_axiom("C4")
    assert modal_axiom("W") == modal_axiom("Loeb")
    assert modal_axiom("Alt1") == modal_axiom("Alt3") == modal_axiom("CD")
    assert modal_axiom("Alt2") == modal_axiom("Mshift")


def test_M_is_not_silently_taken_for_T():
    # "M" names T in some texts and the shift-reflexivity axiom in others.
    # The registry refuses the letter rather than picking a reading.
    with pytest.raises(ValueError, match="unknown modal axiom"):
        modal_axiom("M")


# ---------------------------------------------------------------------------
# One table for six routes
# ---------------------------------------------------------------------------

def test_every_route_reads_the_same_frame_table():
    from unicode_fol_kit.atp import fitch, kripke_enum, modal_tableau
    from unicode_fol_kit.fol import modal_translation, qml
    from unicode_fol_kit.hol import isabelle_modal

    for module, attribute in ((qml, "_FRAMES"),
                              (modal_tableau, "_FRAMES"),
                              (kripke_enum, "_FRAMES"),
                              (fitch, "_FRAME_AXIOMS"),
                              (modal_translation, "_HYBRID_FRAMES"),
                              (isabelle_modal, "_FRAMES")):
        assert getattr(module, attribute) is FRAMES, module.__name__


def test_the_systems_are_the_ones_their_axioms_say_they_are():
    # Spot-pinned rather than recomputed, so a silent edit to the table
    # (dropping 4 from S4, say) fails here.
    assert FRAMES["K"] == ()
    assert FRAMES["S4"] == ("refl", "trans")
    assert FRAMES["S5"] == ("refl", "trans", "sym")
    assert FRAMES["KD45"] == ("serial", "trans", "eucl")
    assert FRAMES["S4.1"] == ("refl", "trans", "mckinsey")
    assert FRAMES["S4.2"] == ("refl", "trans", "directed")
    assert FRAMES["S4.3"] == ("refl", "trans", "connected")
    assert FRAMES["GL"] == ("trans", "loeb")
    assert FRAMES["Grz"] == ("refl", "trans", "grz")
    assert FRAMES["Ver"] == ("empty",)
    # The two spellings of one system are the same system.
    assert FRAMES["D"] == FRAMES["KD"]
    assert FRAMES["B"] == FRAMES["KTB"]


def test_a_geach_spec_is_accepted_as_a_frame_name():
    assert resolve_frame("G(1,1,1,1)") == ("geach:1,1,1,1",)
    assert parse_geach("G(0,2,1,0)") == GeachSpec(0, 2, 1, 0)
    assert parse_geach("S4") is None
    with pytest.raises(ValueError, match="Geach spec"):
        resolve_frame("G(1,1,1)")


def test_an_unknown_frame_names_what_is_available():
    with pytest.raises(ValueError, match="unknown frame"):
        resolve_frame("S99")


# ---------------------------------------------------------------------------
# The routes agree on what each system validates
# ---------------------------------------------------------------------------

#: (axiom, its system) for the conditions a FIRST-ORDER route can carry.
_CHARACTERISTIC = [
    ("T", "T"), ("D", "KD"), ("B", "B"), ("4", "K4"), ("5", "K5"),
    ("CD", "KCD"), ("C4", "KC4"), ("Mshift", "KShift"), ("Ver", "Ver"),
    (".2", "S4.2"), (".3", "S4.3"),
]


@pytest.mark.parametrize("axiom,frame", _CHARACTERISTIC)
def test_the_first_order_route_validates_each_axiom_on_its_own_frame(axiom,
                                                                     frame):
    """Z3 over the standard translation: valid on the system the axiom
    characterises, and NOT valid on K — the second half is what makes the
    first half evidence rather than a tautology check."""
    from unicode_fol_kit.fol.qml import qml_is_valid

    formula = modal_axiom(axiom)
    assert qml_is_valid(formula, frame=frame) is True
    assert qml_is_valid(formula, frame="K") is False


@pytest.mark.parametrize("axiom,frame", _CHARACTERISTIC)
def test_the_hybrid_route_agrees_with_the_first_order_one(axiom, frame):
    from unicode_fol_kit.fol.modal_translation import hybrid_is_valid

    formula = modal_axiom(axiom)
    assert hybrid_is_valid(formula, frame=frame) is True
    assert hybrid_is_valid(formula, frame="K") is False


@pytest.mark.parametrize("axiom,frame", _CHARACTERISTIC)
def test_the_enumerator_finds_no_countermodel_on_the_right_frame(axiom, frame):
    """The finite enumerator cannot PROVE, but its countermodel search must
    come back empty exactly where the axiom is valid — and non-empty on K.
    This is the check that would have failed while ``_holds_conditions``
    still ignored conditions it did not recognise."""
    from unicode_fol_kit.atp.kripke_enum import modal_enum_search

    formula = modal_axiom(axiom)
    assert modal_enum_search(formula, frame=frame, max_worlds=3).model is None
    assert modal_enum_search(formula, frame="K", max_worlds=3).model is not None


@pytest.mark.parametrize("axiom,frame", [
    ("T", "T"), ("D", "KD"), ("B", "B"), ("4", "K4"), ("5", "K5"),
])
def test_the_tableau_agrees_on_the_conditions_it_has_rules_for(axiom, frame):
    from unicode_fol_kit.atp.modal_tableau import is_modal_valid

    formula = modal_axiom(axiom)
    assert is_modal_valid(formula, frame=frame) is True
    assert is_modal_valid(formula, frame="K") is False


@pytest.mark.parametrize("frame,condition", [
    ("S4.2", "directed"), ("KCD", "functional"), ("KC4", "dense"),
    ("KShift", "shift_refl"), ("Ver", "empty"), ("S4.3", "connected"),
])
def test_the_tableau_refuses_what_it_has_no_rule_for(frame, condition):
    """Named, with the route that does carry it named too — never ignored."""
    from unicode_fol_kit.atp.modal_tableau import is_modal_valid

    with pytest.raises(UnsupportedFrameCondition, match=condition):
        is_modal_valid(modal_axiom("T"), frame=frame)


@pytest.mark.parametrize("frame", ["GL", "S4.1", "Grz"])
def test_every_first_order_route_refuses_the_non_first_order_systems(frame):
    from unicode_fol_kit.atp.kripke_enum import modal_enum_search
    from unicode_fol_kit.fol.modal_translation import hybrid_is_valid
    from unicode_fol_kit.fol.qml import qml_is_valid

    formula = modal_axiom("T")
    for call in (lambda: qml_is_valid(formula, frame=frame),
                 lambda: hybrid_is_valid(formula, frame=frame),
                 lambda: modal_enum_search(formula, frame=frame)):
        with pytest.raises(NotImplementedError):
            call()


@pytest.mark.parametrize("frame,axiom_name", [
    ("GL", "loeb"), ("S4.1", "mckinsey"), ("Grz", "grz"),
])
def test_the_higher_order_routes_carry_what_the_others_refuse(frame,
                                                              axiom_name):
    """The HOL routes assert the schema itself, quantified over
    propositions — which is exactly why they can hold what no first-order
    frame condition captures."""
    from unicode_fol_kit.hol.isabelle_modal import isabelle_modal_theory
    from unicode_fol_kit.hol.thf_modal import to_thf_modal_full

    theory = isabelle_modal_theory(modal_axiom("T"), frame=frame,
                                   theory_name="FrameReg")
    assert f"r_{axiom_name}" in theory
    thf = to_thf_modal_full(modal_axiom("T"), frame=frame)
    assert f"thf({axiom_name}," in thf


def test_a_geach_frame_reaches_the_routes_that_understand_it():
    from unicode_fol_kit.atp.kripke_enum import modal_enum_search
    from unicode_fol_kit.fol.modal_translation import hybrid_is_valid
    from unicode_fol_kit.fol.qml import qml_is_valid

    formula = modal_axiom(".2")
    assert qml_is_valid(formula, frame="G(1,1,1,1)") is True
    assert hybrid_is_valid(formula, frame="G(1,1,1,1)") is True
    assert modal_enum_search(formula, frame="G(1,1,1,1)",
                             max_worlds=3).model is None
    # …and a spec whose class does NOT validate it still refutes it.
    assert qml_is_valid(formula, frame="G(0,1,0,0)") is False
