"""Tests for hybrid logic H(@): nominals + the satisfaction operator.

Covers the four hybrid work surfaces:

1. Kripke evaluation — ``KripkeModel(nominals={...})``: a nominal is true at
   exactly the world it names, ``@i φ`` jumps to that world, unassigned
   nominals raise a ValueError naming the nominal, dangling assignments are
   rejected at construction.
2. The standard translation — ``ST(Nominal i)(w) = (w = nom_i)`` and
   ``ST(@i φ)(w) = ST(φ)(nom_i)`` — pinned structurally AND cross-checked
   differentially against the Kripke evaluator through the pre-existing Tarski
   evaluator (worlds as the FO domain, nominal constants interpreted by the
   nominal assignment).
3. ``hybrid_is_valid`` — every VALID/INVALID claim below is a hand-checked
   standard H(@) (in)validity, justified in a comment; frame sensitivity is
   checked (K vs T vs S4/S5) and PURE modal formulas are cross-checked against
   the independent tableau oracle ``is_modal_valid``.
4. The modal tableau — hybrid inputs raise NotImplementedError (mentioning
   "hybrid") through every public entry point, never a wrong verdict.
"""

import pytest

from unicode_fol_kit import (
    MSFLParser, Node,
    Atom, Not, And, Or, Implies, Iff, Box, Diamond,
    Constant, Variable, Quantifier,
    Nominal, At,
    KripkeModel, satisfies_modal,
    standard_translation,
    is_modal_valid, modal_decide, modal_countermodel, modal_prove,
    modal_tableau_closed, is_valid_tableau,
)
from unicode_fol_kit.atp.modal_tableau import has_modal
from unicode_fol_kit.fol.modal_translation import hybrid_is_valid
from unicode_fol_kit.semantics.tarski import Structure, satisfies

mp = MSFLParser(modal=True)

P = Atom("P", [])
Q = Atom("Q", [])


def _model():
    """The hand-checked reference model.

    Worlds 0 → 1 → 2 (alethic), P true only at 1, Q true only at 2,
    nominal i names world 1, nominal j names world 2.
    """
    return KripkeModel(
        worlds={0, 1, 2},
        relations={"alethic": {(0, 1), (1, 2)}},
        valuation={1: {"P"}, 2: {"Q"}},
        nominals={"i": 1, "j": 2},
    )


# =========================
# 1. Kripke evaluation
# =========================

def test_nominal_true_exactly_at_its_world():
    m = _model()
    # i names world 1: true there, false at 0 and 2.
    assert satisfies_modal(Nominal("i"), m, 0) is False
    assert satisfies_modal(Nominal("i"), m, 1) is True
    assert satisfies_modal(Nominal("i"), m, 2) is False
    # j names world 2.
    assert satisfies_modal(Nominal("j"), m, 0) is False
    assert satisfies_modal(Nominal("j"), m, 1) is False
    assert satisfies_modal(Nominal("j"), m, 2) is True


def test_at_jumps_worlds():
    m = _model()
    # @i P evaluates P at world 1 (where P holds) — true from EVERY world.
    for w in (0, 1, 2):
        assert satisfies_modal(At("i", P), m, w) is True
    # @j P evaluates P at world 2 (P false there) — false from every world.
    for w in (0, 1, 2):
        assert satisfies_modal(At("j", P), m, w) is False
    # @j Q: Q holds at world 2 — true from every world.
    for w in (0, 1, 2):
        assert satisfies_modal(At("j", Q), m, w) is True


def test_at_i_i_true_everywhere():
    m = _model()
    # @i i: the nominal i is (trivially) true at the world it names.
    for w in (0, 1, 2):
        assert satisfies_modal(At("i", Nominal("i")), m, w) is True
    # ... but @j i is false: world 2 is not world 1.
    for w in (0, 1, 2):
        assert satisfies_modal(At("j", Nominal("i")), m, w) is False


def test_hybrid_composes_with_modalities():
    m = _model()
    # ◇i: "some successor is the world named i".
    assert satisfies_modal(Diamond(Nominal("i")), m, 0) is True   # 0 → 1 = i
    assert satisfies_modal(Diamond(Nominal("i")), m, 1) is False  # 1 → 2 ≠ i
    assert satisfies_modal(Diamond(Nominal("i")), m, 2) is False  # no successors
    # □(i → P) at 0: the only successor is 1 = i, and P holds at 1.
    assert satisfies_modal(Box(Implies(Nominal("i"), P)), m, 0) is True
    # @i ◇j: from world 1 the successor 2 is named j.
    assert satisfies_modal(At("i", Diamond(Nominal("j"))), m, 0) is True
    # Instance of the bridge law at world 0: ◇i ∧ @i P → ◇P (all three parts true).
    bridge = mp.parse("(◇i ∧ @i P) → ◇P")
    assert satisfies_modal(bridge, m, 0) is True


def test_unassigned_nominal_raises_naming_it():
    m = _model()
    with pytest.raises(ValueError, match="'k'"):
        satisfies_modal(Nominal("k"), m, 0)
    with pytest.raises(ValueError, match="'k'"):
        satisfies_modal(At("k", P), m, 0)
    # A model built without nominals= rejects every nominal the same way.
    bare = KripkeModel({0, 1}, {"alethic": {(0, 1)}}, {1: {"P"}})
    assert bare.nominals == {}
    with pytest.raises(ValueError, match="'i'"):
        satisfies_modal(Nominal("i"), bare, 0)


def test_dangling_nominal_assignment_rejected_at_construction():
    with pytest.raises(ValueError, match="'i'"):
        KripkeModel({0, 1}, nominals={"i": 7})


def test_nominals_are_copied():
    src = {"i": 0}
    m = KripkeModel({0, 1}, nominals=src)
    src["j"] = 1  # later edits to the caller's dict must not leak in
    assert m.nominals == {"i": 0}
    # Non-hybrid behaviour is untouched: plain modal evaluation still works.
    m2 = KripkeModel({0, 1}, {"alethic": {(0, 1)}}, {1: {"P"}}, nominals={"i": 1})
    assert satisfies_modal(Diamond(P), m2, 0) is True


# =========================
# 2. Standard translation
# =========================

def test_st_nominal_is_world_equality():
    # ST(i)(w) = (w = nom_i) — the "nom_" prefix keeps user constants safe.
    assert standard_translation(Nominal("i")) == \
        Atom("=", [Variable("w"), Constant("nom_i")])
    assert standard_translation(Nominal("i")).to_unicode_str() == "w = nom_i"
    # The world= parameter re-names the free current-world term.
    assert standard_translation(Nominal("i"), world="u") == \
        Atom("=", [Variable("u"), Constant("nom_i")])


def test_st_at_reanchors_the_world_term():
    # ST(@i P)(w) = P(nom_i): no quantifier, just a constant world term.
    assert standard_translation(At("i", P)) == Atom("P", [Constant("nom_i")])
    # ST(@i □P)(w) = ∀w0 (R(nom_i, w0) → P(w0)) — the box quantifies FROM nom_i.
    assert standard_translation(At("i", Box(P))) == Quantifier(
        "∀", Variable("w0"),
        Implies(Atom("R", [Constant("nom_i"), Variable("w0")]),
                Atom("P", [Variable("w0")])))
    # ST(◇i)(w) = ∃w0 (R(w, w0) ∧ w0 = nom_i).
    assert standard_translation(Diamond(Nominal("i"))) == Quantifier(
        "∃", Variable("w0"),
        And(Atom("R", [Variable("w"), Variable("w0")]),
            Atom("=", [Variable("w0"), Constant("nom_i")])))


def test_st_nom_prefix_avoids_user_constant_collision():
    # An atom whose own argument is the ground constant `i` stays `i`; only the
    # nominal becomes nom_i, so the two cannot collide.
    f = At("i", Atom("P", [Constant("i")]))
    assert standard_translation(f) == Atom("P", [Constant("i"), Constant("nom_i")])


def _structure_from(model):
    """First-order companion of the reference Kripke model.

    Worlds are the FO domain, the alethic relation is R, each propositional
    atom becomes the unary predicate {(w,) : atom true at w}, and each nominal
    constant nom_i denotes the world the nominal assignment names.
    """
    predicates = {("R", 2): set(model.relations.get("alethic", set()))}
    for name in ("P", "Q"):
        predicates[(name, 1)] = {(w,) for w in model.worlds
                                 if name in model.atoms_true_at(w)}
    constants = {"nom_" + n: w for n, w in model.nominals.items()}
    return Structure(domain=set(model.worlds), constants=constants,
                     predicates=predicates)


def test_st_agrees_with_kripke_via_tarski():
    """Differential soundness check: Kripke truth == Tarski truth of the ST image."""
    m = _model()
    s = _structure_from(m)
    formulas = [
        Nominal("i"),
        Nominal("j"),
        At("i", P),
        At("j", Q),
        At("i", Nominal("j")),
        At("i", Nominal("i")),
        Diamond(Nominal("i")),
        Box(Implies(Nominal("i"), P)),
        And(Nominal("i"), Diamond(P)),
        At("i", Diamond(Nominal("j"))),
        Implies(Diamond(Nominal("i")), At("i", P)),
        Not(At("j", P)),
        mp.parse("(◇i ∧ @i P) → ◇P"),
        mp.parse("@i (P → ◇j)"),
    ]
    for f in formulas:
        st = standard_translation(f)
        for w in m.worlds:
            assert satisfies_modal(f, m, w) == satisfies(st, s, {"w": w}), \
                f"ST/Kripke mismatch for {f.to_unicode_str()} at world {w}"


# =========================
# 3. Validity: hybrid_is_valid
# =========================

# Standard H(@) validities over K. Each is a hand-checked theorem:
#   @i i               — a nominal holds at the world it names (reflexivity of @).
#   @i P ↔ ¬@i ¬P     — @ is self-dual (it targets exactly one world).
#   @i (P→Q) → (@i P → @i Q) — @ is a normal modality (K-distribution).
#   @i j ↔ @j i       — world-equality is symmetric.
#   @i @j P ↔ @j P    — @ jumps discard any outer jump (transitivity of @).
#   (i ∧ P) → @i P    — introduction: if HERE is i and P holds here, P holds at i.
#   (i ∧ ◇P) → @i ◇P — the same with a modalized body.
#   (◇i ∧ @i P) → ◇P — bridge: a successor named i where P holds witnesses ◇P.
#   @i (P ∨ ¬P)       — @ of a tautology is valid (necessitation for @).
VALID_K = [
    "@i i",
    "@i P ↔ ¬@i ¬P",
    "@i (P → Q) → (@i P → @i Q)",
    "@i j ↔ @j i",
    "@i @j P ↔ @j P",
    "(i ∧ P) → @i P",
    "(i ∧ ◇P) → @i ◇P",
    "(◇i ∧ @i P) → ◇P",
    "@i (P ∨ ¬P)",
]

# Hand-checked NON-theorems over K, each refuted by a two-world model:
#   @i P → P   — P may hold at the i-world but fail at the evaluation world.
#   i          — a nominal fails at every world other than the one it names.
#   P → @i P   — P here says nothing about P at the i-world.
#   ◇i → □i   — the current world may see i AND a second, different world.
INVALID_K = [
    "@i P → P",
    "i",
    "P → @i P",
    "◇i → □i",
]


@pytest.mark.parametrize("text", VALID_K)
def test_hybrid_validities_over_K(text):
    assert hybrid_is_valid(mp.parse(text), frame="K") is True


@pytest.mark.parametrize("text", INVALID_K)
def test_hybrid_invalidities_over_K(text):
    assert hybrid_is_valid(mp.parse(text), frame="K") is False


@pytest.mark.parametrize("text", VALID_K)
def test_K_validities_persist_on_stronger_frames(text):
    # T/S4/S5 models are a SUBCLASS of K models, so K-validity implies validity there.
    f = mp.parse(text)
    assert hybrid_is_valid(f, frame="T") is True
    assert hybrid_is_valid(f, frame="S5") is True


def test_frame_sensitivity_with_a_nominal():
    # (□P ∧ i) → P is the T schema with a nominal conjoined: it needs R(w, w).
    f = mp.parse("(□P ∧ i) → P")
    assert hybrid_is_valid(f, frame="K") is False   # dead-end world named i refutes it
    assert hybrid_is_valid(f, frame="T") is True    # reflexivity gives P at w itself
    assert hybrid_is_valid(f, frame="S4") is True   # S4 ⊇ T conditions
    assert hybrid_is_valid(f, frame="S5") is True   # S5 ⊇ T conditions


def test_frame_sensitivity_four_schema_at_a_named_world():
    # @i (□P → □□P): the 4 schema pinned at the world named i. Valid exactly
    # when R is transitive — a reflexive-only frame can fail it at the i-world.
    g = mp.parse("@i (□P → □□P)")
    assert hybrid_is_valid(g, frame="T") is False
    assert hybrid_is_valid(g, frame="S4") is True
    assert hybrid_is_valid(g, frame="S5") is True


def test_unknown_frame_rejected():
    # Since the frame tables were unified (fol.frames), this route understands
    # every named system the others do — KD45 among them — so the refusal is
    # pinned on a name that is genuinely not a system.
    with pytest.raises(ValueError, match="unknown frame"):
        hybrid_is_valid(mp.parse("@i i"), frame="S99")


def test_the_hybrid_route_shares_the_common_frame_table():
    from unicode_fol_kit.fol.frames import FRAMES
    from unicode_fol_kit.fol.modal_translation import _HYBRID_FRAMES

    assert _HYBRID_FRAMES is FRAMES


# --- cross-check: pure modal formulas must agree with the tableau oracle ---

# (formula text, expected over K, expected over T) — all hand-checked standards:
#   K axiom: valid on every frame.  □P → P: needs reflexivity (T).
#   ◇(P∨Q) ↔ ◇P∨◇Q and □(P∧Q) ↔ □P∧□Q: valid on every frame (normality).
#   □P → ◇P (D): needs seriality — K lacks it, reflexive T has it.
PURE_MODAL = [
    ("□(P → Q) → (□P → □Q)", True, True),
    ("□P → P", False, True),
    ("◇(P ∨ Q) ↔ (◇P ∨ ◇Q)", True, True),
    ("□(P ∧ Q) ↔ (□P ∧ □Q)", True, True),
    ("□P → ◇P", False, True),
]


@pytest.mark.parametrize("text,exp_K,exp_T", PURE_MODAL)
def test_pure_modal_agrees_with_tableau_oracle(text, exp_K, exp_T):
    f = mp.parse(text)
    assert hybrid_is_valid(f, frame="K") is exp_K
    assert hybrid_is_valid(f, frame="T") is exp_T
    # ... and both verdicts match the independent modal-tableau oracle.
    assert is_modal_valid(f, frame="K") is exp_K
    assert is_modal_valid(f, frame="T") is exp_T


# =========================
# 4. Tableau rejection
# =========================

def test_tableau_rejects_hybrid_everywhere():
    hybrid = mp.parse("@i P → P")
    with pytest.raises(NotImplementedError, match="hybrid"):
        is_modal_valid(hybrid)
    with pytest.raises(NotImplementedError, match="hybrid"):
        modal_decide(mp.parse("◇i"))
    with pytest.raises(NotImplementedError, match="hybrid"):
        modal_countermodel(At("i", P), frame="S5")
    with pytest.raises(NotImplementedError, match="hybrid"):
        modal_prove([mp.parse("@i P")], P)
    with pytest.raises(NotImplementedError, match="hybrid"):
        modal_tableau_closed([Nominal("i"), Not(Nominal("i"))])


def test_classical_tableau_routes_hybrid_to_the_clean_rejection():
    # has_modal flags hybrid constructs, so is_valid_tableau routes them to the
    # modal engine, whose guard raises — never a silent wrong verdict.
    assert has_modal(Nominal("i")) is True
    assert has_modal(At("i", P)) is True
    assert has_modal(Implies(P, Q)) is False
    with pytest.raises(NotImplementedError, match="hybrid"):
        is_valid_tableau(mp.parse("@i P"))
    # Non-hybrid inputs are untouched by the guard.
    assert is_valid_tableau(mp.parse("P ∨ ¬P")) is True
    assert is_modal_valid(mp.parse("□(P → Q) → (□P → □Q)"), frame="K") is True


# =========================
# 5. Regression pins: parsing / rendering round-trips
# =========================

@pytest.mark.parametrize("text", [
    "i",
    "@i P",
    "@i j ↔ @j i",
    "(◇i ∧ @i P) → ◇P",
    "@i (P → ◇j)",
])
def test_hybrid_round_trips(text):
    f = mp.parse(text)
    assert mp.parse(f.to_unicode_str()) == f            # render → reparse
    assert Node.from_dict(f.to_dict()) == f             # dict serialisation


def test_hybrid_parse_shapes():
    assert mp.parse("i") == Nominal("i")
    assert mp.parse("@i P") == At(Nominal("i"), P)
    assert mp.parse("@i P").to_unicode_str() == "@i P"
    # At coerces a bare string, and exposes the nominal as .agent for renderers.
    assert At("i", P) == At(Nominal("i"), P)
    assert At("i", P).agent == Nominal("i")
