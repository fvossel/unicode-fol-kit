"""Tests for the added modal frames B, S4.2, S4.3 and GL.

B / S4.2 / S4.3 are first-order definable, so the Z3 embedding (``qml_is_valid``)
decides their characteristic axioms — these run everywhere. GL (Gödel–Löb) is
transitive + converse-well-founded, NOT first-order definable, so the Z3 path
rejects it; it lives only in the higher-order Isabelle / THF exporters via the Löb
schema. Structural checks confirm the right frame axioms are emitted; the
Isabelle-gated tests confirm the emitted theories actually prove the characteristic
theorems (and refute the non-theorems).
"""

import pytest

from unicode_fol_kit.fol.nodes import Atom, Implies, Or, Box, Diamond
from unicode_fol_kit.fol.qml import qml_is_valid, to_thf_modal
from unicode_fol_kit.hol.isabelle_modal import (
    isabelle_modal_theory, modal_axiom_names,
)
from unicode_fol_kit.hol.thf_modal import to_thf_modal_full
from unicode_fol_kit.hol.isabelle_runner import isabelle_available, check_theory, isabelle_decide_modal

p, q = Atom("p", ()), Atom("q", ())
_B_AX = Implies(p, Box(Diamond(p)))                                    # Brouwer
_G2 = Implies(Diamond(Box(p)), Box(Diamond(p)))                       # .2 convergence
_G3 = Or(Box(Implies(Box(p), q)), Box(Implies(Box(q), p)))           # .3 linearity
_LOEB = Implies(Box(Implies(Box(p), p)), Box(p))                      # Löb's theorem
_T = Implies(Box(p), p)                                               # T (fails in GL)


# --------------------------------------------------------------------------- #
# First-order frames decided by Z3 (no Isabelle needed).
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("formula, frame, expected", [
    (_B_AX, "B", True), (_B_AX, "S4", False), (_B_AX, "S5", True),
    (_G2, "S4.2", True), (_G2, "S4", False), (_G2, "S5", True),
    (_G3, "S4.3", True), (_G3, "S4", False), (_G3, "S4.2", False),
    (Implies(Box(p), Box(Box(p))), "S4.2", True),       # 4 holds (S4.2 ⊇ S4)
    (Implies(Box(p), p), "B", True),                    # T holds (B ⊇ T)
])
def test_first_order_frame_validities_via_z3(formula, frame, expected):
    assert qml_is_valid(formula, frame=frame) is expected


def test_gl_rejected_by_first_order_embedding():
    with pytest.raises(NotImplementedError, match="GL.*provability|not first-order"):
        qml_is_valid(Box(p), frame="GL")


# --------------------------------------------------------------------------- #
# Structural: the emitted theories / THF carry the right frame axioms.
# --------------------------------------------------------------------------- #

def test_modal_axiom_names_per_frame():
    assert modal_axiom_names(_B_AX, frame="B") == ["r_refl", "r_sym"]
    assert modal_axiom_names(_G2, frame="S4.2") == ["r_refl", "r_trans", "r_directed"]
    assert modal_axiom_names(_G3, frame="S4.3") == ["r_refl", "r_trans", "r_conn"]
    assert modal_axiom_names(_LOEB, frame="GL") == ["r_trans", "r_loeb"]


def test_gl_isabelle_theory_uses_loeb_in_proof():
    thy = isabelle_modal_theory(_LOEB, frame="GL", tactic="blast", theory_name="GLChk")
    assert "r_loeb" in thy
    # GL is irreflexive: the reflexivity axiom must NOT appear.
    assert "r_refl" not in thy
    using_line = next(l for l in thy.splitlines() if l.strip().startswith("using"))
    assert "r_loeb" in using_line and "r_trans" in using_line


def test_thf_exporters_carry_new_frame_axioms():
    assert "thf(loeb" in to_thf_modal(_LOEB, frame="GL")
    assert "thf(loeb" in to_thf_modal_full(_LOEB, frame="GL")
    assert "thf(directed" in to_thf_modal_full(_G2, frame="S4.2")
    assert "thf(connected" in to_thf_modal_full(_G3, frame="S4.3")


# --------------------------------------------------------------------------- #
# Isabelle-gated: the emitted theories really prove / refute (incl. GL/Löb).
# --------------------------------------------------------------------------- #

_isa = pytest.mark.skipif(not isabelle_available(),
                          reason="no Isabelle installation found")


@_isa
@pytest.mark.parametrize("formula, frame", [
    (_LOEB, "GL"), (_G2, "S4.2"), (_G3, "S4.3"), (_B_AX, "B"),
])
def test_characteristic_theorems_discharge_in_isabelle(formula, frame):
    thy = isabelle_modal_theory(formula, frame=frame, tactic="blast",
                                theory_name="FrameLive")
    r = check_theory(thy, "FrameLive", session_timeout=300)
    assert r.ok, f"[{frame}] blast did not discharge (exit {r.exit_code}):\n{r.output[-1000:]}"


@_isa
def test_gl_does_not_prove_the_t_axiom():
    # T (□p → p) is NOT a GL theorem (GL is irreflexive). The prove battery must not
    # discharge it; nitpick cannot easily model-find against the second-order Löb
    # schema, so the sound verdict is "not valid" (invalid or unknown), never "valid".
    v = isabelle_decide_modal(_T, frame="GL", prove_timeout=120, refute_timeout=120)
    assert v.status != "valid", v
