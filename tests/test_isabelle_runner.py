"""Unit tests for the Isabelle runner that need NO Isabelle installation.

These cover the pure machinery: path translation, the proof-battery / nitpick
proof construction, install validation, verdict dataclass semantics, and the
graceful no-Isabelle path. The *live* differential validation against a real
Isabelle is in ``test_isabelle_runner_live.py`` (skipped when none is present).
"""

import os
import pytest

from unicode_fol_kit.fol.nodes import Atom, Implies, Box, Diamond
from unicode_fol_kit.hol import isabelle_runner as R
from unicode_fol_kit.hol.isabelle_runner import (
    ModalVerdict, FolVerdict, IsabelleInstall, IsabelleNotAvailable,
    isabelle_decide_modal, isabelle_decide_fol, check_theory,
    DEFAULT_METHODS, VALID, INVALID, UNKNOWN,
)
from unicode_fol_kit.hol.isabelle_modal import isabelle_modal_theory, modal_axiom_names

p, q = Atom("p", ()), Atom("q", ())


# --------------------------------------------------------------------------- #
# Cygwin path translation.
# --------------------------------------------------------------------------- #

def test_cygpath_basic_drive():
    assert R._cygpath(r"C:\Users\me\x") == "/cygdrive/c/Users/me/x"
    assert R._cygpath(r"D:\Isabel\Isabelle2025-2") == "/cygdrive/d/Isabel/Isabelle2025-2"


def test_cygpath_lowercases_drive_letter():
    assert R._cygpath(r"E:\Foo").startswith("/cygdrive/e/")


# --------------------------------------------------------------------------- #
# Proof-battery construction.
# --------------------------------------------------------------------------- #

def test_battery_proof_with_axioms_uses_them():
    proof = R._battery_proof(["r_refl", "r_trans"], DEFAULT_METHODS)
    # axioms chained in, and handed explicitly to meson/metis
    assert "using r_refl r_trans" in proof
    assert "meson r_refl r_trans" in proof
    assert "metis r_refl r_trans" in proof
    assert proof.strip().startswith("using")
    assert " by (" in proof


def test_battery_proof_without_axioms_has_no_using():
    proof = R._battery_proof([], ("blast", "auto"))
    assert "using" not in proof
    assert proof.strip() == "by (blast | auto)"


def test_battery_proof_smt_wrapped():
    proof = R._battery_proof([], ("smt",))
    assert "(smt (verit))" in proof


def test_infra_error_detection():
    # Infrastructure-failure signatures are recognised; an honest no-proof / nitpick
    # output is not. (UNKNOWN with infra_error != None means a broken theory/env, not
    # benign incompleteness — it never changes the verdict.)
    assert R._infra_error("*** Outer syntax error at ...") == "Outer syntax error"
    assert R._infra_error('*** Bad name: "r_"') == "Bad name"
    assert R._infra_error("x", "java.lang.OutOfMemoryError: Java heap space") is not None
    assert R._infra_error("[runner] wall-clock timeout after 60.0s") == "wall-clock timeout"
    assert R._infra_error("Nitpick found a counterexample for card i = 1") is None
    assert R._infra_error("Finished S_x (0:00:02 elapsed time)", "") is None


def test_alethic_countermodel_search():
    # Needs no Isabelle: a bounded Kripke enumeration that exhibits a witness for an
    # INVALID propositional alethic formula, and declines outside the fragment.
    from unicode_fol_kit.fol.nodes import Box, Quantifier, Variable, Knows, Constant
    cm = R._find_alethic_countermodel(Implies(Box(p), p), "K")        # T axiom, invalid in K
    assert cm and "Kripke counter-model" in cm and "false at world" in cm
    assert R._find_alethic_countermodel(Implies(Box(p), p), "T") is None     # valid -> no model
    x = Variable("x")
    assert R._find_alethic_countermodel(Quantifier("∀", x, Atom("A", [x])), "K") is None  # quantified
    assert R._find_alethic_countermodel(Knows(Constant("a"), p), "K") is None             # epistemic


def test_battery_proof_splices_into_loadable_theory_shape():
    # The runner emits the goal theory with the battery proof spliced in; check the
    # shape: a real lemma, the battery, no 'oops' left in the proof, ends with end.
    proof = R._battery_proof(["r_refl"], ("blast", "metis"))
    thy = isabelle_modal_theory(Implies(Box(p), p), frame="T", tactic="oops",
                                theory_name="Goal_x", proof=proof)
    assert "lemma modal_goal:" in thy
    assert "using r_refl" in thy
    assert "by (blast | metis r_refl)" in thy
    assert "\n  oops\n" not in thy           # override replaced the oops preset
    assert thy.rstrip().endswith("end")


# --------------------------------------------------------------------------- #
# Install validation / discovery (no real install required).
# --------------------------------------------------------------------------- #

def test_validate_install_rejects_none_and_missing():
    assert R._validate_install(None) is None
    assert R._validate_install(os.path.join(os.sep, "no", "such", "isabelle_xyz")) is None


def test_validate_install_rejects_dir_without_launcher(tmp_path):
    # A directory that exists but has no bin/isabelle is not an install.
    (tmp_path / "bin").mkdir()
    assert R._validate_install(str(tmp_path)) is None


def test_find_isabelle_is_cached_and_returns_install_or_none():
    a = R.find_isabelle()
    b = R.find_isabelle()
    assert a is b                       # cached (same object / both None)
    assert a is None or isinstance(a, IsabelleInstall)


# --------------------------------------------------------------------------- #
# Verdict dataclass semantics.
# --------------------------------------------------------------------------- #

def test_modal_verdict_truthiness_and_props():
    v = ModalVerdict(status=VALID, frame="K", mode="constant", method="prove-battery")
    assert bool(v) is True and v.is_valid and not v.is_invalid and not v.is_unknown
    iv = ModalVerdict(status=INVALID, frame="K", mode="constant", countermodel="…")
    assert bool(iv) is False and iv.is_invalid
    uk = ModalVerdict(status=UNKNOWN, frame="K", mode="constant")
    assert bool(uk) is False and uk.is_unknown
    assert "valid" in str(v)


# --------------------------------------------------------------------------- #
# Graceful absence: when no Isabelle can be located the API raises clearly.
# --------------------------------------------------------------------------- #

def test_decide_raises_when_no_isabelle(monkeypatch):
    monkeypatch.setattr(R, "find_isabelle", lambda *a, **k: None)
    with pytest.raises(IsabelleNotAvailable):
        isabelle_decide_modal(Implies(Box(p), p), frame="T")


def test_check_theory_raises_when_no_isabelle(monkeypatch):
    monkeypatch.setattr(R, "find_isabelle", lambda *a, **k: None)
    with pytest.raises(IsabelleNotAvailable):
        check_theory("theory T imports Main begin end", "T")


def test_isabelle_available_reflects_find(monkeypatch):
    monkeypatch.setattr(R, "find_isabelle", lambda *a, **k: None)
    assert R.isabelle_available() is False


def test_fol_verdict_semantics():
    assert bool(FolVerdict(status=VALID, method="prove-battery")) is True
    assert FolVerdict(status=INVALID).is_invalid
    assert FolVerdict(status=UNKNOWN).is_unknown and not FolVerdict(status=UNKNOWN)
    assert "valid" in str(FolVerdict(status=VALID))


def test_decide_fol_raises_when_no_isabelle(monkeypatch):
    monkeypatch.setattr(R, "find_isabelle", lambda *a, **k: None)
    with pytest.raises(IsabelleNotAvailable):
        isabelle_decide_fol(Implies(p, p))


# --------------------------------------------------------------------------- #
# modal_axiom_names is the contract the runner relies on for `using <axioms>`.
# --------------------------------------------------------------------------- #

def test_modal_axiom_names_per_frame():
    assert modal_axiom_names(Box(p), frame="K") == []
    assert modal_axiom_names(Box(p), frame="T") == ["r_refl"]
    assert modal_axiom_names(Box(p), frame="S4") == ["r_refl", "r_trans"]
    assert set(modal_axiom_names(Box(p), frame="S5")) == {"r_refl", "r_trans", "r_sym"}
