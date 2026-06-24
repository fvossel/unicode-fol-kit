"""Tests for Vampire-backed entailment checking.

Most tests need no Vampire binary: they exercise the TPTP problem generation and
the stdout result parser directly, and the error contracts (bad path, non-FOL
input). A final integration test runs a real Vampire only when one is resolvable,
and is skipped otherwise.
"""

import shutil
import subprocess

import pytest

from unicode_fol_kit import MSFLParser, check_logical_entailment_vampire
from unicode_fol_kit.atp.vampire_entailment import (
    _generate_vampire_input, _is_entailed_output,
)

_FOL = MSFLParser()
_MODUS_PONENS_PREMISES = [
    _FOL.parse("∀x (Human(x) → Mortal(x))"),
    _FOL.parse("Human(socrates)"),
]
_MORTAL = _FOL.parse("Mortal(socrates)")


# ---------------------------------------------------------------------------
# TPTP problem generation (no binary)
# ---------------------------------------------------------------------------

def test_generate_vampire_input_shape():
    """Premises become numbered axioms; the conclusion becomes the conjecture.

    The bodies are exactly each node's ``to_tptp()`` — this pins the fof wrapping,
    role assignment, and naming without re-asserting the TPTP rendering itself.
    """
    text = _generate_vampire_input(_MODUS_PONENS_PREMISES, _MORTAL)
    lines = [ln for ln in text.splitlines() if ln.strip()]
    assert lines == [
        f"fof(premise_1, axiom, {_MODUS_PONENS_PREMISES[0].to_tptp()}).",
        f"fof(premise_2, axiom, {_MODUS_PONENS_PREMISES[1].to_tptp()}).",
        f"fof(goal, conjecture, {_MORTAL.to_tptp()}).",
    ]
    # Exactly one conjecture; one axiom per premise.
    assert text.count(", conjecture, ") == 1
    assert text.count(", axiom, ") == len(_MODUS_PONENS_PREMISES)


def test_generate_vampire_input_no_premises():
    """A conclusion with no premises is just the conjecture (validity check)."""
    conclusion = _FOL.parse("P(socrates) ∨ ¬P(socrates)")
    text = _generate_vampire_input([], conclusion)
    lines = [ln for ln in text.splitlines() if ln.strip()]
    assert lines == [f"fof(goal, conjecture, {conclusion.to_tptp()})."]


# ---------------------------------------------------------------------------
# stdout parsing (no binary)
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("stdout, expected", [
    ("% SZS status Theorem for problem\nRefutation found. Thanks to Tanya!", True),
    ("Refutation found. Thanks to Tanya!", True),
    ("% SZS status Theorem for x", True),
    ("% SZS status CounterSatisfiable for x", False),
    ("% SZS status Satisfiable for x", False),
    ("% SZS status Timeout for x", False),
    ("Termination reason: Time limit", False),
    ("", False),
])
def test_is_entailed_output_parser(stdout, expected):
    """The success signal is SZS-Theorem or a found refutation; nothing else."""
    assert _is_entailed_output(stdout) is expected


# ---------------------------------------------------------------------------
# Error contracts (no real Vampire needed)
# ---------------------------------------------------------------------------

def test_bad_vampire_path_raises_file_not_found():
    """A wrong vampire_path surfaces as FileNotFoundError (as for Prover9)."""
    with pytest.raises(FileNotFoundError):
        check_logical_entailment_vampire(
            _MODUS_PONENS_PREMISES, _MORTAL,
            vampire_path="definitely_not_a_real_vampire_binary_xyz",
        )


def test_non_first_order_input_is_rejected_before_running():
    """A modal premise has no TPTP form, so to_tptp's NotImplementedError
    propagates before any subprocess is spawned (path is never consulted)."""
    modal_premise = MSFLParser(modal=True).parse("□Human(socrates)")
    with pytest.raises(NotImplementedError):
        check_logical_entailment_vampire(
            [modal_premise], _MORTAL, vampire_path="vampire",
        )


# ---------------------------------------------------------------------------
# Integration — only when a Vampire binary is actually present
# ---------------------------------------------------------------------------

_VAMPIRE = shutil.which("vampire")


@pytest.mark.skipif(_VAMPIRE is None, reason="no Vampire binary on PATH")
def test_vampire_decides_entailment_when_installed():
    """Modus ponens is entailed; a missing premise leaves it underivable."""
    assert check_logical_entailment_vampire(
        _MODUS_PONENS_PREMISES, _MORTAL, vampire_path=_VAMPIRE) is True
    assert check_logical_entailment_vampire(
        [_FOL.parse("Human(socrates)")], _MORTAL, vampire_path=_VAMPIRE) is False


def _wsl_vampire_ok():
    """True iff a Vampire is reachable through ``wsl vampire`` (Windows + WSL)."""
    try:
        result = subprocess.run(["wsl.exe", "vampire", "--version"],
                                capture_output=True, text=True, timeout=20)
        return result.returncode == 0 and "Vampire" in result.stdout
    except Exception:  # noqa: BLE001 — any failure means "not available"
        return False


_WSL_VAMPIRE = _wsl_vampire_ok()


@pytest.mark.skipif(not _WSL_VAMPIRE,
                    reason="no Vampire reachable via 'wsl vampire'")
def test_vampire_via_wsl_decides_entailment():
    """Drive a Linux Vampire under WSL from Windows (use_wsl=True).

    Exercises the full path: TPTP generation -> Windows temp file -> wslpath
    translation -> wsl.exe vampire -> SZS parsing. Uses multi-character constants
    (NAME tokens), since single lowercase letters are VARIABLEs and Vampire
    rejects unquantified variables.
    """
    kw = dict(vampire_path="vampire", use_wsl=True)
    # Modus ponens holds; dropping the rule leaves it underivable.
    assert check_logical_entailment_vampire(_MODUS_PONENS_PREMISES, _MORTAL, **kw) is True
    assert check_logical_entailment_vampire(
        [_FOL.parse("Human(socrates)")], _MORTAL, **kw) is False
    # A transitive chain over a real constant is entailed.
    chain = [_FOL.parse("∀x (A(x) → B(x))"), _FOL.parse("∀x (B(x) → C(x))"),
             _FOL.parse("A(dave)")]
    assert check_logical_entailment_vampire(chain, _FOL.parse("C(dave)"), **kw) is True
    # A different individual is not reached by that chain.
    assert check_logical_entailment_vampire(chain, _FOL.parse("C(erin)"), **kw) is False
