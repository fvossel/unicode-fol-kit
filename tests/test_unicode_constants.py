"""Non-ASCII (Greek) constant names — e.g. a threshold θ in μ(x, dim) > θ.

Greek letters (except the reserved operator glyphs λ / μ) lex as CONSTANT tokens, so
they can name ground constants. The Kripke evaluator and Z3 carry the raw unicode
name; the ASCII-only Prover9 / TPTP exporters transliterate deterministically and
reversibly (θ → theta), so an emitted problem is always valid ASCII.
"""

import pytest

from unicode_fol_kit.fol.msflparser import MSFLParser
from unicode_fol_kit.fol.nodes import Node
from unicode_fol_kit.fol._fol_nodes import (
    Constant, Measure,
    constant_name_to_ascii, constant_name_from_ascii,
    _GREEK_CONST_TO_ASCII,
)
from unicode_fol_kit.fol._msfl_nodes import Lambda

_FOL = MSFLParser()
_MODAL = MSFLParser(modal=True)


# --------------------------------------------------------------------------- #
# Parsing: a bare Greek letter is a Constant (not a name/variable/nominal).
# --------------------------------------------------------------------------- #

def test_bare_greek_letter_is_constant():
    rhs = _FOL.parse("μ(x, volume) > θ").args[1]
    assert isinstance(rhs, Constant)
    assert rhs.name == "θ"


def test_greek_constant_in_modal_mode_is_constant_not_nominal():
    # In modal mode a bare lowercase ASCII name is a hybrid nominal; a Greek letter
    # still lexes as CONSTANT (higher priority), so it stays a Constant.
    f = _MODAL.parse("◇ Above(θ, c_limit)")
    arg0 = f.formula.args[0]
    assert isinstance(arg0, Constant) and arg0.name == "θ"


def test_multiple_greek_letters_all_parse():
    for g in _GREEK_CONST_TO_ASCII:
        c = _FOL.parse(f"P({g})").args[0]
        assert isinstance(c, Constant) and c.name == g


def test_lambda_and_mu_are_not_constants():
    # μ (U+03BC) stays the Measure operator; λ (U+03BB) stays the binder — neither is
    # swallowed as a Greek constant.
    assert isinstance(_FOL.parse("μ(a, b) > c").args[0], Measure)
    assert isinstance(_FOL.parse("λx. P(x)"), Lambda)


# --------------------------------------------------------------------------- #
# Export: ASCII-only back-ends transliterate; output is pure ASCII.
# --------------------------------------------------------------------------- #

def test_prover9_tptp_transliterate_theta():
    f = _FOL.parse("μ(x, volume) > θ")
    p9, tptp = f.to_prover9(), f.to_tptp()
    assert "theta" in p9 and "theta" in tptp
    assert "θ" not in p9 and "θ" not in tptp
    assert p9.isascii() and tptp.isascii()


def test_export_is_ascii_for_every_greek_constant():
    for g in _GREEK_CONST_TO_ASCII:
        f = _FOL.parse(f"P({g})")
        assert f.to_prover9().isascii()
        assert f.to_tptp().isascii()


# --------------------------------------------------------------------------- #
# Transliteration scheme: deterministic and reversible per single symbol.
# --------------------------------------------------------------------------- #

def test_translit_round_trip_greek_ascii_and_escape():
    cases = list(_GREEK_CONST_TO_ASCII) + ["x", "john", "c_limit", "⊙", "π"]
    for name in cases:
        assert constant_name_from_ascii(constant_name_to_ascii(name)) == name


def test_translit_theta_is_readable():
    assert constant_name_to_ascii("θ") == "theta"
    assert constant_name_from_ascii("theta") == "θ"


def test_non_greek_non_ascii_uses_codepoint_escape():
    # ⊙ (U+2299) is not in the Greek table -> reversible uXXXX escape, never raw.
    assert constant_name_to_ascii("⊙") == "u2299"
    assert constant_name_from_ascii("u2299") == "⊙"


def test_ascii_names_pass_through_unchanged():
    for name in ["x", "john", "c_theta", "height"]:
        assert constant_name_to_ascii(name) == name


# --------------------------------------------------------------------------- #
# Serialization keeps the raw unicode name.
# --------------------------------------------------------------------------- #

def test_serialization_round_trip_preserves_unicode():
    f = _FOL.parse("μ(x, volume) > θ")
    f2 = Node.from_dict(f.to_dict())
    assert f2 == f
    assert f2.args[1].name == "θ"
