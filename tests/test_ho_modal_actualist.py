"""Domain regime (``mode=``) at THIRD order: hol.ho_modal's actualist port (C18, axis 1).

``hol.ho_modal`` used to be possibilist/constant-domain only, with no ``mode=``
parameter at all. This module pins the widened behaviour:

1. The default (``mode="constant"``, i.e. unspecified) is BYTE-IDENTICAL to
   the pre-widening output -- so ``hol.goedel`` and the docs example are
   unaffected (see ``test_default_mode_is_unchanged_*`` below).
2. An actualist ``mode`` (``"varying"``/``"increasing"``/``"cumulative"``/
   ``"decreasing"``) existsAt-guards INDIVIDUAL quantification only; a
   PROPERTY quantifier (``SecondOrderQuantifier``) stays ``mall``/``mex``,
   unguarded, under every mode -- the one new judgment call this port makes.
3. Both claims are checked against an INDEPENDENT oracle: the first-order
   shallow embedding's own ``qml_is_valid`` (Z3-backed), via the classic
   Barcan formula / converse Barcan formula litmus test, on formulas that
   carry NO PredicateTerm (property argument) at all -- so the third-order
   machinery is exercised on exactly the fragment the first-order oracle can
   also decide. The live-Isabelle tests then confirm this module's OWN
   theories discharge (prove or nitpick-refute) exactly where the oracle
   says they should, for every one of the four domain regimes.
"""

import pytest

from unicode_fol_kit import MSFLParser, qml_is_valid, BARCAN, CONVERSE_BARCAN
from unicode_fol_kit.hol.ho_modal import (
    HoGoal, isabelle_ho_modal_theory, to_thf_ho_modal,
)
from unicode_fol_kit.hol.isabelle_runner import check_theory, isabelle_available

TOM = MSFLParser(third_order=True, modal=True)

# The Barcan formula / converse Barcan formula, spelled out in the kit's own
# syntax and parsed THIRD-order-modal -- structurally identical to
# unicode_fol_kit.fol.qml.BARCAN / CONVERSE_BARCAN (same shape: ◇∃x A(x) ↔
# ∃x ◇A(x), just parsed through a different grammar), so qml_is_valid decides
# the SAME formula this module embeds, not a lookalike.
BF_TEXT = "◇∃x A(x) → ∃x ◇A(x)"
CBF_TEXT = "∃x ◇A(x) → ◇∃x A(x)"

# The property-quantifier analogue of BF -- same shape, but ∃P/◇ over a
# PROPERTY variable rather than an individual. Used to pin the judgment call:
# under an actualist mode this must stay VALID (property domains are
# constant) exactly where the individual-level BF above stops being valid.
BF_PROPERTY_TEXT = "◇∃P Pos(P) → ∃P ◇Pos(P)"


# --------------------------------------------------------------------------- #
# 1. Defaults are unchanged (byte-identical to before this port).
# --------------------------------------------------------------------------- #

def test_default_mode_is_unchanged_isabelle():
    """Omitting ``mode=`` renders exactly like ``mode="constant"`` -- and like
    the pre-C18 module, which had no existsAt machinery at all."""
    formula = TOM.parse("∀x □∀y (Pos(G) → G(x))")
    default = isabelle_ho_modal_theory("T", (), [HoGoal("g", formula)])
    explicit = isabelle_ho_modal_theory("T", (), [HoGoal("g", formula)], mode="constant")
    assert default == explicit
    # No existsAt scaffolding at all under the default -- the individual
    # binder still renders through the SAME "mall"/"mex" a property binder
    # uses, exactly as before this port.
    assert "existsAt" not in default
    assert "mforall" not in default and "mexists" not in default
    assert "mall (\\<lambda>x::i." in default


def test_default_mode_is_unchanged_thf():
    formula = TOM.parse("∀x □∀y (Pos(G) → G(x))")
    default = to_thf_ho_modal(formula)
    explicit = to_thf_ho_modal(formula, mode="constant")
    assert default == explicit
    assert "existsat" not in default


def test_an_unknown_mode_is_refused():
    formula = TOM.parse("Pos(G)")
    with pytest.raises(ValueError, match="unknown mode"):
        isabelle_ho_modal_theory("T", (), [HoGoal("g", formula)], mode="bogus")
    with pytest.raises(ValueError, match="unknown mode"):
        to_thf_ho_modal(formula, mode="bogus")


# --------------------------------------------------------------------------- #
# 2. The judgment call: individual binders are guarded, property binders
#    never are -- structural pin, no prover needed.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("mode", ["varying", "increasing", "cumulative", "decreasing"])
def test_actualist_mode_guards_individual_quantifiers_only(mode):
    """A formula quantifying over BOTH an individual and a property: only the
    individual binder is existsAt-guarded under an actualist mode."""
    formula = TOM.parse("∀P ∀x (Ess(P, x) → □P(x))")
    theory = isabelle_ho_modal_theory("T", (), [HoGoal("g", formula)], mode=mode)
    # The individual binder x: mforall, existsAt-guarded.
    assert "mforall (\\<lambda>x::i." in theory
    # The property binder P: still mall, unguarded -- never mforall/mexists.
    assert "mall (\\<lambda>P::i \\<Rightarrow> sigma." in theory
    assert "mforall (\\<lambda>P::" not in theory
    assert 'consts existsAt :: "i \\<Rightarrow> world \\<Rightarrow> bool"' in theory

    problem = to_thf_ho_modal(formula, mode=mode)
    assert "existsat @ X_V @ W" in problem  # the individual binder is guarded
    # The property binder's THF rendering is untouched: still a bare
    # "! [P_P: ...]" with no existsat guard anywhere near it.
    assert "existsat @ P_P" not in problem


def test_constant_and_possibilist_are_synonyms_and_stay_unguarded():
    formula = TOM.parse("∀x P(x)")
    constant = isabelle_ho_modal_theory("T", (), [HoGoal("g", formula)], mode="constant")
    possibilist = isabelle_ho_modal_theory("T", (), [HoGoal("g", formula)], mode="possibilist")
    # Identical apart from the header comment's own echo of the mode name.
    assert constant.replace("constant", "possibilist", 1) == possibilist
    assert "existsAt" not in constant and "existsAt" not in possibilist
    assert "mall (\\<lambda>x::i." in constant and "mall (\\<lambda>x::i." in possibilist


def test_increasing_and_cumulative_are_synonyms():
    """``_domain_axiom_lines``/``_thf_domain_axiom_lines`` both gate on
    ``mode in ("increasing", "cumulative")`` with the SAME axiom text (see
    ``hol/ho_modal.py``), so the two modes must render identically apart from
    the header comment's own echo of the mode name -- this is the fast,
    structural pin the live Barcan/CBF battery below deliberately does not
    also cover (it exercises "increasing" only; running the same live proof
    twice under a byte-for-byte-identical axiom set would add Isabelle
    session time without checking anything new)."""
    formula = TOM.parse("∀x P(x)")
    increasing = isabelle_ho_modal_theory("T", (), [HoGoal("g", formula)], mode="increasing")
    cumulative = isabelle_ho_modal_theory("T", (), [HoGoal("g", formula)], mode="cumulative")
    assert increasing.replace("increasing", "cumulative") == cumulative
    assert "cumul_dom" in increasing and "cumul_dom" in cumulative

    increasing_thf = to_thf_ho_modal(formula, mode="increasing")
    cumulative_thf = to_thf_ho_modal(formula, mode="cumulative")
    # The THF exporter never echoes the mode name in its output at all, so
    # these are expected to be fully byte-identical, not just after a replace.
    assert increasing_thf == cumulative_thf
    assert "cumul_dom" in increasing_thf


# --------------------------------------------------------------------------- #
# 3. Faithfulness: the Barcan/converse-Barcan litmus, live, against qml_is_valid.
# --------------------------------------------------------------------------- #

_isa = pytest.mark.skipif(not isabelle_available(), reason="no Isabelle installation found")
_isa_live = pytest.mark.isabelle_live

# Hand-derived proof text for the cases where the oracle says VALID but the
# monotonicity axiom is needed explicitly (Isabelle's `blast` alone does not
# chain it automatically) -- discovered by hand while writing this test and
# confirmed live; see the module docstring's cross-reference to qml_is_valid.
_TACTIC_HINTS = {
    ("increasing", "CBF"): "using cumul_dom by blast",
    ("decreasing", "BF"): "using decr_dom by blast",
}


@_isa_live
@_isa
@pytest.mark.parametrize("mode", ["constant", "varying", "increasing", "decreasing"])
@pytest.mark.parametrize("which,text,oracle", [
    ("BF", BF_TEXT, BARCAN), ("CBF", CBF_TEXT, CONVERSE_BARCAN),
])
def test_barcan_and_converse_barcan_match_qml_is_valid_per_mode(mode, which, text, oracle):
    """The third-order embedding proves/refutes BF and CBF exactly where the
    INDEPENDENT first-order oracle (Z3-backed ``qml_is_valid``, over the
    property-free ``BARCAN``/``CONVERSE_BARCAN`` formulas of ``fol.qml``)
    says it should, for every domain regime -- hand-checked by computing the
    oracle's own verdict below and confirmed once live for every (mode,
    formula) pair while writing this test:

    constant: BF valid, CBF valid.  varying: BF invalid, CBF invalid.
    increasing: BF invalid, CBF valid.  decreasing: BF valid, CBF invalid.

    This is the textbook Barcan-formula divergence (Fitting & Mendelsohn):
    CBF needs domains non-increasing along R (so "increasing" refutes it
    only in the OTHER direction... see the table -- increasing domains
    validate CBF, decreasing validate BF), matching the FIRST-order oracle
    exactly.
    """
    expected_valid = qml_is_valid(oracle, mode=mode, frame="K")
    formula = TOM.parse(text)
    tactic = _TACTIC_HINTS.get((mode, which))
    if tactic is None:
        tactic = "by blast" if expected_valid else "nitpick [user_axioms, expect = genuine]\n  oops"
    goal = HoGoal("g", formula, proof=tactic)
    theory = isabelle_ho_modal_theory(f"Barcan_{mode}_{which}", (), [goal], mode=mode)
    result = check_theory(theory, f"Barcan_{mode}_{which}", session_timeout=240)
    assert result.ok, (
        f"{which} under mode={mode} (oracle says valid={expected_valid}) did not "
        f"discharge (exit {result.exit_code}):\n{result.output[-2000:]}"
    )


@_isa_live
@_isa
def test_the_domain_mode_judgment_call_is_pinned():
    """THE pin for this port's one new judgment call.

    Under ``mode="increasing"`` the INDIVIDUAL-level Barcan formula is
    refuted (matches ``qml_is_valid(BARCAN, mode="increasing")`` == False,
    see the parametrized test above) -- but the structurally identical
    PROPERTY-level version (◇∃P Pos(P) → ∃P ◇Pos(P)) is PROVABLE outright by
    ``blast``, with no domain axiom needed at all, because a property
    quantifier is never existsAt-guarded: it stays constant-domain in every
    mode. If a future change accidentally guarded property quantifiers too,
    this property-level goal would stop discharging by plain ``blast``
    (nitpick would find a countermodel instead, exactly like the individual
    version does), so this test would catch that regression.
    """
    individual = TOM.parse(BF_TEXT)
    property_level = TOM.parse(BF_PROPERTY_TEXT)

    refuted = HoGoal("g", individual,
                     proof="nitpick [user_axioms, expect = genuine]\n  oops")
    thy_ind = isabelle_ho_modal_theory("JudgmentInd", (), [refuted], mode="increasing")
    r_ind = check_theory(thy_ind, "JudgmentInd", session_timeout=240)
    assert r_ind.ok, f"individual BF unexpectedly not refuted:\n{r_ind.output[-2000:]}"

    proved = HoGoal("g", property_level, proof="by blast")
    thy_prop = isabelle_ho_modal_theory("JudgmentProp", (), [proved], mode="increasing")
    r_prop = check_theory(thy_prop, "JudgmentProp", session_timeout=240)
    assert r_prop.ok, f"property-level BF unexpectedly not proved:\n{r_prop.output[-2000:]}"
