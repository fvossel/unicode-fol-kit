"""Tests for the nanoCoP-M backend (atp.nanocop_backend).

No Prolog runs here: the translator goldens are hand-derived against the
shipped ReadMe's documented syntax (v2.0, quoted in the module docstring),
and the decide() tests stub the runner with the wrapper script's REAL
output/exit-code contract (``… is a modal (s4/cumul) Theorem`` etc., read
from nanocopm.sh). The mandatory cross-check policy is the heart of the
suite: nanoCoP-M is opt-in ONLY under it.
"""

import pytest

from unicode_fol_kit import MSFLParser
from unicode_fol_kit.atp import nanocop_backend as nb
from unicode_fol_kit.atp.nanocop_backend import NanocopBackend, to_nanocop
from unicode_fol_kit.atp.protocol import (
    BackendUnavailable,
    default_chain,
    get_backend,
)

_PARSE = MSFLParser(modal=True).parse


# ---------------------------------------------------------------------------
# Translator (goldens hand-derived from the ReadMe syntax)
# ---------------------------------------------------------------------------

def test_readme_example_shape():
    """The ReadMe's own example is (□∀x P(x)) → ∀x ◇P(x); the kit
    translation must produce the same operator spelling: '#' box, '*'
    diamond, 'all X:' — hand-derived with the kit's full parenthesising."""
    formula = _PARSE("□(∀x P(x)) → ∀x ◇P(x)")
    assert to_nanocop(formula) == (
        "f( ((# (all X: p(X))) => (all X: (* p(X)))) ).\n")


def test_premises_fold_into_implication():
    """nanoCoP-M takes ONE validity question: premises ⊨ φ becomes
    (∧ premises) => φ. Hand-derived for □P, □(P→Q) ⊨ □Q."""
    premises = [_PARSE("□P"), _PARSE("□(P → Q)")]
    goal = _PARSE("□Q")
    assert to_nanocop(goal, premises) == (
        "f( (((# p) , (# (p => q))) => (# q)) ).\n")


def test_connective_spelling():
    """Conjunction ',', disjunction ';', negation '~', equivalence '<=>' —
    exactly the ReadMe's operator table. Hand-derived: every compound gets
    one paren pair, so (P∧Q)∨¬(P↔Q) is ((p , q) ; (~ (p <=> q)))."""
    assert to_nanocop(_PARSE("(P ∧ Q) ∨ ¬(P ↔ Q)")) == (
        "f( ((p , q) ; (~ (p <=> q))) ).\n")


def test_name_collision_refused():
    """Kit predicates 'P' and 'p'... the kit's grammar cannot even parse a
    lowercase predicate, but direct AST construction can: both would render
    as Prolog 'p' — refuse, never alias (NXF discipline)."""
    from unicode_fol_kit.fol.nodes import And as _And, Atom as _Atom

    clash = _And(_Atom("Px", ()), _Atom("px", ()))
    with pytest.raises(NotImplementedError, match="refusing to alias"):
        to_nanocop(clash)


def test_equality_and_free_variables_refused():
    from unicode_fol_kit.fol.nodes import Atom as _Atom, Variable as _Var

    with pytest.raises(NotImplementedError, match="equality"):
        to_nanocop(_PARSE("□(x1 = x1)") if False else _Atom("=", (_Var("x"), _Var("x"))))
    with pytest.raises(ValueError, match="free variable"):
        to_nanocop(_Atom("P", (_Var("x"),)))


def test_out_of_fragment_operator_refused():
    knows = MSFLParser(modal=True).parse("K_anne P")
    with pytest.raises(NotImplementedError, match="outside the supported"):
        to_nanocop(knows)


# ---------------------------------------------------------------------------
# Registry / availability
# ---------------------------------------------------------------------------

def test_registered_opt_in_never_default():
    backend = get_backend("nanocop")
    assert isinstance(backend, NanocopBackend)
    assert backend.external is True
    assert "nanocop" not in default_chain("modal")
    assert "nanocop" not in default_chain("fol")


def test_unavailable_raises_with_instructions(monkeypatch):
    monkeypatch.setattr(nb, "_discover", lambda: None)
    with pytest.raises(BackendUnavailable, match="UFK_NANOCOP_CMD"):
        get_backend("nanocop").decide(_PARSE("□P → P"))


# ---------------------------------------------------------------------------
# decide(): the wrapper-script output contract + the mandatory cross-check
# ---------------------------------------------------------------------------

_THEOREM_OUT = "problem.ncp is a modal (t/cumul) Theorem\n"
_NONTHEOREM_OUT = "problem.ncp is a modal (t/cumul) Non-Theorem\n"


@pytest.fixture()
def stubbed(monkeypatch):
    monkeypatch.setattr(nb, "_discover", lambda: ("nanocopm.sh", False))
    holder = {"response": (_THEOREM_OUT, 0)}
    monkeypatch.setattr(nb, "_run_nanocop",
                        lambda problem, cmd, wsl, t: holder["response"])
    return holder


def test_theorem_cross_checked_and_confirmed(stubbed):
    """□P → P is T-valid: nanoCoP says Theorem (t/cumul) and the REAL
    modal-tableau cross-check on frame T confirms — PROVED with both
    provenances in detail."""
    verdict = get_backend("nanocop").decide(_PARSE("□P → P"))
    assert verdict.status == "proved"
    assert "nanoCoP-M (t/cumul)" in verdict.detail
    assert "cross-check modal-tableau: confirmed" in verdict.detail


def test_theorem_contradicted_by_tableau_is_a_soundness_alarm(stubbed):
    """□P → P is NOT K-valid… but here we force the disagreement directly:
    the stub claims Theorem for ◇P → □P (t/cumul), which the real tableau
    on frame T REFUTES — the backend must alarm, not answer."""
    verdict = get_backend("nanocop").decide(_PARSE("◇P → □P"))
    assert verdict.status == "error"
    assert "SOUNDNESS ALARM" in verdict.detail


def test_nontheorem_with_countermodel_is_refuted(stubbed):
    """◇P → □P is T-invalid: nanoCoP claims Non-Theorem and the real
    kripke-enum finds the 2-world countermodel — REFUTED, countermodel
    attached as the certificate."""
    stubbed["response"] = (_NONTHEOREM_OUT, 1)
    verdict = get_backend("nanocop").decide(_PARSE("◇P → □P"))
    assert verdict.status == "refuted"
    assert verdict.countermodel is not None
    assert "kripke-enum countermodel confirms" in verdict.detail


def test_nontheorem_without_countermodel_stays_unknown(stubbed, monkeypatch):
    """A Non-Theorem claim the enumerator cannot certify is recorded but
    NOT vouched for: UNKNOWN/incomplete (FO modal validity is undecidable —
    the module's asymmetric trust policy)."""
    stubbed["response"] = (_NONTHEOREM_OUT, 1)
    monkeypatch.setattr(NanocopBackend, "_cross_check",
                        staticmethod(lambda *a, **kw: None))
    verdict = get_backend("nanocop").decide(_PARSE("◇P → □P"))
    assert verdict.status == "unknown"
    assert verdict.reason == "incomplete"
    assert "not vouched for" in verdict.detail


def test_logic_mismatch_is_an_error(stubbed):
    """The script REPORTS what configuration ran; a caller who requested
    s5 but whose script is configured t/cumul gets an ERROR telling them to
    reconfigure — never an answer from the wrong logic."""
    verdict = get_backend("nanocop").decide(_PARSE("□P → P"), logic="s5")
    assert verdict.status == "error"
    assert "edit LOGIC in your nanocopm.sh" in verdict.detail


def test_timeout_contract(stubbed):
    stubbed["response"] = ("Timeout\n", 2)
    verdict = get_backend("nanocop").decide(_PARSE("□P → P"))
    assert verdict.status == "unknown"
    assert verdict.reason == "timeout"


def test_garbage_output_is_infra_error(stubbed):
    stubbed["response"] = ("eclipse: command not found\n", 0)
    verdict = get_backend("nanocop").decide(_PARSE("□P → P"))
    assert verdict.status == "error"
    assert verdict.reason == "infra"
