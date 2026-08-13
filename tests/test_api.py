"""Tests for the seven-verb facade (unicode_fol_kit/api.py) and the
comorphism registry (unicode_fol_kit/comorphism.py).

Hand-checked contracts:

* parse_any detects each supported dialect and NEVER raises — failure comes
  back as ok=False with every attempt's error recorded;
* check accepts Node or raw text, reports the validate() defect classes, and
  signature conformance produces did-you-mean suggestions;
* prove routes by syntax, honours explicit backend lists (with the loud
  availability contract), and require_agreement fills the agreement tuple;
* repair converges exactly when the (caller-supplied) fixer fixes the defect;
* translate composes registry edges by BFS.
"""

import json

import pytest

from unicode_fol_kit import MSFLParser, api
from unicode_fol_kit.atp.protocol import BackendUnavailable
from unicode_fol_kit.comorphism import Comorphism, ComorphismRegistry

_P = MSFLParser()


# ---------------------------------------------------------------------------
# parse_any
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("text, dialect, root_type", [
    ("∀x (P(x) → Q(x))", "fol", "Quantifier"),
    ("□P → ◇P", "modal", "Implies"),
    ("∀x:Nat P(x)", "msfol", "SortedQuantifier"),
    ("![X]: (p(X) => q(X))", "tptp_bare", "Quantifier"),
    ("fof(a, axiom, ![X]: p(X)).", "tptp", "Quantifier"),
    ("all x (P(x) -> Q(x)).", "prover9", "Quantifier"),
    (r"\forall x (P(x) \rightarrow Q(x))", "latex", "Quantifier"),
    ("(declare-const p Bool) (assert p)", "smtlib", "Atom"),
])
def test_parse_any_detects_dialects(text, dialect, root_type):
    r = api.parse_any(text)
    assert r.ok and r.dialect == dialect
    assert type(r.formula).__name__ == root_type


def test_parse_any_smtlib_folds_assertions_conjunctively():
    r = api.parse_any("(declare-const p Bool) (declare-const q Bool) "
                      "(assert p) (assert q)")
    assert r.ok and r.formula.to_unicode_str() == "p ∧ q"


def test_parse_any_never_raises_and_records_attempts():
    r = api.parse_any("∀x (P(x) →")                # truncated: no mode parses it
    assert not r.ok and r.formula is None
    assert len(r.errors) >= 1
    assert all("dialect" in e and "message" in e for e in r.errors)
    json.dumps(r.to_dict())                        # JSON-able including errors


def test_parse_any_hint_pins_the_dialect():
    """⊕ means Xor in fol but StrongDisjunction under the fl hint."""
    assert type(api.parse_any("P(x) ⊕ Q(x)", hint="fol").formula).__name__ == "Xor"
    assert (type(api.parse_any("P(x) ⊕ Q(x)", hint="fl").formula).__name__
            == "StrongDisjunction")


def test_parse_any_unknown_hint_raises():
    with pytest.raises(ValueError, match="unknown hint"):
        api.parse_any("P(a)", hint="klingon")


def test_parse_any_multi_formula_tptp_is_refused():
    r = api.parse_any("fof(a, axiom, p). fof(b, axiom, q).")
    assert not r.ok
    assert any("2 annotated formulas" in e["message"] for e in r.errors)


# ---------------------------------------------------------------------------
# check
# ---------------------------------------------------------------------------

def test_check_flags_free_variables_on_text_input():
    r = api.check("∀x (P(x) → Q(y))")
    assert r.parseable and not r.ok
    assert r.free_variables == ("y",)


def test_check_flags_arity_conflict_with_namespace():
    r = api.check("P(a) ∧ P(a, b)")
    assert not r.ok and not r.arity_consistent
    assert r.arity_conflicts[0] == {"namespace": "pred", "symbol": "P",
                                    "arities": [1, 2]}


def test_check_unparseable_text_reports_instead_of_raising():
    r = api.check("∀x (P(x) →")
    assert not r.ok and not r.parseable and r.error


def test_check_signature_wrong_arity_and_suggestion():
    node = _P.parse("Humann(a) ∧ Mortal(a, b)")
    r = api.check(node, signature={"predicates": {"Human": 1, "Mortal": 1},
                                   "constants": ["a", "b"]})
    assert not r.ok
    kinds = {e["kind"] for e in r.signature_errors}
    assert kinds == {"unknown_predicate", "wrong_arity"}
    unknown = next(e for e in r.signature_errors if e["kind"] == "unknown_predicate")
    assert unknown["symbol"] == "Humann" and unknown["suggestion"] == "Human"


def test_check_passes_a_clean_sentence():
    r = api.check("∀x (Human(x) → Mortal(x))",
                  signature={"predicates": {"Human": 1, "Mortal": 1}})
    assert r.ok and bool(r)
    json.dumps(r.to_dict())


# ---------------------------------------------------------------------------
# prove / countermodel
# ---------------------------------------------------------------------------

def test_prove_routes_fol_and_modal_automatically():
    fol = _P.parse("∀x (P(x) → Q(x)) ∧ P(a) → Q(a)")
    assert api.prove(fol).status == "proved"
    modal = MSFLParser(modal=True).parse("□(P → Q) → (□P → □Q)")   # K axiom
    v = api.prove(modal)
    assert v.status == "proved" and v.logic == "modal"


def test_prove_with_premises():
    premises = [_P.parse("∀x (P(x) → Q(x))"), _P.parse("P(a)")]
    assert api.prove(_P.parse("Q(a)"), premises).status == "proved"


def test_prove_require_agreement_fills_agreement_tuple():
    f = _P.parse("P(a) → P(a)")
    v = api.prove(f, backends=["z3", "tableau", "resolution"],
                  require_agreement=2)
    assert v.status == "proved"
    assert len(v.agreement) == 2 and v.agreement[0] != v.agreement[1]


def test_prove_rejects_backend_logic_mismatch():
    modal = MSFLParser(modal=True).parse("□P → P")
    with pytest.raises(ValueError, match="does not support logic"):
        api.prove(modal, backends=["z3"])


def test_prove_unavailable_explicit_backend_raises():
    """An explicitly requested missing backend must raise, never skip."""
    from unicode_fol_kit.atp.protocol import _REGISTRY, ProverBackend

    class Ghost(ProverBackend):
        name = "ghost"
        logics = frozenset({"fol"})
        external = True

        def available(self):
            return False

        def decide(self, formula, premises=(), timeout=10000, **options):
            raise AssertionError("unreachable")

    _REGISTRY["ghost"] = Ghost()
    try:
        with pytest.raises(BackendUnavailable):
            api.prove(_P.parse("P(a)"), backends=["ghost"])
    finally:
        del _REGISTRY["ghost"]


def test_prove_chain_summarises_when_nothing_definitive():
    """Ⓕ ∀x P(x) → ∀x P(x) is INVALID (same shape as Ⓕ P → P) but outside
    every default modal backend's definitive reach: the tableau has no F rule
    (unsupported), kripke-enum cannot handle the object quantifier — no
    per-world domains in its enumeration — and reports unsupported too, and
    the sound-incomplete qml route cannot refute. The chain verdict must
    summarise per-backend.

    (Deliberately NOT the propositional ``Ⓕ P → P``: kripke-enum REFUTES
    that now — that upgrade is pinned by test_cli's prove test and
    test_t1_integration. And not ``Ⓖ P → P``: G is reflexive here, so qml
    PROVES that.)
    """
    modal = MSFLParser(modal=True).parse("Ⓕ ∀x P(x) → ∀x P(x)")
    v = api.prove(modal)
    assert v.status == "unknown" and v.backend == "chain"
    assert "modal-tableau:unknown/unsupported" in v.detail
    assert "kripke-enum:unknown/unsupported" in v.detail
    assert "qml:unknown/incomplete" in v.detail


def test_countermodel_fol_prefers_finite_structure():
    cm = api.countermodel(_P.parse("∀x P(x)"))
    assert cm.found and cm.backend == "modelfinder"
    assert cm.model["kind"] == "finite_structure"
    assert "structure" in cm.explanation_nl
    json.dumps(cm.to_dict())


def test_countermodel_modal_yields_kripke_witness():
    cm = api.countermodel(MSFLParser(modal=True).parse("□P → P"))
    assert cm.found and cm.model["kind"] == "kripke"


def test_countermodel_absence_is_not_a_validity_claim():
    cm = api.countermodel(_P.parse("P(a) → P(a)"))
    assert not cm.found and cm.model is None


# ---------------------------------------------------------------------------
# repair
# ---------------------------------------------------------------------------

def test_repair_without_fixer_yields_one_diagnostic_step():
    steps = list(api.repair("∀x (P(x) → Q(y))"))
    assert len(steps) == 1 and not steps[0].converged
    assert "y" in steps[0].suggestion
    json.dumps(steps[0].to_dict())


def test_repair_with_fixer_converges():
    def fixer(text, diagnostics):
        assert diagnostics["check"] is not None    # parse succeeded, check failed
        return text.replace("Q(y)", "Q(x)")

    steps = list(api.repair("∀x (P(x) → Q(y))", fixer=fixer))
    assert [s.converged for s in steps] == [False, True]
    assert steps[1].ok


def test_repair_fixes_syntax_then_signature():
    """Two-defect run: broken syntax first, then a signature typo.

    (``alice``, not ``a`` — single lowercase letters are VARIABLES in the
    grammar, so ``Human(a)`` would additionally be an open formula.)
    """
    fixes = iter(["Humann(alice)", "Human(alice)"])

    def fixer(text, diagnostics):
        return next(fixes)

    steps = list(api.repair("Humann(alice", fixer=fixer,
                            signature={"predicates": {"Human": 1}}))
    assert [s.converged for s in steps] == [False, False, True]
    assert "syntax" in steps[0].suggestion.lower()
    assert "did you mean" in steps[1].suggestion.lower()


def test_repair_stops_at_max_attempts():
    steps = list(api.repair("P(x", fixer=lambda t, d: t, max_attempts=3))
    assert len(steps) == 3 and not any(s.converged for s in steps)


def test_repair_suggestion_comes_from_the_dialect_that_read_furthest():
    """'A ∧ B ∨ C' is a mixed-connective failure, and the suggestion has to
    say so.

    ``parse_any`` reports one error per candidate dialect in detection order,
    and the specialised dialects at the END of that order are the ones that
    give up EARLIEST on ordinary input: here the final entry is a lambek/
    linear complaint about the predicate 'A' at position 3, while the seven
    dialects that read as far as the ∨ name the real cause. Handing back the
    last entry — which is what the suggestion used to do — tells the reader
    to rename a predicate that is already well formed, and renaming it fails
    in exactly the same place.
    """
    step = next(api.repair("A ∧ B ∨ C"))
    assert not step.converged
    assert "Cannot mix" in step.suggestion
    assert "Invalid predicate" not in step.suggestion

    # The mechanism, pinned directly: "ended unexpectedly" means the dialect
    # consumed the whole input, which beats any positional failure.
    assert (api._message_progress("SYNTAX_ERROR: Incomplete formula - the "
                                  "input ended unexpectedly. Expected: x")
            > api._message_progress("boom at position 99"))
    assert (api._message_progress("boom at position 7")
            > api._message_progress("boom at position 3"))
    assert api._message_progress("no position at all") == 0


# ---------------------------------------------------------------------------
# translate / comorphism registry
# ---------------------------------------------------------------------------

def test_translate_modal_to_fol_standard_translation():
    modal = MSFLParser(modal=True).parse("□P")
    t = api.translate(modal, "modal", "fol")
    assert t.path == ("standard_translation",)
    assert t.result.to_unicode_str() == "∀w0 (R(w, w0) → P(w0))"
    assert not t.lossy and "free" in t.note.lower() or "FREE" in t.note


def test_translate_alc_reaches_fol_directly():
    from unicode_fol_kit.dl import parse_concept
    concept = parse_concept("A ⊓ ∃r.B")
    t = api.translate(concept, "alc", "fol")
    assert t.path == ("concept_to_fol",)


def test_registry_bfs_composes_edges():
    """a→b→c composes when no direct a→c edge exists."""
    reg = ComorphismRegistry()
    reg.register(Comorphism("double", "a", "b", lambda x: x * 2))
    reg.register(Comorphism("succ", "b", "c", lambda x: x + 1))
    t = reg.translate(5, "a", "c")
    assert t.result == 11 and t.path == ("double", "succ")


def test_registry_refuses_silent_edge_overwrite_and_unknown_path():
    reg = ComorphismRegistry()
    reg.register(Comorphism("e1", "a", "b", lambda x: x))
    with pytest.raises(ValueError, match="already registered"):
        reg.register(Comorphism("e2", "a", "b", lambda x: x))
    with pytest.raises(ValueError, match="no comorphism path"):
        reg.find_path("b", "a")
    with pytest.raises(ValueError, match="unknown logic label"):
        reg.find_path("a", "zz")
