# -*- coding: utf-8 -*-
"""Central-integration tests for the Tier-1 wave: registry, chains, witnesses.

Every expectation here is hand-checked:

- ``Ⓕ P → P`` is INVALID: in the two-world model ``0 →(temporal) 1`` with
  ``P`` true only at world 1, ``Ⓕ P`` holds at 0 (world 1 is reachable) but
  ``P`` does not — so the implication fails at 0. No route in the kit could
  refute this before ``kripke-enum`` joined the default modal chain (the
  tableau has no temporal rule, qml is proof-only).
- ``◇P → □P`` is INVALID in K: a world seeing one P-world and one ¬P-world
  falsifies it — the tableau finds that model, and its witness now carries the
  structured ``data`` payload alongside ``repr``.
- The rebuilt witness models are re-checked with ``satisfies_modal`` — the
  SAME evaluator every Kripke-based route answers to — so a wrong
  ``kripke_model_from_dict`` cannot pass these tests.
"""

import importlib.util
import shutil
import subprocess

import pytest

import unicode_fol_kit as u
from unicode_fol_kit import api
from unicode_fol_kit.atp.protocol import get_backend
from unicode_fol_kit.semantics.kripke import KripkeModel, satisfies_modal

_HAS_CVC5 = importlib.util.find_spec("cvc5") is not None


# --------------------------------------------------------------------------- #
# Registry + default chains
# --------------------------------------------------------------------------- #

def test_new_backends_are_registered():
    """cvc5 / kripke-enum / leo3 are addressable by name after a plain import."""
    assert get_backend("cvc5").name == "cvc5"
    assert get_backend("kripke-enum").name == "kripke-enum"
    assert get_backend("leo3").name == "leo3"


def test_default_modal_chain_gained_kripke_enum():
    assert u.default_chain("modal") == ("modal-tableau", "kripke-enum", "qml")


def test_default_fol_chain_adapts_to_the_cvc5_extra():
    """cvc5 sits right after z3 iff the optional extra is installed.

    Both branches are asserted so the test is meaningful on machines with AND
    without the extra (CI installs only ``[test]``, the dev venv has cvc5).
    """
    chain = u.default_chain("fol")
    if _HAS_CVC5:
        assert chain == ("z3", "cvc5", "tableau", "resolution", "modelfinder")
    else:
        assert chain == ("z3", "tableau", "resolution", "modelfinder")


def test_top_level_exports_for_the_tier1_wave():
    for name in ("portfolio_prove", "Cvc5Backend", "KripkeEnumBackend",
                 "Leo3Backend", "EnumSearchResult", "modal_enum_search",
                 "modal_enum_countermodel", "kripke_model_to_dict",
                 "kripke_model_from_dict", "to_tptp_ncl",
                 "extract_szs_status", "szs_to_verdict_fields",
                 "TstpStep", "TstpDerivation", "parse_tstp_derivation",
                 "check_entailment_vampire_detailed",
                 "explain_countermodel", "batch_decide"):
        assert hasattr(u, name), f"unicode_fol_kit.{name} missing"
        assert name in u.__all__, f"{name} not in __all__"
    # The datasets subpackage rides in via eval.
    from unicode_fol_kit.eval import datasets
    assert hasattr(datasets, "load_folio") and hasattr(datasets, "load_malls")


# --------------------------------------------------------------------------- #
# The temporal-refutation gap is closed IN THE DEFAULT CHAIN
# --------------------------------------------------------------------------- #

def _modal(text: str):
    return u.MSFLParser(modal=True).parse(text)


def test_prove_refutes_invalid_temporal_formula_via_default_chain():
    """Ⓕ P → P: previously permanently 'unknown', now REFUTED by kripke-enum."""
    verdict = api.prove(_modal("Ⓕ P → P"))
    assert verdict.status == "refuted"
    assert verdict.backend == "kripke-enum"
    assert verdict.szs_status == "CounterSatisfiable"
    # The witness model itself falsifies the formula under the shared evaluator.
    model = u.kripke_model_from_dict(verdict.countermodel["data"])
    assert satisfies_modal(_modal("Ⓕ P → P"), model, 0) is False


def test_prove_still_proves_valid_temporal_formula_via_qml():
    """Ⓖ P → P is valid (the kit's Ⓖ includes 'now'): kripke-enum exhausts
    its bound without a countermodel and qml closes the proof."""
    verdict = api.prove(_modal("Ⓖ P → P"))
    assert verdict.status == "proved"
    assert verdict.backend == "qml"


def test_countermodel_default_modal_chain_reaches_kripke_enum():
    result = api.countermodel(_modal("Ⓕ P → P"))
    assert result.found
    assert result.backend == "kripke-enum"
    assert result.model["kind"] == "kripke"
    assert isinstance(result.model["data"], dict)


# --------------------------------------------------------------------------- #
# Structured Kripke witnesses + the explain wiring
# --------------------------------------------------------------------------- #

def test_modal_tableau_witness_carries_verified_structured_data():
    """◇P → □P: the tableau's witness data rebuilds into a model that the
    shared evaluator confirms falsifies the goal at world 0."""
    goal = _modal("◇P → □P")
    result = api.countermodel(goal)
    assert result.found and result.backend == "modal-tableau"
    data = result.model["data"]
    model = u.kripke_model_from_dict(data)
    assert satisfies_modal(goal, model, 0) is False


def test_countermodel_explanation_narrates_the_kripke_model():
    """The explanation is the world-by-world rendering, not the one-line gloss."""
    result = api.countermodel(_modal("Ⓕ P → P"))
    assert "world" in result.explanation_nl
    assert "temporal" in result.explanation_nl
    assert result.explanation_nl.endswith("At world 0 the formula fails.")


def test_countermodel_explanation_with_premises_uses_the_folded_goal():
    """premises ⊨ φ: the world-0 check must evaluate (∧premises) → φ.

    □P ⊨ P is invalid in K (no reflexivity): a countermodel makes □P true and
    P false at world 0 — so the folded implication fails there, and the
    explanation still ends with the honest world-0 sentence.
    """
    result = api.countermodel(_modal("P"), [_modal("□P")])
    assert result.found
    model = u.kripke_model_from_dict(result.model["data"])
    folded = _modal("□P → P")
    assert satisfies_modal(folded, model, 0) is False
    assert result.explanation_nl.endswith("At world 0 the formula fails.")


def test_countermodel_explanation_for_z3_witness():
    """A z3_model witness routes through explain's assignment branch."""
    goal = u.MSFLParser().parse("Mortal(socrates)")
    result = api.countermodel(goal, backends=["z3"])
    assert result.found and result.backend == "z3"
    assert isinstance(result.explanation_nl, str) and result.explanation_nl


# --------------------------------------------------------------------------- #
# kripke_model_to_dict / kripke_model_from_dict round trip
# --------------------------------------------------------------------------- #

def test_kripke_dict_roundtrip_plain():
    m = KripkeModel({0, 1}, {"alethic": {(0, 1), (1, 1)}}, {0: {"P"}, 1: {"P", "Q"}})
    d = u.kripke_model_to_dict(m)
    assert "nominals" not in d and "domains" not in d
    m2 = u.kripke_model_from_dict(d)
    assert m2.worlds == m.worlds
    assert m2.relations == m.relations
    assert m2.valuation == m.valuation
    assert u.kripke_model_to_dict(m2) == d


def test_kripke_dict_roundtrip_with_nominals_and_domains():
    """Hybrid nominals and per-world domains survive the round trip — they are
    exactly what the old repr-only witness silently dropped."""
    m = KripkeModel({0, 1}, {"alethic": {(0, 1)}}, {1: {"P"}},
                    domains={0: {"a"}, 1: {"a", "b"}}, nominals={"i": 1})
    d = u.kripke_model_to_dict(m)
    assert d["nominals"] == {"i": 1}
    assert d["domains"] == {"0": ["a"], "1": ["a", "b"]}
    m2 = u.kripke_model_from_dict(d)
    assert m2.nominals == {"i": 1}
    assert m2.domains == m.domains
    assert u.kripke_model_to_dict(m2) == d


# --------------------------------------------------------------------------- #
# cvc5 in the chain
# --------------------------------------------------------------------------- #

@pytest.mark.skipif(not _HAS_CVC5, reason="cvc5 extra not installed")
def test_cvc5_backend_proves_via_api():
    verdict = api.prove(u.MSFLParser().parse("∀x (P(x) ∨ ¬P(x))"),
                        backends=["cvc5"])
    assert verdict.status == "proved" and verdict.backend == "cvc5"


@pytest.mark.skipif(not _HAS_CVC5, reason="cvc5 extra not installed")
def test_cvc5_agrees_with_z3_under_require_agreement():
    """require_agreement=2 collects z3 AND cvc5 on the same proved verdict."""
    verdict = api.prove(u.MSFLParser().parse("P(alice) → P(alice)"),
                        backends=["z3", "cvc5"], require_agreement=2)
    assert verdict.status == "proved"
    assert set(verdict.agreement) == {"z3", "cvc5"}


# --------------------------------------------------------------------------- #
# VampireBackend: the SZS/TSTP detailed route (live, gated)
# --------------------------------------------------------------------------- #

def _wsl_vampire_ok() -> bool:
    if shutil.which("wsl") is None:
        return False
    try:
        proc = subprocess.run(["wsl", "vampire", "--version"],
                              capture_output=True, timeout=20)
    except (OSError, subprocess.TimeoutExpired):
        return False
    return proc.returncode == 0 or b"Vampire" in proc.stdout + proc.stderr


_NATIVE_VAMPIRE = shutil.which("vampire")
_WSL_VAMPIRE = _NATIVE_VAMPIRE is None and _wsl_vampire_ok()


def _vampire_decide(formula, premises=()):
    backend = get_backend("vampire")
    if _NATIVE_VAMPIRE:
        return backend.decide(formula, premises, timeout=30000,
                              vampire_path=_NATIVE_VAMPIRE, use_wsl=False)
    return backend.decide(formula, premises, timeout=30000,
                          vampire_path="vampire", use_wsl=True)


@pytest.mark.skipif(not (_NATIVE_VAMPIRE or _WSL_VAMPIRE),
                    reason="no Vampire binary (native or WSL)")
def test_vampire_backend_proved_carries_szs_and_tstp_proof():
    """Modus ponens: SZS Theorem verbatim + a parsed TSTP derivation DAG."""
    p = u.MSFLParser()
    verdict = _vampire_decide(
        p.parse("Mortal(socrates)"),
        [p.parse("∀x (Human(x) → Mortal(x))"), p.parse("Human(socrates)")])
    assert verdict.status == "proved"
    assert verdict.szs_status == "Theorem"
    assert verdict.proof is not None and verdict.proof["steps"]


@pytest.mark.skipif(not (_NATIVE_VAMPIRE or _WSL_VAMPIRE),
                    reason="no Vampire binary (native or WSL)")
def test_vampire_backend_refutes_countersatisfiable():
    """P(a) ⊭ Q(a): Vampire's CounterSatisfiable is an honest REFUTED now,
    where the old substring route collapsed it into 'unknown'."""
    p = u.MSFLParser()
    verdict = _vampire_decide(p.parse("Q(alice)"), [p.parse("P(alice)")])
    assert verdict.status == "refuted"
    assert verdict.szs_status == "CounterSatisfiable"
