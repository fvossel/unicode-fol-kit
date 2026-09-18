"""Tests for the C11/C12 premise-relevance layer, across all its routes.

The per-route algorithms (z3_relevant_premises, the TSTP ancestor walk,
Z3Backend's/Cvc5Backend's unsat-core proof certificates) each have their own
hand-checked unit tests in tests/test_protocol.py, tests/test_cvc5_backend.py
and tests/test_tstp.py. This file is the INTEGRATION layer: the shared
ONE-Z3-assert_and_track-mechanism claim (C11+C12 overlap), api.prove's
relevant_premises= wiring, the absent Vampire route, and a
differential cross-check between the Z3-native and E-derivation-based legs on
the same textbook problem.
"""

import pytest

from unicode_fol_kit import MSFLParser, api
from unicode_fol_kit.atp.eprover_backend import eprover_available, eprover_relevant_premises
from unicode_fol_kit.atp.protocol import PROVED, Z3Backend, z3_relevant_premises

_P = MSFLParser()

# Bird(tweety) shares no symbol with the modus-ponens derivation of
# Mortal(socrates) -- a textbook red herring, independently hand-verified via
# a direct z3.Solver().assert_and_track() experiment (see
# tests/test_protocol.py's TestZ3RelevantPremises docstring) before being
# pinned here too.
_PREMISES = [_P.parse("∀x (Human(x) → Mortal(x))"),
            _P.parse("Human(socrates)"),
            _P.parse("Bird(tweety)")]
_GOAL = _P.parse("Mortal(socrates)")


# ---------------------------------------------------------------------------
# Verdict field: additive, default None, present in to_dict()
# ---------------------------------------------------------------------------

def test_verdict_relevant_premises_defaults_to_none_and_serialises():
    from unicode_fol_kit import Verdict
    v = Verdict("proved", "z3")
    assert v.relevant_premises is None
    d = v.to_dict()
    assert "relevant_premises" in d and d["relevant_premises"] is None

    v2 = Verdict("proved", "z3", relevant_premises=(0, 2))
    assert v2.to_dict()["relevant_premises"] == [0, 2]


# ---------------------------------------------------------------------------
# One Z3 assert_and_track mechanism serving BOTH C11 and C12 (never
# z3.set_param(proof=True) -- a per-Solver()-instance check).
# ---------------------------------------------------------------------------

def test_z3_backend_and_z3_relevant_premises_share_one_mechanism_not_global_state():
    """z3.set_param(proof=True) would be a PROCESS-WIDE global -- if either
    C11's z3_relevant_premises or C12's Z3Backend touched it (or otherwise
    forced unsat-core tracking on globally), a brand-new, completely vanilla
    z3.Solver() built AFTER either call would start reporting a non-empty
    unsat_core() for PLAIN (non-assert_and_track) contradictory assertions,
    which is NOT today's baseline Z3 behaviour (verified directly below,
    before touching this module at all)."""
    import z3

    def baseline_core_on_untracked_assertions():
        s = z3.Solver()
        s.add(z3.Bool("x"))
        s.add(z3.Not(z3.Bool("x")))
        s.check()
        return list(s.unsat_core())

    before = baseline_core_on_untracked_assertions()
    assert before == []      # today's baseline: no tracking, no core reported

    z3_relevant_premises(_GOAL, _PREMISES)
    Z3Backend().decide(_GOAL, _PREMISES)

    after = baseline_core_on_untracked_assertions()
    assert after == []       # unchanged -- neither call left any global trace


def test_z3backend_proof_core_and_z3_relevant_premises_are_literally_the_same_query():
    """Both read _z3_track_and_check -- their premise-side answers must be
    identical for the same (formula, premises), not just "similar"."""
    v = Z3Backend().decide(_GOAL, _PREMISES)
    assert v.status == PROVED
    from_proof = tuple(sorted(int(tag[1:]) for tag in v.proof["core"] if tag != "goal"))
    from_relevant = z3_relevant_premises(_GOAL, _PREMISES)
    assert from_proof == from_relevant == (0, 1)


# ---------------------------------------------------------------------------
# api.prove(relevant_premises=...)
# ---------------------------------------------------------------------------

def test_prove_default_does_not_compute_relevant_premises():
    v = api.prove(_GOAL, _PREMISES)
    assert v.status == "proved"
    assert v.relevant_premises is None


def test_prove_relevant_premises_true_fills_it_for_the_winning_z3_backend():
    v = api.prove(_GOAL, _PREMISES, relevant_premises=True)
    assert v.backend == "z3"          # z3 heads default_chain("fol")
    assert v.relevant_premises == (0, 1)


def test_prove_relevant_premises_only_applies_on_a_proved_verdict():
    """A REFUTED verdict has no 'premises used' question to answer -- the
    field must stay None, not raise or fabricate anything."""
    v = api.prove(_P.parse("Q(a)"), [_P.parse("P(a)")],
                  backends=["z3"], relevant_premises=True)
    assert v.status == "refuted"
    assert v.relevant_premises is None


def test_prove_relevant_premises_unsupported_winning_backend_stays_none():
    """The tableau backend has no premise-relevance route wired in
    api._relevant_premises_for -- the flag must not raise for it, it just
    does not fill the field (refuse, don't guess)."""
    v = api.prove(_GOAL, _PREMISES, backends=["tableau"], relevant_premises=True)
    assert v.status == "proved"
    assert v.relevant_premises is None


# ---------------------------------------------------------------------------
# Vampire: no route -- its derivations rename the premises.
# ---------------------------------------------------------------------------

def test_api_prove_has_no_vampire_relevance_route():
    """api._relevant_premises_for has no "vampire" entry: Vampire renames
    every statement to f1/f2/..., so its leaves cannot be mapped back to the
    caller's premises (pinned offline in tests/test_tstp.py). Checked
    directly rather than through a live Vampire run."""
    from unicode_fol_kit.api import _relevant_premises_for
    assert _relevant_premises_for("vampire", _GOAL, _PREMISES, 10000) is None


# ---------------------------------------------------------------------------
# Live: the E-derivation leg, gated exactly like test_eprover_zipperposition.py
# gates its own live tests (skip, never fake a pass, when eprover is absent
# or the packaged binary aborts on startup).
# ---------------------------------------------------------------------------

_CRASH_MARKERS = ("Assertion", "assertion failed", "Segmentation fault",
                  "core dumped", "Aborted")


def _skip_if_the_binary_crashed(premises, goal) -> None:
    """Skip when the eprover build aborts on startup (see
    tests/test_eprover_zipperposition.py's helper of the same name): a crashed
    binary says nothing about this route. A binary that runs is asserted
    against, so a relevance walk that wrongly returns None fails."""
    from unicode_fol_kit.atp.eprover_backend import check_entailment_eprover_detailed
    result = check_entailment_eprover_detailed(premises, goal, timeout=15)
    if result["status"] == "error" and any(
            m in (result.get("raw") or "") for m in _CRASH_MARKERS):
        pytest.skip("the eprover binary aborted")


def _entails(premises, goal) -> bool:
    import z3
    solver = z3.Solver()
    for p in premises:
        solver.add(p.to_z3())
    solver.add(z3.Not(goal.to_z3()))
    return solver.check() == z3.unsat


@pytest.mark.skipif(not eprover_available(), reason="no eprover binary found")
class TestEproverRelevantPremisesLive:
    def test_red_herring_excluded_live(self):
        _skip_if_the_binary_crashed(_PREMISES, _GOAL)
        assert eprover_relevant_premises(_PREMISES, _GOAL, timeout=15) == (0, 1)

    def test_non_theorem_is_none(self):
        assert eprover_relevant_premises([_P.parse("Human(socrates)")],
                                         _GOAL, timeout=15) is None

    def test_agrees_with_z3_on_the_same_textbook_fixture(self):
        """The Z3-native and E-derivation legs need not always agree (different
        calculi can use different sufficient subsets), but here the sufficient
        subset is unique: dropping either of the first two premises breaks the
        derivation, and the third shares no symbol with anything."""
        _skip_if_the_binary_crashed(_PREMISES, _GOAL)
        z3_indices = z3_relevant_premises(_GOAL, _PREMISES)
        e_indices = eprover_relevant_premises(_PREMISES, _GOAL, timeout=15)
        assert z3_indices == e_indices == (0, 1)

    def test_redundant_premises_report_one_sufficient_subset_live(self):
        """Each premise alone entails the goal, so E may use either one. What
        must hold is that the reported subset is non-empty and still entails
        the goal on its own."""
        premises = [_P.parse("Mortal(socrates)"),
                   _P.parse("Mortal(socrates) ∧ Human(socrates)")]
        _skip_if_the_binary_crashed(premises, _GOAL)
        indices = eprover_relevant_premises(premises, _GOAL, timeout=15)
        assert indices in ((0,), (1,), (0, 1))
        assert _entails([premises[i] for i in indices], _GOAL)
