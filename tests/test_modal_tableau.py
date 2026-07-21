"""Tests for the labelled modal tableau (unicode_fol_kit.atp.modal_tableau).

The verdicts are hand-checked against the standard modal correspondence theory
(T↔reflexive, 4↔transitive, B↔symmetric, 5↔euclidean, D↔serial) and, in bulk,
differentially against a brute-force Kripke oracle over the frame classes with
≤3 worlds (the same oracle style the live Isabelle tests use). Every *invalid*
verdict is additionally backed by a counter-model that ``satisfies_modal``
confirms falsifies the formula.
"""

import itertools
import random

import pytest

from unicode_fol_kit.fol.nodes import (
    Atom, Not, And, Or, Implies, Iff, Box, Diamond,
    Knows, Believes, Obligatory, Permitted, Next, Always, Eventually, Until,
)
from unicode_fol_kit.atp.modal_tableau import (
    is_modal_valid, modal_prove, modal_decide, modal_countermodel,
    modal_tableau_closed, has_modal,
)
from unicode_fol_kit.atp.tableau import is_valid_tableau, prove_tableau, tableau_model
from unicode_fol_kit.semantics.kripke import KripkeModel, satisfies_modal

p, q, r = Atom("p", ()), Atom("q", ()), Atom("r", ())


# --------------------------------------------------------------------------- #
# Characteristic axioms: valid exactly on their corresponding frames.
# --------------------------------------------------------------------------- #

# (formula, frame, expected_valid)
_AXIOM_CASES = [
    # K: distribution + necessitation hold on every frame.
    (Implies(Box(Implies(p, q)), Implies(Box(p), Box(q))), "K", True),
    (Box(Or(p, Not(p))), "K", True),
    (Iff(Diamond(p), Not(Box(Not(p)))), "K", True),                 # □/◇ duality
    (Implies(And(Box(p), Box(q)), Box(And(p, q))), "K", True),
    # T = reflexive: □p → p.
    (Implies(Box(p), p), "K", False),
    (Implies(Box(p), p), "T", True),
    (Implies(Box(p), p), "S4", True),
    (Implies(Box(p), p), "S5", True),
    # D = serial: □p → ◇p.
    (Implies(Box(p), Diamond(p)), "K", False),
    (Implies(Box(p), Diamond(p)), "KD", True),
    (Implies(Box(p), Diamond(p)), "T", True),                        # reflexive ⇒ serial
    # 4 = transitive: □p → □□p.
    (Implies(Box(p), Box(Box(p))), "K", False),
    (Implies(Box(p), Box(Box(p))), "T", False),
    (Implies(Box(p), Box(Box(p))), "S4", True),
    (Implies(Box(p), Box(Box(p))), "K4", True),
    # B = symmetric: p → □◇p.
    (Implies(p, Box(Diamond(p))), "T", False),
    (Implies(p, Box(Diamond(p))), "B", True),
    (Implies(p, Box(Diamond(p))), "S5", True),
    # 5 = euclidean: ◇p → □◇p.
    (Implies(Diamond(p), Box(Diamond(p))), "S4", False),
    (Implies(Diamond(p), Box(Diamond(p))), "S5", True),
    (Implies(Diamond(p), Box(Diamond(p))), "K45", True),
]


@pytest.mark.parametrize("formula, frame, expected", _AXIOM_CASES,
                         ids=[f"{i}" for i in range(len(_AXIOM_CASES))])
def test_characteristic_axioms(formula, frame, expected):
    assert is_modal_valid(formula, frame=frame) is expected
    # modal_decide agrees and is never 'unknown' on these small inputs.
    assert modal_decide(formula, frame=frame) == ("valid" if expected else "invalid")


@pytest.mark.parametrize("formula, frame, expected", _AXIOM_CASES,
                         ids=[f"{i}" for i in range(len(_AXIOM_CASES))])
def test_invalid_axioms_have_verified_countermodels(formula, frame, expected):
    cm = modal_countermodel(formula, frame=frame)
    if expected:
        assert cm is None
    else:
        assert cm is not None
        # The counter-model genuinely falsifies the formula at its root world.
        assert satisfies_modal(formula, cm, 0) is False


# --------------------------------------------------------------------------- #
# Epistemic / doxastic / deontic systems.
# --------------------------------------------------------------------------- #

def test_epistemic_factivity_needs_reflexive_system():
    factive = Implies(Knows("a", p), p)
    assert is_modal_valid(factive, frame="K") is False              # plain K: not factive
    assert is_modal_valid(factive, frame="K", systems={"epistemic": "S5"}) is True
    assert is_modal_valid(factive, frame="K", systems={"epistemic": "T"}) is True


def test_positive_introspection_needs_transitive_epistemic():
    pi = Implies(Knows("a", p), Knows("a", Knows("a", p)))          # K_a p → K_a K_a p
    assert is_modal_valid(pi, frame="K", systems={"epistemic": "S5"}) is True
    assert is_modal_valid(pi, frame="K", systems={"epistemic": "T"}) is False


def test_belief_consistency_in_kd45():
    # Consistent belief D: B_a p → ¬B_a ¬p, valid when belief is serial (KD45).
    consist = Implies(Believes("a", p), Not(Believes("a", Not(p))))
    assert is_modal_valid(consist, frame="K", systems={"doxastic": "KD45"}) is True
    assert is_modal_valid(consist, frame="K") is False


def test_deontic_d_axiom_default_kd():
    # Standard Deontic Logic: Oφ → Pφ (deontic relation is serial by default).
    assert is_modal_valid(Implies(Obligatory(p), Permitted(p))) is True
    # ...but not if the deontic system is downgraded to plain K (non-serial).
    assert is_modal_valid(Implies(Obligatory(p), Permitted(p)),
                          systems={"deontic": "K"}) is False


def test_no_deontic_explosion():
    # Oφ ∧ O¬φ is consistent in plain K-deontic but inconsistent under seriality:
    # O(p) ∧ O(¬p) → O(False)-style collapse only with a successor.
    both = And(Obligatory(p), Obligatory(Not(p)))
    # In KD (serial) the two obligations clash at the mandated world ⇒ ¬(both) valid.
    assert is_modal_valid(Not(both)) is True
    # In K-deontic there need be no deontic successor ⇒ both can hold ⇒ ¬(both) invalid.
    assert is_modal_valid(Not(both), systems={"deontic": "K"}) is False


def test_next_is_universal_over_temporal_successors():
    # Next distributes over → (K axiom for the temporal one-step box).
    k_next = Implies(Next(Implies(p, q)), Implies(Next(p), Next(q)))
    assert is_modal_valid(k_next) is True
    # X p → p is NOT valid (the next state need not be the current one).
    assert is_modal_valid(Implies(Next(p), p)) is False


# --------------------------------------------------------------------------- #
# Entailment (local consequence) and the multi-modal mix.
# --------------------------------------------------------------------------- #

def test_local_consequence():
    # Necessitation is a *global* rule, not local: p ⊬ □p.
    assert modal_prove([p], Box(p), frame="S5") is False
    # But □p, □(p→q) ⊢ □q locally (K-distribution).
    assert modal_prove([Box(p), Box(Implies(p, q))], Box(q), frame="K") is True


def test_mixed_modalities_independent_relations():
    # Knowledge and obligation use different relations: K_a p ⊬ O p.
    assert is_modal_valid(Implies(Knows("a", p), Obligatory(p)),
                          systems={"epistemic": "S5"}) is False


# --------------------------------------------------------------------------- #
# Delegation from the classical tableau entry points.
# --------------------------------------------------------------------------- #

def test_classical_tableau_delegates_modal_instead_of_raising():
    # The classical engine used to raise ValueError on a Box node; now it decides
    # the formula over K via the modal tableau.
    assert is_valid_tableau(Implies(Box(Implies(p, q)), Implies(Box(p), Box(q)))) is True
    assert is_valid_tableau(Implies(Box(p), p)) is False            # T-axiom invalid in K
    assert prove_tableau([Box(p), Box(Implies(p, q))], Box(q)) is True


def test_tableau_model_rejects_modal_with_pointer():
    with pytest.raises(NotImplementedError, match="modal_countermodel"):
        tableau_model([Box(p)])


def test_has_modal():
    assert has_modal(Box(p)) is True
    assert has_modal(Implies(p, Knows("a", q))) is True
    assert has_modal(Implies(p, q)) is False


# --------------------------------------------------------------------------- #
# Temporal-closure operators: sound verdicts, never a crash.
#
# The tableau has no rule for G/F/U/H/P/Y/S, so it leaves them INERT: a branch
# may still close on other grounds (sound — closure is monotone), and an open
# branch's model reaches a caller only after satisfies_modal verification. The
# result is valid / invalid-with-verified-countermodel / honest unknown — the
# earlier behaviour (raising NotImplementedError) violated modal_decide's own
# documented three-way contract.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("formula", [
    Always(p), Eventually(p), Until(p, q),
    Implies(Always(p), p), Not(Eventually(p)),
])
def test_temporal_closure_operators_never_raise(formula):
    verdict = modal_decide(formula)
    assert verdict in ("valid", "invalid", "unknown")


def test_temporal_closure_verdicts_are_sound():
    # Ⓖp alone is refutable, and the countermodel is VERIFIED by satisfies_modal
    # before being handed back — a genuine "invalid", not a guess.
    assert modal_decide(Always(p)) == "invalid"
    assert modal_countermodel(Always(p)) is not None
    # Ⓖp → p (the T reading over the reflexive closure) is beyond the inert
    # treatment: neither provable nor refutable here, so honestly unknown.
    assert modal_decide(Implies(Always(p), p)) == "unknown"
    # is_modal_valid stays sound: False (= not proved), never a crash.
    assert is_modal_valid(Implies(Always(p), p)) is False


def test_quantified_constructs_are_opaque_literals_not_crashes():
    # A quantified construct under a modal operator has no rule either, but a
    # syntactic-complement closure is still sound — the identity is provable.
    from unicode_fol_kit.fol.msflparser import MSFLParser
    m = MSFLParser(modal=True)
    assert modal_decide(m.parse("◇(∃≥1 x P(x)) → ◇(∃≥1 x P(x))")) == "valid"
    # No closure and no verifiable countermodel → honest unknown, no crash.
    assert modal_decide(m.parse("¬◇(∃≥1 x P(x))")) == "unknown"


# --------------------------------------------------------------------------- #
# Frame / system validation.
# --------------------------------------------------------------------------- #

def test_unknown_frame_and_system_rejected():
    with pytest.raises(ValueError, match="unknown frame"):
        is_modal_valid(Box(p), frame="S99")
    with pytest.raises(ValueError, match="unknown system"):
        is_modal_valid(Box(p), systems={"epistemic": "Z9"})
    with pytest.raises(ValueError, match="unknown system family"):
        is_modal_valid(Box(p), systems={"alethic": "S4"})


# --------------------------------------------------------------------------- #
# Bulk differential test against a brute-force Kripke oracle (≤3 worlds).
# --------------------------------------------------------------------------- #

_ATOMS = [Atom("p", ()), Atom("q", ())]
_FRAME_CONDS = {
    "K": [], "T": ["refl"], "S4": ["refl", "trans"],
    "S5": ["refl", "trans", "sym"], "KD": ["serial"], "B": ["refl", "sym"],
}


def _rand_formula(depth, rng):
    if depth <= 0 or (depth < 3 and rng.random() < 0.4):
        return rng.choice(_ATOMS)
    k = rng.random()
    if k < 0.18:
        return Not(_rand_formula(depth - 1, rng))
    if k < 0.33:
        return Box(_rand_formula(depth - 1, rng))
    if k < 0.48:
        return Diamond(_rand_formula(depth - 1, rng))
    if k < 0.62:
        return And(_rand_formula(depth - 1, rng), _rand_formula(depth - 1, rng))
    if k < 0.76:
        return Or(_rand_formula(depth - 1, rng), _rand_formula(depth - 1, rng))
    if k < 0.90:
        return Implies(_rand_formula(depth - 1, rng), _rand_formula(depth - 1, rng))
    return Iff(_rand_formula(depth - 1, rng), _rand_formula(depth - 1, rng))


def _relation_ok(R, n, conds):
    W = range(n)
    if "refl" in conds and any((w, w) not in R for w in W):
        return False
    if "sym" in conds and any((w, v) in R and (v, w) not in R for w in W for v in W):
        return False
    if "trans" in conds and any((w, v) in R and (v, u) in R and (w, u) not in R
                                for w in W for v in W for u in W):
        return False
    if "eucl" in conds and any((w, v) in R and (w, u) in R and (v, u) not in R
                               for w in W for v in W for u in W):
        return False
    if "serial" in conds and any(not any((w, v) in R for v in W) for w in W):
        return False
    return True


def _brute_valid(f, conds, N=3):
    keys = [a.to_unicode_str() for a in _ATOMS]
    for n in range(1, N + 1):
        W = list(range(n))
        all_edges = [(w, v) for w in W for v in W]
        for rbits in range(1 << len(all_edges)):
            R = set(all_edges[i] for i in range(len(all_edges)) if rbits >> i & 1)
            if not _relation_ok(R, n, conds):
                continue
            for vbits in range(1 << (len(keys) * n)):
                val, idx = {}, 0
                for w in W:
                    s = set()
                    for key in keys:
                        if vbits >> idx & 1:
                            s.add(key)
                        idx += 1
                    val[w] = s
                m = KripkeModel(W, {"alethic": R}, val)
                if any(not satisfies_modal(f, m, w) for w in W):
                    return False
    return True


def test_differential_vs_brute_force_oracle():
    rng = random.Random(2026)
    checked = 0
    for _ in range(80):
        f = _rand_formula(3, rng)
        frame = rng.choice(list(_FRAME_CONDS))
        brute = _brute_valid(f, _FRAME_CONDS[frame], N=3)
        tab = is_modal_valid(f, frame=frame)
        # Soundness: a closed tableau (valid) must hold in every small model.
        assert not (tab and not brute), \
            f"tableau VALID but oracle found a countermodel [{frame}]: {f.to_unicode_str()}"
        # Completeness (within the FMP bound of these shallow formulas): oracle-valid
        # up to 3 worlds must be matched by the tableau.
        assert not (brute and not tab), \
            f"oracle VALID(<=3w) but tableau did not close [{frame}]: {f.to_unicode_str()}"
        # When the tableau reports invalid it must be via a verified counter-model.
        if not tab:
            assert modal_decide(f, frame=frame) == "invalid"
            assert satisfies_modal(f, modal_countermodel(f, frame=frame), 0) is False
        checked += 1
    assert checked == 80
