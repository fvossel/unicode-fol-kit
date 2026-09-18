"""Tests for CTL (branching-time) model checking: ctl_ex/ctl_af/ctl_eg/ctl_au.

Three independent routes, mirroring the style of ``test_kripke.py``:

1. Duality/property-based checks over randomly generated small TOTAL Kripke
   models (AF/EG De Morgan duality, ``AU(φ,ψ) ⊨ AF ψ``, ``AG φ → AF φ ∧ EG φ``
   — the last using the kit's existing ``Always`` node, which IS textbook AG
   here, see ``kripke.py``'s own docstring on why that reduction is exact).
2. A brute-force differential: enumerate every LASSO path (a finite simple
   prefix plus a simple cycle) reachable from a world and decide AF/EG/AU by
   explicit path quantification over that finite representative set, sharing
   no code with kripke.py's fixpoint implementation, then cross-check.
3. Hand-checked textbook fixtures: a small mutual-exclusion-style Kripke
   structure with worked-by-hand AG/AF/EG/EX/AU truth values, plus a
   dead-end fixture pinning down the totality/deadlock convention.
"""

import random

import pytest

from unicode_fol_kit.semantics.kripke import (
    KripkeModel, satisfies_modal, ctl_ex, ctl_af, ctl_eg, ctl_au,
)
from unicode_fol_kit.fol.nodes import Atom, Not, And, Always, Next

P = Atom("P", [])
Q = Atom("Q", [])
CRIT1 = Atom("crit1", [])
CRIT2 = Atom("crit2", [])


# ---------------------------------------------------------------------------
# Random-model helper (total on worlds, so ctl_af/ctl_eg/ctl_au never raise)
# ---------------------------------------------------------------------------

def _random_total_temporal_model(rng, n_worlds=5, p_edge=0.35):
    """A random temporal Kripke model over 0..n-1 with atoms P, Q.

    Total on ``worlds``: any world random edge selection left without an
    in-worlds successor gets a forced self-loop, so ctl_af/ctl_eg/ctl_au are
    always well-defined on these models (no ValueError).
    """
    worlds = list(range(n_worlds))
    edges = {(a, b) for a in worlds for b in worlds if rng.random() < p_edge}
    for w in worlds:
        if not any(a == w for (a, _) in edges):
            edges.add((w, w))
    valuation = {}
    for w in worlds:
        true_here = set()
        if rng.random() < 0.5:
            true_here.add("P")
        if rng.random() < 0.5:
            true_here.add("Q")
        valuation[w] = true_here
    return KripkeModel(worlds=worlds, relations={"temporal": edges}, valuation=valuation)


# ---------------------------------------------------------------------------
# Route 1: duality / entailment properties over random total models
# ---------------------------------------------------------------------------

def test_af_eg_duality_random():
    """AF φ ⇔ ¬EG¬φ, and its mirror EG φ ⇔ ¬AF¬φ, on many random total models."""
    rng = random.Random(4242)
    for _ in range(200):
        model = _random_total_temporal_model(rng, n_worlds=rng.randint(1, 5))
        for w in model.worlds:
            assert ctl_af(model, w, P) == (not ctl_eg(model, w, Not(P)))
            assert ctl_eg(model, w, P) == (not ctl_af(model, w, Not(P)))


def test_au_entails_af_random():
    """A[φ U ψ] ⊨ AF ψ, on many random total models."""
    rng = random.Random(99991)
    for _ in range(200):
        model = _random_total_temporal_model(rng, n_worlds=rng.randint(1, 5))
        for w in model.worlds:
            if ctl_au(model, w, P, Q):
                assert ctl_af(model, w, Q)


def test_ag_implies_af_and_eg_random():
    """AG φ → (AF φ ∧ EG φ), on many random total models.

    ``Always`` IS textbook AG here (kripke.py's module docstring: Always
    reduces exactly to reflexive-transitive reachability, unlike AF, which
    does not reduce to reachability and needs a genuine forward fixpoint).
    """
    rng = random.Random(31337)
    for _ in range(200):
        model = _random_total_temporal_model(rng, n_worlds=rng.randint(1, 5))
        for w in model.worlds:
            if satisfies_modal(Always(P), model, w):
                assert ctl_af(model, w, P)
                assert ctl_eg(model, w, P)


def test_ex_is_dual_of_next_random():
    """EX φ ⇔ ¬Next(¬φ) ("¬AX¬φ"), on random models — including dangling
    temporal edges into worlds OUTSIDE model.worlds and worlds with no
    successor at all, since ctl_ex needs neither totality nor in-worlds
    successors (see its own docstring). This is an independent oracle: it
    cross-checks ctl_ex against satisfies_modal's PRE-EXISTING Next dispatch
    branch, not against any code written for this ticket.
    """
    rng = random.Random(161803)
    for _ in range(300):
        n = rng.randint(1, 5)
        worlds = list(range(n))
        # b ranges over n+2 so some edges dangle outside model.worlds.
        edges = {(a, b) for a in worlds for b in range(n + 2) if rng.random() < 0.3}
        valuation = {w: ({"P"} if rng.random() < 0.5 else set()) for w in worlds}
        model = KripkeModel(worlds=worlds, relations={"temporal": edges}, valuation=valuation)
        for w in worlds:
            assert ctl_ex(model, w, P) == (not satisfies_modal(Next(Not(P)), model, w))


# ---------------------------------------------------------------------------
# Route 2: an independent brute-force lasso-path decision procedure
# ---------------------------------------------------------------------------

def _successors_in_worlds(model, w):
    """Raw temporal successors of ``w``, filtered to ``model.worlds``.

    Deliberately re-derived from ``model.relation("temporal")`` here (not
    imported from kripke.py's private ``_ctl_temporal_successors``), so this
    brute-force route shares no code with the fixpoint implementation under
    test.
    """
    return {w2 for (w1, w2) in model.relation("temporal") if w1 == w and w2 in model.worlds}


def _enumerate_lassos(model, start):
    """Yield every ``(prefix, cycle)`` lasso decomposition of an infinite
    temporal path from ``start`` (both tuples of worlds).

    ``cycle`` is nonempty and its last world has a temporal edge back to its
    first; the infinite path is ``prefix + cycle`` repeated forever. On a
    finite graph a path must revisit some world within ``|model.worlds|``
    steps (pigeonhole), so every infinite path reduces, for the purpose of
    deciding an eventually/globally-style property, to one of these lassos —
    found here by depth-first search over SIMPLE paths from ``start``: at
    each step, closing back into an already-visited world yields one lasso;
    stepping to a genuinely new world extends the search.
    """
    def dfs(path):
        last = path[-1]
        for s in sorted(_successors_in_worlds(model, last), key=repr):
            if s in path:
                j = path.index(s)
                yield tuple(path[:j]), tuple(path[j:])
            else:
                yield from dfs(path + [s])
    yield from dfs([start])


def _brute_af(model, start, formula):
    """AF φ by explicit lasso quantification: φ must occur in every lasso."""
    for prefix, cycle in _enumerate_lassos(model, start):
        window = prefix + cycle
        if not any(satisfies_modal(formula, model, w) for w in window):
            return False
    return True


def _brute_eg(model, start, formula):
    """EG φ by explicit lasso quantification: some lasso has φ everywhere."""
    for prefix, cycle in _enumerate_lassos(model, start):
        window = prefix + cycle
        if all(satisfies_modal(formula, model, w) for w in window):
            return True
    return False


def _brute_au(model, start, phi, psi):
    """A[φ U ψ] by explicit lasso quantification.

    A lasso VIOLATES the formula iff ψ never holds anywhere in one full
    unrolling (``prefix + cycle`` — if ψ is absent there it is absent from
    every later repetition of the cycle too, so one lap suffices), or φ
    fails at some world strictly before ψ's first occurrence in that window.
    """
    for prefix, cycle in _enumerate_lassos(model, start):
        window = prefix + cycle
        psi_indices = [i for i, w in enumerate(window) if satisfies_modal(psi, model, w)]
        if not psi_indices:
            return False
        first = psi_indices[0]
        if not all(satisfies_modal(phi, model, w) for w in window[:first]):
            return False
    return True


def test_brute_force_differential_af_eg_au():
    """Cross-check ctl_af/ctl_eg/ctl_au against the independent lasso-path decision."""
    rng = random.Random(271828)
    for _ in range(150):
        model = _random_total_temporal_model(rng, n_worlds=rng.randint(1, 6), p_edge=0.4)
        for w in model.worlds:
            assert ctl_af(model, w, P) == _brute_af(model, w, P)
            assert ctl_eg(model, w, P) == _brute_eg(model, w, P)
            assert ctl_au(model, w, P, Q) == _brute_au(model, w, P, Q)


# ---------------------------------------------------------------------------
# Route 3: hand-checked textbook fixtures
# ---------------------------------------------------------------------------

def test_mutex_hand_checked_ag_af_eg_ex_au():
    """A 3-world mutual-exclusion-style model; every value below is worked out
    by hand (see the comment on each assertion), not derived from the code
    under test.

    Worlds: 0 = idle, 1 = process 1's critical section, 2 = process 2's
    critical section. Temporal edges: 0->1 (P1 may enter), 0->0 (idle may
    stay idle forever — an infinite "nobody ever enters" path exists), 1->2,
    2->0 (round-robin back to idle). Total: every world has a successor.
    """
    model = KripkeModel(
        worlds={0, 1, 2},
        relations={"temporal": {(0, 1), (0, 0), (1, 2), (2, 0)}},
        valuation={1: {"crit1"}, 2: {"crit2"}},
    )
    mutex_safety = Not(And(CRIT1, CRIT2))

    # AG(not(crit1 and crit2)): never both critical at once. True everywhere,
    # since no world's valuation has both atoms true (Always IS AG here).
    for w in (0, 1, 2):
        assert satisfies_modal(Always(mutex_safety), model, w) is True

    # AF(crit1): true only where crit1 already holds (world 1); worlds 0 and
    # 2 can both escape via the 0->0 self-loop and never reach crit1.
    assert ctl_af(model, 0, CRIT1) is False
    assert ctl_af(model, 1, CRIT1) is True
    assert ctl_af(model, 2, CRIT1) is False

    # EG(not crit1): worlds 0 and 2 both have the "loop at 0 forever, never
    # revisit 1" path witnessing it; world 1 fails immediately since crit1 IS
    # true there right now (EG needs the formula at the CURRENT world too).
    assert ctl_eg(model, 0, Not(CRIT1)) is True
    assert ctl_eg(model, 1, Not(CRIT1)) is False
    assert ctl_eg(model, 2, Not(CRIT1)) is True

    # EX(crit1): only world 0 has an immediate successor (world 1) with crit1.
    assert ctl_ex(model, 0, CRIT1) is True
    assert ctl_ex(model, 1, CRIT1) is False
    assert ctl_ex(model, 2, CRIT1) is False

    # A[not crit1 U crit2]: true only at world 2, where crit2 already holds
    # (n=0 case); false at 0 (the self-loop path never reaches crit2 at all)
    # and at 1 ("not crit1" already fails there, since crit1 IS true at 1).
    assert ctl_au(model, 0, Not(CRIT1), CRIT2) is False
    assert ctl_au(model, 1, Not(CRIT1), CRIT2) is False
    assert ctl_au(model, 2, Not(CRIT1), CRIT2) is True


def test_af_eg_au_raise_on_temporal_deadlock():
    """A world with no temporal successor inside model.worlds makes
    ctl_af/ctl_eg/ctl_au raise ValueError naming it — the deadlock convention
    this ticket fixes: AF/EG/AU quantify over INFINITE paths, so a dead end
    cannot be given the silent vacuous-truth reading Next/ctl_ex use.
    """
    model = KripkeModel(worlds={0, 1}, relations={"temporal": {(0, 1)}},
                        valuation={0: {"P"}, 1: {"P"}})
    for fn, args in (
        (ctl_af, (P,)),
        (ctl_eg, (P,)),
        (ctl_au, (P, P)),
    ):
        with pytest.raises(ValueError, match=r"world 1 has no temporal successor"):
            fn(model, 0, *args)


def test_ex_needs_no_totality_at_a_dead_end():
    """Unlike ctl_af/ctl_eg/ctl_au, ctl_ex never raises: a dead end just makes
    it False there (the existential dual of Next's vacuous True), even though
    the model as a whole is not total.
    """
    model = KripkeModel(worlds={0, 1}, relations={"temporal": {(0, 1)}},
                        valuation={0: {"P"}, 1: {"P"}})
    assert ctl_ex(model, 1, P) is False              # 1 is the dead end
    assert satisfies_modal(Next(P), model, 1) is True  # Next's own vacuous-true dual
    assert ctl_ex(model, 0, P) is True                # 0 -> 1, and P holds at 1


def test_ex_follows_next_convention_for_out_of_model_successor():
    """A temporal edge into a world OUTSIDE model.worlds still counts for EX,
    exactly as it already does for the built-in universal Next (hand check;
    see the module docstring on Next/Always/.../Until being read off
    ``model.successors``/``model.relation`` unfiltered).
    """
    model = KripkeModel(worlds={0}, relations={"temporal": {(0, 99)}}, valuation={99: {"Q"}})
    assert ctl_ex(model, 0, Q) is True
    assert satisfies_modal(Next(Q), model, 0) is True


def test_ctl_functions_do_not_mutate_model():
    """Calling all four CTL functions repeatedly must not change the model."""
    model = KripkeModel(
        worlds={0, 1, 2},
        relations={"temporal": {(0, 1), (1, 2), (2, 0)}},
        valuation={0: {"P"}, 2: {"Q"}},
    )
    relations_snapshot = dict(model.relations)
    valuation_snapshot = dict(model.valuation)
    for w in model.worlds:
        ctl_ex(model, w, P)
        ctl_af(model, w, P)
        ctl_eg(model, w, P)
        ctl_au(model, w, P, Q)
    assert model.relations == relations_snapshot
    assert model.valuation == valuation_snapshot
