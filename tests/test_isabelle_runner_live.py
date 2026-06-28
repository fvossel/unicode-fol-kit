"""LIVE differential validation of the Isabelle runner against a Kripke oracle.

Skipped unless a real Isabelle/HOL installation is found (``isabelle_available()``);
these tests actually run ``isabelle build`` and take ~1-2 minutes total.

The oracle is an INDEPENDENT brute-force decision procedure for the alethic modal
fragment: it enumerates every Kripke frame of the chosen class (K/T/S4/S5) on up to
three worlds and every atom valuation, deciding validity with ``satisfies_modal``
directly (no shared code with the embedding / runner). For each (formula, frame)
the test asserts the real Isabelle verdict matches the oracle:

    oracle valid    => isabelle_decide_modal -> VALID   (battery proof closes it)
    oracle invalid  => isabelle_decide_modal -> INVALID  (nitpick finds a counter-model)

A divergence would mean the shallow embedding is unfaithful, the prove-battery is
unsound, or the runner mis-reads the build — exactly the failures unit tests on the
emitted *text* cannot catch. Two extra checks confirm the emitted axiom sets are
*consistent* (a contingent formula is INVALID, not vacuously VALID).

The standard modal axioms used here all have counter-models within three worlds, so
the bounded oracle is decisive for this corpus.
"""

from itertools import product

import pytest

from unicode_fol_kit.fol.nodes import Atom, And, Implies, Box, Diamond, Always, Next
from unicode_fol_kit.semantics.kripke import KripkeModel, satisfies_modal
from unicode_fol_kit.hol.isabelle_runner import (
    isabelle_available, isabelle_decide_modal, VALID, INVALID,
)

pytestmark = pytest.mark.skipif(
    not isabelle_available(),
    reason="no Isabelle installation found (set UFK_ISABELLE_HOME / ISABELLE_HOME)")


# --------------------------------------------------------------------------- #
# Independent brute-force Kripke oracle for the alethic fragment.
# --------------------------------------------------------------------------- #

_AX = {"K": (), "T": ("refl",), "S4": ("refl", "trans"),
       "S5": ("refl", "trans", "sym")}


def _frames(n, axioms):
    """Yield (worlds, alethic-relation) for every frame of ``axioms`` on n worlds."""
    worlds = list(range(n))
    edges = [(i, j) for i in worlds for j in worlds]
    for mask in product((False, True), repeat=len(edges)):
        rel = frozenset(e for e, inc in zip(edges, mask) if inc)
        if "refl" in axioms and not all((w, w) in rel for w in worlds):
            continue
        if "trans" in axioms and any(
                (a, b) in rel and (b, c) in rel and (a, c) not in rel
                for a in worlds for b in worlds for c in worlds):
            continue
        if "sym" in axioms and any(
                (a, b) in rel and (b, a) not in rel
                for a in worlds for b in worlds):
            continue
        yield worlds, rel


def _atom_keys(f):
    return sorted({n.to_unicode_str() for n in f.walk() if isinstance(n, Atom)})


def oracle_valid(f, frame_class, max_worlds=3):
    """True iff ``f`` is true at every world of every frame/valuation of the class."""
    keys = _atom_keys(f)
    for n in range(1, max_worlds + 1):
        for worlds, rel in _frames(n, _AX[frame_class]):
            for bits in product((False, True), repeat=n * len(keys)):
                val, idx = {}, 0
                for w in worlds:
                    cell = set()
                    for k in keys:
                        if bits[idx]:
                            cell.add(k)
                        idx += 1
                    val[w] = cell
                model = KripkeModel(worlds, {"alethic": rel}, val)
                if not all(satisfies_modal(f, model, w) for w in worlds):
                    return False
    return True


# --------------------------------------------------------------------------- #
# Corpus: standard modal axioms and their non-theorem instances.
# --------------------------------------------------------------------------- #

p, q = Atom("p", ()), Atom("q", ())
K_AX = Implies(Box(Implies(p, q)), Implies(Box(p), Box(q)))   # valid in K
T_AX = Implies(Box(p), p)                                     # reflexivity
FOUR = Implies(Box(p), Box(Box(p)))                           # transitivity
FIVE = Implies(Diamond(p), Box(Diamond(p)))                   # euclidean
B_AX = Implies(p, Box(Diamond(p)))                            # symmetry

# (formula, frame). The oracle decides the expected verdict; Isabelle must match.
CASES = [
    (K_AX, "K"),     # valid (K theorem)
    (T_AX, "K"),     # invalid (T not valid in K)
    (T_AX, "T"),     # valid
    (FOUR, "S4"),    # valid
    (FIVE, "K"),     # invalid
    (B_AX, "S5"),    # valid
]


@pytest.mark.parametrize("formula,frame", CASES,
                         ids=[f"{n}-{fr}" for n, (_, fr) in
                              zip(["K", "T", "T", "4", "5", "B"], CASES)])
def test_isabelle_matches_kripke_oracle(formula, frame):
    expected_valid = oracle_valid(formula, frame)
    v = isabelle_decide_modal(formula, frame=frame, card="1-3",
                              prove_timeout=40, refute_timeout=40)
    if expected_valid:
        assert v.status == VALID, (
            f"oracle: VALID in {frame}, Isabelle: {v.status}\n{v.prove_output[-800:]}")
        assert v.method == "prove-battery"
    else:
        # nitpick[expect=genuine] makes the build succeed IFF it finds a genuine
        # counter-model, so the INVALID verdict is certified by the exit code. The
        # counter-model *text* is best-effort: `isabelle build` does not echo theory
        # output to stdout, so `countermodel` is typically None — that is expected
        # and does not weaken the (sound) verdict.
        assert v.status == INVALID, (
            f"oracle: INVALID in {frame}, Isabelle: {v.status}\n"
            f"{v.refute_output[-800:]}")
        # these CASES are all propositional alethic, so a concrete Kripke witness is
        # reconstructed for the INVALID verdict.
        assert v.countermodel and "Kripke counter-model" in v.countermodel


# --------------------------------------------------------------------------- #
# Consistency: the emitted axioms must not be contradictory, else a VALID verdict
# would be vacuous (everything provable). A contingent atom must come out INVALID.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("frame", ["S4", "S5"])
def test_axiom_set_consistent_contingent_atom_is_invalid(frame):
    # `p` is contingent: it must NOT be valid (nitpick finds a ¬p world). If the
    # frame axioms were inconsistent the battery would "prove" it VALID.
    assert not oracle_valid(p, frame)                 # oracle agrees p is contingent
    v = isabelle_decide_modal(p, frame=frame, card="1-2",
                              prove_timeout=30, refute_timeout=30)
    assert v.status == INVALID, v.prove_output[-800:]


# --------------------------------------------------------------------------- #
# Temporal Always+Next faithfulness (audit regression): the henceforth relation t
# is pinned to the reflexive-transitive closure of the one-step n (t = n**), so a
# satisfies_modal-VALID temporal-induction formula is NOT spuriously refuted. The
# closure / Next fragment is only a shallow approximation (the prove battery does not
# do rtrancl induction and nitpick does not search the closure), so the guarantee
# here is the soundness one: NO false INVALID. Always→Next stays provable.
# --------------------------------------------------------------------------- #

def test_temporal_always_implies_next_is_valid():
    v = isabelle_decide_modal(Implies(Always(p), Next(p)), frame="K",
                              card="1-3", prove_timeout=40, refute_timeout=40)
    assert v.status == VALID, v.prove_output[-800:]


def test_temporal_induction_not_spuriously_invalid():
    # (p ∧ G(p→Xp)) → Gp is satisfies_modal-VALID; before the t = n** closure fix the
    # embedding's nitpick found a spurious counter-model and returned INVALID. It must
    # now NOT be INVALID (UNKNOWN is the honest outcome — the battery cannot do the
    # rtrancl induction; the point is no wrong verdict).
    f = Implies(And(p, Always(Implies(p, Next(p)))), Always(p))
    v = isabelle_decide_modal(f, frame="K", card="1-3",
                              prove_timeout=40, refute_timeout=40)
    assert v.status != INVALID, v.refute_output[-800:]


def test_temporal_next_implies_always_is_invalid():
    # Next(p) → Always(p) is satisfies_modal-INVALID. The refute theory defines
    # t = rtranclp n, so nitpick constructs the closure and genuinely refutes it —
    # restoring the INVALID the bare-axiom closure form could only report as UNKNOWN.
    v = isabelle_decide_modal(Implies(Next(p), Always(p)), frame="K",
                              card="1-3", prove_timeout=40, refute_timeout=40)
    assert v.status == INVALID, v.refute_output[-800:]
