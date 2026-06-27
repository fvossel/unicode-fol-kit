"""Independent differential test for the modal (alethic) Fitch checker.

The Fitch modal checker certifies each step via the *standard translation* to FOL plus
the frame axioms, decided by Z3. This test cross-checks its accept/reject decisions
against a SECOND, independent oracle: brute-force enumeration of small Kripke frames of
the relevant class (K / T / S4 / S5), using ``satisfies_modal`` directly. A regression
in ``standard_translation`` or the frame-axiom set would diverge here even though the
committed hand-pinned modal tests (which exercise the same translation path) would not.

Scope: the alethic □/◇ fragment, which uses the single ``"alethic"`` accessibility
relation; the epistemic/deontic agent-keyed relations are out of scope for this harness.
"""

from itertools import product

import pytest

from unicode_fol_kit.fol.nodes import Atom, Not, And, Or, Implies, Box, Diamond
from unicode_fol_kit.atp.fitch import Proof, premise, line, check_proof
from unicode_fol_kit.semantics.kripke import KripkeModel, satisfies_modal

P, Q = Atom("P", ()), Atom("Q", ())

# Frame-class → relational axioms (mirrors fitch._FRAME_AXIOMS for the alethic systems).
_AXIOMS = {"K": (), "T": ("refl",), "S4": ("refl", "trans"), "S5": ("refl", "trans", "sym")}


def _atom_keys(*formulas):
    keys = set()
    for f in formulas:
        for node in f.walk():
            if isinstance(node, Atom):
                keys.add(node.to_unicode_str())
    return sorted(keys)


def _frames(n, axioms):
    """Yield every ``"alethic"`` relation on ``{0..n-1}`` satisfying ``axioms``."""
    worlds = list(range(n))
    edges = [(i, j) for i in worlds for j in worlds]
    for mask in product((False, True), repeat=len(edges)):
        R = frozenset(e for e, inc in zip(edges, mask) if inc)
        if "refl" in axioms and not all((w, w) in R for w in worlds):
            continue
        if "trans" in axioms and any((a, b) in R and (b, c) in R and (a, c) not in R
                                     for a in worlds for b in worlds for c in worlds):
            continue
        if "sym" in axioms and any((a, b) in R and (b, a) not in R
                                   for a in worlds for b in worlds):
            continue
        yield R


def alethic_valid(premises, conclusion, frame_class, max_worlds=3):
    """True iff ``premises`` entail ``conclusion`` over every Kripke frame of the class.

    Independent of the checker: enumerates frames (satisfying the class axioms) and all
    world-valuations of the atoms, and checks that wherever all premises hold at a world
    the conclusion holds there too. A counterexample makes it False.
    """
    axioms = _AXIOMS[frame_class]
    keys = _atom_keys(*premises, conclusion)
    for n in range(1, max_worlds + 1):
        worlds = list(range(n))
        for R in _frames(n, axioms):
            for bits in product((False, True), repeat=n * len(keys)):
                valuation = {}
                idx = 0
                for w in worlds:
                    cell = set()
                    for key in keys:
                        if bits[idx]:
                            cell.add(key)
                        idx += 1
                    valuation[w] = cell
                model = KripkeModel(worlds=worlds, relations={"alethic": R}, valuation=valuation)
                for w in worlds:
                    if all(satisfies_modal(p, model, w) for p in premises) \
                            and not satisfies_modal(conclusion, model, w):
                        return False
    return True


# Each case: (label, premises, steps, conclusion, frame_class, expected) where `expected`
# is what BOTH the checker and the independent Kripke oracle must report.
_K_AXIOM = Implies(Box(Implies(P, Q)), Implies(Box(P), Box(Q)))
_AX4 = Implies(Box(P), Box(Box(P)))

_CASES = [
    # T-factivity □P ⊢ P: valid with reflexivity, invalid without.
    ("T-factivity in T", [premise(1, Box(P))], [line(2, P, "□E", 1)], P, "T", True),
    ("T-factivity not in K", [premise(1, Box(P))], [line(2, P, "□E", 1)], P, "K", False),
    # Axiom 4 □P→□□P: valid with transitivity, invalid without.
    ("Ax4 in S4", [], [line(1, _AX4, "Ax4")], _AX4, "S4", True),
    ("Ax4 not in T", [], [line(1, _AX4, "Ax4")], _AX4, "T", False),
    # K distribution axiom: valid on every frame.
    ("K-axiom in K", [], [line(1, _K_AXIOM, "K")], _K_AXIOM, "K", True),
    # Necessitation of a tautology: valid on every frame.
    ("Nec ⊤ in K", [], [line(1, Box(Or(P, Not(P))), "Nec")], Box(Or(P, Not(P))), "K", True),
    # Contingent necessitation P ⊢ □P: invalid everywhere.
    ("contingent Nec in S5", [premise(1, P)], [line(2, Box(P), "Nec")], Box(P), "S5", False),
]


@pytest.mark.parametrize("label,prem,steps,concl,frame,expected",
                         _CASES, ids=[c[0] for c in _CASES])
def test_modal_checker_matches_independent_kripke_oracle(label, prem, steps, concl, frame, expected):
    accepted = check_proof(Proof(premises=prem, steps=steps, logic=frame))
    prem_formulas = [p.formula for p in prem]
    valid = alethic_valid(prem_formulas, concl, frame)
    # The independent oracle confirms the intended frame-validity...
    assert valid is expected, f"{label}: Kripke oracle says valid={valid}, expected {expected}"
    # ...and the checker's accept/reject tracks it (soundness: accepted ⇒ valid).
    assert accepted is expected, f"{label}: checker accepted={accepted}, expected {expected}"
    if accepted:
        assert valid, f"{label}: checker accepted an alethically INVALID step"
