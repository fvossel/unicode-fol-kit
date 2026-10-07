"""Tests for the labelled modal tableau (unicode_logic_kit.atp.modal_tableau).

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

from unicode_logic_kit.fol.nodes import (
    Atom, Not, And, Or, Implies, Iff, Box, Diamond,
    Knows, Believes, Obligatory, Permitted, Next, Always, Eventually, Until,
)
from unicode_logic_kit.atp.modal_tableau import (
    is_modal_valid, modal_prove, modal_decide, modal_countermodel,
    modal_tableau_closed, has_modal,
)
from unicode_logic_kit.atp.tableau import is_valid_tableau, prove_tableau, tableau_model
from unicode_logic_kit.semantics.kripke import KripkeModel, satisfies_modal

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
    from unicode_logic_kit.fol.msflparser import MSFLParser
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
    # A system name is resolved through the shared frame registry now, so an
    # unknown one reports as an unknown FRAME (same refusal, one vocabulary).
    with pytest.raises(ValueError, match="unknown frame"):
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


# --------------------------------------------------------------------------- #
# Equality is NOT interpreted: an '=' / '≠' atom is refused BY NAME, wherever it
# sits, at the ENTRY of every public function.
#
# The tableau has no term semantics (an atom is a propositional letter: a branch
# closes on a syntactic complement, an open branch is read off as a valuation of
# rendered atom keys), so it would read ``a = b`` as an uninterpreted proposition
# while ``fol.qml.qml_is_valid`` reads it as RIGID identity: ``a = a`` came back
# "not valid" here (valid there) and ``a = b → □(a = b)`` "unknown" (valid there).
# The refusal is a whole-formula scan BEFORE the search, so a verdict can never be
# returned by a run that did not look at the atom: each "skeleton" case below is
# decided by the tableau without ever examining the atom it contains.
# tests/test_kripke.py holds the same table for the Kripke evaluator.
# --------------------------------------------------------------------------- #

from unicode_logic_kit.fol.nodes import (
    Constant, Variable, Xor, Says, Wants, Historically, Once, Previous, Since,
    Quantifier, SortedQuantifier,
)
from unicode_logic_kit.fol._modal_nodes import (
    EverybodyKnows, DistributedKnowledge, CommonKnowledge,
    Announce, AnnounceDiamond,
)
from unicode_logic_kit.semantics._modal_reject import (
    reject_equality, reject_equality_in, is_equality_atom, EQUALITY_PREDICATES,
)

_a, _b = Constant("a"), Constant("b")
EQ = Atom("=", (_a, _b))
NEQ = Atom("≠", (_a, _b))
Z = Atom("Z", ())          # the control: the same wrapper around an ordinary atom
_REFUSAL = r"equality is not interpreted by the propositional modal tableau.*qml_is_valid"


# every place an equality atom can sit: each node type that has a sub-formula and
# that the tableau does not reject for another reason (the hybrid constructs
# Nominal / At / Down are refused whole, with or without an equality atom)
_WRAPPERS = {
    "bare": lambda e: e,
    "not": Not,
    "not_not": lambda e: Not(Not(e)),
    "and_left": lambda e: And(e, Z),
    "and_right": lambda e: And(Z, e),
    "or_left": lambda e: Or(e, Z),
    "or_right": lambda e: Or(Z, e),
    "xor": lambda e: Xor(Z, e),
    "implies_antecedent": lambda e: Implies(e, Z),
    "implies_consequent": lambda e: Implies(Z, e),
    "iff": lambda e: Iff(Z, e),
    "box": Box,
    "diamond": Diamond,
    "not_box": lambda e: Not(Box(e)),
    "not_diamond": lambda e: Not(Diamond(e)),
    "knows": lambda e: Knows(Constant("a"), e),
    "believes": lambda e: Believes(Constant("a"), e),
    "says": lambda e: Says(Constant("a"), e),
    "wants": lambda e: Wants(Constant("a"), e),
    "obligatory": Obligatory,
    "permitted": Permitted,
    "next": Next,
    "always": Always,                       # inert in the tableau, still scanned
    "eventually": Eventually,
    "until_left": lambda e: Until(e, Z),
    "until_right": lambda e: Until(Z, e),
    "historically": Historically,
    "once": Once,
    "previous": Previous,
    "since_left": lambda e: Since(e, Z),
    "since_right": lambda e: Since(Z, e),
    "announce_announcement": lambda e: Announce(e, Z),
    "announce_body": lambda e: Announce(Z, e),
    "announce_diamond_announcement": lambda e: AnnounceDiamond(e, Z),
    "announce_diamond_body": lambda e: AnnounceDiamond(Z, e),
    "everybody_knows": lambda e: EverybodyKnows((Constant("a"),), e),
    "distributed_knowledge": lambda e: DistributedKnowledge((Constant("a"),), e),
    "common_knowledge": lambda e: CommonKnowledge((Constant("a"),), e),
    "forall": lambda e: Quantifier("∀", Variable("x"), e),     # an opaque literal here
    "exists": lambda e: Quantifier("∃", Variable("x"), e),
    "sorted_forall": lambda e: SortedQuantifier("∀", Variable("x"), "S", e),
    "deep": lambda e: Box(Diamond(And(Z, Or(Not(Z), Knows(Constant("a"), e))))),
}


@pytest.mark.parametrize("name", sorted(_WRAPPERS))
def test_equality_atom_is_refused_wherever_it_sits(name):
    """Control: the wrapper around an ordinary atom is decided (a verdict, no
    refusal). Then the very same wrapper around ``a = b`` / ``a ≠ b`` is refused."""
    wrap = _WRAPPERS[name]
    assert modal_decide(wrap(Z)) in ("valid", "invalid", "unknown")        # control
    with pytest.raises(NotImplementedError, match=_REFUSAL):
        modal_decide(wrap(EQ))
    with pytest.raises(NotImplementedError, match=r"disequality atom.*" + _REFUSAL):
        modal_decide(wrap(NEQ))


def test_equality_refusal_names_the_atom_the_route_and_where_to_go():
    with pytest.raises(NotImplementedError) as info:
        is_modal_valid(Box(EQ))
    msg = str(info.value)
    assert msg.startswith("modal_tableau:")        # the module's own refusal style
    # the atom, by name: its text is 'a' = 'b' (each constant a single letter, so written in
    # quotes), shown by repr, which uses double quotes for a text that holds single quotes
    assert "\"'a' = 'b'\"" in msg and "'='" in msg
    assert "equality atom" in msg
    assert "propositional modal tableau" in msg     # the route that refuses
    assert "fol.qml.qml_is_valid" in msg and "rigid identity" in msg
    assert "first-order" in msg
    with pytest.raises(NotImplementedError) as info:
        is_modal_valid(NEQ)
    assert "disequality" in str(info.value) and "'≠'" in str(info.value)


# Skeletons the tableau decides WITHOUT examining the atom inside them. A lazy check
# at the Atom case would let each of these return a verdict that never looked at it.
# Each row is (wrapper, hand-derived verdict of the same wrapper around the ordinary
# atom Z over K):
_SKELETON_DECIDED = {
    # ¬((p ∧ ¬p) → _) = (p ∧ ¬p) ∧ ¬_ : the branch closes on p / ¬p, never reaching _
    "closes_on_unrelated_contradiction": (lambda e: Implies(And(p, Not(p)), e), "valid"),
    # ¬((p ∨ ¬p) ∨ _) : the ¬(p ∨ ¬p) conjunct is refuted by the p / ¬p pair alone
    "tautologous_disjunct": (lambda e: Or(Or(p, Not(p)), e), "valid"),
    # ¬(□_ → □_) : □_ and ¬□_ at world 0 are complementary, whatever _ is
    "box_against_itself": (lambda e: Implies(Box(e), Box(e)), "valid"),
    # □_ → ¬◇¬_ : the □/◇ duality, a fact about the skeleton
    "box_diamond_duality": (lambda e: Implies(Box(e), Not(Diamond(Not(e)))), "valid"),
    # □_ → □(p ∨ ¬p) : the necessitated tautology; the premise □_ is never used
    "necessitated_tautology": (lambda e: Implies(Box(e), Box(Or(p, Not(p)))), "valid"),
    # ¬□(_ ∨ ¬_) : □(…) is valid in K, so this is INVALID; its single-world counter-model
    # has no successor, so the box is vacuous at the dead end and _ is never examined
    "vacuous_box_at_a_dead_end": (lambda e: Not(Box(Or(e, Not(e)))), "invalid"),
}


@pytest.mark.parametrize("name", sorted(_SKELETON_DECIDED))
def test_equality_refusal_survives_a_verdict_that_never_reaches_the_atom(name):
    wrap, expected = _SKELETON_DECIDED[name]
    assert modal_decide(wrap(Z)) == expected                  # control: decided as derived
    for atom in (EQ, NEQ):
        with pytest.raises(NotImplementedError, match=_REFUSAL):
            modal_decide(wrap(atom))
        with pytest.raises(NotImplementedError, match=_REFUSAL):
            is_modal_valid(wrap(atom))
        with pytest.raises(NotImplementedError, match=_REFUSAL):
            modal_countermodel(wrap(atom))


# Every public entry point, and the routed ones that reach it, refuses at the door:
_ENTRIES = {
    "is_modal_valid": is_modal_valid,
    "modal_decide": modal_decide,
    "modal_countermodel": modal_countermodel,
    "modal_prove, as the conclusion": lambda f: modal_prove([p], f),
    "modal_prove, as a premise": lambda f: modal_prove([f], q),
    "modal_tableau_closed": lambda f: modal_tableau_closed([p, f]),
    "modal_tableau_closed, a generator": lambda f: modal_tableau_closed(g for g in [p, f]),
    "is_valid_tableau (routed)": is_valid_tableau,
    "prove_tableau (routed)": lambda f: prove_tableau([p], f),
}


@pytest.mark.parametrize("entry", sorted(_ENTRIES))
@pytest.mark.parametrize("formula", [
    Box(EQ), Not(Box(NEQ)), Implies(EQ, Box(EQ)), Implies(And(p, Not(p)), Box(EQ)),
], ids=["box", "not-box-neq", "rigidity", "closed-branch"])
def test_every_entry_point_refuses_an_equality_atom(entry, formula):
    with pytest.raises(NotImplementedError, match=_REFUSAL):
        _ENTRIES[entry](formula)


def test_the_refusal_is_the_first_guard_whatever_the_frame_and_systems():
    # a frame the tableau accepts, a system it accepts, and the S5 / KD45 corner:
    # none of them is a way past the scan
    for frame in ("K", "T", "S4", "S5", "KD45"):
        with pytest.raises(NotImplementedError, match=_REFUSAL):
            modal_decide(Implies(EQ, Box(EQ)), frame=frame)
    with pytest.raises(NotImplementedError, match=_REFUSAL):
        modal_decide(Knows(_a, EQ), systems={"epistemic": "S5"})


def test_the_backend_reports_unsupported_not_a_verdict():
    """The portfolio's tableau backend turns the refusal into UNKNOWN/unsupported, so
    the chain moves on to a route that DOES interpret identity instead of an
    ``invalid`` / ``unknown`` read off a propositional letter."""
    from unicode_logic_kit.atp.protocol import ModalTableauBackend, UNKNOWN
    for f in (Implies(EQ, Box(EQ)), EQ, Implies(Box(NEQ), NEQ)):
        v = ModalTableauBackend().decide(f)
        assert v.status == UNKNOWN and v.reason == "unsupported", f.to_unicode_str()
        assert "qml_is_valid" in v.detail


def test_the_default_modal_chain_reaches_a_route_that_reads_identity():
    """End to end: ``a = b → □(a = b)`` is valid under rigid identity. The tableau
    refuses it; the chain's identity-aware route (qml) proves it."""
    from unicode_logic_kit import api
    from unicode_logic_kit.atp.protocol import PROVED
    v = api.prove(Implies(EQ, Box(EQ)))
    assert v.status == PROVED and v.backend != "modal-tableau"


def test_other_infix_and_predicate_atoms_are_still_ordinary_letters():
    """Only '=' / '≠' are refused: '<', '≤', and a predicate with arguments are
    propositional letters here exactly as before."""
    lt = Atom("<", (_a, _b))
    le = Atom("≤", (_a, _b))
    pa = Atom("P", (_a,))
    assert modal_decide(Implies(Box(lt), lt), "T") == "valid"      # T axiom, any letter
    assert modal_decide(Implies(Box(lt), lt)) == "invalid"         # not in K
    assert modal_decide(Implies(pa, Box(pa))) == "invalid"
    assert modal_decide(Implies(Box(le), le), "S5") == "valid"
    # ... and a predicate merely NAMED like a keyword is not the identity atom
    eq_named = Atom("eq", (_a, _b))
    assert modal_decide(Implies(Box(eq_named), eq_named), "T") == "valid"


# The shared helper itself (semantics/_modal_reject.py) ----------------------------

def test_reject_equality_is_check_and_raise_by_name():
    assert EQUALITY_PREDICATES == ("=", "≠")
    for ok in (Z, Atom("<", (_a, _b)), Atom("P", (_a,)), _a, Not(EQ)):
        assert reject_equality(ok, "somewhere") is None      # not an identity atom itself
    assert is_equality_atom(EQ) and is_equality_atom(NEQ) and not is_equality_atom(Z)
    # by NAME, whatever the arity: a malformed identity atom is refused, not skipped
    for odd in (Atom("=", ()), Atom("=", (_a,)), Atom("≠", (_a, _b, _a))):
        with pytest.raises(NotImplementedError, match="refused by name"):
            reject_equality(odd, "somewhere")


def test_reject_equality_in_scans_the_whole_tree():
    deep = Box(Or(Z, Not(Diamond(And(Z, Knows(_a, EQ))))))
    with pytest.raises(NotImplementedError, match=r"^somewhere: the equality atom"):
        reject_equality_in(deep, "somewhere")
    assert reject_equality_in(Box(Or(Z, Diamond(Z))), "somewhere") is None


def test_reject_equality_message_is_parameterised_by_route():
    with pytest.raises(NotImplementedError) as info:
        reject_equality(EQ, "my_entry", "some other route", atom_reading="it does X",
                        instead="Go elsewhere.")
    msg = str(info.value)
    assert msg.startswith("my_entry: the equality atom \"'a' = 'b'\" ('=') is refused by name")
    assert "equality is not interpreted by some other route." in msg
    assert "(it does X)" in msg and msg.endswith("Go elsewhere.")


def test_reject_equality_default_message_is_the_kripke_evaluators():
    """With no route given the helper speaks for the Kripke evaluator, so
    ``satisfies_modal`` (which keeps its own copy until it switches to this one) and
    the helper give the same refusal word for word."""
    model = KripkeModel(worlds={0})
    for atom in (EQ, NEQ):
        with pytest.raises(NotImplementedError) as from_kripke:
            satisfies_modal(Box(atom), model, 0)
        with pytest.raises(NotImplementedError) as from_helper:
            reject_equality(atom, "satisfies_modal")
        assert str(from_helper.value) == str(from_kripke.value)
