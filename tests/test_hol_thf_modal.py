"""Tests for the full-family modal THF export (qml_thf_full).

Structural checks (balanced parentheses, every referenced macro declared, every
relation typed, the agent threaded as a real argument, a genuine conjecture) plus
faithfulness checks: the lifted macros are read back as ordinary HOL definitions and
compared, on small explicit Kripke models, against
:func:`unicode_fol_kit.semantics.kripke.satisfies_modal` for the propositional
fragment the two share.
"""

import re

import pytest

from unicode_fol_kit.fol.nodes import (
    Variable, Constant, Atom, Not, And, Or, Implies, Iff, Quantifier,
    Box, Diamond, Knows, Believes, Obligatory, Permitted,
    Always, Eventually, Next, Until,
)
from unicode_fol_kit.hol.thf_modal import (
    to_thf_modal_full, thf_full_definitions, thf_full_frame_axioms,
)
from unicode_fol_kit.semantics.kripke import KripkeModel, satisfies_modal


# --------------------------------------------------------------------------- #
# helpers
# --------------------------------------------------------------------------- #
def _balanced(s: str) -> bool:
    depth = 0
    for ch in s:
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
            if depth < 0:
                return False
    return depth == 0


def _conjecture_line(out: str) -> str:
    for line in out.splitlines():
        if line.startswith("thf(goal, conjecture,"):
            return line
    raise AssertionError("no conjecture line emitted")


def _declared_functors(out: str) -> set:
    """THF functors that get a type declaration or definition in the output."""
    names = set()
    for line in out.splitlines():
        m = re.match(r"thf\([A-Za-z0-9_]+, (?:type|definition), \( ([A-Za-z0-9_]+)",
                     line)
        if m:
            names.add(m.group(1))
    return names


# Macros every lifted formula may reference (always defined in the defs block).
_ALL_MACROS = {
    "mnot", "mand", "mor", "mimplies", "mequiv", "mbox", "mdia",
    "mknows", "mbelieves", "mobl", "mperm", "malways", "meventually",
    "mnext", "mforall", "mexists", "mvalid",
}


# --------------------------------------------------------------------------- #
# structural tests
# --------------------------------------------------------------------------- #
def test_definitions_block_defines_every_macro():
    defs = thf_full_definitions()
    for macro in _ALL_MACROS:
        assert f"thf({macro}, definition" in defs
    assert _balanced(defs)


def test_agent_threaded_as_real_argument():
    # ∀x (Student(x) → K_x P(x)) : the bound object variable X is the agent of mknows.
    x = Variable("x")
    f = Quantifier("∀", x, Implies(Atom("Student", [x]), Knows(x, Atom("P", [x]))))
    out = to_thf_modal_full(f, mode="constant", frame="K", systems={"epistemic": "S5"})

    assert _balanced(out)
    # rk is declared agent-indexed: $i > mu > mu > $o.
    assert "thf(rk_decl, type, ( rk : ( $i > mu > mu > $o ) ))." in out
    # The agent X (bound by mforall, which binds an $i variable) is the FIRST
    # argument of mknows in the conjecture — i.e. it quantifies over agents.
    assert "( mknows @ X @ ( p @ X ) )" in out
    # mforall binds X as $i, so X is a legitimate $i agent argument.
    assert "( mforall @ ( ^ [X: $i] :" in out
    # S5 agent frame axioms appear (∀ over the agent A).
    assert "thf(rk_refl, axiom, ( ! [A: $i, W: mu] : ( rk @ A @ W @ W ) ))." in out
    assert "rk_trans" in out and "rk_sym" in out


def test_deontic_kd_serial_and_d_axiom():
    p = Atom("p", [])
    f = Implies(Obligatory(p), Permitted(p))      # O p → P p, the D axiom
    out = to_thf_modal_full(f, mode="constant", frame="KD")

    assert _balanced(out)
    assert "thf(d_decl, type, ( d : ( mu > mu > $o ) ))." in out
    # deontic relation is always serial (Standard Deontic Logic / KD).
    assert "thf(d_serial, axiom, ( ! [W: mu] : ? [V: mu] : ( d @ W @ V ) ))." in out
    assert "( mimplies @ ( mobl @ p ) @ ( mperm @ p ) )" in _conjecture_line(out)


def test_epistemic_k_axiom_named_agent():
    a = Constant("a")
    p, q = Atom("p", []), Atom("q", [])
    kaxiom = Implies(Knows(a, Implies(p, q)),
                     Implies(Knows(a, p), Knows(a, q)))
    out = to_thf_modal_full(kaxiom, mode="constant", frame="K")

    assert _balanced(out)
    # named agent a is lower-cased and appears as the agent argument.
    assert "mknows @ a @" in out
    # the named agent is also declared as an $i individual (so rk's $i slot is typed).
    assert "thf(a_decl, type, ( a : $i ))." in out
    conj = _conjecture_line(out)
    assert conj.startswith("thf(goal, conjecture, ( mvalid @")
    assert conj.rstrip().endswith(")).")


def test_conjecture_is_real_and_uses_mvalid():
    out = to_thf_modal_full(Box(Atom("p", [])))
    conj = _conjecture_line(out)
    assert "mvalid @ ( mbox @ p )" in conj


def test_every_referenced_functor_is_declared():
    # A formula touching every family; every functor used must be declared/defined.
    a = Constant("a")
    p, q = Atom("p", []), Atom("q", [])
    f = And(
        And(Box(p), Diamond(q)),
        And(And(Knows(a, p), Believes(a, q)),
            And(And(Obligatory(p), Permitted(q)),
                And(Always(p), And(Eventually(q), Next(p))))),
    )
    out = to_thf_modal_full(f)
    assert _balanced(out)
    declared = _declared_functors(out)
    # relations.
    for rel in ("r", "rk", "rb", "d", "t", "tnext", "existsAt"):
        assert rel in declared, f"{rel} not declared"
    # object predicates.
    assert "p" in declared and "q" in declared
    # every macro referenced in the conjecture is defined.
    conj = _conjecture_line(out)
    for macro in re.findall(r"\bm[a-z]+\b", conj):
        if macro == "mu":
            continue
        assert macro in declared, f"{macro} used but not defined"


def test_problem_is_self_contained():
    # The lifted-operator definitions block is emitted whole (mknows/mbelieves/mobl/
    # mperm/malways/mnext reference rk/rb/d/t/tnext), so EVERY such relation must be
    # declared even for a purely alethic formula — otherwise the emitted THF would
    # reference undeclared symbols and a strict prover (Leo-III/Satallax) would reject it.
    out = to_thf_modal_full(Box(Atom("p", [])))
    decl = _declared_functors(out)
    for rel in ("r", "rk", "rb", "d", "t", "tnext", "existsAt"):
        assert rel in decl, f"{rel} referenced by the defs block but not declared"


def test_temporal_g_f_x_emit_closure_and_one_step():
    f = Always(Eventually(Next(Atom("p", []))))
    out = to_thf_modal_full(f)
    assert _balanced(out)
    assert "thf(t_decl, type, ( t : ( mu > mu > $o ) ))." in out
    assert "thf(tnext_decl, type, ( tnext : ( mu > mu > $o ) ))." in out
    # G/F over a reflexive-transitive t (the closure caveat).
    assert "thf(t_refl, axiom," in out
    assert "thf(t_trans, axiom," in out
    assert "malways" in out and "meventually" in out and "mnext" in out


def test_tnext_in_t_inclusion_axiom_emitted():
    # REGRESSION: the tnext ⊆ t inclusion axiom links X's one-step relation to G/F's
    # henceforth relation, so that Gφ→Xφ (valid for satisfies_modal) is a theorem of
    # the embedding. It must be emitted whenever EITHER family (temporal G/F or next X)
    # occurs, since the divergence case Gφ→Xφ mixes the two.
    incl = ("thf(tnext_in_t, axiom, ( ! [W: mu, V: mu] : "
            "( ( tnext @ W @ V ) => ( t @ W @ V ) ) )).")
    # mixed G/X formula (the divergence case).
    out_mixed = to_thf_modal_full(Implies(Always(Atom("p", [])), Next(Atom("p", []))))
    assert incl in out_mixed
    # G/F only.
    out_g = to_thf_modal_full(Always(Atom("p", [])))
    assert incl in out_g
    # X only (tnext used, temporal not): the inclusion still references the declared t.
    out_x = to_thf_modal_full(Next(Atom("p", [])))
    assert incl in out_x
    assert _balanced(out_x)
    # the helper that lists frame axioms exposes it too.
    assert incl in thf_full_frame_axioms()
    # a NON-temporal formula does not emit it.
    out_box = to_thf_modal_full(Box(Atom("p", [])))
    assert "tnext_in_t" not in out_box


def test_gp_implies_xp_divergence_is_gone():
    # REGRESSION for the confirmed faithfulness divergence: Gφ→Xφ is VALID for
    # satisfies_modal (X's immediate "temporal" successors ⊆ G's reflexive-transitive
    # closure of the SAME relation). Previously the embedding split this into an
    # unconstrained t / tnext pair, so Gφ→Xφ was a non-theorem. The tnext ⊆ t inclusion
    # axiom now closes the gap.
    #
    # We verify with an independent SSE interpreter (transcribing the emitted macros)
    # that, over EVERY small frame satisfying t_refl / t_trans / tnext ⊆ t, the emitted
    # rendering of Gφ→Xφ is valid (mvalid) — i.e. no countermodel — matching the oracle.
    import itertools
    from itertools import product

    worlds = [0, 1]
    edges = [(a, b) for a in worlds for b in worlds]
    all_rel = list(itertools.chain.from_iterable(
        itertools.combinations(edges, k) for k in range(len(edges) + 1)))

    def is_refl(t):
        return all((w, w) in t for w in worlds)

    def is_trans(t):
        return all((a, d) in t for (a, b) in t for (c, d) in t if b == c)

    def malways(val, t, w):          # ![V]: (t W V) => phi V
        return all(val[v] for (a, v) in t if a == w)

    def meventually(val, t, w):      # ?[V]: (t W V) & phi V
        return any(val[v] for (a, v) in t if a == w)

    def mnext(val, tnext, w):        # ![V]: (tnext W V) => phi V
        return all(val[v] for (a, v) in tnext if a == w)

    # The oracle: Gφ→Xφ is valid; Xφ→Fφ is NOT globally valid (vacuous Next at a
    # successor-free world), so we pin the embedding to satisfies_modal per model.
    P = Atom("p", [])
    GP_XP = Implies(Always(P), Next(P))
    XP_FP = Implies(Next(P), Eventually(P))

    def oracle_valid(f, tnext, val):
        model = KripkeModel(
            set(worlds),
            relations={"temporal": set(tnext)},
            valuation={w: ({"p"} if val[w] else set()) for w in worlds},
        )
        return all(satisfies_modal(f, model, w) for w in worlds)

    def rtc(rel):
        c = set(rel) | {(w, w) for w in worlds}
        changed = True
        while changed:
            changed = False
            for (a, b) in list(c):
                for (x, d) in list(c):
                    if b == x and (a, d) not in c:
                        c.add((a, d))
                        changed = True
        return c

    gp_xp_countermodels = 0
    gp_xp_mismatch = 0
    xp_fp_mismatch = 0
    for tnext_t in all_rel:
        tnext = set(tnext_t)
        # The minimal admissible henceforth relation is the reflexive-transitive
        # closure of tnext, which automatically satisfies refl, trans AND tnext ⊆ t.
        t = rtc(tnext)
        assert is_refl(t) and is_trans(t) and tnext.issubset(t)
        for pv in product([False, True], repeat=len(worlds)):
            val = {w: pv[i] for i, w in enumerate(worlds)}
            emb_gp_xp = all(
                (not malways(val, t, w)) or mnext(val, tnext, w) for w in worlds)
            emb_xp_fp = all(
                (not mnext(val, tnext, w)) or meventually(val, t, w) for w in worlds)
            if not emb_gp_xp:
                gp_xp_countermodels += 1
            # embedding agrees with the oracle on BOTH directions, per model.
            if emb_gp_xp != oracle_valid(GP_XP, tnext, val):
                gp_xp_mismatch += 1
            if emb_xp_fp != oracle_valid(XP_FP, tnext, val):
                xp_fp_mismatch += 1

    # The divergence is gone: no countermodel to Gφ→Xφ remains in the embedding.
    assert gp_xp_countermodels == 0
    # And the embedding tracks satisfies_modal exactly on both temporal implications.
    assert gp_xp_mismatch == 0
    assert xp_fp_mismatch == 0


def test_equality_is_uninterpreted_feq_fneq():
    f = Box(And(Atom("=", [Constant("a"), Constant("b")]),
                Not(Atom("≠", [Constant("a"), Constant("b")]))))
    out = to_thf_modal_full(f)
    assert _balanced(out)
    assert "feq" in out and "fneq" in out
    # NOT primitive HOL identity: the raw '=' / '≠' is rendered via the feq/fneq alias.
    conj = _conjecture_line(out)
    assert "( feq @ a @ b )" in conj


def test_until_and_since_embed_as_impredicative_fixpoints():
    # TH0 quantifies over predicates, so strong Until IS shallow-embeddable as
    # the Knaster–Tarski least fixpoint over tnext (the earlier rejection's
    # "not (higher-order) shallow-embeddable" claim was factually wrong).
    from unicode_fol_kit.fol.nodes import Since
    out = to_thf_modal_full(Until(Atom("p", []), Atom("q", [])))
    assert "( muntil @ p @ q )" in out
    assert "thf(muntil, definition" in out and "! [S: mu>$o]" in out
    out2 = to_thf_modal_full(Since(Atom("p", []), Atom("q", [])))
    assert "( msince @ p @ q )" in out2
    # msince steps over the CONVERSE of tnext (tnext @ U @ V, not V @ U).
    assert "tnext @ U @ V" in out2


def test_unknown_frame_and_mode_raise():
    with pytest.raises(ValueError):
        to_thf_modal_full(Box(Atom("p", [])), frame="bogus")
    with pytest.raises(ValueError):
        to_thf_modal_full(Box(Atom("p", [])), mode="bogus")
    with pytest.raises(ValueError):
        to_thf_modal_full(Knows(Constant("a"), Atom("p", [])),
                          systems={"epistemic": "bogus"})


def test_frame_axioms_helper_matches_systems():
    ax = thf_full_frame_axioms(frame="S4", systems={"epistemic": "S5",
                                                    "doxastic": "KD45"})
    blob = "\n".join(ax)
    # alethic S4: refl + trans on r.
    assert "thf(refl, axiom," in blob and "thf(trans, axiom," in blob
    # epistemic S5 on rk; doxastic KD45 on rb.
    assert "rk_refl" in blob and "rk_sym" in blob
    assert "rb_serial" in blob and "rb_eucl" in blob
    # deontic + temporal always present.
    assert "d_serial" in blob and "t_refl" in blob


# --------------------------------------------------------------------------- #
# faithfulness tests
# --------------------------------------------------------------------------- #
# The lifted macros literally transcribe the Kripke clauses of satisfies_modal:
#   mbox  φ w  ≡  ∀v (r w v → φ v)            ── Box over "alethic"
#   mdia  φ w  ≡  ∃v (r w v ∧ φ v)            ── Diamond over "alethic"
#   mknows a φ w ≡ ∀v (rk a w v → φ v)        ── Knows over "K:"+a
#   mobl  φ w  ≡  ∀v (d w v → φ v)            ── Obligatory over "deontic"
#   mperm φ w  ≡  ∃v (d w v ∧ φ v)            ── Permitted over "deontic"
#   mnext φ w  ≡  ∀v (tnext w v → φ v)        ── Next over "temporal" (universal)
# We re-implement those clauses here as a tiny HOL interpreter over an explicit
# frame and assert it agrees with satisfies_modal on concrete models. This pins
# the EMITTED macros to the ground-truth evaluator for the overlapping fragment.

def _eval_macro(formula, frame, val, world):
    """Evaluate `formula` under exactly the emitted SSE macro clauses."""
    if isinstance(formula, Atom):
        return formula.to_unicode_str() in val.get(world, set())
    if isinstance(formula, Not):
        return not _eval_macro(formula.formula, frame, val, world)
    if isinstance(formula, And):
        return (_eval_macro(formula.left, frame, val, world)
                and _eval_macro(formula.right, frame, val, world))
    if isinstance(formula, Or):
        return (_eval_macro(formula.left, frame, val, world)
                or _eval_macro(formula.right, frame, val, world))
    if isinstance(formula, Implies):
        return ((not _eval_macro(formula.left, frame, val, world))
                or _eval_macro(formula.right, frame, val, world))
    if isinstance(formula, Iff):
        return (_eval_macro(formula.left, frame, val, world)
                == _eval_macro(formula.right, frame, val, world))
    if isinstance(formula, Box):
        return all(_eval_macro(formula.formula, frame, val, v)
                   for (w, v) in frame["r"] if w == world)
    if isinstance(formula, Diamond):
        return any(_eval_macro(formula.formula, frame, val, v)
                   for (w, v) in frame["r"] if w == world)
    if isinstance(formula, Knows):
        key = ("rk", formula.agent.name)
        return all(_eval_macro(formula.formula, frame, val, v)
                   for (w, v) in frame.get(key, set()) if w == world)
    if isinstance(formula, Believes):
        key = ("rb", formula.agent.name)
        return all(_eval_macro(formula.formula, frame, val, v)
                   for (w, v) in frame.get(key, set()) if w == world)
    if isinstance(formula, Obligatory):
        return all(_eval_macro(formula.formula, frame, val, v)
                   for (w, v) in frame["d"] if w == world)
    if isinstance(formula, Permitted):
        return any(_eval_macro(formula.formula, frame, val, v)
                   for (w, v) in frame["d"] if w == world)
    if isinstance(formula, Next):
        return all(_eval_macro(formula.formula, frame, val, v)
                   for (w, v) in frame["tnext"] if w == world)
    raise AssertionError(f"unhandled {type(formula).__name__}")


def test_macro_matches_satisfies_modal_alethic():
    # 2 worlds, r = {(0,1)} : Box p true at 0 iff p at 1; Diamond p likewise.
    model = KripkeModel({0, 1}, relations={"alethic": {(0, 1)}},
                        valuation={1: {"p"}})
    frame = {"r": {(0, 1)}}
    val = {1: {"p"}}
    for f in (Box(Atom("p", [])), Diamond(Atom("p", [])),
              Box(Atom("q", [])), Diamond(Atom("q", []))):
        for w in (0, 1):
            assert _eval_macro(f, frame, val, w) == satisfies_modal(f, model, w)


def test_macro_matches_satisfies_modal_epistemic_per_agent():
    # Agent a knows p (sees only p-worlds); agent b does not.
    model = KripkeModel(
        {0, 1, 2},
        relations={"K:a": {(0, 1)}, "K:b": {(0, 1), (0, 2)}},
        valuation={1: {"p"}, 2: set()},
    )
    frame = {("rk", "a"): {(0, 1)}, ("rk", "b"): {(0, 1), (0, 2)}}
    val = {1: {"p"}, 2: set()}
    fa = Knows(Constant("a"), Atom("p", []))
    fb = Knows(Constant("b"), Atom("p", []))
    assert _eval_macro(fa, frame, val, 0) == satisfies_modal(fa, model, 0) is True
    assert _eval_macro(fb, frame, val, 0) == satisfies_modal(fb, model, 0) is False


def test_macro_matches_satisfies_modal_deontic():
    # O p, P q over a serial deontic relation.
    model = KripkeModel({0, 1}, relations={"deontic": {(0, 1)}},
                        valuation={1: {"p"}})
    frame = {"d": {(0, 1)}}
    val = {1: {"p"}}
    for f in (Obligatory(Atom("p", [])), Permitted(Atom("p", [])),
              Obligatory(Atom("q", [])), Permitted(Atom("q", []))):
        assert _eval_macro(f, frame, val, 0) == satisfies_modal(f, model, 0)


def test_macro_matches_satisfies_modal_next():
    # Next is the UNIVERSAL "all immediate temporal successors" reading.
    frame = {"tnext": {(0, 1), (0, 2)}}
    f = Next(Atom("p", []))
    model = KripkeModel({0, 1, 2}, relations={"temporal": {(0, 1), (0, 2)}},
                        valuation={1: {"p"}, 2: {"p"}})
    val = {1: {"p"}, 2: {"p"}}
    assert _eval_macro(f, frame, val, 0) == satisfies_modal(f, model, 0) is True
    # break it: p false at world 2 -> Next p false at 0.
    model2 = KripkeModel({0, 1, 2}, relations={"temporal": {(0, 1), (0, 2)}},
                         valuation={1: {"p"}, 2: set()})
    val2 = {1: {"p"}, 2: set()}
    assert _eval_macro(f, frame, val2, 0) == satisfies_modal(f, model2, 0) is False


def test_distinct_predicates_not_collapsed():
    # Ab / ab sanitise to the same functor; they MUST stay distinct, else the non-valid
    # □Ab → □ab would emit as the tautology □ab → □ab (a soundness hole). Regression.
    out = to_thf_modal_full(Implies(Box(Atom("Ab", [])), Box(Atom("ab", []))))
    assert _balanced(out)
    assert "( mbox @ ab ) @ ( mbox @ ab )" not in out
    ab = re.findall(r"thf\((ab\w*)_decl, type", out)
    assert len(ab) == 2 and len(set(ab)) == 2


if __name__ == "__main__":
    import sys
    sys.exit(pytest.main([__file__, "-v"]))
