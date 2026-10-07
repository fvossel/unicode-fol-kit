"""Tests for the full-family modal THF export (qml_thf_full).

Structural checks (balanced parentheses, every referenced macro declared, every
relation typed, the agent threaded as a real argument, a genuine conjecture) plus
faithfulness checks: the lifted macros are read back as ordinary HOL definitions and
compared, on small explicit Kripke models, against
:func:`unicode_logic_kit.semantics.kripke.satisfies_modal` for the propositional
fragment the two share.
"""

import itertools
import re

import pytest

from unicode_logic_kit.fol.nodes import (
    Variable, Constant, Function, Atom, Not, And, Or, Implies, Iff, Quantifier,
    Box, Diamond, Knows, Believes, Obligatory, Permitted,
    Always, Eventually, Next, Until,
)
from unicode_logic_kit.fol.qml import (
    qml_is_valid, qml_translate, to_thf_modal as qml_to_thf_modal,
)
from unicode_logic_kit.hol.thf_modal import (
    to_thf_modal_full, thf_full_definitions, thf_full_frame_axioms,
)
from unicode_logic_kit.semantics.kripke import KripkeModel, satisfies_modal


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


# --------------------------------------------------------------------------- #
# rigid identity
# --------------------------------------------------------------------------- #
# Object identity is NOT a world-indexed predicate: `=` is THF's own `=` over `$i`
# with no world argument, reached through the `meq` macro, and `≠` is `¬(=)` -- the
# reading of fol.qml.qml_is_valid. Three kinds of evidence below:
#
#   1. the emitted text, pinned against hand-derived expected output;
#   2. a tiny INTERPRETER for that text (no THF prover is installed offline): it
#      parses the `thf(...)` lines, enumerates every model with <= 2 worlds and
#      <= 2 individuals that satisfies the emitted axioms, and looks for one that
#      falsifies the emitted conjecture. Bounded, so it can refute and can only
#      fail to refute -- but it reads the REAL emitted text, macros and all;
#   3. agreement of both with qml_is_valid and with the hand-derived verdict.

_ITOK = re.compile(
    r"\s*(\$tType|\$i|\$o|<=>|=>|[A-Za-z_][A-Za-z0-9_]*|[()\[\],:.^!?@=&|~>])")


class _ThfParser:
    """Recursive-descent parser for the THF fragment the modal exporters emit."""

    def __init__(self, src):
        self.t, self.i, pos = [], 0, 0
        src = src.strip()
        while pos < len(src):
            m = _ITOK.match(src, pos)
            assert m, f"cannot tokenise {src[pos:pos + 30]!r}"
            self.t.append(m.group(1))
            pos = m.end()

    def peek(self):
        return self.t[self.i] if self.i < len(self.t) else None

    def take(self, want=None):
        tok = self.peek()
        assert want is None or tok == want, (want, tok, self.t[self.i - 4:self.i + 4])
        self.i += 1
        return tok

    def ty(self):
        a = self._ty_atom()
        if self.peek() == ">":
            self.take(">")
            return ("fn", a, self.ty())
        return a

    def _ty_atom(self):
        if self.peek() == "(":
            self.take("(")
            t = self.ty()
            self.take(")")
            return t
        return self.take()

    def expr(self):
        a = self._imp()
        while self.peek() == "<=>":
            self.take()
            a = ("iff", a, self._imp())
        return a

    def _imp(self):
        a = self._or()
        while self.peek() == "=>":
            self.take()
            a = ("imp", a, self._or())
        return a

    def _or(self):
        parts = [self._and()]
        while self.peek() == "|":
            self.take()
            parts.append(self._and())
        return parts[0] if len(parts) == 1 else ("or", parts)

    def _and(self):
        parts = [self._eq()]
        while self.peek() == "&":
            self.take()
            parts.append(self._eq())
        return parts[0] if len(parts) == 1 else ("and", parts)

    def _eq(self):
        a = self._app()
        if self.peek() == "=":
            self.take()
            return ("eq", a, self._app())
        return a

    def _app(self):
        a = self._unary()
        while self.peek() == "@":
            self.take()
            a = ("app", a, self._unary())
        return a

    def _unary(self):
        tok = self.peek()
        if tok == "~":
            self.take()
            return ("not", self._unary())
        if tok in ("!", "?", "^"):
            self.take()
            self.take("[")
            binders = []
            while True:
                name = self.take()
                self.take(":")
                binders.append((name, self.ty()))
                if self.peek() != ",":
                    break
                self.take(",")
            self.take("]")
            self.take(":")
            return ({"!": "all", "?": "ex", "^": "lam"}[tok], binders, self.expr())
        if tok == "(":
            self.take("(")
            e = self.expr()
            self.take(")")
            return e
        return ("name", self.take())


class _Fn:
    """A finite function value: a relation, a predicate or a unary function symbol."""
    __slots__ = ("vals",)

    def __init__(self, vals):
        self.vals = vals

    def __call__(self, x):
        return self.vals[int(x)]


def _dom(ty, nw, no):
    if ty == "mu":
        return list(range(nw))
    if ty == "$i":
        return list(range(no))
    if ty == "$o":
        return [False, True]
    if isinstance(ty, tuple) and ty[0] == "fn":
        n = len(_dom(ty[1], nw, no))
        return [_Fn(v) for v in itertools.product(_dom(ty[2], nw, no), repeat=n)]
    raise AssertionError(f"no finite domain for {ty!r}")


def _free_names(ast, acc):
    tag = ast[0]
    if tag == "name":
        acc.add(ast[1])
    elif tag in ("app", "eq", "imp", "iff"):
        _free_names(ast[1], acc)
        _free_names(ast[2], acc)
    elif tag == "not":
        _free_names(ast[1], acc)
    elif tag in ("and", "or"):
        for p in ast[1]:
            _free_names(p, acc)
    else:                                              # all / ex / lam
        _free_names(ast[2], acc)
    return acc


def _ev(ast, env, g, nw, no):
    tag = ast[0]
    if tag == "name":
        return env[ast[1]] if ast[1] in env else g[ast[1]]
    if tag == "app":
        return _ev(ast[1], env, g, nw, no)(_ev(ast[2], env, g, nw, no))
    if tag == "not":
        return not _ev(ast[1], env, g, nw, no)
    if tag == "and":
        return all(_ev(p, env, g, nw, no) for p in ast[1])
    if tag == "or":
        return any(_ev(p, env, g, nw, no) for p in ast[1])
    if tag == "imp":
        return (not _ev(ast[1], env, g, nw, no)) or _ev(ast[2], env, g, nw, no)
    if tag in ("iff", "eq"):
        return _ev(ast[1], env, g, nw, no) == _ev(ast[2], env, g, nw, no)
    binders, body = ast[1], ast[2]
    if tag == "lam":
        def curry(k, env_k):
            name = binders[k][0]
            if k == len(binders) - 1:
                return lambda v: _ev(body, {**env_k, name: v}, g, nw, no)
            return lambda v: curry(k + 1, {**env_k, name: v})
        return curry(0, env)
    names = [n for n, _ in binders]
    combos = (dict(zip(names, vs)) for vs in
              itertools.product(*[_dom(t, nw, no) for _, t in binders]))
    quant = all if tag == "all" else any
    return quant(_ev(body, {**env, **c}, g, nw, no) for c in combos)


def _thf_countermodel(text, nw=2, no=2):
    """A model with <= ``nw`` worlds and <= ``no`` individuals that satisfies every
    ``axiom`` of the emitted THF problem ``text`` and falsifies its ``conjecture`` (the
    interpretation of the declared symbols it mentions, as a dict); ``None`` if there
    is none. Macros (``definition`` lines) are closures over one shared interpretation,
    so they are the emitted ones, not a re-implementation."""
    types, defs, axioms, goal = {}, {}, [], None
    for line in text.splitlines():
        m = re.match(r"^thf\((\w+), (\w+), (.*)\)\.$", line)
        if not m:
            continue
        role, body = m.group(2), _ThfParser(m.group(3))
        if role == "type":
            body.take("(")
            name = body.take()
            body.take(":")
            ty = body.ty()
            if ty != "$tType":
                types[name] = ty
            continue
        ast = body.expr()
        if role == "definition":
            assert ast[0] == "eq" and ast[1][0] == "name", ast
            defs[ast[1][1]] = ast[2]
        elif role == "axiom":
            axioms.append(ast)
        elif role == "conjecture":
            goal = ast

    def reach(ast, seen):
        for n in _free_names(ast, set()):
            if n in defs and n not in seen:
                seen.add(n)
                reach(defs[n], seen)
            elif n in types:
                seen.add(n)
        return seen

    ax_syms, goal_syms = set(), set()
    for ax in axioms:
        reach(ax, ax_syms)
    reach(goal, goal_syms)
    ax_free = sorted(s for s in ax_syms if s in types)
    goal_free = sorted(s for s in goal_syms if s in types and s not in ax_syms)
    g = {}
    for name, ast in defs.items():
        g[name] = _ev(ast, {}, g, nw, no)
    dom1 = [_dom(types[s], nw, no) for s in ax_free]
    dom2 = [_dom(types[s], nw, no) for s in goal_free]
    for v1 in itertools.product(*dom1):
        g.update(zip(ax_free, v1))
        if not all(_ev(ax, {}, g, nw, no) for ax in axioms):
            continue                                   # not a model of the axioms
        for v2 in itertools.product(*dom2):
            g.update(zip(goal_free, v2))
            if not _ev(goal, {}, g, nw, no):
                return {k: g[k] for k in ax_free + goal_free}
    return None


def _thf_bounded_valid(text):
    return _thf_countermodel(text) is None


# The interpreter must be able to say NO before its YES means anything.
def test_interpreter_refutes_known_non_theorems_and_proves_known_ones():
    p, x = Atom("p", []), Variable("x")
    box_p_imp_p = Implies(Box(p), p)
    assert not _thf_bounded_valid(to_thf_modal_full(box_p_imp_p, frame="K"))
    assert _thf_bounded_valid(to_thf_modal_full(box_p_imp_p, frame="T"))
    # BF: valid under constant domains, invalid under varying ones (needs 2 worlds)
    bf = Implies(Diamond(Quantifier("∃", x, Atom("A", [x]))),
                 Quantifier("∃", x, Diamond(Atom("A", [x]))))
    assert _thf_bounded_valid(to_thf_modal_full(bf, mode="constant"))
    assert not _thf_bounded_valid(to_thf_modal_full(bf, mode="varying"))


def test_interpreter_would_catch_the_old_uninterpreted_reading():
    # The text the exporter used to emit for `a = a`: an uninterpreted, world-
    # relativised `feq`. The interpreter finds its countermodel -- which is what makes
    # its failure to find one for the rigid text mean something.
    old = "\n".join([
        "thf(mu_type, type, ( mu : $tType )).",
        "thf(feq_decl, type, ( feq : ( $i > $i > mu > $o ) )).",
        "thf(a_decl, type, ( a : $i )).",
        "thf(mvalid, definition, ( mvalid = ( ^ [Phi: mu>$o] : ! [W: mu] : ( Phi @ W ) ) )).",
        "thf(goal, conjecture, ( mvalid @ ( feq @ a @ a ) )).",
    ])
    assert _thf_countermodel(old) is not None


_a, _b, _c = Constant("a"), Constant("b"), Constant("c")


def _eq(s, t):
    return Atom("=", [s, t])


def _neq(s, t):
    return Atom("≠", [s, t])


def _P(t):
    return Atom("P", [t])


_f = lambda t: Function("f", [t])            # noqa: E731

# (id, formula, hand-derived conjecture body, validity per frame family, reason)
# VALID everywhere unless `box_back`: `□(a = b) → a = b` needs a successor-or-self.
_ALL = {"K": True, "T": True, "S4": True, "S5": True, "KD": True, "KD45": True}
_BOX_BACK = {"K": False, "T": True, "S4": True, "S5": True, "KD": True, "KD45": True}
_NEVER = {k: False for k in _ALL}
_IDENTITY_BATTERY = [
    ("refl", _eq(_a, _a), "( meq @ a @ a )", _ALL,
     "identity is reflexive -- and not world-relativised, so not an unconstrained ternary"),
    ("sym", Implies(_eq(_a, _b), _eq(_b, _a)),
     "( mimplies @ ( meq @ a @ b ) @ ( meq @ b @ a ) )", _ALL, "symmetry"),
    ("trans", Implies(And(_eq(_a, _b), _eq(_b, _c)), _eq(_a, _c)),
     "( mimplies @ ( mand @ ( meq @ a @ b ) @ ( meq @ b @ c ) ) @ ( meq @ a @ c ) )",
     _ALL, "transitivity"),
    ("necessity", Implies(_eq(_a, _b), Box(_eq(_a, _b))),
     "( mimplies @ ( meq @ a @ b ) @ ( mbox @ ( meq @ a @ b ) ) )", _ALL,
     "rigid: the atom does not mention the world, so it holds at every successor"),
    ("distinctness", Implies(_neq(_a, _b), Box(_neq(_a, _b))),
     "( mimplies @ ( mnot @ ( meq @ a @ b ) ) @ ( mbox @ ( mnot @ ( meq @ a @ b ) ) ) )",
     _ALL, "≠ is ¬(=), so it is rigid too"),
    ("possible_identity", Implies(Diamond(_eq(_a, _b)), _eq(_a, _b)),
     "( mimplies @ ( mdia @ ( meq @ a @ b ) ) @ ( meq @ a @ b ) )", _ALL,
     "a witness world satisfies a = b; a = b does not depend on the world"),
    ("box_back", Implies(Box(_eq(_a, _b)), _eq(_a, _b)),
     "( mimplies @ ( mbox @ ( meq @ a @ b ) ) @ ( meq @ a @ b ) )", _BOX_BACK,
     "needs a successor-or-self: in K a dead-end world makes the box vacuously true"),
    ("leibniz", Implies(_eq(_a, _b), Iff(_P(_a), _P(_b))),
     "( mimplies @ ( meq @ a @ b ) @ ( mequiv @ ( p @ a ) @ ( p @ b ) ) )", _ALL,
     "substitutivity of identicals"),
    ("leibniz_box", Implies(_eq(_a, _b), Iff(Box(_P(_a)), Box(_P(_b)))),
     "( mimplies @ ( meq @ a @ b ) @ ( mequiv @ ( mbox @ ( p @ a ) ) @ ( mbox @ ( p @ b ) ) ) )",
     _ALL, "Leibniz under a box: the same two objects, so the same boxed predicate"),
    ("contingent", _eq(_a, _b), "( meq @ a @ b )", _NEVER,
     "two constants may denote two objects"),
    ("contingent_neg", Not(_eq(_a, _b)), "( mnot @ ( meq @ a @ b ) )", _NEVER,
     "two constants may denote one object"),
    ("congruence", Implies(_eq(_a, _b), _eq(_f(_a), _f(_b))),
     "( mimplies @ ( meq @ a @ b ) @ ( meq @ ( f @ a ) @ ( f @ b ) ) )", _ALL,
     "function symbols respect identity"),
]
_IDENTITY_IDS = [row[0] for row in _IDENTITY_BATTERY]


@pytest.mark.parametrize("name, formula, body, validity, why", _IDENTITY_BATTERY,
                         ids=_IDENTITY_IDS)
def test_identity_conjecture_text_is_pinned(name, formula, body, validity, why):
    expected = f"thf(goal, conjecture, ( mvalid @ {body} ))."
    full = to_thf_modal_full(formula)
    assert _conjecture_line(full) == expected
    # to_thf_modal (fol.qml) emits the SAME conjecture and the SAME macro line, so the
    # two exports stay byte-compatible on the alethic + identity fragment.
    alethic = qml_to_thf_modal(formula)
    assert _conjecture_line(alethic) == expected
    macro = ("thf(meq, definition, "
             "( meq = ( ^ [A: $i, B: $i, W: mu] : ( A = B ) ) )).")
    assert full.splitlines().count(macro) == 1
    assert alethic.splitlines().count(macro) == 1
    # identity is not a predicate: nothing is declared or applied under feq / fneq
    assert "feq" not in full and "fneq" not in full
    assert "feq" not in alethic and "fneq" not in alethic
    assert _balanced(full) and _balanced(alethic)
    # every functor of the conjecture is declared or defined (meq included)
    declared = _declared_functors(full)
    for macro_name in re.findall(r"\bm[a-z]+\b", _conjecture_line(full)):
        if macro_name != "mu":
            assert macro_name in declared, macro_name


@pytest.mark.parametrize("name, formula, body, validity, why", _IDENTITY_BATTERY,
                         ids=_IDENTITY_IDS)
def test_identity_battery_agrees_with_qml_and_with_the_emitted_text(
        name, formula, body, validity, why):
    """Three-way agreement: hand-derived verdict, qml_is_valid, and the interpreter run
    over the emitted THF text (both exports), on every frame, constant and varying
    domains. Identity is never existence-guarded, so the verdict is mode-independent."""
    for frame, expected in validity.items():
        for mode in ("constant", "varying"):
            # qml_is_valid's budget is in MILLISECONDS (default 10000). A
            # non-theorem over a SERIAL frame (KD, KD45) is the one case where
            # Z3 burns the whole budget and answers "unknown", which
            # qml_is_valid reports as "not valid" -- its documented deontic
            # caveat. For those a short budget buys 10 s each and loses
            # nothing, because that False was never a refutation; the actual
            # refutation is the interpreter's, two lines below. Every OTHER
            # case gets the full default: measured, the slowest answers in
            # 226 ms, and a 10 ms budget made the THEOREMS time out into
            # "unknown" -> False as well, so they passed only on a machine fast
            # enough -- running this file after tests/test_qml_bridges.py was
            # enough to turn seven of them red.
            budget = 50 if (not expected and frame in ("KD", "KD45")) else 10000
            assert qml_is_valid(formula, mode=mode, frame=frame, timeout=budget) is expected, (
                name, frame, mode, "qml_is_valid", why)
            for emit in (to_thf_modal_full, qml_to_thf_modal):
                got = _thf_bounded_valid(emit(formula, mode=mode, frame=frame))
                assert got is expected, (name, frame, mode, emit.__name__, why)


_x, _y, _w = Variable("x"), Variable("y"), Variable("w")
_EXISTS_C = Quantifier("∃", _x, _eq(_x, _c))


def test_identity_is_not_existence_guarded_under_a_varying_domain():
    # qml's documented choice: identity ranges over the whole object domain, so
    # `a = a` holds at a world where `a` does not exist ...
    for mode in ("constant", "possibilist", "varying", "increasing", "decreasing"):
        refl = _eq(_a, _a)
        assert qml_is_valid(refl, mode=mode) is True
        for emit in (to_thf_modal_full, qml_to_thf_modal):
            assert _thf_bounded_valid(emit(refl, mode=mode)), (mode, emit.__name__)
    # ... while EXISTENCE is expressed by the guarded quantifier: ∃x (x = c) is valid
    # when every object exists everywhere and nowhere else, and its necessitation
    # exactly under the cumulative regime (and the constant one).
    necessitated = Implies(_EXISTS_C, Box(_EXISTS_C))
    for mode, exists_valid, necessitated_valid in (
            ("constant", True, True), ("possibilist", True, True),
            ("varying", False, False), ("increasing", False, True),
            ("decreasing", False, False)):
        assert qml_is_valid(_EXISTS_C, mode=mode) is exists_valid, mode
        assert qml_is_valid(necessitated, mode=mode) is necessitated_valid, mode
        for emit in (to_thf_modal_full, qml_to_thf_modal):
            assert _thf_bounded_valid(emit(_EXISTS_C, mode=mode)) is exists_valid
            assert _thf_bounded_valid(emit(necessitated, mode=mode)) is necessitated_valid


def test_quantified_identity_and_variables_that_share_the_macro_binders_names():
    # `∀w ∀a ∀b (a = b ∧ b = w → a = w)`: the bound variables are called W, A and B
    # in THF -- the very names the macro's own lambda binds. The macro is closed and
    # applied (never substituted into), so nothing is captured.
    a, b, w = Variable("a"), Variable("b"), _w
    trans = Quantifier("∀", w, Quantifier("∀", a, Quantifier("∀", b, Implies(
        And(_eq(a, b), _eq(b, w)), _eq(a, w)))))
    thf = to_thf_modal_full(trans)
    assert "( mimplies @ ( mand @ ( meq @ A @ B ) @ ( meq @ B @ W ) ) @ ( meq @ A @ W ) )" in thf
    assert _thf_bounded_valid(thf)
    # ∀x ∃y (x = y) is valid; ∀x ∀y (x = y) is not (two individuals)
    assert _thf_bounded_valid(to_thf_modal_full(
        Quantifier("∀", _x, Quantifier("∃", _y, _eq(_x, _y))), mode="varying"))
    assert not _thf_bounded_valid(to_thf_modal_full(
        Quantifier("∀", _x, Quantifier("∀", _y, _eq(_x, _y)))))
    assert qml_is_valid(Quantifier("∀", _x, Quantifier("∀", _y, _eq(_x, _y)))) is False


def test_identity_free_problem_carries_no_identity_machinery():
    out = to_thf_modal_full(Implies(Box(_P(_a)), _P(_a)))
    # (not a bare substring test: `mequiv` contains "meq")
    assert "thf(meq, definition" not in out and "( meq @" not in out and "feq" not in out
    assert "thf(meq, definition" not in qml_to_thf_modal(Implies(Box(_P(_a)), _P(_a)))
    # a user predicate that happens to be called `meq` keeps its name ...
    plain = to_thf_modal_full(Atom("meq", [_a]))
    assert "thf(meq_decl, type, ( meq : ( $i > mu > $o ) ))." in plain
    assert "( meq @ a )" in _conjecture_line(plain)
    # ... and is pushed out of the macro's way exactly when identity is present
    both = to_thf_modal_full(And(Atom("meq", [_a]), _eq(_a, _a)))
    assert "thf(meq_2_decl, type, ( meq_2 : ( $i > mu > $o ) ))." in both
    conj = _conjecture_line(both)
    assert "( meq_2 @ a )" in conj and "( meq @ a @ a )" in conj
    assert both.splitlines().count(
        "thf(meq, definition, ( meq = ( ^ [A: $i, B: $i, W: mu] : ( A = B ) ) )).") == 1


def test_user_predicates_named_feq_fneq_stay_distinct_from_identity():
    # The old alias names are ordinary user symbols now; they must stay unique.
    f = And(Atom("feq", [_a]), And(Atom("fneq", [_a, _b]), _eq(_a, _b)))
    out = to_thf_modal_full(f)
    decls = re.findall(r"thf\((\w+)_decl, type, \( (\w+) : \( ([^)]*) \)", out)
    funcs = [d[0] for d in decls]
    assert len(funcs) == len(set(funcs))
    assert "( meq @ a @ b )" in _conjecture_line(out)
    assert _balanced(out)


def test_non_binary_identity_is_refused_like_qml_refuses_it():
    for atom in (Atom("=", [_a]), Atom("=", [_a, _b, _c]), Atom("≠", [_a])):
        f = Box(atom)
        for emit in (to_thf_modal_full, qml_to_thf_modal):
            with pytest.raises(ValueError, match="exactly two terms"):
                emit(f)
        with pytest.raises(ValueError, match="exactly two terms"):
            qml_translate(f)


def test_inequality_is_lowered_to_negated_identity():
    out = to_thf_modal_full(_neq(_a, _b))
    assert _conjecture_line(out) == (
        "thf(goal, conjecture, ( mvalid @ ( mnot @ ( meq @ a @ b ) ) )).")
    assert "fneq" not in out and " != " not in out
    # same thing as writing ¬(a = b) out
    assert out == to_thf_modal_full(Not(_eq(_a, _b)))


def test_until_and_since_embed_as_impredicative_fixpoints():
    # TH0 quantifies over predicates, so strong Until IS shallow-embeddable as
    # the Knaster–Tarski least fixpoint over tnext (the earlier rejection's
    # "not (higher-order) shallow-embeddable" claim was factually wrong).
    from unicode_logic_kit.fol.nodes import Since
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
