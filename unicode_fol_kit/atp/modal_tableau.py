"""Labelled analytic tableaux for the propositional modal family.

The classical :mod:`unicode_fol_kit.atp.tableau` engine has no rule for a modal
operator — a ``Box`` / ``Knows`` / ``Obligatory`` node makes it raise. This module
fills that gap with a **labelled** (world-prefixed) tableau: a branch is a set of
*labelled* formulas ``w: φ`` (worlds are integers) together with the accessibility
edges generated along the way. The propositional / connective rules act at a fixed
world; the modal rules move between worlds:

- ``w: □φ`` (a *box* over its relation) asserts ``v: φ`` at every successor ``v`` of
  ``w`` — and is re-applied whenever a new successor appears;
- ``w: ◇φ`` (a *diamond*) creates a **fresh** successor ``v`` with ``v: φ``;
- a negated box becomes a diamond of the negation and vice versa (``¬□φ ≡ ◇¬φ``).

The box/diamond family handled here is exactly the one with a single accessibility
relation: alethic ``□``/``◇``, epistemic ``K_a``, doxastic ``B_a``, deontic
``O``/``P``, and the one-step temporal ``X`` (``Next``). The relation names match the
:class:`~unicode_fol_kit.semantics.kripke.KripkeModel` convention
(``"alethic"`` / ``"K:"+a`` / ``"B:"+a`` / ``"deontic"`` / ``"temporal"``), so an open
branch is read off directly as a Kripke counter-model. The temporal *closure*
operators ``Always`` (G), ``Eventually`` (F) and ``Until`` need least/greatest-fixpoint
(eventuality) machinery beyond a basic labelled tableau and are rejected with a pointer
to :func:`~unicode_fol_kit.semantics.kripke.satisfies_modal` /
:func:`~unicode_fol_kit.hol.isabelle_runner.isabelle_decide_modal`.

**Frame conditions** are realised as structural rules over the edge set: reflexivity
adds ``w → w`` for every world, symmetry mirrors each edge, transitivity takes the
closure, the euclidean rule closes ``w→v, w→u ⊢ v→u``, and seriality manufactures a
successor for a world that lacks one. The named systems are K, T, D/KD, B/KB, K4, K45,
S4, S5, KD45.

**Soundness vs. completeness.** Every rule preserves satisfiability over its frame
class, so a *closed* tableau is a real proof — ``is_modal_valid`` only returns ``True``
when the tableau closes. Termination on the transitive logics relies on subset
*blocking*, and the whole search is bounded (``max_worlds`` / ``max_steps``); to keep
the *invalid* verdict trustworthy regardless of any blocking/bound effect, an open
branch's model is **verified** with :func:`satisfies_modal` before it is reported, and
a model that fails to falsify the formula downgrades the answer to ``"unknown"`` rather
than risk a wrong ``"invalid"``. The result is the same valid / invalid / unknown
contract as the local-Isabelle runner, but in-process and install-free.

Public API: :func:`modal_tableau_closed`, :func:`is_modal_valid`, :func:`modal_prove`,
:func:`modal_decide`, :func:`modal_countermodel`.
"""

from typing import List, Optional, Tuple

from ..fol.nodes import (
    Node, Atom, Not, And, Or, Xor, Implies, Iff,
    Box, Diamond, Knows, Believes, Obligatory, Permitted,
    Next, Always, Eventually, Until,
    Historically, Once, Previous, Since,
)
from ..semantics.kripke import KripkeModel, satisfies_modal
from .fitch import is_falsum


# Relation names — the contract with semantics.kripke.KripkeModel.
_ALETHIC = "alethic"
_DEONTIC = "deontic"
_TEMPORAL = "temporal"
_KNOWS = "K:"
_BELIEVES = "B:"

# Named modal systems as frame-condition sets (mirrors fol.qml._FRAMES, with the
# extra non-normal-of-T members B/KB/K4/K45 that a tableau handles uniformly).
_FRAMES = {
    "K": (),
    "T": ("refl",),
    "D": ("serial",),
    "KD": ("serial",),
    "B": ("refl", "sym"),
    "KB": ("sym",),
    "K4": ("trans",),
    "K45": ("trans", "eucl"),
    "S4": ("refl", "trans"),
    "S5": ("refl", "trans", "sym"),
    "KD45": ("serial", "trans", "eucl"),
}

# Operators needing least/greatest-fixpoint (eventuality) or converse-relation
# machinery beyond this labelled tableau — routed to satisfies_modal / Isabelle.
_TEMPORAL_CLOSURE = (Always, Eventually, Until, Historically, Once, Previous, Since)


def _agent_key(agent: Node) -> str:
    """Relation-key suffix for an epistemic/doxastic agent term (its name)."""
    return getattr(agent, "name", None) or agent.to_unicode_str()


def _neg(f: Node) -> Node:
    """Return the complementary formula of ``f`` (``¬φ`` ↔ ``φ``)."""
    return f.formula if isinstance(f, Not) else Not(f)


def has_modal(node: Node) -> bool:
    """True iff ``node`` contains any modal/temporal/epistemic/deontic operator."""
    modal = (Box, Diamond, Knows, Believes, Obligatory, Permitted,
             Next, Always, Eventually, Until,
             Historically, Once, Previous, Since)
    return any(isinstance(n, modal) for n in node.walk())


def _decompose(f: Node):
    """Classify a formula for the tableau.

    Returns one of:
      ``("lit",)``                         — atom / negated atom / ⊥ (closure only);
      ``("true",)``                        — ¬⊥ (always true, discard);
      ``("alpha", [comp, …])``             — assert all components at the same world;
      ``("beta", [[…], […]])``             — branch (each list one branch's components);
      ``("box", relname, body)``           — universal modality over ``relname``;
      ``("dia", relname, body)``           — existential modality over ``relname``;
      ``("unsupported", node)``            — a temporal-closure operator (G / F / U).
    """
    if is_falsum(f):
        return ("lit",)
    if isinstance(f, Atom):
        return ("lit",)

    # --- positive modal operators ---
    if isinstance(f, Box):
        return ("box", _ALETHIC, f.formula)
    if isinstance(f, Diamond):
        return ("dia", _ALETHIC, f.formula)
    if isinstance(f, Knows):
        return ("box", _KNOWS + _agent_key(f.agent), f.formula)
    if isinstance(f, Believes):
        return ("box", _BELIEVES + _agent_key(f.agent), f.formula)
    if isinstance(f, Obligatory):
        return ("box", _DEONTIC, f.formula)
    if isinstance(f, Permitted):
        return ("dia", _DEONTIC, f.formula)
    if isinstance(f, Next):
        return ("box", _TEMPORAL, f.formula)
    if isinstance(f, _TEMPORAL_CLOSURE):
        return ("unsupported", f)

    # --- positive connectives ---
    if isinstance(f, And):
        return ("alpha", [f.left, f.right])
    if isinstance(f, Or):
        return ("beta", [[f.left], [f.right]])
    if isinstance(f, Implies):
        return ("beta", [[Not(f.left)], [f.right]])
    if isinstance(f, Iff):
        return ("beta", [[f.left, f.right], [Not(f.left), Not(f.right)]])
    if isinstance(f, Xor):
        return ("beta", [[f.left, Not(f.right)], [Not(f.left), f.right]])

    # --- negations: push through ---
    if isinstance(f, Not):
        g = f.formula
        if is_falsum(g):
            return ("true",)
        if isinstance(g, Atom):
            return ("lit",)
        if isinstance(g, Not):
            return ("alpha", [g.formula])
        if isinstance(g, And):
            return ("beta", [[Not(g.left)], [Not(g.right)]])
        if isinstance(g, Or):
            return ("alpha", [Not(g.left), Not(g.right)])
        if isinstance(g, Implies):
            return ("alpha", [g.left, Not(g.right)])
        if isinstance(g, Iff):
            return ("beta", [[g.left, Not(g.right)], [Not(g.left), g.right]])
        if isinstance(g, Xor):
            return ("beta", [[g.left, g.right], [Not(g.left), Not(g.right)]])
        if isinstance(g, Box):
            return ("dia", _ALETHIC, Not(g.formula))
        if isinstance(g, Diamond):
            return ("box", _ALETHIC, Not(g.formula))
        if isinstance(g, Knows):
            return ("dia", _KNOWS + _agent_key(g.agent), Not(g.formula))
        if isinstance(g, Believes):
            return ("dia", _BELIEVES + _agent_key(g.agent), Not(g.formula))
        if isinstance(g, Obligatory):
            return ("dia", _DEONTIC, Not(g.formula))
        if isinstance(g, Permitted):
            return ("box", _DEONTIC, Not(g.formula))
        if isinstance(g, Next):
            return ("dia", _TEMPORAL, Not(g.formula))
        if isinstance(g, _TEMPORAL_CLOSURE):
            return ("unsupported", f)

    raise NotImplementedError(
        f"modal_tableau: no rule for {type(f).__name__} {f.to_unicode_str()}")


class _Branch:
    """A single open tableau branch: labelled formulas, edges, box obligations."""

    __slots__ = ("tv", "rels", "boxes", "wcount", "expanded")

    def __init__(self):
        self.tv = {0: set()}                 # world -> set of labelled formulas
        self.rels = {}                       # relname -> set of (w, v) edges
        self.boxes = set()                   # (world, relname, body) obligations
        self.wcount = 1                      # next fresh world id
        self.expanded = set()                # (world, formula) already consumed

    def copy(self) -> "_Branch":
        b = _Branch.__new__(_Branch)
        b.tv = {w: set(s) for w, s in self.tv.items()}
        b.rels = {r: set(e) for r, e in self.rels.items()}
        b.boxes = set(self.boxes)
        b.wcount = self.wcount
        b.expanded = set(self.expanded)
        return b


class _Ctx:
    """Search budget and frame configuration shared across the branch tree."""

    def __init__(self, frame: str, systems, max_worlds: int, max_steps: int):
        self.frame = frame
        self.systems = systems or {}
        self.max_worlds = max_worlds
        self.steps = max_steps
        self.exhausted = False

    def tick(self) -> bool:
        self.steps -= 1
        if self.steps <= 0:
            self.exhausted = True
            return False
        return True

    def conds(self, relname: str) -> Tuple[str, ...]:
        """Frame conditions for a relation name, per the configured systems."""
        if relname == _ALETHIC:
            return _FRAMES[self.frame]
        if relname == _DEONTIC:
            return _FRAMES[self.systems.get("deontic", "KD")]
        if relname == _TEMPORAL:
            return _FRAMES[self.systems.get("temporal", "K")]
        if relname.startswith(_KNOWS):
            return _FRAMES[self.systems.get("epistemic", "K")]
        if relname.startswith(_BELIEVES):
            return _FRAMES[self.systems.get("doxastic", "K")]
        return ()


def _assert(b: _Branch, w: int, f: Node) -> bool:
    """Assert ``w: f``; return True iff it was new."""
    s = b.tv.setdefault(w, set())
    if f in s:
        return False
    s.add(f)
    return True


def _closes(b: _Branch) -> bool:
    """True iff some world holds a formula and its negation (or ⊥)."""
    for s in b.tv.values():
        for f in s:
            if is_falsum(f):
                return True
            if _neg(f) in s:
                return True
    return False


def _relnames(b: _Branch):
    """Relation names that are 'live' on this branch (have edges or box obligations)."""
    names = set(b.rels)
    for (_w, rel, _body) in b.boxes:
        names.add(rel)
    return names


def _frame_close(b: _Branch, ctx: _Ctx) -> bool:
    """Apply reflexive/symmetric/transitive/euclidean edge rules; return True if changed."""
    changed = False
    worlds = list(b.tv)
    for rel in list(_relnames(b)):
        conds = ctx.conds(rel)
        if not conds:
            continue
        edges = b.rels.setdefault(rel, set())
        if "refl" in conds:
            for w in worlds:
                if (w, w) not in edges:
                    edges.add((w, w))
                    changed = True
        if "sym" in conds:
            for (w, v) in list(edges):
                if (v, w) not in edges:
                    edges.add((v, w))
                    changed = True
        if "eucl" in conds:
            out = {}
            for (w, v) in edges:
                out.setdefault(w, []).append(v)
            for w, succs in out.items():
                for v in succs:
                    for u in succs:
                        if (v, u) not in edges:
                            edges.add((v, u))
                            changed = True
        if "trans" in conds:
            added = True
            while added:
                added = False
                for (w, v) in list(edges):
                    for (v2, u) in list(edges):
                        if v == v2 and (w, u) not in edges:
                            edges.add((w, u))
                            added = True
                            changed = True
    return changed


def _apply_boxes(b: _Branch) -> bool:
    """Push every box obligation to its successors; return True if anything was new."""
    changed = False
    for (w, rel, body) in list(b.boxes):
        for (a, v) in b.rels.get(rel, ()):
            if a == w and _assert(b, v, body):
                changed = True
    return changed


def _expand_simple(b: _Branch) -> bool:
    """Apply double-negation / α / box-record rules; return True if anything changed.

    Raises NotImplementedError on a temporal-closure operator.
    """
    changed = False
    for w in list(b.tv):
        for f in list(b.tv[w]):
            if (w, f) in b.expanded:
                continue
            kind = _decompose(f)
            tag = kind[0]
            if tag in ("lit", "true"):
                b.expanded.add((w, f))
            elif tag == "alpha":
                for comp in kind[1]:
                    if _assert(b, w, comp):
                        changed = True
                b.expanded.add((w, f))
                changed = True
            elif tag == "box":
                _, rel, body = kind
                if (w, rel, body) not in b.boxes:
                    b.boxes.add((w, rel, body))
                    changed = True
                b.expanded.add((w, f))
            elif tag == "unsupported":
                raise NotImplementedError(
                    "modal_tableau: the temporal-closure operator "
                    f"{type(kind[1]).__name__} (G/F/Until over the reflexive-"
                    "transitive temporal relation) is not handled by this tableau; "
                    "evaluate it with semantics.kripke.satisfies_modal, or decide it "
                    "with hol.isabelle_runner.isabelle_decide_modal.")
            # beta / dia handled by the search loop
    return changed


def _find_beta(b: _Branch):
    """Return ``(w, f, options)`` for an unexpanded branching formula, or None."""
    for w in b.tv:
        for f in b.tv[w]:
            if (w, f) in b.expanded:
                continue
            kind = _decompose(f)
            if kind[0] == "beta":
                return (w, f, kind[1])
    return None


def _find_diamond(b: _Branch):
    """Return ``(w, f, relname, body)`` for an unexpanded diamond, or None."""
    for w in b.tv:
        for f in b.tv[w]:
            if (w, f) in b.expanded:
                continue
            kind = _decompose(f)
            if kind[0] == "dia":
                return (w, f, kind[1], kind[2])
    return None


def _blocked(b: _Branch, w: int, relname: str, ctx: _Ctx) -> bool:
    """Subset-blocking for transitive relations: an earlier world subsumes ``w``.

    Only applied when the relation is transitive (where unbounded regress is
    otherwise possible); sound for the K4 family and, with the counter-model
    verification downstream, safe for S5/B too.
    """
    if "trans" not in ctx.conds(relname):
        return False
    sw = b.tv.get(w, set())
    for u in b.tv:
        if u < w and sw <= b.tv[u]:
            return True
    return False


def _find_seriality(b: _Branch, ctx: _Ctx):
    """A serial relation with a box obligation at a world that has no successor."""
    for (w, rel, _body) in b.boxes:
        if "serial" not in ctx.conds(rel):
            continue
        if not any(a == w for (a, _v) in b.rels.get(rel, ())):
            return (w, rel)
    return None


def _build_model(b: _Branch) -> KripkeModel:
    """Read an open saturated branch off as a Kripke model."""
    valuation = {}
    for w, s in b.tv.items():
        valuation[w] = {f.to_unicode_str() for f in s if isinstance(f, Atom)}
    relations = {r: set(e) for r, e in b.rels.items()}
    return KripkeModel(set(b.tv) | {0}, relations, valuation)


def _solve(b: _Branch, ctx: _Ctx):
    """Depth-first saturation of one branch.

    Returns ``("closed", None)``, ``("open", model)``, or ``("unknown", None)``.
    """
    while True:
        if not ctx.tick():
            return ("unknown", None)
        if _closes(b):
            return ("closed", None)

        # 1) propositional + box + frame saturation to fixpoint
        progressed = True
        while progressed:
            if not ctx.tick():
                return ("unknown", None)
            progressed = False
            if _expand_simple(b):
                progressed = True
            if _frame_close(b, ctx):
                progressed = True
            if _apply_boxes(b):
                progressed = True
            if _closes(b):
                return ("closed", None)

        # 2) a branching formula?
        beta = _find_beta(b)
        if beta is not None:
            w, f, options = beta
            all_closed = True
            for opt in options:
                child = b.copy()
                child.expanded.add((w, f))
                for comp in opt:
                    _assert(child, w, comp)
                res, model = _solve(child, ctx)
                if res == "open":
                    return ("open", model)
                if res != "closed":
                    all_closed = False
            return ("closed", None) if all_closed else ("unknown", None)

        # 3) an unfulfilled diamond?
        dia = _find_diamond(b)
        if dia is not None:
            w, f, relname, body = dia
            b.expanded.add((w, f))
            if _blocked(b, w, relname, ctx):
                continue
            if b.wcount >= ctx.max_worlds:
                return ("unknown", None)
            v = b.wcount
            b.wcount += 1
            b.tv.setdefault(v, set())
            b.rels.setdefault(relname, set()).add((w, v))
            _assert(b, v, body)
            continue

        # 4) seriality witness for a box-bearing world with no successor
        ser = _find_seriality(b, ctx)
        if ser is not None:
            w, relname = ser
            if b.wcount >= ctx.max_worlds:
                return ("unknown", None)
            v = b.wcount
            b.wcount += 1
            b.tv.setdefault(v, set())
            b.rels.setdefault(relname, set()).add((w, v))
            continue

        # 5) saturated and open
        return ("open", _build_model(b))


def _check_frame(frame: str, systems) -> None:
    if frame not in _FRAMES:
        raise ValueError(
            f"modal_tableau: unknown frame {frame!r} (use one of {sorted(_FRAMES)}).")
    for fam, sys in (systems or {}).items():
        if fam not in ("epistemic", "doxastic", "deontic", "temporal"):
            raise ValueError(
                f"modal_tableau: unknown system family {fam!r} (use epistemic / "
                "doxastic / deontic / temporal).")
        if sys not in _FRAMES:
            raise ValueError(
                f"modal_tableau: unknown system {sys!r} for {fam} "
                f"(use one of {sorted(_FRAMES)}).")


def _run(formulas, frame: str, systems, max_worlds: int, max_steps: int):
    """Build the root branch from ``formulas`` at world 0 and search it."""
    _check_frame(frame, systems)
    ctx = _Ctx(frame, systems, max_worlds, max_steps)
    root = _Branch()
    for f in formulas:
        _assert(root, 0, f)
    return _solve(root, ctx)


def modal_tableau_closed(formulas, frame: str = "K", systems=None,
                         max_worlds: int = 400, max_steps: int = 200000) -> bool:
    """Return True iff ``formulas`` are jointly unsatisfiable at a world (the tableau closes).

    Interprets the list as a set of formulas true at the same (root) world under the
    chosen ``frame`` (alethic system) and ``systems`` (per-family systems for
    epistemic / doxastic / deontic / temporal relations). Sound: a True is a real
    closed tableau. A False means "no closed tableau within the bound", never a
    positive satisfiability claim — use :func:`modal_countermodel` for that.
    """
    res, _ = _run(formulas, frame, systems, max_worlds, max_steps)
    return res == "closed"


def is_modal_valid(formula: Node, frame: str = "K", systems=None,
                   max_worlds: int = 400, max_steps: int = 200000) -> bool:
    """Return True iff ``formula`` is modally valid over ``frame`` — ``¬formula`` closes.

    Sound: only the closed tableau yields True. An open or bound-exhausted search
    yields False (the formula is then invalid-or-unknown; :func:`modal_decide`
    distinguishes the two with a verified counter-model).
    """
    res, _ = _run([Not(formula)], frame, systems, max_worlds, max_steps)
    return res == "closed"


def modal_prove(premises, conclusion: Node, frame: str = "K", systems=None,
                max_worlds: int = 400, max_steps: int = 200000) -> bool:
    """Return True iff ``premises`` locally entail ``conclusion`` over ``frame``.

    Local consequence: the tableau for ``premises ∪ {¬conclusion}`` at one world
    closes. Sound (a True is a closed tableau); incomplete only up to the bound.
    """
    res, _ = _run(list(premises) + [Not(conclusion)], frame, systems,
                  max_worlds, max_steps)
    return res == "closed"


def modal_countermodel(formula: Node, frame: str = "K", systems=None,
                       max_worlds: int = 400, max_steps: int = 200000):
    """Return a Kripke model falsifying ``formula`` over ``frame``, or None.

    None means the formula is valid (the tableau closed) **or** the search was
    inconclusive within the bound. The returned model is *verified*: it is only
    handed back when :func:`satisfies_modal` confirms the formula is false at its
    root world, so a counter-model is never spurious.
    """
    res, model = _run([Not(formula)], frame, systems, max_worlds, max_steps)
    if res != "open" or model is None:
        return None
    if satisfies_modal(formula, model, 0):
        return None
    return model


def modal_decide(formula: Node, frame: str = "K", systems=None,
                 max_worlds: int = 400, max_steps: int = 200000) -> str:
    """Decide ``formula`` over ``frame``: ``"valid"`` / ``"invalid"`` / ``"unknown"``.

    ``"valid"``   — the tableau for ``¬formula`` closed (a sound proof).
    ``"invalid"`` — an open branch yielded a counter-model **verified** by
                    :func:`satisfies_modal`.
    ``"unknown"`` — the search hit the world/step bound, or an open branch's model
                    failed verification (so neither verdict is safe to assert).

    Mirrors the valid / invalid / unknown contract of the local-Isabelle runner
    (:func:`~unicode_fol_kit.hol.isabelle_runner.isabelle_decide_modal`), but runs
    fully in-process with no external prover.
    """
    res, model = _run([Not(formula)], frame, systems, max_worlds, max_steps)
    if res == "closed":
        return "valid"
    if res == "open" and model is not None and not satisfies_modal(formula, model, 0):
        return "invalid"
    return "unknown"
