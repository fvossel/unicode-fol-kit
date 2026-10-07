"""A decision procedure for propositional linear-time temporal logic (LTL+Past).

**Scoping correction this module exists to state up front.** The kit's Kripke
semantics for ``Next``/``Always``/``Eventually``/``Until``/``Historically``/
``Once``/``Previous``/``Since`` (:mod:`unicode_logic_kit.semantics.kripke`) is
NOT standard linear-time LTL: ``"temporal"`` is an arbitrary (not necessarily
linear, not necessarily total) accessibility relation, ``Until``/``Since`` are
existential finite-path searches over it, and ``fol.qml``'s default temporal
axioms (refl + trans + ``N ⊆ T``) do not pin it down to a line either — see
``docs/guide/quantified-modal.md``'s worked example, where
``resolution.prove([], Ⓖ P → P)`` and ``qml_is_valid`` already disagree on a
temporal formula for exactly this reason, without either being unsound. This
module decides a DIFFERENT, narrower question: validity and satisfiability
under the STANDARD reading, where the temporal frame is fixed to the unique
discrete strict order on the natural numbers (0 < 1 < 2 < …) — "real" LTL, the
one PSPACE-complete decision problem the literature means by the name. It
answers a strictly more specific question than every other route in this kit
that touches these operator names, and says so by construction: it has no
``frame=`` parameter, because there is only one frame here.

**What the operator names mean on this frame** (matching this kit's own node
docstrings and ``semantics/kripke.py``'s documented semantics, so the same
name means the same thing everywhere in the kit, only the frame class
differs):

* ``Next`` (X): φ holds at the immediately following position.
* ``Always`` (G) / ``Eventually`` (F): φ holds at every / some position from
  NOW on, current position INCLUDED (``Gφ → φ`` and ``φ → Fφ`` are theorems).
* ``Until`` (U), non-strict/strong: ``φUψ`` holds iff ψ holds at some position
  ``n ≥`` now with φ holding at every position strictly before ``n`` — ψ may
  hold RIGHT NOW (n = now is allowed), matching
  ``_until_holds``'s ``n ≥ 0`` base case exactly.
* ``Historically`` (H) / ``Once`` (O): the past duals of G / F — φ at every /
  some position from the BEGINNING of time up to and including now.
* ``Since`` (S), non-strict/strong: the backward mirror of Until — ``φSψ``
  holds iff ψ held at some position ``n ≤`` now with φ holding at every
  position strictly after ``n`` up to and including now; ψ may hold right now.
* ``Previous`` (Y), WEAK at position 0: universal over the (at most one)
  immediate predecessor, per its own docstring ("vacuously true at a world
  with no past") — so ``Yφ`` is TRUE at position 0 for every φ, including
  ``Y(p ∧ ¬p)``. There is no existential ("strong") previous operator in the
  kit's AST; on a linear frame the existential reading is expressible as
  ``¬Y¬φ`` and this module uses exactly that identity internally.

**Initial vs. floating validity.** With past operators these genuinely
differ: ``Previous(p ∧ ¬p)`` — "there is no earlier position" — is TRUE at
position 0 of every model (the weak-Y vacuity above) but FALSE at every
later position (which does have a predecessor), so it is valid when
"valid" means "true at the start of every model" but not when it means
"true at every position of every model". ``mode="initial"`` (the default on
every public function here) decides the first, more standard reading for a
logic with past operators — the one every textbook LTL-with-past validity
claim means — by requiring the witness/refutation to be anchored at a
position with no predecessor. ``mode="floating"`` decides the second: a
position may be any point of any model, reachable by SOME finite legitimate
history from an actual start (this is cheap to add once the tableau graph
exists — see :func:`_run` — so both are offered instead of picking one
silently). Every SATISFIABLE floating query is also satisfiable in the
initial sense once you either need a genuine predecessor (unreachable at
position 0) or don't (reachable at position 0 too) — the two notions coincide
exactly on the past-operator-free (pure future) fragment.

**Algorithm.** A Fischer–Ladner-style closure of the input over
Next/Always/Eventually/Until (forward fixpoints, unfolded via their own
``Next``-wrapped continuation) and Historically/Once/Previous/Since (backward
fixpoints, unfolded via their own ``Previous``-wrapped continuation — Once and
Since need the existential ``¬Previous(¬·)`` form of that continuation, since
``Previous`` itself is only ever weak/universal); every syntactic shape in the
closure gets a LOCAL boolean equation (a Wolper-style "elementary atom")
relating it to smaller subformulas plus exactly one Next/Previous-wrapped
term, which is therefore INDEPENDENT of every other atom's choices — so, in
contrast to a general modal tableau, every combination of the FREE (ground
atom / Next / Previous) elements determines a full, locally consistent atom by
plain deterministic evaluation (:func:`_all_atoms`), no branching search
needed. Next/Previous membership between adjacent atoms is pinned by an
Next/Previous-consistency EDGE relation (:func:`_build_graph`) exactly like a
box modality's successor obligation, but two-way, since Next and Previous are
mirror images of the same edge. Satisfiability is then GENERALIZED BÜCHI
emptiness on this finite graph — Wolper's classical reduction — decided by
finding a reachable, non-trivial strongly connected component that intersects
every outstanding eventuality's fulfillment set (:func:`_fairness_sets`,
:func:`_has_fair_witness`). Past obligations need no separate fairness check,
because their truth is already pinned, position by position, by the
(backward, terminating-at-0) Previous-edge chain as the path is walked
forward. Two FORWARD shapes do need one: an explicit ``Eventually``/``Until``
promise, and — easy to miss, see :func:`_fairness_sets`'s own docstring for
the countermodel that catches getting it wrong — the IMPLICIT ``F(¬φ)``
hiding inside a false ``Always(φ)``, since ``¬Gφ`` is itself an eventuality
even though this module tracks only ``Gφ`` as a closure element.

**Soundness and completeness.** This is a complete decision procedure for the
supported fragment (Atom/And/Or/Not/Implies/Iff/Xor plus the eight temporal
operators above) on the standard linear frame — PSPACE-complete in general,
and the closure/atom construction here is worst-case exponential in formula
size (as any sound LTL decision procedure must be), guarded by ``max_atoms``:
exceeding it yields ``"unknown"`` (reason ``bound_hit``), never a wrong
``"valid"``/``"invalid"``. Every returned countermodel/witness
(:class:`LTLTrace`, an explicit finite-prefix-plus-cycle lasso) is verified
before release by :func:`ltl_trace_satisfies` — a direct, from-the-semantic-
equations evaluator over the lasso, independent of the closure/atom/graph
machinery above (mirroring how :func:`modal_tableau.modal_countermodel`
verifies against :func:`~unicode_logic_kit.semantics.kripke.satisfies_modal`
before release) — so a bug in the graph construction can make this module
report ``"unknown"`` too often, never hand back a spurious witness. Any node
outside the supported fragment (Box, Knows, a quantifier, …) is refused by
name with ``NotImplementedError`` rather than approximated; use
:mod:`unicode_logic_kit.atp.modal_tableau`, :func:`~unicode_logic_kit.fol.qml.qml_is_valid`,
or :func:`~unicode_logic_kit.hol.isabelle_runner.isabelle_decide_modal` for
anything genuinely modal.

**Equality is NOT interpreted here.** An atom is a propositional letter: the elementary
atoms of the closure are sets of rendered atom keys, and a trace is read off as a valuation of
those keys. ``a = a`` or ``a ≠ b`` would therefore be an unconstrained letter, and
``⊢ a = a`` would be refuted by a lasso in which the letter ``a = a`` is false although
identity is reflexive. Every entry point refuses an equality or disequality atom anywhere in
its formulas by name (the shared :func:`~unicode_logic_kit.semantics._modal_reject.reject_equality_in`,
the refusal :mod:`unicode_logic_kit.atp.modal_tableau` and the Kripke evaluator give), before any
search. Decide identity with :func:`~unicode_logic_kit.fol.qml.qml_is_valid` or another
first-order route.

**Where this is a strict completeness gain.** Temporal induction
``(φ ∧ G(φ → Xφ)) → Gφ`` is the standard textbook example that ``qml_is_valid``
cannot reach — its own docstring says so explicitly: "reaching an arbitrary
T-successor from the first step needs induction over the closure, which no
first-order theory states." This module proves it (see
``tests/test_ltl_tableau.py``), because the Fischer–Ladner closure computes
that induction directly rather than approximating it with finitely many
unfoldings.

**Sorted constants and bounds.** A sorted constant ``c:S`` is the constant ``c`` and lies
in ``S`` at EVERY position (a constant is a rigid designator): ``Mortal(c:S)`` and
``Mortal(c)`` are one letter, ``S(c)`` is a letter true everywhere, and a countermodel is
only released if it makes it so (:func:`_lift_sorted_constants`). Besides ``max_atoms`` every
entry point takes an optional wall-clock ``timeout`` in milliseconds, read while the atoms
and the graph between them are built and in every step after that (reachability, pruning,
strongly connected components, fairness, the witness walk); past it the answer is ``"unknown"``.

Public API: :func:`ltl_tableau_closed`, :func:`ltl_valid`, :func:`ltl_decide`,
:func:`ltl_countermodel`, :func:`ltl_trace_satisfies`, :class:`LTLTrace`.
"""

import time
from dataclasses import dataclass
from typing import Dict, FrozenSet, List, Optional, Sequence, Tuple

from .._deadline import DeadlineReached, passed as _passed
from ..fol.nodes import (
    Node, Atom, Not, And, Or, Implies, Iff, Xor,
    Next, Always, Eventually, Until,
    Historically, Once, Previous, Since,
)
from ..fol._atom_keys import AtomKeys, atom_key
from ..fol._truth_constants import truth_value
from ..semantics._modal_reject import reject_equality_in
from .lj import _forget_constant_sorts

__all__ = [
    "LTLTrace",
    "ltl_tableau_closed", "ltl_valid", "ltl_decide", "ltl_countermodel",
    "ltl_trace_satisfies",
    "LtlTableauBackend",
]

# The fragment this module decides: classical connectives plus the eight
# temporal operators named in the module docstring. Anything else is refused
# by name in _closure().
_TEMPORAL_FUTURE = (Always, Eventually, Until)
_TEMPORAL_PAST = (Historically, Once, Since)
_SUPPORTED = (Atom, And, Or, Implies, Iff, Xor,
             Next, Previous) + _TEMPORAL_FUTURE + _TEMPORAL_PAST

#: Safety cap on the number of FREE closure elements (ground atoms plus
#: Next/Previous-shaped terms): the atom set has size ``2 ** len(free)``, so
#: this bounds both memory and the O(atoms^2) graph-construction cost.
#: Exceeding it yields "unknown"/bound_hit rather than hanging — the same
#: honest-incompleteness contract modal_tableau's max_worlds/max_steps give.
_DEFAULT_MAX_ATOMS = 4096


@dataclass(frozen=True)
class LTLTrace:
    """An explicit ultimately-periodic witness word (a "lasso").

    ``prefix + cycle*`` is the infinite word: positions ``0 .. len(prefix)-1``
    are the (possibly empty) finite lead-in, then ``cycle`` repeats forever.
    Each position's valuation is a frozenset of ground-atom keys
    (``Atom.to_unicode_str()``, the same convention
    :class:`~unicode_logic_kit.semantics.kripke.KripkeModel` uses) true there.

    ``witness_position`` is the 0-based index (into the infinite word, so it
    may fall inside ``cycle``) at which the formula this trace witnesses was
    checked. It is ``0`` for every ``mode="initial"`` result (the only
    position that mode ever anchors at) and may be greater than
    ``len(prefix)`` for a ``mode="floating"`` result, where ``prefix`` still
    starts at a genuine position-0 (no-predecessor) state so that PAST
    operators evaluated at ``witness_position`` see a real, finite history.
    """

    prefix: Tuple[FrozenSet[str], ...]
    cycle: Tuple[FrozenSet[str], ...]
    witness_position: int = 0

    def at(self, n: int) -> FrozenSet[str]:
        """Return the valuation at position ``n`` (>= 0) of the infinite word."""
        if n < 0:
            raise ValueError(f"LTLTrace.at: position {n} is negative")
        if n < len(self.prefix):
            return self.prefix[n]
        if not self.cycle:
            raise ValueError("LTLTrace.at: position past the prefix but cycle is empty")
        return self.cycle[(n - len(self.prefix)) % len(self.cycle)]

    def to_dict(self) -> dict:
        """Serialise to a JSON-compatible dict."""
        return {
            "kind": "ltl_lasso",
            "prefix": [sorted(v) for v in self.prefix],
            "cycle": [sorted(v) for v in self.cycle],
            "witness_position": self.witness_position,
        }


# --------------------------------------------------------------------------- #
# Closure construction.
# --------------------------------------------------------------------------- #

#: How this route reads an atom: the clause the shared equality refusal needs to say why
#: identity cannot be read here.
_EQUALITY_ROUTE = "the propositional LTL tableau"
_EQUALITY_ATOM_READING = ("an atom is a propositional letter: the elementary atoms are sets of "
                          "rendered atom keys and a trace is a valuation of those keys")


def _reject_equality(formulas: Sequence[Node], caller: str) -> None:
    """Refuse an equality / disequality atom ANYWHERE in ``formulas``, by name.

    A whole-tree scan, run before anything else reads the formulas (see the module
    docstring's "Equality is NOT interpreted here"): a branch of the search that never
    reaches the atom would otherwise answer without having looked at it.
    """
    for formula in formulas:
        reject_equality_in(formula, caller, _EQUALITY_ROUTE,
                           atom_reading=_EQUALITY_ATOM_READING)


def _strip_not(node: Node) -> Node:
    """Unwrap every leading ``Not`` (so double negation collapses to nothing)."""
    while isinstance(node, Not):
        node = node.formula
    return node


def _closure(seeds: Sequence[Node]) -> FrozenSet[Node]:
    """Return the Fischer–Ladner-style closure of ``seeds`` (see module docstring).

    Every element is stored in its "base" (non-``Not``) shape; a query for its
    negated reading goes through :func:`_holds`, never a second closure entry
    — so ``φ`` and ``¬φ`` are never redundantly double-counted. Raises
    ``NotImplementedError`` naming the first node outside ``_SUPPORTED`` found
    anywhere in ``seeds`` (Box, Knows, a quantifier, PAL, hybrid, …).
    """
    cl: set = set()
    stack: List[Node] = list(seeds)
    while stack:
        n = _strip_not(stack.pop())
        if n in cl:
            continue
        if not isinstance(n, _SUPPORTED):
            raise NotImplementedError(
                f"ltl_tableau: no rule for {type(n).__name__} "
                f"({n.to_unicode_str()!r}) — this module decides only the "
                "propositional temporal-closure fragment (Atom/And/Or/Not/"
                "Implies/Iff/Xor + Next/Always/Eventually/Until/Historically/"
                "Once/Previous/Since) over the STANDARD LINEAR frame; use "
                "atp.modal_tableau, fol.qml.qml_is_valid, or "
                "hol.isabelle_runner.isabelle_decide_modal for anything else.")
        cl.add(n)
        if isinstance(n, Atom):
            continue
        if isinstance(n, (And, Or, Implies, Iff, Xor)):
            stack.append(n.left)
            stack.append(n.right)
        elif isinstance(n, (Next, Previous)):
            stack.append(n.formula)
        elif isinstance(n, Always):
            stack.append(n.formula)
            stack.append(Next(n))
        elif isinstance(n, Eventually):
            stack.append(n.formula)
            stack.append(Next(n))
        elif isinstance(n, Until):
            stack.append(n.left)
            stack.append(n.right)
            stack.append(Next(n))
        elif isinstance(n, Historically):
            stack.append(n.formula)
            stack.append(Previous(n))
        elif isinstance(n, Once):
            stack.append(n.formula)
            stack.append(Previous(Not(n)))
        elif isinstance(n, Since):
            stack.append(n.left)
            stack.append(n.right)
            stack.append(Previous(Not(n)))
    return frozenset(cl)


def _holds(atom: FrozenSet[Node], node: Node) -> bool:
    """Not-aware ATOM membership query: is ``node`` true according to the
    frozenset ``atom`` of an atom's true closure elements? Strips every
    leading ``Not`` first. Used everywhere an already-BUILT atom is read
    (graph construction, the initial/seeded filters, fairness sets, …)."""
    neg = False
    while isinstance(node, Not):
        node = node.formula
        neg = not neg
    return (node in atom) != neg


def _truth(node: Node, vals: Dict[Node, bool]) -> bool:
    """Recursively DERIVE ``node``'s truth in ``vals`` (memoizing into ``vals``
    as it goes — this is the one place a closure element's value is computed
    from scratch, via :func:`_dval` on its equation's operands).

    ``vals`` starts pre-seeded with the FREE elements' chosen truth values
    (ground atoms and Next/Previous-shaped closure members — see the module
    docstring's "every combination ... determines a full atom" argument).
    Every other closure element's equation references only structurally
    smaller subformulas (already resolvable by recursion) and exactly one
    already-free Next/Previous-wrapped term, so this always terminates.
    """
    if node in vals:
        return vals[node]
    if isinstance(node, And):
        v = _dval(vals, node.left) and _dval(vals, node.right)
    elif isinstance(node, Or):
        v = _dval(vals, node.left) or _dval(vals, node.right)
    elif isinstance(node, Implies):
        v = (not _dval(vals, node.left)) or _dval(vals, node.right)
    elif isinstance(node, Iff):
        v = _dval(vals, node.left) == _dval(vals, node.right)
    elif isinstance(node, Xor):
        v = _dval(vals, node.left) != _dval(vals, node.right)
    elif isinstance(node, Always):
        v = _dval(vals, node.formula) and _dval(vals, Next(node))
    elif isinstance(node, Eventually):
        v = _dval(vals, node.formula) or _dval(vals, Next(node))
    elif isinstance(node, Until):
        v = _dval(vals, node.right) or (
            _dval(vals, node.left) and _dval(vals, Next(node)))
    elif isinstance(node, Historically):
        v = _dval(vals, node.formula) and _dval(vals, Previous(node))
    elif isinstance(node, Once):
        v = _dval(vals, node.formula) or (not _dval(vals, Previous(Not(node))))
    elif isinstance(node, Since):
        v = _dval(vals, node.right) or (
            _dval(vals, node.left) and not _dval(vals, Previous(Not(node))))
    else:  # pragma: no cover — every non-free _SUPPORTED shape is handled above
        raise AssertionError(f"ltl_tableau: {node!r} should already be a free element")
    vals[node] = v
    return v


def _dval(vals: Dict[Node, bool], node: Node) -> bool:
    """Not-aware truth query INTO an in-progress ``vals`` computation: strips
    every leading ``Not``, then recurses through :func:`_truth` (never a bare
    dict lookup) so a not-yet-computed dependency is derived on demand."""
    neg = False
    while isinstance(node, Not):
        node = node.formula
        neg = not neg
    return _truth(node, vals) != neg


def _all_atoms(cl: FrozenSet[Node], max_atoms: int, deadline: Optional[float] = None):
    """Enumerate every locally consistent atom over ``cl``, or ``None`` if the
    free-element count would make ``2 ** k`` exceed ``max_atoms`` or the
    ``time.perf_counter()`` ``deadline`` passes first."""
    # `$true` / `$false` are constants: they are never free (not varied), and every
    # atom gives them their one value.
    constants: Dict[Node, bool] = {}
    for c in cl:
        value = truth_value(c)
        if value is not None:
            constants[c] = value
    free = sorted((c for c in cl
                   if isinstance(c, (Atom, Next, Previous)) and c not in constants),
                  key=repr)
    if 2 ** len(free) > max_atoms:
        return None
    atoms = []
    for bits in _bit_combinations(len(free)):
        if deadline is not None and time.perf_counter() > deadline:
            return None
        vals: Dict[Node, bool] = dict(zip(free, bits))
        vals.update(constants)
        for c in cl:
            _truth(c, vals)
        atoms.append(frozenset(c for c in cl if vals[c]))
    return atoms


def _bit_combinations(k: int):
    """Yield every length-``k`` tuple of bools, ``False``/``True`` per slot."""
    if k == 0:
        yield ()
        return
    for rest in _bit_combinations(k - 1):
        yield (False,) + rest
        yield (True,) + rest


# --------------------------------------------------------------------------- #
# Graph construction: Next/Previous-consistency edges between atoms.
# --------------------------------------------------------------------------- #

def _build_graph(atoms: List[FrozenSet[Node]],
                 next_terms: List[Next], prev_terms: List[Previous],
                 deadline: Optional[float] = None):
    """Return ``edges``: ``edges[i]`` is the set of ``j`` with atoms[i] -> atoms[j]
    a valid step — for every ``Next(g)``: ``Next(g) in A <=> g holds in B``;
    for every ``Previous(g)``: ``Previous(g) in B <=> g holds in A``. Bucketed
    by B's "as-a-next-target" signature so this is faster than the naive
    O(atoms^2 * |terms|) in the common case of few distinct signatures.
    Returns ``None`` instead if the ``time.perf_counter()`` instant ``deadline``
    passes while the edges are built.
    """
    n = len(atoms)

    def next_body_sig(atom):
        return tuple(_holds(atom, t.formula) for t in next_terms)

    def next_own_sig(atom):
        return tuple(t in atom for t in next_terms)

    def prev_body_sig(atom):
        return tuple(_holds(atom, t.formula) for t in prev_terms)

    def prev_own_sig(atom):
        return tuple(t in atom for t in prev_terms)

    buckets: Dict[tuple, List[int]] = {}
    prev_own = [None] * n
    prev_body = [None] * n
    for j, B in enumerate(atoms):
        buckets.setdefault(next_body_sig(B), []).append(j)
        prev_own[j] = prev_own_sig(B)
    for i in range(n):
        prev_body[i] = prev_body_sig(atoms[i])

    edges: List[set] = [set() for _ in range(n)]
    for i, A in enumerate(atoms):
        if deadline is not None and time.perf_counter() > deadline:
            return None
        for j in buckets.get(next_own_sig(A), ()):
            if prev_own[j] == prev_body[i]:
                edges[i].add(j)
    return edges


# --------------------------------------------------------------------------- #
# Reachability, pruning, SCC, generalized-Büchi fairness, witness extraction.
# --------------------------------------------------------------------------- #

def _check(deadline: Optional[float]) -> None:
    """Raise :class:`~unicode_logic_kit._deadline.DeadlineReached` if ``deadline`` has passed.

    The graph algorithms below call it once per node they take up, so none of them runs
    past the deadline by more than one node's edges; :func:`_run` catches the exception.
    """
    if _passed(deadline):
        raise DeadlineReached


def _bfs_reachable(starts, edges, deadline: Optional[float] = None) -> set:
    """Every index reachable from ``starts`` (inclusive) following ``edges``."""
    seen = set(starts)
    frontier = list(starts)
    while frontier:
        _check(deadline)
        i = frontier.pop()
        for j in edges[i]:
            if j not in seen:
                seen.add(j)
                frontier.append(j)
    return seen


def _bfs_path(start: int, targets: set, edges,
              deadline: Optional[float] = None) -> Optional[List[int]]:
    """Shortest path (list of indices, ``start`` first) from ``start`` to any
    index in ``targets``, following only edges whose BOTH ends are keys of
    ``edges`` (i.e. edges already restricted to the relevant induced
    subgraph); ``None`` if unreachable."""
    if start in targets:
        return [start]
    parent: Dict[int, Optional[int]] = {start: None}
    frontier = [start]
    while frontier:
        nxt = []
        for i in frontier:
            _check(deadline)
            for j in edges.get(i, ()):
                if j in parent:
                    continue
                parent[j] = i
                if j in targets:
                    path = [j]
                    back = parent[j]
                    while back is not None:
                        path.append(back)
                        back = parent[back]
                    path.reverse()
                    return path
                nxt.append(j)
        frontier = nxt
    return None


def _prune(nodes: set, edges, deadline: Optional[float] = None) -> set:
    """Remove nodes with no outgoing edge staying inside the current set,
    to a fixpoint — exactly the nodes that can start SOME infinite path."""
    alive = set(nodes)
    changed = True
    while changed:
        changed = False
        for i in list(alive):
            _check(deadline)
            if not (edges[i] & alive):
                alive.discard(i)
                changed = True
    return alive


def _sccs(nodes: set, edges, deadline: Optional[float] = None) -> List[set]:
    """Strongly connected components of the subgraph induced by ``nodes``
    (iterative Kosaraju: two passes, no recursion-depth risk)."""
    order: List[int] = []
    visited = set()
    for start in nodes:
        if start in visited:
            continue
        stack = [(start, iter(edges[start] & nodes))]
        visited.add(start)
        while stack:
            _check(deadline)
            node, it = stack[-1]
            advanced = False
            for nxt in it:
                if nxt not in visited:
                    visited.add(nxt)
                    stack.append((nxt, iter(edges[nxt] & nodes)))
                    advanced = True
                    break
            if not advanced:
                order.append(node)
                stack.pop()

    reverse: Dict[int, set] = {i: set() for i in nodes}
    for i in nodes:
        _check(deadline)
        for j in edges[i] & nodes:
            reverse[j].add(i)

    seen = set()
    components = []
    for node in reversed(order):
        if node in seen:
            continue
        comp = set()
        pending = [node]
        seen.add(node)
        while pending:
            _check(deadline)
            cur = pending.pop()
            comp.add(cur)
            for prev in reverse[cur]:
                if prev not in seen:
                    seen.add(prev)
                    pending.append(prev)
        components.append(comp)
    return components


def _fairness_sets(cl: FrozenSet[Node], atoms: List[FrozenSet[Node]],
                   deadline: Optional[float] = None):
    """Generalized-Büchi acceptance sets: atom-indices where an outstanding
    promise is either not made or already kept. A fair path must hit EVERY
    one of these infinitely often. Two kinds of promise need one:

    * an EXPLICIT future eventuality — ``Eventually(g)``/``Until(l, r)`` in
      ``cl`` — kept once ``g``/``r`` holds;
    * an IMPLICIT one hiding inside a FALSE ``Always(g)``: ``¬Gφ`` is,
      semantically, ``F(¬φ)`` — a promise of an eventual ``¬φ`` — but this
      module tracks only ``Gφ`` itself as a closure element (see
      :func:`_closure`), so an atom's plain ABSENCE of ``Always(g)`` carries
      that promise with no explicit node to hang a fairness set on. Without
      one, the atom/edge construction alone is only LOCALLY consistent at
      every step (``¬Gφ`` at ``n`` needs only ``¬Gφ`` or ``¬φ`` at ``n+1``),
      which a path can satisfy forever by always deferring — asserting
      ``Gφ`` false at every position while ``φ`` holds at every position too,
      never actually witnessing ``¬φ`` — a "lying" run a bounded lasso search
      catches immediately (this fairness set is what makes ``Fp ↔ ¬G¬p``
      come back valid rather than handing back exactly such a countermodel).

    Past duals (``Historically``/``Once``/``Since``, in either polarity) need
    NONE of this: their truth is pinned by the Previous-edge chain as a path
    is walked forward, and that chain always terminates at an actual
    position-0 base case in finitely many backward steps — so nothing past
    can ever be "promised and deferred forever" the way a FORWARD obligation
    can (see the module docstring).
    """
    sets = []
    for e in cl:
        _check(deadline)
        if isinstance(e, Eventually):
            sets.append({i for i, atom in enumerate(atoms)
                        if e not in atom or _holds(atom, e.formula)})
        elif isinstance(e, Until):
            sets.append({i for i, atom in enumerate(atoms)
                        if e not in atom or _holds(atom, e.right)})
        elif isinstance(e, Always):
            sets.append({i for i, atom in enumerate(atoms)
                        if e in atom or not _holds(atom, e.formula)})
    return sets


def _has_fair_witness(starts: set, atoms, edges, fairness_sets,
                      deadline: Optional[float] = None):
    """Does SOME infinite path from ``starts`` hit every fairness set
    infinitely often? Returns ``(True, entry, scc, reach_edges)`` — ``entry``
    a chosen SCC member and ``reach_edges`` the induced-subgraph edge map
    used to build the witness path — or ``(False, None, None, None)``.
    """
    reach = _bfs_reachable(starts, edges, deadline)
    reach_edges = {i: (edges[i] & reach) for i in reach}
    alive = _prune(reach, {i: reach_edges[i] for i in reach}, deadline)
    if not alive:
        return False, None, None, None
    alive_edges = {i: (reach_edges[i] & alive) for i in alive}
    for comp in _sccs(alive, alive_edges, deadline):
        _check(deadline)
        nontrivial = len(comp) > 1 or any(i in alive_edges[i] for i in comp)
        if not nontrivial:
            continue
        if all(comp & fs for fs in fairness_sets):
            entry = next(iter(comp))
            return True, entry, comp, alive_edges
    return False, None, None, None


def _cycle_visiting_all(entry: int, scc: set, edges,
                        deadline: Optional[float] = None) -> List[int]:
    """A closed walk ``entry -> ... -> entry`` (indices, entry both ends, at
    least one edge taken) visiting every node of ``scc`` at least once —
    always exists since ``scc`` is strongly connected (or, for a singleton
    ``scc``, has a self-loop — the other half of "non-trivial", checked by
    the caller). Chains shortest paths through an arbitrary but fixed order
    of ``scc``'s members, so it trivially hits every fairness set's
    intersection with ``scc`` along the way."""
    local_edges = {i: (edges[i] & scc) for i in scc}
    others = [n for n in scc if n != entry]
    if not others:
        # A singleton non-trivial SCC is exactly a self-loop.
        return [entry, entry]
    order = [entry] + others + [entry]
    walk = [entry]
    for k in range(len(order) - 1):
        _check(deadline)
        path = _bfs_path(walk[-1], {order[k + 1]}, local_edges, deadline)
        walk.extend(path[1:])
    return walk


def _valuation(atom: FrozenSet[Node]) -> FrozenSet[str]:
    """Ground-atom keys true at ``atom`` (mirrors modal_tableau's ``_build_model``)."""
    return frozenset(a.to_unicode_str() for a in atom
                     if isinstance(a, Atom) and truth_value(a) is None)


# --------------------------------------------------------------------------- #
# The core engine.
# --------------------------------------------------------------------------- #

def _run(seeds: Sequence[Node], mode: str, max_atoms: int, timeout: Optional[int] = None):
    """Decide joint satisfiability of ``seeds`` under ``mode``.

    Returns ``("unsat", None)``, ``("sat", LTLTrace)``, or ``("unknown", None)``
    (the atom count exceeded ``max_atoms``, or the ``timeout`` in milliseconds ran
    out). The clock is read while the atoms and the graph between them are built and
    in every step after that (the reachability searches, the pruning, the strongly
    connected components, the fairness test and the witness walk), so the call as a
    whole ends at its deadline.
    """
    if mode not in ("initial", "floating"):
        raise ValueError(f"ltl_tableau: unknown mode {mode!r} (use 'initial' or 'floating')")
    _reject_equality(seeds, "ltl_tableau")

    deadline = None if timeout is None else time.perf_counter() + timeout / 1000.0
    try:
        return _decide(seeds, mode, max_atoms, deadline)
    except DeadlineReached:
        return "unknown", None


def _decide(seeds: Sequence[Node], mode: str, max_atoms: int, deadline: Optional[float]):
    """The search of :func:`_run`; raises :class:`~unicode_logic_kit._deadline.DeadlineReached`
    once ``deadline`` (a ``perf_counter`` instant, or ``None``) has passed."""
    cl = _closure(seeds)
    atoms = _all_atoms(cl, max_atoms, deadline)
    if atoms is None:
        return "unknown", None
    next_terms = [c for c in cl if isinstance(c, Next)]
    prev_terms = [c for c in cl if isinstance(c, Previous)]
    edges = _build_graph(atoms, next_terms, prev_terms, deadline)
    if edges is None:
        return "unknown", None

    init = set()
    seeded = set()
    for i, atom in enumerate(atoms):
        _check(deadline)
        if all(pv in atom for pv in prev_terms):
            init.add(i)
        if all(_holds(atom, s) for s in seeds):
            seeded.add(i)

    if mode == "initial":
        starts = init & seeded
        prefix_from_init: Dict[int, List[int]] = {i: [i] for i in starts}
    else:
        reach_from_init = _bfs_reachable(init, edges, deadline)
        starts = reach_from_init & seeded
        if not starts:
            prefix_from_init = {}
        else:
            # BFS from EVERY init atom at once, recording one shortest
            # path per reached index (used only for the witness, below).
            parent: Dict[int, Optional[int]] = {i: None for i in init}
            frontier = list(init)
            while frontier:
                nxt = []
                for i in frontier:
                    _check(deadline)
                    for j in edges[i]:
                        if j not in parent:
                            parent[j] = i
                            nxt.append(j)
                frontier = nxt

            def _path_to(i):
                path = [i]
                while parent[path[-1]] is not None:
                    path.append(parent[path[-1]])
                path.reverse()
                return path

            prefix_from_init = {i: _path_to(i) for i in starts}

    if not starts:
        return "unsat", None

    fairness_sets = _fairness_sets(cl, atoms, deadline)
    ok, entry, scc, alive_edges = _has_fair_witness(starts, atoms, edges, fairness_sets, deadline)
    if not ok:
        return "unsat", None

    # Pick a start atom that can actually reach the fair SCC on its own (one
    # must exist: `entry` was found reachable from `starts` taken together,
    # and a multi-source BFS only ever discovers a node through ONE origin).
    start_idx = None
    for i in starts:
        local_reach = _bfs_reachable({i}, edges, deadline)
        if entry in local_reach:
            start_idx = i
            break

    lead_in = prefix_from_init[start_idx]
    reach_of_start = _bfs_reachable({start_idx}, edges, deadline)
    to_scc_edges = {i: (edges[i] & reach_of_start) for i in reach_of_start}
    path_to_scc = _bfs_path(lead_in[-1], scc, to_scc_edges, deadline)
    entry_actual = path_to_scc[-1]
    cycle_walk = _cycle_visiting_all(entry_actual, scc, alive_edges, deadline)

    full_prefix_idx = lead_in[:-1] + path_to_scc          # ends AT entry_actual
    # `cycle_walk` is the CLOSED walk entry_actual -> ... -> entry_actual, so
    # its own first element duplicates full_prefix_idx's last one (same
    # atom, not a second hop) — drop THAT one, not the last: the position
    # right after the prefix must be reached from entry_actual by an actual
    # edge (cycle_walk[1]), and the cycle's own last element must be the one
    # with a valid edge BACK to cycle_walk[1] (i.e. entry_actual itself,
    # cycle_walk[-1]) to close the loop soundly.
    cycle_idx = cycle_walk[1:]                             # first hop .. back to entry_actual

    prefix = tuple(_valuation(atoms[i]) for i in full_prefix_idx)
    cycle = tuple(_valuation(atoms[i]) for i in cycle_idx)
    witness_position = len(lead_in) - 1
    trace = LTLTrace(prefix=prefix, cycle=cycle, witness_position=witness_position)
    return "sat", trace


# --------------------------------------------------------------------------- #
# Independent evaluator (used to verify every witness before release).
# --------------------------------------------------------------------------- #

def ltl_trace_satisfies(formula: Node, trace: LTLTrace,
                        position: Optional[int] = None, horizon: int = 200) -> bool:
    """Evaluate ``formula`` at ``position`` (default ``trace.witness_position``)
    of ``trace``, directly from the linear-time satisfaction equations — no
    connection to the closure/atom/graph machinery in this module, so it is a
    genuine independent check on any witness this module produces.

    ``horizon`` bounds how far the FUTURE (G/F/U) search looks ahead; it is
    always sound to stop early because the trace is eventually periodic (an
    exhaustive check across one full extra period after the point it last
    changed value is conclusive forever after). Past operators (H/O/Y/S)
    recurse strictly backward to position 0, always exactly (never
    approximated) and always terminating, since every position has only
    finitely many predecessors. ``horizon`` defaults generously (the tests
    here use prefixes/cycles of at most a handful of positions), so 200 is
    already far more than any nesting of temporal operators this module's own
    tests exercise could need to stabilise a forward search across.

    An equality or disequality atom is refused by name (``NotImplementedError``), as
    in every entry point of this module: a trace is a valuation of rendered atom keys,
    which gives identity no meaning. So are two different atoms that print alike (the
    numeral ``1`` and a constant named ``1``, a free variable ``x`` and a constant named
    ``x``): one key of the trace could not tell them apart.

    A sorted constant ``c:S`` is the constant ``c``: ``Mortal(carl:Human)`` is read at the
    key ``'Mortal(carl)'``, the key every countermodel trace of this module holds. That
    ``Human(carl)`` is true at every position is a property of the trace which this
    evaluator, like every evaluator of a given structure, does not check (the decision
    functions add it as a premise).
    """
    _reject_equality([formula], "ltl_trace_satisfies")
    AtomKeys("ltl_trace_satisfies").letters([formula])
    return _trace_satisfies(formula, trace, position, horizon)


def _trace_satisfies(formula: Node, trace: LTLTrace,
                     position: Optional[int] = None, horizon: int = 200) -> bool:
    """The evaluation of :func:`ltl_trace_satisfies`, for a formula already known to hold no
    equality atom and no two atoms of one key (the decision functions verify the witness of
    a search that kept its atoms as nodes, and read a pair of clashing atoms as ``unknown``
    rather than refuse)."""
    if position is None:
        position = trace.witness_position
    memo: Dict[Tuple[Node, int], bool] = {}

    def ev(node: Node, i: int) -> bool:
        key = (node, i)
        if key in memo:
            return memo[key]
        if isinstance(node, Not):
            v = not ev(node.formula, i)
        elif isinstance(node, Atom):
            constant = truth_value(node)
            v = constant if constant is not None else atom_key(node) in trace.at(i)
        elif isinstance(node, And):
            v = ev(node.left, i) and ev(node.right, i)
        elif isinstance(node, Or):
            v = ev(node.left, i) or ev(node.right, i)
        elif isinstance(node, Implies):
            v = (not ev(node.left, i)) or ev(node.right, i)
        elif isinstance(node, Iff):
            v = ev(node.left, i) == ev(node.right, i)
        elif isinstance(node, Xor):
            v = ev(node.left, i) != ev(node.right, i)
        elif isinstance(node, Next):
            v = ev(node.formula, i + 1)
        elif isinstance(node, Previous):
            v = True if i == 0 else ev(node.formula, i - 1)
        elif isinstance(node, Always):
            v = all(ev(node.formula, m) for m in range(i, i + horizon))
        elif isinstance(node, Eventually):
            v = any(ev(node.formula, m) for m in range(i, i + horizon))
        elif isinstance(node, Until):
            v = False
            for m in range(i, i + horizon):
                if ev(node.right, m):
                    v = True
                    break
                if not ev(node.left, m):
                    break
        elif isinstance(node, Historically):
            v = all(ev(node.formula, m) for m in range(0, i + 1))
        elif isinstance(node, Once):
            v = any(ev(node.formula, m) for m in range(0, i + 1))
        elif isinstance(node, Since):
            v = False
            for m in range(i, -1, -1):
                if ev(node.right, m):
                    v = True
                    break
                if not ev(node.left, m):
                    break
        else:
            raise NotImplementedError(
                f"ltl_trace_satisfies: no rule for {type(node).__name__}")
        memo[key] = v
        return v

    return ev(formula, position)


# --------------------------------------------------------------------------- #
# Public entry points — mirroring modal_tableau's surface.
# --------------------------------------------------------------------------- #

def _fold_goal(formula: Node, premises: Sequence[Node]) -> Node:
    """Fold ``premises ⊨ formula`` into ``(∧ premises) → formula`` (empty
    premises: ``formula`` unchanged) — same convention as
    ``atp.protocol._implication``, reimplemented locally so this module stays
    a self-contained new addition rather than reaching into protocol.py."""
    premises = list(premises)
    if not premises:
        return formula
    conj = premises[0]
    for p in premises[1:]:
        conj = And(conj, p)
    return Implies(conj, formula)


def _lift_sorted_constants(formulas: Sequence[Node], mode: str):
    """``formulas`` with every sorted constant plain, and the seeds that keep its sort true of it.

    A sorted constant ``c:S`` is the constant ``c`` and an element of ``S`` at EVERY
    position (a constant is a rigid designator), so ``Mortal(c:S)`` and ``Mortal(c)``
    are one letter and the guard atom ``S(c)`` is a letter true everywhere. The seeds
    are ``Always S(c)`` (and, for ``mode="floating"``, where the anchor may have a
    past, ``Historically S(c)`` too), one set per distinct ``c:S``. Without them
    ``Human(carl:Human)`` has a model in which carl is no ``Human``, and a valid
    formula is reported invalid. A formula without a sorted constant is returned as
    it is, with no seed.
    """
    membership: List[Node] = []
    plain = [_forget_constant_sorts(f, membership) for f in formulas]
    seeds: List[Node] = []
    for atom in dict.fromkeys(membership):
        seeds.append(Always(atom))
        if mode == "floating":
            seeds.append(Historically(atom))
    return plain, seeds


def ltl_tableau_closed(formulas: Sequence[Node], mode: str = "initial",
                       max_atoms: int = _DEFAULT_MAX_ATOMS,
                       timeout: Optional[int] = None) -> bool:
    """True iff ``formulas`` are jointly UNSATISFIABLE under ``mode`` (see the
    module docstring for "initial" vs. "floating"). ``False`` means either a
    genuine model exists or the search hit ``max_atoms`` — use
    :func:`ltl_decide`/:func:`ltl_countermodel` to tell those apart.

    A sorted constant ``c:S`` lies in ``S`` at every position (see
    :func:`_lift_sorted_constants`). ``timeout`` (milliseconds, default none) ends
    the construction of the atoms and of the graph between them: ``False`` then."""
    plain, seeds = _lift_sorted_constants(list(formulas), mode)
    status, _ = _run(plain + seeds, mode, max_atoms, timeout)
    return status == "unsat"


def ltl_valid(formula: Node, premises: Sequence[Node] = (), mode: str = "initial",
              max_atoms: int = _DEFAULT_MAX_ATOMS, timeout: Optional[int] = None) -> bool:
    """True iff ``premises`` entail ``formula`` under the standard linear-time
    reading — i.e. ``¬((∧ premises) → formula)`` has no model. Sound and
    complete for the supported fragment up to ``max_atoms``; use
    :func:`ltl_decide` to distinguish a genuine "invalid" from "unknown". ``timeout``
    is as for :func:`ltl_tableau_closed`."""
    (goal,), seeds = _lift_sorted_constants([_fold_goal(formula, premises)], mode)
    status, _ = _run([Not(goal)] + seeds, mode, max_atoms, timeout)
    return status == "unsat"


def ltl_decide(formula: Node, premises: Sequence[Node] = (), mode: str = "initial",
               max_atoms: int = _DEFAULT_MAX_ATOMS, timeout: Optional[int] = None) -> str:
    """Decide ``premises ⊨ formula``: ``"valid"`` / ``"invalid"`` / ``"unknown"``.

    * ``"valid"``   — no model of the negation exists (a sound proof).
    * ``"invalid"`` — a witness trace was found AND independently verified by
      :func:`ltl_trace_satisfies` to falsify ``formula`` (at ``witness_position``).
    * ``"unknown"`` — ``max_atoms`` was hit, the ``timeout`` (milliseconds, default
      none) ran out, or (should never happen — an
      internal-consistency safety net, not a real incompleteness source) the
      witness failed independent verification.

    A sorted constant ``c:S`` lies in ``S`` at every position (see
    :func:`_lift_sorted_constants`), and a witness is verified to be such a model.
    """
    (goal,), seeds = _lift_sorted_constants([_fold_goal(formula, premises)], mode)
    status, trace = _run([Not(goal)] + seeds, mode, max_atoms, timeout)
    if status == "unsat":
        return "valid"
    if status == "sat" and trace is not None:
        if (not _trace_satisfies(goal, trace)
                and all(_trace_satisfies(seed, trace) for seed in seeds)):
            return "invalid"
    return "unknown"


def ltl_countermodel(formula: Node, premises: Sequence[Node] = (), mode: str = "initial",
                     max_atoms: int = _DEFAULT_MAX_ATOMS,
                     timeout: Optional[int] = None) -> Optional[LTLTrace]:
    """Return an :class:`LTLTrace` falsifying ``premises ⊨ formula``, or ``None``.

    ``None`` means "valid" (the negation is unsatisfiable) **or** the search
    was inconclusive within ``max_atoms``. The returned trace is verified: it
    is only handed back once :func:`ltl_trace_satisfies` confirms ``formula``
    is false at ``witness_position``, so a countermodel is never spurious. ``timeout``
    is as for :func:`ltl_tableau_closed`.
    """
    (goal,), seeds = _lift_sorted_constants([_fold_goal(formula, premises)], mode)
    status, trace = _run([Not(goal)] + seeds, mode, max_atoms, timeout)
    if status != "sat" or trace is None:
        return None
    if (not _trace_satisfies(goal, trace)
            and all(_trace_satisfies(seed, trace) for seed in seeds)):
        return trace
    return None


# --------------------------------------------------------------------------- #
# ProverBackend registration.
# --------------------------------------------------------------------------- #

from .protocol import ProverBackend, Verdict, PROVED, REFUTED, UNKNOWN  # noqa: E402


class LtlTableauBackend(ProverBackend):
    """This module as a :class:`~unicode_logic_kit.atp.protocol.ProverBackend`.

    Registered under ``"ltl-tableau"``. Tagged ``logics={"modal"}`` for
    discovery alongside ``modal-tableau``/``qml`` (:func:`available_backends`),
    but NOT part of ``default_chain("modal")`` — this backend answers a
    strictly NARROWER question (the standard linear frame) than the rest of
    that chain, so it must be reached by name, exactly like the external
    provers, rather than silently joining a portfolio that assumes a shared
    frame class. It can never REFUTE something ``qml_is_valid`` already
    proved (the linear frame is a strict subset of qml's refl+trans+N⊆T
    frame class, so validity there implies validity here) and it can PROVE
    strictly more (temporal induction — see the module docstring) — so a
    disagreement between this backend and ``qml``/``modal-tableau`` is never
    possible in the unsound direction.
    """

    name = "ltl-tableau"
    logics = frozenset({"modal"})
    external = False

    def available(self) -> bool:
        return True

    def decide(self, formula: Node, premises: Sequence[Node] = (),
               timeout: int = 10000, **options) -> Verdict:
        mode = options.pop("mode", "initial")
        max_atoms = options.pop("max_atoms", _DEFAULT_MAX_ATOMS)
        start = time.perf_counter()
        try:
            status = ltl_decide(formula, premises, mode=mode, max_atoms=max_atoms,
                                timeout=timeout)
        except NotImplementedError as exc:
            return Verdict(UNKNOWN, self.name, logic="modal",
                           reason="unsupported", detail=str(exc))
        elapsed = time.perf_counter() - start
        if status == "valid":
            return Verdict(PROVED, self.name, logic="modal", wall_time=elapsed)
        if status == "invalid":
            # the witness is a second search; it gets what is left of the limit
            trace = ltl_countermodel(formula, premises, mode=mode, max_atoms=max_atoms,
                                     timeout=max(1, int(timeout - elapsed * 1000)))
            witness = trace.to_dict() if trace is not None else None
            return Verdict(REFUTED, self.name, logic="modal", wall_time=elapsed,
                           countermodel=witness)
        if elapsed * 1000 >= timeout:
            return Verdict(UNKNOWN, self.name, logic="modal", reason="timeout",
                           wall_time=elapsed,
                           detail=f"no verdict within the {timeout} ms limit")
        return Verdict(UNKNOWN, self.name, logic="modal", reason="bound_hit",
                       wall_time=elapsed,
                       detail=f"closure exceeded max_atoms={max_atoms}")
