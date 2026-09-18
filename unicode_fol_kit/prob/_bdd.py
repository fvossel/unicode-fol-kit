"""In-house Reduced Ordered BDD (ROBDD) engine — exact weighted model counting.

A minimal, self-contained Boolean-function representation used by
:mod:`unicode_fol_kit.prob.distribution`'s ``method="compile"`` evaluation
route (kept local, mirroring the sibling module's own "no cross-module
dependency" convention — this file has no dependency on ``distribution.py``
or ``nilsson.py``; the dependency runs the other way).

**Representation.** A node is ``(var_index, low, high)``: the Shannon
cofactors of the function when its ``var_index``-th variable is false
(``low``) and true (``high``). Two sentinel integers, :data:`FALSE` = 0 and
:data:`TRUE` = 1, are the terminal nodes; every internal node gets an integer
id >= 2. Nodes are canonicalised through a *unique table*
(:class:`BDDManager._unique`) keyed by ``(var_index, low, high)``, with the
standard ROBDD reduction rule applied on construction: ``low == high``
collapses to that shared child directly (the node is redundant — the
variable doesn't matter) rather than being allocated. Canonicalisation means
structural equality is REFERENCE (id) equality: two BDD node ids are equal
iff the Boolean functions they represent are identical, for any input order
of construction — this is what lets the least-fixpoint loop in
``distribution.py`` detect "no change" by a plain ``!=`` on node ids.

**Fixed variable order, no dynamic reordering.** The order is whatever order
the caller assigns indices in (``distribution.py`` uses the pruned
relevant-fact list order) and never changes — this is a CORRECTNESS tool, not
a competitive weighted-model-counting engine; a bad order can blow up node
counts where a good order collapses them, and no attempt is made here to
find (or shuffle into) a good one. The :data:`max_bdd_nodes`-style brake
(``max_nodes`` below) exists precisely because worst-case Boolean functions
have exponentially many ROBDD nodes under ANY fixed order — weighted model
counting is #P-hard, so no algorithm (fixed-order ROBDDs included) escapes
that in general; this module refuses loudly rather than silently grinding.

**AND / OR** are the standard memoized recursive Shannon-expansion ``apply``:
recurse on the pair's earlier (smaller-index) top variable, combine the
cofactored results, and re-canonicalise via the unique table. **NOT** is
deliberately NOT built as ``ite(f, FALSE, TRUE)`` through that same
general two-argument machinery; it is its own single-argument memoized
recursion whose base case is exactly a 0/1-terminal swap (``NOT(FALSE) =
TRUE``, ``NOT(TRUE) = FALSE``) and whose recursive case swaps the same two
terminals arbitrarily far down the DAG, memoized per node id so any node's
negation is built (or looked up) once no matter how many times it is asked
for — cheaper, and simpler to verify correct, than routing every negation
through the ternary apply used for AND/OR.

Public API: :data:`FALSE`, :data:`TRUE`, :class:`BDDManager`,
:func:`weighted_model_count`.
"""

from fractions import Fraction
from typing import Dict, List, Sequence, Tuple

__all__ = ["FALSE", "TRUE", "BDDManager", "weighted_model_count"]


FALSE: int = 0
TRUE: int = 1


class BDDManager:
    """Owns one ROBDD's node universe over a fixed set of ``num_vars`` Boolean variables.

    ``variable(i)`` returns the (canonical, cached) single-variable node for
    variable ``i``; :meth:`AND`, :meth:`OR`, :meth:`NOT` combine existing
    nodes into new canonical ones. ``max_nodes`` bounds the TOTAL node count
    (the two terminals plus every internal node ever allocated) — the same
    style of loud, explicit, overridable brake
    :func:`~unicode_fol_kit.prob.distribution.query`'s ``max_choice_facts``
    already is for the enumeration route, here for the compiled route's own
    failure mode (node blow-up instead of choice-count blow-up).
    """

    def __init__(self, num_vars: int, *, max_nodes: int = 100_000):
        if num_vars < 0:
            raise ValueError(f"BDDManager: num_vars must be >= 0, got {num_vars}.")
        if max_nodes < 2:
            raise ValueError(f"BDDManager: max_nodes must be >= 2 (room for both terminals), got {max_nodes}.")
        self.num_vars = num_vars
        self.max_nodes = max_nodes
        # Internal node id `n` (n >= 2) is stored at self._nodes[n - 2]; ids 0
        # and 1 are the FALSE/TRUE terminals and are never stored here.
        self._nodes: List[Tuple[int, int, int]] = []
        self._unique: Dict[Tuple[int, int, int], int] = {}
        self._and_memo: Dict[Tuple[int, int], int] = {}
        self._or_memo: Dict[Tuple[int, int], int] = {}
        self._not_memo: Dict[int, int] = {}
        self._var_nodes: List[int] = [self._make_node(i, FALSE, TRUE) for i in range(num_vars)]

    # -- construction -------------------------------------------------------

    def variable(self, index: int) -> int:
        """Return the canonical node for "variable ``index`` is true" alone."""
        if not (0 <= index < self.num_vars):
            raise ValueError(f"BDDManager: variable index {index} out of range [0, {self.num_vars}).")
        return self._var_nodes[index]

    def node(self, node_id: int) -> Tuple[int, int, int]:
        """Return ``(var_index, low, high)`` for an internal node id (never a terminal)."""
        if self.is_terminal(node_id):
            raise ValueError(f"BDDManager.node: {node_id} is a terminal, not an internal node id.")
        return self._nodes[node_id - 2]

    def is_terminal(self, node_id: int) -> bool:
        return node_id == FALSE or node_id == TRUE

    def size(self) -> int:
        """Total node count so far, terminals included (what ``max_nodes`` bounds)."""
        return len(self._nodes) + 2

    def _make_node(self, var: int, low: int, high: int) -> int:
        """Canonical constructor: reduction rule, then unique-table dedup, then the brake."""
        if low == high:
            return low
        key = (var, low, high)
        existing = self._unique.get(key)
        if existing is not None:
            return existing
        new_id = len(self._nodes) + 2
        if new_id >= self.max_nodes:
            raise ValueError(
                f"BDDManager: node count would exceed max_nodes={self.max_nodes}. "
                "Weighted model counting is #P-hard -- worst-case Boolean functions have "
                "exponentially many ROBDD nodes under any fixed variable order, so no "
                "algorithm escapes that blow-up in general; reduce the program, tighten "
                "the goal (which tightens dependency-cone pruning), or pass a larger "
                "max_bdd_nodes explicitly if that blow-up is intended."
            )
        self._nodes.append(key)
        self._unique[key] = new_id
        return new_id

    def _top_var(self, node: int) -> int:
        """The node's own variable index, or ``num_vars`` (past every real variable) for a terminal."""
        return self.num_vars if self.is_terminal(node) else self._nodes[node - 2][0]

    def _cofactor(self, node: int, var: int) -> Tuple[int, int]:
        """``(node|var=False, node|var=True)``: the node's own children if it tests ``var``, else unchanged."""
        if self.is_terminal(node) or self._nodes[node - 2][0] != var:
            return node, node
        _, low, high = self._nodes[node - 2]
        return low, high

    # -- Boolean combinators --------------------------------------------------

    def AND(self, a: int, b: int) -> int:
        """Conjunction of two nodes; memoized recursive Shannon-expansion apply."""
        if a == FALSE or b == FALSE:
            return FALSE
        if a == TRUE:
            return b
        if b == TRUE:
            return a
        if a == b:
            return a
        key = (a, b) if a <= b else (b, a)
        cached = self._and_memo.get(key)
        if cached is not None:
            return cached
        top = min(self._top_var(a), self._top_var(b))
        a_lo, a_hi = self._cofactor(a, top)
        b_lo, b_hi = self._cofactor(b, top)
        result = self._make_node(top, self.AND(a_lo, b_lo), self.AND(a_hi, b_hi))
        self._and_memo[key] = result
        return result

    def OR(self, a: int, b: int) -> int:
        """Disjunction of two nodes; memoized recursive Shannon-expansion apply."""
        if a == TRUE or b == TRUE:
            return TRUE
        if a == FALSE:
            return b
        if b == FALSE:
            return a
        if a == b:
            return a
        key = (a, b) if a <= b else (b, a)
        cached = self._or_memo.get(key)
        if cached is not None:
            return cached
        top = min(self._top_var(a), self._top_var(b))
        a_lo, a_hi = self._cofactor(a, top)
        b_lo, b_hi = self._cofactor(b, top)
        result = self._make_node(top, self.OR(a_lo, b_lo), self.OR(a_hi, b_hi))
        self._or_memo[key] = result
        return result

    def NOT(self, a: int) -> int:
        """Negation, via a dedicated memoized unary 0/1-terminal-swap recursion (see module docstring)."""
        if a == FALSE:
            return TRUE
        if a == TRUE:
            return FALSE
        cached = self._not_memo.get(a)
        if cached is not None:
            return cached
        var, low, high = self._nodes[a - 2]
        result = self._make_node(var, self.NOT(low), self.NOT(high))
        self._not_memo[a] = result
        return result


def weighted_model_count(manager: BDDManager, root: int, weights: Sequence[Fraction]) -> Fraction:
    """Exact weighted model count of ``root``, ``weights[i]`` the weight of "variable ``i`` true".

    ``WMC(node) = p_v * WMC(high) + (1 - p_v) * WMC(low)``, terminals
    ``TRUE -> 1``, ``FALSE -> 0``, memoized bottom-up over the node DAG so
    every SHARED node is priced exactly once. That sharing is the entire
    performance claim of the compiled route: a chain/tree/diamond-shaped
    program collapses to ``O(#nodes)`` here instead of the ``O(2^k)`` exact
    weights the enumeration route sums for the same answer. Arithmetic is
    exact ``Fraction`` throughout, never a float.
    """
    memo: Dict[int, Fraction] = {FALSE: Fraction(0), TRUE: Fraction(1)}

    def rec(node: int) -> Fraction:
        cached = memo.get(node)
        if cached is not None:
            return cached
        var, low, high = manager.node(node)
        p = weights[var]
        value = p * rec(high) + (Fraction(1) - p) * rec(low)
        memo[node] = value
        return value

    return rec(root)
