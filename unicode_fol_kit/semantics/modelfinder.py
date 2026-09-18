"""Finite model finder — search for a finite model (or countermodel) of a theory.

The complement of the provers: where ``prove`` / ``is_valid`` answer *"does it
follow?"*, this answers *"is there a structure where it holds?"* by brute-force
enumeration of finite :class:`~unicode_fol_kit.semantics.tarski.Structure`\\ s over a
domain ``{0, 1, …, k-1}`` for increasing ``k``, checking each with the Tarskian
evaluator. It is the Mace4-style partner of the resolution prover: a valid entailment
has *no* countermodel, an invalid one usually has a small finite one.

- :func:`find_model` — a finite model satisfying every formula of a theory, or None.
- :func:`find_countermodel` — a finite structure satisfying ``premises`` but not
  ``conclusion`` (a witness that the entailment fails), or None.
- :func:`is_satisfiable_finite` / :func:`is_valid_finite` — the boolean wrappers.

Free variables are read as universally quantified (each formula is universally
closed). The search is **bounded**: a domain size whose interpretation space exceeds
``max_candidates`` is skipped, so ``None`` means "no model found within the bounds",
not "unsatisfiable" (first-order satisfiability is undecidable, and some satisfiable
sentences have only infinite models).

**Symmetry breaking (``symmetry_breaking=True``, the default).** The raw enumeration
below revisits every one of a domain's ``k!`` relabelings of the same underlying
structure — a named-constant-heavy signature spends almost its whole budget on
interpretations that differ only by *which* domain element happens to be called
``0`` versus ``1``. :func:`_canonical_interpretations` applies the classical
**least-number heuristic (LNH)** to CONSTANT assignments (a constant has no
argument tuple — it is simply "choose one of ``k`` interchangeable labels" — so a
global relabeling acts on it cleanly): they are filled by backtracking in
canonical (sorted) name order, each one taking either an already-used domain value
or the smallest still-unused one — never skipping ahead to a "fresh" element out of
order. That visits exactly one representative per isomorphism class of constant
assignments instead of ``k!`` of them. FUNCTION and PREDICATE tables are still
enumerated exhaustively per accepted constant skeleton — see
:func:`_canonical_interpretations`'s docstring both for why the search stays
complete regardless, and for why functions are NOT also LNH-reduced (a roadmap
draft called for that too, and it is unsound — a hand-checked counterexample is in
the same docstring). Pass ``symmetry_breaking=False`` to fall back to the plain
:func:`_interpretations` enumeration (kept unchanged, e.g. for differential
testing against the canonical generator). MSFOL (sorted) search is unaffected either
way — :func:`_sorted_interpretations` has no LNH pass (see its own scope note).

**Many-sorted (MSFOL)** input is handled directly: each named sort gets a non-empty
universe (a non-empty subset of the domain) enumerated alongside the rest of the
interpretation, sorted constants are placed inside their sort, and a
``SortedQuantifier`` ranges over its sort — so a found :class:`Structure` carries the
``sorts`` mapping. Sorts may overlap (the relativisation reading).

**Subsorting** (``subsorts``, optional, every public function below). A subsort
edge ``S -> {T}`` (child sort name -> its DIRECT parent sort names — the same
shape as :attr:`unicode_fol_kit.fol.signature.Signature.subsorts`, and typically
passed as exactly that attribute) means every accepted universe assignment must
satisfy ``set(sorts[S]) <= set(sorts[T])`` — the SAME subset-semantics reading
``fol.to_fol``'s emitted axioms and ``Signature.validate`` enforce elsewhere (see
that module's "Subsorting" docstring section), so all three routes agree on what
a subsort edge means. :func:`_sorted_interpretations` enforces this by filtering,
not by a new search algorithm — but, UNLIKE ``fol.to_fol``, it cannot rely on
DIRECT edges alone: this module's :class:`_Signature` only gives a sort its own
universe when that sort is actually USED by a sorted binder somewhere in the
theory, so a chain ``S < T < U`` where ``T`` is never otherwise mentioned would
silently lose the ``S ⊆ U`` consequence if only direct parents were checked
(``to_fol`` avoids this because it always emits a guard predicate for every
declared sort regardless of usage, letting direct-edge implications chain on
their own — see :func:`_subsort_closure`'s docstring for the full contrast).
:func:`_sorted_interpretations` instead computes the FULL TRANSITIVE closure of
``subsorts`` once per search (:func:`_subsort_closure`) and skips a
``sort_choice`` combination whose universes violate ANY closure pair present in
the theory's own signature, before its constants/functions/predicates are even
enumerated (see :func:`_respects_subsorts`). Only sorts occurring in this
theory's OWN signature are checked; an
edge naming an irrelevant sort is silently ignored, mirroring ``to_fol``'s own
"omitting it is byte-identical" convention. This is a pure filter over an
unchanged enumeration, so it never affects the ``max_candidates`` pre-flight
check's honesty contract (see ``find_model``'s docstring) — a size is still
either fully searched or fully skipped, never partially.

Public API: :func:`find_model`, :func:`find_countermodel`,
:func:`is_satisfiable_finite`, :func:`is_valid_finite`, :func:`is_size_exhaustive`.
"""

from itertools import product
from typing import Dict, FrozenSet, Iterable, List, Mapping, Optional

from ..fol.nodes import Node, Atom, Not, Quantifier, Variable, Constant, Number, Function
from ..fol.nodes import SortedConstant, SortedQuantifier
from ..fol.nodes import Count, Cardinality, SortedCount, SortedCardinality
from ..fol.nodes import SlashedExists, Measure
from .tarski import Structure, models, _MEASURE_FUNC


#: Node types that bind a logical variable over a ``formula`` scope — the quantifiers,
#: the counting quantifiers and cardinality terms (and their sorted variants), and the
#: IF-logic slashed existential.
_VAR_BINDERS = (Quantifier, SortedQuantifier, Count, Cardinality,
                SortedCount, SortedCardinality, SlashedExists)

#: The subset of the above that additionally names a sort the structures must interpret.
_SORTED_BINDERS = (SortedQuantifier, SortedCount, SortedCardinality)


MAX_CANDIDATES = 1 << 20  # ~1M structures per domain size before a size is skipped


# ---------------------------------------------------------------------------
# Free-variable closure and signature collection
# ---------------------------------------------------------------------------

def _free_var_names(node: Node, bound: frozenset = frozenset()) -> set:
    """Return the names of variables occurring free in ``node``."""
    if isinstance(node, Variable):
        return set() if node.name in bound else {node.name}
    if isinstance(node, SlashedExists):
        # The slash set names ENCLOSING binders, so those names are free here (and
        # are not shadowed by this binder's own variable).
        inner = _free_var_names(node.formula, bound | {node.variable.name})
        return inner | {n for n in node.slashed if n not in bound}
    if isinstance(node, _VAR_BINDERS):
        return _free_var_names(node.formula, bound | {node.variable.name})
    names: set = set()
    for child in node._child_nodes():
        names |= _free_var_names(child, bound)
    return names


def _universal_closure(node: Node) -> Node:
    """Wrap ``node`` in ∀ for each free variable (deterministic order)."""
    result = node
    for name in sorted(_free_var_names(node), reverse=True):
        result = Quantifier("∀", Variable(name), result)
    return result


class _Signature:
    """The constants, functions, predicates, and sorts a theory's structures interpret."""

    def __init__(self):
        self.constants: set = set()                 # names
        self.functions: set = set()                 # (name, arity)
        self.predicates: set = set()                # (name, arity)
        self.sorts: set = set()                      # sort names (MSFOL)
        self.sorted_constants: dict = {}             # constant name -> sort name

    def scan(self, node: Node) -> None:
        if isinstance(node, SortedConstant):
            self.constants.add(node.name)
            self.sorts.add(node.sort)
            self.sorted_constants[node.name] = node.sort
        elif isinstance(node, Constant):
            self.constants.add(node.name)
        elif isinstance(node, Number):
            self.constants.add(str(node.value))
        elif isinstance(node, Function):
            self.functions.add((node.name, len(node.args)))
            for a in node.args:
                self.scan(a)
        elif isinstance(node, Measure):
            # μ(entity, dimension) denotes the binary function ``measure`` — the same
            # symbol Measure.to_z3 / to_prover9 emit, so a structure found here
            # interprets what the provers see. The dimension is an ordinary term.
            self.functions.add(_MEASURE_FUNC)
            self.scan(node.entity)
            self.scan(node.dimension)
        elif isinstance(node, Atom):
            if node.predicate not in ("=", "≠"):     # identity is built in
                self.predicates.add((node.predicate, len(node.args)))
            for a in node.args:
                self.scan(a)
        elif isinstance(node, _VAR_BINDERS):
            # Scan only the scope: a binder's ``variable`` is not a signature symbol,
            # and a Count's ``n`` is a cardinality bound, not an individual — walking
            # the children generically would register it as a domain constant.
            if isinstance(node, _SORTED_BINDERS):
                self.sorts.add(node.sort)
            self.scan(node.formula)
        else:
            for child in node._child_nodes():
                self.scan(child)


# ---------------------------------------------------------------------------
# Enumeration of finite interpretations
# ---------------------------------------------------------------------------

def _candidate_count(sig: "_Signature", k: int) -> int:
    """The number of distinct interpretations of ``sig`` over a ``k``-element domain."""
    total = k ** len(sig.constants)
    for _, arity in sig.functions:
        total *= k ** (k ** arity)
    for _, arity in sig.predicates:
        total *= 1 << (k ** arity)
    # Each sort ranges over the non-empty subsets of the domain (its universe).
    for _ in sig.sorts:
        total *= (1 << k) - 1
    return total


def _lnh_constant_count(n_slots: int, k: int) -> int:
    """The EXACT number of LNH-canonical constant assignments for ``n_slots``
    constants over a ``k``-element domain — the count :func:`_canonical_interpretations`
    actually yields for its constant part, computed analytically (``O(n_slots * k)``
    arithmetic, no enumeration) so :func:`_canonical_candidate_count` never needs to
    fall back to a live count just to decide whether a size fits ``max_candidates``.

    Equivalently, this counts the "restricted growth strings" :func:`_lnh_choices`
    generates: a value may repeat any of the ``j`` already-used domain indices, or
    introduce exactly the next unused one (if ``j < k``). ``dp[j]`` tracks, working
    backward from the last slot, "ways to fill the remaining slots given ``j``
    distinct values already committed" — the same recursion the backtracking
    generator walks, just summed instead of enumerated. (This is the number of set
    partitions of an ``n_slots``-element set into at most ``k`` blocks, i.e.
    ``sum_{j=1}^{min(n_slots, k)} S(n_slots, j)`` in Stirling-number-of-the-second-kind
    terms — hand-checked for n_slots=2,k=2 -> 2 and n_slots=3,k=2 -> 4 in
    ``tests/test_modelfinder_symmetry.py``.)
    """
    if n_slots == 0:
        return 1
    dp = [1] * (k + 1)  # boundary: 0 slots left to fill is 1 way, for every j
    for _ in range(n_slots):
        new_dp = [0] * (k + 1)
        for j in range(k + 1):
            total = j * dp[j]              # repeat one of the j already-used values
            if j < k:
                total += dp[j + 1]          # or introduce the next still-unused one
            new_dp[j] = total
        dp = new_dp
    return dp[0]


def _canonical_candidate_count(sig: "_Signature", k: int) -> int:
    """The EXACT number of interpretations :func:`_canonical_interpretations` yields
    for ``sig`` over a ``k``-element domain — the analytic pre-flight count backing
    ``find_model``'s "skip this size" check when ``symmetry_breaking=True``, playing
    the same role :func:`_candidate_count` plays for the unbroken enumeration.

    Only the constants factor changes, from ``k ** len(sig.constants)`` to
    :func:`_lnh_constant_count`'s LNH-reduced count; functions, predicates and sorts
    keep the exact same raw factors :func:`_candidate_count` uses, because
    :func:`_canonical_interpretations` leaves those fully exhaustive (see its
    docstring). Being exact (not an estimate) means the pre-flight check alone
    decides whether a size is searched — no live count-and-break loop is needed
    inside the search itself, which is what makes the check safe to run
    unconditionally: a signature with few or no constants (where LNH gives little
    or no reduction) is skipped exactly as cheaply, and exactly as correctly, as it
    was under :func:`_candidate_count` before symmetry breaking existed.
    """
    total = _lnh_constant_count(len(sig.constants), k)
    for _, arity in sig.functions:
        total *= k ** (k ** arity)
    for _, arity in sig.predicates:
        total *= 1 << (k ** arity)
    # sig.sorts is always empty here (_canonical_interpretations raises otherwise),
    # kept parallel to _candidate_count's shape for clarity and future-proofing.
    for _ in sig.sorts:
        total *= (1 << k) - 1
    return total


def _nonempty_subsets(domain: tuple):
    """Yield every non-empty subset of ``domain`` as a tuple (a sort universe)."""
    items = list(domain)
    for mask in range(1, 1 << len(items)):
        yield tuple(items[i] for i in range(len(items)) if (mask >> i) & 1)


def _func_pred_interpretations(sig: "_Signature", domain: tuple):
    """Yield ``(functions, predicates)`` for every interpretation of the func/pred part."""
    func_sig = sorted(sig.functions)
    pred_sig = sorted(sig.predicates)
    func_options = []
    for _, arity in func_sig:
        arg_tuples = list(product(domain, repeat=arity))
        func_options.append(list(product(domain, repeat=len(arg_tuples))))
    pred_options = []
    for _, arity in pred_sig:
        arg_tuples = list(product(domain, repeat=arity))
        pred_options.append(list(product((False, True), repeat=len(arg_tuples))))
    for func_choice in (product(*func_options) if func_options else [()]):
        functions = {}
        for (name, arity), values in zip(func_sig, func_choice):
            arg_tuples = list(product(domain, repeat=arity))
            functions[(name, arity)] = dict(zip(arg_tuples, values))
        for pred_choice in (product(*pred_options) if pred_options else [()]):
            predicates = {}
            for (name, arity), mask in zip(pred_sig, pred_choice):
                arg_tuples = list(product(domain, repeat=arity))
                predicates[(name, arity)] = {t for t, inc in zip(arg_tuples, mask) if inc}
            yield functions, predicates


def _subsort_closure(subsorts: Mapping[str, FrozenSet[str]]) -> Dict[str, FrozenSet[str]]:
    """The reflexive-free TRANSITIVE closure of a DIRECT subsort-edges
    mapping — child sort name -> every ancestor reachable by chaining one or
    more edges, regardless of whether that ancestor (or any sort along the
    chain) is otherwise mentioned anywhere in the theory being searched.

    This is NOT the same "direct edges are enough" story ``fol.to_fol``'s
    axiom emission tells: ``to_fol`` can rely on direct edges alone because
    it ALWAYS emits one implication axiom per declared edge into the SAME
    classical signature, so an intermediate sort's guard predicate ``B`` is
    still present (as an ordinary, if otherwise-unconstrained, predicate
    symbol) for the chain ``A(x) → B(x)`` and ``B(x) → C(x)`` to compose
    into ``A(x) → C(x)``. This module's :class:`_Signature` (see
    :meth:`_Signature.scan`), by contrast, only gives a sort ITS OWN universe
    in a searched :class:`~unicode_fol_kit.semantics.tarski.Structure` when
    that sort is actually USED (by a sorted binder) somewhere in the theory
    — a theory built from ``∃x:A ∀y:C (x ≠ y)`` alone never mentions ``B`` at
    all, so a check limited to DIRECT edges would silently miss the
    ``A ⊆ C`` consequence whenever the chain passes through such an unused
    intermediate sort (review-confirmed: this is exactly the gap that made
    an earlier, direct-edges-only version of this filter disagree with the
    ``to_fol`` + Z3 route on a hand-built two-level-chain case). Computing
    the full closure and checking every ancestor PRESENT in the theory's own
    signature — not just DIRECT parents — closes that gap while still
    reading ``subsorts`` in the same DIRECT-edges shape
    :attr:`~unicode_fol_kit.fol.signature.Signature.subsorts` stores it in.

    Assumed acyclic (never independently re-checked here — a caller passing
    a real :class:`~unicode_fol_kit.fol.signature.Signature`'s own
    ``.subsorts`` already had it refused at construction time on a cycle);
    a cycle in a hand-built raw mapping simply stops contributing further
    ancestors once revisited, rather than raising or looping forever.
    """
    memo: Dict[str, FrozenSet[str]] = {}

    def closure_of(node: str, visiting: FrozenSet[str]) -> FrozenSet[str]:
        if node in memo:
            return memo[node]
        if node in visiting:
            return frozenset()
        ancestors: set = set()
        for parent in subsorts.get(node, frozenset()):
            ancestors.add(parent)
            ancestors |= closure_of(parent, visiting | {node})
        memo[node] = frozenset(ancestors)
        return memo[node]

    for node in subsorts:
        closure_of(node, frozenset())
    return memo


def _respects_subsorts(sorts: dict, closure: Mapping[str, FrozenSet[str]]) -> bool:
    """True iff every ancestor edge in the subsort CLOSURE (see
    :func:`_subsort_closure`) is honoured by ``sorts`` (sort name -> its
    universe, as one ``sort_choice`` assigns it):
    ``set(sorts[child]) <= set(sorts[ancestor])`` for every
    ``(child, ancestor)`` pair the closure names.

    A pair naming a sort absent from ``sorts`` (this theory never mentions
    it) is silently skipped — there is no universe to compare, and a theory
    that never uses that sort must decide identically whether or not the
    caller's full :class:`~unicode_fol_kit.fol.signature.Signature` happens
    to declare an edge for it (mirrors ``fol.to_fol``'s own "irrelevant
    edges change nothing" convention).
    """
    for child, ancestors in closure.items():
        if child not in sorts:
            continue
        child_universe = set(sorts[child])
        for ancestor in ancestors:
            if ancestor not in sorts:
                continue
            if not child_universe <= set(sorts[ancestor]):
                return False
    return True


def _sorted_interpretations(sig: "_Signature", domain: tuple,
                            subsorts: Optional[Mapping[str, FrozenSet[str]]] = None):
    """Yield ``(constants, functions, predicates, sorts)`` for an MSFOL signature.

    Each sort gets a non-empty universe (a non-empty subset of the domain); a sorted
    constant is restricted to its sort's universe; the rest is the classical
    enumeration. Sorts may overlap (the relativisation reading) — UNLESS
    ``subsorts`` (or its transitive closure — see :func:`_subsort_closure`)
    declares an edge between them, in which case every yielded ``sort_choice``
    must additionally satisfy that edge's subset constraint (see
    :func:`_respects_subsorts` and the module docstring's "Subsorting"
    section); a combination that fails is skipped before its
    constants/functions/predicates are enumerated at all.
    """
    sort_names = sorted(sig.sorts)
    const_names = sorted(sig.constants)
    sort_options = [list(_nonempty_subsets(domain)) for _ in sort_names]
    closure = _subsort_closure(subsorts) if subsorts else None
    for sort_choice in (product(*sort_options) if sort_options else [()]):
        sorts = {name: universe for name, universe in zip(sort_names, sort_choice)}
        if closure and not _respects_subsorts(sorts, closure):
            continue
        const_option_lists = [
            list(sorts[sig.sorted_constants[name]]) if name in sig.sorted_constants
            else list(domain)
            for name in const_names
        ]
        for const_choice in (product(*const_option_lists) if const_option_lists else [()]):
            constants = dict(zip(const_names, const_choice))
            for functions, predicates in _func_pred_interpretations(sig, domain):
                yield constants, functions, predicates, sorts


def _interpretations(sig: "_Signature", domain: tuple):
    """Yield ``(constants, functions, predicates)`` dicts for every interpretation."""
    k = len(domain)
    const_names = sorted(sig.constants)
    func_sig = sorted(sig.functions)
    pred_sig = sorted(sig.predicates)

    # Per-symbol option lists.
    const_options = list(product(domain, repeat=len(const_names)))
    func_options = []
    for _, arity in func_sig:
        arg_tuples = list(product(domain, repeat=arity))
        func_options.append(list(product(domain, repeat=len(arg_tuples))))
    pred_options = []
    for _, arity in pred_sig:
        arg_tuples = list(product(domain, repeat=arity))
        pred_options.append(list(product((False, True), repeat=len(arg_tuples))))

    for const_choice in const_options:
        constants = dict(zip(const_names, const_choice))
        for func_choice in (product(*func_options) if func_options else [()]):
            functions = {}
            for (name, arity), values in zip(func_sig, func_choice):
                arg_tuples = list(product(domain, repeat=arity))
                functions[(name, arity)] = dict(zip(arg_tuples, values))
            for pred_choice in (product(*pred_options) if pred_options else [()]):
                predicates = {}
                for (name, arity), mask in zip(pred_sig, pred_choice):
                    arg_tuples = list(product(domain, repeat=arity))
                    predicates[(name, arity)] = {
                        t for t, inc in zip(arg_tuples, mask) if inc
                    }
                yield constants, functions, predicates


# ---------------------------------------------------------------------------
# LNH symmetry breaking (roadmap C23)
# ---------------------------------------------------------------------------

def _lnh_choices(next_new: int, k: int):
    """The domain-VALUE choices for one least-number-heuristic (LNH) table cell.

    ``next_new`` is how many distinct domain values earlier cells (in canonical
    symbol order) have already used. A cell may repeat any of them (indices
    ``0 .. next_new - 1``) or introduce exactly the next still-unused one (index
    ``next_new``, if the ``k``-element domain has one left) — never a value further
    out, which would let two candidates differ only in *which* arbitrary index a
    fresh domain element happens to receive. Every ``k!`` relabeling of an
    argument-free assignment (a constant, or free_logic's partial constant) collapses
    to the single one built by always picking the least eligible index at each cell
    (a restricted-growth-string argument), which is exactly what makes
    :func:`_canonical_interpretations` visit one candidate per isomorphism class of
    constant assignments instead of ``k!`` (this cap is safe ONLY for argument-free
    cells — see :func:`_canonical_interpretations`'s docstring for why a function's
    table cells, indexed by an argument tuple, are a different, unsound case).

    Shared, single-source bookkeeping for both
    :func:`_canonical_interpretations` here and
    :func:`~unicode_fol_kit.semantics.free_logic._canonical_partial_interpretations`
    (which additionally offers a non-denoting choice alongside this range — see its
    own docstring for why that choice is exempt from the relabeling argument).
    """
    return range(min(next_new + 1, k))


def _canonical_interpretations(sig: "_Signature", domain: tuple):
    """Yield ``(constants, functions, predicates)`` with LNH symmetry breaking.

    A drop-in structural match for :func:`_interpretations` (same yielded shape,
    same scanned signature): CONSTANT assignments are filled by backtracking in
    canonical (sorted) name order, each cell's choice capped by
    :func:`_lnh_choices` — any already-used domain value, or exactly the next
    still-unused one. A constant has no argument tuple, so it is exactly "choose
    one of ``k`` interchangeable labels", and LNH's restricted-growth-string
    argument applies to it cleanly: every ``k!`` relabeling of a constant
    assignment collapses to the single one built by always picking the least
    eligible index, so this generator visits one candidate per isomorphism class
    of constant assignments instead of (up to) ``k!`` of them.

    FUNCTION and PREDICATE tables are still enumerated exhaustively per accepted
    constant skeleton, via :func:`_func_pred_interpretations` (the same helper
    :func:`_sorted_interpretations` already uses) — **deliberately**, not as an
    afterthought. A roadmap draft for this generator (C23) described applying the
    identical per-cell LNH cap to FUNCTION table cells too, in canonical
    ``(name, arity, arg_tuple)`` order; that is UNSOUND and was caught by this
    module's own differential test (``tests/test_modelfinder_symmetry.py``), so it
    is deliberately not implemented — see the deviation note below. Predicates
    were always intended to stay exhaustive (codomain ``{0, 1}``, not the domain),
    so leaving BOTH functions and predicates exhaustive keeps this generator
    trivially sound and COMPLETE by the same argument the roadmap already gives for
    predicates: for any raw interpretation ``I``, some domain permutation ``π``
    makes ``π(I)``'s constant part LNH-canonical, and because the function and
    predicate parts here range over their FULL, unrestricted space regardless of
    what the constants happen to be, ``π(I)``'s function/predicate part is
    generated too — so this generator yields a structure isomorphic to ``I`` for
    every ``I`` :func:`_interpretations` would yield.

    **Deviation from the roadmap draft — why functions are NOT LNH-reduced here.**
    A function's table cell is indexed by an ARGUMENT TUPLE, which is itself made
    of domain elements — so a domain permutation ``π`` does not just relabel a
    cell's *value* (as for a constant), it also moves WHICH cell holds an entry
    (the cell at argument tuple ``t`` moves to argument tuple ``π(t)``). A flat,
    per-cell LNH cap in a FIXED argument order (as the draft described) ignores
    that second effect and is provably incomplete: on a 2-element domain with a
    single unary function ``f`` and no constants, the "swap" table ``f(0)=1,
    f(1)=0`` is its own isomorphism class (both domain permutations fix it — try
    them), yet the draft's scheme forces cell ``f(0)`` to be ``0`` on the very
    first choice, so that legitimate, non-isomorphic-to-anything-else table is
    never produced by *any* permutation of it. A sound LNH pass for functions
    would need to process argument tuples in a REACHABILITY order tied to element
    discovery (walk the term structure generated from the constants through the
    functions, à la classical Mace-/Paradox-style model builders), not a fixed
    domain-lexicographic argument order — a materially larger undertaking left to
    future work, alongside the predicate-aware automorphism group the roadmap
    itself already scoped out. Leaving functions exhaustive is the SOUND choice;
    reducing them incorrectly would silently turn "no model found" into a false
    negative, which this module refuses to risk.

    ``sig.sorts`` must be empty — MSFOL search has no LNH pass in v1 (a sort's
    universe is an arbitrary domain SUBSET, so its automorphism group depends on
    the sort partition — a materially harder variant, left to
    :func:`_sorted_interpretations`, unchanged).
    """
    if sig.sorts:
        raise ValueError(
            "_canonical_interpretations: sig.sorts is non-empty; MSFOL (sorted) "
            "search has no LNH pass — use _sorted_interpretations instead."
        )
    k = len(domain)
    const_names = sorted(sig.constants)
    n_slots = len(const_names)

    def backtrack(i: int, next_new: int, values: list):
        if i == n_slots:
            constants = dict(zip(const_names, (domain[v] for v in values)))
            for functions, predicates in _func_pred_interpretations(sig, domain):
                yield constants, functions, predicates
            return
        for v in _lnh_choices(next_new, k):
            values.append(v)
            new_next = next_new + 1 if v == next_new else next_new
            yield from backtrack(i + 1, new_next, values)
            values.pop()

    yield from backtrack(0, 0, [])


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------

def find_model(formulas, max_size: int = 4,
               max_candidates: int = MAX_CANDIDATES,
               symmetry_breaking: bool = True,
               subsorts: Optional[Mapping[str, FrozenSet[str]]] = None) -> Optional[Structure]:
    """Return a finite :class:`Structure` satisfying every formula, or None.

    Searches domains of size ``1 .. max_size`` in turn, enumerating every
    interpretation of the theory's signature and returning the first structure in
    which all formulas hold.

    ``subsorts`` (default ``None``, no constraint) additionally requires every
    searched universe assignment to honour the given DIRECT subsort edges — see
    the module docstring's "Subsorting" section. Typically the ``.subsorts`` of a
    :class:`~unicode_fol_kit.fol.signature.Signature` the caller already has.
    Ignored entirely for an unsorted theory (``sig.sorts`` empty), exactly like
    ``fol.to_fol``'s own ``signature=`` parameter is a no-op on a theory with no
    sorted nodes.

    ``symmetry_breaking`` (default True) enumerates CONSTANT assignments with the
    LNH generator, :func:`_canonical_interpretations`, instead of the plain
    :func:`_interpretations` — see the module docstring. Because the LNH-reduced
    candidate count for a size can be far below the ANALYTIC (unbroken) count
    :func:`_candidate_count` computes, the pre-flight "skip this size" check uses
    :func:`_canonical_candidate_count` instead — the EXACT count of what the
    canonical generator will yield, computed analytically in
    ``O(n_constants * domain size)`` arithmetic, with no enumeration and no model
    checking. This is deliberately an O(1)-per-size analytic check, not a live
    count of the generator: a signature with few or no constants (where LNH cannot
    reduce anything — functions and predicates stay fully exhaustive either way)
    is skipped exactly as cheaply as it was before symmetry breaking existed,
    instead of paying to enumerate and model-check up to ``max_candidates``
    structures on every size just to discover that a function- or
    predicate-dominated signature was never going to fit the budget. A size still
    only counts as "searched" if its exact canonical count is ``<= max_candidates``
    (so it is always FULLY enumerated, never truncated mid-generator), preserving
    the existing "no model found within the bounds" (never a false negative)
    honesty contract. With ``symmetry_breaking=False`` the search is byte-for-byte
    the original exhaustive one (the analytic pre-flight check, then
    :func:`_interpretations`), kept available for differential testing against the
    canonical generator.
    Many-sorted (MSFOL) signatures are unaffected by this flag either way — sorted
    search always uses the unbroken :func:`_sorted_interpretations` (see its own
    scope note in the module docstring).
    """
    sentences = [_universal_closure(f) for f in formulas]
    sig = _Signature()
    for s in sentences:
        sig.scan(s)
    for k in range(1, max_size + 1):
        domain = tuple(range(k))
        if sig.sorts:
            if _candidate_count(sig, k) > max_candidates:
                continue
            for constants, functions, predicates, sorts in _sorted_interpretations(
                sig, domain, subsorts):
                structure = Structure(domain, constants=constants, functions=functions,
                                      predicates=predicates, sorts=sorts)
                if all(models(s, structure) for s in sentences):
                    return structure
        elif symmetry_breaking:
            if _canonical_candidate_count(sig, k) > max_candidates:
                continue
            for constants, functions, predicates in _canonical_interpretations(sig, domain):
                structure = Structure(domain, constants=constants,
                                      functions=functions, predicates=predicates)
                if all(models(s, structure) for s in sentences):
                    return structure
        else:
            if _candidate_count(sig, k) > max_candidates:
                continue
            for constants, functions, predicates in _interpretations(sig, domain):
                structure = Structure(domain, constants=constants,
                                      functions=functions, predicates=predicates)
                if all(models(s, structure) for s in sentences):
                    return structure
    return None


def find_countermodel(premises, conclusion: Node, max_size: int = 4,
                      max_candidates: int = MAX_CANDIDATES,
                      symmetry_breaking: bool = True,
                      subsorts: Optional[Mapping[str, FrozenSet[str]]] = None) -> Optional[Structure]:
    """Return a finite structure satisfying ``premises`` but not ``conclusion``, or None.

    A countermodel witnesses that ``premises`` do **not** entail ``conclusion``. The
    conclusion is universally closed and negated, so the structure refutes the
    entailment for some assignment of its free variables. See :func:`find_model`
    for ``symmetry_breaking`` and ``subsorts``.
    """
    refuted = Not(_universal_closure(conclusion))
    return find_model(list(premises) + [refuted], max_size, max_candidates,
                      symmetry_breaking, subsorts)


def is_satisfiable_finite(formula: Node, max_size: int = 4,
                          max_candidates: int = MAX_CANDIDATES,
                          symmetry_breaking: bool = True,
                          subsorts: Optional[Mapping[str, FrozenSet[str]]] = None) -> bool:
    """True iff ``formula`` has a finite model of size ≤ ``max_size`` (bounded)."""
    return find_model([formula], max_size, max_candidates,
                      symmetry_breaking, subsorts) is not None


def is_valid_finite(formula: Node, max_size: int = 4,
                    max_candidates: int = MAX_CANDIDATES,
                    symmetry_breaking: bool = True,
                    subsorts: Optional[Mapping[str, FrozenSet[str]]] = None) -> bool:
    """True iff no finite countermodel of ``formula`` exists up to ``max_size`` (bounded).

    Bounded and one-sided: True means "no countermodel found within the bounds"
    (strong evidence of validity, not a proof); a False is a genuine refutation —
    :func:`find_countermodel` returns the witnessing structure.
    """
    return find_countermodel([], formula, max_size, max_candidates,
                             symmetry_breaking, subsorts) is None


def is_size_exhaustive(formulas: Iterable[Node], k: int,
                       max_candidates: int = MAX_CANDIDATES,
                       symmetry_breaking: bool = True) -> bool:
    """True iff :func:`find_model` would FULLY enumerate domain size ``k`` for
    this theory's signature, rather than skip it.

    ``find_model`` conflates two reasons a given size ``k`` contributes nothing
    to its ``None`` result: either every interpretation at size ``k`` was tried
    and none satisfied the theory (a genuine refutation of that size), or the
    interpretation space at size ``k`` exceeded ``max_candidates`` and the whole
    size was skipped via ``continue`` without a single structure being built or
    checked (see the module docstring's "honesty contract" and ``find_model``'s
    own per-size ``continue``). Both look identical from the outside — a caller
    cannot tell "refuted" from "never asked" just by seeing that ``find_model``
    returned ``None`` — so a claim like "size ``k`` has no model" (e.g. to
    certify a *minimal* model size found at some larger size) needs this
    function alongside ``find_model`` to rule the "skipped" case out. A skipped
    size is NEVER reported as "no model" by this module; it is this function's
    job to let a caller detect that case explicitly instead of silently trusting
    the absence.

    This is a pure COUNT-ONLY pre-flight check — it mirrors exactly the
    candidate-count arithmetic ``find_model`` itself runs before searching a
    size, and does not run the search or the Tarskian evaluator at all, so it
    costs O(1) arithmetic regardless of ``k``.

    What is being counted (this matters for what "exhaustive" promises):

    - For a many-sorted (MSFOL) signature (any formula uses a
      :class:`~unicode_fol_kit.fol.nodes.SortedQuantifier` or sorted constant),
      the count is the RAW, unreduced number of interpretations
      (:func:`_candidate_count`) — ``symmetry_breaking`` is ignored, exactly as
      ``find_model`` itself ignores it for sorted search (see the module
      docstring's "Subsorting" section: sorted search always uses the unbroken
      :func:`_sorted_interpretations`).
    - Otherwise, with ``symmetry_breaking=True`` (the default, matching
      ``find_model``'s own default), the count is
      :func:`_canonical_candidate_count`: ONE representative per isomorphism
      class of CONSTANT assignments (the LNH reduction), crossed with the FULL,
      unreduced enumeration of function and predicate tables — this is NOT "one
      representative per isomorphism class of the whole structure", only of the
      constant-naming part (see the module docstring's LNH section for why
      functions/predicates stay exhaustive).
    - With ``symmetry_breaking=False``, the count is the raw, unreduced
      :func:`_candidate_count` — every structure, no isomorphism reduction at
      all.

    A size is exhaustive iff its count is ``<= max_candidates``; ``find_model``
    always fully enumerates such a size (never truncates mid-generator), so
    "exhaustive" here means exactly what it means there.

    ``subsorts`` has no parameter here because it never changes this count:
    :func:`find_model` applies a subsort edge as a FILTER during enumeration
    (:func:`_respects_subsorts`), which only discards candidates the unfiltered
    count already includes — it can only make an exhaustive search find fewer
    or equal models, never fall outside the ``max_candidates`` bound the
    unfiltered count already decided.
    """
    sentences = [_universal_closure(f) for f in formulas]
    sig = _Signature()
    for s in sentences:
        sig.scan(s)
    if sig.sorts:
        return _candidate_count(sig, k) <= max_candidates
    if symmetry_breaking:
        return _canonical_candidate_count(sig, k) <= max_candidates
    return _candidate_count(sig, k) <= max_candidates
