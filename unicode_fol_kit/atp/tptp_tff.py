"""Native TF0 (monomorphic typed first-order TPTP, ``tff``) export.

The classical ``fof`` route (:mod:`atp._tptp_problem`) already handles
many-sorted formulas via :meth:`~unicode_fol_kit.fol.nodes.SortedQuantifier
.to_tptp`'s auto-reduction: a sort ``S`` becomes an ordinary guard predicate,
``∀x:S φ`` becomes ``![X]: (s(X) => <φ>)``. That is sound but throws the
typing away — an external prover sees an unsorted formula with one extra
predicate per sort, not a genuinely typed problem. This module instead emits
TPTP's own typed dialect: one ``tff(name, type, Sym: Type).`` declaration per
sort/predicate/function/constant, and formula bodies with GENUINE typed
quantifiers (``![X: sort]: ...``) rather than guard atoms.

Scope: TF0 only
----------------
Deliberately narrower than full TFF: no THF (higher-order), no TF1
polymorphism (type variables, ``!>``), and none of TPTP's built-in
arithmetic sorts (``$int``/``$rat``/``$real``) — none of those constructs are
producible by this kit's own AST in the first place (there is no "type
variable" or "higher-order" node class), so the writer's fragment gate below
simply enumerates the classical many-sorted FOL node set it understands and
refuses everything else BY NAME, mirroring
:mod:`unicode_fol_kit.fol.casl_export`'s ``_check_fragment`` gate for the
structurally identical problem (CASL's own typed spec syntax). The built-in
arithmetic operators (``+``/``-``/``*``/``/``) and comparisons
(``<``/``>``/``≤``/``≥``) are refused too, by name, for the same reason: TF0
has no arithmetic sort for them to range over without ``$int``/``$rat``/
``$real``, which is out of scope.

The two builtin TPTP types this module DOES use, ``$i`` (the default
individual type — never declared, exactly the TPTP standard's own
convention) and ``$o`` (booleans — only ever appears as a predicate's own
result type), are never routed through the sort-name sanitiser below; they
are TPTP reserved dollar-words, lexically disjoint from every
``lower_word``-shaped user sort name this module CAN synthesise.

Sort/type inference: a union-find over symbol-position "slots"
-------------------------------------------------------------------
The same technique :mod:`unicode_fol_kit.fol.casl_export` uses for CASL's
``ops``/``preds`` blocks, adapted for TFF: :class:`~unicode_fol_kit.fol.nodes
.SortedQuantifier` only annotates its OWN bound variable, not every symbol
position that variable is later passed to, so before any ``tff(...,type,...)``
declaration can be written, this module infers a single concrete sort for
every predicate/function ARGUMENT position and every function/constant
RESULT, by propagating the sort annotations that ARE present
(:class:`SortedQuantifier`, :class:`~unicode_fol_kit.fol.nodes.SortedConstant`)
through every place a term is passed as an argument. A plain, unsorted
:class:`~unicode_fol_kit.fol.nodes.Quantifier`'s variable anchors its slot to
``$i`` directly (TPTP's own "no type given" default), which plugs into
EXACTLY the same union-find machinery as a genuine sort name — a position
connected to both ``$i`` (from one occurrence) and a real sort ``S`` (from
another) is a genuine conflict and is refused loudly, precisely because
mixing an implicitly-``$i`` and an explicitly-sorted use of the same symbol
position really is unsound. See :mod:`unicode_fol_kit.fol.casl_export`'s
module docstring for the full union-find account (:class:`_UnionFind`
below is line-for-line the same algorithm, ``$i`` playing CASL's
``default_sort`` role).

``SortedCount`` (∃≥n / ∃≤n / ∃=n x:S φ) is lowered BEFORE inference/rendering
via :func:`_expand_sorted_count` — the same distinct-witnesses encoding
:class:`~unicode_fol_kit.fol.nodes.Count._expand` uses, reimplemented here
with SORT-TYPED witness quantifiers (``SortedQuantifier`` over the SAME sort
``S``) instead of Count's plain, unsorted ones, so the exported problem never
needs a synthetic guard predicate for the witnesses either.
:class:`~unicode_fol_kit.fol.nodes.SortedCardinality` has no first-order
export at all (set cardinality is second-order) and is refused by the
fragment gate, exactly like :class:`~unicode_fol_kit.fol.nodes.Cardinality`
in the classical route.

Free variables are refused, not implicitly closed
---------------------------------------------------
TPTP semantics implicitly universally-close a free variable in an
axiom/conjecture at type ``$i``. This module refuses a free variable instead
(mirroring :func:`unicode_fol_kit.fol.casl_export.formula_to_casl`'s own
refusal, for the same reason): a kit-level formula that reaches this module
with a genuinely free variable has no way to tell whether that variable was
MEANT to range over a user sort — silently defaulting it to ``$i`` could
render a DIFFERENT, unintended typed problem. Every variable rendered here
comes from an explicit :class:`~unicode_fol_kit.fol.nodes.Quantifier` /
``SortedQuantifier`` binder in the kit's own AST.

Name legality (ASCII, first-letter-fold, whole-problem-injective)
-------------------------------------------------------------------
Mirrors :mod:`atp._tptp_problem`'s sanitisation for predicates/functions/
constants (ASCII transliteration, then fold only the first character for
TPTP's lower_word rule, with a synthesised token when the original name is
not already TPTP-legal) and extends the SAME treatment to SORT names, which
share the kit's uppercase-initial :samp:`PREDICATE` lexical convention (see
``fol/_identifiers.py``'s ``sort_pattern()``) and therefore need exactly the
same fold. Predicates, functions+constants (one shared namespace, matching
how a TPTP-reading prover resolves a bare identifier by SYNTACTIC POSITION
rather than a single shared table), and sorts (a third, independent
namespace — TPTP types live in yet another syntactic position) are each
de-collided separately; two DISTINCT kit-level names in the same namespace
that would fold to the same TPTP identifier are refused with
``NotImplementedError`` naming both, exactly like ``_tptp_problem``'s own
collision guard. This module deliberately does not depend on
``atp._tptp_problem`` (nor the reverse) to avoid a circular import between
the two — the small renaming primitives are duplicated here at the size CASL
export's own ``_check_reserved`` duplicates ``eval.validate``'s builtin sets
(see that module's docstring for the same "importing would be backwards"
reasoning).
"""

import re
from dataclasses import dataclass, field
from typing import Callable, Dict, List, Optional, Sequence, Set, Tuple, Union

from ..fol.nodes import (
    Node, Variable, Constant, SortedConstant, Function,
    Atom, Not, And, Or, Xor, Implies, Iff, Quantifier, SortedQuantifier,
    SortedCount, free_variables, substitute,
)
from ..fol._fol_nodes import constant_name_to_ascii, tptp_fold_first_letter
from ..fol.signature import Signature, PredicateDecl, FunctionDecl, ConstantDecl
from ._ascii_names import ascii_safe_base, reserve_rendered

__all__ = [
    "generate_tff_problem", "formula_to_tff", "infer_tff_signature",
    "problem_needs_tff", "TFF_INDIVIDUAL_SORT", "TFF_BOOLEAN_SORT",
]

_SORTED_NODE_NAMES = frozenset({"SortedQuantifier", "SortedConstant", "SortedCount"})


def problem_needs_tff(premises: Sequence[Node], conclusion: Node) -> bool:
    """Whether any of ``premises`` + ``conclusion`` contains a
    :class:`~unicode_fol_kit.fol.nodes.SortedQuantifier` /
    :class:`~unicode_fol_kit.fol.nodes.SortedConstant` /
    :class:`~unicode_fol_kit.fol.nodes.SortedCount` node.

    The auto-select signal the TPTP-family backends
    (:mod:`atp.vampire_entailment`, :mod:`atp.eprover_backend`) use to
    route to this module's native typed export instead of the classical
    guard-predicate ``fof`` route (:mod:`atp._tptp_problem`) — see each
    backend's ``tff=`` option. A batch with no sorted node at all is
    already fully served by the classical route (a plain ``Quantifier``
    needs no typing to export soundly), so the default stays ``fof`` there.
    """
    for f in list(premises) + [conclusion]:
        for n in f.walk():
            if type(n).__name__ in _SORTED_NODE_NAMES:
                return True
    return False

#: TPTP's built-in "individual" type — the implicit type of an untyped
#: quantified variable. Never declared with its own ``tff(...,type,...)``
#: statement (it is a TPTP reserved word), and never routed through the
#: sort-name sanitiser (it is not a kit-level sort name at all).
TFF_INDIVIDUAL_SORT = "$i"

#: TPTP's built-in boolean type — only ever a PREDICATE's own result type.
TFF_BOOLEAN_SORT = "$o"

_ARITHMETIC_PREDS = frozenset({"<", ">", "≤", "≥"})
_ARITHMETIC_FUNCS = frozenset({"+", "-", "*", "/"})

_ARITH_OUT_OF_SCOPE = (
    "generate_tff_problem: {kind} {name!r} needs TPTP's arithmetic sorts "
    "($int/$rat/$real), which are out of scope for this TF0-only exporter "
    "(see module docstring 'Scope: TF0 only'); rename or remove it before "
    "exporting, or use the classical fof route (Node.to_tptp) instead."
)


# =============================================================================
# Fragment gate
# =============================================================================

# The classical MSFOL node set this exporter understands PLUS SortedCount
# (lowered away by _expand_all_sorted_counts before inference/rendering ever
# see it) — exactly unicode_fol_kit.fol.casl_export's _ALLOWED_CASL_NODES
# with SortedCount added; see the module docstring's "Scope" section for why
# every other node class (Cardinality/SortedCardinality, modal/temporal,
# second-order, lambda, Łukasiewicz, Number, ...) is refused by name rather
# than silently narrowed.
_ALLOWED_TFF_NODES = frozenset({
    "Variable", "Constant", "SortedConstant", "Function",
    "Atom", "Not", "And", "Or", "Xor", "Implies", "Iff",
    "Quantifier", "SortedQuantifier", "SortedCount",
})


def _check_fragment(formula: Node) -> None:
    """Walk ``formula`` and refuse (loudly, by name) the first node outside
    the TF0-expressible fragment this exporter covers.

    A bespoke recursion rather than ``Node.walk()``: ``SortedCount.n`` is a
    ``Number`` child (the symbolic counting bound, e.g. the ``2`` in
    ``∃≥2 x:S φ``) but is not itself a FORMULA or TERM position — it is
    never rendered as a TFF expression, only read as a Python int by
    :func:`_expand_sorted_count` — so it must NOT trip the "a numeric
    literal needs an arithmetic sort" refusal below the way an actual
    ``Number`` TERM occurrence (e.g. inside an Atom's arguments) should.
    """
    def visit(node: Node) -> None:
        cls = type(node).__name__
        if cls not in _ALLOWED_TFF_NODES:
            if cls == "Number":
                raise NotImplementedError(
                    "generate_tff_problem: a numeric literal needs TPTP's "
                    "arithmetic sorts ($int/$rat/$real), which are out of "
                    "scope for this TF0-only exporter (see module "
                    "docstring 'Scope: TF0 only')."
                )
            raise NotImplementedError(
                f"generate_tff_problem: {cls!r} is outside the classical "
                "many-sorted FOL fragment this native TF0 exporter covers "
                "(only Atom, Not, And, Or, Xor, Implies, Iff, Quantifier, "
                "SortedQuantifier, SortedCount, and the term classes "
                "Variable, Constant, SortedConstant, Function are "
                "TF0-expressible here). Modal/temporal/epistemic operators, "
                "second-order quantification, SortedCardinality (set "
                "cardinality has no first-order counterpart), and lambda "
                "terms are all out of scope for this TF0-only exporter."
            )
        if cls == "SortedCount":
            visit(node.variable)
            visit(node.formula)
            return
        for child in node._child_nodes():
            visit(child)

    visit(formula)


# =============================================================================
# SortedCount lowering: typed distinct-witnesses encoding
# =============================================================================

_COUNT_EXPAND_MAX = 500
_COUNT_TOO_LARGE = (
    "generate_tff_problem: SortedCount n={n} is too large to expand to "
    "typed first-order TFF (the distinct-witnesses encoding materialises "
    f"O(n^2) constraints under n nested quantifiers; the limit is n<={_COUNT_EXPAND_MAX})."
)


def _balanced_and(parts: List[Node]) -> Node:
    """Fold a non-empty list of formulas into a balanced (shallow) And tree —
    mirrors ``fol._fol_nodes._balanced_and``, duplicated here (a private
    helper of a module this one does not otherwise depend on) so an
    O(n^2)-conjunct count expansion stays only O(log n) deep."""
    while len(parts) > 1:
        merged = [And(parts[i], parts[i + 1]) for i in range(0, len(parts) - 1, 2)]
        if len(parts) % 2:
            merged.append(parts[-1])
        parts = merged
    return parts[0]


def _expand_sorted_count(node: SortedCount) -> Node:
    """Lower one ``SortedCount`` to plain SortedQuantifier/And/Or/Not/Atom,
    via the standard distinct-witnesses counting encoding, SORT-TYPED: every
    witness variable is bound by a ``SortedQuantifier`` over ``node.sort``,
    not a plain (guard-predicate-needing) ``Quantifier``.

    ``∃≥m x:S φ`` becomes ``∃x_0:S … ∃x_{m-1}:S (⋀ φ[x_i] ∧ ⋀_{i<j} x_i ≠ x_j)``;
    ``∃≤n`` is ``¬(∃≥n+1)``; ``∃=n`` is ``∃≥n ∧ ¬(∃≥n+1)`` — the exact reading
    :meth:`~unicode_fol_kit.fol.nodes.Count._expand` uses, reimplemented here
    (rather than delegating to ``SortedCount._relativize``/``Count._expand``)
    because those guard the matrix with a predicate atom instead of typing
    the witness quantifier, which is exactly the guard-atom encoding this
    NATIVE TFF exporter exists to avoid.
    """
    if node.n.value > _COUNT_EXPAND_MAX:
        raise NotImplementedError(_COUNT_TOO_LARGE.format(n=node.n.value))
    var, sort, phi = node.variable, node.sort, node.formula
    avoid = {v.name for v in free_variables(phi)} | {var.name}

    def fresh(k: int) -> List[Variable]:
        out: List[Variable] = []
        i = 0
        while len(out) < k:
            cand = f"{var.name}_{i}"
            if cand not in avoid:
                out.append(Variable(cand))
                avoid.add(cand)
            i += 1
        return out

    def at_least(m: int) -> Node:
        if m <= 0:
            w = fresh(1)[0]
            g = substitute(phi, var, w)
            return SortedQuantifier("∃", w, sort, Or(g, Not(g)))
        ws = fresh(m)
        conjuncts = [substitute(phi, var, w) for w in ws]
        conjuncts += [Atom("≠", [ws[i], ws[j]])
                      for i in range(m) for j in range(i + 1, m)]
        body = _balanced_and(conjuncts)
        for w in reversed(ws):
            body = SortedQuantifier("∃", w, sort, body)
        return body

    if node.op == "ge":
        return at_least(node.n.value)
    if node.op == "le":
        return Not(at_least(node.n.value + 1))
    return And(at_least(node.n.value), Not(at_least(node.n.value + 1)))


def _expand_all_sorted_counts(node: Node) -> Node:
    """Bottom-up rewrite: every ``SortedCount`` (including one nested inside
    another's matrix) is replaced by :func:`_expand_sorted_count`'s typed
    encoding. After this pass the tree is guaranteed to use only the
    fragment :mod:`unicode_fol_kit.fol.casl_export` also accepts (plus
    ``SortedQuantifier``/``SortedConstant``), since ``_check_fragment`` has
    already run on the (pre-expansion) input."""
    node = node.map_children(_expand_all_sorted_counts)
    if isinstance(node, SortedCount):
        return _expand_sorted_count(node)
    return node


# =============================================================================
# Sort inference: union-find over slots and concrete sort names
# =============================================================================
#
# Line-for-line the same algorithm as unicode_fol_kit.fol.casl_export's
# _UnionFind — see that module's docstring for the full account. $i plays
# CASL's default_sort role: it is unioned in directly wherever a plain
# (unsorted) Quantifier's variable is used, so a position that is EVER used
# both implicitly-$i and explicitly-sorted is a genuine, correctly-refused
# conflict rather than two different silently-coexisting readings.

_Slot = Union[Tuple[str, str, int], Tuple[str, str], str]


class _UnionFind:
    """Weighted union-find over sort-inference slots and concrete sort names.

    Invariant: whenever a class contains a concrete sort name (a plain str
    member, including ``$i``), that string is ALWAYS the class's root.
    """

    def __init__(self) -> None:
        self._parent: Dict[_Slot, _Slot] = {}
        self._rank: Dict[_Slot, int] = {}

    def find(self, x: _Slot) -> _Slot:
        self._parent.setdefault(x, x)
        path = []
        while self._parent[x] != x:
            path.append(x)
            x = self._parent[x]
        for n in path:
            self._parent[n] = x
        return x

    def union(self, a: _Slot, b: _Slot, context: str) -> None:
        ra, rb = self.find(a), self.find(b)
        if ra == rb:
            return
        a_concrete, b_concrete = isinstance(ra, str), isinstance(rb, str)
        if a_concrete and b_concrete:
            raise ValueError(
                f"generate_tff_problem: sort conflict while resolving "
                f"{context} — inferred both {ra!r} and {rb!r}."
            )
        if a_concrete:
            self._parent[rb] = ra
        elif b_concrete:
            self._parent[ra] = rb
        else:
            rank_a, rank_b = self._rank.get(ra, 0), self._rank.get(rb, 0)
            if rank_a < rank_b:
                ra, rb = rb, ra
            self._parent[rb] = ra
            if rank_a == rank_b:
                self._rank[ra] = rank_a + 1

    def sort_of(self, slot: _Slot) -> str:
        """Return the concrete sort resolved for ``slot``, defaulting to
        :data:`TFF_INDIVIDUAL_SORT` if that slot's class has no concrete
        member at all (a symbol position never connected to any sort
        annotation — TPTP's own "no type given" reading)."""
        root = self.find(slot)
        return root if isinstance(root, str) else TFF_INDIVIDUAL_SORT


@dataclass
class _Signature:
    """Mutable accumulator built by one :func:`_analyze` pass — mirrors
    ``casl_export._Signature`` minus ``default_sort`` (fixed to ``$i``)."""

    uf: _UnionFind = field(default_factory=_UnionFind)
    pred_arity: Dict[str, int] = field(default_factory=dict)
    func_arity: Dict[str, int] = field(default_factory=dict)
    const_names: Set[str] = field(default_factory=set)
    func_names: Set[str] = field(default_factory=set)
    literal_sorts: Set[str] = field(default_factory=set)


_CONST_VS_FUNCTION = (
    "generate_tff_problem: {name!r} is used both as a constant and as a "
    "function — this exporter declares at most one 'tff(...,type,...)' "
    "entry per name, so the two uses cannot be reconciled into one symbol."
)


def _infer_term(node: Node, env: Dict[str, str], sig: _Signature) -> _Slot:
    """Process a term node: register its symbol, recurse into sub-terms,
    return the union-find slot representing its sort. Mirrors
    ``casl_export._infer_term``."""
    cls = type(node).__name__

    if cls == "Variable":
        if node.name not in env:
            raise ValueError(
                f"generate_tff_problem: free variable '{node.name}' — every "
                "variable must be bound by an enclosing Quantifier or "
                "SortedQuantifier; TPTP's implicit top-level closure would "
                "silently default an unbound variable to $i, which this "
                "exporter refuses to guess (see module docstring)."
            )
        return env[node.name]

    if cls in ("Constant", "SortedConstant"):
        name = node.name
        if name in sig.func_names:
            raise ValueError(_CONST_VS_FUNCTION.format(name=name))
        sig.const_names.add(name)
        slot: _Slot = ("const", name)
        if cls == "SortedConstant":
            sig.literal_sorts.add(node.sort)
            sig.uf.union(slot, node.sort, f"constant '{name}' sort annotation")
        return slot

    if cls == "Function":
        name = node.name
        if name in _ARITHMETIC_FUNCS:
            raise NotImplementedError(_ARITH_OUT_OF_SCOPE.format(kind="function", name=name))
        if name in sig.const_names:
            raise ValueError(_CONST_VS_FUNCTION.format(name=name))
        arity = len(node.args)
        prev = sig.func_arity.get(name)
        if prev is not None and prev != arity:
            raise ValueError(
                f"generate_tff_problem: function '{name}' used with "
                f"conflicting arities {prev} and {arity}."
            )
        sig.func_arity[name] = arity
        sig.func_names.add(name)
        for i, a in enumerate(node.args):
            arg_slot = _infer_term(a, env, sig)
            sig.uf.union(("func", name, i), arg_slot,
                        f"function '{name}' argument {i + 1}")
        return ("func_result", name)

    raise AssertionError(
        f"generate_tff_problem: unreachable — term node {cls!r} passed the "
        "fragment check but is not handled by _infer_term."
    )


def _infer_formula(node: Node, env: Dict[str, str], sig: _Signature) -> None:
    """Walk a formula node, threading the bound-variable environment,
    registering every predicate/connective/quantifier constraint. Mirrors
    ``casl_export._infer_formula``."""
    cls = type(node).__name__

    if cls == "Atom":
        if node.predicate in _ARITHMETIC_PREDS:
            raise NotImplementedError(
                _ARITH_OUT_OF_SCOPE.format(kind="predicate", name=node.predicate))
        if node.predicate in ("=", "≠"):
            if len(node.args) != 2:
                raise ValueError(
                    "generate_tff_problem: an equality/disequality atom "
                    f"must have exactly 2 arguments, got {len(node.args)}."
                )
            s0 = _infer_term(node.args[0], env, sig)
            s1 = _infer_term(node.args[1], env, sig)
            sig.uf.union(s0, s1, "an equality/disequality atom")
            return
        arity = len(node.args)
        prev = sig.pred_arity.get(node.predicate)
        if prev is not None and prev != arity:
            raise ValueError(
                f"generate_tff_problem: predicate '{node.predicate}' used "
                f"with conflicting arities {prev} and {arity}."
            )
        sig.pred_arity[node.predicate] = arity
        for i, a in enumerate(node.args):
            arg_slot = _infer_term(a, env, sig)
            sig.uf.union(("pred", node.predicate, i), arg_slot,
                        f"predicate '{node.predicate}' argument {i + 1}")
        return

    if cls == "Not":
        _infer_formula(node.formula, env, sig)
        return

    if cls in ("And", "Or", "Xor", "Implies", "Iff"):
        _infer_formula(node.left, env, sig)
        _infer_formula(node.right, env, sig)
        return

    if cls == "Quantifier":
        new_env = dict(env)
        new_env[node.variable.name] = TFF_INDIVIDUAL_SORT
        _infer_formula(node.formula, new_env, sig)
        return

    if cls == "SortedQuantifier":
        sig.literal_sorts.add(node.sort)
        new_env = dict(env)
        new_env[node.variable.name] = node.sort
        _infer_formula(node.formula, new_env, sig)
        return

    raise AssertionError(
        f"generate_tff_problem: unreachable — formula node {cls!r} passed "
        "the fragment check but is not handled by _infer_formula."
    )


def _analyze(formulas: Sequence[Node]) -> _Signature:
    """Run sort inference over a batch of already-fragment-checked,
    already-SortedCount-expanded formulas that share one TFF signature."""
    sig = _Signature()
    for f in formulas:
        _infer_formula(f, {}, sig)
    return sig


# =============================================================================
# Name legality: ASCII, first-letter-fold, whole-problem-injective
# =============================================================================

_TPTP_SAFE_RE = re.compile(r"[A-Za-z][A-Za-z0-9_]*")


def _is_tptp_safe(name: str) -> bool:
    return bool(name) and name.isascii() and bool(_TPTP_SAFE_RE.fullmatch(name))


def _upper_initial(base: str) -> str:
    """Force uppercase-initial — the kit's own PREDICATE/SORT convention."""
    return base[0].upper() + base[1:] if base else base


def _lower_initial(base: str) -> str:
    """Force lowercase-initial — the kit's own NAME (function/constant) convention."""
    return base[0].lower() + base[1:] if base else base


def _render_token(raw: str) -> str:
    """ASCII-transliterate then TPTP-fold a sanitised (possibly still
    non-ASCII) raw name — the single render function every namespace's
    renamer below de-collides against."""
    return tptp_fold_first_letter(constant_name_to_ascii(raw))


@dataclass
class _Renamer:
    """One symbol namespace's original -> TPTP-legal-token map.

    Two passes (mirrors ``atp._tptp_problem._Renamer``): :meth:`collect`
    reserves every already-legal name immediately (R1: never renamed);
    :meth:`finalize` synthesises a token for everything else, de-collided
    against every reservation so far. :meth:`check_no_collisions` then
    catches the one case the two-pass split cannot rule out by construction:
    two DIFFERENT already-legal names (both bypass synthesis entirely) that
    fold to the SAME rendered identifier (``Foo``/``foo``).
    """

    prefix: str
    case_fix: Callable[[str], str]
    mapping: Dict[str, str] = field(default_factory=dict)
    used: set = field(default_factory=set)
    _pending: List[str] = field(default_factory=list)

    def collect(self, name: str) -> None:
        if name in self.mapping or name in self._pending:
            return
        if _is_tptp_safe(name):
            self.used.add(_render_token(name))
            self.mapping[name] = name
        else:
            self._pending.append(name)

    def finalize(self) -> None:
        for name in self._pending:
            base = self.case_fix(ascii_safe_base(name, self.prefix))
            token = reserve_rendered(base, self.used, _render_token)
            self.mapping[name] = token
        self._pending = []

    def get(self, name: str) -> str:
        return _render_token(self.mapping[name])

    def check_no_collisions(self, kind: str) -> None:
        seen: Dict[str, str] = {}
        for name in sorted(self.mapping):
            rendered = _render_token(self.mapping[name])
            if rendered in seen and seen[rendered] != name:
                raise NotImplementedError(
                    f"generate_tff_problem: distinct {kind} names "
                    f"{seen[rendered]!r} and {name!r} would both render as "
                    f"the TFF identifier {rendered!r} — refusing to "
                    "silently merge two distinct symbols; rename one of "
                    "them before exporting this problem."
                )
            seen[rendered] = name


@dataclass
class _Names:
    predicate: _Renamer
    term: _Renamer
    sort: _Renamer


def _build_names(sig: _Signature) -> _Names:
    predicates = _Renamer(prefix="p", case_fix=_upper_initial)
    terms = _Renamer(prefix="n", case_fix=_lower_initial)
    sorts = _Renamer(prefix="s", case_fix=_upper_initial)
    for name in sig.pred_arity:
        predicates.collect(name)
    for name in sorted(sig.func_names | sig.const_names):
        terms.collect(name)
    for name in sig.literal_sorts:
        sorts.collect(name)
    predicates.finalize()
    terms.finalize()
    sorts.finalize()
    predicates.check_no_collisions("predicate")
    terms.check_no_collisions("function/constant")
    sorts.check_no_collisions("sort")
    return _Names(predicates, terms, sorts)


def _sort_text(sort: str, names: _Names) -> str:
    if sort == TFF_INDIVIDUAL_SORT:
        return sort
    return names.sort.get(sort)


# =============================================================================
# Formula rendering — mirrors Node.to_tptp's own (always fully-parenthesised)
# shape exactly, so nesting never needs a bespoke parenthesisation policy.
# =============================================================================

def _render_term(node: Node, names: _Names) -> str:
    if isinstance(node, Variable):
        return node.name.upper()
    if isinstance(node, (Constant, SortedConstant)):
        return names.term.get(node.name)
    if isinstance(node, Function):
        name = names.term.get(node.name)
        if not node.args:
            return name
        args = ",".join(_render_term(a, names) for a in node.args)
        return f"{name}({args})"
    raise AssertionError(f"generate_tff_problem: unreachable term node {type(node).__name__!r}.")


def _render_atom(node: Atom, names: _Names) -> str:
    if node.predicate == "=":
        return f"{_render_term(node.args[0], names)} = {_render_term(node.args[1], names)}"
    if node.predicate == "≠":
        return f"{_render_term(node.args[0], names)} != {_render_term(node.args[1], names)}"
    pred = names.predicate.get(node.predicate)
    if not node.args:
        return pred
    args = ",".join(_render_term(a, names) for a in node.args)
    return f"{pred}({args})"


def _quant_symbol(qtype: str) -> str:
    if qtype in ("∀", "forall"):
        return "!"
    if qtype in ("∃", "exists"):
        return "?"
    raise ValueError(f"generate_tff_problem: unknown quantifier type {qtype!r}.")


def _render(node: Node, names: _Names) -> str:
    if isinstance(node, Atom):
        return _render_atom(node, names)
    if isinstance(node, Not):
        return f"~({_render(node.formula, names)})"
    if isinstance(node, And):
        return f"({_render(node.left, names)} & {_render(node.right, names)})"
    if isinstance(node, Or):
        return f"({_render(node.left, names)} | {_render(node.right, names)})"
    if isinstance(node, Xor):
        return f"({_render(node.left, names)} <~> {_render(node.right, names)})"
    if isinstance(node, Implies):
        return f"({_render(node.left, names)} => {_render(node.right, names)})"
    if isinstance(node, Iff):
        return f"({_render(node.left, names)} <=> {_render(node.right, names)})"
    if isinstance(node, Quantifier):
        var = node.variable.name.upper()
        q = _quant_symbol(node.type)
        return f"({q}[{var}: {TFF_INDIVIDUAL_SORT}]: {_render(node.formula, names)})"
    if isinstance(node, SortedQuantifier):
        var = node.variable.name.upper()
        q = _quant_symbol(node.type)
        sort_text = _sort_text(node.sort, names)
        return f"({q}[{var}: {sort_text}]: {_render(node.formula, names)})"
    raise AssertionError(f"generate_tff_problem: unreachable formula node {type(node).__name__!r}.")


# =============================================================================
# Type declaration rendering
# =============================================================================

def _render_map_type(arg_sorts: List[str], result_sort: str) -> str:
    if not arg_sorts:
        return result_sort
    if len(arg_sorts) == 1:
        return f"{arg_sorts[0]} > {result_sort}"
    return "(" + " * ".join(arg_sorts) + ") > " + result_sort


def _render_type_decls(sig: _Signature, names: _Names) -> List[str]:
    lines: List[str] = []
    counter = [0]

    def next_name(prefix: str) -> str:
        counter[0] += 1
        return f"{prefix}_{counter[0]}"

    for sort in sorted(sig.literal_sorts):
        lines.append(f"tff({next_name('sort_decl')}, type, {_sort_text(sort, names)}: $tType ).")
    for name in sorted(sig.func_names):
        arity = sig.func_arity[name]
        arg_sorts = [_sort_text(sig.uf.sort_of(("func", name, i)), names) for i in range(arity)]
        result_sort = _sort_text(sig.uf.sort_of(("func_result", name)), names)
        type_str = _render_map_type(arg_sorts, result_sort)
        lines.append(f"tff({next_name('func_decl')}, type, {names.term.get(name)}: {type_str} ).")
    for name in sorted(sig.const_names):
        const_sort = _sort_text(sig.uf.sort_of(("const", name)), names)
        lines.append(f"tff({next_name('const_decl')}, type, {names.term.get(name)}: {const_sort} ).")
    for name in sorted(sig.pred_arity):
        arity = sig.pred_arity[name]
        arg_sorts = [_sort_text(sig.uf.sort_of(("pred", name, i)), names) for i in range(arity)]
        type_str = _render_map_type(arg_sorts, TFF_BOOLEAN_SORT)
        lines.append(f"tff({next_name('pred_decl')}, type, {names.predicate.get(name)}: {type_str} ).")
    return lines


# =============================================================================
# Public API
# =============================================================================

def formula_to_tff(formula: Node) -> str:
    """Render a single formula as bare TFF formula text (no ``tff(...)``
    statement wrapper) — the TF0 sibling of
    :func:`unicode_fol_kit.fol.casl_export.formula_to_casl`.

    Runs the full validation pipeline (fragment check, SortedCount lowering,
    free-variable check, arity/sort-conflict detection, name legalisation —
    see the module docstring) on ``formula`` ALONE; a symbol's sort/name
    token is therefore whatever this one formula's own occurrences pin down,
    not shared with any other formula the way :func:`generate_tff_problem`
    shares one signature across a whole premise/conclusion batch.

    Raises:
        NotImplementedError: ``formula`` contains a node outside the TF0
            fragment (see module docstring 'Scope'), or a name-folding
            collision (two distinct symbols in one namespace).
        ValueError: a free variable, or an unsatisfiable sort constraint.
    """
    _check_fragment(formula)
    expanded = _expand_all_sorted_counts(formula)
    sig = _analyze([expanded])
    names = _build_names(sig)
    return _render(expanded, names)


def generate_tff_problem(premises: List[Node], conclusion: Node) -> str:
    """Build a native, genuinely-typed TPTP ``tff`` problem string.

    The TF0 sibling of :func:`atp._tptp_problem.generate_tptp_problem`: same
    ``premise_<i>``/``goal`` naming and axiom/conjecture role split, but
    emits real ``tff(name, type, Sym: Type).`` declarations (one per sort,
    predicate, function, and constant used anywhere in ``premises`` +
    ``conclusion``) followed by formula bodies with genuine typed
    quantifiers, instead of the classical route's guard-predicate encoding.

    Args:
        premises: many-sorted (or plain classical) FOL premises, using
            :class:`~unicode_fol_kit.fol.nodes.SortedQuantifier` /
            :class:`~unicode_fol_kit.fol.nodes.SortedConstant` /
            :class:`~unicode_fol_kit.fol.nodes.SortedCount` freely alongside
            plain :class:`~unicode_fol_kit.fol.nodes.Quantifier` (which
            renders as an explicitly-``$i``-typed variable).
        conclusion: the conjecture.

    Returns:
        The complete ``tff`` problem text, newline-terminated: type
        declarations first (sorts, then functions, then constants, then
        predicates — declaration-before-use, matching
        ``casl_export.to_casl_spec``'s ordering), then one
        ``tff(premise_<i>, axiom, ...).`` per premise (1-based), then
        ``tff(goal, conjecture, ...).``.

    Raises:
        NotImplementedError: a node outside the TF0 fragment (see module
            docstring 'Scope'), or a name-folding collision — see
            :func:`formula_to_tff`.
        ValueError: a free variable, an arity conflict, a constant-vs-
            function name clash, or an unsatisfiable sort constraint — see
            :func:`formula_to_tff`.
    """
    formulas = list(premises) + [conclusion]
    for f in formulas:
        _check_fragment(f)
    expanded = [_expand_all_sorted_counts(f) for f in formulas]
    sig = _analyze(expanded)
    names = _build_names(sig)

    lines = _render_type_decls(sig, names)
    for i, premise in enumerate(expanded[:-1], start=1):
        lines.append(f"tff(premise_{i}, axiom, {_render(premise, names)} ).")
    lines.append(f"tff(goal, conjecture, {_render(expanded[-1], names)} ).")
    return "\n".join(lines) + "\n"


def infer_tff_signature(formulas: Sequence[Node]) -> Signature:
    """Infer a full :class:`~unicode_fol_kit.fol.signature.Signature` (with
    per-argument-position and result sorts pinned down, never ``None``) from
    a batch of formulas — the same union-find inference
    :func:`generate_tff_problem` uses internally, exposed as a genuine
    :class:`Signature` object for callers that want it directly (e.g. to
    call :meth:`Signature.validate` on a further formula against the same
    vocabulary) rather than TFF text.

    Unlike :meth:`Signature.from_formulas` (which leaves every argument
    position unsorted — see that method's docstring), every predicate/
    function argument and every function/constant result here is pinned to
    a concrete sort, defaulting to :data:`TFF_INDIVIDUAL_SORT` (``"$i"``)
    wherever the formulas never connect that position to a declared sort —
    exactly TPTP's own "no type given" reading, and exactly the sort text
    :func:`generate_tff_problem` would emit for it.

    Kit-level names are used verbatim (unlike the TFF-text writer, this
    function does no ASCII/TPTP-legality renaming) — the returned
    :class:`Signature` is meant for use back inside the kit, not for
    rendering TPTP text.

    Raises:
        NotImplementedError: as :func:`formula_to_tff` (fragment/arithmetic
            refusals) — never a name-folding collision (no renaming happens
            here).
        ValueError: as :func:`formula_to_tff` (free variable, arity/sort
            conflicts).
    """
    formulas = list(formulas)
    for f in formulas:
        _check_fragment(f)
    expanded = [_expand_all_sorted_counts(f) for f in formulas]
    sig = _analyze(expanded)

    def sort_or_none(slot) -> Optional[str]:
        resolved = sig.uf.sort_of(slot)
        return None if resolved == TFF_INDIVIDUAL_SORT else resolved

    predicates: Dict[str, PredicateDecl] = {}
    for name, arity in sig.pred_arity.items():
        arg_sorts = tuple(sort_or_none(("pred", name, i)) for i in range(arity))
        predicates[name] = PredicateDecl(name, arity, arg_sorts)

    functions: Dict[str, FunctionDecl] = {}
    for name, arity in sig.func_arity.items():
        arg_sorts = tuple(sort_or_none(("func", name, i)) for i in range(arity))
        result_sort = sort_or_none(("func_result", name))
        functions[name] = FunctionDecl(name, arity, arg_sorts, result_sort)

    constants: Dict[str, ConstantDecl] = {}
    for name in sig.const_names:
        constants[name] = ConstantDecl(name, sort_or_none(("const", name)))

    sorts: Set[str] = set(sig.literal_sorts)
    for decl in predicates.values():
        sorts.update(s for s in decl.arg_sorts if s is not None)
    for decl in functions.values():
        sorts.update(s for s in decl.arg_sorts if s is not None)
        if decl.result_sort is not None:
            sorts.add(decl.result_sort)
    for decl in constants.values():
        if decl.sort is not None:
            sorts.add(decl.sort)

    return Signature(predicates=predicates, functions=functions,
                     constants=constants, sorts=frozenset(sorts))
