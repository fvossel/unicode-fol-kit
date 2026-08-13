"""Model-checking-oriented simplification of FOL formulas, and a bridge between
Count and the "distinct existential witnesses" encoding an LLM tends to write.

Motivation (ChEBI2FOL, NeSy 2026, Appendix B.3, quoted in this module's task
brief): an LLM translating a class definition such as "has at least 40
carbons" produces ``∃x_0…∃x_39 (⋀_i c(x_i) ∧ ⋀_{i<j} x_i≠x_j)`` — 40
existentially-quantified variables plus all ``binomial(40,2) = 780`` pairwise
inequalities between them. The paper's own diagnosis: "These constraints are
unnecessary in our setting, as the model checker already interprets separately
introduced variables as distinct. [...] FOL definitions that rely on such
predicates or that contain trivial pairwise inequality constraints are prone
to timeouts." The paper also asks for "parameterised built-ins for such cases
(e.g. hasAtLeastNCarbons(n)), evaluated directly by the model checker" — this
kit already has that built-in: :class:`~unicode_fol_kit.fol.nodes.Count`
(``∃≥n x φ``), which is first-order EXPRESSIBLE (so nothing about the target
logic changes) but is represented and can be *evaluated* without ever
materialising the O(n²) encoding (see :mod:`unicode_fol_kit.semantics` for the
structure-checking side of that).

This module supplies the missing piece: recognising and rewriting the
NL-generated distinct-witnesses pattern (in both directions), plus a separate,
narrower simplification pass that removes exactly the redundant pairwise
inequalities WITHOUT requiring the whole formula to be that one clean pattern
— real LLM output routinely interleaves the inequalities with other content
(actual chemical bonds between the same variables, for instance), which
:func:`count_from_existential_chain` must conservatively refuse to touch.

Two independent tools, two independent soundness stories
----------------------------------------------------------
``simplify_for_checking(formula, all_different=...)``
    A conservative rewriter that never changes what the formula MEANS. Most
    of its rules (duplicate conjuncts/disjuncts, ``t=t``, vacuous quantifiers,
    double negation) hold under ordinary classical FOL semantics — the
    ``removed``/`changed`` bookkeeping documents exactly what left the tree
    and why. Its one semantics-DEPENDENT rule (``all_different=True``) removes
    pairwise inequalities between separately ∃-bound variables under the
    *specific, non-standard convention the paper's model checker uses* —
    "separately introduced [existential] variables are [already] distinct" —
    which is NOT a theorem of ordinary FOL (a domain with one element makes
    ``∃x∃y(x≠y)`` false there). ``all_different`` therefore defaults to
    ``False``: soundness under standard semantics is the default, and the
    paper's convention must be opted into explicitly, one call at a time.

``count_from_existential_chain`` / ``expand_count``
    A structural equivalence, sound under ORDINARY FOL semantics (no flag,
    no assumption beyond a non-empty domain): ``∃x_0…∃x_{n-1} (⋀ φ(x_i) ∧
    ⋀_{i<j} x_i≠x_j)`` and ``Count("ge", n, x, φ(x))`` denote the same set of
    structures, because the former is exactly what
    :meth:`~unicode_fol_kit.fol.nodes.Count._expand` produces when lowering
    the latter. ``count_from_existential_chain`` is therefore conservative in
    a DIFFERENT sense than the flag above: it recognises only a complete,
    exact instance of the pattern (every φ(x_i), every C(n,2) inequality,
    nothing else) and returns ``None`` rather than guess at a rewrite that
    would silently drop real content (e.g. a bond literal connecting two of
    the witnesses). ``expand_count`` is the inverse direction, for backends
    that have no ``Count`` node of their own; it does not duplicate the
    distinct-witnesses encoding — it walks the tree and reuses
    :meth:`Count._expand` on every ``Count`` node found (the same lowering
    ``Count.to_z3``/``to_prover9``/``to_tptp`` already use internally).

Both rewriters are purely syntactic (no ``to_z3``, no model). Semantic
equivalence between the two directions is checked in the test suite via
:func:`unicode_fol_kit.atp.z3_equivalence.formulas_are_equivalent` on small
instances (n≤4) — see tests/test_simplify_check.py.
"""

from dataclasses import dataclass, fields
from typing import Dict, List, Optional, Tuple

from .nodes import (
    Node, Variable, Constant, Number, Atom, Not, And, Or, Quantifier, Count,
    Cardinality, SortedQuantifier, SortedCount, SortedCardinality, Lambda,
    free_variables,
)

__all__ = [
    "SimplifyResult", "simplify_for_checking",
    "count_from_existential_chain", "expand_count",
]

_EXISTS = ("∃", "exists")
_FORALL = ("∀", "forall")

# Sentinel marking a "combine the two children just pushed" step in the
# iterative chain walk below — distinct from any real Node by identity.
_COMBINE = object()


@dataclass(frozen=True)
class SimplifyResult:
    """The result of :func:`simplify_for_checking`.

    ``simplified`` is the rewritten formula (structurally identical to the
    input, down to the exact ∧/∨ bracketing, whenever nothing was removed —
    see :func:`_rebuild_like`). ``removed`` is one human-readable description
    per individual construct that was dropped or collapsed (so
    ``len(result.removed)`` counts, e.g., exactly how many redundant pairwise
    inequalities a call with ``all_different=True`` removed). ``changed`` is
    ``True`` iff ``removed`` is non-empty; it never disagrees with ``removed``
    because every rewrite rule below logs its own action before applying it —
    there is no rule that changes the tree silently.
    """

    simplified: Node
    removed: Tuple[str, ...]
    changed: bool


# ---------------------------------------------------------------------------
# Iterative flatten/rebuild over a binary ∧- or ∨-chain.
#
# Both are iterative (explicit stack), not recursive, on purpose: an n-ary
# conjunction as an LLM actually writes it (left- or right-nested, never
# balanced) recurses to depth n in the naive implementation, and n is exactly
# the O(n²)-inequality count this module exists to simplify (820 conjuncts for
# the paper's hasAtLeast40Carbols example) — close enough to Python's default
# recursion limit (1000) to be a real risk, not a theoretical one.
# ---------------------------------------------------------------------------

def _chain_ops(node: Node, cls) -> List:
    """POSTORDER walk of a binary ``cls``-chain (``cls`` is ``And`` or ``Or``).

    Returns a flat list mixing leaf Nodes (in left-to-right order) with the
    ``_COMBINE`` sentinel marking "pop two values and join them" — enough
    information to both read off the leaves (:func:`_flatten_chain`) and
    rebuild the exact original shape around a substitute leaf sequence
    (:func:`_rebuild_like`), without walking the tree twice recursively.
    """
    ops: List = []
    stack = [(node, False)]
    while stack:
        cur, expanded = stack.pop()
        if isinstance(cur, cls):
            if not expanded:
                stack.append((cur, True))
                stack.append((cur.right, False))
                stack.append((cur.left, False))
            else:
                ops.append(_COMBINE)
        else:
            ops.append(cur)
    return ops


def _flatten_chain(node: Node, cls) -> List[Node]:
    """The leaves of a binary ``cls``-chain, left to right (``[node]`` if
    ``node`` is not itself a ``cls``)."""
    return [op for op in _chain_ops(node, cls) if op is not _COMBINE]


def _fold(cls, parts: List[Node]) -> Node:
    """Left-associative rebuild of ``parts`` under ``cls`` — the shape used
    whenever the leaf sequence actually changed (so there is no "original
    shape" left to preserve)."""
    result = parts[0]
    for part in parts[1:]:
        result = cls(result, part)
    return result


def _rebuild_like(template: Node, cls, leaves) -> Node:
    """Rebuild EXACTLY ``template``'s bracketing, substituting ``leaves`` (an
    iterator, consumed left to right) for its original leaf positions.

    Used only when nothing was removed from the chain, so the result is
    byte-for-byte the same shape as the input (with each leaf replaced by its
    own, independently simplified, form) — callers that compare
    ``result.simplified`` against the input with plain ``==`` when
    ``changed`` is ``False`` get exact equality, not just equivalence.
    """
    stack: List[Node] = []
    for op in _chain_ops(template, cls):
        if op is _COMBINE:
            right = stack.pop()
            left = stack.pop()
            stack.append(cls(left, right))
        else:
            stack.append(next(leaves))
    return stack[0]


# ---------------------------------------------------------------------------
# Eligibility for "drop this conjunct" — the two rules that only make sense
# INSIDE a conjunction (dropping a conjunct that is always true preserves
# meaning; dropping it from a DISJUNCTION would not: A ∨ True ≡ True, not A).
# ---------------------------------------------------------------------------

def _is_trivial_equality(node: Node) -> bool:
    """``t = t`` for any term ``t`` (not just a bare variable): reflexivity of
    ``=`` makes this valid regardless of what ``t`` denotes, so ``φ ∧ (t=t) ≡
    φ`` always — no ``all_different`` assumption needed."""
    return (isinstance(node, Atom) and node.predicate == "="
            and len(node.args) == 2 and node.args[0] == node.args[1])


def _is_redundant_all_diff_ne(node: Node, binders: Dict[str, str]) -> bool:
    """``x ≠ y`` where both ``x`` and ``y`` are separately ∃-bound variables —
    redundant ONLY under the ``all_different=True`` convention (see the module
    docstring). Deliberately narrow:

    - both sides must be plain :class:`Variable` terms (a constant or a
      function application on either side is excluded — the paper's
      convention is about how the model checker treats freshly INTRODUCED
      existential variables, and says nothing about a comparison against a
      fixed denotation);
    - the two names must differ (``x ≠ x`` is not "two separate variables
      happen to be distinct", it is an outright contradiction — leaving it
      alone is the conservative choice, not an oversight);
    - both must be bound by an enclosing ``∃`` specifically — a ``∀``-bound
      variable ranges over the WHOLE domain, so "this witness is distinct
      from that other witness" is not something the model checker's
      convention says anything about.
    """
    if not (isinstance(node, Atom) and node.predicate == "≠" and len(node.args) == 2):
        return False
    left, right = node.args
    if not (isinstance(left, Variable) and isinstance(right, Variable)):
        return False
    if left.name == right.name:
        return False
    return binders.get(left.name) == "exists" and binders.get(right.name) == "exists"


def _is_removable_conjunct(node: Node, all_different: bool, binders: Dict[str, str]) -> bool:
    return _is_trivial_equality(node) or (all_different and _is_redundant_all_diff_ne(node, binders))


def _describe_removed_conjunct(node: Node, all_different: bool) -> str:
    if _is_trivial_equality(node):
        return ("dropped trivial reflexive equality from a conjunction "
                f"(φ ∧ (t=t) ≡ φ): {node.to_unicode_str()}")
    left, right = node.args
    return ("dropped redundant pairwise inequality under all_different=True "
            f"(φ ∧ ({left.name}≠{right.name}) ≡ φ under this kit's "
            "all_different convention, since both are separately ∃-bound "
            f"and hence already distinct): {node.to_unicode_str()}")


def _dedupe_chain(parts: List[Node], op_glyph: str, removed: List[str]) -> List[Node]:
    """Drop later occurrences of a structurally-identical operand (idempotence
    of ∧/∨: ``φ op φ ≡ φ``) — valid regardless of ``op_glyph`` and regardless
    of ``all_different``, so this runs unconditionally for both And and Or."""
    seen = set()
    kept: List[Node] = []
    for part in parts:
        if part in seen:
            removed.append(
                f"dropped duplicate {op_glyph}-operand (idempotence: "
                f"φ {op_glyph} φ ≡ φ): {part.to_unicode_str()}"
            )
            continue
        seen.add(part)
        kept.append(part)
    return kept


def _filter_and_conjuncts(parts: List[Node], all_different: bool,
                           binders: Dict[str, str], removed: List[str]) -> List[Node]:
    """Drop every removable conjunct (:func:`_is_removable_conjunct`), except
    that when EVERY conjunct in the chain is removable, one is kept —
    otherwise the chain would collapse to an empty (nonexistent) formula.
    The kept one is equivalent to True anyway (it is one of the removable
    ones), so keeping it changes nothing observable; which one is kept is an
    arbitrary but deterministic choice (the first, by list order)."""
    eligible = [i for i, p in enumerate(parts) if _is_removable_conjunct(p, all_different, binders)]
    drop = set(eligible)
    if eligible and len(eligible) == len(parts):
        drop.discard(eligible[0])
    kept: List[Node] = []
    for i, part in enumerate(parts):
        if i in drop:
            removed.append(_describe_removed_conjunct(part, all_different))
            continue
        kept.append(part)
    return kept


# ---------------------------------------------------------------------------
# The recursive engine.
# ---------------------------------------------------------------------------

# Node classes that bind exactly one variable over exactly one Node-valued
# "body" field but are NOT a Quantifier subclass, so the dedicated Quantifier
# branch above never sees them — Count/Cardinality/SortedQuantifier/
# SortedCount/SortedCardinality all bind via a field named ``variable`` over
# a field named ``formula``; Lambda binds via ``param`` (a LambdaVar, not a
# Variable) over ``body``. Mirrors exactly the case list
# :func:`unicode_fol_kit.fol._msfl_nodes.free_variables` already special-cases
# for the same reason (a binder whose bound name is not tracked as its own
# scope leaks the ENCLOSING scope's variable classification into a name that,
# inside this node, actually refers to something else entirely).
#
# Used below to SHADOW (remove, not reclassify as "exists"/"forall") the
# bound name out of ``binders`` while descending into the body field only —
# this is deliberately not the same as adding it with a "exists" kind: the
# all_different convention is documented as being about separately ∃-bound
# Quantifier variables specifically, so these binders still never make the
# rule fire on THEIR OWN bound name; the fix here is purely to stop an
# outer, differently-scoped ∃/∀ of the identical name from being applied to
# occurrences that this binder has re-bound (see Finding 1 in the task brief:
# ``all_different=True`` could otherwise drop a ``≠`` between a variable
# re-bound by an enclosing Count/Cardinality/SortedQuantifier/SortedCount/
# SortedCardinality/Lambda and an unrelated, same-named ∃-bound variable
# further out — unsound, since the two occurrences do not denote the same
# thing).
_SINGLE_VAR_BINDER_FIELDS: Dict[type, Tuple[str, str]] = {
    Count: ("variable", "formula"),
    Cardinality: ("variable", "formula"),
    SortedQuantifier: ("variable", "formula"),
    SortedCount: ("variable", "formula"),
    SortedCardinality: ("variable", "formula"),
    Lambda: ("param", "body"),
}


def _simplify(n: Node, binders: Dict[str, str], all_different: bool,
              removed: List[str]) -> Node:
    if isinstance(n, (Variable, Constant, Number, Atom)):
        return n  # leaves/terms: none of the rules below rewrite term structure

    if isinstance(n, Not):
        inner = _simplify(n.formula, binders, all_different, removed)
        if isinstance(inner, Not):
            # ¬¬φ ≡ φ, unconditionally (classical double negation elimination).
            removed.append(
                f"collapsed double negation (¬¬φ ≡ φ): ¬¬{inner.formula.to_unicode_str()}"
            )
            return inner.formula
        return Not(inner)

    if isinstance(n, And):
        raw = _flatten_chain(n, And)
        parts = [_simplify(p, binders, all_different, removed) for p in raw]
        kept = _dedupe_chain(parts, "∧", removed)
        kept = _filter_and_conjuncts(kept, all_different, binders, removed)
        if kept == parts:
            return _rebuild_like(n, And, iter(parts))
        return _fold(And, kept)

    if isinstance(n, Or):
        raw = _flatten_chain(n, Or)
        parts = [_simplify(p, binders, all_different, removed) for p in raw]
        kept = _dedupe_chain(parts, "∨", removed)
        if kept == parts:
            return _rebuild_like(n, Or, iter(parts))
        return _fold(Or, kept)

    if isinstance(n, Quantifier):
        if n.type in _EXISTS:
            kind = "exists"
        elif n.type in _FORALL:
            kind = "forall"
        else:
            raise ValueError(f"simplify_for_checking: unknown quantifier type {n.type!r}")
        new_binders = dict(binders)
        new_binders[n.variable.name] = kind
        body = _simplify(n.formula, new_binders, all_different, removed)
        # ∃x φ ≡ φ / ∀x φ ≡ φ when x does not occur free in φ — valid because
        # this kit's semantics (like Count._expand's own '≥0' case) assumes a
        # NON-EMPTY domain throughout, so a quantifier that never inspects its
        # variable is a no-op regardless of quantifier kind.
        if n.variable.name not in {v.name for v in free_variables(body)}:
            removed.append(
                f"dropped vacuous {n.type}{n.variable.name} ({n.variable.name} "
                "does not occur free in the body; valid on a non-empty domain): "
                f"{n.type}{n.variable.name}"
            )
            return body
        return Quantifier(n.type, n.variable, body)

    # Generic structural fallback: every other node type (Implies, Iff, Xor,
    # Count, Cardinality, Measure, and any modal/hybrid/linear/second-order/
    # MSFL node). Recurse into Node-valued fields; leave the node's own type
    # and every non-Node field untouched. This makes the function total
    # (it never raises on an unfamiliar node) while never MISAPPLYING a
    # classical rule to a same-looking but semantically different construct —
    # e.g. Łukasiewicz LukNegation is a distinct class from Not, so double
    # negation collapse never touches it; WeakConjunction is a distinct class
    # from And, so it never gets the classical idempotence/trivial-conjunct
    # treatment. A Count/Cardinality/SortedQuantifier/SortedCount/
    # SortedCardinality/Lambda node's own bound variable is deliberately NOT
    # added to ``binders`` here as "exists"/"forall" (none of these are a
    # Quantifier subclass, and the all_different convention is documented as
    # being specifically about separately ∃-bound Quantifier variables) — but
    # its name MUST still be shadowed (removed from ``binders``) while
    # descending into the body, or an outer ∃/∀ of the identical name would
    # incorrectly keep classifying occurrences that this binder has re-bound
    # to something else entirely (see ``_SINGLE_VAR_BINDER_FIELDS``).
    binder_fields = _SINGLE_VAR_BINDER_FIELDS.get(type(n))
    shadowed_binders = binders
    shadow_field = None
    if binder_fields is not None:
        var_field, shadow_field = binder_fields
        bound_name = getattr(n, var_field).name
        if bound_name in binders:
            shadowed_binders = dict(binders)
            del shadowed_binders[bound_name]

    new_kwargs = {}
    for f in fields(n):
        val = getattr(n, f.name)
        field_binders = shadowed_binders if f.name == shadow_field else binders
        if isinstance(val, Node):
            new_kwargs[f.name] = _simplify(val, field_binders, all_different, removed)
        elif isinstance(val, (list, tuple)):
            new_kwargs[f.name] = type(val)(
                _simplify(c, field_binders, all_different, removed) if isinstance(c, Node) else c
                for c in val
            )
        else:
            new_kwargs[f.name] = val
    return type(n)(**new_kwargs)


def simplify_for_checking(formula: Node, *, all_different: bool = False) -> SimplifyResult:
    """Simplify ``formula`` for model checking; see the module docstring for
    the full rule list and their equivalence arguments.

    Args:
        formula: any :class:`Node`.
        all_different: if ``True``, ALSO remove pairwise inequalities between
            separately ∃-bound variables (see
            :func:`_is_redundant_all_diff_ne`). This is sound only under the
            model checker's own "separately introduced existential variables
            are already distinct" convention, NOT under standard FOL
            semantics — leave it ``False`` (the default) unless the
            downstream checker actually implements that convention.

    Returns:
        A :class:`SimplifyResult`. Applying :func:`simplify_for_checking`
        again to ``result.simplified`` (same ``all_different``) always yields
        ``changed=False`` — every rule above leaves no further instance of
        its own pattern behind (checked in the test suite).
    """
    removed: List[str] = []
    simplified = _simplify(formula, {}, all_different, removed)
    return SimplifyResult(simplified=simplified, removed=tuple(removed), changed=bool(removed))


# ---------------------------------------------------------------------------
# Existential-chain <-> Count.
# ---------------------------------------------------------------------------

def count_from_existential_chain(formula: Node) -> Optional[Node]:
    """Recognise ``∃x_0…∃x_{n-1} (⋀_i φ(x_i) ∧ ⋀_{i<j} x_i≠x_j)`` and rewrite
    it to ``Count("ge", n, x, φ(x))``. Returns ``None`` if ``formula`` is not
    EXACTLY this pattern.

    Requires, at the top of ``formula``:

    - a chain of ``n ≥ 1`` consecutive ``∃`` quantifiers over ``n`` distinct
      variable names (a ``∀`` anywhere in the prefix, or a shadowed/repeated
      name, is not this pattern);
    - a body that — once fully flattened as a ∧-chain — has EXACTLY
      ``n + n·(n-1)/2`` conjuncts: for every quantified variable exactly one
      unary atom ``φ(x_i)`` (same predicate ``φ`` for all of them), and for
      every unordered pair exactly one ``x_i≠x_j``, and NOTHING else.

    Any deviation — a variable appearing in a further literal (a bond between
    two of the witnesses, say), a mismatched predicate, an inequality against
    a constant, a missing or duplicated pair, an extra or missing conjunct —
    returns ``None`` rather than guessing: since the rewrite DISCARDS
    everything except "n witnesses, all φ, all pairwise distinct", rewriting
    a formula that also asserts something else about those witnesses would
    silently drop that content. This is the CONSERVATIVE direction; the
    all_different flag on :func:`simplify_for_checking` is the narrower,
    non-conservative-in-scope tool for formulas that don't fit this pattern
    exactly but still have redundant pairwise inequalities in them.

    The equivalence this relies on is exactly :meth:`Count._expand`'s own
    encoding (``∃≥n x φ`` unfolds to precisely this shape) — checked via Z3
    equivalence for n≤4 in the test suite, in both directions.
    """
    variables: List[Variable] = []
    body = formula
    while isinstance(body, Quantifier) and body.type in _EXISTS:
        variables.append(body.variable)
        body = body.formula
    n = len(variables)
    if n == 0:
        return None
    names = [v.name for v in variables]
    if len(set(names)) != n:
        return None
    name_set = set(names)

    parts = _flatten_chain(body, And)
    expected = n + n * (n - 1) // 2
    if len(parts) != expected:
        return None

    phi_name: Optional[str] = None
    matched_var: Dict[str, str] = {}
    pairs_seen = set()
    all_pairs = {frozenset((names[i], names[j])) for i in range(n) for j in range(i + 1, n)}

    for part in parts:
        if isinstance(part, Atom) and part.predicate == "≠" and len(part.args) == 2:
            left, right = part.args
            if not (isinstance(left, Variable) and isinstance(right, Variable)):
                return None
            if left.name not in name_set or right.name not in name_set or left.name == right.name:
                return None
            pair = frozenset((left.name, right.name))
            if pair in pairs_seen:
                return None
            pairs_seen.add(pair)
            continue
        if (isinstance(part, Atom) and len(part.args) == 1
                and isinstance(part.args[0], Variable)
                and part.args[0].name in name_set):
            v = part.args[0].name
            if v in matched_var:
                return None
            if phi_name is None:
                phi_name = part.predicate
            elif part.predicate != phi_name:
                return None
            matched_var[v] = part.predicate
            continue
        return None  # anything else — extra/foreign literal — disqualifies the rewrite

    if set(matched_var) != name_set or pairs_seen != all_pairs:
        return None

    rep = variables[0]
    return Count("ge", Number(n), rep, Atom(phi_name, [rep]))


def expand_count(formula: Node) -> Node:
    """Lower every ``Count`` node anywhere in ``formula`` to plain FOL, for
    backends with no ``Count`` node of their own.

    Reuses :meth:`Count._expand` (the same distinct-witnesses lowering
    ``Count.to_z3``/``to_prover9``/``to_tptp`` already call internally)
    rather than duplicating it — this function only supplies the tree walk.
    Mirrors the ``Count``-handling branch of
    :func:`unicode_fol_kit.fol._msfl_nodes.to_fol`'s ``_reduce_nl_nodes``,
    minus that function's other, unrelated reductions (Łukasiewicz collapse,
    sort relativisation): this one does exactly one thing.
    """
    reduced = formula.map_children(expand_count)
    if isinstance(reduced, Count):
        return reduced._expand()
    return reduced
