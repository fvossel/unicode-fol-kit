"""Canonical form and canonical exact match for NL→FOL evaluation.

``canonicalize`` maps a formula to a normal form that quotients out exactly the
"free" syntactic differences that should NOT count as a mismatch when comparing
a predicted FOL formula against a reference one, while staying LOGICALLY
EQUIVALENT to the input. It normalizes four — and only four — kinds of
difference:

  (a) ALPHA-renaming of bound variables (Quantifier / SortedQuantifier bound
      Variable, Lambda param, and the counting-quantifier / set-cardinality
      binders Count and Cardinality, which likewise bind a Variable over their
      matrix): two formulas that differ only in the names of their bound
      variables canonicalize identically. Bound variables are
      renamed to a deterministic scheme (``q0``, ``q1``, … — a single lowercase
      letter plus digits, which is a valid VARIABLE token and therefore
      round-trips through the parser; underscores are deliberately avoided
      because they do not round-trip). The rename is capture-safe.

  (b) COMMUTATIVITY + ASSOCIATIVITY of the commutative connectives: classical
      And, Or, Iff, Xor and fuzzy WeakConjunction, WeakDisjunction,
      StrongConjunction, StrongDisjunction. Nested same-class chains are
      flattened, each operand is canonicalized, the operands are sorted by a
      deterministic alpha-invariant key, and the group is rebuilt left-folded.
      Identical operands are de-duplicated (``P ∧ P`` → ``P``) ONLY for the
      IDEMPOTENT connectives — classical And/Or and fuzzy WeakConjunction (min)
      / WeakDisjunction (max), where ``a ⋆ a ≡ a`` makes removal
      equivalence-preserving. The remaining commutative connectives are NOT
      idempotent (``P ⊕ P ≡ ⊥``, ``P ↔ P ≡ ⊤``, and the Łukasiewicz strong
      conjunction/disjunction t-norm/t-conorm), so their repeated operands are
      kept intact; only flatten + sort applies to them. Implies and
      LukImplication are NOT commutative, so their operand order is preserved.

  (c) DOUBLE NEGATION: ``Not(Not(x))`` → ``x`` and ``LukNegation(LukNegation(x))``
      → ``x`` (Łukasiewicz negation is involutive: 1−(1−x)=x).

It does NOT perform distributivity, CNF/DNF conversion, or any full
logical-equivalence decision. ``canonicalize`` is a normal form for EXACTLY the
set {alpha, commutativity, associativity, operand-dedup, double-negation}; it
sits strictly between raw structural equality (``==`` on frozen nodes) and full
logical equivalence. Two formulas with the same canonical form are logically
equivalent, but logically-equivalent formulas need not share a canonical form
(e.g. ``P → Q`` and ``¬P ∨ Q`` canonicalize differently).

REQUIRED INVARIANTS (each is exercised by tests/test_canonical.py):
  P1 equivalence-preserving: ``canonicalize(f)`` is logically equivalent to f.
  P2 idempotent: ``canonicalize(canonicalize(f)) == canonicalize(f)``.
  P3 alpha-invariance: renaming f's bound variables does not change
     ``canonicalize(f)``.
  P4 comm/assoc-invariance: reordering or reassociating the operands of the
     commutative connectives does not change the result.
  P5 double-negation: ``canonicalize(¬¬f) == canonicalize(f)``.

Implementation note on the alpha-vs-sort ordering interplay: the operand sort
key must be invariant under bound-variable renaming, otherwise sorting and
alpha-renaming would race. We therefore key the sort on the
``to_unicode_str()`` of the ALPHA-NORMALIZED operand, and apply a final
deterministic alpha-normalization pass to the fully structured tree. Because the
sort key is alpha-invariant and the final pass assigns names by binder-encounter
order on a now-stable structure, the whole pipeline reaches a fixpoint —
idempotency (P2) guards against any residual ordering bug.
"""

from typing import List

from unicode_fol_kit.fol.nodes import (
    Node, Variable,
    And, Or, Xor, Iff, Implies,
    Not, Quantifier, SortedQuantifier,
    Count, Cardinality, SortedCount, SortedCardinality,
    WeakConjunction, WeakDisjunction, StrongConjunction, StrongDisjunction,
    LukNegation, LukImplication, LukEquivalence,
    Lambda, LambdaVar,
    free_variables,
)


# Commutative connective classes: associative + commutative, so their operand
# groups may be flattened, sorted, and rebuilt left-folded. Implies /
# LukImplication and the (non-commutative) negations are deliberately excluded.
_COMMUTATIVE = (
    And, Or, Xor, Iff,
    WeakConjunction, WeakDisjunction, StrongConjunction, StrongDisjunction,
)

# IDEMPOTENT commutative connectives — exactly those for which ``a ⋆ a ≡ a``, so
# that de-duplicating repeated operands is equivalence-preserving:
#   And / Or            (classical ∧ ∨ are idempotent)
#   WeakConjunction / WeakDisjunction (fuzzy min / max are idempotent)
# The remaining commutative connectives are NOT idempotent and MUST NOT be
# de-duplicated:
#   Xor / StrongDisjunction (⊕): a ⊕ a ≡ ⊥  (classical) / x⊕x = min{1,2x} (fuzzy)
#   Iff                     (↔): a ↔ a ≡ ⊤
#   StrongConjunction       (⊗): x⊗x = max{0,2x−1} ≢ x
# Removing a duplicate from any of these would change the truth value, breaking
# the equivalence-preservation invariant P1.
_IDEMPOTENT = (And, Or, WeakConjunction, WeakDisjunction)

# Involutive negations: ``op(op(x)) == x``.
_INVOLUTIVE_NEG = (Not, LukNegation)


# ---------------------------------------------------------------------------
# Capture-safe alpha-normalization
# ---------------------------------------------------------------------------

def _alpha_normalize(node: Node) -> Node:
    """Rename every bound variable to a canonical ``q0``, ``q1``, … name.

    Performs a deterministic pre-order traversal: each binder encountered
    (Quantifier / SortedQuantifier / Count / Cardinality over a Variable, Lambda
    over a LambdaVar) consumes the next FREE-name-avoiding ``q``-index and its
    bound occurrences are rewritten to a fresh canonical name of the matching kind
    (Variable for quantifiers/counts/cardinalities, LambdaVar for lambdas). An
    environment maps each currently-in-scope original bound name to its canonical
    replacement; inner binders shadow outer ones of the same name, exactly as
    scope demands.

    The scheme is capture-safe in BOTH directions. (i) An inner binder never
    reuses an enclosing canonical name, because names are minted from a single
    monotonic counter. (ii) A bound variable is never renamed onto a FREE variable
    of the matrix: ``avoid`` holds every free name in ``node`` (a ``q``-name is a
    legal VARIABLE token, so a formula may legitimately contain a free ``q0``), and
    the mint skips any ``q``-index already in ``avoid``. Without (ii) the disjoint
    formulas ``∃x P(x)`` and ``∃x P(q0)`` would both collapse to ``∃q0 P(q0)`` and
    wrongly compare equal — a false positive that breaks equivalence-preservation
    (P1). Free variables themselves are left untouched. The result is invariant
    under any alpha-renaming of ``node`` (P3; renaming bound variables cannot change
    the free-name set) and is idempotent (P2; a second pass sees the same free
    names and the same binder-encounter order, so it assigns identical names).
    """
    counter = [0]
    avoid = frozenset(v.name for v in free_variables(node))
    return _alpha(node, {}, {}, counter, avoid)


def _fresh_canonical_name(counter: list, avoid) -> str:
    """Return the next ``q``-index name that does NOT collide with a free name.

    Advances the monotonic ``counter`` past any ``q``-index present in ``avoid``
    (the set of names free in the whole formula), so a minted bound name is always
    disjoint from every free variable — the capture-safety guarantee (ii) in
    :func:`_alpha_normalize`. Distinctness among minted names is preserved because
    every successful mint consumes a strictly larger counter value.
    """
    name = f"q{counter[0]}"
    counter[0] += 1
    while name in avoid:
        name = f"q{counter[0]}"
        counter[0] += 1
    return name


def _alpha(node: Node, var_env: dict, lam_env: dict, counter: list, avoid) -> Node:
    """Recurse, rewriting bound occurrences per the two environments.

    ``var_env`` maps an in-scope original logical-variable name to its canonical
    Variable; ``lam_env`` does the same for lambda-bound names → canonical
    LambdaVar. The environments are copied (never mutated) when entering a
    binder, so siblings never see each other's bindings. ``avoid`` is the frozen
    set of names free in the whole formula, threaded unchanged so every fresh
    canonical name skips them (see :func:`_fresh_canonical_name`).
    """
    if isinstance(node, Variable):
        return var_env.get(node.name, node)
    if isinstance(node, LambdaVar):
        return lam_env.get(node.name, node)

    if isinstance(node, Quantifier):
        fresh = Variable(_fresh_canonical_name(counter, avoid))
        inner = dict(var_env)
        inner[node.variable.name] = fresh
        return Quantifier(node.type, fresh, _alpha(node.formula, inner, lam_env, counter, avoid))

    if isinstance(node, SortedQuantifier):
        fresh = Variable(_fresh_canonical_name(counter, avoid))
        inner = dict(var_env)
        inner[node.variable.name] = fresh
        return SortedQuantifier(
            node.type, fresh, node.sort,
            _alpha(node.formula, inner, lam_env, counter, avoid),
        )

    if isinstance(node, Lambda):
        fresh = LambdaVar(_fresh_canonical_name(counter, avoid))
        inner = dict(lam_env)
        inner[node.param.name] = fresh
        return Lambda(fresh, _alpha(node.body, var_env, inner, counter, avoid))

    # Count / Cardinality also bind a logical Variable over their matrix (Count
    # additionally carries the op code and the symbolic bound n, both copied
    # verbatim — neither contains a variable). They rename like a quantifier.
    if isinstance(node, Count):
        fresh = Variable(_fresh_canonical_name(counter, avoid))
        inner = dict(var_env)
        inner[node.variable.name] = fresh
        return Count(node.op, node.n, fresh,
                     _alpha(node.formula, inner, lam_env, counter, avoid))

    if isinstance(node, Cardinality):
        fresh = Variable(_fresh_canonical_name(counter, avoid))
        inner = dict(var_env)
        inner[node.variable.name] = fresh
        return Cardinality(fresh, _alpha(node.formula, inner, lam_env, counter, avoid))

    # The sorted counterparts bind a Variable too; the sort string is copied verbatim.
    if isinstance(node, SortedCount):
        fresh = Variable(_fresh_canonical_name(counter, avoid))
        inner = dict(var_env)
        inner[node.variable.name] = fresh
        return SortedCount(node.op, node.n, fresh, node.sort,
                           _alpha(node.formula, inner, lam_env, counter, avoid))

    if isinstance(node, SortedCardinality):
        fresh = Variable(_fresh_canonical_name(counter, avoid))
        inner = dict(var_env)
        inner[node.variable.name] = fresh
        return SortedCardinality(fresh, node.sort,
                                 _alpha(node.formula, inner, lam_env, counter, avoid))

    # Non-binder structural node (Atom, Function, Not, binary connectives,
    # Measure, Contrast, Application, …): recurse into every child with the same
    # environments.
    return node.map_children(lambda c: _alpha(c, var_env, lam_env, counter, avoid))


# ---------------------------------------------------------------------------
# Structural canonicalization (comm/assoc/dedupe/double-negation)
# ---------------------------------------------------------------------------

def _flatten(node: Node, cls: type) -> List[Node]:
    """Collect the operands of a maximal same-class commutative chain.

    Walks the left/right spine of ``node`` (assumed an instance of ``cls``),
    descending into any nested node of the same class so that, e.g.,
    ``(P ∧ Q) ∧ R`` and ``P ∧ (Q ∧ R)`` both yield ``[P, Q, R]``. Operands of a
    different class terminate the chain and are returned as-is (not yet
    canonicalized — the caller canonicalizes each).
    """
    out: List[Node] = []
    for side in (node.left, node.right):
        if isinstance(side, cls):
            out.extend(_flatten(side, cls))
        else:
            out.append(side)
    return out


def _canon_operands(node: Node, cls: type, levels: dict) -> List[Node]:
    """Return the canonicalized operands of a commutative ``cls`` group.

    Flattens the raw chain, canonicalizes each operand (threading the enclosing
    binder ``levels`` map), then RE-FLATTENS any operand that itself canonicalized
    into the same class. The re-flatten step is essential: a double-negation
    collapse can turn an operand such as ``¬¬(P ∨ Q)`` into a bare ``P ∨ Q`` (the
    same class as its parent ``∨``), and that newly-exposed nested group must be
    absorbed into the parent chain — otherwise the duplicate ``Q`` in
    ``¬¬(P ∨ Q) ∨ Q`` would survive a single pass (breaking idempotency P2 and
    associativity-invariance P4).
    """
    out: List[Node] = []
    for raw in _flatten(node, cls):
        canon = _structural(raw, levels)
        if isinstance(canon, cls):
            out.extend(_flatten(canon, cls))
        else:
            out.append(canon)
    return out


def _sort_key(operand: Node, levels: dict) -> str:
    """Deterministic sort key, invariant under bound-variable renaming AND under
    commutative reordering of sibling operands.

    The commutative sort runs bottom-up *before* the final whole-tree
    ``_alpha_normalize`` pass renames variables bound by ENCLOSING binders. A
    name-sensitive key would therefore order operands differently on the first
    pass (enclosing binders still named ``x``, ``w``) than on the second (renamed
    ``q0``, ``q1``) — the classic alpha-vs-sort non-idempotence trap (P2). We
    avoid it by encoding every variable occurrence by POSITION, not name:

      * a variable bound by an ENCLOSING binder is encoded by that binder's LEVEL
        (its depth from the root, supplied in ``levels``). The level is invariant
        under commutative reordering of siblings — reordering operands never
        changes any binder's depth — so two operands that reference *different*
        enclosing binders (e.g. ``P(x)`` vs ``P(y)`` under ``∀y ∀x``) get
        DIFFERENT keys and a stable order, fixing comm/assoc-invariance (P4);
      * a variable bound INSIDE the operand is encoded by a local de-Bruijn-style
        index assigned in binder-encounter order;
      * a genuinely free variable is encoded by its name (such variables are not
        renamed by canonicalize, so the name is already stable).

    Because the key depends on no renamable name, the ordering is identical
    across passes (P2) and identical for any alpha-variant of the input (P3).
    """
    parts: List[str] = []
    local_depth = [0]  # monotonic binder counter; immune to shadowing

    def rec(n: Node, local: dict) -> None:
        cls_name = type(n).__name__
        if isinstance(n, (Variable, LambdaVar)):
            if n.name in local:
                parts.append(f"b{local[n.name]}")            # operand-bound
            elif n.name in levels:
                parts.append(f"L{levels[n.name]}")           # enclosing-bound
            else:
                parts.append(f"v:{n.name}")                  # genuinely free
            return
        if isinstance(n, (Quantifier, SortedQuantifier)):
            inner = dict(local)
            inner[n.variable.name] = local_depth[0]
            local_depth[0] += 1
            sort = getattr(n, "sort", "")
            parts.append(f"Q{n.type}:{sort}")
            rec(n.formula, inner)
            return
        if isinstance(n, Lambda):
            inner = dict(local)
            inner[n.param.name] = local_depth[0]
            local_depth[0] += 1
            parts.append("LAM")
            rec(n.body, inner)
            return
        if isinstance(n, Count):
            inner = dict(local)
            inner[n.variable.name] = local_depth[0]
            local_depth[0] += 1
            # op and n distinguish ∃≥3 from ∃≤3 / ∃≥5; neither is renamable, so
            # the key stays invariant under bound-variable renaming (P3).
            parts.append(f"CNT{n.op}:{n.n.value}")
            rec(n.formula, inner)
            return
        if isinstance(n, Cardinality):
            inner = dict(local)
            inner[n.variable.name] = local_depth[0]
            local_depth[0] += 1
            parts.append("CARD")
            rec(n.formula, inner)
            return
        if isinstance(n, SortedCount):
            inner = dict(local)
            inner[n.variable.name] = local_depth[0]
            local_depth[0] += 1
            # op, n AND sort are all significant and non-renamable.
            parts.append(f"SCNT{n.op}:{n.n.value}:{n.sort}")
            rec(n.formula, inner)
            return
        if isinstance(n, SortedCardinality):
            inner = dict(local)
            inner[n.variable.name] = local_depth[0]
            local_depth[0] += 1
            parts.append(f"SCARD:{n.sort}")
            rec(n.formula, inner)
            return
        parts.append(cls_name)
        if cls_name == "Atom":
            parts.append(n.predicate)
        elif cls_name == "Function":
            parts.append(n.name)
        for child in n._child_nodes():
            rec(child, local)
        parts.append("/")

    rec(operand, {})
    return "|".join(parts)


# NOTE on de-duplication: the dedup identity key is ``_sort_key`` itself. Two
# operands sharing the same enclosing scope are logically identical iff they are
# alpha-equivalent with the variables bound by ENCLOSING binders held fixed —
# which is EXACTLY what ``_sort_key`` encodes (enclosing-bound variables by
# level, operand-bound by local index, genuinely-free by name). Crucially this
# is capture-proof: a string built from ``_alpha_normalize(operand)`` would, on a
# second pass, capture a free variable that the first pass had renamed to ``q0``
# under a freshly-minted bound ``q0`` (e.g. the shadowing case
# ``∃x R(x) ∧ ∃z R(x)``), wrongly collapsing two NON-equivalent operands and
# breaking both idempotency (P2) and equivalence-preservation (P1). Keying dedup
# on ``_sort_key`` avoids any name-based capture entirely.


def _structural(node: Node, levels: dict) -> Node:
    """Apply comm/assoc/dedupe and double-negation, bottom-up.

    ``levels`` maps each variable bound by an ENCLOSING binder to that binder's
    level (depth from the root); it is extended when recursing through a
    quantifier or lambda and consulted by ``_sort_key`` so the commutative sort
    is stable under bound-variable renaming (see ``_sort_key``).

    Children are canonicalized first; then double negations collapse and
    commutative groups are flattened, their operands sorted by ``_sort_key`` and
    (for the idempotent connectives only) de-duplicated, and the group is rebuilt
    left-folded. Bound-variable renaming is deferred to a single final pass (see
    ``canonicalize``).
    """
    # Double negation: collapse op(op(x)) for the involutive negations.
    for neg_cls in _INVOLUTIVE_NEG:
        if isinstance(node, neg_cls) and isinstance(node.formula, neg_cls):
            return _structural(node.formula.formula, levels)

    if isinstance(node, _COMMUTATIVE):
        cls = type(node)
        operands = _canon_operands(node, cls, levels)
        operands.sort(key=lambda op: _sort_key(op, levels))
        if isinstance(node, _IDEMPOTENT):
            # Dedupe operands ONLY for the idempotent connectives (∧ ∨ and fuzzy
            # min/max), where P ⋆ P ≡ P makes removal equivalence-preserving.
            # Dedup keys on ``_sort_key`` (level-encoded, capture-proof — see the
            # note above), so alpha-equivalent operands like (∀x P(x)) and
            # (∀y P(y)) collapse while genuinely distinct operands like R(x) and
            # R(w) do NOT. Xor / Iff / StrongConjunction / StrongDisjunction are
            # NOT idempotent and are left intact (deduping them would break P1).
            seen: set = set()
            deduped: List[Node] = []
            for op in operands:
                key = _sort_key(op, levels)
                if key not in seen:
                    seen.add(key)
                    deduped.append(op)
            operands = deduped
        result = operands[0]
        for op in operands[1:]:
            result = cls(result, op)
        return result

    # Binders extend the enclosing-level map for their body, then keep their bound
    # variable verbatim (it is renamed by the final _alpha_normalize pass). The
    # new level is one past the deepest existing one — NOT ``len(levels)`` — so a
    # shadowing binder (e.g. the inner ``∀z`` in ``∀z ∀z ∀w …``) overwrites its
    # name's entry yet still advances the depth, keeping every level distinct.
    next_level = (max(levels.values()) + 1) if levels else 0
    if isinstance(node, Quantifier):
        inner = dict(levels)
        inner[node.variable.name] = next_level
        return Quantifier(node.type, node.variable, _structural(node.formula, inner))
    if isinstance(node, SortedQuantifier):
        inner = dict(levels)
        inner[node.variable.name] = next_level
        return SortedQuantifier(node.type, node.variable, node.sort,
                                _structural(node.formula, inner))
    if isinstance(node, Lambda):
        inner = dict(levels)
        inner[node.param.name] = next_level
        return Lambda(node.param, _structural(node.body, inner))
    if isinstance(node, Count):
        inner = dict(levels)
        inner[node.variable.name] = next_level
        return Count(node.op, node.n, node.variable,
                     _structural(node.formula, inner))
    if isinstance(node, Cardinality):
        inner = dict(levels)
        inner[node.variable.name] = next_level
        return Cardinality(node.variable, _structural(node.formula, inner))
    if isinstance(node, SortedCount):
        inner = dict(levels)
        inner[node.variable.name] = next_level
        return SortedCount(node.op, node.n, node.variable, node.sort,
                           _structural(node.formula, inner))
    if isinstance(node, SortedCardinality):
        inner = dict(levels)
        inner[node.variable.name] = next_level
        return SortedCardinality(node.variable, node.sort,
                                 _structural(node.formula, inner))

    # Any other node (Implies, LukImplication, Not/LukNegation without a nested
    # negation, Contrast, Measure, atoms, terms, Application): keep its shape,
    # recursing structurally into the children. Operand order of the
    # non-commutative connectives is thereby preserved.
    return node.map_children(lambda c: _structural(c, levels))


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------

def canonicalize(node: Node) -> Node:
    """Return the canonical form of ``node`` (see the module docstring).

    The result is logically equivalent to ``node`` (P1) and quotients out
    exactly alpha-renaming (P3), commutativity/associativity (P4), operand
    duplication, and double negation (P5). It is idempotent (P2).

    Pipeline: first ``_structural`` rewrites the tree under comm/assoc/dedupe and
    double-negation (sorting commutative operands by a key invariant under
    bound-variable renaming and sibling reordering — see ``_sort_key``), then a
    single ``_alpha_normalize`` pass assigns canonical bound-variable names over
    the now-stable structure.
    """
    return _alpha_normalize(_structural(node, {}))


def exact_match(pred: Node, ref: Node, canonical: bool = True) -> bool:
    """Return whether ``pred`` matches ``ref``.

    When ``canonical`` is True (the default), the comparison is up to canonical
    form: ``canonicalize(pred) == canonicalize(ref)``, so differences in
    bound-variable names, commutative-operand order/association, duplicated
    operands, and double negation do not cause a mismatch. When ``canonical`` is
    False, the comparison is raw structural equality (``pred == ref``); because
    the nodes are frozen and hashable with tuple-normalized argument lists, this
    already ignores list-vs-tuple construction but nothing else.
    """
    if canonical:
        return canonicalize(pred) == canonicalize(ref)
    return pred == ref
