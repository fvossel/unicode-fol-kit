"""Sound first-order resolution theorem prover (refutation-based).

A self-contained, Prover9-free decision procedure for first-order entailment and
validity, built on the project's existing normal-form and unification machinery.
It is *sound* — it never reports a theorem that is not one — but, since
first-order resolution is only semi-decidable, it is deliberately *incomplete*
under a step bound: when the bound is hit it conservatively reports "not proved".

Pipeline:

1. Clausal form (:func:`to_clauses`). A formula is ``skolemize``-d (prenex NNF,
   existentials replaced by Skolem terms, universal prefix retained), the ∀
   prefix is dropped (``_prenex_split``), the matrix is put into CNF (``_cnf``)
   and split into clauses (``_clauses``). Each literal is a positive ``Atom`` or
   a ``Not(Atom)``; each clause is a ``frozenset`` of literals; the clause set is
   a ``set`` of such frozensets. Variables are implicitly universally quantified.

2. Standardize apart (:func:`_standardize_apart`). Before two clauses are
   resolved their variables are renamed to fresh disjoint names so the clauses
   share no variable. This is required for soundness.

3. Binary resolution (:func:`_resolvents`). For a literal ``L`` in one clause and
   a complementary literal ``M`` in the other (one ``Atom A``, the other
   ``Not(B)`` with ``A``/``B`` the same predicate and arity), the atoms are
   unified; on success with mgu σ the resolvent is σ applied to
   ``(C1 ∖ L) ∪ (C2 ∖ M)``.

4. Factoring (:func:`_factors`). Within a clause, two literals of the same
   polarity that unify are merged under their mgu, yielding a factored clause —
   needed for completeness on some inputs.

5. Redundancy elimination (:func:`_is_tautology`, :func:`_subsumes`). A clause
   containing a literal and its exact complement on the same atom is a
   tautology and is never kept. A clause D is discarded the moment some kept
   clause C subsumes it (``∃σ`` — binding only C's variables via one-sided
   matching, :func:`_match` — with ``Cσ ⊆ D``); conversely, keeping a new
   clause D retires every previously kept clause that D subsumes. This keeps
   the given-clause set free of redundant clauses without weakening what is
   ultimately derivable — see :func:`refute` for why completeness survives.

6. Equality (:func:`_paramodulants_cross`,
   :func:`_reflexivity_resolvents`, :func:`_demodulate_to_fixpoint`). Equality
   (``=``) is, by itself, just an ordinary uninterpreted binary predicate to
   every mechanism above — nothing here or elsewhere in this module injects
   reflexivity/symmetry/transitivity/congruence AXIOMS. Instead the module
   adds equality's INFERENCE RULES directly:

   - Paramodulation: from a positive equality literal ``s ≈ t`` in one clause
     and a literal ``L`` containing a subterm at position ``p`` in another
     (or the same) clause, if ``s`` unifies with that subterm (mgu σ), infer
     the clauses' remainders plus ``L[p ↦ t]`` — all under σ. Unconditionally
     SOUND in either direction (from ``s`` into occurrences that look like
     ``s``, or symmetrically from ``t`` into occurrences that look like
     ``t``); a simple term order (:func:`_term_gt` — weight = term size, ties
     broken lexicographically by ``to_unicode_str()``, see its docstring)
     prunes the search by allowing paramodulation only from the
     order-greater side when the order strictly decides, trying both
     directions only when it does not (which, under this concrete order,
     only happens for two occurrences of the very same term). Paramodulation
     is ONLY generated cross-clause (:func:`_paramodulants_cross`,
     standardized apart like :func:`_resolvents`) — a clause paramodulating
     into itself goes through the same path with a renamed copy via the
     given/kept loop. A shared-instance "self-paramodulation" shortcut
     (dropping both the consumed equation and the target literal from ONE
     instantiation) is deliberately absent: it is UNSOUND — for
     ``{u ≈ v, L[u]}`` it would infer ``{L[v]}``, false in any model that
     satisfies the clause via ``L[u]`` alone while ``u ≠ v`` (adversarial
     review, Tier 3: the shortcut produced confirmed false-positive
     refutations and was removed together with its checker rule).
   - Reflexivity resolution (:func:`_reflexivity_resolvents`): a literal
     ``¬(u ≈ v)`` where ``u``, ``v`` unify is dropped from its clause under
     the unifier — the mechanism that closes goals like ``⊢ c=c`` (whose
     negation clausifies to ``{¬(c=c)}``).
   - Demodulation (:func:`_demodulate_to_fixpoint`): a SIMPLIFICATION, not a
     search-widening inference. A kept UNIT clause ``{l ≈ r}`` is oriented by
     the same term order and used as a rewrite rule ``l → r`` (only when the
     order strictly says so; an unoriented unit equation contributes no
     rule). Newly generated clauses are rewritten to a fixpoint using
     one-sided MATCHING (:func:`_match_term` — not unification: the rule's
     variables bind, the target's are held fixed) before being tested for
     redundancy/kept — every individual rewrite is its own accounted step
     against ``max_steps`` (see :func:`refute`), never a free/silent
     rewrite. Only NEWLY GENERATED clauses are demodulated (forward
     demodulation); already-kept clauses are never retroactively
     re-simplified by a later rule (backward demodulation is out of scope).

   Honesty note, as promised by this module's general incompleteness stance:
   paramodulation + factoring + resolution is refutation-complete for
   first-order logic WITH equality in principle (this is the classical
   paramodulation completeness theorem), but this implementation does not
   pursue the additional refinements (selection functions, the "basic"
   restriction, splitting, a genuine reduction/simplification ORDER with the
   substitution- and subterm-compatibility closure a real Knuth–Bendix or
   lexicographic path order provides) that a serious equality prover needs
   to be practically complete. This stays SOUND unconditionally; completeness
   for equality problems is emphatically NOT guaranteed beyond what small,
   textbook-sized problems reach within ``max_steps`` — it is a didactic
   equality prover, not a competitive one.

7. Saturation (:func:`refute`). Resolution, factoring, and the equality rules
   above are iterated, filtered through the redundancy elimination in step 5
   (applied after demodulation simplifies each new candidate), until the
   empty clause ``frozenset()`` appears (⇒ unsatisfiable / refuted) or no new,
   non-redundant clause is produced (⇒ saturated) or a step bound is reached
   (⇒ undecided, reported conservatively as not refuted).

Public API: :func:`to_clauses`, :func:`refute`, :func:`prove`,
:func:`is_valid_resolution`.
"""

from ..fol.nodes import (
    Node, Atom, Not, Implies, Quantifier, Variable, Constant, Number, Function,
    Measure,
)
from ..fol.normalforms import skolemize, _prenex_split, _cnf, _clauses
from ..fol.unification import unify, apply_subst


# ---------------------------------------------------------------------------
# Free variables and universal closure
# ---------------------------------------------------------------------------

def _free_var_names(node: Node, bound: frozenset = frozenset()) -> set:
    """Return the set of names of variables occurring free in node.

    A :class:`Variable` is free unless its name is bound by an enclosing
    :class:`Quantifier`. Recurses structurally; the quantifier's bound name is
    added to ``bound`` for its body. The input is not mutated.
    """
    if isinstance(node, Variable):
        return set() if node.name in bound else {node.name}
    if isinstance(node, (Constant, Number)):
        return set()
    if isinstance(node, Quantifier):
        return _free_var_names(node.formula, bound | {node.variable.name})
    names = set()
    for child in node._child_nodes():
        names |= _free_var_names(child, bound)
    return names


def _universal_closure(node: Node) -> Node:
    """Return node wrapped in ∀ for each of its free variables.

    Closing a source formula over its free variables BEFORE skolemisation is a
    soundness requirement: ``skolemize`` is only satisfiability-preserving for
    sentences. If a free variable were left in the matrix, the per-clause
    "implicitly universally quantified" reading used by resolution would
    decouple it from existentials in its scope — e.g. ``¬(P(x) → ∀y P(y))``
    would skolemise to ``P(x) ∧ ¬P(sk0)`` with a free ``x`` and a Skolem
    *constant* ``sk0``, which spuriously resolve to the empty clause. Closing
    first makes the existential a Skolem *function* of the universal, so the
    occurs-check correctly blocks the unsound resolution. The names are sorted so
    the closure is deterministic. The input is not mutated.
    """
    free = sorted(_free_var_names(node))
    result = node
    for name in reversed(free):
        result = Quantifier("∀", Variable(name), result)
    return result


# ---------------------------------------------------------------------------
# Clausal form
# ---------------------------------------------------------------------------

def _symbol_names(node: Node) -> set:
    """Return every constant, function, and predicate symbol name in node.

    Variables are excluded (they are renamed separately). Used to detect which
    symbols skolemisation introduced, so they can be made globally unique.
    """
    names = set()
    for n in node.walk():
        if isinstance(n, Constant):
            names.add(n.name)
        elif isinstance(n, Function):
            names.add(n.name)
        elif isinstance(n, Atom):
            names.add(n.predicate)
    return names


def _rename_symbols(node: Node, mapping: dict) -> Node:
    """Return node with each Constant/Function name remapped via ``mapping``.

    Only Constant and Function *symbol names* are rewritten (predicates and
    variables are untouched). This makes the Skolem symbols introduced by one
    source formula disjoint from those of another, so two independently
    skolemised sources cannot share a Skolem name (e.g. both producing ``sk0``)
    and spuriously resolve. Recursion is fully structural (``map_children``), so
    it works on any node — including the quantifier-prefixed, still-connective
    formula produced by skolemisation, before prenex-splitting. The input is not
    mutated.
    """
    if isinstance(node, Constant):
        return Constant(mapping.get(node.name, node.name))
    if isinstance(node, Function):
        return Function(mapping.get(node.name, node.name),
                        [_rename_symbols(a, mapping) for a in node.args])
    return node.map_children(lambda c: _rename_symbols(c, mapping))


def to_clauses(formula: Node, sk_counter: list = None) -> set:
    """Return the clausal form of a single formula as a set of frozensets.

    The formula is first universally closed over its free variables (a soundness
    requirement before skolemisation — see :func:`_universal_closure`), then
    skolemised (prenex NNF, existentials → Skolem terms, ∀ prefix kept). The
    Skolem symbols that skolemisation introduced are renamed to globally unique
    names — using the shared mutable cursor ``sk_counter`` when one is supplied —
    so that two independently clausified source formulas can never share a Skolem
    symbol (which would be UNSOUND: e.g. ``∃x P(x)`` and the negated conclusion of
    ``∀y P(y)`` both skolemise to ``sk0`` and would spuriously resolve to the
    empty clause). The universal prefix is then dropped, the matrix is converted
    to CNF and split into clauses. Each literal is a positive :class:`Atom` or a
    :class:`Not` wrapping an Atom; each clause is a ``frozenset`` of literals; the
    result is a ``set`` of those frozensets. The remaining variables are
    implicitly universally quantified. The input node is not mutated.
    """
    closed = _universal_closure(formula)
    before = _symbol_names(closed)
    sk = skolemize(closed)
    if sk_counter is None:
        sk_counter = [0]
    # Symbols present after skolemisation but not before are Skolem symbols.
    introduced = _symbol_names(sk) - before
    mapping = {}
    for name in sorted(introduced):
        mapping[name] = f"_sk{sk_counter[0]}"
        sk_counter[0] += 1
    if mapping:
        sk = _rename_symbols(sk, mapping)
    _, matrix = _prenex_split(sk)
    cnf = _cnf(matrix)
    result = set()
    for clause in _clauses(cnf):
        result.add(frozenset(clause))
    return result


# ---------------------------------------------------------------------------
# Literal helpers
# ---------------------------------------------------------------------------

def _atom_of(literal: Node) -> Atom:
    """Return the underlying Atom of a literal (Atom or Not(Atom))."""
    if isinstance(literal, Not):
        return literal.formula
    return literal


def _is_positive(literal: Node) -> bool:
    """Return True iff the literal is a positive Atom (not wrapped in Not)."""
    return isinstance(literal, Atom)


def _subst_literal(literal: Node, subst: dict) -> Node:
    """Apply a substitution to a literal, preserving its polarity."""
    if isinstance(literal, Not):
        return Not(apply_subst(literal.formula, subst))
    return apply_subst(literal, subst)


def _rename_term(node: Node, mapping: dict) -> Node:
    """Return node with each Variable replaced via a one-level name mapping.

    Unlike :func:`apply_subst`, this does NOT follow chains: a variable name is
    looked up exactly once in ``mapping``. That makes it safe for standardizing
    apart, where a fresh name may itself appear as a key (e.g. renaming a clause
    whose variables are already ``_r0`` while ``_r0`` is being mapped to a new
    fresh variable), which would otherwise loop.
    """
    if isinstance(node, Variable):
        return mapping.get(node.name, node)
    if isinstance(node, (Constant, Number)):
        return node
    if isinstance(node, Function):
        return Function(node.name, [_rename_term(a, mapping) for a in node.args])
    if isinstance(node, Measure):
        # μ(entity, dimension) is an ordinary binary term (the exports lower it
        # to the uninterpreted function measure/2), so renaming recurses into
        # both argument slots exactly as for Function.
        return Measure(_rename_term(node.entity, mapping),
                       _rename_term(node.dimension, mapping))
    if isinstance(node, Atom):
        return Atom(node.predicate, [_rename_term(a, mapping) for a in node.args])
    if isinstance(node, Not):
        return Not(_rename_term(node.formula, mapping))
    raise TypeError(f"_rename_term: unsupported node type {type(node).__name__}")


# ---------------------------------------------------------------------------
# Standardizing variables apart
# ---------------------------------------------------------------------------

def _lit_key(literal) -> str:
    """Canonical sort key for a literal (its surface form): the saturation loop
    must visit literals and clauses in a content-determined order so a proof
    search is reproducible run to run (frozenset iteration is hash-randomised)."""
    return literal.to_unicode_str()


def _clause_vars(clause: frozenset) -> set:
    """Return the set of variable names occurring anywhere in a clause."""
    names = set()
    for literal in clause:
        for node in _atom_of(literal).walk():
            if isinstance(node, Variable):
                names.add(node.name)
    return names


def _rename_clause(clause: frozenset, counter: list) -> frozenset:
    """Return a copy of clause with every variable renamed to a fresh name.

    ``counter`` is a single-element list used as a shared mutable cursor so that
    successive renamings across the whole run draw disjoint names (``_r0``,
    ``_r1`` …). The mapping is consistent within the clause, so distinct
    occurrences of the same variable stay shared.
    """
    mapping = {}
    # Sorted: variable numbering must be a function of the clause CONTENT, not
    # of set iteration order — otherwise two runs of the same proof search build
    # alpha-variant (differently named) clauses, the kept-set dedup stops
    # recognising repeats, and whether a goal closes within max_steps becomes
    # hash-seed-dependent (an irreproducible verdict).
    for name in sorted(_clause_vars(clause)):
        mapping[name] = Variable(f"_r{counter[0]}")
        counter[0] += 1
    if not mapping:
        return clause
    return frozenset(_rename_term(lit, mapping) for lit in clause)


# ---------------------------------------------------------------------------
# Redundancy elimination: tautology deletion and clause subsumption
# ---------------------------------------------------------------------------

def _is_tautology(clause: frozenset) -> bool:
    """Return True iff clause contains a literal and its exact complement.

    A clause is a tautology (true in every interpretation, hence useless as a
    resolution premise) when it contains both a positive occurrence and a
    negative occurrence of the SAME atom — same predicate, same arguments,
    checked by structural equality, not merely unifiability. ``P(x) ∨ ¬P(y)``
    is NOT caught (x and y are different atoms syntactically, and identifying
    them would require instantiation this check does not perform); ``P(x) ∨
    ¬P(x)`` is. The empty clause is never a tautology.
    """
    positive = {_atom_of(l) for l in clause if _is_positive(l)}
    negative = {_atom_of(l) for l in clause if not _is_positive(l)}
    return bool(positive & negative)


def _match_term(pattern: Node, target: Node, subst: dict):
    """One-sided structural match of pattern against target, extending subst.

    Unlike :func:`~unicode_fol_kit.fol.unification.unify`, which may bind
    variables on EITHER side, this binds only PATTERN's variables; TARGET is
    held fixed and its own variables (if any) are treated as opaque constants
    — never instantiated. That asymmetry is exactly what clause subsumption
    needs: the subsuming clause's variables range over all its instances, but
    the subsumed clause is the fixed fact being checked against, not a term
    free to unify. A repeated pattern variable must match the same target
    subterm everywhere (checked via structural equality against the existing
    binding). Returns the extended substitution, or None if no match exists.
    No occurs-check is needed: nothing is ever built from a pattern variable's
    own binding, so no cyclic term can arise.
    """
    if isinstance(pattern, Variable):
        if pattern.name in subst:
            return subst if subst[pattern.name] == target else None
        extended = dict(subst)
        extended[pattern.name] = target
        return extended
    if isinstance(pattern, Function):
        if (not isinstance(target, Function)
                or pattern.name != target.name
                or len(pattern.args) != len(target.args)):
            return None
        for p_arg, t_arg in zip(pattern.args, target.args):
            subst = _match_term(p_arg, t_arg, subst)
            if subst is None:
                return None
        return subst
    if isinstance(pattern, Measure):
        if not isinstance(target, Measure):
            return None
        subst = _match_term(pattern.entity, target.entity, subst)
        if subst is None:
            return None
        return _match_term(pattern.dimension, target.dimension, subst)
    # Constant / Number (or any other leaf term): match iff structurally
    # identical. Dataclass equality already requires equal type, so e.g. a
    # Constant pattern can never match a Function or Variable target here.
    return subst if pattern == target else None


def _match(pattern_atom: Atom, target_atom: Atom, subst: dict = None):
    """One-sided match of two atoms: bind pattern_atom's variables against
    target_atom's structure (see :func:`_match_term`). Same predicate and
    arity are required; arguments are matched pairwise, threading the
    substitution left to right. Returns the substitution, or None on failure.
    ``subst`` defaults to the empty substitution.
    """
    if subst is None:
        subst = {}
    if (pattern_atom.predicate != target_atom.predicate
            or len(pattern_atom.args) != len(target_atom.args)):
        return None
    for p_arg, t_arg in zip(pattern_atom.args, target_atom.args):
        subst = _match_term(p_arg, t_arg, subst)
        if subst is None:
            return None
    return subst


def _match_literal(pattern_lit: Node, target_lit: Node, subst: dict):
    """One-sided match of two literals: same polarity, then :func:`_match` on
    their atoms. Returns the extended substitution, or None on failure."""
    if _is_positive(pattern_lit) != _is_positive(target_lit):
        return None
    return _match(_atom_of(pattern_lit), _atom_of(target_lit), subst)


def _subsumes(pattern_clause: frozenset, target_clause: frozenset) -> bool:
    """Return True iff pattern_clause subsumes target_clause.

    Clause subsumption: ``∃σ`` (binding only pattern_clause's variables) with
    ``σ(pattern_clause) ⊆ target_clause`` as a set of literals — i.e. every
    literal of pattern_clause can be assigned, under one SHARED substitution,
    to some literal of target_clause. The assignment need not be injective:
    two distinct pattern literals may map to the same target literal (e.g.
    ``{P(x), P(y)}`` subsumes ``{P(a)}`` via x, y ↦ a both landing on the sole
    target literal). Decided by backtracking search over literal assignments.

    Only the boolean answer is observable here (not which σ was found), and
    that answer is a pure function of the two clauses' CONTENT regardless of
    what order literals are tried internally — an existential search visits
    every candidate assignment either way — so, unlike the resolvent/factor
    generation order elsewhere in this module, no content-based sort is
    needed for :func:`refute`'s determinism guarantee. Internally, target
    literals are bucketed by ``(predicate, polarity)`` so each pattern
    literal only ever considers candidates it could possibly match (a
    predicate/polarity mismatch is rejected by an O(1) dict lookup instead of
    a doomed call into :func:`_match_literal`), and pattern literals are tried
    rarest-candidate-first so an unmatchable pattern literal fails fast
    instead of being discovered deep in the recursion.

    A subsumed clause is logically redundant: it is entailed by the subsuming
    clause alone (an instance of a clause already follows from that clause),
    so discarding it loses no logical content.
    """
    pattern_lits = list(pattern_clause)
    if not pattern_lits:
        return True  # the empty clause is a subset of every clause

    buckets = {}
    for lit in target_clause:
        key = (_atom_of(lit).predicate, _is_positive(lit))
        buckets.setdefault(key, []).append(lit)

    def candidates(lit):
        return buckets.get((_atom_of(lit).predicate, _is_positive(lit)), ())

    # Necessary condition, checked once up front: every pattern literal needs
    # SOME same-predicate-and-polarity candidate, or no assignment can exist.
    if any(not candidates(lit) for lit in pattern_lits):
        return False
    pattern_lits.sort(key=lambda lit: len(candidates(lit)))

    def backtrack(i: int, subst: dict) -> bool:
        if i == len(pattern_lits):
            return True
        lit = pattern_lits[i]
        for target_lit in candidates(lit):
            extended = _match_literal(lit, target_lit, subst)
            if extended is not None and backtrack(i + 1, extended):
                return True
        return False

    return backtrack(0, {})


# ---------------------------------------------------------------------------
# Binary resolution
# ---------------------------------------------------------------------------

def _resolvents(clause1: frozenset, clause2: frozenset) -> list:
    """Return every binary resolvent of two (already standardized-apart) clauses.

    For each positive/negative complementary pair — one literal an ``Atom A`` in
    one clause, the other a ``Not(B)`` in the other clause with ``A``/``B`` the
    same predicate and arity — the atoms are unified. On success with mgu σ the
    resolvent is σ applied to ``(clause1 ∖ L) ∪ (clause2 ∖ M)``, as a frozenset.
    """
    results = []
    # Deterministic literal order (see _rename_clause): resolvent GENERATION
    # order feeds the agenda, so it must not depend on frozenset hash order.
    for lit1 in sorted(clause1, key=_lit_key):
        for lit2 in sorted(clause2, key=_lit_key):
            if _is_positive(lit1) == _is_positive(lit2):
                continue  # need complementary polarity
            atom1 = _atom_of(lit1)
            atom2 = _atom_of(lit2)
            subst = unify(atom1, atom2)
            if subst is None:
                continue
            rest1 = (lit for lit in clause1 if lit != lit1)
            rest2 = (lit for lit in clause2 if lit != lit2)
            resolvent = frozenset(
                [_subst_literal(lit, subst) for lit in rest1]
                + [_subst_literal(lit, subst) for lit in rest2]
            )
            results.append(resolvent)
    return results


# ---------------------------------------------------------------------------
# Factoring
# ---------------------------------------------------------------------------

def _factors(clause: frozenset) -> list:
    """Return every factor of a clause.

    For each pair of same-polarity literals whose atoms unify, the clause is
    instantiated by their mgu σ (merging the two literals) and the σ-image of the
    whole clause is returned as a frozenset. Needed for completeness on inputs
    where two literals must be identified before the empty clause can appear.
    """
    results = []
    literals = sorted(clause, key=_lit_key)
    for i in range(len(literals)):
        for j in range(i + 1, len(literals)):
            lit_i, lit_j = literals[i], literals[j]
            if _is_positive(lit_i) != _is_positive(lit_j):
                continue  # factoring needs equal polarity
            subst = unify(_atom_of(lit_i), _atom_of(lit_j))
            if subst is None:
                continue
            factored = frozenset(_subst_literal(lit, subst) for lit in clause)
            results.append(factored)
    return results


# ---------------------------------------------------------------------------
# Equality: a simple term order, subterm positions, paramodulation,
# reflexivity resolution, and demodulation.
# ---------------------------------------------------------------------------

def _is_equality_atom(atom: Atom) -> bool:
    """Return True iff atom is a binary ``=`` atom (a positive OR negative
    equality literal wraps one of these — this only tests the atom itself,
    call on ``_atom_of(literal)``)."""
    return atom.predicate == "=" and len(atom.args) == 2


def _term_weight(term: Node) -> int:
    """The module's term order, part 1: WEIGHT, defined as term size.

    A leaf (:class:`Variable`, :class:`Constant`, :class:`Number`) has
    weight 1; a :class:`Function` application has weight ``1 +`` the sum of
    its arguments' weights. :class:`Measure` and other non-Function compound
    terms are treated as opaque leaves (weight 1) — this module's equality
    reasoning does not descend into them (see :func:`_subterm_positions`).
    """
    if isinstance(term, Function):
        return 1 + sum(_term_weight(a) for a in term.args)
    return 1


def _term_order_key(term: Node):
    """The module's term order, part 2: ties in weight are broken
    LEXICOGRAPHICALLY by the term's ``to_unicode_str()`` rendering (plain
    Python string comparison). Returns the ``(weight, rendering)`` pair
    compared by :func:`_term_gt`.
    """
    return (_term_weight(term), term.to_unicode_str())


def _term_gt(s: Node, t: Node) -> bool:
    """Return True iff ``s`` is STRICTLY greater than ``t`` under this
    module's term order: compare :func:`_term_order_key` pairs (weight
    first, then the lexicographic tie-break). This order is total up to
    genuine term equality — two DISTINCT terms are, barring a rendering
    collision, always strictly ordered one way or the other, so
    "incomparable" (neither ``_term_gt(s, t)`` nor ``_term_gt(t, s)``) only
    arises when ``s`` and ``t`` are, for the order's purposes, the same term.

    Soundness note (why no substitution-compatibility closure is needed):
    every USE of this order in this module — orienting a paramodulation
    direction, or confirming a demodulation rewrite — compares two already
    fully- or partially-INSTANTIATED terms directly (e.g. ``lσ`` versus
    ``rσ`` for the concrete σ actually used), never an abstract rule "before"
    substitution. A real term-rewriting system needs its order to be stable
    under substitution and monotone under context (the standard KBO/LPO
    closure properties) to prove a whole many-rule system terminates; this
    module sidesteps that requirement by re-checking the concrete inequality
    at each individual rewrite instead of trusting it to persist abstractly.
    A single demodulation step is still guaranteed to terminate the fixpoint
    loop that applies it repeatedly (:func:`_demodulate_to_fixpoint`),
    because replacing a subterm by a strictly lighter one strictly decreases
    the WEIGHT of every ancestor up to the literal's atom (weight is
    additive over immediate children), hence the clause's total weight — a
    bounded-below natural number, so no infinite descending chain exists.
    """
    return _term_order_key(s) > _term_order_key(t)


def _paramodulation_directions(u: Node, v: Node):
    """Return the list of ``(from, to)`` direction pairs licensed for the
    equation ``u ≈ v`` by the term order: paramodulate only from the
    order-GREATER side into the smaller one when :func:`_term_gt` strictly
    decides; if neither side is greater (only ``u`` and ``v`` being the same
    term under the order, see its docstring), try both directions. This is a
    pure SEARCH-SPACE restriction — paramodulation is unconditionally sound
    in either direction regardless of what the order says (see the module
    docstring); dropping a direction here only ever costs completeness, never
    soundness.
    """
    if _term_gt(u, v):
        return [(u, v)]
    if _term_gt(v, u):
        return [(v, u)]
    return [(u, v), (v, u)]


def _subterm_positions(atom: Atom):
    """Yield every position (a non-empty tuple of argument indices) that
    addresses a non-Variable subterm reachable from atom's arguments, in
    pre-order, left to right, descending into :class:`Function` arguments.

    A position addresses a Function application itself (before descending
    into its arguments) as well as every Constant/Number leaf; a Variable
    position is never yielded — paramodulating INTO a bare variable
    occurrence is a standard, deliberate restriction (redundant with
    instantiation, and a large source of unproductive branching for no
    completeness gain worth having in a didactic prover — see the module
    docstring's honesty note). Non-Function compound terms (e.g.
    :class:`Measure`) are treated as opaque leaves — reachable as a position
    themselves, but not descended into — equality reasoning here is scoped
    to the ordinary Function/Atom term language.
    """
    def walk(term, prefix):
        if isinstance(term, Function):
            yield prefix
            for i, arg in enumerate(term.args):
                yield from walk(arg, prefix + (i,))
        elif not isinstance(term, Variable):
            yield prefix
    for i, arg in enumerate(atom.args):
        yield from walk(arg, (i,))


def _term_at(node: Node, position) -> Node:
    """Walk position (a tuple of argument indices, as yielded by
    :func:`_subterm_positions`) from node down to the addressed subterm."""
    for i in position:
        node = node.args[i]
    return node


def _replace_at(node: Node, position, replacement: Node) -> Node:
    """Return a copy of node (an :class:`Atom` or :class:`Function`) with
    the subterm at position replaced by replacement. ``position == ()``
    replaces node itself."""
    if not position:
        return replacement
    i, rest = position[0], position[1:]
    new_args = list(node.args)
    new_args[i] = _replace_at(node.args[i], rest, replacement)
    if isinstance(node, Atom):
        return Atom(node.predicate, new_args)
    return Function(node.name, new_args)


def _paramodulate_target(eq_clause, eq_lit, frm: Node, to: Node, target_clause, tgt_lit):
    """Return every one-step paramodulant of using ``eq_lit`` (``frm ≈ to``,
    one already-chosen direction) from eq_clause to rewrite tgt_lit's atom
    within target_clause, at every unifiable subterm position of tgt_lit.

    Core of :func:`_paramodulants_cross` — kept clause-set-agnostic (it just
    returns ``(new_target_literal, sigma)`` pairs for the caller to
    assemble), which is also what :func:`_demodulate_once`'s cousin logic
    mirrors on the matching side.
    """
    results = []
    tgt_atom = _atom_of(tgt_lit)
    for pos in _subterm_positions(tgt_atom):
        subterm = _term_at(tgt_atom, pos)
        sigma = unify(frm, subterm)
        if sigma is None:
            continue
        new_atom = _replace_at(tgt_atom, pos, to)
        new_lit = new_atom if _is_positive(tgt_lit) else Not(new_atom)
        results.append((new_lit, sigma))
    return results


def _paramodulants_cross(eq_clause: frozenset, target_clause: frozenset) -> list:
    """Return every cross-clause paramodulant using a positive equality
    literal of eq_clause to rewrite a literal of target_clause.

    Mirrors :func:`_resolvents`'s calling convention: both clauses must
    already be standardized apart by the caller (a soundness requirement —
    the two clauses' variables must not be conflated), and ``target_clause``
    may be a differently-renamed copy of the very same logical clause as
    ``eq_clause`` (the caller's given/kept-list loop already relies on this
    for binary resolution's own "resolve a clause against itself" case; the
    same renaming makes cross-clause paramodulation of a clause against
    itself sound too). For each positive equality literal ``s ≈ t`` in
    eq_clause and each direction :func:`_paramodulation_directions` allows,
    every literal of target_clause is tried at every subterm position (see
    :func:`_subterm_positions`); on a successful unification with mgu σ, the
    paramodulant is σ applied to ``(eq_clause ∖ {s≈t}) ∪ (target_clause ∖
    {L}) ∪ {L[p ↦ t]}``.
    """
    results = []
    eq_lits = [l for l in sorted(eq_clause, key=_lit_key)
               if _is_positive(l) and _is_equality_atom(_atom_of(l))]
    if not eq_lits:
        return results
    target_lits = sorted(target_clause, key=_lit_key)
    for eq_lit in eq_lits:
        u, v = _atom_of(eq_lit).args
        for frm, to in _paramodulation_directions(u, v):
            for tgt_lit in target_lits:
                for new_lit, sigma in _paramodulate_target(
                        eq_clause, eq_lit, frm, to, target_clause, tgt_lit):
                    rest_eq = [l for l in eq_clause if l != eq_lit]
                    rest_tgt = [l for l in target_clause if l != tgt_lit]
                    results.append(frozenset(
                        [_subst_literal(l, sigma) for l in rest_eq]
                        + [_subst_literal(l, sigma) for l in rest_tgt]
                        + [_subst_literal(new_lit, sigma)]
                    ))
    return results


def _reflexivity_resolvents(clause: frozenset) -> list:
    """Return every reflexivity resolvent of clause: for each NEGATIVE
    equality literal ``¬(u ≈ v)`` whose two sides unify (mgu σ), the literal
    is dropped and σ applied to the rest — the mechanism that closes goals
    such as ``⊢ c=c`` (whose negation clausifies to ``{¬(c=c)}``, unified by
    the trivial mgu ``{}``) or, more generally, any clause carrying a
    negated equation between two terms that are really the same up to
    instantiation.
    """
    results = []
    for lit in sorted(clause, key=_lit_key):
        if _is_positive(lit):
            continue
        atom = _atom_of(lit)
        if not _is_equality_atom(atom):
            continue
        u, v = atom.args
        sigma = unify(u, v)
        if sigma is None:
            continue
        rest = frozenset(_subst_literal(l, sigma) for l in clause if l != lit)
        results.append(rest)
    return results


# Demodulation fixpoint loop: defensively capped, though termination is
# already guaranteed without it (see _term_gt's soundness note) — same
# spirit as _SUBSUMPTION_PATTERN_CAP below, a belt-and-braces bound on a
# process that is mathematically guaranteed to terminate anyway.
_DEMODULATION_ITERATION_CAP = 100


def _unit_rewrite_rules(clauses) -> list:
    """Return the oriented ``(l, r)`` demodulation rules licensed by the
    UNIT (single-literal) positive equality clauses among clauses.

    A non-unit clause ``{u≈v, Q}`` is never used as a rewrite rule: it only
    asserts ``u≈v ∨ Q``, not the unconditional fact ``u≈v`` — using it to
    rewrite unconditionally would be unsound. An equation whose two sides
    are the same term under :func:`_term_gt` (so neither is strictly
    greater) contributes no rule — rewriting a term to itself is vacuous and
    an unoriented rule cannot be checked for termination.
    """
    rules = []
    for clause in clauses:
        if len(clause) != 1:
            continue
        (lit,) = tuple(clause)
        if not _is_positive(lit):
            continue
        atom = _atom_of(lit)
        if not _is_equality_atom(atom):
            continue
        u, v = atom.args
        if _term_gt(u, v):
            rules.append((u, v))
        elif _term_gt(v, u):
            rules.append((v, u))
    return rules


def _demodulate_once(clause: frozenset, rules: list):
    """Try one demodulation rewrite of clause using rules (oriented ``(l,
    r)`` pairs, as :func:`_unit_rewrite_rules` produces). Returns the
    rewritten clause, or None if no rule applies.

    A rule applies at a literal's subterm (found via :func:`_subterm_positions`)
    when ``l`` one-sidedly MATCHES it (:func:`_match_term` — the rule's own
    variables bind, the target clause's variables are held fixed, unlike
    paramodulation's full unification) AND the concrete orientation
    ``subterm ≻ rσ`` holds under :func:`_term_gt` for the match's σ — checked
    on the instantiated terms, not merely inherited from the rule's abstract
    orientation (see :func:`_term_gt`'s soundness note). Literals and
    positions are visited in a fixed, content-determined order (mirroring
    every other generator in this module) so which of several possible
    rewrites fires is reproducible run to run.
    """
    for lit in sorted(clause, key=_lit_key):
        atom = _atom_of(lit)
        for pos in _subterm_positions(atom):
            subterm = _term_at(atom, pos)
            for l, r in rules:
                sigma = _match_term(l, subterm, {})
                if sigma is None:
                    continue
                r_sigma = apply_subst(r, sigma)
                if not _term_gt(subterm, r_sigma):
                    continue
                new_atom = _replace_at(atom, pos, r_sigma)
                new_lit = new_atom if _is_positive(lit) else Not(new_atom)
                return frozenset([new_lit] + [other for other in clause if other != lit])
    return None


def _demodulate_to_fixpoint(clause: frozenset, rules: list,
                             cap: int = _DEMODULATION_ITERATION_CAP):
    """Repeatedly apply :func:`_demodulate_once` to clause until no rule
    applies (a simplification fixpoint) or cap rewrites have fired. Returns
    ``(simplified_clause, rewrite_count)`` — the caller (:func:`refute`)
    charges rewrite_count against the overall step budget, so demodulation
    is never a free/silent rewrite (see the module docstring).
    """
    count = 0
    while count < cap:
        rewritten = _demodulate_once(clause, rules)
        if rewritten is None:
            break
        clause = rewritten
        count += 1
    return clause, count


# ---------------------------------------------------------------------------
# Saturation
# ---------------------------------------------------------------------------

# A clause acting as a subsumption PATTERN (the candidate subsumer, on either
# side of the check) is only considered when it has at most this many
# literals. Subsumption by a short clause — unit and binary clauses above all
# — is where almost all practical redundancy in a resolution search lives
# (an instantiated fact or rule absorbing padded/weakened copies of itself,
# exactly the shape :func:`refute`'s docstring measurable-case test uses).
# Larger clauses generally originate from problem-specific structure that is
# rarely literally repeated, so extending the search to them buys little
# extra pruning while its worst-case cost (a per-clause O(kept-set) scan) is
# what it costs regardless of pattern size. Honesty note: this makes forward
# and backward subsumption a BOUNDED, not exhaustive, redundancy check — a
# clause subsumed only by a longer pattern may survive. That never affects
# soundness or completeness (see the completeness argument below); it only
# means some redundant clauses are not pruned, exactly like hitting the step
# bound leaves some resolvents unexplored.
_SUBSUMPTION_PATTERN_CAP = 3


def refute(clauses, max_steps: int = 10000) -> bool:
    """Return True iff the clause set is unsatisfiable (empty clause derivable).

    Runs given-clause saturation: resolution between the new clause and every
    previously kept clause, plus factoring of the new clause, PLUS (see the
    module docstring's "Equality" section) reflexivity resolution and
    self-paramodulation of the new clause, and cross-clause paramodulation
    between it and every kept clause in both roles (equation-supplier /
    rewrite-target) — with clause pairs standardized apart before each
    cross-clause step, exactly as for resolution. Every newly generated
    candidate is demodulated to a simplification fixpoint (using the
    currently kept UNIT equations as oriented rewrite rules) before being
    tested for redundancy and possibly kept — each individual demodulation
    rewrite is charged against ``max_steps`` too, just like every other
    inference here. Returns True as soon as the empty clause (``frozenset()``)
    is derived; False if the set saturates with no new clause; and False
    (conservatively, "not refuted within the bound") if ``max_steps``
    inference/demodulation steps are taken first. Soundness rests on the
    empty clause genuinely witnessing unsatisfiability, so True is only ever
    returned when ``frozenset()`` is actually derived — paramodulation,
    reflexivity resolution, and demodulation are all unconditionally sound
    (see the module docstring), so adding them costs nothing on that front;
    completeness for equality problems is explicitly NOT claimed beyond
    what small problems reach within the bound (same module docstring).

    Two redundancy eliminations are applied throughout (tautology deletion and
    subsumption, see :func:`_is_tautology` / :func:`_subsumes`):

    - A tautologous clause (containing a literal and its exact complement) is
      never kept — not even as a seed clause.
    - Forward subsumption: a newly generated clause D is discarded outright if
      some already-kept clause C subsumes it (only attempted when
      ``len(C) <= len(D)``, the necessary case this search targets, AND
      ``len(C) <= _SUBSUMPTION_PATTERN_CAP`` — see that constant's docstring
      for why the subsuming side is deliberately bounded).
    - Backward subsumption: keeping a new clause D retires every already-kept
      clause that D subsumes (same restrictions — D itself must be short
      enough to act as a pattern), including agenda entries not yet
      processed — the agenda-pop loop below checks membership in ``kept``
      and silently skips an entry removed this way.

    Completeness is preserved FOR THE EQUALITY-FREE FRAGMENT: resolution +
    factoring is refutation-complete there (Robinson's theorem — any
    unsatisfiable equality-free clause set has a derivation of the empty
    clause by resolution and factoring alone), and both eliminations only
    ever drop a clause that is redundant given what remains kept — this
    argument is UNCHANGED by adding the equality rules (they only ever add
    more ways to derive a clause, never remove one that resolution/factoring
    alone would have produced). For clause sets that use equality, the
    module docstring's honesty note applies: paramodulation is sound but
    this implementation does not claim the additional completeness
    refinements a serious equality prover needs. A tautology
    is valid in every model, so it can never itself contribute to deriving the
    empty clause (which certifies unsatisfiability) — it can only ever resolve
    away to something already derivable without it. A subsumed clause D is a
    strict logical consequence of the subsuming clause C alone (Cσ ⊆ D means
    every model of C is a model of D), so anything the saturation could
    eventually derive using D remains derivable using C in D's place; dropping
    D (or clauses D itself later subsumes) cannot make an unsatisfiable set
    appear satisfiable to the search. This is the standard redundancy-elimination
    result for resolution (tautology deletion and subsumption are both
    special cases of the general redundancy criterion under which saturation
    remains complete). The bool return, signature, and step-counting semantics
    are unchanged from the plain-saturation version.

    ``clauses`` is any iterable of frozensets of literals; it is not mutated.
    """
    # Insertion-ordered working structures (kept_list mirrors the kept set):
    # processing order must be a function of the INPUT, not of hash seeds, or
    # "proved within max_steps" varies between runs of the same call. Seed
    # tautologies are filtered before dedup/sort so they never enter kept.
    seed = sorted((c for c in dict.fromkeys(clauses) if not _is_tautology(c)),
                  key=lambda c: (len(c), sorted(_lit_key(l) for l in c)))
    if frozenset() in seed:
        return True

    counter = [0]
    kept = set()
    kept_list = []
    # Kept clauses bucketed by literal count: subsumption is only ever
    # attempted between a pattern no longer than its target (len(C) <=
    # len(D)), so indexing by length lets both sweeps below visit only the
    # buckets that could possibly participate, instead of the whole kept set
    # — the necessary optimisation once kept grows into the thousands.
    kept_by_length = {}
    agenda = []
    steps = 0

    def _forward_subsumed(clause) -> bool:
        """True iff some short kept clause (no longer than clause) subsumes it."""
        target_len = len(clause)
        for bucket_len, bucket in kept_by_length.items():
            if bucket_len <= target_len and bucket_len <= _SUBSUMPTION_PATTERN_CAP:
                for c in bucket:
                    if _subsumes(c, clause):
                        return True
        return False

    def _keep(clause):
        # Backward subsumption FIRST: retire every currently kept clause that
        # the new clause subsumes (only those no shorter than the new
        # clause). ``clause`` is not yet indexed, so no self-comparison risk.
        # Skipped entirely when the new clause itself is too long to be a
        # capped subsuming pattern (see _SUBSUMPTION_PATTERN_CAP below).
        pattern_len = len(clause)
        if pattern_len <= _SUBSUMPTION_PATTERN_CAP:
            for bucket_len in list(kept_by_length):
                if bucket_len < pattern_len:
                    continue
                bucket = kept_by_length[bucket_len]
                subsumed = [c for c in bucket if _subsumes(clause, c)]
                for other in subsumed:
                    kept.discard(other)
                    kept_list.remove(other)
                    bucket.remove(other)
                if not bucket:
                    del kept_by_length[bucket_len]
        kept.add(clause)
        kept_list.append(clause)
        kept_by_length.setdefault(pattern_len, []).append(clause)
        agenda.append(clause)

    def _consider(clause) -> bool:
        """Try to add a newly generated clause; True iff it is the empty
        clause (the caller must report refutation immediately)."""
        if clause == frozenset():
            return True
        if not _is_tautology(clause) and clause not in kept and not _forward_subsumed(clause):
            _keep(clause)
        return False

    def _process(candidate) -> bool:
        """Account one freshly generated candidate clause against the step
        budget, demodulate it to a simplification fixpoint under the
        CURRENTLY kept unit equations (forward demodulation only — see the
        module docstring; ``kept_list`` at call time is exactly "currently
        kept"), and try to keep the result. Returns True iff the empty
        clause was reached. The caller must still check ``steps >=
        max_steps`` right after calling this, exactly like every existing
        per-candidate site below — demodulation's own rewrites are charged
        into the same nonlocal ``steps`` counter, so a candidate that takes
        many rewrites to simplify can itself exhaust the budget.
        """
        nonlocal steps
        steps += 1
        rules = _unit_rewrite_rules(kept_list)
        simplified, rewrite_count = _demodulate_to_fixpoint(
            candidate, rules, cap=min(_DEMODULATION_ITERATION_CAP, max(0, max_steps - steps)))
        steps += rewrite_count
        return _consider(simplified)

    for clause in seed:
        # Empty-clause seeds already returned above; ordinary seeds only need
        # forward subsumption (nothing kept yet can be backward-subsumed by a
        # clause not yet added, so _keep's own sweep is what matters here).
        # Seeds are NOT demodulated (see the module docstring) — only clauses
        # generated during saturation pass through _process.
        if clause not in kept and not _forward_subsumed(clause):
            _keep(clause)

    while agenda:
        given = agenda.pop(0)
        if given not in kept:
            continue  # removed by backward subsumption after being queued

        # Factor the given clause against itself.
        for factor in _factors(given):
            if _process(factor):
                return True
            if steps >= max_steps:
                return False

        # Reflexivity-resolve the given clause against itself (shared
        # variables, no renaming — see its docstring). Paramodulation of a
        # clause into itself deliberately has NO shared-variable shortcut
        # (unsound — see the module docstring); it happens below via the
        # renamed-copy cross path only.
        for candidate in _reflexivity_resolvents(given):
            if _process(candidate):
                return True
            if steps >= max_steps:
                return False

        # Resolve/paramodulate the given clause against every kept clause
        # (including itself, via renaming).
        for other in list(kept_list):
            if other not in kept:
                continue  # backward-subsumed by an earlier resolvent this round
            r_given = _rename_clause(given, counter)
            r_other = _rename_clause(other, counter)
            for resolvent in _resolvents(r_given, r_other):
                if _process(resolvent):
                    return True
                if steps >= max_steps:
                    return False
            # Paramodulation is directional (which clause supplies the
            # equation versus the rewrite target), unlike resolution's
            # symmetric literal scan, so both roles are tried explicitly.
            for candidate in _paramodulants_cross(r_given, r_other):
                if _process(candidate):
                    return True
                if steps >= max_steps:
                    return False
            for candidate in _paramodulants_cross(r_other, r_given):
                if _process(candidate):
                    return True
                if steps >= max_steps:
                    return False

    return False  # saturated without deriving the empty clause


# ---------------------------------------------------------------------------
# Entailment and validity
# ---------------------------------------------------------------------------

def _translate_modal_inputs(premises, conclusion: Node):
    """Return ``(lowered, first_order)`` for a modal entailment, or None.

    ``lowered`` is the classical FOL image; ``first_order`` says the quantified
    (qml) route produced it, so :func:`prove` can scale its step budget to the
    larger image. ``None`` means the input was classical all along.

    When any input carries a modal/temporal/hybrid operator, the whole LOCAL
    consequence ``premises ⊢ conclusion`` is folded into one implication sharing
    a single free world variable and lowered with ``standard_translation`` — the
    same local reading :func:`~unicode_fol_kit.atp.modal_tableau.modal_prove`
    decides. The universal closure that :func:`prove` applies afterwards then
    quantifies that ONE world over the implication as a whole, which is exactly
    K-validity of the local consequence. Returns ``None`` for classical input.

    A QUANTIFIED modal input (object quantifiers mixed with modalities) is
    lowered with the first-order shallow embedding instead
    (:func:`unicode_fol_kit.fol.qml.qml_translate` via its validity formula),
    under the same K frame and the ``constant``-domain regime — the FO-modal
    default of ``qml_is_valid``. For other frames or domain regimes
    (varying/increasing/decreasing) call ``qml_is_valid`` directly.

    Counterfactuals are guarded first: ``standard_translation`` predates them and
    its generic error would not name the sphere tools.

    Raises:
        NotImplementedError: from ``standard_translation`` / ``qml`` on the
            genuinely non-first-order residue (Until/Since, hybrid nominals
            under quantifiers), with their documented reasons; or here for
            ``□→``/``◇→`` with a pointer at the sphere semantics.
    """
    from .modal_tableau import has_modal, _contains_counterfactual
    inputs = list(premises) + [conclusion]
    if not any(has_modal(f) for f in inputs):
        return None
    for f in inputs:
        if _contains_counterfactual(f):
            raise NotImplementedError(
                "resolution: the counterfactuals □→/◇→ have no first-order "
                "standard translation (they read a similarity ordering, not an "
                "accessibility relation); use cf_valid / cf_satisfies or "
                "isabelle_decide_counterfactual.")
    combined = conclusion
    for p in reversed(list(premises)):
        combined = Implies(p, combined)
    from ..fol.nodes import Quantifier, SortedQuantifier
    if any(isinstance(n, (Quantifier, SortedQuantifier)) for n in combined.walk()):
        # First-order modal logic: the propositional standard translation cannot
        # express object domains, but the FO shallow embedding can — same K
        # reading, constant domains (qml_is_valid's default).
        from ..fol.qml import _validity_formula
        return (_validity_formula(combined, "constant", "K"), True)
    from ..fol.modal_translation import standard_translation
    return (standard_translation(combined), False)


def prove(premises, conclusion: Node, max_steps: int = 10000) -> bool:
    """Return True iff ``premises`` entail ``conclusion`` (premises ⊨ conclusion).

    Decided by refutation. Each premise is treated as a sentence: free variables
    are read as universally quantified (its universal closure). The conclusion is
    universally closed *and then negated* — crucially in that order, because
    ``¬∀x φ`` is ``∃x ¬φ``: a free variable of the conclusion must skolemise to a
    fresh witness constant/function under the negation, NOT to a universally
    quantified variable. (Closing after negating would misplace the ∀ outside the
    ¬ and unsoundly turn ``∃x ¬φ`` into ``∀x ¬φ``.) Each source formula is
    clausified independently and every clause is renamed apart, so the Skolem and
    variable names from one source cannot collide with another's. The clause sets
    are unioned and saturation is run. Returns True iff the empty clause is
    derived; False if the union saturates without it; and False (conservatively,
    "not proved within the bound") if ``max_steps`` is reached first — never
    reporting a non-theorem as proved.
    """
    premises = list(premises)
    translated = _translate_modal_inputs(premises, conclusion)
    if translated is not None:
        lowered, first_order = translated
        # The FO shallow embedding's image (guard predicates + domain/frame
        # axioms as hypotheses) is an order of magnitude larger than the
        # propositional ST image; scale the step budget so the textbook
        # quantified-modal validities (Barcan / converse Barcan under constant
        # domains, ~200k steps) close under the default budget. False remains
        # "not proved within the bound", as everywhere in this module.
        return prove([], lowered, max_steps=max_steps * (20 if first_order else 1))

    counter = [0]
    sk_counter = [0]
    clause_set = set()
    sources = [_universal_closure(p) for p in premises]
    sources.append(Not(_universal_closure(conclusion)))
    for source in sources:
        for clause in to_clauses(source, sk_counter=sk_counter):
            clause_set.add(_rename_clause(clause, counter))
    return refute(clause_set, max_steps=max_steps)


def is_valid_resolution(formula: Node, max_steps: int = 10000) -> bool:
    """Return True iff ``formula`` is valid (its negation is refutable).

    Equivalent to ``prove([], formula)``: a formula is valid exactly when
    ¬formula is unsatisfiable, which resolution decides by deriving the empty
    clause from the clauses of ¬formula. Incomplete under the bound: a return of
    False means "not shown valid within ``max_steps``", never a false claim of
    invalidity-as-validity.
    """
    return prove([], formula, max_steps=max_steps)
