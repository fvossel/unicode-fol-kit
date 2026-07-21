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

5. Saturation (:func:`refute`). Resolution and factoring are iterated until the
   empty clause ``frozenset()`` appears (⇒ unsatisfiable / refuted) or no new
   clause is produced (⇒ saturated) or a step bound is reached (⇒ undecided,
   reported conservatively as not refuted).

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
# Saturation
# ---------------------------------------------------------------------------

def refute(clauses, max_steps: int = 10000) -> bool:
    """Return True iff the clause set is unsatisfiable (empty clause derivable).

    Runs given-clause saturation: resolution between the new clause and every
    previously kept clause, plus factoring of the new clause, with both operands
    standardized apart before each resolution step. Returns True as soon as the
    empty clause (``frozenset()``) is derived; False if the set saturates with no
    new clause; and False (conservatively, "not refuted within the bound") if
    ``max_steps`` resolution/factoring steps are taken first. Soundness rests on
    the empty clause genuinely witnessing unsatisfiability, so True is only ever
    returned when ``frozenset()`` is actually derived.

    ``clauses`` is any iterable of frozensets of literals; it is not mutated.
    """
    # Insertion-ordered working structures (kept_list mirrors the kept set):
    # processing order must be a function of the INPUT, not of hash seeds, or
    # "proved within max_steps" varies between runs of the same call.
    seed = sorted(dict.fromkeys(clauses),
                  key=lambda c: (len(c), sorted(_lit_key(l) for l in c)))
    kept = set(seed)
    if frozenset() in kept:
        return True

    counter = [0]
    kept_list = list(seed)
    agenda = list(seed)
    steps = 0

    def _keep(clause):
        kept.add(clause)
        kept_list.append(clause)
        agenda.append(clause)

    while agenda:
        given = agenda.pop(0)
        # Factor the given clause against itself.
        for factor in _factors(given):
            steps += 1
            if factor == frozenset():
                return True
            if factor not in kept:
                _keep(factor)
            if steps >= max_steps:
                return False

        # Resolve the given clause against every kept clause (including itself).
        for other in list(kept_list):
            r_given = _rename_clause(given, counter)
            r_other = _rename_clause(other, counter)
            for resolvent in _resolvents(r_given, r_other):
                steps += 1
                if resolvent == frozenset():
                    return True
                if resolvent not in kept:
                    _keep(resolvent)
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
