"""Independent first-order resolution *proof checker* (not a searcher).

Where :mod:`unicode_fol_kit.atp.resolution` *searches* for a refutation (given
clause saturation, unification-driven), this module *certifies* one that was
produced elsewhere: an external searcher — a research engine comparing
calculi, a human, another prover — hands over a :class:`ResolutionDerivation`
(a flat list of clauses each justified as an input clause, a binary resolvent,
or a factor of an earlier clause) and :func:`verify_resolution_proof` decides,
independently, whether every step genuinely follows. This is the same
division of labour as :mod:`unicode_fol_kit.atp.fitch` (``check_proof``) and
:mod:`unicode_fol_kit.atp.sequent` (``check_sequent_proof``): a derivation is
only as trustworthy as its checker, so the checker must never share code with
whatever produced the derivation.

Clauses are represented exactly as :func:`unicode_fol_kit.atp.resolution.to_clauses`
produces them: a clause is a ``frozenset`` of literals, each literal a kit
:class:`~unicode_fol_kit.fol.nodes.Atom` (positive) or
:class:`~unicode_fol_kit.fol.nodes.Not` wrapping one (negative); variables are
implicitly universally quantified over the whole clause. Steps are 1-indexed in
derivation order — ``step.index`` must equal its 1-based position in
``derivation.steps`` — mirroring :mod:`atp.fitch`'s ``1..N`` line-numbering
convention.

Checking semantics (soundness is the only job; the searcher's search *strategy*
— which pair it picked, in what order — is irrelevant and not reconstructed):

- ``"input"`` (0 parents): the step's clause must be a *variant* (see below) of
  one of ``derivation.inputs``.
- ``"resolve"`` (2 parents ``i, j``, both ``< step.index``): the two parent
  clauses are standardized apart (deterministic disjoint renaming — required
  for soundness, since two clauses may share a variable name that names
  logically unrelated individuals), and the step is accepted iff *some* pair
  of complementary-polarity literals has unifiable atoms whose mgu, applied to
  the union of the two remainder clauses, is a variant of the stated clause.
- ``"factor"`` (1 parent ``i``): accepted iff *some* pair of same-polarity
  literals in the parent unifies, and the mgu applied to the whole clause is a
  variant of the stated clause.
- The empty step list is ``ok=True, refuted=False`` (a derivation may verify
  ok without proving anything); ``refuted`` is True iff some *successfully
  verified* step's clause is empty, tracked independently of whether a later
  step fails (so a bogus tail does not retroactively hide a genuine
  refutation reached earlier).

Two deliberate independence requirements (the checker's raison d'être — an
external searcher must be certifiable *without trusting it*, and in particular
without trusting any inference machinery it might also use):

1. **Unification is reimplemented from scratch here** (:func:`_unify` /
   :func:`_apply`, Robinson's algorithm with an occurs-check) instead of
   importing :mod:`unicode_fol_kit.fol.unification`. A searcher built on top of
   the kit's own ``unify`` must not be checked by the very same unification
   code — a bug shared between searcher and checker would be invisible to
   both. This is checker independence in the sense of Sicherheitsanforderungen
   wie FA-5.2 des Zielprojekts: der Prüfer teilt keinen Code mit dem Sucher
   ("the checker shares no code with the searcher"). ``tests/test_resolution_check.py``
   holds a differential battery: on unifiable/non-unifiable atom pairs
   (occurs-check both directions, function nesting, repeated variables),
   :func:`_unify` and :func:`unicode_fol_kit.fol.unification.unify` must agree
   on unifiability, and where both succeed each substitution must equalize its
   own two atoms.
2. **Variant (alpha-equivalence) checking is exact, not an approximation.**
   Two clauses are *variants* iff there is a bijection between their literals
   together with a bijection on variable names under which corresponding
   literals become syntactically identical — this is implemented as an
   explicit backtracking search over literal correspondences
   (:func:`_is_variant`), not a canonical/sorted-form shortcut (which would be
   wrong: e.g. sorting literals by a variable-name-sensitive key does not
   commute with the variable renaming a real variant requires). This matters
   because both ``"input"`` and the resolvent/factor of ``"resolve"``/``"factor"``
   are checked *up to variant*, not up to literal `==`: a searcher's exact
   choice of variable spelling must never cause a genuinely correct step to be
   rejected, while a real structural mismatch (different arity, a constant
   where a variable was needed, an unmatched literal) must still be caught.

Public API: :class:`ResolutionStep`, :class:`ResolutionDerivation`,
:class:`ResolutionCheckResult`, the checkers :func:`verify_resolution_proof` /
:func:`check_resolution_proof`, and :func:`render_resolution_proof`.
"""

from dataclasses import dataclass
from typing import Dict, FrozenSet, Optional, Tuple

from ..fol.nodes import Node, Atom, Not, Variable, Constant, Number, Function


# ---------------------------------------------------------------------------
# Derivation objects
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class ResolutionStep:
    """One line of a resolution derivation: a clause and how it was obtained.

    ``rule`` is one of ``"input"`` (0 parents — the clause must be a variant
    of one of the derivation's inputs), ``"resolve"`` (2 parents — a binary
    resolvent of the two cited earlier clauses), or ``"factor"`` (1 parent — a
    factor of the one cited earlier clause). ``parents`` holds the 1-based
    ``index`` values of the cited earlier steps, in citation order (so for
    ``"resolve"`` the pair is *not* order-sensitive — both orderings of the
    complementary literal are tried by the checker). ``clause`` is coerced to
    a ``frozenset`` and ``parents`` to a ``tuple`` so the step stays hashable.
    """

    index: int
    clause: FrozenSet[Node]
    rule: str
    parents: Tuple[int, ...] = ()

    def __post_init__(self):
        """Coerce ``clause``/``parents`` to a frozenset/tuple for hashability."""
        object.__setattr__(self, "clause", frozenset(self.clause))
        object.__setattr__(self, "parents", tuple(self.parents))


@dataclass(frozen=True)
class ResolutionDerivation:
    """A full resolution derivation: the original clauses plus a proof of steps.

    ``inputs`` is the set of clauses the ``"input"`` steps are licensed to
    restate (up to variant) — typically the clausal form of the premises and
    the negated conclusion, as :func:`unicode_fol_kit.atp.resolution.to_clauses`
    would produce them, though the checker does not require or re-derive that
    provenance; it only checks that every ``"input"`` step matches one of
    them. ``steps`` is the ordered derivation body (see :class:`ResolutionStep`).
    """

    inputs: Tuple[FrozenSet[Node], ...] = ()
    steps: Tuple[ResolutionStep, ...] = ()

    def __post_init__(self):
        """Coerce ``inputs`` to a tuple of frozensets and ``steps`` to a tuple."""
        object.__setattr__(self, "inputs", tuple(frozenset(c) for c in self.inputs))
        object.__setattr__(self, "steps", tuple(self.steps))


@dataclass(frozen=True)
class ResolutionCheckResult:
    """The outcome of checking a derivation.

    ``ok`` is True iff every step up to (and including) the point of failure —
    i.e. every step, if there was no failure — is licensed by its rule.
    ``error_index``/``error`` name the first offending step (``error`` in the
    style ``"step N: reason"``) or are ``None`` on success. ``refuted`` is True
    iff some *successfully verified* step derives the empty clause — computed
    independently of ``ok``, so a refutation reached before a later malformed
    step is still reported.
    """

    ok: bool
    error_index: Optional[int]
    error: Optional[str]
    refuted: bool

    def __bool__(self) -> bool:
        """A ResolutionCheckResult is truthy iff the derivation checked out."""
        return self.ok


# ---------------------------------------------------------------------------
# Independent unification (Robinson's algorithm, occurs-check) — see module
# docstring, independence requirement 1: this must NOT import or call
# unicode_fol_kit.fol.unification.unify. A substitution is a plain dict
# mapping a variable NAME (str) to a term Node, exactly as in that module,
# but every function below is a from-scratch reimplementation.
# ---------------------------------------------------------------------------

def _apply(node: Node, subst: Dict[str, Node]) -> Node:
    """Apply ``subst`` to ``node``, following chained bindings, without mutation."""
    if isinstance(node, Variable):
        if node.name in subst:
            return _apply(subst[node.name], subst)
        return node
    if isinstance(node, (Constant, Number)):
        return node
    if isinstance(node, Function):
        return Function(node.name, [_apply(a, subst) for a in node.args])
    if isinstance(node, Atom):
        return Atom(node.predicate, [_apply(a, subst) for a in node.args])
    raise TypeError(f"_apply: unsupported node type {type(node).__name__}")


def _apply_literal(literal: Node, subst: Dict[str, Node]) -> Node:
    """Apply ``subst`` to a literal (``Atom`` or ``Not(Atom)``), preserving polarity."""
    if isinstance(literal, Not):
        return Not(_apply(literal.formula, subst))
    return _apply(literal, subst)


def _occurs(name: str, term: Node, subst: Dict[str, Node]) -> bool:
    """Return True iff variable ``name`` occurs in ``term`` after applying ``subst``.

    The occurs-check: rejects a binding such as ``x ↦ f(x)`` that would build
    an infinite (cyclic) term.
    """
    term = _apply(term, subst)
    if isinstance(term, Variable):
        return term.name == name
    if isinstance(term, Function):
        return any(_occurs(name, a, subst) for a in term.args)
    return False


def _bind(name: str, term: Node, subst: Dict[str, Node]) -> Optional[Dict[str, Node]]:
    """Extend ``subst`` with ``name ↦ term`` (occurs-checked); returns a new dict or None.

    Binding a variable to itself is a no-op that returns ``subst`` unchanged.
    """
    if isinstance(term, Variable) and term.name == name:
        return subst
    if _occurs(name, term, subst):
        return None
    new_subst = dict(subst)
    new_subst[name] = _apply(term, subst)
    return new_subst


def _leaf_value(node: Node):
    """Return the comparable payload of a leaf node (Constant name / Number value)."""
    if isinstance(node, Constant):
        return node.name
    if isinstance(node, Number):
        return node.value
    return None


def _unify_args(args1, args2, subst: Dict[str, Node]) -> Optional[Dict[str, Node]]:
    """Unify two equal-length argument lists left-to-right, threading ``subst``."""
    for a, b in zip(args1, args2):
        subst = _unify(a, b, subst)
        if subst is None:
            return None
    return subst


def _unify(t1: Node, t2: Node, subst: Optional[Dict[str, Node]] = None) -> Optional[Dict[str, Node]]:
    """Most general unifier of ``t1`` and ``t2``, or None (Robinson, occurs-checked).

    Independent reimplementation of :func:`unicode_fol_kit.fol.unification.unify`
    (see module docstring, independence requirement 1) — same term language
    (``Variable``/``Constant``/``Number``/``Function``, plus ``Atom`` for the
    literal case) and the same algorithm, but sharing no code with it.
    """
    if subst is None:
        subst = {}

    t1 = _apply(t1, subst)
    t2 = _apply(t2, subst)

    if isinstance(t1, Variable):
        return _bind(t1.name, t2, subst)
    if isinstance(t2, Variable):
        return _bind(t2.name, t1, subst)

    if isinstance(t1, (Constant, Number)) or isinstance(t2, (Constant, Number)):
        if type(t1) is type(t2) and _leaf_value(t1) == _leaf_value(t2):
            return subst
        return None

    if isinstance(t1, Function) and isinstance(t2, Function):
        if t1.name != t2.name or len(t1.args) != len(t2.args):
            return None
        return _unify_args(t1.args, t2.args, subst)

    if isinstance(t1, Atom) and isinstance(t2, Atom):
        if t1.predicate != t2.predicate or len(t1.args) != len(t2.args):
            return None
        return _unify_args(t1.args, t2.args, subst)

    return None


# ---------------------------------------------------------------------------
# Exact variant (alpha-equivalence) checking — see module docstring,
# independence requirement 2: a backtracking search for a literal
# correspondence plus a variable-name BIJECTION, not a canonical-form
# shortcut.
# ---------------------------------------------------------------------------

def _term_alpha_match(t1: Node, t2: Node, fwd: Dict[str, str], bwd: Dict[str, str]):
    """Try to extend the variable bijection ``(fwd, bwd)`` matching ``t1`` (A-side)
    onto ``t2`` (B-side); returns the extended ``(fwd, bwd)`` pair or None.

    ``fwd``/``bwd`` map A-variable-name -> B-variable-name and back; neither
    input dict is mutated (a matched extension is a fresh copy), so a failed
    branch never corrupts an earlier partial match a backtracking caller may
    still want to try again on a different literal.
    """
    if isinstance(t1, Variable) and isinstance(t2, Variable):
        mapped = fwd.get(t1.name)
        if mapped is not None:
            return (fwd, bwd) if mapped == t2.name else None
        if t2.name in bwd:
            return None  # t2 already claimed by a different A-variable: not injective
        new_fwd = dict(fwd)
        new_fwd[t1.name] = t2.name
        new_bwd = dict(bwd)
        new_bwd[t2.name] = t1.name
        return new_fwd, new_bwd
    if isinstance(t1, Variable) or isinstance(t2, Variable):
        return None  # a variable can only match a variable — constants are not variables
    if isinstance(t1, Constant) and isinstance(t2, Constant):
        return (fwd, bwd) if t1.name == t2.name else None
    if isinstance(t1, Number) and isinstance(t2, Number):
        return (fwd, bwd) if t1.value == t2.value else None
    if isinstance(t1, Function) and isinstance(t2, Function):
        if t1.name != t2.name or len(t1.args) != len(t2.args):
            return None
        for a1, a2 in zip(t1.args, t2.args):
            res = _term_alpha_match(a1, a2, fwd, bwd)
            if res is None:
                return None
            fwd, bwd = res
        return fwd, bwd
    return None  # mismatched node kinds (e.g. Constant vs Number)


def _lit_alpha_match(l1: Node, l2: Node, fwd: Dict[str, str], bwd: Dict[str, str]):
    """As :func:`_term_alpha_match`, but for a whole literal (``Atom``/``Not(Atom)``).

    Polarity must match, and the underlying atoms' predicate and arity must
    match, before any variable matching is attempted.
    """
    neg1, neg2 = isinstance(l1, Not), isinstance(l2, Not)
    if neg1 != neg2:
        return None
    a1 = l1.formula if neg1 else l1
    a2 = l2.formula if neg2 else l2
    if not (isinstance(a1, Atom) and isinstance(a2, Atom)):
        return None
    if a1.predicate != a2.predicate or len(a1.args) != len(a2.args):
        return None
    for x, y in zip(a1.args, a2.args):
        res = _term_alpha_match(x, y, fwd, bwd)
        if res is None:
            return None
        fwd, bwd = res
    return fwd, bwd


def _is_variant(a: FrozenSet[Node], b: FrozenSet[Node]) -> bool:
    """Return True iff clause ``a`` is a variant (alpha-equivalent copy) of clause ``b``.

    Backtracking search for a bijection between the literals of ``a`` and
    ``b`` together with a bijection on variable names under which every
    matched literal pair becomes syntactically identical. Deliberately exact
    (not a sorted/canonical-form shortcut — see the module docstring): e.g.
    ``{P(x,y), P(y,x)}`` IS a variant of ``{P(u,v), P(v,u)}`` (a 2-cycle
    literal correspondence with a 2-variable bijection), ``{P(x,x)}`` is NOT a
    variant of ``{P(x,y)}`` (no single variable can equal two distinct ones),
    and ``{P(x)}`` is NOT a variant of ``{P(a)}`` (a constant is never matched
    by a variable). Worst case is factorial in clause size, which is fine for
    the small clauses resolution steps actually produce.
    """
    la, lb = list(a), list(b)
    if len(la) != len(lb):
        return False
    used = [False] * len(lb)

    def backtrack(i: int, fwd: Dict[str, str], bwd: Dict[str, str]) -> bool:
        if i == len(la):
            return True
        for j in range(len(lb)):
            if used[j]:
                continue
            res = _lit_alpha_match(la[i], lb[j], fwd, bwd)
            if res is None:
                continue
            used[j] = True
            if backtrack(i + 1, res[0], res[1]):
                return True
            used[j] = False
        return False

    return backtrack(0, {}, {})


# ---------------------------------------------------------------------------
# Standardizing apart (deterministic disjoint renaming of two clauses)
# ---------------------------------------------------------------------------

def _clause_var_names(clause: FrozenSet[Node]) -> set:
    """Return the set of variable names occurring anywhere in ``clause``."""
    names = set()
    for literal in clause:
        for n in literal.walk():
            if isinstance(n, Variable):
                names.add(n.name)
    return names


def _rename_term(node: Node, mapping: Dict[str, Variable]) -> Node:
    """Return ``node`` with each Variable renamed via the one-level ``mapping``."""
    if isinstance(node, Variable):
        return mapping.get(node.name, node)
    if isinstance(node, (Constant, Number)):
        return node
    if isinstance(node, Function):
        return Function(node.name, [_rename_term(a, mapping) for a in node.args])
    if isinstance(node, Atom):
        return Atom(node.predicate, [_rename_term(a, mapping) for a in node.args])
    raise TypeError(f"_rename_term: unsupported node type {type(node).__name__}")


def _rename_literal(literal: Node, mapping: Dict[str, Variable]) -> Node:
    """Return ``literal`` with each Variable renamed via the one-level ``mapping``."""
    if isinstance(literal, Not):
        return Not(_rename_term(literal.formula, mapping))
    return _rename_term(literal, mapping)


def _standardize_apart(ca: FrozenSet[Node], cb: FrozenSet[Node]):
    """Rename the variables of ``ca`` and ``cb`` to disjoint fresh names.

    A soundness requirement before resolving two clauses: each clause's
    variables are implicitly universally quantified *over that clause alone*,
    so a name they happen to share (e.g. both using ``x``) names logically
    unrelated individuals and must not be conflated. Renaming is deterministic
    (sorted by original name, prefixed ``_L``/``_R``) so the check is
    reproducible; the *choice* of fresh names is otherwise immaterial since
    every candidate resolvent is compared up to variant, not up to `==`.
    """
    names_a = sorted(_clause_var_names(ca))
    names_b = sorted(_clause_var_names(cb))
    map_a = {name: Variable(f"_L{i}") for i, name in enumerate(names_a)}
    map_b = {name: Variable(f"_R{i}") for i, name in enumerate(names_b)}
    new_a = frozenset(_rename_literal(lit, map_a) for lit in ca)
    new_b = frozenset(_rename_literal(lit, map_b) for lit in cb)
    return new_a, new_b


# ---------------------------------------------------------------------------
# Literal polarity
# ---------------------------------------------------------------------------

def _lit_atom_polarity(literal: Node) -> Optional[Tuple[Atom, bool]]:
    """Return ``(atom, is_positive)`` for a well-formed literal, or None.

    A well-formed literal is a bare ``Atom`` (positive) or a ``Not`` wrapping
    exactly one (negative); anything else (e.g. a doubly-negated or non-atomic
    literal) is not a legal clause literal and is returned as None so callers
    can skip it rather than crash — a malformed clause simply matches nothing.
    """
    if isinstance(literal, Not) and isinstance(literal.formula, Atom):
        return literal.formula, False
    if isinstance(literal, Atom):
        return literal, True
    return None


def _lit_key(literal: Node) -> str:
    """Canonical sort key for a literal (its surface form): search order over a
    clause's literals must be a function of CONTENT, not of frozenset iteration
    order (hash-randomised across processes), so the checker's behaviour and
    :func:`render_resolution_proof`'s output are reproducible run to run."""
    return literal.to_unicode_str()


# ---------------------------------------------------------------------------
# Per-rule step checkers: each returns None (licensed) or an error string
# (WITHOUT the "step N: " prefix, added by the caller).
# ---------------------------------------------------------------------------

def _check_input_step(step: ResolutionStep, inputs: Tuple[FrozenSet[Node], ...]) -> Optional[str]:
    """``"input"``: the clause must be a variant of one of ``inputs``."""
    for inp in inputs:
        if _is_variant(step.clause, inp):
            return None
    return "'input' clause is not a variant (alpha-equivalent copy) of any derivation input"


def _check_resolve_step(step: ResolutionStep, ci: FrozenSet[Node], cj: FrozenSet[Node]) -> Optional[str]:
    """``"resolve"``: some complementary-polarity literal pair's mgu must give the clause."""
    ci2, cj2 = _standardize_apart(ci, cj)
    found_complementary_pair = False
    for lit1 in sorted(ci2, key=_lit_key):
        parsed1 = _lit_atom_polarity(lit1)
        if parsed1 is None:
            continue
        atom1, pos1 = parsed1
        for lit2 in sorted(cj2, key=_lit_key):
            parsed2 = _lit_atom_polarity(lit2)
            if parsed2 is None:
                continue
            atom2, pos2 = parsed2
            if pos1 == pos2:
                continue
            found_complementary_pair = True
            sigma = _unify(atom1, atom2)
            if sigma is None:
                continue
            resolvent = frozenset(
                [_apply_literal(l, sigma) for l in ci2 if l != lit1]
                + [_apply_literal(l, sigma) for l in cj2 if l != lit2]
            )
            if _is_variant(resolvent, step.clause):
                return None
    if not found_complementary_pair:
        return "'resolve': the parent clauses contain no complementary-polarity literal pair"
    return ("'resolve': no complementary-polarity literal pair's mgu produces "
            "the stated resolvent clause")


def _check_factor_step(step: ResolutionStep, ci: FrozenSet[Node]) -> Optional[str]:
    """``"factor"``: some same-polarity literal pair's mgu must give the clause."""
    literals = sorted(ci, key=_lit_key)
    for a in range(len(literals)):
        parsed_a = _lit_atom_polarity(literals[a])
        if parsed_a is None:
            continue
        atom_a, pos_a = parsed_a
        for b in range(a + 1, len(literals)):
            parsed_b = _lit_atom_polarity(literals[b])
            if parsed_b is None:
                continue
            atom_b, pos_b = parsed_b
            if pos_a != pos_b:
                continue
            sigma = _unify(atom_a, atom_b)
            if sigma is None:
                continue
            factored = frozenset(_apply_literal(l, sigma) for l in ci)
            if _is_variant(factored, step.clause):
                return None
    return ("'factor': no same-polarity literal pair's mgu produces the "
            "stated factored clause")


_RULE_ARITY = {"input": 0, "resolve": 2, "factor": 1}


# ---------------------------------------------------------------------------
# The checker
# ---------------------------------------------------------------------------

def verify_resolution_proof(derivation: "ResolutionDerivation") -> ResolutionCheckResult:
    """Check ``derivation`` and return a :class:`ResolutionCheckResult`.

    Walks ``derivation.steps`` in order, verifying each step's structural
    shape (index == position, parents strictly earlier, parent count matches
    the rule) and then its rule-specific licensing (see the module docstring).
    Stops at the first failure and reports it as ``"step N: reason"``.
    ``refuted`` tracks, independently of ``ok``, whether some step verified
    *before* any failure derives the empty clause.
    """
    clause_by_index: Dict[int, FrozenSet[Node]] = {}
    refuted = False

    for pos, step in enumerate(derivation.steps):
        expected_index = pos + 1
        if not isinstance(step, ResolutionStep):
            return ResolutionCheckResult(
                False, None,
                f"step {expected_index}: expected a ResolutionStep, got "
                f"{type(step).__name__}",
                refuted)
        if step.index != expected_index:
            return ResolutionCheckResult(
                False, step.index,
                f"step {step.index}: index must equal its position in the "
                f"derivation (expected {expected_index})",
                refuted)

        arity = _RULE_ARITY.get(step.rule)
        if arity is None:
            return ResolutionCheckResult(
                False, step.index,
                f"step {step.index}: unknown rule {step.rule!r} (expected "
                f"'input', 'resolve', or 'factor')",
                refuted)
        if len(step.parents) != arity:
            return ResolutionCheckResult(
                False, step.index,
                f"step {step.index}: rule {step.rule!r} takes {arity} "
                f"parent(s), got {len(step.parents)}",
                refuted)

        for p in step.parents:
            if p not in clause_by_index or p >= step.index:
                return ResolutionCheckResult(
                    False, step.index,
                    f"step {step.index}: parent {p} does not refer to a "
                    f"strictly earlier verified step (parents must cite "
                    f"smaller indices)",
                    refuted)

        if step.rule == "input":
            err = _check_input_step(step, derivation.inputs)
        elif step.rule == "resolve":
            i, j = step.parents
            err = _check_resolve_step(step, clause_by_index[i], clause_by_index[j])
        else:  # "factor"
            (i,) = step.parents
            err = _check_factor_step(step, clause_by_index[i])

        if err is not None:
            return ResolutionCheckResult(False, step.index, f"step {step.index}: {err}", refuted)

        clause_by_index[step.index] = step.clause
        if not step.clause:
            refuted = True

    return ResolutionCheckResult(True, None, None, refuted)


def check_resolution_proof(derivation: "ResolutionDerivation") -> bool:
    """Return True iff ``derivation`` is a valid resolution derivation (sound).

    A thin bool wrapper over :func:`verify_resolution_proof`; use that for the
    failing step index and reason, or to read ``refuted``.
    """
    return verify_resolution_proof(derivation).ok


# ---------------------------------------------------------------------------
# Rendering
# ---------------------------------------------------------------------------

def _render_clause(clause: FrozenSet[Node]) -> str:
    """Render a clause as its literals joined by ``∨``, or ``□`` if empty.

    Literals are sorted by their Unicode rendering for a deterministic,
    frozenset-iteration-order-independent string.
    """
    if not clause:
        return "□"
    return " ∨ ".join(lit.to_unicode_str() for lit in sorted(clause, key=_lit_key))


def render_resolution_proof(derivation: "ResolutionDerivation") -> str:
    """Render ``derivation`` as numbered lines: ``"N. <clause> [rule parents]"``.

    The empty clause renders as ``□``. Parent indices are comma-joined in
    citation order; a rule with no parents (``"input"``) renders with no
    trailing citation list, e.g. ``"1. P(a) [input]"``.
    """
    lines = []
    for step in derivation.steps:
        bracket = step.rule
        if step.parents:
            bracket += " " + ",".join(str(p) for p in step.parents)
        lines.append(f"{step.index}. {_render_clause(step.clause)} [{bracket}]")
    return "\n".join(lines)
