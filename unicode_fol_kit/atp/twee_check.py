"""Independent verification of a parsed Twee proof (not a searcher — a checker).

Where :mod:`atp.twee_entailment` drives Twee and PARSES its stdout into a
:class:`~atp.twee_entailment.TweeProof`, this module re-derives, from
scratch, whether that proof actually holds — the same division of labour as
:mod:`atp.resolution_check` for resolution refutations and
:mod:`atp.fitch`/:mod:`atp.sequent` for their calculi: a proof produced by an
external tool is only as trustworthy as an INDEPENDENT re-check of it, so
Twee itself is trusted only for search, never for soundness.

Two things are checked, independently of each other:

1. :func:`check_twee_proof` — every rewrite step in every lemma's and the
   goal's proof chain is a genuine single-rewrite instance of the axiom or
   lemma it cites (in the stated direction), lemmas are only cited after they
   are themselves proved, and — the actual trust boundary, since Twee could
   in principle print a fabricated "Axiom N (name): ..." line — every axiom
   the proof restates is cross-checked, up to alpha-equivalence, against the
   ORIGINAL premise (or premise conjunct) the caller actually gave Twee.
2. :func:`goal_matches_conclusion` — the proof's Goal equation is actually a
   restatement of the conclusion the caller asked Twee to prove (guards
   against a proof that is internally perfect but answers a different
   question — see :mod:`atp.twee_entailment`'s module docstring for the
   ``tuple(...)`` encoding a conjunctive conclusion gets rewritten into,
   which this function has to reverse to compare against the original).
   The two readings it relies on hold only for names of Twee's own: a universally
   quantified variable stands for a constant that occurs in no axiom of the proof and
   nowhere in the conclusion, and the symbol that encodes a conjunction is one that
   occurs in neither (:func:`goal_mismatch` says which name made it refuse).

Independence, concretely: rewrite-step verification is implemented here from
scratch (:func:`_match`, one-directional structural matching — NOT
:mod:`fol.unification`'s ``unify``, which is bidirectional and would let a
term-side variable bind, which is unsound here — a Twee proof term's own
variables, whatever their surface form, are always ground/opaque data to be
matched literally, never something to unify against; see the module
docstring of :mod:`atp.twee_entailment` for why axiom-side variables are
canonically renamed and goal-side variables are Skolem constants). Only
SUBSTITUTION application reuses :func:`unicode_fol_kit.fol.unification
.apply_subst` — a generic, direction-agnostic tree rewrite with no bearing on
matching soundness, explicitly fine to share.
"""

from dataclasses import dataclass
from typing import Dict, FrozenSet, List, Optional, Sequence, Set, Tuple

from ..fol.nodes import (
    And, Atom, Constant, Function, Node, Number, Quantifier, SortedConstant, Variable,
)
from ..fol.unification import apply_subst
from .twee_entailment import TweeChain, TweeCitation, TweeProof

__all__ = ["TweeCheckResult", "check_twee_proof", "goal_matches_conclusion", "goal_mismatch"]


@dataclass(frozen=True)
class TweeCheckResult:
    """The outcome of :func:`check_twee_proof`.

    ``ok`` is True iff every axiom restatement and every rewrite step checks
    out; ``error`` names the first failure (``None`` on success).
    """

    ok: bool
    error: Optional[str] = None

    def __bool__(self) -> bool:
        return self.ok


# ---------------------------------------------------------------------------
# Flattening a premise/conclusion into its top-level equational conjuncts —
# used BOTH to build the axiom-provenance name map (see module docstring of
# atp.twee_entailment for the premise_<i>/premise_<i>_<k> naming Twee's own
# clausifier produces) and to decompose a (possibly tupled) goal for
# goal_matches_conclusion.
# ---------------------------------------------------------------------------

def _erase_sorts(term: Node) -> Node:
    """``term`` with every sorted constant ``c:S`` read as the constant ``c``.

    Twee decides unit equality and prints plain constants. A sorted constant is the
    constant of its name (the kit's one-universe reading: ``c:S`` and ``c`` are one
    symbol), and what its sort adds, that ``c`` is a member of ``S``, is a premise of
    the problem, never part of an equation: a derivation of an equation from equations
    is a derivation whatever else is assumed. So the equations are compared with the
    sorts read off. A function of no arguments is the constant of its name (the problem
    writer writes it so, and Twee prints it so), and is read as one."""
    if isinstance(term, SortedConstant):
        return Constant(term.name)
    if isinstance(term, Function):
        if not term.args:
            return Constant(term.name)
        return Function(term.name, tuple(_erase_sorts(a) for a in term.args))
    return term


def _variable_names(term: Node, into: Set[str]) -> None:
    """Add the name of every ``Variable`` occurring in ``term`` to ``into``."""
    if isinstance(term, Variable):
        into.add(term.name)
    elif isinstance(term, Function):
        for arg in term.args:
            _variable_names(arg, into)


def _symbol_names(term: Node, into: Set[str]) -> None:
    """Add the name of every constant and every function symbol occurring in ``term`` to
    ``into``: ONE namespace, as in a TPTP problem, where a functor ``x`` and a constant ``x``
    are not told apart by Twee (it renames its own symbol when either is taken)."""
    if isinstance(term, (Constant, SortedConstant)):
        into.add(term.name)
    elif isinstance(term, Function):
        into.add(term.name)
        for arg in term.args:
            _symbol_names(arg, into)


def _flatten_scoped(node: Node, bound: FrozenSet[str] = frozenset()
                    ) -> List[Tuple[Node, Node, FrozenSet[str]]]:
    """Flatten like :func:`_flatten_equations`, and say which variables each equation
    leaves FREE: ``[(lhs, rhs, free), ...]`` where ``free`` holds the name of every
    variable of the equation that no quantifier above it binds."""
    if isinstance(node, Quantifier):
        if node.type not in ("forall", "∀"):
            raise ValueError(f"twee_check: non-universal quantifier {node.type!r} in premise/conclusion")
        return _flatten_scoped(node.formula, bound | {node.variable.name})
    if isinstance(node, And):
        return _flatten_scoped(node.left, bound) + _flatten_scoped(node.right, bound)
    if isinstance(node, Atom) and node.predicate == "=" and len(node.args) == 2:
        lhs, rhs = _erase_sorts(node.args[0]), _erase_sorts(node.args[1])
        occurring: Set[str] = set()
        _variable_names(lhs, occurring)
        _variable_names(rhs, occurring)
        return [(lhs, rhs, frozenset(occurring - bound))]
    raise ValueError(f"twee_check: not an equation or conjunction of equations: "
                     f"{node.to_unicode_str()!r}")


def _flatten_equations(node: Node) -> List[Tuple[Node, Node]]:
    """Flatten a (forall-closed) equation-or-conjunction into ``[(lhs, rhs), ...]``.

    Left-to-right in source order (``And`` is binary and this recurses
    left-then-right). That is the order of the SOURCE and nothing relies on it
    for naming: Twee numbers the clauses of a conjunctive premise in an order of
    its own (see :func:`_expected_axiom_equations`). Quantifiers are stripped
    (matching is variable-name-blind — see module docstring), so the returned
    pairs are plain term ``Node`` objects, still possibly containing the original bound
    variables. A sorted constant is read as the plain constant of its name
    (:func:`_erase_sorts`).
    """
    return [(lhs, rhs) for lhs, rhs, _ in _flatten_scoped(node)]


def _expected_axiom_equations(axioms: Sequence[Node]) -> Dict[str, List[Tuple[Node, Node]]]:
    """Map every axiom name Twee can give a clause of the premises to the equations it may be.

    Twee names the clauses of premise ``i`` (1-based) ``premise_<i>``, ``premise_<i>_1``, ...
    ``premise_<i>_<n - 1>`` for a premise of ``n`` conjuncts, and which clause carries which
    suffix is Twee's own business, not the order of the source: its clausifier numbers the
    clauses in an order of its own and drops a ground conjunct that repeats an earlier one
    (measured, Twee 2.6.1: for ``aa = bb ∧ ∀x ff(x) = x`` the clause ``ff(X) = X`` is
    ``premise_1`` and ``aa = bb`` is ``premise_1_1``; for ``∀x ∀y (hh(x, y) = hh(y, x) ∧
    ff(x) = x)`` the clause ``ff(X) = X`` is ``premise_1``; for ``aa = bb ∧ aa = bb ∧ cc = dd``
    the clause ``cc = dd`` is ``premise_1_1``). So a name determines the
    PREMISE and nothing else: the value of ``premise_<i>`` and of every ``premise_<i>_<k>`` is
    the list of all the conjuncts of premise ``i``, and a restated axiom is checked against
    what it SAYS (:func:`check_twee_proof`: it must be one of them, up to the renaming of its
    variables), never against its position. A name of another premise, or a suffix beyond
    the last conjunct, is not a key.

    A premise whose equation has a free variable is refused (``ValueError``): a free
    variable is one unknown element of the problem, and the axiom Twee restates, with
    its variables universal, would be a stronger statement than the premise.
    """
    mapping: Dict[str, List[Tuple[Node, Node]]] = {}
    for i, premise in enumerate(axioms, start=1):
        equations: List[Tuple[Node, Node]] = []
        for lhs, rhs, free in _flatten_scoped(premise):
            if free:
                raise ValueError(
                    f"twee_check: premise {i} has the free variable(s) {sorted(free)}: a free "
                    f"variable is one unknown element, not a universally quantified one, so the "
                    f"equation is not one a proof's axiom with universal variables restates")
            equations.append((lhs, rhs))
        for k in range(len(equations)):
            mapping[f"premise_{i}" if k == 0 else f"premise_{i}_{k}"] = equations
    return mapping


# ---------------------------------------------------------------------------
# Alpha-equivalence (variable-renaming-blind) equation matching — used ONLY
# for the axiom-provenance cross-check (an axiom's restated equation must be
# the SAME equation as the original premise, up to a variable bijection,
# since Twee renames axiom variables to a canonical X/Y/Z scheme — see
# atp.twee_entailment's module docstring).
# ---------------------------------------------------------------------------

def _alpha_extend(t1: Node, t2: Node, fwd: Dict[str, str], bwd: Dict[str, str]):
    """Extend the variable bijection ``(fwd, bwd)`` matching ``t1`` onto ``t2``.

    ``fwd``/``bwd`` map ``t1``-side variable names to ``t2``-side names and
    back; returns the extended pair, or ``None`` on a genuine mismatch.
    Neither input dict is mutated.
    """
    if isinstance(t1, Variable) and isinstance(t2, Variable):
        mapped = fwd.get(t1.name)
        if mapped is not None:
            return (fwd, bwd) if mapped == t2.name else None
        if t2.name in bwd:
            return None
        new_fwd, new_bwd = dict(fwd), dict(bwd)
        new_fwd[t1.name] = t2.name
        new_bwd[t2.name] = t1.name
        return new_fwd, new_bwd
    if isinstance(t1, Variable) or isinstance(t2, Variable):
        return None
    if isinstance(t1, Constant) and isinstance(t2, Constant):
        return (fwd, bwd) if t1.name == t2.name else None
    if isinstance(t1, Number) and isinstance(t2, Number):
        return (fwd, bwd) if t1.value == t2.value else None
    if isinstance(t1, Function) and isinstance(t2, Function):
        if t1.name != t2.name or len(t1.args) != len(t2.args):
            return None
        for a1, a2 in zip(t1.args, t2.args):
            res = _alpha_extend(a1, a2, fwd, bwd)
            if res is None:
                return None
            fwd, bwd = res
        return fwd, bwd
    return None


def _equation_is_variant(expected: Tuple[Node, Node], actual: Tuple[Node, Node]) -> bool:
    """True iff ``actual`` is ``expected`` up to a single consistent variable renaming.

    Orientation-sensitive (``expected[0]`` must correspond to ``actual[0]``,
    not either side) — Twee's ``Axiom N (name): lhs = rhs.`` header was
    observed to always echo the premise's original left-to-right orientation
    (never auto-flipped), so this deliberately does not also try the swapped
    pairing.
    """
    res = _alpha_extend(expected[0], actual[0], {}, {})
    if res is None:
        return False
    res = _alpha_extend(expected[1], actual[1], res[0], res[1])
    return res is not None


# ---------------------------------------------------------------------------
# One-directional structural matching + position/replacement — the rewrite-
# step verifier's core. See module docstring: deliberately NOT
# fol.unification.unify (bidirectional; a term-side variable must never bind).
# ---------------------------------------------------------------------------

def _match(pattern: Node, term: Node, subst: Dict[str, Node]) -> Optional[Dict[str, Node]]:
    """Match ``pattern`` (may contain bindable Variables) against ``term`` (ground/opaque).

    Only ``pattern``'s own ``Variable`` nodes are ever bound; a ``Variable``
    appearing on the ``term`` side (e.g. a lemma's own rewrite variable
    showing up inside another citation's redex) is compared like any other
    leaf — by structural equality against whatever ``term`` already is,
    never unified against. Returns the extended substitution, or ``None``.
    ``subst`` is not mutated; already-bound pattern variables must match
    ``term`` exactly (via kit ``Node`` structural ``==``) to succeed again.
    """
    if isinstance(pattern, Variable):
        if pattern.name in subst:
            return subst if subst[pattern.name] == term else None
        new_subst = dict(subst)
        new_subst[pattern.name] = term
        return new_subst
    if isinstance(pattern, Constant):
        return subst if (isinstance(term, Constant) and term.name == pattern.name) else None
    if isinstance(pattern, Number):
        return subst if (isinstance(term, Number) and term.value == pattern.value) else None
    if isinstance(pattern, Function):
        if not isinstance(term, Function) or term.name != pattern.name \
                or len(term.args) != len(pattern.args):
            return None
        extended = subst
        for pa, ta in zip(pattern.args, term.args):
            step = _match(pa, ta, extended)
            if step is None:
                return None
            extended = step
        return extended
    return None   # a pattern shape this checker does not expect (e.g. an Atom)


def _positions(node: Node) -> List[Tuple[int, ...]]:
    """All subterm positions of ``node`` (argument-index paths), including ``()`` (the root)."""
    positions: List[Tuple[int, ...]] = [()]
    if isinstance(node, Function):
        for i, arg in enumerate(node.args):
            positions.extend((i,) + p for p in _positions(arg))
    return positions


def _get_at(node: Node, path: Tuple[int, ...]) -> Optional[Node]:
    """The subterm of ``node`` at ``path``, or ``None`` if ``path`` does not exist in it."""
    for i in path:
        if not isinstance(node, Function) or i >= len(node.args):
            return None
        node = node.args[i]
    return node


def _replace_at(node: Node, path: Tuple[int, ...], replacement: Node) -> Node:
    """Return ``node`` with the subterm at ``path`` replaced by ``replacement``."""
    if not path:
        return replacement
    if not isinstance(node, Function):
        raise ValueError("twee_check: _replace_at called with a path into a non-Function term")
    i, rest = path[0], path[1:]
    new_args = list(node.args)
    new_args[i] = _replace_at(node.args[i], rest, replacement)
    return Function(node.name, tuple(new_args))


def _freshen(node: Node, prefix: str) -> Node:
    """Rename every ``Variable`` in ``node`` by prepending ``prefix``.

    Twee names axiom/lemma rewrite variables from a canonical ``X``/``Y``/
    ``Z``/... pool that STARTS OVER independently for every equation (see
    :mod:`atp.twee_entailment`'s module docstring) — so a citation's "X" and
    the current proof term's own "X" (e.g. inside a LEMMA's chain, which
    keeps its own rewrite variables live throughout — verified live: this
    genuinely happens, e.g. Lemma 4 using X, Y while citing an axiom that
    ALSO prints as X, Y) are two unrelated variables that merely share a
    spelling. Without freshening, :func:`_match` would bind the citation's
    "X" to a term-side ``Variable("X")`` and :func:`~unicode_fol_kit.fol
    .unification.apply_subst` would loop forever resolving ``X -> X``
    (found live while building this checker). ``prefix`` uses ``#``, a
    character :func:`atp.twee_entailment._tokenize` never produces, so a
    freshened name can never collide with a genuine Twee-parsed one.
    """
    if isinstance(node, Variable):
        return Variable(prefix + node.name)
    if isinstance(node, Function):
        return Function(node.name, tuple(_freshen(a, prefix) for a in node.args))
    return node


def _verify_rewrite(term1: Node, term2: Node, from_pattern: Node, to_pattern: Node) -> bool:
    """True iff ``term2`` is ``term1`` with ONE subterm rewritten via ``from_pattern = to_pattern``.

    Tries every subterm position ``p`` of ``term1``: if the subterm there
    matches ``from_pattern`` (binding ``from_pattern``'s variables), and the
    corresponding subterm of ``term2`` at the SAME position matches
    ``to_pattern`` under that (extended) substitution — needed because a
    variable can appear only on the ``to`` side, e.g. an ``R->L`` step whose
    cited equation's "from" side (the original right-hand side) is a bare
    variable that does not mention every variable the "to" side does — then
    rebuilding ``term1`` with that position replaced by the fully-substituted
    ``to_pattern`` must reproduce ``term2`` exactly. Succeeds on the first
    matching position found.

    ``from_pattern``/``to_pattern`` are freshened (see :func:`_freshen`)
    before anything else — they belong to a DIFFERENT equation's variable
    scope than ``term1``/``term2``, and must never be confused with it.
    """
    from_pattern = _freshen(from_pattern, "#")
    to_pattern = _freshen(to_pattern, "#")
    for path in _positions(term1):
        sub1 = _get_at(term1, path)
        if sub1 is None:   # unreachable: every path of _positions(term1) exists in term1
            continue
        subst = _match(from_pattern, sub1, {})
        if subst is None:
            continue
        sub2 = _get_at(term2, path)
        if sub2 is None:
            continue
        subst2 = _match(to_pattern, sub2, subst)
        if subst2 is None:
            continue
        candidate = _replace_at(term1, path, apply_subst(to_pattern, subst2))
        if candidate == term2:
            return True
    return False


# ---------------------------------------------------------------------------
# check_twee_proof
# ---------------------------------------------------------------------------

def check_twee_proof(proof: TweeProof, axioms: Sequence[Node]) -> TweeCheckResult:
    """Independently verify ``proof`` against the original ``axioms`` (premises).

    Two passes:

    1. Every ``Axiom N (name): ...`` header in ``proof`` must name a premise
       actually present in ``axioms`` (``premise_<i>``, or ``premise_<i>_<k>``
       with ``k`` below the number of its conjuncts — see
       :func:`_expected_axiom_equations`), and its restated equation must be
       alpha-equivalent (see :func:`_equation_is_variant`) to that premise's
       equation or, for a conjunctive premise, to one of its conjuncts: which
       one is decided by what the axiom says, never by the suffix of its name,
       because Twee numbers the clauses of a conjunction in an order of its
       own. This is the boundary that makes the check genuinely independent
       of trusting Twee's own transcription: every axiom a proof uses is a
       consequence of a premise.
    2. Every lemma's proof chain, then the goal's, is walked step by step:
       each step must be licensed by :func:`_verify_rewrite` against the
       cited axiom (already cross-checked in pass 1) or an EARLIER lemma in
       the SAME proof (forward/self-citation is rejected); each chain's
       first and last term must equal its own header's stated ``lhs``/``rhs``.

    Returns the first failure found (``TweeCheckResult(False, "...")``), or
    ``TweeCheckResult(True)`` if everything checks out. Never raises for a
    well-formed :class:`TweeProof` and any ``axioms`` sequence of ``Node``s —
    a malformed ``axioms`` entry (not itself equational) is reported as a
    failure, not an exception.
    """
    try:
        expected = _expected_axiom_equations(axioms)
    except ValueError as exc:
        return TweeCheckResult(False, f"invalid axioms argument: {exc}")

    axiom_by_number: Dict[int, Tuple[str, Tuple[Node, Node]]] = {}
    for ax in proof.axioms:
        if ax.number in axiom_by_number:
            return TweeCheckResult(False, f"axiom {ax.number} is restated more than once")
        exp = expected.get(ax.name)
        if exp is None:
            return TweeCheckResult(
                False, f"axiom {ax.number} ({ax.name}): no given premise (or flattened "
                       f"conjunct of one) is named {ax.name!r}")
        actual = (ax.equation.lhs, ax.equation.rhs)
        if not any(_equation_is_variant(candidate, actual) for candidate in exp):
            return TweeCheckResult(
                False, f"axiom {ax.number} ({ax.name}): restated equation is not "
                       f"alpha-equivalent to the given premise or to any conjunct of it")
        axiom_by_number[ax.number] = (ax.name, actual)

    lemma_by_number: Dict[int, Tuple[Node, Node]] = {}

    def _resolve(citation: TweeCitation, enforce_before: Optional[int]):
        """Return ``(equation, None)`` or ``(None, error)`` for a citation."""
        if citation.kind == "axiom":
            entry = axiom_by_number.get(citation.number)
            if entry is None:
                return None, f"cites axiom {citation.number}, which was never stated in the proof header"
            stored_name, eq = entry
            if citation.name != stored_name:
                return None, (f"cites axiom {citation.number} as ({citation.name}), but that "
                              f"axiom number was stated as ({stored_name})")
            return eq, None
        lemma_eq = lemma_by_number.get(citation.number)
        if lemma_eq is None:
            return None, f"cites lemma {citation.number}, which is not an earlier proven lemma"
        if enforce_before is not None and citation.number >= enforce_before:
            return None, f"cites lemma {citation.number}, which is not strictly earlier"
        return lemma_eq, None

    def _check_chain(chain: TweeChain, enforce_before: Optional[int], label: str) -> Optional[str]:
        for i, citation in enumerate(chain.citations):
            eq, err = _resolve(citation, enforce_before)
            if err is not None:
                return f"{label} step {i + 1}: {err}"
            from_pattern, to_pattern = (eq[1], eq[0]) if citation.reversed else (eq[0], eq[1])
            if not _verify_rewrite(chain.terms[i], chain.terms[i + 1], from_pattern, to_pattern):
                cite_desc = (f"axiom {citation.number} ({citation.name})" if citation.kind == "axiom"
                            else f"lemma {citation.number}")
                direction = " R->L" if citation.reversed else ""
                return (f"{label} step {i + 1}: not a valid single-rewrite instance of "
                       f"{cite_desc}{direction}")
        return None

    for lemma in proof.lemmas:
        if lemma.chain.terms[0] != lemma.equation.lhs:
            return TweeCheckResult(
                False, f"lemma {lemma.number}: proof chain does not start at its stated left-hand side")
        if lemma.chain.terms[-1] != lemma.equation.rhs:
            return TweeCheckResult(
                False, f"lemma {lemma.number}: proof chain does not end at its stated right-hand side")
        err = _check_chain(lemma.chain, lemma.number, f"lemma {lemma.number}")
        if err is not None:
            return TweeCheckResult(False, err)
        lemma_by_number[lemma.number] = (lemma.equation.lhs, lemma.equation.rhs)

    goal = proof.goal
    if goal.chain.terms[0] != goal.equation.lhs:
        return TweeCheckResult(False, "goal: proof chain does not start at its stated left-hand side")
    if goal.chain.terms[-1] != goal.equation.rhs:
        return TweeCheckResult(False, "goal: proof chain does not end at its stated right-hand side")
    err = _check_chain(goal.chain, None, "goal")   # goal may cite ANY lemma (it is always last)
    if err is not None:
        return TweeCheckResult(False, err)

    return TweeCheckResult(True)


# ---------------------------------------------------------------------------
# goal_matches_conclusion
# ---------------------------------------------------------------------------

def _matches_conjunct(exp_lhs: Node, exp_rhs: Node, act_lhs: Node, act_rhs: Node,
                      taken: FrozenSet[str] = frozenset(),
                      notes: Optional[List[str]] = None) -> bool:
    """One conjunct's match: ``(exp_lhs, exp_rhs)`` structurally matches ``(act_lhs, act_rhs)``.

    Uses the same one-directional :func:`_match` as rewrite-step checking:
    the conclusion's own (bound) variables bind to whatever term Twee's Goal
    line actually shows there, threading ONE substitution across both sides
    of the equation. Two conditions make that binding the Skolemisation of
    the universal quantifiers and nothing weaker:

    * **Every variable is bound to a fresh constant.** ``Γ ⊨ ∀x φ(x)`` follows
      from ``Γ ⊨ φ(c)`` only when ``c`` is a constant of its own: one that
      occurs in no axiom the proof used and nowhere in the conclusion (nor is
      the name ``taken`` by the encoding of a conjunction, see
      :func:`goal_mismatch`). A constant that does occur there makes the goal
      an INSTANCE of the claim, and an instance is weaker: ``f(a) = g(a)`` from
      the premise ``f(a) = g(a)`` is not ``∀x f(x) = g(x)`` (universe ``{0, 1}``,
      ``a`` ↦ 0, ``f`` ↦ (0, 0), ``g`` ↦ (0, 1)). A compound term, a number or a
      variable of the goal is not a constant either. ``taken`` holds the
      names that are not fresh; a reason for a refusal is appended to ``notes``.
    * **The binding is INJECTIVE:** two distinct conclusion variables may never
      collapse onto the same goal constant. Skolemization maps distinct
      universally quantified variables to distinct fresh constants, so a
      non-injective binding means the Goal line proves a strictly WEAKER
      statement than the conclusion (a fresh ``c`` with ``f(c) = g(c)`` would
      otherwise "prove" ``∀X,Y. f(X) = g(Y)`` by binding both X and Y to
      ``c``) — the same bijection discipline :func:`_equation_is_variant`
      already enforces on the axiom-restatement trust boundary.
    """
    subst = _match(exp_lhs, act_lhs, {})
    if subst is None:
        return False
    subst = _match(exp_rhs, act_rhs, subst)
    if subst is None:
        return False
    names = []
    for variable, value in subst.items():
        if not isinstance(value, Constant):
            if notes is not None:
                notes.append(
                    f"the conclusion's variable {variable} is matched to "
                    f"{value.to_unicode_str()}, which is not a constant: only a constant of its "
                    f"own can stand for a universally quantified variable")
            return False
        if value.name in taken:
            if notes is not None:
                notes.append(
                    f"the conclusion's variable {variable} is matched to the constant "
                    f"{value.name}, which already occurs in an axiom of the proof or in the "
                    f"conclusion, so the goal is an instance of the claim, not the claim")
            return False
        names.append(value.name)
    return len(set(names)) == len(names)


def goal_matches_conclusion(proof: TweeProof, conclusion: Node) -> bool:
    """True iff ``proof.goal`` actually restates ``conclusion``: :func:`goal_mismatch` has
    nothing to say against it. Never raises."""
    return goal_mismatch(proof, conclusion) is None


def goal_mismatch(proof: TweeProof, conclusion: Node) -> Optional[str]:
    """``None`` iff ``proof.goal`` actually restates ``conclusion``, else why it does not.

    This is the second, SEPARATE trust boundary from :func:`check_twee_proof`
    (which never sees ``conclusion`` at all): a proof can be internally
    flawless yet prove the wrong thing if Twee's ``Goal`` header were ever
    inconsistent with the conjecture it was asked to prove. The two checks speak
    about ONE proof: the names that must be fresh below are fresh against the
    axioms the proof restates, which :func:`check_twee_proof` has cross-checked
    against the premises.

    A single-equation ``conclusion`` is matched directly against the goal's
    ``lhs``/``rhs``. A conjunctive ``conclusion`` (``n > 1`` top-level
    conjuncts after flattening) is matched against Twee's observed
    ``tuple(...)`` encoding: the goal's ``lhs`` and ``rhs`` must each be an
    application of ONE function symbol to exactly ``n`` arguments, matched against the
    ``n`` conjuncts by a
    backtracking SEARCH for a bijection (slot <-> conjunct), each pairing
    using its own independent fresh substitution — Twee was observed to (a)
    Skolemize each conjunct's variables separately even when they share a
    source name, and (b) NOT preserve the conclusion's source conjunct order
    in the tuple once a shared quantifier is involved (verified live: a
    2-conjunct quantified conclusion ``![X]: (g(g(g(g(X))))=X) &
    (f(f(X))=X)`` — g-conjunct first, f-conjunct second in the SOURCE —
    printed its Goal as ``tuple(f(f(x)), g(g(g(g(x2))))) = tuple(x, x2)``,
    f-conjunct FIRST) — so slot order cannot be assumed to track conjunct
    order; see :mod:`atp.twee_entailment`'s module docstring. Returns
    a reason (never raises) if ``conclusion`` is not itself a valid
    equation/conjunction, or if the tuple shape/bijection does not exist.

    **The encoding symbol is a name of Twee's own.** Twee calls it ``tuple``, and
    ``tuple2`` (then ``tuple3``, ...) when the problem already uses ``tuple``
    (measured: ``tuple2(tuple(b, c), e) = tuple2(d, f)`` for the conclusion
    ``tuple(b, c) = d ∧ e = f``). Which name it chose is not assumed: the symbol must
    occur in no axiom of the proof and nowhere in the conclusion, and it is not
    a name a variable of the conclusion is bound to. An equation between applications
    of a symbol the problem itself uses (a premise ``tuple(f(a), g(a)) = tuple(b, c)``)
    is a statement about that symbol, never the conjunction ``f(a) = b ∧ g(a) = c``
    (which does not follow: ``tuple`` need not be injective).

    **The constants a variable is bound to are fresh** (see :func:`_matches_conjunct`):
    a goal that is an instance of a universal claim at a constant of the problem is a
    weaker statement, and is refused with the constant's name.

    **A free variable of the conclusion** is one unknown element, not a universal
    one, and no goal Twee prints can say which: it is refused by name.

    **A conjunct that repeats another is one conjunct.** ``A ∧ A`` is ``A``, and Twee
    answers it as it answers ``A``: its clausifier drops a repeated GROUND conjunct
    (measured: ``f(a) = b ∧ f(a) = b`` is proved as the single goal ``f(a) = b``, and
    ``f(a) = b ∧ g(a) = c ∧ f(a) = b`` as ``tuple(f(a), g(a)) = tuple(b, c)``), where
    it keeps two conjuncts that have variables apart (each is Skolemised on its own:
    ``∀x (f(x) = x ∧ f(x) = x)`` is ``tuple(f(x2), f(x)) = tuple(x2, x)``). So the goal
    is matched against the conjuncts as they stand, and, when some of them repeat an
    earlier one (equal up to the renaming of their own variables, in the same
    orientation), also against the conjuncts with the repeats removed. Both are sound
    readings of the conclusion: a proof of every conjunct of the shorter list proves
    the longer one, whose extra members are copies of members of the shorter. Neither
    loosens the match itself: a proof of ``A`` still does not match ``A ∧ B``, a
    conjunct is still matched under an injective substitution, and a proof of the
    repeated conjunct matches ``A ∧ A`` only when the goal is that conjunct.
    """
    try:
        scoped = _flatten_scoped(conclusion)
    except ValueError as exc:
        return str(exc)

    free = sorted(set().union(*(variables for _, _, variables in scoped)))
    if free:
        return (f"the conclusion has the free variable(s) {free}: a free variable is one unknown "
                f"element, and the goal of a proof, whose variables are all universal, cannot "
                f"be the statement about it")

    conjuncts = [(lhs, rhs) for lhs, rhs, _ in scoped]
    taken: Set[str] = set()
    for axiom in proof.axioms:
        _symbol_names(axiom.equation.lhs, taken)
        _symbol_names(axiom.equation.rhs, taken)
    for lhs, rhs in conjuncts:
        _symbol_names(lhs, taken)
        _symbol_names(rhs, taken)

    goal_lhs, goal_rhs = proof.goal.equation.lhs, proof.goal.equation.rhs
    notes: List[str] = []

    if _goal_matches_conjuncts(goal_lhs, goal_rhs, conjuncts, frozenset(taken), notes):
        return None
    distinct = _distinct_conjuncts(conjuncts)
    if len(distinct) < len(conjuncts) and _goal_matches_conjuncts(
            goal_lhs, goal_rhs, distinct, frozenset(taken), notes):
        return None
    return notes[0] if notes else ("the goal is neither the conclusion's equation nor, for a "
                                   "conjunction, the equation between two applications of one "
                                   "fresh symbol to its conjuncts")


def _distinct_conjuncts(conjuncts: List[Tuple[Node, Node]]) -> List[Tuple[Node, Node]]:
    """``conjuncts`` without any that repeats an earlier one: the same equation, in the
    same orientation, up to a consistent renaming of its variables
    (:func:`_equation_is_variant`). Order is kept."""
    kept: List[Tuple[Node, Node]] = []
    for conjunct in conjuncts:
        if not any(_equation_is_variant(earlier, conjunct) for earlier in kept):
            kept.append(conjunct)
    return kept


def _goal_matches_conjuncts(goal_lhs: Node, goal_rhs: Node,
                            conjuncts: List[Tuple[Node, Node]],
                            taken: FrozenSet[str], notes: List[str]) -> bool:
    """Whether the goal ``goal_lhs = goal_rhs`` restates exactly ``conjuncts`` (see
    :func:`goal_mismatch`): one conjunct against the goal itself, several against
    the encoding of a conjunction, by a bijection of slots and conjuncts. ``taken`` holds
    the names the encoding symbol and the constants of the variables must not have."""
    if len(conjuncts) == 1:
        exp_lhs, exp_rhs = conjuncts[0]
        return _matches_conjunct(exp_lhs, exp_rhs, goal_lhs, goal_rhs, taken, notes)

    n = len(conjuncts)
    if not (isinstance(goal_lhs, Function) and len(goal_lhs.args) == n
            and isinstance(goal_rhs, Function) and goal_rhs.name == goal_lhs.name
            and len(goal_rhs.args) == n):
        return False
    encoding = goal_lhs.name
    if encoding in taken:
        notes.append(
            f"the goal is an equation between applications of {encoding}, which is how Twee "
            f"encodes a conjunction as one equation, but {encoding} is a symbol of an axiom of "
            f"the proof or of the conclusion, so the goal says something about that symbol, not "
            f"about the conjuncts")
        return False
    taken = taken | {encoding}

    used = [False] * n

    def backtrack(i: int) -> bool:
        if i == n:
            return True
        exp_lhs, exp_rhs = conjuncts[i]
        for j in range(n):
            if used[j]:
                continue
            if _matches_conjunct(exp_lhs, exp_rhs, goal_lhs.args[j], goal_rhs.args[j],
                                 taken, notes):
                used[j] = True
                if backtrack(i + 1):
                    return True
                used[j] = False
        return False

    return backtrack(0)
