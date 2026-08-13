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
from typing import Dict, List, Optional, Sequence, Tuple

from ..fol.nodes import And, Atom, Constant, Function, Node, Number, Quantifier, Variable
from ..fol.unification import apply_subst
from .twee_entailment import TweeChain, TweeCitation, TweeProof

__all__ = ["TweeCheckResult", "check_twee_proof", "goal_matches_conclusion"]


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

def _flatten_equations(node: Node) -> List[Tuple[Node, Node]]:
    """Flatten a (forall-closed) equation-or-conjunction into ``[(lhs, rhs), ...]``.

    Left-to-right in source order (``And`` is binary and this recurses
    left-then-right), matching the order Twee's own clausifier splits a
    conjunctive premise/conclusion into. Quantifiers are stripped (matching
    is variable-name-blind — see module docstring), so the returned pairs
    are plain term ``Node``s, still possibly containing the original bound
    variables.
    """
    if isinstance(node, Quantifier):
        if node.type not in ("forall", "∀"):
            raise ValueError(f"twee_check: non-universal quantifier {node.type!r} in premise/conclusion")
        return _flatten_equations(node.formula)
    if isinstance(node, And):
        return _flatten_equations(node.left) + _flatten_equations(node.right)
    if isinstance(node, Atom) and node.predicate == "=" and len(node.args) == 2:
        return [(node.args[0], node.args[1])]
    raise ValueError(f"twee_check: not an equation or conjunction of equations: "
                     f"{node.to_unicode_str()!r}")


def _expected_axiom_equations(axioms: Sequence[Node]) -> Dict[str, Tuple[Node, Node]]:
    """Map every ``premise_<i>``/``premise_<i>_<k>`` name to its (lhs, rhs) pair.

    Reproduces :mod:`atp.twee_entailment`'s naming exactly (see its module
    docstring): premise ``i`` (1-based) flattens to conjuncts ``k = 0, 1,
    2, ...``; conjunct 0 keeps the bare ``premise_<i>``, every later conjunct
    is ``premise_<i>_<k>``.
    """
    mapping: Dict[str, Tuple[Node, Node]] = {}
    for i, premise in enumerate(axioms, start=1):
        conjuncts = _flatten_equations(premise)
        for k, eq in enumerate(conjuncts):
            name = f"premise_{i}" if k == 0 else f"premise_{i}_{k}"
            mapping[name] = eq
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
        for pa, ta in zip(pattern.args, term.args):
            subst = _match(pa, ta, subst)
            if subst is None:
                return None
        return subst
    return None   # a pattern shape this checker does not expect (e.g. an Atom)


def _positions(node: Node) -> List[Tuple[int, ...]]:
    """All subterm positions of ``node`` (argument-index paths), including ``()`` (the root)."""
    positions = [()]
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
    return Function(node.name, new_args)


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
        return Function(node.name, [_freshen(a, prefix) for a in node.args])
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
       (or, for a conjunctive premise, one of its flattened conjuncts — see
       :func:`_expected_axiom_equations`) actually present in ``axioms``, and
       its restated equation must be alpha-equivalent to that premise's
       equation (see :func:`_equation_is_variant`) — this is the boundary
       that makes the check genuinely independent of trusting Twee's own
       transcription.
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
        if not _equation_is_variant(exp, actual):
            return TweeCheckResult(
                False, f"axiom {ax.number} ({ax.name}): restated equation is not "
                       f"alpha-equivalent to the given premise")
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
        eq = lemma_by_number.get(citation.number)
        if eq is None:
            return None, f"cites lemma {citation.number}, which is not an earlier proven lemma"
        if enforce_before is not None and citation.number >= enforce_before:
            return None, f"cites lemma {citation.number}, which is not strictly earlier"
        return eq, None

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

def _matches_conjunct(exp_lhs: Node, exp_rhs: Node, act_lhs: Node, act_rhs: Node) -> bool:
    """One conjunct's match: ``(exp_lhs, exp_rhs)`` structurally matches ``(act_lhs, act_rhs)``.

    Uses the same one-directional :func:`_match` as rewrite-step checking:
    the conclusion's own (possibly bound) variables bind to whatever term
    Twee's Goal line actually shows there (a Skolem constant, ordinarily —
    see :mod:`atp.twee_entailment`'s module docstring), threading ONE
    substitution across both sides of the equation — and then the binding
    must be INJECTIVE: two distinct conclusion variables may never collapse
    onto the same goal term. Skolemization maps distinct universally
    quantified variables to distinct fresh constants, so a non-injective
    binding means the Goal line proves a strictly WEAKER statement than the
    conclusion (adversarial-review reproduced: a ground fact ``f(a) = g(a)``
    would otherwise "prove" ``∀X,Y. f(X) = g(Y)`` by binding both X and Y
    to ``a``) — the same bijection discipline :func:`_equation_is_variant`
    already enforces on the axiom-restatement trust boundary.
    """
    subst = _match(exp_lhs, act_lhs, {})
    if subst is None:
        return False
    subst = _match(exp_rhs, act_rhs, subst)
    if subst is None:
        return False
    values = list(subst.values())
    return len(set(values)) == len(values)


def goal_matches_conclusion(proof: TweeProof, conclusion: Node) -> bool:
    """True iff ``proof.goal`` actually restates ``conclusion``.

    This is the second, SEPARATE trust boundary from :func:`check_twee_proof`
    (which never sees ``conclusion`` at all): a proof can be internally
    flawless yet prove the wrong thing if Twee's ``Goal`` header were ever
    inconsistent with the conjecture it was asked to prove.

    A single-equation ``conclusion`` is matched directly against the goal's
    ``lhs``/``rhs``. A conjunctive ``conclusion`` (``n > 1`` top-level
    conjuncts after flattening) is matched against Twee's observed
    ``tuple(...)`` encoding: the goal's ``lhs`` and ``rhs`` must each be a
    :class:`~unicode_fol_kit.fol.nodes.Function` named ``"tuple"`` with
    exactly ``n`` arguments, matched against the ``n`` conjuncts by a
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
    ``False`` (never raises) if ``conclusion`` is not itself a valid
    equation/conjunction, or if the tuple shape/bijection does not exist.
    """
    try:
        conjuncts = _flatten_equations(conclusion)
    except ValueError:
        return False

    goal_lhs, goal_rhs = proof.goal.equation.lhs, proof.goal.equation.rhs

    if len(conjuncts) == 1:
        exp_lhs, exp_rhs = conjuncts[0]
        return _matches_conjunct(exp_lhs, exp_rhs, goal_lhs, goal_rhs)

    n = len(conjuncts)
    if not (isinstance(goal_lhs, Function) and goal_lhs.name == "tuple" and len(goal_lhs.args) == n):
        return False
    if not (isinstance(goal_rhs, Function) and goal_rhs.name == "tuple" and len(goal_rhs.args) == n):
        return False

    used = [False] * n

    def backtrack(i: int) -> bool:
        if i == n:
            return True
        exp_lhs, exp_rhs = conjuncts[i]
        for j in range(n):
            if used[j]:
                continue
            if _matches_conjunct(exp_lhs, exp_rhs, goal_lhs.args[j], goal_rhs.args[j]):
                used[j] = True
                if backtrack(i + 1):
                    return True
                used[j] = False
        return False

    return backtrack(0)
