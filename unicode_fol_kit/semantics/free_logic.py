r"""Free logic — first-order logic without the existence assumption.

Classical FOL assumes every term denotes an *existing* individual, so universal
instantiation ``∀x φ → φ(c)`` and existential generalisation ``φ(c) → ∃x φ`` are
valid. **Free logic** drops that assumption: quantifiers range only over an *inner
domain* of existing objects ``E``, while constants and function terms may denote an
object of the wider outer domain, or fail to denote at all. An existence predicate
``E!(t)`` says "``t`` denotes an existing object", and the classical inference rules
hold only in their *guarded* forms ``(∀x φ ∧ E!(c)) → φ(c)`` and ``(φ(c) ∧ E!(c)) → ∃x φ``.

A :class:`FreeModel` carries an ``outer`` domain, the ``existing`` inner subset, a
(possibly partial) constant/function interpretation, and predicate tables over the
outer domain. Three policies for an atom that contains a **non-denoting** term:

- ``"negative"`` (default) — the atom is simply **false** (negative free logic;
  ``t = t`` then also fails when ``t`` does not denote);
- ``"positive"`` — self-identity ``t = t`` is **true** for any term, while every other
  atom with a non-denoting term is false (the common positive-free-logic convention
  for identity);
- ``"supervaluation"`` — treats every ground atom with a non-denoting term as a
  genuine truth-value **gap** rather than forcing it false, then asks whether the
  *whole formula* comes out true under **every** classical way of filling the gaps
  (a *precisification*), false under every one, or neither. A formula is true
  (*supertrue*) iff every precisification makes it true, false (*superfalse*) iff
  every precisification makes it false, and otherwise it is itself a gap — reported
  as ``False``, the same convention ``"negative"`` already uses for a single gappy
  atom (``free_satisfies`` always returns a plain ``bool``; there is no third value
  in the return type). The distinguishing case is a classical tautology such as
  ``P(e) ∨ ¬P(e)`` for non-denoting ``e``: each disjunct is individually a gap, yet
  *every* precisification of ``P(e)`` (true or false) makes the disjunction true, so
  the whole formula is supertrue — unlike naively combining each disjunct's own
  gappy verdict, which would stay a gap. See :func:`free_satisfies` for the bounded
  precisification search this policy runs (:data:`SUPERVALUATION_MAX_GAPS`).

Beyond single-model checking, :func:`free_find_model`, :func:`free_countermodel`,
:func:`free_is_valid` and :func:`free_entails` add a Mace4-style **bounded
search** over ``FreeModel``\ s, in the style of
:mod:`~unicode_fol_kit.semantics.modelfinder`: every outer domain size up to a bound,
every existing/outer split, every partial constant/function assignment, and every
predicate extension. See their docstrings for the honest bounded-search contract.
By default (``symmetry_breaking=True``) the partial constant assignment is
LNH-canonical rather than exhaustive — the same symmetry-breaking pass
:mod:`~unicode_fol_kit.semantics.modelfinder` applies (roadmap C23); see
``_search``'s docstring.

**Numerals.** A numeral is a constant identified by its VALUE (``Number(1) == Number(1.0)``:
one constant, named ``'1'`` in ``FreeModel.constants``), so it may fail to denote like any
constant, and nothing else is known about it: ``P(1) ⊢ P(1.0)`` is valid and ``⊢ 1 ≠ 2`` is
not. ``+ - * /`` are partial function symbols and ``< > ≤ ≥`` ordinary predicates. A
numeral and a constant spelled like its value (``Number(1)`` next to ``Constant('1')``) would
share one entry of ``constants``, so the pair is refused by name.

**A free variable is a parameter.** The search routes read a free variable as ONE unknown
EXISTING object, the same in every formula handed to a call (the assignment-wise consequence
relation: a variable ranges over the inner domain, as a bound one does). It is replaced, in all
the formulas of the call together, by a constant of its own name
(:func:`~unicode_fol_kit.fol._free_parameters.parameterize`) and the model must satisfy
``E!`` of that constant, so a model whose ``existing`` domain is empty is no model of a
problem that has a free variable, and the constant is reported in ``FreeModel.constants`` under
the variable's name. No formula is closed universally, and a conclusion is never negated
before its variables are replaced: ``P(x) ⊢ P(x)`` and ``P(x) ⊢ ∃y P(y)`` are valid,
``P(x) ⊢ P(alpha)`` is not. A free variable spelled like a constant of the problem is refused
(``NotImplementedError``): ``FreeModel.constants`` holds one entry per name.

Public API: :class:`FreeModel`, :data:`NONDENOTING`, :data:`SUPERVALUATION_MAX_GAPS`,
:func:`free_satisfies`, :func:`free_holds`, :func:`free_find_model`,
:func:`free_countermodel`, :func:`free_is_valid`, :func:`free_entails`.
"""

from dataclasses import dataclass, field
from itertools import product
from typing import Any, Dict, FrozenSet, List, Mapping, Optional, Sequence, Tuple

from ..fol.nodes import (
    Node, Atom, Not, And, Or, Xor, Implies, Iff, Quantifier,
    Variable, Constant, Number, Function,
)
from ..fol._fol_nodes import numeral_key
from ..fol._truth_constants import truth_value as _truth_value
from ..fol._free_parameters import parameterize
from .modelfinder import _lnh_choices
from .tarski import _refuse_numeral_constant_pair

# Sentinel returned by term evaluation when a term has no referent.
NONDENOTING = object()

_FORALL = ("∀", "forall")
_EXISTS = ("∃", "exists")
_EXISTS_PRED = "E!"     # the existence predicate


@dataclass(frozen=True)
class FreeModel:
    """A free-logic model: an inner ``existing`` domain inside an ``outer`` domain.

    ``outer`` lists every object (existing or merely possible); ``existing`` is the
    inner domain the quantifiers range over (⊆ ``outer``). ``constants`` maps a name to
    an ``outer`` element — a name absent from the map is **non-denoting**. ``functions``
    maps ``(name, arity)`` to a partial table ``{argtuple: value}`` (a missing entry, or
    any non-denoting argument, makes the application non-denoting). ``predicates`` maps
    ``(name, arity)`` to a set of ``outer`` tuples.
    """

    outer: Tuple[Any, ...]
    existing: FrozenSet[Any]
    constants: Mapping[str, Any] = field(default_factory=dict)
    functions: Mapping[Tuple[str, int], Mapping[Tuple[Any, ...], Any]] = field(default_factory=dict)
    predicates: Mapping[Tuple[str, int], FrozenSet[Tuple[Any, ...]]] = field(default_factory=dict)


def _term_value(term: Node, model: FreeModel, assignment: Mapping[str, Any]):
    """Evaluate a term to an outer-domain element, or :data:`NONDENOTING`."""
    if isinstance(term, Variable):
        return assignment.get(term.name, NONDENOTING)
    if isinstance(term, Constant):
        return model.constants.get(term.name, NONDENOTING)
    if isinstance(term, Number):
        # a numeral is the constant of its VALUE (1 and 1.0 are one), absent = non-denoting
        return model.constants.get(numeral_key(term.value), NONDENOTING)
    if isinstance(term, Function):
        args = tuple(_term_value(a, model, assignment) for a in term.args)
        if any(v is NONDENOTING for v in args):
            return NONDENOTING
        table = model.functions.get((term.name, len(term.args)), {})
        return table.get(args, NONDENOTING)
    raise TypeError(f"free_logic: not a term: {type(term).__name__}")


def free_satisfies(formula: Node, model: FreeModel,
                   assignment: Optional[Mapping[str, Any]] = None,
                   policy: str = "negative") -> bool:
    """Return whether ``model`` satisfies ``formula`` under free-logic semantics.

    Quantifiers range over ``model.existing``; ``E!(t)`` is true iff ``t`` denotes an
    existing object; an atom with a non-denoting term is handled per ``policy``
    (``"negative"`` / ``"positive"`` / ``"supervaluation"`` — see the module
    docstring). Under ``"supervaluation"`` this delegates to :func:`_supervaluate`,
    a bounded search over every classical completion of the formula's gap atoms
    (capped at :data:`SUPERVALUATION_MAX_GAPS` distinct gaps).

    A numeral is a constant identified by its VALUE (``1`` and ``1.0`` are one, looked up
    under ``'1'`` in ``model.constants``, and non-denoting when absent there).

    Raises:
        NotImplementedError: ``formula`` holds a :class:`Number` and a constant spelled like
            its value (``Number(1)`` next to ``Constant('1')``): ``model.constants`` has ONE
            entry ``'1'`` for both, so the kit refuses to merge a numeral with the constant
            of the same spelling.
    """
    if assignment is None:
        assignment = {}
    if policy not in ("negative", "positive", "supervaluation"):
        raise ValueError(
            f"free_satisfies: unknown policy {policy!r} (negative / positive / supervaluation).")
    _refuse_numeral_constant_pair([formula], "semantics.free_logic")
    return _satisfies(formula, model, assignment, policy)


def _satisfies(formula: Node, model: FreeModel, assignment: Mapping[str, Any],
               policy: str) -> bool:
    """:func:`free_satisfies` without the checks of the formula as a whole, which the
    entry made: every recursive step and the model search land here."""
    if policy == "supervaluation":
        return _supervaluate(formula, model, assignment)

    if isinstance(formula, Atom):
        return _atom(formula, model, assignment, policy)
    if isinstance(formula, Not):
        return not _satisfies(formula.formula, model, assignment, policy)
    if isinstance(formula, And):
        return (_satisfies(formula.left, model, assignment, policy)
                and _satisfies(formula.right, model, assignment, policy))
    if isinstance(formula, Or):
        return (_satisfies(formula.left, model, assignment, policy)
                or _satisfies(formula.right, model, assignment, policy))
    if isinstance(formula, Xor):
        return (_satisfies(formula.left, model, assignment, policy)
                != _satisfies(formula.right, model, assignment, policy))
    if isinstance(formula, Implies):
        return ((not _satisfies(formula.left, model, assignment, policy))
                or _satisfies(formula.right, model, assignment, policy))
    if isinstance(formula, Iff):
        return (_satisfies(formula.left, model, assignment, policy)
                == _satisfies(formula.right, model, assignment, policy))
    if isinstance(formula, Quantifier):
        var = formula.variable.name
        results = (
            _satisfies(formula.formula, model, {**assignment, var: d}, policy)
            for d in model.existing
        )
        if formula.type in _FORALL:
            return all(results)
        if formula.type in _EXISTS:
            return any(results)
        raise ValueError(f"free_satisfies: unknown quantifier {formula.type!r}")
    raise TypeError(f"free_satisfies: unsupported node {type(formula).__name__}")


def _atom(atom: Atom, model: FreeModel, assignment: Mapping[str, Any], policy: str) -> bool:
    """Truth value of an atom, applying the non-denoting policy."""
    constant = _truth_value(atom)
    if constant is not None:
        return constant         # `$true` / `$false` have no term, so nothing can fail to denote
    values = tuple(_term_value(a, model, assignment) for a in atom.args)
    nondenoting = any(v is NONDENOTING for v in values)

    if atom.predicate == _EXISTS_PRED and len(atom.args) == 1:
        return (not nondenoting) and values[0] in model.existing
    if atom.predicate in ("=", "≠"):
        if nondenoting:
            # negative: t=t false when t non-denoting; positive: self-identity true.
            eq = (policy == "positive" and atom.args[0] == atom.args[1])
            return eq if atom.predicate == "=" else (not eq)
        eq = values[0] == values[1]
        return eq if atom.predicate == "=" else (not eq)
    if nondenoting:
        return False                              # negative & positive agree for predicates
    relation = model.predicates.get((atom.predicate, len(atom.args)), frozenset())
    return values in relation


def free_holds(formula: Node, model: FreeModel, policy: str = "negative") -> bool:
    """Convenience: ``free_satisfies`` of a closed ``formula`` (empty assignment)."""
    return free_satisfies(formula, model, {}, policy)


# ---------------------------------------------------------------------------
# Supervaluationism — policy="supervaluation" for free_satisfies.
#
# A "gap atom" is a ground occurrence of an ordinary predicate atom (never ``=``,
# ``≠`` or ``E!`` — those are always decided, per the negative-free-logic reading,
# regardless of policy: identity/existence are not treated as an additional locus
# of gap here) that has a non-denoting argument. A *precisification* assigns each
# distinct gap atom a classical truth value, consistently everywhere it recurs in
# the formula (the same ground atom under a quantifier, e.g. one instantiated at
# the same domain element from two different sub-formulas, gets the same value).
# The formula is supertrue / superfalse / a gap according to whether every, no, or
# some-but-not-all of the 2**n precisifications make it true — see the module
# docstring for the running P(e) ∨ ¬P(e) example.
# ---------------------------------------------------------------------------

#: Hard cap on the number of distinct gap atoms a single supervaluation may
#: enumerate (2**n precisifications to check, each a full recursive evaluation of
#: the formula) — exceeding it raises rather than silently truncating the search.
SUPERVALUATION_MAX_GAPS = 16


def _term_repr(term: Node, assignment: Mapping[str, Any]) -> Tuple[Any, ...]:
    """A hashable structural key identifying ``term`` under ``assignment``.

    Unlike :func:`_term_value`, this never collapses to :data:`NONDENOTING` — two
    syntactically different non-denoting terms (e.g. two different constants
    absent from ``model.constants``) get different keys, so they can be
    precisified independently, while the same term recurring (e.g. under a
    quantifier, once per bound variable) gets the same key both times, so
    :func:`_supervaluate` can hold it to a single consistent precisified value.
    """
    if isinstance(term, Variable):
        return ("var", assignment.get(term.name))
    if isinstance(term, Constant):
        return ("const", term.name)
    if isinstance(term, Number):
        return ("num", numeral_key(term.value))
    if isinstance(term, Function):
        return ("fn", term.name, tuple(_term_repr(a, assignment) for a in term.args))
    raise TypeError(f"free_logic: not a term: {type(term).__name__}")


def _is_gap_candidate(atom: Atom) -> bool:
    """Whether ``atom`` is ever subject to precisification (identity/E!/$true/$false never are)."""
    if _truth_value(atom) is not None:
        return False
    if atom.predicate == _EXISTS_PRED and len(atom.args) == 1:
        return False
    if atom.predicate in ("=", "≠"):
        return False
    return True


def _gap_key(atom: Atom, assignment: Mapping[str, Any]) -> Tuple[Any, ...]:
    """The precisification-dict key for a gappy occurrence of ``atom``."""
    return (atom.predicate, tuple(_term_repr(a, assignment) for a in atom.args))


def _collect_gap_atoms(formula: Node, model: FreeModel,
                       assignment: Mapping[str, Any], gaps: set) -> None:
    """Populate ``gaps`` with the key of every non-denoting gap-candidate atom in
    ``formula``, instantiating quantifiers over ``model.existing`` (finite domain)."""
    if isinstance(formula, Atom):
        if not _is_gap_candidate(formula):
            return
        values = tuple(_term_value(a, model, assignment) for a in formula.args)
        if any(v is NONDENOTING for v in values):
            gaps.add(_gap_key(formula, assignment))
        return
    if isinstance(formula, Quantifier):
        var = formula.variable.name
        for d in model.existing:
            _collect_gap_atoms(formula.formula, model, {**assignment, var: d}, gaps)
        return
    for child in formula._child_nodes():
        _collect_gap_atoms(child, model, assignment, gaps)


def _atom_precisified(atom: Atom, model: FreeModel, assignment: Mapping[str, Any],
                      precisification: Mapping[Tuple[Any, ...], bool]) -> bool:
    """Truth value of ``atom`` under one precisification (identity/E! bypass it)."""
    if not _is_gap_candidate(atom):
        return _atom(atom, model, assignment, "negative")
    values = tuple(_term_value(a, model, assignment) for a in atom.args)
    if any(v is NONDENOTING for v in values):
        return precisification[_gap_key(atom, assignment)]
    relation = model.predicates.get((atom.predicate, len(atom.args)), frozenset())
    return values in relation


def _eval_precisified(formula: Node, model: FreeModel, assignment: Mapping[str, Any],
                      precisification: Mapping[Tuple[Any, ...], bool]) -> bool:
    """``free_satisfies``'s recursion, but gap atoms resolve via ``precisification``."""
    if isinstance(formula, Atom):
        return _atom_precisified(formula, model, assignment, precisification)
    if isinstance(formula, Not):
        return not _eval_precisified(formula.formula, model, assignment, precisification)
    if isinstance(formula, And):
        return (_eval_precisified(formula.left, model, assignment, precisification)
                and _eval_precisified(formula.right, model, assignment, precisification))
    if isinstance(formula, Or):
        return (_eval_precisified(formula.left, model, assignment, precisification)
                or _eval_precisified(formula.right, model, assignment, precisification))
    if isinstance(formula, Xor):
        return (_eval_precisified(formula.left, model, assignment, precisification)
                != _eval_precisified(formula.right, model, assignment, precisification))
    if isinstance(formula, Implies):
        return ((not _eval_precisified(formula.left, model, assignment, precisification))
                or _eval_precisified(formula.right, model, assignment, precisification))
    if isinstance(formula, Iff):
        return (_eval_precisified(formula.left, model, assignment, precisification)
                == _eval_precisified(formula.right, model, assignment, precisification))
    if isinstance(formula, Quantifier):
        var = formula.variable.name
        results = (
            _eval_precisified(formula.formula, model, {**assignment, var: d}, precisification)
            for d in model.existing
        )
        if formula.type in _FORALL:
            return all(results)
        if formula.type in _EXISTS:
            return any(results)
        raise ValueError(f"free_satisfies: unknown quantifier {formula.type!r}")
    raise TypeError(f"free_satisfies: unsupported node {type(formula).__name__}")


def _supervaluate(formula: Node, model: FreeModel, assignment: Mapping[str, Any]) -> bool:
    """``policy="supervaluation"`` entry point: enumerate every precisification.

    Collects the formula's gap atoms (quantifiers instantiated over
    ``model.existing``), enumerates all ``2**n`` classical completions, and
    evaluates the formula under each with :func:`_eval_precisified`. Returns
    ``True`` iff every completion agrees on ``True`` (supertrue), ``False`` iff
    every completion agrees on ``False`` (superfalse) OR the completions disagree
    (a genuine gap — see the module docstring for why this collapses to the same
    ``False`` a lone gappy atom already returns under ``"negative"``).
    """
    gaps: set = set()
    _collect_gap_atoms(formula, model, assignment, gaps)
    if len(gaps) > SUPERVALUATION_MAX_GAPS:
        raise ValueError(
            f"free_satisfies: supervaluation over {len(gaps)} distinct gap atom(s) exceeds "
            f"SUPERVALUATION_MAX_GAPS = {SUPERVALUATION_MAX_GAPS} (2**n precisifications to "
            "check, each a full evaluation of the formula); reformulate with fewer "
            "non-denoting ground atoms, or evaluate under policy='negative' / 'positive' "
            "instead.")
    gap_list = sorted(gaps, key=repr)   # order just needs to be fixed across the loop below

    saw_true = False
    saw_false = False
    for bits in product((False, True), repeat=len(gap_list)):
        precisification = dict(zip(gap_list, bits))
        if _eval_precisified(formula, model, assignment, precisification):
            saw_true = True
        else:
            saw_false = True
        if saw_true and saw_false:
            return False                  # already a gap; no need to check the rest
    return saw_true and not saw_false


# ---------------------------------------------------------------------------
# Bounded model search — the Mace4-style partner of free_satisfies, in the
# style of semantics/modelfinder.py (read it first: _Signature, _candidate_count,
# _interpretations, find_model / find_countermodel / is_valid_finite).
#
# Symmetry breaking (roadmap C23, ``symmetry_breaking=True`` below, the default):
# hand-ports modelfinder's LNH generator to this module's PARTIAL constant tables
# — see ``_canonical_constant_assignments`` and ``_canonical_candidate_models``,
# and ``modelfinder._canonical_interpretations``'s docstring for the full
# soundness argument (and the hand-checked counterexample showing why functions
# are deliberately NOT also LNH-reduced here, for the identical reason).
# ---------------------------------------------------------------------------

#: A partial function's table has, per argument tuple, (n+1) choices (one of the n
#: domain elements, or "undefined"/non-denoting — see _term_value) and n**arity
#: argument tuples, so the table space is (n+1)**(n**arity): already ~4·10^7 at
#: n=3, arity=3. Rather than let max_candidates silently starve every domain size
#: for a function this shape (see _search's "every size skipped" check), functions
#: above this arity are rejected outright, up front, with a clean message.
MAX_FUNCTION_ARITY = 2

#: Interpretations visited per domain size before that size is skipped (mirrors
#: modelfinder.MAX_CANDIDATES). Free logic multiplies further by the number of
#: existing/outer splits tried (2**k under domain_split="any", 1 under "total"), so
#: a signature that modelfinder would happily search at some k can cost more here.
MAX_CANDIDATES = 1 << 20


def _free_var_names(node: Node, bound: FrozenSet[str] = frozenset()) -> set:
    """Return the names of variables occurring free in ``node`` (Quantifier binds).

    Mirrors modelfinder._free_var_names, restricted to the node types free_satisfies
    supports (no Count/Cardinality/SlashedExists binders exist in this fragment).
    """
    if isinstance(node, Variable):
        return set() if node.name in bound else {node.name}
    if isinstance(node, Quantifier):
        return _free_var_names(node.formula, bound | {node.variable.name})
    names: set = set()
    for child in node._child_nodes():
        names |= _free_var_names(child, bound)
    return names


def _universal_closure(node: Node) -> Node:
    """Wrap ``node`` in ∀ for each free variable (deterministic order).

    ∀ ranges over ``existing`` under free-logic semantics (see the module
    docstring), so the closure of ONE sentence says it holds under every assignment of
    its free variables to existing objects. It is a tool for a single sentence that is
    evaluated, never the reading of a problem: the search routes read a free variable as
    a parameter shared by every formula of the call (:func:`_with_parameters`).
    """
    result = node
    for name in sorted(_free_var_names(node), reverse=True):
        result = Quantifier("∀", Variable(name), result)
    return result


def _signature(node: Node) -> Tuple[set, set, set]:
    """Return ``(constant names, {(name, arity)} functions, {(name, arity)} predicates)``.

    Mirrors modelfinder._Signature.scan for the node types free_satisfies supports.
    ``=``, ``≠`` and the existence predicate ``E!`` are handled natively by
    free_satisfies / _atom and are never collected as ordinary predicates to
    interpret (interpreting ``E!`` would be incoherent: it is defined FROM
    ``existing``, not a free table).
    """
    constants: set = set()
    functions: set = set()
    predicates: set = set()

    def scan(n: Node) -> None:
        if isinstance(n, Constant):
            constants.add(n.name)
        elif isinstance(n, Number):
            constants.add(numeral_key(n.value))
        elif isinstance(n, Function):
            functions.add((n.name, len(n.args)))
            for a in n.args:
                scan(a)
        elif isinstance(n, Atom):
            if n.predicate not in ("=", "≠", _EXISTS_PRED) and _truth_value(n) is None:
                predicates.add((n.predicate, len(n.args)))
            for a in n.args:
                scan(a)
        else:
            for child in n._child_nodes():
                scan(child)

    scan(node)
    return constants, functions, predicates


def _candidate_count(n_constants: int, functions: set, predicates: set,
                     k: int, domain_split: str) -> int:
    """The number of distinct FreeModel candidates of outer-domain size ``k``.

    Existing/outer splits (``2**k`` under ``"any"`` — every subset, INCLUDING the
    empty set: free logic, unlike classical FOL, does not require an existing
    object, so an empty inner domain is a legitimate model, see
    :func:`_existing_subsets`; exactly ``1`` under ``"total"``) times
    ``(k+1)**n_constants`` partial constant assignments (k denoting choices +
    non-denoting) times, per function of arity a, ``(k+1)**(k**a)`` partial tables,
    times, per predicate of arity a, ``2**(k**a)`` extensional choices over the
    OUTER domain (predicates apply to outer elements whether or not they exist —
    see ``_atom``).
    """
    splits = (1 << k) if domain_split == "any" else 1
    total = splits * ((k + 1) ** n_constants)
    for _, arity in functions:
        total *= (k + 1) ** (k ** arity)
    for _, arity in predicates:
        total *= 1 << (k ** arity)
    return total


def _canonical_constant_count(n_slots: int, k: int) -> int:
    """The EXACT number of LNH-canonical PARTIAL constant assignments
    :func:`_canonical_constant_assignments` yields for ``n_slots`` constant names
    over a ``k``-element domain — computed analytically (``O(n_slots * k)``
    arithmetic, no enumeration), mirroring
    :func:`~unicode_fol_kit.semantics.modelfinder._lnh_constant_count`'s DP but with
    the extra "non-denoting" (``None``) option :func:`_canonical_constant_assignments`
    offers at every cell alongside :func:`~unicode_fol_kit.semantics.modelfinder._lnh_choices`'s
    domain-value range — a cell can go non-denoting, repeat one of the ``j``
    already-used domain values, or (if ``j < k``) introduce the next unused one.
    ``None`` is never subject to the relabeling argument (a term either denotes an
    outer-domain element or it does not, independent of which permutation would
    rename that element were it to denote one — see
    :func:`_canonical_constant_assignments`'s docstring), so it is simply one more
    option per cell, orthogonal to ``j``. Hand-checked for n_slots=1,k=1 -> 2 in
    ``tests/test_modelfinder_symmetry.py``.
    """
    if n_slots == 0:
        return 1
    dp = [1] * (k + 1)
    for _ in range(n_slots):
        new_dp = [0] * (k + 1)
        for j in range(k + 1):
            total = (1 + j) * dp[j]        # non-denoting, or repeat a used value
            if j < k:
                total += dp[j + 1]          # or introduce the next still-unused one
            new_dp[j] = total
        dp = new_dp
    return dp[0]


def _canonical_candidate_count(n_constants: int, functions: set, predicates: set,
                               k: int, domain_split: str) -> int:
    """The EXACT number of FreeModel candidates :func:`_canonical_candidate_models`
    yields for this signature over an outer domain of size ``k`` — the analytic
    pre-flight count backing :func:`_search`'s "skip this size" check when
    ``symmetry_breaking=True``, playing the same role :func:`_candidate_count` plays
    for the unbroken enumeration (see
    :func:`~unicode_fol_kit.semantics.modelfinder._canonical_candidate_count` for the
    classical-FOL analogue). Only the constants factor changes, via
    :func:`_canonical_constant_count`; functions and predicates keep the exact same
    raw factors :func:`_candidate_count` uses, because
    :func:`_canonical_candidate_models` leaves those fully exhaustive. Being exact
    means this alone decides whether a size is searched — a signature with few or no
    constants (where LNH cannot reduce anything) is skipped exactly as cheaply as it
    was before symmetry breaking existed, instead of live-enumerating candidates and
    calling :func:`free_satisfies` on each up to ``max_candidates`` before finding
    that out.
    """
    splits = (1 << k) if domain_split == "any" else 1
    total = splits * _canonical_constant_count(n_constants, k)
    for _, arity in functions:
        total *= (k + 1) ** (k ** arity)
    for _, arity in predicates:
        total *= 1 << (k ** arity)
    return total


def _existing_subsets(domain: Tuple[Any, ...], domain_split: str):
    """Yield every candidate ``existing`` set for ``domain`` under ``domain_split``.

    ``"any"`` — every subset of the outer domain, INCLUDING the empty set (an
    empty inner domain is a legitimate free-logic model — ∀ vacuously true, ∃
    always false there, per free_satisfies). ``"total"`` — only
    ``existing == outer`` (everything denotable exists), the classical-FOL-
    equivalent reading; with no constants/functions in the formula this makes the
    search coincide with :mod:`~unicode_fol_kit.semantics.modelfinder` exactly
    (see the differential test in tests/test_free_logic_search.py).
    """
    if domain_split == "total":
        yield frozenset(domain)
        return
    if domain_split != "any":
        raise ValueError(
            f"free_logic model search: unknown domain_split {domain_split!r} "
            '("any" / "total").')
    n = len(domain)
    for mask in range(1 << n):
        yield frozenset(domain[i] for i in range(n) if (mask >> i) & 1)


def _constant_assignments(domain: Tuple[Any, ...], const_names: List[str]):
    """Yield every partial constant assignment: each name to a domain element, or omitted."""
    options = list(domain) + [None]          # None = "omit" = non-denoting
    for choice in product(options, repeat=len(const_names)):
        yield {name: val for name, val in zip(const_names, choice) if val is not None}


def _function_interpretations(domain: Tuple[Any, ...], func_sig: List[Tuple[str, int]]):
    """Yield every partial function-table dict for ``func_sig`` over ``domain``.

    Each argument tuple maps to a domain element, or is omitted (the application is
    non-denoting on that tuple — see ``_term_value``).
    """
    if not func_sig:
        yield {}
        return
    per_function = []
    for _, arity in func_sig:
        arg_tuples = list(product(domain, repeat=arity))
        value_options = list(domain) + [None]
        per_function.append(list(product(value_options, repeat=len(arg_tuples))))
    for combo in product(*per_function):
        functions = {}
        for (name, arity), values in zip(func_sig, combo):
            arg_tuples = list(product(domain, repeat=arity))
            functions[(name, arity)] = {
                at: v for at, v in zip(arg_tuples, values) if v is not None
            }
        yield functions


def _predicate_interpretations(domain: Tuple[Any, ...], pred_sig: List[Tuple[str, int]]):
    """Yield every predicate-table dict for ``pred_sig``: a subset of outer**arity each."""
    if not pred_sig:
        yield {}
        return
    per_predicate = []
    for _, arity in pred_sig:
        arg_tuples = list(product(domain, repeat=arity))
        per_predicate.append(list(product((False, True), repeat=len(arg_tuples))))
    for combo in product(*per_predicate):
        predicates = {}
        for (name, arity), mask in zip(pred_sig, combo):
            arg_tuples = list(product(domain, repeat=arity))
            predicates[(name, arity)] = frozenset(t for t, inc in zip(arg_tuples, mask) if inc)
        yield predicates


def _candidate_models(domain, const_names, func_sig, pred_sig, domain_split):
    """Yield every FreeModel candidate over ``domain`` for the given signature."""
    for existing in _existing_subsets(domain, domain_split):
        for constants in _constant_assignments(domain, const_names):
            for functions in _function_interpretations(domain, func_sig):
                for predicates in _predicate_interpretations(domain, pred_sig):
                    yield FreeModel(outer=domain, existing=existing, constants=constants,
                                    functions=functions, predicates=predicates)


def _canonical_constant_assignments(domain: Tuple[Any, ...], const_names: List[str]):
    """Yield every partial constant assignment, LNH-canonical (roadmap C23).

    The free-logic analogue of ``modelfinder._canonical_interpretations``,
    restricted — like it — to CONSTANTS only; see that function's docstring for
    the hand-checked counterexample showing why a flat per-cell LNH cap is sound
    for an argument-free cell (a constant) but NOT for a function's table (its
    cells are indexed by argument tuples that are themselves domain elements,
    subject to the same relabeling as the stored value).

    Each cell is offered, in this order: "non-denoting" first (never subject to
    the relabeling argument at all — a term either denotes some outer-domain
    element or it does not, independent of *which* permutation would rename that
    element were it to denote one), then :func:`~unicode_fol_kit.semantics.modelfinder._lnh_choices`'s
    domain-value range: an already-used domain value, or the smallest still-unused
    one. Functions, predicates and the existing/outer split are exhaustively
    enumerated around this generator by the caller
    (:func:`_canonical_candidate_models`), exactly as
    ``modelfinder._canonical_interpretations`` leaves functions and predicates
    untouched — see its docstring for why that keeps the search complete.
    """
    k = len(domain)
    n = len(const_names)

    def backtrack(i: int, next_new: int, values: list):
        if i == n:
            yield {name: domain[v] for name, v in zip(const_names, values) if v is not None}
            return
        for v in (None,) + tuple(_lnh_choices(next_new, k)):
            values.append(v)
            new_next = next_new + 1 if (v is not None and v == next_new) else next_new
            yield from backtrack(i + 1, new_next, values)
            values.pop()

    yield from backtrack(0, 0, [])


def _canonical_candidate_models(domain, const_names, func_sig, pred_sig, domain_split):
    """Yield every FreeModel candidate with LNH-canonical constants (roadmap C23).

    Mirrors :func:`_candidate_models`, but the constant assignment comes from
    :func:`_canonical_constant_assignments` instead of the exhaustive
    :func:`_constant_assignments`; functions, predicates and the existing/outer
    split stay fully exhaustive (see that function's docstring, and
    ``modelfinder._canonical_interpretations``'s, for why that keeps the search
    sound and complete).
    """
    for existing in _existing_subsets(domain, domain_split):
        for constants in _canonical_constant_assignments(domain, const_names):
            for functions in _function_interpretations(domain, func_sig):
                for predicates in _predicate_interpretations(domain, pred_sig):
                    yield FreeModel(outer=domain, existing=existing, constants=constants,
                                    functions=functions, predicates=predicates)


def _with_parameters(formulas: Sequence[Node]) -> Tuple[List[Node], List[Node]]:
    """Read every free variable of ``formulas`` as a PARAMETER: ``(formulas, guards)``.

    The variable is replaced, in all the formulas together, by a constant of its own name
    (:func:`~unicode_fol_kit.fol._free_parameters.parameterize`). A variable of free logic
    ranges over the EXISTING objects, so each parameter comes with the guard ``E!(c)``
    that a model has to satisfy too: ``c`` denotes and is in ``existing``. A model with
    no existing object therefore satisfies no problem that has a free variable.

    Raises:
        NotImplementedError: a free variable has the spelling of a constant of ``formulas``.
    """
    closed, parameters = parameterize(list(formulas), after_variables=True)
    return closed, [Atom(_EXISTS_PRED, (constant,)) for constant in parameters.values()]


def _search(formulas: Sequence[Node], max_size: int, policy: str, domain_split: str,
           max_candidates: int, symmetry_breaking: bool = True) -> Optional[FreeModel]:
    """Return the first FreeModel making every one of ``formulas`` true, or None.

    ``formulas`` must not have a free variable: the callers read each one as a parameter
    first (:func:`_with_parameters`), before any formula is negated. The signature
    (constants/functions/predicates) is collected from the formulas jointly, and every
    domain size ``1..max_size`` is tried in turn.

    ``symmetry_breaking`` (default True, roadmap C23) enumerates constants with
    :func:`_canonical_candidate_models` (LNH — see its docstring) instead of the
    plain :func:`_candidate_models`. Because the LNH-reduced candidate count for a
    size can be far below the analytic ``_candidate_count`` estimate, this path
    uses :func:`_canonical_candidate_count` for the pre-flight "skip this size"
    check instead — the EXACT count of what the canonical generator will yield,
    computed analytically (``O(n_constants * domain size)`` arithmetic, no
    enumeration, no ``free_satisfies`` calls), mirroring
    ``modelfinder.find_model``'s own analytic pre-flight. This is deliberately an
    O(1)-per-size check, not a live count of the generator: a signature with few or
    no constants (where LNH cannot reduce anything — functions and predicates stay
    fully exhaustive either way) is skipped exactly as cheaply as it was before
    symmetry breaking existed, instead of paying to enumerate and call
    ``free_satisfies`` on up to ``max_candidates`` models on every size just to
    discover that a function- or predicate-dominated signature was never going to
    fit the budget. A size counts as genuinely searched (``tried_any_size = True``
    below) only if its exact canonical count is ``<= max_candidates`` (so it is
    always FULLY enumerated, never truncated mid-generator), so the honesty
    contract below is unchanged: if every size still ends up skipped, nothing was
    actually searched, and a bare ``None`` would misleadingly look like a completed
    bounded search — this raises instead (see the arity/message in the
    ValueError). With ``symmetry_breaking=False`` the search is byte-for-byte the
    original exhaustive one (the analytic pre-flight check, then
    :func:`_candidate_models`).
    """
    if policy not in ("negative", "positive", "supervaluation"):
        raise ValueError(
            f"free_logic model search: unknown policy {policy!r} "
            "(negative / positive / supervaluation).")
    closed = list(formulas)
    _refuse_numeral_constant_pair(closed, "semantics.free_logic")

    constants: set = set()
    functions: set = set()
    predicates: set = set()
    for f in closed:
        c, fn, p = _signature(f)
        constants |= c
        functions |= fn
        predicates |= p

    for name, arity in functions:
        if arity > MAX_FUNCTION_ARITY:
            raise ValueError(
                f"free_logic model search: function {name}/{arity} exceeds "
                f"MAX_FUNCTION_ARITY = {MAX_FUNCTION_ARITY}. A partial function table over "
                f"an n-element domain has (n+1)**(n**arity) entries — arity {arity} blows up "
                "too fast to enumerate at any useful domain size. Reformulate with "
                "lower-arity functions/predicates, or curry the function.")

    const_names = sorted(constants)
    func_sig = sorted(functions)
    pred_sig = sorted(predicates)

    tried_any_size = False
    for k in range(1, max_size + 1):
        domain = tuple(range(k))
        if symmetry_breaking:
            if _canonical_candidate_count(len(const_names), functions, predicates,
                                          k, domain_split) > max_candidates:
                continue
            tried_any_size = True
            for model in _canonical_candidate_models(domain, const_names, func_sig,
                                                      pred_sig, domain_split):
                if all(_satisfies(f, model, {}, policy) for f in closed):
                    return model
            continue
        if _candidate_count(len(const_names), functions, predicates, k, domain_split) > max_candidates:
            continue
        tried_any_size = True
        for model in _candidate_models(domain, const_names, func_sig, pred_sig, domain_split):
            if all(_satisfies(f, model, {}, policy) for f in closed):
                return model
    if not tried_any_size:
        raise ValueError(
            f"free_logic model search: every domain size 1..{max_size} exceeds "
            f"max_candidates = {max_candidates} for this signature "
            f"({len(const_names)} constant(s), {len(func_sig)} function(s), "
            f"{len(pred_sig)} predicate(s)). Raise max_candidates, lower max_size, or "
            "simplify the formula.")
    return None


def free_find_model(formula: Node, max_size: int = 3, *, policy: str = "negative",
                    domain_split: str = "any",
                    max_candidates: int = MAX_CANDIDATES,
                    symmetry_breaking: bool = True) -> Optional[FreeModel]:
    """Return a FreeModel satisfying ``formula``, or None.

    Mace4-style search (see
    :func:`~unicode_fol_kit.semantics.modelfinder.find_model`) over outer domain
    sizes ``1..max_size``: for each size, every existing/outer split (``domain_split``
    — ``"any"`` tries every subset including empty ``existing``; ``"total"`` forces
    ``existing == outer``), every partial constant/function assignment (a symbol may
    be non-denoting), and every predicate extension over the OUTER domain (predicates
    apply regardless of existence — see ``_atom``). ``formula``'s free variables are
    PARAMETERS (see the module docstring): each is one existing object, reported in
    ``constants`` under the variable's name, so ``P(x) ∧ ¬P(y)`` has a model and a model
    with no existing object is none for a formula with a free variable. A domain size
    whose candidate count exceeds ``max_candidates`` is skipped; a function whose
    arity exceeds :data:`MAX_FUNCTION_ARITY` is rejected outright (see :func:`_search`).
    ``None`` means "none found within the bounds", not "unsatisfiable" — free FOL is
    exactly as undecidable as classical FOL.

    ``symmetry_breaking`` (default True, roadmap C23) enumerates CONSTANT
    assignments with the LNH generator instead of exhaustively — see
    :func:`_search`'s docstring for the live-counted budget it uses instead of the
    plain pre-flight check, and
    :func:`~unicode_fol_kit.semantics.modelfinder._canonical_interpretations`'s
    docstring for why this stays sound and complete, and why FUNCTIONS are
    deliberately not also LNH-reduced.

    Raises:
        NotImplementedError: a free variable has the spelling of a constant of ``formula``.
    """
    closed, guards = _with_parameters([formula])
    return _search(closed + guards, max_size, policy, domain_split, max_candidates,
                   symmetry_breaking)


def free_countermodel(formula: Node, max_size: int = 3, *, policy: str = "negative",
                      domain_split: str = "any",
                      max_candidates: int = MAX_CANDIDATES,
                      symmetry_breaking: bool = True) -> Optional[FreeModel]:
    """Return a FreeModel where ``formula`` is FALSE (a witness against its validity), or None.

    Searches for a model of ``¬formula`` exactly like :func:`free_find_model`
    (including its ``symmetry_breaking``); the search's success check
    (``free_satisfies`` of the negation) already verifies the returned model, so a
    non-None result is a definitive refutation of validity — the same
    verify-before-return discipline as
    :func:`~unicode_fol_kit.semantics.relevant.rel_countermodel` /
    :func:`~unicode_fol_kit.semantics.conditional.cf_countermodel`.

    A free variable is a parameter (see the module docstring) that is read BEFORE the
    formula is negated: the countermodel falsifies ``formula`` under one assignment of
    existing objects, reported in ``constants`` under the variables' names. (Negating
    first would close ``¬formula`` as ``∀x ¬formula``, which an empty ``existing``
    domain satisfies for every formula.)

    Raises:
        NotImplementedError: a free variable has the spelling of a constant of ``formula``.
    """
    closed, guards = _with_parameters([formula])
    return _search([Not(closed[0])] + guards, max_size, policy, domain_split, max_candidates,
                   symmetry_breaking)


def free_is_valid(formula: Node, max_size: int = 3, *, policy: str = "negative",
                  domain_split: str = "any",
                  max_candidates: int = MAX_CANDIDATES,
                  symmetry_breaking: bool = True) -> bool:
    """Return True iff no free-logic countermodel to ``formula`` is found within the bound.

    HONEST CONTRACT (mirroring
    :func:`~unicode_fol_kit.semantics.relevant.rel_valid` /
    :func:`~unicode_fol_kit.semantics.conditional.cf_valid`): ``False`` is
    *definitive* — it is backed by an explicit, :func:`free_satisfies`-verified
    countermodel from :func:`free_countermodel`, so ``formula`` is certainly not
    valid under this free-logic semantics (for this ``policy``). ``True`` means only
    "no countermodel with outer domain size ≤ ``max_size``" — free FOL is as
    undecidable as classical FOL, so this is bounded evidence, not a proof; raising
    ``max_size`` never turns a ``False`` into a ``True``, only ever the reverse.
    """
    return free_countermodel(formula, max_size, policy=policy, domain_split=domain_split,
                             max_candidates=max_candidates,
                             symmetry_breaking=symmetry_breaking) is None


def free_entails(premises: Sequence[Node], conclusion: Node, max_size: int = 3, *,
                 policy: str = "negative", domain_split: str = "any",
                 max_candidates: int = MAX_CANDIDATES,
                 symmetry_breaking: bool = True) -> bool:
    """Return True iff no bounded FreeModel satisfies every premise but not ``conclusion``.

    Same honest contract as :func:`free_is_valid`: a ``False`` is backed by a
    verified countermodel (every premise true there, ``conclusion`` false there, under
    one assignment); ``True`` means only "none found within the bounds".
    A free variable is a PARAMETER shared by every premise and the conclusion
    (see the module docstring), as in
    :func:`~unicode_fol_kit.semantics.modelfinder.find_countermodel`: ``P(x) ⊢ P(x)`` and
    ``P(x) ⊢ ∃y P(y)`` are valid, ``P(x) ⊢ P(alpha)`` is not, and a premise is never
    closed universally. The variables are read before the conclusion is negated.

    Raises:
        NotImplementedError: a free variable has the spelling of a constant of the formulas.
    """
    closed, guards = _with_parameters(list(premises) + [conclusion])
    return _search(closed[:-1] + [Not(closed[-1])] + guards, max_size, policy, domain_split,
                   max_candidates, symmetry_breaking) is None
