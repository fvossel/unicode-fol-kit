"""Second-order finite-model semantics: Tarskian satisfaction with ∀P / ∃P.

This evaluator extends classical Tarskian satisfaction (see
:mod:`semantics.tarski`) with second-order quantification over PREDICATE
variables: ``∀P φ`` and ``∃P φ``, where ``P`` ranges over every relation of its
arity on a FINITE domain. It reuses :class:`semantics.tarski.Structure` and
:func:`semantics.tarski.term_value` unchanged; only satisfaction is re-defined,
so that a bound predicate variable can be interpreted by a transient
``pred_binding`` rather than by the structure's fixed predicate tables.

A ``pred_binding`` maps a bound predicate-variable name → its current
interpretation: a set of argument tuples (a relation on the domain). It is the
predicate-level analogue of the first-order variable ``assignment``. Both are
threaded immutably — extended into a fresh copy for each bound symbol, never
mutated in place.

Second-order quantification is interpreted by brute-force enumeration over the
powerset of ``domain ** arity`` (every relation of the right arity). This is
``2 ** (n ** k)`` relations for a domain of size ``n`` and arity ``k`` — doubly
exponential, and intended ONLY for very small finite models (a handful of
elements, arity ≤ 2). Arity 0 is the propositional/Boolean case: the two
"relations" are ``frozenset()`` (false) and ``frozenset({()})`` (true), so
``∀P``/``∃P`` over an arity-0 ``P`` quantifies over ``P``'s truth value.

Scope of the second order here: this is second-order PREDICATE (relation)
quantification only. Quantification over functions, over relations-of-relations
(third order and up), and a full higher-order type system are OUT OF SCOPE; the
lambda layer (:class:`fol.nodes.Lambda` / ``Application``) already supplies
higher-order TERMS and is intentionally rejected by this evaluator — beta-reduce
and lambda-eliminate first. Łukasiewicz (fuzzy) and modal nodes are likewise
rejected: use the fuzzy / Kripke evaluators.

A free OBJECT variable of a formula handed to a search function (:func:`so_find_model`,
:func:`so_find_countermodel`, :func:`so_is_satisfiable_finite`, :func:`so_is_valid_finite`)
is a PARAMETER: one unknown element, a constant of its own name that every candidate
structure interprets (see :func:`_so_sentence`). It is never closed universally, so
``P(x) ∧ ¬P(y)`` is satisfiable, and the structure a search returns reports the element as
``constants['x']``. The evaluators :func:`satisfies_so` and :func:`holds` take the
assignment from the caller and close nothing.

The four search functions answer for every domain size ``1 .. max_size`` or they raise. A
size whose number of candidate interpretations of the free symbols exceeds ``max_candidates``
is NOT skipped: a search that has found no structure at the smaller sizes raises
:class:`CandidateBoundExceeded` on reaching it (the size, the number, and the two ways out:
raise ``max_candidates`` or lower ``max_size``), because "valid" or "no model" for
``max_size`` would otherwise be said about sizes nobody looked at. A structure found at a
smaller size is returned as before. A many-sorted formula is searched by the one-universe
reading of :mod:`~unicode_logic_kit.semantics.modelfinder`: one domain, each sort a non-empty
subset of it, ``c:S`` an element of ``S``, a sort and the unary predicate of its name one
symbol; the second-order quantifiers range over every relation on the whole domain. A
predicate name is a free symbol of the structure wherever no second-order quantifier of that
name encloses it, so ``¬P(a) ∧ ∃P P(a)`` is about the structure's own ``P`` in its first
conjunct and a bound one in its second.
"""

from itertools import product
from typing import Any, FrozenSet, Iterable, Mapping, Optional, Tuple

from ..fol._free_parameters import parameterize
from ..fol.nodes import (
    Node,
    Atom, Not, And, Or, Xor, Implies, Iff, Quantifier,
    SortedQuantifier,
    SecondOrderQuantifier,
)
from .tarski import (
    Structure, term_value, _atom_value, _extend,
    _FORALL, _EXISTS, _FUZZY_TYPES, _LAMBDA_TYPES, _refuse_cardinality_as_individual,
)

# A relation interpretation for a bound predicate variable: a (frozen)set of
# argument tuples of domain individuals. Mapping name -> relation.
Relation = FrozenSet[Tuple[Any, ...]]
PredBinding = Mapping[str, Relation]

# Safety cap for second-order enumeration. A ∀P/∃P over an arity-k predicate on
# an n-element domain ranges over 2 ** (n ** k) relations. Past this many the
# enumeration cannot finish in practice, so it raises a clear error instead of
# hanging. Raise this module attribute if you really mean to enumerate more.
MAX_RELATIONS = 1 << 22  # ~4.2 million


def satisfies_so(
    formula: Node,
    structure: Structure,
    assignment: Optional[Mapping[str, Any]] = None,
    pred_binding: Optional[PredBinding] = None,
) -> bool:
    """Return whether ``structure`` satisfies ``formula`` (second-order Tarski).

    ``assignment`` maps object-variable names to individuals (as in
    :func:`semantics.tarski.satisfies`); ``pred_binding`` maps a *bound*
    predicate-variable name to its current relation (a set of argument tuples).
    Both default to empty and are threaded immutably.

    Recursion:

    - **Atom** ``A(t1..tk)``: if ``A`` is currently bound (``A in pred_binding``),
      it is true iff the tuple of evaluated term values is in ``pred_binding[A]``
      (an arity-0 bound ``A`` is true iff ``() in pred_binding[A]``). Otherwise
      satisfaction falls back to the structure exactly as
      :func:`semantics.tarski.satisfies` does — including ``=`` as identity and
      ``≠`` as non-identity.
    - **Not/And/Or/Xor/Implies/Iff**: the classical truth tables.
    - **Quantifier / SortedQuantifier** (object-level): range over the domain
      (or the named sort), threading the same ``pred_binding``.
    - **SecondOrderQuantifier** ``∀P/k φ`` / ``∃P/k φ``: range ``P`` over every
      relation ``R ⊆ domain ** k`` (the powerset of all ``k``-tuples). ``∀``
      holds iff ``φ`` holds for all such ``R``; ``∃`` iff for some. See the
      module docstring for the ``2 ** (n ** k)`` complexity.

    Raises:
        ValueError: on a Łukasiewicz node (use the fuzzy evaluator), an unknown
            quantifier type / node type, or when a ``∀P`` / ``∃P`` would enumerate
            more than :data:`MAX_RELATIONS` relations (a clear error instead of a
            hang — see the module docstring for the ``2 ** (n ** k)`` cost).
        NotImplementedError: on a lambda or modal node — these are out of scope
            for second-order predicate semantics (lambda: beta-reduce and
            lambda-eliminate first).
    """
    if assignment is None:
        assignment = {}
    if pred_binding is None:
        pred_binding = {}

    if isinstance(formula, Atom):
        return _so_atom_value(formula, structure, assignment, pred_binding)

    if isinstance(formula, Not):
        return not satisfies_so(formula.formula, structure, assignment, pred_binding)

    if isinstance(formula, And):
        return (satisfies_so(formula.left, structure, assignment, pred_binding)
                and satisfies_so(formula.right, structure, assignment, pred_binding))

    if isinstance(formula, Or):
        return (satisfies_so(formula.left, structure, assignment, pred_binding)
                or satisfies_so(formula.right, structure, assignment, pred_binding))

    if isinstance(formula, Xor):
        return (satisfies_so(formula.left, structure, assignment, pred_binding)
                != satisfies_so(formula.right, structure, assignment, pred_binding))

    if isinstance(formula, Implies):
        return ((not satisfies_so(formula.left, structure, assignment, pred_binding))
                or satisfies_so(formula.right, structure, assignment, pred_binding))

    if isinstance(formula, Iff):
        return (satisfies_so(formula.left, structure, assignment, pred_binding)
                == satisfies_so(formula.right, structure, assignment, pred_binding))

    if isinstance(formula, Quantifier):
        return _eval_object_quantifier(
            formula.type, formula.variable.name, structure.domain,
            formula.formula, structure, assignment, pred_binding,
        )

    if isinstance(formula, SortedQuantifier):
        universe = structure.sort_universe(formula.sort)
        return _eval_object_quantifier(
            formula.type, formula.variable.name, universe,
            formula.formula, structure, assignment, pred_binding,
        )

    if isinstance(formula, SecondOrderQuantifier):
        return _eval_second_order_quantifier(
            formula, structure, assignment, pred_binding,
        )

    if isinstance(formula, _FUZZY_TYPES):
        raise ValueError(
            f"Cannot evaluate Łukasiewicz node {type(formula).__name__} with the "
            "two-valued second-order evaluator; use the fuzzy evaluator instead."
        )

    if isinstance(formula, _LAMBDA_TYPES):
        raise NotImplementedError(
            f"Lambda node {type(formula).__name__} is out of scope for the "
            "second-order evaluator (it handles second-order PREDICATE "
            "quantification, not higher-order terms); beta-reduce and "
            "lambda-eliminate the formula first."
        )

    # Modal nodes (Box / Diamond) live in the modal AST and have no class here;
    # they fall through to this generic rejection alongside any other unknown
    # node type. Modal formulas need the Kripke evaluator.
    if type(formula).__name__ in ("Box", "Diamond"):
        raise NotImplementedError(
            f"Modal node {type(formula).__name__} is out of scope for the "
            "second-order evaluator; use the Kripke (modal) evaluator instead."
        )

    raise ValueError(
        f"satisfies_so: unsupported node type {type(formula).__name__}."
    )


def _so_atom_value(
    atom: Atom,
    structure: Structure,
    assignment: Mapping[str, Any],
    pred_binding: PredBinding,
) -> bool:
    """Truth value of an atom, consulting ``pred_binding`` for bound predicates.

    If the atom's predicate name is currently bound to a relation, the atom is
    true iff the tuple of evaluated argument values is in that relation. (For an
    arity-0 bound predicate the relevant tuple is the empty tuple ``()``.)
    Otherwise satisfaction is delegated to the first-order
    :func:`semantics.tarski._atom_value`, which handles ``=`` / ``≠`` and the
    structure's predicate tables. The ``=`` / ``≠`` builtins are never treated
    as bindable predicate variables.
    """
    if atom.predicate in pred_binding and atom.predicate not in ("=", "≠"):
        relation = pred_binding[atom.predicate]
        values = tuple(
            term_value(a, structure, assignment) for a in atom.args
        )
        return values in relation
    return _atom_value(atom, structure, assignment)


def _eval_object_quantifier(
    qtype: str,
    var_name: str,
    universe: Iterable[Any],
    body: Node,
    structure: Structure,
    assignment: Mapping[str, Any],
    pred_binding: PredBinding,
) -> bool:
    """Evaluate an object-level ∀/∃ over a universe, threading ``pred_binding``.

    Mirrors :func:`semantics.tarski._eval_quantifier` but recurses through
    :func:`satisfies_so` so the predicate binding survives object quantifiers.
    """
    if qtype in _FORALL:
        return all(
            satisfies_so(body, structure, _extend(assignment, var_name, d), pred_binding)
            for d in universe
        )
    if qtype in _EXISTS:
        return any(
            satisfies_so(body, structure, _extend(assignment, var_name, d), pred_binding)
            for d in universe
        )
    raise ValueError(f"Unknown quantifier type: {qtype!r}")


def _all_relations(domain: Tuple[Any, ...], arity: int) -> Iterable[Relation]:
    """Yield every relation R ⊆ domain ** arity (the powerset of all arity-tuples).

    The base set is all ``arity``-tuples of domain elements (``len ==
    n ** arity``); a relation is any subset of it, so there are ``2 ** (n **
    arity)`` of them. For ``arity == 0`` the base set is the single empty tuple
    ``{()}``, giving exactly two relations — ``frozenset()`` (Boolean false) and
    ``frozenset({()})`` (Boolean true).

    Each subset is yielded as a ``frozenset`` so it is hashable and immutable.
    """
    base = list(product(domain, repeat=arity))
    # Enumerate subsets via the bitmask 0 .. 2**len(base) - 1.
    for mask in range(1 << len(base)):
        subset = frozenset(
            base[i] for i in range(len(base)) if (mask >> i) & 1
        )
        yield subset


def _eval_second_order_quantifier(
    node: SecondOrderQuantifier,
    structure: Structure,
    assignment: Mapping[str, Any],
    pred_binding: PredBinding,
) -> bool:
    """Evaluate ∀P/k or ∃P/k by enumerating every relation R ⊆ domain ** k.

    The bound predicate name is interpreted, in turn, by each candidate relation
    added to a *copy* of ``pred_binding`` (shadowing any outer binding of the
    same name). ``∀`` holds iff the body holds under every candidate; ``∃`` iff
    under some. See the module docstring for the doubly-exponential cost.

    Raises ValueError if the 2 ** (n ** k) relation count exceeds
    :data:`MAX_RELATIONS`, rather than enumerating a hopelessly large space.
    """
    num_tuples = len(structure.domain) ** node.arity
    num_relations = 1 << num_tuples  # 2 ** (n ** k)
    if num_relations > MAX_RELATIONS:
        raise ValueError(
            f"Second-order quantifier {node.type}{node.predicate}/{node.arity} "
            f"over a {len(structure.domain)}-element domain would enumerate "
            f"2 ** ({len(structure.domain)} ** {node.arity}) = 2 ** {num_tuples} "
            f"relations, above MAX_RELATIONS = {MAX_RELATIONS}. Shrink the domain "
            "or the arity (or raise secondorder.MAX_RELATIONS)."
        )
    relations = _all_relations(structure.domain, node.arity)
    if node.type in _FORALL:
        return all(
            satisfies_so(
                node.formula, structure, assignment,
                _extend(pred_binding, node.predicate, relation),
            )
            for relation in relations
        )
    if node.type in _EXISTS:
        return any(
            satisfies_so(
                node.formula, structure, assignment,
                _extend(pred_binding, node.predicate, relation),
            )
            for relation in relations
        )
    raise ValueError(
        f"Unknown second-order quantifier type: {node.type!r}"
    )


def holds(formula: Node, structure: Structure, fast: bool = False) -> bool:
    """Convenience: ``satisfies_so(formula, structure, {}, {})`` for a sentence.

    Reads as "structure satisfies the (closed) second-order formula": the empty
    object assignment and empty predicate binding are appropriate when the
    formula has no free object or predicate variables.

    Args:
        fast: opt-in (default ``False``, which keeps every existing call's
            behaviour byte-identical); when ``True``, checks via
            :func:`~unicode_logic_kit.semantics.asp_models.asp_holds_so`
            instead — ASP-grounded (clingo propagation prunes the search
            instead of this module's brute-force ``2 ** (n ** k)``
            enumeration; see that function's docstring) but restricted to
            second-order sentences whose ``SecondOrderQuantifier``
            occurrences form a single, same-polarity block (roadmap C24). A
            ``formula`` outside that fragment raises ``ValueError`` naming
            the offending construct (never a silent fallback to the
            brute-force reading above); a missing ``clingo`` install (the
            optional ``asp`` extra) raises too.
    """
    if fast:
        from .asp_models import asp_holds_so
        return asp_holds_so(formula, structure)
    return satisfies_so(formula, structure, {}, {})


# ---------------------------------------------------------------------------
# Bounded second-order validity / (counter)model search
# ---------------------------------------------------------------------------
#
# Second-order logic has no complete proof system and SO validity is not even
# semi-decidable, so this is a *bounded finite-model* search (the SO analogue of
# semantics.modelfinder): it enumerates finite structures interpreting the FREE
# symbols — the SO-quantified predicates are NOT interpreted by the structure, the
# satisfies_so evaluator ranges them over every relation — and evaluates the SO
# sentence in each. A found model/counter-model is genuine; "none up to size N" is
# bounded evidence, not a proof. The free-symbol enumeration (_so_structures below)
# uses modelfinder's LNH symmetry-breaking generator (roadmap C23), so a
# constant-heavy free signature is searched without the k! relabeling redundancy —
# see _so_structures's docstring.


def _so_bound_predicate_names(formula: Node) -> set:
    """Names bound by a second-order quantifier anywhere in ``formula``."""
    return {n.predicate for n in formula.walk()
            if isinstance(n, SecondOrderQuantifier)}


def _so_free_predicates(node: Node, bound: FrozenSet[str] = frozenset()) -> set:
    """The ``(name, arity)`` of every atom of ``node`` whose predicate no enclosing
    second-order quantifier binds: the predicates a structure has to interpret.

    A name that a quantifier binds is a bound variable only inside that quantifier's scope,
    so ``P(a) ∧ ∃P ¬P(a)`` has the free predicate ``P`` (its first conjunct) and a bound one.
    """
    if isinstance(node, SecondOrderQuantifier):
        return _so_free_predicates(node.formula, bound | {node.predicate})
    found: set = set()
    if isinstance(node, Atom) and node.predicate not in bound:
        found.add((node.predicate, len(node.args)))
    for child in node._child_nodes():
        found |= _so_free_predicates(child, bound)
    return found


def _so_signature(sentence: Node):
    """The structure signature of ``sentence`` minus its SO-bound predicates.

    A predicate is left out only where a second-order quantifier binds it: an occurrence of the
    same name outside every such quantifier is a free predicate, which a structure interprets.

    Raises:
        NotImplementedError: a bound predicate variable has the name of a sort of ``sentence``
            (a sort and the unary predicate of its name are one symbol, and a quantifier cannot
            rebind half of it).
    """
    from .modelfinder import _Signature
    bound = _so_bound_predicate_names(sentence)
    sig = _Signature()
    sig.scan(sentence)
    clash = sorted(bound & sig.sorts)
    if clash:
        raise NotImplementedError(
            f"semantics.secondorder: the predicate variable {clash[0]!r} that a second-order "
            f"quantifier binds has the name of a sort of the formula. A sort and the unary "
            f"predicate of its name are ONE symbol, so a quantifier over it would rebind "
            f"the predicate but not the sort; rename the bound predicate variable.")
    free = _so_free_predicates(sentence)
    sig.predicates = {(name, ar) for (name, ar) in sig.predicates if (name, ar) in free}
    return sig


def _describe_symbols(sig) -> str:
    """The symbols of ``sig`` as the user wrote them (``c``, ``f/1``, ``T/3``, sort ``S``)."""
    parts = sorted(sig.constants)
    parts += [f"{name}/{arity}" for name, arity in sorted(sig.functions)]
    parts += [f"{name}/{arity}" for name, arity in sorted(sig.predicates)]
    parts += [f"sort {name}" for name in sorted(sig.sorts)]
    return ", ".join(parts) if parts else "none"


class CandidateBoundExceeded(ValueError):
    """A bounded second-order search reached a domain size it does not enumerate.

    :func:`so_find_model`, :func:`so_find_countermodel`, :func:`so_is_satisfiable_finite` and
    :func:`so_is_valid_finite` answer "no model" (or "valid") for the domain sizes
    ``1 .. max_size``, which is only true if every one of them was searched. A size whose
    number of candidate interpretations of the free symbols exceeds ``max_candidates`` is not
    searched, and an answer that leaves it out would be an answer about structures the search
    never looked at; so the search raises this error when it reaches such a size without
    having found a structure. A structure found at a smaller size is returned as before, since
    it is a witness whatever the larger sizes hold.

    The instance carries ``size`` (the first size that was not searched), ``candidates`` (how
    many interpretations of the free symbols it has: an upper bound for a many-sorted formula)
    and ``max_candidates`` (the bound that was exceeded). The message names the two ways out:
    raise ``max_candidates``, or lower ``max_size`` below ``size``.
    """

    size: int = 0
    candidates: int = 0
    max_candidates: int = 0


def _bound_exceeded(where: str, sig, size: int, candidates: int,
                    max_candidates: int) -> CandidateBoundExceeded:
    """The :class:`CandidateBoundExceeded` that the search ``where`` raises at ``size``."""
    way_out = (f"lower max_size to {size - 1}, which asks only about the sizes that were searched"
               if size > 1 else "there is no smaller size to ask about")
    error = CandidateBoundExceeded(
        f"{where}: domain size {size} has {'at most ' if sig.sorts else ''}{candidates} "
        f"candidate interpretations of the free symbols ({_describe_symbols(sig)}), more than "
        f"max_candidates = {max_candidates}, so that size is not searched and the search gives "
        f"no answer for it (leaving it out would report 'no model' or 'valid' for structures "
        f"never looked at). Either raise max_candidates to at least {candidates}, or {way_out}.")
    error.size = size
    error.candidates = candidates
    error.max_candidates = max_candidates
    return error


def _so_structures(sentence: Node, max_size: int, max_candidates: int,
                   where: str = "semantics.secondorder"):
    """Yield every candidate :class:`Structure` over domains ``1 .. max_size``.

    A size is searched completely or the generator raises :class:`CandidateBoundExceeded` on
    reaching it: it never skips a size and goes on to the next one. What it has yielded before
    the raise is complete for the smaller sizes.

    Enumerates the FREE-symbol part with :func:`modelfinder._canonical_interpretations`
    (roadmap C23) instead of the plain :func:`modelfinder._interpretations`, so
    ``so_find_model``/``so_find_countermodel`` inherit the LNH symmetry-breaking
    reduction on constant assignments for free — no separate implementation needed
    here (functions and predicates, including the SO-quantified ones
    ``satisfies_so`` ranges over, stay exhaustive exactly as before; see that
    generator's docstring for the full soundness argument and why functions are
    NOT LNH-reduced). The number of candidates of a size is the EXACT count the canonical
    generator yields (:func:`modelfinder._canonical_candidate_count`), so a size is refused
    only when it really has more than ``max_candidates`` structures.

    A formula with sorts is enumerated with :func:`modelfinder._sorted_interpretations`, which
    is the one-universe reading of the model finder: ONE domain, each sort a non-empty subset of
    it (overlapping freely), a sorted constant ``c:S`` an element of ``S``, a sort and the unary
    predicate of its name one symbol, every other symbol over the whole domain. That search has
    no symmetry breaking, and its candidate count is the upper bound
    :func:`modelfinder._candidate_count`.

    ``where`` names the public function the caller is, for the message of the raise.
    """
    from .modelfinder import (
        _canonical_candidate_count, _canonical_interpretations, _candidate_count,
        _sorted_interpretations,
    )
    sig = _so_signature(sentence)
    for k in range(1, max_size + 1):
        candidates = _candidate_count(sig, k) if sig.sorts else _canonical_candidate_count(sig, k)
        if candidates > max_candidates:
            raise _bound_exceeded(where, sig, k, candidates, max_candidates)
        domain = tuple(range(k))
        if sig.sorts:
            for constants, functions, predicates, sorts in _sorted_interpretations(sig, domain):
                yield Structure(domain, constants=constants, functions=functions,
                                predicates=predicates, sorts=sorts)
        else:
            for constants, functions, predicates in _canonical_interpretations(sig, domain):
                yield Structure(domain, constants=constants,
                                functions=functions, predicates=predicates)


def _so_sentence(formula: Node) -> Node:
    """``formula`` with every free object variable read as a PARAMETER.

    A free variable is one unknown element (the assignment-wise reading of the other
    finite-model routes: a structure AND an assignment satisfy ``φ(x)`` iff the
    structure satisfies ``φ(c)`` with ``x`` ↦ ``c``): it is replaced by a constant of its
    own name (:func:`~unicode_logic_kit.fol._free_parameters.parameterize`), which every
    structure of the search interprets and which a returned structure reports as
    ``constants['x']``. The formula is never closed universally, so ``P(x) ∧ ¬P(y)`` has a
    model (``x`` and ``y`` are two elements), and validity is still validity under every
    assignment.

    Raises:
        NotImplementedError: a free variable has the spelling of a constant of ``formula``
            (a structure holds one entry per name), or a cardinality term ``|{v : φ}|`` is not
            an operand of a comparison with a number (a natural number is no element of the
            domain; see :func:`~unicode_logic_kit.semantics.tarski.satisfies`).
    """
    sentence = parameterize([formula], after_variables=True)[0][0]
    _refuse_cardinality_as_individual([sentence], "semantics.secondorder")
    return sentence


def _first_structure(formula: Node, max_size: int, max_candidates: int, fast: bool,
                     satisfying: bool, where: str) -> Optional[Structure]:
    """The first candidate structure, smallest domain first, in which ``formula`` is true
    (``satisfying=True``) or false (``satisfying=False``); ``None`` when every size up to
    ``max_size`` was searched and none is such a structure.

    Raises:
        NotImplementedError: see :func:`_so_sentence`, and :func:`_so_signature`.
        ~unicode_logic_kit.semantics.secondorder.CandidateBoundExceeded:
            a size up to ``max_size`` has more candidates than ``max_candidates`` and no
            structure was found at a smaller size.
    """
    sentence = _so_sentence(formula)
    for structure in _so_structures(sentence, max_size, max_candidates, where):
        if bool(holds(sentence, structure, fast=fast)) == satisfying:
            return structure
    return None


def so_find_model(formula: Node, max_size: int = 3,
                  max_candidates: int = MAX_RELATIONS, fast: bool = False) -> Optional[Structure]:
    """Return a finite structure in which the SO ``formula`` holds, or None (bounded).

    ``None`` means that every domain size ``1 .. max_size`` was searched and none has a model.
    A size with more than ``max_candidates`` candidate interpretations of the free symbols is
    not skipped: the search raises instead (see below). A free object variable is a PARAMETER
    (:func:`_so_sentence`): the structure holds when some assignment satisfies ``formula``, and
    it reports that assignment as the constant of the variable's own name. A formula with
    sorts is read by the one-universe reading of
    :mod:`~unicode_logic_kit.semantics.modelfinder`: the returned structure carries ``sorts``,
    each a non-empty subset of the one domain, and ``∀x:S`` / ``∃x:S`` range over it.

    ``fast`` is passed straight through to :func:`holds` for each candidate
    structure — see that function's ``fast`` parameter (opt-in, default
    ``False`` keeps this byte-identical to before). With ``fast=True`` a sorted quantifier or
    sorted constant INSIDE the scope of a second-order quantifier is refused by a
    ``ValueError`` that names it (the ASP encoding reads unsorted formulas only); outside
    every second-order quantifier a sort is evaluated as with ``fast=False``.

    Raises:
        NotImplementedError: a free variable has the spelling of a constant of ``formula``, a
            cardinality term is used as an individual (see :func:`_so_sentence`), or a bound
            predicate variable has the name of one of the sorts of ``formula``.
        ~unicode_logic_kit.semantics.secondorder.CandidateBoundExceeded:
            a domain size up to ``max_size`` has more than ``max_candidates`` candidate
            interpretations and no model was found at a smaller size. Raise ``max_candidates`` or
            lower ``max_size``; the message gives the size and the number.
    """
    return _first_structure(formula, max_size, max_candidates, fast, True, "so_find_model")


def so_find_countermodel(formula: Node, max_size: int = 3,
                         max_candidates: int = MAX_RELATIONS, fast: bool = False) -> Optional[Structure]:
    """Return a finite structure in which the SO ``formula`` FAILS, or None (bounded).

    A returned structure witnesses that ``formula`` is not second-order valid. A free
    object variable is a PARAMETER (:func:`_so_sentence`): the structure reports the
    assignment that falsifies ``formula`` as the constant of the variable's own name.
    For a formula on its own this is the same verdict as the universal closure gives
    (``φ`` holds under every assignment iff ``∀x φ`` holds); it is the reading of the
    satisfiability routes, so a returned structure is a model of ``¬formula`` there too.

    ``None`` means that every domain size ``1 .. max_size`` was searched and none has a
    countermodel: a size with more than ``max_candidates`` candidate interpretations of the
    free symbols is not skipped, the search raises instead. A formula with sorts is read by the
    one-universe reading of :mod:`~unicode_logic_kit.semantics.modelfinder` (see
    :func:`so_find_model`).

    ``fast`` is passed straight through to :func:`holds` for each candidate
    structure — see that function's ``fast`` parameter (opt-in, default
    ``False`` keeps this byte-identical to before).

    Raises:
        NotImplementedError: see :func:`so_find_model`.
        ~unicode_logic_kit.semantics.secondorder.CandidateBoundExceeded:
            a domain size up to ``max_size`` has more than ``max_candidates`` candidate
            interpretations and no countermodel was found at a smaller size.
    """
    return _first_structure(formula, max_size, max_candidates, fast, False, "so_find_countermodel")


def so_is_satisfiable_finite(formula: Node, max_size: int = 3,
                             max_candidates: int = MAX_RELATIONS, fast: bool = False) -> bool:
    """True iff the SO ``formula`` has a finite model of size ≤ ``max_size`` (bounded).

    ``False`` means that every size ``1 .. max_size`` was searched and has no model; a size
    that cannot be searched within ``max_candidates`` raises (see :func:`so_find_model`).

    ``fast``: see :func:`holds`'s parameter of the same name (opt-in, default
    ``False`` keeps this byte-identical to before).

    Raises:
        NotImplementedError: see :func:`so_find_model`.
        ~unicode_logic_kit.semantics.secondorder.CandidateBoundExceeded:
            a domain size up to ``max_size`` has more than ``max_candidates`` candidate
            interpretations and no model was found at a smaller size.
    """
    return _first_structure(formula, max_size, max_candidates, fast, True,
                            "so_is_satisfiable_finite") is not None


def so_is_valid_finite(formula: Node, max_size: int = 3,
                       max_candidates: int = MAX_RELATIONS, fast: bool = False) -> bool:
    """True iff no finite counter-model of the SO ``formula`` is found up to ``max_size``.

    Bounded and one-sided: ``True`` is strong evidence of second-order validity (not a
    proof — SO validity is not semi-decidable) and means that EVERY domain size
    ``1 .. max_size`` was searched; ``False`` is a genuine refutation, with
    the witness available from :func:`so_find_countermodel`. A size with more than
    ``max_candidates`` candidate interpretations of the free symbols is never left out to
    answer ``True`` for the rest: the call raises instead.

    ``fast``: see :func:`holds`'s parameter of the same name (opt-in, default
    ``False`` keeps this byte-identical to before) — each candidate structure
    is then checked via
    :func:`~unicode_logic_kit.semantics.asp_models.asp_holds_so` instead of the
    brute-force :func:`satisfies_so`, restricted to the single-block SO
    fragment that function accepts.

    Raises:
        NotImplementedError: see :func:`so_find_model`.
        ~unicode_logic_kit.semantics.secondorder.CandidateBoundExceeded:
            a domain size up to ``max_size`` has more than ``max_candidates`` candidate
            interpretations and no countermodel was found at a smaller size.
    """
    return _first_structure(formula, max_size, max_candidates, fast, False,
                            "so_is_valid_finite") is None
