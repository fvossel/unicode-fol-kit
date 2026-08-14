"""Reading a learner's answer back as a kit formula.

:func:`~unicode_fol_kit.fol.parse_prolog_clause` already turns a Prolog clause
into an AST. One step is missing before the result can be model-checked: the
**membership atom has to go**. ``atom_in(A, B)`` says "B is one of the things
in example A" — it anchors the clause to the example set and says nothing
whatever about the structure being checked. Left in, it is a predicate no
structure interprets, and evaluation raises
:class:`~unicode_fol_kit.semantics.model_eval.UninterpretedSymbol` instead of
deciding anything.

Dropping it is also where the encoding's soundness gets checked a second time,
from the other side. Two shapes are refused rather than translated:

* **A membership atom whose first argument is not the head's variable.** That
  is the learner naming a SECOND example — the clause is then a statement
  about a pair of examples, and there is no formula about one structure that
  means the same thing.
* **The head variable surviving the drop.** Same problem, found by its
  symptom rather than its shape.
* **A body goal the membership atoms never reached.** In
  ``t(A) :- n(C), atom_in(A, B), o(B).`` the goal ``n(C)`` is not connected to
  ``B`` by anything, so in Prolog it ranges over the WHOLE fact base: it
  succeeds if *any* example has a nitrogen, which makes the clause true of
  every example at once. Reading it as ``∃c N(c)`` over one structure would
  quietly turn a global claim into a local one — and a learner's clause that
  covers a negative example would come back scoring perfectly. Linkage is
  therefore required, and it propagates only through POSITIVE goals, because
  ``\\+`` binds nothing in SLDNF.

The first two are the second trap from the package docstring, caught after the
fact; the third is the third trap in disguise (an unlinked goal is effectively
0-ary — it holds globally). A task built by
:class:`~unicode_fol_kit.ilp.IlpTask` cannot produce the first two, and a
learner searching a task built by it will not usually produce the third; these
checks exist for clauses that came from somewhere else, and for the learner
that surprises you.

What is left is closed existentially: every variable of the remaining body,
including the ones the membership atom introduced. That is the right reading —
``atom_in(A, B)`` restricted ``B`` to the individuals of example ``A``, and
once the example is the structure being checked, "some individual of the
example" is exactly ``∃b`` over its domain. Top-level ``∃`` is also the right
scope for a variable under ``\\+``: linkage guarantees such a variable also
occurs in a positive goal, which is what binds it before the negation is
tested, so ``∃c (P(c) ∧ ¬Q(c))`` — and not the much weaker ``∃c ¬Q(c)`` — is
what comes back.

**Predicate names come back exactly as they went out** — if you say which
ones. The importer capitalises (``bSINGLE`` in, ``BSINGLE`` back), because
that is the kit's spelling and the right default for a clause from anywhere.
But a structure's symbols are whatever the structure calls them, so a formula
in kit spelling cannot be evaluated against one. Pass ``predicates=`` — or
call :meth:`~unicode_fol_kit.ilp.IlpTask.read_clause`, which passes the task's
own vocabulary — and the emitted spelling is restored, making the round trip
name-exact for exactly the symbols the task offered.
"""

from typing import Dict, Iterable, List, Optional, Sequence, Tuple, Union

from ..fol.nodes import (
    And, Atom, Implies, Node, Quantifier, Variable, free_variables,
)
from ..fol.prolog_input import parse_prolog_clause
from .task import IlpEncodingError

__all__ = ["clause_to_formula", "hypothesis_to_formulas"]

_FORALL = ("∀", "forall")


def _cap(name: str) -> str:
    """The kit's spelling of a Prolog functor — first character up.

    Mirrors :func:`unicode_fol_kit.fol.prolog_input._cap` rather than
    importing it, for the reason that module gives for not importing the TPTP
    importer's: the two conventions are meant to be visibly the same rule, and
    a divergence should surface as a failing round-trip test.
    """
    return name[:1].upper() + name[1:] if name else name


def _conjuncts(node: Node) -> List[Node]:
    """Flatten a top-level ``∧`` tree, left to right."""
    if isinstance(node, And):
        return _conjuncts(node.left) + _conjuncts(node.right)
    return [node]


def _conjoin(parts: List[Node]) -> Node:
    result = parts[0]
    for part in parts[1:]:
        result = And(result, part)
    return result


PredicateSpec = Union[str, Tuple[str, int]]


def _rename_map(predicates: Optional[Iterable[PredicateSpec]]
                ) -> Dict[Tuple[str, Optional[int]], str]:
    """``{(capitalised functor, arity): the structure's own spelling}``.

    Accepts bare names or ``(name, arity)`` pairs, so
    :attr:`~unicode_fol_kit.ilp.IlpTask.body_predicates` can be handed over
    unchanged; a bare name is stored under arity ``None`` and matches any
    arity. Keying by arity matters: ``P/1`` and ``p/2`` emit as the DISTINCT
    Prolog predicates ``p/1`` and ``p/2``, so a clause can say which it meant.
    Only a genuine clash — the same functor at the same arity from two
    different symbols — is refused, and
    :class:`~unicode_fol_kit.ilp.IlpTask` refuses to emit one in the first
    place.
    """
    mapping: Dict[Tuple[str, Optional[int]], str] = {}
    for entry in predicates or ():
        if isinstance(entry, (tuple, list)):
            name, arity = entry[0], int(entry[1])
        else:
            name, arity = entry, None
        key = (_cap(name), arity)
        if key in mapping and mapping[key] != name:
            raise IlpEncodingError(
                f"clause_to_formula: predicates {mapping[key]!r} and {name!r} "
                f"both arrive as {key[0]!r} at the same arity — the importer "
                "cannot tell them apart, so which one a learned clause meant "
                "is undecidable")
        mapping[key] = name
    return mapping


def _rename(node: Node, mapping: Dict[Tuple[str, Optional[int]], str]) -> Node:
    """Restore the emitted spelling of every predicate the mapping covers."""
    if isinstance(node, Atom):
        for key in ((node.predicate, len(node.args)), (node.predicate, None)):
            if key in mapping:
                node = Atom(mapping[key], node.args)
                break
    return node.map_children(lambda child: _rename(child, mapping))


def _close_existentially(formula: Node) -> Node:
    """Close every free variable, alphabetically outermost-first.

    Order among quantifiers of the same kind never changes truth, so this is
    purely so the same clause always renders the same way — the same choice
    :func:`unicode_fol_kit.fol.parse_prolog_clause` makes.
    """
    result = formula
    for variable in sorted(free_variables(formula), key=lambda v: v.name,
                           reverse=True):
        result = Quantifier("∃", variable, result)
    return result


def clause_to_formula(clause: str, *, membership: str = "atom_in",
                      predicates: Optional[Iterable[PredicateSpec]] = None,
                      negation_as_failure: str = "refuse") -> Node:
    """One learned clause → the kit formula it states about a single structure.

    Args:
        clause: a definite clause as a learner prints it, e.g.
            ``"amide(A) :- bSINGLE(C,D), bDOUBLE(D,B), n(C), atom_in(A,B)."``
            — every goal reaching the example through the membership atom, as
            a task built by :class:`~unicode_fol_kit.ilp.IlpTask` forces.
        membership: the predicate carrying the example argument — the same
            name :class:`~unicode_fol_kit.ilp.IlpTask` emitted. Matched after
            the importer's capitalisation, so ``"atom_in"`` matches the
            ``Atom_in`` the parser produces.
        predicates: the vocabulary the task offered, as names or
            ``(name, arity)`` pairs. Each is restored to that exact spelling,
            undoing the importer's capitalisation so the result can be
            evaluated against the structures it came from. Symbols not listed
            keep the kit spelling — and will then fail loudly as
            uninterpreted, which is the correct outcome for a predicate the
            task never offered.
        negation_as_failure: passed through to
            :func:`~unicode_fol_kit.fol.parse_prolog_clause`; ``"classical"``
            asserts the closed world assumption for the learner's program.

    Returns:
        The body, without membership atoms, existentially closed.

    Raises:
        ~unicode_fol_kit.ilp.IlpEncodingError: the clause is a fact (no
            body), its head is not
            ``target(Variable)``, a membership atom names a different example
            or is buried inside a disjunction or negation, nothing but
            membership atoms was there to begin with, the example variable
            survives the drop, or a goal is not linked to the example.
        ~unicode_fol_kit.fol.prolog_input.PrologParsingError: the text is
            outside the accepted Prolog fragment.

    Example:
        >>> from unicode_fol_kit.ilp import clause_to_formula
        >>> learned = "amide(A) :- n(C), bDOUBLE(C,B), atom_in(A,B)."
        >>> clause_to_formula(learned).to_unicode_str()
        '∃b ∃c (N(c) ∧ BDOUBLE(c, b))'
        >>> clause_to_formula(learned, predicates=["n", "bDOUBLE"]
        ...                   ).to_unicode_str()
        '∃b ∃c (n(c) ∧ bDOUBLE(c, b))'
    """
    node = parse_prolog_clause(clause, mode="clause",
                               negation_as_failure=negation_as_failure)
    matrix = node
    while isinstance(matrix, Quantifier) and matrix.type in _FORALL:
        matrix = matrix.formula

    head, body = _split_implication(matrix, clause)
    if not isinstance(head, Atom) or len(head.args) != 1:
        raise IlpEncodingError(
            f"clause_to_formula: the head must be target(Example) with exactly "
            f"one argument, got {head.to_unicode_str()!r}")
    example = head.args[0]
    if not isinstance(example, Variable):
        raise IlpEncodingError(
            "clause_to_formula: the head's argument must be a VARIABLE (the "
            f"example), got {example.to_unicode_str()!r} — a ground head is a "
            "fact about one example, not a rule")

    wanted = _cap(membership)
    kept: List[Node] = []
    seeds: set = set()
    dropped = 0
    for conjunct in _conjuncts(body):
        if _is_membership(conjunct, wanted):
            _check_membership(conjunct, example, membership)
            seeds |= conjunct.args[1].variables()
            dropped += 1
            continue
        buried = [a for a in conjunct.atoms() if _is_membership(a, wanted)]
        if buried:
            raise IlpEncodingError(
                f"clause_to_formula: a {membership} atom occurs inside "
                f"{conjunct.to_unicode_str()!r} rather than as a top-level "
                "condition. Dropping it there would change what the clause "
                "says, so it is refused instead.")
        kept.append(conjunct)

    if not kept:
        raise IlpEncodingError(
            f"clause_to_formula: the clause has no content besides its "
            f"{dropped} {membership} atom(s) — it says only that the example "
            "has an individual, which is true of every non-empty structure")

    remaining = _conjoin(kept)
    # Survival first, linkage second: a surviving example variable is also an
    # unlinked one, and "the example variable is still here" is the more
    # specific diagnosis of the same clause.
    if example in free_variables(remaining):
        raise IlpEncodingError(
            f"clause_to_formula: the example variable "
            f"{example.to_unicode_str()} still occurs after the {membership} "
            "atoms were dropped, so the clause is not a statement about a "
            "single structure. This is the encoding trap the ilp package "
            "exists to prevent: see unicode_fol_kit.ilp's docstring.")
    _check_linked(kept, seeds, membership)
    return _close_existentially(_rename(remaining, _rename_map(predicates)))


def _split_implication(matrix: Node, clause: str):
    """``Body → Head`` from the universally closed clause, or a clear refusal."""
    if not isinstance(matrix, Implies):
        raise IlpEncodingError(
            f"clause_to_formula: {clause.strip()!r} is a fact, not a rule — "
            "there is no body to turn into a formula")
    return matrix.right, matrix.left


def _check_linked(kept: List[Node], seeds: set, membership: str) -> None:
    """Every remaining goal must reach the example through the membership atoms.

    The reachability relation is co-occurrence in a POSITIVE goal, seeded by
    the variables the dropped membership atoms restricted. Negation and
    disjunction contribute no edges — ``\\+ q(B, C)`` binds nothing in SLDNF,
    and which branch of a disjunction binds what is branch-dependent — so a
    variable that occurs only there must already be linked by a positive goal.

    A goal with no variables at all is refused for the same reason it would
    fail: a ground goal is decided against the whole fact base, not against
    one example.
    """
    linked = set(seeds)
    positive = [c for c in kept if isinstance(c, Atom)]
    growing = True
    while growing:
        growing = False
        for atom in positive:
            variables = atom.variables()
            if variables & linked and not variables <= linked:
                linked |= variables
                growing = True

    for conjunct in kept:
        variables = conjunct.variables()
        if not variables:
            raise IlpEncodingError(
                f"clause_to_formula: the goal {conjunct.to_unicode_str()!r} "
                "has no variables, so it is decided against the whole fact "
                "base rather than against one example — it cannot be part of "
                "a formula about a single structure")
        unlinked = variables - linked
        if unlinked:
            names = ", ".join(sorted(v.name for v in unlinked))
            detail = (f"no {membership} atom is present at all"
                      if not seeds else
                      f"nothing connects {names} to the example")
            raise IlpEncodingError(
                f"clause_to_formula: the goal {conjunct.to_unicode_str()!r} "
                f"is not linked to the example — {detail}. In Prolog such a "
                "goal ranges over every example's facts at once, so it holds "
                "globally; reading it as an ∃ over one structure would turn a "
                "global claim into a local one. See unicode_fol_kit.ilp."
                "readback's docstring.")


def _is_membership(node: Node, wanted: str) -> bool:
    return (isinstance(node, Atom) and node.predicate == wanted
            and len(node.args) == 2)


def _check_membership(atom: Atom, example: Variable, membership: str) -> None:
    if atom.args[0] != example:
        raise IlpEncodingError(
            f"clause_to_formula: {atom.to_unicode_str()!r} attaches an "
            f"individual to {atom.args[0].to_unicode_str()!r}, which is not "
            f"the head's example {example.to_unicode_str()!r}. The clause "
            "names a SECOND example and joins through it, so no formula about "
            "one structure means the same thing — see unicode_fol_kit.ilp's "
            "docstring for how this arises.")


def hypothesis_to_formulas(text: str, *, membership: str = "atom_in",
                           predicates: Optional[Iterable[PredicateSpec]] = None,
                           negation_as_failure: str = "refuse",
                           target: Optional[str] = None) -> List[Node]:
    """Every clause of a learner's printed hypothesis, in order.

    Comment lines — which is what a learner's precision/recall banner looks
    like to a Prolog reader — are skipped by
    :func:`~unicode_fol_kit.fol.parse_prolog_program`'s splitter.

    The clauses come back **separately and are not disjoined**. Two clauses
    with the same head are alternatives only under the COMPLETION of the
    program, which is an assumption about the whole program rather than a fact
    about those two clauses — the same line
    :mod:`unicode_fol_kit.fol.prolog_input` draws. If the assumption holds for
    your learner, ``functools.reduce(Or, formulas)`` is the definition it
    licenses, and writing that yourself is the point.

    Args:
        target: when given, refuse any clause whose head is not this
            predicate. A learner that invented a helper predicate has produced
            a program, not a definition, and silently reading only its first
            clause would be wrong.
    """
    formulas: List[Node] = []
    for clause in _clauses_of(text):
        if target is not None:
            _check_head(clause, target, negation_as_failure)
        formulas.append(clause_to_formula(
            clause, membership=membership, predicates=predicates,
            negation_as_failure=negation_as_failure))
    return formulas


def _clauses_of(text: str) -> List[str]:
    """The clause texts, reusing the program splitter's comment handling."""
    from ..fol.prolog_input import _split_clauses

    return [c for c in _split_clauses(text) if c.strip()]


def _check_head(clause: str, target: str, negation_as_failure: str) -> None:
    # The caller's negation_as_failure has to be forwarded here too: this is a
    # SECOND parse of the same text, and parsing it under the default would
    # refuse a `\+` clause before clause_to_formula ever saw the opt-in — and
    # the refusal would tell the caller to pass the flag they just passed.
    matrix = parse_prolog_clause(clause, mode="clause",
                                 negation_as_failure=negation_as_failure)
    while isinstance(matrix, Quantifier) and matrix.type in _FORALL:
        matrix = matrix.formula
    head = matrix.right if isinstance(matrix, Implies) else matrix
    predicate = head.predicate if isinstance(head, Atom) else None
    if predicate != _cap(target):
        raise IlpEncodingError(
            f"hypothesis_to_formulas: expected every clause to define "
            f"{_cap(target)}, but {clause.strip()!r} defines {predicate!r}. A "
            "hypothesis with invented helper predicates is a program, not one "
            "definition; read it with parse_prolog_program instead.")
