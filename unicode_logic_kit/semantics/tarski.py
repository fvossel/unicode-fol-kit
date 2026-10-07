"""Classical (two-valued) Tarskian model theory for FOL and MSFOL.

A :class:`Structure` is a first-order "world": a non-empty domain of
individuals together with interpretations of the constant, function, and
predicate symbols (and, for MSFOL, the named sorts). :func:`satisfies`
computes the truth value of a formula in such a structure under a variable
assignment, following Tarski's recursive definition of satisfaction.

Only the classical fragment is interpreted here. Łukasiewicz (fuzzy) operators
and lambda nodes are rejected with a clear error: the former need the
many-valued evaluator, the latter must be beta-reduced / lambda-eliminated
first.

Functional style: the variable assignment dict is never mutated. When a
quantifier ranges over the domain, the binding is added to a *copy* of the
assignment for each candidate individual.

**What a many-sorted structure is.** There is ONE domain. A sort ``S`` is a
non-empty subset of it, and sorts may overlap. The sort ``S`` and the unary
predicate ``S`` are ONE symbol: an atom ``S(t)`` holds exactly when the value of
``t`` is in the sort (a structure that names ``S`` only as a sort needs no
second table for the predicate, and one that gives both must give them the same
extension). A sorted constant ``c:S`` denotes an element of ``S``. An unsorted
constant, an unsorted variable and the value of a function may be any element of
the domain; a predicate is a relation over the whole domain. A structure that
breaks one of these laws is not a structure of the definition, and evaluating a
formula in it is an :class:`IllegalStructureError` naming the law, not a truth
value: a truth value in such a structure answers a question nobody asked. The
checks run where the evaluator reads the thing they are about (a sort when it is
read, a sorted constant when it is evaluated); :func:`check_structure` runs all
of them at once, up front.
"""

import html
import operator
from typing import Any, Callable, Dict, Iterable, List, Mapping, Optional, Set, Tuple, Union

from ..fol.nodes import (
    Node,
    Variable, Constant, Number, Function,
    Atom, Not, And, Or, Xor, Implies, Iff, Quantifier,
    SortedQuantifier, SortedConstant,
    Count, Cardinality, SortedCount, SortedCardinality, Measure,
    LukNegation, WeakConjunction, WeakDisjunction,
    StrongConjunction, StrongDisjunction,
    LukImplication, LukEquivalence,
    LambdaVar, Lambda, Application,
)
from ..fol._fol_nodes import numeral_key
from ..fol._numeral_symbols import term_numerals
from ..fol._tptp_symbols import is_tptp_boolean_atom as _is_tptp_boolean_atom
from ..fol._tptp_symbols import truth_constant_word as _truth_constant_word

# Quantifier.type spellings accepted for each quantifier kind.
_FORALL = ("∀", "forall")
_EXISTS = ("∃", "exists")

#: The function symbol a :class:`Measure` term denotes. Matches ``Measure.to_z3`` and
#: ``Measure.to_prover9``, so a structure found here interprets the same symbol the
#: provers see.
_MEASURE_FUNC = ("measure", 2)

# Infix comparison predicates that are NOT equality/disequality. Their
# extensions live in Structure.predicates like any ordinary relation.
_ORDER_COMPARISONS = frozenset({"<", ">", "≤", "≥"})

#: Numeric readings of the order comparisons (see :func:`_order_value`).
_ORDER_OPS = {
    "<": operator.lt, ">": operator.gt, "≤": operator.le, "≥": operator.ge,
}

# Łukasiewicz node types: two-valued Tarski cannot interpret them.
_FUZZY_TYPES = (
    LukNegation, WeakConjunction, WeakDisjunction,
    StrongConjunction, StrongDisjunction,
    LukImplication, LukEquivalence,
)

# Lambda-calculus node types: must be eliminated before evaluation.
_LAMBDA_TYPES = (LambdaVar, Lambda, Application)


class IllegalStructureError(ValueError):
    """A :class:`Structure` that is not a structure of the many-sorted definition.

    Raised instead of a truth value when a formula is evaluated in a structure
    that breaks one of the laws in the module docstring: a sort that is empty or
    holds an element outside the domain, a name that is a sort and a unary
    predicate with two different extensions, or a sorted constant whose value is
    not in its sort. The message names the law and the symbols that break it.

    It is also raised when a :class:`Structure` is BUILT with a table keyed in a shape
    the evaluator never reads (see :class:`Structure`): such a table would be dropped
    without a word and its symbol would denote the empty relation.
    """


def _first_length(table: Any) -> Optional[int]:
    """The one length shared by every argument tuple in ``table``, if it has one.

    ``table`` is the extension of a predicate (a container of argument tuples) or the
    table of a function (a mapping from argument tuples); ``None`` when it is
    empty, a callable or has tuples of different lengths (a bool is a nullary
    predicate's value, whose tuple has length 0).
    """
    if isinstance(table, bool):
        return 0
    try:
        lengths = {len(row) for row in table}
    except TypeError:
        return None
    return lengths.pop() if len(lengths) == 1 else None


def _table_key_problems(constants: Mapping[Any, Any], functions: Mapping[Any, Any],
                        predicates: Mapping[Any, Any], sorts: Mapping[Any, Any]) -> List[str]:
    """Every table key of a structure that the evaluator would never read.

    A function or predicate table is read under ``(name, arity)`` (``name`` a ``str``,
    ``arity`` a non-negative ``int``); a constant and a sort are read under their name, a
    ``str``. A table under any other key is not an extension of anything: it is dropped,
    and the symbol it was meant for denotes the empty relation (a predicate) or has no
    value (a function). One line per offending key, naming the table, the key and what
    to write instead.
    """
    problems: List[str] = []
    for table_name, table, consequence in (
            ("functions", functions, "the function would have no value"),
            ("predicates", predicates, "the predicate would denote the empty relation")):
        for key, value in table.items():
            if (isinstance(key, tuple) and len(key) == 2 and isinstance(key[0], str)
                    and isinstance(key[1], int) and not isinstance(key[1], bool) and key[1] >= 0):
                continue
            if isinstance(key, str):
                length = _first_length(value)
                arity = "arity" if length is None else str(length)
                problems.append(
                    f"{table_name}[{key!r}] is keyed by the bare name, but a table is read "
                    f"under (name, arity); this one would never be read and {consequence}. "
                    f"Write the key as ({key!r}, {arity})")
            else:
                problems.append(
                    f"{table_name}[{key!r}] is not keyed by (name, arity), a pair of a str "
                    f"and a non-negative int, so it would never be read and {consequence}")
    for table_name, table in (("constants", constants), ("sorts", sorts)):
        for key in table:
            if not isinstance(key, str):
                problems.append(
                    f"{table_name}[{key!r}] is not keyed by a name (a str), so it would "
                    f"never be read")
    return problems


class Structure:
    """A first-order structure (model / "world") over a non-empty domain.

    Args:
        domain: a non-empty iterable of individuals (any hashable Python
            values, e.g. ``{"alice", "bob"}`` or ``{0, 1}``). Stored as a
            tuple preserving order; duplicates are dropped.
        constants: maps a constant NAME (str) to an individual in the domain.
            Interprets both :class:`Constant` and :class:`SortedConstant`.
            :class:`Number` ``n`` defaults to the individual ``n`` unless the
            name of its VALUE is overridden here (``"1"`` for ``1`` and for
            ``1.0``, ``"2.5"`` for ``2.5``: one constant per value, see
            :func:`~unicode_logic_kit.fol._fol_nodes.numeral_key`) — except where ``n``
            is compared with a cardinality, which always reads it as the numeral
            itself.
        functions: maps ``(name, arity)`` to either a Python callable
            ``(*args) -> individual`` or a plain dict ``{arg_tuple: individual}``.
            A dict is looked up by the tuple of evaluated argument individuals.
        predicates: maps ``(name, arity)`` to the relation's extension — a set
            (or any container) of argument tuples of individuals. A nullary
            predicate maps ``(name, 0)`` to a bool. A missing predicate denotes
            the empty relation (always false), except for the order comparisons
            ``< > ≤ ≥``, which fall back to arithmetic when both operands
            evaluate to numbers — see :func:`_order_value`.
        sorts: maps a sort name (str) to its universe — a NON-EMPTY subset of
            the domain. Used by :class:`SortedQuantifier`, the sorted counting
            quantifiers and cardinality terms to restrict the range, and read
            by an atom ``S(t)`` over a name ``S`` that is a sort and has no
            predicate table of its own: a sort and the unary predicate of the
            same name are one symbol. A structure that lists both must give
            them the same extension. A sorted constant ``c:S`` must denote an
            element of ``S``. Anything else is an
            :class:`IllegalStructureError` when the formula is evaluated.

    All mapping arguments default to empty, so a bare ``Structure(domain)`` is
    a valid (if symbol-free) world.

    **Keys are checked when the structure is built.** ``functions`` and ``predicates``
    are keyed by ``(name, arity)`` and ``constants`` and ``sorts`` by the name; the
    evaluator reads a table under no other key. A table under a bare name
    (``predicates={"Q": {(0,)}}``) would therefore be dropped without a word and ``Q``
    would denote the empty relation, so a key of any other shape is refused with an
    :class:`IllegalStructureError` that names the key and the key to write instead
    (``("Q", 1)``).

    The laws on ``sorts`` are checked when a sort is first read and again after
    its table (or the domain, or the predicate table of the same name) is
    replaced by another object; changing a set in place after the first read is
    not noticed. :func:`check_structure` checks everything, every time.
    """

    def __init__(
        self,
        domain: Iterable[Any],
        constants: Optional[Mapping[str, Any]] = None,
        functions: Optional[Mapping[Tuple[str, int], Union[Callable, Mapping]]] = None,
        predicates: Optional[Mapping[Tuple[str, int], Any]] = None,
        sorts: Optional[Mapping[str, Iterable[Any]]] = None,
    ):
        """Build a structure, copying each mapping so later edits never leak in.

        Raises:
            ValueError: the domain is empty.
            ~unicode_logic_kit.semantics.tarski.IllegalStructureError:
                a ``functions`` or ``predicates`` table is not keyed
                by ``(name, arity)`` (a bare name included), or a ``constants`` or
                ``sorts`` table is not keyed by a name: the evaluator would never read
                such a table, and its symbol would silently denote nothing. The
                message names each offending key and what to write instead.
        """
        # Deduplicate while preserving order; reject an empty domain.
        seen = []
        for d in domain:
            if d not in seen:
                seen.append(d)
        if not seen:
            raise ValueError("Structure domain must be non-empty.")
        self.domain: Tuple[Any, ...] = tuple(seen)

        problems = _table_key_problems(constants or {}, functions or {},
                                       predicates or {}, sorts or {})
        if problems:
            raise IllegalStructureError("Structure: " + "; ".join(problems))

        self.constants: Dict[str, Any] = dict(constants or {})
        self.functions: Dict[Tuple[str, int], Union[Callable, Mapping]] = dict(functions or {})
        self.predicates: Dict[Tuple[str, int], Any] = dict(predicates or {})
        self.sorts: Dict[str, Tuple[Any, ...]] = {
            name: tuple(universe) for name, universe in (sorts or {}).items()
        }
        # sort name -> the objects (universe, predicate table, domain) the laws
        # on that sort were last verified against; see sort_universe.
        self._verified_sorts: Dict[str, Tuple[Any, Any, Any]] = {}

    def __repr__(self) -> str:
        """Show the domain size and the symbol tables for quick inspection."""
        return (
            f"Structure(domain={self.domain!r}, "
            f"constants={self.constants!r}, "
            f"functions={list(self.functions)!r}, "
            f"predicates={list(self.predicates)!r}, "
            f"sorts={self.sorts!r})"
        )

    def _repr_html_(self) -> str:
        """Jupyter/IPython rich-display hook: an HTML summary table.

        Same conservative shape as :meth:`__repr__`: the (already fully
        materialised, finite) domain and constant VALUES are shown, but
        functions/predicates are represented by their ``(name, arity)`` KEYS
        only — an interpretation may be a plain Python callable, and it is
        never invoked here, exactly as ``__repr__`` already chooses not to
        dump ``self.functions``/``self.predicates`` themselves. Every value is
        rendered through ``repr()`` and HTML-escaped, since a domain
        individual, constant name, or sort name may be an arbitrary
        user-supplied string (e.g. containing ``<``/``>``/``&``).
        """
        def esc(value: Any) -> str:
            return html.escape(repr(value))

        def keys_html(mapping: Mapping[Tuple[str, int], Any]) -> str:
            return ", ".join(html.escape(f"{name}/{arity}")
                              for name, arity in sorted(mapping)) or "—"

        constants_html = ", ".join(
            f"{html.escape(name)} = {esc(value)}"
            for name, value in sorted(self.constants.items())
        ) or "—"
        sorts_html = ", ".join(
            f"{html.escape(name)} = {{{', '.join(esc(v) for v in universe)}}}"
            for name, universe in sorted(self.sorts.items())
        ) or "—"
        rows = [
            ("domain", ", ".join(esc(d) for d in self.domain) or "—"),
            ("constants", constants_html),
            ("functions", keys_html(self.functions)),
            ("predicates", keys_html(self.predicates)),
            ("sorts", sorts_html),
        ]
        body = "".join(f"<tr><th>{label}</th><td>{cell}</td></tr>" for label, cell in rows)
        return f"<table><tbody>{body}</tbody></table>"

    def sort_universe(self, sort: str) -> Tuple[Any, ...]:
        """Return the universe of a named sort.

        Raises:
            KeyError: if the sort is undeclared. An undeclared sort is an error
                rather than the empty set, since ``∀x:Undeclared φ`` vacuously
                true and ``∃x:Undeclared φ`` false would silently mask a typo.
            IllegalStructureError: if the sort is empty, holds an element that
                is not in the domain, or is also a unary predicate of this
                structure with a different extension. A vacuous ``∀`` over an
                empty sort would be a truth value in a structure that is not a
                structure of the definition.
        """
        if sort not in self.sorts:
            raise KeyError(
                f"Sort {sort!r} is not declared in this structure "
                f"(known sorts: {sorted(self.sorts)})."
            )
        universe = self.sorts[sort]
        predicate = self.predicates.get((sort, 1))
        verified = self._verified_sorts.get(sort)
        if (verified is None or verified[0] is not universe
                or verified[1] is not predicate or verified[2] is not self.domain):
            problems = _sort_problems(self, sort)
            if problems:
                raise IllegalStructureError("; ".join(problems))
            self._verified_sorts[sort] = (universe, predicate, self.domain)
        return universe


def _sort_problems(structure: Structure, name: str) -> List[str]:
    """Every way the sort ``name`` of ``structure`` breaks the definition (none: empty list).

    A sort is a NON-EMPTY subset of the domain, and a sort that is also a unary
    predicate of the structure has the same extension as that predicate.
    """
    universe = structure.sorts[name]
    problems: List[str] = []
    if not universe:
        problems.append(f"sort {name!r} is empty, and a sort is never empty")
    outside = [d for d in universe if d not in structure.domain]
    if outside:
        problems.append(
            f"sort {name!r} holds {outside!r}, which "
            f"{'is' if len(outside) == 1 else 'are'} not in the domain"
        )
    declared = structure.predicates.get((name, 1))
    if declared is not None:
        in_sort = [d for d in structure.domain if d in universe]
        in_predicate = [d for d in structure.domain if (d,) in declared]
        if in_sort != in_predicate:
            problems.append(
                f"{name!r} is both a sort and a unary predicate, and they have "
                f"different extensions: the sort holds {in_sort!r}, the "
                f"predicate holds {in_predicate!r}"
            )
    return problems


def _undeclared_sort_message(sort: str) -> str:
    """The message for a formula that uses a sort the structure does not declare."""
    return f"the formula uses the sort {sort!r}, which this structure does not declare"


def _sorted_constant_problem(structure: Structure, term: SortedConstant) -> Optional[str]:
    """Why ``term`` (``c:S``) is not an element of its declared sort in ``structure``, or None.

    A constant the structure does not interpret has no value to be outside the
    sort; a sort the structure does not declare is a different violation (see
    :func:`_undeclared_sort_message`).
    """
    if term.name not in structure.constants or term.sort not in structure.sorts:
        return None
    value = structure.constants[term.name]
    if value not in structure.sorts[term.sort]:
        return (f"sorted constant {term.name}:{term.sort} denotes {value!r}, "
                f"which is not in the sort {term.sort!r} "
                f"({list(structure.sorts[term.sort])!r})")
    return None


def structure_violations(structure: Structure, *formulas: Node) -> List[str]:
    """Every way ``structure`` is not a structure of the many-sorted definition.

    The structure's own laws are always checked: every sort in ``structure.sorts``
    is a non-empty subset of the domain, and a sort that is also a unary
    predicate has that predicate's extension. With ``formulas``, the laws that
    depend on what is written are checked too: every sort a formula uses (a
    sorted quantifier, counting quantifier, cardinality term or constant) is
    declared, and every sorted constant ``c:S`` the structure interprets denotes
    an element of ``S``. A constant written with two sorts must therefore lie in
    both.

    Returns:
        One message per violation, in a stable order; an empty list for a
        legal structure. Nothing is raised.
    """
    problems: List[str] = []
    for name in structure.sorts:
        problems.extend(_sort_problems(structure, name))
    for formula in formulas:
        for node in formula.walk():
            if not isinstance(node, (SortedQuantifier, SortedCount, SortedCardinality,
                                     SortedConstant)):
                continue
            if node.sort not in structure.sorts:
                problems.append(_undeclared_sort_message(node.sort))
            elif isinstance(node, SortedConstant):
                problem = _sorted_constant_problem(structure, node)
                if problem is not None:
                    problems.append(problem)
    return list(dict.fromkeys(problems))


def check_structure(structure: Structure, *formulas: Node) -> None:
    """Raise :class:`IllegalStructureError` unless ``structure`` is a structure of the definition.

    The up-front, complete version of the checks the evaluator makes as it
    reads sorts and sorted constants: see :func:`structure_violations` for what
    is checked. The error lists every violation, not only the first.

    Raises:
        IllegalStructureError: if :func:`structure_violations` is not empty.
    """
    problems = structure_violations(structure, *formulas)
    if problems:
        raise IllegalStructureError("; ".join(problems))


def _refuse_numeral_constant_pair(formulas: Iterable[Node], where: str) -> None:
    """Refuse formulas that hold a numeral and a constant spelled like its value.

    A structure interprets a constant under its name and a numeral under the name of its
    VALUE (:func:`~unicode_logic_kit.fol._fol_nodes.numeral_key`: ``1`` and ``1.0`` are
    ``'1'``), in the one table ``constants``. ``Number(1)`` next to ``Constant('1')`` would
    therefore be ONE entry, and a structure could not tell them apart: the evaluator and the
    finite model finder (which enumerates that table) would read two symbols as one. A
    numeral is a constant of its own, so the pair is refused by name, as the Z3 route, the
    cvc5 route, the Prover9 writer and the TPTP writers refuse it. A number that is the bound
    of a counting quantifier, or the operand a cardinality is compared with, is no individual
    and is not looked up there; it clashes with nothing. ``where`` is the caller, which the
    refusal names.

    Raises:
        NotImplementedError: a :class:`Constant` or :class:`SortedConstant` is named like
            the value of a numeral of the formulas.
    """
    formulas = list(formulas)
    numerals: Dict[str, Number] = {}
    for formula in formulas:
        for numeral in term_numerals(formula, counting_comparisons=True):
            numerals.setdefault(numeral_key(numeral.value), numeral)
    if not numerals:
        return
    for formula in formulas:
        for node in formula.walk():
            if isinstance(node, (Constant, SortedConstant)) and node.name in numerals:
                raise _numeral_constant_clash(node.name, where)


def _numeral_constant_clash(name: str, where: str) -> NotImplementedError:
    """The refusal of a numeral and a constant that are one entry ``name`` of a structure."""
    return NotImplementedError(
        f"{where}: the number {name} and the constant {name!r} would be ONE entry of a "
        "structure's constants (a numeral is the constant of its value and is interpreted "
        "under that name), so a structure could not tell them apart. A numeral is a constant "
        "of its own, identified by its value (1 and 1.0 are one constant), and the kit "
        "refuses to merge it with the constant of the same spelling. Rename the constant.")


#: The comparisons a cardinality may be an operand of (arithmetic over the natural numbers).
_COUNTING_COMPARISONS = frozenset({"=", "≠"}) | _ORDER_COMPARISONS


def _cardinality_vs_individual(where: str, predicate: str, operand: Node) -> NotImplementedError:
    """The refusal of a cardinality compared with something that is not a number."""
    return NotImplementedError(
        f"{where}: {predicate!r} compares a cardinality with {operand.to_unicode_str()}, which "
        "is not a number. A cardinality |{v : φ}| is a natural number the evaluator counts, "
        "not an element of the domain, so it is only compared with a numeral or with another "
        "cardinality. Compare it with a number, or quantify over the individuals instead.")


def _cardinality_as_individual(where: str, cardinality: Node, position: str) -> NotImplementedError:
    """The refusal of a cardinality that stands where an individual is expected."""
    return NotImplementedError(
        f"{where}: the cardinality {cardinality.to_unicode_str()} is {position}. A cardinality "
        "is a natural number the evaluator counts, not an element of the domain, so it has no "
        "value there: it would be read as the element that shares its value. It can only be "
        "compared with a number (= ≠ < > ≤ ≥ against a numeral or another cardinality). "
        "Compare it, or quantify over the individuals instead.")


def _refuse_cardinality_as_individual(formulas: Iterable[Node], where: str) -> None:
    """Refuse a cardinality term that does not stand as an operand of a comparison with a number.

    ``|{v : φ}|`` is a natural number that the evaluator counts, not an element of the
    domain. Its one reading is arithmetic: an operand of ``= ≠ < > ≤ ≥`` whose other operand
    is a number (a numeral or another cardinality). Anywhere else (an argument of an ordinary
    predicate or of a function, or compared with an individual) it would have to be read as
    the element of the domain that happens to share its value (the count ``1`` as the element
    ``1``), which is another statement and one that changes with how the domain is named. The
    finite routes that state counting (the ASP and MiniZinc encodings, ``model_eval``) refuse
    these forms, and so does the evaluator, by name, instead of answering for a different
    question. ``where`` is the caller, which the refusal names.

    Raises:
        NotImplementedError: a :class:`Cardinality` or :class:`SortedCardinality` is an
            argument of a predicate, a function or another term, or an operand of a
            comparison whose other operand is not a number.
    """
    cardinalities = (Cardinality, SortedCardinality)
    for formula in formulas:
        readable: Set[int] = set()
        for node in formula.walk():
            if (isinstance(node, Atom) and node.predicate in _COUNTING_COMPARISONS
                    and len(node.args) == 2
                    and any(isinstance(a, cardinalities) for a in node.args)):
                for operand in node.args:
                    if not isinstance(operand, cardinalities + (Number,)):
                        raise _cardinality_vs_individual(where, node.predicate, operand)
                readable.update(id(a) for a in node.args if isinstance(a, cardinalities))
        for node in formula.walk():
            for child in node._child_nodes():
                if isinstance(child, cardinalities) and id(child) not in readable:
                    if isinstance(node, Atom):
                        position = f"an argument of the predicate {node.predicate!r}"
                    elif isinstance(node, Function):
                        position = f"an argument of the function {node.name!r}"
                    else:
                        position = f"an operand of a {type(node).__name__}"
                    raise _cardinality_as_individual(where, child, position)


#: The formulas ``_check_formula_once`` has already checked, by identity. The
#: formula is kept in the table so that its identity cannot be reused while the entry stands.
_CHECKED_FORMULAS: Dict[int, Node] = {}
_CHECKED_FORMULAS_MAX = 1024


def _check_formula_once(formula: Node) -> None:
    """The checks of a formula as a whole (:func:`_refuse_numeral_constant_pair` and
    :func:`_refuse_cardinality_as_individual`) for the evaluator's entry, which a model finder
    calls once per candidate structure with the same formula: a formula that passed is
    remembered (a table of bounded size), so the check costs one lookup after the first."""
    if id(formula) in _CHECKED_FORMULAS:
        return
    _refuse_numeral_constant_pair([formula], "semantics.tarski.satisfies")
    _refuse_cardinality_as_individual([formula], "semantics.tarski.satisfies")
    if len(_CHECKED_FORMULAS) >= _CHECKED_FORMULAS_MAX:
        _CHECKED_FORMULAS.clear()
    _CHECKED_FORMULAS[id(formula)] = formula


def term_value(term: Node, structure: Structure, assignment: Mapping[str, Any]) -> Any:
    """Evaluate a term to its individual in the structure under an assignment.

    - :class:`Variable` ``v`` → ``assignment[v.name]``.
    - :class:`Constant` ``c`` → ``structure.constants[c.name]``.
    - :class:`SortedConstant` ``c:S`` → ``structure.constants[c.name]``, which
      must be an element of the sort ``S`` of the structure.
    - :class:`Number` ``n`` → ``structure.constants.get(numeral_key(n.value), n.value)``
      (the literal value itself by default): a numeral is a constant named by its
      VALUE, so ``Number(1)`` and ``Number(1.0)`` are one constant. A comparison with a
      cardinality bypasses this and reads the numeral directly — see
      :func:`_operand_value`.
    - :class:`Function` → the interpreted function applied to the evaluated args;
      the interpretation may be a callable or a ``{arg_tuple: value}`` dict.

    Raises:
        KeyError: for an unassigned variable, an uninterpreted constant, or the
            sort of a sorted constant that the structure does not declare.
        IllegalStructureError: for a sorted constant whose value is not an
            element of its sort, or whose sort breaks the laws in
            :meth:`Structure.sort_universe`.
        ValueError: for an uninterpreted function symbol, a dict interpretation
            missing an argument tuple, or a lambda / non-term node.
    """
    if isinstance(term, Variable):
        if term.name not in assignment:
            raise KeyError(f"Variable {term.name!r} is not bound in the assignment.")
        return assignment[term.name]

    if isinstance(term, Constant):
        if term.name not in structure.constants:
            raise KeyError(
                f"Constant {term.name!r} has no interpretation in the structure."
            )
        return structure.constants[term.name]

    if isinstance(term, Number):
        return structure.constants.get(numeral_key(term.value), term.value)

    if isinstance(term, Function):
        args = tuple(term_value(a, structure, assignment) for a in term.args)
        key = (term.name, len(term.args))
        if key not in structure.functions:
            raise ValueError(
                f"Function {term.name!r}/{len(term.args)} has no interpretation "
                f"in the structure."
            )
        interp = structure.functions[key]
        if callable(interp):
            return interp(*args)
        # Dict-style interpretation: look up the evaluated argument tuple.
        if args not in interp:
            raise ValueError(
                f"Function {term.name!r}/{len(term.args)} is undefined for "
                f"arguments {args!r}."
            )
        return interp[args]

    if isinstance(term, (Cardinality, SortedCardinality)):
        # |{v : φ}| counts the individuals satisfying φ. The count is a NATURAL
        # NUMBER, not a domain individual: it has no value as one, and answering with
        # the integer would read it as the element that shares its value. The only
        # reading it has is the operand of a comparison with a number, which
        # _operand_value counts itself.
        raise _cardinality_as_individual(
            "semantics.tarski.term_value", term, "evaluated as an individual")

    if isinstance(term, Measure):
        # μ(entity, dimension) is the binary function ``measure``, matching the Z3 and
        # Prover9 lowerings — a structure that interprets it agrees with the provers.
        args = (term_value(term.entity, structure, assignment),
                term_value(term.dimension, structure, assignment))
        if _MEASURE_FUNC not in structure.functions:
            raise ValueError(
                "Measure term μ(…) needs an interpretation for the function "
                f"{_MEASURE_FUNC[0]!r}/{_MEASURE_FUNC[1]} in the structure."
            )
        interp = structure.functions[_MEASURE_FUNC]
        if callable(interp):
            return interp(*args)
        if args not in interp:
            raise ValueError(
                f"Function {_MEASURE_FUNC[0]!r}/{_MEASURE_FUNC[1]} is undefined for "
                f"arguments {args!r}."
            )
        return interp[args]

    if isinstance(term, SortedConstant):
        # Tested after the hot branches above, so an unsorted formula pays nothing
        # for it. The value is the constant's, as for a plain Constant; the extra
        # step is the law that it lies in the sort.
        if term.name not in structure.constants:
            raise KeyError(
                f"Constant {term.name!r} has no interpretation in the structure."
            )
        value = structure.constants[term.name]
        if value not in structure.sort_universe(term.sort):
            raise IllegalStructureError(_sorted_constant_problem(structure, term))
        return value

    if isinstance(term, _LAMBDA_TYPES):
        raise ValueError(
            f"Cannot evaluate lambda node {type(term).__name__} as a term; "
            "beta-reduce and lambda-eliminate the formula first."
        )

    raise ValueError(
        f"term_value: {type(term).__name__} is not a term node."
    )


def _witnesses(
    binder: Node,
    structure: Structure,
    assignment: Mapping[str, Any],
) -> Iterable[Any]:
    """Yield the individuals in ``binder``'s range that satisfy its matrix.

    Shared by the counting quantifiers and the cardinality terms: both bind one
    variable over a matrix and differ only in what they do with the witnesses. A
    sorted binder ranges over its sort's universe, an unsorted one over the domain.
    """
    universe = (structure.sort_universe(binder.sort)
                if isinstance(binder, (SortedCount, SortedCardinality))
                else structure.domain)
    name = binder.variable.name
    for d in universe:
        if _evaluate(binder.formula, structure, _extend(assignment, name, d)):
            yield d


def _is_number(value: Any) -> bool:
    """Whether a term value counts as a number for an order comparison.

    ``bool`` is excluded even though Python makes it an ``int`` subclass: a truth
    value is not a position on a scale, and letting ``True ≥ False`` quietly
    succeed would hide a modelling error rather than surface it.
    """
    return not isinstance(value, bool) and isinstance(value, (int, float))


def _compares_a_cardinality(atom: Atom) -> bool:
    """Whether a comparison atom has a cardinality operand."""
    return any(isinstance(a, (Cardinality, SortedCardinality)) for a in atom.args)


def _operand_value(term: Node, structure: Structure, assignment: Mapping[str, Any],
                   numeric: bool) -> Any:
    """Evaluate one operand of a comparison.

    Next to a cardinality (``numeric``), a :class:`Number` is the numeral it
    spells, never whatever ``structure.constants`` maps its name to: the other
    side is a count, so ``|{x : P(x)}| > 1`` asks about the number one. Reading
    the literal through the constant table instead would let a structure that
    interprets the name ``"1"`` as some other individual change the question —
    and a model finder that enumerates interpretations for every numeral it sees
    finds exactly such a structure, reporting a countermodel to a valid
    entailment.

    Next to a cardinality the other operand has to be a number too: the count of a
    cardinality is the only value of one, and an individual (a constant, a variable, a
    function term) is not a number, whatever integer it happens to be.

    Raises:
        NotImplementedError: ``numeric`` and ``term`` is neither a numeral nor a cardinality.
    """
    if numeric:
        if isinstance(term, Number):
            return term.value
        if isinstance(term, (Cardinality, SortedCardinality)):
            return sum(1 for _ in _witnesses(term, structure, assignment))
        raise _cardinality_vs_individual("semantics.tarski", "a comparison", term)
    return term_value(term, structure, assignment)


def _order_value(atom: Atom, structure: Structure, assignment: Mapping[str, Any]) -> bool:
    """Truth value of a binary order comparison ``< > ≤ ≥``.

    Three readings apply, in this order of precedence:

    1. A :class:`Cardinality` operand forces the **numeric** reading. A cardinality
       is a natural number this evaluator computes itself, so there is no freedom
       left to a structure; routing it through a relation extension would be a
       category error. A :class:`Number` on the other side is read as the numeral
       itself, not through ``structure.constants`` (see :func:`_operand_value`).
       A cardinality compared against a non-number raises.
    2. Otherwise a **declared** extension wins. The order symbols are ordinary
       relation symbols of the language, and a structure may interpret ``<`` over
       its domain however it likes — that is also the reading ``to_z3`` /
       ``to_prover9`` export, where the comparison is an uninterpreted relation.
    3. Otherwise, if both operands evaluate to numbers, the **numeric** reading
       applies. This is what makes an undeclared order over :class:`Measure` values
       behave: ``μ`` is an uninterpreted function, so a structure that maps it to
       numbers without also declaring ``≥`` would otherwise fall through to the
       empty relation and be silently false — the same failure mode (1) exists to
       prevent for cardinalities.

    Anything else is the empty relation, hence false, like any uninterpreted
    predicate. Note the asymmetry between (1) and (2) is deliberate and not an
    inconsistency: a cardinality *is* a number, whereas a measure's values are
    whatever the structure says they are.
    """
    numeric = _compares_a_cardinality(atom)
    left, right = (_operand_value(a, structure, assignment, numeric) for a in atom.args)

    if numeric:
        for value in (left, right):
            if not _is_number(value):
                raise ValueError(
                    f"Cannot compare a cardinality with {value!r}: an order "
                    f"comparison involving |{{v : φ}}| is numeric, so both operands "
                    f"must evaluate to numbers."
                )
        return _ORDER_OPS[atom.predicate](left, right)

    key = (atom.predicate, 2)
    if key in structure.predicates:
        return (left, right) in structure.predicates[key]

    if _is_number(left) and _is_number(right):
        return _ORDER_OPS[atom.predicate](left, right)

    return False


def _atom_value(atom: Atom, structure: Structure, assignment: Mapping[str, Any]) -> bool:
    """Compute the truth value of an atomic formula.

    Equality ``=`` is identity of the two term values; ``≠`` is non-identity. When
    one side is a cardinality, a :class:`Number` on the other is read as the
    numeral itself, as for the order comparisons (see :func:`_operand_value`).
    A nullary predicate reads its bool from ``predicates[(name, 0)]``. A binary
    order comparison ``< > ≤ ≥`` is delegated to :func:`_order_value`. Every other
    predicate is true iff the tuple of argument values lies in its extension; a
    missing extension is the empty relation, hence false — unless the name is a
    SORT of the structure: a sort and the unary predicate of that name are one
    symbol, so ``S(t)`` is then true iff the value of ``t`` is in the sort (and
    when the structure lists a predicate table for ``S`` as well, it must agree
    with the sort — :meth:`Structure.sort_universe` checks that).
    """
    if atom.predicate in ("=", "≠") and len(atom.args) == 2:
        numeric = _compares_a_cardinality(atom)
        left, right = (_operand_value(a, structure, assignment, numeric) for a in atom.args)
        return (left == right) if atom.predicate == "=" else (left != right)

    if not atom.args:
        if _is_tptp_boolean_atom(atom):
            return _truth_constant_word(atom) == "$true"    # the truth constants, in every structure
        return bool(structure.predicates.get((atom.predicate, 0), False))

    if atom.predicate in _ORDER_COMPARISONS and len(atom.args) == 2:
        return _order_value(atom, structure, assignment)

    values = tuple(term_value(a, structure, assignment) for a in atom.args)
    arity = len(atom.args)
    extension = structure.predicates.get((atom.predicate, arity))
    if structure.sorts and arity == 1 and atom.predicate in structure.sorts:
        universe = structure.sort_universe(atom.predicate)
        if extension is None:
            return values[0] in universe
    return extension is not None and values in extension


def _extend(assignment: Mapping[str, Any], name: str, value: Any) -> Dict[str, Any]:
    """Return a copy of the assignment with ``name`` bound to ``value``.

    The input mapping is never mutated (functional style).
    """
    extended = dict(assignment)
    extended[name] = value
    return extended


def satisfies(
    formula: Node,
    structure: Structure,
    assignment: Optional[Mapping[str, Any]] = None,
) -> bool:
    """Return whether ``structure`` satisfies ``formula`` under ``assignment``.

    ``assignment`` maps logical variable names to individuals; it defaults to
    the empty assignment (appropriate for a sentence with no free variables).

    Connectives follow the classical truth tables. ``∀x φ`` holds iff every
    individual of the domain satisfies ``φ`` with ``x`` bound to it; ``∃x φ``
    iff some individual does. A :class:`SortedQuantifier` ranges over the named
    sort's universe instead of the whole domain.

    Raises:
        ValueError: on a Łukasiewicz node (use the fuzzy evaluator — Tarski is
            two-valued) or a lambda node (eliminate it first), or on an unknown
            quantifier type or node type.
        IllegalStructureError: when ``structure`` is not a structure of the
            many-sorted definition and the evaluation reads the part that is
            wrong: an empty sort or one holding a non-domain element, a name
            that is a sort and a unary predicate with two extensions, a sorted
            constant outside its sort (see the module docstring and
            :func:`check_structure`). A subclass of ``ValueError``.
        NotImplementedError: when ``formula`` holds a :class:`Number` and a constant
            spelled like its value (``Number(1)`` next to ``Constant('1')``, or
            ``Number(1.0)`` next to ``Constant('1')``): a structure holds ONE entry
            ``'1'`` for both, so it could not tell them apart, and the kit refuses to
            merge a numeral with the constant of the same spelling. Also when a cardinality
            ``|{v : φ}|`` is not an operand of a comparison with a number (an argument of a
            predicate or a function, or compared with an individual): it is a natural number
            the evaluator counts, not an element of the domain, so it has no value there.
    """
    _check_formula_once(formula)
    return _evaluate(formula, structure, {} if assignment is None else assignment)


def _evaluate(formula: Node, structure: Structure, assignment: Mapping[str, Any]) -> bool:
    """:func:`satisfies` without the check of the formula as a whole, which the entry made.

    Every recursive step lands here and not on :func:`satisfies`, so a formula is checked
    once, when it is handed in, and not once per subformula and quantified individual.
    """
    if isinstance(formula, Atom):
        # `$true` / `$false` with no arguments are TPTP's DEFINED propositions (the
        # kit's TPTP reader produces them), not letters of the user's: the same
        # reading to_z3 and the TPTP writers give them.
        if _is_tptp_boolean_atom(formula):
            return _truth_constant_word(formula) == "$true"
        return _atom_value(formula, structure, assignment)

    if isinstance(formula, Not):
        return not _evaluate(formula.formula, structure, assignment)

    if isinstance(formula, And):
        return (_evaluate(formula.left, structure, assignment)
                and _evaluate(formula.right, structure, assignment))

    if isinstance(formula, Or):
        return (_evaluate(formula.left, structure, assignment)
                or _evaluate(formula.right, structure, assignment))

    if isinstance(formula, Xor):
        return (_evaluate(formula.left, structure, assignment)
                != _evaluate(formula.right, structure, assignment))

    if isinstance(formula, Implies):
        return ((not _evaluate(formula.left, structure, assignment))
                or _evaluate(formula.right, structure, assignment))

    if isinstance(formula, Iff):
        return (_evaluate(formula.left, structure, assignment)
                == _evaluate(formula.right, structure, assignment))

    if isinstance(formula, Quantifier):
        return _eval_quantifier(
            formula.type, formula.variable.name, structure.domain,
            formula.formula, structure, assignment,
        )

    if isinstance(formula, SortedQuantifier):
        universe = structure.sort_universe(formula.sort)
        return _eval_quantifier(
            formula.type, formula.variable.name, universe,
            formula.formula, structure, assignment,
        )

    if isinstance(formula, (Count, SortedCount)):
        # ∃≥n / ∃≤n / ∃=n: count the witnesses, compare against the bound. The whole
        # (finite) universe is walked — ``le`` and ``eq`` need the exact count anyway,
        # and the universes here are the small ones the model search enumerates.
        witnesses = sum(1 for _ in _witnesses(formula, structure, assignment))
        n = formula.n.value
        if formula.op == "ge":
            return witnesses >= n
        if formula.op == "le":
            return witnesses <= n
        if formula.op == "eq":
            return witnesses == n
        raise ValueError(f"Unknown counting-quantifier op: {formula.op!r}")

    if isinstance(formula, _FUZZY_TYPES):
        raise ValueError(
            f"Cannot evaluate Łukasiewicz node {type(formula).__name__} with the "
            "two-valued Tarskian evaluator; use the fuzzy evaluator instead."
        )

    if isinstance(formula, _LAMBDA_TYPES):
        raise ValueError(
            f"Cannot evaluate lambda node {type(formula).__name__}; beta-reduce "
            "and lambda-eliminate the formula before calling satisfies."
        )

    raise ValueError(
        f"satisfies: unsupported node type {type(formula).__name__}."
    )


def _eval_quantifier(
    qtype: str,
    var_name: str,
    universe: Iterable[Any],
    body: Node,
    structure: Structure,
    assignment: Mapping[str, Any],
) -> bool:
    """Evaluate a quantifier over a given universe of individuals.

    ``∀`` holds iff the body holds for every individual; ``∃`` iff for some.
    Each candidate is bound in a fresh copy of the assignment (no mutation).
    """
    if qtype in _FORALL:
        return all(
            _evaluate(body, structure, _extend(assignment, var_name, d))
            for d in universe
        )
    if qtype in _EXISTS:
        return any(
            _evaluate(body, structure, _extend(assignment, var_name, d))
            for d in universe
        )
    raise ValueError(f"Unknown quantifier type: {qtype!r}")


def models(formula: Node, structure: Structure) -> bool:
    """Convenience alias: ``satisfies(formula, structure, {})``.

    Reads as "structure models formula" — the sentence is evaluated under the
    empty assignment, so it is meaningful for closed formulas (no free
    variables).
    """
    return satisfies(formula, structure, {})
