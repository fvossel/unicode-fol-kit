"""Shared machinery for the two third-order HOL exporters.

:mod:`unicode_logic_kit.hol.thirdorder` (classical) and
:mod:`unicode_logic_kit.hol.ho_modal` (the shallow modal embedding) differ in
exactly one thing: whether a proposition is a truth value or a function from
worlds to truth values. Everything BEFORE that decision is the same work —
renaming bound predicate variables apart so a theory-wide signature analysis
answers the right question, collecting the free symbols that need declaring, and
peeling λ-binders off a property argument — so it lives here rather than twice.
"""

import re
from typing import Dict, Iterable, List, Sequence, Set, Tuple

from ..fol.nodes import (
    Node, Atom, Quantifier, SecondOrderQuantifier, PredicateTerm,
    Variable, Constant, Function, LambdaVar, Lambda,
)
from ..fol._symbol_names import dedupe
from ..fol._truth_constants import truth_value
from ..fol.qml import _thf_name

#: The two kinds of individual symbol a writer declares. A free variable is a PARAMETER of the
#: problem: one unknown element, the same in every formula (see
#: :mod:`unicode_logic_kit.fol._free_parameters`). A constant is a particular element that its
#: name stands for. ``P(x)`` with a free ``x`` and ``P('x')`` are two statements, so the two are
#: two symbols of the output even when they are spelled alike. The string ``"individual"`` is the
#: key the free variable has always had.
FREE_VARIABLE = "individual"
CONSTANT = "constant"

_LOWER_WORD = re.compile(r"[a-z][A-Za-z0-9_]*\Z")


def functor_stem(name: str) -> str:
    """A TPTP lower word (``[a-z][A-Za-z0-9_]*``) that ``name`` is turned into; NOT injective.

    This is the kit's THF stem (:func:`~unicode_logic_kit.fol.qml._thf_name`: ASCII, a Greek
    letter by its name, any other non-ASCII character as a ``uXXXX`` escape, every other
    character as ``_``, a ``p`` in front of a leading digit, a lower-case initial) with one
    repair: a name that starts with an underscore (``_sk0``, ``-3``) would still not be a lower
    word, so it gets a ``p`` in front as well. Two names can have one stem (``a b`` and ``a_b``);
    :func:`~unicode_logic_kit.fol._symbol_names.dedupe` over one pool is what keeps the symbols
    apart.
    """
    stem = _thf_name(name)
    return stem if _LOWER_WORD.match(stem) else "p" + stem


class UnsupportedHigherOrderNode(NotImplementedError):
    """Raised for an AST node a third-order embedding has no reading for.

    Subclasses NotImplementedError, matching the kit's other export refusals: a
    route that cannot carry a construct says so by name instead of dropping it.
    """


#: The ordering predicates ``<`` ``>`` ``≤`` ``≥``. Neither target format has an
#: ordering on the uninterpreted individual type, so they are ordinary
#: uninterpreted relations (WORLD-relativised in the modal embedding, exactly as
#: :mod:`unicode_logic_kit.fol.qml` reads them) under the stems named here.
ORDERING = {"<": "flt", ">": "fgt", "≤": "fle", "≥": "fge"}

#: The aliases of the CLASSICAL third-order exporter
#: (:mod:`unicode_logic_kit.hol.thirdorder`), which reads ``=`` / ``≠`` as the
#: uninterpreted relations ``feq`` / ``fneq`` — not primitive HOL identity — next to
#: the :data:`ORDERING` predicates. The MODAL exporter
#: (:mod:`unicode_logic_kit.hol.ho_modal`) does NOT use the first two entries: there
#: object identity is RIGID (HOL's own ``=`` over the individual type, no world
#: argument, as in :func:`unicode_logic_kit.fol.qml.qml_is_valid`), so it takes only
#: :data:`ORDERING` and reads ``=`` / ``≠`` through
#: :func:`unicode_logic_kit.hol.isabelle_modal._lower_identity`.
EQUALITY = {"=": "feq", "≠": "fneq", **ORDERING}


def peel_lambdas(node: Node) -> Tuple[List[str], Node]:
    """Split a (possibly nested) Lambda into its binder names and its body.

    ``λx. λy. φ`` denotes a binary relation, so the number of binders IS the
    arity of the property the argument denotes.
    """
    names = []
    while isinstance(node, Lambda):
        names.append(node.param.name)
        node = node.body
    return names, node


def rename_bound_pred(node: Node, old: str, new: str) -> Node:
    """Rename every occurrence of the predicate variable ``old`` to ``new``.

    Renames it in HEAD position (``Atom``) and in ARGUMENT position
    (``PredicateTerm``) alike, and stops at an inner binder over the same name,
    whose occurrences belong to that binding rather than this one.
    """
    if isinstance(node, SecondOrderQuantifier) and node.predicate == old:
        return node
    if isinstance(node, Atom) and node.predicate == old:
        return Atom(new, [rename_bound_pred(a, old, new) for a in node.args])
    if isinstance(node, PredicateTerm) and node.name == old:
        return PredicateTerm(new)
    return node.map_children(lambda child: rename_bound_pred(child, old, new))


def rename_apart(formulas: Sequence[Node]) -> Tuple[List[Node], Dict[str, str]]:
    """Give every second-order binder a name unique across ``formulas``.

    A theory-wide signature analysis merges by NAME, and a bound variable's name
    is scoped to its own formula: two axioms may each bind ``P`` at a different
    arity without disagreeing about anything, and a binder may even shadow
    another of the same name inside one formula. Renaming apart first is what
    keeps the analysis answering the question that was actually asked — what the
    FREE symbols are, and what arity each binding really has — instead of a
    false conflict between two local bindings.

    Returns the renamed formulas and a ``{fresh name: original name}`` map. The
    renaming is for the ANALYSIS; emission renders the renamed tree but prints
    the original names back through that map, which is sound because the emitted
    binders reproduce the original scoping exactly.
    """
    counter = [0]
    original: Dict[str, str] = {}

    def walk(node: Node) -> Node:
        if isinstance(node, SecondOrderQuantifier):
            counter[0] += 1
            fresh = f"Bound{counter[0]}"
            original[fresh] = node.predicate
            renamed = rename_bound_pred(node.formula, node.predicate, fresh)
            return SecondOrderQuantifier(node.type, fresh, node.arity, walk(renamed))
        return node.map_children(walk)

    return [walk(f) for f in formulas], original


def bound_pred_names(node: Node, acc: Set[str] = None) -> Set[str]:
    """Collect every predicate-variable name bound by a second-order quantifier."""
    acc = set() if acc is None else acc
    if isinstance(node, SecondOrderQuantifier):
        acc.add(node.predicate)
    for child in node._child_nodes():
        bound_pred_names(child, acc)
    return acc


def atom_predicates(node: Node, acc: Set[str] = None) -> Set[str]:
    """Collect every predicate name applied in ``node``."""
    acc = set() if acc is None else acc
    if isinstance(node, Atom) and truth_value(node) is None:
        acc.add(node.predicate)         # (`$true` / `$false` are constants, not predicates)
    for child in node._child_nodes():
        atom_predicates(child, acc)
    return acc


def function_symbols(formulas: Sequence[Node], acc: Dict[str, int] = None) -> Dict[str, int]:
    """Collect ``{function name: arity}`` over ``formulas``."""
    acc = {} if acc is None else acc
    for node in formulas:
        if isinstance(node, Function):
            acc[node.name] = len(node.args)
        function_symbols(list(node._child_nodes()), acc)
    return acc


def constant_name(node: Constant) -> str:
    """The name of the constant ``node``, which has to be a string.

    Every other kind of name has no identifier in either target, so it is refused here, by
    name, before any text is written.
    """
    if not isinstance(node.name, str):
        raise TypeError(
            f"the name of a constant must be a string, got {node.name!r} "
            f"({type(node.name).__name__}): a constant of that name has no identifier in THF "
            "or in Isabelle; write the name as a string")
    return node.name


def individual_symbols(formulas: Sequence[Node]) -> List[Tuple[str, str]]:
    """The individual symbols of ``formulas`` that a closed theory has to declare, as ``(kind, name)``.

    ``kind`` is :data:`CONSTANT` for a :class:`~unicode_logic_kit.fol.nodes.Constant` and
    :data:`FREE_VARIABLE` for an object variable bound by no quantifier or λ. A closed HOL theory
    has no free variables, so the second is declared as an individual constant too, but it stays
    the symbol it is: one unknown element, never the constant that is spelled like it.

    The list is sorted by name and, within one name, the free variable comes first; for a formula
    in which no variable is spelled like a constant that is the order of the sorted names.
    """
    variables: Set[str] = set()
    constants: Set[str] = set()

    def walk(node: Node, bound: frozenset) -> None:
        if isinstance(node, Constant):
            constants.add(constant_name(node))
            return
        if isinstance(node, Variable):
            if node.name not in bound:
                variables.add(node.name)
            return
        if isinstance(node, LambdaVar):
            return
        if isinstance(node, Quantifier):
            walk(node.formula, bound | {node.variable.name})
            return
        if isinstance(node, Lambda):
            walk(node.body, bound | {node.param.name})
            return
        for child in node._child_nodes():
            walk(child, bound)

    for formula in formulas:
        walk(formula, frozenset())
    symbols = [(FREE_VARIABLE, name) for name in variables] + [(CONSTANT, name) for name in constants]
    return sorted(symbols, key=lambda symbol: (symbol[1], symbol[0] != FREE_VARIABLE))


class ThfNames:
    """THF identifiers for one problem emitted by a third-order exporter.

    A THF constant and an annotated formula's name must be a lower word: an
    upper-case initial makes a token a VARIABLE, so the kit's ``Positive``/``G``
    written out verbatim is not a constant at all and the problem does not parse.
    Free symbols therefore go through the kit's THF stem (ASCII, lower-case
    initial, see :func:`functor_stem`) and are made unique — keyed by
    ``(kind, name)``, because THF has one namespace for predicates, individuals
    and functions, and pushed off ``reserved`` (the embedding's own functors) so
    ``G`` and ``g``, or a user predicate named ``r``, cannot collide with each
    other or with the accessibility relation. The kinds a writer uses are
    ``"predicate"``, ``"function"``, ``"nominal"`` and the two of an individual,
    :data:`FREE_VARIABLE` and :data:`CONSTANT`: a free variable and a constant that
    are spelled alike are two symbols with two functors. A bound variable is not
    named here; its token is upper-case (see :func:`bound_token`) and a functor
    lower-case, so a bound variable never has the token of a symbol of this class.
    """

    def __init__(self, reserved: Sequence[str] = ()):
        self._used: Set[str] = set(reserved)
        self._functors: Dict[Tuple[str, str], str] = {}
        self._units: Set[str] = set()

    def functor(self, kind: str, name: str) -> str:
        """The unique THF constant for the free symbol ``name`` of ``kind``."""
        key = (kind, name)
        if key not in self._functors:
            self._functors[key] = dedupe(functor_stem(name), self._used)
        return self._functors[key]

    def unit(self, name: str) -> str:
        """Claim a unique annotated-formula name derived from ``name``."""
        return dedupe(functor_stem(name), self._units)


_ISABELLE_IDENTIFIER = re.compile(r"[A-Za-z][A-Za-z0-9_']*\Z")

#: The constants of HOL that the text of an exporter names itself (``True`` and ``False`` for
#: ``$true`` / ``$false``): a symbol of the formula never takes one of these names.
ISABELLE_BUILT_IN = frozenset({"True", "False"})


def is_isabelle_identifier(name: str) -> bool:
    """Whether ``name`` is an Isabelle identifier as it stands: an ASCII letter, then ASCII
    letters, digits, underscores and apostrophes."""
    return _ISABELLE_IDENTIFIER.match(name) is not None


class IsabelleNames:
    """Isabelle identifiers for the free symbols of one theory emitted by a third-order exporter.

    A symbol is keyed by ``(kind, name)`` (``"predicate"``, ``"function"``, :data:`FREE_VARIABLE`,
    :data:`CONSTANT`), and the identifiers are made unique over ONE pool, because an Isabelle
    theory has one namespace for the constants it declares: a constant ``P`` and a predicate
    ``P``, a free variable ``x`` and a constant ``x``, are four symbols and must not be declared
    under one name. ``reserved`` are the names the text already gives a meaning to (the
    embedding's own vocabulary, HOL's ``True`` and ``False``): no symbol takes one of them.

    A name that is an Isabelle identifier (:func:`is_isabelle_identifier`) is written as it is,
    so ``socrates`` and ``Alice`` keep their names and the text of a formula whose symbols are
    plain words is the text it always was. Any other name (``John Doe``, ``G-910``, ``C++``,
    ``2008SummerOlympics``, ``θ``, ``_sk0``) is written under its :func:`functor_stem`. Names
    that are identifiers claim their own spelling FIRST, so a name that merely sanitises onto
    one (``a b`` next to ``a_b``) is the one pushed to ``a_b_2``.
    """

    def __init__(self, reserved: Iterable[str] = ()):
        self._used: Set[str] = set(reserved)
        self._tokens: Dict[Tuple[str, str], str] = {}

    def claim(self, symbols: Iterable[Tuple[str, str]]) -> None:
        """Name ``symbols`` (``(kind, name)`` pairs): those that are identifiers first, each
        group in the order given, so the order a caller gives decides who keeps a contested name."""
        pending = [s for s in dict.fromkeys(symbols) if s not in self._tokens]
        for verbatim in (True, False):
            for kind, name in pending:
                if is_isabelle_identifier(name) == verbatim:
                    base = name if verbatim else functor_stem(name)
                    self._tokens[(kind, name)] = dedupe(base, self._used)

    def symbol(self, kind: str, name: str) -> str:
        """The identifier of the symbol ``name`` of ``kind`` (named now when it has none yet)."""
        if (kind, name) not in self._tokens:
            self.claim([(kind, name)])
        return self._tokens[(kind, name)]


def bound_token(name: str, suffix: str, scope: Dict[str, str]) -> str:
    """An upper-case THF variable token for a binder of ``name``.

    ``scope`` maps each source name bound further out to its token. The result
    differs from every one of those tokens: ``x`` and ``X`` share a stem, and
    reusing it for an inner binder of a DIFFERENT name would capture the outer
    variable's occurrences inside the body.
    """
    stem = _thf_name(name).upper()
    if not stem[:1].isalpha():
        stem = "V" + stem
    stem += suffix
    taken = set(scope.values())
    token, i = stem, 2
    while token in taken:
        token, i = f"{stem}{i}", i + 1
    return token
