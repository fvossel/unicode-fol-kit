"""A numeral is a constant: the one name a writer gives it, and the check that keeps it apart.

On every route that was not asked for arithmetic, a :class:`~unicode_logic_kit.fol.nodes.Number`
is a CONSTANT symbol identified by its VALUE: ``Number(1)``, ``Number(1.0)`` and the
numeral written ``01`` are one constant (one node: a ``Number`` stores a float with a
whole value as the integer it equals), and
nothing else is known about it, so two numerals of different value may denote the same
element, like any two constants. The operators ``+ - * /`` are uninterpreted function
symbols and ``< > ≤ ≥`` uninterpreted predicates. A problem writer for a language whose
own numbers are arithmetic (TPTP's ``1`` is an ``$int``, ``$sum`` is addition) must not
hand a numeral to the prover as a number: Vampire and E read the bare ``1`` as an
integer, and the text ``p(1)`` is then a type error for a predicate over individuals,
while ``1 != 2`` and ``$sum(1,1) = 2`` are theorems of the prover's arithmetic that the
kit's reading does not have.

This module is what such a writer shares:

* :func:`numeral_name` -- the name a numeral is written under, one per VALUE: the text of
  the number, with an integral float spelled as the integer (``1.0`` is ``1``). The writer
  then treats it as a constant of that name, so the writer's ordinary renaming (a name
  that is no word in the target language is replaced by a legal, collision-free token,
  and the replacement is recorded) gives it its word, and the writer's name map reads it
  back. :func:`numeral_value` is the inverse.
* :func:`numerals_as_constants` -- rewrite every numeral in term position as that
  constant, and refuse by name a constant, sorted constant or function that is spelled
  like a numeral of the problem (``Number(1)`` and ``Constant('1')``): they would be one
  symbol under one name, and the kit keeps a numeral and a constant apart.

A ``Number`` that is the bound of a counting quantifier (``Count.n``,
``SortedCount.n``) is not a term and is left as it is. A writer whose target states a
comparison with a cardinality arithmetically (``|{x : P(x)}| ≥ 2`` is HOL's ``card {x. P x}
≥ 2`` over the naturals) asks for ``counting_comparisons=True``: a ``Number`` operand of
such a comparison is then the number of the comparison and not a constant, and is left as
it is too.
"""

from dataclasses import replace
from typing import Callable, Dict, FrozenSet, Iterable, Iterator, List, Sequence, Tuple, Union

from ._fol_nodes import _number_text
from .nodes import (
    Atom, Cardinality, Constant, Count, Function, Node, Number, SortedCardinality,
    SortedConstant, SortedCount,
)

__all__ = ["numeral_name", "prefixed_numeral_name", "numeral_value", "term_numerals",
           "numerals_as_constants"]

_COUNT_NODES = (Count, SortedCount)

#: The comparisons whose operands are numbers when one of them is a cardinality.
_COMPARISONS = frozenset({"=", "≠", "<", ">", "≤", "≥"})


def _plain(value: Union[int, float]) -> Union[int, float]:
    """``value`` as the ``int`` or ``float`` it is; a ``bool`` is the integer it equals."""
    if isinstance(value, bool):
        return int(value)
    if isinstance(value, (int, float)):
        return value
    raise NotImplementedError(
        f"Number({value!r}) holds a {type(value).__name__}, and only an int or a float is a "
        "numeral the kit's writers can name; convert the value first.")


def numeral_name(value: Union[int, float]) -> str:
    """The name a numeral of value ``value`` is written under: ONE name per value.

    The text of the number as the kit prints it everywhere (digits, an optional fractional
    part, a leading ``-``, no exponent), except that a float with an integral value is
    spelled as that integer, so ``1`` and ``1.0`` are one name
    (``numeral_name(1.0) == numeral_name(1) == '1'``) while ``2.5`` stays ``'2.5'``. A
    :class:`~unicode_logic_kit.fol.nodes.Number` already stores such a float as the integer, so for
    the value of a node this is simply its printed text; the function takes a raw value too.

    Raises:
        ValueError: ``value`` is ``inf``, ``-inf`` or ``nan``: no syntax of the kit has a
            literal for it.
        NotImplementedError: ``value`` is neither an ``int`` nor a ``float``.
    """
    value = _plain(value)
    if isinstance(value, float) and value.is_integer():
        value = int(value)
    return _number_text(value)


def prefixed_numeral_name(value: Union[int, float]) -> str:
    """:func:`numeral_name` with an ``n`` in front (``n1``, ``n2.5``, ``n-1``): the spelling
    the higher-order writers (THF, Isabelle/HOL) give a numeral, so that the identifier
    their own sanitiser makes of it starts with a lower-case letter (``n1``, ``n2_5``,
    ``n_1``). One name per value, like :func:`numeral_name`."""
    return "n" + numeral_name(value)


def numeral_value(name: str) -> Union[int, float]:
    """The value of the numeral that :func:`numeral_name` named ``name``: an ``int`` when the
    name has no ``.``, a ``float`` otherwise.

    The exact inverse of :func:`numeral_name` and of nothing else: the name of a float is the
    shortest text that reads back as that float, so reading it back gives the float that was
    named. A text a person typed is read by ``_numeral_from_text`` (at most 15 significant digits),
    never by this function, and a name that :func:`numeral_name` does not produce is refused, so
    two different names are never read as one value.

    Raises:
        ValueError: ``name`` is not a name :func:`numeral_name` produces (``1.0``, ``007``, ``1e3``
            and ``0.30000000000000005``, whose nearest float is named ``0.30000000000000004``,
            are not).
    """
    value = float(name) if "." in name else int(name)
    if numeral_name(value) != name:
        raise ValueError(
            f"{name!r} is not a name numeral_name produces (the numeral of that value is named "
            f"{numeral_name(value)!r}), so it is not read as that value")
    return value


def _is_counting_comparison(atom: Atom) -> bool:
    """Whether ``atom`` compares a cardinality (``|{x : φ}|``, sorted or not) with
    something, by ``= ≠ < > ≤ ≥``: its ``Number`` operands are numbers, not individuals."""
    return (atom.predicate in _COMPARISONS and len(atom.args) == 2
            and any(isinstance(a, (Cardinality, SortedCardinality)) for a in atom.args))


def _term_children(node: Node, counting_comparisons: bool = False) -> List[Node]:
    """The children of ``node`` that can hold a term: the bound of a counting quantifier
    is not a term, and (with ``counting_comparisons``) neither is a number compared with a
    cardinality; everything else is read as it is."""
    if isinstance(node, _COUNT_NODES):
        return [node.variable, node.formula]
    if counting_comparisons and isinstance(node, Atom) and _is_counting_comparison(node):
        return [a for a in node.args if not isinstance(a, Number)]
    return node._child_nodes()


def term_numerals(formula: Node, *, counting_comparisons: bool = False) -> Iterator[Number]:
    """Every :class:`~unicode_logic_kit.fol.nodes.Number` of ``formula`` that stands in term
    position, in pre-order: not the bound ``n`` of a ``Count`` / ``SortedCount`` and, with
    ``counting_comparisons=True``, not a ``Number`` compared with a cardinality."""
    stack: List[Node] = [formula]
    while stack:
        node = stack.pop()
        if isinstance(node, Number):
            yield node
            continue
        stack.extend(reversed(_term_children(node, counting_comparisons)))


def _spellings(numeral: Number, spell: Callable[[Union[int, float]], str]) -> Tuple[str, ...]:
    """The texts a numeral is written as: the name ``spell`` gives it and its canonical name.

    A value has one spelling (a :class:`~unicode_logic_kit.fol.nodes.Number` stores a float with a
    whole value as the integer it equals), so the text the kit prints for the node is the
    canonical name and there is no third text."""
    value = _plain(numeral.value)
    return tuple(dict.fromkeys((spell(value), numeral_name(value))))


def _clash(where: str, numeral: Number, spelling: str, kind: str, name: str) -> NotImplementedError:
    return NotImplementedError(
        f"{where}: the number {_number_text(_plain(numeral.value))} and the {kind} {name!r} are spelled "
        f"alike ({spelling!r}), so they would be written under one name and be ONE symbol. "
        "A numeral is a constant of its own, identified by its value (1 and 1.0 are one "
        "constant), and it is not the constant of the same spelling -- the kit refuses to "
        f"merge the two. Rename the {kind}.")


def _check_names(formulas: Sequence[Node], spelled: Dict[str, Number], where: str) -> None:
    for formula in formulas:
        for node in formula.walk():
            if isinstance(node, (Constant, SortedConstant)):
                kind = "constant"
            elif isinstance(node, Function):
                kind = "function"
            else:
                continue
            numeral = spelled.get(node.name)
            if numeral is not None:
                raise _clash(where, numeral, node.name, kind, node.name)


def _rewrite(node: Node, spell: Callable[[Union[int, float]], str],
             counting_comparisons: bool = False) -> Node:
    if isinstance(node, Number):
        return Constant(spell(_plain(node.value)))
    if isinstance(node, _COUNT_NODES):
        return replace(node, formula=_rewrite(node.formula, spell, counting_comparisons))   # the bound variable holds no numeral
    if counting_comparisons and isinstance(node, Atom) and _is_counting_comparison(node):
        return Atom(node.predicate, tuple(a if isinstance(a, Number) else _rewrite(a, spell, True)
                                          for a in node.args))
    return node.map_children(lambda child: _rewrite(child, spell, counting_comparisons))


def numerals_as_constants(formulas: Iterable[Node], *, where: str,
                          spell: Callable[[Union[int, float]], str] = numeral_name,
                          counting_comparisons: bool = False
                          ) -> Tuple[List[Node], FrozenSet[str]]:
    """``formulas`` with every numeral in term position written as a constant, and the set
    of the names of those constants.

    The constant of a numeral is named ``spell(value)``: :func:`numeral_name` unless a writer
    has its own spelling (the HOL writers spell a numeral ``n1``, ``n2.5``), which is
    one name per value either way. A formula without a numeral comes back as the very same
    object. ``where`` is the name of the writer that is calling, which a refusal opens with.
    With ``counting_comparisons=True`` a ``Number`` that is an operand of a comparison with a
    cardinality (``|{x : P(x)}| ≥ 2``) is not in term position: it is the number the target
    compares the count with, and stays a ``Number``.

    Raises:
        NotImplementedError: a ``Constant``, ``SortedConstant`` or ``Function`` of the
            formulas is spelled like a numeral of the formulas (``Number(1)`` next to
            ``Constant('1')``, or ``Number(2.5)`` next to ``Constant('2.5')``; ``Number(1.0)``
            is ``Number(1)``, so ``Constant('1.0')`` is spelled like no numeral), or a
            ``Number`` holds a value that is neither an ``int`` nor a ``float``.
        ValueError: a numeral is ``inf``, ``-inf`` or ``nan``.
    """
    formulas = list(formulas)
    spelled: Dict[str, Number] = {}
    numerals_of: List[List[Number]] = []
    for formula in formulas:
        found = list(term_numerals(formula, counting_comparisons=counting_comparisons))
        numerals_of.append(found)
        for numeral in found:
            for spelling in _spellings(numeral, spell):
                spelled.setdefault(spelling, numeral)
    if not spelled:
        return formulas, frozenset()
    _check_names(formulas, spelled, where)
    names = frozenset(spell(_plain(n.value)) for found in numerals_of for n in found)
    return [_rewrite(f, spell, counting_comparisons) if found else f
            for f, found in zip(formulas, numerals_of)], names
