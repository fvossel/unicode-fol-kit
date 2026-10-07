"""The key of an atom on a route that identifies an atom by its written form.

A propositional route (a truth table, a many-valued or fuzzy evaluator, the intuitionistic
and counterfactual deciders, a trace of a linear-time formula) takes every ground atom as a
letter of its own and names the letter by the KEY of the atom: the text it prints as, with
every constant written by its bare name (``key_text`` of ``fol/_msfl_nodes.py``:
``'P'``, ``'P(a)'``, ``'Likes(a, b)'``). The text of the FORMULA (``Atom.to_unicode_str()``)
writes a constant in quotes when its bare name would read as something else (``P('a')``);
the key does not, so a valuation typed as ``{"P(a)": True}`` keeps meaning the atom ``P``
over the element ``a``, as it always did.

An atom whose constants are all bare-readable has ONE spelling: its key and its formula text
are the same string. An atom with a quoted constant has TWO, and a caller's valuation may be
keyed in either: the guide taught ``atom.to_unicode_str()`` as "the key", and a hand-built atom
over ``Constant("a")`` prints ``Likes('a', 'b')`` since quoted constants exist. So a lookup in a
table that comes FROM THE CALLER goes through :func:`find_key`, which reads the key and then the
formula text; a table the kit builds itself and reads back is keyed by :func:`atom_key` alone.
The two spellings cannot name two atoms because a key that holds a complete quoted constant
(that of ``Constant("'a'")``: its key ``P('a')`` is also the formula text of ``P`` over the
constant ``a``) is refused where a key is made.

The key is faithful only while two different atoms never have one. Two do, and the route would
read them as ONE letter and answer about another problem:

* the numeral ``1`` and a constant named ``1`` (``Number(1)`` and ``Constant('1')``: the
  TPTP reader makes the pair from ``p(1)`` and ``p('1')``): ``P(1) ⊢ P('1')`` would be valid;
* a free variable ``x`` and a constant named ``x``: ``P(c) → P(x)`` would be valid for
  ``c = Constant('x')``, although a free variable is a parameter (one unknown element), not
  the constant of its name;
* a constant named like a compound term (``Constant('f(a)')`` and ``f(a)``).

:class:`AtomKeys` is the one place the key is built. It gives every atom of one problem its
key and refuses, by name, a problem in which two different atoms would get the same key (the
refusal every route that names a symbol by its text already gives for a numeral and a constant
of one spelling). :func:`atom_key` is the key alone, for a route that already knows the
problem has no such pair.

A sorted constant ``c:S`` is the constant ``c`` (it denotes an element of ``S``): its key is
the key of the plain constant, so ``Mortal(c:S)`` and ``Mortal(c)`` are ONE letter. A route
that cannot state what membership of the sort means for its truth values refuses the sorted
constant by name instead (``sorted_constants="refuse"``).

The operators of an agent are named in the same way: a model keeps the relation of ``K_a`` under
the name ``"K:" + agent_key(a)``, so two different agent terms with one key (the numeral ``1``
and the constant ``'1'``) would be ONE agent. :func:`refuse_alike_agents` refuses such a pair,
for the routes that file a relation, a tableau branch or a first-order predicate under that name.
"""

import re
from collections.abc import Mapping
from functools import lru_cache
from typing import Any, Container, Dict, Iterable, List, Optional, Tuple, Type

from ._fol_nodes import Atom, Constant, Function, Node, Number, Variable
from ._identifiers import (
    _UNSPELLABLE, _unquote_constant, is_bare_constant, quoted_name_pattern)
from ._modal_nodes import (
    Believes, CommonKnowledge, DistributedKnowledge, EverybodyKnows, Knows, Says, Wants)
from ._msfl_nodes import SortedConstant, key_text
from ._truth_constants import truth_value

__all__ = ["atom_key", "other_key", "find_key", "find_own_key", "plain_atom",
           "refuse_sorted_constant", "AtomKeys", "agent_key", "refuse_alike_agents"]


@lru_cache(maxsize=1)
def _free_standing_quoted_token():
    """A complete QUOTED_NAME token with no letter, digit or apostrophe next to it.

    Where the text of a formula writes a constant in quotes, the token stands free: what
    comes before it is the start, ``(`` or a space, and what follows is the end, ``)``, ``,``, a
    space, ``:`` or ``}``. The pattern asks for less (anything but a letter, a digit or an
    apostrophe on either side), so it finds every such token and some text that is none.
    """
    return re.compile(r"(?<![^\W_])(?<!')" + quoted_name_pattern() + r"(?![^\W_])(?!')")


@lru_cache(maxsize=8192)
def _has_text(name: str) -> bool:
    """Whether a constant of this (not bare-readable) name has a text, in quotes.

    The empty name and a name with a control character have none, so the formula text of an atom
    that holds such a constant does not exist.
    """
    return name != "" and _UNSPELLABLE.search(name) is None


def _refuse_key_that_reads_as_text(key: str, route: str, error: Type[Exception]) -> None:
    """Refuse a key that holds a complete quoted constant.

    A key writes every name as it is, so a quote in a key is part of a NAME (a constant named
    ``'a'``, one named ``ab, 'b'``, a proposition a TPTP file calls ``'p(\\'a\\')'``). The text
    of a formula writes a quote only around a constant. A key that holds a whole quoted
    constant, standing free, may therefore be the text of ANOTHER atom as a formula: ``P('a')``
    is the key of ``P`` over the constant named ``'a'`` and the text of ``P`` over the constant
    ``a``. A valuation may be keyed either way, so one entry would answer for two atoms.

    The check is on the safe side. It refuses every key that is the formula text of another atom
    with a quoted constant, and also a key such as ``P(rock 'n' roll)``, which is the text of no
    formula. A name with one apostrophe (``D'Alembert``), with apostrophes next to letters or
    digits (``3',5'-cyclic``), or two such names in one atom, is not refused.
    """
    found = _free_standing_quoted_token().search(key)
    if found is None:
        return
    token = found.group(0)
    inner = _unquote_constant(token)
    raise error(
        f"{route}: the key of this atom, {key!r}, reads as the text of another atom. A key "
        f"writes every name as it is, and a name here holds apostrophes, so the key holds "
        f"{token}, which is how a formula writes the constant named \"{inner}\" (in quotes). "
        f"A valuation may be keyed by the key of an atom or by its text as a formula, so one "
        f"entry would answer for two atoms. Rename the symbol (a name that merely holds an "
        f"apostrophe, such as D'Alembert, is fine).")


def _survey(atom: Node) -> Tuple[bool, bool, bool]:
    """One walk over ``atom``: ``(has a sorted constant, its formula text writes a quote, a name
    of it may hold an apostrophe)``.

    The third is what :func:`_refuse_key_that_reads_as_text` is asked about: a key holds a quote
    only where a name does, so an atom whose names hold none is never scanned.
    """
    if type(atom) is Atom and not atom.args:
        return False, False, "'" in atom.predicate      # a proposition holds no constant
    has_sorted = False
    has_quoted = False
    has_no_text = False
    apostrophe = False
    # The same nodes as ``atom.walk()``, but without the generic ``_child_nodes`` (which reads
    # the dataclass fields of every node): a key is made for every atom of every evaluation,
    # and an atom is a handful of constants, variables and numerals. A node of another kind
    # takes the generic way.
    # ``Any``: the node kinds are told apart by their class below, which a type checker does
    # not follow, and each branch reads the fields of the class it found.
    stack: List[Any] = [atom]
    while stack:
        node = stack.pop()
        kind = type(node)
        if kind is Number:
            continue
        if kind is Variable:
            apostrophe = apostrophe or "'" in node.name
            continue
        if kind is Atom:
            apostrophe = apostrophe or "'" in node.predicate
            stack.extend(node.args)
            continue
        if kind is Function:
            apostrophe = apostrophe or "'" in node.name
            stack.extend(node.args)
            continue
        if kind is SortedConstant:
            has_sorted = True
        elif kind is not Constant:
            stack.extend(node._child_nodes())
            if not isinstance(node, (Constant, SortedConstant)):
                # a node of a kind not listed here: its own name is not looked at, so the key
                # is scanned to be sure
                apostrophe = True
                continue
            has_sorted = has_sorted or isinstance(node, SortedConstant)
        name = node.name
        if not isinstance(name, str):
            has_no_text = True
        elif is_bare_constant(name):
            continue                    # a bare name holds no apostrophe
        else:
            apostrophe = apostrophe or "'" in name
            if _has_text(name):
                has_quoted = True
            else:
                has_no_text = True
    # an atom that holds a constant without a text has no formula text at all
    return has_sorted, has_quoted and not has_no_text, apostrophe


def _key(atom: Node, route: str, error: Type[Exception]) -> Tuple[str, Node, bool]:
    """``(key, plain atom, whether its formula text differs from the key)`` of ``atom``.

    The one place a key is rendered. A key that reads as the formula text of another atom is
    refused here (:func:`_refuse_key_that_reads_as_text`).
    """
    has_sorted, quoted, apostrophe = _survey(atom)
    plain = _plain(atom) if has_sorted else atom
    key = key_text(plain)
    if apostrophe:
        _refuse_key_that_reads_as_text(key, route, error)
    return key, plain, quoted


def _has_sorted_constant(node: Node) -> bool:
    """Whether a sorted constant occurs anywhere inside ``node``."""
    return any(isinstance(n, SortedConstant) for n in node.walk())


def _plain(node: Node) -> Node:
    """``node`` with every sorted constant ``c:S`` replaced by the plain constant ``c``."""
    if isinstance(node, SortedConstant):
        return Constant(node.name)
    return node.map_children(_plain)


def plain_atom(atom: Node) -> Node:
    """The atom with each sorted constant ``c:S`` read as the constant ``c`` (the atom itself
    when it has none)."""
    return _plain(atom) if _has_sorted_constant(atom) else atom


def atom_key(atom: Node) -> str:
    """The key of an atom: the text of the atom with every constant written by its bare name.

    This is the definition of a key. The valuations, models and traces that the evaluators of
    the kit read (``satisfies_modal``, ``fuzzy_evaluate``, the many-valued, matrix,
    intuitionistic and counterfactual evaluators, ``ltl_trace_satisfies``, the probabilistic
    programs) are keyed by it, and so is every table the kit RETURNS (the countermodels of the
    modal, intuitionistic and counterfactual deciders, the models of a tableau, the columns of a
    truth table). A sorted constant ``c:S`` is written ``c``, as the constant it is.

    The key is NOT the text of the formula. ``Constant("k2")`` is written ``'k2'`` in the formula
    text, so that the text reads back as that constant, and ``k2`` in the key: for the atom
    ``Likes`` over the constants ``a`` and ``b`` the key is ``Likes(a, b)`` and the text of the
    formula is ``Likes('a', 'b')``. For an atom whose constants are all bare-readable
    (``Likes(alice, bob)``) the two are the same string. The evaluators also read a valuation
    that a caller keyed by the text of the atom as a formula, ``atom.to_unicode_str()``, so
    either spelling is found.

    No check is made that another atom does not have the same key; :class:`AtomKeys` does that
    for the atoms of one problem.

    Raises:
        NotImplementedError: the key would hold a complete quoted constant, because a name of
            the atom holds apostrophes (``Constant("'a'")``, ``Constant("ab, 'b'")``): such a key
            is also the formula text of another atom (``P`` over the constant ``a``), and one
            key must not name two atoms. A name that merely holds an apostrophe
            (``D'Alembert``, ``3',5'-cyclic``) has its key.
    """
    return _key(atom, "atom_key", NotImplementedError)[0]


def other_key(atom: Node) -> Optional[str]:
    """The OTHER spelling of the key of an atom: its text as a formula, when that differs.

    ``None`` when no constant of the atom is written in quotes (every constant reads back
    bare), where the formula text and :func:`atom_key` are one string and nothing is rendered; else
    the text of the same plain atom as a formula (``Likes('a', 'b')`` for the key
    ``Likes(a, b)``). A valuation a caller keyed by ``atom.to_unicode_str()`` holds this one.
    The two spellings are different strings whenever the second exists, and the refusal of a
    key that holds a quoted constant (:func:`atom_key`) keeps them from naming two atoms.

    Raises:
        NotImplementedError: as :func:`atom_key`.
    """
    has_sorted, quoted, apostrophe = _survey(atom)
    plain = _plain(atom) if has_sorted else atom
    if apostrophe:
        _refuse_key_that_reads_as_text(key_text(plain), "other_key", NotImplementedError)
    return plain.to_unicode_str() if quoted else None


def _locate(table: Container[str], key: str, plain: Node, quoted: bool,
            route: str) -> Optional[str]:
    """The body of :func:`find_key`, for an atom whose ``key`` is made already."""
    if not quoted:
        return key if key in table else None
    if key in table:
        if isinstance(table, Mapping):
            other = plain.to_unicode_str()
            if other in table:
                a, b = table[key], table[other]
                if not (a is b or a == b):
                    raise ValueError(
                        f"{route}: one atom, two entries. The atom {other} is keyed both "
                        f"{key!r} (value {a!r}) and {other!r} (value {b!r}) in this table, "
                        f"and the two values differ. A key written with the bare names of the "
                        f"constants and one written as the text of the formula are two "
                        f"spellings of ONE atom, and the table says two different things "
                        f"about it. Keep one of the two entries.")
        return key
    other = plain.to_unicode_str()
    return other if other in table else None


def find_own_key(table: Container[str], atom: Node) -> Optional[str]:
    """The key under which a table THE KIT BUILT holds ``atom``, or ``None``.

    For a route that fills a table itself, keyed by :func:`atom_key`, and reads it back (the rows
    of a truth table, the assignments an enumeration tries): there is no second spelling to look
    for, and the lookup is as cheap as it was before the formula text of a constant was quoted.
    A table that comes from a caller is read by :func:`find_key`.
    """
    key = atom_key(atom)
    return key if key in table else None


def find_key(keys: Container[str], atom: Node) -> Optional[str]:
    """The key under which ``keys`` holds ``atom``, or ``None``.

    ``keys`` is what a caller's table offers for ``in``: the set of keys true at one world, a
    dict from key to value. The atom is looked up under :func:`atom_key` first (the bare names of
    its constants, ``Likes(a, b)``) and then under its text as a formula
    (``Likes('a', 'b')``), the key a caller gets from ``atom.to_unicode_str()``. An atom whose two
    spellings are one string is looked up once and nothing is rendered a second time.

    Raises:
        ValueError: ``keys`` is a mapping that holds both spellings of the atom with different
            values (one atom, two entries); equal values, or both spellings in a set, are no
            conflict.
        NotImplementedError: as :func:`atom_key`.
    """
    key, plain, quoted = _key(atom, "find_key", NotImplementedError)
    return _locate(keys, key, plain, quoted, "find_key")


def refuse_sorted_constant(atom: Node, route: str,
                           error: Type[Exception] = NotImplementedError) -> None:
    """Refuse an atom that holds a sorted constant, by name.

    For a route that has no reading of what ``c:S`` being an element of ``S`` means for its
    values: reading ``S(c)`` as unrelated to the annotation would answer about another
    problem. ``error`` is the exception class raised (the exception a route already uses for
    the input it refuses).

    Raises:
        NotImplementedError: a sorted constant occurs in ``atom`` (or the class ``error``).
    """
    for sub in atom.walk():
        if isinstance(sub, SortedConstant):
            raise error(
                f"{route}: the sorted constant {sub.to_unicode_str()} in the atom "
                f"{atom.to_unicode_str()!r} has no reading here. {sub.name}:{sub.sort} is the "
                f"constant {sub.name} and lies in the sort {sub.sort}, a fact about the sort "
                f"that this route has no way to state for its values, and reading the atom as "
                f"another letter would answer about another problem. Write the constant "
                f"without its sort, and the fact as an atom ({sub.sort}({sub.name})) if it "
                f"matters.")


def _first_difference(a: Node, b: Node) -> Tuple[Node, Node]:
    """The first pair of corresponding sub-terms of two atoms that are not equal."""
    if isinstance(a, Atom) and isinstance(b, Atom):
        same_head = a.predicate == b.predicate
        a_args, b_args = a.args, b.args
    elif isinstance(a, Function) and isinstance(b, Function):
        same_head = a.name == b.name
        a_args, b_args = a.args, b.args
    else:
        return a, b
    if same_head and len(a_args) == len(b_args):
        for x, y in zip(a_args, b_args):
            if x != y:
                return _first_difference(x, y)
    return a, b


def _why_alike(a: Node, b: Node) -> str:
    """One sentence on why two different terms are written alike."""
    for numeral, constant in ((a, b), (b, a)):
        if isinstance(numeral, Number) and isinstance(constant, Constant):
            return (f"The numeral {numeral.to_unicode_str()} and a constant named "
                    f"{constant.name!r} are one symbol on such a route (a numeral is the "
                    f"constant of its value, written as its digits). Write the number as a "
                    f"constant of another name, or rename the constant.")
    for variable, constant in ((a, b), (b, a)):
        if isinstance(variable, Variable) and isinstance(constant, Constant):
            return (f"A free variable is a parameter, one unknown element of the problem, and "
                    f"not the constant named {variable.name!r}; a symbol named by its text "
                    f"cannot tell them apart. Rename the constant or the variable.")
    return ("They are different terms with one written form, which a letter named by text "
            "cannot tell apart. Rename one of the symbols.")


class AtomKeys:
    """The keys of the atoms of ONE problem, refusing two different atoms with one key.

    Create one per problem and pass every atom of it through :meth:`key`; the first atom
    that has the key of a different atom ends in a ``NotImplementedError`` that names both.
    Two atoms are the same atom when their nodes are equal after each sorted constant has
    been read as the plain constant (``Number(1)`` and ``Number(1.0)`` are one node). A route
    that reads a valuation from its caller passes each atom through :meth:`find` instead, which
    does the same and then looks the atom up in the caller's table under either spelling.

    Args:
        route: what to call the route in a refusal (``'is_tautology'``, ``'int_prove'``).
        sorted_constants: ``"read"`` (the default) keys ``c:S`` as the constant ``c``;
            ``"refuse"`` refuses a sorted constant by name, for a route that has no reading of
            what membership of a sort means for its values.
        error: the exception class a refusal raises, ``NotImplementedError`` by default; a
            route whose callers already handle another class for the input it refuses
            (``ValueError``) names it here.
    """

    def __init__(self, route: str, sorted_constants: str = "read",
                 error: Type[Exception] = NotImplementedError) -> None:
        if sorted_constants not in ("read", "refuse"):
            raise ValueError(f"AtomKeys: sorted_constants must be 'read' or 'refuse', "
                             f"got {sorted_constants!r}.")
        self._route = route
        self._refuse_sorted = sorted_constants == "refuse"
        self._error = error
        self._atoms: Dict[str, Node] = {}

    def key(self, atom: Node) -> str:
        """The key of ``atom``, which is also recorded as the atom that has it.

        Raises:
            NotImplementedError: the atom holds a sorted constant on a route that refuses
                it, the key would hold a complete quoted constant (that of
                ``Constant("'a'")`` is also the formula text of the atom over the constant
                ``a``), or a different atom already has the same key (the class ``error`` of
                the constructor).
        """
        return self._record(atom)[0]

    def find(self, table: Container[str], atom: Node) -> Optional[str]:
        """The key under which a caller's ``table`` holds ``atom``, or ``None``.

        What :func:`find_key` does, after what :meth:`key` does: the atom is recorded and
        checked against the other atoms of the problem first, so the refusal of two different
        atoms with one key keeps working where a route reads a caller's valuation. ``table`` is
        what the caller's valuation offers for ``in`` (a set of keys, a dict from key to value).

        Raises:
            ValueError: ``table`` is a mapping that holds both spellings of the atom (its key
                and its text as a formula) with different values.
            NotImplementedError: as :meth:`key`.
        """
        key, plain, quoted = self._record(atom)
        return _locate(table, key, plain, quoted, self._route)

    def _record(self, atom: Node) -> Tuple[str, Node, bool]:
        """``(key, plain atom, whether its formula text differs)`` of ``atom``, recorded."""
        if self._refuse_sorted:
            refuse_sorted_constant(atom, self._route, self._error)
        key, plain, quoted = _key(atom, self._route, self._error)
        known = self._atoms.setdefault(key, plain)
        if known is not plain and known != plain:
            a, b = _first_difference(known, plain)
            # "have one key": as formulas the two atoms are written differently (a constant
            # named like a variable is written in quotes), and it is the key, the text with
            # every constant written by its name, that they share.
            raise self._error(
                f"{self._route}: two different atoms have one key and are both written "
                f"{key!r}: one has the term {a!r} where the other has {b!r}. This route "
                f"names an atom by its written form, so it would read them as one letter and "
                f"answer about another problem. {_why_alike(a, b)}")
        return key, plain, quoted

    def letters(self, formulas: Iterable[Node]) -> List[str]:
        """The distinct keys of the atoms of ``formulas`` that are letters, in first-seen order.

        The truth constants ``$true`` and ``$false`` are not letters and are left out.
        """
        keys: List[str] = []
        seen = set()
        for formula in formulas:
            for node in formula.walk():
                if isinstance(node, Atom) and truth_value(node) is None:
                    key = self.key(node)
                    if key not in seen:
                        seen.add(key)
                        keys.append(key)
        return keys


def agent_key(agent: Node) -> str:
    """The name of the relation an operator of ``agent`` reads: its name, else its key text.

    A modal operator of an agent (``K_a``, ``B_a``, ``Say_a``, ``Want_a``) reads the relation
    named ``"K:" + agent_key(a)`` (and so on) of a model, the convention of
    :mod:`~unicode_logic_kit.semantics.kripke`. A term without a name of its own (a numeral)
    is keyed by its text with every constant written by its bare name, like an atom.
    """
    return getattr(agent, "name", None) or key_text(agent)


def _agents_of(node: Node) -> Tuple[Node, ...]:
    """The agent terms of one modal operator (none for any other node)."""
    if isinstance(node, (Knows, Believes, Says, Wants)):
        return (node.agent,)
    if isinstance(node, (EverybodyKnows, DistributedKnowledge, CommonKnowledge)):
        return tuple(node.group)
    return ()


def refuse_alike_agents(formulas: Iterable[Node], route: str) -> None:
    """Refuse two different agent terms that would name ONE relation, by name.

    The operators of an agent are named by :func:`agent_key`, so two different terms with one
    key (the numeral ``1`` and the constant ``'1'``; a free variable ``x`` and the constant
    ``x``) would be one agent on a route that files a relation under that name, and a formula
    about two agents would be read as one about a single agent.

    Raises:
        NotImplementedError: two different agent terms of ``formulas`` have one
            :func:`agent_key`.
    """
    agents: Dict[str, Node] = {}
    for formula in formulas:
        for node in formula.walk():
            for agent in _agents_of(node):
                agent = _plain(agent)       # ``a:S`` is the agent ``a``
                key = agent_key(agent)
                known = agents.setdefault(key, agent)
                if known != agent:
                    raise NotImplementedError(
                        f"{route}: two different agents are both named {key!r}: {known!r} "
                        f"and {agent!r}. This route files the operators of an agent under "
                        f"the relation of that name, so it would read them as ONE agent and "
                        f"answer about another problem. {_why_alike(known, agent)}")
