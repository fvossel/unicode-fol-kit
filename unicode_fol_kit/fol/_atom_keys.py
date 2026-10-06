"""The key of an atom on a route that identifies an atom by its written form.

A propositional route (a truth table, a many-valued or fuzzy evaluator, the intuitionistic
and counterfactual deciders, a trace of a linear-time formula) takes every ground atom as a
letter of its own and names the letter by the text the atom prints as
(``Atom.to_unicode_str()``: ``'P'``, ``'P(a)'``, ``'Likes(a, b)'``). That is faithful only
while two different atoms never print alike. Two do, and the route would read them as ONE
letter and answer about another problem:

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

from typing import Dict, Iterable, List, Tuple, Type

from ._fol_nodes import Atom, Constant, Function, Node, Number, Variable
from ._modal_nodes import (
    Believes, CommonKnowledge, DistributedKnowledge, EverybodyKnows, Knows, Says, Wants)
from ._msfl_nodes import SortedConstant
from ._truth_constants import truth_value

__all__ = ["atom_key", "plain_atom", "refuse_sorted_constant", "AtomKeys", "agent_key",
           "refuse_alike_agents"]


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
    """The key of an atom: the text it prints as, with a sorted constant ``c:S`` printed as ``c``.

    No check is made that another atom does not print alike; :class:`AtomKeys` does that for
    the atoms of one problem.
    """
    return plain_atom(atom).to_unicode_str()


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
    been read as the plain constant (``Number(1)`` and ``Number(1.0)`` are one node).

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
                it, or a different atom already has the same key (the class ``error`` of the
                constructor).
        """
        if self._refuse_sorted:
            refuse_sorted_constant(atom, self._route, self._error)
        plain = plain_atom(atom)
        key = plain.to_unicode_str()
        known = self._atoms.setdefault(key, plain)
        if known is not plain and known != plain:
            a, b = _first_difference(known, plain)
            raise self._error(
                f"{self._route}: two different atoms are both written {key!r}: one has the "
                f"term {a!r} where the other has {b!r}. This route names an atom by its "
                f"written form, so it would read them as one letter and answer about another "
                f"problem. {_why_alike(a, b)}")
        return key

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
    """The name of the relation an operator of ``agent`` reads: its name, else its written form.

    A modal operator of an agent (``K_a``, ``B_a``, ``Say_a``, ``Want_a``) reads the relation
    named ``"K:" + agent_key(a)`` (and so on) of a model, the convention of
    :mod:`~unicode_fol_kit.semantics.kripke`.
    """
    return getattr(agent, "name", None) or agent.to_unicode_str()


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
