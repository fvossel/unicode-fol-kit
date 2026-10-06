"""Satisfiability / validity checks and model (counterexample) extraction via Z3.

**Many-sorted (MSFOL) soundness.** ``Node.to_z3()`` relativises a sorted
quantifier/constant/count to plain classical FOL (``fol.nodes.to_fol``,
auto-run by ``SortedQuantifier.to_z3`` etc.) but that relativisation alone
does NOT guarantee a sort's universe is non-empty — and MSFOL, by
convention, never gives a sort an empty one (see the classical-reasoning
guide's many-sorted section). Left unaddressed, Z3 is free to interpret a
sort predicate as always-false, which can turn a genuinely valid many-sorted
formula invalid (or a genuinely unsatisfiable one satisfiable) via a
spurious empty-sort "model" no legal MSFOL structure would ever be. The
relativisation likewise reads a sorted constant ``c:S`` as the plain constant
``c``, so it forgets that ``c`` lies in ``S``: ``∀x:Human Mortal(x)`` would
not entail ``Mortal(socrates:Human)``, because ``socrates`` could be outside
``Human``. Every function below closes both gaps the same way: it collects
``unicode_fol_kit.fol._msfl_nodes.sort_axioms(formula)`` — one ``∃x S(x)`` per
sort and one ``S(c)`` per sorted constant — and adds them as their own extra,
UNCONDITIONAL, never-negated assertions on the solver — never folded inside
``to_z3()`` itself, which is polarity-blind and shared with every OTHER caller
(see that function's docstring for why). For an unsorted formula the axiom
list is empty, so the Z3 query — and every one of these functions' return
values — is unchanged by it.
"""

from collections import Counter
from typing import Callable, Dict, List, Optional, Sequence, Tuple

from ..fol._fol_nodes import kit_name_of_z3_symbol, z3_variable_name
from ..fol._msfl_nodes import sort_axioms
from ..fol.nodes import Node, Z3Env
from z3 import Solver, sat, unsat, Not


def declaration_keys(entries: Sequence[Tuple[str, int, str]]) -> List[str]:
    """One key per declaration of a model, ``(name, arity, range)`` each.

    A name that only one declaration carries is its own key, so a model of
    ``P(a)`` still reads ``{"P": ..., "a": ...}``. When several declarations
    share a name (``P(a)`` next to ``P(a, b)``, a function ``f`` next to a
    predicate ``f``, a proposition ``a`` next to a constant ``a``) each is keyed
    by its name and arity, ``"P/1"`` and ``"P/2"``, and when a name and an arity
    still do not tell two apart (a predicate and a function of one name and
    arity) by the sort the declaration returns as well, ``"P/1:Bool"`` and
    ``"P/1:S"``. The keys are pairwise distinct; a key that would meet another
    symbol's own name gets a ``#2``, ``#3``, ... suffix.

    Shared by every route that reads a Z3 model back into a dict and by the
    cvc5 route, so a countermodel names its symbols the same way whichever
    solver found it.
    """
    by_name = Counter(name for name, _, _ in entries)
    by_arity = Counter((name, arity) for name, arity, _ in entries)
    keys: List[Optional[str]] = [name if by_name[name] == 1 else None for name, _, _ in entries]
    taken = {key for key in keys if key is not None}        # a symbol's own name comes first
    for i, (name, arity, range_text) in enumerate(entries):
        if keys[i] is not None:
            continue
        key = (f"{name}/{arity}" if by_arity[(name, arity)] == 1
               else f"{name}/{arity}:{range_text}")
        candidate, n = key, 1
        while candidate in taken:
            n += 1
            candidate = f"{key}#{n}"
        taken.add(candidate)
        keys[i] = candidate
    return keys  # type: ignore[return-value]


def separate_variables(entries: Sequence[Tuple[str, int, str]],
                       is_variable: Sequence[bool]) -> List[Tuple[str, int, str]]:
    """Give each variable among the ``(name, arity, range)`` entries the name it is reported under.

    A free variable ``x`` is a symbol of the model next to the constants. It is reported
    under its own name, ``x``, unless a constant of that name is declared too: then the
    constant keeps ``x`` and the variable is ``x!v``, so that the two are told apart and the
    constant is always found under its plain name. If ``x!v`` is itself the name of another
    symbol (a constant spelled ``x!v``, another variable), the variable is ``x!v!v``, and so on:
    a variable never takes the name of a symbol that is not it, so that no constant loses
    its plain name to a variable. A constant is a symbol of no arguments whose range is not
    ``Bool`` (a proposition is a predicate): the sort ``S``, or a numeric sort.
    """
    names = {name for name, _, _ in entries}
    constants = {name for (name, arity, range_text), variable in zip(entries, is_variable)
                 if not variable and arity == 0 and range_text != "Bool"}
    reported = []
    for (name, arity, range_text), variable in zip(entries, is_variable):
        if variable and name in constants:
            name = z3_variable_name(name)
            while name in names:
                name = z3_variable_name(name)
            names.add(name)
        reported.append((name, arity, range_text))
    return reported


def _kit_entry(decl, ranges: Sequence[str] = ("S",)) -> Tuple[Tuple[str, int, str], bool]:
    """The ``(name, arity, range)`` entry of a declaration of a model, with the kit's name, and
    whether the declaration is a variable. Only a constant of one of the sorts ``ranges`` (the
    uninterpreted sort ``S``, or the numeric sort of the arithmetic route) is written with the
    marks of :func:`~unicode_fol_kit.fol._fol_nodes.kit_name_of_z3_symbol`; every other name is
    the declaration's own."""
    name, arity, range_text = str(decl.name()), decl.arity(), str(decl.range())
    if arity == 0 and range_text in ranges:
        name, variable = kit_name_of_z3_symbol(name)
        return (name, arity, range_text), variable
    return (name, arity, range_text), False


def model_assignment(model, skip: Optional[Callable] = None,
                     ranges: Sequence[str] = ("S",)) -> Dict[str, str]:
    """Read a satisfying ``z3.ModelRef`` into ``{key: interpretation}``.

    Keys are the kit's names of the symbols, told apart by arity (and result sort) only
    where one name is declared more than once — see :func:`declaration_keys`. A constant
    is under its plain name; a free variable (a symbol of its own, see
    :class:`~unicode_fol_kit.fol.nodes.Z3Env`) is under its name too, and as ``x!v`` when a
    constant ``x`` is declared as well (:func:`separate_variables`).
    ``skip(decl)`` leaves out a declaration (the tracking booleans of an
    ``assert_and_track`` call, say) before the keys are chosen, so a skipped
    symbol never makes another one's key longer. ``ranges`` are the sorts of the constants
    and variables of the model: ``("S",)``, or the numeric sort of the arithmetic route.
    """
    decls = [d for d in model.decls() if skip is None or not skip(d)]
    entries = [_kit_entry(d, ranges) for d in decls]
    keys = declaration_keys(separate_variables([e for e, _ in entries], [v for _, v in entries]))
    return {key: str(model[d]) for key, d in zip(keys, decls)}


def _add_sort_axioms(solver: Solver, *formulas: Node, env: Optional[Z3Env] = None) -> None:
    """Assert ``sort_axioms(*formulas)`` on ``solver``, unconditionally.

    Shared by every function in this module so they can never drift apart on
    how the axioms are added (see the module docstring). A no-op — literally
    zero calls to ``solver.add`` — when none of ``formulas`` is many-sorted.
    ``env`` is the environment the formulas themselves were translated with.
    """
    for axiom in sort_axioms(*formulas):
        solver.add(axiom.to_z3(env) if env is not None else axiom.to_z3())


def is_satisfiable(formula: Node, timeout: int = 10000) -> bool:
    """Return True if the formula has a model (Z3 reports sat).

    A Z3 ``unknown`` result (e.g. on hard quantified formulas hitting the
    timeout) is treated as not-known-satisfiable and returns False. A
    many-sorted ``formula``'s sorts are asserted non-empty, and each of its
    sorted constants is asserted to lie in its sort, alongside it — see the
    module docstring.
    """
    solver = Solver()
    solver.set("timeout", timeout)
    solver.set("random_seed", 42)
    env = Z3Env()
    solver.add(formula.to_z3(env))
    _add_sort_axioms(solver, formula, env=env)
    return solver.check() == sat


def is_valid(formula: Node, timeout: int = 10000) -> bool:
    """Return True if the formula is valid, i.e. its negation is unsatisfiable.

    A Z3 ``unknown`` result (e.g. on hard quantified formulas hitting the
    timeout) is treated as not-known-valid and returns False. A many-sorted
    ``formula``'s sorts are asserted non-empty and its sorted constants are
    asserted to lie in their sorts, as extra, UNNEGATED premises alongside the
    negated goal — see the module docstring; this is what makes ``is_valid``
    agree with ``semantics.modelfinder`` on many-sorted input instead of
    exploiting an empty-sort or constant-outside-its-sort loophole modelfinder
    never considers a legal structure. (Asserted outside the negation: were
    ``S(c)`` negated with the goal it would be one more thing to prove.)
    """
    solver = Solver()
    solver.set("timeout", timeout)
    solver.set("random_seed", 42)
    env = Z3Env()
    goal = Not(formula.to_z3(env))
    _add_sort_axioms(solver, formula, env=env)
    solver.add(goal)
    return solver.check() == unsat


def get_model(formula: Node, timeout: int = 10000):
    """Return a satisfying assignment as a dict, or None if unsat/unknown.

    The dict maps each Z3 declaration name (constants, uninterpreted
    functions/predicates) to the string form of its interpretation. A name that
    is declared more than once in the formula (``P(a)`` next to ``P(a, b)``, a
    function and a predicate of one name) is two symbols, and each is reported
    under its own key, ``"P/1"`` and ``"P/2"`` (see :func:`declaration_keys`);
    a name declared once keeps its plain name. For an
    invalid equivalence or entailment, ``get_model(Not(...))`` yields the
    concrete counterexample. Returns None when the formula is unsatisfiable or
    Z3 cannot decide it within the timeout. Every many-sorted node's sort
    anywhere in ``formula`` — including under a ``Not(...)`` a caller wraps
    it in — is asserted non-empty, and every sorted constant anywhere in it is
    asserted to lie in its sort, alongside it, so a returned model is always
    a legal MSFOL structure (see the module docstring); the returned dict may
    therefore also carry an interpretation for a sort's own predicate.
    """
    solver = Solver()
    solver.set("timeout", timeout)
    solver.set("random_seed", 42)
    env = Z3Env()
    solver.add(formula.to_z3(env))
    _add_sort_axioms(solver, formula, env=env)
    if solver.check() != sat:
        return None
    return model_assignment(solver.model())
