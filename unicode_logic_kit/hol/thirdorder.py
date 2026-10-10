r"""Classical third-order logic → HOL/THF (predicates of properties, mapped natively).

Second-order logic quantifies over predicates; :mod:`unicode_logic_kit.hol.secondorder`
exports that, and a HOL prover takes it directly because a predicate variable is
just a variable at a function type. Third-order logic is the next step and it is
a step in a different direction: a predicate whose ARGUMENT is a predicate —
``Positive(G)``, ``Essence(G, x)``, ``Positive(λx. ¬G(x))``. HOL takes that
directly too, for the same reason, one type higher::

    x           : i                          an individual
    G           : i => bool                  a property
    Positive    : (i => bool) => bool        a predicate OF properties
    Essence     : (i => bool) => i => bool   a relation between a property and an individual

so the embedding is again a translation and not a simulation: an object
quantifier is a HOL ``∀`` at type ``i``, a property quantifier a HOL ``∀`` at
``i => bool``, and an application is an application.

**Where the types come from.** They are not written in the surface syntax. What
each argument slot holds is inferred from the formulas TOGETHER by
:func:`unicode_logic_kit.fol.nodes.analyse_signatures` — ``Positive(G)`` in one
formula and ``G(x)`` in another jointly say that ``Positive`` takes a property
of arity 1 — with bound predicate variables renamed apart first so two local
bindings named ``P`` are never mistaken for one symbol. A property slot that
nothing in the input constrains defaults to arity 1 and is reported, not
silently assumed.

**Standard semantics, as in the second-order module.** The quantifiers range
over the prover's full function space, i.e. standard (full) semantics. Validity
at these orders is not semi-decidable, so an external prover may fail on a valid
conjecture; the kit emits the problem and does not run one. For Henkin
(general-models) semantics, add comprehension axioms yourself — this module does
not do it for you.

**Equality** follows the kit's HOL convention: ``=`` / ``≠`` are the
uninterpreted relations ``feq`` / ``fneq``, not primitive HOL identity.

**Sorts.** A many-sorted formula (``MSFLParser(third_order=True, many_sorted=True)``)
is written in the kit's one-universe reading of sorts: ``∀x:S φ`` as
``∀x (S(x) → φ)``, ``∃x:S φ`` as ``∃x (S(x) ∧ φ)``, ``c:S`` as the constant ``c``,
and the sort as the unary predicate of its name, of type ``i => bool``. Two families
of axioms state what that rewriting drops: ``nonempty_sort<i>`` (no sort is empty)
and ``sort_member<i>`` (a sorted constant lies in its sort). A property and a
predicate quantifier are not sorted: ``∀P`` ranges over ``i => bool`` as before.

**Constants and free variables.** A constant is a particular individual that its name
stands for, and a free variable is a parameter of the problem: one unknown element, the
same in every formula (see :mod:`unicode_logic_kit.fol._free_parameters`). The two are
different symbols even when they are spelled alike, so ``P(x)`` with a free ``x`` and
``P('x')`` are two statements, and each is declared under a name of its own: the second
``x`` is written ``x_2``. A constant is never looked up among the bound variables, so no
binder, of any name, captures it: ``∀x P(x, 'x')`` is written with the bound variable
``X_V`` and the constant ``x`` in THF and with ``x_2`` and ``x`` in Isabelle. A constant of
any name has a legal identifier in the target: a name that is an Isabelle identifier is
written as it is, and any other (``John Doe``, ``G-910``, ``θ``) under the kit's ASCII
stem of it; in THF every name goes through that stem. The identifiers are made unique over
every kind of symbol of the problem, so two names that share a stem (``a b`` and ``a_b``)
are still two symbols.

Public API: :func:`to_thf_to`, :func:`to_isabelle_to`.
"""

from typing import Dict, Optional, Sequence

from ..fol.nodes import (
    Node, Atom, Not, And, Or, Xor, Implies, Iff, Quantifier,
    SecondOrderQuantifier, PredicateTerm,
    Variable, Constant, Function, LambdaVar, Lambda,
    analyse_signatures,
)
from ..fol._ho_nodes import INDIVIDUAL
from ..fol._truth_constants import truth_value
from ._ho_common import (
    UnsupportedHigherOrderNode, EQUALITY, FREE_VARIABLE, CONSTANT, ISABELLE_BUILT_IN,
    peel_lambdas, rename_apart, bound_pred_names, atom_predicates,
    function_symbols, individual_symbols, ThfNames, IsabelleNames, bound_token,
    sorted_reading,
)
from ._isabelle_binders import (
    PREDICATE, VARIABLE, BinderScope, binder_tokens, collect_binders, declared_names,
)

_ALL = r"\<forall>"
_EX = r"\<exists>"
_AND = r"\<and>"
_OR = r"\<or>"
_IMP = r"\<longrightarrow>"
_IFF = r"\<longleftrightarrow>"
_NOT = r"\<not>"
_LAM = r"\<lambda>"
_FUN = r"\<Rightarrow>"
_NEQ = r"\<noteq>"


def _isa_prop_type(arity: int) -> str:
    """Isabelle type of a property of ``arity`` arguments: ``i => … => bool``."""
    return "".join(f"i {_FUN} " for _ in range(arity)) + "bool"


def _isa_slot_type(kind) -> str:
    """Isabelle type of one argument slot: ``i``, or a parenthesised property type."""
    return "i" if kind == INDIVIDUAL else f"({_isa_prop_type(kind[1])})"


def _thf_prop_type(arity: int) -> str:
    """THF type of a property of ``arity`` arguments: ``$i > … > $o``."""
    return " > ".join(["$i"] * arity + ["$o"])


def _thf_slot_type(kind) -> str:
    """THF type of one argument slot."""
    return "$i" if kind == INDIVIDUAL else f"( {_thf_prop_type(kind[1])} )"


# --------------------------------------------------------------------------
# Isabelle
# --------------------------------------------------------------------------

_BINARY_ISA = {And: _AND, Or: _OR, Implies: _IMP, Iff: _IFF}


def _isa_arg(node: Node, arity: Dict[str, int], display: Dict[str, str],
             scope: Optional[BinderScope] = None,
             symbols: Optional[IsabelleNames] = None) -> str:
    """Render a node in ARGUMENT position — an individual term or a property.

    ``scope`` holds the binders that enclose the node and the names they are printed under: a
    variable or a lambda variable bound by one of them is printed under its binder's name. A
    free variable and a constant are not bound by any binder, whatever their spelling: each is
    printed under the name ``symbols`` gives it, and the two have two names. Without a ``scope``
    every binder is printed under its own name.
    """
    if scope is None:
        scope = BinderScope({})
    if symbols is None:
        symbols = IsabelleNames(ISABELLE_BUILT_IN)
    if isinstance(node, (Variable, LambdaVar)):
        # a binder's token is never empty, so "" means: no binder of this name encloses the node
        return scope.token(VARIABLE, node.name, default="") or symbols.symbol(FREE_VARIABLE, node.name)
    if isinstance(node, Constant):
        return symbols.symbol(CONSTANT, node.name)
    if isinstance(node, PredicateTerm):
        return display.get(node.name) or symbols.symbol("predicate", node.name)
    if isinstance(node, Lambda):
        names, body = peel_lambdas(node)
        binders = []
        for name in names:
            token, scope = scope.enter(VARIABLE, name)
            binders.append(f"{_LAM}{token}::i.")
        return f"({' '.join(binders)} {_isa(body, arity, display, scope, symbols)})"
    if isinstance(node, Function):
        head = symbols.symbol("function", node.name)
        args = " ".join(_isa_arg(a, arity, display, scope, symbols) for a in node.args)
        return f"({head} {args})" if args else head
    raise UnsupportedHigherOrderNode(
        f"thirdorder: {type(node).__name__} cannot stand in argument position; an "
        f"argument is an individual term, a predicate name, or a λ-abstraction.")


def _isa(node: Node, arity: Dict[str, int], display: Dict[str, str],
         scope: Optional[BinderScope] = None,
         symbols: Optional[IsabelleNames] = None) -> str:
    """Render ``node`` as an Isabelle/HOL formula.

    ``display`` gives each bound predicate variable the name it is printed under, ``scope`` each
    enclosing object binder (see :mod:`unicode_logic_kit.hol._isabelle_binders`); without a
    ``scope`` every binder is printed under its own name. ``symbols`` names the free symbols
    (predicates, functions, free variables, constants) and is the one the declarations were
    written under.
    """
    if scope is None:
        scope = BinderScope({})
    if symbols is None:
        symbols = IsabelleNames(ISABELLE_BUILT_IN)
    if isinstance(node, Not):
        return f"({_NOT} {_isa(node.formula, arity, display, scope, symbols)})"
    glyph = _BINARY_ISA.get(type(node))
    if glyph is not None:
        left = _isa(node.left, arity, display, scope, symbols)
        right = _isa(node.right, arity, display, scope, symbols)
        return f"({left} {glyph} {right})"
    if isinstance(node, Xor):
        left = _isa(node.left, arity, display, scope, symbols)
        right = _isa(node.right, arity, display, scope, symbols)
        return f"({left} {_NEQ} {right})"
    if isinstance(node, Quantifier):
        binder = _ALL if node.type == "∀" else _EX
        token, inner = scope.enter(VARIABLE, node.variable.name)
        body = _isa(node.formula, arity, display, inner, symbols)
        return f"({binder}{token}::i. {body})"
    if isinstance(node, SecondOrderQuantifier):
        binder = _ALL if node.type == "∀" else _EX
        k = arity.get(node.predicate, node.arity)
        name = display.get(node.predicate, node.predicate)
        body = _isa(node.formula, arity, display, scope, symbols)
        return f"({binder}{name}::{_isa_prop_type(k)}. {body})"
    if isinstance(node, Atom):
        if truth_value(node) is not None:
            return "True" if truth_value(node) else "False"
        if node.predicate in EQUALITY:
            name = EQUALITY[node.predicate]
        else:
            name = display.get(node.predicate) or symbols.symbol("predicate", node.predicate)
        if not node.args:
            return name
        args = " ".join(_isa_arg(a, arity, display, scope, symbols) for a in node.args)
        return f"({name} {args})"
    raise UnsupportedHigherOrderNode(
        f"thirdorder: no reading for {type(node).__name__}. This export covers "
        f"CLASSICAL third-order syntax; modal operators belong to "
        f"hol.ho_modal.to_isabelle_ho_modal.")


def to_isabelle_to(formula: Node, name: str = "TO_Goal",
                   assumptions: Sequence[Node] = (),
                   proof: str = None) -> str:
    """Emit a self-contained Isabelle/HOL theory for a classical third-order formula.

    ``assumptions`` are asserted with ``axiomatization`` and are analysed
    together with ``formula``, so a symbol whose argument types only the
    assumptions determine is still typed correctly. Without a ``proof`` the goal
    is left ``oops`` — the kit states the problem; it does not invent a proof.

    ``name`` becomes the theory name and must be a legal Isabelle identifier.

    A many-sorted problem (``∀x:S``, ``c:S``) is written in the kit's reading of sorts
    (see the module docstring): the formulas relativised, and the facts
    ``nonempty_sort<i>`` and ``sort_member<i>`` as axioms before the assumptions.
    """
    facts, relativised = sorted_reading(list(assumptions) + [formula], "to_isabelle_to")
    formulas = [fact for _, fact in facts] + relativised
    apart, display = rename_apart(formulas)
    signatures = analyse_signatures(apart)
    bound = set()
    for f in apart:
        bound |= bound_pred_names(f)

    lines = [
        "(* Classical third-order logic -> HOL (predicates of properties are native). *)",
        "(* Standard (full) semantics; validity at this order is NOT semi-decidable, *)",
        "(* so a sound prover may fail to close a valid goal. *)",
        f"theory {name}",
        "  imports Main",
        "begin",
        "",
        "typedecl i  \\<comment> \\<open>individuals\\<close>",
        "",
    ]
    predicates = [pred for pred in sorted(signatures.slots)
                  if not (pred in bound or pred in EQUALITY)]
    individuals = individual_symbols(apart)
    aliases = sorted({EQUALITY[p] for f in apart for p in atom_predicates(f) if p in EQUALITY})
    functions = sorted(function_symbols(apart).items())
    # One pool of identifiers for every symbol the theory declares: a constant is never
    # declared under the name of a free variable, a predicate or a function, nor of an alias
    # of the embedding, and a name that is no Isabelle identifier gets one.
    symbols = IsabelleNames(ISABELLE_BUILT_IN | set(aliases))
    symbols.claim([("predicate", pred) for pred in predicates]
                  + [("function", symbol) for symbol, _ in functions] + individuals)
    for pred in predicates:
        arrow = "".join(f"{_isa_slot_type(k)} {_FUN} " for k in signatures.slots[pred])
        lines.append(f'consts {symbols.symbol("predicate", pred)} :: "{arrow}bool"')
    for kind, name in individuals:
        lines.append(f'consts {symbols.symbol(kind, name)} :: "i"')
    for symbol in aliases:
        lines.append(f'consts {symbol} :: "i {_FUN} i {_FUN} bool"')
    for symbol, k in functions:
        arrow = "".join(f"i {_FUN} " for _ in range(k))
        lines.append(f'consts {symbols.symbol("function", symbol)} :: "{arrow}i"')
    lines.append("")
    # A binder shadows a constant of its own spelling inside its scope: every binder (object
    # quantifier, lambda parameter, bound predicate variable) is printed under a name that no
    # declared symbol has. ``display`` gives each renamed-apart predicate variable that name.
    tokens = binder_tokens(collect_binders(formulas), declared_names(lines))
    display = {fresh: tokens[(PREDICATE, original)] for fresh, original in display.items()}
    scope = BinderScope(tokens)
    if signatures.defaulted:
        pairs = ", ".join(f"{p}[{i}]" for p, i in sorted(signatures.defaulted))
        lines.append(f"\\<comment> \\<open>arity defaulted to 1 (nothing in the "
                     f"input fixes it): {pairs}\\<close>")
        lines.append("")
    for (fact_name, _), fact in zip(facts, apart):
        lines.append(f'axiomatization where {fact_name}: '
                     f'"{_isa(fact, signatures.arity, display, scope, symbols)}"')
    for index, assumption in enumerate(apart[len(facts):-1], start=1):
        lines.append(f'axiomatization where assumption{index}: '
                     f'"{_isa(assumption, signatures.arity, display, scope, symbols)}"')
    if len(apart) > 1:
        lines.append("")
    lines.append(f'lemma "{_isa(apart[-1], signatures.arity, display, scope, symbols)}"')
    lines.append(f"  {proof}" if proof else
                 "  oops  \\<comment> \\<open>try: by auto / by blast / sledgehammer\\<close>")
    lines.append("")
    lines.append("end")
    return "\n".join(lines) + "\n"


# --------------------------------------------------------------------------
# THF
# --------------------------------------------------------------------------

_BINARY_THF = {And: "&", Or: "|", Implies: "=>", Iff: "<=>", Xor: "<~>"}


def _thf_arg(node: Node, upper: Dict[str, str], display: Dict[str, str],
             names: ThfNames) -> str:
    """Render a node in ARGUMENT position in THF.

    ``upper`` maps each source name bound in scope to its THF variable token;
    a variable that is not in it is free and spelled through ``names``. A constant
    is never looked up in ``upper``: no binder captures it, whatever its spelling.
    """
    if isinstance(node, (Variable, LambdaVar)):
        return upper.get(node.name) or names.functor(FREE_VARIABLE, node.name)
    if isinstance(node, Constant):
        return names.functor(CONSTANT, node.name)
    if isinstance(node, PredicateTerm):
        return upper.get(node.name) or names.functor("predicate", node.name)
    if isinstance(node, Lambda):
        params, body = peel_lambdas(node)
        fresh = dict(upper)
        for n in params:
            fresh[n] = bound_token(n, "_V", fresh)
        binders = ", ".join(f"{fresh[n]}: $i" for n in params)
        return f"( ^ [{binders}] : {_thf(body, fresh, display, names)} )"
    if isinstance(node, Function):
        functor = names.functor("function", node.name)
        args = " @ ".join(_thf_arg(a, upper, display, names) for a in node.args)
        return f"( {functor} @ {args} )" if node.args else functor
    raise UnsupportedHigherOrderNode(
        f"thirdorder: {type(node).__name__} cannot stand in argument position.")


def _thf(node: Node, upper: Dict[str, str], display: Dict[str, str],
         names: ThfNames) -> str:
    """Render ``node`` as a THF (TH0) formula."""
    if isinstance(node, Not):
        return f"( ~ {_thf(node.formula, upper, display, names)} )"
    glyph = _BINARY_THF.get(type(node))
    if glyph is not None:
        return (f"( {_thf(node.left, upper, display, names)} {glyph} "
                f"{_thf(node.right, upper, display, names)} )")
    if isinstance(node, Quantifier):
        var = bound_token(node.variable.name, "_V", upper)
        fresh = dict(upper, **{node.variable.name: var})
        quant = "!" if node.type == "∀" else "?"
        return f"( {quant} [{var}: $i] : {_thf(node.formula, fresh, display, names)} )"
    if isinstance(node, SecondOrderQuantifier):
        var = bound_token(display.get(node.predicate, node.predicate), "_P", upper)
        fresh = dict(upper, **{node.predicate: var})
        quant = "!" if node.type == "∀" else "?"
        return (f"( {quant} [{var}: {_thf_prop_type(node.arity)}] : "
                f"{_thf(node.formula, fresh, display, names)} )")
    if isinstance(node, Atom):
        if truth_value(node) is not None:
            return "$true" if truth_value(node) else "$false"
        if node.predicate in EQUALITY:
            name = EQUALITY[node.predicate]
        else:
            name = upper.get(node.predicate) or names.functor("predicate", node.predicate)
        if not node.args:
            return name
        args = " @ ".join(_thf_arg(a, upper, display, names) for a in node.args)
        return f"( {name} @ {args} )"
    raise UnsupportedHigherOrderNode(
        f"thirdorder: no THF reading for {type(node).__name__}; this export "
        f"covers classical third-order syntax.")


def to_thf_to(formula: Node, assumptions: Sequence[Node] = (),
              conjecture: bool = True) -> str:
    """Emit a THF (TH0) problem for a classical third-order formula.

    ``assumptions`` become ``axiom`` formulas and are typed together with the
    goal. With ``conjecture=False`` the formula is emitted as an ``axiom``
    instead — the form to hand a model finder when the question is
    satisfiability rather than validity.

    A many-sorted problem is written as in :func:`to_isabelle_to`: the formulas
    relativised, and the facts ``nonempty_sort<i>`` and ``sort_member<i>`` as axioms.
    """
    facts, relativised = sorted_reading(list(assumptions) + [formula], "to_thf_to")
    formulas = [fact for _, fact in facts] + relativised
    apart, display = rename_apart(formulas)
    signatures = analyse_signatures(apart)
    bound = set()
    for f in apart:
        bound |= bound_pred_names(f)

    lines = [
        "% Classical third-order logic -> THF (predicates of properties are native).",
        "% Standard (full) semantics; validity at this order is NOT semi-decidable,",
        "% so a sound prover may fail to close a valid goal.",
    ]
    names = ThfNames(reserved=EQUALITY.values())
    for pred in sorted(signatures.slots):
        if pred in bound or pred in EQUALITY:
            continue
        parts = [_thf_slot_type(k) for k in signatures.slots[pred]]
        thf_type = " > ".join(parts + ["$o"]) if parts else "$o"
        functor = names.functor("predicate", pred)
        lines.append(f"thf({functor}_type, type, ( {functor} : {thf_type} )).")
    for kind, symbol in individual_symbols(apart):
        functor = names.functor(kind, symbol)
        lines.append(f"thf({functor}_type, type, ( {functor} : $i )).")
    for symbol in sorted({EQUALITY[p] for f in apart for p in atom_predicates(f)
                          if p in EQUALITY}):
        lines.append(f"thf({symbol}_type, type, ( {symbol} : $i > $i > $o )).")
    for symbol, k in sorted(function_symbols(apart).items()):
        functor = names.functor("function", symbol)
        lines.append(f"thf({functor}_type, type, ( {functor} : "
                     f"{' > '.join(['$i'] * (k + 1))} )).")
    for (fact_name, _), fact in zip(facts, apart):
        lines.append(f"thf({fact_name}, axiom, ( {_thf(fact, {}, display, names)} )).")
    for index, assumption in enumerate(apart[len(facts):-1], start=1):
        lines.append(f"thf(assumption{index}, axiom, "
                     f"( {_thf(assumption, {}, display, names)} )).")
    role = "conjecture" if conjecture else "axiom"
    lines.append(f"thf(goal, {role}, ( {_thf(apart[-1], {}, display, names)} )).")
    return "\n".join(lines) + "\n"
