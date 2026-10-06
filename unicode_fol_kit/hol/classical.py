"""Classical FOL / MSFOL → HOL exporters: TPTP **THF** problems and Isabelle/HOL theories.

A classical first-order formula embeds into higher-order logic *trivially*: the
first-order fragment (TPTP ``fof``) is a syntactic subset of typed higher-order
logic (TPTP ``thf``), and likewise sits inside Isabelle/HOL over uninterpreted
constants and predicates. This module turns a toolkit :class:`~unicode_fol_kit.fol.nodes.Node`
into:

* a complete, self-contained TPTP **THF** problem — a single individual type, a
  typed declaration for every predicate / function / constant, and the formula as
  the ``conjecture`` (:func:`to_thf_fol`); and
* a loadable **Isabelle/HOL** theory — the same uninterpreted signature declared
  with ``consts`` and the formula as a real ``lemma`` to be discharged by an
  external prover / Sledgehammer (:func:`to_isabelle_fol`).

**MSFOL (many-sorted FOL).** Two routes map a many-sorted formula into single-sorted
HOL. The *typed* route would give each sort its own HOL type; the *guard-relativization*
route — the one implemented here for robustness — turns each sort into a unary guard
predicate and relativizes the quantifiers (``∀x:S φ ↦ ∀x. S(x) → φ``, ``∃x:S φ ↦
∃x. S(x) ∧ φ``). That reduction is exactly the toolkit's
:func:`~unicode_fol_kit.fol.nodes.to_fol`, so the MSFOL exporters reuse it and then
emit the resulting plain-FOL formula. That reduction forgets two facts the many-sorted
reading carries — no sort is empty, and a sorted constant ``c:S`` is an element of ``S``
(:func:`~unicode_fol_kit.fol.nodes.sort_axioms`) — so the MSFOL exporters state them
(``include_sort_facts=True``, the default). They are stated OUTSIDE the conjecture: a
THF ``axiom`` line per fact, Isabelle hypotheses ``⟦…⟧ ⟹ φ`` of the lemma, a hypothesis
of the Lean theorem. A fact conjoined to the goal itself (``Human(socrates) ∧ φ``) could
never be proved, even for a tautology ``φ``, because the guard is an uninterpreted
predicate. Only a formula that is itself ASSERTED (``conjecture=False``) keeps the
membership facts as a conjunct — there they are part of what is asserted — and gets the
non-emptiness facts as separate ``axiom`` lines. ``include_sort_facts=False`` is the bare
relativisation, with no sort facts at all.

**Equality.** By default, to stay consistent with the rest of the toolkit's HOL layer
(``qml.to_thf_modal``), ``=`` / ``≠`` are emitted as *uninterpreted* binary predicates
(``feq`` / ``fneq``), **not** primitive HOL identity. Pass ``native_equality=True`` to
:func:`to_thf_fol` / :func:`to_isabelle_fol` (and the MSFOL wrappers) to emit ``=`` /
``≠`` as the target logic's own built-in identity instead — TPTP THF's native infix
``=`` / ``!=`` and Isabelle/HOL's polymorphic ``=`` / ``\\<noteq>`` are both genuine,
axiom-free HOL identity at every type (including the uninterpreted individual type
``$i`` / ``i``), so this is a *rendering* choice, not new machinery: no congruence or
reflexivity axiom is generated or needed, because the target format's own ``=``
already validates them. The comparison predicates ``<`` ``>`` ``≤`` ``≥`` are
unaffected by this flag and always stay uninterpreted (``flt``/``fgt``/``fle``/``fge``)
— they have no built-in counterpart in either target. The default remains ``False``
(uninterpreted ``feq``/``fneq``) so existing output is unchanged; if you want genuine
HOL identity without the flag, post-process the output or add the congruence/identity
axioms yourself.

**Honesty / scope.** This module only *emits* problems and theories; it does **not**
run Leo-III, Satallax, Vampire, Isabelle, or Sledgehammer. Classical first-order
logic is **semi-decidable only** (validity is recursively enumerable; invalidity is
not), and the HOL embedding inherits that — a prover may confirm a valid conjecture
but is not guaranteed to terminate on an invalid one. No claim of decision is made:
:func:`to_thf_fol` / :func:`to_isabelle_fol` produce a *sound* problem an external
prover may discharge, nothing more.

Public API: :func:`to_thf_fol`, :func:`to_isabelle_fol`, :func:`to_thf_msfol`,
:func:`to_isabelle_msfol`.
"""

from typing import Dict, List, Sequence, Tuple

from ..fol._fol_nodes import constant_name_to_ascii
from ..fol._numeral_symbols import numerals_as_constants, prefixed_numeral_name
from ..fol._symbol_names import dedupe
from ..fol._truth_constants import truth_value
from ..fol._msfl_nodes import _reduce_nl_nodes
from ..fol.nodes import (
    Node, Variable, Constant, Number, Function, Measure,
    Atom, Not, And, Or, Xor, Implies, Iff, Quantifier,
    SortedQuantifier, to_fol, sort_axioms, nonempty_sort_axioms,
)

# Equality / inequality are uninterpreted binary predicates in this toolkit's HOL
# layer (NOT primitive HOL identity), matching qml.to_thf_modal. These aliases give
# them valid, distinct functor / constant names in THF and Isabelle.
_PRED_ALIAS = {"=": "feq", "≠": "fneq", "<": "flt", ">": "fgt", "≤": "fle", "≥": "fge"}

# The two symbols native_equality=True renders as the target logic's own built-in
# identity (binary use only — a same-named symbol at any OTHER arity is left as an
# ordinary uninterpreted predicate via _PRED_ALIAS, same as when the flag is off).
_NATIVE_EQ_NAMES = {"=", "≠"}

_FORALL = "∀"
_EXISTS = "∃"


def _is_native_eq(name: str, arity: int, native_equality: bool) -> bool:
    """True if ``(name, arity)`` is rendered as the target's built-in identity.

    Only ``=``/``≠`` at their natural binary arity qualify — this bypasses the
    ``feq``/``fneq`` alias (no declaration, no functor application) in favour of
    THF's native infix ``=``/``!=`` or Isabelle's polymorphic ``=``/``\\<noteq>``.
    """
    return native_equality and name in _NATIVE_EQ_NAMES and arity == 2


# ===========================================================================
# Shared: name sanitisation and signature extraction
# ===========================================================================

def _sanitize(name: str) -> str:
    """Lower-case-initial ASCII alphanumeric/underscore functor stem for THF/Isabelle.

    Equality/comparison glyphs map through ``_PRED_ALIAS``. Every other name is
    FIRST transliterated to ASCII with :func:`~unicode_fol_kit.fol._fol_nodes
    .constant_name_to_ascii` — the same transliteration ``Constant.to_tptp`` /
    ``to_prover9`` already use (ASCII passthrough; a Greek letter maps to its
    conventional name; any other non-ASCII character becomes a reversible
    ``uXXXX`` codepoint escape) — and only THEN run through the legacy
    alnum-or-underscore filter. Since ``constant_name_to_ascii`` is the identity
    on a string that is already pure ASCII, this changes nothing for a name that
    was already legal: the underscore/digit-prefix behaviour below is exactly
    what it was before. What it fixes is that ``str.isalnum()`` is ``True`` for
    almost every Unicode letter (``ś``, ``中``, …), so the OLD filter alone let
    those straight through as "harmless" — THF/Isabelle are ASCII-only formats,
    so that was silent corruption, not sanitisation. A leading digit (which can
    now also arise from a transliterated escape, though those always start with
    the ASCII letter ``u``) is still prefixed with ``p`` so the result is a
    legal lower identifier.

    NOTE: this is *not* injective — neither the old filter (``'Ab'``/``'ab'``
    collide) nor ``constant_name_to_ascii`` (a literal ``'theta'`` and the Greek
    ``'θ'`` both fold to ``'theta'``) guarantee that. De-collision is the job of
    :class:`_SymbolResolver` (predicates/functions/constants) and
    :class:`_VarResolver` (variables), which route every declaration AND usage
    through :func:`~unicode_fol_kit.fol._symbol_names.dedupe` to a unique, valid
    identifier per symbol. Do not emit ``_sanitize`` output directly for a
    declaration or a usage.
    """
    if name in _PRED_ALIAS:
        return _PRED_ALIAS[name]
    ascii_name = constant_name_to_ascii(name)
    safe = "".join(c if (c.isalnum() or c == "_") else "_" for c in ascii_name)
    if not safe:
        return "p"
    if safe[0].isdigit():
        safe = "p" + safe
    return safe[:1].lower() + safe[1:]


# Backwards-compatible alias (older call sites / tests may reference ``_safe_name``).
_safe_name = _sanitize


def _signature(formula: Node):
    """Collect (predicates, functions, constants) with arities from ``formula``.

    Returns ``(preds, funcs, consts)`` where ``preds`` and ``funcs`` are sets of
    ``(name, arity)`` pairs — a predicate or function used at *two* arities yields
    *two* distinct entries (each a distinct emitted symbol) — and ``consts`` is a
    set of nullary individual names (plain constants plus numeric literals, the
    latter rendered ``n<value>``). Equality / comparison atoms contribute their
    glyph as an ordinary predicate.
    """
    preds, funcs, consts = set(), set(), set()
    for n in formula.walk():
        if isinstance(n, Atom):
            if truth_value(n) is None:      # `$true` / `$false` are written as THF's / HOL's own
                preds.add((n.predicate, len(n.args)))
        elif isinstance(n, Function):
            funcs.add((n.name, len(n.args)))
        elif isinstance(n, Measure):
            # μ(entity, dimension) is the binary function ``measure`` — the same
            # symbol Measure.to_z3 / to_prover9 / to_tptp emit.
            funcs.add(("measure", 2))
        elif isinstance(n, Constant):
            consts.add(n.name)
        elif isinstance(n, Number):
            consts.add("n" + str(n.value))
    return preds, funcs, consts


# ===========================================================================
# Global symbol resolver — DISTINCT source symbols map to DISTINCT identifiers
# ===========================================================================

# Category tags. Every emitted symbol is keyed by (category, raw_name, arity);
# predicates and functions carry their arity so the SAME raw name used at two
# arities becomes two distinct, distinctly-named emitted symbols.
_CAT_PRED = "pred"
_CAT_FUNC = "func"
_CAT_CONST = "const"


class _SymbolResolver:
    """Assign a UNIQUE, valid emitted identifier to every source symbol.

    Keyed by ``(category, raw_name, arity)``. Distinct source symbols — whether
    they differ by category (a predicate vs. a function vs. a constant sharing a
    raw name), by raw name, or by arity (a predicate used at two arities) — are
    guaranteed distinct emitted identifiers. The ``_PRED_ALIAS`` targets
    (``feq``/``fneq``/…) are reserved up front so a user symbol named ``feq``
    cannot collide with the ``=`` alias.

    Both *declarations* and *usages* must go through :meth:`name`, so a symbol is
    declared and referenced under exactly the same (de-collided) identifier.

    ``native_equality=True`` makes this resolver skip reserving ``feq``/``fneq``
    for the binary ``=``/``≠`` entries (they render as native identity and need no
    identifier at all), which also frees those stems for a user symbol literally
    named ``feq``/``fneq`` — there is no longer an alias target to collide with.
    """

    def __init__(self, formula: Node, native_equality: bool = False):
        self._used = set()
        self._map: Dict[Tuple[str, str, int], str] = {}
        preds, funcs, consts = _signature(formula)
        # Assign the equality/comparison alias predicates (=, ≠, …) FIRST so they
        # claim their natural alias names (feq, fneq, …); any user symbol that
        # would sanitise to the same stem is then de-collided away from them. This
        # makes the alias targets collision-proof while keeping = -> feq when there
        # is no competing user 'feq'. Skip this for a (name, arity) that
        # native_equality renders natively — it needs no alias/identifier.
        for name, arity in sorted(preds):
            if name in _PRED_ALIAS and not _is_native_eq(name, arity, native_equality):
                self._assign(_CAT_PRED, name, arity)
        # Deterministic assignment order so emitted problems are stable.
        for name, arity in sorted(preds):
            if name not in _PRED_ALIAS:
                self._assign(_CAT_PRED, name, arity)
        for name, arity in sorted(funcs):
            self._assign(_CAT_FUNC, name, arity)
        for name in sorted(consts):
            self._assign(_CAT_CONST, name, 0)

    def _assign(self, category: str, raw: str, arity: int) -> str:
        key = (category, raw, arity)
        if key in self._map:
            return self._map[key]
        cand = dedupe(_sanitize(raw), self._used)
        self._map[key] = cand
        return cand

    def name(self, category: str, raw: str, arity: int) -> str:
        """Return the unique emitted identifier for ``(category, raw, arity)``.

        Assigns one on demand (covers any symbol not pre-seeded, e.g. an alias
        target) so declarations and usages always agree.
        """
        key = (category, raw, arity)
        if key not in self._map:
            return self._assign(category, raw, arity)
        return self._map[key]


class _VarResolver:
    """Map DISTINCT bound/free variable names to DISTINCT emitted variable tokens.

    THF upper-cases variable tokens, so distinct source names that differ only in
    case (``x`` vs. ``X``) would otherwise collide on one token. De-collide by
    suffixing while preserving the natural token for the first claimant.

    ``used`` is the set of tokens a variable must not take. THF needs none (a variable is
    upper-case and a functor lower-case, so the two never meet). Isabelle needs the
    functor tokens: its binder ``\\<forall> x.`` shadows a constant ``x`` in its own
    scope, so a variable spelled like a constant of the theory would capture it. The
    set is shared, not copied: a symbol that the functor resolver names later is kept
    off the variables' tokens as well.
    """

    def __init__(self, render, used=None):
        self._render = render          # raw_name -> base token
        self._used = set() if used is None else used
        self._map: Dict[str, str] = {}

    def token(self, raw: str) -> str:
        if raw in self._map:
            return self._map[raw]
        cand = dedupe(self._render(raw), self._used)
        self._map[raw] = cand
        return cand


def _free_variables(formula: Node) -> List[str]:
    """Return the names of variables occurring free in ``formula`` (first-occurrence order).

    Quantifier / SortedQuantifier bind their variable; everything else is structural.
    """
    out: List[str] = []
    seen = set()

    def rec(node: Node, bound: frozenset):
        if isinstance(node, Variable):
            if node.name not in bound and node.name not in seen:
                seen.add(node.name)
                out.append(node.name)
            return
        if isinstance(node, (Quantifier, SortedQuantifier)):
            rec(node.formula, bound | {node.variable.name})
            return
        for child in node._child_nodes():
            rec(child, bound)

    rec(formula, frozenset())
    return out


# ===========================================================================
# (A) TPTP THF export
# ===========================================================================

def _thf_term(node: Node, syms: "_SymbolResolver", vars_: "_VarResolver") -> str:
    """Render an individual (``$i``) term in THF applicative (``@``) form."""
    if isinstance(node, Variable):
        return vars_.token(node.name)
    if isinstance(node, Constant):
        return syms.name(_CAT_CONST, node.name, 0)
    if isinstance(node, Number):
        return syms.name(_CAT_CONST, "n" + str(node.value), 0)
    if isinstance(node, Function):
        head = syms.name(_CAT_FUNC, node.name, len(node.args))
        return "( " + " @ ".join([head] + [_thf_term(a, syms, vars_) for a in node.args]) + " )"
    if isinstance(node, Measure):
        head = syms.name(_CAT_FUNC, "measure", 2)
        return ("( " + " @ ".join([head, _thf_term(node.entity, syms, vars_),
                                   _thf_term(node.dimension, syms, vars_)]) + " )")
    raise NotImplementedError(
        f"to_thf_fol: unsupported term {type(node).__name__} (classical FOL terms only)."
    )


def _thf_formula(node: Node, syms: "_SymbolResolver", vars_: "_VarResolver",
                  native_equality: bool = False) -> str:
    """Render a classical FOL formula as a THF ``$o`` term.

    Connectives use the THF/FOF operators (``~ & | => <=> <~>``); quantifiers bind
    individual variables ``! [X: $i]`` / ``? [X: $i]``; atoms apply their declared
    predicate constant with ``@``. Every predicate / function / constant / variable
    name is routed through the resolvers so distinct source symbols stay distinct.
    Anything outside the classical fragment (modal, second-order, Łukasiewicz,
    lambda) raises ``NotImplementedError``.

    With ``native_equality=True``, a binary ``=``/``≠`` atom renders as THF's own
    infix ``( a = b )`` / ``( a != b )`` instead of applying the ``feq``/``fneq``
    functor — genuine HOL identity, built in at every type, no declaration needed.
    """
    def f(n):
        return _thf_formula(n, syms, vars_, native_equality)
    if isinstance(node, Atom):
        constant = truth_value(node)
        if constant is not None:
            return "$true" if constant else "$false"    # THF's own constants
        if _is_native_eq(node.predicate, len(node.args), native_equality):
            op = "=" if node.predicate == "=" else "!="
            left = _thf_term(node.args[0], syms, vars_)
            right = _thf_term(node.args[1], syms, vars_)
            return f"( {left} {op} {right} )"
        head = syms.name(_CAT_PRED, node.predicate, len(node.args))
        if not node.args:
            return head
        return "( " + " @ ".join([head] + [_thf_term(a, syms, vars_) for a in node.args]) + " )"
    if isinstance(node, Not):
        return f"( ~ {f(node.formula)} )"
    if isinstance(node, And):
        return f"( {f(node.left)} & {f(node.right)} )"
    if isinstance(node, Or):
        return f"( {f(node.left)} | {f(node.right)} )"
    if isinstance(node, Implies):
        return f"( {f(node.left)} => {f(node.right)} )"
    if isinstance(node, Iff):
        return f"( {f(node.left)} <=> {f(node.right)} )"
    if isinstance(node, Xor):
        return f"( {f(node.left)} <~> {f(node.right)} )"
    if isinstance(node, Quantifier):
        x = vars_.token(node.variable.name)
        binder = "!" if node.type in (_FORALL, "forall") else "?"
        return f"( {binder} [{x}: $i] : {f(node.formula)} )"
    raise NotImplementedError(
        f"to_thf_fol: {type(node).__name__} is outside the classical FOL fragment "
        "supported by the THF export (no modal / second-order / Łukasiewicz / "
        "substructural / lambda). Modal family → hol.thf_modal.to_thf_modal_full; "
        "second-order → hol.secondorder.to_thf_so; K3/LP → hol.manyvalued; "
        "ILL/Lambek derivations → hol.isabelle_substructural."
    )


def _thf_signature_decls(formula: Node, syms: "_SymbolResolver",
                         native_equality: bool = False) -> List[str]:
    """Type declarations for every predicate / function / constant in ``formula``.

    Each declaration uses the resolver-assigned identifier, so a symbol is
    declared under exactly the name its usages reference, and distinct symbols
    (including a predicate at two arities) get distinct, single-typed decls.
    A binary ``=``/``≠`` skips its declaration when ``native_equality=True`` —
    THF's built-in identity is polymorphic and needs no type declaration.
    """
    preds, funcs, consts = _signature(formula)
    decls: List[str] = []
    for name, arity in sorted(preds):
        if _is_native_eq(name, arity, native_equality):
            continue
        ident = syms.name(_CAT_PRED, name, arity)
        typ = " > ".join(["$i"] * arity + ["$o"]) if arity else "$o"
        decls.append(f"thf({ident}_decl, type, ( {ident} : ( {typ} ) )).")
    for name, arity in sorted(funcs):
        ident = syms.name(_CAT_FUNC, name, arity)
        typ = " > ".join(["$i"] * (arity + 1))
        decls.append(f"thf({ident}_decl, type, ( {ident} : ( {typ} ) )).")
    for name in sorted(consts):
        ident = syms.name(_CAT_CONST, name, 0)
        decls.append(f"thf({ident}_decl, type, ( {ident} : $i )).")
    return decls


def to_thf_fol(formula: Node, conjecture: bool = True, native_equality: bool = False) -> str:
    """Emit a complete TPTP **THF** problem for a classical FOL ``formula``.

    The problem declares the individual type ``$i`` implicitly (TPTP's built-in),
    a typed constant for every predicate / function / constant in the signature,
    and the formula itself. With ``conjecture=True`` (default) the formula is the
    ``conjecture`` — a higher-order ATP (Leo-III, Satallax) reports ``Theorem`` iff
    the formula is valid; with ``conjecture=False`` it is emitted as an ``axiom``
    (e.g. to assert it as a hypothesis in a larger problem).

    A free variable of a CONJECTURE is closed universally before emission (TPTP formula
    roles do not admit free variables). A free variable is a parameter of the problem, one
    unknown individual, and for a single formula with no premise the two readings
    coincide: the formula is valid for the parameter iff it is valid for every individual.
    An ASSERTED formula (``conjecture=False``) is a premise of a larger problem, and there
    the closure would say more than the formula says: ``∀x P(x)`` entails ``P(a)``, the
    premise ``P(x)`` does not. So an asserted formula with a free variable is refused by
    name; state the parameter with a constant, or bind the variable with a quantifier.

    By default, equality ``=`` / ``≠`` becomes the uninterpreted predicate ``feq`` /
    ``fneq`` (see module docstring);
    pass ``native_equality=True`` to instead emit THF's own built-in infix
    ``=`` / ``!=`` — genuine HOL identity, so congruence/substitutivity for every
    declared function and predicate is free (no axioms to add). The comparison
    predicates ``<`` ``>`` ``≤`` ``≥`` are unaffected either way.

    Classical FOL is *semi-decidable only*: a prover may confirm a valid conjecture
    but is not guaranteed to terminate otherwise. This function only emits the
    problem; it does not run any prover.

    Raises:
        NotImplementedError: ``conjecture`` is false and ``formula`` has a free variable;
            or a numeral and a constant are spelled alike.
    """
    return _thf_problem(formula, conjecture, native_equality)


def _scope(formula: Node, background: Sequence[Node]) -> Node:
    """``formula`` and every background fact as one tree, for signature scans only.

    A problem's declarations and symbol names must cover the sort facts it states
    as well as its formula — a sort that occurs only through a sorted constant is
    mentioned by the fact alone. With no background this is ``formula`` itself, so
    a problem without sort facts is resolved and declared exactly as it was.
    """
    scope = formula
    for fact in background:
        scope = And(scope, fact)
    return scope


def _refuse_open_assertion(formula: Node, conjecture: bool, where: str) -> None:
    """Refuse an ASSERTED ``formula`` that has a free variable, by name.

    A free variable is a parameter of the problem: one unknown individual, the same in
    every formula. Closing it universally is the same thing for a conjecture that stands
    alone (valid for the parameter iff valid for every individual), but an axiom is a
    premise of a larger problem, and ``∀x P(x)`` says more than ``P(x)`` does. So the
    writer states no closure for an axiom and tells the caller how to state the parameter.
    ``where`` is the name of the writer, which the refusal opens with.

    Raises:
        NotImplementedError: ``conjecture`` is false and ``formula`` has a free variable.
    """
    if conjecture:
        return
    free = _free_variables(formula)
    if free:
        names = ", ".join(repr(name) for name in free)
        noun = "variable" if len(free) == 1 else "variables"
        raise NotImplementedError(
            f"{where}: the asserted formula (conjecture=False) has the free {noun} "
            f"{names}, and an axiom cannot say what a free variable stands for. Closing it "
            "universally would assert more than the formula says (a free variable is a "
            "PARAMETER of the problem, one unknown individual shared by every formula: "
            "'∀x P(x)' entails 'P(a)', the premise 'P(x)' does not). State the parameter "
            "yourself: replace the variable by a constant, or bind it with a quantifier, "
            "or emit the formula as the conjecture (conjecture=True), where, for one "
            "formula with no premise, the closure and the parameter reading coincide.")


def _thf_problem(formula: Node, conjecture: bool, native_equality: bool,
                 background: Sequence[Node] = (), where: str = "to_thf_fol") -> str:
    """The THF problem of ``formula``, with ``background`` as ``axiom`` lines before it.

    ``background`` are closed sentences (the many-sorted reading's sort facts, see
    :func:`_msfol_split`). They are named ``nonempty_sort_<i>`` (an ``∃``) and
    ``sort_member_<i>`` (an atom) and come after the type declarations, so a prover
    can use them but never has to prove them. ``where`` names the public writer that
    is calling, for the refusal of an asserted formula that has a free variable.
    """
    formula = _reduce_nl_nodes(formula)   # Contrast → ∧, Count → witnesses
    # A numeral is a constant identified by its value (1 and 1.0 are one), named ``n1``:
    # a user constant spelled like it is refused, not merged with it.
    [formula], _ = numerals_as_constants([formula], where="to_thf_fol",
                                         spell=prefixed_numeral_name)
    _refuse_open_assertion(formula, conjecture, where)
    closed = formula
    for name in reversed(_free_variables(formula)):
        closed = Quantifier(_FORALL, Variable(name), closed)
    role = "conjecture" if conjecture else "axiom"
    scope = _scope(closed, background)
    syms = _SymbolResolver(scope, native_equality=native_equality)
    vars_ = _VarResolver(lambda raw: _sanitize(raw).upper())
    lines = [
        "% Classical FOL embedded into THF (first-order fragment of HOL).",
        f"% The formula is emitted as the {role}; '$i' is the individual type.",
    ]
    # Only the comment differs, and only when '=' / '≠' actually occur at their
    # native binary arity — a formula without them emits byte-identical output
    # whether native_equality is True or False (nothing about it would differ).
    preds, _, _ = _signature(scope)
    if any(_is_native_eq(n, a, native_equality) for n, a in preds):
        lines.append("% '=' / '≠' are THF's native, built-in HOL identity (no axioms needed).")
    else:
        lines.append("% '=' / '≠' are uninterpreted predicates (feq / fneq), not HOL identity.")
    if background:
        lines.append("% The sort facts below are axioms of the problem, not conjuncts of the goal.")
    lines += _thf_signature_decls(scope, syms, native_equality=native_equality)
    nonempty = member = 0
    for fact in background:
        if isinstance(fact, Quantifier):
            name, nonempty = f"nonempty_sort_{nonempty}", nonempty + 1
        else:
            name, member = f"sort_member_{member}", member + 1
        lines.append(f"thf({name}, axiom, "
                     f"{_thf_formula(fact, syms, vars_, native_equality=native_equality)}).")
    lines.append(f"thf(goal, {role}, "
                 f"{_thf_formula(closed, syms, vars_, native_equality=native_equality)}).")
    return "\n".join(lines) + "\n"


def _msfol_split(formula: Node, conjecture: bool,
                 include_sort_facts: bool) -> Tuple[Node, Tuple[Node, ...]]:
    """Split a many-sorted ``formula`` into its plain-FOL image and the sort facts to state beside it.

    The image is :func:`~unicode_fol_kit.fol.nodes.to_fol`: each sort a unary guard
    predicate, each sorted quantifier relativized, each sorted constant its plain
    name. What that forgets is stated separately, by
    :func:`~unicode_fol_kit.fol.nodes.sort_axioms` — no sort is empty, and a sorted
    constant ``c:S`` is an element of ``S``.

    For a CONJECTURE both kinds are returned as background facts, never folded into
    the formula: a conjunct ``S(c) ∧ φ`` could not be proved even for a tautology
    ``φ``. For an asserted formula (``conjecture=False``) the membership atoms are
    part of what is asserted and stay the conjunct ``to_fol`` builds, and only the
    non-emptiness facts are returned. ``include_sort_facts=False`` is the bare
    relativisation, with no facts at all. A formula with no sorted node returns
    ``to_fol(formula)`` and ``()``.
    """
    if not include_sort_facts:
        return to_fol(formula), ()
    if conjecture:
        return to_fol(formula), tuple(sort_axioms(formula))
    return to_fol(formula, include_sort_facts=True), tuple(nonempty_sort_axioms(formula))


def to_thf_msfol(formula: Node, conjecture: bool = True,
                 include_sort_facts: bool = True, native_equality: bool = False) -> str:
    """Emit a TPTP **THF** problem for a *many-sorted* FOL ``formula`` via guard relativization.

    Each sort becomes a unary guard predicate and each sorted quantifier is
    relativized (``∀x:S φ ↦ ∀x. S(x) → φ``, ``∃x:S φ ↦ ∃x. S(x) ∧ φ``) by the
    toolkit's :func:`~unicode_fol_kit.fol.nodes.to_fol`; the resulting plain-FOL
    formula is then emitted as :func:`to_thf_fol` does. With
    ``include_sort_facts=True`` (default) the two facts that reduction forgets are
    stated too (:func:`~unicode_fol_kit.fol.nodes.sort_axioms`): every sort is
    non-empty (``∃x S(x)``) and a sorted constant is in its sort
    (``Mortal(socrates:Human)`` carries ``Human(socrates)``). For a ``conjecture``
    each is a separate THF ``axiom`` (``nonempty_sort_<i>`` / ``sort_member_<i>``) —
    a fact conjoined to the goal, ``Human(socrates) ∧ φ``, could never be proved,
    even for a tautology ``φ`` — so the problem asks whether the formula follows from
    them, which is the many-sorted question. An asserted formula
    (``conjecture=False``) keeps the membership atoms as a conjunct, since they are
    part of what is asserted, and gets the non-emptiness facts as ``axiom`` lines.
    ``include_sort_facts=False`` emits the bare relativisation, no sort facts. All
    sorts share the single THF individual type ``$i`` — the relativization, not the
    type system, keeps the sorts apart. See :func:`to_thf_fol` for ``native_equality``
    and for the free variable of an asserted formula, which is refused by name.

    Raises:
        NotImplementedError: ``conjecture`` is false and ``formula`` has a free variable.
    """
    plain, background = _msfol_split(formula, conjecture, include_sort_facts)
    return _thf_problem(plain, conjecture, native_equality, background, where="to_thf_msfol")


# ===========================================================================
# (B) Isabelle/HOL export
# ===========================================================================

_ISA_BINOP = {And: "\\<and>", Or: "\\<or>", Implies: "\\<longrightarrow>",
              Iff: "\\<longleftrightarrow>"}


def _isa_term(node: Node, syms: "_SymbolResolver", vars_: "_VarResolver") -> str:
    """Render an individual term in Isabelle/HOL term syntax (curried application)."""
    if isinstance(node, Variable):
        return vars_.token(node.name)
    if isinstance(node, Constant):
        return syms.name(_CAT_CONST, node.name, 0)
    if isinstance(node, Number):
        return syms.name(_CAT_CONST, "n" + str(node.value), 0)
    if isinstance(node, Function):
        head = syms.name(_CAT_FUNC, node.name, len(node.args))
        return "(" + " ".join([head] + [_isa_term(a, syms, vars_) for a in node.args]) + ")"
    if isinstance(node, Measure):
        head = syms.name(_CAT_FUNC, "measure", 2)
        return ("(" + " ".join([head, _isa_term(node.entity, syms, vars_),
                                _isa_term(node.dimension, syms, vars_)]) + ")")
    raise NotImplementedError(
        f"to_isabelle_fol: unsupported term {type(node).__name__} (classical FOL terms only)."
    )


def _isa_formula(node: Node, syms: "_SymbolResolver", vars_: "_VarResolver",
                  native_equality: bool = False) -> str:
    """Render a classical FOL formula in Isabelle/HOL syntax (fully parenthesised).

    Uses Isabelle's logical-symbol control sequences (``\\<not>``, ``\\<and>`` …)
    and meta/object quantifiers ``\\<forall> x. …`` / ``\\<exists> x. …``. Atoms
    apply their predicate by curried juxtaposition. Xor is rendered as the negated
    biconditional ``\\<not>(l \\<longleftrightarrow> r)``. Every functor / variable
    name is routed through the resolvers so distinct source symbols stay distinct.

    With ``native_equality=True``, a binary ``=``/``≠`` atom renders as Isabelle's
    own infix ``(a = b)`` / ``(a \\<noteq> b)`` instead of the ``feq``/``fneq``
    consts — genuine, polymorphic HOL identity, no declaration needed.
    """
    def g(n):
        return _isa_formula(n, syms, vars_, native_equality)
    if isinstance(node, Atom):
        constant = truth_value(node)
        if constant is not None:
            return "True" if constant else "False"      # HOL's own constants
        if _is_native_eq(node.predicate, len(node.args), native_equality):
            left = _isa_term(node.args[0], syms, vars_)
            right = _isa_term(node.args[1], syms, vars_)
            op = "=" if node.predicate == "=" else "\\<noteq>"
            return f"({left} {op} {right})"
        head = syms.name(_CAT_PRED, node.predicate, len(node.args))
        if not node.args:
            return head
        return "(" + " ".join([head] + [_isa_term(a, syms, vars_) for a in node.args]) + ")"
    if isinstance(node, Not):
        return f"(\\<not> {g(node.formula)})"
    if type(node) in _ISA_BINOP:
        op = _ISA_BINOP[type(node)]
        return f"({g(node.left)} {op} {g(node.right)})"
    if isinstance(node, Xor):
        inner = f"({g(node.left)} \\<longleftrightarrow> {g(node.right)})"
        return f"(\\<not> {inner})"
    if isinstance(node, Quantifier):
        binder = "\\<forall>" if node.type in (_FORALL, "forall") else "\\<exists>"
        return f"({binder} {vars_.token(node.variable.name)}. {g(node.formula)})"
    raise NotImplementedError(
        f"to_isabelle_fol: {type(node).__name__} is outside the classical FOL fragment "
        "supported by the Isabelle export (no modal / second-order / Łukasiewicz / "
        "substructural / lambda). Modal family → hol.isabelle_modal.to_isabelle_modal; "
        "second-order → hol.secondorder.to_isabelle_so; K3/LP → hol.manyvalued; "
        "ILL/Lambek derivations → hol.isabelle_substructural."
    )


def _isa_consts_block(formula: Node, syms: "_SymbolResolver",
                      native_equality: bool = False) -> List[str]:
    """``consts`` declarations for every predicate / function / constant.

    Individuals live in a single uninterpreted HOL type ``i``; a k-ary predicate
    has type ``i ⇒ … ⇒ bool`` and a k-ary function ``i ⇒ … ⇒ i``. Each ``consts``
    entry uses the resolver-assigned identifier, so no two declarations share a
    name (no duplicate-``consts`` load error) and every name matches its usages.
    A binary ``=``/``≠`` skips its declaration when ``native_equality=True`` —
    Isabelle's polymorphic ``=`` is built in and needs no ``consts`` entry.
    """
    preds, funcs, consts = _signature(formula)
    lines: List[str] = []
    arrow = " \\<Rightarrow> "
    for name, arity in sorted(preds):
        if _is_native_eq(name, arity, native_equality):
            continue
        ident = syms.name(_CAT_PRED, name, arity)
        typ = arrow.join(["i"] * arity + ["bool"]) if arity else "bool"
        lines.append(f"consts {ident} :: \"{typ}\"")
    for name, arity in sorted(funcs):
        ident = syms.name(_CAT_FUNC, name, arity)
        typ = arrow.join(["i"] * (arity + 1))
        lines.append(f"consts {ident} :: \"{typ}\"")
    for name in sorted(consts):
        ident = syms.name(_CAT_CONST, name, 0)
        lines.append(f"consts {ident} :: \"i\"")
    return lines


def to_isabelle_fol(formula: Node, theory_name: str = "FOL_Export",
                    lemma_name: str = "goal", proof: str = "oops",
                    native_equality: bool = False) -> str:
    """Emit a loadable **Isabelle/HOL** theory with ``formula`` as a real ``lemma``.

    The theory declares a single uninterpreted individual type ``i`` and a
    ``consts`` entry for every predicate / function / constant in the signature,
    then states the formula as ``lemma <lemma_name>: "⌜formula⌝"`` over those
    uninterpreted symbols. Free variables are left as Isabelle schematic/free
    term variables (HOL closes them implicitly at the lemma level). The lemma is a
    goal, never an assertion, so a free variable is the parameter it is: one
    individual, for which the lemma holds iff it holds for every individual (the
    refusal that :func:`to_thf_fol` makes for an asserted formula has no counterpart
    here).

    The proof line defaults to ``oops`` (the lemma is *stated* but deliberately
    left open, so the theory loads without claiming a proof). Pass
    ``proof="by auto"``, ``"sledgehammer"``, ``"by blast"``, … to attempt a
    discharge — but note that classical FOL is semi-decidable only, so no tactic
    is guaranteed to close every valid lemma, and this function does not run
    Isabelle. By default, equality ``=`` / ``≠`` is the uninterpreted predicate
    ``feq`` / ``fneq`` (see module docstring), not HOL ``=``; pass
    ``native_equality=True`` to emit Isabelle's own polymorphic ``=`` / ``\\<noteq>``
    instead — genuine HOL identity, so congruence closes by ``simp``/``auto`` with
    no axioms added. The comparison predicates ``<`` ``>`` ``≤`` ``≥`` are
    unaffected either way.
    """
    return _isabelle_problem(formula, theory_name, lemma_name, proof, native_equality)


def _isabelle_problem(formula: Node, theory_name: str, lemma_name: str, proof: str,
                      native_equality: bool, background: Sequence[Node] = ()) -> str:
    r"""The Isabelle theory of ``formula``, with ``background`` as the HYPOTHESES of the lemma.

    ``background`` are closed sentences (the many-sorted reading's sort facts, see
    :func:`_msfol_split`). They are not ``axiomatization`` facts and not conjuncts of
    the goal but premises of the lemma, ``\<lbrakk>f1; f2\<rbrakk> \<Longrightarrow> φ``: a premise is used by
    ``blast`` / ``auto`` / ``metis`` / ``nitpick`` without a ``using`` clause, which an
    ``axiomatization`` fact is not — and the proof battery of
    :func:`~unicode_fol_kit.hol.isabelle_runner.isabelle_decide_fol` names no facts.
    """
    formula = _reduce_nl_nodes(formula)   # Contrast → ∧, Count → witnesses
    # A numeral is a constant identified by its value (1 and 1.0 are one), named ``n1``:
    # a user constant spelled like it is refused, not merged with it.
    [formula], _ = numerals_as_constants([formula], where="to_isabelle_fol",
                                         spell=prefixed_numeral_name)
    scope = _scope(formula, background)
    # Only the comment differs, and only when '=' / '≠' actually occur at their
    # native binary arity — a formula without them emits byte-identical output
    # whether native_equality is True or False (nothing about it would differ).
    preds, _, _ = _signature(scope)
    if any(_is_native_eq(n, a, native_equality) for n, a in preds):
        eq_comment = "   '=' / '≠' are Isabelle's own built-in HOL identity (no axioms needed)."
    else:
        eq_comment = "   '=' / '≠' are the uninterpreted predicates feq / fneq, NOT HOL identity."
    lines = [
        f"theory {theory_name}",
        "  imports Main",
        "begin",
        "",
        "(* Classical FOL embedded into Isabelle/HOL over an uninterpreted",
        "   individual type and uninterpreted predicates/functions/constants.",
        eq_comment,
        "   FOL is semi-decidable only: no tactic closes every valid lemma. *)",
        "",
        "typedecl i  \\<comment> \\<open>uninterpreted individuals\\<close>",
    ]
    syms = _SymbolResolver(scope, native_equality=native_equality)
    # A binder shadows the constants of its own name, so the bound variables take their
    # tokens from the pool the constants, functions and predicates already took theirs from.
    vars_ = _VarResolver(_sanitize, used=syms._used)
    lines += _isa_consts_block(scope, syms, native_equality=native_equality)
    lines.append("")
    statement = _isa_formula(formula, syms, vars_, native_equality=native_equality)
    if background:
        facts = "; ".join(_isa_formula(fact, syms, vars_, native_equality=native_equality)
                          for fact in background)
        statement = f"\\<lbrakk>{facts}\\<rbrakk> \\<Longrightarrow> {statement}"
    lines.append(f"lemma {lemma_name}: \"{statement}\"")
    lines.append(f"  {proof}")
    lines.append("")
    lines.append("end")
    return "\n".join(lines) + "\n"


def to_isabelle_msfol(formula: Node, theory_name: str = "MSFOL_Export",
                      lemma_name: str = "goal", proof: str = "oops",
                      include_sort_facts: bool = True, native_equality: bool = False) -> str:
    """Emit an **Isabelle/HOL** theory for a many-sorted formula via guard relativization.

    Reduces ``formula`` with :func:`~unicode_fol_kit.fol.nodes.to_fol` (each sort
    becomes a unary guard predicate over the single individual type ``i``, each
    sorted quantifier is relativized) and emits the result as
    :func:`to_isabelle_fol` does. With ``include_sort_facts=True`` (default) the two
    facts that reduction forgets are stated too
    (:func:`~unicode_fol_kit.fol.nodes.sort_axioms`): every sort is non-empty
    (``∃x S(x)``) and a sorted constant is in its sort (``Human(socrates)`` for
    ``Mortal(socrates:Human)``). They are HYPOTHESES of the lemma, not conjuncts of
    the goal — ``lemma goal: "⟦∃x. human x; human socrates⟧ ⟹ φ"`` — because a goal
    ``human socrates ∧ φ`` could never be proved, even for a tautology ``φ``, the
    guard being an uninterpreted predicate; and a premise needs no ``using`` clause
    for ``blast`` / ``auto`` / ``nitpick`` to use it. So the lemma asks whether the
    formula follows from the sort facts, which is the many-sorted question.
    ``include_sort_facts=False`` is the bare relativisation, no sort facts. See
    :func:`to_isabelle_fol` for ``native_equality``.
    """
    plain, background = _msfol_split(formula, True, include_sort_facts)
    return _isabelle_problem(plain, theory_name, lemma_name, proof, native_equality,
                             background)
