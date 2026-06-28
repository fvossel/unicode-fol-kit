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
emit the resulting plain-FOL formula. Pass ``include_sort_facts=True`` to also conjoin
the sort-membership facts of any sorted constants.

**Equality.** To stay consistent with the rest of the toolkit's HOL layer
(``qml.to_thf_modal``), ``=`` / ``≠`` are emitted as *uninterpreted* binary predicates
(``feq`` / ``fneq``), **not** primitive HOL identity. If you want genuine HOL identity,
post-process the output or add the congruence/identity axioms yourself.

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

from typing import Dict, List, Tuple

from ..fol._symbol_names import dedupe
from ..fol.nodes import (
    Node, Variable, Constant, Number, Function,
    Atom, Not, And, Or, Xor, Implies, Iff, Quantifier,
    SortedQuantifier, to_fol,
)

# Equality / inequality are uninterpreted binary predicates in this toolkit's HOL
# layer (NOT primitive HOL identity), matching qml.to_thf_modal. These aliases give
# them valid, distinct functor / constant names in THF and Isabelle.
_PRED_ALIAS = {"=": "feq", "≠": "fneq", "<": "flt", ">": "fgt", "≤": "fle", "≥": "fge"}

_FORALL = "∀"
_EXISTS = "∃"


# ===========================================================================
# Shared: name sanitisation and signature extraction
# ===========================================================================

def _sanitize(name: str) -> str:
    """Lower-case-initial alphanumeric/underscore functor stem for THF/Isabelle.

    Equality/comparison glyphs map through ``_PRED_ALIAS``; every other character
    that is neither alphanumeric nor underscore becomes an underscore. A leading
    digit is prefixed with ``p`` so the result is a legal lower identifier.

    NOTE: this is *not* injective (e.g. ``'Ab'`` and ``'ab'`` both sanitise to
    ``'ab'``). De-collision is the job of :class:`_SymbolResolver`, which routes
    every declaration AND usage through a unique, valid identifier per symbol.
    Do not emit ``_sanitize`` output directly for a declaration or a usage.
    """
    if name in _PRED_ALIAS:
        return _PRED_ALIAS[name]
    safe = "".join(c if (c.isalnum() or c == "_") else "_" for c in name)
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
            preds.add((n.predicate, len(n.args)))
        elif isinstance(n, Function):
            funcs.add((n.name, len(n.args)))
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
    """

    def __init__(self, formula: Node):
        self._used = set()
        self._map: Dict[Tuple[str, str, int], str] = {}
        preds, funcs, consts = _signature(formula)
        # Assign the equality/comparison alias predicates (=, ≠, …) FIRST so they
        # claim their natural alias names (feq, fneq, …); any user symbol that
        # would sanitise to the same stem is then de-collided away from them. This
        # makes the alias targets collision-proof while keeping = -> feq when there
        # is no competing user 'feq'.
        for name, arity in sorted(preds):
            if name in _PRED_ALIAS:
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
    """

    def __init__(self, render):
        self._render = render          # raw_name -> base token
        self._used = set()
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
    raise NotImplementedError(
        f"to_thf_fol: unsupported term {type(node).__name__} (classical FOL terms only)."
    )


def _thf_formula(node: Node, syms: "_SymbolResolver", vars_: "_VarResolver") -> str:
    """Render a classical FOL formula as a THF ``$o`` term.

    Connectives use the THF/FOF operators (``~ & | => <=> <~>``); quantifiers bind
    individual variables ``! [X: $i]`` / ``? [X: $i]``; atoms apply their declared
    predicate constant with ``@``. Every predicate / function / constant / variable
    name is routed through the resolvers so distinct source symbols stay distinct.
    Anything outside the classical fragment (modal, second-order, Łukasiewicz,
    lambda) raises ``NotImplementedError``.
    """
    def f(n):
        return _thf_formula(n, syms, vars_)
    if isinstance(node, Atom):
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
        "supported by the THF export (no modal / second-order / Łukasiewicz / lambda)."
    )


def _thf_signature_decls(formula: Node, syms: "_SymbolResolver") -> List[str]:
    """Type declarations for every predicate / function / constant in ``formula``.

    Each declaration uses the resolver-assigned identifier, so a symbol is
    declared under exactly the name its usages reference, and distinct symbols
    (including a predicate at two arities) get distinct, single-typed decls.
    """
    preds, funcs, consts = _signature(formula)
    decls: List[str] = []
    for name, arity in sorted(preds):
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


def to_thf_fol(formula: Node, conjecture: bool = True) -> str:
    """Emit a complete TPTP **THF** problem for a classical FOL ``formula``.

    The problem declares the individual type ``$i`` implicitly (TPTP's built-in),
    a typed constant for every predicate / function / constant in the signature,
    and the formula itself. With ``conjecture=True`` (default) the formula is the
    ``conjecture`` — a higher-order ATP (Leo-III, Satallax) reports ``Theorem`` iff
    the formula is valid; with ``conjecture=False`` it is emitted as an ``axiom``
    (e.g. to assert it as a hypothesis in a larger problem).

    Free variables in ``formula`` are universally closed before emission (TPTP
    formula roles do not admit free variables). Equality ``=`` / ``≠`` becomes the
    uninterpreted predicate ``feq`` / ``fneq`` (see module docstring); for genuine
    HOL identity add your own axioms.

    Classical FOL is *semi-decidable only*: a prover may confirm a valid conjecture
    but is not guaranteed to terminate otherwise. This function only emits the
    problem; it does not run any prover.
    """
    closed = formula
    for name in reversed(_free_variables(formula)):
        closed = Quantifier(_FORALL, Variable(name), closed)
    role = "conjecture" if conjecture else "axiom"
    syms = _SymbolResolver(closed)
    vars_ = _VarResolver(lambda raw: _sanitize(raw).upper())
    lines = [
        "% Classical FOL embedded into THF (first-order fragment of HOL).",
        f"% The formula is emitted as the {role}; '$i' is the individual type.",
        "% '=' / '≠' are uninterpreted predicates (feq / fneq), not HOL identity.",
    ]
    lines += _thf_signature_decls(closed, syms)
    lines.append(f"thf(goal, {role}, {_thf_formula(closed, syms, vars_)}).")
    return "\n".join(lines) + "\n"


def to_thf_msfol(formula: Node, conjecture: bool = True,
                 include_sort_facts: bool = True) -> str:
    """Emit a TPTP **THF** problem for a *many-sorted* FOL ``formula`` via guard relativization.

    Each sort becomes a unary guard predicate and each sorted quantifier is
    relativized (``∀x:S φ ↦ ∀x. S(x) → φ``, ``∃x:S φ ↦ ∃x. S(x) ∧ φ``) by the
    toolkit's :func:`~unicode_fol_kit.fol.nodes.to_fol`; the resulting plain-FOL
    formula is then emitted with :func:`to_thf_fol`. With
    ``include_sort_facts=True`` (default) the sort-membership facts of any sorted
    constants are conjoined first, so e.g. ``Mortal(socrates:Human)`` carries
    ``Human(socrates)``. All sorts share the single THF individual type ``$i`` —
    the relativization, not the type system, keeps the sorts apart.
    """
    return to_thf_fol(to_fol(formula, include_sort_facts=include_sort_facts),
                      conjecture=conjecture)


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
    raise NotImplementedError(
        f"to_isabelle_fol: unsupported term {type(node).__name__} (classical FOL terms only)."
    )


def _isa_formula(node: Node, syms: "_SymbolResolver", vars_: "_VarResolver") -> str:
    """Render a classical FOL formula in Isabelle/HOL syntax (fully parenthesised).

    Uses Isabelle's logical-symbol control sequences (``\\<not>``, ``\\<and>`` …)
    and meta/object quantifiers ``\\<forall> x. …`` / ``\\<exists> x. …``. Atoms
    apply their predicate by curried juxtaposition. Xor is rendered as the negated
    biconditional ``\\<not>(l \\<longleftrightarrow> r)``. Every functor / variable
    name is routed through the resolvers so distinct source symbols stay distinct.
    """
    def g(n):
        return _isa_formula(n, syms, vars_)
    if isinstance(node, Atom):
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
        "supported by the Isabelle export (no modal / second-order / Łukasiewicz / lambda)."
    )


def _isa_consts_block(formula: Node, syms: "_SymbolResolver") -> List[str]:
    """``consts`` declarations for every predicate / function / constant.

    Individuals live in a single uninterpreted HOL type ``i``; a k-ary predicate
    has type ``i ⇒ … ⇒ bool`` and a k-ary function ``i ⇒ … ⇒ i``. Each ``consts``
    entry uses the resolver-assigned identifier, so no two declarations share a
    name (no duplicate-``consts`` load error) and every name matches its usages.
    """
    preds, funcs, consts = _signature(formula)
    lines: List[str] = []
    arrow = " \\<Rightarrow> "
    for name, arity in sorted(preds):
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
                    lemma_name: str = "goal", proof: str = "oops") -> str:
    """Emit a loadable **Isabelle/HOL** theory with ``formula`` as a real ``lemma``.

    The theory declares a single uninterpreted individual type ``i`` and a
    ``consts`` entry for every predicate / function / constant in the signature,
    then states the formula as ``lemma <lemma_name>: "⌜formula⌝"`` over those
    uninterpreted symbols. Free variables are left as Isabelle schematic/free
    term variables (HOL closes them implicitly at the lemma level).

    The proof line defaults to ``oops`` (the lemma is *stated* but deliberately
    left open, so the theory loads without claiming a proof). Pass
    ``proof="by auto"``, ``"sledgehammer"``, ``"by blast"``, … to attempt a
    discharge — but note that classical FOL is semi-decidable only, so no tactic
    is guaranteed to close every valid lemma, and this function does not run
    Isabelle. Equality ``=`` / ``≠`` is the uninterpreted predicate ``feq`` /
    ``fneq`` (see module docstring), not HOL ``=``.
    """
    lines = [
        f"theory {theory_name}",
        "  imports Main",
        "begin",
        "",
        "(* Classical FOL embedded into Isabelle/HOL over an uninterpreted",
        "   individual type and uninterpreted predicates/functions/constants.",
        "   '=' / '≠' are the uninterpreted predicates feq / fneq, NOT HOL identity.",
        "   FOL is semi-decidable only: no tactic closes every valid lemma. *)",
        "",
        "typedecl i  \\<comment> \\<open>uninterpreted individuals\\<close>",
    ]
    syms = _SymbolResolver(formula)
    vars_ = _VarResolver(_sanitize)
    lines += _isa_consts_block(formula, syms)
    lines.append("")
    lines.append(f"lemma {lemma_name}: \"{_isa_formula(formula, syms, vars_)}\"")
    lines.append(f"  {proof}")
    lines.append("")
    lines.append("end")
    return "\n".join(lines) + "\n"


def to_isabelle_msfol(formula: Node, theory_name: str = "MSFOL_Export",
                      lemma_name: str = "goal", proof: str = "oops",
                      include_sort_facts: bool = True) -> str:
    """Emit an **Isabelle/HOL** theory for a many-sorted formula via guard relativization.

    Reduces ``formula`` with :func:`~unicode_fol_kit.fol.nodes.to_fol` (each sort
    becomes a unary guard predicate over the single individual type ``i``, each
    sorted quantifier is relativized) and emits the result with
    :func:`to_isabelle_fol`. With ``include_sort_facts=True`` (default) the
    sort-membership facts of sorted constants are conjoined first.
    """
    return to_isabelle_fol(to_fol(formula, include_sort_facts=include_sort_facts),
                           theory_name=theory_name, lemma_name=lemma_name, proof=proof)
