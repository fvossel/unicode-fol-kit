"""CASL text emission for classical FOL and many-sorted FOL (MSFOL).

`CASL <https://en.wikipedia.org/wiki/Common_Algebraic_Specification_Language>`_
(the Common Algebraic Specification Language) is the CoFI family's central
ASCII, keyword-based specification language; ``libraries`` of CASL ``spec``s
are what `Hets <https://github.com/spechub/Hets>`_ (the Heterogeneous Tool
Set) parses, structures, and hands off to first-order/HOL back-ends. This
module is a one-way EXPORTER only (kit AST -> CASL text): it turns a batch of
the kit's classical FOL / MSFOL formulas into a complete, Hets-parsable
``spec ... end`` block, or a bare formula fragment for embedding in
hand-written CASL. There is no CASL importer here — going the other way needs
a real CASL parser, out of scope for this module.

Scope: classical, two-valued FOL and many-sorted FOL only
-----------------------------------------------------------
CASL's basic first-order layer has no counting quantifiers, no modal/temporal
operators, no second-order quantification, and no substructural connectives —
so this exporter accepts exactly the classical fragment those constructs sit
outside of: :class:`~unicode_fol_kit.fol.nodes.Atom`, :class:`Not`,
:class:`And`, :class:`Or`, :class:`Xor`, :class:`Implies`, :class:`Iff`,
:class:`Quantifier`, :class:`SortedQuantifier` on the formula side, and
:class:`Variable`, :class:`Constant`, :class:`SortedConstant`,
:class:`Function` on the term side. Every OTHER node class the kit knows about
(modal/temporal/epistemic operators, :class:`Count`/:class:`Measure`/
:class:`Cardinality`/:class:`Contrast`/:class:`SortedCount`/
:class:`SortedCardinality`, :class:`Number`, second-order quantifiers,
Lambda/Application, and the linear/Lambek/team-semantic node families) is
REFUSED with a loud :class:`NotImplementedError` naming the offending node
class, per the kit's honesty convention (an unsupported construct is a
precise, actionable error — never a silent mistranslation or a weaker result
than what the input actually says). :func:`_check_fragment` implements this
gate by class-NAME membership in :data:`_ALLOWED_CASL_NODES` rather than an
``isinstance`` chain over dozens of unrelated classes scattered across the
kit's node modules — the gate is meant to reject everything not explicitly
allow-listed, and a name-set is the form that stays correct (rejects) when a
new node class is added elsewhere in the kit and nobody updates this module.
A future richer bridge for the non-classical logics may route through DOL
(the Distributed Ontology, Modelling and Specification Language, CoFI's
heterogeneous layer over CASL/OWL/etc.) instead of a direct CASL emitter —
this module does not attempt that.

``Number`` is deliberately EXCLUDED even though it is a term the classical
grammar can trivially produce (``NUMBER`` is a term-layer alternative), because
CASL's basic library has no built-in numeric sort — a bare literal such as
``3`` would need an ad hoc ``Nat``/``Int`` structuring this module does not
attempt, so it is refused rather than silently emitted as an undeclared term.

Sort inference: a union-find over symbol-position "slots"
-------------------------------------------------------------
A CASL ``ops``/``preds`` block declares the ARGUMENT SORTS of every operation
and predicate symbol — but the kit's classical (unsorted) :class:`Atom` /
:class:`Function` / :class:`Constant` carry no sort annotations at all, and
even :class:`SortedQuantifier` only annotates the BOUND VARIABLE, not every
symbol that variable is later passed to. So before any declaration can be
written, this module infers a single concrete sort for every symbol POSITION
that appears anywhere across the axioms and conjectures being exported, by
propagating the sort annotations that ARE present (:class:`SortedQuantifier`,
:class:`SortedConstant`) through every place a term is passed as an argument.

The inference is a classic union-find (disjoint-set) over a universe of
members of two kinds:

* a SLOT — one of ``("pred", name, i)`` (argument ``i`` of predicate
  ``name``), ``("func", name, i)`` (argument ``i`` of function ``name``),
  ``("func_result", name)`` (the sort of what ``name(...)`` itself denotes as
  a term), or ``("const", name)`` (a constant symbol's own sort);
* a concrete SORT NAME (a plain string) — every string used as a sort
  anywhere (a :class:`SortedQuantifier` sort, a :class:`SortedConstant` sort,
  or ``default_sort``) acts as its own permanently-rooted anchor.

Each formula is walked with a variable environment (``name -> concrete sort``)
built up as quantifiers are entered — :class:`SortedQuantifier` binds its
variable to its own (concrete) sort; a plain (unsorted) :class:`Quantifier`
binds its variable to ``default_sort``; shadowing is scope-correct because the
environment is threaded functionally (a fresh dict per binder, never mutated
in place). Every place two term positions must agree in sort contributes ONE
union: a non-equality :class:`Atom`'s argument ``i`` unifies
``("pred", name, i)`` with that argument's own slot; an equality
:class:`Atom` unifies its two arguments' slots directly with each other; a
:class:`Function`'s argument ``i`` unifies ``("func", name, i)`` with that
argument's slot, and the :class:`Function` application ITSELF (when it occurs
as someone else's argument) contributes the slot ``("func_result", name)``; a
:class:`Variable`'s slot is simply its environment sort (already concrete); a
:class:`Constant`'s slot is ``("const", name)``; a :class:`SortedConstant`
unifies ``("const", name)`` with its own concrete sort immediately.

After every formula has been walked, each union-find equivalence class is
resolved to a single sort: a class containing a concrete sort name uses it (a
class can never legitimately contain TWO DIFFERENT concrete names — that
situation is a genuine sort conflict and is refused immediately, at the
``union`` call that would create it, with a :class:`ValueError` naming both
conflicting sorts and the symbol/position being unified); a class with no
concrete member at all (a symbol never connected, directly or transitively,
to any sort annotation) resolves to ``default_sort``. :class:`_UnionFind`
keeps concrete-sort roots as an INVARIANT (a string member is always its
class's root, never reparented under a slot-tuple root), which is what makes
conflict detection a plain root-equality check rather than a separate
per-class bookkeeping pass.

Two further checks ride along the same walk, both refusals the kit's honesty
convention requires rather than a mistranslation: a predicate or function
name used at two DIFFERENT arities across the exported formulas (CASL has no
notion of a single symbol overloaded across arities in this module's simple
model) raises :class:`ValueError`; and a name used both as a bare
:class:`Constant`/:class:`SortedConstant` and as a :class:`Function`
application raises :class:`ValueError` (this module declares at most one
``ops`` entry per name, so the two uses cannot be reconciled). A free
:class:`Variable` — one never bound by any enclosing quantifier — also
raises :class:`ValueError`: CASL ``. <formula>`` axioms must be closed, so
there is no implicit universal closure or variable declaration to fall back
on here.

Reserved words and identifier hygiene
----------------------------------------
CASL keywords (``sort``, ``pred``, ``forall``, ``not``, …; the exact list is
:data:`_CASL_KEYWORDS`, taken from the CASL Reference Manual's lexical
grammar) may not be used as ordinary identifiers. This module checks every
CONSTANT, FUNCTION, and VARIABLE name it emits against that list (variables
are checked too, even though the kit's grammar restricts a variable to a
single lowercase letter optionally followed by digits — ``[a-z][0-9]*`` — so
in practice a variable can never collide with any of the (all
two-or-more-character) CASL keywords; the check runs anyway, both for
uniformity with the constant/function path and as a safety net if the kit's
variable grammar or the keyword list ever changes) and refuses with
:class:`ValueError` on any collision. ``spec_name`` (the ``spec <NAME> = ...``
header) is validated separately: it must match the simple-identifier pattern
``[A-Za-z][A-Za-z0-9_]*`` and must not itself be a keyword.

Formula emission rules (exact, classical two-valued reading)
------------------------------------------------------------
* Connectives render as CASL's ASCII operators: ``/\\`` (and), ``\\/`` (or),
  ``=>`` (implies), ``<=>`` (iff), ``not <f>`` (negation), ``t = t'``
  (equality). :class:`Xor` has no direct CASL operator, so it is expanded to
  its exact classical reading, ``not (<a> <=> <b>)`` — i.e. XOR-as-negated-IFF,
  the standard truth-functional identity (P XOR Q is true exactly when P and Q
  disagree, i.e. exactly when P IFF Q is false).
* A quantifier renders as ``forall x : Sort . <body>`` / ``exists x : Sort .
  <body>``; a plain (unsorted) :class:`Quantifier` uses ``default_sort`` for
  its bound variable's declared sort.
* Parenthesisation follows one rule, applied uniformly at every non-root
  position: an :class:`Atom` renders bare; a :class:`Not` **of an atom** is
  rendered bare as a connective operand (``not P /\\ Q`` — CASL's ``not``
  binds tightest, so this is unambiguous), while a Not of a COMPOUND gets
  the operand-level parens like any other compound child — yielding e.g.
  ``(not (P /\\ Q)) \\/ R``, where the inner pair is Not self-delimiting
  its own operand and the outer pair is the ordinary child wrap. The outer
  pair is technically redundant (the inner parens already delimit the
  scope) but harmless, and keeping the child rule uniform beats a special
  case (adversarial-review adjudicated: docstring corrected to the actual,
  semantically exact behaviour). As Not's OWN operand the rule is
  narrower: an atom stays bare (``not P``), anything else is wrapped in
  one pair (``not (P /\\ Q)``); every OTHER node
  (And/Or/Xor/Implies/Iff, and — with one exception — Quantifier/
  SortedQuantifier) is wrapped in parens whenever it is not the formula's own
  root. The one exception: a quantifier used as the BODY of an enclosing
  quantifier stays bare (``forall x:S . exists y:T . phi``, no parens) — CASL
  quantifier scope already extends as far right as syntactically possible, so
  chained binders are unambiguous without help, exactly the same reason
  nested parens are never needed between a quantifier and a following
  ``not``. A quantifier used as the operand of a BINARY connective, or as
  Not's operand, IS wrapped (a bare ``P => exists x:S . Q`` would let the
  quantifier's scope run past where the writer intended, so CASL text must
  delimit it explicitly there) — this is also why a binary connective used as
  a quantifier's body is wrapped (``forall x:S . (P => Q)``, never ``forall
  x:S . P => Q``): the worked example in this module's docstring and test
  suite is exactly this shape.
* A 0-ary :class:`Atom` renders as its bare predicate name, both in a formula
  and as a ``preds`` declaration (``Rain : ()``).

``to_casl_spec`` output shape (see the module's tests for the byte-exact
golden cases): a ``spec <name> =`` header; an optional ``sorts`` line (only
if at least one sort is used) with every distinct sort name, alphabetically,
comma-separated on one line; an optional ``ops`` block (constants AND
functions merged into ONE alphabetically-sorted list — a constant's ``ops``
entry is ``name : Sort``, a function's is ``name : Sort1 * … -> Result``);
an optional ``preds`` block (``name : Sort1 * … * Sortn``, or ``name : ()``
for a nullary predicate), alphabetically; each axiom as its own ``. <formula>``
line, each conjecture as its own ``. <formula> %implied`` line (the ``%implied``
annotation is what Hets turns into a proof obligation rather than an assumed
axiom); and a closing ``end``. A section header's entries after the first are
indented to align under the first entry's own column, each non-final entry
suffixed with ``;``. Output is a pure function of the input AST (no
timestamps, no incidental set-iteration-order nondeterminism — every
collection is explicitly sorted before being joined into text), so the same
input always produces byte-identical output.
"""

from dataclasses import dataclass, field
from typing import Dict, Iterable, List, Sequence, Set, Tuple, Union
import re

from .nodes import Node

__all__ = ["to_casl_spec", "formula_to_casl"]


# =============================================================================
# Fragment gate
# =============================================================================

# Exactly the classical FOL / many-sorted-FOL node classes this exporter
# understands. See the module docstring's "Scope" section for why detection
# is by class-NAME membership here rather than an isinstance chain, and why
# Number is excluded despite being a plain classical term.
_ALLOWED_CASL_NODES = frozenset({
    "Variable", "Constant", "SortedConstant", "Function",
    "Atom", "Not", "And", "Or", "Xor", "Implies", "Iff",
    "Quantifier", "SortedQuantifier",
})


def _check_fragment(formula: Node) -> None:
    """Walk ``formula`` and refuse (loudly) the first node outside the
    classical FOL / MSFOL fragment this exporter covers.

    Raises :class:`NotImplementedError` naming the specific offending node
    class. ``Node.walk()`` yields in pre-order, so for a disallowed
    CONSTRUCT (e.g. a :class:`Count` wrapping an otherwise-classical
    formula) the outer, disallowed node itself is what gets named — not
    some allowed node buried inside it.
    """
    for n in formula.walk():
        cls = type(n).__name__
        if cls not in _ALLOWED_CASL_NODES:
            raise NotImplementedError(
                f"CASL export: {cls!r} is outside the classical FOL / "
                "many-sorted FOL fragment this exporter covers (only Atom, "
                "Not, And, Or, Xor, Implies, Iff, Quantifier, SortedQuantifier, "
                "and the term classes Variable, Constant, SortedConstant, "
                "Function are CASL-expressible here). Non-classical logics "
                "(modal/temporal/epistemic operators, counting/measure/"
                "cardinality, second-order quantification, linear/Lambek/"
                "team-semantic connectives, …) may later be routed through a "
                "DOL (Distributed Ontology Language) heterogeneous "
                "translation instead of a direct CASL emitter."
            )


# =============================================================================
# CASL reserved words and identifier validation
# =============================================================================

# The CASL lexical keyword set (case-sensitive; all lowercase), per the CASL
# Reference Manual. None of these may be used as an ordinary sort/op/pred/
# variable identifier.
_CASL_KEYWORDS = frozenset({
    "and", "arch", "as", "assoc", "axiom", "axioms", "closed", "comm", "def",
    "else", "end", "exists", "false", "fit", "forall", "free", "from",
    "generated", "get", "given", "hide", "idem", "if", "in", "lambda",
    "library", "local", "logic", "not", "op", "ops", "pred", "preds",
    "result", "reveal", "sort", "sorts", "spec", "then", "to", "true",
    "type", "types", "unit", "units", "var", "vars", "version", "view",
    "when", "with", "within",
})

_SIMPLE_ID_RE = re.compile(r"[A-Za-z][A-Za-z0-9_]*")


def _check_reserved(name: str, kind: str) -> None:
    """Refuse ``name`` (a ``kind`` identifier — 'constant' / 'function' /
    'variable' / 'predicate' / 'sort') if it collides with a CASL keyword
    or is not a simple CASL word at all.

    Predicates and sorts are checked since the adversarial review: the
    parser's casing rules never apply to directly-constructed AST nodes
    (``Atom("axiom", ())``) or to raw sort strings (``SortedQuantifier``
    annotations, ``default_sort``), and a keyword or malformed identifier
    in ANY emitted position renders a spec HETS cannot parse (verified
    live: HTTP 500 ``unexpected keyword``). See the module docstring's
    "Reserved words" section for why the 'variable' case is checked even
    though it can never fire under the kit's own variable grammar.
    """
    if name in _CASL_KEYWORDS:
        raise ValueError(
            f"CASL export: {kind} name '{name}' collides with the reserved "
            f"CASL keyword '{name}' and cannot be emitted as an identifier."
        )
    if not _SIMPLE_ID_RE.fullmatch(name):
        raise ValueError(
            f"CASL export: {kind} name {name!r} is not a simple CASL "
            "identifier matching [A-Za-z][A-Za-z0-9_]*."
        )


def _validate_spec_name(name: str) -> None:
    """Refuse a ``spec_name`` that is not a simple CASL identifier, or that
    is itself a CASL keyword."""
    if not _SIMPLE_ID_RE.fullmatch(name):
        raise ValueError(
            f"CASL export: spec_name {name!r} is not a simple CASL "
            "identifier matching [A-Za-z][A-Za-z0-9_]*."
        )
    if name in _CASL_KEYWORDS:
        raise ValueError(
            f"CASL export: spec_name {name!r} collides with the reserved "
            f"CASL keyword '{name}'."
        )


# =============================================================================
# Sort inference: union-find over slots and concrete sort names
# =============================================================================

# A "slot" is a tuple key identifying one symbol POSITION whose sort is being
# inferred; a plain str member is a concrete, already-known sort name. See the
# module docstring's "Sort inference" section for the full account.
_Slot = Union[Tuple[str, str, int], Tuple[str, str], str]


class _UnionFind:
    """Weighted union-find over sort-inference slots and concrete sort names.

    Invariant: whenever a class contains a concrete sort name (a plain str
    member), that string is ALWAYS the class's root — union() only ever
    reparents a slot-tuple root onto a string root, never the reverse. That
    invariant is what makes conflict detection O(1) once both roots are
    known: if find(a) and find(b) are both strings and different, the merge
    would put two incompatible concrete sorts in one class.
    """

    def __init__(self) -> None:
        self._parent: Dict[_Slot, _Slot] = {}
        self._rank: Dict[_Slot, int] = {}

    def find(self, x: _Slot) -> _Slot:
        """Return the root of x's class, path-compressing along the way."""
        self._parent.setdefault(x, x)
        path = []
        while self._parent[x] != x:
            path.append(x)
            x = self._parent[x]
        for n in path:
            self._parent[n] = x
        return x

    def union(self, a: _Slot, b: _Slot, context: str) -> None:
        """Merge the classes of ``a`` and ``b``.

        ``context`` names what triggered this merge (a predicate/function
        argument position, an equality, or a sort annotation) and is used
        only to build the error message below.

        Raises :class:`ValueError` if ``a`` and ``b``'s classes each already
        carry a DIFFERENT concrete sort name — an unsatisfiable constraint —
        naming both conflicting sorts and ``context``.
        """
        ra, rb = self.find(a), self.find(b)
        if ra == rb:
            return
        a_concrete, b_concrete = isinstance(ra, str), isinstance(rb, str)
        if a_concrete and b_concrete:
            raise ValueError(
                f"CASL export: sort conflict while resolving {context} — "
                f"inferred both '{ra}' and '{rb}'."
            )
        if a_concrete:
            self._parent[rb] = ra
        elif b_concrete:
            self._parent[ra] = rb
        else:
            rank_a, rank_b = self._rank.get(ra, 0), self._rank.get(rb, 0)
            if rank_a < rank_b:
                ra, rb = rb, ra
            self._parent[rb] = ra
            if rank_a == rank_b:
                self._rank[ra] = rank_a + 1

    def sort_of(self, slot: _Slot, default_sort: str) -> str:
        """Return the concrete sort resolved for ``slot``, or ``default_sort``
        if that slot's class has no concrete member at all."""
        root = self.find(slot)
        return root if isinstance(root, str) else default_sort


@dataclass
class _Signature:
    """Mutable accumulator built by one :func:`_analyze` pass.

    uf            — the union-find carrying every sort-inference constraint.
    pred_arity    — predicate name -> the single arity it is checked against.
    func_arity    — function name -> the single arity it is checked against.
    const_names   — every constant symbol seen (Constant or SortedConstant).
    func_names    — every function symbol seen.
    literal_sorts — every sort name written explicitly in the source (a
                    SortedQuantifier's or SortedConstant's own sort) or
                    implied by a plain Quantifier (default_sort) —
                    independent of whether union-find ever connects that sort
                    to any declared op/pred, so a vacuously-used sort (e.g. a
                    quantified variable that is never passed to anything) is
                    still declared in the spec's ``sorts`` line.
    default_sort  — threaded through so the walk functions don't need it as
                    a separate parameter.
    """

    uf: _UnionFind = field(default_factory=_UnionFind)
    pred_arity: Dict[str, int] = field(default_factory=dict)
    func_arity: Dict[str, int] = field(default_factory=dict)
    const_names: Set[str] = field(default_factory=set)
    func_names: Set[str] = field(default_factory=set)
    literal_sorts: Set[str] = field(default_factory=set)
    default_sort: str = "Thing"


_CONST_VS_FUNCTION = (
    "CASL export: '{name}' is used both as a constant and as a function — "
    "this exporter declares at most one 'ops' entry per name, so the two "
    "uses cannot be reconciled into a single CASL operation symbol."
)


def _infer_term(node: Node, env: Dict[str, str], sig: _Signature) -> _Slot:
    """Process a term node: register its symbol, recurse into any
    sub-terms, and return the union-find slot that represents its sort.

    Raises ValueError on a free variable, an arity conflict, a constant/
    function name clash, or (via ``sig.uf.union``) a sort conflict.
    """
    cls = type(node).__name__

    if cls == "Variable":
        if node.name not in env:
            raise ValueError(
                f"CASL export: free variable '{node.name}' — CASL axioms "
                "must be closed formulas; every variable must be bound by "
                "an enclosing quantifier."
            )
        return env[node.name]

    if cls in ("Constant", "SortedConstant"):
        name = node.name
        if name in sig.func_names:
            raise ValueError(_CONST_VS_FUNCTION.format(name=name))
        sig.const_names.add(name)
        slot: _Slot = ("const", name)
        if cls == "SortedConstant":
            sig.literal_sorts.add(node.sort)
            sig.uf.union(slot, node.sort, f"constant '{name}' sort annotation")
        return slot

    if cls == "Function":
        name = node.name
        if name in sig.const_names:
            raise ValueError(_CONST_VS_FUNCTION.format(name=name))
        arity = len(node.args)
        prev = sig.func_arity.get(name)
        if prev is not None and prev != arity:
            raise ValueError(
                f"CASL export: function '{name}' used with conflicting "
                f"arities {prev} and {arity}."
            )
        sig.func_arity[name] = arity
        sig.func_names.add(name)
        for i, a in enumerate(node.args):
            arg_slot = _infer_term(a, env, sig)
            sig.uf.union(("func", name, i), arg_slot,
                        f"function '{name}' argument {i + 1}")
        return ("func_result", name)

    raise AssertionError(
        f"CASL export: unreachable — term node {cls!r} passed the fragment "
        "check but is not handled by _infer_term."
    )


def _infer_formula(node: Node, env: Dict[str, str], sig: _Signature) -> None:
    """Walk a formula node, threading the bound-variable environment,
    registering every predicate/connective/quantifier constraint into
    ``sig``. Raises ValueError per :func:`_infer_term` and on a predicate
    arity conflict or a malformed equality atom.
    """
    cls = type(node).__name__

    if cls == "Atom":
        if node.predicate == "=":
            if len(node.args) != 2:
                raise ValueError(
                    "CASL export: equality atom must have exactly 2 "
                    f"arguments, got {len(node.args)}."
                )
            s0 = _infer_term(node.args[0], env, sig)
            s1 = _infer_term(node.args[1], env, sig)
            sig.uf.union(s0, s1, "an equality (=) atom")
            return
        arity = len(node.args)
        prev = sig.pred_arity.get(node.predicate)
        if prev is not None and prev != arity:
            raise ValueError(
                f"CASL export: predicate '{node.predicate}' used with "
                f"conflicting arities {prev} and {arity}."
            )
        sig.pred_arity[node.predicate] = arity
        for i, a in enumerate(node.args):
            arg_slot = _infer_term(a, env, sig)
            sig.uf.union(("pred", node.predicate, i), arg_slot,
                        f"predicate '{node.predicate}' argument {i + 1}")
        return

    if cls == "Not":
        _infer_formula(node.formula, env, sig)
        return

    if cls in ("And", "Or", "Xor", "Implies", "Iff"):
        _infer_formula(node.left, env, sig)
        _infer_formula(node.right, env, sig)
        return

    if cls == "Quantifier":
        _check_reserved(node.variable.name, "variable")
        sig.literal_sorts.add(sig.default_sort)
        new_env = dict(env)
        new_env[node.variable.name] = sig.default_sort
        _infer_formula(node.formula, new_env, sig)
        return

    if cls == "SortedQuantifier":
        _check_reserved(node.variable.name, "variable")
        sig.literal_sorts.add(node.sort)
        new_env = dict(env)
        new_env[node.variable.name] = node.sort
        _infer_formula(node.formula, new_env, sig)
        return

    raise AssertionError(
        f"CASL export: unreachable — formula node {cls!r} passed the "
        "fragment check but is not handled by _infer_formula."
    )


def _analyze(formulas: Sequence[Node], default_sort: str) -> _Signature:
    """Run the full validation + sort-inference pipeline over a batch of
    formulas that will share one CASL signature (all the axioms and
    conjectures of a single :func:`to_casl_spec` call, or the single formula
    passed to :func:`formula_to_casl`).

    Every formula is fragment-checked FIRST, across the whole batch, so an
    out-of-fragment node is always reported before any sort-inference error
    that a DIFFERENT, in-fragment formula in the same batch might otherwise
    trigger. Each formula gets its own FRESH variable environment (formulas
    are independent closed statements; a variable named ``x`` in one axiom
    is unrelated to ``x`` in another), but all formulas share one
    :class:`_Signature` (one union-find, one arity/name-clash bookkeeping),
    because they share one CASL ``ops``/``preds`` vocabulary.
    """
    for f in formulas:
        _check_fragment(f)
    # default_sort is validated UNCONDITIONALLY, not only when a quantifier
    # binds it into sig.literal_sorts: the union-find's sort_of() fallback
    # emits it into the `sorts` line for any argument slot never connected
    # to a concrete annotation (e.g. a quantifier-free axiom batch), so a
    # keyword or malformed default_sort would otherwise slip straight into
    # the spec text (adversarial review, Tier 3 — the DolSpec.default_sort
    # route reaches here with an arbitrary caller string).
    _check_reserved(default_sort, "sort")
    sig = _Signature(default_sort=default_sort)
    for f in formulas:
        _infer_formula(f, {}, sig)
    for name in sig.const_names:
        _check_reserved(name, "constant")
    for name in sig.func_names:
        _check_reserved(name, "function")
    # Predicates and sorts are emitted identifiers exactly like constants
    # and functions: a keyword-named predicate (Atom("axiom", ()) built
    # directly on the AST — the parser's casing rule never applies there)
    # or a keyword sort (SortedQuantifier/SortedConstant annotations, or a
    # caller-supplied default_sort, all raw strings) would render a spec
    # HETS cannot parse at all. Review-confirmed live; refuse loudly.
    for name in sig.pred_arity:
        if name != "=":
            _check_reserved(name, "predicate")
    for name in sig.literal_sorts:
        _check_reserved(name, "sort")
    return sig


# =============================================================================
# Formula rendering
# =============================================================================
#
# Three separate "child" contexts, per the module docstring's parenthesisation
# rule — each decides, for the specific node it is about to render, whether
# that node needs an extra pair of parens in THAT position:
#
#   _render_conn_operand — an operand of a binary connective (And/Or/Xor/
#       Implies/Iff): bare only for an Atom or a Not-of-Atom; everything else
#       (another binary connective, a Quantifier/SortedQuantifier, or a
#       Not-of-compound) is wrapped.
#   _render_not_operand  — Not's own operand: bare for an Atom, wrapped for
#       anything else (including another Not, a connective, or a quantifier).
#   _render_quant_body   — a quantifier's body: a binary connective is
#       wrapped (matches _render_conn_operand's blanket rule — this is the
#       'forall x:S . (P => Q)' shape); a nested Quantifier/SortedQuantifier,
#       Atom, or Not stays bare, since quantifier scope (and Not's prefix
#       scope) already extends maximally to the right.
#
# _render(node, default_sort) itself is always called BARE — at the root of
# formula_to_casl's argument, at the root of each to_casl_spec axiom/
# conjecture line, and internally wherever one of the three context helpers
# above has already decided not to wrap. No function here re-wraps its own
# return value; wrapping is applied exactly once, by whichever caller placed
# the node in a non-root position.

_CONN_SYMBOLS = {"And": "/\\", "Or": "\\/", "Implies": "=>", "Iff": "<=>"}


def _quant_keyword(qtype: str) -> str:
    """Map a Quantifier/SortedQuantifier ``type`` field to its CASL keyword."""
    if qtype in ("∀", "forall"):
        return "forall"
    if qtype in ("∃", "exists"):
        return "exists"
    raise ValueError(f"CASL export: unknown quantifier type {qtype!r}.")


def _render_term(node: Node) -> str:
    """Render a term node (Variable / Constant / SortedConstant / Function)."""
    cls = type(node).__name__
    if cls in ("Variable", "Constant", "SortedConstant"):
        return node.name
    if cls == "Function":
        if not node.args:
            # A 0-ary operation is declared like a constant (ops f : S) and
            # must be REFERENCED bare too — 'f()' is not valid CASL term
            # syntax (review-confirmed; mirrors _render_atom's 0-ary rule).
            return node.name
        args = ", ".join(_render_term(a) for a in node.args)
        return f"{node.name}({args})"
    raise NotImplementedError(
        f"CASL export: term node {cls!r} is outside the classical FOL/MSFOL "
        "fragment this exporter supports; non-classical logics may later go "
        "through DOL."
    )


def _render_atom(node: Node) -> str:
    """Render an Atom: infix equality, a 0-ary bare predicate name, or an
    applied predicate."""
    if node.predicate == "=":
        if len(node.args) != 2:
            raise ValueError(
                "CASL export: equality atom must have exactly 2 arguments, "
                f"got {len(node.args)}."
            )
        return f"{_render_term(node.args[0])} = {_render_term(node.args[1])}"
    if not node.args:
        return node.predicate
    args = ", ".join(_render_term(a) for a in node.args)
    return f"{node.predicate}({args})"


def _render(node: Node, default_sort: str) -> str:
    """Render ``node`` bare (no self-wrapping) as CASL formula text."""
    cls = type(node).__name__

    if cls == "Atom":
        return _render_atom(node)

    if cls == "Not":
        return f"not {_render_not_operand(node.formula, default_sort)}"

    if cls in _CONN_SYMBOLS:
        left = _render_conn_operand(node.left, default_sort)
        right = _render_conn_operand(node.right, default_sort)
        return f"{left} {_CONN_SYMBOLS[cls]} {right}"

    if cls == "Xor":
        # Exact classical reading: P XOR Q == not (P <=> Q). See the module
        # docstring's "Formula emission rules".
        left = _render_conn_operand(node.left, default_sort)
        right = _render_conn_operand(node.right, default_sort)
        return f"not ({left} <=> {right})"

    if cls == "Quantifier":
        body = _render_quant_body(node.formula, default_sort)
        return (f"{_quant_keyword(node.type)} {node.variable.name} : "
                f"{default_sort} . {body}")

    if cls == "SortedQuantifier":
        body = _render_quant_body(node.formula, default_sort)
        return (f"{_quant_keyword(node.type)} {node.variable.name} : "
                f"{node.sort} . {body}")

    raise NotImplementedError(
        f"CASL export: formula node {cls!r} is outside the classical "
        "FOL/MSFOL fragment this exporter supports; non-classical logics "
        "may later go through DOL."
    )


def _render_conn_operand(node: Node, default_sort: str) -> str:
    """Render ``node`` as the operand of a binary connective (And/Or/Xor/
    Implies/Iff): bare for an Atom or a Not-of-Atom, else wrapped."""
    cls = type(node).__name__
    if cls == "Atom" or (cls == "Not" and type(node.formula).__name__ == "Atom"):
        return _render(node, default_sort)
    return f"({_render(node, default_sort)})"


def _render_not_operand(node: Node, default_sort: str) -> str:
    """Render ``node`` as Not's own operand: bare for an Atom, else wrapped."""
    if type(node).__name__ == "Atom":
        return _render(node, default_sort)
    return f"({_render(node, default_sort)})"


def _render_quant_body(node: Node, default_sort: str) -> str:
    """Render ``node`` as a quantifier's body: a binary connective (And/Or/
    Xor/Implies/Iff) is wrapped; everything else (Atom, Not, a nested
    Quantifier/SortedQuantifier) stays bare."""
    if type(node).__name__ in _CONN_SYMBOLS or type(node).__name__ == "Xor":
        return f"({_render(node, default_sort)})"
    return _render(node, default_sort)


# =============================================================================
# Declaration synthesis (to_casl_spec only)
# =============================================================================

def _render_op_type(arg_sorts: List[str], result_sort: str) -> str:
    """Render an ``ops`` entry's type: ``Result`` for a 0-ary function
    (indistinguishable in shape from a constant's own type), else
    ``Sort1 * … * Sortn -> Result``."""
    if not arg_sorts:
        return result_sort
    return " * ".join(arg_sorts) + " -> " + result_sort


def _render_pred_type(arg_sorts: List[str]) -> str:
    """Render a ``preds`` entry's type: ``()`` for a 0-ary predicate, else
    ``Sort1 * … * Sortn``."""
    if not arg_sorts:
        return "()"
    return " * ".join(arg_sorts)


def _render_block(keyword: str, entries: List[Tuple[str, str]]) -> str:
    """Render one ``ops``/``preds`` block: ``  <keyword> name : type;`` for
    the first entry, each further entry on its own line indented to align
    under the first entry's own column, every non-final entry ending in
    ``;``. ``entries`` must already be sorted by name."""
    prefix = f"  {keyword} "
    cont_indent = " " * len(prefix)
    last = len(entries) - 1
    lines = []
    for i, (name, type_str) in enumerate(entries):
        text = f"{name} : {type_str}"
        if i != last:
            text += ";"
        lines.append((prefix if i == 0 else cont_indent) + text)
    return "\n".join(lines)


# =============================================================================
# Public API
# =============================================================================

def formula_to_casl(formula: Node, *, default_sort: str = "Thing") -> str:
    """Render a single closed formula as bare CASL formula text, without a
    ``spec`` wrapper.

    This is the same rendering :func:`to_casl_spec` uses for each of its
    ``. <formula>`` lines, for embedding into hand-written CASL.

    Runs the full validation pipeline first (see the module docstring's
    "Sort inference" and "Reserved words" sections): fragment check, free-
    variable check, arity/name-clash checks, and sort-conflict detection —
    even though the resolved sorts themselves are not needed to render a
    bare formula (only :class:`SortedQuantifier`'s own literal sort and
    ``default_sort`` ever appear in the text), the checks still apply,
    because CASL text with a free variable, a reserved-word identifier, or
    an unsatisfiable sort constraint is not valid CASL either way.

    Raises:
        NotImplementedError: ``formula`` contains a node outside the
            classical FOL/MSFOL fragment (see the module docstring's
            "Scope" section).
        ValueError: a free variable, a reserved-word identifier, an arity
            or constant/function-vs-function conflict, or an unsatisfiable
            sort constraint.
    """
    _analyze([formula], default_sort)
    return _render(formula, default_sort)


def to_casl_spec(
    axioms: Iterable[Node],
    *,
    conjectures: Iterable[Node] = (),
    spec_name: str = "KitExport",
    default_sort: str = "Thing",
) -> str:
    """Render ``axioms`` and ``conjectures`` as one complete CASL basic spec:
    ``spec <spec_name> = … end``, Hets-parsable ASCII text.

    ``axioms`` and ``conjectures`` share ONE signature: every predicate,
    function, and constant that appears anywhere across both is declared
    exactly once (sort inference — see the module docstring — runs over the
    whole combined batch). Each axiom becomes its own ``. <formula>`` line;
    each conjecture becomes its own ``. <formula> %implied`` line (the
    ``%implied`` annotation is what turns a formula into a Hets proof
    obligation rather than an assumed axiom). ``sorts``/``ops``/``preds``
    sections are emitted only when non-empty, sorted alphabetically by
    symbol name (``ops`` merges constants and functions into one list).

    Raises:
        ValueError: neither ``axioms`` nor ``conjectures`` contains any
            formula; ``spec_name`` is not a simple identifier or collides
            with a CASL keyword; or any of the sort-inference / identifier
            refusals documented on :func:`formula_to_casl` above.
        NotImplementedError: as :func:`formula_to_casl`.
    """
    _validate_spec_name(spec_name)
    axioms = list(axioms)
    conjectures = list(conjectures)
    all_formulas = axioms + conjectures
    if not all_formulas:
        raise ValueError(
            "CASL export: to_casl_spec needs at least one axiom or "
            "conjecture; an empty spec has no formulas to export."
        )

    sig = _analyze(all_formulas, default_sort)
    declared_sorts: Set[str] = set(sig.literal_sorts)

    op_entries: List[Tuple[str, str]] = []
    for name in sorted(sig.func_names):
        arity = sig.func_arity[name]
        arg_sorts = [sig.uf.sort_of(("func", name, i), default_sort)
                     for i in range(arity)]
        result_sort = sig.uf.sort_of(("func_result", name), default_sort)
        declared_sorts.update(arg_sorts)
        declared_sorts.add(result_sort)
        op_entries.append((name, _render_op_type(arg_sorts, result_sort)))
    for name in sorted(sig.const_names):
        const_sort = sig.uf.sort_of(("const", name), default_sort)
        declared_sorts.add(const_sort)
        op_entries.append((name, const_sort))
    op_entries.sort(key=lambda e: e[0])

    pred_entries: List[Tuple[str, str]] = []
    for name in sorted(sig.pred_arity):
        arity = sig.pred_arity[name]
        arg_sorts = [sig.uf.sort_of(("pred", name, i), default_sort)
                     for i in range(arity)]
        declared_sorts.update(arg_sorts)
        pred_entries.append((name, _render_pred_type(arg_sorts)))

    lines = [f"spec {spec_name} ="]
    if declared_sorts:
        lines.append("  sorts " + ", ".join(sorted(declared_sorts)))
    if op_entries:
        lines.append(_render_block("ops", op_entries))
    if pred_entries:
        lines.append(_render_block("preds", pred_entries))
    for f in axioms:
        lines.append(f"  . {_render(f, default_sort)}")
    for f in conjectures:
        lines.append(f"  . {_render(f, default_sort)} %implied")
    lines.append("end")
    return "\n".join(lines)
