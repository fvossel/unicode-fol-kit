"""CASL text emission for classical FOL and many-sorted FOL (MSFOL).

`CASL <https://en.wikipedia.org/wiki/Common_Algebraic_Specification_Language>`_
(the Common Algebraic Specification Language) is the CoFI family's central
ASCII, keyword-based specification language; ``libraries`` of CASL ``spec``s
are what `Hets <https://github.com/spechub/Hets>`_ (the Heterogeneous Tool
Set) parses, structures, and hands off to first-order/HOL back-ends. This
module is the EXPORTER (kit AST -> CASL text): it turns a batch of
the kit's classical FOL / MSFOL formulas into a complete, Hets-parsable
``spec ... end`` block, or a bare formula fragment for embedding in
hand-written CASL. The other direction, for the text this module writes, is
:func:`unicode_logic_kit.fol.casl_import.parse_casl_spec`.

Scope: classical, two-valued FOL and many-sorted FOL only
-----------------------------------------------------------
CASL's basic first-order layer has no counting quantifiers, no modal/temporal
operators, no second-order quantification, and no substructural connectives —
so this exporter accepts exactly the classical fragment those constructs sit
outside of: :class:`~unicode_logic_kit.fol.nodes.Atom`, :class:`Not`,
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
A richer bridge for one non-classical logic — quantified modal logic — DOES
exist, and goes through DOL (the Distributed Ontology, Modelling and
Specification Language, CoFI's heterogeneous layer over CASL/OWL/etc.)
rather than a native "logic Modal" CASL institution:
:func:`unicode_logic_kit.fol.qml.qml_validity_formula` already lowers a modal
formula to exactly this module's classical fragment (the shallow, first-order
"standard translation" — see that module's own docstring), and
:func:`unicode_logic_kit.hets.dol.to_dol_library_from_modal` composes that
translation with THIS module's :func:`to_casl_spec` (sanitising ``qml``'s
auto-generated identifiers first, since those are not always legal CASL) to
hand the result to Hets as a DOL library. Identity needs no translation on
that path any more: ``qml`` keeps an ``=`` atom RIGID and exactly 2-ary — no
world argument — which is precisely CASL's own built-in ``=``, and lowers
``≠`` to ``¬(=)``. The alias that used to rename a world-relativized,
ternary ``=``/``≠`` to a fresh uninterpreted predicate is gone with the
behaviour that produced it; a hand-built non-binary ``=`` is passed through
and refused by this module's own arity check, and a ``≠`` atom is refused by
``hets.dol``'s sanitiser. This module's OWN
fragment gate — and its own exactly-2-ary ``=`` check — is unaffected: it
still refuses every non-classical node, and every malformed equality atom,
it always refused (see :func:`_check_fragment` and :func:`_infer_formula`);
the bridge works by translating the modal formula down to this fragment
BEFORE it ever reaches here, not by widening what this exporter itself
accepts.

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

This is the TYPED reading, and it is stronger than the kit's own. The kit has ONE
universe, a sort is a (non-empty) subset of it, a constant written ``c:S`` is in
``S``, and an unannotated constant, an unsorted variable and the value of a function
are ANY element of the universe: a function has no declared result sort. The
inference above declares an unannotated constant or a function value at the sort of
the position it is used in (``∀x:Human Mortal(x), Mortal(socrates)`` declares
``socrates : Human``), and CASL's sorts are disjoint, so an unsorted quantifier
(typed with ``default_sort``) bounds a sort of its own rather than the universe the
other sorts are subsets of. An export into a typed language keeps writing that
reading, as a designed feature (the round trip through
:mod:`~unicode_logic_kit.fol.casl_import` and the typed worked examples rest on it); a
caller that DECIDES with the text must not take its answer for the kit's. The check that says when the
two readings differ is :func:`~unicode_logic_kit.atp.tptp_tff.check_typed_reading`
(shared with the TF0 and NXF writers), and
:class:`~unicode_logic_kit.atp.hets_backend.HetsBackend` applies it before it asks
Hets, answering ``unknown`` / ``unsupported`` for such a problem.

**The default sort is a sort of its own.** ``default_sort`` (``Thing``) is the sort of every
unsorted quantifier and of every position no annotation reaches. A sort of the SAME name
that the formulas write (``∀x:Thing``, ``c:Thing``) or ``subsorts`` declares would be one
sort with it, so an unsorted position would silently be a position of the user's sort:
``∀x:Thing P(x) ⊢ ∀y P(y)`` would be proved, which the kit's reading (a sort is a part of
the universe) does not say. When the default sort is used at all (an unsorted quantifier,
or a symbol connected to no annotation) and a sort of that name is also written, the
export is refused by name, and the refusal names the keyword that picks another default
sort: ``default_sort=`` of :func:`to_casl_spec` and :func:`formula_to_casl`
(``DolSpec.default_sort`` in :mod:`~unicode_logic_kit.hets.dol`).
:class:`~unicode_logic_kit.atp.hets_backend.HetsBackend` picks a default sort that no sort
of the problem has, so it never meets the refusal.

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

Bound variables and the symbols of the spec
----------------------------------------------
CASL text writes a bound variable, a constant (a 0-ary operation) and a predicate as
one identifier, compared exactly (``w`` and ``W`` are two names), and inside a
quantifier the name of its variable is the variable: ``forall w : Thing . (P(w) =>
Q(w))`` next to ``ops w : Thing`` says nothing about a constant ``w``, whatever the
formula was. So a bound variable that is spelled like ANY symbol of the whole spec (a
constant, a function, a predicate, a sort, the default sort) is renamed to a fresh
variable name, fresh against every name the formulas hold, in its quantifier and in
every occurrence it binds (``forall w0 : Thing . (P(w0) => Q(w))``). Text without such
a clash is byte-identical to what it was before. The renaming is an alpha-conversion
of a closed sentence, so the text means the formula; read back through
:func:`~unicode_logic_kit.fol.casl_import.parse_casl_spec` it is the same formula up to
the names of the variables that had to be renamed. :func:`to_casl_spec` and
:func:`formula_to_casl` take ``visible_symbols`` for the symbols the text meets
without declaring them.

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
* The truth constants ``$true`` / ``$false`` render as CASL's own formulas
  ``true`` / ``false`` and declare no predicate.

``to_casl_spec`` output shape (see the module's tests for the byte-exact
golden cases): a ``spec <name> =`` header; an optional ``sorts`` line (only
if at least one sort is used) with every distinct sort name, alphabetically,
comma-separated on one line; when ``subsorts`` is given (see below), one
further ``sort <child> < <parent>`` line per DIRECT edge, in
``(child, parent)`` order — one line per edge even when a child has several
parents or several children share one parent, never CASL's list-sharing form
(``sort S1, S2 < T``), which keeps the emitted grammar a strict subset of
what :mod:`unicode_logic_kit.fol.casl_import` already parses one edge at a
time; an optional ``ops`` block (constants AND functions merged into ONE
alphabetically-sorted list — a constant's ``ops`` entry is ``name : Sort``,
a function's is ``name : Sort1 * … -> Result``);
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

from dataclasses import dataclass, field, replace
from typing import Dict, FrozenSet, Iterable, List, Mapping, Optional, Sequence, Set, Tuple, Union
import re

from .nodes import Node, SortedConstant, SortedQuantifier, Variable
from ._identifiers import fresh_variable_like, symbol_names
from ._truth_constants import truth_value
# Shared arity-conflict / constant-vs-function name-clash refusal, factored
# out into unicode_logic_kit.fol.signature so this module's independently-
# accumulated bookkeeping (see _Signature's docstring) and Signature.
# from_formulas's own arity/name-clash refusals come from one tested
# comparison-and-raise, even though each keeps its own accumulation
# strategy and message wording — see signature.py's module docstring's
# DESIGN NOTE.
from .signature import _check_single_valued, _check_not_dual_use

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
                "Function are CASL-expressible here). Quantified modal logic "
                "already has a route to CASL/DOL/Hets: translate the RAW modal "
                "formula first with unicode_logic_kit.fol.qml.qml_validity_formula "
                "(the standard translation to this classical fragment), then "
                "hand it to unicode_logic_kit.hets.dol.to_dol_library_from_modal — "
                "do not pass a modal node (Box/Diamond/…) to this exporter "
                "directly. Every other non-classical logic (counting/measure/"
                "cardinality, second-order quantification, linear/Lambek/"
                "team-semantic connectives, …) has no such route yet and may "
                "later be routed through a DOL (Distributed Ontology Language) "
                "heterogeneous translation instead of a direct CASL emitter."
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
    #: the sorts the caller wrote (a SortedQuantifier's or a SortedConstant's), never the
    #: default sort that a plain Quantifier implies
    user_sorts: Set[str] = field(default_factory=set)
    #: whether a plain Quantifier typed a variable with the default sort
    default_quantified: bool = False


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
        _check_not_dual_use(name, sig.func_names, _CONST_VS_FUNCTION.format(name=name))
        sig.const_names.add(name)
        slot: _Slot = ("const", name)
        if cls == "SortedConstant":
            # _check_fragment admits a node only by class name, and SortedConstant is the
            # one class of that name in the node hierarchy.
            assert isinstance(node, SortedConstant)
            sig.literal_sorts.add(node.sort)
            sig.user_sorts.add(node.sort)
            sig.uf.union(slot, node.sort, f"constant '{name}' sort annotation")
        return slot

    if cls == "Function":
        name = node.name
        _check_not_dual_use(name, sig.const_names, _CONST_VS_FUNCTION.format(name=name))
        arity = len(node.args)
        prev = sig.func_arity.get(name)
        if prev is not None:
            _check_single_valued(
                {prev, arity},
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
        if truth_value(node) is not None:
            return                       # CASL's own `true` / `false`: no predicate
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
        if prev is not None:
            _check_single_valued(
                {prev, arity},
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
        sig.default_quantified = True
        new_env = dict(env)
        new_env[node.variable.name] = sig.default_sort
        _infer_formula(node.formula, new_env, sig)
        return

    if cls == "SortedQuantifier":
        # Same invariant as for SortedConstant in _infer_term.
        assert isinstance(node, SortedQuantifier)
        _check_reserved(node.variable.name, "variable")
        sig.literal_sorts.add(node.sort)
        sig.user_sorts.add(node.sort)
        new_env = dict(env)
        new_env[node.variable.name] = node.sort
        _infer_formula(node.formula, new_env, sig)
        return

    raise AssertionError(
        f"CASL export: unreachable — formula node {cls!r} passed the "
        "fragment check but is not handled by _infer_formula."
    )


def _analyze(formulas: Sequence[Node], default_sort: str,
             declared_sorts: Iterable[str] = ()) -> _Signature:
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

    ``declared_sorts`` are sorts the caller declares without a formula (the names of the
    ``subsorts`` edges); like the sorts the formulas write they must not be the default
    sort when that is used (:func:`_check_default_sort_is_free`).
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
    _check_default_sort_is_free(sig, declared_sorts)
    return sig


#: A sort name no caller can write (it is not an identifier): marks a slot no annotation reaches.
_NO_SORT = "\0"


def _default_sort_is_used(sig: _Signature) -> bool:
    """Whether the default sort types anything: a variable of a plain quantifier, or a
    symbol position that no sort annotation reaches (:meth:`_UnionFind.sort_of` falls back
    to the default sort for it)."""
    if sig.default_quantified:
        return True
    slots: List[_Slot] = [("const", name) for name in sig.const_names]
    for name, arity in sig.func_arity.items():
        slots.append(("func_result", name))
        slots.extend(("func", name, i) for i in range(arity))
    for name, arity in sig.pred_arity.items():
        if name != "=":
            slots.extend(("pred", name, i) for i in range(arity))
    return any(sig.uf.sort_of(slot, _NO_SORT) == _NO_SORT for slot in slots)


def _check_default_sort_is_free(sig: _Signature, declared_sorts: Iterable[str]) -> None:
    """Refuse a sort the caller wrote that is spelled like the default sort, when the
    default sort is used (see the module docstring, "The default sort is a sort of its own").

    Raises:
        ValueError: such a sort exists; the message names it and the keyword that picks
            another default sort.
    """
    written = sig.user_sorts | set(declared_sorts)
    if sig.default_sort in written and _default_sort_is_used(sig):
        raise ValueError(
            f"CASL export: the sort {sig.default_sort!r} is written in the formulas (or "
            f"declared in subsorts) and is also the default sort, which this exporter gives "
            "every unsorted quantifier and every position no sort annotation reaches, so the "
            "two would be ONE sort and an unsorted position would silently become a position "
            f"of your sort {sig.default_sort!r} (∀x:{sig.default_sort} P(x) ⊢ ∀y P(y) would "
            "be proved). Pick another default sort with the keyword default_sort= of "
            "to_casl_spec / formula_to_casl (DolSpec.default_sort in hets.dol), for "
            f"example default_sort={sig.default_sort + '1'!r}.")


# =============================================================================
# Bound variables against the symbols of the specification
# =============================================================================
#
# In CASL text a bound variable, a constant (a 0-ary operation) and a predicate are
# all written as one identifier, and identifiers are compared exactly (``w`` and ``W``
# are two names, as :func:`~unicode_logic_kit.fol.casl_import.parse_casl_spec` reads
# them). ``forall w : Thing . (P(w) => Q(w))`` therefore cannot say that ``Q`` is
# applied to a constant ``w``: inside the quantifier the name is the variable. A
# binder is renamed when its name is the name of any symbol of the specification, and
# only then, so text without such a clash is unchanged.

def _specification_symbols(sig: _Signature, extra: Iterable[str] = ()) -> FrozenSet[str]:
    """Every name of the specification that a bound variable must not share: the constants,
    functions and predicates it declares, every sort it names, the default sort, and the
    names in ``extra`` (sorts declared by ``subsorts``, symbols visible from outside)."""
    names: Set[str] = set(sig.const_names) | set(sig.func_names)
    names.update(name for name in sig.pred_arity if name != "=")
    names.update(sig.literal_sorts)
    names.update(sig.user_sorts)
    names.update(extra)
    names.add(sig.default_sort)
    return frozenset(names)


def _bind_apart(formulas: Sequence[Node], symbols: FrozenSet[str]) -> List[Node]:
    """``formulas`` with every bound variable that is spelled like one of ``symbols`` renamed.

    A binder whose name is in ``symbols`` is renamed to a fresh variable name (the same
    one the occurrences it binds are rewritten to), fresh against every name any of the
    formulas holds, against ``symbols``, and against every name minted before it. Every
    other binder and every other node is kept as it is, and when no binder clashes the
    formulas come back unchanged. A formula is a closed sentence here (a free variable
    has been refused), so renaming a binder changes nothing the formula says.
    """
    clashing = {node.variable.name for f in formulas for node in f.walk()
                if type(node).__name__ in ("Quantifier", "SortedQuantifier")
                and node.variable.name in symbols}
    if not clashing:
        return list(formulas)
    names = set(symbol_names(*formulas)) | set(symbols)

    def rename(node: Node, scope: Dict[str, str]) -> Node:
        kind = type(node).__name__
        if kind == "Variable":
            new = scope.get(node.name)
            return node if new is None else Variable(new)
        if kind in ("Quantifier", "SortedQuantifier"):
            old = node.variable.name
            if old in clashing:
                new = fresh_variable_like(old, names)
                names.add(new)
                inner = {**scope, old: new}
            else:
                new = old
                inner = {name: image for name, image in scope.items() if name != old}
            return replace(node, variable=Variable(new), formula=rename(node.formula, inner))
        return node.map_children(lambda child: rename(child, scope))

    return [rename(f, {}) for f in formulas]


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
    applied predicate (the truth constants render as ``true`` / ``false``)."""
    if truth_value(node) is not None:
        return "true" if truth_value(node) else "false"
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

def formula_to_casl(formula: Node, *, default_sort: str = "Thing",
                    visible_symbols: Iterable[str] = ()) -> str:
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

    A bound variable that is spelled like a symbol of the formula (a constant, a
    function, a predicate or a sort it names, or ``default_sort``) is renamed, as in
    :func:`to_casl_spec`. ``visible_symbols`` names the symbols of the hand-written CASL
    the text is embedded into, which this function cannot see: a bound variable is
    never given the spelling of one of them either.

    Raises:
        NotImplementedError: ``formula`` contains a node outside the
            classical FOL/MSFOL fragment (see the module docstring's
            "Scope" section).
        ValueError: a free variable, a reserved-word identifier, an arity
            or constant/function-vs-function conflict, an unsatisfiable
            sort constraint, or a sort written in the formula that is spelled like
            ``default_sort`` while the default sort is used (the message names the
            keyword that picks another one).
    """
    sig = _analyze([formula], default_sort)
    [formula] = _bind_apart([formula], _specification_symbols(sig, visible_symbols))
    return _render(formula, default_sort)


def to_casl_spec(
    axioms: Iterable[Node],
    *,
    conjectures: Iterable[Node] = (),
    spec_name: str = "KitExport",
    default_sort: str = "Thing",
    subsorts: Optional[Mapping[str, FrozenSet[str]]] = None,
    visible_symbols: Iterable[str] = (),
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

    ``subsorts`` (default ``None``, no subsort declarations emitted) is the
    child-sort-to-DIRECT-parent-sorts mapping — the same shape as
    :attr:`~unicode_logic_kit.fol.signature.Signature.subsorts`, and typically
    passed as exactly that attribute — completing the round trip with
    :func:`unicode_logic_kit.fol.casl_import.parse_casl_spec`, which reads
    ``sort <child> < <parent>`` back into the identical mapping. Unlike
    every other declaration here, a subsort edge is NOT inferred from the
    formulas (nothing about ``S < T`` is derivable from how ``S``/``T`` are
    USED in an axiom), so both sort names in every edge are added to the
    ``sorts`` line even if neither appears in any formula, and both are
    checked against the CASL reserved-word list exactly like every other
    emitted sort name (see the module docstring's "Reserved words" section).

    **Bound variables and the symbols of the spec.** CASL writes a bound variable and a
    constant as the same identifier, and the variable wins inside its quantifier, so a
    constant ``w`` under a quantifier that binds ``w`` would be read as the variable. A
    bound variable that is spelled like ANY symbol of the whole spec (a constant, function
    or predicate of any axiom or conjecture, a sort, ``default_sort``, a name in
    ``visible_symbols``) is therefore renamed to a fresh variable name (``w0``, ``w1``, …,
    fresh against every name the formulas hold), in its quantifier and in every
    occurrence it binds; names are compared exactly, as CASL does (``W`` and ``w`` do not
    clash). Text without such a clash is unchanged. The result reads back through
    :func:`~unicode_logic_kit.fol.casl_import.parse_casl_spec` as the same formula up to
    the names of the bound variables that had to be renamed (and is the same formula
    where none was). ``visible_symbols`` are the names of symbols the spec sees without
    declaring them (those of a spec it extends with ``then``); no formula is read for
    them, they only keep the binders away.

    Raises:
        ValueError: neither ``axioms`` nor ``conjectures`` contains any
            formula; ``spec_name`` is not a simple identifier or collides
            with a CASL keyword; a sort name in ``subsorts`` is reserved; a sort
            written in the formulas or named in ``subsorts`` is spelled like
            ``default_sort`` while the default sort is used (the message names the
            keyword ``default_sort=`` that picks another one); or
            any of the sort-inference / identifier refusals documented on
            :func:`formula_to_casl` above.
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
    subsorts = subsorts or {}
    subsort_edges: List[Tuple[str, str]] = sorted(
        (child, parent) for child, parents in subsorts.items() for parent in parents
    )
    for child, parent in subsort_edges:
        _check_reserved(child, "sort")
        _check_reserved(parent, "sort")

    edge_sorts = [s for edge in subsort_edges for s in edge]
    sig = _analyze(all_formulas, default_sort, declared_sorts=edge_sorts)
    bound_apart = _bind_apart(all_formulas,
                              _specification_symbols(sig, [*edge_sorts, *visible_symbols]))
    axioms, conjectures = bound_apart[:len(axioms)], bound_apart[len(axioms):]
    declared_sorts: Set[str] = set(sig.literal_sorts)
    for child, parent in subsort_edges:
        declared_sorts.add(child)
        declared_sorts.add(parent)

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
    for child, parent in subsort_edges:
        lines.append(f"  sort {child} < {parent}")
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
