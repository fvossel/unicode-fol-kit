"""Native TF0 (monomorphic typed first-order TPTP, ``tff``) export.

The classical ``fof`` route (:mod:`atp._tptp_problem`) already handles
many-sorted formulas via :meth:`~unicode_logic_kit.fol.nodes.SortedQuantifier
.to_tptp`'s auto-reduction: a sort ``S`` becomes an ordinary guard predicate,
``∀x:S φ`` becomes ``![X]: (s(X) => <φ>)``. That is sound but throws the
typing away — an external prover sees an unsorted formula with one extra
predicate per sort, not a genuinely typed problem. This module instead emits
TPTP's own typed dialect: one ``tff(name, type, Sym: Type).`` declaration per
sort/predicate/function/constant, and formula bodies with GENUINE typed
quantifiers (``![X: sort]: ...``) rather than guard atoms.

Scope: TF0 only
----------------
Deliberately narrower than full TFF: no THF (higher-order), no TF1
polymorphism (type variables, ``!>``), and none of TPTP's built-in
arithmetic sorts (``$int``/``$rat``/``$real``) — none of those constructs are
producible by this kit's own AST in the first place (there is no "type
variable" or "higher-order" node class), so the writer's fragment gate below
simply enumerates the classical many-sorted FOL node set it understands and
refuses everything else BY NAME, mirroring
:mod:`unicode_logic_kit.fol.casl_export`'s ``_check_fragment`` gate for the
structurally identical problem (CASL's own typed spec syntax).

**Numerals and operators are ordinary symbols here.** A problem that was not asked
for arithmetic reads a :class:`~unicode_logic_kit.fol.nodes.Number` as a CONSTANT
identified by its value (``1`` and ``1.0`` are one constant) and ``+ - * /`` and ``<
> ≤ ≥`` as uninterpreted function and predicate symbols (the same definition the
``fof`` writer writes, see :mod:`unicode_logic_kit.atp._tptp_problem`). So this writer
declares a numeral as a constant of ``$i`` (``tff(const_decl_1, type, n1: $i ).``),
an operator as an uninterpreted function ``$i * $i > $i`` and a comparison as an
uninterpreted predicate ``$i * $i > $o``, each under a word of the TF0 grammar that the
ordinary renamer chose and the returned name map records; the numerals are the map's
``numerals``, which is how a proof's ``n1`` reads back as ``Number(1)``. The numeral has
no sort annotation to write, so a numeral that the inference would put into a user sort
(``∀x:S P(x), P(1)``: the position of ``P``'s argument holds ``S``) is refused as an
unannotated constant is (:class:`Tf0Refusal`), and the backends' automatic mode writes
``fof`` for it. A ``Constant`` spelled like a numeral of the problem (``Number(1)`` next
to ``Constant('1')``) is refused by name. TPTP's own arithmetic (``$int``, ``$sum``,
``$less``, number literals) is the TFA writer's
(:func:`~unicode_logic_kit.atp._tff_problem.generate_tff_arith_problem`, the ``sort=``
option of the backends), and is out of scope here.

The two builtin TPTP types this module DOES use, ``$i`` (the default
individual type — never declared, exactly the TPTP standard's own
convention) and ``$o`` (booleans — only ever appears as a predicate's own
result type), are never routed through the sort-name sanitiser below; they
are TPTP reserved dollar-words, lexically disjoint from every
``lower_word``-shaped user sort name this module CAN synthesise.

Sort/type inference: a union-find over symbol-position "slots"
-------------------------------------------------------------------
The same technique :mod:`unicode_logic_kit.fol.casl_export` uses for CASL's
``ops``/``preds`` blocks, adapted for TFF: :class:`~unicode_logic_kit.fol.nodes
.SortedQuantifier` only annotates its OWN bound variable, not every symbol
position that variable is later passed to, so before any ``tff(...,type,...)``
declaration can be written, this module infers a single concrete sort for
every predicate/function ARGUMENT position and every function/constant
RESULT, by propagating the sort annotations that ARE present
(:class:`SortedQuantifier`, :class:`~unicode_logic_kit.fol.nodes.SortedConstant`)
through every place a term is passed as an argument. A plain, unsorted
:class:`~unicode_logic_kit.fol.nodes.Quantifier`'s variable anchors its slot to
``$i`` directly (TPTP's own "no type given" default), which plugs into
EXACTLY the same union-find machinery as a genuine sort name — a position
connected to both ``$i`` (from one occurrence) and a real sort ``S`` (from
another) is a genuine conflict and is refused loudly, precisely because
mixing an implicitly-``$i`` and an explicitly-sorted use of the same symbol
position really is unsound. See :mod:`unicode_logic_kit.fol.casl_export`'s
module docstring for the full union-find account (:class:`_UnionFind`
below is line-for-line the same algorithm, ``$i`` playing CASL's
``default_sort`` role).

``SortedCount`` (∃≥n / ∃≤n / ∃=n x:S φ) is lowered BEFORE inference/rendering
via :func:`_expand_sorted_count` — the same distinct-witnesses encoding
:class:`~unicode_logic_kit.fol.nodes.Count._expand` uses, reimplemented here
with SORT-TYPED witness quantifiers (``SortedQuantifier`` over the SAME sort
``S``) instead of Count's plain, unsorted ones, so the exported problem never
needs a synthetic guard predicate for the witnesses either.
:class:`~unicode_logic_kit.fol.nodes.SortedCardinality` has no first-order
export at all (set cardinality is second-order) and is refused by the
fragment gate, exactly like :class:`~unicode_logic_kit.fol.nodes.Cardinality`
in the classical route.

Free variables are refused, not implicitly closed
---------------------------------------------------
TPTP semantics implicitly universally-close a free variable in an
axiom/conjecture at type ``$i``. This module refuses a free variable instead
(mirroring :func:`unicode_logic_kit.fol.casl_export.formula_to_casl`'s own
refusal, for the same reason): a kit-level formula that reaches this module
with a genuinely free variable has no way to tell whether that variable was
MEANT to range over a user sort — silently defaulting it to ``$i`` could
render a DIFFERENT, unintended typed problem. Every variable rendered here
comes from an explicit :class:`~unicode_logic_kit.fol.nodes.Quantifier` /
``SortedQuantifier`` binder in the kit's own AST.

Name legality (ASCII, first-letter-fold, whole-problem-injective)
-------------------------------------------------------------------
Mirrors :mod:`atp._tptp_problem`'s sanitisation for predicates/functions/
constants (ASCII transliteration, every other character outside
``[A-Za-z0-9_]`` written as a ``uXXXX`` code-point escape, then fold only the
first character for TPTP's lower_word rule, with a synthesised token
(:func:`_tptp_word_base`) when the original name is not already TPTP-legal)
and extends the SAME treatment to SORT names, which
share the kit's uppercase-initial :samp:`PREDICATE` lexical convention (see
``fol/_identifiers.py``'s ``sort_pattern()``) and therefore need exactly the
same fold. Predicates, functions+constants (one shared namespace) and sorts
(a third, independent namespace — TPTP types live in yet another syntactic
position) are each de-collided separately; two DISTINCT kit-level names in
the same namespace that would fold to the same TPTP identifier are refused
with ``NotImplementedError`` naming both, exactly like ``_tptp_problem``'s
own collision guard. This module deliberately does not depend on
``atp._tptp_problem`` at import time (that module imports this one) to avoid
a circular import between the two — the small renaming primitives are
duplicated here at the size CASL export's own ``_check_reserved`` duplicates
``eval.validate``'s builtin sets (see that module's docstring for the same
"importing would be backwards" reasoning).

A predicate and a function/constant that fold to the SAME identifier
--------------------------------------------------------------------
Unlike untyped ``fof``, TF0 has ONE flat table of declared symbols, so a
predicate ``Agent`` and a role function ``agent`` (both ``agent``) would get
two ``tff(…, type, agent: …)`` declarations for one name — for the function
case Vampire and E both refuse the problem (``agent(X0) … is not an instance
of sort $i`` / ``type error``) before they answer anything, so no verdict
comes back at all. The writer therefore renames the
TERM-side symbol (the function or constant; the predicate keeps its natural
name) to ``<name>_term`` — de-collided with a numeric suffix against every
identifier the problem already uses — whenever its rendered name equals a
predicate's, whatever the arities. The rename is exact (a symbol is only a
name) and is recorded: :func:`generate_tff_problem_with_mapping` returns the
:class:`~unicode_logic_kit.atp._tptp_problem.TptpNameMap`
(:func:`~unicode_logic_kit.atp._tptp_problem.apply_reverse_tptp` restores the
original names).

A function/constant that folds to the name of a SORT is separated the same way,
for a measured reason: Vampire 5.0.1 resolves the term's name to the type
(``The sort $tType of the intended term argument human … is not an instance of
sort human``) and refuses the problem, while E accepts it.

A SORT and a PREDICATE that fold to the same name are REFUSED, by name. They are
read correctly by Vampire and E (``human: $tType`` next to ``human: human > $o``),
but they would not mean what the kit's other routes mean. The kit defines a sort
as its guard predicate: ``∀x:S φ`` is ``∀x (S(x) → φ)``, with ``∃x S(x)`` for the
sort's non-emptiness, which is what ``to_z3``, the ``fof`` writer and the Prover9
writer do, so there ``∃y:Car Car(y)`` is valid (``Car`` is one symbol, and it is
non-empty). TF0 declares the type ``car`` and an UNRELATED predicate ``car`` over
it, and ``∃y:Car Car(y)`` is then not a theorem (let ``Car`` hold of nothing): a
prover answering over TF0 would answer a different question than z3 does, and the
default backend chain and ``backends=['vampire']`` would disagree on one input.
TF0 cannot express the guard reading, so the pair is refused, naming both, in the
same family as the same-kind refusal below; rename one of the two, or write the
problem with the ``fof`` writer, which reads the sort as that predicate. (The TFA
writer has no sorts: it refuses a sorted node by name.)

A problem needs no conclusion: ``conclusion=None`` writes no ``conjecture`` line,
for a prover asked whether the premises are satisfiable. Every check and rename
works on the premises alone.

A variable that has no TPTP spelling (``ä`` is written ``Ä``, ``x-1``, ``1x``) is
renamed to a fresh legal one, per formula, without a record: a variable is bound
(:func:`unicode_logic_kit.fol._tptp_symbols.legalise_variables`). The nullary atoms
``$true`` and ``$false`` are TPTP's own propositions (this kit's TPTP reader
produces them): they are written verbatim and are neither declared nor renamed.

The typed text against the kit's own reading of a sort
------------------------------------------------------------
What a sort IS in this kit: there is ONE universe; a sort ``S`` is a non-empty
subset of it (the extension of the unary predicate ``S``) and sorts may overlap; a
constant written ``c:S`` is an element of ``S``, and ``c:S`` here and a plain ``c``
there are one constant; an unannotated constant, an unsorted variable and the value
of a function may be ANY element of the universe (there is no way to declare a
function's result sort); a predicate is a relation over the whole universe. That is
what ``to_z3``, the ``fof`` writer (with the non-emptiness and the sort membership
axioms it adds), the Prover9 writer and the finite model finder answer.

TF0's types are DISJOINT sets, and the union-find above decides the type of every
position, so a typed text can ask another question. Two shapes of it are REFUSED
(:class:`Tf0Refusal`, by name, with what to write instead; :func:`check_typed_reading`
is the one implementation, which the NXF writer and the Hets backend share):

* **An unannotated constant or a function value that the inference puts into a
  sort.** A constant that is written ``c:S`` NOWHERE in the problem, or the value
  of a function, whose position is in one class with a sort ``S`` (an argument
  position that a ``∀x:S`` binds, an equation with a sorted term, ...) would be
  declared ``c: s`` / ``f: ... > s``, which asserts what no formula says. (A
  function ARGUMENT position may be a sort: nothing is asserted about the value of
  the function there. A constant annotated ``c:S`` anywhere is in ``S`` at every
  occurrence.) Measured, Vampire 5.0.1 and E 3.5.1: ``∀x:Human Mortal(x) ⊢
  Mortal(socrates)`` and ``∀x:Foo R(x), Q(g(a)) ⊢ R(g(a))`` were theorems of the
  typed text and are not entailed (take a universe of two elements, the sort and the
  predicate on the first, the constant or ``g(a)`` the second).
* **An equation over a variable bound by an unsorted quantifier, in a problem that
  has a sort.** An unsorted quantifier ranges over the whole universe, the elements
  of every sort included, so with an equation it bounds the size of the universe;
  in the typed text it ranges over ``$i``, a separate type. ``∀x ∀y x = y ⊢ ∀x:A ∀z:A
  x = z`` is valid (the universe has one element, ``A`` is a subset of it) and is
  not a theorem of the typed text; ``∀x ∀y x = y, ∃x:A ∃z:A ¬(x = z)`` is
  unsatisfiable and the typed text is satisfiable. (An equation between sorted
  variables, or between constants and function values, is harmless. A ``SortedCount``
  is expanded first: its witnesses are sorted variables.)

Why these two conditions are enough. Say the typed text has neither. (1) A model of
the kit's reading in which the premises hold and the conclusion fails gives a model
of the typed text in which they do too: ``$i`` is the universe, each type a tagged
copy of its sort, and every term at a position of type ``s`` is a variable bound by
``∀x:S`` or a constant annotated ``c:S`` (the others were refused), so it denotes
an element of ``S``, and the two evaluations agree: a theorem of the typed text is
valid in the kit. (2) A model of the typed text in which the premises hold and the
conclusion fails gives a model of the kit's reading: multiply ``$i`` by a set at
least as large as every type, with constants and function values at the first
coordinate and the predicates ignoring the second; that changes no formula without
an equation over an unsorted variable, and every type then embeds into the result,
which is the universe; a constant or function value that the inference had put into
a sort is simply the embedded element, which the kit allows for an unannotated
symbol. So a countermodel of the typed text is one of the kit's reading. Differentially
(Vampire on the typed text and on the ``fof`` text, ``tests/test_tf0_typed_reading.py``)
what the writer accepts is answered the same.

The two conditions are SUFFICIENT, not necessary: ``∀x:S P(x), c = d:S ⊢ P(c)`` is
refused (``c`` is written with no sort) although the typed text happens to answer it
correctly, and such a problem goes to the ``fof`` route, which asks the kit's
question for every problem. With
``tff=None`` the backends fall back to it and say so in the verdict's detail;
``tff=True`` reports the refusal (``unknown`` / ``unsupported``) and ``tff=False``
writes ``fof``. :func:`infer_tff_signature` is signature inference, not a decision
route, and keeps inferring.

The asymmetry with the same-namespace rule above is deliberate for this
release. Two LEGAL names of ONE kind that fold together (``Foo``/``foo``) are
still refused by name rather than renamed: that refusal predates the name map
and is kept so that no existing caller silently receives a renamed symbol it
did not ask for. A name that is not TPTP-legal at all, or that clashes across
kinds, has always needed a rewrite to be expressible, so it is renamed and
recorded.
"""

import re
from dataclasses import dataclass, field
from typing import (
    TYPE_CHECKING, Callable, Dict, FrozenSet, Iterable, List, Optional, Sequence, Set, Tuple,
    Union,
)

from ..fol.nodes import (
    Node, Variable, Constant, SortedConstant, Function,
    Atom, Not, And, Or, Xor, Implies, Iff, Quantifier, SortedQuantifier,
    SortedCount, free_variables, substitute,
)
from ..fol._fol_nodes import constant_name_to_ascii, tptp_fold_first_letter
from ..fol._numeral_symbols import numerals_as_constants
from ..fol._tptp_symbols import check_variable_names, is_tptp_boolean_atom, legalise_variables
from ..fol.signature import Signature, PredicateDecl, FunctionDecl, ConstantDecl
from ._ascii_names import ascii_safe_base, reserve_rendered
from ._writer_support import (
    check_against_generated, normalise_premise_names, refusals_speak_as, tptp_name_token,
)

if TYPE_CHECKING:
    from ._tptp_problem import TptpNameMap

__all__ = [
    "generate_tff_problem", "generate_tff_problem_with_mapping",
    "formula_to_tff", "infer_tff_signature", "check_typed_reading",
    "unsorted_equality_refusal", "Tf0Refusal",
    "problem_needs_tff", "TFF_INDIVIDUAL_SORT", "TFF_BOOLEAN_SORT",
]

_SORTED_NODE_NAMES = frozenset({"SortedQuantifier", "SortedConstant", "SortedCount"})


class Tf0Refusal(ValueError, NotImplementedError):
    """The typed (TF0) writer will not write this problem.

    Raised when the typed text would not ask the question the kit's other routes
    ask (an unannotated constant or a function value that the inference would put
    into a sort, an equation over an unsorted variable next to a sort, one position
    holding two sorts, a sort that is also a predicate), or when it cannot be written
    at all in one table of typed symbols (a free variable, a predicate or function at
    two arities, a name that is both a constant and a function). The message names the
    term, the sort and the reason, and says what to write instead. The fof writer
    (:func:`~unicode_logic_kit.atp._tptp_problem.generate_tptp_problem_with_mapping`)
    asks the kit's question for every one of these problems; the backends'
    automatic mode (``tff=None``) falls back to it when this is raised.

    It derives from both :class:`ValueError` and :class:`NotImplementedError`, so
    that code which caught either of the two before this class existed (the sort
    conflict was a ``ValueError``, the sort and predicate of one name a
    ``NotImplementedError``) keeps working.

    Fields:

    * ``reason`` -- a short machine-readable word: ``"sort_conflict"``,
      ``"sort_predicate_name"``, ``"unsorted_term_in_sort"``,
      ``"unsorted_equality"``, ``"free_variable"``, ``"arity_conflict"``,
      ``"constant_function_clash"`` or ``"premise_name"`` (a premise named like one of
      the lines the writer writes itself).
    """

    def __init__(self, message: str, reason: str = "") -> None:
        super().__init__(message)
        self.reason = reason


def problem_needs_tff(premises: Sequence[Node], conclusion: Optional[Node] = None) -> bool:
    """Whether any of ``premises`` + ``conclusion`` contains a
    :class:`~unicode_logic_kit.fol.nodes.SortedQuantifier` /
    :class:`~unicode_logic_kit.fol.nodes.SortedConstant` /
    :class:`~unicode_logic_kit.fol.nodes.SortedCount` node.

    The auto-select signal the TPTP-family backends
    (:mod:`atp.vampire_entailment`, :mod:`atp.eprover_backend`) use to try
    this module's native typed export before the classical guard-predicate
    ``fof`` route (:mod:`atp._tptp_problem`) — see each backend's ``tff=``
    option. It says that the problem is worth TRYING as TF0, not that TF0 will
    take it: the typed writer refuses (:class:`Tf0Refusal`) the problems whose
    typed text would not ask the kit's question, and the automatic mode then
    writes the ``fof`` problem. A batch with no sorted node at all is already
    fully served by the classical route (a plain ``Quantifier`` needs no typing
    to export soundly), so the default stays ``fof`` there.
    """
    for f in list(premises) + ([] if conclusion is None else [conclusion]):
        for n in f.walk():
            if type(n).__name__ in _SORTED_NODE_NAMES:
                return True
    return False

#: TPTP's built-in "individual" type — the implicit type of an untyped
#: quantified variable. Never declared with its own ``tff(...,type,...)``
#: statement (it is a TPTP reserved word), and never routed through the
#: sort-name sanitiser (it is not a kit-level sort name at all).
TFF_INDIVIDUAL_SORT = "$i"

#: TPTP's built-in boolean type — only ever a PREDICATE's own result type.
TFF_BOOLEAN_SORT = "$o"

_ARITHMETIC_PREDS = frozenset({"<", ">", "≤", "≥"})
_ARITHMETIC_FUNCS = frozenset({"+", "-", "*", "/"})

_ARITH_OUT_OF_SCOPE = (
    "generate_tff_problem: {kind} {name!r} is an arithmetic symbol, and this entry point "
    "does not read it as an ordinary one: reading it as arithmetic needs TPTP's arithmetic "
    "sorts ($int/$rat/$real), which are out of scope for a TF0-only exporter (see module "
    "docstring 'Scope: TF0 only'). The problem writers generate_tff_problem and "
    "generate_tptp_problem_with_mapping write it as an ordinary uninterpreted symbol, which "
    "is what this kit means by it unless arithmetic is asked for by name "
    "(generate_tff_arith_problem, sort='int')."
)


# =============================================================================
# Fragment gate
# =============================================================================

# The classical MSFOL node set this exporter understands PLUS SortedCount
# (lowered away by _expand_all_sorted_counts before inference/rendering ever
# see it) — exactly unicode_logic_kit.fol.casl_export's _ALLOWED_CASL_NODES
# with SortedCount added; see the module docstring's "Scope" section for why
# every other node class (Cardinality/SortedCardinality, modal/temporal,
# second-order, lambda, Łukasiewicz, Number, ...) is refused by name rather
# than silently narrowed.
_ALLOWED_TFF_NODES = frozenset({
    "Variable", "Constant", "SortedConstant", "Function",
    "Atom", "Not", "And", "Or", "Xor", "Implies", "Iff",
    "Quantifier", "SortedQuantifier", "SortedCount",
})


def _check_fragment(formula: Node) -> None:
    """Walk ``formula`` and refuse (loudly, by name) the first node outside
    the TF0-expressible fragment this exporter covers.

    A bespoke recursion rather than ``Node.walk()``: ``SortedCount.n`` is a
    ``Number`` child (the symbolic counting bound, e.g. the ``2`` in
    ``∃≥2 x:S φ``) but is not itself a FORMULA or TERM position — it is
    never rendered as a TFF expression, only read as a Python int by
    :func:`_expand_sorted_count` — so it must NOT trip the "a numeric
    literal needs an arithmetic sort" refusal below the way an actual
    ``Number`` TERM occurrence (e.g. inside an Atom's arguments) should.
    """
    def visit(node: Node) -> None:
        cls = type(node).__name__
        if getattr(node, "sort", None) == TFF_INDIVIDUAL_SORT:
            raise NotImplementedError(
                f"generate_tff_problem: a sort named {TFF_INDIVIDUAL_SORT!r} cannot be "
                f"written in TF0: {TFF_INDIVIDUAL_SORT} is TPTP's built-in type of "
                f"individuals, the type this writer gives every UNSORTED term, so a "
                f"user sort of that name would be merged with everything that has no "
                f"sort (∀x:$i R(x) would say ∀x R(x)). Rename the sort.")
        if cls not in _ALLOWED_TFF_NODES:
            if cls == "Number":
                raise NotImplementedError(
                    "generate_tff_problem: this entry point does not read a numeric "
                    "literal as an ordinary constant. Read as arithmetic it would need "
                    "TPTP's arithmetic sorts ($int/$rat/$real), which are out of scope "
                    "for this TF0-only exporter (see module docstring 'Scope: TF0 "
                    "only'). The problem writers generate_tff_problem and "
                    "generate_tptp_problem_with_mapping write a numeral as a constant "
                    "of $i, which is what this kit means by it unless arithmetic is "
                    "asked for by name (generate_tff_arith_problem, sort='int')."
                )
            raise NotImplementedError(
                f"generate_tff_problem: {cls!r} is outside the classical "
                "many-sorted FOL fragment this native TF0 exporter covers "
                "(only Atom, Not, And, Or, Xor, Implies, Iff, Quantifier, "
                "SortedQuantifier, SortedCount, and the term classes "
                "Variable, Constant, SortedConstant, Function are "
                "TF0-expressible here). Modal/temporal/epistemic operators, "
                "second-order quantification, SortedCardinality (set "
                "cardinality has no first-order counterpart), and lambda "
                "terms are all out of scope for this TF0-only exporter."
            )
        if cls == "SortedCount":
            visit(node.variable)
            visit(node.formula)
            return
        for child in node._child_nodes():
            visit(child)

    visit(formula)


# =============================================================================
# SortedCount lowering: typed distinct-witnesses encoding
# =============================================================================

_COUNT_EXPAND_MAX = 500
_COUNT_TOO_LARGE = (
    "generate_tff_problem: SortedCount n={n} is too large to expand to "
    "typed first-order TFF (the distinct-witnesses encoding materialises "
    f"O(n^2) constraints under n nested quantifiers; the limit is n<={_COUNT_EXPAND_MAX})."
)


def _balanced_and(parts: List[Node]) -> Node:
    """Fold a non-empty list of formulas into a balanced (shallow) And tree —
    mirrors ``fol._fol_nodes._balanced_and``, duplicated here (a private
    helper of a module this one does not otherwise depend on) so an
    O(n^2)-conjunct count expansion stays only O(log n) deep."""
    while len(parts) > 1:
        merged: List[Node] = [And(parts[i], parts[i + 1]) for i in range(0, len(parts) - 1, 2)]
        if len(parts) % 2:
            merged.append(parts[-1])
        parts = merged
    return parts[0]


def _expand_sorted_count(node: SortedCount) -> Node:
    """Lower one ``SortedCount`` to plain SortedQuantifier/And/Or/Not/Atom,
    via the standard distinct-witnesses counting encoding, SORT-TYPED: every
    witness variable is bound by a ``SortedQuantifier`` over ``node.sort``,
    not a plain (guard-predicate-needing) ``Quantifier``.

    ``∃≥m x:S φ`` becomes ``∃x_0:S … ∃x_{m-1}:S (⋀ φ[x_i] ∧ ⋀_{i<j} x_i ≠ x_j)``;
    ``∃≤n`` is ``¬(∃≥n+1)``; ``∃=n`` is ``∃≥n ∧ ¬(∃≥n+1)`` — the exact reading
    :meth:`~unicode_logic_kit.fol.nodes.Count._expand` uses, reimplemented here
    (rather than delegating to ``SortedCount._relativize``/``Count._expand``)
    because those guard the matrix with a predicate atom instead of typing
    the witness quantifier, which is exactly the guard-atom encoding this
    NATIVE TFF exporter exists to avoid.
    """
    if node.n.value > _COUNT_EXPAND_MAX:
        raise NotImplementedError(_COUNT_TOO_LARGE.format(n=node.n.value))
    var, sort, phi = node.variable, node.sort, node.formula
    avoid = {v.name for v in free_variables(phi)} | {var.name}

    def fresh(k: int) -> List[Variable]:
        out: List[Variable] = []
        i = 0
        while len(out) < k:
            cand = f"{var.name}_{i}"
            if cand not in avoid:
                out.append(Variable(cand))
                avoid.add(cand)
            i += 1
        return out

    def at_least(m: int) -> Node:
        if m <= 0:
            w = fresh(1)[0]
            g = substitute(phi, var, w)
            return SortedQuantifier("∃", w, sort, Or(g, Not(g)))
        ws = fresh(m)
        conjuncts = [substitute(phi, var, w) for w in ws]
        conjuncts += [Atom("≠", (ws[i], ws[j]))
                      for i in range(m) for j in range(i + 1, m)]
        body = _balanced_and(conjuncts)
        for w in reversed(ws):
            body = SortedQuantifier("∃", w, sort, body)
        return body

    if node.op == "ge":
        return at_least(node.n.value)
    if node.op == "le":
        return Not(at_least(node.n.value + 1))
    return And(at_least(node.n.value), Not(at_least(node.n.value + 1)))


def _expand_all_sorted_counts(node: Node) -> Node:
    """Bottom-up rewrite: every ``SortedCount`` (including one nested inside
    another's matrix) is replaced by :func:`_expand_sorted_count`'s typed
    encoding. After this pass the tree is guaranteed to use only the
    fragment :mod:`unicode_logic_kit.fol.casl_export` also accepts (plus
    ``SortedQuantifier``/``SortedConstant``), since ``_check_fragment`` has
    already run on the (pre-expansion) input."""
    node = node.map_children(_expand_all_sorted_counts)
    if isinstance(node, SortedCount):
        return _expand_sorted_count(node)
    return node


# =============================================================================
# Sort inference: union-find over slots and concrete sort names
# =============================================================================
#
# Line-for-line the same algorithm as unicode_logic_kit.fol.casl_export's
# _UnionFind — see that module's docstring for the full account. $i plays
# CASL's default_sort role: it is unioned in directly wherever a plain
# (unsorted) Quantifier's variable is used, so a position that is EVER used
# both implicitly-$i and explicitly-sorted is a genuine, correctly-refused
# conflict rather than two different silently-coexisting readings.

_Slot = Union[Tuple[str, str, int], Tuple[str, str], str]


class _UnionFind:
    """Weighted union-find over sort-inference slots and concrete sort names.

    Invariant: whenever a class contains a concrete sort name (a plain str
    member, including ``$i``), that string is ALWAYS the class's root.
    """

    def __init__(self) -> None:
        self._parent: Dict[_Slot, _Slot] = {}
        self._rank: Dict[_Slot, int] = {}

    def find(self, x: _Slot) -> _Slot:
        self._parent.setdefault(x, x)
        path = []
        while self._parent[x] != x:
            path.append(x)
            x = self._parent[x]
        for n in path:
            self._parent[n] = x
        return x

    def union(self, a: _Slot, b: _Slot, context: str) -> None:
        ra, rb = self.find(a), self.find(b)
        if ra == rb:
            return
        a_concrete, b_concrete = isinstance(ra, str), isinstance(rb, str)
        if a_concrete and b_concrete:
            raise Tf0Refusal(
                f"generate_tff_problem: sort conflict while resolving "
                f"{context} — inferred both {ra!r} and {rb!r}. TF0's types are "
                f"disjoint sets, so one position cannot hold two of them; in this "
                f"kit a sort is a subset of ONE universe, sorts may overlap, and an "
                f"unsorted variable or term ranges over the whole universe, sorted "
                f"elements included. The other routes ask that question and this "
                f"text cannot: write the problem with the fof writer "
                f"(generate_tptp_problem_with_mapping; tff=False in the backends, "
                f"which tff=None falls back to).",
                reason="sort_conflict",
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

    def sort_of(self, slot: _Slot) -> str:
        """Return the concrete sort resolved for ``slot``, defaulting to
        :data:`TFF_INDIVIDUAL_SORT` if that slot's class has no concrete
        member at all (a symbol position never connected to any sort
        annotation — TPTP's own "no type given" reading)."""
        root = self.find(slot)
        return root if isinstance(root, str) else TFF_INDIVIDUAL_SORT


@dataclass
class _Signature:
    """Mutable accumulator built by one :func:`_analyze` pass — mirrors
    ``casl_export._Signature`` minus ``default_sort`` (fixed to ``$i``).

    ``sorted_constants`` are the constants written ``c:S`` somewhere in the
    problem (``c`` is ONE symbol wherever it occurs, so a plain occurrence of
    it is covered too); ``unsorted_equality`` is the first equality or
    disequality atom that has a bare variable bound by an unsorted quantifier
    as one of its sides. :func:`_check_reading` reads both.

    ``uninterpreted_arithmetic`` says that ``+ - * /`` and ``< > ≤ ≥`` are ordinary
    symbols of the problem (the problem writers) and not a refused construct (signature
    inference and the typed-reading check)."""

    uf: _UnionFind = field(default_factory=_UnionFind)
    pred_arity: Dict[str, int] = field(default_factory=dict)
    func_arity: Dict[str, int] = field(default_factory=dict)
    const_names: Set[str] = field(default_factory=set)
    func_names: Set[str] = field(default_factory=set)
    literal_sorts: Set[str] = field(default_factory=set)
    sorted_constants: Set[str] = field(default_factory=set)
    unsorted_equality: Optional[Node] = None
    uninterpreted_arithmetic: bool = False


_CONST_VS_FUNCTION = (
    "generate_tff_problem: {name!r} is used both as a constant and as a "
    "function — this exporter declares at most one 'tff(...,type,...)' "
    "entry per name, so the two uses cannot be reconciled into one symbol. "
    "Rename one of the two, or write the problem with the fof writer "
    "(tff=False in the backends), which writes them as two symbols."
)


def _infer_term(node: Node, env: Dict[str, str], sig: _Signature) -> _Slot:
    """Process a term node: register its symbol, recurse into sub-terms,
    return the union-find slot representing its sort. Mirrors
    ``casl_export._infer_term``."""
    cls = type(node).__name__

    if cls == "Variable":
        if node.name not in env:
            raise Tf0Refusal(
                f"generate_tff_problem: free variable '{node.name}' — every "
                "variable must be bound by an enclosing Quantifier or "
                "SortedQuantifier; TPTP's implicit top-level closure would "
                "silently default an unbound variable to $i, which this "
                "exporter refuses to guess (see module docstring). Bind the "
                "variable with a quantifier; the fof writer refuses a free "
                "variable too, so every route answers the same.",
                reason="free_variable",
            )
        return env[node.name]

    if cls in ("Constant", "SortedConstant"):
        name = node.name
        if name in sig.func_names:
            raise Tf0Refusal(_CONST_VS_FUNCTION.format(name=name),
                             reason="constant_function_clash")
        sig.const_names.add(name)
        slot: _Slot = ("const", name)
        if cls == "SortedConstant":
            sig.literal_sorts.add(node.sort)
            sig.sorted_constants.add(name)
            sig.uf.union(slot, node.sort, f"constant '{name}' sort annotation")
        return slot

    if cls == "Function":
        name = node.name
        if name in _ARITHMETIC_FUNCS and not sig.uninterpreted_arithmetic:
            raise NotImplementedError(_ARITH_OUT_OF_SCOPE.format(kind="function", name=name))
        if name in sig.const_names:
            raise Tf0Refusal(_CONST_VS_FUNCTION.format(name=name),
                             reason="constant_function_clash")
        arity = len(node.args)
        prev = sig.func_arity.get(name)
        if prev is not None and prev != arity:
            raise Tf0Refusal(
                f"generate_tff_problem: function '{name}' used with "
                f"conflicting arities {prev} and {arity}. This exporter "
                f"declares one type per name; write the problem with the fof "
                f"writer (tff=False in the backends), which writes the two "
                f"arities as two symbols, or rename one of them.",
                reason="arity_conflict",
            )
        sig.func_arity[name] = arity
        sig.func_names.add(name)
        for i, a in enumerate(node.args):
            arg_slot = _infer_term(a, env, sig)
            sig.uf.union(("func", name, i), arg_slot,
                        f"function '{name}' argument {i + 1}")
        return ("func_result", name)

    raise AssertionError(
        f"generate_tff_problem: unreachable — term node {cls!r} passed the "
        "fragment check but is not handled by _infer_term."
    )


def _infer_formula(node: Node, env: Dict[str, str], sig: _Signature) -> None:
    """Walk a formula node, threading the bound-variable environment,
    registering every predicate/connective/quantifier constraint. Mirrors
    ``casl_export._infer_formula``."""
    cls = type(node).__name__

    if cls == "Atom":
        if is_tptp_boolean_atom(node):      # $true / $false: TPTP's own, declared by no one
            return
        if node.predicate in _ARITHMETIC_PREDS and not sig.uninterpreted_arithmetic:
            raise NotImplementedError(
                _ARITH_OUT_OF_SCOPE.format(kind="predicate", name=node.predicate))
        if node.predicate in ("=", "≠"):
            if len(node.args) != 2:
                raise ValueError(
                    "generate_tff_problem: an equality/disequality atom "
                    f"must have exactly 2 arguments, got {len(node.args)}."
                )
            s0 = _infer_term(node.args[0], env, sig)
            s1 = _infer_term(node.args[1], env, sig)
            sig.uf.union(s0, s1, "an equality/disequality atom")
            if sig.unsorted_equality is None and any(
                    isinstance(a, Variable) and env[a.name] == TFF_INDIVIDUAL_SORT
                    for a in node.args):
                sig.unsorted_equality = node
            return
        arity = len(node.args)
        prev = sig.pred_arity.get(node.predicate)
        if prev is not None and prev != arity:
            raise Tf0Refusal(
                f"generate_tff_problem: predicate '{node.predicate}' used "
                f"with conflicting arities {prev} and {arity}. This exporter "
                f"declares one type per name; write the problem with the fof "
                f"writer (tff=False in the backends), which writes the two "
                f"arities as two symbols, or rename one of them.",
                reason="arity_conflict",
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
        new_env = dict(env)
        new_env[node.variable.name] = TFF_INDIVIDUAL_SORT
        _infer_formula(node.formula, new_env, sig)
        return

    if cls == "SortedQuantifier":
        sig.literal_sorts.add(node.sort)
        new_env = dict(env)
        new_env[node.variable.name] = node.sort
        _infer_formula(node.formula, new_env, sig)
        return

    raise AssertionError(
        f"generate_tff_problem: unreachable — formula node {cls!r} passed "
        "the fragment check but is not handled by _infer_formula."
    )


def _analyze(formulas: Sequence[Node], *, uninterpreted_arithmetic: bool = False) -> _Signature:
    """Run sort inference over a batch of already-fragment-checked,
    already-SortedCount-expanded formulas that share one TFF signature.

    With ``uninterpreted_arithmetic`` the operators and comparisons are symbols like
    any other (the problem writers); without it they are refused by name."""
    sig = _Signature(uninterpreted_arithmetic=uninterpreted_arithmetic)
    for f in formulas:
        _infer_formula(f, {}, sig)
    return sig


# =============================================================================
# The typed reading against the definition
# =============================================================================
#
# The inference above is a decision about TYPES, not about the kit's model
# theory. TF0's types are disjoint sets and the inference puts a symbol position
# into a sort whenever it shares a class with one, while the kit has ONE universe,
# sorts that are subsets of it, and terms that are in a sort only when a formula
# says so. Two situations make the typed text ask another question, and
# :func:`_check_reading` refuses both (the argument is in the module docstring):
#
# * a constant that is written ``c:S`` NOWHERE, or a function value, whose position
#   is typed to a user sort: the typed text declares ``c: s`` / ``f: ... > s``, which
#   asserts what no formula says (and a theorem of the typed text may then be no
#   theorem);
# * an equation with a bare variable bound by an UNSORTED quantifier, in a problem
#   that has a sort: the unsorted variable ranges over ``$i``, a type of its own,
#   instead of over the universe the sort is a subset of (and a countermodel of the
#   typed text may then be no countermodel).

def _first_atom_text(formulas: Sequence[Node], matches: Callable[[Node], bool]) -> str:
    """The first atom, in problem order, that has a sub-term for which ``matches``
    holds, as text -- where a message points the reader at; ``""`` if there is none."""
    for formula in formulas:
        for node in formula.walk():
            if isinstance(node, Atom) and any(
                    matches(term) for arg in node.args for term in arg.walk()):
                return node.to_unicode_str()
    return ""


_FOF_ADVICE = ("write the problem with the fof writer (generate_tptp_problem_with_mapping; "
               "tff=False in the backends, which tff=None falls back to), which does not "
               "type it")


def unsorted_equality_refusal(writer: str, equation: str, sorts: Iterable[str],
                              unsorted_type: str = TFF_INDIVIDUAL_SORT) -> Tf0Refusal:
    """The refusal for an equation over a variable bound by an unsorted quantifier
    in a problem that has a sort, as an exception for the caller to raise: the typed
    writers (TF0, NXF, and CASL through :func:`check_typed_reading`) share its text.

    ``equation`` is the atom as text, ``sorts`` the sorts of the problem and
    ``unsorted_type`` the type an unsorted variable has in the text being refused.
    The condition itself is syntactic: a user sort occurs, and an equality or
    disequality atom has a bare variable bound by an unsorted quantifier as one of
    its sides (after a ``SortedCount`` is expanded: its witnesses are sorted).
    """
    names = sorted(sorts)
    first = names[0]
    return Tf0Refusal(
        f"{writer}: the equation {equation} has a variable bound by an UNSORTED "
        f"quantifier, and the problem also uses the sort "
        f"{', '.join(repr(s) for s in names)}. In this kit an unsorted quantifier ranges "
        f"over the whole universe, sorted elements included, so an equation over it "
        f"bounds how many elements there are, and a sort is a subset of that universe; "
        f"in the typed text the unsorted variable ranges over {unsorted_type}, a type "
        f"of its own that is disjoint from {first}, so the same equation says nothing "
        f"about the elements of {first}. For example ∀x ∀y x = y ⊢ ∀x:{first} "
        f"∀z:{first} x = z is valid in this kit and is not a theorem of the typed text. "
        f"To ask the kit's question, {_FOF_ADVICE}; or quantify the variable with a sort "
        f"(∀x:{first} ...) if it is meant to range over one.",
        reason="unsorted_equality")


def _check_reading(sig: _Signature, formulas: Sequence[Node], *, writer: str,
                   unsorted_type: str = TFF_INDIVIDUAL_SORT,
                   numerals: FrozenSet[str] = frozenset()) -> None:
    """Refuse (:class:`Tf0Refusal`, by name) a problem whose typed text would not
    ask the kit's question. ``sig`` is :func:`_analyze`'s result over ``formulas``
    (already expanded); ``writer`` names the caller in the message and
    ``unsorted_type`` the type an unsorted variable gets in the text (``$i`` in
    TF0). ``numerals`` are the names of the constants that stand for numerals: a
    numeral that is typed into a sort is refused like an unannotated constant, in
    words that fit a numeral (it cannot be written with a sort).

    Checked in a fixed order (function values, then constants, each by name, then
    the equation), so that the refusal does not depend on the order of the
    formulas.
    """
    for name in sorted(sig.func_names):
        sort = sig.uf.sort_of(("func_result", name))
        if sort == TFF_INDIVIDUAL_SORT:
            continue

        def is_that_function(t: Node, name: str = name) -> bool:
            return isinstance(t, Function) and t.name == name

        use = _first_atom_text(formulas, is_that_function)
        raise Tf0Refusal(
            f"{writer}: the value of the function {name!r} would be typed as the sort "
            f"{sort!r}, because it is used at a position that also holds terms of that "
            f"sort ({use}). In this kit a function value may be any element of the "
            f"universe: a function has no declared result sort, and nothing in the "
            f"problem says that {name}(...) is a {sort}. The typed text would assume it, "
            f"so a prover would answer a stronger question than the other routes ask. "
            f"To ask the kit's question, {_FOF_ADVICE}; if the function is meant to "
            f"return {sort}s, say so there as a premise with the sort written as a "
            f"predicate ({sort}({name}(...))).",
            reason="unsorted_term_in_sort")
    for name in sorted(sig.const_names - sig.sorted_constants):
        sort = sig.uf.sort_of(("const", name))
        if sort == TFF_INDIVIDUAL_SORT:
            continue

        def is_that_constant(t: Node, name: str = name) -> bool:
            return isinstance(t, Constant) and t.name == name

        use = _first_atom_text(formulas, is_that_constant)
        if name in numerals:
            raise Tf0Refusal(
                f"{writer}: the numeral {name} would be typed as the sort {sort!r}, because "
                f"it is used at a position that also holds terms of that sort ({use}). In "
                f"this kit a numeral is a constant that may be any element of the universe, "
                f"and nothing says that it is a {sort}; a numeral cannot be written with a "
                f"sort ({name}:{sort}), and the typed declaration would assume it, so a "
                f"prover would answer a stronger question than the other routes ask. To ask "
                f"the kit's question, {_FOF_ADVICE}.",
                reason="unsorted_term_in_sort")
        raise Tf0Refusal(
            f"{writer}: the constant {name!r} is written with a sort nowhere in this "
            f"problem (there is no {name}:{sort}), but the typed text would declare it "
            f"in the sort {sort!r}, because it is used at a position that also holds "
            f"terms of that sort ({use}). In this kit an unannotated constant may be "
            f"any element of the universe, and nothing here says that it is a {sort}; "
            f"the typed declaration would assume it, so a prover would answer a "
            f"stronger question than the other routes ask. Write the constant with its "
            f"sort ({name}:{sort}) if it is meant to be one; otherwise {_FOF_ADVICE}.",
            reason="unsorted_term_in_sort")
    if sig.unsorted_equality is not None and sig.literal_sorts:
        raise unsorted_equality_refusal(
            writer, sig.unsorted_equality.to_unicode_str(), sig.literal_sorts,
            unsorted_type)


def check_typed_reading(formulas: Sequence[Node], *, writer: str = "check_typed_reading",
                        unsorted_type: str = TFF_INDIVIDUAL_SORT) -> None:
    """Refuse a problem for which a TYPED reading would differ from the kit's.

    The kit has one universe, a sort is a non-empty subset of it, a constant
    written ``c:S`` is in ``S`` and an unannotated constant, an unsorted variable
    and a function value are any element. A typed language (TF0, CASL) has disjoint
    types and the writers infer the type of each symbol position, which gives a
    problem a different meaning when (a) an unannotated constant or a function value
    is put into a sort by the inference, (b) an equation over a variable bound by an
    unsorted quantifier meets a sort, (c) one position would hold two sorts, or
    (d) a sort and a predicate share a name. This function runs the same inference
    as :func:`generate_tff_problem` over ``formulas`` (premises and conclusion
    together) and raises :class:`Tf0Refusal` for each of them. It is the check the
    TF0 writer, the NXF writer and :class:`~unicode_logic_kit.atp.hets_backend.HetsBackend`
    share; the last uses it because CASL's inference is the same algorithm with
    ``Thing`` as the type of an unsorted variable.

    ``writer`` is the name that opens the message, ``unsorted_type`` the type an
    unsorted variable has in the text being guarded.

    Raises:
        Tf0Refusal: for each case above, and for a free variable, a symbol at two
            arities and a name that is both a constant and a function (which the
            typed writers cannot write either).
        NotImplementedError: a node outside the fragment the typed writers cover.
    """
    formulas = list(formulas)
    for f in formulas:
        _check_fragment(f)
    expanded = [_expand_all_sorted_counts(f) for f in formulas]
    sig = _analyze(expanded)
    clash = sorted(sig.literal_sorts & set(sig.pred_arity))
    if clash:
        raise Tf0Refusal(
            f"{writer}: {clash[0]!r} is both a sort and a predicate in this problem. "
            "This kit reads a sort as the guard predicate of its name (∀x:S φ is "
            "∀x (S(x) → φ), with ∃x S(x) for its non-emptiness), and a typed text "
            "declares the type and the predicate separately, so a prover would answer "
            "a different question than the other routes do. Rename one of the two, "
            f"or {_FOF_ADVICE}.",
            reason="sort_predicate_name")
    _check_reading(sig, expanded, writer=writer, unsorted_type=unsorted_type)


# =============================================================================
# Name legality: ASCII, first-letter-fold, whole-problem-injective
# =============================================================================

_TPTP_SAFE_RE = re.compile(r"[A-Za-z][A-Za-z0-9_]*")


def _is_tptp_safe(name: str) -> bool:
    return bool(name) and name.isascii() and bool(_TPTP_SAFE_RE.fullmatch(name))


_NON_WORD_CHARACTER = re.compile(r"[^A-Za-z0-9_]")


def _tptp_word_base(name: str, prefix: str) -> str:
    """The base of the replacement for a name that is not a TPTP word: only
    ``[A-Za-z0-9_]``, letter-initial.

    :func:`~unicode_logic_kit.atp._ascii_names.ascii_safe_base` transliterates a
    non-ASCII character (``θ`` is ``theta``, anything else ``u03a9``) and puts
    ``prefix`` in front of a digit-leading or empty name, but it leaves an ASCII
    character that is no TPTP word character (``-``, ``.``, ``:``, ``$``) where it
    is, and a name written like that is rejected by Vampire and by E
    (``has-part``). Every such character is written as the code-point escape
    ``uXXXX`` the transliteration already uses, so ``has-part`` is
    ``hasu002dpart``; a name that starts with an underscore gets ``prefix`` too.
    Injectivity is not this function's job but the renamer's: a token it
    synthesises is de-collided against every name of the problem
    (:func:`~unicode_logic_kit.atp._ascii_names.reserve_rendered`), so
    ``has-part`` next to ``has_part`` stay two symbols, and so do ``has-part``
    next to a name that is itself spelled ``hasu002dpart``.
    """
    base = _NON_WORD_CHARACTER.sub(lambda m: "u%04x" % ord(m.group()),
                                   ascii_safe_base(name, prefix))
    return base if base[:1].isalpha() else prefix + base


def _upper_initial(base: str) -> str:
    """Force uppercase-initial — the kit's own PREDICATE/SORT convention."""
    return base[0].upper() + base[1:] if base else base


def _lower_initial(base: str) -> str:
    """Force lowercase-initial — the kit's own NAME (function/constant) convention."""
    return base[0].lower() + base[1:] if base else base


def _render_token(raw: str) -> str:
    """ASCII-transliterate then TPTP-fold a sanitised (possibly still
    non-ASCII) raw name — the single render function every namespace's
    renamer below de-collides against."""
    return tptp_fold_first_letter(constant_name_to_ascii(raw))


#: Suffix of the replacement name a function/constant receives when its
#: rendered TPTP name equals a predicate's (see the module docstring's "A
#: predicate and a function/constant that fold to the SAME identifier").
#: One shared definition: :mod:`atp._tptp_problem`'s ``fof`` writer imports
#: :func:`_separated_term_token` from here so both dialects mint the same
#: names.
_TERM_SEPARATOR_SUFFIX = "_term"


def _separated_term_token(token: str, taken: Set[str],
                          render: Callable[[str], str] = _render_token) -> str:
    """The replacement for the term-symbol ``token`` whose rendered name
    equals a predicate's: its lower-initial form plus
    :data:`_TERM_SEPARATOR_SUFFIX`, de-collided (numeric suffix) against
    ``taken`` — the RENDERED form of every identifier the problem already
    uses, in any namespace — which this call extends with the rendered
    result (:func:`~unicode_logic_kit.atp._ascii_names.reserve_rendered`).

    ``token`` is already ASCII and letter-initial (a legal name passes
    through the sanitiser untouched, an illegal one was given such a token),
    so the result matches ``[a-z][A-Za-z0-9_]*``: it renders as itself, which
    is what lets a reverse map keyed on the token also match rendered text.
    """
    return reserve_rendered(token[:1].lower() + token[1:] + _TERM_SEPARATOR_SUFFIX,
                            taken, render)


@dataclass
class _Renamer:
    """One symbol namespace's original -> TPTP-legal-token map.

    Two passes (mirrors ``atp._tptp_problem._Renamer``): :meth:`collect`
    reserves every already-legal name immediately (R1: never renamed);
    :meth:`finalize` synthesises a token for everything else, de-collided
    against every reservation so far. :meth:`check_no_collisions` then
    catches the one case the two-pass split cannot rule out by construction:
    two DIFFERENT already-legal names (both bypass synthesis entirely) that
    fold to the SAME rendered identifier (``Foo``/``foo``).
    """

    prefix: str
    case_fix: Callable[[str], str]
    mapping: Dict[str, str] = field(default_factory=dict)
    used: set = field(default_factory=set)
    _pending: List[str] = field(default_factory=list)

    def collect(self, name: str) -> None:
        if name in self.mapping or name in self._pending:
            return
        if _is_tptp_safe(name):
            self.used.add(_render_token(name))
            self.mapping[name] = name
        else:
            self._pending.append(name)

    def finalize(self) -> None:
        for name in self._pending:
            base = self.case_fix(_tptp_word_base(name, self.prefix))
            token = reserve_rendered(base, self.used, _render_token)
            self.mapping[name] = token
        self._pending = []

    def get(self, name: str) -> str:
        return _render_token(self.mapping[name])

    def separate_from(self, predicates: "_Renamer", sorts: "_Renamer") -> None:
        """Rename every name of THIS (function/constant) namespace whose
        rendered token equals a PREDICATE's or a SORT's rendered token, so that
        no term symbol shares a TF0 identifier with either (one flat symbol
        table). A term named like a sort is not read: Vampire resolves the
        term's name to the type (``The sort $tType of the intended term
        argument human … is not an instance of sort human``), while E happens
        to accept it. (A predicate and a sort that share a name never get this
        far: :func:`_check_no_sort_predicate_clash` refuses the pair.)

        Runs after :meth:`check_no_collisions`, so the refusal of two LEGAL
        names of one kind (``Foo``/``foo``) is decided first and unchanged.
        Names are visited in sorted order of their kit-level spelling and the
        replacement is de-collided against every rendered identifier in the
        problem (predicates, sorts, this namespace), so the result is the
        same for the same symbols however the formulas were ordered. Only
        ``mapping`` changes; a namespace with no clash is left byte-for-byte
        as it was.
        """
        predicate_tokens = {_render_token(t) for t in predicates.mapping.values()}
        sort_tokens = {_render_token(t) for t in sorts.mapping.values()}
        taken = predicate_tokens | sort_tokens
        taken |= {_render_token(t) for t in self.mapping.values()}
        for name in sorted(self.mapping):
            if _render_token(self.mapping[name]) in predicate_tokens | sort_tokens:
                self.mapping[name] = _separated_term_token(self.mapping[name], taken)

    def check_no_collisions(self, kind: str) -> None:
        seen: Dict[str, str] = {}
        for name in sorted(self.mapping):
            rendered = _render_token(self.mapping[name])
            if rendered in seen and seen[rendered] != name:
                raise NotImplementedError(
                    f"generate_tff_problem: distinct {kind} names "
                    f"{seen[rendered]!r} and {name!r} would both render as "
                    f"the TFF identifier {rendered!r} — refusing to "
                    "silently merge two distinct symbols; rename one of "
                    "them before exporting this problem."
                )
            seen[rendered] = name


@dataclass
class _Names:
    predicate: _Renamer
    term: _Renamer
    sort: _Renamer


def _check_no_sort_predicate_clash(predicates: _Renamer, sorts: _Renamer) -> None:
    """Refuse a sort and a predicate that render as one TF0 identifier.

    The kit reads a sort as the guard predicate of its name (see the module
    docstring), which TF0, with a type and a predicate in two tables of its own,
    cannot say. The first pair in the sorted order of the kit names is reported,
    so the message does not depend on the order of the formulas."""
    sort_of_word: Dict[str, str] = {}
    for sort in sorted(sorts.mapping):
        sort_of_word.setdefault(_render_token(sorts.mapping[sort]), sort)
    for predicate in sorted(predicates.mapping):
        word = _render_token(predicates.mapping[predicate])
        if word in sort_of_word:
            sort = sort_of_word[word]
            raise Tf0Refusal(
                f"generate_tff_problem: the sort {sort!r} and the predicate "
                f"{predicate!r} would both render as the TF0 identifier {word!r}. "
                "This kit reads a sort as the guard predicate of its name "
                "(∀x:S φ is ∀x (S(x) → φ), with ∃x S(x) for its non-emptiness: "
                "what to_z3, the fof writer and the Prover9 writer do), and TF0 "
                f"cannot say that: it would declare {word!r} once as a type and "
                "once as an unrelated predicate, so a prover would answer a "
                "different question than the other routes do — refusing; rename "
                "one of the two, or write the problem with the fof writer "
                "(generate_tptp_problem_with_mapping), which reads the sort as "
                "that predicate.",
                reason="sort_predicate_name")


def _build_names(sig: _Signature) -> _Names:
    predicates = _Renamer(prefix="p", case_fix=_upper_initial)
    terms = _Renamer(prefix="n", case_fix=_lower_initial)
    sorts = _Renamer(prefix="s", case_fix=_upper_initial)
    for name in sig.pred_arity:
        predicates.collect(name)
    for name in sorted(sig.func_names | sig.const_names):
        terms.collect(name)
    for name in sig.literal_sorts:
        sorts.collect(name)
    predicates.finalize()
    terms.finalize()
    sorts.finalize()
    predicates.check_no_collisions("predicate")
    terms.check_no_collisions("function/constant")
    sorts.check_no_collisions("sort")
    _check_no_sort_predicate_clash(predicates, sorts)
    terms.separate_from(predicates, sorts)
    return _Names(predicates, terms, sorts)


def _sort_text(sort: str, names: _Names) -> str:
    if sort == TFF_INDIVIDUAL_SORT:
        return sort
    return names.sort.get(sort)


# =============================================================================
# Formula rendering — mirrors Node.to_tptp's own (always fully-parenthesised)
# shape exactly, so nesting never needs a bespoke parenthesisation policy.
# =============================================================================

def _render_term(node: Node, names: _Names) -> str:
    if isinstance(node, Variable):
        return node.name.upper()
    if isinstance(node, (Constant, SortedConstant)):
        return names.term.get(node.name)
    if isinstance(node, Function):
        name = names.term.get(node.name)
        if not node.args:
            return name
        args = ",".join(_render_term(a, names) for a in node.args)
        return f"{name}({args})"
    raise AssertionError(f"generate_tff_problem: unreachable term node {type(node).__name__!r}.")


def _render_atom(node: Atom, names: _Names) -> str:
    if is_tptp_boolean_atom(node):
        return node.to_tptp()        # the truth constant's own word, whichever spelling it has
    if node.predicate == "=":
        return f"{_render_term(node.args[0], names)} = {_render_term(node.args[1], names)}"
    if node.predicate == "≠":
        return f"{_render_term(node.args[0], names)} != {_render_term(node.args[1], names)}"
    pred = names.predicate.get(node.predicate)
    if not node.args:
        return pred
    args = ",".join(_render_term(a, names) for a in node.args)
    return f"{pred}({args})"


def _quant_symbol(qtype: str) -> str:
    if qtype in ("∀", "forall"):
        return "!"
    if qtype in ("∃", "exists"):
        return "?"
    raise ValueError(f"generate_tff_problem: unknown quantifier type {qtype!r}.")


def _render(node: Node, names: _Names) -> str:
    if isinstance(node, Atom):
        return _render_atom(node, names)
    if isinstance(node, Not):
        return f"~({_render(node.formula, names)})"
    if isinstance(node, And):
        return f"({_render(node.left, names)} & {_render(node.right, names)})"
    if isinstance(node, Or):
        return f"({_render(node.left, names)} | {_render(node.right, names)})"
    if isinstance(node, Xor):
        return f"({_render(node.left, names)} <~> {_render(node.right, names)})"
    if isinstance(node, Implies):
        return f"({_render(node.left, names)} => {_render(node.right, names)})"
    if isinstance(node, Iff):
        return f"({_render(node.left, names)} <=> {_render(node.right, names)})"
    if isinstance(node, Quantifier):
        var = node.variable.name.upper()
        q = _quant_symbol(node.type)
        return f"({q}[{var}: {TFF_INDIVIDUAL_SORT}]: {_render(node.formula, names)})"
    if isinstance(node, SortedQuantifier):
        var = node.variable.name.upper()
        q = _quant_symbol(node.type)
        sort_text = _sort_text(node.sort, names)
        return f"({q}[{var}: {sort_text}]: {_render(node.formula, names)})"
    raise AssertionError(f"generate_tff_problem: unreachable formula node {type(node).__name__!r}.")


# =============================================================================
# Type declaration rendering
# =============================================================================

def _render_map_type(arg_sorts: List[str], result_sort: str) -> str:
    if not arg_sorts:
        return result_sort
    if len(arg_sorts) == 1:
        return f"{arg_sorts[0]} > {result_sort}"
    return "(" + " * ".join(arg_sorts) + ") > " + result_sort


def _render_type_decls(sig: _Signature, names: _Names) -> List[str]:
    lines: List[str] = []
    counter = [0]

    def next_name(prefix: str) -> str:
        counter[0] += 1
        return f"{prefix}_{counter[0]}"

    for sort in sorted(sig.literal_sorts):
        lines.append(f"tff({next_name('sort_decl')}, type, {_sort_text(sort, names)}: $tType ).")
    for name in sorted(sig.func_names):
        arity = sig.func_arity[name]
        arg_sorts = [_sort_text(sig.uf.sort_of(("func", name, i)), names) for i in range(arity)]
        result_sort = _sort_text(sig.uf.sort_of(("func_result", name)), names)
        type_str = _render_map_type(arg_sorts, result_sort)
        lines.append(f"tff({next_name('func_decl')}, type, {names.term.get(name)}: {type_str} ).")
    for name in sorted(sig.const_names):
        const_sort = _sort_text(sig.uf.sort_of(("const", name)), names)
        lines.append(f"tff({next_name('const_decl')}, type, {names.term.get(name)}: {const_sort} ).")
    for name in sorted(sig.pred_arity):
        arity = sig.pred_arity[name]
        arg_sorts = [_sort_text(sig.uf.sort_of(("pred", name, i)), names) for i in range(arity)]
        type_str = _render_map_type(arg_sorts, TFF_BOOLEAN_SORT)
        lines.append(f"tff({next_name('pred_decl')}, type, {names.predicate.get(name)}: {type_str} ).")
    return lines


# =============================================================================
# Public API
# =============================================================================

def formula_to_tff(formula: Node) -> str:
    """Render a single formula as bare TFF formula text (no ``tff(...)``
    statement wrapper) — the TF0 sibling of
    :func:`unicode_logic_kit.fol.casl_export.formula_to_casl`.

    Runs the full validation pipeline (fragment check, SortedCount lowering,
    free-variable check, arity/sort-conflict detection, name legalisation —
    see the module docstring) on ``formula`` ALONE; a symbol's sort/name
    token is therefore whatever this one formula's own occurrences pin down,
    not shared with any other formula the way :func:`generate_tff_problem`
    shares one signature across a whole premise/conclusion batch.

    A function/constant whose TF0 name equals a predicate's is renamed
    ``<name>_term`` here too, but this function returns bare text and so
    cannot report it; use :func:`generate_tff_problem_with_mapping` when the
    rename has to be undone.

    Raises:
        NotImplementedError: ``formula`` contains a node outside the TF0
            fragment (see module docstring 'Scope'), a name-folding
            collision (two distinct symbols in one namespace), a sort and a
            predicate that render as one identifier, or two LEGAL variables that
            render as one TPTP variable (``x`` and ``X``), or the typed text would
            ask another question than the kit's (see :class:`Tf0Refusal`: an
            unannotated constant, a numeral or a function value typed into a sort, an
            equation over an unsorted variable next to a sort), or a constant, sorted
            constant or function is spelled like a numeral of the formula
            (``Number(1)`` next to ``Constant('1')``). A numeral and ``+ - * /
            < > ≤ ≥`` are NOT refused: they are written as a constant of ``$i`` and
            as uninterpreted symbols (see the module docstring).
        ValueError: a free variable, or an unsatisfiable sort constraint. Every
            refusal that is not a fragment or name-folding one is a
            :class:`Tf0Refusal`, which is a ``ValueError`` and a
            ``NotImplementedError`` at once.
    """
    with refusals_speak_as("formula_to_tff", "generate_tff_problem"):
        [formula], numerals = numerals_as_constants([formula], where="generate_tff_problem")
        _check_fragment(formula)
        formula = legalise_variables(formula)
        expanded = _expand_all_sorted_counts(formula)
        check_variable_names(expanded, where="generate_tff_problem", subject="formula")
        sig = _analyze([expanded], uninterpreted_arithmetic=True)
        names = _build_names(sig)
        _check_reading(sig, [expanded], writer="generate_tff_problem", numerals=numerals)
        return _render(expanded, names)


def generate_tff_problem(premises: List[Node], conclusion: Optional[Node] = None,
                         *, premise_names: Optional[Sequence[str]] = None) -> str:
    """Build a native, genuinely-typed TPTP ``tff`` problem string.

    The TF0 sibling of :func:`atp._tptp_problem.generate_tptp_problem`: same
    ``premise_<i>``/``goal`` naming and axiom/conjecture role split, but
    emits real ``tff(name, type, Sym: Type).`` declarations (one per sort,
    predicate, function, and constant used anywhere in ``premises`` +
    ``conclusion``) followed by formula bodies with genuine typed
    quantifiers, instead of the classical route's guard-predicate encoding.

    Args:
        premises: many-sorted (or plain classical) FOL premises, using
            :class:`~unicode_logic_kit.fol.nodes.SortedQuantifier` /
            :class:`~unicode_logic_kit.fol.nodes.SortedConstant` /
            :class:`~unicode_logic_kit.fol.nodes.SortedCount` freely alongside
            plain :class:`~unicode_logic_kit.fol.nodes.Quantifier` (which
            renders as an explicitly-``$i``-typed variable).
        conclusion: the conjecture, or ``None`` for a problem without one
            (no ``conjecture`` line is written; the prover is asked whether
            the premises are satisfiable).
        premise_names: one name per premise for the ``axiom`` lines instead of
            ``premise_<i>`` — see :func:`generate_tff_problem_with_mapping`, which also
            records them.

    Returns:
        The complete ``tff`` problem text, newline-terminated: type
        declarations first (sorts, then functions, then constants, then
        predicates — declaration-before-use, matching
        ``casl_export.to_casl_spec``'s ordering), then one
        ``tff(premise_<i>, axiom, ...).`` per premise (1-based), then
        ``tff(goal, conjecture, ...).`` unless ``conclusion`` is ``None``.

    Raises:
        NotImplementedError: a node outside the TF0 fragment (see module
            docstring 'Scope'), a name-folding collision, a sort and a predicate
            that render as one identifier, two variables of one formula that
            render as one TPTP variable, or a constant spelled like a numeral
            of the problem — see :func:`formula_to_tff`.
        ValueError: a free variable, an arity conflict, a constant-vs-
            function name clash, or an unsatisfiable sort constraint — see
            :func:`formula_to_tff`. These and the typed-reading refusals
            (an unannotated constant or a function value that the inference
            types into a sort, an equation over an unsorted variable next to a
            sort; see the module docstring and :class:`Tf0Refusal`) are all
            :class:`Tf0Refusal`, a ``ValueError`` and a ``NotImplementedError``
            at once; the backends' automatic mode (``tff=None``) writes ``fof``
            instead when it is raised.

    A function or constant whose TF0 name equals a predicate's (the class
    ``Agent`` and the role function ``agent``) is renamed ``<name>_term`` so
    the problem never declares one identifier at two types; use
    :func:`generate_tff_problem_with_mapping` to also receive the record of
    that rename.
    """
    text, _mapping = _write_tff_problem(premises, conclusion, premise_names)
    return text


def generate_tff_problem_with_mapping(premises: List[Node],
                                      conclusion: Optional[Node] = None,
                                      *, premise_names: Optional[Sequence[str]] = None
                                      ) -> Tuple[str, "TptpNameMap"]:
    """Like :func:`generate_tff_problem`, but also returns the
    :class:`~unicode_logic_kit.atp._tptp_problem.TptpNameMap` recording every
    predicate/function/constant name the writer changed — a name that is not
    TPTP-legal (non-ASCII, digit-leading) and a function/constant renamed
    because its TF0 name equals a predicate's — and the premise names.

    Returns ``(text, name_map)``. ``name_map`` is the same
    :class:`~unicode_logic_kit.atp._tptp_problem.TptpNameMap` the ``fof`` writer
    (:func:`~unicode_logic_kit.atp._tptp_problem.generate_tptp_problem_with_mapping`)
    returns, so :func:`~unicode_logic_kit.atp._tptp_problem.apply_reverse_tptp`
    translates a formula read back from this problem (or from a prover's
    answer to it) to the original kit-level names. Sort names are not part of
    the map: a sort that is not TPTP-legal is still rewritten (as before, with
    no record of it), and two distinct sorts that fold together are refused.
    ``name_map.premises`` holds the premise names in order, also the default ones.

    ``premise_names`` names the premises' ``axiom`` lines instead of
    ``premise_<i>``, exactly as in
    :func:`~unicode_logic_kit.atp._tptp_problem.generate_tptp_problem_with_mapping`; the
    names the writer gives its own lines are ``goal``, ``sort_decl_<n>``,
    ``func_decl_<n>``, ``const_decl_<n>`` and ``pred_decl_<n>`` (a premise named like
    one of them is a :class:`Tf0Refusal`, which is a ``ValueError``).

    Raises what :func:`generate_tff_problem` raises, and, for ``premise_names``,
    ``TypeError`` (a single string, a non-string entry) and ``ValueError`` (other than
    one name per premise, a name no TPTP name can spell, two names that are the same
    as written).
    """
    with refusals_speak_as("generate_tff_problem_with_mapping", "generate_tff_problem"):
        return _write_tff_problem(premises, conclusion, premise_names)


def _write_tff_problem(premises: Sequence[Node], conclusion: Optional[Node],
                       premise_names: Optional[Sequence[str]]
                       ) -> Tuple[str, "TptpNameMap"]:
    """The TF0 writer; its refusals open with ``generate_tff_problem`` (the entry points
    above word them as their own, :func:`~unicode_logic_kit.atp._writer_support
    .refusals_speak_as`)."""
    from ._tptp_problem import TptpNameMap   # deferred: that module imports this one

    premises = list(premises)
    premise_labels = normalise_premise_names(premise_names, len(premises),
                                             where="generate_tff_problem")
    formulas = premises + ([] if conclusion is None else [conclusion])
    # A numeral is a constant of $i (see the module docstring): written under the name of
    # its value, so that the renamer gives it a word and the map reads it back.
    formulas, numerals = numerals_as_constants(formulas, where="generate_tff_problem")
    for f in formulas:
        _check_fragment(f)
    formulas = [legalise_variables(f) for f in formulas]
    expanded = [_expand_all_sorted_counts(f) for f in formulas]
    for f in expanded:
        check_variable_names(f, where="generate_tff_problem", subject="problem")
    sig = _analyze(expanded, uninterpreted_arithmetic=True)
    names = _build_names(sig)
    _check_reading(sig, expanded, writer="generate_tff_problem", numerals=numerals)

    lines = _render_type_decls(sig, names)
    generated = [("goal", "the conjecture")] if conclusion is not None else []
    for line in lines:
        # tff(sort_decl_1, type, ...): the name of each declaration the writer gave
        generated.append((line[len("tff("):line.index(",")], "a type declaration"))
    try:
        check_against_generated(premise_labels, generated, where="generate_tff_problem")
    except ValueError as clash:
        raise Tf0Refusal(str(clash), reason="premise_name") from None
    for label, premise in zip(premise_labels, expanded):
        lines.append(f"tff({tptp_name_token(label)}, axiom, {_render(premise, names)} ).")
    if conclusion is not None:
        lines.append(f"tff(goal, conjecture, {_render(expanded[-1], names)} ).")
    return "\n".join(lines) + "\n", TptpNameMap(
        predicate=dict(names.predicate.mapping), term=dict(names.term.mapping),
        premises=premise_labels, numerals=numerals)


def infer_tff_signature(formulas: Sequence[Node]) -> Signature:
    """Infer a full :class:`~unicode_logic_kit.fol.signature.Signature` (with
    per-argument-position and result sorts pinned down, never ``None``) from
    a batch of formulas — the same union-find inference
    :func:`generate_tff_problem` uses internally, exposed as a genuine
    :class:`Signature` object for callers that want it directly (e.g. to
    call :meth:`Signature.validate` on a further formula against the same
    vocabulary) rather than TFF text.

    Unlike :meth:`Signature.from_formulas` (which leaves every argument
    position unsorted — see that method's docstring), every predicate/
    function argument and every function/constant result here is pinned to
    a concrete sort, defaulting to :data:`TFF_INDIVIDUAL_SORT` (``"$i"``)
    wherever the formulas never connect that position to a declared sort —
    exactly TPTP's own "no type given" reading, and exactly the sort text
    :func:`generate_tff_problem` would emit for it.

    Kit-level names are used verbatim (unlike the TFF-text writer, this
    function does no ASCII/TPTP-legality renaming) — the returned
    :class:`Signature` is meant for use back inside the kit, not for
    rendering TPTP text.

    This is signature INFERENCE, not a decision route: it reports the sort the
    writers' union-find assigns to every position, including the result of a
    function and an unannotated constant at a sorted position, which the kit's
    own reading of a sort does NOT say (a function has no declared result sort).
    :func:`generate_tff_problem` therefore refuses a problem in which the
    inference would do that (see :func:`check_typed_reading`), while this
    function keeps inferring.

    Raises:
        NotImplementedError: a node outside the fragment, and a numeral or an
            arithmetic operator or comparison, which this function does not read as
            an ordinary symbol (:func:`generate_tff_problem` does, and writes it
            under a word of its own: no renaming happens here) — never a
            name-folding collision.
        ValueError: as :func:`formula_to_tff` (free variable, arity/sort
            conflicts).
    """
    formulas = list(formulas)
    for f in formulas:
        _check_fragment(f)
    expanded = [_expand_all_sorted_counts(f) for f in formulas]
    sig = _analyze(expanded)

    def sort_or_none(slot) -> Optional[str]:
        resolved = sig.uf.sort_of(slot)
        return None if resolved == TFF_INDIVIDUAL_SORT else resolved

    predicates: Dict[str, PredicateDecl] = {}
    for name, arity in sig.pred_arity.items():
        arg_sorts = tuple(sort_or_none(("pred", name, i)) for i in range(arity))
        predicates[name] = PredicateDecl(name, arity, arg_sorts)

    functions: Dict[str, FunctionDecl] = {}
    for name, arity in sig.func_arity.items():
        arg_sorts = tuple(sort_or_none(("func", name, i)) for i in range(arity))
        result_sort = sort_or_none(("func_result", name))
        functions[name] = FunctionDecl(name, arity, arg_sorts, result_sort)

    constants: Dict[str, ConstantDecl] = {}
    for name in sig.const_names:
        constants[name] = ConstantDecl(name, sort_or_none(("const", name)))

    sorts: Set[str] = set(sig.literal_sorts)
    # Every declaration above is built with a tuple of argument sorts, never None.
    for pred_decl in predicates.values():
        sorts.update(s for s in pred_decl.arg_sorts or () if s is not None)
    for func_decl in functions.values():
        sorts.update(s for s in func_decl.arg_sorts or () if s is not None)
        if func_decl.result_sort is not None:
            sorts.add(func_decl.result_sort)
    for const_decl in constants.values():
        if const_decl.sort is not None:
            sorts.add(const_decl.sort)

    return Signature(predicates=predicates, functions=functions,
                     constants=constants, sorts=frozenset(sorts))
