"""Direct structural evaluation of a formula against a :class:`FiniteStructure`.

This is model CHECKING (is this sentence true HERE, on this one finite
structure?), computed by walking the formula's AST directly — no prenex /
clausal preprocessing of any kind. The kit already has a Tarskian evaluator
(:func:`unicode_fol_kit.semantics.tarski.satisfies`); it is correct and
general but iterates every quantifier over the WHOLE domain and gives no
special treatment to negated quantifiers or counting. This module targets
exactly the practical bottleneck of that style of checker when the structure
is a molecule (one individual per non-hydrogen atom) and the formula is an
LLM-produced ChEBI class definition. Three design decisions carry the
module's value:

1. **No PNF/CNF normal form, ever.** The existing ChemLog TPTP checker this
   module is meant to out-perform requires prenex form with a CNF matrix, and
   that requirement alone produces two normal-form-*induced* timeout sources
   that direct evaluation simply does not have:

   * A negated existential ``¬(∃o: o(o) ∧ bDOUBLE(c,o))`` is mechanically
     Skolem/prenex-turned into ``∀x (¬o(x) ∨ ¬bDOUBLE(c,x))``, which then has
     to range over *every* atom in the molecule. Evaluated directly, ``¬∃x φ``
     is "search for one witness of φ, stop at the first hit, otherwise true" —
     the same search :func:`evaluate` uses for a bare ``∃``, just negated at
     the end (see :func:`_eval`, the ``Not`` / ``Quantifier`` cases). It never
     becomes a ``∀`` over the whole domain.
   * A top-level disjunction of two existentials gets DISTRIBUTED across a
     CNF matrix — a realistic ``oxoFattyAcid`` definition turns into 32
     disjunctive clauses that must be resolved "simultaneously". Evaluated
     directly, ``Or`` just short-circuits (Python's ``or`` on the two
     recursive calls in :func:`_eval`): the first disjunct that is true wins,
     full stop.

2. **Index-driven candidate generation with dynamically reordered variables.**
   ``∃x (o(x) ∧ bDOUBLE(c,x) ∧ …)`` must not iterate the whole domain for
   ``x``. :func:`_variable_candidates` derives a SOUND (superset) candidate
   set for a quantified variable from the immediate body by intersecting (i)
   :meth:`FiniteStructure.individuals_with` for every unary atom the variable
   occurs in POSITIVELY (i.e. un-negated, and not hidden behind ``∨`` /
   ``→`` / another quantifier — see the harvesting rule below) and (ii)
   :meth:`FiniteStructure.neighbors` (or its local reverse index, see
   :func:`_reverse_neighbors`) for every binary atom relating it to an
   ALREADY-BOUND variable or constant. When several existential variables are
   introduced back to back (``∃x∃y: …``, the common ChemLog shape), the search
   in :func:`_search_exists` picks, at every step, the still-unbound variable
   with the SMALLEST current candidate set (a minimum-remaining-values /
   most-constrained-variable heuristic borrowed from constraint search) —
   concretely: start at the rare heteroatom, then walk outward along its
   bonds, rather than iterating the common atom type first and hoping a bond
   happens to match. This is a HEURISTIC, not a completeness or optimality
   guarantee: it can never make the answer wrong (the harvested constraints
   are all genuinely necessary — see below — so the candidate set is always a
   superset of the true satisfiers, and every candidate is still fully
   re-checked by evaluating the whole body), but a formula whose real
   constraints live behind an ``∨`` or inside a nested ``Count`` gets none of
   this narrowing and falls back to scanning the whole domain for that
   variable — still correct, just not fast.

   *Harvesting rule (soundness argument):* :func:`_harvest_atoms` collects
   atoms reachable from the body through a chain of nested ``And`` nodes only
   (both branches), and stops (does not descend) at ``Or``, ``Not``,
   ``Implies``, ``Iff``, ``Xor``, nested ``Quantifier`` or ``Count``. Anything
   found this way is a conjunct that is unconditionally required for the
   whole formula to hold, so filtering candidates by it can never exclude a
   genuine satisfier — which is exactly what makes it safe to use for a
   NEGATIVE existential search too (``¬∃x φ`` is false only if some candidate
   in this superset satisfies φ; if the whole harvested superset is checked
   and none does, there truly is no witness, precisely because the superset
   was sound).

3. **``Count`` is evaluated natively, not expanded.** The kit's ``Count``
   node (``∃≥n``/``∃≤n``/``∃=n``) already keeps its bound symbolically instead
   of unrolling to n nested existentials — but every OTHER consumer
   (``to_z3``/``to_prover9``/``to_tptp``) still has to lower it to the
   standard distinct-witnesses encoding before use, because those back-ends
   only understand plain FOL. This evaluator does not: :func:`_eval_count`
   counts satisfying individuals directly off the candidate set from (2),
   short-circuiting as soon as the bound is reached for ``op="ge"`` (and as
   soon as it is provably exceeded for ``"le"``/``"eq"``). The motivating
   case is ``hasAtLeast40Carbons``, written today as 40 nested existentials
   plus all C(40,2)=780 pairwise inequalities — a formula shape that is a
   primary timeout source in practice. As ``∃≥40 x c(x)`` against a
   structure of ~50 carbons, this evaluator does a single pass over the
   ~50-element carbon candidate list and stops at the 40th hit (see
   ``tests/test_model_eval.py``'s performance test). Evaluating the SAME
   formula already given in its expanded nested-∃-with-pairwise-≠ form gets
   none of this — the ``≠`` atoms carry no membership information for
   :func:`_harvest_atoms` (deliberately: a disequality is not "individual x
   has property p", so it is not folded into ``individuals_with``), so the
   search degrades back to unindexed backtracking. This is not a bug this
   module could fix by being cleverer about ``≠``: recognising an expanded
   counting encoding and un-expanding it back to ``Count`` is a distinct,
   out-of-scope problem. The fix is architectural — a front-end should emit
   ``Count`` directly, which is exactly what makes this evaluator's
   native-``Count`` path pay off.

Supported nodes: ``Atom`` (incl. ``=``/``≠``, read as term identity — domain
individuals are opaque names, so identity is Python ``==``), ``Not``, ``And``,
``Contrast`` (truth-functionally ``And``: concession is a DISCOURSE relation,
and the node's own contract says every export treats it as ``∧``, so reading
it any other way here would invent a semantics that contract denies), ``Or``,
``Xor``, ``Implies``, ``Iff``, ``Quantifier`` (``forall``/``exists``, ASCII or
``∀``/``∃``), ``Count`` (``ge``/``le``/``eq``) and ``Cardinality``
(``|{v : φ}|``, in a comparison — see below). Argument positions accept only
``Variable`` (via ``assignment``) and ``Constant`` (via
:attr:`FiniteStructure.constants`) — no ``Function`` terms, since a
:class:`FiniteStructure` interprets predicates, not functions. Anything else
(modal/epistemic/temporal operators, Łukasiewicz/fuzzy connectives, lambda
terms, second-order quantifiers, sorted/many-sorted nodes, ``Measure``, ...)
is refused LOUDLY with :class:`UnsupportedNode` rather than silently
approximated — this kit never guesses at semantics it was not told to
implement. ``SortedCount`` was weighed deliberately rather than just skipped:
it needs a sort universe to range over, and :class:`FiniteStructure` has no
``sorts`` concept at all (unlike ``tarski.Structure``) — inventing one here
would mean extending the shared structure contract, out of bounds for this
module.

**Two kinds of term value, kept apart.** ``Cardinality`` denotes a NATURAL
NUMBER, not a domain individual, and every term in an ARGUMENT position must
denote an individual (that is what makes it usable as a predicate argument).
Admitting numbers everywhere really would be a redesign. It is not needed:
over a finite structure a numeric term can only occur as an operand of a
COMPARISON, so the two notions never have to mix. :func:`_term_value` still
answers with individuals and still refuses ``Cardinality``;
:func:`_numeric_value` answers with integers and is reached only from the
comparison branch of :func:`_atom_value`, which switches on the syntactic
shape of the operands. ``|{v : φ}|`` is then simply counted over the domain —
the same "counting is decidable on a finite structure" that makes ``Count``
native here, one level down at the term. This is what lets the finite-domain
backends (:mod:`unicode_fol_kit.atp.clingo_backend`) have their answers
CHECKED: a solver that decides a cardinality comparison is of no use if the
kit cannot verify the model it returns.

**``all_different`` — a SEMANTICS switch, not a performance knob.** Under
plain FOL semantics (``all_different=False``, the default), two separately
quantified existential variables MAY denote the same individual unless the
formula itself says otherwise. ChemLog's TPTP output instead follows the
convention that separately introduced existential variables always denote
PAIRWISE DISTINCT individuals (e.g. ``∃x∃y (c(x) ∧ c(y) ∧ …)`` demands two
DIFFERENT carbons, with no explicit ``x≠y`` anywhere in the text). Passing
``all_different=True`` reproduces that convention, but only among
existentials in an ANCESTOR/DESCENDANT relationship in the formula's syntax
tree — i.e. ``∃y`` sits somewhere inside the MATRIX that ``∃x`` quantifies
over, reachable by descending through any mix of ``Not``/``And``/``Or``/
``Xor``/``Implies``/``Iff``/``∀``/``Count``'s own formula/further ``∃``
layers. Concretely: every individual already bound to such an ENCLOSING
active ``Quantifier(type="exists", …)`` — including an outer layer of the
SAME peeled ``∃x∃x∃x…`` chain reusing one variable name, each layer counted
separately even though later layers shadow earlier ones in the final
assignment — is excluded from the candidate set considered for the next one,
for as long as that enclosing search is still on the call stack (tracked as
``bound_existentials``, extended only inside :func:`_search_exists` /
:func:`_search_exists_witness` and threaded unchanged through every other
node's recursive calls).

**This does NOT reach SIBLING existentials** — two ``∃`` nodes where neither
is nested inside the other's matrix, e.g. ``(∃x φ(x)) ∧ (∃y ψ(y))`` at the
same ``And``, or two ``∃`` under different disjuncts of an ``Or``, or one in
each of two ``Count`` bodies. Each such ``∃`` is evaluated with the
``bound_existentials`` frozenset :func:`_eval` received on entry to that
connective — a sibling's search accumulates its own bindings only for the
duration of its own (fully self-contained) call to :func:`_search_exists`,
and that accumulation is discarded, never propagated sideways, once that
call returns the connective's boolean result. So ``x`` and ``y`` above MAY
still denote the same individual even under ``all_different=True`` — this is
a deliberate, narrow reading of "separately introduced": the module only
tracks quantifiers that are still SYNTACTICALLY ACTIVE (an ancestor whose
witness search has not yet returned) at the point ``∃y`` is evaluated, not
every existential anywhere else in the formula. Widening it to cover
siblings would need a whole-formula pre-pass collecting every ``∃`` in the
tree before evaluation starts (or a different, non-local candidate-pruning
strategy) — a real semantics change, not attempted here; nest the
quantifiers (``∃x (φ(x) ∧ ∃y ψ(y))``) if sibling-level distinctness is what a
formula needs.

This applies ONLY to plain existential ``Quantifier`` nodes. It does NOT
reach into ``Count``: ``Count``'s own ``n`` witnesses are already required to
be pairwise distinct by definition (that is what ``∃≥n`` means) regardless of
this flag, and this flag does not additionally force a ``Count``'s witnesses
to avoid individuals used by an outer, separately scoped ``∃`` — model that
case as nested ``∃`` if you need it. ``∀``-bound variables are never
affected.

**Budget / the three-valued contract.** ``evaluate_detailed(..., budget=k)``
counts one "step" per node visited (see ``_Ctx.tick``, called once per
:func:`_eval` invocation and once per node of the existential search tree in
:func:`_search_exists`); if evaluation would need more than ``k`` steps, it
stops and reports ``exhausted=True`` with ``holds=None`` — an honest UNKNOWN,
never a guessed ``False``. :func:`evaluate` (the boolean-only entry point)
cannot represent "unknown" in its return type, so on exhaustion it raises
:class:`BudgetExhausted` instead of silently returning a value: a caller that
only wants a bool must explicitly decide what an unknown answer means to it,
rather than have this module decide for them. ``witness``/``failing_conjunct``
extraction (see below) is a secondary pass that reuses the caller's budget but
degrades to ``None`` on running out, WITHOUT invalidating the already-decided
``holds`` — see :func:`evaluate_detailed`.

**Uninterpreted symbols.** :meth:`FiniteStructure.holds` /
:meth:`~FiniteStructure.individuals_with` / :meth:`~FiniteStructure.neighbors`
raise ``KeyError`` for a predicate the structure does not interpret. This
module catches that and re-raises :class:`UninterpretedSymbol`, a small typed
exception carrying ``.symbol``/``.arity`` plus a message naming what is
missing — a vocabulary mismatch between a formula and a structure is a bug in
the caller's pipeline, not a reason to call the definition merely unsatisfied.

**``witness`` / ``failing_conjunct`` — best-effort explanations, not a proof
object.** They recognise exactly the ``∧``/``∃``/``∨`` shape that a class
definition like ChEBI's typically has:

* ``witness`` (populated only when ``holds`` is ``True``) is built by
  :func:`_find_witness`: an ``And`` merges the witnesses of both conjuncts: an
  ``∃`` (chain) re-derives, via the SAME candidate search as the main
  evaluation, ONE variable→individual binding that makes it true, and merges
  in the witness of its matrix under that binding; an ``Or`` reports the
  witness of whichever disjunct is true (preferring the left, matching
  evaluation order). Everything else (``Not``, ``∀``, ``Count``, ``Implies``,
  ``Iff``, ``Xor``, a bare ``Atom``) contributes no bindings — not every true
  formula has a natural single-assignment witness, and this does not attempt
  to invent one (a ``Count``'s witness is a SET of individuals, which does
  not fit a ``Dict[str, str]``; a disjunction's untaken branch is simply not
  reported).
* ``failing_conjunct`` (populated only when ``holds`` is ``False``) is built
  by :func:`_find_blame`: it drills through a chain of nested ``And`` nodes
  (left-to-right, the same short-circuit order the main evaluation used) to
  the first conjunct that is actually false, and stops there — an ``Or``, a
  ``Not``, or any other non-``And`` node is reported AS ITSELF (not
  decomposed further: which of two false disjuncts is "the" reason is
  genuinely ambiguous, so this does not guess).
"""

from dataclasses import dataclass
from typing import Dict, FrozenSet, List, Mapping, Optional, Tuple

from .structures import FiniteStructure, Individual, Key
from ..fol.nodes import (
    Node, Variable, Constant, Number, Cardinality,
    Atom, Not, And, Contrast, Or, Xor, Implies, Iff, Quantifier, Count,
)

__all__ = [
    "EvalResult", "BudgetExhausted", "UninterpretedSymbol", "UnsupportedNode",
    "evaluate", "evaluate_detailed",
]

# Quantifier.type spellings accepted for each quantifier kind (matches tarski.py).
_FORALL = ("forall", "∀")
_EXISTS = ("exists", "∃")

Assignment = Mapping[str, Individual]


# ---------------------------------------------------------------------------
# Errors
# ---------------------------------------------------------------------------

class UninterpretedSymbol(LookupError):
    """A formula mentions a predicate/constant this structure does not interpret.

    Raised instead of letting :class:`FiniteStructure`'s bare ``KeyError``
    propagate, so a caller sees WHICH symbol (name + arity) is missing without
    having to parse a generic key-error message. ``.symbol`` and ``.arity``
    carry that structurally (``.arity`` is ``None`` for a missing constant).
    """

    def __init__(self, message: str, *, symbol: str, arity: Optional[int]):
        super().__init__(message)
        self.symbol = symbol
        self.arity = arity


class UnsupportedNode(NotImplementedError):
    """A node type outside this evaluator's classical, non-modal, non-fuzzy,
    non-lambda, non-second-order, first-order fragment (see the module
    docstring's "Supported nodes" list). Raised loudly rather than
    approximated — this kit never silently treats an operator it was not told
    how to evaluate as a no-op."""


class BudgetExhausted(RuntimeError):
    """:func:`evaluate` could not determine a truth value within its step
    budget. The honest reading is UNKNOWN, not ``False`` — ``evaluate`` cannot
    express that in a ``bool`` return, so it raises instead of guessing. Call
    :func:`evaluate_detailed` directly to receive the three-valued
    :class:`EvalResult` (``holds=None``, ``exhausted=True``) rather than an
    exception. ``.steps`` is how many steps were actually spent."""

    def __init__(self, message: str, *, steps: int):
        super().__init__(message)
        self.steps = steps


# ---------------------------------------------------------------------------
# Result object
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class EvalResult:
    """Outcome of :func:`evaluate_detailed`.

    ``holds`` is ``Optional[bool]``: ``None`` iff ``exhausted`` is ``True``
    (the budget ran out before a definitive answer — UNKNOWN, not ``False``).
    ``witness`` (only ever set when ``holds is True``) and ``failing_conjunct``
    (only ever set when ``holds is False``) are best-effort explanations — see
    the module docstring for exactly what shape of formula they can explain.
    ``steps`` is the number of evaluation steps actually performed (see
    ``_Ctx.tick``), including any spent on ``witness``/``failing_conjunct``
    extraction. ``exhausted`` is ``True`` iff the ``budget`` passed to
    :func:`evaluate_detailed` was used up before the core truth value itself
    was decided (running out of budget only *during* witness/blame extraction
    does not set this — see :func:`evaluate_detailed`).
    """

    holds: Optional[bool]
    witness: Optional[Dict[str, str]]
    failing_conjunct: Optional[Node]
    steps: int
    exhausted: bool


# ---------------------------------------------------------------------------
# Budget / evaluation context
# ---------------------------------------------------------------------------

class _BudgetHit(Exception):
    """Internal control-flow signal only: the step budget ran out. Always
    caught inside this module; never escapes evaluate()/evaluate_detailed()."""


class _Ctx:
    """Mutable state threaded through one :func:`evaluate_detailed` call:
    the step counter/budget, the ``all_different`` flag, and a per-call cache
    for reverse binary-relation lookups (see :func:`_reverse_neighbors`) —
    scoped to one call, not to the structure, because unlike
    :meth:`FiniteStructure.neighbors`'s own cache this module cannot attach
    a cache to the (frozen, unowned-by-us) structure object itself."""

    __slots__ = ("budget", "steps", "all_different", "reverse_cache",
                 "harvest_cache")

    def __init__(self, budget: Optional[int], all_different: bool):
        self.budget = budget
        self.steps = 0
        self.all_different = all_different
        self.reverse_cache: Dict[Key, Dict[Individual, FrozenSet[Individual]]] = {}
        #: node -> _harvest_atoms(node). The harvest depends on the FORMULA
        #: alone, never on the assignment, but candidate generation asks for
        #: it once per binding attempt — so without this it is recomputed,
        #: by full recursive descent, on every single step. Keyed by the node
        #: itself (nodes are frozen and hashable), scoped to one call.
        self.harvest_cache: Dict[Node, List[Atom]] = {}

    def tick(self) -> None:
        self.steps += 1
        if self.budget is not None and self.steps > self.budget:
            raise _BudgetHit()


def _extend(assignment: Assignment, name: str, value: Individual) -> Dict[str, Individual]:
    """A copy of ``assignment`` with ``name`` bound to ``value`` (functional
    style — the caller's dict, and every other branch's, is never mutated)."""
    new = dict(assignment)
    new[name] = value
    return new


# ---------------------------------------------------------------------------
# Terms and atoms
# ---------------------------------------------------------------------------

def _term_value(term: Node, structure: FiniteStructure, assignment: Assignment) -> Individual:
    """Evaluate a TERM to an individual. Only ``Variable`` and ``Constant`` are
    supported (see the module docstring) — a :class:`FiniteStructure`
    interprets predicates, not functions, so ``Function``/``Number``/other
    term nodes have nothing to evaluate against and are refused."""
    if isinstance(term, Variable):
        if term.name not in assignment:
            raise ValueError(
                f"model_eval: variable {term.name!r} is free — it is bound by "
                "no enclosing quantifier and was not supplied in assignment=."
            )
        return assignment[term.name]
    if isinstance(term, Constant):
        if term.name not in structure.constants:
            raise UninterpretedSymbol(
                f"model_eval: constant {term.name!r} is not interpreted by this "
                f"structure (known constants: {sorted(structure.constants)}).",
                symbol=term.name, arity=None,
            )
        return structure.constants[term.name]
    raise UnsupportedNode(
        f"model_eval: term node {type(term).__name__} is not supported — only "
        "Variable and Constant terms are evaluated (no Function/Number/"
        "Cardinality/Measure terms; see the module docstring)."
    )


def _holds(structure: FiniteStructure, name: str, args: Tuple[Individual, ...]) -> bool:
    """``structure.holds`` wrapped to turn its bare ``KeyError`` into
    :class:`UninterpretedSymbol`."""
    try:
        return structure.holds(name, args)
    except KeyError:
        raise UninterpretedSymbol(
            f"model_eval: predicate {name!r}/{len(args)} is not interpreted by "
            "this structure (known: "
            f"{[f'{n}/{a}' for n, a in structure.signature()]}).",
            symbol=name, arity=len(args),
        ) from None


#: The comparison predicates, with the integer relation each denotes when its
#: operands are NUMERIC. ``=``/``≠`` appear here as well as in the identity
#: path below: which reading applies is decided by the operands, never by the
#: symbol alone.
_ORDER_OPS = {
    "=": lambda a, b: a == b, "≠": lambda a, b: a != b,
    "<": lambda a, b: a < b, ">": lambda a, b: a > b,
    "≤": lambda a, b: a <= b, "≥": lambda a, b: a >= b,
}

#: Term nodes that denote a NUMBER rather than an individual. Their presence
#: in a comparison is what switches that comparison to the numeric reading.
_NUMERIC_TERMS = (Cardinality, Number)


def _numeric_value(term: Node, structure: FiniteStructure, assignment: Assignment,
                   bound_existentials: FrozenSet[Individual], ctx: "_Ctx") -> int:
    """Evaluate a NUMERIC term to an integer.

    Deliberately separate from :func:`_term_value`, which answers with
    individuals: the two notions of "term value" are incompatible and are kept
    apart rather than merged (see the module docstring). Only the comparison
    branch of :func:`_atom_value` calls this.

    ``|{v : φ}|`` is counted over the whole domain — no candidate narrowing,
    because a COUNT needs every satisfying individual, not one witness, so
    there is nothing to prune. Each individual costs a ``tick``, so the
    evaluation budget covers counting exactly as it covers quantification.
    """
    if isinstance(term, Number):
        return term.value
    if isinstance(term, Cardinality):
        name = term.variable.name
        total = 0
        for d in structure.domain:
            ctx.tick()
            if _eval(term.formula, structure, _extend(assignment, name, d),
                     bound_existentials, ctx):
                total += 1
        return total
    raise UnsupportedNode(
        f"model_eval: {type(term).__name__} does not denote a number, so it "
        "cannot be compared with one — a comparison mixing a cardinality with "
        "a domain individual has no reading here."
    )


def _atom_value(atom: Atom, structure: FiniteStructure, assignment: Assignment,
                bound_existentials: FrozenSet[Individual], ctx: "_Ctx") -> bool:
    """Truth value of an atomic formula.

    Three readings, chosen by the operands rather than by the predicate name:

    * a comparison with at least one NUMERIC operand (``Cardinality`` or
      ``Number``) is arithmetic — ``|{x : P(x)}| > |{y : Q(y)}|`` compares two
      counts;
    * ``=``/``≠`` over individuals is term identity, read directly (domain
      individuals are opaque names, so identity is Python ``==``) rather than
      routed through the structure, which never stores an extension for them;
    * everything else, INCLUDING ``<``/``>``/``≤``/``≥`` between ordinary
      terms, is an ordinary predicate looked up via :func:`_holds`. A
      structure is free to interpret ``<`` as any relation it likes, and this
      evaluator does not impose an order on an uninterpreted symbol.
    """
    if (atom.predicate in _ORDER_OPS and len(atom.args) == 2
            and any(isinstance(a, _NUMERIC_TERMS) for a in atom.args)):
        left = _numeric_value(atom.args[0], structure, assignment,
                              bound_existentials, ctx)
        right = _numeric_value(atom.args[1], structure, assignment,
                               bound_existentials, ctx)
        return _ORDER_OPS[atom.predicate](left, right)
    if atom.predicate in ("=", "≠") and len(atom.args) == 2:
        left_i = _term_value(atom.args[0], structure, assignment)
        right_i = _term_value(atom.args[1], structure, assignment)
        same = left_i == right_i
        return same if atom.predicate == "=" else not same
    args = tuple(_term_value(a, structure, assignment) for a in atom.args)
    return _holds(structure, atom.predicate, args)


# ---------------------------------------------------------------------------
# Candidate generation (design decision #2 — see module docstring)
# ---------------------------------------------------------------------------

def _harvest_atoms(node: Node) -> List[Atom]:
    """Atoms that are UNCONDITIONALLY required by ``node`` — reachable only
    through a chain of nested ``And`` (both branches); does not descend into
    ``Or``/``Not``/``Implies``/``Iff``/``Xor``/nested ``Quantifier``/``Count``.
    See the module docstring's "Harvesting rule" for why this is sound."""
    if isinstance(node, (And, Contrast)):
        return _harvest_atoms(node.left) + _harvest_atoms(node.right)
    if isinstance(node, Atom):
        return [node]
    return []


def _resolved_individual(
    term: Node, structure: FiniteStructure, assignment: Assignment
) -> Optional[Individual]:
    """The individual an ALREADY-BOUND term denotes, or ``None`` if it is not
    (yet) resolvable. Not an error path: candidate generation is a heuristic
    that simply skips an atom it cannot yet use — :func:`_term_value` is what
    enforces free-variable/uninterpreted-constant errors during real
    evaluation."""
    if isinstance(term, Constant) and term.name in structure.constants:
        return structure.constants[term.name]
    if isinstance(term, Variable) and term.name in assignment:
        return assignment[term.name]
    return None


def _reverse_neighbors(
    structure: FiniteStructure, name: str, individual: Individual, ctx: "_Ctx"
) -> Tuple[Individual, ...]:
    """The ``x`` with ``name(x, individual)`` true — the REVERSE direction of
    :meth:`FiniteStructure.neighbors` (which only indexes forward). Built from
    the STORED extension when the relation is stored (cheap: a single pass
    over an already-materialised set, cached in ``ctx`` for the rest of this
    evaluation call). A ``computed`` binary predicate has no extension to
    index — there is no way to invert an opaque callable without evaluating
    it on every pair, so that one case falls back to an O(|domain|) scan of
    :meth:`FiniteStructure.holds`. This is a deliberate, honest, documented
    limitation (see the module docstring), not a silent unsoundness: the
    result is still the exact reverse-neighbour set, just not indexed."""
    key = (name, 2)
    if key in structure.extensions:
        index = ctx.reverse_cache.get(key)
        if index is None:
            index = {}
            for a, b in structure.extensions[key]:
                index.setdefault(b, set()).add(a)
            ctx.reverse_cache[key] = index
        members = index.get(individual, ())
        return tuple(x for x in structure.domain if x in members)
    if key in structure.computed:
        decide = structure.computed[key]
        return tuple(x for x in structure.domain if decide(x, individual))
    raise UninterpretedSymbol(
        f"model_eval: predicate {name!r}/2 is not interpreted by this structure "
        f"(known: {[f'{n}/{a}' for n, a in structure.signature()]}).",
        symbol=name, arity=2,
    )


def _variable_candidates(
    var_name: str, body: Node, structure: FiniteStructure, assignment: Assignment,
    ctx: "_Ctx",
) -> Tuple[Individual, ...]:
    """A SOUND (superset) candidate set for ``var_name``, in ``structure``
    domain order: the intersection of every unary/binary constraint on it
    harvested from ``body`` (see :func:`_harvest_atoms`). Falls back to the
    WHOLE domain if nothing usable was found — still correct (every candidate
    is fully re-checked by evaluating the whole body), just not narrowed."""
    harvested = ctx.harvest_cache.get(body)
    if harvested is None:
        harvested = _harvest_atoms(body)
        ctx.harvest_cache[body] = harvested
    found: Optional[set] = None
    for atom in harvested:
        if atom.predicate in ("=", "≠"):
            continue  # (dis)equality carries no domain-membership information
        if len(atom.args) == 1:
            (t,) = atom.args
            if isinstance(t, Variable) and t.name == var_name:
                try:
                    members = set(structure.individuals_with(atom.predicate))
                except KeyError:
                    raise UninterpretedSymbol(
                        f"model_eval: predicate {atom.predicate!r}/1 is not "
                        "interpreted by this structure (known: "
                        f"{[f'{n}/{a}' for n, a in structure.signature()]}).",
                        symbol=atom.predicate, arity=1,
                    ) from None
                found = members if found is None else (found & members)
        elif len(atom.args) == 2:
            t0, t1 = atom.args
            is_v0 = isinstance(t0, Variable) and t0.name == var_name
            is_v1 = isinstance(t1, Variable) and t1.name == var_name
            if is_v0 and not is_v1:
                other = _resolved_individual(t1, structure, assignment)
                if other is not None:
                    members = set(_reverse_neighbors(structure, atom.predicate, other, ctx))
                    found = members if found is None else (found & members)
            elif is_v1 and not is_v0:
                other = _resolved_individual(t0, structure, assignment)
                if other is not None:
                    try:
                        members = set(structure.neighbors(atom.predicate, other))
                    except KeyError:
                        raise UninterpretedSymbol(
                            f"model_eval: predicate {atom.predicate!r}/2 is not "
                            "interpreted by this structure (known: "
                            f"{[f'{n}/{a}' for n, a in structure.signature()]}).",
                            symbol=atom.predicate, arity=2,
                        ) from None
                    found = members if found is None else (found & members)
            # both/neither position is var_name: this atom carries no usable
            # constraint yet (rel(x,x) self-pairs, or both ends still unbound).
        # arity 0 or > 2: not a per-individual membership constraint, skip.
    if found is None:
        return structure.domain
    return tuple(d for d in structure.domain if d in found)


def _peel_exists_chain(node: Quantifier) -> Tuple[List[str], Node]:
    """Peel a maximal run of adjacent ``∃`` layers starting at ``node`` (which
    must itself be existential); return the bound variable names in outer-to-
    inner order and the innermost non-quantifier matrix."""
    names = [node.variable.name]
    body = node.formula
    while isinstance(body, Quantifier) and body.type in _EXISTS:
        names.append(body.variable.name)
        body = body.formula
    return names, body


def _pick_most_constrained(
    remaining: List[str], matrix: Node, structure: FiniteStructure,
    assignment: Assignment, bound_existentials: FrozenSet[Individual], ctx: "_Ctx",
) -> Tuple[str, Tuple[Individual, ...]]:
    """The most-constrained-variable heuristic: among ``remaining``, the
    variable whose CURRENT candidate set (given what is bound so far) is
    smallest — recomputed at every call, since a bond-neighbour constraint
    only becomes usable once the other end of the bond is bound. Ties keep
    the first (leftmost) variable with the smallest set seen so far."""
    best_name, best_cands = None, None
    for name in remaining:
        cands = _variable_candidates(name, matrix, structure, assignment, ctx)
        if ctx.all_different:
            cands = tuple(c for c in cands if c not in bound_existentials)
        if best_cands is None or len(cands) < len(best_cands):
            best_name, best_cands = name, cands
            if not best_cands:
                break  # an empty candidate set cannot be beaten
    return best_name, best_cands


def _search_exists(
    remaining: List[str], matrix: Node, structure: FiniteStructure,
    assignment: Assignment, bound_existentials: FrozenSet[Individual], ctx: "_Ctx",
) -> bool:
    """Backtracking search for a satisfying binding of ``remaining`` existential
    variables over ``matrix``, dynamically reordered by
    :func:`_pick_most_constrained` at every step (design decision #2)."""
    ctx.tick()
    if not remaining:
        return _eval(matrix, structure, assignment, bound_existentials, ctx)
    name, cands = _pick_most_constrained(
        remaining, matrix, structure, assignment, bound_existentials, ctx)
    # Remove exactly the ONE occurrence of `name` that was just picked, not
    # every occurrence of that name — a chain can reuse a variable name
    # across layers (`∃x∃x∃x φ`, each layer legitimately shadowing the last),
    # and `[n for n in remaining if n != name]` used to drop all of them at
    # once, collapsing an N-deep same-named chain into a single quantifier
    # (see the module docstring's `all_different` bullet: this used to let
    # `all_different=True` silently require only 1 witness instead of N).
    # `_pick_most_constrained` always resolves ties by keeping the FIRST
    # (leftmost) `remaining` entry with the smallest candidate set, and two
    # occurrences of the same name always have IDENTICAL candidate sets at
    # this point (same matrix, same assignment, same bound_existentials), so
    # the leftmost remaining occurrence of `name` is always the one that was
    # just picked — exactly what `list.remove` (first-occurrence) deletes.
    rest = list(remaining)
    rest.remove(name)
    for c in cands:
        if _search_exists(rest, matrix, structure, _extend(assignment, name, c),
                           bound_existentials | {c}, ctx):
            return True
    return False


def _search_exists_witness(
    remaining: List[str], matrix: Node, structure: FiniteStructure,
    assignment: Assignment, bound_existentials: FrozenSet[Individual], ctx: "_Ctx",
) -> Optional[Dict[str, Individual]]:
    """Like :func:`_search_exists` but returns the satisfying binding (or
    ``None``) instead of just whether one exists — used by :func:`_find_witness`."""
    ctx.tick()
    if not remaining:
        return {} if _eval(matrix, structure, assignment, bound_existentials, ctx) else None
    name, cands = _pick_most_constrained(
        remaining, matrix, structure, assignment, bound_existentials, ctx)
    # See the identical `rest` line in _search_exists just above for why this
    # must remove exactly one (the first-occurring, i.e. just-picked)
    # occurrence of `name` rather than every occurrence of that name.
    rest = list(remaining)
    rest.remove(name)
    for c in cands:
        sub = _search_exists_witness(rest, matrix, structure, _extend(assignment, name, c),
                                      bound_existentials | {c}, ctx)
        if sub is not None:
            merged = {name: c}
            merged.update(sub)
            return merged
    return None


# ---------------------------------------------------------------------------
# Quantifier / Count evaluation
# ---------------------------------------------------------------------------

def _eval_quantifier(
    node: Quantifier, structure: FiniteStructure, assignment: Assignment,
    bound_existentials: FrozenSet[Individual], ctx: "_Ctx",
) -> bool:
    if node.type in _FORALL:
        # ∀ iterates the whole domain — see the module docstring: this
        # evaluator's optimisations target ∃/Count (the bottlenecks that
        # actually bite), not ∀, which has no analogous candidate-narrowing
        # opportunity without also inspecting the (possibly absent) guard
        # implicit in an implication body.
        name = node.variable.name
        for d in structure.domain:
            if not _eval(node.formula, structure, _extend(assignment, name, d),
                         bound_existentials, ctx):
                return False
        return True
    if node.type in _EXISTS:
        names, matrix = _peel_exists_chain(node)
        return _search_exists(names, matrix, structure, assignment, bound_existentials, ctx)
    raise ValueError(f"model_eval: unknown quantifier type {node.type!r}")


def _eval_count(
    node: Count, structure: FiniteStructure, assignment: Assignment,
    bound_existentials: FrozenSet[Individual], ctx: "_Ctx",
) -> bool:
    """∃≥n / ∃≤n / ∃=n, counted directly over the (index-narrowed) candidate
    set for the bound variable — see design decision #3 in the module
    docstring. ``all_different`` does not apply here: n distinct witnesses are
    already what ``Count`` means, independent of that flag."""
    name = node.variable.name
    n = node.n.value
    cands = _variable_candidates(name, node.formula, structure, assignment, ctx)
    count = 0
    for d in cands:
        if _eval(node.formula, structure, _extend(assignment, name, d), bound_existentials, ctx):
            count += 1
            if node.op == "ge" and count >= n:
                return True
        if node.op in ("le", "eq") and count > n:
            return False
    if node.op == "ge":
        return count >= n
    if node.op == "le":
        return count <= n
    if node.op == "eq":
        return count == n
    raise ValueError(f"model_eval: unknown Count op {node.op!r}")


# ---------------------------------------------------------------------------
# Core recursive evaluator
# ---------------------------------------------------------------------------

def _eval(
    node: Node, structure: FiniteStructure, assignment: Assignment,
    bound_existentials: FrozenSet[Individual], ctx: "_Ctx",
) -> bool:
    """Evaluate ``node`` directly against ``structure`` — the single
    recursive engine behind :func:`evaluate`/:func:`evaluate_detailed`. One
    step is charged per call (see ``_Ctx.tick``, which may raise the internal
    ``_BudgetHit`` signal). ``And``/``Or`` short-circuit via Python's own
    ``and``/``or`` on the two recursive calls; ``Implies`` short-circuits
    explicitly on a false antecedent."""
    ctx.tick()
    if isinstance(node, Atom):
        return _atom_value(node, structure, assignment, bound_existentials, ctx)
    if isinstance(node, Not):
        return not _eval(node.formula, structure, assignment, bound_existentials, ctx)
    if isinstance(node, (And, Contrast)):
        # Contrast (``P Ⓒ Q``, whereas/although/but) is truth-functionally
        # conjunction — concession is a DISCOURSE relation, not a
        # truth-functional one. The node exists so a front-end can keep the
        # contrast instead of flattening it to ∧, and every export already
        # treats it as ∧; evaluating it any other way here would invent a
        # semantics the node's own contract denies.
        return (_eval(node.left, structure, assignment, bound_existentials, ctx)
                and _eval(node.right, structure, assignment, bound_existentials, ctx))
    if isinstance(node, Or):
        return (_eval(node.left, structure, assignment, bound_existentials, ctx)
                or _eval(node.right, structure, assignment, bound_existentials, ctx))
    if isinstance(node, Xor):
        return (_eval(node.left, structure, assignment, bound_existentials, ctx)
                != _eval(node.right, structure, assignment, bound_existentials, ctx))
    if isinstance(node, Implies):
        if not _eval(node.left, structure, assignment, bound_existentials, ctx):
            return True
        return _eval(node.right, structure, assignment, bound_existentials, ctx)
    if isinstance(node, Iff):
        return (_eval(node.left, structure, assignment, bound_existentials, ctx)
                == _eval(node.right, structure, assignment, bound_existentials, ctx))
    if isinstance(node, Quantifier):
        return _eval_quantifier(node, structure, assignment, bound_existentials, ctx)
    if isinstance(node, Count):
        return _eval_count(node, structure, assignment, bound_existentials, ctx)
    raise UnsupportedNode(
        f"model_eval: node type {type(node).__name__} is not supported by direct "
        "structural evaluation — only Atom/Not/And/Or/Xor/Implies/Iff/Quantifier/"
        "Count are (see the module docstring's 'Supported nodes'). Modal, "
        "lambda, fuzzy, second-order, sorted, and other MSFL/kit extensions are "
        "out of scope here; use the dedicated evaluator for that fragment."
    )


# ---------------------------------------------------------------------------
# Explanations (best-effort — see the module docstring)
# ---------------------------------------------------------------------------

def _find_witness(
    node: Node, structure: FiniteStructure, assignment: Assignment,
    bound_existentials: FrozenSet[Individual], ctx: "_Ctx",
) -> Dict[str, Individual]:
    """Best-effort variable→individual bindings that make a TRUE ``node``
    true — see the module docstring's "witness" bullet for exactly which
    node shapes contribute bindings."""
    ctx.tick()
    if isinstance(node, And):
        w = _find_witness(node.left, structure, assignment, bound_existentials, ctx)
        w2 = _find_witness(node.right, structure, assignment, bound_existentials, ctx)
        merged = dict(w)
        merged.update(w2)
        return merged
    if isinstance(node, Or):
        if _eval(node.left, structure, assignment, bound_existentials, ctx):
            return _find_witness(node.left, structure, assignment, bound_existentials, ctx)
        return _find_witness(node.right, structure, assignment, bound_existentials, ctx)
    if isinstance(node, Quantifier) and node.type in _EXISTS:
        names, matrix = _peel_exists_chain(node)
        binding = _search_exists_witness(names, matrix, structure, assignment,
                                          bound_existentials, ctx)
        if binding is None:
            return {}  # defensive: should not happen if node evaluated True
        new_assignment = dict(assignment)
        new_assignment.update(binding)
        new_bound = bound_existentials | set(binding.values())
        w = dict(binding)
        w.update(_find_witness(matrix, structure, new_assignment, new_bound, ctx))
        return w
    return {}  # Not / ∀ / Count / Implies / Iff / Xor / Atom: no natural witness


def _find_blame(
    node: Node, structure: FiniteStructure, assignment: Assignment,
    bound_existentials: FrozenSet[Individual], ctx: "_Ctx",
) -> Node:
    """Drill through a spine of nested ``And`` (left-to-right, the same
    short-circuit order evaluation used) to the first conjunct that is
    actually false; any other node type is returned as itself (not
    decomposed — see the module docstring's "failing_conjunct" bullet)."""
    ctx.tick()
    if isinstance(node, And):
        if not _eval(node.left, structure, assignment, bound_existentials, ctx):
            return _find_blame(node.left, structure, assignment, bound_existentials, ctx)
        return _find_blame(node.right, structure, assignment, bound_existentials, ctx)
    return node


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------

def evaluate_detailed(
    formula: Node, structure: FiniteStructure, *,
    all_different: bool = False,
    assignment: Optional[Assignment] = None,
    budget: Optional[int] = None,
) -> EvalResult:
    """Evaluate ``formula`` against ``structure`` and return a full
    :class:`EvalResult` (three-valued: ``holds`` is ``None`` iff the budget
    was exhausted before a definitive answer). See the module docstring for
    the semantics of ``all_different``, the budget contract, and exactly what
    ``witness``/``failing_conjunct`` can and cannot explain.

    Raises:
        UninterpretedSymbol: ``formula`` mentions a predicate/constant
            ``structure`` does not interpret.
        UnsupportedNode: ``formula`` contains a node type outside this
            evaluator's classical first-order fragment.
        ValueError: ``formula`` has a free variable not covered by
            ``assignment``.
    """
    env: Dict[str, Individual] = dict(assignment) if assignment else {}
    ctx = _Ctx(budget, all_different)
    try:
        holds = _eval(formula, structure, env, frozenset(), ctx)
    except _BudgetHit:
        return EvalResult(holds=None, witness=None, failing_conjunct=None,
                           steps=ctx.steps, exhausted=True)

    # The core answer is already decided at this point; witness/failing_conjunct
    # extraction is a secondary, best-effort pass that reuses ctx's step budget
    # but — deliberately — cannot retroactively turn a decided answer back into
    # "exhausted": running out here just means the explanation is dropped.
    try:
        if holds:
            witness = _find_witness(formula, structure, env, frozenset(), ctx)
            failing = None
        else:
            witness = None
            failing = _find_blame(formula, structure, env, frozenset(), ctx)
    except _BudgetHit:
        witness = None
        failing = None

    return EvalResult(holds=holds, witness=witness, failing_conjunct=failing,
                       steps=ctx.steps, exhausted=False)


def evaluate(
    formula: Node, structure: FiniteStructure, *,
    all_different: bool = False,
    assignment: Optional[Assignment] = None,
    budget: Optional[int] = None,
) -> bool:
    """Boolean-only convenience wrapper around :func:`evaluate_detailed`.

    Raises :class:`BudgetExhausted` if ``budget`` runs out before a
    definitive answer — see the module docstring's budget contract for why
    this cannot simply return ``False``. Same other exceptions as
    :func:`evaluate_detailed`.
    """
    result = evaluate_detailed(formula, structure, all_different=all_different,
                                assignment=assignment, budget=budget)
    if result.exhausted:
        raise BudgetExhausted(
            f"model_eval.evaluate: budget of {budget} steps was exhausted after "
            f"{result.steps} steps before a definitive truth value could be "
            "established — the result is UNKNOWN, not False. Raise `budget`, or "
            "call evaluate_detailed() to receive the three-valued EvalResult "
            "instead of an exception.",
            steps=result.steps,
        )
    return result.holds
