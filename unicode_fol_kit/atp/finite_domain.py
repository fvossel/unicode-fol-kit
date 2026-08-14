"""Solver-independent core for the finite-domain (ASP / CP) refutation backends.

Two backends (``ClingoBackend``, ``MinizincBackend`` — built alongside this
module, not in it) decide FOL questions by searching for a finite
countermodel of ``premises ∧ ¬φ``: they GROUND that goal into ASP or CP and
let clingo / MiniZinc search. Everything the two backends would otherwise
duplicate lives here instead, so ``unsupported`` and a re-verified
countermodel read identically whichever solver was asked:

* :class:`FiniteDomainProblem` — the one problem shape both backends encode:
  a batch of sentences to satisfy simultaneously, a domain size, a
  :class:`~unicode_fol_kit.fol.signature.Signature`, and the
  distinct-constants convention.
* :func:`fragment_check` — the single gate: is a sentence even IN the
  fragment these backends can ground? Unsorted classical FOL plus the
  counting fragment (``Count``, ``Cardinality``) is encodable — function
  symbols are NOT, refused for the same "cannot be checked back" reason
  :func:`verify_model` exists to enforce; everything without a reading over
  one finite, bivalent, first-order structure is refused BY NAME (see
  "Fragment boundary" below).
* :func:`structure_from_solution` — turn a solver's true ground atoms back
  into a :class:`~unicode_fol_kit.semantics.structures.FiniteStructure`,
  including the shared "function = total relation + functionality
  constraint" reconstruction so neither backend has to invent it twice.
* :func:`verify_model` — the safety net: re-check a reconstructed structure
  against the ORIGINAL sentences with the kit's own independent evaluator
  before a backend is allowed to call anything REFUTED. See "Known
  verification gap" below — a narrow residual collision between this
  module's own scope and an existing module it does not own, down from
  four node types to one (``Contrast``) now that the counting fragment is
  independently verifiable and ``Function`` is refused upstream instead.

This module never grounds anything itself. clingo and MiniZinc both ground
better than a hand-rolled loop here would (see the design note), so the job
here stops at emitting a solver-agnostic PROBLEM and re-checking a
solver-agnostic SOLUTION; the ASP/CP text itself is each backend's own.

THE ONE RULE THIS MODULE EXISTS TO PROTECT
-------------------------------------------
Both backends are refutation-only: a finite model of ``premises ∧ ¬φ``
proves ``φ`` REFUTED, but the absence of one up to a size bound proves
NOTHING (first-order logic has no finite model property). Neither backend
may ever report ``PROVED`` from this search. :func:`verify_model` is the
second half of that discipline: a model-finder that hands back a structure
that does not actually satisfy the goal is worse than one that finds
nothing, so every witness is re-checked here before a backend is allowed to
call it REFUTED.

Fragment boundary (what :func:`fragment_check` accepts and refuses)
---------------------------------------------------------------------
IN: ``Atom``, ``Not``, ``And``, ``Or``, ``Xor``, ``Implies``, ``Iff``,
``Contrast`` (truth-functionally ``And`` — see its own docstring),
``Quantifier`` (unsorted ``∀``/``∃`` only), ``Count`` (``∃≥n``/``∃≤n``/
``∃=n``), ``Cardinality`` (``|S|`` as a term), and the term vocabulary
``Variable``/``Constant``/``Number``. This is "unsorted classical FOL plus
the counting fragment" — exactly the scope the design this module
implements calls for. ``Function`` is deliberately NOT part of this term
vocabulary — see its own bullet below.

OUT, each refused by name with the reason that node type has no reading
over a SINGLE finite bivalent structure:

* ``Measure`` — a degree on an uninterpreted ORDERED codomain; nothing for
  ``#count``/``sum`` to range over.
* the sorted family (``SortedQuantifier``, ``SortedConstant``,
  ``SortedCount``, ``SortedCardinality``) — needs per-sort subdomains
  :class:`FiniteDomainProblem` does not carry; a real extension, not a
  detail, and left for a later revision.
* the modal/temporal/epistemic/hybrid family (``Box``, ``Diamond``,
  ``Knows``, ``Believes``, ``Says``, ``Wants``, ``Always``, ``Eventually``,
  ``Next``, ``Until``, ``Historically``, ``Once``, ``Previous``, ``Since``,
  ``Obligatory``, ``Permitted``, ``Would``, ``Might``, ``Announce``,
  ``AnnounceDiamond``, ``Nominal``, ``At``) — these quantify over POSSIBLE
  WORLDS, not domain individuals; the modal family already has its own
  finite-model backend (``kripke-enum``).
* ``SecondOrderQuantifier`` — ranges over relations, not individuals.
* the substructural family (linear logic's ``Tensor``, ``With``, ``OPlus``,
  ``LinearImplies``, ``OfCourse``, ``One``, ``Top``, ``Zero``; Lambek's
  ``Product``, ``Under``, ``Over``) — these track RESOURCE USE, not truth in
  one structure.
* the lambda family (``LambdaVar``, ``Lambda``, ``Application``) — functions
  FROM formulas TO formulas; higher-order, not first-order individuals.
* the team-semantic family (``Dependence``, ``SlashedExists``) — evaluated
  against a TEAM (a set of assignments), not a single structure; not named
  in the originating design's exclusion table but excluded for the
  identical reason, so it gets its own family here rather than being
  silently swept into "modal" or left unclassified.
* the Łukasiewicz fuzzy family (``WeakConjunction``, ``WeakDisjunction``,
  ``StrongConjunction``, ``StrongDisjunction``, ``LukNegation``,
  ``LukImplication``, ``LukEquivalence``) — many-valued; a finite
  countermodel search assumes classical, two-valued truth. Also not named
  in the design's own table, excluded for the same reason as team
  semantics.
* ``Function`` — a solver can find a model containing one, but
  :class:`~unicode_fol_kit.semantics.structures.FiniteStructure` has fields
  for domain/extensions/computed/constants and NO slot for a function
  interpretation, so such a model could never be checked back by
  :func:`verify_model` — and this layer does not hand out countermodels it
  cannot verify (see "THE ONE RULE" above). Refused HERE, at
  :func:`fragment_check`, rather than discovered later as a verification
  failure: an honest, machine-stable ``UNKNOWN``/``"unsupported"`` instead
  of a late ``ERROR``/``"infra"`` that reads like a transient fault and
  invites a pointless retry. Adding function interpretations to
  ``FiniteStructure`` touches serialisation, the evaluator, and every
  consumer of a structure — a separate, larger piece of work, not a detail
  of this backend (see ``_FUNCTION_REASON`` below, and
  :func:`structure_from_solution`'s own function-reconstruction machinery,
  kept for direct callers even though neither backend can reach it via this
  gate any more).

A node type this module has never heard of (a future addition to the kit's
AST) is refused too, with a generic reason, rather than silently accepted —
default-deny, matching :mod:`~unicode_fol_kit.fol.signature`'s own
loud-refusal convention.

Known verification gap (an objection, not a silent deviation)
-----------------------------------------------------------------
:func:`verify_model` is specified to re-check a reconstructed structure by
running the kit's OWN independent evaluator,
:func:`~unicode_fol_kit.semantics.model_eval.evaluate` (re-exported as
``evaluate_in_structure``), over every sentence — and that is exactly what
it does here. Two of the four node types that used to defeat that evaluator
no longer do:

``Cardinality`` and ``Number`` (as a comparison operand) are now read
ARITHMETICALLY by ``evaluate_in_structure`` itself: its comparison branch
(``_atom_value``, via ``_numeric_value``) counts ``|{v : φ}|`` and compares
it against another count or a bare numeral whenever the comparison has at
least one numeric operand (see that module's own docstring, "Two kinds of
term value, kept apart"). The counting fragment this whole design exists to
decide (see the design's §1) is therefore now DECIDED AND VERIFIED end to
end: ``|{x : P(x)}| > |{y : Q(y)}|`` can be correctly REFUTED by
clingo/MiniZinc, reconstructed by :func:`structure_from_solution`, AND
independently confirmed here — no more downgrade to ``ERROR``/``"infra"``
for that shape of sentence.

That leaves two node types this evaluator still cannot touch — but they no
longer sit at the same level:

* ``Function`` still makes ``evaluate_in_structure`` raise
  ``UnsupportedNode`` — a :class:`~unicode_fol_kit.semantics.structures.FiniteStructure`
  interprets predicates and constants, never functions (see
  ``_FUNCTION_REASON`` below), and that has not changed. Call
  :func:`verify_model` DIRECTLY on a sentence containing one and it still
  reports "could not verify", exactly as before. But this is now MOOT for
  the two backends this module serves: :func:`fragment_check` refuses
  ``Function`` BY NAME before a backend ever grounds anything (see
  "Fragment boundary" above), so no function-bearing sentence either
  backend controls ever reaches :func:`structure_from_solution` or
  :func:`verify_model` in the first place. What is left here is a fact
  about :func:`verify_model` as a general-purpose function callable on ANY
  sentence, not a live gap in either backend's actual behaviour.
* ``Contrast`` IS in the encodable fragment (:func:`fragment_check` admits
  it — truth-functionally ``And``, see its own docstring) but is genuinely
  NOT in ``evaluate_in_structure``'s supported-node list (that module's own
  "Supported nodes" section stops at ``Atom``/``Not``/``And``/``Or``/
  ``Xor``/``Implies``/``Iff``/``Quantifier``/``Count``) — it raises
  ``UnsupportedNode`` there like any node type the evaluator has never
  heard of. A sentence built with ``Contrast`` can therefore still be
  correctly REFUTED by a backend and correctly reconstructed, and still
  fail :func:`verify_model` — not because the countermodel is wrong, but
  because the independent checker this module is told to call cannot
  evaluate ``Contrast`` AT ALL. Per this module's OWN rule above (never
  hand back an unverified countermodel), that failure is treated as "could
  not verify" and a calling backend must downgrade to ``ERROR``/``"infra"``
  rather than ever return ``REFUTED`` for such a sentence — SOUND, but,
  unlike ``Function`` above, this one IS still live: closing it needs
  either :mod:`~unicode_fol_kit.semantics.model_eval` to grow a
  ``Contrast`` case (out of this file's assignment — that module is owned
  elsewhere) or :func:`verify_model` to be redesigned with its own
  evaluator for this one connective (a decision this module deliberately
  does not make unilaterally; see the instructions this file was written
  under).

Separately, and NOT a gap: comparing a domain INDIVIDUAL with a numeral
remains refused, deliberately. ``∀x (x = 1)`` reaches the same comparison
branch as a genuine counting comparison, but ``_numeric_value`` is only
ever handed the operand syntactically marked numeric (``Cardinality``/
``Number``); called on the OTHER, individual-denoting operand it raises
``UnsupportedNode`` ("does not denote a number, so it cannot be compared
with one"). Admitting numeric terms into comparisons between two numeric
operands is the whole of what the counting fragment calls for; admitting
them into a comparison against a domain individual was never in scope, and
staying refused there is correct, not incomplete — a structure whose
individuals happen to be named ``"0"``/``"1"``/… must not tempt anyone into
reading those names as integers.

This is reported here, in the code, rather than silently worked around, and
again in :func:`verify_model`'s own docstring.
"""

import itertools
from dataclasses import dataclass
from typing import Dict, Iterable, Optional, Sequence, Tuple, Type

from ..fol.nodes import (
    Node,
    Variable, Constant, Number, Function,
    Atom, Not, And, Or, Xor, Implies, Iff, Quantifier,
    Count, Cardinality, Contrast, Measure,
    SortedQuantifier, SortedConstant, SortedCount, SortedCardinality,
    Box, Diamond, Knows, Believes, Says, Wants,
    Always, Eventually, Next, Until,
    Historically, Once, Previous, Since,
    Obligatory, Permitted, Would, Might,
    Announce, AnnounceDiamond,
    SecondOrderQuantifier,
    Nominal, At,
    Dependence, SlashedExists,
    Tensor, With, OPlus, LinearImplies, OfCourse, One, Top, Zero,
    Product, Under, Over,
    WeakConjunction, WeakDisjunction, StrongConjunction, StrongDisjunction,
    LukNegation, LukImplication, LukEquivalence,
    LambdaVar, Lambda, Application,
)
from ..fol.signature import Signature
from ..semantics.structures import FiniteStructure
from ..semantics.model_eval import (
    evaluate as _evaluate_in_structure,
    UninterpretedSymbol, UnsupportedNode,
)

__all__ = [
    "FiniteDomainProblem", "fragment_check", "structure_from_solution", "verify_model",
]


# =============================================================================
# FiniteDomainProblem
# =============================================================================

@dataclass(frozen=True)
class FiniteDomainProblem:
    """A finite-domain search problem: sentences to satisfy over a bounded domain.

    Both backends encode the SAME shape into their own solver language, so a
    problem built once is what ``ClingoBackend`` and ``MinizincBackend`` both
    read — this is what makes the two backends' answers comparable at all.

    ``sentences`` are conjoined (every one must hold simultaneously); for a
    refutation search a caller passes ``premises + (¬φ,)``, but this class
    has no opinion about where its sentences came from — it is the shared
    CONTAINER, not the refutation-goal-building logic (that lives in each
    backend's own ``decide()``).

    Args:
        sentences: the formulas to satisfy together. Must be non-empty —
            an empty problem has no goal to search for.
        size: the domain size ``n``; individuals are ``0 … n-1``. Must be
            ``>= 1`` — an empty domain satisfies no ``∃`` and is never a
            useful search.
        signature: the declared vocabulary. When ``None`` (the default) it
            is inferred from ``sentences`` via
            :meth:`~unicode_fol_kit.fol.signature.Signature.from_formulas`
            — the canonical way to get one, so most callers never need to
            build it by hand.
        all_different: whether every declared CONSTANT must denote a
            pairwise-distinct individual (the unique-names convention some
            encodings rely on). This is a property of the SOLUTION a
            backend is allowed to return, not of ``sentences`` themselves —
            it is deliberately a separate flag rather than baked into the
            sentences as explicit ``≠`` atoms, and it is UNRELATED to
            :func:`~unicode_fol_kit.semantics.model_eval.evaluate`'s own
            ``all_different`` parameter (that one governs whether separately
            quantified EXISTENTIAL VARIABLES must denote distinct
            individuals — a different symbol class, a different convention;
            conflating the two would be exactly the kind of silent semantic
            substitution this kit refuses elsewhere). Defaults to ``False``.

    Raises:
        TypeError: a sentence is not a
            :class:`~unicode_fol_kit.fol.nodes.Node`, ``signature`` is
            neither ``None`` nor a
            :class:`~unicode_fol_kit.fol.signature.Signature`, or
            ``all_different`` is not a ``bool``.
        ValueError: ``sentences`` is empty, or ``size < 1``.
    """

    sentences: Tuple[Node, ...]
    size: int
    signature: Optional[Signature] = None
    all_different: bool = False

    def __post_init__(self):
        object.__setattr__(self, "sentences", tuple(self.sentences))
        if not self.sentences:
            raise ValueError(
                "FiniteDomainProblem: sentences must be non-empty — there is "
                "no goal to search for otherwise."
            )
        for s in self.sentences:
            if not isinstance(s, Node):
                raise TypeError(
                    f"FiniteDomainProblem: every sentence must be a Node, got "
                    f"{type(s).__name__}."
                )
        if isinstance(self.size, bool) or not isinstance(self.size, int) or self.size < 1:
            raise ValueError(
                f"FiniteDomainProblem: size must be an int >= 1, got {self.size!r}."
            )
        if self.signature is None:
            object.__setattr__(self, "signature", Signature.from_formulas(self.sentences))
        elif not isinstance(self.signature, Signature):
            raise TypeError(
                f"FiniteDomainProblem: signature must be a Signature or None, "
                f"got {type(self.signature).__name__}."
            )
        if not isinstance(self.all_different, bool):
            raise TypeError(
                f"FiniteDomainProblem: all_different must be a bool, got "
                f"{type(self.all_different).__name__}."
            )


# =============================================================================
# fragment_check — the single gate
# =============================================================================

# The counting-fragment-plus-unsorted-classical-FOL node types both backends
# may encode. Deliberately an ALLOW-list, not a deny-list: a future AST
# addition this module has never seen is refused by default (see
# _GENERIC_REASON below), matching the kit's loud-refusal convention rather
# than silently letting an unrecognised node type through.
_ALLOWED_NODE_TYPES: frozenset = frozenset({
    Variable, Constant, Number,
    Atom, Not, And, Or, Xor, Implies, Iff, Contrast,
    Quantifier, Count, Cardinality,
})

_FUNCTION_REASON = (
    "function symbols: a solver can find a model containing one, but "
    "FiniteStructure interprets predicates and constants only — it has no "
    "slot for a function interpretation — so the model could not be checked "
    "back with verify_model, and this layer does not hand out countermodels "
    "it cannot verify. Adding function interpretations to FiniteStructure "
    "touches serialisation, the evaluator and every consumer of a structure; "
    "it is a separate piece of work, not a detail of this backend"
)


def _family(reason: str, *classes: Type[Node]) -> Dict[Type[Node], str]:
    """Map every class in ``classes`` to the SAME rejection ``reason``.

    A small helper so each family below states its reason exactly once
    rather than repeating the string per node type — a family that grows a
    new node type later needs one new entry in a tuple, not a new copy of
    the prose.
    """
    return {cls: reason for cls in classes}


_SORTED_REASON = (
    "the sorted/many-sorted family needs per-sort subdomains that "
    "FiniteDomainProblem does not carry — a real extension, not a detail, "
    "and out of scope for this backend"
)
_MODAL_REASON = (
    "modal/temporal/epistemic/hybrid operators quantify over POSSIBLE "
    "WORLDS, not domain individuals — no finite-domain reading here; the "
    "modal family already has its own finite-model backend (kripke-enum)"
)
_SECOND_ORDER_REASON = (
    "second-order quantification ranges over relations, not individuals — "
    "no finite-DOMAIN (single-structure) reading"
)
_SUBSTRUCTURAL_REASON = (
    "linear/Lambek connectives track RESOURCE USE (how many times a "
    "formula is consumed), not truth in one structure — no finite-domain "
    "reading; see the dedicated linear/Lambek provers for this fragment"
)
_LAMBDA_REASON = (
    "lambda terms are functions FROM formulas TO formulas — higher-order, "
    "not first-order individuals — no finite-domain reading"
)
_TEAM_REASON = (
    "team-semantic connectives are evaluated against a TEAM (a set of "
    "assignments), not a single structure — no finite-domain reading"
)
_FUZZY_REASON = (
    "Łukasiewicz connectives are many-valued — a finite-domain "
    "countermodel search assumes classical, two-valued truth"
)
_MEASURE_REASON = (
    "Measure denotes a degree on an uninterpreted ORDERED codomain, not a "
    "set to count — nothing for #count/sum to range over"
)
_GENERIC_REASON = (
    "not part of the unsorted-classical-FOL-plus-Count/Cardinality "
    "fragment these backends encode"
)

_REJECTED_NODE_REASONS: Dict[Type[Node], str] = {}
_REJECTED_NODE_REASONS.update(_family(
    _SORTED_REASON,
    SortedQuantifier, SortedConstant, SortedCount, SortedCardinality,
))
_REJECTED_NODE_REASONS.update(_family(
    _MODAL_REASON,
    Box, Diamond, Knows, Believes, Says, Wants,
    Always, Eventually, Next, Until,
    Historically, Once, Previous, Since,
    Obligatory, Permitted, Would, Might,
    Announce, AnnounceDiamond, Nominal, At,
))
_REJECTED_NODE_REASONS.update(_family(_SECOND_ORDER_REASON, SecondOrderQuantifier))
_REJECTED_NODE_REASONS.update(_family(
    _SUBSTRUCTURAL_REASON,
    Tensor, With, OPlus, LinearImplies, OfCourse, One, Top, Zero,
    Product, Under, Over,
))
_REJECTED_NODE_REASONS.update(_family(_LAMBDA_REASON, LambdaVar, Lambda, Application))
_REJECTED_NODE_REASONS.update(_family(_TEAM_REASON, Dependence, SlashedExists))
_REJECTED_NODE_REASONS.update(_family(
    _FUZZY_REASON,
    WeakConjunction, WeakDisjunction, StrongConjunction, StrongDisjunction,
    LukNegation, LukImplication, LukEquivalence,
))
_REJECTED_NODE_REASONS.update(_family(_MEASURE_REASON, Measure))
_REJECTED_NODE_REASONS.update(_family(_FUNCTION_REASON, Function))


def fragment_check(sentences: Iterable[Node]) -> Optional[str]:
    """Return why ``sentences`` cannot be finite-domain-encoded, or ``None``.

    The single gate both :class:`ClingoBackend
    <unicode_fol_kit.atp.clingo_backend.ClingoBackend>` and
    :class:`MinizincBackend
    <unicode_fol_kit.atp.minizinc_backend.MinizincBackend>` consult before
    attempting to ground anything, so an ``UNKNOWN``/``"unsupported"``
    verdict (see :mod:`unicode_fol_kit.atp.protocol`) names the exact same
    offending node type and reason regardless of which solver was asked.
    Walks every sentence with
    :meth:`~unicode_fol_kit.fol.nodes.Node.walk` (pre-order, every
    descendant), so a disallowed node buried under an allowed one — e.g. a
    ``Box`` nested inside an otherwise-plain ``And`` — is still caught; see
    the module docstring's "Fragment boundary" section for the exact
    allow/refuse lists and the reason given for each refused family.

    Args:
        sentences: the formulas to check, e.g. a
            :class:`FiniteDomainProblem`'s ``sentences``.

    Returns:
        ``None`` if every sentence stays inside the encodable fragment;
        otherwise a message of the form ``"<NodeType> is not encodable:
        <reason>"`` naming the FIRST offending node type encountered (in
        sentence order, then pre-order within a sentence).

    Raises:
        TypeError: a member of ``sentences`` is not a
            :class:`~unicode_fol_kit.fol.nodes.Node`.
    """
    for sentence in sentences:
        if not isinstance(sentence, Node):
            raise TypeError(
                f"fragment_check: every sentence must be a Node, got "
                f"{type(sentence).__name__}."
            )
        for node in sentence.walk():
            node_type = type(node)
            if node_type in _ALLOWED_NODE_TYPES:
                continue
            reason = _REJECTED_NODE_REASONS.get(node_type, _GENERIC_REASON)
            return f"{node_type.__name__} is not encodable: {reason}"
    return None


# =============================================================================
# structure_from_solution — the shared reconstruction
# =============================================================================

def structure_from_solution(
    signature: Signature,
    atoms: Iterable[Tuple[str, Sequence[int]]],
    size: int,
    *,
    all_different: bool = False,
) -> FiniteStructure:
    """Rebuild a :class:`~unicode_fol_kit.semantics.structures.FiniteStructure`
    from a solver's true ground atoms.

    ``atoms`` is the one solver-agnostic shape both backends must translate
    their native output INTO before calling this function: pairs of
    ``(symbol_name, args)`` where ``args`` is a tuple of individual
    indices in ``0 … size-1``. A backend's OWN auxiliary/helper atoms (a
    ``dom/1`` domain fact, an aggregate's internal bookkeeping atom, …) must
    already be filtered out by the caller — every symbol name reaching this
    function is checked against ``signature`` and an unrecognised one is
    refused (see Raises), so a leaked helper atom surfaces as a loud error
    here rather than silently becoming a phantom predicate.

    Three namespaces, told apart by which section of ``signature`` the
    symbol name is declared in:

    * a PREDICATE ``p`` of arity ``k`` — each atom supplies one ``k``-tuple
      of the relation's extension. A predicate with zero true atoms is a
      perfectly valid (empty) extension, not an error — a countermodel is
      free to make a relation entirely false.
    * a FUNCTION ``f`` of arity ``k`` — the standard finite-model-finding
      "total relation" reading: each atom is a ``(k+1)``-tuple, the first
      ``k`` entries the arguments and the last the result. This is where
      the "functionality constraint (exactly one value per argument
      tuple)" the design calls for is actually enforced — see Raises — so
      neither backend has to re-derive that check from its own solver
      output.
    * a CONSTANT ``c`` — a 1-tuple naming the single individual it denotes;
      the arity-0 special case of the same "exactly one value" reading.

    Every declared predicate/function/constant gets an extension entry even
    when no atom mentions it (an all-false relation still needs a ``set()``
    in ``extensions``, or
    :meth:`~unicode_fol_kit.semantics.structures.FiniteStructure.holds`
    would read "no atoms" as "uninterpreted" and raise, rather than as the
    correct answer "false everywhere").

    Args:
        signature: the problem's declared vocabulary (typically
            ``problem.signature`` for some :class:`FiniteDomainProblem`).
        atoms: the solver's true ground atoms, translated into the shared
            ``(name, args)`` shape described above.
        size: the domain size; individuals are named ``"0" … "<size-1>"``.
        all_different: when ``True``, additionally check that every
            declared constant denotes a DISTINCT individual (see
            :class:`FiniteDomainProblem`'s ``all_different``) — a solver
            whose encoding was supposed to enforce this but did not is a
            solver/encoding bug, and this catches it here rather than
            handing back a structure that quietly violates the convention
            it was asked to honour.

    Returns:
        The reconstructed structure: ``domain`` is ``("0", …,
        "<size-1>")``; every predicate AND every function (stored as an
        arity-``(k+1)`` relation) has an extension; every constant is set.

    Raises:
        TypeError: ``signature`` is not a
            :class:`~unicode_fol_kit.fol.signature.Signature`, or an
            atom's individual index is not a plain ``int``.
        ValueError: ``size < 1``; an atom names an individual index outside
            ``0 … size-1``; an atom's arity does not match its symbol's
            declared arity; an atom names a symbol ``signature`` does not
            declare as a predicate, function, or constant; a function or
            constant is given two DIFFERENT results for the same inputs
            (functionality violated); a function is missing a result for
            some input tuple (totality violated); a constant is never
            assigned an individual; or ``all_different=True`` and two
            constants denote the same individual.
    """
    if not isinstance(signature, Signature):
        raise TypeError(
            f"structure_from_solution: signature must be a Signature, got "
            f"{type(signature).__name__}."
        )
    if isinstance(size, bool) or not isinstance(size, int) or size < 1:
        raise ValueError(f"structure_from_solution: size must be an int >= 1, got {size!r}.")

    domain_range = range(size)
    pred_rows: Dict[Tuple[str, int], set] = {}
    func_graph: Dict[str, Dict[Tuple[int, ...], int]] = {}
    const_val: Dict[str, int] = {}

    for name, raw_args in atoms:
        args = tuple(raw_args)
        for a in args:
            if isinstance(a, bool) or not isinstance(a, int):
                raise TypeError(
                    f"structure_from_solution: atom {name}{args} has a "
                    f"non-int individual index {a!r}."
                )
        bad = [a for a in args if a not in domain_range]
        if bad:
            raise ValueError(
                f"structure_from_solution: atom {name}{args} names "
                f"individual index(es) {bad} outside the domain "
                f"0..{size - 1}."
            )
        if name in signature.predicates:
            decl = signature.predicates[name]
            if len(args) != decl.arity:
                raise ValueError(
                    f"structure_from_solution: predicate {name!r} is "
                    f"declared arity {decl.arity}, but the solver returned "
                    f"a {len(args)}-tuple {args}."
                )
            pred_rows.setdefault((name, decl.arity), set()).add(args)
        elif name in signature.functions:
            decl = signature.functions[name]
            expected = decl.arity + 1        # k inputs + 1 result
            if len(args) != expected:
                raise ValueError(
                    f"structure_from_solution: function {name!r} is "
                    f"declared arity {decl.arity}, so its total-relation "
                    f"encoding needs {expected} args (inputs + result), "
                    f"but the solver returned a {len(args)}-tuple {args}."
                )
            inputs, result = args[:-1], args[-1]
            graph = func_graph.setdefault(name, {})
            if inputs in graph and graph[inputs] != result:
                raise ValueError(
                    f"structure_from_solution: functionality violated for "
                    f"{name}{inputs} — both {graph[inputs]} and {result} "
                    f"are claimed as the result (a solver/encoding bug: a "
                    f"function must have EXACTLY one value per argument "
                    f"tuple)."
                )
            graph[inputs] = result
        elif name in signature.constants:
            if len(args) != 1:
                raise ValueError(
                    f"structure_from_solution: constant {name!r} names "
                    f"exactly one individual, but the solver returned a "
                    f"{len(args)}-tuple {args}."
                )
            (val,) = args
            if name in const_val and const_val[name] != val:
                raise ValueError(
                    f"structure_from_solution: functionality violated for "
                    f"constant {name!r} — both {const_val[name]} and {val} "
                    f"are claimed as its denotation."
                )
            const_val[name] = val
        else:
            raise ValueError(
                f"structure_from_solution: the solver returned an atom for "
                f"{name!r}, which the signature does not declare as a "
                f"predicate, function, or constant."
            )

    # Totality: every function symbol needs a result for EVERY input tuple,
    # not just the ones an atom happened to mention — functionality (checked
    # above, one value at most) is only half of "total relation"; this is
    # the other half. Bounded by size ** arity, the same finite domain the
    # search already covers, so this is cheap validation of an
    # already-finite solution, not the grounding this module otherwise
    # deliberately avoids (see the module docstring).
    for name, decl in signature.functions.items():
        graph = func_graph.get(name, {})
        for inputs in itertools.product(domain_range, repeat=decl.arity):
            if inputs not in graph:
                raise ValueError(
                    f"structure_from_solution: totality violated for "
                    f"{name}{inputs} — the total-relation encoding must "
                    f"give it SOME result, but the solver returned none "
                    f"(a solver/encoding bug)."
                )

    for name in signature.constants:
        if name not in const_val:
            raise ValueError(
                f"structure_from_solution: constant {name!r} was never "
                f"assigned an individual by the solver."
            )

    if all_different:
        seen: Dict[int, str] = {}
        for name, val in const_val.items():
            if val in seen:
                raise ValueError(
                    f"structure_from_solution: all_different=True requires "
                    f"every constant to denote a distinct individual, but "
                    f"{name!r} and {seen[val]!r} both denote {val}."
                )
            seen[val] = name

    domain = tuple(str(i) for i in domain_range)
    extensions: Dict[Tuple[str, int], set] = {
        key: {tuple(str(i) for i in row) for row in rows}
        for key, rows in pred_rows.items()
    }
    # Every declared predicate gets an entry even with zero true atoms — see
    # the "empty extension, not uninterpreted" note in the docstring above.
    for name, decl in signature.predicates.items():
        extensions.setdefault((name, decl.arity), set())
    for name, decl in signature.functions.items():
        graph = func_graph.get(name, {})
        extensions[(name, decl.arity + 1)] = {
            tuple(str(i) for i in (*inputs, result))
            for inputs, result in graph.items()
        }
    constants = {name: str(val) for name, val in const_val.items()}

    return FiniteStructure(domain=domain, extensions=extensions, constants=constants)


# =============================================================================
# verify_model — the safety net
# =============================================================================

def verify_model(structure: FiniteStructure, sentences: Iterable[Node]) -> Optional[str]:
    """Re-check ``structure`` against ``sentences`` with the kit's OWN evaluator.

    The §3 safety net: a backend must call this on every reconstructed
    structure before reporting ``REFUTED`` and, if it returns anything but
    ``None``, report ``ERROR``/``"infra"`` instead — never hand back a
    countermodel this function could not confirm. Delegates every sentence,
    whole, to
    :func:`~unicode_fol_kit.semantics.model_eval.evaluate` (re-exported as
    ``evaluate_in_structure``) — the kit's independent, hand-checked
    structural evaluator, so a mistake in a backend's OWN ASP/CP encoder
    cannot also be the thing that validates its output.

    .. warning::
       ``evaluate_in_structure`` now evaluates ``Cardinality`` and
       ``Number`` (as a comparison operand) ARITHMETICALLY — see
       :mod:`~unicode_fol_kit.semantics.model_eval`'s own docstring — so
       the counting fragment this module exists to decide is fully
       re-verified here too, not merely decided. Two gaps remain, at
       different levels: ``Function`` still makes ``evaluate_in_structure``
       raise ``UnsupportedNode`` when a sentence containing one is handed
       to THIS function directly, but such a sentence never reaches here
       via either backend — :func:`fragment_check` refuses ``Function`` BY
       NAME first (see the module docstring's "Fragment boundary"), so this
       is a fact about :func:`verify_model` in isolation, not a live gap in
       either backend. ``Contrast`` genuinely still raises
       ``UnsupportedNode`` here even though :func:`fragment_check` admits
       it into the encodable fragment — a live collision, not a moot one.
       Either way this function reports "could not verify", and the caller
       still MUST treat that as a reason not to report ``REFUTED`` (per
       this module's one rule: never hand back an unverified countermodel).
       Comparing a domain individual with a bare numeral (``∀x (x = 1)``)
       is ALSO reported as "could not verify" — but that is the deliberate
       edge of the counting fragment, not a gap. See the module docstring's
       "Known verification gap" section for the full account of all three.

    Args:
        structure: the candidate countermodel, typically fresh out of
            :func:`structure_from_solution`.
        sentences: the sentences ``structure`` is claimed to satisfy —
            typically a :class:`FiniteDomainProblem`'s ``sentences``.

    Returns:
        ``None`` if every sentence evaluates ``True`` in ``structure``;
        otherwise a message naming the FIRST sentence (in order) that
        either evaluates ``False`` or could not be evaluated at all, and
        why.
    """
    for sentence in sentences:
        try:
            holds = _evaluate_in_structure(sentence, structure)
        except (UninterpretedSymbol, UnsupportedNode, ValueError) as exc:
            return (
                f"could not verify {sentence.to_unicode_str()!r}: the "
                f"independent checker (evaluate_in_structure) could not "
                f"evaluate it — {exc}"
            )
        if not holds:
            return (
                f"{sentence.to_unicode_str()!r} does not hold in the "
                f"reconstructed structure."
            )
    return None
