"""Logical generality analysis — an early-warning signal for over-general
class definitions, computed WITHOUT any molecule database.

Motivation (ChEBI2FOL, NeSy 2026): an LLM translates ChEBI class definitions
to FOL and classification is then model-checking a definition against real
molecule structures. The paper's holdout evaluation found micro-precision of
only 0.0363 at a recall of 0.8836 — the learned formulas match far too much.
Two of the paper's own worked examples (Appendix) show exactly why, and both
are literal enough to serve as this module's calibration cases:

    molecule <=> net_charge_neutral
    organicMolecularEntity <=> ?[A1]: (molecule & c(A1))

The right-hand side of the first is satisfied by ANY neutrally-charged
structure, however tiny; the second by any neutral structure with a single
carbon. A real acyl-CoA has on the order of 50 atoms — if its class
definition is already satisfied by a 3-atom structure, the definition is
under-determined, and this can be SEEN before a single real molecule is
checked. That is the whole point of this module: it never touches a molecule
database, ChemLog, or RDKit. It only asks the kit's own finite model finder
(:mod:`unicode_fol_kit.semantics.modelfinder`) "what is the SMALLEST finite
structure that satisfies this formula", and the kit's own prover chain
(:mod:`unicode_fol_kit.api`) "does this subclass body actually add anything
over its superclass body". Both questions are purely syntactic/semantic
properties of the FORMULA — no corpus required.

Three tools, matching the three questions a definition author should ask:

* :func:`minimal_model_size` / :func:`generality_report` — "how small a
  structure already satisfies this?" A thin, HONEST wrapper around
  :func:`~unicode_fol_kit.semantics.modelfinder.find_model`: that finder
  already searches domain sizes ``1, 2, 3, …`` in ascending order and returns
  the first (hence smallest) satisfying interpretation, so "minimal model
  size" needs no search logic of its own here — just an honest reading of
  what the finder already does, and an honest report of what it does NOT
  prove (see the calibration discipline below).

* :func:`is_vacuous_specialisation` / :func:`strictly_stronger` — "does the
  subclass body actually narrow down the superclass body, or does it
  (possibly after being dressed up differently) mean the same thing?" A
  "specialisation" that is logically equivalent to what it specialises has
  added nothing — exactly the kind of silent redundancy the paper's
  auxiliary-predicate-inheritance mechanism (each helper predicate is
  optimised only in the context of the class that introduces it, then
  inherited by every subclass verbatim) can produce without anyone noticing.

**Calibration discipline (read before using the "underdetermined" verdict).**
A small minimal model size is an INDICATION of under-determination, never a
PROOF: a class can legitimately be satisfiable by a small structure (a
definition that is genuinely about a 2-atom functional group, say). This
module therefore refuses to invent an absolute threshold ("smaller than 5 is
bad") — :func:`generality_report`'s verdict is only ever RELATIVE to an
``expected_min_size`` the CALLER supplies (e.g. from the real ChEBI class's
typical atom count); without one, the report states the fact (the size) and
makes no judgement at all. This mirrors the kit-wide rule that an "unknown"
or "not judged" outcome must never be silently reported as a negative
finding.

**Boundedness (the other honesty axis).** Finite-model search is inherently
bounded here, for two independent reasons documented in
:mod:`unicode_fol_kit.semantics.modelfinder` and inherited verbatim by this
module: (1) the search only goes up to ``max_size`` — a formula whose
smallest model is bigger is reported the same way as a genuinely
unsatisfiable one (``size=None, exhausted=True``); this module does NOT
attempt to disambiguate the two, because doing so would require a
decision procedure this kit does not have (FOL satisfiability is
undecidable). (2) a domain size whose interpretation space exceeds
``max_candidates`` is SKIPPED rather than exhaustively searched — so, in
principle, a skipped smaller size could also have been satisfying, and the
"minimal" size this module reports is only minimal among the SIZES ACTUALLY
SEARCHED. Both are the modelfinder's own pre-existing, tested contract; nothing
here works around or hides them.

**Solver tri-state discipline.** :func:`strictly_stronger` /
:func:`is_vacuous_specialisation` route both entailment directions through
:func:`unicode_fol_kit.api.prove`'s backend chain, which is itself already
tri-state (PROVED / REFUTED / UNKNOWN). This module keeps that third value
alive end to end: an entailment direction the chain could not decide within
its budget is reported as ``None``, and — per the Kleene-logic combination
documented on :class:`StrictlyStrongerResult` — propagates to an honest
``"undecided"`` classification rather than a guessed one, EXCEPT in the one
case where the algebra makes a guess unnecessary: once one conjunct of
"sub |= sup AND NOT sup |= sub" is definitely known to be False, the whole
conjunction is False regardless of the other, undecided, conjunct — that is
not a guess, it is deduction, and reporting it as ``None`` would itself be
the dishonest choice (silently downgrading a proven answer to "unknown").
"""

from dataclasses import dataclass
from typing import Optional, Sequence, Tuple

from ..fol.nodes import Node
from ..fol.signature import Signature
from ..semantics.modelfinder import MAX_CANDIDATES, find_model
from ..semantics.tarski import Structure
from ..atp.protocol import PROVED, REFUTED
from .explain import explain_countermodel

__all__ = [
    "MinimalModelResult", "minimal_model_size",
    "GeneralityReport", "generality_report",
    "StrictlyStrongerResult", "strictly_stronger",
    "VacuousSpecialisationResult", "is_vacuous_specialisation",
    "NO_SMALL_MODEL_FOUND", "REPORTED_ONLY", "UNDERDETERMINED", "MEETS_EXPECTATION",
    "EQUIVALENT", "STRICTLY_STRONGER", "NOT_A_SPECIALISATION", "UNDECIDED",
]

# ---------------------------------------------------------------------------
# generality_report verdict vocabulary — see the module docstring's
# "Calibration discipline" for why there is no absolute-threshold verdict.
# ---------------------------------------------------------------------------

NO_SMALL_MODEL_FOUND = "no_small_model_found"  # no model up to max_size — NOT a claim of unsatisfiability
REPORTED_ONLY = "reported_only"                # a size was found, but no expected_min_size to judge it against
UNDERDETERMINED = "underdetermined"            # size < expected_min_size — an INDICATION, not a proof
MEETS_EXPECTATION = "meets_expectation"        # size >= expected_min_size — no warning raised (not a positive guarantee either)

# ---------------------------------------------------------------------------
# is_vacuous_specialisation classification vocabulary
# ---------------------------------------------------------------------------

EQUIVALENT = "equivalent"                  # sub_body <=> sup_body: the "specialisation" adds nothing
STRICTLY_STRONGER = "strictly_stronger"    # sub_body |= sup_body, sup_body does NOT |= sub_body: a genuine narrowing
NOT_A_SPECIALISATION = "not_a_specialisation"  # sub_body does NOT even entail sup_body — the premise of the question is false
UNDECIDED = "undecided"                    # the backend chain could not settle enough of the two directions


# ---------------------------------------------------------------------------
# minimal_model_size
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class MinimalModelResult:
    """Outcome of :func:`minimal_model_size`.

    ``size`` is the domain size of the smallest satisfying structure found,
    or ``None`` iff no satisfying structure was found up to ``max_size_tried``
    (``exhausted`` is then ``True`` — read as "no small satisfying structure
    found", NEVER as "unsatisfiable": see the module docstring's
    "Boundedness" section for the two independent reasons a genuinely
    satisfiable formula can still come back this way). ``model`` is the
    witness structure itself (a
    :class:`~unicode_fol_kit.semantics.tarski.Structure`) when one was found,
    else ``None``.
    """

    size: Optional[int]
    model: Optional[Structure]
    exhausted: bool
    max_size_tried: int

    def to_dict(self) -> dict:
        return {
            "size": self.size,
            "model": ({"kind": "finite_structure", "repr": repr(self.model)}
                       if self.model is not None else None),
            "exhausted": self.exhausted,
            "max_size_tried": self.max_size_tried,
        }


def minimal_model_size(
    formula: Node, *,
    signature: Optional[Signature] = None,
    max_size: int = 6,
    max_candidates: int = MAX_CANDIDATES,
) -> MinimalModelResult:
    """Search for the SMALLEST finite structure satisfying ``formula``.

    This is a thin, honesty-preserving wrapper around
    :func:`unicode_fol_kit.semantics.modelfinder.find_model`: that finder
    already enumerates domain sizes ``1, 2, 3, …, max_size`` in ascending
    order and returns the structure for the FIRST size at which one is found
    — which is, by construction, the smallest size (among those actually
    searched, see below) at which ``formula`` is satisfiable. No separate
    search loop is implemented here; duplicating that logic would risk it
    silently diverging from the finder's own (tested) enumeration order.

    Args:
        formula: the definitional BODY to test (e.g. the right-hand side of
            a ``class <=> body`` definition) — not the whole biconditional,
            which would trivially be satisfiable by choosing the class
            predicate's extension to match whatever the body denotes. Free
            variables are read as universally quantified, matching
            :mod:`~unicode_fol_kit.semantics.modelfinder`'s own convention.
        signature: if given, ``formula`` is validated against it first
            (:meth:`~unicode_fol_kit.fol.signature.Signature.validate`) and a
            formula using any undeclared predicate/function/constant is
            REFUSED with ``ValueError`` before any search runs — a
            generality analysis over a symbol that is not even part of the
            real vocabulary (e.g. a typo'd helper-predicate name) would be
            meaningless, and this kit does not silently search anyway when
            the input itself looks wrong.
        max_size: the largest domain size tried (inclusive). Bigger costs
            more; see ``max_candidates`` for the per-size cutoff.
        max_candidates: forwarded to :func:`~unicode_fol_kit.semantics.modelfinder.find_model`
            — a domain size whose interpretation space would exceed this is
            SKIPPED rather than exhaustively enumerated. This means the
            "minimal" size reported here is minimal among the sizes that
            were actually searched, not provably minimal overall — see the
            module docstring's "Boundedness" section. Formulas built only
            from unary predicates and 0-ary facts (the paper's own worked
            examples, and this module's own tests) stay far under the
            default budget for every ``max_size`` this module defaults to;
            a formula with several binary predicates can hit the skip much
            sooner, since a binary predicate's interpretation space grows as
            ``2**(k**2)``.

    Returns:
        A :class:`MinimalModelResult`. Any exception the underlying finder
        or evaluator raises for an out-of-fragment node (e.g. a modal or
        fuzzy operator :func:`~unicode_fol_kit.semantics.tarski.satisfies`
        has no rule for) propagates UNCHANGED — this module adds no
        swallowing of its own, per the kit's loud-refusal convention.
    """
    if signature is not None:
        violations = signature.validate(formula)
        if violations:
            extra = f" (and {len(violations) - 1} more)" if len(violations) > 1 else ""
            raise ValueError(
                "generality.minimal_model_size: formula uses vocabulary outside "
                f"the given signature -- {violations[0]}{extra}. Fix the formula "
                "or the signature before searching for a model: a generality "
                "analysis over an undeclared symbol would be meaningless."
            )

    model = find_model([formula], max_size=max_size, max_candidates=max_candidates)
    if model is None:
        return MinimalModelResult(size=None, model=None, exhausted=True,
                                  max_size_tried=max_size)
    return MinimalModelResult(size=len(model.domain), model=model, exhausted=False,
                              max_size_tried=max_size)


def _describe_model(model: Structure) -> str:
    """A short, deterministic English rendering of a witness structure.

    Delegates to :func:`unicode_fol_kit.eval.explain.explain_countermodel`,
    which already renders an arbitrary
    :class:`~unicode_fol_kit.semantics.tarski.Structure` as a few plain
    sentences (domain, constants, every predicate's extension) — the
    rendering logic is identical whether the structure is framed as a
    countermodel of a failed entailment (its original purpose) or, as here,
    as a minimal SATISFYING witness; reimplementing that formatting here
    would just duplicate already-tested code for no behavioural difference.
    """
    return explain_countermodel(model)


# ---------------------------------------------------------------------------
# generality_report
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class GeneralityReport:
    """Outcome of :func:`generality_report`.

    ``verdict`` is one of the module's four verdict constants
    (:data:`NO_SMALL_MODEL_FOUND`, :data:`REPORTED_ONLY`,
    :data:`UNDERDETERMINED`, :data:`MEETS_EXPECTATION`) — see the module
    docstring's "Calibration discipline" for why :data:`UNDERDETERMINED` is
    only ever reached RELATIVE to a caller-supplied ``expected_min_size``,
    never from an absolute size alone. ``narrative`` is the same judgement
    spelled out as one or two plain-English sentences, including the
    relevant caveat every time (never a bare verdict word with no context).
    """

    name: str
    formula: Node
    minimal_model: MinimalModelResult
    expected_min_size: Optional[int]
    verdict: str
    narrative: str
    witness_description: Optional[str]

    def to_dict(self) -> dict:
        return {
            "name": self.name,
            "formula": self.formula.to_dict(),
            "minimal_model": self.minimal_model.to_dict(),
            "expected_min_size": self.expected_min_size,
            "verdict": self.verdict,
            "narrative": self.narrative,
            "witness_description": self.witness_description,
        }


def generality_report(
    name: str, formula: Node, *,
    expected_min_size: Optional[int] = None,
    signature: Optional[Signature] = None,
    max_size: int = 6,
    max_candidates: int = MAX_CANDIDATES,
) -> GeneralityReport:
    """Report on how easily ``formula`` (a class's definitional body) is
    satisfied, optionally judged against ``expected_min_size``.

    Args:
        name: a label for the class this ``formula`` defines (e.g.
            ``"acylCoA"``) — carried through purely for a readable report,
            never inspected.
        formula: as in :func:`minimal_model_size`.
        expected_min_size: the caller's own expectation of how large a
            REAL instance of this class must be (e.g. the typical atom
            count of the real ChEBI class) — the one number this module
            will not invent for you (see the module docstring). Omitted
            (``None``) means: report the fact, make no judgement.
        signature / max_size / max_candidates: forwarded to
            :func:`minimal_model_size` verbatim.

    Returns:
        A :class:`GeneralityReport`. Every verdict branch names its own
        caveat in ``narrative`` — this module never emits a bare "bad" or
        "good" without repeating why that is not a proof either way.
    """
    minimal = minimal_model_size(formula, signature=signature, max_size=max_size,
                                 max_candidates=max_candidates)
    witness = _describe_model(minimal.model) if minimal.model is not None else None

    if minimal.size is None:
        verdict = NO_SMALL_MODEL_FOUND
        narrative = (
            f"No structure of size <= {max_size} satisfies this definition. This "
            "is honestly UNKNOWN territory, not a finding of overgenerality (if "
            "anything the opposite direction) and not a proof of "
            "unsatisfiability either -- FOL satisfiability is undecidable, and "
            "the search is bounded by max_size and max_candidates (see "
            "minimal_model_size's docstring)."
        )
    elif expected_min_size is None:
        verdict = REPORTED_ONLY
        narrative = (
            f"The smallest structure satisfying '{name}' found within the "
            f"search bound has {minimal.size} individual(s). No "
            "expected_min_size was supplied, so no generality judgement is "
            "made -- a bare 'small is bad' threshold is deliberately not "
            "built into this module (see its docstring)."
        )
    elif minimal.size < expected_min_size:
        verdict = UNDERDETERMINED
        narrative = (
            f"The smallest structure satisfying '{name}' has {minimal.size} "
            f"individual(s), below the expected minimum of {expected_min_size}. "
            "This is an INDICATION of possible under-determination (a "
            "structure this small can hardly represent the intended real-world "
            "instances) -- NOT a proof: a class can legitimately be satisfiable "
            "by a small structure, and this module has no way to distinguish "
            "that from a genuinely too-permissive definition on its own."
        )
    else:
        verdict = MEETS_EXPECTATION
        narrative = (
            f"The smallest structure satisfying '{name}' has {minimal.size} "
            f"individual(s), at or above the expected minimum of "
            f"{expected_min_size}. No generality warning is raised here -- "
            "this does not positively CONFIRM the definition is correctly "
            "restrictive either; it only means this particular early-warning "
            "check found nothing to flag."
        )

    return GeneralityReport(
        name=name, formula=formula, minimal_model=minimal,
        expected_min_size=expected_min_size, verdict=verdict,
        narrative=narrative, witness_description=witness,
    )


# ---------------------------------------------------------------------------
# strictly_stronger / is_vacuous_specialisation
# ---------------------------------------------------------------------------

def _entails(
    premise: Node, conclusion: Node, *,
    timeout: int, backends: Optional[Sequence[str]],
) -> Tuple[Optional[bool], Optional[dict], Optional[str]]:
    """Tri-state answer to "does ``premise`` entail ``conclusion``?"

    Routes through :func:`unicode_fol_kit.api.prove` (imported lazily —
    ``api`` itself imports from this package at module scope elsewhere in
    the kit, so importing it at THIS module's top level would risk a
    circular import the moment something wires this module into
    ``unicode_fol_kit.eval``'s own ``__init__``; every other entry point in
    this file that needs ``api`` imports it the same way, immediately before
    use). Returns ``(entails, countermodel, backend)``:

    * ``(True, None, name)``  — the chain PROVED it; ``name`` is the
      backend that closed it.
    * ``(False, cm, name)``   — the chain REFUTED it; ``cm`` is the
      Verdict-layer countermodel witness dict (same shape as
      ``Verdict.countermodel`` / ``CountermodelResult.model``).
    * ``(None, None, name)``  — neither: the chain's final UNKNOWN verdict
      (``name`` is ``"chain"`` unless a single backend was requested via
      ``backends``) — an honest "could not decide within budget", never
      silently read as either PROVED or REFUTED.
    """
    from .. import api  # lazy: see the docstring above for why

    kwargs = {} if backends is None else {"backends": list(backends)}
    verdict = api.prove(conclusion, [premise], timeout=timeout, **kwargs)
    if verdict.status == PROVED:
        return True, None, verdict.backend
    if verdict.status == REFUTED:
        return False, verdict.countermodel, verdict.backend
    return None, None, verdict.backend


def _kleene_and(a: Optional[bool], b: Optional[bool]) -> Optional[bool]:
    """Three-valued (Kleene strong) conjunction: ``False`` short-circuits
    even when the OTHER operand is ``None`` (unknown) — this is the one
    place :class:`StrictlyStrongerResult` legitimately reports a definite
    answer despite one entailment direction being undecided; see the module
    docstring's "Solver tri-state discipline"."""
    if a is False or b is False:
        return False
    if a is True and b is True:
        return True
    return None


@dataclass(frozen=True)
class StrictlyStrongerResult:
    """Tri-state answer to ``sub_body |= sup_body  AND  NOT sup_body |= sub_body``.

    ``forward`` / ``backward`` are the two entailment directions
    (``sub_body |= sup_body`` and ``sup_body |= sub_body`` respectively),
    each ``True`` (PROVED) / ``False`` (REFUTED, with a witness) / ``None``
    (the backend chain could not decide within ``timeout``) — see
    :func:`unicode_fol_kit.api.prove`'s own tri-state contract, which this
    is a direct read-out of.

    ``stronger`` combines them via :func:`_kleene_and` applied to
    ``(forward, not backward)`` — see the module docstring's "Solver
    tri-state discipline" for why this can be a definite ``False`` even when
    ``forward`` itself is ``None`` (once ``backward`` is PROVED ``True``,
    ``NOT backward`` is definitely ``False``, and ``anything AND False`` is
    ``False`` regardless of the unknown operand — a deduction, not a guess).

    ``countermodel`` witnesses ``backward is False`` (a structure where
    ``sup_body`` holds but ``sub_body`` does not — the genuine-narrowing
    witness); ``forward_countermodel`` witnesses ``forward is False`` (a
    structure where ``sub_body`` holds but ``sup_body`` does not — meaning
    ``sub_body`` was never even a specialisation of ``sup_body`` to begin
    with). Each is populated only when its corresponding direction was
    actually REFUTED, ``None`` otherwise — never a guessed placeholder.
    """

    stronger: Optional[bool]
    forward: Optional[bool]
    backward: Optional[bool]
    forward_backend: Optional[str]
    backward_backend: Optional[str]
    countermodel: Optional[dict] = None
    forward_countermodel: Optional[dict] = None

    def to_dict(self) -> dict:
        return {
            "stronger": self.stronger,
            "forward": self.forward,
            "backward": self.backward,
            "forward_backend": self.forward_backend,
            "backward_backend": self.backward_backend,
            "countermodel": self.countermodel,
            "forward_countermodel": self.forward_countermodel,
        }


def strictly_stronger(
    sub_body: Node, sup_body: Node, *,
    timeout: int = 10000,
    backends: Optional[Sequence[str]] = None,
) -> StrictlyStrongerResult:
    """Decide whether ``sub_body`` is a genuine (non-vacuous) logical
    specialisation of ``sup_body``: ``sub_body |= sup_body`` AND
    ``sup_body`` does NOT ``|= sub_body``, each direction decided through
    :func:`unicode_fol_kit.api.prove`'s backend chain.

    Args:
        sub_body / sup_body: the two definitional bodies to compare (e.g. a
            subclass's and its superclass's ``<=>`` right-hand sides).
        timeout: forwarded to ``api.prove`` for EACH of the two entailment
            checks (so the total wall-clock budget is up to ``2 * timeout``).
        backends: forwarded to ``api.prove`` verbatim; ``None`` (the
            default) uses the kit's full default chain for the detected
            logic. Restricting this to a single, deliberately weak backend
            (e.g. ``["z3"]`` with a tiny ``timeout``) is how a caller can
            deliberately force the honest ``None``/undecided branch — see
            ``tests/test_generality.py`` for exactly that use.

    Returns:
        A :class:`StrictlyStrongerResult` — see its docstring for the
        Kleene-logic combination behind ``.stronger``.
    """
    fwd, fwd_cm, fwd_backend = _entails(sub_body, sup_body, timeout=timeout,
                                        backends=backends)
    bwd, bwd_cm, bwd_backend = _entails(sup_body, sub_body, timeout=timeout,
                                        backends=backends)
    not_bwd = {True: False, False: True, None: None}[bwd]
    stronger = _kleene_and(fwd, not_bwd)
    return StrictlyStrongerResult(
        stronger=stronger, forward=fwd, backward=bwd,
        forward_backend=fwd_backend, backward_backend=bwd_backend,
        countermodel=bwd_cm if bwd is False else None,
        forward_countermodel=fwd_cm if fwd is False else None,
    )


@dataclass(frozen=True)
class VacuousSpecialisationResult:
    """Outcome of :func:`is_vacuous_specialisation`.

    ``classification`` is one of :data:`EQUIVALENT` (the "specialisation"
    means the same thing as what it specialises — vacuous), :data:`STRICTLY_STRONGER`
    (a genuine, machine-checked narrowing), :data:`NOT_A_SPECIALISATION`
    (``sub_body`` does not even entail ``sup_body`` — the premise that this
    IS a subclass/superclass pair is itself false), or :data:`UNDECIDED`
    (the backend chain could not settle enough of the two directions to
    place this in one of the other three — see ``detail`` for exactly what
    WAS decided; in particular, a caller that only cares whether ``sub_body``
    genuinely narrows ``sup_body`` should read ``detail.stronger`` directly
    rather than only this coarser label, since ``detail.stronger`` can be a
    definite ``False`` in one edge case where this classification still
    says :data:`UNDECIDED` — see :class:`StrictlyStrongerResult`).
    """

    classification: str
    detail: StrictlyStrongerResult

    def to_dict(self) -> dict:
        return {"classification": self.classification, "detail": self.detail.to_dict()}


def is_vacuous_specialisation(
    sub_body: Node, sup_body: Node, *,
    timeout: int = 10000,
    backends: Optional[Sequence[str]] = None,
) -> VacuousSpecialisationResult:
    """Is ``sub_body`` (a subclass's definitional body) a VACUOUS
    specialisation of ``sup_body`` (its superclass's) — i.e. logically
    EQUIVALENT to it, so the "specialisation" adds nothing?

    Built directly on :func:`strictly_stronger` (see its docstring for the
    two entailment directions this classification is derived from):

    * both directions PROVED           -> :data:`EQUIVALENT`
    * forward PROVED, backward REFUTED -> :data:`STRICTLY_STRONGER`
    * forward REFUTED                  -> :data:`NOT_A_SPECIALISATION`
    * anything else                    -> :data:`UNDECIDED`

    Args:
        sub_body / sup_body / timeout / backends: as in
            :func:`strictly_stronger`.

    Returns:
        A :class:`VacuousSpecialisationResult`.
    """
    detail = strictly_stronger(sub_body, sup_body, timeout=timeout, backends=backends)
    if detail.forward is True and detail.backward is True:
        classification = EQUIVALENT
    elif detail.forward is True and detail.backward is False:
        classification = STRICTLY_STRONGER
    elif detail.forward is False:
        classification = NOT_A_SPECIALISATION
    else:
        classification = UNDECIDED
    return VacuousSpecialisationResult(classification=classification, detail=detail)
