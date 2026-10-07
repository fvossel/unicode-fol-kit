"""Five per-logic :class:`~unicode_logic_kit.atp.protocol.ProverBackend` adapters.

Each substructural / non-classical logic below already has its own
hand-built decision procedure or bounded search elsewhere in the kit
(:mod:`atp.lj`, :mod:`atp.lambek`, :mod:`atp.linear`,
:mod:`semantics.relevant`, :mod:`fol.modal_translation`). This module wraps
each one in the uniform :class:`~unicode_logic_kit.atp.protocol.Verdict`
contract WITHOUT pretending the five share one shape — they do not, so each
adapter is reasoned about on its own terms (what a ``True``/``False``/
``None`` from the underlying routine actually PROVES, versus where it is
merely "nothing found within the bound") rather than registered
mechanically off one template:

* :class:`IntBackend` (``logic="intuitionistic"``) — Dyckhoff's G4ip via
  :func:`~unicode_logic_kit.atp.lj.int_prove`, a genuine terminating decision
  procedure on the propositional fragment. REFUTED carries a best-effort
  Kripke witness from
  :func:`~unicode_logic_kit.semantics.intuitionistic.int_countermodel`.
* :class:`LambekBackend` (``logic="lambek"``) — the Lambek calculus L via
  :func:`~unicode_logic_kit.atp.lambek.lambek_derivable`. ``premises`` is the
  LITERAL ORDERED antecedent (word order is the entire point of L), so the
  shared :func:`~unicode_logic_kit.atp.protocol._implication` And-fold is
  never used here — L has no exchange/weakening to make a conjunction
  interchangeable with its conjuncts in the first place.
* :class:`IllBackend` (``logic="ill"``) — intuitionistic linear logic via
  :func:`~unicode_logic_kit.atp.linear.ill_derivable`: a complete decision
  procedure on the ``!``-free fragment, a depth/step-bounded search once
  ``!`` occurs (see :func:`~unicode_logic_kit.atp.linear._has_bang`).
* :class:`RelevantBackend` (``logic="relevant"``) — the relevant logic B via
  :func:`~unicode_logic_kit.semantics.relevant.rel_countermodel`. NEVER
  PROVED: ``rel_valid``/``rel_countermodel`` are sound but INCOMPLETE (a
  bounded Routley-Meyer search), so "no countermodel found" is honestly
  UNKNOWN(bound_hit). A genuine PROVED route needs a real Isabelle proof
  (:mod:`hol.isabelle_relevant`'s ``to_isabelle_relevant``/``battery_proof``
  driven as a subprocess) and is an explicit out-of-scope follow-up.
* :class:`HybridBackend` (``logic="hybrid"``) — hybrid modal logic H(@) via
  the standard translation (:mod:`fol.modal_translation`) into classical
  FOL, closed under the frame axioms and decided by a per-call tracked Z3
  ``Solver()`` (:func:`~unicode_logic_kit.atp.protocol._z3_track_and_check`,
  the same routine :class:`~unicode_logic_kit.atp.protocol.Z3Backend` uses) —
  deliberately NOT
  :func:`~unicode_logic_kit.fol.modal_translation.hybrid_is_valid` (nor the
  :func:`~unicode_logic_kit.atp.z3_models.is_valid` underneath it), whose bare
  bool collapses a genuine countermodel (SAT) and a solver timeout/unknown
  into the same ``False``.

Routing: :func:`unicode_logic_kit.api.prove`'s ``logic="auto"`` detects
``"lambek"`` / ``"ill"`` / ``"hybrid"`` from an unambiguous syntactic
marker — each is the sole occupant of its own parser mode's node types
(Product/Under/Over; the ``linear`` mode's Tensor/With/OPlus/LinearImplies/
OfCourse/One/Top/Zero; Nominal/At). Intuitionistic and relevant logic reuse
the PLAIN classical propositional AST with no syntactic marker of their
own, so ``logic=`` must always be given explicitly for those two —
auto-detection never guesses between a "classical", "intuitionistic" and
"relevant" reading of the same formula.
"""

import time
from typing import Optional, Sequence

from .._deadline import instant as _instant, run_until as _run_until
from ..fol.nodes import Node
from ._substructural_input import ILL, LAMBEK, Calculus, unreadable_reason
from .protocol import (
    ProverBackend, Verdict, PROVED, REFUTED, UNKNOWN,
    _timed, _implication, _z3_track_and_check, _z3_model_assignment,
)

__all__ = [
    "IntBackend", "LambekBackend", "IllBackend", "RelevantBackend", "HybridBackend",
]


def _unreadable_refusal(logic: str, calculus: Calculus, formula: Node,
                        premises: Sequence[Node]) -> Optional[str]:
    """Why a propositional substructural calculus cannot read this input, or ``None``.

    Intuitionistic linear logic and the Lambek calculus read the connectives they have rules
    for (``calculus.glyphs``) and atoms: no individuals, no sorts, no quantifiers, no counting,
    no identity, and no connective of another logic. An atom over terms is one category (a
    sound reading, argued in ``atp/_substructural_input.py``); any other node read as one more
    opaque category would make a derivability verdict about a DIFFERENT formula
    (``∀x P(x)`` does not derive ``P(alpha)`` there, and it does in every first-order
    reading; ``And(A, B)`` does not derive ``A``, and it does classically), so the node is
    refused by name instead and the text says what to do.
    """
    return unreadable_reason([*premises, formula], logic, calculus)


# ---------------------------------------------------------------------------
# Witness serializers — IntKripkeModel / RelevantModel are not JSON-native.
# ---------------------------------------------------------------------------

def _int_kripke_witness_to_dict(model, world: int) -> dict:
    """JSON-able witness for an
    :class:`~unicode_logic_kit.semantics.intuitionistic.IntKripkeModel`
    countermodel: the up-set order, the monotone valuation, and (for a
    first-order witness, which :class:`IntBackend` never actually reaches —
    see its docstring) the per-world domains.
    """
    out = {
        "kind": "intuitionistic_kripke",
        "world": world,
        "upset": {str(w): sorted(ws) for w, ws in model.upset.items()},
        "valuation": {k: sorted(ws) for k, ws in model.valuation.items()},
    }
    if model.domains is not None:
        out["domains"] = {str(w): sorted(ds) for w, ds in model.domains.items()}
    return out


def _relevant_model_to_dict(model, world: str) -> dict:
    """JSON-able witness for a
    :class:`~unicode_logic_kit.semantics.relevant.RelevantModel` countermodel.

    ``RelevantModel`` is frozen/hashable but not JSON-native (its
    ``star``/``valuation`` are the module's own ``_FrozenMap``); this
    unpacks every field the constructor takes into plain lists/dicts, so
    both ``json.dumps`` and rebuilding a ``RelevantModel`` from the dict
    round-trip cleanly (the differential test exercises exactly that).
    """
    return {
        "kind": "relevant_routley_meyer",
        "world": world,
        "worlds": list(model.worlds),
        "normal": sorted(model.normal),
        "star": {w: model.star[w] for w in model.worlds},
        "R": sorted([list(triple) for triple in model.R]),
        "valuation": {k: sorted(ws) for k, ws in model.valuation.items()},
    }


# ---------------------------------------------------------------------------
# Intuitionistic propositional logic
# ---------------------------------------------------------------------------

class IntBackend(ProverBackend):
    """Propositional intuitionistic logic via Dyckhoff's G4ip (:mod:`atp.lj`).

    ``int_prove`` is a genuine, terminating decision procedure on the
    propositional fragment (see its own docstring): PROVED and REFUTED are
    both definitive. Quantified input is out of scope for G4ip (propositional
    only — :func:`~unicode_logic_kit.atp.lj._reject_quantified`); it comes back
    UNKNOWN(unsupported) rather than raising, so a batch run over mixed-arity
    formulas records the gap instead of crashing. A REFUTED verdict's witness
    is a best-effort call to
    :func:`~unicode_logic_kit.semantics.intuitionistic.int_countermodel` on the
    folded goal ``(∧ premises) → formula`` — the REFUTED status itself is
    always definitive (it comes from ``int_prove``, not from this search),
    but the witness search is NOT: ``int_countermodel``'s bounded Kripke
    search at its default ``max_worlds=3`` can still miss a countermodel for
    some genuine non-theorems, since the finite-model-property bound grows
    with the formula (see ``int_valid``'s own docstring for a worked
    example needing 4 worlds). The ``Verdict`` contract permits
    ``countermodel=None`` for exactly this reason, so a bound miss never
    turns into a broken Verdict — only a REFUTED with no witness attached.

    The call's ``timeout`` bounds both searches
    (:func:`~unicode_logic_kit._deadline.run_until`): an ``int_prove`` that has not
    finished is UNKNOWN(timeout), and a witness search that has not finished
    leaves a REFUTED verdict without its witness. An ``int_prove`` that spends its
    step budget (the calculus terminates, but the number of steps is exponential in
    the nesting of implications) is UNKNOWN(bound_hit): a spent budget is a bound,
    not a failure of the backend.
    """

    name = "intuitionistic"
    logics = frozenset({"intuitionistic"})
    external = False

    def available(self) -> bool:
        return True

    def decide(self, formula: Node, premises: Sequence[Node] = (),
               timeout: int = 10000, **options) -> Verdict:
        from .lj import int_prove, _MAX_STEPS
        from ..semantics.intuitionistic import int_countermodel

        premises = list(premises)
        cm_kwargs = {k: options.pop(k) for k in
                     ("max_worlds", "domain_elements", "max_steps") if k in options}
        deadline = _instant(timeout)
        started = time.perf_counter()
        try:
            (finished, proved), elapsed = _timed(
                lambda: _run_until(deadline, lambda: int_prove(premises, formula)))
        except NotImplementedError as exc:
            return Verdict(UNKNOWN, self.name, logic="intuitionistic",
                           reason="unsupported", detail=str(exc))
        except RecursionError:
            # The search recurses once per rule it applies along a branch of the derivation,
            # so the interpreter's recursion limit is a bound of it, next to the step budget:
            # a formula whose nesting is small but whose search is long (nested Peirce
            # formulas) reaches it. Nothing was decided.
            import sys
            return Verdict(UNKNOWN, self.name, logic="intuitionistic", reason="bound_hit",
                           wall_time=time.perf_counter() - started,
                           detail="the proof search recursed deeper than the interpreter's "
                                  f"recursion limit ({sys.getrecursionlimit()}) allows before "
                                  "it decided the sequent: no verdict was reached")
        except RuntimeError as exc:
            # The prover's step counter ran out; any other RuntimeError is a failure.
            if "step budget" not in str(exc):
                raise
            return Verdict(UNKNOWN, self.name, logic="intuitionistic", reason="bound_hit",
                           wall_time=time.perf_counter() - started,
                           detail=f"the prover used up its step budget ({_MAX_STEPS} steps) "
                                  "before it decided the sequent: G4ip terminates, but the "
                                  "number of steps is exponential in the nesting of "
                                  "implications, so no verdict was reached")
        if not finished:
            # ``int_prove`` is a decision procedure, but its cost is exponential in the formula
            return Verdict(UNKNOWN, self.name, logic="intuitionistic", reason="timeout",
                           wall_time=elapsed,
                           detail=f"no verdict within the {timeout} ms limit")
        if proved:
            return Verdict(PROVED, self.name, logic="intuitionistic", wall_time=elapsed)

        # The verdict is settled; the witness is a second, best-effort search that gets what
        # is left of the limit, and a REFUTED answer needs no witness (``countermodel=None``).
        goal = _implication(formula, premises)
        found, cm = _run_until(deadline, lambda: int_countermodel(goal, **cm_kwargs))
        witness = _int_kripke_witness_to_dict(*cm) if found and cm is not None else None
        return Verdict(REFUTED, self.name, logic="intuitionistic", wall_time=elapsed,
                       countermodel=witness)


# ---------------------------------------------------------------------------
# The Lambek calculus L
# ---------------------------------------------------------------------------

class LambekBackend(ProverBackend):
    """The Lambek calculus L via :mod:`atp.lambek` — a complete, terminating
    decision procedure (see that module's docstring: every rule's premises
    are strictly smaller than its conclusion, so ``lambek_prove`` returning
    ``None`` PROVES underivability).

    ``premises`` is read as the sequence's LITERAL ORDER, never folded
    through the shared ``∧``-based :func:`~unicode_logic_kit.atp.protocol._implication`
    helper: L drops exchange along with weakening/contraction, so
    ``A, A\\B ⊢ B`` and ``A\\B, A ⊢ B`` are different sequents with different
    answers — collapsing ``premises`` into an unordered classical conjunction
    would silently erase exactly the distinction this calculus exists to
    draw (the regression battery in ``tests/test_logic_backends.py`` pins
    this pair directly). Every PROVED verdict is re-validated internally by
    :func:`~unicode_logic_kit.atp.lambek.check_lambek_proof` (inside
    ``lambek_prove``), so a search bug can only lose proofs, never invent
    one. A REFUTED verdict's ``countermodel`` is always ``None`` — L has no
    semantic model theory in this kit, only the syntactic decision procedure
    (which is itself exhaustive, so ``None`` from the search IS the
    refutation, not an admission of incompleteness).

    The calculus reads the connectives ``• \\ /`` and atoms; an atom over terms is one
    category. Every other node is refused by name, UNKNOWN(unsupported): a quantifier (sorted
    or not), a counting or cardinality node, a sorted constant, an equality atom and a node of
    another logic (``And``, ``Not``, ``Box``, ...) have no rule in L, and an opaque category
    in their place would answer about another formula. So is an EMPTY premise list: L has no
    sequent with an empty antecedent (Lambek's restriction), so there is nothing to decide,
    and a backend states that as an answer instead of raising.

    The call's ``timeout`` bounds the search (:func:`~unicode_logic_kit._deadline.run_until`):
    the search is exhaustive and terminating, and its cost is exponential in the sequent, so a
    search that has not finished at the limit is UNKNOWN(timeout), never a refutation.
    """

    name = "lambek"
    logics = frozenset({"lambek"})
    external = False

    def available(self) -> bool:
        return True

    def decide(self, formula: Node, premises: Sequence[Node] = (),
               timeout: int = 10000, **options) -> Verdict:
        from .lambek import lambek_prove

        premises = list(premises)
        deadline = _instant(timeout)
        if not premises:
            return Verdict(UNKNOWN, self.name, logic="lambek", reason="unsupported",
                           detail="lambek: decide() needs a nonempty, ORDERED premises "
                                  "sequence — the Lambek calculus has no sequent with an "
                                  "empty antecedent (Lambek's own restriction; see "
                                  "atp.lambek's module docstring), so there is no notion "
                                  "of unconditional validity to fall back to. Give the "
                                  "premises the goal is read from, in order.")
        refusal = _unreadable_refusal("lambek", LAMBEK, formula, premises)
        if refusal is not None:
            return Verdict(UNKNOWN, self.name, logic="lambek", reason="unsupported",
                           detail=refusal)

        try:
            (finished, derivation), elapsed = _timed(
                lambda: _run_until(deadline, lambda: lambek_prove(premises, formula)))
        except NotImplementedError as exc:
            return Verdict(UNKNOWN, self.name, logic="lambek",
                           reason="unsupported", detail=str(exc))
        if not finished:
            # The search is exhaustive and terminating, but its cost is exponential in the sequent.
            return Verdict(UNKNOWN, self.name, logic="lambek", reason="timeout",
                           wall_time=elapsed,
                           detail=f"no verdict within the {timeout} ms limit")
        if derivation is not None:
            return Verdict(PROVED, self.name, logic="lambek", wall_time=elapsed)
        return Verdict(REFUTED, self.name, logic="lambek", wall_time=elapsed,
                       countermodel=None,
                       detail="no cut-free L derivation exists — lambek_prove's "
                              "backward search is exhaustive and terminating "
                              "(every rule strictly shrinks the sequent), so this "
                              "is a genuine syntactic refutation, not a bound")


# ---------------------------------------------------------------------------
# Intuitionistic linear logic (ILL)
# ---------------------------------------------------------------------------

class IllBackend(ProverBackend):
    """Intuitionistic linear logic (ILL) via :mod:`atp.linear`.

    The cut-free backward search is a complete, terminating decision
    procedure on the ``!``-FREE fragment (every rule strictly shrinks the
    sequent there — see that module's docstring), so PROVED/REFUTED are both
    definitive when no ``!`` occurs (checked via
    :func:`~unicode_logic_kit.atp.linear._has_bang` on ``formula`` and every
    premise) AND the depth bound in force is at least the sequent's own
    "safe" bound (``total`` size when ``!``-free, ``2*total + 4`` once ``!``
    occurs — exactly :func:`~unicode_logic_kit.atp.linear.ill_prove`'s own
    default). A caller-supplied ``max_depth`` can shrink the search below
    that safe bound (e.g. to force the bounded path deterministically for
    testing); a ``False`` result from a search truncated below the safe
    bound proves nothing, so it is reported UNKNOWN(bound_hit) too, never
    REFUTED. Once ``!`` occurs, the contraction rule ``!C`` can GROW a
    sequent, so the search is depth/step-bounded there regardless, and a
    ``False`` means only "no derivation found within the bound" — reported
    as UNKNOWN(bound_hit), NEVER REFUTED, exactly matching
    :func:`~unicode_logic_kit.atp.linear.ill_prove`'s own honesty contract.

    The calculus reads the connectives ``⊗ & ⊕ ⊸ ! 𝟙 ⊤ 𝟘`` and atoms; an atom over terms is
    one category. Every other node is refused by name, UNKNOWN(unsupported): a quantifier
    (sorted or not), a counting or cardinality node, a sorted constant, an equality atom and a
    node of another logic (``And``, ``Not``, ``Box``, ...) have no rule in ILL, and an opaque
    category in their place would answer about another formula.

    The call's ``timeout`` bounds the search (:func:`~unicode_logic_kit._deadline.run_until`):
    even the ``!``-free search, a complete decision procedure, is exponential in the sequent,
    so a search that has not finished at the limit is UNKNOWN(timeout), never a refutation.
    """

    name = "ill"
    logics = frozenset({"ill"})
    external = False

    def available(self) -> bool:
        return True

    def decide(self, formula: Node, premises: Sequence[Node] = (),
               timeout: int = 10000, **options) -> Verdict:
        from .linear import ill_derivable, _has_bang, _size

        premises = list(premises)
        deadline = _instant(timeout)
        refusal = _unreadable_refusal("ill", ILL, formula, premises)
        if refusal is not None:
            return Verdict(UNKNOWN, self.name, logic="ill", reason="unsupported",
                           detail=refusal)
        max_depth = options.pop("max_depth", None)
        max_steps = options.pop("max_steps", 200000)
        bang = _has_bang(formula) or any(_has_bang(p) for p in premises)
        # The same "safe" depth ill_prove itself falls back to when max_depth
        # is None (see its docstring) — a smaller CALLER-supplied max_depth
        # is an intentionally truncated search, not a complete one.
        total = sum(_size(p) for p in premises) + _size(formula)
        safe_depth = 2 * total + 4 if bang else total
        bounded = max_depth is not None and max_depth < safe_depth

        try:
            (finished, proved), elapsed = _timed(
                lambda: _run_until(deadline, lambda: ill_derivable(
                    premises, formula, max_depth=max_depth, max_steps=max_steps)))
        except NotImplementedError as exc:
            return Verdict(UNKNOWN, self.name, logic="ill",
                           reason="unsupported", detail=str(exc))
        if not finished:
            # Even the !-free search, a complete decision procedure, is exponential in the sequent.
            return Verdict(UNKNOWN, self.name, logic="ill", reason="timeout",
                           wall_time=elapsed,
                           detail=f"no verdict within the {timeout} ms limit")
        if proved:
            return Verdict(PROVED, self.name, logic="ill", wall_time=elapsed)
        if bang or bounded:
            return Verdict(UNKNOWN, self.name, logic="ill", reason="bound_hit",
                           wall_time=elapsed,
                           detail="no ILL derivation found within max_depth/"
                                  "max_steps — the !-bearing fragment's search "
                                  "is bounded, not complete, and/or max_depth "
                                  "was set below the sequent's own safe bound, "
                                  "so this is honestly unknown, never a refutation")
        return Verdict(REFUTED, self.name, logic="ill", wall_time=elapsed,
                       countermodel=None,
                       detail="the !-free fragment's search is a complete "
                              "decision procedure; no cut-free ILL derivation "
                              "exists (a syntactic refutation — ILL has no "
                              "semantic model theory in this kit)")


# ---------------------------------------------------------------------------
# Relevant logic B
# ---------------------------------------------------------------------------

class RelevantBackend(ProverBackend):
    """The relevant logic B via the bounded Routley-Meyer search in
    :mod:`semantics.relevant`.

    NEVER emits PROVED. :func:`~unicode_logic_kit.semantics.relevant.rel_valid`
    (equivalently, "no countermodel from
    :func:`~unicode_logic_kit.semantics.relevant.rel_countermodel`") is sound
    but INCOMPLETE — an exhaustive search only up to ``max_worlds`` worlds —
    so a clean search is reported UNKNOWN(bound_hit), never treated as a
    proof of validity, exactly as ``rel_valid``'s own docstring insists. A
    REFUTED verdict is always backed by a genuine countermodel: the search
    itself re-verifies it with
    :func:`~unicode_logic_kit.semantics.relevant.rel_satisfies` before
    returning (see ``rel_countermodel``'s docstring), and this backend
    serializes that exact model into ``countermodel`` (see
    :func:`_relevant_model_to_dict`).

    A genuine PROVED route for B needs a real Isabelle proof over EVERY
    Routley-Meyer interpretation (not just small ones) — see
    :mod:`unicode_logic_kit.hol.isabelle_relevant`'s ``to_isabelle_relevant`` /
    ``battery_proof`` — and is an explicit out-of-scope follow-up, not part
    of this backend.

    The call's ``timeout`` bounds the search (:func:`~unicode_logic_kit._deadline.run_until`);
    a search it cut off is UNKNOWN(timeout), not bound_hit.
    """

    name = "relevant"
    logics = frozenset({"relevant"})
    external = False

    def available(self) -> bool:
        return True

    def decide(self, formula: Node, premises: Sequence[Node] = (),
               timeout: int = 10000, **options) -> Verdict:
        from ..semantics.relevant import rel_countermodel

        max_worlds = options.pop("max_worlds", 2)
        goal = _implication(formula, premises)
        try:
            (finished, result), elapsed = _timed(
                lambda: _run_until(_instant(timeout),
                                   lambda: rel_countermodel(goal, max_worlds=max_worlds)))
        except TypeError as exc:
            return Verdict(UNKNOWN, self.name, logic="relevant",
                           reason="unsupported", detail=str(exc))
        if not finished:
            return Verdict(UNKNOWN, self.name, logic="relevant", reason="timeout",
                           wall_time=elapsed,
                           detail=f"no B-countermodel found within the {timeout} ms limit")
        if result is None:
            return Verdict(UNKNOWN, self.name, logic="relevant", reason="bound_hit",
                           wall_time=elapsed,
                           detail=f"no B-countermodel with <= {max_worlds} worlds "
                                  "found — rel_countermodel's search is sound but "
                                  "incomplete, so this is NEVER treated as a proof "
                                  "(see rel_valid's own honesty contract)")
        model, world = result
        return Verdict(REFUTED, self.name, logic="relevant", wall_time=elapsed,
                       countermodel=_relevant_model_to_dict(model, world))


# ---------------------------------------------------------------------------
# Hybrid modal logic H(@)
# ---------------------------------------------------------------------------

class HybridBackend(ProverBackend):
    """Hybrid modal logic H(@) and H(@,↓) via the standard translation + a real Z3 ``Solver``.

    The ↓ binder needs nothing extra here: the standard translation maps
    ``↓x.φ`` to ``φ``'s translation with ``x`` bound to the current world
    variable (the bounded fragment of FOL), which is faithful in both
    directions, so ``unsat`` is a proof and ``sat`` a genuine countermodel of
    the translation, hence of the formula. H(@,↓) is undecidable, so Z3 may
    time out; that stays UNKNOWN. (The narrower
    :func:`~unicode_logic_kit.atp.hybrid_down.down_is_valid` keeps its
    PROVED-only contract.)

    Deliberately does NOT call
    :func:`~unicode_logic_kit.fol.modal_translation.hybrid_is_valid` (nor the
    :func:`~unicode_logic_kit.atp.z3_models.is_valid` it delegates to): both
    return a bare ``bool``, so a genuine countermodel (Z3 SAT) and Z3 giving
    up (UNKNOWN/timeout) are both reported as the same ``False`` — exactly
    the ambiguity this uniform layer exists to remove. This backend instead
    builds the SAME ST-closed goal ``hybrid_is_valid`` builds —
    :func:`~unicode_logic_kit.fol.modal_translation.standard_translation`
    closed under :func:`~unicode_logic_kit.fol.modal_translation.frame_axioms`
    (the frame axioms of every relation the goal mentions, and the membership of
    each sorted constant ``c:S`` in ``S`` at every world) — and decides it with the kit's own tracked per-call
    :func:`~unicode_logic_kit.atp.protocol._z3_track_and_check` (the identical
    routine :class:`~unicode_logic_kit.atp.protocol.Z3Backend` uses for plain
    FOL), so Z3's own ``unsat``/``sat``/``unknown`` map to real
    PROVED / REFUTED(countermodel) / UNKNOWN(timeout|incomplete).

    ``premises`` fold through the shared
    :func:`~unicode_logic_kit.atp.protocol._implication` And/Implies helper at
    the MODAL level first — exactly like
    :class:`~unicode_logic_kit.atp.protocol.ModalTableauBackend` — before
    translation: hybrid logic keeps full classical structure over ``∧``/
    ``→``, so this fold is sound here (unlike the substructural Lambek/ILL
    backends, where it would not be). ``frame`` (default ``"K"``) selects the
    alethic frame class, exactly as it does for ``hybrid_is_valid``; so do the two other
    keywords of that function: ``systems`` (the frame system of the agent-indexed families,
    e.g. ``{"epistemic": "S5"}``, which makes ``Knows(a, P) → P`` valid) and ``temporal_closure``
    (default ``True``: the temporal relation is reflexive and transitive; ``False`` drops
    both, so ``Ⓖφ → φ`` is no longer valid). All three reach
    :func:`~unicode_logic_kit.fol.modal_translation.frame_axioms` and nothing else, and an
    unknown frame system or modal family is UNKNOWN(unsupported), never an exception.
    """

    name = "hybrid"
    logics = frozenset({"hybrid"})
    external = False

    def available(self) -> bool:
        return True

    def decide(self, formula: Node, premises: Sequence[Node] = (),
               timeout: int = 10000, **options) -> Verdict:
        from ..fol.modal_translation import standard_translation, frame_axioms
        from ..fol.nodes import Quantifier, Variable, And, Implies

        frame = options.pop("frame", "K")
        systems = options.pop("systems", None)
        temporal_closure = options.pop("temporal_closure", True)
        goal_modal = _implication(formula, list(premises))
        try:
            translated = standard_translation(goal_modal, world="w")
            closed = Quantifier("∀", Variable("w"), translated)
            hyp = None
            # The axioms of every relation the goal's translation emits (so ``Ⓖφ → φ``
            # and ``Ⓞφ → Ⓟφ`` are decided as ``hybrid_is_valid`` decides them) and the
            # membership of every sorted constant in its sort at every world.
            for axiom in frame_axioms(goal_modal, frame, systems=systems,
                                      temporal_closure=temporal_closure):
                hyp = axiom if hyp is None else And(hyp, axiom)
            st_goal = closed if hyp is None else Implies(hyp, closed)
            z3_formula = st_goal.to_z3()
        except (NotImplementedError, ValueError) as exc:
            return Verdict(UNKNOWN, self.name, logic="hybrid",
                           reason="unsupported", detail=str(exc))

        from z3 import sat, unsat

        (res, solver), elapsed = _timed(
            lambda: _z3_track_and_check(z3_formula, [], timeout))
        if res == unsat:
            return Verdict(PROVED, self.name, logic="hybrid", wall_time=elapsed)
        if res == sat:
            assignment = _z3_model_assignment(solver.model(), 0)
            return Verdict(REFUTED, self.name, logic="hybrid", wall_time=elapsed,
                           countermodel={"kind": "z3_model", "assignment": assignment})
        why = solver.reason_unknown()
        reason = "timeout" if ("timeout" in why or "cancel" in why) else "incomplete"
        return Verdict(UNKNOWN, self.name, logic="hybrid", reason=reason,
                       wall_time=elapsed, detail=why)
