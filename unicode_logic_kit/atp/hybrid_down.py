"""The ↓ binder's "route B" combinator: down_is_valid + KripkeEnumBackend (N1).

``fol.modal_translation.down_is_valid`` and ``atp.kripke_enum.KripkeEnumBackend``
are each already a complete, independently-correct decision route on their own
half of the verdict space for full hybrid logic H(@,↓):

* ``down_is_valid`` (the standard translation + a direct Z3 ``Solver()`` call)
  can PROVE validity (Z3 ``unsat`` of the negated goal) but, by design, never
  claims REFUTED — see its own docstring for why that is a deliberate
  completeness sacrifice, not a soundness one.
* ``KripkeEnumBackend`` (bounded finite-Kripke-model enumeration) can REFUTE
  validity with a concrete, ``satisfies_modal``-verified countermodel, but
  exhausting its search space never proves anything (H(@,↓) — indeed modal
  logic generally — has no small-model property bounding a countermodel to
  ``max_worlds`` worlds).

Together they cover exactly the two halves of what H(@,↓) validity's
undecidability still leaves DECIDABLE-in-the-relevant-direction: co-r.e.
(refutable, via search) and — for the instances Z3 actually closes —
provable (via the meaning-preserving standard translation, Areces/
Blackburn/Marx 1999). Neither route alone can decide the fragment; running
BOTH and reporting whichever one succeeds is the honest, maximal answer this
kit can give in one call, and it is exactly what
``docs/guide/hybrid.md``'s existing tableau-vs-Z3 pattern for H(@) already
models for the decidable fragment. See ``fol._hybrid_nodes``' module
docstring for the three-route architecture this module's function is the
"route B" entry point for (route A is ``semantics.kripke.satisfies_modal``
on a model the caller already has).

This is a thin combinator over two already-complete, already-tested routes:
no new semantic rule is added here, and no ``Verdict`` this module returns
carries a status either underlying route would not have produced on its own.
"""

from typing import Dict, Optional

from ..fol.nodes import Node
from ..fol.modal_translation import down_is_valid
from .kripke_enum import KripkeEnumBackend
from .protocol import PROVED, REFUTED, UNKNOWN, Verdict

__all__ = ["down_decide"]


def down_decide(formula: Node, frame: str = "K", timeout: int = 10000,
                *, systems: Optional[Dict[str, str]] = None,
                max_worlds: int = 3, max_atoms: Optional[int] = None,
                max_models: int = 200000) -> Verdict:
    """Decide a hybrid-modal ``formula`` (H(@,↓), ``Down``/↓ included) over ``frame``.

    Tries :func:`~unicode_logic_kit.fol.modal_translation.down_is_valid` first
    (fast: one Z3 call on a small translated formula). If it returns
    ``PROVED``, that Verdict is returned as-is. Otherwise — ``UNKNOWN`` from
    ``down_is_valid``, which NEVER claims ``REFUTED`` on its own — this falls
    back to :class:`~unicode_logic_kit.atp.kripke_enum.KripkeEnumBackend`'s
    bounded finite-model search for an actual countermodel:

    * a countermodel found        → ``REFUTED``, carrying that model (already
      independently confirmed by ``satisfies_modal`` — see
      :func:`~unicode_logic_kit.atp.kripke_enum.modal_enum_search`'s own
      soundness argument — this function performs no re-verification of its
      own beyond calling that route);
    * the search space exhausted, or its budget ran out, or the formula falls
      outside the propositional/ground modal fragment ``satisfies_modal``
      understands → ``UNKNOWN``, with BOTH routes' ``detail`` text combined
      (so a caller can see whether Z3 timed out / found nothing to prove, and
      separately why the bounded search did not find a countermodel either).

    This never returns ``REFUTED`` for a formula ``down_is_valid`` alone
    reported ``PROVED`` for (only one of the two branches ever runs — see
    above), and it never returns ``PROVED`` from anywhere but
    ``down_is_valid`` (:class:`KripkeEnumBackend` is refutation-only and never
    reports ``PROVED`` either).

    Args:
        formula: the hybrid-modal formula (with or without ``Down``/↓ — a
            plain H(@) formula is handled identically, just more
            conservatively on the PROVED side than
            :func:`~unicode_logic_kit.fol.modal_translation.hybrid_is_valid`
            would be for that decidable fragment).
        frame: the alethic frame name, shared by both routes (``down_is_valid``
            for the frame axioms, ``KripkeEnumBackend`` for the relation
            conditions it enumerates over — see :mod:`unicode_logic_kit.fol.frames`).
        timeout: milliseconds, the limit of the whole call. ``down_is_valid``'s
            Z3 call runs under it, and the bounded search that follows is
            given what is left of it (at least one millisecond), ending at a
            candidate model with ``reason="timeout"`` when that runs out — on
            top of its own budget, ``max_worlds``/``max_atoms``/``max_models``,
            below.
        systems, max_worlds, max_atoms, max_models: forwarded verbatim to
            :class:`KripkeEnumBackend`'s ``decide`` (equivalently,
            :func:`~unicode_logic_kit.atp.kripke_enum.modal_enum_search`) — see
            their docstrings.
    """
    proved = down_is_valid(formula, frame=frame, timeout=timeout)
    if proved.status == PROVED:
        return proved

    enum_options = {"frame": frame, "max_worlds": max_worlds,
                    "max_atoms": max_atoms, "max_models": max_models}
    if systems is not None:
        enum_options["systems"] = systems
    left = max(1, int(timeout - proved.wall_time * 1000))
    enum_verdict = KripkeEnumBackend().decide(formula, timeout=left, **enum_options)

    if enum_verdict.status == REFUTED:
        return Verdict(
            REFUTED, "down_decide", logic="hybrid",
            wall_time=proved.wall_time + enum_verdict.wall_time,
            countermodel=enum_verdict.countermodel,
            detail=(f"down_is_valid: {proved.reason} ({proved.detail}); "
                    f"kripke-enum: {enum_verdict.detail}"),
        )
    return Verdict(
        UNKNOWN, "down_decide", logic="hybrid",
        reason=enum_verdict.reason or proved.reason,
        wall_time=proved.wall_time + enum_verdict.wall_time,
        detail=(f"down_is_valid: {proved.reason} ({proved.detail}); "
                f"kripke-enum: {enum_verdict.reason} ({enum_verdict.detail})"),
    )
