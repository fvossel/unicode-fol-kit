"""Twee as a :class:`~unicode_fol_kit.atp.protocol.ProverBackend` — verified equational proofs.

Wires :mod:`atp.twee_entailment` (the runner + stdout parser) and
:mod:`atp.twee_check` (the independent checker) into one adapter, following
the same shape as :class:`atp.protocol.VampireBackend` and
:class:`atp.cvc5_backend.Cvc5Backend`: ``premises``/``formula`` go in exactly
as given (no folding into one implication — Twee, like Vampire, takes a list
of axioms plus a separate conjecture), a :class:`~atp.protocol.Verdict` comes
out.

The one thing this backend does that no other in the kit does: a Twee
``Theorem`` is NEVER reported ``PROVED`` on Twee's say-so alone. Every parsed
proof is run through :func:`atp.twee_check.check_twee_proof` (does every
rewrite step genuinely follow, and does every restated axiom genuinely match
a given premise?) AND :func:`atp.twee_check.goal_matches_conclusion` (does
the proved goal actually restate the requested conclusion, not some other
formula?) before ``PROVED`` is returned. If either check fails, that is
reported as ``ERROR``/``"infra"`` — never a silent ``PROVED`` — because a
Twee bug or an adversarial/corrupted proof text must never pass through
undetected as an established theorem.
"""

import time
from typing import Sequence

from ..fol.nodes import Node
from .protocol import ERROR, PROVED, REFUTED, UNKNOWN, ProverBackend, Verdict

__all__ = ["TweeBackend"]


def _timed(fn):
    """Run ``fn()`` returning ``(result, seconds)`` — local copy, see cvc5_backend's."""
    start = time.perf_counter()
    result = fn()
    return result, time.perf_counter() - start


class TweeBackend(ProverBackend):
    """Unit equality via Twee, with every ``Theorem`` independently re-checked.

    ``premises``/``formula`` outside Twee's equational fragment (see
    :mod:`atp.twee_entailment`'s module docstring) come back
    UNKNOWN/``"unsupported"`` — Twee decides pure unit equality only, and
    pretending otherwise (e.g. by silently dropping non-equational premises)
    would be unsound. ``CounterSatisfiable`` becomes REFUTED (Twee's
    completion procedure genuinely certifies this — it is not a "gave up"
    signal, see the module docstring of :mod:`atp.twee_entailment`); a
    missing ``RESULT`` line (subprocess timeout, or a Twee-side crash) and
    Twee's own resource-budget ``GaveUp``/other status both come back
    UNKNOWN with the honest ``reason``.
    """

    name = "twee"
    logics = frozenset({"fol"})
    external = True

    def available(self) -> bool:
        from .twee_entailment import twee_available
        return twee_available()

    def decide(self, formula: Node, premises: Sequence[Node] = (),
               timeout: int = 10000, **options) -> Verdict:
        """Decide ``premises ⊨ formula`` via Twee, verifying any Theorem proof independently.

        Args:
            formula: the conclusion — must be a (forall-closed) equation or
                conjunction of equations.
            premises: likewise, each must be equational; passed to Twee as
                separate named axioms (NOT folded into one implication).
            timeout: milliseconds, per the :class:`ProverBackend` contract;
                converted to whole seconds (minimum 1) for
                :func:`atp.twee_entailment.check_entailment_twee_detailed`'s
                subprocess timeout.
            **options: ``use_wsl`` (default ``True``) and ``twee_cmd``
                (default: ``$UFK_TWEE_CMD``, else ``~/.local/bin/twee``) are
                forwarded to the runner; no other options are read.

        Returns:
            PROVED (with ``proof`` = the parsed :class:`~atp.twee_entailment
            .TweeProof`, JSON-serialised via its own ``to_dict()``) only when
            Twee reports ``Theorem`` AND the proof independently verifies
            (see the class docstring); REFUTED on ``CounterSatisfiable``;
            UNKNOWN/``"timeout"`` on a subprocess timeout; ERROR/``"infra"``
            when Twee reports ``Theorem`` but the proof fails independent
            verification (Twee and the checker disagreed — an
            infrastructure-level failure, not "we don't know"); any other
            status is UNKNOWN/``"incomplete"``.
        """
        from .twee_check import check_twee_proof, goal_matches_conclusion
        from .twee_entailment import check_entailment_twee_detailed

        premises = list(premises)
        use_wsl = options.pop("use_wsl", True)
        twee_cmd = options.pop("twee_cmd", None)
        seconds = max(1, timeout // 1000)

        try:
            result, elapsed = _timed(lambda: check_entailment_twee_detailed(
                premises, formula, timeout=seconds, use_wsl=use_wsl, twee_cmd=twee_cmd))
        except NotImplementedError as exc:
            return Verdict(UNKNOWN, self.name, reason="unsupported", detail=str(exc))
        except (OSError, RuntimeError) as exc:
            # RuntimeError covers environmental plumbing below the OSError
            # layer — notably _to_wsl_path's "wslpath could not translate"
            # on a broken WSL distro (review-confirmed leak): decide() must
            # return a Verdict for in-contract input, never raise.
            return Verdict(ERROR, self.name, reason="infra", detail=str(exc))

        status = result["status"]

        if status == "Theorem":
            proof = result["proof"]
            if proof is None:
                # Twee said Theorem but its proof text did not parse (see
                # check_entailment_twee_detailed's proof_parse_error key):
                # the policy stands — no independent verification, no
                # PROVED — but this is an ERROR verdict, never a crash.
                return Verdict(
                    ERROR, self.name, reason="infra", wall_time=elapsed,
                    detail="twee reported Theorem but its proof text was "
                           "unparseable — refusing PROVED without "
                           "verification: "
                           + str(result.get("proof_parse_error")))
            check_result = check_twee_proof(proof, premises)
            matches_goal = goal_matches_conclusion(proof, formula)
            if check_result.ok and matches_goal:
                return Verdict(PROVED, self.name, wall_time=elapsed, proof=proof.to_dict(),
                               detail="proof independently verified by atp.twee_check")
            problems = []
            if not check_result.ok:
                problems.append(f"check_twee_proof: {check_result.error}")
            if not matches_goal:
                problems.append("goal_matches_conclusion: the proved goal does not "
                                "restate the requested conclusion")
            return Verdict(ERROR, self.name, reason="infra", wall_time=elapsed,
                           detail="twee reported Theorem but its proof failed independent "
                                  "verification: " + "; ".join(problems))

        if status == "CounterSatisfiable":
            return Verdict(REFUTED, self.name, wall_time=elapsed)

        if result["timed_out"]:
            return Verdict(UNKNOWN, self.name, reason="timeout", wall_time=elapsed,
                           detail="twee did not finish within the time budget")

        return Verdict(UNKNOWN, self.name, reason="incomplete", wall_time=elapsed,
                       detail=f"twee status: {status}")
