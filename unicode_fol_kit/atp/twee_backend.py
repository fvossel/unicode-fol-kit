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

**Twee's one-line ``Reflexivity.`` proof.** When the goal is an instance of ``x = x``
(``a = a``, ``f(a) = f(a)``, ``tuple(a, b) = tuple(a, b)``) Twee prints no rewrite
chain at all, only ``Proof:`` and ``Reflexivity.``
(:func:`atp.twee_entailment.parse_twee_proof` reads chains and says it cannot read
this). It is a proof with ZERO steps, and is read as one: :func:`_reflexivity_proof`
builds the :class:`~atp.twee_entailment.TweeProof` whose goal chain is the single
term (no citation), so it goes through the SAME two checks as every other proof. A
goal whose two sides differ fails the first, and one that is not the requested
conclusion fails the second; either is ERROR, as ever.
"""

import time
from typing import Sequence

from ..fol.nodes import Node
from .protocol import (
    ERROR, PROVED, REFUTED, UNKNOWN, ProverBackend, Verdict, _rejection_detail,
)

__all__ = ["TweeBackend"]


def _reflexivity_proof(raw_output: str):
    """The :class:`~atp.twee_entailment.TweeProof` of Twee's one-line ``Reflexivity.``
    proof, or ``None`` when ``raw_output`` is anything else.

    Twee prints it, recorded on Twee 2.6.1, for a goal that is an instance of
    ``x = x``::

        The conjecture is true! Here is a proof.


        Goal 1 (goal): a = a.
        Proof:
        Reflexivity.

        RESULT: Theorem (the conjecture is true).

    Nothing is guessed: the text must be exactly those five non-blank lines (no axiom
    is listed, none was used), the goal line must read as an equation, and the chain
    is the goal's left-hand side alone with no citation. Whether the two sides really
    are one term, and whether the goal is the requested conclusion, is for
    :func:`atp.twee_check.check_twee_proof` and
    :func:`atp.twee_check.goal_matches_conclusion` to say, exactly as for any proof.
    """
    from .twee_entailment import (
        _GOAL_RE, TweeChain, TweeEquation, TweeGoal, TweeProof, _parse_term, _split_equation,
    )

    lines = [line.rstrip() for line in raw_output.splitlines() if line.strip()]
    if (len(lines) != 5 or lines[0] != "The conjecture is true! Here is a proof."
            or lines[2] != "Proof:" or lines[3] != "Reflexivity."
            or not lines[4].startswith("RESULT: Theorem")):
        return None
    goal_line = _GOAL_RE.match(lines[1])
    if goal_line is None:
        return None
    try:
        lhs_text, rhs_text = _split_equation(goal_line.group(3))
        lhs, rhs = _parse_term(lhs_text), _parse_term(rhs_text)
    except ValueError:
        return None
    return TweeProof((), (), TweeGoal(int(goal_line.group(1)), goal_line.group(2),
                                      TweeEquation(lhs, rhs), TweeChain((lhs,), ())))


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
    subprocess timeout and Twee's own resource-budget ``GaveUp``/other status
    come back UNKNOWN with the honest ``reason``. A missing ``RESULT`` line
    WITHOUT a timeout is Twee refusing the problem (its parse/usage error is on
    stderr) or dying, and is ERROR/``"infra"`` with Twee's own message in
    ``detail`` — never UNKNOWN, which reads like a run that ran out of time.
    """

    name = "twee"
    logics = frozenset({"fol"})
    external = True

    def available(self) -> bool:
        return self.available_for({})

    def available_for(self, options: dict) -> bool:
        """Whether Twee answers where :meth:`decide` will run it: through WSL
        unless ``use_wsl=False``, and as the command ``twee_cmd=`` names (else
        ``$UFK_TWEE_CMD``, else ``~/.local/bin/twee``) -- the two options
        :meth:`decide` forwards to the runner, with its own defaults."""
        from .twee_entailment import twee_available
        return twee_available(use_wsl=options.get("use_wsl", True),
                              twee_cmd=options.get("twee_cmd"))

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
            infrastructure-level failure, not "we don't know"), and likewise
            ERROR/``"infra"`` when Twee printed no ``RESULT:`` line although
            the timeout did not fire (it refused the problem — its own message
            is in ``detail``); any other status is UNKNOWN/``"incomplete"``.
        """
        from .twee_check import check_twee_proof, goal_matches_conclusion, goal_mismatch
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
            reflexivity = proof is None and _reflexivity_proof(result.get("raw_output", ""))
            if reflexivity:
                proof = reflexivity
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
                detail = "proof independently verified by atp.twee_check"
                if reflexivity:
                    detail += ("; Twee's proof is the one line 'Reflexivity.' (the goal is "
                               "an instance of x = x), a proof with no rewrite step")
                return Verdict(PROVED, self.name, wall_time=elapsed, proof=proof.to_dict(),
                               detail=detail)
            problems = []
            if not check_result.ok:
                problems.append(f"check_twee_proof: {check_result.error}")
            if not matches_goal:
                reason = goal_mismatch(proof, formula)
                problems.append("goal_matches_conclusion: the proved goal does not "
                                "restate the requested conclusion"
                                + (f" ({reason})" if reason else ""))
            return Verdict(ERROR, self.name, reason="infra", wall_time=elapsed,
                           detail="twee reported Theorem but its proof failed independent "
                                  "verification: " + "; ".join(problems))

        if status == "CounterSatisfiable":
            return Verdict(REFUTED, self.name, wall_time=elapsed)

        if result["timed_out"]:
            return Verdict(UNKNOWN, self.name, reason="timeout", wall_time=elapsed,
                           detail="twee did not finish within the time budget")

        if status == "Unknown":
            # No RESULT line although our timeout did not fire (the case above):
            # Twee refused the problem or died -- its parse/usage error is on
            # stderr, exit 1, with nothing on stdout (see the module docstring
            # of atp.twee_entailment, shape 5; ``raw_output`` carries stderr).
            # An error with Twee's own text, not "incomplete".
            return Verdict(ERROR, self.name, reason="infra", wall_time=elapsed,
                           detail=_rejection_detail(
                               "twee", result.get("raw_output", ""),
                               "no RESULT line in its output"))

        return Verdict(UNKNOWN, self.name, reason="incomplete", wall_time=elapsed,
                       detail=f"twee status: {status}")
