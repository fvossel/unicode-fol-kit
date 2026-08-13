"""Leo-III backend: mono-modal alethic decisions via NXF + the Leo-III prover.

`Leo-III <https://github.com/leoprover/Leo-III>`_ is a higher-order ATP with
native support for TPTP's Non-Classical Logic dialect (NXF/NHF, see
:mod:`atp.tptp_ncl`): handed an NXF problem with a ``logic`` role statement,
it decides the formula in exactly that non-classical logic rather than a
first-order approximation of it. This module is the thin
:class:`~atp.protocol.ProverBackend` adapter around that: it folds
``premises ⊨ formula`` into one NXF conjecture (:mod:`atp.tptp_ncl`), spawns
``java -jar leo3.jar <problem> -t <seconds>``, and reads the result back
through the shared TPTP-family SZS reader (:mod:`atp.tstp`) — the identical
plumbing shape :mod:`atp.vampire_entailment` uses for classical Vampire runs,
generalised to Leo-III's non-classical mode.

Scope: exactly what :func:`atp.tptp_ncl.to_tptp_ncl` can render — the
mono-modal alethic PROPOSITIONAL fragment, frames K/T/S4/S5. A formula
outside that fragment (a quantifier, a non-nullary atom, or a non-alethic
modal family) is reported as ``UNKNOWN``/``"unsupported"`` rather than a
malformed or silently wrong NXF file ever reaching the subprocess — see
:func:`Leo3Backend.decide`.

Discovery is deliberately narrow and explicit, matching
:class:`atp.protocol.Prover9Backend`/:class:`atp.protocol.VampireBackend`'s
own env-var-then-PATH convention: ``$UFK_LEO3`` must point to either a
Leo-III ``.jar`` (invoked as ``java -jar <path> ...``) or an already-executable
wrapper script/binary (invoked directly, no ``java -jar`` — for a machine
where Leo-III is wrapped in a shell/batch launcher instead of a bare jar), AND
``java`` must be resolvable on ``PATH``. Both are required for
:meth:`Leo3Backend.available` to return ``True`` — this kit's own
:mod:`atp.protocol` module explicitly documents that a "known but
unavailable" backend must raise :class:`~atp.protocol.BackendUnavailable`
rather than silently vanish from a chain, and this backend follows that
contract.

NOT independently verified on this machine: no local Leo-III install was
available to actually run against (see the module docstring of
``tests/test_tptp_ncl.py`` for what IS/is-not exercised). The live test below
is skipped unless ``$UFK_LEO3`` is set, and documents the intended path for
whoever next runs it against a real Leo-III.
"""

import os
import shutil
import subprocess
import tempfile
import time
from typing import Optional, Sequence

from ..fol.nodes import And, Implies, Node
from .protocol import ERROR, UNKNOWN, BackendUnavailable, ProverBackend, Verdict
from .tptp_ncl import to_tptp_ncl
from .tstp import extract_szs_status, szs_to_verdict_fields

__all__ = ["Leo3Backend"]

# How much of Leo-III's stdout+stderr to keep on an ERROR verdict (no SZS
# status line found at all) — mirrors atp.vampire_entailment's _EXCERPT_CHARS
# convention: enough to diagnose a syntax/CLI-usage failure without dumping
# an unbounded proof search log into a Verdict.
_EXCERPT_CHARS = 2000

# How many EXTRA seconds beyond the prover's own ``-t <seconds>`` budget the
# subprocess itself is allowed before this backend gives up waiting — Leo-III
# is asked to stop at ``timeout_sec`` internally, so the outer subprocess
# timeout is only a safety net against a prover that ignores ``-t`` (a hung
# JVM, a malformed CLI invocation that silently no-ops the flag, ...).
_SUBPROCESS_SLACK_SECONDS = 10


def _fold_premises(formula: Node, premises: Sequence[Node]) -> Node:
    """Fold ``premises ⊨ formula`` into the single formula ``(∧premises) → formula``.

    A local copy of :mod:`atp.protocol`'s private ``_implication`` helper
    (that module must not be modified or imported from beyond its public
    surface — see this kit's contribution conventions): NXF has no separate
    premise list, so every :class:`ProverBackend` that speaks it must fold
    premises into one conjecture itself, same as
    :class:`atp.protocol.Z3Backend`/``ModalTableauBackend``/``QmlBackend`` do
    via the module they live in.
    """
    premises = list(premises)
    if not premises:
        return formula
    conj = premises[0]
    for p in premises[1:]:
        conj = And(conj, p)
    return Implies(conj, formula)


class Leo3Backend(ProverBackend):
    """Mono-modal alethic decisions (K/T/S4/S5, propositional fragment) via Leo-III.

    See the module docstring for scope, discovery, and the SZS-reading
    contract. ``premises`` is the standard LOCAL consequence reading shared
    by every modal backend in this kit (see
    :class:`atp.protocol.ProverBackend`'s docstring): ``⊨ (∧premises) →
    formula``.
    """

    name = "leo3"
    logics = frozenset({"modal"})
    external = True

    @staticmethod
    def _jar_or_wrapper() -> Optional[str]:
        """Return ``$UFK_LEO3`` (a leo3.jar path or executable wrapper), or ``None``."""
        return os.environ.get("UFK_LEO3") or None

    @staticmethod
    def _java() -> Optional[str]:
        """Return the resolved ``java`` binary on PATH, or ``None``."""
        return shutil.which("java")

    def available(self) -> bool:
        """True iff both ``$UFK_LEO3`` is set and ``java`` resolves on PATH.

        Pure discovery (env var + PATH lookup only) — deliberately does NOT
        check that ``$UFK_LEO3`` actually points at an existing file: neither
        :class:`atp.protocol.Prover9Backend` nor ``VampireBackend`` do that
        check either, leaving a stale/typo'd path to surface as a genuine
        ``FileNotFoundError`` from the subprocess call instead (caught and
        reported as an ``ERROR``/``"infra"`` verdict — see :meth:`decide`).
        """
        return self._jar_or_wrapper() is not None and self._java() is not None

    def decide(self, formula: Node, premises: Sequence[Node] = (),
               timeout: int = 10000, **options) -> Verdict:
        """Decide ``premises ⊨ formula`` in the given alethic modal frame via Leo-III.

        Args:
            formula: the conclusion; together with ``premises`` folded into
                one NXF conjecture by :func:`_fold_premises` +
                :func:`atp.tptp_ncl.to_tptp_ncl`.
            premises: local-consequence premises (see class docstring).
            timeout: milliseconds, per the :class:`ProverBackend` contract;
                converted to whole seconds (minimum 1) for Leo-III's own
                ``-t <seconds>`` flag.
            **options: ``frame`` (default ``"K"``) and ``domains`` (default
                ``"constant"``) are forwarded to
                :func:`atp.tptp_ncl.to_tptp_ncl`; no other options are read.

        Returns:
            A :class:`~atp.protocol.Verdict` with ``logic="modal"``:

            * the formula is outside the supported NXF fragment (a
              :class:`ValueError`/:class:`NotImplementedError` from
              :func:`to_tptp_ncl`) → ``UNKNOWN``/``"unsupported"``, with no
              subprocess ever spawned;
            * the subprocess exceeds its safety-net timeout → ``UNKNOWN``/
              ``"timeout"``;
            * the subprocess cannot even be started (bad ``$UFK_LEO3``/java
              path) → ``ERROR``/``"infra"``;
            * output has no ``% SZS status`` line at all → ``ERROR``/
              ``"infra"``, with a trailing excerpt of the raw output in
              ``detail`` (Leo-III printed SOMETHING but not in the expected
              form — a genuine infrastructure surprise, not a decided
              ``UNKNOWN``);
            * otherwise, the SZS status is mapped through
              :func:`atp.tstp.szs_to_verdict_fields` with
              ``query="conjecture"`` (the problem carries exactly one
              ``conjecture``-role formula — see :func:`to_tptp_ncl`'s
              docstring) into ``PROVED``/``REFUTED``/``UNKNOWN``, with the
              raw SZS token kept verbatim in ``szs_status``.

        Raises:
            BackendUnavailable: neither ``$UFK_LEO3`` nor ``java`` (or
                neither) was found — mirrors
                :class:`atp.protocol.Prover9Backend`/``VampireBackend``'s own
                defensive re-check inside ``decide()`` (in case a caller
                invokes this backend directly rather than through
                :func:`atp.protocol.run_backend`, which already enforces
                this).
        """
        jar = self._jar_or_wrapper()
        java = self._java()
        if jar is None or java is None:
            raise BackendUnavailable(
                "leo3: needs $UFK_LEO3 (path to leo3.jar or an executable wrapper) "
                "and 'java' on PATH — set $UFK_LEO3 and/or put 'java' on PATH.")

        frame = options.pop("frame", "K")
        domains = options.pop("domains", "constant")
        goal = _fold_premises(formula, premises)

        try:
            problem_text = to_tptp_ncl(goal, frame=frame, domains=domains,
                                       conjecture_name="c")
        except (ValueError, NotImplementedError) as exc:
            return Verdict(UNKNOWN, self.name, logic="modal", reason="unsupported",
                           detail=str(exc))

        timeout_sec = max(1, timeout // 1000)
        start = time.perf_counter()

        with tempfile.NamedTemporaryFile(mode="w", suffix=".p", delete=False,
                                         encoding="utf-8") as problem_file:
            problem_file.write(problem_text)
            problem_path = problem_file.name

        try:
            if jar.lower().endswith(".jar"):
                command = [java, "-jar", jar, problem_path, "-t", str(timeout_sec)]
            else:
                command = [jar, problem_path, "-t", str(timeout_sec)]
            try:
                result = subprocess.run(
                    command, capture_output=True, text=True,
                    timeout=timeout_sec + _SUBPROCESS_SLACK_SECONDS)
            except subprocess.TimeoutExpired:
                elapsed = time.perf_counter() - start
                return Verdict(UNKNOWN, self.name, logic="modal", reason="timeout",
                               wall_time=elapsed,
                               detail=f"leo3 exceeded {timeout_sec + _SUBPROCESS_SLACK_SECONDS}s "
                                      "(prover -t budget plus safety-net slack)")
            except OSError as exc:
                elapsed = time.perf_counter() - start
                return Verdict(ERROR, self.name, logic="modal", reason="infra",
                               wall_time=elapsed, detail=f"{type(exc).__name__}: {exc}")
        finally:
            try:
                os.unlink(problem_path)
            except OSError:
                pass

        elapsed = time.perf_counter() - start
        output = result.stdout + "\n" + result.stderr
        szs = extract_szs_status(output)
        if szs is None:
            excerpt = output[-_EXCERPT_CHARS:]
            return Verdict(ERROR, self.name, logic="modal", reason="infra",
                           wall_time=elapsed,
                           detail=f"no 'SZS status' line in leo3 output: {excerpt!r}")

        status, reason = szs_to_verdict_fields(szs, query="conjecture")
        return Verdict(status, self.name, logic="modal", reason=reason,
                       wall_time=elapsed, szs_status=szs,
                       detail=f"leo3 SZS status {szs} (frame={frame})")
