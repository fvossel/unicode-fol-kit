"""Entailment checking via the Vampire theorem prover (TPTP backend).

The companion to :func:`prover9_entailment.check_logical_entailment`, but driving
`Vampire <https://vprover.github.io/>`_ instead of Prover9. The problem is emitted
in TPTP ``fof`` syntax — every premise as an ``axiom`` and the conclusion as a
``conjecture`` — and handed to a Vampire binary whose path the caller supplies.
Vampire negates the conjecture internally and reports ``SZS status Theorem`` when
the premises entail the conclusion.

Only the classical FOL fragment is supported, exactly as far as ``Node.to_tptp``
reaches: a modal, second-order, Łukasiewicz, or lambda node raises
``NotImplementedError`` from ``to_tptp`` and that error propagates here.

A Windows host can drive a Linux Vampire installed in WSL by passing
``use_wsl=True``: Vampire is then launched through ``wsl.exe`` and the temporary
problem file's path is translated to its ``/mnt/...`` form with ``wslpath``.

:func:`check_logical_entailment_vampire` is the original bool-returning entry
point and its behaviour is unchanged below. :func:`check_entailment_vampire_detailed`
is an additive alternative that reads Vampire's SZS status line and TSTP
derivation (via :mod:`atp.tstp`) instead of the old substring heuristic, for
callers that want the full ``atp.protocol`` status/reason vocabulary and a proof
DAG rather than a bare bool.
"""

import os
import subprocess
import tempfile
from typing import List, Tuple

from ..fol.nodes import Node
from ._ascii_names import reverse_map_text
from ._tptp_problem import generate_tptp_problem, generate_tptp_problem_with_mapping


def _generate_vampire_input(premises: List[Node], conclusion: Node) -> str:
    """Build a TPTP ``fof`` problem string from premises and a conclusion.

    Each premise becomes ``fof(premise_<i>, axiom, <tptp>).`` and the conclusion
    becomes ``fof(goal, conjecture, <tptp>).``. The bodies come from
    ``Node.to_tptp`` (so variables are upper-cased TPTP-style). Vampire treats the
    single conjecture as the goal to prove from the axioms.

    A thin wrapper over the shared :func:`atp._tptp_problem.generate_tptp_problem`
    (also used by :mod:`atp.eprover_backend` and :mod:`atp.twee_entailment`,
    which build the identical problem shape) — see that module for the
    cross-formula symbol-collision guard this delegates to, which can itself
    raise ``NotImplementedError`` before any TPTP text is produced.
    """
    return generate_tptp_problem(premises, conclusion)


def _is_entailed_output(stdout: str) -> bool:
    """Decide entailment from Vampire's stdout.

    Vampire reports ``SZS status Theorem`` when it proves the conjecture from the
    axioms; ``Refutation found`` is the equivalent message in its default proof
    output (and also covers the vacuous case of inconsistent premises, which
    entail anything). Either signal means the entailment holds. A
    ``CounterSatisfiable`` / ``Satisfiable`` / ``Timeout`` status — or no proof at
    all — means it does not.
    """
    return ("SZS status Theorem" in stdout) or ("Refutation found" in stdout)


def _to_wsl_path(windows_path: str) -> str:
    """Translate a Windows path to its WSL ``/mnt/...`` form via ``wslpath``.

    Backslashes are turned into forward slashes first: the WSL interop layer
    swallows backslashes in arguments (``C:\\Users\\…`` reaches ``wslpath`` as
    ``C:Users…`` with the separators gone), whereas ``wslpath`` accepts the
    forward-slash spelling ``C:/Users/…`` directly.
    """
    result = subprocess.run(
        ["wsl.exe", "wslpath", "-u", windows_path.replace("\\", "/")],
        capture_output=True,
        text=True,
        timeout=20,
    )
    wsl_path = result.stdout.strip()
    if not wsl_path:
        raise RuntimeError(
            f"wslpath could not translate {windows_path!r} (is WSL available?): "
            f"{result.stderr.strip()}"
        )
    return wsl_path


def _spawn_vampire(input_str: str, vampire_path: str, timeout: int = 30,
                   use_wsl: bool = False,
                   extra_args: Tuple[str, ...] = ()) -> Tuple[str, bool]:
    """Write the TPTP problem to a temp file, run Vampire, return its raw stdout.

    Shared by :func:`_run_vampire` (the original bool-returning route, which
    calls this with ``extra_args=()`` — an unchanged command line) and
    :func:`check_entailment_vampire_detailed` (the SZS/TSTP-reading route,
    which adds ``--proof tptp`` so Vampire's proof is printed as annotated
    TSTP ``fof(...)`` statements instead of its native ``N. formula [rule
    N1,N2]`` numbered-line format — only the TSTP form is what
    :func:`atp.tstp.parse_tstp_derivation` reads).

    Returns:
        ``(stdout, timed_out)`` — ``stdout`` is Vampire's captured stdout text
        (``""`` if the process timed out before producing any), ``timed_out``
        is ``True`` iff the subprocess exceeded ``timeout`` seconds. A
        subprocess timeout is swallowed into this return value, exactly as the
        Prover9 runner swallows one into a bool; any OTHER error — notably
        ``FileNotFoundError`` for a wrong ``vampire_path`` — propagates to the
        caller. The temporary file is always removed, even when the subprocess
        raises.

    With ``use_wsl=True`` Vampire is invoked inside WSL as
    ``wsl.exe <vampire_path> <extra_args...> <file>``, and the Windows temp-file
    path is first translated to its ``/mnt/...`` form with ``wslpath`` so a
    Linux Vampire under WSL can read the file the Windows side created.
    """
    with tempfile.NamedTemporaryFile(mode="w", suffix=".p", delete=False,
                                     encoding="utf-8") as temp_file:
        temp_file.write(input_str)
        temp_filename = temp_file.name

    try:
        if use_wsl:
            command = ["wsl.exe", vampire_path, *extra_args, _to_wsl_path(temp_filename)]
        else:
            command = [vampire_path, *extra_args, temp_filename]
        result = subprocess.run(
            command,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
        return result.stdout, False
    except subprocess.TimeoutExpired:
        return "", True
    finally:
        try:
            os.unlink(temp_filename)
        except OSError:
            pass


def _run_vampire(input_str: str, vampire_path: str, timeout: int = 30,
                 use_wsl: bool = False) -> bool:
    """Run Vampire and decide entailment from its stdout (see :func:`_spawn_vampire`
    for the process plumbing this delegates to; behaviour is unchanged from before
    the refactor — a timeout still reports ``False``, other errors still propagate).
    """
    stdout, timed_out = _spawn_vampire(input_str, vampire_path, timeout=timeout,
                                       use_wsl=use_wsl)
    if timed_out:
        return False
    return _is_entailed_output(stdout)


def check_logical_entailment_vampire(premises: List[Node], conclusion: Node,
                                     vampire_path: str, timeout: int = 30,
                                     use_wsl: bool = False) -> bool:
    """Return whether ``premises`` entail ``conclusion``, decided by Vampire.

    Args:
        premises: a list of classical FOL premise formulas.
        conclusion: the classical FOL conclusion formula.
        vampire_path: path to a Vampire executable (e.g. ``"/usr/bin/vampire"``).
            With ``use_wsl=True`` this is the command/path INSIDE WSL — e.g.
            ``"vampire"`` if it is on the WSL ``PATH``, or ``"/home/me/vampire"``.
        timeout: seconds to allow the Vampire process before giving up and
            returning ``False`` (default 30).
        use_wsl: when True, run Vampire inside WSL via ``wsl.exe`` and translate
            the temp-file path to its ``/mnt/...`` form, so a Windows host can
            drive a Linux Vampire installed in WSL.

    Returns:
        ``True`` iff Vampire proves the conclusion follows from the premises.
        Note that every premise and the conclusion must be a closed sentence:
        Vampire rejects formulas with unquantified (free) variables, and such a
        rejection is reported as ``False`` (no proof), not raised.

    Raises:
        FileNotFoundError: ``vampire_path`` does not point to an executable (or,
            with ``use_wsl=True``, ``wsl.exe`` itself is not found).
        NotImplementedError: either a formula is outside the first-order
            fragment (modal / second-order / Łukasiewicz / lambda), surfaced
            by ``to_tptp``, or two distinct predicate (or function/constant)
            names across ``premises``/``conclusion`` would render as the
            same TPTP identifier — see
            :mod:`atp._tptp_problem`'s module docstring for why that is
            refused rather than silently merged into one symbol.
    """
    vampire_input = _generate_vampire_input(premises, conclusion)
    return _run_vampire(vampire_input, vampire_path, timeout=timeout,
                        use_wsl=use_wsl)


# ---------------------------------------------------------------------------
# SZS/TSTP-reading route (additive)
# ---------------------------------------------------------------------------

# How much of Vampire's stdout to keep in "output_excerpt": the TAIL, since
# that is where the SZS status line and (when present) the end of the proof
# live for Vampire's default output ordering; the full text is kept whenever
# it is already shorter than this.
_EXCERPT_CHARS = 4000


def check_entailment_vampire_detailed(premises: List[Node], conclusion: Node,
                                      vampire_path: str, timeout: int = 30,
                                      use_wsl: bool = False) -> dict:
    """Run Vampire and read its SZS status + TSTP derivation, not just a bool.

    Builds the same TPTP ``fof`` problem as :func:`check_logical_entailment_vampire`
    (every premise an ``axiom``, the conclusion the single ``conjecture`` — a
    ``query="conjecture"`` framing in :mod:`atp.tstp` terms) and drives the same
    subprocess plumbing (:func:`_spawn_vampire`), but decides the outcome by
    reading the ``% SZS status ...`` line with :func:`atp.tstp.extract_szs_status`
    and :func:`atp.tstp.szs_to_verdict_fields` instead of the old
    ``"SZS status Theorem" in stdout`` substring test — so ``CounterSatisfiable``,
    ``Timeout``, ``GaveUp``, etc. each come back as their own honest
    ``atp.protocol`` status/reason pair rather than all collapsing into "not
    entailed". Unlike :func:`check_logical_entailment_vampire`, this function
    passes ``--proof tptp`` on Vampire's command line: Vampire's DEFAULT proof
    output is its own native numbered-line format (``10. mortal(socrates)
    [resolution 7,8]``), which carries the same information but is not
    TSTP-annotated ``fof``/``cnf`` syntax, so ``--proof tptp`` is what makes
    :func:`atp.tstp.parse_tstp_derivation` able to read it into a proof DAG.

    Args:
        premises: a list of classical FOL premise formulas.
        conclusion: the classical FOL conclusion formula.
        vampire_path: path to a Vampire executable — see
            :func:`check_logical_entailment_vampire`.
        timeout: seconds to allow the Vampire process before giving up
            (default 30).
        use_wsl: drive a Linux Vampire under WSL — see
            :func:`check_logical_entailment_vampire`.

    Returns:
        A JSON-compatible dict:

        * ``szs_status``: the raw SZS status token (e.g. ``"Theorem"``), or
          ``None`` if Vampire's output had no ``SZS status`` line at all (a
          timeout before any output, or a Vampire build/mode that suppresses
          the line — in which case ``status``/``reason`` fall back to the
          same "Refutation found" substring heuristic
          :func:`check_logical_entailment_vampire` uses, so this function is
          never STRICTLY less informative than the old one).
        * ``status``: ``atp.protocol.PROVED`` / ``REFUTED`` / ``UNKNOWN`` /
          ``ERROR`` (``UNKNOWN``/``"timeout"`` on a subprocess timeout).
        * ``reason``: the matching ``atp.protocol`` reason axis value, or
          ``None`` for a definitive verdict.
        * ``output_excerpt``: the last :data:`_EXCERPT_CHARS` characters of
          Vampire's stdout (the whole thing, if shorter) — always present,
          even ``""`` on a timeout, so a caller always has something to show.
        * ``derivation``: :class:`atp.tstp.TstpDerivation`'s ``to_dict()``
          when the output contained at least one parseable ``fof``/``cnf``
          statement, else ``None`` (no derivation to report — not an error).

        Every symbol name in ``output_excerpt`` and in ``derivation``'s
        formulas has already been translated back from whatever ASCII-safe
        token :func:`atp._tptp_problem.generate_tptp_problem_with_mapping`
        may have substituted (a non-ASCII or digit-leading kit-level name) to
        the ORIGINAL kit-level name — see that function's module docstring.
        A name Vampire introduced itself (a Skolem constant, a
        clausification symbol) was never one of ours and is left as Vampire
        printed it.

    Raises:
        FileNotFoundError: ``vampire_path`` does not point to an executable
            (or, with ``use_wsl=True``, ``wsl.exe`` itself is not found) —
            same contract as :func:`check_logical_entailment_vampire`.
        NotImplementedError: a formula is outside the first-order fragment,
            or a symbol-folding collision (see
            :func:`check_logical_entailment_vampire`'s ``Raises`` for both),
            surfaced before any subprocess is spawned — same contract as
            :func:`check_logical_entailment_vampire`.
    """
    from .protocol import PROVED, UNKNOWN
    from .tstp import extract_szs_status, parse_tstp_derivation, reverse_map_derivation, szs_to_verdict_fields

    vampire_input, name_map = generate_tptp_problem_with_mapping(premises, conclusion)
    stdout, timed_out = _spawn_vampire(vampire_input, vampire_path, timeout=timeout,
                                       use_wsl=use_wsl, extra_args=("--proof", "tptp"))

    if timed_out:
        return {
            "szs_status": None,
            "status": UNKNOWN,
            "reason": "timeout",
            "output_excerpt": "",
            "derivation": None,
        }

    pred_rev, term_rev = name_map.reverse_rendered()
    excerpt = reverse_map_text(stdout[-_EXCERPT_CHARS:], pred_rev, term_rev)
    szs = extract_szs_status(stdout)
    if szs is None:
        status = PROVED if _is_entailed_output(stdout) else UNKNOWN
        reason = None if status == PROVED else "incomplete"
    else:
        status, reason = szs_to_verdict_fields(szs, query="conjecture")

    derivation = reverse_map_derivation(parse_tstp_derivation(stdout), name_map)
    derivation_dict = derivation.to_dict() if derivation.steps else None

    return {
        "szs_status": szs,
        "status": status,
        "reason": reason,
        "output_excerpt": excerpt,
        "derivation": derivation_dict,
    }
