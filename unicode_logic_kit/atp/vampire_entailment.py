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
import re
import subprocess
import tempfile
from typing import List, Optional, Sequence, Tuple

from ..fol.nodes import Node
from ._ascii_names import reverse_map_text
from ._tff_problem import generate_tff_arith_problem
from ._tptp_problem import generate_tptp_problem_for_prover, generate_tptp_problem_with_mapping
from ._writer_support import names_kwargs


def _generate_vampire_input(premises: List[Node], conclusion: Node,
                            *, tff: Optional[bool] = None,
                            sort: Optional[str] = None,
                            premise_names: Optional[Sequence[str]] = None) -> str:
    """Build a TPTP problem string from premises and a conclusion.

    Each premise becomes an ``axiom`` and the conclusion the single
    ``conjecture``. Vampire treats the single conjecture as the goal to
    prove from the axioms.

    ``sort`` (``None`` by default) selects the single-numeric-sort typed
    arithmetic route (:func:`atp._tff_problem.generate_tff_arith_problem`,
    ``'real'`` or ``'int'`` — see that module's docstring) UNCONDITIONALLY
    when given, taking priority over ``tff``: an opt-in alternative, so a
    caller must ask for it explicitly (every existing caller that never
    passes ``sort`` keeps its current ``tff``-selected/auto-selected
    behaviour byte-for-byte). With ``sort=None``, ``tff`` selects between
    the two dialects: ``None`` (the default) tries the native, genuinely-typed
    ``tff`` route (:func:`atp.tptp_tff.generate_tff_problem`) when
    ``premises``/``conclusion`` contain a SortedQuantifier/SortedConstant/
    SortedCount node (see :func:`atp.tptp_tff.problem_needs_tff`), and falls back
    to the classical guard-predicate ``fof`` route when the typed writer refuses
    the problem (a :class:`~unicode_logic_kit.atp.tptp_tff.Tf0Refusal`: its text would
    ask another question than the kit's; or a node it does not cover that the ``fof``
    writer does: a counting quantifier, ``Contrast``, ``Measure`` — see
    :func:`atp._tptp_problem.generate_tptp_problem_for_prover`); a problem without a sorted node goes to
    the ``fof`` route (:func:`atp._tptp_problem.generate_tptp_problem` — also
    used by :mod:`atp.eprover_backend` and :mod:`atp.twee_entailment`, which build
    the identical ``fof`` problem shape). ``tff=True``/``False`` force one route
    explicitly, and ``True`` raises the typed writer's refusal. Every route's own
    cross-formula symbol-collision guard can raise ``NotImplementedError`` before
    any TPTP text is produced. ``premise_names`` names the premises' ``axiom`` lines
    in whichever route is written (see :func:`atp._tptp_problem
    .generate_tptp_problem_with_mapping`), ``premise_<i>`` when it is ``None``.
    """
    if sort is not None:
        problem, _name_map = generate_tff_arith_problem(
            premises, conclusion, sort=sort, **names_kwargs(premise_names))
        return problem
    return generate_tptp_problem_for_prover(
        premises, conclusion, tff=tff, fof_writer=generate_tptp_problem_with_mapping,
        premise_names=premise_names).text


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


#: Text that says Vampire FAILED rather than ended a search: its own
#: ``User error: ...``, a parse error or exception, a crash. Seen in an output
#: it rules out the "ended by itself" reading below, whatever else is printed.
_FAILURE_TEXT = re.compile(
    r"\berror\b|exception|assertion|segmentation|core dumped|abort", re.IGNORECASE)

#: The line Vampire's statistics block ends a search with:
#: ``% Termination reason: Refutation not found, incomplete strategy``.
_TERMINATION_REASON = re.compile(r"^\s*%?\s*Termination reason:\s*(?P<why>.*?)\s*$",
                                 re.MULTILINE)


def _ended_by_itself(stdout: str) -> Optional[Tuple[str, str]]:
    """Whether a run WITHOUT an SZS status line is a search Vampire ended itself.

    Vampire does not always print an SZS line when it gives up. Measured on
    Vampire 5.0.1: a non-theorem of a typed-arithmetic (``$int``) problem ends
    ``% Refutation not found, incomplete strategy`` ... ``% Termination reason:
    Refutation not found, incomplete strategy`` (exit code 1, no SZS line), and
    a run stopped by its own ``--time_limit`` / ``--activation_limit`` ends
    ``% Termination reason: Time limit`` / ``Activation limit`` the same way.
    Those are honest answers, not refusals: the problem WAS read and searched.

    Returns ``(reason, why)`` -- the :mod:`atp.protocol` reason axis value and
    the termination reason as Vampire worded it -- or ``None`` when the output
    does not show a search that ended: no ``Termination reason`` line and no
    ``Refutation not found``, or any text of a failure (``User error``, a parse
    error, an exception, a crash), in which case the caller reports an ERROR.
    A reason naming a ``limit`` is a budget Vampire was given: ``Time limit`` is
    ``"timeout"``, any other limit ``"bound_hit"``; every other reason is the
    prover giving up, ``"incomplete"``.
    """
    if _FAILURE_TEXT.search(stdout):
        return None
    match = _TERMINATION_REASON.search(stdout)
    if match is not None:
        why = match.group("why")
    elif "Refutation not found" in stdout:
        why = "Refutation not found"
    else:
        return None
    if re.search(r"\blimit\b", why, re.IGNORECASE):
        return ("timeout" if re.match(r"time\b", why, re.IGNORECASE) else "bound_hit"), why
    return "incomplete", why


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
        followed by its stderr (``""`` if the process timed out before
        producing any): Vampire writes its own ``User error: ...`` to stdout,
        but a launcher failure (``wsl.exe`` cannot find the binary) or a crash
        speaks on stderr, and a refusal whose explanation was dropped would
        read like a run that merely found nothing. ``timed_out``
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
        return (result.stdout or "") + (result.stderr or ""), False
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
                                     use_wsl: bool = False,
                                     tff: Optional[bool] = None,
                                     sort: Optional[str] = None) -> bool:
    """Return whether ``premises`` entail ``conclusion``, decided by Vampire.

    Args:
        premises: a list of classical (or many-sorted) FOL premise formulas.
        conclusion: the (classical or many-sorted) FOL conclusion formula.
        vampire_path: path to a Vampire executable (e.g. ``"/usr/bin/vampire"``).
            With ``use_wsl=True`` this is the command/path INSIDE WSL — e.g.
            ``"vampire"`` if it is on the WSL ``PATH``, or ``"/home/me/vampire"``.
        timeout: seconds to allow the Vampire process before giving up and
            returning ``False`` (default 30).
        use_wsl: when True, run Vampire inside WSL via ``wsl.exe`` and translate
            the temp-file path to its ``/mnt/...`` form, so a Windows host can
            drive a Linux Vampire installed in WSL.
        tff: which TPTP dialect to export as — see :func:`_generate_vampire_input`.
            ``None`` (the default) tries the native typed ``tff`` route whenever
            a sort is used and writes ``fof`` when the typed writer refuses the
            problem; ``True``/``False`` force one route (``True`` raises the
            typed writer's refusal).
        sort: ``None`` (default) leaves ``tff`` in charge as above; ``'real'``
            or ``'int'`` opts into the single-numeric-sort typed arithmetic
            route (:func:`atp._tff_problem.generate_tff_arith_problem`)
            UNCONDITIONALLY, activating Vampire's native arithmetic decision
            procedures — see that module's docstring for the fragment it
            covers (a formula that genuinely mixes several sorts, or is
            outside the arithmetic fragment, raises ``NotImplementedError``
            naming the construct rather than silently falling back). Without
            ``sort`` arithmetic is NOT asked for: a numeral is a constant identified
            by its value and ``+ - * /  < > ≤ ≥`` are uninterpreted symbols, which
            the problem writers write under ordinary words (see
            :mod:`unicode_logic_kit.atp._tptp_problem`), so ``1 ≠ 2`` and ``1 + 1 = 2``
            are not provable here and are with ``sort='int'``.

    Returns:
        ``True`` iff Vampire proves the conclusion follows from the premises.
        Note that every premise and the conclusion must be a closed sentence:
        Vampire rejects formulas with unquantified (free) variables, and such a
        rejection is reported as ``False`` (no proof), not raised — EXCEPT on
        the ``sort=`` route, which refuses a free variable
        (:class:`~unicode_logic_kit.atp._tff_problem.TfaRefusal`, a ``ValueError`` and a
        ``NotImplementedError``) instead of silently picking an implicit-closure
        convention (see :mod:`atp._tff_problem`'s module docstring).

    Raises:
        FileNotFoundError: ``vampire_path`` does not point to an executable (or,
            with ``use_wsl=True``, ``wsl.exe`` itself is not found).
        NotImplementedError: either a formula is outside the fragment the
            selected route covers (see :func:`_generate_vampire_input`), or
            two distinct predicate (or function/constant, or — ``tff``/
            ``sort`` route — sort) names across ``premises``/``conclusion``
            would render as the same TPTP identifier — see
            :mod:`atp._tptp_problem`'s, :mod:`atp.tptp_tff`'s, and
            :mod:`atp._tff_problem`'s module docstrings for why that is
            refused rather than silently merged into one symbol. With
            ``tff=True`` it is also a :class:`~unicode_logic_kit.atp.tptp_tff.Tf0Refusal`
            when the typed text would ask another question than the kit's (that
            class is a ``ValueError`` too). On the ``sort=`` route it is also a
            :class:`~unicode_logic_kit.atp._tff_problem.TfaRefusal` for a free
            variable, an arity conflict, or a constant-vs-function name clash
            (a ``ValueError`` too; see :mod:`atp._tff_problem`'s module docstring).
        ValueError: on the ``sort=`` route only — an invalid ``sort``.
    """
    vampire_input = _generate_vampire_input(premises, conclusion, tff=tff, sort=sort)
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
                                      use_wsl: bool = False,
                                      tff: Optional[bool] = None,
                                      sort: Optional[str] = None,
                                      premise_names: Optional[Sequence[str]] = None,
                                      axiom_names: bool = False) -> dict:
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
        sort: ``None`` (default) leaves ``tff`` in charge; ``'real'``/``'int'``
            opts into the single-numeric-sort typed arithmetic route — see
            :func:`check_logical_entailment_vampire`'s ``sort`` for the full
            contract. Every route (``fof``, ``tff``, ``sort``) hands back a
            :class:`~unicode_logic_kit.atp._tptp_problem.TptpNameMap`, so
            ``output_excerpt`` below IS reverse-mapped to original kit-level
            names on all of them. ``derivation`` still degrades to ``None``
            on the ``tff`` and ``sort`` routes (see below) — :mod:`atp.tstp`
            reads only ``fof``/``cnf`` derivation lines, never ``tff``, a
            pre-existing gap.
        premise_names: one name per premise for the problem's ``axiom`` lines
            instead of ``premise_<i>``, in whichever dialect is written (see
            :func:`atp._tptp_problem.generate_tptp_problem_with_mapping`). Naming the
            premises also asks Vampire to print the names of the axioms of its proof
            (``--output_axiom_names on``), which it otherwise replaces by ``unknown``, so
            that ``relevant_premises`` below can be read.
        axiom_names: ask Vampire for the names of the axioms of its proof without naming
            the premises (they are then ``premise_<i>``). The command line stays
            ``--proof tptp`` when neither this nor ``premise_names`` is given.

    Returns:
        A JSON-compatible dict:

        * ``szs_status``: the raw SZS status token (e.g. ``"Theorem"``), or
          ``None`` if Vampire's output had no ``SZS status`` line at all (a
          timeout before any output, a Vampire build/mode that suppresses
          the line, or Vampire REFUSING the problem). With no line,
          ``status``/``reason`` fall back to the same "Refutation found"
          substring heuristic :func:`check_logical_entailment_vampire` uses
          (``PROVED`` when it is there, so this function is never STRICTLY
          less informative than the old one); otherwise to what Vampire
          printed about how its search ended. A ``Termination reason:`` line
          (``Refutation not found, incomplete strategy`` — Vampire 5.0.1 ends
          a non-theorem of a typed-arithmetic problem this way, with no SZS
          line) is an honest ``UNKNOWN``: ``"incomplete"``, or ``"timeout"``
          / ``"bound_hit"`` when the reason is Vampire's own ``Time limit`` /
          another limit (see :func:`_ended_by_itself`). Only when it printed
          neither a verdict, a refutation nor such an account, although
          nothing cut it off — or printed an error — is it ``ERROR``/
          ``"infra"``: a refusal or a crash. Its own message is in
          ``output_excerpt``.
        * ``status``: ``atp.protocol.PROVED`` / ``REFUTED`` / ``UNKNOWN`` /
          ``ERROR`` (``UNKNOWN``/``"timeout"`` on a subprocess timeout;
          ``ERROR``/``"infra"`` when there is no SZS line and no account of
          a search that ended, or an SZS line that itself names an error such
          as ``SyntaxError``).
        * ``reason``: the matching ``atp.protocol`` reason axis value, or
          ``None`` for a definitive verdict.
        * ``output_excerpt``: the last :data:`_EXCERPT_CHARS` characters of
          Vampire's stdout and stderr (the whole thing, if shorter) — always
          present, even ``""`` on a timeout, so a caller always has something
          to show.
        * ``derivation``: :class:`atp.tstp.TstpDerivation`'s ``to_dict()``
          when the output contained at least one parseable ``fof``/``cnf``
          statement, else ``None`` (no derivation to report — not an error).
          :func:`atp.tstp.parse_tstp_derivation` only recognises ``fof``/
          ``cnf`` statements (see its own docstring), never ``tff``/``tcf``
          ones, so on the ``tff`` route ``derivation`` is CURRENTLY ALWAYS
          ``None`` — even for a genuine, successful proof whose stdout is
          full of well-formed ``tff(...)`` proof lines. This is a real gap
          in the READER (:func:`atp.tstp.parse_tstp_derivation` reads
          ``fof``/``cnf`` lines only), not in the name mapping: the excerpt
          of a ``tff`` run IS translated back through the TF0 writer's name
          map.
        * ``dialect``: which writer produced the problem Vampire was given:
          ``"fof"``, ``"tff"`` or ``"tfa"`` (the ``sort=`` route).
        * ``tff_fallback``: ``None``, or — when ``tff=None`` tried the typed
          writer for a sorted problem, was refused, and wrote ``fof`` instead —
          the sentence that says so and quotes the typed writer's reason (the
          backend puts it into the verdict's ``detail``).
        * ``relevant_premises``: for a PROVED answer to a run that asked for the axiom
          names (``premise_names`` or ``axiom_names``), the sorted 0-based indices of the
          premises the proof's axiom leaves are
          (:func:`atp.tstp.relevant_premises_from_tstp`, read through the problem's name
          map); ``None`` otherwise, and when the proof cannot be read that way.
        * ``background_used``: the ``(name, meaning)`` pairs of the background axioms the
          writer added on its own (the non-emptiness of a sort, the membership of a sorted
          constant) that the proof used — background, not premises, so they are not in
          ``relevant_premises``; ``()`` when none, or when ``relevant_premises`` is
          ``None``.

        Every symbol name in ``output_excerpt`` and in ``derivation``'s
        formulas has already been translated back from whatever ASCII-safe
        token the problem writer may have substituted (a non-ASCII or
        digit-leading kit-level name, or a function/constant renamed because
        its word is a predicate's: ``agent`` -> ``agent_term``) to the
        ORIGINAL kit-level name — on the ``fof`` route
        (:func:`atp._tptp_problem.generate_tptp_problem_with_mapping`), the
        ``tff`` route (:func:`atp.tptp_tff.generate_tff_problem_with_mapping`)
        and the ``sort`` route alike. A name Vampire introduced itself (a
        Skolem constant, a clausification symbol) was never one of ours and
        is left as Vampire printed it, and so is a SORT name on the ``tff``
        route (the TF0 map covers predicates, functions and constants, not
        sorts).

    Raises:
        FileNotFoundError: ``vampire_path`` does not point to an executable
            (or, with ``use_wsl=True``, ``wsl.exe`` itself is not found) —
            same contract as :func:`check_logical_entailment_vampire`.
        NotImplementedError: a formula is outside the fragment the selected
            route covers, or a symbol-folding collision (see
            :func:`check_logical_entailment_vampire`'s ``Raises`` for both),
            surfaced before any subprocess is spawned — same contract as
            :func:`check_logical_entailment_vampire`.
    """
    from .protocol import ERROR, PROVED, UNKNOWN
    from .tstp import (
        _premise_use_from_tstp, extract_szs_status, parse_tstp_derivation,
        reverse_map_derivation, szs_to_verdict_fields,
    )

    if sort is not None:
        vampire_input, name_map = generate_tff_arith_problem(
            premises, conclusion, sort=sort, **names_kwargs(premise_names))
        dialect, fallback_note = "tfa", None
    else:
        built = generate_tptp_problem_for_prover(
            premises, conclusion, tff=tff, fof_writer=generate_tptp_problem_with_mapping,
            premise_names=premise_names)
        vampire_input, name_map = built.text, built.name_map
        dialect, fallback_note = built.dialect, built.fallback_note
    read_axiom_names = axiom_names or premise_names is not None
    extra_args = ("--proof", "tptp") + (("--output_axiom_names", "on") if read_axiom_names else ())
    stdout, timed_out = _spawn_vampire(vampire_input, vampire_path, timeout=timeout,
                                       use_wsl=use_wsl, extra_args=extra_args)

    if timed_out:
        return {
            "szs_status": None,
            "status": UNKNOWN,
            "reason": "timeout",
            "output_excerpt": "",
            "derivation": None,
            "dialect": dialect,
            "tff_fallback": fallback_note,
            "relevant_premises": None,
            "background_used": (),
        }

    if name_map is None:
        excerpt = stdout[-_EXCERPT_CHARS:]
    else:
        pred_rev, term_rev = name_map.reverse_rendered()
        excerpt = reverse_map_text(stdout[-_EXCERPT_CHARS:], pred_rev, term_rev)
    szs = extract_szs_status(stdout)
    if szs is None:
        if _is_entailed_output(stdout):
            status, reason = PROVED, None
        elif (ended := _ended_by_itself(stdout)) is not None:
            # No SZS line, but Vampire printed how its search ended
            # ("Termination reason: Refutation not found, incomplete strategy"):
            # it READ the problem and gave up (or hit its own limit). That is
            # an honest UNKNOWN, not a refusal.
            status, reason = UNKNOWN, ended[0]
        else:
            # No SZS verdict, no refutation and no account of a search, and the
            # process was not cut off by our timeout (handled above): Vampire
            # REFUSED the problem (its "User error: ..." / parse-error text is
            # in the output) or died. That is a failure, not "incomplete" --
            # reporting it as UNKNOWN made a problem Vampire could not read
            # look like one it ran out of time on.
            status, reason = ERROR, "infra"
    else:
        status, reason = szs_to_verdict_fields(szs, query="conjecture")

    parsed = parse_tstp_derivation(stdout)
    derivation = parsed if name_map is None else reverse_map_derivation(parsed, name_map)
    derivation_dict = derivation.to_dict() if derivation.steps else None

    # The proof's axiom leaves, by the names the problem gave them: read from the text
    # Vampire printed (a premise name is not a symbol, so never the renamed excerpt).
    relevant: Optional[Tuple[int, ...]] = None
    background_used: Tuple[Tuple[str, str], ...] = ()
    if read_axiom_names and status == PROVED:
        use = _premise_use_from_tstp(stdout, len(premises), name_map)
        if use is not None:
            relevant, background_used = use

    return {
        "szs_status": szs,
        "status": status,
        "reason": reason,
        "output_excerpt": excerpt,
        "derivation": derivation_dict,
        "dialect": dialect,
        "tff_fallback": fallback_note,
        "relevant_premises": relevant,
        "background_used": background_used,
    }
