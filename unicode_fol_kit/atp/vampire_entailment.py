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
"""

import os
import subprocess
import tempfile
from typing import List

from ..fol.nodes import Node


def _generate_vampire_input(premises: List[Node], conclusion: Node) -> str:
    """Build a TPTP ``fof`` problem string from premises and a conclusion.

    Each premise becomes ``fof(premise_<i>, axiom, <tptp>).`` and the conclusion
    becomes ``fof(goal, conjecture, <tptp>).``. The bodies come from
    ``Node.to_tptp`` (so variables are upper-cased TPTP-style). Vampire treats the
    single conjecture as the goal to prove from the axioms.
    """
    lines: List[str] = []
    for i, premise in enumerate(premises, start=1):
        lines.append(f"fof(premise_{i}, axiom, {premise.to_tptp()}).")
    lines.append(f"fof(goal, conjecture, {conclusion.to_tptp()}).")
    return "\n".join(lines) + "\n"


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


def _run_vampire(input_str: str, vampire_path: str, timeout: int = 30,
                 use_wsl: bool = False) -> bool:
    """Write the TPTP problem to a temp file and run Vampire on it.

    Mirrors the Prover9 runner's contract: a subprocess timeout is swallowed and
    reported as "not entailed" (Vampire could not finish), while any other error —
    notably ``FileNotFoundError`` for a wrong ``vampire_path`` — propagates to the
    caller. The temporary file is always removed, even when the subprocess raises.

    With ``use_wsl=True`` Vampire is invoked inside WSL as
    ``wsl.exe <vampire_path> <file>``, and the Windows temp-file path is first
    translated to its ``/mnt/...`` form with ``wslpath`` so a Linux Vampire under
    WSL can read the file the Windows side created.
    """
    with tempfile.NamedTemporaryFile(mode="w", suffix=".p", delete=False,
                                     encoding="utf-8") as temp_file:
        temp_file.write(input_str)
        temp_filename = temp_file.name

    try:
        if use_wsl:
            command = ["wsl.exe", vampire_path, _to_wsl_path(temp_filename)]
        else:
            command = [vampire_path, temp_filename]
        result = subprocess.run(
            command,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
        return _is_entailed_output(result.stdout)
    except subprocess.TimeoutExpired:
        return False
    finally:
        try:
            os.unlink(temp_filename)
        except OSError:
            pass


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
        NotImplementedError: a formula is outside the first-order fragment
            (modal / second-order / Łukasiewicz / lambda), surfaced by
            ``to_tptp``.
    """
    vampire_input = _generate_vampire_input(premises, conclusion)
    return _run_vampire(vampire_input, vampire_path, timeout=timeout,
                        use_wsl=use_wsl)
