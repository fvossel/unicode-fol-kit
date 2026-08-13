"""nanoCoP-M as an opt-in modal backend with a MANDATORY cross-check.

nanoCoP-M (Jens Otten, http://leancop.de/nanocop-m/, GPL) is one of the
very few provers that decide FIRST-ORDER modal logic natively — with
explicit domain conditions (constant / cumulative / varying), which the
kit's own QML embedding can only approximate. That power comes with two
sharp edges this module manages instead of hiding:

1. **It is a Prolog program the user configures.** The shipped
   ``nanocopm.sh`` hard-codes LOGIC (d/t/s4/s5) and DOMAIN
   (const/cumul/vary) as shell variables and needs an ECLiPSe or
   SWI-Prolog install. This backend therefore never guesses an
   installation: discovery is ``$UFK_NANOCOP_CMD`` (the user's configured
   wrapper script; prefix ``wsl:`` for the WSL route) → ``nanocopm.sh`` on
   PATH → the same name inside WSL. The script prints which configuration
   actually ran (``… is a modal (s4/cumul) Theorem``) and this backend
   PARSES that back: if the caller requested ``logic=``/``domain=``
   options and the script's report disagrees, the verdict is an ERROR
   telling the user to reconfigure their script — never a silently wrong
   logic.
2. **The roadmap's mandatory cross-check.** Connection provers earn their
   keep exactly where other methods time out, so their claims must be
   independently checked (the kit granted nanoCoP-M opt-in status ONLY
   under this condition). Policy, asymmetric on purpose:

   * ``Theorem`` → the kit re-runs ``modal-tableau`` on the same problem.
     Agreement or an inconclusive tableau keeps PROVED (with the
     cross-check outcome in ``detail``); a tableau REFUTATION raises the
     soundness alarm as an ERROR verdict — two definitive answers may
     never disagree silently.
   * ``Non-Theorem`` → only a ``kripke-enum`` COUNTERMODEL turns it into
     REFUTED (then the countermodel is the certificate, carried in the
     verdict); without one the claim stays UNKNOWN/``incomplete`` with
     the Non-Theorem noted in ``detail``. First-order modal validity is
     undecidable, so a proof-search failure — even from the script's
     COMP=y "complete" strategy — is not a refutation certificate this
     kit will vouch for on its own.

Input syntax (from the shipped ReadMe, v2.0, verified): the problem file
contains ``f(<formula>).`` with ``~`` negation, ``#`` box, ``*`` diamond,
``,`` conjunction, ``;`` disjunction, ``=>``, ``<=>``, ``all X:`` /
``ex X:`` quantifiers; atoms are Prolog terms. Kit names map by
first-letter case flip (predicate ``P``→``p``, variable ``x``→``X``);
the mapping must be injective — ``P``/``p`` colliding on ``p`` refuses
loudly (the same discipline as the NXF exporter's collision check).
Fragment: Box/Diamond + classical connectives + ∀/∃ over
predicates/constants/variables. Everything else (Knows/temporal/deontic
operators, functions with clashing names, sorted nodes, …) is refused as
unsupported, never approximated.

Output contract (from ``nanocopm.sh``): exit 0 + ``… is a modal
(<logic>/<domain>) Theorem`` on proof; exit 1 + ``… Non-Theorem`` on
disproof (printed only by COMP=y strategy slots); exit 2 / ``Timeout`` on
budget exhaustion.
"""

import os
import re
import shutil
import subprocess
import tempfile
import time
from typing import Dict, List, Optional, Sequence, Tuple

from ..fol.nodes import (
    And, Atom, Box, Constant, Diamond, Function, Iff, Implies, Node, Not,
    Or, Quantifier, Variable,
)
from .protocol import ProverBackend, Verdict, PROVED, REFUTED, UNKNOWN, ERROR

__all__ = ["NanocopBackend", "to_nanocop", "nanocop_available"]

_RESULT_RE = re.compile(
    r"is (?:a )?modal \(([^)/]+)/([^)]+)\) (Theorem|Non-Theorem)")


class _NameMap:
    """Injective kit→Prolog name mapping with loud collision refusal."""

    def __init__(self):
        self._forward: Dict[Tuple[str, str], str] = {}
        self._taken: Dict[str, Tuple[str, str]] = {}

    def get(self, namespace: str, kit_name: str, prolog_name: str) -> str:
        key = (namespace, kit_name)
        if key in self._forward:
            return self._forward[key]
        owner = self._taken.get(prolog_name)
        if owner is not None and owner != key:
            raise NotImplementedError(
                f"nanocop: refusing to alias — kit {namespace} '{kit_name}' "
                f"and {owner[0]} '{owner[1]}' would both render as Prolog "
                f"name '{prolog_name}'.")
        self._forward[key] = prolog_name
        self._taken[prolog_name] = key
        return prolog_name


def _term(node: Node, names: _NameMap, bound: Dict[str, str]) -> str:
    cls = type(node).__name__
    if cls == "Variable":
        if node.name not in bound:
            raise ValueError(
                f"nanocop: free variable '{node.name}' — the formula must "
                "be closed.")
        return bound[node.name]
    if cls == "Constant":
        lowered = node.name[0].lower() + node.name[1:]
        return names.get("constant", node.name, lowered)
    if cls == "Function":
        head = names.get("function", node.name,
                         node.name[0].lower() + node.name[1:])
        args = ", ".join(_term(a, names, bound) for a in node.args)
        return f"{head}({args})"
    raise NotImplementedError(
        f"nanocop: term node {cls!r} is outside the supported fragment.")


def _formula(node: Node, names: _NameMap, bound: Dict[str, str]) -> str:
    cls = type(node).__name__
    if cls == "Atom":
        if node.predicate == "=":
            raise NotImplementedError(
                "nanocop: equality is not in the supported fragment "
                "(nanoCoP-M has no built-in equality handling).")
        head = names.get("predicate", node.predicate,
                         node.predicate[0].lower() + node.predicate[1:])
        if not node.args:
            return head
        args = ", ".join(_term(a, names, bound) for a in node.args)
        return f"{head}({args})"
    if cls == "Not":
        return f"(~ {_formula(node.formula, names, bound)})"
    if cls == "Box":
        return f"(# {_formula(node.formula, names, bound)})"
    if cls == "Diamond":
        return f"(* {_formula(node.formula, names, bound)})"
    if cls == "And":
        return (f"({_formula(node.left, names, bound)} , "
                f"{_formula(node.right, names, bound)})")
    if cls == "Or":
        return (f"({_formula(node.left, names, bound)} ; "
                f"{_formula(node.right, names, bound)})")
    if cls == "Implies":
        return (f"({_formula(node.left, names, bound)} => "
                f"{_formula(node.right, names, bound)})")
    if cls == "Iff":
        return (f"({_formula(node.left, names, bound)} <=> "
                f"{_formula(node.right, names, bound)})")
    if cls == "Quantifier":
        # Variables go through the SAME injective map as every other name
        # class (review-confirmed hole: kit 'x1' and 'X1' both case-flip to
        # Prolog 'X1', which Prolog's reader would silently unify into ONE
        # variable — corrupting the formula instead of refusing).
        upper = names.get("variable", node.variable.name,
                          node.variable.name[0].upper() + node.variable.name[1:])
        keyword = "all" if node.type in ("∀", "forall") else "ex"
        new_bound = dict(bound)
        new_bound[node.variable.name] = upper
        return f"({keyword} {upper}: {_formula(node.formula, names, new_bound)})"
    raise NotImplementedError(
        f"nanocop: formula node {cls!r} is outside the supported fragment "
        "(Box/Diamond + classical connectives + plain quantifiers only).")


def to_nanocop(formula: Node, premises: Sequence[Node] = ()) -> str:
    """Render ``premises ⊨ formula`` as a nanoCoP-M problem ``f(...).``.

    Premises fold into ``(∧ premises) => formula`` first (nanoCoP-M takes
    one validity question, not an axioms/conjecture split).
    """
    goal = formula
    premises = list(premises)
    if premises:
        conj = premises[0]
        for p in premises[1:]:
            conj = And(conj, p)
        goal = Implies(conj, formula)
    names = _NameMap()
    return f"f( {_formula(goal, names, {})} ).\n"


_DISCOVERY_CACHE: dict = {}


def _discover() -> Optional[Tuple[str, bool]]:
    """``(command, use_wsl)`` for the nanocopm wrapper, or ``None``.

    The env override is read fresh on every call (never cached), so setting
    ``$UFK_NANOCOP_CMD`` mid-process repoints immediately; only the
    PATH/WSL binary probes are cached.
    """
    override = os.environ.get("UFK_NANOCOP_CMD")
    if override:
        return ((override[4:], True) if override.startswith("wsl:")
                else (override, False))
    if "cmd" in _DISCOVERY_CACHE:
        return _DISCOVERY_CACHE["cmd"]
    resolved: Optional[Tuple[str, bool]] = None
    if shutil.which("nanocopm.sh"):
        resolved = ("nanocopm.sh", False)
    else:
        try:
            probe = subprocess.run(["wsl.exe", "which", "nanocopm.sh"],
                                   capture_output=True, text=True, timeout=20)
            path = probe.stdout.strip()
            if probe.returncode == 0 and path:
                resolved = (path, True)
        except (OSError, subprocess.TimeoutExpired):
            resolved = None
    _DISCOVERY_CACHE["cmd"] = resolved
    return resolved


def nanocop_available() -> bool:
    """Pure discovery (env → PATH → WSL); see the module docstring."""
    return _discover() is not None


def _run_nanocop(problem: str, command: str, use_wsl: bool,
                 timeout_s: int) -> Tuple[str, int]:
    """Write the problem file, run the wrapper, return ``(output, code)``."""
    from .eprover_backend import _to_wsl_path

    with tempfile.NamedTemporaryFile(mode="w", suffix=".ncp", delete=False,
                                     encoding="utf-8") as tmp:
        tmp.write(problem)
        path = tmp.name
    try:
        target = _to_wsl_path(path) if use_wsl else path
        cmd = (["wsl.exe", command, target, str(timeout_s)] if use_wsl
               else [command, target, str(timeout_s)])
        result = subprocess.run(cmd, capture_output=True, text=True,
                                timeout=timeout_s + 15)
        return (result.stdout or "") + (result.stderr or ""), result.returncode
    except subprocess.TimeoutExpired:
        return "", 2
    finally:
        try:
            os.unlink(path)
        except OSError:
            pass


class NanocopBackend(ProverBackend):
    """nanoCoP-M, opt-in, cross-checked (see the module docstring)."""

    name = "nanocop"
    logics = frozenset({"modal"})
    external = True

    def available(self) -> bool:
        return nanocop_available()

    def decide(self, formula: Node, premises: Sequence[Node] = (),
               timeout: int = 10000, **options) -> Verdict:
        from .protocol import BackendUnavailable

        logic = options.pop("logic", None)        # d | t | s4 | s5
        domain = options.pop("domain", None)      # const | cumul | vary

        found = _discover()
        if found is None:
            raise BackendUnavailable(
                "nanocop: no nanocopm.sh found — install nanoCoP-M "
                "(http://leancop.de/nanocop-m/, needs ECLiPSe or SWI-Prolog, "
                "configure LOGIC/DOMAIN in nanocopm.sh) and set "
                "$UFK_NANOCOP_CMD to the wrapper (prefix 'wsl:' for WSL).")
        command, use_wsl = found

        try:
            problem = to_nanocop(formula, premises)
        except (ValueError, NotImplementedError) as exc:
            return Verdict(UNKNOWN, self.name, reason="unsupported",
                           detail=str(exc))

        timeout_s = max(1, timeout // 1000)
        start = time.perf_counter()
        try:
            output, code = _run_nanocop(problem, command, use_wsl, timeout_s)
        except (OSError, RuntimeError) as exc:
            return Verdict(ERROR, self.name, reason="infra",
                           detail=f"{type(exc).__name__}: {exc}")
        elapsed = time.perf_counter() - start

        match = _RESULT_RE.search(output)
        if match is None:
            if code == 2 or "Timeout" in output:
                return Verdict(UNKNOWN, self.name, reason="timeout",
                               wall_time=elapsed)
            return Verdict(ERROR, self.name, reason="infra", wall_time=elapsed,
                           detail="no recognisable nanoCoP-M result line: "
                                  + output.strip()[-200:])
        ran_logic, ran_domain, result = match.groups()

        # The exit code is authoritative alongside the text (the script's
        # documented contract: 0=Theorem, 1=Non-Theorem, 2=timeout). A
        # result line left in the buffer of a run that ultimately exited 2
        # is stale, not an answer (review-reproduced); a code/text mismatch
        # is an infrastructure fault, never silently resolved either way.
        if code == 2:
            return Verdict(UNKNOWN, self.name, reason="timeout",
                           wall_time=elapsed,
                           detail="exit code 2 (timeout) despite a "
                                  f"'{result}' line in the buffer — the run "
                                  "did not complete; discarding the line.")
        expected_code = 0 if result == "Theorem" else 1
        if code != expected_code:
            return Verdict(ERROR, self.name, reason="infra", wall_time=elapsed,
                           detail=f"nanocopm.sh printed '{result}' but "
                                  f"exited {code} (contract: "
                                  f"{expected_code}) — refusing the answer.")

        # The script's own report is authoritative about what ran; a caller
        # who requested a specific logic/domain must not get an answer from
        # a differently-configured script.
        if logic is not None and logic != ran_logic:
            return Verdict(ERROR, self.name, reason="infra", wall_time=elapsed,
                           detail=f"requested logic={logic!r} but the "
                                  f"configured script ran {ran_logic!r} — "
                                  "edit LOGIC in your nanocopm.sh.")
        if domain is not None and domain != ran_domain:
            return Verdict(ERROR, self.name, reason="infra", wall_time=elapsed,
                           detail=f"requested domain={domain!r} but the "
                                  f"configured script ran {ran_domain!r} — "
                                  "edit DOMAIN in your nanocopm.sh.")

        frame = {"d": "D", "t": "T", "s4": "S4", "s5": "S5"}.get(ran_logic)
        provenance = f"nanoCoP-M ({ran_logic}/{ran_domain})"
        # The propositional cross-checkers treat Quantifier nodes as opaque
        # (modal-tableau) or unsupported (kripke-enum) — review-confirmed —
        # so quantified problems route through the QML embedding instead.
        quantified = any(type(n).__name__ in ("Quantifier", "SortedQuantifier")
                         for f in [formula, *premises] for n in f.walk())

        if result == "Theorem":
            if quantified:
                # qml is the K-frame embedding: a qml PROOF is valid in
                # every stronger frame (K ⊆ D/T/S4/S5 theorems), so it
                # CONFIRMS; a qml refutation is a K-countermodel that says
                # nothing against a D/T/S4/S5 theorem — never an alarm.
                check = self._cross_check("qml", formula, premises, None,
                                          timeout)
                agreement = ("confirmed (qml, K-frame proof implies "
                             f"{ran_logic})" if check is not None
                             and check.status == PROVED
                             else "inconclusive (qml)")
                return Verdict(PROVED, self.name, wall_time=elapsed,
                               detail=f"{provenance} Theorem; cross-check "
                                      f"{agreement}")
            check = self._cross_check("modal-tableau", formula, premises,
                                      frame, timeout)
            if check is not None and check.status == REFUTED:
                return Verdict(
                    ERROR, self.name, reason="infra", wall_time=elapsed,
                    detail=f"SOUNDNESS ALARM: {provenance} says Theorem but "
                           f"modal-tableau (frame {frame}) refutes it — "
                           "refusing to answer.")
            agreement = ("confirmed" if check is not None
                         and check.status == PROVED else "inconclusive")
            return Verdict(PROVED, self.name, wall_time=elapsed,
                           detail=f"{provenance} Theorem; cross-check "
                                  f"modal-tableau: {agreement}")

        # Non-Theorem: only an independent countermodel certifies REFUTED.
        if quantified:
            # kripke-enum has no quantified route (unsupported by its own
            # contract): the FO fragment has NO independent countermodel
            # source, so a quantified Non-Theorem is never vouched for.
            return Verdict(UNKNOWN, self.name, reason="incomplete",
                           wall_time=elapsed,
                           detail=f"{provenance} claims Non-Theorem; the "
                                  "kit has no independent FIRST-ORDER modal "
                                  "countermodel route to certify it — "
                                  "recorded, not vouched for.")
        check = self._cross_check("kripke-enum", formula, premises, frame,
                                  timeout)
        if check is not None and check.status == REFUTED:
            return Verdict(REFUTED, self.name, wall_time=elapsed,
                           countermodel=check.countermodel,
                           detail=f"{provenance} Non-Theorem; kripke-enum "
                                  "countermodel confirms")
        return Verdict(UNKNOWN, self.name, reason="incomplete",
                       wall_time=elapsed,
                       detail=f"{provenance} claims Non-Theorem, but no "
                              "independent countermodel was found — the "
                              "claim is recorded, not vouched for.")

    @staticmethod
    def _cross_check(backend_name: str, formula: Node,
                     premises: Sequence[Node], frame: Optional[str],
                     timeout: int):
        """Run the named kit backend on the same problem; None on any error.

        The cross-check is best-effort infrastructure: ITS failure must not
        mask nanoCoP-M's answer, only its definitive disagreement may.
        """
        from .protocol import get_backend

        try:
            kwargs = {"frame": frame} if frame else {}
            return get_backend(backend_name).decide(
                formula, list(premises), timeout=timeout, **kwargs)
        except Exception:                                  # noqa: BLE001
            return None
