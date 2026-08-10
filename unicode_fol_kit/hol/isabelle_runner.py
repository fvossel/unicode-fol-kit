r"""Run a **local Isabelle** to actually discharge the emitted shallow-embedding
theories — turning the :mod:`unicode_fol_kit.hol` exporters from *emit* into
*proven / refuted*.

The rest of the toolkit only *emits* HOL/Isabelle/THF problem files (see the
``hol`` package docstring): it is honest that first-order modal logic, FOL and
SOL are undecidable, so an emission is "a sound problem a prover *may* discharge".
This module is the **opt-in** other half: if a local Isabelle/HOL is installed, it
writes the emitted theory to a scratch session, invokes ``isabelle build``, and
reads the verdict off the build — a real proof, not a promise.

Decision procedure for modal validity (:func:`isabelle_decide_modal`)
---------------------------------------------------------------------
The shallow embedding is *faithful* to the Kripke evaluator
:func:`unicode_fol_kit.semantics.kripke.satisfies_modal`, so deciding the emitted
lemma decides the modal formula (for the chosen frame / domain regime):

1. **Prove** — emit ``lemma <goal>`` with a proof that brings the frame/domain
   axioms into scope and tries a battery of methods
   (``using <axioms> by (blast | force | fastforce | auto | meson … | metis …)``).
   If ``isabelle build`` exits 0, the lemma is a **theorem** ⇒ the formula is
   **VALID**.
2. **Refute** — otherwise emit the same lemma followed by
   ``nitpick[expect = genuine]``. Nitpick searches for a finite counter-model;
   ``expect = genuine`` makes the build **succeed iff a genuine counter-model is
   found**, so exit 0 here ⇒ the formula is **INVALID**. The verdict is certified by
   the exit code; for the propositional alethic fragment ``ModalVerdict.countermodel``
   then carries a concrete Kripke counter-model reconstructed from the toolkit's own
   evaluator (``isabelle build`` does not echo nitpick's model), and is ``None`` for
   fragments the bounded search does not cover — never weakening the verdict.
3. Otherwise the result is **UNKNOWN** (neither a battery proof nor a finite
   counter-model within the time/size budget — expected, since the logic is
   undecidable).

This is *sound* (Isabelle's kernel certifies the proof; nitpick reports only
*genuine* counter-models), and necessarily *incomplete*.

Honesty / soundness boundary
----------------------------
A VALID / INVALID verdict is only as meaningful as the embedding's faithfulness
to the chosen semantics. UNKNOWN is a real outcome, not a failure. The runner
never claims a decision it did not obtain from the prover.

Which logic a verdict is *about* is selected by the options that reach the
emitter, and each of them is forwarded to **every** theory the decision builds —
the prove theory, the proof battery, and the nitpick theory. That is not
tidiness: the two steps decide opposite questions, so an option that reached only
one of them would produce a verdict about a logic nobody asked for (a prove
theory missing an axiom degrades to UNKNOWN; a *nitpick* theory missing one
certifies a "genuine" counter-model outside the requested class, i.e. a false
INVALID). The options are ``frame`` / ``mode`` / ``systems`` / ``temporal_closure``
/ ``bridges`` for :func:`isabelle_decide_modal`, and ``centering`` for
:func:`isabelle_decide_counterfactual` — whose default ``"weak"`` matches
:func:`~unicode_fol_kit.semantics.conditional.cf_valid`, so the two routes decide
the same conditional logic unless told otherwise.

Platform support
----------------
**Linux and macOS are the primary path**: the ``isabelle`` binary is invoked
directly (``isabelle build -D <dir>``) with nothing platform-specific. **Windows**
is also supported — Isabelle ships its own Cygwin and its CLI is a Bash script, so
there the runner additionally routes the build through ``contrib/cygwin/bin/bash``,
translates the scratch path to a ``/cygdrive/...`` path, and (idempotently) sets the
execute bit on the launcher scripts (some installs ship them without it, which makes
the internal ``exec isabelle java`` fail with *Permission denied*). No install path
is ever hard-coded; installations are discovered generically (see below).

Locating Isabelle
-----------------
:func:`find_isabelle` looks, in order, at an explicit path, the env vars
``UFK_ISABELLE_HOME`` / ``ISABELLE_HOME``, ``isabelle`` on ``PATH``, and a light
scan of standard install locations. :func:`isabelle_available` is the cheap
predicate tests gate on (skip when no Isabelle is present).
"""

from __future__ import annotations

import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
import uuid
from dataclasses import dataclass, field
from typing import Iterable, List, Optional, Sequence, Tuple

from unicode_fol_kit.fol.nodes import Node
from unicode_fol_kit.hol.isabelle_modal import (
    isabelle_modal_theory, modal_axiom_names,
)

__all__ = [
    "IsabelleNotAvailable", "IsabelleInstall", "BuildResult",
    "ModalVerdict", "FolVerdict",
    "find_isabelle", "isabelle_available",
    "check_theory", "isabelle_decide_modal", "isabelle_decide_fol",
    "isabelle_decide_relevant",
    "DEFAULT_METHODS",
]

# Ordered so cheap, fail-fast methods run before the ones that can loop; the first
# alternative to close the goal wins. meson/metis take the axioms as explicit args.
DEFAULT_METHODS: Tuple[str, ...] = (
    "blast", "force", "fastforce", "auto", "meson", "metis",
)


class IsabelleNotAvailable(RuntimeError):
    """Raised when an Isabelle install is required but none could be located."""


# --------------------------------------------------------------------------- #
# Locating an Isabelle installation.
# --------------------------------------------------------------------------- #

_VERSION_RE = re.compile(r"Isabelle\d{4}(?:-\d+)?", re.I)


@dataclass(frozen=True)
class IsabelleInstall:
    """A located Isabelle/HOL installation and how to invoke its CLI."""

    home: str                       # ISABELLE_HOME (the install directory)
    is_windows: bool                # invoke via the bundled Cygwin bash?
    isabelle_exe: str               # POSIX: path to bin/isabelle (direct)
    cygwin_bash: Optional[str] = None   # Windows: contrib/cygwin/bin/bash.exe
    version: Optional[str] = None

    def __str__(self) -> str:
        return f"Isabelle({self.version or '?'} at {self.home})"


def _validate_install(home: Optional[str]) -> Optional[IsabelleInstall]:
    """Turn a candidate ``ISABELLE_HOME`` into an :class:`IsabelleInstall` or None."""
    if not home:
        return None
    home = os.path.abspath(home)
    if not os.path.isdir(home):
        return None
    launcher = os.path.join(home, "bin", "isabelle")
    if not os.path.isfile(launcher):
        return None
    m = _VERSION_RE.search(os.path.basename(home.rstrip("\\/")))
    version = m.group(0) if m else None
    if os.name == "nt":
        bash = os.path.join(home, "contrib", "cygwin", "bin", "bash.exe")
        if not os.path.isfile(bash):
            return None
        return IsabelleInstall(home=home, is_windows=True, isabelle_exe=launcher,
                               cygwin_bash=bash, version=version)
    return IsabelleInstall(home=home, is_windows=False, isabelle_exe=launcher,
                           version=version)


def _scan_standard_locations() -> List[str]:
    """A light, best-effort scan for ``Isabelle*`` install dirs (no deep recursion)."""
    out: List[str] = []
    try:
        if os.name == "nt":
            import glob
            roots = [r"C:\Program Files", r"C:\Program Files (x86)"]
            drives = [f"{d}:\\" for d in "CDEFG" if os.path.isdir(f"{d}:\\")]
            roots += drives
            patterns: List[str] = []
            for r in roots:
                patterns.append(os.path.join(r, "Isabelle*"))
                patterns.append(os.path.join(r, "*", "Isabelle*"))  # an Isabelle* dir one level down
            for pat in patterns:
                try:
                    out += [p for p in glob.glob(pat) if os.path.isdir(p)]
                except OSError:
                    continue
        else:
            import glob
            home = os.path.expanduser("~")
            for r in ("/usr/local", "/opt", home, os.path.join(home, ".local")):
                try:
                    out += [p for p in glob.glob(os.path.join(r, "Isabelle*"))
                            if os.path.isdir(p)]
                except OSError:
                    continue
    except Exception:
        return out
    # Prefer the highest version string (lexicographic on Isabelleyyyy-n is fine).
    out.sort(reverse=True)
    return out


_FIND_CACHE: dict = {}


def find_isabelle(isabelle_home: Optional[str] = None,
                  *, use_cache: bool = True) -> Optional[IsabelleInstall]:
    """Locate an Isabelle installation, or return ``None`` if none is found.

    Search order: ``isabelle_home`` argument → env ``UFK_ISABELLE_HOME`` → env
    ``ISABELLE_HOME`` → ``isabelle`` on ``PATH`` → a light scan of standard install
    locations. The result is cached (keyed by the explicit argument); pass
    ``use_cache=False`` to force a fresh lookup.
    """
    key = isabelle_home or ""
    if use_cache and key in _FIND_CACHE:
        return _FIND_CACHE[key]

    candidates: List[str] = []
    if isabelle_home:
        candidates.append(isabelle_home)
    for var in ("UFK_ISABELLE_HOME", "ISABELLE_HOME"):
        v = os.environ.get(var)
        if v:
            candidates.append(v)
    exe = shutil.which("isabelle")
    if exe:
        candidates.append(os.path.dirname(os.path.dirname(os.path.abspath(exe))))
    candidates += _scan_standard_locations()

    found: Optional[IsabelleInstall] = None
    seen = set()
    for home in candidates:
        ah = os.path.abspath(home) if home else home
        if ah in seen:
            continue
        seen.add(ah)
        inst = _validate_install(home)
        if inst:
            found = inst
            break
    if use_cache:
        _FIND_CACHE[key] = found
    return found


def isabelle_available(isabelle_home: Optional[str] = None) -> bool:
    """``True`` iff an Isabelle installation can be located (cheap; cached)."""
    return find_isabelle(isabelle_home) is not None


# --------------------------------------------------------------------------- #
# Invoking ``isabelle build`` on a scratch session.
# --------------------------------------------------------------------------- #

def _cygpath(win_path: str) -> str:
    r"""Translate a Windows path to a Cygwin ``/cygdrive/<d>/...`` path.

    Parses the drive letter directly rather than via ``os.path`` (whose drive
    handling differs on POSIX — ``splitdrive`` ignores ``C:`` and ``abspath``
    prepends the cwd), so the function is correct and testable on every platform,
    though it is only *used* on Windows. Inputs from the runner are already absolute.
    """
    p = win_path.replace("\\", "/")
    if len(p) >= 2 and p[0].isalpha() and p[1] == ":":
        return "/cygdrive/" + p[0].lower() + p[2:]
    return p


def _run_build(install: IsabelleInstall, session_dir: str,
               wall_timeout: float) -> Tuple[int, str]:
    """Run ``isabelle build -D <session_dir>``; return (exit_code, combined_output)."""
    if not install.is_windows:
        # Linux / macOS — the primary path: invoke the isabelle binary directly.
        argv = [install.isabelle_exe, "build", "-D", session_dir]
        env = dict(os.environ)
    else:
        # Windows: route through Isabelle's bundled Cygwin bash. One bash -c puts bin
        # on PATH, ensures the launcher scripts are executable (idempotent; some
        # installs ship them without the bit), then builds the /cygdrive-translated dir.
        cyg_home = _cygpath(install.home)
        cyg_dir = _cygpath(session_dir)
        script = (
            f'I="{cyg_home}"\n'
            f'export PATH="$I/bin:$PATH"\n'
            f'chmod -R u+x "$I/bin" "$I/lib/Tools" "$I/lib/scripts" 2>/dev/null\n'
            f'isabelle build -D "{cyg_dir}"\n'
        )
        argv = [install.cygwin_bash, "--login", "-c", script]
        env = dict(os.environ, CHERE_INVOKING="true", LANG="en_US.UTF-8")
    try:
        proc = subprocess.run(
            argv, capture_output=True, text=True, encoding="utf-8",
            errors="replace", env=env, timeout=wall_timeout,
        )
    except subprocess.TimeoutExpired as e:
        out = (e.stdout or "") + (e.stderr or "")
        if isinstance(out, bytes):
            out = out.decode("utf-8", "replace")
        return 124, out + f"\n[runner] wall-clock timeout after {wall_timeout}s\n"
    return proc.returncode, (proc.stdout or "") + (proc.stderr or "")


@dataclass
class BuildResult:
    """Outcome of building one scratch theory with ``isabelle build``."""

    ok: bool                # exit code == 0 (every lemma in the theory discharged)
    exit_code: int
    output: str             # combined stdout+stderr of the build
    theory_name: str
    session: str
    elapsed: float

    def __bool__(self) -> bool:
        return self.ok


def check_theory(theory_text: str, theory_name: str, *,
                 install: Optional[IsabelleInstall] = None,
                 session: Optional[str] = None,
                 session_timeout: int = 120,
                 wall_timeout: Optional[float] = None,
                 keep: bool = False) -> BuildResult:
    """Build one self-contained Isabelle theory and report whether it loads/proves.

    Writes ``<theory_name>.thy`` plus a ``ROOT`` (``session ... = HOL + options
    [timeout] theories <theory_name>``) into a scratch directory and runs
    ``isabelle build`` on it. ``ok`` is ``True`` iff the build exits 0 — i.e. every
    proof in the theory was discharged by Isabelle's kernel.

    Args:
        theory_text: the full ``theory <theory_name> ... end`` text. Its declared
            theory name MUST equal ``theory_name``.
        theory_name: the theory / file name (a valid Isabelle identifier).
        install: an :class:`IsabelleInstall`; located via :func:`find_isabelle`
            when ``None``.
        session: the build session name (default ``"S_" + theory_name``).
        session_timeout: per-session Isabelle ``timeout`` option, in seconds.
        wall_timeout: hard subprocess timeout; defaults to ``session_timeout + 180``
            to cover JVM startup + image load.
        keep: keep the scratch directory (for debugging) instead of deleting it.

    Raises:
        IsabelleNotAvailable: if no Isabelle installation can be located.
    """
    install = install or find_isabelle()
    if install is None:
        raise IsabelleNotAvailable(
            "No Isabelle installation found. Set UFK_ISABELLE_HOME (or ISABELLE_HOME) "
            "to the install directory, or put `isabelle` on PATH.")
    session = session or ("S_" + theory_name)
    if wall_timeout is None:
        wall_timeout = float(session_timeout) + 180.0

    work = tempfile.mkdtemp(prefix="ufk_isa_")
    try:
        with open(os.path.join(work, theory_name + ".thy"), "w",
                  encoding="utf-8") as f:
            f.write(theory_text)
        root = (f'session "{session}" = HOL +\n'
                f'  options [timeout = {int(session_timeout)}]\n'
                f'  theories\n    {theory_name}\n')
        with open(os.path.join(work, "ROOT"), "w", encoding="utf-8") as f:
            f.write(root)
        t0 = time.perf_counter()
        code, output = _run_build(install, work, wall_timeout)
        elapsed = time.perf_counter() - t0
        return BuildResult(ok=(code == 0), exit_code=code, output=output,
                           theory_name=theory_name, session=session,
                           elapsed=elapsed)
    finally:
        if not keep:
            shutil.rmtree(work, ignore_errors=True)


# --------------------------------------------------------------------------- #
# Deciding modal validity through Isabelle.
# --------------------------------------------------------------------------- #

VALID = "valid"
INVALID = "invalid"
UNKNOWN = "unknown"

_NITPICK_CTEX_RE = re.compile(
    r"Nitpick found a (?:genuine )?counterexample.*", re.S)

# Signatures of an INFRASTRUCTURE failure (a broken theory or a broken environment),
# as opposed to an honest "no proof / no counter-model". A non-zero build that matches
# one of these is surfaced on ModalVerdict.infra_error so an UNKNOWN is not silently
# mistaken for benign incompleteness. This never changes the verdict — both decisive
# verdicts require an exit-0 build, so an infra failure can only land on UNKNOWN, the
# conservative side; this just makes the cause visible.
_INFRA_ERROR_RE = re.compile(
    r"Outer syntax error|Inner syntax error|Type unification failed|Bad name|"
    r"Malformed|Undefined command|Undefined type|Duplicate constant|"
    r"java\.lang\.\w*(?:OutOfMemoryError|Error)|Permission denied|"
    r"wall-clock timeout|No such file")


def _infra_error(*outputs: str) -> Optional[str]:
    """Return the first infrastructure-error signature found in the build outputs."""
    for out in outputs:
        m = _INFRA_ERROR_RE.search(out or "")
        if m:
            return m.group(0)
    return None


@dataclass
class ModalVerdict:
    """Result of deciding a modal formula's validity through Isabelle.

    ``status`` is one of ``"valid"`` (a battery proof closed the lemma),
    ``"invalid"`` (nitpick found a genuine counter-model), or ``"unknown"``
    (neither, within budget). Truthiness follows validity. On an ``"unknown"`` result,
    ``infra_error`` is set to a short signature when a build failed for an
    infrastructure reason (syntax/JVM/timeout/…) rather than honest incompleteness —
    it never changes the status (an infra failure can only land on UNKNOWN).
    """

    status: str
    frame: str
    mode: str
    method: Optional[str] = None          # the proof family that closed it (when valid)
    countermodel: Optional[str] = None    # for an INVALID alethic-propositional formula, a concrete
                                          # Kripke counter-model from the toolkit's evaluator (isabelle
                                          # build does not echo nitpick's model); None for fragments the
                                          # bounded search does not cover — verdict still certified
    prove_output: str = ""
    refute_output: str = ""
    prove_elapsed: float = 0.0
    refute_elapsed: float = 0.0
    infra_error: Optional[str] = None     # set on UNKNOWN when a build failed for an
                                          # infrastructure reason (syntax/JVM/timeout/…),
                                          # not honest incompleteness; never affects status

    @property
    def is_valid(self) -> bool:
        return self.status == VALID

    @property
    def is_invalid(self) -> bool:
        return self.status == INVALID

    @property
    def is_unknown(self) -> bool:
        return self.status == UNKNOWN

    def __bool__(self) -> bool:
        return self.status == VALID

    def __str__(self) -> str:
        extra = ""
        if self.status == VALID and self.method:
            extra = f" (by {self.method})"
        return f"ModalVerdict[{self.status}{extra}, frame={self.frame}, mode={self.mode}]"


# Frame conditions on the alethic relation r (mirror the emitter's _FRAMES).
_FRAME_CONDS = {
    "K": (), "T": ("refl",), "S4": ("refl", "trans"),
    "S5": ("refl", "trans", "sym"), "KD": ("serial",),
    "KD45": ("serial", "trans", "eucl"),
}

# Node types of the purely propositional ALETHIC fragment the bounded countermodel
# search can exhibit a witness for (no quantifiers / agents / deontic / temporal).
_ALETHIC_OK = ("Atom", "Not", "And", "Or", "Xor", "Implies", "Iff", "Box", "Diamond")


def _is_alethic_propositional(formula: Node) -> bool:
    """True iff ``formula`` is Box/Diamond + connectives over GROUND atoms only."""
    from unicode_fol_kit.fol.nodes import Variable
    for node in formula.walk():
        if type(node).__name__ not in _ALETHIC_OK and not isinstance(node, Variable):
            # allow the ground arguments of an atom (Constant/Number/Function), but a
            # free/bound Variable means it is not propositional.
            if type(node).__name__ in ("Constant", "Number", "Function"):
                continue
            return False
        if isinstance(node, Variable):
            return False
    return True


def _frame_ok(worlds, rel, conds) -> bool:
    if "refl" in conds and not all((w, w) in rel for w in worlds):
        return False
    if "trans" in conds and any((a, b) in rel and (b, c) in rel and (a, c) not in rel
                                for a in worlds for b in worlds for c in worlds):
        return False
    if "sym" in conds and any((a, b) in rel and (b, a) not in rel
                              for a in worlds for b in worlds):
        return False
    if "serial" in conds and not all(any((w, v) in rel for v in worlds) for w in worlds):
        return False
    if "eucl" in conds and any((a, b) in rel and (a, c) in rel and (b, c) not in rel
                               for a in worlds for b in worlds for c in worlds):
        return False
    return True


def _find_alethic_countermodel(formula: Node, frame: str,
                               max_worlds: int = 4) -> Optional[str]:
    """A concrete Kripke counter-model to ``formula`` over ``frame``, as a readable
    string — or ``None`` if the formula is outside the propositional alethic fragment
    or no counter-model exists within ``max_worlds``.

    Isabelle/nitpick certifies the INVALID verdict; this exhibits a witness from the
    toolkit's own evaluator (``isabelle build`` does not echo nitpick's model). Bounded
    brute force over the frame's relations and valuations, decided by ``satisfies_modal``.
    """
    if frame not in _FRAME_CONDS or not _is_alethic_propositional(formula):
        return None
    from itertools import product
    from unicode_fol_kit.fol.nodes import Atom
    from unicode_fol_kit.semantics.kripke import KripkeModel, satisfies_modal

    conds = _FRAME_CONDS[frame]
    keys = sorted({n.to_unicode_str() for n in formula.walk() if isinstance(n, Atom)})
    for n in range(1, max_worlds + 1):
        worlds = list(range(n))
        edges = [(i, j) for i in worlds for j in worlds]
        for mask in product((False, True), repeat=len(edges)):
            rel = frozenset(e for e, inc in zip(edges, mask) if inc)
            if not _frame_ok(worlds, rel, conds):
                continue
            for bits in product((False, True), repeat=n * len(keys)):
                val, idx = {}, 0
                for w in worlds:
                    cell = set()
                    for k in keys:
                        if bits[idx]:
                            cell.add(k)
                        idx += 1
                    val[w] = cell
                model = KripkeModel(worlds, {"alethic": rel}, val)
                bad = [w for w in worlds if not satisfies_modal(formula, model, w)]
                if bad:
                    rels = "{" + ", ".join(f"{a}->{b}" for (a, b) in sorted(rel)) + "}"
                    vals = ", ".join(f"{w}:{{{', '.join(sorted(val[w])) or '-'}}}"
                                     for w in worlds)
                    return (f"Kripke counter-model (frame {frame}, {n} world(s)): "
                            f"worlds={{{', '.join(map(str, worlds))}}}, r={rels}, "
                            f"valuation=[{vals}]; formula is false at world {bad[0]}")
    return None


def _battery_proof(axiom_ids: Sequence[str], methods: Sequence[str]) -> str:
    """Build a ``using <axioms> by (m1 | m2 | ...)`` proof block (the prove step)."""
    alts: List[str] = []
    facts = (" " + " ".join(axiom_ids)) if axiom_ids else ""
    for m in methods:
        if m in ("meson", "metis"):
            alts.append(m + facts)          # accept the axioms as explicit facts
        elif m == "smt":
            alts.append("(smt (verit))")
        else:
            alts.append(m)
    proof = ""
    if axiom_ids:
        proof += "  using " + " ".join(axiom_ids) + "\n"
    proof += "  by (" + " | ".join(alts) + ")"
    return proof


def isabelle_decide_modal(
    formula: Node, *,
    frame: str = "K",
    mode: str = "constant",
    temporal_closure: bool = True,
    systems: Optional[dict] = None,
    bridges: Optional[Iterable[str]] = None,
    methods: Sequence[str] = DEFAULT_METHODS,
    refute: bool = True,
    card: str = "1-4",
    prove_timeout: int = 60,
    refute_timeout: int = 60,
    install: Optional[IsabelleInstall] = None,
) -> ModalVerdict:
    """Decide a modal formula's validity by running a local Isabelle.

    Emits the Benzmüller shallow embedding of ``formula``
    (:func:`~unicode_fol_kit.hol.isabelle_modal.isabelle_modal_theory`, faithful to
    :func:`~unicode_fol_kit.semantics.kripke.satisfies_modal`) and:

    1. tries a proof battery — exit 0 ⇒ :data:`VALID`;
    2. otherwise (``refute``) runs ``nitpick[expect = genuine]`` — exit 0 ⇒
       :data:`INVALID` (certified by the exit code; for the propositional alethic
       fragment ``countermodel`` carries a concrete Kripke model from the toolkit's
       evaluator, else ``None``);
    3. otherwise :data:`UNKNOWN`.

    Args:
        formula: the modal AST node.
        frame: alethic frame system (K/T/S4/S5/KD/KD45) — fixes the axioms on ``r``.
        mode: object-quantifier domain regime (constant/possibilist/varying/…).
        temporal_closure: constrain the temporal relation to refl+trans (henceforth).
        systems: optional per-family frame systems for the agent-indexed relations
            (``{"epistemic": "S5", "doxastic": "KD45", "assertive"/"bouletic": …}``),
            passed through to the emitter — so e.g. factivity ``K_a P → P`` is
            provable under ``{"epistemic": "T"}``.
        bridges: optional CROSS-family bridge names from
            :data:`~unicode_fol_kit.hol.isabelle_modal.BRIDGES`
            (``knowledge_implies_belief`` / ``sincerity`` / ``ought_implies_can``),
            off by default. Threading this through is load-bearing on BOTH steps,
            not only on the prove step: the prove theory needs the axiom *and* its
            name in the ``using`` list (an ``axiomatization`` fact is not in the
            default claset), and the nitpick theory needs the same axiom or nitpick
            would happily build a model violating the bridge and certify a
            **false INVALID** for a formula that is valid over the requested class.
            ``ValueError`` when a requested bridge's partner family does not occur
            in ``formula`` (see
            :func:`~unicode_fol_kit.hol.isabelle_modal._bridge_axioms`).
        methods: proof methods tried, in order, as a ``by (… | …)`` battery.
        refute: also run nitpick to certify INVALID when the proof battery fails.
        card: nitpick cardinality range for the world type ``i`` (e.g. ``"1-4"``).
        prove_timeout / refute_timeout: per-session Isabelle timeouts (seconds).
        install: an :class:`IsabelleInstall`; located via :func:`find_isabelle` when
            ``None``.

    Returns:
        A :class:`ModalVerdict`.

    Raises:
        IsabelleNotAvailable: if no Isabelle installation can be located.
        ValueError / NotImplementedError: propagated from the emitter for an
            unsupported frame/mode/operator (e.g. ``Until``).
    """
    install = install or find_isabelle()
    if install is None:
        raise IsabelleNotAvailable(
            "No Isabelle installation found. Set UFK_ISABELLE_HOME (or ISABELLE_HOME) "
            "to the install directory, or put `isabelle` on PATH.")

    # An unknown bridge name (or a bridge whose partner family is absent) is a
    # ValueError from the emitter; raising it here, before the first build, keeps a
    # typo from costing a JVM start — and every call below passes the SAME bridges,
    # so the axiom list, the prove theory and the nitpick theory cannot disagree
    # about which logic is being decided.
    axiom_ids = modal_axiom_names(formula, mode=mode, frame=frame,
                                  temporal_closure=temporal_closure, systems=systems,
                                  bridges=bridges)

    # --- step 1: prove ---------------------------------------------------- #
    tok = "G" + uuid.uuid4().hex[:8]
    prove_proof = _battery_proof(axiom_ids, methods)
    prove_thy = isabelle_modal_theory(
        formula, mode=mode, frame=frame, tactic="oops", theory_name=tok,
        temporal_closure=temporal_closure, proof=prove_proof, systems=systems,
        bridges=bridges)
    r1 = check_theory(prove_thy, tok, install=install,
                      session_timeout=prove_timeout)
    if r1.ok:
        return ModalVerdict(status=VALID, frame=frame, mode=mode,
                            method="prove-battery", prove_output=r1.output,
                            prove_elapsed=r1.elapsed)

    # --- step 2: refute (nitpick) ----------------------------------------- #
    refute_output = ""
    refute_elapsed = 0.0
    if refute:
        tok2 = "G" + uuid.uuid4().hex[:8]
        nit_proof = (f"  nitpick[card i = {card}, timeout = {int(refute_timeout)}, "
                     f"expect = genuine]\n  oops")
        # temporal_def=True: when Always/Eventually co-occur with Next, define
        # t = rtranclp n so nitpick can construct the closure and actually refute a
        # non-theorem of the temporal fragment (the prove theory above keeps the
        # axiom form, which the battery needs — both encode t = n**).
        nit_thy = isabelle_modal_theory(
            formula, mode=mode, frame=frame, tactic="oops", theory_name=tok2,
            temporal_closure=temporal_closure, proof=nit_proof, temporal_def=True,
            systems=systems, bridges=bridges)
        # nitpick can use most of the session budget; give the wall clock headroom.
        r2 = check_theory(nit_thy, tok2, install=install,
                          session_timeout=refute_timeout + 30,
                          wall_timeout=float(refute_timeout) + 240.0)
        refute_output = r2.output
        refute_elapsed = r2.elapsed
        if r2.ok:
            m = _NITPICK_CTEX_RE.search(r2.output)
            ctex = m.group(0).strip() if m else None
            if ctex is None and not bridges:
                # isabelle build does not echo nitpick's model; exhibit a witness from
                # the toolkit's own evaluator for the propositional alethic fragment.
                # Skipped under bridges=: the evaluator has no notion of a cross-family
                # frame condition, so its witness would not be checked against the
                # requested class. (Today this is belt-and-braces — a bridge requires
                # its partner family to OCCUR, and every bridge has a non-alethic
                # family, so _is_alethic_propositional already rejects such a formula —
                # but the guard states the invariant instead of relying on it.)
                ctex = _find_alethic_countermodel(formula, frame)
            return ModalVerdict(status=INVALID, frame=frame, mode=mode,
                                countermodel=ctex, prove_output=r1.output,
                                refute_output=refute_output,
                                prove_elapsed=r1.elapsed,
                                refute_elapsed=refute_elapsed)

    return ModalVerdict(status=UNKNOWN, frame=frame, mode=mode,
                        prove_output=r1.output, refute_output=refute_output,
                        prove_elapsed=r1.elapsed, refute_elapsed=refute_elapsed,
                        infra_error=_infra_error(r1.output, refute_output))


# --------------------------------------------------------------------------- #
# Deciding classical FOL / MSFOL through Isabelle.
# --------------------------------------------------------------------------- #

@dataclass
class FolVerdict:
    """Result of deciding a classical FOL formula's validity through Isabelle.

    Same VALID / INVALID / UNKNOWN scheme as :class:`ModalVerdict` (no frame/mode).
    Note that FOL is only *semi-decidable*, so UNKNOWN is common and expected; and
    equality ``=`` / ``≠`` is the **uninterpreted** predicate ``feq`` / ``fneq`` of
    :func:`~unicode_fol_kit.hol.classical.to_isabelle_fol` (no equality axioms are
    assumed), so e.g. ``∀x. x = x`` is *not* VALID here.
    """

    status: str
    method: Optional[str] = None
    countermodel: Optional[str] = None    # nitpick text if surfaced (usually None; verdict certified)
    prove_output: str = ""
    refute_output: str = ""
    prove_elapsed: float = 0.0
    refute_elapsed: float = 0.0
    infra_error: Optional[str] = None

    @property
    def is_valid(self) -> bool:
        return self.status == VALID

    @property
    def is_invalid(self) -> bool:
        return self.status == INVALID

    @property
    def is_unknown(self) -> bool:
        return self.status == UNKNOWN

    def __bool__(self) -> bool:
        return self.status == VALID

    def __str__(self) -> str:
        extra = f" (by {self.method})" if self.status == VALID and self.method else ""
        return f"FolVerdict[{self.status}{extra}]"


def isabelle_decide_fol(
    formula: Node, *,
    msfol: bool = False,
    methods: Sequence[str] = DEFAULT_METHODS,
    refute: bool = True,
    card: str = "1-4",
    prove_timeout: int = 60,
    refute_timeout: int = 60,
    install: Optional[IsabelleInstall] = None,
) -> FolVerdict:
    """Decide a classical **FOL** (or MSFOL) formula's validity by running Isabelle.

    Emits the uninterpreted-signature embedding
    (:func:`~unicode_fol_kit.hol.classical.to_isabelle_fol`, or ``to_isabelle_msfol``
    when ``msfol=True``) and, exactly like :func:`isabelle_decide_modal`:

    1. tries a proof battery — exit 0 ⇒ :data:`VALID`;
    2. otherwise (``refute``) runs ``nitpick[expect = genuine]`` over the individual
       type ``i`` — exit 0 ⇒ :data:`INVALID`;
    3. otherwise :data:`UNKNOWN` (common — FOL is only semi-decidable).

    Sound (Isabelle's kernel certifies the proof; nitpick reports only genuine finite
    counter-models) and necessarily incomplete. Equality is uninterpreted (see
    :class:`FolVerdict`).

    Args:
        formula: the FOL AST node.
        msfol: emit the many-sorted embedding (sorts relativised to guard predicates)
            instead of plain FOL.
        methods / refute / card / prove_timeout / refute_timeout / install: as for
            :func:`isabelle_decide_modal` (``card`` bounds the individual type ``i``).

    Raises:
        IsabelleNotAvailable: if no Isabelle installation can be located.
    """
    install = install or find_isabelle()
    if install is None:
        raise IsabelleNotAvailable(
            "No Isabelle installation found. Set UFK_ISABELLE_HOME (or ISABELLE_HOME) "
            "to the install directory, or put `isabelle` on PATH.")
    from unicode_fol_kit.hol.classical import to_isabelle_fol, to_isabelle_msfol
    emit = to_isabelle_msfol if msfol else to_isabelle_fol

    # --- step 1: prove ---------------------------------------------------- #
    tok = "G" + uuid.uuid4().hex[:8]
    prove_proof = _battery_proof([], methods).lstrip()   # no axioms in the FOL embedding
    prove_thy = emit(formula, theory_name=tok, proof=prove_proof)
    r1 = check_theory(prove_thy, tok, install=install, session_timeout=prove_timeout)
    if r1.ok:
        return FolVerdict(status=VALID, method="prove-battery",
                          prove_output=r1.output, prove_elapsed=r1.elapsed)

    # --- step 2: refute (nitpick) ----------------------------------------- #
    refute_output = ""
    refute_elapsed = 0.0
    if refute:
        tok2 = "G" + uuid.uuid4().hex[:8]
        nit_proof = (f"nitpick[card i = {card}, timeout = {int(refute_timeout)}, "
                     f"expect = genuine]\n  oops")
        nit_thy = emit(formula, theory_name=tok2, proof=nit_proof)
        r2 = check_theory(nit_thy, tok2, install=install,
                          session_timeout=refute_timeout + 30,
                          wall_timeout=float(refute_timeout) + 240.0)
        refute_output = r2.output
        refute_elapsed = r2.elapsed
        if r2.ok:
            m = _NITPICK_CTEX_RE.search(r2.output)
            return FolVerdict(status=INVALID,
                              countermodel=(m.group(0).strip() if m else None),
                              prove_output=r1.output, refute_output=refute_output,
                              prove_elapsed=r1.elapsed, refute_elapsed=refute_elapsed)

    return FolVerdict(status=UNKNOWN, prove_output=r1.output,
                      refute_output=refute_output, prove_elapsed=r1.elapsed,
                      refute_elapsed=refute_elapsed,
                      infra_error=_infra_error(r1.output, refute_output))


# --------------------------------------------------------------------------- #
# Deciding counterfactual (Lewis sphere) validity through Isabelle.
# --------------------------------------------------------------------------- #

def isabelle_decide_counterfactual(
    formula: Node, *,
    centering: str = "weak",
    methods: Optional[Sequence[str]] = None,
    refute: bool = True,
    card: str = "1-3",
    prove_timeout: int = 60,
    refute_timeout: int = 60,
    install: Optional[IsabelleInstall] = None,
) -> FolVerdict:
    """Decide a counterfactual formula's validity by running a local Isabelle.

    Emits the Lewis sphere embedding
    (:func:`~unicode_fol_kit.hol.isabelle_conditional.isabelle_conditional_theory`,
    the same truth condition
    :func:`~unicode_fol_kit.semantics.conditional.cf_satisfies` evaluates) and,
    exactly like :func:`isabelle_decide_fol`:

    1. tries a proof battery — exit 0 ⇒ :data:`VALID` over every **nested** sphere
       system meeting the requested ``centering`` level;
    2. otherwise (``refute``) runs ``nitpick[expect = genuine]`` over the world
       type ``w`` — exit 0 ⇒ :data:`INVALID` (nesting and centering are *premises*
       of the goal, so nitpick constructs the sphere system itself and certifies
       the model as genuine);
    3. otherwise :data:`UNKNOWN`.

    Args:
        formula: the AST node — the propositional connectives plus ``□→`` / ``◇→``
            (``Would`` / ``Might``).
        centering: which sphere class to decide over — ``"none"`` (Lewis **V**,
            nesting only) / ``"weak"`` (**VW**, the default) / ``"strong"``
            (**VC**). The default matches
            :func:`~unicode_fol_kit.semantics.conditional.cf_valid`'s, so this
            route and the internal evaluator answer the same question unless told
            otherwise. It is threaded to **all three** emission sites — the prove
            theory, the proof battery's ``unfolding`` list, and the nitpick theory:
            a partial forward would silently decide a different logic than
            requested (a premise the battery cannot unfold degrades to UNKNOWN, and
            a nitpick theory carrying the wrong premise can certify a counter-model
            that is not in the requested class at all).
        methods: proof battery; defaults to the embedding's own
            :data:`~unicode_fol_kit.hol.isabelle_conditional.DEFAULT_METHODS`
            (verit-first — see there for why the order matters). Built at
            ``centering`` here, so a caller-supplied battery need not repeat it.
        refute / card / prove_timeout / refute_timeout / install: as for
            :func:`isabelle_decide_fol` (``card`` bounds the world type ``w``).

    Note:
        ``card`` here and ``max_worlds`` in
        :func:`~unicode_fol_kit.semantics.conditional.cf_countermodel` bound
        different searches (nitpick's finite-model search over the world type vs.
        the Python enumeration of sphere chains), so equal numbers do not mean
        equal coverage. The default *numbers* do coincide at the centered levels —
        ``card="1-3"`` here against
        :data:`~unicode_fol_kit.semantics.conditional.DEFAULT_MAX_WORLDS`'s 3 —
        which is why the schemas whose only countermodels have three worlds
        (conditional excluded middle at VC, importation at VW) are now refuted by
        both routes rather than only this one.

    Raises:
        IsabelleNotAvailable: if no Isabelle installation can be located.
        ValueError: on an unknown ``centering`` level — checked *before* the
            install lookup, so a typo is reported as a typo on a machine with no
            Isabelle rather than masked by ``IsabelleNotAvailable``.
        NotImplementedError: propagated from the emitter on a quantifier or a
            modal operator (□/◇ range over an accessibility relation, not a
            similarity ordering).
    """
    from unicode_fol_kit.hol.isabelle_conditional import (
        isabelle_conditional_theory, battery_proof, nitpick_proof,
        DEFAULT_METHODS as _CF_METHODS)
    from unicode_fol_kit.semantics.conditional import check_centering

    check_centering(centering)
    install = install or find_isabelle()
    if install is None:
        raise IsabelleNotAvailable(
            "No Isabelle installation found. Set UFK_ISABELLE_HOME (or ISABELLE_HOME) "
            "to the install directory, or put `isabelle` on PATH.")

    # --- step 1: prove ---------------------------------------------------- #
    tok = "G" + uuid.uuid4().hex[:8]
    prove_thy = isabelle_conditional_theory(
        formula, theory_name=tok, centering=centering,
        proof=battery_proof(methods if methods is not None else _CF_METHODS,
                            centering=centering))
    r1 = check_theory(prove_thy, tok, install=install, session_timeout=prove_timeout)
    if r1.ok:
        return FolVerdict(status=VALID, method="prove-battery",
                          prove_output=r1.output, prove_elapsed=r1.elapsed)

    # --- step 2: refute (nitpick) ----------------------------------------- #
    refute_output = ""
    refute_elapsed = 0.0
    if refute:
        tok2 = "G" + uuid.uuid4().hex[:8]
        nit_thy = isabelle_conditional_theory(
            formula, theory_name=tok2, centering=centering,
            proof=nitpick_proof(card=card, timeout=refute_timeout))
        r2 = check_theory(nit_thy, tok2, install=install,
                          session_timeout=refute_timeout + 30,
                          wall_timeout=float(refute_timeout) + 240.0)
        refute_output = r2.output
        refute_elapsed = r2.elapsed
        if r2.ok:
            m = _NITPICK_CTEX_RE.search(r2.output)
            return FolVerdict(status=INVALID,
                              countermodel=(m.group(0).strip() if m else None),
                              prove_output=r1.output, refute_output=refute_output,
                              prove_elapsed=r1.elapsed, refute_elapsed=refute_elapsed)

    return FolVerdict(status=UNKNOWN, prove_output=r1.output,
                      refute_output=refute_output, prove_elapsed=r1.elapsed,
                      refute_elapsed=refute_elapsed,
                      infra_error=_infra_error(r1.output, refute_output))


# --------------------------------------------------------------------------- #
# Deciding relevant logic B (simplified Routley-Meyer) validity through Isabelle.
# --------------------------------------------------------------------------- #

def isabelle_decide_relevant(
    formula: Node, *,
    methods: Optional[Sequence[str]] = None,
    refute: bool = True,
    card: str = "1-3",
    prove_timeout: int = 60,
    refute_timeout: int = 60,
    install: Optional[IsabelleInstall] = None,
) -> FolVerdict:
    """Decide a relevant-logic-B formula's validity by running a local Isabelle.

    Emits the simplified Routley-Meyer shallow embedding
    (:func:`~unicode_fol_kit.hol.isabelle_relevant.to_isabelle_relevant`, the same
    truth conditions
    :func:`~unicode_fol_kit.semantics.relevant.rel_satisfies` evaluates) and,
    exactly like :func:`isabelle_decide_counterfactual`:

    1. tries a proof battery -- exit 0 => :data:`VALID` over every interpretation
       satisfying the ``wellformed`` frame conditions (N nonempty, ``star`` a
       total involution, ``R`` sourced only at non-normal worlds);
    2. otherwise (``refute``) runs ``nitpick[expect = genuine]`` over the world
       type ``w`` -- exit 0 => :data:`INVALID` (``wellformed`` is a *premise* of
       the goal, so nitpick constructs ``N``/``star``/``R`` itself and certifies
       the model as genuine);
    3. otherwise :data:`UNKNOWN`.

    Args:
        formula: the AST node -- the propositional connectives
            not/and/or/implies/iff over nullary atoms (no quantifiers,
            modalities, lambda terms, or ``Xor`` -- there is no B reading for
            them, matching
            :func:`unicode_fol_kit.semantics.relevant._reject_non_propositional`).
        methods: proof battery; defaults to the embedding's own
            :data:`~unicode_fol_kit.hol.isabelle_relevant.DEFAULT_METHODS`.
        refute / card / prove_timeout / refute_timeout / install: as for
            :func:`isabelle_decide_counterfactual` (``card`` bounds the world
            type ``w``).

    Raises:
        IsabelleNotAvailable: if no Isabelle installation can be located.
        TypeError: propagated from the emitter on a quantifier, modality, lambda
            term, ``Xor``, or non-nullary atom.
    """
    install = install or find_isabelle()
    if install is None:
        raise IsabelleNotAvailable(
            "No Isabelle installation found. Set UFK_ISABELLE_HOME (or ISABELLE_HOME) "
            "to the install directory, or put `isabelle` on PATH.")
    from unicode_fol_kit.hol.isabelle_relevant import (
        to_isabelle_relevant, battery_proof, nitpick_proof,
        DEFAULT_METHODS as _REL_METHODS)

    # --- step 1: prove ---------------------------------------------------- #
    tok = "G" + uuid.uuid4().hex[:8]
    prove_thy = to_isabelle_relevant(
        formula, theory_name=tok,
        proof=battery_proof(methods if methods is not None else _REL_METHODS))
    r1 = check_theory(prove_thy, tok, install=install, session_timeout=prove_timeout)
    if r1.ok:
        return FolVerdict(status=VALID, method="prove-battery",
                          prove_output=r1.output, prove_elapsed=r1.elapsed)

    # --- step 2: refute (nitpick) ----------------------------------------- #
    refute_output = ""
    refute_elapsed = 0.0
    if refute:
        tok2 = "G" + uuid.uuid4().hex[:8]
        nit_thy = to_isabelle_relevant(
            formula, theory_name=tok2,
            proof=nitpick_proof(card=card, timeout=refute_timeout))
        r2 = check_theory(nit_thy, tok2, install=install,
                          session_timeout=refute_timeout + 30,
                          wall_timeout=float(refute_timeout) + 240.0)
        refute_output = r2.output
        refute_elapsed = r2.elapsed
        if r2.ok:
            m = _NITPICK_CTEX_RE.search(r2.output)
            return FolVerdict(status=INVALID,
                              countermodel=(m.group(0).strip() if m else None),
                              prove_output=r1.output, refute_output=refute_output,
                              prove_elapsed=r1.elapsed, refute_elapsed=refute_elapsed)

    return FolVerdict(status=UNKNOWN, prove_output=r1.output,
                      refute_output=refute_output, prove_elapsed=r1.elapsed,
                      refute_elapsed=refute_elapsed,
                      infra_error=_infra_error(r1.output, refute_output))
