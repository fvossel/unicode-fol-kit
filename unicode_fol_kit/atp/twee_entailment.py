"""Entailment checking via the Twee equational theorem prover, through WSL.

`Twee <https://nick8325.github.io/twee/>`_ is a Knuth-Bendix-completion-based
prover for pure UNIT EQUALITY: every axiom and the conjecture must be a
(possibly universally quantified) equation ``s = t``, or a conjunction of
such equations — nothing else (no disjunction, no implication, no predicates
other than ``=``). This module drives Twee exactly as far as that fragment
reaches: :func:`check_entailment_twee_detailed` raises ``NotImplementedError``
naming the offending premise/conclusion for anything outside it, mirroring
:mod:`atp.vampire_entailment`'s contract for the FOL-vs-non-FOL boundary.

Twee has no native Windows build; on this machine (and presumably any other
Windows dev box following the same install recipe) it lives in WSL at
``~/.local/bin/twee`` (installed via ``ghcup``/``cabal``, Twee 2.6.1). Every
invocation therefore goes through ``wsl.exe -e bash -lc "<cmd> ..."`` by
default (``use_wsl=True``) — the ``bash -lc`` wrapper is required, not
cosmetic: invoking ``wsl.exe ~/.local/bin/twee`` directly lets the OUTER
(Windows/Git-Bash) shell expand the ``~`` before ``wsl.exe`` ever sees it,
which resolves to nonsense on the Windows side. Wrapping the whole command in
a WSL-side login shell (``bash -lc "..."``) makes WSL's own bash expand the
``~`` correctly. The command is overridable via ``$UFK_TWEE_CMD`` (defaults
to ``~/.local/bin/twee``), and ``use_wsl=False`` switches to a bare
subprocess call for a machine with a native ``twee`` on ``PATH`` (e.g. a
Linux/macOS host) — the same ``use_wsl`` toggle :mod:`atp.vampire_entailment`
uses for Vampire, just defaulted the other way since Twee's only known
install on THIS kit's dev machines is the WSL one.

Windows temp-file paths are translated to their WSL ``/mnt/...`` form via
``wslpath`` (identical technique to :mod:`atp.vampire_entailment`'s
``_to_wsl_path`` — re-implemented locally here rather than imported, so this
module has no dependency on the Vampire module).

Every run passes ``--quiet`` (Twee's own flag: "Only print essential
information"). This is not just cosmetic either — WITHOUT it, Twee's stdout
opens with a restated/flattened echo of the input problem and a running
completion trace ("Here is the input problem: ... 1. f(a) -> f5 ...") before
the actual result, which is irrelevant noise for parsing; ``--quiet`` was
verified live to produce exactly the axiom/lemma/goal/proof text documented
below and nothing else.

Observed output shapes (every one below was produced by a real ``twee
--quiet`` run on this machine, Twee 2.6.1, and is what
:func:`parse_twee_proof` is built to read — anything else raises
``ValueError``, never a guess):

1. **Theorem, no lemmas** (input ``![X]: f(f(X)) = X`` proving
   ``f(f(f(f(a)))) = a``)::

       The conjecture is true! Here is a proof.

       Axiom 1 (a): f(f(X)) = X.

       Goal 1 (g): f(f(f(f(a)))) = a.
       Proof:
         f(f(f(f(a))))
       = { by axiom 1 (a) }
         f(f(a))
       = { by axiom 1 (a) }
         a

       RESULT: Theorem (the conjecture is true).

   The opening banner line is fixed and always present on a Theorem run —
   even under ``--quiet`` ("only print ESSENTIAL information" apparently
   includes it); :func:`parse_twee_proof` requires it verbatim before the
   axiom block.

2. **Theorem with a lemma, and a reverse-direction (``R->L``) step**
   (left-group axioms proving right-identity; banner line omitted below for
   brevity — see shape 1 for where it goes)::

       Axiom 1 (left_id): mult(e, X) = X.
       Axiom 2 (left_inv): mult(inv(X), X) = e.
       Axiom 3 (assoc): mult(mult(X, Y), Z) = mult(X, mult(Y, Z)).

       Lemma 4: mult(inv(X), mult(X, Y)) = Y.
       Proof:
         mult(inv(X), mult(X, Y))
       = { by axiom 3 (assoc) R->L }
         mult(mult(inv(X), X), Y)
       = { by axiom 2 (left_inv) }
         mult(e, Y)
       = { by axiom 1 (left_id) }
         Y

       Goal 1 (right_id): mult(x, e) = x.
       Proof:
         mult(x, e)
       = { by lemma 4 R->L }
         mult(inv(inv(x)), mult(inv(x), mult(x, e)))
       = { by lemma 4 }
         mult(inv(inv(x)), e)
       = { by axiom 2 (left_inv) R->L }
         mult(inv(inv(x)), mult(inv(x), x))
       = { by lemma 4 }
         x

       RESULT: Theorem (the conjecture is true).

   Grammar notes distilled from this and further examples (``inv(inv(X))=X``
   needing 2 chained lemma applications with mixed directions; a 2-variable
   commutation goal; a 3-conjunct tupled goal; see ``tests/test_twee.py``
   for the exact captured texts used as fixtures):

   * A citation is either ``{ by axiom N (name) }`` or ``{ by lemma N }``
     (lemmas are NEVER named in a citation — only axioms carry a ``(name)``,
     because that name is the one WE assigned when generating the TPTP
     problem, see :func:`_generate_twee_input`), optionally suffixed
     ``R->L`` (apply the equation right-to-left).
   * Axiom variables print in a CANONICAL ``X``/``Y``/``Z``... scheme, NOT
     the original source names — verified by feeding an axiom variable named
     ``V`` and seeing it echoed as ``X``. A goal's variables, by contrast,
     are Skolemized to a FRESH constant that is the ORIGINAL bound-variable
     letter, lowercased (``W`` in the conjecture prints as ``w`` in the Goal
     line and its proof) — this is why axioms are matched to the caller's
     original premises up to alpha-equivalence (a name-blind bijection
     check, see :mod:`atp.twee_check`), while goal variables are matched
     structurally instead of by any assumed naming convention.
   * Only axioms actually USED in the proof are listed in the header block —
     an irrelevant extra axiom is silently omitted, so axiom numbers in the
     proof are a purely LOCAL indexing scheme, unrelated to the caller's
     premise-list position; :func:`_generate_twee_input` names every axiom
     ``premise_<i>`` (1-based, matching the caller's premise list) precisely
     so the checker can still recover which original premise a citation
     means, regardless of Twee's renumbering/omission.
   * A premise that is a top-level conjunction of equations gets clausified
     by Twee into one clause per conjunct; the first conjunct keeps the bare
     ``premise_<i>`` name and each SUBSEQUENT conjunct is suffixed
     ``premise_<i>_<k>`` (``k`` = 1, 2, ... in left-to-right conjunct order)
     — verified with 2- and 3-conjunct premises. :mod:`atp.twee_check`
     replicates this exact naming when cross-checking axiom provenance.
   * A conjunctive CONCLUSION is encoded by Twee as a single equation
     between ``tuple(...)`` applications: ``![X]: (P(X)) & (Q(X))`` proves
     as ``Goal 1 (goal): tuple(P(sk1), Q(sk2)) = tuple(true, true)``-shaped
     (schematically) — and, importantly, each conjunct receives an
     INDEPENDENT fresh Skolem constant even when the conjuncts share a
     source variable name (verified: a 2-conjunct goal over a shared ``X``
     Skolemized to ``x2`` in the first slot and ``x`` in the second) — sound,
     since ``∀X.(P(X)∧Q(X))`` is equivalent to ``(∀X.P(X))∧(∀X.Q(X))``, two
     independent universal claims. A single-conjunct conclusion is NEVER
     tuple-wrapped.

3. **CounterSatisfiable** (the conjecture does not follow) — with
   ``--quiet``, this is the ENTIRE output, no axiom/proof text at all::

       RESULT: CounterSatisfiable (the conjecture is false).

   (Likewise ``Satisfiable``/``Unsatisfiable`` for an axiom-only problem
   with no conjecture — out of scope for this module, which always emits
   exactly one conjecture, but confirmed live for documentation.)

4. **GaveUp** — Twee's own resource budget (``--max-time``, ``--max-cps``,
   etc. — none of which this module passes by default, so this is only
   reachable if a caller forwards such a flag) was exhausted before
   completion could decide the problem either way::

       RESULT: GaveUp (couldn't solve the problem).

5. **No RESULT line at all** — a genuine subprocess timeout (Twee's own
   resource limits are UNLIMITED by default, so an undecided problem just
   runs forever until this module's own ``timeout`` kills the process; the
   partial stdout at that point, if any, is empty since Twee buffers its
   report until the very end), or a Twee-side parse/usage error (printed to
   STDERR with a non-zero exit and nothing on stdout — verified live with a
   malformed conjecture). Both come back as ``status="Unknown"`` from
   :func:`check_entailment_twee_detailed`; ``result["timed_out"]``
   distinguishes the two.

Public API: :func:`twee_available`, :func:`check_entailment_twee_detailed`,
the proof data classes (:class:`TweeEquation`, :class:`TweeCitation`,
:class:`TweeChain`, :class:`TweeAxiom`, :class:`TweeLemma`, :class:`TweeGoal`,
:class:`TweeProof`), and :func:`parse_twee_proof`.
"""

import os
import re
import subprocess
import tempfile
from dataclasses import dataclass
from typing import List, Optional, Tuple

from ..fol.nodes import Atom, And, Constant, Function, Node, Number, Quantifier, Variable
from ._tptp_problem import generate_tptp_problem

__all__ = [
    "twee_available", "check_entailment_twee_detailed",
    "TweeEquation", "TweeCitation", "TweeChain",
    "TweeAxiom", "TweeLemma", "TweeGoal", "TweeProof",
    "parse_twee_proof",
]

_DEFAULT_TWEE_CMD = "~/.local/bin/twee"


def _twee_cmd(explicit: Optional[str]) -> str:
    """Resolve the command used to invoke Twee: explicit arg > ``$UFK_TWEE_CMD`` > default."""
    return explicit or os.environ.get("UFK_TWEE_CMD") or _DEFAULT_TWEE_CMD


# ---------------------------------------------------------------------------
# The equational fragment
# ---------------------------------------------------------------------------

def _is_equational(node: Node) -> bool:
    """True iff ``node`` is a (forall-closed) equation or conjunction of equations.

    Twee decides unit equality only: an ``Atom`` with predicate ``"="`` and
    exactly two arguments, universally quantified any number of times
    (``∀``/``forall`` — an ``∃`` or any other quantifier is out of fragment),
    and/or conjoined with ``And``. Anything else (disjunction, negation,
    implication, a non-``=`` predicate, a modal/second-order/substructural
    node, ...) is not.
    """
    if isinstance(node, Quantifier):
        return node.type in ("forall", "∀") and _is_equational(node.formula)
    if isinstance(node, And):
        return _is_equational(node.left) and _is_equational(node.right)
    if isinstance(node, Atom):
        return node.predicate == "=" and len(node.args) == 2
    return False


def _require_equational(node: Node, role: str) -> None:
    """Raise ``NotImplementedError`` naming ``role`` if ``node`` is not equational."""
    if not _is_equational(node):
        raise NotImplementedError(
            f"twee: {role} is outside the equational fragment Twee decides — "
            f"every premise and the conclusion must be a (forall-closed) "
            f"equation `s = t` or a conjunction of such equations, got "
            f"{role}={node.to_unicode_str()!r}")


# ---------------------------------------------------------------------------
# TPTP problem generation
# ---------------------------------------------------------------------------

def _generate_twee_input(premises: List[Node], conclusion: Node) -> str:
    """Build a TPTP ``fof`` problem string, one axiom per premise plus one conjecture.

    A thin wrapper over the shared :func:`atp._tptp_problem.generate_tptp_problem`
    (also used by :mod:`atp.vampire_entailment` and :mod:`atp.eprover_backend`,
    which build the identical problem shape): each premise becomes
    ``fof(premise_<i>, axiom, <tptp>).`` (1-based) and the conclusion becomes
    ``fof(goal, conjecture, <tptp>).``. The ``premise_<i>`` naming is not
    cosmetic here — it is the anchor :mod:`atp.twee_check` uses to recover
    which original premise an axiom citation in Twee's proof refers to (see
    the module docstring's naming-scheme notes). ``generate_tptp_problem``'s
    cross-formula symbol-collision guard can raise ``NotImplementedError``
    before any TPTP text is produced — see ``_tptp_problem``'s module
    docstring.
    """
    return generate_tptp_problem(premises, conclusion)


# ---------------------------------------------------------------------------
# Process plumbing (WSL by default — see module docstring)
# ---------------------------------------------------------------------------

def _to_wsl_path(windows_path: str) -> str:
    """Translate a Windows path to its WSL ``/mnt/...`` form via ``wslpath``.

    A local copy of :func:`atp.vampire_entailment._to_wsl_path`'s technique
    (backslashes to forward slashes first, since the WSL interop layer
    swallows literal backslashes in arguments) — reimplemented here rather
    than imported so this module carries no dependency on the Vampire one.
    """
    result = subprocess.run(
        ["wsl.exe", "wslpath", "-u", windows_path.replace("\\", "/")],
        capture_output=True, text=True, timeout=20,
    )
    wsl_path = result.stdout.strip()
    if not wsl_path:
        raise RuntimeError(
            f"wslpath could not translate {windows_path!r} (is WSL available?): "
            f"{result.stderr.strip()}")
    return wsl_path


def _spawn_twee(input_str: str, timeout: int, use_wsl: bool,
                twee_cmd: Optional[str]) -> Tuple[str, str, bool]:
    """Write the TPTP problem to a temp file, run Twee, return ``(stdout, stderr, timed_out)``.

    With ``use_wsl=True`` (the default), Twee is invoked as
    ``wsl.exe -e bash -lc "<cmd> --quiet '<wsl-path>'"`` — the ``bash -lc``
    wrapper is required so WSL's own shell (not the Windows/Git-Bash caller)
    expands a leading ``~`` in ``<cmd>`` (see module docstring). With
    ``use_wsl=False``, ``<cmd>`` is invoked as a bare subprocess with the
    Windows temp path directly (for a native, non-WSL Twee).

    A subprocess timeout is swallowed into ``timed_out=True`` (stdout/stderr
    both ``""``), matching :mod:`atp.vampire_entailment`'s convention; any
    other error (e.g. ``FileNotFoundError`` for ``wsl.exe`` itself missing)
    propagates. The temp file is always removed.
    """
    cmd = _twee_cmd(twee_cmd)
    with tempfile.NamedTemporaryFile(mode="w", suffix=".p", delete=False,
                                     encoding="utf-8") as temp_file:
        temp_file.write(input_str)
        temp_filename = temp_file.name

    try:
        if use_wsl:
            wsl_path = _to_wsl_path(temp_filename)
            full_command = f"{cmd} --quiet '{wsl_path}'"
            command = ["wsl.exe", "-e", "bash", "-lc", full_command]
        else:
            command = [cmd, "--quiet", temp_filename]
        result = subprocess.run(command, capture_output=True, text=True, timeout=timeout)
        return result.stdout, result.stderr, False
    except subprocess.TimeoutExpired:
        return "", "", True
    finally:
        try:
            os.unlink(temp_filename)
        except OSError:
            pass


def twee_available(use_wsl: bool = True, twee_cmd: Optional[str] = None) -> bool:
    """``True`` iff a Twee binary responds to ``--version`` (cheap; no caching).

    Discovery: ``twee_cmd`` argument > ``$UFK_TWEE_CMD`` > ``~/.local/bin/twee``
    (see :func:`_twee_cmd`). With ``use_wsl=True`` (the default) the check runs
    ``wsl.exe -e bash -lc "<cmd> --version"``; any failure (no ``wsl.exe``, no
    WSL distro, the command not found inside WSL, ...) is swallowed to
    ``False`` — pure discovery, never raises. Twee prints ``--version`` to
    STDERR, not stdout (verified live), so both streams are checked.
    """
    cmd = _twee_cmd(twee_cmd)
    try:
        if use_wsl:
            command = ["wsl.exe", "-e", "bash", "-lc", f"{cmd} --version"]
        else:
            command = [cmd, "--version"]
        result = subprocess.run(command, capture_output=True, text=True, timeout=20)
        combined = (result.stdout + result.stderr).lower()
        return result.returncode == 0 and "twee version" in combined
    except Exception:   # noqa: BLE001 - any failure means "not available"
        return False


# ---------------------------------------------------------------------------
# Term parsing (Twee's own printed syntax: NAME or NAME(arg, arg, ...))
# ---------------------------------------------------------------------------

_TOKEN_RE = re.compile(r"\s*([A-Za-z_$][A-Za-z0-9_$]*|-?\d+(?:\.\d+)?|[(),])")


def _tokenize(text: str) -> List[str]:
    """Tokenize a Twee-printed term into identifiers, numbers, and ``( ) ,``."""
    tokens = []
    pos = 0
    while pos < len(text):
        m = _TOKEN_RE.match(text, pos)
        if not m:
            if text[pos:].strip() == "":
                break
            raise ValueError(f"twee term parser: unrecognised text at {text[pos:]!r} in {text!r}")
        tokens.append(m.group(1))
        pos = m.end()
    return tokens


def _parse_term(text: str) -> Node:
    """Parse one Twee-printed term into a kit term ``Node``.

    An identifier starting with an uppercase letter is a :class:`Variable`
    (Twee's own convention for axiom/lemma rewrite variables, e.g. ``X``);
    any other identifier is a :class:`Constant` (no args) or :class:`Function`
    (parenthesised, comma-space-separated args, e.g. ``mult(inv(X), Y)``); a
    bare numeral is a :class:`Number`. Raises ``ValueError`` for anything that
    does not parse as exactly one such term (trailing tokens, unbalanced
    parens, ...) — this is the boundary past which the module refuses to
    guess, per the "anything unrecognised raises" contract.
    """
    tokens = _tokenize(text)
    if not tokens:
        raise ValueError(f"twee term parser: empty term text {text!r}")
    pos = [0]

    def _peek() -> Optional[str]:
        return tokens[pos[0]] if pos[0] < len(tokens) else None

    def _numeric(tok: str) -> bool:
        return re.fullmatch(r"-?\d+(?:\.\d+)?", tok) is not None

    def parse_one() -> Node:
        tok = _peek()
        if tok is None:
            raise ValueError(f"twee term parser: unexpected end of term in {text!r}")
        if _numeric(tok):
            pos[0] += 1
            return Number(float(tok) if "." in tok else int(tok))
        if tok in "(),":
            raise ValueError(f"twee term parser: unexpected {tok!r} in {text!r}")
        name = tok
        pos[0] += 1
        if _peek() == "(":
            pos[0] += 1
            args = [parse_one()]
            while _peek() == ",":
                pos[0] += 1
                args.append(parse_one())
            if _peek() != ")":
                raise ValueError(f"twee term parser: unbalanced parentheses in {text!r}")
            pos[0] += 1
            return Function(name, args)
        if name[0].isupper():
            return Variable(name)
        return Constant(name)

    result = parse_one()
    if pos[0] != len(tokens):
        raise ValueError(f"twee term parser: trailing tokens after a complete term in {text!r}")
    return result


def _split_equation(text: str) -> Tuple[str, str]:
    """Split a header's ``"lhs = rhs"`` text on the (sole) top-level ``" = "``."""
    if " = " not in text:
        raise ValueError(f"twee proof parser: expected 'lhs = rhs', got {text!r}")
    lhs, rhs = text.split(" = ", 1)
    return lhs, rhs


# ---------------------------------------------------------------------------
# Parsed-proof data model
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class TweeEquation:
    """One equation as Twee restates it: ``lhs = rhs`` (both kit term Nodes)."""

    lhs: Node
    rhs: Node

    def to_dict(self) -> dict:
        return {"lhs": self.lhs.to_dict(), "rhs": self.rhs.to_dict()}


@dataclass(frozen=True)
class TweeCitation:
    """One ``{ by axiom N (name) [R->L] }`` / ``{ by lemma N [R->L] }`` citation.

    ``name`` is the axiom's ``(name)`` (always present for ``kind="axiom"``,
    always ``None`` for ``kind="lemma"`` — lemmas are never named in Twee's
    own citations). ``reversed`` is ``True`` iff the citation carries the
    ``R->L`` suffix (apply the equation right-to-left).
    """

    kind: str
    number: int
    name: Optional[str]
    reversed: bool = False

    def __post_init__(self):
        if self.kind not in ("axiom", "lemma"):
            raise ValueError(f"TweeCitation: kind must be 'axiom' or 'lemma', got {self.kind!r}")

    def to_dict(self) -> dict:
        return {"kind": self.kind, "number": self.number, "name": self.name,
                "reversed": self.reversed}


@dataclass(frozen=True)
class TweeChain:
    """A rewrite chain: ``terms[0]`` rewritten step by step down to ``terms[-1]``.

    ``len(terms) == len(citations) + 1`` — ``citations[i]`` justifies the step
    from ``terms[i]`` to ``terms[i+1]``.
    """

    terms: Tuple[Node, ...]
    citations: Tuple[TweeCitation, ...] = ()

    def __post_init__(self):
        object.__setattr__(self, "terms", tuple(self.terms))
        object.__setattr__(self, "citations", tuple(self.citations))
        if len(self.terms) != len(self.citations) + 1:
            raise ValueError(
                f"TweeChain: {len(self.terms)} terms need exactly "
                f"{max(len(self.terms) - 1, 0)} citations, got {len(self.citations)}")

    def to_dict(self) -> dict:
        return {"terms": [t.to_dict() for t in self.terms],
                "citations": [c.to_dict() for c in self.citations]}


@dataclass(frozen=True)
class TweeAxiom:
    """One ``Axiom N (name): lhs = rhs.`` header line."""

    number: int
    name: str
    equation: TweeEquation

    def to_dict(self) -> dict:
        return {"number": self.number, "name": self.name, "equation": self.equation.to_dict()}


@dataclass(frozen=True)
class TweeLemma:
    """One ``Lemma N: lhs = rhs.`` block with its own ``Proof:`` chain."""

    number: int
    equation: TweeEquation
    chain: TweeChain

    def to_dict(self) -> dict:
        return {"number": self.number, "equation": self.equation.to_dict(),
                "chain": self.chain.to_dict()}


@dataclass(frozen=True)
class TweeGoal:
    """The (single, always-last) ``Goal N (name): lhs = rhs.`` block."""

    number: int
    name: str
    equation: TweeEquation
    chain: TweeChain

    def to_dict(self) -> dict:
        return {"number": self.number, "name": self.name,
                "equation": self.equation.to_dict(), "chain": self.chain.to_dict()}


@dataclass(frozen=True)
class TweeProof:
    """A full parsed Twee ``Theorem`` proof: the used axioms, lemmas, then the goal."""

    axioms: Tuple[TweeAxiom, ...] = ()
    lemmas: Tuple[TweeLemma, ...] = ()
    goal: TweeGoal = None

    def __post_init__(self):
        object.__setattr__(self, "axioms", tuple(self.axioms))
        object.__setattr__(self, "lemmas", tuple(self.lemmas))
        if self.goal is None:
            raise ValueError("TweeProof: goal is required")

    def to_dict(self) -> dict:
        return {"axioms": [a.to_dict() for a in self.axioms],
                "lemmas": [l.to_dict() for l in self.lemmas],
                "goal": self.goal.to_dict()}


# ---------------------------------------------------------------------------
# Proof parser
# ---------------------------------------------------------------------------

_AXIOM_RE = re.compile(r"^Axiom (\d+) \(([^)]*)\): (.+)\.$")
_LEMMA_RE = re.compile(r"^Lemma (\d+): (.+)\.$")
_GOAL_RE = re.compile(r"^Goal (\d+) \(([^)]*)\): (.+)\.$")
_CITATION_RE = re.compile(r"^= \{ by (axiom|lemma) (\d+)(?: \(([^)]*)\))?( R->L)? \}$")
_RESULT_RE = re.compile(r"^RESULT: (\S+) \(.*\)\.$")


def _extract_result_status(stdout: str) -> Optional[str]:
    """Return Twee's ``RESULT: <Status> (...)`` token, or ``None`` if absent.

    Only the last non-blank line is checked (that is always where ``RESULT:``
    lives in every observed shape) — a stray line elsewhere that happens to
    start with ``RESULT:`` (not observed, never generated by Twee) is not
    treated as the verdict.
    """
    lines = [ln for ln in stdout.splitlines() if ln.strip()]
    if not lines:
        return None
    m = _RESULT_RE.match(lines[-1].strip())
    return m.group(1) if m else None


def _parse_chain(lines: List[str], idx: int) -> Tuple[TweeChain, int]:
    """Parse a ``Proof:``-following rewrite chain starting at ``lines[idx]``.

    Returns ``(chain, next_idx)`` where ``next_idx`` is the first line after
    the chain (a blank line, a new header, or end of input).
    """
    if idx >= len(lines) or not lines[idx].startswith("  "):
        raise ValueError(f"twee proof parser: expected an indented term line, got {lines[idx:idx+1]!r}")
    terms = [_parse_term(lines[idx][2:].strip())]
    idx += 1
    citations: List[TweeCitation] = []
    while idx < len(lines) and lines[idx].strip():
        cm = _CITATION_RE.match(lines[idx])
        if not cm:
            break
        kind, number, name, rev = cm.group(1), int(cm.group(2)), cm.group(3), cm.group(4) is not None
        if kind == "axiom" and name is None:
            raise ValueError(f"twee proof parser: axiom citation missing its (name): {lines[idx]!r}")
        if kind == "lemma" and name is not None:
            raise ValueError(f"twee proof parser: lemma citation must not carry a (name): {lines[idx]!r}")
        citations.append(TweeCitation(kind, number, name, rev))
        idx += 1
        if idx >= len(lines) or not lines[idx].startswith("  "):
            raise ValueError(f"twee proof parser: expected an indented term line after a citation, "
                             f"got {lines[idx:idx+1]!r}")
        terms.append(_parse_term(lines[idx][2:].strip()))
        idx += 1
    return TweeChain(tuple(terms), tuple(citations)), idx


def parse_twee_proof(stdout: str) -> Optional[TweeProof]:
    """Parse Twee's ``--quiet`` stdout into a :class:`TweeProof`, or ``None``.

    Returns ``None`` whenever the ``RESULT`` is not ``Theorem`` (Twee's
    ``--quiet`` output for ``CounterSatisfiable``/``Satisfiable``/etc. is just
    the bare ``RESULT:`` line — nothing to parse — see the module docstring's
    shape 3). Raises ``ValueError`` when ``RESULT`` IS ``Theorem`` but the
    surrounding text does not match the grammar distilled in the module
    docstring (shapes 1-2) — never silently produces a partial/guessed proof.
    """
    if _extract_result_status(stdout) != "Theorem":
        return None

    lines = [ln.rstrip() for ln in stdout.splitlines()]
    idx = 0

    # Every observed Theorem run opens with this fixed banner line (even
    # under --quiet — verified live; it is the one piece of "essential
    # information" --quiet does not suppress) followed by a blank line.
    if idx >= len(lines) or lines[idx] != "The conjecture is true! Here is a proof.":
        raise ValueError(
            f"twee proof parser: expected the 'conjecture is true' banner line, "
            f"got {lines[idx:idx + 1]!r}")
    idx += 1
    while idx < len(lines) and not lines[idx].strip():
        idx += 1

    axioms: List[TweeAxiom] = []
    while idx < len(lines) and lines[idx].strip():
        m = _AXIOM_RE.match(lines[idx])
        if not m:
            break
        number, name, eq_text = int(m.group(1)), m.group(2), m.group(3)
        lhs_text, rhs_text = _split_equation(eq_text)
        axioms.append(TweeAxiom(number, name,
                                TweeEquation(_parse_term(lhs_text), _parse_term(rhs_text))))
        idx += 1
    while idx < len(lines) and not lines[idx].strip():
        idx += 1

    lemmas: List[TweeLemma] = []
    goal: Optional[TweeGoal] = None
    while idx < len(lines):
        if not lines[idx].strip():
            idx += 1
            continue
        if _RESULT_RE.match(lines[idx]):
            # The trailing RESULT line is a natural terminator, not a
            # Lemma/Goal header — reached here only for a malformed proof
            # that has no Goal block at all (see the "no Goal block" check
            # below); the RESULT's own status was already read separately.
            break
        m_lemma = _LEMMA_RE.match(lines[idx])
        m_goal = _GOAL_RE.match(lines[idx])
        if m_lemma:
            number, eq_text = int(m_lemma.group(1)), m_lemma.group(2)
            lhs_text, rhs_text = _split_equation(eq_text)
            equation = TweeEquation(_parse_term(lhs_text), _parse_term(rhs_text))
            idx += 1
            if idx >= len(lines) or lines[idx].strip() != "Proof:":
                raise ValueError(f"twee proof parser: expected 'Proof:' after Lemma {number}")
            idx += 1
            chain, idx = _parse_chain(lines, idx)
            lemmas.append(TweeLemma(number, equation, chain))
        elif m_goal:
            number, name, eq_text = int(m_goal.group(1)), m_goal.group(2), m_goal.group(3)
            lhs_text, rhs_text = _split_equation(eq_text)
            equation = TweeEquation(_parse_term(lhs_text), _parse_term(rhs_text))
            idx += 1
            if idx >= len(lines) or lines[idx].strip() != "Proof:":
                raise ValueError(f"twee proof parser: expected 'Proof:' after Goal {number}")
            idx += 1
            chain, idx = _parse_chain(lines, idx)
            goal = TweeGoal(number, name, equation, chain)
            break   # the goal is always the last block Twee prints
        else:
            raise ValueError(
                f"twee proof parser: expected a Lemma/Goal header, got {lines[idx]!r}")

    if goal is None:
        raise ValueError("twee proof parser: RESULT was Theorem but no Goal block was found")

    return TweeProof(tuple(axioms), tuple(lemmas), goal)


# ---------------------------------------------------------------------------
# Public entry point
# ---------------------------------------------------------------------------

def check_entailment_twee_detailed(premises: List[Node], conclusion: Node,
                                   timeout: int = 30, use_wsl: bool = True,
                                   twee_cmd: Optional[str] = None) -> dict:
    """Run Twee on ``premises ⊨ conclusion`` and return its status, output, and proof.

    Both ``premises`` and ``conclusion`` must be in Twee's equational
    fragment (see :func:`_is_equational`) — anything else raises
    ``NotImplementedError`` naming the offender, BEFORE any subprocess is
    spawned (same contract as :func:`atp.vampire_entailment
    .check_entailment_vampire_detailed`). Problem generation additionally
    refuses (also ``NotImplementedError``, also before any subprocess) if
    two distinct function/constant names would fold to the same TPTP
    identifier — see :mod:`atp._tptp_problem`'s module docstring; ``=`` is
    the only predicate this fragment ever uses, and it is excluded from that
    check entirely (see the same docstring), so only a function/constant
    collision can occur here.

    Args:
        premises: equational premise formulas.
        conclusion: the equational conclusion formula.
        timeout: seconds to allow the Twee process before giving up (a
            subprocess timeout, not one of Twee's own ``--max-*`` flags,
            which this function never passes).
        use_wsl: drive Twee through WSL (default ``True`` — see module
            docstring); ``False`` for a native, non-WSL Twee on ``PATH``.
        twee_cmd: override the Twee command/path (default: ``$UFK_TWEE_CMD``,
            else ``~/.local/bin/twee``).

    Returns:
        A dict with:

        * ``status``: Twee's own ``RESULT:`` token verbatim (``"Theorem"``,
          ``"CounterSatisfiable"``, ``"GaveUp"``, ``"Satisfiable"``,
          ``"Unsatisfiable"``, ...), or ``"Unknown"`` when no ``RESULT:``
          line was found at all (a subprocess timeout, or a Twee-side
          parse/usage error — see ``timed_out`` to distinguish).
        * ``raw_output``: Twee's full stdout; if no ``RESULT:`` line was
          found and Twee wrote to stderr (a parse/usage error), stderr is
          appended so the failure is diagnosable.
        * ``proof``: the parsed :class:`TweeProof` when ``status ==
          "Theorem"`` (call ``.to_dict()`` for a JSON-compatible form — kept
          as the live dataclass here, not pre-serialised, because
          :func:`atp.twee_check.check_twee_proof` consumes it directly),
          else ``None``.
        * ``timed_out``: ``True`` iff this function's own ``timeout`` (not
          one of Twee's ``--max-*`` budgets) killed the subprocess.
    """
    for i, premise in enumerate(premises, start=1):
        _require_equational(premise, f"premise {i}")
    _require_equational(conclusion, "conclusion")

    problem = _generate_twee_input(list(premises), conclusion)
    stdout, stderr, timed_out = _spawn_twee(problem, timeout=timeout, use_wsl=use_wsl,
                                            twee_cmd=twee_cmd)

    if timed_out:
        return {"status": "Unknown", "raw_output": "", "proof": None,
                "timed_out": True, "proof_parse_error": None}

    status = _extract_result_status(stdout) or "Unknown"
    raw_output = stdout
    if status == "Unknown" and stderr:
        raw_output = f"{stdout}\n{stderr}" if stdout else stderr

    proof = None
    proof_parse_error = None
    if status == "Theorem":
        try:
            proof = parse_twee_proof(stdout)
        except ValueError as exc:
            # A Theorem status with proof text outside this module's
            # distilled grammar (another Twee version, a reformat) must not
            # CRASH the caller: the status stands, the proof is honestly
            # absent, and the parser's complaint travels along so
            # TweeBackend can refuse PROVED with the reason on record
            # (review-confirmed: this previously raised out of decide()).
            proof_parse_error = str(exc)
    return {"status": status, "raw_output": raw_output, "proof": proof,
            "timed_out": False, "proof_parse_error": proof_parse_error}
