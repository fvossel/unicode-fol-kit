"""cvc5 as a second, independent SMT decision procedure for classical FOL.

cvc5 (BSD-3, https://cvc5.github.io) is a full SMT solver with its own
quantifier-instantiation engine (E-matching, enumerative and syntax-guided
instantiation, finite model finding), independent of and often complementary
to Z3's. This module wires it in as a :class:`~unicode_fol_kit.atp.protocol
.ProverBackend` (:class:`Cvc5Backend`, registry name ``"cvc5"``) using
exactly the same classical-FOL fragment Z3 decides in
:class:`unicode_fol_kit.atp.protocol.Z3Backend`: whatever ``Node.to_z3()``
can translate (uninterpreted sort + equality, no arithmetic — see
``fol/_fol_nodes.py``); substructural nodes (linear logic, Lambek calculus)
reject with ``NotImplementedError`` from ``to_z3()`` itself and are reported
UNKNOWN/``"unsupported"`` here, never guessed at.

Translation route — SMT-LIB2 text, not the pythonic term API
--------------------------------------------------------------
cvc5's Python API (1.3.x) builds terms through its own :class:`cvc5.Solver`
/ ``TermManager``, which do not accept Z3 expressions. Re-walking every kit
``Node`` a second time against cvc5's term constructors would duplicate the
entire ``to_z3`` translation and risk it drifting out of sync. Instead this
backend reuses ``to_z3()`` as already trusted by :class:`Z3Backend`, hands
the resulting Z3 expression to a throwaway ``z3.Solver`` for canonical
SMT-LIB2 serialisation (``Solver.to_smt2()`` — sorts, functions and the goal
all print correctly, including quantifiers), and replays that text into
cvc5 via ``cvc5.InputParser``. Each parsed command is invoked on the cvc5
solver immediately (the parser resolves later symbols against earlier
declarations, so streaming invocation is required — buffering all commands
before invoking any breaks the sort/symbol lookups); the ``(check-sat)``
command in the text is skipped and ``Solver.checkSat()`` is called directly
so a genuine :class:`cvc5.Result` (not a string) drives the verdict.

Validity is asked as an UNSAT question, mirroring Z3Backend: ``unsat`` on
``¬((⋀ premises) → φ)`` proves the entailment; ``sat`` produces a genuine
countermodel (a best-effort variable/function assignment read back off the
cvc5 model — one term at a time, so a model cvc5 cannot print for some
symbol does not blank out the whole witness); ``unknown`` is honestly
UNKNOWN, with ``reason="timeout"`` iff cvc5's own explanation says the time
budget (``tlimit``, set from the ``timeout`` argument, milliseconds) was the
cause, else ``"incomplete"`` (quantified UF is undecidable in general; cvc5
gave up without exhausting time or hitting a bound it can name).

Optional dependency: this backend needs ``pip install cvc5`` (extra
``unicode-fol-kit[cvc5]``). :meth:`Cvc5Backend.available` is pure discovery
(``importlib.util.find_spec``, no import) so probing it never pays the
binding's load cost; ``cvc5`` itself is imported lazily inside ``decide()``.

**ASCII/legality sanitisation (problem-level seam) — narrower than TPTP's.**
``Node.to_z3()`` hands a symbol's name to Z3's Python API completely raw —
no transliteration, no fold — and that is FINE for Z3 itself: a Z3 symbol
name is an arbitrary Python string, not text that has to satisfy any
lexical grammar. The gap this module has is specifically in the SMT-LIB2
TEXT round trip described above (``Solver.to_smt2()`` -> ``InputParser``):
Z3's own ``to_smt2()`` already pipe-quotes (``|...|``) any name that is not
already a legal SMT-LIB2 ``simple_symbol`` — verified live, a non-ASCII
name such as ``świątek`` round-trips through it correctly ALREADY, with no
help from this module — except for TWO cases it gets wrong: a name that is
pure ASCII, made only of ``simple_symbol``-legal characters, but starts
with a DIGIT (``2008SummerOlympics``), and a name that IS one of the SEVEN
SMT-LIB2 ``<reserved>`` words Z3's OWN parser actually treats specially as
syntax (``!``, ``_``, ``as``, ``exists``, ``forall``, ``let``, ``match``).
SMT-LIB2 v2.6's grammar (Sec. 3.1) lists six more words as ``<reserved>``
(``BINARY``, ``DECIMAL``, ``HEXADECIMAL``, ``NUMERAL``, ``par``,
``STRING``) but Z3's parser does not special-case any of them when they
appear as an ordinary declared symbol — verified live, in every role this
module can emit one (bare declaration, applied as a predicate/function
head, used as an argument) — so renaming them would violate R1 below for
no reason; only the seven above are ever queued. SMT-LIB2's grammar
requires a ``simple_symbol`` to start with a non-digit and to not BE a
reserved word, so a digit-leading name needs quoting and so do these seven,
but Z3's serialiser adds it for neither — verified live for both: a
function named ``let`` prints as the undecorated head of ``(let x)``,
which its OWN parser then reads as the ``let``-BINDING form, not an
application of a symbol named ``let``. Either way the resulting ``.smt2``
text fails to parse (``z3.parse_smt2_string`` raises; reproduced live for
the digit-leading case, and feeding one such name to this backend
segfaults the whole process before :meth:`Cvc5Backend.decide` ever gets to
return an ERROR ``Verdict``, since a native crash is not a Python
exception ``decide()`` can catch). So, unlike :mod:`atp._tptp_problem` and
:mod:`atp.prover9_entailment` (which must fix BOTH non-ASCII and
digit-leading names — Vampire/E/Prover9 have no automatic quoting of their
own), :func:`_sanitize_for_smtlib` only ever touches a name that is
digit-leading OR reserved; every other name, including every non-ASCII
one, is left completely untouched — touching one would change the export
for a name this backend already handles correctly today, which R1
forbids. The sanitised goal's ``sat`` countermodel is translated back via
:func:`_reverse_map_assignment` before it reaches the caller, so a caller
always sees the ORIGINAL kit-level symbol name, never the synthesised
digit-safe/reserved-safe token.
"""

import importlib.metadata
import importlib.util
import time
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Sequence, Tuple

from ..fol._msfl_nodes import nonempty_sort_axioms
from ..fol.nodes import Atom, Constant, Function, Node, And, Implies
from ._ascii_names import ascii_safe_base, reserve_rendered, reverse_map_text
from .protocol import ProverBackend, Verdict, PROVED, REFUTED, UNKNOWN, ERROR

__all__ = ["Cvc5Backend"]


# ---------------------------------------------------------------------------
# ASCII/legality sanitisation — see the module docstring's sanitisation
# section for why this is narrower than atp._tptp_problem's / atp
# .prover9_entailment's (only digit-leading pure-ASCII names and SMT-LIB2's
# own reserved words are unsafe here; everything else, including every
# non-ASCII name, already round-trips correctly through Z3's own SMT-LIB2
# serialisation).
# ---------------------------------------------------------------------------

#: The SEVEN SMT-LIB2 <reserved> words (of the thirteen the v2.6 grammar's
#: Sec. 3.1 lists) that Z3's OWN parser actually treats as syntax rather
#: than an ordinary <symbol> — none of these is a legal plain <symbol> when
#: used as a declared name, even though nothing else about the string looks
#: illegal (no digit, no non-ASCII character, no special character Z3 would
#: quote). Z3's own ``to_smt2()`` does not quote any of them either (verified
#: live: a function declared under the name ``let`` prints as the
#: undecorated head of ``(let x)``, which its own parser then reads as the
#: ``let``-BINDING form, not a call to a symbol named ``let``) — see the
#: module docstring. The other six <reserved> words (``BINARY``, ``DECIMAL``,
#: ``HEXADECIMAL``, ``NUMERAL``, ``par``, ``STRING``) are DELIBERATELY
#: excluded: verified live that Z3's parser round-trips every one of them
#: as a bare declaration, as an applied predicate/function head, and as an
#: argument — renaming them would be an unforced, undocumented rename of a
#: name this backend already handles correctly, which R1 (see the module
#: docstring) forbids.
_SMTLIB_RESERVED_WORDS = frozenset({
    "!", "_", "as", "exists", "forall", "let", "match",
})


def _is_smtlib_safe(name: str) -> bool:
    if not name:
        return False
    if name in _SMTLIB_RESERVED_WORDS:
        return False
    return not (name.isascii() and name[0].isdigit())


def _unquote_smtlib(s: str) -> str:
    """Strip an SMT-LIB2 ``|...|`` quoted-symbol wrapper, if present.

    A quoted symbol has no escape mechanism (the only characters forbidden
    INSIDE one are ``|`` and ``\\``, per the SMT-LIB2 spec), so stripping the
    outer pair is a lossless, exact inverse of the quoting Z3's ``to_smt2()``
    already applies to any name it did not consider a plain ``simple_symbol``
    (see the module docstring) — no unescaping needed, unlike a string
    literal.
    """
    if len(s) >= 2 and s[0] == "|" and s[-1] == "|":
        return s[1:-1]
    return s


@dataclass
class SmtNameMap:
    """The digit-leading/reserved-word renamings :func:`_sanitize_for_smtlib`
    chose for one goal — a single FLAT namespace across predicate/function/
    constant names (Z3/SMT-LIB2's uninterpreted-function declarations share
    one symbol space regardless of return sort), built from the same
    :func:`~atp._ascii_names.ascii_safe_base` / :func:`~atp._ascii_names
    .reserve_rendered` primitives :mod:`atp._tptp_problem` and
    :mod:`atp.prover9_entailment` use, with SMT-LIB2's own (much narrower —
    see the module docstring) legality test and no render/fold step (SMT-LIB2
    text is never case-folded, so the rendered form IS the raw token).
    """

    mapping: Dict[str, str] = field(default_factory=dict)
    used: set = field(default_factory=set)
    _pending: list = field(default_factory=list)

    def collect(self, name: str) -> None:
        """First pass: register `name`; an already-legal name is reserved
        immediately (order-independent — see
        :class:`~atp._tptp_problem._Renamer`'s docstring for why collision
        avoidance for a synthesised name must not depend on processing
        order relative to an unrelated already-legal name)."""
        if name in self.mapping or name in self._pending:
            return
        if _is_smtlib_safe(name):
            self.used.add(name)
            self.mapping[name] = name
        else:
            self._pending.append(name)

    def finalize(self) -> None:
        """Second pass: synthesise a token for every queued digit-leading or
        reserved-word name, now that every already-legal name in the goal is
        reserved.

        :func:`~atp._ascii_names.ascii_safe_base` only prepends its prefix
        when the transliterated result is EMPTY or DIGIT-leading — a
        reserved word such as ``let`` is neither (it is already a plain
        ASCII, non-digit-leading string), so it comes back unchanged and
        would be reserved verbatim, defeating the whole point of queuing it.
        The extra check below catches exactly that residual case.
        """
        for name in self._pending:
            base = ascii_safe_base(name, "n")
            if base in _SMTLIB_RESERVED_WORDS:
                base = "n" + base
            token = reserve_rendered(base, self.used)
            self.mapping[name] = token
        self._pending = []

    def get(self, name: str) -> str:
        return self.mapping[name]

    def reverse(self) -> Dict[str, str]:
        return {v: k for k, v in self.mapping.items()}


def _sanitize_node_for_smtlib(node: Node, names: SmtNameMap) -> Node:
    """Rebuild ``node`` with every digit-leading symbol name replaced.

    Mirrors :func:`atp._tptp_problem._sanitize_node_for_tptp`'s structural
    recursion; ``=``/``≠`` are excluded from renaming because
    :meth:`~fol.nodes.Atom.to_z3` maps them to Z3's native equality
    operators rather than an uninterpreted predicate — they are never
    identifiers to begin with.
    """
    if isinstance(node, Atom):
        if node.predicate in ("=", "≠"):
            pred = node.predicate
        else:
            pred = names.get(node.predicate)
        return Atom(pred, [_sanitize_node_for_smtlib(a, names) for a in node.args])
    if isinstance(node, Function):
        return Function(names.get(node.name),
                        [_sanitize_node_for_smtlib(a, names) for a in node.args])
    if isinstance(node, Constant):
        return Constant(names.get(node.name))
    return node.map_children(lambda c: _sanitize_node_for_smtlib(c, names))


def _collect_names_for_smtlib(node: Node, names: SmtNameMap) -> None:
    """First pass (see :meth:`SmtNameMap.collect`): register every
    predicate/function/constant name ``node`` uses, without rewriting
    anything yet."""
    for n in node.walk():
        if isinstance(n, Atom):
            if n.predicate not in ("=", "≠"):
                names.collect(n.predicate)
        elif isinstance(n, Function):
            names.collect(n.name)
        elif isinstance(n, Constant):
            names.collect(n.name)


def _sanitize_for_smtlib(node: Node) -> Tuple[Node, SmtNameMap]:
    """Sanitise ``node`` (the already-folded ``(∧ premises) → φ`` goal) for
    the SMT-LIB2 round trip. Returns ``(sanitised_node, mapping)`` — the
    two-pass collect-then-finalize split (see :class:`SmtNameMap`, mirroring
    :class:`atp._tptp_problem._Renamer`) means a synthesised digit-safe
    token can never collide with an already-legal name anywhere in
    ``node``, regardless of which one this walk reaches first.

    Single-node case, kept for the digit-leading/R1/R2/R5 regression tests
    that exercise it directly; :meth:`Cvc5Backend.decide` itself uses
    :func:`_sanitize_many_for_smtlib` (below) so premises stay SEPARATE
    SMT-LIB2 assertions rather than one folded implication — see that
    function's docstring for why.
    """
    names = SmtNameMap()
    _collect_names_for_smtlib(node, names)
    names.finalize()
    return _sanitize_node_for_smtlib(node, names), names


def _sanitize_many_for_smtlib(nodes: Sequence[Node]) -> Tuple[List[Node], SmtNameMap]:
    """Sanitise several nodes (this backend's premises, then the goal, in
    that order) against ONE SHARED name map, so a symbol used across
    several of them renames consistently — the same two-pass
    collect-then-finalize discipline as :func:`_sanitize_for_smtlib`
    (:class:`SmtNameMap`), just collected across the WHOLE list before any
    renaming is finalised, rather than over one already-folded node.

    :meth:`Cvc5Backend.decide` asserts each returned node as its OWN
    ``(assert ...)`` SMT-LIB2 command (see :meth:`Cvc5Backend._run`) instead
    of folding ``premises`` into one ``(∧ premises) → φ`` implication first
    (:func:`_implication` — still used by :func:`_sanitize_for_smtlib`'s own
    regression tests, unrelated to this path): cvc5's ``getUnsatCore()``
    reports relevance at the granularity of INDIVIDUAL top-level assertions,
    so a single folded assertion would always report as "the whole thing",
    a technically sound but useless certificate — the exact failure mode
    this module's own C12 test suite checks for. Logically this changes
    nothing (SMT solvers conjoin every assertion regardless of how many
    ``(assert ...)`` commands they arrived in), only the unsat-core
    bookkeeping's resolution.
    """
    names = SmtNameMap()
    for node in nodes:
        _collect_names_for_smtlib(node, names)
    names.finalize()
    return [_sanitize_node_for_smtlib(node, names) for node in nodes], names


def _reverse_map_assignment(assignment: Dict[str, str], reverse: Dict[str, str]) -> Dict[str, str]:
    """Translate a cvc5 ``sat`` model's ``{declared_term_str: value_str}``
    witness back to original kit-level names.

    Every key AND value is first unquoted (:func:`_unquote_smtlib`) — cvc5's
    ``str(term)``/``str(value)`` reproduce whatever quoting the term's own
    declaration used, so a non-ASCII name that Z3 pipe-quoted on export (see
    the module docstring — already correct, never renamed by
    :func:`_sanitize_for_smtlib`) would otherwise reach the caller as
    ``"|świątek|"`` rather than the true original ``"świątek"``. After
    unquoting, a name found in ``reverse`` (a digit-leading name this module
    DID rename) is translated back to its original; anything else — cvc5's
    own fresh model-value tokens (``"(as @S_0 S)"``, ``"(lambda (...) ...)"``,
    ...) included — passes through the unquoted form unchanged, since
    ``reverse.get(..., default)`` falls back to the unquoted string itself.
    """
    return {
        reverse.get(_unquote_smtlib(k), _unquote_smtlib(k)):
            reverse.get(_unquote_smtlib(v), _unquote_smtlib(v))
        for k, v in assignment.items()
    }


def _implication(formula: Node, premises: Sequence[Node]) -> Node:
    """Fold ``premises ⊨ φ`` into the single formula ``(∧ premises) → φ``.

    Reimplemented locally (rather than imported from
    :mod:`unicode_fol_kit.atp.protocol`) because the helper there is a
    private, unexported symbol — this module only imports protocol's public
    contract (:class:`ProverBackend`, :class:`Verdict`, the status
    constants).
    """
    premises = list(premises)
    if not premises:
        return formula
    conj = premises[0]
    for p in premises[1:]:
        conj = And(conj, p)
    return Implies(conj, formula)


def _timed(fn):
    """Run ``fn()`` returning ``(result, seconds)``."""
    start = time.perf_counter()
    result = fn()
    return result, time.perf_counter() - start


# ---------------------------------------------------------------------------
# Solver-version provenance (K1). cvc5 is a pip binding (``external = False``
# — see the class attribute below), not a spawned binary, so there is no
# ``--version`` subprocess to run and memoize the way
# ``atp.protocol._binary_version`` does for Vampire/Prover9/E/Zipperposition;
# the installed package's own distribution metadata is the analogous
# provenance, and it is exactly as immutable for the life of THIS process
# (the interpreter would have to restart to pick up a different install), so
# a one-slot memo is the same "ask once" discipline, just backed by
# ``importlib.metadata`` instead of a subprocess.
# ---------------------------------------------------------------------------

_VERSION_CACHE: Dict[str, Optional[str]] = {}


def _cvc5_package_version() -> Optional[str]:
    """The installed ``cvc5`` PyPI package's version, memoized process-wide.

    ``None`` when the package is not importable (mirrors
    :meth:`Cvc5Backend.available`) or its distribution metadata cannot be
    read for any reason (e.g. an editable/vendored install with no METADATA
    file) — best-effort provenance, never raises.
    """
    if "cvc5" in _VERSION_CACHE:
        return _VERSION_CACHE["cvc5"]
    version: Optional[str] = None
    if importlib.util.find_spec("cvc5") is not None:
        try:
            version = importlib.metadata.version("cvc5")
        except importlib.metadata.PackageNotFoundError:
            version = None
    _VERSION_CACHE["cvc5"] = version
    return version


class Cvc5Backend(ProverBackend):
    """Classical FOL/MSFOL via cvc5 — tri-state, with a model on refutation.

    Structurally the same contract as ``Z3Backend``: an entailment
    ``premises ⊨ formula`` is decided by asking whether the negated goal is
    UNSAT. ``proved`` and ``refuted`` are both fully trustworthy (cvc5's
    ``unsat``/``sat`` are sound and, on the quantifier-free fragment,
    complete); ``unknown`` only ever means cvc5's own instantiation search
    did not close the goal — never a silent downgrade of a real answer.

    Registered automatically: ``atp/protocol.py`` imports and registers this
    backend at the bottom of its own module, and its ``default_chain("fol")``
    inserts ``"cvc5"`` directly after ``"z3"`` whenever :meth:`available`
    is true — so on a machine with the optional ``cvc5`` extra installed, a
    plain ``prove()`` call runs cvc5 with zero caller action (see
    ``default_chain``'s docstring for why that one member is
    availability-dependent). This module itself never touches the registry.

    A PROVED verdict also carries a certificate in ``Verdict.proof``:
    ``{"kind": "cvc5_alethe", "text": <Alethe proof text>, "unsat_core":
    [<original-name term text>, ...]}``. Both are produced by cvc5's own
    ``getProof``/``proofToString``/``getUnsatCore`` on the SAME per-call
    ``cvc5.Solver()`` this backend already builds — no process-wide cvc5
    setting is ever touched, mirroring ``Z3Backend``'s own per-``Solver``
    discipline. ``unsat_core`` is SOUND (re-asserting just those terms is
    still unsat) but not necessarily MINIMAL — cvc5's core extraction is
    free to keep more than the smallest sufficient subset, exactly like
    ``Z3Backend``'s ``z3_unsat_core``. It also never contains one of the
    synthetic many-sorted non-emptiness axioms described below — see
    :meth:`_run`'s docstring for how that exclusion is done, since this
    backend's SMT-LIB2-replay route has no ``assert_and_track``-style
    tagged boolean to lean on the way ``Z3Backend``'s own core does.
    ``proof``/``unsat_core`` reading is
    best-effort (a format/version edge case degrades to ``None``/``[]``
    rather than turning a sound PROVED verdict into an ERROR one), and both
    are reverse-mapped back to original kit-level symbol names before they
    reach the caller — see :func:`_reverse_map_assignment`'s sibling
    treatment of the ``sat`` branch's ``countermodel``.

    **Many-sorted (MSFOL) soundness.** A sorted quantifier/constant/count
    lowers to a plain unary predicate guard (the same relativisation
    :class:`Z3Backend` relies on), which by itself carries no guarantee that
    the guarded sort is non-empty — and MSFOL, by convention, never gives a
    sort an empty universe (see the classical-reasoning guide's many-sorted
    section). :meth:`decide` closes that gap exactly like
    :class:`Z3Backend` does: it adds
    ``unicode_fol_kit.fol._msfl_nodes.nonempty_sort_axioms(formula, *premises)``
    as their own extra, UNNEGATED top-level assertions (one more
    ``(assert ...)`` command each, mirroring how every premise already gets
    its own — see :meth:`_run`'s docstring), never folded inside ``to_z3()``
    itself. These axioms use the sort's RAW kit-level name — the same
    (currently un-sanitised — see the module docstring's ASCII-legality
    section, a narrower, pre-existing gap this fix does not touch) name a
    sorted node's own lazy ``to_fol`` reduction already uses elsewhere in the
    same problem, so the two can never talk about different predicates.
    Empty for an unsorted query, so behaviour there is unchanged.
    """

    name = "cvc5"
    logics = frozenset({"fol"})
    external = False   # pip package (optional extra), not a spawned binary

    def available(self) -> bool:
        """Pure discovery: is the ``cvc5`` package importable? (No import.)"""
        return importlib.util.find_spec("cvc5") is not None

    def solver_version(self) -> Optional[str]:
        """The installed ``cvc5`` package's own distribution version
        (``importlib.metadata.version("cvc5")``), memoized process-wide —
        see :func:`_cvc5_package_version`. ``None`` when the package is not
        installed.
        """
        return _cvc5_package_version()

    def decide(self, formula: Node, premises: Sequence[Node] = (),
               timeout: int = 10000, **options) -> Verdict:
        """Decide ``premises ⊨ formula`` and return a :class:`Verdict`.

        Args:
            formula: the goal.
            premises: entailment premises (``⊨ formula`` when empty).
            timeout: milliseconds; forwarded to cvc5's ``tlimit`` option
                (``0``/negative disables the limit, matching cvc5's own
                "unlimited" default).
            **options: ``logic`` overrides the SMT-LIB logic string handed
                to cvc5 (default ``"ALL"`` — safe for any classical FOL/MSFOL
                fragment ``to_z3`` produces, since it is always a single
                uninterpreted sort with equality and uninterpreted
                functions/predicates, never arithmetic); ``random_seed``
                overrides cvc5's search seed (default ``42``, for
                reproducible verdicts across runs).

        Returns:
            A :class:`Verdict` with ``status`` in
            ``{"proved", "refuted", "unknown", "error"}``. Never raises for
            an in-contract ``Node`` — an unsupported fragment (``to_z3``
            raising ``NotImplementedError``, e.g. linear-logic/Lambek nodes)
            comes back UNKNOWN/``"unsupported"``; any failure in the
            SMT-LIB2 round trip through cvc5 itself comes back
            ERROR/``"infra"`` rather than propagating. A REFUTED verdict's
            ``countermodel["assignment"]`` names every symbol by its
            ORIGINAL kit-level name — see :func:`_reverse_map_assignment`
            and the module docstring's sanitisation section — never a
            digit-safe synthesised token, and never SMT-LIB2 ``|...|``
            quoting syntax wrapped around a non-ASCII one.
        """
        premises = list(premises)
        sanitised_nodes, name_map = _sanitize_many_for_smtlib(premises + [formula])
        *sanitised_premises, sanitised_formula = sanitised_nodes
        try:
            z3_premises = [p.to_z3() for p in sanitised_premises]
            z3_formula = sanitised_formula.to_z3()
            # Built from the ORIGINAL (pre-sanitisation) premises/formula and
            # translated straight to Z3, bypassing the SMT-LIB2 renaming map
            # entirely — see the class docstring's many-sorted-soundness
            # paragraph for why: these axioms must use the exact same raw
            # sort-predicate name a sorted node's own lazy relativisation
            # emits elsewhere in this same problem.
            z3_nonempty = [axiom.to_z3()
                          for axiom in nonempty_sort_axioms(*premises, formula)]
        except NotImplementedError as exc:
            return Verdict(UNKNOWN, self.name, reason="unsupported",
                           solver_version=self.solver_version(), detail=str(exc))

        logic = options.pop("logic", "ALL")
        random_seed = options.pop("random_seed", 42)
        # One importlib.metadata read, memoized process-wide (see
        # _cvc5_package_version) — cheap enough to call unconditionally on
        # every decide(), unlike the subprocess-spawning backends' own
        # solver_version() lookups.
        solver_version = self.solver_version()

        try:
            (kind, payload), elapsed = _timed(
                lambda: self._run(z3_formula, z3_premises, z3_nonempty,
                                  timeout, logic, random_seed))
        except Exception as exc:   # noqa: BLE001 - cvc5/z3 raise plain RuntimeError/etc.
            return Verdict(ERROR, self.name, reason="infra",
                           solver_version=solver_version,
                           detail=f"{type(exc).__name__}: {exc}")

        if kind == "unsat":
            proof = None
            if payload is not None:
                reverse = name_map.reverse()
                text = payload.get("proof_text")
                proof = {
                    "kind": "cvc5_alethe",
                    "text": reverse_map_text(text, reverse) if text is not None else None,
                    # An unsat CORE, per cvc5's own getUnsatCore() — sound
                    # (re-asserting just these terms is still unsat) but not
                    # necessarily MINIMAL, exactly like Z3Backend's core; see
                    # this backend's class docstring.
                    "unsat_core": [reverse_map_text(term, reverse)
                                   for term in payload.get("unsat_core", [])],
                }
            return Verdict(PROVED, self.name, wall_time=elapsed,
                           solver_version=solver_version, proof=proof)
        if kind == "sat":
            assignment = _reverse_map_assignment(payload, name_map.reverse())
            return Verdict(REFUTED, self.name, wall_time=elapsed,
                           solver_version=solver_version,
                           countermodel={"kind": "cvc5_model", "assignment": assignment})
        # kind == "unknown"
        return Verdict(UNKNOWN, self.name, reason=payload["reason"], wall_time=elapsed,
                       solver_version=solver_version, detail=payload["detail"])

    @staticmethod
    def _run(z3_formula, z3_premises: Sequence, z3_nonempty: Sequence, timeout: int,
             logic: str, random_seed: int):
        """Serialise ``z3_premises``/``z3_nonempty``/``¬z3_formula`` to
        SMT-LIB2 and decide with cvc5.

        Each of ``z3_premises``, ``z3_nonempty`` and ``Not(z3_formula)``
        becomes its OWN top-level Z3 ``.add()`` call, hence its OWN
        ``(assert ...)`` line in ``Solver.to_smt2()`` and its OWN
        ``assertFormula`` when replayed — see
        :func:`_sanitize_many_for_smtlib`'s docstring for why: cvc5's
        ``getUnsatCore()`` reports relevance per top-level assertion, so
        this is what lets it exclude an irrelevant premise instead of
        always naming "the whole conjoined problem". Logically identical to
        asserting one folded ``(∧ premises ∧ nonempty) → φ`` implication (a
        solver conjoins every assertion regardless of how many commands they
        arrived in) — this changes only the unsat-core bookkeeping.
        ``z3_premises`` are asserted FIRST, then ``z3_nonempty``, then the
        negated goal — :meth:`decide` keeps them as two separate arguments
        (rather than one pre-concatenated list) so this method knows exactly
        which assertion INDICES are the synthetic non-emptiness axioms once
        it needs to exclude them from the reported core below.

        Returns ``("unsat", proof_payload)``, ``("sat", assignment_dict)``,
        or ``("unknown", {"reason": ..., "detail": ...})``. ``proof_payload``
        is ``{"proof_text": str_or_None, "unsat_core": [term_text, ...]}``
        with every string still in cvc5's OWN (possibly sanitised) symbol
        names — :meth:`decide` reverse-maps it to original kit-level names,
        exactly like the ``sat`` branch's ``assignment``; this method stays a
        pure cvc5-API wrapper.

        ``unsat_core`` NEVER contains one of ``z3_nonempty`` — those are
        background MSFOL convention (every sort is non-empty), never one of
        the caller's own premises, mirroring how
        ``atp.protocol._z3_track_and_check`` asserts the identical axioms
        UNTRACKED so :class:`~unicode_fol_kit.atp.protocol.Z3Backend`'s own
        ``z3_unsat_core`` can never name them either (see that function's
        docstring). cvc5's SMT-LIB2-replay route here has no tagged-boolean
        ``assert_and_track`` equivalent to lean on, so exclusion instead
        matches each ``getUnsatCore()`` term against the non-emptiness slice
        of ``solver.getAssertions()`` (the SAME solver, in the SAME order
        just asserted above) by cvc5 ``Term`` equality — robust to cvc5's
        own core/assertion printers disagreeing on whitespace, and exact
        unless a CALLER-supplied premise is itself syntactically identical
        to one of the synthetic axioms (e.g. a premise that itself reads
        ``∃x (Ghost(x))`` for a sort literally named ``Ghost``), in which
        case that one coincidental duplicate is silently absorbed into the
        background fact instead of being listed twice — harmless, since
        ``unsat_core`` is already documented as sound-but-not-necessarily-
        minimal.

        Proof/core production is enabled unconditionally (Alethe format,
        per-``Solver``-instance only — this class never touches a
        process-wide cvc5 setting), but reading them back
        (:meth:`cvc5.Solver.getProof`/``proofToString``/``getUnsatCore``/
        ``getAssertions``) is best-effort: a failure there must not turn a
        genuinely sound ``unsat`` result into anything but PROVED, so it
        degrades to ``None``/an empty core rather than raising.
        """
        import cvc5
        from z3 import Solver as Z3Solver, Not as _ZNot

        z3_solver = Z3Solver()
        for z3_premise in z3_premises:
            z3_solver.add(z3_premise)
        for z3_axiom in z3_nonempty:
            z3_solver.add(z3_axiom)
        z3_solver.add(_ZNot(z3_formula))
        smt2_text = z3_solver.to_smt2()

        solver = cvc5.Solver()
        solver.setLogic(logic)
        solver.setOption("produce-models", "true")
        solver.setOption("produce-proofs", "true")
        solver.setOption("proof-format-mode", "alethe")
        solver.setOption("produce-unsat-cores", "true")
        solver.setOption("seed", str(random_seed))
        if timeout and timeout > 0:
            solver.setOption("tlimit", str(timeout))

        parser = cvc5.InputParser(solver)
        symbol_manager = parser.getSymbolManager()
        parser.setStringInput(cvc5.InputLanguage.SMT_LIB_2_6, smt2_text, "cvc5_backend")

        while True:
            command = parser.nextCommand()
            if command.isNull():
                break
            # The (check-sat) command in the replayed text is skipped so we
            # get a real cvc5.Result from checkSat() below, not its stringified
            # form from Command.invoke().
            if command.getCommandName() == "check-sat":
                continue
            command.invoke(solver, symbol_manager)

        result = solver.checkSat()

        if result.isUnsat():
            proof_text = None
            try:
                proofs = solver.getProof()
                if proofs:
                    # Verified single-lemma for the kit's uninterpreted-sort
                    # fragment (one whole-problem Alethe proof, no separate
                    # per-lemma structure) -- see this method's docstring.
                    raw = solver.proofToString(proofs[0])
                    proof_text = raw.decode("utf-8") if isinstance(raw, bytes) else raw
            except Exception:   # noqa: BLE001 - best-effort certificate, must not sink a sound PROVED verdict
                proof_text = None
            try:
                core = solver.getUnsatCore()
                # solver.getAssertions() replays in the SAME order the three
                # groups were asserted above: z3_premises, then z3_nonempty,
                # then Not(z3_formula) — slice out exactly the non-emptiness
                # group so it can be excluded from the reported core by
                # cvc5 Term equality (see this method's docstring).
                assertions = solver.getAssertions()
                n_premises = len(z3_premises)
                nonempty_terms = list(assertions[n_premises:n_premises + len(z3_nonempty)])
                core_terms = [str(term) for term in core if term not in nonempty_terms]
            except Exception:   # noqa: BLE001 - ditto
                core_terms = []
            return "unsat", {"proof_text": proof_text, "unsat_core": core_terms}
        if result.isSat():
            assignment = {}
            for term in symbol_manager.getDeclaredTerms():
                try:
                    assignment[str(term)] = str(solver.getValue(term))
                except Exception:   # noqa: BLE001 - best-effort witness, one symbol must not blank out the rest
                    continue
            return "sat", assignment

        explanation = result.getUnknownExplanation()
        reason = "timeout" if explanation == cvc5.UnknownExplanation.TIMEOUT else "incomplete"
        return "unknown", {"reason": reason, "detail": str(explanation)}
