"""Deductive verification layer for a collection of predicate definitions.

ChEBI2FOL (NeSy 2026) has an LLM translate ChEBI class definitions to FOL and
then classifies by MODEL CHECKING a definition against a molecule structure
(:mod:`unicode_fol_kit.semantics.model_eval`). That measures whether the
definitions are individually *useful* against real data (their holdout
micro-precision is 0.0363 at recall 0.8836 — the formulas are wildly too
general). It says nothing about whether the definitions are *coherent as a
theory*: an auxiliary predicate is optimised only in the context of the one
class that introduces it and then silently inherited by every subclass
("prone to overfitting to that specific context" — the paper's own words),
and OWL-subsumption checks against Vampire report only bewiesen/nicht bewiesen
(237 axioms: 171 proved, 56 not proved, 10 timeouts) with **no counterexample**
when a subsumption fails. This module is the layer that sits between "does
this predicate fire on real molecules" and "is this DEFINITION SET internally
consistent" — it never touches a molecule; every question here is decided
purely from the definitions' own logical content, via the kit's existing
prover chain (:mod:`unicode_fol_kit.atp.protocol`) and finite model finder.

Data model — why a plain ``name -> body`` mapping
---------------------------------------------------
A "definition" is a **named 0-ary predicate** with a defining FORMULA: exactly
the ``className <=> body`` shape the paper itself uses, e.g. (verbatim from
its appendix)::

    molecule <=> net_charge_neutral
    organicMolecularEntity <=> ?[A1]: (molecule & c(A1))
    carboxylicAcid <=> (carbonOxoacid & ?[A1,A2,A3]: (c(A1) & o(A2) & o(A3) &
                         has_1_hs(A3) & bDOUBLE(A1,A2) & bSINGLE(A1,A3)))

Every LHS here (``molecule``, ``organicMolecularEntity``, ``carboxylicAcid``,
``carbonOxoacid``) is used with NO arguments — a ChEBI class membership fact is
a global property of "the one molecule this structure represents"
(:class:`~unicode_fol_kit.semantics.structures.FiniteStructure` already builds
its 0-ary extension exactly this way: ``frozenset()`` or ``frozenset({()})``).
So this module represents a definition set as ``Mapping[str, Node]``: the key
is the defined 0-ary predicate's name, the value is its BODY (the right-hand
side of the ``<=>`` — never re-wrap it in ``Iff(Atom(name, ()), body)``, the
mapping key already carries the left-hand side). This is a deliberate,
narrower choice than a general "Definition object with parameters" — a
parametrised definition (``isRing(x) <=> ...``) would need a substitution-
with-arguments mechanic none of the paper's examples exercise; admitting it
here would be a real design expansion, not a small one, so a body atom that
names a defined predicate is only ever recognised as a USE of that definition
when it appears with ZERO arguments (:func:`dependency_graph`, :func:`unfold`)
— a same-named atom used elsewhere with arguments is simply a different,
primitive symbol, left completely alone.

Why unfolding is the hard part
-------------------------------
Definitions reference each other (``carboxylicAcid`` names ``carbonOxoacid``,
``organicMolecularEntity`` names ``molecule``), and a subsumption or
satisfiability question is only meaningful against the CLOSED formula in
terms of primitive (undefined) predicates — a prover asked to check
``carboxylicAcid -> carbonOxoacid`` while ``carbonOxoacid`` is still an
uninterpreted 0-ary atom would trivially fail to see that the axioms actually
force it (nothing tells the prover ``carbonOxoacid`` unfolds to anything).
:func:`unfold` collects that background theory correctly by *substituting*
every defined-predicate use with its own (recursively unfolded) body, so what
reaches the prover is a single sentence over only primitive vocabulary — no
separate list of background axioms is needed or possible, because a defined
0-ary predicate reused in two different bodies is DEFINITIONALLY (not just
materially) identical to its expansion everywhere, and substitution is the
operation that makes that identity explicit to a syntactic prover.

Plain substitution like this is only correct when every body is CLOSED
(no free variable): pasting a body verbatim into an enclosing definition's
own ``∃``/``∀`` scope would otherwise silently CAPTURE a free variable that
never meant to refer to that binder at all. :func:`unfold` therefore refuses
up front — see :class:`NonClosedDefinition` — rather than attempt
capture-avoiding (alpha-renaming) substitution: this module's data model is
0-ARY class-membership definitions (see "Data model" above), for which a
free variable is a malformed input, not a feature to accommodate.

Circular definitions are MEANINGLESS, not merely hard
-------------------------------------------------------
``className <=> P(..., className, ...)`` pins down no fact: any truth value
of ``className`` is self-consistent with such a biconditional (a fixed point
is not guaranteed to be UNIQUE — the classical case for why circular
"definitions" are not definitions at all). This module never guesses a
reading for one (least/greatest fixed point, etc.) — :func:`unfold` refuses
with :class:`CyclicDefinition` the moment substitution would revisit a name
already being expanded on the current path, and :func:`find_cycles` reports
every such cycle in the STATIC dependency graph up front so a caller can see
the problem without triggering it via a substitution call. A definition
reachable from a cycle cannot be unfolded at all, so :func:`check_satisfiable`
/ :func:`check_subsumption` report it as its own status, ``"cyclic"`` —
distinct from ``"unknown"`` (an honest "we could not decide this within the
budget") because a cyclic definition is not merely undecided, it is a PROVEN
defect in the definition set, on exactly the same footing as an unsatisfiable
one (see :attr:`TheoryReport.proved_problems`).

Three-valued honesty, end to end
-----------------------------------
Every check in this module returns one of a definitive PROVEN status
(``"unsatisfiable"`` / ``"entailed"`` / ``"refuted"``, the last always
carrying a countermodel — see :func:`check_subsumption`), the definitive
defect status ``"cyclic"``, or ``"unknown"``. ``"unknown"`` is never
downgraded to ``False``/``"refuted"`` and never upgraded to ``True``/
``"entailed"`` — a timeout, a step-bound, or an incomplete backend all mean
exactly "not decided", full stop, matching this kit's house rule (see
CLAUDE.md) that an unknown result is never reported as a false one.
:func:`check_satisfiable` and :func:`check_subsumption` are thin, honest
wrappers around :func:`unicode_fol_kit.api.prove` (which already returns this
same three/four-valued :class:`~unicode_fol_kit.atp.protocol.Verdict`
contract over its whole backend chain — Z3, the kit's own tableau/resolution
provers, and the finite model finder by default): they add nothing but the
unfolding step and the translation from "prove/refute a goal" to "is this
definition satisfiable" / "does this subsumption hold", so an unsatisfiable
result is exactly a Z3/tableau/resolution-checkable PROOF of a contradiction
and a refuted subsumption's countermodel is exactly the model the backend
that refuted it actually produced (never fabricated or approximated).

What this module is deliberately silent about
-------------------------------------------------
It never runs a definition against real data (that is model_eval's job) and
it never suggests a fix for a broken definition — it only proves, precisely,
THAT something is broken (dead classifier, meaningless cycle, missing
conjunct) and, for a refuted subsumption, exhibits WHY via a concrete
countermodel. That is the whole value-add over the paper's own Vampire check,
which reports only bewiesen/nicht bewiesen with no witness.
"""

from dataclasses import dataclass, field
from typing import Dict, FrozenSet, Mapping, Optional, Sequence, Tuple

from ..fol.nodes import Node, Atom, Not, Implies
from ..atp.protocol import PROVED, REFUTED, UNKNOWN

__all__ = [
    "Definitions",
    "CyclicDefinition", "UnfoldDepthExceeded", "NonClosedDefinition",
    "DEFAULT_MAX_DEPTH",
    "dependency_graph", "find_cycles", "unfold",
    "SatisfiabilityResult", "check_satisfiable",
    "SubsumptionResult", "check_subsumption",
    "TheoryReport", "check_theory",
]

#: A definition set: defined 0-ary predicate name -> its defining BODY (the
#: right-hand side of ``name <=> body``). See the module docstring's "Data
#: model" section for why this shape and not a parametrised Definition object.
Definitions = Mapping[str, Node]

#: How many nested definitional expansions :func:`unfold` will perform along
#: one substitution path before giving up with :class:`UnfoldDepthExceeded`.
#: Chosen generously relative to any real ChEBI-style class hierarchy (a
#: handful to a few dozen levels of subclassing) while still catching a
#: genuinely runaway/undetected-cycle situation instead of recursing forever.
DEFAULT_MAX_DEPTH = 50


# ---------------------------------------------------------------------------
# Errors
# ---------------------------------------------------------------------------

class CyclicDefinition(ValueError):
    """:func:`unfold` refuses to expand a definition through a cycle.

    Raised the moment substitution would revisit a name already being
    expanded on the CURRENT path (a live on-stack check, the standard DFS
    cycle test) — see the module docstring's "Circular definitions are
    MEANINGLESS" section for why this is a refusal, not an approximation.
    """


class UnfoldDepthExceeded(ValueError):
    """:func:`unfold`'s substitution chain exceeded ``max_depth`` without
    terminating in primitive-only vocabulary.

    This is a SEPARATE failure mode from :class:`CyclicDefinition`: the
    on-stack check catches every cycle regardless of depth, so hitting this
    instead means either a definition chain that is genuinely deeper than
    ``max_depth`` (raise it), or — mixed with sibling reuse of the same name
    at different points of a body — a combinatorial expansion that never
    revisits a name on any single path yet keeps growing (rare, but not
    provably impossible for a hand-written definition set); either way this
    is reported rather than silently truncating the formula.
    """


class NonClosedDefinition(ValueError):
    """:func:`unfold` refuses to substitute a definition body that is not a
    CLOSED sentence (has a free logical variable).

    Why this matters: :func:`unfold` substitutes a defined 0-ary atom
    IN PLACE, wherever it occurs — including inside an enclosing definition's
    own ``∃``/``∀`` scopes. If the substituted body itself has a free
    variable with the SAME NAME as one of those enclosing binders, plain
    (non-capture-avoiding) substitution silently re-binds it: the free
    occurrence, which denoted "whatever the definition's own body meant by
    that name" (nothing, since it was never bound — an ill-formed input to
    begin with), now denotes "the enclosing definition's witness" instead —
    two occurrences that do not denote the same thing get silently
    identified. That is a SOUNDNESS bug, not a decidability one, so it is
    caught up front rather than risked on every substitution.

    Why refuse rather than substitute capture-freely (alpha-rename the
    clashing binder before substituting): every definition in this module's
    data model is a 0-ARY class-membership fact (see the module docstring's
    "Data model" section) — its body is only ever quantified INTERNALLY
    (auxiliary existentials over its own chemical-substructure witnesses,
    say), never parametrised by a variable a caller substitutes in from
    outside. A body with a genuine free variable is therefore not a
    well-formed 0-ary definition at all — it is a typo, an accidentally
    unbound witness, or an attempt at a parametrised definition this module
    was never designed to represent (see the module docstring's "why a plain
    name -> body mapping" section: admitting parametrised definitions would
    be a real design expansion, not a small one). Capture-avoiding
    substitution would quietly accept and "fix" that malformed input by
    inventing a reading for it, rather than reporting the actual defect —
    exactly the kind of silent approximation this kit's house rules forbid.
    This mirrors the ``KeyError`` :func:`unfold` already raises for a name
    that is not even a key of ``definitions``: both are input-validation
    failures decided BEFORE any unfolding/proving work begins, not
    proof-budget questions like :class:`UnfoldDepthExceeded`.
    """


# ---------------------------------------------------------------------------
# Dependency graph / cycle detection
# ---------------------------------------------------------------------------

def _direct_uses(body: Node, definitions: Definitions) -> FrozenSet[str]:
    """The defined names ``body`` uses AS A DEFINITION (0-ary atom, name is a
    key of ``definitions``) — direct references only, not transitive."""
    used = set()
    for node in body.walk():
        if isinstance(node, Atom) and not node.args and node.predicate in definitions:
            used.add(node.predicate)
    return frozenset(used)


def dependency_graph(definitions: Definitions) -> Dict[str, FrozenSet[str]]:
    """Direct definitional dependencies: ``name -> frozenset(names it uses)``.

    A name is counted as "used" only where it occurs as a bare 0-ary atom
    whose predicate is itself a key of ``definitions`` — matching exactly what
    :func:`unfold` will substitute (see the module docstring). This is the
    DIRECT (one-hop) graph; :func:`find_cycles` walks it to find cycles, and
    a topological/transitive closure is deliberately not offered here — a
    caller that needs it can compute it from this graph, and adding it would
    just be more surface for something one line of graph code already covers.
    """
    return {name: _direct_uses(body, definitions) for name, body in definitions.items()}


def _normalize_cycle(cycle: Tuple[str, ...]) -> Tuple[str, ...]:
    """Canonical form of a cycle (``(n0, n1, ..., n0)``, first==last) for
    deduplication: rotate to start at the lexicographically smallest name,
    keeping direction (A->B->A and B->A->B are the SAME cycle; A->B->A and
    A->C->A, if both exist, are DIFFERENT cycles and stay distinct)."""
    core = cycle[:-1]
    best = None
    for i in range(len(core)):
        rotated = core[i:] + core[:i]
        candidate = rotated + (rotated[0],)
        if best is None or candidate < best:
            best = candidate
    return best


def find_cycles(definitions: Definitions) -> Tuple[Tuple[str, ...], ...]:
    """Every elementary cycle in the definitional dependency graph.

    Each cycle is a name sequence ``(n0, n1, ..., nk, n0)`` — first and last
    entry identical, tracing the dependency chain that closes the loop. A
    direct self-reference (``A <=> ... A ...``) appears as ``("A", "A")``.
    Results are deduplicated (see :func:`_normalize_cycle`) and returned in
    sorted order, so the output is deterministic regardless of dict iteration
    order.

    Implementation: plain DFS from every node with an explicit "on the current
    path" set — the standard cycle test, and exactly what :func:`unfold`'s
    live on-stack check also performs (this function just runs it eagerly,
    up front, over the whole graph, rather than only along the one path a
    particular :func:`unfold` call happens to take). Complexity is bounded by
    the number of simple paths in the graph, which is fine for a definition
    set the size of a class hierarchy (sparse, near-tree-shaped with the
    occasional bug introducing a 2-3 node loop) but is NOT guaranteed
    polynomial on a dense graph — this is a correctness-first, not a
    scalability-first, implementation.
    """
    deps = dependency_graph(definitions)
    cycles: set = set()

    def dfs(node: str, path: Tuple[str, ...], on_path: FrozenSet[str]) -> None:
        for nxt in sorted(deps.get(node, ())):
            if nxt in on_path:
                idx = path.index(nxt)
                cycles.add(_normalize_cycle(path[idx:] + (nxt,)))
            else:
                dfs(nxt, path + (nxt,), on_path | {nxt})

    for start in sorted(deps):
        dfs(start, (start,), frozenset({start}))

    return tuple(sorted(cycles))


# ---------------------------------------------------------------------------
# Unfolding
# ---------------------------------------------------------------------------

def _require_closed_definitions(definitions: Definitions) -> None:
    """Raise :class:`NonClosedDefinition` if any body in ``definitions`` is
    not a closed sentence.

    Reuses :func:`unicode_fol_kit.eval.validate.validate`'s own closedness
    check (``ValidationReport.is_closed``, which counts a free ``Variable``
    OR a free ``LambdaVar`` against closedness) rather than reimplementing
    it. Checks EVERY body in ``definitions``, not just ones reachable from a
    particular call's starting name: :func:`unfold`'s substitution walk can
    reach any definition transitively, and which ones it actually reaches
    depends on ``name`` and on the bodies themselves, so a check narrower
    than "the whole set" would make whether a malformed body gets caught
    depend on which name happens to be unfolded first — see
    :class:`NonClosedDefinition` for why this is refused at all.
    """
    from .validate import validate  # lazy: mirrors this module's other lazy imports

    offenders = []
    for name, body in definitions.items():
        report = validate(body)
        if not report.is_closed:
            offenders.append((name, report.free_variable_names))
    if offenders:
        detail = "; ".join(
            f"{name!r} has free variable(s) {', '.join(free_names)}"
            for name, free_names in offenders
        )
        raise NonClosedDefinition(
            "unfold: every definition body must be a CLOSED sentence — this "
            "module's data model is 0-ary class-membership definitions, not "
            f"parametrised ones (see the module docstring): {detail}. See "
            "NonClosedDefinition's docstring for why this is refused rather "
            "than patched via capture-avoiding substitution."
        )


def _substitute(node: Node, definitions: Definitions, active: Tuple[str, ...],
                depth: int, max_depth: int) -> Node:
    """Recursively replace every 0-ary defined-predicate atom in ``node`` with
    its (further-unfolded) body. ``active`` is the ordered stack of names
    currently being expanded ON THIS PATH — membership in it is the live
    cycle check; ``depth`` is how many substitutions deep this path already
    is. Sibling reuse of the same name (e.g. ``A & A`` in one body) is NOT a
    cycle: each occurrence recurses independently with the SAME ``active``/
    ``depth`` it was called with, since neither branch is "inside" the
    other's expansion."""
    if isinstance(node, Atom) and not node.args and node.predicate in definitions:
        pred = node.predicate
        if pred in active:
            raise CyclicDefinition(
                f"unfold: definitional cycle detected: {' -> '.join(active + (pred,))} "
                "— a circular biconditional like this pins down no fact (any truth "
                "value is self-consistent with it), so it is refused rather than "
                "evaluated. See find_cycles() to locate every such cycle up front."
            )
        if depth >= max_depth:
            raise UnfoldDepthExceeded(
                f"unfold: expanding {active[0]!r} did not reach a primitive-only "
                f"formula within max_depth={max_depth} steps (currently expanding: "
                f"{' -> '.join(active + (pred,))}). Raise max_depth if this chain is "
                "genuinely this deep, or check find_cycles() for an undetected cycle."
            )
        body = definitions[pred]
        return _substitute(body, definitions, active + (pred,), depth + 1, max_depth)
    return node.map_children(
        lambda c: _substitute(c, definitions, active, depth, max_depth))


def unfold(name: str, definitions: Definitions, *,
          max_depth: int = DEFAULT_MAX_DEPTH) -> Node:
    """Expand ``definitions[name]`` until only primitive predicates remain.

    Every 0-ary atom in the body whose predicate is itself a key of
    ``definitions`` is replaced by that key's own (recursively unfolded)
    body — see the module docstring's "Why unfolding is the hard part". The
    result is a single formula a prover can check directly, with no separate
    background-axiom list needed (there is nothing FOR such a list to say
    that substitution has not already said).

    Raises:
        KeyError: ``name`` is not a key of ``definitions``.
        NonClosedDefinition: some body in ``definitions`` has a free
            variable — checked over the WHOLE ``definitions`` mapping before
            any substitution begins (see :class:`NonClosedDefinition` for
            why: substituting a non-closed body can silently capture its
            free variable in an unrelated enclosing binder of the same
            name).
        CyclicDefinition: expanding ``name`` would revisit a name already
            being expanded on the current path — see :func:`find_cycles` to
            locate the cycle without triggering this.
        UnfoldDepthExceeded: the expansion did not terminate within
            ``max_depth`` nested substitutions.
    """
    if name not in definitions:
        raise KeyError(
            f"unfold: {name!r} is not a defined name (known: {sorted(definitions)})")
    _require_closed_definitions(definitions)
    return _substitute(definitions[name], definitions, (name,), 0, max_depth)


# ---------------------------------------------------------------------------
# Satisfiability
# ---------------------------------------------------------------------------

_SATISFIABILITY_STATUSES = ("satisfiable", "unsatisfiable", "unknown", "cyclic")


@dataclass(frozen=True)
class SatisfiabilityResult:
    """Outcome of :func:`check_satisfiable`.

    ``status``:
        ``"unsatisfiable"`` — PROVEN: the unfolded definition is a
            contradiction, so ``name`` can hold of no possible molecule/object
            whatsoever — a dead classifier that silently returns 0 matches
            forever. ``detail`` names the backend that proved it.
        ``"satisfiable"`` — PROVEN: some model makes ``name`` true.
            ``witness`` is that model, in the SAME JSON-able shape as
            :attr:`unicode_fol_kit.atp.protocol.Verdict.countermodel`
            (``{"kind": ..., ...}``) — it may occasionally be ``None`` even
            on this status, for a backend that can refute unsatisfiability
            without producing a readable model (rare; the default chain's
            Z3/model-finder members always attach one).
        ``"unknown"`` — neither was established within the backend chain's
            budget. NEVER a claim of unsatisfiability — see the module
            docstring's three-valued-honesty section.
        ``"cyclic"`` — ``name`` could not even be unfolded (it is reachable
            from a definitional cycle); ``unfolded`` is ``None`` in this case.
            This is its own PROVEN-defect status, not folded into
            ``"unknown"`` — see :func:`find_cycles`.
    """

    name: str
    status: str
    unfolded: Optional[Node]
    witness: Optional[dict]
    backend: Optional[str]
    detail: Optional[str]

    def __post_init__(self):
        if self.status not in _SATISFIABILITY_STATUSES:
            raise ValueError(
                f"SatisfiabilityResult: unknown status {self.status!r} "
                f"(use one of {_SATISFIABILITY_STATUSES})")

    def to_dict(self) -> dict:
        return {
            "name": self.name,
            "status": self.status,
            "unfolded": self.unfolded.to_dict() if self.unfolded is not None else None,
            "witness": self.witness,
            "backend": self.backend,
            "detail": self.detail,
        }


def check_satisfiable(name: str, definitions: Definitions, *,
                      timeout: int = 10000,
                      backends: Optional[Sequence[str]] = None,
                      max_depth: int = DEFAULT_MAX_DEPTH,
                      **options) -> SatisfiabilityResult:
    """Is ``name``'s (unfolded) definition satisfiable by ANY object at all?

    Decided by handing ``Not(unfold(name, definitions))`` to
    :func:`unicode_fol_kit.api.prove` (empty premises, i.e. a validity check)
    over its FOL backend chain (Z3, the kit's tableau/resolution provers, and
    the finite model finder, by default — see
    :func:`unicode_fol_kit.atp.protocol.default_chain`): proving
    ``¬unfolded`` valid is exactly proving ``unfolded`` unsatisfiable, and
    REFUTING ``¬unfolded`` means some backend produced an actual model of
    ``unfolded`` — a genuine, checkable witness rather than a guess. This is
    the "und/oder api.prove" reading: the model finder is already one member
    of that chain, so this one call already uses both routes the finder and
    the prover can offer.

    ``backends``/``timeout``/``**options`` are forwarded verbatim to
    :func:`~unicode_fol_kit.api.prove` — as there, extra ``options`` (e.g.
    ``max_steps=``) are sent to EVERY backend in the chain, so only combine
    them with an explicit single-backend ``backends=[...]`` list unless every
    member of the chain genuinely accepts that keyword.

    Raises:
        KeyError: ``name`` is not a key of ``definitions``.
        NonClosedDefinition: some body in ``definitions`` is not closed —
            see :func:`unfold`.
    """
    if name not in definitions:
        raise KeyError(
            f"check_satisfiable: {name!r} is not a defined name "
            f"(known: {sorted(definitions)})")
    try:
        unfolded = unfold(name, definitions, max_depth=max_depth)
    except CyclicDefinition as exc:
        return SatisfiabilityResult(name=name, status="cyclic", unfolded=None,
                                    witness=None, backend=None, detail=str(exc))
    except UnfoldDepthExceeded as exc:
        # NOT the same finding as CyclicDefinition: budget exhaustion proves
        # nothing about whether name's definition chain is actually acyclic
        # (it may well be a long but perfectly acyclic hierarchy — see
        # UnfoldDepthExceeded's own docstring) — reporting "cyclic" here would
        # upgrade an undecided budget question into a PROVEN-defect claim
        # (see TheoryReport.proved_problems, which treats "cyclic" as exactly
        # that). Honest status is "unknown".
        return SatisfiabilityResult(name=name, status="unknown", unfolded=None,
                                    witness=None, backend=None, detail=str(exc))

    from .. import api  # lazy: avoids importing the whole facade at module load

    verdict = api.prove(Not(unfolded), timeout=timeout, backends=backends, **options)
    if verdict.status == PROVED:
        return SatisfiabilityResult(
            name=name, status="unsatisfiable", unfolded=unfolded, witness=None,
            backend=verdict.backend,
            detail=f"{name} can hold of no object: its unfolded definition is a "
                   f"contradiction, proved by {verdict.backend}.")
    if verdict.status == REFUTED:
        return SatisfiabilityResult(
            name=name, status="satisfiable", unfolded=unfolded,
            witness=verdict.countermodel, backend=verdict.backend,
            detail=f"a model satisfying {name} was found by {verdict.backend}.")
    return SatisfiabilityResult(
        name=name, status="unknown", unfolded=unfolded, witness=None,
        backend=verdict.backend if verdict.backend != "chain" else None,
        detail=verdict.detail or "neither proved unsatisfiable nor witnessed "
                                  "satisfiable within the given backend budget")


# ---------------------------------------------------------------------------
# Subsumption
# ---------------------------------------------------------------------------

_SUBSUMPTION_STATUSES = ("entailed", "refuted", "unknown", "cyclic")


@dataclass(frozen=True)
class SubsumptionResult:
    """Outcome of :func:`check_subsumption` — does ``Def(sub) |= Def(sup)``?

    ``status``:
        ``"entailed"`` — PROVEN: every object satisfying ``sub``'s unfolded
            definition also satisfies ``sup``'s.
        ``"refuted"`` — PROVEN false: ``countermodel`` is ALWAYS populated
            here (never ``None`` — see the defensive fallback in
            :func:`check_subsumption`'s implementation), a concrete witness
            where ``sub`` holds and ``sup`` does not. This is the module's
            main value-add over the paper's Vampire-only "not proved": a
            reader can see EXACTLY which conjunct of the superclass the
            subclass definition forgot.
        ``"unknown"`` — neither proved nor refuted within the backend
            budget (e.g. a timeout, or a deliberately tiny step bound) —
            NEVER reported as ``"refuted"``.
        ``"cyclic"`` — ``sub`` or ``sup`` could not be unfolded (reachable
            from a definitional cycle); ``verdict``/``countermodel`` are
            ``None`` in this case.

    ``verdict`` is the underlying :class:`~unicode_fol_kit.atp.protocol.Verdict`
    (as a dict, via its own ``to_dict()``) for full provenance — ``None`` only
    for ``"cyclic"``. ``explanation`` is a short plain-English gloss: for
    ``"refuted"`` it is built the same way ``api.countermodel`` builds
    ``explanation_nl`` (:func:`unicode_fol_kit.eval.explain.explain_countermodel`),
    for every other status it falls back to the verdict's own ``detail``/the
    cycle message.
    """

    sub: str
    sup: str
    status: str
    verdict: Optional[dict]
    countermodel: Optional[dict]
    explanation: Optional[str]

    def __post_init__(self):
        if self.status not in _SUBSUMPTION_STATUSES:
            raise ValueError(
                f"SubsumptionResult: unknown status {self.status!r} "
                f"(use one of {_SUBSUMPTION_STATUSES})")
        if self.status == "refuted" and self.countermodel is None:
            raise ValueError(
                "SubsumptionResult: status='refuted' must always carry a "
                "countermodel — a refutation claim with no witness is exactly "
                "what this module exists to never emit (see check_subsumption's "
                "defensive fallback, which downgrades to 'unknown' instead of "
                "constructing a result like this).")

    def to_dict(self) -> dict:
        return {
            "sub": self.sub,
            "sup": self.sup,
            "status": self.status,
            "verdict": self.verdict,
            "countermodel": self.countermodel,
            "explanation": self.explanation,
        }


def check_subsumption(sub: str, sup: str, definitions: Definitions, *,
                      timeout: int = 10000,
                      backends: Optional[Sequence[str]] = None,
                      max_depth: int = DEFAULT_MAX_DEPTH,
                      **options) -> SubsumptionResult:
    """Does ``Def(sub)`` entail ``Def(sup)`` — ``sub`` really a subclass?

    Both definitions are unfolded (see :func:`unfold`), and
    :func:`unicode_fol_kit.api.prove` is asked to decide
    ``unfold(sub) -> unfold(sup)`` (empty premises: a plain validity check of
    the implication) over its FOL backend chain. A ``"refuted"`` result is
    NEVER handed back without a countermodel: if the chain's own
    :class:`~unicode_fol_kit.atp.protocol.Verdict` reports REFUTED but (for
    some backend combination) carries no witness, :func:`api.countermodel`
    is tried once more before conceding — and if that also finds nothing,
    the result is downgraded to ``"unknown"`` rather than asserting an
    unwitnessed refutation (see :class:`SubsumptionResult`'s invariant).

    ``backends``/``timeout``/``**options`` are forwarded verbatim to
    :func:`~unicode_fol_kit.api.prove` — see :func:`check_satisfiable`'s
    docstring for the same caveat about mixing ``**options`` with a
    multi-backend chain.

    Raises:
        KeyError: ``sub`` or ``sup`` is not a key of ``definitions``.
        NonClosedDefinition: some body in ``definitions`` is not closed —
            see :func:`unfold`.
    """
    for role, class_name in (("sub", sub), ("sup", sup)):
        if class_name not in definitions:
            raise KeyError(
                f"check_subsumption: {role}={class_name!r} is not a defined name "
                f"(known: {sorted(definitions)})")

    try:
        unfolded_sub = unfold(sub, definitions, max_depth=max_depth)
        unfolded_sup = unfold(sup, definitions, max_depth=max_depth)
    except CyclicDefinition as exc:
        return SubsumptionResult(sub=sub, sup=sup, status="cyclic", verdict=None,
                                 countermodel=None, explanation=str(exc))
    except UnfoldDepthExceeded as exc:
        # See check_satisfiable's identical split: a depth-budget exhaustion
        # is not a proof of a cycle (find_cycles proves that structurally,
        # via find_cycles/CyclicDefinition), so it must not be reported as
        # "cyclic" — that status is documented (TheoryReport.proved_problems)
        # as a PROVEN defect. Honest status is "unknown".
        return SubsumptionResult(sub=sub, sup=sup, status="unknown", verdict=None,
                                 countermodel=None, explanation=str(exc))

    from .. import api  # lazy, matching check_satisfiable

    goal = Implies(unfolded_sub, unfolded_sup)
    verdict = api.prove(goal, timeout=timeout, backends=backends, **options)

    if verdict.status == PROVED:
        return SubsumptionResult(
            sub=sub, sup=sup, status="entailed", verdict=verdict.to_dict(),
            countermodel=None,
            explanation=f"Def({sub}) |= Def({sup}) — proved by {verdict.backend}.")

    if verdict.status == REFUTED:
        countermodel = verdict.countermodel
        if countermodel is None:
            # Defensive fallback: every default-chain member that can REFUTE
            # (z3, modelfinder) already attaches one, but a caller-supplied
            # backends= list could in principle name one that cannot (see
            # VampireBackend's documented CounterSatisfiable-without-model
            # case). Try the dedicated countermodel search once before
            # conceding — see the module/class docstrings for why an
            # unwitnessed "refuted" is never acceptable here.
            cm_result = api.countermodel(goal, timeout=timeout, backends=backends)
            countermodel = cm_result.model if cm_result.found else None
        if countermodel is None:
            return SubsumptionResult(
                sub=sub, sup=sup, status="unknown", verdict=verdict.to_dict(),
                countermodel=None,
                explanation="a backend reported refutation without a recoverable "
                            "countermodel witness; treated as undecided rather "
                            "than asserting an unwitnessed refutation.")
        explanation = None
        try:
            from .explain import explain_countermodel
            explanation = explain_countermodel(countermodel)
        except Exception:
            pass
        if explanation is None:
            explanation = (f"{verdict.backend} found a countermodel: {sub} holds "
                           f"but {sup} does not.")
        return SubsumptionResult(
            sub=sub, sup=sup, status="refuted", verdict=verdict.to_dict(),
            countermodel=countermodel, explanation=explanation)

    return SubsumptionResult(
        sub=sub, sup=sup, status="unknown", verdict=verdict.to_dict(),
        countermodel=None,
        explanation=verdict.detail or "neither proved nor refuted within the "
                                       "given backend budget")


# ---------------------------------------------------------------------------
# Whole-theory report
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class TheoryReport:
    """The combined verification result over a definition set.

    ``cycles`` is :func:`find_cycles`'s output (the authoritative structural
    view — a name inside a cycle also shows up with ``status="cyclic"`` in
    ``satisfiability``/``subsumptions``, individually, but ``cycles`` is what
    names the actual loop). ``satisfiability`` covers EVERY name in the
    definition set (not just ones mentioned in ``subsumptions``); a dead
    classifier is exactly as reportable on its own as a broken subsumption.

    :attr:`proved_problems` / :attr:`undecided` are the split the module
    docstring promises: the first is every finding this module actually
    PROVED (a cycle, an unsatisfiable definition, a refuted subsumption —
    each with its evidence), the second is every finding that stayed
    genuinely open. A caller building a pass/fail gate should fail on the
    first and merely flag the second for human attention.
    """

    cycles: Tuple[Tuple[str, ...], ...]
    satisfiability: Mapping[str, SatisfiabilityResult]
    subsumptions: Tuple[SubsumptionResult, ...]

    @property
    def proved_problems(self) -> Tuple[dict, ...]:
        """Every DEFINITIVELY established defect — never an 'unknown'."""
        problems = []
        for cycle in self.cycles:
            problems.append({"kind": "cycle", "names": list(cycle)})
        for name, result in sorted(self.satisfiability.items()):
            if result.status == "unsatisfiable":
                problems.append({"kind": "unsatisfiable", "name": name,
                                 "detail": result.detail})
        for result in self.subsumptions:
            if result.status == "refuted":
                problems.append({"kind": "subsumption_refuted", "sub": result.sub,
                                 "sup": result.sup, "explanation": result.explanation})
        return tuple(problems)

    @property
    def undecided(self) -> Tuple[dict, ...]:
        """Every check that ended in 'unknown' — genuinely open, not a defect."""
        open_items = []
        for name, result in sorted(self.satisfiability.items()):
            if result.status == "unknown":
                open_items.append({"kind": "satisfiability", "name": name,
                                   "detail": result.detail})
        for result in self.subsumptions:
            if result.status == "unknown":
                open_items.append({"kind": "subsumption", "sub": result.sub,
                                   "sup": result.sup, "detail": result.explanation})
        return tuple(open_items)

    def to_dict(self) -> dict:
        return {
            "cycles": [list(c) for c in self.cycles],
            "satisfiability": {name: r.to_dict()
                               for name, r in sorted(self.satisfiability.items())},
            "subsumptions": [r.to_dict() for r in self.subsumptions],
            "proved_problems": list(self.proved_problems),
            "undecided": list(self.undecided),
        }


def check_theory(definitions: Definitions, *,
                 subsumptions: Sequence[Tuple[str, str]] = (),
                 timeout: int = 10000,
                 backends: Optional[Sequence[str]] = None,
                 max_depth: int = DEFAULT_MAX_DEPTH,
                 **options) -> TheoryReport:
    """Run every check this module offers over a whole definition set.

    Cycles (:func:`find_cycles`), satisfiability of every definition
    (:func:`check_satisfiable`, one call per name), and every requested
    subsumption pair (:func:`check_subsumption`, one call per pair in
    ``subsumptions``) — see :class:`TheoryReport` for how the results are
    organised and split into proved-vs-undecided. ``timeout``/``backends``/
    ``max_depth``/``**options`` apply uniformly to every underlying call.

    Raises:
        KeyError: a name in ``subsumptions`` is not a key of ``definitions``.
        NonClosedDefinition: some body in ``definitions`` is not closed —
            see :func:`unfold`. Raised by the first underlying
            :func:`check_satisfiable`/:func:`check_subsumption` call that
            reaches it, so ``cycles`` (computed first, structurally, with no
            unfolding involved) is never the cause of this and is simply not
            returned when it happens.
    """
    cycles = find_cycles(definitions)
    satisfiability = {
        name: check_satisfiable(name, definitions, timeout=timeout,
                                backends=backends, max_depth=max_depth, **options)
        for name in sorted(definitions)
    }
    sub_results = tuple(
        check_subsumption(sub, sup, definitions, timeout=timeout,
                          backends=backends, max_depth=max_depth, **options)
        for sub, sup in subsumptions
    )
    return TheoryReport(cycles=cycles, satisfiability=satisfiability,
                        subsumptions=sub_results)
