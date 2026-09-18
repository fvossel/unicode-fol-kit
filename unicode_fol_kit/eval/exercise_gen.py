"""Constructively-generated, independently-checked practice exercises.

This is teaching infrastructure, not an evaluator: everything else in
:mod:`unicode_fol_kit.eval` assumes an LLM (or a student) already produced a
formula that needs SCORING against a gold answer. This module runs the other
direction — it MANUFACTURES the exercise (formula, proof, or theory) itself,
purely constructively, with **no LLM involved anywhere**. Every answer key is
either decided by a genuine decision procedure or assembled by hand from sound
primitives and then re-checked by an INDEPENDENT route before it is returned,
so a bug here can make a generator *refuse* or *retry* but never ship a wrong
answer key.

Three generators, each deliberately narrower than the roadmap's original
framing, to avoid two claims this kit's own primitives cannot actually
support (see each function's docstring for the full argument):

* :func:`generate_valid_invalid_pair` — samples a quantifier-free formula
  over the **propositional fragment** (0-ary predicates from ``signature``,
  each one an opaque proposition) and classifies it with
  :func:`~unicode_fol_kit.semantics.truthtable.truth_table` — a genuine,
  complete decision procedure for that fragment, no caveats. A first-order
  variant (quantified formulas, classified by countermodel-search-plus-proof)
  is explicitly OUT OF SCOPE here: it would need both a countermodel miss
  (bounded, hence never a proof of validity on its own) AND a positive proof
  from a refutation-complete backend before a "valid" label was honest, and
  the roadmap itself flags this as a stretch goal, not this module's job.

* :func:`generate_entailment_with_proof` — does **not** search for a proof of
  a given depth. :func:`~unicode_fol_kit.atp.fitch_search.find_fitch_proof`'s
  own docstring is explicit that a depth-bounded search returning ``None``
  means "no proof found within the bound", never "not a theorem" — so "no
  proof found at depth d−1" can never certify that a proof of depth d is
  *minimal*. Instead this generator builds the answer key CONSTRUCTIVELY,
  composing :mod:`unicode_fol_kit.atp.fitch`'s ``Proof``/``Subproof``/``Line``
  primitives bottom-up into a derivation with EXACTLY the requested number of
  nested subproof levels, then verifies it with the existing checker
  (``verify_proof`` — "soundness is free", per that module's own docstring).
  The claim shipped is "the worked solution has depth N", never "the minimal
  proof has depth N" — exactly how a textbook exercise is actually authored.

* :func:`generate_theory_with_model_size` — samples a small finite theory (a
  strict total order over one binary relation from ``signature``, forced to
  contain a chain of the requested length) and confirms BOTH that a model of
  exactly the target size exists AND that no smaller one does. The second
  half is the subtle part: :func:`~unicode_fol_kit.semantics.modelfinder.find_model`
  conflates "this size was searched and refuted" with "this size was SKIPPED
  because its interpretation space exceeded ``max_candidates``" — both look
  like plain absence from outside. This generator therefore also calls the
  new :func:`~unicode_fol_kit.semantics.modelfinder.is_size_exhaustive` helper
  for every size below the target and refuses (``ValueError``, never a
  silent wrong "minimal size" claim) if any of them was only skipped.

Determinism. Every generator takes an optional ``seed``; the SAME seed always
produces a BYTE-IDENTICAL exercise (same AST, same ``to_unicode_str()``
rendering, same proof, same witness structure) — see
``tests/test_exercise_gen.py``'s reproducibility tests, which pin this
directly. ``seed=None`` draws from unseeded system randomness instead.
Caveat for :class:`ModelSizeExercise`: "byte-identical" describes its
*content*, not what ``==`` reports — its ``witness`` field is a
:class:`~unicode_fol_kit.semantics.tarski.Structure`, which defines no
``__eq__`` and so compares by object identity. Two exercises built from the
same seed are content-identical but ``exercise1 == exercise2`` is always
``False``; compare ``witness.domain`` / ``witness.constants`` /
``witness.predicates`` / ``witness.sorts`` field-by-field instead (see
``ModelSizeExercise``'s own docstring, and how the reproducibility test for
this generator does it).

Deviations from the roadmap draft that produced this module (recorded here
rather than silently "fixed", per this kit's convention):

* The draft's test-oracle text names ``semantics.evaluator.models`` as the
  independent countermodel checker; no ``unicode_fol_kit.semantics.evaluator``
  module exists. The actual function, used throughout this module and its
  tests, is :func:`unicode_fol_kit.semantics.tarski.models`.
* The draft names ``docs/guide/teaching.md`` as the surfacing page; the
  accepted filename for this batch is ``docs/guide/exercises.md`` (see that
  file).
* No MCP tool is added here: ``unicode_fol_kit/mcp/server.py`` is outside
  this module's ownership for this change.
"""

import random
from dataclasses import dataclass
from functools import reduce
from typing import Dict, List, Mapping, Optional, Sequence, Tuple, Union

from ..fol.nodes import Atom, And, Implies, Node, Not, Or, Quantifier, Variable
from ..fol.signature import Signature
from ..semantics import modelfinder
from ..semantics.tarski import Structure, models
from ..semantics.truthtable import TruthTable, truth_table
from ..atp.fitch import Line, Proof, Subproof, assume, line, verify_proof

__all__ = [
    "ValidInvalidPair", "generate_valid_invalid_pair",
    "EntailmentExercise", "generate_entailment_with_proof",
    "ModelSizeExercise", "generate_theory_with_model_size",
]

#: How many random samples a generator tries before falling back to a
#: deterministic, formula-shape-guaranteed construction (see
#: ``generate_valid_invalid_pair``). Generous relative to how quickly a small
#: random propositional formula tends to land on either side of "tautology",
#: so the fallback is rarely exercised in practice; it exists purely so every
#: call TERMINATES, never so a returned label is trusted without the
#: post-construction self-check that follows it either way.
_RETRY_BUDGET = 60


# ---------------------------------------------------------------------------
# Shared: the propositional atom pool a signature offers, and a small
# seeded quantifier-free grammar over it.
# ---------------------------------------------------------------------------

def _nullary_atoms(signature: Signature) -> Tuple[Atom, ...]:
    """The 0-ary predicates ``signature`` declares, as bare :class:`Atom` nodes.

    Sorted by name first so the pool itself is deterministic across calls
    with the same ``signature`` regardless of dict iteration order; the
    caller's ``seed`` then governs which of them are actually picked.
    """
    return tuple(
        Atom(name, ())
        for name, decl in sorted(signature.predicates.items())
        if decl.arity == 0
    )


def _random_prop_formula(rng: random.Random, atoms: Sequence[Atom], budget: int) -> Node:
    """A random quantifier-free formula over ``atoms``, using only the AST
    constructors ``And``/``Or``/``Not``/``Implies``/``Atom`` (per the roadmap
    spec). ``budget`` bounds the recursion so a call always terminates and the
    result stays exercise-sized; it is consumed by one per connective, and a
    leaf (bare atom, or its negation) can also be chosen early at random.
    """
    if budget <= 0 or rng.random() < 0.4:
        atom = rng.choice(atoms)
        return Not(atom) if rng.random() < 0.3 else atom
    op = rng.choice(("and", "or", "implies", "not"))
    if op == "not":
        return Not(_random_prop_formula(rng, atoms, budget - 1))
    left = _random_prop_formula(rng, atoms, budget - 1)
    right = _random_prop_formula(rng, atoms, budget - 1)
    cls = {"and": And, "or": Or, "implies": Implies}[op]
    return cls(left, right)


def _first_countermodel(table: TruthTable) -> Dict[str, bool]:
    """The first (in row order) non-designated valuation of ``table`` as an
    ``{atom_surface_form: bool}`` mapping. Requires ``table`` to actually have
    one (i.e. not be a tautology) — callers check that first.
    """
    for assignment, _value, designated in table.rows:
        if not designated:
            return {atom: bool(v) for atom, v in zip(table.atoms, assignment)}
    raise AssertionError(  # pragma: no cover — callers only reach this for a non-tautology
        "internal: _first_countermodel called on a tautology (no falsifying row)."
    )


def _nullary_structure(valuation: Mapping[str, bool]) -> Structure:
    """A minimal :class:`Structure` encoding a propositional valuation.

    One dummy individual as domain (no term in a nullary-atom formula ever
    needs more) and each atom mapped to its truth value at ``(name, 0)`` —
    exactly :class:`Structure`'s own documented nullary-predicate convention,
    so :func:`~unicode_fol_kit.semantics.tarski.models` reads it correctly.
    """
    return Structure(domain=("*",), predicates={(name, 0): bool(v) for name, v in valuation.items()})


# ---------------------------------------------------------------------------
# 1. generate_valid_invalid_pair
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class ValidInvalidPair:
    """One valid (tautologous) and one invalid (non-tautologous) propositional
    formula, sampled over the same atom pool.

    ``invalid_valuation`` is a genuine falsifying assignment for
    ``invalid_formula`` — a plain ``{atom_surface_form: bool}`` mapping, chosen
    so a caller (or a test) can rebuild a
    :class:`~unicode_fol_kit.semantics.tarski.Structure` from it independently
    of how this module built its own (see
    :func:`~unicode_fol_kit.semantics.tarski.models`). ``atoms`` is the pool
    this pair was sampled from — not necessarily every atom in it appears in
    either formula.
    """

    valid_formula: Node
    invalid_formula: Node
    invalid_valuation: Mapping[str, bool]
    atoms: Tuple[Atom, ...]
    seed: Optional[int]


def generate_valid_invalid_pair(signature: Signature, max_atoms: int = 3,
                                seed: Optional[int] = None) -> ValidInvalidPair:
    """Sample a valid/invalid propositional exercise pair over ``signature``.

    Draws up to ``max_atoms`` distinct 0-ary predicates from ``signature`` as
    the propositional atom pool (fewer if the signature declares fewer;
    refuses if it declares none), samples quantifier-free formulas from a
    small seeded grammar (:func:`And`/:func:`Or`/:func:`Not`/:func:`Implies`
    over those atoms), and classifies each with
    :func:`~unicode_fol_kit.semantics.truthtable.truth_table` — a complete
    decision procedure for this fragment, so the "valid" label is never a
    guess. Retries up to :data:`_RETRY_BUDGET` times per formula to find a
    naturally-shaped tautology / non-tautology; if that budget is exhausted
    (rare — most small random formulas are quickly classified either way) it
    falls back to a construction that is tautologous (resp. non-tautologous)
    BY CONSTRUCTION — ``Implies(phi, phi)`` is a tautology for any ``phi``;
    ``And(atom, Not(atom))`` is a contradiction, hence never a tautology —
    so every call terminates. Either way, both formulas are re-classified
    (and the countermodel independently re-evaluated against a fresh
    :class:`~unicode_fol_kit.semantics.tarski.Structure` via
    :func:`~unicode_fol_kit.semantics.tarski.models`) before returning, so a
    bug in the sampler can only make this function raise, never ship a
    mislabelled pair.

    Raises:
        ValueError: ``max_atoms < 1``, or ``signature`` declares no 0-ary
            predicate (this generator is propositional-only — see the module
            docstring for why the first-order case is out of scope here).
    """
    if max_atoms < 1:
        raise ValueError("generate_valid_invalid_pair: max_atoms must be >= 1.")
    pool = _nullary_atoms(signature)
    if not pool:
        raise ValueError(
            "generate_valid_invalid_pair: signature declares no nullary (arity-0) "
            "predicates; this generator samples over the propositional fragment "
            "only, where each distinct atom is a bare propositional variable -- "
            "add at least one 0-ary predicate to the signature."
        )
    rng = random.Random(seed)
    n = min(max_atoms, len(pool))
    atoms = tuple(rng.sample(pool, n))
    budget = n + 2

    valid_formula: Optional[Node] = None
    for _ in range(_RETRY_BUDGET):
        candidate = _random_prop_formula(rng, atoms, budget)
        if truth_table(candidate).is_tautology:
            valid_formula = candidate
            break
    if valid_formula is None:
        phi = _random_prop_formula(rng, atoms, budget)
        valid_formula = Implies(phi, phi)

    invalid_formula: Optional[Node] = None
    invalid_valuation: Optional[Dict[str, bool]] = None
    for _ in range(_RETRY_BUDGET):
        candidate = _random_prop_formula(rng, atoms, budget)
        table = truth_table(candidate)
        if not table.is_tautology:
            invalid_formula = candidate
            invalid_valuation = _first_countermodel(table)
            break
    if invalid_formula is None:
        atom0 = atoms[0]
        invalid_formula = And(atom0, Not(atom0))
        invalid_valuation = {atom0.predicate: False}

    # Self-check (defence in depth, same route as construction). The
    # INDEPENDENT check -- a fresh 2^n enumeration and a fresh Structure, not
    # reusing truth_table/models at all -- lives in tests/test_exercise_gen.py.
    if not truth_table(valid_formula).is_tautology:
        raise AssertionError("internal: constructed 'valid' formula is not a tautology.")
    if truth_table(invalid_formula).is_tautology:
        raise AssertionError("internal: constructed 'invalid' formula is a tautology.")
    if models(invalid_formula, _nullary_structure(invalid_valuation)):
        raise AssertionError("internal: invalid_valuation does not falsify invalid_formula.")

    return ValidInvalidPair(valid_formula, invalid_formula, invalid_valuation, atoms, seed)


# ---------------------------------------------------------------------------
# 2. generate_entailment_with_proof
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class EntailmentExercise:
    """A constructively-built Fitch proof exercise.

    ``depth`` is a STATIC count of nested :class:`~unicode_fol_kit.atp.fitch.Subproof`
    levels in ``proof.steps`` — the shipped worked solution's depth, not a
    claim that no shallower proof of ``conclusion`` exists (see the module
    docstring). ``premises``/``conclusion`` are read off the checked proof
    itself (:func:`~unicode_fol_kit.atp.fitch.verify_proof`'s own certified
    sequent), not re-derived separately.
    """

    proof: Proof
    premises: Tuple[Node, ...]
    conclusion: Node
    depth: int
    seed: Optional[int]


def _build_depth_chain(atoms: Sequence[Atom], start: int
                       ) -> Tuple[Subproof, Line, int]:
    """Build one ``→I`` box for ``atoms[0]``, recursively nesting one more box
    per remaining atom, numbering lines from ``start``.

    The innermost box (a single remaining atom) just reiterates its own
    assumption; each enclosing box discharges the one it wraps with ``→I``,
    so the fully assembled chain proves
    ``atoms[0] → (atoms[1] → ( … → (atoms[-1] → atoms[-1]) … ))`` with
    exactly ``len(atoms)`` nested subproof levels — one per atom. Returns
    ``(subproof, discharge_line, next_free_line_number)``: ``subproof`` is
    the box for ``atoms[0]`` and ``discharge_line`` is the ``→I`` line that
    closes it (placed by the CALLER, in the enclosing scope — a box never
    contains the line that closes it).
    """
    a0 = atoms[0]
    assume_line = assume(start, a0)
    if len(atoms) == 1:
        reit_line = line(start + 1, a0, "Reit", start)
        body: Tuple[Union[Line, Subproof], ...] = (reit_line,)
        body_formula = a0
        next_num = start + 2
    else:
        inner_subproof, inner_discharge, next_num = _build_depth_chain(atoms[1:], start + 1)
        body = (inner_subproof, inner_discharge)
        body_formula = inner_discharge.formula
    subproof = Subproof(assumption=assume_line, body=body)
    discharge = line(next_num, Implies(a0, body_formula), "→I", (start, next_num - 1))
    return subproof, discharge, next_num + 1


def _nesting_depth(steps: Sequence[Union[Line, Subproof]]) -> int:
    """The maximum number of NESTED :class:`Subproof` levels among ``steps``
    (0 if none; two sibling subproofs at the same level both count as 1, not
    2 — see the module's De Morgan / LEM hand-counted examples in the tests).
    """
    depth = 0
    for step in steps:
        if isinstance(step, Subproof):
            depth = max(depth, 1 + _nesting_depth(step.body))
    return depth


def generate_entailment_with_proof(signature: Signature, target_depth: int,
                                   seed: Optional[int] = None) -> EntailmentExercise:
    """Constructively build a Fitch proof with exactly ``target_depth`` nested
    subproof levels, over ``target_depth`` distinct 0-ary predicates drawn
    from ``signature``.

    The derivation is a chain of nested ``→I`` introductions (see
    :func:`_build_depth_chain`): no search is performed, so the depth is
    exact by construction, not merely a search bound. The assembled proof is
    re-checked with :func:`~unicode_fol_kit.atp.fitch.verify_proof` before
    being returned — the module's own "soundness is free" independent
    checker (see the module docstring for why a depth-bounded SEARCH could
    never certify this the same way).

    Raises:
        ValueError: ``target_depth < 1``, or ``signature`` declares fewer
            than ``target_depth`` distinct 0-ary predicates.
    """
    if target_depth < 1:
        raise ValueError("generate_entailment_with_proof: target_depth must be >= 1.")
    pool = _nullary_atoms(signature)
    if len(pool) < target_depth:
        raise ValueError(
            f"generate_entailment_with_proof: signature declares only "
            f"{len(pool)} nullary (arity-0) predicate(s), but target_depth="
            f"{target_depth} distinct ones are needed -- this generator builds "
            "one nested ->I box per level over distinct propositional atoms."
        )
    rng = random.Random(seed)
    atoms = rng.sample(pool, target_depth)

    subproof, discharge, _next = _build_depth_chain(atoms, 1)
    proof = Proof(premises=(), steps=(subproof, discharge), logic="fol")

    result = verify_proof(proof)
    if not result.ok:
        raise AssertionError(  # pragma: no cover -- construction is formally sound
            f"internal: constructively-built proof failed to verify at line "
            f"{result.error_line}: {result.error}"
        )
    depth = _nesting_depth(proof.steps)
    if depth != target_depth:
        raise AssertionError(  # pragma: no cover -- one box per atom, by construction
            f"internal: assembled proof has nesting depth {depth}, expected {target_depth}."
        )

    return EntailmentExercise(proof=proof, premises=result.premises,
                              conclusion=result.conclusion, depth=depth, seed=seed)


# ---------------------------------------------------------------------------
# 3. generate_theory_with_model_size
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class ModelSizeExercise:
    """A small finite theory whose minimal model size is exactly ``target_size``.

    ``theory`` is a strict total order (irreflexive, transitive, total) over
    the binary predicate ``relation`` (drawn from ``signature``), conjoined
    with an existential chain forcing at least ``target_size`` pairwise
    distinct, linearly ``relation``-ordered elements. ``witness`` is a
    concrete model of exactly that size, found by
    :func:`~unicode_fol_kit.semantics.modelfinder.find_model`.

    Equality caveat: ``witness`` is a
    :class:`~unicode_fol_kit.semantics.tarski.Structure`, which has no
    ``__eq__`` and so compares by object identity — two
    ``ModelSizeExercise`` values with identical content (e.g. from the same
    ``seed``) are never ``==`` to each other. Compare ``witness.domain``,
    ``witness.constants``, ``witness.predicates`` and ``witness.sorts``
    directly instead of the whole dataclass or the whole ``witness``.
    """

    theory: Tuple[Node, ...]
    target_size: int
    relation: str
    witness: Structure
    seed: Optional[int]


def generate_theory_with_model_size(
    signature: Signature, target_size: int, seed: Optional[int] = None,
    max_candidates: int = modelfinder.MAX_CANDIDATES,
) -> ModelSizeExercise:
    """Build a theory (a strict total order forced to contain a chain of
    length ``target_size``) whose minimal finite model size is EXACTLY
    ``target_size``, over one binary predicate drawn from ``signature``.

    Why this family: a strict order (irreflexive + transitive + total) that
    additionally asserts a chain ``x1 R x2 R … R xN`` forces at least ``N``
    pairwise distinct elements (irreflexivity + transitivity rule out any
    ``xi = xj``), and a genuine ``N``-element total order trivially satisfies
    everything, so the minimal model size is exactly ``N`` — the textbook
    fact this roadmap item's own test oracle names ("an irreflexive total
    order needs domain size >= 2") generalised to an arbitrary chain length.

    Both halves of the claim are confirmed before returning, not assumed:

    - :func:`~unicode_fol_kit.semantics.modelfinder.is_size_exhaustive` is
      checked for every size ``1..target_size`` FIRST. ``find_model`` itself
      conflates "this size was searched and refuted" with "this size was
      skipped because its interpretation space exceeded ``max_candidates``"
      (see that function's docstring) — a claim like "no smaller model
      exists" would be unsound if it rested on a skipped size, so this
      generator refuses outright (``ValueError``, not a wrong "minimal size"
      claim) rather than risk that.
    - Only once every relevant size is confirmed exhaustive does it call
      ``find_model`` for the witness (at ``target_size``) and for minimality
      (at ``target_size - 1``, expecting ``None``).

    Raises:
        ValueError: ``target_size < 1``; ``signature`` declares no binary
            (arity-2) predicate; or some size ``<= target_size`` would be
            skipped (not exhaustively searched) under ``max_candidates`` —
            raise ``max_candidates`` or lower ``target_size`` to proceed. A
            binary relation's interpretation count grows as ``2**(k**2)``, so
            this budget is reached well before ``target_size`` gets large —
            by design: refusing loudly beats silently narrowing the claim.
    """
    if target_size < 1:
        raise ValueError("generate_theory_with_model_size: target_size must be >= 1.")
    binaries = sorted(
        name for name, decl in signature.predicates.items() if decl.arity == 2
    )
    if not binaries:
        raise ValueError(
            "generate_theory_with_model_size: signature declares no binary "
            "(arity-2) predicate; this generator builds a strict-total-order "
            "theory (irreflexive, transitive, total) over one binary relation, "
            "forced to a chain of the target length -- add a 2-ary predicate."
        )
    rng = random.Random(seed)
    relation = rng.choice(binaries)

    def R(a: Node, b: Node) -> Atom:
        return Atom(relation, (a, b))

    x, y, z = Variable("x"), Variable("y"), Variable("z")
    irreflexive = Quantifier("∀", x, Not(R(x, x)))
    transitive = Quantifier(
        "∀", x, Quantifier(
            "∀", y, Quantifier(
                "∀", z, Implies(And(R(x, y), R(y, z)), R(x, z)))))
    total = Quantifier(
        "∀", x, Quantifier(
            "∀", y, Or(R(x, y), Or(Atom("=", (x, y)), R(y, x)))))
    theory: List[Node] = [irreflexive, transitive, total]

    if target_size >= 2:
        chain_vars = [Variable(f"e{i}") for i in range(target_size)]
        links = [R(chain_vars[i], chain_vars[i + 1]) for i in range(target_size - 1)]
        chain_body: Node = reduce(And, links)
        chain_formula = chain_body
        for v in reversed(chain_vars):
            chain_formula = Quantifier("∃", v, chain_formula)
        theory.append(chain_formula)
    theory_t = tuple(theory)

    for k in range(1, target_size + 1):
        if not modelfinder.is_size_exhaustive(theory_t, k, max_candidates=max_candidates):
            raise ValueError(
                f"generate_theory_with_model_size: cannot certify a minimal "
                f"model size of {target_size} for relation {relation!r}: "
                f"domain size {k}'s interpretation space exceeds "
                f"max_candidates={max_candidates} and would be SKIPPED, not "
                "exhaustively searched or refuted, by find_model -- raise "
                "max_candidates or lower target_size."
            )

    witness = modelfinder.find_model(theory_t, max_size=target_size,
                                     max_candidates=max_candidates)
    if witness is None or len(witness.domain) != target_size:
        raise AssertionError(  # pragma: no cover -- formally guaranteed by construction
            f"internal: the strict-order+chain theory for relation={relation!r} "
            f"has no model of exactly size {target_size}, despite every size "
            f"1..{target_size} being confirmed exhaustively searched."
        )
    if target_size > 1:
        smaller = modelfinder.find_model(theory_t, max_size=target_size - 1,
                                         max_candidates=max_candidates)
        if smaller is not None:
            raise AssertionError(  # pragma: no cover -- formally guaranteed minimal
                f"internal: a smaller model of size {len(smaller.domain)} exists "
                f"for relation={relation!r}, despite target_size={target_size}."
            )

    return ModelSizeExercise(theory=theory_t, target_size=target_size,
                             relation=relation, witness=witness, seed=seed)
