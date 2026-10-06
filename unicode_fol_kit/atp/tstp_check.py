"""Independent checker for Vampire/E TSTP derivations (:mod:`atp.tstp`'s read side).

:func:`atp.tstp.parse_tstp_derivation` turns a prover's printed proof into a
:class:`~atp.tstp.TstpDerivation` DAG, but nothing re-derives it — the DAG is
trusted verbatim. This module is that independent check, in the same spirit
as :mod:`atp.resolution_check` (an external searcher's derivation is only as
trustworthy as its checker) and :mod:`atp.twee_check`, but TILED rather than
uniform: a real captured proof (see ``tests/fixtures/tstp_check/`` and
``tests/fixtures/eprover_3_5_1_theorem.txt``) mixes three very different
kinds of step, and this module gives each its own honest treatment instead of
pretending they are all equally certifiable.

Three tiers
-----------

1. **Core, independently-checked rules** (:data:`VAMPIRE_CHECKED_RULES` /
   :data:`EPROVER_CHECKED_RULES`): binary resolution, factoring,
   superposition/paramodulation, equality resolution, forward/backward
   demodulation, forward/backward subsumption resolution, and the removal of
   the literals that are false in every interpretation
   (``true_and_false_elimination``). Each step's
   clause and its cited parents' clauses are converted from the general
   :class:`~fol.nodes.Node` :func:`atp.tstp.parse_tstp_derivation` already
   produced into :mod:`atp.resolution_check`'s frozenset-of-literals clause
   shape (:func:`_node_to_clause`), and the re-derivation itself reuses that
   module's :func:`~atp.resolution_check._unify` /
   :func:`~atp.resolution_check._apply` (a unifier's output, whose bindings are
   followed) / :func:`~atp.resolution_check._apply_matcher` (a one-sided
   matcher, applied in one simultaneous step) /
   :func:`~atp.resolution_check._is_variant` /
   :func:`~atp.resolution_check._term_gt` primitives directly (imported as
   ``_rc.<name>`` throughout this module) — no code is shared with any
   *searcher* (:mod:`atp.resolution`, Vampire, E themselves), preserving
   :mod:`atp.resolution_check`'s checker-independence property.

   TSTP carries no ``eq_literal``/``target_literal``/``direction``/
   ``position`` fields the way a hand-built :class:`atp.resolution_check
   .ResolutionStep` does, so the equality-rule checkers here
   (:func:`_check_tstp_superposition`, :func:`_check_tstp_demodulation`,
   :func:`_check_tstp_equality_resolution`) are *generalized* from
   :mod:`atp.resolution_check`'s "trust the stated fields, only re-derive the
   unifier" design into a bounded SEARCH over candidate literals, subterm
   positions (:func:`_all_positions`) and rewrite directions — this is new
   work, not reuse, and is exercised by hand-built accept/reject fixtures in
   ``tests/test_tstp_check.py`` for each rule. Forward/backward subsumption
   resolution (:func:`_check_tstp_subsumption_resolution`) is new work too —
   :mod:`atp.resolution_check` has no such rule at all — implemented as a
   bounded backtracking one-sided match (the subsumer clause's variables
   bind, the target clause is held fixed), independently reimplemented here
   rather than reusing :mod:`atp.resolution`'s own subsumption/matching code.
   ``true_and_false_elimination`` (Vampire's name for it, captured live in
   ``tests/fixtures/tstp_check/vampire_true_and_false_elimination.txt``; the kit's
   own ``truth_constants`` rule is written under it) takes ONE parent and
   licenses its clause minus some literals, each of which is ``$false`` or
   ``¬$true`` (:func:`_check_tstp_truth_constants`): dropping any other literal,
   or keeping a literal the parent does not have, is rejected. It reads the
   parent with its constant literals kept (:func:`_node_to_clause` with
   ``keep_constants=True``), which no other core rule sees. A step whose
   formula is not a flat clause (Vampire also uses the rule on whole formulas)
   comes back unchecked, never approximately checked.

2. **Clausification checked by entailment** (:data:`VAMPIRE_CLAUSIFICATION_RULES` /
   :data:`EPROVER_CLAUSIFICATION_RULES`): steps whose rule identifies them as
   clausification/normalisation (``negated_conjecture``, ``flattening``,
   ``(e)nnf_transformation``, ``cnf_transformation``, ``rectify``,
   ``shift_quantors``, ``variable_rename``, ``pure_predicate_removal``;
   E's ``assume_negation``, ``fof_simplification``, ``fof_nnf``,
   ``split_conjunct``) are not re-derived transformation by transformation
   -- any sound clausifier output passes -- but each one's stated formula
   must be ENTAILED by its (already verified) parents, which Z3 has to
   PROVE within a per-step budget (:func:`_entailed`; ``unknown`` or a
   timeout is a failure, never a pass). That is exactly what a
   refutation's soundness needs: every statement is then a consequence of
   the caller's premises plus the negated conjecture, so a derived
   ``$false`` really refutes them.

   The conjecture needs one more rule, because entailment alone would let
   a proof ASSUME it: a leaf standing for the caller's conclusion may be
   cited only by ``negated_conjecture``/``assume_negation`` (and those may
   cite nothing else), whose formula must be entailed by the conjecture's
   NEGATION. Any other step -- clausification or core rule -- that cites
   the conjecture leaf fails, naming it.

   Leaves themselves (a :class:`~atp.tstp.TstpStep` whose own ``rule is
   None`` -- a ``file(...)``-sourced original, or any other
   non-``inference(...)`` source) must be an ALPHA-VARIANT
   (:func:`_formula_alpha_equal` -- ordered structural equality up to a
   consistent bound-variable renaming, ``Quantifier``-scope aware) of one of
   the caller's own ``premises``/``conclusion``, so a derivation cannot
   smuggle in an extra axiom as a leaf either.

   ``skolemisation`` is recognised but refused by name (tier
   ``"unchecked"``): a Skolemized formula is NOT a consequence of its
   parent -- Skolemization preserves satisfiability only -- so no
   entailment check can license it, and certifying it needs a structural
   "fresh symbol, right argument list" check this module does not do.
   Vampire's Skolemization step also cites a leaf sourced
   ``introduced(definition, [], [skolem_symbol_introduction])``, which is not
   one of the caller's premises and fails the leaf check for the same
   reason. Any derivation that Skolemizes therefore comes back unverified;
   see ``tests/fixtures/tstp_check/vampire_skolemisation.txt`` and its test.

   An earlier version of this tier only walked each clausification step's
   parent chain back to genuine leaves and never looked at the step's own
   formula, so a single ``cnf_transformation`` step could state anything --
   ``p(a) |- p(b)`` came back ``verified=True`` -- and a step could cite the
   conjecture positively. Both are pinned as regression tests.

3. **Refuse loudly on everything else**: any step whose rule is outside both
   tables above — AVATAR splitting, global subsumption, ``definition_
   unfolding``, equality factoring (deliberately not implemented — see
   below), E's ``cn`` (see below), or any unrecognised/future rule name —
   makes that step, and therefore the WHOLE derivation
   (:attr:`TstpCheckResult.verified`), come back ``False``, naming the
   offending rule (:attr:`TstpStepResult.detail`); never silently accepted.

Deliberate scope decisions (not oversights — each is a step this module
could not honestly certify without materially expanding its scope):

* **Equality factoring** is not implemented as a checked rule. It is the
  least-used of the superposition-calculus rules, is not exercised by any
  real fixture this module was developed against, and is not required by
  its own test oracle. A step naming it is honestly reported unchecked
  rather than approximately checked.
* **E's ``cn`` rule** is not registered in either table. In the one real E
  fixture available (``tests/fixtures/eprover_3_5_1_theorem.txt``), the
  final refutation step's rule is ``cn`` with a SINGLE nested
  ``inference(rw, ..., [inference(spm, ..., [...]), ...])`` parent, and an
  earlier step (``c_0_6``, ``fof_nnf``) similarly nests a
  ``variable_rename``/``fof_nnf`` chain inside ONE compound parent-list
  entry — :func:`atp.tstp._parse_source` (deliberately, for the proof-DAG-
  display use case it serves) drops a parent-list entry that is itself a
  compound ``inference(...)`` term, so both steps' own
  :attr:`~atp.tstp.TstpStep.parents` come back EMPTY. Even setting that
  parsing choice aside, ``cn`` ("clause normalisation") has no single fixed
  licensing condition the way ``resolution``/``factoring``/etc. do — it is
  E's generic wrapper for "here is the final simplified clause", not one
  calculus rule — so there is nothing well-defined to re-derive even given
  resolvable parents. E's own ``spm``/``rw``/``er`` abbreviations
  (superposition/rewrite=demodulation/equality-resolution, confirmed from
  that same nested record) ARE registered in :data:`EPROVER_CHECKED_RULES`
  for the case where a future E configuration prints one as its own
  top-level statement with resolvable parents. A consequence, confirmed by
  ``tests/test_tstp_check.py::test_eprover_real_fixture_is_not_fully_verified``:
  the one available real E fixture comes back UNVERIFIED overall (the
  ``fof_nnf``/``cn`` steps come back unchecked/unresolvable), not fully
  verified — the honest outcome given what the parser can actually recover,
  not a bug in this module.
* **Wiring into ``VampireBackend``/``EProverBackend`` as an opt-in
  ``verify_tstp`` option** (this item's original 4th point) is out of scope
  for this module — :mod:`atp.protocol` is not this change's file, see the
  integration notes accompanying it.

Public API: :class:`TstpStepResult`, :class:`TstpCheckResult`,
:func:`check_tstp_derivation`, and the four rule-name tables
:data:`VAMPIRE_CLAUSIFICATION_RULES`, :data:`VAMPIRE_CHECKED_RULES`,
:data:`EPROVER_CLAUSIFICATION_RULES`, :data:`EPROVER_CHECKED_RULES`.
"""

from dataclasses import dataclass
from typing import Callable, Dict, FrozenSet, List, Optional, Sequence, Tuple

from ..fol.nodes import (
    Node, Atom, Not, And, Or, Xor, Implies, Iff, Quantifier,
    Variable, Constant, Number, Function, free_variables,
)
from . import resolution_check as _rc
from .tstp import TstpDerivation, TstpStep

__all__ = [
    "TstpStepResult", "TstpCheckResult", "check_tstp_derivation",
    "VAMPIRE_CLAUSIFICATION_RULES", "VAMPIRE_CHECKED_RULES",
    "EPROVER_CLAUSIFICATION_RULES", "EPROVER_CHECKED_RULES",
]


# ---------------------------------------------------------------------------
# Rule-name tables — separate per prover (their TSTP vocabularies do not
# overlap in the sense that no name below means something different across
# the two — see the module docstring), merged for runtime dispatch since a
# rule's checking logic depends only on the rule's own semantics, not on
# which prover happened to print it.
# ---------------------------------------------------------------------------

# Confirmed against tests/fixtures/tstp_check/vampire_*.txt (captured live,
# `vampire --proof tptp --avatar off`, Vampire 5.0.1, during this module's
# development) and tests/test_tstp.py's own pre-existing _THEOREM_OUTPUT
# fixture. 'nnf_transformation'/'rectify'/'shift_quantors'/
# 'pure_predicate_removal' are Vampire's documented preprocessing rule names
# for constructs the small fixtures above did not individually exercise, but
# which get the exact same entailment check as the ones that were captured
# ('skolemisation' is recognised only to be refused by name: see
# _SATISFIABILITY_ONLY_RULES).
VAMPIRE_CLAUSIFICATION_RULES: FrozenSet[str] = frozenset({
    "negated_conjecture", "flattening", "nnf_transformation",
    "ennf_transformation", "cnf_transformation", "rectify",
    "shift_quantors", "variable_rename", "pure_predicate_removal",
    "skolemisation",
})

# 'resolution', 'superposition', 'equality_resolution' and
# 'forward_subsumption_resolution' are each confirmed from a real captured
# fixture (see tests/fixtures/tstp_check/). 'factoring',
# 'backward_subsumption_resolution' and 'forward_demodulation'/
# 'backward_demodulation' are the standard TPTP-family names for the
# remaining core rules (not independently captured this session) — see the
# module docstring for 'equality_factoring', deliberately absent.
# 'true_and_false_elimination' is confirmed from a real captured fixture too
# (tests/fixtures/tstp_check/vampire_true_and_false_elimination.txt, Vampire
# 5.0.1): it drops the literals $false and ~$true from a clause.
VAMPIRE_CHECKED_RULES: FrozenSet[str] = frozenset({
    "resolution", "factoring", "superposition",
    "forward_demodulation", "backward_demodulation",
    "equality_resolution",
    "forward_subsumption_resolution", "backward_subsumption_resolution",
    "true_and_false_elimination",
})

# Confirmed against tests/fixtures/eprover_3_5_1_theorem.txt (already
# captured for tests/test_tstp.py / tests/test_eprover_zipperposition.py):
# 'assume_negation', 'fof_simplification', 'fof_nnf', 'variable_rename' and
# 'split_conjunct' all appear there as genuine top-level steps.
EPROVER_CLAUSIFICATION_RULES: FrozenSet[str] = frozenset({
    "assume_negation", "fof_simplification", "fof_nnf", "variable_rename",
    "split_conjunct",
})

# 'spm'/'rw'/'er' appear in that same fixture, but only NESTED inside its
# final 'cn' step's source record — never as their own top-level statement.
# Registered here (same generalized checkers as Vampire's 'superposition'/
# 'demodulation'/'equality_resolution') for when a top-level step uses one
# directly; see the module docstring for why 'cn' itself is not registered.
EPROVER_CHECKED_RULES: FrozenSet[str] = frozenset({"spm", "rw", "er"})

_CLAUSIFICATION_RULES: FrozenSet[str] = VAMPIRE_CLAUSIFICATION_RULES | EPROVER_CLAUSIFICATION_RULES

# The only rules allowed to cite the CONJECTURE itself: a refutation derives
# $false from premises + negated conjecture, so the conjecture enters exactly
# once, negated. Any other step citing it would be assuming what is to be proved.
_NEGATION_RULES: FrozenSet[str] = frozenset({"negated_conjecture", "assume_negation"})

# Recognised, but refused by name: Skolemisation preserves SATISFIABILITY
# only -- the Skolemized formula is not a logical consequence of its parent --
# so no entailment check can license it, and certifying it needs the
# structural "fresh symbol, right argument list" check this module does not do.
_SATISFIABILITY_ONLY_RULES: FrozenSet[str] = frozenset({"skolemisation"})

# Per-step budget for the Z3 entailment check. A timeout is NOT a pass: the
# step then comes back unconfirmed, never verified.
_ENTAILMENT_TIMEOUT_MS = 5000


# ---------------------------------------------------------------------------
# Node -> clause conversion: a TstpStep.formula (a general Node, possibly
# carrying a leading universal-quantifier prefix the way an un-Skolemized
# clausal fof step does) into resolution_check.py's frozenset-of-literals
# clause shape. Returns None — refuse rather than guess — for any formula
# shape that is not a flat, already-clausal disjunction of literals (an And,
# an Implies/Iff/Xor at the matrix level, a leading existential, ...): such a
# step simply cannot be treated as a clause by this module's core-checked
# tier, and the caller reports that step unverified rather than misreading it.
# ---------------------------------------------------------------------------

def _normalize_literal(lit: Node) -> Node:
    """Rewrite TPTP's dedicated disequality atom into resolution_check.py's
    ``Not(Atom("=", ...))`` shape (and the symmetric double-negative), so
    every downstream helper (:func:`~atp.resolution_check._lit_atom_polarity`,
    ``_is_equality_atom``, ...) only ever has to recognise ONE negative-
    equality shape. :func:`fol.tptp_input.parse_tptp_formula` maps TPTP's
    ``a != b`` to a dedicated ``Atom("≠", [a, b])`` (never to
    ``Not(Atom("=", ...))``) — see that module's docstring — so without this
    normalization a real disequality literal (e.g. the ``a != X0`` in
    ``tests/fixtures/tstp_check/vampire_equality_resolution.txt``) would be
    invisible to every equality-rule checker below.
    """
    if isinstance(lit, Atom) and lit.predicate == "≠" and len(lit.args) == 2:
        return Not(Atom("=", list(lit.args)))
    if (isinstance(lit, Not) and isinstance(lit.formula, Atom)
            and lit.formula.predicate == "≠" and len(lit.formula.args) == 2):
        return Atom("=", list(lit.formula.args))
    return lit


def _flatten_or_into(node: Node, out: List[Node], keep_constants: bool = False) -> bool:
    """Append ``node``'s literals (recursing through ``Or``) onto ``out``.

    Returns False — leaving ``out`` in an unspecified partial state the
    caller discards — the moment a non-literal, non-``Or`` node is reached,
    or a literal reduces to the ``$true``/``$false`` marker atoms (neither is
    a genuine literal within a clause; ``$false`` alone as the WHOLE matrix
    is handled separately by :func:`_node_to_clause`, as the empty clause).
    With ``keep_constants`` the marker atoms are kept as literals instead: the
    one rule that reads them (``true_and_false_elimination``) needs to see
    which ones its parent holds.
    """
    if isinstance(node, Or):
        return (_flatten_or_into(node.left, out, keep_constants)
                and _flatten_or_into(node.right, out, keep_constants))
    lit = _normalize_literal(node)
    parsed = _rc._lit_atom_polarity(lit)
    if parsed is None:
        return False
    atom, _is_positive = parsed
    if atom.predicate in ("$true", "$false") and not keep_constants:
        return False
    out.append(lit)
    return True


def _node_to_clause(node: Node, keep_constants: bool = False) -> Optional[FrozenSet[Node]]:
    """Convert a TSTP step's formula into a clause (frozenset of literals).

    Strips a leading chain of universal (``"∀"``) quantifiers (an
    existential anywhere in that prefix means this is not a clause — a
    genuinely clausal TSTP step is always implicitly-or-explicitly
    universally quantified), then reads the remaining matrix as ``$false``
    (the empty clause) or a flat ``Or``-tree of literals
    (:func:`_flatten_or_into`). Returns ``None`` on any other shape.
    ``keep_constants`` keeps a ``$true`` / ``$false`` literal of a longer clause
    as a literal (see :func:`_flatten_or_into`); the formula ``$false`` alone is
    the empty clause either way.
    """
    n = node
    while isinstance(n, Quantifier):
        if n.type != "∀":
            return None
        n = n.formula
    if isinstance(n, Atom) and n.predicate == "$false" and not n.args:
        return frozenset()
    literals: List[Node] = []
    if not _flatten_or_into(n, literals, keep_constants):
        return None
    return frozenset(literals)


# ---------------------------------------------------------------------------
# Formula-level alpha-equivalence (leaf-boundary check, tier 2). Deliberately
# an ORDERED structural comparison (unlike resolution_check.py's clause-level
# _is_variant, which permutes an unordered literal set) -- a leaf formula is
# a near-verbatim restatement of ONE whole original formula, so its
# top-level shape (which side of an Implies, which And/Or came first, ...)
# is expected to match exactly; only the concrete spelling of bound variable
# names may differ. A free (unbound-in-this-walk) Variable must match by
# name literally -- premises/conclusions passed to check_tstp_derivation are
# expected to be closed sentences or ground atoms, so this case is not
# exercised by any real derivation, but it is the safe (never a false
# "matches") default when it is.
# ---------------------------------------------------------------------------

def _formula_alpha_equal(a: Node, b: Node,
                         fwd: Optional[Dict[str, str]] = None,
                         bwd: Optional[Dict[str, str]] = None) -> bool:
    """True iff ``a`` and ``b`` are the same formula up to a consistent
    renaming of bound variables (Quantifier-scope aware)."""
    if fwd is None:
        fwd, bwd = {}, {}
    if type(a) is not type(b):
        return False
    if isinstance(a, Variable):
        mapped = fwd.get(a.name)
        if mapped is not None:
            return mapped == b.name
        if b.name in bwd:
            return False
        return a.name == b.name
    if isinstance(a, Constant):
        return a.name == b.name
    if isinstance(a, Number):
        return a.value == b.value
    if isinstance(a, Function):
        if a.name != b.name or len(a.args) != len(b.args):
            return False
        return all(_formula_alpha_equal(x, y, fwd, bwd) for x, y in zip(a.args, b.args))
    if isinstance(a, Atom):
        if a.predicate != b.predicate or len(a.args) != len(b.args):
            return False
        return all(_formula_alpha_equal(x, y, fwd, bwd) for x, y in zip(a.args, b.args))
    if isinstance(a, Not):
        return _formula_alpha_equal(a.formula, b.formula, fwd, bwd)
    if isinstance(a, (And, Or, Xor, Implies, Iff)):
        return (_formula_alpha_equal(a.left, b.left, fwd, bwd)
                and _formula_alpha_equal(a.right, b.right, fwd, bwd))
    if isinstance(a, Quantifier):
        if a.type != b.type:
            return False
        new_fwd = dict(fwd)
        new_fwd[a.variable.name] = b.variable.name
        new_bwd = dict(bwd)
        new_bwd[b.variable.name] = a.variable.name
        return _formula_alpha_equal(a.formula, b.formula, new_fwd, new_bwd)
    return a == b


# ---------------------------------------------------------------------------
# Per-rule checkers (core-checked tier). Each has the signature
# ``(clause, *parent_clauses) -> Optional[str]`` (None = licensed, else an
# error string without a "step N:" prefix — the caller adds that), mirroring
# resolution_check.py's per-rule checkers but reused as a bounded SEARCH
# (TSTP names no literal/position/direction explicitly) instead of trusting
# caller-stated fields.
# ---------------------------------------------------------------------------

def _check_tstp_resolve(clause: FrozenSet[Node], ci: FrozenSet[Node],
                        cj: FrozenSet[Node]) -> Optional[str]:
    """``"resolution"``: some complementary-polarity literal pair's mgu must
    give ``clause`` -- direct port of
    :func:`atp.resolution_check._check_resolve_step`."""
    ci2, cj2 = _rc._standardize_apart(ci, cj)
    found_complementary_pair = False
    for lit1 in sorted(ci2, key=_rc._lit_key):
        parsed1 = _rc._lit_atom_polarity(lit1)
        if parsed1 is None:
            continue
        atom1, pos1 = parsed1
        for lit2 in sorted(cj2, key=_rc._lit_key):
            parsed2 = _rc._lit_atom_polarity(lit2)
            if parsed2 is None:
                continue
            atom2, pos2 = parsed2
            if pos1 == pos2:
                continue
            found_complementary_pair = True
            sigma = _rc._unify(atom1, atom2)
            if sigma is None:
                continue
            resolvent = frozenset(
                [_rc._apply_literal(l, sigma) for l in ci2 if l != lit1]
                + [_rc._apply_literal(l, sigma) for l in cj2 if l != lit2]
            )
            if _rc._is_variant(resolvent, clause):
                return None
    if not found_complementary_pair:
        return "'resolution': the parent clauses contain no complementary-polarity literal pair"
    return "'resolution': no complementary-polarity literal pair's mgu produces the stated clause"


def _check_tstp_factor(clause: FrozenSet[Node], ci: FrozenSet[Node]) -> Optional[str]:
    """``"factoring"``: some same-polarity literal pair's mgu must give
    ``clause`` -- direct port of
    :func:`atp.resolution_check._check_factor_step`."""
    literals = sorted(ci, key=_rc._lit_key)
    for a_idx in range(len(literals)):
        parsed_a = _rc._lit_atom_polarity(literals[a_idx])
        if parsed_a is None:
            continue
        atom_a, pos_a = parsed_a
        for b_idx in range(a_idx + 1, len(literals)):
            parsed_b = _rc._lit_atom_polarity(literals[b_idx])
            if parsed_b is None:
                continue
            atom_b, pos_b = parsed_b
            if pos_a != pos_b:
                continue
            sigma = _rc._unify(atom_a, atom_b)
            if sigma is None:
                continue
            factored = frozenset(_rc._apply_literal(l, sigma) for l in ci)
            if _rc._is_variant(factored, clause):
                return None
    return "'factoring': no same-polarity literal pair's mgu produces the stated clause"


def _check_tstp_equality_resolution(clause: FrozenSet[Node],
                                    ci: FrozenSet[Node]) -> Optional[str]:
    """``"equality_resolution"``/E's ``"er"``: some negative equality
    literal's own two sides must unify, and dropping it under that unifier
    must give ``clause`` -- generalizes
    :func:`atp.resolution_check._check_reflexivity_step` (which trusts a
    caller-stated ``eq_literal``) into a search over every negative equality
    literal of ``ci``."""
    found_negative_equality = False
    for lit in sorted(ci, key=_rc._lit_key):
        parsed = _rc._lit_atom_polarity(lit)
        if parsed is None:
            continue
        atom, is_positive = parsed
        if is_positive or not _rc._is_equality_atom(atom):
            continue
        found_negative_equality = True
        u, v = atom.args
        sigma = _rc._unify(u, v)
        if sigma is None:
            continue
        expected = frozenset(_rc._apply_literal(l, sigma) for l in ci if l != lit)
        if _rc._is_variant(expected, clause):
            return None
    if not found_negative_equality:
        return "'equality_resolution': the parent clause has no negative equality literal"
    return "'equality_resolution': no negative equality literal's self-unifier produces the stated clause"


def _all_positions(node: Node) -> List[Tuple[int, ...]]:
    """Every non-empty argument-index position reachable within ``node``
    (an :class:`Atom` or :class:`Function`), depth-first, including
    positions inside nested :class:`Function` arguments. Excludes the empty
    position — a position always addresses a subterm reached by descending
    at least one argument, never the whole atom itself (see
    :func:`atp.resolution_check._term_at`'s docstring)."""
    positions: List[Tuple[int, ...]] = []

    def walk(n: Node, prefix: Tuple[int, ...]) -> None:
        if isinstance(n, (Atom, Function)):
            for i, arg in enumerate(n.args):
                positions.append(prefix + (i,))
                walk(arg, prefix + (i,))

    walk(node, ())
    return positions


def _check_tstp_superposition(clause: FrozenSet[Node], ci: FrozenSet[Node],
                              cj: FrozenSet[Node]) -> Optional[str]:
    """``"superposition"``/E's ``"spm"``: generalizes
    :func:`atp.resolution_check._check_paramodulate_step` into a bounded
    search over which parent supplies the positive equality literal, which
    literal it is, its rewrite direction, which literal of the OTHER parent
    is the target, and which subterm position of that literal is rewritten
    (TSTP names none of these explicitly). Both parent-role assignments are
    tried (the real captured fixtures in ``tests/fixtures/tstp_check/`` cite
    the TARGET clause first and the EQUATION clause second — the opposite of
    :mod:`atp.resolution_check`'s own convention — so this checker does not
    assume either order)."""
    for eq_side, tgt_side in ((cj, ci), (ci, cj)):
        eq_side2, tgt_side2 = _rc._standardize_apart(eq_side, tgt_side)
        eq_candidates = []
        for lit in eq_side2:
            parsed = _rc._lit_atom_polarity(lit)
            if parsed is None:
                continue
            atom, is_positive = parsed
            if is_positive and _rc._is_equality_atom(atom):
                eq_candidates.append((lit, atom))
        for eq_lit, eq_atom in eq_candidates:
            for direction in ("lr", "rl"):
                frm, to = _rc._direction_sides(eq_atom, direction)
                for tgt_lit in tgt_side2:
                    parsed_tgt = _rc._lit_atom_polarity(tgt_lit)
                    if parsed_tgt is None:
                        continue
                    tgt_atom, tgt_is_positive = parsed_tgt
                    for position in _all_positions(tgt_atom):
                        try:
                            subterm = _rc._term_at(tgt_atom, position)
                        except (IndexError, TypeError, AttributeError):
                            continue
                        sigma = _rc._unify(frm, subterm)
                        if sigma is None:
                            continue
                        try:
                            rewritten_atom = _rc._replace_at(tgt_atom, position, to)
                        except (IndexError, TypeError, AttributeError):
                            continue
                        rewritten_lit = (rewritten_atom if tgt_is_positive
                                        else Not(rewritten_atom))
                        expected = frozenset(
                            [_rc._apply_literal(l, sigma) for l in eq_side2 if l != eq_lit]
                            + [_rc._apply_literal(l, sigma) for l in tgt_side2 if l != tgt_lit]
                            + [_rc._apply_literal(rewritten_lit, sigma)]
                        )
                        if _rc._is_variant(expected, clause):
                            return None
    return ("'superposition': no positive equality literal, rewrite position and "
            "direction reproduces the stated clause")


def _check_tstp_demodulation(clause: FrozenSet[Node], ci: FrozenSet[Node],
                             cj: FrozenSet[Node]) -> Optional[str]:
    """``"forward_demodulation"``/``"backward_demodulation"``/E's ``"rw"``:
    generalizes :func:`atp.resolution_check._check_demodulate_step` (one-
    sided MATCHING, not unification, with the rewrite orientation re-checked
    against the term order) into a search over which parent is the UNIT
    equation, which literal of the other parent is the target, and which
    subterm position is rewritten. Whichever of ``ci``/``cj`` is a unit
    clause carrying a positive equality literal is tried as the equation
    side; if both are, both are tried.

    The matcher binds the equation's variables to subterms of the target, and the
    two clauses are not standardized apart (a prover numbers the variables of every
    clause from ``X0``), so an image can be spelled like a variable the matcher
    binds. The matcher is therefore applied to the right-hand side in ONE
    simultaneous step (:func:`atp.resolution_check._apply_matcher`), never by
    following its bindings."""
    for tgt_side, eq_side in ((cj, ci), (ci, cj)):
        if len(eq_side) != 1:
            continue
        eq_lit = next(iter(eq_side))
        parsed_eq = _rc._lit_atom_polarity(eq_lit)
        if parsed_eq is None:
            continue
        eq_atom, eq_is_positive = parsed_eq
        if not eq_is_positive or not _rc._is_equality_atom(eq_atom):
            continue
        for direction in ("lr", "rl"):
            l, r = _rc._direction_sides(eq_atom, direction)
            for tgt_lit in tgt_side:
                parsed_tgt = _rc._lit_atom_polarity(tgt_lit)
                if parsed_tgt is None:
                    continue
                tgt_atom, tgt_is_positive = parsed_tgt
                for position in _all_positions(tgt_atom):
                    try:
                        subterm = _rc._term_at(tgt_atom, position)
                    except (IndexError, TypeError, AttributeError):
                        continue
                    sigma = _rc._match_term(l, subterm, {})
                    if sigma is None:
                        continue
                    r_sigma = _rc._apply_matcher(r, sigma)
                    if not _rc._term_gt(subterm, r_sigma):
                        continue
                    try:
                        rewritten_atom = _rc._replace_at(tgt_atom, position, r_sigma)
                    except (IndexError, TypeError, AttributeError):
                        continue
                    rewritten_lit = (rewritten_atom if tgt_is_positive
                                    else Not(rewritten_atom))
                    rest = [l2 for l2 in tgt_side if l2 != tgt_lit]
                    expected = frozenset(rest + [rewritten_lit])
                    if _rc._is_variant(expected, clause):
                        return None
    return ("'demodulation': no unit positive equality parent orients, matches and "
            "rewrites into the stated clause")


def _match_atom_onesided(pattern: Atom, target: Atom,
                         subst: Dict[str, Node]) -> Optional[Dict[str, Node]]:
    """One-sided match of ``pattern``'s arguments against ``target``'s
    (``pattern``'s variables bind, ``target``'s are held fixed), extending
    ``subst`` argument by argument via
    :func:`atp.resolution_check._match_term`."""
    if pattern.predicate != target.predicate or len(pattern.args) != len(target.args):
        return None
    for p_arg, t_arg in zip(pattern.args, target.args):
        subst = _rc._match_term(p_arg, t_arg, subst)
        if subst is None:
            return None
    return subst


def _match_literals_into(remaining: List[Node], pool: List[Node],
                         subst: Dict[str, Node]) -> Optional[Dict[str, Node]]:
    """Backtracking search: extend ``subst`` (one-sided, ``remaining``'s
    variables bind) so every literal in ``remaining`` matches SOME literal of
    ``pool`` (order-independent, repeats allowed — soundness only needs
    membership, not an injective mapping)."""
    if not remaining:
        return subst
    lit = remaining[0]
    parsed_lit = _rc._lit_atom_polarity(lit)
    if parsed_lit is None:
        return None
    atom_lit, pos_lit = parsed_lit
    for candidate in pool:
        parsed_cand = _rc._lit_atom_polarity(candidate)
        if parsed_cand is None:
            continue
        atom_cand, pos_cand = parsed_cand
        if pos_lit != pos_cand:
            continue
        new_subst = _match_atom_onesided(atom_lit, atom_cand, subst)
        if new_subst is None:
            continue
        result = _match_literals_into(remaining[1:], pool, new_subst)
        if result is not None:
            return result
    return None


def _check_tstp_subsumption_resolution(clause: FrozenSet[Node], target: FrozenSet[Node],
                                       subsumer: FrozenSet[Node]) -> Optional[str]:
    """``"forward_subsumption_resolution"``/``"backward_subsumption_resolution"``:
    a rule :mod:`atp.resolution_check` does not have at all. ``target`` is
    the FIRST cited parent, ``subsumer`` the SECOND (matching the real
    captured fixtures in ``tests/fixtures/tstp_check/``). Licensing
    condition: some literal ``L`` of ``subsumer`` has a complement that
    one-sided-MATCHES (subsumer's variables bind, target's are held fixed)
    some literal ``M`` of ``target``, AND every other literal of
    ``subsumer`` also matches (under the SAME substitution) some literal of
    ``target`` OTHER THAN ``M`` — then ``target`` minus ``M`` is licensed.
    The "other than M" restriction is required, not cosmetic: resolving
    ``L ∨ Rest`` against ``M ∨ D'`` via ordinary binary resolution gives
    ``Restσ ∨ D'``, and this inference is sound only because that resolvent
    is already SUBSUMED by (syntactically contained in) ``D'`` when
    ``Restσ ⊆ D'`` — the rest of the subsumer must map into the target
    clause with ``M`` itself already removed, not into the target clause
    still carrying ``M``. Letting ``Restσ`` re-match ``M`` would license
    dropping ``M`` using ``M`` as its own witness (e.g. a tautologous or
    self-redundant ``subsumer`` could "explain away" an arbitrary literal of
    ``target``, which is unsound). Both are bounded backtracking searches
    (:func:`_match_literals_into` for "every other literal"; the outer loop
    below for the choice of ``L``/``M``)."""
    target_lits = list(target)
    subsumer_lits = list(subsumer)
    for l_idx, lit_c in enumerate(subsumer_lits):
        parsed_c = _rc._lit_atom_polarity(lit_c)
        if parsed_c is None:
            continue
        atom_c, pos_c = parsed_c
        for m_idx, lit_d in enumerate(target_lits):
            parsed_d = _rc._lit_atom_polarity(lit_d)
            if parsed_d is None:
                continue
            atom_d, pos_d = parsed_d
            if pos_c == pos_d:
                continue  # L's COMPLEMENT must match M -- same polarity can't
            theta0 = _match_atom_onesided(atom_c, atom_d, {})
            if theta0 is None:
                continue
            rest_c = [l for i, l in enumerate(subsumer_lits) if i != l_idx]
            rest_target = [l for i, l in enumerate(target_lits) if i != m_idx]
            theta = _match_literals_into(rest_c, rest_target, theta0)
            if theta is None:
                continue
            expected = frozenset(rest_target)
            if _rc._is_variant(expected, clause):
                return None
    return ("'subsumption_resolution': no subsumer literal's complement plus a "
            "one-sided match of its clause-mates licenses the stated clause")


def _is_false_constant_literal(lit: Node) -> bool:
    """Whether ``lit`` holds in no interpretation: the atom ``$false`` or the
    negation of the atom ``$true``."""
    parsed = _rc._lit_atom_polarity(lit)
    if parsed is None:
        return False
    atom, is_positive = parsed
    if atom.args:
        return False
    return (atom.predicate == "$false") if is_positive else (atom.predicate == "$true")


def _check_tstp_truth_constants(clause: FrozenSet[Node], ci: FrozenSet[Node]) -> Optional[str]:
    """``"true_and_false_elimination"``: the stated clause is the parent clause
    without some literals, each of which is false in every interpretation
    (``$false`` or ``¬$true``) — and without any other literal.

    Both clauses are read with their constant literals kept
    (:func:`_node_to_clause` with ``keep_constants=True``). The literals that are
    not such a constant must be the same on both sides up to a renaming of
    variables (a prover renames the variables of each statement); the constant
    literals of the stated clause must be among the parent's, so the step can
    neither keep a literal the parent does not have nor drop a literal that is
    not false. ``$true`` and ``¬$false`` are NOT false: a step that drops one of
    them (a tautology's literal) is rejected like any other dropped literal.
    """
    kept_by_parent = frozenset(lit for lit in ci if not _is_false_constant_literal(lit))
    constants_of_parent = frozenset(lit for lit in ci if _is_false_constant_literal(lit))
    kept_by_step = frozenset(lit for lit in clause if not _is_false_constant_literal(lit))
    constants_of_step = frozenset(lit for lit in clause if _is_false_constant_literal(lit))
    if not constants_of_step <= constants_of_parent:
        return "'true_and_false_elimination': the stated clause has a constant literal the parent does not have"
    if not _rc._is_variant(kept_by_parent, kept_by_step):
        return ("'true_and_false_elimination': the stated clause is not the parent clause "
                "without literals that are false in every interpretation ($false or ~$true): "
                "another literal was added or dropped")
    return None


_CHECKED_DISPATCH: Dict[str, Tuple[int, Callable]] = {
    "resolution": (2, _check_tstp_resolve),
    "factoring": (1, _check_tstp_factor),
    "superposition": (2, _check_tstp_superposition),
    "forward_demodulation": (2, _check_tstp_demodulation),
    "backward_demodulation": (2, _check_tstp_demodulation),
    "equality_resolution": (1, _check_tstp_equality_resolution),
    "forward_subsumption_resolution": (2, _check_tstp_subsumption_resolution),
    "backward_subsumption_resolution": (2, _check_tstp_subsumption_resolution),
    "spm": (2, _check_tstp_superposition),
    "rw": (2, _check_tstp_demodulation),
    "er": (1, _check_tstp_equality_resolution),
    "true_and_false_elimination": (1, _check_tstp_truth_constants),
}
assert set(_CHECKED_DISPATCH) == VAMPIRE_CHECKED_RULES | EPROVER_CHECKED_RULES

#: The core rules that read the ``$true`` / ``$false`` literals of a clause, and so
#: are handed clauses that keep them (every other rule gets the clause without).
_CONSTANT_READING_RULES: FrozenSet[str] = frozenset({"true_and_false_elimination"})


# ---------------------------------------------------------------------------
# Leaves and the entailment-checked clausification tier (tier 2)
# ---------------------------------------------------------------------------

def _check_leaf_formula(leaf: TstpStep, premises: Sequence[Node],
                        conclusion: Optional[Node], query: str) -> Tuple[bool, Optional[str]]:
    """Whether ``leaf`` (a :class:`~atp.tstp.TstpStep` with ``rule is None``)
    is an alpha-variant of one of the caller's own originals -- ``conclusion``
    when ``query == "conjecture"`` and ``leaf.role == "conjecture"``,
    otherwise some member of ``premises``."""
    if leaf.formula is None:
        return False, "formula failed to parse"
    if query == "conjecture" and leaf.role == "conjecture":
        if conclusion is None:
            return False, "role is 'conjecture' but no conclusion was supplied to match against"
        if _formula_alpha_equal(leaf.formula, conclusion):
            return True, None
        return False, "is not an alpha-variant of the supplied conclusion"
    for premise in premises:
        if _formula_alpha_equal(leaf.formula, premise):
            return True, None
    return False, "is not an alpha-variant of any supplied premise"


_TRUTH = Atom("__tstp_truth", [])


def _for_z3(node: Node) -> Node:
    """``node`` with TSTP's ``$true``/``$false`` made logical, for Z3.

    :func:`fol.tptp_input.parse_tptp_formula` reads them as ordinary 0-ary
    atoms named ``$true``/``$false``, which Z3 would treat as free
    propositions; they become ``T ∨ ¬T`` / ``T ∧ ¬T`` over one fixed atom,
    exactly true and exactly false in every model."""
    if isinstance(node, Atom):
        if node.predicate == "$true" and not node.args:
            return Or(_TRUTH, Not(_TRUTH))
        if node.predicate == "$false" and not node.args:
            return And(_TRUTH, Not(_TRUTH))
        return node
    if isinstance(node, Not):
        return Not(_for_z3(node.formula))
    if isinstance(node, (And, Or, Implies, Iff, Xor)):
        return type(node)(_for_z3(node.left), _for_z3(node.right))
    if isinstance(node, Quantifier):
        return Quantifier(node.type, node.variable, _for_z3(node.formula))
    return node


def _closed(node: Node) -> Node:
    """``node`` universally closed over its free variables -- the reading TSTP
    gives a clause's variables -- with ``$true``/``$false`` made logical."""
    out = _for_z3(node)
    names = sorted({v.name for v in free_variables(node) if isinstance(v, Variable)})
    for name in reversed(names):
        out = Quantifier("∀", Variable(name), out)
    return out


def _entailed(assumptions: Sequence[Node], formula: Node) -> bool:
    """Whether the (each separately closed) ``assumptions`` entail ``formula``.

    Z3, PROVED-only: ``unknown`` or a timeout is False, never a pass."""
    from .z3_models import is_valid  # deferred: z3_models pulls in the whole fol layer
    goal = _closed(formula)
    if assumptions:
        hypothesis = _closed(assumptions[0])
        for extra in assumptions[1:]:
            hypothesis = And(hypothesis, _closed(extra))
        goal = Implies(hypothesis, goal)
    return is_valid(goal, timeout=_ENTAILMENT_TIMEOUT_MS)


def _conjecture_misuse(rule: str, cited: Sequence[str]) -> str:
    return (f"rule {rule!r} cites the conjecture {cited[0]!r} itself; a refutation may "
            f"only use the conjecture through {sorted(_NEGATION_RULES)}")


def _check_clausification_step(step: TstpStep, results: Dict[str, "TstpStepResult"],
                               by_name: Dict[str, TstpStep],
                               conjecture_names: FrozenSet[str]) -> Tuple[bool, Optional[str]]:
    """Check a clausification/normalisation step SEMANTICALLY: its formula must
    be entailed by its parents (for a negation rule: by the negated
    conjecture). The specific transformation is not re-derived -- any sound
    clausifier output passes -- but a step that states something its parents
    do not license fails, which is all a refutation's soundness needs."""
    if step.formula is None:
        return False, "formula failed to parse"
    if not step.parents:
        return False, f"rule {step.rule!r} step has no resolvable parents"
    parents: List[TstpStep] = []
    for pname in step.parents:
        pres = results.get(pname)
        if pres is None or not pres.ok:
            return False, f"parent {pname!r} is not an earlier, successfully verified statement"
        parent = by_name[pname]
        if parent.formula is None:
            return False, f"parent {pname!r}'s formula failed to parse"
        parents.append(parent)
    cited = [p.name for p in parents if p.name in conjecture_names]
    if step.rule in _NEGATION_RULES:
        if len(cited) != len(parents):
            others = [p.name for p in parents if p.name not in conjecture_names]
            return False, (f"rule {step.rule!r} may only negate the conjecture, "
                           f"but also cites {others[0]!r}")
        negated = Not(_closed(parents[0].formula))
        if _entailed([negated], step.formula):
            return True, None
        return False, (f"rule {step.rule!r}: the stated formula is not entailed by the "
                       f"negated conjecture (Z3, PROVED-only)")
    if cited:
        return False, _conjecture_misuse(step.rule, cited)
    if _entailed([p.formula for p in parents], step.formula):
        return True, None
    return False, (f"rule {step.rule!r}: the stated formula is not entailed by its parents "
                   f"(Z3, PROVED-only, {_ENTAILMENT_TIMEOUT_MS} ms)")


# ---------------------------------------------------------------------------
# The checker
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class TstpStepResult:
    """The outcome of checking one :class:`~atp.tstp.TstpStep`.

    ``tier`` is one of:

    - ``"leaf"``: ``step.rule is None`` (a ``file(...)``-sourced original, or
      any other non-``inference(...)`` source); ``ok`` iff its formula is an
      alpha-variant of one of the caller's premises/conclusion.
    - ``"entailed"``: ``step.rule`` is a clausification/normalisation rule
      (:data:`VAMPIRE_CLAUSIFICATION_RULES` / :data:`EPROVER_CLAUSIFICATION_RULES`);
      ``ok`` iff every parent verified, none is the conjecture itself (unless
      the rule is ``negated_conjecture``/``assume_negation``, which may cite
      ONLY the conjecture), and Z3 proves the parents (resp. the negated
      conjecture) entail the stated formula.
    - ``"checked"``: ``step.rule`` is in the core independently-checked tier
      (:data:`VAMPIRE_CHECKED_RULES` / :data:`EPROVER_CHECKED_RULES`); ``ok``
      iff the re-derivation licenses the stated clause.
    - ``"unchecked"``: ``step.rule`` is outside every table above, or is
      ``skolemisation`` (satisfiability-preserving only); ``ok`` is always
      False, and ``detail`` names the rule.
    """

    name: str
    tier: str
    ok: bool
    detail: Optional[str] = None

    def to_dict(self) -> dict:
        """Serialise to a JSON-compatible dict."""
        return {"name": self.name, "tier": self.tier, "ok": self.ok, "detail": self.detail}


@dataclass(frozen=True)
class TstpCheckResult:
    """The outcome of checking a whole :class:`~atp.tstp.TstpDerivation`.

    ``verified`` is True iff EVERY step — leaf, entailed, and checked alike —
    came back ``ok``; this is deliberately all-or-nothing (see the module
    docstring's tier 3: one unchecked/unrecognised/failing rule anywhere
    makes the whole thing unverified), but ``steps`` carries the full
    per-step tiered breakdown so a caller can see exactly how far
    verification reached. ``error`` names the FIRST failing step
    (``"step <name> (<tier>): <reason>"``), or is ``None`` on full success.
    ``refuted`` is True iff some successfully-verified step's clause is
    empty (the empty-clause / ``$false`` sink of a refutation), tracked
    independently of ``verified`` exactly as
    :attr:`atp.resolution_check.ResolutionCheckResult.refuted` is.
    """

    verified: bool
    steps: Tuple[TstpStepResult, ...]
    error: Optional[str]
    refuted: bool

    def __bool__(self) -> bool:
        """A TstpCheckResult is truthy iff the whole derivation verified."""
        return self.verified

    def to_dict(self) -> dict:
        """Serialise to a JSON-compatible dict."""
        return {
            "verified": self.verified,
            "steps": [s.to_dict() for s in self.steps],
            "error": self.error,
            "refuted": self.refuted,
        }


def check_tstp_derivation(derivation: TstpDerivation, premises: Sequence[Node],
                          conclusion: Optional[Node] = None, *,
                          query: str = "conjecture") -> TstpCheckResult:
    """Independently check whether ``derivation`` genuinely holds.

    Args:
        derivation: a parsed :class:`~atp.tstp.TstpDerivation`
            (:func:`atp.tstp.parse_tstp_derivation`'s output).
        premises: the caller's own original premise formulas, in the SAME
            representation basis as the derivation's leaf statements (i.e.
            typically :func:`fol.tptp_input.parse_tptp_formula`'d from the
            exact TPTP problem text handed to the prover — predicate names
            already capitalised the way that parser does; a caller that
            renamed symbols before generating the TPTP problem must
            :func:`atp.tstp.reverse_map_derivation` first, or pass the
            renamed originals here).
        conclusion: the caller's original conclusion, required when
            ``query == "conjecture"`` and the derivation has a
            ``conjecture``-role leaf (every real Vampire/E fixture this
            module was developed against does); ``None`` is fine for a
            ``query == "refutation"`` derivation, where ``premises`` is
            understood to already hold the caller's whole folded
            premises-plus-negated-conclusion set (see
            :func:`atp.tstp.szs_to_verdict_fields`'s module docstring for
            what the two framings mean).
        query: ``"conjecture"`` or ``"refutation"`` — see ``conclusion``
            above and :func:`atp.tstp.szs_to_verdict_fields`.

    Returns:
        A :class:`TstpCheckResult` with the full per-step tiered breakdown.

    Raises:
        ValueError: ``query`` is neither ``"conjecture"`` nor ``"refutation"``.
    """
    if query not in ("conjecture", "refutation"):
        raise ValueError(
            f"check_tstp_derivation: query must be 'conjecture' or 'refutation', got {query!r}")

    by_name: Dict[str, TstpStep] = {step.name: step for step in derivation.steps}
    results: Dict[str, TstpStepResult] = {}
    clause_by_name: Dict[str, FrozenSet[Node]] = {}
    clause_with_constants_by_name: Dict[str, FrozenSet[Node]] = {}
    step_results: List[TstpStepResult] = []
    refuted = False
    first_error: Optional[str] = None
    # Leaves standing for the caller's conclusion: usable only negated.
    conjecture_names: FrozenSet[str] = frozenset(
        step.name for step in derivation.steps
        if query == "conjecture" and step.rule is None and step.role == "conjecture")

    for step in derivation.steps:
        clause = _node_to_clause(step.formula) if step.formula is not None else None
        if clause is not None:
            clause_by_name[step.name] = clause
        clause_with_constants = (_node_to_clause(step.formula, keep_constants=True)
                                 if step.formula is not None else None)
        if clause_with_constants is not None:
            clause_with_constants_by_name[step.name] = clause_with_constants

        if step.rule is None:
            tier = "leaf"
            ok, detail = _check_leaf_formula(step, premises, conclusion, query)
        elif step.rule in _SATISFIABILITY_ONLY_RULES:
            tier = "unchecked"
            ok, detail = False, (f"rule {step.rule!r} only preserves satisfiability, not "
                                 f"entailment; this checker does not certify it")
        elif step.rule in _CLAUSIFICATION_RULES:
            tier = "entailed"
            ok, detail = _check_clausification_step(step, results, by_name, conjecture_names)
        elif step.rule in _CHECKED_DISPATCH:
            tier = "checked"
            cited = [p for p in step.parents if p in conjecture_names]
            if cited:
                ok, detail = False, _conjecture_misuse(step.rule, cited)
            else:
                arity, checker = _CHECKED_DISPATCH[step.rule]
                if step.rule in _CONSTANT_READING_RULES:
                    ok, detail = _check_checked_step(step, arity, checker, results,
                                                     clause_with_constants_by_name,
                                                     clause_with_constants)
                else:
                    ok, detail = _check_checked_step(step, arity, checker, results,
                                                     clause_by_name, clause)
        else:
            tier = "unchecked"
            ok, detail = False, f"rule {step.rule!r} is not in this checker's clausification or core-checked tables"

        if ok and clause is not None and not clause:
            refuted = True

        result = TstpStepResult(name=step.name, tier=tier, ok=ok, detail=detail)
        results[step.name] = result
        step_results.append(result)
        if not ok and first_error is None:
            first_error = f"step {step.name!r} ({tier}): {detail}"

    verified = all(r.ok for r in step_results)
    return TstpCheckResult(verified=verified, steps=tuple(step_results),
                           error=first_error, refuted=refuted)


def _check_checked_step(step: TstpStep, arity: int, checker,
                        results: Dict[str, TstpStepResult],
                        clause_by_name: Dict[str, FrozenSet[Node]],
                        clause: Optional[FrozenSet[Node]]) -> Tuple[bool, Optional[str]]:
    """Shared plumbing for every core-checked rule: parent count/arity,
    "parents must be earlier and already verified", "every clause (own and
    parents') must be flat clausal form" -- then dispatches to ``checker``."""
    if len(step.parents) != arity:
        return False, f"rule {step.rule!r} takes {arity} parent(s), got {len(step.parents)}"
    parent_clauses = []
    for pname in step.parents:
        pres = results.get(pname)
        if pres is None or not pres.ok:
            return False, f"parent {pname!r} is not an earlier, successfully verified statement"
        pclause = clause_by_name.get(pname)
        if pclause is None:
            return False, f"parent {pname!r}'s formula is not in flat clausal (disjunction-of-literals) form"
        parent_clauses.append(pclause)
    if clause is None:
        return False, "this step's own formula is not in flat clausal (disjunction-of-literals) form"
    error = checker(clause, *parent_clauses)
    if error is not None:
        return False, error
    return True, None
