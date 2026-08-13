"""Sato distribution semantics — the ProbLog core, exact, no sampling.

Sato (*A Statistical Learning Method for Logic Programs*, ICLP 1995) and
ProbLog (De Raedt, Kimmig & Toivonen, IJCAI 2007) attach an independent
probability to each of a finite set of GROUND probabilistic facts and read off
the probability of a query as a sum over "total choices". Concretely: a
:class:`ProbProgram` is a set of :class:`ProbFact`\\ s (each an independent
Bernoulli-distributed ground atom), a set of definite-clause ``rules``, and a
set of deterministic ``hard_facts``. A **total choice** ``C`` is a subset of
the probabilistic facts (the ones chosen "true"; the rest are "false"); it has
weight ``Π_{f∈C} p_f · Π_{f∉C} (1−p_f)`` — the probability, under mutual
independence, that exactly this subset comes out true. Every total choice,
together with ``hard_facts`` and ``rules``, is a plain (non-probabilistic)
DEFINITE logic program, which — being definite (no negation, no disjunctive
heads) — has a UNIQUE least Herbrand model, computed here by straightforward
forward-chaining (no stratification needed: definite programs are always
stratified trivially). :func:`query`'s result is the sum, over every total
choice whose least model satisfies the goal, of that choice's weight — exactly,
in :class:`~fractions.Fraction` arithmetic throughout (never sampled, never a
float): with ``k`` probabilistic facts this sums ``2^k`` exact weights, not an
approximation of them.

**Rule language.** A rule is Kit-AST shaped as either a bare ground
:class:`~unicode_fol_kit.fol.nodes.Atom` (a fact with an implicitly-true empty
body), or a (possibly nested) ``∀``-quantification wrapping
``Implies(Body, Head)`` where ``Head`` is a single positive atom and ``Body``
is a conjunction of positive atoms. Negation anywhere, a non-atomic or
disjunctive head, an existential quantifier, or a variable used in the clause
but not bound by an enclosing ``∀`` are all refused with ``ValueError`` — this
is exactly the DEFINITE-clause fragment distribution semantics is defined
over; anything outside it has no unique least model to speak of, so it is
rejected loudly rather than silently coerced. ``hard_facts`` accepts the same
two shapes (ground atom, or ∀-quantified definite clause) — they differ from
``rules`` only in being unconditionally available in EVERY total choice's
program, never gated by a probabilistic fact's inclusion.

**Grounding.** Rules are grounded over the FINITE set of constants occurring
anywhere in the program (facts, rules, hard_facts) and the goal — the
"Herbrand universe" is deliberately this finite, program-derived set, not an
open-ended one, so grounding always terminates.

**Goal language and CLOSED-WORLD NEGATION.** A goal is a ground literal, or a
conjunction/disjunction/negation of such — **NEGATION IS EVALUATED AGAINST THE
LEAST HERBRAND MODEL UNDER THE CLOSED-WORLD ASSUMPTION**: ``¬p`` is true in a
given total choice's model iff ``p`` is NOT a member of that model's (unique,
forward-chained) least fixpoint. This is the standard ProbLog convention, not
a general negation-as-failure over a possibly-non-stratified program (definite
programs need none of that machinery — the least model is unique regardless of
which atoms end up outside it). ``∀``/``∃`` in the goal are expanded, before
evaluation, into a finite ``∧``/``∨`` over the same finite constant domain
used for grounding rules.

**Correctness-preserving pruning (``prune=True``, the default).** Only
probabilistic facts that lie in the goal's GROUND DEPENDENCY CONE — reachable
by walking grounded-rule body→head edges backward from a goal atom — can
possibly change whether that goal atom is derivable; every other fact
marginalises to a factor of 1 (its own probability mass sums away: ``p_f +
(1−p_f) = 1``) and is simply never enumerated, which is why omitting it from
both the choice enumeration AND the seed set of the least-model computation
never changes the result. This is the whole of the optimization: it narrows
which facts are enumerated as 2^k choices, never which RULES fire during
forward chaining. ``max_choice_facts`` (default 16, i.e. up to 65536 choices)
is a deliberate, overridable brake on the ``2^k`` enumeration over the
(pruned, if ``prune=True``) relevant fact set.

Public API: :class:`ProbFact`, :class:`ProbProgram`, :func:`query`.
"""

from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from typing import Dict, List, Sequence, Set, Tuple

from ..fol.nodes import (
    Node, Atom, Not, And, Or, Implies, Quantifier, Variable, Constant, substitute,
)

__all__ = ["ProbFact", "ProbProgram", "query"]


# ---------------------------------------------------------------------------
# Exact-rational helper (mirrors nilsson._as_exact_prob; kept local so this
# module has no dependency on its sibling).
# ---------------------------------------------------------------------------

def _as_exact_prob(value, label: str) -> Fraction:
    """Coerce ``value`` to an exact Fraction in [0, 1]; reject float (never sampled/rounded)."""
    if isinstance(value, bool) or not isinstance(value, (Fraction, int)):
        raise TypeError(
            f"ProbFact: {label} must be an exact Fraction (or int, coerced losslessly) "
            f"— got {type(value).__name__} {value!r}. Pass Fraction({label}) explicitly; "
            "a float is refused because this module never approximates a probability."
        )
    p = Fraction(value)
    if not (Fraction(0) <= p <= Fraction(1)):
        raise ValueError(f"ProbFact: {label} must satisfy 0 <= {label} <= 1; got {p}.")
    return p


# ---------------------------------------------------------------------------
# ProbFact / ProbProgram
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class ProbFact:
    """One independent Bernoulli-distributed GROUND atom: ``atom`` is true with probability ``prob``.

    ``atom`` must be a ground :class:`~unicode_fol_kit.fol.nodes.Atom` (no
    :class:`~unicode_fol_kit.fol.nodes.Variable` anywhere in its arguments) —
    distribution semantics assigns a probability to one concrete ground fact,
    not a schema; a parametrised probability needs a family of ``ProbFact``\\ s
    (one per grounding) or a deterministic ``∀``-rule deriving the pattern from
    such a family. ``prob`` is coerced to an exact ``Fraction`` (float rejected;
    see :func:`_as_exact_prob`).
    """

    atom: Node
    prob: Fraction

    def __post_init__(self):
        if not isinstance(self.atom, Atom):
            raise ValueError(f"ProbFact: atom must be an Atom, got {type(self.atom).__name__}.")
        if self.atom.variables():
            names = sorted(v.name for v in self.atom.variables())
            raise ValueError(
                f"ProbFact: atom {self.atom.to_unicode_str()!r} is not ground (free "
                f"variable(s) {names}) — a ProbFact assigns a probability to ONE ground "
                "atom, not a schema; ground it, or express the pattern with a "
                "deterministic ∀-quantified rule over a family of ground ProbFacts."
            )
        object.__setattr__(self, "prob", _as_exact_prob(self.prob, "prob"))


@dataclass(frozen=True)
class ProbProgram:
    """A distribution-semantics program: probabilistic facts, definite rules, hard facts.

    ``facts`` are the independent :class:`ProbFact`\\ s whose total choices
    define the distribution. ``rules`` and ``hard_facts`` both hold definite
    clauses in the shape documented in the module docstring (ground atom, or
    ∀-quantified ``Implies(Body, Head)``); ``hard_facts`` are simply always
    available (in every total choice), while ``rules`` are as well — the two
    fields are one combined rule set for forward chaining, kept separate only
    so callers can organise "background theory" apart from the rules that
    mediate between probabilistic facts and derived predicates. Malformed
    rules/hard_facts raise ``ValueError`` eagerly, at construction time.
    """

    facts: Sequence[ProbFact]
    rules: Sequence[Node]
    hard_facts: Sequence[Node] = ()

    def __post_init__(self):
        object.__setattr__(self, "facts", tuple(self.facts))
        object.__setattr__(self, "rules", tuple(self.rules))
        object.__setattr__(self, "hard_facts", tuple(self.hard_facts))
        for f in self.facts:
            if not isinstance(f, ProbFact):
                raise ValueError(f"ProbProgram: facts must be ProbFact, got {type(f).__name__}.")
        for r in self.rules:
            _decompose_rule(r, "rule")
        for hf in self.hard_facts:
            _decompose_rule(hf, "hard fact")


# ---------------------------------------------------------------------------
# Definite-clause validation
# ---------------------------------------------------------------------------

def _decompose_rule(node: Node, kind: str) -> Tuple[Tuple[Atom, ...], Atom, Tuple[str, ...]]:
    """Validate ``node`` as a definite clause; return ``(body_atoms, head, bound_var_names)``.

    Accepts exactly two shapes: a bare ground-or-not Atom (empty body,
    ``bound_var_names`` from any variables it uses is checked to be empty —
    plain atoms are never quantifier-wrapped in this grammar), or a chain of
    one-or-more ``∀`` quantifiers directly wrapping ``Implies(Body, Head)``
    with ``Head`` a single positive Atom and ``Body`` a conjunction of
    positive atoms. Anything else — negation anywhere, a disjunctive/negated
    head, an existential in the chain, or a variable used but not bound by the
    chain — raises ``ValueError`` naming ``kind`` (``"rule"`` / ``"hard fact"``).
    """
    if isinstance(node, Atom):
        if node.variables():
            names = sorted(v.name for v in node.variables())
            raise ValueError(
                f"ProbProgram: {kind} {node.to_unicode_str()!r} is a bare atom with free "
                f"variable(s) {names}; a variable must be bound by an enclosing ∀ over an "
                "Implies(Body, Head) clause, or the atom must be ground."
            )
        return (), node, ()

    bound: Set[str] = set()
    cur = node
    while isinstance(cur, Quantifier):
        if cur.type not in ("forall", "∀"):
            raise ValueError(
                f"ProbProgram: {kind} uses a non-universal quantifier {cur.type!r}; only "
                "ground atoms or ∀-quantified definite clauses are accepted (no ∃ — "
                "distribution semantics is defined over DEFINITE clauses only)."
            )
        bound.add(cur.variable.name)
        cur = cur.formula

    if not isinstance(cur, Implies):
        raise ValueError(
            f"ProbProgram: {kind} must be a ground Atom or a (possibly ∀-quantified) "
            f"Implies(Body, Head) definite clause; found {type(cur).__name__} under the "
            "quantifier chain."
        )

    head = cur.right
    if not isinstance(head, Atom):
        raise ValueError(
            f"ProbProgram: {kind} head must be a single positive Atom; found "
            f"{type(head).__name__} — negation or disjunction in the head is not a "
            "definite clause."
        )

    body_atoms: List[Atom] = []

    def _flatten_body(n: Node) -> None:
        if isinstance(n, Atom):
            body_atoms.append(n)
            return
        if isinstance(n, And):
            _flatten_body(n.left)
            _flatten_body(n.right)
            return
        raise ValueError(
            f"ProbProgram: {kind} body must be a conjunction of positive atoms; found "
            f"{type(n).__name__} — negation or disjunction in the body is not a definite "
            "clause."
        )

    _flatten_body(cur.left)

    used: Set[str] = set()
    for a in body_atoms + [head]:
        used |= {v.name for v in a.variables()}
    free = used - bound
    if free:
        raise ValueError(
            f"ProbProgram: {kind} has free variable(s) {sorted(free)} not bound by an "
            "enclosing ∀."
        )

    return tuple(body_atoms), head, tuple(sorted(bound))


# ---------------------------------------------------------------------------
# Constants, grounding, goal expansion
# ---------------------------------------------------------------------------

def _constants_in(node: Node, out: Set[str]) -> None:
    """Collect every Constant name occurring anywhere in ``node`` into ``out``."""
    for n in node.walk():
        if isinstance(n, Constant):
            out.add(n.name)


def _ground_clause(body_atoms: Tuple[Atom, ...], head: Atom, bound_vars: Tuple[str, ...],
                   constants: Tuple[str, ...]):
    """Yield every ``(ground_body, ground_head)`` instance of a clause over ``constants``.

    With no bound variables the clause is already ground and yields once
    unchanged. Otherwise every combination of constants for ``bound_vars`` is
    substituted in (capture-avoiding, via :func:`~unicode_fol_kit.fol.nodes.substitute`);
    with an empty ``constants`` domain and at least one bound variable this
    yields NOTHING (an empty-domain clause has no ground instances).
    """
    if not bound_vars:
        yield body_atoms, head
        return
    for combo in product(constants, repeat=len(bound_vars)):
        mapping = dict(zip(bound_vars, combo))

        def sub(term: Node) -> Node:
            for vname, cname in mapping.items():
                term = substitute(term, Variable(vname), Constant(cname))
            return term

        yield tuple(sub(a) for a in body_atoms), sub(head)


def _ground_definite_clauses(nodes: Sequence[Node], kind: str, constants: Tuple[str, ...]):
    """Validate+ground every clause in ``nodes``; split into always-true seeds and body-gated rules.

    A grounding whose body comes out empty (a bare fact, or a clause whose
    body atoms all disappeared — impossible here since body atoms are never
    dropped, only substituted, but kept general) is a SEED — always true,
    independent of any total choice. Everything else is a grounded rule
    ``(ground_body, ground_head)`` for forward chaining.
    """
    seeds: List[Atom] = []
    grounded: List[Tuple[Tuple[Atom, ...], Atom]] = []
    for node in nodes:
        body_atoms, head, bound_vars = _decompose_rule(node, kind)
        for g_body, g_head in _ground_clause(body_atoms, head, bound_vars, constants):
            if g_body:
                grounded.append((g_body, g_head))
            else:
                seeds.append(g_head)
    return seeds, grounded


_GOAL_LANGUAGE = (
    "query: unsupported node type {cls} in a goal; expected a ground literal, a "
    "∧/∨/¬ combination of such, or a ∀/∃ quantifier over the program's finite "
    "constant domain (→/↔ are not part of the goal language — encode them via "
    "¬/∧/∨ if needed)."
)


def _expand_goal(node: Node, constants: Tuple[str, ...]) -> Node:
    """Expand every ∀/∃ in ``node`` into a finite ∧/∨ over ``constants``; validate the rest.

    Recurses through Atom/Not/And/Or unchanged (validating shape); a
    Quantifier is expanded via :func:`~unicode_fol_kit.fol.nodes.substitute`
    into the conjunction (∀) or disjunction (∃) of its body over every
    constant, each branch recursively expanded (so nested quantifiers work).
    Raises ``ValueError`` on an empty constant domain under a quantifier, or
    on any node type outside the goal language.
    """
    if isinstance(node, Atom):
        return node
    if isinstance(node, Not):
        return Not(_expand_goal(node.formula, constants))
    if isinstance(node, And):
        return And(_expand_goal(node.left, constants), _expand_goal(node.right, constants))
    if isinstance(node, Or):
        return Or(_expand_goal(node.left, constants), _expand_goal(node.right, constants))
    if isinstance(node, Quantifier):
        if not constants:
            raise ValueError(
                "query: cannot expand a ∀/∃ in the goal over an empty constant domain "
                "(the program and goal mention no constants at all)."
            )
        branches = [_expand_goal(substitute(node.formula, node.variable, Constant(c)), constants)
                    for c in constants]
        if node.type in ("forall", "∀"):
            result = branches[0]
            for b in branches[1:]:
                result = And(result, b)
            return result
        if node.type in ("exists", "∃"):
            result = branches[0]
            for b in branches[1:]:
                result = Or(result, b)
            return result
        raise ValueError(f"query: unknown quantifier type {node.type!r} in goal.")
    raise ValueError(_GOAL_LANGUAGE.format(cls=type(node).__name__))


def _goal_atom_keys(node: Node, out: Set[str]) -> None:
    """Collect the surface-form keys of every Atom leaf in a (already-expanded) goal."""
    if isinstance(node, Atom):
        out.add(node.to_unicode_str())
        return
    if isinstance(node, Not):
        _goal_atom_keys(node.formula, out)
        return
    if isinstance(node, (And, Or)):
        _goal_atom_keys(node.left, out)
        _goal_atom_keys(node.right, out)
        return
    raise ValueError(_GOAL_LANGUAGE.format(cls=type(node).__name__))  # pragma: no cover — defensive


def _eval_goal(node: Node, known_true: Set[str]) -> bool:
    """Evaluate an expanded ground goal against a least-model's atom-key set."""
    if isinstance(node, Atom):
        return node.to_unicode_str() in known_true
    if isinstance(node, Not):
        return not _eval_goal(node.formula, known_true)
    if isinstance(node, And):
        return _eval_goal(node.left, known_true) and _eval_goal(node.right, known_true)
    if isinstance(node, Or):
        return _eval_goal(node.left, known_true) or _eval_goal(node.right, known_true)
    raise ValueError(_GOAL_LANGUAGE.format(cls=type(node).__name__))  # pragma: no cover — defensive


# ---------------------------------------------------------------------------
# Dependency cone (pruning) and least Herbrand model (forward chaining)
# ---------------------------------------------------------------------------

def _dependency_cone(goal_keys: Set[str],
                     grounded_rules: List[Tuple[Tuple[Atom, ...], Atom]]) -> Set[str]:
    """Backward-reachable atom keys from ``goal_keys`` over grounded body→head edges.

    A conservative (safe-to-over-include, never under-include) approximation
    of "could possibly affect whether some goal atom is derivable": walks
    grounded-rule edges in REVERSE (head -> its body atoms) from every goal
    atom, transitively. See the module docstring's pruning-correctness note.
    """
    predecessors: Dict[str, Set[str]] = {}
    for body_atoms, head in grounded_rules:
        hk = head.to_unicode_str()
        predecessors.setdefault(hk, set()).update(a.to_unicode_str() for a in body_atoms)

    seen = set(goal_keys)
    frontier = list(goal_keys)
    while frontier:
        cur = frontier.pop()
        for pred in predecessors.get(cur, ()):
            if pred not in seen:
                seen.add(pred)
                frontier.append(pred)
    return seen


def _least_model(seed_keys: Set[str],
                 grounded_rules: List[Tuple[Tuple[Atom, ...], Atom]]) -> Set[str]:
    """Forward-chain ``grounded_rules`` from ``seed_keys`` to the (unique) least Herbrand model."""
    known = set(seed_keys)
    changed = True
    while changed:
        changed = False
        for body_atoms, head in grounded_rules:
            hk = head.to_unicode_str()
            if hk in known:
                continue
            if all(a.to_unicode_str() in known for a in body_atoms):
                known.add(hk)
                changed = True
    return known


# ---------------------------------------------------------------------------
# Public query
# ---------------------------------------------------------------------------

def query(program: ProbProgram, goal: Node, *, max_choice_facts: int = 16,
         prune: bool = True) -> Fraction:
    """Return the exact distribution-semantics probability of ``goal`` under ``program``.

    Sums the weight of every total choice of the (by default, pruned to the
    goal's dependency cone — see the module docstring) relevant probabilistic
    facts whose resulting least Herbrand model satisfies ``goal``. The result
    is an exact :class:`~fractions.Fraction` — Z3 is not used anywhere in this
    module; the arithmetic is plain Python ``Fraction`` products and sums over
    a finite, explicitly enumerated set of choices.

    Raises:
        ValueError: on a malformed ``goal`` (outside ground-literal /
            ∧/∨/¬ / ∀/∃-over-constants); if the number of relevant
            probabilistic facts exceeds ``max_choice_facts`` (the choice
            enumeration is ``2^k`` — an explicit, overridable brake); or if
            ``program`` itself is malformed (raised eagerly by
            :class:`ProbProgram` / :class:`ProbFact` at construction time,
            before ``query`` is ever called).
    """
    constant_names: Set[str] = set()
    for f in program.facts:
        _constants_in(f.atom, constant_names)
    for r in program.rules:
        _constants_in(r, constant_names)
    for hf in program.hard_facts:
        _constants_in(hf, constant_names)
    _constants_in(goal, constant_names)
    constants = tuple(sorted(constant_names))

    ground_goal = _expand_goal(goal, constants)

    rule_seeds, grounded_rules = _ground_definite_clauses(program.rules, "rule", constants)
    hard_seeds, hard_grounded = _ground_definite_clauses(program.hard_facts, "hard fact", constants)
    always_true = {a.to_unicode_str() for a in rule_seeds + hard_seeds}
    all_grounded_rules = grounded_rules + hard_grounded

    if prune:
        goal_keys: Set[str] = set()
        _goal_atom_keys(ground_goal, goal_keys)
        cone = _dependency_cone(goal_keys, all_grounded_rules)
        relevant = [f for f in program.facts if f.atom.to_unicode_str() in cone]
    else:
        relevant = list(program.facts)

    if len(relevant) > max_choice_facts:
        raise ValueError(
            f"query: {len(relevant)} relevant probabilistic facts exceeds "
            f"max_choice_facts={max_choice_facts}. The total-choice enumeration is "
            f"O(2^k) — {len(relevant)} facts means 2**{len(relevant)} = "
            f"{2 ** len(relevant)} choices. Reduce the program (or tighten the goal, "
            "which tightens the dependency-cone pruning), or pass a larger "
            "max_choice_facts explicitly if that blow-up is intended."
        )

    total = Fraction(0)
    for combo in product((False, True), repeat=len(relevant)):
        weight = Fraction(1)
        chosen_keys = set(always_true)
        for fact, is_chosen in zip(relevant, combo):
            weight *= fact.prob if is_chosen else (Fraction(1) - fact.prob)
            if is_chosen:
                chosen_keys.add(fact.atom.to_unicode_str())
        if weight == 0:
            continue
        known_true = _least_model(chosen_keys, all_grounded_rules)
        if _eval_goal(ground_goal, known_true):
            total += weight
    return total
