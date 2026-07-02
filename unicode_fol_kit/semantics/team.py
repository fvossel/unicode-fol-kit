"""Team semantics for dependence logic and IF logic (Väänänen 2007).

In team semantics a formula is satisfied not by a single variable assignment
but by a TEAM: a *set* of assignments, each mapping variable names to elements
of a :class:`~unicode_fol_kit.semantics.tarski.Structure`'s domain. Teams model
*information states* — the set of assignments still considered possible — and
this is what gives meaning to the two team-native constructs:

- the **dependence atom** ``=(t₁, …, tₙ)``: within the team, the value of
  ``tₙ`` is functionally determined by the values of ``t₁ … tₙ₋₁`` (with a
  single argument, ``=(t)`` says ``t`` is constant across the team);
- the **slashed existential** ``∃x/{y, …} φ`` of IF logic: the witness for
  ``x`` must be chosen *uniformly in* (independently of) the slashed
  variables.

This module implements Väänänen's STRICT semantics (Dependence Logic, 2007)
over finite structures, by brute-force search:

- ``X ⊨ α`` for a first-order literal ``α`` (an atom or a negated atom): every
  assignment in ``X`` satisfies ``α`` classically — literals are FLAT. Single-
  assignment evaluation is delegated to the Tarskian evaluator.
- ``X ⊨ φ∧ψ`` iff ``X ⊨ φ`` and ``X ⊨ ψ``.
- ``X ⊨ φ∨ψ`` iff ``X = Y ∪ Z`` with ``Y ⊨ φ`` and ``Z ⊨ ψ`` (the SPLIT
  disjunction — the team divides its assignments between the disjuncts).
- ``X ⊨ ∃x φ`` iff some supplementing function ``F : X → dom`` gives
  ``X[F/x] := {s[x↦F(s)] : s ∈ X} ⊨ φ`` (strict: one witness per assignment).
- ``X ⊨ ∀x φ`` iff the duplicated team ``X[dom/x] := {s[x↦a] : s ∈ X, a ∈ dom}``
  satisfies ``φ``.
- ``X ⊨ =(t₁,…,tₙ)`` iff any two assignments in ``X`` agreeing on the values
  of ``t₁ … tₙ₋₁`` also agree on the value of ``tₙ``.
- ``X ⊨ ∃x/{V} φ`` iff some ``F : X → dom`` that is UNIFORM IN ``V`` — i.e.
  ``F(s) = F(s')`` whenever ``s`` and ``s'`` agree on every variable outside
  ``V ∪ {x}`` — gives ``X[F/x] ⊨ φ``.

The EMPTY team satisfies every formula of the fragment (the empty-team
property), and every formula is DOWNWARD CLOSED: if ``X ⊨ φ`` and ``Y ⊆ X``
then ``Y ⊨ φ`` (Väänänen 2007, Prop. 3.10) — both facts are relied on below
and pinned by the test suite.

The team fragment is deliberately small: literals, ``∧``, split ``∨``,
``∀``/``∃``, ``=(…)``, and ``∃x/{…}``. ``→``/``↔`` have no faithful team
semantics here and are rejected with :class:`TypeError`, as is negation of
anything but an atom (dual negation of team atoms is out of scope).

Everything is evaluated over FINITE structures only. This is not a stopgap:
dependence logic has the expressive power of existential second-order logic,
so its validity problem is not even arithmetical (Väänänen 2007) — finite
model checking is the honest thing a library can offer.
"""

from itertools import product
from typing import Any, Dict, Iterable, List, Mapping, Tuple

from ..fol.nodes import (
    Node, Atom, Not, And, Or, Quantifier, Dependence, SlashedExists,
)
from .tarski import (
    Structure, term_value,
    satisfies as _tarski_satisfies,
    _FORALL, _EXISTS,
)

# A team is normalised internally to a tuple of plain dicts (duplicates
# removed — a team is a SET of assignments).
Team = Tuple[Dict[str, Any], ...]

#: Ceiling on the number of candidates any single brute-force search may
#: enumerate. Witness-function searches for ∃ / ∃x/{…} try ``|dom| ** k``
#: candidates (k = number of assignments, resp. uniformity classes) and the
#: split-disjunction search tries ``2 ** |X|`` subteams; if a search would
#: exceed this bound a :class:`ValueError` is raised instead of hanging.
#: The default 65536 = 4**8 = 2**16 admits the documented working scale
#: (|domain| ≤ 4 with teams of up to 8 assignments; splits of teams of up to
#: 16 assignments).
MAX_TEAM_SEARCH = 65536


def _normalise_team(team: Iterable[Mapping[str, Any]]) -> Team:
    """Copy an iterable of assignment mappings into a deduplicated tuple of dicts.

    A team is a set of assignments, so duplicates are dropped (two assignments
    are the same iff they bind the same variables to the same values). The
    input mappings are copied and never mutated.
    """
    seen = set()
    out: List[Dict[str, Any]] = []
    for s in team:
        d = dict(s)
        key = frozenset(d.items())
        if key not in seen:
            seen.add(key)
            out.append(d)
    return tuple(out)


def _dedupe(assignments: Iterable[Dict[str, Any]]) -> Team:
    """Deduplicate freshly built assignments (already dicts) into a team tuple."""
    seen = set()
    out: List[Dict[str, Any]] = []
    for d in assignments:
        key = frozenset(d.items())
        if key not in seen:
            seen.add(key)
            out.append(d)
    return tuple(out)


def _guard(candidates: int, what: str) -> None:
    """Raise a clear ValueError when a brute-force search would be too large.

    ``candidates`` is the exact number of alternatives the search would
    enumerate; the bound is :data:`MAX_TEAM_SEARCH`.
    """
    if candidates > MAX_TEAM_SEARCH:
        raise ValueError(
            f"team_satisfies: the {what} search would enumerate {candidates} "
            f"candidates, above the bound MAX_TEAM_SEARCH = {MAX_TEAM_SEARCH}. "
            "Team-semantic model checking is brute-force and exponential; use "
            "a smaller domain or team (the documented scale is |domain| <= 4 "
            "with teams of <= 8 assignments)."
        )


def _fragment_error(formula: Node) -> TypeError:
    """Build the rejection error for nodes outside the team-semantics fragment."""
    return TypeError(
        f"team_satisfies: {type(formula).__name__} is outside the "
        "team-semantics fragment. Dependence/IF evaluation covers literals "
        "(atoms and negated atoms), ∧, the splitting ∨, ∀, ∃, dependence "
        "atoms =(…), and slashed existentials ∃x/{…}. In particular → and ↔ "
        "have no faithful team semantics in this fragment, ¬ applies to atoms "
        "only, and dual negation of =(…) / ∃x/{…} is out of scope."
    )


def _literal_holds(literal: Node, structure: Structure,
                   assignment: Mapping[str, Any]) -> bool:
    """Evaluate a FO literal (atom or negated atom) under ONE assignment.

    Delegates to the classical Tarskian evaluator, which already interprets
    named predicates, infix equality/disequality, and the order comparisons.
    """
    return _tarski_satisfies(literal, structure, assignment)


def _team_sat(formula: Node, structure: Structure, team: Team) -> bool:
    """Recursive strict-semantics satisfaction: does ``team`` satisfy ``formula``?

    ``team`` is already normalised (tuple of deduplicated dicts). Every case
    below is written so that the empty team returns True (the empty-team
    property): ``all(...)`` over no assignments holds, the empty team splits
    into two empty halves, and the witness-function searches admit the empty
    function ``F = ∅`` (``itertools.product(dom, repeat=0)`` yields exactly
    one empty choice).
    """
    # --- literals: FLAT — every assignment must satisfy them classically ---
    if isinstance(formula, Atom):
        return all(_literal_holds(formula, structure, s) for s in team)

    if isinstance(formula, Not):
        inner = formula.formula
        if isinstance(inner, Atom):
            return all(not _literal_holds(inner, structure, s) for s in team)
        # Dual negation of team atoms, and ¬ of anything compound, are out of
        # scope: the fragment is negation-normal with ¬ on atoms only.
        raise _fragment_error(formula)

    # --- conjunction: both conjuncts on the SAME team ---
    if isinstance(formula, And):
        return (_team_sat(formula.left, structure, team)
                and _team_sat(formula.right, structure, team))

    # --- split disjunction: X = Y ∪ Z with Y ⊨ φ and Z ⊨ ψ ---
    if isinstance(formula, Or):
        n = len(team)
        _guard(2 ** n, "split-disjunction (2^|team|)")
        # Completeness of searching PARTITIONS only: dependence logic is
        # downward closed (Väänänen 2007, Prop. 3.10) — if Y ⊨ φ and Y' ⊆ Y
        # then Y' ⊨ φ. So whenever a possibly-overlapping cover X = Y ∪ Z has
        # Y ⊨ φ and Z ⊨ ψ, the partition (Y, X∖Y) also works: X∖Y ⊆ Z, hence
        # X∖Y ⊨ ψ by downward closure. Enumerating the 2^|X| subsets Y with
        # complement X∖Y therefore loses nothing.
        for mask in range(2 ** n):
            left_part = tuple(s for i, s in enumerate(team) if mask >> i & 1)
            right_part = tuple(s for i, s in enumerate(team) if not mask >> i & 1)
            if (_team_sat(formula.left, structure, left_part)
                    and _team_sat(formula.right, structure, right_part)):
                return True
        return False

    # --- quantifiers ---
    if isinstance(formula, Quantifier):
        var = formula.variable.name
        dom = structure.domain

        if formula.type in _FORALL:
            # Duplication: X[dom/x] = {s[x↦a] : s ∈ X, a ∈ dom}. Polynomial
            # growth (|X|·|dom| before deduplication) — no guard needed here;
            # any downstream search guards itself.
            duplicated = _dedupe({**s, var: a} for s in team for a in dom)
            return _team_sat(formula.formula, structure, duplicated)

        if formula.type in _EXISTS:
            # Strict supplementation: search all F : X → dom. Each F is a
            # tuple of one witness per assignment (in team order); for the
            # empty team the single empty tuple encodes F = ∅.
            _guard(len(dom) ** len(team), "existential witness function")
            for choice in product(dom, repeat=len(team)):
                supplemented = _dedupe(
                    {**s, var: v} for s, v in zip(team, choice)
                )
                if _team_sat(formula.formula, structure, supplemented):
                    return True
            return False

        raise ValueError(f"Unknown quantifier type: {formula.type!r}")

    # --- dependence atom =(t₁, …, tₙ) ---
    if isinstance(formula, Dependence):
        *determinants, dependent = formula.args
        # tₙ is a function of t₁…tₙ₋₁ across the team: record the dependent
        # value seen for each tuple of determinant values; a clash refutes.
        # With n = 1 the determinant tuple is always (), so this reduces to
        # constancy of the single term. The empty team holds vacuously.
        witnessed: Dict[Tuple[Any, ...], Any] = {}
        for s in team:
            key = tuple(term_value(t, structure, s) for t in determinants)
            value = term_value(dependent, structure, s)
            if key in witnessed:
                if witnessed[key] != value:
                    return False
            else:
                witnessed[key] = value
        return True

    # --- slashed existential ∃x/{V} φ ---
    if isinstance(formula, SlashedExists):
        var = formula.variable.name
        dom = structure.domain
        hidden = set(formula.slashed) | {var}
        # F must be uniform in V: F(s) = F(s') whenever s and s' agree on
        # every variable OUTSIDE V ∪ {x}. Equivalently, F factors through the
        # "visible part" of each assignment (its restriction away from the
        # hidden variables), so the uniform functions are exactly the choices
        # of one witness per visible-part equivalence class.
        class_index: Dict[frozenset, int] = {}
        member_class: List[int] = []
        for s in team:
            visible = frozenset(
                (k, v) for k, v in s.items() if k not in hidden
            )
            if visible not in class_index:
                class_index[visible] = len(class_index)
            member_class.append(class_index[visible])
        _guard(len(dom) ** len(class_index), "uniform (slashed) witness function")
        for choice in product(dom, repeat=len(class_index)):
            supplemented = _dedupe(
                {**s, var: choice[ci]} for s, ci in zip(team, member_class)
            )
            if _team_sat(formula.formula, structure, supplemented):
                return True
        return False

    # --- everything else (→, ↔, ⊕, modal, fuzzy, lambda, sorted, …) ---
    raise _fragment_error(formula)


def team_satisfies(structure: Structure, team: Iterable[Mapping[str, Any]],
                   formula: Node) -> bool:
    """Return whether ``team`` satisfies ``formula`` in ``structure``.

    Väänänen's strict team semantics over a finite structure. ``team`` is any
    iterable of assignments (mappings from variable names to domain elements);
    it is copied and deduplicated internally, so the caller's dicts are never
    mutated and duplicates are harmless.

    Args:
        structure: a finite first-order :class:`Structure` (the same class the
            Tarskian evaluator uses).
        team: an iterable of ``dict[str, element]`` assignments. The empty
            team satisfies every formula of the fragment.
        formula: a formula of the team fragment — literals, ``∧``, the
            splitting ``∨``, ``∀``/``∃``, dependence atoms ``=(…)``, and
            slashed existentials ``∃x/{…}`` (parse with
            ``MSFLParser(dependence=True)``).

    Raises:
        TypeError: for a node outside the team fragment (``→``, ``↔``, ``¬``
            of a non-atom, dual negation of team atoms, modal/fuzzy nodes, …).
        ValueError: when a brute-force search would exceed
            :data:`MAX_TEAM_SEARCH` candidates.
    """
    return _team_sat(formula, structure, _normalise_team(team))


def team_models(structure: Structure, formula: Node) -> bool:
    """Return whether the structure makes the SENTENCE true: ``{∅} ⊨ formula``.

    Sentence evaluation in team semantics starts from the singleton team
    containing just the empty assignment (NOT the empty team, which satisfies
    everything). Quantifiers then grow the team: each ``∀`` duplicates it over
    the domain and each ``∃`` supplements it with witnesses.
    """
    return team_satisfies(structure, ({},), formula)
