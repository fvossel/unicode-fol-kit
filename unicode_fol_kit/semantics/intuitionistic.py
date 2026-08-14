"""Intuitionistic propositional logic — Kripke semantics and a validity/countermodel search.

Intuitionistic logic drops the law of excluded middle and double-negation elimination;
its models are **Kripke models**: a partial order of *worlds* (stages of knowledge)
with a **monotone** forcing relation (once an atom is forced at a world it is forced at
every later world). The connectives ``→`` and ``¬`` quantify over future worlds, which
is exactly what makes ``P ∨ ¬P`` and ``¬¬P → P`` fail.

- :class:`IntKripkeModel` — build a model and ask ``model.forces(world, φ)``.
- :func:`int_valid` — is ``φ`` intuitionistically valid? Decided by searching every
  small Kripke model (intuitionistic propositional logic has the finite-model property,
  so this is a genuine decision procedure up to ``max_worlds`` worlds).
- :func:`int_countermodel` — a model + world where ``φ`` fails (a witness that it is
  *not* intuitionistically valid), or None.

The **propositional** fragment is decided exactly (finite-model property). The
**first-order** fragment (``∀x`` / ``∃x``) is handled over *increasing-domain* Kripke
models — ``w ⊩ ∀x φ`` quantifies over every later world and every individual existing
there — by a *bounded* search: a counter-model it finds genuinely refutes validity,
but a clean search does **not** prove validity (first-order intuitionistic logic is
undecidable, and some non-theorems such as the double-negation shift have only infinite
counter-models, being valid in every finite model). Every intuitionistic validity is
also classically valid, which the test-suite cross-checks.

Public API: :class:`IntKripkeModel`, :func:`int_valid`, :func:`int_countermodel`.
"""

from dataclasses import dataclass
from itertools import combinations, product
from typing import Dict, FrozenSet, List, Optional, Tuple

from ..fol.nodes import (
    Node, Atom, Not, And, Or, Xor, Implies, Iff, Quantifier, SortedQuantifier,
    Constant, Function, substitute,
)
from ..fol._so_nodes import SecondOrderQuantifier


def _is_propositional(formula: Node) -> bool:
    """True iff ``formula`` has no quantifier (the decidable propositional fragment)."""
    return not any(
        isinstance(node, (Quantifier, SortedQuantifier, SecondOrderQuantifier))
        for node in formula.walk())


def _reject_second_order(formula: Node) -> None:
    """Reject a second-order quantifier / sorted quantifier in the FO search."""
    for node in formula.walk():
        if isinstance(node, SecondOrderQuantifier):
            raise ValueError("intuitionistic: second-order quantifiers are not supported.")
        if isinstance(node, SortedQuantifier):
            raise ValueError(
                "intuitionistic: sorted quantifiers are not supported; use plain ∀x/∃x.")
        if isinstance(node, Function):
            raise ValueError(
                "intuitionistic: function terms are not supported in the first-order "
                "Kripke search; use predicates over variables and constants.")


@dataclass(frozen=True)
class IntKripkeModel:
    """A finite intuitionistic Kripke model over the worlds ``0`` to ``n-1``.

    ``upset[w]`` is the set of worlds accessible from ``w`` (its up-set in the partial
    order, reflexive and transitive — including ``w`` itself). ``valuation[key]`` is the
    up-closed set of worlds forcing the atom ``key`` (its surface form). Build directly,
    or let :func:`int_countermodel` produce one.
    """

    upset: Dict[int, FrozenSet[int]]
    valuation: Dict[str, FrozenSet[int]]
    domains: Optional[Dict[int, FrozenSet]] = None

    def forces(self, world: int, formula: Node) -> bool:
        """Return whether ``world`` forces ``formula`` (the intuitionistic clauses).

        First-order clauses (when the model carries per-world ``domains``, which must
        be **increasing** along the order): ``w ⊩ ∀x φ`` iff for every later ``w' ≥ w``
        and every ``d ∈ D_{w'}``, ``w' ⊩ φ[x:=d]``; ``w ⊩ ∃x φ`` iff some ``d ∈ D_w``
        has ``w ⊩ φ[x:=d]``.
        """
        if isinstance(formula, Quantifier):
            if self.domains is None:
                raise ValueError(
                    "intuitionistic forcing: a quantifier needs per-world domains "
                    "(build the model with domains={world: [...]}).")
            var = formula.variable
            if formula.type in ("∀", "forall"):
                return all(
                    self.forces(w2, substitute(formula.formula, var, Constant(d)))
                    for w2 in self.upset[world] for d in self.domains[w2])
            if formula.type in ("∃", "exists"):
                return any(
                    self.forces(world, substitute(formula.formula, var, Constant(d)))
                    for d in self.domains[world])
            raise ValueError(f"intuitionistic forcing: unknown quantifier {formula.type!r}")
        if isinstance(formula, Atom):
            return world in self.valuation.get(formula.to_unicode_str(), frozenset())
        if isinstance(formula, And):
            return self.forces(world, formula.left) and self.forces(world, formula.right)
        if isinstance(formula, Or):
            return self.forces(world, formula.left) or self.forces(world, formula.right)
        if isinstance(formula, Implies):
            # w ⊩ A→B  iff  for every w' ≥ w, w' ⊩ A implies w' ⊩ B.
            return all(self.forces(w2, formula.right)
                       for w2 in self.upset[world] if self.forces(w2, formula.left))
        if isinstance(formula, Not):
            # w ⊩ ¬A  iff  no w' ≥ w forces A.
            return not any(self.forces(w2, formula.formula) for w2 in self.upset[world])
        if isinstance(formula, Iff):
            return (self.forces(world, Implies(formula.left, formula.right))
                    and self.forces(world, Implies(formula.right, formula.left)))
        if isinstance(formula, Xor):
            # Defined intuitionistically as (A ∨ B) ∧ ¬(A ∧ B).
            a, b = formula.left, formula.right
            return self.forces(world, And(Or(a, b), Not(And(a, b))))
        raise ValueError(f"intuitionistic forcing: unsupported node "
                         f"{type(formula).__name__}")


def _atom_keys(formula: Node) -> List[str]:
    """Distinct atom surface-forms (propositional variables) in ``formula``."""
    keys: List[str] = []
    seen = set()
    for node in formula.walk():
        if isinstance(node, Atom):
            key = node.to_unicode_str()
            if key not in seen:
                seen.add(key)
                keys.append(key)
    return keys


def _partial_orders(n: int):
    """Yield each partial order on ``{0..n-1}`` as a dict ``world -> up-set frozenset``.

    Enumerates reflexive relations and keeps the transitive (and antisymmetric) ones;
    the up-set ``upset[w] = {w' : w ≤ w'}`` is what the forcing clauses consult.
    """
    worlds = list(range(n))
    off_diagonal = [(i, j) for i in worlds for j in worlds if i != j]
    for mask in product((False, True), repeat=len(off_diagonal)):
        leq = {(i, i) for i in worlds}
        leq |= {pair for pair, inc in zip(off_diagonal, mask) if inc}
        # transitivity
        if any((a, b) in leq and (b, c) in leq and (a, c) not in leq
               for a in worlds for b in worlds for c in worlds):
            continue
        # antisymmetry (a genuine partial order; preorders collapse to these for forcing)
        if any(a != b and (a, b) in leq and (b, a) in leq for a in worlds for b in worlds):
            continue
        yield {w: frozenset(j for j in worlds if (w, j) in leq) for w in worlds}


def _monotone_valuations(upset: Dict[int, FrozenSet[int]], keys: List[str]):
    """Yield every monotone (up-closed) valuation of ``keys`` over the order ``upset``."""
    worlds = list(upset)
    # Up-closed subsets: a set S with w∈S ⇒ upset[w] ⊆ S.
    upclosed = []
    for r in range(len(worlds) + 1):
        for combo in combinations(worlds, r):
            s = frozenset(combo)
            if all(upset[w] <= s for w in s):
                upclosed.append(s)
    for choice in product(upclosed, repeat=len(keys)):
        yield dict(zip(keys, choice))


def _upclosed_subsets(upset: Dict[int, FrozenSet[int]], allowed) -> List[FrozenSet[int]]:
    """Every up-closed subset of the (itself up-closed) world set ``allowed``."""
    worlds = sorted(allowed)
    out: List[FrozenSet[int]] = []
    for r in range(len(worlds) + 1):
        for combo in combinations(worlds, r):
            s = frozenset(combo)
            if all(upset[w] <= s for w in s):
                out.append(s)
    return out


def _increasing_domains(upset: Dict[int, FrozenSet[int]], consts: List[str], n_fresh: int):
    """Yield each increasing per-world domain over ``consts`` + up to ``n_fresh`` elements.

    Constants exist at every world (rigid). A base fresh element ``_e0`` exists
    everywhere so no world is empty; each further fresh element appears on an
    up-closed set of worlds (so the domains grow along the order).
    """
    worlds = sorted(upset)
    base = set(consts)
    fresh = [f"_e{i}" for i in range(n_fresh)]
    if not fresh:
        if base:
            yield {w: frozenset(base) for w in worlds}
        return
    always = frozenset(worlds)
    var_fresh = fresh[1:]
    options = _upclosed_subsets(upset, worlds)
    for appearances in product(options, repeat=len(var_fresh)):
        appear = {fresh[0]: always}
        appear.update(zip(var_fresh, appearances))
        domains = {}
        for w in worlds:
            elems = set(base) | {fresh[0]}
            elems.update(e for e in var_fresh if w in appear[e])
            domains[w] = frozenset(elems)
        yield domains


def _fo_countermodel(formula: Node, max_worlds: int, domain_elements: int,
                     max_steps: int) -> Optional[Tuple[IntKripkeModel, int]]:
    """Bounded first-order intuitionistic counter-model search (sound; not a decision).

    Enumerates Kripke models up to ``max_worlds`` worlds with increasing domains drawn
    from the formula's constants plus ``domain_elements`` fresh individuals, and
    monotone predicate valuations respecting element existence. A returned model
    genuinely refutes intuitionistic validity; ``None`` means "no counter-model within
    the bounds" — NOT a proof of validity (first-order intuitionistic logic is
    undecidable).
    """
    _reject_second_order(formula)
    consts = sorted({n.name for n in formula.walk() if isinstance(n, Constant)})
    preds: Dict[str, int] = {}
    for node in formula.walk():
        if isinstance(node, Atom):
            preds[node.predicate] = len(node.args)
    steps = 0
    for n in range(1, max_worlds + 1):
        for upset in _partial_orders(n):
            for domains in _increasing_domains(upset, consts, domain_elements):
                pool = sorted(set().union(*domains.values()))
                ground, seen = [], set()
                for name, ar in preds.items():
                    for tup in product(pool, repeat=ar):
                        key = Atom(name, [Constant(t) for t in tup]).to_unicode_str()
                        if key not in seen:
                            seen.add(key)
                            allowed = frozenset(w for w in upset if set(tup) <= domains[w])
                            ground.append((key, _upclosed_subsets(upset, allowed)))
                keys = [k for k, _ in ground]
                option_lists = [opts for _, opts in ground]
                for choice in (product(*option_lists) if ground else [()]):
                    steps += 1
                    if steps > max_steps:
                        return None
                    model = IntKripkeModel(upset, dict(zip(keys, choice)), domains)
                    for w in range(n):
                        if not model.forces(w, formula):
                            return model, w
    return None


def int_countermodel(formula: Node, max_worlds: int = 3,
                     domain_elements: int = 2,
                     max_steps: int = 300000) -> Optional[Tuple[IntKripkeModel, int]]:
    """Return ``(model, world)`` where ``formula`` fails intuitionistically, or None.

    For a **propositional** formula this is a decision procedure: it searches every
    Kripke model up to ``max_worlds`` worlds (intuitionistic propositional logic has
    the finite-model property), so ``None`` proves validity. For a **first-order**
    formula (containing ∀/∃) it is a *bounded* search over increasing-domain Kripke
    models (the formula's constants plus ``domain_elements`` fresh individuals, up to
    ``max_steps`` valuations): a returned model genuinely refutes validity, but
    ``None`` only means "no counter-model within the bounds" — first-order
    intuitionistic logic is undecidable.
    """
    if _is_propositional(formula):
        keys = _atom_keys(formula)
        for n in range(1, max_worlds + 1):
            for upset in _partial_orders(n):
                for valuation in _monotone_valuations(upset, keys):
                    model = IntKripkeModel(upset, valuation)
                    for w in range(n):
                        if not model.forces(w, formula):
                            return model, w
        return None
    return _fo_countermodel(formula, max_worlds, domain_elements, max_steps)


def int_valid(formula: Node, max_worlds: int = 3,
              domain_elements: int = 2, max_steps: int = 300000) -> bool:
    """Return True iff ``formula`` is intuitionistically valid.

    **Split contract** — the two fragments are decided differently, and honestly:

    - **Propositional**: a genuine decision procedure, full stop, REGARDLESS of
      ``max_worlds``. The bounded Kripke search (:func:`int_countermodel`) is tried
      first as a fast path — a countermodel it finds within ``max_worlds`` worlds is a
      real witness, so a quick ``False`` is returned without going further. But
      propositional IPL's finite-model-property bound *grows with the formula* (e.g.
      ``(p→q)∨(q→r)∨(r→p)`` needs 4 worlds — 3, the default, finds nothing), so
      "no countermodel within the bound" is NOT by itself proof of validity. When the
      bounded search comes up empty, the verdict is instead handed to
      :func:`~unicode_fol_kit.atp.lj.int_prove` (Dyckhoff's contraction-free G4ip, a
      terminating decision procedure with no bound to exhaust) for a DEFINITIVE
      True-or-False answer. Net effect: both the ``True`` and the ``False`` verdicts on
      a propositional formula are exact, at every ``max_worlds`` — including the
      default. (Before this delegation, ``int_valid`` of the formula above wrongly
      returned ``True`` at ``max_worlds=3``; see ``tests/test_lj_search.py`` for the
      pinned regression.)
    - **First-order**: unchanged — a sound but *incomplete* check. ``True`` means "no
      counter-model within the bounds" (not a proof, since first-order intuitionistic
      validity is undecidable), while ``False`` is always backed by a real counter-model
      from :func:`int_countermodel`.
    """
    if not _is_propositional(formula):
        return int_countermodel(formula, max_worlds, domain_elements, max_steps) is None
    if int_countermodel(formula, max_worlds, domain_elements, max_steps) is not None:
        return False
    from ..atp.lj import int_prove   # lazy: avoids a semantics<->atp import cycle
    return int_prove([], formula)
