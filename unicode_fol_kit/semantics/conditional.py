"""Counterfactual conditionals — Lewis / Stalnaker sphere semantics.

The material conditional gets counterfactuals wrong: "if kangaroos had no tails they
would topple over" is not made true by kangaroos having tails. **Counterfactuals**
``A □→ B`` ("if A were the case, B would be") are evaluated over a *similarity*
ordering of worlds: from the actual world ``w`` you look at the **closest** worlds
where ``A`` holds and check that ``B`` holds throughout them.

This module uses Lewis's **system of spheres**: each world ``w`` carries a nested
sequence of sets of worlds ``$_w$`` (innermost first, ``w`` in the innermost), read as
"increasingly distant neighbourhoods". The truth condition (finite version)::

    w ⊨ A □→ B   iff   no sphere of w contains an A-world (vacuously true),
                       or, for the smallest sphere S that does, every A-world in S is a B-world.

The "might" counterfactual is the dual ``A ◇→ B ≡ ¬(A □→ ¬B)``. Antecedents and
consequents are ordinary propositional formulas (atoms, ¬ ∧ ∨ → ↔). With a single
innermost sphere ``{closest A-world}`` this is Stalnaker's semantics; with ties it is
Lewis's.

``□→`` and ``◇→`` parse in modal mode (``MSFLParser(modal=True)``) as the
:class:`~unicode_fol_kit.fol.nodes.Would` / :class:`~unicode_fol_kit.fol.nodes.Might`
nodes, so a whole formula can be handed to :func:`cf_satisfies` directly; the
sphere ordering is not an accessibility relation, so these nodes have no
first-order export and the Kripke evaluator rejects them.

CENTERING — which sphere systems count
--------------------------------------
"Nested" alone does not pin down a logic. Lewis names three systems, and
:data:`CENTERING_LEVELS` is exactly that list:

``"none"`` (Lewis's **V**)
    Nesting and nothing else. A world's spheres need not contain the world, and a
    world may have no sphere at all.
``"weak"`` (Lewis's **VW**) — the DEFAULT
    Some sphere of ``w`` contains ``w``, and every non-empty sphere of ``w``
    contains ``w``.
``"strong"`` (Lewis's **VC**)
    ``{w}`` is itself a sphere of ``w`` — with nesting, the innermost non-empty one.

``"weak"`` is the default because it is what makes ``□→`` behave like a
*conditional*. Under ``"none"`` a sphere system that does not contain the
evaluation world makes ``A □→ B`` vacuously true even where ``A`` actually holds,
so **modus ponens fails**: ``(P ∧ (P □→ Q)) → Q`` and ``(P □→ Q) → (P → Q)`` are
both refutable in V, by the one-world model whose sphere system is empty. V is a
real logic and is kept reachable (``centering="none"``), but it is not what a
reader who writes ``P ∧ (P □→ Q)`` means by "counterfactual".

The three classes are strictly nested — ``strong ⊆ weak ⊆ none`` as sets of
models — so validity propagates ``none ⇒ weak ⇒ strong`` and refutation
propagates the other way. Strong centering ``(P ∧ Q) → (P □→ Q)`` separates VC
from VW; modus ponens and weak centering separate VW from V; antecedent
strengthening, contraposition and transitivity stay invalid in all three, which
is the whole point of the connective.

Centering is a property of a *class of models*, not of a single model: it is an
argument of :func:`cf_valid` / :func:`cf_countermodel` (which quantify over a
class), never of :func:`cf_satisfies` / :func:`would` / :func:`might` (which
evaluate in one given model).

HOW MANY WORLDS — and why the default is not one number
-------------------------------------------------------
The search is bounded, so a ``True`` verdict is only ever "no countermodel with at
most ``max_worlds`` worlds". Two worlds is **systematically too few for the
centered levels**, and that is a structural fact about the classes rather than bad
luck with a few schemas:

* At ``"strong"`` (VC) the innermost sphere is pinned to ``{w}``, so refuting a
  disjunction of two counterfactuals needs ``w`` to falsify the antecedent *plus*
  two antecedent-worlds that disagree — three worlds minimum. Conditional excluded
  middle ``(A □→ B) ∨ (A □→ ¬B)``, Stalnaker's principle and one of the schemas
  VC is supposed to leave open, is reported VALID at ``|W| ≤ 2`` and refuted at
  ``|W| ≤ 3``.
* At ``"weak"`` (VW) the plain schemas are already settled at two worlds, but a
  NESTED counterfactual is not: importation
  ``(A □→ (B □→ C)) → ((A ∧ B) □→ C)`` is reported VALID at ``|W| ≤ 2`` and
  refuted at ``|W| ≤ 3``.

:data:`DEFAULT_MAX_WORLDS` therefore sets the default per level — 3 for ``"weak"``
and ``"strong"``, 2 for ``"none"``, whose enumeration is an order of magnitude
larger per world (see the chain-count table in :func:`_sphere_chains`; measured, a
three-atom schema is seconds at VW and minutes at V). One consequence is worth
stating rather than discovering: because the levels are searched to different
depths by default, the class inclusion ``strong ⊆ weak ⊆ none`` need not show up
in the *default* verdicts — a schema first refuted at three worlds can read
"invalid at weak, valid at none". Pass the same explicit ``max_worlds`` to every
call whenever you are comparing levels.

Public API: :class:`CounterfactualModel`, :func:`cf_satisfies`, :func:`would`,
:func:`might`, :func:`cf_countermodel`, :func:`cf_valid`, :data:`CENTERING_LEVELS`,
:data:`DEFAULT_MAX_WORLDS`.
"""

from dataclasses import dataclass
from itertools import product
from typing import Any, Dict, FrozenSet, Iterable, Iterator, List, Optional, Tuple

from ..fol.nodes import Node, Atom, Not, And, Or, Xor, Implies, Iff, Would, Might


#: The three Lewis sphere systems :func:`cf_valid` / :func:`cf_countermodel` can
#: quantify over — ``"none"`` = V, ``"weak"`` = VW, ``"strong"`` = VC. See the
#: module docstring for what each one is and why ``"weak"`` is the default.
CENTERING_LEVELS: Tuple[str, ...] = ("none", "weak", "strong")

#: The ``max_worlds`` bound :func:`cf_valid` / :func:`cf_countermodel` use when the
#: caller does not give one, keyed by centering level. Three for the centered levels
#: because two is *structurally* too few there (module docstring: conditional excluded
#: middle at VC, importation at VW, both spuriously VALID at ``|W| ≤ 2``); two for
#: ``"none"``, whose per-world chain count is 26 against VW's 11 and VC's 6, so the same
#: schema costs minutes instead of seconds. Deciding a level at another bound is one
#: positional argument away — and is what to do when comparing levels against each other.
DEFAULT_MAX_WORLDS: Dict[str, int] = {"none": 2, "weak": 3, "strong": 3}


def check_centering(level: str) -> str:
    """Validate a centering level name and return it unchanged.

    The single source of truth for the level names:
    :mod:`unicode_fol_kit.hol.isabelle_conditional` imports this rather than
    keeping its own tuple, so the Python enumeration and the Isabelle premise
    cannot drift on what a level is called (or on which levels exist).

    Raises:
        ValueError: naming all three legal levels, on anything else.
    """
    if level not in CENTERING_LEVELS:
        raise ValueError(
            f"centering must be one of {CENTERING_LEVELS} "
            f"(Lewis V / VW / VC), got {level!r}.")
    return level


def _reject_free_variable_atom(atom: Atom) -> None:
    """Reject an atom with a free Variable argument: the sphere semantics is
    propositional/ground. Keying such an atom by its surface string would treat
    ``P(x)`` as one opaque proposition and silently return a verdict for an
    out-of-contract formula — the sibling ``to_isabelle_conditional`` already
    rejects the identical input, and the two must agree."""
    from ..fol.nodes import Variable
    for arg in atom.args:
        for sub in arg.walk():
            if isinstance(sub, Variable):
                raise TypeError(
                    f"conditional: atom {atom.to_unicode_str()!r} has a free "
                    "variable — the Lewis sphere semantics here is "
                    "propositional/ground. Use ground atoms (constants are "
                    "fine), matching hol.isabelle_conditional.")


@dataclass(frozen=True)
class CounterfactualModel:
    """A Lewis sphere model over a set of worlds.

    ``valuation`` maps each world to the set of atom keys (``atom.to_unicode_str()``)
    true there. ``spheres`` maps each world ``w`` to its nested system of spheres — a
    list of frozensets ordered **innermost (closest) first**, each a superset of the
    previous. A world omitted from ``spheres`` is taken to have the single sphere
    ``{w}``.

    NO CENTERING IS IMPOSED HERE. The dataclass deliberately does not require ``w``
    to belong to any of its own spheres, and accepts the empty system ``[]``,
    because it has to be able to represent all three Lewis classes (see
    :data:`CENTERING_LEVELS`) — a centered-by-construction dataclass would make
    ``centering="none"`` models unconstructible and so unreachable for
    :func:`cf_countermodel`. Centering is therefore a property of the model *class*
    that :func:`cf_valid` / :func:`cf_countermodel` quantify over, selected by their
    ``centering=`` argument.

    The trap that follows is worth naming: a hand-built model may perfectly well
    falsify ``(P ∧ (P □→ Q)) → Q`` under :func:`cf_satisfies` while
    ``cf_valid`` reports that formula valid. Those are not in conflict — one is
    model-relative, the other class-relative, and the hand-built model simply is
    not weakly centered. :func:`_centering_ok` is the predicate that decides which
    class a given sphere system belongs to.

    Note that :meth:`sphere_system`'s fallback ``[{world}]`` for an omitted world is
    a **strongly centered** default (it satisfies VC, hence VW too), which is what
    makes a partially specified ``spheres`` dict behave the way a reader expects.
    """

    worlds: Tuple[Any, ...]
    valuation: Dict[Any, FrozenSet[str]]
    spheres: Dict[Any, List[FrozenSet[Any]]]

    def sphere_system(self, world: Any) -> List[FrozenSet[Any]]:
        """The nested spheres around ``world`` (default ``[{world}]``)."""
        return self.spheres.get(world, [frozenset({world})])


def cf_satisfies(formula: Node, model: CounterfactualModel, world: Any) -> bool:
    """Return whether ``world`` satisfies ``formula`` in the sphere ``model``.

    Handles the propositional connectives plus the counterfactual conditionals
    :class:`~unicode_fol_kit.fol.nodes.Would` (``□→``) and
    :class:`~unicode_fol_kit.fol.nodes.Might` (``◇→``), so a parsed formula can be
    evaluated directly and counterfactuals may NEST — a conditional in an antecedent
    or consequent is evaluated at the world under consideration, with that world's own
    spheres, which is what Lewis's semantics prescribes.

    Raises:
        TypeError: on any other node (quantifiers, modal operators, …), and on an
            atom with a FREE VARIABLE argument (``P(x)``) — the sphere semantics is
            propositional/ground here; a Kripke accessibility relation is a
            different structure, so mixing ``□`` with ``□→`` is rejected rather than
            silently reinterpreted, and a first-order atom is rejected rather than
            silently read as one opaque proposition (matching
            ``hol.isabelle_conditional``).
    """
    if isinstance(formula, Atom):
        _reject_free_variable_atom(formula)
        return formula.to_unicode_str() in model.valuation.get(world, frozenset())
    if isinstance(formula, Not):
        return not cf_satisfies(formula.formula, model, world)
    if isinstance(formula, And):
        return (cf_satisfies(formula.left, model, world)
                and cf_satisfies(formula.right, model, world))
    if isinstance(formula, Or):
        return (cf_satisfies(formula.left, model, world)
                or cf_satisfies(formula.right, model, world))
    if isinstance(formula, Xor):
        return (cf_satisfies(formula.left, model, world)
                != cf_satisfies(formula.right, model, world))
    if isinstance(formula, Implies):
        return ((not cf_satisfies(formula.left, model, world))
                or cf_satisfies(formula.right, model, world))
    if isinstance(formula, Iff):
        return (cf_satisfies(formula.left, model, world)
                == cf_satisfies(formula.right, model, world))
    if isinstance(formula, Would):
        return _would_holds(model, world, formula.left, formula.right)
    if isinstance(formula, Might):
        # The dual ¬(A □→ ¬B). Note this makes ◇→ vacuously FALSE exactly where
        # □→ is vacuously true (no antecedent-world in any sphere).
        return not _would_holds(model, world, formula.left, Not(formula.right))
    raise TypeError(
        f"conditional: formula must be propositional or a counterfactual, got "
        f"{type(formula).__name__}.")


def _would_holds(model: CounterfactualModel, world: Any,
                 antecedent: Node, consequent: Node) -> bool:
    """The Lewis sphere condition for ``antecedent □→ consequent`` at ``world``."""
    for sphere in model.sphere_system(world):
        a_worlds = [w for w in sphere if cf_satisfies(antecedent, model, w)]
        if a_worlds:
            return all(cf_satisfies(consequent, model, w) for w in a_worlds)
    return True                                  # no antecedent-world anywhere → vacuous


def would(model: CounterfactualModel, world: Any,
          antecedent: Node, consequent: Node) -> bool:
    """Return whether ``world ⊨ antecedent □→ consequent`` (Lewis "would" counterfactual).

    Vacuously true if no sphere of ``world`` holds an antecedent-world; otherwise the
    consequent must hold at every antecedent-world of the smallest antecedent-permitting
    sphere. Equivalent to ``cf_satisfies(Would(antecedent, consequent), model, world)``.

    The vacuous case can arise **even when the antecedent holds at ``world``
    itself**, if ``model`` is not (weakly) centered — ``world`` may belong to none
    of its own spheres, or have no sphere at all. That is not a bug in the clause
    but the defining behaviour of Lewis's bare system V, and it is exactly what a
    ``centering="none"`` countermodel from :func:`cf_countermodel` exhibits; the
    ``centering="weak"`` default of :func:`cf_valid` excludes it.
    """
    return _would_holds(model, world, antecedent, consequent)


def might(model: CounterfactualModel, world: Any,
          antecedent: Node, consequent: Node) -> bool:
    """Return whether ``world ⊨ antecedent ◇→ consequent`` — the dual ``¬(A □→ ¬B)``."""
    return not _would_holds(model, world, antecedent, Not(consequent))


# --------------------------------------------------------------------------- #
# Bounded countermodel search / validity over Lewis sphere models.
# --------------------------------------------------------------------------- #

def _atom_keys(formula: Node) -> Tuple[str, ...]:
    """The distinct atom keys (``atom.to_unicode_str()``) of ``formula``, sorted.

    Rejects free-variable atoms upfront (same contract as :func:`cf_satisfies`),
    so ``cf_countermodel`` / ``cf_valid`` fail fast instead of mid-enumeration.
    """
    keys = set()
    for n in formula.walk():
        if isinstance(n, Atom):
            _reject_free_variable_atom(n)
            keys.add(n.to_unicode_str())
    return tuple(sorted(keys))


def _centering_ok(spheres: Iterable[FrozenSet[Any]], world: Any,
                  centering: str) -> bool:
    """Whether ``spheres`` is an admissible sphere system for ``world`` at ``centering``.

    Written independently of :func:`_sphere_chains`, so the generator can be
    cross-checked against it (see ``tests/test_counterfactual_centering.py``) in both
    directions instead of being trusted twice over.

    It denotes the same class as the Isabelle predicates ``weakly_centered`` /
    ``strongly_centered``, but it is not a literal transcription of them, and the
    difference is worth naming for anyone auditing the two side by side: HOL's
    ``strongly_centered`` asserts only that ``{x}`` is a sphere, whereas ``"strong"``
    below re-imposes the two weak clauses on top. On a NESTED family the two agree
    (``{world}`` being a member forces every non-empty member to contain ``world``),
    and ``isabelle_conditional`` always emits ``nested Sel`` as a co-premise, so the
    denoted classes are identical; off nested families they differ — smallest witness
    ``{{0}, {1}}`` at ``world=0``, which HOL's predicate accepts and this one rejects.

    * ``"none"``: no condition — nesting is the caller's business.
    * ``"weak"``: some sphere contains ``world``, AND every *non-empty* sphere
      contains ``world``. The non-emptiness guard is not slack: Lewis's ``$_w`` is
      closed under unions and so contains ``∅``, and ``∅`` is truth-value inert
      anyway (see :func:`_sphere_chains`).
    * ``"strong"``: weakly centered and ``{world}`` is itself a sphere. Under
      nesting that makes it the ⊆-least non-empty sphere, which is the usual
      phrasing of VC.
    """
    check_centering(centering)
    if centering == "none":
        return True
    if not any(world in s for s in spheres):
        return False
    if any(s and world not in s for s in spheres):
        return False
    if centering == "strong":
        return any(set(s) == {world} for s in spheres)
    return True


def _sphere_chains(world: int, worlds: Tuple[int, ...],
                   centering: str = "weak") -> Iterator[List[FrozenSet[int]]]:
    """Yield every admissible nested sphere system around ``world`` over ``worlds``.

    A system is a strictly increasing chain ``S₁ ⊂ S₂ ⊂ … ⊂ Sₖ`` of frozensets,
    innermost first. What ``centering`` selects (see :data:`CENTERING_LEVELS`):

    * ``"none"`` (V): members are arbitrary non-empty subsets — they need not
      contain ``world`` — and the EMPTY chain ``[]`` is emitted too (no sphere at
      all, so every ``□→`` is vacuously true at ``world``). That chain is the sole
      difference between V and VW at one world, and it is the one that refutes
      modus ponens.
    * ``"weak"`` (VW, default): every member contains ``world``, and the chain is
      non-empty. Both weak-centering clauses follow immediately.
    * ``"strong"`` (VC): as ``"weak"``, plus the innermost member is pinned to
      ``{world}``.

    ``∅`` is never a *member* of an emitted chain at any level. That loses no
    generality, because ``∅`` is truth-value inert: :func:`_would_holds` can never
    select it (it holds no antecedent-world) and it satisfies the vacuous clause
    outright, so adding or deleting it changes no ``□→`` anywhere. This is the same
    "strictness loses no generality" argument that justifies excluding repeated
    spheres, and it is what lets the Isabelle premises in
    :mod:`unicode_fol_kit.hol.isabelle_conditional` — which are ``∅``-tolerant, as
    Lewis is — denote exactly the class enumerated here.

    Chains per world, measured — this is the enumeration cost (``c(n)ⁿ`` chain
    assignments per valuation), and it is the whole reason
    :data:`DEFAULT_MAX_WORLDS` is 3 at the centered levels and 2 at ``"none"``::

        |W|:        1     2     3
        none        2     6    26
        weak        1     3    11
        strong      1     2     6
    """
    check_centering(centering)
    others = [w for w in worlds if w != world]
    pool: List[FrozenSet[int]] = []
    for k in range(len(others) + 1):
        for bits in product((False, True), repeat=len(others)):
            if sum(bits) != k:
                continue
            rest = {o for o, b in zip(others, bits) if b}
            if centering == "none":
                # V does not require `world` in its own spheres, so the pool is
                # every non-empty subset of `worlds`, with and without `world`.
                if rest:
                    pool.append(frozenset(rest))
                pool.append(frozenset({world} | rest))
            else:
                pool.append(frozenset({world} | rest))
    pool.sort(key=len)
    # pool is now ordered by size, so chains can be built left-to-right; for the
    # centered levels pool[0] is the unique smallest member, {world}.

    def extend(chain: List[FrozenSet[int]], start: int):
        if chain:                                   # [] is emitted only for "none"
            yield list(chain)
        for i in range(start, len(pool)):
            if not chain or chain[-1] < pool[i]:    # strict superset
                yield from extend(chain + [pool[i]], i + 1)

    if centering == "strong":
        yield from extend([frozenset({world})], 1)
    else:
        if centering == "none":
            yield []                                # only V admits the empty system
        yield from extend([], 0)


def cf_countermodel(formula: Node, max_worlds: Optional[int] = None, *,
                    centering: str = "weak"
                    ) -> Optional[Tuple[CounterfactualModel, Any]]:
    """Return ``(model, world)`` where ``formula`` fails, or None.

    EXHAUSTIVE search over every Lewis sphere model with ``|W| ≤ max_worlds`` that
    satisfies ``centering``: every valuation of the formula's atoms and every
    admissible nested sphere system around every world. The failure check *is*
    :func:`cf_satisfies`, so a non-None result definitively refutes validity **over
    that class** — the countermodel is verified by construction.

    Args:
        formula: the AST node to refute (propositional connectives plus ``□→``/``◇→``).
        max_worlds: the world-count bound; every ``|W|`` from 1 up to it is tried.
            ``None`` (the default) means :data:`DEFAULT_MAX_WORLDS` for the chosen
            level — 3 at ``"weak"`` / ``"strong"``, 2 at ``"none"``.
        centering: which class to search — ``"none"`` (V), ``"weak"`` (VW, the
            default) or ``"strong"`` (VC). Keyword-only, so existing positional
            ``cf_countermodel(f, 3)`` calls keep working. See
            :data:`CENTERING_LEVELS`.

    Raises:
        ValueError: on an unknown ``centering`` level.
        TypeError: on a free-variable atom (via :func:`_atom_keys`).

    The space is exponential: ``2^(n·a)`` valuations times ``c(n)ⁿ`` sphere
    assignments for ``n`` worlds and ``a`` atoms, where ``c(n)`` is the per-world
    chain count tabulated in :func:`_sphere_chains`. The level matters a lot to the
    cost, which is why the default bound is level-dependent: measured on the
    toolkit's ten-schema Lewis battery at ``max_worlds=3``, ``"strong"`` takes 9 s
    and ``"weak"`` 55 s in total (worst single schema 27 s, three atoms), whereas
    ``"none"`` is ``26³`` chain assignments per valuation instead of ``11³`` and the
    same three-atom schema runs for minutes. ``centering="none"`` together with
    ``max_worlds ≥ 3`` is therefore a deliberate choice, not a default.
    """
    check_centering(centering)
    if max_worlds is None:
        max_worlds = DEFAULT_MAX_WORLDS[centering]
    atoms = _atom_keys(formula)
    for n in range(1, max_worlds + 1):
        worlds = tuple(range(n))
        chain_options = [list(_sphere_chains(w, worlds, centering)) for w in worlds]
        for bits in product((False, True), repeat=n * max(1, len(atoms))):
            valuation = {
                w: frozenset(a for j, a in enumerate(atoms)
                             if bits[w * len(atoms) + j])
                for w in worlds
            } if atoms else {w: frozenset() for w in worlds}
            for chains in product(*chain_options):
                model = CounterfactualModel(
                    worlds, valuation,
                    {w: chains[w] for w in worlds})
                for w in worlds:
                    if not cf_satisfies(formula, model, w):
                        return (model, w)
    return None


def cf_valid(formula: Node, max_worlds: Optional[int] = None, *,
             centering: str = "weak") -> bool:
    """Return True iff no sphere countermodel to ``formula`` is found within the bound.

    HONEST CONTRACT (mirroring :func:`~unicode_fol_kit.semantics.relevant.rel_valid`):
    ``False`` is *definitive* — it is backed by an explicit,
    :func:`cf_satisfies`-verified countermodel from :func:`cf_countermodel`, so
    the formula is certainly not valid over Lewis sphere models. ``True`` means
    only "no countermodel with at most ``max_worlds`` worlds"; a non-theorem
    whose smallest refuting model needs more worlds is (spuriously) reported
    valid — for a certified positive verdict use
    :func:`~unicode_fol_kit.hol.isabelle_runner.isabelle_decide_counterfactual`,
    whose proof battery is a real validity proof over ALL nested sphere systems
    of the requested level. Raising ``max_worlds`` never turns a ``False`` into a
    ``True``.

    THE BOUND IS NOT ONE NUMBER, and the reason is structural rather than
    performance tuning: at VC two worlds cannot host a countermodel to a
    disjunction of two counterfactuals at all (``{w}`` is pinned as the innermost
    sphere), and at VW two worlds cannot host one to a NESTED counterfactual. The
    default is :data:`DEFAULT_MAX_WORLDS` for the level — 3 for ``"weak"`` and
    ``"strong"``, 2 for ``"none"`` — so ``(A □→ B) ∨ (A □→ ¬B)`` at ``"strong"``
    and ``(A □→ (B □→ C)) → ((A ∧ B) □→ C)`` at ``"weak"`` come back ``False``,
    as they should, instead of the spurious ``True`` a two-world bound reports.
    The flip side, stated so it is not discovered: default verdicts at DIFFERENT
    levels are not directly comparable, since they are searched to different
    depths. Pass an explicit ``max_worlds`` when comparing levels.

    EVERY VERDICT IS RELATIVE TO ``centering``, and the relation between levels is
    DIRECTIONAL. Because ``strong ⊆ weak ⊆ none`` as classes of models, a
    countermodel found at ``"strong"`` is automatically a countermodel at ``"weak"``
    and ``"none"``, and validity found at ``"none"`` automatically holds at
    ``"weak"`` and ``"strong"``. Neither implication runs backwards:
    ``cf_valid(φ, centering="none") is False`` does **not** refute ``φ`` over VW —
    the witness may be a model VW excludes, which is precisely what happens to
    modus ponens ``(P ∧ (P □→ Q)) → Q``. Compare like with like: the
    certified-positive counterpart is
    :func:`~unicode_fol_kit.hol.isabelle_runner.isabelle_decide_counterfactual`,
    and it answers *at the level of the theory it emits* — which is
    :func:`~unicode_fol_kit.hol.isabelle_conditional.isabelle_conditional_theory`'s
    default, ``"weak"``, the same default as here.

    Args:
        formula: the AST node to decide.
        max_worlds: the world-count bound handed to :func:`cf_countermodel`;
            ``None`` (the default) means :data:`DEFAULT_MAX_WORLDS` for the level.
        centering: ``"none"`` (V) / ``"weak"`` (VW, default) / ``"strong"`` (VC);
            keyword-only, so ``cf_valid(f, 3)`` keeps working. The default matches
            :func:`~unicode_fol_kit.hol.isabelle_runner.isabelle_decide_counterfactual`'s,
            so the two routes decide the same question unless told otherwise — and
            at the centered levels the default *bounds* now match too, three worlds
            here against that route's ``card="1-3"``.

    Raises:
        ValueError: on an unknown ``centering`` level.
    """
    return cf_countermodel(formula, max_worlds, centering=centering) is None
