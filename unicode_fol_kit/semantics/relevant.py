"""Relevant logic — the basic affixing system **B**, via simplified Routley–Meyer semantics.

Relevance logics reject the classical "paradoxes of material implication": in **B**
an implication ``A → B`` is a genuine entailment claim, so ``P → (Q → P)`` (an
irrelevant antecedent) and ``(P ∧ ¬P) → Q`` (ex falso quodlibet) are *not* theorems.
The semantics implemented here is the Priest–Sylvan **simplified** Routley–Meyer
semantics (Priest & Sylvan 1992, "Simplified semantics for basic relevant logics",
*J. Philosophical Logic*; Priest, *Introduction to Non-Classical Logic*, 2nd ed.,
ch. 10), which is sound and complete for B.

An interpretation is ``⟨W, N, *, R, V⟩``:

- ``W`` — a set of worlds, with ``N ⊆ W`` a **nonempty** set of *normal* worlds;
- ``*`` — the Routley star, an involution on worlds (``w** = w``), interpreting ``¬``;
- ``R`` — a ternary relation sourced only at NON-normal worlds
  (``R ⊆ (W∖N) × W × W``), interpreting ``→`` at non-normal worlds;
- ``V`` — a valuation mapping each propositional atom to the set of worlds where
  it holds.

Truth at a world ``w``:

- ``w ⊨ p``             iff ``w ∈ V(p)``
- ``w ⊨ A ∧ B``         iff ``w ⊨ A`` and ``w ⊨ B``
- ``w ⊨ A ∨ B``         iff ``w ⊨ A`` or ``w ⊨ B``
- ``w ⊨ ¬A``            iff ``w* ⊭ A``                          (Routley star)
- ``w ⊨ A → B``, w ∈ N  iff for ALL ``x ∈ W``: ``x ⊨ A`` ⇒ ``x ⊨ B``
- ``w ⊨ A → B``, w ∉ N  iff for all ``x, y`` with ``R(w, x, y)``: ``x ⊨ A`` ⇒ ``y ⊨ B``

``A ↔ B`` abbreviates ``(A → B) ∧ (B → A)``. A formula is **valid** iff it is true
at every normal world of every interpretation. Formulas are the classical
propositional nodes of the default ``MSFLParser()`` — ``And``, ``Or``, ``Not``,
``Implies``, ``Iff`` over nullary ``Atom``s — reused with relevant semantics,
exactly as :mod:`.intuitionistic` reuses classical syntax over Kripke models.

Public API: :class:`RelevantModel`, :func:`rel_satisfies`,
:func:`rel_countermodel`, :func:`rel_valid`.
"""

from collections.abc import Mapping as MappingABC
from dataclasses import dataclass, field
from itertools import chain, combinations, permutations, product
from typing import Dict, FrozenSet, Iterator, List, Mapping, Optional, Tuple

from ..fol.nodes import Node, Atom, Not, And, Or, Implies, Iff


class _FrozenMap(MappingABC):
    """An immutable, hashable mapping: dict-like lookup over a frozen tuple of pairs."""

    __slots__ = ("_dict", "_pairs")

    def __init__(self, mapping):
        items = mapping.items() if isinstance(mapping, MappingABC) else mapping
        self._dict: Dict = dict(items)
        # Sorted by key so equal mappings hash equally regardless of insertion order.
        self._pairs: Tuple = tuple(sorted(self._dict.items(), key=lambda kv: kv[0]))

    def __getitem__(self, key):
        return self._dict[key]

    def __iter__(self) -> Iterator:
        return iter(self._dict)

    def __len__(self) -> int:
        return len(self._dict)

    def __hash__(self) -> int:
        return hash(self._pairs)

    def __repr__(self) -> str:
        return repr(self._dict)


@dataclass(frozen=True)
class RelevantModel:
    """A simplified Routley–Meyer interpretation ``⟨W, N, *, R, V⟩`` for the logic B.

    Plain containers are welcome — everything is copied and frozen in
    ``__post_init__`` (the constructor ergonomics of
    :class:`~unicode_fol_kit.semantics.kripke.KripkeModel`),
    and the frozen model is hashable.

    Args:
        worlds: the worlds ``W`` (an iterable of names; order kept, duplicates
            collapse).
        normal: the **nonempty** set ``N ⊆ W`` of normal worlds.
        star: the Routley star, a mapping ``w → w*`` that must be total on ``W``
            and involutive (``w** = w``). ``None`` (the default) means the
            identity. Stored hashable (a frozen mapping) with dict-like lookup:
            ``model.star["w0"]``.
        R: the ternary relation — a set of triples ``(w, x, y)`` whose source
            ``w`` must be NON-normal (``R ⊆ (W∖N) × W × W``). Consulted only when
            evaluating ``→`` at a non-normal world. Defaults to empty.
        valuation: maps an atom key (its rendered form, e.g. ``"P"``) to the set
            of worlds where the atom holds. A missing key is false everywhere.
            Dict-like lookup: ``model.valuation.get("P", frozenset())``.

    Raises ValueError from ``__post_init__`` if ``normal`` is empty or not a
    subset of ``worlds``, if ``star`` is not a total involution on ``worlds``,
    if some ``R``-triple is sourced at a normal world or mentions an unknown
    world, or if the valuation mentions an unknown world.
    """

    worlds: Tuple[str, ...]
    normal: FrozenSet[str]
    star: Optional[Mapping[str, str]] = None
    R: FrozenSet[Tuple[str, str, str]] = frozenset()
    valuation: Mapping[str, FrozenSet[str]] = field(default_factory=dict)

    def __post_init__(self):
        worlds = tuple(dict.fromkeys(self.worlds))  # dedupe, keep order
        wset = frozenset(worlds)
        normal = frozenset(self.normal)
        star = (_FrozenMap({w: w for w in worlds}) if self.star is None
                else _FrozenMap(self.star))
        relation = frozenset(tuple(t) for t in self.R)
        val_in = self.valuation
        val_items = val_in.items() if isinstance(val_in, MappingABC) else val_in
        valuation = _FrozenMap({key: frozenset(ws) for key, ws in val_items})

        if not normal:
            raise ValueError("RelevantModel: the set N of normal worlds must be nonempty.")
        if not normal <= wset:
            raise ValueError(
                f"RelevantModel: normal worlds {sorted(normal - wset)} are not in worlds.")
        if frozenset(star) != wset or not frozenset(star.values()) <= wset:
            raise ValueError(
                "RelevantModel: star must be a total map W → W; got domain "
                f"{sorted(star)} with values {sorted(set(star.values()))} over "
                f"worlds {sorted(wset)}.")
        for w in worlds:
            if star[star[w]] != w:
                raise ValueError(
                    f"RelevantModel: star is not an involution (w** = w fails): "
                    f"{w!r}* = {star[w]!r} but {star[w]!r}* = {star[star[w]]!r}.")
        for triple in relation:
            if len(triple) != 3:
                raise ValueError(f"RelevantModel: R entries must be triples; got {triple!r}.")
            a, b, c = triple
            if a not in wset or b not in wset or c not in wset:
                raise ValueError(f"RelevantModel: R{triple!r} mentions a world not in W.")
            if a in normal:
                raise ValueError(
                    "RelevantModel: R must be sourced at NON-normal worlds only "
                    f"(R ⊆ (W∖N) × W × W); R{triple!r} starts at the normal world {a!r}.")
        for key, ws in valuation.items():
            if not ws <= wset:
                raise ValueError(
                    f"RelevantModel: valuation for {key!r} mentions worlds "
                    f"{sorted(set(ws) - wset)} not in W.")

        object.__setattr__(self, "worlds", worlds)
        object.__setattr__(self, "normal", normal)
        object.__setattr__(self, "star", star)
        object.__setattr__(self, "R", relation)
        object.__setattr__(self, "valuation", valuation)


def _reject_non_propositional(formula: Node) -> None:
    """Raise TypeError unless ``formula`` is ∧ ∨ ¬ → ↔ over nullary atoms.

    The B semantics interprets exactly the classical propositional connectives;
    quantifiers, modalities, lambda terms, Xor and non-nullary atoms are rejected
    (there is no agreed relevant reading for them here).
    """
    if not isinstance(formula, Node):
        raise TypeError(
            f"relevant: expected a formula Node, got {type(formula).__name__}.")
    for node in formula.walk():
        if isinstance(node, Atom):
            if node.args:
                raise TypeError(
                    "relevant: only nullary propositional atoms are supported; "
                    f"got the atom {node.to_unicode_str()!r} with arguments.")
        elif not isinstance(node, (Not, And, Or, Implies, Iff)):
            raise TypeError(
                f"relevant: unsupported node {type(node).__name__} in "
                f"{formula.to_unicode_str()!r}; the B semantics interprets only "
                "the propositional connectives ∧ ∨ ¬ → ↔ over nullary atoms "
                "(no quantifiers, modalities, or lambda terms).")


def _sat(model: RelevantModel, world: str, formula: Node) -> bool:
    """The simplified Routley–Meyer truth clauses (input already validated)."""
    if isinstance(formula, Atom):
        return world in model.valuation.get(formula.to_unicode_str(), frozenset())
    if isinstance(formula, And):
        return _sat(model, world, formula.left) and _sat(model, world, formula.right)
    if isinstance(formula, Or):
        return _sat(model, world, formula.left) or _sat(model, world, formula.right)
    if isinstance(formula, Not):
        # w ⊨ ¬A  iff  w* ⊭ A   (Routley star).
        return not _sat(model, model.star[world], formula.formula)
    if isinstance(formula, Iff):
        # A ↔ B is defined as (A → B) ∧ (B → A), with the relevant →.
        return (_sat(model, world, Implies(formula.left, formula.right))
                and _sat(model, world, Implies(formula.right, formula.left)))
    if isinstance(formula, Implies):
        if world in model.normal:
            # Normal world: w ⊨ A → B iff EVERY world satisfying A satisfies B.
            return all(_sat(model, x, formula.right)
                       for x in model.worlds if _sat(model, x, formula.left))
        # Non-normal world: quantify over the R-successor pairs of w.
        return all(_sat(model, y, formula.right)
                   for (a, x, y) in model.R
                   if a == world and _sat(model, x, formula.left))
    raise TypeError(  # unreachable after _reject_non_propositional
        f"relevant: unsupported node {type(formula).__name__}.")


def rel_satisfies(model: RelevantModel, world: str, formula: Node) -> bool:
    """Return whether ``formula`` is true at ``world`` in ``model``.

    Implements the simplified Routley–Meyer clauses: atoms via the valuation,
    ``∧``/``∨`` pointwise, ``¬A`` true at ``w`` iff ``A`` is false at ``w*``,
    ``A → B`` at a *normal* world iff every world satisfying ``A`` satisfies
    ``B``, and at a *non-normal* world iff ``x ⊨ A ⇒ y ⊨ B`` for every triple
    ``R(w, x, y)``. ``A ↔ B`` unfolds to ``(A → B) ∧ (B → A)``.

    Raises TypeError for non-propositional input (quantifiers, modalities,
    lambdas, non-nullary atoms) and ValueError for an unknown world.
    """
    _reject_non_propositional(formula)
    if world not in model.worlds:
        raise ValueError(
            f"rel_satisfies: unknown world {world!r}; the model's worlds are "
            f"{model.worlds}.")
    return _sat(model, world, formula)


def _atom_keys(formula: Node) -> List[str]:
    """Distinct atom surface-forms in ``formula``, in first-seen order."""
    keys: List[str] = []
    seen = set()
    for node in formula.walk():
        if isinstance(node, Atom):
            key = node.to_unicode_str()
            if key not in seen:
                seen.add(key)
                keys.append(key)
    return keys


def _powerset(items) -> Iterator[tuple]:
    """Every subset of ``items`` as a tuple, smallest first."""
    seq = list(items)
    return chain.from_iterable(combinations(seq, r) for r in range(len(seq) + 1))


def _involutions(worlds: Tuple[str, ...]) -> Iterator[Dict[str, str]]:
    """Every involutive permutation of ``worlds`` (each ``w** = w``) as a dict."""
    for perm in permutations(worlds):
        mapping = dict(zip(worlds, perm))
        if all(mapping[mapping[w]] == w for w in worlds):
            yield mapping


def rel_countermodel(formula: Node,
                     max_worlds: int = 2) -> Optional[Tuple[RelevantModel, str]]:
    """Return ``(model, world)`` where ``formula`` fails at a normal world, or None.

    EXHAUSTIVE search over every simplified Routley–Meyer interpretation with
    ``|W| ≤ max_worlds`` worlds and exactly ONE normal world ``"w0"``: every
    involution for ``*``, every ``R ⊆ (W∖N) × W × W``, and every valuation of the
    formula's atoms. The returned countermodel is verified with
    :func:`rel_satisfies` before it is returned (the search's failure check *is*
    that call), so a non-None result definitively refutes validity in B.

    One normal world is WLOG for countermodel *existence*: if ``φ`` fails at a
    normal world ``w0`` of any interpretation, demote every other normal world
    ``w`` to non-normal and add the triples ``R(w, x, x)`` for all ``x`` — the
    demoted →-clause with those triples coincides with the normal-world clause,
    the other clauses never mention ``N``, so every truth value is preserved and
    ``w0`` (relabelled first) still refutes ``φ``. The search enumerates ALL
    ``R``, so it covers that transformed interpretation.

    The space is EXPONENTIAL: about ``inv(n) · 2^((n-1)·n²) · 2^(n·a)``
    interpretations for ``n`` worlds and ``a`` atoms. ``max_worlds=2`` with ≤ 3
    atoms is ~2·16·64 ≈ 2000 models (well under a second); ``max_worlds=3`` with
    3 atoms is already ≈ 5·10⁸ — keep the bound tiny.
    """
    _reject_non_propositional(formula)
    atoms = _atom_keys(formula)
    for n in range(1, max_worlds + 1):
        worlds = tuple(f"w{i}" for i in range(n))
        w0 = worlds[0]
        normal = frozenset({w0})
        non_normal = worlds[1:]
        triples = [(w, x, y) for w in non_normal for x in worlds for y in worlds]
        world_subsets = [frozenset(s) for s in _powerset(worlds)]
        for star in _involutions(worlds):
            for r_subset in _powerset(triples):
                relation = frozenset(r_subset)
                for choice in product(world_subsets, repeat=len(atoms)):
                    model = RelevantModel(worlds, normal, star, relation,
                                          dict(zip(atoms, choice)))
                    # rel_satisfies IS the verification: a False here certifies
                    # that the model refutes the formula at its normal world.
                    if not rel_satisfies(model, w0, formula):
                        return model, w0
    return None


def rel_valid(formula: Node, max_worlds: int = 2) -> bool:
    """Return True iff no B-countermodel to ``formula`` is found within the bound.

    HONEST CONTRACT (mirroring
    :func:`~unicode_fol_kit.semantics.intuitionistic.int_valid`'s first-order
    contract): ``False`` is *definitive* — it is backed by an explicit,
    :func:`rel_satisfies`-verified countermodel from :func:`rel_countermodel`,
    so the formula is certainly not a theorem of B. ``True`` means only "no
    countermodel with at most ``max_worlds`` worlds": B is decidable, but this
    search is *bounded*, so a non-theorem whose smallest refuting interpretation
    needs more worlds than the bound is (spuriously) reported valid — for a
    certified positive verdict use
    :func:`~unicode_fol_kit.hol.isabelle_runner.isabelle_decide_relevant`, whose
    proof battery is a real validity proof over EVERY interpretation satisfying
    B's frame conditions (N nonempty, the Routley star a total involution, R
    sourced only at non-normal worlds) — not just those with at most
    ``max_worlds`` worlds. Raising ``max_worlds`` never turns a ``False`` into a
    ``True``; it is exponentially more expensive (see :func:`rel_countermodel`).
    """
    return rel_countermodel(formula, max_worlds) is None
