"""A molecule-structure cache that survives a whole campaign.

Why this is worth a module. Checking K class definitions against N molecules
rebuilds the same :class:`~unicode_fol_kit.semantics.structures.FiniteStructure`
K times unless something remembers it — and the structure does not depend on
the formula at all. Measured on this kit (Python 3.11, rdkit 2026.03.5):
building a structure costs 0.045 ms (methane) to 1.04 ms (ATP, 31 heavy
atoms), rising linearly in the domain size, while EVALUATING a definition
against it costs 0.005–1.13 ms depending almost entirely on the FORMULA. So
the ratio build/evaluate runs from about 0.6 (a hard three-variable pattern on
a large molecule) to 58 (a definition that short-circuits immediately), and
caching turns ``K·(build + eval)`` into ``build + K·eval`` — a speed-up of
``1 + build/eval``, i.e. **1.6× to 59×**, around 3–8× for a realistic mix.
Worth doing, and worth measuring rather than assuming, which is why
:attr:`StructureCache.hits`/:attr:`~StructureCache.misses` are part of the
type rather than something a caller has to bolt on.

**The key is the full option tuple, not the SMILES.**
:func:`~unicode_fol_kit.chem.mol_to_structure` builds a genuinely different
structure for the same molecule depending on three parameters, and a key that
omits any of them lets one call's structure silently answer another call's
question:

* ``naming`` — ``"chemlog"`` spells the carbon predicate ``c`` and the single
  bond ``bSINGLE``; ``"paper"`` spells them ``c`` and ``singleBond``. A
  formula checked against the wrong one fails with
  :class:`~unicode_fol_kit.semantics.model_eval.UninterpretedSymbol` on every
  molecule — a different failure than "does not hold", and a confusing one.
* ``aromatic`` — ``False`` Kekulizes the bond typing, so ``bAROMATIC`` is
  empty where ``True`` fills it. Benzene answers differently.
* ``computed`` — ``False`` omits ``in_ring``, ``in_ring_of_size_N``,
  ``aromatic``, ``same_fragment`` and ``carbon_connected`` entirely, so a
  definition mentioning any of them raises instead of deciding.

The SMILES is stored **raw, never canonicalised**: individual names are a
readout of the input string's atom order (``"CCO"`` names the methyl carbon
``c1``, ``"OCC"`` names the methylene carbon ``c1``), so canonicalising would
merge two structures whose individuals mean different atoms and mislabel every
witness. Two spellings of one molecule therefore cost two entries — the
correct trade.

What is deliberately NOT in the key: ``all_different``, the evaluation budget,
and the formula. Those decide the VERDICT, not the structure; a verdict cache
is a separate concern and this module does not pretend to be one.

Failures are cached too. A SMILES RDKit refuses will be refused identically
next time, so :class:`StructureBuildError` is stored in place of the structure
and returned on the next lookup instead of paying for the same failure again.
"""

from collections import OrderedDict
from typing import Any, Dict, Iterator, Optional, Tuple

__all__ = ["StructureBuildError", "StructureCache", "CacheKey"]

#: ``(smiles, naming, aromatic, computed)`` — see the module docstring for why
#: each field is load-bearing.
CacheKey = Tuple[str, str, bool, bool]


class StructureBuildError:
    """Cached in place of a structure when
    :func:`~unicode_fol_kit.chem.mol_to_structure` refused a SMILES.

    Deliberately NOT an exception: it is a stored VALUE, and raising it on
    lookup would make a cache hit and a cache miss behave differently at the
    call site. Callers test with ``isinstance`` and read :attr:`message`.
    """

    __slots__ = ("message",)

    def __init__(self, message: str):
        self.message = message

    def __repr__(self) -> str:            # pragma: no cover - debugging aid
        return f"StructureBuildError({self.message!r})"

    def __eq__(self, other: object) -> bool:
        return (isinstance(other, StructureBuildError)
                and other.message == self.message)

    def __hash__(self) -> int:
        return hash((StructureBuildError, self.message))


class StructureCache:
    """Build-or-fetch cache for molecule structures, with a bounded size.

    Implements enough of the ``MutableMapping`` protocol
    (``in``/``[]``/``[]=``/``del``/``len``/iteration) to be passed straight to
    :func:`unicode_fol_kit.eval.datasets.c3po.score_definition`'s
    ``structure_cache`` parameter, which is typed against that protocol and
    was previously handed a plain ``dict``.

    Eviction is least-recently-used and bounded by ``max_entries``, because a
    campaign over hundreds of thousands of molecules would otherwise hold
    every structure it ever built. LRU rather than "clear when full": the
    campaign loop revisits the SAME molecules across definitions, so recency
    is exactly the right predictor here.

    Args:
        max_entries: hard upper bound on stored structures. ``None`` disables
            eviction (use only when the molecule set is known to be small).
    """

    def __init__(self, *, max_entries: Optional[int] = 100_000):
        if max_entries is not None and max_entries < 1:
            raise ValueError("StructureCache: max_entries must be >= 1 or None")
        self.max_entries = max_entries
        self._entries: "OrderedDict[CacheKey, Any]" = OrderedDict()
        self.hits = 0
        self.misses = 0
        self.evictions = 0

    # -- mapping protocol ---------------------------------------------------

    def __contains__(self, key: object) -> bool:
        return key in self._entries

    def __getitem__(self, key: CacheKey) -> Any:
        value = self._entries[key]
        self._entries.move_to_end(key)
        return value

    def __setitem__(self, key: CacheKey, value: Any) -> None:
        self._entries[key] = value
        self._entries.move_to_end(key)
        while self.max_entries is not None and len(self._entries) > self.max_entries:
            self._entries.popitem(last=False)
            self.evictions += 1

    def __delitem__(self, key: CacheKey) -> None:
        del self._entries[key]

    def __len__(self) -> int:
        return len(self._entries)

    def __iter__(self) -> Iterator[CacheKey]:
        return iter(self._entries)

    # -- build-or-fetch -----------------------------------------------------

    def structure_for(self, smiles: str, *, naming: str = "chemlog",
                      aromatic: bool = True, computed: bool = True) -> Any:
        """The structure for ``smiles`` under these options, built once.

        Returns either a
        :class:`~unicode_fol_kit.semantics.structures.FiniteStructure` or a
        :class:`StructureBuildError` — the latter for a SMILES
        :func:`~unicode_fol_kit.chem.mol_to_structure` refused, which is
        per-molecule DATA and must not stop a campaign.

        :class:`ImportError` (RDKit missing) and :class:`TypeError` (a caller
        passing something that is not a string) propagate untouched: those are
        environment and caller bugs, and turning them into 200 000 identical
        cached "errors" would bury the one thing worth fixing.
        """
        from .mol import mol_to_structure

        key: CacheKey = (smiles, naming, aromatic, computed)
        if key in self._entries:
            self.hits += 1
            return self[key]
        self.misses += 1
        try:
            value: Any = mol_to_structure(smiles, naming=naming,
                                          aromatic=aromatic, computed=computed)
        except ValueError as exc:
            value = StructureBuildError(f"{type(exc).__name__}: {exc}")
        self[key] = value
        return value

    # -- reporting ----------------------------------------------------------

    @property
    def hit_rate(self) -> Optional[float]:
        """Hits over lookups, or ``None`` before the first lookup — never a
        fabricated 0.0 for a cache nobody has asked anything yet."""
        total = self.hits + self.misses
        return self.hits / total if total else None

    def stats(self) -> Dict[str, Any]:
        return {"entries": len(self._entries), "hits": self.hits,
                "misses": self.misses, "evictions": self.evictions,
                "hit_rate": self.hit_rate, "max_entries": self.max_entries}
