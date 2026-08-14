# Checking at campaign scale

Three questions, three entry points, and they are easy to confuse:

| Question | Entry point |
|---|---|
| Does this formula hold in *this* structure? | {func}`~unicode_fol_kit.semantics.evaluate_detailed` — {doc}`model-checking` |
| How good is *this* definition against a labelled split? | `eval.datasets.c3po.score_definition` — a confusion matrix |
| Run *these* definitions over *these* molecules and write down everything that happened | {func}`~unicode_fol_kit.eval.check_definitions` — this page |

The third is what a campaign needs: thousands of checks, hours of wall clock, and
a result that survives the run being interrupted. Its whole contract follows from
one distinction.

## Data becomes a row; configuration raises

> **Is this failure a property of the input data, or of the configuration?**

A molecule RDKit refuses, a definition that mentions a predicate no structure
interprets, an evaluation that runs out of budget — those are *data*. Each
becomes a row with a `status`, so one bad molecule among 200 000 never costs the
other 199 999.

RDKit not installed, an unknown `naming`, a results path whose directory does not
exist — those are *configuration*. They fail loudly **before the first molecule
is built**, because reporting them as 200 000 identical error rows would bury the
one thing worth fixing.

```python
from unicode_fol_kit.eval import check_definitions

AMIDE = "?[C,O,N]: (c(C) & o(O) & n(N) & bDOUBLE(C,O) & bSINGLE(C,N))"

result = check_definitions(
    [{"id": "amide", "formula": AMIDE},
     {"id": "broken", "formula": "?[X]: (c(X) &"}],          # will not parse
    ["NCC(=O)NCC(=O)O", "CCO", "not-a-molecule((("]           # one bad SMILES
)
print(result.counts)
# → {'ok': 2, 'exhausted': 0, 'structure_error': 1, 'parse_error': 1, 'eval_error': 0}
```

Two definitions × three molecules would be six checks. It is four rows: the
unparseable definition is reported **once**, on a row with `smiles=None`, and
then skipped — a broken formula is one fact about the definition, not three facts
about the molecules.

And the configuration side, before anything is built:

```python
from unicode_fol_kit.eval import check_definitions

AMIDE = "?[C,O,N]: (c(C) & o(O) & n(N) & bDOUBLE(C,O) & bSINGLE(C,N))"
try:
    check_definitions([{"id": "a", "formula": AMIDE}], ["CCO"], naming="nonsense")
except ValueError as exc:
    print(str(exc)[:52])
# → check_definitions: unknown naming='nonsense'
```

## The statuses

| `status` | `holds` | Meaning |
|---|---|---|
| `ok` | `True`/`False` | evaluated |
| `exhausted` | **`None`** | the step budget ran out — never reported as `False` |
| `structure_error` | `None` | RDKit refused the SMILES; cached, so it costs one attempt per molecule for the whole run |
| `parse_error` | `None` | the definition did not parse; recorded once, definition skipped |
| `eval_error` | `None` | the evaluator refused this formula/structure pair — usually a class predicate that only exists in another definition |

`exhausted` earning its own status is not pedantry. Counting an undecided check
as a negative is how an evaluation quietly flatters itself:

```python
from unicode_fol_kit.eval import check_definitions

AMIDE = "?[C,O,N]: (c(C) & o(O) & n(N) & bDOUBLE(C,O) & bSINGLE(C,N))"
row = check_definitions([{"id": "amide", "formula": AMIDE}],
                        ["NCC(=O)NCC(=O)O"], budget=1).rows[0]
print(row["status"], row["holds"], row["exhausted"])
# → exhausted None True
```

## A definition that delegates

A class definition legitimately names *other* class predicates — they have to be
unfolded before a molecule can decide them. Refusing the definition for it would
reject most of a real corpus, so the unknown symbols are reported once per
definition instead:

```python
from unicode_fol_kit.eval import check_definitions

row = check_definitions([{"id": "delegating", "formula": "?[X]: (c(X) & lipid(X))"}],
                        ["CCO"]).rows[0]
print(row["status"], row["unknown_predicates"])
# → eval_error ['Lipid/1']
```

Reported as `Lipid/1`, not `lipid/1`: the TPTP importer capitalises every parsed
predicate and only ChemLog's own 35 symbols are renamed back, so a class
predicate keeps the kit's spelling. The report names the symbol as the
*evaluator* saw it — which is the one you have to go and define.

## The cache is the point

A structure does not depend on the formula. So K definitions over N molecules
should build N structures, not K·N — and that is exactly what
{class}`~unicode_fol_kit.chem.StructureCache` does when you pass one in:

```python
from unicode_fol_kit.chem import StructureCache
from unicode_fol_kit.eval import check_definitions

AMIDE = "?[C,O,N]: (c(C) & o(O) & n(N) & bDOUBLE(C,O) & bSINGLE(C,N))"
ACID = "?[C,O1,O2]: (c(C) & o(O1) & o(O2) & bDOUBLE(C,O1) & bSINGLE(C,O2))"

cache = StructureCache()
check_definitions([{"id": "amide", "formula": AMIDE},
                   {"id": "acid", "formula": ACID}],
                  ["NCC(=O)NCC(=O)O", "CCO", "CC(=O)O"], cache=cache)
print(cache.stats()["misses"], cache.stats()["hits"])
# → 3 3
```

Three molecules built once each; the second definition hits all three. Measured
on this kit with four definitions over sixty molecules: **1860 → 8000 checks per
second, a factor of 4.3**, at a hit rate of 0.958. The factor depends on how fast
the formula short-circuits — a definition that fails on its first conjunct makes
the structure build dominate, a hard three-variable pattern on a large molecule
makes it almost irrelevant.

### Why the key is a four-tuple

`(smiles, naming, aromatic, computed)`. Each field is load-bearing, and a key
missing any of them lets one call's structure answer another call's question:

- **`naming`** — `"chemlog"` spells the single bond `bSINGLE`, `"paper"` spells
  it `singleBond`. Cross-answered, every predicate comes back uninterpreted.
- **`aromatic`** — `False` Kekulizes the bond typing, so `bAROMATIC` is empty
  where `True` fills it. Benzene answers differently.
- **`computed`** — `False` omits `in_ring`, `aromatic` and friends entirely, so a
  definition mentioning one raises instead of deciding.

The SMILES is stored **raw, never canonicalised**: individual names are a readout
of the input string's atom order (`"CCO"` names the methyl carbon `c1`, `"OCC"`
names the methylene carbon `c1`), so canonicalising would merge two structures
whose individuals mean different atoms and mislabel every witness.

```python
from unicode_fol_kit.chem import StructureCache

cache = StructureCache()
full = cache.structure_for("CCO", computed=True)
lean = cache.structure_for("CCO", computed=False)
print(full is lean, full.interprets("in_ring", 1), lean.interprets("in_ring", 1))
# → False True False
```

Failures are cached too — a SMILES RDKit refuses will be refused identically next
time, so it costs one RDKit call for the whole run, not one per definition.

## Surviving an interrupt

Rows are flushed to JSONL after each **definition**, so a run killed at 90 % keeps
90 %. Re-running reads back what is already there and skips those pairs:

```python
import tempfile, os
from unicode_fol_kit.eval import check_definitions

AMIDE = "?[C,O,N]: (c(C) & o(O) & n(N) & bDOUBLE(C,O) & bSINGLE(C,N))"
path = os.path.join(tempfile.mkdtemp(), "rows.jsonl")

first = check_definitions([{"id": "amide", "formula": AMIDE}],
                          ["NCC(=O)NCC(=O)O", "CCO"], results_path=path)
second = check_definitions([{"id": "amide", "formula": AMIDE}],
                           ["NCC(=O)NCC(=O)O", "CCO"], results_path=path)
print(len(first.rows), len(second.rows), second.skipped)
# → 2 0 2
```

`rows` and `counts` describe the work **this call** did; `skipped` says how many
pairs the resume passed over, so the difference between the call and the file is
never silent. Pass `resume=False` to redo everything.

A truncated final line — the normal shape of an interrupted run — is ignored
rather than raising: the pair it described simply gets redone.

## Where to go next

- {doc}`model-checking` — what a single check does, and what a witness looks like.
- {doc}`verification` — auditing the definition *set* itself: circularity,
  subsumption, and whether a definition is too easily satisfied.
- {doc}`interoperability` — where the definitions can come from, including a rule
  learner's Prolog output.
