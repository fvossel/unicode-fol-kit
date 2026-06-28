# Many-valued logic

Evaluate and decide classical-syntax formulas over more than two truth values: the three-valued Kleene **K3** and Priest **LP** logics over `{0, ½, 1}`, and — new in 0.9.0 — arbitrary finite logical matrices, including the four-valued Belnap–Dunn **FDE**.

All inputs are ordinary classical formulas built with `MSFLParser()`; there is no new grammar. A logic is fixed entirely by its set of truth values, its **designated** (assertible) values, and the truth tables for the connectives.

## Three-valued evaluation: `kleene_value`

`kleene_value()` evaluates a classical formula over the three values `0.0` (false), `0.5` (undefined / both) and `1.0` (true) using the strong-Kleene tables:

```
¬x    = 1 − x
a ∧ b = min(a, b)
a ∨ b = max(a, b)
a → b = max(1 − a, b)        (material implication)
a ↔ b = min(a → b, b → a)
```

The valuation maps each ground atom's canonical `to_unicode_str()` key (e.g. `"P"`, `"P(a)"`) to one of the three values. Quantifiers range over a finite `domain` of constant names, with `∀ = min` and `∃ = max`.

```python
from unicode_fol_kit import MSFLParser, kleene_value

p = MSFLParser()
kleene_value(p.parse("P ∧ Q"), {"P": 1.0, "Q": 0.5})  # → 0.5   (min(1, ½))
kleene_value(p.parse("P ∧ ¬P"), {"P": 0.5})           # → 0.5   (min(½, ½))
kleene_value(p.parse("P → Q"), {"P": 1.0, "Q": 0.0})  # → 0.0   (max(0, 0))
kleene_value(p.parse("P ∨ ¬P"), {"P": 0.5})           # → 0.5   (excluded middle is undefined at ½)
```

## Truth tables: `truth_table`

`truth_table(formula, logic=...)` enumerates every assignment of a quantifier-free formula's atoms. The same strong-Kleene tables back all three logics; they differ only in the value set and the designated set. `classical` uses `{0, 1}` designating `{1}`; `K3` uses `{0, ½, 1}` designating `{1}`; `LP` uses `{0, ½, 1}` designating `{½, 1}`. `.render()` returns a GitHub-flavoured Markdown table (deterministic row order, values descending `1, ½, 0`).

```python
from unicode_fol_kit import MSFLParser, truth_table

p = MSFLParser()
print(truth_table(p.parse("P ∨ ¬P"), logic="K3").render())
```

K3 truth table for the law of excluded middle — note the middle row takes value `½`, which is **not** designated under K3:

```
| P | P ∨ ¬P |
|---|---|
| 1 | 1 |
| ½ | ½ |
| 0 | 1 |
```

The `TruthTable` carries `is_tautology` / `is_contradiction` / `is_satisfiable` properties:

```python
truth_table(p.parse("P ∨ ¬P"), logic="K3").is_tautology   # → False  (½ is undesignated)
truth_table(p.parse("P ∨ ¬P"), logic="LP").is_tautology   # → True   (½ is designated)
```

## Three-valued decisions: `is_valid` / `is_satisfiable` / `entails`

These three functions live in `unicode_fol_kit.semantics` and decide validity, satisfiability, and entailment by enumerating all `3**n` assignments of the `n` distinct ground atoms. They default to `logic="K3"`; pass `"LP"` for the paraconsistent reading.

```python
from unicode_fol_kit.semantics import is_valid, is_satisfiable, entails
```

They are intentionally namespaced under `semantics` so they do not shadow the Z3-based `is_valid` / `is_satisfiable` exported at the package top level. These are the **three-valued** decision procedures.

### Excluded middle and explosion

The single choice of designated set produces the headline contrasts between K3 and LP. The law of excluded middle `P ∨ ¬P` is K3-invalid but LP-valid; explosion `P, ¬P ⊨ Q` holds in K3 but fails in LP (LP is *paraconsistent*).

```python
from unicode_fol_kit import MSFLParser
from unicode_fol_kit.semantics import is_valid, is_satisfiable, entails

p = MSFLParser()
lem  = p.parse("P ∨ ¬P")
nc   = p.parse("¬(P ∧ ¬P)")
P, notP, Q = p.parse("P"), p.parse("¬P"), p.parse("Q")

is_valid(lem, "K3")            # → False   excluded middle fails in K3 (½ undesignated)
is_valid(lem, "LP")            # → True    holds in LP (½ designated)

is_valid(nc, "K3")             # → False   non-contradiction also fails in K3
is_valid(nc, "LP")             # → True

entails([P, notP], Q, "K3")    # → True    K3: P and ¬P are never both designated, so vacuous
entails([P, notP], Q, "LP")    # → False   LP is paraconsistent: at P=½, Q=0 both premises hold, Q does not

is_satisfiable(p.parse("P ∧ ¬P"), "K3")   # → False  a contradiction is never K3-designated
is_satisfiable(p.parse("P ∧ ¬P"), "LP")   # → True   designated at P=½
```

In short: K3 is **paracomplete** (no logical truths from `∨`/`¬` alone — excluded middle fails) and explosive; LP is **paraconsistent** (explosion fails) but validates excluded middle.

## Finite matrices: `semantics.matrix`

New in 0.9.0, `unicode_fol_kit.semantics.matrix` makes the matrix schema first-class, so *any* finite many-valued logic can be evaluated and decided — not just the hard-wired `{0, ½, 1}`. A `TruthMatrix` is a set of values, a designated subset, and a table per connective. The decision procedures mirror the three-valued ones: `matrix_value`, `matrix_is_valid`, `matrix_is_satisfiable`, `matrix_entails`.

`TruthMatrix.from_functions` materialises a matrix from value-level operations. `impl` defaults to the material conditional `¬a ∨ b`; the biconditional is `(a→b) ∧ (b→a)` and exclusive-or is `¬(a↔b)`. Every operation is checked to land back in the value set, so a malformed table is caught at build time. `∀` / `∃` fold `conj` / `disj` over a finite `domain` (a generalised min / max), so no separate quantifier tables are needed.

```python
from unicode_fol_kit import MSFLParser
from unicode_fol_kit.semantics.matrix import TruthMatrix, matrix_is_valid, matrix_entails

p = MSFLParser()

# K3 rebuilt as a matrix from scratch.
K3 = TruthMatrix.from_functions(
    "K3", values=(0.0, 0.5, 1.0), designated=(1.0,),
    neg=lambda x: 1.0 - x, conj=min, disj=max,
    impl=lambda a, b: max(1.0 - a, b),
)
matrix_is_valid(p.parse("P ∨ ¬P"), K3)                              # → False
matrix_entails([p.parse("P"), p.parse("¬P")], p.parse("Q"), K3)    # → True
```

### Shipped K3 / LP matrices

`K3_MATRIX`, `LP_MATRIX` and `FDE_MATRIX` ship built in (and `MATRICES` maps `"K3"`/`"LP"`/`"FDE"` to them). K3 and LP are re-expressed here as matrices and reproduce the three-valued decisions exactly:

```python
from unicode_fol_kit.semantics.matrix import (
    K3_MATRIX, LP_MATRIX, matrix_is_valid, matrix_entails,
)

lem = p.parse("P ∨ ¬P")
P, notP, Q = p.parse("P"), p.parse("¬P"), p.parse("Q")

matrix_is_valid(lem, K3_MATRIX)               # → False
matrix_is_valid(lem, LP_MATRIX)               # → True
matrix_entails([P, notP], Q, K3_MATRIX)       # → True
matrix_entails([P, notP], Q, LP_MATRIX)       # → False
```

### Four-valued Belnap–Dunn FDE

`FDE_MATRIX` is the Belnap–Dunn four-valued logic of first-degree entailment. Each value is a `(has-true, has-false)` bit pair: `T` (true only), `F` (false only), `N` (neither / told nothing), `B` (both). The designated values are the true-containing ones, `{T, B}`.

```python
from unicode_fol_kit.semantics.matrix import FDE_MATRIX

FDE_MATRIX.values             # → ('F', 'N', 'T', 'B')
sorted(FDE_MATRIX.designated) # → ['B', 'T']
```

FDE is both **paraconsistent** (`p ∧ ¬p ⊭ q`) and **paracomplete** (`p ⊭ q ∨ ¬q`), and — unlike K3/LP — has **no logical truths at all**: even `p → p` fails, taking the undesignated value `N` at `N`.

```python
from unicode_fol_kit.semantics.matrix import (
    FDE_MATRIX, matrix_value, matrix_is_valid, matrix_entails,
)

matrix_is_valid(p.parse("P → P"), FDE_MATRIX)        # → False   p→p is not valid
matrix_is_valid(p.parse("P ∨ ¬P"), FDE_MATRIX)       # → False   excluded middle fails
matrix_value(p.parse("P → P"), {"P": "N"}, FDE_MATRIX)  # → 'N'   undesignated, hence the failure

matrix_entails([P, notP], Q, FDE_MATRIX)             # → False   paraconsistent: explosion fails
matrix_entails([P], p.parse("Q ∨ ¬Q"), FDE_MATRIX)   # → False   paracomplete: q∨¬q not entailed
```
