# Many-valued logic

Evaluate and decide classical-syntax formulas over more than two truth values: the three-valued Kleene **K3** and Priest **LP** logics over `{0, ½, 1}`, and — new in 0.9.0 — arbitrary finite logical matrices, including the four-valued Belnap–Dunn **FDE**.

All inputs are ordinary classical formulas built with `MSFLParser()`; there is no new grammar. A logic is fixed entirely by its set of truth values, its **designated** (assertible) values, and the truth tables for the connectives. This page walks the surface top to bottom — evaluation, truth tables, the three-valued decision procedures, and the general finite-matrix layer — and finishes with an end-to-end scenario.

| You want to… | Use | Lives in |
|---|---|---|
| Score one formula under a fixed `{0, ½, 1}` valuation | `kleene_value` | top level |
| Enumerate a propositional truth table | `truth_table`, `is_tautology`, … | top level |
| Decide K3/LP validity, satisfiability, entailment | `is_valid` / `is_satisfiable` / `entails` | `unicode_fol_kit.semantics` |
| Work in *any* finite logic (incl. FDE, custom) | `matrix_value`, `matrix_is_valid`, … | top level (and `semantics.matrix`) |

## Three-valued evaluation: `kleene_value`

`kleene_value()` evaluates a classical formula over the three values `0.0` (false), `0.5` (undefined / both) and `1.0` (true) using the strong-Kleene tables:

```
¬x    = 1 − x
a ∧ b = min(a, b)
a ∨ b = max(a, b)
a → b = max(1 − a, b)        (material implication)
a ↔ b = min(a → b, b → a)
a ⊕ b = min(max(a, b), 1 − min(a, b))    (exclusive or)
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

Every classical connective has a strong-Kleene reading, including `↔` and `⊕`, and they nest as expected:

```python
kleene_value(p.parse("P ↔ Q"), {"P": 1.0, "Q": 0.0})  # → 0.0   (min(0, 1))
kleene_value(p.parse("P ↔ Q"), {"P": 0.5, "Q": 0.5})  # → 0.5   (½ ↔ ½ is undefined)
kleene_value(p.parse("P ⊕ Q"), {"P": 1.0, "Q": 0.5})  # → 0.5   (xor with an undefined arg)
kleene_value(p.parse("(P ∨ Q) → R"), {"P": 0.0, "Q": 0.5, "R": 0.0})  # → 0.5
```

A ground atom's key is its full canonical surface form, so `P` and `P(a)` are independent keys:

```python
kleene_value(p.parse("P(a) ∧ P(b)"), {"P(a)": 1.0, "P(b)": 0.5})  # → 0.5
```

### More evaluation examples

Deeply nested structures compute correctly thanks to associativity and proper precedence:

```python
kleene_value(p.parse("((P ∧ Q) ∨ R) → S"), 
             {"P": 0.5, "Q": 1.0, "R": 0.0, "S": 0.5})  # → 0.5
```

The contrapositive law `(P → Q) ↔ (¬Q → ¬P)` is valid in LP but not K3:

```python
contrapositive = p.parse("(P → Q) ↔ (¬Q → ¬P)")
kleene_value(contrapositive, {"P": 0.5, "Q": 0.0})  # → 0.5  (½ ↔ ½ is ½, undesignated in K3)
kleene_value(contrapositive, {"P": 0.0, "Q": 1.0})  # → 1.0  (1 ↔ 1 is 1, designated in both)
```

Double negation `P ↔ ¬¬P` is also paracomplete-sensitive:

```python
double_neg = p.parse("P ↔ ¬¬P")
kleene_value(double_neg, {"P": 0.5})  # → 0.5  (½ ↔ ½)
kleene_value(double_neg, {"P": 1.0})  # → 1.0  (1 ↔ 1)
kleene_value(double_neg, {"P": 0.0})  # → 1.0  (0 ↔ 0)
```

### Quantifiers need a domain

A quantifier is read substitutionally over a finite `domain` of constant names: `∀` takes the `min` and `∃` the `max` of the body across the domain.

```python
kleene_value(p.parse("∀x P(x)"), {"P(a)": 1.0, "P(b)": 0.5}, domain={"a", "b"})  # → 0.5  (min)
kleene_value(p.parse("∃x P(x)"), {"P(a)": 0.0, "P(b)": 0.5}, domain={"a", "b"})  # → 0.5  (max)
```

Nested quantifiers over two-place predicates require all ground instances:

```python
# ∃x ∀y P(x, y) — "there exists x such that P holds for all y"
valuation = {
    "P(a, a)": 1.0, "P(a, b)": 1.0,
    "P(b, a)": 0.0, "P(b, b)": 0.0
}
kleene_value(p.parse("∃x ∀y P(x, y)"), valuation, domain={"a", "b"})  # → 1.0
# At x=a: ∀y P(a,y) = min(1,1) = 1; at x=b: ∀y P(b,y) = min(0,0) = 0; ∃ = max(1,0) = 1
```

Quantifier scope interacts with undefined values:

```python
# ∀x (P(x) → Q(x)) with one undefined premise
kleene_value(p.parse("∀x (P(x) → Q(x))"), 
             {"P(a)": 1.0, "Q(a)": 1.0, "P(b)": 0.5, "Q(b)": 0.5},
             domain={"a", "b"})  # → 0.5
# At x=a: 1 → 1 = 1; at x=b: 0.5 → 0.5 = 0.5; ∀ = min(1, 0.5) = 0.5
```

### Common errors

`kleene_value` is strict about its inputs, which catches typos early. A missing atom key raises `KeyError`; a quantifier without a domain, or a valuation entry that is not one of `{0.0, 0.5, 1.0}`, raises `ValueError`; and a Łukasiewicz/sorted/lambda/modal node — which has no strong-Kleene reading — raises `NotImplementedError`.

```python
kleene_value(p.parse("P ∧ Q"), {"P": 1.0})    # raises KeyError: no value for 'Q'
kleene_value(p.parse("∀x P(x)"), {"P(a)": 1.0})  # raises ValueError: a Quantifier requires a 'domain'
kleene_value(p.parse("P"), {"P": 0.3})        # raises ValueError: value must be one of {0.0, 0.5, 1.0}
kleene_value(p.parse("∃x ∀y P(x, y)"), {"P(a, a)": 1.0}, domain={"a", "b"})  # raises KeyError on missing instances
```

## Truth tables: `truth_table`

`truth_table(formula, logic=...)` enumerates every assignment of a quantifier-free formula's atoms. The same strong-Kleene tables back all three logics; they differ only in the value set and the designated set. `classical` (the **default**) uses `{0, 1}` designating `{1}`; `K3` uses `{0, ½, 1}` designating `{1}`; `LP` uses `{0, ½, 1}` designating `{½, 1}`. `.render()` returns a GitHub-flavoured Markdown table (deterministic row order, values descending `1, ½, 0`).

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

The default `classical` logic uses two values and `T`/`F` glyphs:

```python
print(truth_table(p.parse("P → Q")).render())
# | P | Q | P → Q |
# |---|---|---|
# | T | T | T |
# | T | F | F |
# | F | T | T |
# | F | F | T |
```

A three-valued table grows to `3**n` rows; here is the full LP biconditional over two atoms (note `½ ↔ ½ = ½`, designated under LP):

```python
print(truth_table(p.parse("P ↔ Q"), logic="LP").render())
# | P | Q | P ↔ Q |
# |---|---|---|
# | 1 | 1 | 1 |
# | 1 | ½ | ½ |
# | 1 | 0 | 0 |
# | ½ | 1 | ½ |
# | ½ | ½ | ½ |
# | ½ | 0 | ½ |
# | 0 | 1 | 0 |
# | 0 | ½ | ½ |
# | 0 | 0 | 1 |
```

More truth table examples showing key schematic differences:

```python
# Exclusive or: asymmetry at undefined
tt_xor = truth_table(p.parse("P ⊕ Q"), logic="K3")
print(f"XOR is_tautology: {tt_xor.is_tautology}")  # → False
# At P=½, Q=½: (½ ∨ ½) ∧ ¬(½ ∧ ½) = ½ ∧ ½ = ½ (undesignated)

# Negation: perfectly symmetric around ½
tt_neg = truth_table(p.parse("P ∧ ¬P"), logic="LP")
print(f"Contradiction in LP: {tt_neg.is_contradiction}")  # → False  (½ makes it true!)
```

### Inspecting the `TruthTable` object

`truth_table` returns a `TruthTable` dataclass, not just a string. `.atoms` are the column headers, `.logic` the logic name, `.formula` the node, and `.rows` a tuple of `(assignment, value, designated)` triples — so you can drive your own analysis off the raw rows. `str(tt)` is `tt.render()`.

```python
tt = truth_table(p.parse("P ∨ ¬P"), logic="K3")
tt.atoms                              # → ('P',)
tt.logic                              # → 'K3'
tt.formula.to_unicode_str()           # → 'P ∨ ¬P'
tt.rows                               # → (((1.0,), 1.0, True), ((0.5,), 0.5, False), ((0.0,), 1.0, True))
[d for _, _, d in tt.rows]            # → [True, False, True]   (which rows are designated)
```

Programmatic analysis:

```python
# Find all undesignated rows
tt = truth_table(p.parse("P ∧ Q"), logic="K3")
undesignated = [(a, v) for a, v, d in tt.rows if not d]
print(len(undesignated))  # → 8  (out of 9: all except (T, T))
```

### Tautology / contradiction / satisfiability

The `TruthTable` carries `is_tautology` / `is_contradiction` / `is_satisfiable` properties, and there are convenience functions `is_tautology` / `is_contradiction` / `is_satisfiable_tt` that compute the table and read the property in one call:

```python
truth_table(p.parse("P ∨ ¬P"), logic="K3").is_tautology   # → False  (½ is undesignated)
truth_table(p.parse("P ∨ ¬P"), logic="LP").is_tautology   # → True   (½ is designated)
```

```python
from unicode_fol_kit import is_tautology, is_contradiction, is_satisfiable_tt

is_tautology(p.parse("P ∨ ¬P"))             # → True   (classical default)
is_tautology(p.parse("P ∨ ¬P"), "K3")       # → False
is_tautology(p.parse("P ∨ ¬P"), "LP")       # → True

is_contradiction(p.parse("P ∧ ¬P"))         # → True   (classical)
is_contradiction(p.parse("P ∧ ¬P"), "LP")   # → False  (designated at ½)
is_satisfiable_tt(p.parse("P ∧ ¬P"), "LP")  # → True
```

Quantified formulas have no finite truth table and are rejected:

```python
truth_table(p.parse("∀x P(x)"))   # raises ValueError: quantified formulas have no finite truth table
```

## Three-valued decisions: `is_valid` / `is_satisfiable` / `entails`

These three functions live in `unicode_fol_kit.semantics` and decide validity, satisfiability, and entailment by enumerating all `3**n` assignments of the `n` distinct ground atoms. They default to `logic="K3"`; pass `"LP"` for the paraconsistent reading.

```python
from unicode_fol_kit.semantics import is_valid, is_satisfiable, entails
```

They are intentionally namespaced under `semantics` so they do not shadow the Z3-based `is_valid` / `is_satisfiable` exported at the package top level. These are the **three-valued** decision procedures. An unknown logic name is rejected:

```python
is_valid(p.parse("P ∨ ¬P"), "FDE")   # raises ValueError: Unknown logic 'FDE'; choose one of ['K3', 'LP']
```

(For FDE and other matrices, use the matrix layer below.)

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

### Entailment with several premises

`entails` enumerates over the ground atoms of the premises *and* the conclusion together. Both the disjunctive syllogism `P ∨ Q, ¬P ⊨ Q` and even **modus ponens** `P, P → Q ⊨ Q` hold in K3 but fail in LP — the price LP pays for paraconsistency, because its material `→` does not detach. Each fails in LP at `P = ½, Q = 0` (both premises take the designated `½`, yet `Q = 0`):

```python
mp = ([p.parse("P"), p.parse("P → Q")], p.parse("Q"))         # modus ponens
ds = ([p.parse("P ∨ Q"), p.parse("¬P")], p.parse("Q"))        # disjunctive syllogism

entails(*mp, "K3")    # → True
entails(*mp, "LP")    # → False   LP's material → does not detach (fails at P=½, Q=0)
entails(*ds, "K3")    # → True
entails(*ds, "LP")    # → False   the paraconsistent price: DS fails at P=½, Q=0
```

Quantified decisions instantiate the quantifier over a `domain` first, so a `domain=` is required when a quantifier is present. Universal instantiation `∀x P(x) → P(a)` is conditional-shaped, so — like every `→`-law — it fails in K3 (no logical truths from the material conditional) but holds in LP:

```python
ui = p.parse("∀x P(x) → P(a)")
is_valid(ui, "K3", domain={"a", "b"})  # → False
is_valid(ui, "LP", domain={"a", "b"})  # → True
```

## Finite matrices: `semantics.matrix`

New in 0.9.0, `unicode_fol_kit.semantics.matrix` makes the matrix schema first-class, so *any* finite many-valued logic can be evaluated and decided — not just the hard-wired `{0, ½, 1}`. A `TruthMatrix` is a set of values, a designated subset, and a table per connective. The decision procedures mirror the three-valued ones: `matrix_value`, `matrix_is_valid`, `matrix_is_satisfiable`, `matrix_entails`. All of these — and the shipped matrices below — are also re-exported at the package top level.

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

### `matrix_value` — one formula under a fixed assignment

`matrix_value(formula, valuation, matrix, domain=None)` is the matrix analogue of `kleene_value`: it scores one formula to a matrix value. The valuation maps each ground-atom key to a value of the matrix.

```python
from unicode_fol_kit.semantics.matrix import matrix_value, K3_MATRIX

matrix_value(p.parse("P ∧ Q"), {"P": 1.0, "Q": 0.5}, K3_MATRIX)   # → 0.5
matrix_value(p.parse("P → P"), {"P": 0.5}, K3_MATRIX)             # → 0.5  (material ½→½)
```

### Introspecting a matrix

A `TruthMatrix` exposes its `name`, `values`, `designated` set, the per-connective tables (`neg`, `conj`, `disj`, `impl`, `iff`, `xor` — plain dicts), and an `is_designated(v)` helper:

```python
from unicode_fol_kit.semantics.matrix import K3_MATRIX, LP_MATRIX

K3_MATRIX.values                  # → (0.0, 0.5, 1.0)
sorted(K3_MATRIX.designated)      # → [1.0]
sorted(LP_MATRIX.designated)      # → [0.5, 1.0]
K3_MATRIX.is_designated(0.5)      # → False
LP_MATRIX.is_designated(0.5)      # → True
K3_MATRIX.conj[(0.5, 1.0)]        # → 0.5   (min, straight from the table)
```

### Shipped K3 / LP matrices

`K3_MATRIX`, `LP_MATRIX` and `FDE_MATRIX` ship built in (and `MATRICES` maps `"K3"`/`"LP"`/`"FDE"` to them). K3 and LP are re-expressed here as matrices and reproduce the three-valued decisions exactly:

```python
from unicode_fol_kit.semantics.matrix import (
    K3_MATRIX, LP_MATRIX, matrix_is_valid, matrix_is_satisfiable, matrix_entails,
)

lem = p.parse("P ∨ ¬P")
P, notP, Q = p.parse("P"), p.parse("¬P"), p.parse("Q")

matrix_is_valid(lem, K3_MATRIX)               # → False
matrix_is_valid(lem, LP_MATRIX)               # → True
matrix_entails([P, notP], Q, K3_MATRIX)       # → True
matrix_entails([P, notP], Q, LP_MATRIX)       # → False

matrix_is_satisfiable(p.parse("P ∧ ¬P"), K3_MATRIX)   # → False
matrix_is_satisfiable(p.parse("P ∧ ¬P"), LP_MATRIX)   # → True
```

### Four-valued Belnap–Dunn FDE

`FDE_MATRIX` is the Belnap–Dunn four-valued logic of first-degree entailment. Each value is a `(has-true, has-false)` bit pair: `T` (true only), `F` (false only), `N` (neither / told nothing), `B` (both). The designated values are the true-containing ones, `{T, B}`.

```python
from unicode_fol_kit.semantics.matrix import FDE_MATRIX

FDE_MATRIX.values             # → ('F', 'N', 'T', 'B')
sorted(FDE_MATRIX.designated) # → ['B', 'T']
```

Negation swaps the two bits, so `T ↔ F`, while `N` and `B` are their own negations:

```python
[FDE_MATRIX.neg[v] for v in FDE_MATRIX.values]   # → ['T', 'N', 'F', 'B']
```

You can read off the whole conjunction table straight from the dict — `∧` keeps `T` only when both have-true, and collects `F` when either has-false:

```python
{(a, b): FDE_MATRIX.conj[(a, b)]
 for a in ("T", "B") for b in ("F", "N")}
# → {('T', 'F'): 'F', ('T', 'N'): 'N', ('B', 'F'): 'F', ('B', 'N'): 'F'}
```

FDE is both **paraconsistent** (`p ∧ ¬p ⊭ q`) and **paracomplete** (`p ⊭ q ∨ ¬q`), and — unlike K3/LP — has **no logical truths at all**: even `p → p` fails, taking the undesignated value `N` at `N`.

```python
from unicode_fol_kit.semantics.matrix import (
    FDE_MATRIX, matrix_value, matrix_is_valid, matrix_is_satisfiable, matrix_entails,
)

matrix_is_valid(p.parse("P → P"), FDE_MATRIX)        # → False   p→p is not valid
matrix_is_valid(p.parse("P ∨ ¬P"), FDE_MATRIX)       # → False   excluded middle fails
matrix_value(p.parse("P → P"), {"P": "N"}, FDE_MATRIX)  # → 'N'   undesignated, hence the failure

matrix_entails([P, notP], Q, FDE_MATRIX)             # → False   paraconsistent: explosion fails
matrix_entails([P], p.parse("Q ∨ ¬Q"), FDE_MATRIX)   # → False   paracomplete: q∨¬q not entailed
matrix_is_satisfiable(p.parse("P ∧ ¬P"), FDE_MATRIX) # → True    designated at B
```

`FDE_MATRIX` — or any matrix you build with `TruthMatrix.from_functions` — also exports to TPTP THF and Isabelle/HOL: `hol.to_thf_matrix` / `hol.to_isabelle_matrix` generalise the K3/LP exporters to work data-driven over any `TruthMatrix`. See {doc}`higher-order`.

### Comparing the three shipped logics side by side

Iterating `MATRICES` shows where the four classic inferences land in each logic — and that K3 alone is explosive while only LP has logical truths from `∨`/`¬`:

```python
from unicode_fol_kit.semantics.matrix import MATRICES, matrix_is_valid, matrix_entails

sorted(MATRICES)                                  # → ['FDE', 'K3', 'LP']

lem = p.parse("P ∨ ¬P")
pp  = p.parse("P → P")
ds  = ([p.parse("P ∨ Q"), p.parse("¬P")], p.parse("Q"))   # disjunctive syllogism

for name in ("K3", "LP", "FDE"):
    M = MATRICES[name]
    print(name,
          matrix_is_valid(lem, M),        # excluded middle
          matrix_is_valid(pp, M),         # p → p
          matrix_entails([P, notP], Q, M),  # explosion
          matrix_entails(*ds, M))         # disjunctive syllogism
# K3 False False True True
# LP True True False False
# FDE False False False False
```

So LP keeps every logical truth but drops explosion *and* the disjunctive syllogism; K3 keeps explosion (and DS) but loses excluded middle; FDE drops everything, including `p → p`.

### Quantifiers over a matrix

`matrix_value` and the deciders take a `domain` and fold `conj` (`∀`) / `disj` (`∃`) over it — a generalised min/max — so quantified formulas work in any matrix without extra tables. A quantified decision requires a non-empty `domain`.

```python
matrix_value(p.parse("∀x P(x)"), {"P(a)": "T", "P(b)": "B"}, FDE_MATRIX, domain=("a", "b"))  # → 'B'  (conj)
matrix_value(p.parse("∃x P(x)"), {"P(a)": "F", "P(b)": "N"}, FDE_MATRIX, domain=("a", "b"))  # → 'N'  (disj)
matrix_is_valid(p.parse("∀x (P(x) → P(x))"), FDE_MATRIX, domain=("a", "b"))                  # → False
```

## Building a custom matrix

`from_functions` is all you need to add a new finite logic. Supply the value set, the designated subset, and value-level `neg` / `conj` / `disj` (and optionally `impl`); the biconditional and exclusive-or are derived for you. Two illustrative builds:

**Łukasiewicz Ł3** — same values and designated set as K3, but a *different* conditional `min(1, 1−a+b)` instead of the material `max(1−a, b)`. The one change makes `p → p` valid (it is the only three-valued conditional that does):

```python
from unicode_fol_kit.semantics.matrix import (
    TruthMatrix, matrix_value, matrix_is_valid, K3_MATRIX,
)

L3 = TruthMatrix.from_functions(
    "Ł3", values=(0.0, 0.5, 1.0), designated=(1.0,),
    neg=lambda x: 1.0 - x, conj=min, disj=max,
    impl=lambda a, b: min(1.0, 1.0 - a + b),     # Łukasiewicz conditional
)

matrix_value(p.parse("P → P"), {"P": 0.5}, L3)          # → 1.0   (Łukasiewicz ½→½)
matrix_value(p.parse("P → P"), {"P": 0.5}, K3_MATRIX)   # → 0.5   (material ½→½)
matrix_is_valid(p.parse("P → P"), L3)                   # → True
matrix_is_valid(p.parse("P → P"), K3_MATRIX)            # → False
```

**A plain two-valued classical matrix** — `from_functions` happily builds the ordinary boolean logic, recovering the classical theorems (Peirce's law, excluded middle) and explosion:

```python
from unicode_fol_kit.semantics.matrix import matrix_is_valid, matrix_entails

CL2 = TruthMatrix.from_functions(
    "CL2", values=(0.0, 1.0), designated=(1.0,),
    neg=lambda x: 1.0 - x, conj=min, disj=max,
)
matrix_is_valid(p.parse("P ∨ ¬P"), CL2)                                      # → True
matrix_is_valid(p.parse("((P → Q) → P) → P"), CL2)                           # → True   (Peirce)
matrix_entails([p.parse("P"), p.parse("¬P")], p.parse("Q"), CL2)             # → True   (explosive)
```

### Build-time and run-time checks

Because every connective result is checked against the value set at build time, a table that escapes the values is rejected immediately — you cannot ship a malformed matrix:

```python
TruthMatrix.from_functions(                       # raises ValueError: a connective produced 0.5
    "bad", values=(0.0, 1.0), designated=(1.0,),  #   which is not one of the matrix values
    neg=lambda x: 0.5, conj=min, disj=max,
)
TruthMatrix.from_functions(                        # raises ValueError: designated value 0.5 is not a value
    "bad2", values=(0.0, 1.0), designated=(0.5,),
    neg=lambda x: 1.0 - x, conj=min, disj=max,
)
```

At evaluation time, a missing atom raises `KeyError` and a value outside the matrix raises `ValueError`:

```python
matrix_value(p.parse("P ∧ Q"), {"P": "T"}, FDE_MATRIX)   # raises KeyError: no value for ground atom 'Q'
matrix_value(p.parse("P"), {"P": "X"}, FDE_MATRIX)        # raises ValueError: 'X' is not a matrix value
matrix_is_valid(p.parse("∀x P(x)"), FDE_MATRIX)          # raises ValueError: requires a non-empty 'domain'
```

## End-to-end: parse → decide → tabulate

A complete walk for one formula, from string to rendered table. We take the law of excluded middle, decide it three ways, and render the K3 and LP truth tables to compare where the value `½` lands:

```python
from unicode_fol_kit import MSFLParser, truth_table
from unicode_fol_kit.semantics import is_valid
from unicode_fol_kit.semantics.matrix import matrix_is_valid, K3_MATRIX, LP_MATRIX, FDE_MATRIX

p = MSFLParser()
lem = p.parse("P ∨ ¬P")

# 1. Decide with the three-valued procedures…
is_valid(lem, "K3")                      # → False
is_valid(lem, "LP")                      # → True

# 2. …and cross-check via the matrix layer (incl. four-valued FDE).
matrix_is_valid(lem, K3_MATRIX)          # → False
matrix_is_valid(lem, LP_MATRIX)          # → True
matrix_is_valid(lem, FDE_MATRIX)         # → False   FDE has no logical truths

# 3. Tabulate to see exactly why: the ½ row is undesignated under K3, designated under LP.
print(truth_table(lem, logic="K3").render())
# | P | P ∨ ¬P |
# |---|---|
# | 1 | 1 |
# | ½ | ½ |
# | 0 | 1 |

truth_table(lem, "K3").is_tautology      # → False  (the ½ row breaks it)
truth_table(lem, "LP").is_tautology      # → True   (½ is designated under LP)
```
