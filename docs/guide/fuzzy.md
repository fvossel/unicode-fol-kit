# Fuzzy (Łukasiewicz / BL) logic

The fuzzy layer interprets the Łukasiewicz / basic-logic (BL) connectives over the real interval `[0, 1]`: `fuzzy_evaluate` computes a truth **degree** under a valuation, and `fuzzy_is_satisfiable` / `fuzzy_is_valid` / `fuzzy_get_model` decide formulas via Z3 reals. Version 0.9.0 adds a t-norm selector (Łukasiewicz / Gödel / product) and quantifier grounding so quantified fuzzy validity is decidable.

## Parsing fuzzy formulas (FL / MSFL mode)

Parse with `MSFLParser(fuzzy=True)` for single-sorted FL (unsorted quantifiers, plain constants) or `MSFLParser(many_sorted=True, fuzzy=True)` for many-sorted MSFL (`∀x:Sort`, `alice:Sort`). In both modes the connectives carry Łukasiewicz semantics:

| Surface | Node | Semantics |
|---|---|---|
| weak `∧` | `WeakConjunction` | `min(x, y)` |
| weak `∨` | `WeakDisjunction` | `max(x, y)` |
| strong `⊗` | `StrongConjunction` | t-norm (default `max(0, x+y−1)`) |
| strong `⊕` | `StrongDisjunction` | t-conorm (default `min(1, x+y)`) |
| `¬` | `LukNegation` | `1 − x` |
| `→` | `LukImplication` | `min(1, 1−x+y)` |
| `↔` | `LukEquivalence` | `1 − \|x−y\|` |

Classical boolean nodes (`And`/`Or`/`Not`/…) are intentionally rejected by the evaluator: a formula meant for fuzzy evaluation must be parsed in FL/MSFL mode so its connectives are unambiguous. You can also build nodes directly — `StrongConjunction`, `LukNegation`, etc. — instead of parsing.

## `fuzzy_evaluate` — truth degree under a valuation

`fuzzy_evaluate(node, valuation, domain=None, sort_universes=None, tnorm="lukasiewicz")` returns the degree in `[0, 1]`. The `valuation` maps each ground atom's canonical key — its `to_unicode_str()` rendering, e.g. `"P(alice)"` or just `"P"` — to a degree. A missing key raises `KeyError`.

```python
from unicode_fol_kit import MSFLParser, fuzzy_evaluate

fl = MSFLParser(fuzzy=True)

fuzzy_evaluate(fl.parse("P ⊗ ¬P"), {"P": 0.6})           # → 0.0   (strong: max(0, 0.6+0.4−1))
fuzzy_evaluate(fl.parse("P ⊕ ¬P"), {"P": 0.6})           # → 1.0   (strong: min(1, 0.6+0.4))
fuzzy_evaluate(fl.parse("P ∧ ¬P"), {"P": 0.6})           # → 0.4   (weak: min(0.6, 0.4))
fuzzy_evaluate(fl.parse("P ↔ Q"), {"P": 0.6, "Q": 0.7})  # → 0.9   (1 − |0.6 − 0.7|)
fuzzy_evaluate(fl.parse("P → Q"), {"P": 0.8, "Q": 0.5})  # → 0.7   (min(1, 1−0.8+0.5))
```

Quantifiers are the infimum (`∀` = min) and supremum (`∃` = max) over a finite `domain` of constant names; a `SortedQuantifier` ranges over `sort_universes[sort]`:

```python
fuzzy_evaluate(fl.parse("∀x P(x)"), {"P(a)": 0.3, "P(b)": 0.8}, domain={"a", "b"})  # → 0.3 (min)
fuzzy_evaluate(fl.parse("∃x P(x)"), {"P(a)": 0.3, "P(b)": 0.8}, domain={"a", "b"})  # → 0.8 (max)
```

## `fuzzy_is_satisfiable` / `fuzzy_is_valid` / `fuzzy_get_model` (Z3 reals)

Rather than fixing a valuation, you can ask the solver whether *some* (or *every*) assignment reaches a degree. Each ground atom becomes a Z3 `Real` constrained to `[0, 1]`, and the connectives become their piecewise-linear definitions.

- `fuzzy_is_valid(formula)` — `True` iff the degree is `1` under every valuation (it asserts `degree < 1` and checks unsatisfiability).
- `fuzzy_is_satisfiable(formula, threshold=1.0, strict=False)` — `True` iff some valuation reaches `degree >= threshold` (`> threshold` when `strict=True`).
- `fuzzy_get_model(formula, threshold=1.0)` — an atom→degree dict reaching the threshold (plus a `'degree'` entry), or `None`.

```python
from unicode_fol_kit import (
    MSFLParser, fuzzy_is_valid, fuzzy_is_satisfiable, fuzzy_get_model,
)

fl = MSFLParser(fuzzy=True)

fuzzy_is_valid(fl.parse("P ⊕ ¬P"))                       # → True   (degree is 1 for every P)
fuzzy_is_satisfiable(fl.parse("P ⊗ ¬P"), threshold=0.5)  # → False  (strong: max degree is 0)
fuzzy_is_satisfiable(fl.parse("P ∧ ¬P"), threshold=0.5)  # → True   (weak: max degree is 0.5)

m = fuzzy_get_model(fl.parse("P → Q"), threshold=1.0)
sorted(m)         # → ['P', 'Q', 'degree']
m["degree"]       # → 1.0
```

The exact degrees a model assigns to `P` and `Q` are solver-dependent; only the `'degree'` it achieves (here `1.0`) is determined by the threshold.

## The t-norm selector (0.9.0)

Three continuous t-norms fix the **strong** connectives `⊗ ⊕ → ¬ ↔`; the weak `∧ / ∨` stay `min / max` and the quantifiers stay inf / sup regardless. Pass `tnorm=` to `fuzzy_evaluate` and the deciders:

| `tnorm` | `⊗` | `→` | `¬` |
|---|---|---|---|
| `"lukasiewicz"` (default) | `max(0, x+y−1)` | `min(1, 1−x+y)` | `1−x` (involutive) |
| `"godel"` | `min(x, y)` | `1 if x≤y else y` | `1 if x≤0 else 0` |
| `"product"` | `x·y` | `1 if x≤y else y/x` | `1 if x≤0 else 0` |

`get_tnorm(name)` returns the `TNorm` object and `TNORMS` is the registry:

```python
from unicode_fol_kit import MSFLParser, fuzzy_evaluate, get_tnorm, TNORMS

sorted(TNORMS)              # → ['godel', 'lukasiewicz', 'product']
get_tnorm("godel").name    # → 'godel'

fl = MSFLParser(fuzzy=True)
fuzzy_evaluate(fl.parse("P ⊗ Q"), {"P": 0.5, "Q": 0.3}, tnorm="lukasiewicz")  # → 0.0  (max(0, 0.5+0.3−1))
fuzzy_evaluate(fl.parse("P ⊗ Q"), {"P": 0.5, "Q": 0.3}, tnorm="godel")        # → 0.3  (min)
fuzzy_evaluate(fl.parse("P ⊗ Q"), {"P": 0.5, "Q": 0.5}, tnorm="product")      # → 0.25 (x·y)
```

The Łukasiewicz and Gödel t-norms are **piecewise-linear**, so Z3 decides them; `fuzzy_is_valid(…, tnorm="lukasiewicz")` and `fuzzy_is_valid(…, tnorm="godel")` are full decision procedures. The **product** t-norm needs nonlinear arithmetic (`x·y`, `y/x`) that Z3 cannot decide completely, so it is **evaluator-only** — `fuzzy_evaluate(…, tnorm="product")` works, but passing it to the Z3 deciders raises `NotImplementedError`.

### A distinguishing validity: contraction

Contraction `p → (p ⊗ p)` separates the two deciders. Under Gödel it is valid (`⊗` is idempotent `min`, so `p ⊗ p = p` and the implication is always `1`); under Łukasiewicz it fails (at `p = 0.5` the consequent `p ⊗ p = 0`, so the degree is only `0.5`):

```python
from unicode_fol_kit import MSFLParser, fuzzy_is_valid, fuzzy_evaluate

fl = MSFLParser(fuzzy=True)
contraction = fl.parse("P → (P ⊗ P)")

fuzzy_is_valid(contraction, tnorm="godel")        # → True
fuzzy_is_valid(contraction, tnorm="lukasiewicz")  # → False
fuzzy_evaluate(contraction, {"P": 0.5}, tnorm="lukasiewicz")  # → 0.5  (the counterexample)
```

## Quantifier grounding (0.9.0)

The Z3 deciders are propositional, but passing `domain=` (and `sort_universes=` for sorted quantifiers) **grounds** each quantifier over the finite universe first — `∀` folds into a weak-conjunction (min), `∃` into a weak-disjunction (max) — so quantified fuzzy validity and satisfiability become decidable:

```python
from unicode_fol_kit import MSFLParser, fuzzy_is_valid

fl = MSFLParser(fuzzy=True)

# Quantified contraction: Gödel-valid, Łukasiewicz-invalid, over a 2-element domain.
q = fl.parse("∀x (P(x) → (P(x) ⊗ P(x)))")
fuzzy_is_valid(q, domain={"a", "b"}, tnorm="godel")        # → True
fuzzy_is_valid(q, domain={"a", "b"}, tnorm="lukasiewicz")  # → False
```

Without the matching universe a quantifier raises `ValueError` (or, in `fuzzy_evaluate`, when `domain` is omitted).

## Building fuzzy nodes directly

Every connective has a node class — `WeakConjunction`, `WeakDisjunction`, `StrongConjunction`, `StrongDisjunction`, `LukNegation`, `LukImplication`, `LukEquivalence` — that the evaluator and deciders accept without parsing:

```python
from unicode_fol_kit import StrongConjunction, LukNegation, Atom, fuzzy_evaluate

node = StrongConjunction(Atom("P", []), LukNegation(Atom("P", [])))
node.to_unicode_str()             # → 'P ⊗ ¬P'
fuzzy_evaluate(node, {"P": 0.6})  # → 0.0
```
