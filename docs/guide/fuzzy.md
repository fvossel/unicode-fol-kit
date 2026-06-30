# Fuzzy (Łukasiewicz / BL) logic

The fuzzy layer interprets the Łukasiewicz / basic-logic (BL) connectives over the real interval `[0, 1]`: `fuzzy_evaluate` computes a truth **degree** under a valuation, and `fuzzy_is_satisfiable` / `fuzzy_is_valid` / `fuzzy_get_model` decide formulas via Z3 reals. Version 0.9.0 adds a t-norm selector (Łukasiewicz / Gödel / product) and quantifier grounding so quantified fuzzy validity is decidable.

Everything on this page is imported from the top-level package:

```python
from unicode_fol_kit import (
    MSFLParser,
    fuzzy_evaluate, fuzzy_is_valid, fuzzy_is_satisfiable, fuzzy_get_model,
    get_tnorm, TNORMS, TNorm,
    WeakConjunction, WeakDisjunction,
    StrongConjunction, StrongDisjunction,
    LukNegation, LukImplication, LukEquivalence,
    Atom,
)
```

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

```python
from unicode_fol_kit import MSFLParser

fl = MSFLParser(fuzzy=True)                       # single-sorted FL
ms = MSFLParser(many_sorted=True, fuzzy=True)     # many-sorted MSFL

fl.parse("P ⊗ (Q → R)").to_unicode_str()          # → 'P ⊗ (Q → R)'
type(fl.parse("P ⊗ Q")).__name__                  # → 'StrongConjunction'
type(fl.parse("P ∧ Q")).__name__                  # → 'WeakConjunction'
type(fl.parse("¬P")).__name__                     # → 'LukNegation'

ms.parse("∀x:Person Tall(x)").to_unicode_str()    # → '∀x:Person Tall(x)'
ms.parse("Tall(alice:Person)").to_unicode_str()   # → 'Tall(alice:Person)'
```

Parsing a classical boolean formula in fuzzy mode (or feeding a classically parsed formula to the evaluator) is the one common mistake — the connective node carries no Łukasiewicz reading and the evaluator rejects it:

```python
from unicode_fol_kit import MSFLParser, fuzzy_evaluate

classical = MSFLParser()                            # default: classical FOL
fuzzy_evaluate(classical.parse("P ∧ Q"), {"P": 0.5, "Q": 0.5})
# raises TypeError: Classical connective And is not valid in fuzzy input …
```

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

### Weak vs strong, side by side

The weak `∧ / ∨` are the lattice `min / max`; the strong `⊗ / ⊕` are the t-norm and its t-conorm. They coincide only at the extremes — in the middle the strong pair is "more demanding" (`⊗ ≤ ∧`) and "more permissive" (`⊕ ≥ ∨`):

```python
v = {"P": 0.6, "Q": 0.7}
fuzzy_evaluate(fl.parse("P ∧ Q"), v)             # → 0.6   weak conjunction = min
round(fuzzy_evaluate(fl.parse("P ⊗ Q"), v), 10)  # → 0.3   strong  = max(0, 0.6+0.7−1)
fuzzy_evaluate(fl.parse("P ∨ Q"), v)             # → 0.7   weak disjunction = max
fuzzy_evaluate(fl.parse("P ⊕ Q"), v)             # → 1.0   strong  = min(1, 0.6+0.7)
```

> Many Łukasiewicz degrees are not exactly representable in binary floating point: `0.6 + 0.7 − 1` evaluates to `0.2999999999999998`, so the examples above wrap a noisy result in `round(..., 10)`. The underlying arithmetic is exact; only the display is rounded.

### Negation and implication

Łukasiewicz negation `1 − x` is **involutive** (`¬¬P = P`), and the implication is the residuum of `⊗`:

```python
round(fuzzy_evaluate(fl.parse("¬P"), {"P": 0.3}), 10)    # → 0.7
round(fuzzy_evaluate(fl.parse("¬¬P"), {"P": 0.3}), 10)   # → 0.3   (involutive)

fuzzy_evaluate(fl.parse("P → Q"), {"P": 0.4, "Q": 0.9})  # → 1.0   (x ≤ y ⇒ implication is 1)
fuzzy_evaluate(fl.parse("P → Q"), {"P": 0.9, "Q": 0.4})  # → 0.5   (min(1, 1−0.9+0.4))
```

### A missing atom raises `KeyError`

Every ground atom that appears must have a degree in the valuation:

```python
fuzzy_evaluate(fl.parse("P ⊗ Q"), {"P": 0.6})
# raises KeyError: "No degree for ground atom 'Q' in the valuation. …"
```

### Quantifiers (inf / sup over a finite domain)

Quantifiers are the infimum (`∀` = min) and supremum (`∃` = max) over a finite `domain` of constant names; a `SortedQuantifier` ranges over `sort_universes[sort]`:

```python
fuzzy_evaluate(fl.parse("∀x P(x)"), {"P(a)": 0.3, "P(b)": 0.8}, domain={"a", "b"})  # → 0.3 (min)
fuzzy_evaluate(fl.parse("∃x P(x)"), {"P(a)": 0.3, "P(b)": 0.8}, domain={"a", "b"})  # → 0.8 (max)
```

For sorted quantifiers, pass `sort_universes`. The bound variable is grounded to a **bare** constant, so the valuation keys drop the sort annotation (`Tall(alice)`, not `Tall(alice:Person)`):

```python
ms = MSFLParser(many_sorted=True, fuzzy=True)
val = {"Tall(alice)": 0.7, "Tall(carol)": 0.4}
uni = {"Person": {"alice", "carol"}}

fuzzy_evaluate(ms.parse("∀x:Person Tall(x)"), val, sort_universes=uni)  # → 0.4 (inf)
fuzzy_evaluate(ms.parse("∃x:Person Tall(x)"), val, sort_universes=uni)  # → 0.7 (sup)
```

Omitting the universe for a quantifier raises `ValueError`:

```python
fuzzy_evaluate(fl.parse("∀x P(x)"), {"P(a)": 0.5})
# raises ValueError: Evaluating an unsorted Quantifier requires a 'domain' …
```

## The three t-norms

A *t-norm* `T` fixes the **strong** connectives `⊗ ⊕ → ¬ ↔`; the weak `∧ / ∨` stay `min / max` and the quantifiers stay inf / sup regardless of `tnorm`. Three continuous t-norms ship — their ordinal sums generate every continuous t-norm (Mostert–Shields):

| `tnorm` | `⊗` | `⊕` | `→` | `¬` |
|---|---|---|---|---|
| `"lukasiewicz"` (default) | `max(0, x+y−1)` | `min(1, x+y)` | `min(1, 1−x+y)` | `1−x` (involutive) |
| `"godel"` | `min(x, y)` | `max(x, y)` | `1 if x≤y else y` | `1 if x≤0 else 0` |
| `"product"` | `x·y` | `x+y−x·y` | `1 if x≤y else y/x` | `1 if x≤0 else 0` |

Pass `tnorm=` to `fuzzy_evaluate` and to the deciders. The strong conjunction `⊗` is the clearest discriminator — same inputs, three answers:

```python
from unicode_fol_kit import MSFLParser, fuzzy_evaluate

fl = MSFLParser(fuzzy=True)
v = {"P": 0.5, "Q": 0.3}

fuzzy_evaluate(fl.parse("P ⊗ Q"), v, tnorm="lukasiewicz")  # → 0.0   max(0, 0.5+0.3−1)
fuzzy_evaluate(fl.parse("P ⊗ Q"), v, tnorm="godel")        # → 0.3   min(x, y)
fuzzy_evaluate(fl.parse("P ⊗ Q"), {"P": 0.5, "Q": 0.5}, tnorm="product")  # → 0.25  x·y
```

The implication `→` and equivalence `↔` differ too:

```python
w = {"P": 0.8, "Q": 0.4}
fuzzy_evaluate(fl.parse("P → Q"), w, tnorm="lukasiewicz")  # → 0.6    min(1, 1−0.8+0.4)
fuzzy_evaluate(fl.parse("P → Q"), w, tnorm="godel")        # → 0.4    1 if x≤y else y
fuzzy_evaluate(fl.parse("P → Q"), w, tnorm="product")      # → 0.5    1 if x≤y else y/x

e = {"P": 0.6, "Q": 0.7}
fuzzy_evaluate(fl.parse("P ↔ Q"), e, tnorm="lukasiewicz")          # → 0.9    1 − |x−y|
fuzzy_evaluate(fl.parse("P ↔ Q"), e, tnorm="godel")                # → 0.6    min(x→y, y→x)
round(fuzzy_evaluate(fl.parse("P ↔ Q"), e, tnorm="product"), 10)   # → 0.8571428571
```

### Negation: Łukasiewicz vs Gödel/product

Only Łukasiewicz negation is *involutive*. The Gödel and product negations are the residual "`x → 0`": `0` whenever `x > 0`, so they collapse all positive degrees:

```python
fuzzy_evaluate(fl.parse("¬P"), {"P": 0.3}, tnorm="godel")    # → 0.0   (any x>0 ↦ 0)
fuzzy_evaluate(fl.parse("¬P"), {"P": 0.0}, tnorm="godel")    # → 1.0
fuzzy_evaluate(fl.parse("¬¬P"), {"P": 0.3}, tnorm="godel")   # → 1.0   (NOT involutive!)
fuzzy_evaluate(fl.parse("¬¬P"), {"P": 0.0}, tnorm="godel")   # → 0.0
```

### `get_tnorm`, `TNORMS`, and the `TNorm` object

`get_tnorm(name)` returns the `TNorm` object and `TNORMS` is the registry dict. Each `TNorm` exposes the raw scalar operations `conj` / `disj` / `impl` / `neg` and the derived `equiv` — handy for plotting a connective or sanity-checking a hand calculation:

```python
from unicode_fol_kit import get_tnorm, TNORMS

sorted(TNORMS)                       # → ['godel', 'lukasiewicz', 'product']
get_tnorm("godel").name              # → 'godel'
get_tnorm("godel") is TNORMS["godel"]  # → True   (the registry instance)

luk = get_tnorm("lukasiewicz")
luk.conj(0.6, 0.7)                   # → 0.3000000000000... (max(0, x+y−1))
luk.disj(0.6, 0.7)                   # → 1.0                (min(1, x+y))
luk.impl(0.8, 0.5)                   # → 0.7                (min(1, 1−x+y))
luk.neg(0.3)                         # → 0.7
luk.equiv(0.6, 0.7)                  # → 0.9                (min(x→y, y→x))

god = get_tnorm("godel")
god.impl(0.3, 0.5)                   # → 1.0   (x ≤ y)
god.impl(0.8, 0.5)                   # → 0.5   (else y)
god.neg(0.4)                         # → 0.0
```

An unknown name raises `ValueError`:

```python
get_tnorm("zadeh")
# raises ValueError: unknown t-norm 'zadeh'; use one of ['godel', 'lukasiewicz', 'product'].
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

### Thresholds and `strict`

The threshold is the bar the degree must clear. `strict=True` turns `>=` into `>`, which matters exactly at the boundary — the weak `P ∧ ¬P` peaks at `0.5`, so it reaches `0.5` but never *exceeds* it:

```python
fuzzy_is_satisfiable(fl.parse("P ∧ ¬P"), threshold=0.5)               # → True   (degree = 0.5 ≥ 0.5)
fuzzy_is_satisfiable(fl.parse("P ∧ ¬P"), threshold=0.5, strict=True)  # → False  (no valuation > 0.5)
fuzzy_is_satisfiable(fl.parse("P ∧ ¬P"))                              # → False  (default threshold 1.0)
fuzzy_is_satisfiable(fl.parse("P ⊗ Q"), threshold=0.3)               # → True
```

### A partial-degree model

Ask `fuzzy_get_model` for a witness that reaches a partial threshold; the returned `'degree'` meets it exactly when the solver can hit the bound, and is `None` when the threshold is unreachable:

```python
m = fuzzy_get_model(fl.parse("P ⊗ Q"), threshold=0.5)
sorted(m)          # → ['P', 'Q', 'degree']
m["degree"]        # → 0.5    (P + Q − 1 ≥ 0.5 has solutions, e.g. P = Q = 0.75)

fuzzy_get_model(fl.parse("P ⊗ ¬P"), threshold=1.0)   # → None  (max degree is 0)
```

### Validity differs by t-norm

The same formula can be valid under one t-norm and not another. Excluded middle `P ⊕ ¬P` is Łukasiewicz-valid (bounded sum reaches `1`) but Gödel-invalid (Gödel `⊕` is `max`, which only reaches `1` if `P` or `¬P` is `1`):

```python
fuzzy_is_valid(fl.parse("P ⊕ ¬P"), tnorm="lukasiewicz")  # → True
fuzzy_is_valid(fl.parse("P ⊕ ¬P"), tnorm="godel")        # → False

# Self-implication and double-negation introduction are robust:
fuzzy_is_valid(fl.parse("P → P"), tnorm="lukasiewicz")   # → True
fuzzy_is_valid(fl.parse("P → P"), tnorm="godel")         # → True

# Involution P ↔ ¬¬P holds only for Łukasiewicz:
fuzzy_is_valid(fl.parse("P ↔ ¬¬P"), tnorm="lukasiewicz")  # → True
fuzzy_is_valid(fl.parse("P ↔ ¬¬P"), tnorm="godel")        # → False
```

Modus ponens and a De Morgan law survive both deciders:

```python
fuzzy_is_valid(fl.parse("(P ⊗ (P → Q)) → Q"), tnorm="lukasiewicz")  # → True
fuzzy_is_valid(fl.parse("(P ⊗ (P → Q)) → Q"), tnorm="godel")        # → True
fuzzy_is_valid(fl.parse("¬(P ⊗ Q) ↔ (¬P ⊕ ¬Q)"), tnorm="lukasiewicz")  # → True
```

### The product t-norm is evaluator-only

The Łukasiewicz and Gödel t-norms are **piecewise-linear**, so Z3 decides them; `fuzzy_is_valid(…, tnorm="lukasiewicz")` and `fuzzy_is_valid(…, tnorm="godel")` are full decision procedures. The **product** t-norm needs nonlinear arithmetic (`x·y`, `y/x`) that Z3 cannot decide completely, so it is **evaluator-only** — `fuzzy_evaluate(…, tnorm="product")` works, but passing it to the Z3 deciders raises `NotImplementedError`:

```python
fuzzy_evaluate(fl.parse("P → Q"), {"P": 0.8, "Q": 0.4}, tnorm="product")  # → 0.5  (works)

fuzzy_is_satisfiable(fl.parse("P → Q"), tnorm="product")
# raises NotImplementedError: z3_fuzzy: the product t-norm needs nonlinear real arithmetic …
```

An unknown name still raises `ValueError` in the decider path:

```python
fuzzy_is_valid(fl.parse("P ⊕ ¬P"), tnorm="zadeh")
# raises ValueError: z3_fuzzy: unknown t-norm 'zadeh' (use lukasiewicz / godel).
```

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

Grounded satisfiability and models work the same way — the model keys are the grounded ground atoms:

```python
from unicode_fol_kit import fuzzy_is_satisfiable, fuzzy_get_model

fl = MSFLParser(fuzzy=True)

# ∃ reaches a high degree iff some instance can:
fuzzy_is_satisfiable(fl.parse("∃x P(x)"), threshold=0.9, domain={"a", "b"})  # → True

# A model for ∀x (P(x) ⊕ ¬P(x)) at degree 1 — one degree per grounded atom:
m = fuzzy_get_model(fl.parse("∀x (P(x) ⊕ ¬P(x))"), threshold=1.0, domain={"a", "b"})
sorted(m)      # → ['P(a)', 'P(b)', 'degree']
m["degree"]    # → 1.0
```

Sorted quantifiers ground over `sort_universes` instead:

```python
ms = MSFLParser(many_sorted=True, fuzzy=True)
qs = ms.parse("∀x:Person (Tall(x) → (Tall(x) ⊗ Tall(x)))")

fuzzy_is_valid(qs, sort_universes={"Person": {"a", "b"}}, tnorm="godel")        # → True
fuzzy_is_valid(qs, sort_universes={"Person": {"a", "b"}}, tnorm="lukasiewicz")  # → False
```

Without the matching universe a quantifier raises `ValueError` (in the deciders) or, in `fuzzy_evaluate`, when `domain` is omitted:

```python
fuzzy_is_valid(fl.parse("∀x P(x)"), tnorm="lukasiewicz")
# raises ValueError: Grounding an unsorted Quantifier requires a non-empty 'domain'.
```

## Building fuzzy nodes directly

Every connective has a node class — `WeakConjunction`, `WeakDisjunction`, `StrongConjunction`, `StrongDisjunction`, `LukNegation`, `LukImplication`, `LukEquivalence` — that the evaluator and deciders accept without parsing. Each binary class takes `(left, right)`; `LukNegation` takes one operand; an atom is `Atom(predicate, args)`:

```python
from unicode_fol_kit import (
    StrongConjunction, StrongDisjunction, LukNegation, LukImplication,
    Atom, fuzzy_evaluate, fuzzy_is_valid,
)

node = StrongConjunction(Atom("P", []), LukNegation(Atom("P", [])))
node.to_unicode_str()             # → 'P ⊗ ¬P'
fuzzy_evaluate(node, {"P": 0.6})  # → 0.0

# Build excluded-middle and decide it without ever parsing a string:
em = StrongDisjunction(Atom("P", []), LukNegation(Atom("P", [])))
em.to_unicode_str()                       # → 'P ⊕ ¬P'
fuzzy_is_valid(em, tnorm="lukasiewicz")   # → True

# Predicate atoms carry their argument terms (use the constant name as the arg key):
impl = LukImplication(Atom("P", []), Atom("Q", []))
fuzzy_evaluate(impl, {"P": 0.9, "Q": 0.4})  # → 0.5
```

## End-to-end: a small fuzzy rule base

Parse → evaluate → solve, in one scenario. A diagnostic rule says that strong *fever* together with a *cough* implies elevated *risk*; we both score it under a fixed reading and ask whether the antecedent can reach a target degree.

```python
from unicode_fol_kit import MSFLParser, fuzzy_evaluate, fuzzy_is_satisfiable, fuzzy_get_model

fl = MSFLParser(fuzzy=True)
rule = fl.parse("(Fever ⊗ Cough) → Risk")
rule.to_unicode_str()             # → 'Fever ⊗ Cough → Risk'

# Score the rule under one patient's degrees (Łukasiewicz default):
reading = {"Fever": 0.9, "Cough": 0.8, "Risk": 0.4}
round(fuzzy_evaluate(rule, reading), 10)   # → 0.7  antecedent = max(0, 1.7−1) = 0.7; min(1, 1−0.7+0.4)

# Can the antecedent Fever ⊗ Cough alone reach 0.7?
fuzzy_is_satisfiable(fl.parse("Fever ⊗ Cough"), threshold=0.7)  # → True

# Recover a witness valuation that attains it:
m = fuzzy_get_model(fl.parse("Fever ⊗ Cough"), threshold=0.7)
sorted(m)        # → ['Cough', 'Fever', 'degree']
m["degree"]      # → 0.7
```
