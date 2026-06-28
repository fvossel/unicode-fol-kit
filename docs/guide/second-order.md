# Second-order logic

`MSFLParser(second_order=True)` adds quantification over **predicate variables** — `∀P φ` and `∃P φ`, where `P` is an uppercase predicate symbol bound by the quantifier — with full (standard) finite-model semantics and a bounded validity / counter-model search.

## Parsing: ∀P / ∃P with inferred arity

Select the mode with the `second_order=True` flag. Object quantifiers keep using lowercase variables, so `∀x` is first-order and `∀P` is second-order. The bound predicate variable's arity is **inferred** from how it is applied in the body: monadic if applied to one argument, n-ary if applied to n, and arity 0 (propositional) if never applied. The arity is recorded on the `SecondOrderQuantifier` node but is not printed, since it is re-inferred on re-parse.

```python
from unicode_fol_kit import MSFLParser

p = MSFLParser(second_order=True).parse

n = p("∀P P(x)")
type(n).__name__   # → 'SecondOrderQuantifier'
n.predicate        # → 'P'
n.arity            # → 1   (applied to one argument: monadic)

p("∀R R(x, y)").arity   # → 2   (binary)
p("∃P (P ∧ Q)").arity   # → 0   (never applied: propositional)
```

Applying a bound predicate at conflicting arities raises `ConflictingArityError`. Second-order formulas reject the first-order export back-ends — `to_z3()` / `to_prover9()` / `to_tptp()` all raise `NotImplementedError`, because second-order quantification is not first-order and not SMT-expressible. Evaluate them with the finite-model semantics below instead.

## Finite-model evaluation: `satisfies_so` / `holds`

`satisfies_so(formula, structure, assignment={}, pred_binding={})` extends classical Tarskian satisfaction with `∀P` / `∃P`: a second-order quantifier ranges over **every** relation of its arity on the structure's finite domain. `holds(formula, structure)` is the convenience wrapper for a closed sentence (empty assignment and empty predicate binding).

```python
from unicode_fol_kit import MSFLParser, Structure, holds

p = MSFLParser(second_order=True).parse
universe = Structure(domain={0, 1})            # a bare 2-element domain

holds(p("∃P ∀x P(x)"), universe)    # → True   (take P = the whole domain)
holds(p("∀P ∃x P(x)"), universe)    # → False  (take P = ∅, the empty relation)

# Leibniz's identity of indiscernibles is expressible and holds:
holds(p("∀x ∀y (∀P (P(x) ↔ P(y)) → x = y)"), universe)   # → True
```

A `∀P` / `∃P` over an arity-`k` predicate on an `n`-element domain enumerates `2 ** (n ** k)` relations — doubly exponential. This is for very small models only (a handful of elements, arity ≤ 2); past `secondorder.MAX_RELATIONS` (~4.2 million) the evaluator raises a `ValueError` rather than hang. For example, evaluating a binary `∀R` over a 6-element domain would require `2 ** (6 ** 2)` relations and is rejected with a clear message.

## Bounded second-order search (new in 0.9.0)

Second-order logic has no complete proof system, and SO validity is not even semi-decidable — so there is no decision procedure and no `to_tptp`-style hand-off to a prover. The four search functions are instead a **bounded finite-model search** (the SO analogue of the first-order model finder): they enumerate finite structures interpreting the formula's *free* symbols over domains `1 .. max_size`, while `satisfies_so` ranges the SO-quantified predicates over every relation. A returned model or counter-model is genuine; "none found up to size N" is bounded evidence, not a proof.

| Function | Returns | Meaning |
|---|---|---|
| `so_find_model(f, max_size=3)` | `Structure` or `None` | a finite structure in which `f` holds |
| `so_find_countermodel(f, max_size=3)` | `Structure` or `None` | a finite structure in which `f` fails (refutes SO validity) |
| `so_is_satisfiable_finite(f, max_size=3)` | `bool` | `f` has a finite model of size ≤ `max_size` |
| `so_is_valid_finite(f, max_size=3)` | `bool` | no finite counter-model found up to `max_size` |

`so_is_valid_finite` is one-sided: `True` is strong evidence of second-order validity (not a proof), while `False` is a genuine refutation whose witness is available from `so_find_countermodel`.

```python
from unicode_fol_kit import (
    MSFLParser, holds,
    so_find_model, so_find_countermodel,
    so_is_satisfiable_finite, so_is_valid_finite,
)

p = MSFLParser(second_order=True).parse

# Standard second-order validities ----------------------------------------
# The complement of any predicate is definable:
so_is_valid_finite(p("∃P ∀x (P(x) ↔ ¬Q(x))"), max_size=3)        # → True
# Leibniz's definition of equality (indiscernibility ⇔ identity):
so_is_valid_finite(p("∀x ∀y (∀P (P(x) ↔ P(y)) ↔ x = y)"), max_size=3)   # → True

# Not valid: "every relation is non-empty" -------------------------------
f = p("∀P ∃x P(x)")
so_is_valid_finite(f, max_size=3)            # → False
cm = so_find_countermodel(f, max_size=3)     # a 1-element Structure
holds(f, cm)                                 # → False  (P = ∅ refutes it)

# Satisfiability ---------------------------------------------------------
so_is_satisfiable_finite(p("∃P ∀x P(x)"), max_size=2)            # → True
# ∃P (∀x P(x) ∧ ∃x ¬P(x)) is contradictory — no finite model:
so_is_satisfiable_finite(p("∃P (∀x P(x) ∧ ∃x ¬P(x))"), max_size=3)   # → False

# Find a witnessing model ------------------------------------------------
g = p("∃P ∀x (P(x) ↔ Q(x))")
m = so_find_model(g, max_size=2)             # a Structure interpreting Q
holds(g, m)                                  # → True
```

`so_find_countermodel(p("∀P ∃x P(x)"))` returns a single-element domain; the empty relation `P = ∅` falsifies `∃x P(x)`, so the structure refutes the sentence. (The exact `repr` of a returned `Structure` depends on the search order over candidate interpretations, so verdicts and `holds(...)` re-checks are the stable things to assert.)

## Building SO nodes directly

The same evaluators and search functions accept a `SecondOrderQuantifier` AST node built without the parser — `SecondOrderQuantifier(type, predicate, arity, formula)`, where `type` is `"∀"` or `"∃"`, `predicate` is the bound predicate name, and `arity` is its arity.

```python
from unicode_fol_kit import so_is_valid_finite
from unicode_fol_kit.fol.nodes import Atom, Not, Iff, Quantifier, Variable
from unicode_fol_kit.fol._so_nodes import SecondOrderQuantifier

x = Variable("x")
# ∃P ∀x (P(x) ↔ ¬Q(x))  — complement-definability, built by hand
node = SecondOrderQuantifier(
    "∃", "P", 1,
    Quantifier("∀", x, Iff(Atom("P", [x]), Not(Atom("Q", [x])))),
)
so_is_valid_finite(node, max_size=3)   # → True
```

`SecondOrderQuantifier` is also exported at the top level as `unicode_fol_kit.SecondOrderQuantifier`.

## Scope

This is second-order **predicate** (relation) quantification with standard semantics over finite models. Quantification over functions, third-order and up, and a complete higher-order type system are out of scope; the lambda layer already supplies higher-order *terms* (`λP. P(x)`), which you beta-reduce and lambda-eliminate before evaluation. The `second_order=True` mode does not combine with sorts, fuzziness, or the modal mode — the constructor rejects an unsupported combination with a `ValueError`. For exporting `∀P` / `∃P` to a higher-order prover, see `unicode_fol_kit.hol` (`to_thf_so` / `to_isabelle_so`), which map them to native HOL predicate quantifiers.
