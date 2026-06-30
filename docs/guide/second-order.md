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

### Arity inference in detail

The arity is inferred from all applications of the bound predicate in its scope. Arity-0 quantifiers are propositional (the bound variable appears alone, without arguments or as part of a Boolean combination):

```python
# Arity-0 examples: P appears as a proposition, not applied to arguments
p("∃P P").arity                  # → 0   (P used as a truth value)
p("∃P (P ∧ Q)").arity           # → 0   (P combined with Q, no arguments)
p("∃P (¬P → Q)").arity          # → 0   (P in negation and implication)

# Arity-1 (monadic): P applied to one argument
p("∀P P(x)").arity              # → 1
p("∀P (P(x) ∧ P(y))").arity    # → 1   (both applications monadic)
p("∀P ∀x P(x)").arity          # → 1

# Arity-2 (binary) and higher
p("∀R R(x, y)").arity          # → 2   (applied to two arguments)
p("∃R (R(a, b) ∨ R(c, d))").arity  # → 2
p("∀P ∃x ∃y P(x, y)").arity    # → 2
```

The node is a frozen dataclass with the fields `type` (`"∀"` / `"∃"`), `predicate`, `arity`, and `formula` (the body). The `repr` shows them all; the renderers and the tree printer show the bound predicate with its arity, and `to_unicode_str` deliberately omits the arity so the parse round-trip stays stable.

```python
n = p("∀P ∃x P(x)")

n.type             # → '∀'
n.formula          # → Quantifier(type='∃', variable=Variable(name='x'), …)
n.to_unicode_str() # → '∀P ∃x P(x)'   (arity not printed)
n.to_latex()       # → '\\forall P\\, \\exists x\\, P(x)'

print(n.tree_str())
# ∀ P/1
# └── ∃ x
#     └── Atom: P
#         └── Variable: x

# The unicode round-trip re-infers the arity, so it is stable:
p(n.to_unicode_str()).arity   # → 1
```

### Nesting and shadowing

Object quantifiers (lowercase variables) thread normally inside an SO binder, and SO binders nest. The arity is inferred only from applications *in scope*: an inner `∀P` / `∃P` over the **same** name shadows the outer one, so the descent stops there; an inner binder over a **different** name is descended into.

```python
# Inner ∃P rebinds P, so the outer P's arity counts only the outer P(x): monadic.
shadow = p("∀P (P(x) → ∃P P(x, y))")
shadow.arity                 # → 1   (outer P: monadic)
shadow.formula.right.arity   # → 2   (inner P: binary, independent binding)

# A different inner name (R) does not stop the scan for P:
p("∀P (∃R R(x, y) → P(x))").arity   # → 1

# Multiple nested binders with different names:
p("∀P ∃Q ∀x (P(x) → Q(x))").arity          # → 1 (P is monadic)
p("∀P ∃Q ∀x (P(x) → Q(x))").formula.arity  # → 1 (Q is monadic)

# Nesting without shadowing: P and Q are quantified independently
both = p("∀P (∃Q ∀x (P(x) → Q(x)))")
both.arity           # → 1   (outer P)
both.formula.arity   # → 1   (inner Q)
```

### Conflicting arities: parse-time errors

Applying one bound predicate at two different arities is a parse-time error, `ConflictingArityError` (a subclass of the parser's `ParsingError`, re-exported from `unicode_fol_kit.fol.msflparser`):

```python
from unicode_fol_kit.fol.msflparser import ConflictingArityError

try:
    p("∀P (P(x) ∧ P(x, y))")          # raises ConflictingArityError
except ConflictingArityError as e:
    print(str(e)[:60])
    # → SYNTAX_ERROR: Second-order predicate variable 'P' is applied
```

The error occurs at parse time, before evaluation, so the formula is never constructed.

### First-order export unsupported

Second-order formulas reject the first-order export back-ends — `to_z3()` / `to_prover9()` / `to_tptp()` all raise `NotImplementedError`, because second-order quantification is not first-order and not SMT-expressible. Evaluate them with the finite-model semantics below, or hand them to a HOL prover via [`to_thf_so` / `to_isabelle_so`](#exporting-to-a-hol-prover).

```python
n = p("∀P P(x)")
try:
    n.to_z3()                          # raises NotImplementedError
except NotImplementedError as e:
    print(str(e)[:47])
    # → Second-order quantification is not first-order

try:
    n.to_prover9()                     # raises NotImplementedError
except NotImplementedError:
    pass

try:
    n.to_tptp()                        # raises NotImplementedError
except NotImplementedError:
    pass
```

### Serialisation and round-tripping

Serialisation survives the second-order field, so SO ASTs round-trip through `to_dict` / `from_dict` (and therefore JSON):

```python
from unicode_fol_kit.fol.nodes import Node

n = p("∀P P(x)")
d = n.to_dict()
d["_type"], d["predicate"], d["arity"]   # → ('SecondOrderQuantifier', 'P', 1)
Node.from_dict(d) == n                    # → True

# Round-trip preserves equivalence
restored = Node.from_dict(d)
restored.to_unicode_str()                # → '∀P P(x)'
restored.arity                           # → 1
```

## Finite-model evaluation: `satisfies_so` / `holds`

`satisfies_so(formula, structure, assignment={}, pred_binding={})` extends classical Tarskian satisfaction with `∀P` / `∃P`: a second-order quantifier ranges over **every** relation of its arity on the structure's finite domain. `holds(formula, structure)` is the convenience wrapper for a closed sentence (empty assignment and empty predicate binding).

### Basic evaluation: closed formulas

```python
from unicode_fol_kit import MSFLParser, Structure, holds

p = MSFLParser(second_order=True).parse
universe = Structure(domain={0, 1})            # a bare 2-element domain

holds(p("∃P ∀x P(x)"), universe)    # → True   (take P = the whole domain)
holds(p("∀P ∃x P(x)"), universe)    # → False  (take P = ∅, the empty relation)

# Leibniz's identity of indiscernibles is expressible and holds:
holds(p("∀x ∀y (∀P (P(x) ↔ P(y)) → x = y)"), universe)   # → True
```

For `∃P ∀x P(x)` on a 2-element domain `{0, 1}`, there exists a relation (the whole domain itself, interpreted as `{(0,), (1,)}`), so the formula holds. For `∀P ∃x P(x)`, take `P = ∅` (the empty relation); then `∃x P(x)` is false since no element satisfies an empty predicate, refuting the outer universal.

### Free object variables: assignment

`holds` is for closed sentences. When the formula has a free *object* variable, pass an `assignment`; when it has a free *predicate* (i.e. one not bound by a `∀P` / `∃P` in the formula and not given by the structure), pass a `pred_binding` mapping that name to a relation — a `frozenset` of argument tuples. Both are threaded immutably through the recursion exactly like a Tarskian assignment.

```python
from unicode_fol_kit import satisfies_so

S = Structure(domain={0, 1})

# free object variable x bound by the assignment; free predicate P bound to {(0,)}:
satisfies_so(p("P(x)"), S, {"x": 0}, {"P": frozenset({(0,)})})   # → True
satisfies_so(p("P(x)"), S, {"x": 1}, {"P": frozenset({(0,)})})   # → False

# holds(f, s) is exactly satisfies_so(f, s, {}, {}):
holds(p("∃P ∀x P(x)"), S) == satisfies_so(p("∃P ∀x P(x)"), S, {}, {})   # → True

# Free variables in the body of a SO quantifier
f = p("∃P P(x)")
satisfies_so(f, S, {"x": 0}, {})   # → True  (take P = {(0,)})
satisfies_so(f, S, {"x": 1}, {})   # → True  (take P = {(1,)})
```

### Free predicates: structure predicates

A *free* (structure-level) predicate is read from the structure's `predicates` tables instead of being quantified. Tables for an arity-`k≥1` predicate may be keyed by the bare name or by the `(name, arity)` pair; the relation is a set of tuples. The SO quantifier then ranges over *every* relation while the free predicate stays fixed:

```python
# Q is a fixed monadic predicate on the domain; P is second-order-quantified.
S = Structure(domain={0, 1}, predicates={"Q": {(0,)}})
holds(p("∃P ∀x (P(x) ↔ Q(x))"), S)   # → True   (take P = Q)

# A binary structure relation R, with an object-level SO-free check:
SR = Structure(domain={0, 1}, predicates={("R", 2): {(0, 1), (1, 0)}})
holds(p("∀x ∀y (R(x, y) → R(y, x))"), SR)   # → True   (R is symmetric here)

# Multiple free predicates in the structure
S_multi = Structure(
    domain={0, 1},
    predicates={"P": {(0,)}, "Q": {(1,)}}
)
holds(p("∃R ∀x (R(x) ↔ (P(x) ∨ Q(x)))"), S_multi)  # → True
```

### Propositional (arity-0) quantifiers

Arity-0 (propositional) bound predicates quantify over a truth value: the two "relations" are `∅` (false) and `{()}` (true). So `∃P P` is satisfiable on any non-empty domain and `∀P P` never holds:

```python
holds(p("∃P P"), Structure(domain={0}))   # → True   (take P = true)
holds(p("∀P P"), Structure(domain={0}))   # → False  (take P = false)

# Propositional quantifiers combined with object quantifiers
holds(p("∀P ∃x P(x)"), Structure(domain={0, 1}))  # → False (P = false refutes)
holds(p("∃P ∀x ¬P(x)"), Structure(domain={0, 1}))  # → True  (P = false works)
```

### Computational limits: MAX_RELATIONS

A `∀P` / `∃P` over an arity-`k` predicate on an `n`-element domain enumerates `2 ** (n ** k)` relations — doubly exponential. This is for very small models only (a handful of elements, arity ≤ 2); past `secondorder.MAX_RELATIONS` (~4.2 million) the evaluator raises a `ValueError` rather than hang. For example, evaluating a binary `∀R` over a 6-element domain would require `2 ** (6 ** 2)` relations and is rejected with a clear message.

```python
from unicode_fol_kit.semantics import secondorder

secondorder.MAX_RELATIONS              # → 4194304   (2 ** 22)

big = Structure(domain=set(range(6)))  # 6 elements
try:
    holds(p("∀R R(x, y)"), big)        # raises ValueError: 2 ** (6 ** 2) relations
except ValueError as e:
    print(str(e)[:46])
    # → Second-order quantifier ∀R/2 over a 6-element

# Safe combinations:
# - Arity 1, up to ~4 million elements (unrealistic)
# - Arity 2, up to ~21 elements (e.g., 21^2 = 441 < 2^22)
# - Arity 3, up to ~12 elements (e.g., 12^3 = 1728 < 2^22)
safe_1 = Structure(domain=set(range(4)))
holds(p("∀P ∀x P(x)"), safe_1)  # → fine

safe_2 = Structure(domain=set(range(20)))
holds(p("∀R ∀x ∃y R(x, y)"), safe_2)  # → fine
```

## Bounded second-order search (new in 0.9.0)

Second-order logic has no complete proof system, and SO validity is not even semi-decidable — so there is no decision procedure and no `to_tptp`-style hand-off to a prover. The four search functions are instead a **bounded finite-model search** (the SO analogue of the first-order model finder): they enumerate finite structures interpreting the formula's *free* symbols over domains `1 .. max_size`, while `satisfies_so` ranges the SO-quantified predicates over every relation. A returned model or counter-model is genuine; "none found up to size N" is bounded evidence, not a proof.

| Function | Returns | Meaning |
|---|---|---|
| `so_find_model(f, max_size=3)` | `Structure` or `None` | a finite structure in which `f` holds |
| `so_find_countermodel(f, max_size=3)` | `Structure` or `None` | a finite structure in which `f` fails (refutes SO validity) |
| `so_is_satisfiable_finite(f, max_size=3)` | `bool` | `f` has a finite model of size ≤ `max_size` |
| `so_is_valid_finite(f, max_size=3)` | `bool` | no finite counter-model found up to `max_size` |

`so_is_valid_finite` is one-sided: `True` is strong evidence of second-order validity (not a proof), while `False` is a genuine refutation whose witness is available from `so_find_countermodel`.

### Standard SO validities and refutations

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

# Distribution over conjunction (Boolean lattice structure)
so_is_valid_finite(p("∀P ∀Q ∀x ((P(x) ∧ Q(x)) ↔ (P(x) ∧ Q(x)))"), max_size=2)  # → True

# Not valid: "every relation is non-empty" -------------------------------
f = p("∀P ∃x P(x)")
so_is_valid_finite(f, max_size=3)            # → False
cm = so_find_countermodel(f, max_size=3)     # a 1-element Structure
holds(f, cm)                                 # → False  (P = ∅ refutes it)
```

### Satisfiability vs validity

```python
# Satisfiability ---------------------------------------------------------
so_is_satisfiable_finite(p("∃P ∀x P(x)"), max_size=2)            # → True

# ∃P (∀x P(x) ∧ ∃x ¬P(x)) is contradictory — no finite model:
so_is_satisfiable_finite(p("∃P (∀x P(x) ∧ ∃x ¬P(x))"), max_size=3)   # → False

# A formula with no model up to size 3 but perhaps larger:
unsure = p("∀P (P(a) → ∃x P(x))")
so_is_satisfiable_finite(unsure, max_size=1)  # → True  (1-element domain)
```

### Finding models

```python
# Find a witnessing model ------------------------------------------------
g = p("∃P ∀x (P(x) ↔ Q(x))")
m = so_find_model(g, max_size=2)             # a Structure interpreting Q
holds(g, m)                                  # → True

# Model for a property: "there is a reflexive relation"
refl = p("∃R ∀x R(x, x)")
m = so_find_model(refl, max_size=2)
print(m.domain)       # → (0,) or (0, 1)
print(m.predicates)   # → {} (R is SO-quantified, not stored)
```

The exact `repr` of a returned `Structure` depends on the search order over candidate interpretations, so verdicts and `holds(...)` re-checks are the stable things to assert.

### Free symbols and universal closure

The search treats every predicate *not* bound by a `∀P` / `∃P` as a free signature symbol to be interpreted by the candidate structure, and free *object* variables are universally closed before the search. So `∃P P(x)` (with `x` free) is searched as `∀x ∃P P(x)` — valid, since for each `x` you may pick the singleton `P = {(x,)}`:

```python
so_is_valid_finite(p("∃P P(x)"), max_size=2)   # → True  (closed over x; pick P = {(x,)})

# Multiple free variables, universally closed
so_is_valid_finite(p("∃P P(x, y)"), max_size=2)  # → True  (searched as ∀x ∀y ∃P P(x, y))
```

### Adjusting max_size

`max_size` is the largest domain searched. Raising it widens the bounded evidence for `so_is_valid_finite` (more counter-model candidates ruled out) and widens the reach of `so_is_satisfiable_finite` / `so_find_model`:

```python
# A countermodel may need a particular size; the witness is re-checkable:
f = p("∀P ∃x P(x)")
so_find_countermodel(f, max_size=1) is not None   # → True   (1-element domain suffices)
so_find_countermodel(f, max_size=5) is not None   # → True   (still found, smaller-first)

# Some formulas require larger domains to even have a model:
sat = p("∃P ∀x (P(x) ↔ x = a)")
so_is_satisfiable_finite(sat, max_size=1)  # → True  (1-element works for *any* model)
```

### Schemas: comprehension and induction

Comprehension — "every first-order-definable subset exists as a predicate" — is a family of standard SO validities; each instance asserts a witnessing `P` extensionally equal to a definable formula:

```python
# P = the complement of Q:
so_is_valid_finite(p("∃P ∀x (P(x) ↔ ¬Q(x))"), max_size=2)              # → True

# P = Q minus S (any Boolean combination of free predicates):
so_is_valid_finite(p("∃P ∀x (P(x) ↔ (Q(x) ∧ ¬S(x)))"), max_size=2)     # → True

# Binary comprehension: the complement of a free relation S:
so_is_valid_finite(p("∃R ∀x ∀y (R(x, y) ↔ ¬S(x, y))"), max_size=2)     # → True

# Three-way composition: P = (Q ∨ R) ∧ ¬S
so_is_valid_finite(p("∃P ∀x (P(x) ↔ ((Q(x) ∨ R(x)) ∧ ¬S(x)))"), max_size=2)  # → True

# Binary comprehension with complex condition
so_is_valid_finite(p("∃R ∀x ∀y (R(x, y) ↔ (S(x, y) ∧ ¬T(x, y)))"), max_size=2)  # → True
```

### The induction axiom

The second-order induction *axiom* — "any `P` containing `zero` and closed under `succ` contains everything" — is **not** valid over arbitrary finite structures (the free `succ` need not reach every element from `zero`), so the search finds a counter-model; it does hold in a one-element structure:

```python
induction = p(
    "∀P ((P(zero) ∧ ∀x (P(x) → P(succ(x)))) → ∀x P(x))"
)
so_is_valid_finite(induction, max_size=3)             # → False  (succ need not be onto)
cm = so_find_countermodel(induction, max_size=3)
holds(induction, cm)                                  # → False

m = so_find_model(induction, max_size=1)              # holds on a 1-element domain
holds(induction, m)                                   # → True

# The reason: on a singleton {0}, succ(0) can be anything; any property including 0
# and closed under succ (for one element) includes all elements trivially.
```

(Note: single-letter lowercase names like `f` parse as object *variables*; a function symbol such as `succ` needs a multi-character lowercase name.)

### End-to-end: parse → search → re-check → export

A complete loop — parse an SO sentence, refute it with the bounded search, re-check the witness, then hand the conjecture to a HOL prover:

```python
from unicode_fol_kit.hol import to_thf_so

f = p("∀P ∃x P(x)")                 # "every relation is non-empty" — not SO-valid
verdict = so_is_valid_finite(f, max_size=3)   # → False
cm = so_find_countermodel(f, max_size=3)      # bounded witness
len(cm.domain)                                # → 1
holds(f, cm)                                  # → False   (re-check: P = ∅ refutes it)

print(to_thf_so(f).splitlines()[-1])
# → thf(goal, conjecture, ( ( ! [P: ( $i > $o )] : ( ? [X: $i] : ( P @ X ) ) ) )).

# Iterating: if you increase max_size, you check a larger search space
verdict_5 = so_is_valid_finite(f, max_size=5)  # → False (still no models)
```

## Building SO nodes directly

The same evaluators and search functions accept a `SecondOrderQuantifier` AST node built without the parser — `SecondOrderQuantifier(type, predicate, arity, formula)`, where `type` is `"∀"` or `"∃"`, `predicate` is the bound predicate name, and `arity` is its arity.

```python
from unicode_fol_kit import so_is_valid_finite, SecondOrderQuantifier
from unicode_fol_kit.fol.nodes import Atom, Not, Iff, Quantifier, Variable, And

x = Variable("x")
# ∃P ∀x (P(x) ↔ ¬Q(x))  — complement-definability, built by hand
node = SecondOrderQuantifier(
    "∃", "P", 1,
    Quantifier("∀", x, Iff(Atom("P", [x]), Not(Atom("Q", [x])))),
)
so_is_valid_finite(node, max_size=3)   # → True
```

### Building more complex nodes

```python
# ∀P ∀Q ∀x ((P(x) ∧ Q(x)) → (P(x) ∨ Q(x)))
P = Atom("P", [x])
Q = Atom("Q", [x])
inner = Quantifier(
    "∀", x,
    Implies(And(P, Q), Or(P, Q))  # (P ∧ Q) → (P ∨ Q)
)
q_binder = SecondOrderQuantifier("∀", "Q", 1, inner)
p_binder = SecondOrderQuantifier("∀", "P", 1, q_binder)

so_is_valid_finite(p_binder, max_size=2)  # → True
```

`SecondOrderQuantifier` is also exported at the top level as `unicode_fol_kit.SecondOrderQuantifier`.

(SO nodes built directly bypass the parser's arity inference, so set `arity` to match the body's applications yourself; the evaluator and the exporters both trust the recorded `arity`.)

## Exporting to a HOL prover

Because there is no first-order export, `unicode_fol_kit.hol` instead embeds an SO formula *directly* into a higher-order logic, where predicate quantification is native: an object variable has type `$i`, a predicate variable of arity `k` has type `$i > … > $i > $o` (arity 0 → `$o`), and each `∀P` / `∃P` becomes a HOL quantifier over a predicate-typed variable. Two emitters are provided — `to_thf_so` (TPTP THF, for Leo-III / Satallax) and `to_isabelle_so` (an Isabelle/HOL theory). Both only *emit*; they run no prover, and SO validity is not semi-decidable, so a sound prover may still fail on a valid goal.

```python
from unicode_fol_kit.hol import to_thf_so, to_isabelle_so

f = p("∃P ∀x (P(x) ↔ ¬Q(x))")     # complement-definability

print(to_thf_so(f))
# % Direct second-order -> HOL embedding (predicate quantifiers are native).
# % Standard (full) second-order semantics in a HOL prover; SOL validity is
# % NOT semi-decidable, so a sound prover may fail to close a valid goal.
# thf(q_decl, type, ( q : ( $i > $o ) )).
# thf(goal, conjecture, ( ( ? [P: ( $i > $o )] : ( ! [X: $i] : ( ( P @ X ) <=> ( ~ ( q @ X ) ) ) ) ) )).
```

### THF export: TPTP for external provers

The free predicate `Q` becomes a declared problem symbol `q`; the bound `P` becomes a THF predicate-typed variable and is *not* declared. Pass `conjecture=False` to emit the formula as an `axiom` instead of a `conjecture`:

```python
"axiom" in to_thf_so(f, conjecture=False)   # → True

# Export multiple formulas as axioms, then a single conjecture
f1 = p("∃P ∀x (P(x) ↔ Q(x))")
f2 = p("∃R ∀x ∀y (R(x, y) ↔ S(x, y))")
f3 = p("∀P ∃x P(x)")  # the query

thf1 = to_thf_so(f1, conjecture=False)
thf2 = to_thf_so(f2, conjecture=False)
thf3 = to_thf_so(f3, conjecture=True)
print(thf1.splitlines()[0])   # % comment line
print("axiom" in thf1)        # → True
print("conjecture" in thf3)   # → True
```

### Isabelle/HOL export

`to_isabelle_so` produces a self-contained theory whose lemma is left `oops` (replace with `by auto` / `sledgehammer`); the predicate type is `i ⇒ … ⇒ i ⇒ bool`:

```python
thy = to_isabelle_so(f, name="Complement")
"theory Complement" in thy        # → True
'consts q :: "i' in thy           # → True   (free predicate Q declared as a const)
"lemma" in thy and "oops" in thy  # → True

# Print a snippet
lines = thy.split('\n')
print('\n'.join(lines[:15]))  # Header and early declarations
```

### Equality and uninterpreted relations

In both exports equality `=` / `≠` is an *uninterpreted* relation (`feq` / `fneq`), not primitive HOL identity — add reflexivity / Leibniz axioms in the prover if you need true identity.

```python
# Exporting a formula with equality
f_eq = p("∀x (x = x)")
thf = to_thf_so(f_eq)
print("feq" in thf)   # → True  (= becomes the uninterpreted feq)

# The exported problem is *not* automatically reflexive
# You would need to add an axiom: ∀x. feq(x, x)
thy_eq = to_isabelle_so(f_eq, name="Reflexivity")
print("feq" in thy_eq)  # → True
```

## Scope

This is second-order **predicate** (relation) quantification with standard semantics over finite models. Quantification over functions, third-order and up, and a complete higher-order type system are out of scope; the lambda layer already supplies higher-order *terms* (`λP. P(x)`), which you beta-reduce and lambda-eliminate before evaluation. The `second_order=True` mode does not combine with sorts, fuzziness, or the modal mode — the constructor rejects an unsupported combination with a `ValueError`. For exporting `∀P` / `∃P` to a higher-order prover, see `unicode_fol_kit.hol` (`to_thf_so` / `to_isabelle_so`), which map them to native HOL predicate quantifiers.

### Combining second-order with other modes

```python
# These combinations raise ValueError:
try:
    MSFLParser(second_order=True, many_sorted=True)  # raises ValueError
except ValueError as e:
    print("unsupported combination" in str(e))  # → True

try:
    MSFLParser(second_order=True, fuzzy=True)  # raises ValueError
except ValueError:
    pass

try:
    MSFLParser(second_order=True, modal=True)  # raises ValueError
except ValueError:
    pass

# But first-order quantifiers, lambdas, and standard logic connectives work fine:
p = MSFLParser(second_order=True).parse
p("∀x ∃P P(x)")           # ✓ mix of ∀x and ∃P
p("(λx. x)(a) → ∀P P")    # ✓ lambda terms
p("∀P (P ↔ (Q ∧ R))")     # ✓ Boolean connectives
```

