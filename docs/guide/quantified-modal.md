# Quantified Modal Logic

Combining the modalities with `∀x` / `∃x` gives **quantified modal logic** (QML), where validity turns on how the individual domain varies between worlds. `unicode-fol-kit` handles QML both *semantically* (a `KripkeModel` with per-world domains and an actualist `satisfies_modal`) and via two **shallow embeddings** in the Benzmüller style — a first-order one decided by Z3, and a higher-order one exported as TPTP THF.

The kit gives you four views of the same logic, and they are designed to agree:

| Tool | What it is | Verdict |
| --- | --- | --- |
| `satisfies_modal` | brute-force evaluator over an *explicit* finite model | ground truth + countermodels |
| `qml_is_valid` | first-order shallow embedding → **Z3** | sound, bounded-incomplete |
| `resolution.prove` | the qml embedding lowered further and saturated in-process | sound, bounded-incomplete |
| `to_thf_modal` / `to_isabelle_modal` | higher-order shallow embedding → external prover | sound (you run the prover) |

## Building modal formulas as nodes

Every example below builds the AST directly from `unicode_fol_kit`, so no parser is involved. A modal formula mixes the modal nodes `Box` / `Diamond` with the ordinary first-order nodes `Quantifier` / `Atom` / `Variable`. The Barcan formula `◇∃x A(x) → ∃x ◇A(x)` and its converse are the standard litmus tests for the domain regime, and the kit exports them ready-made as `BARCAN` / `CONVERSE_BARCAN`:

```python
from unicode_fol_kit import (
    Box, Diamond, Quantifier, Atom, Variable, Implies,
    BARCAN, CONVERSE_BARCAN,
)

x = Variable("x")
A = lambda t: Atom("A", [t])

# Barcan formula:  ◇∃x A(x) → ∃x ◇A(x)
bf  = Implies(Diamond(Quantifier("∃", x, A(x))),
              Quantifier("∃", x, Diamond(A(x))))
# Converse Barcan: ∃x ◇A(x) → ◇∃x A(x)
cbf = Implies(Quantifier("∃", x, Diamond(A(x))),
              Diamond(Quantifier("∃", x, A(x))))

bf  == BARCAN           # → True
cbf == CONVERSE_BARCAN  # → True
```

`Quantifier(type, variable, formula)` takes `"∃"` / `"exists"` (or `"∀"` / `"forall"`) as its type; the bound variable is a `Variable`. `Box` and `Diamond` each wrap a single subformula.

You rarely have to spell the AST out by hand: `MSFLParser(modal=True)` parses the Unicode surface form, quantifiers and modalities together, and produces exactly the same node. Parse it and feed it straight into the validity checker:

```python
from unicode_fol_kit import MSFLParser, qml_is_valid

mp = MSFLParser(modal=True)
parsed = mp.parse("◇∃x A(x) → ∃x ◇A(x)")

parsed == BARCAN                       # → True
qml_is_valid(parsed, mode="constant")  # → True
```

### Parsing real-world scenarios

Beyond the canonical Barcan tests, you can parse natural multi-quantifier and multi-predicate formulas:

```python
# "Someone must necessarily satisfy a property"
f1 = mp.parse("∃x □P(x)")
f1.to_unicode_str()  # → '∃x □P(x)'

# "A property must hold of everyone"
f2 = mp.parse("□∀x Q(x)")
f2.to_unicode_str()  # → '□∀x Q(x)'

# "Everyone can possibly know something"
f3 = mp.parse("∀x ◇∃y Knows(x, y)")
f3.to_unicode_str()  # → '∀x ◇∃y Knows(x, y)'

# "If something is necessary, it can't be avoidable"
f4 = mp.parse("□P(a) → ¬◇¬P(a)")
f4.to_unicode_str()  # → '□P(a) → ¬◇¬P(a)'

# "Someone who exists possibly satisfies a relational property"
f5 = mp.parse("∃x (∃y Loves(x, y) ∧ ◇Happy(x))")
f5.to_unicode_str()  # → '∃x (∃y Loves(x, y) ∧ ◇Happy(x))'
```

### Comparing modal quantifier orders

The **order** of quantifiers matters crucially. Swapping `∃x` and `□` can change validity:

```python
# Existential inside the box: some specific thing is necessarily P
ex_box = Quantifier("∃", x, Box(A(x)))

# Box around existential: necessarily, there exists something that is P
box_ex = Box(Quantifier("∃", x, A(x)))

# Compare their validity across regimes
qml_is_valid(ex_box, mode="constant")      # → True
qml_is_valid(box_ex, mode="constant")      # → True

qml_is_valid(ex_box, mode="increasing")    # → True   (existing objects stay)
qml_is_valid(box_ex, mode="increasing")    # → False  (new objects might appear)

# Their equivalence depends on the regime
qml_equivalent(ex_box, box_ex, mode="constant")    # → True
qml_equivalent(ex_box, box_ex, mode="increasing")  # → False
```

There is a *second* Barcan pair phrased with `□`/`∀` rather than `◇`/`∃` — the **box Barcan** `∀x □A(x) → □∀x A(x)` and **box Converse Barcan** `□∀x A(x) → ∀x □A(x)`. They are the contrapositive duals of `BARCAN` / `CONVERSE_BARCAN`, so the regime correspondence is mirrored (box-BF ⇔ decreasing, box-CBF ⇔ increasing). You build them the same way:

```python
from unicode_fol_kit import qml_is_valid

box_bf  = Implies(Quantifier("∀", x, Box(A(x))),
                  Box(Quantifier("∀", x, A(x))))   # ∀x □A(x) → □∀x A(x)
box_cbf = Implies(Box(Quantifier("∀", x, A(x))),
                  Quantifier("∀", x, Box(A(x))))   # □∀x A(x) → ∀x □A(x)

qml_is_valid(box_bf,  mode="decreasing")  # → True   (box-BF ⇔ decreasing)
qml_is_valid(box_bf,  mode="increasing")  # → False
qml_is_valid(box_cbf, mode="increasing")  # → True   (box-CBF ⇔ increasing)
qml_is_valid(box_cbf, mode="decreasing")  # → False
qml_is_valid(box_bf,  mode="constant")    # → True   (constant ⇒ both)
qml_is_valid(box_cbf, mode="constant")    # → True
```

## Semantics: per-world domains and actualist quantifiers

Build a `KripkeModel` with per-world object domains — `domains={w: {...}}` for a varying domain, or `domain={...}` for a single constant domain shared by every world. `satisfies_modal(φ, model, world)` then interprets `∀x` / `∃x` **actualistically**: at a world `w` they range over `D_w`, the objects that exist *at that world*. This is the ground truth against which the embeddings are cross-checked.

`model.domain_at(w)` shows the live domain of a world; the constant-domain shorthand `domain={...}` simply assigns that same set to every world:

```python
from unicode_fol_kit.semantics.kripke import KripkeModel

varying  = KripkeModel(worlds={0, 1}, domains={0: {"a"}, 1: {"a", "b"}})
constant = KripkeModel(worlds={0, 1}, domain={"a", "b"})

sorted(varying.domain_at(0))    # → ['a']
sorted(varying.domain_at(1))    # → ['a', 'b']
sorted(constant.domain_at(0))   # → ['a', 'b']
sorted(constant.domain_at(1))   # → ['a', 'b']
```

### Building models with valuations

Attach a valuation (truth assignment for atoms) to make concrete evaluations:

```python
from unicode_fol_kit import satisfies_modal, Variable, Atom, Quantifier
from unicode_fol_kit.semantics.kripke import KripkeModel

x = Variable("x")
A = lambda t: Atom("A", [t])

# Model where only world 1 has A(b)
m = KripkeModel(
    worlds={0, 1},
    relations={"alethic": {(0, 1)}},
    domains={0: {"a"}, 1: {"a", "b"}},
    valuation={0: {"A(a)"}, 1: {"A(a)", "A(b)"}}
)

# Check what's true at each world
from unicode_fol_kit import Constant
a = Constant("a")
b = Constant("b")
satisfies_modal(A(a), m, 0)  # → True   (A(a) holds at world 0)
satisfies_modal(A(b), m, 0)  # → False  (b does not exist at world 0)
satisfies_modal(A(b), m, 1)  # → True   (A(b) holds at world 1)

# Existential quantifiers range over the actualist domain
# At world 0, ∃x A(x) is true because A(a) is true and a ∈ D_0
satisfies_modal(Quantifier("∃", x, A(x)), m, 0)  # → True

# At world 1, both a and b witness the existential
satisfies_modal(Quantifier("∃", x, A(x)), m, 1)  # → True
```

### Multi-world, multi-predicate models

Build realistic scenarios with multiple predicates and connectivity:

```python
# A three-world model with growing domain
model = KripkeModel(
    worlds={0, 1, 2},
    relations={"alethic": {(0, 1), (1, 2), (0, 2)}},  # path 0→1→2, plus shortcut
    domains={0: {"alice"}, 1: {"alice", "bob"}, 2: {"alice", "bob", "charlie"}},
    valuation={
        0: {"Person(alice)", "Happy(alice)"},
        1: {"Person(alice)", "Person(bob)", "Happy(bob)"},
        2: {"Person(alice)", "Person(bob)", "Person(charlie)", "Happy(charlie)"}
    }
)

Person = lambda t: Atom("Person", [t])
Happy = lambda t: Atom("Happy", [t])

# At world 0, everyone who exists is happy
satisfies_modal(
    Quantifier("∀", x, Implies(Person(x), Happy(x))),
    model, 0
)  # → True

# But "everyone" in world 0 is just alice
satisfies_modal(Quantifier("∀", x, Person(x)), model, 0)  # → True (only alice exists)

# At world 1, not everyone is necessarily happy yet
satisfies_modal(
    Quantifier("∀", x, Implies(Person(x), Happy(x))),
    model, 1
)  # → True  (alice and bob are both happy here)

# "It's possible that everyone is a person" — true at 0, since worlds 1,2 have all
satisfies_modal(
    Diamond(Quantifier("∀", x, Person(x))),
    model, 0
)  # → True
```

A model built **without** domains is the purely propositional fragment of {doc}`modal`; asking it to evaluate an object quantifier is an error rather than a silent default:

```python
from unicode_fol_kit import satisfies_modal, Quantifier, Variable, Atom

x = Variable("x")
prop_only = KripkeModel(worlds={0}, valuation={0: {"A(a)"}})
satisfies_modal(Quantifier("∃", x, Atom("A", [x])), prop_only, 0)
# raises ValueError: this Kripke model has no object domains …
```

### Barcan fails when domains grow

The Barcan formula is valid under constant domains but **fails when domains grow**, because an object can appear only in a successor world:

```python
from unicode_fol_kit import BARCAN, satisfies_modal
from unicode_fol_kit.semantics.kripke import KripkeModel

rel = {"alethic": {(0, 1)}}   # world 0 sees world 1

constant = KripkeModel(
    worlds={0, 1}, relations=rel,
    valuation={1: {"A(b)"}}, domain={"a", "b"},
)
increasing = KripkeModel(
    worlds={0, 1}, relations=rel,
    valuation={1: {"A(b)"}}, domains={0: {"a"}, 1: {"a", "b"}},
)

satisfies_modal(BARCAN, constant, 0)     # → True
satisfies_modal(BARCAN, increasing, 0)   # → False
```

Under `increasing`, `b` exists only at world 1: `◇∃x A(x)` holds at world 0 (a `b` with `A(b)` is reachable), but `∃x ◇A(x)` fails because no object *in `D_0`* possibly satisfies `A`. You can watch the two antecedent/consequent halves come apart directly:

```python
ant = Diamond(Quantifier("∃", x, Atom("A", [x])))   # ◇∃x A(x)
con = Quantifier("∃", x, Diamond(Atom("A", [x])))   # ∃x ◇A(x)

satisfies_modal(ant, increasing, 0)   # → True   (a b with A(b) is reachable)
satisfies_modal(con, increasing, 0)   # → False  (no object in D_0 possibly has A)
```

This asymmetry shows why Barcan breaks: the antecedent escapes the domain restriction by quantifying within the modal operator, while the consequent must quantify over D_0.

`satisfies_modal` is also the way to obtain a definite countermodel — it is a complete brute-force oracle over the explicit model.

### Converse Barcan fails when domains shrink

The Converse Barcan is the mirror image: it holds under constant domains but **fails when domains shrink** along the accessibility relation. Put `b` in `D_0` with `A(b)` true at the successor world 1, but drop `b` from `D_1`:

```python
from unicode_fol_kit import CONVERSE_BARCAN

decreasing = KripkeModel(
    worlds={0, 1}, relations=rel,
    valuation={1: {"A(b)"}}, domains={0: {"a", "b"}, 1: {"a"}},
)

satisfies_modal(CONVERSE_BARCAN, decreasing, 0)   # → False
satisfies_modal(BARCAN,          decreasing, 0)   # → True   (BF survives shrinking)
```

Here `∃x ◇A(x)` is true at world 0 (the object `b`, which exists at 0, has `A` at the reachable world 1), but `◇∃x A(x)` is false: the only successor is world 1, whose actualist domain `D_1 = {a}` contains no `A`-witness because `b` no longer exists there.

```python
ant = Quantifier("∃", x, Diamond(Atom("A", [x])))   # ∃x ◇A(x)
con = Diamond(Quantifier("∃", x, Atom("A", [x])))   # ◇∃x A(x)

satisfies_modal(ant, decreasing, 0)   # → True
satisfies_modal(con, decreasing, 0)   # → False
```

So `satisfies_modal` gives you both halves of the correspondence by hand-built example: **BF breaks on growth, CBF breaks on shrinkage**, and a constant domain (neither growing nor shrinking) validates both.

### Varying domains: BF and CBF both fail

When domains can move arbitrarily (neither growing nor shrinking), neither Barcan formula holds:

```python
# Domain oscillates: D_0 = {a}, D_1 = {b}  (completely disjoint)
oscillating = KripkeModel(
    worlds={0, 1}, relations={"alethic": {(0, 1), (1, 0)}},
    domains={0: {"a"}, 1: {"b"}},
    valuation={0: {"A(a)"}, 1: {"A(b)"}}
)

satisfies_modal(BARCAN, oscillating, 0)          # → False  (breaks on growth)
satisfies_modal(CONVERSE_BARCAN, oscillating, 0)  # → False  (breaks on shrinkage)
```

## (A) First-order shallow embedding → Z3

`qml_translate` rewrites a modal formula into classical FOL — quantifiers over worlds for the modalities, and an existence predicate `E` relativising the actualist object quantifiers — and `qml_is_valid(φ, mode, frame)` decides validity with **Z3**. The `mode` is the domain regime (`"constant"`, `"increasing"` / `"cumulative"`, `"decreasing"`, `"varying"`, `"possibilist"`) and `frame` ∈ {`K`, `T`, `S4`, `S5`, `KD`, `KD45`, `B`, `S4.2`, `S4.3`}.

### Seeing the translation

`qml_translate(φ, mode, world="w")` is the rewrite itself — a plain classical-FOL `Node` you can render. Each atom gets the current world appended as a last argument, `◇` becomes a guarded `∃` over accessible worlds, and `□` a guarded `∀`:

```python
from unicode_fol_kit.fol.qml import qml_translate

qml_translate(Box(A(x)), mode="constant").to_unicode_str()
# → '∀_w0 (World(_w0) ∧ R(w, _w0) → A(x, _w0))'

qml_translate(Diamond(A(x)), mode="constant").to_unicode_str()
# → '∃_w0 (World(_w0) ∧ R(w, _w0) ∧ A(x, _w0))'
```

More complex formulas show how structure is preserved:

```python
# Nested: □(∃x A(x))
nested = Box(Quantifier("∃", x, A(x)))
qml_translate(nested, mode="constant").to_unicode_str()
# → '∀_w0 (World(_w0) ∧ R(w, _w0) → ∃x (Object(x) → A(x, _w0)))'

# With box: □∀x A(x)
forall_box = Box(Quantifier("∀", x, A(x)))
qml_translate(forall_box, mode="constant").to_unicode_str()
# → '∀_w0 (World(_w0) ∧ R(w, _w0) → ∀x (Object(x) → A(x, _w0)))'
```

The domain regime shows up in how the *object* quantifiers are guarded. Under a **constant / possibilist** mode `∀x` is unrelativised (just typed `Object(x)`); under an **actualist** mode (`increasing` / `decreasing` / `varying`) it is additionally guarded by the existence predicate `E(x, w)` ("`x` exists at world `w`"):

```python
forall = Quantifier("∀", x, A(x))

qml_translate(forall, mode="constant").to_unicode_str()
# → '∀x (Object(x) → A(x, w))'

qml_translate(forall, mode="increasing").to_unicode_str()
# → '∀x (Object(x) ∧ E(x, w) → A(x, w))'
```

Compare existential quantifiers:

```python
exists = Quantifier("∃", x, A(x))

qml_translate(exists, mode="constant").to_unicode_str()
# → '∃x (Object(x) ∧ A(x, w))'

qml_translate(exists, mode="increasing").to_unicode_str()
# → '∃x (Object(x) ∧ E(x, w) ∧ A(x, w))'
```

The background axioms (sort typing, frame conditions, the existence-axiom that *defines* the regime) are exposed separately as `qml_axioms(mode, frame)`; `qml_is_valid` checks `⋀axioms → ∀w (World(w) → ST(φ, w))`:

```python
from unicode_fol_kit.fol.qml import qml_axioms

ax = qml_axioms(mode="increasing", frame="S4")
len(ax)                       # → 9
ax[0].to_unicode_str()        # → '∀t ¬(World(t) ∧ Object(t))'   (worlds and objects are disjoint)

# Inspect the axioms for different regimes
ax_const = qml_axioms(mode="constant", frame="K")
ax_incr = qml_axioms(mode="increasing", frame="K")
ax_decr = qml_axioms(mode="decreasing", frame="K")

len(ax_const), len(ax_incr), len(ax_decr)  # → (7, 7, 7)  (same base count)

# Check if increasing mode has domain constraints
any("cumulative" in str(ax) for ax in ax_incr)  # → True
any("decreasing" in str(ax) for ax in ax_decr)  # → True
```

### Deciding validity per regime

The core decision procedure: test a formula under all domain regimes:

```python
from unicode_fol_kit import qml_is_valid, qml_equivalent, BARCAN, CONVERSE_BARCAN

qml_is_valid(BARCAN, mode="constant")           # → True
qml_is_valid(BARCAN, mode="increasing")         # → False
qml_is_valid(BARCAN, mode="decreasing")         # → True

qml_is_valid(CONVERSE_BARCAN, mode="increasing")  # → True
qml_is_valid(CONVERSE_BARCAN, mode="decreasing")  # → False
qml_is_valid(BARCAN, mode="varying")              # → False
```

The full correspondence (verified against the Kripke enumerator) is: **BF ⇔ decreasing** domains, **CBF ⇔ increasing**, **constant ⇔ both**, and **varying ⇔ neither**. The `cumulative` alias is `increasing`, and `possibilist` is `constant` (every individual exists everywhere):

```python
qml_is_valid(BARCAN, mode="cumulative")           # → False   (alias of "increasing")
qml_is_valid(BARCAN, mode="possibilist")          # → True    (alias of "constant")

qml_is_valid(CONVERSE_BARCAN, mode="constant")    # → True
qml_is_valid(CONVERSE_BARCAN, mode="varying")     # → False
```

This reproduces, decision-procedure-style, exactly the by-hand verdicts from `satisfies_modal` above.

### Testing mixed quantifiers

Quantifier nesting shows regime-dependent effects:

```python
# Existential outside box: "there exists someone for whom P is necessary"
ex_nec = Quantifier("∃", x, Box(A(x)))

# Box outside existential: "it is necessary that someone exists with P"
nec_ex = Box(Quantifier("∃", x, A(x)))

# Under constant domains, these are equivalent
qml_is_valid(ex_nec, mode="constant")           # → True
qml_is_valid(nec_ex, mode="constant")           # → True
qml_equivalent(ex_nec, nec_ex, mode="constant") # → True

# Under increasing domains, they diverge
qml_is_valid(ex_nec, mode="increasing")           # → True  (a fixed object)
qml_is_valid(nec_ex, mode="increasing")           # → False (new objects appear)
qml_equivalent(ex_nec, nec_ex, mode="increasing") # → False
```

### Adding a frame system

The `frame` argument fixes the **alethic** accessibility relation (defaulting to the minimal `K`). The Barcan correspondence is a *domain* phenomenon, so it is robust across frames — BF stays valid under constant domains whether the frame is `K`, `S4`, or `S5`:

```python
qml_is_valid(BARCAN, mode="constant", frame="K")    # → True
qml_is_valid(BARCAN, mode="constant", frame="S4")   # → True
qml_is_valid(BARCAN, mode="constant", frame="S5")   # → True

qml_is_valid(CONVERSE_BARCAN, mode="increasing", frame="S5")  # → True
```

Frame *schemata* (as opposed to domain effects) do depend on the system. The classic propositional ones decide through this embedding too, because Z3 sees their first-order frame conditions:

```python
p = Atom("P", [])

qml_is_valid(Implies(Box(p), p), frame="T")              # → True   (T: reflexive)
qml_is_valid(Implies(Box(p), p), frame="K")              # → False
qml_is_valid(Implies(Box(p), Box(Box(p))), frame="S4")   # → True   (4: transitive)
qml_is_valid(Implies(Diamond(p), Box(Diamond(p))), frame="S5")  # → True   (5: euclidean)
qml_is_valid(Implies(Diamond(p), Box(Diamond(p))), frame="S4")  # → False
```

Test the deontic frame (seriality):

```python
# KD: serial frame (every world has a successor)
qml_is_valid(Implies(Diamond(p), Implies(Box(Not(p)), Diamond(p))), frame="KD")  # → True
```

### `qml_equivalent`

`qml_equivalent(left, right, mode, frame)` is just `qml_is_valid` of the biconditional. Since both BF and CBF are valid under constant domains, they are QML-equivalent there — but not under a one-sided regime:

```python
qml_equivalent(BARCAN, CONVERSE_BARCAN, mode="constant")     # → True
qml_equivalent(BARCAN, CONVERSE_BARCAN, mode="constant", frame="S4")  # → True
qml_equivalent(BARCAN, CONVERSE_BARCAN, mode="increasing")   # → False   (only CBF holds)
qml_equivalent(BARCAN, CONVERSE_BARCAN, mode="decreasing")   # → False   (only BF holds)
```

Test complex equivalences:

```python
# These two are equivalent under constant domains
f1 = Implies(Box(A(x)), Diamond(A(x)))
f2 = Diamond(A(x))

qml_equivalent(f1, f2, mode="constant")    # → False  (f1 is actually too strong)

# A simpler test: are quantifiers commutative under all regimes?
y = Variable("y")
B = lambda t: Atom("B", [t])

# ∃x ∃y A(x) ∧ B(y)  vs  ∃y ∃x A(x) ∧ B(y)
both_exist = Quantifier("∃", x, Quantifier("∃", y, And(A(x), B(y))))
both_exist_flip = Quantifier("∃", y, Quantifier("∃", x, And(A(x), B(y))))

qml_equivalent(both_exist, both_exist_flip, mode="constant")    # → True
qml_equivalent(both_exist, both_exist_flip, mode="increasing")  # → True
```

### Soundness caveat and error modes

This embedding is **sound but bounded-incomplete**: first-order modal logic is undecidable, so a `False` may mean "Z3 did not prove validity within the bound" rather than "definitely invalid" — use `satisfies_modal` on an explicit model for a guaranteed countermodel. The API also fails loudly on bad inputs rather than guessing:

```python
qml_is_valid(BARCAN, mode="weird")   # raises ValueError: unknown mode 'weird'
qml_is_valid(BARCAN, frame="ZZ")     # raises ValueError: unknown frame 'ZZ'
qml_is_valid(BARCAN, frame="GL")     # raises NotImplementedError: GL is not first-order definable
```

`GL` (Gödel–Löb provability) is transitive + converse-well-founded, which is **not** first-order definable, so the Z3 path rejects it; reach it only through the higher-order exporters below.

Inspect error messages closely:

```python
from unicode_fol_kit import qml_is_valid

try:
    qml_is_valid(BARCAN, mode="unknown_mode")
except ValueError as e:
    print(f"Error: {e}")  # Shows the allowed modes
```

### A fourth view: `resolution.prove` over the qml embedding

`resolution.prove(premises, conclusion)` also accepts quantified-modal input directly: it lowers the folded consequence `premises ⊢ conclusion` through the same first-order embedding `qml_is_valid` uses (constant domains, frame **K**), scales the saturation step budget to the larger translated clause set, and runs the resolution loop in-process — no Z3 dependency for this path. Both Barcan directions are provable:

```python
from unicode_fol_kit.atp import resolution

resolution.prove([], BARCAN)              # → True
resolution.prove([], CONVERSE_BARCAN)     # → True
```

Like `qml_is_valid`, this is **sound but bounded-incomplete**: `False` means "not proved within `max_steps`", never "definitely invalid" — reach for `satisfies_modal` on an explicit model when you need a guaranteed countermodel. Unlike `qml_is_valid`, there is no `mode=`/`frame=` choice here; it is fixed to constant-domain K, matching `qml_is_valid`'s own defaults.

## (B) Higher-order shallow embedding → TPTP THF

`to_thf_modal(φ, mode, frame)` emits a complete Benzmüller-style **TPTP THF** problem for an external higher-order prover (Leo-III, Satallax). A modal proposition is a function `mu > $o` (world → bool); the modalities are λ-lifted quantifiers over the accessibility relation `r`, and object quantifiers are `existsAt`-guarded (actualist). The frame and domain regime are encoded as axioms.

```python
from unicode_fol_kit import to_thf_modal, BARCAN

thf = to_thf_modal(BARCAN, mode="constant", frame="S5")
type(thf)                  # → <class 'str'>
thf.splitlines()[0]
# → "% Shallow embedding of a quantified modal formula (mode=constant, frame=S5)."
"thf(mbox," in thf         # → True   (lifted operators mbox/mdia/mforall/mexists are defined)
```

The emitted file is a full, self-contained problem: the type of worlds `mu`, the lifted operator definitions, the frame axioms, the `existsAt` domain axiom for the regime, and the conjecture `mvalid @ ⟨formula⟩`. You can see those pieces by grepping the lines:

```python
thf_T = to_thf_modal(Implies(Box(Atom("P", [])), Atom("P", [])), mode="constant", frame="T")

[l for l in thf_T.splitlines() if l.startswith("thf(refl")][0]
# → 'thf(refl, axiom, ( ! [W: mu] : ( r @ W @ W ) )).'
[l for l in thf_T.splitlines() if l.startswith("thf(const_dom")][0]
# → 'thf(const_dom, axiom, ( ! [X: $i, W: mu] : ( existsAt @ X @ W ) )).'
[l for l in thf_T.splitlines() if l.startswith("thf(goal")][0][:45]
# → 'thf(goal, conjecture, ( mvalid @ ( mimplies @'
```

### Inspecting domain axioms

Different regimes emit different existsAt constraints. Check what axiom is in a THF problem:

```python
# Constant domain: everyone exists everywhere
thf_const = to_thf_modal(CONVERSE_BARCAN, mode="constant", frame="K")
"! [X: $i, W: mu] : ( existsAt @ X @ W )" in thf_const  # → True

# Increasing domain: objects only appear, never disappear
thf_incr = to_thf_modal(CONVERSE_BARCAN, mode="increasing", frame="K")
"cumulative_dom" in thf_incr  # → True

# Decreasing domain: objects disappear, never appear
thf_decr = to_thf_modal(BARCAN, mode="decreasing", frame="K")
"decreasing_dom" in thf_decr  # → True

# Varying domain: no constraint on existsAt
thf_var = to_thf_modal(BARCAN, mode="varying", frame="K")
any(d in thf_var for d in ("const_dom", "cumulative_dom", "decreasing_dom"))  # → False
```

The domain regime selects which `existsAt` axiom is emitted. `constant` (and its alias `possibilist`) asserts every individual exists at every world; `increasing` / `decreasing` assert the monotone existence axioms; `varying` emits **none** of them (no constraint on how the domain moves):

```python
"cumulative_dom" in to_thf_modal(CONVERSE_BARCAN, mode="increasing", frame="S4")  # → True
"decreasing_dom" in to_thf_modal(BARCAN, mode="decreasing", frame="S4")           # → True

thf_v = to_thf_modal(BARCAN, mode="varying", frame="K")
any(d in thf_v for d in ("const_dom", "cumulative_dom", "decreasing_dom"))        # → False
```

Unlike the Z3 path, the THF exporter **accepts** `frame="GL"`: it emits the Löb schema as a higher-order axiom for the prover (HOL can express converse-well-foundedness where first-order logic cannot):

```python
loeb = Implies(Box(Implies(Box(Atom("P", [])), Atom("P", []))), Box(Atom("P", [])))
"thf(loeb," in to_thf_modal(loeb, frame="GL")   # → True
```

Generate THF for more complex formulas:

```python
# Combine quantifiers and modalities
f = Quantifier("∀", x, Implies(Atom("Person", [x]), Diamond(Atom("Happy", [x]))))
thf_person = to_thf_modal(f, mode="constant", frame="S5")

# Check that the formula appears in the THF
"mforall" in thf_person  # → True
"mdia" in thf_person     # → True
```

The function **emits** the problem (like the other `to_*` exporters); it does not run a prover in-process. The conjecture comes out a `Theorem` for the prover exactly when the formula is QML-valid under the given regime.

### A loadable Isabelle/HOL theory

`to_isabelle_modal(φ, mode, frame)` is the Isabelle counterpart — a complete, loadable `theory … begin … end` with every lifted operator defined and a genuine `lemma` to discharge:

```python
from unicode_fol_kit import to_isabelle_modal

iz = to_isabelle_modal(BARCAN, mode="constant", frame="S5")
iz.splitlines()[0]          # → 'theory ModalEmbedding'
"lemma" in iz               # → True
```

Inspect the Isabelle output structure:

```python
iz_lines = iz.splitlines()
print(iz_lines[0])     # → 'theory ModalEmbedding'
print(iz_lines[-3:])   # → end / proof lines
"imports HOL.Equiv_Relations" in iz  # → True (imports standard HOL libraries)
```

This covers the alethic □/◇ fragment; for the full modal family (epistemic / doxastic / deontic / temporal) and the additional exporter options, see {doc}`higher-order`.

## End-to-end: parse → decide → cross-check → export

A complete pass over one formula, exercising all three views. Take the box Converse Barcan `□∀x A(x) → ∀x □A(x)`, decide it under each regime with Z3, confirm the increasing-domain verdict on an explicit model, then export a prover problem:

```python
from unicode_fol_kit import MSFLParser, qml_is_valid, to_thf_modal, satisfies_modal
from unicode_fol_kit.semantics.kripke import KripkeModel

mp = MSFLParser(modal=True)
phi = mp.parse("□∀x A(x) → ∀x □A(x)")     # box Converse Barcan ⇔ increasing domains

# 1. decision procedure (Z3) across the regimes
qml_is_valid(phi, mode="increasing")   # → True
qml_is_valid(phi, mode="decreasing")   # → False
qml_is_valid(phi, mode="constant")     # → True

# 2. cross-check the True verdict semantically on a constant-domain S5 model
S5 = {"alethic": {(0, 0), (0, 1), (1, 0), (1, 1)}}
model = KripkeModel(
    worlds={0, 1}, relations=S5,
    valuation={0: {"A(a)", "A(b)"}, 1: {"A(a)", "A(b)"}},
    domain={"a", "b"},
)
satisfies_modal(phi, model, 0)         # → True

# 3. export a higher-order problem for an external prover
problem = to_thf_modal(phi, mode="increasing", frame="S5")
problem.splitlines()[0]
# → "% Shallow embedding of a quantified modal formula (mode=increasing, frame=S5)."
```

The three steps agree by construction — that triangulation between the brute-force evaluator, the Z3 embedding, and the exported HOL problem is the whole point of carrying three views of QML.

### Comparing all three approaches on a custom formula

Test a non-canonical formula across all pathways:

```python
# Parse a realistic formula: "Something can necessarily know something"
custom = mp.parse("∃x ∃y □Knows(x, y)")

# Path 1: Z3 decision (all regimes)
for mode in ["constant", "increasing", "decreasing", "varying"]:
    result = qml_is_valid(custom, mode=mode)
    print(f"{mode:12}: {result}")
# → constant   : False
#   increasing : False
#   decreasing : False
#   varying    : False

# Path 2: Semantics — build a model where it's true
knows_model = KripkeModel(
    worlds={0, 1},
    relations={"alethic": {(0, 1)}},
    domain={"alice", "bob"},
    valuation={1: {"Knows(alice, bob)"}}
)

x = Variable("x")
y = Variable("y")
Knows = lambda a, b: Atom("Knows", [a, b])

formula = Quantifier("∃", x, Quantifier("∃", y, Box(Knows(x, y))))
satisfies_modal(formula, knows_model, 0)  # → True (alice and bob in world 1)

# Path 3: Export to THF for external verification
thf_custom = to_thf_modal(custom, mode="constant", frame="S5")
len(thf_custom.splitlines())  # → (large problem, many axiom lines)
"mforall" in thf_custom  # → True (existentials become mforall in the embedding)
```
