# Quantified Modal Logic

Combining the modalities with `∀x` / `∃x` gives **quantified modal logic** (QML), where validity turns on how the individual domain varies between worlds. `unicode-logic-kit` handles QML both *semantically* (a `KripkeModel` with per-world domains and an actualist `satisfies_modal`) and via two **shallow embeddings** in the Benzmüller style — a first-order one decided by Z3, and a higher-order one exported as TPTP THF.

The kit gives you four views of the same logic, and they are designed to agree:

| Tool | What it is | Verdict |
| --- | --- | --- |
| `satisfies_modal` | brute-force evaluator over an *explicit* finite model | ground truth + countermodels |
| `qml_is_valid` | first-order shallow embedding → **Z3** | sound, bounded-incomplete |
| `resolution.prove` | the qml embedding lowered further and saturated in-process | sound, bounded-incomplete |
| `to_thf_modal` / `to_isabelle_modal` | higher-order shallow embedding → external prover | sound (you run the prover) |

## Building modal formulas as nodes

Every example below builds the AST directly from `unicode_logic_kit`, so no parser is involved. A modal formula mixes the modal nodes `Box` / `Diamond` with the ordinary first-order nodes `Quantifier` / `Atom` / `Variable`. The Barcan formula `◇∃x A(x) → ∃x ◇A(x)` and its converse are the standard litmus tests for the domain regime, and the kit exports them ready-made as `BARCAN` / `CONVERSE_BARCAN`:

```python
from unicode_logic_kit import (
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
from unicode_logic_kit import MSFLParser, qml_is_valid

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

The **order** of quantifiers matters crucially. Swapping `∃x` and `□` gives two formulas that are not equivalent under any domain regime (frame `K`, the default), and whether the first implies the second depends on the regime:

```python
from unicode_logic_kit import qml_is_valid, qml_equivalent

# Existential outside the box: some specific thing is necessarily A
ex_box = Quantifier("∃", x, Box(A(x)))

# Box around existential: necessarily, there exists something that is A
box_ex = Box(Quantifier("∃", x, A(x)))

# Neither is valid on its own (A may hold of nothing), so compare them as an implication
qml_is_valid(Implies(ex_box, box_ex), mode="constant")      # → True
qml_is_valid(Implies(ex_box, box_ex), mode="increasing")    # → True   (existing objects stay)
qml_is_valid(Implies(ex_box, box_ex), mode="decreasing")    # → False  (the object may leave)

# The converse fails in every regime: the witness may differ from world to world
qml_is_valid(Implies(box_ex, ex_box), mode="constant")      # → False

qml_equivalent(ex_box, box_ex, mode="constant")    # → False
qml_equivalent(ex_box, box_ex, mode="increasing")  # → False
```

There is a *second* Barcan pair phrased with `□`/`∀` rather than `◇`/`∃` — the **box Barcan** `∀x □A(x) → □∀x A(x)` and **box Converse Barcan** `□∀x A(x) → ∀x □A(x)`. They are the contrapositive duals of `BARCAN` / `CONVERSE_BARCAN`, so the regime correspondence is mirrored (box-BF ⇔ decreasing, box-CBF ⇔ increasing). You build them the same way:

```python
from unicode_logic_kit import qml_is_valid

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
from unicode_logic_kit.semantics.kripke import KripkeModel

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
from unicode_logic_kit import satisfies_modal, Variable, Atom, Quantifier
from unicode_logic_kit.semantics.kripke import KripkeModel

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
from unicode_logic_kit import Constant
a = Constant("a")
b = Constant("b")
satisfies_modal(A(a), m, 0)  # → True   (A(a) holds at world 0)
satisfies_modal(A(b), m, 0)  # → False  (the valuation of world 0 has no A(b))
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
)  # → False  (alice is not happy here)

# "It's possible that everyone is a person" — true at 0, since worlds 1,2 have all
satisfies_modal(
    Diamond(Quantifier("∀", x, Person(x))),
    model, 0
)  # → True
```

A model built **without** domains is the purely propositional fragment of {doc}`modal`; asking it to evaluate an object quantifier is an error rather than a silent default:

```python
from unicode_logic_kit import satisfies_modal, Quantifier, Variable, Atom

x = Variable("x")
prop_only = KripkeModel(worlds={0}, valuation={0: {"A(a)"}})
satisfies_modal(Quantifier("∃", x, Atom("A", [x])), prop_only, 0)
# raises ValueError: this Kripke model has no object domains …
```

### Barcan fails when domains grow

The Barcan formula is valid under constant domains but **fails when domains grow**, because an object can appear only in a successor world:

```python
from unicode_logic_kit import BARCAN, satisfies_modal
from unicode_logic_kit.semantics.kripke import KripkeModel

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
from unicode_logic_kit import CONVERSE_BARCAN

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
    valuation={0: {"A(b)"}, 1: {"A(b)"}}
)

satisfies_modal(BARCAN, oscillating, 0)           # → False  (b appears at world 1: breaks on growth)
satisfies_modal(CONVERSE_BARCAN, oscillating, 1)  # → False  (b is gone at world 0: breaks on shrinkage)
```

## (A) First-order shallow embedding → Z3

`qml_translate` rewrites a modal formula into classical FOL — quantifiers over worlds for the modalities, and an existence predicate `E` relativising the actualist object quantifiers — and `qml_is_valid(φ, mode, frame)` decides validity with **Z3**. The `mode` is the domain regime (`"constant"`, `"increasing"` / `"cumulative"`, `"decreasing"`, `"varying"`, `"possibilist"`) and `frame` ∈ {`K`, `T`, `S4`, `S5`, `KD`, `KD45`, `B`, `S4.2`, `S4.3`}.

### Seeing the translation

`qml_translate(φ, mode, world="w")` is the rewrite itself — a plain classical-FOL `Node` you can render. Each atom gets the current world appended as a last argument, `◇` becomes a guarded `∃` over accessible worlds, and `□` a guarded `∀`:

```python
from unicode_logic_kit.fol.qml import qml_translate

qml_translate(Box(A(x)), mode="constant").to_unicode_str()
# → '∀w0 (World(w0) ∧ R(w, w0) → A(x, w0))'

qml_translate(Diamond(A(x)), mode="constant").to_unicode_str()
# → '∃w0 (World(w0) ∧ R(w, w0) ∧ A(x, w0))'
```

More complex formulas show how structure is preserved:

```python
# Nested: □(∃x A(x))
nested = Box(Quantifier("∃", x, A(x)))
qml_translate(nested, mode="constant").to_unicode_str()
# → '∀w0 (World(w0) ∧ R(w, w0) → ∃x (Object(x) ∧ A(x, w0)))'

# With box: □∀x A(x)
forall_box = Box(Quantifier("∀", x, A(x)))
qml_translate(forall_box, mode="constant").to_unicode_str()
# → '∀w0 (World(w0) ∧ R(w, w0) → ∀x (Object(x) → A(x, w0)))'
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
from unicode_logic_kit.fol.qml import qml_axioms

ax = qml_axioms(mode="increasing", frame="S4")
len(ax)                       # → 17
ax[0].to_unicode_str()        # → '∀t ¬(World(t) ∧ Object(t))'   (worlds and objects are disjoint)

# Inspect the axioms for different regimes
ax_const = qml_axioms(mode="constant", frame="K")
ax_incr = qml_axioms(mode="increasing", frame="K")
ax_decr = qml_axioms(mode="decreasing", frame="K")

len(ax_const), len(ax_incr), len(ax_decr)  # → (15, 15, 15)  (same base count)

# The regime axiom is the last one, and the two regimes are mirror images:
# increasing carries existence FORWARD along R, decreasing carries it BACK.
ax_incr[-1].to_unicode_str()
# → '∀x ∀w ∀v (Object(x) ∧ World(w) ∧ (World(v) ∧ (E(x, w) ∧ R(w, v))) → E(x, v))'
ax_decr[-1].to_unicode_str()
# → '∀x ∀w ∀v (Object(x) ∧ World(w) ∧ (World(v) ∧ (E(x, v) ∧ R(w, v))) → E(x, w))'
```

Called with no `formula=`, that is the *whole* background theory: one relation per modal family (alethic `R`, temporal `T`, one-step `N`, deontic `D`) plus their default frame conditions. Pass the formula and only the relations it actually mentions are typed and constrained — for a `□`-only formula the list is exactly what it was before the temporal/deontic conditions existed:

```python
from unicode_logic_kit import MSFLParser

pm = MSFLParser(modal=True).parse
len(qml_axioms(formula=pm("□P → P")))          # → 7   (nothing temporal or deontic in scope)
len(qml_axioms())                              # → 15  (every family's relation)
```

### Temporal and deontic conditions are on by default

The temporal relation `T` is reflexive + transitive (it *is* the henceforth relation), `N ⊆ T` links the one-step relation to it, and the deontic relation `D` is serial. These are on by default because that is what makes this route agree with `satisfies_modal` and with the Isabelle / THF exporters — before, a temporal or deontic formula was judged with *no* condition on its relation at all, so plainly valid principles came back `False`:

```python
from unicode_logic_kit import qml_is_valid

qml_is_valid(pm("Ⓖ P → P"))          # → True   (T reflexive)
qml_is_valid(pm("Ⓖ P → Ⓖ Ⓖ P"))      # → True   (T transitive)
qml_is_valid(pm("Ⓖ P → Ⓝ P"))        # → True   (N ⊆ T)
qml_is_valid(pm("Ⓞ P → Ⓟ P"))        # → True   (D serial)

qml_is_valid(pm("Ⓝ P → P"))          # → False  (a step need not stay put)
qml_is_valid(pm("Ⓞ P → P"))          # → False  (obligation is not fact)
```

So `True` for a deontic formula means "valid over every **serial-deontic** model" — `satisfies_modal` will still refute `Ⓞφ → Ⓟφ` on a hand-built dead-end model, and that is the honest reading of the disagreement, not a bug on either side. Set `temporal_closure=False` for parity with the exporters' own flag; be aware it answers for a strictly weaker temporal logic (`Ⓖφ → φ` and `Ⓖφ → Ⓕφ` become underivable).

`T` is axiomatised as reflexive-transitive rather than *defined* as the transitive closure of `N`, because a first-order theory cannot pin a closure down. A first-order *consequence* of `T = N*` can be stated, though, and `qml_axioms` emits it whenever both relations occur (`first_step`):

```text
∀w ∀v (World(w) ∧ World(v) ∧ T(w,v) → w = v ∨ ∃u (World(u) ∧ N(w,u) ∧ T(u,v)))
```

— "a henceforth-step is either standing still or one step followed by a henceforth-step". Every `T = N*` model satisfies it, so it over-validates nothing, and with it the fixpoint unfolding `(φ ∧ Ⓝ Ⓖ φ) → Ⓖ φ` becomes provable here. Temporal induction `(φ ∧ Ⓖ(φ → Ⓝ φ)) → Ⓖ φ` genuinely does stay out of reach — reaching an arbitrary `T`-successor from the first step needs induction over the closure, which no first-order theory states. Decide that one with `hol.isabelle_runner.isabelle_decide_modal`, whose theory defines the closure outright. So this route's temporal strength is "refl + trans + `N ⊆ T` + `first_step`" — a chosen axiom set, not "the limit of first-order logic".

### Cross-family bridges with `bridges=`

`frame=` and `systems=` each constrain one relation; a **bridge** relates two relations of *different* families, which is what a principle like "whatever you know, you believe" needs. Bridges are opt-in — none is on by default — and an unknown name raises `ValueError` listing the known ones:

| `bridges=` name | Schema | Frame condition |
| --- | --- | --- |
| `"knowledge_implies_belief"` | `K_a φ → B_a φ` | `Rb ⊆ Rk` |
| `"sincerity"` | `Say_a φ → B_a φ` | `Rb ⊆ Rs` |
| `"ought_implies_can"` | `Ⓞ φ → ◇φ` | `∀w ∃v (D(w,v) ∧ R(w,v))` |

```python
from unicode_logic_kit import QML_BRIDGES, qml_is_valid

sorted(QML_BRIDGES)   # → ['knowledge_implies_belief', 'ought_implies_can', 'sincerity']

kb = pm("K_a P → B_a P")
qml_is_valid(kb)                                            # → False  (off by default)
qml_is_valid(kb, bridges=["knowledge_implies_belief"])      # → True
qml_is_valid(pm("B_a P → K_a P"),
             bridges=["knowledge_implies_belief"])          # → False  (the converse stays invalid)
```

The two inclusions are emitted **unguarded** (`∀a ∀w ∀v (Rb(a,w,v) → Rk(a,w,v))`), which is what lets them fire for a quantified agent — `∀x (K_x φ → B_x φ)` is valid under the bridge. `ought_implies_can` is deliberately *not* the folklore `D ⊆ R`: measured, that inclusion fails to validate `Ⓞφ → ◇φ` on its own, and together with the default-on `d_serial` it over-validates both `□φ → Ⓞφ` ("whatever is necessary is obligatory") and `Ⓟφ → ◇φ`. The ∃-quantified *meet* condition emitted instead is the exact correspondent: it subsumes deontic seriality, validates the schema, and carries neither artefact. It is the same condition the HOL routes emit under the same name (`d_meets_r`), so **one option name denotes one logic on every route** — see [Higher-order logic](higher-order.md).

A bridge relates two relations, so requesting one while the formula mentions only one of the two families raises `ValueError` rather than silently emitting a weaker logic (skipping it) or a stronger one (the meet condition entails seriality of the alethic `R`, which would quietly make `□P → ◇P` valid under `frame="K"`). The same rule applies on every route. `qml_axioms()` called without `formula=` asks for the whole background theory, in which every relation is in scope, so nothing is rejected there.

### Deciding validity per regime

The core decision procedure: test a formula under all domain regimes:

```python
from unicode_logic_kit import qml_is_valid, qml_equivalent, BARCAN, CONVERSE_BARCAN

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

### Free variables are parameters

A variable that is free in a formula is a **parameter**: one unknown individual, the same everywhere in the formula and rigid like a constant (the same individual at every world). Under `constant` and `possibilist` domains it is an element of the object domain, so `∀x P(x) → P(y)` and `P(y) → ∃x P(x)` are valid. Under `varying`, `increasing` and `decreasing` domains it exists at the world of evaluation and need not exist at any other world. Those two formulas stay valid there, but `□∀x P(x) → □P(y)` and `□∃x (x = y)` are valid only under `constant`, `possibilist` and `increasing` domains, where an individual that exists here exists at every accessible world. `P(y) → P(alice)` is valid under none, since `y` need not be `alice`. For a formula with no premise the reading is its universal closure, guarded by existence under an actualist mode (`increasing` / `decreasing` / `varying`):

```python
box_inst = pm("□∀x P(x) → □P(y)")                         # y is free: a parameter
qml_is_valid(pm("∀x P(x) → P(y)"), mode="varying")        # → True
qml_is_valid(pm("P(y) → ∃x P(x)"), mode="varying")        # → True
qml_is_valid(box_inst, mode="increasing")                 # → True   (y exists here, so at every later world)
qml_is_valid(box_inst, mode="decreasing")                 # → False  (y may be gone from a later world)
qml_is_valid(box_inst, mode="varying")                    # → False
qml_is_valid(pm("∀y (□∀x P(x) → □P(y))"), mode="varying")  # → False  (the guarded closure gives the same verdict)
qml_is_valid(pm("□∃x (x = y)"), mode="constant")          # → True
qml_is_valid(pm("□∃x (x = y)"), mode="varying")           # → False
qml_is_valid(pm("P(y) → P(alice)"), mode="constant")      # → False  (y need not be alice)
```

### Testing mixed quantifiers

Quantifier nesting shows regime-dependent effects:

```python
# Existential outside box: "there exists someone for whom P is necessary"
ex_nec = Quantifier("∃", x, Box(A(x)))

# Box outside existential: "it is necessary that someone exists with P"
nec_ex = Box(Quantifier("∃", x, A(x)))

# Neither is valid on its own (A may hold of nothing). Under constant domains the
# first implies the second, but not the other way round: the witness may change
qml_is_valid(Implies(ex_nec, nec_ex), mode="constant")  # → True
qml_is_valid(Implies(nec_ex, ex_nec), mode="constant")  # → False
qml_equivalent(ex_nec, nec_ex, mode="constant")         # → False

# Under increasing domains the implication still holds (a fixed object stays),
# under decreasing domains it fails (the object may be gone at the successor)
qml_is_valid(Implies(ex_nec, nec_ex), mode="increasing")  # → True
qml_is_valid(Implies(ex_nec, nec_ex), mode="decreasing")  # → False
qml_equivalent(ex_nec, nec_ex, mode="increasing")         # → False
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
from unicode_logic_kit import Not

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
# f1 is weaker than f2 (f2 implies f1, but f1 also holds where □A(x) fails),
# so the two are not equivalent
f1 = Implies(Box(A(x)), Diamond(A(x)))
f2 = Diamond(A(x))

qml_equivalent(f1, f2, mode="constant")    # → False

# A simpler test: are quantifiers commutative under all regimes?
from unicode_logic_kit import And

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
qml_is_valid(BARCAN, frame="GL")     # raises NotImplementedError: the frame 'GL' needs the condition 'loeb' (… NOT first-order definable …)
```

`GL` (Gödel–Löb provability) is transitive + converse-well-founded, which is **not** first-order definable, so the Z3 path rejects it; reach it only through the higher-order exporters below.

Inspect error messages closely:

```python
from unicode_logic_kit import qml_is_valid

try:
    qml_is_valid(BARCAN, mode="unknown_mode")
except ValueError as e:
    print(f"Error: {e}")  # Shows the allowed modes
```

### A fourth view: `resolution.prove` over the qml embedding

`resolution.prove(premises, conclusion)` also accepts quantified-modal input directly: it lowers the folded consequence `premises ⊢ conclusion` through the same first-order embedding `qml_is_valid` uses (constant domains, frame **K**), scales the saturation step budget to the larger translated clause set, and runs the resolution loop in-process — no Z3 dependency for this path. Both Barcan directions are provable:

```python
from unicode_logic_kit.atp import resolution

resolution.prove([], BARCAN)              # → True
resolution.prove([], CONVERSE_BARCAN)     # → True
```

Like `qml_is_valid`, this is **sound but bounded-incomplete**: `False` means "not proved within `max_steps` (or within `timeout=`, in milliseconds, when one is given)", never "definitely invalid" — reach for `satisfies_modal` on an explicit model when you need a guaranteed countermodel. Unlike `qml_is_valid`, there is no `mode=`/`frame=` choice here; it is fixed to constant-domain K, matching `qml_is_valid`'s own defaults.

One route difference is worth knowing before you compare verdicts on a **temporal or deontic** formula. Purely propositional modal input is lowered by `standard_translation`, which emits the accessibility relation and no frame conditions at all, so `resolution.prove([], Ⓖ P → P)` is `False` where `qml_is_valid` is `True` — the resolution route is answering for a temporal logic with an unconstrained relation. (`modal_decide` returns `'unknown'` on the same formula, for its own reason: the tableau has no rule for the henceforth closure.) Nothing here is unsound — a resolution `False` never claims invalidity — but it is not evidence against `qml_is_valid`'s `True`. The one fact this route does add is the rigid membership of a sorted constant: for a sorted constant `c:S` (read by `MSFLParser(modal=True, many_sorted=True)`) the lowered problem takes `∀v0 S(c, v0)` as a hypothesis, so `□Human(carl:Human)` is proved while `◇Human(carl:Human)` is not (in K a world may have no successor). That lowering mints its world variables clear of every name of the formula, so a variable or constant named `w`, `w0`, `v0` or `x0` is not captured (the rule is stated with the hybrid translation, {doc}`hybrid`); the embedding of `qml_is_valid` keeps such a name apart from its own world variables too.

## (B) Higher-order shallow embedding → TPTP THF

`to_thf_modal(φ, mode, frame)` emits a complete Benzmüller-style **TPTP THF** problem for an external higher-order prover (Leo-III, Satallax). A modal proposition is a function `mu > $o` (world → bool); the modalities are λ-lifted quantifiers over the accessibility relation `r`, and object quantifiers are `existsAt`-guarded (actualist). The frame and domain regime are encoded as axioms.

```python
from unicode_logic_kit import to_thf_modal, BARCAN

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
"mforall @" in thf_person  # → True   (applied in the conjecture, not only defined in the preamble)
"mdia @" in thf_person     # → True
```

The function **emits** the problem (like the other `to_*` exporters); it does not run a prover in-process. The conjecture comes out a `Theorem` for the prover exactly when the formula is QML-valid under the given regime.

THF has no free variable, so `to_thf_modal` binds a parameter in front of the conjecture and, under an actualist mode, guards it with `existsAt` inside the conjecture, which is the reading `qml_is_valid` has. `hol.thf_modal.to_thf_modal_full` binds it the same way, so the two writers emit the same conjecture on the alethic fragment, also for a formula with a free variable:

```python
from unicode_logic_kit.hol.thf_modal import to_thf_modal_full

goal_of = lambda text: [l for l in text.splitlines() if l.startswith("thf(goal")][0]
box_y = pm("□P(y)")
goal_of(to_thf_modal(box_y, mode="constant", frame="K"))   # → 'thf(goal, conjecture, ( ! [Y: $i] : ( mvalid @ ( mbox @ ( p @ Y ) ) ) )).'
goal_of(to_thf_modal(box_y, mode="varying", frame="K"))    # → 'thf(goal, conjecture, ( ! [Y: $i] : ( mvalid @ ( mimplies @ ( existsAt @ Y ) @ ( mbox @ ( p @ Y ) ) ) ) )).'
goal_of(to_thf_modal_full(box_y, mode="varying", frame="K")) == goal_of(to_thf_modal(box_y, mode="varying", frame="K"))  # → True
```

Object identity is **rigid** here, the same reading `qml_is_valid` has: `=` becomes THF's own `=` over the individual sort `$i`, with no world argument, through one extra macro that is emitted only when the formula mentions identity, and `t₁ ≠ t₂` is lowered to `¬(t₁ = t₂)`. So the prover answers the question `qml_is_valid` answers — `a = b → □(a = b)` is a theorem even in `K`, while `□(a = b) → a = b` needs a reflexive or serial frame. Until 0.30.0 the exporters rendered identity as an uninterpreted world-relativised predicate `feq`, which made `∀x (x = x)` unprovable from the THF problem while `qml_is_valid` called it valid; `feq` is gone.

```python
from unicode_logic_kit.fol.nodes import Constant

thf_eq = to_thf_modal(Atom("=", [Constant("a"), Constant("b")]), frame="K")
"feq" in thf_eq                                                    # → False
[l for l in thf_eq.splitlines() if l.startswith("thf(meq,")][0]
# → 'thf(meq, definition, ( meq = ( ^ [A: $i, B: $i, W: mu] : ( A = B ) ) )).'
"thf(meq," in to_thf_modal(Atom("P", [Constant("a")]), frame="K")  # → False
```

The truth constants `⊤` / `⊥` are the same at every world, so the exporters lift them to a constant function of the world (`( ^ [W: mu] : $true )` in THF, `(\<lambda>_. True)` in Isabelle) and never declare them as atoms:

```python
box_top = to_thf_modal(MSFLParser(modal=True).parse("□⊤"), frame="K")
box_top.splitlines()[-1]
# → 'thf(goal, conjecture, ( mvalid @ ( mbox @ ( ^ [W: mu] : $true ) ) )).'
```

### A loadable Isabelle/HOL theory

`to_isabelle_modal(φ, mode, frame)` is the Isabelle counterpart — a complete, loadable `theory … begin … end` with every lifted operator defined and a genuine `lemma` to discharge:

```python
from unicode_logic_kit import to_isabelle_modal

iz = to_isabelle_modal(BARCAN, mode="constant", frame="S5")
iz.splitlines()[0]          # → 'theory ModalEmbedding'
"lemma" in iz               # → True
```

Inspect the Isabelle output structure:

```python
iz_lines = iz.splitlines()
print(iz_lines[0])     # → 'theory ModalEmbedding'
print(iz_lines[-3:])   # → end / proof lines
"imports Main" in iz     # → True (the theory needs nothing beyond Main)
```

This covers the alethic □/◇ fragment; for the full modal family (epistemic / doxastic / deontic / temporal) and the additional exporter options, see {doc}`higher-order`.

## End-to-end: parse → decide → cross-check → export

A complete pass over one formula, exercising all three views. Take the box Converse Barcan `□∀x A(x) → ∀x □A(x)`, decide it under each regime with Z3, confirm the increasing-domain verdict on an explicit model, then export a prover problem:

```python
from unicode_logic_kit import MSFLParser, qml_is_valid, to_thf_modal, satisfies_modal
from unicode_logic_kit.semantics.kripke import KripkeModel

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
len(thf_custom.splitlines())  # → 22  (comments, declarations, lifted operators, axioms, the conjecture)
"mexists @" in thf_custom  # → True (the existentials become applications of mexists)
```

## A fifth view: NXF export, and reading QMLTP problems back

Besides the THF/Isabelle shallow embeddings above, `to_tptp_ncl` (in `atp.tptp_ncl`) exports a QUANTIFIED modal formula as **NXF** ("Non-Classical TFF"), the TPTP World's own native syntax for non-classical logics — a `logic` role statement naming the frame (`K`/`T`/`S4`/`S5`/`D`) and domain regime, native `!`/`?` quantifiers, and one `tff(...,type,...)` declaration per sort/constant/predicate the formula actually uses:

```python
from unicode_logic_kit import BARCAN, to_tptp_ncl

nxf = to_tptp_ncl(BARCAN, frame="S4", conjecture_name="bf")
print(nxf)
# → tff(bf_logic,logic,
#       $modal ==
#         [ $domains == $constant,
#           $designation == $rigid,
#           $terms == $global,
#           $modalities == $modal_system_S4 ] ).
#
#     tff(a_decl,type,
#         a: $i > $o ).
#
#     tff(bf,conjecture,
#         (<.> ? [X: $i] : (a(X)) => ? [X: $i] : (<.> a(X))) ).
```

The companion reader, `fol.qmltp_input`, goes the other way for a DIFFERENT (older, QMLTP-native) surface syntax: it reads the 600-problem [QMLTP library](https://www.iltp.de/qmltp/)'s own `qmf(name, role, formula).` statements and `#box`/`#dia` connectives, plus the structured comment header recording that problem's status (`Theorem`/`Non-Theorem`) per logic and per domain regime — exactly the litmus-test table this page has been building by hand all along:

```python
from unicode_logic_kit.fol.qmltp_input import load_qmltp
from unicode_logic_kit.fol.qml import qml_is_valid

problem = load_qmltp("tests/fixtures/qmltp/barcan.p")   # the test suite's own stand-in, in QMLTP syntax
problem.header.problem
# → 'Barcan scheme instance.'
problem.header.status_for("S4", "constant")
# → 'Theorem'

formula = problem.formulas[0].formula
formula.to_unicode_str()
# → '∀x □F(x) → □∀x F(x)'   (the box-Barcan scheme, parsed straight into a kit Node)

qml_is_valid(formula, mode="constant", frame="S4")  # → True -- agrees with the file's own status table
```

That agreement is not incidental: QMLTP's logic names (`K`/`D`/`T`/`S4`/`S5`) and domain-condition names (`varying`/`cumulative`/`constant`) are used verbatim as `qml_is_valid`'s own `frame=`/`mode=` values, and every `(logic, domain)` cell of every bundled fixture is cross-checked against `qml_is_valid` this way in `tests/test_qmltp_input.py`. The kit ships no QMLTP file — no redistribution licence for the library could be found — so those fixtures are small stand-ins written in the same syntax with hand-derived status tables; point `load_qmltp` at your own copy of QMLTP to read the real problems — the reader and this page's own oracle are required to agree on all of them, not just the one shown here. See `atp.tptp_ncl` / `fol.qmltp_input`'s own module docstrings for the exact supported fragment (mono-modal alethic, native quantifiers, atoms over variables and constants — the exporter refuses a compound function term and a variable that no quantifier binds, the reader an indexed multi-modal connective, each by name, as documented extensions) and the primary sources each syntax choice was checked against.
