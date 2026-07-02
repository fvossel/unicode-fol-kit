# Hybrid logic H(@) — naming worlds

Plain modal logic can say *"somewhere accessible, P holds"* (`◇P`) — but it cannot say **where**. Hybrid logic H(@) closes that gap with two constructs that parse in the modal mode (`MSFLParser(modal=True)`):

- a **nominal** `i` — an atomic formula true at *exactly one* world, thereby naming it;
- the **satisfaction operator** `@i φ` — "at the world named `i`, `φ` holds", evaluated *there* no matter where you currently stand.

Together they buy things plain modal logic cannot express: asserting facts about a *specific* world from anywhere (`@i P`), asserting **world equality** (`@i j` — "the worlds named `i` and `j` are the same"), and pinning frame properties to named points (`(◇i ∧ @i P) → ◇P`). H(@) over **K** stays decidable — the undecidable `↓` binder is deliberately not in the kit (see the boundary section below).

## Syntax

| construct | Unicode | AST node | meaning |
| --- | --- | --- | --- |
| nominal | `i` (a bare lowercase name in formula position) | `Nominal("i")` | true at exactly the world named `i` |
| satisfaction | `@i φ` | `At(Nominal("i"), φ)` | `φ` holds at the world named `i` |

`@i` binds like the other prefix operators (`¬`, `K_a`), and nominals combine freely with every modal operator:

```python
from unicode_fol_kit import MSFLParser, Nominal, At

mp = MSFLParser(modal=True)

mp.parse("i")            # → Nominal(name='i')
mp.parse("@i P")         # → At(nominal=Nominal(name='i'), formula=Atom(predicate='P', args=()))
mp.parse("◇i").to_unicode_str()             # → '◇i'      (some successor is the world i)
mp.parse("@i (□P → □□P)").to_unicode_str()  # → '@i (□P → □□P)'
mp.parse("@i P").to_latex()                 # → '@_{i} P'
```

The nodes are ordinary kit nodes — they render, serialise, and round-trip like everything else, and `At` coerces a bare string for convenience:

```python
from unicode_fol_kit import Node, Atom

p = Atom("P", [])
At("i", p) == At(Nominal("i"), p)            # → True   (string is coerced to a Nominal)
f = mp.parse("@i j ↔ @j i")
mp.parse(f.to_unicode_str()) == f            # → True   (render → reparse round-trip)
Node.from_dict(f.to_dict()) == f             # → True   (dict serialisation round-trip)
```

## Evaluating with a nominal assignment

A `KripkeModel` interprets nominals through the optional `nominals=` mapping (name → world). Every referenced world must exist — a dangling assignment raises at construction time. A nominal is then true at **exactly** the world it names, and `@i φ` evaluates `φ` at that world, wherever the evaluation currently stands:

```python
from unicode_fol_kit import KripkeModel, satisfies_modal, Atom, Nominal, At

sunny = Atom("Sunny", [])
m = KripkeModel(
    worlds={"here", "there"},
    relations={"alethic": {("here", "there")}},
    valuation={"there": {"Sunny"}},
    nominals={"i": "there"},          # the nominal i names the world "there"
)

satisfies_modal(Nominal("i"), m, "here")   # → False  (a nominal is true ONLY at its world)
satisfies_modal(Nominal("i"), m, "there")  # → True
satisfies_modal(At("i", sunny), m, "here") # → True   (@ jumps: Sunny is checked AT "there")
satisfies_modal(sunny, m, "here")          # → False  (… while "here" itself stays rainy)
```

`@i i` is true everywhere (the world named `i` is, trivially, named `i`), and `@` composes with the modal operators — `◇i` reads "some successor is the world `i`":

```python
from unicode_fol_kit import Diamond

satisfies_modal(At("i", Nominal("i")), m, "here")   # → True   (valid at every world)
satisfies_modal(Diamond(Nominal("i")), m, "here")   # → True   ("here" sees the world i)
satisfies_modal(Diamond(Nominal("i")), m, "there")  # → False  ("there" has no successors)
```

A nominal without an assignment is a modelling error, not a truth value — the evaluator raises a `ValueError` naming the offending nominal:

```python
satisfies_modal(Nominal("k"), m, "here")   # raises ValueError: the nominal 'k' has no world assignment …
KripkeModel({0, 1}, nominals={"i": 7})     # raises ValueError: nominal 'i' … not among the model's worlds
```

## The standard translation: nominals as world constants

`standard_translation` maps hybrid constructs into classical FOL alongside the modal ones ({doc}`modal`). A nominal becomes a **world equality** against a dedicated constant, and `@i` simply **re-anchors** the current-world term at that constant — no quantifier is introduced:

- `ST(i)(w)` = `w = nom_i`
- `ST(@i φ)(w)` = `ST(φ)(nom_i)`

```python
from unicode_fol_kit import standard_translation

standard_translation(mp.parse("i")).to_unicode_str()      # → 'w = nom_i'
standard_translation(mp.parse("@i P")).to_unicode_str()   # → 'P(nom_i)'
standard_translation(mp.parse("@i □P")).to_unicode_str()  # → '∀w0 (R(nom_i, w0) → P(w0))'
standard_translation(mp.parse("◇i")).to_unicode_str()     # → '∃w0 (R(w, w0) ∧ w0 = nom_i)'
```

The `nom_` prefix keeps the generated world constants **disjoint from user constants**: a formula whose atoms mention a ground constant `i` can never collide with the nominal `i` — the translation of `@i P(i)` is `P(i, nom_i)`, with both symbols intact.

Because a first-order constant denotes exactly one domain element, `nom_i` captures the "true at exactly one world" semantics of a nominal *for free* once the worlds are the FO domain — no extra axiom needed.

## Deciding validity: `hybrid_is_valid`

`hybrid_is_valid(formula, frame=…)` decides hybrid-modal validity over the frame classes **K / T / S4 / S5** by closing the standard translation over the current world under the frame axioms — `frame_axioms → ∀w ST(φ)(w)` — and asking the Z3 validity oracle. The nominal constants stay free, and first-order validity quantifies free constants universally: that is exactly "for every nominal assignment". First-order validity is only semi-decidable in general, but H(@) over K is **decidable** and these translation images are small enough that Z3 settles them instantly; `True` is always a real proof.

The standard H(@) validities all come out true over **K**:

```python
from unicode_fol_kit import hybrid_is_valid

hybrid_is_valid(mp.parse("@i i"))                          # → True  (i holds at the world named i)
hybrid_is_valid(mp.parse("@i P ↔ ¬@i ¬P"))               # → True  (@ is self-dual: one target world)
hybrid_is_valid(mp.parse("@i (P → Q) → (@i P → @i Q)"))  # → True  (@ is a normal modality)
hybrid_is_valid(mp.parse("@i j ↔ @j i"))                  # → True  (world equality is symmetric)
hybrid_is_valid(mp.parse("@i @j P ↔ @j P"))               # → True  (an @ discards any outer jump)
hybrid_is_valid(mp.parse("(i ∧ P) → @i P"))               # → True  (if HERE is i, P here is P at i)
hybrid_is_valid(mp.parse("(◇i ∧ @i P) → ◇P"))           # → True  (a successor named i witnesses ◇P)
```

… while the tempting non-theorems are refuted (each fails on a two-world model):

```python
hybrid_is_valid(mp.parse("@i P → P"))   # → False  (P at the i-world says nothing about HERE)
hybrid_is_valid(mp.parse("i"))          # → False  (a nominal fails everywhere but at its world)
hybrid_is_valid(mp.parse("P → @i P"))   # → False
hybrid_is_valid(mp.parse("◇i → □i"))   # → False  (w may see i AND a second, different world)
```

### Frame sensitivity

`frame=` constrains the **alethic** relation: `"K"` (no conditions), `"T"` (reflexive), `"S4"` (reflexive + transitive), `"S5"` (reflexive + symmetric + transitive). The frame schemas keep their usual behaviour with nominals mixed in — the T schema with a nominal conjoined still needs reflexivity, and the 4 schema pinned to a named world still needs transitivity:

```python
f = mp.parse("(□P ∧ i) → P")            # the T schema, with a nominal conjoined
hybrid_is_valid(f, frame="K")            # → False  (a dead-end world named i refutes it)
hybrid_is_valid(f, frame="T")            # → True   (reflexivity delivers P at w itself)

g = mp.parse("@i (□P → □□P)")           # the 4 schema AT the world named i
hybrid_is_valid(g, frame="T")            # → False  (reflexivity alone is not enough)
hybrid_is_valid(g, frame="S4")           # → True   (transitivity validates 4 — anywhere, so also at i)
```

On pure modal input (no nominals) `hybrid_is_valid` agrees with the native tableau `is_modal_valid` ({doc}`modal`) — the tests cross-check the two oracles on the standard schemas.

## The honest boundary

- **The `↓` binder is deliberately out of scope.** Full hybrid logic adds `↓x φ` ("name the current world x and continue"), which makes validity **undecidable**; H(@) without it stays decidable. There is no `↓` node in the kit.
- **The modal tableau rejects hybrid input** — cleanly, never with a wrong verdict. A labelled tableau would need extra rules to honour a nominal's name-exactly-one-world constraint (treating it as an ordinary atom would wrongly refute `@i i`), so `is_modal_valid`, `modal_decide`, `modal_prove`, `modal_countermodel`, and `modal_tableau_closed` all raise on nominals:

```python
from unicode_fol_kit import is_modal_valid

is_modal_valid(mp.parse("@i P → P"))
# raises NotImplementedError: … hybrid constructs (nominals/@) are not supported
# by the modal tableau; use hybrid_is_valid or a KripkeModel.
```

- **The direct classical exporters reject too** (`Nominal(…).to_z3()` and friends raise): a nominal is world-relative, so the *sanctioned* routes into classical reasoning are the standard translation and `hybrid_is_valid`.

For the plain modal machinery these constructs extend — Kripke models, the standard translation, the tableau, frames — see {doc}`modal`; for quantified modal logic see {doc}`quantified-modal`.
