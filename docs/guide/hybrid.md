# Hybrid logic H(@) — naming worlds

Plain modal logic can say *"somewhere accessible, P holds"* (`◇P`) — but it cannot say **where**. Hybrid logic H(@) closes that gap with two constructs that parse in the modal mode (`MSFLParser(modal=True)`):

- a **nominal** `i` — an atomic formula true at *exactly one* world, thereby naming it;
- the **satisfaction operator** `@i φ` — "at the world named `i`, `φ` holds", evaluated *there* no matter where you currently stand.

Together they buy things plain modal logic cannot express: asserting facts about a *specific* world from anywhere (`@i P`), asserting **world equality** (`@i j` — "the worlds named `i` and `j` are the same"), and pinning frame properties to named points (`(◇i ∧ @i P) → ◇P`). H(@) over **K** stays decidable. Adding the **↓** binder (`↓x.φ` — "name the current world `x`, then continue") gives the full hybrid language **H(@,↓)**, which the kit also supports, through three separate, honestly-scoped routes rather than one bare-bool check — see {ref}`full-hybrid-logic-h-the-binder` below.

## Syntax

| construct | Unicode | AST node | meaning |
| --- | --- | --- | --- |
| nominal | `i` (a bare term-valued identifier in formula position — same shape as a variable or constant, any script, never uppercase-initial) | `Nominal("i")` | true at exactly the world named `i` |
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

- **The modal tableau rejects hybrid input** — cleanly, never with a wrong verdict. A labelled tableau would need extra rules to honour a nominal's name-exactly-one-world constraint (treating it as an ordinary atom would wrongly refute `@i i`), so `is_modal_valid`, `modal_decide`, `modal_prove`, `modal_countermodel`, and `modal_tableau_closed` all raise on nominals:

```python
from unicode_fol_kit import is_modal_valid

is_modal_valid(mp.parse("@i P → P"))
# raises NotImplementedError: … hybrid constructs (nominals/@) are not supported
# by the modal tableau; use hybrid_is_valid or a KripkeModel.
```

- **The direct classical exporters reject too** (`Nominal(…).to_z3()` and friends raise): a nominal is world-relative, so the *sanctioned* routes into classical reasoning are the standard translation and `hybrid_is_valid`.

For the plain modal machinery these constructs extend — Kripke models, the standard translation, the tableau, frames — see {doc}`modal`; for quantified modal logic see {doc}`quantified-modal`.

(full-hybrid-logic-h-the-binder)=
## Full hybrid logic H(@,↓): the ↓ binder

`↓x.φ` **binds the state variable `x` to the CURRENT world**, then evaluates `φ` — which may refer back to `x`, exactly the way it would refer to a nominal, via a bare occurrence or `@x`. This is strictly more expressive than H(@): a plain nominal names a world *fixed in advance by the model*, but `↓x` names *whichever world evaluation happens to be visiting right now* — so `↓x.□¬x` ("name here `x`; every successor differs from `x`") states **irreflexivity of the current world** as a single formula, something no fixed nominal assignment can express. `↓x` parses and renders like any other binder (`AST` node `Down`, grammar level `quantifier`, same precedence as `∀`/`∃`):

```python
from unicode_fol_kit import MSFLParser, KripkeModel, satisfies_modal, standard_translation

mp = MSFLParser(modal=True)

irreflexive = mp.parse("↓x.□¬x")
irreflexive
# → Down(variable=Nominal(name='x'), formula=Box(formula=Not(formula=Nominal(name='x'))))
irreflexive.to_unicode_str()          # → '↓x.□¬x'   (round-trips: mp.parse(...) == irreflexive)

m = KripkeModel({0, 1}, {"alethic": {(0, 1), (1, 1)}})   # world 1 has a self-loop, world 0 does not
satisfies_modal(irreflexive, m, 0)    # → True   (world 0 has no self-loop)
satisfies_modal(irreflexive, m, 1)    # → False  (world 1 DOES have one)
```

Adding `↓` to H(@) gives full **H(@,↓)**, whose validity is **UNDECIDABLE** (Areces, Blackburn & Marx 1999) — but the standard translation stays *meaning-preserving* for it (this is exactly the theorem that defines the "bounded fragment"), so nothing here silently approximates: each of the three routes below is honest about exactly what it can and cannot decide, instead of collapsing PROVED/REFUTED/UNKNOWN into one bare bool the way `hybrid_is_valid` safely can for the *decidable* H(@) fragment.

### Three routes, honestly scoped

| route | what it decides | never wrong about |
| --- | --- | --- |
| `satisfies_modal` (route A) | truth of `↓`, at a GIVEN finite model | everything — the ground truth; always terminates |
| `down_is_valid(formula, frame=…)` (Z3) | validity — **PROVED only** | a `PROVED` verdict (sound: depends only on Z3's soundness, never on completeness for this undecidable fragment) |
| `atp.kripke_enum.KripkeEnumBackend` / `modal_enum_search` (bounded search) | validity — **REFUTED only** | a `REFUTED` verdict (every countermodel is independently re-checked with `satisfies_modal`); exhausting the search is *never* a validity proof |

```python
from unicode_fol_kit.fol.modal_translation import down_is_valid
from unicode_fol_kit.atp.kripke_enum import modal_enum_search
from unicode_fol_kit.atp.hybrid_down import down_decide

standard_translation(irreflexive).to_unicode_str()
# → '∀w0 (R(w, w0) → ¬w0 = w)'   -- exactly the FO irreflexivity condition, hand-derivable

down_is_valid(irreflexive, frame="K").status      # → 'unknown'  (K does not force irreflexivity)

reflexive = mp.parse("↓x.◇x")
down_is_valid(reflexive, frame="T").status         # → 'proved'   (T IS reflexive, by definition)
down_is_valid(reflexive, frame="K").status          # → 'unknown'  (never REFUTED — see its own docstring)

result = modal_enum_search(reflexive, frame="K", max_worlds=2)
result.model                                        # → KripkeModel(worlds={0}, relations={'alethic': set()}, …)
satisfies_modal(reflexive, result.model, 0)         # → False   (independently re-verified — a genuine countermodel)

# down_decide runs down_is_valid first, then KripkeEnumBackend if needed, and
# returns whichever route actually settled the question:
down_decide(reflexive, frame="K", max_worlds=2).status   # → 'refuted'
```

`↓x.(@x p ↔ p)` is a tautology over **every** frame/valuation (worked out by hand: `@x` re-anchors at `x`, and `↓x` just bound `x` to the *current* world — so "`p` at `x`" and bare "`p`" ask the identical question); `↓x.↓x.φ` makes the outer binding entirely inert (the inner `↓x` rebinds first); `↓x.(P ∧ ↓y.@x Q)` (`y ≠ x`) shows the inner binder canNOT capture the outer `@x`. `tests/test_hybrid_down.py` checks all of these — including a brute-force sweep over every relation/valuation on 1–3 worlds, cross-checked against an independent, from-scratch reference evaluator, not just `satisfies_modal` agreeing with itself.

### `↓` is refused, by name, wherever it cannot be decided

Every route that is only sound because it is scoped to a *decidable* fragment refuses a `↓`-formula explicitly, rather than silently deciding a larger logic than it was built for: `hybrid_is_valid` (its bare-bool contract needs H(@)'s decidability — see its own docstring), the modal tableau's five entry points (`is_modal_valid` / `modal_decide` / `modal_prove` / `modal_countermodel` / `modal_tableau_closed`), `fol.qml` (`qml_translate` / `qml_is_valid` / `to_thf_modal`), and the HOL/THF shallow embeddings (`hol.isabelle_modal.to_isabelle_modal`, `hol.thf_modal.to_thf_modal_full`, `hol.ho_modal`'s third-order routes):

```python
from unicode_fol_kit.fol.modal_translation import hybrid_is_valid

hybrid_is_valid(irreflexive)
# raises NotImplementedError: hybrid_is_valid: the ↓ binder (Down) makes hybrid
# validity undecidable, so this bare-bool, PROVED-and-REFUTED-conflating check
# cannot honestly answer for it. Use down_is_valid …
```

`Down(…).to_z3()` / `.to_prover9()` / `.to_tptp()` raise the same way, naming `down_is_valid` / `KripkeEnumBackend` as the sanctioned routes. `standard_translation` itself does NOT raise on `↓` — it threads a `↓`-bound name to the current-world term (no fresh quantifier introduced), which is exactly what makes `down_is_valid` possible in the first place.
