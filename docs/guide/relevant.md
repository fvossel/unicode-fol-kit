# Relevant logic

The toolkit implements the basic affixing relevant logic **B** through the Priest–Sylvan **simplified Routley–Meyer semantics** (Priest & Sylvan 1992; Priest, *Introduction to Non-Classical Logic*, 2nd ed., ch. 10): `rel_valid` and `rel_countermodel` perform an exhaustive bounded model search, `rel_satisfies` replays the truth clauses on a `RelevantModel` you can also build by hand. The syntax is the ordinary classical propositional fragment of `MSFLParser` — `∧ ∨ ¬ → ↔` over nullary atoms — reused with relevant semantics, exactly as the [intuitionistic guide](intuitionistic.md) reuses it over Kripke models.

## Why relevance?

Classically, `A → B` is material: it holds whenever `A` is false or `B` is true, however unrelated the two are. That validates the "paradoxes of material implication" — `P → (Q → P)` (a true consequent follows from *anything*) and `(P ∧ ¬P) → Q` (*ex falso quodlibet*: a contradiction entails everything). Relevance logics insist that `→` express a genuine connection between antecedent and consequent, so both paradoxes — and with them the explosion of inconsistent theories — must fail. **B** is the weakest logic in the mainstream relevant family: what it validates, essentially all relevance logics validate.

## The simplified Routley–Meyer semantics

An interpretation is `⟨W, N, *, R, V⟩`:

- `W` — a set of worlds, with `N ⊆ W` a **nonempty** set of *normal* worlds;
- `*` — the **Routley star**, an involution on worlds (`w** = w`), interpreting negation;
- `R` — a ternary relation sourced only at *non-normal* worlds (`R ⊆ (W∖N) × W × W`), interpreting `→` there;
- `V` — a valuation mapping each atom to the set of worlds where it holds.

Truth at a world `w`:

| formula | true at `w` iff |
| --- | --- |
| `p` | `w ∈ V(p)` |
| `A ∧ B` | `w ⊨ A` and `w ⊨ B` |
| `A ∨ B` | `w ⊨ A` or `w ⊨ B` |
| `¬A` | `w* ⊭ A` |
| `A → B`, `w ∈ N` | for **all** `x ∈ W`: `x ⊨ A` ⇒ `x ⊨ B` |
| `A → B`, `w ∉ N` | for all `x, y` with `R(w, x, y)`: `x ⊨ A` ⇒ `y ⊨ B` |

`A ↔ B` abbreviates `(A → B) ∧ (B → A)`. A formula is **valid** iff it is true at every normal world of every interpretation.

Two devices do all the work. The **star** decouples the truth of `¬A` at `w` from the falsity of `A` at `w`, so a world may be *inconsistent* (`w ⊨ A` and `w ⊨ ¬A`, when `w* ⊭ A`) or *incomplete* (neither), without any global collapse. The **non-normal worlds** evaluate `→` by the ternary `R` rather than by truth-preservation, so a conditional can fail at some world even when it never leads from truth to falsity — which is exactly what refutes nested-implication paradoxes like `P → (Q → P)`.

## Validity and the headline failures

```python
from unicode_fol_kit import MSFLParser, rel_valid

p = MSFLParser().parse

# theorems of B
rel_valid(p("P → P"))                                 # → True
rel_valid(p("(P ∧ Q) → P"))                           # → True
rel_valid(p("P → (P ∨ Q)"))                           # → True
rel_valid(p("(P ∧ (Q ∨ R)) → ((P ∧ Q) ∨ (P ∧ R))"))   # → True   ∧/∨ distribution
rel_valid(p("¬¬P → P"))                               # → True   the star is an involution
rel_valid(p("P → ¬¬P"))                               # → True

# classically valid, but NOT theorems of B
rel_valid(p("P → (Q → P)"))                           # → False  positive paradox
rel_valid(p("(P ∧ ¬P) → Q"))                          # → False  explosion (ex falso)
rel_valid(p("P → (Q ∨ ¬Q)"))                          # → False  irrelevant tautological consequent
rel_valid(p("((P → Q) → P) → P"))                     # → False  Peirce's law
rel_valid(p("P ∨ ¬P"))                                # → False  LEM is not a theorem of B
rel_valid(p("((P ∨ Q) ∧ ¬P) → Q"))                    # → False  disjunctive syllogism
```

The profile is instructively different from intuitionistic logic: **B keeps both double-negation laws** (the star is an involution, so `¬¬P` and `P` hold at exactly the same worlds) **yet loses excluded middle** — a world can simply be incomplete about `P`. Intuitionistic logic rejects `¬¬P → P` and `P ∨ ¬P` alike; classical logic keeps both; B splits them. And where intuitionistic logic happily keeps `(P ∧ ¬P) → Q` and `P → (Q → P)`, B rejects them — relevance and constructivity prune classical logic along entirely different axes.

## Reading a countermodel

`rel_countermodel(φ)` returns `None` or a verified pair `(model, world)`: a `RelevantModel` together with a *normal* world of it where `φ` fails. The refutation of excluded middle is a two-world model whose star swaps the worlds:

```python
from unicode_fol_kit import rel_countermodel, rel_satisfies

model, world = rel_countermodel(p("P ∨ ¬P"))

world                  # → 'w0'    the normal world where the formula fails
model.worlds           # → ('w0', 'w1')
model.normal           # → frozenset({'w0'})
dict(model.star)       # → {'w0': 'w1', 'w1': 'w0'}    the star swaps the two worlds
model.R                # → frozenset()
dict(model.valuation)  # → {'P': frozenset({'w1'})}
```

At `w0` neither disjunct holds: `P` fails there outright (`V(P) = {'w1'}`), and `¬P` fails because its star world `w0* = w1` *does* satisfy `P`. So `w0` is an incomplete world, and the disjunction is unforced:

```python
rel_satisfies(model, "w0", p("P"))        # → False
rel_satisfies(model, "w0", p("¬P"))       # → False   w0* = w1 satisfies P
rel_satisfies(model, "w0", p("P ∨ ¬P"))   # → False
rel_satisfies(model, "w1", p("P ∨ ¬P"))   # → True    w1 satisfies P outright
```

The positive paradox falls in a model that needs neither the star nor `R` — just a `Q`-world that lacks `P`:

```python
model, world = rel_countermodel(p("P → (Q → P)"))

dict(model.star)       # → {'w0': 'w0', 'w1': 'w1'}    identity — negation plays no role
model.R                # → frozenset()
dict(model.valuation)  # → {'P': frozenset({'w0'}), 'Q': frozenset({'w1'})}

# w0 satisfies P; but Q → P fails at w0, because w1 is a Q-world without P.
rel_satisfies(model, "w0", p("P"))              # → True
rel_satisfies(model, "w0", p("Q → P"))          # → False
rel_satisfies(model, "w0", p("P → (Q → P)"))    # → False
```

Read the last three lines against the normal-world clause: `P → (Q → P)` holds at `w0` only if *every* `P`-world satisfies `Q → P`; but `w0` itself is a `P`-world at which `Q → P` fails. The truth of the consequent's *conclusion* at `w0` is beside the point — what matters is the missing connection between `Q` and `P`.

## Building a model by hand

`RelevantModel` accepts plain tuples, sets and dicts and freezes them internally (the constructor validates that `N` is nonempty, that the star is a total involution, and that `R` is sourced at non-normal worlds only). `star` defaults to the identity and `R` to empty. Here is an *inconsistent* world refuting explosion — note that `w1 ⊨ P ∧ ¬P` does **not** make everything true there:

```python
from unicode_fol_kit import RelevantModel

m = RelevantModel(
    worlds=("w0", "w1"), normal={"w0"},
    star={"w0": "w1", "w1": "w0"},        # the Routley star swaps the worlds
    valuation={"P": {"w1"}},
)

rel_satisfies(m, "w1", p("P"))               # → True
rel_satisfies(m, "w1", p("¬P"))              # → True    w1* = w0 does not satisfy P
rel_satisfies(m, "w1", p("P ∧ ¬P"))          # → True    an inconsistent world, no explosion
rel_satisfies(m, "w1", p("Q"))               # → False
rel_satisfies(m, "w0", p("(P ∧ ¬P) → Q"))    # → False   refuted at the normal world
```

Non-normal worlds refute Peirce's law by *vacuity*: with no `R`-triples sourced at `w1`, every conditional whatsoever holds there, while `P` does not:

```python
m = RelevantModel(worlds=("w0", "w1"), normal={"w0"})   # star = identity, R = ∅

rel_satisfies(m, "w1", p("(P → Q) → P"))         # → True    vacuous: no R-triples at w1
rel_satisfies(m, "w1", p("P"))                   # → False
rel_satisfies(m, "w0", p("((P → Q) → P) → P"))   # → False   Peirce fails at w0
```

## The bounded-validity contract

`rel_countermodel(φ, max_worlds=2)` searches **every** interpretation with at most `max_worlds` worlds and exactly one normal world (which is without loss of generality for countermodel existence), every involution for `*`, every `R ⊆ (W∖N) × W × W` and every valuation of `φ`'s atoms, and verifies the countermodel with `rel_satisfies` before returning it. The contract of `rel_valid` is therefore exactly that of the first-order `int_valid`:

- **`False` is definitive** — it is backed by an explicit, verified countermodel; the formula is certainly not a theorem of B.
- **`True` is bounded** — it means "no countermodel with at most `max_worlds` worlds". B is decidable, but this search is not a decision procedure: a non-theorem whose smallest refuting interpretation needs more worlds than the bound is reported valid.

The search space is exponential — roughly `2^((n−1)·n²)` ternary relations and `2^(n·a)` valuations for `n` worlds and `a` atoms. The default `max_worlds=2` checks about two thousand interpretations for a 3-atom formula (milliseconds); `max_worlds=3` already costs on the order of `10⁸` interpretations. Every headline invalidity above falls within two worlds.

One consequence of the semantics is worth internalising: a **1-world** interpretation *is* a classical valuation — the single world is normal, the only involution on it is the identity (so `¬` is classical negation) and `R` must be empty (so `→` is material implication over that world). Hence `max_worlds=1` decides *classical* validity, and B's soundness with respect to classical logic (`B ⊆ CL`) is executable:

```python
from unicode_fol_kit import is_valid

# B ⊆ CL: everything B-valid is classically valid (the Z3 oracle agrees) ...
rel_valid(p("(P ∧ Q) → P"))         # → True
is_valid(p("(P ∧ Q) → P"))          # → True

# ... and a classical countermodel IS a 1-world Routley–Meyer model:
rel_valid(p("P ∨ ¬P"), max_worlds=1)    # → True    one world behaves classically
rel_valid(p("P ∨ ¬P"), max_worlds=2)    # → False   the star needs a second world
```

### A certified positive counterpart: `isabelle_decide_relevant`

`rel_valid`'s `True` is only "no countermodel within `max_worlds`" — bounded evidence, not a proof. With a local Isabelle installed, `hol.isabelle_relevant.to_isabelle_relevant` emits the *same* simplified Routley–Meyer semantics as a shallow Isabelle embedding — `N`, `star`, `R` as uninterpreted `consts`, the well-formedness conditions bundled as a `wellformed` **premise** of the goal (not an `axiomatization`, so nitpick can build the frame itself and certify a countermodel as *genuine* rather than downgrading to `quasi_genuine`) — and `isabelle_decide_relevant(φ)` runs it: prove-battery ⇒ `VALID` (true at every normal world of every wellformed interpretation, matching `rel_valid`'s "true at every normal world" contract), else `nitpick[expect = genuine]` over the world type ⇒ `INVALID`, else `UNKNOWN`.

```python
# doctest: +SKIP
from unicode_fol_kit import MSFLParser, isabelle_decide_relevant

p = MSFLParser().parse
print(isabelle_decide_relevant(p("(P ∧ Q) → P")))
# → FolVerdict[valid (by prove-battery)]
print(isabelle_decide_relevant(p("(P → (P → Q)) → (P → Q)")))
# → FolVerdict[invalid]     (contraction — a theorem of R, genuinely not of B)
```

Same restriction as `rel_satisfies`: only the propositional connectives `¬ ∧ ∨ → ↔` over nullary atoms — no quantifiers, modalities, or `Xor` (there is no B reading for it). `rel_valid`'s bounded `True` finally has a certified positive counterpart, checked live end-to-end against the headline B-facts above during development.

## Beyond B: why the toolkit ships B

B is the *basic* affixing system: the stronger relevant logics (DW, TW, T, E, **R**, …) arise by imposing frame conditions on `R` — and each condition validates new implicational theorems. **Contraction**, for instance, holds in R but not in B, and the search exhibits the two-world reason:

```python
rel_valid(p("(P → (P → Q)) → (P → Q)"))   # → False   contraction: a theorem of R, not of B
```

So `B ⊂ R` properly. The decisive fact is Urquhart's theorem ("The undecidability of entailment and relevant implication", *J. Symbolic Logic* 49, 1984): the logics **R**, **E** and their neighbours are **undecidable**, so no terminating countermodel-or-proof search for them can exist. B, by contrast, is decidable, and its simplified semantics keeps the model search small and honest — which is why the toolkit ships B.
