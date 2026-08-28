# Third-order logic

`MSFLParser(third_order=True)` adds the one thing second-order syntax cannot express: a predicate whose **argument** is a predicate.

Second-order logic binds predicate variables, but a bound predicate is still only ever *applied* — `∀P (P(x) ∨ ¬P(x))`. Third-order logic lets a predicate **take a property as an argument**: `Positive(G)`, `Essence(G, x)`, `Positive(λx. ¬G(x))`. That is a change to the argument layer, not another binder, which is why no amount of extra quantification gets you there.

```python
from unicode_fol_kit import MSFLParser

p = MSFLParser(third_order=True).parse

p("Pos(G)")                 # Atom('Pos', [PredicateTerm('G')])
p("Ess(G, a)")              # a property and an individual, in that order
p("Pos(λx. ¬G(x))")         # a λ-abstraction as the property argument
```

`PredicateTerm` is deliberately **not** a nullary `Atom`: `Atom("G", [])` is the *proposition* G, `PredicateTerm("G")` is the *property* G, and keeping them apart is exactly the distinction the third order exists to make.

Add `modal=True` for **third-order modal logic** — the setting Gödel's ontological argument is stated in:

```python
tom = MSFLParser(third_order=True, modal=True).parse
tom("∀P (Pos(P) → □Pos(P))")
tom("∀P ∀x (Ess(P, x) ↔ P(x) ∧ ∀Q (Q(x) → □∀y (P(y) → Q(y))))")
```

The two third-order modes are their base modes over a widened argument layer: `third_order` accepts exactly what `second_order` accepts plus predicate arguments, and `third_order` + `modal` accepts the whole modal family the same way. They do not combine with `second_order` (which they contain), sorts, or fuzziness.

`api.parse_any` tries the **classical** one last, after `fol`, `modal` and `second_order`: it is served by the same LALR table as `second_order`, so the only inputs it newly accepts are the ones with a predicate really standing in an argument slot, and nothing previously detected as something else moves. The modal one is deliberately off the ladder — it inherits `modal`'s Earley table, and with a second-order binder also available `∀ P(x)` parses there as a quantifier over the propositional atom `x` instead of failing as the malformed quantifier every other dialect reports. Reach it explicitly with `MSFLParser(third_order=True, modal=True)`.

## Typing: what a slot holds is inferred

The surface syntax says nothing about argument types, so `analyse_signatures` works them out — **across a whole theory**, because that is the scope on which the answer is determined:

```python
from unicode_fol_kit import analyse_signatures

analyse_signatures([p("Pos(G)")]).slots
# → {'Pos': (('p', 1),), 'G': ('i',)}    ... but arity 1 was a DEFAULT

analyse_signatures([p("Pos(G)"), p("G(a, b)")]).slots
# → {'Pos': (('p', 2),), 'G': ('i', 'i')}   ... now it is determined
```

`'i'` is an individual slot; `('p', k)` a property of arity `k`. Two things are refused rather than guessed:

- a predicate applied at two arities → `ConflictingArityError`;
- one slot used for an individual *and* for a property → `MixedSlotError`, raised at parse time.

```python
p("Loves(x, y) ∧ Loves(x, G)")
# MixedSlotError: argument slot 1 of 'Loves' is used both for an individual
# and for a predicate; a slot holds one or the other, not both.
```

One thing *is* defaulted, and reported: a property slot no evidence reaches gets arity 1, because argument position is what makes it a property slot at all and arity 0 would silently retype it as a predicate over propositions. Which slots were guessed is in `Signatures.defaulted`, and the HOL exporters print them as a comment in the emitted theory.

## Export: HOL takes it directly

A HOL prover has predicate arguments natively, so the export is a translation and not a simulation — one type higher than the second-order case:

```
x         : i                          an individual
G         : i ⇒ bool                   a property
Positive  : (i ⇒ bool) ⇒ bool          a predicate OF properties
Essence   : (i ⇒ bool) ⇒ i ⇒ bool      a property and an individual
```

```python
from unicode_fol_kit import to_isabelle_to, to_thf_to

print(to_isabelle_to(p("∀P (Pos(P) → P(a))"), assumptions=[p("Pos(G)"), p("G(a)")]))
print(to_thf_to(p("∀P (Pos(P) → P(a))")))
```

As in the second-order module these are **standard (full)** semantics: validity at this order is not semi-decidable, so a sound prover may fail on a valid conjecture. The kit emits the problem; it does not run one.

## Third-order modal: the shallow embedding

`hol.ho_modal` adds worlds the way the rest of the kit does — a proposition is a function from worlds to truth values, and every connective acts pointwise:

```
i                       individuals
world                   worlds
sigma = world ⇒ bool    propositions
i ⇒ sigma               properties
(i ⇒ sigma) ⇒ sigma     predicates of properties
```

```python
from unicode_fol_kit import isabelle_ho_modal_theory, HoAxiom, HoGoal

theory = isabelle_ho_modal_theory(
    "Demo",
    axioms=[HoAxiom("A", tom("∀P (Pos(P) → □Pos(P))"))],
    goals=[HoGoal("g", tom("∀P (Pos(P) → □□Pos(P))"), proof="using A by blast")],
    frame="S4",
)
```

The lifted vocabulary is emitted as Isabelle `abbreviation`s, not `definition`s, on purpose: an abbreviation is unfolded by the parser, so `blast`/`metis` see through the embedding to plain HOL instead of having to unfold it first. `mall`/`mex` are polymorphic (`('a ⇒ sigma) ⇒ sigma`), so one pair of binders serves individual and property quantification alike — the orders are distinguished by the type at the binder, which is the embedding's own point.

Frame systems come from the shared registry (`fol.frames`), so `"S5"` means here what it means everywhere else in the kit. Two things are refused **by name** rather than approximated: a frame whose condition is not first-order (`GL`, `S4.1`, `Grz` constrain propositions, not `R`), and every modal family but the alethic one — the parser accepts `K_a`, `Ⓞ`, `Ⓖ` because it is the same AST, and this embedding will not silently drop them.

## Gödel's ontological argument, both readings

`hol.goedel` is the machinery's proving ground, and the axioms are written in the kit's own syntax:

```python
from unicode_fol_kit.hol.goedel import axiom_texts, goedel_theory, check_variant

axiom_texts("scott")["A1"]   # → '∀P (Pos(λx. ¬P(x)) ↔ ¬Pos(P))'
print(goedel_theory("scott"))
check_variant("scott").ok    # needs a local Isabelle
```

The two variants differ in **one conjunct** and nowhere else:

```
D2 (Scott)   ∀P ∀x (Ess(P, x) ↔ P(x) ∧ ∀Q (Q(x) → □∀y (P(y) → Q(y))))
D2 (Gödel)   ∀P ∀x (Ess(P, x) ↔        ∀Q (Q(x) → □∀y (P(y) → Q(y))))
```

Under **Scott's** reading the theory discharges the argument's four steps — `T1` every positive property is possibly instantiated, `C` a God-like being is possible, `T2` God-likeness is an essence of any God-like being, `T3` necessarily a God-like being exists — plus `MC`, **modal collapse** (`φ → □φ` for every proposition), which is the argument's best-known and least comfortable consequence. It also runs Nitpick, which finds a genuine model: the axioms are consistent, so those theorems hold because they follow and not because everything does.

Under **Gödel's own** reading the theory proves `False`. Without the `P(x)` conjunct the empty property is vacuously an essence of every individual (there is no `y` with `⊥(y)`, so `□∀y (⊥(y) → Q(y))` holds outright), and necessary existence then demands the empty property be instantiated. The control is on the other side: under Scott's D2 the theory proves `Ess(P, x) → P(x)`, hence that the empty property is an essence of *nothing*. One conjunct is the whole difference — a discrepancy first noticed mechanically, by Benzmüller and Woltzenlogel Paleo in 2013.

The Isar proofs are written out by hand and shipped as text; the kit emits the theory and hands it to Isabelle. Nothing here searches for a proof, and nothing claims a result you have not run. Both theories check in about ten seconds each on a local Isabelle — which is worth stating, because the same theories with one-line automation in place of the structured proofs do not finish at all.

## Finite models: `satisfies_to`

`semantics.thirdorder` is the third-order counterpart of `satisfies_so`, and the difference is that arity is no longer enough to say what a predicate *is*: `Positive` and `G` can both have arity 1 and mean entirely different things, because `G`'s slot holds an individual and `Positive`'s holds a property. So the evaluator enumerates over each bound symbol's **signature**, which `analyse_signatures` supplies.

```python
from unicode_fol_kit import holds_to
from unicode_fol_kit.semantics import Structure

G = frozenset({(0,)})                    # the property "is 0"
S = Structure((0, 1), predicates={("G", 1): {(0,)},
                                  ("Pos", 1): {(G,)}})   # G is the one positive property

holds_to(p("Pos(G)"), S)                       # True
holds_to(p("Pos(λx. x = 0)"), S)               # True  -- same extension as G
holds_to(p("Pos(λx. x = 1)"), S)               # False
holds_to(p("∀P (Pos(P) → P(0))"), S)           # True
holds_to(p("∃Z (Z(G) ∧ ¬Z(λx. x = 1))"), S)    # a quantifier over predicates OF properties
```

A λ in argument position is evaluated to its **extension** — which is why `λx. x = 0` and `G` are interchangeable above. That is the one place a λ has a reading here; anywhere else it is refused, as are modal and Łukasiewicz nodes.

Where the cost sits is worth knowing, because it is not where the syntax suggests. An individual slot ranges over the `n` domain elements and a property slot of arity `j` over the `2 ** (n ** j)` relations, so a *property* variable is cheap (`2 ** n` — 32 on a five-element domain) while a *predicate of properties* is not:

| domain `n` | monadic properties `2 ** n` | predicates of them `2 ** (2 ** n)` |
|---|---|---|
| 2 | 4 | 16 |
| 3 | 8 | 256 |
| 4 | 16 | 65 536 |
| 5 | 32 | ≈ 4.3 · 10⁹ |

`interpretation_count(signature, n)` gives that number without enumerating anything, and `MAX_INTERPRETATIONS` refuses an enumeration past ~10⁶ with a clear error rather than hanging. Beyond those sizes, Nitpick through `check_theory` is what finds finite models at this order — it is what the Gödel consistency check uses.

The evaluator is a **conservative extension**: on a second-order formula it and `satisfies_so` return the same verdict in every structure, which the test suite checks exhaustively over two-element domains rather than on samples.
