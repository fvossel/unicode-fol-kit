# Third-order logic

`MSFLParser(third_order=True)` adds the one thing second-order syntax cannot express: a predicate whose **argument** is a predicate.

Second-order logic binds predicate variables, but a bound predicate is still only ever *applied* — `∀P (P(x) ∨ ¬P(x))`. Third-order logic lets a predicate **take a property as an argument**: `Positive(G)`, `Essence(G, x)`, `Positive(λx. ¬G(x))`. That is a change to the argument layer, not another binder, which is why no amount of extra quantification gets you there.

```python
from unicode_logic_kit import MSFLParser

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

The two third-order modes are their base modes over a widened argument layer: `third_order` accepts what `second_order` accepts plus predicate arguments, and `third_order` + `modal` accepts the whole modal family the same way; the one difference is the typing below, which reads names globally. They do not combine with `second_order` (which they contain), sorts, or fuzziness.

`api.parse_any` tries the **classical** one after `fol`, `modal` and `second_order` and before `dependence` and the sorted, fuzzy, linear and Lambek modes: it is served by the same LALR table as `second_order`, so the only inputs it newly accepts are the ones with a predicate really standing in an argument slot, and nothing previously detected as something else moves. The modal one is deliberately off the ladder — it inherits `modal`'s Earley table, and with a second-order binder also available `∀ P(x)` parses there as `∀P` over the nominal `x` instead of failing, as it does in every other dialect. Reach it explicitly with `MSFLParser(third_order=True, modal=True)`.

## Typing: what a slot holds is inferred

The surface syntax says nothing about argument types, so `analyse_signatures` works them out — **across a whole theory**, because that is the scope on which the answer is determined:

```python
from unicode_logic_kit import analyse_signatures

analyse_signatures([p("Pos(G)")]).slots
# → {'Pos': (('p', 1),), 'G': ('i',)}    ... but arity 1 was a DEFAULT

analyse_signatures([p("Pos(G)"), p("G(a, b)")]).slots
# → {'Pos': (('p', 2),), 'G': ('i', 'i')}   ... now it is determined
```

`'i'` is an individual slot; `('p', k)` a property of arity `k`. Three things are refused rather than guessed:

- a predicate applied at two arities → `ConflictingArityError`;
- one slot used for an individual *and* for a property → `MixedSlotError`, raised at parse time;
- a predicate that takes a property *and* stands in a property slot of another predicate → `NestedPropertySlotError`, raised at parse time and by `holds_to`, `to_isabelle_to`, `to_thf_to`, `isabelle_ho_modal_theory`, `to_isabelle_ho_modal` and `to_thf_ho_modal`.

```python
p("Loves(x, y) ∧ Loves(x, G)")
# raises MixedSlotError: TYPE_ERROR: argument slot 1 of 'Loves' is used both for an individual
# and for a predicate; a slot holds one or the other, not both.
```

In `Meta(Pos) ∧ Pos(G)`, `Pos` takes a property, so `Meta` would be a predicate of predicates of properties (fourth order). A slot holds an individual or a property of individuals, `('p', k)`, so that typing cannot be stated and is refused instead of being read as if `Pos` were a property of individuals. `NestedPropertySlotError` is importable, like `MixedSlotError`, from `unicode_logic_kit` and `unicode_logic_kit.fol`; all three errors are `ParsingError`s.

```python
from unicode_logic_kit import NestedPropertySlotError

p("Meta(Pos) ∧ Pos(G)")
# raises NestedPropertySlotError: TYPE_ERROR: 'Meta' takes the predicate 'Pos' as a property in argument
# slot 0, but 'Pos' itself takes a property in its argument slot 0: 'Meta' would be a predicate of
# predicates of properties (fourth order or higher). …
```

The analysis reads names globally, so a name bound by two quantifiers has to be typed alike in both: `(∀Z Z(G)) ∧ (∃Z Z(a))` is refused like the mixed slot above, and `(∀P P(a)) ∧ (∃P P(a, b))` like two arities, which `second_order=True` accepts.

One thing *is* defaulted, and reported: a property slot no evidence reaches gets arity 1, because argument position is what makes it a property slot at all and arity 0 would silently retype it as a predicate over propositions. Which slots were guessed is in `Signatures.defaulted`, and the Isabelle exporters print them as a comment in the emitted theory.

## Export: HOL takes it directly

A HOL prover has predicate arguments natively, so the export is a translation and not a simulation — one type higher than the second-order case:

```
x         : i                          an individual
G         : i ⇒ bool                   a property
Positive  : (i ⇒ bool) ⇒ bool          a predicate OF properties
Essence   : (i ⇒ bool) ⇒ i ⇒ bool      a property and an individual
```

```python
from unicode_logic_kit import to_isabelle_to, to_thf_to

print(to_isabelle_to(p("∀P (Pos(P) → P(a))"), assumptions=[p("Pos(G)"), p("G(a)")]))
print(to_thf_to(p("∀P (Pos(P) → P(a))")))
```

`to_isabelle_to` renames binders as the [second-order](second-order.md) writer does: a binder keeps its own name unless a symbol of the theory is spelled like it, and is then written `x_2`, `x_3`, …, so a quantifier never captures a constant of the same spelling. `isabelle_ho_modal_theory` does the same.

```python
clash = to_isabelle_to(p("Pos(G) ∧ G(x) ∧ ∀x Q(x)"))   # the free x is declared as a constant
"\\<forall>x_2::i." in clash   # → True   (the bound x is written x_2)
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
from unicode_logic_kit import isabelle_ho_modal_theory, HoAxiom, HoGoal

theory = isabelle_ho_modal_theory(
    "Demo",
    axioms=[HoAxiom("A", tom("∀P (Pos(P) → □Pos(P))"))],
    goals=[HoGoal("g", tom("∀P (Pos(P) → □□Pos(P))"), proof="using A by blast")],
    frame="S4",
)
```

The lifted vocabulary is emitted as Isabelle `abbreviation`s, not `definition`s, on purpose: an abbreviation is unfolded by the parser, so `blast`/`metis` see through the embedding to plain HOL instead of having to unfold it first. `mall`/`mex` are polymorphic (`('a ⇒ sigma) ⇒ sigma`), so one pair of binders serves individual and property quantification alike — the orders are distinguished by the type at the binder, which is the embedding's own point.

Frame systems come from the shared registry (`fol.frames`), so `"S5"` means here what it means everywhere else in the kit — including `GL`, `S4.1` and `Grz`, whose condition (Löb / McKinsey / Grzegorczyk) is not first-order-definable over `R`: those are stated as schemas over **propositions** rather than as conditions on `R`, exactly as `hol.isabelle_modal` states them at first order:

```python
from unicode_logic_kit import isabelle_ho_modal_theory, HoGoal

theory = isabelle_ho_modal_theory(
    "GL", (), [HoGoal("loeb", tom("□(□P→P)→□P"), proof="using R_loeb by blast")],
    frame="GL",
)
"axiomatization where R_loeb:" in theory   # → True
```

One point of style in that port: the schema's own predicate `P` is bound **explicitly** — `axiomatization where R_loeb: "∀P::sigma. ∀x. …"` — rather than left free the way `hol.isabelle_modal`'s first-order `r_loeb` is. That first-order module gets away with a free schema variable via a side convention (it lower-cases every user predicate's leading character, so a free `P` can never collide with a user symbol); this module carries no such convention, and doesn't need one for a structural reason instead: `isabelle_ho_modal_theory` always emits the frame axioms *before* the signature's `consts` declarations, so a formula's own `Positive`/`Ess`/`P` is never yet declared as a constant at the point the frame schema is elaborated — Isabelle turns the frame axiom's free `P` into a schematic variable of that statement rather than resolving it to anything, which is exactly the generalisation an explicit `∀P` gives directly (confirmed live: reversing that order, so a user's `P` is declared first, does let a free schema variable stick to it and stall a proof for an unrelated proposition). The explicit binder is kept anyway as defense-in-depth against that emission order ever changing, and because it makes the schema's universal scope visible in the source text; the THF export states the same schema with an explicit `! [P: mu > $o]` for the same reason. On the THF side a user's own `P` could not collide with it anyway: THF constants have to be lower words (an upper-case initial makes a token a variable), so the exporters spell every free symbol as one — `P` becomes `p`, `Positive` becomes `positive` — renaming apart symbols that would coincide (`Pos` and `pos`) and any that would take one of the embedding's own names (`r`, `mu`, `mbox`, …).

The embedding carries the whole non-counterfactual modal family the parser accepts: alethic `□`/`◇`, agent-indexed `K_a`/`B_a`/`Say_a`/`Want_a` (epistemic/doxastic/assertive/bouletic), deontic `Ⓞ`/`Ⓟ` (serial), temporal `Ⓖ`/`Ⓕ`/`Ⓝ`/`Ⓤ`/`⒮` and their past mirrors `⒣`/`⒫`/`⒴`, and hybrid nominals/`@`. `systems=` optionally constrains one or more of the four agent-indexed relations, the same way `frame=` constrains the alethic one:

```python
theory = isabelle_ho_modal_theory(
    "Epistemic", (),
    [HoGoal("t_thm", tom("K_a Pos(G) → Pos(G)"), proof="using Rk_refl by blast")],
    systems={"epistemic": "T"},
)
"mknows" in theory and "Rk_refl" in theory   # → True
```

Two things stay refused **by name**: the Lewis counterfactuals `Would`/`Might` (`□→`/`◇→`), which read a similarity ordering of worlds rather than an accessibility relation — see `hol.isabelle_conditional` — and the group-epistemic operators `EverybodyKnows`/`DistributedKnowledge`/`CommonKnowledge` (`C_G` would need a transitive closure this embedding does not attempt).

### Domain regime: `mode=`

`mode=` (default `"constant"`, i.e. possibilist — unchanged from before this parameter existed) accepts `"varying"`/`"increasing"`/`"cumulative"`/`"decreasing"`, the same actualist vocabulary `hol.isabelle_modal` uses at first order. An actualist mode `existsAt`-guards INDIVIDUAL quantification (a plain `∀x`/`∃x`) — but **not** property quantification (`∀P`/`∃P`), which stays `mall`/`mex`, constant across worlds, in every mode. That is the one genuinely new judgment call this port makes: first order has no property quantifier to decide about, and the ontological-argument literature treats a property (unlike an individual) as not something that comes and goes with a world's domain.

```python
barcan = tom("∀x □∀y (Pos(G) → G(x))")
constant = isabelle_ho_modal_theory("Dom", (), [HoGoal("g", barcan)])
varying = isabelle_ho_modal_theory("Dom", (), [HoGoal("g", barcan)], mode="varying")
"mall (\\<lambda>x::i." in constant     # → True  (default: unguarded, as before)
"mforall (\\<lambda>x::i." in varying  # → True  (actualist: existsAt-guarded)
"existsAt" in varying, "existsAt" in constant   # → (True, False)
```

Faithfulness to the domain regime is checked against the first-order embedding's own `qml_is_valid`: the classic Barcan formula and its converse diverge across `"constant"`/`"varying"`/`"increasing"`/`"decreasing"` exactly the same way at both orders, live-checked in `tests/test_ho_modal_actualist.py`.

## Gödel's ontological argument, both readings

`hol.goedel` is the machinery's proving ground, and the axioms are written in the kit's own syntax:

```python
from unicode_logic_kit.hol.goedel import axiom_texts, goedel_theory, check_variant

axiom_texts("scott")["A1"]   # → '∀P (Pos(λx. ¬P(x)) ↔ ¬Pos(P))'
print(goedel_theory("scott"))
```

```python
# doctest: +SKIP  — needs a local Isabelle; raises IsabelleNotAvailable without one
check_variant("scott").ok
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
from unicode_logic_kit import holds_to
from unicode_logic_kit.semantics import Structure

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

`x = 0` inside that λ is read by the evaluator as identity of domain elements, which is what makes the two interchangeable. The **exporters** are a separate question, and they do not all answer it the same way: `hol.ho_modal` (the third-order MODAL route) reads `=` between individuals as rigid identity — HOL's own `=`, no world argument, matching `fol.qml` — and refuses identity at a *property* type by name, because HOL's `=` there would silently pick necessary coextension as what "the same property" means. `hol.thirdorder` (the classical route) still renders `=` / `≠` as the uninterpreted `feq` / `fneq`, its documented convention. So a formula whose identity is meant to be identity belongs on the modal route or in `holds_to`, not in a classical third-order export.

A property named like a sort is read as that sort when the structure has a sort of the name and no table for the unary predicate, as `Human(t)` is read at first order: the property is the set of 1-tuples, one per member of the sort. A name that is no sort and has no table is the empty relation, and an empty sort, or a table that disagrees with the sort, raises `IllegalStructureError`:

```python
H = Structure((0, 1), sorts={"Human": {0}}, predicates={("Pos", 1): {(G,)}})
holds_to(p("Pos(Human)"), H)   # → True   (Human = {0}, the same relation as G)
```

Where the cost sits is worth knowing, because it is not where the syntax suggests. An individual slot ranges over the `n` domain elements and a property slot of arity `j` over the `2 ** (n ** j)` relations, so a *property* variable is cheap (`2 ** n` — 32 on a five-element domain) while a *predicate of properties* is not:

| domain `n` | monadic properties `2 ** n` | predicates of them `2 ** (2 ** n)` |
|---|---|---|
| 2 | 4 | 16 |
| 3 | 8 | 256 |
| 4 | 16 | 65 536 |
| 5 | 32 | ≈ 4.3 · 10⁹ |

`interpretation_count(signature, n)` gives that number without enumerating anything, and `MAX_INTERPRETATIONS` refuses an enumeration past ~10⁶ with a clear error rather than hanging. Beyond those sizes, Nitpick through `check_theory` is what finds finite models at this order — it is what the Gödel consistency check uses.

The evaluator is a **conservative extension**: on a second-order formula it and `satisfies_so` return the same verdict in every structure, which the test suite checks exhaustively over two-element domains rather than on samples.
