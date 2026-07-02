# Substructural logics: linear and Lambek

Intuitionistic linear logic (ILL) and the Lambek calculus **L** are logics of
**resources** rather than truths. A classical hypothesis, once established, can be
reused (contraction) or ignored (weakening) at will; a linear hypothesis is
*consumed* — used exactly once — and a Lambek hypothesis is consumed *in the order
it was given*. The toolkit parses both (`MSFLParser(linear=True)` /
`MSFLParser(lambek=True)`) and decides derivability with cut-free backward sequent
search:

| Logic | Functions | Module |
| --- | --- | --- |
| ILL prover (complete decision for the !-free fragment) | `ill_prove`, `ill_derivable` | `unicode_fol_kit.atp.linear` |
| ILL derivation checker | `check_ill_proof`, `verify_ill_proof` | `unicode_fol_kit.atp.linear` |
| Lambek decision procedure (L is decidable) | `lambek_prove`, `lambek_derivable` | `unicode_fol_kit.atp.lambek` |
| Lambek derivation checker | `check_lambek_proof`, `verify_lambek_proof` | `unicode_fol_kit.atp.lambek` |

Both provers return an explicit derivation tree that the corresponding checker
re-validates step by step (and does so automatically before any proof is handed
back, so a search bug can lose proofs but never invent them).

## Resources, not truths — why `A ⊬ A ⊗ A`

A sequent `Γ ⊢ C` here reads "consuming exactly the resources in `Γ` produces one
`C`". Dropping contraction and weakening makes the two classical absurdities of
resource accounting underivable: one `A` does not make two, and a resource cannot
be silently discarded.

```python
from unicode_fol_kit import MSFLParser, ill_derivable

p = MSFLParser(linear=True).parse   # ⊗  &  ⊕  ⊸  !  𝟙

ill_derivable([p("A")], p("A"))            # → True    a resource yields itself
ill_derivable([p("A")], p("A ⊗ A"))        # → False   no contraction: one A is not two
ill_derivable([p("A"), p("B")], p("A"))    # → False   no weakening: B cannot be discarded
```

Exchange, by contrast, *is* kept: the antecedent is a multiset, so order never
matters in ILL (that is the extra rule Lambek drops below).

## The connective tour, vending-machine style

Read `Coin ⊸ Coffee` as a vending machine: it consumes one coin and produces one
coffee. `⊸L` is exactly "insert coin":

```python
machine = p("Coin ⊸ Coffee")

ill_derivable([p("Coin"), machine], p("Coffee"))             # → True
ill_derivable([machine], p("Coffee"))                        # → False  no coin, no coffee
ill_derivable([p("Coin"), p("Coin"), machine], p("Coffee"))  # → False  the spare coin
                                                             #          cannot be discarded
```

The two conjunctions split what classical `∧` conflates. `Tea & Coffee` (*with*) is
a **menu**: both options are offered, you take exactly one. `Tea ⊗ Coffee`
(*tensor*) is a **tray**: both items, side by side, and both must be accounted for:

```python
menu = p("Tea & Coffee")
ill_derivable([menu], p("Tea"))             # → True    take either option ...
ill_derivable([menu], p("Coffee"))          # → True    ... your choice
ill_derivable([menu], p("Tea ⊗ Coffee"))    # → False   but one choice is not both

tray = p("Tea ⊗ Coffee")
ill_derivable([tray], p("Tea"))             # → False   the coffee can't be thrown away
```

`⊕` is the dual choice — the **provider** picks, you must be ready for either:

```python
ill_derivable([p("Tea")], p("Tea ⊕ Coffee"))   # → True   a Tea settles "Tea or Coffee"
ill_derivable([p("Tea ⊕ Coffee")], p("Tea"))   # → False  you don't get to pick
```

`𝟙` is the empty resource, `⊗`'s neutral element, and `⊗` commutes (exchange):

```python
ill_derivable([], p("𝟙"))                     # → True   the empty tray, for free
ill_derivable([p("A")], p("𝟙 ⊗ A"))           # → True   𝟙 ⊗ A is just A
ill_derivable([p("A ⊗ B")], p("B ⊗ A"))       # → True   multisets: ⊗L then ⊗R
```

## `!` as banking

`!A` is an **account** holding `A`s rather than a single note: the exponential
re-admits, for banked formulas only, exactly the structural rules linear logic
dropped. Dereliction (`!D`) withdraws one, contraction (`!C`) duplicates the
account, weakening (`!W`) lets an account be ignored — and promotion (`!P`) opens
an account only when everything used to produce `A` is itself banked:

```python
ill_derivable([p("!Coin")], p("Coin"))               # → True   withdraw one
ill_derivable([p("!Coin")], p("!Coin ⊗ !Coin"))      # → True   the account duplicates
ill_derivable([p("!Coin")], p("𝟙"))                  # → True   an account may sit unused
ill_derivable([p("Coin")], p("!Coin"))               # → False  one coin is not an account
```

`ill_prove` returns the derivation tree; `.render()` prints it with the rule at
each node (premises indented below their conclusion):

```python
from unicode_fol_kit import ill_prove

d = ill_prove([p("A"), p("A ⊸ B")], p("B"))
print(d.render())
# → A, A ⊸ B ⊢ B   [⊸L]
# →   A ⊢ A   [Ax]
# →   B ⊢ B   [Ax]
```

## The Lambek calculus as grammar

`MSFLParser(lambek=True)` parses the type logic of categorial grammar: atomic
categories (`NP`, `S`, …) and three connectives — `A • B` (an `A` followed by a
`B`), `A \ B` (*under*: combines with an `A` on its **left** to give a `B`) and
`B / A` (*over*: combines with an `A` on its **right** to give a `B`). On top of
linearity, L drops **exchange**: the antecedent is a sequence, and word order is
exactly what the calculus tracks.

A transitive verb like *sees* is `(NP \ S) / NP`: it first finds its object `NP`
on the right, then its subject `NP` on the left, yielding a sentence:

```python
from unicode_fol_kit import lambek_prove, lambek_derivable

q = MSFLParser(lambek=True).parse
verb = q("(NP \\ S) / NP")                             # note: \\ is \ in source

lambek_derivable([q("NP"), verb, q("NP")], q("S"))     # → True   "Alice sees Bob"
lambek_derivable([verb, q("NP"), q("NP")], q("S"))     # → False  "sees Bob Alice"
```

The derivation *is* the parse of the sentence — `/L` consumes the object, `\L` the
subject:

```python
d = lambek_prove([q("NP"), verb, q("NP")], q("S"))
print(d.render())
# → NP, (NP \ S) / NP, NP ⊢ S   [/L]
# →   NP ⊢ NP   [Ax]
# →   NP, NP \ S ⊢ S   [\L]
# →     NP ⊢ NP   [Ax]
# →     S ⊢ S   [Ax]
```

Order sensitivity is total — the same resources in the wrong arrangement fail, and
the two slashes are genuinely different types:

```python
lambek_derivable([q("A"), q("A \\ B")], q("B"))    # → True    argument on the left of \
lambek_derivable([q("A \\ B"), q("A")], q("B"))    # → False   ORDER!
lambek_derivable([q("A • B")], q("B • A"))         # → False   no exchange
lambek_derivable([q("B / A")], q("A \\ B"))        # → False   / is not \
```

The classic categorial laws come out as theorems — type lifting, composition, and
associativity of `•`:

```python
lambek_derivable([q("A")], q("B / (A \\ B)"))            # → True   type lifting
lambek_derivable([q("A")], q("(B / A) \\ B"))            # → True   (the other direction)
lambek_derivable([q("A / B"), q("B / C")], q("A / C"))   # → True   composition
lambek_derivable([q("A • (B • C)")], q("(A • B) • C"))   # → True   associativity
```

Antecedents must be **nonempty** (Lambek's restriction, the variant relevant to
grammar — a category must be assigned to at least one word):

```python
lambek_prove([], q("S"))   # raises ValueError: nonempty antecedent required
```

## Decidability status — what a `None` means

The three fragments give three different guarantees:

- **Lambek calculus: a decision procedure.** Every rule's premises are strictly
  smaller than its conclusion, so the exhaustive, memoised backward search always
  terminates, and `lambek_prove(...) is None` *proves* underivability.
- **!-free ILL: a decision procedure.** The same size argument applies, and the
  default depth bound (the sequent's total node count) can never truncate a proof,
  so `None` again proves underivability.
- **ILL with `!`: a bounded search.** Contraction (`!C`) *grows* sequents, so the
  search is depth- and step-bounded, and `None` means only "no derivation found
  within the bound" — honest, but not a refutation. Raise `max_depth` /
  `max_steps` to search deeper:

```python
ill_derivable([p("!A")], p("!A ⊗ !A"), max_depth=1)   # → False  not found within depth 1
ill_derivable([p("!A")], p("!A ⊗ !A"))                # → True   the default bound finds it
```

## The honest boundary: no classical export

Every other logic in the kit exports to Z3/Prover9/TPTP through some faithful or
documented encoding. The substructural nodes deliberately **refuse**: the only
candidate collapse (`⊗`,`&` → `∧`; `⊕` → `∨`; `⊸` → `→`; drop `!` and word order)
erases precisely the distinctions these logics exist to draw. It is *sound* — every
ILL/L theorem collapses to a classical tautology, which the test-suite verifies
against Z3 — but wildly incomplete in reverse, so shipping it as `to_z3()` would
silently classicalise your formulas:

```python
p("A ⊗ B").to_z3()
# raises NotImplementedError: Linear-logic formulas have no classical
# first-order export ... Use the sequent prover (ill_prove / ill_derivable).
```

The collapse's blind spot in one line: `A & B ⊢ A ⊗ B` is **not** ILL-derivable (a
menu is not a tray), yet its collapse `(A ∧ B) → (A ∧ B)` is classically valid.
Classical logic simply cannot see the difference — which is why these two logics
get provers of their own instead of an export.
