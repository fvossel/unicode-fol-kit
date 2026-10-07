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
| ILL prover (complete decision for the !-free fragment) | `ill_prove`, `ill_derivable` | `unicode_logic_kit.atp.linear` |
| ILL derivation checker | `check_ill_proof`, `verify_ill_proof` | `unicode_logic_kit.atp.linear` |
| Lambek decision procedure (L is decidable) | `lambek_prove`, `lambek_derivable` | `unicode_logic_kit.atp.lambek` |
| Lambek derivation checker | `check_lambek_proof`, `verify_lambek_proof` | `unicode_logic_kit.atp.lambek` |

Both provers return an explicit derivation tree that the corresponding checker
re-validates step by step (and does so automatically before any proof is handed
back, so a search bug can lose proofs but never invent them).

## Resources, not truths — why `A ⊬ A ⊗ A`

A sequent `Γ ⊢ C` here reads "consuming exactly the resources in `Γ` produces one
`C`". Dropping contraction and weakening makes the two classical absurdities of
resource accounting underivable: one `A` does not make two, and a resource cannot
be silently discarded.

```python
from unicode_logic_kit import MSFLParser, ill_derivable

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

## The additive units `⊤` and `𝟘`

`⊗`/`𝟙` and `&`/`⊕` each has a unit; `&` (with) and `⊕` (plus) get theirs too: `⊤` is the **additive** top — provable from *any* antecedent, no matter what — and `𝟘` is the additive bottom — an antecedent containing it proves *anything*, vacuously, since it can never actually be produced. Neither consumes or contributes resources the way `𝟙` does; they are the additive units, dual to `𝟙`/`⊥` the same way `&`/`⊕` are dual to `⊗`/`⅋`-style choice:

```python
ill_derivable([p("A")], p("⊤"))              # → True    ⊤R: provable from anything
ill_derivable([p("A"), p("𝟘")], p("B"))      # → True    0L: 𝟘 in the antecedent proves anything
```

`ill_prove` names the rules `⊤R` / `0L`:

```python
from unicode_logic_kit import ill_prove

print(ill_prove([p("A")], p("⊤")).render())
# → A ⊢ ⊤   [⊤R]
print(ill_prove([p("𝟘")], p("A ⊗ B")).render())
# → 𝟘 ⊢ (A ⊗ B)   [0L]
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
from unicode_logic_kit import ill_prove

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
from unicode_logic_kit import lambek_prove, lambek_derivable

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
lambek_prove([], q("S"))   # raises ValueError: the Lambek calculus requires a nonempty antecedent sequence ...
```

The `lambek` backend answers instead of raising: for an empty premise list it returns `unknown` with reason `unsupported`, because L has no sequent with an empty antecedent and there is nothing to decide.

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

## Isabelle export: replaying a derivation as a lemma

`hol.isabelle_substructural` does not attempt the classical-collapse export the next section rules out. Instead it takes a derivation the toolkit's *own* cut-free search already found and **replays** it in Isabelle, one `intro` rule application per tree node — no automation searches for the proof, so a successful build is a genuine, independent re-check of the search. The sequent rules themselves become an Isabelle `inductive derivable` predicate over a deep-embedded `datatype`: a **list** antecedent with an explicit `Exch` (exchange) rule for ILL (whose sequents are really multisets — the module docstring explains why list-plus-`Exch` rather than a native Isabelle multiset type), and a plain **list**, with no `Exch` at all, for Lambek — the absence is the point, since order is exactly what L tracks.

```python
from unicode_logic_kit.hol.isabelle_substructural import to_isabelle_ill, to_isabelle_lambek

thy = to_isabelle_ill([p("A"), p("A ⊸ B")], p("B"))
"inductive derivable" in thy      # → True   the deep-embedded sequent calculus
"theorem" in thy or "lemma" in thy.lower()  # → True   a real proof, not an oops hook
```

`to_isabelle_ill(premises, goal, ...)` / `to_isabelle_lambek(sequence, goal, ...)` run the toolkit's own prover internally and transcribe whatever derivation it finds; `ill_derivation_theory(derivation)` / `lambek_derivation_theory(derivation)` do the same starting from an already-computed `ILLDerivation` / `LambekDerivation` (e.g. one you inspected with `.render()` above), so you never pay for the search twice:

```python
from unicode_logic_kit import ill_prove
from unicode_logic_kit.hol.isabelle_substructural import ill_derivation_theory

d = ill_prove([p("A"), p("A ⊸ B")], p("B"))
theory = ill_derivation_theory(d)
theory == to_isabelle_ill([p("A"), p("A ⊸ B")], p("B"))   # → True   same replay either way
```

Building the theory needs a local Isabelle install (see {doc}`higher-order` for `check_theory` / `isabelle_available`); the exporter itself has no such dependency.

## What each calculus reads

Intuitionistic linear logic reads the connectives `⊗ & ⊕ ⊸ !` and the units `𝟙 ⊤ 𝟘`; the Lambek calculus reads `• \ /`. Both read them over atoms, and an atom over terms is one category (see below). Every other node is refused by name: `NotImplementedError` from `ill_prove` / `lambek_prove` and the `_derivable` functions, `unknown` with reason `unsupported` from the `ill` and `lambek` backends. The refused nodes are quantifiers, counting and cardinality nodes, sorted constants and equality atoms; the nodes of other logics (`And`, `Or`, `Not`, `Implies`, the modal, temporal, epistemic and hybrid operators, the connectives of the other calculus); the lambda layer (`Lambda`, `Application`); the truth constants of the other routes (the nullary atoms `⊤` and `⊥`, `$true` and `$false`), which neither calculus reads as a truth, ILL having the units `⊤`, `𝟙`, `𝟘` of its own and L no constants; and a term where a formula stands. `And(A, B) ⊢ A` is refused rather than answered "no derivation": it holds classically, and between the categories `And(A, B)` and `A` it has none, so any verdict would be about another formula.

```python
from unicode_logic_kit import And, Atom
from unicode_logic_kit.atp.linear import ILLDerivation, ILLSequent, verify_ill_proof
from unicode_logic_kit.atp.protocol import get_backend

conj = And(Atom("A", []), Atom("B", []))                        # a classical conjunction, not a ⊗ or a &
verdict = get_backend("ill").decide(p("A"), [conj])
(verdict.status, verdict.reason)                                # → ('unknown', 'unsupported')

bogus = ILLDerivation(ILLSequent((conj,), p("A")), "Ax", ())    # a hand-built "derivation" of  A ∧ B ⊢ A
result = verify_ill_proof(bogus)
(result.ok, result.error_rule)                                  # → (False, 'formula')
```

A derivation that holds such a node does not check: `verify_ill_proof` / `verify_lambek_proof` return `ok` False with `error_rule` `'formula'`, and `ill_derivation_theory` / `lambek_derivation_theory` raise `ValueError` for it. `to_isabelle_ill` / `to_isabelle_lambek` run the prover first and raise `NotImplementedError` for such input, as the call itself does:

```python
ill_derivable([conj], p("A"))   # raises NotImplementedError: ill_prove: the node of another logic 'A ∧ B' (And) is refused by name ...
```

The `ill` and `lambek` backends take the call's `timeout` (milliseconds) and answer `unknown` with reason `timeout` when it runs out: the search terminates, but its cost is exponential in the sequent.

```python
verdict = get_backend("lambek").decide(q("A"), [q("A")], timeout=0)   # a limit that is already over
(verdict.status, verdict.reason)                                       # → ('unknown', 'timeout')
```

### First-order input

An atom over terms (`P(alpha)`, `Loves(john, mary)`, a free variable included) is one category, identified by its predicate and its terms as written:

```python
ill_derivable([p("P(alpha)")], p("P(alpha)"))   # → True
ill_derivable([p("P(alpha)")], p("P(beta)"))    # → False   two categories: no rule replaces one term by another
```

That reading is sound in both directions: a sequent without quantifiers, counts, sorts or equality has no rule that substitutes a term for another, so its first-order derivations and its derivations over categories are the same derivations. With any of those the reading would be unsound, because one more category answers about another formula: `∀x P(x) ⊢ P(alpha)` holds in first-order linear logic (instantiation) and has no derivation between the categories `∀x P(x)` and `P(alpha)`. A sorted constant `c:S` also asserts `S(c)`, which a category drops, and `⊢ alpha = alpha` holds with identity and has no derivation between categories. So each of them is refused, not read as a category:

```python
forall_x = MSFLParser().parse("∀x P(x)")
ill_derivable([forall_x], p("P(alpha)"))   # raises NotImplementedError: ill_prove: the quantifier '∀x P(x)' (Quantifier) is refused by name ...
```

Decide such input with a first-order route (`z3`, `vampire`, `eprover`, `tableau`, `resolution`; see {doc}`classical-reasoning`).

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
