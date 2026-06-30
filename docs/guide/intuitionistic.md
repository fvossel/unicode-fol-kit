# Intuitionistic logic

Intuitionistic propositional validity is **decided** by Kripke-model search; the first-order fragment (0.9.0) is a sound, bounded counter-model search over increasing-domain Kripke models. The same (in)validities are confirmed by the **LJ** sequent-calculus checker and by the Gödel–McKinsey–Tarski embedding into S4.

Intuitionistic logic drops the law of excluded middle and double-negation elimination. Its models are **Kripke models**: a partial order of *worlds* (stages of knowledge) with a monotone forcing relation (once an atom is forced at a world it stays forced at every later world). The connectives `→` and `¬` quantify over future worlds, which is exactly what makes `P ∨ ¬P` and `¬¬P → P` fail.

The toolkit gives you three independent, cross-checking views of the same logic:

| View | Function(s) | Module |
| --- | --- | --- |
| Kripke-model search (decides propositional; bounded FO) | `int_valid`, `int_countermodel`, `IntKripkeModel` | `unicode_fol_kit.semantics.intuitionistic` |
| LJ sequent-calculus proof checker | `check_lj_proof`, `verify_lj_proof` | `unicode_fol_kit.atp.lj` |
| Gödel–McKinsey–Tarski embedding into S4 | `gmt_translate` | `unicode_fol_kit.hol` |

All three are exercised below against the same battery of formulas.

## Propositional validity and counter-models

`int_valid(formula)` returns a bool; `int_countermodel(formula)` returns either `None` (when the formula is valid) or a pair `(model, world)` — an `IntKripkeModel` and the index of a world that fails to force the formula. For a propositional formula the search is a genuine **decision procedure**: intuitionistic propositional logic has the finite-model property, so the search over Kripke models up to `max_worlds` worlds (default 3) is exhaustive, and `None` proves validity.

```python
from unicode_fol_kit import MSFLParser, int_valid, int_countermodel, IntKripkeModel

p = MSFLParser().parse  # parser uses Unicode operators: →  ¬  ∧  ∨  ∀  ∃

int_valid(p("P ∨ ¬P"))               # → False   excluded middle (LEM)
int_valid(p("¬¬P → P"))              # → False   double-negation elimination (DNE)
int_valid(p("((P → Q) → P) → P"))    # → False   Peirce's law

int_valid(p("P → ¬¬P"))              # → True    double-negation *introduction*
int_valid(p("¬¬(P ∨ ¬P)"))           # → True    LEM is not refutable
int_valid(p("P → P"))                # → True
```

A wider battery sharpens the boundary. Everything classical *and* constructive survives;
the casualties are exactly the principles that need a "from now on it's decided" jump:

```python
# survive (intuitionistically valid)
int_valid(p("¬(P ∧ ¬P)"))                       # → True    non-contradiction
int_valid(p("P → (Q → P)"))                     # → True    weakening (K combinator)
int_valid(p("(P → (Q → R)) → ((P → Q) → (P → R))"))  # → True    S combinator
int_valid(p("¬¬¬P → ¬P"))                       # → True    triple negation collapses
int_valid(p("¬P → ¬¬¬P"))                       # → True
int_valid(p("(¬P ∨ ¬Q) → ¬(P ∧ Q)"))           # → True    one De Morgan direction
int_valid(p("¬(P ∨ Q) → (¬P ∧ ¬Q)"))           # → True    a full De Morgan law
int_valid(p("(¬P ∧ ¬Q) → ¬(P ∨ Q)"))           # → True

# fail (classical but not constructive)
int_valid(p("¬(P ∧ Q) → (¬P ∨ ¬Q)"))           # → False   the other De Morgan
int_valid(p("(P → Q) ∨ (Q → P)"))              # → False   Dummett's linearity axiom
int_valid(p("¬¬P → P"))                         # → False   DNE again, for contrast
```

### The constructive/classical fault line

A few more contrasts pin down *which way* the constructive content runs. Implication-based
laws survive in the direction that builds a witness and fail in the direction that would
have to extract one from a negation:

```python
# survive — these never demand a decision
int_valid(p("(P → Q) → (¬Q → ¬P)"))             # → True    contraposition (forward)
int_valid(p("((P ∧ Q) → R) → (P → (Q → R))"))   # → True    currying / import-export
int_valid(p("(P → (Q → R)) → ((P → Q) → (P → R))"))  # → True    Frege's axiom
int_valid(p("(P ∧ ¬P) → Q"))                    # → True    ex falso quodlibet

# fail — these would have to *decide* P to build the consequent
int_valid(p("(¬Q → ¬P) → (P → Q)"))             # → False   contraposition (reverse)
int_valid(p("¬P ∨ ¬¬P"))                        # → False   weak excluded middle (WEM)
```

### Glivenko's theorem: double-negation rescues every classical tautology

Glivenko's theorem says that for **propositional** logic, a formula `φ` is classically
valid iff `¬¬φ` is intuitionistically valid. So every classical tautology that *fails*
constructively comes back to life under a double negation — the search confirms each one:

```python
int_valid(p("¬¬(P ∨ ¬P)"))                      # → True    ¬¬LEM
int_valid(p("¬¬(((P → Q) → P) → P)"))           # → True    ¬¬Peirce
int_valid(p("¬¬(¬¬P → P)"))                     # → True    ¬¬DNE
int_valid(p("¬¬(¬(P ∧ Q) → (¬P ∨ ¬Q))"))        # → True    ¬¬(bad De Morgan)
```

This is also a fast sanity check on `int_valid`: any formula for which `int_valid(φ)` is
`False` but `int_valid(¬¬φ)` is `True` is precisely a classical-but-not-constructive law.

### Exploring the role of `max_worlds`: when is a refutation possible?

The number of worlds a refutation needs is informative. A **single** world behaves
classically (the future is empty), so every counter-model must grow past it. LEM, DNE and
Peirce fall in **two** worlds, while Dummett's `(P → Q) ∨ (Q → P)` and the failing De
Morgan need a genuine **fork** of three — hence the default `max_worlds=3`:

```python
int_valid(p("P ∨ ¬P"), max_worlds=1)            # → True   one world is classical
int_valid(p("P ∨ ¬P"), max_worlds=2)            # → False  two-world chain refutes it

int_valid(p("(P → Q) ∨ (Q → P)"), max_worlds=2) # → True   no 2-world counter-model
int_valid(p("(P → Q) ∨ (Q → P)"), max_worlds=3) # → False  a 3-world fork refutes it
```

This parameter lets you probe *exactly* what frame shapes a refutation needs. Formulas that
become invalid at `max_worlds=2` but pass every 1-world model require a **chain**; formulas
that survive `max_worlds=2` and only fall at `max_worlds=3` require **branching**.

```python
# Need exactly a 2-world chain (classical in one world, refuted in two)
int_valid(p("¬¬P → P"), max_worlds=1)           # → True
int_valid(p("¬¬P → P"), max_worlds=2)           # → False  needs growth beyond the root
int_valid(p("((P → Q) → P) → P"), max_worlds=1) # → True   Peirce survives one world
int_valid(p("((P → Q) → P) → P"), max_worlds=2) # → False  refuted by a 2-world chain

# Need a 3-world fork (a chain is not enough)
int_valid(p("¬(P ∧ Q) → (¬P ∨ ¬Q)"), max_worlds=2) # → True   no chain counter-model
int_valid(p("¬(P ∧ Q) → (¬P ∨ ¬Q)"), max_worlds=3) # → False  a fork separates ¬P from ¬Q
```

Because intuitionistic propositional logic has the finite-model property, *every*
non-theorem eventually falls for a large enough `max_worlds`; raising the bound never turns
a `False` back into `True`. Lowering it below what a refutation needs is the only thing that
yields a (spurious) `True` for a propositional non-theorem.

### Unpacking a counter-model: why a formula fails

Each invalidity comes with an explicit `IntKripkeModel`. An `IntKripkeModel` carries three
fields: `upset[w]` is the set of worlds reachable from `w` (its up-set in the order,
including `w` itself), `valuation[key]` is the up-closed set of worlds forcing the atom
`key`, and `domains` is `None` for a propositional model. The canonical two-world refutation
of LEM, DNE and Peirce is the same chain: a root that knows nothing and one later world that
has learned `P`.

```python
model, world = int_countermodel(p("¬¬P → P"))

world                 # → 1                 the world (the root) that fails to force it
dict(model.upset)     # → {0: frozenset({0}), 1: frozenset({0, 1})}
dict(model.valuation) # → {'P': frozenset({0})}     P is forced only at world 0
model.domains         # → None              propositional model, no per-world domains
```

The root is `world 1`: it sees `{0, 1}` (itself and the later world 0), while `world 0` is a
leaf seeing only itself. Read the chain bottom-up — `world 1 ⊑ world 0`, and `P` is forced
exactly at the later `world 0`. You can replay the forcing clauses directly with
`model.forces(world, formula)`:

```python
model.forces(0, p("P"))            # → True    the later world has learned P
model.forces(1, p("P"))            # → False   the root knows nothing yet

# ¬¬P holds at the root: P can never be *refuted* (it becomes true at world 0) ...
model.forces(1, p("¬¬P"))          # → True
# ... yet P itself is not forced there, so ¬¬P → P fails at the root.
model.forces(1, p("¬¬P → P"))      # → False
model.forces(0, p("¬¬P → P"))      # → True    but it does hold at the leaf
```

The same chain refutes LEM and Peirce — only the atoms differ — which is why all three share
one frame:

```python
for goal in ["P ∨ ¬P", "¬¬P → P", "((P → Q) → P) → P"]:
    model, world = int_countermodel(p(goal))
    print(goal, "fails at", world, "| upset", dict(model.upset))
# → P ∨ ¬P fails at 1 | upset {0: frozenset({0}), 1: frozenset({0, 1})}
# → ¬¬P → P fails at 1 | upset {0: frozenset({0}), 1: frozenset({0, 1})}
# → ((P → Q) → P) → P fails at 1 | upset {0: frozenset({0}), 1: frozenset({0, 1})}
```

At the root of the LEM counter-model neither `P` nor `¬P` holds — `P` is not yet forced, and
`¬P` fails because `P` *will* be forced at the reachable `world 0` — so the disjunction is
unforced:

```python
model, world = int_countermodel(p("P ∨ ¬P"))
model.forces(world, p("P"))        # → False
model.forces(world, p("¬P"))       # → False   a later world forces P, so ¬P is refuted
model.forces(world, p("P ∨ ¬P"))   # → False   neither disjunct holds at the root
```

A valid formula has no counter-model, so `int_countermodel` returns `None` and `int_valid`
is its `is None` test:

```python
int_countermodel(p("P → P"))       # → None
int_countermodel(p("¬(P ∧ ¬P)"))   # → None
```

### Building a Kripke model by hand

You can also construct an `IntKripkeModel` directly and interrogate it — useful for teaching
or for checking a specific frame. The frame below is the canonical LEM/DNE refuter, written
with an explicit root `0 ⊑ 1` and `P` learned at the later world `1`:

```python
m = IntKripkeModel(
    upset={0: frozenset({0, 1}), 1: frozenset({1})},  # 0 is the root, 0 ⊑ 1
    valuation={"P": frozenset({1})},                  # P forced only at world 1
)

m.forces(0, p("P"))           # → False   the root has not learned P
m.forces(1, p("P"))           # → True
m.forces(0, p("¬¬P"))         # → True    P is unrefutable from the root
m.forces(0, p("¬¬P → P"))     # → False   so DNE fails here
m.forces(0, p("P ∨ ¬P"))      # → False   and so does LEM
```

## First-order intuitionistic logic

When a formula contains `∀x` / `∃x`, the search switches to *increasing-domain* Kripke
models: each world has a domain of individuals, domains only grow along the order, and
`w ⊩ ∀x φ` quantifies over every later world *and* every individual existing there. This is a
**bounded** search (the formula's constants plus `domain_elements` fresh individuals, up to
`max_steps` valuations): a returned counter-model genuinely refutes validity, but a clean
search does **not** prove validity — first-order intuitionistic logic is undecidable.

The first-order analogues of LEM and the `∃`-introducing De Morgan law fail, just as in the
propositional case:

```python
int_valid(p("∀x (P(x) ∨ ¬P(x))"))     # → False   FO excluded middle
int_valid(p("¬∀x P(x) → ∃x ¬P(x)"))   # → False   "not all" does not yield a witness
```

Their constructive duals — the ones that only *consume* a witness or push a negation
inward — survive:

```python
int_valid(p("∃x ¬P(x) → ¬∀x P(x)"))   # → True    a witness refutes the universal
int_valid(p("¬∃x P(x) → ∀x ¬P(x)"))   # → True    no witness ⇒ each instance is refuted
```

A first-order counter-model carries per-world `domains`. The refuter of FO excluded middle
mirrors the propositional chain: one individual `_e0` exists throughout, and the predicate
`P(_e0)` is only learned at the later world:

```python
model, world = int_countermodel(p("∀x (P(x) ∨ ¬P(x))"))

world                                      # → 1
dict(model.upset)                          # → {0: frozenset({0}), 1: frozenset({0, 1})}
{w: sorted(d) for w, d in model.domains.items()}   # → {0: ['_e0'], 1: ['_e0']}
{k: sorted(v) for k, v in model.valuation.items()} # → {'P(_e0)': [0]}
```

Read it the same way: the root (`world 1`) has the individual `_e0` but has not yet learned
`P(_e0)` (which becomes forced at `world 0`), so `P(_e0) ∨ ¬P(_e0)` is unforced and the
universal fails.

### The double-negation shift — a bounded-search caveat

The **double-negation shift** `(∀x ¬¬P(x)) → ¬¬(∀x P(x))` is *not* an intuitionistic
theorem, yet all of its counter-models are **infinite** — it is valid in every *finite*
Kripke model. The bounded search therefore reports no counter-model, which (for a
first-order formula) means only "none within the bounds", *not* a proof of validity:

```python
# NOT actually an intuitionistic theorem — but it has only infinite counter-models,
# so the finite, bounded search cannot exhibit one and returns True.
int_valid(p("(∀x ¬¬P(x)) → ¬¬(∀x P(x))"))   # → True   (bounded search: no finite refuter)
```

This is the one place where a `True` from `int_valid` must be read carefully: for
**propositional** formulas `True` is a decision (validity), but for **first-order** formulas
it means "no counter-model within `max_worlds` / `max_steps`". A `False`, by contrast, is
*always* backed by a concrete counter-model and is reliable in both fragments.

## LJ sequent-calculus proofs

Gentzen's **LJ** is the sequent calculus for intuitionistic logic: structurally the classical
**LK**, but with the single decisive restriction that *a sequent's succedent holds at most
one formula*. That one change blocks exactly the classical theorems above. You build a
derivation tree with `sequent`, `derive` and `axiom`, then check it with `check_lj_proof`
(bool) or `verify_lj_proof` (a `SequentResult` with `.ok`, `.endsequent`, `.error`).

```python
from unicode_fol_kit.fol.nodes import Atom, Not, And, Or, Implies, Quantifier, Variable, Constant
from unicode_fol_kit.atp.sequent import sequent, derive, axiom
from unicode_fol_kit import check_lj_proof, verify_lj_proof, render_sequent_proof

P, Q = Atom("P", ()), Atom("Q", ())
NP, NNP = Not(P), Not(Not(P))

# ⊢ P → ¬¬P   (double-negation *introduction*, an intuitionistic theorem)
proof = derive(sequent([], [Implies(P, NNP)]), "→R",
            derive(sequent([P], [NNP]), "¬R",
                derive(sequent([P, NP], []), "¬L",
                    axiom(sequent([P], [P])))))

check_lj_proof(proof)              # → True
verify_lj_proof(proof).ok          # → True
str(verify_lj_proof(proof).endsequent)   # → '⊢ P → ¬¬P'
```

`render_sequent_proof` pretty-prints the derivation tree, leaves last, with the rule name in
brackets:

```python
print(render_sequent_proof(proof))
# → ⊢ P → ¬¬P   [→R]
# →   P ⊢ ¬¬P   [¬R]
# →     P, ¬P ⊢   [¬L]
# →       P ⊢ P   [Ax]
```

Modus ponens uses the LJ `→L` rule, whose left premise `Γ ⊢ A` *replaces* the succedent (the
restriction that defeats Peirce's law):

```python
mp = derive(sequent([P, Implies(P, Q)], [Q]), "→L",
            axiom(sequent([P], [P])), axiom(sequent([P, Q], [Q])))

check_lj_proof(mp)                 # → True
print(render_sequent_proof(mp))
# → P, P → Q ⊢ Q   [→L]
# →   P ⊢ P   [Ax]
# →   P, Q ⊢ Q   [Ax]
```

Non-contradiction `⊢ ¬(P ∧ ¬P)` threads `¬R`, `∧L` and `¬L`:

```python
nc = derive(sequent([], [Not(And(P, NP))]), "¬R",
        derive(sequent([And(P, NP)], []), "∧L",
            derive(sequent([P, NP], []), "¬L",
                axiom(sequent([P], [P])))))

check_lj_proof(nc)                 # → True
print(render_sequent_proof(nc))
# → ⊢ ¬(P ∧ ¬P)   [¬R]
# →   P ∧ ¬P ⊢   [∧L]
# →     P, ¬P ⊢   [¬L]
# →       P ⊢ P   [Ax]
```

The quantifier rules pass their term / eigenvariable through `extra=`. A `∀L`
instantiation `∀x P(x) ⊢ P(c)`:

```python
x, c = Variable("x"), Constant("c")
Px = lambda t: Atom("P", [t])

fa = derive(sequent([Quantifier("∀", x, Px(x))], [Px(c)]), "∀L",
            axiom(sequent([Px(c)], [Px(c)])), extra=[c])

check_lj_proof(fa)                 # → True
print(render_sequent_proof(fa))
# → ∀x P(x) ⊢ P(c)   [∀L c]
# →   P(c) ⊢ P(c)   [Ax]
```

### What LJ rejects

The checker enforces the single-succedent restriction *first*. The classical route to
excluded middle keeps `¬P` alongside `P` in the succedent (`⊢ P, ¬P`); LJ refuses it
outright:

```python
bad_lem = derive(sequent([], [P, NP]), "¬R", axiom(sequent([P], [P])))
res = verify_lj_proof(bad_lem)
res.ok                             # → False
res.error                          # → 'intuitionistic (LJ) sequents have at most one
                                   #    succedent formula; found 2 in '⊢ P, ¬P''
```

And a derivation that *looks* single-conclusion but rests on an unjustified leaf is caught at
that leaf — here `∨R1` is fed an underivable `⊢ P` (an `Ax` with an empty antecedent):

```python
bad_em = derive(sequent([], [Or(P, NP)]), "∨R1", derive(sequent([], [P]), "Ax"))
check_lj_proof(bad_em)             # → False
verify_lj_proof(bad_em).error      # → 'Ax: the succedent formula must occur in the antecedent'
```

The soundness guarantee is two-way with the Kripke search: every formula with an accepted LJ
proof is `int_valid`, and every `int_valid` propositional formula has an LJ proof.

## Cross-check: the Gödel–McKinsey–Tarski embedding into S4

The same (in)validities are mirrored by the GMT translation, which boxes every subformula
and sends intuitionistic `φ` to a modal `S4` formula valid in `S4` iff `φ` is
intuitionistically valid. `gmt_translate` (from `unicode_fol_kit.hol`) returns the modal AST;
render it with `.to_unicode_str()`:

```python
from unicode_fol_kit.hol import gmt_translate

gmt_translate(p("P ∨ ¬P")).to_unicode_str()    # → '□P ∨ □¬□P'
gmt_translate(p("¬¬P → P")).to_unicode_str()   # → '□(□¬□¬□P → □P)'
```

The boxes on the implication and the negation are exactly the "quantify over future worlds"
that the Kripke clauses encode — which is why `□¬□¬□P → □P` is not S4-valid, matching
`int_valid(p("¬¬P → P")) == False`.
