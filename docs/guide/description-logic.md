# Description logic ALC

The `unicode_fol_kit.dl` subpackage (new in 0.9.0) implements **ALC**, the smallest propositionally closed description logic and the notation underlying OWL. It provides concept constructors, negation-normal-form rewriting, and a tableau reasoner that decides satisfiability, subsumption, equivalence, and ABox consistency over **general** TBoxes. Import it as `import unicode_fol_kit.dl as dl`.

## Concept constructors

A *concept* describes a set of individuals; a *role* (a plain string) describes a binary relation between them. The constructors are dataclasses in the `dl` namespace — distinct from the FOL AST's connectives.

| Constructor | Glyph | Meaning |
|---|---|---|
| `dl.Top()` | ⊤ | every individual |
| `dl.Bottom()` | ⊥ | no individual |
| `dl.Atomic("Person")` | `Person` | a primitive concept name |
| `dl.Not(C)` | ¬C | complement |
| `dl.And(C, D)` | C ⊓ D | intersection |
| `dl.Or(C, D)` | C ⊔ D | union |
| `dl.Exists("r", C)` | ∃r.C | has an `r`-successor in C |
| `dl.ForAll("r", C)` | ∀r.C | all `r`-successors are in C |

```python
import unicode_fol_kit.dl as dl

Person = dl.Atomic("Person")
parent = dl.And(Person, dl.Exists("hasChild", Person))
print(parent.to_unicode())   # → Person ⊓ ∃hasChild.Person
```

Concepts are frozen dataclasses, so they nest freely and compose like any other
value. The two roles below (`hasChild`, `hasPet`) are just strings, and ⊤/⊥ act as
the trivial top and bottom concepts:

```python
import unicode_fol_kit.dl as dl

Person = dl.Atomic("Person")
Dog    = dl.Atomic("Dog")

# someone whose children are all people and who owns at least one dog
c = dl.And(dl.ForAll("hasChild", Person), dl.Exists("hasPet", Dog))
print(c.to_unicode())   # → ∀hasChild.Person ⊓ ∃hasPet.Dog

# "has a pet at all" — ∃hasPet.⊤ — versus "owns nothing" — ∀hasPet.⊥
print(dl.Exists("hasPet", dl.Top()).to_unicode())    # → ∃hasPet.⊤
print(dl.ForAll("hasPet", dl.Bottom()).to_unicode())  # → ∀hasPet.⊥

# being frozen dataclasses, structurally equal concepts compare equal
print(dl.Atomic("Person") == dl.Atomic("Person"))    # → True
print(dl.Exists("r", dl.Top()) == dl.Exists("r", dl.Bottom()))  # → False
```

### More concept construction examples

Build richer descriptions by nesting constructors. Quantifiers can express cardinality constraints (at least one, all):

```python
import unicode_fol_kit.dl as dl

A, B, C = dl.Atomic("A"), dl.Atomic("B"), dl.Atomic("C")

# a concept with three nested quantifiers: ∃r.∀s.∃t.A
deep = dl.Exists("r", dl.ForAll("s", dl.Exists("t", A)))
print(deep.to_unicode())  # → ∃r.∀s.∃t.A

# a three-way conjunction: A ⊓ B ⊓ C
triple_and = dl.And(dl.And(A, B), C)
print(triple_and.to_unicode())  # → A ⊓ B ⊓ C

# mixed negation: (A ⊓ ¬B) ⊔ C
mixed = dl.Or(dl.And(A, dl.Not(B)), C)
print(mixed.to_unicode())  # → A ⊓ ¬B ⊔ C
```

Multiple roles can be combined. An existential restriction ties requirements to exactly one role:

```python
import unicode_fol_kit.dl as dl

Person = dl.Atomic("Person")
Happy = dl.Atomic("Happy")

# someone with at least one parent and at least one sibling
has_parents_and_siblings = dl.And(
    dl.Exists("hasParent", Person),
    dl.Exists("hasSibling", Person)
)
print(has_parents_and_siblings.to_unicode())  # → ∃hasParent.Person ⊓ ∃hasSibling.Person

# someone whose parents and siblings are all happy
all_family_happy = dl.And(
    dl.ForAll("hasParent", Happy),
    dl.ForAll("hasSibling", Happy)
)
print(all_family_happy.to_unicode())  # → ∀hasParent.Happy ⊓ ∀hasSibling.Happy
```

## Rendering

`Concept.to_unicode()` renders with the standard DL glyphs and precedence-aware parenthesisation (binding order: atoms/⊤/⊥ tightest, then ¬ / ∃ / ∀, then ⊓, then ⊔). `str(C)` is an alias.

```python
import unicode_fol_kit.dl as dl

c = dl.Or(dl.Atomic("A"), dl.And(dl.Atomic("B"), dl.Not(dl.Atomic("C"))))
print(c.to_unicode())                                  # → A ⊔ B ⊓ ¬C
print(dl.ForAll("r", dl.Or(dl.Atomic("A"), dl.Atomic("B"))).to_unicode())  # → ∀r.(A ⊔ B)
print(dl.Top().to_unicode(), dl.Bottom().to_unicode())  # → ⊤ ⊥
```

### Rendering complex expressions

Precedence rules are consistent across deeply nested expressions. Understand the precedence order to predict parenthesisation:

```python
import unicode_fol_kit.dl as dl

A, B, C, D = (dl.Atomic("A"), dl.Atomic("B"), 
              dl.Atomic("C"), dl.Atomic("D"))

# ⊔ has lowest precedence (loosest binding), so ⊔ inside ⊓ does not need parens
very_loose = dl.And(A, dl.Or(B, dl.And(C, D)))
print(very_loose.to_unicode())  # → A ⊓ B ⊔ C ⊓ D

# ⊓ is tighter than ⊔, so ⊓ inside ⊔ needs parens
tighter = dl.Or(dl.And(A, B), dl.And(C, D))
print(tighter.to_unicode())  # → A ⊓ B ⊔ C ⊓ D

# complex quantifier nesting with ⊔ and ⊓
complex_q = dl.ForAll("r", dl.Or(A, dl.Exists("s", B)))
print(complex_q.to_unicode())  # → ∀r.(A ⊔ ∃s.B)

# ¬ over quantifier needs parentheses
neg_quant = dl.Not(dl.Exists("r", A))
print(neg_quant.to_unicode())  # → ¬∃r.A
```

Parentheses appear only where precedence demands them. A ⊔ under a ⊓, a ⊓ under a ¬,
or any binary concept under a quantifier or ¬ gets wrapped; tighter structure does
not:

```python
import unicode_fol_kit.dl as dl

A, B, C = dl.Atomic("A"), dl.Atomic("B"), dl.Atomic("C")

# ⊔ is loosest, so a ⊓ inside it needs no parens, but a ⊔ inside a ⊓ does
print(dl.And(dl.Or(A, B), C).to_unicode())   # → (A ⊔ B) ⊓ C
print(dl.Or(dl.And(A, B), C).to_unicode())   # → A ⊓ B ⊔ C

# ¬ binds as tightly as a quantifier, so it parenthesises any binary operand
print(dl.Not(dl.And(A, B)).to_unicode())     # → ¬(A ⊓ B)
print(dl.Not(dl.Or(A, B)).to_unicode())      # → ¬(A ⊔ B)
print(dl.Not(A).to_unicode())                # → ¬A

# nested quantifiers chain without parentheses (they bind equally tight)
print(dl.ForAll("r", dl.Exists("s", A)).to_unicode())   # → ∀r.∃s.A
print(dl.Exists("r", dl.Not(A)).to_unicode())           # → ∃r.¬A

# str(C) is exactly to_unicode()
print(str(dl.And(A, B)))                     # → A ⊓ B
```

## Parsing concepts from strings

`dl.parse_concept(text)` is the inverse of `to_unicode()`: it reads the same glyph syntax the renderer emits (`⊤ ⊥ ¬ ⊓ ⊔ ∃r.C ∀r.C`, plus parentheses for grouping) and returns a `Concept`. `dl.parse_gci(text)` parses a **general concept inclusion** `C ⊑ D` and returns the `(sub, sup)` pair ready for `dl.subsumes(sub, sup)` or a `TBox`.

```python
import unicode_fol_kit.dl as dl

c = dl.parse_concept("∃hasChild.Person ⊓ ∀hasPet.Dog")
c.to_unicode()                          # → '∃hasChild.Person ⊓ ∀hasPet.Dog'
c == dl.And(dl.Exists("hasChild", dl.Atomic("Person")),
            dl.ForAll("hasPet", dl.Atomic("Dog")))     # → True

# ⊤ / ⊥ parse too:
dl.parse_concept("∃hasPet.⊤")           # → Exists(role='hasPet', concept=Top())
dl.parse_concept("∀hasPet.⊥")           # → ForAll(role='hasPet', concept=Bottom())

sub, sup = dl.parse_gci("Dog ⊑ Mammal")
(sub, sup)                              # → (Atomic('Dog'), Atomic('Mammal'))
dl.subsumes(sub, sup)                   # → False   (no TBox axiom says so — yet)
```

Round-trips both ways — `to_unicode()` output re-parses, and the parsed tree renders back to the same string:

```python
c2 = dl.And(dl.Or(dl.Atomic("A"), dl.Atomic("B")), dl.Not(dl.Atomic("C")))
dl.parse_concept(c2.to_unicode()) == c2     # → True
```

A malformed concept raises `dl.ConceptSyntaxError` with the offending position, rather than a bare parser exception:

```python
dl.parse_concept("Person ⊓")
# raises ConceptSyntaxError: parse_concept: unexpected end of input at position 8;
# expected '⊤', '⊥', a concept name, '¬', '∃', '∀', or '(' in 'Person ⊓'
```

## Negation normal form

`dl.nnf(C)` pushes ¬ inward so that negation occurs only on atomic concepts, using the De Morgan and modal dualities (`¬⊤=⊥`, `¬¬C=C`, `¬(C⊓D)=¬C⊔¬D`, `¬∃r.C=∀r.¬C`, `¬∀r.C=∃r.¬C`). This is the shape the tableau consumes.

```python
import unicode_fol_kit.dl as dl

neg = dl.Not(dl.Exists("r", dl.And(dl.Atomic("A"), dl.Atomic("B"))))
print(dl.nnf(neg).to_unicode())   # → ∀r.(¬A ⊔ ¬B)

print(dl.nnf(dl.Not(dl.ForAll("r", dl.Atomic("A")))).to_unicode())  # → ∃r.¬A
```

Each rewrite rule, in isolation:

```python
import unicode_fol_kit.dl as dl

A, B = dl.Atomic("A"), dl.Atomic("B")

print(dl.nnf(dl.Not(dl.Top())).to_unicode())              # → ⊥   (¬⊤ = ⊥)
print(dl.nnf(dl.Not(dl.Bottom())).to_unicode())           # → ⊤   (¬⊥ = ⊤)
print(dl.nnf(dl.Not(dl.Not(A))).to_unicode())             # → A   (¬¬C = C)
print(dl.nnf(dl.Not(dl.And(A, B))).to_unicode())          # → ¬A ⊔ ¬B
print(dl.nnf(dl.Not(dl.Or(A, B))).to_unicode())           # → ¬A ⊓ ¬B
print(dl.nnf(dl.Not(dl.Exists("r", A))).to_unicode())     # → ∀r.¬A
print(dl.nnf(dl.Not(dl.ForAll("r", A))).to_unicode())     # → ∃r.¬A
```

Negation is driven all the way down to the atoms in a single pass, even through
deeply nested mixtures of quantifiers and connectives:

```python
import unicode_fol_kit.dl as dl

A, B = dl.Atomic("A"), dl.Atomic("B")

deep = dl.Not(dl.And(dl.Exists("r", A), dl.ForAll("s", B)))
print(dl.nnf(deep).to_unicode())   # → ∀r.¬A ⊔ ∃s.¬B

# already-positive concepts are returned structurally unchanged
already = dl.Or(A, dl.Exists("r", dl.Not(B)))
print(dl.nnf(already) == already)  # → True
```

### Additional NNF examples: complex structures

Push negation through multiple layers of quantifiers and connectives:

```python
import unicode_fol_kit.dl as dl

A, B, C = dl.Atomic("A"), dl.Atomic("B"), dl.Atomic("C")

# ¬(A ⊓ (¬B ⊔ C)) → ¬A ⊔ ¬(¬B ⊔ C) → ¬A ⊔ (¬¬B ⊓ ¬C) → ¬A ⊔ B ⊓ ¬C
complex1 = dl.Not(dl.And(A, dl.Or(dl.Not(B), C)))
print(dl.nnf(complex1).to_unicode())  # → ¬A ⊔ B ⊓ ¬C

# Negated universal over a disjunction
# ¬∀r.(A ⊔ B) → ∃r.¬(A ⊔ B) → ∃r.(¬A ⊓ ¬B)
nforall = dl.Not(dl.ForAll("r", dl.Or(A, B)))
print(dl.nnf(nforall).to_unicode())  # → ∃r.(¬A ⊓ ¬B)

# Multiple layers of quantifier negation
# ¬∃r.∀s.A → ∀r.¬∀s.A → ∀r.∃s.¬A
multi_q = dl.Not(dl.Exists("r", dl.ForAll("s", A)))
print(dl.nnf(multi_q).to_unicode())  # → ∀r.∃s.¬A
```

NNF is idempotent: applying it twice gives the same result as once:

```python
import unicode_fol_kit.dl as dl

A = dl.Atomic("A")
complex_c = dl.Not(dl.And(dl.Exists("r", A), dl.ForAll("s", A)))

nnf1 = dl.nnf(complex_c)
nnf2 = dl.nnf(nnf1)
print(nnf1 == nnf2)  # → True
print(nnf1.to_unicode())  # → ∀r.¬A ⊔ ∃s.¬A
```

## Reasoning API

The reasoner is a tableau with **TBox internalisation** and **subset blocking**. Every reasoning function takes an optional `tbox` (default: the empty TBox).

- `dl.concept_satisfiable(C, tbox=None)` — does some model place an individual in `C` while obeying every TBox axiom?
- `dl.concept_unsatisfiable(C, tbox=None)` — its negation.
- `dl.subsumes(sub, sup, tbox=None)` — does the TBox entail `sub ⊑ sup`? Decided by the standard reduction: `sub ⊓ ¬sup` is unsatisfiable.
- `dl.equivalent(C, D, tbox=None)` — mutual subsumption, `C ≡ D`.
- `dl.abox_consistent(abox, tbox=None)` — does the knowledge base have a model?

ALC is exactly the multi-modal logic **K** — a role `r` is a modality, `∃r` its ◇ and `∀r` its □ — which is why these tasks are decidable.

```python
import unicode_fol_kit.dl as dl

A = dl.Atomic("A")
print(dl.concept_satisfiable(dl.And(A, dl.Not(A))))    # → False
print(dl.concept_satisfiable(dl.Atomic("Person")))     # → True

# ⊓-elimination is a subsumption; the converse is not
print(dl.subsumes(dl.And(A, dl.Atomic("B")), A))       # → True
print(dl.subsumes(A, dl.And(A, dl.Atomic("B"))))       # → False

# the modal duality ¬∃r.A ≡ ∀r.¬A
lhs = dl.Not(dl.Exists("r", A))
rhs = dl.ForAll("r", dl.Not(A))
print(dl.equivalent(lhs, rhs))                         # → True
```

### Satisfiability, including ⊤/⊥ and quantifier corner cases

`concept_unsatisfiable` is simply the negation of `concept_satisfiable`. ⊤ is always
satisfiable, ⊥ never; `∃r.⊥` cannot be witnessed (the successor would be in ⊥), while
`∀r.⊥` is satisfiable by an individual with *no* `r`-successors:

```python
import unicode_fol_kit.dl as dl

A = dl.Atomic("A")
print(dl.concept_satisfiable(dl.Top()))                 # → True
print(dl.concept_satisfiable(dl.Bottom()))              # → False
print(dl.concept_unsatisfiable(dl.Bottom()))            # → True

print(dl.concept_satisfiable(dl.Exists("r", dl.Bottom())))   # → False
print(dl.concept_satisfiable(dl.ForAll("r", dl.Bottom())))   # → True

# ∃r.A ⊓ ∀r.¬A forces a single r-successor to be both A and ¬A → clash
clash = dl.And(dl.Exists("r", A), dl.ForAll("r", dl.Not(A)))
print(dl.concept_satisfiable(clash))                    # → False
```

### Satisfiability with complex role patterns

Role interactions can indirectly force unsatisfiability. When existential and universal quantifiers conflict over a shared role:

```python
import unicode_fol_kit.dl as dl

A, B = dl.Atomic("A"), dl.Atomic("B")

# ∃r.A ⊓ ∀r.B is satisfiable only if A and B can overlap
overlap_sat = dl.And(dl.Exists("r", A), dl.ForAll("r", B))
print(dl.concept_satisfiable(overlap_sat))  # → True (their r-successor can be in A ⊓ B)

# but forcing A and B to be disjoint makes it unsatisfiable
disjoint = dl.And(
    dl.Exists("r", A),
    dl.ForAll("r", dl.Not(B))
)
print(dl.concept_satisfiable(disjoint))  # → False (r-successor cannot be A and ¬B)

# multiple roles do not conflict: ∃r.A ⊓ ∀s.¬A is always satisfiable
no_conflict = dl.And(
    dl.Exists("r", A),
    dl.ForAll("s", dl.Not(A))
)
print(dl.concept_satisfiable(no_conflict))  # → True (different roles, different successors)
```

### Subsumption with ⊤, ⊥, and under quantifiers

⊥ is below everything and ⊤ above everything; subsumption is also *monotone* inside
∃ and ∀ (replacing the filler by a superconcept preserves the inclusion):

```python
import unicode_fol_kit.dl as dl

A = dl.Atomic("A")
print(dl.subsumes(dl.Bottom(), A))                      # → True   (⊥ ⊑ A)
print(dl.subsumes(A, dl.Top()))                         # → True   (A ⊑ ⊤)
print(dl.subsumes(dl.Exists("r", A), dl.Exists("r", dl.Top())))  # → True
print(dl.subsumes(dl.ForAll("r", A), dl.ForAll("r", dl.Top())))  # → True
```

### Subsumption with compound concepts

Subsumption behaves classically for conjunctions and complements:

```python
import unicode_fol_kit.dl as dl

A, B, C = dl.Atomic("A"), dl.Atomic("B"), dl.Atomic("C")

# A ⊓ B ⊑ A (left elimination)
print(dl.subsumes(dl.And(A, B), A))  # → True

# A ⊑ A ⊔ B (weakening)
print(dl.subsumes(A, dl.Or(A, B)))  # → True

# ¬A ⊑ ¬B iff B ⊑ A (contrapositive)
print(dl.subsumes(dl.Not(B), dl.Not(A)))  # → True (since A ⊑ B is False)
print(dl.subsumes(B, A))  # → False

# transitivity: if A ⊑ B and B ⊑ C then A ⊑ C
print(dl.subsumes(A, B))  # → False (without TBox)
# but with a TBox (see below), transitivity holds
```

### Equivalence: De Morgan, distributivity, and quantifier laws

`equivalent(C, D)` is mutual subsumption. It captures the propositional laws as well
as the ALC-specific facts that ∃ distributes over ⊔ and ∀ over ⊓:

```python
import unicode_fol_kit.dl as dl

A, B, C = dl.Atomic("A"), dl.Atomic("B"), dl.Atomic("C")

# distributivity of ⊓ over ⊔
lhs = dl.And(A, dl.Or(B, C))
rhs = dl.Or(dl.And(A, B), dl.And(A, C))
print(dl.equivalent(lhs, rhs))                          # → True

# ∃r.(A ⊔ B) ≡ ∃r.A ⊔ ∃r.B
print(dl.equivalent(dl.Exists("r", dl.Or(A, B)),
                    dl.Or(dl.Exists("r", A), dl.Exists("r", B))))   # → True

# ∀r.(A ⊓ B) ≡ ∀r.A ⊓ ∀r.B
print(dl.equivalent(dl.ForAll("r", dl.And(A, B)),
                    dl.And(dl.ForAll("r", A), dl.ForAll("r", B))))  # → True
```

### Equivalence with negation and interaction

De Morgan's laws and modal dualities hold:

```python
import unicode_fol_kit.dl as dl

A, B = dl.Atomic("A"), dl.Atomic("B")

# De Morgan: ¬(A ⊓ B) ≡ ¬A ⊔ ¬B
print(dl.equivalent(
    dl.Not(dl.And(A, B)),
    dl.Or(dl.Not(A), dl.Not(B))
))  # → True

# Modal duality: ¬∀r.A ≡ ∃r.¬A
print(dl.equivalent(
    dl.Not(dl.ForAll("r", A)),
    dl.Exists("r", dl.Not(A))
))  # → True

# Double negation: ¬¬A ≡ A
print(dl.equivalent(dl.Not(dl.Not(A)), A))  # → True

# Duality chain: ¬∃r.∀s.A ≡ ∀r.∃s.¬A
print(dl.equivalent(
    dl.Not(dl.Exists("r", dl.ForAll("s", A))),
    dl.ForAll("r", dl.Exists("s", dl.Not(A)))
))  # → True
```

## Translating to FOL and modal logic

The tableau above is a purpose-built ALC reasoner. `dl.translate` gives you the other route: the **standard translation** of ALC into classical FOL — `∃r.C` becomes `∃y (r(x, y) ∧ C(y))`, `∀r.C` becomes `∀y (r(x, y) → C(y))`, and the propositional connectives pass through unchanged — so ALC reasoning can reuse every FOL-facing tool in the kit: `is_valid`, the resolution prover, the finite model finder, and the Isabelle/THF exporters.

```python
import unicode_fol_kit.dl as dl
from unicode_fol_kit import is_valid

c = dl.And(dl.Exists("hasPet", dl.Atomic("Dog")), dl.ForAll("hasPet", dl.Atomic("Mammal")))
fol = dl.concept_to_fol(c, "x")               # concept membership, one free variable
fol.to_unicode_str()
# → '∃x_1 (hasPet(x, x_1) ∧ Dog(x_1)) ∧ ∀x_2 (hasPet(x, x_2) → Mammal(x_2))'
```

`dl.subsumption_to_fol(sub, sup, var="x")` is the standard reduction `∀x (sub(x) → sup(x))` — decide it with any FOL prover, and it agrees with the tableau's `dl.subsumes`:

```python
sub, sup = dl.Atomic("Dog"), dl.Atomic("Mammal")
fol_sub = dl.subsumption_to_fol(sub, sup)
fol_sub.to_unicode_str()               # → '∀x (Dog(x) → Mammal(x))'
is_valid(fol_sub)                      # → False   (no TBox axiom asserts it)
```

`dl.tbox_to_fol(tbox, var="x")` and `dl.abox_to_fol(abox)` translate a whole knowledge base — a TBox becomes the conjunction of its internalised GCIs (universally closed), an ABox the conjunction of its concept- and role-assertions — so `dl.concept_satisfiable` / `dl.abox_consistent` have an independent FOL-level cross-check via `is_valid` / the model finder.

### One role only: `concept_to_modal`

ALC is exactly the multi-modal logic K, with one modality *per role* — so a **single-role** concept also translates directly to propositional modal logic: `∃r.C` becomes `◇C`, `∀r.C` becomes `□C`.

```python
single_role = dl.And(dl.Exists("hasPet", dl.Atomic("Dog")), dl.ForAll("hasPet", dl.Atomic("Mammal")))
modal = dl.concept_to_modal(single_role)
modal.to_unicode_str()                 # → '◇Dog ∧ □Mammal'
```

A concept using **more than one** role has no faithful rendering here — propositional modal K has exactly one accessibility relation, so there is no honest way to recover which role a given `□`/`◇` came from — and `concept_to_modal` raises rather than guess:

```python
two_roles = dl.And(dl.Exists("hasChild", dl.Atomic("Person")), dl.Exists("hasPet", dl.Atomic("Dog")))
dl.concept_to_modal(two_roles)
# raises NotImplementedError: concept_to_modal: concept uses 2 distinct roles
# ['hasChild', 'hasPet']; ... Use concept_to_fol instead: it has no such limitation,
# since a role is just another binary FOL predicate r(x, y) and FOL scales to any
# number of them.
```

Both translations are differentially validated against the ALC tableau across a battery of concepts, so `concept_to_fol` / `concept_to_modal` and `dl.concept_satisfiable` / `dl.subsumes` agree by construction — pick whichever entry point fits the rest of your pipeline.

## General TBoxes

`dl.TBox()` holds general concept inclusions (GCIs). `add(sub, sup)` adds `sub ⊑ sup`; `add_equivalence(C, D)` adds `C ≡ D` (the two inclusions `C ⊑ D` and `D ⊑ C`). Both return the TBox, so calls chain. Each GCI is internalised as the concept `nnf(¬sub ⊔ sup)`, forced on every individual.

```python
import unicode_fol_kit.dl as dl

t = dl.TBox()
t.add(dl.Atomic("Dog"), dl.Atomic("Mammal"))
t.add(dl.Atomic("Mammal"), dl.Atomic("Animal"))

print(dl.subsumes(dl.Atomic("Dog"), dl.Atomic("Animal"), t))   # → True  (transitivity)
print(dl.subsumes(dl.Atomic("Animal"), dl.Atomic("Dog"), t))   # → False
```

Because both methods return the TBox, axioms can be added in a single chain. You can
inspect what each GCI becomes internally with `internalized()` — one `nnf(¬sub ⊔ sup)`
concept per inclusion, the form forced on every individual:

```python
import unicode_fol_kit.dl as dl

t = (dl.TBox()
     .add(dl.Atomic("Dog"), dl.Atomic("Mammal"))
     .add(dl.Atomic("Mammal"), dl.Atomic("Animal")))
print(len(t.inclusions))                                 # → 2
print([c.to_unicode() for c in t.internalized()])
# → ['¬Dog ⊔ Mammal', '¬Mammal ⊔ Animal']
```

A GCI of the form `C ⊑ ⊥` makes `C` itself unsatisfiable — the classic way to spot a
modelling error where a named concept can have no instances:

```python
import unicode_fol_kit.dl as dl

t = dl.TBox().add(dl.Atomic("Squircle"), dl.Bottom())
print(dl.concept_satisfiable(dl.Atomic("Squircle"), t))  # → False
```

Domain/range-style axioms work too. Saying "anything with a `hasChild` edge is a
`Parent`" (`∃hasChild.⊤ ⊑ Parent`) makes any existential over `hasChild` subsumed by
`Parent`:

```python
import unicode_fol_kit.dl as dl

t = dl.TBox().add(dl.Exists("hasChild", dl.Top()), dl.Atomic("Parent"))
print(dl.subsumes(dl.Exists("hasChild", dl.Atomic("Person")),
                  dl.Atomic("Parent"), t))               # → True
```

`add_equivalence` lets you give a concept a definition and then reason with it:

```python
import unicode_fol_kit.dl as dl

Person = dl.Atomic("Person")
Parent = dl.Atomic("Parent")

t = dl.TBox()
t.add_equivalence(Parent, dl.And(Person, dl.Exists("hasChild", Person)))

print(dl.subsumes(Parent, Person, t))                                  # → True
definition = dl.And(Person, dl.Exists("hasChild", Person))
print(dl.equivalent(Parent, definition, t))                            # → True
```

A disjointness axiom (`Cat ⊑ ¬Dog`) makes the conjunction unsatisfiable:

```python
import unicode_fol_kit.dl as dl

t = dl.TBox()
t.add(dl.Atomic("Cat"), dl.Not(dl.Atomic("Dog")))
print(dl.concept_satisfiable(dl.And(dl.Atomic("Cat"), dl.Atomic("Dog")), t))  # → False
```

### TBox examples: complex hierarchies

Build taxonomies with multiple levels and cross-cutting relationships:

```python
import unicode_fol_kit.dl as dl

Animal = dl.Atomic("Animal")
Mammal = dl.Atomic("Mammal")
Bird = dl.Atomic("Bird")
Dog = dl.Atomic("Dog")
Cat = dl.Atomic("Cat")
Eagle = dl.Atomic("Eagle")
Penguin = dl.Atomic("Penguin")

t = (dl.TBox()
     .add(Mammal, Animal)
     .add(Bird, Animal)
     .add(Dog, Mammal)
     .add(Cat, Mammal)
     .add(Eagle, Bird)
     .add(Penguin, Bird))

# Classification: Dog ⊑ Mammal ⊑ Animal
print(dl.subsumes(Dog, Animal, t))  # → True
print(dl.subsumes(Dog, Mammal, t))  # → True

# Dog and Bird are incomparable (no subsumption in either direction)
print(dl.subsumes(Dog, Bird, t))    # → False
print(dl.subsumes(Bird, Dog, t))    # → False

# All birds and mammals are animals
print(dl.subsumes(Mammal, Animal, t))  # → True
print(dl.subsumes(Bird, Animal, t))    # → True
```

Add constraints to concepts: what must be true of all members of a concept:

```python
import unicode_fol_kit.dl as dl

Person = dl.Atomic("Person")
Adult = dl.Atomic("Adult")
HasSSN = dl.Atomic("HasSSN")
Employed = dl.Atomic("Employed")

t = (dl.TBox()
     .add(Adult, Person)
     .add(Adult, dl.And(HasSSN, dl.Or(Employed, dl.Atomic("Retired")))))

# Being adult entails being a person
print(dl.subsumes(Adult, Person, t))  # → True

# Being adult entails having an SSN (via the conjunction)
print(dl.subsumes(Adult, HasSSN, t))  # → True

# But being a person does not entail being an adult
print(dl.subsumes(Person, Adult, t))  # → False
```

### TBox examples: role constraints

Express constraints on roles — who can have what relationship:

```python
import unicode_fol_kit.dl as dl

Person = dl.Atomic("Person")
Parent = dl.Atomic("Parent")

# "Anything with a child is a Parent" — domain/range axiom
t = dl.TBox().add(
    dl.Exists("hasChild", dl.Top()),  # "has at least one child"
    Parent
)

# So anyone with any child (of any type) is classified as a parent
anyone_with_child = dl.Exists("hasChild", dl.Atomic("Being"))
print(dl.subsumes(anyone_with_child, Parent, t))  # → True

# Role ranges: "All children must be persons"
# ∀hasChild.Person means "all children are persons"
t2 = dl.TBox().add(dl.Top(), dl.ForAll("hasChild", Person))

# Under this axiom, something with a child that is not a person is unsatisfiable
non_person = dl.Atomic("NonPerson")
bad_concept = dl.And(
    dl.Exists("hasChild", non_person),
    dl.ForAll("hasChild", Person)
)
print(dl.concept_satisfiable(bad_concept, t2))  # → False
```

## ABoxes

`dl.ABox()` collects assertions. `assert_concept(individual, C)` adds `individual : C`; `assert_role(a, b, role)` adds `(a, b) : role`. Both chain. `dl.abox_consistent(abox, tbox)` checks the whole knowledge base.

```python
import unicode_fol_kit.dl as dl

Person = dl.Atomic("Person")
t = dl.TBox().add_equivalence(
    dl.Atomic("Parent"), dl.And(Person, dl.Exists("hasChild", Person)))

abox = dl.ABox()
abox.assert_concept("alice", Person)
abox.assert_role("alice", "bob", "hasChild")
abox.assert_concept("bob", Person)
print(dl.abox_consistent(abox, t))   # → True
```

An empty ABox is trivially consistent, and a single individual asserted to be both
`P` and `¬P` is the simplest inconsistency:

```python
import unicode_fol_kit.dl as dl

print(dl.abox_consistent(dl.ABox()))   # → True

clash = (dl.ABox()
         .assert_concept("a", dl.Atomic("P"))
         .assert_concept("a", dl.Not(dl.Atomic("P"))))
print(dl.abox_consistent(clash))       # → False
```

The TBox constrains every named individual too. With `Cat ⊑ ¬Dog`, asserting that
`nemo` is both a `Cat` and a `Dog` is inconsistent:

```python
import unicode_fol_kit.dl as dl

t = dl.TBox().add(dl.Atomic("Cat"), dl.Not(dl.Atomic("Dog")))
abox = dl.ABox().assert_concept("nemo", dl.And(dl.Atomic("Cat"), dl.Atomic("Dog")))
print(dl.abox_consistent(abox, t))     # → False
```

Role assertions propagate value restrictions: `alice` has only happy children, but `bob` is asserted not happy, so the ∀-rule produces a clash.

```python
import unicode_fol_kit.dl as dl

abox = dl.ABox()
abox.assert_concept("alice", dl.ForAll("hasChild", dl.Atomic("Happy")))
abox.assert_role("alice", "bob", "hasChild")
abox.assert_concept("bob", dl.Not(dl.Atomic("Happy")))
print(dl.abox_consistent(abox))   # → False
```

A `∀r` and an `∃r` on the same individual interact even without an explicit role edge:
asserting `a : ∀r.A` together with `a : ∃r.¬A` forces the generated witness to be both
`A` and `¬A`:

```python
import unicode_fol_kit.dl as dl

A = dl.Atomic("A")
abox = (dl.ABox()
        .assert_concept("a", dl.ForAll("r", A))
        .assert_concept("a", dl.Exists("r", dl.Not(A))))
print(dl.abox_consistent(abox))   # → False
```

## Cyclic TBoxes terminate

A GCI such as `A ⊑ ∃r.A` would naively generate an infinite chain of `r`-successors. The tableau uses **subset blocking**: a generated individual whose label is contained in that of an earlier individual is not expanded (its successors are reused). This is sound and complete for ALC, so cyclic axioms terminate.

```python
import unicode_fol_kit.dl as dl

A = dl.Atomic("A")
t = dl.TBox().add(A, dl.Exists("r", A))   # A ⊑ ∃r.A
print(dl.concept_satisfiable(A, t))       # → True  (terminates via blocking)
```

Blocking only suppresses *redundant* expansion; a genuine contradiction along the
generated chain is still found. If the same `r`-successor required by the cycle is also
forced to be empty (`∀r.⊥`), the concept is unsatisfiable:

```python
import unicode_fol_kit.dl as dl

A = dl.Atomic("A")
t = dl.TBox().add(A, dl.And(dl.Exists("r", A), dl.ForAll("r", dl.Bottom())))
print(dl.concept_satisfiable(A, t))       # → False (∃r.A and ∀r.⊥ clash)
```

And the cyclic concept can still impose constraints that interact with extra
assumptions. Here `A ⊑ ∃r.A ⊓ ¬B`, so nothing in `A` is ever `B`:

```python
import unicode_fol_kit.dl as dl

A, B = dl.Atomic("A"), dl.Atomic("B")
t = dl.TBox().add(A, dl.And(dl.Exists("r", A), dl.Not(B)))
print(dl.concept_satisfiable(A, t))               # → True
print(dl.concept_satisfiable(dl.And(A, B), t))    # → False
```

### Cyclic TBox examples: linked structures

Express recursive structures that reference themselves:

```python
import unicode_fol_kit.dl as dl

Node = dl.Atomic("Node")
Terminal = dl.Atomic("Terminal")

t = dl.TBox().add(
    Node,
    dl.Or(Terminal, dl.Exists("successor", Node))
)

print(dl.concept_satisfiable(Node, t))  # → True

nonterminal = dl.And(Node, dl.Not(Terminal))
print(dl.concept_satisfiable(nonterminal, t))  # → True

acyclic_one_level = dl.And(
    Node,
    dl.Exists("successor", Terminal)
)
print(dl.concept_satisfiable(acyclic_one_level, t))  # → True
```

Combine cyclic axioms with role constraints:

```python
import unicode_fol_kit.dl as dl

Tree = dl.Atomic("Tree")
Leaf = dl.Atomic("Leaf")

t = (dl.TBox()
     .add(Tree, dl.Or(Leaf, dl.Exists("child", Tree)))
     .add(Tree, dl.ForAll("child", Tree)))

print(dl.concept_satisfiable(Tree, t))  # → True

non_leaf = dl.And(Tree, dl.Not(Leaf))
print(dl.concept_satisfiable(non_leaf, t))  # → True
```


## End-to-end: a small family ontology

Putting it together — define a vocabulary as a TBox, classify the concepts by
subsumption, then check a concrete ABox of individuals against it.

```python
import unicode_fol_kit.dl as dl

Person, Male, Female = dl.Atomic("Person"), dl.Atomic("Male"), dl.Atomic("Female")
Parent, Mother, Father = dl.Atomic("Parent"), dl.Atomic("Mother"), dl.Atomic("Father")

t = (dl.TBox()
     .add_equivalence(Parent, dl.And(Person, dl.Exists("hasChild", Person)))
     .add_equivalence(Mother, dl.And(Parent, Female))
     .add_equivalence(Father, dl.And(Parent, Male))
     .add(Male, dl.Not(Female)))                  # sexes are disjoint

# classification: Mother ⊑ Parent ⊑ Person, and Mother/Father are disjoint
print(dl.subsumes(Mother, Parent, t))             # → True
print(dl.subsumes(Mother, Person, t))             # → True
print(dl.concept_satisfiable(dl.And(Mother, Father), t))  # → False
print(dl.subsumes(Parent, Mother, t))             # → False (not every parent is a mother)

# a consistent knowledge base: Alice is a mother with a child Bob
kb = (dl.ABox()
      .assert_concept("alice", Mother)
      .assert_role("alice", "bob", "hasChild")
      .assert_concept("bob", Person))
print(dl.abox_consistent(kb, t))                  # → True

# add a contradiction: a Mother is Female, but Males are not Female
bad = (dl.ABox()
       .assert_concept("alice", Mother)
       .assert_concept("alice", Male))
print(dl.abox_consistent(bad, t))                 # → False
```

### End-to-end example: university domain

A realistic scenario with multiple concept levels, roles, and consistency checking:

```python
import unicode_fol_kit.dl as dl

Person = dl.Atomic("Person")
Student = dl.Atomic("Student")
Faculty = dl.Atomic("Faculty")
GradStudent = dl.Atomic("GradStudent")
Professor = dl.Atomic("Professor")
Course = dl.Atomic("Course")

t = (dl.TBox()
     .add(Student, Person)
     .add(GradStudent, Student)
     .add(Faculty, Person)
     .add(Professor, Faculty)
     .add(Professor, dl.Exists("advises", GradStudent))
     .add(GradStudent, dl.Exists("hasAdvisor", Professor))
     .add(dl.Exists("enrolledIn", Course), Student)
     .add(Student, dl.Not(Faculty)))

kb = (dl.ABox()
      .assert_concept("alice", Professor)
      .assert_concept("bob", GradStudent)
      .assert_role("bob", "alice", "hasAdvisor")
      .assert_role("alice", "bob", "advises")
      .assert_role("bob", "cs101", "enrolledIn")
      .assert_concept("cs101", Course))

print(dl.abox_consistent(kb, t))  # → True

bad_kb = (dl.ABox()
          .assert_concept("bob", GradStudent)
          .assert_concept("bob", Faculty))

print(dl.abox_consistent(bad_kb, t))  # → False
```

### End-to-end example: product classification

Organize products with constraints on features and relationships:

```python
import unicode_fol_kit.dl as dl

Product = dl.Atomic("Product")
PhysicalProduct = dl.Atomic("PhysicalProduct")
DigitalProduct = dl.Atomic("DigitalProduct")
Book = dl.Atomic("Book")
EBook = dl.Atomic("EBook")
PrintedBook = dl.Atomic("PrintedBook")
Tangible = dl.Atomic("Tangible")
Downloadable = dl.Atomic("Downloadable")

t = (dl.TBox()
     .add(PhysicalProduct, Product)
     .add(DigitalProduct, Product)
     .add(Book, Product)
     .add(EBook, dl.And(Book, DigitalProduct))
     .add(PrintedBook, dl.And(Book, PhysicalProduct))
     .add(PhysicalProduct, Tangible)
     .add(DigitalProduct, Downloadable)
     .add(PhysicalProduct, dl.Not(DigitalProduct)))

print(dl.subsumes(EBook, Book, t))              # → True
print(dl.subsumes(EBook, DigitalProduct, t))    # → True
print(dl.subsumes(EBook, Downloadable, t))      # → True
print(dl.subsumes(PrintedBook, Tangible, t))    # → True

print(dl.concept_satisfiable(EBook, t))         # → True
print(dl.concept_satisfiable(PrintedBook, t))   # → True

bad = dl.And(EBook, Tangible)
print(dl.concept_satisfiable(bad, t))           # → False

inventory = (dl.ABox()
             .assert_concept("item-1", PrintedBook)
             .assert_concept("item-2", EBook))

print(dl.abox_consistent(inventory, t))  # → True
```

