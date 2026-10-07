# Description logic ALC

The `unicode_logic_kit.dl` subpackage (new in 0.9.0) implements **ALC**, the smallest propositionally closed description logic and the notation underlying OWL, extended with role hierarchies and transitive roles (**ALCH+S** — see "Role hierarchies and transitive roles (RBox)" below) and qualified number restrictions (**ALCQ**, giving **ALCHQ** combined — see "Qualified number restrictions" below). It provides concept constructors, negation-normal-form rewriting, and a tableau reasoner that decides satisfiability, subsumption, equivalence, and ABox consistency over **general** TBoxes. Import it as `import unicode_logic_kit.dl as dl`.

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
| `dl.AtLeast(n, "r", C)` | ≥n r.C | at least `n` *pairwise-distinct* `r`-successors are in C |
| `dl.AtMost(n, "r", C)` | ≤n r.C | at most `n` pairwise-distinct `r`-successors are in C |

```python
import unicode_logic_kit.dl as dl

Person = dl.Atomic("Person")
parent = dl.And(Person, dl.Exists("hasChild", Person))
print(parent.to_unicode())   # → Person ⊓ ∃hasChild.Person
```

Concepts are frozen dataclasses, so they nest freely and compose like any other
value. The two roles below (`hasChild`, `hasPet`) are just strings, and ⊤/⊥ act as
the trivial top and bottom concepts:

```python
import unicode_logic_kit.dl as dl

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
import unicode_logic_kit.dl as dl

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
import unicode_logic_kit.dl as dl

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

`Concept.to_unicode()` renders with the standard DL glyphs and precedence-aware parenthesisation (binding order: atoms/⊤/⊥ tightest, then ¬ / ∃ / ∀ / ≥ / ≤, then ⊓, then ⊔). The reader folds a chain of one connective to the left, so the right operand of a connective of the same kind is parenthesised as well: `And(A, And(B, C))` renders as `A ⊓ (B ⊓ C)`, `And(And(A, B), C)` as `A ⊓ B ⊓ C`. `str(C)` is the same glyph text but never raises (it is display text); `C.to_unicode()` raises `ValueError` when a name would read back as a different concept.

```python
import unicode_logic_kit.dl as dl

c = dl.Or(dl.Atomic("A"), dl.And(dl.Atomic("B"), dl.Not(dl.Atomic("C"))))
print(c.to_unicode())                                  # → A ⊔ B ⊓ ¬C
print(dl.ForAll("r", dl.Or(dl.Atomic("A"), dl.Atomic("B"))).to_unicode())  # → ∀r.(A ⊔ B)
print(dl.Top().to_unicode(), dl.Bottom().to_unicode())  # → ⊤ ⊥
```

### Rendering complex expressions

Precedence rules are consistent across deeply nested expressions. Understand the precedence order to predict parenthesisation:

```python
import unicode_logic_kit.dl as dl

A, B, C, D = (dl.Atomic("A"), dl.Atomic("B"), 
              dl.Atomic("C"), dl.Atomic("D"))

# ⊔ binds loosest, so a ⊔ INSIDE a ⊓ needs parentheses
very_loose = dl.And(A, dl.Or(B, dl.And(C, D)))
print(very_loose.to_unicode())  # → A ⊓ (B ⊔ C ⊓ D)

# ⊓ binds tighter than ⊔, so a ⊓ inside a ⊔ needs none
tighter = dl.Or(dl.And(A, B), dl.And(C, D))
print(tighter.to_unicode())  # → A ⊓ B ⊔ C ⊓ D

# complex quantifier nesting with ⊔ and ⊓
complex_q = dl.ForAll("r", dl.Or(A, dl.Exists("s", B)))
print(complex_q.to_unicode())  # → ∀r.(A ⊔ ∃s.B)

# ¬ and a quantifier bind equally tight, so ¬ over a quantifier needs none
neg_quant = dl.Not(dl.Exists("r", A))
print(neg_quant.to_unicode())  # → ¬∃r.A
```

Parentheses appear only where precedence demands them, or where the reader's left fold
would otherwise read another tree. A ⊔ under a ⊓, a ⊓ under a ¬, or any binary concept
under a quantifier or ¬ gets wrapped, and so does the right operand of a connective of
its own kind; tighter structure does not:

```python
import unicode_logic_kit.dl as dl

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

# the reader folds A ⊓ B ⊓ C to (A ⊓ B) ⊓ C, so only a LEFT operand of the same
# connective goes without parentheses
print(dl.And(A, dl.And(B, C)).to_unicode())  # → A ⊓ (B ⊓ C)
print(dl.And(dl.And(A, B), C).to_unicode())  # → A ⊓ B ⊓ C
print(dl.Or(A, dl.Or(B, C)).to_unicode())    # → A ⊔ (B ⊔ C)

# str(C) is the same text as to_unicode(), and never raises
print(str(dl.And(A, B)))                     # → A ⊓ B
print(str(dl.Atomic("A ⊓ B")))               # → A ⊓ B   (a CLASS named 'A ⊓ B', shown as it is)
dl.Atomic("A ⊓ B").to_unicode()
# raises ValueError: to_unicode: 'A ⊓ B' reads back as And(left=Atomic(name='A'),
# right=Atomic(name='B')), not as the concept it was written from ...
```

## Parsing concepts from strings

`dl.parse_concept(text)` is the inverse of `to_unicode()`: it reads the same glyph syntax the renderer emits (`⊤ ⊥ ¬ ⊓ ⊔ ∃r.C ∀r.C ≥n r.C ≤n r.C`, plus parentheses for grouping) and returns a `Concept`. `parse_concept(c.to_unicode()) == c` holds as exact concept equality for every constructor that syntax can read, with no re-folding of a nested chain. Four kinds of concept are written but do not read back: a `Nominal` and a `HasValue` (refused by name), an `InverseRole` (a role name ending in `⁻` is refused as an INVERSE role name, not read as a role of that name), and the data restrictions (the glyph syntax has no data layer: a built-in datatype name is refused by name, a datatype you defined reads as a class, and a data value `∃d.{v}` is refused like a `HasValue`). `dl.parse_gci(text)` parses a **general concept inclusion** `C ⊑ D` and returns the `(sub, sup)` pair ready for `dl.subsumes(sub, sup)` or a `TBox`.

```python
import unicode_logic_kit.dl as dl

c = dl.parse_concept("∃hasChild.Person ⊓ ∀hasPet.Dog")
c.to_unicode()                          # → '∃hasChild.Person ⊓ ∀hasPet.Dog'
c == dl.And(dl.Exists("hasChild", dl.Atomic("Person")),
            dl.ForAll("hasPet", dl.Atomic("Dog")))     # → True

# ⊤ / ⊥ parse too:
dl.parse_concept("∃hasPet.⊤")           # → Exists(role='hasPet', concept=Top())
dl.parse_concept("∀hasPet.⊥")           # → ForAll(role='hasPet', concept=Bottom())

sub, sup = dl.parse_gci("Dog ⊑ Mammal")
(sub, sup)                              # → (Atomic(name='Dog'), Atomic(name='Mammal'))
dl.subsumes(sub, sup)                   # → False   (no TBox axiom says so — yet)
```

Round-trips both ways — `to_unicode()` output re-parses, and the parsed tree renders back to the same string:

```python
c2 = dl.And(dl.Or(dl.Atomic("A"), dl.Atomic("B")), dl.Not(dl.Atomic("C")))
dl.parse_concept(c2.to_unicode()) == c2     # → True

# also for the nesting a left-folding reader would turn around
c3 = dl.And(dl.Atomic("A"), dl.And(dl.Atomic("B"), dl.Atomic("C")))
c3.to_unicode()                             # → 'A ⊓ (B ⊓ C)'
dl.parse_concept(c3.to_unicode()) == c3     # → True
```

A malformed concept raises `dl.ConceptSyntaxError` with the offending position, rather than a bare parser exception:

```python
dl.parse_concept("Person ⊓")
# raises ConceptSyntaxError: parse_concept: unexpected end of input at position 8;
# expected '⊤', '⊥', a concept name, '¬', '∃', '∀', '≥', '≤', or '(' in 'Person ⊓'
```

## Negation normal form

`dl.nnf(C)` pushes ¬ inward so that negation occurs only on atomic concepts, using the De Morgan and modal dualities (`¬⊤=⊥`, `¬¬C=C`, `¬(C⊓D)=¬C⊔¬D`, `¬∃r.C=∀r.¬C`, `¬∀r.C=∃r.¬C`). This is the shape the tableau consumes.

```python
import unicode_logic_kit.dl as dl

neg = dl.Not(dl.Exists("r", dl.And(dl.Atomic("A"), dl.Atomic("B"))))
print(dl.nnf(neg).to_unicode())   # → ∀r.(¬A ⊔ ¬B)

print(dl.nnf(dl.Not(dl.ForAll("r", dl.Atomic("A")))).to_unicode())  # → ∃r.¬A
```

Each rewrite rule, in isolation:

```python
import unicode_logic_kit.dl as dl

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
import unicode_logic_kit.dl as dl

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
import unicode_logic_kit.dl as dl

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
import unicode_logic_kit.dl as dl

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
import unicode_logic_kit.dl as dl

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
import unicode_logic_kit.dl as dl

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
import unicode_logic_kit.dl as dl

A, B = dl.Atomic("A"), dl.Atomic("B")

# ∃r.A ⊓ ∀r.B is satisfiable only if A and B can overlap
overlap_sat = dl.And(dl.Exists("r", A), dl.ForAll("r", B))
print(dl.concept_satisfiable(overlap_sat))  # → True (their r-successor can be in A ⊓ B)

# but a TBox that makes A and B disjoint refutes it
disjoint = dl.TBox().add(A, dl.Not(B))
print(dl.concept_satisfiable(overlap_sat, disjoint))  # → False (the r-successor would be in A and in B)

# without such an axiom the two atoms are unrelated: ∃r.A ⊓ ∀r.¬B is satisfiable
print(dl.concept_satisfiable(dl.And(dl.Exists("r", A), dl.ForAll("r", dl.Not(B)))))  # → True

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
import unicode_logic_kit.dl as dl

A = dl.Atomic("A")
print(dl.subsumes(dl.Bottom(), A))                      # → True   (⊥ ⊑ A)
print(dl.subsumes(A, dl.Top()))                         # → True   (A ⊑ ⊤)
print(dl.subsumes(dl.Exists("r", A), dl.Exists("r", dl.Top())))  # → True
print(dl.subsumes(dl.ForAll("r", A), dl.ForAll("r", dl.Top())))  # → True
```

### Subsumption with compound concepts

Subsumption behaves classically for conjunctions and complements:

```python
import unicode_logic_kit.dl as dl

A, B, C = dl.Atomic("A"), dl.Atomic("B"), dl.Atomic("C")

# A ⊓ B ⊑ A (left elimination)
print(dl.subsumes(dl.And(A, B), A))  # → True

# A ⊑ A ⊔ B (weakening)
print(dl.subsumes(A, dl.Or(A, B)))  # → True

# contraposition: ¬B ⊑ ¬A holds exactly when A ⊑ B does
print(dl.subsumes(dl.Not(B), dl.Not(A)))  # → False (A ⊑ B does not hold without a TBox)
print(dl.subsumes(dl.Not(B), dl.Not(A), dl.TBox().add(A, B)))  # → True (it does once A ⊑ B is an axiom)
print(dl.subsumes(B, A))  # → False

# transitivity: if A ⊑ B and B ⊑ C then A ⊑ C
print(dl.subsumes(A, B))  # → False (without TBox)
# but with a TBox (see below), transitivity holds
```

### Equivalence: De Morgan, distributivity, and quantifier laws

`equivalent(C, D)` is mutual subsumption. It captures the propositional laws as well
as the ALC-specific facts that ∃ distributes over ⊔ and ∀ over ⊓:

```python
import unicode_logic_kit.dl as dl

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
import unicode_logic_kit.dl as dl

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
import unicode_logic_kit.dl as dl
from unicode_logic_kit import is_valid

c = dl.And(dl.Exists("hasPet", dl.Atomic("Dog")), dl.ForAll("hasPet", dl.Atomic("Mammal")))
fol = dl.concept_to_fol(c, "x")               # concept membership, one free variable
fol.to_unicode_str()
# → '∃x0 (hasPet(x, x0) ∧ Dog(x0)) ∧ ∀x1 (hasPet(x, x1) → Mammal(x1))'
```

`dl.subsumption_to_fol(sub, sup, var="x")` is the standard reduction `∀x (sub(x) → sup(x))` — decide it with any FOL prover, and it agrees with the tableau's `dl.subsumes`:

```python
sub, sup = dl.Atomic("Dog"), dl.Atomic("Mammal")
fol_sub = dl.subsumption_to_fol(sub, sup)
fol_sub.to_unicode_str()               # → '∀x (Dog(x) → Mammal(x))'
is_valid(fol_sub)                      # → False   (no TBox axiom asserts it)
```

`dl.tbox_to_fol(tbox, var="x")` renders the concept inclusions ONLY (each internalised GCI, universally closed) and `dl.abox_to_fol(abox)` the ABox alone, so each answers a question about the *empty* knowledge base. A `TBox` also holds the role box, and rendering the GCIs alone would silently drop it, which can report a false counterexample for a subsumption the tableau accepts — so `tbox_to_fol` raises `dl.RoleBoxOmittedError` for a TBox with a role inclusion or a transitive role, unless you pass `concept_inclusions_only=True`.

For a question *relative to a knowledge base* use `dl.kb_to_fol(tbox, abox)`: it returns the knowledge base as one formula and the role-box axioms separately, to be passed as `api.prove` premises — `kb.tbox_premises` for subsumption, `kb.premises` for instance checking, and `api.prove(Not(kb.formula), kb.axioms)` for consistency (proved means inconsistent). The bundle builds the matching goal as well — `kb.subsumption_goal(sub, sup)`, `kb.unsatisfiability_goal(concept)` and `kb.instance_goal(individual, concept)` — which for a knowledge base without a data layer is the spelling above, and for one with a data layer is the only right one (see "The data layer: two sorts" below). That is what gives `dl.concept_satisfiable` / `dl.subsumes` / `dl.abox_consistent` an independent FOL-level cross-check via `is_valid` / the model finder.

**A bound variable never shares a name with an individual.** In the FOL image an individual is a constant. A constant and a variable of one name are two symbols to Z3 and two texts in the Unicode syntax (`x` and `'x'`), but a writer that gives the two one namespace (the third-order THF writers `to_thf_to` and `to_thf_ho_modal`) writes them as one symbol, so an ABox that names an individual `x` would be captured there by the `∀x` the image binds around a general concept inclusion or a role-box axiom — and the knowledge base would silently say something else. The translation therefore renames its bound variables (alpha-equivalence, so the meaning of every axiom is unchanged) so that none of them is an individual of the knowledge base; the rename is one choice for a whole `kb_to_fol` call, so the formula and the axioms always agree on it:

```python
t = dl.TBox().add_transitive_role("r")
kb = dl.kb_to_fol(t, dl.ABox().assert_role("x", "y", "r"))
print([a.to_unicode_str() for a in kb.axioms])
# → ['∀x0 ∀y0 ∀z (r(x0, y0) ∧ r(y0, z) → r(x0, z))']    # not ∀x ∀y: x and y are individuals
```

`dl.concept_to_fol(concept, var)` is the one place a caller names a FREE variable, and it cannot rename that one: if `var` is an individual of the concept (a `HasValue` filler or a `Nominal`), it raises `ValueError` and asks for another name, instead of answering a question the caller did not ask.

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

## Instance checking, retrieval, and realization

Given an ABox (and optionally a TBox), four functions answer the standard ABox
reasoning tasks. All four are reductions to `dl.abox_consistent` — they add no
tableau rule, so they inherit its soundness/completeness rather than adding to it
(`instance_retrieval`, `realize` and `realize_all` run the refusal guard first, so
a knowledge base the tableau refuses is refused even when there is nothing to
sweep; `instance_check` meets it in `dl.abox_consistent`).

- `dl.instance_check(abox, individual, C, tbox=None)` — does the knowledge base
  entail `individual : C`? Decided the same way `dl.subsumes` is: assert the
  complement `individual : ¬C` alongside the ABox and check the result is
  *inconsistent*. Open-world, like the rest of the reasoner: `False` means "not
  entailed", not "entailed to be false".
- `dl.instance_retrieval(abox, C, tbox=None)` — every individual entailed to be a `C`.
- `dl.realize(abox, individual, vocabulary, tbox=None)` — `individual`'s
  *most-specific* concepts from a caller-supplied `vocabulary` list (this reasoner
  keeps no persistent registry of "all named concepts", so realization needs that
  list up front; see `dl.classify` below for the TBox-wide version of that registry).
- `dl.realize_all(abox, vocabulary, tbox=None)` — `dl.realize` for every individual
  named in the ABox, as a `{individual: [concepts]}` dict.

An ABox with no individual has no instances: `instance_retrieval` returns the
empty set and `realize_all` the empty dict (an older version invented a phantom
individual `a` to probe with, and could report it). Every public entry point —
these four, `dl.classify` and the `dl.external_*` functions included — reaches
the same guard as `concept_satisfiable` / `abox_consistent`, even on the paths
where there is nothing to reduce (an empty ABox, an empty vocabulary), so a role
box or an assertion the reasoner cannot honour is refused by name and never
answered silently because the loop body never ran.

```python
import unicode_logic_kit.dl as dl

Human, Mortal = dl.Atomic("Human"), dl.Atomic("Mortal")
t = dl.TBox().add(Human, Mortal)
abox = dl.ABox().assert_concept("socrates", Human)
print(dl.instance_check(abox, "socrates", Mortal, t))   # → True

Dog, Mammal, Animal = dl.Atomic("Dog"), dl.Atomic("Mammal"), dl.Atomic("Animal")
t2 = dl.TBox().add(Dog, Mammal).add(Mammal, Animal)
kb = dl.ABox().assert_concept("rex", Dog).assert_concept("tweety", dl.Atomic("Bird"))

print(sorted(dl.instance_retrieval(kb, Animal, t2)))    # → ['rex']

# rex is a Dog, hence a Mammal, hence an Animal — realize keeps only the
# most-specific of those, dropping Mammal/Animal/⊤ as strictly subsumed by Dog.
vocabulary = [Animal, Mammal, Dog, dl.Top()]
print([c.to_unicode() for c in dl.realize(kb, "rex", vocabulary, t2)])   # → ['Dog']
```

## General TBoxes

`dl.TBox()` holds general concept inclusions (GCIs). `add(sub, sup)` adds `sub ⊑ sup`; `add_equivalence(C, D)` adds `C ≡ D` (the two inclusions `C ⊑ D` and `D ⊑ C`). Both return the TBox, so calls chain. Each GCI is internalised as the concept `nnf(¬sub ⊔ sup)`, forced on every individual.

```python
import unicode_logic_kit.dl as dl

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
import unicode_logic_kit.dl as dl

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
import unicode_logic_kit.dl as dl

t = dl.TBox().add(dl.Atomic("Squircle"), dl.Bottom())
print(dl.concept_satisfiable(dl.Atomic("Squircle"), t))  # → False
```

Domain/range-style axioms work too. Saying "anything with a `hasChild` edge is a
`Parent`" (`∃hasChild.⊤ ⊑ Parent`) makes any existential over `hasChild` subsumed by
`Parent`:

```python
import unicode_logic_kit.dl as dl

t = dl.TBox().add(dl.Exists("hasChild", dl.Top()), dl.Atomic("Parent"))
print(dl.subsumes(dl.Exists("hasChild", dl.Atomic("Person")),
                  dl.Atomic("Parent"), t))               # → True
```

`add_equivalence` lets you give a concept a definition and then reason with it:

```python
import unicode_logic_kit.dl as dl

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
import unicode_logic_kit.dl as dl

t = dl.TBox()
t.add(dl.Atomic("Cat"), dl.Not(dl.Atomic("Dog")))
print(dl.concept_satisfiable(dl.And(dl.Atomic("Cat"), dl.Atomic("Dog")), t))  # → False
```

### TBox examples: complex hierarchies

Build taxonomies with multiple levels and cross-cutting relationships:

```python
import unicode_logic_kit.dl as dl

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
import unicode_logic_kit.dl as dl

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
import unicode_logic_kit.dl as dl

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
bad_concept = dl.Exists("hasChild", dl.Not(Person))
print(dl.concept_satisfiable(bad_concept, t2))  # → False

# an atom merely NAMED NonPerson is not disjoint from Person unless an axiom says so
non_person = dl.Atomic("NonPerson")
print(dl.concept_satisfiable(dl.Exists("hasChild", non_person), t2))  # → True
```

### Role hierarchies and transitive roles (RBox)

On top of the concept-level TBox, `dl.TBox()` also carries an **RBox**: role
inclusions `r ⊑ s` (`add_role_inclusion(sub_role, super_role)`) and transitivity
declarations `Trans(r)` (`add_transitive_role(role)`). Together with ALC this gives
**ALCH** (role hierarchies) plus transitive roles — the non-inverse fragment of the
DL usually written **SH**. Both methods return the TBox, so they chain like `add`/
`add_equivalence`.

A role hierarchy alone lets an `r`-edge count as an `s`-edge for every declared
`r ⊑ s`, so an `∃hasSon` witness is also an `∃hasChild` witness — but only once the
inclusion is declared:

```python
import unicode_logic_kit.dl as dl

sub, sup = dl.Exists("hasSon", dl.Top()), dl.Exists("hasChild", dl.Top())
print(dl.subsumes(sub, sup))                                   # → False (unrelated roles)

t = dl.TBox().add_role_inclusion("hasSon", "hasChild")
print(dl.subsumes(sub, sup, t))                                 # → True
```

A transitive role makes a 2-hop chain collapse into a 1-hop fact. `Trans("partOf")`
makes "part of a part of an Engine" entail "part of an Engine":

```python
import unicode_logic_kit.dl as dl

Engine = dl.Atomic("Engine")
sub = dl.Exists("partOf", dl.Exists("partOf", Engine))
sup = dl.Exists("partOf", Engine)
print(dl.subsumes(sub, sup))                                    # → False

t = dl.TBox().add_transitive_role("partOf")
print(dl.subsumes(sub, sup, t))                                  # → True
```

The two combine: a role hierarchy edge that feeds into a transitive super-role
still composes along the whole chain, not just one hop. With `hasChild ⊑
hasDescendant` and `Trans(hasDescendant)`, a value restriction on `hasDescendant`
propagates down an arbitrarily long `hasChild` chain — three hops here, `alice`
down to `carol`:

```python
import unicode_logic_kit.dl as dl

Happy = dl.Atomic("Happy")
t = dl.TBox().add_role_inclusion("hasChild", "hasDescendant").add_transitive_role("hasDescendant")
kb = (dl.ABox()
      .assert_concept("alice", dl.ForAll("hasDescendant", Happy))
      .assert_role("alice", "bob", "hasChild")
      .assert_role("bob", "carol", "hasChild")
      .assert_concept("carol", dl.Not(Happy)))
print(dl.abox_consistent(kb, t))                                  # → False (carol must be Happy)
```

`dl.instance_check`, `dl.classify`, and the rest of the reasoning API above respect
a TBox's RBox automatically — they are pure reductions to `concept_satisfiable`/
`abox_consistent`, which is where the RBox lives, so there is no separate
RBox-aware entry point to call.

`dl.translate.rbox_to_fol(tbox)` renders the RBox itself as FOL — a role inclusion
as `∀x,y (r(x,y) → s(x,y))`, a transitivity declaration as `∀x,y,z (r(x,y) ∧
r(y,z) → r(x,z))` — giving an independent cross-check for the tableau's RBox rules
via any FOL prover, the same way `tbox_to_fol` cross-checks GCIs:

```python
from unicode_logic_kit.dl.translate import rbox_to_fol

print(rbox_to_fol(t).to_unicode_str())
# → '∀x ∀y (hasChild(x, y) → hasDescendant(x, y)) ∧
#     ∀x ∀y ∀z (hasDescendant(x, y) ∧ hasDescendant(y, z) → hasDescendant(x, z))'
```

RBox axioms also read from OWL Manchester syntax's two matching one-line shapes,
`"r SubPropertyOf s"` and `"r Characteristics: Transitive"`, via
`dl.parse_manchester_role_axiom`:

```python
import unicode_logic_kit.dl as dl

print(dl.parse_manchester_role_axiom("hasChild SubPropertyOf hasDescendant"))
# → ('subproperty', 'hasChild', 'hasDescendant')
print(dl.parse_manchester_role_axiom("hasDescendant Characteristics: Transitive"))
# → ('transitive', 'hasDescendant')
```

All SEVEN of OWL 2's object-property characteristics are read, plus the three
other binary role frames — a parser never refuses an axiom KIND, because a
`TBox` is what a parser fills from a file:

```python
print(dl.parse_manchester_role_axiom("hasSpouse Characteristics: Symmetric"))
# -> ('symmetric', 'hasSpouse')
print(dl.parse_manchester_role_axiom("partOf InverseOf hasPart"))
# -> ('inverse', 'partOf', 'hasPart')
print(dl.parse_manchester_role_axiom("hasSink DisjointWith hasSource"))
# -> ('disjoint', 'hasSink', 'hasSource')
print(dl.parse_manchester_role_axiom("hasSink EquivalentTo hasOutput"))
# -> ('equivalentproperty', 'hasSink', 'hasOutput')
```

Two shapes stay refused by name, and the refusal names the entry point that
does read them: a PROPERTY CHAIN (`"r o s SubPropertyOf t"` — the bare name `o`
is deliberately not a keyword here, so a class or role literally named `o` keeps
working in `parse_manchester`) and the comma-separated n-ary
`DisjointWith`/`EquivalentTo` frame slot. One deliberate asymmetry with
`parse_owl_functional`: an OWL 2 built-in property name is refused here in
every position, including the tautological super-role case
`parse_owl_functional` consumes as a no-op — a single-axiom parser has no
return shape for "this axiom is nothing".

### The rest of the OWL 2 object property box

A `TBox` carries every OWL 2 object-property axiom kind, and `dl.rbox_to_fol`
renders every one of them as its OWL 2 direct-semantics sentence:

| axiom | builder | FOL image | in-house tableau |
| --- | --- | --- | --- |
| `r ⊑ s` | `add_role_inclusion` | `∀x ∀y (r(x, y) → s(x, y))` | rule H |
| `Trans(r)` | `add_transitive_role` | `∀x ∀y ∀z (r(x, y) ∧ r(y, z) → r(x, z))` | rule S |
| `r ≡ s` | `add_equivalent_roles` | the two inclusions | rule H (no new rule) |
| `Disj(p, q)` | `add_disjoint_roles` | `∀x ∀y ¬(p(x, y) ∧ q(x, y))` | clash condition |
| `Asym(r)` | `add_asymmetric_role` | `∀x ∀y (r(x, y) → ¬r(y, x))` | clash condition |
| `Irr(r)` | `add_irreflexive_role` | `∀x ¬r(x, x)` | clash condition |
| `Func(r)` | `add_functional_role` | `∀x ∀y ∀z (r(x, y) ∧ r(x, z) → y = z)` | internalised as `⊤ ⊑ ≤1 r.⊤` |
| `Inv(p, q)` | `add_inverse_roles` | `∀x ∀y (p(x, y) ↔ q(y, x))` | refused by name |
| `Sym(r)` | `add_symmetric_role` | `∀x ∀y (r(x, y) → r(y, x))` | refused by name |
| `Refl(r)` | `add_reflexive_role` | `∀x r(x, x)` | refused by name |
| `InvFunc(r)` | `add_inverse_functional_role` | `∀x ∀y ∀z (r(y, x) ∧ r(z, x) → y = z)` | refused by name |
| `p₁ ∘ p₂ ⊑ q` | `add_role_chain` | `∀x ∀y ∀z (p₁(x, y) ∧ p₂(y, z) → q(x, z))` | refused by name |

The three clash conditions cost nothing but a check on the branch's EDGES,
because each forbids an edge PATTERN and forces no concept on anybody:

```python
import unicode_logic_kit.dl as dl

t = dl.TBox().add_irreflexive_role("hasPhysicalInput")
ab = dl.ABox().assert_role("a", "a", "hasPhysicalInput")
print(dl.abox_consistent(ab, t))                     # -> False
print(dl.abox_consistent(ab, dl.TBox()))             # -> True

# r ⊑ s makes every r-pair an s-pair, so an r-pair would be in BOTH — which
# disjointness forbids. Hence r is empty.
t2 = dl.TBox().add_role_inclusion("r", "s").add_disjoint_roles("r", "s")
print(dl.concept_satisfiable(dl.Exists("r", dl.Top()), t2))   # -> False
```

Functionality is not a new rule at all: `Func(P)` IS the GCI `⊤ ⊑ ≤1 P.⊤`, and
a `≤1 P.⊤` on a simple role is already decided by the ALCQ machinery below.

```python
A, B = dl.Atomic("A"), dl.Atomic("B")
t = dl.TBox().add_functional_role("hasState")
sub = dl.And(dl.Exists("hasState", A), dl.Exists("hasState", B))
print(dl.subsumes(sub, dl.Exists("hasState", dl.And(A, B)), t))          # -> True
print(dl.subsumes(sub, dl.Exists("hasState", dl.And(A, B)), dl.TBox()))  # -> False
```

The five refused kinds are refused LOUDLY, each message saying why and what to
use instead — never approximated, never silently ignored:

```python
dl.concept_satisfiable(dl.Top(), dl.TBox().add_symmetric_role("isConnectedTo"))
# raises dl.UnsupportedAxiomError: ... SymmetricObjectProperty x1 ... Why a
# symmetric role IS the inverse-role inclusion P ⊑ P⁻: materialising the
# converse edge would put a cycle in the completion graph, so a blocked node's
# blocker can become its own descendant and subset blocking no longer applies.
# Use dl.owl_reasoner's external, HermiT-backed reasoner ... or ask the same
# question of the FOL image with dl.kb_to_fol(tbox, abox) and api.prove.
```

Four of them are the **I** of SHIQ or its counting cousin (an inverse pair, a
symmetric role, inverse-functionality — which is `≤1 r⁻.⊤`, so it counts
PREDECESSORS — and a reflexive role, which would let the ≤-rule merge a node
with its own successor). The fifth, a property chain, is the **R** of SROIQ and
needs the role automaton and regularity restriction of Horrocks, Kutz & Sattler
2006; the local label rule that would cover an acyclic chain set is written out
in `dl/tableau.py`'s module docstring so it need not be re-derived. In every
case `dl.rbox_to_fol` still renders the axiom, so the question has an answer by
another route:

```python
t = dl.TBox().add_role_chain(("isAbout", "covers"), "coversShortcut")
kb = dl.kb_to_fol(t)
print(kb.axioms_of_kind("ObjectPropertyChain")[0].to_unicode_str())
# -> ∀x ∀y ∀z (isAbout(x, y) ∧ covers(y, z) → coversShortcut(x, z))
```

OWL 2 (Structural Specification §11) restricts asymmetry, irreflexivity, role
disjointness, functionality and inverse-functionality — and every qualified
number restriction — to SIMPLE roles: a role no COMPOSITE role (one declared
transitive, or the super-role of a property chain) entails via `⊑*`. That
restriction is what makes the three clash conditions EXACT rather than merely
sound, and the kit enforces it by name on the in-house AND the external route:

```python
t = dl.TBox().add_transitive_role("partOf").add_asymmetric_role("partOf")
dl.concept_satisfiable(dl.Top(), t)
# raises dl.NonSimpleRoleError: dl.tableau: AsymmetricObjectProperty('partOf')
# is not allowed: 'partOf' is NON-SIMPLE ...
```

A role-box builder handed something that is not a usable role in that position
raises `dl.RoleExpressionError` on the call that is wrong, rather than storing
it and printing an atom that looks like an axiom and is not:

```python
dl.TBox().add_role_inclusion(("r", "s"), "t")
# raises dl.RoleExpressionError: ... A sequence of roles is a PROPERTY CHAIN —
# use dl.TBox.add_role_chain(chain, super_role) ...
dl.TBox().add_transitive_role(dl.InverseRole("r"))
# raises dl.RoleExpressionError: ... a characteristic of r⁻ is the SAME axiom
# as the characteristic of r ... pass 'r' instead
```

`RoleExpressionError` is the one exception for a role that cannot be used where
it stands, and it says which case it is, with the remedy that is TRUE for that
axiom (the advice differs per characteristic: `Functional(r⁻)` is
`InverseFunctional(r)`, `Domain(r⁻, C)` is `Range(r, C)`, while `Trans(r⁻)` is
simply `Trans(r)`):

```python
dl.TBox().add_functional_role(dl.InverseRole("r"))
# raises dl.RoleExpressionError: ... Functional(r⁻) is NOT Functional(r): it says an
# element has at most one r-PREDECESSOR, which is InverseFunctional(r). Use
# dl.TBox.add_inverse_functional_role('r') ...
dl.TBox().add_role_chain("rs", "t")
# raises dl.RoleExpressionError: ... a property chain is a SEQUENCE of role names ...
# A str would be split into its CHARACTERS ... Write add_role_chain(['r', 's'], 't').
dl.TBox().add_functional_role("=")
# raises dl.RoleExpressionError: ... '=' is the name of the EQUALITY atom the FOL
# image renders ... not a role name
```

An `InverseRole` on either side of a role INCLUSION is the exception: `r ⊑ s⁻`
is a genuinely different axiom from `r ⊑ s`, so it is accepted and rendered
correctly (`∀x ∀y (r(x, y) → s(y, x))`) — and the tableau refuses the role box
by name, as the **I** of SHIQ. `to_owl_functional` writes it as
`SubObjectPropertyOf(r ObjectInverseOf(s))` and `parse_owl_functional` reads it
back (see "OWL 2 Functional-Style Syntax" below); `ObjectInverseOf` is read in
that position only.

### The OWL 2 built-in property names

`owl:topObjectProperty` denotes the whole of `ΔI × ΔI` and
`owl:bottomObjectProperty` the empty relation. ALCHQ has neither the universal
nor the empty role, so no role-box field may carry one. A TAUTOLOGICAL
inclusion — a reserved TOP name as the super-role, or a reserved BOTTOM name as
the sub-role — is consumed by `dl.parse_owl_functional` as a documented no-op,
the same precedent that module already sets for `Declaration(...)` and
`Annotation(...)`; a tautology carries no truth to lose. Every other
occurrence, in either the abbreviated or the full-IRI spelling, is refused by
name:

```python
tbox, abox = dl.parse_owl_functional(
    "Ontology(SubObjectPropertyOf(partOf owl:topObjectProperty))")
print(tbox == dl.TBox(), abox == dl.ABox())   # -> True True

dl.parse_owl_functional("Ontology(SubObjectPropertyOf(owl:topObjectProperty partOf))")
# raises OwlFunctionalUnsupportedError: the OWL 2 BUILT-IN property
# 'owl:topObjectProperty' (owl:topObjectProperty — the universal property (it
# relates every pair)) in SubObjectPropertyOf is not supported — outside ALCHQ ...
```

So `∃owl:topObjectProperty.C` ("C is non-empty") stays inexpressible, and
"P is empty" must be written as the concept inclusion `⊤ ⊑ ∀P.⊥`.

The same names (`owl:topObjectProperty` / `owl:bottomObjectProperty` and the data
pair `owl:topDataProperty` / `owl:bottomDataProperty`, in both spellings) can also be typed in by hand, where no OWL parser stands in the
way: as the role of a restriction, in a role assertion, in a role-box builder, in
the glyph parser or in the Manchester class parser. None of those readers can
mean the universal or the empty relation, and an ordinary role of that name is a
DIFFERENT restriction with a different verdict, so every one of them is refused
by name — a `dl.RoleExpressionError` at query time and translation time, a
`ConceptSyntaxError` / `ManchesterSyntaxError` at parse time — with the OWL 2
reading of the name and the true remedy:

```python
dl.concept_satisfiable(dl.Exists("owl:topObjectProperty", dl.Atomic("A")))
# raises dl.RoleExpressionError: dl.tableau: the OWL 2 BUILT-IN property
# 'owl:topObjectProperty' (... the universal property: it relates every pair of
# elements) is the role of Exists (∃owl:topObjectProperty.A), and it would be read
# as an ORDINARY role of that name ... A global 'every element is in C' is the
# general concept inclusion ⊤ ⊑ C (dl.TBox.add(dl.Top(), C)).
```

An ObjectPropertyAssertion over the universal property holds in every
interpretation (and over the empty property in none), and the message says so:
it is not a role fact to approximate but an assertion to drop, or an
inconsistency to state with `assert_concept(a, Bottom())`. A data built-in used in
an object-property axiom is called what it is, ill-typed, not mistaken for an
object one.

## Qualified number restrictions (ALCQ)

`dl.AtLeast(n, role, C)` (≥n r.C) and `dl.AtMost(n, role, C)` (≤n r.C) count *pairwise-distinct* `role`-successors in `C`. There is **no unique name assumption** anywhere in this reasoner — an individual (named or generated) is distinct from another only when something forces it — so `n` really means "n individuals the reasoner cannot merge together", not "n names":

```python
import unicode_logic_kit.dl as dl

Person = dl.Atomic("Person")
c = dl.AtLeast(2, "hasChild", Person)
print(c.to_unicode())   # → ≥2 hasChild.Person
```

The classic pigeonhole example — at most one `hasChild`-successor overall, but at least two `Person`-successors and at least two non-`Person`-successors — is unsatisfiable, since satisfying both `≥2` restrictions forces two individuals that are *each* pairwise-distinct from the other members of their own restriction, and nothing can collapse them back under the `≤1` bound:

```python
pigeonhole = dl.And(
    dl.And(dl.AtMost(1, "hasChild", dl.Top()), dl.AtLeast(2, "hasChild", Person)),
    dl.AtLeast(2, "hasChild", dl.Not(Person)))
print(dl.concept_satisfiable(pigeonhole))   # → False
```

Named ABox individuals stay mergeable until something forces them apart. Two `hasChild`-successors of `alice`, with `alice` bound (via a global TBox axiom, `⊤ ⊑ ≤1 hasChild.⊤`) to at most one, are satisfiable exactly because `bob` and `carol` are free to denote the same domain element:

```python
ab = (dl.ABox().assert_role("alice", "bob", "hasChild")
      .assert_role("alice", "carol", "hasChild"))
t = dl.TBox().add(dl.Top(), dl.AtMost(1, "hasChild", dl.Top()))
print(dl.abox_consistent(ab, t))    # → True  (bob and carol may be merged)

ab2 = ab.assert_distinct("bob", "carol")   # ABox.assert_distinct: force them apart
print(dl.abox_consistent(ab2, t))          # → False (now genuinely 2 successors)
```

**Simple roles only.** A number restriction may not target a role that is transitive, or that has a transitive sub-role reachable through the RBox — combining unrestricted transitivity with counting is undecidable (Horrocks, Sattler & Tobies 1999/2000; the same "simple roles" restriction SHQ/SHIQ use). The kit refuses the combination by name, before the tableau ever starts:

```python
t2 = dl.TBox().add_transitive_role("hasChild")
dl.concept_satisfiable(dl.AtLeast(2, "hasChild", Person), t2)
# raises NonSimpleRoleError: qualified number restriction on role 'hasChild' is not
# allowed: 'hasChild' is NON-SIMPLE — it is transitive, or has a transitive sub-role
# via the RBox (a role inclusion into it from a declared-transitive role). Number
# restrictions on non-simple roles make the logic undecidable (Horrocks, Sattler &
# Tobies 1999/2000: SHQ/SHIQ restrict AtLeast/AtMost to SIMPLE roles for exactly
# this reason), so this kit refuses the combination outright rather than risk an
# unsound or non-terminating result.
```

Role hierarchies compose correctly with counting: an `r`-edge counts as an `s`-neighbour for every declared `r ⊑ s`, so `≤n s.C` and `≥n s.C` are decided over every such neighbour, not just literal `s`-edges — see `unicode_logic_kit.dl.tableau`'s "Qualified number restrictions" section for the full tableau algorithm (the ≥-rule, the ≤-rule's merge, and the choose-rule needed for the ≤-rule's completeness) and its termination argument. This counts *neighbours*, not *edges*: if `bob` is reached from `alice` by two DIFFERENT sub-roles of `hasChild` at once, he is still exactly one `hasChild`-neighbour, so a `≤1 hasChild.Person` bound is satisfied (not, say, spuriously violated by counting him twice):

```python
t3 = dl.TBox().add_role_inclusion("hasSon", "hasChild").add_role_inclusion("hasDaughter", "hasChild")
ab3 = (dl.ABox().assert_role("alice", "bob", "hasSon").assert_role("alice", "bob", "hasDaughter")
       .assert_concept("bob", Person).assert_concept("alice", dl.AtMost(1, "hasChild", Person)))
print(dl.abox_consistent(ab3, t3))   # → True (bob counts once, not twice)

ab3.assert_concept("alice", dl.AtMost(0, "hasChild", Person))   # tighten the bound to 0
print(dl.abox_consistent(ab3, t3))   # → False (bob is still a genuine hasChild-neighbour)
```

`dl.concept_to_fol`/`dl.translate.abox_to_fol` route `AtLeast`/`AtMost` through the kit's existing counting-quantifier FOL node, `fol.nodes.Count` (`∃≥n`/`∃≤n`), reusing its already-tested distinct-witnesses expansion rather than a new encoding — this is also the independent Z3-backed oracle `tests/test_dl_alcq.py` cross-checks the tableau against.

OWL Manchester Syntax's `min`/`max`/`exactly` parse into exactly these constructors, with the qualifying class optional (defaulting to `owl:Thing`):

```python
from unicode_logic_kit.dl.owl_manchester import parse_manchester, to_manchester

parse_manchester("hasChild min 2 Person")     # → AtLeast(n=2, role='hasChild', concept=Atomic(name='Person'))
parse_manchester("hasChild min 2")            # → AtLeast(n=2, role='hasChild', concept=Top())
parse_manchester("hasChild exactly 1 Person")
# → And(left=AtLeast(n=1, role='hasChild', concept=Atomic(name='Person')),
#       right=AtMost(n=1, role='hasChild', concept=Atomic(name='Person')))
to_manchester(dl.AtLeast(2, "hasChild", dl.Top()))   # → 'hasChild min 2'
```

`to_manchester` writes a nested operand of the same connective on the RIGHT in parentheses, because `A and B and C` reads back as the left-nested tree; `parse_manchester(to_manchester(c)) == c` holds for every constructor the reader reads:

```python
A, B, C = dl.Atomic("A"), dl.Atomic("B"), dl.Atomic("C")
to_manchester(dl.And(A, dl.And(B, C)))   # → 'A and (B and C)'
to_manchester(dl.And(dl.And(A, B), C))   # → 'A and B and C'
parse_manchester(to_manchester(dl.And(A, dl.And(B, C)))) == dl.And(A, dl.And(B, C))   # → True
```

## ABoxes

`dl.ABox()` collects assertions. `assert_concept(individual, C)` adds `individual : C`; `assert_role(a, b, role)` adds `(a, b) : role`; `assert_distinct(a, b)` adds `a ≠ b` (see "Qualified number restrictions" above — there is no unique name assumption, so this is the only thing that ever forces two individuals apart). All three chain. `dl.abox_consistent(abox, tbox)` checks the whole knowledge base.

```python
import unicode_logic_kit.dl as dl

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
import unicode_logic_kit.dl as dl

print(dl.abox_consistent(dl.ABox()))   # → True

clash = (dl.ABox()
         .assert_concept("a", dl.Atomic("P"))
         .assert_concept("a", dl.Not(dl.Atomic("P"))))
print(dl.abox_consistent(clash))       # → False
```

The TBox constrains every named individual too. With `Cat ⊑ ¬Dog`, asserting that
`nemo` is both a `Cat` and a `Dog` is inconsistent:

```python
import unicode_logic_kit.dl as dl

t = dl.TBox().add(dl.Atomic("Cat"), dl.Not(dl.Atomic("Dog")))
abox = dl.ABox().assert_concept("nemo", dl.And(dl.Atomic("Cat"), dl.Atomic("Dog")))
print(dl.abox_consistent(abox, t))     # → False
```

Role assertions propagate value restrictions: `alice` has only happy children, but `bob` is asserted not happy, so the ∀-rule produces a clash.

```python
import unicode_logic_kit.dl as dl

abox = dl.ABox()
abox.assert_concept("alice", dl.ForAll("hasChild", dl.Atomic("Happy")))
abox.assert_role("alice", "bob", "hasChild")
abox.assert_concept("bob", dl.Not(dl.Atomic("Happy")))
print(dl.abox_consistent(abox))   # → False
```

## Value restrictions, domain/range and individual identity

Three more OWL 2 shapes a real ontology is full of. The in-house tableau decides
two of them — domain/range axioms and individual identity — and **refuses** the
third, the value restriction, by name: the FOL image and the external reasoner
decide it.

`dl.HasValue(role, individual)` is OWL's `ObjectHasValue(r a)` — "has `a` among
its `r`-successors", written `∃r.{a}` in the textbook notation. It is a concept
constructor of its own, deliberately NOT `dl.Exists(role, dl.Nominal(a))`: the
two are distinct OWL 2 structural objects, and the glyph syntax cannot tell them
apart. It can be built, printed, read and written (Manchester `r value a`,
Functional Syntax `ObjectHasValue(r a)`), and its first-order image is the
ground atom, not a minted variable plus an equality:

```python
import unicode_logic_kit.dl as dl

t = dl.TBox().add(dl.Atomic("Sirup"), dl.HasValue("HasStateOfMatter", "Liquid"))
print(dl.HasValue("HasStateOfMatter", "Liquid"))      # → ∃HasStateOfMatter.{Liquid}
print(dl.kb_to_fol(t).tbox.to_unicode_str())
# → ∀x (Sirup(x) → HasStateOfMatter(x, 'Liquid'))
```

An individual whose name starts upper-case is written in single quotes (`'Liquid'`), since a bare upper-case word is a predicate; see "An individual of any name has a printed text" below.

It is also a **nominal**: it names the individual `a` inside a concept. So the
in-house tableau does not decide it, exactly as it does not decide a bare
`Nominal` — `dl.concept_satisfiable`, `dl.abox_consistent` and everything built
on them raise `dl.UnsupportedConceptError`, wherever the value restriction sits:
the queried concept, a TBox axiom (a domain or range included), an ABox
assertion, negated or not.

The reason is a counterexample, not caution. A value restriction gives a
*generated* node an edge back to a *named* one, and the subset blocking the
tableau terminates by does not cover that. Take an asymmetric role `s` whose
range is `∃s.∃s.{b}`. Any `s`-edge `x → y` puts `y` in `∃s.∃s.{b}`, so there are
`y → z` and `z → b`; the edge `z → b` is an `s`-edge too, so `b` is in
`∃s.∃s.{b}` as well, giving `b → w` and `w → b` — which asymmetry forbids. No
`s`-edge can exist, so `∃s.⊤` is unsatisfiable. A tableau rule for value
restrictions that fires on unblocked nodes only answers *satisfiable*: the second
generated node is blocked by the first, a blocked node never gets the edge back to
`b`, and the clash is never seen. The FOL image proves the real verdict, and HermiT agrees:

```python
import unicode_logic_kit.dl as dl
from unicode_logic_kit import api
from unicode_logic_kit.fol.nodes import Not as FNot, Quantifier, Variable

# Asym(s), and range(s) = ∃s.∃s.{b}
tbox = (dl.TBox().add_asymmetric_role("s")
        .add_role_range("s", dl.Exists("s", dl.HasValue("s", "b"))))
query = dl.Exists("s", dl.Top())                      # ∃s.⊤

try:
    dl.concept_satisfiable(query, tbox)
except dl.UnsupportedConceptError as e:
    print("refused:", "ObjectHasValue" in str(e))     # → refused: True

kb = dl.kb_to_fol(tbox)
goal = FNot(Quantifier("∃", Variable("x"), dl.concept_to_fol(query)))   # ¬∃x ∃s.⊤
print(api.prove(goal, list(kb.tbox_premises), timeout=60000).status)    # → proved
# dl.external_concept_satisfiable(query, tbox) is False as well (needs the
# [owl] extra): every dl.external_* entry point decides a value restriction.
```

The `timeout` of `api.prove` is in milliseconds. Whether a rule that fires on
blocked nodes too would be sound and complete is open — the "Value restrictions
(ObjectHasValue)" section of `dl.tableau`'s module docstring records the rule
and what has not been shown — so the kit refuses rather than approximate.

`TBox.add_role_domain(role, C)` and `add_role_range(role, C)` are
`ObjectPropertyDomain`/`ObjectPropertyRange`. They are stored in the role box
rather than desugared into the GCIs `∃r.⊤ ⊑ C` / `⊤ ⊑ ∀r.C` they are equivalent
to, because their image has to be the direct two-variable sentence — the GCI
rewrite prints a tautological `x0 = x0` filler the reader has to decode — and
because `to_owl_functional` has to round-trip the axiom to itself. The TABLEAU
does internalise exactly those GCIs, so there is no new rule and nothing about
termination changes:

```python
import unicode_logic_kit.dl as dl

t = dl.TBox().add_role_domain("Covers", dl.Atomic("Study"))
t.add_role_range("HasUnit", dl.Atomic("Unit"))
for axiom in dl.kb_to_fol(t).axioms:
    print(axiom.to_unicode_str())
# → ∀x ∀y (Covers(x, y) → Study(x))
# → ∀x ∀y (HasUnit(x, y) → Unit(y))

print(dl.subsumes(dl.Exists("Covers", dl.Top()), dl.Atomic("Study"), t))   # → True
```

They are SIDE axioms, like every other role-box kind, so a `TBox` carrying only
a domain axiom still makes `tbox_to_fol` raise `RoleBoxOmittedError` — which is
the point: silently dropping 218 of the Open Energy Ontology's axioms is the
alternative.

`ABox.assert_same(a, b)` is `SameIndividual(a b)`, the mirror of
`assert_distinct`, and `assert_negative_role(a, b, role)` is
`NegativeObjectPropertyAssertion(role a b)` — note the argument order matches
`assert_role`'s, the two individuals first. Sameness is decided by genuine node
MERGING, applied once the branch is set up and before any completion rule runs,
closed under the equivalence the assertions generate (so `a = b` with `b = c`
collapses all three); a negative role assertion by a clash condition over
forbidden edges, closed under the role hierarchy the same way:

```python
import unicode_logic_kit.dl as dl

ab = (dl.ABox()
      .assert_concept("alice", dl.Atomic("Person"))
      .assert_same("alice", "al")
      .assert_negative_role("alice", "bob", "HasChild"))
print(dl.abox_to_fol(ab).to_unicode_str())
# → Person(alice) ∧ alice = al ∧ ¬HasChild(alice, bob)

print(dl.instance_check(ab, "al", dl.Atomic("Person")))   # → True: one element
print(dl.abox_consistent(dl.ABox().assert_same("a", "b").assert_distinct("a", "b")))
# → False: a = b and a ≠ b have no common model
```

Like `assert_distinct(a, a)`, `assert_same(a, a)` is accepted — it is a no-op,
since `a = a` holds in every model. A builder that refused could not hold an
ontology read from a file, and the honest answer to "is this knowledge base
consistent?" is a verdict, not a constructor exception.

### An individual of any name has a printed text

The kit decides predicate-versus-term by the first character's case (see
`fol/_identifiers.py`), so in the first-order grammar a bare word that starts
upper-case is a predicate, and a bare single letter (with digits) is a variable.
An OWL individual is an IRI or a label, where capitals are the norm — every one
of the 98 `ObjectHasValue` fillers in the Open Energy Ontology starts with one.
The printer therefore writes an individual in single quotes whenever its bare
word would not read back as that constant (see "Quoted constants" in the
{doc}`syntax-reference`), and the quoted name is the individual, spelled exactly
as the ontology spells it. An upper-case individual, one spelled like a variable
and the literal `"abc"^^xsd:string` all read back as the formula that was printed:

```python
import unicode_logic_kit.dl as dl
from unicode_logic_kit import api

equal = dl.abox_to_fol(dl.ABox().assert_same("Alice", "Bob"))
print(equal.to_unicode_str())                              # → 'Alice' = 'Bob'
print(api.parse_any(equal.to_unicode_str()).formula == equal)   # → True

image = dl.concept_to_fol(dl.HasValue("HasStateOfMatter", "Liquid"))
print(image.to_unicode_str())                              # → HasStateOfMatter(x, 'Liquid')
print(api.parse_any(image.to_unicode_str()).formula == image)   # → True

variable_like = dl.abox_to_fol(dl.ABox().assert_concept("x1", dl.Atomic("Person")))
print(variable_like.to_unicode_str())                      # → Person('x1')
print(api.parse_any(variable_like.to_unicode_str()).formula == variable_like)   # → True
```

A lower-case individual of two letters or more, such as `alice`, stays bare
(`Person(alice)`). The routes that never go through text — the tableau, and
`api.prove` over `kb_to_fol`'s nodes — answer the same either way.

What still does not read back is a name that is not an individual, because only a
constant has a quoted form. A role or a class is a predicate, and a predicate
starts upper-case in this grammar, so a role spelled in lower case (`hasChild`) is
printed as it is and the text is rejected; the name of a built-in datatype
(`xsd:integer`) is a predicate too, and so is rejected (see "The printed text is
not always readable" in the data-layer section below). Renaming on print would make the
printed formula stop naming the OWL role, so the kit leaves the name alone:

```python
role = dl.concept_to_fol(dl.Exists("hasChild", dl.Atomic("Doctor")))
print(role.to_unicode_str(), api.parse_any(role.to_unicode_str()).ok)
# → ∃x0 (hasChild(x, x0) ∧ Doctor(x0)) False

upper = dl.concept_to_fol(dl.Exists("HasChild", dl.Atomic("Doctor")))
print(upper.to_unicode_str(), api.parse_any(upper.to_unicode_str()).ok)
# → ∃x0 (HasChild(x, x0) ∧ Doctor(x0)) True
```

The domain and range images contain no individual at all and read back whatever
the vocabulary.

## Which route decides what: the axiom-kind table

Every question about a knowledge base has two routes in this kit — the in-house tableau (`dl.concept_satisfiable`, `dl.abox_consistent`, and everything that reduces to them) and the first-order image (`dl.kb_to_fol` handed to `api.prove`). They must never answer the same question differently, and the way that goes wrong in practice is not a wrong rule: it is an axiom kind only ONE route knows about. So the kit keeps one table, `dl.tableau._AXIOM_KINDS`, with a row per axiom kind a `TBox`/`ABox` can hold, saying what each route does with it. Three rules follow from it.

**Builders never refuse.** `TBox.add_*` and `ABox.assert_*` accept every kind, because a `TBox` is what a parser fills from a file — a builder that refused could not hold an ontology the kit is supposed to report on.

**A kind the tableau has no rule for is refused BY NAME, at query time**, with `dl.UnsupportedAxiomError`, from `concept_satisfiable`/`abox_consistent` and so from every function that reduces to them. The message names every refused kind present with its count, and points at the two routes that do answer it: `dl.external_*` (the HermiT-backed reasoner) and `dl.kb_to_fol` + `api.prove`. Nothing is ever approximated or silently dropped. Thirteen kinds are refused today — `InverseObjectProperties`, `SymmetricObjectProperty`, `ReflexiveObjectProperty`, `InverseFunctionalObjectProperty` and a property chain, and the eight kinds of the data layer (see "The data layer: two sorts" below) — and each row's message carries its own reason and remedy (see "The rest of the OWL 2 object property box" above).

**The FOL image keeps the knowledge base and its side axioms apart.** `kb_to_fol(tbox, abox).formula` is the knowledge base; `.side_axioms` are the premises that are deliberately NOT part of it. Each is a `dl.SideAxiom` carrying the OWL 2 keyword it came from, so a census of an ontology's image is a question with an answer:

```python
import unicode_logic_kit.dl as dl

t = dl.TBox().add(dl.Atomic("Cat"), dl.Atomic("Animal"))
t.add_role_inclusion("hasPart", "overlapsWith").add_transitive_role("overlapsWith")
kb = dl.kb_to_fol(t)

print([(a.kind, a.group) for a in kb.side_axioms])
# → [('SubObjectPropertyOf', 'rbox'), ('TransitiveObjectProperty', 'rbox')]
print(len(kb.axioms_of_kind("TransitiveObjectProperty")))   # → 1
print(len(kb.axioms_of_kind("ObjectPropertyDomain")))       # → 0
print(kb.axioms == tuple(a.formula for a in kb.side_axioms))   # → True
```

`kb.axioms` is the bare-formula view of that one field, so the two can never drift apart. `kb.formulas` is the per-axiom list behind `kb.formula`, for a knowledge base big enough that passing `(*kb.formulas, *kb.axioms)` as premises beats passing one large conjunction.

## The data layer: two sorts

OWL 2 has two domains: individuals, and the data values of datatypes (`xsd:integer`, `xsd:string`, …), disjoint from each other. A data property relates an individual to a value; a datatype is a set of values; a data range is a datatype, a restriction of one by facets, an enumeration, or a Boolean combination of those. The kit stores all of it — `DataExists`, `DataForAll`, `DataHasValue`, `DataAtLeast`/`DataAtMost` as concepts, `Literal` and the data ranges as their operands, `TBox.add_data_property_*` / `add_datatype_definition` and `ABox.assert_data` / `assert_negative_data` as axioms — and it reads and writes it in Manchester and Functional-Style syntax:

```python
import unicode_logic_kit.dl as dl

tbox = dl.TBox()
tbox.add_data_property_range(
    "hasAge", dl.parse_manchester_data_range("xsd:integer[>= 0, <= 150]"))
tbox.add(dl.Atomic("Adult"), dl.parse_manchester("hasAge some xsd:integer[>= 18]"))
tbox.add_functional_data_property("hasAge")
abox = dl.ABox().assert_data(
    "alice", "hasAge", dl.parse_manchester_literal('"34"^^xsd:integer'))
```

The Manchester reader tells `hasAge some xsd:integer` (data) from `hasPet some Dog` (object) by the filler: a built-in datatype name, a facet bracket or a `{literal}` makes it a data restriction. Because the filler decides, a CLASS named like a built-in datatype (`xsd:integer`, `rdfs:Literal`, `owl:real`, …, in either namespace spelling, bracketed or not) has no Manchester spelling: `dl.to_manchester` and `dl.role_axiom_to_manchester` refuse it by name, in every position, instead of writing text that the reader takes for a data restriction or refuses. The Functional-Style writer writes it as given, and its reader refuses it. A nominal or a value restriction whose individual is spelled like a numeral is refused too (`r some {3}` is a data one-of, `r value 3` a data value). A role named like a built-in datatype is written as it is; when a restriction on such a role is nested directly in a filler (`r some xsd:integer some Z` is the text of `Exists("r", Exists("xsd:integer", Z))`), the reader refuses the text, it does not misread it. A full IRI is stored without its angle brackets by both readers: `<http://x.org/a>` in Manchester Syntax and in Functional-Style Syntax both give the name `http://x.org/a`, so a datatype, class or individual read by one reader is the same name in a knowledge base or a query read by the other. `dl.to_manchester` and `dl.to_owl_functional` add the brackets again on the way out. A name that does not read back as itself when written bare is written in the syntax's own angle brackets when the kit's reader reads that back as that name (Functional-Style: a name with whitespace or a parenthesis, a class-expression keyword such as `ObjectSomeValuesFrom`, `Annotation`, `_:x`; Manchester: only a full IRI, which needs a scheme and no whitespace, so a name that holds `://` is written `<...>`). A name for which no spelling reads back as exactly that name is refused by name with `ValueError` instead of being written: in Manchester a keyword (`and`, `some`, ...), a name with whitespace, and a name with one of `( ) { } [ ] ,` and no IRI scheme, in both syntaxes a name that already holds the angle brackets of a full IRI and a class named `owl:Thing` or `owl:Nothing` (read back as ⊤ and ⊥ in every spelling), and in Functional-Style a name that holds `>`. `owl:Thing` / `owl:Nothing` are recognised in the abbreviated and the full-IRI spelling alike, including as the datatype of a literal, which both readers refuse by name. A datatype *you* define is an ordinary name, so say so: `dl.parse_manchester(text, datatypes=("Digit",))`. A full IRI in angle brackets is ONE name even when it contains a comma, parentheses or square brackets: `dl.parse_manchester("<http://example.org/a,b(c)[d]> some Dog")` reads as an existential over the role of that name. The glyph syntax has no data layer — `dl.parse_concept` refuses a built-in datatype name by name rather than read `∃hasAge.xsd:integer` as an object restriction.

**The in-house tableau refuses all of it, by name.** It has no data domain: it cannot decide datatype membership, facet arithmetic, how many values a value space has, or that two literals denote different values. So `dl.abox_consistent`, `dl.concept_satisfiable`, `dl.classify` and everything that reduces to them raise `UnsupportedAxiomError` (an axiom) or `UnsupportedConceptError` (a concept) naming every data kind present, and `dl.owl_reasoner` does the same. Nothing is approximated.

**The FOL image answers**, as a *guarded one-sorted* theory over two reserved predicates, `OwlThing` and `OwlData`. A datatype is a unary predicate, a data property a binary one, a literal a term — the number itself for an exact-number literal (`"34"^^xsd:integer` is `34`), a constant named by its OWL text otherwise. A literal is one *value*, however it is spelled: `xsd:normalizedString` and `xsd:token` literals denote the `xsd:string` value of their whitespace-processed text (`"  a  b "^^xsd:token` is `"a b"^^xsd:string`), and an `xsd:anyURI` is compared by its collapsed text. A literal the kit cannot give a term it can stand behind is refused by name rather than approximated: `xsd:float` and `xsd:double` (their value space is not the exact numbers'), `xsd:language`, `xsd:Name`, `xsd:NCName` and `xsd:NMTOKEN` (the kit does not validate their lexical spaces), and a decimal of more than 15 significant digits (`UnsupportedDatatypeError`, with the reason: two different decimals of that length can be one float, `0.30000000000000004` and `0.30000000000000005` are; up to 15 digits a decimal is the number it spells, and a whole value is the integer, so `"1.0"^^xsd:decimal` is `1`). The two sorts are held apart by **side axioms**, so they must be premises:

```python
kb = dl.kb_to_fol(tbox, abox)
print(kb.separation)                      # → two-sorted
for a in kb.side_axioms[:2]:
    print(a.kind, a.group, a.formula.to_unicode_str())
# → FunctionalDataProperty data ∀x ∀v ∀w (hasAge(x, v) ∧ hasAge(x, w) → v = w)
# → DataPropertyRange data ∀x ∀v (hasAge(x, v) → xsd:integer(v) ∧ v ≥ 0 ∧ v ≤ 150)
print(kb.formula.to_unicode_str())
# → ∀x (OwlThing(x) ∧ Adult(x) → ∃x0 (hasAge(x, x0) ∧ (xsd:integer(x0) ∧ x0 ≥ 18))) ∧ hasAge(alice, 34)
```

One name is one predicate, so `dl.kb_to_fol` and the functions that collect the vocabulary (`dl.data_sort_axioms`, `dl.databox_to_fol`, `dl.abox_to_fol`) refuse — with `UnsupportedDatatypeError` — a name used both as an object property and a data property, or both as a class and a datatype, which OWL 2 DL forbids; the image would otherwise read the name as both at once and change what follows (a functional property with an object successor and a data value came out inconsistent). Rename one of the two. A class, an object property and an individual that share a name (punning that OWL 2 DL *does* allow) are accepted: the image holds three symbols, the unary predicate `A(x)`, the binary predicate `A(x, y)` and the constant `A`, and the TPTP route (Vampire, E) and the Z3 route answer over such a knowledge base. The check is made over what one call is given, so `tbox_to_fol`, `rbox_to_fol`, `databox_to_fol` and `abox_to_fol` each see only their own box; `dl.check_kb_names(tbox, abox, ...)` runs the check of `kb_to_fol` over boxes you rendered separately and conjoined by hand. Pass it the `TBox` / `ABox` (or the `KnowledgeBaseFOL`) the images came from, not the formulas, which do not record whether a predicate was an object or a data property:

```python
from unicode_logic_kit import api

# A ⊑ ∃A.B, and the individual A is an A: one name, three symbols
t_pun = dl.TBox().add(dl.Atomic("A"), dl.Exists("A", dl.Atomic("B")))
a_pun = dl.ABox().assert_concept("A", dl.Atomic("A"))
goal = dl.Exists("A", dl.Atomic("B"))
kb_pun = dl.kb_to_fol(t_pun, a_pun, query=[goal])
print(kb_pun.formula.to_unicode_str())
# → ∀x (A(x) → ∃x0 (A(x, x0) ∧ B(x0))) ∧ A('A')
print(api.prove(kb_pun.instance_goal("A", goal), kb_pun.premises, backends=["z3"]).status)   # → proved  (A('A') puts the element A in the class, the inclusion gives it an A-successor in B)

# P is a data property in one box and an object property in the other
t_p = dl.TBox().add_data_property_range("P", dl.Datatype("xsd:integer"))
a_p = dl.ABox().assert_role("a", "b", "P")
dl.databox_to_fol(t_p)      # accepted: in this box P is only a data property
dl.abox_to_fol(a_p)         # accepted: in this box P is only an object property
dl.check_kb_names(t_p, a_p)
# raises dl.UnsupportedDatatypeError: dl.check_kb_names: the name 'P' is used as both an object
# property and a data property in the pieces it is given, taken together ...
```

Six things follow, and the first two are the ones that go wrong if forgotten:

* **Pass the side axioms.** The two-sorted question is the one the prover answers only when the premises are `kb.premises` (the whole knowledge base) or `kb.tbox_premises` (the terminology), which carry the separation, the typing, the datatype lattice and literal distinctness. `kb.formula` alone is a weaker question. `kb.data_axioms` lists just the data layer's part.
* **Let the bundle build the goal, and tell it what you will ask about.** Every GCI of `kb.formula` is restricted to `OwlThing` — otherwise `⊤ ⊑ {a}` would also range over data values and turn an OWL-consistent knowledge base inconsistent — and a goal must be restricted the same way. The side axioms are also derived from the *names the knowledge base uses*, so a goal that names a datatype, a data property, a literal or an object property the knowledge base does not is asked of a weaker theory: a question about `xsd:decimal` over a knowledge base that only mentions `xsd:integer` has no `integer ⊑ decimal` to use. So hand the concepts you are going to ask about to `kb_to_fol(tbox, abox, query=[...])` — their vocabulary joins everything derived from the vocabulary, and a data restriction in the query makes the image two-sorted even when the TBox and ABox have no data layer — and ask through the three methods of the bundle, each of which builds the goal the bundle's `separation` calls for: `kb.subsumption_goal(sub, sup)` and `kb.unsatisfiability_goal(concept)` with `kb.tbox_premises`, `kb.instance_goal(individual, concept)` with `kb.premises`. A concept the bundle does not cover is *refused by name*, saying to pass `query=`, instead of answered wrongly:

```python
from unicode_logic_kit import api

older = dl.parse_manchester("hasAge some xsd:decimal")
kb = dl.kb_to_fol(tbox, abox, query=[older])
api.prove(kb.instance_goal("alice", older), kb.premises, timeout=30000).status        # → 'proved'
api.prove(kb.subsumption_goal(dl.Atomic("Adult"), older), kb.tbox_premises,
          timeout=30000).status                                                         # → 'proved'
# integer ⊑ decimal: a 34 is a decimal, and so is every Adult's age

try:
    dl.kb_to_fol(tbox, abox).instance_goal("alice", older)        # xsd:decimal is not in the knowledge base
except dl.UnsupportedDatatypeError as exc:
    print(str(exc)[:96])
# → KnowledgeBaseFOL.instance_goal: the goal names the datatype 'xsd:decimal', which the knowledge b

clash = dl.And(dl.DataExists("hasAge", dl.Datatype("xsd:integer")),
               dl.DataForAll("hasAge", dl.Datatype("xsd:string")))
kb = dl.kb_to_fol(dl.TBox(), query=[clash])                      # a TBox with no data layer at all
api.prove(kb.unsatisfiability_goal(clash), kb.tbox_premises, timeout=30000).status   # → 'proved'
```

  `clash` is unsatisfiable in OWL 2 because `xsd:integer` and `xsd:string` are disjoint; the closure `∃x concept_to_fol(clash)` on its own is *satisfiable* (a data value satisfies it), which is why the registry edge `alc → fol` refuses a concept with a data restriction and points here. Without a data layer the three methods build exactly the spellings the earlier releases documented (`dl.subsumption_to_fol`, `¬∃x π(C, x)`, `π(C, a)`); a hand-built subsumption goal on a two-sorted bundle needs `dl.subsumption_to_fol(sub, sup, object_sort=True)`, and the unrelativised default asks about data values too and answers `refuted` for a pure object-level subsumption that holds.
* **A `refuted` is not a verdict when there is a data layer.** The image is sound — every OWL model expands to a model of it — so `proved` always transfers to OWL 2. It is not complete, so `refuted` means only that *the image* has a countermodel, and `kb.refutation_is_decisive` is `False` exactly when there is a data layer (with none, the image is faithful and `refuted` is a real "no"). Three things it does not state: a facet is an uninterpreted comparison, so with `DataPropertyRange(HasN xsd:integer[>= 10])` the assertion `HasN(a, 5)` is OWL-inconsistent and the image says `refuted` (consistent), and `HasN(a, 15)` entails `a : ∃HasN.xsd:integer[>= 3]` in OWL while the image has no fact `15 ≥ 3`; a literal is typed only by the datatype it was written with, so `d(a, "1.0"^^xsd:decimal)` entails `a : ∃d.xsd:integer` (the value 1 is an integer), `d(a, "5"^^xsd:int)` entails `a : ∃d.xsd:nonNegativeInteger` and `d(a, "-1"^^xsd:int)` entails `a : ∃d.xsd:negativeInteger`, each `refuted`; and the number of values in a value space is not stated. An `unknown` is no answer in either direction. Decide facet entailment directly with `atp.z3_arith.is_valid_arith` (timeout in milliseconds): `∀v (xsd:integer(v) ∧ v ≥ 18 → xsd:integer(v) ∧ v ≥ 0)`, built from `dl.datarange_to_fol`, is valid with `sort="int"`. Choose the sort by the base datatype: **`sort="real"` for an `xsd:decimal` base** — over `int` the arithmetic calls `xsd:decimal[> 0] ⊑ xsd:decimal[>= 1]` valid, and OWL 2 refutes it (0.5 is a decimal).
* **Scope of facets.** `xsd:minInclusive`/`maxInclusive`/`minExclusive`/`maxExclusive` on an exact-number base are read; `xsd:length`, `xsd:pattern` and the rest are refused by name — string length and regular expressions are not first-order, and a facet that constrained nothing would be a silent weakening.
* **Distinctness is quadratic.** Two different literals of one family (numbers, strings, `xsd:anyURI`, booleans) are different values, stated pairwise: a knowledge base with 1000 distinct integer literals carries 499,500 `LiteralDistinctness` axioms.
* **The printed text is not always readable.** An image that names a built-in datatype (`xsd:integer(x0)`) prints text that `api.parse_any` rejects, because the datatype is a predicate and a predicate has no quoted form — a deliberate carve-out from "what the kit prints reads back": that name is OWL's, not the kit's to rename, and `api.prove` takes the nodes, not the text. A non-numeric literal is a constant and has one: `"abc"^^xsd:string` prints `'"abc"^^xsd:string'` and reads back. To print an image the kit reads, rename its symbols with `sanitize_all` over the *whole* premise list, so one mapping serves every formula; `sanitize_names` applied to each formula with a fresh mapping gives `xsd:integer` and a class called `Xsdinteger` the same token:

```python
from unicode_logic_kit.fol.sanitize import sanitize_all

text = dl.concept_to_fol(dl.DataExists("hasAge", dl.Datatype("xsd:integer"))).to_unicode_str()
print(text, api.parse_any(text).ok)
# → ∃x0 (hasAge(x, x0) ∧ xsd:integer(x0)) False
names_tbox = dl.TBox().add_data_property_range("HasN", "xsd:integer").add(dl.Atomic("Xsdinteger"), dl.Atomic("B"))
image = dl.kb_to_fol(names_tbox)
legal, mapping = sanitize_all([image.tbox, *image.axioms])
print(legal[1].to_unicode_str(), all(api.parse_any(f.to_unicode_str()).ok for f in legal))
# → ∀x ∀v (HasN(x, v) → Xsdinteger2(v)) True
```

`separation="data-lattice"` keeps the datatype facts without the object/data separation, and a knowledge base with no data layer is rendered exactly as before, whatever `separation` says. It is not a cheaper version of the default, and it is not sound for a knowledge base with a data layer: its GCIs are not restricted to the objects, so a `⊤ ⊑ {a}` also ranges over data values and the premises are *stronger* than OWL 2's — an OWL-consistent knowledge base can have an inconsistent image, from which everything is proved. The three goal methods therefore refuse a data-layer bundle that is not two-sorted. The default regime does add premises — every GCI restricted to `OwlThing`, every role typed — and on some TBoxes z3 gives up on a question the data-free image decides at once (a single GCI `⊤ ⊔ ⊤ ⊑ ∃r.C` beside an unrelated data range, asking `⊤ ⊑ ¬⊤`, is `unknown`); then `unknown` is the answer.

## OWL 2 Functional-Style Syntax

`unicode_logic_kit.dl.owl_functional` reads and writes a whole ontology *document* — not just a single class expression or axiom, like OWL Manchester Syntax above — in the W3C's [OWL 2 Functional-Style Syntax](https://www.w3.org/TR/owl2-syntax/#Functional-Style_Syntax), restricted to ALCHQ. Unlike Manchester Syntax's keyword-infix notation, Functional Syntax is a flat `Keyword(arg arg ...)` S-expression form, so there is no precedence to resolve when rendering: every compound expression is already fully parenthesised by its own keyword.

`dl.to_owl_functional(tbox, abox, ontology_iri=...)` writes a `Declaration(...)` block for every class/role/individual name referenced, the RBox (`SubObjectPropertyOf`/`TransitiveObjectProperty`), the TBox's inclusions (as `SubClassOf`/`EquivalentClasses`), and the ABox's assertions (`ClassAssertion`/`ObjectPropertyAssertion`/`DifferentIndividuals`); `dl.parse_owl_functional(text)` reads it all back into a `(TBox, ABox)` pair:

```python
import unicode_logic_kit.dl as dl

Person, Doctor = dl.Atomic("Person"), dl.Atomic("Doctor")
t = dl.TBox().add(Doctor, dl.And(Person, dl.Exists("hasChild", Doctor)))
t.add_role_inclusion("hasSon", "hasChild")
t.add_transitive_role("hasChild")

ab = dl.ABox().assert_concept("alice", Doctor)
ab.assert_role("alice", "bob", "hasChild")

text = dl.to_owl_functional(t, ab, ontology_iri="http://example.org/family")
print(text)
# → Ontology(<http://example.org/family>
#     Declaration(Class(Doctor))
#     Declaration(Class(Person))
#     Declaration(ObjectProperty(hasChild))
#     Declaration(ObjectProperty(hasSon))
#     Declaration(NamedIndividual(alice))
#     Declaration(NamedIndividual(bob))
#     SubObjectPropertyOf(hasSon hasChild)
#     TransitiveObjectProperty(hasChild)
#     SubClassOf(Doctor ObjectIntersectionOf(Person ObjectSomeValuesFrom(hasChild Doctor)))
#     ClassAssertion(Doctor alice)
#     ObjectPropertyAssertion(hasChild alice bob)
#   )

t2, ab2 = dl.parse_owl_functional(text)
print(t2 == t, ab2 == ab)   # → True True
```

A role inclusion may carry an inverse role on either side — `add_role_inclusion("r", dl.InverseRole("s"))` — and the writer and the reader agree on it: `SubObjectPropertyOf(r ObjectInverseOf(s))`, read back as the same `InverseRole`, and written again byte for byte. Every other position that takes a role (a characteristic, a domain or range, a restriction in a class expression) refuses `ObjectInverseOf` by name, as the builders do: write the equivalent plain axiom instead, for instance `InverseFunctionalObjectProperty(r)` for `FunctionalObjectProperty(ObjectInverseOf(r))`.

A single class expression parses/renders independently via `dl.parse_owl_functional_class_expression`/`dl.to_owl_functional_class_expression`, the Functional-Syntax analogue of `parse_manchester`/`to_manchester`:

```python
c = dl.parse_owl_functional_class_expression(
    "ObjectIntersectionOf(Person ObjectSomeValuesFrom(hasChild Doctor))")
print(c)                                      # → Person ⊓ ∃hasChild.Doctor
print(dl.to_owl_functional_class_expression(c))
# → 'ObjectIntersectionOf(Person ObjectSomeValuesFrom(hasChild Doctor))'
```

`ObjectMinCardinality`/`ObjectMaxCardinality`/`ObjectExactCardinality` map onto `AtLeast`/`AtMost` exactly like Manchester's `min`/`max`/`exactly` (`ObjectExactCardinality` desugars to their conjunction at parse time), and `EquivalentClasses`/`DisjointClasses`/`DifferentIndividuals` — each genuinely n-ary in the OWL grammar, with no direct n-ary counterpart in `TBox`/`ABox` — are decomposed at parse time: `EquivalentClasses(A B C)` into the pairwise-consecutive chain `add_equivalence(A, B)`, `add_equivalence(B, C)` (sound, since ⊑ is transitive); `DisjointClasses`/`DifferentIndividuals` into *every* unordered pair (not a chain — disjointness and distinctness have no transitive shortcut the way equivalence does), so `DisjointClasses(A B C)` becomes three GCIs `A ⊓ B ⊑ ⊥`, `A ⊓ C ⊑ ⊥`, `B ⊓ C ⊑ ⊥`, and `DifferentIndividuals(a b c)` becomes three `assert_distinct` calls covering all three pairs — never fewer, since (with no unique name assumption — see "Qualified number restrictions" above) omitting even one pair would silently understate what the axiom actually asserts.

Every construct outside ALCHQ is rejected by its OWL name, the same honesty convention as Manchester Syntax:

```python
from unicode_logic_kit.dl.owl_functional import OwlFunctionalSyntaxError

try:
    dl.parse_owl_functional("Ontology(SubClassOf(A ObjectHasSelf(r)))")
except OwlFunctionalSyntaxError as e:
    print(e)
# → parse_owl_functional: Self restrictions (ObjectHasSelf) is not supported —
#   outside ALCHQ (this kit's DL fragment), found 'ObjectHasSelf' at position 22
#   in 'Ontology(SubClassOf(A ObjectHasSelf(r)))'
```

### Reading a whole ontology: the refusals as data

`dl.parse_owl_functional` is strict, and stays so: it raises on the FIRST
construct outside the fragment, which for a 4041-axiom ontology carrying one
`HasKey` means no TBox at all. `dl.parse_owl_functional_axioms` is
the per-axiom reader — one tokenization, one pass, recovering at AXIOM
boundaries — and returns everything it could read plus one `RefusedAxiom` per
axiom it could not:

```python
import unicode_logic_kit.dl as dl

doc = dl.parse_owl_functional_axioms(
    "Ontology(SubClassOf(A B) HasKey(A () (r)) SubClassOf(B C))")
print(doc.accepted, len(doc.refused), doc.ok)   # → 2 1 False
print(doc.refused_keywords)                      # → {'HasKey': 1}
print(doc.refused[0].text, doc.refused[0].position)
# → HasKey(A () (r)) 25
print(doc.tbox.inclusions)
# → [(Atomic(name='A'), Atomic(name='B')), (Atomic(name='B'), Atomic(name='C'))]

kb = doc.to_kb()        # == dl.kb_to_fol(doc.tbox, doc.abox)
```

A third list reports what was read and found to carry **no logical content**:
`doc.consumed` holds one `ConsumedAxiom` per annotation-property axiom
(`SubAnnotationPropertyOf`, `AnnotationPropertyDomain`,
`AnnotationPropertyRange`) and per tautological property inclusion
(`SubObjectPropertyOf(P owl:topObjectProperty)` and its data and bottom
twins). They build nothing — dropping a tautology loses no truth — but they
*look* logical, so they are reported rather than vanishing, and `accepted +
skipped + len(consumed) + len(refused)` is the document's axiom count. A
property inclusion that is *not* a tautology (`owl:topObjectProperty ⊑ P`, or a
data property under `owl:topObjectProperty`) is refused, not consumed. The strict
`dl.parse_owl_functional` drops the annotation-property axioms and the
tautological property inclusions *without a report*; `parse_owl_functional_axioms`
lists them in `.consumed`.

Four more things the reader decides at read time. A literal with no first-order
term (`xsd:float`/`xsd:double`, `xsd:language`/`xsd:Name`/`xsd:NCName`/`xsd:NMTOKEN`,
a decimal of more than 15 significant digits) is refused as a `RefusedAxiom` keyed by its
datatype, so an axiom that is `accepted` is one `to_kb()` can render — though
`to_kb()` may still refuse the knowledge base as a whole, for a name used as two
kinds of thing, or for a cyclic datatype definition in a result assembled by hand.
A `DatatypeDefinition` that closes a cycle with one read earlier in the document
(`DatatypeDefinition(A B)` then `DatatypeDefinition(B A)`), or gives a name a second
and different definition (`A` is `xsd:integer`, then `xsd:string`), is a
`RefusedAxiom` keyed `DatatypeDefinition`, with the strict reader's reason; it is
not stored and the earlier definitions are kept. The same definition said twice is
accepted. Both OWL readers (Functional-Style
and Manchester) refuse a built-in datatype name where a class is wanted, and
`owl:Thing`/`owl:Nothing` where a data range is wanted. And a class expression
nested about a thousand levels deep raises `RecursionError` — the readers are
recursive — rather than a refusal.

`refused[i].reason` is the full refusal message, still naming the construct and
saying what to use instead — the refusals are part of the RESULT, so a caller
who ignores them is choosing to, in writing. `to_kb()` is the method to reach
for next rather than `tbox_to_fol`, because it carries the role box as separate
premises; `tbox_to_fol` would refuse the TBox outright for exactly that reason.

It recovers from one thing only: `OwlFunctionalUnsupportedError`, the subclass
raised for input that is valid OWL 2 outside this fragment. MALFORMED input — an
unterminated IRI, an unbalanced paren, a missing `Ontology(`, trailing text —
still raises, because recovering from one of those could silently drop
arbitrary content. Each axiom is parsed into a scratch `TBox`/`ABox` and merged
only on success, so a refused axiom provably leaves nothing behind.


A `∀r` and an `∃r` on the same individual interact even without an explicit role edge:
asserting `a : ∀r.A` together with `a : ∃r.¬A` forces the generated witness to be both
`A` and `¬A`:

```python
import unicode_logic_kit.dl as dl

A = dl.Atomic("A")
abox = (dl.ABox()
        .assert_concept("a", dl.ForAll("r", A))
        .assert_concept("a", dl.Exists("r", dl.Not(A))))
print(dl.abox_consistent(abox))   # → False
```

## Inverse roles and nominals (I, O): the external OWL 2 DL reasoner

Two constructs sit outside ALCHQ, this kit's in-house DL fragment: `InverseRole("r")` (the role expression `r⁻`, used wherever a plain role name is expected) and `Nominal("a")` (the singleton concept `{a}`; its disguise, the value restriction `HasValue("r", "a")` = `∃r.{a}`, is refused with it — see "Value restrictions" above for the counterexample). `dl.concepts`/`dl.tableau` recognise them all — they can be built, printed, and negated — but the in-house tableau refuses to *reason* over them, by name, rather than risk an unsound or silently-incomplete result:

```python
import unicode_logic_kit.dl as dl

A = dl.Atomic("A")
r = "r"

try:
    dl.concept_satisfiable(dl.Exists(dl.InverseRole(r), A))
except dl.UnsupportedConceptError as e:
    print(e)
# → dl.tableau: an InverseRole (r⁻) is outside ALCHQ (this kit's in-house DL
#   fragment) — no in-house tableau rule decides it (see the module docstring's
#   'Inverse roles and nominals (I, O)' section for why: it breaks subset
#   blocking's soundness/completeness argument). Use dl.owl_reasoner's
#   external, HermiT-backed reasoner instead.
```

Every entry point built on `dl.tableau.subsumes`/`abox_consistent` refuses it too: `subsumes`, `equivalent` and `instance_check` by reduction, and `dl.classify`, `instance_retrieval`, `realize` and `realize_all` by running the same guard themselves (a reduction with nothing to reduce would otherwise return before any guard had run). `dl.translate`, by contrast, translates both faithfully to FOL (`r⁻` swaps the role atom's argument order; `{a}` becomes the equality `x = a`) — see `unicode_logic_kit.dl.translate`'s module docstring. `to_manchester` can still *render* a concept using either (useful for diagnostics), while `parse_manchester` keeps refusing the matching input, unchanged:

```python
c = dl.Exists(dl.InverseRole("hasChild"), dl.Top())
print(dl.to_manchester(c))               # → 'inverse hasChild some owl:Thing'
try:
    dl.parse_manchester(dl.to_manchester(c))
except dl.ManchesterSyntaxError as e:
    print(e)
# → parse_manchester: inverse roles ('inverse r') — not supported outside ALC
#   (found 'inverse' at position 0) in 'inverse hasChild some owl:Thing'

print(dl.to_manchester(dl.Nominal("alice")))   # → '{alice}'
```

`to_owl_functional`/`to_owl_functional_class_expression`, unlike `to_manchester`, do **not** get this export-only exception: they refuse `InverseRole`/`Nominal` in both directions, exactly like every other construct outside ALCHQ — named in the error, not a low-level crash:

```python
try:
    dl.to_owl_functional_class_expression(c)   # same c = ∃hasChild⁻.⊤ as above
except TypeError as e:
    print(e)
# → to_owl_functional_class_expression: the inverse role hasChild⁻ (InverseRole)
#   is outside ALCHQ (this kit's DL fragment) -- OWL 2 Functional-Style Syntax
#   rendering only covers ALCHQ, the same fragment this module's parser
#   accepts. Use dl.to_manchester for a diagnostic-only rendering that does
#   support inverse roles (I) and nominals (O), or dl.owl_reasoner to actually
#   decide a concept that needs them.
```

To actually *decide* a concept that needs I/O, use `dl.owl_reasoner`'s external, HermiT-backed reasoner (`pip install unicode-logic-kit[owl]`, an optional dependency — `dl.owl_reasoner_available()` checks whether it is installed). Every `dl.external_*` function mirrors its in-house-tableau namesake's signature and reduction exactly, just decided over the bigger ALCHQ + I + O fragment:

```python
print(dl.owl_reasoner_available())   # → True (once the 'owl' extra is installed)

# (alice, bob):hasChild entails bob : ∃hasChild⁻.⊤ — bob has an INCOMING
# hasChild edge, i.e. an hasChild-inverse successor (alice).
ab = dl.ABox().assert_role("alice", "bob", "hasChild")
query = dl.Exists(dl.InverseRole("hasChild"), dl.Top())
print(dl.external_instance_check(ab, "bob", query))   # → True

# {alice} ⊓ {bob}: satisfiable absent an explicit distinctness assertion —
# OWL 2 has no unique name assumption, exactly like this kit's own ABoxes.
concept = dl.And(dl.Nominal("alice"), dl.Nominal("bob"))
print(dl.external_concept_satisfiable(concept))   # → True

ab2 = dl.ABox().assert_distinct("alice", "bob").assert_concept("_probe", concept)
print(dl.external_abox_consistent(ab2))   # → False: alice and bob can no longer coincide
```

`dl.external_concept_satisfiable` asks its question about a probe individual of its own, named so that no individual of the concept or the TBox bears the name. A hand-written ABox like `ab2` must not reuse a name that a nominal of the concept already names: with `{_probe} ⊑ A`, the concept `¬A ⊓ ∃r.{_probe}` is satisfiable (its witness is some other element), but asserted of an individual named `_probe` it makes the knowledge base inconsistent.

`dl.owl_reasoner` spawns a fresh `java` subprocess (HermiT, via `owlready2`) per call, so it is orders of magnitude slower than the in-house tableau — expected for an occasional cross-check over the I/O-extended fragment, not a hot-path reasoner. See `unicode_logic_kit.dl.owl_reasoner`'s module docstring for the full translation and licensing (`owlready2` is LGPL-3.0-or-later) notes.

## A second, independent external oracle: Hets/FaCT++

`dl.owl_reasoner` is one external OWL 2 DL route (HermiT, in-process via `owlready2`). `unicode_logic_kit.hets.owl_backend` is a second, INDEPENDENT one: it renders the same `TBox`/`ABox`/`Concept` AST to an OWL 2 Functional-Style Syntax document, uploads it to a running [Hets](https://github.com/spechub/Hets) server (`unicode_logic_kit.hets`, the same Docker-backed REST server the kit's FOL route uses — see the [interoperability guide](interoperability.md)), and asks it to run `Fact` (FaCT++, a *different* reasoner implementation, LGPL-2.1) via `POST /consistency-check`. Agreement between two independently-implemented reasoners, reached two structurally different ways (an in-process JVM binding vs. a Docker container's REST API), is a stronger correctness signal than either alone — this is why it exists, not to replace `dl.owl_reasoner`.

It lives outside the `dl` package on purpose (in `unicode_logic_kit.hets`, alongside the kit's other Hets/Docker integration) and mirrors `dl.owl_reasoner`'s function-per-namesake shape exactly, over the same ALCHQ + I + O fragment:

```python
from unicode_logic_kit.hets.owl_backend import (
    hets_owl_available, external_subsumes, external_instance_check,
)

print(hets_owl_available())   # → True iff a Hets server answers right now (never starts one)

t = dl.TBox().add(dl.Atomic("A"), dl.Atomic("B")).add(dl.Atomic("B"), dl.Atomic("C"))
print(dl.subsumes(dl.Atomic("A"), dl.Atomic("C"), t))                # → True  (in-house tableau)
print(external_subsumes(dl.Atomic("A"), dl.Atomic("C"), t))          # → True  (FaCT++ via Hets)

# The I/O fragment: same textbook case as dl.owl_reasoner's example above,
# decided by a different reasoner over the same REST/Docker boundary the
# kit's FOL route already uses.
ab = dl.ABox().assert_role("alice", "bob", "hasChild")
query = dl.Exists(dl.InverseRole("hasChild"), dl.Top())
print(external_instance_check(ab, "bob", query))   # → True
```

Like `dl.owl_reasoner` and `unicode_logic_kit.atp.hets_backend`, this is opt-in and never part of any default chain: no function here starts a container, and `hets_owl_available()` only ever checks whether one is already reachable. It needs Docker running with the `spechub2/hets` image, nothing extra pip-installed (it talks plain HTTP, the same as the rest of `unicode_logic_kit.hets`). See `unicode_logic_kit.hets.owl_backend`'s module docstring for the live capability spike that justified building this at all (which reasoners the image actually offers, and why), and `unicode_logic_kit.hets.docker`'s "OWL 2 / description-logic support" section for the underlying wire-protocol facts.

## Cyclic TBoxes terminate

A GCI such as `A ⊑ ∃r.A` would naively generate an infinite chain of `r`-successors. The tableau uses **subset blocking**: a generated individual whose label is contained in that of an earlier individual is not expanded (its successors are reused). This is sound and complete for ALC, so cyclic axioms terminate.

```python
import unicode_logic_kit.dl as dl

A = dl.Atomic("A")
t = dl.TBox().add(A, dl.Exists("r", A))   # A ⊑ ∃r.A
print(dl.concept_satisfiable(A, t))       # → True  (terminates via blocking)
```

Blocking only suppresses *redundant* expansion; a genuine contradiction along the
generated chain is still found. If the same `r`-successor required by the cycle is also
forced to be empty (`∀r.⊥`), the concept is unsatisfiable:

```python
import unicode_logic_kit.dl as dl

A = dl.Atomic("A")
t = dl.TBox().add(A, dl.And(dl.Exists("r", A), dl.ForAll("r", dl.Bottom())))
print(dl.concept_satisfiable(A, t))       # → False (∃r.A and ∀r.⊥ clash)
```

And the cyclic concept can still impose constraints that interact with extra
assumptions. Here `A ⊑ ∃r.A ⊓ ¬B`, so nothing in `A` is ever `B`:

```python
import unicode_logic_kit.dl as dl

A, B = dl.Atomic("A"), dl.Atomic("B")
t = dl.TBox().add(A, dl.And(dl.Exists("r", A), dl.Not(B)))
print(dl.concept_satisfiable(A, t))               # → True
print(dl.concept_satisfiable(dl.And(A, B), t))    # → False
```

### Cyclic TBox examples: linked structures

Express recursive structures that reference themselves:

```python
import unicode_logic_kit.dl as dl

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
import unicode_logic_kit.dl as dl

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
import unicode_logic_kit.dl as dl

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

### TBox classification: the whole hierarchy at once

`dl.classify(tbox, concepts=None)` reproduces, as data, exactly the hierarchy the
prose above describes by hand: it collects every named concept mentioned in the
TBox, decides `dl.subsumes` for every pair, and returns a `Classification` —
`equivalents` (mutual-subsumption synonym classes, keyed by the lexicographically
smallest name in each), `parents`/`children` (the transitively-reduced Hasse
diagram — *direct* super-/sub-concepts only), and `ancestors` (the full transitive
closure, a free byproduct of the pairwise matrix). It is itself a pure reduction to
`dl.subsumes`, so it adds no reasoning risk beyond what the tableau already carries.

```python
import unicode_logic_kit.dl as dl

Person, Male, Female = dl.Atomic("Person"), dl.Atomic("Male"), dl.Atomic("Female")
Parent, Mother, Father = dl.Atomic("Parent"), dl.Atomic("Mother"), dl.Atomic("Father")

t = (dl.TBox()
     .add_equivalence(Parent, dl.And(Person, dl.Exists("hasChild", Person)))
     .add_equivalence(Mother, dl.And(Parent, Female))
     .add_equivalence(Father, dl.And(Parent, Male))
     .add(Male, dl.Not(Female)))

cl = dl.classify(t)
# cl.children/.parents/.ancestors are frozensets, so their repr's element
# order is hash-seed-dependent, not the sorted order shown below — sort
# before printing (or comparing) whenever the order itself matters.
print(sorted(cl.children["Person"]))   # → ['Parent']
print(sorted(cl.children["Parent"]))   # → ['Father', 'Mother']

# Mother ≡ Parent ⊓ Female: both are direct parents, since neither subsumes
# the other, and Person is only an *ancestor* of Mother, not a direct parent.
print(sorted(cl.parents["Mother"]))    # → ['Female', 'Parent']
print(sorted(cl.ancestors["Mother"]))  # → ['Female', 'Parent', 'Person']
```

### End-to-end example: university domain

A realistic scenario with multiple concept levels, roles, and consistency checking:

```python
import unicode_logic_kit.dl as dl

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
import unicode_logic_kit.dl as dl

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

bad = dl.And(EBook, PhysicalProduct)
print(dl.concept_satisfiable(bad, t))           # → False (an EBook is digital, and nothing physical is)
# "tangible" alone is not enough: PhysicalProduct ⊑ Tangible, but not the converse
print(dl.concept_satisfiable(dl.And(EBook, Tangible), t))  # → True

inventory = (dl.ABox()
             .assert_concept("item-1", PrintedBook)
             .assert_concept("item-2", EBook))

print(dl.abox_consistent(inventory, t))  # → True
```

