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

## Rendering

`Concept.to_unicode()` renders with the standard DL glyphs and precedence-aware parenthesisation (binding order: atoms/⊤/⊥ tightest, then ¬ / ∃ / ∀, then ⊓, then ⊔). `str(C)` is an alias.

```python
import unicode_fol_kit.dl as dl

c = dl.Or(dl.Atomic("A"), dl.And(dl.Atomic("B"), dl.Not(dl.Atomic("C"))))
print(c.to_unicode())                                  # → A ⊔ B ⊓ ¬C
print(dl.ForAll("r", dl.Or(dl.Atomic("A"), dl.Atomic("B"))).to_unicode())  # → ∀r.(A ⊔ B)
print(dl.Top().to_unicode(), dl.Bottom().to_unicode())  # → ⊤ ⊥
```

## Negation normal form

`dl.nnf(C)` pushes ¬ inward so that negation occurs only on atomic concepts, using the De Morgan and modal dualities (`¬⊤=⊥`, `¬¬C=C`, `¬(C⊓D)=¬C⊔¬D`, `¬∃r.C=∀r.¬C`, `¬∀r.C=∃r.¬C`). This is the shape the tableau consumes.

```python
import unicode_fol_kit.dl as dl

neg = dl.Not(dl.Exists("r", dl.And(dl.Atomic("A"), dl.Atomic("B"))))
print(dl.nnf(neg).to_unicode())   # → ∀r.(¬A ⊔ ¬B)

print(dl.nnf(dl.Not(dl.ForAll("r", dl.Atomic("A")))).to_unicode())  # → ∃r.¬A
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

Role assertions propagate value restrictions: `alice` has only happy children, but `bob` is asserted not happy, so the ∀-rule produces a clash.

```python
import unicode_fol_kit.dl as dl

abox = dl.ABox()
abox.assert_concept("alice", dl.ForAll("hasChild", dl.Atomic("Happy")))
abox.assert_role("alice", "bob", "hasChild")
abox.assert_concept("bob", dl.Not(dl.Atomic("Happy")))
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
