# Verifying the definitions themselves

{doc}`model-checking` asks whether a definition holds of a structure you have.
This page asks a question that comes *before* any data: is the definition set
coherent at all? Is a class satisfiable, or has it been written so that nothing
can ever be one? Does the subclass actually entail its superclass? Is the
"specialisation" logically equivalent to what it claims to specialise?

None of these touch a molecule, a graph or any other structure. They are decided
from the definitions' own logical content, through the kit's prover chain and
finite model finder. They matter because a scoring run cannot tell you any of
them: a definition that is unsatisfiable simply never fires, and in a precision
and recall table that looks like a cautious classifier rather than a broken one.

## First: syntax repair that costs no generation attempt

Machine-generated TPTP fails in a small number of recurring ways, and most of
them are mechanical. `repair_tptp_formula` fixes what can be fixed
meaning-preservingly and *reports* what cannot.

```python
from unicode_fol_kit import repair_tptp_formula

r = repair_tptp_formula("p <=> q & r")
print(r.ok, r.changed)             # → True True
print(r.repaired_text)             # → (p <=> (q & r))
print([i.kind for i in r.issues])  # → ['bracket_normalisation']
```

The rewrite is meaning-preserving because the kit's own TPTP parser already reads
the input with that precedence — the brackets only make explicit what was already
parsed, which the test suite pins with an equivalence check rather than a claim.
Some TPTP tools are stricter than the standard here, so the bracketed form is the
one to hand on.

A chemical name that is not a legal unquoted TPTP functor gets **quoted**, not
sanitised:

```python
from unicode_fol_kit import repair_tptp_formula

r = repair_tptp_formula("1,2-diacyl-sn-glycero(X)")
print(r.repaired_text)             # → '1,2-diacyl-sn-glycero'(X)
print([i.kind for i in r.issues])
# → ['invalid_predicate_name', 'free_variable']
```

Quoting preserves the full name, locant prefixes and all; inventing a camel-case
replacement would silently discard chemically meaningful information and break the
link to the ontology class.

Free variables are the case that is *reported and left alone*. Closing them would
change what the author claimed, so it happens only on explicit opt-in
(`close_free_variables=True`):

```python
from unicode_fol_kit import repair_tptp_formula

r = repair_tptp_formula("threeOxoSteroid(X) <=> (?[A]: c(A))")
print(r.ok)                                     # → True
print([i.kind for i in r.issues])
# → ['bracket_normalisation', 'free_variable']
```

`repair_tptp_problem` does the same across a whole `fof(...)` file, entry by
entry:

```python
from unicode_fol_kit import repair_tptp_problem

p = repair_tptp_problem("fof(a, axiom, p <=> q & r).\n"
                        "fof(b, axiom, s <=> t | u).")
print(p.ok, p.changed)   # → True True
print(p.repaired_text)
# → fof(a, axiom, (p <=> (q & r))).
#   fof(b, axiom, (s <=> (t | u))).
```

## The definition map

A definition is a **named 0-ary predicate with a defining body** — the
`className <=> body` shape ontology exports use. The kit represents a set of them
as a plain mapping from name to body:

```python
from unicode_fol_kit import chem

definitions = {
    "Molecule":               chem.parse_chemlog_tptp("net_charge_neutral"),
    "OrganicMolecularEntity": chem.parse_chemlog_tptp("molecule & ?[A1]: c(A1)"),
    "Hydrocarbon":            chem.parse_chemlog_tptp(
        "organicMolecularEntity & ?[A1]: (c(A1) & ?[A2]: (h(A2) & bond(A1,A2)))"),
}
print(definitions["Hydrocarbon"].to_unicode_str())
# → OrganicMolecularEntity ∧ ∃a1 (c(a1) ∧ ∃a2 (h(a2) ∧ bond(a1, a2)))
```

```{warning}
The key must be spelled exactly as the atom appears **in the parsed AST**, not as
it was written in the source text. The TPTP importer inverts the case convention,
so `molecule` in the TPTP body arrives as the atom `Molecule` — hence the
capitalised keys above. Key it `"molecule"` instead and nothing breaks loudly:
the body's `Molecule` is then simply an undefined primitive, unfolding stops
there, and a subsumption that should be *entailed* comes back *refuted*. There is
no way to detect this in general, because an atom that is not a key is a perfectly
legitimate primitive (`net_charge_neutral` above is one).
```

## Circularity, satisfiability, subsumption

`find_cycles` reports definitional cycles as paths, before any prover runs:

```python
from unicode_fol_kit import chem
from unicode_fol_kit.eval import find_cycles, check_satisfiable

cyclic = {"A": chem.parse_chemlog_tptp("b & ?[X]: c(X)"),
          "B": chem.parse_chemlog_tptp("a")}
print(find_cycles(cyclic))   # → (('A', 'B', 'A'),)
print(check_satisfiable("A", cyclic).status)   # → cyclic
```

Note the status: `cyclic`, not `unknown` and not `unsatisfiable`. A circular
biconditional is a *proven* defect of the definition set, and reporting it as an
inconclusive result would hide it among the genuine timeouts.

`check_satisfiable` unfolds a definition and asks whether anything at all can
satisfy it:

```python
from unicode_fol_kit import chem
from unicode_fol_kit.eval import check_satisfiable

impossible = {"Impossible": chem.parse_chemlog_tptp("?[X]: (c(X) & ~c(X))")}
r = check_satisfiable("Impossible", impossible)
print(r.status, r.backend)   # → unsatisfiable z3
```

`check_subsumption` decides whether one class's body entails another's — and when
it does not, it returns the countermodel rather than a bare "not proved":

```python
from unicode_fol_kit import chem
from unicode_fol_kit.eval import check_subsumption

definitions = {
    "Molecule":               chem.parse_chemlog_tptp("net_charge_neutral"),
    "OrganicMolecularEntity": chem.parse_chemlog_tptp("molecule & ?[A1]: c(A1)"),
    "Hydrocarbon":            chem.parse_chemlog_tptp(
        "organicMolecularEntity & ?[A1]: (c(A1) & ?[A2]: (h(A2) & bond(A1,A2)))"),
}
print(check_subsumption("Hydrocarbon", "OrganicMolecularEntity",
                        definitions).status)   # → entailed
back = check_subsumption("OrganicMolecularEntity", "Hydrocarbon", definitions)
print(back.status)                             # → refuted
print(back.explanation[:60])
# → Z3 found a model with 4 assignments. Under the assignm
```

The explanation is the point. A prover that answers only *proved* / *not proved*
leaves you unable to distinguish "the subclass really is broader" from "the prover
gave up", and those call for opposite reactions.

`check_theory` runs all three checks over the whole set in one call:

```python
from unicode_fol_kit import chem
from unicode_fol_kit.eval import check_theory

definitions = {
    "Molecule":               chem.parse_chemlog_tptp("net_charge_neutral"),
    "OrganicMolecularEntity": chem.parse_chemlog_tptp("molecule & ?[A1]: c(A1)"),
    "Hydrocarbon":            chem.parse_chemlog_tptp(
        "organicMolecularEntity & ?[A1]: (c(A1) & ?[A2]: (h(A2) & bond(A1,A2)))"),
}
report = check_theory(definitions,
                      subsumptions=[("Hydrocarbon", "OrganicMolecularEntity"),
                                    ("OrganicMolecularEntity", "Hydrocarbon")])
print(report.cycles)                                          # → ()
print(sorted((k, v.status) for k, v in report.satisfiability.items()))
# → [('Hydrocarbon', 'satisfiable'), ('Molecule', 'satisfiable'), ('OrganicMolecularEntity', 'satisfiable')]
print([(s.sub, s.sup, s.status) for s in report.subsumptions])
# → [('Hydrocarbon', 'OrganicMolecularEntity', 'entailed'), ('OrganicMolecularEntity', 'Hydrocarbon', 'refuted')]
```

## Is the definition too easily satisfied?

Satisfiable is a low bar. The interesting failure of a generated class definition
is the opposite one: it is satisfied by almost anything. `minimal_model_size`
measures that directly — the smallest structure in which the body holds.

```python
from unicode_fol_kit import chem
from unicode_fol_kit.eval import minimal_model_size

phi = chem.parse_chemlog_tptp("?[A1]: (c(A1) & ?[A2]: (o(A2) & bond(A1,A2)))")
m = minimal_model_size(phi)
print(m.size, m.exhausted)   # → 1 False
```

One individual. Nothing in the formula says that a carbon is not an oxygen, or
that an atom is not bonded to itself, so a single self-bonded individual that is
both satisfies "there is a carbon bonded to an oxygen". As a *description of a
chemical class* that is hopeless; as a *formula* it is exactly what was written.

`generality_report` wraps this into a verdict against an expectation, with the
witness spelled out:

```python
from unicode_fol_kit import chem
from unicode_fol_kit.eval import generality_report

phi = chem.parse_chemlog_tptp("?[A1]: (c(A1) & ?[A2]: (o(A2) & bond(A1,A2)))")
rep = generality_report("HydroxyCompound", phi, expected_min_size=20)
print(rep.verdict)                    # → underdetermined
print(rep.witness_description)
# → The domain has 1 individual: 0. The predicate bond/2 holds for: (0, 0).
#   The predicate c/1 holds for: (0). The predicate o/1 holds for: (0).
```

The verdict is `underdetermined`, not `wrong`: a small minimal model is an
*indication*, since the missing constraints (disjoint element predicates,
irreflexive bonds) are background knowledge the formula never stated. What the
report gives you is the concrete structure to look at.

The related question — does the subclass definition add anything at all over its
superclass? — is `is_vacuous_specialisation`:

```python
from unicode_fol_kit import chem
from unicode_fol_kit.eval import is_vacuous_specialisation

sup   = chem.parse_chemlog_tptp("?[A1]: c(A1)")
vac   = chem.parse_chemlog_tptp("?[A1]: (c(A1) & ?[A2]: (c(A2) & c(A2)))")
real  = chem.parse_chemlog_tptp("?[A1]: (c(A1) & ?[A2]: (o(A2) & bond(A1,A2)))")
unrel = chem.parse_chemlog_tptp("?[A1]: o(A1)")

for label, body in (("vacuous", vac), ("real", real), ("unrelated", unrel)):
    print(label, is_vacuous_specialisation(body, sup).classification)
# → vacuous equivalent
#   real strictly_stronger
#   unrelated not_a_specialisation
```

`equivalent` is the alarm: the subclass has piled on conjuncts that its
superclass already entails, so it will match exactly the same things while
appearing more specific. Anything the provers cannot settle comes back
`undecided` rather than being folded into one of the three verdicts.

## Where to go next

- {doc}`batch-checking` — running a whole definition set against a molecule
  corpus once the definitions themselves have been audited.
- {doc}`model-checking` — the other half: evaluating a definition against a
  structure you already have.
- {doc}`classical-reasoning` — the prover chain and finite model finder these
  checks are built on.
