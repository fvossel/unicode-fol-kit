# Interoperability: reading and writing other people's logic

The kit is rarely the only tool in a pipeline. Formulas arrive from a prover, a
rule learner, an ontology dump or a language model, and they have to leave again
for whatever comes next. This page covers the import/export family — including
the three subsystems that had no page until now: **Prolog/Datalog**, **CASL**
and **HETS**.

One rule governs all of them, and it is worth stating before the details:

> **An importer inverts naming, and refuses what it cannot read.** Where a
> source language's conventions differ from the kit's, the importer converts
> them exactly; where a construct has no first-order reading, it says so by
> name instead of dropping it.

## What can be read

| Source | Entry point | Notes |
|---|---|---|
| TPTP (FOF/CNF) | {func}`~unicode_fol_kit.parse_tptp_formula`, {func}`~unicode_fol_kit.parse_tptp`, {func}`~unicode_fol_kit.load_tptp` | single-quoted atoms supported; `parse_tptp_problem` also keeps SZS header metadata |
| Prover9 / LADR | {func}`~unicode_fol_kit.parse_prover9`, {func}`~unicode_fol_kit.load_prover9` | statement scanner, not a lenient grammar — a missing `end_of_list` is an error, not a silent degradation |
| SMT-LIB 2 | {func}`~unicode_fol_kit.parse_smtlib`, {func}`~unicode_fol_kit.load_smtlib` | several assertions fold into their conjunction |
| Z3 expressions | {func}`~unicode_fol_kit.from_z3` | in memory, no text round trip |
| LaTeX | {func}`~unicode_fol_kit.parse_latex` | |
| CASL | {func}`~unicode_fol_kit.parse_casl_spec` | sorted; see below |
| **Prolog / Datalog** | {func}`~unicode_fol_kit.parse_prolog_clause`, {func}`~unicode_fol_kit.parse_prolog_program`, {func}`~unicode_fol_kit.load_prolog` | **new**; see below |

{func}`~unicode_fol_kit.api.parse_any` detects the dialect for you, and
{func}`~unicode_fol_kit.detect_dialects` shows what it is considering:

```python
from unicode_fol_kit import detect_dialects

print(detect_dialects("fof(a, axiom, p(X))."))
# → ('tptp', 'unicode')
print(detect_dialects("all x (P(x) -> Q(x))."))
# → ('prover9', 'unicode')
```

Prolog is deliberately **not** in that ladder. `p(a).` is a legal fragment of
several of these dialects at once, and a wrong guess would be silent — ask for
the Prolog reader by name.

## Prolog and Datalog

The immediate use is reading back what a rule learner produced. An ILP system
(Popper, Aleph, Metagol) emits Prolog clauses; parsing them turns an induced
rule into something you can model-check, prove with, export to TPTP or compare
against a reference — rather than eyeball.

### The two readings

A definite clause says two different things, and the kit will not choose for
you:

```python
from unicode_fol_kit import parse_prolog_clause

clause = "amide(A) :- carbon(C), nitrogen(N), bond(C, N), in(A, C)."

print(parse_prolog_clause(clause).to_unicode_str())
# → ∀a ∀c ∀n (Carbon(c) ∧ Nitrogen(n) ∧ Bond(c, n) ∧ In(a, c) → Amide(a))

print(parse_prolog_clause(clause, mode="body").to_unicode_str())
# → ∃c ∃n (Carbon(c) ∧ Nitrogen(n) ∧ Bond(c, n) ∧ In(a, c))
```

`mode="clause"` (the default) is the standard logical reading: every variable
universally quantified over the implication. `mode="body"` is the **condition
alone** — body-only variables existentially closed, the head's variables left
free. That second form is what a *class definition* is: the property a thing
must have, ready to check against one structure. They are different formulas.

Note the naming inversion in both: Prolog spells a predicate lower-case and a
variable upper-case; the kit does the opposite, so `carbon(A)` arrives as
`Carbon(a)`. Only the **first** character is folded, so a mixed-case atom such
as `bSINGLE` survives as `BSINGLE` rather than collapsing to `Bsingle`.

### Negation as failure is not negation

`\+ G` succeeds when Prolog fails to prove `G`. That coincides with `¬G` only
under the closed world assumption on a stratified program, so reading it
silently would turn "not derivable here" into "false everywhere":

```python
from unicode_fol_kit import parse_prolog_clause
from unicode_fol_kit.fol.prolog_input import PrologParsingError

try:
    parse_prolog_clause("p(A) :- q(A), \\+ r(A).", mode="body")
except PrologParsingError as exc:
    print("refused:", "closed world assumption" in str(exc))
# → refused: True

opted_in = parse_prolog_clause("p(A) :- q(A), \\+ r(A).", mode="body",
                               negation_as_failure="classical")
print(opted_in.to_unicode_str())
# → Q(a) ∧ ¬R(a)
```

Passing `negation_as_failure="classical"` is you asserting that the assumption
holds for your program.

### What it refuses, and why

The cut, if-then, `is`, `=..` and list terms are refused **by name**:

```python
from unicode_fol_kit import parse_prolog_clause
from unicode_fol_kit.fol.prolog_input import PrologParsingError

for text in ("p(A) :- q(A), !.", "p(A) :- q(A) -> r(A).", "p(A) :- foo is 1."):
    try:
        parse_prolog_clause(text, mode="body")
    except PrologParsingError as exc:
        print(str(exc).split(": ", 2)[-1][:52])
# → the cut (!) — a control construct with no truth-cond
# → if-then (->) — Prolog's is a committed choice, not m
# → arithmetic evaluation (is) — a computation, not a re
```

A parser that quietly dropped a cut would change what the program means, and
the reader would go looking for a typo instead.

### Whole programs

```python
from unicode_fol_kit import parse_prolog_program

program = """
% a comment with a period.
val(1.5).
p(A) :- q(A).
p(A) :- r(A).
"""
clauses = parse_prolog_program(program)
print(len(clauses))
# → 3
```

Splitting happens on a clause-ending period only — not on a decimal point, not
inside a quoted atom. Two clauses sharing a head **are** alternatives, but only
under the completion of the program, which is an assumption about the whole
program rather than a fact about those two clauses. They come back separately
and are not disjoined for you.

## CASL

CASL is the Common Algebraic Specification Language — the sorted specification
format HETS speaks. Export produces a whole spec, sorts and predicate
declarations included:

```python
from unicode_fol_kit import MSFLParser, to_casl_spec

phi = MSFLParser().parse("∀x (Human(x) → Mortal(x))")
print(to_casl_spec([phi], spec_name="Ontology"))
```

```text
spec Ontology =
  sorts Thing
  preds Human : Thing;
        Mortal : Thing
  . forall x : Thing . (Human(x) => Mortal(x))
end
```

And it reads back:

```python
from unicode_fol_kit import MSFLParser, to_casl_spec, parse_casl_spec

phi = MSFLParser().parse("∀x (Human(x) → Mortal(x))")
spec = parse_casl_spec(to_casl_spec([phi], spec_name="Ontology"))
print([axiom.to_unicode_str() for axiom in spec.axioms])
# → ['∀x (Human(x) → Mortal(x))']
```

Unsorted formulas are exported over a single `default_sort` (`Thing` unless you
say otherwise); a genuinely sorted MSFOL formula keeps its sorts.

## HETS

[HETS](http://hets.eu/) is the Heterogeneous Tool Set: a broker that speaks many
specification languages, knows the translations (*comorphisms*) between them,
and drives a fleet of provers behind one interface. The kit binds to its REST
API, which means a formula written here can be proved by a prover the kit has no
backend for.

Everything below needs a running HETS — the kit can start the official Docker
image for you — so the examples are not executed in the docs.

### Finding or starting a server

```python
# doctest: +SKIP  — needs Docker
from unicode_fol_kit.hets import hets_available, discover_hets_url

print(hets_available())                       # already running on :8000?
url, container = discover_hets_url(start_container=True)
print(url)                                    # → http://localhost:8000
```

`discover_hets_url` returns the container handle alongside the URL so you can
stop what you started. Without `start_container=True` it only looks.

### Asking it something

```python
# doctest: +SKIP  — needs Docker
from unicode_fol_kit import MSFLParser, to_casl_spec
from unicode_fol_kit.hets import HetsClient

client = HetsClient("http://localhost:8000")
print(client.version())
print(client.provers())                       # what HETS can reach right now

phi = MSFLParser().parse("∀x (Human(x) → Mortal(x))")
handle = client.upload(to_casl_spec([phi], spec_name="Ontology"))
print(client.theory(handle))
print(client.consistency_check(handle))
```

`HetsClient` exposes `version`, `provers`, `translations`, `upload`, `theory`,
`dg` (the development graph), `prove` and `consistency_check`.

### As a backend, and as translations

Two integrations sit on top of the client. `HetsBackend` implements the kit's
own {class}`~unicode_fol_kit.ProverBackend` protocol, so HETS joins the prover
chain like any other backend. And
{func}`~unicode_fol_kit.hets.register_hets_comorphisms` asks the running server
which translations it knows and registers each as a `hets:<Name>` edge in the
kit's comorphism registry — so `translate` can follow a path the kit does not
implement itself:

```python
# doctest: +SKIP  — needs Docker
from unicode_fol_kit.hets import register_hets_comorphisms

edges = register_hets_comorphisms()
print(len(edges), edges[:3])
```

The edges are **discovered, not hardcoded**: what you get depends on the HETS
build you are talking to.

## Round trip: an induced rule, checked

Putting the pieces together — this is the loop that motivated the Prolog reader.
A learner returns a clause; the kit turns it into a formula and evaluates it
against real structures, with no hand-written translation in between:

```python
from unicode_fol_kit import parse_prolog_clause

learned = "amide(A) :- bSINGLE(C, D), bDOUBLE(D, B), n(C), atom_in(A, B)."
body = parse_prolog_clause(learned, mode="body")
print(body.to_unicode_str())
# → ∃b ∃c ∃d (BSINGLE(c, d) ∧ BDOUBLE(d, b) ∧ N(c) ∧ Atom_in(a, b))
```

`atom_in/2` is the learner's membership predicate — it anchors the clause to its
example and says nothing about the structure being checked, so it is dropped
before evaluation. What remains is a chemical pattern, and
{doc}`model-checking` shows how to run it against molecules.

Two encoding traps are worth knowing if you are producing the learner's input
rather than consuming its output, because both produce a hypothesis that scores
perfectly and means nothing:

- **Example-local individual names.** If every example names its individuals
  `c1`, `n1`, …, the same constant denotes a different thing in each example and
  a learner will happily join across them. Make the names globally unique.
- **The example argument on every predicate.** If each predicate carries the
  example (`c(M, X)`, `bond(M, X, Y)`), the learner can introduce a *second*
  example variable and connect through it — and the resulting clause is no
  longer a statement about one structure. Put the example on exactly one
  membership predicate and leave it off the rest.
