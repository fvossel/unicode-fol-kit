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
| **ACE (controlled English)** | {func}`~unicode_fol_kit.ace.ace_to_fol` | **new**; needs the external APE binary; see below |

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

## Attempto Controlled English

[ACE](https://github.com/Attempto/APE) is a controlled natural language with
exactly one reading per sentence — fixed by documented convention, not by a
guesser — which makes English-shaped text a real input format rather than an
NLP gamble. The kit drives the reference parser APE as an external subprocess
(LGPL; install: `git clone https://github.com/Attempto/APE ~/APE && cd ~/APE
&& make install`, needs SWI-Prolog — on Windows a WSL build is found
automatically, and `$UFK_APE_CMD` overrides discovery):

```python
from unicode_fol_kit.ace import ace_to_fol

for f in ace_to_fol("Every farmer who owns a donkey beats it."):
    print(f.to_unicode_str())
# → ∀a ∀b ∀c (Farmer(a) ∧ (Donkey(b) ∧ Predicate2(c, own, a, b)) → ∃d Predicate2(d, beat, a, b))
```

The donkey sentence arrives with the correct universal reading of its
indefinite, events are explicit (neo-Davidsonian: `Predicate1/2/3` carry the
event referent first), and cross-sentence anaphora ("A man waits. He sleeps.")
resolves before translation.

Three outcomes, none silent — this route refuses rather than mistranslates:

- **not ACE** → `AceParseError` with APE's own diagnosis, down to a repair
  hint (`"waitz"` → `"wait"`). APE's built-in lexicon is deliberately small;
  the `ulex` parameter supplies missing words:
  `ace_to_fol("A man whistles.", ulex="iv_finsg(whistles, whistle).")`.
- **ACE, but beyond Attempto's own TPTP export** → `AceTptpUnsupportedError`
  carrying the DRS: the four modal boxes (`must`/`can`/`should`/`may`),
  negation as failure, questions and commands. A yes/no question is refused
  for a subtler reason: APE renders it as a TPTP *conjecture*, and flattening
  that role would silently turn "Does John wait?" into the claim that he
  does. Routing all of these into the kit's modal family is milestone ACE-3.
- **ACE, but the counting is inert** → *on this route* the formula comes back
  with a reified `Object(b, man, countable, na, geq, 3)` atom instead of
  counting force — that is Attempto's own TPTP export, kept verbatim;
  {func}`~unicode_fol_kit.ace.ace_coverage` flags such sentences
  (`reified_cardinality`). The DRS and formula routes below DO carry the
  counting force since ACE-4/5.

{func}`~unicode_fol_kit.ace.ace_coverage` runs any sentence list through the
route and reports each sentence's fate (`ok` / `tptp_unsupported` /
`tptp_unread` / `not_ace` / `infra`) — the kit's own 55-sentence corpus and
its recorded per-sentence outcomes live in `tests/fixtures/ace_corpus_v1.tsv`
and `tests/fixtures/ape_5f4d535_corpus_v1.json`.

### The DRS route: `ace_to_drs`

APE's own representation is a Discourse Representation Structure, and the kit
has a DRS core — so since 0.24.0 the DRS itself is first-class.
{func}`~unicode_fol_kit.ace.parse_ape_drs` reads APE's printed term 1:1
(pinned by a byte-identical round-trip over the whole corpus), and
{func}`~unicode_fol_kit.ace.ace_to_drs` maps it onto {mod}`unicode_fol_kit.drt`:

```python
from unicode_fol_kit.ace import ace_to_drs
from unicode_fol_kit.drt import drs_to_fol

drs = ace_to_drs("Every farmer who owns a donkey beats it.")
print(drs_to_fol(drs).to_unicode_str())
# → ∀x1 ∀x2 ∀e1 (Farmer(x1) ∧ Donkey(x2) ∧ Own(e1, x1, x2) → ∃e2 Beat(e2, x1, x2))
```

Verbs, nouns, adjectives and prepositions become kit predicates (`See(e1,
x1, x2)` — events stay, neo-Davidsonian), the copula becomes equality with
the be-event dropped (Attempto's own reference reading), proper names become
constants. A sentence maps **completely or not at all**:
{func}`~unicode_fol_kit.ace.map_ace_drs` returns a per-condition report
(`DrsMapping.rows`) naming every condition's verdict, and
{func}`~unicode_fol_kit.ace.condition_statistics` aggregates those verdicts
over a corpus — on the kit's own corpus, 38 of 50 ACE sentences map
completely, and every refusal names its reason and, where one exists, its
carrier (modality, questions, the `exactly`/`at most` maximality and
arithmetic → `ace_to_formula`; commands and negation as failure → honestly
undecided).

The mapping is pinned by a differential: for every corpus sentence both
routes cover, `drs_to_fol` over the mapped DRS is Z3-equivalent to APE's own
TPTP output read by the kit — two independent implementations of the
standard translation, agreeing formula by formula.

### The formula route: `ace_to_formula`

What a classical DRS cannot hold, a kit formula can.
{func}`~unicode_fol_kit.ace.ace_to_formula` translates straight to one
formula, routing ACE's four modal boxes onto the kit's modal family —
`must` → `□`, `can` → `◇` (alethic), `should` → `Ⓞ`, `may` → `Ⓟ` (deontic, a
documented choice matching Attempto's recommendation/admissibility gloss):

```python
from unicode_fol_kit.ace import ace_to_formula

print(ace_to_formula("Every man must wait.").formula.to_unicode_str())
# → ∀x1 (Man(x1) → □∃e1 Wait(e1, x1))
```

The result re-parses identically through the kit's own modal parser and is a
first-class citizen of the modal backends (`qml_is_valid`, tableaux,
Isabelle). Questions keep their interrogative force instead of losing it:
a wh-question yields an OPEN formula (`kind="wh_question"`, the queried
variable named in `query_variables` — answering is model finding), a yes/no
question a closed one (`kind="yesno_question"` — answering is an entailment
check). Commands and negation as failure still refuse, with the same
reasons on every route.

### Plurals, counting, arithmetic (ACE-4/5)

ACE reads an unmarked plural **collectively**: "At least 3 men wait."
asserts one waiting *group* of at least three men, not three individual
waits. The kit keeps that reading — the DRS core carries two plural-DRT
conditions, `Card` (a group's cardinality bound) and `Part` (membership,
exported as the binary `Part_of`), and `Card` lowers to the kit's counting
quantifier on export:

```python
from unicode_fol_kit.ace import ace_to_drs
from unicode_fol_kit.drt import drs_to_fol

drs = ace_to_drs("At least 3 men wait.")
print(drs.to_box_notation())
# → [g1, e1 | Card(g1, >=, 3), [x1 | Part_of(x1, g1)] -> [ | Man(x1)], Wait(e1, g1)]
print(drs_to_fol(drs).to_unicode_str())
# → ∃g1 ∃e1 (∃≥3 p1 Part_of(p1, g1) ∧ ∀x1 (Part_of(x1, g1) → Man(x1)) ∧ Wait(e1, g1))
```

The strict operators shift exactly ("more than 2" and "at least 3" produce
Z3-equivalent formulas), coordinations become closed groups ("John and
Mary" → two `Part_of` atoms plus `Card(g, =, 2)`), and "each of"
distributes through an ordinary duplex — no extra operator needed, and
Z3 draws the distributed consequences.

Two counting constructs live on the **formula route only**. The maximality
of `exactly`/`at most` (APE's `[...]` list condition) becomes a counting
quantifier over the whole scope — the *distributive* counting reading
("Exactly 2 dogs bark." → `∃=2 g1 ∃e1 (Dog(g1) ∧ Bark(e1, g1))`: exactly
two individual barkers; collective maximality is not first-order
expressible, a documented choice at `translate.box_with_lists`). And
arithmetic translates to kit terms — `"1 + 2 = 3."` → `1 + 2 = 3` — where
the default backend deliberately reads `+` uninterpreted;
{func}`~unicode_fol_kit.atp.z3_arith.is_valid_arith` decides the
arithmetic fragment (proves `1 + 2 = 3`, refutes `1 + 2 = 4`).

### The reverse direction: `drs_to_ace` (ACE-6)

The pipeline also runs backwards. {func}`~unicode_fol_kit.ace.drs_to_ace`
verbalizes a kit DRS as ACE text plus the APE user-lexicon entries that
carry its content words, and {func}`~unicode_fol_kit.ace.ace_round_trip`
is the machine self-check: the text goes back through APE and the mapping,
and Z3 judges the result against the input — over the kit's corpus, every
mappable sentence closes that loop.

```python
from unicode_fol_kit.ace import drs_to_ace, ace_round_trip
from unicode_fol_kit.drt import parse_drs

drs = parse_drs("[ | [x1 | Farmer(x1)] -> [e1 | Wait(e1, x1)]]")
print(drs_to_ace(drs).text)
# → If there is a farmer X1 then X1 waits.
print(ace_round_trip(drs).equivalent)   # needs a live APE
# → True
```

The claim is deliberately NOT "natural English" — it is that the text
*means* the DRS, machine-checked. Surface forms are mechanical and
lexicon-defined: the third-person singular and the plural add
`s`/`es`/`ies`, underscores become hyphens (`Bond_to` → the verb
`bond-to`), and "at least 3 mans" is intentional — the emitted
`noun_pl(mans, man, neutr)` entry defines that surface, APE parses it, and
the logical symbol underneath is exactly `man`. Everything the probed ACE
fragment cannot carry back refuses by name
({class}`~unicode_fol_kit.ace.AceVerbalizationError`): upper-bound
cardinalities (`Card(g, <=, n)` — APE reads "at most" as the maximality
list), values outside equalities, binary predicates over individuals
(an ACE verb always carries an event), non-invertible names.

Since 0.25.0 the reverse direction also takes FORMULAS.
{func}`~unicode_fol_kit.drt.fol_to_drs` runs the standard translation
backwards — it recognizes exactly the shape `drs_to_fol` emits and
rebuilds the box structure, refusing everything outside that image by
name ({class}`~unicode_fol_kit.drt.FolToDrsError`: modality,
biconditionals, bare universals, formula-level counting, function terms,
free variables). {func}`~unicode_fol_kit.ace.formula_to_ace` chains the
two: "is this formula expressible as ACE?" becomes two refusal-checked
steps, and a positive answer is a sentence:

```python
from unicode_fol_kit import MSFLParser
from unicode_fol_kit.ace import formula_to_ace

donkey = MSFLParser().parse(
    "∀x1 ∀x2 ∀e1 (Farmer(x1) ∧ Donkey(x2) ∧ Own(e1, x1, x2)"
    " → ∃e2 Beat(e2, x1, x2))")
print(formula_to_ace(donkey).text)
# → If a farmer X1 owns a donkey X2 then X1 beats X2.
```

{func}`~unicode_fol_kit.ace.chem_ulex` renders the ChemLog signature
(`unicode_fol_kit.chem`) as such a user lexicon, so ACE can talk about
molecules — "There is a carbon X1. X1 bonds an oxygen X2. X1 is
aromatic." parses with the DRS carrying `c`, `bond`, `aromatic`. Two
shape facts are documented rather than hidden: kit-side the symbols
arrive capitalized ({func}`~unicode_fol_kit.ace.ace_kit_name` computes
the spelling), and ACE verbs are neo-Davidsonian, so binary ChemLog
relations arrive with an event argument (`Bond(e1, x1, x2)`); the three
nullary net-charge predicates are unspeakable in ACE (a sentence needs a
subject) and excluded by name.

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

## Inductive logic programming: the other direction

Reading a learner's answer is half the loop. {mod}`unicode_fol_kit.ilp` writes
the learner's *question* — the background knowledge, examples and language bias
an ILP system (Popper, Aleph, Metagol) reads — from the very same
{class}`~unicode_fol_kit.semantics.structures.FiniteStructure` objects the model
checker evaluates against:

```text
structure ──IlpTask──▶ Prolog task ──learner──▶ clause
    ──clause_to_formula──▶ kit formula ──model checker──▶ verdicts
```

Nothing runs a learner: Popper needs SWI-Prolog and, from v4, `janus_swi`, which
is not a dependency the kit takes on for a file format. It writes `bk.pl`,
`exs.pl` and `bias.pl`, and reads the text a learner prints.

```python
from unicode_fol_kit.semantics import FiniteStructure
from unicode_fol_kit.ilp import IlpTask, Example

amide = FiniteStructure(
    domain=("c1", "o1", "n1"),
    extensions={("c", 1): [("c1",)], ("o", 1): [("o1",)], ("n", 1): [("n1",)],
                ("bDOUBLE", 2): [("c1", "o1"), ("o1", "c1")],
                ("bSINGLE", 2): [("c1", "n1"), ("n1", "c1")]})
acid = FiniteStructure(
    domain=("c1", "o1", "o2"),
    extensions={("c", 1): [("c1",)], ("o", 1): [("o1",), ("o2",)], ("n", 1): [],
                ("bDOUBLE", 2): [("c1", "o1"), ("o1", "c1")],
                ("bSINGLE", 2): [("c1", "o2"), ("o2", "c1")]})

task = IlpTask("amide", [Example("m1", amide, True),
                         Example("m2", acid, False)])
print(task.counts)
# → {'positive': 1, 'negative': 1, 'predicates': 5, 'facts': 20}
print(task.examples_text(), end="")
# → pos(amide(m1)).
# → neg(amide(m2)).
```

`task.write(directory)` puts the three files there. The facts are the extension
exactly — one Prolog fact per tuple, no orientation guessed — so a symmetric
relation comes out symmetric because it was stored that way, and an asymmetric
one keeps the single direction it has.

### Why this is a module and not a script

Because two encoding mistakes are easy to make, invisible in the output, and
both produce a hypothesis that scores **precision 1.00 and means nothing**. Both
were made while building this kit's own pre-trial. They are now refused rather
than written down as advice:

- **Example-local individual names.** Every molecule has a `c1`. Emitted raw,
  one constant denotes a different atom in each example and the learner joins
  *across* examples through it — the first run of that pre-trial returned a
  clause that scored perfectly by hopping between molecules. `IlpTask` prefixes
  every individual with its example and refuses the task if two constants would
  still collide, examples and individuals sharing one namespace.
- **The example argument on every predicate.** Carry it everywhere (`c(M, X)`,
  `bond(M, X, Y)`) and the learner introduces a *second* example variable and
  connects through it. Here the example argument exists on the membership
  predicate alone — the emitter has no way to put it anywhere else.

A third guard falls out of the same reasoning: a **0-ary** predicate cannot be
attached to one example, so it would hold globally. It is excluded from an
inferred vocabulary (visibly, and noted in the emitted file) and refused if
named explicitly.

### Reading the clause back

```python
from unicode_fol_kit.ilp import clause_to_formula

learned = "amide(A) :- bSINGLE(C, D), bDOUBLE(D, B), n(C), atom_in(A, B)."
print(clause_to_formula(learned).to_unicode_str())
# → ∃b ∃c ∃d (BSINGLE(c, d) ∧ BDOUBLE(d, b) ∧ N(c))
```

The membership atom is gone: it anchored the clause to its example and says
nothing about the structure being checked. `IlpTask.read_clause` does the same
with the task's own vocabulary, so the predicate names come back **exactly as
they were emitted** rather than in the importer's capitalised spelling — which
is what makes the result checkable against the structures it came from.

The way back is where the encoding is checked a second time. Three shapes are
refused instead of translated, each because no formula about a single structure
means the same thing:

```python
from unicode_fol_kit.ilp import clause_to_formula, IlpEncodingError

for clause, why in [
    ("amide(A) :- n(C), atom_in(B, C).",          "names a second example"),
    ("amide(A) :- n(A), atom_in(A, B).",          "example variable survives"),
    ("amide(A) :- n(C), atom_in(A, B), o(B).",    "goal not linked to the example"),
]:
    try:
        clause_to_formula(clause)
    except IlpEncodingError:
        print("refused:", why)
# → refused: names a second example
# → refused: example variable survives
# → refused: goal not linked to the example
```

The third is the subtle one. In `amide(A) :- n(C), atom_in(A, B), o(B).` nothing
connects `C` to `B`, so in Prolog `n(C)` ranges over the **whole fact base**: it
succeeds if *any* example has a nitrogen, which makes the clause true of every
example at once. Reading it as `∃c N(c)` over one structure would turn that
global claim into a local one, and a clause that covers a negative example would
come back scoring perfectly — the very outcome the module exists to prevent.
Linkage propagates through positive goals only, because `\+` binds nothing in
SLDNF.

### Is the task even sound?

Ask before you learn, not after. If the reference definition you already believe
in does not separate the two example sets under the kit's own model checker,
the task is broken and no answer from any learner would have meant anything:

```python
from unicode_fol_kit.semantics import FiniteStructure
from unicode_fol_kit.ilp import Example, IlpTask, check_separation

amide = FiniteStructure(
    domain=("c1", "o1", "n1"),
    extensions={("c", 1): [("c1",)], ("o", 1): [("o1",)], ("n", 1): [("n1",)],
                ("bDOUBLE", 2): [("c1", "o1"), ("o1", "c1")],
                ("bSINGLE", 2): [("c1", "n1"), ("n1", "c1")]})
acid = FiniteStructure(
    domain=("c1", "o1", "o2"),
    extensions={("c", 1): [("c1",)], ("o", 1): [("o1",), ("o2",)], ("n", 1): [],
                ("bDOUBLE", 2): [("c1", "o1"), ("o1", "c1")],
                ("bSINGLE", 2): [("c1", "o2"), ("o2", "c1")]})
task = IlpTask("amide", [Example("m1", amide, True),
                         Example("m2", acid, False)])

reference = task.read_clause(
    "amide(A) :- c(C), o(O), n(N), bDOUBLE(C,O), bSINGLE(C,N), atom_in(A,C).")
report = check_separation(reference, task)
print(report.separates, report.counts["true_positive"],
      report.counts["true_negative"])
# → True 1 1
```

And after: a learner returns the *smallest* hypothesis consistent with its
examples, so every property the negatives did not force it to name is a hole.
Run the learned clause over held-out structures and the holes show up as false
positives — `report.misclassified` names them, while `exhausted` and
`eval_error` rows stay separate from "decided the wrong way", because those call
for different fixes.
