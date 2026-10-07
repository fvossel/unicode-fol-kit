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
| TPTP (FOF/CNF) | {func}`~unicode_logic_kit.parse_tptp_formula`, {func}`~unicode_logic_kit.parse_tptp`, {func}`~unicode_logic_kit.load_tptp` | single-quoted atoms supported; `parse_tptp_problem` also keeps SZS header metadata; `load_tptp`/`load_tptp_problem`/`load_tff_problem` resolve `include(...)` directives — see below |
| **TPTP TF0 (typed)** | {func}`~unicode_logic_kit.fol.tptp_input.parse_tff_problem` | **new**; many-sorted `tff` — see below |
| Prover9 / LADR | {func}`~unicode_logic_kit.parse_prover9`, {func}`~unicode_logic_kit.load_prover9` | statement scanner, not a lenient grammar — a missing `end_of_list` is an error, not a silent degradation; a genuinely new `op(...)` operator declaration is applied to later formulas; a name that no quantifier binds is read by the file's own `set(prolog_style_variables)` (or Prover9's default); a double-quoted symbol is a name that is never a variable, and a free variable stays free — see below |
| SMT-LIB 2 | {func}`~unicode_logic_kit.parse_smtlib`, {func}`~unicode_logic_kit.load_smtlib` | one `Node` per assertion (`parse_any` folds several into their conjunction); **writing** is new — see below |
| Z3 expressions | {func}`~unicode_logic_kit.from_z3` | in memory, no text round trip; a free `Variable` that `to_z3` wrote (the symbol `x!v`) reads back as that `Variable` |
| LaTeX | {func}`~unicode_logic_kit.parse_latex` | |
| CASL | {func}`~unicode_logic_kit.parse_casl_spec` | sorted; see below |
| **Prolog / Datalog** | {func}`~unicode_logic_kit.parse_prolog_clause`, {func}`~unicode_logic_kit.parse_prolog_program`, {func}`~unicode_logic_kit.load_prolog` | **new**; see below |
| **ACE (controlled English)** | {func}`~unicode_logic_kit.ace.ace_to_fol` | **new**; needs the external APE binary; see below |

{func}`~unicode_logic_kit.api.parse_any` detects the dialect for you, and
{func}`~unicode_logic_kit.detect_dialects` shows what it is considering:

```python
from unicode_logic_kit import detect_dialects

print(detect_dialects("fof(a, axiom, p(X))."))
# → ('tptp', 'unicode')
print(detect_dialects("all x (P(x) -> Q(x))."))
# → ('prover9', 'unicode')
```

Prolog is deliberately **not** in that ladder. `p(a).` is a legal fragment of
several of these dialects at once, and a wrong guess would be silent — ask for
the Prolog reader by name.

## Prover9: applying `op(...)` operator declarations

Prover9's `op(precedence, type, symbol)` directive declares a new operator —
Prover9's own manual documents the default table and the eight type keywords
(`infix`, `infix_left`, `infix_right`, `prefix`, `prefix_paren`, `postfix`,
`postfix_paren`, `ordinary`; the Prolog reader's `xfx`/`yfx`/`xfy`/`fy`/`fx`
under different names). {func}`~unicode_logic_kit.parse_prover9_problem` /
{func}`~unicode_logic_kit.load_prover9` apply a genuinely *new* declaration to
every formula parsed after it in the same file:

```python
from unicode_logic_kit import parse_prover9_problem

text = """
op(650, infix, before).
formulas(sos).
  all X all Y (X before Y -> -(Y before X)).
  a before b.
end_of_list.
formulas(goals).
  -(b before a).
end_of_list.
"""
for rec in parse_prover9_problem(text):
    print(rec.role, "|", rec.formula.to_unicode_str())
# sos   | ∀x ∀y (before(x, y) → ¬before(y, x))
# sos   | before('a', 'b')
# goals | ¬before('b', 'a')
```

`before` becomes a new predicate-like (`Atom`-producing) infix operator
because 650 sits between Prover9's arithmetic tier (500) and its comparison
tier (700); a declaration below 500 instead becomes a `Function`-producing
term operator. Two things are refused — by name, as a
`unicode_logic_kit.fol.prover9_input.Prover9ParsingError` — regardless of
whether the operator is ever used: **redeclaring an existing built-in**
(`op(500, infix, "+")`, say) and **redeclaring a symbol the same file already
declared**; a malformed directive (wrong arity, a non-integer precedence, an
unknown type keyword, an unsupported symbol) is refused the same way. A
precedence this reader has no splice point for (it ties a built-in tier, or
sits at/above the quantifier tier) is accepted but left inert — recorded
against future redeclaration, but never applied, so a formula that tries to
use it as an operator still fails to parse, just at that later point rather
than at the declaration.

A quantifier binds the symbol it names, whatever its case (`all x P(x)` and
`all X P(X)` are one formula). A name that no quantifier binds is a variable or a
constant by the convention of the file, and the reader takes the convention from
the file as Prover9 does: the last `set(prolog_style_variables)` or
`clear(prolog_style_variables)` in it decides for every formula of it. Under the
flag a name that starts with an upper-case letter is a variable (an underscore
makes none: Prover9 reads `_x` as a constant), without it a name that starts with
`u` to `z` is, and every other name is a constant.
{func}`~unicode_logic_kit.parse_prover9`, which has no file around its formula,
reads under the flag unless it is given `prolog_style_variables=False`. The
example above reads alike under either convention, because the capitals in it are
bound.

Every file the kit writes sets `prolog_style_variables`. `Node.to_prover9` writes a
name that starts with an upper-case letter or an underscore, where it means a
constant or a proposition, in double quotes (an underscore-initial name is quoted
too: Prover9 reads it as a constant, but a Prolog reader takes it for a
variable), and the reader reads a
double-quoted symbol as a name that is never a variable: `"Rain"` is the proposition `Rain`, `P("Gaseous")` has the
constant `Gaseous`, and `"Foo"(a)` is the atom `Foo` (in term position, the
function `Foo`). Only a quoted name made of ASCII letters, digits and underscores,
not starting with a digit, is read (a quoted numeral is read as a number, below);
any other quoted text is refused by name. `Node.to_prover9` also quotes `all`
and `exists` and the three symbols that Prover9 itself reads as syntax at one
arity (`if` with three arguments, `end_of_list` with none, `formulas` with one),
and the reader reads them back. Prover9 keeps `"rain"` and `rain` apart as two symbols, while this
reader has one name for both, so a file that writes one symbol (the same kind,
name and arity) both quoted and bare is refused with a `Prover9ParsingError`,
wherever in the file the two spellings stand. The file scanner does not end a
statement at a `.` inside a quoted symbol or start a comment at a `%`, and an
unclosed quote is an error.

A quoted numeral in term position (`P("2.5")`) reads as the `Number` of that
value, in its canonical spelling only: `"2.50"` and `"1.0"` are refused, because
Prover9 keeps them apart from `"2.5"` and `"1"`, which are the same numbers. For
the same reason a file that spells one numeral value two ways (`01` and `1`,
`1.0` and `1`, quoted or bare) is refused, while a numeral that stands alone is
read as the number it spells (`P(01)` is `P(1)`). A decimal is read exactly or
refused: a whole value is the integer, and a fraction is the float it spells when
it has at most 15 significant digits (`P(3.14159265358979)` is read); beyond that
it is refused by name (`P(0.30000000000000004)`), because two different decimals
of 16 or 17 digits can be one float. `-(a, b)` is the function `-` of
two arguments, which is how a binary minus is written for Prover9; a prefix minus
in a term (`-(a)`, `-a`) is the function `-` of one argument, and a minus in front
of a formula that is not a comparison, or of a parenthesised formula, is a
negation (`-P(a)`, `-(a = b)`). A bare `-1` is still read as `Number(-1)`, also in
front of a comparison.

A free variable stays free. Prover9 closes each formula of a file universally
(`P(X)` there says `∀X P(X)`, under the flag; without it `P(x)` does); the reader
does not, and the kit's provers read a free variable as one unknown element, the
same in every formula of the problem. A file with free variables can therefore
mean something else on the two sides: the premise `P(X)` with the goal `P(a)`,
under the flag, is a theorem for Prover9 and is not valid for the kit, since the
element `X` may differ from `a`. Wrap the formulas in `∀` first when the closure
is what is meant.

## Prolog and Datalog

The immediate use is reading back what a rule learner produced. An ILP system
(Popper, Aleph, Metagol) emits Prolog clauses; parsing them turns an induced
rule into something you can model-check, prove with, export to TPTP or compare
against a reference — rather than eyeball.

### The two readings

A definite clause says two different things, and the kit will not choose for
you:

```python
from unicode_logic_kit import parse_prolog_clause

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
from unicode_logic_kit import parse_prolog_clause
from unicode_logic_kit.fol.prolog_input import PrologParsingError

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
from unicode_logic_kit import parse_prolog_clause
from unicode_logic_kit.fol.prolog_input import PrologParsingError

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
from unicode_logic_kit import parse_prolog_program

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

### Exporting back to Prolog

`fol.prolog_export.formula_to_prolog_clause` is the return leg: a formula
BUILT to look like a fact or a definite/normal clause goes back out as
Prolog text, `parse_prolog_clause`'s own `mode="clause"` reading run in
reverse. It is not a general `to_prolog()` — Prolog can only hold a narrow
shape, so most formulas are refused by name rather than approximated.

```python
from unicode_logic_kit import parse_prolog_clause
from unicode_logic_kit.fol.prolog_export import formula_to_prolog_clause

clause = "amide(A) :- carbon(C), nitrogen(N), bond(C, N), in(A, C)."
node = parse_prolog_clause(clause)
print(node.to_unicode_str())
# → ∀a ∀c ∀n (Carbon(c) ∧ Nitrogen(n) ∧ Bond(c, n) ∧ In(a, c) → Amide(a))

text = formula_to_prolog_clause(node)
print(text)
# → amide(V0) :- carbon(V1), nitrogen(V2), bond(V1, V2), in(V0, V1).
```

Every variable is renamed to a fresh `V0`, `V1`, ... — Prolog variable
spelling is scoped to one clause and carries no meaning beyond identity — in
the SAME alphabetical order `parse_prolog_clause` itself closes them in, so
reading the text back lands on the identical quantifier nesting:

```python
print(parse_prolog_clause(text).to_unicode_str())
# → ∀v0 ∀v1 ∀v2 (Carbon(v1) ∧ Nitrogen(v2) ∧ Bond(v1, v2) ∧ In(v0, v1) → Amide(v0))
```

A disjunctive head, a variable that occurs only in the head (not
range-restricted), a nested quantifier, or anything outside classical FOL is
refused **by name**:

```python
from unicode_logic_kit.fol.nodes import Atom, Implies, Or, Quantifier, Variable
from unicode_logic_kit.fol.prolog_export import PrologExportError

x = Variable("x")
bad = Quantifier("∀", x, Implies(Atom("Q", [x]),
                                 Or(Atom("P", [x]), Atom("R", [x]))))
try:
    formula_to_prolog_clause(bad)
except PrologExportError as exc:
    print(str(exc).split(": ", 1)[-1][:56])
# → the head of a rule must be a single atom, got Or ('P(x) 
```

`negation_as_failure="classical"` mirrors the importer's own opt-in, and the
same warning applies in reverse: passing it makes the round trip
syntactically faithful, but `\+ G` still only agrees with `¬G` when the
Prolog program is complete for `G` — see
{func}`~unicode_logic_kit.fol.prolog_export.formula_to_prolog_clause`'s module
docstring for exactly when that holds, and when it does not.

```python
node = parse_prolog_clause("p(A) :- q(A), \\+ r(A).",
                           negation_as_failure="classical")
try:
    formula_to_prolog_clause(node)
except PrologExportError as exc:
    print("refused:", "closed world assumption" in str(exc))
# → refused: True

print(formula_to_prolog_clause(node, negation_as_failure="classical"))
# → p(V0) :- q(V0), \+ r(V0).
```

`formula_to_prolog_program` renders several clauses at once, splitting a
top-level `∧` the way `parse_prolog_program` reads several clauses back
separately rather than disjoined.

## Attempto Controlled English

[ACE](https://github.com/Attempto/APE) is a controlled natural language with
exactly one reading per sentence — fixed by documented convention, not by a
guesser — which makes English-shaped text a real input format rather than an
NLP gamble. The kit drives the reference parser APE as an external subprocess
(LGPL; install: `git clone https://github.com/Attempto/APE ~/APE && cd ~/APE
&& make install`, needs SWI-Prolog — on Windows a WSL build is found
automatically, and `$UFK_APE_CMD` overrides discovery):

```python
from unicode_logic_kit.ace import ace_to_fol

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
  {func}`~unicode_logic_kit.ace.ace_coverage` flags such sentences
  (`reified_cardinality`). The DRS and formula routes below DO carry the
  counting force since ACE-4/5.

{func}`~unicode_logic_kit.ace.ace_coverage` runs any sentence list through the
route and reports each sentence's fate (`ok` / `tptp_unsupported` /
`tptp_unread` / `not_ace` / `infra`) — the kit's own 55-sentence corpus and
its recorded per-sentence outcomes live in `tests/fixtures/ace_corpus_v1.tsv`
and `tests/fixtures/ape_5f4d535_corpus_v1.json`.

### The DRS route: `ace_to_drs`

APE's own representation is a Discourse Representation Structure, and the kit
has a DRS core — so since 0.24.0 the DRS itself is first-class.
{func}`~unicode_logic_kit.ace.parse_ape_drs` reads APE's printed term 1:1
(pinned by a byte-identical round-trip over the whole corpus), and
{func}`~unicode_logic_kit.ace.ace_to_drs` maps it onto {mod}`unicode_logic_kit.drt`:

```python
from unicode_logic_kit.ace import ace_to_drs
from unicode_logic_kit.drt import drs_to_fol

drs = ace_to_drs("Every farmer who owns a donkey beats it.")
print(drs_to_fol(drs).to_unicode_str())
# → ∀x1 ∀x2 ∀e1 (Farmer(x1) ∧ Donkey(x2) ∧ Own(e1, x1, x2) → ∃e2 Beat(e2, x1, x2))
```

Verbs, nouns, adjectives and prepositions become kit predicates (`See(e1,
x1, x2)` — events stay, neo-Davidsonian), the copula becomes equality with
the be-event dropped (Attempto's own reference reading), proper names become
constants. A sentence maps **completely or not at all**:
{func}`~unicode_logic_kit.ace.map_ace_drs` returns a per-condition report
(`DrsMapping.rows`) naming every condition's verdict, and
{func}`~unicode_logic_kit.ace.condition_statistics` aggregates those verdicts
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
{func}`~unicode_logic_kit.ace.ace_to_formula` translates straight to one
formula, routing ACE's four modal boxes onto the kit's modal family —
`must` → `□`, `can` → `◇` (alethic), `should` → `Ⓞ`, `may` → `Ⓟ` (deontic, a
documented choice matching Attempto's recommendation/admissibility gloss):

```python
from unicode_logic_kit.ace import ace_to_formula

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
from unicode_logic_kit.ace import ace_to_drs
from unicode_logic_kit.drt import drs_to_fol

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
{func}`~unicode_logic_kit.atp.z3_arith.is_valid_arith` decides the
arithmetic fragment (proves `1 + 2 = 3`, refutes `1 + 2 = 4`).

### The reverse direction: `drs_to_ace` (ACE-6)

The pipeline also runs backwards. {func}`~unicode_logic_kit.ace.drs_to_ace`
verbalizes a kit DRS as ACE text plus the APE user-lexicon entries that
carry its content words, and {func}`~unicode_logic_kit.ace.ace_round_trip`
is the machine self-check: the text goes back through APE and the mapping,
and Z3 judges the result against the input — over the kit's corpus, every
mappable sentence closes that loop.

```python
from unicode_logic_kit.ace import drs_to_ace, ace_round_trip
from unicode_logic_kit.drt import parse_drs

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
({class}`~unicode_logic_kit.ace.AceVerbalizationError`): upper-bound
cardinalities (`Card(g, <=, n)` — APE reads "at most" as the maximality
list), values outside equalities, binary predicates over individuals
(an ACE verb always carries an event), non-invertible names.

Since 0.25.0 the reverse direction also takes FORMULAS.
{func}`~unicode_logic_kit.drt.fol_to_drs` runs the standard translation
backwards — it recognizes exactly the shape `drs_to_fol` emits and
rebuilds the box structure, refusing everything outside that image by
name ({class}`~unicode_logic_kit.drt.FolToDrsError`: modality,
biconditionals, bare universals, formula-level counting, function terms,
free variables). {func}`~unicode_logic_kit.ace.formula_to_ace` chains the
two: "is this formula expressible as ACE?" becomes two refusal-checked
steps, and a positive answer is a sentence:

```python
from unicode_logic_kit import MSFLParser
from unicode_logic_kit.ace import formula_to_ace

donkey = MSFLParser().parse(
    "∀x1 ∀x2 ∀e1 (Farmer(x1) ∧ Donkey(x2) ∧ Own(e1, x1, x2)"
    " → ∃e2 Beat(e2, x1, x2))")
print(formula_to_ace(donkey).text)
# → If a farmer X1 owns a donkey X2 then X1 beats X2.
```

{func}`~unicode_logic_kit.ace.chem_ulex` renders the ChemLog signature
(`unicode_logic_kit.chem`) as such a user lexicon, so ACE can talk about
molecules — "There is a carbon X1. X1 bonds an oxygen X2. X1 is
aromatic." parses with the DRS carrying `c`, `bond`, `aromatic`. Two
shape facts are documented rather than hidden: kit-side the symbols
arrive capitalized ({func}`~unicode_logic_kit.ace.ace_kit_name` computes
the spelling), and ACE verbs are neo-Davidsonian, so binary ChemLog
relations arrive with an event argument (`Bond(e1, x1, x2)`); the three
nullary net-charge predicates are unspeakable in ACE (a sentence needs a
subject) and excluded by name.

## SMT-LIB2 writing

Reading (the table above) returns one {class}`~unicode_logic_kit.Node` per assertion.
Writing is the inverse, one formula — or several — per `(assert ...)`:
{func}`~unicode_logic_kit.atp.z3_input.to_smtlib` (premises plus a goal) and its
single-formula convenience form `Node.to_smtlib()` (no premises).

A naive `Node.to_z3()` + `z3.Solver.to_smt2()` combination is not sound enough
to build this on directly. Z3's own serialiser pipe-quotes almost every
illegal symbol name automatically — a non-ASCII name round-trips correctly
with no help at all — but it silently emits some names *unquoted*: one that is
pure ASCII and starts with a digit (`2008SummerOlympics`) or reads as a numeral
(`-1`), one that IS an SMT-LIB2 `<reserved>` word used as a symbol (`let`), and
one that holds a `'` — producing `.smt2` text that fails to parse back. It also
writes names that Z3 reads back but that SMT-LIB does not allow, or that another
solver reads as something else: one that begins with `.` or `@`, one that holds
`|` or `\`, `par`, and the symbols of the SMT-LIB theories (`+`, `>`, `select`,
`str.len`, ...), which cvc5 already knows with a fixed signature. And it writes a
shared sub-term as `(let (($x24 ...)) ...)` or `(let ((?x10 ...)) ...)`, under
names of its own and without looking at the symbols the text declares, so a
declared symbol spelled `$x24` or `?x10` would be shadowed inside the `let`.
`to_smtlib` reuses the sanitiser {class}`~unicode_logic_kit.Cvc5Backend` already
proves against Z3's own parser (one shared name map across every premise and the
goal, so a symbol renames consistently everywhere it occurs) instead of solving
this a second time, and it renames every one of these names (a symbol spelled
`$x24` is written `n$x24`, one spelled `?x10` is written `n?x10`, and the text
reads back under the new name), so the text is the same whatever logic the
reading solver is set to:

```python
from unicode_logic_kit import MSFLParser
from unicode_logic_kit.atp.z3_input import to_smtlib

p = MSFLParser()
premises = [p.parse("∀x (P(x) → Q(x))"), p.parse("P(alice)")]
goal = p.parse("Q(alice)")
print(to_smtlib(goal, premises))
```

```text
(set-logic ALL)
; benchmark generated from python API
(set-info :status unknown)
(declare-sort S 0)
(declare-fun Q (S) Bool)
(declare-fun P (S) Bool)
(declare-fun alice () S)
(assert
 (forall ((x S) )(let (($x10 (Q x)))
 (let (($x11 (P x)))
 (=> $x11 $x10))))
 )
(assert
 (P alice))
(assert
 (Q alice))
(check-sat)
```

Every premise gets its own assertion ahead of the goal's — more useful as a
standalone problem than one folded `(∧ premises) → goal` implication, and
what `parse_smtlib` reads back: one {class}`~unicode_logic_kit.Node` per
top-level `assert`. Refusal is inherited, not reimplemented: a construct that
`to_z3()` itself has no encoding for (second-order quantification, a modal
operator, ...) raises the exact same `NotImplementedError` from `to_smtlib`
too, naming the construct, with one sentence appended pointing at SMT-LIB2
export specifically.

Each formula is one `(assert ...)`, a truth constant included (`⊤` is
`(assert true)`). A counting quantifier is expanded before the symbols are
renamed, so its witnesses are never spelled like a predicate, a function, a
constant or a sort of the problem: in SMT-LIB text a bound variable and the
symbol it shadows are one identifier, and cvc5 can end the process on such a text
(`(exists ((x0 S)) (x0 x0))`) instead of reporting a type error. The expansion
grows with the bound: a counting quantifier is written for any bound up to 500 and
refused above, with a `NotImplementedError` that names the bound.

A symbol is a predicate, a function or a variable at one arity, and two
declarations of one name are an error in SMT-LIB2, so a symbol whose name is
taken by another of a different arity or kind is renamed too: `P(a)` and
`P(a, b)`, a predicate and a function of one name, a variable and a constant of
one name are written under different tokens (the first keeps the name, the
others get one of their own, such as `P_2`). A constant or a variable whose name
ends in `!v` or `!c` is renamed as well, because the reader of the text decodes
such a symbol as a variable or as another constant; it reads back under its
token, like any renamed name. `parse_smtlib` reads two different symbols of one
text as two different names: `a!c` and `a!c!c` are two constants. A free variable is written as a constant of that
name, and `parse_smtlib` reads it back as a `Constant`. A sort is the unary
predicate of its name, so a sort name that is digit-leading or an SMT-LIB word is
renamed like any other predicate (`2D` is written `n2D`), and a sorted constant
`c:S` takes the same token as the plain constant `c`. `to_smtlib` is a writer: it
adds no sort axioms, so its text asserts neither that a sort is non-empty nor
that `c` is in `S`.

A numeral is the constant of its value (`1` and `1.0` are one constant), and
`+ - * / < > ≤ ≥` are uninterpreted symbols, because this route is not asked for
arithmetic:

```python
print(to_smtlib(p.parse("1 + 2 = 3")))
```

```text
(set-logic ALL)
; benchmark generated from python API
(set-info :status unknown)
(declare-sort S 0)
(declare-fun |3| () S)
(declare-fun n+ (S S) S)
(declare-fun |2| () S)
(declare-fun |1| () S)
(assert
 (= (n+ |1| |2|) |3|))
(check-sat)
```

`+` is written as `n+`, and `1`, `2` and `3` are constants of the one sort, so
this text does not say that `1 + 2` is `3`. A numeral made of digits, or of
digits and an exponent, is written between bars (`|1|`, `|1e-07|`); a decimal or
a negative number gets a token (`n2.5`, `n-3`).

{func}`~unicode_logic_kit.parse_smtlib` reads a declared symbol as a number only
when its sort is uninterpreted, which is where the writer puts a numeral (`P(1)`
is written with a symbol `|1|` of the sort `S`; a decimal or a negative number
gets a token and is read back as the constant of that token). A symbol of sort
`Int` or `Real` is a constant whatever its name: in
`(declare-fun |1| () Int) (assert (not (= |1| 1)))` the symbol is the constant
named `1` and the numeral is the number `1`, two different terms, so the text is
satisfiable, and `to_z3` and `to_smtlib`, which write both as one symbol, refuse
the pair by name. A Z3 rational numeral is read through the exact decimal text it
spells (its denominator has no prime factor but 2 and 5), by the 15-digit rule of
the Prover9 section above; a numeral with more digits, or with no decimal text
(the quotient `1/3` handed to {func}`~unicode_logic_kit.from_z3`), is refused with a
`ValueError` that names the numeral. `(/ 1 3)` in a text is an application of `/`,
not a numeral.

This page's read table has entry points for every format the kit imports;
several formats besides SMT-LIB2 also have an export function without a
matching entry here (TPTP, Prover9 and LaTeX are `Node` methods, documented at
their own class rather than per format).

The nullary atoms `$true` and `$false` (printed `⊤` and `⊥`) are the truth
constants of every writer that can carry them, spelled as the target spells
them: TPTP and THF `$true` / `$false`, Prover9 `$T` / `$F`, SMT-LIB `true` /
`false`, CASL `true` / `false` (which `parse_casl_spec` reads back), Isabelle and
Lean `True` / `False`. A target with no agreed reading of them refuses the
formula by name: the Prolog and nanoCoP writers, the deep embeddings and the
relevant and substructural Isabelle exports.

A free variable is a parameter: one unknown element, the same in every formula
of the problem (`P(x) ⊢ P(x)` holds, `P(x) ⊢ P(alice)` does not). The SMT-LIB and
Prover9 writers write it as a constant of its name; the TPTP (`fof` and TF0) and
CASL writers cannot state a parameter, and refuse a free variable by name.

## CASL

CASL is the Common Algebraic Specification Language — the sorted specification
format HETS speaks. Export produces a whole spec, sorts and predicate
declarations included:

```python
from unicode_logic_kit import MSFLParser, to_casl_spec

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
from unicode_logic_kit import MSFLParser, to_casl_spec, parse_casl_spec

phi = MSFLParser().parse("∀x (Human(x) → Mortal(x))")
spec = parse_casl_spec(to_casl_spec([phi], spec_name="Ontology"))
print([axiom.to_unicode_str() for axiom in spec.axioms])
# → ['∀x (Human(x) → Mortal(x))']
```

Unsorted formulas are exported over a single `default_sort` (`Thing` unless you
say otherwise); a genuinely sorted MSFOL formula keeps its sorts. The default is
a sort of its own: a sort that the formulas write (`∀x:Thing`, `c:Thing`) or
`subsorts` declares under the same name is refused when the default is used,
because an unsorted position would silently become a position of that sort, and
the refusal names `default_sort=`. The export is a typed text: CASL's sorts are
disjoint, and an unannotated constant or a function value is declared at the sort
of the position it is used in. That is stronger than the kit's own reading of a
sort (see the TF0 section below), so a decision about the exported text can differ
from the kit's; {class}`~unicode_logic_kit.atp.HetsBackend` refuses the problems on
which it does (see HETS below).

CASL writes a bound variable, a constant and a predicate as one identifier, and
inside its quantifier a name is the variable. So a bound variable that is spelled
like any symbol of the spec (a constant, a function, a predicate or a sort of any
formula, or the default sort) is renamed in the text, in its quantifier and in
every occurrence it binds. Names are compared exactly (`W` and `w` are two), and
text without a clash is unchanged:

```python
from unicode_logic_kit import to_casl_spec
from unicode_logic_kit.fol.nodes import And, Atom, Constant, Quantifier, Variable

w = Variable("w")
clash = And(Quantifier("∀", w, Atom("P", [w])), Atom("Q", [Constant("w")]))
print(to_casl_spec([clash], spec_name="Clash"))
```

```text
spec Clash =
  sorts Thing
  ops w : Thing
  preds P : Thing;
        Q : Thing
  . (forall w0 : Thing . P(w0)) /\ Q(w)
end
```

The text reads back as the same formula up to the names of the renamed binders
(`∀w0 P(w0) ∧ Q('w')`, where `'w'` is the constant `w`, written in quotes because a
bare `w` would be a variable). `to_casl_spec` and `formula_to_casl` take `visible_symbols`
for the symbols that the text sees without declaring them, and `to_dol_library`
gives `to_casl_spec` those of the specs that a spec extends.

### Subsorting

A `Signature`'s optional `subsorts` — a child sort mapped to its direct
declared parents, read with plain subset semantics (`S < T` means `⟦S⟧ ⊆
⟦T⟧`, nothing more) — round-trips through CASL's own native `sort S < T`
syntax. `to_casl_spec(..., subsorts=sig.subsorts)` emits one `sort <child> <
<parent>` line per direct edge (both sort names are declared even if a
formula never mentions one of them), and `parse_casl_spec` reads the same
declarations — including the list form `sort S1, S2 < T` — back into the
identical `subsorts` mapping on the parsed spec's `Signature`:

```python
from unicode_logic_kit import MSFLParser, to_casl_spec, parse_casl_spec, Signature

msfol = MSFLParser(many_sorted=True)
phi = msfol.parse("∀x:Animal Mortal(x)")
sig = Signature.from_dict({"subsorts": {"Human": ["Animal"], "Animal": ["Thing"]}})

spec = to_casl_spec([phi], spec_name="Ontology", subsorts=sig.subsorts)
print(spec)
```

```text
spec Ontology =
  sorts Animal, Human, Thing
  sort Animal < Thing
  sort Human < Animal
  preds Mortal : Animal
  . forall x : Animal . Mortal(x)
end
```

```python
parsed = parse_casl_spec(spec)
dict(parsed.signature.subsorts)
# → {'Animal': frozenset({'Thing'}), 'Human': frozenset({'Animal'})}
```

Only the plain subset reading round-trips this way: a partial function, a
free/generated type, or overloading a predicate/operation across the
hierarchy stays refused on import exactly as it was before subsorting was
added — subsorting adds one new accepted declaration shape, not a wider
CASL fragment.

## TF0 (typed TPTP)

TPTP's classical `fof` dialect has no notion of sorts: exporting a many-sorted
formula through `Node.to_tptp` turns each sort into an ordinary guard predicate
(`∀x:Human φ` becomes `![X]: (human(X) => φ)`). {mod}`unicode_logic_kit.atp.tptp_tff`
writes the OTHER TPTP dialect instead — **TF0**, monomorphic typed first-order
TPTP — where a sort is a genuine `tff` type, not a predicate:

```python
from unicode_logic_kit import MSFLParser
from unicode_logic_kit.atp.tptp_tff import generate_tff_problem

MSFOL = MSFLParser(many_sorted=True)
premises = [MSFOL.parse("∀x:Human Mortal(x)"), MSFOL.parse("Philosopher(socrates:Human)")]
conclusion = MSFOL.parse("Mortal(socrates:Human)")
print(generate_tff_problem(premises, conclusion))
```

```text
tff(sort_decl_1, type, human: $tType ).
tff(const_decl_2, type, socrates: human ).
tff(pred_decl_3, type, mortal: human > $o ).
tff(pred_decl_4, type, philosopher: human > $o ).
tff(premise_1, axiom, (![X: human]: mortal(X)) ).
tff(premise_2, axiom, philosopher(socrates) ).
tff(goal, conjecture, mortal(socrates) ).
```

And it reads back, recovering the declared {class}`~unicode_logic_kit.fol.signature.Signature`
alongside the formulas — a sort name round-trips exactly, and a bare constant
occurrence is promoted back to a `SortedConstant` wherever its own separate
`type` declaration gave it a concrete sort (a formula body has no room to say
that inline; only a bound variable does):

```python
from unicode_logic_kit.fol.tptp_input import parse_tff_problem

sig, formulas = parse_tff_problem(generate_tff_problem(premises, conclusion))
print(sig.predicates["Mortal"])
for f in formulas:
    print(f.role, f.formula.to_unicode_str())
```

```text
PredicateDecl(name='Mortal', arity=1, arg_sorts=('Human',))
axiom ∀x:Human Mortal(x)
axiom Philosopher(socrates:Human)
conjecture Mortal(socrates:Human)
```

Scope is deliberately narrow: THF (higher-order TPTP), TF1 polymorphism
(`!> [...] : ...`, type variables), and TPTP's built-in arithmetic sorts
(`$int`/`$rat`/`$real`) are each refused **by name**, and the TF0 writer writes
none of them — never silently narrowed to something they are not. The reader
refuses the first two by the kind of statement and by the binder, before it reads
a formula: a `thf(...)` statement of any body is a `TptpParsingError` that names
THF, and the type binder `!>` or a quantifier variable of type `$tType`
(`![A: $tType]`) is an error that names TF1 polymorphism and is both a
`TptpParsingError` and a `NotImplementedError`. The arithmetic sorts stay a
`NotImplementedError`. A comment or a quoted atom never triggers a refusal. A
numeral is an ordinary constant here: the writer declares it as a constant of
`$i` named after its value (`1` and `1.0` are one constant, `n1`; `2.5` is
`n2u002e5`), `+ - * /` as uninterpreted functions and `< > ≤ ≥` as uninterpreted
predicates. The {class}`~unicode_logic_kit.atp.TptpNameMap` that
{func}`~unicode_logic_kit.atp.generate_tff_problem_with_mapping` returns lists the
numerals (its `numerals` set; `reverse_numerals()` gives each word back as its
value). A numeral that the sort inference would put into a user sort, and a
`Constant` spelled like a numeral of the problem (`Number(1)` next to
`Constant('1')`), are refused. TPTP's own arithmetic is the TFA writer's
({func}`~unicode_logic_kit.generate_tff_arith_problem`, the `sort="int"` /
`sort="real"` option of the backends).

{mod}`~unicode_logic_kit.atp.vampire_entailment` and
{mod}`~unicode_logic_kit.atp.eprover_backend` (E, Zipperposition) try this route
the moment a sorted node shows up anywhere in the premises or the conclusion, and
write `fof` instead when the TF0 writer refuses the problem (the two refusals
below). The result says which text was written (`dialect`, `"tff"` or `"fof"`)
and, after a refusal, why (`tff_fallback`; the verdict's `detail` repeats it).
`tff=True` insists on TF0: the `check_entailment_*_detailed` functions then raise
the refusal, and a backend answers it with the verdict `unknown` /
`unsupported`. `tff=False` writes `fof`.

TF0 declares every symbol once, in one flat table, so a predicate and a
function/constant that render as the same word (the class `Agent` and the role
function `agent`) are never declared under one name: the function or constant is
written `agent_term` instead, and
{func}`~unicode_logic_kit.atp.generate_tff_problem_with_mapping` returns the
{class}`~unicode_logic_kit.atp.TptpNameMap` that records the rename. See
"Building a TPTP problem for a prover" in {doc}`classical-reasoning`.

A **sort** and a **predicate** that render as the same word are refused, naming
both. In the example above the predicate is `Philosopher` rather than `Human`
for that reason: the kit defines a sort as the guard predicate of its name
(`∀x:S φ` is `∀x (S(x) → φ)`, `∃x S(x)` says the sort is non-empty, and a
sorted constant `c:S` is an element of `S`, `S(c)`), which is what `to_z3`, the
`fof` writer and the Prover9 writer do, so there
`∃y:Car Car(y)` is valid. TF0 would declare the type `car` and an unrelated
predicate `car`, and `∃y:Car Car(y)` is not a theorem of that problem, so a
prover answering over TF0 would answer another question than z3 does. Rename one
of the two, or write the problem with the `fof` writer, which reads the sort as
that predicate. A problem needs no conclusion: `generate_tff_problem(premises)`
writes no `conjecture` line, for a prover that is asked whether the premises are
satisfiable.

TF0 *types* a sorted constant (`socrates:Human` is declared `socrates: human`),
which agrees with the kit: `c:S` is an element of `S` on every route. What TF0
cannot say is that a term belongs to no sort. It infers the sort of an
unannotated term from where the term is used, its types are disjoint, and its
`$i` is a type of its own, while the kit has ONE universe: a sort is a subset of
it, and an unannotated constant, an unsorted variable and the value of a
function may be any element. So the writer refuses, by name, the two shapes of
problem for which the typed text would answer another question than `to_z3` does
(`Tf0Refusal`, a `ValueError` and a `NotImplementedError` at once), and says what
to write instead:

- **A constant or a function value that the inference puts into a sort though the
  problem does not say so.** `∀x:Human Mortal(x) ⊢ Mortal(socrates)` is not
  entailed (a universe of two elements: `Human` and `Mortal` hold of the first,
  `socrates` is the second), but TF0 would declare `socrates` a `Human` and prove
  it. Write the constant with its sort (`socrates:Human`, which is entailed), or
  write the problem as `fof`.
- **An equation over a variable of an unsorted quantifier, in a problem that has
  a sort.** `∀x ∀y x = y ⊢ ∀x:A ∀z:A x = z` is valid (the premise leaves the
  universe one element, and `A` is a subset of it), but TF0's `$i` is a type apart
  from `A`, so the typed text does not entail it. Give the variable its sort, or
  write the problem as `fof`.

The automatic mode of the backends writes `fof` for such a problem (above), and
`HetsBackend` refuses it (see HETS below).

One subtlety worth knowing when you compare the two routes: TPTP TF0
quantifiers range over **non-empty** types (and this kit's own many-sorted model
finder already assumes the same — every sort gets a non-empty universe), so
`∀x:S φ ⊢ ∃x:S φ` is a theorem under `tff` even with no witness of sort `S`
anywhere in the problem. There the type declaration carries the assumption, and
the TF0 writer emits nothing extra for it. The classical guard-atom `fof` route
has no types, so it states the same assumption as an axiom:
{func}`~unicode_logic_kit.atp.generate_tptp_problem` and
{func}`~unicode_logic_kit.atp.generate_tptp_problem_with_mapping` add one
`fof(nonempty_sort_<i>, axiom, (?[X0]: s(X0)))` per distinct sort the problem
mentions (numbered from 1, written between the premises and the `conjecture`; an
extra, never-negated axiom, not folded into any formula's own translation), and
the Prover9 writer adds the same `∃x S(x)` as an extra line of
`formulas(assumptions)`. So both routes prove `∀x:S φ ⊢ ∃x:S φ` with no witnessed
member of `S`, and a "not entailed" verdict from either is not an artefact of an
empty sort. An unsorted problem gets no such line.

The membership of a sorted constant is stated the same way: after the
non-emptiness lines, one `fof(sort_member_<i>, axiom, s(c))` per pair of a sorted
constant and its sort (a constant written with two sorts gets two lines), and the
same atoms in `formulas(assumptions)` for Prover9. Without them
`∀x:Human Mortal(x) ⊢ Mortal(socrates:Human)` would not be proved, because the
plain text forgets that `socrates` is a `Human`. Both kinds of line are
background assumptions and never part of the goal. A sort and a constant that are
spelled alike are two symbols (in `fof`, `human` the sort and `human_term` the
constant). The Prover9 writer sends a sort name through the same sanitiser as every
other symbol, so a non-ASCII, digit-leading or keyword-like name is renamed (`2D`
is written `s2D`, `exists` is written `exists2`), and the TF0 writer renames a
non-ASCII or digit-leading sort too; the `fof` writer refuses a sort name that is
not a TPTP word (a digit-leading or non-ASCII one), naming it. When a proof of
Vampire or E uses such a line, the verdict's
`detail` names it, apart from the premises (a Vampire verdict's
`relevant_premises` lists the premises that its proof used, and never a
background line).

## `include` directives

A TPTP problem often pulls its shared axioms in from a separate file rather
than repeating them: `include('animals.ax').` — or, TPTP-library style,
`include('Axioms/SET001+0.ax')`, a path relative to a *library root*, not
to the referring problem file. {func}`~unicode_logic_kit.load_tptp` (and
{func}`~unicode_logic_kit.load_tptp_problem`,
{func}`~unicode_logic_kit.fol.tptp_input.load_tff_problem`) resolve these —
{func}`~unicode_logic_kit.parse_tptp_formula` never does, since a single bare
formula has no "including file" to resolve one relative to:

```python
import os, tempfile

root = tempfile.mkdtemp()
with open(os.path.join(root, "animals.ax"), "w") as f:
    f.write(
        "fof(dog_is_animal, axiom, ![X]: (dog(X) => animal(X))).\n"
        "fof(rex_is_dog, axiom, dog(rex)).\n"
    )
with open(os.path.join(root, "problem.p"), "w") as f:
    f.write(
        "include('animals.ax').\n"
        "fof(goal, conjecture, animal(rex)).\n"
    )

from unicode_logic_kit import load_tptp

for record in load_tptp(os.path.join(root, "problem.p")):
    print(record.name, record.role, record.formula.to_unicode_str())
```

```text
dog_is_animal axiom ∀x (Dog(x) → Animal(x))
rex_is_dog axiom Dog(rex)
goal conjecture Animal(rex)
```

`animals.ax`'s two axioms are spliced in exactly where the `include`
appeared. Resolution tries, in order: the including file's own directory,
then each root in `search_paths` (`load_tptp(path, search_paths=(...))`),
then `os.environ["TPTP"]` if set — the convention external TPTP tooling
itself uses for the library root. `include('path', [name1, name2])`
imports only those formulas, by their own TPTP statement name. A missing
file, an unresolvable name, or a circular include chain (`A` includes `B`
includes `A`) each raise `TptpParsingError` naming the path or chain, never
silently drop or loop; {func}`~unicode_logic_kit.fol.tptp_input.parse_tff_problem`
and `load_tff_problem` resolve them too, except a
selection list cannot be applied to an included file that itself declares
TFF vocabulary (a `tff(name, type, ...).` statement) — its own statement
name isn't tracked separately from the symbol it declares, so that
combination is refused by name rather than guessed at. The optional 4th
(`source`)/5th (`useful_info`) annotation fields of any statement —
`fof(name, role, formula, file(...), [...])` — parse and are silently
discarded, in every reader (`fof`/`cnf`/`tff` alike): this reader models a
statement's FORMULA, never its provenance metadata.

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
from unicode_logic_kit.hets import hets_available, discover_hets_url

print(hets_available())                       # already running on :8000?
url, container = discover_hets_url(start_container=True)
print(url)                                    # → http://localhost:8000
```

`discover_hets_url` returns the container handle alongside the URL so you can
stop what you started. Without `start_container=True` it only looks.

### Asking it something

```python
# doctest: +SKIP  — needs Docker
from unicode_logic_kit import MSFLParser, to_casl_spec
from unicode_logic_kit.hets import HetsClient

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
own {class}`~unicode_logic_kit.ProverBackend` protocol, so HETS joins the prover
chain like any other backend. And
{func}`~unicode_logic_kit.hets.register_hets_comorphisms` asks the running server
which translations it knows and registers each as a `hets:<Name>` edge in the
kit's comorphism registry — so `translate` can follow a path the kit does not
implement itself:

```python
# doctest: +SKIP  — needs Docker
from unicode_logic_kit.hets import register_hets_comorphisms

edges = register_hets_comorphisms()
print(len(edges), edges[:3])
```

The edges are **discovered, not hardcoded**: what you get depends on the HETS
build you are talking to.

`HetsBackend` decides the kit's question. The CASL it uploads is the typed text
described in the CASL section, so a problem on which that text would answer
another question than `to_z3` does (the two shapes listed in the TF0 section: a
constant or a function value that the inference puts into a sort, and an
equation over a variable of an unsorted quantifier next to a sort) is refused
before it is uploaded. `decide` answers `unknown` / `unsupported` with the
reason; `check_consistency`, which asks whether the premises have a model,
raises the same refusal. The sort that the export gives every unsorted position
is `Thing`, or the first of `Thing1`, `Thing2`, ... that no sort of the problem is
spelled like.

### Quantified modal logic, via `fol.qml`

CASL/DOL have no modal operators of their own — {mod}`unicode_logic_kit.fol.casl_export`
refuses `Box`/`Diamond`/… by name, on purpose (see that module's own
docstring). But {mod}`unicode_logic_kit.fol.qml` already translates the kit's
full first-order modal fragment (alethic/temporal/deontic/per-agent
epistemic-doxastic/PAL) down to plain classical FOL — the *standard
translation* Z3 already decides for {func}`~unicode_logic_kit.fol.qml.qml_is_valid`
— so a modal formula CAN reach HETS, by translating it first:
{func}`unicode_logic_kit.hets.dol.to_dol_library_from_modal` composes that
translation, an identifier-sanitising rename (injective, and nothing else —
`qml` renames a user predicate spelled like one of its own relations by
appending U+00B7, `R` → `R·`, and that is no CASL identifier; the world
variables it mints are CASL identifiers as they are), and the
plain CASL exporter above into one uploadable `.dol` library:

```python
from unicode_logic_kit.fol.nodes import Atom, Box, Implies
from unicode_logic_kit.fol.qml import qml_is_valid
from unicode_logic_kit.hets.dol import to_dol_library_from_modal

P = Atom("P", ())
t_axiom = Implies(Box(P), P)                  # □P → P, valid on a REFLEXIVE frame

print(qml_is_valid(t_axiom, frame="T"))       # Z3's own verdict, for comparison
print(to_dol_library_from_modal(t_axiom, frame="T", spec_name="TAxiom",
                                library_name="ModalLib"))
```

```text
True
library ModalLib
logic CASL

spec TAxiom =
  sorts Thing
  preds E : Thing * Thing;
        Object : Thing;
        P : Thing;
        R : Thing * Thing;
        World : Thing
  . ((((((((forall t : Thing . not (World(t) /\ Object(t))) /\ (exists w : Thing . World(w))) /\ (exists x : Thing . Object(x))) /\ (forall w : Thing . forall v : Thing . (R(w, v) => (World(w) /\ World(v))))) /\ (forall x : Thing . forall w : Thing . (E(x, w) => (Object(x) /\ World(w))))) /\ (forall w : Thing . (World(w) => R(w, w)))) /\ (forall x : Thing . forall w : Thing . forall v : Thing . (((Object(x) /\ World(w)) /\ (World(v) /\ (E(x, w) /\ R(w, v)))) => E(x, v)))) /\ (forall x : Thing . forall w : Thing . forall v : Thing . (((Object(x) /\ World(w)) /\ (World(v) /\ (E(x, v) /\ R(w, v)))) => E(x, w)))) => (forall w : Thing . (World(w) => ((forall w0 : Thing . ((World(w0) /\ R(w, w0)) => P(w0))) => P(w)))) %implied
end
```

Uploaded to a running HETS, this proves the same way any other CASL spec
does:

```python
# doctest: +SKIP  — needs Docker
from unicode_logic_kit.hets.docker import discover_hets_url
from unicode_logic_kit.hets.client import HetsClient

url, container = discover_hets_url(start_container=True)
client = HetsClient(url)
lib = to_dol_library_from_modal(t_axiom, frame="T", spec_name="TAxiom",
                                library_name="ModalLib")
iri = client.upload(lib, "t_axiom.dol")
print(client.prove(iri, "TAxiom", reasoner="SPASS")[0]["result"])
```

```text
Proved
```

`mode=`/`frame=`/`systems=`/`bridges=`/`temporal_closure=` all forward
straight through to {func}`~unicode_logic_kit.fol.qml.qml_validity_formula`, so
Barcan/converse-Barcan under a domain regime, an S5 knowledge system, a
Geach frame, or a cross-family bridge each reach HETS exactly like the plain
alethic case above. Scoped to exactly what `fol.qml` already translates — no
native `logic Modal` CASL institution is added; a construct that module
itself refuses (`Until`/`Since`, the `↓` binder, a non-first-order frame
condition such as Löb/McKinsey/Grz) is refused here too, by the same name,
unchanged.

The translation binds variables of its own (`w`, `v`, `w0`, `x`, `t`, ...). A user
constant, function or predicate spelled like one of them is not read as that
variable: the CASL exporter renames the clashing binder (see the CASL section), so
the text reads back as the translation up to the names of those variables, and a
constant called `w`, `v`, `x`, `t` or `w0` never changes the query.

Object identity (`=`/`≠`) inside a modal formula needs no special handling,
and the reason is worth stating. `fol.qml` translates `a = b` to the *same
binary* `a = b` over the object terms, with **no world argument** (and
`a ≠ b` to `¬(a = b)`), so identity is rigid: it does not vary from world to
world. That is exactly CASL's own fixed, built-in `=` — always two terms,
never declared in `preds` — so `to_dol_library_from_modal` renders it infix
and renames nothing, and {func}`~unicode_logic_kit.fol.casl_import.parse_casl_spec`
reads the identical atom back. CASL has no disequality connective and needs
none: `a ≠ b` arrives as `not a = b`.

```python
from unicode_logic_kit.fol.nodes import Atom, Box, Constant, Implies

a, b = Constant("a"), Constant("b")
eq_axiom = Implies(Box(Atom("=", [a, b])), Atom("=", [a, b]))   # □(a=b) → a=b

print(qml_is_valid(eq_axiom, frame="T"))   # True — the T-schema, on an atomic sentence
lib = to_dol_library_from_modal(eq_axiom, frame="T", spec_name="EqT",
                                library_name="EqLib")
print(lib)
```

```text
True
library EqLib
logic CASL

spec EqT =
  sorts Thing
  ops a : Thing;
      b : Thing
  preds E : Thing * Thing;
        Object : Thing;
        R : Thing * Thing;
        World : Thing
  . ((((((((((forall t : Thing . not (World(t) /\ Object(t))) /\ (exists w : Thing . World(w))) /\ (exists x : Thing . Object(x))) /\ (forall w : Thing . forall v : Thing . (R(w, v) => (World(w) /\ World(v))))) /\ (forall x : Thing . forall w : Thing . (E(x, w) => (Object(x) /\ World(w))))) /\ (forall w : Thing . (World(w) => R(w, w)))) /\ (forall x : Thing . forall w : Thing . forall v : Thing . (((Object(x) /\ World(w)) /\ (World(v) /\ (E(x, w) /\ R(w, v)))) => E(x, v)))) /\ (forall x : Thing . forall w : Thing . forall v : Thing . (((Object(x) /\ World(w)) /\ (World(v) /\ (E(x, v) /\ R(w, v)))) => E(x, w)))) /\ Object(a)) /\ Object(b)) => (forall w : Thing . (World(w) => ((forall w0 : Thing . ((World(w0) /\ R(w, w0)) => a = b)) => a = b))) %implied
end
```

Because identity is rigid, the usual facts about it hold on this route exactly
as they do for `qml_is_valid`, and HETS agrees with Z3 on each of them
(`tests/test_dol.py`'s live battery): `a = b → □(a = b)` and
`a ≠ b → □(a ≠ b)` are theorems in every frame, K included, while the
converse `□(a = b) → a = b` needs a frame in which every world has at least
one accessible world (T, S4, S5, KD, …) — in K a dead-end world makes the box
vacuously true while `a` and `b` differ, which is why `eq_axiom` above is
`False` under `frame="K"`:

```python
necessity = Implies(Atom("=", [a, b]), Box(Atom("=", [a, b])))   # a=b → □(a=b)
print(qml_is_valid(necessity, frame="K"))   # True — identity is rigid
print(qml_is_valid(eq_axiom, frame="K"))    # False — a dead-end world
```

```text
True
False
```

`sanitize_modal_identifiers` (the renaming step above, exposed publicly so it
can also be used standalone — e.g. to inspect the sanitised `Node` itself, or
to unit-test the renaming in isolation from CASL rendering) renames
identifiers only; it does not rewrite connectives. So a `≠` atom, of any
arity, handed to it directly is refused loudly rather than mis-renamed: CASL
has no native disequality, and `fol.qml` never leaves one in its output, so
such an atom can only come from a hand-built or classically parsed formula that
bypassed `to_dol_library_from_modal`/`qml_validity_formula`. Write
`Not(Atom("=", [a, b]))` there, which is what `fol.qml` writes itself:

```python
from unicode_logic_kit.fol.nodes import Atom, Constant
from unicode_logic_kit.hets.dol import sanitize_modal_identifiers

a, b = Constant("a"), Constant("b")
sanitize_modal_identifiers(Atom("≠", [a, b]))   # raises NotImplementedError
```

```text
NotImplementedError: hets.dol: sanitize_modal_identifiers cannot rename a '≠'
atom ('a' ≠ 'b') -- CASL has no native disequality connective, so it would either
become a meaningless renamed predicate (masking the lost 'not equal' meaning)
or crash fol.casl_export's own identifier check. ...
```

A `=` atom with other than two terms is not CASL's identity. No text front-end
of the kit produces one and `qml_validity_formula` refuses it by name, so it
can only be built by hand; the sanitiser leaves it under its literal name and
CASL's own exactly-two-terms check refuses it.

### Reading a real HETS translation of an ontology

The three sections above drive HETS with text this kit WROTE. Reading back a
translation HETS made of somebody else's ontology is a different job, and
HETS 0.108.0 puts three obstacles in the way. Each gets a named tool, and
none of them is a widened parser.

**The development graph is not valid JSON.** HETS serialises OWL axiom
strings by applying Haskell's `show` to a string whose characters are the
UTF-8 *bytes* of the intended text, and `show` emits a DECIMAL escape for
every code point above 127. `\226` is not a JSON escape, so one non-ASCII
annotation anywhere makes `GET /dg` unreadable for the whole library — and
with it every `hets:` comorphism edge, which resolves its node through
`dg()`. {func}`~unicode_logic_kit.hets.repair_haskell_json` recovers it:

```python
import json
from unicode_logic_kit.hets import repair_haskell_json

body = (
    '{"DGraph": {"DGNode": [{"name": "oeo", "Declarations": [], "Axioms": ['
    '{"name": "Ax1", "Axiom": "AnnotationAssertion( obo:IAO_0000112 '
    'obo:BFO_0000001 \\"Verdi\\226\\128\\153s Requiem\\"@en )"}]}]}}')

try:
    json.loads(body)
except json.JSONDecodeError as exc:
    print("json.loads:", exc)

repair = repair_haskell_json(body)
print(repair.summary())
graph = json.loads(repair.text)
print(graph["DGraph"]["DGNode"][0]["Axioms"][0]["Axiom"])
```

```text
json.loads: Invalid \escape: line 1 column 157 (char 156)
3 decimal escape(s) in 1 run(s), 0 \& separator(s), 0 mnemonic escape(s)
AnnotationAssertion( obo:IAO_0000112 obo:BFO_0000001 "Verdi’s Requiem"@en )
```

This is lossless recovery of a KNOWN emitter, not an approximation: GHC's
`showLitChar` is a finite, enumerable function, and exactly five of its
outputs are not also JSON escapes (the decimal runs, the empty-string
separator `\&`, the three-letter mnemonics, `\a` and `\v`). On a real
8,345,206-character development graph the census is 897 decimal escapes in
389 runs plus 7 `\&`, every one of the 389 runs decodes as strict UTF-8, and
the repaired body loads as 13032 axioms over 2099 declarations.

Two things it deliberately does NOT do. It never makes invalid JSON valid by
guessing — a backslash outside a string literal, or an escape it does not
recognise, is copied verbatim so `json.loads` raises as before — and
{meth}`~unicode_logic_kit.hets.HetsClient.dg` calls it only AFTER `json.loads`
has already failed, so a body the standard library accepts is never touched
at all. {meth}`~unicode_logic_kit.hets.HetsClient.dg_raw` gives you the body
untouched when you want to look yourself.

**`GET /theory` does not return a TPTP problem.** For a TPTP comorphism HETS
prefixes its output with a DOL `logic TPTP.FOF` line and a CASL
`%{ ... }%` block carrying its own signature listing. TPTP has exactly two
comment forms (`%` to end of line, `/* ... */`), so `parse_tptp` refuses this
text — by name, pointing at the stripper, rather than learning CASL's block
comment. That refusal is the point: a reader taught `%{ ... }%` would accept
a CASL theory, treat its entire body as a comment, and answer with an EMPTY
formula list.

```python
from unicode_logic_kit.fol.tptp_input import parse_tptp
from unicode_logic_kit.hets import strip_hets_theory_header

theory = """logic TPTP.FOF

%{

predicates:  pred_p: $i > $o

}%

fof(ax_ax1, axiom, ! [VAR_X]: (pred_p(VAR_X) => sort_Thing(VAR_X))).
"""

header, body = strip_hets_theory_header(theory)
print(header.splitlines()[0], "...", len(header.splitlines()), "lines")
print([f.name for f in parse_tptp(body)])

try:
    parse_tptp(theory)
except Exception as exc:
    print(type(exc).__name__)
```

```text
logic TPTP.FOF ... 7 lines
['ax_ax1']
TptpParsingError
```

The split is structural, never `text[text.index("fof("):]`: a blind cut would
swallow a HETS `*** Error` body whole, and a symbol ending in `_fof` inside
the signature block would move the cut point. Measured on the real
1,554,903-character rendering, the header is 187,689 characters (2267 lines)
and the remainder is byte-identical to the file `hets-server -o tptp` writes
— so the REST route and the command-line route deliver the same text.
{meth}`~unicode_logic_kit.hets.HetsClient.theory_tptp` does the fetch and the
strip in one call and refuses a CASL body by name.

Note one limit of reading TPTP back as kit formulas, whatever the source:
this kit's VARIABLE terminal is one term-valued letter followed by digits, and
the reader lower-cases a TPTP variable to get a kit one, so HETS' `VAR_gn_x1`
becomes `var_gn_x1` — a formula that PRINTS but does not re-parse. Use the
AST route for imported TPTP (`TptpFormula.formula` goes straight to
`api.prove`, `to_z3` and `to_tptp`); the limit is documented with its
siblings in `tests/test_printed_text_reads_back.py`.

**A TPTP symbol does not say which class it is.** HETS mangles an entity's
printed name into `pred_`/`op_`/`sort_` plus `_u` for every character outside
`[A-Za-z0-9_]`, so a real class arrives as
`pred_https_u_u_uopenenergyplatform_uorg_uontology_uoeo_uOEO_00000072`.
{func}`~unicode_logic_kit.hets.hets_symbol_table` joins that back onto the IRI
and the `rdfs:label`, and {func}`~unicode_logic_kit.hets.untranslated_axioms`
names the axioms the translation dropped. Both are pure functions over a
`/dg` dict and a TPTP string — no server needed:

```python
from unicode_logic_kit.hets import (
    hets_prefixes, hets_symbol_table, untranslated_axioms)

dg = {"DGraph": {"DGNode": [{
    "name": "oeo",
    "Declarations": [
        {"kind": "Class", "name": "BFO_0000001", "iri": "obo:BFO_0000001"},
        {"kind": "AnnotationProperty", "name": "IAO_0000112",
         "iri": "obo:IAO_0000112"},
    ],
    "Axioms": [
        {"name": "Ax1", "Axiom": "SubClassOf( obo:BFO_0000001 owl:Thing )"},
        {"name": "Ax2", "Axiom": 'AnnotationAssertion( rdfs:label '
                                 'obo:BFO_0000001 "entity"@en )'},
        {"name": "Ax3", "Axiom": "DataPropertyRange( obo:hasValue "
                                 "rdfs:Literal )"},
    ],
}]}}
tptp = "fof(ax_ax1, axiom, ! [VAR_X]: pred_obo_uBFO_0000001(VAR_X)).\n"

prefixes = hets_prefixes("     Prefix: obo: <http://purl.obolibrary.org/obo/>")
table = hets_symbol_table(dg, tptp, prefixes=prefixes)
for row in table.symbols:
    print(row.kind, row.tptp_name, row.in_tptp, row.iri)
print([r.name for r in table.by_label("entity")])
print([(a.name, a.kind) for a in untranslated_axioms(dg, tptp)])
```

```text
Class pred_obo_uBFO_0000001 True http://purl.obolibrary.org/obo/BFO_0000001
AnnotationProperty pred_obo_uIAO_0000112 False http://purl.obolibrary.org/obo/IAO_0000112
['BFO_0000001']
[('Ax3', 'DataPropertyRange')]
```

`in_tptp=False` is a reported FACT, not an error: an annotation property
carries no logical content under OWL 2's direct semantics, so a comorphism
legitimately never emits one. On the real ontology 2026 of 2099 declarations
have a symbol and 73 do not (68 annotation properties and 5 object properties
used in no logical axiom), with zero mangling collisions; a collision would
make the table refuse to BUILD rather than keep whichever declaration came
last. `unmapped_tptp` is the other direction — the 21 symbols with no
declaration behind them (CASL numerals, `pred_Thing`, HETS' sort predicates).

`untranslated_axioms` excludes the OWL 2 annotation axiom kinds by default,
which is a specification fact rather than a heuristic. On the real pair that
leaves exactly two axioms — the two `DataPropertyRange(d rdfs:Literal)`
assertions — out of 13032, derived from the `Ax<N>` ↔ `ax_ax<N>` name
correspondence. The requesting project reached the same two by diffing
against a hand-reduced ontology, a completely different method; two
independent derivations agreeing is what makes the number trustworthy.

### The lossy route: `hets.owl_to_tptp`

HETS refuses a comorphism whose source sublogic does not cover the theory,
and `GET /theory` then answers HTTP 422 — now a typed, branchable
{class}`~unicode_logic_kit.hets.HetsSublogicError` carrying HETS' three
strings (`comorphism`, `expected`, `found`) instead of prose to grep. On a
real ontology that refusal can hang on very little: two
`DataPropertyRange(d rdfs:Literal)` axioms out of 4041 push all of OEO
2.13.0 out of `OWL22CASL`'s sublogic. `GET /translations` is no help — for
the same library it answers a well-formed list with ZERO entries, HTTP 200,
no reason at all, which is why that method now raises
{class}`~unicode_logic_kit.hets.HetsNoTranslationsError` naming the endpoint
where the reason does live rather than returning `[]`.

`hets-server`'s `-Y` flag translates anyway and drops what it cannot
express. It exists ONLY on the command line, so
{func}`~unicode_logic_kit.hets.owl_to_tptp` is the one part of this subpackage
that `docker exec`s instead of speaking HTTP:

```python
# doctest: +SKIP  — needs Docker and a running spechub2/hets container
from unicode_logic_kit.hets import HetsClient, owl_to_tptp
from unicode_logic_kit.fol.tptp_input import parse_tptp

result = owl_to_tptp("oeo.owl", container="ufk-hets-oeo",
                     client=HetsClient("http://localhost:8000"))
print(result.lossy, result.comorphism)
print(result.sublogic_mismatch.expected, "<-", result.sublogic_mismatch.found)
print(len(parse_tptp(result.tptp)), "formulas")
for axiom in result.omitted_axioms:
    print("dropped:", axiom.name, axiom.owl)
```

```text
True OWL22CASL;CASL2TPTP_FOF
NP-sROIQux-D|-| <- NP-sROIQ-D|Literal|dateTime|decimal|integer|string|
4291 formulas
dropped: Ax4027 DataPropertyRange( .../OEO_00390094 rdfs:Literal )
dropped: Ax4030 DataPropertyRange( .../OEO_00390098 rdfs:Literal )
```

Three design decisions are worth knowing about before you depend on it.

`lossy=True` is the default, as requested — but it runs the NON-lossy
translation first. `-Y` is silent: it prints only `Translated using
comorphism ...`, and the sublogic warning appears solely in the run without
it. A single `-Y` run would therefore hand you a quietly smaller theory with
nothing to indicate it, so the probe run is what makes
`sublogic_mismatch` non-`None` exactly when `-Y` was actually needed. The
cost is two HETS runs — measured 4.6 s + 4.4 s for a 3.85 MB ontology, so
about 9 s rather than 4.5 s. On a much larger ontology that doubling is the
dominant cost of the call, and the way to avoid it is to pass `client=` and
let `untranslated_axioms` compute the loss from `/dg` against the TPTP
instead, which is both exact and free. `lossy=False` does one run and raises
`HetsSublogicError`.

`symbols` and `omitted_axioms` are `None` without a `client=`, never an
empty table: both need `/dg`, and `()` has to keep meaning "computed, and
nothing was omitted".

EXIT 0 is not success, so it is never the test. Both non-lossy runs exit 0
and keep the UNTRANSLATED theory, writing no `.tptp` at all; the `;`
spelling of a composition — which is how HETS prints it in its own messages —
exits 0 with `Cannot find logic comorphism`. Success is the conjunction of a
`.tptp` appearing and the console containing `Translated using comorphism`,
and each of the other outcomes is a refusal that names itself. The
`SoftFOL` target is refused up front: HETS 0.108.0 aborts on CASL numerals,
which any ontology with a `DataHasValue` numeral produces.

One thing `owl_to_tptp` will NOT do is normalise your ontology. HETS rejects
an `AnnotationAssertion` whose subject is undeclared, which OWL 2 does not
require; repairing that would mean choosing an entity KIND for an
annotation-only IRI (a guess that puts a symbol into the logical signature),
growing an RDF/XML writer this kit does not have, and deleting annotations.
So it detects the pattern, collects every undeclared IRI and raises
{class}`~unicode_logic_kit.hets.HetsOwlNormalizationError` listing them with
both remedies — the semantic choice stays with the ontology's owner.

Finally, the reason all of this reports so carefully: a HETS translation is
the SECOND FOL image of an ontology, to be compared against
{func}`~unicode_logic_kit.dl.tbox_to_fol` / {func}`~unicode_logic_kit.dl.kb_to_fol`
and `api.prove`. A comparison is worth nothing if either side is presented as
more complete than it is. HETS' own translation defects are listed in
{mod}`unicode_logic_kit.hets.symbols`' docstring so a disagreement is
attributable rather than blamed on this kit — among them an n-ary
`DifferentIndividuals` expanded to fewer than all pairs, a
`DataPropertyRange` rendered with its existential over the implication, both
facets of a `DatatypeRestriction` collapsing to one predicate, and 19
duplicated formula names (so never key formulas by name).

## Inductive logic programming: the other direction

Reading a learner's answer is half the loop. {mod}`unicode_logic_kit.ilp` writes
the learner's *question* — the background knowledge, examples and language bias
an ILP system (Popper, Aleph, Metagol) reads — from the very same
{class}`~unicode_logic_kit.semantics.structures.FiniteStructure` objects the model
checker evaluates against:

```text
structure ──IlpTask──▶ Prolog task ──learner──▶ clause
    ──clause_to_formula──▶ kit formula ──model checker──▶ verdicts
```

Nothing runs a learner: Popper needs SWI-Prolog and, from v4, `janus_swi`, which
is not a dependency the kit takes on for a file format. It writes `bk.pl`,
`exs.pl` and `bias.pl`, and reads the text a learner prints.

```python
from unicode_logic_kit.semantics import FiniteStructure
from unicode_logic_kit.ilp import IlpTask, Example

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

### Aleph: the other file layout

Popper's three files (`bk.pl`/`exs.pl`/`bias.pl`) are one convention; Aleph
reads a genuinely different one — `modeh`/`modeb` mode declarations plus
`determination/2` instead of `head_pred`/`body_pred`, positive and negative
examples in *separate* files (`.f`/`.n`) as bare atoms rather than one file
wrapped in `pos(...)`/`neg(...)`, and background knowledge sharing a file
with the bias rather than living apart from it. `IlpTask.write_aleph`
produces that layout from the exact same task — the facts, the individual
naming, every encoding check are unchanged; only the bias and example
*renderings* differ:

```python
print(task.aleph_bias_text(), end="")
# → :- modeh(1, amide(+example)).
# → :- modeb(*, atom_in(+example,-individual)).
# → :- modeb(*, bDOUBLE(+individual,-individual)).
# → :- modeb(*, bSINGLE(+individual,-individual)).
# → :- modeb(*, c(+individual)).
# → :- modeb(*, n(+individual)).
# → :- modeb(*, o(+individual)).
# → :- determination(amide/1, atom_in/2).
# → :- determination(amide/1, bDOUBLE/2).
# → :- determination(amide/1, bSINGLE/2).
# → :- determination(amide/1, c/1).
# → :- determination(amide/1, n/1).
# → :- determination(amide/1, o/1).
# → % max_vars(6) and max_clauses(1) have no single-clause Aleph equivalent: ...
# → :- set(clauselength, 8).
print(task.aleph_examples_text(True), end="")
# → amide(m1).
print(task.aleph_examples_text(False), end="")
# → amide(m2).
```

`task.write_aleph(directory)` puts these into `task.b` (background facts and
bias, concatenated — Aleph's own convention), `task.f` and `task.n`.

The mode line for every body predicate follows one fixed, documented
convention rather than anything inferred: `FiniteStructure` carries no
per-argument sort to derive a real mode pattern from, so the first argument
is always bound (`+individual`) and every remaining argument is free
(`-individual`) — exactly right for a functional fact like `c(X)`, merely
usable for a genuinely symmetric one like `bDOUBLE(X, Y)`. `max_body`
translates to Aleph's `clauselength` bound; `max_vars` and `max_clauses` have
no single-clause equivalent (Aleph's clause count comes from `induce`'s own
covering loop, not from a bias file) and are named in a comment rather than
silently dropped.

This was checked against a real Aleph — the SWI-Prolog `aleph` pack's
`aleph_orig.pl` — not just by eye: the emitted `.b`/`.f`/`.n` triple loads
with no `example/1` or `individual/1` type fact anywhere (`+example` and
`+individual` bind purely from resolving the actual background predicates
during saturation, never from enumerating a declared type), and `induce`
learns the intended target clause from it. `tests/test_ilp_aleph.py` carries
that check as a test, skip-gated on Aleph being installed.

### Reading the clause back

```python
from unicode_logic_kit.ilp import clause_to_formula

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
from unicode_logic_kit.ilp import clause_to_formula, IlpEncodingError

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
from unicode_logic_kit.semantics import FiniteStructure
from unicode_logic_kit.ilp import Example, IlpTask, check_separation

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
