# Natural-language translation targets

When a natural-language front-end (for example a CCG parser producing logical forms)
translates English into logic, a handful of constructions have no clean home in plain
first-order syntax: cardinal determiners (*at least three*), degree comparatives (*more
water*, *taller*), counting comparisons (*more votes than*), reportative and
desiderative attitudes (*says that*, *wants to*), and concessive coordination
(*whereas*, *although*). The kit provides determinate, **round-trippable** AST nodes for
each, so a pipeline can *emit* them as faithful logical forms (translation only — these
are representations, not new reasoning back-ends, though several do plug into the
existing evaluators).

All of these are reached through `MSFLParser`: `Count`, `Measure`, `Cardinality`, and
`Contrast` parse with the **default** parser; the attitude operators `Says`/`Wants` are
**modal** (`MSFLParser(modal=True)`), like `Knows`/`Believes`.

## Counting quantifier — `Count` (∃≥n / ∃≤n / ∃=n)

`Count` is a cardinality quantifier: *at least*, *at most*, or *exactly* `n` distinct
individuals satisfy the matrix. The bound `n` is carried **symbolically** (a `Number`),
never expanded into single-letter variables, so an arbitrarily large `n` is represented
exactly — `over 500 pages`, `a million`, `180 degrees` all work.

```python
from unicode_fol_kit import MSFLParser
from unicode_fol_kit.fol.nodes import Count

p = MSFLParser()
p.parse("∃≥3 x (R(x) ∧ Q(x))")   # Count(op='ge', n=Number(3), variable=x, formula=…)
p.parse("∃≤2 y P(y)")             # at most 2
p.parse("∃=4 z S(z)")             # exactly 4

big = p.parse("∃≥500 x Page(x)")
big.n.value                       # → 500   (not clamped to a plain ∃)
```

The bound variable is read off the node, and the count itself binds it — `free_variables`
excludes it but keeps any free variable of the matrix:

```python
from unicode_fol_kit.fol.nodes import free_variables

c = p.parse("∃≥3 x R(x, y)")
c.op, c.n.value, c.variable.name        # → ('ge', 3, 'x')
sorted(v.name for v in free_variables(c))   # → ['y']   (x is bound, y stays free)
```

The two boundary cases are first-class. `∃=0` is "no such individual" and `∃≥0` is
vacuously true on a non-empty domain — both stay symbolic `Count` nodes, not collapsed
forms:

```python
p.parse("∃=0 x P(x)").op            # → 'eq'   (a genuine Count, n=0)
is_valid(p.parse("(∃=0 x P(x)) ↔ ¬∃x P(x)"))     # True
is_valid(p.parse("(∃=0 x P(x)) ↔ ∀x ¬P(x)"))     # True
is_valid(p.parse("∃≥0 x P(x)"))                  # True  (≥ 0 is always satisfiable)
```

Coordinated per-noun counts (*more than 3 bedrooms and at least 2 baths*) compose as a
conjunction of `Count`s — each binds its own variable independently:

```python
both = p.parse("(∃≥4 x Bedroom(x)) ∧ (∃≥2 y Bath(y))")
# And(Count(ge,4,…), Count(ge,2,…))
type(both.left).__name__, both.left.n.value, both.right.n.value   # → ('Count', 4, 2)
```

`Count` round-trips through Unicode and JSON, and substitution into the matrix is
capture-avoiding:

```python
import json
from unicode_fol_kit.fol.nodes import Node

c.to_unicode_str()                       # → '∃≥3 x R(x, y)'
p.parse(c.to_unicode_str()) == c         # True   (Unicode round-trip)
Node.from_dict(json.loads(json.dumps(c.to_dict()))) == c   # True   (JSON round-trip)
```

It is first-order expressible, so the exporters lower it to the standard
distinct-witnesses encoding, and the usual cardinality entailments all check out:

```python
from unicode_fol_kit import is_valid

# ∃≥1 x P(x) is just ∃x P(x); ∃≥2 entails ∃≥1; ∃=1 is the classic "exactly one".
is_valid(p.parse("∃≥2 x P(x) → ∃≥1 x P(x)"))                       # True
is_valid(p.parse("∃=1 x P(x) ↔ ∃x (P(x) ∧ ∀y (P(y) → x = y))"))   # True
is_valid(p.parse("∃≥3 x P(x) → ∃≥2 x P(x)"))                       # True  (monotone up)
is_valid(p.parse("∃≤2 x P(x) → ∃≤3 x P(x)"))                       # True  (monotone up)
is_valid(p.parse("∃=2 x P(x) → (∃≥2 x P(x) ∧ ∃≤2 x P(x))"))        # True  (= is ≥ ∧ ≤)

p.parse("∃≥2 x P(x)").to_tptp()   # nested ?[X] existentials with distinctness
p.parse("∃≤1 x P(x)").to_tptp()   # ∃≤n lowers to ¬(∃≥n+1)
```

`Count` also verbalizes with `to_english`:

```python
from unicode_fol_kit import to_english

to_english(p.parse("∃≥3 x (R(x) ∧ Q(x))"))
# → 'there are at least 3 x such that x is r and x is q'
```

## Degree term — `Measure` (μ)

`Measure` is a measure-function term `μ(entity, dimension)` — the degree to which an
entity has a gradable property — so a bare comparative gets a determinate argument
instead of a thin relational paraphrase. Compare degrees with `>` / `<`:

```python
from unicode_fol_kit.fol.nodes import Measure

cmp = p.parse("μ(x, height) > μ(y, height)")   # Atom('>', [Measure(x, height), Measure(y, height)])
isinstance(cmp.args[0], Measure)               # True
cmp.to_prover9()                               # uses the function measure(x, height)
```

## Cardinality term — `Cardinality` (|{v : φ}|)

`Cardinality` is the set-cardinality term `|{v : φ}|` — the number of individuals `v`
that satisfy `φ` — for faithful counting comparisons:

```python
from unicode_fol_kit.fol.nodes import Cardinality

votes = p.parse("|{v : Votes(x, v)}| > |{v : Votes(y, v)}|")   # "x got more votes than y"
isinstance(votes.args[0], Cardinality)                          # True
```

Any comparison or equality works on the two cardinality terms — *as many … as*
(`=`), *at least as many* (`≥`), *fewer* (`<`):

```python
ge  = p.parse("|{v : Votes(x, v)}| ≥ |{v : Votes(y, v)}|")   # "at least as many as"
ge.predicate                                                  # → '≥'
same = p.parse("|{w : P(w)}| = |{w : Q(w)}|")                 # "as many P as Q"
same.predicate                                                # → '='
```

It binds its variable (so the outer `x`, `y` stay free) and round-trips:

```python
sorted(n.name for n in free_variables(votes))   # → ['x', 'y']   (v is bound away)
p.parse(votes.to_unicode_str()) == votes        # True
```

Set cardinality is a *second-order* notion, so `Cardinality` has **no** first-order
export — `to_z3` / `to_prover9` / `to_tptp` raise `NotImplementedError`; keep it at the
AST level, or use a `Count` quantifier when a fixed numeric bound suffices:

```python
votes.to_prover9()   # raises NotImplementedError — cardinality is not first-order
```

## Concessive connective — `Contrast` (Ⓒ)

`Contrast` (`P Ⓒ Q`) renders *whereas* / *although* / *but*. Concession is a discourse
relation, not a truth-functional one, so `Contrast` is truth-functionally identical to
`∧` — but kept as a distinct node so the contrast survives translation:

```python
from unicode_fol_kit.fol.nodes import Contrast

c = p.parse("Sunny(today) Ⓒ Cold(today)")   # Contrast(...)
is_valid(p.parse("(P Ⓒ Q) ↔ (P ∧ Q)"))      # True — same truth conditions as ∧
```

Like `∧` / `∨` / `⊕`, it sits in the no-mixing same-level group, so mixing it with
another connective needs parentheses: `(P Ⓒ Q) ∧ R`.

## Attitude operators — `Says` / `Wants`

`Says` (`Say_a φ`, *a asserts that φ*) and `Wants` (`Want_a φ`, *a wants it to be that
φ*) are modal `agent_prefix` operators alongside `Knows`/`Believes`. The agent is a
β-bindable term, so a bound agent works (`∀x (Speaker(x) → Say_x φ)`).

```python
m = MSFLParser(modal=True)
m.parse("Say_alice Rain")                       # Says(agent=alice, formula=Rain)
m.parse("Want_bob Win(bob)")                    # Wants(agent=bob, …)
m.parse("∀x (Speaker(x) → Say_x Honest(x))")    # bound agent x
```

Each is a minimal normal modality **K** over its own per-agent accessibility relation
(`"Say:"+a`, `"Want:"+a`), with **no** frame conditions. The point of distinguishing
them from `Knows`/`Believes` is exactly what that buys:

- `Says` is **non-factive** (`Say_a φ ⊭ φ` — an assertion can be false) and
  **non-doxastic** (`Say_a φ ⊭ Believes_a φ`).
- `Wants` is **non-veridical** (`Want_a φ ⊭ φ` — wanting does not make it so).

```python
from unicode_fol_kit import is_modal_valid

is_modal_valid(m.parse("(Say_a P) → P"))    # False  (non-factive)
is_modal_valid(m.parse("(Want_a P) → P"))   # False  (non-veridical)
is_modal_valid(m.parse("(Say_a P) → (B_a P)"))   # False  (non-doxastic: saying ≠ believing)
# but K (distribution) holds for both — they are normal modal operators:
is_modal_valid(m.parse("(Say_a (P → Q)) → ((Say_a P) → (Say_a Q))"))    # True
is_modal_valid(m.parse("(Want_a (P → Q)) → ((Want_a P) → (Want_a Q))")) # True
```

The agent is a structural term, so a quantifier can bind it — *every speaker says they
are honest* is a single closed formula with a bound `Say_x`, and it round-trips and
verbalizes:

```python
from unicode_fol_kit import to_english

ba = m.parse("∀x (Speaker(x) → Say_x Honest(x))")     # bound agent x under ∀
m.parse(ba.to_unicode_str()) == ba                    # True
to_english(ba)
# → 'for every x, if x is speaker, then agent x says that x is honest'

to_english(m.parse("Say_alice Rain"))      # → 'agent alice says that Rain'
to_english(m.parse("Want_bob Win(bob)"))   # → 'agent bob wants it to be that bob is win'
```

They plug into the Kripke evaluator and the modal tableau, verbalize with `to_english`,
and (being modal) reject the first-order exporters — round-trip them through Unicode or
JSON, as with the other modal operators.

## Reading Prover9 files

The Prover9 reader complements `load_tptp` and `load_smtlib`: `load_prover9(path)` and
`parse_prover9_problem(text)` read a whole Prover9/LADR input file — `set`/`clear`/
`assign` directives (skipped), `formulas(LIST). … end_of_list.` blocks, and bare
top-level formulas — into `Prover9Formula(role, formula)` records, with the list name as
each formula's role. See {doc}`transforms` for the full import/export reference.

`parse_prover9_problem` takes the file text directly. Directives are dropped, `%` comments
are ignored, and each formula's `role` is the name of the `formulas(...)` list it came
from:

```python
from unicode_fol_kit import parse_prover9_problem

src = """
set(prolog_style_variables).
assign(max_seconds, 30).
formulas(assumptions).
  all x (man(x) -> mortal(x)).   % a universally quantified implication
  man(socrates).
end_of_list.
formulas(goals).
  mortal(socrates).
end_of_list.
"""
problem = parse_prover9_problem(src)
[(f.role, f.formula.to_unicode_str()) for f in problem]
# → [('assumptions', '∀x (man(x) → mortal(x))'),
#    ('assumptions', 'man(socrates)'),
#    ('goals', 'mortal(socrates)')]
type(problem[0]).__name__   # → 'Prover9Formula'
```

A formula written outside any `formulas(...)` block (a bare top-level formula) is kept
with an empty role `''`:

```python
loose = parse_prover9_problem("P(a) | Q(a).")
loose[0].role, loose[0].formula.to_unicode_str()   # → ('', 'P(a) ∨ Q(a)')
```

`load_prover9(path)` is the same reader over a file on disk:

```python
import tempfile, os

fd, path = tempfile.mkstemp(suffix=".p9")
os.write(fd, b"formulas(sos).\n  all x (P(x) -> Q(x)).\n  P(a).\nend_of_list.\n")
os.close(fd)

from unicode_fol_kit import load_prover9
[(f.role, f.formula.to_unicode_str()) for f in load_prover9(path)]
# → [('sos', '∀x (P(x) → Q(x))'), ('sos', 'P(a)')]
os.remove(path)
```

## Making imported names re-parseable — `sanitize_names`

A formula imported from TPTP, SMT-LIB, or Prover9 can carry symbol names the AST accepts
but the `MSFLParser` *lexer* does not — IRIs with underscores and mixed case, single-letter
or digit-leading constants, and so on. Rendering such a node with `to_unicode_str` then
yields a string that does **not** re-parse. `sanitize_names(node)` rewrites every symbol to
a token that re-parses to its intended class, returning `(clean_node, mapping)`:

```python
from unicode_fol_kit import sanitize_names
from unicode_fol_kit.fol.nodes import Atom, Constant

# an OWL→FOL import: an IRI predicate over a single-letter constant
raw = Atom("http___example_org_Thing", [Constant("a")])
clean, mapping = sanitize_names(raw)
clean.to_unicode_str()                     # → 'HttpexampleorgThing(c_a)'
p.parse(clean.to_unicode_str()) == clean   # True   (now it round-trips)
```

Predicates become `[A-Z][a-zA-Z0-9]*`, functions a multi-letter lowercase name, and a
single-letter or digit-bearing constant takes the explicit `c_…` form so it does not
collapse to a variable on re-parse. The returned `NameMapping` records every renaming and
`reverse()` recovers the originals:

```python
mapping.predicate    # → {'http___example_org_Thing': 'HttpexampleorgThing'}
mapping.constant     # → {'a': 'c_a'}
mapping.reverse()    # → {'HttpexampleorgThing': 'http___example_org_Thing', 'c_a': 'a'}
```

Already-legal names pass through untouched, so a clean classical formula is unchanged:

```python
f = p.parse("∀x (Human(x) → Mortal(x))")
clean_f, _ = sanitize_names(f)
clean_f == f          # True   (nothing to rewrite)
```

Across a whole problem, reuse one mapping so the same original symbol maps to the same
token in every formula — `sanitize_all` does exactly that with one shared `NameMapping`:

```python
from unicode_fol_kit import sanitize_all

n1 = Atom("http___ex_A", [Constant("x")])
n2 = Atom("http___ex_A", [Constant("y")])      # same IRI predicate, different constant
out, shared = sanitize_all([n1, n2])
[o.to_unicode_str() for o in out]              # → ['HttpexA(c_x)', 'HttpexA(c_y)']
shared.predicate                               # → {'http___ex_A': 'HttpexA'}
```
