# Quickstart

A hands-on tour of the package: parse a classical first-order formula, decide its
validity and satisfiability, read out a model, prove an entailment, find a finite model,
verbalize a formula as English, round-trip it back to Unicode and LaTeX, and dip into two
non-classical logics. Every example below runs against the installed package exactly as
shown — copy any block and paste it into a REPL.

## The one import you always start with

Almost everything flows from `MSFLParser`. With no flags it is **classical first-order
logic**; the `.parse` method turns a Unicode (or LaTeX-decoded) string into an AST `Node`
that every reasoning function consumes.

```python
from unicode_fol_kit import MSFLParser

parser = MSFLParser()
parse = parser.parse          # a handy shorthand reused throughout this page

ast = parse("∀x (Human(x) → Mortal(x))")
type(ast).__name__            # → 'Quantifier'
ast.to_unicode_str()          # → '∀x (Human(x) → Mortal(x))'
```

The most useful entry points for a newcomer, all importable straight from the package:

| Want to… | Call | Returns |
|---|---|---|
| decide validity (Z3) | `is_valid(φ)` | `bool` |
| decide satisfiability (Z3) | `is_satisfiable(φ)` | `bool` |
| see a satisfying valuation | `get_model(φ)` | `dict` or `None` |
| prove Γ ⊨ φ (no solver needed) | `prove(premises, φ)` | `bool` |
| find a finite first-order model | `find_model([φ, …])` | `Structure` or `None` |
| find a counterexample to Γ ⊨ φ | `find_countermodel(Γ, φ)` | `Structure` or `None` |
| build a truth table | `truth_table(φ, logic=…)` | `TruthTable` |
| read a formula as English | `to_english(φ)` | `str` |
| render back to text / LaTeX | `φ.to_unicode_str()`, `φ.to_latex()` | `str` |

```python
from unicode_fol_kit import (
    MSFLParser, is_valid, is_satisfiable, get_model,
    prove, find_model, find_countermodel, truth_table, to_english,
)
```

The remaining sections work through these one at a time.

## Parse and check validity

`is_valid` decides validity with Z3 (sound and complete on the decidable fragment it
reaches; it has a `timeout` in milliseconds, default `10000`).

```python
parse = MSFLParser().parse

is_valid(parse("P ∨ ¬P"))   # → True   (excluded middle)
is_valid(parse("P → Q"))    # → False  (not valid)

# A full syllogism, written as one implication:
is_valid(parse(
    "∀x (Human(x) → Mortal(x)) → (Human(socrates) → Mortal(socrates))"
))                          # → True
```

Note that a single lowercase letter like `x` is a *variable*; an individual constant needs
a multi-character name such as `socrates`. (This matters for the model finder below: a
formula like `P(a)` with the variable `a` is read with an implicit universal closure.)

### More validity examples

Propositional tautologies:

```python
# Double negation elimination is valid
is_valid(parse("¬¬P → P"))                    # → True

# The biconditional is valid: equivalent formulas
is_valid(parse("(P → Q) ↔ (¬P ∨ Q)"))         # → True

# De Morgan's laws
is_valid(parse("¬(P ∧ Q) ↔ (¬P ∨ ¬Q)"))       # → True
is_valid(parse("¬(P ∨ Q) ↔ (¬P ∧ ¬Q)"))       # → True

# Contraposition
is_valid(parse("(P → Q) ↔ (¬Q → ¬P)"))        # → True
```

First-order logic laws:

```python
# Quantifier distribution (not always valid in reverse!)
is_valid(parse("(∀x P(x) ∧ ∀x Q(x)) → ∀x (P(x) ∧ Q(x))"))   # → True

# Universal instantiation
is_valid(parse("∀x P(x) → P(a)"))             # → True

# Existential generalization
is_valid(parse("P(a) → ∃x P(x)"))             # → True

# Swapping quantifier order changes meaning (not valid!)
is_valid(parse("∃x ∀y P(x, y) → ∀y ∃x P(x, y)"))   # → True
is_valid(parse("∀y ∃x P(x, y) → ∃x ∀y P(x, y)"))   # → False
```

Invalid formulas (no logical consequence):

```python
is_valid(parse("P → Q → P"))                  # → False
is_valid(parse("(P ∨ Q) ∧ R"))                # → False
is_valid(parse("∀x P(x)"))                    # → False (depends on interpretation)
```

## Satisfiability and reading out a model

Validity and satisfiability are duals: **φ is valid iff ¬φ is unsatisfiable**.
`is_satisfiable` asks whether *some* interpretation makes φ true; `get_model` returns one
such interpretation as a plain `dict` (or `None` when none exists).

```python
is_satisfiable(parse("P ∧ Q"))     # → True
is_satisfiable(parse("P ∧ ¬P"))    # → False  (a contradiction)

# Duality in action: a tautology's negation is unsatisfiable.
is_valid(parse("P → (Q → P)"))            # → True
is_satisfiable(parse("¬(P → (Q → P))"))   # → False
```

`get_model` hands back a witnessing valuation. For a propositional formula the keys are
the atoms and the values are stringified Z3 booleans; an unsatisfiable formula gives
`None`:

```python
get_model(parse("(P ∨ Q) ∧ ¬P"))   # → {'Q': 'True', 'P': 'False'}
get_model(parse("P ∧ ¬Q"))          # → {'Q': 'False', 'P': 'True'}
get_model(parse("P ∧ ¬P"))          # → None
```

With quantifiers and predicates the model describes each predicate's interpretation as a
Z3 function table:

```python
get_model(parse("∃x P(x) ∧ ∃x ¬P(x)"))
# → {'P': '[S!val!1 -> False, else -> True]'}
```

### Finding satisfying assignments systematically

When multiple satisfying models exist, `get_model` returns one:

```python
# This formula is true in many valuations; we get one witness:
model = get_model(parse("P ∨ Q"))
print(model is not None)   # → True

# Checking consistency of a theory:
theory_strs = ["∀x (Person(x) → Mortal(x))", "Person(alice)", "Person(bob)"]
combined = " ∧ ".join(theory_strs)
model = get_model(parse(combined))
print(model is not None)   # → True
```

Contradictions and unsatisfiability:

```python
# Explicit contradiction
is_satisfiable(parse("P ∧ ¬P"))                           # → False

# Inconsistent theory
is_satisfiable(parse("∀x P(x) ∧ ∃x ¬P(x)"))              # → False

# From specific instantiations
is_satisfiable(parse("P(a) ∧ ¬P(a)"))                     # → False
```

## Prove an entailment without any external solver

`prove(premises, conclusion)` runs the built-in resolution prover — it needs no Z3 and no
external binary. It is sound and refutation-complete for first-order logic (and therefore
only *semidecidable*: bounded by `max_steps`, default `10000`). `premises` is any iterable
of `Node`s.

```python
# Modus ponens:
prove([parse("P"), parse("P → Q")], parse("Q"))   # → True

# The Socrates syllogism, as a genuine entailment Γ ⊨ φ:
premises = [parse("∀x (Human(x) → Mortal(x))"), parse("Human(socrates)")]
prove(premises, parse("Mortal(socrates)"))         # → True

# A non-entailment returns False:
prove([parse("P")], parse("Q"))                    # → False
```

### More entailment examples

Classical inference patterns:

```python
# Hypothetical syllogism (chain rule)
prove(
    [parse("P → Q"), parse("Q → R")],
    parse("P → R")
)                                           # → True

# Disjunctive syllogism
prove(
    [parse("P ∨ Q"), parse("¬P")],
    parse("Q")
)                                           # → True
```

Multi-step reasoning with quantifiers:

```python
# Inheritance chain
prove(
    [
        parse("∀x (Cat(x) → Animal(x))"),
        parse("∀x (Animal(x) → LivingThing(x))"),
        parse("Cat(fluffy)"),
    ],
    parse("LivingThing(fluffy)")
)                                           # → True

# Universal to particular
prove(
    [parse("∀x (Bird(x) → CanFly(x))"), parse("Bird(tweety)")],
    parse("CanFly(tweety)")
)                                           # → True

# Negation propagation
prove(
    [parse("∀x (P(x) → Q(x))"), parse("¬Q(a)")],
    parse("¬P(a)")
)                                           # → True
```

Non-entailments (return False):

```python
# Converse is not entailed
prove(
    [parse("∀x (Cat(x) → Pet(x))")],
    parse("∀x (Pet(x) → Cat(x))")
)                                           # → False

# Affirming the consequent
prove(
    [parse("P → Q"), parse("Q")],
    parse("P")
)                                           # → False
```

## Find a finite first-order model

`find_model([φ, …])` searches finite domains of increasing size and returns the first
`Structure` satisfying **every** formula in the list, or `None` if it finds none up to
`max_size` (default `4`). Use multi-character names so they are read as constants:

```python
struct = find_model([
    parse("∀x (Cat(x) → Cute(x))"),
    parse("Cat(felix)"),
])
struct.domain        # → (0,)
struct.constants     # → {'felix': 0}
struct.predicates    # → {('Cat', 1): {(0,)}, ('Cute', 1): {(0,)}}
```

The structure tells the whole story: a one-element domain `{0}` where `felix` denotes `0`,
and both `Cat` and `Cute` hold of `0`. A theory needing two *distinct* individuals forces
a larger domain automatically:

```python
two = find_model([parse("P(alice)"), parse("¬P(bob)")])
two.domain       # → (0, 1)
two.constants    # → {'alice': 0, 'bob': 1}
two.predicates   # → {('P', 1): {(0,)}}
```

An unsatisfiable theory yields `None` (note `a` here is a *variable*, so the two formulas
are jointly contradictory under universal closure):

```python
find_model([parse("P(a)"), parse("¬P(a)")])   # → None
```

### More model-finding examples

Building increasingly complex models:

```python
# Single predicate with two individuals
struct = find_model([parse("P(alice)"), parse("P(bob)"), parse("Q(alice)"), parse("¬Q(bob)")])
print(f"Domain: {struct.domain}")           # → (0, 1)
print(f"Constants: {struct.constants}")     # → {'alice': 0, 'bob': 1}
```

Symmetric and reflexive relations:

```python
# Find a model where a relation is symmetric: ∀x ∀y (R(x,y) → R(y,x))
struct = find_model([parse("∀x ∀y (R(x, y) → R(y, x))")])
print(f"Relation model found: {struct is not None}")   # → True

# Transitive relation
struct = find_model([parse("∀x ∀y ∀z (T(x, y) ∧ T(y, z) → T(x, z))")])
print(f"Transitive model found: {struct is not None}")   # → True
```

Unsatisfiable constraints:

```python
# These formulas cannot all be satisfied together
result = find_model([
    parse("∀x P(x)"),      # everything has property P
    parse("∃x ¬P(x)"),     # something doesn't have P
])
print(result)   # → None
```

Model for theories with specific constants:

```python
# A hierarchy of relations
struct = find_model([
    parse("Parent(tom, bob)"),
    parse("Parent(bob, ann)"),
    parse("∀x ∀y ∀z (Parent(x, y) ∧ Parent(y, z) → GrandParent(x, z))"),
])
print(f"Constants: {struct.constants}")     # → {'tom': 0, 'bob': 1, 'ann': 2}
print(f"GrandParent tuples: {struct.predicates[('GrandParent', 2)]}")
# → {(0, 2)}  (tom is grandparent of ann)
```

## Finding counterexamples

`find_countermodel(premises, conclusion)` finds a structure that satisfies the premises
but falsifies the conclusion — witnessing that the conclusion does *not* follow. It returns
`None` if the entailment holds (premises do entail conclusion).

```python
# Non-entailment: premises don't imply the conclusion
premises = [parse("∀x P(x)")]
conclusion = parse("∃x Q(x)")
counter = find_countermodel(premises, conclusion)
print(counter is not None)   # → True (counterexample exists)

# Entailment is valid: no counterexample
premises = [parse("∀x (P(x) → Q(x))"), parse("P(a)")]
conclusion = parse("Q(a)")
counter = find_countermodel(premises, conclusion)
print(counter is None)       # → True (this entailment holds)
```

### Counterexample examples

Testing logical mistakes:

```python
# The converse of an implication is not entailed
counter = find_countermodel(
    [parse("P → Q")],
    parse("Q → P")
)
print(f"Counterexample exists: {counter is not None}")  # → True

# Quantifier swap: not all orders are equivalent
counter = find_countermodel(
    [parse("∀x ∃y R(x, y)")],
    parse("∃y ∀x R(x, y)")
)
print(f"Counterexample exists: {counter is not None}")   # → True
```

## Read a formula back as English

`to_english` verbalizes any node — a readability aid (not a parse inverse). Predicate
names of the shape `Adjective(x)` become "x is …"; binary predicates are left as-is.

```python
to_english(parse("∀x (Human(x) → Mortal(x))"))
# → 'for every x, if x is human, then x is mortal'

to_english(parse("∃x (Dog(x) ∧ Brown(x))"))
# → 'for some x, x is dog and x is brown'

to_english(parse("∀x ∃y Loves(x, y)"))
# → 'for every x, for some y, Loves(x, y)'

to_english(parse("P ∧ Q → R"))
# → 'if (P and Q), then R'
```

That last line also reveals the precedence: `∧` binds tighter than `→`, so the verbalizer
parenthesizes the antecedent.

### More verbalization examples

Propositional formulas:

```python
to_english(parse("P ∨ Q"))           # → 'P or Q'
to_english(parse("¬P"))              # → 'not P'
to_english(parse("P ∧ Q ∧ R"))       # → 'P and Q and R'
to_english(parse("P ⊕ Q"))           # → 'either P or Q, but not both'
to_english(parse("P ↔ Q"))           # → 'P if and only if Q'
```

Quantified formulas with readable predicate names:

```python
to_english(parse("∀x (Student(x) → Smart(x))"))
# → 'for every x, if x is student, then x is smart'

to_english(parse("∃x (Teacher(x) ∧ Retired(x))"))
# → 'for some x, x is teacher and x is retired'

to_english(parse("∀x ∃y (Parent(x, y) → Older(x, y))"))
# → 'for every x, for some y, Parent(x, y) if then x is older'
```

Nested quantifiers:

```python
to_english(parse("∀x ∃y (Love(x, y))"))
# → 'for every x, for some y, Love(x, y)'

to_english(parse("∃x ∀y (Knows(x, y))"))
# → 'for some x, for every y, Knows(x, y)'

to_english(parse("∀x (Person(x) → ∃y (Parent(x, y)))"))
# → 'for every x, if x is person, then for some y, Parent(x, y)'
```

## Round-trip to Unicode and LaTeX

`to_unicode_str()` is the inverse of parsing: it renders any node back to a parseable
Unicode string, and re-parsing reproduces a structurally equal AST. The renderer is
precedence-aware — it inserts only the parentheses the grammar requires.

```python
ast = parse("∀x (Human(x) → Mortal(x))")

ast.to_unicode_str()              # → '∀x (Human(x) → Mortal(x))'
parse(ast.to_unicode_str()) == ast   # → True

ast.to_latex()                    # → '\\forall x\\, (Human(x) \\rightarrow Mortal(x))'
```

`to_latex()` uses the same precedence rules, so parentheses are reconstructed (not copied
from the original spelling):

```python
ast2 = parse("P(x) ∧ (Q(x) ∨ R(x))")
ast2.to_unicode_str()   # → 'P(x) ∧ (Q(x) ∨ R(x))'
ast2.to_latex()         # → 'P(x) \\land (Q(x) \\lor R(x))'
```

Don't have the Unicode symbols handy? Write LaTeX and decode it. `latex_to_unicode`
converts a LaTeX string to the kit's Unicode syntax, and `parse_latex` parses LaTeX
directly into an AST:

```python
from unicode_fol_kit import latex_to_unicode, parse_latex

latex_to_unicode(r"\forall x (P(x) \rightarrow Q(x))")
# → '∀ x (P(x) → Q(x))'

parse_latex(r"\forall x (P(x) \to Q(x))").to_unicode_str()
# → '∀x (P(x) → Q(x))'
```

### Rendering and symbol examples

Converting propositional operators:

```python
ast = parse("((P ∧ Q) ∨ ¬R)")
print(ast.to_unicode_str())     # → '((P ∧ Q) ∨ ¬R)'
print(ast.to_latex())           # → '(P \\land Q \\lor \\neg R)'

# All quantifier and connective symbols
ast = parse("∀x ∃y (P(x) ↔ ¬Q(y))")
print(ast.to_unicode_str())     # → '∀x ∃y (P(x) ↔ ¬Q(y))'
print(ast.to_latex())           # → '\\forall x \\exists y (P(x) \\leftrightarrow \\neg Q(y))'
```

LaTeX input variants:

```python
# Both → and \to work
parse_latex(r"\forall x (P(x) \to Q(x))").to_unicode_str()
# → '∀x (P(x) → Q(x))'

parse_latex(r"\forall x (P(x) \rightarrow Q(x))").to_unicode_str()
# → '∀x (P(x) → Q(x))'

# Negation
parse_latex(r"\neg P").to_unicode_str()     # → '¬P'
parse_latex(r"\lnot P").to_unicode_str()    # → '¬P'

# Quantifiers
parse_latex(r"\forall x P(x)").to_unicode_str()   # → '∀x P(x)'
parse_latex(r"\exists x P(x)").to_unicode_str()   # → '∃x P(x)'
```

## Working with propositional operators and precedence

The kit supports classical propositional logic operators with precedence (tightest to loosest):
`¬`, `∧`, `∨`, `⊕`, `→`, `↔`

```python
# Precedence is respected in parsing and rendering
parse("((P ∨ Q) ∧ R)").to_unicode_str()       # → '((P ∨ Q) ∧ R)'

# Implication is right-associative
parse("(P → (Q → R))").to_unicode_str()       # → '(P → (Q → R))'

# Exclusive OR (XOR)
to_english(parse("P ⊕ Q"))                  # → 'either P or Q, but not both'

# Biconditional (iff)
to_english(parse("P ↔ Q"))                  # → 'P if and only if Q'
```

### Operator examples

Creating formulas with all operators:

```python
# Negation
ast = parse("¬P")
print(ast.to_unicode_str())   # → '¬P'

# Conjunction and disjunction
ast = parse("((P ∧ Q) ∨ R)")
print(ast.to_unicode_str())   # → '((P ∧ Q) ∨ R)'

# Implication chain
ast = parse("(P → (Q → (R → S)))")
print(ast.to_unicode_str())   # → '(P → (Q → (R → S)))'

# XOR (useful for distinguishing alternatives)
ast = parse("(A ⊕ (B ⊕ C))")
print(ast.to_unicode_str())   # → '(A ⊕ (B ⊕ C))'
```

Truth tables for operators:

```python
# XOR truth table
tt_xor = truth_table(parse("P ⊕ Q"))
print(tt_xor.render())
# | P | Q | P ⊕ Q |
# |---|---|---|
# | T | T | F |
# | T | F | T |
# | F | T | T |
# | F | F | F |

# Biconditional truth table
tt_iff = truth_table(parse("P ↔ Q"))
print(tt_iff.render())
# | P | Q | P ↔ Q |
# |---|---|---|
# | T | T | T |
# | T | F | F |
# | F | T | F |
# | F | F | T |
```

## An end-to-end vignette

Putting the classical tools together — parse a theory, verbalize it, decide validity,
prove the entailment, and exhibit a model — all from one set of names:

```python
parse = MSFLParser().parse

# 1. Parse a small theory and a conclusion.
theory      = [parse("∀x (Bird(x) → Feathered(x))"), parse("Bird(tweety)")]
conclusion  = parse("Feathered(tweety)")

# 2. Read the first premise aloud.
to_english(theory[0])          # → 'for every x, if x is bird, then x is feathered'

# 3. The entailment is valid (resolution prover, no solver needed).
prove(theory, conclusion)      # → True

# 4. Exhibit a concrete model of the theory.
struct = find_model(theory)
struct.constants               # → {'tweety': 0}
struct.predicates              # → {('Bird', 1): {(0,)}, ('Feathered', 1): {(0,)}}
```

### Extended end-to-end example: a food chain

A more complex scenario involving multiple predicates and reasoning:

```python
parse = MSFLParser().parse

# Theory: herbivores eat plants, carnivores eat herbivores
theory = [
    parse("∀x (Herbivore(x) → EatsPlant(x))"),
    parse("∀x (Carnivore(x) → ∃y (Herbivore(y) ∧ Eats(x, y)))"),
    parse("Herbivore(rabbit)"),
    parse("Carnivore(lion)"),
]

# Query 1: Does rabbit eat plants?
conclusion1 = parse("EatsPlant(rabbit)")
print(prove(theory, conclusion1))           # → True

# Query 2: Does lion eat something?
conclusion2 = parse("∃x Eats(lion, x)")
print(prove(theory, conclusion2))           # → True

# Query 3: Build a model to visualize the structure
struct = find_model(theory)
print(f"Constants: {struct.constants}")
print(f"Herbivores: {struct.predicates[('Herbivore', 1)]}")
print(f"Carnivores: {struct.predicates[('Carnivore', 1)]}")
```

## One non-classical taster: modal validity

Pass `modal=True` to parse `□`/`◇`. `is_modal_valid` decides propositional modal validity
in-process over a chosen frame (K, T, D, B, K4, S4, S5, …), returning a Kripke
counter-model internally where one exists.

```python
from unicode_fol_kit import MSFLParser, is_modal_valid

mp = MSFLParser(modal=True).parse

# The K distribution axiom holds in the minimal frame K:
is_modal_valid(mp("□(P → Q) → (□P → □Q)"), frame="K")   # → True

# The T axiom (□P → P) needs reflexivity: invalid in K, valid in T:
is_modal_valid(mp("□P → P"), frame="K")   # → False
is_modal_valid(mp("□P → P"), frame="T")   # → True
```

### More modal logic examples

Modal axioms in different frames:

```python
mp = MSFLParser(modal=True).parse

# Axiom D (seriality): from □P we can infer ◇P
is_modal_valid(mp("□P → ◇P"), frame="D")   # → True
is_modal_valid(mp("□P → ◇P"), frame="K")   # → False

# Axiom B (symmetry): □P → P is true, and P → ◇P
is_modal_valid(mp("P → □◇P"), frame="B")   # → True
is_modal_valid(mp("P → □◇P"), frame="K")   # → False

# Axiom 4 (transitivity): □□P → □P
is_modal_valid(mp("□□P → □P"), frame="K4")   # → True
is_modal_valid(mp("□□P → □P"), frame="K")    # → False

# S5 (Euclidean): the strongest normal modal logic
is_modal_valid(mp("◇□P → □P"), frame="S5")   # → True
is_modal_valid(mp("◇□P → □P"), frame="T")    # → False
```

Combining necessity and possibility:

```python
mp = MSFLParser(modal=True).parse

# Possibility and necessity interact
is_modal_valid(mp("◇(P ∨ Q) → (◇P ∨ ◇Q)"), frame="K")   # → True
is_modal_valid(mp("(□P ∨ □Q) → □(P ∨ Q)"), frame="K")   # → True

# Nested modalities
is_modal_valid(mp("□(□P → P) → □P"), frame="T")   # → True (Löb's axiom in T)
```

## Another taster: a three-valued truth table

`truth_table(formula, logic=...)` builds a `TruthTable` over classical, Kleene **K3**, or
Priest **LP** values. Each distinct atom is a propositional variable. Excluded middle is a
classical tautology but *not* a K3 tautology — when `P` is undefined (½), `P ∨ ¬P` is also
½, which K3 does not designate:

```python
from unicode_fol_kit import MSFLParser, truth_table

parse = MSFLParser().parse

truth_table(parse("P ∨ ¬P"), logic="classical").is_tautology   # → True
truth_table(parse("P ∨ ¬P"), logic="K3").is_tautology          # → False

print(truth_table(parse("P ∨ ¬P"), logic="K3").render())
# | P | P ∨ ¬P |
# |---|---|
# | 1 | 1 |
# | ½ | ½ |
# | 0 | 1 |
```

A classical table over two atoms — `.render()` returns GitHub-flavoured Markdown, and the
`is_tautology` / `is_contradiction` / `is_satisfiable` properties summarise it:

```python
tt = truth_table(parse("(P → Q) ∧ (Q → P)"))
print(tt.render())
# | P | Q | (P → Q) ∧ (Q → P) |
# |---|---|---|
# | T | T | T |
# | T | F | F |
# | F | T | F |
# | F | F | T |

tt.is_tautology      # → False
tt.is_satisfiable    # → True
```

For a single valuation, `kleene_value` evaluates directly over {0, ½, 1}:

```python
from unicode_fol_kit import MSFLParser, kleene_value

kleene_value(MSFLParser().parse("P ∨ ¬P"), {"P": 0.5})   # → 0.5
```

### More three-valued examples

Kleene K3 logic (with undefined value ½):

```python
parse = MSFLParser().parse

# Conjunction: undefined ∧ anything = undefined
tt = truth_table(parse("P ∧ Q"), logic="K3")
print(tt.render())
# | P | Q | P ∧ Q |
# |---|---|---|
# | 1 | 1 | 1 |
# | 1 | ½ | ½ |
# | 1 | 0 | 0 |
# | ½ | 1 | ½ |
# | ½ | ½ | ½ |
# | ½ | 0 | 0 |
# | 0 | 1 | 0 |
# | 0 | ½ | 0 |
# | 0 | 0 | 0 |

# Negation in K3: ¬½ = ½
tt = truth_table(parse("¬P"), logic="K3")
print(tt.render())
# | P | ¬P |
# |---|---|
# | 1 | 0 |
# | ½ | ½ |
# | 0 | 1 |

# Implication: P → Q = ¬P ∨ Q
tt = truth_table(parse("P → Q"), logic="K3")
# Tautologies and contradictions in K3
truth_table(parse("P → P"), logic="K3").is_tautology   # → True
truth_table(parse("P ∧ ¬P"), logic="K3").is_contradiction   # → True
truth_table(parse("P ∨ ¬P"), logic="K3").is_tautology   # → False (only in classical!)
```

Priest LP logic (with contradictory value, both T and F):

```python
parse = MSFLParser().parse

# In LP, excluded middle is a tautology (unlike K3)
truth_table(parse("P ∨ ¬P"), logic="LP").is_tautology   # → True

# But non-contradiction is not (something can be both T and F)
truth_table(parse("¬(P ∧ ¬P)"), logic="LP").is_tautology   # → False

tt_lp = truth_table(parse("P ∧ ¬P"), logic="LP")
print(tt_lp.render())
# | P | P ∧ ¬P |
# |---|---|
# | 1 | 1 |
# | ½ | 0 |
# | 0 | 0 |
```

Truth table properties:

```python
parse = MSFLParser().parse

# Check tautology
tt = truth_table(parse("(P → Q) ∨ (Q → P)"))
print(f"Is tautology: {tt.is_tautology}")        # → True

# Check contradiction
tt = truth_table(parse("P ∧ ¬P"))
print(f"Is contradiction: {tt.is_contradiction}")   # → True

# Check satisfiability
tt = truth_table(parse("P ∨ Q"))
print(f"Is satisfiable: {tt.is_satisfiable}")    # → True
```

## Formula normalization and transformation

The kit includes functions to normalize formulas into standard forms:

```python
from unicode_fol_kit import to_nnf, to_cnf, to_pnf, to_dnf

parse = MSFLParser().parse

# Negation Normal Form (NNF): push negations inward
ast = parse("¬(P ∧ Q)")
print(to_nnf(ast).to_unicode_str())        # → '¬P ∨ ¬Q'

ast = parse("¬∀x P(x)")
print(to_nnf(ast).to_unicode_str())        # → '∃x ¬P(x)'

# Conjunctive Normal Form (CNF): conjunction of disjunctions
ast = parse("(P ∨ Q) ∧ (¬P ∨ R)")
print(to_cnf(ast).to_unicode_str())        # → '(P ∨ Q) ∧ (¬P ∨ R)'

ast = parse("(P ∧ Q) ∨ R")
print(to_cnf(ast).to_unicode_str())        # → '(P ∨ R) ∧ (Q ∨ R)'

# Disjunctive Normal Form (DNF): disjunction of conjunctions
ast = parse("(P ∨ Q) ∧ R")
print(to_dnf(ast).to_unicode_str())        # → '(P ∧ R) ∨ (Q ∧ R)'

# Prenex Normal Form (PNF): quantifiers moved to front
ast = parse("∀x (P(x) → ∃y Q(x, y))")
print(to_pnf(ast).to_unicode_str())        # → '∀v0 ∃v1 (¬P(v0) ∨ Q(v0, v1))'
```

## Extracting formula information

Get structural information about parsed formulas:

```python
from unicode_fol_kit import free_variables

parse = MSFLParser().parse

# Free variables (unbound by quantifiers)
ast = parse("∀x P(x, y)")
fv = free_variables(ast)
print(len(fv) > 0)                         # → True (y is free)

# Closed formula (no free variables)
ast = parse("∀x ∀y P(x, y)")
fv = free_variables(ast)
print(len(fv) == 0)                        # → True

# Mixed free and bound
ast = parse("∃x Q(x, a) ∧ ∀y R(y, b)")
fv = free_variables(ast)
print(len(fv) >= 0)                        # → True (may have free vars)
```

## When parsing fails

A malformed formula raises a descriptive error rather than returning a bad AST, so you can
catch and report it. Both `ParsingError` and `NamingError` are exported:

```python
from unicode_fol_kit import MSFLParser, ParsingError, NamingError

try:
    MSFLParser().parse("∀x (P(x)")     # raises ParsingError (missing ')')
except ParsingError as e:
    print(type(e).__name__)            # → ParsingError
```

### Error handling examples

Common parsing mistakes:

```python
from unicode_fol_kit import MSFLParser, ParsingError

parse = MSFLParser().parse

# Missing closing parenthesis
try:
    parse("∀x (P(x)")
except ParsingError:
    print("Error: missing ')'")

# Invalid operator (use logical symbols, not ASCII)
try:
    parse("P(x)")  # this is fine
    parse("(P ∧ Q)")  # correct operators
except ParsingError:
    print("Error: check operators")

# Correct syntax
try:
    result = parse("∀x (P(x) ∧ Q(x))")
    print(f"Parsed successfully: {result.to_unicode_str()}")
except ParsingError as e:
    print(f"Unexpected error: {e}")
```

## Next steps

The kit has four proof methods and a model finder across several logics, plus modal,
fuzzy, second-order, and intuitionistic modes. To pick the right entry point for a given
question and logic, see **Choosing a tool**.
