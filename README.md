# unicode-fol-kit

A Python toolkit for parsing and working with first-order logic (FOL) formulas written with Unicode operators.

## Features

- **Parser** — parse FOL formulas using natural Unicode symbols (∀, ∃, ∧, ∨, ¬, →, ↔, ⊕, =, ≠, ≤, ≥)
- **AST** — full abstract syntax tree with all standard FOL constructs
- **Serialisation** — convert formulas to/from JSON dictionaries
- **Tree view** — render any formula as a readable ASCII tree
- **Z3 export** — translate formulas to Z3 expressions for SMT solving
- **Prover9 export** — translate formulas to Prover9 syntax for automated theorem proving
- **TPTP export** — translate formulas to TPTP syntax
- **Equivalence checking** — check if two formulas are logically equivalent via Z3
- **Entailment checking** — check if a conclusion follows from premises via Prover9

## Installation

### Via pip

```bash
pip install unicode-fol-kit
```

### Via git clone

```bash
git clone https://github.com/felixvossel/unicode-fol-kit.git
cd unicode-fol-kit
pip install .
```

## Usage

### Parsing a formula

```python
from unicode_fol_kit import FOLParser

parser = FOLParser()
formula = parser.parse("∀x (Human(x) → Mortal(x))")
```

### ASCII tree view

```python
print(formula.tree_str())
# ∀ x
# └── →
#     ├── Atom: Human
#     │   └── Variable: x
#     └── Atom: Mortal
#         └── Variable: x
```

### Exporting to other formats

```python
formula.to_prover9()   # '(all x (Human(x) -> Mortal(x)))'
formula.to_tptp()      # '(![X]: (human(X) => mortal(X)))'
formula.to_dict()      # JSON-serialisable dict
```

### Serialisation

```python
from unicode_fol_kit import Node

d = formula.to_dict()
formula2 = Node.from_dict(d)  # round-trip
```

### Equivalence checking (Z3)

```python
from unicode_fol_kit import FOLParser, formulas_are_equivalent

parser = FOLParser()
f1 = parser.parse("¬(P(x) ∧ Q(x))")
f2 = parser.parse("¬P(x) ∨ ¬Q(x)")

formulas_are_equivalent(f1, f2)  # True
```

### Entailment checking (Prover9)

```python
from unicode_fol_kit import FOLParser, check_logical_entailment

parser = FOLParser()
premises = [
    parser.parse("∀x (Human(x) → Mortal(x))"),
    parser.parse("Human(socrates)"),
]
conclusion = parser.parse("Mortal(socrates)")

check_logical_entailment(premises, conclusion, prover9_path="/usr/bin/prover9")  # True
```

## Syntax reference

This section describes the full surface syntax accepted by the parser: which
symbols are recognised, how terms and formulas are built, and how operator
precedence and associativity resolve ambiguous input.

### Tokens

The lexer distinguishes the following kinds of identifier, each by a strict
pattern. Because the categories are separated at the token level, a given
identifier is unambiguously a variable, a constant, a function/predicate name,
or a number.

| Token | Pattern | Examples | Meaning |
|---|---|---|---|
| Variable | one lowercase letter, optional trailing digits | `x`, `y`, `x1`, `z42` | a (possibly bound) logical variable |
| Name | lowercase, at least two letters, may contain digits and uppercase after the first letter | `socrates`, `distance`, `centerOf`, `foo1` | a constant or a function symbol |
| Constant (`c_`) | `c_` followed by letters/digits | `c_a`, `c_zero`, `c_42` | an explicitly marked constant |
| Predicate | one uppercase letter, then letters/digits | `P`, `Human`, `OnSurfaceOf` | a predicate symbol |
| Number | digits, optional decimal part | `0`, `42`, `3.14` | a numeric literal |

The `c_` form exists so that **single-letter constants** can be written without
colliding with variables. A bare `a` is always a variable; if you need the
constant *a*, write `c_a`.

A function or predicate is recognised by being immediately followed by a
parenthesised argument list, e.g. `distance(x, y)` or `Human(socrates)`.
The same identifier class (Name) serves both as a bare constant and, when
applied, as a function symbol.

### Terms

A term is one of:

- a variable (`x`, `x1`)
- a constant (`socrates`, `c_a`) or number (`42`, `3.14`)
- a function application (`f(t1, ..., tn)`, e.g. `centerOf(x)`)
- an arithmetic combination of terms using `+`, `-`, `*`, `/`
- a parenthesised term (`(t)`)

Arithmetic follows the usual precedence: `*` and `/` bind tighter than `+` and
`-`, and both groups are left-associative. For example `x + y * z` parses as
`x + (y * z)`.

### Atomic formulas

An atomic formula is either:

- a predicate applied to terms: `P`, `Human(socrates)`, `OnSurfaceOf(y, x)`
  (a predicate may be nullary, i.e. used without arguments)
- an infix comparison between two terms using `=`, `≠`, `<`, `>`, `≤`, `≥`,
  e.g. `x1 + 1 = y1` or `distance(y, c) > distance(z, c)`

### Compound formulas

Atomic formulas are combined with the logical connectives and quantifiers:

- negation: `¬φ`
- conjunction: `φ ∧ ψ`
- disjunction: `φ ∨ ψ`
- exclusive or: `φ ⊕ ψ`
- implication: `φ → ψ`
- biconditional: `φ ↔ ψ`
- universal quantification: `∀x φ`
- existential quantification: `∃x φ`

A formula may be wrapped in parentheses `( … )` or square brackets `[ … ]`;
the two are interchangeable for grouping.

### Operator precedence

From highest (binds tightest) to lowest (binds loosest):

| Precedence | Operators | Associativity |
|---|---|---|
| 1 (highest) | `¬`, quantifiers `∀` / `∃` | prefix |
| 2 | `∧`, `∨`, `⊕` | left |
| 3 | `→` | right |
| 4 (lowest) | `↔` | right |

Worked examples (parenthesised to show how the parser groups them):

- `¬P(x) ∧ Q(x)` → `(¬P(x)) ∧ Q(x)` — negation binds tighter than conjunction
- `P(x) ∧ Q(x) → R(x)` → `(P(x) ∧ Q(x)) → R(x)` — conjunction binds tighter than implication
- `P(x) → Q(x) ↔ R(x)` → `(P(x) → Q(x)) ↔ R(x)` — implication binds tighter than biconditional
- `P(x) → Q(x) → R(x)` → `P(x) → (Q(x) → R(x))` — implication is right-associative
- `P(x) ∧ Q(x) ∧ R(x)` → `(P(x) ∧ Q(x)) ∧ R(x)` — conjunction is left-associative

### Mixing ∧, ∨ and ⊕

Conjunction, disjunction and exclusive or sit at the **same** precedence level
and **cannot be mixed without explicit parentheses**. This is deliberate: it
avoids the silent, easy-to-misread grouping that a default precedence would
impose. For example:

```text
P(x) ∧ Q(x) ∨ R(x)        # rejected — ambiguous
(P(x) ∧ Q(x)) ∨ R(x)      # accepted
P(x) ∧ (Q(x) ∨ R(x))      # accepted
```

A chain of the *same* operator is fine: `P ∧ Q ∧ R` and `P ∨ Q ∨ R` both parse.

### Quantifier scope

A quantifier binds **only the immediately following (tightly bound) formula**,
not the rest of the line. In particular it does *not* automatically extend over
a following connective. This means:

```text
∀x P(x) ∧ Q(x)            # parses as (∀x P(x)) ∧ Q(x)
∀x P(x) → Q(x)            # parses as (∀x P(x)) → Q(x)
```

If you intend the quantifier to range over the whole implication or
conjunction — which is usually what is meant — **add parentheses**:

```text
∀x (P(x) → Q(x))          # quantifier ranges over the implication
∀x (P(x) ∧ Q(x))          # quantifier ranges over the conjunction
```

Quantifiers can be stacked directly: `∀x ∀y ∃z φ`.

### Supported symbols

| Category | Symbols |
|---|---|
| Quantifiers | `∀` `∃` |
| Connectives | `∧` `∨` `⊕` `¬` `→` `↔` |
| Equality / comparison | `=` `≠` `<` `>` `≤` `≥` |
| Arithmetic | `+` `-` `*` `/` |
| Grouping | `(` `)` `[` `]` |
| Argument separator | `,` |

Whitespace is insignificant and may be used freely between tokens.

### A complete example

```text
∀x ((Object(x) ∧ HasThreeDimensionalShape(x) ∧
     ∀y ∀z ((Point(y) ∧ OnSurfaceOf(y, x) ∧ Point(z) ∧ OnSurfaceOf(z, x))
            → distance(y, centerOf(x)) = distance(z, centerOf(x))))
    → Sphere(x))
```

This uses unary predicates (`Object`, `Sphere`, `Point`), a binary predicate
(`OnSurfaceOf`), functions (`distance`, `centerOf`), an infix equality between
two function terms, nested quantifiers, and explicit parentheses to control
both the inner implication and the quantifier scope.

## Error handling

Parse errors are reported with human-readable messages rather than raw parser
internals. Lexer-level problems (an invalid character, a malformed name or
number) raise `NamingError`; structural problems (an incomplete formula, a
misplaced operator, or an attempt to mix `∧`/`∨`/`⊕` without parentheses) raise
`ParsingError`. Both report the offending position and, where useful, a hint.

```python
from unicode_fol_kit import FOLParser

parser = FOLParser()
parser.parse("P(x) ∧ Q(x) ∨ R(x)")
# Parsing/NamingError: SYNTAX_ERROR: Unexpected character '∨' ...
#   Hint: Cannot mix conjunction (∧), disjunction (∨), and exclusive or (⊕) without parentheses
```

## Citation

If you use this toolkit in academic work, please cite the accompanying
preprint:

```bibtex
@misc{vossel2025advancingnaturallanguageformalization,
      title={Advancing Natural Language Formalization to First Order Logic with Fine-tuned LLMs},
      author={Felix Vossel and Till Mossakowski and Björn Gehrke},
      year={2025},
      eprint={2509.22338},
      archivePrefix={arXiv},
      primaryClass={cs.CL},
      url={https://arxiv.org/abs/2509.22338},
}
```

> Vossel, F., Mossakowski, T., & Gehrke, B. (2025). *Advancing Natural Language
> Formalization to First Order Logic with Fine-tuned LLMs.* arXiv preprint
> arXiv:2509.22338.

## License

MIT
