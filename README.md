# unicode-fol-kit

A Python toolkit for parsing and working with first-order logic (FOL) formulas written with Unicode operators. The single parser class `MSFLParser` supports four modes — classical FOL, many-sorted FOL (MSFOL), many-sorted fuzzy logic (MSFL), and single-sorted fuzzy logic (FL, Łukasiewicz) — selected by constructor flags.

## Features

- **Four parser modes** — FOL, many-sorted FOL (MSFOL), many-sorted fuzzy/Łukasiewicz logic (MSFL), and single-sorted fuzzy/Łukasiewicz logic (FL), all from one class
- **Unicode surface syntax** — natural symbols (∀ ∃ ∧ ∨ ¬ → ↔ ⊕ ⊗ = ≠ ≤ ≥) with no ASCII fallbacks needed
- **Sorted quantifiers and constants** — `∀x:Human P(x)`, `P(alice:Human)` in MSFOL and MSFL modes
- **Łukasiewicz operators** — weak ∧ / ∨ (min/max), strong ⊗ / ⊕ (t-norm/t-conorm), and Łukasiewicz ¬ → ↔ in MSFL mode
- **Full AST** — all standard FOL constructs plus MSFL-specific nodes, all as Python dataclasses
- **Reductions** — `to_msfol()` lowers Łukasiewicz operators to classical nodes; `to_fol()` further eliminates sorts via relativisation
- **Serialisation** — convert formulas to/from JSON dictionaries; round-trip safe
- **Tree view** — render any formula as a readable ASCII tree
- **Unicode round-trip** — `to_unicode_str()` renders any node back to a parseable Unicode formula; re-parsing in the matching mode yields a structurally equal AST
- **LaTeX export** — `to_latex()` renders any node as LaTeX math-mode markup, with the same precedence-aware parenthesisation as the Unicode renderer
- **Normal forms** — `to_nnf()`, `to_pnf()`, `to_cnf()` (equivalence-preserving), and `skolemize()` (satisfiability-preserving) for classical FOL
- **Horn check** — `is_horn()` reports whether a formula's clausal form consists of Horn clauses
- **Traversal API** — `walk()`, `subformulas()`, `atoms()`, `variables()`, `count()`, `depth()` on every node
- **Graphviz export** — `to_dot()` renders the AST as a Graphviz DOT digraph
- **Z3 export** — translate formulas to Z3 expressions for SMT solving
- **Satisfiability / validity / models** — `is_satisfiable()`, `is_valid()`, and `get_model()` (counterexample extraction) via Z3
- **Prover9 export** — translate formulas to Prover9 syntax for automated theorem proving
- **TPTP export** — translate formulas to TPTP syntax
- **Equivalence checking** — check if two formulas are logically equivalent via Z3
- **Entailment checking** — check if a conclusion follows from premises via Prover9
- **Lambda abstraction** — `λx. φ` syntax in all three parser modes; parameters can be variables (`λx.`), named constants (`λfoo.`), or predicate symbols (`λP.`); body extends rightward through all connectives
- **Higher-order predicate application** — `(func)(arg)` explicit application; `λP. P(x)` writes the body naturally and is automatically scope-resolved to `Application(LambdaVar("P"), Variable("x"))`
- **Lambda-calculus operations** — free-variable computation, capture-avoiding substitution, beta-reduction (normal-order, step-limited), eta-reduction, combined beta-eta normalisation to fixpoint, and lexical scope resolution

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

## Parser modes

`MSFLParser` is instantiated with two boolean flags:

```python
MSFLParser(many_sorted=False, fuzzy=False)   # FOL   (default)
MSFLParser(many_sorted=True,  fuzzy=False)   # MSFOL
MSFLParser(many_sorted=True,  fuzzy=True)    # MSFL
MSFLParser(many_sorted=False, fuzzy=True)    # FL
```

| `many_sorted` | `fuzzy` | Mode | Quantifiers | Constants | Connectives |
|---|---|---|---|---|---|
| `False` | `False` | **FOL** | unsorted `∀x` | unsorted | classical ∧ ∨ ⊕ ¬ → ↔ |
| `True` | `False` | **MSFOL** | sorted `∀x:Sort` | sorted `alice:Sort` | classical ∧ ∨ ¬ → ↔ (no ⊕) |
| `True` | `True` | **MSFL** | sorted `∀x:Sort` | sorted `alice:Sort` | weak ∧ ∨, strong ⊗ ⊕, Łuk ¬ → ↔ |
| `False` | `True` | **FL** | unsorted `∀x` | unsorted | weak ∧ ∨, strong ⊗ ⊕, Łuk ¬ → ↔ |

## Usage

### FOL mode (default)

```python
from unicode_fol_kit import MSFLParser

parser = MSFLParser()
formula = parser.parse("∀x (Human(x) → Mortal(x))")
```

### MSFOL mode

Quantifiers and ground constants must carry a sort annotation. The colon can be written with or without a space before it:

```python
parser = MSFLParser(many_sorted=True)

# Sorted quantifier
q = parser.parse("∀x:Human (Mortal(x) ∧ ¬Immortal(x))")
# SortedQuantifier(type='∀', variable=Variable('x'), sort='Human', formula=…)

# Sorted constant — both spacing forms are accepted
parser.parse("P(alice:Human)")
parser.parse("P(alice :Human)")
```

### MSFL mode

Uses Łukasiewicz logic: `∧`/`∨` become weak (min/max), `⊗`/`⊕` become strong (t-norm/t-conorm), and `¬`/`→`/`↔` map to their Łukasiewicz counterparts:

```python
parser = MSFLParser(many_sorted=True, fuzzy=True)

parser.parse("P(x) ∧ Q(x)")    # WeakConjunction (min)
parser.parse("P(x) ⊗ Q(x)")    # StrongConjunction (t-norm: max{0, x+y−1})
parser.parse("P(x) ⊕ Q(x)")    # StrongDisjunction (t-conorm: min{1, x+y})
parser.parse("¬P(x)")           # LukNegation (1−x)
parser.parse("P(x) → Q(x)")    # LukImplication (min{1, 1−x+y})
parser.parse("∀x:Human P(x)")  # SortedQuantifier
```

### FL mode

Łukasiewicz operators with **unsorted** quantifiers and plain constants — same connectives as MSFL, same quantifier/constant syntax as FOL:

```python
parser = MSFLParser(many_sorted=False, fuzzy=True)

parser.parse("P(x) ∧ Q(x)")          # WeakConjunction (min)
parser.parse("P(x) ⊗ Q(x)")          # StrongConjunction (t-norm: max{0, x+y−1})
parser.parse("P(x) ⊕ Q(x)")          # StrongDisjunction (t-conorm: min{1, x+y})
parser.parse("¬P(x)")                 # LukNegation (1−x)
parser.parse("P(x) → Q(x)")          # LukImplication (min{1, 1−x+y})
parser.parse("∀x P(x)")              # unsorted Quantifier (no sort annotation)
parser.parse("P(alice)")             # plain Constant (no sort annotation)

# Lambda works in FL mode too
parser.parse("λx. P(x) ⊗ Q(x)")
# Lambda(LambdaVar("x"), StrongConjunction(Atom("P",[LambdaVar("x")]), Atom("Q",[LambdaVar("x")])))
```

### ASCII tree view

```python
formula = MSFLParser().parse("∀x (Human(x) → Mortal(x))")
print(formula.tree_str())
# ∀ x
# └── →
#     ├── Atom: Human
#     │   └── Variable: x
#     └── Atom: Mortal
#         └── Variable: x
```

### Round-trip to Unicode

`to_unicode_str()` is the inverse of parsing: it renders any node back to a Unicode formula string. Re-parsing that string in the same mode reproduces a structurally equal AST. The renderer is precedence-aware and only inserts the parentheses the grammar requires — including the no-mixing rule for same-level connectives and the tight-binding rule for quantifiers.

```python
parser = MSFLParser()

ast = parser.parse("∀x P(x) ∧ Q(x)")
ast.to_unicode_str()              # '∀x P(x) ∧ Q(x)'
parser.parse(ast.to_unicode_str()) == ast   # True

# Precedence-driven parentheses are reconstructed, not the original spelling:
parser.parse("((P(x) ∧ Q(x)))").to_unicode_str()   # 'P(x) ∧ Q(x)'
parser.parse("P(x) ∧ (Q(x) ∨ R(x))").to_unicode_str()  # 'P(x) ∧ (Q(x) ∨ R(x))'
```

Available on every node, so subformulas render too. The output targets parseable
ASTs; alpha-renamed variables introduced by `beta_reduce` (e.g. `x_0`) are not
valid surface tokens and will not round-trip.

### Exporting to other formats

```python
formula.to_prover9()   # '(all x (Human(x) -> Mortal(x)))'
formula.to_tptp()      # '(![X]: (human(X) => mortal(X)))'
formula.to_latex()     # '\\forall x\\, (Human(x) \\rightarrow Mortal(x))'
formula.to_dict()      # JSON-serialisable dict
```

`to_latex()` uses the same precedence-aware parenthesisation as `to_unicode_str()`. Sorts render as `\forall x{:}\mathrm{Human}\,`; strong Łukasiewicz operators as `\otimes` / `\oplus`. Symbol and predicate names are emitted verbatim (no `\mathrm` wrapping).

### Traversal and inspection

Every node exposes a small traversal API:

```python
f = MSFLParser().parse("∀x (Human(x) → Mortal(x))")

list(f.walk())        # pre-order: every node and descendant
f.subformulas()       # every sub-node that is a formula (terms excluded)
f.atoms()             # [Atom("Human", …), Atom("Mortal", …)]
f.variables()         # {Variable("x")}  — set of logical variables (free + bound)
f.count()             # total node count
f.count(Atom)         # nodes of a given type
f.depth()             # tree height (a leaf has depth 1)
```

### Graphviz export

```python
print(f.to_dot())
# digraph AST {
#   node [shape=box];
#   n0 [label="∀ x"];
#   n1 [label="→"];
#   ...
# }
```

`to_dot()` mirrors the `tree_str()` view (the quantifier's bound variable is folded into its node label). Pipe the output to `dot -Tpng` to render an image.

### Serialisation

```python
from unicode_fol_kit import Node

d = formula.to_dict()
formula2 = Node.from_dict(d)  # round-trip
```

### Lambda-calculus

All three parser modes support lambda abstraction and application. `parse()` automatically applies scope resolution, so the returned AST is always fully resolved.

```python
from unicode_fol_kit import (
    MSFLParser,
    LambdaVar, Lambda, Application,
    free_variables, substitute,
    beta_reduce, eta_reduce, beta_eta_normalize,
    resolve_lambda_scope,
    ReductionLimitError,
)

parser = MSFLParser()

# Parse — scope resolution is applied automatically
term = parser.parse("λP. λx. P(x)")
# Lambda(LambdaVar("P"), Lambda(LambdaVar("x"), Application(LambdaVar("P"), LambdaVar("x"))))

# Application
app = parser.parse("(λP. P(x))(Q)")
# Application(Lambda(LambdaVar("P"), Application(LambdaVar("P"), Variable("x"))),
#             Atom("Q", []))
```

#### Free variables

```python
term = parser.parse("λP. P(x)")
free_variables(term)
# {Variable("x")}  — x is free; P is lambda-bound and does not appear
```

The result is a mixed set that may contain both `Variable` (logical) and `LambdaVar` (lambda-bound) objects.

#### Beta-reduction

`beta_reduce` reduces to beta-normal form using a normal-order (leftmost-outermost) strategy with full capture-avoiding substitution. It raises `ReductionLimitError` after 10 000 steps if the term does not normalise.

```python
# (λP. λx. P(x))(Q) → λx. Application(Atom("Q",[]), LambdaVar("x"))
result = beta_reduce(parser.parse("(λP. λx. P(x))(Q)"))

# Full pipeline: parse → resolve → reduce
reduced = beta_reduce(parser.parse("(λP. P(x))(λy. Q(y))"))
# Atom("Q", [Variable("x")])
```

#### Eta-reduction

`eta_reduce` performs a single bottom-up pass contracting all eta-redexes: `λp. f(p) → f` when `p` is not free in `f`. Quantifiers are recursed into but never treated as eta-redexes.

```python
from unicode_fol_kit import LambdaVar, Lambda, Application, Atom, Variable

f = Atom("P", [Variable("x")])                  # some formula
term = Lambda(LambdaVar("p"), Application(f, LambdaVar("p")))  # λp. f(p)
eta_reduce(term)   # → f  (the Atom node, not the Lambda)
```

#### Beta-eta normalisation

`beta_eta_normalize` alternates `beta_reduce` and `eta_reduce` to fixpoint (up to 100 rounds). The alternation loop is a genuine necessity: eta-reduction can expose fresh beta-redexes, requiring another beta pass.

```python
normal = beta_eta_normalize(parser.parse("(λP. P(x))(Q)"))
```

`ReductionLimitError` is raised if the inner beta-reduction limit or the outer round limit is exceeded.

#### Scope resolution (standalone)

`resolve_lambda_scope` is also available as a standalone function for hand-built ASTs:

```python
from unicode_fol_kit import resolve_lambda_scope, Lambda, LambdaVar, Atom, Variable

raw = Lambda(LambdaVar("x"), Atom("P", [Variable("x")]))
resolved = resolve_lambda_scope(raw)
# Lambda(LambdaVar("x"), Atom("P", [LambdaVar("x")]))
```

### Reducing MSFL formulas to classical FOL

`to_fol()` performs a two-phase reduction: it first lowers Łukasiewicz operators to classical ones (`to_msfol()`), then eliminates sort annotations via relativisation (`_relativize()`):

```python
from unicode_fol_kit import MSFLParser, to_fol

parser = MSFLParser(many_sorted=True, fuzzy=True)
formula = parser.parse("∀x:Human (P(x) ∧ ¬Q(x))")

classical = to_fol(formula)
# Quantifier(∀, x, Implies(Atom(Human, [x]), And(Atom(P,[x]), Not(Atom(Q,[x])))))

# Optionally, conjoin sort-membership facts for constants at the top level:
classical_with_facts = to_fol(formula, include_sort_facts=True)
```

### Normal forms

`to_nnf()`, `to_pnf()`, `to_cnf()`, and `skolemize()` operate on classical FOL. They accept FOL, MSFOL, MSFL, and FL inputs — sorts and Łukasiewicz operators are reduced via `to_fol()` first. (Lambda terms must be beta-reduced and lambda-eliminated beforehand.)

```python
from unicode_fol_kit import MSFLParser, to_nnf, to_pnf, to_cnf, skolemize

parser = MSFLParser()

to_nnf(parser.parse("P → Q"))        # eliminates → ↔ ⊕, pushes ¬ down to atoms
to_pnf(parser.parse("∀x P(x) ∧ ∃y Q(y)"))   # quantifier prefix + quantifier-free matrix
to_cnf(parser.parse("P ∨ (Q ∧ R)"))  # matrix as a conjunction of clauses
skolemize(parser.parse("∀x ∃y Loves(x, y)"))
# ∀v0 Loves(v0, sk0(v0)) — the existential becomes a Skolem function of x
```

- `to_nnf` / `to_pnf` / `to_cnf` are **equivalence-preserving**: the result is logically equivalent to the (classical) input.
- `skolemize` is **satisfiability-preserving** (not equivalence-preserving): existentials are replaced by Skolem terms over the universals in scope, and the universal prefix is retained. Bound variables are standardised apart (renamed to fresh `v0, v1, …`); Skolem symbols are named `sk0, sk1, …`.

### Horn check

`is_horn()` reports whether a formula's clausal form consists of Horn clauses — each clause has at most one positive literal. The formula is skolemised, its universal prefix dropped, and the matrix put into CNF before the clauses are checked.

```python
from unicode_fol_kit import MSFLParser, is_horn

parser = MSFLParser()
is_horn(parser.parse("∀x (Body(x) → Head(x))"))     # True  (definite clause)
is_horn(parser.parse("P → (Q ∧ R)"))                # True  (splits into two Horn clauses)
is_horn(parser.parse("P → (Q ∨ R)"))                # False (clause has two positive literals)
```

### Equivalence checking (Z3)

```python
from unicode_fol_kit import MSFLParser, formulas_are_equivalent

parser = MSFLParser()
f1 = parser.parse("¬(P(x) ∧ Q(x))")
f2 = parser.parse("¬P(x) ∨ ¬Q(x)")

formulas_are_equivalent(f1, f2)  # True
```

### Satisfiability, validity, and counterexamples (Z3)

```python
from unicode_fol_kit import MSFLParser, is_satisfiable, is_valid, get_model, Not

parser = MSFLParser()

is_satisfiable(parser.parse("P ∧ Q"))     # True
is_satisfiable(parser.parse("P ∧ ¬P"))    # False
is_valid(parser.parse("P ∨ ¬P"))          # True

get_model(parser.parse("P ∧ Q"))          # {'P': 'True', 'Q': 'True'}
get_model(parser.parse("P ∧ ¬P"))         # None  (unsatisfiable)

# Counterexample to a claimed equivalence: a model of its negation.
get_model(Not(parser.parse("P ↔ Q")))     # e.g. {'P': 'True', 'Q': 'False'}
```

`get_model` returns a dict mapping each Z3 declaration (constants, uninterpreted predicates/functions) to its interpretation, or `None` when the formula is unsatisfiable or Z3 returns `unknown` within the timeout.

### Entailment checking (Prover9)

```python
from unicode_fol_kit import MSFLParser, check_logical_entailment

parser = MSFLParser()
premises = [
    parser.parse("∀x (Human(x) → Mortal(x))"),
    parser.parse("Human(socrates)"),
]
conclusion = parser.parse("Mortal(socrates)")

check_logical_entailment(premises, conclusion, prover9_path="/usr/bin/prover9")  # True
```

## Syntax reference

This section describes the full surface syntax accepted by the parser. Because the three modes share the same term and atom layer, most of the syntax is identical across modes; differences are called out explicitly.

### Tokens

The lexer distinguishes the following token kinds. Because the patterns are mutually exclusive, a given identifier is unambiguously a variable, a constant, a function/predicate name, a number, or a sort annotation.

| Token | Pattern | Examples | Meaning |
|---|---|---|---|
| Variable | one lowercase letter, optional trailing digits | `x`, `y`, `x1`, `z42` | a (possibly bound) logical variable |
| Name | lowercase, at least two letters, may contain digits and uppercase after the first letter | `socrates`, `distance`, `centerOf`, `foo1` | a bare constant or a function symbol |
| Constant (`c_`) | `c_` followed by letters/digits | `c_a`, `c_zero`, `c_42` | an explicitly marked constant |
| Predicate | one uppercase letter, then letters/digits | `P`, `Human`, `OnSurfaceOf` | a predicate symbol |
| Number | digits, optional decimal part | `0`, `42`, `3.14` | a numeric literal |
| Sort annotation | `:` followed by an uppercase letter and letters/digits | `:Human`, `:Sort1` | a sort tag *(MSFOL and MSFL modes only)* |

The `c_` form exists so that **single-letter constants** can be written without colliding with variables. A bare `a` is always a variable; if you need the constant *a*, write `c_a`.

A function or predicate is recognised by being immediately followed by a parenthesised argument list, e.g. `distance(x, y)` or `Human(socrates)`. The same token class (Name) serves both as a bare constant and, when applied, as a function symbol.

The sort annotation token always begins with `:`, which makes it lexically disjoint from all other tokens. **Whitespace before the colon is optional**: `∀x:Human P(x)` and `∀x :Human P(x)` are both valid and produce identical parse trees.

### Terms

A term is one of:

- a variable (`x`, `x1`)
- a constant (`socrates`, `c_a`) or number (`42`, `3.14`)
- in MSFOL / MSFL modes: a **sort-annotated constant** (`alice:Human`, `c_a:Sort1`)
- a function application (`f(t1, …, tn)`, e.g. `centerOf(x)`)
- an arithmetic combination of terms using `+`, `-`, `*`, `/`
- a parenthesised term (`(t)`)

Arithmetic follows the usual precedence: `*` and `/` bind tighter than `+` and `-`, and both groups are left-associative. For example `x + y * z` parses as `x + (y * z)`.

**Sort rules in MSFOL / MSFL modes:** variables are sorted implicitly by the quantifier that binds them; ground constants must carry an explicit sort annotation. An unsorted constant (e.g. bare `alice`) is a syntax error in sorted modes.

### Atomic formulas

An atomic formula is either:

- a predicate applied to terms: `P`, `Human(socrates)`, `OnSurfaceOf(y, x)`
  (a predicate may be nullary, i.e. used without arguments)
- an infix comparison between two terms: `=`, `≠`, `<`, `>`, `≤`, `≥`,
  e.g. `x1 + 1 = y1` or `distance(y, c) > distance(z, c)`

### Compound formulas

Atomic formulas are combined with connectives and quantifiers. The available connectives and their interpretations depend on the mode:

#### FOL mode

| Syntax | Operator | Interpretation |
|---|---|---|
| `¬φ` | negation | classical |
| `φ ∧ ψ` | conjunction | classical |
| `φ ∨ ψ` | disjunction | classical |
| `φ ⊕ ψ` | exclusive or | classical |
| `φ → ψ` | implication | classical |
| `φ ↔ ψ` | biconditional | classical |
| `∀x φ` | universal | unsorted |
| `∃x φ` | existential | unsorted |

#### MSFOL mode

Same connectives as FOL **except `⊕` (exclusive or) is not available**. Quantifiers require a sort annotation:

| Syntax | Operator |
|---|---|
| `¬φ`, `φ ∧ ψ`, `φ ∨ ψ`, `φ → ψ`, `φ ↔ ψ` | classical (as FOL) |
| `∀x:Sort φ`, `∃x:Sort φ` | sorted quantifiers |

#### MSFL mode

Connectives are reinterpreted as Łukasiewicz operators:

| Syntax | Operator | Semantics |
|---|---|---|
| `¬φ` | Łuk. negation | 1 − φ |
| `φ ∧ ψ` | weak conjunction | min(φ, ψ) |
| `φ ∨ ψ` | weak disjunction | max(φ, ψ) |
| `φ ⊗ ψ` | strong conjunction | max(0, φ + ψ − 1) |
| `φ ⊕ ψ` | strong disjunction | min(1, φ + ψ) |
| `φ → ψ` | Łuk. implication | min(1, 1 − φ + ψ) |
| `φ ↔ ψ` | Łuk. equivalence | 1 − \|φ − ψ\| |
| `∀x:Sort φ`, `∃x:Sort φ` | sorted quantifiers | |

#### FL mode

Same Łukasiewicz connectives as MSFL, but with **unsorted** quantifiers and plain constants (no `:Sort` required):

| Syntax | Operator | Semantics |
|---|---|---|
| `¬φ` | Łuk. negation | 1 − φ |
| `φ ∧ ψ` | weak conjunction | min(φ, ψ) |
| `φ ∨ ψ` | weak disjunction | max(φ, ψ) |
| `φ ⊗ ψ` | strong conjunction | max(0, φ + ψ − 1) |
| `φ ⊕ ψ` | strong disjunction | min(1, φ + ψ) |
| `φ → ψ` | Łuk. implication | min(1, 1 − φ + ψ) |
| `φ ↔ ψ` | Łuk. equivalence | 1 − \|φ − ψ\| |
| `∀x φ`, `∃x φ` | unsorted quantifiers | |

A formula may be wrapped in parentheses `( … )` or square brackets `[ … ]`; the two are interchangeable for grouping.

### Operator precedence

The precedence levels are the same across all three modes (MSFL uses the same syntactic structure with Łukasiewicz semantics):

| Precedence | Operators | Associativity |
|---|---|---|
| 1 (highest) | `¬`, quantifiers `∀` / `∃` | prefix |
| 2 | `∧` `∨` `⊕` (FOL) / `∧` `∨` (MSFOL) / `∧` `∨` `⊗` `⊕` (MSFL / FL) | left |
| 3 | `→` | right |
| 4 (lowest) | `↔` | right |

Worked examples (parenthesised to show how the parser groups them):

- `¬P(x) ∧ Q(x)` → `(¬P(x)) ∧ Q(x)` — negation binds tighter than conjunction
- `P(x) ∧ Q(x) → R(x)` → `(P(x) ∧ Q(x)) → R(x)` — conjunction binds tighter than implication
- `P(x) → Q(x) ↔ R(x)` → `(P(x) → Q(x)) ↔ R(x)` — implication binds tighter than biconditional
- `P(x) → Q(x) → R(x)` → `P(x) → (Q(x) → R(x))` — implication is right-associative
- `P(x) ∧ Q(x) ∧ R(x)` → `(P(x) ∧ Q(x)) ∧ R(x)` — conjunction is left-associative

### Mixing same-level operators

The same-level connectives (level 2 above) **cannot be mixed without explicit parentheses**. This is deliberate: it avoids the silent, easy-to-misread grouping that a default precedence would impose.

**FOL mode** — `∧`, `∨`, `⊕` cannot be mixed:

```text
P(x) ∧ Q(x) ∨ R(x)      # rejected
(P(x) ∧ Q(x)) ∨ R(x)    # accepted
```

**MSFOL mode** — `∧` and `∨` cannot be mixed:

```text
P(x) ∧ Q(x) ∨ R(x)      # rejected
(P(x) ∧ Q(x)) ∨ R(x)    # accepted
```

**MSFL / FL mode** — `∧`, `∨`, `⊗`, `⊕` cannot be mixed:

```text
P(x) ∧ Q(x) ⊗ R(x)        # rejected
(P(x) ∧ Q(x)) ⊗ R(x)      # accepted
```

A chain of the *same* operator is always fine: `P ∧ Q ∧ R`, `P ⊗ Q ⊗ R`, etc.

### Quantifier scope

A quantifier binds **only the immediately following (tightly bound) formula**, not the rest of the line:

```text
∀x P(x) ∧ Q(x)      # parses as (∀x P(x)) ∧ Q(x)
∀x P(x) → Q(x)      # parses as (∀x P(x)) → Q(x)
```

If you intend the quantifier to range over the whole formula — which is usually what is meant — **add parentheses**:

```text
∀x (P(x) → Q(x))    # quantifier ranges over the implication
∀x (P(x) ∧ Q(x))    # quantifier ranges over the conjunction
```

Quantifiers can be stacked directly: `∀x:H ∀y:H ∃z:A φ`.

### Supported symbols

| Category | FOL | MSFOL | MSFL | FL |
|---|---|---|---|---|
| Quantifiers | `∀` `∃` (unsorted) | `∀` `∃` (sorted `:Sort`) | `∀` `∃` (sorted `:Sort`) | `∀` `∃` (unsorted) |
| Connectives | `∧` `∨` `⊕` `¬` `→` `↔` | `∧` `∨` `¬` `→` `↔` | `∧` `∨` `⊗` `⊕` `¬` `→` `↔` | `∧` `∨` `⊗` `⊕` `¬` `→` `↔` |
| Lambda | `λ` | `λ` | `λ` | `λ` |
| Sort annotations | — | `:Sort` | `:Sort` | — |
| Equality / comparison | `=` `≠` `<` `>` `≤` `≥` | same | same | same |
| Arithmetic | `+` `-` `*` `/` | same | same | same |
| Grouping | `(` `)` `[` `]` | same | same | same |
| Argument separator | `,` | same | same | same |

Whitespace is insignificant and may be used freely between tokens — including before sort annotation colons.

### Lambda abstraction and application (all modes)

A lambda abstraction is written `λ` followed by a parameter name, a literal `.`, and a body formula. All three parser modes support identical lambda surface notation.

#### Parameter types

| Parameter form | Example | Typical use |
|---|---|---|
| Single lowercase letter | `λx. P(x)` | value variable |
| Multi-letter lowercase name | `λfoo. P(foo(x))` | named-constant parameter |
| Uppercase predicate symbol | `λP. P(x)` | predicate / higher-order parameter |

All three token classes become a `LambdaVar` in the AST. Scope resolution (applied automatically by `parse()`) then rewrites body occurrences of the lambda-bound name:

- **Variable occurrence** — `λx. P(x)`: the `x` in `P(x)` becomes `LambdaVar("x")`.
- **Predicate-application occurrence** — `λP. P(x)`: the `P(x)` in the body becomes `Application(LambdaVar("P"), Variable("x"))`. Multi-argument atoms curry left: `P(x, y)` → `Application(Application(LambdaVar("P"), x), y)`.
- **Named-function occurrence** — `λfoo. P(foo(x))`: the `foo(x)` in `P`'s argument list (a term-level function call) becomes `Application(LambdaVar("foo"), Variable("x"))`.

The scope obeys the **innermost-binder rule**: a quantifier removes the quantified name from the lambda-bound set. Inside `λx. ∀x P(x)`, the `x` in `P(x)` is logical (stays `Variable`).

#### Body scope

The body extends rightward through all connectives — lambda has lower precedence than every binary operator:

```text
λx. P(x) ∧ Q(x)      # body is the And node P(x) ∧ Q(x)
λx. P(x) → Q(x)      # body is the Implies node P(x) → Q(x)
```

Multi-parameter lambdas are written by nesting: `λP. λx. P(x)`.

#### Application syntax

A lambda application requires both sides to be parenthesised: `(func)(arg)`.

```text
(λx. P(x))(a)         # arg is variable a
(λx. P(x))(alice)     # arg is constant alice
(λP. P(x))(Q)         # arg is the zero-arity atom Q
(λP. P(x))(Q(y))      # arg is the atom Q(y)
```

Higher-order application inside the body — a predicate parameter applied to arguments — is written in the natural `P(x)` notation, not as `(P)(x)`. Scope resolution handles the rewrite automatically.

#### Parse examples

```python
parser = MSFLParser()

parser.parse("λx. P(x)")
# Lambda(LambdaVar("x"), Atom("P", [LambdaVar("x")]))

parser.parse("λP. P(x)")
# Lambda(LambdaVar("P"), Application(LambdaVar("P"), Variable("x")))

parser.parse("λP. λx. P(x)")
# Lambda(LambdaVar("P"), Lambda(LambdaVar("x"), Application(LambdaVar("P"), LambdaVar("x"))))

parser.parse("λx. ∀x P(x)")
# Lambda(LambdaVar("x"), Quantifier("∀", Variable("x"), Atom("P", [Variable("x")])))
# x inside ∀ is quantifier-bound — NOT rewritten to LambdaVar

parser.parse("(λP. P(x))(Q)")
# Application(Lambda(LambdaVar("P"), Application(LambdaVar("P"), Variable("x"))), Atom("Q", []))
```

### A complete FOL example

```text
∀x ((Object(x) ∧ HasThreeDimensionalShape(x) ∧
     ∀y ∀z ((Point(y) ∧ OnSurfaceOf(y, x) ∧ Point(z) ∧ OnSurfaceOf(z, x))
            → distance(y, centerOf(x)) = distance(z, centerOf(x))))
    → Sphere(x))
```

### A complete MSFOL example

```text
∀x:Person ∀y:Person (Knows(x, y) ∧ Trusted(y)) → Shares(x, y)
```

### A complete MSFL example

```text
∀x:Patient ∀y:Treatment
    (Effective(y) ⊗ Tolerable(x, y))
    → Recommended(x, y)
```

### A complete FL example

```text
∀x ∀y
    (Effective(y) ⊗ Tolerable(x, y))
    → Recommended(x, y)
```

## AST nodes

All nodes are Python dataclasses and can be imported from `unicode_fol_kit`.

### Shared term and atom nodes (all modes)

| Class | Fields | Notes |
|---|---|---|
| `Variable` | `name: str` | bound or free variable |
| `Constant` | `name: str` | bare constant or c_-prefixed |
| `Number` | `value: int \| float` | numeric literal |
| `Function` | `name: str`, `args: list` | function application and arithmetic ops |
| `Atom` | `predicate: str`, `args: list` | predicate or infix comparison |

### Classical formula nodes (FOL / MSFOL)

| Class | Fields |
|---|---|
| `Not` | `formula` |
| `And` | `left`, `right` |
| `Or` | `left`, `right` |
| `Xor` | `left`, `right` *(FOL only)* |
| `Implies` | `left`, `right` |
| `Iff` | `left`, `right` |
| `Quantifier` | `type: str`, `variable`, `formula` *(FOL only)* |

### MSFOL / MSFL nodes

| Class | Fields | Notes |
|---|---|---|
| `SortedQuantifier` | `type: str`, `variable`, `sort: str`, `formula` | sort annotation without leading `:` |
| `SortedConstant` | `name: str`, `sort: str` | sort annotation without leading `:` |

### MSFL Łukasiewicz nodes

| Class | Fields | Semantics |
|---|---|---|
| `LukNegation` | `formula` | 1 − φ |
| `WeakConjunction` | `left`, `right` | min(φ, ψ) |
| `WeakDisjunction` | `left`, `right` | max(φ, ψ) |
| `StrongConjunction` | `left`, `right` | max(0, φ + ψ − 1) |
| `StrongDisjunction` | `left`, `right` | min(1, φ + ψ) |
| `LukImplication` | `left`, `right` | min(1, 1 − φ + ψ) |
| `LukEquivalence` | `left`, `right` | 1 − \|φ − ψ\| |

### Lambda-calculus nodes (all modes)

| Class | Fields | Notes |
|---|---|---|
| `LambdaVar` | `name: str` | lambda-bound variable; frozen and hashable — distinct from `Variable` |
| `Lambda` | `param: LambdaVar`, `body: Node` | lambda abstraction `λparam. body` |
| `Application` | `func: Node`, `arg: Node` | lambda application `func(arg)` |

`LambdaVar` is kept separate from `Variable` so that logical binding (by quantifiers) and lambda binding never get confused. `free_variables()` returns a mixed set that may contain both.

### Reductions

Every MSFL node implements two reduction steps:

- **`to_msfol()`** — lowers Łukasiewicz connectives to classical nodes while preserving sort annotations (`SortedQuantifier` and `SortedConstant` survive unchanged).
- **`_relativize(facts)`** — eliminates sort annotations by replacing `∀x:S φ` with `∀x (S(x) → φ)` and `∃x:S φ` with `∃x (S(x) ∧ φ)`, and replacing `SortedConstant(name, sort)` with a plain `Constant(name)`.

The top-level helper `to_fol(node, include_sort_facts=False)` chains both steps and optionally conjoins sort-membership atoms for all ground constants at the top level.

## Error handling

Parse errors are reported with human-readable messages rather than raw parser internals. Lexer-level problems (an invalid character, a malformed name or number) raise `NamingError`; structural problems (an incomplete formula, a misplaced operator, or an attempt to mix same-level connectives without parentheses) raise `ParsingError`. Both report the offending position and, where useful, a hint. The hint text is mode-aware:

```python
from unicode_fol_kit import MSFLParser

# FOL mode — hint names ∧, ∨, and ⊕
MSFLParser().parse("P(x) ∧ Q(x) ∨ R(x)")
# SYNTAX_ERROR: … Hint: Cannot mix conjunction (∧), disjunction (∨), and exclusive or (⊕) without parentheses

# MSFOL mode — hint names only ∧ and ∨
MSFLParser(many_sorted=True).parse("P(x) ∧ Q(x) ∨ R(x)")
# SYNTAX_ERROR: … Hint: Cannot mix conjunction (∧) and disjunction (∨) without parentheses

# MSFL mode — hint names all four Łukasiewicz connectives
MSFLParser(many_sorted=True, fuzzy=True).parse("P(x) ∧ Q(x) ⊗ R(x)")
# SYNTAX_ERROR: … Hint: Cannot mix weak conjunction (∧), weak disjunction (∨),
#                        strong conjunction (⊗), and strong disjunction (⊕) without parentheses

# FL mode — same hint as MSFL (Łukasiewicz connectives, unsorted)
MSFLParser(many_sorted=False, fuzzy=True).parse("P(x) ∧ Q(x) ⊗ R(x)")
# SYNTAX_ERROR: … Hint: Cannot mix weak conjunction (∧), weak disjunction (∨),
#                        strong conjunction (⊗), and strong disjunction (⊕) without parentheses
```

## Citation

If you use this toolkit in academic work, please cite the accompanying preprint:

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
