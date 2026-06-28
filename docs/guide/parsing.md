# Parsing and the AST

`MSFLParser` turns a Unicode formula string into a typed AST of Python dataclasses. One parser class covers six modes — classical FOL, many-sorted FOL (MSFOL), many-sorted fuzzy logic (MSFL), single-sorted fuzzy logic (FL), modal/temporal/epistemic/deontic logic, and second-order logic — each selected by constructor flags.

## Parser modes

The four core modes form the `many_sorted` × `fuzzy` matrix; two further modes — modal and second-order — are each enabled by their own flag and are mutually exclusive with the others.

```python
from unicode_fol_kit import MSFLParser

MSFLParser(many_sorted=False, fuzzy=False)   # FOL   (default)
MSFLParser(many_sorted=True,  fuzzy=False)   # MSFOL
MSFLParser(many_sorted=True,  fuzzy=True)    # MSFL
MSFLParser(many_sorted=False, fuzzy=True)    # FL
MSFLParser(modal=True)                       # modal / temporal / epistemic / deontic
MSFLParser(second_order=True)                # second-order (∀P / ∃P)
```

| `many_sorted` | `fuzzy` | Mode | Quantifiers | Constants | Connectives |
|---|---|---|---|---|---|
| `False` | `False` | **FOL** | unsorted `∀x` | unsorted | classical ∧ ∨ ⊕ ¬ → ↔ |
| `True` | `False` | **MSFOL** | sorted `∀x:Sort` | sorted `alice:Sort` | classical ∧ ∨ ¬ → ↔ |
| `True` | `True` | **MSFL** | sorted `∀x:Sort` | sorted `alice:Sort` | weak ∧ ∨, strong ⊗ ⊕, Łuk ¬ → ↔ |
| `False` | `True` | **FL** | unsorted `∀x` | unsorted | weak ∧ ∨, strong ⊗ ⊕, Łuk ¬ → ↔ |

The two extension modes are classical unsorted FOL plus their own operators:

- **modal** (`modal=True`) — adds `□ ◇` (alethic), `K_a B_a` (epistemic/doxastic), `Ⓖ Ⓕ Ⓝ Ⓤ` (temporal), and `Ⓞ Ⓟ` (deontic). The agent of `K_a`/`B_a` is a first-class term, so a bound `K_x` quantifies over agents.
- **second-order** (`second_order=True`) — adds `∀P / ∃P` over predicate variables (arity inferred from use).

The constructor rejects an unsupported combination (e.g. `modal=True, many_sorted=True`) with a clear `ValueError`.

## Unicode surface syntax

Formulas are written with natural symbols — `∀ ∃ ∧ ∨ ¬ → ↔ ⊕ ⊗ = ≠ ≤ ≥` — with no ASCII fallbacks required. Predicates are uppercase-initial and applied with parentheses; a single lowercase letter (`x`, `y`) is a logical variable, while a multi-character lowercase name (`alice`, `socrates`) is a constant.

```python
parser = MSFLParser()
parser.parse("∀x (Human(x) → Mortal(x))")
# Quantifier(type='∀', variable=Variable('x'), formula=Implies(...))
```

### MSFOL — sorted quantifiers and constants

Quantifiers and ground constants must carry a sort annotation. The colon may be written with or without a space before it.

```python
parser = MSFLParser(many_sorted=True)

q = parser.parse("∀x:Human (Mortal(x) ∧ ¬Immortal(x))")
# SortedQuantifier(type='∀', variable=Variable('x'), sort='Human', formula=…)

parser.parse("P(alice:Human)") == parser.parse("P(alice :Human)")  # both spacings parse
parser.parse("P(alice:Human)")
# Atom(predicate='P', args=(SortedConstant(name='alice', sort='Human'),))
```

### MSFL / FL — Łukasiewicz operators

In the fuzzy modes `∧`/`∨` are the weak (min/max) connectives, `⊗`/`⊕` the strong (t-norm/t-conorm) connectives, and `¬`/`→`/`↔` their Łukasiewicz counterparts. MSFL adds sorts; FL keeps the unsorted FOL quantifier/constant syntax.

```python
parser = MSFLParser(many_sorted=True, fuzzy=True)   # MSFL

parser.parse("P(x) ∧ Q(x)")    # WeakConjunction   (min)
parser.parse("P(x) ⊗ Q(x)")    # StrongConjunction (t-norm: max{0, x+y−1})
parser.parse("P(x) ⊕ Q(x)")    # StrongDisjunction (t-conorm: min{1, x+y})
parser.parse("¬P(x)")           # LukNegation       (1−x)
parser.parse("P(x) → Q(x)")    # LukImplication    (min{1, 1−x+y})
parser.parse("∀x:Human P(x)")  # SortedQuantifier
```

FL is the same connectives with unsorted quantifiers and plain constants:

```python
parser = MSFLParser(fuzzy=True)        # FL
parser.parse("∀x P(x)")                # unsorted Quantifier (no sort annotation)
parser.parse("P(alice)")               # plain Constant
```

### Modal and second-order

```python
modal = MSFLParser(modal=True)
modal.parse("□P → ◇Q")                          # Implies(Box(...), Diamond(...))
modal.parse("K_a P(b)")                          # Knows(agent='a', ...)
modal.parse("∀x (Student(x) → K_x Smart(x))")   # K_x — the bound x is the agent

so = MSFLParser(second_order=True)
so.parse("∀P (P(a) ∨ ¬P(a))")                   # SecondOrderQuantifier (predicate var P)
so.parse("∃R ∀x R(x,x)")                         # arity inferred from R(x,x)
```

## Lambda syntax

Every mode supports lambda abstraction with `λx. φ`. The parameter can be a variable (`λx.`), a named constant (`λfoo.`), or a predicate symbol (`λP.`); the body extends rightward through all connectives. `parse()` applies scope resolution automatically, so the returned AST is fully resolved.

```python
parser = MSFLParser()
parser.parse("λx. P(x)")
# Lambda(param=LambdaVar('x'), body=Atom('P', (LambdaVar('x'),)))

parser.parse("λfoo. P(foo)")
# Lambda(param=LambdaVar('foo'), body=Atom('P', (Constant('foo'),)))

parser.parse("λP. P(x)")   # P used in predicate position
# Lambda(param=LambdaVar('P'), body=Application(LambdaVar('P'), Variable('x')))
```

It works in the fuzzy and extension modes too:

```python
MSFLParser(fuzzy=True).parse("λx. P(x) ⊗ Q(x)")   # body uses the strong conjunction
MSFLParser(modal=True).parse("λx. □P(x)")
MSFLParser(second_order=True).parse("λP. P(x)")
```

## ASCII tree view

`tree_str()` renders any node as a readable ASCII tree; `print` it to display. (A quantifier folds its bound variable — and, in MSFOL/MSFL, its sort — into the node label.)

```python
formula = MSFLParser().parse("∀x (Human(x) → Mortal(x))")
print(formula.tree_str())
# ∀ x
# └── →
#     ├── Atom: Human
#     │   └── Variable: x
#     └── Atom: Mortal
#         └── Variable: x

print(MSFLParser(many_sorted=True).parse("∀x:Human (Mortal(x) ∧ ¬Immortal(x))").tree_str())
# ∀ x:Human
# └── ∧
#     ├── Atom: Mortal
#     │   └── Variable: x
#     └── ¬
#         └── Atom: Immortal
#             └── Variable: x
```

## Unicode round-trip

`to_unicode_str()` is the inverse of parsing: it renders any node back to a Unicode formula string, and re-parsing that string in the same mode reproduces a structurally equal AST. The renderer is precedence-aware and inserts only the parentheses the grammar requires — including the no-mixing rule for same-level connectives and the tight-binding rule for quantifiers, so the reconstructed parenthesisation reflects the AST rather than the original spelling.

```python
parser = MSFLParser()

ast = parser.parse("∀x P(x) ∧ Q(x)")
ast.to_unicode_str()                          # → '∀x P(x) ∧ Q(x)'
parser.parse(ast.to_unicode_str()) == ast     # → True

parser.parse("((P(x) ∧ Q(x)))").to_unicode_str()        # → 'P(x) ∧ Q(x)'  (redundant parens dropped)
parser.parse("P(x) ∧ (Q(x) ∨ R(x))").to_unicode_str()   # → 'P(x) ∧ (Q(x) ∨ R(x))'  (required paren kept)
```

The round-trip holds in every mode (each re-parsed in its matching parser):

```python
MSFLParser(modal=True).parse("□P → ◇Q").to_unicode_str()                 # → '□P → ◇Q'
MSFLParser(second_order=True).parse("∀P (P(a) ∨ ¬P(a))").to_unicode_str() # → '∀P (P(a) ∨ ¬P(a))'
MSFLParser(many_sorted=True, fuzzy=True).parse("∀x:Human (P(x) ⊗ Q(x))").to_unicode_str()
# → '∀x:Human (P(x) ⊗ Q(x))'
```

`to_unicode_str()` is available on every node, so subformulas render too. The output targets parseable ASTs; alpha-renamed variables introduced by reduction (e.g. `x_0`) are not valid surface tokens and will not round-trip.

## JSON round-trip

`to_dict()` produces a JSON-serialisable dict keyed by a `_type` discriminator; `Node.from_dict()` rebuilds the AST. The round-trip is structure-preserving across all node families (including modal and second-order nodes that the TPTP/Prover9 exporters cannot represent).

```python
from unicode_fol_kit import MSFLParser, Node

formula = MSFLParser().parse("P(x) ∧ Q(x)")
d = formula.to_dict()
# {'_type': 'And',
#  'left':  {'_type': 'Atom', 'predicate': 'P', 'args': [{'_type': 'Variable', 'name': 'x'}]},
#  'right': {'_type': 'Atom', 'predicate': 'Q', 'args': [{'_type': 'Variable', 'name': 'x'}]}}

Node.from_dict(d) == formula                  # → True

# Holds for modal nodes too:
m = MSFLParser(modal=True).parse("□P → ◇Q")
Node.from_dict(m.to_dict()) == m              # → True
```
