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

The constructor rejects an unsupported combination with a clear `ValueError`. The two extension modes are classical unsorted FOL plus their own operators, so neither can be sorted or fuzzy:

```python
from unicode_fol_kit import MSFLParser

for kwargs in [dict(modal=True, many_sorted=True),
               dict(second_order=True, fuzzy=True),
               dict(modal=True, fuzzy=True)]:
    try:
        MSFLParser(**kwargs)            # raises
    except ValueError as e:
        print(str(e)[:46])
# → modal=True cannot be combined with many_sort
# → second_order=True cannot be combined with man
# → modal=True cannot be combined with many_sort
```

## Unicode surface syntax

Formulas are written with natural symbols — `∀ ∃ ∧ ∨ ¬ → ↔ ⊕ ⊗ = ≠ ≤ ≥` — with no ASCII fallbacks required. Predicates are uppercase-initial and applied with parentheses; the lowercase identifier rules below decide whether a bare lowercase token is a variable or a constant.

```python
parser = MSFLParser()
parser.parse("∀x (Human(x) → Mortal(x))")
# → Quantifier(type='∀', variable=Variable(name='x'),
#              formula=Implies(left=Atom(predicate='Human', args=(Variable(name='x'),)),
#                              right=Atom(predicate='Mortal', args=(Variable(name='x'),))))
```

### The three lowercase identifier classes

A bare lowercase token resolves to one of three terminal classes — and therefore one of three node types — purely by its spelling:

- **`VARIABLE`** — a single lowercase letter, optionally followed by digits (`x`, `y`, `x2`). It becomes a `Variable`.
- **`NAME`** — a multi-character lowercase identifier with a non-leading letter (`alice`, `socrates`). It becomes a `Constant` (and, when applied with parentheses, the head of a `Function`).
- **`CONSTANT`** — the explicit `c_`-prefix form (`c_7`, `c_alice`). It becomes a `Constant` too, and is the way to force a single-symbol name to be a constant.

```python
parser = MSFLParser()

parser.parse("P(x)")          # → Atom(predicate='P', args=(Variable(name='x'),))
parser.parse("P(x2)")         # → Atom(predicate='P', args=(Variable(name='x2'),))
parser.parse("P(alice)")      # → Atom(predicate='P', args=(Constant(name='alice'),))
parser.parse("P(c_7)")        # → Atom(predicate='P', args=(Constant(name='c_7'),))
parser.parse("P(c_alice)")    # → Atom(predicate='P', args=(Constant(name='c_alice'),))
```

Because a single lowercase letter is always a *variable*, a function symbol must be a multi-character `NAME`; `f(x)` is a parse error (`f` is a variable, which cannot be applied), whereas `father(x)` is a `Function`:

```python
parser = MSFLParser()
parser.parse("father(x) = bob")
# → Atom(predicate='=',
#        args=(Function(name='father', args=(Variable(name='x'),)),
#              Constant(name='bob')))
```

### Comparisons and arithmetic

The six infix comparison glyphs `= ≠ < > ≤ ≥` build a binary `Atom` whose predicate is the glyph itself; the four arithmetic operators `+ - * /` build a `Function` whose name is the glyph, with the usual precedence (`*`/`/` bind tighter than `+`/`-`):

```python
parser = MSFLParser()

parser.parse("x ≤ y")
# → Atom(predicate='≤', args=(Variable(name='x'), Variable(name='y')))

parser.parse("x ≠ y")
# → Atom(predicate='≠', args=(Variable(name='x'), Variable(name='y')))

parser.parse("x + y * 2 < z")
# → Atom(predicate='<',
#        args=(Function(name='+',
#                       args=(Variable(name='x'),
#                             Function(name='*', args=(Variable(name='y'), Number(value=2))))),
#              Variable(name='z')))
```

### Tight quantifier scope

A quantifier binds only the immediately following prefix-level formula, not the rest of the line: `∀x P(x) ∧ Q(x)` is `(∀x P(x)) ∧ Q(x)`, with the second `Q(x)` *outside* the quantifier. Add parentheses to extend the scope.

```python
parser = MSFLParser()

parser.parse("∀x P(x) ∧ Q(x)")
# → And(left=Quantifier(type='∀', variable=Variable(name='x'),
#                       formula=Atom(predicate='P', args=(Variable(name='x'),))),
#       right=Atom(predicate='Q', args=(Variable(name='x'),)))

parser.parse("∀x (P(x) ∧ Q(x))")
# → Quantifier(type='∀', variable=Variable(name='x'),
#              formula=And(left=Atom(predicate='P', args=(Variable(name='x'),)),
#                          right=Atom(predicate='Q', args=(Variable(name='x'),))))
```

Both parentheses `( … )` and square brackets `[ … ]` group identically:

```python
parser = MSFLParser()
parser.parse("[P(x) ∧ Q(x)]") == parser.parse("(P(x) ∧ Q(x))")   # → True
```

### MSFOL — sorted quantifiers and constants, and `to_fol` lowering

In many-sorted mode quantifiers and ground constants must carry a sort annotation. The colon may be written with or without a space before it.

```python
parser = MSFLParser(many_sorted=True)

parser.parse("∀x:Human (Mortal(x) ∧ ¬Immortal(x))")
# → SortedQuantifier(type='∀', variable=Variable(name='x'), sort='Human',
#                    formula=And(left=Atom(predicate='Mortal', args=(Variable(name='x'),)),
#                                right=Not(formula=Atom(predicate='Immortal', args=(Variable(name='x'),)))))

parser.parse("P(alice:Human)") == parser.parse("P(alice :Human)")  # both spacings parse → True
parser.parse("P(alice:Human)")
# → Atom(predicate='P', args=(SortedConstant(name='alice', sort='Human'),))
```

`to_fol` *relativises* a sorted formula to plain FOL: a `∀x:S` becomes a guarded `∀x (S(x) → …)`, a `∃x:S` becomes `∃x (S(x) ∧ …)`, and a `SortedConstant` drops to a plain `Constant`.

```python
from unicode_fol_kit import MSFLParser, to_fol

m = MSFLParser(many_sorted=True)

to_fol(m.parse("∀x:Human Mortal(x)"))
# → Quantifier(type='∀', variable=Variable(name='x'),
#              formula=Implies(left=Atom(predicate='Human', args=(Variable(name='x'),)),
#                              right=Atom(predicate='Mortal', args=(Variable(name='x'),))))

to_fol(m.parse("∃x:Human Happy(x)"))
# → Quantifier(type='∃', variable=Variable(name='x'),
#              formula=And(left=Atom(predicate='Human', args=(Variable(name='x'),)),
#                          right=Atom(predicate='Happy', args=(Variable(name='x'),))))

to_fol(m.parse("Mortal(socrates:Human)"))
# → Atom(predicate='Mortal', args=(Constant(name='socrates'),))
```

Passing `include_sort_facts=True` conjoins the collected sort-membership atoms (e.g. `Human(socrates)`) onto the result:

```python
to_fol(m.parse("Mortal(socrates:Human)"), include_sort_facts=True)
# → And(left=Atom(predicate='Human', args=(Constant(name='socrates'),)),
#       right=Atom(predicate='Mortal', args=(Constant(name='socrates'),)))
```

### MSFL / FL — Łukasiewicz operators

In the fuzzy modes `∧`/`∨` are the weak (min/max) connectives, `⊗`/`⊕` the strong (t-norm/t-conorm) connectives, and `¬`/`→`/`↔` their Łukasiewicz counterparts. Each glyph maps to a distinct node class — the same `∧` glyph is `And` in FOL but `WeakConjunction` here.

```python
parser = MSFLParser(many_sorted=True, fuzzy=True)   # MSFL

type(parser.parse("P(x) ∧ Q(x)")).__name__   # → 'WeakConjunction'    (min)
type(parser.parse("P(x) ∨ Q(x)")).__name__   # → 'WeakDisjunction'    (max)
type(parser.parse("P(x) ⊗ Q(x)")).__name__   # → 'StrongConjunction'  (t-norm: max{0, x+y−1})
type(parser.parse("P(x) ⊕ Q(x)")).__name__   # → 'StrongDisjunction'  (t-conorm: min{1, x+y})
type(parser.parse("¬P(x)")).__name__          # → 'LukNegation'        (1−x)
type(parser.parse("P(x) → Q(x)")).__name__   # → 'LukImplication'     (min{1, 1−x+y})
type(parser.parse("P(x) ↔ Q(x)")).__name__   # → 'LukEquivalence'
type(parser.parse("∀x:Human P(x)")).__name__  # → 'SortedQuantifier'
```

`to_msfol()` lowers every Łukasiewicz node to its classical counterpart (this is the first half of what `to_fol` does), leaving the structure otherwise unchanged:

```python
parser = MSFLParser(many_sorted=True, fuzzy=True)
luk = parser.parse("¬P(x) → Q(x)")
type(luk).__name__               # → 'LukImplication'
type(luk.to_msfol()).__name__    # → 'Implies'
# → Implies(left=Not(formula=Atom(predicate='P', args=(Variable(name='x'),))),
#           right=Atom(predicate='Q', args=(Variable(name='x'),)))
```

FL is the same connectives with unsorted quantifiers and plain constants:

```python
parser = MSFLParser(fuzzy=True)        # FL
parser.parse("∀x P(x)")                # → unsorted Quantifier (no sort annotation)
type(parser.parse("P(x) ⊗ Q(x)")).__name__   # → 'StrongConjunction'
parser.parse("P(alice)")               # → Atom(predicate='P', args=(Constant(name='alice'),))
```

### Modal, temporal, epistemic, deontic

Modal mode is classical unsorted FOL plus the prefix operators `□ ◇` (alethic), `Ⓖ Ⓕ Ⓝ` (temporal future), `Ⓞ Ⓟ` (deontic), the agent operators `K_a B_a`, and the infix temporal `Ⓤ` (until).

```python
modal = MSFLParser(modal=True)

modal.parse("□P → ◇Q")
# → Implies(left=Box(formula=Atom(predicate='P', args=())),
#           right=Diamond(formula=Atom(predicate='Q', args=())))

type(modal.parse("Ⓖ P(a)")).__name__       # → 'Always'
type(modal.parse("Ⓞ P(a)")).__name__       # → 'Obligatory'
type(modal.parse("P(a) Ⓤ Q(a)")).__name__  # → 'Until'
```

The agent of `K_a`/`B_a` is a **term**, not a bare string. A *free* agent denotes a named individual (a `Constant`), while an agent bound by an enclosing quantifier stays a `Variable` — so `K_x` genuinely quantifies over agents:

```python
modal = MSFLParser(modal=True)

modal.parse("K_a P(a)")
# → Knows(agent=Constant(name='a'), formula=Atom(predicate='P', args=(Variable(name='a'),)))

modal.parse("∀x (Student(x) → K_x Smart(x))")
# → Quantifier(type='∀', variable=Variable(name='x'),
#              formula=Implies(left=Atom(predicate='Student', args=(Variable(name='x'),)),
#                              right=Knows(agent=Variable(name='x'),
#                                          formula=Atom(predicate='Smart', args=(Variable(name='x'),)))))
```

(The free `K_a P(a)` resolves the agent `a` to a `Constant` even though the same letter `a` *inside* `P(a)` stays a `Variable` — agent position and term position are resolved independently.)

### Second-order — arity inference and `ConflictingArityError`

Second-order mode adds `∀P / ∃P` over a predicate variable. The bound predicate's arity is **inferred** from its applications in the body and recorded on the node (it is not part of the surface syntax):

```python
so = MSFLParser(second_order=True)

so.parse("∀P (P(a) ∨ ¬P(a))")
# → SecondOrderQuantifier(type='∀', predicate='P', arity=1, formula=Or(...))

so.parse("∃R ∀x R(x,x)")
# → SecondOrderQuantifier(type='∃', predicate='R', arity=2, formula=Quantifier(...))

so.parse("∀P (P ∨ ¬P)")
# → SecondOrderQuantifier(type='∀', predicate='P', arity=0, formula=Or(...))   (never applied ⇒ arity 0)
```

If the same bound predicate is applied at two different arities the inference fails with `ConflictingArityError` (a subclass of `ParsingError`, so a caller catching the parser's error type also catches this):

```python
from unicode_fol_kit import MSFLParser, ParsingError
from unicode_fol_kit.fol.msflparser import ConflictingArityError

so = MSFLParser(second_order=True)
try:
    so.parse("∀P (P(a) ∧ P(a,b))")    # raises
except ConflictingArityError as e:
    print(str(e)[:78])
# → SYNTAX_ERROR: Second-order predicate variable 'P' is applied at conflicting

issubclass(ConflictingArityError, ParsingError)   # → True
```

## Natural-language constructs

Classical FOL mode (`many_sorted=False, fuzzy=False`) carries four extra surface forms used by natural-language → logic front-ends. They are FOL-mode only.

### Counting quantifier `∃≥n / ∃≤n / ∃=n`

The counting quantifier binds a variable and carries its bound `n` **symbolically** (a `Number`, not expanded), so an arbitrarily large `n` round-trips exactly:

```python
parser = MSFLParser()

parser.parse("∃≥2 x P(x)")
# → Count(op='ge', n=Number(value=2), variable=Variable(name='x'),
#         formula=Atom(predicate='P', args=(Variable(name='x'),)))

parser.parse("∃≤3 x P(x)")    # → Count(op='le', n=Number(value=3), …)
parser.parse("∃=1 x P(x)")    # → Count(op='eq', n=Number(value=1), …)
```

It is first-order expressible; the first-order exporters lower it to the distinct-witnesses encoding on demand (the AST keeps `n` symbolic):

```python
parser = MSFLParser()
print(parser.parse("∃≥2 x P(x)").to_tptp())
# → (?[X_0]: (?[X_1]: ((p(X_0) & p(X_1)) & (X_0 != X_1))))
```

### Measure term `μ(entity, dimension)`

A degree/measure term for bare comparatives (`taller`, `more water`) — an uninterpreted binary function on export. Both children are terms; the result is typically compared with `>`/`<`:

```python
parser = MSFLParser()
parser.parse("μ(x, height) > μ(y, height)")
# → Atom(predicate='>',
#        args=(Measure(entity=Variable(name='x'), dimension=Constant(name='height')),
#              Measure(entity=Variable(name='y'), dimension=Constant(name='height'))))
```

### Set-cardinality term `|{v : φ}|`

A set-cardinality term for faithful counting comparisons (`more votes than`). It *binds* its variable over the matrix. Set cardinality is genuinely second-order, so it has no first-order export:

```python
parser = MSFLParser()
parser.parse("|{v : Votes(x, v)}| > |{v : Votes(y, v)}|")
# → Atom(predicate='>',
#        args=(Cardinality(variable=Variable(name='v'),
#                          formula=Atom(predicate='Votes', args=(Variable(name='x'), Variable(name='v')))),
#              Cardinality(variable=Variable(name='v'),
#                          formula=Atom(predicate='Votes', args=(Variable(name='y'), Variable(name='v'))))))
```

Exporting a `Cardinality` to a first-order back-end raises — it is not first-order definable:

```python
parser = MSFLParser()
card = parser.parse("|{v : P(v)}| > |{v : Q(v)}|")
try:
    card.to_tptp()    # raises
except NotImplementedError as e:
    print(str(e)[:55])
# → Cardinality terms (|{v : φ}|) denote set cardinalit
```

### Concessive connective `Ⓒ`

A concessive (contrastive) connective — *whereas / although / but*. It is truth-functionally identical to `∧`, but kept as a distinct node so a front-end can preserve the concession rather than flattening it:

```python
parser = MSFLParser()
parser.parse("P(x) Ⓒ Q(x)")
# → Contrast(left=Atom(predicate='P', args=(Variable(name='x'),)),
#            right=Atom(predicate='Q', args=(Variable(name='x'),)))
```

## Lambda syntax

Every mode supports lambda abstraction with `λx. φ`. The parameter can be a variable (`λx.`), a named constant (`λfoo.`), or a predicate symbol (`λP.`); the body extends rightward through all connectives. `parse()` applies scope resolution automatically, so the returned AST is fully resolved.

```python
parser = MSFLParser()

parser.parse("λx. P(x)")
# → Lambda(param=LambdaVar(name='x'), body=Atom(predicate='P', args=(LambdaVar(name='x'),)))

parser.parse("λfoo. P(foo)")
# → Lambda(param=LambdaVar(name='foo'), body=Atom(predicate='P', args=(Constant(name='foo'),)))

parser.parse("λP. P(x)")   # P used in predicate position
# → Lambda(param=LambdaVar(name='P'), body=Application(func=LambdaVar(name='P'), arg=Variable(name='x')))
```

It works in the fuzzy and extension modes too:

```python
type(MSFLParser(fuzzy=True).parse("λx. P(x) ⊗ Q(x)").body).__name__   # → 'StrongConjunction'

MSFLParser(modal=True).parse("λx. □P(x)")
# → Lambda(param=LambdaVar(name='x'), body=Box(formula=Atom(predicate='P', args=(LambdaVar(name='x'),))))

MSFLParser(second_order=True).parse("λP. P(x)")
# → Lambda(param=LambdaVar(name='P'), body=Application(func=LambdaVar(name='P'), arg=Variable(name='x')))
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

The label format is node-specific — a counting quantifier shows `∃≥n`, a `Knows` shows its agent, and a second-order quantifier shows the bound predicate with its inferred arity:

```python
print(MSFLParser().parse("∃≥2 x P(x)").tree_str())
# ∃≥2 x
# └── Atom: P
#     └── Variable: x

print(MSFLParser(modal=True).parse("K_alice Smart(alice)").tree_str())
# K_alice
# └── Atom: Smart
#     └── Constant: alice

print(MSFLParser(second_order=True).parse("∃R ∀x R(x,x)").tree_str())
# ∃ R/2
# └── ∀ x
#     └── Atom: R
#         ├── Variable: x
#         └── Variable: x
```

## Graphviz DOT view

`to_dot()` renders the same label/child view as a Graphviz `digraph` source string (no external dependency — it returns the source, which you can pipe to `dot`):

```python
print(MSFLParser().parse("P(x) ∧ Q(x)").to_dot())
# digraph AST {
#   node [shape=box];
#   n0 [label="∧"];
#   n1 [label="Atom: P"];
#   n2 [label="Variable: x"];
#   n1 -> n2;
#   n0 -> n1;
#   n3 [label="Atom: Q"];
#   n4 [label="Variable: x"];
#   n3 -> n4;
#   n0 -> n3;
# }
```

## Inspection API

Every node exposes a small structural-inspection API. `walk()` yields the node and every descendant in pre-order; `subformulas()` is the same but excludes atomic terms; `atoms()` / `variables()` collect those leaf families; `count()` and `depth()` give size and height; a leaf has depth 1.

```python
phi = MSFLParser().parse("∀x (Human(x) → Mortal(x))")

phi.depth()                                    # → 4
phi.count()                                    # → 7   (all nodes)
phi.count(Atom)                                # → 2   (only Atoms)
[a.predicate for a in phi.atoms()]             # → ['Human', 'Mortal']
sorted(v.name for v in phi.variables())        # → ['x']
[type(n).__name__ for n in phi.subformulas()]  # → ['Quantifier', 'Implies', 'Atom', 'Atom']
[type(n).__name__ for n in phi.walk()]
# → ['Quantifier', 'Variable', 'Implies', 'Atom', 'Variable', 'Atom', 'Variable']
```

`count` takes an optional class to filter by, and `Atom` is importable from the top level:

```python
from unicode_fol_kit import MSFLParser, Atom, Variable

phi = MSFLParser().parse("∀x (Human(x) → Mortal(x))")
phi.count(Variable)   # → 3   (one bound + two occurrences)
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
parser.parse("∀x (P(x) ∧ Q(x))").to_unicode_str()       # → '∀x (P(x) ∧ Q(x))'  (scope paren kept)
```

The round-trip holds in every mode (each re-parsed in its matching parser):

```python
MSFLParser(modal=True).parse("□P → ◇Q").to_unicode_str()                  # → '□P → ◇Q'
MSFLParser(modal=True).parse("∀x (Student(x) → K_x Smart(x))").to_unicode_str()
# → '∀x (Student(x) → K_x Smart(x))'
MSFLParser(second_order=True).parse("∃R ∀x R(x,x)").to_unicode_str()      # → '∃R ∀x R(x, x)'
MSFLParser(many_sorted=True, fuzzy=True).parse("∀x:Human (P(x) ⊗ Q(x))").to_unicode_str()
# → '∀x:Human (P(x) ⊗ Q(x))'
```

The natural-language constructs round-trip too:

```python
parser = MSFLParser()
parser.parse("∃≥2 x P(x)").to_unicode_str()                            # → '∃≥2 x P(x)'
parser.parse("P(x) Ⓒ Q(x)").to_unicode_str()                          # → 'P(x) Ⓒ Q(x)'
parser.parse("μ(x, height) > μ(y, height)").to_unicode_str()          # → 'μ(x, height) > μ(y, height)'
parser.parse("|{v : Votes(x, v)}| > |{v : Votes(y, v)}|").to_unicode_str()
# → '|{v : Votes(x, v)}| > |{v : Votes(y, v)}|'
```

`to_unicode_str()` is available on every node, so subformulas render too. The output targets parseable ASTs; alpha-renamed variables introduced by reduction (e.g. `x_0`) are not valid surface tokens and will not round-trip.

```python
phi = MSFLParser().parse("∀x (Human(x) → Mortal(x))")
phi.formula.to_unicode_str()    # → 'Human(x) → Mortal(x)'  (the body subformula alone)
```

## JSON round-trip

`to_dict()` produces a JSON-serialisable dict keyed by a `_type` discriminator; `Node.from_dict()` rebuilds the AST. The round-trip is structure-preserving across all node families (including modal and second-order nodes that the TPTP/Prover9 exporters cannot represent).

```python
from unicode_fol_kit import MSFLParser, Node
import json

formula = MSFLParser().parse("P(x) ∧ Q(x)")
d = formula.to_dict()
# {'_type': 'And',
#  'left':  {'_type': 'Atom', 'predicate': 'P', 'args': [{'_type': 'Variable', 'name': 'x'}]},
#  'right': {'_type': 'Atom', 'predicate': 'Q', 'args': [{'_type': 'Variable', 'name': 'x'}]}}

Node.from_dict(d) == formula                       # → True
Node.from_dict(json.loads(json.dumps(d))) == formula   # → True  (survives a JSON string)
```

It holds for the extension and natural-language nodes too — including the inferred arity on a second-order quantifier and the symbolic `n` on a counting quantifier:

```python
from unicode_fol_kit import MSFLParser, Node

m = MSFLParser(modal=True).parse("□P → ◇Q")
Node.from_dict(m.to_dict()) == m                   # → True

soq = MSFLParser(second_order=True).parse("∃R ∀x R(x,x)")
soq.to_dict()["arity"]                             # → 2  (inferred arity is serialised)
Node.from_dict(soq.to_dict()) == soq               # → True

cnt = MSFLParser().parse("∃=1 x P(x)")
Node.from_dict(cnt.to_dict()) == cnt               # → True
```

## The error model: `NamingError` vs `ParsingError`

`parse()` raises one of two errors. `NamingError` is a **lexer-level** failure — an unrecognised character, a malformed identifier, or a token that cannot start where it appears. `ParsingError` is a **parser-level** failure — a structurally incomplete formula (unexpected token or end of input). They are distinct classes (`NamingError` is *not* a subclass of `ParsingError`), so catch both if you want to handle any malformed input.

```python
from unicode_fol_kit import MSFLParser, NamingError, ParsingError

parser = MSFLParser()

try:
    parser.parse("P(x) % Q(x)")      # raises — stray character
except NamingError as e:
    print("NamingError :", str(e)[:52])
# → NamingError : SYNTAX_ERROR: Unexpected character '%' at positi

try:
    parser.parse("∀x")               # raises — quantifier with no body
except ParsingError as e:
    print("ParsingError:", str(e)[:52])
# → ParsingError: SYNTAX_ERROR: Incomplete formula - the input end
```

The **no-mixing rule** — same-level connectives `∧ ∨ ⊕` cannot be combined without explicit parentheses — surfaces as a `NamingError`, because the offending connective is rejected by the lexer at the point where mixing would begin. The message carries a hint naming the rule:

```python
from unicode_fol_kit import MSFLParser, NamingError

parser = MSFLParser()
try:
    parser.parse("P(x) ∧ Q(x) ∨ R(x)")    # raises — ∧ and ∨ mixed without parens
except NamingError as e:
    print(str(e))
# → SYNTAX_ERROR: Unexpected character '∨' at position 13 after closing parenthesis ')'. Hint: Cannot mix conjunction (∧), disjunction (∨), and exclusive or (⊕) without parentheses
```

Parenthesising the mixed group resolves it; the resulting AST reflects the chosen grouping:

```python
parser = MSFLParser()
parser.parse("(P(x) ∧ Q(x)) ∨ R(x)")
# → Or(left=And(left=Atom(predicate='P', args=(Variable(name='x'),)),
#               right=Atom(predicate='Q', args=(Variable(name='x'),))),
#      right=Atom(predicate='R', args=(Variable(name='x'),)))
```
