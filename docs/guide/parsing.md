# Parsing and the AST

`MSFLParser` turns a Unicode formula string into a typed AST of Python dataclasses. One parser class covers nine modes — classical FOL, many-sorted FOL (MSFOL), many-sorted fuzzy logic (MSFL), single-sorted fuzzy logic (FL), modal/temporal/epistemic/deontic/hybrid/counterfactual/PAL logic, second-order logic, dependence/IF logic, intuitionistic linear logic, and the Lambek calculus — each selected by constructor flags.

## Parser modes

The four core modes form the `many_sorted` × `fuzzy` matrix; five further modes — modal, second-order, dependence, linear and Lambek — are each enabled by their own flag and are mutually exclusive with the others.

```python
from unicode_fol_kit import MSFLParser

MSFLParser(many_sorted=False, fuzzy=False)   # FOL   (default)
MSFLParser(many_sorted=True,  fuzzy=False)   # MSFOL
MSFLParser(many_sorted=True,  fuzzy=True)    # MSFL
MSFLParser(many_sorted=False, fuzzy=True)    # FL
MSFLParser(modal=True)                       # modal / temporal / epistemic / deontic / hybrid / □→ / [φ!]ψ
MSFLParser(second_order=True)                # second-order (∀P / ∃P)
MSFLParser(dependence=True)                  # dependence/IF logic (=(x,y), ∃x/{y})
MSFLParser(linear=True)                      # intuitionistic linear logic (⊗ ⊸ & ⊕ ! 𝟙 ⊤ 𝟘)
MSFLParser(lambek=True)                      # Lambek calculus (• \ /)
```

| `many_sorted` | `fuzzy` | Mode | Quantifiers | Constants | Connectives |
|---|---|---|---|---|---|
| `False` | `False` | **FOL** | unsorted `∀x` | unsorted | classical ∧ ∨ ⊕ ¬ → ↔ |
| `True` | `False` | **MSFOL** | sorted `∀x:Sort` | sorted `alice:Sort` | classical ∧ ∨ ¬ → ↔ |
| `True` | `True` | **MSFL** | sorted `∀x:Sort` | sorted `alice:Sort` | weak ∧ ∨, strong ⊗ ⊕, Łuk ¬ → ↔ |
| `False` | `True` | **FL** | unsorted `∀x` | unsorted | weak ∧ ∨, strong ⊗ ⊕, Łuk ¬ → ↔ |

The modal and second-order extension modes are classical unsorted FOL plus their own operators; the remaining three are standalone fragments with their own connective sets:

- **modal** (`modal=True`) — adds `□ ◇` (alethic), `K_a B_a Say_a Want_a` (epistemic/doxastic/assertive/bouletic), `Ⓖ Ⓕ Ⓝ Ⓤ ⒣ ⒫ ⒴ ⒮` (temporal, future and past), `Ⓞ Ⓟ` (deontic), nominals and `@i` (hybrid), the counterfactuals `□→ ◇→`, and the public announcements `[φ!]ψ / ⟨φ!⟩ψ`. The agent of `K_a`/`B_a` is a first-class term, so a bound `K_x` quantifies over agents.
- **second-order** (`second_order=True`) — adds `∀P / ∃P` over predicate variables (arity inferred from use).
- **dependence** (`dependence=True`) — the team-semantic fragment `¬ ∧ ∨ ∀ ∃` with dependence atoms `=(x, y)` and slashed existentials `∃x/{y}`.
- **linear** (`linear=True`) — intuitionistic linear logic `⊗ ⊸ & ⊕ !` with the units `𝟙 ⊤ 𝟘`.
- **lambek** (`lambek=True`) — the Lambek calculus `• \ /` over atomic categories.

The constructor rejects an unsupported combination with a clear `ValueError`. The extension modes cannot be combined with each other or with the sorted/fuzzy flags:

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

Formulas are written with natural symbols — `∀ ∃ ∧ ∨ ¬ → ↔ ⊕ ⊗ = ≠ ≤ ≥` — with no ASCII fallbacks required. An identifier's own first character decides whether it is predicate-valued or term-valued: an uppercase-initial identifier is a predicate, applied with parentheses; anything else is term-valued, and the term-level identifier rules below decide whether a bare token is a variable or a constant.

```python
parser = MSFLParser()
parser.parse("∀x (Human(x) → Mortal(x))")
# → Quantifier(type='∀', variable=Variable(name='x'),
#              formula=Implies(left=Atom(predicate='Human', args=(Variable(name='x'),)),
#                              right=Atom(predicate='Mortal', args=(Variable(name='x'),))))
```

### The three term-valued identifier classes

A bare term-valued token resolves to one of three terminal classes — and therefore one of three node types — purely by its spelling:

- **`VARIABLE`** — a single term-valued letter, optionally followed by digits (`x`, `y`, `x2`). It becomes a `Variable`.
- **`NAME`** — a multi-character term-valued identifier with a non-leading letter (`alice`, `socrates`). It becomes a `Constant` (and, when applied with parentheses, the head of a `Function`).
- **`CONSTANT`** — the explicit `c_`-prefix form (`c_7`, `c_alice`). It becomes a `Constant` too, and is the way to force a single-symbol name to be a constant.

```python
parser = MSFLParser()

parser.parse("P(x)")          # → Atom(predicate='P', args=(Variable(name='x'),))
parser.parse("P(x2)")         # → Atom(predicate='P', args=(Variable(name='x2'),))
parser.parse("P(alice)")      # → Atom(predicate='P', args=(Constant(name='alice'),))
parser.parse("P(c_7)")        # → Atom(predicate='P', args=(Constant(name='c_7'),))
parser.parse("P(c_alice)")    # → Atom(predicate='P', args=(Constant(name='c_alice'),))
```

Because a single term-valued letter is always a *variable*, a function symbol must be a multi-character `NAME`; `f(x)` is a parse error (`f` is a variable, which cannot be applied), whereas `father(x)` is a `Function`:

```python
parser = MSFLParser()
parser.parse("father(x) = bob")
# → Atom(predicate='=',
#        args=(Function(name='father', args=(Variable(name='x'),)),
#              Constant(name='bob')))
```

### Non-ASCII letters, underscores, and digit-leading names

`PREDICATE`/`CONSTANT`/`NAME`/`VARIABLE` are not ASCII-only: any Unicode
letter is accepted (Greek is the one exception — see below), a `NAME` may
contain underscores anywhere past its first character, and a `NAME` may
also start with one or more digits, as long as a letter follows. Which
class a token belongs to is still decided the same way as the plain-ASCII
case above — by its first character, never by a special case for "this is
non-ASCII" — so the rule to keep in mind is just: **`str.isupper()` on the
first character means predicate, anything else means term-valued.**

```python
parser = MSFLParser()

parser.parse("LostTo(x, świątek)")
# → Atom(predicate='LostTo', args=(Variable(name='x'), Constant(name='świątek')))
parser.parse("Sibling(dani_Shapiro, family_History)")
# → Atom(predicate='Sibling', args=(Constant(name='dani_Shapiro'), Constant(name='family_History')))
parser.parse("Hosted(beijing, 2008SummerOlympics)")
# → Atom(predicate='Hosted', args=(Constant(name='beijing'), Constant(name='2008SummerOlympics')))
```

A script with no upper/lower distinction — Chinese, Arabic, Hebrew,
Devanagari, and most others — never satisfies `str.isupper()`, so a bare
identifier from such a script is always term-valued and can never head an
atom by itself:

```python
parser.parse("P(中文)")   # → Atom(predicate='P', args=(Constant(name='中文'),))
parser.parse("中文(x)")   # → ParsingError — 中文(x) parses as a term (a Function), and a
                          #   bare term is not a complete formula; a caseless-script
                          #   identifier can never head an atom on its own
```

A digit-leading identifier (`2008SummerOlympics`) is a `NAME`, never a
number and never a predicate: `NUMBER` itself is unchanged (`2008` and
`2.5` still lex as plain numbers), and nothing lets an atom's head start
with a digit. Underscore is a continuation character only — never legal as
the first character of any identifier (`_foo` is a `NamingError`) — and it
widens `NAME`/`CONSTANT`/`VARIABLE` but deliberately **not** `PREDICATE`:
`Family_History(x)` is still rejected, exactly as `Foo_bar(x)` always was.

Greek letters are excluded from every one of these widened classes,
because they are already spoken for: `λ` opens a lambda term (see "Lambda
syntax" below), `μ` opens a measure term (see "Measure term
`μ(entity, dimension)`" below), and the plain lowercase Greek run
(`αβγδεζηθικνξοπρστυφχψω`) is `CONSTANT`'s other alternative alongside
`c_...` — widening the letter classes without this exclusion would have
turned those operators into ordinary identifier characters instead.

```python
parser.parse("λx. P(x)")   # → still a Lambda, not P applied to a NAME "λx"
parser.parse("P(α)")       # → Atom(predicate='P', args=(Constant(name='α'),)) — via the Greek CONSTANT form
```

This widening is purely additive: every formula this kit's grammar
accepted before still parses to the structurally identical AST (see
`CHANGELOG.md`'s entry for the change, and
`tests/test_identifier_widening.py`).

The two shapes only this widening lets through — a non-ASCII predicate or
function name, and a digit-leading term — are not automatically legal
wherever a parsed formula is *exported* to next: TPTP, Prover9, SMT-LIB2,
THF, Isabelle, and MiniZinc are each ASCII-only formats with their own
legality rules that a raw `świątek` or `2008SummerOlympics` can violate.
Every one of those export routes now sanitises for its own target format
before rendering — an injective, whole-problem-consistent ASCII rewrite,
with the original names translated back into anything a prover's answer
echoes — see {doc}`transforms` for the mechanism and examples, and
`CHANGELOG.md`'s entry for the full account. This is a *different*
mechanism from `fol.sanitize`: that module rewrites a name to a token
THIS parser's own grammar can re-parse (the case an import from outside
the kit runs into — an IRI-derived TPTP predicate name, say — not a name
this parser already accepts), and stays untouched by the export-format
fix.

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

## Source spans: pointing a node back at its own text

`parse()` builds an AST but keeps no record of where in the input each node
came from. `parse_with_spans()` does: it parses exactly like `parse()`, then
also returns a `SpanMap` — each node of the returned formula maps back to
the exact character range(s) of `text` it was parsed from.

```python
parser = MSFLParser()

spanned = parser.parse_with_spans("∀x (Human(x) → Mortal(x))")
spanned.formula == parser.parse("∀x (Human(x) → Mortal(x))")   # → True — same AST parse() builds

human = spanned.formula.formula.left        # the Human(x) atom
spanned.spans.for_node(human)
# → NodeSpans(extent=Span(start=4, end=12, ..., text='Human(x)'),
#              head=Span(start=4, end=9, ..., text='Human'))
```

A span never has to be re-derived: `Span.text` is already the slice, and
`start`/`end` index straight into the original `text` passed to
`parse_with_spans`. Every node gets TWO spans, bundled as `NodeSpans`:
`extent` is the minimal text the whole node covers (redundant outer
parentheses excluded), `head` is just its own head token — a connective's
occurrence, an atom's predicate name, a quantifier's symbol together with
its bound variable (`"∀x"`, whitespace included). A leaf term
(`Variable`/`Constant`/`Number`) has `head == extent`: it IS its one token.

The spans are returned as a table alongside the AST, keyed by PATH — a tuple
of child indices from the root — not as a field on each node, and not by the
node object's own identity or value. Every node class is a frozen dataclass
with structural equality (`P(x) == P(x)` even from two different formulas,
or two occurrences in the SAME formula, as in `P(x) ∧ P(x)`), which a
per-node span field — or a table keyed by the node's value — would break:
two textually-distinct occurrences of the same subformula would collapse
onto one span. `spans.get(path)` is the primary lookup; `spans.for_node(node)`
above is the convenience form for when you already have a node object in
hand (resolved by identity against whichever tree the map is currently bound
to — `parse_with_spans`'s own result is already bound to `spanned.formula`).
Walk every `(path, node)` pair with `unicode_fol_kit.traverse(spanned.formula)`.

Either half of a `NodeSpans` may independently report `UNKNOWN` — a sentinel
distinct from every real `Span`, and falsy, so `if span:` and `if span is
UNKNOWN:` both work. This happens in narrow, specific situations, never as a
silent guess: an operator outside the classical FOL fragment this feature
targets (`∀ ∃ ¬ ∧ ∨ → ↔ ⊕`, predicates over constants/variables/function
terms — those get BOTH spans exactly, always), a higher-order application of
a lambda-bound predicate (rewritten during scope resolution into nodes the
original parse never produced), and an agent variable sliced out of a
combined `K_a`-style token in modal mode — the enclosing `Knows`/`Believes`/…
node itself still has an exact EXTENT, only its bare agent sub-node does not:

```python
modal = MSFLParser(modal=True)
ms = modal.parse_with_spans("K_alice P(alice)")

ms.spans.get(()).extent                  # the whole Knows node — known
# → Span(start=0, end=16, line=1, column=1, end_line=1, end_column=17, text='K_alice P(alice)')
ms.spans.get((0,)).extent is UNKNOWN     # → True — the agent, sliced out of one combined token
```

`unicode_fol_kit.replace_at(root, path, new_node)` is the matching
path-addressed edit: it rebuilds only the spine from `root` down to `path`,
so every node reachable via a path that does not run through the edit is the
exact same object in the result — including under a span table built before
the edit, which stays valid for every path outside it.
