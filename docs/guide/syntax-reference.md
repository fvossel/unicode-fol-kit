# Syntax reference

The full surface syntax accepted by `MSFLParser`, the AST node catalogue, and the parser's error / mixing-hint behaviour. Because all modes share the same term and atom layer, most of the syntax is identical across modes; differences are called out explicitly.

## Tokens

The lexer distinguishes the following token kinds. Because the patterns are mutually exclusive, a given identifier is unambiguously a variable, a constant, a function/predicate name, a number, or a sort annotation.

| Token | Pattern | Examples | Meaning |
|---|---|---|---|
| Variable | one term-valued letter, optional trailing digits | `x`, `y`, `x1`, `z42`, `ś`, `ś1` | a (possibly bound) logical variable |
| Name | term-valued, at least two letters (or one-or-more digits then a letter), may also contain digits, underscores, and uppercase letters after the first character | `socrates`, `distance`, `centerOf`, `foo1`, `dani_Shapiro`, `2008SummerOlympics`, `świątek` | a bare constant or a function symbol |
| Constant (`c_`) | `c_` followed by letters/digits (any script) | `c_a`, `c_zero`, `c_42`, `c_świątek` | an explicitly marked constant |
| Constant (Greek) | a run of Greek letters, **excluding** `λ` and `μ` | `θ`, `α`, `π` | a constant, e.g. a threshold `θ` in `μ(x, dim) > θ` |
| Predicate | one uppercase-signalling letter, then letters/digits/underscores | `P`, `Human`, `OnSurfaceOf`, `Has_bond`, `Ś` | a predicate symbol |
| Number | digits, optional decimal part | `0`, `42`, `3.14` | a numeric literal |
| Sort annotation | `:` followed by an uppercase-signalling letter and letters/digits/underscores | `:Human`, `:Sort1` | a sort tag *(MSFOL and MSFL modes only)* |

"Term-valued letter" and "uppercase-signalling letter" are not ASCII-only: any Unicode letter qualifies, decided by the SAME rule Python's `str.isupper()` uses on that letter — true means uppercase-signalling (Predicate/Sort), anything else (including every letter of a script with no case distinction at all, such as Chinese, Arabic, Hebrew, or Devanagari) means term-valued (Variable/Name/Constant). A caseless-script identifier is therefore always term-valued and can never head an atom by itself. Underscore is a continuation character only — never legal as a token's first character (`_foo` and `_Family(x)` are rejected) — and it may follow the first character of a Name, a Predicate or a Sort, so `Foo_bar(x)` is an atom; a Variable and the tail of a `c_` constant take none. A Name may also start with one or more ASCII digits followed by a letter (`2008SummerOlympics`); `Number` itself is unaffected, so a bare digit run with no trailing letter (`2008`, `3.14`) still lexes as a number, never a Name. Greek letters are excluded from every one of these classes (not just carved out of Name/Predicate specifically) because `λ`/`μ`/the Greek Constant run already use them; see below.

The `c_` form exists so that **single-letter constants** can be written without colliding with variables. A bare `a` is always a variable; if you need the constant *a*, write `c_a`.

Greek letters (except the reserved operators `λ` Lambda and `μ` Measure) name constants directly — handy for symbolic thresholds and parameters, e.g. `μ(x, volume) > θ` (“too much”). This is **constants only**: predicates, function names, and variables never draw from this Greek-letter Constant form, though they do accept non-Greek Unicode letters as described above. The Kripke evaluator and Z3 carry the raw unicode name; `Constant.to_prover9`/`to_tptp` transliterate a constant's own name deterministically and reversibly (`θ` → `theta`, other non-ASCII → a `uXXXX` codepoint escape) on their own, node by node. A non-ASCII predicate or function name, and any digit-leading term, need a wider fix a single node cannot do by itself — an injective rewrite across a whole problem, with the original names translated back out of a prover's answer — which every ASCII-only export route (TPTP, Prover9, SMT-LIB2, THF, Isabelle, MiniZinc) now applies before rendering; see {doc}`transforms` for how. `unicode_logic_kit.fol.sanitize` is a different mechanism for a different problem: it rewrites a name to a token THIS PARSER's own grammar can re-parse (an import from outside the kit, not a name this parser already accepts), and is unrelated to what any export format accepts.

A function or predicate is recognised by being immediately followed by a parenthesised argument list, e.g. `distance(x, y)` or `Human(socrates)`. The same token class (Name) serves both as a bare constant and, when applied, as a function symbol. **A single term-valued letter is the one exception to "Variable, always"**: standing alone it is a variable (`f` in `∀f P(f)`), but immediately followed by `(` it is read as a one-letter function symbol instead — `f(x)` is `Function("f", [x])`, not a variable applied to something:

```python
from unicode_logic_kit import MSFLParser

p = MSFLParser()
p.parse("P(x)")        # → Atom(predicate='P', args=(Variable(name='x'),))   bare x: a variable
p.parse("P(f(x))")     # → Atom(predicate='P', args=(Function(name='f', args=(Variable(name='x'),)),))   f(...): a function
```

The sort annotation token always begins with `:`, which makes it lexically disjoint from all other tokens. **Whitespace before the colon is optional**: `∀x:Human P(x)` and `∀x :Human P(x)` are both valid and produce identical parse trees.

## Terms

A term is one of:

- a variable (`x`, `x1`)
- a constant (`socrates`, `c_a`) or number (`42`, `3.14`)
- in MSFOL / MSFL modes: a **sort-annotated constant** (`alice:Human`, `c_a:Sort1`)
- a function application (`f(t1, …, tn)`, e.g. `centerOf(x)`)
- an arithmetic combination of terms using `+`, `-`, `*`, `/`
- a parenthesised term (`(t)`)

Arithmetic follows the usual precedence: `*` and `/` bind tighter than `+` and `-`, and both groups are left-associative. For example `x + y * z` parses as `x + (y * z)`.

**Sort rules in MSFOL / MSFL modes:** variables are sorted implicitly by the quantifier that binds them; ground constants must carry an explicit sort annotation. An unsorted constant (e.g. bare `alice`) is a syntax error in sorted modes.

## Atomic formulas

An atomic formula is one of:

- a predicate applied to terms: `P`, `Human(socrates)`, `OnSurfaceOf(y, x)` (a predicate may be nullary, i.e. used without arguments)
- an infix comparison between two terms: `=`, `≠`, `<`, `>`, `≤`, `≥`, e.g. `x1 + 1 = y1` or `distance(y, c) > distance(z, c)`
- a truth constant, `⊤` or `⊥`: the nullary atoms `$true` and `$false`

Every unicode mode except `linear` and `lambek` reads `⊤` and `⊥` as these two atoms, as does LaTeX `\top` / `\bot`, and they print back as `⊤` / `⊥`. In `linear=True` mode `⊤` is instead the additive truth `Top` and there is no `⊥` (the units are `𝟙 ⊤ 𝟘`); in `lambek=True` mode there are no truth constants.

```python
from unicode_logic_kit import api

p.parse("⊤")                    # → Atom(predicate='$true', args=())
p.parse("P → ⊥")                # → Implies(left=Atom(predicate='P', args=()), right=Atom(predicate='$false', args=()))
api.parse_any("⊥").formula      # → Atom(predicate='$false', args=())
p.parse("P → ⊥").to_unicode_str()               # → 'P → ⊥'
MSFLParser(linear=True).parse("⊤")              # → Top()
```

## Compound formulas

Atomic formulas are combined with connectives and quantifiers. The available connectives and their interpretations depend on the mode.

### FOL mode

| Syntax | Operator | Interpretation |
|---|---|---|
| `¬φ` | negation | classical |
| `φ ∧ ψ` | conjunction | classical |
| `φ ∨ ψ` | disjunction | classical |
| `φ ⊕ ψ` | exclusive or | classical |
| `φ → ψ` | implication | classical |
| `φ ↔ ψ` | biconditional | classical |
| `φ Ⓒ ψ` | concessive (Contrast) | *whereas* / *although* — truth-functionally `∧` |
| `∀x φ` | universal | unsorted |
| `∃x φ` | existential | unsorted |
| `∃≥n x φ` / `∃≤n x φ` / `∃=n x φ` | counting quantifier (Count) | at least / at most / exactly `n` distinct `x` |

FOL mode additionally accepts two term forms for natural-language translation: the
degree term `μ(entity, dimension)` (Measure) and the set-cardinality term `|{v : φ}|`
(Cardinality), compared with `<` / `>`. See {doc}`natural-language` for all five
NL-front-end constructs (these four plus the modal `Say_a` / `Want_a`).

### MSFOL mode

Same connectives as FOL, `⊕` (exclusive or) included. Quantifiers require a sort annotation:

| Syntax | Operator |
|---|---|
| `¬φ`, `φ ∧ ψ`, `φ ∨ ψ`, `φ ⊕ ψ`, `φ → ψ`, `φ ↔ ψ` | classical (as FOL) |
| `∀x:Sort φ`, `∃x:Sort φ` | sorted quantifiers |

### MSFL mode

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

### FL mode

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

## Operator precedence

The precedence levels are the same across all four core modes (MSFL/FL use the same syntactic structure with Łukasiewicz semantics):

| Precedence | Operators | Associativity |
|---|---|---|
| 1 (highest) | `¬`, quantifiers `∀` / `∃` | prefix |
| 2 | `∧` `∨` `⊕` (FOL / MSFOL) / `∧` `∨` `⊗` `⊕` (MSFL / FL) | left |
| 3 | `→` | right |
| 4 (lowest) | `↔` | right |

Worked examples (parenthesised to show how the parser groups them):

- `¬P(x) ∧ Q(x)` → `(¬P(x)) ∧ Q(x)` — negation binds tighter than conjunction
- `P(x) ∧ Q(x) → R(x)` → `(P(x) ∧ Q(x)) → R(x)` — conjunction binds tighter than implication
- `P(x) → Q(x) ↔ R(x)` → `(P(x) → Q(x)) ↔ R(x)` — implication binds tighter than biconditional
- `P(x) → Q(x) → R(x)` → `P(x) → (Q(x) → R(x))` — implication is right-associative
- `P(x) ∧ Q(x) ∧ R(x)` → `(P(x) ∧ Q(x)) ∧ R(x)` — conjunction is left-associative

These verdicts are exactly what the parser produces, e.g.:

```python
from unicode_logic_kit import MSFLParser

p = MSFLParser()
p.parse("¬P(x) ∧ Q(x)")
# → And(Not(P(x)), Q(x))            negation binds tighter than ∧
p.parse("P(x) → Q(x) ↔ R(x)")
# → Iff(Implies(P(x), Q(x)), R(x))  → binds tighter than ↔
```

## Mixing same-level operators

The same-level connectives (level 2 above) **cannot be mixed without explicit parentheses**. This is deliberate: it avoids the silent, easy-to-misread grouping that a default precedence would impose.

- **FOL mode** — `∧`, `∨`, `⊕` cannot be mixed.
- **MSFOL mode** — `∧`, `∨`, `⊕` cannot be mixed.
- **MSFL / FL mode** — `∧`, `∨`, `⊗`, `⊕` cannot be mixed.
- **Modal and second-order modes** — same as FOL (`∧`, `∨`, `⊕`), since the modal/temporal and second-order operators bind tighter, like `¬`.

```text
P(x) ∧ Q(x) ∨ R(x)      # rejected
(P(x) ∧ Q(x)) ∨ R(x)    # accepted
```

A chain of the *same* operator is always fine: `P ∧ Q ∧ R`, `P ⊗ Q ⊗ R`, etc.

## Quantifier scope

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

## Supported symbols

| Category | FOL | MSFOL | MSFL | FL |
|---|---|---|---|---|
| Quantifiers | `∀` `∃` (unsorted) | `∀` `∃` (sorted `:Sort`) | `∀` `∃` (sorted `:Sort`) | `∀` `∃` (unsorted) |
| Connectives | `∧` `∨` `⊕` `¬` `→` `↔` | `∧` `∨` `⊕` `¬` `→` `↔` | `∧` `∨` `⊗` `⊕` `¬` `→` `↔` | `∧` `∨` `⊗` `⊕` `¬` `→` `↔` |
| Lambda | `λ` | `λ` | `λ` | `λ` |
| Sort annotations | — | `:Sort` | `:Sort` | — |
| Equality / comparison | `=` `≠` `<` `>` `≤` `≥` | same | same | same |
| Arithmetic | `+` `-` `*` `/` | same | same | same |
| Grouping | `(` `)` `[` `]` | same | same | same |
| Argument separator | `,` | same | same | same |

Whitespace is insignificant and may be used freely between tokens — including before sort annotation colons.

The **modal mode** (`MSFLParser(modal=True)`) adds `□` `◇` (alethic), `K_a` `B_a` (epistemic/doxastic), `Say_a` `Want_a` (assertive/bouletic — see {doc}`natural-language`), `Ⓞ` `Ⓟ` (deontic), and the temporal operators below; the **second-order mode** (`MSFLParser(second_order=True)`) adds `∀P` / `∃P` over predicate variables.

### Temporal operators (modal mode)

| Glyph | Operator | Surface syntax | Meaning |
|---|---|---|---|
| `Ⓖ` | `Always` | `Ⓖφ` | henceforth (now and at every future point) |
| `Ⓕ` | `Eventually` | `Ⓕφ` | eventually (now or at some future point) |
| `Ⓝ` | `Next` | `Ⓝφ` | at the immediately following point |
| `Ⓤ` | `Until` | `φ Ⓤ ψ` | φ holds until ψ does (binary) |
| `⒣` | `Historically` | `⒣φ` | has always been (now and at every **past** point) |
| `⒫` | `Once` | `⒫φ` | was once the case (now or at some **past** point) |
| `⒴` | `Previous` | `⒴φ` | at every immediate **past** point (yesterday) |
| `⒮` | `Since` | `φ ⒮ ψ` | φ has held since ψ was last true (binary) |
| `□→` | `Would` | `φ □→ ψ` | counterfactual: if φ *were* so, ψ *would* be (binary) |
| `◇→` | `Might` | `φ ◇→ ψ` | counterfactual: if φ were so, ψ *might* be (binary) |

The four past-tense duals `⒣` / `⒫` / `⒴` / `⒮` (Prior tense logic) run over the **converse** of the one-step `"temporal"` relation: `⒣`/`⒫`/`⒴` are the backward mirrors of `Ⓖ`/`Ⓕ`/`Ⓝ`, and `⒮` is the backward mirror of `Ⓤ`. They are recognised throughout the toolkit — parser, `satisfies_modal`, `standard_translation`, and the QML embedding. The prefix temporal operators (`Ⓖ Ⓕ Ⓝ ⒣ ⒫ ⒴`) bind as tightly as `¬`; the binary `Ⓤ` and `⒮` bind looser than `∧`/`∨` but tighter than `→`, right-associative.

```python
from unicode_logic_kit import MSFLParser

p = MSFLParser(modal=True)
p.parse("⒣P").to_unicode_str()              # → '⒣P'         (Historically)
p.parse("P ⒮ Q").to_unicode_str()           # → 'P ⒮ Q'       (Since, binary)
p.parse("⒣(Rain → ⒫ Sun)").to_unicode_str() # → '⒣(Rain → ⒫Sun)'
p.parse("⒣P ∧ Q").to_unicode_str()          # → '⒣P ∧ Q'   (⒣ binds like ¬)
```

### Public announcement operators (modal mode)

| Glyph | Operator | Surface syntax | Meaning |
|---|---|---|---|
| `[…!]` | `Announce` | `[φ!]ψ` | after truthfully announcing φ, ψ holds (box) |
| `⟨…!⟩` | `AnnounceDiamond` | `⟨φ!⟩ψ` | φ is truthful, and after announcing it ψ holds (diamond) |

The announcement itself is bracketed, so it needs no separate precedence rule — `[φ!]` reads as one prefix unit, exactly like `□` or `K_a`, and binds its formula the same tight way:

```python
p.parse("[P!]Q ∧ R").to_unicode_str()    # → '[P!]Q ∧ R'   ([P!] binds tighter than ∧)
p.parse("[P → Q!]R").to_unicode_str()    # → '[P → Q!]R'   (the announcement can be any formula)
```

See {doc}`nonclassical` for `reduce_announcements` and how the modal tableau decides PAL through it.

### Group-epistemic operators (modal mode)

| Glyph | Operator | Surface syntax | Meaning |
|---|---|---|---|
| `E_{…}` | `EverybodyKnows` | `E_{a,b,…}φ` | every agent in the group knows φ (one-step, ⋀K_a φ) |
| `D_{…}` | `DistributedKnowledge` | `D_{a,b,…}φ` | φ is distributed knowledge in the group (one-step, pooled) |
| `C_{…}` | `CommonKnowledge` | `C_{a,b,…}φ` | φ is common knowledge in the group (reflexive-transitive closure) |

Each opening glyph is followed by a brace-delimited, comma-separated agent list — `a`/`b` (single-letter, like a quantified variable) or `alice`/`bob` (multi-letter, like `K_alice`'s own agent) — closed by `}`, then the formula at the same tight, prefix-level precedence every other operator in this family uses:

```python
p.parse("D_{a,b} P").to_unicode_str()          # → 'D_{a,b} P'
p.parse("E_{alice,bob} P").to_unicode_str()     # → 'E_{alice,bob} P'
p.parse("C_{a,b,c} (P ∧ Q)").to_unicode_str()   # → 'C_{a,b,c} (P ∧ Q)'
```

The brace list needs **at least one** agent (`C_{}` is not valid syntax), and it cannot collide with the pre-existing `{…}` uses elsewhere in the grammar — Cardinality's `|{v : φ}|`, or a plain predicate whose name happens to start `C_`/`D_`/`E_` (e.g. `C_alpha(x)`, unaffected, since the group terminals fuse the letter, the underscore AND the opening brace into one token). See {doc}`modal` for the semantics (union / intersection / closure) and the FHMV strength ordering `C_G φ → E_G φ → K_a φ → D_G φ`.

## Lambda abstraction and application (all modes)

A lambda abstraction is written `λ` followed by a parameter name, a literal `.`, and a body formula. Every parser mode supports identical lambda surface notation.

### Parameter types

| Parameter form | Example | Typical use |
|---|---|---|
| Single term-valued letter | `λx. P(x)` | value variable |
| Multi-letter term-valued name | `λfoo. P(foo(x))` | named-constant parameter |
| Uppercase predicate symbol | `λP. P(x)` | predicate / higher-order parameter |

All three token classes become a `LambdaVar` in the AST. Scope resolution (applied automatically by `parse()`) then rewrites body occurrences of the lambda-bound name:

- **Variable occurrence** — `λx. P(x)`: the `x` in `P(x)` becomes `LambdaVar("x")`.
- **Predicate-application occurrence** — `λP. P(x)`: the `P(x)` in the body becomes `Application(LambdaVar("P"), Variable("x"))`. Multi-argument atoms curry left: `P(x, y)` → `Application(Application(LambdaVar("P"), x), y)`.
- **Named-function occurrence** — `λfoo. P(foo(x))`: the `foo(x)` in `P`'s argument list (a term-level function call) becomes `Application(LambdaVar("foo"), Variable("x"))`.

The scope obeys the **innermost-binder rule**: a quantifier removes the quantified name from the lambda-bound set. Inside `λx. ∀x P(x)`, the `x` in `P(x)` is logical (stays `Variable`).

### Body scope

The body extends rightward through all connectives — lambda has lower precedence than every binary operator:

```text
λx. P(x) ∧ Q(x)      # body is the And node P(x) ∧ Q(x)
λx. P(x) → Q(x)      # body is the Implies node P(x) → Q(x)
```

Multi-parameter lambdas are written by nesting: `λP. λx. P(x)`.

### Application syntax

A lambda application requires both sides to be parenthesised: `(func)(arg)`.

```text
(λx. P(x))(a)         # arg is variable a
(λx. P(x))(alice)     # arg is constant alice
(λP. P(x))(Q)         # arg is the zero-arity atom Q
(λP. P(x))(Q(y))      # arg is the atom Q(y)
```

Higher-order application inside the body — a predicate parameter applied to arguments — is written in the natural `P(x)` notation, not as `(P)(x)`. Scope resolution handles the rewrite automatically.

### Parse examples

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

## A complete example per mode

```text
# FOL
∀x ((Object(x) ∧ HasThreeDimensionalShape(x) ∧
     ∀y ∀z ((Point(y) ∧ OnSurfaceOf(y, x) ∧ Point(z) ∧ OnSurfaceOf(z, x))
            → distance(y, centerOf(x)) = distance(z, centerOf(x))))
    → Sphere(x))

# MSFOL
∀x:Person ∀y:Person (Knows(x, y) ∧ Trusted(y)) → Shares(x, y)

# MSFL
∀x:Patient ∀y:Treatment (Effective(y) ⊗ Tolerable(x, y)) → Recommended(x, y)

# FL
∀x ∀y (Effective(y) ⊗ Tolerable(x, y)) → Recommended(x, y)
```

## AST nodes

All nodes are **frozen** Python dataclasses and can be imported from `unicode_logic_kit`. Being frozen, every node is immutable and **hashable**, so nodes can be put in sets, used as dict keys, and deduplicated. `Function` and `Atom` store their `args` as a `tuple` (a list passed to the constructor is accepted and coerced), which is what makes them hashable.

### Shared term and atom nodes (all modes)

| Class | Fields | Notes |
|---|---|---|
| `Variable` | `name: str` | bound or free variable |
| `Constant` | `name: str` | bare constant or `c_`-prefixed |
| `Number` | `value: int \| float` | numeric literal; a whole value is stored as the `int` it equals (`1`, `1.0` and `01` are all `Number(value=1)`) |
| `Function` | `name: str`, `args: tuple` | function application and arithmetic ops |
| `Atom` | `predicate: str`, `args: tuple` | predicate or infix comparison |

### Classical formula nodes (FOL / MSFOL)

| Class | Fields |
|---|---|
| `Not` | `formula` |
| `And` | `left`, `right` |
| `Or` | `left`, `right` |
| `Xor` | `left`, `right` *(the classical modes; `⊕` is `StrongDisjunction` in MSFL / FL)* |
| `Implies` | `left`, `right` |
| `Iff` | `left`, `right` |
| `Contrast` | `left`, `right` *(FOL — concessive `Ⓒ`; truth-functionally `∧`)* |
| `Quantifier` | `type: str`, `variable`, `formula` *(FOL / FL — the unsorted modes)* |

### Natural-language extension nodes (FOL mode)

| Class | Fields | Notes |
|---|---|---|
| `Count` | `op: str` (`"ge"` / `"le"` / `"eq"`), `n: Number`, `variable`, `formula` | counting quantifier `∃≥n` / `∃≤n` / `∃=n`; `n` is symbolic; FO-expandable on export |
| `Measure` | `entity`, `dimension` | degree term `μ(e, d)`; exports as the function `measure(e, d)` |
| `Cardinality` | `variable`, `formula` | set-cardinality term `|{v : φ}|`; binds `v`; no first-order export |

See {doc}`natural-language` for the semantics and worked examples.

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

### Modal / temporal nodes (modal mode)

The prefix temporal duals are the past-tense mirrors of the forward operators.

| Class | Fields | Glyph | Notes |
|---|---|---|---|
| `Always` | `formula` | `Ⓖ` | henceforth (future) |
| `Eventually` | `formula` | `Ⓕ` | eventually (future) |
| `Next` | `formula` | `Ⓝ` | next point |
| `Until` | `left`, `right` | `Ⓤ` | strong until (binary) |
| `Historically` | `formula` | `⒣` | past dual of `Always` |
| `Once` | `formula` | `⒫` | past dual of `Eventually` |
| `Previous` | `formula` | `⒴` | past dual of `Next` |
| `Since` | `left`, `right` | `⒮` | past dual of `Until` (binary) |
| `Would` | `left`, `right` | `□→` | Lewis counterfactual; no first-order export |
| `Might` | `left`, `right` | `◇→` | dual `¬(A □→ ¬B)`; no first-order export |
| `Announce` | `announcement`, `formula` | `[…!]` | PAL box: after truthfully announcing `announcement`, `formula` holds |
| `AnnounceDiamond` | `announcement`, `formula` | `⟨…!⟩` | PAL diamond: `announcement` is truthful and `formula` then holds |
| `EverybodyKnows` | `group: Tuple[Node, ...]`, `formula` | `E_{…}` | E_G: everyone in `group` knows `formula` (one-step, union) |
| `DistributedKnowledge` | `group: Tuple[Node, ...]`, `formula` | `D_{…}` | D_G: distributed knowledge in `group` (one-step, intersection; refuses an empty `group`) |
| `CommonKnowledge` | `group: Tuple[Node, ...]`, `formula` | `C_{…}` | C_G: common knowledge in `group` (reflexive-transitive closure) |

The alethic (`Box`, `Diamond`), epistemic/doxastic (`Knows`, `Believes`), assertive/bouletic (`Says`, `Wants` — agent-prefix attitude operators `Say_a` / `Want_a`; see {doc}`natural-language`), and deontic (`Obligatory`, `Permitted`) nodes round out the modal family; see the modal-logic page. All modal nodes reject `to_z3` / `to_prover9` / `to_tptp` directly — translate first with `standard_translation()` (or, for `Announce`/`AnnounceDiamond`, reduce first with `reduce_announcements` — see {doc}`nonclassical`). `standard_translation()` itself further refuses `CommonKnowledge` (not first-order definable, like `Until`); `EverybodyKnows`/`DistributedKnowledge`, like `Knows`, translate to ordinary FOL. `EverybodyKnows`'s `group` field is each member's own agent **term** (`Variable`/`Constant`, exactly like `Knows`'s `agent` field), a structural child reached by `free_variables`/substitution/`map_children` like any other — not a special binder.

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

Parse errors are reported with human-readable messages rather than raw parser internals. Lexer-level problems (an invalid character, a malformed name or number, or an attempt to mix same-level connectives without parentheses) raise `NamingError`; structural problems (an incomplete formula or a misplaced operator) raise `ParsingError`. Both report the offending position and, where useful, a hint. The hint text is **mode-aware**:

```python
from unicode_logic_kit import MSFLParser  # these snippets intentionally raise

# FOL mode — hint names ∧, ∨, and ⊕
MSFLParser().parse("P(x) ∧ Q(x) ∨ R(x)")    # raises NamingError
# SYNTAX_ERROR: Unexpected character '∨' at position 13 after closing parenthesis ')'.
#   Hint: Cannot mix conjunction (∧), disjunction (∨), and exclusive or (⊕) without parentheses

# MSFOL mode — classical same-level group, hint names ∧, ∨, and ⊕
MSFLParser(many_sorted=True).parse("P(x) ∧ Q(x) ∨ R(x)")
#   Hint: Cannot mix conjunction (∧), disjunction (∨), and exclusive or (⊕) without parentheses

# MSFL / FL mode — hint names all four Łukasiewicz connectives
MSFLParser(many_sorted=True, fuzzy=True).parse("P(x) ∧ Q(x) ⊗ R(x)")
#   Hint: Cannot mix weak conjunction (∧), weak disjunction (∨),
#         strong conjunction (⊗), and strong disjunction (⊕) without parentheses

# Modal mode — classical same-level group, hint names ∧, ∨, and ⊕
MSFLParser(modal=True).parse("P(x) ∧ Q(x) ∨ R(x)")
#   Hint: Cannot mix conjunction (∧), disjunction (∨), and exclusive or (⊕) without parentheses

# Second-order mode — same classical hint as FOL
MSFLParser(second_order=True).parse("P(x) ∧ Q(x) ∨ R(x)")
#   Hint: Cannot mix conjunction (∧), disjunction (∨), and exclusive or (⊕) without parentheses
```

The modal and second-order modes share FOL's same-level group because their extra operators (modal/temporal prefixes, `∀P` / `∃P`) bind tighter, at the `¬` level, and so never participate in same-level mixing.
