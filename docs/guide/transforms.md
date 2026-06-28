# Transforming & exporting formulas

Every AST node carries a uniform set of transformations: normal forms and Horn checks for classical FOL, lambda-calculus reduction, sort relativisation, a small traversal API, and round-tripping exporters/importers for LaTeX, TPTP, Prover9, SMT-LIB, and Graphviz. Most operations are methods on the node; the rest are free functions importable from `unicode_fol_kit`.

## Normal forms

`to_nnf()`, `to_pnf()`, `to_cnf()`, and `skolemize()` operate on classical FOL. They accept FOL, MSFOL, MSFL, and FL inputs — sorts and Łukasiewicz operators are reduced via `to_fol()` first. (Lambda terms must be beta-reduced and lambda-eliminated beforehand; see below.)

```python
from unicode_fol_kit import MSFLParser, to_nnf, to_pnf, to_cnf, to_dnf, skolemize

p = MSFLParser()

to_nnf(p.parse("P → Q")).to_unicode_str()
# → '¬P ∨ Q'        (eliminates → ↔ ⊕, pushes ¬ down to atoms)

to_pnf(p.parse("∀x P(x) ∧ ∃y Q(y)")).to_unicode_str()
# → '∀v0 ∃v1 (P(v0) ∧ Q(v1))'   (quantifier prefix + quantifier-free matrix)

to_cnf(p.parse("P ∨ (Q ∧ R)")).to_unicode_str()
# → '(P ∨ Q) ∧ (P ∨ R)'   (conjunction of clauses)

to_dnf(p.parse("P ∧ (Q ∨ R)")).to_unicode_str()
# → '(P ∧ Q) ∨ (P ∧ R)'   (disjunction of conjunctive clauses)

skolemize(p.parse("∀x ∃y Loves(x, y)")).to_unicode_str()
# → '∀v0 Loves(v0, sk0(v0))'   (the existential becomes a Skolem function of x)
```

- `to_nnf` / `to_pnf` / `to_cnf` / `to_dnf` are **equivalence-preserving**: the result is logically equivalent to the (classical) input. `to_dnf` is the dual of `to_cnf` — a prenex form whose matrix is a disjunction of conjunctive clauses.
- `skolemize` is **satisfiability-preserving** (not equivalence-preserving): existentials are replaced by Skolem terms over the universals in scope, and the universal prefix is retained. Bound variables are standardised apart (renamed to fresh `v0, v1, …`); Skolem symbols are named `sk0, sk1, …`.

### Tseitin CNF (equisatisfiable)

`to_tseitin_cnf()` produces an **equisatisfiable** CNF using the Tseitin/definitional encoding: it introduces fresh auxiliary atoms (`ts0, ts1, …`) for compound subformulas, so the result grows linearly instead of risking the exponential blow-up of the distributive `to_cnf`. It is **not** logically equivalent to the input (the auxiliaries are existentially fresh), but the input is satisfiable iff its Tseitin CNF is. It operates on quantifier-free (propositional / ground) formulas and raises `ValueError` on quantified input.

```python
from unicode_fol_kit import MSFLParser, to_tseitin_cnf, is_satisfiable

p = MSFLParser()
phi = p.parse("(P ∨ Q) ∧ (¬P ∨ R)")

is_satisfiable(phi) == is_satisfiable(to_tseitin_cnf(phi))
# → True   (equisatisfiable; the Tseitin form adds atoms ts0, ts1, ts2)
```

### Horn check

`is_horn()` reports whether a formula's clausal form consists of Horn clauses — each clause has at most one positive literal. The formula is skolemised, its universal prefix dropped, and the matrix put into CNF before the clauses are checked.

```python
from unicode_fol_kit import MSFLParser, is_horn

p = MSFLParser()
is_horn(p.parse("∀x (Body(x) → Head(x))"))   # → True   (definite clause)
is_horn(p.parse("P → (Q ∧ R)"))              # → True   (splits into two Horn clauses)
is_horn(p.parse("P → (Q ∨ R)"))              # → False  (clause has two positive literals)
```

## Sort relativisation: `to_fol()`

`to_fol()` performs a two-phase reduction: it first lowers Łukasiewicz operators to classical ones (`to_msfol()`), then eliminates sort annotations via relativisation — a sorted `∀x:S φ` becomes `∀x (S(x) → φ)`.

```python
from unicode_fol_kit import MSFLParser, to_fol

p = MSFLParser(many_sorted=True, fuzzy=True)
formula = p.parse("∀x:Human (P(x) ∧ ¬Q(x))")

to_fol(formula).to_unicode_str()
# → '∀x (Human(x) → P(x) ∧ ¬Q(x))'

# Optionally conjoin sort-membership facts for constants at the top level:
to_fol(formula, include_sort_facts=True)
```

```{note}
This is a classical (Boolean) projection, not a fuzzy-preserving translation. `to_msfol()` maps *both* the strong (`⊗`/`⊕`) and the weak (`∧`/`∨`) Łukasiewicz connectives to the same classical `And`/`Or`. On crisp truth values {0, 1} the operators coincide, so the reduction is sound as the two-valued projection — but the genuinely many-valued content is discarded. To compute the real-valued Łukasiewicz degree, use `fuzzy_evaluate()` or the fuzzy Z3 solver instead.
```

The normal-form functions above call `to_fol()` internally, so they accept sorted and fuzzy input directly.

## Lambda-calculus operations

Every parser mode supports lambda abstraction and application, and `parse()` applies scope resolution automatically. The reduction functions are free functions on the AST.

### Free variables and substitution

`free_variables(term)` returns the set of variables free in a term; the result is a mixed set that may contain both `Variable` (logical) and `LambdaVar` (lambda-bound) objects. `substitute(term, var, replacement)` performs a capture-avoiding substitution.

```python
from unicode_fol_kit import MSFLParser, free_variables, substitute, Variable, Constant

p = MSFLParser()

free_variables(p.parse("λP. P(x)"))
# → {Variable(name='x')}   (x is free; P is lambda-bound and does not appear)

substitute(p.parse("P(x)"), Variable("x"), Constant("a")).to_unicode_str()
# → 'P(a)'
```

### Beta-, eta-, and beta-eta-reduction

`beta_reduce` reduces to beta-normal form using a normal-order (leftmost-outermost) strategy with full capture-avoiding substitution; it raises `ReductionLimitError` after 10 000 steps if the term does not normalise. `eta_reduce` does a single bottom-up pass contracting `λp. f(p) → f` when `p` is not free in `f`. `beta_eta_normalize` alternates the two to fixpoint (eta-reduction can expose fresh beta-redexes).

```python
from unicode_fol_kit import (
    MSFLParser, beta_reduce, eta_reduce, beta_eta_normalize,
    LambdaVar, Lambda, Application, Atom, Variable,
)

p = MSFLParser()

beta_reduce(p.parse("(λP. P(x))(λy. Q(y))")).to_unicode_str()
# → 'Q(x)'

# η:  λp. f(p) → f   (returns the inner Atom node, not the Lambda)
f = Atom("P", [Variable("x")])
eta_reduce(Lambda(LambdaVar("p"), Application(f, LambdaVar("p")))) == f
# → True
```

### Lambda elimination and reduction trace

`eliminate_lambdas()` beta-eta-normalises a term **and** verifies the result is lambda-free, so it can be fed to the exporters or the normal-form functions (which otherwise reject lambda nodes). A term that is stuck or only partially applied (no further redex but lambdas remain) raises `ValueError`. `reduce_trace()` returns the step-by-step reduction sequence, and `has_lambdas()` tests for residual lambda nodes.

```python
from unicode_fol_kit import MSFLParser, eliminate_lambdas, reduce_trace, has_lambdas

p = MSFLParser()
term = p.parse("(λP. P(x))(Q)")

has_lambdas(term)                       # → True
reduced = eliminate_lambdas(term)
reduced.to_unicode_str()                # → 'Q(x)'  (an Atom)
has_lambdas(reduced)                    # → False
reduced.to_tptp()                       # → 'q(X)'  (now exportable)

steps = reduce_trace(p.parse("(λP. λx. P(x))(Q)"))
len(steps)                              # → 2   (original, …, normal form)
```

```{note}
`eliminate_lambdas` fully resolves an `Application` of an atom to a term (yielding `Q(x)`); the raw `beta_eta_normalize` leaves it as an unresolved `Application` rendered `(Q)(x)`. Use `eliminate_lambdas` when you need a lambda-free AST ready for export or normal forms.
```

## Traversal and inspection

Every node exposes a small traversal API.

```python
from unicode_fol_kit import MSFLParser, Atom

f = MSFLParser().parse("∀x (Human(x) → Mortal(x))")

list(f.walk())        # pre-order: every node and descendant
f.subformulas()       # every sub-node that is a formula (terms excluded)
f.atoms()             # → [Atom("Human", …), Atom("Mortal", …)]
f.variables()         # → {Variable("x")}  (free + bound logical variables)
f.count()             # → 7   total node count
f.count(Atom)         # → 2   nodes of a given type
f.depth()             # → 4   tree height (a leaf has depth 1)
```

## Export

The `to_*` exporters are methods on every node and use the same precedence-aware parenthesisation as `to_unicode_str()`.

```python
f = MSFLParser().parse("∀x (Human(x) → Mortal(x))")

f.to_prover9()   # → '(all x (Human(x) -> Mortal(x)))'
f.to_tptp()      # → '(![X]: (human(X) => mortal(X)))'
f.to_latex()     # → '\\forall x\\, (Human(x) \\rightarrow Mortal(x))'
f.to_dict()      # JSON-serialisable dict
```

`to_latex()` renders sorts as `\forall x{:}\mathrm{Human}\,` and the strong Łukasiewicz operators as `\otimes` / `\oplus`; symbol and predicate names are emitted verbatim. TPTP lowercases predicates and uppercases variables per its convention. Second-order formulas reject `to_z3` / `to_prover9` / `to_tptp` — round-trip those (and modal / fuzzy) through LaTeX or JSON instead.

### Graphviz

`to_dot()` renders the AST as a Graphviz DOT digraph, mirroring the `tree_str()` view (the quantifier's bound variable is folded into its node label). Pipe the output to `dot -Tpng` to render an image.

```python
print(f.to_dot())
# digraph AST {
#   node [shape=box];
#   n0 [label="∀ x"];
#   n1 [label="→"];
#   ...
```

## Import

The exporters have inverses, so formulas written for the standard tools can be read back into the AST. **The importers cover classical FOL** — the format the external tools speak. Modal, second-order, and fuzzy formulas round-trip instead through **LaTeX or JSON**, which preserve every node family.

### LaTeX

`parse_latex()` is the inverse of `to_latex()`: it translates LaTeX commands to the Unicode surface syntax (`latex_to_unicode()`), then parses. It accepts the exact output of `to_latex()` as well as common hand-written synonyms (`\neg`/`\lnot`, `\wedge`/`\land`, `\vee`/`\lor`, `\to`/`\rightarrow`, …). It takes the same mode flags as `MSFLParser`.

```python
from unicode_fol_kit import MSFLParser, parse_latex, latex_to_unicode

latex_to_unicode(r"\forall x (P(x) \to Q(x))")
# → '∀ x (P(x) → Q(x))'   (spacing preserved; the parser ignores it)

# Round-trip a sorted formula:
ast = MSFLParser(many_sorted=True).parse("∀x:Human P(x)")
parse_latex(ast.to_latex(), many_sorted=True) == ast        # → True

# Modal and second-order round-trip via LaTeX:
m = MSFLParser(modal=True).parse("□P → ◇Q")
parse_latex(m.to_latex(), modal=True) == m                  # → True

s = MSFLParser(second_order=True).parse("∀P P(x)")
parse_latex(s.to_latex(), second_order=True) == s           # → True
```

Hand-written `c_`-constants need an escaped underscore (`c\_zero` or `c_{zero}`), since a bare `_` is LaTeX subscript.

### TPTP, Prover9, SMT-LIB

```python
from unicode_fol_kit import parse_tptp, parse_tptp_formula, parse_prover9, parse_smtlib

# TPTP: one bare FOF/CNF formula, or a whole problem file
parse_tptp_formula("![X]: (man(X) => mortal(X))").to_unicode_str()
# → '∀x (Man(x) → Mortal(x))'

problem = parse_tptp("""
fof(ax,  axiom,      ![X]: (man(X) => mortal(X))).
fof(hyp, hypothesis, man(socrates)).
fof(g,   conjecture, mortal(socrates)).
""")
[f.role for f in problem]
# → ['axiom', 'hypothesis', 'conjecture']

# Prover9 / LADR
parse_prover9("(all X (man(X) -> mortal(X)))").to_unicode_str()
# → '∀x (man(x) → mortal(x))'

# SMT-LIB2 text (parsed via Z3's own parser)
[a.to_unicode_str() for a in parse_smtlib("(declare-fun x () Int) (assert (< x (+ x 1)))")]
# → ['x < x + 1']
```

- **TPTP** — `parse_tptp_formula(s)` reads one FOF/CNF formula; `parse_tptp(text)` reads a whole problem into a list of `TptpFormula(name, role, formula)` records; `load_tptp(path)` reads a `.p`/`.tptp` file. `%` and `/* */` comments are ignored. TPTP lowercases predicates, so a predicate is capitalised on import (`man` → `Man`); `$true`/`$false` import as opaque atoms; the typed `tff`/`thf` dialects and `include` directives are out of scope.
- **Prover9** — `parse_prover9(s)` reads a Prover9/LADR formula (a trailing `.` is accepted). It follows `set(prolog_style_variables)` — uppercase/underscore-initial names are variables — matching `to_prover9()`'s output, and is case-preserving.
- **Z3 / SMT-LIB** — `from_z3(expr)` turns a `z3.ExprRef` back into the AST; `parse_smtlib(text)` / `load_smtlib(path)` parse SMT-LIB2 and convert every assertion. The conversion is **meaning-preserving, not structure-preserving**: Z3 maps variables/constants/numbers onto one uninterpreted sort, so a *free* variable comes back as a `Constant` (only bound variables survive as `Variable`); `A == B` reads as `Iff` on Booleans and `=` on individuals.

```python
from unicode_fol_kit import MSFLParser, from_z3

g = MSFLParser().parse("P(x) ∧ Q(x)")
from_z3(g.to_z3()).to_unicode_str()
# → 'P(x) ∧ Q(x)'   (note: a free x round-trips through to_z3 as a Constant)
```
