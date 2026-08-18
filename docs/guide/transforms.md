# Transforming & exporting formulas

Every AST node carries a uniform set of transformations: normal forms and Horn checks for classical FOL, lambda-calculus reduction, sort relativisation, a small traversal API, and round-tripping exporters/importers for LaTeX, TPTP, Prover9, SMT-LIB, and Graphviz. Most operations are methods on the node; the rest are free functions importable from `unicode_fol_kit`.

## Normal forms

`to_nnf()`, `to_pnf()`, `to_cnf()`, and `skolemize()` operate on classical FOL. They accept FOL and MSFOL directly — sorts are reduced via `to_fol()` internally. **Łukasiewicz (MSFL/FL) input is refused**, not silently classicalised: a Łukasiewicz connective is not classical, and treating `P ∨ ¬P` as excluded middle would decide the wrong logic (weak disjunction has no excluded middle). Evaluate fuzzy input with `semantics.fuzzy.evaluate` / `fuzzy_is_valid`, or collapse it explicitly first with `to_fol(node)` if the classical skeleton is really what you want. (Lambda terms must be beta-reduced and lambda-eliminated beforehand; see below.)

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

### NNF: every connective is eliminated

`to_nnf` rewrites `→`, `↔`, and `⊕` away, collapses double negations, and pushes `¬` down to the atoms (De Morgan over `∧`/`∨` and over the quantifiers).

```python
to_nnf(p.parse("¬¬P")).to_unicode_str()
# → 'P'                          (double negation removed)

to_nnf(p.parse("¬(P ∧ Q)")).to_unicode_str()
# → '¬P ∨ ¬Q'

to_nnf(p.parse("¬(∀x P(x) → ∃y Q(y))")).to_unicode_str()
# → '∀x P(x) ∧ ∀y ¬Q(y)'

to_nnf(p.parse("∀x (P(x) ↔ Q(x))")).to_unicode_str()
# → '∀x ((¬P(x) ∨ Q(x)) ∧ (¬Q(x) ∨ P(x)))'

to_nnf(p.parse("P ∧ Q → R ∨ S")).to_unicode_str()
# → '¬P ∨ ¬Q ∨ (R ∨ S)'                    (De Morgan)

to_nnf(p.parse("¬∀x P(x)")).to_unicode_str()
# → '∃x ¬P(x)'                   (¬∀ ≡ ∃¬)

to_nnf(p.parse("P ↔ Q")).to_unicode_str()
# → '(¬P ∨ Q) ∧ (¬Q ∨ P)'        (biconditional as two implications)

to_nnf(p.parse("P ⊕ Q")).to_unicode_str()
# → '(P ∧ ¬Q) ∨ (¬P ∧ Q)'        (exclusive-or expanded)
```

### PNF: quantifiers hoisted, variables standardised apart

`to_pnf` returns a quantifier prefix over a quantifier-free NNF matrix. Bound variables are renamed to fresh `v0, v1, …` first, so quantifiers can hoist freely even when the source reuses a name across scopes.

```python
to_pnf(p.parse("∀x P(x) → ∃x Q(x)")).to_unicode_str()
# → '∃v0 ∃v1 (¬P(v0) ∨ Q(v1))'

to_pnf(p.parse("∀x P(x) ∨ ∃x Q(x)")).to_unicode_str()
# → '∀v0 ∃v1 (P(v0) ∨ Q(v1))'

to_pnf(p.parse("∃x P(x) → ∀y Q(y)")).to_unicode_str()
# → '∀v0 ∀v1 (¬P(v0) ∨ Q(v1))'

to_pnf(p.parse("∀x ∃y ∀z R(x, y, z) → ∃w S(w)")).to_unicode_str()
# → '∃v0 ∀v1 ∃v2 ∃v3 (¬R(v0, v1, v2) ∨ S(v3))'   (note: ∀ flips to ∃ under the → ¬, names made distinct)
```

### CNF / DNF are idempotent

Re-running the pass on its own output is a no-op (the result is already in the target shape).

```python
cnf = to_cnf(p.parse("P ∨ (Q ∧ R)"))
to_cnf(cnf).to_unicode_str() == cnf.to_unicode_str()    # → True
```

### Skolemization: constants vs. functions

An existential with no universal in scope becomes a Skolem **constant**; one under universals becomes a Skolem **function** of exactly those universals.

```python
skolemize(p.parse("∃y P(y)")).to_unicode_str()
# → 'P(sk0)'                              (no universals → Skolem constant)

skolemize(p.parse("∀x ∀y ∃z R(x, y, z)")).to_unicode_str()
# → '∀v0 ∀v1 R(v0, v1, sk0(v0, v1))'

skolemize(p.parse("∃x P(x) ∧ ∃y Q(y)")).to_unicode_str()
# → 'P(sk0) ∧ Q(sk1)'

skolemize(p.parse("∃x (∀y P(x, y) ∧ ∃z Q(x, z))")).to_unicode_str()
# → '∀v1 (P(sk0, v1) ∧ Q(sk0, sk1(v1)))'      (z depends on both universals)
```

### Tseitin CNF (equisatisfiable)

`to_tseitin_cnf()` produces an **equisatisfiable** CNF using the Tseitin/definitional encoding: it introduces fresh auxiliary atoms (`ts0, ts1, …`) for compound subformulas, so the result grows linearly instead of risking the exponential blow-up of the distributive `to_cnf`. It is **not** logically equivalent to the input (the auxiliaries are existentially fresh), but the input is satisfiable iff its Tseitin CNF is. It operates on quantifier-free (propositional / ground) formulas and raises `ValueError` on quantified input.

```python
from unicode_fol_kit import MSFLParser, to_tseitin_cnf, is_satisfiable

p = MSFLParser()
phi = p.parse("(P ∨ Q) ∧ (¬P ∨ R)")

is_satisfiable(phi) == is_satisfiable(to_tseitin_cnf(phi))
# → True   (equisatisfiable; the Tseitin form adds atoms ts0, ts1, ts2)

# The fresh auxiliaries appear alongside the originals:
sorted({a.predicate for a in to_tseitin_cnf(phi).atoms()})
# → ['P', 'Q', 'R', 'ts0', 'ts1', 'ts2']

# Equisatisfiability is preserved on an UNSAT input too:
is_satisfiable(p.parse("P ∧ ¬P")) == is_satisfiable(to_tseitin_cnf(p.parse("P ∧ ¬P")))
# → True   (both sides False)
```

Quantified input is rejected — a single 0-ary auxiliary cannot track a subformula whose truth value varies over the domain:

```python
to_tseitin_cnf(p.parse("∀x P(x)"))    # raises ValueError: only quantifier-free input
```

### Horn check

`is_horn()` reports whether a formula's clausal form consists of Horn clauses — each clause has at most one positive literal. The formula is skolemised, its universal prefix dropped, and the matrix put into CNF before the clauses are checked.

```python
from unicode_fol_kit import MSFLParser, is_horn

p = MSFLParser()
is_horn(p.parse("∀x (Body(x) → Head(x))"))   # → True   (definite clause)
is_horn(p.parse("P → (Q ∧ R)"))              # → True   (splits into two Horn clauses)
is_horn(p.parse("P → (Q ∨ R)"))              # → False  (clause has two positive literals)
is_horn(p.parse("P(a)"))                     # → True   (a unit fact is a Horn clause)
is_horn(p.parse("¬P ∨ ¬Q"))                  # → True   (a goal clause: zero positive literals)

is_horn(p.parse("(P → Q) ∧ (Q → R)"))           # → True
is_horn(p.parse("¬Bird(x) ∨ Flies(x)"))        # → True
is_horn(p.parse("P ∨ Q"))                       # → False
is_horn(p.parse("(P → Q) ∧ (R ∨ S)"))          # → False
```

## Sort relativisation: `to_fol()`

`to_fol()` performs a two-phase reduction: it first lowers Łukasiewicz operators to classical ones (`to_msfol()`), then eliminates sort annotations via relativisation — a sorted `∀x:S φ` becomes `∀x (S(x) → φ)`.

```python
from unicode_fol_kit import MSFLParser, to_fol

p = MSFLParser(many_sorted=True, fuzzy=True)
formula = p.parse("∀x:Human (P(x) ∧ ¬Q(x))")

to_fol(formula).to_unicode_str()
# → '∀x (Human(x) → P(x) ∧ ¬Q(x))'
```

An **existential** sort relativises with a conjunction, not an implication — `∃x:S φ` becomes `∃x (S(x) ∧ φ)`:

```python
to_fol(p.parse("∃x:Human P(x)")).to_unicode_str()
# → '∃x (Human(x) ∧ P(x))'

to_fol(p.parse("∀x:Human ∃y:Animal Likes(x, y)")).to_unicode_str()
# → '∀x (Human(x) → ∃y (Animal(y) ∧ Likes(x, y)))'

to_fol(p.parse("∀x:Agent (∃y:Agent Knows(x, y) ∨ Alone(x))")).to_unicode_str()
# → '∀x (Agent(x) → (∃y (Agent(y) ∧ Knows(x, y)) ∨ Alone(x)))'
```

A **sorted constant** is written `alice:Human` (the constant name needs at least two letters, otherwise it lexes as a variable). `to_fol` drops the annotation to a plain constant; pass `include_sort_facts=True` to conjoin the membership atoms it implies at the top level:

```python
from unicode_fol_kit import Atom, SortedConstant

knows = Atom("Knows", [SortedConstant("alice", "Human"),
                       SortedConstant("bob", "Human")])
knows.to_unicode_str()
# → 'Knows(alice:Human, bob:Human)'

to_fol(knows).to_unicode_str()
# → 'Knows(alice, bob)'                       (annotation stripped)

to_fol(knows, include_sort_facts=True).to_unicode_str()
# → 'Human(alice) ∧ Human(bob) ∧ Knows(alice, bob)'   (membership facts conjoined)
```

```{note}
This is a classical (Boolean) projection, not a fuzzy-preserving translation. `to_msfol()` maps *both* the strong (`⊗`/`⊕`) and the weak (`∧`/`∨`) Łukasiewicz connectives to the same classical `And`/`Or`. On crisp truth values {0, 1} the operators coincide, so the reduction is sound as the two-valued projection — but the genuinely many-valued content is discarded. To compute the real-valued Łukasiewicz degree, use `fuzzy_evaluate()` or the fuzzy Z3 solver instead.
```

The normal-form functions above call `to_fol()` internally for **sorts**, so they accept sorted input directly — e.g. you can `skolemize` a sorted formula. Fuzzy input still needs the explicit `to_fol()` call first (see above); passing it straight to `skolemize`/`to_nnf`/etc. raises:

```python
from unicode_fol_kit import skolemize

skolemize(p.parse("∀x:Human ∃y:Human Loves(x, y)")).to_unicode_str()
# → '∀v0 (Human(v0) → Human(sk0(v0)) ∧ Loves(v0, sk0(v0)))'

fuzzy = MSFLParser(fuzzy=True).parse("P ⊗ Q")
skolemize(fuzzy)
# raises NotImplementedError: StrongConjunction is a Łukasiewicz connective — classical
# normal forms (and the resolution prover on top of them) would silently decide the
# WRONG logic. Evaluate with semantics.fuzzy.evaluate or decide with
# atp.z3_fuzzy.fuzzy_is_valid; collapse explicitly with to_fol(node) first if the
# classical skeleton is wanted.

skolemize(to_fol(fuzzy)).to_unicode_str()   # → 'P ∧ Q'   (the explicit, documented opt-in)
```

## Lambda-calculus operations

Every parser mode supports lambda abstraction and application, and `parse()` applies scope resolution automatically. The reduction functions are free functions on the AST.

### Free variables and substitution

`free_variables(term)` returns the set of variables free in a term; the result is a mixed set that may contain both `Variable` (logical) and `LambdaVar` (lambda-bound) objects. `substitute(term, var, replacement)` performs a capture-avoiding substitution.

```python
from unicode_fol_kit import MSFLParser, free_variables, substitute, Variable, Constant

p = MSFLParser()

free_variables(p.parse("λP. P(x)"))
# → {Variable(name='x')}   (x is free; P is lambda-bound and does not appear)

free_variables(p.parse("R(x, y) ∧ ∃y Q(y)"))
# → {Variable(name='x'), Variable(name='y')}   (the leftmost y is free; the ∃-bound y is not)

substitute(p.parse("P(x)"), Variable("x"), Constant("a")).to_unicode_str()
# → 'P(a)'
```

Substitution is **capture-avoiding**: replacing into a formula whose binder would capture the incoming variable renames the binder first.

```python
substitute(p.parse("∀x R(x, y)"), Variable("y"), Variable("x")).to_unicode_str()
# → '∀x_0 R(x_0, x)'   (the bound x is renamed so the substituted x stays free)
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

```python
beta_reduce(p.parse("(λx. (λy. P(x, y))(a))(b)")).to_unicode_str()
# → 'P(b, a)'

# Higher-order: a predicate parameter F is applied to an argument in the body.
beta_reduce(p.parse("(λF. F(x))(λy. Q(y))")).to_unicode_str()
# → 'Q(x)'

# Partial application: applying only the first of two parameters.
partially = beta_reduce(p.parse("(λx. λy. R(x, y))(a)"))
partially.to_unicode_str()
# → 'λy. R(a, y)'
```

A **curried** application reduces one argument at a time; spell currying with nested parentheses, `((g)(c))(d)`:

```python
beta_reduce(p.parse("((λx. λy. R(x, y))(c))(d)")).to_unicode_str()
# → 'R(c, d)'

beta_reduce(p.parse("((λP. λQ. P ∧ Q)(A))(B)")).to_unicode_str()
# → 'A ∧ B'
```

A non-normalising term (e.g. the classic Ω = `(λx. x x)(λx. x x)`, built directly since the parser rejects self-application) raises `ReductionLimitError` rather than looping forever:

```python
from unicode_fol_kit import ReductionLimitError

omega_half = Lambda(LambdaVar("x"), Application(LambdaVar("x"), LambdaVar("x")))
omega = Application(omega_half, omega_half)
beta_reduce(omega)    # raises ReductionLimitError after the step limit
```

### Single-step reduction

`beta_reduce_step(node)` contracts exactly **one** leftmost-outermost redex and returns `(new_node, reduced)`; `reduced` is `False` (and the node is returned unchanged) once it is in beta-normal form.

```python
from unicode_fol_kit import beta_reduce_step

term = p.parse("(λP. λx. P(x))(Q)")
step1, did = beta_reduce_step(term)
did                              # → True
step1.to_unicode_str()          # → 'λx. (Q)(x)'   (one outer redex contracted)

step2, did2 = beta_reduce_step(step1)
did2                             # → False   (already in beta-normal form)
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
[s.to_unicode_str() for s in steps]
# → ['(λP. λx. (P)(x))(Q)', 'λx. (Q)(x)']
```

A term with a free higher-order variable applied to arguments is **stuck** — no redex remains, yet a lambda construct survives — so `eliminate_lambdas` raises `ValueError`:

```python
from unicode_fol_kit import Application, LambdaVar, Variable

eliminate_lambdas(Application(LambdaVar("g"), Variable("x")))   # raises ValueError: not lambda-free
```

`reduce_trace` honours a `limit` and raises `ReductionLimitError` for a non-normalising term (the Ω from above):

```python
omega_half = Lambda(LambdaVar("x"), Application(LambdaVar("x"), LambdaVar("x")))
omega = Application(omega_half, omega_half)
reduce_trace(omega, limit=5)            # raises ReductionLimitError: exceeded 5 steps
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

`subformulas()` excludes atomic terms (`Variable`, `Constant`, `Number`, `Function`, …) — only the formula-valued nodes are returned, in pre-order:

```python
[s.to_unicode_str() for s in f.subformulas()]
# → ['∀x (Human(x) → Mortal(x))', 'Human(x) → Mortal(x)', 'Human(x)', 'Mortal(x)']

[a.to_unicode_str() for a in f.atoms()]
# → ['Human(x)', 'Mortal(x)']
```

`map_children(fn)` is the single point of structural recursion: it rebuilds a node, applying `fn` to each immediate child. The identity rebuild is a deep copy; substituting a child is how the reduction passes are built.


```python
# More traversal examples
f_complex = p.parse("∀x ((P(x) ∧ Q(x)) ∨ (R(x) → S(x)))")
from unicode_fol_kit import And, Or, Implies
f_complex.count()           # → 11
f_complex.count(Atom)       # → 4
f_complex.count(And)        # → 1
f_complex.count(Or)         # → 1
f_complex.count(Implies)    # → 1

# Listing all atoms with their arguments
f_relational = p.parse("∀x ∀y (Knows(x, y) ∧ ¬Likes(y, x))")
atoms_by_arity = {}
for atom in f_relational.atoms():
    arity = len(atom.args)
    if arity not in atoms_by_arity:
        atoms_by_arity[arity] = []
    atoms_by_arity[arity].append(atom.predicate)
# → {2: ['Knows', 'Likes']}
```

from unicode_fol_kit import Not

g = MSFLParser().parse("¬(P ∧ Q)")
g.map_children(lambda c: c).to_unicode_str()    # → '¬(P ∧ Q)'   (structural copy)
```

## Export

The `to_*` exporters are methods on every node and use the same precedence-aware parenthesisation as `to_unicode_str()`.

```python
f = MSFLParser().parse("∀x (Human(x) → Mortal(x))")

f.to_prover9()   # → '(all x (Human(x) -> Mortal(x)))'
f.to_tptp()      # → '(![X]: (human(X) => mortal(X)))'
f.to_latex()     # → '\\forall x\\, (Human(x) \\rightarrow Mortal(x))'
f.to_dict()      # JSON-serialisable dict

# Export with comparisons
comp_formula = p.parse("x < 5 ∧ y ≥ 0")
comp_formula.to_unicode_str()
# → 'x < 5 ∧ y ≥ 0'

comp_formula.to_tptp()
# → '($less(X,5) & $greatereq(Y,0))'

comp_formula.to_prover9()
# → '((X < 5) & (Y >= 0))'

```

`to_latex()` renders sorts as `\forall x{:}\mathrm{Human}\,` and the strong Łukasiewicz operators as `\otimes` / `\oplus`; symbol and predicate names are emitted verbatim. TPTP lowercases predicates and uppercases variables per its convention. Second-order formulas reject `to_z3` / `to_prover9` / `to_tptp` — round-trip those (and modal / fuzzy) through LaTeX or JSON instead.

```python
# Sorts, modal operators, and strong Łukasiewicz connectives in LaTeX:
MSFLParser(many_sorted=True).parse("∀x:Human P(x)").to_latex()
# → '\\forall x{:}\\mathrm{Human}\\, P(x)'

MSFLParser(modal=True).parse("□P → ◇Q").to_latex()
# → '\\Box P \\rightarrow \\Diamond Q'

MSFLParser(fuzzy=True).parse("P ⊗ Q").to_latex()
# → 'P \\otimes Q'
```

A second-order formula has no TPTP/Prover9/Z3 image and raises `NotImplementedError` (use LaTeX or JSON for it):

```python
so = MSFLParser(second_order=True).parse("∀P P(x)")
so.to_tptp()       # raises NotImplementedError (no first-order image)
```

### ASCII-legal names in export, for a whole problem

`to_tptp()` / `to_prover9()` render a predicate/function/constant name close to verbatim: TPTP folds only the exported name's first character to lower-case, Prover9 folds nothing at all, and neither transliterates a non-ASCII predicate or function name (only `Constant.to_tptp`/`to_prover9` transliterate, via `constant_name_to_ascii`). {doc}`parsing`'s identifier widening lets a predicate/function name carry a non-ASCII letter and a term start with a digit, so calling these two methods directly on such a formula can produce text that is not legal TPTP/Prover9 in the first place:

```python
f = MSFLParser().parse("Świątek(x)")
f.to_tptp()      # → 'świątek(X)'    — the raw non-ASCII letter, only the case folded
f.to_prover9()   # → 'Świątek(X)'    — completely untouched

g = MSFLParser().parse("P(2008SummerOlympics)")
g.to_tptp()      # → 'p(2008SummerOlympics)'   — leading digit intact, illegal TPTP lower_word
```

That is deliberate at the node level, not an oversight: a single node has no view of the rest of the problem it belongs to, so it cannot keep two distinct names from colliding once "fixed", and a per-node fix could never reach a caller that later needs to read a prover's own answer back. The fix instead runs once, over a WHOLE set of premises and a conclusion together — inside every one of the kit's own external-prover entry points: `check_logical_entailment_vampire` / `atp.vampire_entailment.check_entailment_vampire_detailed`, `atp.eprover_backend.check_entailment_eprover_detailed` (E and Zipperposition), `atp.twee_entailment.check_entailment_twee_detailed`, `check_logical_entailment` (Prover9), and `Cvc5Backend.decide` (SMT-LIB2, narrower — only a digit-leading name needs fixing there, since Z3's own SMT-LIB2 serialiser already quotes a non-ASCII name correctly on its own). Call any of these — see {doc}`classical-reasoning`'s "External provers" section for the Prover9/Vampire pair — on the same two formulas above, and the external tool sees a legal, ASCII, non-digit-leading problem instead; an already-legal name passes through completely untouched, so nothing changes for a formula these entry points already handled correctly. Wherever the tool's own answer can carry a symbol name back (a TSTP proof step, a countermodel), that answer is translated back to the ORIGINAL kit-level names before it reaches the caller — a real `Świątek`/`2008SummerOlympics`, never the synthesised token the external tool actually saw. See `CHANGELOG.md`'s `fol.grammars` / `fol._identifiers` entry for the full mechanism (the injective, whole-problem-consistent rewrite; the reverse mapping; what was checked against a real E, Vampire, Twee, and cvc5).

`hol.classical.to_thf_fol` / `to_isabelle_fol` (and their MSFOL/modal counterparts in `fol.qml` / `hol.isabelle_modal`, see {doc}`higher-order`) and `atp.minizinc_backend.to_minizinc` (see {doc}`finite-domain`) sanitise the same way on every call, with no separate step to remember: their own name resolvers already transliterate and de-collide every predicate, function, constant, and (for the modal exporters) bound variable name before any THF/Isabelle/MiniZinc text is emitted.

### JSON round-trip

`to_dict()` produces a JSON-serialisable dict tagged with `_type`; the static `Node.from_dict()` reconstructs the AST. This preserves **every** node family (modal, second-order, fuzzy, lambda), so it is the portable serialisation of choice.

```python
import json
from unicode_fol_kit import Node

f = MSFLParser().parse("∀x (Human(x) → Mortal(x))")
blob = json.dumps(f.to_dict())          # store / send the string
Node.from_dict(json.loads(blob)) == f   # → True   (exact AST recovered)
```

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

The full output for the formula above (every node and edge, terms included) is:

```python
print(f.to_dot())
# digraph AST {
#   node [shape=box];
#   n0 [label="∀ x"];
#   n1 [label="→"];
#   n2 [label="Atom: Human"];
#   n3 [label="Variable: x"];
#   n2 -> n3;
#   n1 -> n2;
#   n4 [label="Atom: Mortal"];
#   n5 [label="Variable: x"];
#   n4 -> n5;
#   n1 -> n4;
#   n0 -> n1;
# }
```

## Import

The exporters have inverses, so formulas written for the standard tools can be read back into the AST. **The importers cover classical FOL** — the format the external tools speak. Modal, second-order, fuzzy, dependence, linear (ILL), and Lambek formulas round-trip instead through **LaTeX or JSON**, which preserve every node family.

### LaTeX

`parse_latex()` is the inverse of `to_latex()`: it translates LaTeX commands to the Unicode surface syntax (`latex_to_unicode()`), then parses. It accepts the exact output of `to_latex()` as well as common hand-written synonyms (`\neg`/`\lnot`, `\wedge`/`\land`, `\vee`/`\lor`, `\to`/`\rightarrow`, …). It takes the same mode flags as `MSFLParser`.

```python
from unicode_fol_kit import MSFLParser, parse_latex, latex_to_unicode

latex_to_unicode(r"\forall x (P(x) \to Q(x))")
# → '∀ x (P(x) → Q(x))'   (spacing preserved; the parser ignores it)

latex_to_unicode(r"P \lor \lnot Q")
# → 'P ∨ ¬ Q'             (hand-written \lor / \lnot synonyms accepted)

# Round-trip a sorted formula:
ast = MSFLParser(many_sorted=True).parse("∀x:Human P(x)")
parse_latex(ast.to_latex(), many_sorted=True) == ast        # → True

# Modal and second-order round-trip via LaTeX:
m = MSFLParser(modal=True).parse("□P → ◇Q")
parse_latex(m.to_latex(), modal=True) == m                  # → True

s = MSFLParser(second_order=True).parse("∀P P(x)")
parse_latex(s.to_latex(), second_order=True) == s           # → True

# Dependence, linear (ILL), and Lambek round-trip via LaTeX too:
d = MSFLParser(dependence=True).parse("∀x ∃y (=(y) ∧ Edge(x, y))")
parse_latex(d.to_latex(), dependence=True) == d              # → True

lin = MSFLParser(linear=True).parse("A ⊸ B")
parse_latex(lin.to_latex(), linear=True) == lin              # → True

lam = MSFLParser(lambek=True).parse("NP \\ S")
parse_latex(lam.to_latex(), lambek=True) == lam              # → True
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

# Prover9 / LADR — one formula, or a whole input file
parse_prover9("(all X (man(X) -> mortal(X)))").to_unicode_str()
# → '∀x (man(x) → mortal(x))'

from unicode_fol_kit import parse_prover9_problem
recs = parse_prover9_problem("""
formulas(assumptions).
  all X (man(X) -> mortal(X)).
  man(socrates).
end_of_list.
formulas(goals).
  mortal(socrates).
end_of_list.
""")
[(r.role, r.formula.to_unicode_str()) for r in recs]
# → [('assumptions', '∀x (man(x) → mortal(x))'),
#    ('assumptions', 'man(socrates)'),
#    ('goals', 'mortal(socrates)')]

# SMT-LIB2 text (parsed via Z3's own parser)
[a.to_unicode_str() for a in parse_smtlib("(declare-fun x () Int) (assert (< x (+ x 1)))")]
# → ['x < x + 1']
```

- **TPTP** — `parse_tptp_formula(s)` reads one FOF/CNF formula; `parse_tptp(text)` reads a whole problem into a list of `TptpFormula(name, role, formula)` records; `load_tptp(path)` reads a `.p`/`.tptp` file. `%` and `/* */` comments are ignored. TPTP lowercases predicates, so a predicate is capitalised on import (`man` → `Man`); **single-quoted atoms** (`'http___example_org_Thing'`, the form OWL→FOL dumps use for IRIs) are read with the quotes stripped and `\'` / `\\` unescaped; `$true`/`$false` import as opaque atoms; the typed `tff`/`thf` dialects and `include` directives are out of scope.
- **Prover9** — `parse_prover9(s)` reads a single Prover9/LADR formula (a trailing `.` is accepted); `parse_prover9_problem(text)` / `load_prover9(path)` read a whole input file — `set`/`clear`/`assign` directives (recognised and skipped), `formulas(LIST). … end_of_list.` blocks, and bare top-level formulas — into a list of `Prover9Formula(role, formula)` records (the list name is the role; `""` for a bare formula; `op(...)` declarations are out of scope). It follows `set(prolog_style_variables)` — uppercase/underscore-initial names are variables — matching `to_prover9()`'s output, and is case-preserving.
- **Z3 / SMT-LIB** — `from_z3(expr)` turns a `z3.ExprRef` back into the AST; `parse_smtlib(text)` / `load_smtlib(path)` parse SMT-LIB2 and convert every assertion. The conversion is **meaning-preserving, not structure-preserving**: Z3 maps variables/constants/numbers onto one uninterpreted sort, so a *free* variable comes back as a `Constant` (only bound variables survive as `Variable`); `A == B` reads as `Iff` on Booleans and `=` on individuals.

The TPTP and Prover9 readers map the comparison and arithmetic operators back to their glyph atoms/functions, and TPTP's `=` / `!=` / dollar-words too:

```python
parse_tptp_formula("X = Y").to_unicode_str()         # → 'x = y'
parse_tptp_formula("X != Y").to_unicode_str()        # → 'x ≠ y'
parse_tptp_formula("$less(x, y)").to_unicode_str()   # → 'x < y'
parse_tptp_formula("p($sum(x, y))").to_unicode_str() # → 'P(x + y)'

parse_prover9("all X (X >= 0 -> p(X)).").to_unicode_str()
# → '∀x (x ≥ 0 → p(x))'
```

A single-quoted TPTP atom (an IRI) imports with the quotes stripped; the resulting name is **not** a legal `MSFLParser` token, so sanitize it before re-parsing (see below):

```python
f = parse_tptp("fof(a, axiom, (![X]: ('http___ex_org_Thing'(X)))).")[0].formula
f.to_unicode_str()
# → '∀x Http___ex_org_Thing(x)'   (underscores: not re-parseable as-is)
```

On the SMT-LIB / Z3 side, `=` over Booleans reads as `Iff`, and a free Z3 symbol comes back as a `Constant`:

```python
[a.to_unicode_str() for a in
 parse_smtlib("(declare-const P Bool)(declare-const Q Bool)(assert (= P Q))")]
# → ['P ↔ Q']   (Boolean = is a biconditional)
```

```python
from unicode_fol_kit import MSFLParser, from_z3

g = MSFLParser().parse("P(x) ∧ Q(x)")
from_z3(g.to_z3()).to_unicode_str()
# → 'P(x) ∧ Q(x)'   (note: a free x round-trips through to_z3 as a Constant)
```

A classical formula survives a full **export → re-import** through TPTP unchanged (modulo the predicate-case convention):

```python
classical = MSFLParser().parse("∀x (Man(x) → Mortal(x))")
parse_tptp_formula(classical.to_tptp()).to_unicode_str()
# → '∀x (Man(x) → Mortal(x))'
```

### Round-trippable names for imported formulas

An external problem file can carry symbol names that the AST accepts but the
`MSFLParser` *lexer* does not — IRIs with underscores and mixed case (an OWL→FOL TPTP
dump renders `'http___example_org_Thing'` as the predicate `Http___example_org_Thing`),
single-letter or digit-bearing constants, and so on. Rendering such a node then yields a
string that does not re-parse. `sanitize_names(node)` (and `sanitize_all(nodes)` for a
whole problem) rewrites every symbol to a legal token so the render round-trips, leaving
already-legal names untouched and returning a `NameMapping` that recovers the originals:

```python
from unicode_fol_kit import MSFLParser, parse_tptp, sanitize_names

f = parse_tptp("fof(a, axiom, (![X]: ('http___ex_org_Thing'(X)))).")[0].formula
f.to_unicode_str()
# → '∀x Http___ex_org_Thing(x)'        (underscores: NOT a legal predicate token)

s, names = sanitize_names(f)
s.to_unicode_str()
# → '∀x HttpexorgThing(x)'              (a legal predicate token)
MSFLParser().parse(s.to_unicode_str()) == s    # → True  (now it round-trips)
names.reverse()[s.formula.predicate]           # → 'Http___ex_org_Thing'  (recover the IRI)
```

Pass the returned `NameMapping` back in (`sanitize_names(node, names)`) — or use
`sanitize_all` — to keep the same IRI mapped to the same token across every formula of a
problem. Predicates become `[A-Z]…`, functions multi-letter lowercase, constants keep a
legal bare name or take the `c_…` form, and variables keep `[a-z][0-9]*` or map to
`v0`/`v1`/….

Each symbol class is rewritten to its own legal shape. A single-letter constant takes the
explicit `c_…` form (so it does not collapse to a variable on re-parse), and a function
that is too short to be a `NAME` is padded:

```python
from unicode_fol_kit import Atom, Constant, Function, Variable

g = Atom("Likes", [Constant("a"), Function("f1", [Variable("x")])])
s, _ = sanitize_names(g)
s.to_unicode_str()
# → 'Likes(c_a, f1fn(x))'   (constant a → c_a; one-letter function f1 → f1fn)
MSFLParser().parse(s.to_unicode_str()) == s     # → True
```

A clean classical formula already uses legal tokens, so it passes through unchanged:

```python
clean = MSFLParser().parse("∀x (Human(x) → Mortal(x))")
sanitize_names(clean)[0] == clean               # → True   (nothing to rewrite)
```

### End-to-end: import → sanitize → render → re-parse

A complete pipeline for an OWL→FOL TPTP dump: read the problem, sanitize the whole batch
with one shared `NameMapping` (so each IRI maps to the same token everywhere), render to
Unicode, and re-parse — every formula round-trips, and the mapping recovers the IRIs.

```python
from unicode_fol_kit import MSFLParser, parse_tptp, sanitize_all

tptp_text = """
fof(sub,  axiom,      ![X]: ('ex_Cat'(X) => 'ex_Animal'(X))).
fof(fact, hypothesis, 'ex_Cat'(felix)).
fof(goal, conjecture, 'ex_Animal'(felix)).
"""

records = parse_tptp(tptp_text)                       # import
formulas = [r.formula for r in records]
sanitized, names = sanitize_all(formulas)             # one shared mapping

rendered = [s.to_unicode_str() for s in sanitized]    # render
rendered
# → ['∀x (ExCat(x) → ExAnimal(x))', 'ExCat(felix)', 'ExAnimal(felix)']

p = MSFLParser()
reparsed = [p.parse(r) for r in rendered]             # re-parse
all(rp == s for rp, s in zip(reparsed, sanitized))    # → True   (lossless round-trip)

names.reverse()
# → {'ExCat': 'Ex_Cat', 'ExAnimal': 'Ex_Animal', 'felix': 'felix', 'x': 'x'}
```
