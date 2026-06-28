# Classical FOL / MSFOL reasoning

This page covers the reasoning layer for classical first-order logic and its many-sorted extension (MSFOL): four proof methods (resolution, Fitch natural deduction, the Gentzen sequent calculi LK/LJ, and analytic tableaux), SMT solving via Z3, external provers, equivalence checking, and a finite model finder. Every Python block below was executed against the package and its printed result is shown in a trailing `# →` comment.

## Built-in resolution prover

For entailment and validity **without** an external prover, the package ships a self-contained first-order **resolution** prover. It clausifies the input (skolemise → drop the ∀ prefix → CNF → clauses), then refutes `premises ∧ ¬conclusion` by binary resolution and factoring, deriving the empty clause iff the entailment holds.

```python
from unicode_fol_kit import MSFLParser, prove, is_valid_resolution

parser = MSFLParser()

premises = [parser.parse("∀x (Human(x) → Mortal(x))"), parser.parse("Human(socrates)")]
prove(premises, parser.parse("Mortal(socrates)"))                    # → True

prove([parser.parse("Human(socrates)")], parser.parse("Mortal(socrates)"))  # → False (no entailment)

is_valid_resolution(parser.parse("P ∨ ¬P"))                          # → True
is_valid_resolution(parser.parse("∃x ∀y L(x, y) → ∀y ∃x L(x, y)"))  # → True
```

- **Sound, deliberately incomplete.** First-order resolution is only semi-decidable, so `prove` / `is_valid_resolution` take a `max_steps` bound (default 10 000). They return `True` **only** when the empty clause is actually derived, and `False` both when the clause set saturates (genuinely no entailment) and when the bound is reached — they never report a non-theorem as proved.
- **Equality is uninterpreted.** `=` is treated as an ordinary predicate (no built-in reflexivity/congruence). Entailments that rely on the theory of equality (e.g. `a = b, P(a) ⊨ P(b)`) need those axioms as explicit premises, or use the Z3 backend instead.
- `to_clauses(formula)` exposes the clausal form, and `refute(clauses)` runs the saturation directly.

## Satisfiability, validity, and models (Z3)

`is_satisfiable` / `is_valid` / `get_model` decide a formula via the Z3 SMT solver and extract a counterexample.

```python
from unicode_fol_kit import MSFLParser, is_satisfiable, is_valid, get_model, Not

parser = MSFLParser()

is_satisfiable(parser.parse("P ∧ Q"))     # → True
is_satisfiable(parser.parse("P ∧ ¬P"))    # → False
is_valid(parser.parse("P ∨ ¬P"))          # → True

get_model(parser.parse("P ∧ Q"))          # → {'Q': 'True', 'P': 'True'}
get_model(parser.parse("P ∧ ¬P"))         # → None  (unsatisfiable)
```

`get_model` returns a dict mapping each Z3 declaration (constants, uninterpreted predicates/functions) to its interpretation, or `None` when the formula is unsatisfiable or Z3 returns `unknown` within the timeout. The key ordering is not guaranteed.

### Arithmetic-aware solving

The default `is_satisfiable` / `to_z3` treat everything as one uninterpreted sort, so arithmetic terms are opaque. The `*_arith` variants instead interpret `+ - * /` and the comparisons over a numeric sort (`"real"` by default, or `"int"`), so the solver can actually reason about numbers.

```python
from unicode_fol_kit import MSFLParser, is_satisfiable_arith, is_valid_arith, get_model_arith

parser = MSFLParser()

is_satisfiable_arith(parser.parse("x + 1 = 2 ∧ x > 0"))      # → True   (x = 1)
is_satisfiable_arith(parser.parse("x > 0 ∧ x < 0"))          # → False
is_valid_arith(parser.parse("∀x (x * 2 = x + x)"))           # → True
get_model_arith(parser.parse("x + 1 = 2 ∧ x > 0"))           # → {'x': '1'}
is_satisfiable_arith(parser.parse("x + x = 1"), sort="int")  # → False (no integer solution)
```

## Equivalence checking (Z3)

`formulas_are_equivalent` checks whether two formulas are logically equivalent (via Z3).

```python
from unicode_fol_kit import MSFLParser, formulas_are_equivalent

parser = MSFLParser()
f1 = parser.parse("¬(P(x) ∧ Q(x))")
f2 = parser.parse("¬P(x) ∨ ¬Q(x)")

formulas_are_equivalent(f1, f2)   # → True
```

## External provers (Prover9 / Vampire)

`check_logical_entailment` (Prover9) and `check_logical_entailment_vampire` (Vampire) decide whether a conclusion follows from a list of premises, each taking the prover's executable path as an argument. **These require the external binary to be installed; the examples below were not executed here.**

```python
from unicode_fol_kit import MSFLParser, check_logical_entailment  # needs an installed Prover9

parser = MSFLParser()
premises = [
    parser.parse("∀x (Human(x) → Mortal(x))"),
    parser.parse("Human(socrates)"),
]
conclusion = parser.parse("Mortal(socrates)")

check_logical_entailment(premises, conclusion, prover9_path="/usr/bin/prover9")  # True
```

The Vampire variant emits the premises as TPTP `axiom`s and the conclusion as a `conjecture` (Vampire reports `SZS status Theorem` when the entailment holds):

```python
from unicode_fol_kit import MSFLParser, check_logical_entailment_vampire  # needs an installed Vampire

# … same premises / conclusion …
check_logical_entailment_vampire(premises, conclusion, vampire_path="/usr/bin/vampire")  # True
```

On Windows a Linux Vampire installed in WSL can be driven with `use_wsl=True` (the temp problem file's path is translated to its `/mnt/...` form automatically). Every premise and the conclusion must be a closed sentence — Vampire rejects free variables, and recall that a single lowercase letter like `x` is a *variable*, so a constant individual needs a multi-character name (`socrates`) or the `c_`-prefix.

## Natural deduction (Fitch proofs)

The provers above decide *whether* an entailment holds; `check_proof` instead **checks a Fitch-style natural-deduction proof** — a derivation with nested subproofs (hypothetical reasoning), per-line justifications, and discharge rules. It is *sound*: it returns `True` only when every line genuinely follows by the cited rule and the proof's premises really do entail its conclusion. `verify_proof` additionally returns a `ProofResult` (fields `ok`, `conclusion`, `premises`, `logic`, `error`, `error_line`).

```python
from unicode_fol_kit import (
    MSFLParser, Proof, Subproof, premise, assume, line,
    check_proof, render_fitch,
)

parse = MSFLParser().parse

# Hypothetical syllogism:  P→Q, Q→R  ⊢  P→R
proof = Proof(
    premises=[premise(1, parse("P → Q")), premise(2, parse("Q → R"))],
    steps=[
        Subproof(
            assumption=assume(3, parse("P")),
            body=[line(4, parse("Q"), "→E", 1, 3),
                  line(5, parse("R"), "→E", 2, 4)],
        ),
        line(6, parse("P → R"), "→I", (3, 5)),
    ],
)

check_proof(proof)   # → True
```

`render_fitch(proof)` lays the proof out in classic Fitch notation — a line-number gutter, one vertical scope bar per open subproof, a rule under each assumption, and a justification column:

```text
1 │ P → Q   Premise
2 │ Q → R   Premise
  ├──────
3 │ │ P     Assume
  │ ├──────
4 │ │ Q     →E 1, 3
5 │ │ R     →E 2, 4
6 │ P → R   →I 3–5
```

The classical rule set covers the connectives (`∧I`/`∧E`, `∨I`/`∨E`, `→I`/`→E`, `↔I`/`↔E`, `¬I`, `⊥I`/`⊥E`, `¬E` double-negation, `RAA`, `Reit`), the first-order quantifiers (`∀I`/`∀E`, `∃I`/`∃E`, with eigenvariable side-conditions enforced via capture-avoiding substitution), and equality (`=I`/`=E`, certified against Z3 since `=` is otherwise uninterpreted). A subproof is cited by its line span, e.g. `(3, 5)`; the instantiation/witness term of `∀E`/`∃I` is passed as `extra=[term]`. `⊥` is the reserved constant `FALSUM`. `∀I` discharges a pure eigenvariable box: head it with `flag(n, e)` (rule `"Flag"`) and set `Subproof(..., flag=e)`.

**Non-classical logics.** Pass `logic=` to check a proof under a different consequence relation. In the three-valued **K3**/**LP** logics each step is certified against the many-valued decision procedure, so the paraconsistency facts come out correctly — in **LP** modus ponens is *not* valid, and the checker rejects a proof that uses it:

```python
from unicode_fol_kit import MSFLParser, Proof, premise, line, check_proof
parse = MSFLParser().parse

mp = Proof(premises=[premise(1, parse("P")), premise(2, parse("P → Q"))],
           steps=[line(3, parse("Q"), "→E", 2, 1)], logic="LP")
check_proof(mp)                                                          # → False

# The very same proof is fine classically:
check_proof(Proof(premises=mp.premises, steps=mp.steps, logic="fol"))    # → True
```

For the **modal family** (`logic="K"`/`"T"`/`"S4"`/`"S5"`) each step is certified by the standard translation to FOL plus the frame axioms, decided by Z3. Knowledge (`Knows`) is factive, but belief (`Believes`) is not:

```python
from unicode_fol_kit import Proof, premise, line, check_proof, Atom, Knows, Believes

p = Atom("P", [])

knows = Proof(premises=[premise(1, Knows("a", p))],
              steps=[line(2, p, "T", 1)], logic="S5")
check_proof(knows)      # → True   (K_a P ⊢ P)

believes = Proof(premises=[premise(1, Believes("a", p))],
                 steps=[line(2, p, "T", 1)], logic="S5")
check_proof(believes)   # → False  (B_a P ⊬ P)
```

Classical FOL/MSFOL is checked by the syntactic rule table; K3/LP and the modal family over their propositional fragment. Temporal/quantified-modal/second-order quantification and the Łukasiewicz connectives are out of scope and rejected with a clear message.

## Finding Fitch proofs (backtracking search)

`find_fitch_proof` *finds* a Fitch proof rather than checking a given one: a goal-directed, iterative-deepening backtracking searcher over the classical propositional and first-order rules (complete for the propositional fragment). `fitch_prove` returns a bool, `is_valid_fitch` proves from no premises, and `find_fitch_proof` returns the actual `Proof` (or `None`). Whatever the search assembles is re-validated by `check_proof` before it is returned, so it is sound by construction.

```python
from unicode_fol_kit import find_fitch_proof, fitch_prove, is_valid_fitch
from unicode_fol_kit.fol.nodes import Atom, Or, Not, Implies

P, Q = Atom("P", ()), Atom("Q", ())

fitch_prove([], Or(P, Not(P)))                          # → True (a proof of P ∨ ¬P was found)
is_valid_fitch(Implies(Implies(Implies(P, Q), P), P))   # → True (Peirce's law)

proof = find_fitch_proof([P, Implies(P, Q)], Q)         # returns a Proof (or None)
print(proof.to_fitch())
```

```text
1 │ P       Premise
2 │ P → Q   Premise
  ├──────
3 │ Q       →E 2, 1
```

Like the resolution prover it is sound and, under its depth bound, incomplete: `find_fitch_proof` returning `None` means "no proof found within `max_depth`", never "not a theorem". Classical FOL only (the non-classical checkers above are verification-only).

## Sequent calculus (Gentzen LK, incl. second-order)

A two-sided Gentzen sequent calculus. A sequent `Γ ⊢ Δ` (multisets, read as `⋀Γ → ⋁Δ`) is derived by a tree of inference rules, and `check_sequent_proof` verifies the tree. This is classical **LK** with the first-order quantifier rules *and* the **second-order** rules (`∀²`/`∃²` over predicate variables), so it reaches the second-order fragment that natural deduction / resolution / Z3 cannot. `verify_sequent_proof` returns a `SequentResult` naming the first offending rule.

```python
from unicode_fol_kit import sequent, derive, axiom, check_sequent_proof, render_sequent_proof
from unicode_fol_kit.fol.nodes import Atom, Quantifier, Variable, Constant

x, c = Variable("x"), Constant("c")
def Px(t): return Atom("P", [t])

# ∀x P(x) ⊢ P(c)   via the ∀L rule (instantiating the bound x with the term c)
d = derive(sequent([Quantifier("∀", x, Px(x))], [Px(c)]), "∀L",
           axiom(sequent([Px(c)], [Px(c)])),
           extra=[c])

check_sequent_proof(d)   # → True
print(render_sequent_proof(d))
```

`render_sequent_proof` prints the derivation as an indented tree (conclusion first, premises below, each annotated with its rule):

```text
∀x P(x) ⊢ P(c)   [∀L c]
  P(c) ⊢ P(c)   [Ax]
```

The rule set is `Ax`; the structural rules `WL`/`WR`, `CL`/`CR`, `Cut`; the connective rules `¬L`/`¬R`, `∧L`/`∧R`, `∨L`/`∨R`, `→L`/`→R`, `↔L`/`↔R`, `⊕L`/`⊕R`; the quantifier rules `∀L`/`∀R`, `∃L`/`∃R` (with the eigenvariable condition on `∀R`/`∃L`); and the second-order rules `∀²L`/`∀²R`, `∃²L`/`∃²R` — the second-order rules instantiate a bound predicate variable with a `Comprehension` term `λx̄.ψ` or use a fresh predicate eigenvariable. The instantiation term / eigenvariable / comprehension goes in `extra=[…]`. Full second-order validity is not recursively enumerable, so `check_sequent_proof` is a *checker*, not a complete prover.

## Sequent calculus — intuitionistic LJ

Gentzen's **LJ** is the same calculus restricted to **at most one formula in the succedent** — the single change that makes intuitionistic logic. `check_lj_proof` / `verify_lj_proof` reuse the LK `Sequent` / `Derivation` data model.

```python
from unicode_fol_kit import sequent, derive, axiom, check_lj_proof
from unicode_fol_kit.fol.nodes import Atom, Not, Implies

P = Atom("P", ())
# ⊢ P → ¬¬P  — double-negation *introduction* is intuitionistically valid:
lj_proof = derive(sequent([], [Implies(P, Not(Not(P)))]), "→R",
              derive(sequent([P], [Not(Not(P))]), "¬R",
                  derive(sequent([P, Not(P)], []), "¬L",
                      axiom(sequent([P], [P])))))
check_lj_proof(lj_proof)   # → True
```

The classical route to `P ∨ ¬P` needs a two-formula succedent (`⊢ P, ¬P`), which LJ rejects — so excluded middle, double-negation *elimination*, and Peirce's law have no LJ derivation. The `∨R` rule is split into `∨R1` / `∨R2`; otherwise the rule names match LK.

## Analytic tableaux

A fourth proof method: `is_valid_tableau` (a formula's negation closes), `prove_tableau(premises, conclusion)` (the premises plus the negated conclusion close), `tableau_closed` (a set of formulas is jointly unsatisfiable), and `tableau_model` (an open branch is a satisfying assignment / countermodel). Sound, and complete and decidable for the propositional fragment; first-order γ-instantiation is bounded.

```python
from unicode_fol_kit import (
    MSFLParser, is_valid_tableau, prove_tableau, tableau_closed, tableau_model,
)
p = MSFLParser().parse

is_valid_tableau(p("((P → Q) → P) → P"))         # → True (Peirce, classically)
is_valid_tableau(p("P → Q"))                      # → False
prove_tableau([p("P"), p("P → Q")], p("Q"))       # → True (modus ponens entailment)
tableau_closed([p("P"), p("¬P")])                 # → True (jointly unsatisfiable)
tableau_model([p("P → Q"), p("P")])               # → {'P': True, 'Q': True}
```

`tableau_model` returns a dict mapping each atom's surface form to its truth value, or `None` if every branch closes. Modal formulas are routed to the labelled modal tableau (system **K** by default).

## Finite model finder

The Mace4-style partner of the provers: instead of asking *"does it follow?"*, the model finder asks *"is there a finite structure where it holds?"* by brute-force enumeration of finite `Structure`s over a domain `{0, …, k−1}` for increasing `k`, checking each with the Tarskian evaluator. `find_model` returns a satisfying structure (or `None`), `find_countermodel` returns one satisfying the premises but refuting the conclusion, and `is_satisfiable_finite` / `is_valid_finite` are the boolean wrappers.

```python
from unicode_fol_kit import (
    MSFLParser, find_model, find_countermodel,
    is_satisfiable_finite, is_valid_finite,
)
p = MSFLParser().parse

# A countermodel witnesses a non-entailment: P(tom) does not entail ∀x P(x)
find_countermodel([p("P(tom)")], p("∀x P(x)"), max_size=3)    # → a Structure (not None)

is_valid_finite(p("∀x P(x) → P(tom)"))                        # → True  (no finite countermodel)
is_satisfiable_finite(p("∃x P(x)"))                           # → True
```

Free variables are read as universally quantified. The search is **bounded**: a domain size whose interpretation space is too large is skipped, so `None` (or a `True` from `is_valid_finite`) means "within the bounds searched", not a proof — first-order satisfiability is undecidable, and some satisfiable sentences have only infinite models.

### Many-sorted (MSFOL) model finding

Many-sorted input is handled directly: each named sort gets a non-empty universe (a non-empty subset of the domain), sorted constants are placed inside their sort, and a `SortedQuantifier` ranges over its sort — so a found `Structure` carries a `.sorts` mapping. Sorts may overlap (the relativisation reading).

```python
from unicode_fol_kit import MSFLParser, find_model, find_countermodel

msfol = MSFLParser(many_sorted=True)

theory = [msfol.parse("∀x:Dog Barks(x)"), msfol.parse("Barks(rex:Dog)")]
m = find_model(theory, max_size=3)
sorted(m.sorts.keys())   # → ['Dog']    (the Structure carries its sort universes)

# "all dogs bark" does not entail "all humans bark" — a sorted countermodel exists:
cm = find_countermodel(
    [msfol.parse("∀x:Dog Barks(x)")],
    msfol.parse("∀x:Human Barks(x)"),
    max_size=3,
)
sorted(cm.sorts.keys())  # → ['Dog', 'Human']
```

The returned `Structure` interprets the domain, constants, functions, predicates, and the `sorts` mapping (e.g. `Structure(domain=(0,), constants={'rex': 0}, predicates={('Barks', 1): {(0,)}}, sorts={'Dog': (0,)})`). The exact repr ordering is not guaranteed, so inspect the structure's attributes rather than asserting a literal repr.
