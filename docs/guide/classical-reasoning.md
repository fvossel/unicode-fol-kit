# Classical FOL / MSFOL reasoning

This page covers the reasoning layer for classical first-order logic and its many-sorted extension (MSFOL): four proof methods (resolution, Fitch natural deduction, the Gentzen sequent calculi LK/LJ, and analytic tableaux), SMT solving via Z3, external provers, equivalence checking, and a finite model finder. Every Python block below was executed against the package and its printed result is shown in a trailing `# →` comment.

## Built-in resolution prover

For entailment and validity **without** an external prover, the package ships a self-contained first-order **resolution** prover. It clausifies the input (skolemise → drop the ∀ prefix → CNF → clauses), then refutes `premises ∧ ¬conclusion` by binary resolution and factoring, deriving the empty clause iff the entailment holds.

```python
from unicode_fol_kit import MSFLParser, prove, is_valid_resolution, is_valid

parser = MSFLParser()

premises = [parser.parse("∀x (Human(x) → Mortal(x))"), parser.parse("Human(socrates)")]
prove(premises, parser.parse("Mortal(socrates)"))                    # → True

prove([parser.parse("Human(socrates)")], parser.parse("Mortal(socrates)"))  # → False (no entailment)

is_valid_resolution(parser.parse("P ∨ ¬P"))                          # → True
is_valid_resolution(parser.parse("∃x ∀y L(x, y) → ∀y ∃x L(x, y)"))  # → True
```

More worked entailments — quantifier reasoning, a non-entailment, and a contradictory premise set:

```python
# Barbara syllogism: ∀x(M→P), ∀x(S→M) ⊨ ∀x(S→P)
barbara = [parser.parse("∀x (Man(x) → Mortal(x))"),
           parser.parse("∀x (Greek(x) → Man(x))")]
prove(barbara, parser.parse("∀x (Greek(x) → Mortal(x))"))           # → True

# Existential conclusion from a universal + a witness
prove([parser.parse("∀x P(x)")], parser.parse("∃x P(x)"))           # → True

# Quantifier-shift validity (the converse fails)
is_valid_resolution(parser.parse("∃x ∀y L(x, y) → ∀y ∃x L(x, y)"))  # → True
is_valid_resolution(parser.parse("∀y ∃x L(x, y) → ∃x ∀y L(x, y)"))  # → False (not valid; bound reached)

# A genuinely non-entailing pair saturates to False
prove([parser.parse("P(a) ∨ Q(a)")], parser.parse("P(a)"))          # → False
```

- **Sound, deliberately incomplete.** First-order resolution is only semi-decidable, so `prove` / `is_valid_resolution` take a `max_steps` bound (default 10 000). They return `True` **only** when the empty clause is actually derived, and `False` both when the clause set saturates (genuinely no entailment) and when the bound is reached — they never report a non-theorem as proved.
- **A deadline.** `prove`, `refute` and `is_valid_resolution` also take `timeout=` (milliseconds, `None` by default). It covers the whole call, clausification and normal forms included, and a limit that has run out gives `False`, never a proof (`api.prove` answers `unknown`, and the `detail` of its verdict names the reason `timeout`).
- **Free variables and Skolem symbols.** A free variable of a problem is a *parameter*: `prove` and `is_valid_resolution` read it as one fresh constant, the same in the premises and the conclusion, and never close a premise, so `P(x) ⊢ P(x)` is proved and `P(x) ⊢ P(alpha)` is not. Skolem symbols are `_sk<n>`, fresh against every name of the problem.
- **Many-sorted input** is read with the guard reading described under "Many-sorted quantifiers" below: `sort_axioms` join the clauses as premises, and a sorted constant keeps its identity across formulas (`P(carl:S)`, `∀x (P(x) → Q(x))` ⊢ `Q(carl:S)` is proved).
- **Truth constants.** Clausification drops a clause that holds `$true` or `¬$false` and removes the literals `$false` and `¬$true`, so `{$false}` is the empty clause. The independent checker `atp.resolution_check` has the matching rule `truth_constants`, which accepts the removal of exactly those literals and no other.

### Inspecting the clausal form

`to_clauses(formula)` exposes the clausal form (a `set` of `frozenset`s of literals; the variables of a clause are universal, and `to_clauses` of one standalone formula closes that formula's free variables), and `refute(clauses)` runs the saturation directly — useful for seeing *why* an entailment holds.

```python
from unicode_fol_kit import to_clauses, refute

to_clauses(parser.parse("∀x (P(x) ∨ ¬Q(x))"))
# → a set with one two-literal clause {P(v0), ¬Q(v0)} (the ∀-bound x is renamed apart)

# Refuting premises ∧ ¬conclusion by hand: ∀x(Human→Mortal), Human(c) ⊨ Mortal(c)
clauses = (to_clauses(parser.parse("∀x (Human(x) → Mortal(x))"))
           | to_clauses(parser.parse("Human(socrates)"))
           | to_clauses(parser.parse("¬Mortal(socrates)")))
refute(clauses)   # → True   (the empty clause is derivable ⇒ jointly unsatisfiable)
```

### Equality via paramodulation

The resolution prover handles `=` with built-in paramodulation, reflexivity
resolution, and demodulation — congruence, symmetry, and transitivity are
provable without hand-supplied equality axioms. The rules are unconditionally
sound; completeness for full equational logic is NOT claimed (this remains
the didactic prover — external ATPs and Z3 are the heavy equipment). Every
equality step appears in the proof object and is re-derived by the
independent checker (`atp.resolution_check`). **Watch the naming
convention:** a single lowercase letter like `a` is a *variable*, so use a
multi-character name (`alice`) for a constant individual.

```python
# Paramodulation connects equal constants without any congruence axiom:
prove([parser.parse("alice = bob"), parser.parse("P(alice)")],
      parser.parse("P(bob)"))                                        # → True

# Function congruence, likewise axiom-free:
prove([parser.parse("carl = dave")],
      parser.parse("f(carl) = f(dave)"))                             # → True

# Z3 also decides it natively (see the next section):
is_valid(parser.parse("(alice = bob ∧ P(alice)) → P(bob)"))          # → True
```

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

`get_model` returns a dict mapping each Z3 declaration (constants, uninterpreted predicates/functions) to its interpretation, or `None` when the formula is unsatisfiable or Z3 returns `unknown` within the timeout. The key ordering is not guaranteed. A name declared once keeps its plain key (`P`, `a`). A name declared more than once, such as `P(a)` next to `P(a, b)`, is keyed `P/1` and `P/2`, and a predicate and a function of one name and arity are `P/1:Bool` and `P/1:S`. A REFUTED verdict's countermodel on the Z3 and cvc5 routes, and `get_model_arith`, use the same keys (in `get_model_arith` the function's key ends in its numeric sort, `P/1:Real` or `P/1:Int`).

**Counterexamples.** A formula is *invalid* exactly when its negation is satisfiable, so `get_model(Not(φ))` hands back a concrete refuting assignment — the witness Z3 found:

```python
get_model(Not(parser.parse("P → Q")))   # → {'Q': 'False', 'P': 'True'}  (P true, Q false refutes it)
is_valid(parser.parse("P → Q"))          # → False  (the same fact as a bool)
```

**Entailment** is validity of the implication. Conjoin the premises and check the conditional, or refute its negation to extract the countermodel:

```python
prem = parser.parse("(Human(socrates) ∧ ∀x (Human(x) → Mortal(x)))")
is_valid(parser.parse("(Human(socrates) ∧ ∀x (Human(x) → Mortal(x))) → Mortal(socrates)"))  # → True
is_satisfiable(parser.parse("∀x (P(x) → Q(x)) ∧ P(a) ∧ ¬Q(a)"))  # → False (the entailment holds)
```

**Free variables.** A free variable is a *parameter* of the problem: one unknown element, the same in every premise and in the conclusion (`Γ ⊨ φ` holds when every structure and assignment that satisfies `Γ` satisfies `φ`). No route closes a premise universally, and a route that cannot state the parameter reading refuses the input by name, as the TPTP writers below do.

```python
from unicode_fol_kit import api

api.prove(parser.parse("P(x)"), [parser.parse("P(x)")]).status       # → 'proved'
api.prove(parser.parse("P(alpha)"), [parser.parse("P(x)")]).status   # → 'refuted'  (universe {0, 1}, x = 0, alpha = 1, P = {0})
```

A formula nested a hundred levels deep or more is decided on a worker thread with a larger stack and a raised recursion limit (for that call only), up to a nesting of about eight thousand levels. A backend that still cannot read a deeper one answers `unknown` / `bound_hit` and names the nesting depth in the `detail` of the verdict (in the `reason` of the result of `api.countermodel`); `api.prove` and `api.countermodel` never raise `RecursionError` for it.

### Many-sorted quantifiers (MSFOL), sort non-emptiness and membership

There is one universe. A sort `S` is the **non-empty** extension of the unary predicate of its name, sorts may overlap, a sorted constant `c:S` is an element of `S`, and a sorted quantifier ranges over `S`. A `SortedQuantifier`/`SortedConstant`/`SortedCount` is relativised to plain classical FOL before it reaches Z3 (`∀x:S φ` → `∀x (S(x) → φ)`, `∃x:S φ` → `∃x (S(x) ∧ φ)`, and `c:S` becomes the plain `c`), but that relativisation alone forgets two facts: that `S` is non-empty, and that `c` lies in `S`. **This kit's MSFOL convention supplies both** — the same convention the finite model finder enforces (`semantics.modelfinder`: a sort's universe is always a *non-empty* subset of the domain, and a sorted constant is drawn from it) and TPTP TF0 guarantees the non-emptiness natively. `is_satisfiable` / `is_valid` / `get_model` — and every other classical decision route in the kit (`prove`/`countermodel`, `cvc5`, Prover9, the TPTP `fof` export, `formulas_are_equivalent`, `eval.equivalence.equivalent`'s solver level, the resolution prover and the tableau) — assert `fol.sort_axioms`: one `∃x (S(x))` sentence per sort mentioned and one atom `S(c)` per sorted constant `c:S`, so a solver is never allowed to "cheat" an otherwise-valid many-sorted formula by making a sort's extension empty or by putting a sorted constant outside its sort:

```python
msfol = MSFLParser(many_sorted=True)

# Valid ONLY because Human is non-empty: the antecedent's "for all" is a
# strictly stronger claim than the consequent's "there exists" precisely
# because at least one Human is guaranteed to exist.
is_valid(msfol.parse("(∀x:Human Mortal(x)) → ∃x:Human Mortal(x)"))          # → True

# "every Ghost is P" together with "every Ghost is not-P" is unsatisfiable
# — a witness Ghost would have to be both P and not-P. (Without the
# non-emptiness assumption a solver could instead make Ghost's extension
# empty, satisfying both universals vacuously — this is what a solver is
# no longer allowed to do.)
is_satisfiable(msfol.parse("∀x:Ghost P(x) ∧ ∀x:Ghost ¬P(x)"))               # → False

from unicode_fol_kit import api
api.prove(msfol.parse("(∀x:Human Mortal(x)) → ∃x:Human Mortal(x)"), backends=["z3"]).status  # → 'proved'
```

The membership atom is what makes a sorted conclusion follow from a sorted premise:

```python
all_human = msfol.parse("∀x:Human Mortal(x)")

# socrates is a Human, so the sorted conclusion follows:
api.prove(msfol.parse("Mortal(socrates:Human)"), [all_human]).status    # → 'proved'
# nothing makes the unsorted socrates a Human (universe {0, 1}, Human = {0}, Mortal = {0}, socrates = 1):
api.prove(parser.parse("Mortal(socrates)"), [all_human]).status         # → 'refuted'
# and with no premise nothing makes socrates Mortal (universe {0}, Human = {0}, Mortal = {}):
api.prove(msfol.parse("Mortal(socrates:Human)"), []).status             # → 'refuted'

# the resolution prover reads a sorted constant the same way:
prove([msfol.parse("P(carl:S)"), parser.parse("∀x (P(x) → Q(x))")], msfol.parse("Q(carl:S)"))  # → True
```

The sentences of `sort_axioms` are added as their own extra, top-level, never-negated assumptions alongside whatever is being decided, over the premises and the conclusion alike — never folded inside the per-formula translation itself (`Node.to_z3`/`to_prover9`/`to_tptp` stay polarity-blind, exactly as before). For a `get_model`/`is_satisfiable` call this means extra asserted conjuncts; for `is_valid`/entailment it means extra premises. A REFUTED verdict's countermodel is therefore a legal MSFOL structure: every sort is non-empty and every sorted constant is inside its sort — never a spurious one `semantics.modelfinder` would refuse to consider a model at all. An unsorted formula is completely unaffected: the extra sentences are empty, so the solver call (and its result) is byte-identical to a formula with no sorts. The arithmetic-aware `is_valid_arith` / `is_satisfiable_arith` / `get_model_arith` below carry the identical assumptions — a sort guard is still just an uninterpreted predicate once lowered, even over the (infinite) real/int numeric sort. There a sorted constant inside an atom or a function is the same numeric symbol as the plain constant of that name, a `SortedCount` is lowered (distinct-witness encoding, numeric disequality), and a `SortedCardinality` is refused by name with `NotImplementedError`: a set cardinality has no first-order reading, so use `SortedCount`.

### Subsorting (S < T)

`Signature` can additionally declare a **subsort** relation between sorts (`subsorts={"Human": frozenset({"Animal"})}`, a child sort mapped to its direct declared parents), read with subset semantics: `S < T` means `⟦S⟧ ⊆ ⟦T⟧`, nothing more — no injection/coercion functions, no casts, no operation or predicate overloading across the hierarchy, unlike full CASL order-sorted algebra. `Signature.is_subsort(s, t)` answers the reflexive-transitive closure of the declared direct edges (cycle-checked at construction time), and it is deliberately one-directional: `is_subsort("Human", "Animal")` and `is_subsort("Animal", "Human")` differ the moment only `Human < Animal` is declared.

Three routes honour a declared `subsorts` mapping when asked to:

```python
from unicode_fol_kit import Signature, MSFLParser, subsort_axioms, api
from unicode_fol_kit.semantics.modelfinder import find_countermodel

sig = Signature.from_dict({
    "predicates": {"Mortal": {"arity": 1, "arg_sorts": ["Thing"]}},
    "sorts": ["Human", "Animal", "Thing"],
    "subsorts": {"Human": ["Animal"], "Animal": ["Thing"]},
})
sig.is_subsort("Human", "Thing")   # → True (transitive)
sig.is_subsort("Thing", "Human")   # → False (not symmetric)

msfol = MSFLParser(many_sorted=True)
premise = msfol.parse("∀x:Animal Mortal(x)")
goal = msfol.parse("∀x:Human Mortal(x)")

# Without the subsort edge, the Human and Animal guard predicates are
# unrelated, so the inference does not go through:
api.prove(goal, [premise]).status                          # → 'refuted'

# subsort_axioms gives one ∀x (S(x) → T(x)) per DIRECT edge, added as extra
# premises -- the same contract as nonempty_sort_axioms:
[a.to_unicode_str() for a in subsort_axioms(sig)]
# → ['∀x (Animal(x) → Thing(x))', '∀x (Human(x) → Animal(x))']
api.prove(goal, [premise, *subsort_axioms(sig)]).status    # → 'proved'

# signature= adds the same axioms to the premises of every backend of the chain:
api.prove(goal, [premise], signature=sig).status           # → 'proved'

# semantics.modelfinder's subsorts= kwarg gives the model finder the same
# guarantee, agreeing with the route above:
find_countermodel([premise], goal, subsorts=sig.subsorts)  # → None (no countermodel)

# a name the theory uses only as a predicate is bounded too, because a sort and
# the predicate of its name are one symbol (Human < Animal < Thing):
find_countermodel([msfol.parse("∃x:Human P(x)")], parser.parse("∃x Thing(x)"), subsorts=sig.subsorts)  # → None
```

`signature=` states what a `Signature` declares as the sentences `fol.signature_axioms` returns: the non-emptiness of each declared sort, `S(c)` for a constant declared in `S`, `∀x (S(x) → T(x))` for each subsort edge, and `∀x (A(x) → B(f(x)))` for a unary function `f` declared from `A` to `B`. A predicate's declared `arg_sorts` add nothing, because a predicate is a relation over the whole universe. The sentences, like the side axioms of a `Sentence`, are background: `relevant_premises` holds indices into the caller's own list of premises, and the Z3 core names only those premises, never one of the added sentences. A dict is a `TypeError` (build the `Signature` with `Signature.from_dict`), a logic other than classical first-order a `ValueError`, and the input is not checked against the signature (`api.check` does that). An option that no backend of the chain reads, such as `subsorts=` next to `backends=["z3"]`, is a `ValueError`, and a backend that does not read an option that changes the question (`subsorts=`, a modal `frame=`) while another one does is not run: the chain's verdict lists it as `unknown` / `unsupported`.

`find_model`/`is_satisfiable_finite`/`is_valid_finite` take the identical `subsorts=` mapping and filter the sorted search space against its FULL transitive closure — computed once per search and checked against every pair of names the theory uses as a sort or as a unary predicate, not just the direct edges (with `S < T`, `∃x:S P(x) ⊢ ∃x T(x)` is valid). A theory without any sorted node ignores `subsorts=`. A constant written with two sorts (`c:A` here, `c:B` there) lies in both on every decision route, but `Signature.from_formulas` refuses it with a `ValueError`: a signature is a typed declaration and gives a constant one sort. `fol.casl_export.to_casl_spec` and `fol.casl_import.parse_casl_spec` complete the round trip through CASL's own `sort S < T` syntax: `to_casl_spec([premise], subsorts=sig.subsorts)` emits `sort Animal < Thing` / `sort Human < Animal` lines, and `parse_casl_spec` reads them back into the identical `subsorts` mapping. The axioms are premises, never part of `to_fol`'s own output: that translation is polarity-blind, and an axiom conjoined onto the formula being proved would itself have to be proved. Omitting `subsorts` adds no axiom to any route; the routes that take no signature at all (the TPTP exporters, the ASP/CP lowering) are not affected by it.

### Arithmetic-aware solving

The default `is_satisfiable` / `to_z3` treat everything as one uninterpreted sort, so arithmetic terms are opaque: a numeral is a constant named by its VALUE (`1`, `1.0` and `01` are one constant), nothing else is known about it, `+ - * /` are uninterpreted functions and `< > ≤ ≥` uninterpreted predicates. So `⊢ 1 ≠ 2`, `⊢ 1 < 2` and `⊢ 1 + 1 = 2` are NOT valid on z3, cvc5, the model finder, the tableau and resolution, and the same holds on every other route that was not asked for arithmetic (the TPTP `fof` and TF0 writers, Prover9). The `*_arith` variants instead interpret `+ - * /` and the comparisons over a numeric sort (`"real"` by default, or `"int"`), so the solver can actually reason about numbers. A one-argument minus, which the Prover9 reader builds for `-t` and the SMT-LIB reader for `(- t)`, is the negation: `is_valid_arith(parse_prover9("all x (-x + x = 0)."))` is `True`. Any other operator or comparison at a number of arguments other than two is an uninterpreted symbol.

```python
from unicode_fol_kit import MSFLParser, is_satisfiable_arith, is_valid_arith, get_model_arith

parser = MSFLParser()

is_satisfiable_arith(parser.parse("x + 1 = 2 ∧ x > 0"))      # → True   (x = 1)
is_satisfiable_arith(parser.parse("x > 0 ∧ x < 0"))          # → False
is_valid_arith(parser.parse("∀x (x * 2 = x + x)"))           # → True
get_model_arith(parser.parse("x + 1 = 2 ∧ x > 0"))           # → {'x': '1'}
is_satisfiable_arith(parser.parse("x + x = 1"), sort="int")  # → False (no integer solution)
```

Under `sort="int"` a numeral with a whole value is the integer (`2.0` is `2`), and one with a fractional part (`2.5`) has no integer reading: `is_valid_arith`, `is_satisfiable_arith`, `get_model_arith` and `to_z3_arith` refuse it with `NotImplementedError`, and `sort="real"` reads it.

On a route that was not asked for arithmetic the numerals and the operators are ordinary symbols, and eleven problems come out as follows (`api.prove` with z3, cvc5, Vampire, E, Prover9, the tableau or resolution, and the finite model finder):

| # | problem | valid? | why |
|---|---|---|---|
| 1 | `∀x P(x) ⊢ P(1)` | valid | an instance |
| 2 | `P(1) ⊢ P(1.0)` | valid | one constant |
| 3 | `⊢ 1 ≠ 2` | not valid | a one-element universe |
| 4 | `⊢ 1 < 2` | not valid | `<` may be empty |
| 5 | `⊢ 1 + 1 = 2` | not valid | universe {0, 1}: `1` ↦ 0, `2` ↦ 1, `+` constantly 0 |
| 6 | `P(1), P(2) ⊢ ∃x ∃y (x ≠ y ∧ P(x) ∧ P(y))` | not valid | a one-element universe |
| 7 | `P(1) ⊢ P(one)` | not valid | universe {0, 1}: `1` ↦ 0, `one` ↦ 1, `P` = {0} |
| 8 | `∀x ∀y x + y = y + x ⊢ 1 + 2 = 2 + 1` | valid | an instance |
| 9 | `∀x (x < 2 → Q(x)), 1 < 2 ⊢ Q(1)` | valid | an instance, then modus ponens |
| 10 | `⊢ 2.5 = 2.5` | valid | reflexivity (a decimal is writable) |
| 11 | `P(-1) ⊢ ∃x P(x)` | valid | existential introduction (a negative numeral is writable) |

Rows 1, 2 and 8 to 11 are proved (the model finder finds no countermodel); the tableau has no equality rule, so it leaves row 10 undecided, as it does `⊢ alice = alice`. Rows 3 to 7 are never proved: z3, Vampire and E answer `refuted` (cvc5 too, except for row 6, where it answers `unknown`), the model finder returns a countermodel, and the tableau, resolution and Prover9 answer `unknown`. No route answers the opposite. With `sort="int"` or `sort="real"` (the `*_arith` functions below, or the TFA writer) the numerals are numbers: `is_valid_arith` proves `⊢ 1 ≠ 2` and `⊢ 1 + 1 = 2`.

A `Constant` and a `Variable` of one name are two symbols: with `c = Constant('x')`, `∀x P(x, c)` does not bind `c`, so `∀x P(x, c) ⊢ P(alpha, c)` is valid and `∀x P(x, c) ⊢ P(alpha, alpha)` is not. A countermodel names the constant plainly, and a free variable under its own name too, written `x!v` only next to a constant `x`. A `Number` and a `Constant` spelled alike (`Number(1)` and `Constant('1')`) are refused by name (`NotImplementedError`; `api.prove` answers `unknown` / `unsupported` with the reason), on Z3, cvc5, the model finder, the evaluator and the `fof`, TF0, Prover9, THF, Isabelle and Lean writers.

More arithmetic, over both sorts:

```python
# Triangle inequality is valid over the reals
is_valid_arith(parser.parse("∀x ∀y (x + y ≥ x ∨ y < 0)"))    # → True
# A quadratic equation, solved
get_model_arith(parser.parse("x * x = 4 ∧ x < 0"))           # → {'x': '-2'}
# Integer divisibility-style constraint with an uninterpreted predicate over the numeric sort
is_satisfiable_arith(parser.parse("Prime(7) ∧ x + 3 = 10"), sort="int")  # → True  (x = 7)
# 1/2 has no integer solution but a real one
is_satisfiable_arith(parser.parse("x + x = 1"), sort="int")  # → False
is_satisfiable_arith(parser.parse("x + x = 1"), sort="real") # → True   (x = 1/2)
```

`to_z3_arith(formula, sort=…)` exposes the underlying Z3 expression if you want to drive the solver yourself:

```python
from unicode_fol_kit import to_z3_arith

to_z3_arith(parser.parse("x + 1 > 0"), sort="int")   # → 0 < x!v + 1   (a z3.BoolRef; the free variable x is the symbol x!v)
```

A `Constant` and a `Variable` of one name are two symbols on this route too, because the symbol of a variable carries the suffix `!v`: with `c = Constant('x')`, `is_valid_arith(∀x. x ≤ c)` is `False` and `is_valid_arith(∃x. x < c)` is `True`, because a quantifier binds the variable only. `get_model_arith` reports a constant under its plain name and a free variable under its own name too, as `x!v` only when a constant of that name is part of the formula (`x = 1` with a free `x` and a constant `x = 2` gives `{'x': '2', 'x!v': '1'}`). `ArithEnv` keeps the constants in `.symbols` and the variables in `.variables` (through `get_variable`).

## Equivalence checking (Z3)

`formulas_are_equivalent` checks whether two formulas are logically equivalent (via Z3).

```python
from unicode_fol_kit import MSFLParser, formulas_are_equivalent

parser = MSFLParser()
f1 = parser.parse("¬(P(x) ∧ Q(x))")
f2 = parser.parse("¬P(x) ∨ ¬Q(x)")

formulas_are_equivalent(f1, f2)   # → True

# More classical equivalences:
formulas_are_equivalent(parser.parse("P → Q"), parser.parse("¬Q → ¬P"))          # → True (contraposition)
formulas_are_equivalent(parser.parse("P → Q"), parser.parse("¬P ∨ Q"))           # → True (material implication)
formulas_are_equivalent(parser.parse("∀x ¬P(x)"), parser.parse("¬∃x P(x)"))      # → True (quantifier duality)
formulas_are_equivalent(parser.parse("∀x (P(x) ∧ Q(x))"),
                        parser.parse("∀x P(x) ∧ ∀x Q(x)"))                       # → True (∀ over ∧ distributes)

# A non-equivalence: ∀ does NOT distribute over ∨
formulas_are_equivalent(parser.parse("∀x (P(x) ∨ Q(x))"),
                        parser.parse("∀x P(x) ∨ ∀x Q(x)"))                       # → False
```

The check is symmetric and the arguments are interchangeable. Since it runs over Z3, equality is interpreted, so `formulas_are_equivalent(parser.parse("a = b ∧ b = c"), parser.parse("a = b ∧ a = c"))` is `True`.

## External provers (Prover9 / Vampire)

`check_logical_entailment` (Prover9) and `check_logical_entailment_vampire` (Vampire) decide whether a conclusion follows from a list of premises, each taking the prover's executable path as an argument. **These require the external binary to be installed; the examples below were not executed here.**

```python
# doctest: +SKIP  — requires an installed Prover9 binary; not executed in CI/docs
from unicode_fol_kit import MSFLParser, check_logical_entailment

parser = MSFLParser()
premises = [
    parser.parse("∀x (Human(x) → Mortal(x))"),
    parser.parse("Human(socrates)"),
]
conclusion = parser.parse("Mortal(socrates)")

check_logical_entailment(premises, conclusion, prover9_path="/usr/bin/prover9")  # True

# A Linux Prover9 inside WSL on Windows: the path is the one inside WSL.
check_logical_entailment(premises, conclusion,
                         prover9_path="/mnt/d/prover9/bin/prover9", use_wsl=True)  # True
```

The Vampire variant emits the premises as TPTP `axiom`s and the conclusion as a `conjecture` (Vampire reports `SZS status Theorem` when the entailment holds):

```python
# doctest: +SKIP  — requires an installed Vampire binary; not executed in CI/docs
from unicode_fol_kit import MSFLParser, check_logical_entailment_vampire

# … same premises / conclusion …
check_logical_entailment_vampire(premises, conclusion, vampire_path="/usr/bin/vampire")  # True
```

The Prover9 writer sets `prolog_style_variables`, under which LADR reads a symbol that has no arguments and starts with an upper-case letter as a *variable* (a name that starts with an underscore is a constant to Prover9 itself, and the writer quotes or renames it all the same). A constant `Gaseous` and a bare proposition `Rain` (an atom with no arguments) would therefore say something else, so the writer spells them lower-case-initial (`gaseous`, `rain`; a numeric suffix when that spelling is taken, and a constant and a proposition of one spelling get two different tokens) and records the rename in the `Prover9NameMap` that `generate_prover9_input_with_mapping` returns. A predicate or function *with* arguments (`Human(x)`) keeps its name. The writer keys its symbols on (kind, name, arity): one name at two arities, as a predicate and a function, or as a predicate and a constant is written as different Prover9 symbols. The first claimant keeps the spelling and the others get a numeric suffix (`P` and `P2`, `all2`), all recorded in the returned map; `all` and `exists` are renamed in every role, and so are the names LADR reads as keywords by arity (`if/3`, `end_of_list/0`, `formulas/1` are written `if2`, `end_of_list2`, `formulas2`). `Node.to_prover9()` on a single node cannot rename a constant, so it writes such a name in double quotes: `Constant('Gaseous')` is `"Gaseous"` and `Atom('Rain', [])` is `"Rain"`. LADR keeps a double-quoted symbol with its quotes, so it is never a variable and is not the bare word (on Prover9 2026-8A: `P(Gaseous)` proves `P(c)`, because the bare word is a variable, `P("Gaseous")` does not, and a bare `Rain` as a formula is refused by Prover9). Only a name that would be a variable and holds a character other than a letter, a digit or an underscore (`Gas-eous`) keeps the refusal by name, and a name that starts with `$` (other than `$true` and `$false`) is refused by name by the writer and by the single renderer. The writer itself renames such names instead of quoting them (only numerals are written in double quotes, below). It also refuses every pair of variables of one formula that are written as one, harmless ones too: a variable is written as the upper-case of its name, so `∀x ∃X R(x, X)` would be `(all X (exists X R(X, X)))`; it uses the check the TPTP writers use. The outermost call of `Node.to_prover9()` sees the whole node: a binder inside the scope of a binder of its own name (a free variable of the node counts) is renamed to a fresh variable, the witnesses of a counting quantifier are fresh against every name of the node with its case folded, and `∀x ∃X R(x, X)` is written `(all X (exists X0 R(X, X0)))`. Two variables that no renaming separates (`∀X P(x)`, `P(x) ∧ Q(X)`) and a variable that is no word (`x-1`) are refused by name. The nullary atoms `$true` and `$false` (TPTP's own propositions, which `parse_tptp` produces) are written `$T` and `$F`, Prover9's constants. `check_logical_entailment` takes the wall-clock budget in seconds (`timeout=`, default 30).

Sorts are lowered to guard atoms plus `sort_axioms` first and then sanitised like every other formula: a sort and the unary predicate of its name are one symbol, and for every sorted constant `c:S` the writer asserts `S(c)` as an assumption, using the token the premises use for `c` (a sorted and a plain constant of one name are one symbol). The atoms and the non-emptiness sentences stand in `formulas(assumptions)`, never in `formulas(goals)`; without `S(c)`, `∀x:Human Mortal(x) ⊢ Mortal(socrates:Human)` is not proved. A non-ASCII sort name is renamed like any other symbol. Numerals follow the reading of "Arithmetic-aware solving": one constant per value, written in double quotes (`"1"` for `1` and `1.0`, `"2.5"`, `"-1"`), with no disequalities between numerals; `+ - * / < >` are uninterpreted symbols, a binary minus is written `-(a, b)`, and a `Number` and a `Constant` spelled alike are refused by name. The witnesses of a counting quantifier are fresh against every variable name of the whole problem. A free variable is a parameter: the writer writes one constant for it for the whole problem, so the Prover9 text is closed and `P(x) ⊢ P(alpha)` is not proved. A Łukasiewicz connective has no classical reading and is refused (`unknown` / `unsupported` through `api.prove`). The `solver_version` of a Prover9 verdict is the banner line of `prover9 -h` (Prover9 has no `--version`), for example `Prover9 (64) version 2026-8A, August 2026.`; it is read once per binary, through WSL when that route is used, with a limit of 10 seconds.

On Windows a Linux Vampire or Prover9 installed in WSL can be driven with `use_wsl=True` (the temp problem file's path is translated to its `/mnt/...` form automatically, and `prover9_path` is the path inside WSL). The `prove` backends find the binaries through `$UFK_VAMPIRE` and `$UFK_PROVER9` (the paths inside WSL) with `$UFK_VAMPIRE_WSL=1` and `$UFK_PROVER9_WSL=1`; the `use_wsl` option does the same for one call. For Vampire and E every premise and the conclusion must be a closed sentence, because the TPTP writers refuse a free variable by name (see "Building a TPTP problem for a prover" below). Recall that a single lowercase letter like `x` is a *variable*, so a constant individual needs a multi-character name (`socrates`) or the `c_`-prefix.

### A prover that refuses the problem is an error, not a timeout

Through the backends (`api.prove(..., backends=["vampire"])`, `"eprover"`, `"zipperposition"`, `"twee"`, `"prover9"`) an external prover can end three different ways without a proof, and the verdict keeps them apart: it ran out of time (`unknown` / `timeout`: the kit stops the process when the `timeout` of the call, in milliseconds, is used up — Prover9 included — and E stopping itself at the `--cpu-limit` the kit derives from that budget, which it announces as `Failure: Resource limit exceeded (time)` and `SZS status ResourceOut`, is the same thing; `detail` says which of the two ended the run), it gave up honestly (`unknown` / `incomplete`, `bound_hit` — the prover's own `GaveUp`, a `ResourceOut` that is not E's time limit (E's memory limit, a limit of the prover's own), `Unknown`; Vampire also gives up *without* an SZS line, ending with `Termination reason: Refutation not found, incomplete strategy`, which is how Vampire 5.0.1 ends a non-theorem of a typed-arithmetic problem, and that is `unknown` / `incomplete` too, while a limit of its own, `Time limit` or `Activation limit`, reads `timeout` / `bound_hit`), or it **refused to read the problem** and printed no verdict at all — Vampire's `User error: Non-boolean term ... is used in a formula context`, E's parse error on stderr, Twee's `Error in <file> (line 2, column 1)`, Prover9's fatal-error exit. The third is `status == "error"`, `reason == "infra"`, and `detail` quotes the prover's own message, so a problem the kit's writer got wrong is never filed with the questions that merely ran out of time. A Prover9 that cannot be started (the shell's exit 127 "no such file", which is what `wsl.exe <path>` reports for a path that does not exist inside WSL, or 126 "not executable") is the same verdict, `error` / `infra` with the shell's message, not "no proof"; `api.prove` does not get that far for a path that does not exist inside WSL, because its availability check raises `BackendUnavailable` first (below). Prover9's output is decoded as UTF-8 with undecodable bytes replaced, so a fatal message that cuts a character in half is that error verdict too, not a crash, and Prover9 never reads the caller's standard input. When *every* backend of a `prove` chain (or `portfolio_prove`) failed this way the chain's verdict is itself `error`; when at least one honestly answered `unknown`, the chain stays `unknown` and the failure is quoted in its `detail`. `prove` and `portfolio_prove` plan their options alike (both take `signature=`): a backend is handed only the options it reads, an option that no backend of the chain reads is a `ValueError`, and a backend that cannot read an option that changes the question (`subsorts=`, a modal `frame=`) is not run and is listed `unknown` / `unsupported`. A binary on a non-default route is named with `use_wsl=`, `vampire_path=`, `prover9_path=` or `twee_cmd=` (the other external backends have options of the same kind), and the availability check answers for that route: a named backend whose binary is missing there raises `BackendUnavailable`. The bool-returning entry points (`check_logical_entailment_vampire`, `check_logical_entailment`) keep their historic contract and return `False` for a refused problem; `check_logical_entailment(..., raise_on_rejection=True)` raises `Prover9Rejected` with Prover9's message (the shell's, for a binary that cannot be started) instead, and `raise_on_timeout=True` raises `Prover9TimedOut` for a run the kit stopped. The text a backend quotes, and the excerpt or proof it returns, name the caller's symbols: a name the problem writer changed (`agent` → `agent_term`, a non-ASCII name) is translated back on the `fof`, the many-sorted TF0 and the typed-arithmetic route alike (a sort name is not in the TF0 map and stays as the prover printed it).

### Native typed arithmetic for Vampire/E (TFA)

By default, Vampire/E see a numeral as a constant identified by its value (`1`, `1.0` and `01` are one constant), `+ - * /` as uninterpreted functions and `< > ≤ ≥` as uninterpreted predicates: the `fof` and TF0 writers write them under ordinary words (`n1`, `n2u002e5`, `u002b`, `u003c`) recorded in the name map, so `1 ≠ 2`, `1 < 2` and `1 + 1 = 2` are not provable and no *native* arithmetic decision procedure is active — the exact same reading `is_satisfiable`/`to_z3` have relative to `is_satisfiable_arith`/`to_z3_arith` (see "Arithmetic-aware solving" above). Passing `sort="real"` or `sort="int"` to `check_logical_entailment_vampire` or `check_entailment_vampire_detailed` (or to `api.prove` with `backends=["vampire"]`) switches the exported problem to TPTP's own typed dialect (`tff`, with genuine `$real`/`$int` declarations) instead — mirroring `is_valid_arith`'s/`is_satisfiable_arith`'s own single-numeric-sort design: the WHOLE problem lives in one caller-chosen numeric sort, and an ordinary (non-arithmetic) predicate/function/constant is simply declared over that same sort rather than guessed at.

```python
# doctest: +SKIP  — requires an installed Vampire binary; not executed in CI/docs
from unicode_fol_kit import MSFLParser, check_logical_entailment_vampire

parser = MSFLParser()

check_logical_entailment_vampire(
    [], parser.parse("∀x (x * 2 = x + x)"),
    vampire_path="vampire", use_wsl=True, sort="real")    # → True

# $int vs $real genuinely changes the answer: every integer > 0 is ≥ 1
# (no integer strictly between 0 and 1), but 0.5 is a real counterexample.
check_logical_entailment_vampire(
    [], parser.parse("∀x (x > 0 → x ≥ 1)"),
    vampire_path="vampire", use_wsl=True, sort="int")     # → True
check_logical_entailment_vampire(
    [], parser.parse("∀x (x > 0 → x ≥ 1)"),
    vampire_path="vampire", use_wsl=True, sort="real")    # → False
```

An ordinary predicate coexists with the arithmetic facts in the same problem, declared over the same numeric sort:

```python
# doctest: +SKIP  — requires an installed Vampire binary; not executed in CI/docs
from unicode_fol_kit.atp.vampire_entailment import check_entailment_vampire_detailed

premises = [parser.parse("Prime(seven) ∧ seven + 3 = 10")]
result = check_entailment_vampire_detailed(
    premises, parser.parse("Prime(seven)"),
    vampire_path="vampire", use_wsl=True, sort="int")
result["status"], result["szs_status"]    # → ('proved', 'Theorem')
```

A formula that mixes the numeric sort with a genuinely different one (a `SortedQuantifier`/`SortedConstant`) is refused loudly rather than guessed at — use the many-sorted `tff` route (`sort` omitted, an implicit `SortedQuantifier` present) for that case instead. TFF also has one flat symbol table, so a predicate and a function/constant that would render as the same TPTP identifier — `Price(price(alpha))`, say, whose predicate and function both fold to `price` — are not written under one name: the function or constant is renamed `price_term` and the rename is recorded in the returned map (see "Building a TPTP problem for a prover" below), rather than emitting two conflicting type declarations for one name.

Under `sort="int"` a numeral with a whole value is the integer literal, written with its own digits (`2.0` is written `2`, and `9007199254740993` stays `9007199254740993`); under `sort="real"` it is the real literal (`2` and `2.0` are written `2.0`, and `9007199254740993` is `9007199254740993.0`); `10**400` is written out in full under both. A numeral with a fractional part has no `$int` literal, and the writer refuses it, naming the literal. The fractional numeral is a plain `NotImplementedError`. `/` over `$int` is written `$quotient_e`, the Euclidean quotient (the remainder is never negative, as in Z3's integer division: `-7 / 2` is `-4`), and over `$real` it is `$quotient`. A one-argument minus, which the Prover9 reader builds for `-t` and the SMT-LIB reader for `(- t)`, is written `$uminus(X)`. Every other operator and every comparison is binary, and one at another number of arguments is refused by name with a plain `NotImplementedError` (`atp.z3_arith` reads it as an uninterpreted symbol). A free variable, a predicate or function used at two arities and a name that is both a constant and a function are refused with `TfaRefusal`, which is a `ValueError` and a `NotImplementedError`. Each of these refusals reaches `api.prove` as `unknown` / `unsupported` with the writer's message on `vampire` and `eprover`. An invalid `sort=` stays a plain `ValueError`.

Only Vampire evaluates the typed text. E 3.5.1 reads it, but it types `$sum`, `$difference`, `$product`, `$quotient`, `$quotient_e` and `$uminus` as functions into the individuals and stops with a type error, reads a `$real` literal only approximately (`1.0 = 1.0000001` is a theorem for it), and reads `$less` and the other comparisons as uninterpreted predicates (it answers `GaveUp`). So `sort="int"` or `sort="real"` with `backends=["eprover"]` answers `unknown` / `unsupported`, naming the operator or the numeral, for a problem with `+ - * /` or (under `sort="real"`) any numeral, and `check_entailment_eprover_detailed` raises `NotImplementedError` for it. What is left (comparisons, and integer numerals under `sort="int"`) E answers soundly and usually without arithmetic: `2 < 3` under `sort="int"` is `unknown` / `incomplete`. Use Vampire, or Z3 through `is_valid_arith` and its relatives with `sort=`, for arithmetic. Zipperposition is not refused for `sort=`, and how it reads the typed text is not established.

### Building a TPTP problem for a prover

A TPTP problem is built with the checked writers, never by joining `Node.to_tptp()` strings: `generate_tptp_problem_with_mapping` (classical `fof`), `generate_tff_problem_with_mapping` (many-sorted TF0) and `generate_tff_arith_problem` (one numeric sort, TFA), all exported from `unicode_fol_kit.atp`. (`generate_tptp_problem` and `generate_tff_problem` return the text alone.) `to_tptp()` sees one formula. It checks that formula (see "One formula" below), but it cannot know that `gaseous` in one premise and `Gaseous` in another are two different constants that fold to the same TPTP word, or that the class `Agent` and the role function `agent` share one. A problem assembled from those strings turns such a pair into one symbol and can prove what the premises do not entail. The writers see the whole problem at once, which is why the cross-formula checks and the renaming live there.

```python
from unicode_fol_kit import MSFLParser
from unicode_fol_kit.atp import generate_tptp_problem_with_mapping

parser = MSFLParser()
premises = [parser.parse("∀x Agent(agent(x))")]
conclusion = parser.parse("∃x Agent(x)")

text, name_map = generate_tptp_problem_with_mapping(premises, conclusion)
print(text, end="")
# fof(premise_1, axiom, (![X]: agent(agent_term(X)))).
# fof(goal, conjecture, (?[X]: agent(X))).
name_map.term                                   # → {'agent': 'agent_term'}
```

A refusal opens with the name of the writer that was called. A free variable is refused by name by every one of these writers, in sorted and unsorted problems alike: a prover reads an unbound variable in a `fof` formula as a syntax error, and the kit picks no closure for it (`api.prove` reads a free variable as a parameter, and these writers do not state that reading, so the verdict is `unknown` / `unsupported`).

The `fof`, TF0 and TFA writers take `premise_names=`: one name for each premise the caller gives, written as a TPTP name (quoted when it is not a plain word) and recorded in `TptpNameMap.premises`, so that the premises a proof used can be read back by name (`relevant_premises` of a Vampire verdict and of the result of `check_entailment_eprover_detailed`). The number of names must equal the number of premises given. A name the writer gives its own lines (`goal`, and in a sorted `fof` problem `sort_member_<i>` and `nonempty_sort_<i>`) is a `ValueError` (for `goal` in TF0 a `Tf0Refusal`), and so is a name a prover uses for something else, which is refused at write time: `unknown`, `f<digits>` for Vampire, `c_<i>_<j>` and `i_<i>_<j>` for E. With `premise_names=` given to `api.prove`, the sentences that `signature=` adds and the side axioms of a `Sentence` are background: the writer names them `background_<k>` (with `_` appended when that is one of the caller's names) and they are never reported as the caller's premises, and so are the lines the writer adds for the sorted reading (`sort_member_<i>`, `nonempty_sort_<i>`). A proof that uses them reports the caller's premises only, and the verdict's `detail` names the lines of the sorted reading that it used.

Four things can go wrong with a name, and the writers treat them differently:

| the problem contains | the writer |
|---|---|
| a name TPTP cannot spell (non-ASCII, digit-leading, leading underscore, or any character that is no letter, digit or `_`) | renames it (`świątek` → `u015bwiu0105tek`, `9lives` → `n9lives`, `has-part` → `hasu002dpart`) and records it |
| a predicate and a function/constant that render as the same word (`Agent` and `agent`, `Car` and `car`, a propositional `P` and a constant `p`); in TF0 also a **sort** and a function/constant (`Human` and `human`) | renames the **function or constant** to `<name>_term` (`agent_term`, then `agent_term2` if that is taken) and records it; the predicate (or sort) keeps its name |
| two **legal** names of one kind that fold together (`gaseous` and `Gaseous`, `Foo` and `foo`) | **refuses**, naming both: `NotImplementedError` |
| in TF0, a **sort** and a **predicate** that render as the same word (`Car` the sort and `Car` the predicate) | **refuses**, naming both: `NotImplementedError` |

The second row exists because the provers do not resolve a bare identifier by its position, whatever a TPTP reader may do: Vampire 5.0.1 answers `Non-boolean term agent(X0) of sort $i is used in a formula context` and E 3.5.1 stops with a parse error, so the problem never reaches an SZS status; the TF0 writer used to declare `agent` at two types. Renaming is exact — a symbol is only a name — and the map is what lets a caller translate a proof or a model back:

```python
from unicode_fol_kit.atp import apply_reverse_tptp
from unicode_fol_kit.fol.tptp_input import parse_tptp

[apply_reverse_tptp(item.formula, name_map).to_unicode_str() for item in parse_tptp(text)]
# → ['∀x Agent(agent(x))', '∃x Agent(x)']
```

For prover output that is plain text, `name_map.reverse_rendered()` gives tables keyed by the words actually written; no word is both a predicate and a term in them.

The third row is deliberately different from the first two, for this release. Two legal names of one kind that fold together have always been refused, and that refusal predates the name map; it is kept so that no existing caller silently receives a symbol renamed behind its back, not because the two situations differ in principle. A problem with no clash at all is written byte-for-byte as before.

```python
from unicode_fol_kit.fol.nodes import Atom, Constant

generate_tptp_problem_with_mapping([Atom("Likes", [Constant("gaseous")])],
                                   Atom("Likes", [Constant("Gaseous")]))
# raises NotImplementedError: generate_tptp_problem_with_mapping: distinct constant/function names
# 'gaseous' and 'Gaseous' would both render as the TPTP identifier 'gaseous' …
```

`to_tptp_ncl` (NXF) has no name map to record a rename in, so it refuses the cross-kind case too, naming both kit symbols, and it refuses every sort named with a leading `$`. The TF0 map covers predicates and functions/constants, not sorts. A sort and a **constant** that render as one word cannot coexist (Vampire resolves the constant's name to the type and refuses the problem), which is why the second row of the table renames the constant. A sort and a **predicate** that render as one word are refused, which is the fourth row. Vampire and E would read `human: $tType` next to `human: human > $o`, but the kit defines a sort as the guard predicate of its name (`∀x:S φ` is `∀x (S(x) → φ)`, with `∃x S(x)` for the sort's non-emptiness and `S(c)` for each sorted constant `c:S`; that is what `to_z3`, the `fof` writer and the Prover9 writer do), so there `∃y:Car Car(y)` is valid. TF0 would declare the type `car` and an unrelated predicate `car`, and `∃y:Car Car(y)` is not a theorem of that problem: a prover answering over TF0 would answer another question than z3 does. Rename one of the two, or write the problem with the `fof` writer, which reads the sort as that predicate. (The TFA writer has no sorts and refuses a sorted node by name.) The `fof` writer applies the same reading across formulas: the guard `Foo` of `∀x:Foo P(x)` in one premise and a predicate `foo` in another are one TPTP word, and are refused like any other pair of one kind.

**The TF0 route asks the question of `to_z3`, or refuses.** TF0 *types* things and the guard reading does not. A sorted constant `c:S` is declared `c: s` in TF0 and is a member of `S` in the `fof` text (the `sort_member_<i>` lines), so both say that `c` lies in `S`. The sort of a term that carries no annotation, however, is *inferred* in TF0 from where it is used (a term in an argument position that a `∀x:S` binds is an `S`), whereas the guard reading lets an unannotated constant or a function value be any element. The typed writer therefore refuses a problem whose TF0 text would ask a stronger question, and says why: a function value, or a constant that is annotated nowhere, that the typed text would put into a user sort; and a user sort together with an equation over a variable bound by an unsorted quantifier (an unsorted quantifier ranges over the whole universe, while TF0's `$i` is a type of its own, disjoint from the user sorts). With `tff=True` the backend reports `unknown` / `unsupported` with that reason; with `tff=None` the problem is written as an untyped `fof` problem and answered under the kit's definition, and the verdict's `detail` names the typed writer's message; `tff=False` writes `fof` directly. Measured with Vampire 5.0.1 and E 3.5.1 against `to_z3`:

| input | `to_z3` / `fof` route | TF0 route |
|---|---|---|
| `∀x:Person (Human(x) → Mortal(x))`, `Human(socrates:Person)` ⊢ `Mortal(socrates:Person)` | proved (z3, and Vampire and E on `fof`) | proved (Vampire, E) |
| `∀x:Foo R(x)`, `Q(g(alpha))` ⊢ `R(g(alpha))` | refuted (z3, and Vampire and E on `fof`) | refused: the value of `g` would be typed `Foo` |
| `∀x:Human Mortal(x)` ⊢ `Mortal(socrates)`, `socrates` annotated nowhere | refuted (z3, and Vampire and E on `fof`) | refused: `socrates` would be typed `Human` |
| `∀x ∀y x = y` ⊢ `∀x:A ∀z:A x = z` | proved (z3, and Vampire and E on `fof`) | refused: an equation over an unsorted variable next to the sort `A` |
| no conclusion: `∀x:Foo R(x)`, `¬R(kay:Foo)` | unsatisfiable (z3), `Unsatisfiable` (`fof`: Vampire, E) | `Unsatisfiable` (Vampire, E) |

So `api.prove`'s default chain (z3) and `backends=["vampire"]` / `["eprover"]` (which try TF0 for a sorted problem) give one answer to one input, or the typed route is refused and the `fof` text answers it. The one refusal of the typed writer that is about a name and not about the question is a sort and a predicate that share a name (above).

Three more cases belong with the table. The nullary atoms `$true` and `$false` are TPTP's own propositions, and the kit's reader (`parse_tptp`) produces them as `Atom('$true')` / `Atom('$false')`, so a problem read and written back must keep them: all three writers and `to_tptp()` write them verbatim, never rename or declare them (TF0 and TFA add no type for them), and `to_z3` reads them as true and false, so z3, Vampire and E answer the question the TPTP text asked (`$false` as an axiom is `ContradictoryAxioms`, a proof of everything; `p(a) ⊢ $true` is proved). They are the truth constants on every route and in every reader, spelled `⊤` and `⊥` as well (the kit's own parser reads `⊤` as `$true` and `⊥` as `$false`, and `Atom('⊤')` and `Atom('⊥')` mean the same; Prover9 writes `$T` and `$F`): `⊥ ⊢ Q`, `⊢ ⊤` and `⊢ ¬⊥` are valid and `⊤ ⊢ Q` is not, on z3, cvc5, Vampire, E, Prover9, the tableau and resolution (the provers that only prove answer `unknown` for the last). With arguments (`⊤(a)`) the name is an ordinary predicate. A writer prints the TPTP word and declares nothing for it, and the verdict of the Vampire backend carries `relevant_premises`. Any other `$`-word as a predicate, function or constant name is one of TPTP's own words and is never written as a user symbol: `to_tptp()` refuses it as a *reserved* word, and the writers rewrite it like `has-part` (`$foo` is `u0024foo`). A **variable** that has no TPTP spelling (a variable is written as the upper-case of its name, and a TPTP variable is an upper-case letter then letters, digits and underscores, so `ä` is `Ä`, `x-1`, `1x`) is renamed by the writers to a fresh legal one (`x0`, `x1`, … minted through `fol._identifiers`, per formula, injective and capture-free) and nothing is recorded, because a variable is bound; `to_tptp()` refuses it by name instead. `∀ä P(ä)`, which the kit's own parser reads, reaches a prover and agrees with z3. Last, a predicate the writer has to rewrite never lands on the word of a **sort** (the `fof` writer writes a sort as its guard predicate): the sort `Hasu002dpart` next to the predicate `has-part` gives the predicate `hasu002dpart2`, where it used to be written `hasu002dpart` too and the two were one symbol; an illegal sort name is refused, saying it is the guard of the sort.

A problem needs no conclusion: `generate_tptp_problem_with_mapping(premises)`, `generate_tff_problem_with_mapping(premises)` and `generate_tff_arith_problem(premises, sort="int")` (the conclusion defaults to `None`) write no `conjecture` line, so a prover is asked whether the premises are satisfiable. Vampire answers `SZS status Satisfiable` or `Unsatisfiable`, as z3 does on the nodes (over an arithmetic sort Vampire can refute but not witness, so only `Unsatisfiable` is an answer there). Every check, the renaming and the returned map work on the premises alone.

One predicate used at two arities (`Zed(alpha)` and `Zed(alpha, beta)`) is written `zed(alpha)` and `zed(alpha,beta)`: two symbols, which is how Vampire and E read them and how the z3 route reads them, in one formula as across formulas (z3 overloads a name by its arity, and a model keys the two `Zed/1` and `Zed/2`). The TF0 and TFA writers declare one type per name and refuse it. Prover9 and Twee type a symbol by its name alone (Prover9 stops on a file that uses one name at two arities, and the Prover9 writer gives the later arity a name of its own, as above), so the Twee route (`backends=["twee"]`) writes every arity of a function or constant name except the first under a name of its own (`sym_arity1`, ...), fresh against every name of the problem, and gives the proof and the output back under the caller's names: `ff = aa`, `∀x ff(x) = x ⊢ ff(aa) = aa` is `proved` there, not `error`. A function of no arguments is written by the `fof` writer as the constant of its name.

#### One formula: `to_tptp()`

A single `to_tptp()` call applies the third row to the formula it renders. Two constants (`gaseous`, `Gaseous`), two predicates (`Foo`, `foo`) or two functions (`Bar`, `bar`) that fold to one word are refused, by the same check the writers run:

```python
from unicode_fol_kit.fol.nodes import Atom, Constant, Iff

Iff(Atom("P", [Constant("gaseous")]), Atom("P", [Constant("Gaseous")])).to_tptp()
# raises NotImplementedError: Node.to_tptp: distinct constant/function names 'gaseous'
# and 'Gaseous' would both render as the TPTP identifier 'gaseous' …
```

Without the check this was written `(p(gaseous) <=> p(gaseous))`: a tautology out of a formula that is not valid. The check runs once, in the outermost `to_tptp()` call, over the names the render actually WRITES, so it also sees a name a reduction introduces: `∀x:Foo foo(x)` reduces to `∀x (Foo(x) → foo(x))`, and the sort `Foo` and the predicate `foo` are refused like any other pair. A formula with no such pair is written byte-for-byte as before.

Four more cases are one TPTP word for two symbols, and are refused in the same way. A number and a constant spelled like it (`Number(1)` and `Constant('1')`, which the kit's own TPTP reader makes of `r(1, '1')`) are both `1`; the `fof`, TF0, Prover9, THF, Isabelle and Lean writers refuse the pair too (and the `fof`, TF0, THF, Isabelle and Lean writers a `Number` next to a `Function` of that spelling; Z3, cvc5, the model finder and Prover9 tell a function from a constant by its arity), and `1` and `1.0` are one numeral everywhere. A single `to_tptp()` writes the arithmetic and comparison symbols as TPTP's own words, so there such a symbol and a symbol written like it are one word: `+` is `$sum`, so a function named `$sum` is the same word, and so are `<` and a predicate named `$less`. The writers do not write them so: on a route that was not asked for arithmetic they write numerals and operators as ordinary words (`n1`, `u002b`), and the `$sum` and `$less` clashes arise in the rendering of one formula only. Two variables that are one TPTP variable are refused: a variable is written as the upper-case of its name, so `x` and `X` are one, and `∀x ∃X R(x, X)` would be written `![X]: ?[X]: r(X,X)`, which says something else. That last check is per formula (a formula that binds `x` in one place and `X` in another is refused even where they never meet), and the writers apply it to each formula of a problem, never across two formulas, which bind separately. Last, a name that is not a TPTP word is refused, never written as it is: an unquoted TPTP name is a lower-case letter followed by letters, digits and underscores, so `has-part`, `2008SummerOlympics`, `_x` and a non-ASCII predicate or function name have no rendering that any prover reads (a constant is transliterated, `θ` is `theta`). Use the writers for those: they rewrite the name under a legal replacement and hand back the map. A word that starts with `$` is one of TPTP's own, and is refused as a *reserved* word (`$foo`); the one exception is the pair of nullary atoms `$true` and `$false`, TPTP's defined propositions, which are written as they are and are no symbol of yours. A variable that is written as no TPTP variable (`ä` is `Ä`, `x-1`, `1x`) is refused by name too; the writers rename a variable instead, which needs no map because it is bound.

The first two rows of the table are not applied to one formula, on purpose, because `to_tptp()` renames nothing: a name TPTP cannot spell is refused (above, and see {doc}`transforms`), and a predicate and a function/constant that share a word are rendered as they are:

```python
from unicode_fol_kit.fol.nodes import Atom, Function, Variable

Atom("Agent", [Function("agent", [Variable("e")])]).to_tptp()
# → 'agent(agent(E))'
```

The text is unambiguous by position and this kit's reader (`parse_tptp_formula`) reads it back as the formula it was written from, so there is nothing to refuse; a prover that does not resolve a bare identifier by position is the case the writers rename for, and only a writer can hand back the name map a caller then needs. A rename that the caller cannot translate back would be worse than the text it replaces, so `to_tptp()` does not make one. Use the writers for anything that goes to a prover.

## Proof objects from external provers (TSTP)

The section above only asks a prover *whether* an entailment holds. TPTP-family provers (Vampire, E, …) can also be asked to print the *proof itself*, as annotated **TSTP** text — a sequence of `fof`/`cnf` statements, each citing the rule and parent statements it followed from:

```text
cnf(name, role, formula, inference(rule, [status(thm)], [parent, ...])).
```

`atp.tstp` reads this text into a proof DAG and `atp.tstp_check` re-derives it independently (Robinson unification and Z3 entailment checks it does not share code with any searcher or with the prover that produced the text); `atp.tstp.to_tstp` goes the other way, turning a derivation the kit has already certified into the same TSTP text.

### Reading and checking a Vampire/E proof

`extract_szs_status` pulls the `% SZS status ...` verdict line out of raw prover stdout, `parse_tstp_derivation` turns the `fof`/`cnf` statements into a `TstpDerivation`, and `check_tstp_derivation` re-derives every step from scratch — clausification/normalisation steps by Z3 entailment (`unknown`/timeout never counts as a pass), the core calculus rules (resolution, factoring, superposition, demodulation, equality resolution, subsumption resolution) by an independent from-scratch unifier and alpha-variant search, and a leaf statement by alpha-equivalence against the caller's own premises/conclusion:

```python
from unicode_fol_kit import extract_szs_status, parse_tstp_derivation, check_tstp_derivation
from unicode_fol_kit.fol.tptp_input import parse_tptp_formula

# Captured from `vampire --proof tptp --avatar off` (Vampire 5.0.1) proving
# {∀X (X=a → q(X))} ⊢ q(a).
vampire_proof = """\
% SZS status Theorem for er
% SZS output start Proof for er
fof(f1,axiom,( ! [X0] : (X0 = a => q(X0))), file('er.p',unknown)).
fof(f2,conjecture,( q(a)), file('er.p',unknown)).
fof(f3,negated_conjecture,( ~q(a)), inference(negated_conjecture,[status(cth)],[f2])).
fof(f4,plain,( ~q(a)), inference(flattening,[],[f3])).
fof(f5,plain,( ! [X0] : (q(X0) | a != X0)), inference(ennf_transformation,[],[f1])).
fof(f6,plain,( ( ! [X0] : (q(X0) | a != X0) )), inference(cnf_transformation,[],[f5])).
fof(f7,plain,( ~q(a)), inference(cnf_transformation,[],[f4])).
fof(f8,plain,( q(a)), inference(equality_resolution,[],[f6])).
fof(f9,plain,( $false), inference(forward_subsumption_resolution,[],[f8,f7])).
% SZS output end Proof for er
"""

extract_szs_status(vampire_proof)                       # → 'Theorem'

d = parse_tstp_derivation(vampire_proof)
[s.name for s in d.steps]                                # → ['f1', 'f2', ..., 'f9']

premises = [parse_tptp_formula("! [X] : (X = a => q(X))")]
conclusion = parse_tptp_formula("q(a)")
r = check_tstp_derivation(d, premises, conclusion)
(r.verified, r.refuted)                                   # → (True, True)
```

A **fake** proof is rejected, not merely "not confirmed" — `c3` below claims that resolving `{p(a)}` against `{¬p(a)}` gives `q(b)`; the real resolvent (mgu `{}`, both literals ground) is the *empty* clause, so the independent re-derivation finds no complementary-literal pair whose mgu produces the stated clause:

```python
fake_proof = """\
cnf(c1, plain, p(a)).
cnf(c2, plain, ~p(a)).
cnf(c3, plain, q(b), inference(resolution, [status(thm)], [c1, c2])).
"""
fake = parse_tstp_derivation(fake_proof)
fake_premises = [parse_tptp_formula("p(a)"), parse_tptp_formula("~p(a)")]
fr = check_tstp_derivation(fake, fake_premises, None, query="refutation")
(fr.verified, fr.error)
# → (False, "step 'c3' (checked): 'resolution': no complementary-polarity
#            literal pair's mgu produces the stated clause")
```

`query="refutation"` (used above, no `conclusion`) is for a derivation that already folds `premises ∧ ¬conclusion` into one clause set with no separate conjecture — the framing `atp.resolution` and the writer below both use; `query="conjecture"` (the default, used for the Vampire example) is for a derivation that poses the conclusion as its own `conjecture`-role leaf, exactly what Vampire/E print.

The demodulation checks (`resolution_check`'s `demodulate` rule and the demodulation steps of `check_tstp_derivation`) apply the one-sided matcher of the equation to its other side in one simultaneous step; a unifier's output, whose bindings are triangular, is still followed. A step that reads the matcher as a chain is rejected and the right instance accepted: with `f(X, Y) = g(X)` on `p(f(Y, Z)) | q(Y)`, the clause `p(g(Y)) | q(Y)` is verified and `p(g(Z)) | q(Y)`, which does not follow, is not. A cyclic or self-binding matcher gets a verdict as well.

### Writing a TSTP proof from a certified derivation

`atp.tstp.to_tstp` is the write-side companion: it serialises a `ResolutionStep`/`ResolutionDerivation` (the same proof-object shape `atp.resolution_check.verify_resolution_proof` independently checks — see [Equality via paramodulation](#equality-via-paramodulation) above) as annotated TSTP `cnf(...)` text. It does **not** let the kit export a proof its own search "discovered" — `prove`/`refute` return a bare `bool` and build no derivation trace — it serialises whatever `ResolutionDerivation` the kit has already **certified**, regardless of who built it (a hand-authored fixture, or one transcribed from elsewhere and checked):

```python
from unicode_fol_kit import ResolutionStep, ResolutionDerivation, verify_resolution_proof
from unicode_fol_kit.atp.tstp import to_tstp
from unicode_fol_kit.fol.nodes import Atom, Not, Constant

a = Constant("a")
def P(*args): return Atom("P", list(args))

# {P(a)}, {¬P(a)} resolve directly to the empty clause.
inputs = (frozenset({P(a)}), frozenset({Not(P(a))}))
steps = (
    ResolutionStep(1, frozenset({P(a)}), "input"),
    ResolutionStep(2, frozenset({Not(P(a))}), "input"),
    ResolutionStep(3, frozenset(), "resolve", (1, 2)),
)
deriv = ResolutionDerivation(inputs, steps)
verify_resolution_proof(deriv).ok                         # → True (certified first)

print(to_tstp(deriv))
# cnf(c1, plain, p(a)).
# cnf(c2, plain, ~(p(a))).
# cnf(c3, plain, $false, inference(resolution, [status(thm)], [c1, c2])).
```

`to_tstp` refuses an **uncertified** derivation loudly (`ValueError`, never silently serialising a bogus step), and the text it produces reads back through the SAME `parse_tstp_derivation` used above:

```python
roundtrip = parse_tstp_derivation(to_tstp(deriv))
[(s.name, s.rule, s.parents) for s in roundtrip.steps]
# → [('c1', None, ()), ('c2', None, ()), ('c3', 'resolution', ('c1', 'c2'))]
```

An `"input"` step (0 parents) carries no `inference(...)` source at all — matching how `parse_tstp_derivation` reads a leaf statement — and the kit's own rule names are mapped onto whichever TSTP token `atp.tstp_check`'s checked-rule tables actually dispatch to a matching re-derivation (`resolve`→`resolution`, `factor`→`factoring`, `paramodulate`→`superposition`, `demodulate`→`rw`, `reflexivity`→`equality_resolution` — TSTP does not standardise this vocabulary, so any stable string would parse, but these are the ones `check_tstp_derivation` can actually re-derive rather than merely accept as unchecked). Non-ASCII, digit-leading, or case-colliding kit-level symbol names are sanitised the same way `atp._tptp_problem.generate_tptp_problem_with_mapping` sanitises a TPTP problem file; passing that call's own returned mapping in via `to_tstp(deriv, name_map=mapping)` keeps a proof's symbol spellings identical to a problem file already exported for the same premises.

A `name_map` passed in this way does not have to cover every symbol the derivation uses — a symbol it does not cover is still sanitised, never emitted unchanged, even when a caller's mapping was built from an unrelated problem:

```python
from unicode_fol_kit.atp._tptp_problem import generate_tptp_problem_with_mapping

# A mapping built for a DIFFERENT problem -- it knows "Foo"/"a", nothing else.
_, mapping = generate_tptp_problem_with_mapping(
    [Atom("Foo", [Constant("a")])], Atom("Foo", [Constant("a")])
)

# This derivation's own constant, "9lives", is digit-leading and absent
# from `mapping` -- to_tstp still sanitises it instead of passing it
# through illegally.
nine = Constant("9lives")
c1, c2 = frozenset({P(nine)}), frozenset({Not(P(nine))})
gap_deriv = ResolutionDerivation(
    (c1, c2),
    (ResolutionStep(1, c1, "input"),
     ResolutionStep(2, c2, "input"),
     ResolutionStep(3, frozenset(), "resolve", (1, 2))))
verify_resolution_proof(gap_deriv).ok                     # → True

print(to_tstp(gap_deriv, name_map=mapping))
# cnf(c1, plain, p(n9lives)).
# cnf(c2, plain, ~(p(n9lives))).
# cnf(c3, plain, $false, inference(resolution, [status(thm)], [c1, c2])).
```

A symbol that is *already* TPTP-legal on its own is still checked against its namespace's own round-trip-safe case (predicates conventionally upper-case-initial, constants/functions conventionally lower-case-initial) before being treated as an untouched identity — a lower-case predicate such as `bar` is legal TPTP syntax, but `atp.tstp`'s own reader (`fol.tptp_input`) upper-cases a parsed predicate's first character *unconditionally* on import, so passing `bar` straight through unchanged would make it come back as the different name `Bar`, silently:

```python
from unicode_fol_kit.atp.tstp import apply_reverse_tptp
from unicode_fol_kit.atp._tptp_problem import TptpNameMap

case_deriv = ResolutionDerivation(
    (frozenset({Atom("bar", [a])}), frozenset({Not(Atom("bar", [a]))})),
    (ResolutionStep(1, frozenset({Atom("bar", [a])}), "input"),
     ResolutionStep(2, frozenset({Not(Atom("bar", [a]))}), "input"),
     ResolutionStep(3, frozenset(), "resolve", (1, 2))))
verify_resolution_proof(case_deriv).ok                    # → True

text = to_tstp(case_deriv)
print(text)
# cnf(c1, plain, bar(a)).
# cnf(c2, plain, ~(bar(a))).
# cnf(c3, plain, $false, inference(resolution, [status(thm)], [c1, c2])).

parsed = parse_tstp_derivation(text)
parsed.steps[0].formula
# → Atom(predicate='Bar', args=(Constant(name='a'),))  -- the reader always
#   upper-cases a parsed predicate's first letter, whatever was printed

apply_reverse_tptp(parsed.steps[0].formula, TptpNameMap(predicate={"bar": "Bar"}))
# → Atom(predicate='bar', args=(Constant(name='a'),))  -- to_tstp chose
#   exactly this token internally, so "bar" -- not "Bar" -- comes back
```

`to_tstp` internally chose the token `Bar` for `bar` (not the identity `bar → bar` a plain ASCII-legality check alone would pick), precisely so the reader's own upper-casing on import maps straight back to the original spelling — the rendered TEXT above looks identical either way, since `Node.to_tptp` folds only the first character on export regardless of which token was chosen; only the round trip through the reader reveals the difference. The same case check applies to constants and functions, in the opposite direction (their kit-level convention is lower-case-initial, and unlike a predicate's first letter, the reader never folds a constant/function name's case at all on import — so an unchecked upper-case-initial constant would be unrecoverable outright, not merely differently cased).

## Natural deduction (Fitch proofs)

The provers above decide *whether* an entailment holds; `check_proof` instead **checks a Fitch-style natural-deduction proof** — a derivation with nested subproofs (hypothetical reasoning), per-line justifications, and discharge rules. It is *sound*: it returns `True` only when every line genuinely follows by the cited rule and the proof's premises really do entail its conclusion. `verify_proof` additionally returns a `ProofResult` (fields `ok`, `conclusion`, `premises`, `logic`, `error`, `error_line`).

```python
from unicode_fol_kit import (
    MSFLParser, Proof, Subproof, premise, assume, line, flag,
    check_proof, verify_proof, render_fitch,
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

The classical rule set covers the connectives (`∧I`/`∧E`, `∨I`/`∨E`, `→I`/`→E`, `↔I`/`↔E`, `¬I`, `⊥I`/`⊥E`, `¬E` double-negation, `RAA`, `Reit`), the first-order quantifiers (`∀I`/`∀E`, `∃I`/`∃E`, with eigenvariable side-conditions enforced via capture-avoiding substitution), and equality (`=I`/`=E`, certified against Z3 since `=` is otherwise uninterpreted). A subproof is cited by its line span, e.g. `(3, 5)`; the instantiation/witness term of `∀E`/`∃I` is passed as `extra=[term]`. `⊥` is the reserved constant `FALSUM`. `⊤I` introduces the truth constant `$true` from nothing, and `⊥E` accepts `$false` as well as `FALSUM`; no other formula counts as a truth constant (`⊥E` from `$true` is rejected). `∀I` discharges a pure eigenvariable box: head it with `flag(n, e)` (rule `"Flag"`) and set `Subproof(..., flag=e)`.

### Quantifier proofs — `∀I` (flag box) and `∃E`

A universal conclusion is introduced by a *flag box*: `flag(n, e)` heads a subproof whose eigenvariable `e` may not escape, and `∀I` cites the box's span. The dual `∃E` opens an assumption box for a fresh witness:

```python
from unicode_fol_kit.fol.nodes import Variable
e = Variable("a")

# ∀x(P(x)→Q(x)), ∀x P(x) ⊢ ∀x Q(x)
all_proof = Proof(
    premises=[premise(1, parse("∀x (P(x) → Q(x))")), premise(2, parse("∀x P(x)"))],
    steps=[
        Subproof(
            assumption=flag(3, e),
            body=[line(4, parse("P(a) → Q(a)"), "∀E", 1, extra=[e]),
                  line(5, parse("P(a)"), "∀E", 2, extra=[e]),
                  line(6, parse("Q(a)"), "→E", 4, 5)],
            flag=e,
        ),
        line(7, parse("∀x Q(x)"), "∀I", (3, 6)),
    ],
)
check_proof(all_proof)   # → True

# ∀x(P(x)→Q(x)), ∃x P(x) ⊢ ∃x Q(x)  — ∃E discharges the witness box
ex_proof = Proof(
    premises=[premise(1, parse("∀x (P(x) → Q(x))")), premise(2, parse("∃x P(x)"))],
    steps=[
        Subproof(
            assumption=assume(3, parse("P(a)")),
            body=[line(4, parse("P(a) → Q(a)"), "∀E", 1, extra=[e]),
                  line(5, parse("Q(a)"), "→E", 4, 3),
                  line(6, parse("∃x Q(x)"), "∃I", 5, extra=[e])],
            flag=e,
        ),
        line(7, parse("∃x Q(x)"), "∃E", 2, (3, 6)),
    ],
)
check_proof(ex_proof)   # → True
```

### Equality rules — `=I` and `=E`

Reflexivity `=I` introduces `t = t` from nothing; `=E` rewrites along an equation. Both are certified against Z3 (so they respect the real theory of equality):

```python
# Reflexivity:  ⊢ alice = alice
refl = Proof(premises=[], steps=[line(1, parse("alice = alice"), "=I")])
check_proof(refl)   # → True

# Substitution:  a = b, P(a) ⊢ P(b)   (=E rewrites P(a) using a = b)
eq = Proof(
    premises=[premise(1, parse("a = b")), premise(2, parse("P(a)"))],
    steps=[line(3, parse("P(b)"), "=E", 1, 2)],
)
check_proof(eq)   # → True
```

### `verify_proof` and reading errors

`verify_proof` returns a `ProofResult` — truthy when `ok`, and on failure it names the first offending line and reason:

```python
good = verify_proof(all_proof)
good.ok, good.conclusion.to_unicode_str(), good.logic
# → (True, '∀x Q(x)', 'fol')

# A bogus step — "Q from P by →E" — is rejected with a located error:
bad = Proof(premises=[premise(1, parse("P"))],
            steps=[line(2, parse("Q"), "→E", 1, 1)])
result = verify_proof(bad)
result.ok          # → False
result.error_line  # → 2
result.error       # → 'line 2: →E: needs an implication φ→ψ and its antecedent φ, concluding ψ'
```

A `Proof` also renders itself: `proof.to_fitch()` (Unicode or `ascii=True`) and `proof.to_latex_fitch()` produce the same output as `render_fitch` / `render_latex_fitch`. `proof.to_html()` renders the same proof as a self-contained, theme-aware HTML page — the same idiom that `CCGDerivation.to_html()` (see the [derivation-trees guide](derivations.md)) established: a numbered line gutter, one nested bar per open subproof (the vertical Fitch scope bars, via `border-left`), and a horizontal rule under the premises and under each assumption, styled with CSS custom properties honouring both `prefers-color-scheme: dark` and an explicit `data-theme` override:

```python
html = proof.to_html()
html.startswith("<!doctype html>"), "prefers-color-scheme:dark" in html  # → (True, True)

open("hs_proof.html", "w", encoding="utf-8").write(html)
```

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

For the **modal family** (`logic="K"`/`"T"`/`"S4"`/`"S5"`) each step is certified by the standard translation to FOL plus the frame axioms, decided by Z3. A step whose line and open assumptions together hold a nominal `a` and a user symbol spelled `nom_a` (the reserved world constant of `a`) is refused by name, whichever of the formulas holds which: `ok` is `False` and the message names the symbol and the nominal. The translation's own refusal is applied once to the whole obligation, not formula by formula. Knowledge (`Knows`) is factive, but belief (`Believes`) is not:

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
from unicode_fol_kit.fol.nodes import Atom, And, Or, Not, Implies

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

More searches — note `fitch_prove(premises, goal)` takes premises, `is_valid_fitch(goal)` proves from none:

```python
# Disjunctive syllogism: P ∨ Q, ¬P ⊢ Q
fitch_prove([Or(P, Q), Not(P)], Q)                     # → True

# De Morgan as an implication (no premises)
is_valid_fitch(Implies(Not(And(P, Q)), Or(Not(P), Not(Q))))   # → True

# A reductio-driven theorem the introduction rules alone cannot reach
is_valid_fitch(Or(P, Not(P)))                          # → True (found via RAA)

# A first-order entailment, with the assembled proof rendered
fo = find_fitch_proof([parse("∀x P(x)")], parse("∃x P(x)"))
print(fo.to_fitch())
```

```text
1 │ ∀x P(x)   Premise
  ├──────
2 │ P(a)      ∀E 1 [a]
3 │ ∃x P(x)   ∃I 2 [a]
```

Like the resolution prover it is sound and, under its depth bound, incomplete: `find_fitch_proof` returning `None` means "no proof found within `max_depth`", never "not a theorem". Classical FOL only (the non-classical checkers above are verification-only).

## Sequent calculus (Gentzen LK, incl. second-order)

A two-sided Gentzen sequent calculus. A sequent `Γ ⊢ Δ` (multisets, read as `⋀Γ → ⋁Δ`) is derived by a tree of inference rules, and `check_sequent_proof` verifies the tree. This is classical **LK** with the first-order quantifier rules *and* the **second-order** rules (`∀²`/`∃²` over predicate variables), so it reaches the second-order fragment that natural deduction / resolution / Z3 cannot. `verify_sequent_proof` returns a `SequentResult` naming the first offending rule.

```python
from unicode_fol_kit import (
    sequent, derive, axiom,
    check_sequent_proof, verify_sequent_proof, render_sequent_proof,
)
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

**Propositional LK.** The right rules build the succedent; `¬R` moves a formula across the turnstile and `∨R` takes *both* disjuncts on the right (`Γ ⊢ Δ, A, B`). Classical excluded middle is the canonical two-formula-succedent derivation:

```python
from unicode_fol_kit.fol.nodes import And, Or, Not, Implies

P, Q = Atom("P", ()), Atom("Q", ())

# ⊢ P ∨ ¬P   via ∨R from  ⊢ P, ¬P   via ¬R from  P ⊢ P
em = derive(sequent([], [Or(P, Not(P))]), "∨R",
        derive(sequent([], [P, Not(P)]), "¬R",
            axiom(sequent([P], [P]))))
check_sequent_proof(em)   # → True
print(render_sequent_proof(em))
```

```text
⊢ P ∨ ¬P   [∨R]
  ⊢ P, ¬P   [¬R]
    P ⊢ P   [Ax]
```

`∧R` branches into two premises; here is conjunction commutativity `P ∧ Q ⊢ Q ∧ P`, each branch closed via `∧L`:

```python
PandQ = And(P, Q)
comm = derive(sequent([PandQ], [And(Q, P)]), "∧R",
          derive(sequent([PandQ], [Q]), "∧L", axiom(sequent([P, Q], [Q]))),
          derive(sequent([PandQ], [P]), "∧L", axiom(sequent([P, Q], [P]))))
check_sequent_proof(comm)   # → True
```

`verify_sequent_proof` returns a `SequentResult` — truthy on success, with the end-sequent and (on failure) the first offending rule:

```python
res = verify_sequent_proof(comm)
res.ok, str(res.endsequent), res.error_rule   # → (True, 'P ∧ Q ⊢ Q ∧ P', None)
```

The rule set is `Ax`, with the truth constants as two further axioms (`Γ ⊢ Δ, $true` and `Γ, $false ⊢ Δ`, and no other sequent with a truth constant is an axiom); the structural rules `WL`/`WR`, `CL`/`CR`, `Cut`; the connective rules `¬L`/`¬R`, `∧L`/`∧R`, `∨L`/`∨R`, `→L`/`→R`, `↔L`/`↔R`, `⊕L`/`⊕R`; the quantifier rules `∀L`/`∀R`, `∃L`/`∃R` (with the eigenvariable condition on `∀R`/`∃L`); and the second-order rules `∀²L`/`∀²R`, `∃²L`/`∃²R` — the second-order rules instantiate a bound predicate variable with a `Comprehension` term `λx̄.ψ` or use a fresh predicate eigenvariable. The instantiation term / eigenvariable / comprehension goes in `extra=[…]`. Full second-order validity is not recursively enumerable, so `check_sequent_proof` is a *checker*, not a complete prover.

`derivation.to_html()` renders the same derivation tree as a self-contained, theme-aware HTML page, in the same CCG-idiom `Proof.to_html()` above uses: each node's premises sit above an inference bar with the rule name (and, when present, the instantiation term / eigenvariable / comprehension) to its right — the Gentzen bar-tree picture of the same indented text `render_sequent_proof` prints:

```python
html = comm.to_html()
html.startswith("<!doctype html>"), "data-theme=dark" in html  # → (True, True)

open("comm.html", "w", encoding="utf-8").write(html)
```

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

The contrast is concrete: double-negation *elimination* `⊢ ¬¬P → P` is derivable in **LK** but the very same derivation is rejected by **LJ**, because its `¬R` step would need two formulas (`P, ¬P`) on the right:

```python
from unicode_fol_kit import check_sequent_proof

# ⊢ ¬¬P → P : LK derivation (¬R yields the forbidden two-formula succedent)
dne = derive(sequent([], [Implies(Not(Not(P)), P)]), "→R",
         derive(sequent([Not(Not(P))], [P]), "¬L",
             derive(sequent([], [P, Not(P)]), "¬R",
                 axiom(sequent([P], [P])))))
check_sequent_proof(dne)   # → True   (classically valid in LK)
check_lj_proof(dne)        # → False  (the succedent P, ¬P is illegal in LJ)
```

`∨R1` introduces the left disjunct, `∨R2` the right; here the intuitionistically valid `P ⊢ P ∨ Q`:

```python
disj = derive(sequent([P], [Or(P, Q)]), "∨R1", axiom(sequent([P], [P])))
check_lj_proof(disj)   # → True
```

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

`tableau_model` returns a dict mapping each atom's surface form to its truth value, or `None` if every branch closes. A model that would hold two different atoms written alike under one key (the numeral `1` and the constant `'1'`, a free variable `x` and a constant `x`) is refused by name with `NotImplementedError`. Modal formulas are routed to the labelled modal tableau (system **K** by default).

**Bounds.** The search is a loop over an explicit stack of branches, so a branch is bounded by `max_steps` (default 20 000) and by an optional wall-clock `timeout` in milliseconds, never by Python's recursion limit: a valid chain of several thousand implications closes, and a branch that is too long is "not closed", never a `RecursionError`. First-order γ-instantiation is also bounded by `max_terms` (default 8). Through `api.prove` the answer is `unknown`, and its `detail` names the reason: `bound_hit` when a bound ended the search and `timeout` when the deadline did. A formula nested deeper than the recursive helpers that walk it can follow (about a thousand levels at the default recursion limit) ends a direct call as a bound does (`prove_tableau` gives `False`). The helpers of the proof checker follow fewer levels (a few hundred), and `check_tableau_proof` refuses a proof of a formula nested deeper than they can follow with `TableauCheckError`, not `RecursionError`. `api.prove` reads a formula that deep on a worker thread with a larger stack and decides it up to a nesting of about eight thousand levels; a deeper one gives `unknown` / `bound_hit` with the nesting depth named in the `detail`.

```python
from unicode_fol_kit.fol.nodes import Atom, Implies

# P0, P0 → P1, …, P5999 → P6000 ⊢ P6000, within the default max_steps
chain = [Atom("P0", [])] + [Implies(Atom(f"P{i}", []), Atom(f"P{i + 1}", [])) for i in range(6000)]
prove_tableau(chain, Atom("P6000", []))    # → True
```

Many-sorted input is searched through its guard image (`to_fol`) together with `sort_axioms` as further formulas to refute, so `∀x:Human Mortal(x) ⊢ Mortal(socrates:Human)` is proved and `⊢ Mortal(socrates)` is not; the assignment `tableau_model` returns is over that image. A free variable is a parameter here too: `P(x) ⊢ P(x)` is proved and `P(x) ⊢ P(alpha)` is not. The truth constants close or drop a branch: `$false` and `¬$true` close it, `$true` and `¬$false` are dropped, and `check_tableau_proof` accepts those closures.

**Countermodels from a failed refutation.** When `prove_tableau` is `False`, the open branch *is* the countermodel: run `tableau_model` on the premises together with the negated conclusion to read it off.

```python
prove_tableau([p("P")], p("Q"))            # → False (P does not entail Q)
tableau_model([p("P"), p("¬Q")])           # → {'Q': False, 'P': True}  (the witnessing branch)

# A closed (unsatisfiable) set has no model:
tableau_model([p("P"), p("¬P")])           # → None

# More validities and a satisfiable disjunction
is_valid_tableau(p("(P ∧ Q) → P"))          # → True
is_valid_tableau(p("(P → Q) → (¬Q → ¬P)"))  # → True (contraposition)
tableau_model([p("P ∨ Q"), p("¬P")])        # → {'Q': True, 'P': False}
```

The dict key order is not guaranteed (the branch is a `frozenset`); inspect by key rather than asserting a literal ordering. `is_valid_tableau` also handles the first-order fragment under its γ-bound — note a single lowercase letter is a *variable*, so use a multi-character constant: `is_valid_tableau(p("∀x P(x) → P(socrates)"))` is `True`, and `prove_tableau([p("∀x (Human(x) → Mortal(x))"), p("Human(socrates)")], p("Mortal(socrates)"))` is `True`.

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

**Inspecting and re-checking a found structure.** The returned `Structure` exposes `.domain`, `.constants`, `.functions`, and `.predicates`; `models(formula, structure)` re-evaluates any formula against it, so you can confirm a countermodel does what it claims:

```python
from unicode_fol_kit import models

# A structure where some, but not all, things are P
m = find_model([p("∃x P(x)"), p("∃x ¬P(x)")], max_size=3)
m.domain           # → (0, 1)
m.predicates       # → {('P', 1): {(1,)}}   (P holds of 1, not of 0)

# Re-check the countermodel for P(tom) ⊭ ∀x P(x)
cm = find_countermodel([p("P(tom)")], p("∀x P(x)"), max_size=3)
models(p("P(tom)"), cm)        # → True   (premise holds…)
models(p("∀x P(x)"), cm)       # → False  (…conclusion fails — a genuine countermodel)
```

**Validity vs. satisfiability, contrasted.** A *valid* sentence has no finite countermodel; an *unsatisfiable* one has no finite model at all:

```python
is_valid_finite(p("(P ∧ (Q ∨ R)) ↔ ((P ∧ Q) ∨ (P ∧ R))"))  # → True   (distributivity)
is_valid_finite(p("∃x P(x) → ∀x P(x)"))                      # → False  (a 2-element countermodel exists)
is_satisfiable_finite(p("P(a) ∧ ¬P(a)"))                     # → False  (contradiction: no model)
is_satisfiable_finite(p("∀x ∃y R(x, y)"), max_size=2)        # → True   (a 2-element model suffices)
```

A free variable is a parameter (see "Free variables" under Z3 above): it is not read as universally quantified, and no premise is closed. `find_countermodel([P(x)], P(alpha))` finds a countermodel and reports the variable under its own name; a problem that holds a variable and a constant of the same spelling is refused with `NotImplementedError` naming the variable. A numeral is one constant per value: a countermodel lists `1` once whatever its spelling, and a `Number` and a `Constant` of one spelling are refused.

```python
cm = find_countermodel([p("P(x)")], p("P(alpha)"), max_size=3)
cm.constants                                                      # → {'alpha': 0, 'x': 1}
find_countermodel([p("P(1.0)")], p("P(2)"), max_size=3).constants  # → {'1': 0, '2': 1}
```

The search is **bounded**: a domain size whose interpretation space is too large is skipped (raise `max_size` / `max_candidates` for harder problems), so `None` (or a `True` from `is_valid_finite`) means "within the bounds searched", not a proof — first-order satisfiability is undecidable, and some satisfiable sentences have only infinite models. `find_model` and `find_countermodel` also take `timeout=` (milliseconds, `None` by default) and return `None` when it ends the search; `search_model` and `search_countermodel` return a `ModelSearch` whose `timed_out` tells a deadline from an exhausted size bound. `is_satisfiable_finite` and `is_valid_finite` take no timeout.

```python
from unicode_fol_kit.semantics.modelfinder import search_model

# a transitive, irreflexive, serial relation has no finite model, and 1 ms is not enough to search for one
no_finite_model = [p("∀x ∃y R(x, y)"), p("∀x ¬R(x, x)"), p("∀x ∀y ∀z (R(x, y) ∧ R(y, z) → R(x, z))")]
search_model(no_finite_model, max_size=6, timeout=1).timed_out   # → True
search_model(no_finite_model, max_size=2).timed_out              # → False  (every size up to 2 was searched)
```

### Many-sorted (MSFOL) model finding

Many-sorted input is handled directly, in one domain: each named sort is a non-empty subset of it, a `SortedQuantifier` ranges over its sort, and sorts overlap freely — so a found `Structure` carries a `.sorts` mapping. A sorted constant lies in EVERY sort it is written with (it is drawn from the intersection of their universes, so the answer does not depend on which annotation is read first), and `c:S` in one place and a plain `c` in another are one constant; an unsorted constant and a function value may be any element. A sort and the unary predicate of the same name are ONE symbol: the predicate is not enumerated on its own, and the returned `Structure` holds that one extension in both `.sorts` and `.predicates`, so `⊢ ∃y:Car Car(y)` has no countermodel and `Mortal(socrates:Human) ⊢ Human(socrates)` has none (a predicate of another arity with a sort's name is a different symbol). Every structure it returns is accepted by `semantics.tarski.check_structure`.

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

# a sort and the unary predicate of its name are one symbol, so this has no countermodel:
find_countermodel([], msfol.parse("∃y:Car Car(y)"), max_size=3)  # → None
```

The returned `Structure` interprets the domain, constants, functions, predicates, and the `sorts` mapping (e.g. `Structure(domain=(0,), constants={'rex': 0}, predicates={('Barks', 1): {(0,)}}, sorts={'Dog': (0,)})`). The exact repr ordering is not guaranteed, so inspect the structure's attributes rather than asserting a literal repr.

`models` and `satisfies` evaluate in a structure you supply, and a structure that is not a structure of the definition is refused with `semantics.tarski.IllegalStructureError` (a `ValueError`) instead of being given a truth value: a sort that is empty or holds an element outside the domain, a name that is a sort and a unary predicate with two extensions, a sorted constant outside its sort. A sorted constant of an undeclared sort is a `KeyError`, like `∀x:Undeclared`, and an atom `S(t)` over a name that the structure knows only as a sort reads the sort. `tarski.check_structure(structure, *formulas)` and `structure_violations` check everything up front; the evaluator itself checks what it reads, so a branch that is short-circuited is not read.

```python
from unicode_fol_kit.semantics.tarski import Structure

outside = Structure(domain=(0, 1), constants={"socrates": 1}, predicates={("Human", 1): {(0,)}}, sorts={"Human": (0,)})
models(msfol.parse("Mortal(socrates:Human)"), outside)
# raises IllegalStructureError: sorted constant socrates:Human denotes 1, which is not in the sort 'Human' ([0])
```

## Truth tables (propositional)

For the **propositional** fragment, the most direct decision method is the truth table: `truth_table` enumerates every assignment to a formula's atoms and records the formula's value under each. The convenience predicates `is_tautology`, `is_contradiction`, and `is_satisfiable_tt` read off the result. Each distinct atom *surface-form* is one column (`P` and `P(a)` are different columns, and `r(1)` is one column for the numerals `1` and `1.0`); two different atoms that are written alike are refused by name with `NotImplementedError`, as under `tableau_model` above; quantified formulas have no finite table and raise `ValueError`.

```python
from unicode_fol_kit import (
    MSFLParser, truth_table, is_tautology, is_contradiction, is_satisfiable_tt,
)
p = MSFLParser().parse

is_tautology(p("P ∨ ¬P"))            # → True
is_contradiction(p("P ∧ ¬P"))        # → True
is_satisfiable_tt(p("P ∧ Q"))        # → True
is_tautology(p("(P → Q) → P"))       # → False  (fails when P false, Q true)
```

A `TruthTable` carries the `atoms` columns, the `rows`, the `logic`, and the same predicates as properties; `render()` (also `str(table)`) emits a GitHub-flavoured Markdown table:

```python
table = truth_table(p("P → Q"))
table.atoms            # → ('P', 'Q')
table.is_tautology     # → False
table.is_satisfiable   # → True
print(table.render())
```

```text
| P | Q | P → Q |
|---|---|---|
| T | T | T |
| T | F | F |
| F | T | T |
| F | F | T |
```

Each row is `(assignment, value, designated)` with the values aligned to `atoms`:

```python
table.rows[0]   # → ((1.0, 1.0), 1.0, True)   (P=1, Q=1 ⇒ P→Q = 1, designated)
```

### Three-valued tables — K3 and LP

Pass `logic="K3"` (strong Kleene) or `logic="LP"` (Priest's paraconsistent logic) for the three-valued tables over `{0, ½, 1}`. They differ only in their *designated* values: K3 designates `{1}`, LP designates `{½, 1}`. The classical truths split apart — excluded middle is an LP tautology but not a K3 one, and `P ∧ ¬P` is not an LP contradiction:

```python
is_tautology(p("P ∨ ¬P"), logic="LP")     # → True   (½ is designated in LP)
is_tautology(p("P ∨ ¬P"), logic="K3")     # → False  (value ½ when P = ½)
is_contradiction(p("P ∧ ¬P"), logic="LP") # → False  (paraconsistent: not always undesignated)

print(truth_table(p("P ∨ ¬P"), logic="K3").render())
```

```text
| P | P ∨ ¬P |
|---|---|
| 1 | 1 |
| ½ | ½ |
| 0 | 1 |
```

These three-valued verdicts agree with the Fitch checker's K3/LP regime and the many-valued matrices documented in the [non-classical logics guide](nonclassical.md).
