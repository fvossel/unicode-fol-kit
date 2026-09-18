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

### Inspecting the clausal form

`to_clauses(formula)` exposes the clausal form (a `set` of `frozenset`s of literals, variables implicitly universally quantified), and `refute(clauses)` runs the saturation directly — useful for seeing *why* an entailment holds.

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

`get_model` returns a dict mapping each Z3 declaration (constants, uninterpreted predicates/functions) to its interpretation, or `None` when the formula is unsatisfiable or Z3 returns `unknown` within the timeout. The key ordering is not guaranteed.

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

### Many-sorted quantifiers (MSFOL) and sort non-emptiness

A `SortedQuantifier`/`SortedConstant`/`SortedCount` is relativised to plain classical FOL before it reaches Z3 (`∀x:S φ` → `∀x (S(x) → φ)`, `∃x:S φ` → `∃x (S(x) ∧ φ)`), but that relativisation alone says nothing about whether `S` is empty. **This kit's MSFOL convention is that no sort is ever empty** — the same convention the finite model finder enforces (`semantics.modelfinder`: a sort's universe is always a *non-empty* subset of the domain) and TPTP TF0 guarantees natively. `is_satisfiable` / `is_valid` / `get_model` — and every other classical decision route in the kit (`prove`/`countermodel`, `cvc5`, Prover9, the TPTP `fof` export, and `eval.equivalence.equivalent`'s solver level) — assert one `∃x (S(x))` sentence per sort mentioned, so a solver is never allowed to "cheat" an otherwise-valid many-sorted formula by making a sort's extension empty:

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

The non-emptiness sentences are added as their own extra, top-level, never-negated assumptions alongside whatever is being decided — never folded inside the per-formula translation itself (`Node.to_z3`/`to_prover9`/`to_tptp` stay polarity-blind, exactly as before). For a `get_model`/`is_satisfiable` call this means an extra asserted conjunct; for `is_valid`/entailment it means an extra premise. A REFUTED verdict's countermodel is therefore always a legal MSFOL structure (every sort non-empty) — never a spurious empty-sort one `semantics.modelfinder` would refuse to consider a model at all. An unsorted formula is completely unaffected: the extra sentences are empty, so the solver call (and its result) is byte-identical to a formula with no sorts. The arithmetic-aware `is_valid_arith` / `is_satisfiable_arith` / `get_model_arith` below carry the identical assumption — a sort guard is still just an uninterpreted predicate once lowered, even over the (infinite) real/int numeric sort.

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

# semantics.modelfinder's subsorts= kwarg gives the model finder the same
# guarantee, agreeing with the route above:
find_countermodel([premise], goal, subsorts=sig.subsorts)  # → None (no countermodel)
```

`find_model`/`is_satisfiable_finite`/`is_valid_finite` take the identical `subsorts=` mapping and filter the sorted search space against its FULL transitive closure — computed once per search and checked against every sort pair the theory actually scans, not just the direct edges. `fol.casl_export.to_casl_spec` and `fol.casl_import.parse_casl_spec` complete the round trip through CASL's own `sort S < T` syntax: `to_casl_spec([premise], subsorts=sig.subsorts)` emits `sort Animal < Thing` / `sort Human < Animal` lines, and `parse_casl_spec` reads them back into the identical `subsorts` mapping. The axioms are premises, never part of `to_fol`'s own output: that translation is polarity-blind, and an axiom conjoined onto the formula being proved would itself have to be proved. Omitting `subsorts` everywhere reproduces every route's prior behaviour byte-for-byte; routes that take no signature at all (the TPTP exporters, the ASP/CP lowering) are unchanged.

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

to_z3_arith(parser.parse("x + 1 > 0"), sort="int")   # → 0 < x + 1   (a z3.BoolRef)
```

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
```

The Vampire variant emits the premises as TPTP `axiom`s and the conclusion as a `conjecture` (Vampire reports `SZS status Theorem` when the entailment holds):

```python
# doctest: +SKIP  — requires an installed Vampire binary; not executed in CI/docs
from unicode_fol_kit import MSFLParser, check_logical_entailment_vampire

# … same premises / conclusion …
check_logical_entailment_vampire(premises, conclusion, vampire_path="/usr/bin/vampire")  # True
```

On Windows a Linux Vampire installed in WSL can be driven with `use_wsl=True` (the temp problem file's path is translated to its `/mnt/...` form automatically). Every premise and the conclusion must be a closed sentence — Vampire rejects free variables, and recall that a single lowercase letter like `x` is a *variable*, so a constant individual needs a multi-character name (`socrates`) or the `c_`-prefix.

### Native typed arithmetic for Vampire/E (TFA)

By default, Vampire/E see `+ - * /` and `< > ≤ ≥` as plain TPTP dollar-word symbols with no type attached — they cannot activate their *native* arithmetic decision procedures on them, the exact same gap `is_satisfiable`/`to_z3` have relative to `is_satisfiable_arith`/`to_z3_arith` (see "Arithmetic-aware solving" above). Passing `sort="real"` or `sort="int"` to `check_logical_entailment_vampire`, `check_entailment_vampire_detailed`, or the equivalent E functions in `unicode_fol_kit.atp.eprover_backend` switches the exported problem to TPTP's own typed dialect (`tff`, with genuine `$real`/`$int` declarations) instead — mirroring `is_valid_arith`'s/`is_satisfiable_arith`'s own single-numeric-sort design: the WHOLE problem lives in one caller-chosen numeric sort, and an ordinary (non-arithmetic) predicate/function/constant is simply declared over that same sort rather than guessed at.

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

A formula that mixes the numeric sort with a genuinely different one (a `SortedQuantifier`/`SortedConstant`) is refused loudly rather than guessed at — use the many-sorted `tff` route (`sort` omitted, an implicit `SortedQuantifier` present) for that case instead. TFF also has one flat symbol table (unlike the classical `fof` route, where syntactic position alone tells a predicate from a function apart), so a predicate and a function/constant that would render as the same TPTP identifier — `Price(x)` alongside `price(x)`, say, both folding to `price` — is refused for the same reason, rather than silently emitting two conflicting type declarations for one name.

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

The rule set is `Ax`; the structural rules `WL`/`WR`, `CL`/`CR`, `Cut`; the connective rules `¬L`/`¬R`, `∧L`/`∧R`, `∨L`/`∨R`, `→L`/`→R`, `↔L`/`↔R`, `⊕L`/`⊕R`; the quantifier rules `∀L`/`∀R`, `∃L`/`∃R` (with the eigenvariable condition on `∀R`/`∃L`); and the second-order rules `∀²L`/`∀²R`, `∃²L`/`∃²R` — the second-order rules instantiate a bound predicate variable with a `Comprehension` term `λx̄.ψ` or use a fresh predicate eigenvariable. The instantiation term / eigenvariable / comprehension goes in `extra=[…]`. Full second-order validity is not recursively enumerable, so `check_sequent_proof` is a *checker*, not a complete prover.

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

`tableau_model` returns a dict mapping each atom's surface form to its truth value, or `None` if every branch closes. Modal formulas are routed to the labelled modal tableau (system **K** by default).

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

Free variables are read as universally quantified. The search is **bounded**: a domain size whose interpretation space is too large is skipped (raise `max_size` / `max_candidates` for harder problems), so `None` (or a `True` from `is_valid_finite`) means "within the bounds searched", not a proof — first-order satisfiability is undecidable, and some satisfiable sentences have only infinite models.

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

## Truth tables (propositional)

For the **propositional** fragment, the most direct decision method is the truth table: `truth_table` enumerates every assignment to a formula's atoms and records the formula's value under each. The convenience predicates `is_tautology`, `is_contradiction`, and `is_satisfiable_tt` read off the result. Each distinct atom *surface-form* is one column (`P` and `P(a)` are different columns); quantified formulas have no finite table and raise `ValueError`.

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
