# Choosing a tool

The kit spans several proof methods, a model finder, and a wide non-classical periphery across many logics. The tables below map a question (and a logic) to the entry point that answers it; each entry point is documented in detail in its own section. After the tables, the **Worked recipes** section gives one short, runnable example for every row — copy a recipe, change the formula, and you have a working program.

Three things hold across the whole kit:

- **Parse first.** Every reasoning entry point takes an AST `Node`, not a string. You get one from a parser — `MSFLParser().parse` for classical FOL, with flags `many_sorted` / `fuzzy` / `modal` / `second_order` for the other modes — or from an importer (`parse_tptp`, `parse_prover9`, `parse_smtlib`, `parse_latex`).
- **A single lowercase letter is a *variable*; a constant needs a multi-character name** (`socrates`, `tom`). This trips up almost every first formula.
- **Decidable vs. semidecidable vs. bounded.** Truth tables, propositional tableaux, matrices, ALC, and (propositional) modal/intuitionistic validity *terminate with a verdict*. Resolution and Fitch are *semidecidable* (they may not halt on a non-theorem). The finite model finder and the second-order / quantified non-classical searches are *bounded* — a negative result means "not found within the bound", not a proof.

## Which tool for which question

| Your question | Use | Returns | Sound / complete / decidable |
|---|---|---|---|
| Is this valid / does Γ entail φ? (general FOL, no external solver) | `prove`, `is_valid_resolution` | bool | sound; refutation-complete; **semidecidable** |
| Same, with an SMT solver | `is_valid`, `is_satisfiable`, `get_model` (Z3) | bool / model | sound & complete on Z3's decidable fragment |
| Same, via an external FO prover | `check_logical_entailment` (Prover9), `check_logical_entailment_vampire` | bool | sound; complete for FOL; needs the binary |
| Propositional / modal tautology? (decidably) | `is_valid_tableau`, `prove_tableau`, `tableau_closed` | bool | sound & complete; decidable propositionally; routes modal inputs to the native modal tableau |
| Modal validity in-process (no external solver) | `is_modal_valid`, `modal_decide`, `modal_countermodel` (`atp.modal_tableau`) | bool / verdict / Kripke counter-model | sound & complete for propositional **K, T, D, B, K4, K45, S4, S5, KD45** |
| Check a Fitch proof I wrote | `check_proof`, `verify_proof` | bool / `ProofResult` | sound; FOL/MSFOL by rule table, K3/LP + modal propositionally |
| Find a Fitch proof | `find_fitch_proof`, `fitch_prove`, `is_valid_fitch` | `Proof` / bool | sound; complete propositionally, depth-bounded FO |
| Check a sequent (LK) derivation | `check_sequent_proof`, `verify_sequent_proof` | bool / `SequentResult` | sound; reaches the second-order fragment |
| Check an intuitionistic (LJ) derivation | `check_lj_proof`, `verify_lj_proof` | bool | sound for intuitionistic consequence |
| Find a model / countermodel | `find_model`, `find_countermodel`, `is_satisfiable_finite`, `is_valid_finite` | `Structure` / None / bool | finite search up to size N; enumerates sort universes for MSFOL |
| Find a second-order model / decide finite SO validity | `so_find_model`, `so_find_countermodel`, `so_is_valid_finite` | `Structure` / None / bool | bounded finite-model search |
| Truth table (classical / K3 / LP) | `truth_table`, `is_tautology`, `is_contradiction`, `is_satisfiable_tt` | `TruthTable` / bool | decidable; propositional only |
| Finite-valued matrix / Belnap–Dunn FDE consequence | `TruthMatrix` (`semantics.matrix`); `K3_MATRIX`, `LP_MATRIX`, `FDE_MATRIX` | matrix verdicts | decidable; propositional, any finite matrix |
| Intuitionistic validity (prop. or first-order) | `int_valid`, `int_countermodel` | bool / `IntKripkeModel` | decidable propositionally; bounded Kripke search for quantifiers |
| Evaluate truth in a structure | `satisfies` (FOL/MSFOL), `satisfies_so`/`holds` (SO), `satisfies_modal` (modal) | bool | direct Tarskian / Kripke / finite SO semantics |
| Same, on a LARGE structure from real data | `evaluate_in_structure`, `evaluate_detailed` over `FiniteStructure` ({doc}`model-checking`) | bool / `EvalResult` | index-driven, no normal form; computed predicates; budget exhausts to UNKNOWN, never False |
| Turn a molecule into a structure | `chem.mol_to_structure`, `chem.parse_chemlog_tptp` | `FiniteStructure` / Node | needs the `[chem]` extra (RDKit); atoms are individuals |
| Audit a whole DEFINITION SET, not one formula | `check_theory`, `check_satisfiable`, `check_subsumption`, `find_cycles` ({doc}`verification`) | reports with countermodels | prover chain + finite model finder; cycles reported as a proven defect |
| Is this definition satisfied by almost anything? | `minimal_model_size`, `generality_report`, `is_vacuous_specialisation` | smallest model / verdict | bounded search; `underdetermined` is an indication, not a proof of error |
| Exact probability bounds / query | `prob.entailment_bounds` (Nilsson), `prob.query` (distribution semantics) ({doc}`probabilistic`) | `Fraction` interval / `Fraction` | exact, no sampling; bounded by atom / choice-fact count |
| Decide modal validity with a real prover (Isabelle installed) | `isabelle_decide_modal` | `ModalVerdict` (valid / invalid / unknown) | sound (kernel-checked proof or genuine nitpick countermodel); incomplete |
| Fuzzy degree or decision (Łukasiewicz / Gödel / product) | `fuzzy_evaluate(…, tnorm=)`; `fuzzy_is_valid(…, tnorm=)`, `fuzzy_is_satisfiable`, `fuzzy_get_model` | degree / bool | real-arithmetic decision via Z3; quantifiers grounded over a finite domain |
| Description-logic concept reasoning (ALC) | `concept_satisfiable`, `subsumes`, `equivalent`, `abox_consistent` (`unicode_fol_kit.dl`) | bool | sound & complete; tableau with TBox internalisation and blocking |
| Read a formula back as English | `to_english` | str | readability aid, not a parse inverse |
| Check / canonicalize a formula before reasoning | `validate_text`, `is_wellformed`, `formulas_are_equivalent`, `canonicalize` | report / bool / Node | static checks; equivalence via Z3 |
| Import a problem from another format | `parse_tptp`, `parse_prover9`, `parse_smtlib`, `parse_latex` | Node(s) | round-trips into the same AST |

## Worked recipes

One runnable example per question above, in reading order. They share these imports — later recipes assume `parse` and the helpers are already defined:

```python
from unicode_fol_kit import *
from unicode_fol_kit import is_modal_valid, modal_decide, modal_countermodel
import unicode_fol_kit.dl as dl

parse = MSFLParser().parse        # classical FOL
```

### I want to … decide validity / entailment (general FOL, no external solver)

`is_valid_resolution` decides a single formula by refutation; `prove` decides `premises ⊨ conclusion`. Both are sound and refutation-complete, but only *semidecidable* — bound the work with `max_steps` if you suspect a non-theorem.

```python
is_valid_resolution(parse("(∀x P(x)) → P(a)"))   # → True

prove(
    [parse("∀x (Human(x) → Mortal(x))"), parse("Human(socrates)")],
    parse("Mortal(socrates)"),
)                                                 # → True

prove([parse("P → Q")], parse("Q → P"))          # → False  (converse does not follow)
```

### I want to … decide validity / get a model with Z3

`is_valid` / `is_satisfiable` call Z3; `get_model` returns a satisfying assignment (or `None`). Z3 is sound and complete on its decidable fragment and is the fastest default for ground / propositional / EPR-shaped problems.

```python
is_valid(parse("(P → Q) ↔ (¬Q → ¬P)"))   # → True   (contraposition)
is_satisfiable(parse("P ∧ ¬Q"))           # → True
get_model(parse("P ∧ ¬Q")) is not None    # → True   (a concrete model exists)
```

### I want to … decide FOL with an external prover

`check_logical_entailment` (Prover9) and `check_logical_entailment_vampire` (Vampire) are complete for FOL but need the binary installed, so they are not run here.

```python
# needs an installed Prover9 binary
check_logical_entailment(
    [parse("∀x (P(x) → Q(x))"), parse("P(a)")],
    parse("Q(a)"),
    prover9_path="/usr/bin/prover9",
)   # → True   # doctest: +SKIP
```

### I want to … decide a propositional / modal tautology

`is_valid_tableau` is a decidable analytic-tableau check for the propositional fragment; `prove_tableau` takes premises; `tableau_closed` reports whether a set of formulas is jointly unsatisfiable.

```python
is_valid_tableau(parse("P ∨ ¬P"))                       # → True
prove_tableau([parse("P → Q"), parse("P")], parse("Q")) # → True   (modus ponens)
tableau_closed([parse("P"), parse("¬P")])               # → True   (P, ¬P clash)
```

### I want to … decide modal validity in-process

`is_modal_valid` returns a bool over a named frame; `modal_decide` returns the verdict string `"valid"` / `"invalid"`; `modal_countermodel` returns a refuting `KripkeModel`. Frames: **K, T, D, B, K4, K45, S4, S5, KD45**.

```python
mp = MSFLParser(modal=True).parse

is_modal_valid(mp("□(P → Q) → (□P → □Q)"), frame="K")   # → True   (K axiom holds everywhere)
is_modal_valid(mp("□P → P"), frame="K")                 # → False  (T axiom needs reflexivity)
modal_decide(mp("□P → P"), frame="T")                   # → 'valid'

cm = modal_countermodel(mp("□P → P"), frame="K")
cm is not None                                          # → True   (a Kripke refutation)
```

### I want to … check a Fitch proof I wrote / find one

`check_proof` verifies a `Proof`; `find_fitch_proof` searches for one (depth-bounded), `fitch_prove` / `is_valid_fitch` are its boolean wrappers.

```python
proof = find_fitch_proof([parse("P → Q"), parse("P")], parse("Q"))
proof is not None        # → True
check_proof(proof)       # → True   (re-verify the found proof)

is_valid_fitch(parse("P → P"))   # → True
```

### I want to … check a sequent (LK / LJ) derivation

`sequent` / `derive` / `axiom` build a derivation tree; `check_sequent_proof` verifies it (classical **LK**, reaching the second-order fragment), `check_lj_proof` verifies the single-succedent **LJ** restriction (intuitionistic).

```python
from unicode_fol_kit import sequent, derive, axiom
x, c = Variable("x"), Constant("c")
Px = lambda t: Atom("P", [t])

lk = derive(sequent([Quantifier("∀", x, Px(x))], [Px(c)]), "∀L",
            axiom(sequent([Px(c)], [Px(c)])), extra=[c])
check_sequent_proof(lk)   # → True   (∀L instantiates ∀x P(x) to P(c))

P = Atom("P", ())
lj = derive(sequent([], [Implies(P, Not(Not(P)))]), "→R",
        derive(sequent([P], [Not(Not(P))]), "¬R",
            derive(sequent([P, Not(P)], []), "¬L",
                axiom(sequent([P], [P])))))
check_lj_proof(lj)        # → True   (P → ¬¬P is intuitionistically valid)
```

### I want to … find a (counter)model by finite search

`find_model` returns a `Structure` satisfying a theory; `find_countermodel` satisfies the premises but refutes the conclusion; `is_valid_finite` / `is_satisfiable_finite` are the booleans. The search is bounded by `max_size`.

```python
find_model([parse("∃x (P(x) ∧ ¬Q(x))")]) is not None        # → True

cm = find_countermodel([parse("P(tom)")], parse("∀x P(x)"), max_size=3)
cm is not None                                              # → True

is_valid_finite(parse("∀x P(x) → P(tom)"))                  # → True   (no finite countermodel)
```

### I want to … find a second-order model / decide finite SO validity

Parse with `second_order=True`. `so_is_valid_finite` decides over finite models up to `max_size`; `so_find_model` / `so_find_countermodel` return witnesses.

```python
so = MSFLParser(second_order=True).parse

so_is_valid_finite(so("∀P (P(a) → P(a))"))   # → True
so_find_model(so("∃P ∃x P(x)")) is not None  # → True
```

### I want to … build a truth table (classical / K3 / LP)

`truth_table(φ, logic=…)` builds a `TruthTable`; `is_tautology` / `is_contradiction` / `is_satisfiable_tt` are classical boolean shortcuts. Each distinct atom is a propositional variable.

```python
is_tautology(parse("P → P"))         # → True
is_contradiction(parse("P ∧ ¬P"))    # → True

truth_table(parse("P ∨ ¬P"), logic="classical").is_tautology   # → True
truth_table(parse("P ∨ ¬P"), logic="K3").is_tautology          # → False  (½ ∨ ½ = ½)
truth_table(parse("(P → Q) ∨ (Q → P)"), logic="LP").is_tautology  # → True
```

### I want to … reason in an arbitrary finite-valued matrix (incl. FDE)

`matrix_is_valid` / `matrix_entails` / `matrix_is_satisfiable` evaluate over a `TruthMatrix`. The kit ships `K3_MATRIX`, `LP_MATRIX`, `FDE_MATRIX`. FDE is paraconsistent — it blocks explosion.

```python
matrix_is_valid(parse("P ∨ ¬P"), K3_MATRIX)   # → False  (Kleene: no designated ½)
matrix_is_valid(parse("P ∨ ¬P"), LP_MATRIX)   # → True   (Priest designates ½)

matrix_entails([parse("P")], parse("P ∨ Q"), FDE_MATRIX)              # → True
matrix_entails([parse("P"), parse("¬P")], parse("Q"), FDE_MATRIX)    # → False  (no explosion)
```

### I want to … decide intuitionistic validity / get a Kripke countermodel

`int_valid` is decidable propositionally and does a bounded Kripke search for quantifiers; `int_countermodel` returns the refuting `(IntKripkeModel, world)` pair.

```python
int_valid(parse("P ∨ ¬P"))          # → False  (excluded middle is not intuitionistic)
int_valid(parse("¬¬(P ∨ ¬P)"))      # → True   (its double negation is)

int_countermodel(parse("¬¬P → P")) is not None   # → True  (DNE fails — countermodel found)
```

### I want to … evaluate truth in a structure I built

`satisfies` evaluates a closed FOL/MSFOL formula in a hand-built `Structure`; `satisfies_so` / `holds` do the second-order case; `satisfies_modal` evaluates against a `KripkeModel`.

```python
S = Structure(domain=(0, 1), constants={"tom": 0},
              predicates={("P", 1): {(0,)}})

satisfies(parse("P(tom)"), S)    # → True
satisfies(parse("∀x P(x)"), S)   # → False  (P fails at 1)
```

### I want to … decide a fuzzy degree or fuzzy validity

Parse with `fuzzy=True`. `fuzzy_evaluate` returns the degree of a formula under a `[0,1]` valuation; `fuzzy_is_valid` / `fuzzy_is_satisfiable` decide via Z3 reals. Pick the t-norm with `tnorm="lukasiewicz"` / `"godel"` / `"product"`.

```python
fp = MSFLParser(fuzzy=True).parse

round(fuzzy_evaluate(fp("P ⊗ Q"), {"P": 0.6, "Q": 0.7},
                     tnorm="lukasiewicz"), 2)   # → 0.3   (max(0, .6+.7−1))
fuzzy_is_valid(fp("P → P"), tnorm="lukasiewicz")   # → True
```

### I want to … reason about ALC concepts / an ABox

Use `unicode_fol_kit.dl`. Build concepts with `dl.Atomic` / `dl.And` / `dl.Exists` / …, axioms with `dl.TBox().add(...)`, facts with `dl.ABox()`. Then `dl.subsumes` / `dl.concept_satisfiable` / `dl.equivalent` / `dl.abox_consistent`.

```python
t = dl.TBox()
t.add(dl.Atomic("Dog"), dl.Atomic("Mammal"))
t.add(dl.Atomic("Mammal"), dl.Atomic("Animal"))

dl.subsumes(dl.Atomic("Dog"), dl.Atomic("Animal"), t)   # → True   (transitivity)
dl.concept_satisfiable(dl.And(dl.Atomic("A"), dl.Not(dl.Atomic("A"))))  # → False
```

### I want to … read a formula back as English / check it statically

`to_english` verbalizes a formula; `validate_text` returns a `ValidationReport`; `is_wellformed` and `formulas_are_equivalent` are quick booleans.

```python
to_english(parse("∀x (Human(x) → Mortal(x))"))
# → 'for every x, if x is human, then x is mortal'

is_wellformed(parse("P ∧ Q"))                                   # → True
formulas_are_equivalent(parse("P → Q"), parse("¬Q → ¬P"))      # → True
```

### I want to … import a problem from another format

The importers return the *same* AST every reasoning function consumes, so you can pipe an external problem straight into a prover.

```python
phi = parse_tptp_formula("![X] : (p(X) => q(X))")
phi.to_unicode_str()   # → '∀x (P(x) → Q(x))'

psi = parse_latex(r"\forall x\, (P(x) \rightarrow Q(x))")
is_valid_resolution(Implies(psi, parse("P(a) → Q(a)")))   # → True
```

## Logics supported

| Logic | Enable | Operators added | Semantics | What can decide / reason about it |
|---|---|---|---|---|
| Classical FOL | `MSFLParser()` | ∀ ∃ ∧ ∨ ¬ → ↔ ⊕ = ≠ | `satisfies()` | resolution, Z3, Prover9/Vampire, tableaux (prop.), Fitch, LK, finite model finder |
| Many-sorted FOL (MSFOL) | `many_sorted=True` | sorted `∀x:S`, `c:S` | `satisfies()` | resolution / Z3 (via `to_fol()`), Fitch; `find_model` enumerates sort universes |
| Fuzzy (FL) | `fuzzy=True` | weak ∧ ∨, strong ⊗ ⊕, Łuk ¬ → ↔ | `fuzzy_evaluate()` | `fuzzy_is_valid` / `fuzzy_is_satisfiable` (Z3 reals); Łukasiewicz / Gödel / product t-norms |
| Many-sorted fuzzy (MSFL) | `many_sorted=True, fuzzy=True` | sorts + Łukasiewicz | `fuzzy_evaluate()` | `fuzzy_*` (Z3 reals); `to_msfol()` lowers to classical |
| Modal / temporal / epistemic / deontic | `modal=True` | □ ◇, K_a B_a, Ⓖ Ⓕ Ⓝ Ⓤ, Ⓞ Ⓟ (+ past-tense ⒣ ⒫ ⒴ ⒮) | `satisfies_modal()` | native modal tableau (`is_modal_valid` / `modal_decide`); `standard_translation()` → Z3/resolution; `qml_is_valid`; Fitch (K/T/S4/S5, prop.) |
| Many-valued K3 / LP / FDE | `MSFLParser()` + `logic=` / `semantics.matrix` | classical syntax over {0, ½, 1} / four-valued | `kleene_value()`; `TruthMatrix` | `truth_table`, three-valued `is_valid`; `K3_MATRIX` / `LP_MATRIX` / `FDE_MATRIX`; Fitch under `logic="K3"`/`"LP"` |
| Second-order | `second_order=True` | ∀P ∃P over predicate vars | `satisfies_so()` / `holds()` | `satisfies_so` on finite models; `so_is_valid_finite` / `so_find_model` (bounded search); LK (`∀²`/`∃²`). Rejects `to_z3`/`to_prover9`/`to_tptp` |
| Intuitionistic | `MSFLParser()` + intuitionistic tools | classical syntax | `IntKripkeModel.forces()` | `int_valid` / `int_countermodel` (decidable prop.; bounded first-order search); LJ (`check_lj_proof`) |
| Description logic ALC | `unicode_fol_kit.dl` | ⊤ ⊥, ¬ ⊓ ⊔, ∃r.C ∀r.C | concept/ABox interpretations | `concept_satisfiable` / `subsumes` / `equivalent` / `abox_consistent` (tableau) |
| Free / dynamic-epistemic / counterfactual / circumscriptive | `semantics.free_logic`, `semantics.dynamic_epistemic`, `semantics.conditional`, `semantics.nonmonotonic` | logic-specific | per-module model classes | free-logic evaluation, public-announcement (PAL) updates, Lewis-sphere counterfactuals, circumscriptive non-monotonic entailment |

Every non-fuzzy logic above also has a **higher-order exporter** in `unicode_fol_kit.hol` — a Benzmüller-style shallow embedding emitted as an Isabelle/HOL theory or a TPTP THF problem for an external prover (Leo-III / Satallax / Sledgehammer) — and, with a local Isabelle installed, `isabelle_decide_modal` actually *runs* it to decide modal validity.

### Recipes for the peripheral logics

The four small evaluators each build an AST from `unicode_fol_kit.fol.nodes` and reason over an explicit, hand-built model. See {doc}`nonclassical` for the full treatment; these are the one-line "is this the tool I want?" probes.

**Free logic** — universal instantiation fails when a constant is non-denoting:

```python
from unicode_fol_kit.fol.nodes import Atom, Implies, Quantifier, Variable, Constant
from unicode_fol_kit.semantics.free_logic import FreeModel, free_holds

xv, cc = Variable("x"), Constant("c")
all_P = Quantifier("∀", xv, Atom("P", [xv]))
m = FreeModel(outer=(0, 1), existing=frozenset({0}), constants={"c": 1},
              predicates={("P", 1): frozenset({(0,)})})

free_holds(all_P, m)                              # → True   (∀x P(x) over {0})
free_holds(Implies(all_P, Atom("P", [cc])), m)    # → False  (UI invalid: c is non-existing)
```

**Public-announcement (dynamic epistemic) logic** — knowledge changes after a truthful announcement:

```python
from unicode_fol_kit.fol.nodes import Knows
from unicode_fol_kit.semantics.dynamic_epistemic import announce, box_announce

pp = Atom("p", ())
Kap = Knows("a", pp)
M = KripkeModel([0, 1], {"K:a": {(0, 0), (0, 1), (1, 0), (1, 1)}}, {0: {"p"}})

satisfies_modal(Kap, M, 0)         # → False  (a does not yet know p)
box_announce(M, 0, pp, Kap)        # → True   ([p!] K_a p — announcing p makes a know it)
```

**Counterfactual conditionals** — Lewis-sphere "would" / "might", non-monotone in the antecedent:

```python
from unicode_fol_kit.fol.nodes import And as FAnd, Not as FNot
from unicode_fol_kit.semantics.conditional import CounterfactualModel, would

A, B, C = Atom("A", ()), Atom("B", ()), Atom("C", ())
CF = CounterfactualModel(
    (0, 1, 2),
    {0: frozenset(), 1: frozenset({"A", "B"}), 2: frozenset({"A", "C"})},
    {0: [frozenset({0}), frozenset({0, 1}), frozenset({0, 1, 2})]},
)

would(CF, 0, A, B)              # → True   (if A were, B would be)
would(CF, 0, FAnd(A, C), B)    # → False  (strengthening the antecedent breaks it)
```

`cf_valid` / `cf_countermodel` lift this from one model to a whole class; `centering="none"` / `"weak"` (default) / `"strong"` picks which of Lewis's V / VW / VC that class is — see [Further non-classical logics](nonclassical.md).

**Circumscription (non-monotonic entailment)** — minimal-model reasoning that strengthening can retract:

```python
from unicode_fol_kit.fol.nodes import Implies as FImplies
from unicode_fol_kit.semantics.nonmonotonic import minimal_entails

a = Constant("a")
Pa, Qa = Atom("P", [a]), Atom("Q", [a])

minimal_entails([FImplies(Pa, Qa)], FNot(Qa), circumscribed={"P", "Q"}, max_size=2)        # → True
minimal_entails([FImplies(Pa, Qa), Pa], FNot(Qa), circumscribed={"P", "Q"}, max_size=2)   # → False
```

### Recipes for the exporters and bridges

**Standard translation** lowers a modal formula to first-order logic so the classical provers can take it:

```python
mp = MSFLParser(modal=True).parse
standard_translation(mp("□P → P")).to_unicode_str()
# → '∀w0 (R(w, w0) → P(w0)) → P(w)'
```

**Quantified modal validity** in-process, choosing the domain mode (`constant` / `varying` / `increasing` / `decreasing`):

```python
qml_is_valid(mp("◇∃x P(x) → ∃x ◇P(x)"), mode="constant", frame="S5")   # → True
qml_equivalent(mp("□P"), mp("¬◇¬P"), frame="K")                        # → True
```

**Higher-order THF / Isabelle export** for an external HOL prover — `to_thf_modal` returns a THF problem string:

```python
thf = to_thf_modal(mp("□P → P"), mode="constant", frame="K")
isinstance(thf, str) and "thf" in thf   # → True   (a TPTP THF problem ready for Leo-III / Satallax)
```

## Composing parser modes

The four core parser modes form the `many_sorted` × `fuzzy` 2×2; the **modal** and **second-order** modes are each "classical unsorted FOL + one extension" and do not combine with sorts, fuzziness, or each other. The **dependence**, **linear**, and **lambek** modes are standalone logics (their connectives and semantics replace the classical ones), so they combine with nothing. The constructor rejects an unsupported combination with a clear `ValueError`. (The matrix, ALC, intuitionistic, relevant, and peripheral logics are separate subsystems, not parser flags.)

| Combine… | with sorts | with fuzzy | with modal | with second-order |
|---|---|---|---|---|
| **base FOL** | ✅ MSFOL | ✅ FL | ✅ modal | ✅ second-order |
| **sorts** | — | ✅ MSFL | ❌ | ❌ |
| **fuzzy** | ✅ MSFL | — | ❌ | ❌ |
| **modal** | ❌ | ❌ | — | ❌ |
| **second-order** | ❌ | ❌ | ❌ | — |

## The frontier families

The families this page used to list as out of scope now ship first-class:

- **Hybrid logic H(@)** — nominals and the satisfaction operator, inside the modal mode (`MSFLParser(modal=True)` parses `@i (P ∧ ◇j)`); Kripke evaluation via `KripkeModel(nominals=…)` and validity per frame via `hybrid_is_valid`. See {doc}`hybrid`.
- **Relevant logic B** — Routley–Meyer semantics over the classical syntax; `rel_valid` / `rel_countermodel` refute the paradoxes of material implication. See {doc}`relevant`.
- **Dependence / IF logic** — team semantics over finite structures: `MSFLParser(dependence=True)` parses `=(x, y)` and `∃y/{x} φ`; evaluate with `team_satisfies` / `team_models`. See {doc}`dependence`.
- **Substructural logics** — `MSFLParser(linear=True)` (⊗ & ⊕ ⊸ ! 𝟙, prover `ill_prove`) and `MSFLParser(lambek=True)` (• \ /, decision procedure `lambek_derivable`). See {doc}`substructural`.
