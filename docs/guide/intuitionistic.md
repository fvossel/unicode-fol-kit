# Intuitionistic logic

Intuitionistic propositional validity is **decided** by Kripke-model search; the first-order fragment (0.9.0) is a sound, bounded counter-model search over increasing-domain Kripke models. The same (in)validities are confirmed by the **LJ** sequent-calculus checker and by the Gödel–McKinsey–Tarski embedding into S4.

Intuitionistic logic drops the law of excluded middle and double-negation elimination. Its models are **Kripke models**: a partial order of *worlds* (stages of knowledge) with a monotone forcing relation (once an atom is forced at a world it stays forced at every later world). The connectives `→` and `¬` quantify over future worlds, which is exactly what makes `P ∨ ¬P` and `¬¬P → P` fail.

## Propositional validity and counter-models

`int_valid(formula)` returns a bool; `int_countermodel(formula)` returns either `None` (when the formula is valid) or a pair `(model, world)` — an `IntKripkeModel` and the index of a world that fails to force the formula. For a propositional formula the search is a genuine **decision procedure**: intuitionistic propositional logic has the finite-model property, so the search over Kripke models up to `max_worlds` worlds (default 3) is exhaustive, and `None` proves validity.

```python
from unicode_fol_kit import MSFLParser, int_valid, int_countermodel

p = MSFLParser().parse  # parser uses Unicode operators: →  ¬  ∧  ∨  ∀  ∃

int_valid(p("P ∨ ¬P"))               # → False   excluded middle (LEM)
int_valid(p("¬¬P → P"))              # → False   double-negation elimination (DNE)
int_valid(p("((P → Q) → P) → P"))    # → False   Peirce's law

int_valid(p("P → ¬¬P"))              # → True    double-negation *introduction*
int_valid(p("¬¬(P ∨ ¬P)"))           # → True    LEM is not refutable
int_valid(p("P → P"))                # → True
```

Each invalidity comes with an explicit `IntKripkeModel`. The canonical two-world refutation of LEM, DNE, and Peirce is the same chain `w0 ≤ w1`: an earlier world that knows nothing and a later world that has learned `P`.

```python
model, world = int_countermodel(p("P ∨ ¬P"))
model.forces(world, p("P ∨ ¬P"))     # → False   the witness genuinely fails
```

In the returned model one world forces `P` while a `≤`-earlier world does not, so at that earlier world `¬P` also fails (a still-later world forces `P`) — hence neither disjunct of `P ∨ ¬P` is forced there. The same model refutes `¬¬P → P` (`¬¬P` holds at the earlier world but `P` does not). For Peirce's law `int_countermodel` likewise returns a two-world model rather than `None`. Build a model by hand and query it directly with `IntKripkeModel.forces(world, formula)` if you want to check a specific frame.

## The GMT embedding into S4

Intuitionistic propositional logic has no truth-functional semantics, but Gödel (1933) and McKinsey–Tarski (1948) showed it embeds *faithfully* into the modal logic **S4**: `A` is intuitionistically valid iff its box-translation `T(A)` is S4-valid. `gmt_translate` (in `unicode_fol_kit.hol`) prefixes `□` exactly where the intuitionistic clauses quantify over future worlds — `T(p)=□p`, `T(¬A)=□¬T(A)`, `T(A→B)=□(T(A)→T(B))`, and `∧`/`∨` pass through.

```python
from unicode_fol_kit.hol import gmt_translate

gmt_translate(p("P ∨ ¬P")).to_unicode_str()   # → '□P ∨ □¬□P'
```

The S4 accessibility relation is precisely the intuitionistic `≥` pre-order, which is why `P ∨ ¬P`, `¬¬P → P`, and Peirce's law translate to S4 non-theorems while `P → ¬¬P` becomes a theorem. The companion exporters `to_thf_intuitionistic` and `to_isabelle_intuitionistic` emit the translated problem as a THF file / loadable Isabelle theory (with an S4 — reflexive, transitive — frame). They *emit* a sound problem; they do not themselves run a prover.

## LJ sequent calculus

Gentzen's **LJ** is the classical sequent calculus **LK** with one decisive restriction: a sequent's **succedent holds at most one formula**. That single change blocks the classical theorems that fail intuitionistically. `check_lj_proof(derivation)` returns a bool; `verify_lj_proof(derivation)` returns a `SequentResult` with the end-sequent and, on failure, the first offending rule and reason. Derivations reuse the LK `sequent` / `derive` / `axiom` builders.

Double-negation *introduction* `⊢ P → ¬¬P` has an LJ derivation:

```python
from unicode_fol_kit import sequent, derive, axiom, check_lj_proof
from unicode_fol_kit.fol.nodes import Atom, Not, Implies

P = Atom("P", ())
NNP = Not(Not(P))                     # ¬¬P

proof = derive(sequent([], [Implies(P, NNP)]), "→R",
           derive(sequent([P], [NNP]), "¬R",
               derive(sequent([P, Not(P)], []), "¬L",
                   axiom(sequent([P], [P])))))

check_lj_proof(proof)                 # → True
```

Double-negation *elimination* and excluded middle have no LJ derivation: the classical route needs a two-formula succedent (`⊢ P, ¬P`), which the checker rejects outright.

```python
from unicode_fol_kit import verify_lj_proof

bad = derive(sequent([], [P, Not(P)]), "¬R", axiom(sequent([P], [P])))
r = verify_lj_proof(bad)
r.ok       # → False
r.error    # → "intuitionistic (LJ) sequents have at most one succedent formula; found 2 in '⊢ P, ¬P'"
```

The `∨R` rule is split into `∨R1` / `∨R2`; the `→L` rule replaces the succedent with the antecedent of the implication (the LJ restriction). Otherwise the rule names match LK, and an LJ derivation renders exactly like an LK one.

## First-order: increasing-domain Kripke search (0.9.0)

For a **quantified** formula `int_valid` / `int_countermodel` search *increasing-domain* Kripke models: each world carries a domain, domains grow along the order, and `w ⊩ ∀x φ` quantifies over every later world and every individual existing there, while `w ⊩ ∃x φ` ranges over the individuals present at `w`. This is a **sound but bounded refutation search**, not a decision procedure: a returned counter-model genuinely refutes validity, but a clean search (`int_valid → True`) only means "no counter-model within the bounds" — first-order intuitionistic logic is undecidable.

```python
# ∀x P(x) → ∃x P(x): valid (domains are non-empty)
int_valid(p("∀x P(x) → ∃x P(x)"), max_worlds=2)        # → True

# ¬∀x P(x) → ∃x ¬P(x): constructively invalid
int_valid(p("¬∀x P(x) → ∃x ¬P(x)"), max_worlds=2)      # → False

model, world = int_countermodel(p("¬∀x P(x) → ∃x ¬P(x)"), max_worlds=2)
model.forces(world, p("¬∀x P(x) → ∃x ¬P(x)"))          # → False
```

The counter-model for `¬∀x P(x) → ∃x ¬P(x)` is a two-world model whose domain grows by one fresh individual on the way to its successor world. At the refuting world, `¬∀x P(x)` holds — a later world introduces an individual of which `P` is never forced, so `∀x P(x)` can never be reached — yet `∃x ¬P(x)` fails there, because no *currently existing* individual is permanently outside `P`. (`model.domains` and `model.valuation` carry the per-world domains and the forcing of each ground atom; their repr labels and ordering are an implementation detail, so inspect them rather than asserting an exact string.)

Because `False` is always backed by a real counter-model, the boundedness only ever weakens `True`. The clearest case is the **double-negation shift** `∀x ¬¬P(x) → ¬¬∀x P(x)`, which is intuitionistically *invalid* but valid in every *finite* model (terminal worlds behave classically), so its only counter-models are infinite:

```python
int_valid(p("∀x ¬¬P(x) → ¬¬∀x P(x)"), max_worlds=2)    # → True (finitely valid; documented incompleteness)
```

The finite search correctly reports it as finitely valid — a deliberate, documented limit of the bounded first-order search, not an unsoundness. The propositional fragment is unaffected and remains an exact decision. `int_valid` rejects function terms and second-order/sorted quantifiers in the first-order search (use plain `∀x` / `∃x` over predicates of variables and constants).
