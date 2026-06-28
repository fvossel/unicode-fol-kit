# unicode-fol-kit

A Python toolkit for first-order logic with Unicode operators: **parse, transform, and reason about** formulas. The single parser class `MSFLParser` supports six modes — classical FOL, many-sorted FOL (MSFOL), many-sorted fuzzy logic (MSFL), single-sorted fuzzy logic (FL, Łukasiewicz), modal/temporal/epistemic/deontic logic, and second-order logic — selected by constructor flags.

On top of the AST sits a full reasoning layer: **four proof methods** (a built-in resolution prover, Fitch-style natural deduction with checker *and* searcher, the Gentzen sequent calculus **LK** including second-order rules plus the intuitionistic **LJ**, and analytic tableaux), a **finite model finder** with countermodel extraction, SMT (Z3) and external-prover (Prover9/Vampire) backends, truth tables, and dedicated semantics for every logic. Formulas import/export to TPTP, Prover9, SMT-LIB, LaTeX, and JSON.

## Features

- **Six parser modes** — FOL, many-sorted FOL (MSFOL), many-sorted fuzzy/Łukasiewicz logic (MSFL), single-sorted fuzzy/Łukasiewicz logic (FL), modal/temporal/epistemic/deontic, and second-order — all from one class
- **Unicode surface syntax** — natural symbols (∀ ∃ ∧ ∨ ¬ → ↔ ⊕ ⊗ = ≠ ≤ ≥) with no ASCII fallbacks needed
- **Sorted quantifiers and constants** — `∀x:Human P(x)`, `P(alice:Human)` in MSFOL and MSFL modes
- **Łukasiewicz operators** — weak ∧ / ∨ (min/max), strong ⊗ / ⊕ (t-norm/t-conorm), and Łukasiewicz ¬ → ↔ in MSFL mode
- **Full AST** — all standard FOL constructs plus MSFL-specific nodes, all as Python dataclasses
- **Reductions** — `to_msfol()` lowers Łukasiewicz operators to classical nodes; `to_fol()` further eliminates sorts via relativisation
- **Serialisation** — convert formulas to/from JSON dictionaries; round-trip safe
- **Tree view** — render any formula as a readable ASCII tree
- **Unicode round-trip** — `to_unicode_str()` renders any node back to a parseable Unicode formula; re-parsing in the matching mode yields a structurally equal AST
- **LaTeX export** — `to_latex()` renders any node as LaTeX math-mode markup, with the same precedence-aware parenthesisation as the Unicode renderer
- **LaTeX import** — `parse_latex()` reads a LaTeX-math formula (the inverse of `to_latex()`); `latex_to_unicode()` does the LaTeX→Unicode translation on its own
- **TPTP / Prover9 / SMT-LIB import** — read formulas back from the standard tools: `parse_tptp()` / `parse_tptp_formula()` / `load_tptp()` (FOF & CNF), `parse_prover9()`, and `from_z3()` / `parse_smtlib()` — the inverses of `to_tptp()` / `to_prover9()` / `to_z3()`
- **Normal forms** — `to_nnf()`, `to_pnf()`, `to_cnf()`, `to_dnf()` (equivalence-preserving), `to_tseitin_cnf()` (equisatisfiable, no blow-up), and `skolemize()` (satisfiability-preserving) for classical FOL
- **Horn check** — `is_horn()` reports whether a formula's clausal form consists of Horn clauses
- **Traversal API** — `walk()`, `subformulas()`, `atoms()`, `variables()`, `count()`, `depth()` on every node
- **Graphviz export** — `to_dot()` renders the AST as a Graphviz DOT digraph
- **Z3 export** — translate formulas to Z3 expressions for SMT solving
- **Satisfiability / validity / models** — `is_satisfiable()`, `is_valid()`, and `get_model()` (counterexample extraction) via Z3
- **Prover9 export** — translate formulas to Prover9 syntax for automated theorem proving
- **TPTP export** — translate formulas to TPTP syntax
- **Equivalence checking** — check if two formulas are logically equivalent via Z3
- **Entailment checking** — check if a conclusion follows from premises via Prover9 (`check_logical_entailment`) or Vampire (`check_logical_entailment_vampire`), each taking the prover's executable path as an argument
- **Built-in resolution prover** — `prove()` and `is_valid_resolution()` decide entailment/validity in-process (sound first-order resolution, no external solver needed)
- **Natural-deduction proof checker** — `check_proof()` / `verify_proof()` check Fitch-style proofs with nested subproofs and discharge rules (classical FOL/MSFOL, plus K3/LP and the modal family via `logic=`); `render_fitch()` lays them out with scope bars and a justification column
- **Sequent-calculus proof checker** — `check_sequent_proof()` checks Gentzen **LK** derivations `Γ ⊢ Δ`, including the **second-order** rules (`∀²`/`∃²` with comprehension and predicate eigenvariables) that reach the `second_order=True` fragment; `render_sequent_proof()` prints the derivation tree
- **Fitch proof search** — `find_fitch_proof()` / `fitch_prove()` / `is_valid_fitch()` automatically *find* a Fitch natural-deduction proof (iterative-deepening backtracking, classical FOL); the result is re-validated by `check_proof`, so it is sound by construction
- **Analytic tableaux** — `is_valid_tableau()` / `prove_tableau()` / `tableau_closed()` and `tableau_model()` (an open branch is a countermodel); a fourth proof method, decidable propositionally
- **Finite model finder** — `find_model()` / `find_countermodel()` / `is_satisfiable_finite()` / `is_valid_finite()` search finite `Structure`s up to size N (Mace4-style: a valid entailment has no countermodel, an invalid one usually a small one)
- **Truth tables** — `truth_table()` (and `is_tautology()` / `is_contradiction()` / `is_satisfiable_tt()`) over classical, Kleene **K3**, and Priest **LP** values, renderable to Markdown
- **Intuitionistic logic** — `int_valid()` / `int_countermodel()` decide intuitionistic propositional validity by Kripke-model search; the **LJ sequent calculus** checker `check_lj_proof()` / `verify_lj_proof()` verifies intuitionistic derivations; LEM, DNE, and Peirce fail with explicit countermodels (`IntKripkeModel.forces()`)
- **Verbalization** — `to_english()` paraphrases a formula as an English sentence
- **Canonical form & exact match** — `canonicalize()` normalises bound-variable renaming, commutativity/associativity, operand duplication, and double negation; `exact_match()` gives a fair NL→FOL comparison stricter than logical equivalence but more forgiving than raw equality
- **Formula validation** — `validate()` / `is_wellformed()` / `validate_text()` report free variables, inconsistent predicate/function arity, leftover lambda nodes, and parseability of raw model output
- **Modal, temporal, epistemic & deontic logic** — `MSFLParser(modal=True)` parses `□`/`◇` (alethic), `K_a`/`B_a` (epistemic/doxastic), `Ⓖ`/`Ⓕ`/`Ⓝ`/`Ⓤ` (temporal), `Ⓞ`/`Ⓟ` (obligation/permission); Kripke-model semantics via `satisfies_modal()`; `standard_translation()` to classical FOL so Z3/resolution can decide modal validity. The agent of `K_a`/`B_a` is a **first-class term**, so a bound `K_x` quantifies over agents — `∀x (Student(x) → K_x φ)` works
- **Quantified modal logic** — `KripkeModel` with per-world domains + actualist `satisfies_modal()`; a Benzmüller-style **shallow embedding** with `qml_is_valid()` / `qml_equivalent()` (first-order → Z3, per domain regime) and `to_thf_modal()` (higher-order → Leo-III/Satallax); the Barcan formula and its converse come out valid per the constant/increasing/decreasing domain regime
- **Higher-order / Isabelle / THF exporters** (`unicode_fol_kit.hol`) — Benzmüller-style shallow embeddings of *every* non-fuzzy logic into HOL: a real loadable **Isabelle** theory + **THF** for the full modal family (agent-indexed epistemic/doxastic, deontic, temporal), plus FOL/MSFOL, K3/LP, second-order, and intuitionistic (Gödel–McKinsey–Tarski → S4). Emits sound problem files for an external prover (it does not run one; the quantified logics are undecidable)
- **Many-valued logic** — `kleene_value()` evaluates a formula over {0, ½, 1} (strong Kleene tables); three-valued `is_valid`/`is_satisfiable`/`entails` with selectable designated values for **Kleene K3** and **Priest LP** (paraconsistent)
- **Second-order logic** — `MSFLParser(second_order=True)` parses `∀P`/`∃P` over predicate variables (arity inferred; monadic & n-ary); `satisfies_so()` gives finite-model semantics by enumerating relations over the domain
- **Lambda abstraction** — `λx. φ` syntax in every parser mode; parameters can be variables (`λx.`), named constants (`λfoo.`), or predicate symbols (`λP.`); body extends rightward through all connectives
- **Higher-order predicate application** — `(func)(arg)` explicit application; `λP. P(x)` writes the body naturally and is automatically scope-resolved to `Application(LambdaVar("P"), Variable("x"))`
- **Lambda-calculus operations** — free-variable computation, capture-avoiding substitution, beta-reduction (normal-order, step-limited), eta-reduction, combined beta-eta normalisation to fixpoint, and lexical scope resolution
- **Lambda elimination** — `eliminate_lambdas()` beta-eta-normalises and checks the result is lambda-free (ready for export / normal forms); `reduce_trace()` returns the step-by-step reduction sequence
- **Tarskian semantics** — define a `Structure` (a world with a domain of individuals and interpretations of constants, functions, predicates, and sorts) and compute a formula's truth value with `satisfies()` (FOL and MSFOL)
- **Fuzzy evaluation** — `fuzzy_evaluate()` computes the Łukasiewicz truth degree in [0, 1] of an FL/MSFL formula under a valuation (∀ = inf, ∃ = sup)
- **Fuzzy satisfiability / validity** — `fuzzy_is_satisfiable()`, `fuzzy_is_valid()`, `fuzzy_get_model()` decide Łukasiewicz formulas via Z3 real arithmetic
- **Arithmetic-aware solving** — `is_satisfiable_arith()`, `is_valid_arith()`, `get_model_arith()` interpret `+ - * / < > ≤ ≥` over Z3 reals/integers (unlike the default uninterpreted-sort `to_z3`)
- **Unification** — `unify()` computes the most general unifier of two terms/atoms (Robinson, with occurs-check); `apply_subst()` applies a substitution
- **Command-line interface** — `python -m unicode_fol_kit "∀x P(x)" --to latex` parses and renders in any export format

## Choosing a tool

The kit has grown four proof methods and a model finder across several logics. These two tables map a question (and a logic) to the entry point that answers it; each is documented in detail in its own section below.

### Which tool for which question

| Your question | Use | Returns | Sound / complete / decidable |
|---|---|---|---|
| Is this valid / does Γ entail φ? (general FOL, no external solver) | `prove`, `is_valid_resolution` | bool | sound; refutation-complete; **semidecidable** |
| Same, with an SMT solver | `is_valid`, `is_satisfiable`, `get_model` (Z3) | bool / model | sound & complete on Z3's decidable fragment |
| Same, via an external FO prover | `check_logical_entailment` (Prover9), `check_logical_entailment_vampire` | bool | sound; complete for FOL; needs the binary |
| Propositional tautology? (decidably) | `is_valid_tableau`, `prove_tableau`, `tableau_closed` | bool | sound & complete; decidable propositionally |
| Check a Fitch proof I wrote | `check_proof`, `verify_proof` | bool / `ProofResult` | sound; FOL/MSFOL by rule table, K3/LP + modal propositionally |
| Find a Fitch proof | `find_fitch_proof`, `fitch_prove`, `is_valid_fitch` | `Proof` / bool | sound; complete propositionally, depth-bounded FO |
| Check a sequent (LK) derivation | `check_sequent_proof`, `verify_sequent_proof` | bool / `SequentResult` | sound; reaches the second-order fragment |
| Check an intuitionistic (LJ) derivation | `check_lj_proof`, `verify_lj_proof` | bool | sound for intuitionistic consequence |
| Find a model / countermodel | `find_model`, `find_countermodel`, `is_satisfiable_finite`, `is_valid_finite` | `Structure` / None / bool | finite search up to size N |
| Truth table (classical / K3 / LP) | `truth_table`, `is_tautology`, `is_contradiction`, `is_satisfiable_tt` | `TruthTable` / bool | decidable; propositional only |
| Intuitionistic propositional validity | `int_valid`, `int_countermodel` | bool / `IntKripkeModel` | decidable; propositional |
| Evaluate truth in a structure | `satisfies` (FOL/MSFOL), `satisfies_so`/`holds` (SO), `satisfies_modal` (modal) | bool | direct Tarskian / Kripke / finite SO semantics |
| Fuzzy (Łukasiewicz) degree or decision | `fuzzy_evaluate`; `fuzzy_is_valid`, `fuzzy_is_satisfiable`, `fuzzy_get_model` | degree / bool | real-arithmetic decision via Z3 |
| Read a formula back as English | `to_english` | str | readability aid, not a parse inverse |

### Logics supported

| Logic | Enable | Operators added | Semantics | What can decide / reason about it |
|---|---|---|---|---|
| Classical FOL | `MSFLParser()` | ∀ ∃ ∧ ∨ ¬ → ↔ ⊕ = ≠ | `satisfies()` | resolution, Z3, Prover9/Vampire, tableaux (prop.), Fitch, LK, finite model finder |
| Many-sorted FOL (MSFOL) | `many_sorted=True` | sorted `∀x:S`, `c:S` | `satisfies()` | resolution / Z3 (via `to_fol()`), Fitch, finite model finder |
| Fuzzy Łukasiewicz (FL) | `fuzzy=True` | weak ∧ ∨, strong ⊗ ⊕, Łuk ¬ → ↔ | `fuzzy_evaluate()` | `fuzzy_is_valid` / `fuzzy_is_satisfiable` (Z3 reals) |
| Many-sorted fuzzy (MSFL) | `many_sorted=True, fuzzy=True` | sorts + Łukasiewicz | `fuzzy_evaluate()` | `fuzzy_*` (Z3 reals); `to_msfol()` lowers to classical |
| Modal / temporal / epistemic / deontic | `modal=True` | □ ◇, K_a B_a, Ⓖ Ⓕ Ⓝ Ⓤ, Ⓞ Ⓟ | `satisfies_modal()` | `standard_translation()` → Z3/resolution; Fitch (K/T/S4/S5, prop.) |
| Many-valued K3 / LP | `MSFLParser()` + `logic=` | classical syntax over {0, ½, 1} | `kleene_value()`; `semantics.is_valid`/`is_satisfiable`/`entails` | `truth_table`, three-valued `is_valid`; Fitch under `logic="K3"`/`"LP"` |
| Second-order | `second_order=True` | ∀P ∃P over predicate vars | `satisfies_so()` / `holds()` | `satisfies_so` on finite models; LK (`∀²`/`∃²`). Rejects `to_z3`/`to_prover9`/`to_tptp` |
| Intuitionistic | `MSFLParser()` + intuitionistic tools | classical syntax | `IntKripkeModel.forces()` | `int_valid` / `int_countermodel` (decidable, prop.); LJ (`check_lj_proof`) |

Every non-fuzzy logic above also has a **higher-order exporter** in `unicode_fol_kit.hol` — a Benzmüller-style shallow embedding emitted as an Isabelle/HOL theory or a TPTP THF problem for an external prover (Leo-III / Satallax / Sledgehammer); see [Higher-order proving](#higher-order-proving-isabelle--thf-exporters-the-hol-subpackage).

## Installation

### Via pip

```bash
pip install unicode-fol-kit
```

### Via git clone

```bash
git clone https://github.com/fvossel/unicode-fol-kit.git
cd unicode-fol-kit
pip install .
```

## Parser modes

`MSFLParser` selects its mode from constructor flags. The four core modes form the `many_sorted` × `fuzzy` matrix; two further modes — modal and second-order — are each enabled by their own flag and are mutually exclusive with the others in v1:

```python
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
| `True` | `False` | **MSFOL** | sorted `∀x:Sort` | sorted `alice:Sort` | classical ∧ ∨ ¬ → ↔ (no ⊕) |
| `True` | `True` | **MSFL** | sorted `∀x:Sort` | sorted `alice:Sort` | weak ∧ ∨, strong ⊗ ⊕, Łuk ¬ → ↔ |
| `False` | `True` | **FL** | unsorted `∀x` | unsorted | weak ∧ ∨, strong ⊗ ⊕, Łuk ¬ → ↔ |

The two extension modes are classical unsorted FOL plus their own operators (each enabled by a single flag, not combinable with `many_sorted`/`fuzzy` in v1):

- **modal** (`modal=True`) — adds `□ ◇` (alethic), `K_a B_a` (epistemic/doxastic), `Ⓖ Ⓕ Ⓝ Ⓤ` (temporal), and `Ⓞ Ⓟ` (deontic).
- **second-order** (`second_order=True`) — adds `∀P / ∃P` over predicate variables (arity inferred from use).

## Usage

### FOL mode (default)

```python
from unicode_fol_kit import MSFLParser

parser = MSFLParser()
formula = parser.parse("∀x (Human(x) → Mortal(x))")
```

### MSFOL mode

Quantifiers and ground constants must carry a sort annotation. The colon can be written with or without a space before it:

```python
parser = MSFLParser(many_sorted=True)

# Sorted quantifier
q = parser.parse("∀x:Human (Mortal(x) ∧ ¬Immortal(x))")
# SortedQuantifier(type='∀', variable=Variable('x'), sort='Human', formula=…)

# Sorted constant — both spacing forms are accepted
parser.parse("P(alice:Human)")
parser.parse("P(alice :Human)")
```

### MSFL mode

Uses Łukasiewicz logic: `∧`/`∨` become weak (min/max), `⊗`/`⊕` become strong (t-norm/t-conorm), and `¬`/`→`/`↔` map to their Łukasiewicz counterparts:

```python
parser = MSFLParser(many_sorted=True, fuzzy=True)

parser.parse("P(x) ∧ Q(x)")    # WeakConjunction (min)
parser.parse("P(x) ⊗ Q(x)")    # StrongConjunction (t-norm: max{0, x+y−1})
parser.parse("P(x) ⊕ Q(x)")    # StrongDisjunction (t-conorm: min{1, x+y})
parser.parse("¬P(x)")           # LukNegation (1−x)
parser.parse("P(x) → Q(x)")    # LukImplication (min{1, 1−x+y})
parser.parse("∀x:Human P(x)")  # SortedQuantifier
```

### FL mode

Łukasiewicz operators with **unsorted** quantifiers and plain constants — same connectives as MSFL, same quantifier/constant syntax as FOL:

```python
parser = MSFLParser(many_sorted=False, fuzzy=True)

parser.parse("P(x) ∧ Q(x)")          # WeakConjunction (min)
parser.parse("P(x) ⊗ Q(x)")          # StrongConjunction (t-norm: max{0, x+y−1})
parser.parse("P(x) ⊕ Q(x)")          # StrongDisjunction (t-conorm: min{1, x+y})
parser.parse("¬P(x)")                 # LukNegation (1−x)
parser.parse("P(x) → Q(x)")          # LukImplication (min{1, 1−x+y})
parser.parse("∀x P(x)")              # unsorted Quantifier (no sort annotation)
parser.parse("P(alice)")             # plain Constant (no sort annotation)

# Lambda works in FL mode too
parser.parse("λx. P(x) ⊗ Q(x)")
# Lambda(LambdaVar("x"), StrongConjunction(Atom("P",[LambdaVar("x")]), Atom("Q",[LambdaVar("x")])))
```

### ASCII tree view

```python
formula = MSFLParser().parse("∀x (Human(x) → Mortal(x))")
print(formula.tree_str())
# ∀ x
# └── →
#     ├── Atom: Human
#     │   └── Variable: x
#     └── Atom: Mortal
#         └── Variable: x
```

### Round-trip to Unicode

`to_unicode_str()` is the inverse of parsing: it renders any node back to a Unicode formula string. Re-parsing that string in the same mode reproduces a structurally equal AST. The renderer is precedence-aware and only inserts the parentheses the grammar requires — including the no-mixing rule for same-level connectives and the tight-binding rule for quantifiers.

```python
parser = MSFLParser()

ast = parser.parse("∀x P(x) ∧ Q(x)")
ast.to_unicode_str()              # '∀x P(x) ∧ Q(x)'
parser.parse(ast.to_unicode_str()) == ast   # True

# Precedence-driven parentheses are reconstructed, not the original spelling:
parser.parse("((P(x) ∧ Q(x)))").to_unicode_str()   # 'P(x) ∧ Q(x)'
parser.parse("P(x) ∧ (Q(x) ∨ R(x))").to_unicode_str()  # 'P(x) ∧ (Q(x) ∨ R(x))'
```

Available on every node, so subformulas render too. The output targets parseable
ASTs; alpha-renamed variables introduced by `beta_reduce` (e.g. `x_0`) are not
valid surface tokens and will not round-trip.

### Exporting to other formats

```python
formula.to_prover9()   # '(all x (Human(x) -> Mortal(x)))'
formula.to_tptp()      # '(![X]: (human(X) => mortal(X)))'
formula.to_latex()     # '\\forall x\\, (Human(x) \\rightarrow Mortal(x))'
formula.to_dict()      # JSON-serialisable dict
```

`to_latex()` uses the same precedence-aware parenthesisation as `to_unicode_str()`. Sorts render as `\forall x{:}\mathrm{Human}\,`; strong Łukasiewicz operators as `\otimes` / `\oplus`. Symbol and predicate names are emitted verbatim (no `\mathrm` wrapping).

### Reading LaTeX

`parse_latex()` is the inverse of `to_latex()`: it reads a LaTeX-math formula by first translating LaTeX commands to the Unicode surface syntax (`latex_to_unicode()`), then parsing. It accepts the exact output of `to_latex()` (so `parse_latex(node.to_latex())` round-trips) as well as common hand-written synonyms (`\neg`/`\lnot`, `\wedge`/`\land`, `\vee`/`\lor`, `\to`/`\rightarrow`, `\iff`, `\le`/`\ge`, …).

```python
from unicode_fol_kit import MSFLParser, parse_latex, latex_to_unicode

parse_latex(r"\forall x\, (P(x) \rightarrow Q(x))")        # ∀x (P(x) → Q(x))  → AST
parse_latex(r"\neg (P \wedge Q)")                           # ¬(P ∧ Q)          → AST
parse_latex(r"\Box P \rightarrow \Diamond Q", modal=True)   # □P → ◇Q           → AST (modal mode)

latex_to_unicode(r"\forall x (P(x) \to Q(x))")              # '∀ x (P(x) → Q(x))'  (spacing preserved; parser ignores it)

# Round-trip: render to LaTeX and read it back
ast = MSFLParser(many_sorted=True).parse("∀x:Human P(x)")
parse_latex(ast.to_latex(), many_sorted=True) == ast        # True
```

`parse_latex` takes the same mode flags as `MSFLParser` (`many_sorted`, `fuzzy`, `modal`, `second_order`); the LaTeX must translate to syntax valid for that mode. Hand-written `c_`-constants need an escaped underscore (`c\_zero` or `c_{zero}`), since a bare `_` is LaTeX subscript.

### Reading TPTP, Prover9, and SMT-LIB

The exporters `to_tptp()` / `to_prover9()` / `to_z3()` have inverses, so formulas written for the standard automated-reasoning tools can be read back into the AST:

```python
from unicode_fol_kit import parse_tptp, parse_tptp_formula, parse_prover9, from_z3, parse_smtlib

# TPTP: a single formula, or a whole problem file (fof/cnf statements)
parse_tptp_formula("![X]: (man(X) => mortal(X))")        # AST for: forall x (Man(x) -> Mortal(x))
problem = parse_tptp("""
fof(ax,  axiom,      ![X]: (man(X) => mortal(X))).
fof(hyp, hypothesis, man(socrates)).
fof(g,   conjecture, mortal(socrates)).
""")
roles = [f.role for f in problem]                        # ['axiom', 'hypothesis', 'conjecture']

# Prover9 / LADR
parse_prover9("(all X (man(X) -> mortal(X)))")           # AST for: forall x (man(x) -> mortal(x))

# Z3: a z3 expression (from_z3), or SMT-LIB2 text (via Z3's own parser)
parse_smtlib("(declare-fun x () Int) (assert (< x (+ x 1)))")   # [x < x + 1]
```

- **TPTP** — `parse_tptp_formula(s)` reads one bare FOF/CNF formula; `parse_tptp(text)` reads a whole problem into a list of `TptpFormula(name, role, formula)` records; `load_tptp(path)` reads a `.p`/`.tptp` file. `%` and `/* */` comments are ignored. Round-trips `to_tptp()`. TPTP lowercases predicates, so a predicate is capitalised on import (`loves` → `Loves`) to match the toolkit's uppercase-predicate convention; `$true`/`$false` import as opaque atoms; the typed `tff`/`thf` dialects and `include` directives are out of scope.
- **Prover9** — `parse_prover9(s)` reads a Prover9/LADR formula (a trailing `.` is accepted). It follows `set(prolog_style_variables)` (uppercase/underscore-initial names are variables), matching `to_prover9()`'s output, and is case-preserving. `to_prover9()` desugars exclusive-or, so an `Xor` round-trips to `(a | b) & -(a & b)`.
- **Z3** — `from_z3(expr)` turns a `z3.ExprRef` back into the AST; `parse_smtlib(text)` / `load_smtlib(path)` parse SMT-LIB2 (via Z3's own parser) and convert every assertion. The conversion is **meaning-preserving, not structure-preserving** — Z3 maps variables/constants/numbers onto one uninterpreted sort, so a *free* variable comes back as a `Constant` (only bound variables survive as `Variable`); `A == B` reads as `Iff` on Booleans and `=` on individuals.

### Traversal and inspection

Every node exposes a small traversal API:

```python
f = MSFLParser().parse("∀x (Human(x) → Mortal(x))")

list(f.walk())        # pre-order: every node and descendant
f.subformulas()       # every sub-node that is a formula (terms excluded)
f.atoms()             # [Atom("Human", …), Atom("Mortal", …)]
f.variables()         # {Variable("x")}  — set of logical variables (free + bound)
f.count()             # total node count
f.count(Atom)         # nodes of a given type
f.depth()             # tree height (a leaf has depth 1)
```

### Graphviz export

```python
print(f.to_dot())
# digraph AST {
#   node [shape=box];
#   n0 [label="∀ x"];
#   n1 [label="→"];
#   ...
# }
```

`to_dot()` mirrors the `tree_str()` view (the quantifier's bound variable is folded into its node label). Pipe the output to `dot -Tpng` to render an image.

### Serialisation

```python
from unicode_fol_kit import Node

d = formula.to_dict()
formula2 = Node.from_dict(d)  # round-trip
```

### Lambda-calculus

Every parser mode supports lambda abstraction and application. `parse()` automatically applies scope resolution, so the returned AST is always fully resolved.

```python
from unicode_fol_kit import (
    MSFLParser,
    LambdaVar, Lambda, Application,
    free_variables, substitute,
    beta_reduce, eta_reduce, beta_eta_normalize,
    resolve_lambda_scope,
    ReductionLimitError,
)

parser = MSFLParser()

# Parse — scope resolution is applied automatically
term = parser.parse("λP. λx. P(x)")
# Lambda(LambdaVar("P"), Lambda(LambdaVar("x"), Application(LambdaVar("P"), LambdaVar("x"))))

# Application
app = parser.parse("(λP. P(x))(Q)")
# Application(Lambda(LambdaVar("P"), Application(LambdaVar("P"), Variable("x"))),
#             Atom("Q", []))
```

#### Free variables

```python
term = parser.parse("λP. P(x)")
free_variables(term)
# {Variable("x")}  — x is free; P is lambda-bound and does not appear
```

The result is a mixed set that may contain both `Variable` (logical) and `LambdaVar` (lambda-bound) objects.

#### Beta-reduction

`beta_reduce` reduces to beta-normal form using a normal-order (leftmost-outermost) strategy with full capture-avoiding substitution. It raises `ReductionLimitError` after 10 000 steps if the term does not normalise.

```python
# (λP. λx. P(x))(Q) → λx. Application(Atom("Q",[]), LambdaVar("x"))
result = beta_reduce(parser.parse("(λP. λx. P(x))(Q)"))

# Full pipeline: parse → resolve → reduce
reduced = beta_reduce(parser.parse("(λP. P(x))(λy. Q(y))"))
# Atom("Q", [Variable("x")])
```

#### Eta-reduction

`eta_reduce` performs a single bottom-up pass contracting all eta-redexes: `λp. f(p) → f` when `p` is not free in `f`. Quantifiers are recursed into but never treated as eta-redexes.

```python
from unicode_fol_kit import LambdaVar, Lambda, Application, Atom, Variable

f = Atom("P", [Variable("x")])                  # some formula
term = Lambda(LambdaVar("p"), Application(f, LambdaVar("p")))  # λp. f(p)
eta_reduce(term)   # → f  (the Atom node, not the Lambda)
```

#### Beta-eta normalisation

`beta_eta_normalize` alternates `beta_reduce` and `eta_reduce` to fixpoint (up to 100 rounds). The alternation loop is a genuine necessity: eta-reduction can expose fresh beta-redexes, requiring another beta pass.

```python
normal = beta_eta_normalize(parser.parse("(λP. P(x))(Q)"))
```

`ReductionLimitError` is raised if the inner beta-reduction limit or the outer round limit is exceeded.

#### Scope resolution (standalone)

`resolve_lambda_scope` is also available as a standalone function for hand-built ASTs:

```python
from unicode_fol_kit import resolve_lambda_scope, Lambda, LambdaVar, Atom, Variable

raw = Lambda(LambdaVar("x"), Atom("P", [Variable("x")]))
resolved = resolve_lambda_scope(raw)
# Lambda(LambdaVar("x"), Atom("P", [LambdaVar("x")]))
```

### Reducing MSFL formulas to classical FOL

`to_fol()` performs a two-phase reduction: it first lowers Łukasiewicz operators to classical ones (`to_msfol()`), then eliminates sort annotations via relativisation (`_relativize()`):

```python
from unicode_fol_kit import MSFLParser, to_fol

parser = MSFLParser(many_sorted=True, fuzzy=True)
formula = parser.parse("∀x:Human (P(x) ∧ ¬Q(x))")

classical = to_fol(formula)
# Quantifier(∀, x, Implies(Atom(Human, [x]), And(Atom(P,[x]), Not(Atom(Q,[x])))))

# Optionally, conjoin sort-membership facts for constants at the top level:
classical_with_facts = to_fol(formula, include_sort_facts=True)
```

> **Note — this is a classical (Boolean) projection, not a fuzzy-preserving translation.** `to_msfol()` maps *both* the strong (`⊗`/`⊕`) and the weak (`∧`/`∨`) Łukasiewicz connectives to the same classical `And`/`Or`. On crisp truth values {0, 1} the strong and weak operators coincide, so the reduction is sound as the two-valued projection of the formula — but the genuinely many-valued content is discarded. To compute the real-valued Łukasiewicz degree instead, use `fuzzy_evaluate()` or the fuzzy Z3 solver (see below).

### Normal forms

`to_nnf()`, `to_pnf()`, `to_cnf()`, and `skolemize()` operate on classical FOL. They accept FOL, MSFOL, MSFL, and FL inputs — sorts and Łukasiewicz operators are reduced via `to_fol()` first. (Lambda terms must be beta-reduced and lambda-eliminated beforehand.)

```python
from unicode_fol_kit import MSFLParser, to_nnf, to_pnf, to_cnf, skolemize

parser = MSFLParser()

to_nnf(parser.parse("P → Q"))        # eliminates → ↔ ⊕, pushes ¬ down to atoms
to_pnf(parser.parse("∀x P(x) ∧ ∃y Q(y)"))   # quantifier prefix + quantifier-free matrix
to_cnf(parser.parse("P ∨ (Q ∧ R)"))  # matrix as a conjunction of clauses
skolemize(parser.parse("∀x ∃y Loves(x, y)"))
# ∀v0 Loves(v0, sk0(v0)) — the existential becomes a Skolem function of x
```

- `to_nnf` / `to_pnf` / `to_cnf` are **equivalence-preserving**: the result is logically equivalent to the (classical) input.
- `skolemize` is **satisfiability-preserving** (not equivalence-preserving): existentials are replaced by Skolem terms over the universals in scope, and the universal prefix is retained. Bound variables are standardised apart (renamed to fresh `v0, v1, …`); Skolem symbols are named `sk0, sk1, …`.

`to_dnf()` is the dual of `to_cnf()`: a prenex form whose matrix is a **disjunction of conjunctive clauses**, and it is likewise equivalence-preserving.

```python
from unicode_fol_kit import MSFLParser, to_dnf, to_tseitin_cnf

parser = MSFLParser()
to_dnf(parser.parse("P ∧ (Q ∨ R)"))   # (P ∧ Q) ∨ (P ∧ R)
```

`to_tseitin_cnf()` produces an **equisatisfiable** CNF using the Tseitin/definitional encoding: it introduces fresh auxiliary atoms (`ts0, ts1, …`) for compound subformulas, so the result grows linearly instead of risking the exponential blow-up of the distributive `to_cnf`. It is **not** logically equivalent to the input (the auxiliaries are existentially fresh), but the input is satisfiable iff its Tseitin CNF is. It operates on quantifier-free (propositional / ground) formulas and raises `ValueError` on quantified input.

```python
from unicode_fol_kit import MSFLParser, to_tseitin_cnf, is_satisfiable

parser = MSFLParser()
phi = parser.parse("(P ∨ Q) ∧ (¬P ∨ R)")
is_satisfiable(phi) == is_satisfiable(to_tseitin_cnf(phi))   # True (equisatisfiable)
```

### Horn check

`is_horn()` reports whether a formula's clausal form consists of Horn clauses — each clause has at most one positive literal. The formula is skolemised, its universal prefix dropped, and the matrix put into CNF before the clauses are checked.

```python
from unicode_fol_kit import MSFLParser, is_horn

parser = MSFLParser()
is_horn(parser.parse("∀x (Body(x) → Head(x))"))     # True  (definite clause)
is_horn(parser.parse("P → (Q ∧ R)"))                # True  (splits into two Horn clauses)
is_horn(parser.parse("P → (Q ∨ R)"))                # False (clause has two positive literals)
```

### Equivalence checking (Z3)

```python
from unicode_fol_kit import MSFLParser, formulas_are_equivalent

parser = MSFLParser()
f1 = parser.parse("¬(P(x) ∧ Q(x))")
f2 = parser.parse("¬P(x) ∨ ¬Q(x)")

formulas_are_equivalent(f1, f2)  # True
```

### Satisfiability, validity, and counterexamples (Z3)

```python
from unicode_fol_kit import MSFLParser, is_satisfiable, is_valid, get_model, Not

parser = MSFLParser()

is_satisfiable(parser.parse("P ∧ Q"))     # True
is_satisfiable(parser.parse("P ∧ ¬P"))    # False
is_valid(parser.parse("P ∨ ¬P"))          # True

get_model(parser.parse("P ∧ Q"))          # {'P': 'True', 'Q': 'True'}
get_model(parser.parse("P ∧ ¬P"))         # None  (unsatisfiable)

# Counterexample to a claimed equivalence: a model of its negation.
get_model(Not(parser.parse("P ↔ Q")))     # e.g. {'P': 'True', 'Q': 'False'}
```

`get_model` returns a dict mapping each Z3 declaration (constants, uninterpreted predicates/functions) to its interpretation, or `None` when the formula is unsatisfiable or Z3 returns `unknown` within the timeout.

### Entailment checking (Prover9)

```python
from unicode_fol_kit import MSFLParser, check_logical_entailment  # doctest: +SKIP (needs an installed Prover9)

parser = MSFLParser()
premises = [
    parser.parse("∀x (Human(x) → Mortal(x))"),
    parser.parse("Human(socrates)"),
]
conclusion = parser.parse("Mortal(socrates)")

check_logical_entailment(premises, conclusion, prover9_path="/usr/bin/prover9")  # True
```

### Entailment checking (Vampire)

The same check backed by [Vampire](https://vprover.github.io/) instead of Prover9: the premises are emitted as TPTP `axiom`s and the conclusion as a `conjecture`, and the path to the Vampire executable is passed as an argument (Vampire reports `SZS status Theorem` when the entailment holds).

```python
from unicode_fol_kit import MSFLParser, check_logical_entailment_vampire  # doctest: +SKIP (needs an installed Vampire)

parser = MSFLParser()
premises = [
    parser.parse("∀x (Human(x) → Mortal(x))"),
    parser.parse("Human(socrates)"),
]
conclusion = parser.parse("Mortal(socrates)")

check_logical_entailment_vampire(premises, conclusion, vampire_path="/usr/bin/vampire")  # True
```

On Windows you can drive a Linux Vampire installed in **WSL** with `use_wsl=True`: Vampire is launched through `wsl.exe` and the temporary problem file's path is translated to its `/mnt/...` form automatically. Here `vampire_path` is the command/path *inside* WSL (e.g. `"vampire"` if it is on the WSL `PATH`).

```python
# Windows host, Vampire installed in WSL:  # doctest: +SKIP (needs WSL + Vampire)
check_logical_entailment_vampire(premises, conclusion, vampire_path="vampire", use_wsl=True)  # True
```

Note that every premise and the conclusion must be a closed sentence — Vampire rejects unquantified (free) variables, and recall that a single lowercase letter like `x` is a *variable*, so a constant individual needs a multi-character name (`socrates`) or the `c_`-prefix.

### Entailment and validity (built-in resolution prover)

For entailment and validity **without** an external prover, the package ships a self-contained first-order **resolution** prover. It clausifies the input (skolemise → drop ∀ prefix → CNF → clauses), then refutes `premises ∧ ¬conclusion` by binary resolution and factoring, deriving the empty clause iff the entailment holds.

```python
from unicode_fol_kit import MSFLParser, prove, is_valid_resolution

parser = MSFLParser()

premises = [parser.parse("∀x (Human(x) → Mortal(x))"), parser.parse("Human(socrates)")]
prove(premises, parser.parse("Mortal(socrates)"))   # True

prove([parser.parse("Human(socrates)")], parser.parse("Mortal(socrates)"))  # False (no entailment)

is_valid_resolution(parser.parse("P ∨ ¬P"))          # True
is_valid_resolution(parser.parse("∃x ∀y L(x, y) → ∀y ∃x L(x, y)"))  # True
```

- **Sound, deliberately incomplete.** First-order resolution is only semi-decidable, so `prove`/`is_valid_resolution` take a `max_steps` bound (default 10 000). They return `True` **only** when the empty clause is actually derived, and `False` both when the clause set saturates (genuinely no entailment) and when the bound is reached ("not proved within the bound") — they never report a non-theorem as proved.
- **Equality is uninterpreted.** `=` is treated as an ordinary predicate (no built-in reflexivity/congruence). Entailments that rely on the theory of equality (e.g. `a = b, P(a) ⊨ P(b)`) need those axioms supplied as explicit premises, or use the Z3 backend instead.
- `to_clauses(formula)` exposes the clausal form, and `refute(clauses)` runs the saturation directly.

### Natural deduction (Fitch proofs)

The provers above decide *whether* an entailment holds. The package can also **check a Fitch-style natural-deduction proof** — a derivation with nested subproofs (hypothetical reasoning), per-line justifications, and discharge rules. `check_proof` is *sound*: it returns `True` only when every line genuinely follows by the cited rule and the proof's premises really do entail its conclusion. `verify_proof` additionally returns the certified sequent and the first failing line with a reason.

```python
from unicode_fol_kit import (
    MSFLParser, Proof, Subproof, premise, assume, line,
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

check_proof(proof)                 # True
print(render_fitch(proof))
```

`render_fitch` lays the proof out in classic Fitch notation — a line-number gutter, one vertical scope bar per open subproof, a rule under each assumption, and a justification column:

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

The classical rule set covers the connectives (`∧I`/`∧E`, `∨I`/`∨E`, `→I`/`→E`, `↔I`/`↔E`, `¬I`, `⊥I`/`⊥E`, `¬E` double-negation, `RAA`, `Reit`), the first-order quantifiers (`∀I`/`∀E`, `∃I`/`∃E`, with the eigenvariable side-conditions enforced via the kit's capture-avoiding substitution), and equality (`=I`/`=E`, certified against Z3 since `=` is otherwise uninterpreted). A subproof is cited by its line span, e.g. `(3, 5)`; the instantiation/witness term of `∀E`/`∃I` is passed as `extra=[term]`. `⊥` is the reserved logical constant `FALSUM`. `∀I` discharges a *pure eigenvariable box*: head it with `flag(n, e)` (a boxed-variable line, rule `"Flag"`) and set `Subproof(..., flag=e)`, so the box `[flag e; … ; φ(e)]` introduces `∀x φ` only if `e` is fresh in every open assumption.

**Non-classical logics.** Pass `logic=` to check a proof under a different consequence relation. For the three-valued **K3**/**LP** logics each step is certified against the many-valued decision procedure, so the paraconsistency facts come out correctly — in **LP** modus ponens, the disjunctive syllogism, and explosion are *not* valid, and the checker rejects a proof that uses them:

```python
# In LP (paraconsistent) modus ponens is NOT valid — the checker rejects it:
mp = Proof(premises=[premise(1, parse("P")), premise(2, parse("P → Q"))],
           steps=[line(3, parse("Q"), "→E", 2, 1)], logic="LP")
check_proof(mp)                    # False

# The very same proof is fine classically:
check_proof(Proof(premises=mp.premises, steps=mp.steps, logic="fol"))   # True
```

For the **modal family** (`logic="K"`/`"T"`/`"S4"`/`"S5"`) each step is certified by the standard translation to FOL plus the frame axioms, decided by Z3. Knowledge (`Knows`) is factive, but belief (`Believes`) and obligation (`Obligatory`) are not:

```python
from unicode_fol_kit import Atom, Knows, Believes

p = Atom("P", [])

# Knowledge is factive (S5):  K_a P ⊢ P
knows = Proof(premises=[premise(1, Knows("a", p))],
              steps=[line(2, p, "T", 1)], logic="S5")
check_proof(knows)                 # True

# Belief is NOT factive:  B_a P ⊬ P  → rejected
believes = Proof(premises=[premise(1, Believes("a", p))],
                 steps=[line(2, p, "T", 1)], logic="S5")
check_proof(believes)              # False
```

- **Sound by construction.** Citation accessibility is enforced (a line may not reach into a closed sibling subproof), discharge rules are checked against the proof's *open assumptions* (not merely the cited lines), and every classical rule application is cross-checked in the test-suite against Z3 and the resolution prover — randomised proofs are audited line-by-line so an accepted step is never one the oracle reports invalid.
- **Scope.** Classical FOL/MSFOL is checked by the syntactic rule table; K3/LP and the modal family are checked over their propositional fragment. Temporal logic (`Ⓖ`/`Ⓕ`/`Ⓝ`/`Ⓤ`), quantified modal logic, second-order quantification, and the substructural Łukasiewicz connectives are out of scope (no sound finitary Fitch calculus / first-order rendering) and are rejected with a clear message.
- **LaTeX.** `render_latex_fitch(proof)` (also `proof.to_latex_fitch()`) emits the derivation as a self-contained LaTeX `array`; `proof.to_dict()` / `Proof.from_dict(...)` round-trips a whole proof to JSON.

### Finding Fitch proofs (backtracking search)

The checker above *verifies* a proof; `find_fitch_proof` *finds* one. It is a goal-directed, iterative-deepening backtracking searcher over the classical propositional and first-order rules — introduction rules, ∨/∃ elimination by case split, backward chaining, and reductio (RAA), which makes it complete for the propositional fragment.

```python
from unicode_fol_kit import find_fitch_proof, fitch_prove, is_valid_fitch
from unicode_fol_kit.fol.nodes import Atom, Or, Not, Implies

P, Q = Atom("P", ()), Atom("Q", ())

fitch_prove([], Or(P, Not(P)))                          # True — a proof of P ∨ ¬P was found
is_valid_fitch(Implies(Implies(Implies(P, Q), P), P))   # True — Peirce's law

proof = find_fitch_proof([P, Implies(P, Q)], Q)         # returns a Proof (or None)
print(proof.to_fitch())
```

```text
1 │ P       Premise
2 │ P → Q   Premise
  ├──────
3 │ Q       →E 2, 1
```

- **Sound by construction.** Whatever the search assembles is re-validated by `check_proof` before it is returned, so a bug in the search can only make it *fail to find* a proof — never return an invalid one. Like the resolution prover it is sound and, under its depth bound, *incomplete*: `find_fitch_proof` returning `None` means "no proof found within `max_depth`", never "not a theorem".
- `fitch_prove(premises, conclusion)` returns a bool; `is_valid_fitch(formula)` proves from no premises; `find_fitch_proof` returns the actual `Proof` (render it, serialise it, or re-check it). Classical FOL only (the non-classical checkers above are verification-only).

### Sequent calculus (Gentzen LK, incl. second-order)

A second proof system: a **two-sided Gentzen sequent calculus**. A sequent `Γ ⊢ Δ` (multisets of formulas, read as `⋀Γ → ⋁Δ`) is derived by a tree of inference rules, and `check_sequent_proof` verifies the tree. This is the classical system **LK** with the first-order quantifier rules *and* the **second-order** rules (`∀²`/`∃²` over predicate variables), so it reaches the second-order fragment (the `MSFLParser(second_order=True)` syntax) that natural deduction / resolution / Z3 cannot.

```python
from unicode_fol_kit import (
    MSFLParser, sequent, derive, axiom, check_sequent_proof, render_sequent_proof,
)
from unicode_fol_kit.fol.nodes import Atom, Implies, Quantifier, Variable, Constant

x, c = Variable("x"), Constant("c")
def Px(t): return Atom("P", [t])

# ∀x P(x) ⊢ P(c)   via the ∀L rule (instantiating the bound x with the term c)
d = derive(sequent([Quantifier("∀", x, Px(x))], [Px(c)]), "∀L",
           axiom(sequent([Px(c)], [Px(c)])),
           extra=[c])

check_sequent_proof(d)               # True
print(render_sequent_proof(d))
```

`render_sequent_proof` prints the derivation as an indented tree (conclusion first, premises below, each annotated with its rule):

```text
∀x P(x) ⊢ P(c)   [∀L c]
  P(c) ⊢ P(c)   [Ax]
```

The second-order rules `∀²L` / `∃²R` instantiate a bound predicate variable `X` with a **comprehension term** `λx̄.ψ` (a `Comprehension`), replacing each `X(t̄)` by `ψ[x̄ := t̄]`; `∀²R` / `∃²L` use a fresh **predicate eigenvariable**:

```python
from unicode_fol_kit import Comprehension
from unicode_fol_kit.fol.nodes import SecondOrderQuantifier

z = Variable("z")
Xc = Atom("X", [c])                  # the bound predicate variable X applied to c
Pc = Px(c)

# ∀X X(c) ⊢ P(c)   via ∀²L, instantiating X with the comprehension  λz. P(z)
so = derive(sequent([SecondOrderQuantifier("∀", "X", 1, Xc)], [Pc]), "∀²L",
            axiom(sequent([Pc], [Pc])),
            extra=[Comprehension((z,), Px(z))])

check_sequent_proof(so)              # True
```

- **Rule set.** `Ax`, the structural rules `WL`/`WR` (weakening), `CL`/`CR` (contraction), `Cut`; the connective rules `¬L`/`¬R`, `∧L`/`∧R`, `∨L`/`∨R`, `→L`/`→R`, `↔L`/`↔R`, `⊕L`/`⊕R` (exclusive-or, via `A⊕B ≡ ¬(A↔B)`); the quantifier rules `∀L`/`∀R`, `∃L`/`∃R` (with the eigenvariable condition on `∀R`/`∃L`); and the second-order rules `∀²L`/`∀²R`, `∃²L`/`∃²R`. Contexts are shared additively and compared as multisets; the instantiation term / eigenvariable / comprehension goes in `extra=[…]`.
- **Checker, not prover.** Full second-order validity is not recursively enumerable (Gödel), so no calculus can be a *complete* prover — `check_sequent_proof` verifies a *given* derivation (the diagnostic form `verify_sequent_proof` returns a `SequentResult` naming the first offending rule). It is sound by the LK metatheory, cross-checked in the test-suite against Z3 (for the first-order-expressible sequents) and `satisfies_so` over small finite models (for the genuinely second-order ones, where a randomised audit confirms every accepted derivation is valid node-by-node).
- `derivation.to_dict()` / `Derivation.from_dict(...)` round-trips a whole derivation (including comprehension terms) to JSON.

### Sequent calculus — intuitionistic LJ

Gentzen's **LJ** is the same calculus restricted to **at most one formula in the succedent** — the single change that makes intuitionistic logic. `check_lj_proof` / `verify_lj_proof` reuse the LK `Sequent` / `Derivation` data model, so an LJ derivation is built and rendered exactly like an LK one.

```python
from unicode_fol_kit import sequent, derive, axiom, check_lj_proof
from unicode_fol_kit.fol.nodes import Atom, Not, Implies

P = Atom("P", ())
# ⊢ P → ¬¬P  — double-negation *introduction* is intuitionistically valid:
lj_proof = derive(sequent([], [Implies(P, Not(Not(P)))]), "→R",
              derive(sequent([P], [Not(Not(P))]), "¬R",
                  derive(sequent([P, Not(P)], []), "¬L",
                      axiom(sequent([P], [P])))))
check_lj_proof(lj_proof)              # True
```

The classical route to `P ∨ ¬P` needs a two-formula succedent (`⊢ P, ¬P`), which LJ rejects — so excluded middle, double-negation *elimination*, and Peirce's law have no LJ derivation, matching the Kripke countermodels from `int_countermodel` (see *Intuitionistic logic*). The `∨R` rule is split into `∨R1` / `∨R2`; otherwise the rule names match LK.

### Tarskian semantics (FOL / MSFOL)

Instead of calling an external solver, you can build a concrete **world** (a first-order `Structure`) and compute the truth value of a formula directly, following Tarski's recursive definition of satisfaction. A structure is a non-empty domain of individuals together with interpretations of the constants, functions, and predicates (and, for MSFOL, the named sorts).

```python
from unicode_fol_kit import MSFLParser, Structure, satisfies

parser = MSFLParser()

# A world with two individuals where everyone loves someone else.
world = Structure(
    domain={"alice", "bob"},
    predicates={("Loves", 2): {("alice", "bob"), ("bob", "alice")}},
)

satisfies(parser.parse("∀x ∃y Loves(x, y)"), world)              # True
satisfies(parser.parse("∃x Loves(x, x)"), world)                 # False
satisfies(parser.parse("∀x ∀y (Loves(x, y) → Loves(y, x))"), world)  # True
```

- `predicates` maps `(name, arity)` to the relation's extension (a set of argument tuples); a missing predicate is the empty relation (false). A nullary predicate maps `(name, 0)` to a bool.
- `functions` maps `(name, arity)` to a Python callable or a `{arg_tuple: value}` dict; `constants` maps a name to an individual.
- **Equality** `=` (and `≠`) is built in as identity on the domain — you do not interpret it. The order comparisons `< > ≤ ≥` are ordinary relations whose extension you supply.
- `satisfies(formula, structure, assignment=None)` takes an optional assignment of free variables; `models(formula, structure)` is the closed-formula convenience alias.

For **MSFOL**, declare each sort's universe and quantify over it:

```python
msfol = MSFLParser(many_sorted=True)

zoo = Structure(
    domain={"alice", "rex"},
    sorts={"Human": {"alice"}, "Dog": {"rex"}},
    predicates={("Barks", 1): {("rex",)}},
)

satisfies(msfol.parse("∀x:Dog Barks(x)"), zoo)     # True
satisfies(msfol.parse("∀x:Human Barks(x)"), zoo)   # False
```

Tarski semantics is two-valued: Łukasiewicz operators and lambda nodes are rejected (use the fuzzy evaluator below, and `eliminate_lambdas()` respectively).

### Fuzzy evaluation (Łukasiewicz)

`fuzzy_evaluate()` computes the **truth degree in [0, 1]** of an FL/MSFL formula under a *valuation* — a mapping from each ground atom (keyed by its Unicode rendering, e.g. `"P(alice)"`) to a degree. The Łukasiewicz operator semantics are applied exactly (weak ∧/∨ = min/max, strong ⊗/⊕ = t-norm/t-conorm, ¬ = 1−x, → and ↔ as usual); quantifiers are infimum (∀) and supremum (∃) over the domain.

```python
from unicode_fol_kit import MSFLParser, fuzzy_evaluate

fl = MSFLParser(fuzzy=True)

fuzzy_evaluate(fl.parse("P ⊗ ¬P"), {"P": 0.6})            # 0.0   (strong: max(0, 0.6+0.4−1))
fuzzy_evaluate(fl.parse("P ⊕ ¬P"), {"P": 0.6})            # 1.0   (strong: min(1, 0.6+0.4))
fuzzy_evaluate(fl.parse("P ↔ Q"), {"P": 0.6, "Q": 0.7})   # 0.9   (1 − |0.6 − 0.7|)

# Quantifiers need a domain of constant-name strings; atoms are grounded to P(a), P(b), …
fuzzy_evaluate(fl.parse("∀x P(x)"), {"P(a)": 0.3, "P(b)": 0.8}, domain={"a", "b"})  # 0.3 (min)
fuzzy_evaluate(fl.parse("∃x P(x)"), {"P(a)": 0.3, "P(b)": 0.8}, domain={"a", "b"})  # 0.8 (max)
```

### Fuzzy satisfiability and validity (Z3)

For Łukasiewicz formulas you can also ask the solver, rather than fixing a valuation, whether *some* (or *every*) assignment reaches a given degree. The atoms become Z3 reals in [0, 1] and the operators their real-arithmetic definitions.

```python
from unicode_fol_kit import MSFLParser, fuzzy_is_valid, fuzzy_is_satisfiable, fuzzy_get_model

fl = MSFLParser(fuzzy=True)

fuzzy_is_valid(fl.parse("P ⊕ ¬P"))                     # True  (degree is 1 for every P)
fuzzy_is_satisfiable(fl.parse("P ⊗ ¬P"), threshold=0.5)  # False (max degree is 0)
fuzzy_is_satisfiable(fl.parse("P ∧ ¬P"), threshold=0.5)  # True  (weak: max degree is 0.5)
fuzzy_get_model(fl.parse("P → Q"), threshold=1.0)        # {'P': ..., 'Q': ..., 'degree': ...}
```

These cover quantifier-free (propositional) Łukasiewicz formulas; quantified input raises `NotImplementedError`.

### Arithmetic-aware solving (Z3)

The default `is_satisfiable()` / `to_z3()` treat everything as one uninterpreted sort, so arithmetic terms are opaque. The `*_arith` variants instead interpret `+ - * /` and the comparisons over a numeric sort (`"real"` by default, or `"int"`), so the solver can actually reason about numbers.

```python
from unicode_fol_kit import MSFLParser, is_satisfiable_arith, is_valid_arith, get_model_arith

parser = MSFLParser()

is_satisfiable_arith(parser.parse("x + 1 = 2 ∧ x > 0"))   # True   (x = 1)
is_satisfiable_arith(parser.parse("x > 0 ∧ x < 0"))       # False
is_valid_arith(parser.parse("∀x (x * 2 = x + x)"))        # True
get_model_arith(parser.parse("x + 1 = 2 ∧ x > 0"))        # {'x': '1'}
is_satisfiable_arith(parser.parse("x + x = 1"), sort="int")  # False (no integer solution)
```

### Lambda elimination and reduction trace

`eliminate_lambdas()` beta-eta-normalises a term and verifies the result is lambda-free, so it can be fed to the exporters or normal-form functions (which otherwise reject lambda nodes). `reduce_trace()` returns the intermediate steps, and `beta_reduce_step()` performs a single leftmost-outermost step.

```python
from unicode_fol_kit import MSFLParser, eliminate_lambdas, reduce_trace, has_lambdas

parser = MSFLParser()

term = parser.parse("(λP. P(x))(Q)")
has_lambdas(term)                 # True
reduced = eliminate_lambdas(term) # Atom("Q", [Variable("x")])
has_lambdas(reduced)              # False
reduced.to_tptp()                 # now exportable: 'q(X)'

steps = reduce_trace(parser.parse("(λP. λx. P(x))(Q)"))  # [original, …, normal form]
```

A term that is stuck or only partially applied (no further redex but lambdas remain) raises `ValueError` from `eliminate_lambdas`.

### Unification

`unify()` computes the most general unifier (Robinson's algorithm with occurs-check) of two terms or two atoms, returned as a substitution dict mapping variable names to terms; `apply_subst()` applies it. Note that single lowercase letters parse as variables, so build genuine constants with `Constant`.

```python
from unicode_fol_kit import unify, apply_subst, Variable, Constant, Function

t1 = Function("f", [Variable("x"), Constant("a")])
t2 = Function("f", [Constant("b"), Variable("y")])

mgu = unify(t1, t2)        # {'x': Constant('b'), 'y': Constant('a')}
apply_subst(t1, mgu) == apply_subst(t2, mgu)   # True

unify(Variable("x"), Function("f", [Variable("x")]))   # None  (occurs-check fails)
```

### Command-line interface

The package is runnable as a module for quick parsing and conversion:

```bash
python -m unicode_fol_kit "∀x (P(x) → Q(x))" --to tptp
# (![X]: (p(X) => q(X)))

python -m unicode_fol_kit "P(x) ⊗ Q(x)" --mode msfl --to latex
# P(x) \otimes Q(x)
```

`--mode` is one of `fol` (default), `msfol`, `msfl`, `fl`; `--to` is one of `tree` (default), `unicode`, `latex`, `tptp`, `prover9`, `json`, `dot`. Parse errors print a `SYNTAX_ERROR` message to stderr and exit with status 1.

### Evaluation utilities (NL→FOL)

When evaluating a model that translates natural language to FOL, **exact string match is too strict** (it penalises a correct paraphrase that merely renames a bound variable or reorders a conjunction) and **logical equivalence is undecidable** in general. `canonicalize()` sits in between: it puts a formula into a normal form that quotients out the *syntactic* differences that should not count as errors — bound-variable renaming (α), commutativity and associativity of the commutative connectives, duplicate operands, and double negation — while staying **logically equivalent** to the input.

```python
from unicode_fol_kit import MSFLParser, canonicalize, exact_match

parser = MSFLParser()
pred = parser.parse("∀x (P(x) ∧ Q(x))")
ref  = parser.parse("∀y (Q(y) ∧ P(y))")     # α-renamed + conjuncts swapped

exact_match(pred, ref)                    # True  (canonical match)
exact_match(pred, ref, canonical=False)   # False (raw structural match)
canonicalize(parser.parse("¬¬P")) == canonicalize(parser.parse("P"))   # True
```

`canonicalize` is a normal form for exactly {α, commutativity, associativity, operand-dedup, double-negation}. It does **not** do distributivity, CNF, or full equivalence — e.g. `P → Q` and `¬P ∨ Q` are equivalent but do not canonicalize equal (use `formulas_are_equivalent` / `prove` for that).

`validate()` flags the defects common in generated formulas:

```python
from unicode_fol_kit import MSFLParser, validate, is_wellformed, validate_text, And, Atom, Variable

parser = MSFLParser()

is_wellformed(parser.parse("∀x (Human(x) → Mortal(x))"))   # True

r = validate(parser.parse("P(x)"))
r.is_closed                # False  — x is free (a sentence should be closed)
r.free_variable_names      # ('x',)

# Same predicate used with two different arities — a common LLM error:
bad = And(Atom("P", [Variable("x")]), Atom("P", [Variable("x"), Variable("y")]))
validate(bad).arity_consistent     # False
validate(bad).arity_conflicts      # {('pred', 'P'): (1, 2)}

# Syntactic validity of raw model output (catches parse errors):
validate_text("∀x (P(x)").parseable   # False  (unbalanced parenthesis)
```

The `ValidationReport` also exposes `has_lambdas`, and `predicates` / `functions` / `constants` / `sorts_used` inventories. Built-in comparison (`= ≠ < > ≤ ≥`) and arithmetic (`+ - * /`) symbols are excluded from the arity checks and inventories.

### Predicate-aligned string match

`canonicalize` / `exact_match` forgive *structural* differences (α-renaming, commutativity/associativity, …) but treat two **different predicate names** as a genuine mismatch. The complementary, lexical notion is `match_predicates`: it greedily renames each predicate/function symbol in a predicted formula to the closest symbol in the reference — by **normalised Levenshtein distance**, accepting a match at or below a threshold (`max_norm_distance`, default `0.6`) — so a structurally-correct answer that merely chose different predicate names is not penalised. `formulas_are_identical` is the plain whitespace- and case-insensitive string equality; `formulas_are_matched_identical` realigns predicates and then compares.

```python
from unicode_fol_kit import (
    match_predicates,
    formulas_are_identical,
    formulas_are_matched_identical,
)

pred = "∀x (Wins(x) → Happy(x))"
ref  = "∀x (Win(x) → Happy(x))"        # same shape; "Wins" vs "Win"

formulas_are_identical(pred, ref)            # False  (raw strings differ)
match_predicates(pred, ref)                  # '∀x (Win(x) → Happy(x))'
formulas_are_matched_identical(pred, ref)    # True   (Wins → Win is a close match)

# A symbol with no sufficiently close reference counterpart is left untouched:
match_predicates("Red(x)", "Tall(x)")        # 'Red(x)'  (normalised distance 1.0 > 0.6)
```

Unlike the `canonicalize`/`exact_match` pair, this matcher is purely **lexical** (string-level), so it also applies to raw model output that does not yet parse, and the two notions are typically reported as separate metrics (e.g. `EXACT_MATCH` vs `PREDICATE_MATCHED_EXACT_MATCH`). The Levenshtein distance is computed in pure Python, so no extra dependency is required.

## Modal, temporal, and epistemic logic

Natural language is full of constructs classical FOL can't express directly — necessity/possibility, knowledge and belief, and time. `MSFLParser(modal=True)` adds a modal mode (classical unsorted FOL extended with modal operators) and the toolkit ships Kripke-model semantics plus a standard translation back to FOL.

| Family | Operators | Surface syntax | Meaning |
|---|---|---|---|
| Alethic | `Box` / `Diamond` | `□φ` / `◇φ` | necessarily / possibly |
| Epistemic / doxastic | `Knows` / `Believes` | `K_a φ` / `B_a φ` | agent *a* knows / believes φ |
| Temporal | `Always` / `Eventually` / `Next` / `Until` | `Ⓖφ` / `Ⓕφ` / `Ⓝφ` / `φ Ⓤ ψ` | henceforth / eventually / next / until |
| Deontic | `Obligatory` / `Permitted` | `Ⓞφ` / `Ⓟφ` | it is obligatory / permitted that φ |

```python
from unicode_fol_kit import MSFLParser

parser = MSFLParser(modal=True)

parser.parse("□(P → Q) → (□P → □Q)")    # the K axiom (Box / Implies …)
parser.parse("K_alice (P ∧ Q)")          # Knows("alice", And(…))
parser.parse("Ⓖ(Rain → Ⓕ Sun)")          # Always(Implies(Rain, Eventually(Sun)))
parser.parse("P Ⓤ Q")                     # Until(P, Q)
```

The prefix operators (`□ ◇ Ⓖ Ⓕ Ⓝ K_a B_a`) bind as tightly as `¬`; `Ⓤ` is binary, binding looser than `∧/∨` but tighter than `→`, right-associative. Agent names in `K_a`/`B_a` are lowercase identifiers, so they never collide with uppercase predicate symbols. Modal mode is classical and unsorted; combining `modal=True` with `many_sorted`/`fuzzy` raises `ValueError`.

### Kripke semantics

A `KripkeModel` is a set of worlds, a dict of **named accessibility relations**, and a per-world propositional valuation (the set of ground atoms true at that world). `satisfies_modal(formula, model, world)` evaluates a formula at a world.

```python
from unicode_fol_kit import MSFLParser, KripkeModel, satisfies_modal

parser = MSFLParser(modal=True)

# Reflexive frame → knowledge/necessity is factive (□P → P holds):
refl = KripkeModel(worlds={"w"}, relations={"alethic": {("w", "w")}}, valuation={"w": {"P"}})
satisfies_modal(parser.parse("□P → P"), refl, "w")     # True

# Non-reflexive frame → □P → P can fail:
frame = KripkeModel(worlds={0, 1}, relations={"alethic": {(0, 1)}}, valuation={1: {"P"}})
satisfies_modal(parser.parse("□P → P"), frame, 0)      # False  (P holds at the successor, not here)
```

Relation-name convention: `"alethic"` for `□`/`◇`, `"K:<agent>"` / `"B:<agent>"` for `Knows`/`Believes`, and `"temporal"` for `Next`/`Always`/`Eventually`/`Until`. `Always`/`Eventually` range over the reflexive-transitive closure of the temporal relation; `Until(φ, ψ)` is the finite-reachability reading (a temporal path to a ψ-world with φ holding until then). This semantics is **propositional/ground** (v1): quantifiers inside modalities are out of scope.

### Standard translation to FOL

`standard_translation()` rewrites a modal formula into classical FOL with explicit world variables and accessibility predicates, so the existing solvers (`is_valid`, `prove`, Z3) can decide modal validity:

```python
from unicode_fol_kit import MSFLParser, standard_translation, is_valid

parser = MSFLParser(modal=True)

standard_translation(parser.parse("◇P"))     # ∃w0 (R(w, w0) ∧ P(w0))

# The K axiom is valid on every frame, so its translation is FOL-valid:
is_valid(standard_translation(parser.parse("□(P → Q) → (□P → □Q)")))   # True

# The T axiom □P → P is valid only on reflexive frames, so the bare translation is not valid:
is_valid(standard_translation(parser.parse("□P → P")))                  # False
#   (add the reflexivity axiom ∀w R(w, w) as a premise to recover it)
```

`Box`/`Diamond` translate over an accessibility predicate `R`, `Knows`/`Believes` over `Rk_a`/`Rb_a`, `Always`/`Eventually`/`Next` over temporal predicates `T`/`N`. `Until` and quantifiers are rejected (transitive closure and first-order modal domains are not first-order definable in this scheme). Modal nodes reject `to_z3`/`to_prover9`/`to_tptp` directly — translate first.

### Deontic logic

`Ⓞ` (obligation) and `Ⓟ` (permission) are box/diamond over a `"deontic"` accessibility relation (Standard Deontic Logic, the modal logic **KD**). On a **serial** frame the D axiom `Ⓞφ → Ⓟφ` holds ("what is obligatory is permitted"), while factivity `Ⓞφ → φ` does **not** ("ought" does not imply "is").

```python
from unicode_fol_kit import MSFLParser, KripkeModel, satisfies_modal, standard_translation

parser = MSFLParser(modal=True)
serial = KripkeModel(worlds={0, 1}, relations={"deontic": {(0, 1), (1, 1)}}, valuation={1: {"P"}})

satisfies_modal(parser.parse("Ⓞ P → Ⓟ P"), serial, 0)    # True   (D axiom, serial frame)
satisfies_modal(parser.parse("Ⓞ P → P"), serial, 0)      # False  (P is obligatory but false here)
standard_translation(parser.parse("Ⓞ P"))                # ∀w0 (D(w, w0) → P(w0))
```

There is no dedicated "forbidden" operator; express it with the operators that exist — "forbidden that φ" is `¬Ⓟφ` (equivalently `Ⓞ¬φ`).

### Quantified modal logic (shallow embedding)

Combining the modalities with `∀x` / `∃x` is **quantified modal logic** (QML), where validity turns on how the individual domain varies between worlds. The kit handles it both semantically and via two *shallow embeddings* (the Benzmüller-style approach: a modal proposition is a function world → bool, the modalities are quantifiers over accessible worlds).

```python
from unicode_fol_kit import qml_is_valid, qml_equivalent, to_thf_modal, BARCAN, CONVERSE_BARCAN
from unicode_fol_kit.semantics.kripke import KripkeModel, satisfies_modal

# Semantic side: per-world domains D_w; quantifiers are ACTUALIST (∀x ranges over D_w).
# Barcan  ◇∃x A → ∃x ◇A  is valid under constant domains, fails when domains GROW.
rel = {"alethic": {(0, 1)}}
constant   = KripkeModel(worlds={0,1}, relations=rel, valuation={1:{"A(b)"}}, domain={"a","b"})
increasing = KripkeModel(worlds={0,1}, relations=rel, valuation={1:{"A(b)"}}, domains={0:{"a"}, 1:{"a","b"}})
satisfies_modal(BARCAN, constant, 0)      # True
satisfies_modal(BARCAN, increasing, 0)    # False — Barcan fails when an object appears only in a successor

# (A) First-order shallow embedding → Z3: validity per domain regime (sound, bounded).
qml_is_valid(BARCAN, mode="constant")            # True
qml_is_valid(BARCAN, mode="increasing")          # False
qml_is_valid(CONVERSE_BARCAN, mode="increasing") # True   (converse Barcan ↔ cumulative domains)

# (B) Higher-order shallow embedding → TPTP THF (for Leo-III / Satallax):
thf = to_thf_modal(BARCAN, mode="constant", frame="S5")
```

- **Semantics.** Build a `KripkeModel` with per-world object domains — `domains={w: [...]}` (varying) or `domain=[...]` (constant). `satisfies_modal` then interprets `∀x` / `∃x` *actualistically*: at a world `w` they range over `D_w`. This is the ground truth against which the embeddings are cross-checked, and it makes the **Barcan formula** (`BARCAN`) and its **converse** (`CONVERSE_BARCAN`) come out valid or invalid exactly as the domains vary.
- **(A) First-order embedding.** `qml_translate` translates a modal formula (with the existence predicate `E!` relativising the actualist quantifiers) into classical FOL; `qml_is_valid(φ, mode, frame)` and `qml_equivalent(f1, f2, …)` decide validity / equivalence with **Z3**. The `mode` is the domain regime — `"constant"`, `"increasing"`/`"cumulative"`, `"decreasing"`, `"varying"` — and `frame` ∈ {K, T, S4, S5, KD, KD45}. The correspondence (verified against the Kripke enumerator): BF ⇔ decreasing domains, CBF ⇔ increasing, constant ⇔ both. Sound but **bounded-incomplete** — first-order modal logic is undecidable, so a `False` may mean "not proven valid"; use `satisfies_modal` for a definite countermodel.
- **(B) Higher-order embedding.** `to_thf_modal(φ, mode, frame)` emits a complete Benzmüller-style **TPTP THF** problem (lifted `mbox`/`mdia`/`mforall`/`mexists`/`mvalid`, frame and domain axioms) for an external higher-order prover (Leo-III, Satallax) — emitted like the other exporters, not run in-process. This covers the alethic □/◇ QML fragment; for the **full modal family**, a real loadable **Isabelle** theory, and HOL exports of the other logics, see [Higher-order proving](#higher-order-proving-isabelle--thf-exporters-the-hol-subpackage) below.

## Higher-order proving: Isabelle / THF exporters (the `hol` subpackage)

Beyond the first-order embedding above, `unicode_fol_kit.hol` emits **Benzmüller-style shallow embeddings into higher-order logic** for *all* the non-fuzzy logics — as complete, self-contained problem files for an external prover (Leo-III / Satallax on TPTP **THF**, or Isabelle/HOL theories for Sledgehammer). As everywhere in the kit it **emits**; it does not run a prover — and it cannot decide everything: first-order modal logic, FOL, and SOL are undecidable / not even semi-decidable, so a successful emission means *"here is a sound problem a prover may discharge"*, never *"decided"*. (The propositional fragments — K3/LP, modal K/T/S4/S5 — are decidable, but these exporters target the general case.)

```python
from unicode_fol_kit import MSFLParser
from unicode_fol_kit.hol import (
    to_isabelle_modal, to_thf_modal_full,    # full modal family
    to_thf_fol, to_isabelle_fol,             # FOL / MSFOL
    to_thf_k3lp, to_thf_so,                   # K3 / LP, second-order
    to_thf_intuitionistic,                    # intuitionistic (GMT → S4)
)

# Quantified, agent-indexed epistemic logic — "every student knows P of themselves":
f = MSFLParser(modal=True).parse("∀x (Student(x) → K_x P(x))")
print(to_isabelle_modal(f))    # a real, loadable Isabelle/HOL theory ending in a `lemma`
print(to_thf_modal_full(f))    # a complete TPTP THF problem; rk is AGENT-indexed
```

- **Full modal family.** `to_isabelle_modal(φ, frame=…)` emits a **real, loadable** Isabelle theory (`theory … imports Main begin … end`, every lifted operator as an abbreviation, frame + domain axioms, the formula lifted into the embedding, and a genuine `lemma` with a Sledgehammer hook) — replacing the old alethic-only skeleton. `to_thf_modal_full(φ, mode, frame, systems=…)` is the THF counterpart. Both cover alethic □/◇, **epistemic** `K_a` / **doxastic** `B_a`, **deontic** `O`/`P`, and **temporal** `G`/`F`/`X`. Epistemic/doxastic accessibility is **agent-indexed**: the agent of `Knows` / `Believes` is a first-class *term*, so a bound `K_x` (as in the example) genuinely quantifies over agents, exactly as the per-agent Kripke relations do. (`Until` is out of the shallow fragment; temporal `G`/`F`/`X` are linked by an inclusion axiom but remain an approximation of the closure semantics — see the module docstring.)
- **Classical FOL / MSFOL.** `to_thf_fol` / `to_isabelle_fol` (and the `…_msfol` variants, which relativise each sort to a guard predicate) emit the formula as a HOL conjecture / lemma.
- **Three-valued K3 / LP.** `to_thf_k3lp(φ, system="K3")` / `to_isabelle_k3lp` (also `…_entailment`) encode the truth-value type, the strong-Kleene connective functions, and the designated set (`{1}` for K3, `{½, 1}` for LP), so emitted theorem-hood matches K3 / LP validity. Cross-checked against `kleene_value`.
- **Second-order.** `to_thf_so` / `to_isabelle_so` map `∀P` / `∃P` to native higher-order predicate quantifiers (standard semantics). Cross-checked against `satisfies_so` on finite structures.
- **Intuitionistic.** `to_thf_intuitionistic` / `to_isabelle_intuitionistic` apply the **Gödel–McKinsey–Tarski** box-translation into S4 then the alethic SSE, so emitted theorem-hood matches intuitionistic validity — `p ∨ ¬p`, `¬¬p → p`, and Peirce's law come out as **non-theorems**. Cross-checked against `int_valid` (`gmt_validity_matches_int_valid` runs the differential).

Each embedding is faithful to its in-toolkit ground-truth oracle (`satisfies_modal`, `kleene_value`, `satisfies_so`, `int_valid`), verified by an adversarial differential audit. Equality `=` / `≠` is an **uninterpreted, world-relativized** predicate throughout (not primitive HOL identity), consistently across every exporter.

## Many-valued logic (Kleene K3 / Priest LP)

`kleene_value()` evaluates a classical formula over the three truth values **0 (false)**, **½ (undefined / both)**, and **1 (true)** using the strong Kleene tables (`¬x = 1−x`, `∧ = min`, `∨ = max`, `→ = max(1−x, y)`). Validity, satisfiability, and entailment are decided by enumeration under a chosen set of **designated** values — Kleene's **K3** designates `{1}`, Priest's paraconsistent **LP** designates `{½, 1}`:

```python
from unicode_fol_kit import MSFLParser, kleene_value
from unicode_fol_kit.semantics import is_valid, is_satisfiable, entails   # three-valued versions

parser = MSFLParser()

kleene_value(parser.parse("P ∧ ¬P"), {"P": 0.5})    # 0.5   (min(0.5, 0.5))

# Excluded middle: not valid in K3, but valid in LP (½ is designated there):
is_valid(parser.parse("P ∨ ¬P"), "K3")    # False
is_valid(parser.parse("P ∨ ¬P"), "LP")    # True

# Explosion: holds in K3 but FAILS in LP (LP is paraconsistent):
entails([parser.parse("P"), parser.parse("¬P")], parser.parse("Q"), "K3")   # True
entails([parser.parse("P"), parser.parse("¬P")], parser.parse("Q"), "LP")   # False
```

`kleene_value` takes a valuation mapping each ground atom's Unicode key (e.g. `"P"`, `"R(a, b)"`) to a value in `{0, 0.5, 1}`; quantifiers range over a finite `domain` (∀ = min, ∃ = max). `is_valid` / `is_satisfiable` / `entails` (importable from `unicode_fol_kit.semantics`) default to `logic="K3"`; pass `"LP"` for the paraconsistent reading. These three-valued functions are intentionally namespaced under `semantics` so they don't shadow the Z3-based `is_valid` / `is_satisfiable` at the package top level.

## Second-order logic

`MSFLParser(second_order=True)` adds quantification over **predicate variables**: `∀P φ` and `∃P φ`, where `P` is an uppercase predicate symbol bound by the quantifier. The predicate variable's arity is **inferred** from how it is applied in the body (`∀P P(x)` is monadic; `∀R R(x, y)` is binary; a never-applied `P` is propositional). Object quantifiers keep using lowercase variables, so `∀x` is first-order and `∀P` is second-order.

`satisfies_so()` (with `holds()` for sentences) gives **finite-model semantics**: a second-order quantifier ranges over *every* relation of its arity on the structure's finite domain (`2^(nᵏ)` relations for domain size `n` and arity `k` — enumeration is brute-force, so keep domains small).

```python
from unicode_fol_kit import MSFLParser, Structure, satisfies_so, holds

parser = MSFLParser(second_order=True)
universe = Structure(domain={0, 1})            # a bare 2-element domain

holds(parser.parse("∃P ∀x P(x)"), universe)    # True   (take P = the whole domain)
holds(parser.parse("∀P ∃x P(x)"), universe)    # False  (take P = ∅)

# Leibniz's identity of indiscernibles is expressible (and holds in full
# second-order finite models):
holds(parser.parse("∀x ∀y (∀P (P(x) ↔ P(y)) → x = y)"), universe)   # True
```

This is second-order **predicate** quantification with full (standard) semantics over finite models. Quantification over functions, third-order and up, and a complete higher-order type system are out of scope; the lambda layer already provides higher-order *terms* (`λP. P(x)`), which you beta-reduce/eliminate before evaluation. Second-order formulas reject `to_z3`/`to_prover9`/`to_tptp` (second-order validity is not first-order / not SMT-expressible) — use `satisfies_so` on finite models instead.

## Truth tables, model finding, tableaux, and intuitionistic logic

Five further analysis tools round out the kit. They all reuse the existing AST and evaluators.

```python
from unicode_fol_kit import (
    MSFLParser, truth_table, is_tautology, find_countermodel, is_valid_finite,
    is_valid_tableau, tableau_model, int_valid, int_countermodel, to_english,
)
p = MSFLParser().parse

# Truth tables (classical / K3 / LP)
print(truth_table(p("P → Q")).render())
is_tautology(p("P ∨ ¬P"))                 # True (classical) …
is_tautology(p("P ∨ ¬P"), "K3")           # … False in K3 (no three-valued tautologies)

# Finite model finder — a countermodel witnesses a non-entailment
find_countermodel([p("P(tom)")], p("∀x P(x)"), max_size=3)    # a Structure (or None)
is_valid_finite(p("∀x P(x) → P(tom)"))                        # True (no finite countermodel)

# Analytic tableaux — and an open branch is a model
is_valid_tableau(p("((P → Q) → P) → P"))      # True (Peirce, classically)
tableau_model([p("P → Q"), p("P")])            # {'P': True, 'Q': True}

# Intuitionistic logic — LEM and Peirce fail, with a Kripke countermodel
int_valid(p("P ∨ ¬P"))                         # False  (int_countermodel returns the model)
int_valid(p("¬¬(P ∨ ¬P)"))                     # True

# Verbalize a formula in English
to_english(p("∀x (Human(x) → Mortal(x))"))     # 'for every x, if x is human, then x is mortal'
```

- **Truth tables** — `truth_table(formula, logic)` (`"classical"` / `"K3"` / `"LP"`) returns a `TruthTable` (`.render()` to Markdown, `.is_tautology` / `.is_contradiction` / `.is_satisfiable`); the convenience predicates `is_tautology` / `is_contradiction` / `is_satisfiable_tt` wrap it. Each distinct atom is a propositional variable; quantified formulas are rejected.
- **Finite model finder** — `find_model(theory, max_size)` brute-force searches finite `Structure`s (domain `1..N`) satisfying a theory; `find_countermodel(premises, conclusion)` finds one refuting an entailment; `is_satisfiable_finite` / `is_valid_finite` are the booleans. The Mace4-style partner of the provers: a valid entailment has no countermodel, an invalid one usually has a small one. Bounded (a domain whose interpretation space is too large is skipped).
- **Analytic tableaux** — `is_valid_tableau`, `prove_tableau`, `tableau_closed`, and `tableau_model` (an open branch is a satisfying assignment / countermodel). A fourth proof method beside resolution, Fitch, and the sequent calculus; decidable and complete propositionally, bounded first-order.
- **Intuitionistic logic** — `int_valid` and `int_countermodel` decide intuitionistic *propositional* validity by Kripke-model search (the logic has the finite-model property); `IntKripkeModel.forces(world, φ)` evaluates a model directly. The **LJ sequent calculus** checker `check_lj_proof` / `verify_lj_proof` verifies intuitionistic derivations — Gentzen **LJ** is the LK calculus restricted to *at most one succedent formula*, which is exactly what blocks the classical theorems. Excluded middle, double-negation elimination, and Peirce's law fail, each with an explicit Kripke countermodel; every intuitionistic validity is also classically valid.
- **Verbalization** — `to_english(formula)` renders a formula as an English sentence (a readability aid, not a parse inverse).

## Syntax reference

This section describes the full surface syntax accepted by the parser. Because the four modes share the same term and atom layer, most of the syntax is identical across modes; differences are called out explicitly.

### Tokens

The lexer distinguishes the following token kinds. Because the patterns are mutually exclusive, a given identifier is unambiguously a variable, a constant, a function/predicate name, a number, or a sort annotation.

| Token | Pattern | Examples | Meaning |
|---|---|---|---|
| Variable | one lowercase letter, optional trailing digits | `x`, `y`, `x1`, `z42` | a (possibly bound) logical variable |
| Name | lowercase, at least two letters, may contain digits and uppercase after the first letter | `socrates`, `distance`, `centerOf`, `foo1` | a bare constant or a function symbol |
| Constant (`c_`) | `c_` followed by letters/digits | `c_a`, `c_zero`, `c_42` | an explicitly marked constant |
| Predicate | one uppercase letter, then letters/digits | `P`, `Human`, `OnSurfaceOf` | a predicate symbol |
| Number | digits, optional decimal part | `0`, `42`, `3.14` | a numeric literal |
| Sort annotation | `:` followed by an uppercase letter and letters/digits | `:Human`, `:Sort1` | a sort tag *(MSFOL and MSFL modes only)* |

The `c_` form exists so that **single-letter constants** can be written without colliding with variables. A bare `a` is always a variable; if you need the constant *a*, write `c_a`.

A function or predicate is recognised by being immediately followed by a parenthesised argument list, e.g. `distance(x, y)` or `Human(socrates)`. The same token class (Name) serves both as a bare constant and, when applied, as a function symbol.

The sort annotation token always begins with `:`, which makes it lexically disjoint from all other tokens. **Whitespace before the colon is optional**: `∀x:Human P(x)` and `∀x :Human P(x)` are both valid and produce identical parse trees.

### Terms

A term is one of:

- a variable (`x`, `x1`)
- a constant (`socrates`, `c_a`) or number (`42`, `3.14`)
- in MSFOL / MSFL modes: a **sort-annotated constant** (`alice:Human`, `c_a:Sort1`)
- a function application (`f(t1, …, tn)`, e.g. `centerOf(x)`)
- an arithmetic combination of terms using `+`, `-`, `*`, `/`
- a parenthesised term (`(t)`)

Arithmetic follows the usual precedence: `*` and `/` bind tighter than `+` and `-`, and both groups are left-associative. For example `x + y * z` parses as `x + (y * z)`.

**Sort rules in MSFOL / MSFL modes:** variables are sorted implicitly by the quantifier that binds them; ground constants must carry an explicit sort annotation. An unsorted constant (e.g. bare `alice`) is a syntax error in sorted modes.

### Atomic formulas

An atomic formula is either:

- a predicate applied to terms: `P`, `Human(socrates)`, `OnSurfaceOf(y, x)`
  (a predicate may be nullary, i.e. used without arguments)
- an infix comparison between two terms: `=`, `≠`, `<`, `>`, `≤`, `≥`,
  e.g. `x1 + 1 = y1` or `distance(y, c) > distance(z, c)`

### Compound formulas

Atomic formulas are combined with connectives and quantifiers. The available connectives and their interpretations depend on the mode:

#### FOL mode

| Syntax | Operator | Interpretation |
|---|---|---|
| `¬φ` | negation | classical |
| `φ ∧ ψ` | conjunction | classical |
| `φ ∨ ψ` | disjunction | classical |
| `φ ⊕ ψ` | exclusive or | classical |
| `φ → ψ` | implication | classical |
| `φ ↔ ψ` | biconditional | classical |
| `∀x φ` | universal | unsorted |
| `∃x φ` | existential | unsorted |

#### MSFOL mode

Same connectives as FOL **except `⊕` (exclusive or) is not available**. Quantifiers require a sort annotation:

| Syntax | Operator |
|---|---|
| `¬φ`, `φ ∧ ψ`, `φ ∨ ψ`, `φ → ψ`, `φ ↔ ψ` | classical (as FOL) |
| `∀x:Sort φ`, `∃x:Sort φ` | sorted quantifiers |

#### MSFL mode

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

#### FL mode

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

### Operator precedence

The precedence levels are the same across all four modes (MSFL/FL use the same syntactic structure with Łukasiewicz semantics):

| Precedence | Operators | Associativity |
|---|---|---|
| 1 (highest) | `¬`, quantifiers `∀` / `∃` | prefix |
| 2 | `∧` `∨` `⊕` (FOL) / `∧` `∨` (MSFOL) / `∧` `∨` `⊗` `⊕` (MSFL / FL) | left |
| 3 | `→` | right |
| 4 (lowest) | `↔` | right |

Worked examples (parenthesised to show how the parser groups them):

- `¬P(x) ∧ Q(x)` → `(¬P(x)) ∧ Q(x)` — negation binds tighter than conjunction
- `P(x) ∧ Q(x) → R(x)` → `(P(x) ∧ Q(x)) → R(x)` — conjunction binds tighter than implication
- `P(x) → Q(x) ↔ R(x)` → `(P(x) → Q(x)) ↔ R(x)` — implication binds tighter than biconditional
- `P(x) → Q(x) → R(x)` → `P(x) → (Q(x) → R(x))` — implication is right-associative
- `P(x) ∧ Q(x) ∧ R(x)` → `(P(x) ∧ Q(x)) ∧ R(x)` — conjunction is left-associative

### Mixing same-level operators

The same-level connectives (level 2 above) **cannot be mixed without explicit parentheses**. This is deliberate: it avoids the silent, easy-to-misread grouping that a default precedence would impose.

**FOL mode** — `∧`, `∨`, `⊕` cannot be mixed:

```text
P(x) ∧ Q(x) ∨ R(x)      # rejected
(P(x) ∧ Q(x)) ∨ R(x)    # accepted
```

**MSFOL mode** — `∧` and `∨` cannot be mixed:

```text
P(x) ∧ Q(x) ∨ R(x)      # rejected
(P(x) ∧ Q(x)) ∨ R(x)    # accepted
```

**MSFL / FL mode** — `∧`, `∨`, `⊗`, `⊕` cannot be mixed:

```text
P(x) ∧ Q(x) ⊗ R(x)        # rejected
(P(x) ∧ Q(x)) ⊗ R(x)      # accepted
```

A chain of the *same* operator is always fine: `P ∧ Q ∧ R`, `P ⊗ Q ⊗ R`, etc.

### Quantifier scope

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

### Supported symbols

| Category | FOL | MSFOL | MSFL | FL |
|---|---|---|---|---|
| Quantifiers | `∀` `∃` (unsorted) | `∀` `∃` (sorted `:Sort`) | `∀` `∃` (sorted `:Sort`) | `∀` `∃` (unsorted) |
| Connectives | `∧` `∨` `⊕` `¬` `→` `↔` | `∧` `∨` `¬` `→` `↔` | `∧` `∨` `⊗` `⊕` `¬` `→` `↔` | `∧` `∨` `⊗` `⊕` `¬` `→` `↔` |
| Lambda | `λ` | `λ` | `λ` | `λ` |
| Sort annotations | — | `:Sort` | `:Sort` | — |
| Equality / comparison | `=` `≠` `<` `>` `≤` `≥` | same | same | same |
| Arithmetic | `+` `-` `*` `/` | same | same | same |
| Grouping | `(` `)` `[` `]` | same | same | same |
| Argument separator | `,` | same | same | same |

Whitespace is insignificant and may be used freely between tokens — including before sort annotation colons.

### Lambda abstraction and application (all modes)

A lambda abstraction is written `λ` followed by a parameter name, a literal `.`, and a body formula. Every parser mode supports identical lambda surface notation.

#### Parameter types

| Parameter form | Example | Typical use |
|---|---|---|
| Single lowercase letter | `λx. P(x)` | value variable |
| Multi-letter lowercase name | `λfoo. P(foo(x))` | named-constant parameter |
| Uppercase predicate symbol | `λP. P(x)` | predicate / higher-order parameter |

All three token classes become a `LambdaVar` in the AST. Scope resolution (applied automatically by `parse()`) then rewrites body occurrences of the lambda-bound name:

- **Variable occurrence** — `λx. P(x)`: the `x` in `P(x)` becomes `LambdaVar("x")`.
- **Predicate-application occurrence** — `λP. P(x)`: the `P(x)` in the body becomes `Application(LambdaVar("P"), Variable("x"))`. Multi-argument atoms curry left: `P(x, y)` → `Application(Application(LambdaVar("P"), x), y)`.
- **Named-function occurrence** — `λfoo. P(foo(x))`: the `foo(x)` in `P`'s argument list (a term-level function call) becomes `Application(LambdaVar("foo"), Variable("x"))`.

The scope obeys the **innermost-binder rule**: a quantifier removes the quantified name from the lambda-bound set. Inside `λx. ∀x P(x)`, the `x` in `P(x)` is logical (stays `Variable`).

#### Body scope

The body extends rightward through all connectives — lambda has lower precedence than every binary operator:

```text
λx. P(x) ∧ Q(x)      # body is the And node P(x) ∧ Q(x)
λx. P(x) → Q(x)      # body is the Implies node P(x) → Q(x)
```

Multi-parameter lambdas are written by nesting: `λP. λx. P(x)`.

#### Application syntax

A lambda application requires both sides to be parenthesised: `(func)(arg)`.

```text
(λx. P(x))(a)         # arg is variable a
(λx. P(x))(alice)     # arg is constant alice
(λP. P(x))(Q)         # arg is the zero-arity atom Q
(λP. P(x))(Q(y))      # arg is the atom Q(y)
```

Higher-order application inside the body — a predicate parameter applied to arguments — is written in the natural `P(x)` notation, not as `(P)(x)`. Scope resolution handles the rewrite automatically.

#### Parse examples

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

### A complete FOL example

```text
∀x ((Object(x) ∧ HasThreeDimensionalShape(x) ∧
     ∀y ∀z ((Point(y) ∧ OnSurfaceOf(y, x) ∧ Point(z) ∧ OnSurfaceOf(z, x))
            → distance(y, centerOf(x)) = distance(z, centerOf(x))))
    → Sphere(x))
```

### A complete MSFOL example

```text
∀x:Person ∀y:Person (Knows(x, y) ∧ Trusted(y)) → Shares(x, y)
```

### A complete MSFL example

```text
∀x:Patient ∀y:Treatment
    (Effective(y) ⊗ Tolerable(x, y))
    → Recommended(x, y)
```

### A complete FL example

```text
∀x ∀y
    (Effective(y) ⊗ Tolerable(x, y))
    → Recommended(x, y)
```

## AST nodes

All nodes are **frozen** Python dataclasses and can be imported from `unicode_fol_kit`. Being frozen, every node is immutable and **hashable**, so nodes can be put in sets, used as dict keys, and deduplicated. `Function` and `Atom` store their `args` as a `tuple` (a list passed to the constructor is accepted and coerced), which is what makes them hashable.

### Shared term and atom nodes (all modes)

| Class | Fields | Notes |
|---|---|---|
| `Variable` | `name: str` | bound or free variable |
| `Constant` | `name: str` | bare constant or c_-prefixed |
| `Number` | `value: int \| float` | numeric literal |
| `Function` | `name: str`, `args: tuple` | function application and arithmetic ops |
| `Atom` | `predicate: str`, `args: tuple` | predicate or infix comparison |

### Classical formula nodes (FOL / MSFOL)

| Class | Fields |
|---|---|
| `Not` | `formula` |
| `And` | `left`, `right` |
| `Or` | `left`, `right` |
| `Xor` | `left`, `right` *(FOL only)* |
| `Implies` | `left`, `right` |
| `Iff` | `left`, `right` |
| `Quantifier` | `type: str`, `variable`, `formula` *(FOL / FL — the unsorted modes)* |

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

Parse errors are reported with human-readable messages rather than raw parser internals. Lexer-level problems (an invalid character, a malformed name or number, or an attempt to mix same-level connectives without parentheses) raise `NamingError`; structural problems (an incomplete formula or a misplaced operator) raise `ParsingError`. Both report the offending position and, where useful, a hint. The hint text is mode-aware:

```python
from unicode_fol_kit import MSFLParser  # doctest: +SKIP (these snippets intentionally raise)

# FOL mode — hint names ∧, ∨, and ⊕
MSFLParser().parse("P(x) ∧ Q(x) ∨ R(x)")
# SYNTAX_ERROR: … Hint: Cannot mix conjunction (∧), disjunction (∨), and exclusive or (⊕) without parentheses

# MSFOL mode — hint names only ∧ and ∨
MSFLParser(many_sorted=True).parse("P(x) ∧ Q(x) ∨ R(x)")
# SYNTAX_ERROR: … Hint: Cannot mix conjunction (∧) and disjunction (∨) without parentheses

# MSFL mode — hint names all four Łukasiewicz connectives
MSFLParser(many_sorted=True, fuzzy=True).parse("P(x) ∧ Q(x) ⊗ R(x)")
# SYNTAX_ERROR: … Hint: Cannot mix weak conjunction (∧), weak disjunction (∨),
#                        strong conjunction (⊗), and strong disjunction (⊕) without parentheses

# FL mode — same hint as MSFL (Łukasiewicz connectives, unsorted)
MSFLParser(many_sorted=False, fuzzy=True).parse("P(x) ∧ Q(x) ⊗ R(x)")
# SYNTAX_ERROR: … Hint: Cannot mix weak conjunction (∧), weak disjunction (∨),
#                        strong conjunction (⊗), and strong disjunction (⊕) without parentheses
```

## Citation

If you use this toolkit in academic work, please cite the accompanying preprint:

```bibtex
@misc{vossel2025advancingnaturallanguageformalization,
      title={Advancing Natural Language Formalization to First Order Logic with Fine-tuned LLMs},
      author={Felix Vossel and Till Mossakowski and Björn Gehrke},
      year={2025},
      eprint={2509.22338},
      archivePrefix={arXiv},
      primaryClass={cs.CL},
      url={https://arxiv.org/abs/2509.22338},
}
```

> Vossel, F., Mossakowski, T., & Gehrke, B. (2025). *Advancing Natural Language
> Formalization to First Order Logic with Fine-tuned LLMs.* arXiv preprint
> arXiv:2509.22338.

## License

MIT
