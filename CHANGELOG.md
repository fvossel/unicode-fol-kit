# Changelog

All notable changes to this project are documented in this file. The format is
loosely based on [Keep a Changelog](https://keepachangelog.com/). Versioning is
semantic, but the project is pre-1.0 (alpha): a **minor** release may contain
breaking changes.

## [Unreleased]

### Added

- **`⊕L` / `⊕R` (exclusive-or) rules in the sequent calculus** (`A⊕B ≡ ¬(A↔B)`),
  closing the one connective that had no inference rule in either checker.

### Internal

- **Adversarial audit of the proof checkers.** A multi-agent audit ran independent
  oracles against every accepted proof/derivation of the Fitch and sequent checkers
  across all logics (~75 hand-built adversarial constructions plus >1M fuzzed cases)
  and found **no soundness hole**. Follow-up hardening from the audit's coverage
  findings: added regression tests pinning the `verify_proof` robustness guards (a
  clean `ProofResult(ok=False)` instead of a crash on a non-`Line` premise or subproof
  assumption) and the mixed quantifier-spelling normalisation (`'forall'` vs `∀`); and
  extended the sequent test corpus so the randomised mutation / Z3 audit now also
  exercises `Cut`, weakening, contraction, `∨L`, `↔L`/`↔R`, `∃L`, and `⊕L`/`⊕R`.
- **Independent differential test harnesses promoted into the committed suite**, so the
  checkers are cross-checked against oracles *other* than the ones they use internally:
  - the alethic modal Fitch checker against brute-force Kripke-frame enumeration
    (`tests/test_modal_differential.py`) — independent of its standard-translation/Z3
    path, covering the K/T/S4/S5 frame-sensitivity facts;
  - the second-order sequent rules against `satisfies_so` (`so_valid_tiny`) under a
    randomised mutation audit (Z3 cannot evaluate second-order nodes);
  - the object-level eigenvariable freshness condition (`∀R`/`∃L`) under randomised
    fresh/non-fresh fuzzing.

## [0.6.0] - 2026-06-27

A large reasoning-and-interoperability release: a Fitch natural-deduction checker and
backtracking prover, a Gentzen **LK** sequent calculus (with second-order rules) and an
intuitionistic **LJ** calculus, analytic tableaux, a finite model finder, truth tables,
reverse importers for TPTP / Prover9 / Z3-SMT-LIB, intuitionistic Kripke semantics, and
formula verbalization. All additive.

### Added

- **Fitch-style natural-deduction proof checker** (`unicode_fol_kit.atp.fitch`) —
  `Proof` / `Subproof` / `Line` / `Justification` proof objects (frozen, hashable,
  JSON-serialisable) plus `check_proof` / `verify_proof`, all re-exported at the
  package top level. The checker is *sound*: it returns `True` only when every
  line genuinely follows by the cited rule and the proof's premises entail its
  conclusion; `verify_proof` reports the certified sequent and the first failing
  line with a reason.
  - **Classical FOL / MSFOL** (`logic="fol"`/`"msfol"`) is checked by a syntactic
    rule table: the connective rules (`∧I`/`∧E`, `∨I`/`∨E`, `→I`/`→E`, `↔I`/`↔E`,
    `¬I`, `⊥I`/`⊥E`, `¬E` double-negation, `RAA`, `Reit`), the quantifier rules
    (`∀I`/`∀E`, `∃I`/`∃E`) with the eigenvariable side-conditions enforced via a
    capture-avoiding substitution, and equality (`=I`/`=E`, certified against Z3).
    Citation accessibility is enforced (no reaching into a closed sibling
    subproof) and discharge rules are checked against the proof's *open
    assumptions*. `⊥` is the reserved logical constant `FALSUM`.
  - **Three-valued K3 / LP** (`logic="K3"`/`"LP"`) certify each step against the
    many-valued decision procedure (`semantics.manyvalued.entails`), so the
    paraconsistency facts hold: LP rejects modus ponens, the disjunctive
    syllogism, and explosion; K3 has no zero-premise theorems. Propositional
    fragment.
  - **Modal family** (`logic="K"`/`"T"`/`"S4"`/`"S5"`) certifies each step by the
    standard translation to FOL plus the frame axioms, decided by Z3. Knowledge
    (`Knows`, S5) is factive; belief (`Believes`, KD45) and obligation
    (`Obligatory`, KD) are not. Propositional fragment; temporal and quantified
    modal input are rejected.
  - **Rendering** — `render_fitch` (Unicode/ASCII scope bars, line-number gutter,
    justification column; also `proof.to_fitch()`) and `render_latex_fitch`
    (self-contained LaTeX `array`; also `proof.to_latex_fitch()`).
  - Tested with hand-derived proofs per rule, soundness guards for the broken
    cases, and a randomised audit that checks every accepted proof line-by-line
    against the Z3 / resolution oracles.
- **Gentzen sequent-calculus checker** (`unicode_fol_kit.atp.sequent`) — a
  two-sided **LK** derivation checker re-exported at the package top level:
  `Sequent` / `Derivation` / `Comprehension` / `SequentResult`, the helpers
  `sequent` / `derive` / `axiom`, and `check_sequent_proof` / `verify_sequent_proof`
  / `render_sequent_proof`. A sequent `Γ ⊢ Δ` (multisets, read `⋀Γ → ⋁Δ`) is
  derived by a tree of rules; the checker verifies each step.
  - Rules: `Ax`, structural `WL`/`WR`/`CL`/`CR`/`Cut`, the connective rules
    (`¬`, `∧`, `∨`, `→`, `↔`, each L and R), the first-order quantifier rules
    (`∀L`/`∀R`, `∃L`/`∃R`, with the eigenvariable condition on `∀R`/`∃L`), and the
    **second-order** rules `∀²L`/`∀²R`, `∃²L`/`∃²R`. `∀²L`/`∃²R` instantiate a bound
    predicate variable with a comprehension term `λx̄.ψ` (a `Comprehension`,
    arity-checked, capture-avoiding); `∀²R`/`∃²L` use a fresh predicate
    eigenvariable. This reaches the second-order fragment (`second_order=True`),
    which has no first-order / SMT encoding.
  - Sound but, for full second-order logic, necessarily **not a complete prover**
    (second-order validity is not r.e.). Tested with hand derivations per rule,
    soundness guards, a randomised mutation audit that re-checks every accepted
    derivation node-by-node against Z3 (first-order fragment), and `satisfies_so`
    spot-checks over small finite models (second-order fragment).
- **Analytic tableaux** (`unicode_fol_kit.atp.tableau`) — `is_valid_tableau`,
  `prove_tableau`, `tableau_closed`, and `tableau_model`, re-exported at the top
  level. A fourth proof method (beside resolution, Fitch, and the sequent calculus):
  the signed-free α/β/γ/δ rules, a branch closing on `φ`/`¬φ`. Decidable and complete
  for the propositional fragment; first-order γ-instantiation is bounded (`max_terms`
  / `max_steps`). An *open* branch is returned as a countermodel by `tableau_model`.
- **Finite model finder** (`unicode_fol_kit.semantics.modelfinder`) — `find_model`,
  `find_countermodel`, `is_satisfiable_finite`, and `is_valid_finite`. Brute-force
  enumeration of finite `Structure`s (domain `1..max_size`) checked with the Tarskian
  evaluator — the Mace4-style partner of the provers (a valid entailment has no
  countermodel; an invalid one usually a small finite one). Bounded by
  `max_candidates`.
- **Truth tables** (`unicode_fol_kit.semantics.truthtable`) — `truth_table` returning
  a `TruthTable` (Markdown `render`, `is_tautology`/`is_contradiction`/`is_satisfiable`),
  plus `is_tautology` / `is_contradiction` / `is_satisfiable_tt`, over **classical**,
  Kleene **K3**, and Priest **LP** value sets (cross-checked against Z3 for classical).
- **Intuitionistic propositional logic** (`unicode_fol_kit.semantics.intuitionistic`) —
  `IntKripkeModel` with monotone Kripke `forces`, and `int_valid` / `int_countermodel`
  that decide intuitionistic validity by Kripke-model search (the logic has the
  finite-model property). Excluded middle, double-negation elimination, and Peirce's
  law are reported invalid with explicit countermodels; every intuitionistic validity
  is also classically valid (cross-checked).
- **Intuitionistic sequent calculus LJ** (`unicode_fol_kit.atp.lj`) — `check_lj_proof`
  / `verify_lj_proof`, re-exported at the top level. Gentzen **LJ** is the LK calculus
  (it reuses the same `Sequent` / `Derivation` data model) restricted to **at most one
  succedent formula** — the change that makes excluded middle / double-negation
  elimination / Peirce's law underivable. Rules: `Ax`, structural `WL`/`WR`/`CL`/`Cut`,
  `¬`/`∧`/`→`/`↔` (L and R), the split disjunction-right `∨R1`/`∨R2` and `∨L`, and the
  quantifier rules `∀L`/`∀R`, `∃L`/`∃R`. Accepted derivations are cross-checked against
  the intuitionistic Kripke decision procedure and classical Z3 validity.
- **Verbalization** (`unicode_fol_kit.fol.verbalize`) — `to_english`, an English
  paraphrase of a formula (a readability aid, not a parse inverse).
- **Fitch proof *searcher*** (`unicode_fol_kit.atp.fitch_search`) — `find_fitch_proof`,
  `fitch_prove`, and `is_valid_fitch`, re-exported at the package top level. A
  goal-directed, **iterative-deepening backtracking** search over the classical
  propositional + first-order natural-deduction rules (introduction rules, ∨/∃
  elimination by case split, backward chaining, ex falso, and reductio/RAA — which
  makes it complete for the propositional fragment). It builds an actual `Proof`
  that is re-validated by `check_proof` before being returned, so it is **sound by
  construction**: a search/assembly bug can only make it fail to find a proof, never
  return an unsound one. Like the resolution prover it is sound but, under its depth
  bound, incomplete (`None`/`False` = "not found within `max_depth`"). Tested with
  curated theorems/non-theorems and a randomised cross-check that every found proof
  is Z3-valid.
- **Reverse importers for TPTP, Prover9, and Z3/SMT-LIB** — the inverses of
  `to_tptp` / `to_prover9` / `to_z3`, all re-exported at the package top level:
  - **TPTP** (`unicode_fol_kit.fol.tptp_input`): `parse_tptp_formula` (one bare
    FOF/CNF formula → `Node`), `parse_tptp` (a whole problem → a list of
    `TptpFormula(name, role, formula)`), and `load_tptp` (a `.p`/`.tptp` file), via
    a dedicated Lark grammar. Round-trips `to_tptp`; `%` and `/* */` comments are
    ignored; predicates are re-capitalised (TPTP lowercases them); typed
    `tff`/`thf` and `include` are out of scope.
  - **Prover9/LADR** (`unicode_fol_kit.fol.prover9_input`): `parse_prover9`,
    following `set(prolog_style_variables)` to match `to_prover9`'s output (a
    trailing `.` is accepted). `Xor` round-trips to its `(a|b) & -(a&b)` desugaring.
  - **Z3** (`unicode_fol_kit.atp.z3_input`): `from_z3` (a `z3.ExprRef` → `Node`)
    and `parse_smtlib` / `load_smtlib` (SMT-LIB2 via Z3's own parser). Conversion is
    meaning-preserving (Z3 collapses variables/constants/numbers onto one
    uninterpreted sort, so a free variable returns as a `Constant`).
  - Tested by round-trip over random formulas (`parse(node.to_X()) == node`) for
    TPTP/Prover9 and by logical equivalence (`is_valid(Iff(node, from_z3(node.to_z3())))`)
    for Z3, plus curated problem-file and SMT-LIB cases.

## [0.5.2] - 2026-06-26

### Added

- **Predicate-aligned string match** (`unicode_fol_kit.eval.predicate_match`) —
  `match_predicates`, `formulas_are_matched_identical`, and
  `formulas_are_identical`, re-exported at the package top level. A lexical
  (string-level) evaluation notion for NL→FOL: `match_predicates` greedily
  renames each predicate/function symbol in a predicted formula to the
  lexically-closest symbol in the reference (by **normalised Levenshtein
  distance**, accepting matches at or below a `max_norm_distance` threshold,
  default `0.6`), so a structurally-correct answer that merely chose different
  predicate names is not penalised. `formulas_are_identical` is the plain
  whitespace- and case-insensitive string equality; `formulas_are_matched_identical`
  combines the two (realign predicates, then compare). This is **complementary**
  to the AST-level `exact_match`: the canonical match quotients out α-renaming /
  commutativity / associativity / double negation but treats different predicate
  names as a mismatch, whereas this matcher quotients out predicate-name (and
  whitespace/case) differences but not the structural rewrites — the two are
  typically reported as separate metrics. The Levenshtein distance is computed in
  pure Python, so **no new dependency** is introduced; the matcher is
  parser-independent and also applies to raw, not-yet-parseable model output.

## [0.5.1] - 2026-06-24

### Added

- **`check_logical_entailment_vampire`** — entailment checking via the
  [Vampire](https://vprover.github.io/) theorem prover, a TPTP-based companion to
  the existing Prover9 backend. Premises are emitted as TPTP `axiom`s and the
  conclusion as a `conjecture`; the path to the Vampire executable is passed as
  the `vampire_path` argument, and a `SZS status Theorem` result means the
  entailment holds. Classical FOL only (the same fragment `to_tptp` supports).
  Pass `use_wsl=True` to drive a Linux Vampire installed in WSL from a Windows
  host (Vampire is launched via `wsl.exe`, with automatic `wslpath` translation of
  the temp-file path).

## [0.5.0] - 2026-06-24

Adds an NL→FOL **evaluation** toolkit and broad **non-classical logic** coverage —
modal/temporal/epistemic/deontic logic with Kripke semantics, three-valued
(Kleene/Priest) logic, and second-order quantification with finite-model
semantics. All additive; no breaking changes.

### Added

- **`unicode_fol_kit.eval`** — `canonicalize` / `exact_match` (a fair "canonical
  exact match" that quotients out bound-variable renaming, commutativity/
  associativity, operand duplication, and double negation while staying logically
  equivalent), and `validate` / `is_wellformed` / `validate_text` /
  `ValidationReport` (free variables, inconsistent predicate/function arity,
  leftover lambda nodes, parseability of raw model output).
- **Modal / temporal / epistemic / deontic logic** (`MSFLParser(modal=True)`):
  node classes `Box`, `Diamond`, `Knows`, `Believes`, `Always`, `Eventually`,
  `Next`, `Until`, `Obligatory`, `Permitted` with surface syntax `□ ◇`, `K_a` /
  `B_a`, `Ⓖ Ⓕ Ⓝ Ⓤ`, `Ⓞ Ⓟ`. Kripke-model semantics (`KripkeModel`,
  `satisfies_modal`, `reflexive_transitive_closure`) and a relational
  `standard_translation()` to classical FOL so Z3/resolution can decide modal
  validity. Propositional/ground (v1).
- **Many-valued logic** (`unicode_fol_kit.semantics.manyvalued`): three-valued
  strong-Kleene evaluation `kleene_value` over {0, ½, 1}, and `is_valid` /
  `is_satisfiable` / `entails` with selectable designated values for Kleene
  **K3** (`{1}`) and Priest **LP** (`{½, 1}`, paraconsistent). `kleene_value` /
  `DESIGNATED` are also re-exported at the package top level.
- **Second-order / monadic-second-order quantification** (`MSFLParser(second_order=True)`):
  `SecondOrderQuantifier` (`∀P` / `∃P`, arity inferred from the body) with
  finite-model semantics (`satisfies_so`) that enumerates relations over a finite
  domain. Higher-order *terms* remain available via the existing lambda layer;
  full HOL types are out of scope.
- **LaTeX import** — `parse_latex()` reads a LaTeX-math formula (the inverse of
  `to_latex()`) and `latex_to_unicode()` does the LaTeX→Unicode translation alone;
  accepts the exact `to_latex()` output (round-trips) and common hand-written synonyms.

### Internal

- **Operator registry** — operators are now fully self-describing, decoupling
  rendering *and* parsing from the central modules:
  - *Rendering:* each operator registers its glyph, LaTeX markup, precedence, and
    fixity via `register_operator()`; the Unicode and LaTeX renderers are driven
    generically from the registry (no per-operator branches, no hand-maintained
    dispatch tables).
  - *Parsing:* each operator also registers its grammar fragment + transform via
    `register_parser_op()`. `MSFLParser` now assembles BOTH the Lark grammar and
    the transformer for every mode (FOL/MSFOL/MSFL/FL/modal/second-order) from the
    registry — there is no longer a hand-written per-mode transformer or a
    hand-loaded `.lark` grammar on the runtime path.
  - Output and parsed ASTs are byte-identical to before (guarded by a
    legacy-vs-registry equivalence test across a 190-formula × 6-mode corpus).
    Adding an operator — or a whole new logic — is now a self-contained registry
    entry in the operator's own module, with no edit to the renderers, the parser,
    or any shared grammar file.
- **Hardening of the new evaluators.**
  - The three-valued enumeration (`is_valid` / `is_satisfiable` / `entails`) now
    scores each assignment with a compiled evaluator built once from the formula
    (no per-assignment AST walk or atom re-rendering), and refuses to start an
    enumeration above `manyvalued.MAX_MODELS` rather than hanging.
  - Second-order `satisfies_so` refuses a `∀P` / `∃P` whose `2 ** (n ** k)`
    relation space exceeds `secondorder.MAX_RELATIONS`, with a clear error.
  - Added seeded, randomized cross-checks: the compiled three-valued path against
    the reference `kleene_value` on every assignment; strong-Kleene algebraic
    identities and the K3-vs-LP headline facts; second-order `∀P φ ≡ ¬∃P ¬φ`
    duality and the agreement of `satisfies_so`'s classical core with the
    first-order Tarski evaluator; render→parse round-trips over random FOL, modal,
    Łukasiewicz, and second-order formulas; and a whole-tree `tree_str` / `to_dot`
    coverage check over every node type.
  - Łukasiewicz-algebra cross-checks for the fuzzy evaluator (strong/weak
    De Morgan, double negation, the residuum `a → b ≡ ¬a ⊕ b`, and the defining
    adjunction `a ⊗ b ≤ c ⟺ a ≤ b → c`) over random + boundary-grid valuations.
  - Eval cross-checks against the independent Z3 oracle: `canonicalize` is
    equivalence-preserving, `exact_match` absorbs the rewrites it should and never
    merges Z3-inequivalent formulas, and `validate` flags free variables, arity
    clashes, and leftover lambdas.
  - A README example runner executes every `python` block in the docs (cumulative
    namespace) so the documentation stays in lock-step with the code.

## [0.4.0] - 2026-06-23

A large feature release adding model-theoretic and many-valued semantics, an
in-process theorem prover, more solver back-ends, and lambda/normal-form tooling,
plus a set of correctness fixes. **Includes one breaking change** (see *Changed*).

### Added

- **Tarskian model theory** (`unicode_fol_kit.semantics.tarski`): define a
  `Structure` (a "world" with a domain of individuals and interpretations of
  constants, functions, predicates, and — for MSFOL — sorts) and compute a
  formula's truth value with `satisfies()` / `models()` / `term_value()`.
  Equality is built in; sorted quantifiers range over their sort universe.
- **Łukasiewicz fuzzy evaluator** (`fuzzy_evaluate`): the truth degree in [0, 1]
  of an FL/MSFL formula under a valuation (`∀` = inf, `∃` = sup).
- **Fuzzy satisfiability / validity** via Z3 reals: `fuzzy_is_satisfiable`,
  `fuzzy_is_valid`, `fuzzy_get_model`, `degree_expr`.
- **Arithmetic-aware Z3 translation**: `to_z3_arith`, `is_satisfiable_arith`,
  `is_valid_arith`, `get_model_arith` interpret `+ - * /` and the comparisons
  over Z3 reals/integers (the default `to_z3` keeps them uninterpreted).
- **Built-in first-order resolution prover** (`unicode_fol_kit.atp.resolution`):
  `prove`, `is_valid_resolution`, `to_clauses`, `refute` — sound entailment and
  validity checking in-process, without an external prover. Deliberately
  incomplete under a step bound (never reports a non-theorem as proved);
  `=` is treated as an uninterpreted predicate.
- **Lambda tooling**: `eliminate_lambdas` (beta-eta normalise and verify
  lambda-free), `reduce_trace`, `beta_reduce_step`, `has_lambdas`.
- **Normal forms**: `to_dnf` (equivalence-preserving) and `to_tseitin_cnf`
  (equisatisfiable, avoids the distributive blow-up).
- **Robinson unification**: `unify` (most general unifier with occurs-check) and
  `apply_subst`.
- **Command-line interface**: `python -m unicode_fol_kit "<formula>" --mode … --to …`.
- **Typing**: a `py.typed` marker (PEP 561).
- **AST helper**: `Node.map_children`, the single structural-recursion engine.

### Changed

- **BREAKING — AST nodes are now frozen dataclasses.** Every node is immutable
  and **hashable**, so nodes can be put in sets, used as dict keys, and
  deduplicated.
- **BREAKING — `Function.args` and `Atom.args` are now `tuple`s, not `list`s.**
  Construction stays lenient: a list passed to the constructor is coerced to a
  tuple, so `Atom("P", [x])` still works and `node == node` comparisons are
  unaffected. Code that relied on `.args` being a *list* (in-place mutation,
  `isinstance(node.args, list)`, or comparing `node.args == [...]`) must switch
  to tuples.

### Fixed

- `Xor.to_tptp` emitted `~|` (TPTP **NOR**); now emits `<~>` (correct XOR /
  non-equivalence).
- TPTP arithmetic comparisons (`<`, `>`, `≤`, `≥`) are now emitted as prefix
  dollar-word predicates (`$less(a, b)`), not as invalid infix expressions.
- Prover9 export: quantified variables are uppercased to match the emitted
  `set(prolog_style_variables)`; nullary predicates render as bare propositional
  atoms instead of the invalid `P()`.
- `to_latex` escapes the underscore in `c_`-prefixed constants (otherwise read as
  a LaTeX subscript).
- Prover9 entailment: the temporary input file is no longer leaked when the
  `prover9_path` is invalid (now cleaned up in a `finally`).
- Several README inaccuracies (clone URL, "three" vs "four" parser modes, the
  exception class raised on mixing same-level connectives, the `Quantifier`
  AST-table annotation), and the `formulas_are_equivalent` / `is_valid`
  docstrings.

### Documentation

- Clarified that `to_fol` / `to_msfol` is a classical **Boolean projection**
  (the strong and weak Łukasiewicz connectives both collapse to `And`/`Or`), not
  a fuzzy-preserving translation — use `fuzzy_evaluate` / the fuzzy Z3 solver for
  many-valued degrees.

### Internal

- Refactored the duplicated structural recursions (`free_variables`,
  substitution, beta/eta reduction, scope resolution, `to_msfol`/`_relativize`,
  term substitution) onto the shared `Node.map_children` / `_child_nodes`
  helpers, removing the per-node `isinstance` chains while preserving the
  binder-aware special cases and the public `TypeError` contracts.

## [0.3.1] - earlier

- LaTeX export, normal forms, Horn check, Z3 models, traversal API, Graphviz export.

## [0.3.0] - earlier

- `to_unicode_str()` with parser round-trip.

## [0.2.1] - earlier

- README patch release.
