# Changelog

All notable changes to this project are documented in this file. The format is
loosely based on [Keep a Changelog](https://keepachangelog.com/). Versioning is
semantic, but the project is pre-1.0 (alpha): a **minor** release may contain
breaking changes.

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
