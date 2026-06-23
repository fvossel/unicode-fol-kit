# Changelog

All notable changes to this project are documented in this file. The format is
loosely based on [Keep a Changelog](https://keepachangelog.com/). Versioning is
semantic, but the project is pre-1.0 (alpha): a **minor** release may contain
breaking changes.

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
