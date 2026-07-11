# Changelog

All notable changes to this project are documented in this file. The format is
loosely based on [Keep a Changelog](https://keepachangelog.com/). Versioning is
semantic, but the project is pre-1.0 (alpha): a **minor** release may contain
breaking changes.

## [0.15.0] - 2026-07-11

Added — **non-ASCII (Greek) constant names.** A ground constant may now be written
with a Greek letter — e.g. a threshold `θ` in `μ(x, volume) > θ` (“too much”) — so a
bare `θ` lexes as a `CONSTANT` rather than being rejected. The reserved operator
glyphs **λ** (Lambda) and **μ** (Measure) are excluded and keep their operator
meaning. Scope is deliberately narrow: **constants only** — predicates, function
names, and variables stay ASCII.

The Kripke evaluator and the Z3 backend carry the raw unicode name directly. The
text-based, ASCII-only first-order back-ends (`to_prover9` / `to_tptp`) transliterate
it deterministically and reversibly via the new `constant_name_to_ascii` /
`constant_name_from_ascii` helpers: each Greek letter maps to its conventional name
(`θ` → `theta`) and any other non-ASCII character to a reversible `uXXXX` codepoint
escape, so an emitted problem is always valid ASCII and never contains a raw
non-ASCII identifier. Round-trip is exact for single-symbol constants (the realistic
case). Serialization (`to_dict` / `from_dict`) preserves the unicode name.

## [0.14.0] - 2026-07-10

Added — **binary interval operators `Until` (Ⓤ) and `Since` (Ⓢ) in the Isabelle/HOL
shallow embedding.** `to_isabelle_modal` / `isabelle_modal_theory` previously raised
`NotImplementedError` on `Until` and did not handle `Since` at all; both are now
emitted as **inductive least-fixpoint predicates** `muntil` / `msince` over the
one-step successor relation `n`:

- `muntil phi psi` is the least predicate closed under `psi w ⟹ muntil w` and
  `phi w ∧ n w v ∧ muntil v ⟹ muntil w`, so it denotes exactly the finite forward
  `n`-paths with `psi` at the endpoint and `phi` at every earlier point — the faithful
  counterpart of `satisfies_modal`'s depth-first path search (`_until_holds`).
  `msince` is the exact backward mirror over the converse of `n` (`_since_holds`). A
  plain interval reading over the henceforth closure `t` would be **unfaithful on
  branching / short-cut frames**; the least fixpoint is faithful on every frame.
- Using `Until` / `Since` now declares `n` (as `Next` does); when `Always` /
  `Eventually` co-occur, the `n_in_t` / `t_in_nstar` link axioms are emitted so the
  henceforth `t` denotes the closure of the *same* one-step relation the path-search
  operators read.

The `muntil` / `msince` definitions are **Isabelle-verified**: the live `check_theory`
gate loads a mixed-temporal theory and proves the strong-Until / Since fixpoint
equation, the base clause `Q → (P U Q)`, and strong-until reachability. Note this is
the HOL (Isabelle) embedding only — the first-order `qml_translate` still correctly
rejects `Until` / `Since`, which are **not** first-order definable (they need a
transitive-closure / fixpoint), and the `to_thf_modal` exporter remains the alethic
□/◇ fragment.

## [0.13.1] - 2026-07-03

Documentation correctness fix: the higher-order guide and the `hol/__init__`,
`isabelle_modal`, and `thf_modal` docstrings previously described FOL as "not even
semi-decidable". That is wrong — FOL validity is recursively enumerable (Gödel
completeness), so FOL and the standard first-order modal logics K/T/S4/S5 are
**undecidable but semi-decidable**; only full second-order validity is *not even
semi-decidable*. Corrected in the source text and in the German translation. No code
changes.

## [0.13.0] - 2026-07-03

Deep and shallow HOL embeddings with **machine-checked faithfulness proofs**,
reproducing Benzmüller, *Faithful Logic Embeddings in HOL — Deep and Shallow*
(arXiv:2502.19311). For each of four worlds-based non-classical logics the new
`unicode_fol_kit.hol.deepshallow` subpackage emits one self-contained Isabelle/HOL
theory carrying all three embeddings — a **deep** one (object syntax as a `datatype`
with a recursive `truthD`), a **maximal (heavyweight) shallow** one (every semantic
parameter explicit), and a **minimal (lightweight) shallow** one (accessibility and
valuation fixed as `consts`) — together with the `primrec` mappings `dpToMax` /
`dpToMin` and the theorems `faithful1a`/`faithful1b` (deep ↔ maximal),
`faithful2`/`faithful3` (↔ minimal in the fixed model) and `sound_min`, each closed
by a one-line `induct`. Unlike the existing emit-only shallow exporters, these
theories are **verified end to end** by the Isabelle runner (`check_theory`): a
green build means Isabelle's kernel discharged every faithfulness proof.

Added:

- `modal_faithfulness_theory` / `modal_to_deep` — propositional modal logic K.
- `intuitionistic_faithfulness_theory` / `int_to_deep` — intuitionistic
  propositional logic (Kripke semantics: preorder ≤, persistent valuation).
- `conditional_faithfulness_theory` / `counterfactual_to_deep` — Lewis
  counterfactual (sphere) logic, matching `semantics.conditional`.
- `relevant_faithfulness_theory` / `rel_to_deep` — relevant logic B (simplified
  Routley–Meyer semantics: normal worlds, Routley star, ternary relation), matching
  `semantics.relevant`.
- Isabelle-gated live tests that build each emitted theory and assert the kernel
  discharges the five faithfulness theorems, plus always-run structure tests.

The stack targets the propositional/schematic fragment (where induction over the
syntax datatype applies); the quantified decision path stays in
`unicode_fol_kit.hol.isabelle_modal`.

## [0.12.0] - 2026-07-03

The four families the documentation used to list as deliberately out of scope are
now first-class: relevant logic, hybrid logic, dependence / IF logic, and the
substructural pair (intuitionistic linear logic and the Lambek calculus). Each
ships with parser support, real semantics or a real proof system, hand-checked
tests cross-checked against existing oracles, and a documentation page.

### Added

- **Relevant logic B** (`semantics.relevant`) — the Priest–Sylvan *simplified*
  Routley–Meyer semantics for the basic affixing system **B** over the classical
  propositional syntax: `RelevantModel` (worlds, normal worlds, involutive Routley
  star, ternary accessibility at non-normal worlds), `rel_satisfies`, and a
  verified exhaustive countermodel search `rel_countermodel` / `rel_valid`
  (bounded, mirroring `int_valid`'s contract). The headline non-theorems come out
  right: `p → (q → p)`, explosion, disjunctive syllogism, Peirce, and even
  `p ∨ ¬p` are refuted, while the B-validities hold. Random formulas are
  cross-checked against the classical Z3 oracle (every classical countermodel is
  a one-world Routley–Meyer model). B is the decidable base; full **R** is
  undecidable (Urquhart 1984) and stays out of scope.
- **Hybrid logic H(@)** — nominals and the satisfaction operator inside the modal
  mode: `MSFLParser(modal=True)` now parses nominals (`i`, `here`) as formulas
  and `@i φ`; `KripkeModel` takes a `nominals=` assignment and `satisfies_modal`
  evaluates both constructs; the standard translation maps a nominal to a
  world-equality with a reserved `nom_…` constant, and the new
  `hybrid_is_valid(φ, frame="K"|"T"|"S4"|"S5")` decides hybrid validity via Z3.
  The ↓ binder is deliberately absent (it makes validity undecidable); the modal
  tableau rejects hybrid input with a clear error instead of guessing.
- **Dependence / IF logic** (`MSFLParser(dependence=True)` + `semantics.team`) —
  Väänänen-style **team semantics** over the toolkit's finite `Structure`s:
  dependence atoms `=(x, y)` (functional determination; `=(x)` constancy) and
  IF slashed existentials `∃y/{x} φ` (witness chosen uniformly in the slashed
  variables), with the splitting `∨`, strict `∃`, duplicating `∀`, and flat
  literals. `team_satisfies` / `team_models` evaluate; the fragment is honest —
  no `→`/`↔`, negation on atoms only, and no classical export (dependence logic
  is expressively second-order). Tested with flatness and downward-closure
  property tests against the Tarski evaluator and the classic `|dom| = 1`
  signalling facts.
- **Substructural logics** — two new sequent provers in `atp`:
  `MSFLParser(linear=True)` parses propositional **intuitionistic linear logic**
  (`⊗ & ⊕ ⊸ ! 𝟙`) and `ill_prove` / `ill_derivable` / `check_ill_proof` decide it
  by cut-free backward search — a complete decision procedure for the !-free
  fragment, honestly bounded when `!` occurs; `MSFLParser(lambek=True)` parses
  **Lambek-calculus** types (`• \ /` over categories like `NP`, `S`) and
  `lambek_prove` / `lambek_derivable` are a complete, terminating decision
  procedure for L (ordered, nonempty antecedents — `A, A\B ⊢ B` derives,
  `A\B, A ⊢ B` does not). Every found derivation is re-validated by its checker,
  and every derivable sequent's classical collapse is verified Z3-valid in the
  test suite.
- The frontier constructs render, verbalize (`to_english`), serialise
  (dict/JSON), and round-trip like every other node family; `exact_match` /
  `canonicalize` α-normalise the slashed binder (slash sets follow their
  enclosing binders' renames).

## [0.11.0] - 2026-07-02

Cross-logic parity for the natural-language / CCG translation-target constructs, plus a
capture-safety fix in the canonical form. The guiding principle: anything expressible in
classical FOL should also be expressible in the richer classical logics that extend it
(modal, second-order, and many-sorted), so a construct is no longer arbitrarily confined
to the plain `fol` mode.

### Added

- **Counting quantifier, concessive connective, and degree/cardinality terms across the
  classical modes.** `Count` (`∃≥n` / `∃≤n` / `∃=n`), `Contrast` (`Ⓒ`), `Measure` (`μ`),
  and `Cardinality` (`|{v : φ}|`) — previously accepted only by `MSFLParser()` — now also
  parse in **modal** mode (`MSFLParser(modal=True)`) and **second-order** mode
  (`MSFLParser(second_order=True)`), with identical semantics. A CCG-derived form that
  nests a counting quantifier under a modal or second-order operator — e.g.
  `B_a ∃≥3 x Pass(x)` ("a believes at least three x pass") — now parses and round-trips as
  a single string, not only as a hand-assembled AST.
- **MSFOL many-sorted parity: `SortedCount` and `SortedCardinality`.** The many-sorted mode
  (`MSFLParser(many_sorted=True)`) gains sort-annotated counterparts of the counting
  quantifier and the set-cardinality term — `∃≥n x:S φ` (`SortedCount`) and `|{v:S : φ}|`
  (`SortedCardinality`) — mirroring `SortedQuantifier`. `SortedCount` reduces to plain FOL
  by guarding the matrix with the sort predicate and reusing the distinct-witnesses
  encoding (so it is Z3-checkable); `SortedCardinality` is second-order and, like
  `Cardinality`, has no first-order export. `Contrast`, the `Measure` term, and `Xor` (`⊕`,
  previously excluded from MSFOL) are available in MSFOL too. Both new node types are
  exported from the package root.
- The fuzzy modes (FL / MSFL) deliberately **do not** gain these constructs: fuzzy logic is
  not a conservative extension of classical FOL (it reinterprets the connectives and its
  evaluator rejects comparison atoms), so counting/degree/cardinality/concession have no
  faithful truth semantics there. This is an intentional boundary, not an omission.

### Fixed

- **`exact_match` / `canonicalize` now α-normalize the counting and cardinality binders.**
  `Count` and `Cardinality` (and their new sorted variants) bind a variable, but the
  canonical form previously treated only `Quantifier` / `SortedQuantifier` / `Lambda` as
  binders. As a result `∃≥3 x P(x)` and `∃≥3 y P(y)` — α-equivalent — compared as unequal.
  They now canonicalize identically, while the op, the bound `n`, the sort, and the matrix
  stay significant.
- **Capture-safety of the canonical bound-variable rename.** The rename to canonical names
  `q0, q1, …` did not avoid free variables that happen to be named the same way, so the
  logically-distinct `∃x P(x)` and `∃x P(q0)` (where `q0` is free) both canonicalized to
  `∃q0 P(q0)` — a false positive in `exact_match` that violated equivalence-preservation.
  The rename now skips any canonical name that occurs free in the formula. The bug affected
  every binder (`Quantifier` / `Lambda` included) and was newly reachable through the
  counting binders; the fix covers all of them.

## [0.10.1] - 2026-06-30

### Fixed

- `unicode_fol_kit.__version__` now reports the actual package version (it lagged
  at `"0.9.0"` in the 0.10.0 release). The Sphinx / Read the Docs configuration
  reads this string for the documented version, so the docs version display is
  corrected as well.

## [0.10.0] - 2026-06-30

Natural-language → logic front-end support: attitude operators, a counting
quantifier, degree and cardinality terms, a concessive connective, a whole-file
Prover9 reader, TPTP single-quoted atoms, and name sanitisation. These are translation
targets and interchange aids for pipelines (e.g. CCG → logical form, or OWL → FOL)
that need a determinate, round-trippable representation of cardinal determiners,
degree comparatives, counting comparisons, reportative/desiderative attitudes, and
concessive coordination — and that ingest external problem files whose symbol names
are not native MSFLParser tokens.

### Added

- **Assertive and bouletic attitude operators** — `Says` (`Say_a φ`, *a asserts that
  φ*) and `Wants` (`Want_a φ`, *a wants it to be that φ*), modal `agent_prefix`
  operators alongside `Knows`/`Believes` (the agent is a β-bindable term, so
  `∀x (Speaker(x) → Say_x φ)` works). `Says` is **non-factive** and **non-doxastic**;
  `Wants` is **non-veridical** — each a minimal normal modality **K** over its own
  per-agent accessibility relation (`"Say:"+a` / `"Want:"+a`), with no frame
  conditions. Wired into the parser (`MSFLParser(modal=True)`), `satisfies_modal`, the
  modal tableau (`is_modal_valid`), `to_english`, and the dict/Unicode/LaTeX renderers.
- **Counting quantifier `Count`** — `∃≥n` / `∃≤n` / `∃=n` (at least / at most /
  exactly *n*). The bound *n* is carried **symbolically** (a `Number`, never expanded
  into single-letter variables), so an arbitrarily large *n* — `∃≥500 x …` — is
  represented exactly and coordinated counts compose as `And(Count(…), Count(…))`.
  First-order expressible: `to_z3` / `to_prover9` / `to_tptp` lower it to the standard
  distinct-witnesses encoding (a balanced conjunction tree, verified against Z3; the
  expansion is bounded to `n ≤ 500` — beyond that the exporters raise a clear error,
  while the symbolic node still round-trips for any `n`). Parses with the default
  `MSFLParser()`.
- **Degree term `Measure`** — `μ(entity, dimension)`, a first-class measure-function
  term for bare quantity comparatives (`μ(x, height) > μ(y, height)`); exports as the
  uninterpreted binary function `measure(entity, dimension)`.
- **Set-cardinality term `Cardinality`** — `|{v : φ}|`, the count of individuals
  satisfying `φ`, for faithful counting comparisons (`|{v : Votes(x, v)}| > |{v :
  Votes(y, v)}|`). It binds `v`; set cardinality is second-order, so it has **no**
  first-order export.
- **Concessive connective `Contrast`** — `P Ⓒ Q` (whereas / although / but),
  truth-functionally identical to `∧` but kept distinct so a front-end can preserve
  the concession instead of flattening it.
- **Whole-file Prover9 reader** — `load_prover9(path)` / `parse_prover9_problem(text)`
  read a Prover9 / LADR input file: `set` / `clear` / `assign` directives (recognised
  and skipped), `formulas(LIST). … end_of_list.` blocks, and bare top-level formulas,
  returning `Prover9Formula(role, formula)` records (the list name becomes the role).
  Completes the file-reading trio with `load_tptp` and `load_smtlib`.
- **TPTP single-quoted atoms** — the TPTP reader now accepts single-quoted functor
  names (`'http___example_org_Thing'(X)`), the form OWL→FOL dumps use for IRIs; the
  quotes are stripped and the `\'` / `\\` escapes unescaped. A 2.3 MB / 7198-formula
  OWL ontology dump reads end to end.
- **Name sanitisation for round-trippable rendering** — `sanitize_names(node)` /
  `sanitize_all(nodes)` rewrite imported symbol names to MSFLParser-legal tokens
  (predicates `[A-Z]…`, functions multi-letter lowercase, constants kept or put in the
  `c_…` form, variables `[a-z][0-9]*`) so that `parse(node.to_unicode_str())` round-trips.
  Already-legal names are unchanged; a returned `NameMapping` recovers the originals and
  keeps names consistent across a whole problem. (Verified: all 7198 formulas of the OWL
  dump round-trip after sanitisation.)

## [0.9.0] - 2026-06-29

A broad non-classical expansion: a native modal tableau, past-tense temporal logic,
more modal frames, four-valued FDE and a general matrix layer, fuzzy t-norms,
first-order intuitionistic and second-order search, sorted model finding, a
description-logic subpackage, and a cluster of non-classical neighbours.

### Added

- **Native modal tableaux — `unicode_fol_kit.atp.modal_tableau`.** A labelled,
  install-free tableau that decides the propositional box/diamond family (alethic
  `□`/`◇`, epistemic `K_a`, doxastic `B_a`, deontic `O`/`P`, one-step temporal `Next`)
  over the systems **K, T, D, B, K4, K45, S4, S5, KD45** plus per-family systems.
  `is_modal_valid` / `modal_decide` / `modal_countermodel` return valid / invalid /
  unknown with a Kripke counter-model **verified** against `satisfies_modal`. The
  classical `is_valid_tableau` / `prove_tableau` / `tableau_closed` now route modal
  inputs here instead of raising `ValueError`.
- **Past-tense temporal operators** — Prior tense logic: `Historically` (⒣), `Once`
  (⒫), `Previous` (⒴) and binary `Since` (⒮), the duals of `Always`/`Eventually`/
  `Next`/`Until` over the converse temporal relation. Covered in the parser,
  `satisfies_modal`, the standard translation, the qml embedding, and `to_english`.
- **More modal frames** — `B` (Brouwer), `S4.2` (convergent), `S4.3` (linear) decided
  by Z3 (`qml_is_valid`); `GL` (Gödel–Löb provability) via the Löb schema in the
  Isabelle / THF exporters (verified to discharge Löb's theorem in real Isabelle).
- **Finite-valued logical matrices + Belnap–Dunn FDE** — `semantics.matrix`:
  `TruthMatrix.from_functions` builds any finite matrix; ships `K3_MATRIX`,
  `LP_MATRIX` (reproducing the existing three-valued decisions) and the four-valued
  `FDE_MATRIX` (paraconsistent *and* paracomplete, with no logical truths).
- **Fuzzy t-norm selector + quantifier grounding** — `fuzzy_evaluate(…, tnorm=)` over
  **Łukasiewicz / Gödel / product** (new `semantics.tnorm`); `z3_fuzzy` decides the two
  piecewise-linear t-norms and **grounds quantifiers** over a finite domain, so
  quantified fuzzy validity / satisfiability is now decidable.
- **First-order intuitionistic Kripke search** — `int_valid` / `int_countermodel`
  search increasing-domain models for quantified formulas (bounded; the propositional
  fragment stays an exact decision).
- **Bounded second-order search** — `so_find_model` / `so_find_countermodel` /
  `so_is_satisfiable_finite` / `so_is_valid_finite` complement `satisfies_so`.
- **Many-sorted (MSFOL) model finding** — `find_model` / `find_countermodel` enumerate
  sort universes and return sorted `Structure`s.
- **Description logic ALC — `unicode_fol_kit.dl`.** Concept syntax (⊤ ⊥, ¬ ⊓ ⊔, ∃r.C
  ∀r.C), and a tableau reasoner (`concept_satisfiable`, `subsumes`, `equivalent`,
  `abox_consistent`) over general TBoxes / ABoxes, with TBox internalisation and subset
  blocking; cross-checked against the modal tableau.
- **Non-classical neighbours** — free logic (`semantics.free_logic`), public-
  announcement / dynamic epistemic logic (`semantics.dynamic_epistemic`),
  counterfactual conditionals (`semantics.conditional`, Lewis spheres), and
  circumscriptive non-monotonic entailment (`semantics.nonmonotonic`).
- **`isabelle_decide_fol` — decide classical FOL / MSFOL through Isabelle.** The
  counterpart of `isabelle_decide_modal` for the classical fragment: prove-battery →
  `nitpick` finite counter-model → UNKNOWN (common, since FOL is only semi-decidable),
  over `to_isabelle_fol` / `to_isabelle_msfol`. Returns a `FolVerdict`. Equality stays
  the **uninterpreted** `feq` / `fneq` of the embedding (no equality axioms assumed).
- **Linux CI for the Isabelle-backed tests** (`.github/workflows/isabelle-tests.yml`).
  Installs a real Linux Isabelle (cached) and runs the gated live tests on
  `ubuntu-latest` — the standing guarantee that the runner's primary (Linux) path
  works, since the dev box is Windows. Path-scoped + `workflow_dispatch`.

### Changed

- **`to_english` paraphrases the non-classical operators** (modal / temporal /
  epistemic / deontic / second-order / fuzzy) instead of falling back to glyphs; the
  fuzzy strong/weak/Łukasiewicz connectives are named so they do not read as their
  classical look-alikes. `naming` gained explicit modal / second-order mixing-error hints.

- **`isabelle_decide_modal` INVALID verdicts now carry a concrete counter-model.** For
  the propositional alethic fragment, `ModalVerdict.countermodel` is populated with a
  finite Kripke counter-model reconstructed from the toolkit's own `satisfies_modal`
  evaluator (`isabelle build` does not echo nitpick's model). `None` for fragments the
  bounded search does not cover — the certified verdict is unaffected.
- **Temporal `Always`/`Eventually` + `Next` refutation is sharp again.** The runner's
  *refute* theory now **defines** the henceforth relation as `t = rtranclp n` (the
  reflexive-transitive closure) instead of axiomatising it, so nitpick can construct the
  closure and genuinely refute a non-theorem — e.g. `Next(p) → Always(p)` is now
  `INVALID` instead of `UNKNOWN`. The *prove* theory keeps the axiom form (the battery
  needs it); both encode `t = n**`. (New `temporal_def` flag on `isabelle_modal_theory`.)

## [0.8.0] - 2026-06-28

### Added

- **Run a local Isabelle to actually *prove* the modal embeddings — `unicode_fol_kit.hol.isabelle_runner`.**
  The `hol` exporters only *emit*; this opt-in module turns "emit" into "proven / refuted" when an
  Isabelle/HOL install is present. `isabelle_decide_modal(φ, frame=…, mode=…)` decides validity by a
  two-step procedure, read off the build's exit code: (1) emit the lemma with a proof battery that
  brings the frame/domain axioms into scope (`using … by (blast | force | … | meson … | metis …)`) — a
  successful `isabelle build` means **VALID**; (2) otherwise emit `nitpick[expect = genuine]`, whose
  build succeeds **iff** a genuine finite counter-model exists — that means **INVALID**; (3) otherwise
  **UNKNOWN**. Sound (Isabelle's kernel certifies the proof; nitpick reports only genuine
  counter-models) and, necessarily, incomplete. The verdict is validated *differentially* against an
  independent brute-force Kripke oracle (`satisfies_modal`) across K/T/S4/S5 in the test suite.
  - `find_isabelle` / `isabelle_available` locate an install (explicit path → `UFK_ISABELLE_HOME` /
    `ISABELLE_HOME` → `isabelle` on `PATH` → a light scan); `check_theory(text, name)` builds any
    self-contained theory; `ModalVerdict` / `BuildResult` / `IsabelleInstall` carry the results.
  - **Linux/macOS is the primary path** — `isabelle` is invoked directly. **Windows** is also
    supported: the build is additionally routed through Isabelle's bundled Cygwin (Windows→`/cygdrive`
    path translation, launcher exec-bit fixup, `bin` on `PATH`). No install path is hard-coded —
    installations are discovered generically. Absent Isabelle raises a clear `IsabelleNotAvailable`;
    the live tests skip.
  - All re-exported at the package top level.

### Fixed

- **`to_isabelle_modal` emitted proofs could not discharge axiom-dependent validities.** A bare
  `axiomatization where r_refl: …` fact is not in Isabelle's default claset, so `by blast` / `by auto`
  / `by (metis …)` could not see it: every validity that *depends* on a frame/domain axiom (T, S4, S5,
  KD, KD45, the temporal closure, a domain regime) failed to prove even though the formula is valid and
  the theory sound (only the pure-K fragment, like the K axiom, went through). The `by`-style tactics
  now emit `using <frame/domain axioms> by …`. New `modal_axiom_names(φ, …)` exposes the axioms in
  scope, and `isabelle_modal_theory(…, proof=…)` accepts an explicit proof override.
- **`to_isabelle_k3lp` / `to_isabelle_k3lp_entailment` emitted a non-discharging proof.**
  `by (simp add: des_def)` does **not** close the validity lemma — `simp` cannot reduce `kneg v` /
  `kor v …` while the quantified truth-value `v` is abstract (e.g. the LP-valid `p ∨ ¬p` failed). The
  `∀` (valid) form is now discharged by exhausting each variable's three `tv` constructors
  (`case_tac` + `simp_all`); the `∃` (refutation) form by supplying the counter-valuation as `rule exI`
  witnesses computed at emit time. Every form is verified to build in real Isabelle.

### Changed

- **`to_isabelle_intuitionistic` now emits a real, Isabelle-checked proof for valid formulas.** The
  proof is verdict-dependent: an intuitionistically valid formula gets `using r_refl r_trans by
  (metis … | meson … | blast | auto)` that Isabelle discharges; a non-valid one is left `oops` (loads,
  claims nothing — see `int_countermodel`). Previously the lemma was always `oops`. The verdict is
  taken from the **decidable** S4 oracle `gmt_is_s4_valid` (Z3 on the GMT→S4 translation), *not* from
  `int_valid`'s default 3-world bound — which is incomplete (IPL's finite-model bound grows with the
  formula, so a non-theorem like `(p→q)∨(q→r)∨(r→p)` would otherwise be mis-emitted with a real
  proof that cannot close).

### Audit hardening

A multi-agent adversarial soundness audit of the new subsystem confirmed five issues (no false
*VALID* is possible — Isabelle's kernel rejects a proof of a false goal), all fixed and re-checked
against a live Isabelle:

- **Intuitionistic proof gated on the decidable oracle** (above) — was a real proof emitted for an
  IPL-*invalid* formula (theory then failed to build).
- **Atom-name collisions in the intuitionistic export.** An atom named `r` (or `w`/`v`/`u`) collided
  with the accessibility relation / frame-axiom variables, emitting a duplicate `consts r` (or an
  ill-typed axiom) so the theory never loaded — even for the valid `r → r`. `_isa_atom_name` now
  reserves the structural identifiers and de-collides (`r` → `p_r`).
- **Temporal closure now pinned faithfully.** When `Always`/`Eventually` co-occur with `Next`, the
  emitted henceforth relation `t` is now forced to equal the reflexive-transitive closure of the
  one-step `n` (`t ⊆ rtranclp n`, with the existing `t_refl`/`t_trans`/`n_in_t` giving the converse),
  matching `satisfies_modal`. Previously `t` could be any refl-trans superset of `n`, so a
  `satisfies_modal`-valid temporal induction `(p ∧ G(p→Xp)) → Gp` was spuriously refuted (a false
  *INVALID*); it is now never refuted (UNKNOWN — the closure fragment is a documented approximation).
- **`ModalVerdict.infra_error`.** An `UNKNOWN` whose build failed for an infrastructure reason
  (syntax / JVM / timeout / …) now carries a short signature, so a broken theory or environment is no
  longer indistinguishable from honest incompleteness. Never changes the verdict.

## [0.7.0] - 2026-06-28

### Added

- **Epistemic / doxastic frame systems in the first-order embedding.**
  `qml_is_valid` / `qml_equivalent` now take `systems={"epistemic": "S5", "doxastic":
  "KD45"}`, emitting per-agent frame axioms for the agent-indexed `Rk` / `Rb` relations
  — so e.g. factivity `∀x (K_x φ → φ)` is valid under a reflexive epistemic system. This
  makes the FO path symmetric to the THF exporter (which already had `systems=`).
- **Quantified modal logic (QML) via shallow embeddings.** Object quantifiers `∀x` /
  `∃x` under a modality, with the domain-regime semantics that decide the Barcan
  formulas:
  - **Semantics** — `KripkeModel` now takes per-world object domains (`domains={w: …}`
    for varying, `domain=[…]` for constant), and `satisfies_modal` interprets `∀x` /
    `∃x` *actualistically* (at a world `w` they range over `D_w`). Barcan
    (`◇∃x A → ∃x ◇A`) and converse Barcan are valid/invalid exactly as the domains
    vary. Backward compatible (omit the domains for the propositional fragment).
  - **(A) First-order shallow embedding** (`unicode_fol_kit.fol.qml`): `qml_translate`
    (with the existence predicate `E!` relativising actualist quantifiers + world/object
    sort guards), `qml_axioms`, and `qml_is_valid` / `qml_equivalent` decide validity /
    equivalence with Z3 per domain regime (`constant` / `increasing` / `decreasing` /
    `varying`) and frame (K/T/S4/S5/KD/KD45). Sound but bounded-incomplete (first-order
    modal logic is undecidable). The regime↔Barcan correspondence (BF ⇔ decreasing,
    CBF ⇔ increasing, constant ⇔ both) is cross-checked against exhaustive Kripke-model
    enumeration over every regime.
  - **(B) Higher-order shallow embedding** — `to_thf_modal` emits a Benzmüller-style
    TPTP **THF** problem (lifted `mbox`/`mdia`/`mforall`/`mexists`/`mvalid` + frame and
    domain axioms) for an external higher-order prover (Leo-III, Satallax); 
    `to_isabelle_modal` emits an Isabelle/HOL skeleton. Alethic □/◇ fragment.
  - All re-exported at the package top level; `BARCAN` / `CONVERSE_BARCAN` are provided
    as the standard litmus formulas.
- **`⊕L` / `⊕R` (exclusive-or) rules in the sequent calculus** (`A⊕B ≡ ¬(A↔B)`),
  closing the one connective that had no inference rule in either checker.
- **HOL / Isabelle / THF exporters for all non-fuzzy logics** (new
  `unicode_fol_kit.hol` subpackage) — Benzmüller-style shallow semantical embeddings,
  emitted as complete problem files for an external prover (the toolkit emits; it does
  not run Leo-III / Satallax / Sledgehammer, and FOL / FO-modal / SOL are undecidable, so
  emission means "a sound problem a prover *may* discharge", never "decided"):
  - `hol.isabelle_modal.to_isabelle_modal` — a **real, loadable** Isabelle/HOL theory
    (`theory … imports Main begin … end`, all lifted operators, frame + domain axioms,
    the formula lifted into the embedding, a real `lemma`) for the **full modal family**:
    alethic, epistemic/doxastic over **agent-indexed** relations, deontic, temporal.
    Replaces the old alethic-only skeleton that emitted the lemma inside a comment.
  - `hol.thf_modal.to_thf_modal_full` — the full-modal-family TPTP **THF** export
    (agent-indexed epistemic/doxastic, deontic, temporal), extending the alethic-only
    `qml.to_thf_modal`; self-contained (every relation the macro block references is declared).
  - `hol.classical` (FOL + MSFOL), `hol.manyvalued` (K3 / LP, cross-checked against the
    three-valued evaluator), `hol.secondorder` (native HOL predicate quantification),
    `hol.intuitionistic` (Gödel–McKinsey–Tarski → S4 → HOL, cross-checked against
    `int_valid`) — each → THF and Isabelle.
- **First-class agent terms for epistemic/doxastic operators.** The `agent` of
  `Knows` / `Believes` is now a **term** (Variable or Constant), a structural child, so
  it is reached by `free_variables` / substitution / β-reduction and can be a quantified
  variable — `∀x (Student(x) → K_x φ)` (a quantified subject, "every student who…")
  finally works: the agent is the bound `x`, not a baked-in relation-name suffix.
  - The Kripke evaluator uses **per-agent** accessibility relations (one agent can know
    what another does not); object quantifiers ground a bound agent before the modality
    is reached.
  - The first-order shallow embedding emits an **agent-indexed ternary** relation
    `Rk(agent, w, v)` / `Rb(agent, w, v)`, so a bound agent genuinely quantifies over
    agents (epistemic/doxastic relations are plain `K` — no frame axioms yet).
  - Parser convention: a free `K_a` is a *named* agent (→ Constant); an agent bound by an
    enclosing quantifier (`K_x` under `∀x`) stays a Variable. A bare string passed to the
    constructor is coerced to a Constant (backward compatible).

### Fixed

- **HOL/THF/Isabelle exporters: distinct symbols can no longer collapse to one name.**
  A de-colliding resolver (`_ThfNames` / `_IsaNames` / the second-order and classical
  resolvers) guarantees each distinct `(kind, name, arity)` symbol gets a unique emitted
  functor / `consts`, and a predicate used at two arities is two symbols. Fixes a
  **soundness hole** where a non-valid formula could be emitted as valid — e.g. `□Ab →
  □ab` collapsing to the tautology `□ab → □ab` (also in the shipped `qml.to_thf_modal`)
  — and the duplicate / ill-typed declarations that made `to_isabelle_so` / the modal
  Isabelle theories non-loadable.
- **`to_isabelle_modal` is now the real exporter everywhere.** The top-level
  `to_isabelle_modal` (and `fol.qml.to_isabelle_modal`) delegate to the complete
  `unicode_fol_kit.hol.isabelle_modal` implementation (a loadable theory with a genuine
  `lemma`), instead of the old alethic-only skeleton that emitted the lemma in a comment.
- **`substitute` is now capture-avoiding for a re-binding quantifier.** Substituting a
  `Variable` (as `satisfies_modal` does when grounding an object quantifier) no longer
  leaks past an inner quantifier that re-binds the same name: `substitute(∃x A(x), x, a)`
  now correctly returns `∃x A(x)` unchanged. This fixes a **soundness bug in the modal
  evaluator**, where a shadowed quantifier (e.g. `∀x ∃x A(x)`, also under modalities)
  evaluated to the wrong truth value. (The `Lambda` branch already stopped at a rebinding
  binder; the `Quantifier` / `SortedQuantifier` branches now do too.)
- **QML rejects an unknown `mode`.** `qml_translate` / `qml_is_valid` / `qml_equivalent`
  raise `ValueError` on an unrecognised domain regime (e.g. a mis-capitalised
  `'Increasing'`) instead of silently treating it as constant-domain and returning a
  wrong validity verdict — matching the existing `frame` validation.
- **THF export: `possibilist` now emits the `const_dom` axiom.** Since the FO embedding
  treats `possibilist` as a constant domain, the THF export does too (its actualist
  `mforall`/`mexists` macros would otherwise model a varying domain), keeping the two
  embeddings in agreement.
- **THF export: `=` / `≠` are now uninterpreted predicates, not primitive HOL identity.**
  `to_thf_modal` previously rendered equality as rigid HOL `=`, diverging from
  `satisfies_modal` and the FO embedding (which key `=` / `≠` as ordinary
  world-relativized predicates) — so e.g. `∀x. x=x` was a THF theorem but
  Kripke-falsifiable. All three embeddings now agree.

### Internal

- **Retired the parser-equivalence oracle.** The registry-assembled parser was pinned
  during migration by a byte-for-byte equivalence test against the legacy hand-written
  per-mode `.lark` grammars + `*Transformer` classes. With that equivalence long
  established, the reference pipeline was removed: the six per-mode grammar files
  (`fol`/`msfol`/`msfl`/`fl`/`modal`/`so.lark`) and the legacy transformer classes are
  gone; the registry self-assembly + grammar-structure guards remain. Only
  `terminals.lark` survives (imported by the generated grammar at runtime).
- **Shared symbol-name de-collision** (`fol/_symbol_names.py`): the `dedupe` helper and
  the THF/Isabelle resolver, previously copy-pasted across the exporters, are now one
  `SymbolNames` base + `dedupe` used by the THF, Isabelle, classical, and second-order
  exporters.
- **Agent token parsing reuses the scope pass.** The epistemic/doxastic agent is parsed
  as a Variable and resolved to bound-Variable / free-Constant by `resolve_agent_variables`
  (mirroring `resolve_lambda_scope`), instead of re-deciding variable-vs-constant with a
  hand-copied lexer regex.
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
