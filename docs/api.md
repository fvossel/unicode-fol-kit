# API reference

Auto-generated from the package docstrings, and **complete**: every name in
`unicode_fol_kit.__all__` and in each subpackage's `__all__` appears in exactly
one table below, linking to its full signature and documentation. A test
(`tests/test_api_reference_complete.py`) enforces that, so a new public name
cannot ship undocumented.

Names are grouped by what they are FOR, not by which module they live in — the
module view is the last section. A name re-exported at top level is documented
under that path; a name that exists only inside a subpackage is documented
there. Two deliberate exceptions:

- Five names appear twice, under different paths, because they are **different
  objects** that happen to share a name: `check_theory`
  ({func}`unicode_fol_kit.check_theory` builds and runs an Isabelle theory,
  {func}`unicode_fol_kit.eval.check_theory` audits a set of definitions), and
  the description-logic concept constructors `And`/`Or`/`Not`/`Top`, which are
  ALC concepts rather than formula nodes.
- Ten dict registries and naming maps are documented at their **definition
  site** rather than at the re-export path, because that is the only place
  their documentation exists: a name imported into a module carries no
  attribute comment there, and the reference would fall back to describing the
  `dict` constructor.

## Parsing & the AST

```{eval-rst}
.. currentmodule:: unicode_fol_kit

.. autosummary::
   :toctree: _autosummary
   :nosignatures:

   MSFLParser
   Node
   replace_at
   node_at
   substitute
   free_variables
   to_fol
   serialize
   deserialize
   SCHEMA_VERSION
   Z3Env
   detect_dialects
   to_english
   CCGDerivation
   reduction_derivation
```

## Source spans

```{eval-rst}
.. currentmodule:: unicode_fol_kit

.. autosummary::
   :toctree: _autosummary
   :nosignatures:

   SpannedFormula
   SpanMap
   NodeSpans
   Path
   Span
   UNKNOWN
   traverse
   build_span_map
   project_spans
```

## AST: terms and the classical connectives

```{eval-rst}
.. autosummary::
   :toctree: _autosummary
   :nosignatures:

   Variable
   Constant
   Number
   Function
   Atom
   Not
   And
   Or
   Xor
   Implies
   Iff
   Quantifier
```

## AST: sorts, signatures and counting

```{eval-rst}
.. autosummary::
   :toctree: _autosummary
   :nosignatures:

   Signature
   PredicateDecl
   FunctionDecl
   ConstantDecl
   SortedQuantifier
   SortedConstant
   SortedCount
   SortedCardinality
   Count
   Measure
   Cardinality
   Contrast
   sanitize_names
   sanitize_all
   NameMapping
```

## AST: lambda terms

```{eval-rst}
.. autosummary::
   :toctree: _autosummary
   :nosignatures:

   LambdaVar
   Lambda
   Application
```

## AST: modal, temporal, epistemic and deontic operators

```{eval-rst}
.. autosummary::
   :toctree: _autosummary
   :nosignatures:

   Box
   Diamond
   Knows
   Believes
   Says
   Wants
   Always
   Eventually
   Next
   Until
   Historically
   Once
   Previous
   Since
   Obligatory
   Permitted
```

## AST: conditional, dynamic-epistemic, hybrid and second-order

```{eval-rst}
.. autosummary::
   :toctree: _autosummary
   :nosignatures:

   Would
   Might
   Announce
   AnnounceDiamond
   Nominal
   At
   Dependence
   SlashedExists
   SecondOrderQuantifier
```

## AST: substructural and many-valued connectives

```{eval-rst}
.. autosummary::
   :toctree: _autosummary
   :nosignatures:

   Tensor
   With
   OPlus
   LinearImplies
   OfCourse
   One
   Top
   Zero
   Product
   Under
   Over
   WeakConjunction
   WeakDisjunction
   StrongConjunction
   StrongDisjunction
   LukNegation
   LukImplication
   LukEquivalence
```

## Normal forms, lambda calculus & unification

```{eval-rst}
.. autosummary::
   :toctree: _autosummary
   :nosignatures:

   to_nnf
   to_pnf
   to_cnf
   to_dnf
   to_tseitin_cnf
   skolemize
   is_horn
   has_lambdas
   eliminate_lambdas
   beta_reduce
   beta_reduce_step
   beta_eta_normalize
   eta_reduce
   reduce_trace
   resolve_lambda_scope
   unify
   apply_subst
```

## Import / export

Every importer inverts its source language's naming convention where it differs
from the kit's — TPTP and Prolog both spell a predicate lower-case and a
variable upper-case, so `carbon(A)` arrives as `Carbon(a)`. A name that is
legal in the source but not a legal kit token survives verbatim; run
{func}`~unicode_fol_kit.sanitize_names` over the result before rendering it
back to kit text.

{func}`~unicode_fol_kit.parse_prolog_clause` additionally asks the caller to
decide what a clause MEANS — the universally closed implication, or the
condition alone with the head's variables free (`mode="body"`). Those are
different formulas, so it will not choose for you. See
{doc}`guide/interoperability`.

```{eval-rst}
.. autosummary::
   :toctree: _autosummary
   :nosignatures:

   parse_tptp
   parse_tptp_formula
   load_tptp
   TptpFormula
   parse_tptp_problem
   load_tptp_problem
   TptpProblem
   TptpHeader
   parse_prover9
   parse_prover9_problem
   load_prover9
   Prover9Formula
   parse_prolog_clause
   parse_prolog_program
   load_prolog
   from_z3
   parse_smtlib
   load_smtlib
   to_casl_spec
   formula_to_casl
   parse_casl_spec
   CaslSpec
   to_tptp_ncl
   parse_latex
   latex_to_unicode
```

## Repairing a formula that will not parse

```{eval-rst}
.. autosummary::
   :toctree: _autosummary
   :nosignatures:

   repair_tptp_formula
   repair_tptp_problem
   repair_formula
   DialectRepairResult
```

## Classical reasoning

```{eval-rst}
.. autosummary::
   :toctree: _autosummary
   :nosignatures:

   prove
   refute
   to_clauses
   is_valid_resolution
   is_valid
   is_satisfiable
   get_model
   is_satisfiable_arith
   is_valid_arith
   get_model_arith
   to_z3_arith
   formulas_are_equivalent
   check_logical_entailment
   check_logical_entailment_vampire
   find_model
   find_countermodel
   is_satisfiable_finite
   is_valid_finite
   truth_table
   TruthTable
   is_tautology
   is_contradiction
   is_satisfiable_tt
```

## Proof systems

```{eval-rst}
.. autosummary::
   :toctree: _autosummary
   :nosignatures:

   Proof
   Line
   Subproof
   Justification
   ProofResult
   premise
   assume
   line
   flag
   FALSUM
   check_proof
   verify_proof
   render_fitch
   render_latex_fitch
   find_fitch_proof
   fitch_prove
   is_valid_fitch
   Sequent
   Derivation
   Comprehension
   SequentResult
   sequent
   derive
   axiom
   check_sequent_proof
   verify_sequent_proof
   render_sequent_proof
   check_lj_proof
   verify_lj_proof
   int_prove
   int_decide
   ResolutionStep
   ResolutionDerivation
   ResolutionCheckResult
   check_resolution_proof
   verify_resolution_proof
   render_resolution_proof
   tableau_closed
   is_valid_tableau
   prove_tableau
   tableau_model
   prove_tableau_detailed
   TableauProof
   check_tableau_proof
   check_entailment_tableau_detailed
   ill_prove
   ill_derivable
   check_ill_proof
   verify_ill_proof
   render_ill_proof
   ILLSequent
   ILLDerivation
   lambek_prove
   lambek_derivable
   check_lambek_proof
   verify_lambek_proof
   render_lambek_proof
   LambekSequent
   LambekDerivation
```

## Modal, temporal, epistemic & deontic logic

```{eval-rst}
.. autosummary::
   :toctree: _autosummary
   :nosignatures:

   KripkeModel
   satisfies_modal
   models_at
   reflexive_transitive_closure
   standard_translation
   qml_translate
   qml_is_valid
   qml_equivalent
   hybrid_is_valid
   announce
   box_announce
   diamond_announce
   reduce_announcements
   ActionModel
   product_update
   public_announcement_action
   common_knowledge_holds
   everybody_knows
   EnumSearchResult
   modal_enum_search
   modal_enum_countermodel
   kripke_model_to_dict
   kripke_model_from_dict
   BARCAN
   CONVERSE_BARCAN
```

## Many-valued, fuzzy, free, conditional & relevant logic

```{eval-rst}
.. autosummary::
   :toctree: _autosummary
   :nosignatures:

   kleene_value
   TruthMatrix
   matrix_value
   matrix_is_valid
   matrix_is_satisfiable
   matrix_entails
   K3_MATRIX
   LP_MATRIX
   FDE_MATRIX
   TNorm
   get_tnorm
   fuzzy_evaluate
   fuzzy_is_valid
   fuzzy_is_satisfiable
   fuzzy_get_model
   IntKripkeModel
   int_valid
   int_countermodel
   FreeModel
   free_satisfies
   free_holds
   NONDENOTING
   free_find_model
   free_countermodel
   free_is_valid
   free_entails
   CounterfactualModel
   cf_satisfies
   cf_countermodel
   cf_valid
   would
   might
   CENTERING_LEVELS
   RelevantModel
   rel_satisfies
   rel_countermodel
   rel_valid
   minimal_models
   minimal_entails
   circumscription_formula
   circumscription_entails_so
   team_satisfies
   team_models
   MAX_TEAM_SEARCH
   dependence_to_eso
   satisfies_so
   so_find_model
   so_find_countermodel
   so_is_satisfiable_finite
   so_is_valid_finite
```

## Model checking in a given structure

```{eval-rst}
.. autosummary::
   :toctree: _autosummary
   :nosignatures:

   Structure
   term_value
   satisfies
   models
   holds
   simplify_for_checking
   count_from_existential_chain
   expand_count
```

## Prover backends, portfolios & batch runs

The backend protocol is the extension point: implement
{class}`~unicode_fol_kit.ProverBackend`, register it, and every chain-driven
entry point can reach it.

```{eval-rst}
.. autosummary::
   :toctree: _autosummary
   :nosignatures:

   Verdict
   ProverBackend
   BackendUnavailable
   register_backend
   get_backend
   available_backends
   default_chain
   run_backend
   portfolio_prove
   Cvc5Backend
   Leo3Backend
   KripkeEnumBackend
   ClingoBackend
   MinizincBackend
   check_entailment_vampire_detailed
   extract_szs_status
   szs_to_verdict_fields
   TstpStep
   TstpDerivation
   parse_tstp_derivation
   batch_decide
```

## Isabelle/HOL: running it, and exporting to it

```{eval-rst}
.. autosummary::
   :toctree: _autosummary
   :nosignatures:

   find_isabelle
   isabelle_available
   IsabelleInstall
   IsabelleNotAvailable
   BuildResult
   isabelle_decide_modal
   isabelle_decide_fol
   isabelle_decide_counterfactual
   isabelle_decide_relevant
   check_theory
   ModalVerdict
   FolVerdict
   modal_axiom_names
   modal_faithfulness_theory
   intuitionistic_faithfulness_theory
   conditional_faithfulness_theory
   relevant_faithfulness_theory
   to_thf_modal
   to_isabelle_modal
   to_isabelle_relevant
   to_isabelle_ill
   ill_derivation_theory
   to_isabelle_lambek
   lambek_derivation_theory
   to_thf_matrix
   to_isabelle_matrix
   to_thf_matrix_entailment
   to_isabelle_matrix_entailment
```

## Evaluating generated formulas

```{eval-rst}
.. autosummary::
   :toctree: _autosummary
   :nosignatures:

   canonicalize
   exact_match
   validate
   is_wellformed
   validate_text
   ValidationReport
   formulas_are_identical
   match_predicates
   formulas_are_matched_identical
   align_symbols
   aligned_exact_match
   EquivalenceResult
   equivalent
   explain_countermodel
```

## Registries, at their definition site

```{eval-rst}
.. currentmodule:: unicode_fol_kit.semantics.matrix

.. autosummary::
   :nosignatures:

   MATRICES
```

```{eval-rst}
.. currentmodule:: unicode_fol_kit.semantics.tnorm

.. autosummary::
   :nosignatures:

   TNORMS
```

```{eval-rst}
.. currentmodule:: unicode_fol_kit.semantics.manyvalued

.. autosummary::
   :toctree: _autosummary
   :nosignatures:

   DESIGNATED
```

```{eval-rst}
.. currentmodule:: unicode_fol_kit.semantics.conditional

.. autosummary::
   :nosignatures:

   DEFAULT_MAX_WORLDS
```

```{eval-rst}
.. currentmodule:: unicode_fol_kit.fol.qml

.. autosummary::
   :toctree: _autosummary
   :nosignatures:

   QML_BRIDGES
```

```{eval-rst}
.. currentmodule:: unicode_fol_kit.hol.isabelle_modal

.. autosummary::
   :toctree: _autosummary
   :nosignatures:

   ISABELLE_TACTICS
```

## Errors

```{eval-rst}
.. currentmodule:: unicode_fol_kit

.. autosummary::
   :toctree: _autosummary
   :nosignatures:

   NamingError
   ParsingError
   CaslImportError
   ReductionLimitError
   TableauCheckError
```

## Structures and the structure evaluator

```{eval-rst}
.. currentmodule:: unicode_fol_kit.semantics

.. autosummary::
   :toctree: _autosummary
   :nosignatures:

   FiniteStructure
   structure_from_dict
   graph_to_structure
   evaluate_in_structure
   evaluate_detailed
   EvalResult
   UninterpretedSymbol
   UnsupportedNode
   BudgetExhausted
   evaluate
   entails
   ground_quantifiers
   GODEL
   LUKASIEWICZ
   PRODUCT
```

### Minimal models via ASP

`unicode_fol_kit.semantics.asp_models` is reached only by its own path — it
is not re-exported anywhere else. {func}`~unicode_fol_kit.semantics.asp_models.asp_minimal_models`
lets `clingo` enumerate models natively and filters them through
{mod}`~unicode_fol_kit.semantics.nonmonotonic`'s own, unmodified minimality
predicate; {func}`~unicode_fol_kit.semantics.asp_models.asp_find_model` is
its single-shot analogue. Both return the same
{class}`~unicode_fol_kit.semantics.tarski.Structure` type `minimal_models`
and `find_model` already return. See {doc}`guide/finite-domain`.

## Verifying and batch-checking definition sets

```{eval-rst}
.. currentmodule:: unicode_fol_kit.eval

.. autosummary::
   :toctree: _autosummary
   :nosignatures:

   Definitions
   check_theory
   TheoryReport
   check_satisfiable
   SatisfiabilityResult
   check_subsumption
   SubsumptionResult
   strictly_stronger
   StrictlyStrongerResult
   find_cycles
   CyclicDefinition
   dependency_graph
   unfold
   UnfoldDepthExceeded
   minimal_model_size
   MinimalModelResult
   generality_report
   GeneralityReport
   is_vacuous_specialisation
   VacuousSpecialisationResult
   check_definitions
   ChemBatchResult
   compute_fol_metrics
   datasets
```

## Chemistry: molecules as structures

`mol_to_structure` builds a structure from a SMILES string,
`parse_chemlog_tptp` reads a ChemLog definition, `to_chemlog_names` /
`to_kit_names` move a formula between the two naming conventions,
`rename_with_spans` / `to_chemlog_names_with_spans` do the same rename while
carrying a `SpanMap` (see "Source spans" above) across it, and
`StructureCache` keeps built structures for a whole run (see
{doc}`guide/batch-checking`).

```{eval-rst}
.. currentmodule:: unicode_fol_kit.chem

.. autosummary::
   :nosignatures:

   mol_to_structure
   CHEMLOG_SIGNATURE
   StructureCache
   StructureBuildError
   parse_chemlog_tptp
   to_chemlog_names
   to_kit_names
   to_chemlog_naming
   to_paper_naming
   rename_with_spans
   to_chemlog_names_with_spans
```

```{eval-rst}
.. currentmodule:: unicode_fol_kit.chem.interop

.. autosummary::
   :nosignatures:

   CHEMLOG_TO_KIT
   KIT_TO_CHEMLOG
```

```{eval-rst}
.. currentmodule:: unicode_fol_kit.chem.signature

.. autosummary::
   :nosignatures:

   CHEMLOG_TO_PAPER
   PAPER_TO_CHEMLOG
```

## Inductive logic programming

Structures in, a learning task out, and the learner's clause back — with the
two encoding traps that silently produce a perfect-scoring, meaningless
hypothesis refused rather than documented. See {doc}`guide/interoperability`.

```{eval-rst}
.. currentmodule:: unicode_fol_kit.ilp

.. autosummary::
   :nosignatures:

   IlpTask
   Example
   task_from_structures
   to_prolog_atom
   clause_to_formula
   hypothesis_to_formulas
   check_separation
   SeparationReport
   IlpEncodingError
```

## Probability

```{eval-rst}
.. currentmodule:: unicode_fol_kit.prob

.. autosummary::
   :nosignatures:

   ProbConstraint
   ProbBounds
   entailment_bounds
   ProbFact
   ProbProgram
   query
```

## Description logic (ALC)

```{eval-rst}
.. currentmodule:: unicode_fol_kit.dl

.. autosummary::
   :nosignatures:

   Concept
   Atomic
   Top
   Bottom
   Not
   And
   Or
   Exists
   ForAll
   TBox
   ABox
   nnf
   parse_concept
   parse_gci
   parse_manchester
   parse_manchester_axiom
   to_manchester
   concept_satisfiable
   concept_unsatisfiable
   subsumes
   abox_consistent
   concept_to_fol
   concept_to_modal
   tbox_to_fol
   abox_to_fol
   subsumption_to_fol
   ConceptSyntaxError
   ManchesterSyntaxError
```

## Discourse representation theory

```{eval-rst}
.. currentmodule:: unicode_fol_kit.drt

.. autosummary::
   :nosignatures:

   DRS
   Condition
   Pred
   Eq
   Neg
   Impl
   Card
   Part
   CARD_OPS
   fol_to_drs
   FolToDrsError
   parse_drs
   parse_sbn
   SBNMapping
   drs_to_fol
   resolve_anaphora
   Resolution
   ResolutionReport
   PRONOUN
   walk_boxes
   is_referent
   is_constant_name
   is_predicate_name
   DRSSyntaxError
   SBNSyntaxError
```

## Attempto Controlled English (via APE)

ACE text in, kit formulas out — driven through the external
[APE](https://github.com/Attempto/APE) parser (LGPL, never vendored; see
`unicode_fol_kit.ace.runner`'s module docstring for discovery and for what
each outcome class means). Three routes share one vocabulary, pinned against
each other by a Z3 differential over the recorded corpus: `ace_to_fol`
(Attempto's own TPTP through the kit's reader), `ace_to_drs` (APE's DRS read
1:1 and mapped onto the classical `drt` core, every condition reported) and
`ace_to_formula` (straight to one kit formula — ACE's four modal boxes become
□/◇/Ⓞ/Ⓟ, a wh-question an open formula, a yes/no question a closed one whose
interrogative force survives on `kind`). Plurals and cardinalities carry
real counting force since ACE-4/5: groups land on the `drt` core's
`Card`/`Part` conditions (collective reading), the maximality of
`exactly`/`at most` becomes a counting quantifier on the formula route, and
`1 + 2 = 3` translates to kit arithmetic decidable by `is_valid_arith`.
Since ACE-6 the pipeline also runs backwards: `drs_to_ace` verbalizes a kit
DRS as ACE text plus its user lexicon, `ace_round_trip` closes the loop
through APE with a Z3 verdict, and `chem_ulex` speaks the ChemLog signature
("a carbon", "bonds", "aromatic"). `formula_to_ace` extends the reverse
direction to FORMULAS: `drt.fol_to_drs` rebuilds the box structure of any
formula in the standard translation's image (refusing the rest by name),
then the verbalizer takes over — the two exceptions are the "is this
expressible as ACE?" verdict.

```{eval-rst}
.. currentmodule:: unicode_fol_kit.ace

.. autosummary::
   :nosignatures:

   ape_available
   run_ape
   ace_to_fol
   ace_to_drs
   ace_to_formula
   ace_coverage
   map_ace_drs
   ace_drs_to_formula
   parse_ape_drs
   condition_statistics
   drs_to_ace
   formula_to_ace
   ace_round_trip
   chem_ulex
   ace_kit_name
   ApeResult
   ApeMessage
   CoverageRow
   DrsMapping
   ConditionReport
   AceFormula
   AceText
   AceRoundTrip
   AceDrs
   AceVar
   AceNamed
   AceInt
   AceReal
   AceString
   AceExpr
   AceTermApp
   AceAtom
   AceNeg
   AceNaf
   AceImpl
   AceOr
   AceModal
   AceQuestion
   AceCommand
   AceCondList
   AceError
   ApeUnavailableError
   AceParseError
   AceTptpUnsupportedError
   AceTptpUnreadError
   AceDrsUnreadError
   AceUnsupportedError
   AceVerbalizationError
```

## HETS, DOL and comorphisms

```{eval-rst}
.. currentmodule:: unicode_fol_kit.hets

.. autosummary::
   :nosignatures:

   hets_available
   discover_hets_url
   HetsClient
   HetsContainer
   HETS_IMAGE
   register_hets_comorphisms
   HETS_EDGE_PREFIX
   to_dol_library
   DolSpec
```

```{eval-rst}
.. currentmodule:: unicode_fol_kit.comorphism

.. autosummary::
   :nosignatures:

   Comorphism
   ComorphismRegistry
   register_comorphism
   TranslationResult
   DEFAULT_REGISTRY
```

## Further HOL exports and deep embeddings

```{eval-rst}
.. currentmodule:: unicode_fol_kit.hol

.. autosummary::
   :toctree: _autosummary
   :nosignatures:

   to_thf_fol
   to_isabelle_fol
   to_thf_msfol
   to_isabelle_msfol
   to_thf_so
   to_isabelle_so
   to_thf_k3lp
   to_isabelle_k3lp
   to_thf_k3lp_entailment
   to_isabelle_k3lp_entailment
   to_thf_intuitionistic
   to_isabelle_intuitionistic
   to_thf_modal_full
   thf_full_definitions
   thf_full_frame_axioms
   isabelle_modal_theory
   modal_to_deep
   int_to_deep
   counterfactual_to_deep
   rel_to_deep
   gmt_translate
   gmt_is_s4_valid
   gmt_validity_matches_int_valid
   BRIDGES
   SYSTEMS
   DEFAULT_METHODS
```

## Optional prover backends and modal tableaux

```{eval-rst}
.. currentmodule:: unicode_fol_kit.atp

.. autosummary::
   :toctree: _autosummary
   :nosignatures:

   EProverBackend
   eprover_available
   check_entailment_eprover_detailed
   ZipperpositionBackend
   zipperposition_available
   TweeBackend
   twee_available
   check_entailment_twee_detailed
   check_twee_proof
   TweeCheckResult
   NanocopBackend
   nanocop_available
   to_nanocop
   HetsBackend
   FiniteDomainProblem
   fragment_check
   structure_from_solution
   verify_model
   clingo_available
   to_asp
   minizinc_available
   to_minizinc
   modal_tableau_closed
   is_modal_valid
   modal_decide
   modal_prove
   modal_countermodel
   TableauStep
   TableauClosure
   ArithEnv
   degree_expr
```

## Repair internals and other fol-level types

```{eval-rst}
.. currentmodule:: unicode_fol_kit.fol

.. autosummary::
   :toctree: _autosummary
   :nosignatures:

   RepairResult
   Issue
   ProblemRepairResult
   ProblemRepairEntry
   TptpRepairError
   PrologParsingError
   SimplifyResult
   qml_axioms
```

## Subpackage modules

The module view of the same code: each entry documents the module's own
docstring — the design decisions and the reasons behind them — and, recursively,
its submodules.

```{eval-rst}
.. currentmodule:: unicode_fol_kit

.. autosummary::
   :toctree: _autosummary
   :recursive:

   dl
   semantics.matrix
   semantics.tnorm
   semantics.free_logic
   semantics.conditional
   semantics.dynamic_epistemic
   semantics.nonmonotonic
   semantics.structures
   semantics.model_eval
   semantics.asp_models
   atp.finite_domain
   atp.clingo_backend
   atp.minizinc_backend
   atp.modal_tableau
   hol.isabelle_runner
   chem
   fol.prolog_input
   fol.dialect_repair
   eval.chem_batch
   eval.datasets
   hets
   comorphism
   drt
   ace
   ilp
   prob
   mcp.syntax_spec
```
