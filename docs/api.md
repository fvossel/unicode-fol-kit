# API reference

Auto-generated from the package docstrings, and **complete**: every name in
`unicode_logic_kit.__all__` and in each subpackage's `__all__` appears in exactly
one table below, linking to its full signature and documentation. A test
(`tests/test_api_reference_complete.py`) enforces that, so a new public name
cannot ship undocumented.

Names are grouped by what they are FOR, not by which module they live in — the
module view is the last section. A name re-exported at top level is documented
under that path; a name that exists only inside a subpackage is documented
there. Two deliberate exceptions:

- Fifteen names appear twice, under different paths, because they are
  **different objects** that happen to share a name: `check_theory`
  ({func}`unicode_logic_kit.check_theory` builds and runs an Isabelle theory,
  {func}`unicode_logic_kit.eval.check_theory` audits a set of definitions), the
  description-logic concept constructors `And`/`Or`/`Not`/`Top`/`Nominal`,
  which are description-logic concepts rather than formula nodes, and the nine
  `external_*` functions, which `dl` (HermiT) and `hets` (FaCT++) each define.
- Fourteen dict registries and naming maps are documented at their **definition
  site** rather than at the re-export path, because that is the only place
  their documentation exists: a name imported into a module carries no
  attribute comment there, and the reference would fall back to describing the
  `dict` constructor.

## Parsing & the AST

```{eval-rst}
.. currentmodule:: unicode_logic_kit

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
   nonempty_sort_axioms
   sort_membership_axioms
   sort_axioms
   subsort_axioms
   signature_axioms
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
.. currentmodule:: unicode_logic_kit

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
   inventory_of
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
   EverybodyKnows
   DistributedKnowledge
   CommonKnowledge
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

## AST: conditional, dynamic-epistemic, hybrid and higher-order

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
   Down
   Dependence
   SlashedExists
   SecondOrderQuantifier
   PredicateTerm
```

`SecondOrderQuantifier` binds a predicate variable; `PredicateTerm` is the step
above it — a predicate standing in ARGUMENT position, which is what makes a
formula third-order. What each argument slot holds is not in the surface syntax
and is inferred across a whole theory by `analyse_signatures`, which returns a
`Signatures` and raises `MixedSlotError` for a slot used once for an individual
and once for a property, and `NestedPropertySlotError` for a slot that would hold
a predicate which itself takes a property (a fourth-order typing).

```{eval-rst}
.. autosummary::
   :toctree: _autosummary
   :nosignatures:

   analyse_signatures
   Signatures
   MixedSlotError
   NestedPropertySlotError
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
{func}`~unicode_logic_kit.sanitize_names` over the result before rendering it
back to kit text.

{func}`~unicode_logic_kit.parse_prolog_clause` additionally asks the caller to
decide what a clause MEANS — the universally closed implication
(`mode="clause"`, the default), or the condition alone with the head's
variables free (`mode="body"`). Those are different formulas, so state the one
you mean. See {doc}`guide/interoperability`.

{func}`~unicode_logic_kit.formula_to_prolog_clause` is the return leg: a
formula built to look like a fact or a definite/normal clause renders back
out as Prolog text, `parse_prolog_clause`'s own `mode="clause"` reading run
in reverse; {func}`~unicode_logic_kit.formula_to_prolog_program` does the same
for several clauses at once. Both refuse — by name, via
{class}`~unicode_logic_kit.fol.PrologExportError` — a formula outside the
narrow accepted fragment rather than approximating it.

Prover9's `op(precedence, type, symbol)` operator declarations are applied to
formulas parsed after them, not just recognised and skipped — see
{doc}`guide/interoperability` for exactly which placements splice into the
grammar, which are refused by name (redeclaring a built-in, or a malformed
directive), and which are accepted but left harmlessly inert.

TF0 (typed TPTP) is its own guide section — see {doc}`guide/interoperability`
— because a many-sorted formula there gets a genuine `tff` type per
sort/symbol instead of the classical route's guard-predicate encoding.
{func}`~unicode_logic_kit.generate_tff_arith_problem` is `generate_tff_problem`'s
single-numeric-sort sibling — see {doc}`guide/classical-reasoning`'s "Native
typed arithmetic for Vampire/E (TFA)" section: every individual lives in ONE
caller-chosen `$int`/`$real` sort (mirroring `is_valid_arith`'s own design),
which is what lets Vampire/E activate their native arithmetic reasoning on
`+ - * /` and `< > ≤ ≥` — the classical `fof` route, and TF0's own many-sorted
route, cannot.

{func}`~unicode_logic_kit.parse_qmltp` reads the QMLTP library's own `#box`/
`#dia` extension of `fof` syntax and its per-logic/per-domain status header;
see {doc}`guide/quantified-modal`.

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
   parse_tff_problem
   load_tff_problem
   generate_tff_problem
   generate_tff_arith_problem
   parse_prover9
   parse_prover9_problem
   load_prover9
   Prover9Formula
   parse_prolog_clause
   parse_prolog_program
   load_prolog
   formula_to_prolog_clause
   formula_to_prolog_program
   from_z3
   parse_smtlib
   load_smtlib
   to_smtlib
   to_casl_spec
   formula_to_casl
   parse_casl_spec
   CaslSpec
   to_tptp_ncl
   parse_qmltp_formula
   parse_qmltp
   load_qmltp
   QmltpFormula
   QmltpHeader
   QmltpStatus
   QmltpProblem
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
   is_size_exhaustive
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

Every modal route — the standard translation, the labelled tableau, the
finite-frame enumerator, natural deduction, the hybrid translation and the
higher-order embeddings — reads ONE frame table,
{mod}`unicode_logic_kit.fol.frames`: its `FRAMES` names the systems (24 of
them), `FRAME_CONDITIONS` describes each condition together with the axiom it
corresponds to (a correspondence brute-forced over every frame on up to three
worlds), and `modal_axiom` builds the schema of a named axiom, literature
aliases included. Both registries are documented at their definition site
below. A Scott–Lemmon spec such as `"G(1,1,1,1)"` is accepted
wherever a frame name is. What a route cannot express soundly it refuses with
`UnsupportedFrameCondition` rather than ignoring.

The first-order route's side conditions are explicit. A formula's translation
mentions several accessibility relations (`R`, `T`, `N`, `D` and one per agent),
and {func}`unicode_logic_kit.fol.modal_translation.frame_axioms` returns the frame
axioms for exactly those, and for each sorted constant `c:S` the axiom that it
lies in `S` at every world, while
{func}`unicode_logic_kit.fol.modal_translation.relations_used` names the relations.
{func}`~unicode_logic_kit.hybrid_is_valid` and {func}`~unicode_logic_kit.down_is_valid`
take `systems=` and `temporal_closure=` and assert them, which is what brings
them into line with {func}`~unicode_logic_kit.qml_is_valid`. The two helpers live
in the module and are not re-exported at the top level, so they have no row in
the table; the module section at the end of this page documents them. The
propositional standard translation and the propositional Kripke evaluator both
refuse an equality atom by name; `qml_translate` is the route where `=` is rigid
identity. The translations are catalogued, with their guarantees, in
{doc}`guide/logic-graph`.

```{eval-rst}
.. autosummary::
   :toctree: _autosummary
   :nosignatures:

   KripkeModel
   satisfies_modal
   models_at
   reflexive_transitive_closure
   ctl_ex
   ctl_af
   ctl_eg
   ctl_au
   FuzzyKripkeModel
   satisfies_fuzzy_modal
   standard_translation
   qml_translate
   qml_is_valid
   qml_equivalent
   hybrid_is_valid
   down_is_valid
   modal_axiom
   UnsupportedFrameCondition
   announce
   box_announce
   diamond_announce
   reduce_announcements
   ActionModel
   product_update
   public_announcement_action
   common_knowledge_holds
   everybody_knows
   distributed_knowledge_holds
   EnumSearchResult
   modal_enum_search
   modal_enum_countermodel
   kripke_model_to_dict
   kripke_model_from_dict
   down_decide
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
   dependence_holds_eso
   satisfies_so
   satisfies_to
   holds_to
   so_find_model
   so_find_countermodel
   so_is_satisfiable_finite
   so_is_valid_finite
   CandidateBoundExceeded
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
{class}`~unicode_logic_kit.ProverBackend`, register it, and every chain-driven
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
   z3_relevant_premises
   IncrementalSession
   portfolio_prove
   Cvc5Backend
   Leo3Backend
   KripkeEnumBackend
   ClingoBackend
   MinizincBackend
   LtlTableauBackend
   IntBackend
   LambekBackend
   IllBackend
   RelevantBackend
   HybridBackend
   check_entailment_vampire_detailed
   extract_szs_status
   szs_to_verdict_fields
   TstpStep
   TstpDerivation
   parse_tstp_derivation
   relevant_premises_from_tstp
   to_tstp
   TstpStepResult
   TstpCheckResult
   check_tstp_derivation
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
   isabelle_decide_free
   check_theory
   ModalVerdict
   FolVerdict
   modal_axiom_names
   modal_faithfulness_theory
   intuitionistic_faithfulness_theory
   conditional_faithfulness_theory
   relevant_faithfulness_theory
   qml_deep_faithfulness_theory
   to_thf_modal
   to_isabelle_modal
   to_thf_conditional
   to_isabelle_conditional
   isabelle_conditional_theory
   to_thf_relevant
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
   explain_proof
```

## Generating exercises

```{eval-rst}
.. autosummary::
   :toctree: _autosummary
   :nosignatures:

   ValidInvalidPair
   generate_valid_invalid_pair
   EntailmentExercise
   generate_entailment_with_proof
   ModelSizeExercise
   generate_theory_with_model_size
```

## Registries, at their definition site

```{eval-rst}
.. currentmodule:: unicode_logic_kit.semantics.matrix

.. autosummary::
   :nosignatures:

   MATRICES
```

```{eval-rst}
.. currentmodule:: unicode_logic_kit.semantics.tnorm

.. autosummary::
   :nosignatures:

   TNORMS
```

```{eval-rst}
.. currentmodule:: unicode_logic_kit.semantics.manyvalued

.. autosummary::
   :toctree: _autosummary
   :nosignatures:

   DESIGNATED
```

```{eval-rst}
.. currentmodule:: unicode_logic_kit.semantics.conditional

.. autosummary::
   :nosignatures:

   DEFAULT_MAX_WORLDS
```

```{eval-rst}
.. currentmodule:: unicode_logic_kit.atp.tstp_check

.. autosummary::
   :nosignatures:

   VAMPIRE_CLAUSIFICATION_RULES
   VAMPIRE_CHECKED_RULES
   EPROVER_CLAUSIFICATION_RULES
   EPROVER_CHECKED_RULES
```

The third-order evaluator ranges over each bound symbol's argument SIGNATURE
rather than its arity, so what one slot can hold is its own question:
`slot_values` answers it, `all_interpretations` yields every interpretation of a
signature, and `interpretation_count` says how many there would be without
enumerating any.

```{eval-rst}
.. currentmodule:: unicode_logic_kit.semantics.thirdorder

.. autosummary::
   :toctree: _autosummary
   :nosignatures:

   slot_values
   all_interpretations
   interpretation_count
```

```{eval-rst}
.. currentmodule:: unicode_logic_kit.fol.qml

.. autosummary::
   :toctree: _autosummary
   :nosignatures:

   QML_BRIDGES
```

```{eval-rst}
.. currentmodule:: unicode_logic_kit.fol.frames

.. autosummary::
   :toctree: _autosummary
   :nosignatures:

   FRAMES
   FRAME_CONDITIONS
   MODAL_AXIOMS
   AXIOM_ALIASES
   resolve_frame
   geach_axiom
   holds_on_finite_frame
   unguarded_frame_axiom
```

```{eval-rst}
.. currentmodule:: unicode_logic_kit.hol.isabelle_modal

.. autosummary::
   :toctree: _autosummary
   :nosignatures:

   ISABELLE_TACTICS
```

## Errors

```{eval-rst}
.. currentmodule:: unicode_logic_kit

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
.. currentmodule:: unicode_logic_kit.semantics

.. autosummary::
   :toctree: _autosummary
   :nosignatures:

   FiniteStructure
   structure_from_dict
   graph_to_structure
   IllegalStructureError
   check_structure
   structure_violations
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

`unicode_logic_kit.semantics.asp_models` is reached only by its own path — it
is not re-exported anywhere else. {func}`~unicode_logic_kit.semantics.asp_models.asp_minimal_models`
lets `clingo` enumerate models natively and filters them through
{mod}`~unicode_logic_kit.semantics.nonmonotonic`'s own, unmodified minimality
predicate; {func}`~unicode_logic_kit.semantics.asp_models.asp_find_model` is
its single-shot analogue. Both return the same
{class}`~unicode_logic_kit.semantics.tarski.Structure` type `minimal_models`
and `find_model` already return. See {doc}`guide/finite-domain`.

## Verifying and batch-checking definition sets

```{eval-rst}
.. currentmodule:: unicode_logic_kit.eval

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
   ConverseDeclaration
   validate_converses
   converse_axioms
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
.. currentmodule:: unicode_logic_kit.chem

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
.. currentmodule:: unicode_logic_kit.chem.interop

.. autosummary::
   :nosignatures:

   CHEMLOG_TO_KIT
   KIT_TO_CHEMLOG
```

```{eval-rst}
.. currentmodule:: unicode_logic_kit.chem.signature

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
.. currentmodule:: unicode_logic_kit.ilp

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
.. currentmodule:: unicode_logic_kit.prob

.. autosummary::
   :nosignatures:

   ProbConstraint
   ProbBounds
   entailment_bounds
   ProbFact
   ProbProgram
   query
```

## Description logic (ALCHQ)

ALCHQ ({mod}`unicode_logic_kit.dl.tableau`) refuses inverse roles and nominals (I, O)
by name; {mod}`unicode_logic_kit.dl.owl_reasoner` decides the full ALCHQ+I+O
fragment via an external, HermiT-backed reasoner (owlready2, optional
`[owl]` extra), mirroring every `dl.tableau` function's own reduction under
an `external_` prefix.

The first-order image of a knowledge base is split on purpose. A `TBox` holds the
concept inclusions *and* the role box, but `tbox_to_fol` renders only the
inclusions, so it raises `RoleBoxOmittedError` for a TBox that has a role box
unless `concept_inclusions_only=True` says that is intended. `kb_to_fol` is the
supported entry point: it returns a `KnowledgeBaseFOL` with the knowledge base as
one formula and the role-box axioms **separately**, to be passed as premises
(`premises`, `tbox_premises`), never conjoined into the formula.
`concept_to_fol`, `subsumption_to_fol` and `abox_to_fol` render exactly what
they are given, so each is an answer about the empty knowledge base. The
convention is the one every translation in {doc}`guide/logic-graph` follows.

Each side axiom is a `SideAxiom`, carrying the OWL 2 keyword it came from, so
`kb.axioms_of_kind("TransitiveObjectProperty")` is a question with an answer;
`kb.axioms` is the bare-formula view of the same one field. Which axiom kinds
the two routes handle, and how, is one table — `dl.tableau._AXIOM_KINDS`. An
axiom kind the in-house tableau has no rule for is refused BY NAME, by
`UnsupportedAxiomError`, from `concept_satisfiable`/`abox_consistent` and so
from everything that reduces to them; the builders `TBox.add_*`/`ABox.assert_*`
accept every kind, because a TBox is what a parser fills from a file.

A `TBox` carries the whole OWL 2 object property box: role inclusions and
transitivity (`add_role_inclusion`, `add_transitive_role`), role equivalence
and disjointness (`add_equivalent_roles`, `add_disjoint_roles`), inverse-property
pairs (`add_inverse_roles`), property chains (`add_role_chain`) and the six
remaining characteristics (`add_symmetric_role`, `add_asymmetric_role`,
`add_reflexive_role`, `add_irreflexive_role`, `add_functional_role`,
`add_inverse_functional_role`). The in-house tableau decides asymmetry,
irreflexivity, role disjointness (one clash condition each) and functionality
(internalised as the GCI `⊤ ⊑ ≤1 P.⊤`); it refuses inverse pairs, symmetric
roles, reflexive roles, inverse-functionality and property chains BY NAME, each
message saying why and what to use instead. `rbox_to_fol` renders all of them,
so `kb_to_fol` + `api.prove` and the external `external_*` reasoner answer what
the tableau will not. A role-box builder handed something that is not a usable
role in that position — a tuple where a chain belongs, an `InverseRole` where a
plain name belongs, or one of the four OWL 2 built-in property names — raises
`RoleExpressionError` on the call that is wrong. `add_role_domain` /
`add_role_range` store `ObjectPropertyDomain`/`ObjectPropertyRange` natively
rather than as the GCIs they are equivalent to, because their FOL image is the
direct `∀x ∀y (P(x, y) → C(x))` sentence and because `to_owl_functional` must
round-trip the axiom to itself; the tableau decides them by internalising those
GCIs, so no new rule.

`HasValue(role, individual)` (`∃r.{a}`, OWL's `ObjectHasValue`) is a nominal in
disguise, and the in-house tableau REFUSES it, by name (`UnsupportedConceptError`),
wherever it occurs, as it refuses a bare `Nominal`: it gives a generated node an
edge back to a named one, which subset blocking does not cover (the module
docstring of `dl.tableau` has the two-axiom counterexample). Its FOL image is the
ground atom `r(x, a)`, the one-point reduction of `∃y (r(x, y) ∧ y = a)`, and
that image with `api.prove`, or `dl.external_*` (HermiT), decides it.
`ABox.assert_same` and `assert_negative_role` are the two ABox assertions that
complete the OWL 2 set: sameness is decided by node merging before any rule
runs, a negative role assertion by a clash condition over forbidden edges, which
it refuses on a NON-SIMPLE role by name since the tableau never materialises a
transitive role's derived edges.

The data half of OWL 2 — the second sort — is stored and translated, and the
in-house tableau refuses it by name. The restrictions are `DataExists`,
`DataForAll`, `DataHasValue`, `DataAtLeast` and `DataAtMost`; their second
argument is a data range (`Datatype`, `DatatypeRestriction`, `DataOneOf`,
`DataComplementOf`, `DataIntersectionOf`, `DataUnionOf`) over `Literal` values.
A `TBox` gets `add_data_property_inclusion`, `add_equivalent_data_properties`,
`add_disjoint_data_properties`, `add_functional_data_property`,
`add_data_property_domain`, `add_data_property_range` and
`add_datatype_definition` (a datatype has one definition and the definitions
are acyclic, OWL 2 §9.4: a second one or a cycle, direct or indirect, is
refused by name); an `ABox` gets `assert_data` and
`assert_negative_data`. Every one is a row of `dl.tableau._AXIOM_KINDS` with
`layer="data"`, and `concept_satisfiable`/`abox_consistent`/`classify` raise
`UnsupportedAxiomError` (an axiom) or `UnsupportedConceptError` (a concept) for
it, as does `dl.owl_reasoner`; HermiT is not wired to it either. What
answers is the FOL image, and the facets are decided by `atp.z3_arith`.

That image is a *guarded one-sorted* theory, not MSFOL: two reserved predicates,
`OWL_THING` (`OwlThing`) and `OWL_DATA` (`OwlData`), stand for the two domains,
a datatype is a unary predicate, a data property a binary one, and a literal a
term (the number itself for an exact-number literal, a constant named by its OWL
text otherwise; `xsd:float`/`xsd:double` literals are refused, because their
value space is not the exact numbers', and so are `xsd:language`, `xsd:Name`,
`xsd:NCName` and `xsd:NMTOKEN`, whose lexical spaces the kit does not validate;
an `xsd:token` or `xsd:normalizedString` literal is the `xsd:string` value of its
whitespace-processed text). The two sorts are kept apart by
**side axioms** — `OwlThing` and `OwlData` disjoint and both non-empty, every
data property typed `OwlThing → OwlData`, the datatype lattice, literal
distinctness — so `kb_to_fol` is sound for the two-sorted question only if they
are *premises*. To ask it, pass `kb.premises` (or `kb.tbox_premises` for a
question about the terminology), never `kb.formula` alone, and let the bundle
build the goal: `kb.subsumption_goal(sub, sup)`, `kb.unsatisfiability_goal(concept)`
and `kb.instance_goal(individual, concept)` relativise it the way `kb.separation`
says. The side axioms are derived from the names the knowledge base uses, so hand
the concepts you will ask about to `kb_to_fol(tbox, abox, query=[...])` (their
vocabulary joins the knowledge base's, and a data restriction in the query makes
the image two-sorted even for a TBox with no data layer); a goal over a name the
bundle does not cover is refused by name (`UnsupportedDatatypeError`), not
answered wrongly. The registry edge `alc → fol` refuses a concept with a data
restriction for the same reason. (A hand-built goal needs
`subsumption_to_fol(sub, sup, object_sort=True)`.)
`kb.separation == "two-sorted"` says the knowledge base was built that way; every
GCI of its `formula` is already restricted to `OwlThing`, which is not
decoration — without it `⊤ ⊑ {a}` would also range over data values and make an
OWL-consistent knowledge base inconsistent. `separation="data-lattice"` keeps
the datatype facts without the separation, which for that very reason is not
sound for a knowledge base with a data layer (the goal methods refuse such a
bundle), and a knowledge base with no data layer is byte-for-byte what it was. One name is ONE predicate, so a name used
both as an object property and a data property, or both as a class and a
datatype, would be conflated and change what follows: OWL 2 DL forbids both, and
`kb_to_fol`, `data_sort_axioms`, `databox_to_fol` and `abox_to_fol` refuse it by
name with `UnsupportedDatatypeError` (rename one of the two). The image is sound — every OWL model
expands to a model of it — and deliberately not complete: a facet is an
uninterpreted comparison for `api.prove` (use `atp.z3_arith.is_valid_arith` for
facet entailment over integers or reals), a literal is typed only by the
datatype it was written with, and the number of values in a value space is not
stated. So `proved` transfers to OWL 2 and `refuted` does not:
`kb.refutation_is_decisive` is `False` exactly when there is a data layer.
`databox_to_fol`, `data_sort_axioms` and `datarange_to_fol` render the three
parts on their own. The name rule above looks only at what one call is given,
so boxes rendered one call at a time and conjoined by hand escape it;
`check_kb_names(*parts)` runs it over the union of several `TBox`, `ABox` and
`KnowledgeBaseFOL` pieces.

`parse_owl_functional` is strict: it raises on the first construct outside the
fragment, so one `HasKey` in a 4041-axiom ontology yields no TBox at
all. `parse_owl_functional_axioms` is the per-axiom reader for a real document
— one pass, recovering at axiom boundaries — returning an `OwlFunctionalResult`
with the TBox/ABox it could build, one `RefusedAxiom` per axiom it could not
(keyword, position, source text, reason), one `ConsumedAxiom` per axiom it read
and found to carry no logical content (an annotation-property axiom, a
tautological inclusion into `owl:topObjectProperty`: reported, so that they do
not vanish from a census), `ok`, `refused_keywords` and `to_kb()`.
It recovers from `OwlFunctionalUnsupportedError` (valid OWL 2, outside this
fragment) and from nothing else: malformed input still raises, because
recovering from an unbalanced paren could drop arbitrary content (and a class
expression nested about a thousand levels deep is a `RecursionError`). Both
OWL readers refuse a built-in datatype name where a class is wanted and
`owl:Thing`/`owl:Nothing` where a data range is wanted, and the Functional-Syntax
reader also refuses a literal with no first-order term (`xsd:float`/`xsd:double`,
`xsd:language`/`xsd:Name`/`xsd:NCName`/`xsd:NMTOKEN`, a decimal of more than 15
significant digits) as a `RefusedAxiom` keyed by its datatype, so an axiom that is `accepted` is one
`to_kb()` can render — though `to_kb()` may still refuse the knowledge base as a
whole (see the name rule above). The strict `parse_owl_functional` drops the
annotation-property axioms and the tautological property inclusions without a
report; `parse_owl_functional_axioms` lists them in `consumed`.

One limit worth knowing before printing an image that mentions an individual:
the kit decides predicate-versus-term by the first character's case, so an
upper-case individual name — the norm for an OWL IRI — prints as itself and does
not read back as the same formula. `Alice = Bob` does not parse at all;
`HasStateOfMatter(x, Liquid)` parses only as third-order, with `Liquid` as a
`PredicateTerm` rather than a `Constant`. The AST is sound either way, and the
`dl` routes that never go through text (the tableau, and `api.prove` over
`kb_to_fol`'s nodes) are unaffected.

```{eval-rst}
.. currentmodule:: unicode_logic_kit.dl

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
   AtLeast
   AtMost
   InverseRole
   Nominal
   HasValue
   DataExists
   DataForAll
   DataHasValue
   DataAtLeast
   DataAtMost
   Literal
   DataRange
   Datatype
   DatatypeRestriction
   DataOneOf
   DataComplementOf
   DataIntersectionOf
   DataUnionOf
   TBox
   ABox
   Classification
   nnf
   parse_concept
   parse_gci
   parse_manchester
   parse_manchester_axiom
   parse_manchester_data_range
   parse_manchester_literal
   to_manchester_data_range
   to_manchester
   parse_manchester_role_axiom
   role_axiom_to_manchester
   parse_owl_functional
   parse_owl_functional_axioms
   parse_owl_functional_class_expression
   to_owl_functional
   to_owl_functional_class_expression
   OwlFunctionalResult
   RefusedAxiom
   ConsumedAxiom
   concept_satisfiable
   concept_unsatisfiable
   subsumes
   abox_consistent
   instance_check
   instance_retrieval
   realize
   realize_all
   classify
   concept_to_fol
   concept_to_modal
   tbox_to_fol
   rbox_to_fol
   abox_to_fol
   subsumption_to_fol
   databox_to_fol
   data_sort_axioms
   check_kb_names
   datarange_to_fol
   OWL_THING
   OWL_DATA
   kb_to_fol
   KnowledgeBaseFOL
   SideAxiom
   RoleBoxOmittedError
   RoleExpressionError
   ConceptSyntaxError
   ManchesterSyntaxError
   OwlFunctionalSyntaxError
   OwlFunctionalUnsupportedError
   owl_reasoner_available
   external_concept_satisfiable
   external_concept_unsatisfiable
   external_subsumes
   external_equivalent
   external_abox_consistent
   external_instance_check
   external_instance_retrieval
   external_realize
   external_realize_all
   OwlReasonerError
   NonSimpleRoleError
   UnsupportedConceptError
   UnsupportedAxiomError
   UnsupportedDatatypeError
```

## Discourse representation theory

```{eval-rst}
.. currentmodule:: unicode_logic_kit.drt

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
`unicode_logic_kit.ace.runner`'s module docstring for discovery and for what
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
expressible as ACE?" verdict. Since ACE-7 the backward direction also covers
the modal/deontic fragment: `fol_to_modal_drs` recognizes a modality
wrapping a whole formula or nested in a duplex's consequent,
`modal_formula_to_ace`/`modal_drs_to_ace` verbalize it (refusing a modal box
whose single clause is not the event-anchored verb clause the modality
actually attaches to), and `modal_ace_round_trip` closes the loop through
APE, judged by `eval.equivalence.equivalent` (a modal formula has no direct
Z3 export).

```{eval-rst}
.. currentmodule:: unicode_logic_kit.ace

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
   fol_to_modal_drs
   modal_drs_to_ace
   modal_formula_to_ace
   modal_ace_round_trip
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
   ModalBox
   ModalImpl
   ModalAceRoundTrip
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

`unicode_logic_kit.hets.owl_backend` adds a second, independent external OWL 2
DL reasoner (FaCT++ via the server's `Fact` prover), mirroring
`dl.owl_reasoner`'s function-per-namesake shape over the same ALCHQ+I+O
fragment.

```{eval-rst}
.. currentmodule:: unicode_logic_kit.hets

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
   to_dol_library_from_modal
   sanitize_modal_identifiers
   hets_owl_available
   external_concept_satisfiable
   external_concept_unsatisfiable
   external_subsumes
   external_equivalent
   external_abox_consistent
   external_instance_check
   external_instance_retrieval
   external_realize
   external_realize_all
   HetsOwlError
```

### Reading a real HETS translation of an ontology

HETS 0.108.0's `GET /dg` serialises OWL axiom strings through Haskell's
`show`, which emits a DECIMAL escape for every character above 127
(`"Verdi\226\128\153s Requiem"` for `"Verdi’s Requiem"`). That is not JSON, so
the whole development graph is unreadable for any library with one non-ASCII
annotation. {func}`~unicode_logic_kit.hets.repair_haskell_json` recovers it —
losslessly, because the emitter is known and enumerable — and
{meth}`~unicode_logic_kit.hets.HetsClient.dg` applies it ONLY after `json.loads`
has already failed, so a body the standard library accepts is never touched.
{meth}`~unicode_logic_kit.hets.HetsClient.dg_raw` returns the body untouched.

The text `GET /theory` returns for a TPTP comorphism is not a TPTP problem
either: HETS prefixes it with a DOL `logic TPTP.FOF` line and a CASL
`%{ ... }%` signature block, neither of which is TPTP syntax.
{func}`~unicode_logic_kit.hets.strip_hets_theory_header` splits the two and
{meth}`~unicode_logic_kit.hets.HetsClient.theory_tptp` fetches it already
stripped; `parse_tptp` refuses the unstripped text by name rather than
learning a comment form that would make it accept a CASL theory and answer
with an empty formula list.

{func}`~unicode_logic_kit.hets.hets_symbol_table` joins HETS' mangled TPTP
symbols (`pred_https_u_u_uopenenergyplatform_uorg_uontology_uoeo_uOEO_00000072`)
back onto the OWL entities, IRIs and `rdfs:label`s they came from, and
{func}`~unicode_logic_kit.hets.untranslated_axioms` names the axioms a
translation dropped. Both are pure functions over a `/dg` dict and a TPTP
string. {func}`~unicode_logic_kit.hets.owl_to_tptp` is the COMMAND-LINE route,
and exists for one reason: `hets-server`'s lossy `-Y` switch, which has no
REST equivalent. It runs the non-lossy translation first so a loss is always
reported on the result rather than silent.

```{eval-rst}
.. currentmodule:: unicode_logic_kit.hets

.. autosummary::
   :nosignatures:

   repair_haskell_json
   HaskellJsonRepair
   HaskellJsonRepairError
   strip_hets_theory_header
   HetsNoTranslationsError
   HetsSublogicError
   hets_symbol_table
   HetsSymbolTable
   HetsSymbol
   HetsSymbolCollisionError
   untranslated_axioms
   UntranslatedAxiom
   hets_prefixes
   owl_to_tptp
   OwlTptpResult
   SublogicMismatch
   HetsOwlNormalizationError
```

### Translations between logics

The registry is a graph of nine one-way translations between logic labels
(`modal`, `qml`, `msfol`, `fuzzy`, `drs`, `fol`, `alc`, `team`, `eso`). Each
edge declares a **guarantee** (one of `GUARANTEES`, or none), the **side
axioms** its image needs, and the **options** it accepts. A converted term is
never a term alone: `TranslationResult` carries the axioms and the guarantee of
the whole path, and they are separate premises of any question asked about the
image, never part of it. {func}`~unicode_logic_kit.comorphism.weakest_guarantee`
is what a composed path promises.

```{eval-rst}
.. currentmodule:: unicode_logic_kit.comorphism

.. autosummary::
   :nosignatures:

   Comorphism
   ComorphismRegistry
   register_comorphism
   TranslationResult
   DEFAULT_REGISTRY
   GUARANTEES
   weakest_guarantee
```

`unicode_logic_kit.logic` is the typed surface over that graph. A
{class}`~unicode_logic_kit.logic.Logic` is a callable value (`FOL`, `MSFOL`,
`MODAL`, `QML`, `ALC`, `DRT`, `TEAM`, `ESO`, `FUZZY`, collected in `LOGICS`):
`FOL(term)` wraps a bare term as a `Sentence` and `FOL(sentence)` converts one,
with its side axioms. {class}`~unicode_logic_kit.Sentence` is exported at the top
level.

```{eval-rst}
.. currentmodule:: unicode_logic_kit

.. autosummary::
   :toctree: _autosummary
   :nosignatures:

   Sentence
```

```{eval-rst}
.. currentmodule:: unicode_logic_kit.logic

.. autosummary::
   :nosignatures:

   Logic
   LOGICS
   FOL
   MSFOL
   MODAL
   QML
   ALC
   DRT
   TEAM
   ESO
   FUZZY
```

## Further HOL exports and deep embeddings

```{eval-rst}
.. currentmodule:: unicode_logic_kit.hol

.. autosummary::
   :toctree: _autosummary
   :nosignatures:

   to_thf_fol
   to_isabelle_fol
   to_thf_msfol
   to_isabelle_msfol
   to_thf_free
   to_isabelle_free
   free_theory
   to_thf_so
   to_isabelle_so
   to_thf_to
   to_isabelle_to
   to_thf_ho_modal
   to_isabelle_ho_modal
   isabelle_ho_modal_theory
   ho_modal_definitions
   HoAxiom
   HoGoal
   UnsupportedHigherOrderNode
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
   qml_to_deep
   gmt_translate
   gmt_is_s4_valid
   gmt_validity_matches_int_valid
   BRIDGES
   SYSTEMS
   DEFAULT_METHODS
```

## Optional prover backends and modal tableaux

A TPTP problem for a prover is built with the checked writers below —
{func}`~unicode_logic_kit.atp.generate_tptp_problem_with_mapping` (classical
`fof`), {func}`~unicode_logic_kit.atp.generate_tff_problem_with_mapping` (many-sorted
TF0) and {func}`~unicode_logic_kit.generate_tff_arith_problem` (one numeric
sort) — never by joining `Node.to_tptp()` strings, which cannot see that two
formulas use one TPTP word for two symbols (a single `to_tptp()` call does check the
one formula it renders). They refuse two legal names of one
kind that fold together (a sort counts as the guard predicate of its name,
and TF0 refuses a sort and a predicate that share a word), rename a
function/constant that would share a word with a predicate, rewrite a name
TPTP cannot spell, and hand back the {class}`~unicode_logic_kit.atp.TptpNameMap`
that {func}`~unicode_logic_kit.atp.apply_reverse_tptp` uses to translate a
proof or a model back. A conclusion is optional: `conclusion=None` writes no
`conjecture` line, for a satisfiability question. The `fof` and TF0 writers
read a numeral as an uninterpreted constant, one per value (`1` and `1.0` are
one), and `+ - * /` and `< > ≤ ≥` as uninterpreted symbols, all recorded in the
map; only `generate_tff_arith_problem` reads them as arithmetic. All three
refuse a free variable by name rather than choose a closure for it, and the TF0
writer refuses (`Tf0Refusal`) a problem whose typed text would not ask the
kit's question, such as one with an unannotated constant or a function value
that the type inference would put into a sort, or an equation over an
unsorted-quantified variable next to a sort. The Vampire and E backends'
automatic mode (`tff=None`) then writes the `fof` text instead. See "Building
a TPTP problem for a prover" in {doc}`guide/classical-reasoning`.

```{eval-rst}
.. currentmodule:: unicode_logic_kit.atp

.. autosummary::
   :toctree: _autosummary
   :nosignatures:

   generate_tptp_problem
   generate_tptp_problem_with_mapping
   generate_tff_problem_with_mapping
   TptpNameMap
   apply_reverse_tptp
   EProverBackend
   eprover_available
   check_entailment_eprover_detailed
   ZipperpositionBackend
   zipperposition_available
   eprover_relevant_premises
   TweeBackend
   twee_available
   check_entailment_twee_detailed
   check_twee_proof
   TweeCheckResult
   NanocopBackend
   nanocop_available
   to_nanocop
   HetsBackend
   lower_msfol
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
   ltl_tableau_closed
   ltl_valid
   ltl_decide
   ltl_countermodel
   ltl_trace_satisfies
   LTLTrace
   TableauStep
   TableauClosure
   ArithEnv
   degree_expr
```

## Repair internals and other fol-level types

```{eval-rst}
.. currentmodule:: unicode_logic_kit.fol

.. autosummary::
   :toctree: _autosummary
   :nosignatures:

   RepairResult
   Issue
   ProblemRepairResult
   ProblemRepairEntry
   TptpRepairError
   PrologParsingError
   PrologExportError
   SimplifyResult
   qml_axioms
   qml_validity_formula
```

## Subpackage modules

The module view of the same code: each entry documents the module's own
docstring — the design decisions and the reasons behind them — and, recursively,
its submodules.

```{eval-rst}
.. currentmodule:: unicode_logic_kit

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
   hol.lean
   chem
   fol.prolog_input
   fol.dialect_repair
   fol.modal_translation
   eval.chem_batch
   eval.datasets
   hets
   comorphism
   logic
   drt
   ace
   ilp
   prob
   mcp.syntax_spec
```
