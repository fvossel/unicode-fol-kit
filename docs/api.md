# API reference

Auto-generated from the package docstrings. The tables below link to the full
signature and documentation of each public entry point; use the search box or the
{ref}`genindex` for anything not listed here.

## Parsing & the AST

```{eval-rst}
.. currentmodule:: unicode_fol_kit

.. autosummary::
   :toctree: _autosummary
   :nosignatures:

   MSFLParser
   Node
   substitute
   free_variables
   to_fol
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
   eliminate_lambdas
   beta_eta_normalize
   reduce_trace
   unify
   apply_subst
```

## Import / export

```{eval-rst}
.. autosummary::
   :toctree: _autosummary
   :nosignatures:

   parse_tptp
   parse_tptp_formula
   load_tptp
   parse_prover9
   parse_prover9_problem
   load_prover9
   from_z3
   parse_smtlib
   load_smtlib
   sanitize_names
   sanitize_all
   parse_latex
   latex_to_unicode
   to_english
```

## Classical reasoning

```{eval-rst}
.. autosummary::
   :toctree: _autosummary
   :nosignatures:

   prove
   is_valid_resolution
   is_valid
   is_satisfiable
   get_model
   is_satisfiable_arith
   is_valid_arith
   formulas_are_equivalent
   check_logical_entailment
   check_logical_entailment_vampire
   find_model
   find_countermodel
   is_satisfiable_finite
   is_valid_finite
```

## Proof systems

```{eval-rst}
.. autosummary::
   :toctree: _autosummary
   :nosignatures:

   check_proof
   find_fitch_proof
   is_valid_fitch
   render_fitch
   check_sequent_proof
   check_lj_proof
   is_valid_tableau
   prove_tableau
   tableau_model
   ill_prove
   ill_derivable
   check_ill_proof
   lambek_prove
   lambek_derivable
   check_lambek_proof
```

## Modal, temporal, epistemic & deontic logic

```{eval-rst}
.. autosummary::
   :toctree: _autosummary
   :nosignatures:

   satisfies_modal
   standard_translation
   is_modal_valid
   modal_decide
   modal_countermodel
   modal_prove
   qml_is_valid
   qml_equivalent
   hybrid_is_valid
   to_thf_modal
   to_isabelle_modal
   isabelle_decide_modal
   isabelle_decide_fol
   isabelle_decide_counterfactual
   modal_faithfulness_theory
   intuitionistic_faithfulness_theory
   conditional_faithfulness_theory
   relevant_faithfulness_theory
```

## Many-valued, fuzzy, intuitionistic & second-order

```{eval-rst}
.. autosummary::
   :toctree: _autosummary
   :nosignatures:

   truth_table
   kleene_value
   matrix_is_valid
   matrix_entails
   fuzzy_evaluate
   fuzzy_is_valid
   get_tnorm
   int_valid
   int_countermodel
   satisfies_so
   so_is_valid_finite
   so_find_countermodel
   minimal_entails
   free_holds
   announce
   would
   cf_satisfies
   cf_valid
   cf_countermodel
   rel_valid
   rel_countermodel
   rel_satisfies
   team_satisfies
   team_models
```

## Model checking in a given structure

```{eval-rst}
.. currentmodule:: unicode_fol_kit.semantics

.. autosummary::
   :toctree: _autosummary
   :nosignatures:

   FiniteStructure
   evaluate_in_structure
   evaluate_detailed
   graph_to_structure
   structure_from_dict
```

```{eval-rst}
.. currentmodule:: unicode_fol_kit

.. autosummary::
   :toctree: _autosummary
   :nosignatures:

   simplify_for_checking
   count_from_existential_chain
   repair_tptp_formula
   repair_tptp_problem
```

## Verifying definition sets

```{eval-rst}
.. currentmodule:: unicode_fol_kit.eval

.. autosummary::
   :toctree: _autosummary
   :nosignatures:

   check_theory
   check_satisfiable
   check_subsumption
   find_cycles
   minimal_model_size
   generality_report
   is_vacuous_specialisation
   explain_countermodel
```

## Probability

```{eval-rst}
.. currentmodule:: unicode_fol_kit.prob

.. autosummary::
   :toctree: _autosummary
   :nosignatures:

   ProbConstraint
   ProbBounds
   entailment_bounds
   ProbFact
   ProbProgram
   query
```

## Subpackage modules

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
   atp.modal_tableau
   hol.isabelle_runner
   chem
   mcp.syntax_spec
```
