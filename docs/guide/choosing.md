# Choosing a tool

The kit spans several proof methods, a model finder, and a wide non-classical periphery across many logics. The tables below map a question (and a logic) to the entry point that answers it; each entry point is documented in detail in its own section.

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
| Decide modal validity with a real prover (Isabelle installed) | `isabelle_decide_modal` | `ModalVerdict` (valid / invalid / unknown) | sound (kernel-checked proof or genuine nitpick countermodel); incomplete |
| Fuzzy degree or decision (Łukasiewicz / Gödel / product) | `fuzzy_evaluate(…, tnorm=)`; `fuzzy_is_valid(…, tnorm=)`, `fuzzy_is_satisfiable`, `fuzzy_get_model` | degree / bool | real-arithmetic decision via Z3; quantifiers grounded over a finite domain |
| Description-logic concept reasoning (ALC) | `concept_satisfiable`, `subsumes`, `equivalent`, `abox_consistent` (`unicode_fol_kit.dl`) | bool | sound & complete; tableau with TBox internalisation and blocking |
| Read a formula back as English | `to_english` | str | readability aid, not a parse inverse |

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

## Composing parser modes

The four core parser modes form the `many_sorted` × `fuzzy` 2×2; the **modal** and **second-order** modes are each "classical unsorted FOL + one extension" and do not combine with sorts, fuzziness, or each other. The constructor rejects an unsupported combination with a clear `ValueError`. (The matrix, ALC, intuitionistic, and peripheral logics are separate subsystems, not parser flags.)

| Combine… | with sorts | with fuzzy | with modal | with second-order |
|---|---|---|---|---|
| **base FOL** | ✅ MSFOL | ✅ FL | ✅ modal | ✅ second-order |
| **sorts** | — | ✅ MSFL | ❌ | ❌ |
| **fuzzy** | ✅ MSFL | — | ❌ | ❌ |
| **modal** | ❌ | ❌ | — | ❌ |
| **second-order** | ❌ | ❌ | ❌ | — |

## Out of scope

PRs welcome for: relevant / relevant-implication logic (Routley–Meyer frames), hybrid logic (nominals / `@`), independence-friendly / dependence logic, and substructural (linear / separation) logics.
