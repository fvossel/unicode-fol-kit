# unicode-fol-kit

A Python toolkit for **first-order logic with Unicode operators** — *parse, transform,
and reason about* formulas — with a reasoning layer that reaches well beyond classical
FOL into modal, temporal, hybrid, many-valued, fuzzy, intuitionistic, relevant,
second-order, description, dependence/IF, substructural, and a range of further
non-classical logics.

```python
from unicode_fol_kit import MSFLParser, is_valid

phi = MSFLParser().parse(
    "∀x (Human(x) → Mortal(x)) ∧ Human(socrates) → Mortal(socrates)")
print(is_valid(phi))   # True
```

One parser class, `MSFLParser`, has **nine modes** (classical FOL, many-sorted FOL,
many-sorted and single-sorted Łukasiewicz fuzzy logic, modal/temporal/epistemic/deontic/
hybrid, second-order, team-semantic dependence/IF logic, intuitionistic linear logic,
and the Lambek calculus) selected by constructor flags, with natural Unicode surface
syntax (`∀ ∃ ∧ ∨ ¬ → ↔ ⊕ ⊗ □ ◇ @ ⊸ 𝟙 …`) and no ASCII fallbacks.

On top of the AST sits a full reasoning stack — **four proof methods** (a built-in
resolution prover, Fitch natural deduction with checker *and* searcher, the Gentzen
sequent calculi **LK**/**LJ** — the latter backed by Dyckhoff's **G4ip**, a genuine
terminating decision procedure for propositional intuitionistic logic — and analytic
tableaux), a **finite model finder**, SMT (Z3) and external-prover (Prover9 / Vampire)
backends, truth tables, and dedicated semantics for every logic. Formulas import/export
to TPTP, Prover9, SMT-LIB, LaTeX, and JSON.

## 📖 Documentation

**Full guide and API reference: <https://unicode-fol-kit.readthedocs.io/>**

The documentation walks through every logic with runnable examples — start with the
[Quickstart](https://unicode-fol-kit.readthedocs.io/en/latest/guide/quickstart.html) and
[Choosing a tool](https://unicode-fol-kit.readthedocs.io/en/latest/guide/choosing.html).

## Installation

```bash
pip install unicode-fol-kit
```

Requires Python 3.10+. Z3 ships with the package; Prover9, Vampire, and Isabelle are
optional external tools you install separately to unlock the corresponding backends.

## Logics at a glance

| Logic | Enable / entry point | Decide / reason with |
|---|---|---|
| Classical FOL / MSFOL | `MSFLParser()` / `many_sorted=True` | resolution, Z3, Prover9/Vampire, tableaux, Fitch, LK, finite model finder |
| Fuzzy Łukasiewicz / Gödel / product | `MSFLParser(fuzzy=True)` | `fuzzy_evaluate`, `fuzzy_is_valid(…, tnorm=…)` (Z3 reals, quantifier grounding); classical routes (`is_valid`, normal forms, resolution) refuse fuzzy input rather than silently collapsing it — opt in explicitly with `to_fol(node)` |
| Modal / temporal / epistemic / deontic | `MSFLParser(modal=True)` | `satisfies_modal`, `standard_translation`, native `is_modal_valid` / `modal_decide` (K…S5, B, KD45) |
| Quantified modal | `KripkeModel(domains=…)` | `qml_is_valid` per domain regime + frame; THF / Isabelle export |
| Many-valued K3 / LP / Belnap FDE | `truth_table`, `semantics.matrix` | `matrix_is_valid` / `matrix_entails` over any finite `TruthMatrix`, incl. THF/Isabelle export |
| Intuitionistic | `int_valid` / `int_countermodel` | propositional **decision procedure** (`int_prove`/`int_decide`, G4ip) + bounded first-order Kripke search; LJ checker |
| Second-order | `MSFLParser(second_order=True)` | `satisfies_so`, bounded `so_is_valid_finite` / `so_find_countermodel` |
| Description logic **ALC** | `unicode_fol_kit.dl` | `concept_satisfiable` / `subsumes` / `abox_consistent` (tableau, TBox + ABox); `parse_concept`/`parse_gci` plus `concept_to_fol`/`tbox_to_fol`/`abox_to_fol` reuse the FOL provers and Isabelle/THF exports |
| Free · public-announcement · counterfactual · circumscription | `semantics.free_logic` / `dynamic_epistemic` / `conditional` / `nonmonotonic` | `free_is_valid`/`free_entails` (bounded search); `[φ!]ψ`/`⟨φ!⟩ψ` parse in modal mode and decide via `reduce_announcements`; `cf_valid`; `minimal_entails` and the unbounded `circumscription_entails_so` |
| Hybrid **H(@)** (nominals, `@i φ`) | `MSFLParser(modal=True)` | `KripkeModel(nominals=…)`, `hybrid_is_valid` per frame (standard translation + Z3) |
| Relevant logic **B** | classical syntax + `semantics.relevant` | `rel_valid` / `rel_countermodel` (Routley–Meyer, bounded exhaustive search); `isabelle_decide_relevant` certifies both directions |
| Dependence / IF (team semantics) | `MSFLParser(dependence=True)` | `team_satisfies` / `team_models` over finite structures; `dependence_to_eso` translates the guarded/slashed sentence fragment to ESO for `satisfies_so` / Isabelle export |
| Linear logic (ILL, incl. `⊤`/`𝟘`) · Lambek calculus | `MSFLParser(linear=True)` / `lambek=True` | `ill_prove` (cut-free; complete for !-free) · `lambek_derivable` (decision procedure); either derivation replays as a machine-checked Isabelle lemma |

With a local **Isabelle** installed, the `hol` subpackage's shallow embeddings become
*proofs*: `isabelle_decide_modal` / `isabelle_decide_fol` / `isabelle_decide_relevant`
actually run the prover, and `hol.isabelle_substructural` replays a Python-found
ILL/Lambek derivation as a machine-checked lemma. The `hol.deepshallow` subpackage goes
further, emitting — for propositional modal, intuitionistic, Lewis-conditional and
relevant logic — the **deep, maximal-shallow and minimal-shallow** embeddings side by
side with **machine-checked faithfulness proofs** between them (Benzmüller,
arXiv:2502.19311), verified end to end by Isabelle. See
the [higher-order guide](https://unicode-fol-kit.readthedocs.io/en/latest/guide/higher-order.html).

## Command line

```bash
python -m unicode_fol_kit "∀x P(x)" --to latex
```

`--mode` selects the parser dialect — `fol` (default), `msfol`, `msfl`, `fl`, `modal`,
`second_order`, `dependence`, `linear`, `lambek` — and `--to` the rendering: `tree`,
`unicode`, `latex`, `tptp`, `prover9`, `json`, `dot`.

## Building the documentation locally

```bash
pip install -e ".[docs]"
sphinx-build -b html docs docs/_build/html
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
