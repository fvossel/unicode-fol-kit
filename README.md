# unicode-logic-kit

[![Tests](https://github.com/fvossel/unicode-logic-kit/actions/workflows/tests.yml/badge.svg)](https://github.com/fvossel/unicode-logic-kit/actions/workflows/tests.yml)
[![Isabelle live tests](https://github.com/fvossel/unicode-logic-kit/actions/workflows/isabelle-tests.yml/badge.svg)](https://github.com/fvossel/unicode-logic-kit/actions/workflows/isabelle-tests.yml)
[![PyPI](https://img.shields.io/pypi/v/unicode-logic-kit)](https://pypi.org/project/unicode-logic-kit/)
[![Docs](https://readthedocs.org/projects/unicode-logic-kit/badge/?version=latest)](https://unicode-logic-kit.readthedocs.io/)

A Python toolkit for **logic with Unicode operators** — *parse, transform, and reason
about* formulas of classical first-order logic and well beyond it: modal, temporal,
hybrid, many-valued, fuzzy, intuitionistic, relevant, second- and third-order,
description, dependence/IF, substructural, and a range of further non-classical
logics. On top of that sits **infrastructure for NL→logic research**:
one small API a verification loop can drive, one uniform verdict type over a dozen
provers, and an evaluation toolbox for scoring LLM-generated formulas against
benchmark gold data.

```python
from unicode_logic_kit import MSFLParser, is_valid

phi = MSFLParser().parse(
    "∀x (Human(x) → Mortal(x)) ∧ Human(socrates) → Mortal(socrates)")
print(is_valid(phi))   # True
```

> **Renamed in 0.31.0.** Up to 0.30.0 this package was `unicode-fol-kit`
> (`import unicode_fol_kit`): first-order logic is one of the logics it handles,
> not the whole of it. `pip install -U unicode-fol-kit` still works — it installs
> this package and forwards the old import name with a `DeprecationWarning` — but
> new code should `pip install unicode-logic-kit` and `import unicode_logic_kit`.
> Nothing else changed its name, the `UFK_` environment variables included.

## Why this kit?

- **One facade, seven verbs, built for LLM loops.** `api.parse_any` (dialect
  auto-detection over Unicode / TPTP / LaTeX / Prover9 / SMT-LIB — never raises,
  records every parser's objection), `api.check` (well-formedness + signature
  conformance with did-you-mean suggestions), `api.equivalent`, `api.prove`,
  `api.countermodel`, `api.repair` (a diagnose→suggest→fix generator whose fixer
  callback is *your* LLM), `api.translate` (logic-to-logic via a comorphism
  registry). Every result has a JSON-compatible `to_dict()`, and the API carries an
  explicit stability policy.
- **Logics as values, and a translation that carries its side conditions.**
  `FOL(MSFOL(f))` converts a sorted formula and keeps its side axioms (each
  sort is non-empty, each sorted constant lies in its sort) *with* the term, as
  a `Sentence`; `api.prove` adds them as premises itself, which is the
  difference between a proof and a spurious countermodel. Each of
  the nine registry edges declares what it preserves (`comorphism.GUARANTEES`),
  which side axioms its image needs and which options it reads; a composed path
  reports the weakest guarantee on it. There is no implicit coercion between
  logics on purpose — see
  [Translating between logics](https://unicode-logic-kit.readthedocs.io/en/latest/guide/logic-graph.html)
  for why a translation is not an upcast.
- **An MCP server out of the box.** `pip install unicode-logic-kit[mcp]`, then
  `python -m unicode_logic_kit.mcp` exposes the toolkit as thirty-seven Model
  Context Protocol tools (23 general-purpose, 6 for chemistry, 8 for
  description logic) — any MCP client (Claude Code/Desktop, agent
  frameworks, editors) can parse, prove, diagnose and translate without
  writing Python; the repair loop inverts naturally (the client LLM is the
  fixer). An error-analysis layer comes along: prediction-vs-gold
  breakdowns with symbol diffs (`compare_formulas`), corpus metrics
  (`score_batch`), satisfiability of premise sets with model witnesses
  (`check_consistency`), normal forms, cross-syntax rendering, truth
  tables, signature extraction, and DRS→FOL for discourse phenomena.
- **Model checking against real structures, not just model finding.** A
  molecule, a knowledge-graph neighbourhood, a scene graph is *given* — the
  question is whether a definition holds of it. `FiniteStructure` +
  `evaluate_in_structure` answer that directly: no prenex form, no CNF
  (both are documented timeout sources elsewhere), quantifiers ranging over
  indexed candidate sets rather than the whole domain, counting quantifiers
  counted instead of expanded, and properties that are decidable on a
  structure but not first-order definable over it (connectivity, ring
  membership) admitted as **computed predicates**. `unicode_logic_kit.chem`
  turns a SMILES string into such a structure over the ChemLog signature.
- **Rule learning, both directions, with the silent failures made loud.**
  `unicode_logic_kit.ilp` turns those same structures into an ILP task (Popper's
  `bk.pl` / `exs.pl` / `bias.pl`) and reads the learned Prolog clause back as a
  kit formula you can model-check. Two encoding mistakes produce a hypothesis
  that scores **precision 1.00 and means nothing** — example-local individual
  names a learner joins across, and the example argument on every predicate —
  and both are refused rather than documented, on the way out and on the way
  back. `check_separation` asks the question that has to come first: does your
  reference definition separate the two example sets at all?
- **Exact probabilistic logic — no sampling, no floats.**
  `prob.entailment_bounds` answers "what does P(bird)=0.9 entail about
  P(fly)?" with the exact tightest interval (Nilsson's probabilistic
  entailment as a rational LP over possible worlds, conditionals included);
  `prob.query` answers ProbLog-style queries over definite programs with
  independent probabilistic facts under Sato's distribution semantics —
  every result an exact `Fraction`, every unsupported fragment a loud
  refusal.
- **Twenty-five prover backends, one honest `Verdict`.** The kit's own calculi and
  semantic searches (resolution — with sound paramodulation/demodulation for
  equality, no hand-supplied congruence axioms needed —, analytic tableaux
  with recorded, independently checkable proof objects, modal tableau, finite
  model finder, bounded Kripke enumeration, QML embedding) are first-class
  citizens next to Z3,
  cvc5, Vampire, E, Zipperposition, Twee (equational proofs re-verified by an
  independent checker before the kit reports them), Prover9, Leo-III, Isabelle,
  nanoCoP-M (native first-order modal logic, opt-in with a mandatory independent
  cross-check) and a Dockerized HETS server (CASL export *and* round-trip
  import with native many-sortedness, multi-spec DOL library emission,
  SPASS/darwin behind one name, comorphism provenance in every
  verdict). Every route returns the same
  `Verdict` with a semantic status (`proved` / `refuted` / `unknown` / `error`),
  a separate *why-not-more* axis (`timeout` ≠ `bound_hit` ≠ `incomplete` ≠
  `unsupported`), the SZS status, wall time, and JSON-able witnesses. Chains,
  portfolios (`portfolio_prove`, parallel with agreement thresholds and a
  soundness alarm on prover disagreement), and cached batch runs
  (`batch_decide`) are built on top.
- **An evaluation toolbox for NL→FOL work.** A graded equivalence ladder (exact →
  canonical → vocabulary-aligned → solver, with a tri-state solver level and
  partial credit), AST-level symbol alignment, gold-formula self-audit, and
  adapters for **FOLIO, MALLS, GROVES, WillowNLtoFOL, ProntoQA, ProofWriter,
  LogicNLI, ProverQA and FraCaS** — each with its upstream schema verified at the
  source and its limitations documented instead of smoothed over. FraCaS is the
  pure-NLI one: no gold formulas at all, so the translation step is an injected
  callable and the kit only decides.
- **Countermodels that explain themselves.** `api.countermodel` returns a
  machine-readable witness *plus* a plain-English rendering ("The countermodel has
  2 possible worlds. … At world 0 the formula fails."), and refutation actually
  covers the temporal fragment: `Ⓕ P → P` comes back **refuted** with a two-world
  Kripke witness, not "unknown".
- **Honesty as a contract.** No route silently degrades: fuzzy input is refused by
  classical provers rather than collapsed, an unavailable backend raises instead
  of vanishing from the chain, incomplete methods report *why* they stopped, and
  every proof method has an independent checker.

```python
from unicode_logic_kit import api

result = api.parse_any("∀x (Raven(x) → Black(x))")     # LLM output, any dialect
report = api.check(result.formula,
                   signature={"predicates": {"Raven": 1, "Black": 1}})
verdict = api.prove(api.parse_any("Black(tweety)").formula,
                    premises=[result.formula,
                              api.parse_any("Raven(tweety)").formula])
print(verdict.status, verdict.backend, verdict.szs_status)  # proved z3 Theorem
```

One parser class, `MSFLParser`, reads classical logic at the **first, second and third
order**, each with or without **sorts** and with or without the **modal** family
(modal/temporal/epistemic/deontic/hybrid): twelve combinations of three constructor
flags. Next to them stand many-sorted and single-sorted Łukasiewicz fuzzy logic,
team-semantic dependence/IF logic, intuitionistic linear logic, and the Lambek calculus.
The surface syntax is natural Unicode (`∀ ∃ ∧ ∨ ¬ → ↔ ⊕ ⊗ □ ◇ @ ⊸ 𝟙 …`) with no ASCII
fallbacks.

On top of the AST sits a full reasoning stack — **four proof methods** (a built-in
resolution prover, Fitch natural deduction with checker *and* searcher, the Gentzen
sequent calculi **LK**/**LJ** — the latter backed by Dyckhoff's **G4ip**, a genuine
terminating decision procedure for propositional intuitionistic logic — and analytic
tableaux), a **finite model finder**, SMT (Z3) and external-prover (Prover9 / Vampire)
backends, truth tables, and dedicated semantics for every logic. Every proof method has
an **independent checker** — including `check_resolution_proof`, which certifies
externally produced resolution derivations (paramodulation steps included) with
its own from-scratch unification, and `check_tableau_proof`, which re-derives
every α/β/γ/δ step of a recorded tableau with its own substitution and
δ-freshness check.
Formulas import/export to TPTP (incl. header `Status`/`Rating` metadata via
`parse_tptp_problem`), Prover9, SMT-LIB, LaTeX, and JSON.

## 📖 Documentation

**Full guide and API reference: <https://unicode-logic-kit.readthedocs.io/>**

The documentation walks through every logic with runnable examples — start with the
[Quickstart](https://unicode-logic-kit.readthedocs.io/en/latest/guide/quickstart.html) and
[Choosing a tool](https://unicode-logic-kit.readthedocs.io/en/latest/guide/choosing.html).

Beyond deciding formulas:
[Model checking](https://unicode-logic-kit.readthedocs.io/en/latest/guide/model-checking.html)
(evaluate a formula in a structure you already have — including molecules),
[Verification](https://unicode-logic-kit.readthedocs.io/en/latest/guide/verification.html)
(is a definition *set* coherent, or just too easily satisfied?),
[Probabilistic logic](https://unicode-logic-kit.readthedocs.io/en/latest/guide/probabilistic.html)
(exact bounds and queries, no sampling), and
[MCP](https://unicode-logic-kit.readthedocs.io/en/latest/guide/mcp.html)
(the toolkit, grammar included, as tools for a language model).

## Installation

```bash
pip install unicode-logic-kit
```

Requires Python 3.10+. Z3 ships with the package. `pip install
"unicode-logic-kit[cvc5]"` adds cvc5 as a second in-process SMT backend (it then
joins the default proving chain right after Z3); `[mcp]` adds the MCP server
(`python -m unicode_logic_kit.mcp`); `[hf]` adds the HuggingFace-`evaluate`
metric wrapper; `[owl]` adds owlready2, so `dl.owl_reasoner` can hand a
description-logic problem to HermiT (needs a JVM on `PATH`) and decide the
inverse roles and nominals the in-house tableau refuses by name — note that
owlready2 is LGPL-3.0-or-later, unlike this MIT-licensed kit. Prover9, Vampire, E, Zipperposition, Twee, nanoCoP-M
(needs your own ECLiPSe/SWI-Prolog install; `$UFK_NANOCOP_CMD`), and
Isabelle are optional external tools you install separately to unlock the
corresponding backends, and the HETS backend wants Docker (`docker pull
spechub2/hets:latest`; a running server is discovered on `localhost:8000`
or via `$UFK_HETS_URL`) — each is discovered explicitly and reports itself
as unavailable rather than silently disappearing.

## Logics at a glance

| Logic | Enable / entry point | Decide / reason with |
|---|---|---|
| Classical FOL / MSFOL | `MSFLParser()` / `many_sorted=True` | resolution, Z3, Prover9/Vampire, tableaux, Fitch, LK, finite model finder |
| Fuzzy Łukasiewicz / Gödel / product | `MSFLParser(fuzzy=True)` | `fuzzy_evaluate`, `fuzzy_is_valid(…, tnorm=…)` (Z3 reals, quantifier grounding; Łukasiewicz and Gödel only — the product t-norm is evaluator-only and `fuzzy_is_valid` refuses it by name); classical routes (`is_valid`, normal forms, resolution) refuse fuzzy input rather than silently collapsing it — opt in explicitly with `to_fol(node)` |
| Modal / temporal / epistemic / deontic | `MSFLParser(modal=True)` | `satisfies_modal`, `standard_translation`, native `is_modal_valid` / `modal_decide` (K…S5, B, KD45) |
| Quantified modal | `KripkeModel(domains=…)` | `qml_is_valid` per domain regime + frame; THF / Isabelle export |
| Many-valued K3 / LP / Belnap FDE | `truth_table`, `semantics.matrix` | `matrix_is_valid` / `matrix_entails` over any finite `TruthMatrix`, incl. THF/Isabelle export |
| Intuitionistic | `int_valid` / `int_countermodel` | propositional **decision procedure** (`int_prove`/`int_decide`, G4ip) + bounded first-order Kripke search; LJ checker |
| Second-order | `MSFLParser(second_order=True)` | `satisfies_so`, bounded `so_is_valid_finite` / `so_find_countermodel` |
| Third-order (incl. modal) | `MSFLParser(third_order=True[, modal=True])` | a predicate whose ARGUMENT is a property (`Pos(G)`, `Pos(λx. ¬G(x))`); slot types inferred across a theory; `to_thf_to` / `to_isabelle_to` and the shallow modal embedding `hol.ho_modal`; `hol.goedel` checks Gödel's ontological argument both ways |
| Description logic **ALCHQ** | `unicode_logic_kit.dl` | `concept_satisfiable` / `subsumes` / `abox_consistent` (tableau, TBox + ABox, role hierarchies + transitive roles, qualified number restrictions `AtLeast`/`AtMost` on simple roles); `parse_concept`/`parse_gci`/`parse_manchester` plus `concept_to_fol`/`kb_to_fol`/`tbox_to_fol`/`rbox_to_fol`/`abox_to_fol` reuse the FOL provers (Z3's `Count` expansion for the number restrictions) and Isabelle/THF exports |
| Free · public-announcement · counterfactual · circumscription | `semantics.free_logic` / `dynamic_epistemic` / `conditional` / `nonmonotonic` | `free_is_valid`/`free_entails` (bounded search); `[φ!]ψ`/`⟨φ!⟩ψ` parse in modal mode and decide via `reduce_announcements`; `cf_valid` over Lewis V / VW / VC (`centering=`, default weakly centered); `minimal_entails` and the unbounded `circumscription_entails_so` |
| Hybrid **H(@)** (nominals, `@i φ`) | `MSFLParser(modal=True)` | `KripkeModel(nominals=…)`, `hybrid_is_valid` per frame (standard translation + Z3) |
| Relevant logic **B** | classical syntax + `semantics.relevant` | `rel_valid` / `rel_countermodel` (Routley–Meyer, bounded exhaustive search); `isabelle_decide_relevant` certifies both directions |
| Dependence / IF (team semantics) | `MSFLParser(dependence=True)` | `team_satisfies` / `team_models` over finite structures; `dependence_to_eso` translates the guarded/slashed sentence fragment to ESO for `satisfies_so` / Isabelle export |
| Linear logic (ILL, incl. `⊤`/`𝟘`) · Lambek calculus | `MSFLParser(linear=True)` / `lambek=True` | `ill_prove` (cut-free; complete for !-free) · `lambek_derivable` (decision procedure); either derivation replays as a machine-checked Isabelle lemma |

With a local **Isabelle** installed, the `hol` subpackage's shallow embeddings become
*proofs*: `isabelle_decide_modal` / `isabelle_decide_fol` / `isabelle_decide_relevant`
actually run the prover, and `hol.isabelle_substructural` replays a Python-found
ILL/Lambek derivation as a machine-checked lemma. The `hol.deepshallow` subpackage goes
further, emitting — for propositional modal, intuitionistic, Lewis-conditional and
relevant logic, plus a Tier 2 quantified fragment (K frame, constant domain, alethic
□/◇ only) — the **deep, maximal-shallow and minimal-shallow** embeddings side by
side with **machine-checked faithfulness proofs** between them (Benzmüller,
arXiv:2502.19311), verified end to end by Isabelle. See
the [higher-order guide](https://unicode-logic-kit.readthedocs.io/en/latest/guide/higher-order.html).

## Command line

```bash
python -m unicode_logic_kit "∀x P(x)" --to latex
```

`--mode` selects the parser dialect — `fol` (default), `msfol`, `msfl`, `fl`, `modal`,
`second_order`, `dependence`, `linear`, `lambek` — and `--to` the rendering: `tree`,
`unicode`, `latex`, `tptp`, `prover9`, `json`, `dot`.

The seven-verb facade is also scriptable via subcommands (`--json` for
machine-readable output; exit codes encode the verdict):

```bash
python -m unicode_logic_kit prove "Ⓕ P → P" --dialect modal
python -m unicode_logic_kit check "∀x (Human(x) → Mortal(x))" --json
```

plus `equiv`, `countermodel`, `repair`, and `translate`.

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
