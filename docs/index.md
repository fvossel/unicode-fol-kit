# unicode-fol-kit

A Python toolkit for **first-order logic with Unicode operators** — parse, transform,
and reason about formulas — with a reasoning layer that reaches well beyond classical
FOL into modal, temporal, many-valued, fuzzy, intuitionistic, second-order, description,
and a range of non-classical logics.

```{code-block} python
from unicode_fol_kit import MSFLParser, is_valid

phi = MSFLParser().parse("∀x (Human(x) → Mortal(x)) ∧ Human(socrates) → Mortal(socrates)")
print(is_valid(phi))   # True
```

One parser class (`MSFLParser`) feeds a full reasoning stack: four proof methods (a
built-in resolution prover, Fitch natural deduction with checker *and* searcher, the
Gentzen sequent calculi **LK**/**LJ**, and analytic tableaux), a finite model finder,
SMT (Z3) and external-prover (Prover9/Vampire) backends, truth tables, and dedicated
semantics for every logic. Formulas import/export to TPTP, Prover9, SMT-LIB, LaTeX,
and JSON.

Beyond deciding formulas, the kit evaluates them against structures you already
have (**{doc}`guide/model-checking`**, including molecules as first-order
structures), audits definition *sets* for coherence and over-generality
(**{doc}`guide/verification`**), computes exact probability bounds and queries
(**{doc}`guide/probabilistic`**), and serves the whole toolkit — grammar
included — to a language model over MCP (**{doc}`guide/mcp`**).

## Where to start

- New here? Read **{doc}`guide/installation`** then **{doc}`guide/quickstart`**.
- Looking for a specific capability? The **{doc}`guide/choosing`** page maps a question
  (and a logic) to the entry point that answers it.
- Want the exact signature of a function? See the **{doc}`api`** reference.

```{toctree}
:maxdepth: 2
:caption: Guide

guide/installation
guide/quickstart
guide/choosing
guide/parsing
guide/transforms
guide/interoperability
guide/classical-reasoning
guide/modal
guide/quantified-modal
guide/higher-order
guide/many-valued
guide/fuzzy
guide/intuitionistic
guide/second-order
guide/third-order
guide/description-logic
guide/hybrid
guide/relevant
guide/dependence
guide/substructural
guide/nonclassical
guide/probabilistic
guide/natural-language
guide/derivations
guide/model-checking
guide/verification
guide/batch-checking
guide/finite-domain
guide/mcp
guide/syntax-reference
```

```{toctree}
:maxdepth: 1
:caption: Reference

api
changelog
```

## Indices

- {ref}`genindex`
- {ref}`modindex`
- {ref}`search`
