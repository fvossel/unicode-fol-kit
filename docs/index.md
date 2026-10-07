# unicode-logic-kit

A Python toolkit for **logic with Unicode operators** — parse, transform, and reason
about formulas of classical first-order logic and well beyond it: modal, temporal,
many-valued, fuzzy, intuitionistic, second- and third-order, description, and a range
of non-classical logics.

```{note}
Up to 0.30.0 this package was called `unicode-fol-kit` (`import unicode_fol_kit`).
`pip install -U unicode-fol-kit` installs this package and forwards the old import
name with a `DeprecationWarning`; new code should use `unicode-logic-kit` and
`import unicode_logic_kit`. See {doc}`guide/installation`.
```

```{code-block} python
from unicode_logic_kit import MSFLParser, is_valid

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
- Moving a formula from one logic to another (modal or many-sorted to first-order, a
  description-logic concept to FOL, …)? Read **{doc}`guide/logic-graph`** first: a translation
  hands back side axioms that must reach the prover with it.
- Want the exact signature of a function? See the **{doc}`api`** reference.

```{toctree}
:maxdepth: 2
:caption: Guide

guide/installation
guide/quickstart
guide/choosing
guide/parsing
guide/transforms
guide/logic-graph
guide/interoperability
guide/classical-reasoning
guide/modal
guide/quantified-modal
guide/linear-temporal
guide/higher-order
guide/lean
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
guide/exercises
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
