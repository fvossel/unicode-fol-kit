# Linear-time temporal logic (LTL + Past)

`unicode_fol_kit.atp.ltl_tableau` is a **complete decision procedure** for the
propositional temporal-closure fragment — `Ⓝ Ⓖ Ⓕ Ⓤ` (Next / Always /
Eventually / Until) and their past mirrors `⒴ ⒣ ⒫ ⒮` (Previous / Historically
/ Once / Since) — under the **standard linear-time reading**: the temporal
frame fixed to the unique discrete strict order on the natural numbers,
`0 < 1 < 2 < …`. It answers exactly the question the LTL literature means by
"is this formula valid" — a strictly narrower, better-behaved question than
every OTHER route in the kit that touches these same operator names.

## Why a fourth route, and how it differs from the other three

`Ⓖ`/`Ⓕ`/`Ⓝ`/`Ⓤ` and their past mirrors are already familiar from {doc}`modal`
and {doc}`quantified-modal`: the kit's Kripke semantics for these operators
({mod}`unicode_fol_kit.semantics.kripke`) is deliberately **not** standard
LTL — `"temporal"` is an arbitrary (not necessarily linear, not necessarily
total) accessibility relation there, and `Until`/`Since` are existential
finite-path searches over it. `fol.qml`'s default axioms (reflexive +
transitive + `N ⊆ T`) don't pin the relation down to a line either — see
{doc}`quantified-modal`'s worked example, where `resolution.prove` and
`qml_is_valid` already disagree on a temporal formula for exactly this
reason, without either being unsound.

| Route | Frame decided | Verdict |
| --- | --- | --- |
| `satisfies_modal` | whatever `KripkeModel` you build | ground truth for THAT model |
| `modal_tableau` | — | refuses G/F/U/H/O/P/S outright (no rule) |
| `qml_is_valid` | refl + trans + `N ⊆ T` (a large class, not just lines) | sound, bounded-incomplete |
| **`ltl_tableau`** | **the standard linear order, exactly** | **sound AND complete** |

Because the linear frame is a strict *subset* of qml's frame class, anything
`qml_is_valid` proves valid is automatically valid here too — this module can
never *refute* something qml already proved. It can, however, prove strictly
more: temporal induction below is the standard example, and `fol.qml`'s own
module docstring names it as genuinely unreachable there.

## What the operator names mean here

Matching each node's own docstring and `semantics/kripke.py`'s documented
semantics, so a name means the same thing on this frame as everywhere else in
the kit — only the frame class changes:

- **`Ⓝ` (Next)**: φ holds at the immediately following position.
- **`Ⓖ`/`Ⓕ` (Always/Eventually)**: φ holds at every / some position from now
  on, **current position included** (`Ⓖφ → φ` and `φ → Ⓕφ` are theorems).
- **`Ⓤ` (Until), non-strict**: `φ Ⓤ ψ` holds iff ψ holds at some position
  `n ≥` now with φ holding at every position strictly before `n` — ψ may hold
  *right now*.
- **`⒣`/`⒫` (Historically/Once)**: the past duals of `Ⓖ`/`Ⓕ` — φ at every /
  some position from the beginning of time up to and including now.
- **`⒮` (Since), non-strict**: the backward mirror of `Ⓤ`.
- **`⒴` (Previous), WEAK at position 0**: vacuously **true** at position 0
  for every φ (there is no predecessor to check) — per the node's own
  docstring. There is no existential "strong previous" operator in the AST;
  on a linear frame it is expressible as `¬⒴¬φ`, and this module uses exactly
  that identity internally.

## Initial vs. floating validity

With past operators, "valid" genuinely splits in two:

- **`mode="initial"`** (the default): φ holds at position 0 of every model —
  the reading every textbook validity claim about a logic WITH past operators
  means.
- **`mode="floating"`**: φ holds at *every* position of every model — a
  strictly stronger requirement.

They coincide on the past-operator-free fragment, but diverge as soon as a
formula can tell "I have no predecessor" apart from "I do":

```python
from unicode_fol_kit import MSFLParser
from unicode_fol_kit.atp.ltl_tableau import ltl_valid

mp = MSFLParser(modal=True)
no_predecessor = mp.parse("⒴(P ∧ ¬P)")   # "there is no earlier position"

ltl_valid(no_predecessor, mode="initial")    # → True  (vacuously, at position 0)
ltl_valid(no_predecessor, mode="floating")   # → False (false at any later position)
```

## A worked example: temporal induction

This is the flagship completeness gain over `qml_is_valid` — its own module
docstring says reaching it "genuinely does stay out of reach" for the
first-order embedding, because it needs induction over the closure that no
first-order theory states:

```python
from unicode_fol_kit import MSFLParser
from unicode_fol_kit.atp.ltl_tableau import ltl_valid
from unicode_fol_kit.fol.qml import qml_is_valid

mp = MSFLParser(modal=True)
ti = mp.parse("(P ∧ Ⓖ(P → Ⓝ P)) → Ⓖ P")

ltl_valid(ti)    # → True   -- this module decides it directly
qml_is_valid(ti) # → False  -- the FO embedding cannot reach it
```

## A worked example: a non-theorem, with an explicit lasso countermodel

`Ⓖ Ⓕ P → Ⓕ Ⓖ P` ("p infinitely often" implies "p forever from some point
on") is the standard non-theorem from Baier & Katoen, ch. 5:

```python
from unicode_fol_kit import MSFLParser
from unicode_fol_kit.atp.ltl_tableau import (
    ltl_valid, ltl_decide, ltl_countermodel, ltl_trace_satisfies,
)

mp = MSFLParser(modal=True)
gf_fg = mp.parse("Ⓖ Ⓕ P → Ⓕ Ⓖ P")

ltl_valid(gf_fg)    # → False
ltl_decide(gf_fg)   # → 'invalid'

cm = ltl_countermodel(gf_fg)
cm.to_dict()
# → {'kind': 'ltl_lasso', 'prefix': [[]], 'cycle': [['P'], []], 'witness_position': 0}
```

`cm` is an {class}`~unicode_fol_kit.atp.ltl_tableau.LTLTrace`: an explicit
finite prefix (`[]`, i.e. p false at position 0) plus an infinitely-repeating
cycle (`['P'], []` — p alternates true/false forever). Every countermodel
this module returns has already been checked against
{func}`~unicode_fol_kit.atp.ltl_tableau.ltl_trace_satisfies` before you see
it — a direct, from-the-semantic-equations evaluator, independent of the
tableau's own closure/graph machinery — so it never comes back spurious:

```python
ltl_trace_satisfies(gf_fg, cm)   # → False, confirming the model above
```

## As a ProverBackend

`ltl_tableau.LtlTableauBackend` is registered under `"ltl-tableau"`, so it
joins {func}`~unicode_fol_kit.atp.protocol.get_backend` alongside
`modal-tableau` / `qml` / `isabelle`:

```python
from unicode_fol_kit.atp.protocol import get_backend

backend = get_backend("ltl-tableau")
backend.decide(ti).status      # → 'proved'
backend.decide(gf_fg).status   # → 'refuted'
```

It is deliberately **not** part of `default_chain("modal")`: this backend
answers a strictly narrower question (the standard linear frame) than the
rest of that chain, so — like the external provers — it must be reached by
name rather than silently joining a portfolio that assumes a shared frame
class. `atp.modal_tableau`'s own "no tableau rule for G/F/U/…" message now
names it as the definitive route for the standard reading, alongside `qml`
and `isabelle` for the general (possibly non-linear) frame.

## What this module refuses

Only the fragment above — classical connectives plus the eight temporal
operators. A `Box`, `Knows`, a quantifier, or any other modal/hybrid/PAL
construct raises `NotImplementedError` naming it, rather than being
approximated:

```python
from unicode_fol_kit import Box, Atom
from unicode_fol_kit.atp.ltl_tableau import ltl_valid

ltl_valid(Box(Atom("P", [])))
# → NotImplementedError: ltl_tableau: no rule for Box (...) — this module
#   decides only the propositional temporal-closure fragment ... use
#   atp.modal_tableau, fol.qml.qml_is_valid, or
#   hol.isabelle_runner.isabelle_decide_modal for anything else.
```

Use {doc}`modal` (`atp.modal_tableau`) for the alethic/epistemic/doxastic/
deontic fragment, and {doc}`quantified-modal` (`fol.qml`) or
`hol.isabelle_runner.isabelle_decide_modal` for quantified or non-linear
temporal reasoning.
