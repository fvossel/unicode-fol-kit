# Linear-time temporal logic (LTL + Past)

`unicode_logic_kit.atp.ltl_tableau` is a **complete decision procedure** for the
propositional temporal-closure fragment — `Ⓝ Ⓖ Ⓕ Ⓤ` (Next / Always /
Eventually / Until) and their past mirrors `⒴ ⒣ ⒫ ⒮` (Previous / Historically
/ Once / Since) — under the **standard linear-time reading**: the temporal
frame fixed to the unique discrete strict order on the natural numbers,
`0 < 1 < 2 < …`. It answers exactly the question the LTL literature means by
"is this formula valid" — a strictly narrower, better-behaved question than
every OTHER route in the kit that touches these same operator names.

The procedure is complete without a limit, and two limits can be set. `max_atoms`
(default 4096) caps the atoms of the closure; `timeout` (milliseconds, default none) ends
the search at a deadline that is read while the atoms and the graph between them are built
and in every later step. When either is reached `ltl_decide` answers `'unknown'` (`ltl_valid`
and `ltl_tableau_closed` return `False`, `ltl_countermodel` returns `None`), never a verdict
that was not reached.

## Why a fourth route, and how it differs from the other three

`Ⓖ`/`Ⓕ`/`Ⓝ`/`Ⓤ` and their past mirrors are already familiar from {doc}`modal`
and {doc}`quantified-modal`: the kit's Kripke semantics for these operators
({mod}`unicode_logic_kit.semantics.kripke`) is deliberately **not** standard
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
from unicode_logic_kit import MSFLParser
from unicode_logic_kit.atp.ltl_tableau import ltl_valid

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
from unicode_logic_kit import MSFLParser
from unicode_logic_kit.atp.ltl_tableau import ltl_valid
from unicode_logic_kit.fol.qml import qml_is_valid

mp = MSFLParser(modal=True)
ti = mp.parse("(P ∧ Ⓖ(P → Ⓝ P)) → Ⓖ P")

ltl_valid(ti)    # → True   -- this module decides it directly
qml_is_valid(ti) # → False  -- the FO embedding cannot reach it
```

## A worked example: a non-theorem, with an explicit lasso countermodel

`Ⓖ Ⓕ P → Ⓕ Ⓖ P` ("p infinitely often" implies "p forever from some point
on") is the standard non-theorem from Baier & Katoen, ch. 5:

```python
from unicode_logic_kit import MSFLParser
from unicode_logic_kit.atp.ltl_tableau import (
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

`cm` is an {class}`~unicode_logic_kit.atp.ltl_tableau.LTLTrace`: an explicit
finite prefix (`[]`, i.e. p false at position 0) plus an infinitely-repeating
cycle (`['P'], []` — p alternates true/false forever). Every countermodel
this module returns has already been checked against
{func}`~unicode_logic_kit.atp.ltl_tableau.ltl_trace_satisfies` before you see
it — a direct, from-the-semantic-equations evaluator, independent of the
tableau's own closure/graph machinery — so it never comes back spurious:

```python
ltl_trace_satisfies(gf_fg, cm)   # → False, confirming the model above
```

A sorted constant `c:S` (read by `MSFLParser(modal=True, many_sorted=True)`) is the constant
`c` and lies in `S` at every position, a constant being a rigid designator: `Mortal(c:S)` and
`Mortal(c)` are one letter, and `S(c)` is true at every position. The procedure adds `Always S(c)`
to what it decides (and `Historically S(c)` in floating mode, where the position may have a
past), and a countermodel word is released only if it is such a model. `ltl_trace_satisfies`
reads a sorted constant the same way: `Mortal(carl:Human)` is read at the key `'Mortal(carl)'`, the
key of every countermodel trace (it does not check that `Human(carl)` holds in the trace you give
it). It refuses, by name, two
different atoms that print alike (the numeral `1` and a constant named `1`, a free variable `x` and a
constant named `x`), which one key of a trace could not tell apart:

```python
sp = MSFLParser(modal=True, many_sorted=True)

ltl_valid(sp.parse("Ⓖ Human(carl:Human)"))                      # → True   carl is a Human from every position on
ltl_valid(sp.parse("⒣ Human(carl:Human)"), mode="floating")     # → True   and at every position before
ltl_countermodel(sp.parse("Ⓕ Mortal(carl:Human)")).to_dict()   # → {'kind': 'ltl_lasso', 'prefix': [['Human(carl)']], 'cycle': [['Human(carl)']], 'witness_position': 0}

from unicode_logic_kit.atp.ltl_tableau import LTLTrace

mortal_now = LTLTrace(prefix=(frozenset({"Mortal(carl)"}),), cycle=(frozenset(),))
ltl_trace_satisfies(sp.parse("Mortal(carl:Human)"), mortal_now)   # → True   the key is 'Mortal(carl)'; 'Human(carl)' is not held, and not checked
```

## As a ProverBackend

`ltl_tableau.LtlTableauBackend` is registered under `"ltl-tableau"`, so it
joins {func}`~unicode_logic_kit.atp.protocol.get_backend` alongside
`modal-tableau` / `qml` / `isabelle`:

```python
from unicode_logic_kit.atp.protocol import get_backend

backend = get_backend("ltl-tableau")
backend.decide(ti).status      # → 'proved'
backend.decide(gf_fg).status   # → 'refuted'
```

`decide` takes the call's `timeout` (milliseconds, 10000 by default) and the options `mode` and
`max_atoms`. A search the deadline ended answers `unknown` with reason `timeout`, including one
that was still building the graph; one that reached `max_atoms` answers `unknown` with reason
`bound_hit`:

```python
v = backend.decide(gf_fg, timeout=0)       # a limit that is already over
(v.status, v.reason)                       # → ('unknown', 'timeout')
v = backend.decide(gf_fg, max_atoms=1)     # a closure of more than one atom
(v.status, v.reason)                       # → ('unknown', 'bound_hit')

ltl_decide(ti, timeout=0)                  # → 'unknown'
ltl_valid(ti, timeout=0)                   # → False   ti is valid, but False says only "not reached"
```

It is deliberately **not** part of `default_chain("modal")`: this backend
answers a strictly narrower question (the standard linear frame) than the
rest of that chain, so — like the external provers — it must be reached by
name rather than silently joining a portfolio that assumes a shared frame
class. `atp.modal_tableau`'s own "(G/F/U/…) have no tableau rule here" message now
names it as the definitive route for the standard reading, alongside `qml`
and `isabelle` for the general (possibly non-linear) frame.

## What this module refuses

Only the fragment above — classical connectives plus the eight temporal
operators. A `Box`, `Knows`, a quantifier, or any other modal/hybrid/PAL
construct raises `NotImplementedError` naming it, rather than being
approximated:

```python
from unicode_logic_kit import Box, Atom
from unicode_logic_kit.atp.ltl_tableau import ltl_valid

ltl_valid(Box(Atom("P", [])))
# raises NotImplementedError: ltl_tableau: no rule for Box (...) — this module
#   decides only the propositional temporal-closure fragment ... use
#   atp.modal_tableau, fol.qml.qml_is_valid, or
#   hol.isabelle_runner.isabelle_decide_modal for anything else.
```

An equality or disequality atom (`dora = dora`, `dora ≠ cleo`) is refused by name too, at every
entry point and in `ltl_trace_satisfies`. The tableau reads an atom as a propositional letter,
and a letter is not valid: it would call `dora = dora` refutable, with a countermodel in which
the letter is false although identity is reflexive. The backend answers `unknown` with reason
`unsupported`. Decide identity with `fol.qml.qml_is_valid` or another first-order route:

```python
v = backend.decide(mp.parse("dora = dora"))
(v.status, v.reason)                          # → ('unknown', 'unsupported')

ltl_valid(mp.parse("dora = dora"))
# raises NotImplementedError: ltl_tableau: the equality atom 'dora = dora' ('=') is refused by name ...
```

Use {doc}`modal` (`atp.modal_tableau`) for the alethic/epistemic/doxastic/
deontic fragment, and {doc}`quantified-modal` (`fol.qml`) or
`hol.isabelle_runner.isabelle_decide_modal` for quantified or non-linear
temporal reasoning.
