# Modal, temporal, epistemic & deontic logic

`MSFLParser(modal=True)` parses one-relation modal logic — alethic `□`/`◇`, epistemic `K_a`/`B_a`, deontic `Ⓞ`/`Ⓟ`, and tense operators — and the kit evaluates it directly over Kripke models, translates it to classical FOL, and (new in 0.9.0) **decides** the propositional fragment in-process with a labelled modal tableau over the standard frame systems.

## Parsing modal mode

`modal=True` is classical unsorted FOL plus the modal operators. It does not combine with `many_sorted`, `fuzzy`, or `second_order`.

```python
from unicode_fol_kit import MSFLParser

mp = MSFLParser(modal=True)

mp.parse("□P → ◇P")     # Implies(Box(P), Diamond(P))
mp.parse("K_alice P")    # Knows(Constant('alice'), P)   — epistemic
mp.parse("B_a P")        # Believes(Constant('a'), P)     — doxastic
mp.parse("Ⓖ P")         # Always(P)        — temporal "henceforth"
mp.parse("Ⓕ P")         # Eventually(P)
mp.parse("Ⓝ P")         # Next(P)
mp.parse("P Ⓤ Q")       # Until(P, Q)      — infix binary
mp.parse("Ⓞ P → Ⓟ P")  # Implies(Obligatory(P), Permitted(P))   — deontic
```

The operator set is `□ ◇` (alethic), `K_a B_a` (epistemic/doxastic), `Ⓖ Ⓕ Ⓝ Ⓤ` (temporal), and `Ⓞ Ⓟ` (obligation/permission). `Ⓤ` (Until) and its past-tense mirror `⒮` (Since) are **infix** binary operators; the rest are prefix.

The agent of `K_a` / `B_a` is a **first-class term**, so a bound `K_x` quantifies over agents:

```python
mp.parse("∀x (Student(x) → K_x Loves(x, logic))")
# Quantifier('∀', x, Implies(Student(x), Knows(Variable('x'), Loves(x, logic))))
# → x is bound, so K_x ranges over agents; a free K_a stays the named agent Constant('a').
```

## Evaluating over a Kripke model

`satisfies_modal(formula, model, world)` evaluates a modal formula at a world of a `KripkeModel`. A model is built from worlds, **named** accessibility relations, and a valuation mapping each world to the set of ground-atom keys (an atom key is `atom.to_unicode_str()`) true there. The recognised relation names are `"alethic"` (`□`/`◇`), `"K:"+agent`, `"B:"+agent`, `"deontic"` (`Ⓞ`/`Ⓟ`), and `"temporal"` (the tense operators).

```python
from unicode_fol_kit import KripkeModel, satisfies_modal, Atom, Box, Diamond

p = Atom("P", [])
m = KripkeModel(
    worlds={0, 1},
    relations={"alethic": {(0, 1)}},   # world 0 sees world 1
    valuation={1: {"P"}},              # P holds only at world 1
)

satisfies_modal(Box(p), m, 0)      # → True   (every successor of 0 satisfies P)
satisfies_modal(Diamond(p), m, 0)  # → True   (some successor satisfies P)
satisfies_modal(p, m, 0)           # → False  (P is not true at world 0 itself)
```

## Standard translation to FOL

`standard_translation(formula, world="w")` rewrites a modal formula into classical first-order logic over an explicit current-world term: an atom `P` becomes `P(w)`, `□φ` becomes `∀w' (R(w, w') → ST(φ, w'))`, and `◇φ` becomes `∃w' (R(w, w') ∧ ST(φ, w'))`. Fresh world variables `w0, w1, …` keep nested modalities from capturing each other. The result is ordinary FOL, so Z3 or the resolution prover can reason about it.

```python
from unicode_fol_kit import MSFLParser, standard_translation

mp = MSFLParser(modal=True)

standard_translation(mp.parse("□P → ◇P")).to_unicode_str()
# → '∀w0 (R(w, w0) → P(w0)) → ∃w1 (R(w, w1) ∧ P(w1))'

standard_translation(mp.parse("K_a P")).to_unicode_str()
# → '∀w0 (Rk_a(w, w0) → P(w0))'   — the epistemic relation is keyed by the agent
```

`Until` and `Since` are **not** first-order definable (they need the transitive closure of the temporal relation) and `standard_translation` rejects them — evaluate those with `satisfies_modal` instead.

## Deciding modal validity — the native tableau (0.9.0)

`unicode_fol_kit.atp.modal_tableau` decides the propositional box/diamond family in-process with a **labelled** analytic tableau. The public entry points are `is_modal_valid`, `modal_decide`, `modal_countermodel`, `modal_prove`, and `modal_tableau_closed`; all take a `frame=` naming the alethic system, one of **K, T, D/KD, B/KB, K4, K45, S4, S5, KD45**.

`is_modal_valid(φ, frame=…)` returns `True` only when the tableau for `¬φ` closes (a sound proof). The reflexivity axiom `□P → P` (the **T** schema) is valid over a reflexive frame but not over the minimal **K**:

```python
from unicode_fol_kit import is_modal_valid, Atom, Box, Implies

p = Atom("P", [])
T = Implies(Box(p), p)        # □P → P

is_modal_valid(T, frame="T")  # → True   (reflexive frame validates T)
is_modal_valid(T, frame="K")  # → False  (no closed tableau — invalid)

four = Implies(Box(p), Box(Box(p)))   # □P → □□P  (the 4 schema)
is_modal_valid(four, frame="K4")  # → True   (transitive frame validates 4)
is_modal_valid(four, frame="T")   # → False  (T alone is not transitive)
```

`modal_decide` sharpens the bool into a three-way verdict — `"valid"`, `"invalid"`, or `"unknown"`:

```python
from unicode_fol_kit import modal_decide

modal_decide(T, frame="T")     # → 'valid'
modal_decide(T, frame="K")     # → 'invalid'
modal_decide(four, frame="S4") # → 'valid'
```

The `"invalid"` verdict is backed by a **verified counter-model**: `modal_countermodel(φ, frame=…)` returns a `KripkeModel` falsifying `φ`, but only after `satisfies_modal` confirms the formula really is false at its root world (an unverifiable open branch downgrades to `"unknown"` rather than risk a wrong verdict). It returns `None` when the formula is valid.

```python
from unicode_fol_kit import modal_countermodel, satisfies_modal

cm = modal_countermodel(T, frame="K")        # □P → P over K
satisfies_modal(T, cm, 0)                     # → False   (independently re-checked)
modal_countermodel(T, frame="T")             # → None     (valid over T)
```

The counter-model for `□P → P` over **K** is the single dead-end world `0` with no accessibility edges and no atoms true: `□P` holds vacuously there while `P` is false, so the conditional is falsified.

`modal_prove(premises, conclusion, frame=…)` decides local consequence (does `premises ∪ {¬conclusion}` close at one world):

```python
from unicode_fol_kit import modal_prove

modal_prove([Box(p)], p, frame="T")  # → True   (□P ⊨ P over a reflexive frame)
modal_prove([Box(p)], p, frame="K")  # → False
```

### Epistemic, doxastic, and deontic systems

The `frame=` argument fixes the **alethic** relation only. Epistemic (`K_a`), doxastic (`B_a`), deontic (`Ⓞ`/`Ⓟ`), and temporal relations take their systems from a separate `systems=` mapping. Knowledge is normally factive (a reflexive epistemic system gives `K_a P → P`); belief is not.

```python
from unicode_fol_kit import is_modal_valid, Knows, Believes, Obligatory, Permitted

KaP = Implies(Knows("a", p), p)        # K_a P → P  (factivity)
is_modal_valid(KaP, frame="K", systems={"epistemic": "S5"})   # → True
is_modal_valid(KaP, frame="T")                                 # → False
#   ↑ frame='T' is the *alethic* system; the epistemic relation is still K, so K_a P → P is invalid.

BaP = Implies(Believes("a", p), p)     # B_a P → P  (belief is not factive)
is_modal_valid(BaP, frame="K", systems={"doxastic": "KD45"})  # → False

OPtoPP = Implies(Obligatory(p), Permitted(p))   # Ⓞ P → Ⓟ P
is_modal_valid(OPtoPP, frame="K", systems={"deontic": "D"})  # → True   (serial = D)
is_modal_valid(OPtoPP, frame="K", systems={"deontic": "K"})  # → False
```

### `is_valid_tableau` now decides modal inputs

The classical analytic-tableau entry points route modal formulas to this engine instead of raising. `is_valid_tableau(φ)` checks validity over the default **K** frame for a modal `φ`, and stays the ordinary propositional decision procedure for classical input:

```python
from unicode_fol_kit import is_valid_tableau, MSFLParser

is_valid_tableau(Implies(Box(p), p))                    # → False  (□P → P invalid over K)
is_valid_tableau(MSFLParser().parse("P ∨ ¬P"))          # → True   (classical tautology)
```

## Past-tense temporal operators (0.9.0)

The Prior tense-logic duals run over the **converse** of the one-step `"temporal"` relation: `Historically` (`⒣`, "always in the past"), `Once` (`⒫`, "at some past point"), `Previous` (`⒴`, the immediate predecessor), and the binary `Since` (`⒮`). They are covered by the parser, `satisfies_modal`, the standard translation, and the qml embedding.

```python
from unicode_fol_kit import KripkeModel, satisfies_modal, Atom, Once, Historically, Previous

p = Atom("P", [])
# A linear flow of time 0 → 1 → 2, with P true only at the start.
tm = KripkeModel(
    worlds={0, 1, 2},
    relations={"temporal": {(0, 1), (1, 2)}},
    valuation={0: {"P"}},
)

satisfies_modal(Once(p), tm, 2)          # → True   (P held at some earlier world)
satisfies_modal(Previous(p), tm, 1)      # → True   (the immediate predecessor 0 has P)
satisfies_modal(Historically(p), tm, 2)  # → False  (world 1 in the past lacks P)
```

## More frames: B, S4.2, S4.3, GL

For richer frame conditions, `qml_is_valid` decides validity through the first-order shallow embedding (Z3), and the higher-order exporters cover frames that are not first-order definable.

`B` (Brouwer), `S4.2` (convergent / directed), and `S4.3` (linear / connected) are first-order definable, so `qml_is_valid(φ, frame=…)` decides them directly:

```python
from unicode_fol_kit import qml_is_valid, Atom, Box, Diamond, Implies

p = Atom("P", [])

qml_is_valid(Implies(Box(p), p), frame="B")   # → True   (T derivable in B)
qml_is_valid(Implies(Box(p), p), frame="K")   # → False

five = Implies(Diamond(p), Box(Diamond(p)))   # ◇P → □◇P  (the 5 schema)
qml_is_valid(five, frame="S5")  # → True
qml_is_valid(five, frame="S4")  # → False

g1 = Implies(Diamond(Box(p)), Box(Diamond(p)))   # the .2 / convergence schema
qml_is_valid(g1, frame="S4.2")  # → True
qml_is_valid(g1, frame="S4")    # → False
```

`GL` (Gödel–Löb provability) is transitive + converse-well-founded, which is **not** first-order definable, so `qml_is_valid(…, frame="GL")` raises `NotImplementedError`. GL is reached only through the higher-order exporters `to_thf_modal` / `to_isabelle_modal`, which assert the Löb schema in HOL. These emit a sound problem file but do not themselves run a prover:

```python
from unicode_fol_kit import to_thf_modal, Atom, Box, Implies

p = Atom("P", [])
loeb = Implies(Box(Implies(Box(p), p)), Box(p))   # Löb's theorem  □(□P → P) → □P
thf = to_thf_modal(loeb, frame="GL")              # a TPTP THF problem string
# → run it through a higher-order prover (Leo-III / Satallax); the kit does not invoke one.
```
