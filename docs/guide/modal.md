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
mp.parse("Say_a P")      # Says(Constant('a'), P)         — assertive (non-factive)
mp.parse("Want_a P")     # Wants(Constant('a'), P)        — bouletic (non-veridical)
mp.parse("Ⓖ P")         # Always(P)        — temporal "henceforth"
mp.parse("Ⓕ P")         # Eventually(P)
mp.parse("Ⓝ P")         # Next(P)
mp.parse("P Ⓤ Q")       # Until(P, Q)      — infix binary
mp.parse("Ⓞ P → Ⓟ P")  # Implies(Obligatory(P), Permitted(P))   — deontic
```

The operator set is `□ ◇` (alethic), `K_a B_a` (epistemic/doxastic), `Say_a Want_a` (assertive/bouletic), `Ⓖ Ⓕ Ⓝ Ⓤ` (temporal), and `Ⓞ Ⓟ` (obligation/permission). `Ⓤ` (Until) and its past-tense mirror `⒮` (Since) are **infix** binary operators; the rest are prefix. `Says` is non-factive and non-doxastic, `Wants` non-veridical (each a minimal **K** modality over its own relation) — see {doc}`natural-language`.

Every modal operator has its own AST node; parsing returns the node tree, and `to_unicode_str` renders it back (note the prefix operators print without the space you may type):

```python
mp.parse("□P → ◇P")
# → Implies(Box(Atom('P', [])), Diamond(Atom('P', [])))

mp.parse("Ⓞ P → Ⓟ P").to_unicode_str()  # → 'ⓄP → ⓅP'  (deontic prefixes print tight)
mp.parse("P Ⓤ Q").to_unicode_str()       # → 'P Ⓤ Q'     (Until stays infix)
mp.parse("K_alice P").to_unicode_str()   # → 'K_alice P'
```

The same nodes are available directly from the top-level package, so you can build a formula without the parser — handy when an example needs a precise tree:

```python
from unicode_fol_kit import Atom, Box, Diamond, Implies

p = Atom("P", [])
Implies(Box(p), Diamond(p))             # □P → ◇P, built by hand
# → Implies(Box(Atom('P', [])), Diamond(Atom('P', [])))
```

Modal nodes render to LaTeX (`to_latex`) and round-trip through `to_dict` / `Node.from_dict`, exactly like the classical nodes:

```python
from unicode_fol_kit import Node

mp.parse("□P → ◇P").to_latex()   # → '\\Box P \\rightarrow \\Diamond P'
mp.parse("K_a P").to_latex()     # → 'K_{a} P'
mp.parse("Ⓞ P").to_latex()      # → '\\mathsf{O} P'
mp.parse("⒫ P").to_latex()      # → '\\overline{\\mathsf{P}} P'  (past "once")

f = mp.parse("K_a (P → ◇Q)")
Node.from_dict(f.to_dict()) == f  # → True   (serialisation round-trips)
```

The agent of `K_a` / `B_a` / `Say_a` / `Want_a` is a **first-class term**, so a bound `K_x` quantifies over agents:

```python
mp.parse("∀x (Student(x) → K_x Loves(x, logic))")
# Quantifier('∀', x, Implies(Student(x), Knows(Variable('x'), Loves(x, logic))))
# → x is bound, so K_x ranges over agents; a free K_a stays the named agent Constant('a').

mp.parse("K_a P")    # → Knows(Constant('a'), Atom('P', []))   — free agent → named Constant
mp.parse("Say_a P")  # → Says(Constant('a'), Atom('P', []))
mp.parse("Want_a P") # → Wants(Constant('a'), Atom('P', []))
```

### Nested modalities

Modal operators nest freely. Combine epistemic and alethic operators, or stack the same operator multiple levels deep:

```python
mp.parse("K_a □P")        # → Knows(Constant('a'), Box(Atom('P', [])))  — agent knows possibility
mp.parse("□□P")           # → Box(Box(Atom('P', [])))  — nested necessity
mp.parse("K_a K_b P → K_a P")  # multi-agent reasoning
```

Nested modalities have distinct scopes:

```python
mp.parse("∀x (K_x P → ∃y R(x, y))")
# Quantifier('∀', x, Implies(Knows(Variable('x'), Atom('P', [])), Quantifier('∃', y, R(x, y))))
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

`Box` is universal over successors and `Diamond` existential, so at a **dead-end** world (no outgoing edges) `□φ` is vacuously true and `◇φ` is false:

```python
dead = KripkeModel(worlds={0})        # no relations, no atoms
satisfies_modal(Box(p), dead, 0)      # → True   (vacuous: nothing to refute it)
satisfies_modal(Diamond(p), dead, 0)  # → False  (no successor can witness it)
```

`Box` fails as soon as one successor lacks `P`, while `Diamond` only needs one that has it:

```python
m2 = KripkeModel(
    worlds={0, 1, 2},
    relations={"alethic": {(0, 1), (0, 2)}},
    valuation={1: {"P"}},              # P at world 1 only
)
satisfies_modal(Box(p), m2, 0)      # → False  (world 2 lacks P)
satisfies_modal(Diamond(p), m2, 0)  # → True   (world 1 has P)
```

An atom with arguments is keyed by its **rendered** Unicode string (`atom.to_unicode_str()`), so a binary atom's valuation key is `"Likes(a, b)"`:

```python
from unicode_fol_kit import Constant

likes = Atom("Likes", [Constant("a"), Constant("b")])
likes.to_unicode_str()                # → 'Likes(a, b)'   — this is the valuation key
mk = KripkeModel(
    worlds={0, 1},
    relations={"alethic": {(0, 1)}},
    valuation={1: {"Likes(a, b)"}},   # use the rendered key, spaces and all
)
satisfies_modal(Box(likes), mk, 0)    # → True
```

Combine multiple agents with their own epistemic relations:

```python
from unicode_fol_kit import Knows

multi_em = KripkeModel(
    worlds={0, 1, 2},
    relations={
        "K:alice": {(0, 0), (0, 1), (1, 0), (1, 1)},
        "K:bob": {(0, 0), (0, 2), (2, 0), (2, 2)},
    },
    valuation={0: {"P"}, 1: {"P"}, 2: {"Q"}},
)

satisfies_modal(Knows("alice", p), multi_em, 0)  # → True
satisfies_modal(Knows("bob", p), multi_em, 0)    # → False
```

### Epistemic, doxastic, assertive, bouletic, deontic models

The same evaluator handles every modality by reading the relation under its own key — `"K:"+agent` for `Knows`, `"B:"+agent` for `Believes`, `"Say:"+agent` for `Says`, `"Want:"+agent` for `Wants`, `"deontic"` for `Obligatory`/`Permitted`. **Knowledge** is the universal modality over an agent's indistinguishability relation: agent `alice` *knows* `P` at a world iff `P` holds in every world she cannot tell apart from it.

```python
from unicode_fol_kit import Knows

# alice cannot distinguish worlds 0 and 1; P is true at both → she knows P.
em = KripkeModel(
    worlds={0, 1},
    relations={"K:alice": {(0, 0), (0, 1), (1, 0), (1, 1)}},
    valuation={0: {"P"}, 1: {"P"}},
)
satisfies_modal(Knows("alice", p), em, 0)  # → True

# Same indistinguishability, but P fails at world 1 → she does NOT know P,
# though she still considers it possible (¬K_a ¬P).
em2 = KripkeModel(
    worlds={0, 1},
    relations={"K:alice": {(0, 0), (0, 1), (1, 0), (1, 1)}},
    valuation={0: {"P"}},                  # P false at world 1
)
satisfies_modal(Knows("alice", p), em2, 0)            # → False
satisfies_modal(Not(Knows("alice", Not(p))), em2, 0)  # → True   (P is epistemically possible)
```

`Says` is **non-factive** and `Wants` **non-veridical** — what is asserted or wanted need not be true at the actual world (the relation simply points elsewhere):

```python
from unicode_fol_kit import Says, Wants

# a SAYS P, but P is false at the actual world 0.
sm = KripkeModel(worlds={0, 1}, relations={"Say:a": {(0, 1)}}, valuation={1: {"P"}})
satisfies_modal(Says("a", p), sm, 0)  # → True
satisfies_modal(p, sm, 0)             # → False  (the assertion is false — Says is non-factive)

# a WANTS to fly, but does not actually fly.
fly = Atom("Fly", [])
wm = KripkeModel(worlds={0, 1}, relations={"Want:a": {(0, 1)}}, valuation={1: {"Fly"}})
satisfies_modal(Wants("a", fly), wm, 0)  # → True
satisfies_modal(fly, wm, 0)              # → False  (wanting it does not make it so)
```

**Obligation** is the universal box and **permission** the existential diamond over the `"deontic"` relation; over a serial relation (some successor exists) whatever is obligatory is permitted:

```python
from unicode_fol_kit import Obligatory, Permitted

dm = KripkeModel(worlds={0, 1}, relations={"deontic": {(0, 1)}}, valuation={1: {"P"}})
satisfies_modal(Obligatory(p), dm, 0)  # → True   (P holds in the one ideal world)
satisfies_modal(Permitted(p), dm, 0)   # → True   (… so P is permitted there too)
```

**Dead-end deontic world** (no idealized successors) makes all obligations vacuously true but nothing permitted:

```python
dead_deontic = KripkeModel(worlds={0})
satisfies_modal(Obligatory(p), dead_deontic, 0)  # → True
satisfies_modal(Permitted(p), dead_deontic, 0)   # → False
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

Each modality picks its own accessibility predicate: `R` (alethic), `Rk_a` / `Rb_a` (epistemic/doxastic, keyed by agent), `D` (deontic), `T` (temporal `Ⓖ`/`Ⓕ`), `N` (`Ⓝ`). Boxes become `∀` over an implication, diamonds `∃` over a conjunction:

```python
standard_translation(mp.parse("B_a P")).to_unicode_str()  # → '∀w0 (Rb_a(w, w0) → P(w0))'
standard_translation(mp.parse("Ⓞ P")).to_unicode_str()   # → '∀w0 (D(w, w0) → P(w0))'
standard_translation(mp.parse("Ⓟ P")).to_unicode_str()   # → '∃w0 (D(w, w0) ∧ P(w0))'
standard_translation(mp.parse("Ⓖ P")).to_unicode_str()   # → '∀w0 (T(w, w0) → P(w0))'
standard_translation(mp.parse("Ⓕ P")).to_unicode_str()   # → '∃w0 (T(w, w0) ∧ P(w0))'
standard_translation(mp.parse("Ⓝ P")).to_unicode_str()   # → '∀w0 (N(w, w0) → P(w0))'
```

Fresh world variables `w0, w1, …` keep **nested** modalities from capturing each other, and a non-propositional atom keeps its own arguments with the world appended last:

```python
standard_translation(mp.parse("□□P")).to_unicode_str()
# → '∀w0 (R(w, w0) → ∀w1 (R(w0, w1) → P(w1)))'

standard_translation(Box(Atom("Likes", [Constant("a"), Constant("b")]))).to_unicode_str()
# → '∀w0 (R(w, w0) → Likes(a, b, w0))'   — the world is appended as the last argument
```

The `world=` argument names the free current-world variable (default `"w"`); the past-tense operators translate over the **converse** of their relation (`T(w0, w)`, `N(w0, w)`):

```python
standard_translation(mp.parse("□P"), world="u").to_unicode_str()  # → '∀w0 (R(u, w0) → P(w0))'
standard_translation(mp.parse("⒫ P")).to_unicode_str()           # → '∃w0 (T(w0, w) ∧ P(w0))'  (Once)
standard_translation(mp.parse("⒣ P")).to_unicode_str()           # → '∀w0 (T(w0, w) → P(w0))'  (Historically)
standard_translation(mp.parse("⒴ P")).to_unicode_str()           # → '∀w0 (N(w0, w) → P(w0))'  (Previous)
```

The point of the translation is that the result is **ordinary FOL**, so the classical reasoners can decide a modal theorem. A modal node refuses the first-order export directly, but its translation does not — and the K distribution axiom is FOL-valid:

```python
from unicode_fol_kit import is_valid

Box(p).to_z3()                                  # raises NotImplementedError — translate first

st_K = standard_translation(mp.parse("□(P → Q) → (□P → □Q)"))
is_valid(st_K)                                  # → True   (Z3 confirms the K axiom is FOL-valid)
```

`Until` and `Since` are **not** first-order definable (they need the transitive closure of the temporal relation) and `standard_translation` rejects them — evaluate those with `satisfies_modal` instead:

```python
standard_translation(mp.parse("P Ⓤ Q"))  # raises NotImplementedError (Until is not FO-definable)
```

### Custom world variable names

Use the `world=` parameter to thread a world variable through nested formulas:

```python
q = Atom("Q", [])
nested = Box(Not(Diamond(p)))
st_default = standard_translation(nested)
st_custom = standard_translation(nested, world="s")
print(st_default.to_unicode_str())  # → '∀w0 (R(w, w0) → ¬∃w1 (R(w0, w1) ∧ P(w1)))'
print(st_custom.to_unicode_str())   # → '∀w0 (R(s, w0) → ¬∃w1 (R(w0, w1) ∧ P(w1)))'
```

## Deciding modal validity — the native tableau (0.9.0)

`unicode_fol_kit.atp.modal_tableau` decides the propositional box/diamond family in-process with a **labelled** analytic tableau. The public entry points are `is_modal_valid`, `modal_decide`, `modal_countermodel`, `modal_prove`, and `modal_tableau_closed`; all take a `frame=` naming the alethic system, one of **K, T, D/KD, B/KB, K4, K45, S4, S5, KD45**.

`is_modal_valid(φ, frame=…)` returns `True` only when the tableau for `¬φ` closes (a sound proof). The reflexivity axiom `□P → P` (the **T** schema) is valid over a reflexive frame but not over the minimal **K**:

```python
from unicode_fol_kit import is_modal_valid, Atom, Box, Diamond, Implies, And, Or, Not, Iff

p = Atom("P", [])
q = Atom("Q", [])
T = Implies(Box(p), p)        # □P → P

is_modal_valid(T, frame="T")  # → True   (reflexive frame validates T)
is_modal_valid(T, frame="K")  # → False  (no closed tableau — invalid)

four = Implies(Box(p), Box(Box(p)))   # □P → □□P  (the 4 schema)
is_modal_valid(four, frame="K4")  # → True   (transitive frame validates 4)
is_modal_valid(four, frame="T")   # → False  (T alone is not transitive)
```

Every standard schema lines up with the frame condition that validates it. The **K** distribution axiom holds over the minimal frame; **D** (`□P → ◇P`) needs seriality; **B** (`P → □◇P`) needs symmetry; **5** (`◇P → □◇P`) needs the euclidean condition:

```python
K = Implies(Box(Implies(p, q)), Implies(Box(p), Box(q)))   # □(P→Q) → (□P→□Q)
is_modal_valid(K, frame="K")                               # → True   (valid even over minimal K)

D = Implies(Box(p), Diamond(p))                            # □P → ◇P
is_modal_valid(D, frame="K")                               # → False  (K is not serial)
is_modal_valid(D, frame="D")                               # → True   (serial frame validates D)
is_modal_valid(D, frame="T")                               # → True   (reflexive ⇒ serial)

B = Implies(p, Box(Diamond(p)))                            # P → □◇P
is_modal_valid(B, frame="B")                               # → True   (symmetric frame validates B)
is_modal_valid(B, frame="T")                               # → False  (T is not symmetric)
is_modal_valid(B, frame="S5")                              # → True

five = Implies(Diamond(p), Box(Diamond(p)))               # ◇P → □◇P  (the 5 schema)
is_modal_valid(five, frame="S5")                           # → True
is_modal_valid(five, frame="K45")                          # → True   (transitive + euclidean)
is_modal_valid(five, frame="S4")                           # → False  (S4 is not euclidean)
```

The accepted frames are **K, T, D/KD, B/KB, K4, K45, S4, S5, KD45** — each fixes a set of conditions on the alethic accessibility relation:

| frame | conditions | characteristic schema |
| --- | --- | --- |
| `K` | (none) | `K`: `□(P→Q) → (□P→□Q)` |
| `T` | reflexive | `T`: `□P → P` |
| `D` / `KD` | serial | `D`: `□P → ◇P` |
| `B` / `KB` | symmetric (`B` also reflexive) | `B`: `P → □◇P` |
| `K4` | transitive | `4`: `□P → □□P` |
| `K45` | transitive + euclidean | `4` + `5` |
| `S4` | reflexive + transitive | `T` + `4` |
| `S5` | reflexive + transitive + symmetric | `T` + `4` + `5` |
| `KD45` | serial + transitive + euclidean | the "doxastic" system `D` + `4` + `5` |

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

It takes any number of premises and respects the per-family `systems=`. A reflexive epistemic system makes knowledge factive, so `K_a P` entails `P`; the minimal **K** epistemic system does not:

```python
from unicode_fol_kit import Knows

modal_prove([Knows("a", p)], p, frame="K", systems={"epistemic": "S5"})  # → True
modal_prove([Knows("a", p)], p, frame="K", systems={"epistemic": "K"})   # → False
```

`modal_tableau_closed(formulas, frame=…)` is the lowest-level entry point: it returns `True` iff the listed formulas are **jointly unsatisfiable** at one world (the tableau closes). It is what `is_modal_valid(φ)` runs on `[¬φ]` and what `modal_prove` runs on the premises plus the negated conclusion:

```python
from unicode_fol_kit import modal_tableau_closed

modal_tableau_closed([p, Not(p)])               # → True   (a flat contradiction closes)
modal_tableau_closed([Box(p), Not(p)], frame="T")  # → True   (□P ⊢ P over T, contradicting ¬P)
modal_tableau_closed([Box(p), Not(p)], frame="K")  # → False  (jointly satisfiable over K)
```

### Comparing frame systems

Test the same formula across all the standard frames:

```python
from unicode_fol_kit import is_modal_valid, Implies, Box

p = Atom("P", [])
four = Implies(Box(p), Box(Box(p)))

frames = ["K", "T", "D", "B", "K4", "K45", "S4", "S5", "KD45"]
for frame in frames:
    valid = is_modal_valid(four, frame=frame)
    print(f"  {frame:5}: {valid}")
```

When a formula is valid over S5, it is automatically valid over all frames that S5 entails. But a formula valid in T is not necessarily valid in B, because T and B are incomparable.

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

**Positive** and **negative introspection** distinguish the epistemic systems. `K_a P → K_a K_a P` (the 4 schema, "you know that you know") needs a transitive epistemic relation (S4 or S5); `¬K_a P → K_a ¬K_a P` (the 5 schema, "you know what you don't know") needs the euclidean condition (S5):

```python
from unicode_fol_kit import Knows

KaP = Knows("a", p)
pos = Implies(KaP, Knows("a", Knows("a", p)))        # positive introspection (4)
is_modal_valid(pos, frame="K", systems={"epistemic": "S4"})  # → True
is_modal_valid(pos, frame="K", systems={"epistemic": "K"})   # → False

neg = Implies(Not(KaP), Knows("a", Not(KaP)))        # negative introspection (5)
is_modal_valid(neg, frame="K", systems={"epistemic": "S5"})  # → True
is_modal_valid(neg, frame="K", systems={"epistemic": "S4"})  # → False  (S4 is not euclidean)
```

Belief under **KD45** is *consistent* (you never believe both `P` and `¬P`) but still not factive — `B_a P → ¬B_a ¬P` holds while `B_a P → P` does not:

```python
BaP = Believes("a", p)
is_modal_valid(Implies(BaP, Not(Believes("a", Not(p)))),  # consistency D
               frame="K", systems={"doxastic": "KD45"})    # → True
is_modal_valid(Implies(BaP, p), frame="K", systems={"doxastic": "KD45"})  # → False (belief is not factive)
```

A `systems=` entry fixes the system for **all** agents of that family at once. So under a reflexive epistemic system, `K_b P → P` holds for every `b`, which makes `K_a K_b P → K_a P` valid; over **K** it is invalid:

```python
from unicode_fol_kit import MSFLParser, modal_decide

mp = MSFLParser(modal=True)
nested = mp.parse("K_a K_b P → K_a P")
modal_decide(nested, frame="K", systems={"epistemic": "T"})  # → 'valid'    (K_b P → P at each a-world)
modal_decide(nested, frame="K", systems={"epistemic": "K"})  # → 'invalid'
```

### Assertive `Says` and bouletic `Wants`

`Says` and `Wants` are each a **minimal K modality over their own relation, with no frame conditions** — they take no `systems=` entry (there is nothing to tune). The K distribution axiom holds (asserting `P → Q` and asserting `P` lets you derive asserting `Q`), but factivity and veridicality do **not**: saying `P` does not make `P` true, and wanting `P` does not make `P` true.

```python
from unicode_fol_kit import is_modal_valid, Says, Wants, Implies, Not, Atom

p = Atom("P", []); q = Atom("Q", [])

# K-distribution holds for Says (it is a normal modality).
say_K = Implies(Says("a", Implies(p, q)), Implies(Says("a", p), Says("a", q)))
is_modal_valid(say_K, frame="K")                  # → True

# Non-factive: Say_a P → P is INVALID (an assertion can be false).
is_modal_valid(Implies(Says("a", p), p), frame="K")   # → False

# Non-veridical: Want_a P → P is INVALID (wanting it does not make it so).
is_modal_valid(Implies(Wants("a", p), p), frame="K")  # → False
```

A counter-model makes the non-factivity concrete: `a` says `P` (so `P` holds in a's report-world) while `P` is false at the actual world.

```python
from unicode_fol_kit import modal_countermodel, satisfies_modal

cm = modal_countermodel(Implies(Says("a", p), p), frame="K")
satisfies_modal(Implies(Says("a", p), p), cm, 0)  # → False  (verified non-factive countermodel)
```

### `is_valid_tableau` now decides modal inputs

The classical analytic-tableau entry points route modal formulas to this engine instead of raising. `is_valid_tableau(φ)` checks validity over the default **K** frame for a modal `φ`, and stays the ordinary propositional decision procedure for classical input:

```python
from unicode_fol_kit import is_valid_tableau, MSFLParser

is_valid_tableau(Implies(Box(p), p))                    # → False  (□P → P invalid over K)
is_valid_tableau(MSFLParser().parse("P ∨ ¬P"))          # → True   (classical tautology)
```

## Future temporal operators over a flow of time

The future tense operators run over the one-step `"temporal"` relation: `Next` (`Ⓝ`, every immediate successor), `Always` (`Ⓖ`, "henceforth", over the reflexive-transitive closure), `Eventually` (`Ⓕ`, "finally"), and the binary `Until` (`Ⓤ`). Model time as a chain of worlds and evaluate them with `satisfies_modal`:

```python
from unicode_fol_kit import KripkeModel, satisfies_modal, Atom, Next, Always, Eventually, Until

p = Atom("P", []); q = Atom("Q", [])
# Linear flow 0 → 1 → 2 → 3: P at 0 and 1, Q at 3.
tm = KripkeModel(
    worlds={0, 1, 2, 3},
    relations={"temporal": {(0, 1), (1, 2), (2, 3)}},
    valuation={0: {"P"}, 1: {"P"}, 3: {"Q"}},
)

satisfies_modal(Next(p), tm, 0)        # → True   (P holds at the next state, world 1)
satisfies_modal(Always(p), tm, 0)      # → False  (P fails at the reachable world 2)
satisfies_modal(Eventually(q), tm, 0)  # → True   (Q is reached at world 3)
satisfies_modal(Until(p, q), tm, 0)    # → False  (P breaks at world 2, before Q at 3)
```

`Always` is the closure box and `Eventually` its dual; `Until(P, Q)` needs `P` to hold at every step **until** `Q` becomes true. Fill in `P` at world 2 and the strong Until is satisfied:

```python
tm2 = KripkeModel(
    worlds={0, 1, 2, 3},
    relations={"temporal": {(0, 1), (1, 2), (2, 3)}},
    valuation={0: {"P"}, 1: {"P"}, 2: {"P"}, 3: {"Q"}},   # P now holds up to Q
)
satisfies_modal(Until(p, q), tm2, 0)   # → True   (P holds at 0,1,2 and Q at 3)
```

The native tableau handles only the box/diamond family (including `Ⓝ`, a box over `"temporal"`); the **closure** operators `Always` / `Eventually` / `Until` need fixpoint machinery beyond a basic labelled tableau, so `is_modal_valid` and friends reject them. Decide those semantically with `satisfies_modal`, or export them via the standard translation (`Ⓖ`/`Ⓕ`/`Ⓝ`) and the qml embedding.

```python
from unicode_fol_kit import is_modal_valid

is_modal_valid(Implies(Always(p), p), frame="K")  # raises NotImplementedError (closure op)
```

### Next operator

Test what holds at the next step only:

```python
from unicode_fol_kit import Next

satisfies_modal(Next(p), tm, 0)    # → True
satisfies_modal(Next(p), tm, 1)    # → False
satisfies_modal(Next(q), tm, 1)    # → True
```

### Understanding Until: weak vs. strong

`Until(P, Q)` is strong: P must hold until Q is true, and Q must eventually be true. Weak until is satisfied if P holds forever:

```python
p_forever = KripkeModel(
    worlds={0, 1, 2},
    relations={"temporal": {(0, 1), (1, 2)}},
    valuation={0: {"P"}, 1: {"P"}, 2: {"P"}},
)

satisfies_modal(Until(p, q), p_forever, 0)  # → False
always_P_or_Q = Always(Or(p, q))
satisfies_modal(always_P_or_Q, p_forever, 0)  # → True
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

`Historically` (the past `Ⓖ`) is true at a world iff `P` held at every past point including now. At the origin world `0` of `tm` the past is just `{0}`, where `P` holds, so it is vacuously satisfied; at world `1` it fails because the present world `1` lacks `P`:

```python
satisfies_modal(Historically(p), tm, 0)  # → True   (past = {0}, and P holds at 0)
satisfies_modal(Historically(p), tm, 1)  # → False  (P fails at the present world 1)
```

The binary `Since` mirrors `Until` backwards: `Since(P, Q)` holds when `Q` was true at some past point and `P` has held at every point since. Build a flow where `Q` started things off and `P` has held since:

```python
from unicode_fol_kit import KripkeModel, satisfies_modal, Atom, Since

p = Atom("P", []); q = Atom("Q", [])
# 0 → 1 → 2: Q true at the origin 0, P true at 1 and 2.
sm = KripkeModel(
    worlds={0, 1, 2},
    relations={"temporal": {(0, 1), (1, 2)}},
    valuation={0: {"Q"}, 1: {"P"}, 2: {"P"}},
)
satisfies_modal(Since(p, q), sm, 2)  # → True   (Q held in the past, P ever since)
```

Like `Until`, `Since` is not first-order definable, so the native tableau and `standard_translation` reject it; evaluate it with `satisfies_modal`.

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

q = Atom("Q", [])
g2 = Or(Box(Implies(Box(p), q)), Box(Implies(Box(q), p)))   # the .3 / linearity schema
qml_is_valid(g2, frame="S4.3")  # → True
qml_is_valid(g2, frame="S4")    # → False
```

`qml_equivalent` decides whether two formulas are interderivable over a frame — the box/diamond duality `□P ≡ ¬◇¬P` holds over the minimal **K**, while `□P ≡ ◇P` does not:

```python
from unicode_fol_kit import qml_equivalent, Not

qml_equivalent(Box(p), Not(Diamond(Not(p))), frame="K")  # → True   (duality)
qml_equivalent(Box(p), Diamond(p), frame="K")            # → False
```

`GL` (Gödel–Löb provability) is transitive + converse-well-founded, which is **not** first-order definable, so `qml_is_valid(…, frame="GL")` raises `NotImplementedError`. GL is reached only through the higher-order exporters `to_thf_modal` / `to_isabelle_modal`, which assert the Löb schema in HOL. These emit a sound problem file but do not themselves run a prover:

```python
from unicode_fol_kit import to_thf_modal, to_isabelle_modal, modal_axiom_names, Atom, Box, Implies

p = Atom("P", [])
loeb = Implies(Box(Implies(Box(p), p)), Box(p))   # Löb's theorem  □(□P → P) → □P

qml_is_valid(loeb, frame="GL")  # raises NotImplementedError (GL is not first-order definable)

thf = to_thf_modal(loeb, frame="GL")              # a TPTP THF problem string
isinstance(thf, str)                              # → True
"thf(loeb, axiom" in thf                          # → True   (the Löb schema is asserted in HOL)
# → run it through a higher-order prover (Leo-III / Satallax); the kit does not invoke one.

iso = to_isabelle_modal(loeb, frame="GL")         # the same problem as an Isabelle theory
"theory ModalEmbedding" in iso                    # → True
```

`modal_axiom_names(φ, frame=…)` lists exactly which frame/link axioms the emitted embedding declares for `φ` — useful for knowing what a downstream prover must use. **GL** asserts transitivity plus the Löb schema; **S5** asserts the three relational conditions; **K** needs none:

```python
from unicode_fol_kit import modal_axiom_names, Atom, Box, Diamond, Implies

p = Atom("P", [])
loeb = Implies(Box(Implies(Box(p), p)), Box(p))   # □(□P → P) → □P

modal_axiom_names(loeb, frame="GL")                                          # → ['r_trans', 'r_loeb']
modal_axiom_names(Implies(Diamond(p), Box(Diamond(p))), frame="S5")          # → ['r_refl', 'r_trans', 'r_sym']
modal_axiom_names(Implies(Box(p), Diamond(p)), frame="K")                    # → []
```

## End-to-end: parse, decide, refute, translate

The pieces compose into one pipeline. Take an epistemic claim — *positive introspection* `K_a P → K_a K_a P` — parse it from Unicode, decide it over two epistemic systems, read off a verified counter-model where it fails, and hand the corresponding *valid* alethic schema to the classical FOL stack through the standard translation.

```python
from unicode_fol_kit import (
    MSFLParser, modal_decide, modal_countermodel, satisfies_modal,
    standard_translation, is_valid,
)

mp = MSFLParser(modal=True)

# 1) Parse the surface syntax.
phi = mp.parse("K_a P → K_a K_a P")
phi.to_unicode_str()                                # → 'K_a P → K_a K_a P'

# 2) Decide it: invalid over the minimal K, valid once knowledge is transitive (S4).
modal_decide(phi, frame="K", systems={"epistemic": "K"})   # → 'invalid'
modal_decide(phi, frame="K", systems={"epistemic": "S4"})  # → 'valid'

# 3) Get a verified counter-model for the K case and re-check it independently.
cm = modal_countermodel(phi, frame="K", systems={"epistemic": "K"})
satisfies_modal(phi, cm, 0)                          # → False   (the model really refutes it)

# 4) The matching alethic schema □P → □□P is the 4 axiom; its standard
#    translation is plain FOL over an explicit accessibility relation R.
st = standard_translation(mp.parse("□P → □□P"))
st.to_unicode_str()
# → '∀w0 (R(w, w0) → P(w0)) → ∀w1 (R(w, w1) → ∀w2 (R(w1, w2) → P(w2)))'
```

The bare translation of `□P → □□P` is **not** FOL-valid on its own — the 4 schema only holds when `R` is transitive, which the standard translation does not assume. Add the transitivity axiom as a hypothesis and the implication becomes a FOL theorem that Z3 confirms:

```python
from unicode_fol_kit import is_valid, Implies, MSFLParser

fp = MSFLParser()   # classical parser for the FOL hypothesis
trans = fp.parse("∀x ∀y ∀z (R(x, y) ∧ R(y, z) → R(x, z))")
st = standard_translation(mp.parse("□P → □□P"))

is_valid(st)                       # → False  (4 is not valid over an arbitrary frame)
is_valid(Implies(trans, st))       # → True   (… but transitivity ⊨ the 4 schema)
```

### Complete workflow: belief and consistency

Construct a doxastic reasoning problem, decide it over KD45, get a model, and verify it:

```python
from unicode_fol_kit import (
    Believes, Implies, Not,
    is_modal_valid, modal_countermodel, satisfies_modal
)

a = "a"
BaP = Believes(a, p)

consistency = Implies(BaP, Not(Believes(a, Not(p))))
is_modal_valid(consistency, frame="K", systems={"doxastic": "KD45"})  # → True

factivity = Implies(BaP, p)
is_modal_valid(factivity, frame="K", systems={"doxastic": "KD45"})  # → False

cm = modal_countermodel(factivity, frame="K", systems={"doxastic": "KD45"})
satisfies_modal(BaP, cm, 0)  # → True
satisfies_modal(p, cm, 0)    # → False
satisfies_modal(factivity, cm, 0)  # → False
```

For the *quantified* modal logic that combines `∀x` / `∃x` with the modalities — Barcan formulas, varying vs. constant domains, and the Z3/THF embeddings — see {doc}`quantified-modal`.
