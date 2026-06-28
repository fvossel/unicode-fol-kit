# Quantified Modal Logic

Combining the modalities with `∀x` / `∃x` gives **quantified modal logic** (QML), where validity turns on how the individual domain varies between worlds. `unicode-fol-kit` handles QML both *semantically* (a `KripkeModel` with per-world domains and an actualist `satisfies_modal`) and via two **shallow embeddings** in the Benzmüller style — a first-order one decided by Z3, and a higher-order one exported as TPTP THF.

## Building modal formulas as nodes

Every example below builds the AST directly from `unicode_fol_kit`, so no parser is involved. A modal formula mixes the modal nodes `Box` / `Diamond` with the ordinary first-order nodes `Quantifier` / `Atom` / `Variable`. The Barcan formula `◇∃x A(x) → ∃x ◇A(x)` and its converse are the standard litmus tests for the domain regime, and the kit exports them ready-made as `BARCAN` / `CONVERSE_BARCAN`:

```python
from unicode_fol_kit import (
    Box, Diamond, Quantifier, Atom, Variable, Implies,
    BARCAN, CONVERSE_BARCAN,
)

x = Variable("x")
A = lambda t: Atom("A", [t])

# Barcan formula:  ◇∃x A(x) → ∃x ◇A(x)
bf  = Implies(Diamond(Quantifier("∃", x, A(x))),
              Quantifier("∃", x, Diamond(A(x))))
# Converse Barcan: ∃x ◇A(x) → ◇∃x A(x)
cbf = Implies(Quantifier("∃", x, Diamond(A(x))),
              Diamond(Quantifier("∃", x, A(x))))

bf  == BARCAN           # → True
cbf == CONVERSE_BARCAN  # → True
```

`Quantifier(type, variable, formula)` takes `"∃"` / `"exists"` (or `"∀"` / `"forall"`) as its type; the bound variable is a `Variable`. `Box` and `Diamond` each wrap a single subformula.

## Semantics: per-world domains and actualist quantifiers

Build a `KripkeModel` with per-world object domains — `domains={w: {...}}` for a varying domain, or `domain={...}` for a single constant domain shared by every world. `satisfies_modal(φ, model, world)` then interprets `∀x` / `∃x` **actualistically**: at a world `w` they range over `D_w`, the objects that exist *at that world*. This is the ground truth against which the embeddings are cross-checked.

The Barcan formula is valid under constant domains but **fails when domains grow**, because an object can appear only in a successor world:

```python
from unicode_fol_kit import BARCAN, satisfies_modal
from unicode_fol_kit.semantics.kripke import KripkeModel

rel = {"alethic": {(0, 1)}}   # world 0 sees world 1

constant = KripkeModel(
    worlds={0, 1}, relations=rel,
    valuation={1: {"A(b)"}}, domain={"a", "b"},
)
increasing = KripkeModel(
    worlds={0, 1}, relations=rel,
    valuation={1: {"A(b)"}}, domains={0: {"a"}, 1: {"a", "b"}},
)

satisfies_modal(BARCAN, constant, 0)     # → True
satisfies_modal(BARCAN, increasing, 0)   # → False
```

Under `increasing`, `b` exists only at world 1: `◇∃x A(x)` holds at world 0 (a `b` with `A(b)` is reachable), but `∃x ◇A(x)` fails because no object *in `D_0`* possibly satisfies `A`. `satisfies_modal` is also the way to obtain a definite countermodel — it is a complete brute-force oracle over the explicit model.

## (A) First-order shallow embedding → Z3

`qml_translate` rewrites a modal formula into classical FOL — quantifiers over worlds for the modalities, and an existence predicate `E!` relativising the actualist object quantifiers — and `qml_is_valid(φ, mode, frame)` decides validity with **Z3**. The `mode` is the domain regime (`"constant"`, `"increasing"` / `"cumulative"`, `"decreasing"`, `"varying"`) and `frame` ∈ {`K`, `T`, `S4`, `S5`, `KD`, `KD45`}.

```python
from unicode_fol_kit import qml_is_valid, qml_equivalent, BARCAN, CONVERSE_BARCAN

qml_is_valid(BARCAN, mode="constant")           # → True
qml_is_valid(BARCAN, mode="increasing")         # → False
qml_is_valid(BARCAN, mode="decreasing")         # → True

qml_is_valid(CONVERSE_BARCAN, mode="increasing")  # → True
qml_is_valid(CONVERSE_BARCAN, mode="decreasing")  # → False
qml_is_valid(BARCAN, mode="varying")              # → False
```

The correspondence (verified against the Kripke enumerator) is: **BF ⇔ decreasing** domains, **CBF ⇔ increasing**, and **constant ⇔ both**. Since both formulas are valid under constant domains, they are QML-equivalent there:

```python
qml_equivalent(BARCAN, CONVERSE_BARCAN, mode="constant")   # → True
```

`qml_equivalent(left, right, mode, frame)` is just `qml_is_valid` of the biconditional. This embedding is **sound but bounded-incomplete**: first-order modal logic is undecidable, so a `False` may mean "Z3 did not prove validity within the bound" rather than "definitely invalid" — use `satisfies_modal` on an explicit model for a guaranteed countermodel.

## (B) Higher-order shallow embedding → TPTP THF

`to_thf_modal(φ, mode, frame)` emits a complete Benzmüller-style **TPTP THF** problem for an external higher-order prover (Leo-III, Satallax). A modal proposition is a function `mu > $o` (world → bool); the modalities are λ-lifted quantifiers over the accessibility relation `r`, and object quantifiers are `existsAt`-guarded (actualist). The frame and domain regime are encoded as axioms.

```python
from unicode_fol_kit import to_thf_modal, BARCAN

thf = to_thf_modal(BARCAN, mode="constant", frame="S5")
type(thf)                  # → <class 'str'>
thf.splitlines()[0]
# → "% Shallow embedding of a quantified modal formula (mode=constant, frame=S5)."
"thf(mbox," in thf         # → True   (lifted operators mbox/mdia/mforall/mexists are defined)
```

The function **emits** the problem (like the other `to_*` exporters); it does not run a prover in-process. The conjecture comes out a `Theorem` for the prover exactly when the formula is QML-valid under the given regime. This covers the alethic □/◇ fragment; for the full modal family (epistemic / doxastic / deontic / temporal) and a loadable Isabelle theory, see the higher-order proving page.
