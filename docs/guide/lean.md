# Lean 4 export: classical FOL/MSFOL and propositional modal K

`unicode_fol_kit.hol.lean` emits classical FOL / MSFOL and the propositional
**modal-K** fragment into **Lean 4** — a first vertical slice, structured
exactly like {doc}`the THF / Isabelle pair <higher-order>` (`hol.classical`),
and deliberately *not* parity with it yet (no relevant / substructural /
many-valued / second-third-order / deepshallow Lean routes — those are
separate follow-on items once this pattern is proven). With a local Lean 4
toolchain installed, the optional live tier actually elaborates — and, for a
hand-written proof, kernel-checks — the emitted file.

## What it emits (and what it does not decide)

Like every other exporter in `hol`, this module **emits**; it does not itself
run a prover. The emitted goal is always closed with `sorry` by default, so
the file *always elaborates* without claiming a proof — Lean's analogue of
Isabelle's `oops`. Classical FOL is semi-decidable only, so no tactic is
guaranteed to close every valid goal.

Import from `unicode_fol_kit.hol.lean` (these names are **not** re-exported
from `unicode_fol_kit.hol` or top-level — see [Why a dedicated
namespace](#why-a-dedicated-namespace) below):

```python
from unicode_fol_kit import MSFLParser
from unicode_fol_kit.hol import lean

p = MSFLParser().parse
syllogism = p("∀x (Human(x) → Mortal(x))")

print(lean.to_lean_fol(syllogism))
# → -- Classical FOL embedded into Lean 4 core (no Mathlib) over an
#   -- uninterpreted, EXPLICITLY NONEMPTY individual type `Ind` and
#   -- uninterpreted predicates/functions/constants declared as `axiom`s.
#   -- '=' / '≠' are the uninterpreted predicates feq / fneq, NOT Lean's `=`.
#
#   axiom Ind : Type
#   axiom Ind_nonempty : Nonempty Ind
#   instance : Nonempty Ind := Ind_nonempty
#
#   open Classical
#
#   axiom human : Ind → Prop
#   axiom mortal : Ind → Prop
#
#   theorem goal : (∀ x : Ind, ((human x) → (mortal x))) := by
#     sorry
```

With `conjecture=False` the formula is emitted as `axiom goal : …` instead —
no proof line at all, useful for asserting it as a hypothesis in a larger
hand-written file.

## The one real semantic trap: non-empty domains

A bare Lean `axiom Ind : Type` is **not** non-empty by fiat — unlike
Isabelle/HOL's `typedecl`, which always denotes a non-empty type. Silently
omitting a witness would invalidate classical schemas that depend on a
non-empty domain, e.g. `(∀x, P x) → ∃x, P x`. This is exactly the
"approximate silently" failure the project refuses to ship, so every emitted
theory declares an explicit witness *and* registers it as a type-class
instance, so a later tactic that searches for `Nonempty`/`Inhabited` finds it
too:

```lean
axiom Ind : Type
axiom Ind_nonempty : Nonempty Ind
instance : Nonempty Ind := Ind_nonempty
```

Hand-checked (and live-tested against a real toolchain — see
`tests/test_lean.py::TestLeanLive::test_nonempty_domain_witness_makes_all_implies_exists_provable`):

```python
from unicode_fol_kit.fol.nodes import Variable, Atom, Quantifier, Implies

x = Variable("x")
f = Implies(Quantifier("∀", x, Atom("P", [x])),
           Quantifier("∃", x, Atom("P", [x])))
proof = "intro h\nobtain ⟨w⟩ := Ind_nonempty\nexact ⟨w, h w⟩"
src = lean.to_lean_fol(f, proof=proof)
r = lean.check_theory(src, "nonempty_domain")
assert r.ok and not r.uses_sorry            # kernel-checked, no sorry
```

The propositional modal-K embedding makes the same commitment for its Kripke
world type (`World` / `World_nonempty`).

## Equality

By default `=` / `≠` are the *uninterpreted* predicates `feq` / `fneq` — not
Lean's own `=` — matching the toolkit-wide HOL convention
(`hol.classical`, `qml.to_thf_modal`). Pass `native_equality=True` for Lean's
own built-in, axiom-free `=` / `≠` instead:

```python
from unicode_fol_kit.fol.nodes import Constant, Atom

eq = Atom("=", [Constant("a"), Constant("b")])
print(lean.to_lean_fol(eq, native_equality=True))
# → ... axiom a : Ind
#       axiom b : Ind
#
#       theorem goal : (a = b) := by
#         sorry
```

## Many-sorted FOL

`to_lean_msfol` reduces a many-sorted formula with `fol.to_fol` (each sort
becomes a unary guard predicate over the single flat `Ind`, each sorted
quantifier relativised — `∀x:S φ ↦ ∀x (S(x) → φ)`) and emits the result with
`to_lean_fol` — **exactly** the reduction `hol.classical.to_isabelle_msfol` /
`to_thf_msfol` already use, so this module adds no new semantics. `Ind` itself
is guaranteed non-empty (above); an individual sort's guard predicate is
**not** additionally forced non-empty — the same reading the two existing
MSFOL exporters already have (sort non-emptiness is a caller concern,
`fol.nonempty_sort_axioms`, for callers that want it, e.g. `api.prove` —
never assumed silently inside a per-formula translation).

## Propositional modal K

`to_lean_modal_k` is a Benzmüller-style shallow Kripke embedding, faithful to
`semantics.kripke.satisfies_modal` restricted to the propositional fragment
(`Box`/`Diamond` plus the classical connectives over *ground* atoms — no
quantifiers, agent-indexed modalities, or deontic/temporal operators; those
raise `NotImplementedError` naming the construct) over an **unconstrained**
accessibility relation `R` — frame **K**, no frame conditions, since this
slice covers only K:

```python
from unicode_fol_kit.fol.nodes import Atom, Implies, Box

p, q = Atom("p", ()), Atom("q", ())
k_axiom = Implies(Box(Implies(p, q)), Implies(Box(p), Box(q)))
print(lean.to_lean_modal_k(k_axiom))
# → ... axiom World : Type
#       axiom World_nonempty : Nonempty World
#       instance : Nonempty World := World_nonempty
#
#       open Classical
#
#       axiom R : World → World → Prop
#
#       axiom p : World → Prop
#       axiom q : World → Prop
#
#       theorem goal : ∀ w0 : World,
#         ((∀ w1 : World, R w0 w1 → ((p w1) → (q w1))) →
#          ((∀ w2 : World, R w0 w2 → (p w2)) → (∀ w3 : World, R w0 w3 → (q w3)))) := by
#         sorry
```

`Box`/`Diamond` translate the standard clauses `⟦□φ⟧w = ∀v, R w v → ⟦φ⟧v` /
`⟦◇φ⟧w = ∃v, R w v ∧ ⟦φ⟧v`, and every distinct ground atom gets its own
`World → Prop` valuation axiom.

### Validating the encoding, two ways

`tests/test_lean.py` checks this embedding is faithful two ways, both
live-tested against a real Lean 4 toolchain:

1. **A known theorem, kernel-checked.** The modal K axiom
   `□(p→q) → (□p → □q)` — valid in every normal modal logic — elaborates
   *and* has a hand-written, `sorry`-free proof, cross-checked against the
   kit's own labelled modal tableau (`atp.tableau.is_valid_tableau`, which
   decides propositional modal formulas over K independently):

   ```python
   proof = "intro w h1 h2 v hRv\nexact h1 v hRv (h2 v hRv)"
   src = lean.to_lean_modal_k(k_axiom, proof=proof)
   r = lean.check_theory(src, "k_axiom")
   assert r.ok and not r.uses_sorry            # kernel-checked, live: lean 4.34.0
   ```

2. **A known non-theorem, refuted by decision, not just unproved.** `□p → p`
   (the T axiom / reflexivity) needs a frame condition K does not have — the
   independent tableau oracle agrees it is *not* valid over K. Rather than
   merely showing no tactic closes it (silence proves nothing), a **concrete,
   two-world, decidable instantiation** makes Lean's own `decide` tactic
   *positively report the proposition is false*:

   ```lean
   theorem not_t_axiom :
       ∀ w : Bool, (∀ v : Bool, (w = false ∧ v = true) → v = true) → w = true := by
     decide
   -- error: Tactic `decide` proved that the proposition
   --   ∀ (w : Bool), (∀ (v : Bool), w = false ∧ v = true → v = true) → w = true
   -- is false
   ```

   World `false` R-sees only world `true`; `p` holds only at `true`; so `□p`
   is true at `false` while `p` itself is false there — exactly the K
   countermodel to `□p → p`.

## The optional live tier

Nothing above needs Lean installed — every function so far only emits text.
`find_lean` / `lean_available` look for a Lean 4 toolchain, in order: an
explicit path, the env var `UFK_LEAN_HOME`, `lean` on `PATH`, and the
standard `elan` install location `~/.elan/bin` — found even when
`elan-init` was run with `--no-modify-path` (nothing on `PATH`). Nothing in
this module ever modifies `PATH` or a shell profile itself.

```python
lean.lean_available()                      # -> True/False, cheap & cached
inst = lean.find_lean()
print(inst)                                 # -> Lean(4.34.0 at .../elan/bin/lean.exe)
```

`check_theory(source, name)` writes the file to a scratch directory and runs
bare `lean <file>.lean` on it — no `lakefile`/project needed: every fragment
this module emits (classical FOL/MSFOL over `Classical` reasoning,
propositional modal K) is expressible in Lean 4 core + the `Classical`
namespace it ships with, confirmed by hand against a real, Mathlib-free Lean
4.34 toolchain. The result's `ok` is `True` iff the file *elaborates*
(true for a `sorry`-closed goal too); `uses_sorry` is set separately when the
elaboration warned about one. `proved` (and truthiness) is the honest,
stronger claim — elaborates **and** is genuinely sorry-free:

```python
r = lean.check_theory(lean.to_lean_fol(syllogism), "syllogism")
r.ok, r.uses_sorry, r.proved     # -> True, True, False  (emit-only: elaborates, not proved)
```

`lean_decide_fol` / `lean_decide_modal_k` additionally try a small tactic
battery (`DEFAULT_METHODS = ("decide", "tauto", "aesop")`) and report the
first genuinely sorry-free success as `VALID`, else `UNKNOWN` — there is no
`INVALID` here (unlike `hol.isabelle_runner`'s nitpick-backed refutation):
this battery can certify a proof but not construct a countermodel, so
`UNKNOWN` is the only honest outcome for a formula it cannot close, valid or
not — never a false "proved".

**No Mathlib is installed or required**, by design (the fragments above don't
need it, and it is a multi-GB, long-build dependency the kit avoids). This
has a real, honest consequence for the battery: `tauto` and `aesop` are
*Mathlib* tactics, so without it they fail to parse ("unknown tactic") and
the battery just moves on to the next method — never a crash, never a false
`VALID`. `decide` only closes a goal Lean can find a computable `Decidable`
instance for; the axiom-based embeddings above are intentionally *not*
decidable (`Ind` / `World` are opaque, uninterpreted types), so in this
environment the battery will typically report `UNKNOWN` even for a valid
formula — exactly the honest, sound-but-incomplete behaviour
`hol.isabelle_runner` already documents for its own battery. Reach for
`check_theory` with a hand-written proof (as in the K-axiom example above)
when you actually have one.

### Installing a toolchain

```sh
# Downloads elan into your home directory; does NOT touch PATH or a shell
# profile. Discover it afterwards via UFK_LEAN_HOME=~/.elan/bin, or nothing
# at all -- find_lean() already checks ~/.elan/bin as a fallback.
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf \
  | sh -s -- --no-modify-path -y --default-toolchain stable
```

## Why a dedicated namespace

`to_lean_fol` / `to_lean_msfol` / `to_lean_modal_k` and the live-tier names
(`find_lean`, `lean_available`, `check_theory`, `LeanInstall`, …) live in
`unicode_fol_kit.hol.lean` only — not re-exported from `unicode_fol_kit.hol`
or top-level, the same treatment `hol.classical`'s own `to_thf_fol` /
`to_isabelle_fol` get. One additional, concrete reason for `hol.lean`
specifically: it needs its own `check_theory` / `DEFAULT_METHODS` (Lean's
elaboration model is different enough from Isabelle's `isabelle build` that
they cannot be the same function), and those names are already taken at the
`unicode_fol_kit.hol` level by `hol.isabelle_runner`'s own `check_theory` /
`DEFAULT_METHODS` — so a flat re-export would silently shadow one or the
other. Import explicitly:

```python
from unicode_fol_kit.hol import lean
# or
from unicode_fol_kit.hol.lean import to_lean_fol, to_lean_modal_k, check_theory
```
