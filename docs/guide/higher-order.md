# Higher-order proving: Isabelle / THF exporters

The `unicode_fol_kit.hol` subpackage emits Benzmüller-style **shallow semantical embeddings** of every non-fuzzy logic into higher-order logic — as complete, self-contained problem files for an external prover (Leo-III / Satallax on TPTP **THF**, or Isabelle/HOL theories for Sledgehammer). With a local Isabelle installed, the opt-in runner turns *emit* into *proven / refuted* and reads a real verdict off the build.

## What the exporters emit (and what they cannot decide)

The exporters **emit**; they do not themselves run a prover. They also cannot decide everything: first-order modal logic, FOL, and SOL are undecidable / not even semi-decidable, so a successful emission means *"here is a sound problem a prover may discharge"*, never *"decided"*. (The propositional fragments — K3/LP, modal K/T/S4/S5 — are decidable, but these exporters target the general case.) Equality `=` / `≠` is an **uninterpreted, world-relativized** predicate throughout (not primitive HOL identity), consistently across every exporter.

Each exporter has a THF variant (`to_thf_*`) and an Isabelle variant (`to_isabelle_*`). **None of these names are top-level** — `from unicode_fol_kit import *` does *not* bring them in. Import them from `unicode_fol_kit.hol`:

```python
from unicode_fol_kit import MSFLParser
from unicode_fol_kit.hol import (
    to_isabelle_modal, to_thf_modal_full,    # full modal family
    to_thf_fol, to_isabelle_fol,             # classical FOL
    to_thf_msfol, to_isabelle_msfol,         # many-sorted FOL (sort guards)
    to_thf_so, to_isabelle_so,               # second-order (native HO quantifiers)
    to_thf_intuitionistic, to_isabelle_intuitionistic,  # intuitionistic (GMT → S4)
    to_thf_k3lp, to_isabelle_k3lp,           # three-valued K3 / LP
    gmt_translate, gmt_is_s4_valid,          # the GMT box-translation + its oracle
)

# Quantified, agent-indexed epistemic logic — "every student knows P of themselves":
f = MSFLParser(modal=True).parse("∀x (Student(x) → K_x P(x))")
thf = to_thf_modal_full(f, frame="S5")
print("thf(" in thf, "mvalid" in thf, "mknows" in thf)   # → True True True
```

The **runner** entry points (`find_isabelle`, `isabelle_available`, `isabelle_decide_modal`, `isabelle_decide_fol`, `check_theory`, and the verdict dataclasses) *are* exposed both top-level and under `unicode_fol_kit.hol`. The pure exporters above are `unicode_fol_kit.hol`-only.

- **Full modal family.** `to_isabelle_modal(φ, mode="constant", frame="K", …)` emits a real, loadable Isabelle theory (`theory … imports Main begin … end`, every lifted operator as an abbreviation, frame + domain axioms, the formula lifted into the embedding, and a genuine `lemma`). `to_thf_modal_full(φ, mode, frame, systems=…)` is the THF counterpart. Both cover alethic □/◇, **epistemic** `K_a` / **doxastic** `B_a`, **deontic** `Ⓞ`/`Ⓟ`, and **temporal** `Ⓖ`/`Ⓕ`/`Ⓝ`. Epistemic/doxastic accessibility is **agent-indexed**: the agent of `Knows` / `Believes` is a first-class *term*, so a bound `K_x` (as in the example) genuinely quantifies over agents, exactly as the per-agent Kripke relations do. (`Until` is out of the shallow fragment; temporal `Ⓖ`/`Ⓕ`/`Ⓝ` are linked by an inclusion axiom but remain an approximation of the closure semantics — see the `isabelle_modal` module docstring.)
- **Classical FOL / MSFOL.** `to_thf_fol` / `to_isabelle_fol` (and the `to_thf_msfol` / `to_isabelle_msfol` variants, which relativise each sort to a guard predicate) emit the formula as a HOL conjecture / lemma.
- **Three-valued K3 / LP.** `to_thf_k3lp(φ, system="K3")` / `to_isabelle_k3lp` (also the `…_entailment` variants) encode the truth-value type, the strong-Kleene connective functions, and the designated set (`{1}` for K3, `{½, 1}` for LP), so emitted theorem-hood matches K3 / LP validity. The Isabelle lemma carries a real proof that discharges — case-exhaustion over the three truth values for a valid formula, an `exI` witness for a refutation. Cross-checked against `kleene_value`.
- **Second-order.** `to_thf_so` / `to_isabelle_so` map `∀P` / `∃P` to native higher-order predicate quantifiers (standard semantics). Cross-checked against `satisfies_so` on finite structures.
- **Intuitionistic.** `to_thf_intuitionistic` / `to_isabelle_intuitionistic` apply the **Gödel–McKinsey–Tarski** box-translation into S4 then the alethic SSE, so emitted theorem-hood matches intuitionistic validity — `p ∨ ¬p`, `¬¬p → p`, and Peirce's law come out as **non-theorems**. For a valid formula the Isabelle theory carries a real, Isabelle-checked proof (gated on the decidable `gmt_is_s4_valid` oracle); a non-theorem is left `oops`. Cross-checked against `int_valid`.

Each embedding is faithful to its in-toolkit ground-truth oracle (`satisfies_modal`, `kleene_value`, `satisfies_so`, `int_valid`), verified by an adversarial differential audit.

## Classical FOL: `to_thf_fol` / `to_isabelle_fol`

The simplest exporters. `to_thf_fol` returns a TPTP-THF problem string; `to_isabelle_fol` returns a loadable Isabelle theory. Predicates become `$i > $o` declarations, the formula becomes the `goal` conjecture, and `=` / `≠` are the *uninterpreted* predicates `feq` / `fneq` (so `∀x. x = x` is **not** a theorem of the embedding — no equality axioms are assumed).

```python
from unicode_fol_kit import MSFLParser
from unicode_fol_kit.hol import to_thf_fol, to_isabelle_fol

p = MSFLParser().parse
syllogism = p("∀x (Human(x) → Mortal(x))")

print(to_thf_fol(syllogism))
# → % Classical FOL embedded into THF (first-order fragment of HOL).
#   % The formula is emitted as the conjecture; '$i' is the individual type.
#   % '=' / '≠' are uninterpreted predicates (feq / fneq), not HOL identity.
#   thf(human_decl, type, ( human : ( $i > $o ) )).
#   thf(mortal_decl, type, ( mortal : ( $i > $o ) )).
#   thf(goal, conjecture, ( ! [X: $i] : ( ( human @ X ) => ( mortal @ X ) ) )).
```

The Isabelle variant wraps the same formula in a `theory … begin … end` block with an uninterpreted individual type `i`, `consts` declarations, and a `lemma goal` left on the `oops` hook so the theory always loads:

```python
print(to_isabelle_fol(syllogism))
# → theory FOL_Export
#     imports Main
#   begin
#   ...
#   typedecl i  \<comment> \<open>uninterpreted individuals\<close>
#   consts human :: "i \<Rightarrow> bool"
#   consts mortal :: "i \<Rightarrow> bool"
#
#   lemma goal: "(\<forall> x. ((human x) \<longrightarrow> (mortal x)))"
#     oops
#
#   end
```

By default the formula is the **conjecture** (what you ask the prover to prove). Pass `conjecture=False` to emit it as an **axiom** instead — useful when you want to add a hypothesis to a separate problem file:

```python
axiom_form = to_thf_fol(syllogism, conjecture=False)
print("axiom" in axiom_form)         # → True
print("conjecture" in axiom_form)    # → False
```

### Equality is uninterpreted

`feq` / `fneq` carry no built-in reflexivity, symmetry, or transitivity. This is deliberate and consistent across every exporter — the embedding does not silently assume HOL identity:

```python
refl = p("∀x (x = x)")
thf_refl = to_thf_fol(refl)
print("feq" in thf_refl)             # → True   (= is the predicate feq)
print("$i = $i" in thf_refl)         # → False  (NOT primitive HOL identity)
```

### Comparison operators and arithmetic in FOL

Comparison predicates (`≤`, `≥`, `<`, `>`) become uninterpreted binary predicates (`fle`, `fge`, `flt`, `fgt`); arithmetic operators (`+`, `-`, `*`, `/`) become uninterpreted function symbols whose names are sanitised to TPTP-legal identifiers:

```python
# Comparison predicates become uninterpreted binary predicates
f_cmp = p("x ≤ y ∧ y < z ∧ x ≠ z")
thf_cmp = to_thf_fol(f_cmp)
print("fle" in thf_cmp)     # → True  (≤ becomes fle)
print("flt" in thf_cmp)     # → True  (< becomes flt)
print("fneq" in thf_cmp)    # → True  (≠ becomes fneq)

# Arithmetic functions: the operator symbols are sanitised. '+' / '*' are
# not TPTP-legal atoms, so they are emitted as underscore-based function
# symbols ('_' for the first op encountered, '__2' for the next, ...).
f_arith = p("result = step + 1 ∧ step * 2 ≥ result")
thf_arith = to_thf_fol(f_arith)
print("feq" in thf_arith)            # → True   (= → feq)
print("fge" in thf_arith)            # → True   (≥ → fge)
print(": ( $i > $i > $i )" in thf_arith)  # → True  (the two binary fn symbols)
```

### Custom Isabelle names and proofs

Control the theory and lemma names to match your project structure, and choose a concrete proof tactic instead of the `oops` hook:

```python
from unicode_fol_kit.hol import ISABELLE_TACTICS

# Default names
isa_default = to_isabelle_fol(p("P(x) → P(x)"))
print("theory FOL_Export" in isa_default)     # → True
print("lemma goal:" in isa_default)            # → True

# Custom names
isa_named = to_isabelle_fol(
    p("∀x (Parent(x, y) ∧ Parent(y, z) → Ancestor(x, z))"),
    theory_name="Genealogy",
    lemma_name="transitivity_of_ancestry",
)
print("theory Genealogy" in isa_named)                 # → True
print("lemma transitivity_of_ancestry:" in isa_named)  # → True

# The known tactic keywords (for reference; pass the full proof via proof=)
print(sorted(ISABELLE_TACTICS.keys()))
# → ['auto', 'blast', 'force', 'metis', 'oops', 'simp', 'sledgehammer', 'smt', 'sorry']

simple = p("P → P")
isa_auto = to_isabelle_fol(simple, proof="by auto")
print("by auto" in isa_auto)     # → True
print("oops" in isa_auto)        # → False  (the proof replaced the hook)
```

## Many-sorted FOL: `to_thf_msfol` / `to_isabelle_msfol`

The MSFOL exporters take a formula parsed with `MSFLParser(many_sorted=True)` and **relativise each sort to a guard predicate** of type `$i > $o`: a `∀x:Person …` becomes `! [X: $i] : ( person @ X ) => …`, a `∃y:Document …` becomes `? [Y: $i] : ( document @ Y ) & …`. There is one untyped individual type and one guard per sort. **Import `to_isabelle_msfol` from `unicode_fol_kit.hol`** — it is *not* available through `from unicode_fol_kit import *`.

```python
from unicode_fol_kit import MSFLParser
from unicode_fol_kit.hol import to_thf_msfol, to_isabelle_msfol

ms = MSFLParser(many_sorted=True).parse
f = ms("∀x:Person ∃y:Document Wrote(x, y)")

print(to_thf_msfol(f))
# → % Classical FOL embedded into THF (first-order fragment of HOL).
#   % ...
#   thf(document_decl, type, ( document : ( $i > $o ) )).
#   thf(person_decl, type, ( person : ( $i > $o ) )).
#   thf(wrote_decl, type, ( wrote : ( $i > $i > $o ) )).
#   thf(goal, conjecture, ( ! [X: $i] : ( ( person @ X ) => ( ? [Y: $i] : ( ( document @ Y ) & ( wrote @ X @ Y ) ) ) ) )).
```

The Isabelle MSFOL theory has the same shape as the FOL one, with each sort emitted as a `consts … :: "i \<Rightarrow> bool"` guard:

```python
isa = to_isabelle_msfol(f)
print("theory MSFOL_Export" in isa)      # → True
print('consts person ::' in isa)          # → True
print('consts document ::' in isa)        # → True
print("(\<forall> x. ((person x)" in isa)  # → True  (universal relativised to the guard)
```

`include_sort_facts=` (default `True`) controls whether sort-inhabitation facts are added when a free constant of a sort occurs; for purely quantified formulas like the one above it makes no difference, but it is available for problems with sorted constants:

```python
with_facts = to_thf_msfol(f, include_sort_facts=True)
without     = to_thf_msfol(f, include_sort_facts=False)
print(with_facts == without)    # → True  (no free sorted constants here)
```

### Many-sorted hierarchies

Many-sorted FOL scales to deep domain hierarchies — every sort that appears becomes its own guard:

```python
ms_complex = ms("∀x:Person ∀y:Organization ∃z:Document (Wrote(x, z) ∧ Cites(z, y))")
isa_complex = to_isabelle_msfol(ms_complex)
print("person" in isa_complex.lower())          # → True
print("organization" in isa_complex.lower())    # → True
print("document" in isa_complex.lower())        # → True
```

## Second-order: `to_thf_so` / `to_isabelle_so`

The SO exporters map predicate quantifiers `∀P` / `∃P` directly onto **native higher-order quantifiers** of the target — a `P` of arity 1 has type `$i > $o` (THF) / `i \<Rightarrow> bool` (Isabelle). This is **standard (full) second-order semantics**, which is not even semi-decidable, so a sound prover may fail to close a valid goal. Parse with `MSFLParser(second_order=True)`.

```python
from unicode_fol_kit import MSFLParser
from unicode_fol_kit.hol import to_thf_so, to_isabelle_so

so = MSFLParser(second_order=True).parse

# "every individual has some property" — trivially valid in full SO semantics
exists_prop = so("∀x ∃P P(x)")
print(to_thf_so(exists_prop))
# → % Direct second-order -> HOL embedding (predicate quantifiers are native).
#   % ...
#   thf(goal, conjecture, ( ( ! [X: $i] : ( ? [P: ( $i > $o )] : ( P @ X ) ) ) )).
```

A more substantial example — the Leibniz characterisation of identity (`x = y` iff `x` and `y` share every property). The `∀P` becomes a genuine higher-order quantifier `! [P: ( $i > $o )]`:

```python
leibniz = so("∀x ∀y (∀P (P(x) ↔ P(y)) → x = y)")
thf_leibniz = to_thf_so(leibniz)
print("[P: ( $i > $o )]" in thf_leibniz)    # → True   (native predicate quantifier)
print("feq" in thf_leibniz)                  # → True   (= is still the uninterpreted feq)
```

The Isabelle variant names its theory via `name=` (note: this exporter uses `name=`, not `theory_name=`):

```python
isa_so = to_isabelle_so(so("∃P ∀x P(x)"), name="Universal_Pred")
print("theory Universal_Pred" in isa_so)     # → True
print("i \<Rightarrow> bool" in isa_so)        # → True   (predicate type)
print("oops" in isa_so)                       # → True   (left for an external prover)
```

## The full modal family: `to_thf_modal_full` / `to_isabelle_modal`

These cover the whole modal surface in one shallow embedding over a world type, with a *separate accessibility family per modality*:

| modality | operators | THF relation | lifted op |
|---|---|---|---|
| alethic | `□` `◇` | `r : mu > mu > $o` | `mbox` / `mdia` |
| epistemic | `K_a` | `rk : $i > mu > mu > $o` (agent-indexed) | `mknows` |
| doxastic | `B_a` | `rb : $i > mu > mu > $o` (agent-indexed) | `mbelieves` |
| deontic | `Ⓞ` `Ⓟ` | `d : mu > mu > $o` (serial) | `mobl` / `mperm` |
| temporal | `Ⓖ` `Ⓕ` `Ⓝ` | `t` / `tnext : mu > mu > $o` | `malways` / `meventually` |

Parse modal formulas with `MSFLParser(modal=True)`. The deontic / temporal operators are the circled letters `Ⓞ Ⓟ` and `Ⓖ Ⓕ Ⓝ`.

### Alethic □/◇ and the frame argument

`frame=` (one of `K` / `T` / `S4` / `S5`) chooses which frame axioms come into scope. Over `K` the T-axiom `□P → P` is *not* derivable; over a reflexive (`T`) frame it is — the embedding just emits the right `axiom` lines and the prover does the rest.

```python
from unicode_fol_kit import MSFLParser
from unicode_fol_kit.hol import to_thf_modal_full, to_isabelle_modal

pm = MSFLParser(modal=True).parse
t_axiom = pm("□P → P")

thf_K = to_thf_modal_full(t_axiom, frame="K")
thf_T = to_thf_modal_full(t_axiom, frame="T")
print("refl" in thf_K)     # → False  (K assumes nothing about r)
print("refl" in thf_T)     # → True   (T emits the reflexivity axiom)
```

The Isabelle counterpart is a complete, loadable theory. For the T-axiom over a reflexive frame:

```python
print(to_isabelle_modal(t_axiom, frame="T"))
# → a 42-line Isabelle theory; the load-bearing lines are:
#   consts r :: "i \<Rightarrow> i \<Rightarrow> bool"            -- alethic accessibility
#   abbreviation mbox … "mbox \<phi> \<equiv> \<lambda>w. \<forall>v. r w v \<longrightarrow> \<phi> v"
#   abbreviation mvalid … ("\<lfloor>_\<rfloor>") "\<lfloor>\<phi>\<rfloor> \<equiv> \<forall>w. \<phi> w"
#   consts p :: "i \<Rightarrow> bool"
#   axiomatization where r_refl: "r w w"
#   lemma modal_goal: "\<lfloor> (mimp (mbox p) p) \<rfloor>"
#     sledgehammer
#     oops
```

The default tactic is the `sledgehammer` / `oops` hook, so the theory always loads even when no automatic proof is found; pass `tactic=` (e.g. `"auto"`, `"blast"`, `"metis"`) or `proof=` to substitute a concrete proof. `mode=` selects the constant- (`"constant"`) vs. varying-domain quantifier regime.

```python
isa = to_isabelle_modal(t_axiom, frame="T")
print(len(isa.splitlines()))                  # → 42
print('axiomatization where r_refl: "r w w"' in isa)   # → True

isa_blast = to_isabelle_modal(t_axiom, frame="T", tactic="blast")
print("blast" in isa_blast)                   # → True
```

### Epistemic K_a / doxastic B_a — agent-indexed

The agent of `Knows` / `Believes` is a **first-class term**, so the accessibility relation `rk` / `rb` is indexed by an `$i`-typed agent. A *bound* `K_x` therefore genuinely quantifies over agents:

```python
# "alice knows P ⇒ P" — epistemic T (knowledge is factive)
epist = pm("K_alice P → P")
thf_epist = to_thf_modal_full(epist, frame="T")
print("rk @ alice" in thf_epist or "mknows @ alice" in thf_epist)   # → True
print("mknows" in thf_epist)                  # → True

# a bound agent variable really quantifies over the agent term:
quantified = pm("∀x (Student(x) → K_x P(x))")
thf_q = to_thf_modal_full(quantified, frame="S5")
print("mknows @ X" in thf_q)                  # → True   (X is the bound agent)

# doxastic: belief is NOT factive — emitted with its own relation rb
doxa = pm("B_alice P → P")
thf_doxa = to_thf_modal_full(doxa, frame="K")
print("mbelieves @ alice" in thf_doxa)        # → True
print("rb :" in thf_doxa)                      # → True
```

### Deontic Ⓞ/Ⓟ and temporal Ⓖ/Ⓕ/Ⓝ

Deontic obligation / permission lift to `mobl` / `mperm` over a **serial** relation `d` (so "ought implies can" — `d_serial` is always emitted). Temporal `Ⓖ` (always) / `Ⓕ` (eventually) / `Ⓝ` (next) lift to `malways` / `meventually` over the temporal relation `t`:

```python
# Ⓞ = Obligatory, Ⓟ = Permitted:  obligation implies permission
deontic = pm("ⓄP → ⓅP")
thf_deontic = to_thf_modal_full(deontic, frame="K")
print("mobl" in thf_deontic)        # → True
print("mperm" in thf_deontic)       # → True
print("d_serial" in thf_deontic)    # → True   (seriality is always emitted)

# Ⓖ = always (temporal box):  G P → P  (needs reflexive temporal access to hold)
temporal = pm("ⒼP → P")
thf_temporal = to_thf_modal_full(temporal, frame="K")
print("malways" in thf_temporal)        # → True
print("meventually" in thf_temporal)    # → True   (the dual is always defined)

# Ⓝ = next
nxt = pm("ⓃP → ⒻP")
thf_next = to_thf_modal_full(nxt, frame="K")
print("tnext" in thf_next)          # → True
```

### Per-family system selection with `systems=`

`to_thf_modal_full(φ, systems={...})` lets you give the **epistemic / doxastic** families their own modal strength independently of the alethic `frame`. Mapping `epistemic → "S5"` emits reflexivity, transitivity and symmetry axioms for `rk`:

```python
introspective = pm("K_alice P → K_alice K_alice P")   # positive introspection (4)
thf_s5 = to_thf_modal_full(introspective, frame="K", systems={"epistemic": "S5"})
print("rk_refl" in thf_s5)     # → True
print("rk_trans" in thf_s5)    # → True
print("rk_sym" in thf_s5)      # → True   (S5 ⇒ symmetric accessibility)
```

## A sample emitted Isabelle theory

`to_isabelle_modal` returns a `str` — a complete theory that starts with `theory ModalEmbedding` and ends with `end`, with every lifted operator as an `abbreviation`, the frame axioms via `axiomatization`, and the formula as a real `lemma`:

```python
sample = to_isabelle_modal(pm("□P → P"), frame="T")
print(sample.startswith("theory ModalEmbedding"))   # → True
print(sample.rstrip().endswith("end"))               # → True
print('abbreviation mbox' in sample)                 # → True
print('abbreviation mvalid' in sample)               # → True
print('lemma modal_goal:' in sample)                 # → True
```

## Intuitionistic logic: the GMT translation

`to_thf_intuitionistic` / `to_isabelle_intuitionistic` route an intuitionistic propositional formula through the **Gödel–McKinsey–Tarski** box-translation into S4 and then the alethic SSE, so emitted theorem-hood matches intuitionistic validity. The translation itself is exposed as `gmt_translate`, and its decidable S4 oracle as `gmt_is_s4_valid`.

```python
from unicode_fol_kit import MSFLParser
from unicode_fol_kit.hol import (
    to_thf_intuitionistic, to_isabelle_intuitionistic,
    gmt_translate, gmt_is_s4_valid,
)

p = MSFLParser().parse

# gmt_translate boxes every subformula; the result is an ordinary modal Node.
print(gmt_translate(p("P → P")).to_unicode_str())     # → □(□P → □P)
print(gmt_translate(p("P ∨ ¬P")).to_unicode_str())     # → □P ∨ □¬□P
print(gmt_translate(p("¬¬P → P")).to_unicode_str())    # → □(□¬□¬□P → □P)
```

The S4 oracle decides intuitionistic validity directly: the classical tautologies that *fail* intuitionistically come out **False**, while genuine intuitionistic theorems come out **True**:

```python
print(gmt_is_s4_valid(p("P → P")))                       # → True   (a theorem)
print(gmt_is_s4_valid(p("P ∨ ¬P")))                       # → False  (LEM fails)
print(gmt_is_s4_valid(p("¬¬P → P")))                      # → False  (DNE fails)
print(gmt_is_s4_valid(p("((P → Q) → P) → P")))            # → False  (Peirce fails)
print(gmt_is_s4_valid(p("¬¬(P ∨ ¬P)")))                   # → True   (weak LEM holds)
```

The THF export is the boxed formula over a reflexive-transitive (S4) frame. For Peirce's law — an intuitionistic **non-theorem** — a sound prover will refuse it:

```python
peirce = p("((P → Q) → P) → P")
thf_peirce = to_thf_intuitionistic(peirce)
print("frame=S4" in thf_peirce)        # → True
print("refl" in thf_peirce)            # → True   (S4 ⇒ reflexive)
print("trans" in thf_peirce)           # → True   (S4 ⇒ transitive)
print("mbox" in thf_peirce)            # → True   (every connective is boxed)
```

For a **valid** formula the Isabelle theory carries a real, Isabelle-checked proof (gated on `gmt_is_s4_valid`); a non-theorem is left on `oops`:

```python
isa_valid = to_isabelle_intuitionistic(p("P → P"))
print("theory IPL_GMT" in isa_valid)   # → True
print("lemma gmt_goal:" in isa_valid)  # → True
print("using r_refl r_trans" in isa_valid)   # → True  (a real, discharged proof)

isa_nontheorem = to_isabelle_intuitionistic(peirce)
print("oops" in isa_nontheorem)        # → True   (left open — not a theorem)
```

## Three-valued K3 / LP (bonus exporters)

`to_thf_k3lp(φ, system="K3"|"LP")` / `to_isabelle_k3lp` encode the three truth values, the strong-Kleene connective functions, and the designated set, so emitted theorem-hood matches K3 / LP validity. The law of excluded middle is a K3 non-theorem (the designated set is `{T}`) but holds in LP:

```python
from unicode_fol_kit.hol import to_thf_k3lp

lem = p("P ∨ ¬P")
thf_k3 = to_thf_k3lp(lem, system="K3")
thf_lp = to_thf_k3lp(lem, system="LP")
print("system=K3" in thf_k3)         # → True
print("system=LP" in thf_lp)         # → True
print("kor" in thf_k3)               # → True   (the strong-Kleene disjunction fn)
print("des" in thf_k3)               # → True   (the designated-set predicate)
print(thf_k3 != thf_lp)              # → True   (different designated sets)
```

## Actually running it: the Isabelle runner

If a local **Isabelle/HOL** is installed, `unicode_fol_kit.hol.isabelle_runner` writes the embedding to a scratch session, runs `isabelle build`, and reads the verdict off the build. It is **opt-in**: with no Isabelle present everything above still works and these calls raise a clear `IsabelleNotAvailable` (the live tests skip). The cheap predicate is `isabelle_available()`; `find_isabelle()` locates an install and returns an `IsabelleInstall` (or `None`). These two are cheap and safe to call unconditionally:

```python
from unicode_fol_kit import isabelle_available, find_isabelle

# Cheap, side-effect-free probe. Returns True only if an Isabelle was located.
available = isabelle_available()
print(type(available).__name__)     # → bool

# find_isabelle() returns an IsabelleInstall or None — never raises.
install = find_isabelle()
if install is None:
    print("no Isabelle on this machine — exporters still work, runner does not")
else:
    # IsabelleInstall fields: home, is_windows, isabelle_exe, cygwin_bash, version
    print("home:", install.home)
    print("version:", install.version)
```

On a machine *with* Isabelle, `available` is `True` and `install` is a populated `IsabelleInstall`; on a machine *without* one, `available` is `False` and `install` is `None`. Either way the call is honest and never raises — guard your actual `isabelle_decide_*` calls behind it.

### Deciding modal validity: `isabelle_decide_modal`

`isabelle_decide_modal(φ, *, frame="K", mode="constant", …)` decides validity (for the chosen `frame` / `mode`) in three steps, read off the build's exit code:

1. **Prove** — emit the lemma with a proof battery that brings the frame/domain axioms into scope (`using <axioms> by (blast | force | fastforce | auto | meson … | metis …)`; the method list is `DEFAULT_METHODS`, overridable via `methods=`). A successful `isabelle build` ⇒ **VALID**.
2. **Refute** — otherwise emit `nitpick[expect = genuine]`, whose build succeeds **iff** Isabelle finds a genuine finite counter-model ⇒ **INVALID**.
3. Otherwise ⇒ **UNKNOWN** (expected — first-order modal logic is undecidable).

This is **sound** (Isabelle's kernel certifies the proof; nitpick reports only *genuine* counter-models) and necessarily **incomplete**; `UNKNOWN` is a real outcome, not a failure. The verdict is validated *differentially* against an independent brute-force Kripke oracle (`satisfies_modal`) across K/T/S4/S5 in the test suite.

Every line below that actually invokes Isabelle is gated with `# doctest: +SKIP` — it needs a local install and can take tens of seconds per call. The shape of the returned `ModalVerdict` is shown without invoking the prover:

```python
# doctest: +SKIP
from unicode_fol_kit import MSFLParser, isabelle_decide_modal

pm = MSFLParser(modal=True).parse

# □P → P is INVALID over K (no reflexivity) but VALID over a reflexive frame:
print(isabelle_decide_modal(pm("□P → P"), frame="K"))    # ModalVerdict[invalid, frame=K, ...]
print(isabelle_decide_modal(pm("□P → P"), frame="T"))    # ModalVerdict[valid (by prove-battery), frame=T, ...]
print(isabelle_decide_modal(pm("□P → □□P"), frame="S4"))  # ModalVerdict[valid (by prove-battery), frame=S4, ...]
```

The verdict is a `ModalVerdict` dataclass; you can build one yourself (no Isabelle needed) to see its fields — `status`, `frame`, `mode`, `method`, `countermodel`, `prove_output`, `refute_output`, `prove_elapsed`, `refute_elapsed`, `infra_error`:

```python
from unicode_fol_kit import ModalVerdict
print(list(ModalVerdict.__dataclass_fields__.keys()))
# → ['status', 'frame', 'mode', 'method', 'countermodel', 'prove_output',
#    'refute_output', 'prove_elapsed', 'refute_elapsed', 'infra_error']

v = ModalVerdict(
    status="VALID", frame="T", mode="constant", method="blast",
    countermodel=None, prove_output="", refute_output="",
    prove_elapsed=0.0, refute_elapsed=0.0, infra_error=None,
)
print(v.status, v.frame, v.method)    # → VALID T blast
```

- **Locating Isabelle.** `find_isabelle()` looks at an explicit path, then `UFK_ISABELLE_HOME` / `ISABELLE_HOME`, then `isabelle` on `PATH`, then a light scan of standard install locations (no path is hard-coded). **Linux/macOS is the primary path** — `isabelle` is invoked directly; **Windows** is also supported, with the build routed through Isabelle's bundled Cygwin automatically (path translation + launcher exec-bit fixup), exposed as the `cygwin_bash` field of `IsabelleInstall`.
- **Counter-models.** An `INVALID` verdict in the propositional alethic fragment carries a concrete Kripke counter-model in `ModalVerdict.countermodel`, reconstructed from `satisfies_modal` (`isabelle build` does not echo nitpick's model). For `Always`/`Eventually` together with `Next`, the refute theory defines the henceforth relation as the reflexive-transitive closure of the one-step relation, so the closure fragment is genuinely refuted rather than left `UNKNOWN`.

### Deciding classical validity: `isabelle_decide_fol`

`isabelle_decide_fol(φ, *, msfol=False, …)` decides classical validity the same way (prove-battery → nitpick finite counter-model), returning a `FolVerdict` (same fields as `ModalVerdict`, minus `frame` / `mode`). FOL is only semi-decidable, so `UNKNOWN` is common; equality is the **uninterpreted** `feq` / `fneq` of the embedding (no equality axioms are assumed, so `∀x. x = x` is *not* valid here).

```python
# doctest: +SKIP
from unicode_fol_kit import MSFLParser, isabelle_decide_fol

p = MSFLParser().parse
print(isabelle_decide_fol(p("P(a) → P(a)")))                 # FolVerdict[valid (by prove-battery), ...]
print(isabelle_decide_fol(p("∀x (Human(x) → Mortal(x))")))   # FolVerdict[unknown, ...]  (not valid)

# Many-sorted: pass msfol=True so the sort guards are interpreted
ms = MSFLParser(many_sorted=True).parse
print(isabelle_decide_fol(ms("∀x:Person P(x) → ∀x:Person P(x)"), msfol=True))
```

`FolVerdict` has the same fields minus `frame` / `mode`:

```python
from unicode_fol_kit import FolVerdict
print(list(FolVerdict.__dataclass_fields__.keys()))
# → ['status', 'method', 'countermodel', 'prove_output', 'refute_output',
#    'prove_elapsed', 'refute_elapsed', 'infra_error']
```

### Building an arbitrary theory: `check_theory`

`check_theory(theory_text, theory_name)` builds an arbitrary self-contained theory and returns a `BuildResult` — used internally, and handy for the non-modal exporters (`to_isabelle_fol`, `to_isabelle_k3lp`, `to_isabelle_intuitionistic`, …), whose emitted proofs are themselves built against real Isabelle in the test suite. The `BuildResult` fields are `ok`, `exit_code`, `output`, `theory_name`, `session`, `elapsed`:

```python
from unicode_fol_kit.hol import BuildResult
print(list(BuildResult.__dataclass_fields__.keys()))
# → ['ok', 'exit_code', 'output', 'theory_name', 'session', 'elapsed']
```

A round trip — emit a provable intuitionistic theory, then build it (the build call needs a local Isabelle, so it is skipped here):

```python
from unicode_fol_kit import MSFLParser
from unicode_fol_kit.hol import to_isabelle_intuitionistic, check_theory

p = MSFLParser().parse
theory = to_isabelle_intuitionistic(p("P → P"))      # a real, discharged proof
print("theory IPL_GMT" in theory)                     # → True

# Actually building it requires a local Isabelle:
result = check_theory(theory, "IPL_GMT")   # doctest: +SKIP
print(result.ok, result.exit_code, result.elapsed)   # doctest: +SKIP
```

When no Isabelle is present, `check_theory` / `isabelle_decide_*` raise `IsabelleNotAvailable`; catch it (or gate on `isabelle_available()`) to keep the pure-export path working everywhere:

```python
from unicode_fol_kit.hol import IsabelleNotAvailable
print(issubclass(IsabelleNotAvailable, Exception))    # → True
```
