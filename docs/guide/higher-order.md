# Higher-order proving: Isabelle / THF exporters

The `unicode_fol_kit.hol` subpackage emits Benzmüller-style **shallow semantical embeddings** of every non-fuzzy logic into higher-order logic — as complete, self-contained problem files for an external prover (Leo-III / Satallax on TPTP **THF**, or Isabelle/HOL theories for Sledgehammer). With a local Isabelle installed, the opt-in runner turns *emit* into *proven / refuted* and reads a real verdict off the build.

## What the exporters emit (and what they cannot decide)

The exporters **emit**; they do not themselves run a prover. They also cannot decide everything: first-order modal logic, FOL, and SOL are all **undecidable**, so a successful emission means *"here is a sound problem a prover may discharge"*, never *"decided"*. (FOL and the standard first-order modal logics are still *semi-decidable* — validity is recursively enumerable — whereas full second-order validity is *not even semi-decidable*; the propositional fragments K3/LP and modal K/T/S4/S5 are outright decidable, but these exporters target the general case.) Equality `=` / `≠` is an **uninterpreted, world-relativized** predicate throughout by default (not primitive HOL identity), consistently across every exporter; the classical `to_thf_fol` / `to_isabelle_fol` family (and their MSFOL variants) additionally accept `native_equality=True` to opt into the target format's own built-in identity instead (see [Opting into native HOL identity](#opting-into-native-hol-identity) below) — every other exporter is unaffected and keeps the uninterpreted reading unconditionally.

Each exporter has a THF variant (`to_thf_*`) and an Isabelle variant (`to_isabelle_*`). **None of these names are top-level** — `from unicode_fol_kit import *` does *not* bring them in. Import them from `unicode_fol_kit.hol`:

```python
from unicode_fol_kit import MSFLParser
from unicode_fol_kit.hol import (
    to_isabelle_modal, to_thf_modal_full,    # full modal family
    to_thf_fol, to_isabelle_fol,             # classical FOL
    to_thf_msfol, to_isabelle_msfol,         # many-sorted FOL (sort guards)
    to_thf_free, to_isabelle_free,           # free logic (D / E! guards)
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

The **runner** entry points (`find_isabelle`, `isabelle_available`, `isabelle_decide_modal`, `isabelle_decide_fol`, `isabelle_decide_counterfactual`, `check_theory`, and the verdict dataclasses) *are* exposed both top-level and under `unicode_fol_kit.hol`. The pure exporters above are `unicode_fol_kit.hol`-only.

- **Full modal family.** `to_isabelle_modal(φ, mode="constant", frame="K", …)` emits a real, loadable Isabelle theory (`theory … imports Main begin … end`, every lifted operator as an abbreviation, frame + domain axioms, the formula lifted into the embedding, and a genuine `lemma`). `to_thf_modal_full(φ, mode, frame, systems=…)` is the THF counterpart. Both cover **the whole modal family the AST expresses**: alethic □/◇, **epistemic** `K_a` / **doxastic** `B_a` / **assertive** `Say_a` / **bouletic** `Want_a` (all agent-indexed — the agent is a first-class *term*, so a bound `K_x` genuinely quantifies over agents; `Say`/`Want` are plain K-boxes over their own relations, with no frame axioms), **deontic** `Ⓞ`/`Ⓟ`, **temporal** `Ⓖ`/`Ⓕ`/`Ⓝ` and the **past-tense** `⒣`/`⒫`/`⒴` (box/diamond over the *converse* of the henceforth `t`, resp. the converse of the one-step `n` — the converse of a refl+trans relation is refl+trans, so the same axioms constrain both directions), and the **hybrid** `Nominal`/`@` (world constants `nom_<name>`). The entity type is the **monomorphic** `typedecl e` — a polymorphic `'a` would give every agent-constant occurrence its own type instance and falsify the agent-K axiom (a false INVALID nitpick would "certify"). Both emitters also cover the **binary interval operators** `Until` (Ⓤ) and `Since` (⒮): Isabelle as **inductive least-fixpoint predicates** `muntil` / `msince` over the one-step relation `n`, THF as the equivalent **impredicative Knaster–Tarski fixpoints** (TH0 quantifies over predicates), both matching `satisfies_modal`'s finite forward / backward path search faithfully on every frame. `Until` / `Since` are **not** first-order definable, so `qml_translate` still rejects them with a pointer here.
- **Classical FOL / MSFOL.** `to_thf_fol` / `to_isabelle_fol` (and the `to_thf_msfol` / `to_isabelle_msfol` variants, which relativise each sort to a guard predicate) emit the formula as a HOL conjecture / lemma.
- **Free logic.** `to_thf_free` / `to_isabelle_free` embed `semantics.free_logic`'s negative/positive free logic via TWO uninterpreted guard predicates over one flat individual type: `D(t)` ("`t` denotes") guards every ordinary atom, `E!(t)` ("`t` exists", strictly narrower than `D`) guards every quantifier — so unrestricted universal instantiation is no longer valid, only its `E!`-guarded form. `policy="supervaluation"` is refused with `NotImplementedError` (see [Free logic](#free-logic-to_thf_free--to_isabelle_free) below for why).
- **Three-valued K3 / LP, and any finite matrix.** `to_thf_k3lp(φ, system="K3")` / `to_isabelle_k3lp` (also the `…_entailment` variants) encode the truth-value type, the strong-Kleene connective functions, and the designated set (`{1}` for K3, `{½, 1}` for LP), so emitted theorem-hood matches K3 / LP validity. The Isabelle lemma carries a real proof that discharges — case-exhaustion over the three truth values for a valid formula, an `exI` witness for a refutation. Cross-checked against `kleene_value`. `to_thf_matrix` / `to_isabelle_matrix` (+ `…_entailment` variants) generalise this to **any** `semantics.matrix.TruthMatrix` — the K3/LP exporters above are now the specialisation of this data-driven encoding to those two matrices, so any custom matrix, or the shipped four-valued Belnap–Dunn **FDE**, gets the same export for free.
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

### Opting into native HOL identity

`native_equality=True` (added on `to_thf_fol` / `to_isabelle_fol` / `to_thf_msfol` / `to_isabelle_msfol`) switches `=` / `≠` from the uninterpreted `feq` / `fneq` predicates to the target format's own built-in identity — THF's infix `=` / `!=`, Isabelle's polymorphic `=` / `\<noteq>`. This is a *rendering* choice, not new machinery: TPTP THF and Isabelle/HOL both already ship a genuine, axiom-free identity relation at every type (including the uninterpreted individual type `$i` / `i`), so reflexivity, symmetry, transitivity, and congruence with every declared function/predicate all come for free — no axioms to add, no declaration for `=` itself:

```python
refl = p("∀x (x = x)")
thf_native = to_thf_fol(refl, native_equality=True)
print("feq" in thf_native)          # → False  (no feq functor, no feq_decl)
print("( X = X )" in thf_native)    # → True   (THF's own infix identity)
```

The default stays `False` (uninterpreted `feq` / `fneq`) — this flag is purely additive, and a formula with no `=` / `≠` at all renders byte-identically either way. Comparison predicates `<` `>` `≤` `≥` are unaffected by the flag; they always stay uninterpreted (`flt` / `fgt` / `fle` / `fge`), since neither target format has a built-in counterpart for them.

The practical payoff is congruence: a lemma that *needs* `x = y ∧ P(x) → P(y)` closes trivially once `=` is real identity, but does not close under the default uninterpreted reading — actually run against a local Isabelle/HOL installation:

```python
congruence = p("∀x ∀y ((x = y ∧ P(x)) → P(y))")

native = to_isabelle_fol(congruence, proof="by auto", native_equality=True)
# `isabelle build` on `native`: succeeds — genuine HOL '=' makes 'by auto' close the goal.

default = to_isabelle_fol(congruence, proof="by auto", native_equality=False)
# `isabelle build` on `default`: FAILS — 'feq' carries no congruence, so the
# same tactic cannot discharge the same-shaped goal. This is the demonstration
# that hand-rolling congruence axioms would have been unnecessary machinery:
# the target format's own identity already does the job.
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

## Free logic: `to_thf_free` / `to_isabelle_free`

Classical FOL assumes every term denotes an *existing* individual, so universal instantiation `∀x φ → φ(c)` is always valid. [Free logic](nonclassical.md) (`semantics.free_logic`) drops that: a constant may denote an object OUTSIDE the domain quantifiers range over, or fail to denote at all. `hol.free` embeds this the same way `to_thf_msfol` embeds sorts — by **guard-relativization** — but needs *two* uninterpreted unary guard predicates over one flat individual type `e`, not one:

- `D(t)` — "`t` denotes" (some object of the OUTER domain) — guards every ordinary atom: `P(t₁, …, tₙ)` becomes `D*(t₁) ∧ … ∧ D*(tₙ) ∧ P(t₁, …, tₙ)`, where `D*` also guards every compound subterm (`D*(f(s)) = D*(s) ∧ D(f(s))`), because `f(s)` cannot denote when `s` does not, while a HOL function is total.
- `E!(t)` — "`t` exists" (an object of the INNER domain quantifiers actually range over; strictly narrower than `D`, tied together by the axiom `E!(x) → D(x)`) — guards every quantifier: `∀x φ ↦ ∀x. E!(x) → φ`, `∃x φ ↦ ∃x. E!(x) ∧ φ`.

`semantics.free_logic`'s own object-language existence predicate — written `E!(t)` directly in a formula (it has no surface grammar of its own; build it with `Atom("E!", [t])`) — is emitted as this same guard predicate, guarded only by `D*` of the proper subterms of `t`: with the tie it already means exactly "`t` denotes and is existing". Equality is HOL's own identity under the same guard, `s = t ↦ D*(s) ∧ D*(t) ∧ s = t` — `free_holds` compares the referents of denoting terms by identity, and an uninterpreted `feq` would let nitpick certify countermodels to free-logic validities such as `∀x ∀y ((x = y ∧ P(x)) → P(y))`.

```python
from unicode_fol_kit import MSFLParser
from unicode_fol_kit.hol import to_thf_free, to_isabelle_free
from unicode_fol_kit.fol.nodes import Atom, Constant

p = MSFLParser().parse
every_unicorn_is_magical = p("∀x (Unicorn(x) → Magical(x))")

print(to_thf_free(every_unicorn_is_magical))
# → % Free logic embedded into THF via denotation/existence guards.
#   % D(t): 't denotes'; existsBang(t): 't exists' (E! implies D). policy='negative'.
#   thf(denotes_decl, type, ( denotes : ( $i > $o ) )).
#   thf(existsBang_decl, type, ( existsBang : ( $i > $o ) )).
#   thf(magical_decl, type, ( magical : ( $i > $o ) )).
#   thf(unicorn_decl, type, ( unicorn : ( $i > $o ) )).
#   thf(free_tie, axiom, ( ! [X: $i] : ( ( existsBang @ X ) => ( denotes @ X ) ) )).
#   thf(goal, conjecture, ( ! [X: $i] : ( ( existsBang @ X ) => ( ( ( denotes @ X ) & ( unicorn @ X ) ) => ( ( denotes @ X ) & ( magical @ X ) ) ) ) )).
```

`D`/`E!` sanitise to `denotes`/`existsBang`. A written `E!(t)` atom (arity 1) IS the guard, because `E!` is the free-logic existence predicate inside `semantics.free_logic.free_holds` itself; a predicate named literally `D!` has no such meaning to `free_holds`, so it is refused with `ValueError` (it is unreachable from the parser anyway — `!` cannot occur in parseable predicate names). An ordinary predicate that merely sanitises to `denotes`/`existsBang`, or a bare `D`, is de-collided away from the guard names, same discipline as `feq`/`fneq` in [classical FOL](#equality-is-uninterpreted). The `E! → D` tie is the only background fact, emitted as an extra `axiom` / lemma **premise** — never `axiomatization` — so nitpick can construct `D`/`E!` itself and certify a counter-model as genuine (see [Deciding free-logic validity](#deciding-free-logic-validity-isabelle_decide_free) below). There is deliberately no `∃x. E!(x)`: an empty inner domain is a free-logic model (`free_is_valid` searches it by default), so `(∀x P(x)) → ∃x P(x)` is not a theorem here either.

The textbook free-logic point: does "every unicorn is magical" plus "Pegasus is a unicorn" let you conclude "Pegasus is magical"? Only with the extra premise that Pegasus **exists** — the object-language `E!` atom, built directly since it has no surface syntax:

```python
from unicode_fol_kit.fol.nodes import Implies, And

pegasus = Constant("pegasus")
pegasus_is_unicorn = p("Unicorn(pegasus)")
pegasus_exists = Atom("E!", [pegasus])              # no surface syntax for E! — built directly
pegasus_is_magical = p("Magical(pegasus)")

premises = And(every_unicorn_is_magical, pegasus_is_unicorn)
guarded_ui = Implies(And(premises, pegasus_exists), pegasus_is_magical)     # a genuine theorem
unguarded_ui = Implies(premises, pegasus_is_magical)                        # NOT a theorem

print(to_isabelle_free(guarded_ui, theory_name="PegasusGuarded"))
# → theory PegasusGuarded
#     imports Main
#   begin
#   ...
#   typedecl e  \<comment> \<open>outer domain: existing or merely possible\<close>
#   consts denotes :: "e \<Rightarrow> bool"
#   consts existsBang :: "e \<Rightarrow> bool"
#   consts magical :: "e \<Rightarrow> bool"
#   consts unicorn :: "e \<Rightarrow> bool"
#   consts pegasus :: "e"
#
#   lemma goal: "(\<forall>x. existsBang x \<longrightarrow> denotes x) \<Longrightarrow> ..."
#     oops
#
#   end
```

Run through the [Isabelle runner](#deciding-free-logic-validity-isabelle_decide_free), `guarded_ui` comes back `FolVerdict[valid (by prove-battery)]` and `unguarded_ui` comes back `FolVerdict[invalid]` — a real Isabelle kernel proof of the guarded schema, and a real, kernel-certified countermodel (a Pegasus that denotes but does not exist) to the unguarded one.

### Two policies, and one explicitly refused

`policy="negative"` (default) makes every atom with a non-denoting term FALSE — `=` included, so self-identity `t = t` fails for a non-denoting `t`. `policy="positive"` carves out ONE exception, mirroring `free_satisfies`'s own `_atom` clause exactly: a **self**-identity atom — the literal SAME term written twice — is exempted from the `D`-guard, so it holds unconditionally instead. Either way the identity itself is THF's / Isabelle's own **native identity**, so the exempted atom is really true and the guarded one really reduces to `D(pegasus)`:

```python
pegasus_self_id = Atom("=", [pegasus, pegasus])

neg = to_thf_free(pegasus_self_id, policy="negative")
pos = to_thf_free(pegasus_self_id, policy="positive")
print("( denotes @ pegasus )" in neg, "( pegasus = pegasus )" in neg, "feq" in neg.split("thf(goal,")[1])
# → True True False   (D-guarded, but the "= " leaf is native identity, not feq)
print("( denotes @ pegasus )" in pos, "( pegasus = pegasus )" in pos, "feq" in pos.split("thf(goal,")[1])
# → False True False  (bare, native identity)
```

`policy="supervaluation"` raises `NotImplementedError` from both `to_thf_free` and `to_isabelle_free`. Supervaluationist truth is a property of a whole MODEL's set of truth-value gaps (true under every classical completion of THAT model — see `semantics.free_logic`'s module docstring), not a fact derivable from a single formula's guarded translation the way negative/positive are; encoding it soundly would need second-order quantification over per-model gap assignments, a different and much larger undertaking this module does not fold in:

```python
try:
    to_thf_free(pegasus_self_id, policy="supervaluation")
except NotImplementedError as e:
    print(str(e)[:52])
    # → to_thf_free: policy='supervaluation' has no guarded-
```

Use `semantics.free_logic.free_holds(formula, model, policy="supervaluation")` directly for that reading instead.

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

`to_thf_modal_full` also takes `temporal_closure=` (default `True`) for parity with the Isabelle emitter's own temporal treatment: opt out with `temporal_closure=False` to drop the `t_refl` / `t_trans` closure axioms while keeping the `tnext ⊆ t` link between the one-step and henceforth relations:

```python
default_closure = to_thf_modal_full(temporal, frame="K")
no_closure = to_thf_modal_full(temporal, frame="K", temporal_closure=False)
print("t_refl" in default_closure, "t_trans" in default_closure)   # → True True
print("t_refl" in no_closure, "t_trans" in no_closure)              # → False False
print("tnext" in no_closure)                                        # → True   (the inclusion axiom stays)
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

`isabelle_modal_theory` / `to_isabelle_modal` / `isabelle_decide_modal` accept the same `systems=` parameter — per-agent frame axioms for `rk`/`rb`/`rs`/`rw`, the agent schematic quantified over just like the accessibility relation itself:

```python
isa_s5 = to_isabelle_modal(introspective, frame="K", systems={"epistemic": "S5"})
print("rk_refl" in isa_s5, "rk_trans" in isa_s5, "rk_sym" in isa_s5)   # → True True True
```

A system whose frame condition has **no per-agent schema** — GL's Löb axiom, or the S4.2/S4.3 directedness conditions — cannot be expressed agent-indexed, and both exporters reject it loudly (pointing at `frame=` on the alethic relation instead) rather than silently weakening it to something that agent-indexes but does not actually mean GL:

```python
to_isabelle_modal(pm("K_alice P"), systems={"epistemic": "GL"})
# raises ValueError: to_isabelle_modal: system 'GL' for epistemic needs the frame
# condition(s) ['loeb'], which have no per-agent axiom schema here; use frame= on
# the alethic relation for those systems.
```

### Cross-family bridges with `bridges=`

`frame=` and `systems=` each constrain **one** relation. A *bridge* relates **two** relations of different families, which is what a principle like "whatever you know, you believe" needs — it is not a property of `rk` or of `rb`, but of how they sit relative to each other. Bridges are therefore a separate, **opt-in** argument; nothing below is on by default.

| `bridges=` name | Schema | Frame condition | Isabelle fact |
| --- | --- | --- | --- |
| `"knowledge_implies_belief"` | `K_a φ → B_a φ` | `rb ⊆ rk` | `rb_in_rk` |
| `"sincerity"` | `Say_a φ → B_a φ` | `rb ⊆ rs` | `rb_in_rs` |
| `"ought_implies_can"` | `Ⓞ φ → ◇φ` | `∀w ∃v. d w v ∧ r w v` | `d_meets_r` |

`unicode_fol_kit.hol.BRIDGES` is the list of accepted names; `to_thf_modal_full`, `to_isabelle_modal` / `isabelle_modal_theory`, `modal_axiom_names` and `isabelle_decide_modal` all take the same `bridges=` argument and emit facts under the same names, so one grep finds both routes.

```python
from unicode_fol_kit.hol import BRIDGES, to_isabelle_modal, to_thf_modal_full

BRIDGES   # → ('knowledge_implies_belief', 'sincerity', 'ought_implies_can')

kb = pm("K_alice P → B_alice P")
print("rb_in_rk" in to_isabelle_modal(kb))                                    # → False (off by default)
print("rb_in_rk" in to_isabelle_modal(kb, bridges=["knowledge_implies_belief"]))  # → True
print("rb_in_rk" in to_thf_modal_full(kb, bridges=["knowledge_implies_belief"]))  # → True
```

Each condition is the **exact** correspondent of its schema, so a bridge adds precisely that principle and nothing stronger. `ought_implies_can` is deliberately *not* the folklore `d ⊆ r`: measured over all frames on ≤ 2 worlds, `d ⊆ r` alone fails to validate `Ⓞφ → ◇φ`, and together with deontic seriality it over-validates `□φ → Ⓞφ` ("whatever is necessary is obligatory"). `d_meets_r` validates the schema and not that artefact.

> **One name, one logic.** `fol.qml` emits the same three conditions under the same three names — including the meet condition for `ought_implies_can`, which it originally realised as the inclusion `D ⊆ R`. So `qml_is_valid(□φ → Ⓞφ, bridges=["ought_implies_can"])` and the HOL routes agree that the artefact is invalid, and `pytest tests/test_hol_bridges.py` pins that agreement in both registries.

A bridge names two relations, and this emitter declares a relation only when its operators occur. Requesting a bridge whose partner family is **absent** from the formula therefore raises `ValueError` instead of silently emitting a weaker logic (skipping it) or a stronger one (`d_meets_r` entails seriality of the alethic `r`, which would quietly make `□P → ◇P` valid under `frame="K"`). `fol.qml` applies the same rule for the same reason:

```python
to_isabelle_modal(pm("□P → ◇P"), bridges=["ought_implies_can"])
# raises ValueError: ... the formula contains no Obligatory/Permitted operator, so
# that relation is never declared ...
```

The native tableau (`modal_decide` and friends) refuses `bridges=` outright with a `NotImplementedError` naming the routes above: every one of its structural rules acts inside a single relation, so it has no rule to apply and no sound way to approximate one.

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

### Any finite matrix: `to_thf_matrix` / `to_isabelle_matrix`

`to_thf_k3lp` / `to_isabelle_k3lp` are the K3/LP specialisation of a data-driven encoding that works for **any** `TruthMatrix` — `to_thf_matrix(φ, matrix)` / `to_isabelle_matrix(φ, matrix)` (plus `to_thf_matrix_entailment` / `to_isabelle_matrix_entailment` for a premises-conclusion goal) read the value set, the per-connective tables, and the designated subset straight off the matrix object, so the four-valued Belnap–Dunn **FDE** — or any matrix you build yourself with `TruthMatrix.from_functions` — exports exactly like K3/LP do:

```python
from unicode_fol_kit.semantics.matrix import FDE_MATRIX
from unicode_fol_kit.hol import to_thf_matrix, to_isabelle_matrix

lem = p("P ∨ ¬P")
thf_fde = to_thf_matrix(lem, FDE_MATRIX)
print("tv_type" in thf_fde)          # → True   (the value type, named from matrix.values)
print("tT" in thf_fde and "tB" in thf_fde)   # → True   (all four FDE values declared)
print("des" in thf_fde)              # → True   (the designated-set predicate, {T, B} here)

isa_fde = to_isabelle_matrix(lem, FDE_MATRIX)
print("theory Matrix_Validity" in isa_fde)   # → True
```

`value_names=` / `conn_names=` override the generated identifiers when the matrix's own value labels or a connective's default name would collide or read poorly; `type_name=` / `predicate_name=` rename the value type and the designated-set predicate. Emitted theorem-hood matches `matrix_is_valid(φ, matrix)` for every matrix, exactly as the K3/LP exporters match `kleene_value`.

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
- **Which logic the verdict is about.** `frame=`, `mode=`, `systems=`, `temporal_closure=` and `bridges=` all select a class of models, and every one of them is forwarded to *both* emitted theories and to the `using` axiom list. That is not tidiness: the two steps decide opposite questions, so an option reaching only the prove step would degrade to `UNKNOWN`, while one reaching only the refute step would let nitpick certify a "genuine" counter-model that is not in the requested class at all — a false `INVALID`.

So opting into a cross-family bridge flips the verdict rather than half of it — the axiom lands in the proof battery *and* in nitpick's theory:

```python
# doctest: +SKIP
print(isabelle_decide_modal(pm("K_alice P → B_alice P")))                              # invalid
print(isabelle_decide_modal(pm("K_alice P → B_alice P"),
                            bridges=["knowledge_implies_belief"]))                     # valid
```

### Deciding classical validity: `isabelle_decide_fol`

`isabelle_decide_fol(φ, *, msfol=False, native_equality=False, …)` decides classical validity the same way (prove-battery → nitpick finite counter-model), returning a `FolVerdict` (same fields as `ModalVerdict`, minus `frame` / `mode`). FOL is only semi-decidable, so `UNKNOWN` is common. By default equality is the **uninterpreted** `feq` / `fneq` of the embedding (no equality axioms are assumed, so `∀x. x = x` is *not* valid here); `native_equality=True` decides FOL with identity instead. The `isabelle` prover backend (`api.prove(..., backends=["isabelle"])`) always uses `native_equality=True`, since every other backend reads `=` as identity — with the uninterpreted reading it used to report `∀x (x = x)` as REFUTED.

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

### Deciding counterfactual validity: `isabelle_decide_counterfactual`

`isabelle_decide_counterfactual(φ)` decides validity for formulas built from the propositional connectives plus the counterfactuals `□→` / `◇→` (`Would` / `Might`, parsed in modal mode). The modal exporter's accessibility relation is the wrong structure here — a counterfactual reads a **similarity ordering** — so `hol.isabelle_conditional` emits its own shallow sphere embedding: the sphere system is the uninterpreted constant `Sel`, and the goal is `nested Sel ⟹ weakly_centered Sel ⟹ ∀x. φ x`. The sphere condition is the same one `cf_satisfies` evaluates, so what Isabelle certifies is what the toolkit computes. Same scheme as `isabelle_decide_fol`: prove-battery ⇒ `VALID`, else `nitpick[expect = genuine]` over the world type ⇒ `INVALID`, else `UNKNOWN`; returns a `FolVerdict`.

```python
# doctest: +SKIP
from unicode_fol_kit import MSFLParser, isabelle_decide_counterfactual

p = MSFLParser(modal=True).parse
print(isabelle_decide_counterfactual(p("A □→ A")))
# → FolVerdict[valid (by prove-battery)]
print(isabelle_decide_counterfactual(p("((A □→ B) ∧ (A □→ C)) → (A □→ (B ∧ C))")))
# → FolVerdict[valid (by prove-battery)]     (agglomeration — needs the nesting premise)
print(isabelle_decide_counterfactual(p("(A □→ B) → ((A ∧ C) □→ B)")))
# → FolVerdict[invalid]                      (antecedent strengthening fails)
```

`centering=` picks the sphere class, exactly as `cf_valid` does in the [non-classical logics guide](nonclassical.md) and with the same default — `"none"` (Lewis **V**, nesting only) / `"weak"` (**VW**, default) / `"strong"` (**VC**) — so the Isabelle route and the internal evaluator decide the same conditional logic unless told otherwise. The level is emitted as a second **premise** (`weakly_centered Sel` / `strongly_centered Sel`) and recorded in the theory as a `text ‹centering = weak (Lewis VW)›` provenance line, since at `"none"` the lemma is otherwise byte-identical to a pre-centering one:

```python
# doctest: +SKIP
mp_cf = p("(A ∧ (A □→ B)) → B")
print(isabelle_decide_counterfactual(mp_cf))                       # valid   (VW: modus ponens)
print(isabelle_decide_counterfactual(mp_cf, centering="none"))     # invalid (V: the empty sphere system)
print(isabelle_decide_counterfactual(p("(A ∧ B) → (A □→ B)"), centering="strong"))   # valid (VC only)
```

The level reaches all three emission sites — the prove theory, the battery's `unfolding` list, and the nitpick theory. A mismatch would not produce a wrong verdict from a proof (an unfoldable premise just fails to close the goal, i.e. `UNKNOWN`), but a nitpick theory carrying the wrong premise would certify a counter-model from the wrong class, so the argument is never split. Note that `card` here bounds nitpick's finite-model search over the world type, while `cf_countermodel`'s `max_worlds` bounds a Python enumeration of sphere chains — equal numbers are not equal coverage.

Two design points worth knowing when you write your own sphere theories: both premises are **premises of the goal**, never an `axiomatization` (nitpick cannot certify a counter-model as genuine while axiomatised constants are in play — it downgrades to `quasi_genuine`); and the default proof battery is **verit-first**, because the `|` combinator has no per-method timeout and `blast` does not terminate on agglomeration, so a blast-first battery hangs before reaching the method that closes it.

A modal operator under a counterfactual is **rejected** (`NotImplementedError`), matching `cf_satisfies`: `□`/`◇` belong to the accessibility-relation embedding, not the sphere one.

#### THF route: `to_thf_conditional`

`to_thf_conditional(φ, *, centering="weak")` is the THF (TH0) sibling of `isabelle_conditional_theory`, for a higher-order ATP (Leo-III, Vampire-THF, Satallax) instead of Isabelle — same sphere embedding, same `nested`/centering **premises**, same fragment and refusals. Unlike a line-for-line transcription of the Isabelle preamble, the connectives are **inlined at the current world** rather than routed through separately-declared `NegC`/`AndC`/`OrC`/`ImpC`/`IffC`/`CondC` combinators, and `nested`/`weakly_centered`/`strongly_centered` are stated directly of the one fixed sphere system rather than as a schema over an arbitrary one — both changes are meaning-preserving (see the comment above `isabelle_conditional._THF_PRELUDE`) and were made because the literal transcription measurably could not be discharged by Vampire 5.0.1's default portfolio (a battery of THF micro-examples, run by hand, needed real higher-order unification to match a combinator's parameter against another combinator's partial application, and that did not close even trivial goals in 60s), while this form is solved in well under a second:

```python
from unicode_fol_kit import MSFLParser
from unicode_fol_kit.hol import to_thf_conditional

p = MSFLParser(modal=True).parse
print(to_thf_conditional(p("(A ∧ (A □→ B)) → B")))
# → a 19-line TH0 problem: thf(w_type,...), thf(sel_type,...), the nested /
#   weakly_centered / strongly_centered definitions, thf(a_type,...),
#   thf(b_type,...), and
#   thf(goal, conjecture, ( nested => ( weakly_centered => ( ! [X: w] :
#     ( ( ( a @ X ) & <A □→ B at X> ) => ( b @ X ) ) ) ) )).
```

Cross-checked by hand against a real Vampire 5.0.1 (inside WSL), for every schema in `tests/test_thf_conditional.py`'s `_LEWIS_FACTS` battery at every centering level: every valid schema is proved `Theorem` in well under a second (one schema needing a higher-order witness synthesised from an abstract `strongly_centered` hypothesis is a documented exception — see `_VAMPIRE_SLOW`), and every invalid schema's `cf_countermodel` witness, translated to closed-domain ground facts characterising `sel` directly, is independently re-proved a refutation by Vampire through the same `_thf_encode` the exporter ships (again with one class of documented exception, `_VAMPIRE_SLOW_INVALID`: refuting a `□→` whose antecedent is satisfiable within some sphere — not vacuously false everywhere — asks Vampire to synthesise a higher-order witness for the countermodel's own `sel` existential, which its default portfolio does not always close quickly; two such rows are in the battery, kept as text-only checks). This is a property of that battery, not a guarantee that an arbitrary invalid Lewis formula closes in bounded time — the failure mode when it does not is Vampire reporting `Timeout`, never a wrong verdict, so it cannot pass a mismatch silently.

### Deciding relevant-logic-B validity: `isabelle_decide_relevant`

`isabelle_decide_relevant(φ)` decides validity in the simplified Routley–Meyer semantics for relevant logic B — the propositional connectives `¬ ∧ ∨ → ↔` over nullary atoms, matching `semantics.relevant.rel_satisfies`'s own restriction. `hol.isabelle_relevant.to_isabelle_relevant` emits the embedding: worlds `N`/`star`/`R` as uninterpreted `consts`, and — following `isabelle_conditional`'s design — the three well-formedness conditions (`N` nonempty, `star` a total involution, `R` sourced only at non-normal worlds) bundled as a `wellformed` **premise** of the goal rather than an `axiomatization`, so nitpick can construct a frame itself and certify a countermodel as *genuine*. Same scheme as `isabelle_decide_fol`: prove-battery ⇒ `VALID`, else `nitpick[expect = genuine]` over the world type ⇒ `INVALID`, else `UNKNOWN`; returns a `FolVerdict`.

```python
# doctest: +SKIP
from unicode_fol_kit import MSFLParser, isabelle_decide_relevant

p = MSFLParser().parse
print(isabelle_decide_relevant(p("(P ∧ Q) → P")))
# → FolVerdict[valid (by prove-battery)]
print(isabelle_decide_relevant(p("(P → (P → Q)) → (P → Q)")))
# → FolVerdict[invalid]     (contraction — valid in R, genuinely not in B)
```

This gives `rel_valid`'s bounded `True` a certified positive counterpart: where `rel_valid` only means "no countermodel with at most `max_worlds` worlds", a `VALID` from `isabelle_decide_relevant` is a real Isabelle proof over every wellformed interpretation. See {doc}`relevant` for the semantics itself.

#### THF route: `to_thf_relevant`

`to_thf_relevant(φ)` is the THF (TH0) sibling of `to_isabelle_relevant`, for a higher-order ATP (Leo-III, Vampire-THF, Satallax) instead of Isabelle — same shallow embedding (`N`/`star`/`R` uninterpreted, frame conditions bundled into a `wellformed` **premise**), same fragment and refusals. As with `to_thf_conditional` above, the connectives (`NegC`/`AndC`/`OrC`/`ImpC`/`IffC`) are inlined at the current world rather than declared as separate combinators applied to already-built terms — the same fix, made for the same measured reason (see the comment above `isabelle_relevant._THF_PRELUDE`):

```python
from unicode_fol_kit import MSFLParser
from unicode_fol_kit.hol import to_thf_relevant

p = MSFLParser().parse
print(to_thf_relevant(p("(P ∧ Q) → P")))
# → a 16-line TH0 problem: thf(w_type,...), the n/star/r declarations, the
#   wellformed_def IFF (not a lambda equality — see below), thf(p_type,...),
#   thf(q_type,...), and
#   thf(goal, conjecture, ( wellformed => ( ! [X: w] :
#     ( ( n @ X ) => <(P ∧ Q) → P at X, ImpC's N/R case split inlined> ) ) )).
```

Cross-checked by hand against a real Vampire 5.0.1 (inside WSL): every fact in `tests/test_relevant.py`'s `VALID_IN_B` is proved `Theorem` in well under a second, and every fact in `INVALID_IN_B` has its `rel_countermodel` witness independently re-proved a refutation by Vampire, after translating the model to closed-domain ground facts and running it through the same `_thf_encode` the exporter ships (`tests/test_thf_relevant.py`). One implementation detail worth knowing if you write your own THF shallow embeddings: `wellformed`'s definition is a THF `<=>` biconditional between two `$o` formulas, not Isabelle-style `=` against a `^`-headed (lambda) term — logically the same statement, but Vampire's default portfolio discharges the former and, measured by hand, did not close even `P → P` from the latter in 60s (ordinary clausification of a biconditional versus general higher-order superposition to beta-reduce the redex the `=` form creates once applied).

### Deciding free-logic validity: `isabelle_decide_free`

`isabelle_decide_free(φ, *, policy="negative", …)` decides validity of the `D`/`E!`-guard embedding (`hol.free.free_theory`, the same truth condition `free_holds` computes for `policy` — see {doc}`nonclassical` for the semantics itself). Same scheme as `isabelle_decide_fol`: prove-battery ⇒ `VALID`, else `nitpick[expect = genuine]` over the individual type `e` ⇒ `INVALID`, else `UNKNOWN`; returns a `FolVerdict`. `=` is HOL identity under the denotation guard and the inner domain may be empty, so a verdict is a verdict about `free_is_valid`'s own semantics: `∀x ∀y ((x = y ∧ P(x)) → P(y))` comes back `valid`, `(∀x P(x)) → ∃x P(x)` comes back `invalid`. The `E! → D` tie is a **premise** of the goal, not `axiomatization` — the same reason `isabelle_decide_relevant`'s `wellformed` and `isabelle_decide_counterfactual`'s `nested Sel` are premises: nitpick cannot certify a countermodel as genuine while axiomatised constants are in play.

This is the pegasus example from [Free logic](#free-logic-to_thf_free--to_isabelle_free) above, actually run:

```python
# doctest: +SKIP
print(isabelle_decide_free(guarded_ui))     # → FolVerdict[valid (by prove-battery)]
print(isabelle_decide_free(unguarded_ui))   # → FolVerdict[invalid]
```

The `policy="positive"` self-identity case (see [Two policies](#two-policies-and-one-explicitly-refused) above) is decided the same way: `isabelle_decide_free(pegasus_self_id, policy="positive")` comes back `FolVerdict[valid (by prove-battery)]`, matching `semantics.free_logic.free_is_valid(pegasus_self_id, policy="positive")` — actually run against a local Isabelle install:

```python
# doctest: +SKIP
print(isabelle_decide_free(pegasus_self_id, policy="positive"))   # → FolVerdict[valid (by prove-battery)]
```

`policy="supervaluation"` raises `NotImplementedError` **before** the Isabelle-install lookup, so a typo-free but deliberately-unsupported policy is reported as exactly that — not masked by `IsabelleNotAvailable` on a machine with no Isabelle:

```python
from unicode_fol_kit.hol import isabelle_decide_free

try:
    isabelle_decide_free(pegasus_self_id, policy="supervaluation")
except NotImplementedError as e:
    print(str(e)[:52])
    # → isabelle_decide_free: policy='supervaluation' has no
```

### Substructural derivations, replayed: `to_isabelle_ill` / `to_isabelle_lambek`

`hol.isabelle_substructural` takes a different shape from the exporters above: rather than asking Isabelle to *decide* a formula, it **replays** a derivation the toolkit's own cut-free search (`ill_prove` / `lambek_prove`) already found, as a machine-checked lemma. The sequent rules become an Isabelle `inductive derivable` predicate over a deep-embedded `datatype` — a **multiset-via-list-plus-`Exch`** antecedent for ILL, and a plain **list** (no `Exch` — order is exactly what Lambek tracks) for the Lambek calculus — and the concrete derivation tree is transcribed one `intro` rule per node, so a successful build is Isabelle independently re-checking a proof the toolkit already has, not searching for one itself.

```python
from unicode_fol_kit import MSFLParser, ill_prove
from unicode_fol_kit.hol.isabelle_substructural import to_isabelle_ill, ill_derivation_theory

lp = MSFLParser(linear=True).parse
theory = to_isabelle_ill([lp("A"), lp("A ⊸ B")], lp("B"))
print("inductive derivable" in theory)   # → True

# Or start from a derivation you already computed (no re-searching):
d = ill_prove([lp("A"), lp("A ⊸ B")], lp("B"))
ill_derivation_theory(d) == theory       # → True
```

`to_isabelle_lambek(sequence, goal, ...)` / `lambek_derivation_theory(derivation)` are the Lambek counterparts. See {doc}`substructural` for the `⊤`/`𝟘` additive units these theories also cover (`⊤R` / `0L` in the search and the replayed proof alike).

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

## Deep and shallow embeddings with faithfulness proofs

The exporters above give one *minimal (lightweight) shallow* embedding — accessibility and valuation as `consts`, formulas as `w ⇒ bool` — which is the style that automates best. The `unicode_fol_kit.hol.deepshallow` subpackage reproduces the full construction of Benzmüller, *Faithful Logic Embeddings in HOL — Deep and Shallow* (arXiv:2502.19311): for one object logic it emits **all three** embeddings side by side and the **machine-checked faithfulness proofs** relating them.

Each emitted theory contains

- a **deep** embedding — the object syntax as a `datatype` with a recursive `primrec truthD`, so you can reason *about* the logic (induction over formula structure, meta-theorems);
- a **maximal (heavyweight) shallow** embedding — every semantic parameter (`W`, the accessibility structure, `V`) carried explicitly as `⇒ w ⇒ bool`;
- a **minimal (lightweight) shallow** embedding — those parameters fixed as metalogical `consts`;
- the `primrec` mappings `dpToMax` / `dpToMin` and the theorems `faithful1a`/`faithful1b` (deep ↔ maximal), `faithful2`/`faithful3` (↔ minimal in the fixed model) and `sound_min`, each closed by a one-line `induct`.

Unlike the emit-only exporters, these theories are **verified end to end**: a green `check_theory` build means Isabelle's kernel discharged every faithfulness proof. Four worlds-based logics are covered — propositional modal K, intuitionistic (Kripke), Lewis counterfactual (sphere), and relevant logic B (Routley–Meyer):

```python
from unicode_fol_kit.fol.nodes import Atom, Implies, Box
from unicode_fol_kit.hol import modal_faithfulness_theory, modal_to_deep, check_theory
from unicode_fol_kit.hol.deepshallow import AtomConsts

# The deep embedding is propositional, so atoms are 0-ary (a bare term-valued
# identifier parses as a hybrid-logic *nominal* in modal mode, not a
# propositional atom):
p, q = Atom("p", ()), Atom("q", ())
k_axiom = Implies(Box(Implies(p, q)), Implies(Box(p), Box(q)))
print(modal_to_deep(k_axiom, AtomConsts()))
# → (ImpD (BoxD (ImpD (Atm p_p) (Atm p_q))) (ImpD (BoxD (Atm p_p)) (BoxD (Atm p_q))))

theory = modal_faithfulness_theory("ModalFaithfulness")   # the full certificate
result = check_theory(theory, "ModalFaithfulness")        # doctest: +SKIP
print(result.ok)                                          # doctest: +SKIP  → True
```

The four entry points are `modal_faithfulness_theory`, `intuitionistic_faithfulness_theory`, `conditional_faithfulness_theory` and `relevant_faithfulness_theory` (each optionally grounding the certificate in a concrete formula). The stack targets the propositional/schematic fragment, where induction over the syntax datatype applies; the quantified decision path stays in `to_isabelle_modal` / `isabelle_decide_modal` above.

### Tier 2: a genuinely quantified deep embedding — `qml_deep_faithfulness_theory` / `qml_to_deep`

The four logics above are all *propositional*: their deep datatype has no binder, so `induct f arbitrary: x` closes every faithfulness proof in one line. `hol.deepshallow.qml` is the first *quantified* member of the family — deep syntax for `∀`/`∃` — and is deliberately scoped down to make that tractable: **K frame, the CONSTANT domain regime only, alethic `□`/`◇` only**. Every other frame, domain regime, agent-indexed/temporal/deontic operator, equality and function term is refused by name (`NotImplementedError`); there is no `frame=`/`mode=` parameter to even ask for one — `R` is left arbitrary (as in the propositional `modal` module) and the domain is a single set `D` shared by every world, baked into the types rather than checked at run time.

Object variables are de Bruijn-indexed (`obj = BVar nat | FVar s`, `FVar` naming a rigid constant) so `truthD` needs no capture-avoiding substitution: going under `∀`/`∃` just prepends one entry to an explicit assignment stack (`case_nat d e`). The one genuinely new step beyond Tier 1's proofs is generalizing that stack too — `induct f arbitrary: e x` instead of `arbitrary: x` — which is still a single line:

```python
from unicode_fol_kit.fol.nodes import Atom, Implies, Box, Quantifier, Variable
from unicode_fol_kit.fol.qml import BARCAN
from unicode_fol_kit.hol.deepshallow.qml import qml_to_deep, qml_deep_faithfulness_theory
from unicode_fol_kit.hol.deepshallow import AtomConsts
from unicode_fol_kit.hol import check_theory

# BARCAN = ◇∃x A(x) → ∃x ◇A(x) (valid under a constant domain). qml_to_deep
# takes TWO required AtomConsts resolvers — atoms for predicate symbols,
# consts for object CONSTANTS (kept separate since both are of Isabelle type
# `s` but read by different functions — `V` for predicates via `Atm`, the
# rigid interpretation `C` for constants via `FVar` — so a predicate and a
# constant that sanitise to the same identifier must still get distinct
# Isabelle names). Sharing consts's de-collision pool with atoms's is the
# caller's job, done once like this:
atoms = AtomConsts()
consts = AtomConsts()
consts._used = atoms._used
print(qml_to_deep(BARCAN, atoms, consts))
# → (ImpD (DiaD (ExD (Atm p_A [(BVar 0)]))) (ExD (DiaD (Atm p_A [(BVar 0)]))))

# The converse Barcan formula, □/∀ form: □∀x A(x) → ∀x □A(x) — note how the
# SAME bound variable becomes (BVar 0) under BOTH the AllD and the BoxD ∘ AllD
# nesting, since only the AllD/ExD constructors push a new stack entry:
x = Variable("x")
A = lambda t: Atom("A", [t])
nested_cbf = Implies(Box(Quantifier("∀", x, A(x))), Quantifier("∀", x, Box(A(x))))
atoms2, consts2 = AtomConsts(), AtomConsts()
consts2._used = atoms2._used
print(qml_to_deep(nested_cbf, atoms2, consts2))
# → (ImpD (BoxD (AllD (Atm p_A [(BVar 0)]))) (AllD (BoxD (Atm p_A [(BVar 0)]))))

theory = qml_deep_faithfulness_theory("QmlFaithfulness", formula=BARCAN)
result = check_theory(theory, "QmlFaithfulness")  # doctest: +SKIP
print(result.ok)                                  # doctest: +SKIP  → True
```

`consts` has no default: an earlier version of `qml_to_deep` auto-created one when omitted, but a resolver the caller never gets back is a resolver whose `consts p_c :: "s"` declaration a hand-assembled theory can silently drop — Isabelle then rejects the theory ("Extra variables on rhs") with no error raised on the Python side first. Any theory built from the returned term — by hand, or via `qml_deep_faithfulness_theory`, which follows the same pool-sharing pattern internally — must emit BOTH `atoms.decls()` and `consts.decls()`. Deciding whether a *specific* formula is QML-valid is still the job of `fol.qml.qml_is_valid` (Z3) or `semantics.kripke.satisfies_modal` (a finite model) — this module proves the *embedding itself* faithful (and, when grounded in a formula, that the grounded term type-checks), the same division of labour Tier 1 already has between the deep/shallow certificate and `isabelle_decide_modal`.
