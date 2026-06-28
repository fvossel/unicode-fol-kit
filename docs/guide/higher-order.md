# Higher-order proving: Isabelle / THF exporters

The `unicode_fol_kit.hol` subpackage emits Benzmüller-style **shallow semantical embeddings** of every non-fuzzy logic into higher-order logic — as complete, self-contained problem files for an external prover (Leo-III / Satallax on TPTP **THF**, or Isabelle/HOL theories for Sledgehammer). With a local Isabelle installed, the opt-in runner turns *emit* into *proven / refuted* and reads a real verdict off the build.

## What the exporters emit (and what they cannot decide)

The exporters **emit**; they do not themselves run a prover. They also cannot decide everything: first-order modal logic, FOL, and SOL are undecidable / not even semi-decidable, so a successful emission means *"here is a sound problem a prover may discharge"*, never *"decided"*. (The propositional fragments — K3/LP, modal K/T/S4/S5 — are decidable, but these exporters target the general case.) Equality `=` / `≠` is an **uninterpreted, world-relativized** predicate throughout (not primitive HOL identity), consistently across every exporter.

Each exporter has a THF variant (`to_thf_*`) and an Isabelle variant (`to_isabelle_*`). They are exposed under `unicode_fol_kit.hol`:

```python
from unicode_fol_kit import MSFLParser
from unicode_fol_kit.hol import (
    to_isabelle_modal, to_thf_modal_full,    # full modal family
    to_thf_fol, to_isabelle_fol,             # FOL / MSFOL (+ ..._msfol variants)
    to_thf_k3lp, to_isabelle_k3lp,           # three-valued K3 / LP
    to_thf_so, to_isabelle_so,               # second-order
    to_thf_intuitionistic, to_isabelle_intuitionistic,  # intuitionistic (GMT → S4)
)

# Quantified, agent-indexed epistemic logic — "every student knows P of themselves":
f = MSFLParser(modal=True).parse("∀x (Student(x) → K_x P(x))")
thf = to_thf_modal_full(f, frame="S5")
print("thf(" in thf, "mvalid" in thf, "mknows" in thf)   # → True True True
```

- **Full modal family.** `to_isabelle_modal(φ, mode="constant", frame="K", …)` emits a real, loadable Isabelle theory (`theory … imports Main begin … end`, every lifted operator as an abbreviation, frame + domain axioms, the formula lifted into the embedding, and a genuine `lemma`). `to_thf_modal_full(φ, mode, frame, systems=…)` is the THF counterpart. Both cover alethic □/◇, **epistemic** `K_a` / **doxastic** `B_a`, **deontic** `O`/`P`, and **temporal** `G`/`F`/`X`. Epistemic/doxastic accessibility is **agent-indexed**: the agent of `Knows` / `Believes` is a first-class *term*, so a bound `K_x` (as in the example) genuinely quantifies over agents, exactly as the per-agent Kripke relations do. (`Until` is out of the shallow fragment; temporal `G`/`F`/`X` are linked by an inclusion axiom but remain an approximation of the closure semantics — see the `isabelle_modal` module docstring.)
- **Classical FOL / MSFOL.** `to_thf_fol` / `to_isabelle_fol` (and the `to_thf_msfol` / `to_isabelle_msfol` variants, which relativise each sort to a guard predicate) emit the formula as a HOL conjecture / lemma.
- **Three-valued K3 / LP.** `to_thf_k3lp(φ, system="K3")` / `to_isabelle_k3lp` (also the `…_entailment` variants) encode the truth-value type, the strong-Kleene connective functions, and the designated set (`{1}` for K3, `{½, 1}` for LP), so emitted theorem-hood matches K3 / LP validity. The Isabelle lemma carries a real proof that discharges — case-exhaustion over the three truth values for a valid formula, an `exI` witness for a refutation. Cross-checked against `kleene_value`.
- **Second-order.** `to_thf_so` / `to_isabelle_so` map `∀P` / `∃P` to native higher-order predicate quantifiers (standard semantics). Cross-checked against `satisfies_so` on finite structures.
- **Intuitionistic.** `to_thf_intuitionistic` / `to_isabelle_intuitionistic` apply the **Gödel–McKinsey–Tarski** box-translation into S4 then the alethic SSE, so emitted theorem-hood matches intuitionistic validity — `p ∨ ¬p`, `¬¬p → p`, and Peirce's law come out as **non-theorems**. For a valid formula the Isabelle theory carries a real, Isabelle-checked proof (gated on the decidable `gmt_is_s4_valid` oracle); a non-theorem is left `oops`. Cross-checked against `int_valid`.

Each embedding is faithful to its in-toolkit ground-truth oracle (`satisfies_modal`, `kleene_value`, `satisfies_so`, `int_valid`), verified by an adversarial differential audit.

## A sample emitted theory

`to_isabelle_modal` returns a `str` — a complete theory that starts with `theory ModalEmbedding` and ends with `end`. For the T-axiom `□P → P` over a reflexive frame it emits the reflexivity axiom and the lifted lemma:

```python
from unicode_fol_kit import MSFLParser
from unicode_fol_kit.hol import to_isabelle_modal

f = MSFLParser(modal=True).parse("□P → P")
print(to_isabelle_modal(f, frame="T"))
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

The default tactic is the `sledgehammer` / `oops` hook, so the emitted theory always loads even when no automatic proof is found; pass `tactic=` (one of `ISABELLE_TACTICS`, e.g. `"auto"`, `"blast"`, `"metis"`) or `proof=` to substitute a concrete proof. The frame argument (`K` / `T` / `S4` / `S5`) controls which frame axioms are emitted; `mode` selects the constant- vs. varying-domain quantifier regime.

## Actually running it: the Isabelle runner

If a local **Isabelle/HOL** is installed, `unicode_fol_kit.hol.isabelle_runner` writes the embedding to a scratch session, runs `isabelle build`, and reads the verdict off the build. It is **opt-in**: with no Isabelle present everything else still works and these calls raise a clear `IsabelleNotAvailable` (the live tests skip). The cheap predicate is `isabelle_available()`; `find_isabelle()` locates an install and returns an `IsabelleInstall`.

```python
# requires a local Isabelle install — NOT executed here
from unicode_fol_kit import MSFLParser, isabelle_available, isabelle_decide_modal

parse = MSFLParser(modal=True).parse
print(isabelle_available())                                  # True if Isabelle was located

print(isabelle_decide_modal(parse("□P → P"), frame="K"))     # ModalVerdict[INVALID, frame=K, …]
print(isabelle_decide_modal(parse("□P → P"), frame="T"))     # ModalVerdict[VALID, frame=T, …]
print(isabelle_decide_modal(parse("□P → □□P"), frame="S4"))   # ModalVerdict[VALID, frame=S4, …]
```

`isabelle_decide_modal(φ, *, frame="K", mode="constant", …)` decides validity (for the chosen `frame` / `mode`) in three steps, read off the build's exit code:

1. **Prove** — emit the lemma with a proof battery that brings the frame/domain axioms into scope (`using <axioms> by (blast | force | fastforce | auto | meson … | metis …)`; the method list is `DEFAULT_METHODS`, overridable via `methods=`). A successful `isabelle build` ⇒ **VALID**.
2. **Refute** — otherwise emit `nitpick[expect = genuine]`, whose build succeeds **iff** Isabelle finds a genuine finite counter-model ⇒ **INVALID**.
3. Otherwise ⇒ **UNKNOWN** (expected — first-order modal logic is undecidable).

This is **sound** (Isabelle's kernel certifies the proof; nitpick reports only *genuine* counter-models) and necessarily **incomplete**; `UNKNOWN` is a real outcome, not a failure. The verdict is validated *differentially* against an independent brute-force Kripke oracle (`satisfies_modal`) across K/T/S4/S5 in the test suite.

The call returns a `ModalVerdict` (dataclass) with fields `status`, `frame`, `mode`, `method`, `countermodel`, `prove_output`, `refute_output`, `prove_elapsed`, `refute_elapsed`, `infra_error`.

- **Locating Isabelle.** `find_isabelle()` looks at an explicit path, then `UFK_ISABELLE_HOME` / `ISABELLE_HOME`, then `isabelle` on `PATH`, then a light scan of standard install locations (no path is hard-coded). **Linux/macOS is the primary path** — `isabelle` is invoked directly; **Windows** is also supported, with the build routed through Isabelle's bundled Cygwin automatically (path translation + launcher exec-bit fixup).
- **Classical FOL / MSFOL.** `isabelle_decide_fol(φ, *, msfol=False, …)` decides classical validity the same way (prove-battery → nitpick finite counter-model), returning a `FolVerdict` (same fields as `ModalVerdict`, minus `frame` / `mode`). FOL is only semi-decidable, so `UNKNOWN` is common; equality is the **uninterpreted** `feq` / `fneq` of the embedding (no equality axioms are assumed, so `∀x. x = x` is *not* valid here).
- **Counter-models.** An `INVALID` verdict in the propositional alethic fragment carries a concrete Kripke counter-model in `ModalVerdict.countermodel`, reconstructed from `satisfies_modal` (`isabelle build` does not echo nitpick's model). For `Always`/`Eventually` together with `Next`, the refute theory defines the henceforth relation as the reflexive-transitive closure of the one-step relation, so the closure fragment is genuinely refuted rather than left `UNKNOWN`.
- **Any theory.** `check_theory(theory_text, theory_name)` builds an arbitrary self-contained theory and returns a `BuildResult` — used internally, and handy for the non-modal exporters (`to_isabelle_fol`, `to_isabelle_k3lp`, `to_isabelle_intuitionistic`, …), whose emitted proofs are themselves built against real Isabelle in the test suite.
