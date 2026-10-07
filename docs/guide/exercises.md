# Generating exercises: constructive, no LLM, independently checked

`unicode_logic_kit.eval.exercise_gen` manufactures small logic exercises —
valid/invalid formula pairs, Fitch proofs of a chosen depth, and theories with
a chosen minimal finite model size — instead of scoring ones a student or an
LLM already produced. Nothing in this module calls an LLM: every answer key
is either decided by a genuine decision procedure or assembled by hand from
sound primitives, and every generator re-checks its own output by an
independent route before returning it.

```{note}
Each generator is deliberately narrower than "generate any exercise of this
shape" might suggest — see each function's own docstring for exactly why. The
short version: this kit's search procedures (`find_fitch_proof`, the finite
model finder) are honest about being *bounded*, so a generator built on top of
them never turns "search failed" into "proved". `generate_entailment_with_proof`
sidesteps this by building its proof directly rather than searching for one;
`generate_theory_with_model_size` sidesteps it by additionally confirming, with
{func}`~unicode_logic_kit.semantics.modelfinder.is_size_exhaustive`, that every
smaller size it needs to rule out was actually *searched* and not silently
skipped.
```

## Valid/invalid formula pairs

`generate_valid_invalid_pair` samples quantifier-free formulas over 0-ary
predicates from a `Signature` and classifies each with the kit's truth-table
decision procedure — complete for this fragment, so "valid" is never a guess.

```python
from unicode_logic_kit.fol.signature import Signature
from unicode_logic_kit.eval.exercise_gen import generate_valid_invalid_pair

sig = Signature.from_dict({"predicates": {"P": 0, "Q": 0, "R": 0, "Precedes": 2}})
pair = generate_valid_invalid_pair(sig, max_atoms=2, seed=7)

print(pair.valid_formula.to_unicode_str())
# → P ∨ ¬P → (¬Q ∧ ¬Q) ∨ Q
print(pair.invalid_formula.to_unicode_str())
# → Q ∨ ((¬P ∨ (¬P → Q)) ∧ P)
print(dict(pair.invalid_valuation))
# → {'Q': False, 'P': False}   -- a genuine falsifying assignment
```

`invalid_valuation` is a plain `{atom: bool}` mapping, so it can be checked
against `invalid_formula` on its own terms — for instance by rebuilding it as
a {class}`~unicode_logic_kit.semantics.tarski.Structure` and calling
{func}`~unicode_logic_kit.semantics.tarski.models`, exactly as
`tests/test_exercise_gen.py` does, independently of the truth table that
produced it.

## Fitch proofs of a chosen depth

`generate_entailment_with_proof` does not search for a proof and then measure
its depth — {func}`~unicode_logic_kit.atp.fitch_search.find_fitch_proof`'s own
docstring says a depth-bounded search returning `None` never certifies that a
shallower proof doesn't exist, so "no proof at depth d−1" could never honestly
become "the minimal proof has depth d". Instead this generator *builds* a
derivation with exactly the requested number of nested subproof levels — a
chain of `→I` introductions, one box per requested atom — and checks it with
{func}`~unicode_logic_kit.atp.fitch.verify_proof` before returning it.

```python
from unicode_logic_kit.eval.exercise_gen import generate_entailment_with_proof

ex = generate_entailment_with_proof(sig, target_depth=2, seed=7)
print(ex.conclusion.to_unicode_str())
# → Q → P → P
print(ex.proof.to_fitch(ascii=True))
```
```text
1 | | Q         Assume
  | +------
2 | | | P       Assume
  | | +------
3 | | | P       Reit 2
4 | | P → P     →I 2–3
5 | Q → P → P   →I 1–4
```

`ex.depth == 2` here — a STATIC count of nested `Subproof` levels, i.e. "the
worked solution has depth 2", never "the minimal proof has depth 2".

## Theories with a chosen minimal model size

`generate_theory_with_model_size` builds a strict total order (irreflexive,
transitive, total) over one binary predicate from `signature`, plus a chain
constraint forcing the order to contain at least `target_size` pairwise
distinct elements — the textbook fact that an irreflexive total order needs
domain size ≥ 2, generalised to an arbitrary chain length.

```python
from unicode_logic_kit.eval.exercise_gen import generate_theory_with_model_size

ms = generate_theory_with_model_size(sig, target_size=2, seed=7)
for f in ms.theory:
    print(f.to_unicode_str())
```
```text
∀x ¬Precedes(x, x)
∀x ∀y ∀z (Precedes(x, y) ∧ Precedes(y, z) → Precedes(x, z))
∀x ∀y (Precedes(x, y) ∨ (x = y ∨ Precedes(y, x)))
∃e0 ∃e1 Precedes(e0, e1)
```

`ms.witness` is a concrete 2-element model (`ms.witness.domain == (0, 1)`,
with `Precedes` holding of `(1, 0)`); `ms.target_size == 2` is genuinely
minimal, not merely "no smaller model was found" — the generator refuses
outright (`ValueError`) rather than ship that claim if any smaller size's
search space exceeds `max_candidates` and would only have been *skipped*, not
searched. Because a binary relation's interpretation count grows as `2**(k*k)`,
this is also why `target_size` cannot grow far past 4 under the default
budget without raising `max_candidates` explicitly — the refusal is
deliberate, not a bug:

```python
generate_theory_with_model_size(sig, target_size=5, seed=1)
# raises ValueError: ... domain size 5's interpretation space exceeds
#   max_candidates=1048576 and would be SKIPPED, not exhaustively
#   searched or refuted, by find_model ...
```

## Reproducibility

Every generator takes an optional `seed`; the same seed always reproduces a
byte-identical exercise (same AST, same rendered text, same proof, same
witness structure) — `seed=None` draws from unseeded system randomness
instead. All three functions also refuse loudly, rather than approximate,
when `signature` cannot support the request — for instance too few 0-ary
predicates for `generate_valid_invalid_pair` / `generate_entailment_with_proof`,
or no binary predicate at all for `generate_theory_with_model_size`.
