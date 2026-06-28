# Quickstart

A five-minute tour: parse a classical first-order formula, check its validity, round-trip it back to Unicode and LaTeX, and try one non-classical logic. Every example below runs against the installed package as shown.

## Parse and check validity

`MSFLParser()` (no flags) is classical FOL. `parse()` returns an AST; `is_valid` decides validity with Z3.

```python
from unicode_fol_kit import MSFLParser, is_valid

parse = MSFLParser().parse

is_valid(parse("P ∨ ¬P"))   # → True   (excluded middle)
is_valid(parse("P → Q"))    # → False  (not valid)

# A full syllogism, written as one implication:
is_valid(parse(
    "∀x (Human(x) → Mortal(x)) → (Human(socrates) → Mortal(socrates))"
))                          # → True
```

Note that a single lowercase letter like `x` is a *variable*; an individual constant needs a multi-character name such as `socrates`.

## Round-trip to Unicode and LaTeX

`to_unicode_str()` is the inverse of parsing: it renders any node back to a parseable Unicode string, and re-parsing reproduces a structurally equal AST. The renderer is precedence-aware — it inserts only the parentheses the grammar requires.

```python
from unicode_fol_kit import MSFLParser

parse = MSFLParser().parse

ast = parse("∀x (Human(x) → Mortal(x))")

ast.to_unicode_str()              # → '∀x (Human(x) → Mortal(x))'
parse(ast.to_unicode_str()) == ast   # → True

ast.to_latex()                    # → '\\forall x\\, (Human(x) \\rightarrow Mortal(x))'
```

`to_latex()` uses the same precedence rules, so parentheses are reconstructed (not copied from the original spelling):

```python
ast2 = parse("P(x) ∧ (Q(x) ∨ R(x))")
ast2.to_unicode_str()   # → 'P(x) ∧ (Q(x) ∨ R(x))'
ast2.to_latex()         # → 'P(x) \\land (Q(x) \\lor R(x))'
```

## One non-classical taster: modal validity

Pass `modal=True` to parse `□`/`◇`. `is_modal_valid` decides propositional modal validity in-process over a chosen frame (K, T, D, B, K4, S4, S5, …), returning a Kripke counter-model internally where one exists.

```python
from unicode_fol_kit import MSFLParser, is_modal_valid

mp = MSFLParser(modal=True).parse

# The K distribution axiom holds in the minimal frame K:
is_modal_valid(mp("□(P → Q) → (□P → □Q)"), frame="K")   # → True

# The T axiom (□P → P) needs reflexivity: invalid in K, valid in T:
is_modal_valid(mp("□P → P"), frame="K")   # → False
is_modal_valid(mp("□P → P"), frame="T")   # → True
```

## Another taster: a three-valued truth table

`truth_table(formula, logic=...)` builds a `TruthTable` over classical, Kleene **K3**, or Priest **LP** values. Each distinct atom is a propositional variable. Excluded middle is a classical tautology but *not* a K3 tautology — when `P` is undefined (½), `P ∨ ¬P` is also ½, which K3 does not designate:

```python
from unicode_fol_kit import MSFLParser, truth_table

parse = MSFLParser().parse

truth_table(parse("P ∨ ¬P"), logic="classical").is_tautology   # → True
truth_table(parse("P ∨ ¬P"), logic="K3").is_tautology          # → False

print(truth_table(parse("P ∨ ¬P"), logic="K3").render())
# | P | P ∨ ¬P |
# |---|---|
# | 1 | 1 |
# | ½ | ½ |
# | 0 | 1 |
```

For a single valuation, `kleene_value` evaluates directly over {0, ½, 1}:

```python
from unicode_fol_kit import MSFLParser, kleene_value

kleene_value(MSFLParser().parse("P ∨ ¬P"), {"P": 0.5})   # → 0.5
```

## Next steps

The kit has four proof methods and a model finder across several logics, plus modal, fuzzy, second-order, and intuitionistic modes. To pick the right entry point for a given question and logic, see **Choosing a tool**.
