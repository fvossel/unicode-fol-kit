# Installation

`unicode-fol-kit` is a pure-Python package. Its solver backend (Z3) is pulled in automatically, so a fresh install can parse, render, and check satisfiability out of the box.

## Supported Python

Python 3.10 or newer (tested on 3.10, 3.11, and 3.12).

## Via pip

```bash
pip install unicode-fol-kit
```

This installs the two runtime dependencies — `lark` (the parser) and `z3-solver` — so `MSFLParser`, the renderers, and the Z3-backed checks (`satisfies()`, `to_z3()`, `from_z3()`) work immediately with no further setup.

## Via git clone

```bash
git clone https://github.com/fvossel/unicode-fol-kit.git
cd unicode-fol-kit
pip install .
```

## Verify the install

```python
from unicode_fol_kit import MSFLParser

formula = MSFLParser().parse("∀x (Human(x) → Mortal(x))")
print(formula.to_unicode_str())
# → ∀x (Human(x) → Mortal(x))
```

## Optional external tools

Z3 ships with the package. A few features instead drive *external* theorem provers, which you install separately and point at by passing the executable's path:

- **Prover9** — used by `check_logical_entailment(premises, conclusion, prover9_path=...)`.
- **Vampire** — used by `check_logical_entailment_vampire(premises, conclusion, vampire_path=...)`; on Windows it can drive a Vampire installed in WSL via `use_wsl=True`.
- **Isabelle** — used by `isabelle_decide_modal(...)` (in `unicode_fol_kit.hol.isabelle_runner`) to actually *run* the modal embeddings; `isabelle_available()` / `find_isabelle()` locate the installation.

None of these are required for the core toolkit — the HOL/THF/Isabelle *exporters* emit problem files without a prover present, and entailment over finite models, resolution, tableaux, and the Z3 checks all run with the base install alone.
