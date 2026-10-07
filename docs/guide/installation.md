# Installation

`unicode-logic-kit` is a pure-Python package. Its solver backend (Z3) is pulled in automatically, so a fresh install can parse, render, and check satisfiability out of the box.

## Supported Python

Python 3.10 or newer (tested on 3.10, 3.11, 3.12 and 3.13).

## Via pip

```bash
pip install unicode-logic-kit
```

This installs the two runtime dependencies — `lark` (the parser) and `z3-solver` — so `MSFLParser`, the renderers, and the Z3-backed checks (`satisfies()`, `to_z3()`, `from_z3()`) work immediately with no further setup.

## Coming from `unicode-fol-kit`

Up to 0.30.0 the package was called `unicode-fol-kit` and imported as `unicode_fol_kit`. It was renamed in 0.31.0, because first-order logic is one of the logics it handles and not the whole of it. To move over:

```bash
pip uninstall unicode-fol-kit
pip install unicode-logic-kit
```

and replace `unicode_fol_kit` by `unicode_logic_kit` in your imports. Nothing else changed its name: the modules, the functions and the `UFK_` environment variables are as they were.

Code that still says `import unicode_fol_kit` keeps running. `unicode-fol-kit` 0.31.0 holds no logic of its own: it installs `unicode-logic-kit` and forwards the old import name to it, so `pip install -U unicode-fol-kit` is enough to get every later release. The forwarded modules are the modules of `unicode_logic_kit` themselves, not copies, so objects reached through the two names mix freely; `python -m unicode_fol_kit.mcp` runs as before, and an extra is passed on (`unicode-fol-kit[mcp]` installs `unicode-logic-kit[mcp]`). The first import raises a `DeprecationWarning` that names the new import.

One combination to avoid: `unicode-fol-kit` 0.30.0 or older installed next to `unicode-logic-kit`. The two are then separate copies of the same code under two names, and a formula built with one is not an instance of the other's classes. Upgrading `unicode-fol-kit` to 0.31.0, or uninstalling it, resolves that. What changes for a logger or a filter that matched on the old name: the modules now report themselves as `unicode_logic_kit.…`.

## Via git clone

```bash
git clone https://github.com/fvossel/unicode-logic-kit.git
cd unicode-logic-kit
pip install .
```

## Verify the install

```python
from unicode_logic_kit import MSFLParser

formula = MSFLParser().parse("∀x (Human(x) → Mortal(x))")
print(formula.to_unicode_str())
# → ∀x (Human(x) → Mortal(x))
```

## Optional external tools

Z3 ships with the package. A few features instead drive *external* theorem provers, which you install separately and point at by passing the executable's path:

- **Prover9** — used by `check_logical_entailment(premises, conclusion, prover9_path=...)`. The `"prover9"` backend of `api.prove` finds the binary through `$UFK_PROVER9`, then `PATH`. A Linux Prover9 inside WSL is reached with `$UFK_PROVER9=<path inside WSL>` and `$UFK_PROVER9_WSL=1` (or `use_wsl=True`, with the path inside WSL as `prover9_path`).
- **Vampire** — used by `check_logical_entailment_vampire(premises, conclusion, vampire_path=...)`; on Windows it can drive a Vampire installed in WSL via `use_wsl=True`.
- **Isabelle** — used by `isabelle_decide_modal(...)` (in `unicode_logic_kit.hol.isabelle_runner`) to actually *run* the modal embeddings; `isabelle_available()` / `find_isabelle()` locate the installation.

None of these are required for the core toolkit — the HOL/THF/Isabelle *exporters* emit problem files without a prover present, and entailment over finite models, resolution, tableaux, and the Z3 checks all run with the base install alone.
