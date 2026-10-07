# unicode-fol-kit is now unicode-logic-kit

The package was renamed in 0.31.0, because first-order logic is one of the
logics it handles and not the whole of it. The code, the documentation and every
later release are under the new name:

- PyPI: <https://pypi.org/project/unicode-logic-kit/>
- Source: <https://github.com/fvossel/unicode-logic-kit>
- Documentation: <https://unicode-logic-kit.readthedocs.io/>

## What to change

```bash
pip uninstall unicode-fol-kit
pip install unicode-logic-kit
```

```python
import unicode_logic_kit          # was: import unicode_fol_kit
```

Nothing else changes: the modules, the functions and the `UFK_` environment
variables keep their names.

## What this release does

`unicode-fol-kit` 0.31.0 holds no logic of its own. It installs
`unicode-logic-kit` and forwards the old import name to it, so existing code
keeps running until you have changed the import:

- `import unicode_fol_kit` and `from unicode_fol_kit.atp import ...` give the
  modules of `unicode_logic_kit` themselves, not copies, so objects from the two
  names mix freely.
- `python -m unicode_fol_kit` and `python -m unicode_fol_kit.mcp` run as before.
- Each extra is passed on: `unicode-fol-kit[mcp]` installs
  `unicode-logic-kit[mcp]`.
- The first import raises a `DeprecationWarning` that names the new import.

Do not keep `unicode-fol-kit` 0.30.0 or older installed next to
`unicode-logic-kit`: the two would be separate copies of the same code under two
names. Upgrading `unicode-fol-kit` to 0.31.0, or uninstalling it, resolves that.

No further release of `unicode-fol-kit` is planned. New versions of the kit
reach an existing installation through the dependency on `unicode-logic-kit`.
