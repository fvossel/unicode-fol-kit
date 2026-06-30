"""Execute every ```python code block in README.md and assert none raise.

The blocks are run cumulatively in one shared namespace, in document order, so a
later snippet may build on names introduced by an earlier one — exactly how a
reader following the README would experience it. This is the end-to-end guard
that the documentation's examples actually run against the current code.

A block may opt out with a ``# doctest: +SKIP`` marker on any line (used for the
rare snippet that needs an external binary such as Prover9).
"""

import contextlib
import io
import pathlib
import re

import pytest

_README = pathlib.Path(__file__).parent.parent / "README.md"
_BLOCK_RE = re.compile(r"```python\n(.*?)```", re.DOTALL)


def _python_blocks():
    """Return (index, source) for each ```python block, skipping opted-out ones."""
    text = _README.read_text(encoding="utf-8")
    blocks = []
    for i, match in enumerate(_BLOCK_RE.finditer(text)):
        src = match.group(1)
        if "# doctest: +SKIP" in src or "# noqa: readme-skip" in src:
            continue
        blocks.append((i, src))
    return blocks


_BLOCKS = _python_blocks()


def test_readme_has_examples():
    """Guard against a regex/format change silently matching zero blocks.

    The README is intentionally slim (the full, per-logic worked examples live in
    the Sphinx docs under ``docs/`` and are verified there); it carries the
    runnable quickstart snippet, so this only guards that at least one block is
    still detected and executed.
    """
    assert len(_BLOCKS) >= 1, f"only {len(_BLOCKS)} python blocks found in README"


def test_readme_examples_execute():
    """Run all README python blocks cumulatively; report every failure.

    The shared namespace is pre-seeded with the package's public API (the names a
    reader is assumed to have imported), so continuation snippets that reference
    e.g. ``Atom`` without re-importing it run as a reader would experience them.
    Blocks that contain their own ``import`` lines still execute those lines, so
    import correctness for the public API is exercised too.
    """
    shared: dict = {"__name__": "__readme__"}
    exec("from unicode_fol_kit import *", shared)
    failures = []
    for index, src in _BLOCKS:
        try:
            with contextlib.redirect_stdout(io.StringIO()):
                exec(compile(src, f"<README block {index}>", "exec"), shared)
        except Exception as exc:  # noqa: BLE001 — surface every failing block
            first = next((ln for ln in src.splitlines() if ln.strip()), "")
            failures.append(f"block {index}: {type(exc).__name__}: {exc}\n    first line: {first.strip()}")
    assert not failures, "README example(s) failed:\n" + "\n".join(failures)
