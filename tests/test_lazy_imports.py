"""Import-time laziness regression tests.

``unicode_logic_kit.eval.metric_hf``'s module docstring/comments claim that
importing the module (and, transitively, ``unicode_logic_kit`` itself) never
pulls in the optional ``evaluate``/``datasets`` packages -- only
*instantiating* :class:`~unicode_logic_kit.eval.metric_hf.FolEquivalence`
(directly, via :func:`~unicode_logic_kit.eval.metric_hf.load`, or via the
module-level ``__getattr__`` PEP 562 hook that name goes through) does. This
file is the test suite that actually pins that claim down -- it is a wiring
check, not new solver math, so there is nothing here to hand-derive: every
assertion is "name X is/is not a key of ``sys.modules``" at a specific point
in the import sequence.

Whether these assertions are interesting locally depends on whether
``evaluate``/``datasets`` are installed in this venv at all: if they are
not, ``'evaluate' not in sys.modules`` holds trivially (nothing could ever
put it there) and does not exercise the laziness fix. The subprocess test
below is unconditional (it is the same check either way, just run in a
fresh interpreter so no earlier test's ``sys.modules`` state can mask a
regression); the module-reimport tests that check the "accessing
FolEquivalence DOES trigger the import" half are skipped when the packages
are absent, since there would be nothing to import.
"""

import importlib
import os
import subprocess
import sys

import pytest

from unicode_logic_kit.eval import metric_hf


# ---------------------------------------------------------------------------
# Package-level check, in a fresh subprocess.
#
# Run from a brand-new interpreter rather than in-process: by the time this
# test file runs, other test modules in the same pytest session may already
# have imported `evaluate`/`datasets` as a side effect of exercising
# FolEquivalence, which would make an in-process `'evaluate' not in
# sys.modules` check pass or fail for the wrong reason. A subprocess with
# nothing loaded yet is the only way to observe the effect of `import
# unicode_logic_kit` alone, in isolation.
# ---------------------------------------------------------------------------

def test_importing_unicode_logic_kit_subprocess_does_not_import_evaluate_or_datasets():
    """The user-facing regression check this whole change exists for: a bare
    ``import unicode_logic_kit`` must never put ``'evaluate'`` or
    ``'datasets'`` into ``sys.modules`` -- regardless of whether those
    optional packages happen to be installed, since the package is not even
    trying to use them yet. See the module docstring for why this needs to
    run in a fresh subprocess rather than against the current process's
    ``sys.modules``.
    """
    result = subprocess.run(
        [sys.executable, "-c",
         "import unicode_logic_kit, sys\n"
         "assert 'evaluate' not in sys.modules, 'evaluate leaked into sys.modules'\n"
         "assert 'datasets' not in sys.modules, 'datasets leaked into sys.modules'\n"],
        capture_output=True, text=True,
        cwd=os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
    )
    assert result.returncode == 0, (
        f"subprocess failed (stdout={result.stdout!r}, stderr={result.stderr!r})")


# ---------------------------------------------------------------------------
# Module-level check: a fresh (in-process) reimport of metric_hf.py alone,
# then touching FolEquivalence, with the real packages -- skipped if they
# are not actually installed, since there is then nothing to observe on
# either side of the assertion.
#
# Mirrors tests/test_metric_hf.py's
# test_module_importable_and_raises_importerror_without_evaluate: deleting
# both the target packages and metric_hf.py's own module entry from
# sys.modules and reimporting forces every import statement metric_hf.py
# contains to actually run, rather than short-circuiting on an
# already-cached sys.modules entry from some earlier test. monkeypatch
# restores all three sys.modules entries on teardown, so nothing here can
# leak into later tests.
# ---------------------------------------------------------------------------

@pytest.mark.skipif(not metric_hf._HAS_EVALUATE,
                    reason="evaluate/datasets not installed -- nothing to observe")
class TestLazinessWithEvaluateInstalled:

    def _fresh_reimport(self, monkeypatch):
        monkeypatch.delitem(sys.modules, "evaluate", raising=False)
        monkeypatch.delitem(sys.modules, "datasets", raising=False)
        monkeypatch.delitem(sys.modules, "unicode_logic_kit.eval.metric_hf", raising=False)
        return importlib.import_module("unicode_logic_kit.eval.metric_hf")

    def test_bare_module_import_does_not_import_evaluate_or_datasets(self, monkeypatch):
        """This is the test that actually encodes the bug being fixed: before
        this change, metric_hf.py's module-level ``try: import evaluate /
        import datasets`` ran unconditionally, so both names would already be
        in ``sys.modules`` right here, before anything ever touched
        ``FolEquivalence``. It must not be true any more."""
        self._fresh_reimport(monkeypatch)
        assert "evaluate" not in sys.modules
        assert "datasets" not in sys.modules

    def test_accessing_fol_equivalence_attribute_imports_evaluate_and_datasets(self, monkeypatch):
        """The other half of the contract: the cost is not skipped forever,
        just deferred -- touching ``FolEquivalence`` (attribute access, which
        is exactly what ``from ... import FolEquivalence`` and
        ``metric_hf.FolEquivalence`` both do) is what is allowed to pay it.
        """
        fresh = self._fresh_reimport(monkeypatch)
        assert "evaluate" not in sys.modules   # re-asserted: see test above

        fresh.FolEquivalence   # PEP 562 module __getattr__ fires here

        assert "evaluate" in sys.modules
        assert "datasets" in sys.modules

    def test_from_import_form_also_triggers_and_returns_a_usable_class(self, monkeypatch):
        """``from unicode_logic_kit.eval.metric_hf import FolEquivalence`` is
        the other documented access path (see the module's ``__getattr__``
        docstring) -- Python's ``from ... import`` machinery falls back to a
        module's ``__getattr__`` for a name it does not find as a plain
        attribute, so this must resolve to the same usable class, not an
        AttributeError."""
        self._fresh_reimport(monkeypatch)
        # Import machinery resolves through sys.modules, so this picks up
        # the freshly-reimported module set up by _fresh_reimport above.
        from unicode_logic_kit.eval.metric_hf import FolEquivalence
        assert "evaluate" in sys.modules
        instance = FolEquivalence()
        assert isinstance(instance, FolEquivalence)

    def test_fol_equivalence_is_cached_not_rebuilt_on_every_access(self, monkeypatch):
        """``_build_fol_equivalence_class`` must return the SAME class object
        every time, not a freshly-defined lookalike -- otherwise
        ``isinstance(metric_hf.load(), metric_hf.FolEquivalence)`` could fail
        depending on which of two separately-built classes each side saw."""
        fresh = self._fresh_reimport(monkeypatch)
        first = fresh.FolEquivalence
        second = fresh.FolEquivalence
        assert first is second


# ---------------------------------------------------------------------------
# __getattr__ must still behave like a normal module for every other name.
# ---------------------------------------------------------------------------

def test_getattr_raises_attribute_error_for_an_unknown_name():
    """PEP 562's contract: a module ``__getattr__`` must raise
    ``AttributeError`` (not, say, return ``None`` or an ``ImportError``) for
    any name it does not specifically handle, so ordinary attribute-error
    handling (``hasattr``, ``getattr(..., default)``, introspection tools)
    keeps working for everything that is not ``FolEquivalence``.
    """
    with pytest.raises(AttributeError, match="no_such_attribute_xyz"):
        metric_hf.no_such_attribute_xyz

    assert hasattr(metric_hf, "compute_fol_metrics")   # unaffected, ordinary attribute
    assert not hasattr(metric_hf, "no_such_attribute_xyz")
