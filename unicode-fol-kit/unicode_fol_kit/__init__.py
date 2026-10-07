"""The former name of :mod:`unicode_logic_kit`.

The package was renamed in 0.31.0. This module keeps an import of the old name
working: ``unicode_fol_kit`` and every one of its submodules ARE the modules of
``unicode_logic_kit``. They are the same objects, not copies, so a class
imported under one name is the class imported under the other, an ``isinstance``
check holds across the two, and an object pickled under the old name loads.
``python -m unicode_fol_kit`` and ``python -m unicode_fol_kit.mcp`` run the
modules of the new name.

Importing it raises one :class:`DeprecationWarning` that names the new import.
"""

import importlib
import importlib.abc
import importlib.machinery
import importlib.util
import sys
import warnings

_OLD = "unicode_fol_kit"
_NEW = "unicode_logic_kit"


def _renamed(name: str) -> str:
    """The module of the new package that ``name`` of the old one stands for."""
    return _NEW + name[len(_OLD):]


class _Forwarder(importlib.abc.MetaPathFinder, importlib.abc.Loader):
    """Finds ``unicode_fol_kit.x`` and loads it as the module ``unicode_logic_kit.x``.

    The loader does not execute anything under the old name. ``exec_module``
    imports the module of the new name and puts THAT object into
    ``sys.modules`` under the old one; the import system returns whatever is
    registered there once ``exec_module`` is back, so the caller gets the real
    module, with the ``__name__`` and ``__spec__`` it has always had.
    """

    def find_spec(self, fullname, path=None, target=None):
        if fullname != _OLD and not fullname.startswith(_OLD + "."):
            return None
        real = importlib.util.find_spec(_renamed(fullname))
        if real is None:
            return None
        spec = importlib.machinery.ModuleSpec(
            fullname, self, origin=real.origin,
            is_package=real.submodule_search_locations is not None)
        if real.submodule_search_locations is not None:
            spec.submodule_search_locations = list(real.submodule_search_locations)
        return spec

    def create_module(self, spec):
        return None

    def exec_module(self, module):
        sys.modules[module.__name__] = importlib.import_module(_renamed(module.__name__))

    def get_code(self, fullname):
        """The code of the module of the new name: what ``python -m`` runs."""
        real = importlib.util.find_spec(_renamed(fullname))
        if real is None or not hasattr(real.loader, "get_code"):
            return None
        return real.loader.get_code(real.name)


warnings.warn(
    "the package unicode_fol_kit was renamed to unicode_logic_kit in 0.31.0: write "
    "'import unicode_logic_kit' and install 'unicode-logic-kit'. The old name is "
    "forwarded for now and nothing else changes.",
    DeprecationWarning, stacklevel=2)

if not any(isinstance(finder, _Forwarder) for finder in sys.meta_path):
    sys.meta_path.insert(0, _Forwarder())

# The import system returns sys.modules[__name__] when this file has run, so the
# name unicode_fol_kit is bound to the package of the new name itself.
sys.modules[__name__] = importlib.import_module(_NEW)
