"""``docs/api.md`` claims to be complete. This is the claim, enforced.

The page says "every name in ``unicode_fol_kit.__all__`` and in each
subpackage's ``__all__`` appears in exactly one table below". A hand-maintained
page drifts the moment someone exports something new, and the drift is
invisible — nothing fails, a name is simply undocumented. So the claim is a
test: add a public name without listing it and this goes red, with the name in
the message.

It checks the two directions separately, because they fail for different
reasons: a MISSING name means new code shipped undocumented, an UNKNOWN entry
means the page still lists something that was renamed or withdrawn.
"""

import importlib
import io
import os
import re

import pytest

import unicode_fol_kit

DOCS = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                    "docs", "api.md")

#: Subpackages whose ``__all__`` is part of the public surface. Anything a
#: caller can import from ``unicode_fol_kit.<name>`` belongs in the reference.
SUBPACKAGES = ["semantics", "eval", "prob", "chem", "ilp", "dl", "hets",
               "drt", "hol", "atp", "fol", "comorphism"]

#: Names in ``unicode_fol_kit.__all__`` that ARE subpackages. They are covered
#: by the module section at the end of the page rather than by a name table.
SUBPACKAGE_NAMES = {"dl", "prob", "chem", "ilp"}

#: An autosummary entry: three spaces of indent inside an ``eval-rst`` block.
_ENTRY = re.compile(r"^   ([A-Za-z_][A-Za-z0-9_.]*)$", re.MULTILINE)


def listed_entries():
    with io.open(DOCS, encoding="utf-8") as handle:
        return set(_ENTRY.findall(handle.read()))


def listed_names():
    """The bare names — the module section's dotted paths are not names."""
    return {entry for entry in listed_entries() if "." not in entry}


def required_names():
    names = set(unicode_fol_kit.__all__) - SUBPACKAGE_NAMES
    for subpackage in SUBPACKAGES:
        module = importlib.import_module("unicode_fol_kit." + subpackage)
        names |= set(getattr(module, "__all__", ()))
    return names


def test_every_public_name_is_in_the_api_reference():
    missing = sorted(required_names() - listed_names())

    assert not missing, (
        f"{len(missing)} public names are missing from docs/api.md: "
        f"{missing}. Add each to the section it belongs to — the page's own "
        "opening paragraph promises they are all there.")


def test_the_reference_lists_nothing_that_no_longer_exists():
    """Every bare name on the page must still be importable from somewhere —
    from the top level, from a subpackage, or as a module."""
    known = required_names() | SUBPACKAGE_NAMES
    for subpackage in SUBPACKAGES:
        known.add(subpackage.split(".")[0])
        module = importlib.import_module("unicode_fol_kit." + subpackage)
        known |= {n for n in dir(module) if not n.startswith("_")}
    known |= {n for n in dir(unicode_fol_kit) if not n.startswith("_")}

    stale = sorted(listed_names() - known)
    assert not stale, f"docs/api.md lists names that do not exist: {stale}"


def test_every_module_the_reference_lists_can_be_imported():
    """The module section's dotted entries are import paths, so a renamed or
    deleted module shows up here rather than as a broken page."""
    broken = []
    for entry in sorted(e for e in listed_entries() if "." in e):
        try:
            importlib.import_module("unicode_fol_kit." + entry)
        except ImportError as exc:                       # pragma: no cover
            broken.append(f"{entry}: {exc}")
    assert not broken, f"docs/api.md lists unimportable modules: {broken}"


@pytest.mark.parametrize("subpackage", SUBPACKAGES)
def test_each_subpackage_declares_what_it_exports(subpackage):
    """The completeness check reads ``__all__``; a subpackage without one
    would silently contribute nothing and the page would look complete."""
    module = importlib.import_module("unicode_fol_kit." + subpackage)

    assert getattr(module, "__all__", None), (
        f"unicode_fol_kit.{subpackage} has no __all__, so nothing enforces "
        "that its public names reach the API reference")
