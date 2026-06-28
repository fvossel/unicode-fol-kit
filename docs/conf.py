"""Sphinx configuration for the unicode-fol-kit documentation.

Builds a narrative guide (MyST Markdown pages under ``guide/``) plus an
autosummary-driven API reference that pulls the package's rich docstrings. The
package is imported for the version and for autodoc, so the build environment must
have ``unicode-fol-kit`` installed (Read the Docs does this via ``.readthedocs.yaml``).
"""

import os
import sys
from datetime import date

# Make the package importable for autodoc / version discovery.
sys.path.insert(0, os.path.abspath(".."))

try:
    from unicode_fol_kit import __version__ as _version
except Exception:  # pragma: no cover - fallback if the package is not installed yet
    _version = "0.0.0"

# -- Project information ------------------------------------------------------
project = "unicode-fol-kit"
author = "Felix Vossel"
copyright = f"{date.today().year}, {author}"
release = _version
version = _version

# -- General configuration ---------------------------------------------------
extensions = [
    "sphinx.ext.autodoc",
    "sphinx.ext.autosummary",
    "sphinx.ext.napoleon",
    "sphinx.ext.intersphinx",
    "sphinx.ext.viewcode",
    "myst_parser",
]

# MyST (Markdown) configuration — the guide pages are written in Markdown.
myst_enable_extensions = [
    "colon_fence",     # ::: fenced directives
    "deflist",         # definition lists
    "smartquotes",
    "substitution",
]
myst_heading_anchors = 3

source_suffix = {
    ".rst": "restructuredtext",
    ".md": "markdown",
}

templates_path = ["_templates"]
exclude_patterns = ["_build", "Thumbs.db", ".DS_Store"]

# -- Autodoc / autosummary ---------------------------------------------------
autosummary_generate = True
autodoc_default_options = {
    "members": True,
    "undoc-members": False,
    "show-inheritance": True,
    "member-order": "bysource",
}
autodoc_typehints = "description"
autodoc_member_order = "bysource"
napoleon_google_docstring = True
napoleon_numpy_docstring = False
# Optional external provers / z3 are real dependencies, but mock anything that may
# be missing in a minimal docs environment so autodoc never fails to import.
autodoc_mock_imports = []

# -- Intersphinx -------------------------------------------------------------
intersphinx_mapping = {
    "python": ("https://docs.python.org/3", None),
}

# -- HTML output -------------------------------------------------------------
html_theme = "furo"
html_title = f"unicode-fol-kit {release}"
html_static_path = ["_static"]
html_theme_options = {
    "source_repository": "https://github.com/fvossel/unicode-fol-kit/",
    "source_branch": "main",
    "source_directory": "docs/",
}
