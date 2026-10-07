"""Shared HTML-rendering primitives for the ``atp`` proof renderers.

:meth:`~unicode_logic_kit.atp.fitch.Proof.to_html` and
:meth:`~unicode_logic_kit.atp.sequent.Derivation.to_html` both render a
self-contained, theme-aware HTML page in the same idiom already established by
:meth:`unicode_logic_kit.fol.derivation.CCGDerivation.to_html` — a ``<!doctype
html>`` page, CSS custom properties themed via both
``@media(prefers-color-scheme:dark)`` *and* a ``:root[data-theme=dark]``
override, and HTML-escaping of every user-supplied string (predicate/variable
names, surface text). This private module holds the pieces genuinely common
to the two ``atp`` renderers — escaping, a shared base colour palette, and the
page wrapper — so :mod:`~unicode_logic_kit.atp.fitch` and
:mod:`~unicode_logic_kit.atp.sequent` do not each reimplement them.

It deliberately does **not** import from :mod:`unicode_logic_kit.fol.derivation`
(nor the reverse): every ``unicode_logic_kit.atp`` module already imports
``unicode_logic_kit.fol`` at module scope (``Node`` and friends), so ``atp`` →
``fol`` is the established one-way dependency direction — ``fol`` only ever
reaches into ``atp`` from inside a function body (e.g. ``fol.qml``,
``fol.modal_translation``, ``fol._fol_nodes``, all lazily importing
``atp.z3_models``/``atp.z3_input`` to keep ``fol`` importable without ``z3``).
Having ``fol/derivation.py`` import this module at module scope would invert
that and risks a real import cycle (``fol/__init__.py`` imports
``.derivation`` eagerly). The handful of lines duplicated below
(``esc_html``) are therefore an intentional, explicitly-permitted duplicate of
``fol.derivation._esc_html`` rather than a cross-package import — see the C56
roadmap item.
"""

__all__: list = []  # private helper module; nothing here is part of the public API


def esc_html(s: str) -> str:
    """Escape ``&``, ``<``, ``>`` for safe inclusion in HTML text content.

    Mirrors ``fol.derivation._esc_html`` exactly (a stable, three-line
    function); duplicated here rather than imported, see the module docstring.
    """
    return s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


# Shared colour tokens (page background / ink / muted text / rule lines /
# accent), following the exact idiom CCGDerivation.to_html() established:
# default (light) values live in :root, overridden both by the OS-level
# prefers-color-scheme media query and by an explicit :root[data-theme=...]
# attribute a host page can set to force one theme regardless of the OS.
_LIGHT_VARS = "--pg:#faf9f6;--ink:#23232a;--muted:#6b6b76;--bar:#3f3f47;--accent:#1c46b0"
_DARK_VARS = "--pg:#15151a;--ink:#e9e8e4;--muted:#a6a6b0;--bar:#c3c3cd;--accent:#84a6ff"

BASE_CSS = (
    "\n:root{%s}"
    "\n@media(prefers-color-scheme:dark){:root{%s}}"
    "\n:root[data-theme=light]{%s}"
    "\n:root[data-theme=dark]{%s}"
    "\nbody{margin:0;background:var(--pg);color:var(--ink)}\n"
) % (_LIGHT_VARS, _DARK_VARS, _LIGHT_VARS, _DARK_VARS)


def html_page(title: str, body_html: str, extra_css: str) -> str:
    """Wrap ``body_html`` in a self-contained, theme-aware HTML page.

    Same skeleton as ``CCGDerivation.to_html()``'s page wrapper: a
    ``<!doctype html>`` document with a viewport meta tag and one inline
    ``<style>`` combining the shared colour tokens (:data:`BASE_CSS`) with the
    caller's ``extra_css``. ``title`` is HTML-escaped.
    """
    return (
        "<!doctype html>\n<html><head><meta charset=\"utf-8\">\n"
        "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n"
        "<title>%s</title>\n<style>%s%s</style></head>\n<body>\n%s\n</body></html>\n"
        % (esc_html(title), BASE_CSS, extra_css, body_html)
    )
