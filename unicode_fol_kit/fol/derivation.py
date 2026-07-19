"""CCG-style derivation trees with lambda-semantics, and renderers.

A :class:`CCGDerivation` is a node in a bottom-up composition tree in the spirit of
ccg2lambda / depccg: a surface ``word`` (leaves), a CCG ``category`` (a display
string such as ``"(S\\NP)/NP"``), the ``term`` (a real toolkit lambda-term
:class:`~unicode_fol_kit.fol.nodes.Node`), a combinator ``rule`` label
(``fa`` / ``ba`` / ``bx`` / ``conj`` / ``lex`` / ``rp`` / …), and ``children``.

The semantics is genuinely *composed*, not hand-written: :meth:`CCGDerivation.forward`
and :meth:`CCGDerivation.backward` apply one child's term to the other and reduce it
with the toolkit's :func:`beta_reduce`, so the ``term`` at every internal node is the
actual beta-normal form of the composition — the same machinery that backs
``reduce_trace`` / ``beta_reduce``.

Three renderers are provided, mirroring the toolkit's existing ``to_unicode_str`` /
``to_latex`` / ``tree_str`` split:

- :meth:`~CCGDerivation.to_text` — a Unicode "prooftree": premises row, an inference
  bar with the combinator at its right, then the category over the lambda-term. This
  is a genuinely new rendering style for the toolkit (neither the indented
  ``render_sequent_proof`` nor the Fitch-bar ``render_fitch`` draws a Gentzen bar).
- :meth:`~CCGDerivation.to_latex` — a ``bussproofs`` ``prooftree`` (needs
  ``\\usepackage{bussproofs}``); each node's term is emitted via ``Node.to_latex``.
- :meth:`~CCGDerivation.to_html` — a self-contained, theme-aware HTML page in the
  ccg2lambda idiom (category red, lambda-term blue, combinator at the bar).

:func:`reduction_derivation` turns a beta-reduction path (``reduce_trace``) into a
``CCGDerivation`` chain, so a lambda reduction can be drawn with the same renderers.
"""

from dataclasses import dataclass
from typing import List, Optional, Tuple

from .nodes import Node, Application, beta_reduce, beta_eta_normalize

__all__ = ["CCGDerivation", "reduction_derivation"]


@dataclass(frozen=True)
class CCGDerivation:
    """One (sub)derivation: its combinator ``rule``, CCG ``category``, lambda ``term``,
    optional surface ``word`` (for leaves), and ``children`` (the premises).

    Build leaves with :meth:`leaf` and combine them with :meth:`forward` (``fa``),
    :meth:`backward` (``ba``), :meth:`unary` (``lex`` / ``rp`` / type-changing), or the
    low-level :meth:`combine`. The composing builders reduce the applied term to
    beta-normal form, so ``term`` is always the real semantics at that node.
    """

    rule: Optional[str] = None
    category: Optional[str] = None
    term: Optional[Node] = None
    word: Optional[str] = None
    children: Tuple["CCGDerivation", ...] = ()

    def __post_init__(self):
        """Coerce ``children`` to a tuple so this frozen node stays hashable."""
        if not isinstance(self.children, tuple):
            object.__setattr__(self, "children", tuple(self.children))

    # ---- constructors ---------------------------------------------------- #

    @classmethod
    def leaf(cls, word: str, category: str, term: Node) -> "CCGDerivation":
        """A lexical leaf: a ``word`` with its ``category`` and lambda ``term``."""
        return cls(rule=None, category=category, term=term, word=word, children=())

    @classmethod
    def unary(cls, rule: str, category: str, child: "CCGDerivation",
              term: Optional[Node] = None) -> "CCGDerivation":
        """A one-premise step (``lex`` type-raising, ``rp`` punctuation, …).

        ``term`` defaults to the child's term (an identity step such as ``rp``); pass
        an explicit ``term`` for a genuine type-change such as ``lex``.
        """
        return cls(rule=rule, category=category,
                   term=child.term if term is None else term,
                   word=None, children=(child,))

    @classmethod
    def combine(cls, rule: str, category: str,
                children: List["CCGDerivation"], term: Node) -> "CCGDerivation":
        """A general step with an explicitly supplied composed ``term``."""
        return cls(rule=rule, category=category, term=term,
                   word=None, children=tuple(children))

    @classmethod
    def forward(cls, category: str, functor: "CCGDerivation",
                argument: "CCGDerivation", *, rule: str = "fa",
                eta: bool = False) -> "CCGDerivation":
        """Forward application (``X/Y  Y -> X``): apply the LEFT child's term to the
        right and beta-normalise. The composed term is ``beta_reduce(functor.term
        argument.term)``. Raises :class:`ReductionLimitError` if that reduction does
        not terminate.
        """
        term = _apply(functor.term, argument.term, eta)
        return cls(rule=rule, category=category, term=term,
                   word=None, children=(functor, argument))

    @classmethod
    def backward(cls, category: str, argument: "CCGDerivation",
                 functor: "CCGDerivation", *, rule: str = "ba",
                 eta: bool = False) -> "CCGDerivation":
        """Backward application (``Y  X\\Y -> X``): the functor is the RIGHT child; its
        term is applied to the left child's term and beta-normalised. Children are kept
        in surface order ``(argument, functor)``. Raises :class:`ReductionLimitError`
        if that reduction does not terminate.
        """
        term = _apply(functor.term, argument.term, eta)
        return cls(rule=rule, category=category, term=term,
                   word=None, children=(argument, functor))

    # ---- renderers ------------------------------------------------------- #

    def to_text(self, gap: int = 3) -> str:
        """Render as a Unicode prooftree (premises above an inference bar above the
        conclusion; the combinator label sits at the right end of the bar).

        Column widths are computed with ``len`` (codepoint count), like the toolkit's
        ``tree_str`` / ``render_fitch``; double-width (CJK) or combining glyphs may
        therefore not align perfectly in a monospace terminal — use ``to_latex`` /
        ``to_html`` for such scripts.
        """
        return "\n".join(_block(self, gap)[0])

    def render(self, gap: int = 3) -> str:
        """Alias for :meth:`to_text` (mirrors ``Derivation.render`` / ``Node.tree_str``)."""
        return self.to_text(gap)

    def to_latex(self) -> str:
        """Render as a ``bussproofs`` proof tree (requires ``\\usepackage{bussproofs}``)."""
        return "\\begin{prooftree}\n" + "\n".join(_latex_lines(self)) + "\n\\end{prooftree}"

    def to_html(self, title: str = "CCG derivation") -> str:
        """Render as a self-contained, theme-aware HTML page (ccg2lambda idiom)."""
        return _html_page(self, title)


# --------------------------------------------------------------------------- #
# Semantic composition.
# --------------------------------------------------------------------------- #

def _apply(functor: Optional[Node], argument: Optional[Node], eta: bool) -> Optional[Node]:
    """Apply ``functor`` to ``argument`` and reduce; None if either term is missing."""
    if functor is None or argument is None:
        return None
    redex = Application(functor, argument)
    return beta_eta_normalize(redex) if eta else beta_reduce(redex)


# --------------------------------------------------------------------------- #
# Text prooftree renderer (block-based; premises row / bar+label / conclusion).
# --------------------------------------------------------------------------- #

def _term_text(term: Optional[Node]) -> str:
    return "" if term is None else term.to_unicode_str()


def _leaf_parts(d: "CCGDerivation") -> List[str]:
    return [p for p in (d.word, d.category, _term_text(d.term)) if p]


def _conc_parts(d: "CCGDerivation") -> List[str]:
    return [p for p in (d.category, _term_text(d.term)) if p]


def _rect(lines: List[str]) -> Tuple[List[str], int]:
    """Left-justify every line to the block's max width; return (lines, width)."""
    w = max((len(l) for l in lines), default=0)
    return [l.ljust(w) for l in lines], w


def _block(d: "CCGDerivation", gap: int) -> Tuple[List[str], int]:
    """Return (lines, bar_width) for the subtree rooted at ``d``.

    ``bar_width`` is the width of the inference bar / conclusion region (the block's
    lines may be wider than ``bar_width`` when a rule label overhangs to the right, so
    a parent centres siblings on ``bar_width`` but joins them on the padded width).
    """
    if not d.children:
        parts = _leaf_parts(d) or [""]
        w = max(len(p) for p in parts)
        return _rect([p.center(w) for p in parts])

    blocks = [_block(c, gap) for c in d.children]
    height = max(len(lines) for lines, _ in blocks)
    padded: List[Tuple[List[str], int]] = []
    for lines, _ in blocks:
        w = max(len(l) for l in lines)                       # full padded width
        lines = [l.ljust(w) for l in lines]
        lines = [" " * w] * (height - len(lines)) + lines    # align bottoms
        padded.append((lines, w))

    sep = " " * gap
    prem_lines = [sep.join(padded[i][0][r] for i in range(len(padded)))
                  for r in range(height)]
    prem_w = max(len(l) for l in prem_lines)

    conc = _conc_parts(d) or [""]
    conc_w = max(len(p) for p in conc)
    bar_w = max(prem_w, conc_w)

    out = [l.center(bar_w) for l in prem_lines]
    bar = "─" * bar_w + (" " + d.rule if d.rule else "")
    out.append(bar)
    out.extend(p.center(bar_w) for p in conc)
    return _rect(out)[0], bar_w


# --------------------------------------------------------------------------- #
# LaTeX (bussproofs) renderer.
# --------------------------------------------------------------------------- #

_INF = {1: "UnaryInfC", 2: "BinaryInfC", 3: "TrinaryInfC",
        4: "QuaternaryInfC", 5: "QuinaryInfC"}

# LaTeX-special characters in free text that must be escaped to compile.
_LATEX_ESC = {
    "&": "\\&", "%": "\\%", "$": "\\$", "#": "\\#", "_": "\\_",
    "{": "\\{", "}": "\\}", "~": "\\textasciitilde{}",
    "^": "\\textasciicircum{}", "\\": "\\textbackslash{}",
}


def _latex_text(s: str) -> str:
    """Escape every LaTeX special in a free-text token (a surface word)."""
    return "".join(_LATEX_ESC.get(c, c) for c in s)


def _cat_latex(category: Optional[str]) -> str:
    """CCG category to math-mode LaTeX: the CCG slash ``\\`` becomes ``\\backslash`` and
    ``_{…}`` subscripts are kept, but compile-breaking specials (``% & # $ ^ ~``) are
    escaped."""
    if not category:
        return ""
    out = []
    for c in category:
        if c == "\\":
            out.append("\\backslash ")
        elif c in ("&", "%", "#", "$"):
            out.append("\\" + c)
        elif c == "~":
            out.append("\\textasciitilde{}")
        elif c == "^":
            out.append("\\textasciicircum{}")
        else:                                   # keep letters, digits, / [ ] = _ { }
            out.append(c)
    return "".join(out)


def _content_latex(d: "CCGDerivation") -> str:
    """The stacked (word / category / term) content of one node, as a math array.

    The ``word`` (free text, ``\\mbox`` — base LaTeX, no amsmath needed) and the
    ``category`` are escaped here; the ``term`` is emitted via ``Node.to_latex`` and
    assumes predicate/function names are LaTeX-safe (the parser's ``[A-Z][a-zA-Z0-9]*``
    predicate names always are).
    """
    rows: List[str] = []
    if d.word:
        rows.append("\\mbox{%s}" % _latex_text(d.word))
    if d.category:
        rows.append(_cat_latex(d.category))
    if d.term is not None:
        rows.append(d.term.to_latex())
    if not rows:
        rows.append("")
    return "$\\begin{array}{c}" + " \\\\ ".join(rows) + "\\end{array}$"


def _latex_lines(d: "CCGDerivation") -> List[str]:
    """Post-order bussproofs commands for the subtree rooted at ``d``."""
    if not d.children:
        return ["  \\AxiomC{%s}" % _content_latex(d)]
    lines: List[str] = []
    for c in d.children:
        lines += _latex_lines(c)
    n = len(d.children)
    if n not in _INF:
        raise ValueError(
            "to_latex: bussproofs supports 1-5 premises per step, got %d "
            "(rule %r); split the step or use to_text/to_html." % (n, d.rule))
    if d.rule:
        lines.append("  \\RightLabel{\\scriptsize %s}" % d.rule)
    lines.append("  \\%s{%s}" % (_INF[n], _content_latex(d)))
    return lines


# --------------------------------------------------------------------------- #
# HTML renderer (self-contained, theme-aware, ccg2lambda idiom).
# --------------------------------------------------------------------------- #

def _esc_html(s: str) -> str:
    return (s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;"))


def _cat_html(category: Optional[str]) -> str:
    if not category:
        return ""
    import re
    return re.sub(r"_\{([^}]*)\}", r"<sub>\1</sub>", _esc_html(category))


def _node_html(d: "CCGDerivation") -> str:
    if not d.children:
        parts = []
        if d.word:
            parts.append('<div class="w">%s</div>' % _esc_html(d.word))
        parts.append('<div class="c">%s</div>' % _cat_html(d.category))
        parts.append('<div class="s">%s</div>' % _esc_html(_term_text(d.term)))
        return '<div class="nd leaf">%s</div>' % "".join(parts)
    prem = "".join(_node_html(c) for c in d.children)
    rule = ('<span class="r">%s</span>' % _esc_html(d.rule)) if d.rule else ""
    return ('<div class="nd"><div class="pr">%s</div>'
            '<div class="bar">%s</div>'
            '<div class="cn"><div class="c">%s</div><div class="s">%s</div></div></div>'
            % (prem, rule, _cat_html(d.category), _esc_html(_term_text(d.term))))


_HTML_CSS = """
:root{--pg:#faf9f6;--ink:#23232a;--cat:#b02a2a;--sem:#1c46b0;--rule:#3f3f47;--bar:#2b2b31;--line:#e4e1d8}
@media(prefers-color-scheme:dark){:root{--pg:#15151a;--ink:#e9e8e4;--cat:#ff7d6d;--sem:#84a6ff;--rule:#c3c3cd;--bar:#d6d5d0;--line:#2c2c34}}
:root[data-theme=light]{--pg:#faf9f6;--ink:#23232a;--cat:#b02a2a;--sem:#1c46b0;--rule:#3f3f47;--bar:#2b2b31;--line:#e4e1d8}
:root[data-theme=dark]{--pg:#15151a;--ink:#e9e8e4;--cat:#ff7d6d;--sem:#84a6ff;--rule:#c3c3cd;--bar:#d6d5d0;--line:#2c2c34}
body{margin:0;background:var(--pg);color:var(--ink);font-family:"Times New Roman",Times,serif}
.scroll{overflow-x:auto;padding:26px 8px}
.fig{width:max-content;min-width:100%;padding:0 30px;font-size:14px}
.nd{display:inline-flex;flex-direction:column;align-items:center;vertical-align:bottom}
.pr{display:flex;align-items:flex-end;justify-content:center;gap:30px}
.bar{position:relative;align-self:stretch;border-top:1.3px solid var(--bar);margin-top:3px}
.r{position:absolute;left:100%;top:50%;transform:translateY(-50%);padding-left:5px;font-size:9.5px;font-style:italic;color:var(--rule);white-space:nowrap}
.cn{padding-top:2px;text-align:center}
.leaf{padding:0 2px}
.w{font-weight:700;white-space:nowrap;padding-bottom:1px}
.c{color:var(--cat);font-style:italic;font-size:12.5px;white-space:nowrap}
.c sub{font-size:.72em}
.s{color:var(--sem);white-space:nowrap;font-size:13px}
"""


def _html_page(d: "CCGDerivation", title: str) -> str:
    return (
        "<!doctype html>\n<html><head><meta charset=\"utf-8\">\n"
        "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n"
        "<title>%s</title>\n<style>%s</style></head>\n<body>\n"
        "<div class=\"scroll\"><div class=\"fig\">%s</div></div>\n</body></html>\n"
        % (_esc_html(title), _HTML_CSS, _node_html(d)))


# --------------------------------------------------------------------------- #
# Bridge: a beta-reduction path as a derivation.
# --------------------------------------------------------------------------- #

def reduction_derivation(term: Node, *, limit: int = 1000) -> CCGDerivation:
    """Turn the beta-reduction path of ``term`` into a :class:`CCGDerivation` chain.

    The topmost premise is the original ``term``; each ``β`` step reduces it one
    contraction further, with the beta-normal form as the bottom conclusion. Render it
    with :meth:`~CCGDerivation.to_text` / ``to_latex`` / ``to_html`` like any
    derivation. Raises :class:`ReductionLimitError` past ``limit`` steps.
    """
    from .lambda_tools import reduce_trace
    trace = reduce_trace(term, limit=limit)
    node = CCGDerivation(term=trace[0])          # a bare term (no word/category)
    for step in trace[1:]:
        node = CCGDerivation.unary("β", None, node, term=step)
    return node
