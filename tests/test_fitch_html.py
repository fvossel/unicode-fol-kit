"""HTML rendering for Fitch proofs (``unicode_fol_kit.atp.fitch.Proof.to_html``).

``Proof.to_html`` is a straight sink of the already-computed, already-trusted
:func:`~unicode_fol_kit.atp.fitch._visual_rows` rows — the exact rows
:func:`~unicode_fol_kit.atp.fitch.render_fitch` itself consumes (hand-checked
in ``test_fitch.py``'s Fitch-notation examples, which match this module's
worked example in ``docs/guide/classical-reasoning.md``). So the oracle here
is DIFFERENTIAL against that trusted text renderer: every formula/
justification substring it prints must also appear, HTML-escaped, in the HTML
output; and the nesting depth of the Fitch scope bars in the markup must match
``_visual_rows``' own ``depth`` field — an independent cross-check between the
two renderers that consume the same rows, not a derivation of the expectation
from the renderer under test. Well-formedness (balanced tags, self-contained,
theme-aware) and escaping of hostile predicate names are checked directly.

A final test guards a design decision this item made: the CCGDerivation HTML
renderer in ``fol/derivation.py`` was deliberately left untouched (see the
module docstring of ``atp/_html.py``) rather than made to share code with the
new Fitch/Sequent HTML renderers, precisely so its output could not change; a
captured-before-the-fact golden string pins that.
"""

import html.parser

from unicode_fol_kit.fol.derivation import CCGDerivation
from unicode_fol_kit.fol.nodes import Atom, Implies, Constant
from unicode_fol_kit.atp.fitch import (
    Proof, Subproof, premise, assume, line,
    check_proof, render_fitch, _visual_rows,
)

P = Atom("P", [])
Q = Atom("Q", [])
R = Atom("R", [])


def _esc(s: str) -> str:
    """The same escaping ``to_html`` applies (mirrors ``atp._html.esc_html``)."""
    return s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


def _hs_proof() -> Proof:
    """P→Q, Q→R ⊢ P→R (hypothetical syllogism via nested →I).

    The exact proof worked out by hand in ``docs/guide/classical-reasoning.md``'s
    "Natural deduction" section (and pinned there against ``render_fitch``'s
    ASCII output), reused here as the HTML fixture.
    """
    return Proof(
        premises=[premise(1, Implies(P, Q)), premise(2, Implies(Q, R))],
        steps=[
            Subproof(assumption=assume(3, P),
                     body=[line(4, Q, "→E", 1, 3), line(5, R, "→E", 2, 4)]),
            line(6, Implies(P, R), "→I", (3, 5)),
        ],
    )


def _nested_proof() -> Proof:
    """P ⊢ Q→(R→Q) (a two-deep nested subproof: an assume box inside an assume
    box), the K-axiom pattern. ``check_proof`` below hand-verifies it is sound;
    it exists to give the depth/nesting tests a fixture reaching depth 2."""
    proof = Proof(
        premises=[premise(1, P)],
        steps=[
            Subproof(assumption=assume(2, Q), body=[
                Subproof(assumption=assume(3, R), body=[
                    line(4, Q, "Reit", 2),
                ]),
                line(5, Implies(R, Q), "→I", (3, 4)),
            ]),
            line(6, Implies(Q, Implies(R, Q)), "→I", (2, 5)),
        ],
    )
    assert check_proof(proof)  # sanity: the fixture is a genuine, sound proof
    return proof


# ---------------------------------------------------------------------------
# Well-formedness helper: every non-void start tag is matched by an end tag,
# correctly nested (an explicit stack, independent of the renderer's own logic).
# ---------------------------------------------------------------------------

class _TagBalanceChecker(html.parser.HTMLParser):
    _VOID = {"meta", "br", "hr", "img", "input", "link"}

    def __init__(self):
        super().__init__()
        self.stack = []

    def handle_starttag(self, tag, attrs):
        if tag not in self._VOID:
            self.stack.append(tag)

    def handle_endtag(self, tag):
        assert self.stack and self.stack[-1] == tag, (
            f"unbalanced </{tag}>; open stack was {self.stack}")
        self.stack.pop()


def _assert_balanced(html_text: str):
    parser = _TagBalanceChecker()
    parser.feed(html_text)
    parser.close()
    assert parser.stack == [], f"unclosed tags at end of document: {parser.stack}"


# ---------------------------------------------------------------------------
# Row-depth counter: for each top-level ".ln"/".ln bar" row div, count its
# ".bx" scope-bar cells — independent of _html_fitch's own loop bookkeeping.
# ---------------------------------------------------------------------------

class _RowBxCounter(html.parser.HTMLParser):
    def __init__(self):
        super().__init__()
        self.rows = []          # [(is_bar_row, bx_count), ...] in document order
        self._depth = None      # div-nesting depth within the current row, or None
        self._cur_bx = 0
        self._cur_is_bar = False

    def handle_starttag(self, tag, attrs):
        if tag != "div":
            return
        cls = dict(attrs).get("class", "")
        if self._depth is None:
            classes = cls.split()
            if classes and classes[0] == "ln":
                self._depth = 1
                self._cur_bx = 0
                self._cur_is_bar = "bar" in classes
            return
        self._depth += 1
        if cls == "bx":
            self._cur_bx += 1

    def handle_endtag(self, tag):
        if tag != "div" or self._depth is None:
            return
        self._depth -= 1
        if self._depth == 0:
            self.rows.append((self._cur_is_bar, self._cur_bx))
            self._depth = None


def _row_bx_counts(html_text: str):
    counter = _RowBxCounter()
    counter.feed(html_text)
    counter.close()
    return counter.rows


# ---------------------------------------------------------------------------
# Well-formedness / theming
# ---------------------------------------------------------------------------

def test_to_html_is_selfcontained_and_themed():
    html_text = _hs_proof().to_html()
    assert html_text.startswith("<!doctype html>")
    assert "<style>" in html_text and "</style>" in html_text
    assert "prefers-color-scheme:dark" in html_text      # dark theme present
    assert "data-theme=dark" in html_text
    assert "http://" not in html_text and "https://" not in html_text
    _assert_balanced(html_text)


def test_to_html_default_and_custom_title():
    assert "<title>Fitch proof</title>" in _hs_proof().to_html()
    assert "<title>My proof</title>" in _hs_proof().to_html(title="My proof")


# ---------------------------------------------------------------------------
# Content fidelity — differential against render_fitch's trusted text output
# ---------------------------------------------------------------------------

def test_to_html_contains_every_formula_and_justification_render_fitch_prints():
    proof = _hs_proof()
    html_text = proof.to_html()
    saw_a_line = False
    for row in _visual_rows(proof):
        if row["kind"] != "line":
            continue
        saw_a_line = True
        assert _esc(row["formula"].to_unicode_str()) in html_text
        assert _esc(row["just"]) in html_text
    assert saw_a_line


def test_to_html_row_count_matches_render_fitch_line_count():
    proof = _nested_proof()
    text_lines = render_fitch(proof).splitlines()
    html_text = proof.to_html()
    # render_fitch emits exactly one output line per _visual_rows row (a "line"
    # row or a "├──────" bar row); to_html emits exactly one ".ln"/".ln bar"
    # div per row — an independent count cross-check between the two renderers.
    assert len(_row_bx_counts(html_text)) == len(text_lines) == len(_visual_rows(proof))


# ---------------------------------------------------------------------------
# Escaping
# ---------------------------------------------------------------------------

def test_to_html_escapes_markup_in_predicate_names():
    weird = Atom("A<b>&c", [])
    proof = Proof(premises=[premise(1, weird)], steps=[line(2, weird, "Reit", 1)])
    html_text = proof.to_html()
    assert "A&lt;b&gt;&amp;c" in html_text
    assert "A<b>&c" not in html_text
    _assert_balanced(html_text)


# ---------------------------------------------------------------------------
# Structural: scope-bar nesting depth in the HTML matches _visual_rows' depth
# ---------------------------------------------------------------------------

def test_to_html_bar_nesting_matches_visual_rows_depth():
    proof = _nested_proof()          # reaches nesting depth 2
    expected = []
    for r in _visual_rows(proof):
        if r["kind"] == "line":
            expected.append((False, r["depth"] + 1))
        else:
            expected.append((True, r["depth"]))
    assert any(d >= 2 for is_bar, d in expected if not is_bar), (
        "fixture does not actually reach nesting depth 2")
    assert _row_bx_counts(proof.to_html()) == expected


def test_to_html_flat_proof_has_single_scope_bar_throughout():
    """A proof with no subproofs at all: every line/bar row is at depth 0, so
    every row draws exactly one ``.bx`` (the outermost, never-closed box)."""
    proof = Proof(premises=[premise(1, P), premise(2, Implies(P, Q))],
                  steps=[line(3, Q, "→E", 2, 1)])
    assert check_proof(proof)
    counts = _row_bx_counts(proof.to_html())
    assert counts == [(False, 1), (False, 1), (True, 0), (False, 1)]


# ---------------------------------------------------------------------------
# Regression guard: CCGDerivation.to_html() (fol/derivation.py) is untouched.
#
# This item's spec allowed sharing HTML helpers between fol/derivation.py and
# the new atp renderers, but atp already depends on fol at module scope (e.g.
# this very module imports unicode_fol_kit.fol.nodes), while fol/__init__.py
# eagerly imports .derivation — so a fol/derivation.py that reached back into
# atp at module scope would risk a real import cycle. The design chosen here
# (see unicode_fol_kit/atp/_html.py's module docstring) keeps atp -> fol
# one-way and leaves fol/derivation.py's HTML renderer untouched; this test
# pins that with a byte-for-byte comparison against output captured from the
# unmodified module.
# ---------------------------------------------------------------------------

_CCG_LEAF_HTML_BASELINE = """<!doctype html>
<html><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>CCG derivation</title>
<style>
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
</style></head>
<body>
<div class="scroll"><div class="fig"><div class="nd leaf"><div class="w">John</div><div class="c">NP</div><div class="s">john</div></div></div></div>
</body></html>
"""


def test_ccg_derivation_to_html_is_byte_identical_to_the_captured_baseline():
    d = CCGDerivation.leaf("John", "NP", Constant("john"))
    assert d.to_html() == _CCG_LEAF_HTML_BASELINE
