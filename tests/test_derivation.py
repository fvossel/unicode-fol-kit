"""CCG-style derivation trees (unicode_fol_kit.fol.derivation).

The correctness oracle for the SEMANTICS is the toolkit's own beta-reduction: a
composed node's ``term`` must equal the beta-normal form of applying one child's term
to the other, checked by parsing the expected term and asserting AST equality. The
RENDERERS (to_text / to_latex / to_html) are checked structurally — bar characters,
combinator labels, the conclusion term on the final line, well-formed LaTeX/HTML —
following the repo's dominant renderer-test style (test_fitch.py / test_sequent.py).
"""

import shutil
import subprocess

import pytest

from unicode_fol_kit import (
    CCGDerivation, reduction_derivation, MSFLParser, Constant,
)

_FOL = MSFLParser()


# --------------------------------------------------------------------------- #
# Semantics: composition really beta-reduces (equality to the parsed target).
# --------------------------------------------------------------------------- #

def test_forward_application_reduces_to_normal_form():
    func = CCGDerivation.leaf("sleeps", "S/NP", _FOL.parse("(λx. Sleep(x))"))
    arg = CCGDerivation.leaf("John", "NP", Constant("john"))
    d = CCGDerivation.forward("S", func, arg)
    assert d.term == _FOL.parse("Sleep(john)")
    assert d.rule == "fa"
    assert d.children == (func, arg)               # functor left, argument right


def test_backward_application_functor_is_right_child():
    arg = CCGDerivation.leaf("John", "NP", Constant("john"))
    func = CCGDerivation.leaf("sleeps", r"S\NP", _FOL.parse("(λx. Sleep(x))"))
    d = CCGDerivation.backward("S", arg, func)
    assert d.term == _FOL.parse("Sleep(john)")
    assert d.rule == "ba"
    # surface order is (argument, functor) even though the functor drives the app
    assert d.children == (arg, func)


def test_forward_and_backward_apply_opposite_children():
    # Same two leaves; fa applies the LEFT term to the right, ba the RIGHT to the left.
    a = CCGDerivation.leaf("a", "X", _FOL.parse("(λx. Left(x))"))
    b = CCGDerivation.leaf("b", "X", _FOL.parse("(λx. Right(x))"))
    fa = CCGDerivation.forward("X", a, b)       # Left applied to b's term
    ba = CCGDerivation.backward("X", a, b)      # Right applied to a's term
    assert fa.term != ba.term
    assert fa.term.predicate == "Left"          # head predicate reflects the functor
    assert ba.term.predicate == "Right"


def test_full_sentence_composition():
    # "Some woman ordered tea": subject GQ is the functor over the VP.
    some = CCGDerivation.leaf("Some", "NP/N", _FOL.parse("(λG. λF. ∃x (G(x) ∧ F(x)))"))
    woman = CCGDerivation.leaf("woman", "N", _FOL.parse("(λx. Woman(x))"))
    subj = CCGDerivation.forward("NP", some, woman)
    ordered = CCGDerivation.leaf("ordered", r"(S\NP)/NP", _FOL.parse("(λo. λx. Order(x, o))"))
    tea = CCGDerivation.leaf("tea", "N", Constant("tea"))
    vp = CCGDerivation.forward(r"S\NP", ordered, tea)
    sent = CCGDerivation.forward("S", subj, vp)
    assert sent.term == _FOL.parse("∃x (Woman(x) ∧ Order(x, tea))")


def test_eta_option_collapses_eta_redex():
    # (λF. λy. F(y))(Q) beta-reduces to λy. Q(y), which eta-reduces to Q.
    func = CCGDerivation.leaf("f", "X/Y", _FOL.parse("(λF. λy. F(y))"))
    q = CCGDerivation.leaf("q", "Y", _FOL.parse("Q"))
    plain = CCGDerivation.forward("X", func, q)
    collapsed = CCGDerivation.forward("X", func, q, eta=True)
    assert collapsed.term != plain.term            # eta actually did something
    assert collapsed.term == _FOL.parse("Q")


# --------------------------------------------------------------------------- #
# Constructors.
# --------------------------------------------------------------------------- #

def test_unary_defaults_term_to_child_but_can_override():
    child = CCGDerivation.leaf("tea", "N", _FOL.parse("(λy. Tea(y))"))
    rp = CCGDerivation.unary("rp", "N", child)                     # identity step
    assert rp.term == child.term
    lifted = CCGDerivation.unary("lex", "NP", child, term=_FOL.parse("(λF. F(tea))"))
    assert lifted.term == _FOL.parse("(λF. F(tea))")


def test_leaf_fields_and_children_coerced_to_tuple():
    leaf = CCGDerivation.leaf("dog", "N", Constant("dog"))
    assert leaf.word == "dog" and leaf.category == "N" and leaf.children == ()
    combined = CCGDerivation.combine("x", "S", [leaf], Constant("dog"))   # list -> tuple
    assert isinstance(combined.children, tuple)


def test_frozen_hashable_and_value_equal():
    a = CCGDerivation.leaf("dog", "N", Constant("dog"))
    b = CCGDerivation.leaf("dog", "N", Constant("dog"))
    assert a == b and hash(a) == hash(b)           # value equality + stable hash
    assert len({a, b}) == 1                        # usable as set/dict keys


# --------------------------------------------------------------------------- #
# Text prooftree renderer.
# --------------------------------------------------------------------------- #

def _sleep():
    arg = CCGDerivation.leaf("John", "NP", Constant("john"))
    func = CCGDerivation.leaf("sleeps", r"S\NP", _FOL.parse("(λx. Sleep(x))"))
    return CCGDerivation.backward("S", arg, func)


def test_to_text_has_bar_label_and_conclusion():
    text = _sleep().to_text()
    lines = text.split("\n")
    bar_lines = [l for l in lines if "─" in l]
    assert len(bar_lines) == 1                      # one inference step
    assert bar_lines[0].rstrip().endswith("ba")     # combinator at the right of the bar
    assert "John" in text and "sleeps" in text      # words shown
    assert r"S\NP" in text                          # category shown verbatim
    assert lines[-1].strip() == "Sleep(john)"       # conclusion term is the last line


def test_to_text_reduction_chain_is_vertical():
    text = reduction_derivation(_FOL.parse("(λx. P(x))(a)")).to_text()
    lines = text.split("\n")
    assert lines[0].strip() == "(λx. P(x))(a)"      # original term on top
    assert "β" in lines[1] and "─" in lines[1]       # one beta step
    assert lines[-1].strip() == "P(a)"              # normal form at the bottom


# --------------------------------------------------------------------------- #
# LaTeX (bussproofs) renderer.
# --------------------------------------------------------------------------- #

def test_to_latex_is_bussproofs():
    tex = _sleep().to_latex()
    assert tex.startswith("\\begin{prooftree}")
    assert tex.rstrip().endswith("\\end{prooftree}")
    assert tex.count("\\AxiomC{") == 2              # two leaves
    assert "\\BinaryInfC{" in tex
    assert "\\RightLabel{\\scriptsize ba}" in tex
    assert "\\backslash" in tex                     # S\NP category escaped for math mode
    assert "Sleep(john)" in tex                     # term via Node.to_latex


def test_to_latex_uses_mbox_and_escapes_specials():
    # \mbox is base LaTeX (compiles with bussproofs alone, no amsmath); word/category
    # LaTeX-specials are escaped so the output compiles.
    tex = CCGDerivation.leaf("a&b", "S%x", Constant("john")).to_latex()
    assert "\\mbox{" in tex and "\\text{" not in tex
    assert "a\\&b" in tex                           # word: & escaped
    assert "S\\%x" in tex                           # category: % escaped
    assert "a&b" not in tex and "S%x" not in tex    # no raw specials remain


def test_to_latex_supports_up_to_five_premises_and_rejects_six():
    def combine(words):
        kids = [CCGDerivation.leaf(w, "N", Constant(w)) for w in words]
        return CCGDerivation.combine("x", "S", kids, Constant("a"))
    assert "QuaternaryInfC" in combine(("a", "b", "c", "d")).to_latex()
    assert "QuinaryInfC" in combine(("a", "b", "c", "d", "e")).to_latex()
    with pytest.raises(ValueError):
        combine(("a", "b", "c", "d", "e", "f")).to_latex()


@pytest.mark.skipif(shutil.which("pdflatex") is None,
                    reason="pdflatex not installed")
def test_to_latex_compiles_with_bussproofs_only(tmp_path):
    """The emitted LaTeX compiles under the documented preamble (bussproofs alone, no
    amsmath), including a leaf word, a category subscript, a CCG backslash, and
    LaTeX-special characters in the word and category."""
    some = CCGDerivation.leaf("Some", "NP/N", _FOL.parse("(λG. λF. ∃x (G(x) ∧ F(x)))"))
    woman = CCGDerivation.leaf("woman", "N", _FOL.parse("(λx. Woman(x))"))
    subj = CCGDerivation.forward("NP", some, woman)
    sleeps = CCGDerivation.leaf("sleeps", r"S\NP", _FOL.parse("(λx. Sleep(x))"))
    sent = CCGDerivation.backward("S", subj, sleeps)
    tricky = CCGDerivation.leaf("a&b%c", "S_{[dcl=true]}", Constant("john"))
    tex = ("\\documentclass{article}\\usepackage{bussproofs}\\pagestyle{empty}\n"
           "\\begin{document}\n" + sent.to_latex() + "\n" + tricky.to_latex() +
           "\n\\end{document}\n")
    (tmp_path / "t.tex").write_text(tex, encoding="utf-8")
    r = subprocess.run(["pdflatex", "-interaction=nonstopmode", "-halt-on-error", "t.tex"],
                       cwd=tmp_path, capture_output=True)
    assert r.returncode == 0, r.stdout.decode("utf-8", "replace")[-1500:]
    assert (tmp_path / "t.pdf").exists()


# --------------------------------------------------------------------------- #
# HTML renderer.
# --------------------------------------------------------------------------- #

def test_to_html_is_selfcontained_and_themed():
    html = _sleep().to_html()
    assert html.startswith("<!doctype html>")
    assert "<style>" in html and "</style>" in html
    assert 'class="fig"' in html
    assert "prefers-color-scheme:dark" in html      # dark theme present
    assert 'data-theme=dark' in html or 'data-theme="dark"' in html
    assert "Sleep(john)" in html and "John" in html
    # no external resource references (self-contained / CSP-safe)
    assert "http://" not in html and "https://" not in html


def test_to_html_rule_label_is_on_the_right_of_the_bar():
    # Consistent with to_text (label after the dashes) and to_latex (\RightLabel).
    css = _sleep().to_html()
    assert "left:100%" in css and "padding-left" in css
    assert "right:100%" not in css


def test_to_html_escapes_markup_in_names():
    html = CCGDerivation.leaf("a<b>", "N", Constant("dog")).to_html()
    assert "a&lt;b&gt;" in html and "a<b>" not in html
