"""Tests for notebook rich-display hooks (C60): ``Node._repr_latex_``,
``TruthTable._repr_html_``, ``Structure._repr_html_``, and
``FiniteStructure._repr_html_``.

None of these hooks add a new dependency (no IPython import anywhere) and none
are exercised through IPython's formatter registry — every test below calls
the dunder method directly, exactly as IPython itself would.

Two properties are checked for every hook:

1. **Differential correctness** against the existing, already-tested renderer
   it delegates to or reuses (``to_latex()``, ``render()``'s row data, or
   ``to_dict()``/``__repr__``) — never a tautological comparison against the
   hook's own output.
2. **Never raises.** ``_repr_latex_`` falls back to ``None`` on an unsupported
   node instead of propagating ``to_latex()``'s refusal, and every
   ``_repr_html_`` never evaluates a computed/callable predicate. HTML output
   also escapes user-chosen symbol names, since the parser's identifier
   grammar forbids ``<``/``>``/``&`` in a predicate/constant name but a
   hand-built AST or structure has no such restriction.
"""

import html as html_module
import re
from dataclasses import dataclass

import pytest

from unicode_fol_kit.fol.msflparser import MSFLParser
from unicode_fol_kit.fol.nodes import Node, Atom
from unicode_fol_kit.semantics.truthtable import truth_table
from unicode_fol_kit.semantics.tarski import Structure
from unicode_fol_kit.semantics.structures import FiniteStructure

FOL = MSFLParser()
parse = FOL.parse


# --------------------------------------------------------------------------- #
# Node._repr_latex_
# --------------------------------------------------------------------------- #

class TestNodeReprLatex:

    def test_hand_checked_value(self):
        """One fully hand-worked example: ∀ → \\forall, → → \\rightarrow, names
        verbatim, wrapped in display-math ``$$...$$``."""
        node = parse("∀x (Human(x) → Mortal(x))")
        assert node._repr_latex_() == r"$$\forall x\, (Human(x) \rightarrow Mortal(x))$$"

    @pytest.mark.parametrize("formula", [
        "∀x (Human(x) → Mortal(x))",
        "(P ∧ Q) ∨ ¬R",
        "∃x ∃y (Loves(x, y) ↔ ¬Loves(y, x))",
        "∀x (P(x) → Q(x)) ∧ ∃y R(y)",
        "∀x (P(x) ⊕ Q(x))",
    ])
    def test_matches_to_latex_exactly(self, formula):
        """Differential against the existing, separately-tested to_latex():
        the hook is exactly to_latex()'s output wrapped in ``$$...$$``, byte
        for byte — this checks the WRAPPING, not to_latex() itself.
        """
        node = parse(formula)
        rendered = node._repr_latex_()
        assert rendered is not None
        assert rendered.startswith("$$") and rendered.endswith("$$")
        assert rendered[2:-2] == node.to_latex()

    def test_never_raises_on_unsupported_node_falls_back_to_none(self):
        """A node type the LaTeX dispatcher has never heard of makes
        to_latex() raise (refuse loudly) — but _repr_latex_ must swallow that
        and return None so IPython falls back to the plain repr instead of a
        traceback in the notebook cell.
        """
        @dataclass(frozen=True)
        class _UnsupportedNode(Node):
            """A bare Node subclass registered nowhere in the LaTeX dispatch."""

        node = _UnsupportedNode()
        with pytest.raises(TypeError):
            node.to_latex()          # confirms this really is the raising case
        assert node._repr_latex_() is None

    def test_does_not_mutate_unicode_repr(self):
        """The hook is purely additive: to_unicode_str()/__repr__ are untouched."""
        node = parse("P ∧ Q")
        before = node.to_unicode_str()
        node._repr_latex_()
        assert node.to_unicode_str() == before


# --------------------------------------------------------------------------- #
# TruthTable._repr_html_
# --------------------------------------------------------------------------- #

def _parse_markdown_rows(markdown: str):
    """Extract the body rows of render()'s Markdown table as lists of cell strings."""
    lines = markdown.splitlines()
    body = lines[2:]                     # skip header row + '---' separator row
    return [[cell.strip() for cell in line.strip("|").split("|")] for line in body]


def _parse_html_rows(html: str):
    """Extract the <tbody> rows of _repr_html_'s table as lists of cell strings."""
    tbody = re.search(r"<tbody>(.*)</tbody>", html, re.S).group(1)
    return [re.findall(r"<td>(.*?)</td>", tr)
            for tr in re.findall(r"<tr>(.*?)</tr>", tbody)]


class TestTruthTableReprHtml:

    def test_classical_conjunction_hand_checked(self):
        """Textbook classical truth table for P ∧ Q: 4 rows, standard T/F pattern."""
        tt = truth_table(parse("P ∧ Q"))
        rows = _parse_html_rows(tt._repr_html_())
        # Hand-derived (standard truth table for conjunction):
        assert rows == [
            ["T", "T", "T"],
            ["T", "F", "F"],
            ["F", "T", "F"],
            ["F", "F", "F"],
        ]

    def test_k3_excluded_middle_half_row_not_designated(self):
        """K3's P ∨ ¬P: when P is undefined (½), the disjunction is also ½,
        which K3 does NOT designate (only {1} is designated) — so the row
        exists in the table but the formula is not a K3 tautology.
        """
        tt = truth_table(parse("P ∨ ¬P"), logic="K3")
        assert tt.is_tautology is False
        # Hand-derived (strong-Kleene max for ∨, involutive ¬):
        # P=1 -> ¬P=0 -> 1∨0=1 (designated); P=½ -> ¬P=½ -> ½∨½=½ (NOT designated);
        # P=0 -> ¬P=1 -> 0∨1=1 (designated).
        assert [designated for _, _, designated in tt.rows] == [True, False, True]
        rows = _parse_html_rows(tt._repr_html_())
        # Each row is [atom-column glyph, formula-column glyph]; the atom
        # column shows P's own assigned value (1, ½, 0 in that order — the
        # value set's iteration order), the formula column P ∨ ¬P's value.
        assert rows == [["1", "1"], ["½", "½"], ["0", "1"]]

    @pytest.mark.parametrize("formula, logic", [
        ("P ∧ Q", "classical"),
        ("(P → Q) ∧ (Q → P)", "classical"),
        ("P ∨ ¬P", "K3"),
        ("P ∧ ¬P", "LP"),
    ])
    def test_html_rows_match_markdown_rows(self, formula, logic):
        """Differential: the HTML table and render()'s Markdown table are two
        independently-written loops over the same self.rows/self.atoms data
        (via the shared _rows_and_glyphs header/glyph selection) — they must
        produce identical cell content, row for row.
        """
        tt = truth_table(parse(formula), logic=logic)
        md_rows = _parse_markdown_rows(tt.render())
        html_rows = _parse_html_rows(tt._repr_html_())
        assert html_rows == md_rows
        assert len(html_rows) == len(tt.rows)

    def test_html_escapes_user_predicate_names(self):
        """A predicate name containing HTML-special characters must not
        produce markup. The parser's identifier grammar forbids these
        characters, so the Atom is built directly rather than parsed.
        """
        atom = Atom(predicate="P<script>&Q", args=())
        tt = truth_table(atom)
        html = tt._repr_html_()
        assert "<script>" not in html
        assert "P&lt;script&gt;&amp;Q" in html

    def test_repr_html_never_raises_and_str_untouched(self):
        """Purely additive: __str__ (== render()) is unchanged by the new hook."""
        tt = truth_table(parse("P ∧ Q"))
        before = str(tt)
        tt._repr_html_()
        assert str(tt) == before


# --------------------------------------------------------------------------- #
# Structure._repr_html_
# --------------------------------------------------------------------------- #

class TestStructureReprHtml:

    def test_tiny_structure_hand_built(self):
        """domain={a,b}, R/2={(a,b)}: the HTML must show the domain elements
        and the predicate's name/arity (never its extension, matching
        __repr__'s own conservative choice not to dump it).
        """
        s = Structure(
            domain=["a", "b"],
            constants={"c": "a"},
            predicates={("R", 2): {("a", "b")}},
        )
        html = s._repr_html_()
        # domain individuals are rendered via repr() then HTML-escaped (an
        # arbitrary Python value, not necessarily a bare string); use the
        # stdlib html.escape independently here rather than reusing the
        # method's own internal helper.
        assert html_module.escape(repr("a")) in html
        assert html_module.escape(repr("b")) in html
        assert "R/2" in html
        assert "c" in html

    def test_matches_repr_key_sets(self):
        """Differential: the set of function/predicate keys shown in HTML must
        be exactly the set __repr__ already reports (an existing, tested
        display method) — same underlying self.functions/self.predicates.
        """
        s = Structure(
            domain=["a", "b", "c"],
            functions={("f", 1): lambda x: x},
            predicates={("R", 2): {("a", "b")}, ("Q", 1): {("a",)}},
        )
        html = s._repr_html_()
        repr_str = repr(s)
        for name, arity in list(s.functions) + list(s.predicates):
            key = f"{name}/{arity}"
            assert key in html
            assert f"('{name}', {arity})" in repr_str

    def test_never_evaluates_a_callable_function(self):
        """A function interpreted by a callable must never be invoked while
        building the HTML — only its (name, arity) key is shown, exactly
        like __repr__.
        """
        def _boom(*args):
            raise AssertionError("Structure._repr_html_ must not call function values")

        s = Structure(domain=["a", "b"], functions={("f", 1): _boom})
        html = s._repr_html_()          # must not raise
        assert "f/1" in html

    def test_html_escapes_special_characters(self):
        """Domain individuals, constant names, and predicate names may be
        arbitrary user-supplied strings (Structure places no restriction on
        them, unlike the parser's identifier grammar) — HTML-special
        characters in any of them must not produce markup.
        """
        s = Structure(
            domain=["a<b>"],
            constants={"c<d>": "a<b>"},
            predicates={("R&S", 1): {("a<b>",)}},
        )
        html = s._repr_html_()
        assert "a<b>" not in html
        assert "c<d>" not in html
        assert "R&S" not in html
        assert "a&lt;b&gt;" in html
        assert "c&lt;d&gt;" in html
        assert "R&amp;S/1" in html


# --------------------------------------------------------------------------- #
# FiniteStructure._repr_html_
# --------------------------------------------------------------------------- #

class TestFiniteStructureReprHtml:

    def test_tiny_structure_hand_built(self):
        """domain={a,b}, R/2={(a,b)}: the HTML must show the domain elements,
        the predicate name/arity, and the exact tuple.
        """
        fs = FiniteStructure(
            domain=("a", "b"),
            extensions={("R", 2): [("a", "b")]},
            constants={"c": "a"},
        )
        html = fs._repr_html_()
        assert "a" in html and "b" in html
        assert "R/2" in html
        assert "<td>a</td><td>b</td>" in html    # the exact tuple, in order

    def test_matches_to_dict_exactly(self):
        """Differential against to_dict(): every domain individual, every
        extension tuple's every element, every constant name/value, and every
        computed-predicate name appearing in to_dict() must appear in the
        HTML too.
        """
        fs = FiniteStructure(
            domain=("a", "b", "c"),
            extensions={("R", 2): [("a", "b"), ("b", "c")], ("P", 1): [("a",)]},
            computed={("Q", 1): lambda x: True},
            constants={"k": "c"},
        )
        data = fs.to_dict()
        html = fs._repr_html_()
        for individual in data["domain"]:
            assert individual in html
        for key, tuples in data["extensions"].items():
            assert key in html
            for row in tuples:
                for individual in row:
                    assert individual in html
        for name, value in data["constants"].items():
            assert name in html and value in html
        for computed_key in data["computed"]:
            assert computed_key in html

    def test_never_evaluates_a_computed_predicate(self):
        """A computed predicate's callable must never be invoked while
        building the HTML — to_dict() already made this choice (listing
        computed predicates by NAME only) and _repr_html_ reuses it.
        """
        def _boom(*args):
            raise AssertionError("FiniteStructure._repr_html_ must not call computed predicates")

        fs = FiniteStructure(domain=("a", "b"), computed={("secret", 1): _boom})
        html = fs._repr_html_()         # must not raise
        assert "secret/1" in html

    def test_html_escapes_special_characters(self):
        """Individual names are ordinary strings (Individual = str, no parser
        restriction) — HTML-special characters must not produce markup.
        """
        fs = FiniteStructure(
            domain=("a<b>",),
            extensions={("R&S", 1): [("a<b>",)]},
            constants={"c<d>": "a<b>"},
        )
        html = fs._repr_html_()
        assert "a<b>" not in html
        assert "c<d>" not in html
        assert "R&S" not in html
        assert "a&lt;b&gt;" in html
        assert "c&lt;d&gt;" in html
        assert "R&amp;S/1" in html

    def test_never_raises_and_repr_untouched(self):
        """Purely additive: __repr__ is unchanged by the new hook."""
        fs = FiniteStructure(domain=("a", "b"), extensions={("R", 2): [("a", "b")]})
        before = repr(fs)
        fs._repr_html_()
        assert repr(fs) == before

    def test_zero_ary_predicate_true_and_false_render_differently(self):
        """A 0-ary predicate's extension is {()} (true) or {} (false) — see
        the module docstring. Both must be visibly distinguishable in the
        HTML, not just two empty-looking tables under the same caption.
        """
        true_fs = FiniteStructure(domain=("a",), extensions={("P", 0): [()]})
        false_fs = FiniteStructure(domain=("a",), extensions={("P", 0): []})
        true_html = true_fs._repr_html_()
        false_html = false_fs._repr_html_()
        assert "P/0" in true_html and "P/0" in false_html
        assert "True" in true_html and "False" not in true_html
        assert "False" in false_html and "True" not in false_html
        assert true_html != false_html
