"""Tests for :func:`unicode_fol_kit.chem.interop.rename_with_spans` /
:func:`unicode_fol_kit.chem.interop.to_chemlog_names_with_spans`.

No RDKit needed here (unlike most of ``tests/test_chem.py``) — this module
only rewrites already-parsed :class:`~unicode_fol_kit.fol.nodes.Node` trees
and a :class:`~unicode_fol_kit.fol.spans.SpanMap` alongside them, no molecule
structure involved.

Two layers of test, deliberately kept separate:

* ``TestRenameWithSpansUnit`` builds a tiny AST BY HAND with a
  hand-constructed (and, in one case, deliberately PARTIAL) ``SpanMap`` —
  keyed by PATH, the kit's path convention (see ``fol.spans``'s module
  docstring) — to pin down ``rename_with_spans``'s own contract — re-key
  every span onto its renamed counterpart, invent nothing for a path the
  input table did not cover — independent of
  ``MSFLParser.parse_with_spans``'s own behaviour.
* ``TestRenameWithSpansIntegration`` goes through the real
  ``MSFLParser.parse_with_spans`` -> ``to_chemlog_names_with_spans`` pipeline
  chem_tools.py actually uses, and checks the resulting spans by SLICING THE
  ORIGINAL SOURCE TEXT — the property a caller actually cares about.

Both layers use ``SpanMap.for_node(node)`` (identity-based, against the tree
the map is currently bound to) rather than ``.get(path)`` — that convenience
lookup is what ``rename_with_spans``'s callers (this test file included)
actually reach for when they already hold a node object.
"""

from unicode_fol_kit.fol.msflparser import MSFLParser
from unicode_fol_kit.fol.nodes import And, Atom, Variable
from unicode_fol_kit.fol.spans import Span, SpanMap, NodeSpans, UNKNOWN
from unicode_fol_kit.chem.interop import rename_with_spans, to_chemlog_names_with_spans


def _span(start: int, end: int, text: str) -> Span:
    """A :class:`Span` with made-up line/column bookkeeping — none of the
    tests below inspect those fields, only start/end/text, so a fixed
    placeholder keeps the fixtures short."""
    return Span(start, end, 1, start + 1, 1, end + 1, text)


def _extent(span) -> NodeSpans:
    """A :class:`NodeSpans` carrying only an EXTENT — head is irrelevant to
    every test in this file, so it is left UNKNOWN throughout."""
    return NodeSpans(span, UNKNOWN)


# ---------------------------------------------------------------------------
# Unit: rename_with_spans's own contract, against a hand-built AST/SpanMap
# ---------------------------------------------------------------------------

class TestRenameWithSpansUnit:
    def test_renamed_leaf_keeps_its_span(self):
        """``C(x)``, mapped ``C -> c``: the renamed Atom is a NEW object
        (rename always reconstructs — see interop._rename), but must carry
        forward the EXACT span the pre-rename Atom had. Paths: the atom
        itself is ``()``, its sole argument ``x`` is ``(0,)``."""
        x = Variable("x")
        atom = Atom("C", [x])
        spans = SpanMap({
            (): _extent(_span(0, 4, "C(x)")),
            (0,): _extent(_span(2, 3, "x")),
        })

        renamed, new_spans = rename_with_spans(atom, {"C": "c"}, spans)

        assert renamed == Atom("c", [Variable("x")])
        assert renamed is not atom  # rename always reconstructs
        assert new_spans.for_node(renamed).extent == _span(0, 4, "C(x)")
        assert new_spans.for_node(renamed.args[0]).extent == _span(2, 3, "x")

    def test_unrenamed_symbol_still_gets_a_new_object_and_keeps_its_span(self):
        """A predicate NOT in ``mapping`` (an auxiliary/class predicate) is
        left spelled as-is, but it is still a freshly reconstructed object
        (``_rename`` walks unconditionally) — the span must follow it too,
        not just the symbols that were actually renamed."""
        atom = Atom("OrganicMolecularEntity", [Variable("x")])
        spans = SpanMap({(): _extent(_span(0, 24, "OrganicMolecularEntity(x)"))})

        renamed, new_spans = rename_with_spans(atom, {"C": "c"}, spans)

        assert renamed == atom
        assert renamed is not atom
        assert new_spans.for_node(renamed).extent == _span(0, 24, "OrganicMolecularEntity(x)")

    def test_ancestor_two_levels_above_a_renamed_leaf_keeps_its_span(self):
        """``C(x) & N(x)``: the top ``And`` is not itself renamed (only
        Atom predicates are), but ``map_children`` reconstructs it anyway
        (see interop._rename / Node.map_children) — its span must survive
        that reconstruction just like the leaves' do. Paths: the ``And`` is
        ``()``, ``left`` is ``(0,)``, ``right`` is ``(1,)``."""
        x = Variable("x")
        left, right = Atom("C", [x]), Atom("N", [x])
        top = And(left, right)
        spans = SpanMap({
            (): _extent(_span(0, 14, "C(x) & N(x)")),
            (0,): _extent(_span(0, 4, "C(x)")),
            (1,): _extent(_span(7, 11, "N(x)")),
        })

        renamed, new_spans = rename_with_spans(top, {"C": "c", "N": "n"}, spans)

        assert renamed == And(Atom("c", [Variable("x")]), Atom("n", [Variable("x")]))
        assert new_spans.for_node(renamed).extent == _span(0, 14, "C(x) & N(x)")
        assert new_spans.for_node(renamed.left).extent == _span(0, 4, "C(x)")
        assert new_spans.for_node(renamed.right).extent == _span(7, 11, "N(x)")

    def test_node_absent_from_the_input_table_stays_unknown_not_invented(self):
        """A partial input ``SpanMap`` (no entry for the top ``And`` at path
        ``()``, nor for either occurrence of ``x`` at ``(0, 0)``/``(1, 0)`` —
        the SAME ``Variable`` object reused as both atoms' argument, so this
        also pins down that the table is keyed by OCCURRENCE/path, not by
        the shared object's identity) must not gain a span from nowhere:
        ``project_spans`` records only what ``old_spans`` actually had, path
        by path, independent of its neighbours."""
        x = Variable("x")
        left, right = Atom("C", [x]), Atom("N", [x])
        top = And(left, right)
        spans = SpanMap({
            (0,): _extent(_span(0, 4, "C(x)")),
            (1,): _extent(_span(7, 11, "N(x)")),
        })

        renamed, new_spans = rename_with_spans(top, {"C": "c", "N": "n"}, spans)

        assert new_spans.for_node(renamed).extent is UNKNOWN
        assert new_spans.for_node(renamed.left.args[0]).extent is UNKNOWN  # the renamed `x`
        assert new_spans.for_node(renamed.left).extent == _span(0, 4, "C(x)")
        assert new_spans.for_node(renamed.right).extent == _span(7, 11, "N(x)")

    def test_empty_input_table_yields_an_all_unknown_result_not_a_crash(self):
        atom = Atom("C", [Variable("x")])
        renamed, new_spans = rename_with_spans(atom, {"C": "c"}, SpanMap({}))
        assert renamed == Atom("c", [Variable("x")])
        assert new_spans.for_node(renamed).extent is UNKNOWN
        assert len(new_spans) == 0


# ---------------------------------------------------------------------------
# Integration: the real MSFLParser.parse_with_spans -> to_chemlog_names_with_spans
# pipeline chem_tools.py actually drives, checked by slicing SOURCE TEXT.
# ---------------------------------------------------------------------------

class TestRenameWithSpansIntegration:
    def test_renamed_atom_span_slices_the_original_kit_spelled_text(self):
        """``C(x)`` (kit spelling) renames to ``c(x)`` (ChemLog spelling);
        the reported span must still point at the ORIGINAL text's ``C(x)``
        substring — the span describes what the CALLER wrote, not what the
        renamed AST would render back to."""
        text = "∃x C(x)"
        spanned = MSFLParser().parse_with_spans(text)
        node, spans = to_chemlog_names_with_spans(spanned.formula, spanned.spans)

        assert node.to_unicode_str() == "∃x c(x)"
        # node is ∃x (c(x)) -- descend to the renamed Atom.
        atom = node.formula
        assert atom.predicate == "c"
        span = spans.for_node(atom).extent
        assert span is not UNKNOWN
        assert text[span.start:span.end] == "C(x)"

    def test_every_node_keeps_its_span_across_a_multi_atom_rename(self):
        """A conjunction of two renamed atoms plus one untouched (auxiliary,
        outside the chemical vocabulary) predicate: every one of the three
        top-level conjuncts must resolve, via its span, back to its own
        exact substring of the original text — proving the propagation
        survives more than one renamed symbol and a mix of renamed/
        unrenamed predicates in the SAME formula."""
        text = "C(x) ∧ N(x) ∧ SomeAuxPredicate(x)"
        spanned = MSFLParser().parse_with_spans(text)
        node, spans = to_chemlog_names_with_spans(spanned.formula, spanned.spans)

        # node is And(And(c(x), n(x)), SomeAuxPredicate(x)) -- left-folded.
        aux = node.right
        middle = node.left.right
        first = node.left.left
        assert (first.predicate, middle.predicate, aux.predicate) == (
            "c", "n", "SomeAuxPredicate")

        for atom, expected in ((first, "C(x)"), (middle, "N(x)"),
                               (aux, "SomeAuxPredicate(x)")):
            span = spans.for_node(atom).extent
            assert span is not UNKNOWN, f"no span recovered for {atom!r}"
            assert text[span.start:span.end] == expected

    def test_whole_formula_span_still_covers_the_full_text(self):
        """The top-level node's own span (the ``And`` chain's root) must
        still span the ENTIRE input, unaffected by the two renames nested
        inside it — the ancestor-keeps-its-span property, exercised through
        the real parser rather than a hand-built AST."""
        text = "C(x) ∧ N(x)"
        spanned = MSFLParser().parse_with_spans(text)
        node, spans = to_chemlog_names_with_spans(spanned.formula, spanned.spans)

        span = spans.for_node(node).extent
        assert span is not UNKNOWN
        assert text[span.start:span.end] == text
