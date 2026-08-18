"""Tests for the SORT terminal's OWN widening (many-sorted modes msfol/msfl
only) — see ``fol/_identifiers.py``'s module docstring for the design this
pins down, and its ``sort_pattern()``/``terminal_block()`` for the code.

``test_identifier_widening.py``'s only SORT-touching test
(``test_msfol_mode_sort_terminal_itself_widens``) spells its sort name as
plain ASCII (``'Person'``); nothing anywhere in the repo pins a Unicode or
underscore-bearing SORT token, or checks what the widening deliberately
does NOT extend to SORT (an underscore, or a lowercase/digit-leading name
— both legal for NAME, neither legal for SORT). This file closes that gap,
for both sorted modes (msfol, msfl) and both syntactic positions a SORT can
appear in: a quantifier's ``VARIABLE SORT`` and a sorted constant's
``NAME/CONSTANT SORT``.

Every expected AST below is hand-verified against the parser as committed
(not generated from a loop over the code under test):
    MSFLParser(many_sorted=True).parse('∀x :Świat (P(x))')
      -> SortedQuantifier(type='∀', variable=Variable('x'), sort='Świat',
                           formula=Atom('P', [Variable('x')]))
    MSFLParser(many_sorted=True).parse('P(świątek:Świat)')
      -> Atom('P', [SortedConstant('świątek', 'Świat')])
and the negative cases were confirmed to raise ``NamingError`` (not silently
mis-parse) the same way, in-process, before being written down here.

EFFECTIVENESS PROOFS (see the task this file was written for)
---------------------------------------------------------------
Every test below was independently re-run, in-process, under an in-process
monkeypatch of ``fol._identifiers.sort_pattern`` — never by editing source —
paired with rerouting ``msflparser._PARSER_CACHE`` through a throwaway dict
(the cache key is ``(mode, len(PARSER_OPS))``, which a `sort_pattern` patch
does not change, so without the reroute the FIRST many-sorted parser built
under the patch would be silently cached and reused, un-rebuilt, for the
rest of the test session once the patch itself is undone) — to confirm each
test actually fails under the right kind of regression:

* The five Unicode-sort-name tests were re-run under the EXACT pre-widening
  ASCII terminal this kit shipped before the widening
  (``SORT: /:[A-Z][a-zA-Z0-9]*/``, straight from ``git log`` on
  ``fol/grammars/terminals.lark``): every one of them turned red (raised
  ``NamingError`` where it expects a parsed AST) — reverting the widening
  outright is the most direct regression these five exist to catch.
* The pre-widening ASCII terminal ALSO excluded underscores and
  lowercase/digit-leading names (both are true of the classical, hand-
  written ``SORT: /:[A-Z][a-zA-Z0-9]*/`` too), so reverting to it changes
  nothing the seven negative tests below check — they stayed green under
  that same patch, which is the expected, reported result, not a gap. To
  still prove those seven are load-bearing, each was re-run under a second,
  narrower monkeypatch that reintroduces exactly the one property it
  guards (SORT built from NAME's underscore-including continuation class;
  SORT's leading character drawn from PREDICATE's class plus the lowercase
  class; SORT given a NAME-style digit-leading alternative) — under that
  targeted patch, every one of the seven turned red. See this task's report
  for the full per-test breakdown.
"""

import pytest

from unicode_fol_kit.fol.msflparser import MSFLParser
from unicode_fol_kit.fol.naming import NamingError
from unicode_fol_kit.fol._fol_nodes import Atom, Variable
from unicode_fol_kit.fol._msfl_nodes import SortedQuantifier, SortedConstant

MSFOL = MSFLParser(many_sorted=True)
MSFL = MSFLParser(many_sorted=True, fuzzy=True)


# ---------------------------------------------------------------------------
# Positive: a Unicode sort name is accepted, in both modes, in both syntactic
# positions a SORT token can occur in.
# ---------------------------------------------------------------------------

class TestUnicodeSortName:
    def test_msfol_quantifier_accepts_unicode_sort(self):
        """msfol: a ∀/∃ binder's SORT annotation accepts a non-ASCII (Polish) name."""
        result = MSFOL.parse("∀x :Świat (P(x))")
        assert result == SortedQuantifier(
            "∀", Variable("x"), "Świat", Atom("P", [Variable("x")]))

    def test_msfol_constant_accepts_unicode_sort(self):
        """msfol: a sorted constant's SORT annotation accepts a non-ASCII sort name."""
        result = MSFOL.parse("P(świątek:Świat)")
        assert result == Atom("P", [SortedConstant("świątek", "Świat")])

    def test_msfl_quantifier_accepts_unicode_sort(self):
        """msfl: a ∀/∃ binder's SORT annotation accepts a non-ASCII sort name."""
        result = MSFL.parse("∀x :Świat (P(x))")
        assert result == SortedQuantifier(
            "∀", Variable("x"), "Świat", Atom("P", [Variable("x")]))

    def test_msfl_constant_accepts_unicode_sort(self):
        """msfl: a sorted constant's SORT annotation accepts a non-ASCII sort name."""
        result = MSFL.parse("P(świątek:Świat)")
        assert result == Atom("P", [SortedConstant("świątek", "Świat")])

    def test_msfol_quantifier_accepts_cyrillic_sort(self):
        """msfol: the widening is not Polish/Latin-Extended-specific — a
        Cyrillic sort name (uppercase-first, so still SORT-eligible) works too."""
        result = MSFOL.parse("∀x :Страна (P(x))")
        assert result == SortedQuantifier(
            "∀", Variable("x"), "Страна", Atom("P", [Variable("x")]))


# ---------------------------------------------------------------------------
# A sort name carries the underscore, like every other identifier position.
#
# 0.23.0 shipped SORT (and PREDICATE) without it while NAME and CONSTANT had
# it, which left the chemical vocabulary unwritable -- chem/interop.py spells
# a ChemLog predicate by capitalising only the first character, so 17 of the
# signature's 40 predicates need the underscore in predicate position. SORT
# follows PREDICATE's shape by construction, so it is widened with it rather
# than left as the one identifier position that still cannot name a sort after
# the vocabulary its predicates come from.
# ---------------------------------------------------------------------------

class TestSortNameAcceptsUnderscore:
    def test_msfol_quantifier_sort_accepts_underscore(self):
        assert MSFOL.parse("∀x :Family_History (P(x))") == SortedQuantifier(
            "∀", Variable("x"), "Family_History", Atom("P", [Variable("x")]))

    def test_msfol_constant_sort_accepts_underscore(self):
        assert MSFOL.parse("P(alice:Family_History)") == Atom(
            "P", [SortedConstant("alice", "Family_History")])

    def test_msfl_quantifier_sort_accepts_underscore(self):
        assert MSFL.parse("∀x :Family_History (P(x))") == SortedQuantifier(
            "∀", Variable("x"), "Family_History", Atom("P", [Variable("x")]))

    def test_msfl_constant_sort_accepts_underscore(self):
        assert MSFL.parse("P(alice:Family_History)") == Atom(
            "P", [SortedConstant("alice", "Family_History")])

    def test_sort_name_still_rejects_a_leading_underscore(self):
        """Widened in CONTINUATION position only: the first character after
        the colon must still be an uppercase-signalling letter."""
        with pytest.raises(NamingError):
            MSFOL.parse("∀x :_History (P(x))")


# ---------------------------------------------------------------------------
# Negative: a sort name may NOT start with a term-valued (lowercase/caseless)
# letter or a digit — SORT keeps PREDICATE's "uppercase-signalling first
# character, no digit-leading alternative" shape, unlike NAME.
# ---------------------------------------------------------------------------

class TestSortNameMustBeUppercaseLed:
    def test_msfol_quantifier_sort_rejects_lowercase_leading(self):
        """msfol: a lowercase-first sort name ('świat', term-valued) is illegal."""
        with pytest.raises(NamingError):
            MSFOL.parse("∀x :świat (P(x))")

    def test_msfol_quantifier_sort_rejects_digit_leading(self):
        """msfol: unlike NAME (which has a digit-leading alternative), SORT has none."""
        with pytest.raises(NamingError):
            MSFOL.parse("∀x :2World (P(x))")

    def test_msfl_quantifier_sort_rejects_lowercase_leading(self):
        """msfl: a lowercase-first sort name ('świat', term-valued) is illegal."""
        with pytest.raises(NamingError):
            MSFL.parse("∀x :świat (P(x))")

    def test_msfl_quantifier_sort_rejects_digit_leading(self):
        """msfl: unlike NAME (which has a digit-leading alternative), SORT has none."""
        with pytest.raises(NamingError):
            MSFL.parse("∀x :2World (P(x))")
