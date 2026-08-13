"""Tests for :mod:`unicode_fol_kit.fol.tptp_repair` — the TPTP syntax-repair
layer for the three ChEBI2FOL (NeSy 2026, Appendix B.1) failure classes.

Every expected string/AST below is hand-derived (never copy-pasted from a
program run) from the TPTP grammar in ``tptp_input.py`` and reasoned about in
each test's docstring or an inline comment:

* **Case 1** (biimplication structure error): the grammar's own operator
  ladder is ``equiv > imp > disj > conj > unary`` (``<=>`` loosest, ``&``
  tightest), so ``predicate(x) <=> condition1 & condition2`` parses as
  ``equiv`` over two ``imp``s, the right one built by ``conj: conj "&"
  unary`` — i.e. ``Iff(Atom(Predicate,[x]), And(Atom(Condition1,[]),
  Atom(Condition2,[])))`` — with or without the redundant parentheses gavel
  wants. ``to_tptp``-style rendering (which the repair's canonical renderer
  matches) always fully brackets, so the repaired text is
  ``"(predicate(x) <=> (condition1 & condition2))"``.
* **Case 2** (invalid predicate name): TPTP's unquoted functor rule
  (``lower_word``: ``[a-z][A-Za-z0-9_]*``) rejects a digit- or
  paren-led name outright, so ``'(2S)Flavan4One'`` /
  ``'1,2-diacyl-sn-glycero-3-phosphocholine'`` (single-quoted, name
  untouched) is the only legal rendering — and since both example names'
  first character is not a letter, ``tptp_input``'s predicate-capitalising
  ``_cap()`` is a no-op on them, so the repair's own recovery of the exact
  original text (via its ``known_names`` mechanism — see the module
  docstring) is uncomplicated by that convention.
* **Case 3** (unbound variable): ``free_variables`` (already tested
  elsewhere) finds ``X`` unbound in the paper's own example; the two
  ``close_free_variables=True`` outcomes (argument-drop vs. universal
  closure) are derived by hand per formula shape in each test below.
"""

import pytest

from unicode_fol_kit import equivalent
from unicode_fol_kit.fol.nodes import (
    Atom, Constant, Variable, Iff, Implies, And, Quantifier, free_variables,
)
from unicode_fol_kit.fol.tptp_input import parse_tptp_formula, parse_tptp
from unicode_fol_kit.fol.tptp_repair import (
    Issue, RepairResult, repair_tptp_formula,
    ProblemRepairEntry, ProblemRepairResult, repair_tptp_problem,
    TptpRepairError, _tptp_quote, _find_prequoted_names,
)


# ---------------------------------------------------------------------------
# Case 1 — biimplication structure error (46 classes in the paper)
# ---------------------------------------------------------------------------

def test_case1_biimplication_paper_example_gets_fully_bracketed():
    """Paper's own literal example (Appendix B.1, Case 1): a definitional
    biimplication whose right side mixes ``<=>`` and ``&`` with no explicit
    grouping — the exact shape gavel rejects.

    Hand-derivation: ``&`` (``conj``) binds tighter than ``<=>`` (``equiv``)
    in the grammar, so this is unambiguously
    ``Iff(Predicate(x), And(Condition1, Condition2))`` — condition1/condition2
    are bare (argument-less) atoms as written, i.e. 0-ary props. Rendering
    that AST with unconditional full bracketing (case 1's fix) gives exactly
    ``"(predicate(x) <=> (condition1 & condition2))"``.
    """
    text = "predicate(x) <=> condition1 & condition2"
    r = repair_tptp_formula(text)

    assert isinstance(r, RepairResult)
    assert r.ok is True
    assert r.changed is True
    assert r.repaired_text == "(predicate(x) <=> (condition1 & condition2))"
    assert r.formula == Iff(
        Atom("Predicate", [Constant("x")]),
        And(Atom("Condition1", []), Atom("Condition2", [])))

    assert all(isinstance(i, Issue) for i in r.issues)
    kinds = [i.kind for i in r.issues]
    assert kinds == ["bracket_normalisation"]
    # No name or free-variable noise on a formula that has neither problem.
    assert not any(i.kind == "invalid_predicate_name" for i in r.issues)
    assert not any(i.kind == "free_variable" for i in r.issues)


def test_bracket_normalisation_preserves_ast_and_is_equivalent():
    """The meaning-preservation argument for case 1, made executable two
    independent ways:

    1. Parsing the ORIGINAL (unbracketed) text and parsing ``repaired_text``
       (fully bracketed) give literally ``==`` ASTs — not merely equivalent
       ones — because :func:`repair_tptp_formula`'s docstring argument holds:
       the grammar's precedence ladder makes both surface forms retrace the
       identical production sequence.
    2. Independently, :func:`unicode_fol_kit.equivalent` (a completely
       separate code path — structural ``==`` under the hood for
       ``method="exact"``, and Z3 unsat-of-negated-biconditional for
       ``method="solver"``) agrees the two ASTs mean the same thing.
    """
    text = "predicate(x) <=> condition1 & condition2"
    r = repair_tptp_formula(text)
    assert r.ok is True

    original_ast = parse_tptp_formula(text)
    repaired_ast = parse_tptp_formula(r.repaired_text)

    # Witness 1: literal AST identity (not just logical equivalence).
    assert original_ast == repaired_ast
    assert original_ast is r.formula or original_ast == r.formula

    # Witness 2: the kit's own equivalence-checking API, two rungs of its
    # ladder (both must see it — "exact" trivially, "solver" genuinely).
    exact = equivalent(original_ast, repaired_ast, method="exact")
    assert exact.equivalent is True and bool(exact) is True

    solver = equivalent(original_ast, repaired_ast, method="solver")
    assert solver.equivalent is True and solver.logically_equivalent is True


# ---------------------------------------------------------------------------
# Case 2 — invalid predicate name (29 classes in the paper)
# ---------------------------------------------------------------------------

def test_case2_stereodescriptor_prefix_paper_example_quoted_and_preserved():
    """Paper's own literal example: ``(2S)Flavan4One`` — a stereodescriptor
    prefix glued to a chemical name, starting with ``(`` so it cannot even be
    LEXED as an unquoted TPTP functor (the grammar's ``(`` is reserved for
    grouping/argument lists). Case-2's fix single-quotes it verbatim.

    Hand-check: the raw text below fails :func:`parse_tptp_formula` outright
    (confirmed separately below); the repaired form must be
    ``'(2S)Flavan4One'(a) => steroid(a)`` — note the capital ``S`` and ``F``/
    ``O`` are exactly as written, since ``(2S)Flavan4One``'s first character
    is ``(``, not a letter, so ``tptp_input``'s predicate-capitalising
    ``_cap()`` never touches ANY part of this name.
    """
    text = "(2S)Flavan4One(a) => steroid(a)"
    with pytest.raises(Exception):
        parse_tptp_formula(text)  # confirms this genuinely doesn't lex bare

    r = repair_tptp_formula(text)

    assert r.ok is True
    assert r.changed is True
    assert r.repaired_text == "('(2S)Flavan4One'(a) => steroid(a))"
    assert isinstance(r.formula, Implies)
    assert r.formula.left == Atom("(2S)Flavan4One", [Constant("a")])

    name_issues = [i for i in r.issues if i.kind == "invalid_predicate_name"]
    assert len(name_issues) == 1
    assert "(2S)Flavan4One" in name_issues[0].message
    assert name_issues[0].suggestion == "'(2S)Flavan4One'"


def test_case2_positional_prefix_paper_example_preserves_full_name():
    """Paper's other literal example: ``1,2-diacyl-sn-glycero-3-phosphocholine``
    — a digit-led, hyphen-/comma-bearing chemical name. The paper explicitly
    contrasts this with the lossy camelCase fallback
    (``diacylSnGlycero3Phosphocholine``, which drops the ``1,2-`` positional
    prefix and severs the ChEBI-class link); this test's whole point is that
    the repair does NOT do that — the ``1,2`` prefix specifically must
    survive, character for character.
    """
    original_name = "1,2-diacyl-sn-glycero-3-phosphocholine"
    text = f"{original_name}(a) => lipid(a)"
    r = repair_tptp_formula(text)

    assert r.ok is True
    assert r.repaired_text == f"('{original_name}'(a) => lipid(a))"
    assert r.formula.left.predicate == original_name
    # The specific fidelity claim the paper cares about: the "1,2" prefix.
    assert r.formula.left.predicate.startswith("1,2-")

    # Reparsing the repaired text recovers the identical predicate name —
    # the quoting round-trips, it does not merely "look right" as a string.
    reparsed = parse_tptp_formula(r.repaired_text)
    assert reparsed.left.predicate == original_name


def test_case2_escaping_of_embedded_quote_and_backslash():
    """A name carrying both a literal ``'`` and a literal ``\\`` (e.g. a
    biochemical name like ``5'-nucleotidase`` with a prime mark, here
    combined with a backslash to exercise both escapes in one string).

    A literal, un-escaped ``'`` inside an otherwise-unquoted name cannot be
    auto-detected by this module's raw-text heuristic (an apostrophe is
    TPTP's own quote delimiter, so :data:`_CANDIDATE_RE` deliberately never
    matches across one — see the module docstring); the realistic way such a
    name reaches this module is ALREADY quoted by its producer, e.g. gavel's
    own TPTP writer. So this test builds that pre-quoted input directly with
    :func:`_tptp_quote` (the function under test for the escaping itself) and
    checks the FULL round trip through :func:`repair_tptp_formula`.

    Hand-check of the escaping: TPTP's quoted-atom grammar token is
    ``'(\\\\.|[^'\\\\])*'`` — every character is either a bare non-quote/
    non-backslash, or a backslash followed by exactly one (any) character.
    ``_tptp_quote`` escapes only ``\\`` (first) and ``'`` (second), which is
    exactly the minimal encoding satisfying that token; the name starts with
    a digit, so ``_cap()``/``_uncap()`` never touch it and the round trip
    through the AST is exact (not merely a re-use of the input text).
    """
    original_name = "5'a\\b-nucleotidase"
    quoted = _tptp_quote(original_name)
    assert quoted == "'5\\'a\\\\b-nucleotidase'"  # hand-checked minimal escaping

    text = f"{quoted}(x) => enzyme(x)"
    directly_parsed = parse_tptp_formula(text)
    assert directly_parsed.left.predicate == original_name  # sanity: pre-quoted parses fine

    r = repair_tptp_formula(text)
    assert r.ok is True
    assert r.changed is True  # bracket normalisation still applies
    assert r.formula.left.predicate == original_name
    assert r.repaired_text == f"({quoted}(x) => enzyme(x))"

    reparsed = parse_tptp_formula(r.repaired_text)
    assert reparsed.left.predicate == original_name


def test_case2_colliding_capitalisation_refuses_rather_than_merging():
    """Regression for a real bug in the ``known_names`` dict this module
    builds while quoting its OWN case-2 candidates (``_cap(name) ->
    name``): two DISTINCT raw-text candidates that differ only in the case
    of their first letter — ``"N-acetyl-x"`` and ``"n-acetyl-x"``, both
    invalid unquoted (the internal hyphen fails ``lower_word``) — get
    quoted independently by ``_apply_name_quoting`` (each keeps its own
    exact spelling as a separate substring in ``retried_text``, so the
    quoted TEXT still distinguishes them) but ``tptp_input``'s
    Atom-predicate ``_cap()`` capitalises the first character of EVERY
    parsed predicate name unconditionally: ``_cap("N-acetyl-x") ==
    _cap("n-acetyl-x") == "N-acetyl-x"``. Both quoted atoms therefore
    reparse to the IDENTICAL ``Atom`` predicate name.

    Hand-derivation of the pre-fix bug: the old code did a plain
    ``known_names[_cap(name)] = name`` in a loop over both candidates in
    discovery order — first ``known_names["N-acetyl-x"] = "N-acetyl-x"``,
    then OVERWRITTEN by ``known_names["N-acetyl-x"] = "n-acetyl-x"`` — so
    BOTH occurrences in the rendered output would have silently come back
    as ``'n-acetyl-x'``, quietly losing the fact that the input named two
    separate predicates. The fix detects the collision while building
    ``known_names`` (``_cap(name)`` already present with a DIFFERENT
    stored value) and refuses outright.
    """
    text = "N-acetyl-x(a) & n-acetyl-x(b)"
    with pytest.raises(Exception):
        parse_tptp_formula(text)  # hyphen is not legal in an unquoted LOWER token

    r = repair_tptp_formula(text)

    assert r.ok is False
    assert r.formula is None
    assert r.repaired_text == text  # untouched — nothing unverified is emitted
    assert r.changed is False
    assert len(r.issues) == 1
    assert r.issues[0].kind == "name_collision"
    assert "N-acetyl-x" in r.issues[0].message
    assert "n-acetyl-x" in r.issues[0].message


def test_case2_prequoted_uppercase_name_direct_parse_keeps_quoting():
    """Regression for the ``_uncap`` fallback silently DROPPING quoting
    entirely (not merely mis-casing it) for a name that was ALREADY quoted
    in the input and needs no case-2 retry at all (``'Foo'(a)`` lexes and
    parses fine directly via the grammar's ``SQ`` token).

    Hand-derivation of the pre-fix bug: ``'Foo'(a) => bar(a)`` parses
    directly (no ``ParsingError``), so the old code's ``known_names`` stayed
    ``{}`` for the whole call — the case-2 retry branch that populates it
    never runs. At render time ``_render_predicate_name("Foo", {})`` missed
    in the (empty) dict and fell back to ``_uncap("Foo") == "foo"``. Since
    ``"foo"`` happens to satisfy ``lower_word`` (no hyphen or other special
    character forces continued quoting), ``_needs_quote("foo")`` was
    ``False`` — so the old renderer emitted the BARE, unquoted, WRONGLY
    lower-cased ``foo(a)``, discarding the caller's original quoting
    entirely rather than merely getting its case wrong. This module's own
    docstring only ever documented the narrower "wrong case, but still
    quoted" failure mode (e.g. an internal hyphen forcing continued
    quoting); dropping the quotes altogether is a strictly worse, previously
    UNDOCUMENTED failure. The fix (``_find_prequoted_names``) scans the raw
    text for every already-quoted literal independently of ``known_names``
    and feeds the recovered exact spelling into ``_render``, so the
    original quoting (and case) survives even on this direct-parse path.
    """
    text = "'Foo'(a) => bar(a)"
    directly_parsed = parse_tptp_formula(text)  # confirms no repair is needed to parse
    assert directly_parsed.left.predicate == "Foo"  # _cap() is a no-op — already capital

    r = repair_tptp_formula(text)

    assert r.ok is True
    assert r.formula.left.predicate == "Foo"
    assert r.repaired_text == "('Foo'(a) => bar(a))"  # quoting AND case preserved
    assert not any(i.kind == "invalid_predicate_name" for i in r.issues)

    # The repaired text really does round-trip to the same quoted name.
    reparsed = parse_tptp_formula(r.repaired_text)
    assert reparsed.left.predicate == "Foo"


def test_find_prequoted_names_drops_genuinely_ambiguous_collisions():
    """Direct unit test of :func:`_find_prequoted_names`'s documented
    ambiguity handling: when two DIFFERENT quoted originals literally
    present in the text share one ``_cap()`` image (``'Foo'`` and ``'foo'``
    both occur), that shared image cannot be resolved from raw text alone
    (there is no way to know which spelling belongs to which occurrence in
    the eventual AST) — the function must drop that key entirely rather
    than guessing, while an UNAMBIGUOUS quoted name elsewhere in the same
    text must still be recovered normally.
    """
    text = "'Foo'(a) => 'foo'(a) & 'bar-baz'(a)"
    found = _find_prequoted_names(text)

    # "Foo"/"foo" collide on the _cap() image "Foo" -> dropped entirely.
    assert "Foo" not in found
    # "bar-baz" is unambiguous (no colliding sibling) -> recovered exactly.
    assert found["Bar-baz"] == "bar-baz"


def test_case2_camelcase_and_uppercase_locant_names_round_trip_exactly():
    """Regression guard for the ``_cap()``/``_uncap`` interaction this module
    has to get right (see the module docstring): a mixed-case unquoted name
    (``threeOxoSteroid``, legal per TPTP's ``lower_word`` — mixed case is
    allowed after the first, lower-case, character) must NOT be flattened by
    the renderer, and an invalid name that happens to start with an
    upper-case chemical locant (``N-acetyl-L-methionine``, a realistic IUPAC
    prefix) must keep that capitalisation exactly, not have it silently
    lower-cased.
    """
    camel = repair_tptp_formula("threeOxoSteroid(a) => steroid(a)")
    assert camel.repaired_text == "(threeOxoSteroid(a) => steroid(a))"
    assert camel.formula.left.predicate == "ThreeOxoSteroid"  # _cap()'d, as always
    assert parse_tptp_formula(camel.repaired_text).left.predicate == "ThreeOxoSteroid"

    locant = repair_tptp_formula("N-acetyl-L-methionine(a) => aminoAcid(a)")
    assert locant.ok is True
    assert locant.formula.left.predicate == "N-acetyl-L-methionine"
    assert locant.repaired_text == "('N-acetyl-L-methionine'(a) => aminoAcid(a))"


# ---------------------------------------------------------------------------
# Case 3 — unbound variable (14 classes in the paper)
# ---------------------------------------------------------------------------

_CASE3_TEXT = "threeOxoSteroid(X) <=> (steroid & ?[A1,A2]: (c(A1) & o(A2)))"


def test_case3_free_variable_paper_example_reported_not_silently_changed():
    """Paper's own literal example. ``X`` is free (it appears only on the
    left; ``A1``/``A2`` are existentially bound). Default
    ``close_free_variables=False``: the free variable is REPORTED but the
    formula is not silently rewritten — the left-hand definiendum still
    carries its (unbound) argument exactly as parsed.
    """
    r = repair_tptp_formula(_CASE3_TEXT)

    assert r.ok is True
    free_issues = [i for i in r.issues if i.kind == "free_variable"]
    assert len(free_issues) == 1
    assert "x" in free_issues[0].message  # parser lower-cases variable names
    assert free_issues[0].suggestion is None  # nothing was applied

    # Not silently changed: the left side still has its 1-ary argument, and
    # the AST still has exactly the one free variable the paper describes.
    assert isinstance(r.formula, Iff)
    assert r.formula.left == Atom("ThreeOxoSteroid", [Variable("x")])
    assert free_variables(r.formula) == {Variable("x")}


def test_case3_close_free_variables_drops_argument_per_paper():
    """``close_free_variables=True`` on the exact same formula: the paper's
    own fix applies here (``X`` is the SOLE argument of the left-hand
    definiendum and does not recur on the right, since the right side only
    mentions the separately-bound ``A1``/``A2``) — the argument is dropped,
    turning ``threeOxoSteroid`` into the 0-ary, molecule-level predicate the
    paper says it always meant.
    """
    r = repair_tptp_formula(_CASE3_TEXT, close_free_variables=True)

    assert r.ok is True
    assert free_variables(r.formula) == set()
    assert isinstance(r.formula, Iff)
    assert r.formula.left == Atom("ThreeOxoSteroid", [])  # argument dropped
    # The right side is UNCHANGED by the drop (only the definiendum's own
    # argument list is touched).
    original_right = parse_tptp_formula(_CASE3_TEXT).right
    assert r.formula.right == original_right

    free_issues = [i for i in r.issues if i.kind == "free_variable"]
    assert len(free_issues) == 1
    assert "dropped" in free_issues[0].message
    assert free_issues[0].suggestion == r.repaired_text

    # And the repaired text really does re-parse to a CLOSED formula.
    reparsed = parse_tptp_formula(r.repaired_text)
    assert free_variables(reparsed) == set()
    assert reparsed.left == Atom("ThreeOxoSteroid", [])


def test_case3_close_free_variables_falls_back_to_universal_closure():
    """When the paper's narrow argument-drop shape does NOT apply — here
    ``X`` recurs on the right (``q(X)``), so dropping the left argument
    would silently discard information the formula actually depends on —
    ``close_free_variables=True`` instead applies the standard, generic
    universal closure: ``∀X (p(X) <=> q(X))``.
    """
    r = repair_tptp_formula("p(X) <=> q(X)", close_free_variables=True)

    assert r.ok is True
    assert free_variables(r.formula) == set()
    assert isinstance(r.formula, Quantifier)
    assert r.formula.type == "∀"
    assert r.formula.variable == Variable("x")
    assert r.formula.formula == Iff(
        Atom("P", [Variable("x")]), Atom("Q", [Variable("x")]))
    assert r.repaired_text == "(![X]: (p(X) <=> q(X)))"

    free_issues = [i for i in r.issues if i.kind == "free_variable"]
    assert len(free_issues) == 1
    assert "universal" in free_issues[0].message


# ---------------------------------------------------------------------------
# Idempotency / honest failure
# ---------------------------------------------------------------------------

def test_already_correct_formula_is_left_unchanged():
    """A formula already in exactly the canonical shape the repair itself
    would produce (fully bracketed, valid names, closed) must come back with
    ``changed=False`` and no issues — running the repair twice is a no-op.
    """
    text = "(![X]: (p(X) => q(X)))"
    r = repair_tptp_formula(text)

    assert r.ok is True
    assert r.changed is False
    assert r.issues == ()
    assert r.repaired_text == text
    assert r.formula == parse_tptp_formula(text)


def test_unbalanced_parentheses_reported_as_honestly_unrepairable():
    """Genuinely broken syntax that ISN'T explained by an invalid-name
    heuristic candidate (no digit-/paren-led name glued to ``(`` anywhere in
    this text — every functor here, ``p``/``q``, is already a legal
    ``lower_word``) must be reported as ``ok=False`` rather than guessed at:
    the module's "refuse rather than silently reinterpret" contract.
    """
    text = "p(x) & (q(x)"
    with pytest.raises(Exception):
        parse_tptp_formula(text)

    r = repair_tptp_formula(text)

    assert r.ok is False
    assert r.formula is None
    assert r.repaired_text == text  # untouched — nothing unverified is emitted
    assert r.changed is False
    assert len(r.issues) == 1
    assert r.issues[0].kind == "syntax_error"


def test_quote_invalid_names_false_disables_the_case2_fallback():
    """With ``quote_invalid_names=False``, a name that WOULD have been
    auto-quotable is instead reported as a plain, unrepaired syntax error —
    the flag gates only this one fallback attempt.
    """
    text = "1,2-diacyl-sn-glycero-3-phosphocholine(a) => lipid(a)"
    r = repair_tptp_formula(text, quote_invalid_names=False)

    assert r.ok is False
    assert r.formula is None
    assert r.repaired_text == text
    assert r.issues[0].kind == "syntax_error"
    assert not any(i.kind == "invalid_predicate_name" for i in r.issues)


# ---------------------------------------------------------------------------
# Whole-problem repair (repair_tptp_problem)
# ---------------------------------------------------------------------------

def test_repair_tptp_problem_repairs_each_statement_and_preserves_metadata():
    """A 2-statement file: one needs case-1 bracketing, the other is already
    clean. Every statement's ``name``/``role`` and the file's own comment
    must survive verbatim in the reassembled text, and the reassembled text
    must itself be a valid TPTP file (re-parseable by :func:`parse_tptp`).
    """
    text = (
        "% a demo problem\n"
        "fof(ax1, axiom, p(x) <=> a & b).\n"
        "fof(ax2, axiom, (steroid(x) => mortal(x))).\n"
    )
    r = repair_tptp_problem(text)

    assert isinstance(r, ProblemRepairResult)
    assert all(isinstance(e, ProblemRepairEntry) for e in r.entries)
    assert r.ok is True
    assert r.changed is True  # ax1 needed bracketing
    assert len(r.entries) == 2
    assert [(e.name, e.role) for e in r.entries] == [("ax1", "axiom"), ("ax2", "axiom")]
    assert r.entries[0].result.changed is True
    assert r.entries[1].result.changed is False  # ax2 was already canonical

    assert "% a demo problem" in r.repaired_text  # comment preserved verbatim

    formulas = parse_tptp(r.repaired_text)
    assert [f.name for f in formulas] == ["ax1", "ax2"]
    assert formulas[0].formula == Iff(
        Atom("P", [Constant("x")]), And(Atom("A", []), Atom("B", [])))
    assert formulas[1].formula == Implies(
        Atom("Steroid", [Constant("x")]), Atom("Mortal", [Constant("x")]))


def test_repair_tptp_problem_one_broken_statement_does_not_block_the_rest():
    """A statement whose FORMULA fails to parse for a reason unrelated to any
    of the three repairable shapes (here: the bare word ``XOR``, which is not
    a TPTP operator — ``<~>`` is — and, upper-case-led, lexes as a stray
    variable token, so the grammar rejects it outright; its parentheses are
    still perfectly balanced, so the statement SPLITTER locates it fine) must
    not prevent the other, valid statement in the same file from being
    located and repaired — that is the entire reason
    :func:`repair_tptp_problem` scans statement boundaries itself instead of
    delegating to the whole-file grammar (which would fail the whole file on
    the first bad statement).
    """
    text = (
        "fof(broken, axiom, p(x) XOR q(x)).\n"
        "fof(ok, axiom, r(x) <=> s & t).\n"
    )
    r = repair_tptp_problem(text)

    assert r.ok is False  # the conjunction — one statement failed
    assert len(r.entries) == 2
    assert r.entries[0].result.ok is False
    assert r.entries[0].result.repaired_text == "p(x) XOR q(x)"  # untouched
    assert r.entries[1].result.ok is True
    assert r.entries[1].result.repaired_text == "(r(x) <=> (s & t))"
    # The broken statement's own text is left untouched in the reassembly;
    # only the valid statement's formula span was rewritten.
    assert "fof(broken, axiom, p(x) XOR q(x))." in r.repaired_text
    assert "fof(ok, axiom, (r(x) <=> (s & t)))." in r.repaired_text


def test_repair_tptp_problem_raises_on_malformed_statement_structure():
    """A missing terminating ``.`` is a STRUCTURAL problem (the scanner
    cannot even tell where the statement ends), distinct from a per-formula
    syntax issue — :func:`repair_tptp_problem` raises rather than silently
    guessing a boundary.
    """
    with pytest.raises(TptpRepairError):
        repair_tptp_problem("fof(ax1, axiom, p(x))")  # no trailing "."


# ---------------------------------------------------------------------------
# Small dict-serialisation sanity (JSON-compatibility contract shared with
# the rest of the kit's *Result dataclasses, e.g. CheckResult/EquivalenceResult)
# ---------------------------------------------------------------------------

def test_to_dict_is_json_compatible_shape():
    r = repair_tptp_formula("predicate(x) <=> condition1 & condition2")
    d = r.to_dict()
    assert d["ok"] is True
    assert d["changed"] is True
    assert d["repaired_text"] == r.repaired_text
    assert d["formula"]["_type"] == "Iff"
    assert isinstance(d["issues"], list) and d["issues"][0]["kind"] == "bracket_normalisation"

    failed = repair_tptp_formula("p(x) & (q(x)")
    assert failed.to_dict()["formula"] is None
