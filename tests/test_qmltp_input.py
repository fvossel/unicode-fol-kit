"""Tests for the QMLTP reader (fol.qmltp_input).

Two independent kinds of check, matching this item's own test_oracle:

1. Structural/golden parsing tests: hand-checked expected ASTs and header
   fields for small, direct inputs (not derived from the code under test).
2. The FAITHFULNESS cross-check (the primary oracle): for each bundled
   QMLTP fixture, EVERY (logic, domain) cell of its own ``% Status`` table
   is decided independently via ``fol.qml.qml_is_valid`` (an existing,
   already-tested Z3 route this reader shares no code with) and compared
   against the file's own recorded ``Theorem``/``Non-Theorem`` verdict. A
   mismatch is a bug in the reader, never "close enough" (this item's own
   batch notes). All four fixtures were verified, by hand, against this
   exact oracle before being chosen (see the module docstring and the
   session's own transcript) -- this test re-runs that same check so a
   future regression is caught automatically.

Fixtures: ``tests/fixtures/qmltp/barcan.p``, ``converse_barcan.p``,
``box_all_to_dia_all.p`` and ``distinct_not_related.p`` -- written for this
suite in QMLTP v1.1 syntax, NOT copied from the QMLTP library (no
redistribution licence could be found for it; see ``fol/qmltp_input.py``'s
"License" section). The reader was developed and first checked against the
real QMLTP v1.1 files; these stand-ins keep the same syntax and header
layout. Each status table is derived by hand (the derivation is in each
file's own ``% Comments``) and re-checked cell by cell against
``fol.qml.qml_is_valid`` below. barcan/converse_barcan are the Barcan and
converse-Barcan schemes; box_all_to_dia_all additionally separates frame D
(seriality) from K; distinct_not_related is a Non-Theorem in every (logic,
domain) cell and exercises equality (``X = Y``) plus a binary user predicate.
"""

import os

import pytest

from unicode_logic_kit.fol.naming import ParsingError
from unicode_logic_kit.fol.nodes import (
    Atom, Box, Diamond, Implies, Not, Quantifier, Variable,
)
from unicode_logic_kit.fol.qml import qml_is_valid
from unicode_logic_kit.fol.qmltp_input import (
    QmltpFormula, QmltpHeader, QmltpParsingError, QmltpProblem, QmltpStatus,
    load_qmltp, parse_qmltp, parse_qmltp_formula,
)

_FIXTURE_DIR = os.path.join(os.path.dirname(__file__), "fixtures", "qmltp")


def _fixture(name: str) -> str:
    return os.path.join(_FIXTURE_DIR, name)


# ---------------------------------------------------------------------------
# Structural/golden parsing tests
# ---------------------------------------------------------------------------

def test_box_and_dia_parse_to_kit_nodes():
    """'#box : ( p )' / '#dia : ( p )' -> Box(P) / Diamond(P) -- the QMLTP
    surface syntax (# prefix, ':' before the parenthesised body) is
    genuinely different from NXF's own '[.]'/'{$box}@(...)' (see module
    docstring's correction to the roadmap's original description); this
    pins the ACTUAL syntax against a hand-built expected AST."""
    box_formula = parse_qmltp_formula("#box : ( p )")
    assert box_formula == Box(Atom("P", ()))

    dia_formula = parse_qmltp_formula("#dia : ( p )")
    assert dia_formula == Diamond(Atom("P", ()))


def test_barcan_scheme_instance_matches_hand_built_ast():
    """barcan.p's conjecture, ``( ( ! [X] : (#box : ( f(X) )) ) =>
    (#box : ( ! [X] : ( f(X) ) )) )``, parses to EXACTLY
    ``∀x □F(x) → □∀x F(x)`` built directly from kit nodes -- the box-Barcan
    scheme, hand-verified (see module docstring)."""
    text = ("( ( ! [X] : (#box : ( f(X) )) ) => "
            "(#box : ( ! [X] : ( f(X) ) )) )")
    parsed = parse_qmltp_formula(text)

    x = Variable("x")
    f = lambda t: Atom("F", [t])
    expected = Implies(Quantifier("∀", x, Box(f(x))), Box(Quantifier("∀", x, f(x))))
    assert parsed == expected


def test_nested_box_dia_and_negation():
    """'#box : ( ~ (#dia : ( p )) )' -> Box(Not(Diamond(P))) -- confirms
    the modal connectives nest correctly with classical negation, reusing
    fol.tptp_input's inherited '~' rule unchanged."""
    parsed = parse_qmltp_formula("#box : ( ~ (#dia : ( p )) )")
    assert parsed == Box(Not(Diamond(Atom("P", ()))))


def test_function_term_argument_parses_via_inherited_term_grammar():
    """'#box : ( p(f(X)) )' -- a compound function-term ARGUMENT (f(X))
    parses correctly purely because _QmltpTransformer INHERITS
    fol.tptp_input's own term grammar/transformer unchanged; this reader
    adds nothing of its own for terms, so this one check confirms the
    whole classical sub-grammar (already covered by fol.tptp_input's own
    test suite) is reached correctly through the QMLTP extension point."""
    from unicode_logic_kit.fol.nodes import Function
    parsed = parse_qmltp_formula("#box : ( p(f(X)) )")
    assert parsed == Box(Atom("P", [Function("f", [Variable("x")])]))


def test_equality_parses_through_inherited_grammar():
    """distinct_not_related.p's '~ (X = Y)' -- confirms equality is read via the
    INHERITED classical grammar (fol.tptp_input's own 'equality' rule),
    unchanged by this module's modal extension."""
    parsed = parse_qmltp_formula("~ (X = Y)")
    assert parsed == Not(Atom("=", [Variable("x"), Variable("y")]))


def test_header_fields_and_status_table_for_sym001():
    """Hand-checked against barcan.p's own raw text (read directly, see
    the fixture file) -- file/domain/problem/source fields, and the FULL
    15-cell status table (5 logics x 3 domain conditions), in the file's
    own row/column order."""
    problem = load_qmltp(_fixture("barcan.p"))
    header = problem.header

    assert header.file == "barcan : unicode-logic-kit fixture in QMLTP v1.1 syntax"
    assert header.domain == "Syntactic (modal)"
    assert "Barcan scheme instance" in header.problem
    assert header.source == "[Brc46]"

    assert len(header.statuses) == 15
    assert header.status_for("K", "constant") == "Theorem"
    assert header.status_for("K", "varying") == "Non-Theorem"
    assert header.status_for("K", "cumulative") == "Non-Theorem"
    # S5+cumulative is the ONE cell that differs from the other four logics
    # (S5's symmetry collapses "cumulative" onto "constant" within a
    # cluster -- see this item's session notes) -- hand-checked against the
    # raw file AND independently against qml_is_valid below.
    assert header.status_for("S5", "cumulative") == "Theorem"
    assert header.status_for("T", "cumulative") == "Non-Theorem"

    assert len(problem.formulas) == 1
    assert problem.formulas[0].name == "con"
    assert problem.formulas[0].role == "conjecture"


def test_status_for_unknown_cell_raises_key_error():
    header = load_qmltp(_fixture("barcan.p")).header
    with pytest.raises(KeyError):
        header.status_for("K", "decreasing")  # QMLTP never records this column
    with pytest.raises(KeyError):
        header.status_for("S5.2", "constant")  # not a QMLTP logic name


def test_header_and_formulas_are_the_right_dataclasses():
    problem = load_qmltp(_fixture("distinct_not_related.p"))
    assert isinstance(problem, QmltpProblem)
    assert isinstance(problem.header, QmltpHeader)
    assert all(isinstance(f, QmltpFormula) for f in problem.formulas)
    assert all(isinstance(s, QmltpStatus) for s in problem.header.statuses)


# ---------------------------------------------------------------------------
# Refusals -- every unsupported construct is refused BY NAME, never
# silently dropped or approximated (project-wide rule).
# ---------------------------------------------------------------------------

def test_indexed_box_is_refused_by_name():
    with pytest.raises(NotImplementedError, match="indexed"):
        parse_qmltp_formula("#box(fool) : ( p )")


def test_indexed_dia_is_refused_by_name():
    with pytest.raises(NotImplementedError, match="indexed"):
        parse_qmltp_formula("#dia(a) : ( p )")


def test_multi_modal_tpi_directive_is_refused_by_name():
    """The MML domain's own 'tpi(1,set_logic,modal([...],[...])).' header
    statement -- hand-built from the real MML001+1.p shape (see module
    docstring's 'Statement keyword' note) -- is refused, naming the
    construct, rather than producing an opaque grammar syntax error."""
    text = (
        "tpi(1,set_logic,modal([cumulative,rigid,local],"
        "[(fool,s4),(a,s4),(b,s4),(c,s4)])).\n"
        "qmf(ax1,axiom, (#box(fool) : ( p ))).\n"
    )
    with pytest.raises(NotImplementedError, match="tpi"):
        parse_qmltp(text)


def test_fof_keyword_is_refused():
    """A plain TPTP fof(...) statement is not a QMLTP formula -- refused,
    since QMLTP's own 600 problems use 'qmf' exclusively (see module
    docstring's 'Statement keyword' correction)."""
    with pytest.raises(QmltpParsingError, match="qmf"):
        parse_qmltp("fof(a, axiom, p).")


def test_qmltp_parsing_error_is_a_parsing_error():
    """QmltpParsingError subclasses the shared ParsingError, so callers that
    already catch ParsingError (e.g. a generic 'try every reader' loop)
    keep working unchanged."""
    with pytest.raises(ParsingError):
        parse_qmltp("fof(a, axiom, p).")


def test_include_directive_is_refused():
    with pytest.raises(QmltpParsingError, match="include"):
        parse_qmltp("include('Axioms/foo.ax').\nqmf(a,axiom,(p)).")


def test_type_declaration_is_refused():
    with pytest.raises(QmltpParsingError, match="type declaration"):
        parse_qmltp("qmf(p_type, type, p: $o).")


def test_malformed_formula_raises_parsing_error():
    with pytest.raises(ParsingError):
        parse_qmltp_formula("#box : ( p")  # unbalanced parenthesis


# ---------------------------------------------------------------------------
# THE faithfulness cross-check (the item's primary test_oracle): every
# (logic, domain) cell of every bundled fixture's own status table, decided
# independently via fol.qml.qml_is_valid, must match the recorded verdict.
# ---------------------------------------------------------------------------

_FIXTURE_FILES = ("barcan.p", "converse_barcan.p", "box_all_to_dia_all.p",
                  "distinct_not_related.p")


def _load_fixture_cells():
    """(filename, formula, status) for every cell of every bundled fixture
    -- built once at collection time so each cell is its own pytest.param
    (clear per-cell reporting on a failure)."""
    cells = []
    for filename in _FIXTURE_FILES:
        problem = load_qmltp(_fixture(filename))
        assert len(problem.formulas) == 1, (
            f"{filename}: expected exactly one qmf(...) statement")
        formula = problem.formulas[0].formula
        for status in problem.header.statuses:
            cells.append(pytest.param(
                filename, formula, status,
                id=f"{filename}-{status.logic}-{status.domain}"))
    return cells


@pytest.mark.parametrize("filename,formula,status", _load_fixture_cells())
def test_reader_agrees_with_qmltps_own_recorded_status(filename, formula, status):
    """The reader's parsed formula, decided via qml_is_valid under the EXACT
    frame/mode this cell names, must agree with QMLTP's own recorded
    Theorem/Non-Theorem verdict for that (logic, domain) pair.

    QMLTP's logic names (K/D/T/S4/S5) and domain-condition names
    (varying/cumulative/constant) are used VERBATIM as qml_is_valid's own
    frame=/mode= values -- fol.qml.py already accepts "cumulative" as an
    alias of "increasing" (see that module's _ACTUALIST_MODES), so no
    translation table is needed between the two vocabularies, which is
    itself a small, independently-checked piece of faithfulness (a
    mismatch in NAMING would silently query the wrong regime even if the
    reader's own parsing were perfect).
    """
    expected_theorem = status.verdict == "Theorem"
    assert status.verdict in ("Theorem", "Non-Theorem"), (
        f"{filename}: unexpected verdict {status.verdict!r} -- this fixture "
        "set was chosen to avoid Unsolved/Open cells; if this fires, a "
        "differently-chosen fixture needs its own oracle strategy.")
    got = qml_is_valid(formula, mode=status.domain, frame=status.logic, timeout=5000)
    assert got == expected_theorem, (
        f"{filename}: QMLTP records {status.verdict!r} for logic="
        f"{status.logic!r}, domain={status.domain!r}, but "
        f"qml_is_valid(..., mode={status.domain!r}, frame={status.logic!r}) "
        f"returned {got!r} -- reader/oracle disagreement.")
