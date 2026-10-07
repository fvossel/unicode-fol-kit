"""Every text reader reads LF, CRLF and bare-CR input identically.

Two ways line breaks other than LF reach the kit's readers:

* a git checkout with ``core.autocrlf`` (the Windows CI leg) turns every LF
  in a committed fixture into CRLF -- even one inside a quoted CSV cell,
  which ``csv`` (opened with ``newline=""``) hands through verbatim. That
  is how the P-FOLIO adapter broke on Windows CI after 0.28.0 (covered in
  ``tests/test_datasets_pfolio.py``);
* text handed to a ``parse_*`` function as a STRING (LLM output, a
  learner's hypothesis, a pasted snippet) skips the universal-newline
  translation a text-mode ``open`` applies, so it may carry CRLF or even a
  bare CR. Every ``%`` line comment used to be bounded by LF alone: on
  bare-CR text the first comment ran to the end of the input and swallowed
  every statement after it.

Each test builds the three conventions from ONE hand-written LF text and
requires the same, hand-checked result from all three.
"""

from pathlib import Path

import pytest

from unicode_logic_kit import MSFLParser
from unicode_logic_kit.fol.nodes import And, Atom, Constant, Implies, Quantifier, Variable

FOL = MSFLParser()

_FIXTURES = Path(__file__).parent / "fixtures"
CONVENTIONS = {"lf": "\n", "crlf": "\r\n", "cr": "\r"}


def _as(text: str, convention: str) -> str:
    """``text`` (any convention) with every line break rewritten."""
    lf = text.replace("\r\n", "\n").replace("\r", "\n")
    return lf.replace("\n", CONVENTIONS[convention])


def _fixture(*parts: str) -> str:
    return _FIXTURES.joinpath(*parts).read_bytes().decode("utf-8")


def _p(name):
    return Atom(name, [Constant("a")])


def test_the_helper_really_produces_each_convention():
    text = "one\r\ntwo\nthree"
    assert _as(text, "lf") == "one\ntwo\nthree"
    assert _as(text, "crlf") == "one\r\ntwo\r\nthree"
    assert _as(text, "cr") == "one\rtwo\rthree"


# ---------------------------------------------------------------------------
# TPTP / QMLTP / Prover9 / Prolog: a '%' comment ends at ANY line break
# ---------------------------------------------------------------------------

_TPTP = "% header\nfof(a1, axiom, p(a)).\n% mid\nfof(c, conjecture, q(a)).\n"


@pytest.mark.parametrize("convention", CONVENTIONS)
def test_tptp_statements_after_a_comment_survive(convention):
    from unicode_logic_kit.fol.tptp_input import parse_tptp, parse_tptp_problem
    text = _as(_TPTP, convention)
    formulas = parse_tptp(text)
    assert [(f.name, f.role, f.formula) for f in formulas] == [
        ("a1", "axiom", _p("P")), ("c", "conjecture", _p("Q"))]
    problem = parse_tptp_problem(text)
    assert problem.formulas == tuple(formulas)
    assert problem.header.comments == ("% header", "% mid")


@pytest.mark.parametrize("convention", CONVENTIONS)
def test_a_qmltp_file_reads_the_same_in_every_convention(convention):
    from unicode_logic_kit.fol.qmltp_input import parse_qmltp
    source = _fixture("qmltp", "barcan.p")
    problem = parse_qmltp(_as(source, convention))
    assert problem == parse_qmltp(_as(source, "lf"))
    assert problem.header.file == "barcan : unicode-logic-kit fixture in QMLTP v1.1 syntax"
    assert len(problem.formulas) == 1


@pytest.mark.parametrize("convention", CONVENTIONS)
def test_a_tpi_directive_after_the_first_line_is_refused_by_name(convention):
    # The tpi pre-scan looks for a statement at a LINE START; after a bare CR
    # it used to see none, and the file fell through to an opaque syntax error.
    from unicode_logic_kit.fol.qmltp_input import parse_qmltp
    text = _as("% MML-style header\n"
               "tpi(1,set_logic,modal([cumulative,rigid,local],"
               "[(fool,s4),(a,s4)])).\n"
               "qmf(ax1,axiom, (#box(fool) : ( p ))).\n", convention)
    with pytest.raises(NotImplementedError, match="'tpi"):
        parse_qmltp(text)


_PROVER9 = ("% c\nformulas(assumptions).\n  p(a).  % tail\nend_of_list.\n"
            "% c2\nformulas(goals).\n  q(a).\nend_of_list.\n")


@pytest.mark.parametrize("convention", CONVENTIONS)
def test_prover9_statements_after_a_comment_survive(convention):
    from unicode_logic_kit.fol.prover9_input import parse_prover9, parse_prover9_problem
    formulas = parse_prover9_problem(_as(_PROVER9, convention))
    assert [(f.role, f.formula) for f in formulas] == [
        ("assumptions", Atom("p", [Constant("a")])),
        ("goals", Atom("q", [Constant("a")]))]
    assert parse_prover9(_as("% c\np(a) & q(a)", convention)) == And(
        Atom("p", [Constant("a")]), Atom("q", [Constant("a")]))


@pytest.mark.parametrize("convention", CONVENTIONS)
def test_prolog_clauses_after_a_comment_survive(convention):
    from unicode_logic_kit.fol.prolog_input import parse_prolog_program
    x = Variable("x")
    clauses = parse_prolog_program(_as("% c\np(a).\n% c2\nq(X) :- p(X).\n", convention))
    assert clauses == [
        _p("P"),
        Quantifier("∀", x, Implies(Atom("P", [x]), Atom("Q", [x]))),
    ]


@pytest.mark.parametrize("convention", CONVENTIONS)
def test_a_learners_hypothesis_after_its_banner_comment_is_read(convention):
    # Popper/Aleph print a '% Precision..., Recall...' banner first; a bare-CR
    # copy used to come back as NO clauses at all.
    from unicode_logic_kit.fol.prolog_input import parse_prolog_program
    text = _as("% Precision:1.00, Recall:1.00, TP:2, FN:0, TN:1, FP:0\n"
               "f(A) :- p(A).\n", convention)
    a = Variable("a")                           # Prolog's A, lower-cased
    assert parse_prolog_program(text) == [
        Quantifier("∀", a, Implies(Atom("P", [a]), Atom("F", [a])))]


@pytest.mark.parametrize("convention", CONVENTIONS)
def test_tptp_repair_finds_every_statement_and_keeps_the_text(convention):
    from unicode_logic_kit.fol.tptp_repair import repair_tptp_problem
    text = _as(_TPTP, convention)
    result = repair_tptp_problem(text)
    assert result.ok and not result.changed
    assert [(e.name, e.role, e.result.formula) for e in result.entries] == [
        ("a1", "axiom", _p("P")), ("c", "conjecture", _p("Q"))]
    assert result.repaired_text == text          # untouched, byte for byte


# ---------------------------------------------------------------------------
# TSTP prover output
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("convention", CONVENTIONS)
def test_a_tstp_derivation_reads_the_same_in_every_convention(convention):
    from unicode_logic_kit.atp.tstp import extract_szs_status, parse_tstp_derivation
    source = _fixture("tstp_check", "vampire_superposition.txt")
    text = _as(source, convention)
    assert extract_szs_status(text) == "Theorem"
    steps = parse_tstp_derivation(text).steps
    reference = parse_tstp_derivation(_as(source, "lf")).steps
    assert [(s.name, s.role, s.formula) for s in steps] == [
        (s.name, s.role, s.formula) for s in reference]
    assert [s.name for s in steps][:2] == ["f1", "f2"]
    assert all(s.formula is not None for s in steps)


# ---------------------------------------------------------------------------
# CASL: comments end at any line break, and error lines count every convention
# ---------------------------------------------------------------------------

# to_casl_spec's own output for this theory, with a comment line in front.
_CASL = ("%% a comment\n"
         "spec KitExport =\n"
         "  sorts Thing\n"
         "  ops socrates : Thing\n"
         "  preds Human : Thing;\n"
         "        Mortal : Thing\n"
         "  . forall x : Thing . (Human(x) => Mortal(x))\n"
         "  . Human(socrates)\n"
         "  . Mortal(socrates) %implied\n"
         "end\n")


@pytest.mark.parametrize("convention", CONVENTIONS)
def test_a_casl_spec_after_a_comment_is_read(convention):
    from unicode_logic_kit.fol.casl_import import parse_casl_spec
    spec = parse_casl_spec(_as(_CASL, convention))
    assert spec.name == "KitExport"
    assert spec.axioms == (FOL.parse("∀x (Human(x) → Mortal(x))"),
                           FOL.parse("Human(socrates)"))
    assert spec.conjectures == (FOL.parse("Mortal(socrates)"),)


@pytest.mark.parametrize("convention", CONVENTIONS)
def test_a_casl_error_names_the_same_line_in_every_convention(convention):
    from unicode_logic_kit.fol.casl_import import CaslImportError, parse_casl_spec
    text = _as("spec S =\n  sorts Thing\n  %def\nend\n", convention)
    with pytest.raises(CaslImportError, match=r"^line 3: unsupported CASL annotation"):
        parse_casl_spec(text)


# ---------------------------------------------------------------------------
# SBN: one line per line, whatever the convention
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("convention", CONVENTIONS)
def test_an_sbn_document_reads_the_same_in_every_convention(convention):
    from unicode_logic_kit.drt.parser import parse_sbn
    source = _fixture("pmb", "p00", "d0001", "en.drs.sbn")
    drs, mapping = parse_sbn(_as(source, convention))
    reference_drs, reference_mapping = parse_sbn(_as(source, "lf"))
    assert drs == reference_drs
    assert mapping == reference_mapping
    assert len(drs.referents) == 2              # dog.n.01 and bark.v.01
