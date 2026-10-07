"""THF and TF1 are refused by name, whatever the rest of the text is.

The module docstring of ``fol.tptp_input`` promises that THF (higher-order TPTP) and TF1
polymorphism (type variables, ``!>``) are refused loudly, naming the construct. Only a THF
statement whose body happened to parse in the first-order grammar got that refusal; real THF
(a type declaration ``p : $i > $o``, an application ``p @ A``) and real TF1 (``!>`` with
typed type variables, ``![A: $tType]``) ended in "could not parse TPTP problem: No terminal
matches ...". The statement's kind and the binder are now found before the first-order
grammar is tried, in the text with its comments and quoted atoms taken out.
"""
import pytest

from unicode_logic_kit.fol.tptp_input import (
    TptpParsingError, load_tff_problem, load_tptp, parse_tff_problem, parse_tptp,
    parse_tptp_formula, parse_tptp_problem,
)

_READERS = [parse_tptp, parse_tff_problem, parse_tptp_problem]

_THF = [
    "thf(a, axiom, p).",
    "thf(g, conjecture, ( ! [A: $i] : ( ( p @ A ) & $true ) )).",
    "thf(d, type, ( p : ( $i > $o ) )).",
    "thf(d, type, p: $i > $o ).",
    "fof(a, axiom, p).\nthf(d, type, ( p : ( $i > $o ) )).",
    "fof(a, axiom, p).  /* the next one is higher-order */  thf(g, axiom, ( q @ a )).",
    "% a header\ntff(s, type, s: $tType).\nthf(h, axiom, ( ^ [X: $i] : ( p @ X ) )).",
]

_TF1 = [
    "tff(d, type, p: !> [A]: (A > $o)).",
    "tff(d, type, p: !>[A: $tType]: (A > $o)).",
    "tff(d, type, p: !> [A: $tType, B: $tType]: ((A * B) > $o)).",
    "tff(f, axiom, ![A: $tType]: p(A)).",
    "tff(f, axiom, ![A: $tType, X: A]: p(X)).",
    "tff(f, axiom, !>[A: $tType]: ![X: A]: p(X)).",
]


@pytest.mark.parametrize("text", _THF)
@pytest.mark.parametrize("reader", _READERS)
def test_a_thf_statement_is_refused_by_name_whatever_its_body(reader, text):
    with pytest.raises(TptpParsingError, match="THF"):
        reader(text)


@pytest.mark.parametrize("text", _TF1)
@pytest.mark.parametrize("reader", _READERS)
def test_tf1_polymorphism_is_refused_by_name_as_a_parse_error_and_as_not_implemented(
        reader, text):
    """Both contracts hold: ``TptpParsingError`` (every refusal of a text this reader does
    not read) and ``NotImplementedError`` (what the refusal of a TF1 type declaration
    always was), and the message says TF1 and polymorphic."""
    with pytest.raises(TptpParsingError, match="TF1") as caught:
        reader(text)
    assert isinstance(caught.value, NotImplementedError)
    assert "polymorphic" in str(caught.value)
    with pytest.raises(NotImplementedError, match="[Pp]olymorphic"):
        reader(text)


def test_a_thf_file_is_refused_by_name_too(tmp_path):
    path = tmp_path / "higher_order.p"
    path.write_text("thf(d, type, ( p : ( $i > $o ) )).\n", encoding="utf-8")
    with pytest.raises(TptpParsingError, match="THF"):
        load_tptp(str(path))
    with pytest.raises(TptpParsingError, match="THF"):
        load_tff_problem(str(path))


def test_a_thf_statement_in_an_included_file_is_refused_by_name(tmp_path):
    (tmp_path / "axioms.ax").write_text("thf(d, type, ( p : ( $i > $o ) )).\n", encoding="utf-8")
    (tmp_path / "main.p").write_text("include('axioms.ax').\nfof(a, axiom, p).\n",
                                     encoding="utf-8")
    with pytest.raises(TptpParsingError, match="THF"):
        load_tptp(str(tmp_path / "main.p"))


@pytest.mark.parametrize("formula", [
    "!>[A: $tType]: p(A)",
    "![A: $tType]: p(A)",
])
def test_a_bare_formula_with_a_type_variable_is_refused_by_name(formula):
    with pytest.raises(TptpParsingError, match="TF1"):
        parse_tptp_formula(formula)


# ---------------------------------------------------------------------------
# What must keep reading
# ---------------------------------------------------------------------------

def test_a_comment_or_a_quoted_atom_that_mentions_thf_or_a_binder_is_no_refusal():
    """``thf(`` and ``!>`` are syntax only outside comments and quoted atoms; what the
    reader read before it still reads (hand-derived: three statements, p, q('...'), r)."""
    text = (
        "% thf(a, axiom, p).  and  !> [A]: p(A)\n"
        "fof(one, axiom, p).\n"
        "/* thf(b, axiom, q).\n   tff(c, type, c: !>[A: $tType]: (A > $o)). */\n"
        "fof(two, axiom, q('a.thf(b)')).\n"
        "fof(three, axiom, r('!> [A: $tType]')).\n"
    )
    names = [record.name for record in parse_tptp(text)]
    assert names == ["one", "two", "three"]


def test_a_predicate_called_thf_is_an_ordinary_predicate():
    """Inside a formula ``thf`` is a lower-case word like any other (the atom ``Thf(a)``);
    only a statement that BEGINS with it is a THF statement."""
    [record] = parse_tptp("fof(a, axiom, thf(a)).")
    assert record.formula.predicate == "Thf"
    assert parse_tptp_formula("thf(a)").predicate == "Thf"


def test_monomorphic_typed_problems_still_read():
    """TF0 uses ``$tType`` only in a sort declaration, whose name is lower-case, and
    quantifies over sorts the problem declares: nothing here is TF1."""
    signature, records = parse_tff_problem(
        "tff(human_type, type, human: $tType).\n"
        "tff(mortal_type, type, mortal: human > $o).\n"
        "tff(all_mortal, axiom, ![X: human]: mortal(X)).\n")
    assert signature.sorts == frozenset({"Human"})
    assert [record.name for record in records] == ["all_mortal"]


@pytest.mark.parametrize("sort", ["$int", "$rat", "$real"])
def test_the_arithmetic_sorts_are_still_refused_as_before(sort):
    with pytest.raises(NotImplementedError, match="arithmetic"):
        parse_tff_problem(f"tff(n_type, type, n: {sort} ).")
