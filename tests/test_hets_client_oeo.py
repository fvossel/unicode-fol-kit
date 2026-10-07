r"""B4 and B5: ``/translations`` that reports nothing, and the theory header.

All offline; ``_get``/``_request`` are monkeypatched, so no HETS server is
needed. Every fixture is a hand-written inline string shaped like the real
response — the real bodies (1.3-8.3 MB) are never committed.

Why this file and not ``tests/test_hets_client.py``: that module is already
523 lines across four concerns and is modified in the working tree. These
tests are additive and self-contained, and the one assertion that has to hold
in the OLD file (``test_dg_raises_runtime_error_on_invalid_json``) is
re-asserted in ``tests/test_hets_haskell_json.py`` so a regression cannot
hide.
"""

import urllib.error

import pytest

from unicode_logic_kit.fol.tptp_input import TptpParsingError, parse_tptp
from unicode_logic_kit.fol.nodes import (
    And, Atom, Constant, Function, Iff, Implies, Not, Number, Or, Quantifier,
    Variable, Xor,
)
from unicode_logic_kit.hets import (
    HetsClient,
    HetsNoTranslationsError,
    HetsSublogicError,
    strip_hets_theory_header,
)

# =============================================================================
# B4: an empty <li> list is not an answer.
# =============================================================================

# The two shapes the real server actually answered for the full OEO file
# (`rest_routes_result.json`: count 0, 3.21 s, no exception).
EMPTY_TRANSLATIONS = (
    "<Translations><translations></translations></Translations>")
SELF_CLOSING_TRANSLATIONS = (
    "<Translations><translations/></Translations>")


@pytest.mark.parametrize("body", [EMPTY_TRANSLATIONS, SELF_CLOSING_TRANSLATIONS])
def test_an_empty_translation_list_raises_and_says_where_the_reason_lives(
        monkeypatch, body):
    """Red before the change: both bodies returned [] with no exception."""
    monkeypatch.setattr(HetsClient, "_get", lambda self, path: body)
    client = HetsClient("http://localhost:8000")
    with pytest.raises(HetsNoTranslationsError) as caught:
        client.translations("/tmp/x/oeo.owl")
    message = str(caught.value)
    assert "offers no comorphism" in message
    assert "sublogic" in message
    assert "owl_to_tptp" in message
    assert "allow_empty=True" in message
    # A RuntimeError subclass, so every existing `except RuntimeError` caller
    # keeps working.
    assert isinstance(caught.value, RuntimeError)


def test_allow_empty_restores_the_old_return_value(monkeypatch):
    monkeypatch.setattr(HetsClient, "_get",
                        lambda self, path: EMPTY_TRANSLATIONS)
    client = HetsClient("http://localhost:8000")
    assert client.translations("/tmp/x/oeo.owl", allow_empty=True) == []


def test_hets_identity_entry_and_blank_entries_are_dropped(monkeypatch):
    """Red before the change: ['', 'OWL22CASL:CASL2TPTP_FOF', '  '].

    The first <li> of the real 21-entry list IS empty (`rest_reduced_
    translations.txt` starts with a blank line). It is HETS' identity
    (no-translation) entry: not a comorphism name, not a legal
    ``translation=`` value, and the reason
    ``register_hets_comorphisms`` used to register an edge named ``hets:``.
    """
    body = ("<Translations><translations>"
            "<li/>"
            "<li>OWL22CASL:CASL2SoftFOL</li>"
            "<li>OWL22CASL:CASL2TPTP_FOF</li>"
            "<li>  </li>"
            "</translations></Translations>")
    monkeypatch.setattr(HetsClient, "_get", lambda self, path: body)
    client = HetsClient("http://localhost:8000")
    assert client.translations("/tmp/x/oeo.owl") == [
        "OWL22CASL:CASL2SoftFOL", "OWL22CASL:CASL2TPTP_FOF"]


def test_the_filter_neither_reorders_nor_dedupes(monkeypatch):
    """Order and duplicates among REAL names are preserved exactly."""
    body = ("<Translations><translations>"
            "<li>CASL2PCFOL</li>"
            "<li>CASL2SoftFOL</li>"
            "<li>CASL2PCFOL</li>"
            "</translations></Translations>")
    monkeypatch.setattr(HetsClient, "_get", lambda self, path: body)
    client = HetsClient("http://localhost:8000")
    assert client.translations("/tmp/x/probe.casl") == [
        "CASL2PCFOL", "CASL2SoftFOL", "CASL2PCFOL"]


def test_node_is_sent_as_a_query_parameter(monkeypatch):
    """Measured 3.21 s without ?node= against 0.12 s with it."""
    seen = []

    def fake_get(self, path):
        seen.append(path)
        return ("<Translations><translations><li>OWL22CASL</li>"
                "</translations></Translations>")

    monkeypatch.setattr(HetsClient, "_get", fake_get)
    client = HetsClient("http://localhost:8000")
    client.translations("/tmp/x/oeo.owl",
                        node="https://openenergyplatform.org/ontology/oeo/")
    assert len(seen) == 1
    assert seen[0].startswith("/translations/%2Ftmp%2Fx%2Foeo.owl?node=")
    assert ("node=https%3A%2F%2Fopenenergyplatform.org%2Fontology%2Foeo%2F"
            in seen[0])


def test_no_node_sends_no_query_string(monkeypatch):
    seen = []

    def fake_get(self, path):
        seen.append(path)
        return ("<Translations><translations><li>OWL22CASL</li>"
                "</translations></Translations>")

    monkeypatch.setattr(HetsClient, "_get", fake_get)
    HetsClient("http://localhost:8000").translations("/tmp/x/oeo.owl")
    assert seen == ["/translations/%2Ftmp%2Fx%2Foeo.owl"]


def test_a_comorphism_name_is_returned_stripped(monkeypatch):
    """Red before: ['  OWL22CASL:CASL2TPTP_FOF \\n'] -- a name that, passed on as
    ``translation=``, is a different (unknown) comorphism than the one listed."""
    body = ("<Translations><translations>"
            "<li>  OWL22CASL:CASL2TPTP_FOF \n</li>"
            "<li>\tCASL2SoftFOL</li>"
            "</translations></Translations>")
    monkeypatch.setattr(HetsClient, "_get", lambda self, path: body)
    client = HetsClient("http://localhost:8000")
    assert client.translations("/tmp/x/oeo.owl") == [
        "OWL22CASL:CASL2TPTP_FOF", "CASL2SoftFOL"]


@pytest.mark.parametrize("body, root", [
    ("<Error>no such library</Error>", "Error"),
    ("<Error><li>OWL22CASL</li></Error>", "Error"),   # an <li> inside an error is not a list
    ("<html><body><ul><li>OWL22CASL</li></ul></body></html>", "html"),
])
@pytest.mark.parametrize("allow_empty", [False, True])
def test_a_well_formed_document_with_another_root_is_a_refusal_not_an_empty_list(
        monkeypatch, body, root, allow_empty):
    """Red before: ``allow_empty=True`` returned [] (and ``<li>`` text inside a
    foreign root was read as comorphism names); without it the answer was
    HetsNoTranslationsError, whose wording blames the library ("offers no
    comorphism") for the server's refusal."""
    monkeypatch.setattr(HetsClient, "_get", lambda self, path: body)
    client = HetsClient("http://localhost:8000")
    with pytest.raises(RuntimeError) as caught:
        client.translations("/tmp/x/oeo.owl", allow_empty=allow_empty)
    assert not isinstance(caught.value, HetsNoTranslationsError)
    message = str(caught.value)
    assert "<Translations>" in message               # names what it expected ...
    assert f"root is <{root}>" in message            # ... and what it got
    assert "offers no comorphism" not in message


# =============================================================================
# B4: the 422 sublogic signature becomes a typed, branchable exception.
# =============================================================================

# HETS' body, verbatim from the live server.
SUBLOGIC_422_BODY = (
    "*** Error:\n"
    "for 'OWL22CASL;CASL2TPTP_FOF' expected sublogic 'NP-sROIQux-D|-|'\n"
    " but found sublogic 'NP-sROIQ-D|Literal|dateTime|decimal|integer|string|'"
    " with signature sublogic 'ELQLRL-ALC'\n"
)


def _raise_http_error(code, body):
    import io

    def fake_urlopen(req, timeout=None):
        raise urllib.error.HTTPError(
            req.full_url, code, "Unprocessable Entity", {},
            io.BytesIO(body.encode("utf-8")))

    return fake_urlopen


def test_a_422_with_the_sublogic_signature_becomes_a_typed_exception(monkeypatch):
    import urllib.request

    monkeypatch.setattr(urllib.request, "urlopen",
                        _raise_http_error(422, SUBLOGIC_422_BODY))
    client = HetsClient("http://localhost:8000")
    with pytest.raises(HetsSublogicError) as caught:
        client.theory("/tmp/x/oeo.owl", node="n",
                      translation="OWL22CASL:CASL2TPTP_FOF")
    error = caught.value
    # HETS' own spelling, with the SEMICOLON, carried verbatim rather than
    # normalised to the ':' the URL takes.
    assert error.comorphism == "OWL22CASL;CASL2TPTP_FOF"
    assert error.expected == "NP-sROIQux-D|-|"
    assert error.found == "NP-sROIQ-D|Literal|dateTime|decimal|integer|string|"
    assert error.body == SUBLOGIC_422_BODY
    assert isinstance(error, RuntimeError)
    assert "owl_to_tptp" in str(error)


def test_a_422_without_the_signature_keeps_the_generic_wording(monkeypatch):
    """The typed exception must not swallow an unrelated 422."""
    import urllib.request

    monkeypatch.setattr(urllib.request, "urlopen",
                        _raise_http_error(422, "*** Error:\nsomething else\n"))
    client = HetsClient("http://localhost:8000")
    with pytest.raises(RuntimeError) as caught:
        client.theory("/tmp/x/oeo.owl", node="n")
    assert not isinstance(caught.value, HetsSublogicError)
    assert "-> HTTP 422:" in str(caught.value)


def test_a_500_is_unaffected(monkeypatch):
    import urllib.request

    monkeypatch.setattr(urllib.request, "urlopen",
                        _raise_http_error(500, SUBLOGIC_422_BODY))
    client = HetsClient("http://localhost:8000")
    with pytest.raises(RuntimeError) as caught:
        client.theory("/tmp/x/oeo.owl", node="n")
    assert not isinstance(caught.value, HetsSublogicError)
    assert "-> HTTP 500:" in str(caught.value)


# =============================================================================
# B5: the theory header.
# =============================================================================

# 30 lines in the shape of the real 1,554,903-char rendering: the DOL logic
# line, the CASL %{ ... }% signature block (whose real form is 2267 lines of
# constants:/predicates:), then the TPTP.
THEORY_FIXTURE = """logic TPTP.FOF

%{

constants:  op_a,
            op_b

predicates:  pred_p: $i > $o,
             sort_Thing: $i > $o

}%

fof(ax_ax1, axiom,
    ! [VAR_X]: (pred_p(VAR_X) => sort_Thing(VAR_X))).

fof(ax_ax2, axiom, ? [VAR_X]: (sort_Thing(VAR_X))).
"""

# The CASL rendering of the SAME library (translation=OWL22CASL, no
# CASL2TPTP_FOF). `rest_routes_result.json` records this head verbatim.
CASL_THEORY_FIXTURE = """logic CASL.SulFOL=

sorts DATA, Thing

preds pred_p : Thing

. forall x : Thing . pred_p(x)
"""


def test_the_header_is_split_off_structurally():
    header, body = strip_hets_theory_header(THEORY_FIXTURE)
    assert header.startswith("logic TPTP.FOF")
    assert header.rstrip().endswith("}%")
    assert "predicates:" in header          # HETS' signature listing is KEPT
    assert body.lstrip().startswith("fof(ax_ax1")
    assert "%{" not in body


def test_the_stripped_body_parses_to_the_hand_derived_formulas():
    r"""Two formulas, with the AST derived from the TPTP text by hand.

    ``VAR_X`` lowers to the variable ``var_x`` and ``pred_p`` capitalises to
    the predicate ``Pred_p`` — tptp_input's documented conventions, confirmed
    against the real file (whose first formula reads back as an ``Atom``
    with predicate ``Sort_DATA``).
    """
    _header, body = strip_hets_theory_header(THEORY_FIXTURE)
    formulas = parse_tptp(body)
    assert [f.name for f in formulas] == ["ax_ax1", "ax_ax2"]
    assert [f.role for f in formulas] == ["axiom", "axiom"]
    var_x = Variable("var_x")
    assert formulas[0].formula == Quantifier(
        "∀", var_x,
        Implies(Atom("Pred_p", (var_x,)), Atom("Sort_Thing", (var_x,))))
    assert formulas[1].formula == Quantifier(
        "∃", var_x, Atom("Sort_Thing", (var_x,)))


def test_parse_tptp_refuses_the_unstripped_text_by_name():
    """Red before the change: 'No terminal matches ...T... at line 1 col 7'."""
    with pytest.raises(TptpParsingError) as caught:
        parse_tptp(THEORY_FIXTURE)
    message = str(caught.value)
    assert "Hets theory rendering" in message
    assert "strip_hets_theory_header" in message
    assert "theory_tptp" in message
    assert "logic TPTP.FOF" in message


def test_a_text_with_no_header_comes_back_untouched():
    """So the call is safe to make unconditionally."""
    assert strip_hets_theory_header("fof(a, axiom, p).") == (
        "", "fof(a, axiom, p).")


def test_a_predicate_named_logic_still_parses():
    """The guard must not fire on a legitimate formula using `logic` as a name.

    A DOL logic name never contains a space and a TPTP statement always ends
    with '.', so requiring the WHOLE first line to be `logic <word>` keeps
    these parsing exactly as before.
    """
    assert parse_tptp("fof(a, axiom, logic & p).")[0].name == "a"
    from unicode_logic_kit.fol.tptp_input import parse_tptp_formula
    assert parse_tptp_formula("logic | p") is not None


# --- the guard is a LOGIC NAME test, so no operator spelling can trip it ------
#
# Measured on the first 0.30.0 build: the guard was "logic, whitespace, ONE
# whitespace-free word", which also matched the first line of the valid formula
# `logic &p` (the constant/proposition `logic`, conjoined with p). A DOL logic
# name is an identifier (CASL, SoftFOL, HasCASL, OWL, TPTP ...), optionally
# followed by `.` and a sublogic, so the word after `logic` can never BEGIN with
# an operator character.
#
# Expected values are hand-derived from the TPTP grammar and this reader's
# documented conventions, never from what the code printed:
#   * a lower-case proposition is capitalised on reading, so `logic` is
#     Atom("Logic") and `p` is Atom("P");
#   * `a & b`, `a | b`, `a => b`, `a <=> b`, `a <~> b` are And, Or, Implies, Iff
#     and Xor of the two operands in reading order;
#   * TPTP `a <= b` means "a if b", i.e. b => a, so it reads as Implies(b, a);
#   * `a ~| b` and `a ~& b` are NOR and NAND: Not(Or) and Not(And);
#   * `logic = t` / `logic != t` are an equality / a disequality whose left
#     term is the constant `logic` (a lower-case word is a constant in term
#     position), and a numeral reads as a Number.

_LOGIC = Atom("Logic", ())
_P = Atom("P", ())

_LOGIC_BINARY_CASES = [
    ("&", And(_LOGIC, _P)),
    ("|", Or(_LOGIC, _P)),
    ("=>", Implies(_LOGIC, _P)),
    ("<=", Implies(_P, _LOGIC)),
    ("<=>", Iff(_LOGIC, _P)),
    ("<~>", Xor(_LOGIC, _P)),
    ("~|", Not(Or(_LOGIC, _P))),
    ("~&", Not(And(_LOGIC, _P))),
]

_LOGIC_EQUALITY_CASES = [
    ("=", "a", Atom("=", (Constant("logic"), Constant("a")))),
    ("=", "7", Atom("=", (Constant("logic"), Number(7)))),
    ("=", "f(a)", Atom("=", (Constant("logic"), Function("f", (Constant("a"),))))),
    ("!=", "a", Atom("≠", (Constant("logic"), Constant("a")))),
    ("!=", "7", Atom("≠", (Constant("logic"), Number(7)))),
    ("!=", "f(a)", Atom("≠", (Constant("logic"), Function("f", (Constant("a"),))))),
]

# every spacing a first line can have: glued, one space, a tab, padded
_LOGIC_SPACINGS = ["logic{op}{atom}", "logic {op}{atom}", "logic\t{op}{atom}",
                   "  logic  {op}{atom}  ", "logic {op} {atom}"]


def _logic_texts():
    for op, expected in _LOGIC_BINARY_CASES:
        for template in _LOGIC_SPACINGS:
            yield template.format(op=op, atom="p"), expected
    for op, atom, expected in _LOGIC_EQUALITY_CASES:
        for template in _LOGIC_SPACINGS:
            yield template.format(op=op, atom=atom), expected
    # the operand on the NEXT line: the first line is `logic <op>`
    for op, expected in _LOGIC_BINARY_CASES:
        yield f"logic {op}\np", expected


def test_the_battery_covers_every_binary_connective_and_both_equalities():
    """So a connective the grammar has and this battery lacks cannot hide: the
    set of operator tokens the grammar's binary rules use, read off the
    grammar text itself."""
    import re

    from unicode_logic_kit.fol import tptp_input

    grammar_ops = set(re.findall(r'"(<=>|<~>|=>|<=|~\||~&|\||&)"', tptp_input._GRAMMAR))
    assert grammar_ops == {op for op, _ in _LOGIC_BINARY_CASES}
    assert {"=", "!="} == {op for op, _, _ in _LOGIC_EQUALITY_CASES}


@pytest.mark.parametrize("text, expected", list(_logic_texts()),
                         ids=lambda value: repr(value) if isinstance(value, str) else "")
def test_a_formula_whose_first_line_is_logic_and_an_operator_is_never_a_header(
        text, expected):
    """Red before the fix, 'Hets theory rendering' for every one of them."""
    from unicode_logic_kit.fol.tptp_input import parse_tptp_formula

    assert parse_tptp_formula(text) == expected


@pytest.mark.parametrize("text, expected", list(_logic_texts()),
                         ids=lambda value: repr(value) if isinstance(value, str) else "")
def test_nothing_the_bare_grammar_accepts_is_refused_by_the_pointer(text, expected):
    """The guarantee the pointer must keep, tested against an INDEPENDENT oracle:
    the raw Earley grammar, which has no pointer at all. Whatever it accepts,
    ``parse_tptp_formula`` must accept too."""
    from unicode_logic_kit.fol.tptp_input import _FORMULA_PARSER, parse_tptp_formula

    _FORMULA_PARSER.parse(text)                 # the oracle accepts (else the case is wrong)
    parse_tptp_formula(text)                    # ... so the pointer must not fire


@pytest.mark.parametrize("first_line", [
    "logic TPTP.FOF",                                   # the real TPTP header
    "logic CASL.SulFOL=",                               # the real CASL header
    "logic OWL.NP-sROIQx-D|Literal|dateTime|string|",   # the real OWL header
    "logic CASL",                                       # a bare logic name
    "logic HasCASL.Sub",
    "  logic   SoftFOL.Sub  ",                          # padded
])
def test_a_real_header_is_still_named(first_line):
    from unicode_logic_kit.fol.tptp_input import parse_tptp_formula

    with pytest.raises(TptpParsingError) as caught:
        parse_tptp_formula(first_line + "\n%{\n}%\nfof(a, axiom, p).")
    assert "Hets theory rendering" in str(caught.value)
    assert first_line.strip() in str(caught.value)


@pytest.mark.parametrize("text, expected", list(_logic_texts()),
                         ids=lambda value: repr(value) if isinstance(value, str) else "")
def test_the_header_splitter_does_not_eat_a_formula_either(text, expected):
    """``strip_hets_theory_header`` shares the notion of a header with the
    pointer (the same identifier-shaped reference): a bare formula whose first
    line is ``logic <op>...`` has NO header, so it comes back untouched. Red
    before: the splitter took ``logic &p`` for a header and returned an empty
    body."""
    assert strip_hets_theory_header(text) == ("", text)


@pytest.mark.parametrize("header_line", [
    "logic TPTP.FOF", "logic CASL.SulFOL=", "logic OWL.NP-sROIQx-D|Literal|dateTime|",
    "logic CASL", "logic TPTP.FOF  ", "logic TPTP.FOF\r",
])
def test_the_splitter_still_splits_every_real_header_shape(header_line):
    text = f"{header_line}\n\n%{{\nconstants: op_a\n}}%\n\nfof(a, axiom, p).\n"
    header, body = strip_hets_theory_header(text)
    assert header == f"{header_line}\n\n%{{\nconstants: op_a\n}}%"
    assert body == "\n\nfof(a, axiom, p).\n"


def test_an_unterminated_block_comment_is_not_silently_truncated():
    text = "logic TPTP.FOF\n\n%{\nconstants: op_a\n"
    header, body = strip_hets_theory_header(text)
    assert header == "logic TPTP.FOF\n"
    assert "%{" in body          # left for the caller's own refusal


def test_theory_tptp_returns_the_stripped_body(monkeypatch):
    monkeypatch.setattr(HetsClient, "_get", lambda self, path: THEORY_FIXTURE)
    client = HetsClient("http://localhost:8000")
    body = client.theory_tptp("/tmp/x/oeo.owl", node="n")
    assert body.lstrip().startswith("fof(ax_ax1")
    assert len(parse_tptp(body)) == 2


def test_theory_tptp_sends_the_tptp_comorphism_by_default(monkeypatch):
    seen = []

    def fake_get(self, path):
        seen.append(path)
        return THEORY_FIXTURE

    monkeypatch.setattr(HetsClient, "_get", fake_get)
    HetsClient("http://localhost:8000").theory_tptp("/tmp/x/oeo.owl", node="n")
    assert "translation=OWL22CASL%3ACASL2TPTP_FOF" in seen[0]
    assert "node=n" in seen[0]


def test_theory_tptp_refuses_a_casl_body_instead_of_returning_nothing(monkeypatch):
    """The case that must NEVER become []: a wrong-translation request.

    ``%`` already swallows ``%{`` as a line comment, so a reader taught the
    CASL block form would treat this whole theory as a comment and answer
    with an empty formula list.
    """
    monkeypatch.setattr(HetsClient, "_get",
                        lambda self, path: CASL_THEORY_FIXTURE)
    client = HetsClient("http://localhost:8000")
    with pytest.raises(RuntimeError) as caught:
        client.theory_tptp("/tmp/x/oeo.owl", node="n",
                           translation="OWL22CASL")
    message = str(caught.value)
    assert "did not return a TPTP problem" in message
    assert "OWL22CASL:CASL2TPTP_FOF" in message
    assert "sorts DATA, Thing" in message       # quotes the first line


def test_theory_tptp_refuses_an_unterminated_block_with_no_statement(monkeypatch):
    monkeypatch.setattr(
        HetsClient, "_get",
        lambda self, path: "logic TPTP.FOF\n\n%{\nconstants: op_a\n")
    client = HetsClient("http://localhost:8000")
    with pytest.raises(RuntimeError, match="did not return a TPTP problem"):
        client.theory_tptp("/tmp/x/oeo.owl", node="n")
