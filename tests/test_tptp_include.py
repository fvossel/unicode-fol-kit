"""Tests for ``include(...)`` directive resolution in ``fol/tptp_input.py``
(roadmap C47), plus the optional 4th (``source``)/5th (``useful_info``)
annotation fields the same grammar change admits.

Scope, matching the build spec:

* :func:`parse_tptp` / :func:`load_tptp` / :func:`parse_tptp_problem` /
  :func:`load_tptp_problem` / :func:`parse_tff_problem` /
  :func:`load_tff_problem` resolve ``include('path')`` /
  ``include('path', [name, ...])`` — relative to the including file's own
  directory first, then each ``search_paths`` root, then
  ``os.environ["TPTP"]`` if set.
* A selection list imports only the named formulas and refuses a name
  absent from the included file.
* A missing include file, a circular include chain, and (for the TF0
  reader) a selection list combined with an included file that declares
  TFF vocabulary are each refused BY NAME, never silently mishandled.
* :func:`parse_tptp_formula` never resolves includes — a single bare
  formula has no "including file".
* The 4th/5th annotation fields parse and are discarded: a statement with
  them is indistinguishable, once parsed, from its 3-field equivalent.

The differential oracle throughout is HAND-FLATTENING: an included file's
own text, spliced at the include's position and parsed with plain
:func:`parse_tptp` on the concatenation, is an independent second route to
the same :class:`TptpFormula` list that never itself calls include
resolution.
"""

from pathlib import Path

import pytest

from unicode_logic_kit.fol.naming import ParsingError
from unicode_logic_kit.fol.nodes import Atom, Constant, Variable
from unicode_logic_kit.fol.signature import Signature, PredicateDecl, ConstantDecl
from unicode_logic_kit.fol.tptp_input import (
    parse_tptp, parse_tptp_formula, load_tptp,
    parse_tptp_problem, load_tptp_problem,
    parse_tff_problem, load_tff_problem,
    TptpFormula, TptpParsingError,
)

FIXTURES = Path(__file__).parent / "fixtures" / "tptp_include"


def _names(records):
    return [r.name for r in records]


# =============================================================================
# Basic include: differential against hand-flattened concatenation
# =============================================================================

def test_basic_include_matches_hand_flattened_concatenation(tmp_path):
    """main.p include('helpers.ax'). + its own fof line, vs. helpers.ax's
    two axioms spliced at the include's position and parsed as one text --
    two independent routes to the identical TptpFormula list."""
    helpers_text = (
        "fof(h1, axiom, human(socrates)).\n"
        "fof(h2, axiom, ![X]: (human(X) => mortal(X))).\n"
    )
    (tmp_path / "helpers.ax").write_text(helpers_text, encoding="utf-8")
    main_text = (
        "include('helpers.ax').\n"
        "fof(goal, conjecture, mortal(socrates)).\n"
    )
    (tmp_path / "main.p").write_text(main_text, encoding="utf-8")

    result = load_tptp(str(tmp_path / "main.p"))

    # Independent second route: hand-splice the included text at the
    # include's position and parse the concatenation with plain parse_tptp
    # (which never itself resolves includes for bare text with no base_dir).
    hand_flattened = helpers_text + "fof(goal, conjecture, mortal(socrates)).\n"
    expected = parse_tptp(hand_flattened)

    assert result == expected
    assert _names(result) == ["h1", "h2", "goal"]
    assert result[0].formula == Atom("Human", [Constant("socrates")])


def test_three_level_nested_chain_transitive(tmp_path):
    """main.p includes a.ax, a.ax includes b.ax -- transitivity and
    ordering: b's statements first (innermost, spliced at a's include
    position), then a's own, then main's own."""
    (tmp_path / "b.ax").write_text("fof(b1, axiom, q(b)).\n", encoding="utf-8")
    (tmp_path / "a.ax").write_text(
        "include('b.ax').\nfof(a1, axiom, r(a)).\n", encoding="utf-8")
    (tmp_path / "main.p").write_text(
        "include('a.ax').\nfof(m1, conjecture, q(b)).\n", encoding="utf-8")

    result = load_tptp(str(tmp_path / "main.p"))
    assert _names(result) == ["b1", "a1", "m1"]

    expected = parse_tptp(
        "fof(b1, axiom, q(b)).\nfof(a1, axiom, r(a)).\nfof(m1, conjecture, q(b)).\n"
    )
    assert result == expected


# =============================================================================
# Selection lists
# =============================================================================

def test_selection_list_imports_only_named_formulas(tmp_path):
    helpers_text = (
        "fof(h1, axiom, p(a)).\n"
        "fof(h2, axiom, q(a)).\n"
        "fof(h3, axiom, r(a)).\n"
    )
    (tmp_path / "helpers.ax").write_text(helpers_text, encoding="utf-8")
    (tmp_path / "main.p").write_text(
        "include('helpers.ax', [h1, h3]).\nfof(goal, conjecture, p(a)).\n",
        encoding="utf-8")

    result = load_tptp(str(tmp_path / "main.p"))
    assert _names(result) == ["h1", "h3", "goal"]

    # Independent second route: hand-filter the FULL parse of helpers.ax
    # down to the same two names, in the selection's own order.
    full = {r.name: r for r in parse_tptp(helpers_text)}
    expected_selected = [full["h1"], full["h3"]]
    assert result[:2] == expected_selected


def test_selection_list_refuses_unknown_name(tmp_path):
    (tmp_path / "helpers.ax").write_text(
        "fof(h1, axiom, p(a)).\n", encoding="utf-8")
    (tmp_path / "main.p").write_text(
        "include('helpers.ax', [nope]).\n", encoding="utf-8")

    with pytest.raises(TptpParsingError, match="nope"):
        load_tptp(str(tmp_path / "main.p"))


# =============================================================================
# Two-tier lookup: base_dir first, then search_paths (never a naive
# same-directory-only resolver)
# =============================================================================

def test_include_resolves_only_via_search_paths_root():
    """uses_library.p's own directory has no Axioms/ subdirectory at all --
    'Axioms/animals.ax' resolves ONLY by trying the library root from
    search_paths, pinning the two-tier lookup rather than a resolver that
    only ever checks the referring file's own directory."""
    problem = str(FIXTURES / "problems" / "uses_library.p")
    library_root = str(FIXTURES / "library")

    result = load_tptp(problem, search_paths=(library_root,))
    assert _names(result) == ["dog_is_animal", "rex_is_dog", "goal"]
    assert result[-1].formula == Atom("Animal", [Constant("rex")])

    # Without search_paths, the same include is NOT found relative to the
    # referring file's own directory -- proves the two-tier lookup is real,
    # not a resolver that happens to always succeed.
    with pytest.raises(TptpParsingError, match="Axioms/animals.ax"):
        load_tptp(problem)


def test_tptp_env_var_is_tried_after_search_paths(tmp_path, monkeypatch):
    """os.environ['TPTP'], if set, is tried as a further root -- even with
    no explicit search_paths given."""
    env_root = tmp_path / "env_root"
    (env_root / "Axioms").mkdir(parents=True)
    (env_root / "Axioms" / "env.ax").write_text(
        "fof(e1, axiom, p(a)).\n", encoding="utf-8")
    problem_dir = tmp_path / "problems2"
    problem_dir.mkdir()
    (problem_dir / "main.p").write_text(
        "include('Axioms/env.ax').\nfof(g, conjecture, p(a)).\n", encoding="utf-8")

    monkeypatch.setenv("TPTP", str(env_root))
    result = load_tptp(str(problem_dir / "main.p"))
    assert _names(result) == ["e1", "g"]


# =============================================================================
# Refusals: missing file, circular chain, bare text with no base_dir
# =============================================================================

def test_missing_include_file_names_the_path(tmp_path):
    (tmp_path / "main.p").write_text(
        "include('does_not_exist.ax').\n", encoding="utf-8")
    with pytest.raises(TptpParsingError, match="does_not_exist.ax"):
        load_tptp(str(tmp_path / "main.p"))


def test_circular_include_a_includes_b_includes_a_names_the_cycle(tmp_path):
    (tmp_path / "a.p").write_text("include('b.p').\n", encoding="utf-8")
    (tmp_path / "b.p").write_text("include('a.p').\n", encoding="utf-8")

    with pytest.raises(TptpParsingError, match="circular") as excinfo:
        load_tptp(str(tmp_path / "a.p"))
    # both files of the cycle are named in the message, not swallowed
    message = str(excinfo.value)
    assert "a.p" in message
    assert "b.p" in message


def test_bare_text_include_without_base_dir_is_refused():
    """parse_tptp on bare text (base_dir=None, the default) cannot resolve
    an include -- there is no "including file's directory" -- and refuses
    naming the directive rather than guessing."""
    with pytest.raises(TptpParsingError, match="helpers.ax"):
        parse_tptp("include('helpers.ax').\n")


def test_parse_tptp_formula_never_resolves_includes():
    """Include resolution applies only to the file/load APIs -- a single
    bare formula (no wrapping fof/cnf statement, no notion of "the
    including file") is simply not include syntax at all."""
    with pytest.raises(ParsingError):
        parse_tptp_formula("include('helpers.ax').")


# =============================================================================
# Regression: every pre-existing (include-free) fixture still parses
# byte-identically with base_dir left at its (None) default
# =============================================================================

def test_regression_include_free_text_unaffected_by_default_base_dir():
    text = (
        "% Status   : Theorem\n"
        "fof(ax1, axiom, ![X]: (man(X) => mortal(X))).\n"
        "fof(ax2, hypothesis, man(socrates)).\n"
        "cnf(cl1, axiom, (~p(X) | q(X))).\n"
    )
    # No base_dir/search_paths given: identical to calling parse_tptp before
    # this task existed, and parse_tptp_problem's header scan is untouched.
    result = parse_tptp(text)
    assert _names(result) == ["ax1", "ax2", "cl1"]
    problem = parse_tptp_problem(text)
    assert problem.header.status == "Theorem"
    assert list(problem.formulas) == result


# =============================================================================
# The optional 4th (source) / 5th (useful_info) annotation fields
# =============================================================================

def test_four_and_five_field_annotations_discarded_fof():
    three = parse_tptp("fof(ax, axiom, p(a)).")
    four = parse_tptp("fof(ax, axiom, p(a), file('Bledsoe90', ax1)).")
    five = parse_tptp(
        "fof(ax, axiom, p(a), "
        "inference(resolution,[status(thm)],[ax1,ax2]), "
        "[description('why we believe this')])."
    )
    assert three == four == five == [
        TptpFormula("ax", "axiom", Atom("P", [Constant("a")]))]


def test_four_field_annotation_discarded_cnf():
    three = parse_tptp("cnf(cl1, axiom, p(X)).")
    four = parse_tptp("cnf(cl1, axiom, p(X), file('Src', cl1)).")
    assert three == four == [
        TptpFormula("cl1", "axiom", Atom("P", [Variable("x")]))]


def test_five_field_annotation_discarded_tff():
    """The same grammar rule backs tff statements too -- a type
    declaration's annotation fields are equally discarded."""
    sig3, formulas3 = parse_tff_problem(
        "tff(s_type, type, human: $tType ).\n"
        "tff(p_decl, type, p: human > $o ).\n"
        "tff(ax, axiom, ![X: human]: p(X) )."
    )
    sig5, formulas5 = parse_tff_problem(
        "tff(s_type, type, human: $tType, file('Src', s_type), [] ).\n"
        "tff(p_decl, type, p: human > $o ).\n"
        "tff(ax, axiom, ![X: human]: p(X), file('Src', ax) )."
    )
    assert sig3 == sig5
    assert formulas3 == formulas5


def test_malformed_annotation_still_raises():
    """A 4th field that is not even syntactically a general term is an
    honest syntax error, never silently ignored."""
    with pytest.raises(ParsingError):
        parse_tptp("fof(ax, axiom, p(a), <>).")


# =============================================================================
# The TF0 reader (parse_tff_problem / load_tff_problem) supports includes
# too -- whole-file always, a selection list only when the included file
# has no TFF type declarations (see the module docstring).
# =============================================================================

def test_tff_problem_whole_file_include_splices_decls_and_formulas(tmp_path):
    (tmp_path / "helpers.ax").write_text(
        "tff(human_type, type, human: $tType ).\n"
        "tff(mortal_decl, type, mortal: human > $o ).\n",
        encoding="utf-8")
    (tmp_path / "main.p").write_text(
        "include('helpers.ax').\n"
        "tff(socrates_decl, type, socrates: human ).\n"
        "tff(ax, axiom, mortal(socrates) ).\n",
        encoding="utf-8")

    sig, formulas = load_tff_problem(str(tmp_path / "main.p"))

    # Independent second route: the identical text with the include
    # manually spliced in, parsed by the very same (non-include) pipeline.
    expected_sig, expected_formulas = parse_tff_problem(
        "tff(human_type, type, human: $tType ).\n"
        "tff(mortal_decl, type, mortal: human > $o ).\n"
        "tff(socrates_decl, type, socrates: human ).\n"
        "tff(ax, axiom, mortal(socrates) ).\n"
    )
    assert sig == expected_sig == Signature(
        predicates={"Mortal": PredicateDecl("Mortal", 1, ("Human",))},
        constants={"socrates": ConstantDecl("socrates", "Human")},
        sorts=frozenset({"Human"}),
    )
    assert formulas == expected_formulas


def test_tff_selection_list_refused_when_included_file_declares_vocabulary(tmp_path):
    (tmp_path / "helpers.ax").write_text(
        "tff(human_type, type, human: $tType ).\n"
        "tff(mortal_decl, type, mortal: human > $o ).\n",
        encoding="utf-8")
    (tmp_path / "main.p").write_text(
        "include('helpers.ax', [human_type]).\n", encoding="utf-8")

    with pytest.raises(TptpParsingError, match="TFF"):
        load_tff_problem(str(tmp_path / "main.p"))


def test_tff_selection_list_still_works_on_a_pure_formula_file(tmp_path):
    """The refusal is scoped to files whose OWN (include-resolved) contents
    still contain a TYPE declaration -- a selection list on an included
    file that is pure tff AXIOM/CONJECTURE statements (no vocabulary of its
    own, declared or inherited via a nested include) works exactly like the
    fof/cnf case. The vocabulary those axioms need is declared directly in
    the file doing the selecting instead."""
    (tmp_path / "facts.ax").write_text(
        "tff(f1, axiom, mortal(socrates) ).\n"
        "tff(f2, axiom, mortal(socrates) ).\n",
        encoding="utf-8")
    (tmp_path / "main.p").write_text(
        "tff(human_type, type, human: $tType ).\n"
        "tff(mortal_decl, type, mortal: human > $o ).\n"
        "tff(socrates_decl, type, socrates: human ).\n"
        "include('facts.ax', [f1]).\n",
        encoding="utf-8")

    sig, formulas = load_tff_problem(str(tmp_path / "main.p"))
    assert _names(formulas) == ["f1"]
    assert sig.sorts == frozenset({"Human"})


# =============================================================================
# load_tptp_problem: includes resolve, header still comes from the ROOT
# file's own '%' lines only (never an included file's).
# =============================================================================

def test_load_tptp_problem_header_from_root_only_formulas_include_resolved(tmp_path):
    (tmp_path / "helpers.ax").write_text(
        "% Status   : Unsatisfiable\nfof(h1, axiom, p(a)).\n", encoding="utf-8")
    (tmp_path / "main.p").write_text(
        "% Status   : Theorem\ninclude('helpers.ax').\nfof(goal, conjecture, p(a)).\n",
        encoding="utf-8")

    problem = load_tptp_problem(str(tmp_path / "main.p"))
    # the ROOT file's own header wins, not the included file's
    assert problem.header.status == "Theorem"
    assert _names(problem.formulas) == ["h1", "goal"]
