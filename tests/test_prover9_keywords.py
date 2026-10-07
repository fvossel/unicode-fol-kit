"""A rename for Prover9 never lands on a LADR keyword.

Prover9 reads an upper-case- or underscore-initial word as a VARIABLE
(``prolog_style_variables``), so a constant or a nullary predicate the kit spells
``All`` has to be written under a lower-case token. The renamer lower-cases the
first letter: ``All`` -> ``all``. But ``all`` and ``exists`` are the quantifier
keywords of LADR, and ``v`` is an infix operator (``a v b``). Measured on Prover9
2026-8A, the binary does NOT reject ``P(all)``: it reads ``all``, ``exists`` and ``v``
as ordinary constants and propositions (``P(all)``, ``all.``, ``v.``, ``all = b``,
``-all`` and ``f(all, a)`` are all accepted), so the rename is not needed to make
Prover9 read the file. It is kept as a precaution, because a word that is syntax in
the language is a poor name for a synthesised symbol: the kit's own Prover9 reader
keeps exactly this reserved set (``fol.prover9_input._RESERVED_SYMBOLS``: a file may
not redeclare them with ``op``), a reader of the written text that treats them as
syntax would misread the token, and the renamer therefore treats every
identifier-shaped member as TAKEN, so that the new token gets the numeric suffix the
scheme gives any token already in use: ``base``, then ``base2``, ``base3``, ...

Hand-derived tokens (the scheme above, applied to the reserved words ``all``,
``exists`` and ``v``): ``All`` -> ``all`` is taken -> ``all2``; ``Exists`` ->
``exists2``; ``V`` -> ``v2``. A name that merely STARTS like a keyword (``Allen``
-> ``allen``) is not one and is renamed as before.
"""

import pytest

from unicode_logic_kit.atp import prover9_entailment as p9
from unicode_logic_kit.atp.prover9_entailment import generate_prover9_input_with_mapping
from unicode_logic_kit.fol import prover9_input
from unicode_logic_kit.fol.nodes import And, Atom, Constant, Function


def _text(premise, conclusion=None):
    conclusion = conclusion if conclusion is not None else Atom("Goal", [])
    text, names = generate_prover9_input_with_mapping([premise], conclusion)
    return text, names


def _lines(text):
    return {line.strip() for line in text.splitlines()}


def test_the_keyword_set_is_the_readers_own_identifier_shaped_reserved_words():
    assert p9._PROVER9_KEYWORDS == frozenset({"all", "exists", "v"})
    assert p9._PROVER9_KEYWORDS <= prover9_input._RESERVED_SYMBOLS


@pytest.mark.parametrize("name, token", [("All", "all2"), ("Exists", "exists2"), ("V", "v2")])
def test_a_constant_that_lower_cases_to_a_keyword_gets_its_suffix(name, token):
    text, names = _text(Atom("P", [Constant(name)]))
    assert f"P({token})." in _lines(text)
    assert f"P({name.lower()})." not in _lines(text)
    assert names.get_constant(name) == token
    # and the token reads back to the original name
    assert names.reverse()[token] == name


@pytest.mark.parametrize("name, token", [("All", "all2"), ("Exists", "exists2"), ("V", "v2")])
def test_a_nullary_predicate_that_lower_cases_to_a_keyword_gets_its_suffix(name, token):
    text, names = _text(Atom(name, []))
    assert f"{token}." in _lines(text)
    assert f"{name.lower()}." not in _lines(text)
    assert names.get_nullary(name) == token
    assert names.reverse()[token] == name


def test_the_two_renames_of_one_word_get_two_tokens():
    # ``All`` as a constant and as a nullary predicate: both are renamed, and the
    # two tokens differ (the second keyword-free candidate is all3).
    text, names = _text(And(Atom("P", [Constant("All")]), Atom("All", [])))
    assert names.get_constant("All") == "all2"
    assert names.get_nullary("All") == "all3"
    assert "(P(all2) & all3)." in _lines(text)


def test_a_token_already_in_use_is_still_avoided_after_the_keyword():
    # The problem already contains a legal name ``all2``: the suffix scheme goes on.
    text, names = _text(And(Atom("P", [Constant("All")]), Atom("Q", [Constant("all2")])))
    assert names.get_constant("All") == "all3"
    assert "P(all3)" in text and "Q(all2)" in text


def test_names_that_are_not_keywords_are_renamed_exactly_as_before():
    # The control, byte for byte: only the three keyword words are special.
    for name, token in [("X", "x"), ("Rain", "rain"), ("Allen", "allen"),
                        ("Exist", "exist"), ("Vee", "vee")]:
        text, names = _text(Atom("P", [Constant(name)]))
        assert f"P({token})." in _lines(text), (name, text)


def test_a_keyword_lowered_constant_under_a_function_gets_its_suffix_too():
    text, _ = _text(Atom("P", [Function("f", [Constant("All")])]))
    assert "P(f(all2))." in _lines(text)
