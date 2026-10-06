"""The fof problem says that a sorted constant is in its sort.

What a sort IS in this kit: ONE universe; a sort ``S`` is a non-empty subset of it
(the extension of the unary predicate ``S``); a sorted constant ``c:S`` denotes an
element of ``S`` (``c:A`` and ``c:B`` put it in both), and ``c:S`` here with a plain
``c`` there is ONE constant. So ``∀x:Human Mortal(x) ⊢ Mortal(socrates:Human)`` is
valid, and a fof text that only guards the quantifier (``human(X) => mortal(X)``) has
the countermodel in which ``socrates`` is no Human at all.

:func:`~unicode_fol_kit.atp._tptp_problem.generate_tptp_problem_with_mapping` therefore
writes, next to the non-emptiness line of every sort, one ``sort_member_<i>`` axiom
line per sorted constant. The constant in that line must be THE TOKEN THE PREMISES USE,
and the writer renames constants: ``human:Human`` is written ``human_term`` (the sort
guard is the word ``human``), ``9lives`` is written ``n9lives``, ``sókrates`` is
transliterated. A line built from the raw name is about another symbol, silently.

Every expected text below was written by hand from those rules, never copied from the
writer's output.
"""

import re
import shutil
import subprocess

import pytest

from unicode_fol_kit import api
from unicode_fol_kit.atp._tptp_problem import generate_tptp_problem_with_mapping
from unicode_fol_kit.atp.eprover_backend import (
    check_entailment_eprover_detailed, eprover_available,
)
from unicode_fol_kit.atp.tstp import extract_szs_status
from unicode_fol_kit.atp.vampire_entailment import (
    _spawn_vampire, check_entailment_vampire_detailed,
)


def parse(text):
    return api.parse_any(text).formula


def write(premise_texts, conclusion_text):
    premises = [parse(t) for t in premise_texts]
    conclusion = None if conclusion_text is None else parse(conclusion_text)
    return generate_tptp_problem_with_mapping(premises, conclusion)


def lines_of(text):
    return [ln for ln in text.splitlines() if ln.strip()]


# =============================================================================
# The text, by hand
# =============================================================================

def test_a_sorted_constant_gets_one_membership_line_after_the_nonemptiness_line():
    """∀x:Human Mortal(x) is ``![X]: (human(X) => mortal(X))``; Human is non-empty;
    socrates is a Human. The conclusion's own constant is the one that is a member
    (a sorted constant ONLY in the conclusion is still asserted: the line is a premise,
    never part of the goal)."""
    text, name_map = write(["∀x:Human Mortal(x)"], "Mortal(socrates:Human)")
    assert lines_of(text) == [
        "fof(premise_1, axiom, (![X]: (human(X) => mortal(X)))).",
        "fof(nonempty_sort_1, axiom, (?[X0]: human(X0))).",
        "fof(sort_member_1, axiom, human(socrates)).",
        "fof(goal, conjecture, mortal(socrates)).",
    ]
    assert name_map.term == {"socrates": "socrates"}


def test_a_constant_named_like_its_sort_is_written_with_the_same_token_in_the_membership_line():
    """``human:Human``: the sort guard is the word ``human``, so the constant cannot be
    written ``human`` (one word, two kinds of symbol): the writer renames it to
    ``human_term`` and records that. The membership line must say ``human(human_term)``;
    ``human(human)`` would assert something about a different, unused symbol and the
    problem would still have the countermodel in which the constant is no Human."""
    text, name_map = write(["∀x:Human Mortal(x)"], "Mortal(human:Human)")
    assert lines_of(text) == [
        "fof(premise_1, axiom, (![X]: (human(X) => mortal(X)))).",
        "fof(nonempty_sort_1, axiom, (?[X0]: human(X0))).",
        "fof(sort_member_1, axiom, human(human_term)).",
        "fof(goal, conjecture, mortal(human_term)).",
    ]
    assert name_map.term == {"human": "human_term"}
    assert "human(human)" not in text


def test_a_non_ascii_sorted_constant_is_written_with_its_transliterated_token():
    """``sókrates``: ``ó`` is not a TPTP word character, so the writer rewrites the name
    to ``su00f3krates`` (the code-point escape of ``ó``, U+00F3, after the letter that
    precedes it) and records it. The membership line uses that token, and the problem is
    not refused: a raw ``sókrates`` in the atom would look like a second constant next to
    ``su00f3krates``."""
    text, name_map = write(["∀x:Human Mortal(x)"], "Mortal(sókrates:Human)")
    token = "su00f3krates"
    assert name_map.term == {"sókrates": token}
    assert lines_of(text) == [
        "fof(premise_1, axiom, (![X]: (human(X) => mortal(X)))).",
        "fof(nonempty_sort_1, axiom, (?[X0]: human(X0))).",
        f"fof(sort_member_1, axiom, human({token})).",
        f"fof(goal, conjecture, mortal({token})).",
    ]


def test_a_digit_leading_sorted_constant_is_written_with_its_rewritten_token():
    """``9lives:Cat``: a TPTP constant starts with a letter, so the writer prefixes ``n``
    (``n9lives``). The membership line uses it; built from the raw name it would be
    refused outright (a digit-leading name is no TPTP word)."""
    text, name_map = write(["∀x:Cat Mortal(x)"], "Mortal(9lives:Cat)")
    assert name_map.term == {"9lives": "n9lives"}
    assert lines_of(text) == [
        "fof(premise_1, axiom, (![X]: (cat(X) => mortal(X)))).",
        "fof(nonempty_sort_1, axiom, (?[X0]: cat(X0))).",
        "fof(sort_member_1, axiom, cat(n9lives)).",
        "fof(goal, conjecture, mortal(n9lives)).",
    ]


def test_a_constant_with_two_sorts_is_a_member_of_both():
    """carl:A and carl:B: carl lies in A AND in B, so there is one membership line per
    pair, in order of first occurrence (A first, in the first premise)."""
    text, _ = write(["P(carl:A)", "Q(carl:B)"], "∃x:A Q(x)")
    assert lines_of(text) == [
        "fof(premise_1, axiom, p(carl)).",
        "fof(premise_2, axiom, q(carl)).",
        "fof(nonempty_sort_1, axiom, (?[X0]: a(X0))).",
        "fof(nonempty_sort_2, axiom, (?[X1]: b(X1))).",
        "fof(sort_member_1, axiom, a(carl)).",
        "fof(sort_member_2, axiom, b(carl)).",
        "fof(goal, conjecture, (?[X]: (a(X) & q(X)))).",
    ]


def test_a_constant_written_sorted_here_and_plain_there_is_one_constant_in_the_sort():
    """``P(carl)`` and ``Q(carl:A)`` are about ONE constant, which therefore is an A:
    one membership line, and the plain occurrence uses the same token."""
    text, _ = write(["P(carl)", "Q(carl:A)"], "∃x:A P(x)")
    assert lines_of(text) == [
        "fof(premise_1, axiom, p(carl)).",
        "fof(premise_2, axiom, q(carl)).",
        "fof(nonempty_sort_1, axiom, (?[X0]: a(X0))).",
        "fof(sort_member_1, axiom, a(carl)).",
        "fof(goal, conjecture, (?[X]: (a(X) & p(X)))).",
    ]


def test_a_sorted_constant_only_in_the_conclusion_is_asserted_as_a_premise():
    """No premise at all: the only sorted node is the conclusion's constant. The
    non-emptiness of Human and the membership of socrates are axioms BEFORE the goal,
    not conjuncts of it (a conjunct ``human(socrates) & ...`` could never be proved)."""
    text, _ = write([], "Mortal(socrates:Human)")
    assert lines_of(text) == [
        "fof(nonempty_sort_1, axiom, (?[X0]: human(X0))).",
        "fof(sort_member_1, axiom, human(socrates)).",
        "fof(goal, conjecture, mortal(socrates)).",
    ]


def test_without_a_conclusion_the_membership_line_is_still_written():
    """conclusion=None asks whether the premises are satisfiable; kay is in Foo, so R(kay)
    contradicts ¬R(kay): the membership line is what makes that so."""
    text, name_map = write(["∀x:Foo R(x)", "¬R(kay:Foo)"], None)
    assert lines_of(text) == [
        "fof(premise_1, axiom, (![X]: (foo(X) => r(X)))).",
        "fof(premise_2, axiom, ~(r(kay))).",
        "fof(nonempty_sort_1, axiom, (?[X0]: foo(X0))).",
        "fof(sort_member_1, axiom, foo(kay)).",
    ]
    assert "conjecture" not in text
    assert name_map.term == {"kay": "kay"}


def test_a_sorted_constant_that_occurs_twice_is_asserted_once():
    text, _ = write(["P(carl:A)", "Q(carl:A)"], "P(carl:A)")
    assert text.count("sort_member_") == 1
    assert lines_of(text).count("fof(sort_member_1, axiom, a(carl)).") == 1


def test_a_constant_renamed_for_a_clash_with_a_predicate_is_a_member_under_its_new_token():
    """``car`` is the constant and ``Car`` a predicate of the same problem: both are the word
    ``car``, so the writer separates the constant (``car_term``). The membership line
    carries that token."""
    text, name_map = write(["Car(car:S)"], "Car(car:S)")
    assert name_map.term == {"car": "car_term"}
    assert "fof(sort_member_1, axiom, s(car_term))." in lines_of(text)
    assert "fof(premise_1, axiom, car(car_term))." in lines_of(text)


def test_a_problem_without_a_sorted_constant_is_written_as_before():
    """Nothing but the existing lines: sorted quantifiers give the non-emptiness line,
    and an UNSORTED constant (``socrates``) is not asserted to be anything."""
    text, _ = write(["∀x:Human Mortal(x)"], "Mortal(socrates)")
    assert lines_of(text) == [
        "fof(premise_1, axiom, (![X]: (human(X) => mortal(X)))).",
        "fof(nonempty_sort_1, axiom, (?[X0]: human(X0))).",
        "fof(goal, conjecture, mortal(socrates)).",
    ]
    plain, _ = write(["∀x (Human(x) → Mortal(x))", "Human(socrates)"], "Mortal(socrates)")
    assert lines_of(plain) == [
        "fof(premise_1, axiom, (![X]: (human(X) => mortal(X)))).",
        "fof(premise_2, axiom, human(socrates)).",
        "fof(goal, conjecture, mortal(socrates)).",
    ]


@pytest.mark.parametrize("premises, conclusion, members", [
    (["∀x:Human Mortal(x)"], "Mortal(human:Human)", {"human"}),
    (["∀x:Human Mortal(x)"], "Mortal(sókrates:Human)", {"sókrates"}),
    (["∀x:Cat Mortal(x)"], "Mortal(9lives:Cat)", {"9lives"}),
    (["P(carl:A)", "Q(carl:B)"], "∃x:A Q(x)", {"carl"}),
    (["Car(car:S)"], "Car(car:S)", {"car"}),
])
def test_the_name_map_covers_every_constant_the_membership_lines_write(premises, conclusion, members):
    """Every constant token of a ``sort_member_<i>`` line is a token of the map, and the
    reverse map gives back the kit's name of the sorted constant (so a prover's proof that
    uses the line is read back in the caller's names)."""
    text, name_map = write(premises, conclusion)
    _, term_reverse = name_map.reverse()
    written = set()
    for line in lines_of(text):
        found = re.fullmatch(r"fof\(sort_member_\d+, axiom, (\w+)\((\w+)\)\)\.", line)
        if found:
            token = found.group(2)
            assert token in term_reverse, (line, name_map)
            written.add(term_reverse[token])
    assert written == members


# =============================================================================
# The text, against provers (Vampire and E), answers worked out by hand
# =============================================================================

def _wsl_vampire_ok() -> bool:
    try:
        result = subprocess.run(["wsl.exe", "vampire", "--version"],
                                capture_output=True, text=True, timeout=20)
        return result.returncode == 0 and "Vampire" in result.stdout
    except Exception:  # noqa: BLE001 -- any failure means "not available"
        return False


_VAMPIRE = shutil.which("vampire")
_WSL_VAMPIRE = _wsl_vampire_ok()
_HAVE_VAMPIRE = _VAMPIRE is not None or _WSL_VAMPIRE
_vampire = dict(vampire_path=_VAMPIRE, use_wsl=False) if _VAMPIRE else dict(vampire_path="vampire", use_wsl=True)

#: (premises, conclusion, entailed?, why) -- the fof text must give this answer. By hand:
_ENTAILMENT = [
    (["∀x:Human Mortal(x)"], "Mortal(socrates:Human)", True,
     "socrates is a Human, every Human is Mortal"),
    (["∀x:Human Mortal(x)"], "Mortal(human:Human)", True,
     "the same with a constant named like its sort (written human_term)"),
    (["∀x:Human Mortal(x)"], "Mortal(sókrates:Human)", True,
     "the same with a non-ASCII constant"),
    (["∀x:Cat Mortal(x)"], "Mortal(9lives:Cat)", True,
     "the same with a digit-leading constant"),
    (["P(carl:A)", "Q(carl:B)"], "∃x:A Q(x)", True,
     "carl is in A and Q(carl): a constant with two sorts is in both"),
    (["P(carl)", "Q(carl:A)"], "∃x:A P(x)", True,
     "carl is ONE constant, and the sorted occurrence puts it in A"),
    ([], "∃x:Human x = socrates:Human", True, "socrates is in Human and equals itself"),
    (["∀x:Human Mortal(x)"], "Mortal(socrates)", False,
     "an UNSORTED constant is no Human: U={0,1}, Human={0}, Mortal={0}, socrates=1"),
    ([], "Mortal(socrates:Human)", False,
     "nothing is known of a sorted constant: U={0}, Human={0}, Mortal={}, socrates=0"),
    ([], "anna:S = bert:S", False,
     "two sorted constants of one sort need not be equal: U={0,1}, S={0,1}"),
]


@pytest.mark.skipif(not _HAVE_VAMPIRE, reason="no Vampire binary reachable (native or WSL)")
@pytest.mark.parametrize("premises, conclusion, entailed, why", _ENTAILMENT)
def test_vampire_answers_the_fof_text_as_the_definition_says(premises, conclusion, entailed, why):
    result = check_entailment_vampire_detailed(
        [parse(t) for t in premises], parse(conclusion), timeout=60, tff=False, **_vampire)
    assert result["dialect"] == "fof"
    assert result["status"] == ("proved" if entailed else "refuted"), (why, result["szs_status"])


@pytest.mark.skipif(not eprover_available(), reason="no eprover binary found")
@pytest.mark.parametrize("premises, conclusion, entailed, why", _ENTAILMENT)
def test_eprover_answers_the_fof_text_as_the_definition_says(premises, conclusion, entailed, why):
    result = check_entailment_eprover_detailed(
        [parse(t) for t in premises], parse(conclusion), tff=False, timeout=30)
    assert result["status"] == ("proved" if entailed else "refuted"), (why, result["szs_status"])


@pytest.mark.skipif(not _HAVE_VAMPIRE, reason="no Vampire binary reachable (native or WSL)")
def test_vampire_finds_the_fof_text_without_a_conjecture_unsatisfiable_through_the_membership_line():
    """∀x:Foo R(x) and ¬R(kay:Foo) have no model: kay is a Foo, so R(kay). The problem has
    NO conjecture, so Vampire answers about the premises themselves. Without the
    membership line it is Satisfiable (kay outside Foo)."""
    text, _ = write(["∀x:Foo R(x)", "¬R(kay:Foo)"], None)
    out, timed_out = _spawn_vampire(text, _vampire["vampire_path"], timeout=60,
                                    use_wsl=_vampire["use_wsl"])
    assert not timed_out
    assert extract_szs_status(out) in ("Unsatisfiable", "ContradictoryAxioms"), out[-400:]
    without_line = "\n".join(ln for ln in text.splitlines() if "sort_member_" not in ln) + "\n"
    out, timed_out = _spawn_vampire(without_line, _vampire["vampire_path"], timeout=60,
                                    use_wsl=_vampire["use_wsl"])
    assert extract_szs_status(out) == "Satisfiable", out[-400:]
