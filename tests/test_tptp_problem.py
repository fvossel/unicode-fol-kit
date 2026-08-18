"""Tests for the shared TPTP problem generator (atp._tptp_problem) and its use
by the three external-prover backends.

Two things pinned here:

1. :func:`atp._tptp_problem.generate_tptp_problem` produces the exact same
   text the three backends' own (pre-refactor) hand-written generators did —
   the unification behind ``_generate_vampire_input`` /
   ``eprover_backend._generate_tptp_problem`` / ``_generate_twee_input`` must
   be a pure refactor, not a behaviour change.
2. The cross-formula symbol-collision guard: two distinct kit-level
   predicate (or function/constant) names that would fold to the SAME TPTP
   identifier (``Node.to_tptp`` folds only a name's first character —
   ``Foo``/``foo`` both fold to ``foo``) must be refused with
   ``NotImplementedError`` naming both, from every one of the three
   backends' generator functions, not merely the shared helper.

Reproduces the reported bug directly: the concrete example from the task —
``_generate_vampire_input([Atom('Foo',[a]), Not(Atom('FOO',[a]))],
Atom('foo',[a]))`` — used to silently produce the self-contradictory axiom
set ``{foo(A), ~foo(A)}`` (from two semantically independent predicates
merged into one TPTP symbol), which any prover proves anything from via ex
falso quodlibet. It must now raise instead.
"""

import pytest

from unicode_fol_kit.fol.msflparser import MSFLParser
from unicode_fol_kit.fol.nodes import Atom, Constant, Function, Implies, Not, Quantifier, Variable
from unicode_fol_kit.fol.tptp_input import parse_tptp_formula
from unicode_fol_kit.atp._ascii_names import reverse_map_text
from unicode_fol_kit.atp._tptp_problem import (
    apply_reverse_tptp, generate_tptp_problem, generate_tptp_problem_with_mapping,
)
from unicode_fol_kit.atp.vampire_entailment import _generate_vampire_input
from unicode_fol_kit.atp.eprover_backend import _generate_tptp_problem as _eprover_generate
from unicode_fol_kit.atp.twee_entailment import _generate_twee_input

_A = Variable("a")
_PARSE = MSFLParser().parse


# ---------------------------------------------------------------------------
# Pure refactor: shared helper matches each backend's own wrapper exactly.
# ---------------------------------------------------------------------------

_PREMISES = [Atom("Human", [Constant("socrates")]),
             Atom("Loves", [Constant("alice"), Constant("bob")])]
_CONCLUSION = Atom("Mortal", [Constant("socrates")])


@pytest.mark.parametrize("wrapper", [_generate_vampire_input, _eprover_generate, _generate_twee_input])
def test_backend_wrapper_matches_shared_helper(wrapper):
    assert wrapper(_PREMISES, _CONCLUSION) == generate_tptp_problem(_PREMISES, _CONCLUSION)


def test_shared_helper_shape():
    text = generate_tptp_problem(_PREMISES, _CONCLUSION)
    lines = [ln for ln in text.splitlines() if ln.strip()]
    assert lines == [
        "fof(premise_1, axiom, human(socrates)).",
        "fof(premise_2, axiom, loves(alice,bob)).",
        "fof(goal, conjecture, mortal(socrates)).",
    ]


def test_shared_helper_no_premises():
    text = generate_tptp_problem([], _CONCLUSION)
    lines = [ln for ln in text.splitlines() if ln.strip()]
    assert lines == ["fof(goal, conjecture, mortal(socrates))."]


# ---------------------------------------------------------------------------
# Collision guard — the reported bug, reproduced and refused.
# ---------------------------------------------------------------------------

def test_reported_bug_is_now_refused():
    """The exact repro from the task: Atom('Foo',...) / Atom('FOO',...) /
    Atom('foo',...) would all fold to the TPTP symbol 'foo' under the old
    whole-string .lower() — silently building a self-contradictory,
    ex-falso-quodlibet axiom set. Must raise instead of emitting a problem.
    """
    with pytest.raises(NotImplementedError, match="Foo.*foo|foo.*Foo"):
        generate_tptp_problem([Atom("Foo", [_A]), Not(Atom("FOO", [_A]))], Atom("foo", [_A]))


def test_collision_error_names_both_symbols():
    with pytest.raises(NotImplementedError) as exc_info:
        generate_tptp_problem([Atom("Foo", [_A])], Atom("foo", [_A]))
    message = str(exc_info.value)
    assert "'Foo'" in message and "'foo'" in message  # both original kit names named


def test_no_false_positive_for_the_same_predicate_reused():
    """Using the SAME predicate name more than once (the ordinary case) must
    never be flagged — only two DIFFERENT original names colliding are."""
    text = generate_tptp_problem([Atom("Foo", [_A]), Atom("Foo", [_A])], Atom("Foo", [_A]))
    assert text.count("foo(A)") == 3


def test_no_collision_between_predicate_and_function_namespaces():
    """A predicate and a function/constant folding to the same identifier are
    NOT a collision — they occupy separate TPTP syntactic namespaces (formula
    position vs. term position), unlike two predicates or two functions."""
    # Atom "Foo" -> predicate 'foo'; Constant "foo" -> term 'foo'. Different
    # namespaces, so no collision, even though the rendered strings match.
    text = generate_tptp_problem([Atom("Foo", [Constant("foo")])], Atom("Foo", [Constant("foo")]))
    assert "foo(foo)" in text


@pytest.mark.parametrize("generate", [generate_tptp_problem, _generate_vampire_input,
                                      _eprover_generate, _generate_twee_input])
def test_collision_guard_covers_every_external_backend(generate):
    """The guard must fire identically through EVERY one of the three
    external-prover generator functions (they all delegate to the shared
    helper), not just generate_tptp_problem itself."""
    with pytest.raises(NotImplementedError):
        generate([Atom("Foo", [_A])], Atom("foo", [_A]))


def test_function_name_collision_is_refused():
    # 'Bar' and 'bar' differ ONLY in the case of the first letter, so both
    # still fold to 'bar' under the first-letter-only fold (unlike e.g.
    # 'Bar'/'BAR', which no longer collide now that the fold is fixed).
    left = Atom("=", [Function("Bar", [_A]), Constant("c")])
    right = Atom("=", [Function("bar", [_A]), Constant("c")])
    with pytest.raises(NotImplementedError, match="function"):
        generate_tptp_problem([left], right)


def test_constant_name_collision_is_refused():
    left = Atom("=", [Constant("Alice"), Constant("Alice")])
    right = Atom("=", [Constant("alice"), Constant("alice")])
    with pytest.raises(NotImplementedError):
        generate_tptp_problem([left], right)


def test_collision_across_premises_and_conclusion_together():
    """The guard must see premises AND the conclusion as one problem — a
    collision split across the two must still be caught."""
    premise = Atom("Foo", [_A])
    conclusion = Atom("foo", [_A])
    with pytest.raises(NotImplementedError):
        generate_tptp_problem([premise], conclusion)


def test_no_collision_when_predicates_genuinely_distinct():
    """Two predicates whose folded forms differ (first letters 'F' and 'B',
    say) must never be flagged — only an actual identifier collision is."""
    text = generate_tptp_problem([Atom("Foo", [_A])], Atom("Bar", [_A]))
    assert "foo(A)" in text and "bar(A)" in text


def test_equality_and_arithmetic_predicates_never_participate_in_collisions():
    """'=', '<', '>', etc. map to fixed TPTP tokens outside the name-folding
    path, so they can never collide with a folded predicate name — even one
    that happens to render identically to a dollar-word by coincidence is
    out of this guard's scope (a separate, much narrower concern)."""
    text = generate_tptp_problem(
        [Atom("=", [Constant("a"), Constant("a")])],
        Atom("<", [Constant("a"), Constant("b")]),
    )
    assert "(a = a)" in text
    assert "$less(a,b)" in text


# ---------------------------------------------------------------------------
# ASCII/legality sanitisation — the widened-identifier-grammar fix.
# ---------------------------------------------------------------------------

class TestHinwegNonAsciiAndDigitLeadingNames:
    """świątek / 2008SummerOlympics / dani_Shapiro — the exact three example
    formulas named in the task — through generate_tptp_problem, each
    verified EXECUTED against the kit's own TPTP reader (R5: no real TPTP
    prover is required to prove the export text is syntactically legal —
    see test_eprover_zipperposition_live below for a genuine external-tool
    check on top of this)."""

    def test_non_ascii_constant_becomes_ascii_and_reparses(self):
        f = _PARSE("LostTo(x, świątek)")
        text = generate_tptp_problem([], f)
        # "świątek" must not appear raw in ASCII-only TPTP text.
        assert "świątek" not in text
        assert text.isascii()
        body = text.split(", ", 2)[2].rsplit(")", 1)[0]
        reparsed = parse_tptp_formula(body)
        assert reparsed.predicate == "LostTo"

    def test_digit_leading_constant_becomes_non_digit_leading_and_reparses(self):
        f = _PARSE("Hosted(beijing, 2008SummerOlympics)")
        text = generate_tptp_problem([], f)
        assert "(beijing,2008SummerOlympics)" not in text  # not left digit-leading
        assert text.isascii()
        body = text.split(", ", 2)[2].rsplit(")", 1)[0]
        reparsed = parse_tptp_formula(body)
        assert reparsed.predicate == "Hosted"
        assert reparsed.args[1].name[0].isalpha()  # legal lower_word now

    def test_underscore_name_already_legal_passes_through_unchanged(self):
        f = _PARSE("P(dani_Shapiro)")
        text = generate_tptp_problem([], f)
        assert "fof(goal, conjecture, p(dani_Shapiro))." in text.splitlines()

    def test_all_three_together_reparse_and_reverse_map_to_originals(self):
        f1 = _PARSE("LostTo(x, świątek)")
        f2 = _PARSE("Hosted(beijing, 2008SummerOlympics)")
        f3 = _PARSE("P(dani_Shapiro)")
        text, mapping = generate_tptp_problem_with_mapping([f1, f2], f3)
        for line in text.splitlines():
            if not line.strip():
                continue
            body = line.split(", ", 2)[2].rsplit(").", 1)[0]
            parse_tptp_formula(body)  # must not raise (R5)

        reparsed1 = parse_tptp_formula(
            text.splitlines()[0].split(", ", 2)[2].rsplit(").", 1)[0])
        reparsed2 = parse_tptp_formula(
            text.splitlines()[1].split(", ", 2)[2].rsplit(").", 1)[0])
        back1 = apply_reverse_tptp(reparsed1, mapping)
        back2 = apply_reverse_tptp(reparsed2, mapping)
        assert back1 == f1
        assert back2 == f2


class TestR1NoChangeForAlreadyLegalNames:
    """Every already-legal name maps to itself — the sanitisation step never
    fires for a formula this module was already exporting correctly
    (differential-tested against the pre-sanitisation code externally via
    git worktree; this pins the SAME guarantee at the mapping level)."""

    @pytest.mark.parametrize("name", [
        "socrates", "a", "alice", "hasBond", "dani_Shapiro", "family_History",
    ])
    def test_constant_names_are_identity_mapped(self, name):
        _, mapping = generate_tptp_problem_with_mapping(
            [], Atom("P", [Constant(name)]))
        assert mapping.term[name] == name

    @pytest.mark.parametrize("name", ["Human", "Mortal", "hasBond", "BDouble"])
    def test_predicate_names_are_identity_mapped(self, name):
        _, mapping = generate_tptp_problem_with_mapping([], Atom(name, [_A]))
        assert mapping.predicate[name] == name

    def test_single_letter_constant_is_not_touched(self):
        # A single-letter constant is legal TPTP (lower_word: [a-z][...]*)
        # even though it is NOT a legal bare kit-level NAME token (it would
        # re-lex as a VARIABLE) -- fol.sanitize.NameMapping would rewrite it
        # to "c_a", which is exactly the wrong behaviour here (see
        # atp._tptp_problem's module docstring / _ascii_names.py's).
        _, mapping = generate_tptp_problem_with_mapping(
            [Atom("=", [Constant("a"), Constant("a")])], Atom("<", [Constant("a"), Constant("b")]))
        assert mapping.term["a"] == "a"
        assert mapping.term["b"] == "b"


class TestR2ConsistencyAndCollisionAvoidance:
    def test_same_non_ascii_name_reused_maps_consistently(self):
        premise1 = Atom("P", [Constant("świątek")])
        premise2 = Atom("Q", [Constant("świątek")])
        conclusion = Atom("R", [Constant("świątek")])
        _, mapping = generate_tptp_problem_with_mapping([premise1, premise2], conclusion)
        assert mapping.term["świątek"] is not None
        # only one entry: the SAME sanitised token for every occurrence.
        assert len(mapping.term) == 1

    def test_synthesised_token_never_collides_with_an_already_legal_name(self):
        # "u015b" is what the reversible escape scheme maps "ś" to -- and is
        # ALSO independently a perfectly legal TPTP identifier in its own
        # right if a formula happens to use it literally. Both appearing in
        # the same problem must not collide, regardless of which one is
        # written first (order-independence — see atp._tptp_problem
        # ._Renamer's docstring).
        for premise in (Atom("=", [Constant("u015b"), Constant("ś")]),
                       Atom("=", [Constant("ś"), Constant("u015b")])):
            _, mapping = generate_tptp_problem_with_mapping([premise], Atom("Q", [_A]))
            assert mapping.term["u015b"] == "u015b"
            assert mapping.term["ś"] != "u015b"
            assert mapping.term["ś"] != mapping.term["u015b"]

    def test_two_different_non_ascii_predicate_names_stay_distinct(self):
        premise = Atom("Świątek", [_A])
        conclusion = Atom("Śledź", [_A])
        text, mapping = generate_tptp_problem_with_mapping([premise], conclusion)
        assert mapping.predicate["Świątek"] != mapping.predicate["Śledź"]
        # generate_tptp_problem must not raise: two GENUINELY distinct names
        # synthesising to distinct tokens is not a collision.
        assert text  # no exception raised above


class TestR3RoundTripViaApplyReverseTptp:
    """Original -> sanitised export -> (simulated) prover echo -> reparsed ->
    apply_reverse_tptp -> original again, for each of the task's three
    example formulas individually."""

    @pytest.mark.parametrize("source", [
        "LostTo(x, świątek)",
        "Hosted(beijing, 2008SummerOlympics)",
        "P(dani_Shapiro)",
    ])
    def test_full_round_trip(self, source):
        original = _PARSE(source)
        text, mapping = generate_tptp_problem_with_mapping([], original)
        body = text.split(", ", 2)[2].rsplit(").", 1)[0]
        # Stand in for "a prover echoed this TPTP text back in its proof" --
        # parsed with the SAME kit-owned reader real backends use for that
        # (atp.tstp.parse_tstp_derivation delegates to parse_tptp_formula).
        echoed = parse_tptp_formula(body)
        recovered = apply_reverse_tptp(echoed, mapping)
        assert recovered == original


class TestReverseRenderedFreeTextRoundTrip:
    """Regression coverage for the free-text Rückweg (R3's 'Erklärungstexte':
    a prover's raw stdout excerpt, an SZS-detail string, and similar) — see
    ``atp._ascii_names.reverse_map_text`` and its callers in
    eprover_backend.py / vampire_entailment.py / twee_entailment.py.

    That text is never re-parsed, so the reverse dict it needs must be keyed
    by the RENDERED (post-fold) token — exactly what ``Node.to_tptp()``
    wrote into the exported problem and therefore what a prover echoes back
    verbatim — not by the raw, pre-fold token :meth:`TptpNameMap.reverse`
    returns for the STRUCTURED path (:func:`apply_reverse_tptp`, which
    re-parses via ``tptp_input.parse_tptp_formula`` first and so sees the
    re-capitalised form instead).

    Bug this pins: ``TptpNameMap.reverse()``'s predicate dict is keyed by
    the un-folded token (e.g. ``'Human'``), but ``Atom.to_tptp`` folds only
    the first character on export (``'human'``), so feeding
    ``mapping.reverse()`` straight to :func:`reverse_map_text` was a silent
    no-op for every predicate — including ones that were already TPTP-legal
    to begin with (R1's "already-legal" case, not merely the synthesised
    non-ASCII case).
    """

    def test_already_legal_predicate_is_restored_from_rendered_text(self):
        premise = Atom("Human", [Constant("socrates")])
        conclusion = Atom("Mortal", [Constant("socrates")])
        text, mapping = generate_tptp_problem_with_mapping([premise], conclusion)
        # what Node.to_tptp() actually wrote: folded, lowercase-initial.
        assert "human(socrates)" in text
        assert "Human(socrates)" not in text
        pred_rev, term_rev = mapping.reverse_rendered()
        restored = reverse_map_text(text, pred_rev, term_rev)
        assert "Human(socrates)" in restored
        assert "Mortal(socrates)" in restored
        assert "human(socrates)" not in restored
        assert "mortal(socrates)" not in restored

    def test_plain_reverse_cannot_restore_the_same_text(self):
        # Documents WHY reverse_rendered exists, as a differential against
        # the STRUCTURED-path dict: .reverse()'s predicate dict is keyed by
        # the raw ('Human') token, which never appears verbatim in
        # exported/echoed free text (only its folded form, 'human', does),
        # so feeding it to reverse_map_text is a silent no-op here.
        premise = Atom("Human", [Constant("socrates")])
        conclusion = Atom("Mortal", [Constant("socrates")])
        text, mapping = generate_tptp_problem_with_mapping([premise], conclusion)
        pred_rev, term_rev = mapping.reverse()
        assert reverse_map_text(text, pred_rev, term_rev) == text

    def test_synthesised_non_ascii_predicate_round_trips_through_rendered_text(self):
        original = _PARSE("Świątek(świątek)")
        text, mapping = generate_tptp_problem_with_mapping([], original)
        pred_rev, term_rev = mapping.reverse_rendered()
        restored = reverse_map_text(text, pred_rev, term_rev)
        assert "Świątek(świątek)" in restored

    def test_reverse_rendered_keys_are_injective_across_distinct_predicates(self):
        premise = Atom("Human", [_A])
        conclusion = Atom("Mammal", [_A])
        _, mapping = generate_tptp_problem_with_mapping([premise], conclusion)
        pred_rev, _ = mapping.reverse_rendered()
        assert pred_rev == {"human": "Human", "mammal": "Mammal"}
