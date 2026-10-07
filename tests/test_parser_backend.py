"""Which parser serves which mode, and why the swap is allowed to be invisible.

Up to 0.23.1 every mode was parsed with Earley. Earley is the right default for
a grammar that needs it; this one does not. Asked for every derivation
(``ambiguity="explicit"``), the classical grammar produces exactly one for all
1260 parsable lines of the 1310-line FOLIO fixture, so Earley was paying for a capability the grammar
never used -- measured at 30x to 50x, mode by mode, on the kit's own corpus.

Since 0.23.2 every mode is parsed with LALR as its FAST path. Two modes,
``modal`` and ``tomodal`` (``_HYBRID_MODES``), cannot move to LALR outright --
a genuine LALR(1) reduce/reduce conflict (documented at ``_HYBRID_MODES`` in
msflparser.py) makes plain LALR silently commit to the wrong reading for one
narrow shape (a bracket-grouped formula headed by a bare lowercase
NAME/VARIABLE) and then fail a few tokens later. Since 0.28.0 those two modes
get an LALR-first, EARLEY-FALLBACK wrapper instead of plain Earley:
``MSFLParser`` tries its LALR parser first and retries with Earley,
transparently, only on the rare input that shape describes -- see
``MSFLParser._parse_tree``. This module is the evidence that none of this
changes anything a caller can observe: every test below now runs against
every mode, hybrid ones included, checked against a live Earley parser built
from the same grammar rather than against recorded strings, so it keeps
testing the real question if the grammar changes. The soundness half of the
hybrid wrapper -- that wherever its LALR fast path itself accepts, it builds
the SAME tree Earley would -- gets its own dedicated (much larger, randomly
generated) corpus in tests/test_modal_lalr_fallback.py; this file's job is
the accept/reject/span/error-message differential, run the same way for
every mode.

The one thing the swap DOES change is where a failure surfaces. Earley's
dynamic lexer only offers tokens the parser can currently use, so a well-formed
symbol in the wrong place never became a token -- it stayed an unscannable
character, and the kit reported a NamingError. LALR tokenises first and refuses
afterwards, so the same input arrives as UnexpectedToken. The mapping back
(`MSFLParser._token_failure`) was derived by measuring both parsers over the
corpus, and the split turned out to be exact rather than approximate: every
input Earley failed with UnexpectedEOF becomes UnexpectedToken on `$END`, and
every input it failed with UnexpectedCharacters becomes UnexpectedToken on
something else. Both directions are pinned below. A hybrid mode's fallback
-exhausted failure (both LALR and Earley refuse) is reported through Earley's
OWN untranslated exception instead -- see MSFLParser._token_failure's
``_from_earley_fallback`` branch -- so it needs no separate mapping here.
"""

from pathlib import Path

import pytest

from lark import Lark

from unicode_logic_kit import MSFLParser
from unicode_logic_kit.fol._fol_nodes import build_grammar
from unicode_logic_kit.fol.msflparser import (
    _allow_single_letter_function_calls, _GRAMMARS_DIR,
    _HYBRID_MODES, _REGISTRY_MODE)
from unicode_logic_kit.fol.naming import NamingError, ParsingError

MODES = {
    "fol": {}, "msfol": {"many_sorted": True},
    "msfl": {"many_sorted": True, "fuzzy": True}, "fl": {"fuzzy": True},
    "so": {"second_order": True}, "dependence": {"dependence": True},
    "linear": {"linear": True}, "lambek": {"lambek": True},
    "modal": {"modal": True},
    "modal_sorted": {"modal": True, "many_sorted": True},
    "so_sorted": {"second_order": True, "many_sorted": True},
    "to": {"third_order": True},
    "tomodal": {"third_order": True, "modal": True},
}

FOLIO = [l.strip() for l in
         (Path("tests/fixtures/folio_fol_strings.txt")
          .read_text(encoding="utf-8").splitlines()) if l.strip()]
# NOT read here: tests/fixtures/folio_fol_strings_nonparsable.txt. It looks
# like a corpus and is not one -- its rows are `lineno<TAB>ErrorClass<TAB>
# message` records ABOUT lines of folio_fol_strings.txt, plus a `#` header.
# An earlier version of this file fed those 53 rows in as if they were
# formulas, which put 53 pieces of tab-separated prose into every differential
# below and inflated every count derived from them. The formulas those rows
# describe are already in FOLIO; the artifact adds nothing but noise.

# Shapes chosen so both failure branches are exercised: the first four end
# early ($END), the rest fail on a token that is fine elsewhere.
MALFORMED = ["∀x", "P(", "∀x (P(x)", "P(x) ∧",
             "P(x) ∧ Q(x) ∨ R(x)", "→ P(x)", "P(x) Q(x)", "Human$(x)"]


def _earley_reference(mode):
    """The parser the kit used before 0.23.2, from the same grammar source."""
    grammar = _allow_single_letter_function_calls(
        build_grammar(_REGISTRY_MODE[mode]))
    return Lark(grammar, parser="earley", import_paths=[str(_GRAMMARS_DIR)],
                propagate_positions=True)


# --- which parser serves which mode -----------------------------------------

@pytest.mark.parametrize("mode, kwargs", sorted(MODES.items()))
def test_each_mode_uses_lalr_as_its_fast_path(mode, kwargs):
    """Every mode's PRIMARY (``.parser``) build is LALR now -- see
    _HYBRID_MODES for the two that ALSO carry an Earley fallback, checked
    separately below."""
    assert MSFLParser(**kwargs).parser.options.parser == "lalr"


@pytest.mark.parametrize("mode, kwargs",
                         sorted((m, k) for m, k in MODES.items() if m in _HYBRID_MODES))
def test_hybrid_modes_also_build_an_earley_fallback(mode, kwargs):
    kit = MSFLParser(**kwargs)
    assert kit._earley_parser is not None
    assert kit._earley_parser.options.parser == "earley"


@pytest.mark.parametrize("mode, kwargs",
                         sorted((m, k) for m, k in MODES.items() if m not in _HYBRID_MODES))
def test_non_hybrid_modes_build_no_earley_fallback(mode, kwargs):
    assert MSFLParser(**kwargs)._earley_parser is None


def test_modal_is_the_only_holdout_and_it_is_deliberate():
    """Earley is kept as a FALLBACK for the modal LANGUAGE, not for two
    unrelated modes.

    ``tomodal`` is on the list only because it is the modal operator set
    over a widened argument layer -- it inherits the language, so it
    inherits the reason. ``modal_sorted`` joined it for the same reason:
    it is the modal operator set over sorted quantifiers, i.e. the same
    LANGUAGE again, so the bare lowercase atoms and nominals below are
    exactly as unreachable for its LALR table. If this ever shrinks to
    nothing, the mode moved and the comment in msflparser.py explaining why
    it could not needs deleting with it; if it ever GROWS to a mode that
    does not carry the modal operators, that is a new claim and needs its
    own evidence -- which is what the second assertion below is for.

    ``so_sorted`` is deliberately NOT here: sorted quantification over the
    second-order language stays pure LALR, so adding sorts to a mode is not
    by itself a reason to keep a fallback."""
    assert _HYBRID_MODES == frozenset({"modal", "modal_sorted", "tomodal"})
    assert all(MODES[m].get("modal") for m in _HYBRID_MODES)
    assert MSFLParser(**MODES["so_sorted"])._earley_parser is None


def test_modal_still_accepts_what_only_earley_reaches():
    """The reason modal keeps an Earley FALLBACK: these are legal modal
    formulas that the LALR table alone refuses. Bare lowercase propositional
    atoms and nominals standing as whole formulas -- moving the mode to plain
    LALR would silently narrow the language, which is not a speedup. This now
    exercises the real LALR-first/Earley-fallback wrapper end to end (see
    tests/test_modal_lalr_fallback.py for the much larger corpus proving the
    fallback path is sound, not just that it fires)."""
    parser = MSFLParser(modal=True)
    for text in ["p→(q→p)", "¬(p∧q)→(¬p∨¬q)", "@i (P ∧ ◇j)", "¬¬(p∨¬p)"]:
        assert parser.parse(text) is not None, text


# --- the swap must be invisible: trees, spans, accept/reject ----------------

@pytest.mark.parametrize("mode", sorted(MODES))
def test_trees_and_acceptance_match_earley(mode):
    """Compares against ``MSFLParser._parse_tree`` rather than the raw
    ``.parser`` Lark object: for the 9 plain-LALR modes that is exactly
    ``.parser.parse`` (no behaviour change from before), and for the 2 hybrid
    modes it is the ACTUAL LALR-first/Earley-fallback lookup ``parse()``
    itself uses -- so this differential now also covers the hybrid wrapper's
    accept/reject set and tree shape, not just the plain-LALR modes'."""
    kit = MSFLParser(**MODES[mode])
    earley = _earley_reference(mode)
    checked = 0
    mismatches = []
    for text in FOLIO + MALFORMED:
        try:
            expected = ("ok", earley.parse(text))
        except Exception as exc:                  # noqa: BLE001 - compared
            expected = ("err", type(exc).__name__)
        try:
            actual = ("ok", kit._parse_tree(text))
        except Exception as exc:                  # noqa: BLE001 - compared
            actual = ("err", type(exc).__name__)
        checked += 1
        if expected[0] != actual[0] or (expected[0] == "ok"
                                        and expected[1] != actual[1]):
            mismatches.append((text[:70], expected[0], actual[0]))
    assert checked > 1300, checked
    assert not mismatches, mismatches[:5]


def _spans(tree):
    """Everything SpanMap can read: subtree meta plus token offsets."""
    out = []
    for node in tree.iter_subtrees():
        meta = node.meta
        out.append((node.data, getattr(meta, "empty", True),
                    getattr(meta, "start_pos", None),
                    getattr(meta, "end_pos", None)))
        for child in node.children:
            if hasattr(child, "start_pos"):
                out.append((child.type, str(child),
                            child.start_pos, child.end_pos))
    return out


@pytest.mark.parametrize("mode", sorted(MODES))
def test_source_spans_match_earley(mode):
    """lark's ``Tree.__eq__`` compares data and children and IGNORES ``meta``,
    so tree equality above says nothing about spans -- and ``parse_with_spans``
    reads exactly that meta. Checked separately for that reason. As above,
    ``_parse_tree`` makes this cover the hybrid modes' Earley fallback too."""
    kit = MSFLParser(**MODES[mode])
    earley = _earley_reference(mode)
    checked = differing = 0
    for text in FOLIO + MALFORMED:
        try:
            a = earley.parse(text)
            b = kit._parse_tree(text)
        except Exception:                          # noqa: BLE001
            continue
        checked += 1
        if _spans(a) != _spans(b):
            differing += 1
    # FOLIO is classical unsorted FOL, so the sorted modes accept only a
    # handful of it -- a fixed "> 200" here would have been a threshold that
    # happens to hold for fol and silently fails the modes it does not fit,
    # which is how a corpus assertion turns into noise. The floor is that the
    # comparison ran at all; test_the_span_corpus_is_large_where_it_can_be
    # below carries the "and it is a real corpus somewhere" half.
    assert checked > 0, f"{mode}: nothing to compare"
    assert differing == 0, f"{mode}: {differing} of {checked} spans differ"


def test_the_span_corpus_is_large_where_it_can_be():
    """Guard for the test above: in the mode FOLIO is written in, the span
    comparison really does run over the whole corpus rather than a handful."""
    earley = _earley_reference("fol")
    accepted = 0
    for text in FOLIO:
        try:
            earley.parse(text)
            accepted += 1
        except Exception:                          # noqa: BLE001
            pass
    assert accepted > 1000, accepted


def test_parse_with_spans_still_points_at_the_source():
    """End-to-end rather than through lark: the public span API keeps working
    on an LALR-backed parser."""
    text = "∀x (Human(x) → Mortal(x))"
    spanned = MSFLParser().parse_with_spans(text)
    assert spanned.formula == MSFLParser().parse(text)
    covered = set()
    for _path, node_spans in spanned.spans.items():
        span = node_spans.extent
        if span:
            covered.add(text[span.start:span.end])
    assert "Human(x)" in covered, sorted(covered)
    assert "Mortal(x)" in covered, sorted(covered)


# --- the error model survives ----------------------------------------------

def test_error_classes_match_earley_on_every_rejected_formula():
    """The measured mapping, as an assertion. Class only -- the message text
    is checked separately, because the two questions fail for different
    reasons and a combined test would not say which."""
    kit = MSFLParser()
    earley = _earley_reference("fol")
    from lark import UnexpectedCharacters, UnexpectedEOF, UnexpectedToken

    rejected = 0
    mismatches = []
    for text in FOLIO + MALFORMED:
        try:
            earley.parse(text)
            continue
        except UnexpectedCharacters:
            want = NamingError
        except (UnexpectedToken, UnexpectedEOF):
            want = ParsingError
        rejected += 1
        with pytest.raises((NamingError, ParsingError)) as excinfo:
            kit.parse(text)
        if not isinstance(excinfo.value, want):
            mismatches.append((text[:70], want.__name__,
                               type(excinfo.value).__name__))
    assert rejected > 50, f"only {rejected} rejected formulas -- probe too weak"
    assert not mismatches, mismatches[:5]


@pytest.mark.parametrize("text, expected, fragment", [
    ("∀x", ParsingError, "Incomplete formula"),
    ("P(", ParsingError, "Incomplete formula"),
    ("∀x (P(x)", ParsingError, "Incomplete formula"),
    ("Human$(x)", NamingError, "Invalid predicate 'Human'"),
    ("→ P(x)", NamingError, "Unexpected character '→' at position 1"),
])
def test_both_branches_of_the_token_failure_mapping(text, expected, fragment):
    """`$END` is the whole rule for "the formula ended too early"; every other
    unshiftable token is a character in the wrong place."""
    with pytest.raises(expected) as excinfo:
        MSFLParser().parse(text)
    assert fragment in str(excinfo.value)


def test_the_no_mixing_hint_survives_the_swap():
    """The hint is the reason the no-mixing rule is actionable rather than
    merely a refusal, and it lives on the NamingError branch -- the branch that
    would have been lost by routing every UnexpectedToken to ParsingError."""
    with pytest.raises(NamingError) as excinfo:
        MSFLParser().parse("P(x) ∧ Q(x) ∨ R(x)")
    message = str(excinfo.value)
    assert "Cannot mix conjunction" in message
    assert "after closing parenthesis ')'" in message


def test_message_text_matches_earley_except_for_narrower_expectations():
    """No error changes class, and most messages are byte-identical. The rest
    differ in one way only: LALR knows exactly which tokens could continue the formula, so its
    "Expected:" list is a subset of Earley's. Anything else is a regression.
    """
    from lark import UnexpectedCharacters, UnexpectedEOF, UnexpectedToken

    kit = MSFLParser()
    earley = _earley_reference("fol")
    identical = narrowed = 0
    unexplained = []
    for text in FOLIO + MALFORMED:
        try:
            earley.parse(text)
            continue
        except UnexpectedCharacters as exc:
            before = str(NamingError(earley, exc, text, mode="fol"))
        except (UnexpectedToken, UnexpectedEOF) as exc:
            before = str(ParsingError(earley, exc, text, mode="fol"))
        try:
            kit.parse(text)
            unexplained.append((text[:60], before, "parsed"))
            continue
        except (NamingError, ParsingError) as exc:
            after = str(exc)
        if before == after:
            identical += 1
            continue
        head = "Incomplete formula - the input ended unexpectedly. Expected: "
        if head in before and head in after:
            old = set(before.split(head, 1)[1].split(", "))
            new = set(after.split(head, 1)[1].split(", "))
            if new < old:
                narrowed += 1
                continue
        unexplained.append((text[:60], before, after))
    # Measured on this corpus: 58 rejected, 26 byte-identical, 32 narrowed,
    # 0 unexplained. The floors sit below the measurement rather than on it --
    # an exact count would fail on any new FOLIO line -- but far enough above
    # zero that an empty comparison cannot pass. The earlier "> 50" here was
    # calibrated against a corpus that mistook the non-parsable ARTIFACT for
    # formulas, which is how a threshold ends up describing nothing.
    assert identical > 20, f"only {identical} identical messages -- probe weak"
    assert narrowed > 10, f"only {narrowed} narrowed messages -- probe weak"
    assert not unexplained, unexplained[:3]


def test_the_nonparsable_artifact_is_not_mistaken_for_a_corpus():
    """A guard against the mistake this file already made once: the artifact
    records VERDICTS about FOLIO lines, not formulas. If it ever does start
    holding formulas, the comment above it is wrong and the differentials
    should be re-pointed at it deliberately."""
    rows = [l for l in (Path("tests/fixtures/folio_fol_strings_nonparsable.txt")
                        .read_text(encoding="utf-8").splitlines())
            if l and not l.startswith("#")]
    assert rows, "artifact is empty"
    assert all(row.count("	") >= 2 for row in rows), rows[:2]
    assert all(row.split("	")[0].isdigit() for row in rows), rows[:2]
    assert all(row.split("	")[1] in ("NamingError", "ParsingError")
               for row in rows), rows[:2]
