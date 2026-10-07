r"""B3: the Haskell ``show`` escapes HETS leaks into its JSON, and the repair.

Every fixture here is a HAND-WRITTEN inline string. The real evidence (an
8,345,206-character ``/dg`` body) is never committed — the kit holds tools,
not corpora — so these small fixtures carry the exact defect instead, and
each one says which assertion it makes. Inline strings also sidestep the
Windows-CI CRLF checkout trap that cost the 0.28.1 release a point release.

Every expected character below is DERIVED, not copied from what the code
prints:

* ``\226\128\153`` = 0xE2 0x80 0x99, which is UTF-8 for U+2019 RIGHT SINGLE
  QUOTATION MARK ``’``;
* ``\194\167`` = 0xC2 0xA7, UTF-8 for U+00A7 SECTION SIGN ``§``;
* ``\&`` is Haskell's empty string, so ``\194\167\&7`` is ``§`` followed by
  the literal digit ``7``. It is there precisely because ``\1677`` would lex
  as ONE escape;
* ``\8594`` is 8594 > 255, so it cannot be a byte: U+2192 ``→``;
* ``\233`` is 233 < 256 but ``bytes([233])`` is not valid UTF-8, so the byte
  reading fails and the code-point reading applies: U+00E9 ``é``. The two
  readings coincide for a lone byte in 0x80..0xFF;
* ``\SOH`` is GHC's ``asciiTab[1]``, U+0001; ``\SO`` is ``asciiTab[14]``,
  U+000E — which is the second reason ``\&`` exists (``\SO\&H`` is
  U+000E then ``H``, not U+0001).
"""

import json

import pytest

from unicode_logic_kit.hets import (
    HaskellJsonRepairError,
    HetsClient,
    repair_haskell_json,
)

# =============================================================================
# Fixture A: the real defect in miniature. The two axiom strings are the real
# bytes from the OEO /dg body (line 92551 and the OEO_00360026 annotation),
# trimmed to 20 lines of JSON.
# =============================================================================

FIXTURE_A = (
    '{"DGraph": {"DGNode": [{"name": "n", "Axioms": [\n'
    '  {"name": "Ax1", "Axiom": "AnnotationAssertion( obo:IAO_0000112 '
    'obo:BFO_0000001 \\"Verdi\\226\\128\\153s Requiem\\"@en )"},\n'
    '  {"name": "Ax2", "Axiom": "AnnotationAssertion( obo:IAO_0000119 :x '
    '\\"See German spatial planning law: \\194\\167\\&7 Absatz 3 ROG\\" )"}\n'
    '], "Declarations": []}]}}'
)


def test_fixture_a_really_carries_the_defect():
    """The fixture's own proof: stdlib json refuses it, exactly as HETS' body is refused."""
    with pytest.raises(json.JSONDecodeError, match=r"Invalid \\escape"):
        json.loads(FIXTURE_A)


def test_repair_census_of_fixture_a_is_hand_counted():
    """5 decimal escapes in 2 runs, 1 separator, 0 mnemonics — counted by hand."""
    repair = repair_haskell_json(FIXTURE_A)
    assert bool(repair) is True
    # \226 \128 \153 is one three-escape run; \194 \167 is one two-escape run.
    assert repair.decimal_escapes == 5
    assert repair.decimal_runs == 2
    assert repair.empty_separators == 1
    assert repair.mnemonic_escapes == 0
    assert "5 decimal escape(s) in 2 run(s)" in repair.summary()


def test_repaired_fixture_a_parses_and_recovers_the_intended_characters():
    """U+2019 from \\226\\128\\153 and U+00A7 from \\194\\167, with the 7 surviving."""
    repair = repair_haskell_json(FIXTURE_A)
    data = json.loads(repair.text)
    axioms = data["DGraph"]["DGNode"][0]["Axioms"]
    assert axioms[0]["Axiom"] == (
        'AnnotationAssertion( obo:IAO_0000112 obo:BFO_0000001 '
        '"Verdi’s Requiem"@en )')
    assert axioms[1]["Axiom"] == (
        'AnnotationAssertion( obo:IAO_0000119 :x '
        '"See German spatial planning law: §7 Absatz 3 ROG" )')
    # The \& decoded to nothing, so the literal digit survived next to the §.
    assert "§7" in axioms[1]["Axiom"]


# =============================================================================
# The identity invariant, and the three ways a careless repair breaks it.
# =============================================================================

def test_valid_json_is_returned_character_for_character_unchanged():
    """A body json already accepts is never touched. Red on a global substitution."""
    source = json.dumps(
        {"quote": 'a "b" c', "backslash": "a\\b", "newline": "x\ny",
         "tab": "x\ty", "accented": "é", "curly": "’",
         "nul": "\x00"},
        ensure_ascii=False)
    repair = repair_haskell_json(source)
    assert bool(repair) is False
    assert repair.text == source
    assert json.loads(repair.text) == json.loads(source)


def test_an_escaped_backslash_followed_by_digits_is_not_a_decimal_escape():
    r"""The JSON ``"x\\226y"`` is a literal backslash then the text 226."""
    source = '{"a": "x\\\\226y"}'
    assert json.loads(source) == {"a": "x\\226y"}        # what it means
    repair = repair_haskell_json(source)
    assert bool(repair) is False
    assert repair.text == source
    assert json.loads(repair.text) == {"a": "x\\226y"}


def test_an_unknown_escape_stays_broken():
    r"""``\q`` is copied verbatim, so json raises its own Invalid \escape.

    Red on the requesting project's approach, which doubles any stray
    backslash (``return "\\\\" + other``) and so turns invalid JSON into
    valid JSON by guessing.
    """
    source = '{"a": "\\q"}'
    repair = repair_haskell_json(source)
    assert bool(repair) is False
    assert repair.text == source
    with pytest.raises(json.JSONDecodeError, match=r"Invalid \\escape"):
        json.loads(repair.text)


def test_a_backslash_outside_a_string_stays_broken():
    """Red on any implementation that is not string-aware."""
    source = '{\\ "a": 1}'
    repair = repair_haskell_json(source)
    assert bool(repair) is False
    assert repair.text == source
    with pytest.raises(json.JSONDecodeError):
        json.loads(repair.text)


# =============================================================================
# The decoding rules, each hand-derived.
# =============================================================================

def test_mnemonics_are_decoded_longest_match_first():
    r"""``\SOH`` is U+0001; ``\SO\&H`` is U+000E then a literal H."""
    one = repair_haskell_json('{"a": "\\SOH"}')
    assert one.mnemonic_escapes == 1
    assert json.loads(one.text) == {"a": "\x01"}

    two = repair_haskell_json('{"a": "\\SO\\&H"}')
    assert two.mnemonic_escapes == 1
    assert two.empty_separators == 1
    assert json.loads(two.text) == {"a": "\x0eH"}


def test_a_value_above_255_is_read_as_a_code_point():
    r"""``\8594`` cannot be a byte, so it is U+2192 — what ``show "\8594"`` emits."""
    repair = repair_haskell_json('{"a": "\\8594"}')
    assert repair.decimal_escapes == 1 and repair.decimal_runs == 1
    assert json.loads(repair.text) == {"a": "→"}


def test_a_lone_high_byte_becomes_its_character_never_a_replacement_char():
    r"""``\233`` is ``é``, NOT U+FFFD.

    bytes([233]) is not valid UTF-8, so rule 1 fails and rule 2 applies;
    233 == 0xE9 == U+00E9, so the byte and code-point readings coincide. A
    first prototype of this decoder used ``errors="replace"`` and silently
    produced U+FFFD here — the exact silent approximation the house rules
    forbid, which is why this assertion exists.
    """
    repair = repair_haskell_json('{"a": "\\233"}')
    assert json.loads(repair.text) == {"a": "é"}
    assert "�" not in repair.text


def test_adjacent_two_byte_characters_decode_as_one_utf8_run():
    r"""``\195\164\195\182`` is one maximal run of four bytes: ``äö``.

    0xC3 0xA4 is U+00E4 and 0xC3 0xB6 is U+00F6, and the pair is valid UTF-8
    as a whole — which is exactly why a RUN, not a single escape, is the unit
    that gets decoded. Nine such four-escape runs occur in the real body.
    """
    repair = repair_haskell_json('{"a": "\\195\\164\\195\\182"}')
    assert repair.decimal_escapes == 4
    assert repair.decimal_runs == 1
    assert json.loads(repair.text) == {"a": "äö"}


def test_a_surrogate_escape_is_refused_by_name():
    r"""``\55296`` is U+D800, not a character: raise, never substitute or drop."""
    with pytest.raises(HaskellJsonRepairError) as caught:
        repair_haskell_json('{"a": "\\55296"}')
    message = str(caught.value)
    assert "55296" in message
    assert "surrogate" in message
    assert "offset" in message
    assert "U+FFFD" in message          # says what it refuses to do


def test_a_value_above_the_unicode_range_is_refused_by_name():
    with pytest.raises(HaskellJsonRepairError, match="above U.10FFFF"):
        repair_haskell_json('{"a": "\\1200000"}')


def test_an_absurdly_long_decimal_escape_is_refused_by_name_not_by_cpython():
    r"""A 5 000-digit escape cannot be a character (U+10FFFF is 1114111, seven
    digits). Red before: CPython's own ``int()`` digit limit answered with a bare
    ``ValueError: Exceeds the limit (4300 digits)`` that names neither the
    escape nor its offset and is not the module's :class:`HaskellJsonRepairError`
    (a ``RuntimeError``), so a caller handling the module's refusal was bypassed.
    """
    body = '{"a": "\\' + "9" * 5000 + '"}'
    with pytest.raises(HaskellJsonRepairError) as caught:
        repair_haskell_json(body)
    message = str(caught.value)
    assert "offset 7" in message                  # the backslash is the 8th character
    assert "line 1" in message
    assert "above U+10FFFF" in message
    assert "U+FFFD" in message                    # says what it refuses to do
    assert "5000 significant digits" in message
    assert len(message) < 1000                    # not the 5 000 digits echoed back


@pytest.mark.parametrize("zeros", [0, 3, 4299, 5000])
def test_leading_zeros_are_not_significant(zeros):
    r"""Haskell's lexer reads ``\0065`` as 65, whatever the count of zeros: the
    decimal run's value is its significant digits, so ``\<zeros>65`` is ``A``
    (U+0041) — also past CPython's 4300-digit limit, where ``int()`` of the whole
    digit string would raise."""
    repair = repair_haskell_json('{"a": "\\' + "0" * zeros + '65"}')
    assert repair.decimal_escapes == 1
    assert json.loads(repair.text) == {"a": "A"}


def test_an_all_zero_escape_is_nul():
    r"""``\000`` has no significant digit: the value is 0, U+0000."""
    assert json.loads(repair_haskell_json('{"a": "\\000"}').text) == {"a": "\x00"}


def test_the_largest_scalar_value_still_reads_as_a_character():
    r"""``\1114111`` is U+10FFFF, seven significant digits: the bound is on the
    VALUE, so the longest legal escape is not caught by the digit-count guard."""
    repair = repair_haskell_json('{"a": "\\1114111"}')
    assert json.loads(repair.text) == {"a": "\U0010ffff"}


def test_a_decoded_control_character_cannot_break_the_document():
    r"""``\NUL`` re-emits as the JSON escape ``\u0000``, not a raw byte."""
    repair = repair_haskell_json('{"a": "\\NUL"}')
    assert "\\u0000" in repair.text
    assert json.loads(repair.text) == {"a": "\x00"}


# =============================================================================
# Through the client: dg() repairs on the FAILURE path only, dg_raw() never.
# =============================================================================

def test_dg_loads_a_body_only_the_repair_can_parse(monkeypatch):
    monkeypatch.setattr(HetsClient, "_get", lambda self, path: FIXTURE_A)
    client = HetsClient("http://localhost:8000")
    node = client.dg("/tmp/x/probe.owl")["DGraph"]["DGNode"][0]
    assert node["name"] == "n"
    assert "Verdi’s Requiem" in node["Axioms"][0]["Axiom"]


def test_dg_raw_returns_the_body_byte_for_byte(monkeypatch):
    monkeypatch.setattr(HetsClient, "_get", lambda self, path: FIXTURE_A)
    client = HetsClient("http://localhost:8000")
    assert client.dg_raw("/tmp/x/probe.owl") == FIXTURE_A


def test_dg_error_message_names_the_repair_when_one_happened(monkeypatch):
    """Repaired but still broken -> the message says so, so a failure is attributable."""
    # One real decimal escape, and a missing closing brace the repair cannot
    # and must not invent.
    broken = '{"a": "Verdi\\226\\128\\153s"'
    monkeypatch.setattr(HetsClient, "_get", lambda self, path: broken)
    client = HetsClient("http://localhost:8000")
    with pytest.raises(RuntimeError, match="after repairing 3 decimal escape"):
        client.dg("/tmp/x/probe.owl")


def test_a_body_with_nothing_to_repair_keeps_the_original_error(monkeypatch):
    """The 0.28.x wording for 'not json at all' is unchanged, verbatim."""
    monkeypatch.setattr(HetsClient, "_get", lambda self, path: "not json at all")
    client = HetsClient("http://localhost:8000")
    with pytest.raises(RuntimeError) as caught:
        client.dg("/tmp/x/probe.casl")
    message = str(caught.value)
    assert message.startswith("hets: dg response was not valid JSON")
    assert "after repairing" not in message
