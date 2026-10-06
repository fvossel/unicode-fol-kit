r"""Repairing Haskell ``show`` escapes that leak into HETS' JSON responses.

The defect, exactly
-------------------
HETS 0.108.0's ``GET /dg/<iri>?format=json`` serialises OWL axiom strings by
applying Haskell's ``show`` to a ``String`` whose ``Char``\ s are the UTF-8
BYTES of the intended text (the classic latin1-decode of a UTF-8 input). GHC's
``showLitChar`` emits a DECIMAL escape for every code point above 127, so the
body that reaches a client contains sequences such as::

    AnnotationAssertion( obo:IAO_0000112 obo:BFO_0000001 "Verdi\226\128\153s Requiem"@en )

``\226`` is not a JSON escape, so :func:`json.loads` refuses the whole 8.3 MB
document with ``Invalid \escape``, and every endpoint that needs the
development graph — including every ``hets:`` comorphism edge, which resolves
its node through :meth:`~unicode_fol_kit.hets.client.HetsClient.dg` — fails on
any library carrying one non-ASCII annotation.

Why this is lossless recovery and not an approximation
------------------------------------------------------
The emitter is known. GHC's ``showLitChar`` is::

    c > '\DEL'      -> '\\' : show (ord c)        -- DECIMAL, with \& if a digit follows
    c == '\DEL'     -> "\\DEL"
    c == '\\'       -> "\\\\"
    c >= ' '        -> the character itself
    c in 7..13      -> "\\a" "\\b" "\\t" "\\n" "\\v" "\\f" "\\r"
    otherwise       -> '\\' : asciiTab !! ord c   -- "\\NUL" .. "\\US", plus "\\SP"

and ``showLitString`` adds ``\"`` for a double quote. So the complete set of
backslash sequences a Haskell-``show``\ n string can contain is finite and
enumerable, and exactly five of its members are not also JSON escapes: the
decimal runs, the empty-string separator ``\&``, the three-letter mnemonics,
``\a`` and ``\v``. Everything else (``\" \\ \n \t \b \f \r``) coincides with
JSON and is left untouched.

The census of the real 8,345,206-character body confirms the emitter: of its
backslash sequences, ``\"`` occurs 17618 times, ``\n`` 8028, ``\ddd`` 897,
``\\`` 354, ``\t`` 29 and ``\&`` 7 — and nothing else. The 897 decimal
escapes form 389 maximal runs, every value lies in 128..226 (i.e. every one is
a byte, never a code point: ``show`` emits decimal only above 127, so a value
below 128 cannot occur), and all 389 runs decode as STRICT UTF-8 with zero
failures. All seven ``\&`` sit in the one place Haskell's lexer needs a
separator, ``\194\167\&7`` — without it ``\1677`` would lex as a single
escape.

The one judgment call: a decimal run is read as UTF-8 BYTES first
-----------------------------------------------------------------
For a maximal run of values ``v1..vk``:

1. if every ``vi < 256`` and ``bytes(v1..vk)`` decodes as strict UTF-8, the
   run's text is that decoding (``\226\128\153`` -> ``’``);
2. else, if every ``vi`` is a Unicode scalar value, the run's text is
   ``"".join(chr(vi))`` — the reading a well-formed Haskell ``String`` would
   mean (``show "\8594" == "\8594"``, and 8594 cannot be a byte);
3. else :class:`HaskellJsonRepairError` is raised, naming the escape, its
   value and its offset.

Rule 1 before rule 2 is an ASSUMPTION ABOUT HETS 0.108.0, not a fact about
Haskell: a HETS build whose strings were NOT latin1-mangled would have a
genuine two-character ``Ã©`` (``\195\169``) read here as ``é``. The evidence
is unanimous for the byte reading — ``Verdi’s``, ``§7 Absatz 3 ROG``, and all
389 runs valid UTF-8 — and the opposite order would mangle the real data, so
this is the right default; it is stated here as an assumption so a future
HETS whose output is clean can be spotted by the census this module reports.

For a lone byte in 0x80..0xFF that is NOT valid UTF-8 the two readings
coincide (``\233`` -> ``é`` either way), so rule 2 is never a guess in that
case. ``errors="replace"`` is deliberately NOT used anywhere: a U+FFFD in
place of a character this module could have recovered is exactly the silent
approximation this kit refuses, so an unrecoverable run raises instead.

What this module will NOT do
----------------------------
It will not make invalid JSON valid by guessing. The scan is STRING-AWARE: a
backslash outside a string literal is copied verbatim (so ``{\ "a": 1}`` still
fails), escaped backslashes are consumed pairwise (so the legitimate JSON
``"x\\226y"`` — a literal backslash followed by the text ``226`` — is left
alone), and ``\`` followed by anything this module does not recognise (e.g.
``\q``) is copied verbatim so :func:`json.loads` raises its own
``Invalid \escape`` as before. Re-emission goes through
``json.dumps(chunk)[1:-1]``, so the standard library does the escaping and a
decoded ``"``, ``\`` or control character cannot break the document.

:meth:`~unicode_fol_kit.hets.client.HetsClient.dg` calls this only on the
FAILURE path — ``json.loads`` first, repair only when it raises — so a body
the standard library already accepts is never touched at all, and that
identity is structural rather than argued.

This module touches nothing in :mod:`unicode_fol_kit.dl`, adds no OWL
construct and has no effect on the description-logic tableau. Its relevance to
the kit's two-route rule is indirect but total: until it exists, the kit cannot
read HETS' axiom list for any ontology with a non-ASCII annotation, so the
HETS FOL image cannot be cross-checked against
:func:`unicode_fol_kit.dl.tbox_to_fol` / :func:`unicode_fol_kit.dl.kb_to_fol`
at all. It changes no verdict on its own.
"""

from __future__ import annotations

import json
import re
from dataclasses import dataclass

__all__ = [
    "HaskellJsonRepair",
    "HaskellJsonRepairError",
    "repair_haskell_json",
]

#: GHC's ``asciiTab``: the mnemonic ``showLitChar`` emits for code points
#: 0..32, plus ``DEL``. Indices 7..13 are never emitted by ``show`` (it
#: prefers the single-letter ``\a \b \t \n \v \f \r``) but Haskell's lexer
#: accepts them, so they are accepted here too.
_ASCII_TAB = (
    "NUL", "SOH", "STX", "ETX", "EOT", "ENQ", "ACK", "BEL",
    "BS", "HT", "LF", "VT", "FF", "CR", "SO", "SI",
    "DLE", "DC1", "DC2", "DC3", "DC4", "NAK", "SYN", "ETB",
    "CAN", "EM", "SUB", "ESC", "FS", "GS", "RS", "US",
    "SP",
)

#: Mnemonic -> character, longest first so ``\SOH`` is matched before ``\SO``
#: (the very reason GHC emits ``\SO\&H`` for a ``\SO`` followed by an ``H``).
#: ``\a`` and ``\v`` are included because JSON has no escape for either;
#: ``\b \f \n \r \t`` are deliberately ABSENT — they are valid JSON already
#: and are copied verbatim, which is what keeps the identity invariant exact.
_MNEMONICS = {
    **{name: chr(code) for code, name in enumerate(_ASCII_TAB)},
    "DEL": "\x7f",
    "a": "\a",
    "v": "\v",
}
_MNEMONIC_NAMES = tuple(sorted(_MNEMONICS, key=len, reverse=True))

#: Only ``"`` and ``\`` can change the scanner's state, so the walk jumps
#: between them with one compiled ``search`` instead of stepping character by
#: character. Measured on the real 8.3 MB body: 0.79 s per-character against
#: 0.02 s for the equivalent skipping walk.
_SPECIAL = re.compile(r'["\\]')

_DIGITS = "0123456789"

#: The highest Unicode scalar value; a decimal escape above it, or inside the
#: surrogate range, is not a character and is refused rather than guessed.
_MAX_SCALAR = 0x10FFFF


class HaskellJsonRepairError(RuntimeError):
    """A Haskell escape that cannot be read as any character.

    Raised instead of substituting U+FFFD or dropping the escape: a decimal
    value above U+10FFFF, or inside the surrogate range D800..DFFF, is not a
    Unicode scalar value, and guessing what the server meant would be the
    silent approximation this kit refuses.
    """


@dataclass(frozen=True)
class HaskellJsonRepair:
    """The repaired JSON text plus a census of what had to be repaired.

    Fields:

    * ``text`` — the repaired JSON document. Equal to the input, character for
      character, when nothing was repaired.
    * ``decimal_escapes`` — how many ``\\ddd`` escapes were decoded.
    * ``decimal_runs`` — how many MAXIMAL runs those escapes formed. A run is
      what gets decoded as UTF-8, so this is the count that matters for
      the byte-first rule: 897 escapes in 389 runs on the real body.
    * ``empty_separators`` — how many ``\\&`` (Haskell's empty string) were
      removed.
    * ``mnemonic_escapes`` — how many ``\\NUL``/``\\ESC``/``\\a``/``\\v``/... were
      decoded.
    """

    text: str
    decimal_escapes: int = 0
    decimal_runs: int = 0
    empty_separators: int = 0
    mnemonic_escapes: int = 0

    def __bool__(self) -> bool:
        """True iff anything at all was repaired.

        A falsy repair means :attr:`text` IS the input, so a caller can
        re-raise the original :func:`json.loads` error against the original
        body and keep its wording unchanged.
        """
        return bool(self.decimal_escapes or self.empty_separators
                    or self.mnemonic_escapes)

    def summary(self) -> str:
        """One-line census, for an error message or a log."""
        return (f"{self.decimal_escapes} decimal escape(s) in "
                f"{self.decimal_runs} run(s), "
                f"{self.empty_separators} \\& separator(s), "
                f"{self.mnemonic_escapes} mnemonic escape(s)")


#: How many significant decimal digits a Unicode scalar value can have
#: (``len("1114111")``): an escape with more is above U+10FFFF whatever its
#: digits are.
_MAX_SCALAR_DIGITS = len(str(_MAX_SCALAR))


def _escape_value(digits: str, offset: int, body: str) -> int:
    """The value of one decimal escape, from its ``digits``.

    Leading zeros are not significant — Haskell's lexer reads ``\\0065`` as
    65, and so does this. An escape with more significant digits than
    U+10FFFF has is refused HERE, by name, before :func:`int` is asked to read
    it: CPython's own digit limit would otherwise answer a 5 000-digit escape
    with a bare ``ValueError`` ("Exceeds the limit (4300 digits)") that names
    neither the escape nor its offset and is not a
    :class:`HaskellJsonRepairError`, so a caller handling the module's own
    refusal would be bypassed (and, with the limit lifted, the message would
    carry all 5 000 digits).
    """
    significant = digits.lstrip("0")
    if len(significant) > _MAX_SCALAR_DIGITS:
        line = body.count("\n", 0, offset) + 1
        raise HaskellJsonRepairError(
            f"hets: the Haskell escape \\{significant[:_MAX_SCALAR_DIGITS]}... "
            f"({len(significant)} significant digits) at offset {offset} "
            f"(line {line}) is not a Unicode scalar value (above U+10FFFF), "
            "so it cannot be a character. This module refuses to guess: it "
            "will not substitute U+FFFD and it will not drop the escape. "
            "Fetch the body with HetsClient.dg_raw() and inspect it, or "
            "report it to the HETS server's maintainers.")
    return int(significant or "0")


def _decode_run(values, offsets, body: str) -> str:
    """Read one maximal decimal-escape run as text (rules 1-3 above)."""
    if all(value < 256 for value in values):
        try:
            return bytes(values).decode("utf-8")
        except UnicodeDecodeError:
            pass
    for value, offset in zip(values, offsets):
        if value > _MAX_SCALAR or 0xD800 <= value <= 0xDFFF:
            line = body.count("\n", 0, offset) + 1
            why = "a surrogate" if value <= _MAX_SCALAR else "above U+10FFFF"
            run = " ".join("\\" + str(v) for v in values)
            raise HaskellJsonRepairError(
                f"hets: the Haskell escape \\{value} at offset {offset} "
                f"(line {line}) is not a Unicode scalar value ({why}), so it "
                f"cannot be a character. The run it belongs to is: {run}. "
                "This module refuses to guess: it will not substitute U+FFFD "
                "and it will not drop the escape. Fetch the body with "
                "HetsClient.dg_raw() and inspect it, or report it to the "
                "HETS server's maintainers.")
    return "".join(chr(value) for value in values)


def repair_haskell_json(body: str) -> HaskellJsonRepair:
    r"""Turn HETS' Haskell-``show`` escapes into JSON ones.

    Handles exactly four things, and only inside a string literal: a decimal
    escape run, ``\&``, a Haskell mnemonic, and nothing else — ``\`` followed
    by any other character (including the JSON-legal ``\" \\ \n \t \b \f \r
    \/ \uXXXX``) is copied verbatim. A backslash OUTSIDE a string literal is
    copied verbatim too, so invalid JSON stays invalid: this function never
    makes a document parse by guessing.

    Args:
        body: the response body, exactly as the server sent it.

    Returns:
        A :class:`HaskellJsonRepair`. It is falsy, with ``.text`` equal to
        ``body``, when there was nothing to repair.

    Raises:
        HaskellJsonRepairError: a decimal escape is not a Unicode scalar
            value. Never raised for anything a Haskell ``show`` can emit.
    """
    out = []
    index = 0
    length = len(body)
    in_string = False
    decimal_escapes = 0
    decimal_runs = 0
    empty_separators = 0
    mnemonic_escapes = 0

    while index < length:
        match = _SPECIAL.search(body, index)
        if match is None:
            out.append(body[index:])
            break
        start = match.start()
        if start > index:
            out.append(body[index:start])
        if body[start] == '"':
            out.append('"')
            in_string = not in_string
            index = start + 1
            continue
        # A backslash. Outside a string it is not an escape at all, and
        # touching it is how a repair turns broken JSON into a guess.
        if not in_string:
            out.append("\\")
            index = start + 1
            continue
        nxt = body[start + 1] if start + 1 < length else ""
        if nxt == "&":
            empty_separators += 1
            index = start + 2
            continue
        if nxt and nxt in _DIGITS:
            values = []
            offsets = []
            cursor = start
            while cursor + 1 < length and body[cursor] == "\\":
                after = body[cursor + 1]
                if after == "&":
                    empty_separators += 1
                    cursor += 2
                    continue
                if after not in _DIGITS:
                    break
                end = cursor + 1
                while end < length and body[end] in _DIGITS:
                    end += 1
                values.append(_escape_value(body[cursor + 1:end], cursor, body))
                offsets.append(cursor)
                cursor = end
            decimal_escapes += len(values)
            decimal_runs += 1
            out.append(json.dumps(_decode_run(values, offsets, body))[1:-1])
            index = cursor
            continue
        for name in _MNEMONIC_NAMES:
            if body.startswith(name, start + 1):
                mnemonic_escapes += 1
                out.append(json.dumps(_MNEMONICS[name])[1:-1])
                index = start + 1 + len(name)
                break
        else:
            # Verbatim: the JSON-legal escapes (\" \\ \n \t \b \f \r \/
            # \uXXXX) and anything unrecognised alike. Consuming the escaped
            # character too is what makes `\\226` a literal backslash
            # followed by the text 226, not a decimal escape.
            out.append("\\" + nxt)
            index = start + 2
        continue

    return HaskellJsonRepair(
        text="".join(out),
        decimal_escapes=decimal_escapes,
        decimal_runs=decimal_runs,
        empty_separators=empty_separators,
        mnemonic_escapes=mnemonic_escapes,
    )
