"""Runtime-generated identifier-terminal patterns for the FOL grammar.

WHY GENERATED, NOT FROZEN INTO A .lark FILE
---------------------------------------------
The predicate/name/constant/variable terminals used to be one hand-written
ASCII regex each (``PREDICATE: /[A-Z][a-zA-Z0-9]*/`` and siblings), which is
exactly why they rejected a FOLIO gold formula's ``LostTo(x, świątek)`` or
``Hosted(beijing, 2008SummerOlympics)`` outright: nothing outside `A-Za-z0-9`
was a letter or digit as far as the grammar was concerned. The fix is not a
bigger hand-written regex — pasting in, say, the Latin-1 Supplement and Latin
Extended-A block boundaries would still reject Cyrillic, CJK, Devanagari, and
everything else, and worse, would go stale the moment Unicode adds a new
script or a codepoint's General_Category changes, silently drifting from
whatever Python interpreter (3.10+) actually runs the kit. There is already a
correct, always-current answer to "is this codepoint a letter, and is it
uppercase" sitting in the interpreter: ``str.isalpha()`` / ``str.isupper()``.
So the character classes below are computed BY SCANNING those tables once,
in Python, at first use in a process (behind ``functools.lru_cache`` — the
scan costs well under a tenth of a second, which is a one-time-per-process
cost this module pays exactly once, not a per-``MSFLParser()`` or per-parse
cost), and handed to Lark as the ordinary compiled regex text it already
expects. A codepoint range is never typed into source; it is read off the
interpreter that will also be doing the matching.

WHY GREEK AND OHM ARE CARVED OUT OF EVERY LETTER CLASS
---------------------------------------------------------
``λ`` is the LAMBDA terminal, ``μ`` is the measure-term operator, and the
plain lowercase Greek letters (``αβγδεζηθικνξοπρστυφχψω``) are already the
CONSTANT terminal's second, non-``c_`` alternative — all three predate this
module and are matched as literal/fixed patterns elsewhere in the grammar.
A "just widen the letter classes to every Unicode letter" pass would swallow
all of that: ``λ`` and ``μ`` would stop being operators and start being
ordinary lowercase letters eligible to open a NAME or VARIABLE token, and the
Greek CONSTANT alternative would become redundant with (and shadowed by, or
racing against) a NAME/VARIABLE token now built from the exact same
characters. So Greek and Coptic (U+0370-U+03FF), Greek Extended
(U+1F00-U+1FFF, the block holding the accented/breathed forms), and U+2126
OHM SIGN (Unicode's own compatibility duplicate of Greek OMEGA, canonically
equivalent to U+03A9) are excluded from every letter this module recognises
— uppercase, lowercase, and the combining-mark continuation class alike.
Greek identifiers do not get a UPGRADE from this module; they keep exactly
the behaviour they had before it existed.

WHY THE FIRST CHARACTER DECIDES PREDICATE VS. TERM, AND WHAT THAT MEANS FOR
SCRIPTS WITHOUT CASE
-----------------------------------------------------------------------------
The kit's grammar has always used capitalisation to tell a predicate from a
term at the lexer level — no keyword, no sigil, just "the first letter is
uppercase" — so widening the alphabet has to widen that same signal rather
than replace it. Concretely: a token whose first character satisfies
``str.isupper()`` classifies as PREDICATE; every other first LETTER
classifies as term-valued (NAME, CONSTANT, or VARIABLE, depending on length
and the ``c_``/Greek forms). Most scripts have no case distinction at all
(CJK, Arabic, Hebrew, Devanagari, Thai, ...) — for every one of them,
``str.isupper()`` is simply always False, so an identifier in such a script
is always term-valued and can never head an atom by itself. That is not an
oversight this module works around; it is the literal reading of the
existing rule extended honestly to alphabets it was never tested against:
predicate-hood is signalled by a case distinction, and where a script draws
no such distinction, there is nothing to signal it with, so term position is
what a bare identifier in that script gets. (A caseless-script PREDICATE is
still reachable the way it always was: spell the atom with a Latin
uppercase-first name.)

WHY A DIGIT-LEADING IDENTIFIER IS ALWAYS TERM-VALUED, NEVER A PREDICATE
---------------------------------------------------------------------------
``2008SummerOlympics`` has to lex as SOMETHING for
``Hosted(beijing, 2008SummerOlympics)`` to parse, but it cannot become a
second numeric terminal (that would make ``NUMBER`` and the new form
ambiguous over every plain integer) and it cannot become eligible for
PREDICATE position (nothing in the classical FOL literature, and nothing
elsewhere in this grammar, lets an atom's head start with a digit — and
doing so would need its own case-style signal for predicate-hood, which a
digit doesn't carry). So a digit-leading identifier is folded into NAME:
one-or-more ASCII digits, then a letter (of either case-class), then the
ordinary NAME continuation. It reuses NAME's own transform (a bare NAME
token becomes a ``Constant``; ``NAME "(" ... ")"`` becomes a ``Function``
head), so ``2008SummerOlympics`` used bare is a ``Constant`` and
``2008SummerOlympics(x)`` would be a function call — never an atom. ASCII
digits only, deliberately: NUMBER is untouched by this whole module (``2008``
still lexes as NUMBER, ``2.5`` still lexes as NUMBER), so the digit run here
is exactly the digits NUMBER itself would have recognised — the difference
is solely the mandatory trailing letter that pulls the token out of NUMBER's
territory and into NAME's.

WHY CONSTANT KEEPS ITS PRIORITY, AND WHY THAT PRIORITY NOW MATTERS MORE
---------------------------------------------------------------------------
Before this module existed, CONSTANT (``c_...`` or a Greek run) and NAME
(``[a-z]...``) could never both match the same span: NAME never contained an
underscore, so ``c_alpha`` was CONSTANT-only ground. Widening NAME to accept
underscores as a continuation character (needed for ``dani_Shapiro`` and
``family_History``) removes that separation — ``c_alpha`` now also matches
NAME's alpha-leading form in full (``c`` is a lowercase letter, ``_alpha``
is legal NAME continuation with one more letter further on). Lark resolves
same-span multi-terminal ambiguity by priority, and CONSTANT was already
declared at priority 3 against NAME's 2 (``CONSTANT.3`` / ``NAME.2`` in the
grammar, both unchanged by this module), so ``c_alpha`` still lexes as
CONSTANT and ``Constant("alpha")`` (the ``c_`` prefix stripped, per the
existing ``const_`` transform) rather than as NAME's
``Constant("c_alpha")`` — but the two terminals now genuinely overlap where
they never used to, so that priority ordering has gone from "never
exercised" to "load-bearing", and is exercised by an explicit regression
test (see ``tests/test_identifier_widening.py``) rather than left to be an
accident of how NAME happened to be spelled.

WHY THE GENERATED PATTERNS ARE SMALL: LOOKAHEAD, NOT A SECOND EXPLICIT LIST
-----------------------------------------------------------------------------
The five terminal patterns below used to be built by literally splicing the
explicit ``upper``/``lower``/``combining`` class bodies (see ``_classes()``)
into each terminal's own pattern text — several times each, since a
terminal's continuation class ("more letters/digits/underscores/marks") had
to be written out in full at every position it appeared. NAME alone spelled
that continuation class out three times inside its own pattern (once for
each of the two ``[cont]*`` runs in its alpha-leading form, once more in its
digit-leading form) plus the combined upper+lower class a fourth time for
its "one more letter" requirement; at over 100KB, that ONE terminal was the
bulk of a combined ~190KB ``terminal_block(include_sort=True)``, and
``re``/Lark compiling text that size is where the measured slowdown (a bare
``MSFLParser()`` going from single-digit milliseconds to ~200ms once the
identifier terminals widened) actually goes — NOT the codepoint scan in
``_classes()``, which stays well under a tenth of a second and was already
the one thing this module paid exactly once per process, cached, before and
after this change; and NOT parse throughput, which is unaffected either way
(the regex engine still walks the input once per character regardless of
how its pattern text is spelled).

The fix is not a tighter enumeration — ``lower`` is already a minimal
run-length encoding of a genuinely scattered set (every alphabetic script's
lowercase block is its own disjoint ``\\uXXXX-\\uYYYY`` span; there are a
lot of scripts) and cannot get meaningfully smaller as a literal list. The
fix is to stop writing that list out over and over, using something
Python's ``re`` module already tests cheaply instead of an enumerated class:
``\\w``. CPython defines ``\\w`` (in Unicode mode, the only mode this module
or Lark's parser ever runs in) as matching a codepoint exactly when
``str.isalnum(c)`` is true or ``c == '_'``, and ``str.isalnum()`` is in turn
``isalpha() or isdecimal() or isdigit() or isnumeric()``. So
``[^\\W\\d_]`` — a word character, with decimal digits and underscore
carved back out via the leading ``\\d``/``_`` in the negated class — is
``isalpha()`` PLUS one small extra sliver: codepoints that are
``isdigit()`` or ``isnumeric()`` without being ``isdecimal()`` (already
excluded by ``\\d``) or ``isalpha()`` — superscript/subscript digits
(``²``), Roman numerals (``Ⅻ``), vulgar fractions (``½``), circled/
parenthesized number forms, and similar. That sliver (below, DELTA) is what
has to be excluded for ``[^\\W\\d_]`` to mean exactly "is a letter"; scanned
at 0x0000-0x2FFFF it comes to 80 disjoint spans, a little over a kilobyte of
pattern text — two orders of magnitude smaller than the 12KB-20KB classes it
stands in for, because it only has to list the exceptions \\w tacks on
beside "is a letter", not the tens of thousands of letters themselves.

So LETTER — "any letter this module recognises", i.e. the exact union of
:func:`uppercase_class` and :func:`lowercase_class` a continuation position
used to get by splicing both bodies in directly — becomes
``(?:[UPPER_NONALPHA]|(?!GREEK)(?!DELTA)(?!CEILING)[^\\W\\d_])``: small,
FIXED-size pieces, used however many times a terminal's shape needs a
letter, instead of the same multi-kilobyte enumeration copy-pasted that
many times. Two alternatives, not one, because ``\\w`` alone cannot stand
in for "is a letter, either case": ``upper`` (``str.isupper()``) contains a
120-codepoint sliver — Roman numerals (U+2160-U+216F, category Nl) and
circled/squared Latin capitals (e.g. U+24B6, category So) — that carries
no case-STYLE distinction Python calls "alphabetic" at all
(``str.isalpha()`` is false for every one of them), so ``\\w``-based DELTA
exclusion or plain non-membership rules them out of the second alternative
regardless of any lookahead tweak; some are not even ``\\w`` members to
begin with (So-category symbols are not ``isalnum()``), so no negative
lookahead over ``\\w`` could ever admit them — a lookahead can only narrow
what a pattern already matches, never widen it. UPPER_NONALPHA
(:data:`_Classes.upper_nonalpha`, ``upper`` intersected with "not
isalpha()") explicitly lists that 120-codepoint sliver instead (five
contiguous spans, closer to DELTA's size than to UPPER's). Every other
letter — every codepoint the union actually shares with plain
``isalpha()`` — still goes through the cheap ``\\w``-based path, with a
CEILING lookahead alongside GREEK/DELTA so the lookahead atom, which has
no length limit of its own the way an enumerated class does, cannot admit
anything :func:`_class_body` did not itself scan up to
:data:`_MAX_CODEPOINT`. It is a regex ATOM, not a character-class body: it
opens with a group and lookahead assertions, so — unlike
:func:`uppercase_class`, :func:`lowercase_class`, and :func:`combining_class`
below, which still return plain class-body text — it cannot be spliced
inside a caller's own ``[...]``. Nothing outside this module needs to
(``dialect_repair.py`` is the only outside consumer of the raw class
bodies, and it always brackets them itself, so those three functions are
untouched, same computation and same output as before this section
existed). UPPER stays fully enumerated regardless: ``re`` has no built-in
uppercase test the way ``\\w`` doubles as a letter test, so there is nothing
to invert it out of. And the term-valued ("lowerish") letter — everywhere
``lowercase_class()``'s ~12KB body used to be spliced in directly — becomes
LETTER with UPPER's already-computed text reused once more as a negative
lookahead in front of it, rather than a second, separately-enumerated
"letter minus upper" class (UPPER's exclusion also correctly screens out
LETTER's own UPPER_NONALPHA alternative, since that alternative is a
subset of UPPER).

Only the functions that build a whole terminal's regex (``predicate_pattern``
and its siblings, and ``terminal_block``) were rewritten on these smaller
atoms. What a caller of those gets back is a differently-spelled pattern for
the exact same set of strings, never a different one.

WHAT SECURES THE EQUIVALENCE
--------------------------------
DELTA and UPPER_NONALPHA are computed the same way UPPER/LOWER/COMBINING
already were — one more call each to :func:`_class_body`, scanning
0x0000-0x2FFFF once more inside the same cached, once-per-process
:func:`_classes` — so neither can ever drift from whatever Unicode version
the running interpreter actually implements, the same guarantee the rest
of this module already gives; neither is typed in by hand and neither can
silently go stale across a Python upgrade. But that construction is an
assertion, not a proof of the claim above (that
``(?:[UPPER_NONALPHA]|(?!GREEK)(?!DELTA)(?!CEILING)[^\\W\\d_])`` matches
precisely "is a letter (either case, including the caseless-but-cased
Roman-numeral/circled-symbol sliver), is not excluded, and is not beyond
``_MAX_CODEPOINT``"), so ``tests/test_identifiers_equivalence.py`` checks
it EXHAUSTIVELY rather than on a sample: for every one of the 0x30000
codepoints from 0x0000 to 0x2FFFF, it confirms the new letter atom matches
exactly where ``str.isalpha() or str.isupper()`` holds and the codepoint is
not one of :data:`_EXCLUDED_RANGES`, and that the new term-valued
("lowerish") atom matches exactly where
``str.isalpha() and not str.isupper()`` holds under the same exclusion —
i.e. exactly the sets the old, fully-enumerated ``lower``/``upper`` classes
contained (in ``lower``'s case exactly; in ``upper``'s case, the LETTER
atom matches the SAME set ``upper`` does, just split across the two
alternatives above), codepoint for codepoint. A second test class checks
codepoints ABOVE ``_MAX_CODEPOINT`` are rejected, since the exhaustive scan
by construction cannot exercise the CEILING lookahead itself.

WHAT THIS MODULE DOES NOT TOUCH
-----------------------------------
NUMBER (``[0-9]+(\\.[0-9]+)?``), FORALL, EXISTS, and LAMBDA stay exactly as
declared in ``fol/grammars/terminals.lark`` — none of them classify a
letter, so none of them need widening, and none of them are generated here.
``fol/sanitize.py``, the layer that maps AST names down to strictly-ASCII
tokens for TPTP/Prover9/SMT-LIB/Isabelle/CASL export, is untouched on
purpose: it exists to make names safe for ASCII-only target formats, not to
make them parseable by this (now Unicode-wide) grammar, and widening it
would leak raw non-ASCII text into export formats that cannot represent it.

PUBLIC SURFACE
------------------
:func:`uppercase_class`, :func:`lowercase_class`, :func:`combining_class`
return the three raw regex character-CLASS BODIES (no enclosing ``[``/``]``)
this module is built from, for reuse by anything that needs to recognise the
same alphabet outside the grammar (``fol/dialect_repair.py``'s legality
check, and tests) by splicing them inside its own ``[...]``. They are
unaffected by the LOOKAHEAD section above: same computation, same returned
text, before and after. :func:`predicate_pattern`, :func:`name_pattern`,
:func:`constant_pattern`, :func:`variable_pattern`, and :func:`sort_pattern`
return the full terminal regex (again without a Lark terminal name or
priority — just the pattern text between the ``/.../``) for each widened
terminal, now built from the small internal lookahead atoms rather than
repeated copies of the class bodies. :func:`terminal_block` renders the
complete, ready-to-splice Lark terminal declarations (name, priority, and
pattern together) that ``_fol_nodes.build_grammar`` inserts into every
mode's grammar text. :data:`HUMAN_READABLE_PATTERNS` maps each widened
terminal's name to a short English description of its shape, for
``fol/naming.py`` to show in a NamingError instead of the generated regex
text.
"""

import unicodedata
from functools import lru_cache
from typing import Callable, NamedTuple

__all__ = [
    "uppercase_class", "lowercase_class", "combining_class",
    "predicate_pattern", "name_pattern", "constant_pattern",
    "variable_pattern", "sort_pattern",
    "terminal_block", "HUMAN_READABLE_PATTERNS",
]

# Greek and Coptic, Greek Extended, and the OHM SIGN — see the module
# docstring's "WHY GREEK AND OHM ARE CARVED OUT" section.
_EXCLUDED_RANGES = ((0x0370, 0x03FF), (0x1F00, 0x1FFF), (0x2126, 0x2126))

# Plane 0 (BMP) through Plane 2 (CJK Extension B/C/... territory). Every
# script this kit's test corpora (FOLIO included) actually exercise lives
# below this, and the scan is a fixed one-time-per-process cost regardless
# of where the ceiling sits, so there is no pressure to trim it further.
_MAX_CODEPOINT = 0x2FFFF


def _excluded(codepoint: int) -> bool:
    return any(lo <= codepoint <= hi for lo, hi in _EXCLUDED_RANGES)


def _escape(codepoint: int) -> str:
    return f"\\u{codepoint:04x}" if codepoint <= 0xFFFF else f"\\U{codepoint:08x}"


def _class_body(predicate: Callable[[str], bool]) -> str:
    """A regex character-class body (no enclosing ``[``/``]``) matching every
    codepoint up to :data:`_MAX_CODEPOINT` for which ``predicate(chr(cp))``
    holds and the codepoint is not one of :data:`_EXCLUDED_RANGES`, run-
    length-encoded into ``\\uXXXX-\\uYYYY`` spans (astral codepoints use the
    8-digit ``\\U........`` form) so the result is a few kilobytes of regex
    text rather than tens of thousands of single-character alternatives."""
    spans = []
    start = None
    for codepoint in range(_MAX_CODEPOINT + 1):
        keep = predicate(chr(codepoint)) and not _excluded(codepoint)
        if keep and start is None:
            start = codepoint
        elif not keep and start is not None:
            spans.append((start, codepoint - 1))
            start = None
    if start is not None:
        spans.append((start, _MAX_CODEPOINT))
    return "".join(
        _escape(lo) if lo == hi else f"{_escape(lo)}-{_escape(hi)}"
        for lo, hi in spans
    )


class _Classes(NamedTuple):
    upper: str
    lower: str
    combining: str
    delta: str
    upper_nonalpha: str


@lru_cache(maxsize=1)
def _classes() -> _Classes:
    """Compute the four character classes this module is built from, once
    per process. Deferred behind ``lru_cache`` rather than run at import
    time: importing this module (or anything that imports it, which given
    ``_fol_nodes.py``'s import means most of the package) must stay cheap
    even for a caller who never actually builds a parser; the codepoint
    scan is paid only when a terminal pattern is first asked for — in
    practice, the first time a grammar for some mode is actually built —
    and never again in that process.

    ``upper``  — codepoints with ``str.isupper() == True``: the PREDICATE-
        signalling class (see the module docstring's "WHY THE FIRST
        CHARACTER DECIDES" section).
    ``lower``  — every other alphabetic codepoint (``str.isalpha()`` true,
        ``str.isupper()`` false): both ordinary lowercase letters and every
        letter from a script with no case distinction at all, which is
        exactly the "term-valued" class that section describes. Returned
        as-is by :func:`lowercase_class` for outside callers; the terminal
        patterns below no longer splice this in directly (see the module
        docstring's LOOKAHEAD section) but it is still computed and
        returned unchanged, since ``dialect_repair.py`` still needs it.
    ``combining`` — codepoints in Unicode general categories Mn (nonspacing
        mark) and Mc (spacing combining mark): NFD-decomposed accents such
        as U+0301 COMBINING ACUTE ACCENT, needed so that ``świątek``
        survives NFD normalisation (``ś`` → ``s`` + U+0301) and still lexes
        as one identifier rather than two tokens plus a stray mark. Not
        part of ``\\w`` (marks are not alphanumeric), so — unlike ``lower``
        — there is no cheaper way to express this one; it stays a literal
        enumerated class either way.
    ``delta`` — codepoints ``\\w`` matches that ``[^\\W\\d_]`` alone would
        wrongly admit as letters: ``isdigit()`` or ``isnumeric()`` without
        being ``isdecimal()`` (already excluded by ``\\d``) or
        ``isalpha()``. Not returned by any public function — nothing
        outside this module needs the raw sliver, only the negative
        lookahead built from it (see :func:`_letter_atom`).
    ``upper_nonalpha`` — codepoints with ``str.isupper() == True`` but
        ``str.isalpha() == False``: e.g. the Roman numeral block
        U+2160-U+216F (category Nl, ``isupper()`` true, ``isalpha()``
        false) and circled/squared Latin capitals such as U+24B6 (category
        So). ``upper`` already contains these (it is built from
        ``str.isupper()`` alone, with no ``isalpha()`` condition), so a
        continuation position that used to splice ``upper`` in directly
        (PREDICATE/SORT/NAME's own continuation, before this module's
        lookahead rewrite) accepted them; a LETTER atom built purely from
        ``\\w`` cannot reach them the same way — some are not even ``\\w``
        members (So-category symbols are not ``isalnum()``), and the rest
        (the Nl-category Roman numerals) are exactly what ``delta`` above
        excludes. So they need a small explicit class of their own rather
        than a lookahead tweak (see :func:`_letter_atom`); it is tiny (five
        contiguous spans, 120 codepoints total) because it is exactly
        ``upper`` minus ``lower``'s complement restricted to ``isupper()``
        already-non-alphabetic codepoints, not a general enumeration.
    """
    upper = _class_body(str.isupper)
    lower = _class_body(lambda ch: ch.isalpha() and not ch.isupper())
    combining = _class_body(lambda ch: unicodedata.category(ch) in ("Mn", "Mc"))
    delta = _class_body(
        lambda ch: ch.isalnum() and not ch.isalpha() and not ch.isdecimal())
    upper_nonalpha = _class_body(lambda ch: ch.isupper() and not ch.isalpha())
    return _Classes(
        upper=upper, lower=lower, combining=combining, delta=delta,
        upper_nonalpha=upper_nonalpha)


def uppercase_class() -> str:
    """Regex character-class body for the PREDICATE-signalling letters."""
    return _classes().upper


def lowercase_class() -> str:
    """Regex character-class body for every term-valued letter (ordinary
    lowercase, plus every letter of a script without case)."""
    return _classes().lower


def combining_class() -> str:
    """Regex character-class body for combining marks (categories Mn/Mc)."""
    return _classes().combining


# ---------------------------------------------------------------------------
# Small, fixed-size lookahead atoms — see the module docstring's "WHY THE
# GENERATED PATTERNS ARE SMALL" section for what these stand in for and why
# they are correct. Private: none of these is a character-class body (each
# opens with a lookahead assertion), so none of them can be spliced inside a
# caller's own ``[...]`` the way uppercase_class()/lowercase_class()/
# combining_class() can — they are used as bare regex atoms/alternatives
# only, exclusively by the pattern-builders below.
# ---------------------------------------------------------------------------

def _greek_lookahead() -> str:
    """``(?!...)`` excluding :data:`_EXCLUDED_RANGES` — built from that same
    tuple (never a second, hand-typed copy of the ranges), so it cannot
    silently drift from what ``_classes()`` already excludes from
    upper/lower/combining/delta."""
    body = "".join(
        _escape(lo) if lo == hi else f"{_escape(lo)}-{_escape(hi)}"
        for lo, hi in _EXCLUDED_RANGES
    )
    return f"(?![{body}])"


def _delta_lookahead() -> str:
    """``(?!...)`` excluding :data:`_Classes.delta` — the ``\\w``-but-not-a-
    letter sliver described in the module docstring's LOOKAHEAD section."""
    return f"(?![{_classes().delta}])"


def _ceiling_lookahead() -> str:
    """``(?!...)`` excluding every codepoint above :data:`_MAX_CODEPOINT`.

    ``[^\\W\\d_]`` (Python's ``\\w`` minus digits/underscore) has no ceiling
    of its own — ``\\w`` matches any codepoint with ``str.isalnum()`` true,
    all the way to U+10FFFF, including scripts like CJK Unified Ideograph
    Extension G (U+30000-U+3134A, category Lo) that :func:`_class_body`
    never scans past ``_MAX_CODEPOINT`` to include. Without this lookahead
    the LETTER atom would silently accept letters the fully-enumerated
    ``upper``/``lower`` classes it stands in for never could, breaking the
    "differently-spelled pattern for the exact same set of strings" promise
    this module's docstring makes for the lookahead rewrite. Built from
    ``_MAX_CODEPOINT`` itself (never a second, hand-typed boundary), so it
    cannot drift out of sync with the ceiling every other class in this
    module already respects."""
    return f"(?![\\U{_MAX_CODEPOINT + 1:08x}-\\U0010ffff])"


@lru_cache(maxsize=1)
def _letter_atom() -> str:
    """LETTER: matches exactly one codepoint for which ``str.isalpha()`` OR
    ``str.isupper()`` holds (not ``isalpha()`` alone — see below), the
    codepoint is not one of :data:`_EXCLUDED_RANGES`, and the codepoint is
    at most :data:`_MAX_CODEPOINT` — i.e. exactly the union of
    :func:`uppercase_class` and :func:`lowercase_class` (which is what "any
    letter, either case" used to be built from directly, by literally
    splicing both class bodies into a continuation position). Two
    alternatives:

    * ``[UPPER_NONALPHA]`` — the small explicit class of codepoints with
      ``isupper()`` true but ``isalpha()`` false (Roman numerals, circled/
      squared Latin capitals; see :func:`_classes`'s ``upper_nonalpha``
      docstring for why these need spelling out rather than a lookahead
      tweak: some are not ``\\w`` members at all, so no negative lookahead
      over ``\\w`` could ever admit them).
    * ``(?!GREEK)(?!DELTA)(?!CEILING)[^\\W\\d_]`` — every ``isalpha()``
      codepoint (upper or lower alike), which is everything ``uppercase_class()``
      and ``lowercase_class()`` contain that is not already covered by the
      first alternative.

    Cached: it is pure string formatting over already-cached data, but it
    gets referenced several times per terminal pattern across nine grammar
    modes, so there is no reason to re-format it every time."""
    upper_nonalpha = _classes().upper_nonalpha
    isalpha_branch = (
        f"{_greek_lookahead()}{_delta_lookahead()}{_ceiling_lookahead()}"
        f"[^\\W\\d_]"
    )
    return f"(?:[{upper_nonalpha}]|{isalpha_branch})"


@lru_cache(maxsize=1)
def _lowerish_atom() -> str:
    """The term-valued ("lowerish") letter: LETTER, with one more negative
    lookahead excluding :func:`uppercase_class` stacked in front — i.e.
    exactly what :func:`lowercase_class`'s body used to be spliced in for
    directly, at every position a term-valued first character was needed.
    Reuses UPPER's already-computed text as a lookahead rather than
    re-deriving a second, separately-enumerated "letter minus upper"
    class — see the module docstring's LOOKAHEAD section."""
    return f"(?![{uppercase_class()}]){_letter_atom()}"


@lru_cache(maxsize=1)
def _continuation_atom(*, underscore: bool) -> str:
    """The shared "letter, digit, or combining mark" continuation atom,
    optionally with ``_`` added. Every identifier terminal now passes
    ``underscore=True``; the flag survives because CONSTANT's ``c_`` form must
    NOT (its own leading ``c_`` is the marker, and letting the tail carry more
    underscores would widen the span it competes with NAME over — see the
    module docstring's CONSTANT-priority section). Matches exactly one
    character; callers append ``*``/``+`` themselves, the same way they would
    to a character class — this is a non-capturing group standing in for one,
    not a class body."""
    digits = "0-9_" if underscore else "0-9"
    return f"(?:{_letter_atom()}|[{digits}{combining_class()}])"


def predicate_pattern() -> str:
    """PREDICATE: an uppercase-signalling letter, then letters/digits/
    underscores/combining marks — the SAME continuation class the term-valued
    terminals get.

    0.23.0 shipped this asymmetric, on the reasoning that keeping ``_`` out of
    predicate position left an IRI-shaped name such as
    ``Http___www_w3_org_owl_Thing`` as illegal a predicate token as it had
    always been, which ``fol/sanitize.py`` relies on. That reasoning does not
    hold: ``sanitize.py`` carries its OWN deliberately ASCII-strict
    ``_PRED_RE`` (``[A-Z][a-zA-Z0-9]*``) and reaches its verdict without
    consulting this module at all, so it renames that IRI either way.

    What the asymmetry did break is ``chem/interop.py``. Its kit spelling of a
    ChemLog predicate capitalises the FIRST character and nothing else, so 17
    of the chemical signature's 40 predicates spell as ``Has_bond_to``,
    ``In_ring_of_size_6``, ``Net_charge_neutral`` and the like — names the kit's
    own parser then refused, leaving the chemical vocabulary impossible to
    write down in the kit's own surface syntax. A generating model handed the
    signature and told to use it produced ``Has_bond_to(c, x)``, was refused,
    and fell back to ``HasBondTo`` — which parses but is in no signature, so
    every molecule came back as an uninterpreted-symbol error rather than a
    verdict.
    """
    cont = _continuation_atom(underscore=True)
    return f"[{uppercase_class()}]{cont}*"


def name_pattern() -> str:
    """NAME: two alternatives, both term-valued.

    The alpha-leading form starts with a term-valued letter, then any
    continuation characters, then one more explicit letter (upper- or
    lower-class — a predicate-signalling letter is legal HERE, mid-token;
    only the first character carries the predicate/term distinction), then
    more continuation — the same "at least two letters" shape the original
    ``[a-z][a-zA-Z0-9]*[a-zA-Z][a-zA-Z0-9]*`` had, just with underscores and
    the wider alphabet spliced into every continuation run, so a single bare
    letter still falls through to VARIABLE instead of NAME.

    The digit-leading form is one-or-more ASCII digits, then a letter, then
    the same continuation — see the module docstring's "WHY A DIGIT-LEADING
    IDENTIFIER" section.
    """
    cont = _continuation_atom(underscore=True)
    letter = _letter_atom()
    alpha_led = f"{_lowerish_atom()}{cont}*{letter}{cont}*"
    digit_led = f"[0-9]+{letter}{cont}*"
    return f"(?:{alpha_led})|(?:{digit_led})"


def variable_pattern() -> str:
    """VARIABLE: one term-valued letter, then only ASCII digits — unchanged
    in shape from before this module, only the letter class is widened."""
    return f"{_lowerish_atom()}[0-9]*"


def constant_pattern() -> str:
    """CONSTANT: the ``c_`` form (now accepting Unicode letters/digits/
    combining marks after the literal ``c_``, e.g. ``c_świątek``) or the
    pre-existing plain lowercase Greek run — untouched, since Greek is
    excluded from every generated class (see the module docstring)."""
    cont = _continuation_atom(underscore=False)
    c_form = f"c_{cont}+"
    greek_form = "[αβγδεζηθικνξοπρστυφχψω]+"
    return f"(?:{c_form})|(?:{greek_form})"


def sort_pattern() -> str:
    """SORT: a literal ``:`` then the same shape as PREDICATE — including the
    underscore, so a sorted signature can name a sort after the same vocabulary
    its predicates come from (``:In_ring``) instead of being the one identifier
    position that still cannot."""
    cont = _continuation_atom(underscore=True)
    return f":[{uppercase_class()}]{cont}*"


def terminal_block(*, include_sort: bool) -> str:
    """The complete Lark terminal declarations for PREDICATE, CONSTANT, NAME,
    VARIABLE, and — when ``include_sort`` is true (the many-sorted modes) —
    SORT, in the priorities the grammar has always used (``CONSTANT.3`` over
    ``NAME.2`` over ``VARIABLE.1``; PREDICATE and SORT are unambiguous with
    everything else so carry no explicit priority). ``include_sort`` is a
    parameter rather than always-on because SORT never appears in a
    classical/modal/second-order grammar's rules, and declaring an unused
    terminal there is needless generated text for no behavioural gain."""
    lines = [
        f"PREDICATE: /{predicate_pattern()}/",
        "",
        f"CONSTANT.3: /{constant_pattern()}/",
        "",
        f"NAME.2: /{name_pattern()}/",
        "",
        f"VARIABLE.1: /{variable_pattern()}/",
    ]
    if include_sort:
        lines += ["", f"SORT: /{sort_pattern()}/"]
    return "\n".join(lines) + "\n"


#: Terminal name -> short English description of its shape, for
#: ``fol/naming.py``'s NamingError to show in place of the generated regex
#: text (a few kilobytes of ``\uXXXX-\uYYYY`` ranges is not a message a
#: human — or a model reading the error to retry — can act on).
HUMAN_READABLE_PATTERNS = {
    "PREDICATE": (
        "an uppercase letter (in any script that has letter case) followed "
        "by letters, digits, or combining marks"
    ),
    "NAME": (
        "a lowercase or caseless letter, then letters/digits/underscores/"
        "combining marks with at least one more letter among them; or one "
        "or more digits followed by a letter and more of the same"
    ),
    "CONSTANT": (
        "'c_' followed by letters, digits, or combining marks, or one or "
        "more lowercase Greek letters (α-ω)"
    ),
    "VARIABLE": (
        "a single lowercase or caseless letter, optionally followed by "
        "digits"
    ),
    "SORT": (
        "':' followed by an uppercase letter and then letters, digits, or "
        "combining marks"
    ),
}
