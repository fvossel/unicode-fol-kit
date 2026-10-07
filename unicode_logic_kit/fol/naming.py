import weakref
from copy import copy

from lark import Lark, UnexpectedCharacters, UnexpectedToken, UnexpectedEOF
from lark.exceptions import ParseError

from ._identifiers import HUMAN_READABLE_PATTERNS

try:
    from lark.lexer import BasicLexer as _BasicLexer, LexerThread as _LexerThread
except ImportError:  # pragma: no cover - lark renamed its lexer internals
    _BasicLexer = _LexerThread = None


# --- Re-lexing the prefix of a failed parse ---------------------------------
#
# NamingError names the token in FRONT of the offending character ("Invalid
# predicate 'Foo' - unexpected character ..."), so it has to tokenize the text
# up to the failure point. The exception lark raises cannot supply that: the
# Earley scanner leaves `token_history` at None, so all it knows is the
# character and the position.
#
# The obvious way to get the rest, `Lark.lex()`, is a trap for this grammar:
#
#   * MSFL is parsed with parser="earley", which lexes dynamically and keeps no
#     standing lexer, so `Lark.lex` finds no `self.lexer` and constructs a
#     fresh BasicLexer on EVERY call;
#   * BasicLexer.__init__ runs a terminal-collision check whenever the package
#     `interegular` merely happens to be importable (lark/lexer.py, `if
#     has_interegular:`), comparing every pair of same-priority terminal
#     regexes;
#   * PREDICATE/NAME/CONSTANT/VARIABLE/SORT are generated at import from the
#     running interpreter's Unicode tables (see _identifiers.py), and comparing
#     THOSE takes MINUTES: measured at 185 s for one failed parse where the
#     same call takes 13 ms with interegular absent.
#
# Note what the third point does NOT say. The generated patterns are not
# enormous as text -- measured across all nine grammars the kit builds, the
# largest is NAME at 4856 characters and the rest are 1.0 to 1.8 kB. The cost
# is not in their length. interegular decides collisions by building a finite
# automaton per pattern and intersecting them pairwise, and these patterns
# range over most of the Unicode letter repertoire, so the automata are wide
# even where the source text is short. Do not "explain" this by their size:
# an earlier draft of this comment did, and the number it quoted was left over
# from the pre-0.23.0 enumerated character classes, which really were 192 kB.
#
# Nobody opts into that. `interegular` arrives as a transitive dependency of
# vLLM (via outlines), so every environment that evaluates model-generated
# formulas has it without asking, and model output fails to parse routinely
# rather than exceptionally. The cost is also invisible: the call looks like an
# ordinary parse and takes four orders of magnitude longer, which reads as a
# hung worker, not as a slow error message.
#
# So the lexer used for messages is built ONCE per parser and kept, with
# validation off. Both halves earn their place: caching pays the check once per
# parser instead of once per failure, and skipping it removes the check
# altogether. Nothing is lost by skipping. Validation checks that the GRAMMAR
# is well formed -- terminal regexes compile, no terminal is zero-width, every
# %ignore name is defined -- which lark already established when it built this
# parser and which cannot change afterwards. It only ever raises or stays
# silent; it never influences which tokens come out.
_ERROR_LEXERS: "weakref.WeakKeyDictionary" = weakref.WeakKeyDictionary()

# Cached in place of a lexer for a parser this module cannot serve, so the
# decision is made once rather than re-attempted on every failed formula.
_UNAVAILABLE = object()


def _error_lexer(parser: Lark):
    """The cached, validation-free lexer for `parser`, or None if lark's
    internals are not shaped the way this module expects.

    BUILDING the lexer is allowed to fail -- lark could rename its classes, or
    reject a grammar that only its own validation would have diagnosed -- and
    falling back to ``parser.lex`` covers that. USING it is not: see
    ``lex_for_message``.

    The cache READ and the cache WRITE are guarded separately from the
    construction, and separately from each other. Not fussiness -- each guard
    answers a different failure, and merging them breaks one of the two things
    this function has to do at once:

    * ``_ERROR_LEXERS`` is a WeakKeyDictionary, so it needs the parser to be
      hashable and weak-referenceable. A lark that grew ``__slots__`` without
      ``__weakref__``, or an ``__eq__`` without ``__hash__``, makes the lookup
      itself raise TypeError -- and unguarded, that TypeError comes out of
      every ``NamingError`` in place of the message, turning a syntax error
      into a crash.
    * One try around the whole body would swallow the construction failure
      before the ``_UNAVAILABLE`` write, so the failed construction would be
      retried on every single failed formula instead of once. That is not
      hypothetical: it is what the first attempt at this guard did, caught by
      ``test_a_grammar_lark_cannot_serve_is_only_attempted_once``.

    Nothing in here lexes, so swallowing is safe throughout: the worst outcome
    is the slow route, which is what the code did before this module existed.
    """
    try:
        cached = _ERROR_LEXERS.get(parser)
    except Exception:
        # The cache itself cannot hold this parser. Nothing to remember, so
        # every failed parse takes the slow route -- but it gets its message.
        return None
    if cached is not None:
        return None if cached is _UNAVAILABLE else cached

    lexer = None
    try:
        if (_BasicLexer is not None and _LexerThread is not None
                and hasattr(_LexerThread, "from_text")
                # postlex: Lark.lex feeds the token stream through it. The MSFL
                # grammars declare none, and reproducing that stage here would
                # be guesswork, so such a parser goes the long way round.
                and parser.options.postlex is None):
            conf = copy(parser.lexer_conf)
            conf.skip_validation = True
            candidate = _BasicLexer(conf)
            # Force the scanner NOW rather than on first use. It compiles the
            # terminal regexes, which is the one step validation would have
            # diagnosed with a readable LexError; doing it inside this try
            # means a grammar lark can only lex the slow way falls back here,
            # where falling back is free, instead of raising re.error out of
            # an error message. It also moves the compile off the first
            # failure's critical path.
            candidate.scanner
            lexer = candidate
    except Exception:
        lexer = None

    try:
        _ERROR_LEXERS[parser] = lexer if lexer is not None else _UNAVAILABLE
    except Exception:
        pass
    return lexer


def lex_for_message(parser: Lark, text: str) -> list:
    """Tokenize `text` the way the grammar does, for use in an error message.

    Equivalent to ``list(parser.lex(text))`` but without lark's per-call
    terminal-collision check -- see the comment above for why that check is
    ruinous on a runtime-generated Unicode grammar.

    Note what is NOT wrapped in a fallback: once a lexer exists, lexing runs
    outside any try. Catching here would be actively harmful, because the
    commonest failure is ``UnexpectedCharacters`` from `text` itself -- and
    "catch it, then retry through ``parser.lex``" would reinstate the whole
    cost this function exists to avoid, for exactly the malformed inputs that
    make it matter, while ending in the same exception. ``parser.lex`` did not
    swallow that exception either, so letting it through also keeps the
    behaviour callers already had.
    """
    lexer = _error_lexer(parser)
    if lexer is None:
        return list(parser.lex(text))
    return list(_LexerThread.from_text(lexer, text).lex(None))


_SYMBOL_NAMES = {
    "↔": "biconditional",
    "→": "implication",
    "∧": "conjunction",
    "∨": "disjunction",
    "⊕": "exclusive or",
    "⊗": "strong conjunction",
    "¬": "negation",
    "∀": "universal quantifier",
    "∃": "existential quantifier",
    "≤": "less-than-or-equal",
    "≥": "greater-than-or-equal",
    "≠": "not-equal",
    "=": "equality",
    "<": "less-than",
    ">": "greater-than",
    "+": "plus",
    "-": "minus",
    "*": "times",
    "/": "division",
    "(": "opening parenthesis",
    ")": "closing parenthesis",
    "[": "opening bracket",
    "]": "closing bracket",
    ",": "comma",
}

_NAMED_TOKENS = {
    "PREDICATE": "predicate",
    "NAME": "name/constant",
    "VARIABLE": "variable",
    "CONSTANT": "constant",
    "NUMBER": "number",
    "SORT": "sort annotation",
}

_MIXING_INFO = {
    "fol":   (
        {"∧", "∨", "⊕"},
        "Cannot mix conjunction (∧), disjunction (∨), and exclusive or (⊕) without parentheses",
    ),
    "msfol": (
        {"∧", "∨"},
        "Cannot mix conjunction (∧) and disjunction (∨) without parentheses",
    ),
    "msfl":  (
        {"∧", "∨", "⊗", "⊕"},
        "Cannot mix weak conjunction (∧), weak disjunction (∨), "
        "strong conjunction (⊗), and strong disjunction (⊕) without parentheses",
    ),
    "fl": (
        {"∧", "∨", "⊗", "⊕"},
        "Cannot mix weak conjunction (∧), weak disjunction (∨), "
        "strong conjunction (⊗), and strong disjunction (⊕) without parentheses",
    ),
    # Modal and second-order modes use the classical connectives at the same-level
    # group (the modal/temporal/second-order operators bind tighter, like ¬).
    "modal": (
        {"∧", "∨", "⊕"},
        "Cannot mix conjunction (∧), disjunction (∨), and exclusive or (⊕) without parentheses",
    ),
    "so": (
        {"∧", "∨", "⊕"},
        "Cannot mix conjunction (∧), disjunction (∨), and exclusive or (⊕) without parentheses",
    ),
    "dependence": (
        {"∧", "∨"},
        "Cannot mix conjunction (∧) and splitting disjunction (∨) without parentheses",
    ),
    "linear": (
        {"⊗", "&", "⊕"},
        "Cannot mix tensor (⊗), with (&), and plus (⊕) without parentheses",
    ),
    "lambek": (
        {"•"},
        "Parenthesise nested products (•) explicitly",
    ),
}


def _build_pattern_index(parser: Lark) -> dict:
    """Map terminal name -> raw pattern string for every terminal in the grammar."""
    index = {}
    for term in parser.terminals:
        pattern = term.pattern
        index[term.name] = pattern.value if hasattr(pattern, "value") else str(pattern)
    return index


def _display_name(token_type: str, patterns: dict) -> str:
    """Resolve a terminal name to a human-readable label.

    Named tokens use a fixed label; symbol tokens are resolved through their
    pattern; anything unknown falls back to the raw terminal name.
    """
    if token_type in _NAMED_TOKENS:
        return _NAMED_TOKENS[token_type]
    pattern = patterns.get(token_type)
    if pattern in _SYMBOL_NAMES:
        return _SYMBOL_NAMES[pattern]
    return token_type


def _is_structural(token_type: str) -> bool:
    """True if the token is a symbol/operator rather than a name-like token."""
    return token_type not in _NAMED_TOKENS


def _format_expected(expected, patterns: dict) -> str:
    """Render a set of expected terminal names as a sorted, deduplicated label list."""
    labels = []
    seen = set()
    for token_type in expected or ():
        label = _display_name(token_type, patterns)
        if label not in seen:
            seen.add(label)
            labels.append(label)
    return ", ".join(sorted(labels)) if labels else "a valid token"


class NamingError(UnexpectedCharacters):
    """Human-readable wrapper around a lexer-level UnexpectedCharacters failure.

    Token names are resolved through the grammar's terminal patterns rather
    than hard-coded anonymous-token numbers, so messages stay correct when the
    grammar changes.
    """

    def __init__(self, parser: Lark, original_exception: UnexpectedCharacters, formula: str, mode: str = "fol"):
        self._patterns = _build_pattern_index(parser)
        self._mode = mode

        pos = original_exception.pos_in_stream
        prefix = formula[:pos] if pos is not None and pos >= 0 else formula
        tokens = lex_for_message(parser, prefix)
        last_token = tokens[-1] if tokens else None

        if last_token is None:
            message = (
                f"SYNTAX_ERROR: Unexpected character "
                f"'{original_exception.char}' at position {original_exception.column}"
            )
        else:
            message = self._build_message(last_token, original_exception)

        self.__dict__.update(original_exception.__dict__)
        self.args = (message,)

    def _build_message(self, last_token, exc: UnexpectedCharacters) -> str:
        """Compose the final error message for a lexer-level failure."""
        display = _display_name(last_token.type, self._patterns)
        mixing_symbols, mixing_hint = _MIXING_INFO.get(self._mode, _MIXING_INFO["fol"])
        mixes = exc.char in mixing_symbols

        # A same-level connective is never a NAMING failure, even when the token
        # in front of it is name-like: in 'A ∧ B ∨ C' the predicate 'B' is
        # perfectly well formed and it is the MIX that the grammar refuses.
        # Reporting it as "Invalid predicate 'B' … Expected pattern: [A-Z]…"
        # sends the reader (or a generating model) off renaming a good name
        # instead of adding the brackets, so the mixing case takes the
        # structural wording — which carries the hint — in both branches.
        if _is_structural(last_token.type) or mixes:
            message = (
                f"SYNTAX_ERROR: Unexpected character '{exc.char}' at position "
                f"{exc.column} after {display} '{last_token.value}'"
            )
            if mixes:
                message += f". Hint: {mixing_hint}"
            return message

        message = (
            f"SYNTAX_ERROR: Invalid {display} '{last_token.value}' - "
            f"unexpected character '{exc.char}' at position {exc.column}"
        )
        # PREDICATE/NAME/CONSTANT/VARIABLE/SORT are generated at runtime from
        # the interpreter's Unicode tables (see fol/_identifiers.py) — their
        # raw pattern text is several kilobytes of \uXXXX-\uYYYY ranges, which
        # is not a message a human (or a model reading the error to retry)
        # can act on, so those five show a short hand-written description
        # instead of the pattern this module resolved from the grammar.
        human = HUMAN_READABLE_PATTERNS.get(last_token.type)
        if human:
            message += f". Expected pattern: {human}"
        else:
            pattern = self._patterns.get(last_token.type)
            if pattern:
                message += f". Expected pattern: {pattern}"
        return message

    def __str__(self):
        return self.args[0]


class ParsingError(ParseError):
    """Human-readable wrapper around parser-level failures.

    Handles both UnexpectedToken (a valid token in an invalid position) and
    UnexpectedEOF (the formula ended before it was complete). The expected-token
    set is rendered through the same pattern-based resolution as NamingError.
    """

    def __init__(self, parser: Lark, original_exception, formula: str, mode: str = "fol"):
        self._patterns = _build_pattern_index(parser)
        expected_str = _format_expected(getattr(original_exception, "expected", None), self._patterns)

        if isinstance(original_exception, UnexpectedEOF):
            message = (
                f"SYNTAX_ERROR: Incomplete formula - the input ended unexpectedly. "
                f"Expected: {expected_str}"
            )
        else:
            token = original_exception.token
            display = _display_name(token.type, self._patterns)
            column = getattr(original_exception, "column", None)
            where = f" at position {column}" if column not in (None, -1) else ""
            message = (
                f"SYNTAX_ERROR: Unexpected {display} '{token.value}'{where}. "
                f"Expected: {expected_str}"
            )
            mixing_symbols, mixing_hint = _MIXING_INFO.get(mode, _MIXING_INFO["fol"])
            if str(token.value) in mixing_symbols:
                message += f". Hint: {mixing_hint}"

        self.__dict__.update(original_exception.__dict__)
        self.args = (message,)

    def __str__(self):
        return self.args[0]
