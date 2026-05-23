from lark import Lark, UnexpectedCharacters, UnexpectedToken, UnexpectedEOF
from lark.exceptions import ParseError


_SYMBOL_NAMES = {
    "↔": "biconditional",
    "→": "implication",
    "∧": "conjunction",
    "∨": "disjunction",
    "⊕": "exclusive or",
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
}

_MIXING_SYMBOLS = {"∧", "∨", "⊕"}


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

    def __init__(self, parser: Lark, original_exception: UnexpectedCharacters, formula: str):
        self._patterns = _build_pattern_index(parser)

        pos = original_exception.pos_in_stream
        prefix = formula[:pos] if pos is not None and pos >= 0 else formula
        tokens = list(parser.lex(prefix))
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

        if _is_structural(last_token.type):
            message = (
                f"SYNTAX_ERROR: Unexpected character '{exc.char}' at position "
                f"{exc.column} after {display} '{last_token.value}'"
            )
            if exc.char in _MIXING_SYMBOLS:
                message += (
                    ". Hint: Cannot mix conjunction (∧), disjunction (∨), and "
                    "exclusive or (⊕) without parentheses"
                )
            return message

        message = (
            f"SYNTAX_ERROR: Invalid {display} '{last_token.value}' - "
            f"unexpected character '{exc.char}' at position {exc.column}"
        )
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

    def __init__(self, parser: Lark, original_exception, formula: str):
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
            if str(token.value) in _MIXING_SYMBOLS:
                message += (
                    ". Hint: Cannot mix conjunction (∧), disjunction (∨), and "
                    "exclusive or (⊕) without parentheses"
                )

        self.__dict__.update(original_exception.__dict__)
        self.args = (message,)

    def __str__(self):
        return self.args[0]
