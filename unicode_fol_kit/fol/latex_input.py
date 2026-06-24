"""LaTeX input: read a LaTeX math-mode formula and parse it with MSFLParser.

This module is the exact inverse of ``node.to_latex()`` (the LaTeX renderer in
``_msfl_nodes.py``). It translates LaTeX math-mode markup into the toolkit's
Unicode surface syntax and then hands the result to :class:`MSFLParser`.

The translation is a tokenizing replacement: multi-token constructs
(``\\mathbin{\\mathsf{U}}``, ``\\mathsf{G}``, ``\\mathrm{...}``, ``{:}``,
``\\left(`` / ``\\right)``, subscript braces ``X_{...}``) are resolved first;
then backslash control sequences (``\\leftrightarrow``, ``\\forall``, …) are
mapped glyph-for-glyph by matching the FULL ``[a-zA-Z]+`` run after the
backslash (so ``\\leq`` is never shadowed by ``\\le``); then LaTeX spacing
(``\\,`` ``\\;`` ``\\!`` ``\\quad`` ``\\qquad`` and a backslash-space) is
deleted; finally leftover grouping braces are stripped, since operator
precedence in the Unicode surface syntax is explicit and LaTeX grouping carries
no information the parser needs.

The control-sequence map also accepts the common hand-written synonyms a person
would type by hand (``\\neg`` for ``¬``, ``\\to`` for ``→``, ``\\iff`` for
``↔``, ``\\le`` for ``≤``, ``\\times`` for ``*``, …) so that pasted LaTeX need
not have come from ``to_latex``.
"""

import re

from .msflparser import MSFLParser


# Control sequences whose argument-brace constructs must be resolved before the
# generic ``[a-zA-Z]+`` control-sequence pass and before brace stripping, since
# each one literally contains braces. ``\mathbin{\mathsf{U}}`` is listed before
# the bare ``\mathsf{U}`` would ever be considered, so the Until glyph wins.
_MULTI_TOKEN = [
    (r"\mathbin{\mathsf{U}}", "Ⓤ"),
    (r"\mathsf{G}", "Ⓖ"),
    (r"\mathsf{F}", "Ⓕ"),
    (r"\mathsf{X}", "Ⓝ"),
    (r"\mathsf{O}", "Ⓞ"),
    (r"\mathsf{P}", "Ⓟ"),
    (r"\left(", "("),
    (r"\right)", ")"),
    (r"\left[", "("),
    (r"\right]", ")"),
    (r"\left{", "("),
    (r"\right}", ")"),
    (r"{:}", ":"),
]

# Backslash control sequences mapped glyph-for-glyph. Keys are the bare names
# (the ``[a-zA-Z]+`` run after the backslash); lookup is by the FULL run, so a
# longer name (``leftrightarrow``) is never shadowed by a prefix (``leq`` vs
# ``le``). Both the glyphs emitted by ``to_latex`` and the common hand-written
# synonyms are included.
_CONTROL_SEQUENCES = {
    # Quantifiers.
    "forall": "∀",
    "exists": "∃",
    # Negation.
    "lnot": "¬",
    "neg": "¬",
    # Conjunction / disjunction.
    "land": "∧",
    "wedge": "∧",
    "lor": "∨",
    "vee": "∨",
    # Łukasiewicz strong connectives.
    "otimes": "⊗",
    "oplus": "⊕",
    # Implication / equivalence.
    "rightarrow": "→",
    "to": "→",
    "implies": "→",
    "leftrightarrow": "↔",
    "iff": "↔",
    # Comparisons.
    "neq": "≠",
    "ne": "≠",
    "leq": "≤",
    "le": "≤",
    "geq": "≥",
    "ge": "≥",
    # Arithmetic.
    "cdot": "*",
    "times": "*",
    # Lambda.
    "lambda": "λ",
    # Modal / temporal / deontic prefix operators.
    "Box": "□",
    "Diamond": "◇",
}

# LaTeX spacing macros built from a backslash plus a NON-letter (``\,`` ``\;``
# ``\!`` and a literal backslash-space). These are deleted outright. The
# letter-run spacing macros ``\quad`` / ``\qquad`` are handled by the
# control-sequence pass (they map to nothing) so they never reach here.
_SPACING_NONLETTER = re.compile(r"\\[,;!\s]")

# ``\mathrm{Sort}`` -> ``Sort``: an unwrapping of the upright-roman sort marker.
_MATHRM = re.compile(r"\\mathrm\{([^{}]*)\}")

# Generic subscript braces ``X_{...}`` -> ``X_...``. Covers epistemic/doxastic
# operators (``K_{alice}`` -> ``K_alice``) and any other braced subscript. The
# inner group forbids nested braces, which never occur in to_latex subscripts.
_SUBSCRIPT_BRACES = re.compile(r"_\{([^{}]*)\}")

# A backslash control sequence: backslash then the LONGEST run of letters.
_CONTROL_SEQ = re.compile(r"\\([a-zA-Z]+)")

# The letter-run spacing macros, mapped to empty so the control-sequence pass
# deletes them. Kept separate from _CONTROL_SEQUENCES (which holds real glyphs)
# purely for readability.
_SPACING_LETTER = {"quad": "", "qquad": ""}


def _replace_control_seq(match: "re.Match") -> str:
    """Map one backslash control sequence to its Unicode glyph (or to nothing).

    The full letter run is looked up so that, e.g., ``\\leftrightarrow`` resolves
    as a whole and is never mis-split into ``\\le`` + ``ftrightarrow``. A spacing
    macro (``\\quad`` / ``\\qquad``) maps to the empty string. An unknown control
    sequence is left verbatim (minus the backslash) so the downstream parser can
    surface a precise error rather than this translator swallowing it.
    """
    name = match.group(1)
    if name in _CONTROL_SEQUENCES:
        return _CONTROL_SEQUENCES[name]
    if name in _SPACING_LETTER:
        return _SPACING_LETTER[name]
    return name


def latex_to_unicode(text: str) -> str:
    """Translate a LaTeX math-mode formula into the toolkit's Unicode surface syntax.

    The result is a Unicode string ready for :class:`MSFLParser`. The pipeline:

    1. Resolve multi-token brace constructs (``\\mathbin{\\mathsf{U}}``,
       ``\\mathsf{G}`` and the other temporal/deontic markers, ``\\left(`` /
       ``\\right)`` grouping, ``{:}`` the sort colon).
    2. Unescape ``\\_`` to a literal underscore (the ``c_``-constant escape that
       ``to_latex`` emits) so it is not later read as a subscript operator.
    3. Unwrap ``\\mathrm{Sort}`` to ``Sort``.
    4. Collapse generic subscript braces ``X_{...}`` to ``X_...``.
    5. Map every remaining backslash control sequence by its full letter run
       (longest-match), covering both the ``to_latex`` glyphs and common
       hand-written synonyms; the letter-run spacing macros map to nothing.
    6. Delete the non-letter spacing macros (``\\,`` ``\\;`` ``\\!`` and a
       backslash-space).
    7. Strip leftover grouping braces ``{`` ``}`` (LaTeX grouping carries no
       parser-relevant information; precedence is explicit via the operators).
    8. Collapse redundant whitespace.
    """
    s = text

    # 1. Multi-token brace constructs, most specific first.
    for src, dst in _MULTI_TOKEN:
        s = s.replace(src, dst)

    # 2. Unescape the c_-constant underscore escape (\_  ->  _). Done before the
    #    subscript-brace and control-sequence passes so the bare underscore in a
    #    name like c_zero survives intact.
    s = s.replace("\\_", "_")

    # 3. Unwrap \mathrm{Sort}.
    s = _MATHRM.sub(r"\1", s)

    # 4. Generic subscript braces  X_{...} -> X_...
    s = _SUBSCRIPT_BRACES.sub(r"_\1", s)

    # 5. Backslash control sequences (longest letter run wins).
    s = _CONTROL_SEQ.sub(_replace_control_seq, s)

    # 6. Non-letter LaTeX spacing macros.
    s = _SPACING_NONLETTER.sub(" ", s)

    # 7. Strip leftover grouping braces.
    s = s.replace("{", "").replace("}", "")

    # 8. Collapse redundant whitespace.
    s = re.sub(r"\s+", " ", s).strip()

    # 9. Tighten the sort colon: the grammar's SORT terminal is /:[A-Z][...]*/ ,
    #    which admits no whitespace before the ':' or between ':' and the sort
    #    name. ``to_latex`` emits the colon glued (``x{:}\mathrm{Human}``), but a
    #    person may hand-write ``x {:} \mathrm{Human}`` or ``x : Human``; the
    #    spaces introduced by steps 1/6/8 would then split the SORT token. Since
    #    ':' occurs nowhere else in any grammar, removing whitespace flanking it
    #    is unambiguous and only ever reconstructs a sort annotation.
    s = re.sub(r"\s*:\s*", ":", s)
    return s


def parse_latex(text: str, many_sorted: bool = False, fuzzy: bool = False,
                modal: bool = False, second_order: bool = False) -> "object":
    """Parse a LaTeX math-mode formula into an AST node.

    Translates ``text`` to the toolkit's Unicode surface syntax with
    :func:`latex_to_unicode`, then parses it with :class:`MSFLParser` in the
    selected mode. The mode flags are passed straight through.

    The Unicode surface syntax produced by the translation must be valid for the
    chosen mode: e.g. modal operators require ``modal=True``, sort annotations
    require ``many_sorted=True``, and Łukasiewicz strong connectives (⊗ ⊕)
    require ``fuzzy=True``. Mismatched flags surface as the parser's usual
    NamingError / ParsingError.

    Args:
        text: a LaTeX math-mode formula (no surrounding ``$…$`` needed).
        many_sorted: parse in MSFOL/MSFL mode (sorted quantifiers/constants).
        fuzzy: parse with Łukasiewicz operators.
        modal: parse classical unsorted FOL plus modal/temporal/deontic operators.
        second_order: parse classical unsorted FOL plus second-order quantifiers.

    Returns:
        The parsed AST :class:`~unicode_fol_kit.fol.nodes.Node`.
    """
    unicode_text = latex_to_unicode(text)
    parser = MSFLParser(
        many_sorted=many_sorted,
        fuzzy=fuzzy,
        modal=modal,
        second_order=second_order,
    )
    return parser.parse(unicode_text)
