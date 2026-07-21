"""LaTeX input: read a LaTeX math-mode formula and parse it with MSFLParser.

This module is the exact inverse of ``node.to_latex()`` (the LaTeX renderer in
``_msfl_nodes.py``). It translates LaTeX math-mode markup into the toolkit's
Unicode surface syntax and then hands the result to :class:`MSFLParser`.

The translation is a tokenizing replacement, run as a fixed pipeline (see
:func:`latex_to_unicode` for the exact, numbered steps): multi-token brace
constructs (``\\mathbin{\\mathsf{U}}``, ``\\mathsf{G}``, ``\\mathrm{...}``,
``{:}``, ``\\left(`` / ``\\right)``, subscript braces ``X_{...}``) are
resolved first; escaped literal braces (``\\{`` ``\\}``, used by the
cardinality and slashed-existential constructs) are protected from the later
brace-stripping step; a bare ``\\mathsf{name}`` left over after the specific
multi-token constructs is unwrapped as a hybrid-logic nominal; then backslash
control sequences (``\\leftrightarrow``, ``\\forall``, …) are mapped
glyph-for-glyph by matching the FULL ``[a-zA-Z]+`` run after the backslash (so
``\\leq`` is never shadowed by ``\\le``); then LaTeX spacing (``\\,`` ``\\;``
``\\!`` ``\\quad`` ``\\qquad`` and a backslash-space) is deleted; the counting
quantifier's exponent (``\\exists^{\\geq 3}``) is collapsed to the glued
``∃≥3`` terminal; finally leftover grouping braces are stripped (the protected
literal ones are restored right after), since operator precedence in the
Unicode surface syntax is explicit and LaTeX grouping carries no information
the parser needs.

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
#
# Every entry here is a full, self-contained literal string, so list order is
# safe regardless of shared prefixes: e.g. ``\mathsf{Say}`` and ``\mathsf{S}``
# (the latter never actually registered — Since uses the overlined
# ``\mathbin{\overline{\mathsf{S}}}`` form below) would not collide even if
# both were present, because ``str.replace`` matches the full literal, not a
# prefix. Any ``\mathsf{...}`` construct NOT listed here (a nominal) falls
# through to the generic unwrap in step 2 of :func:`latex_to_unicode`.
_MULTI_TOKEN = [
    # Past-tense overlined markers FIRST: each contains a bare \mathsf{…} that a
    # later rule would otherwise rewrite (e.g. \overline{\mathsf{P}} ⊃ \mathsf{P}).
    (r"\mathbin{\overline{\mathsf{S}}}", "⒮"),
    (r"\overline{\mathsf{H}}", "⒣"),
    (r"\overline{\mathsf{P}}", "⒫"),
    (r"\overline{\mathsf{Y}}", "⒴"),
    (r"\mathbin{\mathsf{U}}", "Ⓤ"),
    (r"\mathsf{G}", "Ⓖ"),
    (r"\mathsf{F}", "Ⓕ"),
    (r"\mathsf{X}", "Ⓝ"),
    (r"\mathsf{O}", "Ⓞ"),
    (r"\mathsf{P}", "Ⓟ"),
    # Assertive Say_<agent> / bouletic Want_<agent> (agent_prefix, like K_a/B_a).
    (r"\mathsf{Say}", "Say"),
    (r"\mathsf{Want}", "Want"),
    # Contrast (concessive but/whereas) and the box-arrow / diamond-arrow
    # counterfactual conditionals — all registered "mathbin" multi-token forms.
    (r"\mathbin{\mathsf{C}}", "Ⓒ"),
    (r"\mathbin{\Box\!\rightarrow}", "□→"),
    (r"\mathbin{\Diamond\!\rightarrow}", "◇→"),
    # Linear logic: the exponential "!" and additive "with" (&) markup.
    (r"\mathord{!}", "!"),
    (r"\mathbin{\&}", "&"),
    # Linear logic multiplicative unit.
    (r"\mathbf{1}", "𝟙"),
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
    # Łukasiewicz strong connectives / linear-logic tensor & plus (shared glyphs).
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
    # Lambda / degree-measure term.
    "lambda": "λ",
    "mu": "μ",
    # Modal / temporal / deontic prefix operators.
    "Box": "□",
    "Diamond": "◇",
    # Set-cardinality delimiters |{...}|.
    "lvert": "|",
    "rvert": "|",
    # Linear implication (lollipop) and the Lambek product.
    "multimap": "⊸",
    "bullet": "•",
    # Lambek "under" \: the LITERAL backslash character (a formula-level
    # connective in the lambek mode, not LaTeX escaping).
    "backslash": "\\",
}

# LaTeX spacing macros built from a backslash plus a NON-letter (``\,`` ``\;``
# ``\!`` and a literal backslash-space). These are deleted outright. The
# letter-run spacing macros ``\quad`` / ``\qquad`` are handled by the
# control-sequence pass (they map to nothing) so they never reach here.
_SPACING_NONLETTER = re.compile(r"\\[,;!\s]")

# ``\mathrm{Sort}`` -> ``Sort``: an unwrapping of the upright-roman sort marker.
_MATHRM = re.compile(r"\\mathrm\{([^{}]*)\}")

# A bare ``\mathsf{name}`` left after the specific _MULTI_TOKEN entries above
# have consumed every KNOWN operator markup (Say/Want/G/F/X/O/P and the
# mathbin-wrapped U/C/S forms) denotes a hybrid-logic nominal
# (``Nominal.to_latex`` renders as ``\mathsf{i}``) — or, defensively, any other
# hand-written ``\mathsf{...}`` wrapping, which is unwrapped the same way
# ``\mathrm{Sort}`` is. Run AFTER the _MULTI_TOKEN loop so the operator forms
# are already gone, and BEFORE the generic control-sequence pass (which would
# otherwise treat the bare "\mathsf" as an unknown, unmapped control sequence
# and mangle the result into "mathsfi", silently misreading the nominal).
_MATHSF = re.compile(r"\\mathsf\{([^{}]*)\}")

# Generic subscript braces ``X_{...}`` -> ``X_...``. Covers epistemic/doxastic
# operators (``K_{alice}`` -> ``K_alice``) and any other braced subscript. The
# inner group forbids nested braces, which never occur in to_latex subscripts.
_SUBSCRIPT_BRACES = re.compile(r"_\{([^{}]*)\}")

# The hybrid-logic satisfaction operator's ATNOM terminal is ``/@[a-z][a-zA-Z0-9]*/``
# — glued directly to the nominal, no underscore — even though @ is rendered as
# a regular agent_prefix operator (like K_a / B_a) and so emits ``@_{i}`` ->
# (after the subscript-brace pass) ``@_i``. Unlike K_a/B_a/Say_a/Want_a, whose
# underscore IS part of the grammar terminal, @'s underscore is a renderer
# artefact only and must be dropped. Matches ONLY "@_", never touching the
# agent operators' own underscore-bearing terminals.
_AT_UNDERSCORE = re.compile(r"@_([a-zA-Z][a-zA-Z0-9]*)")

# The counting quantifier's LaTeX form ``\exists^{\geq 3}`` / ``\exists^{\leq
# n}`` / ``\exists^{= n}`` (Count.to_latex / SortedCount.to_latex) must collapse
# to the single glued COUNTOP+NUMBER terminal ``∃≥3`` / ``∃≤n`` / ``∃=n`` the
# grammar expects — brace-stripping alone would leave a stray "^" and a space
# between the relation and the bound, neither of which the COUNTOP terminal
# (``/∃[≥≤=]/``) tolerates. Runs AFTER the control-sequence pass (so \geq/\leq
# have already become ≥/≤) and BEFORE brace-stripping (so the ``{...}``
# boundary is still there to anchor the match).
_COUNT_EXPONENT = re.compile(r"∃\^\{\s*([≥≤=])\s*(\d+)\s*\}")

# A backslash control sequence: backslash then the LONGEST run of letters.
_CONTROL_SEQ = re.compile(r"\\([a-zA-Z]+)")

# The letter-run spacing macros, mapped to empty so the control-sequence pass
# deletes them. Kept separate from _CONTROL_SEQUENCES (which holds real glyphs)
# purely for readability.
_SPACING_LETTER = {"quad": "", "qquad": ""}

# Placeholders protecting escaped literal braces (``\{`` ``\}``) — used by the
# cardinality term ``\lvert\{v : φ\}\rvert`` and the slashed existential
# ``\exists x / \{y, z\}\, φ`` — from the generic brace-stripping step, which
# must remove ordinary LaTeX GROUPING braces but leave these literal ones
# behind (the Unicode surface syntax for both constructs uses real ``{`` ``}``
# characters). Private-use-area code points: they cannot occur in any LaTeX
# input this translator is meant to accept, and no pipeline regex below
# matches them, so once step 3 substitutes them in, they pass through steps
# 4-8 inertly until step 9 restores them right after the brace strip.
_LBRACE_PLACEHOLDER = ""
_RBRACE_PLACEHOLDER = ""


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
       ``\\mathsf{G}`` and the other temporal/deontic/agentive markers,
       ``\\mathord{!}``, ``\\mathbin{\\&}``, ``\\mathbf{1}``, ``\\left(`` /
       ``\\right)`` grouping, ``{:}`` the sort colon).
    2. Unwrap any REMAINING ``\\mathsf{name}`` (a hybrid-logic nominal — every
       KNOWN ``\\mathsf{...}`` operator form was already consumed in step 1).
    3. Protect escaped literal braces ``\\{`` / ``\\}`` (cardinality terms,
       slashed existentials) behind placeholders so step 9 does not erase them.
    4. Unescape ``\\_`` to a literal underscore (the ``c_``-constant escape that
       ``to_latex`` emits) so it is not later read as a subscript operator.
    5. Unwrap ``\\mathrm{Sort}`` to ``Sort``.
    6. Collapse generic subscript braces ``X_{...}`` to ``X_...``, then tighten
       the hybrid satisfaction operator's ``@_i`` to ``@i`` (its underscore is a
       renderer artefact, unlike the agent operators' K_a/B_a/Say_a/Want_a).
    7. Delete the non-letter spacing macros (``\\,`` ``\\;`` ``\\!`` and a
       backslash-space) BEFORE mapping control sequences: the ``backslash``
       control sequence (Lambek's *under* connective) maps to a literal
       backslash character, and if spacing deletion ran afterwards it would
       mistake that freshly-produced backslash — now followed by a plain
       space, e.g. ``A \\ B`` — for a backslash-space spacing macro and erase
       it, silently dropping the connective.
    8. Map every remaining backslash control sequence by its full letter run
       (longest-match), covering both the ``to_latex`` glyphs and common
       hand-written synonyms; the letter-run spacing macros map to nothing.
    9. Collapse the counting quantifier's exponent (``\\exists^{\\geq 3}`` ->
       ``∃≥3``), then strip leftover grouping braces ``{`` ``}`` (LaTeX
       grouping carries no information the parser needs) and restore the
       placeholders from step 3 to real literal braces.
    10. Collapse redundant whitespace.
    """
    s = text

    # 1. Multi-token brace constructs, most specific first.
    for src, dst in _MULTI_TOKEN:
        s = s.replace(src, dst)

    # 2. Any \mathsf{...} surviving step 1 is a nominal (or an unrecognised
    #    hand-written \mathsf wrapping) — unwrap it to its bare name.
    s = _MATHSF.sub(r"\1", s)

    # 3. Protect escaped literal braces from the brace-strip in step 9.
    s = s.replace("\\{", _LBRACE_PLACEHOLDER).replace("\\}", _RBRACE_PLACEHOLDER)

    # 4. Unescape the c_-constant underscore escape (\_  ->  _). Done before the
    #    subscript-brace and control-sequence passes so the bare underscore in a
    #    name like c_zero survives intact.
    s = s.replace("\\_", "_")

    # 5. Unwrap \mathrm{Sort}.
    s = _MATHRM.sub(r"\1", s)

    # 6. Generic subscript braces  X_{...} -> X_...  then @_i -> @i.
    s = _SUBSCRIPT_BRACES.sub(r"_\1", s)
    s = _AT_UNDERSCORE.sub(r"@\1", s)

    # 7. Non-letter LaTeX spacing macros — deliberately BEFORE control
    #    sequences (see the docstring above: a literal backslash produced by
    #    step 8's "backslash" mapping must not be mistaken for a spacing macro).
    s = _SPACING_NONLETTER.sub(" ", s)

    # 8. Backslash control sequences (longest letter run wins).
    s = _CONTROL_SEQ.sub(_replace_control_seq, s)

    # 9. Counting-quantifier exponent, then leftover-brace stripping / restore.
    s = _COUNT_EXPONENT.sub(lambda m: f"∃{m.group(1)}{m.group(2)}", s)
    s = s.replace("{", "").replace("}", "")
    s = s.replace(_LBRACE_PLACEHOLDER, "{").replace(_RBRACE_PLACEHOLDER, "}")

    # 10. Collapse redundant whitespace.
    s = re.sub(r"\s+", " ", s).strip()

    # 11. Tighten the sort colon: the grammar's SORT terminal is /:[A-Z][...]*/ ,
    #    which admits no whitespace before the ':' or between ':' and the sort
    #    name. ``to_latex`` emits the colon glued (``x{:}\mathrm{Human}``), but a
    #    person may hand-write ``x {:} \mathrm{Human}`` or ``x : Human``; the
    #    spaces introduced by steps 1/8/10 would then split the SORT token. Since
    #    ':' occurs nowhere else in any grammar, removing whitespace flanking it
    #    is unambiguous and only ever reconstructs a sort annotation.
    s = re.sub(r"\s*:\s*", ":", s)
    return s


def parse_latex(text: str, many_sorted: bool = False, fuzzy: bool = False,
                modal: bool = False, second_order: bool = False,
                dependence: bool = False, linear: bool = False,
                lambek: bool = False) -> "object":
    """Parse a LaTeX math-mode formula into an AST node.

    Translates ``text`` to the toolkit's Unicode surface syntax with
    :func:`latex_to_unicode`, then parses it with :class:`MSFLParser` in the
    selected mode. The mode flags are passed straight through to
    :class:`MSFLParser`, including its mutual-exclusivity rules (e.g.
    ``dependence=True`` cannot be combined with any other flag).

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
        dependence: parse the team-semantic dependence/IF fragment. Standalone.
        linear: parse propositional intuitionistic linear logic. Standalone.
        lambek: parse Lambek-calculus category types. Standalone.

    Returns:
        The parsed AST :class:`~unicode_fol_kit.fol.nodes.Node`.
    """
    unicode_text = latex_to_unicode(text)
    parser = MSFLParser(
        many_sorted=many_sorted,
        fuzzy=fuzzy,
        modal=modal,
        second_order=second_order,
        dependence=dependence,
        linear=linear,
        lambek=lambek,
    )
    return parser.parse(unicode_text)
