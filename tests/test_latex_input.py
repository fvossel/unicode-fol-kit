"""Tests for latex_input: reading LaTeX math-mode back into the toolkit's AST.

Two layers of assurance:

* ROUND-TRIP — the key property. ``latex_input`` is the declared inverse of
  ``node.to_latex()``. For a spread of formulas across every mode, building a
  ground-truth AST with MSFLParser, rendering it with ``to_latex()``, and
  parsing that LaTeX back with ``parse_latex`` (in the matching mode) must
  return a structurally equal AST.

* HAND-WRITTEN LaTeX — a person typing LaTeX uses synonyms (``\\to`` for
  ``\\rightarrow``, ``\\neg`` for ``\\lnot``, ``\\wedge`` ``\\vee`` ``\\le`` …)
  and casual spacing. These must parse to exactly the same AST as the
  equivalent Unicode source.

Plus small unit checks on ``latex_to_unicode`` fragments.
"""

import pytest

from unicode_fol_kit.fol.msflparser import MSFLParser
from unicode_fol_kit.fol.latex_input import latex_to_unicode, parse_latex


# ---------------------------------------------------------------------------
# Round-trip:  parse_latex(ast.to_latex(), <mode>) == ast
# ---------------------------------------------------------------------------
#
# Each row is (source, mode-kwargs). The source is parsed once to get a
# ground-truth AST; that AST is rendered to LaTeX and parsed back, and the two
# ASTs must be equal.

_FOL = {}
_MSFOL = {"many_sorted": True}
_MSFL = {"many_sorted": True, "fuzzy": True}
_MODAL = {"modal": True}
_SO = {"second_order": True}
_DEP = {"dependence": True}
_LIN = {"linear": True}
_LAM = {"lambek": True}

_ROUND_TRIP = [
    # FOL.
    ("∀x (P(x) → Q(x))", _FOL),
    ("¬(P ∧ Q)", _FOL),
    ("x * y = z", _FOL),
    ("x ≤ y", _FOL),
    ("x ≠ y", _FOL),
    ("∀x ∃y R(x, y)", _FOL),
    ("(P ∨ Q) ↔ (Q ∨ P)", _FOL),
    ("P(c_zero) ∧ Q(c_one)", _FOL),
    ("x + y ≥ z", _FOL),
    # MSFOL — sorted quantifiers and a sorted constant.
    ("∀x:Human P(x)", _MSFOL),
    ("P(alice:Human)", _MSFOL),
    ("∀x:Human ∃y:Dog Loves(x, y)", _MSFOL),
    # MSFL — Łukasiewicz strong connectives.
    ("P(x) ⊗ Q(x)", _MSFL),
    ("P(x) ⊕ Q(x)", _MSFL),
    ("∀x:Human (P(x) ⊗ Q(x))", _MSFL),
    # Modal / epistemic / temporal / deontic.
    ("□P → ◇Q", _MODAL),
    ("K_alice P", _MODAL),
    ("B_bob (P ∧ Q)", _MODAL),
    ("Ⓖ(P → Ⓕ Q)", _MODAL),
    ("Ⓞ P", _MODAL),
    ("Ⓟ Q", _MODAL),
    ("P Ⓤ Q", _MODAL),
    ("Ⓝ P → P Ⓤ Q", _MODAL),
    # Deeper modal nesting and Until associativity.
    ("□(P → Q) → (□P → □Q)", _MODAL),
    ("(P Ⓤ Q) Ⓤ R", _MODAL),
    ("P Ⓤ (Q Ⓤ R)", _MODAL),
    ("K_alice (P ∧ Q) → B_bob (P ∨ Q)", _MODAL),
    # Second-order — arity inferred from the body, never printed.
    ("∀P P(x)", _SO),
    ("∃P P(x, y)", _SO),
    ("∀P (P(x) → P(y))", _SO),
    ("∃P ∀x P(x)", _SO),
    ("∀P ∃Q (P(x) → Q(x))", _SO),
    ("∀P P", _SO),
    ("∀P ∀Q (P(x, y) ↔ Q(y, x))", _SO),
    # Heavier FOL precedence / nesting.
    ("(P → Q) → ((Q → R) → (P → R))", _FOL),
    ("(P ↔ Q) ↔ R", _FOL),
    ("∀x (∃y R(x, y) → ∀z S(x, z))", _FOL),
    ("x * y + z = w", _FOL),
    ("(x + y) * z = w", _FOL),
    ("x - (y - z) = w", _FOL),
    # Previously-broken LaTeX round trips (see tests/test_latex_roundtrip.py for
    # the exhaustive per-operator battery — these are a few representative
    # spot checks, curated the way the rest of this table is).
    ("Say_alice P → Want_bob Q", _MODAL),          # \mathsf{Say}_{alice} / \mathsf{Want}_{bob}
    ("(P ∧ Q) □→ R", _MODAL),                       # \mathbin{\Box\!\rightarrow}
    ("(P ∧ Q) ◇→ R", _MODAL),                       # \mathbin{\Diamond\!\rightarrow}
    ("(P Ⓒ Q) ∧ R", _FOL),                          # \mathbin{\mathsf{C}}
    ("@i (P ∧ Q)", _MODAL),                         # @_{i} (underscore must drop)
    ("∃≥3 x P(x) → ∃≤5 y Q(y)", _FOL),               # \exists^{\geq n} exponent form
    ("∃=0 x P(x)", _FOL),
    ("P(|{v : Votes(v)}|, |{w : Q(w)}|)", _FOL),      # escaped \{ \} through the pipeline
    ("∀x:Human (P(|{v:Human : Votes(v)}|) → Q(x))", _MSFOL),
    ("i ∧ @j P", _MODAL),                            # bare nominal + satisfaction operator
    ("μ(x, height) > μ(y, height)", _FOL),
    # Dependence / linear / lambek modes.
    ("=(x, y) ∧ P(x)", _DEP),
    ("∃x/{y} R(x, y)", _DEP),
    ("A ⊗ B", _LIN),
    ("A ⊸ (B & C)", _LIN),
    ("!A ⊗ !A", _LIN),
    ("𝟙", _LIN),
    ("(A • B) \\ C", _LAM),
    ("A / (B • C)", _LAM),
]


@pytest.mark.parametrize("source, mode", _ROUND_TRIP)
def test_round_trip_latex(source, mode):
    """parse_latex(ast.to_latex(), <matching mode>) reproduces the AST exactly."""
    ast = MSFLParser(**mode).parse(source)
    latex = ast.to_latex()
    back = parse_latex(latex, **mode)
    assert back == ast, (
        f"round-trip mismatch for {source!r}\n"
        f"  latex   = {latex!r}\n"
        f"  unicode = {latex_to_unicode(latex)!r}\n"
        f"  back    = {back!r}"
    )


# ---------------------------------------------------------------------------
# Hand-written LaTeX with synonyms == the equivalent Unicode parse
# ---------------------------------------------------------------------------

_HAND_WRITTEN = [
    (r"\forall x (P(x) \to Q(x))", "∀x (P(x) → Q(x))", _FOL),
    (r"\neg (P \wedge Q)", "¬(P ∧ Q)", _FOL),
    (r"P \vee \lnot P", "P ∨ ¬P", _FOL),
    (r"x \le y", "x ≤ y", _FOL),
    (r"\exists y\, R(x,y)", "∃y R(x, y)", _FOL),
    (r"x \ge y \land x \neq y", "x ≥ y ∧ x ≠ y", _FOL),
    (r"P \iff Q", "P ↔ Q", _FOL),
    (r"x \times y = z", "x * y = z", _FOL),
    (r"\forall x\; (P(x) \implies Q(x))", "∀x (P(x) → Q(x))", _FOL),
    # Control-sequence shadowing torture: \le vs \leq vs \leftrightarrow must
    # each resolve on the full letter run, never a prefix.
    (r"x \le y \leftrightarrow x \leq y", "x ≤ y ↔ x ≤ y", _FOL),
    (r"\lnot P \lor \lnot Q", "¬P ∨ ¬Q", _FOL),       # \lnot vs \lor
    (r"\neg \neg \neg P", "¬¬¬P", _FOL),
    (r"x \ne y", "x ≠ y", _FOL),
    (r"a \cdot b = c", "a * b = c", _FOL),
    # Messy grouping: \left/\right, nested and doubled braces, doubled spacing.
    (r"\forall x\, \left( P(x) \rightarrow Q(x) \right)", "∀x (P(x) → Q(x))", _FOL),
    (r"{\neg {(P \land Q)}}", "¬(P ∧ Q)", _FOL),
    (r"P \,\, \lor \,\, \lnot P", "P ∨ ¬P", _FOL),
    # Hand-written sort colons with stray spaces around {:} / before the sort.
    (r"\forall x {:} \mathrm{Human} \; P(x)", "∀x:Human P(x)", _MSFOL),
    (r"R(alice {:} \mathrm{Human}, bob {:} \mathrm{Human})",
     "R(alice:Human, bob:Human)", _MSFOL),
    # Hand-written epistemic agents with braced subscripts.
    (r"K_{alice} B_{bob} P", "K_alice B_bob P", _MODAL),
    (r"\mathsf{G}(P \rightarrow \mathsf{F} Q)", "Ⓖ(P → Ⓕ Q)", _MODAL),
    (r"P \mathbin{\mathsf{U}} Q", "P Ⓤ Q", _MODAL),
    # c_-constant in both escape conventions a person might type.
    (r"P(c\_zero)", "P(c_zero)", _FOL),
    (r"P(c_{zero})", "P(c_zero)", _FOL),
]


@pytest.mark.parametrize("latex, unicode_src, mode", _HAND_WRITTEN)
def test_hand_written_latex(latex, unicode_src, mode):
    """Hand-written LaTeX (synonyms, casual spacing) parses like its Unicode twin."""
    assert parse_latex(latex, **mode) == MSFLParser(**mode).parse(unicode_src)


# ---------------------------------------------------------------------------
# latex_to_unicode fragment unit checks
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("latex, expected", [
    (r"\mathrm{Human}", "Human"),
    (r"{:}", ":"),
    (r"\mathbin{\mathsf{U}}", "Ⓤ"),
    (r"\mathsf{G}", "Ⓖ"),
    (r"\mathsf{F}", "Ⓕ"),
    (r"\mathsf{X}", "Ⓝ"),
    (r"\mathsf{O}", "Ⓞ"),
    (r"\mathsf{P}", "Ⓟ"),
    (r"K_{alice}", "K_alice"),
    (r"B_{bob}", "B_bob"),
    (r"c\_zero", "c_zero"),
    (r"\Box", "□"),
    (r"\Diamond", "◇"),
    (r"\leftrightarrow", "↔"),      # longest-match: not shadowed by \le
    (r"\leq", "≤"),                 # \leq not shadowed by \le
    (r"\left( P \right)", "( P )"),
    (r"alice{:}\mathrm{Human}", "alice:Human"),
    # Sort colon is tightened even when the hand-writer spaces it out, because
    # the grammar's SORT terminal admits no surrounding whitespace.
    (r"x {:} \mathrm{Human}", "x:Human"),
    (r"alice : Human", "alice:Human"),
    # --- New fixes ---
    # \mathsf{Say} / \mathsf{Want} multi-token forms (agent_prefix operators).
    (r"\mathsf{Say}", "Say"),
    (r"\mathsf{Want}", "Want"),
    (r"\mathsf{Say}_{alice}", "Say_alice"),
    # Contrast and the counterfactual arrows.
    (r"\mathbin{\mathsf{C}}", "Ⓒ"),
    (r"\mathbin{\Box\!\rightarrow}", "□→"),
    (r"\mathbin{\Diamond\!\rightarrow}", "◇→"),
    # Hybrid satisfaction operator: the underscore is a renderer artefact and
    # must be dropped, unlike K_a/B_a/Say_a/Want_a where it's part of the token.
    (r"@_{i}", "@i"),
    (r"@_i", "@i"),
    (r"K_{alice}", "K_alice"),      # unaffected: agent operators KEEP their underscore
    # A bare \mathsf{name} left after every known operator form is consumed is
    # a hybrid-logic nominal (the generic catch-all unwrap).
    (r"\mathsf{i}", "i"),
    (r"\mathsf{j1}", "j1"),
    # Counting quantifier exponent forms.
    (r"\exists^{\geq 3}", "∃≥3"),
    (r"\exists^{\leq 5}", "∃≤5"),
    (r"\exists^{= 0}", "∃=0"),
    # Cardinality's escaped literal braces survive the generic brace strip.
    # (The ':' separator is tightened like a sort colon by the final pass —
    # harmless here, since the grammar ignores whitespace around it too; see
    # test_round_trip_latex's Cardinality/SortedCardinality cases, which
    # confirm the tightened form still parses back to the identical AST.)
    (r"\lvert\{v : \phi\}\rvert".replace(r"\phi", "P"), "|{v:P}|"),
    (r"\lvert\{v{:}\mathrm{Human} : P\}\rvert", "|{v:Human:P}|"),
    # Slashed existential's escaped literal braces (the slash set).
    (r"\exists x / \{y, z\}\, P", "∃ x / {y, z} P"),
    # Linear-logic multi-token forms.
    (r"\mathord{!}", "!"),
    (r"\mathbin{\&}", "&"),
    (r"\mathbf{1}", "𝟙"),
    # New control-sequence entries.
    (r"\mu(x, y)", "μ(x, y)"),
    (r"\multimap", "⊸"),
    (r"\bullet", "•"),
    (r"A \backslash B", "A \\ B"),
])
def test_latex_to_unicode_fragments(latex, expected):
    """Individual construct translations and spacing/brace handling."""
    assert latex_to_unicode(latex) == expected


def test_spacing_removed():
    """All LaTeX spacing macros collapse away, leaving a single clean separator."""
    assert latex_to_unicode(r"P\,\;\!\quad\qquad Q") == "P Q"


def test_grouping_braces_stripped():
    """Bare LaTeX grouping braces are dropped (precedence is explicit elsewhere)."""
    assert latex_to_unicode(r"{P \land Q}") == "P ∧ Q"


def test_backslash_control_sequence_not_eaten_by_spacing_cleanup():
    """The 'backslash' control sequence (Lambek's \\ connective) must survive.

    Regression pin: mapping \\backslash to a literal backslash BEFORE the
    non-letter spacing-macro cleanup ran used to make that cleanup mistake the
    freshly-produced "\\ " (backslash + space) for a backslash-space spacing
    macro and delete it, silently dropping the connective. See the ordering
    note in latex_to_unicode's docstring (step 7 before step 8).
    """
    assert latex_to_unicode(r"A \backslash B") == "A \\ B"


def test_escaped_braces_protected_through_full_pipeline():
    """Cardinality's escaped \\{ \\} survive control-sequence + brace-strip."""
    assert latex_to_unicode(r"\lvert\{v : Votes(v)\}\rvert") == "|{v:Votes(v)}|"


def test_mathsf_nominal_unwrap_does_not_shadow_known_operators():
    """The generic \\mathsf unwrap only fires on names no specific rule claimed."""
    # Known operator forms still resolve to their glyphs, not to bare names.
    assert latex_to_unicode(r"\mathsf{G}") == "Ⓖ"
    assert latex_to_unicode(r"\mathsf{Say}_{alice}") == "Say_alice"
    # Anything else \mathsf-wrapped is unwrapped as a bare (nominal) name.
    assert latex_to_unicode(r"\mathsf{k}") == "k"
