"""Parser-registry equivalence + self-assembly guard (Phase 2).

MSFLParser builds its grammar AND its transformer from the operator registry
(``build_grammar`` / ``build_transform_handlers`` over ``PARSER_OPS``) — there is
no per-mode hand-written transformer or hand-loaded ``.lark`` file on the runtime
path. These tests pin that machinery down:

1.  **Equivalence** — for every mode and a broad formula corpus, the registry
    parser (the live ``MSFLParser``) produces an AST byte-identical to the legacy
    reference parser assembled the old way (``Lark.open(<mode>.lark)`` + the
    hand-written ``*Transformer``). The legacy grammars + transformers are retained
    ONLY as this frozen reference oracle; the six v1 modes have mathematically
    fixed operator sets, so this guard never forces a shared-file edit. A *new*
    logic extends the registry alone and is covered by test 3.

2.  **Structure** — each generated grammar is well-formed and exposes exactly the
    operator rule-aliases expected for its mode.

3.  **Self-assembly** — a brand-new operator can be registered into the grammar +
    transformer purely through ``register_parser_op``, with no edit to msflparser
    or any grammar file. This is the decoupling Phase 2 exists to provide. Global
    registry state is restored afterwards.
"""

import pathlib

import pytest
from lark import Lark, UnexpectedCharacters, UnexpectedToken, UnexpectedEOF
from lark.exceptions import VisitError

from unicode_fol_kit.fol.msflparser import (
    MSFLParser,
    LambdaTransformer, MSFOLTransformer, MSFLTransformer, FLTransformer,
    ModalTransformer, SecondOrderTransformer,
)
from unicode_fol_kit.fol._msfl_nodes import resolve_lambda_scope
from unicode_fol_kit.fol._fol_nodes import (
    Not, build_grammar, build_transform_handlers, register_parser_op, PARSER_OPS,
)
from unicode_fol_kit.fol.naming import NamingError, ParsingError

_GDIR = (pathlib.Path(__file__).parent.parent
         / "unicode_fol_kit" / "fol" / "grammars").resolve()

# self._mode -> (legacy .lark file, legacy hand-written transformer class)
_LEGACY = {
    "fol":   ("fol.lark",   LambdaTransformer),
    "msfol": ("msfol.lark", MSFOLTransformer),
    "msfl":  ("msfl.lark",  MSFLTransformer),
    "fl":    ("fl.lark",    FLTransformer),
    "modal": ("modal.lark", ModalTransformer),
    "so":    ("so.lark",    SecondOrderTransformer),
}
# self._mode -> MSFLParser kwargs
_KW = {
    "fol": {}, "msfol": {"many_sorted": True},
    "msfl": {"many_sorted": True, "fuzzy": True}, "fl": {"fuzzy": True},
    "modal": {"modal": True}, "so": {"second_order": True},
}


def _legacy_parse(mode, text):
    """Parse with the legacy reference pipeline (Lark.open + hand transformer)."""
    fname, tcls = _LEGACY[mode]
    parser = Lark.open(str(_GDIR / fname), parser="earley")
    transformer = tcls()
    try:
        tree = parser.parse(text)
        return resolve_lambda_scope(transformer.transform(tree))
    except (UnexpectedCharacters, UnexpectedToken, UnexpectedEOF) as e:
        return ("PARSE_ERR", type(e).__name__)
    except VisitError as e:
        return ("VISIT_ERR", type(e.orig_exc).__name__)


def _registry_parse(mode, text):
    """Parse with the live MSFLParser (registry-assembled grammar + transformer).

    Errors are normalised to the same tuple shapes _legacy_parse produces so the
    two pipelines compare equal on rejected input too. A NamingError mirrors a
    lexer UnexpectedCharacters; a plain ParsingError mirrors UnexpectedToken/EOF;
    a ConflictingArityError mirrors the VisitError-unwrapped arity failure.
    """
    parser = MSFLParser(**_KW[mode])
    try:
        return parser.parse(text)
    except NamingError:
        return ("PARSE_ERR", "UnexpectedCharacters")
    except ParsingError as e:
        if type(e).__name__ == "ConflictingArityError":
            return ("VISIT_ERR", "ConflictingArityError")
        return ("PARSE_ERR", type(e).__name__)


# A broad corpus per mode: every operator, both associativities, precedence
# crossings, grouping, quantifiers (incl. second-order arity inference + shadowing
# + conflicting-arity), terms/arithmetic/infix predicates, sorted constants, and
# the lambda/application layer.
CORPUS = {
    "fol": [
        "P", "Q(x)", "R(x,y)", "S(a, b, c)", "P(c_1)", "P(alice)", "P(3)", "P(3.5)",
        "x < y", "x = a", "x ≤ y", "x ≥ b", "x ≠ y", "f(x) > g(y)",
        "x + y = z", "x * y + z = w", "a - b * c = d", "x / y = z", "P(x + y)",
        "f(2) + 1 = 3",
        "¬P", "¬¬P", "¬P(x)",
        "P ∧ Q", "P ∨ Q", "P ⊕ Q", "P ∧ Q ∧ R", "P ∨ Q ∨ R", "P ⊕ Q ⊕ R",
        "P → Q", "P ↔ Q", "P → Q → R", "P ↔ Q ↔ R",
        "P ∧ Q → R", "¬P ∨ Q", "P → Q ∧ R", "P ↔ Q → R", "¬P ∧ Q → R ∨ S ↔ T",
        "(P ∨ Q) ∧ R", "[P → Q]", "(P)", "¬(P ∧ Q)",
        "∀x P(x)", "∃x P(x)", "∀x ∃y R(x,y)", "∀x (P(x) → Q(x))", "∀x ¬P(x)",
        "∃x P(x) ∧ Q", "∀x ∀y ∀z R(x,y) → R(y,z)",
        "λx. P(x)", "λP. P(a)", "λx. λy. R(x,y)", "(λx. P(x))(a)", "(λx. P(x))(y)",
        "(λx. P(x))(c_1)",
    ],
    "msfol": [
        "P", "Q(x)", "R(x,y)", "P(c_1)", "P(3)",
        "∀x:Human P(x)", "∃x:Animal Q(x)", "∀x:Human ∃y:Animal R(x,y)",
        "P(alice:Human)", "R(a:T, b:U)", "P(c_1:Human)",
        "P ∧ Q → R", "¬P ↔ Q", "¬¬P", "P ∧ Q ∧ R", "P ∨ Q",
        "∀x:Human (P(x) → Q(x))", "x = y", "x < y", "f(x) + 1 = y",
        "λx. P(x)", "(λx. P(x))(a)",
    ],
    "msfl": [
        "P", "Q(x)", "R(x,y)",
        "P ∧ Q", "P ∨ Q", "P ⊗ Q", "P ⊕ Q", "P ⊗ Q ⊗ R", "P ⊕ Q ⊕ R",
        "¬P", "¬¬P", "P → Q", "P ↔ Q", "P → Q → R",
        "P ⊗ Q → R", "¬P ⊕ Q", "(P ⊕ Q) ⊗ R",
        "∀x:Human P(x)", "∃x:Animal Q(x)", "P(alice:Human)",
        "∀x:Human (P(x) → Q(x))",
        "λx. P(x)", "(λx. P(x))(a)",
    ],
    "fl": [
        "P", "Q(x)", "R(x,y)", "P(c_1)",
        "P ∧ Q", "P ∨ Q", "P ⊗ Q", "P ⊕ Q",
        "¬P", "¬¬P", "P → Q", "P ↔ Q", "P → Q → R",
        "P ⊗ Q → R", "¬P ⊕ Q",
        "∀x P(x)", "∃x P(x)", "∀x ∃y R(x,y)", "∀x (P(x) → Q(x))",
        "λx. P(x)", "(λx. P(x))(a)",
    ],
    "modal": [
        "P", "P(x)", "R(x,y)", "x = y", "f(x) + 1 = y", "P(c_1)", "P(alice)",
        "□P", "◇P", "ⒼP", "ⒻP", "ⓃP", "ⓄP", "ⓅP",
        "K_alice P", "B_bob Q(x)", "K_alice (P → Q)",
        "□◇P", "¬□P", "□¬P", "□(P ∧ Q)", "◇P ∨ Q", "◇P ∧ Q",
        "P Ⓤ Q", "P Ⓤ Q Ⓤ R", "P ∧ Q Ⓤ R", "P Ⓤ Q → R", "□P Ⓤ ◇Q",
        "∀x □P(x)", "□∀x P(x)", "∀x (P(x) → ◇Q(x))", "∃x ◇P(x)",
        "P ∧ Q → R", "¬P ↔ Q", "P ⊕ Q", "P → Q → R", "(P ∨ Q) ∧ R",
        "K_alice B_bob P", "□K_alice P", "◇ⒻP",
        "λx. □P(x)", "(λx. □P(x))(a)", "ⒼⒻP", "ⓃP Ⓤ Q",
    ],
    "so": [
        "P", "P(x)", "R(x,y)", "x = y", "P(c_1)", "P(alice)",
        "∀x P(x)", "∃x R(x,y)", "∀x ∃y R(x,y)",
        "∀P P(a)", "∃P P(x)", "∀P ∀x (P(x) → P(x))", "∃P ∀x P(x)",
        "∀P (P(a) → P(b))", "∀P (P → P)", "∃P P",
        "∀P ∀x ∀y (P(x,y) → P(y,x))", "∃R ∀x R(x,x)",
        "∀P (P(a) ∧ ∃P P(b,c))",
        "∀x ∃P P(x)", "∀P ∃x P(x)",
        "P ∧ Q → R", "¬P", "P ⊕ Q", "P → Q → R",
        "∀P (P(a) ∧ P(b,c))",  # conflicting arity -> error in BOTH pipelines
        "λx. P(x)", "(λx. P(x))(a)",
    ],
}

_PARAMS = [(m, f) for m in CORPUS for f in CORPUS[m]]


@pytest.mark.parametrize("mode,text", _PARAMS,
                         ids=[f"{m}:{f}" for m, f in _PARAMS])
def test_registry_matches_legacy(mode, text):
    """Registry-assembled MSFLParser == legacy hand-written parser, byte-for-byte."""
    assert _registry_parse(mode, text) == _legacy_parse(mode, text)


# Expected operator rule-aliases the assembled grammar/transformer must expose.
_EXPECTED_ALIASES = {
    "fol": {"not_", "and_", "or_", "xor_", "implies_", "iff_", "quantifier_"},
    "msfol": {"not_", "and_", "or_", "implies_", "iff_",
              "sorted_quantifier_", "sorted_const_"},
    "msfl": {"luk_not_", "weak_and_", "weak_or_", "strong_and_", "strong_or_",
             "luk_implies_", "luk_iff_", "sorted_quantifier_", "sorted_const_"},
    "fl": {"luk_not_", "weak_and_", "weak_or_", "strong_and_", "strong_or_",
           "luk_implies_", "luk_iff_", "quantifier_"},
    "modal": {"not_", "and_", "or_", "xor_", "implies_", "iff_", "quantifier_",
              "box_", "diamond_", "always_", "eventually_", "next_",
              "knows_", "believes_", "obligatory_", "permitted_", "until_"},
    "second_order": {"not_", "and_", "or_", "xor_", "implies_", "iff_",
                     "quantifier_", "second_order_quantifier_"},
}


@pytest.mark.parametrize("reg_mode", sorted(_EXPECTED_ALIASES))
def test_generated_grammar_is_wellformed_and_complete(reg_mode):
    """build_grammar(mode) compiles, and exposes exactly its expected operators."""
    grammar = build_grammar(reg_mode)
    Lark(grammar, parser="earley", import_paths=[str(_GDIR)])  # compiles cleanly
    aliases = set(build_transform_handlers(reg_mode))
    assert aliases == _EXPECTED_ALIASES[reg_mode]


def test_new_operator_self_registers_without_touching_parser():
    """A brand-new operator joins the grammar+transformer via register_parser_op
    alone — no edit to msflparser.py or any .lark file. Restores registry state."""
    n_before = len(PARSER_OPS)
    sentinel = object()
    register_parser_op(
        Not, "fol", "prefix", "toy_op_", "TOYOP prefix",
        lambda items: (sentinel, items[1]),
        terminal_name="TOYOP", terminal_def='TOYOP: "✦"',
    )
    try:
        grammar = build_grammar("fol")
        parser = Lark(grammar, parser="earley", import_paths=[str(_GDIR)])
        transformer = LambdaTransformer()
        for alias, fn in build_transform_handlers("fol").items():
            setattr(transformer, alias, fn)
        result = transformer.transform(parser.parse("✦P"))
        assert isinstance(result, tuple) and result[0] is sentinel
        assert result[1].predicate == "P"
    finally:
        del PARSER_OPS[n_before:]  # pop the toy op; restore global registry
    assert len(PARSER_OPS) == n_before
