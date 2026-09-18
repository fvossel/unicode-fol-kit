"""Parser-registry structure + self-assembly guards.

``MSFLParser`` builds its grammar AND its transformer from the operator registry
(``build_grammar`` / ``build_transform_handlers`` over ``PARSER_OPS``) on a shared
``LambdaTransformer`` base — there is no per-mode hand-written transformer or
hand-loaded ``.lark`` file on the runtime path (only ``terminals.lark`` is imported by
the generated grammar). These tests pin that machinery down:

1.  **Structure** — each generated grammar compiles and exposes exactly the operator
    rule-aliases expected for its mode.
2.  **Self-assembly** — a brand-new operator joins the grammar + transformer purely
    through ``register_parser_op``, with no edit to ``msflparser.py`` or any grammar
    file. Global registry state is restored afterwards.

(The original migration was additionally pinned by a byte-for-byte *equivalence* test
against the legacy hand-written ``.lark`` grammars + ``*Transformer`` classes. That
reference pipeline was retired once the equivalence was established; the per-mode
grammars and transformers it relied on are gone.)
"""

import pathlib

import pytest
from lark import Lark

from unicode_fol_kit.fol.msflparser import LambdaTransformer
from unicode_fol_kit.fol._fol_nodes import (
    Not, build_grammar, build_transform_handlers, register_parser_op, PARSER_OPS,
)

_GDIR = (pathlib.Path(__file__).parent.parent
         / "unicode_fol_kit" / "fol" / "grammars").resolve()


# Expected operator rule-aliases the assembled grammar/transformer must expose.
_EXPECTED_ALIASES = {
    "fol": {"not_", "and_", "or_", "xor_", "implies_", "iff_", "quantifier_",
            "count_", "contrast_"},
    "msfol": {"not_", "and_", "or_", "xor_", "implies_", "iff_",
              "sorted_quantifier_", "sorted_const_",
              "contrast_", "sorted_count_", "sorted_cardinality_"},
    "msfl": {"luk_not_", "weak_and_", "weak_or_", "strong_and_", "strong_or_",
             "luk_implies_", "luk_iff_", "sorted_quantifier_", "sorted_const_"},
    "fl": {"luk_not_", "weak_and_", "weak_or_", "strong_and_", "strong_or_",
           "luk_implies_", "luk_iff_", "quantifier_"},
    "modal": {"not_", "and_", "or_", "xor_", "implies_", "iff_", "quantifier_",
              "count_", "contrast_",
              "box_", "diamond_", "always_", "eventually_", "next_",
              "knows_", "believes_", "says_", "wants_",
              "obligatory_", "permitted_", "until_",
              "historically_", "once_", "previous_", "since_",
              "would_", "might_",
              "announce_", "announce_diamond_",
              "everybody_knows_", "distributed_knowledge_", "common_knowledge_",
              "nominal_", "at_", "down_"},
    "second_order": {"not_", "and_", "or_", "xor_", "implies_", "iff_",
                     "quantifier_", "second_order_quantifier_",
                     "count_", "contrast_"},
    # modal_sorted / so_sorted (C3): "modal"/"second_order" cloned onto
    # "msfol"'s SORTED quantifier/count/const/cardinality forms, with
    # "modal"'s/"second_order"'s own UNSORTED quantifier_/count_ excluded
    # (see fol/nodes.py's _clone_parser_ops_sorted) — so each is exactly its
    # base mode's aliases, minus {quantifier_, count_}, plus msfol's sorted
    # binder aliases (the classical connectives + contrast_ overlap and
    # dedupe to one copy, same as third_order/third_order_modal already do).
    "modal_sorted": {"not_", "and_", "or_", "xor_", "implies_", "iff_",
                     "sorted_quantifier_", "sorted_const_", "contrast_",
                     "sorted_count_", "sorted_cardinality_",
                     "box_", "diamond_", "always_", "eventually_", "next_",
                     "knows_", "believes_", "says_", "wants_",
                     "obligatory_", "permitted_", "until_",
                     "historically_", "once_", "previous_", "since_",
                     "would_", "might_",
                     "announce_", "announce_diamond_",
                     "everybody_knows_", "distributed_knowledge_", "common_knowledge_",
                     "nominal_", "at_", "down_"},
    "so_sorted": {"not_", "and_", "or_", "xor_", "implies_", "iff_",
                  "sorted_quantifier_", "sorted_const_", "contrast_",
                  "sorted_count_", "sorted_cardinality_",
                  "second_order_quantifier_"},
    "dependence": {"not_", "and_", "or_", "quantifier_", "dep_", "slashed_"},
    "linear": {"tensor_", "with_", "oplus_", "limp_", "ofcourse_", "one_",
               "top_", "zero_"},
    "lambek": {"product_", "under_", "over_"},
}


@pytest.mark.parametrize("reg_mode", sorted(_EXPECTED_ALIASES))
def test_generated_grammar_is_wellformed_and_complete(reg_mode):
    """build_grammar(mode) compiles, and exposes exactly its expected operators."""
    grammar = build_grammar(reg_mode)
    Lark(grammar, parser="earley", import_paths=[str(_GDIR)])  # compiles cleanly
    aliases = set(build_transform_handlers(reg_mode))
    assert aliases == _EXPECTED_ALIASES[reg_mode]


def test_down_inherited_by_modes_that_clone_modal_operators():
    """N1 design decision, pinned: the ↓ binder (rule alias ``down_``) is
    registered ONLY for ``"modal"`` (see fol._hybrid_nodes), exactly like
    ``Nominal``/``At`` before it — and, exactly like ``Nominal``/``At``, it is
    then picked up FOR FREE by every mode that clones "modal"'s operator set
    wholesale: ``"third_order_modal"`` (tomodal, fol.nodes' plain
    ``_clone_parser_ops``) and ``"modal_sorted"`` (fol.nodes'
    ``_clone_parser_ops_sorted``, which excludes only the UNSORTED
    quantifier_/count_ aliases — "down_" binds a Nominal, not an individual
    variable, so it is not sort-specific and is not excluded). This is a
    decision, not an accident: ↓ under a many-sorted individual domain or
    inside a third-order formula is still ordinary state-variable binding
    (only the bound name's NAMESPACE — hybrid nominals — is unsorted/
    order-0), so inheriting it is the right default, the same one ``@``/bare
    nominals already established."""
    from unicode_fol_kit.fol._fol_nodes import parser_ops_for_mode
    for mode in ("third_order_modal", "modal_sorted"):
        aliases = {op.rule_alias for op in parser_ops_for_mode(mode)}
        assert "down_" in aliases, (mode, sorted(aliases))
        assert "nominal_" in aliases and "at_" in aliases, "sanity: hybrid ops present"


def test_new_operator_self_registers_without_touching_parser():
    """A brand-new operator joins the grammar+transformer via register_parser_op
    alone — no edit to msflparser.py or any grammar file. Restores registry state."""
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
