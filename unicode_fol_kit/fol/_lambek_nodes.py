"""Lambek-calculus node classes and the ``lambek`` parser mode.

The Lambek calculus L (Lambek 1958) is the substructural logic of ORDERED
resources — the type logic of categorial grammar. On top of dropping weakening
and contraction (as linear logic does) it also drops EXCHANGE: the antecedent
of a sequent is a sequence, not a multiset, so ``A, A\\B ⊢ B`` is derivable but
``A\\B, A ⊢ B`` is not. The ``lambek`` mode (``MSFLParser(lambek=True)``)
provides the three connectives over atomic categories (nullary predicates such
as ``NP``, ``S``):

- ``A • B``  the product (A followed by B),
- ``A \\ B``  *under*: combines with an ``A`` on its LEFT to give a ``B``,
- ``B / A``  *over*: combines with an ``A`` on its RIGHT to give a ``B``.

``•`` binds tighter than ``\\`` and ``/`` (the categorial convention); ``\\``
and ``/`` are right-associative in the grammar — parenthesise where the
non-associative reading matters. Derivability lives in
``unicode_fol_kit.atp.lambek`` (a complete, terminating cut-free decision
procedure — L is decidable). There is no classical export: collapsing the
directional implications to ``→`` erases word order, which is the calculus's
entire point, so ``to_z3`` / ``to_prover9`` / ``to_tptp`` reject.
"""

from dataclasses import dataclass

from ._fol_nodes import (
    Node, Z3Env,
    NODE_CLASSES, register_operator, register_parser_op, _fold_binary,
)

# Shared rejection message: the order-forgetting collapse is deliberately absent.
_NO_LAMBEK_EXPORT = (
    "Lambek-calculus types have no classical first-order export: collapsing the "
    "directional implications \\ and / to → forgets word order, which is what "
    "the calculus is about. Use the decision procedure "
    "(unicode_fol_kit.lambek_derivable / lambek_prove) instead."
)


def _lambek_binary(name, doc):
    """Build a frozen binary Lambek node class with the shared boilerplate."""

    @dataclass(frozen=True)
    class _Binary(Node):
        left: Node
        right: Node

        def to_dict(self):
            """Serialise to dict with type tag and recursively serialised operands."""
            return {"_type": name, "left": self.left.to_dict(),
                    "right": self.right.to_dict()}

        @staticmethod
        def from_dict(d):
            """Deserialise from a dict produced by to_dict."""
            return NODE_CLASSES[name](Node.from_dict(d["left"]),
                                      Node.from_dict(d["right"]))

        def to_z3(self, env: Z3Env = None):
            """Reject Z3 export: Lambek types have no order-preserving collapse."""
            raise NotImplementedError(_NO_LAMBEK_EXPORT)

        def to_prover9(self) -> str:
            """Reject Prover9 export: Lambek types have no order-preserving collapse."""
            raise NotImplementedError(_NO_LAMBEK_EXPORT)

        def to_tptp(self) -> str:
            """Reject TPTP export: Lambek types have no order-preserving collapse."""
            raise NotImplementedError(_NO_LAMBEK_EXPORT)

    _Binary.__name__ = _Binary.__qualname__ = name
    _Binary.__doc__ = doc
    return _Binary


Product = _lambek_binary(
    "Product",
    "The Lambek product ``A • B``: an ``A`` immediately followed by a ``B``.")
Under = _lambek_binary(
    "Under",
    "The Lambek *under* type ``A \\\\ B``: combines with an ``A`` on its LEFT "
    "to yield a ``B`` (fields are as written: left=A, right=B).")
Over = _lambek_binary(
    "Over",
    "The Lambek *over* type ``B / A``: combines with an ``A`` on its RIGHT "
    "to yield a ``B`` (fields are as written: left=B, right=A).")


NODE_CLASSES.update({"Product": Product, "Under": Under, "Over": Over})


# =========================
# Renderer + parser registration — the "lambek" mode
# =========================
#
# All three connectives are regular registry operators (no renderer branches).
# '\\' and '/' sit at the implication level (right-assoc; parenthesise for the
# non-associative reading), '•' at the tighter same-level group. The '/' glyph
# is arithmetic division in the TERM layer of other modes; at the formula level
# of the lambek mode it is unambiguous (categories are formulas, not terms).

register_operator(Product, "level2", "•", "\\bullet", 3)
register_operator(Under, "binary_implies", "\\", "\\backslash", 2)
register_operator(Over, "binary_implies", "/", "/", 2)

register_parser_op(Product, "lambek", "level2", "product_", '"•"',
                   lambda items: _fold_binary(items, Product),
                   only_name="only_product")
register_parser_op(Under, "lambek", "implication", "under_", '"\\\\"',
                   lambda items: Under(items[0], items[1]))
register_parser_op(Over, "lambek", "implication", "over_", '"/"',
                   lambda items: Over(items[0], items[1]))
