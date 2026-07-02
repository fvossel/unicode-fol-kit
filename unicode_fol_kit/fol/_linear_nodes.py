"""Intuitionistic linear logic (ILL) node classes and the ``linear`` parser mode.

Linear logic (Girard 1987) is the substructural logic in which formulas are
RESOURCES: the structural rules of weakening and contraction are dropped, so a
hypothesis is used exactly once unless explicitly banked under ``!``. The
``linear`` mode (``MSFLParser(linear=True)``) covers propositional
intuitionistic linear logic:

- ``⊗``  multiplicative conjunction (*tensor*: both resources, side by side),
- ``⊸``  linear implication (*lollipop*: consume the antecedent, produce the
  consequent),
- ``&``  additive conjunction (*with*: a choice offered — either can be taken,
  not both),
- ``⊕``  additive disjunction (one of the two, the provider chooses),
- ``!``  the exponential (*of course*: an unlimited, reusable supply),
- ``𝟙``  the multiplicative unit (the empty resource).

``⊗`` / ``&`` / ``⊕`` sit in the no-mixing same-level group (parenthesise mixed
chains); ``⊸`` is right-associative; ``!`` binds like ¬. The glyph ``⊕`` is the
classical Xor / fuzzy strong disjunction in OTHER modes — per-mode glyph reuse
is the established pattern here. Provability lives in
``unicode_fol_kit.atp.linear`` (a cut-free backward-search prover, complete and
terminating for the !-free fragment); there is no classical export — the
classical collapse (⊗,& → ∧; ⊕ → ∨; ⊸ → →; drop !) would erase exactly the
resource distinctions the logic is about, so ``to_z3`` / ``to_prover9`` /
``to_tptp`` reject.
"""

from dataclasses import dataclass

from ._fol_nodes import (
    Node, Z3Env,
    NODE_CLASSES, register_operator, register_parser_op, _fold_binary,
)

# Shared rejection message: the classical collapse is deliberately not provided.
_NO_LINEAR_EXPORT = (
    "Linear-logic formulas have no classical first-order export: collapsing "
    "⊗/& to ∧, ⊕ to ∨, ⊸ to →, and dropping ! erases the resource distinctions "
    "the logic exists to draw. Use the sequent prover "
    "(unicode_fol_kit.ill_prove / ill_derivable) instead."
)


def _linear_binary(name, doc):
    """Build a frozen binary linear-logic node class with the shared boilerplate."""

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
            """Reject Z3 export: linear connectives have no classical collapse here."""
            raise NotImplementedError(_NO_LINEAR_EXPORT)

        def to_prover9(self) -> str:
            """Reject Prover9 export: linear connectives have no classical collapse here."""
            raise NotImplementedError(_NO_LINEAR_EXPORT)

        def to_tptp(self) -> str:
            """Reject TPTP export: linear connectives have no classical collapse here."""
            raise NotImplementedError(_NO_LINEAR_EXPORT)

    _Binary.__name__ = _Binary.__qualname__ = name
    _Binary.__doc__ = doc
    return _Binary


Tensor = _linear_binary(
    "Tensor",
    "Multiplicative conjunction ``A ⊗ B``: both resources, available side by side.")
With = _linear_binary(
    "With",
    "Additive conjunction ``A & B``: an offered choice — either can be taken, "
    "but only one.")
OPlus = _linear_binary(
    "OPlus",
    "Additive disjunction ``A ⊕ B``: one of the two holds, the provider chooses.")
LinearImplies = _linear_binary(
    "LinearImplies",
    "Linear implication ``A ⊸ B``: consuming one ``A`` produces one ``B``.")


@dataclass(frozen=True)
class OfCourse(Node):
    """The exponential ``!A``: an unlimited, reusable supply of the resource A.

    ``!`` reintroduces weakening and contraction for the banked formula — the
    only gateway back to classical-style reuse.
    """

    formula: Node

    def to_dict(self):
        """Serialise to dict with the recursively serialised operand."""
        return {"_type": "OfCourse", "formula": self.formula.to_dict()}

    @staticmethod
    def from_dict(d):
        """Deserialise an OfCourse from a dict produced by to_dict."""
        return OfCourse(Node.from_dict(d["formula"]))

    def to_z3(self, env: Z3Env = None):
        """Reject Z3 export: the exponential has no classical collapse here."""
        raise NotImplementedError(_NO_LINEAR_EXPORT)

    def to_prover9(self) -> str:
        """Reject Prover9 export: the exponential has no classical collapse here."""
        raise NotImplementedError(_NO_LINEAR_EXPORT)

    def to_tptp(self) -> str:
        """Reject TPTP export: the exponential has no classical collapse here."""
        raise NotImplementedError(_NO_LINEAR_EXPORT)


@dataclass(frozen=True)
class One(Node):
    """The multiplicative unit ``𝟙``: the empty resource (⊗'s neutral element)."""

    def _tree_parts(self):
        """Return the unit glyph as an atomic tree label."""
        return "𝟙", []

    def to_dict(self):
        """Serialise to dict with the type tag only (the unit has no children)."""
        return {"_type": "One"}

    @staticmethod
    def from_dict(d):
        """Deserialise a One from a dict produced by to_dict."""
        return One()

    def to_z3(self, env: Z3Env = None):
        """Reject Z3 export: the unit has no classical collapse here."""
        raise NotImplementedError(_NO_LINEAR_EXPORT)

    def to_prover9(self) -> str:
        """Reject Prover9 export: the unit has no classical collapse here."""
        raise NotImplementedError(_NO_LINEAR_EXPORT)

    def to_tptp(self) -> str:
        """Reject TPTP export: the unit has no classical collapse here."""
        raise NotImplementedError(_NO_LINEAR_EXPORT)


NODE_CLASSES.update({
    "Tensor": Tensor, "With": With, "OPlus": OPlus,
    "LinearImplies": LinearImplies, "OfCourse": OfCourse, "One": One,
})


# =========================
# Renderer + parser registration — the "linear" mode
# =========================
#
# Every connective is a regular registry operator, so the Unicode/LaTeX
# renderers need no new branch; only the nullary 𝟙 has an explicit renderer
# branch in _msfl_nodes.

register_operator(Tensor, "level2", "⊗", "\\otimes", 3)
register_operator(With, "level2", "&", "\\mathbin{\\&}", 3)
register_operator(OPlus, "level2", "⊕", "\\oplus", 3)
register_operator(LinearImplies, "binary_implies", "⊸", "\\multimap", 2)
register_operator(OfCourse, "prefix", "!", "\\mathord{!}", 4)

register_parser_op(Tensor, "linear", "level2", "tensor_", '"⊗"',
                   lambda items: _fold_binary(items, Tensor),
                   only_name="only_tensor")
register_parser_op(With, "linear", "level2", "with_", '"&"',
                   lambda items: _fold_binary(items, With),
                   only_name="only_with")
register_parser_op(OPlus, "linear", "level2", "oplus_", '"⊕"',
                   lambda items: _fold_binary(items, OPlus),
                   only_name="only_oplus")
register_parser_op(LinearImplies, "linear", "implication", "limp_", '"⊸"',
                   lambda items: LinearImplies(items[0], items[1]))
register_parser_op(OfCourse, "linear", "prefix", "ofcourse_", '"!" prefix',
                   lambda items: OfCourse(items[0]))
register_parser_op(One, "linear", "prefix", "one_", '"𝟙"',
                   lambda items: One())
