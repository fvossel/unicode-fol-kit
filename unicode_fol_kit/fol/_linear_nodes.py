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
- ``𝟙``  the multiplicative unit (the empty resource),
- ``⊤``  the additive truth (*top*: always available, no information — the
  additive unit of ``&``; ``⊤R`` holds for ANY context, so ⊤ carries no
  information about what it takes to reach it),
- ``𝟘``  the additive falsity (*zero*: the impossible resource — the additive
  unit of ``⊕``; ``0L`` derives ANY sequent once 𝟘 is in the antecedent, ILL's
  analogue of ex falso).

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


@dataclass(frozen=True)
class Top(Node):
    """The additive truth ``⊤``: always derivable (rule ``⊤R``, no premise, any
    context) — the additive unit of ``&`` (``With``). Carries no information: unlike
    ``𝟙`` (which must be consumed exactly, ``⊗``'s unit), ``⊤`` is reachable from
    ANY antecedent, so e.g. ``⊤ ⊸ A`` is NOT derivable in general (having reached
    ⊤ tells the consumer nothing that would let it produce A)."""

    def _tree_parts(self):
        """Return the top glyph as an atomic tree label."""
        return "⊤", []

    def to_dict(self):
        """Serialise to dict with the type tag only (⊤ has no children)."""
        return {"_type": "Top"}

    @staticmethod
    def from_dict(d):
        """Deserialise a Top from a dict produced by to_dict."""
        return Top()

    def to_z3(self, env: Z3Env = None):
        """Reject Z3 export: ⊤ has no classical collapse here."""
        raise NotImplementedError(_NO_LINEAR_EXPORT)

    def to_prover9(self) -> str:
        """Reject Prover9 export: ⊤ has no classical collapse here."""
        raise NotImplementedError(_NO_LINEAR_EXPORT)

    def to_tptp(self) -> str:
        """Reject TPTP export: ⊤ has no classical collapse here."""
        raise NotImplementedError(_NO_LINEAR_EXPORT)


@dataclass(frozen=True)
class Zero(Node):
    """The additive falsity ``𝟘``: once in the antecedent, ANY sequent is derivable
    (rule ``0L``, no premise) — the additive unit of ``⊕`` (``OPlus``) and ILL's
    analogue of ex falso quodlibet. Dual to ``⊤``: ``⊤`` is always a valid RIGHT
    conclusion, ``𝟘`` is always a usable LEFT hypothesis."""

    def _tree_parts(self):
        """Return the zero glyph as an atomic tree label."""
        return "𝟘", []

    def to_dict(self):
        """Serialise to dict with the type tag only (𝟘 has no children)."""
        return {"_type": "Zero"}

    @staticmethod
    def from_dict(d):
        """Deserialise a Zero from a dict produced by to_dict."""
        return Zero()

    def to_z3(self, env: Z3Env = None):
        """Reject Z3 export: 𝟘 has no classical collapse here."""
        raise NotImplementedError(_NO_LINEAR_EXPORT)

    def to_prover9(self) -> str:
        """Reject Prover9 export: 𝟘 has no classical collapse here."""
        raise NotImplementedError(_NO_LINEAR_EXPORT)

    def to_tptp(self) -> str:
        """Reject TPTP export: 𝟘 has no classical collapse here."""
        raise NotImplementedError(_NO_LINEAR_EXPORT)


NODE_CLASSES.update({
    "Tensor": Tensor, "With": With, "OPlus": OPlus,
    "LinearImplies": LinearImplies, "OfCourse": OfCourse, "One": One,
    "Top": Top, "Zero": Zero,
})


# =========================
# Renderer + parser registration — the "linear" mode
# =========================
#
# Every connective is a regular registry operator, so the Unicode/LaTeX
# renderers need no new branch; only the nullary constants (𝟙, and now ⊤/𝟘)
# need an explicit renderer branch in _msfl_nodes (register_operator has no
# "nullary" fixity — see _fol_nodes._VALID_FIXITIES — because every fixity it
# supports arranges at least one operand). PARSING ⊤/𝟘 needs no such branch
# (register_parser_op below is self-contained), so 'MSFLParser(linear=True)'
# already round-trips them; only Node.to_unicode_str()/to_latex() on a formula
# that CONTAINS ⊤ or 𝟘 need the central _msfl_nodes branch, which is wired in
# centrally alongside every other in-flight change to that shared module (see
# render_ill_formula below for the self-contained substitute this module's own
# callers — atp.linear, hol.isabelle_substructural — use in the meantime).

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
register_parser_op(Top, "linear", "prefix", "top_", '"⊤"',
                   lambda items: Top())
register_parser_op(Zero, "linear", "prefix", "zero_", '"𝟘"',
                   lambda items: Zero())


# ---------------------------------------------------------------------------
# A self-contained Unicode renderer for ILL formulas (workaround).
# ---------------------------------------------------------------------------
#
# Node.to_unicode_str() dispatches through unicode_fol_kit.fol._msfl_nodes,
# whose explicit branch table currently only special-cases One ("𝟙") among the
# nullary linear-mode constants (see the comment above register_operator's
# calls). Until Top/Zero get their own branch there, to_unicode_str() (and
# to_latex()) raise TypeError on any formula containing a Top/Zero node
# ANYWHERE in its tree — including nested, e.g. inside a Tensor — because the
# renderer recurses via its own free functions, not via polymorphic dispatch,
# so overriding to_unicode_str on Top/Zero alone would not be seen by a
# containing Tensor's rendering. render_ill_formula is the drop-in substitute
# every ILL-aware caller in this kit (atp.linear, hol.isabelle_substructural)
# uses instead: it renders exactly like to_unicode_str for every existing
# linear-mode node (Atom included, via to_unicode_str — atoms can never
# contain Top/Zero, only term arguments), and adds the ⊤/𝟘 cases. Every
# subformula is fully parenthesised (always safe: MSFLParser accepts redundant
# parens anywhere), so round-tripping through MSFLParser(linear=True).parse
# reproduces a structurally equal AST even though the text differs from what
# the (eventual) central renderer would print.
def render_ill_formula(f: Node) -> str:
    """Render an ILL (``linear`` mode) formula to Unicode text.

    A safe substitute for ``f.to_unicode_str()`` that also handles ``Top``/
    ``Zero`` (see the module comment above). Always produces text that
    re-parses (via ``MSFLParser(linear=True).parse``) to a structurally equal
    formula; every compound subformula is fully parenthesised.
    """
    if isinstance(f, Top):
        return "⊤"
    if isinstance(f, Zero):
        return "𝟘"
    if isinstance(f, One):
        return "𝟙"
    if isinstance(f, OfCourse):
        return f"!({render_ill_formula(f.formula)})"
    if isinstance(f, Tensor):
        return f"({render_ill_formula(f.left)} ⊗ {render_ill_formula(f.right)})"
    if isinstance(f, With):
        return f"({render_ill_formula(f.left)} & {render_ill_formula(f.right)})"
    if isinstance(f, OPlus):
        return f"({render_ill_formula(f.left)} ⊕ {render_ill_formula(f.right)})"
    if isinstance(f, LinearImplies):
        return f"({render_ill_formula(f.left)} ⊸ {render_ill_formula(f.right)})"
    # Atom (and anything else the linear grammar can produce): to_unicode_str
    # is safe here since an Atom's children are TERMS (Variable/Constant/
    # Number/Function), never Top/Zero.
    return f.to_unicode_str()


def _ill_sort_key(f: Node) -> str:
    """A total-order string key for sorting ILL formulas (multiset bookkeeping
    in atp.linear): ``render_ill_formula`` first (readable, and identical to
    the pre-Top/Zero ordering for any formula without Top/Zero, since it then
    equals ``to_unicode_str()``), then ``repr()`` as a tiebreaker.
    """
    return render_ill_formula(f) + "\x00" + repr(f)
