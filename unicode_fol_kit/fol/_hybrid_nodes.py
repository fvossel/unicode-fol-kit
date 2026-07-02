"""Hybrid-logic node classes: nominals and the satisfaction operator @.

Hybrid logic H(@) extends modal logic with NOMINALS — atomic formulas i, j, …
that are true at EXACTLY ONE world, naming it — and the satisfaction operator
``@i φ`` (*at the world named i, φ holds*). Both parse in the modal mode
(``MSFLParser(modal=True)``): a bare lowercase name in formula position is a
nominal, and ``@i φ`` applies the satisfaction operator. H(@) over K stays
decidable; the ↓ binder (which would make validity undecidable) is deliberately
out of scope.

Reasoning routes: the Kripke evaluator (``KripkeModel(nominals={...})`` +
``satisfies_modal``) evaluates hybrid formulas directly, and the standard
translation maps them to classical FOL (a nominal becomes a world-equality with
a fresh world constant), so ``hybrid_is_valid`` decides validity with Z3 per
frame. The direct classical exporters reject (a nominal is world-relative).
"""

from dataclasses import dataclass

from ._fol_nodes import (
    Node, Z3Env,
    NODE_CLASSES, register_operator, register_parser_op,
)

# Shared rejection message: hybrid constructs are world-relative, so they have no
# direct classical export; the standard translation is the sanctioned route.
_NO_HYBRID_EXPORT = (
    "Hybrid-logic constructs (nominals / the satisfaction operator @) are "
    "world-relative and have no direct first-order export. Use the standard "
    "translation (unicode_fol_kit.standard_translation) or hybrid_is_valid, or "
    "evaluate in a KripkeModel with a nominal assignment."
)


@dataclass(frozen=True)
class Nominal(Node):
    """A nominal ``i`` — an atomic formula true at exactly one world (naming it).

    ``name`` is a lowercase identifier (a legal NAME token, so it round-trips).
    In a :class:`~unicode_fol_kit.semantics.kripke.KripkeModel` the assignment
    ``nominals={"i": world}`` fixes which world each nominal names; the nominal
    is then true at that world and false everywhere else.
    """

    name: str

    def _tree_parts(self):
        """Return the nominal's name as an atomic tree label."""
        return self.name, []

    def to_dict(self):
        """Serialise to dict with the type tag and the nominal's name."""
        return {"_type": "Nominal", "name": self.name}

    @staticmethod
    def from_dict(d):
        """Deserialise a Nominal from a dict produced by to_dict."""
        return Nominal(d["name"])

    def to_z3(self, env: Z3Env = None):
        """Reject direct Z3 export: nominals are world-relative."""
        raise NotImplementedError(_NO_HYBRID_EXPORT)

    def to_prover9(self) -> str:
        """Reject direct Prover9 export: nominals are world-relative."""
        raise NotImplementedError(_NO_HYBRID_EXPORT)

    def to_tptp(self) -> str:
        """Reject direct TPTP export: nominals are world-relative."""
        raise NotImplementedError(_NO_HYBRID_EXPORT)


@dataclass(frozen=True)
class At(Node):
    """The satisfaction operator ``@i φ`` — at the world named ``i``, ``φ`` holds.

    ``nominal`` is the :class:`Nominal` naming the evaluation world (a bare
    string is coerced); ``formula`` is evaluated THERE, regardless of the
    current world. ``@`` is self-dual (``@i φ ↔ ¬@i ¬φ``) and a normal
    modality.
    """

    nominal: Nominal
    formula: Node

    def __post_init__(self):
        """Coerce a bare string to a Nominal and validate the field types."""
        if isinstance(self.nominal, str):
            object.__setattr__(self, "nominal", Nominal(self.nominal))
        if not isinstance(self.nominal, Nominal):
            raise ValueError("At: nominal must be a Nominal (or a bare string).")

    @property
    def agent(self):
        """The nominal, exposed under the generic agent-prefix renderer contract.

        The Unicode/LaTeX renderers drive every ``agent_prefix`` operator
        generically via ``node.agent`` (as for ``K_a`` / ``B_a``); exposing the
        nominal here lets ``@i φ`` render with zero renderer special-casing.
        """
        return self.nominal

    def _tree_parts(self):
        """Return the @-label (with the nominal) and the formula child."""
        return f"@{self.nominal.name}", [self.formula]

    def to_dict(self):
        """Serialise to dict with the nominal and the serialised formula."""
        return {"_type": "At", "nominal": self.nominal.to_dict(),
                "formula": self.formula.to_dict()}

    @staticmethod
    def from_dict(d):
        """Deserialise an At from a dict produced by to_dict."""
        return At(Node.from_dict(d["nominal"]), Node.from_dict(d["formula"]))

    def to_z3(self, env: Z3Env = None):
        """Reject direct Z3 export: @ is world-relative."""
        raise NotImplementedError(_NO_HYBRID_EXPORT)

    def to_prover9(self) -> str:
        """Reject direct Prover9 export: @ is world-relative."""
        raise NotImplementedError(_NO_HYBRID_EXPORT)

    def to_tptp(self) -> str:
        """Reject direct TPTP export: @ is world-relative."""
        raise NotImplementedError(_NO_HYBRID_EXPORT)


NODE_CLASSES.update({"Nominal": Nominal, "At": At})


# =========================
# Renderer + parser registration (modal mode)
# =========================
#
# @ registers as a regular agent_prefix operator (the nominal doubles as the
# "agent", see At.agent), so the Unicode/LaTeX renderers need no new branch.
# Nominal is atomic and rendered by an explicit branch in _msfl_nodes (bare name).

register_operator(At, "agent_prefix", "@", "@", 4)


def _nominal_transform(items):
    """Build a Nominal from a NAME token (or the Constant the base pass made of it)."""
    first = items[0]
    name = getattr(first, "name", None) or str(first)
    return Nominal(name)


def _at_transform(items):
    """Build an At from [ATNOM token '@i', body] (strip the leading '@')."""
    return At(Nominal(str(items[0])[1:]), items[1])


# A bare lowercase name in formula position is a nominal; @i binds like ¬ / K_a.
# Both token classes are accepted because the lexer splits lowercase identifiers
# by shape: single letters (+digits) are VARIABLE, multi-letter names are NAME —
# and the standard hybrid nominals i, j, k fall in the VARIABLE class. ATNOM has
# lexer priority 5 so '@i' lexes as one token.
#
# The bare-name form is emitted as a SEPARATE rule at grammar priority -1 (injected
# via the terminal-defs hook) rather than an inline prefix alternative. A lambda
# application argument (``?app_arg: formula | atom_term``) is also a bare name, so
# without the lowered priority Earley would resolve ``(λx. P(x))(y)`` to the nominal
# reading and silently turn the term argument into Nominal('y'); the -1 priority
# makes the term (atom_term) reading win wherever the two overlap, while a nominal
# still parses everywhere a formula is actually required (``i``, ``P ∧ i``, ``@i j``).
register_parser_op(Nominal, "modal", "prefix", "nominal_", "nominal",
                   _nominal_transform,
                   terminal_name="_nominal_rule",
                   terminal_def="?nominal.-1: (NAME | VARIABLE)")
register_parser_op(At, "modal", "prefix", "at_", "ATNOM prefix",
                   _at_transform,
                   terminal_name="ATNOM", terminal_def="ATNOM.5: /@[a-z][a-zA-Z0-9]*/")
