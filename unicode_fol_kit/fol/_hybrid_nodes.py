"""Hybrid-logic node classes: nominals, the satisfaction operator @, and ↓.

Hybrid logic H(@) extends modal logic with NOMINALS — atomic formulas i, j, …
that are true at EXACTLY ONE world, naming it — and the satisfaction operator
``@i φ`` (*at the world named i, φ holds*). Both parse in the modal mode
(``MSFLParser(modal=True)``): a bare lowercase name in formula position is a
nominal, and ``@i φ`` applies the satisfaction operator. H(@) over K stays
DECIDABLE.

Adding the ``↓`` binder gives the full hybrid language H(@,↓): ``↓x.φ`` binds
the state variable ``x`` to the CURRENT world, then evaluates ``φ`` (which may
refer back to ``x`` as an ordinary nominal or via ``@x``). H(@,↓) validity is
UNDECIDABLE (Areces, Blackburn & Marx 1999) — but the standard translation
into classical FOL stays MEANING-PRESERVING for it (that correspondence is
exactly what defines the "bounded fragment"), so validity is co-r.e.: a Z3
route can still PROVE it (never REFUTE it presentably — see
``fol.modal_translation.down_is_valid``), and the Kripke evaluator
(``satisfies_modal``) still evaluates ``↓`` on any finite model, including
inside a bounded finite-model search that REFUTES it
(``atp.kripke_enum.KripkeEnumBackend``). No route here DECIDES full H(@,↓);
a route that stays sound only by staying bounded to a fragment it can fully
search (the labelled modal tableau, the QML embedding, the HOL shallow
embeddings) refuses a ``↓``-containing formula BY NAME instead of silently
mis-scoping.

Reasoning routes: the Kripke evaluator (``KripkeModel(nominals={...})`` +
``satisfies_modal``) evaluates hybrid formulas directly (route A, always
terminating), and the standard translation maps them to classical FOL (a
nominal becomes a world-equality with a fresh world constant; ``↓x`` becomes a
local rebinding of ``x`` to the current-world term, with NO fresh quantifier),
so ``hybrid_is_valid`` (H(@) only) / ``down_is_valid`` (H(@,↓), PROVED-only) /
``KripkeEnumBackend`` (bounded search, REFUTED-only) decide validity with Z3 /
finite enumeration per frame (route B). The direct classical exporters reject
(a nominal — and ``↓`` doubly so — is world-relative).
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

# Rejection message for Down specifically: same world-relativity as Nominal/At,
# PLUS H(@,↓) validity is undecidable, so the sanctioned routes are narrower
# than hybrid_is_valid's (which itself refuses ↓ — see modal_translation.py).
_NO_DOWN_EXPORT = (
    "The ↓ binder is world-relative (like every hybrid-logic construct) and "
    "H(@,↓) validity is undecidable, so it has no direct first-order export "
    "and no bare-bool validity check. Use "
    "unicode_fol_kit.fol.modal_translation.down_is_valid (Z3, PROVED-only) or "
    "unicode_fol_kit.atp.kripke_enum.KripkeEnumBackend (bounded search, "
    "REFUTED-only) for validity, or evaluate directly in a KripkeModel with "
    "unicode_fol_kit.semantics.kripke.satisfies_modal."
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


@dataclass(frozen=True)
class Down(Node):
    """The ↓ binder ``↓x.φ`` — binds the state variable ``x`` to the CURRENT
    world, then evaluates ``φ``, in which ``x`` may occur as an ordinary
    :class:`Nominal` or via :class:`At`. Nesting ``↓`` under a modality lets a
    formula "look back" at a world named earlier — e.g. ``↓x.□¬x``
    (irreflexivity: no successor of the current world IS the current world)
    or ``↓x.◇x`` (reflexivity) — expressive power plain H(@) does not have
    (a nominal only ever names a world FIXED IN ADVANCE by the model, never
    "whichever world evaluation happens to be at").

    ``variable`` is a :class:`Nominal` naming the bound state variable — this
    reuses the Nominal shape rather than adding a new leaf kind, since ↓
    binds exactly the same kind of name (a lowercase, NAME-legal identifier)
    that a plain nominal already is; a bare string is coerced, matching
    :class:`At`'s own convention. ``formula`` is the scope.

    Binding is by NAME, not by a separate de Bruijn/alpha-renaming layer
    (unlike :class:`~unicode_fol_kit.fol._fol_nodes.Quantifier`'s object
    variable): an occurrence of ``Nominal(x)`` or ``At(Nominal(x), …)``
    anywhere in ``formula`` NOT itself inside a nested ``Down(Nominal(x), …)``
    refers to THIS binder — a nested ``↓x`` of the same name shadows it
    exactly the way a nested ``∀x`` would shadow an outer one, so
    ``↓x.↓x.φ`` makes the outer binding entirely inert. This is deliberately
    NOT wired into the generic ``_subst`` / capture-avoiding ``replace`` /
    alpha-renaming machinery those FOL binders use (``fol/_msfl_nodes.py``):
    a nominal is never a first-order term, so no first-order substitution
    ever needs to reach inside one, and the two evaluators that DO give ↓ its
    meaning (:func:`~unicode_fol_kit.semantics.kripke.satisfies_modal` and
    :func:`~unicode_fol_kit.fol.modal_translation.standard_translation`) each
    implement this by-name (re)binding directly, as a small environment keyed
    on the name — see their own docstrings.
    """

    variable: Nominal
    formula: Node

    def __post_init__(self):
        """Coerce a bare string to a Nominal and validate the field types."""
        if isinstance(self.variable, str):
            object.__setattr__(self, "variable", Nominal(self.variable))
        if not isinstance(self.variable, Nominal):
            raise ValueError("Down: variable must be a Nominal (or a bare string).")

    def _tree_parts(self):
        """Return the ↓-label (with the bound name) and the formula child."""
        return f"↓{self.variable.name}", [self.formula]

    def to_dict(self):
        """Serialise to dict with the bound variable and the serialised formula."""
        return {"_type": "Down", "variable": self.variable.to_dict(),
                "formula": self.formula.to_dict()}

    @staticmethod
    def from_dict(d):
        """Deserialise a Down from a dict produced by to_dict."""
        return Down(Node.from_dict(d["variable"]), Node.from_dict(d["formula"]))

    def to_z3(self, env: Z3Env = None):
        """Reject direct Z3 export: ↓ is world-relative and undecidable."""
        raise NotImplementedError(_NO_DOWN_EXPORT)

    def to_prover9(self) -> str:
        """Reject direct Prover9 export: ↓ is world-relative and undecidable."""
        raise NotImplementedError(_NO_DOWN_EXPORT)

    def to_tptp(self) -> str:
        """Reject direct TPTP export: ↓ is world-relative and undecidable."""
        raise NotImplementedError(_NO_DOWN_EXPORT)


NODE_CLASSES.update({"Nominal": Nominal, "At": At, "Down": Down})


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


def _down_transform(items):
    """Build a Down from [DOWNARROW token, bound name (Variable/Constant), body]."""
    bound = items[1]
    name = getattr(bound, "name", None) or str(bound)
    return Down(Nominal(name), items[2])


# ↓ binds at the SAME "quantifier" grammar level as ∀/∃/the counting quantifier
# (structurally identical to the already-shipped Count registration: same level,
# same named-terminal-glyph mechanism), so ``↓x.□¬x`` parses with the same tight
# binding a plain quantifier gets, extending as far right as possible through
# ``prefix``. The bound name accepts BOTH lexer classes, ``(NAME | VARIABLE)`` —
# not just VARIABLE — for the same reason the bare-nominal rule above does: a
# hybrid nominal name is legally either a single-letter VARIABLE-class token
# (the standard i, j, k) or a multi-letter NAME-class one, and ↓'s bound name is
# the very same kind of name (it IS a Nominal, see Down's docstring), so
# restricting it to VARIABLE alone would let ``i`` be bound by ↓ but not
# ``world1`` — an arbitrary asymmetry with the unbound nominal syntax. No
# priority annotation is needed here (unlike the bare-nominal rule's -1): DOWNARROW
# is a distinguishing token that starts this alternative, so it cannot share an
# LALR state with the term/atom_term alternatives the bare-nominal rule's
# priority exists to disambiguate (verified empirically in
# tests/test_modal_lalr_fallback.py, which — because "modal" is an LALR-first,
# Earley-fallback mode regardless, see msflparser.py's _HYBRID_MODES — also
# guarantees correctness even if that empirical claim ever stopped holding).
register_parser_op(Down, "modal", "quantifier", "down_",
                   'DOWNARROW (NAME | VARIABLE) "." prefix', _down_transform,
                   terminal_name="DOWNARROW", terminal_def='DOWNARROW: "↓"')
