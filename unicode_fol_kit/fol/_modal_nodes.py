"""Modal AST node classes: alethic, epistemic, doxastic, temporal, and deontic operators.

These nodes extend the classical FOL AST with modal/temporal operators. They are
purely syntactic in this phase: there is no Kripke semantics yet, and they reject
the classical export back-ends (to_z3/to_prover9/to_tptp) — a modal formula must
first be evaluated by the Kripke evaluator or translated to plain FOL via a
standard-translation (``modal_to_fol``) before any first-order export.

Every node is a frozen dataclass (hashable) subclassing Node. Structural methods
(free_variables, traversal, to_msfol, _relativize) are inherited unchanged: they
go through Node.map_children / Node._child_nodes, which already treat the formula
fields here as structural children, so recursion works automatically. The string
``agent`` field of Knows/Believes is a plain scalar and is copied verbatim by
map_children. The Unicode and LaTeX renderers live in _msfl_nodes.py and dispatch
by class name; serialisation, tree labels, and export-rejection live here.
"""

from dataclasses import dataclass

from ._fol_nodes import Node, Z3Env, NODE_CLASSES, register_operator, register_parser_op


# Shared message for the export back-ends: modal nodes cannot be lowered to a
# first-order back-end directly.
_NO_EXPORT = (
    "Modal operators have no direct first-order export; evaluate the formula with "
    "the Kripke evaluator or translate it to plain FOL (modal_to_fol) before "
    "calling to_z3/to_prover9/to_tptp."
)


@dataclass(frozen=True)
class Box(Node):
    """Alethic necessity □φ: φ holds in every accessible world."""

    formula: Node

    def _tree_parts(self):
        """Return the □ label and the single subformula child."""
        return "□", [self.formula]

    def to_dict(self):
        """Serialise to dict with type tag and recursively serialised subformula."""
        return {"_type": "Box", "formula": self.formula.to_dict()}

    @staticmethod
    def from_dict(d):
        """Deserialise a Box from a dict produced by to_dict."""
        return Box(Node.from_dict(d["formula"]))

    def to_z3(self, env: Z3Env = None):
        """Reject Z3 export: modal operators have no direct first-order encoding."""
        raise NotImplementedError(_NO_EXPORT)

    def to_prover9(self) -> str:
        """Reject Prover9 export: modal operators have no direct first-order encoding."""
        raise NotImplementedError(_NO_EXPORT)

    def to_tptp(self) -> str:
        """Reject TPTP export: modal operators have no direct first-order encoding."""
        raise NotImplementedError(_NO_EXPORT)


@dataclass(frozen=True)
class Diamond(Node):
    """Alethic possibility ◇φ: φ holds in some accessible world."""

    formula: Node

    def _tree_parts(self):
        """Return the ◇ label and the single subformula child."""
        return "◇", [self.formula]

    def to_dict(self):
        """Serialise to dict with type tag and recursively serialised subformula."""
        return {"_type": "Diamond", "formula": self.formula.to_dict()}

    @staticmethod
    def from_dict(d):
        """Deserialise a Diamond from a dict produced by to_dict."""
        return Diamond(Node.from_dict(d["formula"]))

    def to_z3(self, env: Z3Env = None):
        """Reject Z3 export: modal operators have no direct first-order encoding."""
        raise NotImplementedError(_NO_EXPORT)

    def to_prover9(self) -> str:
        """Reject Prover9 export: modal operators have no direct first-order encoding."""
        raise NotImplementedError(_NO_EXPORT)

    def to_tptp(self) -> str:
        """Reject TPTP export: modal operators have no direct first-order encoding."""
        raise NotImplementedError(_NO_EXPORT)


@dataclass(frozen=True)
class Knows(Node):
    """Epistemic K_a φ: agent ``agent`` knows φ.

    ``agent`` is a plain string (the agent name, without the ``K_`` prefix).
    """

    agent: str
    formula: Node

    def _tree_parts(self):
        """Return the K_<agent> label and the single subformula child."""
        return f"K_{self.agent}", [self.formula]

    def to_dict(self):
        """Serialise to dict with type tag, agent name, and serialised subformula."""
        return {"_type": "Knows", "agent": self.agent, "formula": self.formula.to_dict()}

    @staticmethod
    def from_dict(d):
        """Deserialise a Knows from a dict produced by to_dict."""
        return Knows(d["agent"], Node.from_dict(d["formula"]))

    def to_z3(self, env: Z3Env = None):
        """Reject Z3 export: modal operators have no direct first-order encoding."""
        raise NotImplementedError(_NO_EXPORT)

    def to_prover9(self) -> str:
        """Reject Prover9 export: modal operators have no direct first-order encoding."""
        raise NotImplementedError(_NO_EXPORT)

    def to_tptp(self) -> str:
        """Reject TPTP export: modal operators have no direct first-order encoding."""
        raise NotImplementedError(_NO_EXPORT)


@dataclass(frozen=True)
class Believes(Node):
    """Doxastic B_a φ: agent ``agent`` believes φ.

    ``agent`` is a plain string (the agent name, without the ``B_`` prefix).
    """

    agent: str
    formula: Node

    def _tree_parts(self):
        """Return the B_<agent> label and the single subformula child."""
        return f"B_{self.agent}", [self.formula]

    def to_dict(self):
        """Serialise to dict with type tag, agent name, and serialised subformula."""
        return {"_type": "Believes", "agent": self.agent, "formula": self.formula.to_dict()}

    @staticmethod
    def from_dict(d):
        """Deserialise a Believes from a dict produced by to_dict."""
        return Believes(d["agent"], Node.from_dict(d["formula"]))

    def to_z3(self, env: Z3Env = None):
        """Reject Z3 export: modal operators have no direct first-order encoding."""
        raise NotImplementedError(_NO_EXPORT)

    def to_prover9(self) -> str:
        """Reject Prover9 export: modal operators have no direct first-order encoding."""
        raise NotImplementedError(_NO_EXPORT)

    def to_tptp(self) -> str:
        """Reject TPTP export: modal operators have no direct first-order encoding."""
        raise NotImplementedError(_NO_EXPORT)


@dataclass(frozen=True)
class Always(Node):
    """Temporal "globally/henceforth" Gφ: φ holds now and at every future point."""

    formula: Node

    def _tree_parts(self):
        """Return the Ⓖ label and the single subformula child."""
        return "Ⓖ", [self.formula]

    def to_dict(self):
        """Serialise to dict with type tag and recursively serialised subformula."""
        return {"_type": "Always", "formula": self.formula.to_dict()}

    @staticmethod
    def from_dict(d):
        """Deserialise an Always from a dict produced by to_dict."""
        return Always(Node.from_dict(d["formula"]))

    def to_z3(self, env: Z3Env = None):
        """Reject Z3 export: modal operators have no direct first-order encoding."""
        raise NotImplementedError(_NO_EXPORT)

    def to_prover9(self) -> str:
        """Reject Prover9 export: modal operators have no direct first-order encoding."""
        raise NotImplementedError(_NO_EXPORT)

    def to_tptp(self) -> str:
        """Reject TPTP export: modal operators have no direct first-order encoding."""
        raise NotImplementedError(_NO_EXPORT)


@dataclass(frozen=True)
class Eventually(Node):
    """Temporal "finally" Fφ: φ holds now or at some future point."""

    formula: Node

    def _tree_parts(self):
        """Return the Ⓕ label and the single subformula child."""
        return "Ⓕ", [self.formula]

    def to_dict(self):
        """Serialise to dict with type tag and recursively serialised subformula."""
        return {"_type": "Eventually", "formula": self.formula.to_dict()}

    @staticmethod
    def from_dict(d):
        """Deserialise an Eventually from a dict produced by to_dict."""
        return Eventually(Node.from_dict(d["formula"]))

    def to_z3(self, env: Z3Env = None):
        """Reject Z3 export: modal operators have no direct first-order encoding."""
        raise NotImplementedError(_NO_EXPORT)

    def to_prover9(self) -> str:
        """Reject Prover9 export: modal operators have no direct first-order encoding."""
        raise NotImplementedError(_NO_EXPORT)

    def to_tptp(self) -> str:
        """Reject TPTP export: modal operators have no direct first-order encoding."""
        raise NotImplementedError(_NO_EXPORT)


@dataclass(frozen=True)
class Next(Node):
    """Temporal "next" Xφ: φ holds at the immediately following point."""

    formula: Node

    def _tree_parts(self):
        """Return the Ⓝ label and the single subformula child."""
        return "Ⓝ", [self.formula]

    def to_dict(self):
        """Serialise to dict with type tag and recursively serialised subformula."""
        return {"_type": "Next", "formula": self.formula.to_dict()}

    @staticmethod
    def from_dict(d):
        """Deserialise a Next from a dict produced by to_dict."""
        return Next(Node.from_dict(d["formula"]))

    def to_z3(self, env: Z3Env = None):
        """Reject Z3 export: modal operators have no direct first-order encoding."""
        raise NotImplementedError(_NO_EXPORT)

    def to_prover9(self) -> str:
        """Reject Prover9 export: modal operators have no direct first-order encoding."""
        raise NotImplementedError(_NO_EXPORT)

    def to_tptp(self) -> str:
        """Reject TPTP export: modal operators have no direct first-order encoding."""
        raise NotImplementedError(_NO_EXPORT)


@dataclass(frozen=True)
class Until(Node):
    """Temporal "left until right" (left U right): left holds until right does.

    ``right`` must eventually hold; ``left`` holds at every point until then.
    """

    left: Node
    right: Node

    def _tree_parts(self):
        """Return the Ⓤ label and the two subformula children."""
        return "Ⓤ", [self.left, self.right]

    def to_dict(self):
        """Serialise to dict with type tag and recursively serialised operands."""
        return {"_type": "Until", "left": self.left.to_dict(), "right": self.right.to_dict()}

    @staticmethod
    def from_dict(d):
        """Deserialise an Until from a dict produced by to_dict."""
        return Until(Node.from_dict(d["left"]), Node.from_dict(d["right"]))

    def to_z3(self, env: Z3Env = None):
        """Reject Z3 export: modal operators have no direct first-order encoding."""
        raise NotImplementedError(_NO_EXPORT)

    def to_prover9(self) -> str:
        """Reject Prover9 export: modal operators have no direct first-order encoding."""
        raise NotImplementedError(_NO_EXPORT)

    def to_tptp(self) -> str:
        """Reject TPTP export: modal operators have no direct first-order encoding."""
        raise NotImplementedError(_NO_EXPORT)


@dataclass(frozen=True)
class Obligatory(Node):
    """Deontic necessity Oφ: φ holds in every deontically accessible world.

    The obligation operator of Standard Deontic Logic (the modal system KD): a
    □-style box over a SERIAL "deontic" accessibility relation. Seriality gives
    the characteristic D axiom ``Oφ → Pφ`` (whatever is obligatory is permitted).
    """

    formula: Node

    def _tree_parts(self):
        """Return the Ⓞ label and the single subformula child."""
        return "Ⓞ", [self.formula]

    def to_dict(self):
        """Serialise to dict with type tag and recursively serialised subformula."""
        return {"_type": "Obligatory", "formula": self.formula.to_dict()}

    @staticmethod
    def from_dict(d):
        """Deserialise an Obligatory from a dict produced by to_dict."""
        return Obligatory(Node.from_dict(d["formula"]))

    def to_z3(self, env: Z3Env = None):
        """Reject Z3 export: modal operators have no direct first-order encoding."""
        raise NotImplementedError(_NO_EXPORT)

    def to_prover9(self) -> str:
        """Reject Prover9 export: modal operators have no direct first-order encoding."""
        raise NotImplementedError(_NO_EXPORT)

    def to_tptp(self) -> str:
        """Reject TPTP export: modal operators have no direct first-order encoding."""
        raise NotImplementedError(_NO_EXPORT)


@dataclass(frozen=True)
class Permitted(Node):
    """Deontic possibility Pφ: φ holds in some deontically accessible world.

    The permission operator of Standard Deontic Logic (the modal system KD): a
    ◇-style diamond over the SERIAL "deontic" accessibility relation, dual to
    :class:`Obligatory` (``Pφ ≡ ¬O¬φ``). Prohibition ``Fφ ≡ ¬Pφ ≡ O¬φ`` is
    derived and has no dedicated node.
    """

    formula: Node

    def _tree_parts(self):
        """Return the Ⓟ label and the single subformula child."""
        return "Ⓟ", [self.formula]

    def to_dict(self):
        """Serialise to dict with type tag and recursively serialised subformula."""
        return {"_type": "Permitted", "formula": self.formula.to_dict()}

    @staticmethod
    def from_dict(d):
        """Deserialise a Permitted from a dict produced by to_dict."""
        return Permitted(Node.from_dict(d["formula"]))

    def to_z3(self, env: Z3Env = None):
        """Reject Z3 export: modal operators have no direct first-order encoding."""
        raise NotImplementedError(_NO_EXPORT)

    def to_prover9(self) -> str:
        """Reject Prover9 export: modal operators have no direct first-order encoding."""
        raise NotImplementedError(_NO_EXPORT)

    def to_tptp(self) -> str:
        """Reject TPTP export: modal operators have no direct first-order encoding."""
        raise NotImplementedError(_NO_EXPORT)


# =========================
# Operator registration
# =========================
#
# Self-register the modal/epistemic/doxastic/temporal/deontic operators with the
# central renderers. The prefix ops bind as tightly as ¬ (precedence 4); the
# latex markup carries the exact trailing space the renderer emits. Knows/Believes
# are agent_prefix (K_<agent> / K_{<agent>}); Until is the binary temporal
# operator at precedence 2.5. register_operator also adds each class to
# NODE_CLASSES, so no separate NODE_CLASSES.update is needed.

register_operator(Box, "prefix", "□", "\\Box ", 4)
register_operator(Diamond, "prefix", "◇", "\\Diamond ", 4)
register_operator(Always, "prefix", "Ⓖ", "\\mathsf{G} ", 4)
register_operator(Eventually, "prefix", "Ⓕ", "\\mathsf{F} ", 4)
register_operator(Next, "prefix", "Ⓝ", "\\mathsf{X} ", 4)
register_operator(Obligatory, "prefix", "Ⓞ", "\\mathsf{O} ", 4)
register_operator(Permitted, "prefix", "Ⓟ", "\\mathsf{P} ", 4)
register_operator(Knows, "agent_prefix", "K_", "K", 4)
register_operator(Believes, "agent_prefix", "B_", "B", 4)
register_operator(Until, "binary_until", "Ⓤ", "\\mathbin{\\mathsf{U}}", 2.5)


# =========================
# Parser registration (modal mode)
# =========================
#
# Self-register the modal/epistemic/doxastic/temporal/deontic operators with the
# PARSER registry so MSFLParser assembles the modal grammar + transformer from the
# registry alone (no hand-written ModalTransformer, no modal.lark). Each binding
# mirrors the legacy modal.lark rule and ModalTransformer handler EXACTLY so the
# assembled parser produces byte-identical ASTs:
#
#   * The prefix operators (□ ◇ Ⓖ Ⓕ Ⓝ K_a B_a Ⓞ Ⓟ) sit at the ¬ (prefix) level —
#     ``OP prefix -> alias`` — binding as tightly as negation. The classical ¬
#     (not_) is registered for "modal" in _fol_nodes.py; these add to it.
#   * Until (Ⓤ) is the binary right-assoc level between the same_level group and →;
#     registering ANY "until"-level op makes build_grammar route the → level's
#     left operand through the until rule (impl_body = "until"), reproducing
#     modal.lark's ``?implication: until`` layering. Its grammar field is the bare
#     TUNTIL terminal; build_grammar wraps it as ``same_level_ops TUNTIL until``.
#   * Knows/Believes carry their agent in the matched token (e.g. "K_alice"); the
#     transform strips the two-character "K_"/"B_" prefix, exactly as the legacy
#     knows_/believes_ handlers did.
#
# Named terminals (with their lexer priorities) are declared via terminal_def so
# the generated grammar lexes K_a / B_a as KNOWS/BELIEVES (priority 5) ahead of
# PREDICATE, matching terminals/modal.lark.

# --- prefix modal/temporal/deontic operators (¬-level) ---
register_parser_op(Box, "modal", "prefix", "box_", "BOX prefix",
                   lambda items: Box(items[1]),
                   terminal_name="BOX", terminal_def='BOX: "□"')
register_parser_op(Diamond, "modal", "prefix", "diamond_", "DIAMOND prefix",
                   lambda items: Diamond(items[1]),
                   terminal_name="DIAMOND", terminal_def='DIAMOND: "◇"')
register_parser_op(Always, "modal", "prefix", "always_", "TALWAYS prefix",
                   lambda items: Always(items[1]),
                   terminal_name="TALWAYS", terminal_def='TALWAYS: "Ⓖ"')
register_parser_op(Eventually, "modal", "prefix", "eventually_", "TEVENTUALLY prefix",
                   lambda items: Eventually(items[1]),
                   terminal_name="TEVENTUALLY", terminal_def='TEVENTUALLY: "Ⓕ"')
register_parser_op(Next, "modal", "prefix", "next_", "TNEXT prefix",
                   lambda items: Next(items[1]),
                   terminal_name="TNEXT", terminal_def='TNEXT: "Ⓝ"')
register_parser_op(Knows, "modal", "prefix", "knows_", "KNOWS prefix",
                   lambda items: Knows(str(items[0])[2:], items[1]),
                   terminal_name="KNOWS", terminal_def='KNOWS.5: /K_[a-z][a-zA-Z0-9]*/')
register_parser_op(Believes, "modal", "prefix", "believes_", "BELIEVES prefix",
                   lambda items: Believes(str(items[0])[2:], items[1]),
                   terminal_name="BELIEVES", terminal_def='BELIEVES.5: /B_[a-z][a-zA-Z0-9]*/')
register_parser_op(Obligatory, "modal", "prefix", "obligatory_", "OBLIG prefix",
                   lambda items: Obligatory(items[1]),
                   terminal_name="OBLIG", terminal_def='OBLIG: "Ⓞ"')
register_parser_op(Permitted, "modal", "prefix", "permitted_", "PERMIT prefix",
                   lambda items: Permitted(items[1]),
                   terminal_name="PERMIT", terminal_def='PERMIT: "Ⓟ"')

# --- binary temporal Until (Ⓤ): same_level_ops TUNTIL until -> until_ ---
# items = [left, TUNTIL token, right]; the token is the named terminal (kept in
# the item list), so the right operand is items[2], exactly as ModalTransformer.
register_parser_op(Until, "modal", "until", "until_", "TUNTIL",
                   lambda items: Until(items[0], items[2]),
                   terminal_name="TUNTIL", terminal_def='TUNTIL: "Ⓤ"')
