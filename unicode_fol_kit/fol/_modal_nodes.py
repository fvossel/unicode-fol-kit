"""Modal AST node classes: alethic, epistemic, doxastic, temporal, and deontic operators.

These nodes extend the classical FOL AST with modal/temporal operators. They are
purely syntactic in this phase: there is no Kripke semantics yet, and they reject
the classical export back-ends (to_z3/to_prover9/to_tptp) — a modal formula must
first be evaluated by the Kripke evaluator or translated to plain FOL via a
standard-translation (``modal_to_fol``) before any first-order export.

Every node is a frozen dataclass (hashable) subclassing Node. Structural methods
(free_variables, traversal, to_msfol, _relativize) are inherited unchanged: they
go through Node.map_children / Node._child_nodes, which already treat the formula
fields here as structural children, so recursion works automatically. The
``agent`` field of Knows/Believes is itself a **term** (Variable or Constant), a
structural child — so it is reached by free_variables / substitution / β-reduction
and can be a quantified variable (``∀x (Student(x) → K_x φ)``). The Unicode and
LaTeX renderers live in _msfl_nodes.py and dispatch by class name; serialisation,
tree labels, and export-rejection live here.
"""

from dataclasses import dataclass
from typing import Tuple

from ._fol_nodes import (
    Node, Variable, Constant, Z3Env, NODE_CLASSES,
    register_operator, register_parser_op,
)


def _coerce_agent(agent):
    """Coerce an agent to a term Node: a bare string becomes a Constant (named agent)."""
    return Constant(agent) if isinstance(agent, str) else agent


def _agent_label(agent: Node) -> str:
    """Render an agent term as the short name used in K_<agent> / relation keys."""
    return getattr(agent, "name", None) or agent.to_unicode_str()


def _coerce_agent_group(group) -> Tuple[Node, ...]:
    """Coerce an iterable of agents to a tuple of term Nodes (see :func:`_coerce_agent`)."""
    return tuple(_coerce_agent(a) for a in group)


def _group_label(group: Tuple[Node, ...]) -> str:
    """Render a group of agent terms as the comma-joined list used inside ``{…}``."""
    return ",".join(_agent_label(a) for a in group)


def parse_agent_token(token_text: str, prefix_len: int = 2) -> Node:
    """Turn a 'K_x' / 'B_alice' token into an agent **term**.

    The agent is parsed as a Variable; binding is decided afterwards by the
    :func:`resolve_agent_variables` scope pass (the same architecture as
    :func:`resolve_lambda_scope`): an agent bound by an enclosing object quantifier
    stays a Variable, a free one is demoted to a named Constant. We do not re-decide
    variable-vs-constant by name form here — that would duplicate the lexer's VARIABLE
    convention (a quantifier can only bind a VARIABLE-form name, so a bound agent is
    always such a name anyway).
    """
    return Variable(str(token_text)[prefix_len:])


def resolve_agent_variables(node: Node, bound: frozenset = frozenset()) -> Node:
    """Demote a FREE epistemic/doxastic agent variable to a Constant (a named agent).

    An agent that lexes as a variable (``K_x``) is genuinely a bound variable only when
    an enclosing object quantifier binds its name — ``∀x (Student(x) → K_x φ)`` quantifies
    over agents. A bare ``K_a`` with no binder denotes the specific named agent ``a``, so
    its free agent variable is demoted to ``Constant("a")``. Applied as a parser post-pass.
    """
    from dataclasses import replace
    from .nodes import Quantifier, SortedQuantifier
    if isinstance(node, (Quantifier, SortedQuantifier)):
        inner = bound | {node.variable.name}
        return replace(node, formula=resolve_agent_variables(node.formula, inner))
    if isinstance(node, (Knows, Believes, Says, Wants)):
        agent = node.agent
        if isinstance(agent, Variable) and agent.name not in bound:
            agent = Constant(agent.name)
        return replace(node, agent=agent,
                       formula=resolve_agent_variables(node.formula, bound))
    if isinstance(node, (EverybodyKnows, DistributedKnowledge, CommonKnowledge)):
        group = tuple(
            Constant(a.name) if isinstance(a, Variable) and a.name not in bound else a
            for a in node.group
        )
        return replace(node, group=group,
                       formula=resolve_agent_variables(node.formula, bound))
    return node.map_children(lambda c: resolve_agent_variables(c, bound))


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

    ``agent`` is a **term** (Variable or Constant), a structural child, so it can be
    a quantified variable (``∀x (Student(x) → K_x φ)``). A bare string passed to the
    constructor is coerced to a Constant (a named agent) for backward compatibility.
    """

    agent: Node
    formula: Node

    def __post_init__(self):
        """Coerce a string agent to a Constant so legacy ``Knows("alice", φ)`` still works."""
        coerced = _coerce_agent(self.agent)
        if coerced is not self.agent:
            object.__setattr__(self, "agent", coerced)

    def _tree_parts(self):
        """Return the K_<agent> label and the single subformula child."""
        return f"K_{_agent_label(self.agent)}", [self.formula]

    def to_dict(self):
        """Serialise to dict with type tag, agent term, and serialised subformula."""
        return {"_type": "Knows", "agent": self.agent.to_dict(),
                "formula": self.formula.to_dict()}

    @staticmethod
    def from_dict(d):
        """Deserialise a Knows from a dict produced by to_dict (legacy string agent ok)."""
        agent = d["agent"]
        agent = Node.from_dict(agent) if isinstance(agent, dict) else agent
        return Knows(agent, Node.from_dict(d["formula"]))

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

    ``agent`` is a **term** (Variable or Constant), a structural child, so it can be a
    quantified variable. A bare string is coerced to a Constant for backward compatibility.
    """

    agent: Node
    formula: Node

    def __post_init__(self):
        """Coerce a string agent to a Constant so legacy ``Believes("alice", φ)`` still works."""
        coerced = _coerce_agent(self.agent)
        if coerced is not self.agent:
            object.__setattr__(self, "agent", coerced)

    def _tree_parts(self):
        """Return the B_<agent> label and the single subformula child."""
        return f"B_{_agent_label(self.agent)}", [self.formula]

    def to_dict(self):
        """Serialise to dict with type tag, agent term, and serialised subformula."""
        return {"_type": "Believes", "agent": self.agent.to_dict(),
                "formula": self.formula.to_dict()}

    @staticmethod
    def from_dict(d):
        """Deserialise a Believes from a dict produced by to_dict (legacy string agent ok)."""
        agent = d["agent"]
        agent = Node.from_dict(agent) if isinstance(agent, dict) else agent
        return Believes(agent, Node.from_dict(d["formula"]))

    def to_z3(self, env: Z3Env = None):
        """Reject Z3 export: modal operators have no direct first-order encoding."""
        raise NotImplementedError(_NO_EXPORT)

    def to_prover9(self) -> str:
        """Reject Prover9 export: modal operators have no direct first-order encoding."""
        raise NotImplementedError(_NO_EXPORT)

    def to_tptp(self) -> str:
        """Reject TPTP export: modal operators have no direct first-order encoding."""
        raise NotImplementedError(_NO_EXPORT)


#: Why the group-epistemic operators (E_G / D_G / C_G) have no direct
#: first-order export via to_z3/to_prover9/to_tptp, even though E_G and D_G
#: individually ARE first-order definable (see fol.modal_translation): every
#: modal node in this module rejects the classical back-ends directly and
#: requires going through modal_to_fol (standard_translation) first — the
#: SAME rule Knows/Believes themselves follow despite being FO-definable too.
_NO_GROUP_EXPORT = _NO_EXPORT


@dataclass(frozen=True)
class EverybodyKnows(Node):
    """Group-epistemic E_G φ: every agent in ``group`` knows φ (one-step).

    By definition E_G φ ≡ ⋀_{a∈G} K_a φ — equivalently, φ holds at every world
    reachable from the current one by a SINGLE edge of the UNION of the
    group's per-agent ``"K:"+agent`` relations (see
    :func:`unicode_fol_kit.semantics.action_models.everybody_knows`, which
    this node's :func:`~unicode_fol_kit.semantics.kripke.satisfies_modal`
    dispatch calls directly — the same "thin AST wrapper over an existing
    function" pattern :class:`Announce` uses for
    :func:`~unicode_fol_kit.semantics.dynamic_epistemic.announce`).

    ``group`` is a tuple of agent **terms** (Variable or Constant, exactly
    like :class:`Knows`'s ``agent`` field — each reachable by
    free_variables/substitution/β-reduction and resolved by the same
    :func:`resolve_agent_variables` scope pass, so a group member bound by an
    enclosing quantifier stays a Variable, e.g.
    ``∀x (Student(x) → E_{x,b} φ)``). An iterable of bare strings/Nodes is
    accepted and coerced. An EMPTY group is allowed and, matching
    :func:`everybody_knows`'s own convention, makes ``E_∅ φ`` vacuously true
    at every world (the union over zero relations is the empty relation).
    """

    group: Tuple[Node, ...]
    formula: Node

    def __post_init__(self):
        """Coerce every group member to a term Node (see :func:`_coerce_agent_group`)."""
        object.__setattr__(self, "group", _coerce_agent_group(self.group))

    def _tree_parts(self):
        """Return the E_{group} label and the single subformula child."""
        return f"E_{{{_group_label(self.group)}}}", [self.formula]

    def to_dict(self):
        """Serialise to dict with type tag, group terms, and serialised subformula."""
        return {"_type": "EverybodyKnows",
                "group": [a.to_dict() for a in self.group],
                "formula": self.formula.to_dict()}

    @staticmethod
    def from_dict(d):
        """Deserialise an EverybodyKnows from a dict produced by to_dict."""
        return EverybodyKnows(tuple(Node.from_dict(a) for a in d["group"]),
                              Node.from_dict(d["formula"]))

    def to_unicode_str(self) -> str:
        """Render as ``E_{a,b,c} φ`` (see the class docstring; overridden like
        :class:`Announce` — no registry fixity expresses a variable-length
        agent LIST, only :class:`Knows`'s single agent)."""
        post = _pal_wrap(self.formula, 4, lambda n: n.to_unicode_str())
        return f"E_{{{_group_label(self.group)}}} {post}"

    def to_latex(self) -> str:
        """Render as LaTeX ``\\mathsf{E}_{\\{a,b,c\\}} φ``."""
        from ._msfl_nodes import _latex_escape  # lazy: avoid a module-load-order cycle
        agents = ", ".join(_latex_escape(_agent_label(a)) for a in self.group)
        post = _pal_wrap(self.formula, 4, lambda n: n.to_latex())
        return f"\\mathsf{{E}}_{{\\{{{agents}\\}}}} {post}"

    def to_z3(self, env: Z3Env = None):
        """Reject Z3 export: modal operators have no direct first-order encoding."""
        raise NotImplementedError(_NO_GROUP_EXPORT)

    def to_prover9(self) -> str:
        """Reject Prover9 export: modal operators have no direct first-order encoding."""
        raise NotImplementedError(_NO_GROUP_EXPORT)

    def to_tptp(self) -> str:
        """Reject TPTP export: modal operators have no direct first-order encoding."""
        raise NotImplementedError(_NO_GROUP_EXPORT)


@dataclass(frozen=True)
class DistributedKnowledge(Node):
    """Group-epistemic D_G φ: φ is DISTRIBUTED knowledge in ``group`` (one-step).

    D_G φ holds at ``world`` iff φ holds at every world reachable by a SINGLE
    edge of the INTERSECTION ``⋂_{a∈G} R_a`` of the group's per-agent
    ``"K:"+agent`` relations — pooling every agent's information together.
    D_G is the LOGICALLY WEAKEST of the group notions (``K_a φ → D_G φ`` for
    every ``a ∈ G``, and transitively ``E_G φ → D_G φ`` / ``C_G φ → D_G φ``,
    never the converse — see
    :func:`~unicode_fol_kit.semantics.action_models.distributed_knowledge_holds`'s
    docstring for why "logically weakest formal constraint" is not in tension
    with "pools richer information": FHMV, *Reasoning About Knowledge*, MIT
    Press 1995, ch. 2). Dispatch goes to
    :func:`unicode_fol_kit.semantics.action_models.distributed_knowledge_holds`
    (same pattern as :class:`EverybodyKnows` / :func:`everybody_knows`).

    ``group`` is a tuple of agent terms exactly like :class:`EverybodyKnows`'s
    ``group`` (coerced, resolved by :func:`resolve_agent_variables`) — but,
    UNLIKE :class:`EverybodyKnows`/:class:`CommonKnowledge`, an EMPTY group is
    refused at construction: an intersection over an empty family is
    conventionally the UNIVERSAL relation, so ``D_∅ φ`` would demand φ true at
    literally every world of the model — a degenerate reading nobody
    constructing this node means, so this class raises loudly here (matching
    the same refusal
    :func:`~unicode_fol_kit.semantics.action_models.distributed_knowledge_holds`
    raises at evaluation time) rather than let it reach ``modal_to_fol``/the
    Kripke evaluator as a silent vacuous-universal.
    """

    group: Tuple[Node, ...]
    formula: Node

    def __post_init__(self):
        """Coerce every group member to a term Node; refuse an empty group."""
        object.__setattr__(self, "group", _coerce_agent_group(self.group))
        if not self.group:
            raise ValueError(
                "DistributedKnowledge: D_∅ φ (an empty group) is refused — an "
                "intersection over zero relations is conventionally the "
                "UNIVERSAL relation, which would make D_∅ φ demand φ at every "
                "world of the model, not a sensible reading of 'distributed "
                "knowledge of an empty group'. Name at least one agent."
            )

    def _tree_parts(self):
        """Return the D_{group} label and the single subformula child."""
        return f"D_{{{_group_label(self.group)}}}", [self.formula]

    def to_dict(self):
        """Serialise to dict with type tag, group terms, and serialised subformula."""
        return {"_type": "DistributedKnowledge",
                "group": [a.to_dict() for a in self.group],
                "formula": self.formula.to_dict()}

    @staticmethod
    def from_dict(d):
        """Deserialise a DistributedKnowledge from a dict produced by to_dict."""
        return DistributedKnowledge(tuple(Node.from_dict(a) for a in d["group"]),
                                    Node.from_dict(d["formula"]))

    def to_unicode_str(self) -> str:
        """Render as ``D_{a,b,c} φ`` (see :class:`EverybodyKnows`)."""
        post = _pal_wrap(self.formula, 4, lambda n: n.to_unicode_str())
        return f"D_{{{_group_label(self.group)}}} {post}"

    def to_latex(self) -> str:
        """Render as LaTeX ``\\mathsf{D}_{\\{a,b,c\\}} φ``."""
        from ._msfl_nodes import _latex_escape  # lazy: avoid a module-load-order cycle
        agents = ", ".join(_latex_escape(_agent_label(a)) for a in self.group)
        post = _pal_wrap(self.formula, 4, lambda n: n.to_latex())
        return f"\\mathsf{{D}}_{{\\{{{agents}\\}}}} {post}"

    def to_z3(self, env: Z3Env = None):
        """Reject Z3 export: modal operators have no direct first-order encoding."""
        raise NotImplementedError(_NO_GROUP_EXPORT)

    def to_prover9(self) -> str:
        """Reject Prover9 export: modal operators have no direct first-order encoding."""
        raise NotImplementedError(_NO_GROUP_EXPORT)

    def to_tptp(self) -> str:
        """Reject TPTP export: modal operators have no direct first-order encoding."""
        raise NotImplementedError(_NO_GROUP_EXPORT)


@dataclass(frozen=True)
class CommonKnowledge(Node):
    """Group-epistemic C_G φ: φ is COMMON knowledge in ``group``.

    C_G φ is the infinite conjunction ``E_G φ ∧ E_G E_G φ ∧ …`` — equivalently
    (FHMV, *Reasoning About Knowledge*, MIT Press 1995, §2.4), φ holds at
    every world reachable from the current one by the REFLEXIVE-TRANSITIVE
    closure of the group's union relation ``⋃_{a∈G} R_a``. Dispatch goes to
    :func:`unicode_fol_kit.semantics.action_models.common_knowledge_holds`
    (same pattern as :class:`EverybodyKnows`). UNLIKE E_G/D_G, C_G is NOT
    first-order definable (transitive closure): :func:`modal_to_fol`
    (:mod:`unicode_fol_kit.fol.modal_translation`) refuses it by name, exactly
    as it already refuses :class:`Until`/:class:`Since`.

    ``group`` is a tuple of agent terms exactly like :class:`EverybodyKnows`'s
    ``group`` (coerced, resolved by :func:`resolve_agent_variables`). An EMPTY
    group is allowed, matching :func:`common_knowledge_holds`'s own
    convention (``C_∅ φ`` reduces to plain ``φ`` — the reflexive closure of
    the empty relation is just the current world).
    """

    group: Tuple[Node, ...]
    formula: Node

    def __post_init__(self):
        """Coerce every group member to a term Node (see :func:`_coerce_agent_group`)."""
        object.__setattr__(self, "group", _coerce_agent_group(self.group))

    def _tree_parts(self):
        """Return the C_{group} label and the single subformula child."""
        return f"C_{{{_group_label(self.group)}}}", [self.formula]

    def to_dict(self):
        """Serialise to dict with type tag, group terms, and serialised subformula."""
        return {"_type": "CommonKnowledge",
                "group": [a.to_dict() for a in self.group],
                "formula": self.formula.to_dict()}

    @staticmethod
    def from_dict(d):
        """Deserialise a CommonKnowledge from a dict produced by to_dict."""
        return CommonKnowledge(tuple(Node.from_dict(a) for a in d["group"]),
                               Node.from_dict(d["formula"]))

    def to_unicode_str(self) -> str:
        """Render as ``C_{a,b,c} φ`` (see :class:`EverybodyKnows`)."""
        post = _pal_wrap(self.formula, 4, lambda n: n.to_unicode_str())
        return f"C_{{{_group_label(self.group)}}} {post}"

    def to_latex(self) -> str:
        """Render as LaTeX ``\\mathsf{C}_{\\{a,b,c\\}} φ``."""
        from ._msfl_nodes import _latex_escape  # lazy: avoid a module-load-order cycle
        agents = ", ".join(_latex_escape(_agent_label(a)) for a in self.group)
        post = _pal_wrap(self.formula, 4, lambda n: n.to_latex())
        return f"\\mathsf{{C}}_{{\\{{{agents}\\}}}} {post}"

    def to_z3(self, env: Z3Env = None):
        """Reject Z3 export: modal operators have no direct first-order encoding."""
        raise NotImplementedError(_NO_GROUP_EXPORT)

    def to_prover9(self) -> str:
        """Reject Prover9 export: modal operators have no direct first-order encoding."""
        raise NotImplementedError(_NO_GROUP_EXPORT)

    def to_tptp(self) -> str:
        """Reject TPTP export: modal operators have no direct first-order encoding."""
        raise NotImplementedError(_NO_GROUP_EXPORT)


NODE_CLASSES.update({
    "EverybodyKnows": EverybodyKnows,
    "DistributedKnowledge": DistributedKnowledge,
    "CommonKnowledge": CommonKnowledge,
})


@dataclass(frozen=True)
class Says(Node):
    """Assertive (reportative) Say_a φ: agent ``agent`` asserts/says that φ.

    A NON-factive, NON-doxastic attitude: ``Says_a φ`` does not entail φ (an
    assertion can be false) and does not entail ``Believes_a φ`` (one may assert
    what one disbelieves). It is the minimal normal modality K over its own
    per-agent ``"Say:"`` accessibility relation — no frame conditions — so neither
    factivity (T) nor any doxastic bridge is validated. ``agent`` is a **term**
    (Variable or Constant), a structural child, so a bound agent variable works
    (``∀x (Speaker(x) → Say_x φ)``); a bare string is coerced to a Constant.
    """

    agent: Node
    formula: Node

    def __post_init__(self):
        """Coerce a string agent to a Constant so ``Says("alice", φ)`` still works."""
        coerced = _coerce_agent(self.agent)
        if coerced is not self.agent:
            object.__setattr__(self, "agent", coerced)

    def _tree_parts(self):
        """Return the Say_<agent> label and the single subformula child."""
        return f"Say_{_agent_label(self.agent)}", [self.formula]

    def to_dict(self):
        """Serialise to dict with type tag, agent term, and serialised subformula."""
        return {"_type": "Says", "agent": self.agent.to_dict(),
                "formula": self.formula.to_dict()}

    @staticmethod
    def from_dict(d):
        """Deserialise a Says from a dict produced by to_dict (legacy string agent ok)."""
        agent = d["agent"]
        agent = Node.from_dict(agent) if isinstance(agent, dict) else agent
        return Says(agent, Node.from_dict(d["formula"]))

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
class Wants(Node):
    """Bouletic (desiderative) Want_a φ: agent ``agent`` wants it to be that φ.

    A NON-veridical attitude: ``Wants_a φ`` does not entail φ — wanting something
    does not make it so (this is the whole point: ``Wants_a(Fly(a)) ∧ Fly(a)`` is
    not derivable). It is the minimal normal modality K over its own per-agent
    ``"Want:"`` accessibility relation — no frame conditions — so veridicality (T)
    is not validated. ``agent`` is a **term** (Variable or Constant), a structural
    child, so a bound agent variable works; a bare string is coerced to a Constant.
    """

    agent: Node
    formula: Node

    def __post_init__(self):
        """Coerce a string agent to a Constant so ``Wants("alice", φ)`` still works."""
        coerced = _coerce_agent(self.agent)
        if coerced is not self.agent:
            object.__setattr__(self, "agent", coerced)

    def _tree_parts(self):
        """Return the Want_<agent> label and the single subformula child."""
        return f"Want_{_agent_label(self.agent)}", [self.formula]

    def to_dict(self):
        """Serialise to dict with type tag, agent term, and serialised subformula."""
        return {"_type": "Wants", "agent": self.agent.to_dict(),
                "formula": self.formula.to_dict()}

    @staticmethod
    def from_dict(d):
        """Deserialise a Wants from a dict produced by to_dict (legacy string agent ok)."""
        agent = d["agent"]
        agent = Node.from_dict(agent) if isinstance(agent, dict) else agent
        return Wants(agent, Node.from_dict(d["formula"]))

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


#: Why the counterfactual conditionals have no first-order (or Kripke) export.
_NO_COUNTERFACTUAL_EXPORT = (
    "Counterfactual conditionals (□→ / ◇→) are evaluated over a similarity "
    "ordering of worlds (Lewis spheres), not over an accessibility relation, and "
    "are not first-order definable — collapsing □→ to the material → is exactly "
    "the mistake the connective exists to avoid. Evaluate with "
    "unicode_fol_kit.cf_satisfies / would / might over a CounterfactualModel."
)


@dataclass(frozen=True)
class Would(Node):
    """Lewis counterfactual ``left □→ right`` — "if left WERE the case, right WOULD be".

    True at ``w`` iff no sphere around ``w`` contains a ``left``-world (vacuous), or
    else, in the SMALLEST sphere that does, every ``left``-world is a ``right``-world.
    Distinct from the material :class:`Implies`: "if kangaroos had no tails they would
    topple over" is not made true merely by kangaroos having tails.

    The similarity ordering is not an accessibility relation, so this node belongs to
    the sphere semantics (:mod:`unicode_fol_kit.semantics.conditional`) rather than to
    the Kripke evaluator, and it has no first-order export.
    """

    left: Node
    right: Node

    def _tree_parts(self):
        """Return the □→ label and the antecedent/consequent children."""
        return "□→", [self.left, self.right]

    def to_dict(self):
        """Serialise to dict with type tag and recursively serialised operands."""
        return {"_type": "Would", "left": self.left.to_dict(),
                "right": self.right.to_dict()}

    @staticmethod
    def from_dict(d):
        """Deserialise a Would from a dict produced by to_dict."""
        return Would(Node.from_dict(d["left"]), Node.from_dict(d["right"]))

    def to_z3(self, env: Z3Env = None):
        """Reject Z3 export: the counterfactual is not first-order definable."""
        raise NotImplementedError(_NO_COUNTERFACTUAL_EXPORT)

    def to_prover9(self) -> str:
        """Reject Prover9 export: the counterfactual is not first-order definable."""
        raise NotImplementedError(_NO_COUNTERFACTUAL_EXPORT)

    def to_tptp(self) -> str:
        """Reject TPTP export: the counterfactual is not first-order definable."""
        raise NotImplementedError(_NO_COUNTERFACTUAL_EXPORT)


@dataclass(frozen=True)
class Might(Node):
    """Lewis "might" counterfactual ``left ◇→ right`` — the dual ``¬(left □→ ¬right)``.

    "If left were the case, right MIGHT be": some closest ``left``-world is a
    ``right``-world. Note the duality makes it **vacuously false** exactly where
    :class:`Would` is vacuously true (no ``left``-world in any sphere).
    """

    left: Node
    right: Node

    def _tree_parts(self):
        """Return the ◇→ label and the antecedent/consequent children."""
        return "◇→", [self.left, self.right]

    def to_dict(self):
        """Serialise to dict with type tag and recursively serialised operands."""
        return {"_type": "Might", "left": self.left.to_dict(),
                "right": self.right.to_dict()}

    @staticmethod
    def from_dict(d):
        """Deserialise a Might from a dict produced by to_dict."""
        return Might(Node.from_dict(d["left"]), Node.from_dict(d["right"]))

    def to_z3(self, env: Z3Env = None):
        """Reject Z3 export: the counterfactual is not first-order definable."""
        raise NotImplementedError(_NO_COUNTERFACTUAL_EXPORT)

    def to_prover9(self) -> str:
        """Reject Prover9 export: the counterfactual is not first-order definable."""
        raise NotImplementedError(_NO_COUNTERFACTUAL_EXPORT)

    def to_tptp(self) -> str:
        """Reject TPTP export: the counterfactual is not first-order definable."""
        raise NotImplementedError(_NO_COUNTERFACTUAL_EXPORT)


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


@dataclass(frozen=True)
class Historically(Node):
    """Past-tense "has always been" Hφ: φ holds now and at every PAST point.

    The past dual of :class:`Always` (G): a □ over the *converse* of the one-step
    ``"temporal"`` relation, i.e. over the reflexive-transitive set of points from
    which the current world is reachable. Rendered with the parenthesised glyph
    ``⒣`` — the past operators are parenthesised so they read apart from the circled
    future operators (Ⓖ Ⓕ Ⓝ Ⓤ).
    """

    formula: Node

    def _tree_parts(self):
        """Return the ⒣ label and the single subformula child."""
        return "⒣", [self.formula]

    def to_dict(self):
        """Serialise to dict with type tag and recursively serialised subformula."""
        return {"_type": "Historically", "formula": self.formula.to_dict()}

    @staticmethod
    def from_dict(d):
        """Deserialise a Historically from a dict produced by to_dict."""
        return Historically(Node.from_dict(d["formula"]))

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
class Once(Node):
    """Past-tense "was once the case" Pφ: φ held now or at some PAST point.

    The past dual of :class:`Eventually` (F): a ◇ over the converse of the one-step
    ``"temporal"`` relation. Rendered with the parenthesised glyph ``⒫``.
    """

    formula: Node

    def _tree_parts(self):
        """Return the ⒫ label and the single subformula child."""
        return "⒫", [self.formula]

    def to_dict(self):
        """Serialise to dict with type tag and recursively serialised subformula."""
        return {"_type": "Once", "formula": self.formula.to_dict()}

    @staticmethod
    def from_dict(d):
        """Deserialise an Once from a dict produced by to_dict."""
        return Once(Node.from_dict(d["formula"]))

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
class Previous(Node):
    """Past-tense "yesterday" Yφ: φ holds at every immediate PAST point.

    The past dual of :class:`Next` (X): the □-style operator over the converse of
    the one-step ``"temporal"`` relation (universal over immediate predecessors, so
    vacuously true at a world with no past). Rendered with the parenthesised glyph
    ``⒴``.
    """

    formula: Node

    def _tree_parts(self):
        """Return the ⒴ label and the single subformula child."""
        return "⒴", [self.formula]

    def to_dict(self):
        """Serialise to dict with type tag and recursively serialised subformula."""
        return {"_type": "Previous", "formula": self.formula.to_dict()}

    @staticmethod
    def from_dict(d):
        """Deserialise a Previous from a dict produced by to_dict."""
        return Previous(Node.from_dict(d["formula"]))

    def to_z3(self, env: Z3Env = None):
        """Reject Z3 export: modal operators have no direct first-order encoding."""
        raise NotImplementedError(_NO_EXPORT)

    def to_prover9(self) -> str:
        """Reject Prover9 export: modal operators have no direct first-order encoding."""
        raise NotImplementedError(_NO_EXPORT)

    def to_tptp(self) -> str:
        """Reject TPTP export: modal operators have no direct first-order encoding."""
        raise NotImplementedError(_NO_EXPORT)


#: Why the PAL announcement operators have no direct first-order (or classical
#: Kripke) export: they denote a MODEL UPDATE, not a static accessibility relation.
_NO_PAL_EXPORT = (
    "Public-announcement operators ([φ!]ψ / ⟨φ!⟩ψ) denote a MODEL UPDATE (restrict "
    "the Kripke model to the worlds where the announcement is true), not a static "
    "accessibility relation, so they have no direct first-order (or classical "
    "Kripke) export. Eliminate them first with "
    "unicode_fol_kit.fol.pal.reduce_announcements (the standard PAL reduction "
    "axioms, producing an announcement-free modal formula), or evaluate them "
    "directly with semantics.kripke.satisfies_modal / "
    "semantics.dynamic_epistemic.announce."
)


def _pal_wrap(node: Node, min_prec: float, render) -> str:
    """Parenthesise ``render(node)`` when ``node`` binds looser than ``min_prec``.

    Mirrors ``_msfl_nodes._uni_wrap`` / ``_latex_wrap``'s parenthesisation rule
    (reusing the SAME precedence table, via the read-only helper ``_uni_prec``)
    but recurses through the CHILD's own ``to_unicode_str`` / ``to_latex`` method
    rather than the module-level ``_uni`` / ``_latex`` dispatcher — the
    announcements' bracket-delimited two-argument shape fits none of the six
    registered operator fixities, so they render via these overrides; the
    central dispatcher delegates back here for announcement CHILDREN (see the
    "RENDERING" paragraph on :class:`Announce`).
    """
    from ._msfl_nodes import _uni_prec  # lazy: avoid a module-load-order cycle
    text = render(node)
    return f"({text})" if _uni_prec(node) < min_prec else text


@dataclass(frozen=True)
class Announce(Node):
    """Public-announcement box ``[announcement!]formula`` (PAL): after a truthful
    public announcement of ``announcement``, ``formula`` holds.

    ``M, w ⊨ [φ!]ψ`` iff ``M, w ⊨ φ`` implies ``M|φ, w ⊨ ψ``, where ``M|φ`` is the
    model restricted to the worlds satisfying ``φ``
    (:func:`unicode_fol_kit.semantics.dynamic_epistemic.announce`), which
    :func:`unicode_fol_kit.semantics.kripke.satisfies_modal` calls directly for
    this node — the ORACLE that
    :func:`unicode_fol_kit.fol.pal.reduce_announcements` (the syntactic
    reduction to an announcement-free modal formula) is differentially tested
    against. Vacuously true when ``announcement`` is false at the evaluation
    world (an untruthful announcement is not made).

    Both fields are formulas. ``announcement`` (φ) is delimited by the surface
    brackets ``[ … !]`` and so parses at FULL formula precedence — exactly like
    the base grammar's own ``"(" formula ")"`` grouping or Cardinality's
    ``"|{" v ":" φ "}|"``. ``formula`` (ψ), the post-condition following the
    closing bracket, parses at the PREFIX level (as tightly as ¬ / □ / K_a): a
    deliberate design choice mirroring how every other modal operator in this
    module binds, so ``[p!]q ∧ r`` groups as ``([p!]q) ∧ r``, not
    ``[p!](q ∧ r)`` — see the parser-registration comment below.

    RENDERING: ``to_unicode_str`` / ``to_latex`` are direct method overrides on
    this class, NOT driven by ``register_operator``'s central registry. Each of
    the registry's six fixities (prefix, agent_prefix, binary_iff,
    binary_implies, binary_until, level2) is a single FIXED template string, and
    none can express "bracket, formula, delimiter, bracket, ANOTHER formula" —
    two independent operands with the second one OUTSIDE the delimiters. The
    override recurses via each child's own ``to_unicode_str`` / ``to_latex``,
    and the MODULE-LEVEL ``_msfl_nodes._uni`` / ``_latex`` dispatchers carry a
    matching delegation case (plus prefix-level precedence entries in
    ``_UNI_BASE_PREC``), so an Announce/AnnounceDiamond renders — and
    round-trips — both as the outer node and nested at any depth under any
    registry-driven operator (∧ / → / ¬ / □ / K_a / …); see
    ``tests/test_pal.py``.
    """

    announcement: Node
    formula: Node

    def _tree_parts(self):
        """Return the "[!]" label and the [announcement, formula] children."""
        return "[!]", [self.announcement, self.formula]

    def to_dict(self):
        """Serialise to dict with type tag and both serialised operands."""
        return {"_type": "Announce", "announcement": self.announcement.to_dict(),
                "formula": self.formula.to_dict()}

    @staticmethod
    def from_dict(d):
        """Deserialise an Announce from a dict produced by to_dict."""
        return Announce(Node.from_dict(d["announcement"]), Node.from_dict(d["formula"]))

    def to_unicode_str(self) -> str:
        """Render as ``[announcement!]formula`` (see the class docstring)."""
        post = _pal_wrap(self.formula, 4, lambda n: n.to_unicode_str())
        return f"[{self.announcement.to_unicode_str()}!]{post}"

    def to_latex(self) -> str:
        """Render as LaTeX ``[announcement\\mathbin{!}]formula``."""
        post = _pal_wrap(self.formula, 4, lambda n: n.to_latex())
        return f"[{self.announcement.to_latex()}\\mathbin{{!}}]{post}"

    def to_z3(self, env: Z3Env = None):
        """Reject Z3 export: a model update has no static first-order encoding."""
        raise NotImplementedError(_NO_PAL_EXPORT)

    def to_prover9(self) -> str:
        """Reject Prover9 export: a model update has no static first-order encoding."""
        raise NotImplementedError(_NO_PAL_EXPORT)

    def to_tptp(self) -> str:
        """Reject TPTP export: a model update has no static first-order encoding."""
        raise NotImplementedError(_NO_PAL_EXPORT)


@dataclass(frozen=True)
class AnnounceDiamond(Node):
    """Public-announcement diamond ``⟨announcement!⟩formula`` (PAL): the truthful
    dual of :class:`Announce` — ``announcement`` is (actually) true AND, after
    announcing it, ``formula`` holds.

    ``M, w ⊨ ⟨φ!⟩ψ`` iff ``M, w ⊨ φ`` AND ``M|φ, w ⊨ ψ``. See :class:`Announce`
    for the shared oracle / precedence / rendering contract; the surface syntax
    swaps square brackets for angle brackets (``⟨ … !⟩``, U+27E8/U+27E9) — a
    glyph pair unused elsewhere in the grammar, so unlike ``Announce``'s ``[``/``]``
    it needs no disambiguation against another rule at all.
    """

    announcement: Node
    formula: Node

    def _tree_parts(self):
        """Return the "⟨!⟩" label and the [announcement, formula] children."""
        return "⟨!⟩", [self.announcement, self.formula]

    def to_dict(self):
        """Serialise to dict with type tag and both serialised operands."""
        return {"_type": "AnnounceDiamond", "announcement": self.announcement.to_dict(),
                "formula": self.formula.to_dict()}

    @staticmethod
    def from_dict(d):
        """Deserialise an AnnounceDiamond from a dict produced by to_dict."""
        return AnnounceDiamond(Node.from_dict(d["announcement"]), Node.from_dict(d["formula"]))

    def to_unicode_str(self) -> str:
        """Render as ``⟨announcement!⟩formula`` (see :class:`Announce`)."""
        post = _pal_wrap(self.formula, 4, lambda n: n.to_unicode_str())
        return f"⟨{self.announcement.to_unicode_str()}!⟩{post}"

    def to_latex(self) -> str:
        """Render as LaTeX ``\\langle announcement\\mathbin{!}\\rangle formula``."""
        post = _pal_wrap(self.formula, 4, lambda n: n.to_latex())
        return f"\\langle {self.announcement.to_latex()}\\mathbin{{!}}\\rangle {post}"

    def to_z3(self, env: Z3Env = None):
        """Reject Z3 export: a model update has no static first-order encoding."""
        raise NotImplementedError(_NO_PAL_EXPORT)

    def to_prover9(self) -> str:
        """Reject Prover9 export: a model update has no static first-order encoding."""
        raise NotImplementedError(_NO_PAL_EXPORT)

    def to_tptp(self) -> str:
        """Reject TPTP export: a model update has no static first-order encoding."""
        raise NotImplementedError(_NO_PAL_EXPORT)


NODE_CLASSES.update({"Announce": Announce, "AnnounceDiamond": AnnounceDiamond})


@dataclass(frozen=True)
class Since(Node):
    """Past-tense "left since right" (left S right): the mirror of :class:`Until`.

    Holds at the current point iff ``right`` was true at some past point and ``left``
    has held at every point strictly since then up to now — the exact backward dual
    of strong Until over the one-step ``"temporal"`` relation. Rendered ``⒮``.
    """

    left: Node
    right: Node

    def _tree_parts(self):
        """Return the ⒮ label and the two subformula children."""
        return "⒮", [self.left, self.right]

    def to_dict(self):
        """Serialise to dict with type tag and recursively serialised operands."""
        return {"_type": "Since", "left": self.left.to_dict(), "right": self.right.to_dict()}

    @staticmethod
    def from_dict(d):
        """Deserialise a Since from a dict produced by to_dict."""
        return Since(Node.from_dict(d["left"]), Node.from_dict(d["right"]))

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
register_operator(Says, "agent_prefix", "Say_", "\\mathsf{Say}", 4)
register_operator(Wants, "agent_prefix", "Want_", "\\mathsf{Want}", 4)
register_operator(Until, "binary_until", "Ⓤ", "\\mathbin{\\mathsf{U}}", 2.5)
# Past-tense (parenthesised glyphs to read apart from the circled future
# operators; LaTeX overlined so ⒫ never collides with the deontic \mathsf{P}=Ⓟ).
register_operator(Historically, "prefix", "⒣", "\\overline{\\mathsf{H}} ", 4)
register_operator(Once, "prefix", "⒫", "\\overline{\\mathsf{P}} ", 4)
register_operator(Previous, "prefix", "⒴", "\\overline{\\mathsf{Y}} ", 4)
register_operator(Since, "binary_until", "⒮", "\\mathbin{\\overline{\\mathsf{S}}}", 2.5)
# Counterfactuals sit at the Until level (2.5): tighter than → and ↔, looser than
# ∧/∨, so `P ∧ Q □→ R` groups as `(P ∧ Q) □→ R` — the reading the English has.
register_operator(Would, "binary_until", "□→", "\\mathbin{\\Box\\!\\rightarrow}", 2.5)
register_operator(Might, "binary_until", "◇→", "\\mathbin{\\Diamond\\!\\rightarrow}", 2.5)


# =========================
# Parser registration (modal mode)
# =========================
#
# Self-register the modal/epistemic/doxastic/temporal/deontic operators with the
# PARSER registry so MSFLParser assembles the modal grammar + transformer from the
# registry alone — there is no hand-written modal transformer or modal grammar file:
#
#   * The prefix operators (□ ◇ Ⓖ Ⓕ Ⓝ K_a B_a Ⓞ Ⓟ) sit at the ¬ (prefix) level —
#     ``OP prefix -> alias`` — binding as tightly as negation. The classical ¬
#     (not_) is registered for "modal" in _fol_nodes.py; these add to it.
#   * Until (Ⓤ) is the binary right-assoc level between the same_level group and →;
#     registering ANY "until"-level op makes build_grammar route the → level's
#     left operand through the until rule (impl_body = "until"), giving the
#     ``?implication: until`` layering. Its grammar field is the bare TUNTIL
#     terminal; build_grammar wraps it as ``same_level_ops TUNTIL until``.
#   * Knows/Believes carry their agent in the matched token (e.g. "K_alice"); the
#     transform strips the two-character "K_"/"B_" prefix.
#
# Named terminals (with their lexer priorities) are declared via terminal_def so
# the generated grammar lexes K_a / B_a as KNOWS/BELIEVES (priority 5) ahead of
# PREDICATE (terminals come from terminals.lark).

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
                   lambda items: Knows(parse_agent_token(items[0]), items[1]),
                   terminal_name="KNOWS", terminal_def='KNOWS.5: /K_[a-z][a-zA-Z0-9]*/')
register_parser_op(Believes, "modal", "prefix", "believes_", "BELIEVES prefix",
                   lambda items: Believes(parse_agent_token(items[0]), items[1]),
                   terminal_name="BELIEVES", terminal_def='BELIEVES.5: /B_[a-z][a-zA-Z0-9]*/')
# Assertive Say_<agent> / bouletic Want_<agent>: agent_prefix like Knows/Believes.
# The "Say_"/"Want_" prefix is 4/5 characters; parse_agent_token strips it to get
# the agent name. Priority 5 so the token wins over PREDICATE (Say_alice, Want_x).
register_parser_op(Says, "modal", "prefix", "says_", "SAYS prefix",
                   lambda items: Says(parse_agent_token(items[0], 4), items[1]),
                   terminal_name="SAYS", terminal_def='SAYS.5: /Say_[a-z][a-zA-Z0-9]*/')
register_parser_op(Wants, "modal", "prefix", "wants_", "WANTS prefix",
                   lambda items: Wants(parse_agent_token(items[0], 5), items[1]),
                   terminal_name="WANTS", terminal_def='WANTS.5: /Want_[a-z][a-zA-Z0-9]*/')
register_parser_op(Obligatory, "modal", "prefix", "obligatory_", "OBLIG prefix",
                   lambda items: Obligatory(items[1]),
                   terminal_name="OBLIG", terminal_def='OBLIG: "Ⓞ"')
register_parser_op(Permitted, "modal", "prefix", "permitted_", "PERMIT prefix",
                   lambda items: Permitted(items[1]),
                   terminal_name="PERMIT", terminal_def='PERMIT: "Ⓟ"')

# --- binary temporal Until (Ⓤ): same_level_ops TUNTIL until -> until_ ---
# items = [left, TUNTIL token, right]; the token is the named terminal (kept in
# the item list), so the right operand is items[2].
register_parser_op(Until, "modal", "until", "until_", "TUNTIL",
                   lambda items: Until(items[0], items[2]),
                   terminal_name="TUNTIL", terminal_def='TUNTIL: "Ⓤ"')

# --- past-tense prefix operators (¬-level) ---
register_parser_op(Historically, "modal", "prefix", "historically_", "PAST_H prefix",
                   lambda items: Historically(items[1]),
                   terminal_name="PAST_H", terminal_def='PAST_H: "⒣"')
register_parser_op(Once, "modal", "prefix", "once_", "PAST_P prefix",
                   lambda items: Once(items[1]),
                   terminal_name="PAST_P", terminal_def='PAST_P: "⒫"')
register_parser_op(Previous, "modal", "prefix", "previous_", "PAST_Y prefix",
                   lambda items: Previous(items[1]),
                   terminal_name="PAST_Y", terminal_def='PAST_Y: "⒴"')

# --- past-tense binary Since (⒮): same until-level as Ⓤ ---
register_parser_op(Since, "modal", "until", "since_", "TSINCE",
                   lambda items: Since(items[0], items[2]),
                   terminal_name="TSINCE", terminal_def='TSINCE: "⒮"')

# --- counterfactual conditionals (□→ / ◇→) --------------------------------
# Explicit terminal priority: the glyphs START with the box/diamond glyphs, so
# without it "□→" could lex as BOX followed by the implication arrow and the
# counterfactual would silently parse as a modalised material conditional.
register_parser_op(Would, "modal", "until", "would_", "CFWOULD",
                   lambda items: Would(items[0], items[2]),
                   terminal_name="CFWOULD", terminal_def='CFWOULD.5: "□→"')
register_parser_op(Might, "modal", "until", "might_", "CFMIGHT",
                   lambda items: Might(items[0], items[2]),
                   terminal_name="CFMIGHT", terminal_def='CFMIGHT.5: "◇→"')

# --- Public Announcement Logic (PAL): [φ!]ψ / ⟨φ!⟩ψ -----------------------
#
# Parser-ONLY registration: unlike every other operator in this module,
# Announce/AnnounceDiamond are NOT passed to register_operator, because none of
# its six fixities (prefix, agent_prefix, binary_iff, binary_implies,
# binary_until, level2) can express a construct with a formula BETWEEN two
# delimiters and a SECOND, independent formula after the closing delimiter. They
# render via their own to_unicode_str/to_latex overrides instead (see the
# "RENDERING" paragraph on the Announce class) and are added to NODE_CLASSES
# directly above — mirroring how Nominal (also outside the registry, for the
# same reason: an atomic construct the six fixities cannot express) is handled
# in _hybrid_nodes.py.
#
# Both operators sit at the "prefix" level: the announcement (φ) is parsed as a
# full `formula` — it is fully delimited by its own brackets, exactly like the
# base grammar's `"(" formula ")"` grouping or Cardinality's `"|{" v ":" φ "}|"`
# — while the post-condition (ψ) is parsed as `prefix`, binding as tightly as
# ¬ / □ / K_a (the convention every other operator in this module follows), so
# `[p!]q ∧ r` groups as `([p!]q) ∧ r`, not `[p!](q ∧ r)`.
#
# Terminal design / collision note: the base grammar TEMPLATE already has a
# `"[" formula "]"` alternative (plain bracket-grouping, equivalent to parens) at
# this same `prefix` level (see _fol_nodes._BASE_GRAMMAR_TEMPLATE). Reusing
# "["/"]" for the PAL box syntax is therefore the LEAST-INTRUSIVE choice: it
# shares the SAME anonymous terminal with that existing rule instead of
# introducing a new bracket glyph, and Lark's Earley parser accepts two
# alternatives with a common leading literal with no special priority
# annotation needed (unlike the lexer-priority fix CFWOULD/CFMIGHT need above,
# this is a grammar-RULE-level, not a terminal-level, ambiguity question). The
# two rules cannot actually collide on any input: bracket-grouping requires "]"
# to close the bracketed formula immediately, whereas this rule requires a
# literal "!" first — a character that occurs in NO other terminal or rule in
# the grammar — so a given "[...]" span parses under at most one of the two
# alternatives (round-tripped in tests/test_pal.py: "[p]" parses as plain
# grouping, "[p!]q" as Announce, and nothing straddles the two readings). The
# diamond form's "⟨"/"⟩" (U+27E8/U+27E9) are not used ANYWHERE else in the
# grammar, so it has no collision to document at all.
register_parser_op(Announce, "modal", "prefix", "announce_",
                   '"[" formula "!" "]" prefix',
                   lambda items: Announce(items[0], items[1]))
register_parser_op(AnnounceDiamond, "modal", "prefix", "announce_diamond_",
                   '"⟨" formula "!" "⟩" prefix',
                   lambda items: AnnounceDiamond(items[0], items[1]))


# --- group-epistemic operators: E_{a,b,…} / D_{a,b,…} / C_{a,b,…} ----------
#
# Knows/Believes/Says/Wants each carry exactly ONE agent, folded into the
# matched token itself ("K_alice" as a single KNOWS terminal) — the
# `agent_prefix` machinery `register_operator` drives is built around that
# single-token shape and has no way to express a variable-length LIST of
# agents, so (like Announce/AnnounceDiamond just above) these three are
# parser-only registrations with their own to_unicode_str/to_latex overrides
# rather than register_operator calls; NODE_CLASSES already carries them (see
# the NODE_CLASSES.update() next to the three class definitions above).
#
# Surface syntax: GLYPH_{agent,agent,…} formula — e.g. "C_{a,b,c} φ",
# "D_{a,b} φ", "E_{a,b,c} φ". Each opening glyph is its OWN named terminal
# fusing the letter, the underscore AND the opening brace into one token
# ("C_{" / "D_{" / "E_{"), exactly so the lexer never has to choose between
# it and a same-length PREDICATE match: a bare predicate named "C_" can only
# ever lex as PREDICATE up to the "_" (no valid PREDICATE character follows
# a "{"), so GROUP_C's 3-character match is strictly LONGER at every
# position it can start, and standard longest-match lexing picks it with no
# ambiguity to resolve by priority — the ".5" priority below is added anyway,
# purely for consistency with KNOWS/BELIEVES/SAYS/WANTS/COUNTOP/CFWOULD/
# CFMIGHT's own explicit-priority convention, not because it changes the
# outcome here. "C_"/"D_"/"E_" are not used as a prefix ANYWHERE else in the
# grammar (Historically/Once/Previous use the parenthesised glyphs ⒣⒫⒴, not
# ASCII letters), so this introduces no collision with any existing operator.
#
# After the opening terminal, each agent is an ordinary VARIABLE (a, b, x1 —
# single term-valued letter + digits) or NAME (alice, carol_smith — ≥2
# letters, matching what Knows'/Believes' own agent regex already accepts)
# token, comma-separated, closed by a bare "}" — the SAME anonymous "}"
# terminal Cardinality's "|{v : φ}|" and (in the dependence mode) the slashed
# existential's "∃x/{y, z}" already use, so no new terminal is introduced for
# it either. Lark's inline `(A|B) ("," (A|B))*` repetition is already proven
# for exactly this "name, name, …" shape by SlashedExists's slash set in
# _team_nodes.py — mirrored here. Both VARIABLE and NAME tokens are
# auto-transformed to Variable/Constant Nodes by FOLTransformer.VARIABLE/.NAME
# (bottom-up, before this rule's own transform runs — see
# _team_nodes.py's ``_slashed_transform`` for the identical items-slicing
# pattern), so ``items[1:-1]`` below is already a tuple of agent term Nodes
# and needs no further parsing — exactly the Variable/Constant shape
# resolve_agent_variables (this module) expects for EverybodyKnows/
# DistributedKnowledge/CommonKnowledge's ``group`` field. The trailing
# ``prefix`` operand (the payload φ) binds at the SAME precedence every other
# operator in this module uses for its post-modality operand.
#
# The grammar REQUIRES at least one agent (VARIABLE|NAME, not optional), so
# the parser can never produce an empty group; DistributedKnowledge's own
# __post_init__ additionally refuses one built directly through the Python
# API (see that class's docstring) — modal_to_fol therefore never has to
# render a D_∅.
def _group_transform(node_cls):
    """Build ``node_cls(group, formula)`` from [GLYPH token, agent…, formula]."""
    def transform(items):
        return node_cls(tuple(items[1:-1]), items[-1])
    return transform


register_parser_op(
    CommonKnowledge, "modal", "prefix", "common_knowledge_",
    'GROUP_C (VARIABLE|NAME) ("," (VARIABLE|NAME))* "}" prefix',
    _group_transform(CommonKnowledge),
    terminal_name="GROUP_C", terminal_def='GROUP_C.5: "C_{"')
register_parser_op(
    DistributedKnowledge, "modal", "prefix", "distributed_knowledge_",
    'GROUP_D (VARIABLE|NAME) ("," (VARIABLE|NAME))* "}" prefix',
    _group_transform(DistributedKnowledge),
    terminal_name="GROUP_D", terminal_def='GROUP_D.5: "D_{"')
register_parser_op(
    EverybodyKnows, "modal", "prefix", "everybody_knows_",
    'GROUP_E (VARIABLE|NAME) ("," (VARIABLE|NAME))* "}" prefix',
    _group_transform(EverybodyKnows),
    terminal_name="GROUP_E", terminal_def='GROUP_E.5: "E_{"')
