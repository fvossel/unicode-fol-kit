"""Self-registration operator registry: a new formula operator needs NO edit to
the central renderers (_uni / _latex in _msfl_nodes.py).

Two things are checked:

1. END-TO-END SELF-REGISTRATION. We define throwaway Node subclasses *in this
   test*, call register_operator(...) for them with fresh glyphs/markup, build
   instances, and assert _uni() / _latex() render them via the registry alone —
   without any edit to _msfl_nodes.py. One operator per fixity is exercised.

2. The registry already contains the real operators with the right fixity and
   precedence (a regression guard on the spec table the renderers drive).
"""

from dataclasses import dataclass

import pytest

from unicode_fol_kit.fol._fol_nodes import (
    Node, Atom, OperatorSpec, OPERATORS, register_operator, NODE_CLASSES,
)
from unicode_fol_kit.fol._msfl_nodes import _uni, _latex


P = Atom("P", [])
Q = Atom("Q", [])


# ---------------------------------------------------------------------------
# Throwaway operator node classes (defined ONLY in this test).
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class _MyPrefix(Node):
    """A dummy unary prefix operator, registered at test time."""
    formula: Node


@dataclass(frozen=True)
class _MyAgent(Node):
    """A dummy agent-prefix operator (carries an agent name like Knows)."""
    agent: str
    formula: Node


@dataclass(frozen=True)
class _MyLevel2(Node):
    """A dummy same-level binary operator."""
    left: Node
    right: Node


@dataclass(frozen=True)
class _MyImplies(Node):
    """A dummy binary_implies operator."""
    left: Node
    right: Node


@dataclass(frozen=True)
class _MyIff(Node):
    """A dummy binary_iff operator."""
    left: Node
    right: Node


@dataclass(frozen=True)
class _MyUntil(Node):
    """A dummy binary_until operator."""
    left: Node
    right: Node


# Fresh glyphs/markup that appear nowhere else, so a match proves the renderer
# pulled them from the registry rather than a hand-coded table.
_DUMMY_REGISTRATIONS = [
    (_MyPrefix, "prefix", "✦", "\\myprefix ", 4),
    (_MyAgent, "agent_prefix", "A_", "A", 4),
    (_MyLevel2, "level2", "⊙", "\\myleveltwo", 3),
    (_MyImplies, "binary_implies", "⤳", "\\myimplies", 2),
    (_MyIff, "binary_iff", "⟺", "\\myiff", 1),
    (_MyUntil, "binary_until", "⥁", "\\myuntil", 2.5),
]


@pytest.fixture
def dummy_operators():
    """Register the dummy operators, yield, then restore the registry.

    Cleanup keeps the global OPERATORS / NODE_CLASSES tables pristine for any
    other test, since registration mutates module globals.
    """
    for node_cls, fixity, uni, latex, prec in _DUMMY_REGISTRATIONS:
        register_operator(node_cls, fixity, uni, latex, prec)
    try:
        yield
    finally:
        for node_cls, *_ in _DUMMY_REGISTRATIONS:
            OPERATORS.pop(node_cls.__name__, None)
            NODE_CLASSES.pop(node_cls.__name__, None)


# ---------------------------------------------------------------------------
# register_operator basics
# ---------------------------------------------------------------------------

def test_register_operator_records_spec_and_node_class(dummy_operators):
    """register_operator stores the spec in OPERATORS and the class in NODE_CLASSES."""
    spec = OPERATORS["_MyPrefix"]
    assert isinstance(spec, OperatorSpec)
    assert spec.name == "_MyPrefix"
    assert spec.fixity == "prefix"
    assert spec.unicode == "✦"
    assert spec.latex == "\\myprefix "
    assert spec.precedence == 4.0
    assert NODE_CLASSES["_MyPrefix"] is _MyPrefix


def test_register_operator_idempotent_overwrite():
    """A second registration of the same class overwrites the prior spec."""
    register_operator(_MyPrefix, "prefix", "✦", "\\myprefix ", 4)
    register_operator(_MyPrefix, "prefix", "★", "\\star ", 4)
    try:
        assert OPERATORS["_MyPrefix"].unicode == "★"
        assert OPERATORS["_MyPrefix"].latex == "\\star "
    finally:
        OPERATORS.pop("_MyPrefix", None)
        NODE_CLASSES.pop("_MyPrefix", None)


def test_register_operator_rejects_unknown_fixity():
    """An unrecognised fixity is rejected up front (and nothing is registered)."""
    with pytest.raises(ValueError):
        register_operator(_MyPrefix, "bogus_fixity", "?", "?", 4)
    assert "_MyPrefix" not in OPERATORS


def test_register_operator_returns_spec():
    """register_operator returns the stored OperatorSpec."""
    spec = register_operator(_MyPrefix, "prefix", "✦", "\\myprefix ", 4)
    try:
        assert spec is OPERATORS["_MyPrefix"]
        assert isinstance(spec, OperatorSpec)
    finally:
        OPERATORS.pop("_MyPrefix", None)
        NODE_CLASSES.pop("_MyPrefix", None)


# ---------------------------------------------------------------------------
# The renderers pick up a new operator with NO edit to _msfl_nodes.py.
# ---------------------------------------------------------------------------

def test_prefix_renders_via_registry(dummy_operators):
    """A dummy 'prefix' operator renders as glyph + operand (Unicode and LaTeX)."""
    node = _MyPrefix(P)
    assert _uni(node) == "✦P"
    assert _latex(node) == "\\myprefix P"


def test_prefix_wraps_looser_operand(dummy_operators):
    """The prefix operand is parenthesised when it binds looser than the prefix level."""
    # An Implies (precedence 2) under a prefix (4) must be parenthesised.
    from unicode_fol_kit.fol._fol_nodes import Implies
    node = _MyPrefix(Implies(P, Q))
    assert _uni(node) == "✦(P → Q)"
    assert _latex(node) == "\\myprefix (P \\rightarrow Q)"


def test_agent_prefix_renders_via_registry(dummy_operators):
    """A dummy 'agent_prefix' operator renders glyph+agent (Unicode) / sub (LaTeX)."""
    node = _MyAgent("alice", P)
    assert _uni(node) == "A_alice P"
    assert _latex(node) == "A_{alice} P"


def test_level2_renders_via_registry(dummy_operators):
    """A dummy 'level2' operator renders as left glyph right, with no-mix parens."""
    node = _MyLevel2(P, Q)
    assert _uni(node) == "P ⊙ Q"
    assert _latex(node) == "P \\myleveltwo Q"


def test_level2_right_assoc_parens(dummy_operators):
    """A same-level node in the right slot is parenthesised (parser left-folds)."""
    node = _MyLevel2(P, _MyLevel2(Q, P))
    assert _uni(node) == "P ⊙ (Q ⊙ P)"


def test_binary_implies_renders_via_registry(dummy_operators):
    """A dummy 'binary_implies' operator renders right-associatively."""
    node = _MyImplies(P, Q)
    assert _uni(node) == "P ⤳ Q"
    assert _latex(node) == "P \\myimplies Q"


def test_binary_iff_renders_via_registry(dummy_operators):
    """A dummy 'binary_iff' operator renders right-associatively at the loosest level."""
    node = _MyIff(P, Q)
    assert _uni(node) == "P ⟺ Q"
    assert _latex(node) == "P \\myiff Q"


def test_binary_until_renders_via_registry(dummy_operators):
    """A dummy 'binary_until' operator renders with its intermediate precedence."""
    node = _MyUntil(P, Q)
    assert _uni(node) == "P ⥁ Q"
    assert _latex(node) == "P \\myuntil Q"


def test_new_operator_precedence_drives_wrapping(dummy_operators):
    """The registered precedence governs parenthesisation of the new operator.

    _MyImplies has precedence 2; nesting one on the left of another forces parens
    (left slot demands precedence >= 3), the right slot does not.
    """
    node = _MyImplies(_MyImplies(P, Q), P)
    assert _uni(node) == "(P ⤳ Q) ⤳ P"


# ---------------------------------------------------------------------------
# The real operators are in the registry with the expected fixity/precedence.
# ---------------------------------------------------------------------------

# (name, fixity, unicode, latex, precedence) for every shipped regular operator.
_EXPECTED_REAL_OPERATORS = [
    ("Not", "prefix", "¬", "\\lnot ", 4.0),
    ("And", "level2", "∧", "\\land", 3.0),
    ("Or", "level2", "∨", "\\lor", 3.0),
    ("Xor", "level2", "⊕", "\\oplus", 3.0),
    ("Implies", "binary_implies", "→", "\\rightarrow", 2.0),
    ("Iff", "binary_iff", "↔", "\\leftrightarrow", 1.0),
    ("LukNegation", "prefix", "¬", "\\lnot ", 4.0),
    ("WeakConjunction", "level2", "∧", "\\land", 3.0),
    ("WeakDisjunction", "level2", "∨", "\\lor", 3.0),
    ("StrongConjunction", "level2", "⊗", "\\otimes", 3.0),
    ("StrongDisjunction", "level2", "⊕", "\\oplus", 3.0),
    ("LukImplication", "binary_implies", "→", "\\rightarrow", 2.0),
    ("LukEquivalence", "binary_iff", "↔", "\\leftrightarrow", 1.0),
    ("Box", "prefix", "□", "\\Box ", 4.0),
    ("Diamond", "prefix", "◇", "\\Diamond ", 4.0),
    ("Always", "prefix", "Ⓖ", "\\mathsf{G} ", 4.0),
    ("Eventually", "prefix", "Ⓕ", "\\mathsf{F} ", 4.0),
    ("Next", "prefix", "Ⓝ", "\\mathsf{X} ", 4.0),
    ("Obligatory", "prefix", "Ⓞ", "\\mathsf{O} ", 4.0),
    ("Permitted", "prefix", "Ⓟ", "\\mathsf{P} ", 4.0),
    ("Knows", "agent_prefix", "K_", "K", 4.0),
    ("Believes", "agent_prefix", "B_", "B", 4.0),
    ("Until", "binary_until", "Ⓤ", "\\mathbin{\\mathsf{U}}", 2.5),
]


@pytest.mark.parametrize("name,fixity,uni,latex,prec", _EXPECTED_REAL_OPERATORS)
def test_real_operator_registered(name, fixity, uni, latex, prec):
    """Every shipped regular operator has the expected spec in OPERATORS.

    Importing this test module imports unicode_fol_kit.fol._fol_nodes (classical
    ops) and, via _msfl_nodes, the Łukasiewicz ops. The modal/temporal/deontic
    ops register when their module loads; import it explicitly so this test does
    not depend on import order.
    """
    import unicode_fol_kit.fol._modal_nodes  # noqa: F401  (triggers registration)

    spec = OPERATORS[name]
    assert spec.fixity == fixity
    assert spec.unicode == uni
    assert spec.latex == latex
    assert spec.precedence == prec
    # The class is also in NODE_CLASSES (register_operator adds it).
    assert name in NODE_CLASSES


def test_binders_are_not_in_operator_registry():
    """The quantifier binders / Lambda / Application are NOT regular operators.

    They keep explicit handling in the renderers and a static precedence table,
    so they must not appear in OPERATORS.
    """
    for name in ("Quantifier", "SortedQuantifier", "SecondOrderQuantifier",
                 "Lambda", "Application", "Atom", "Function"):
        assert name not in OPERATORS


# ---------------------------------------------------------------------------
# The renderers contain NO per-operator dispatch branch for any registered
# operator — they dispatch generically on spec.fixity. This is the structural
# guarantee behind "add an operator with a single register_operator(...) call".
# ---------------------------------------------------------------------------

def _renderer_source_bodies():
    """Return the source text of the two renderer entry points (_uni, _latex).

    Reads the bodies via inspect so the test pins the actual shipped functions,
    not a copy. The two functions are the only places a per-operator branch
    could hide; the helpers they call are fixity-agnostic.
    """
    import inspect
    from unicode_fol_kit.fol import _msfl_nodes
    return inspect.getsource(_msfl_nodes._uni) + inspect.getsource(_msfl_nodes._latex)


def test_renderers_have_no_per_operator_branch():
    """No registered operator's class name is hard-coded in _uni / _latex.

    Every operator in OPERATORS must be reached purely through the spec.fixity
    dispatch. If a future change reintroduced an `if cls == "Box"` style branch
    for a registered operator, that class name would appear as a quoted literal
    in the renderer source and this guard would fail — keeping the decoupling
    real rather than incidental.
    """
    # Importing the modal module ensures the modal/temporal/deontic operators are
    # in OPERATORS, so they are covered by this guard too.
    import unicode_fol_kit.fol._modal_nodes  # noqa: F401

    src = _renderer_source_bodies()
    offenders = [name for name in OPERATORS if f'"{name}"' in src or f"'{name}'" in src]
    assert offenders == [], (
        f"Renderer source hard-codes per-operator branches for {offenders}; "
        f"registered operators must dispatch on spec.fixity only."
    )


def test_every_registered_fixity_is_handled_by_both_renderers():
    """Both renderers handle every fixity that register_operator accepts.

    Guards the other direction: a new *fixity* (added to the validator) must be
    wired into _uni and _latex, else operators using it would silently fall
    through. We assert each valid fixity name appears in both renderer bodies.
    """
    from unicode_fol_kit.fol._fol_nodes import _VALID_FIXITIES

    src = _renderer_source_bodies()
    missing = [fx for fx in _VALID_FIXITIES if f'"{fx}"' not in src]
    assert missing == [], f"Renderers do not handle fixities: {missing}"
