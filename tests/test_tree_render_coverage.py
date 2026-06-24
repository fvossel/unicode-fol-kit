"""Whole-tree tree_str() / to_dot() coverage for every 0.5.0 node type.

``tree_str`` (ASCII tree) and ``to_dot`` (Graphviz DOT) are both driven by each
node's ``_tree_parts()`` (label, children) view. A node type that forgets to
provide a sensible ``_tree_parts`` would render with a useless label or crash, so
this test instantiates EVERY node class — old and new — via representative
parsed/built formulas and asserts:

* ``tree_str()`` runs, is non-empty, and its first line is the root's label and
  its top-level branch count is the root's child count;
* ``to_dot()`` runs and is a well-formed single-rooted tree: it emits exactly one
  ``[label=...]`` per ``_tree_parts`` node and exactly ``nodes - 1`` edges;
* across all formulas, every targeted node class actually appears — so the
  coverage claim is enforced, not assumed.
"""

from unicode_fol_kit.fol.msflparser import MSFLParser
from unicode_fol_kit.fol.nodes import (
    Atom, Variable, Constant, Number, Function,
    Not, And, Or, Xor, Implies, Iff, Quantifier,
    LukNegation, WeakConjunction, WeakDisjunction,
    StrongConjunction, StrongDisjunction, LukImplication, LukEquivalence,
    Lambda, LambdaVar, Application,
    SortedQuantifier, SortedConstant,
    Box, Diamond, Always, Eventually, Next, Until,
    Knows, Believes, Obligatory, Permitted,
    SecondOrderQuantifier,
)

_FOL = MSFLParser()
_MS = MSFLParser(many_sorted=True)
_FL = MSFLParser(fuzzy=True)
_MODAL = MSFLParser(modal=True)
_SO = MSFLParser(second_order=True)

# Representative formulas whose union instantiates every node class. Each string
# stays inside its mode's no-mixing / associativity rules so it parses cleanly.
FORMULAS = {
    "classical": _FOL.parse("∀x ((P(ff(x)) → Q(x)) ↔ ¬R(7)) ⊕ S"),
    "and": _FOL.parse("P ∧ Q(alice)"),
    "or": _FOL.parse("P ∨ Q(c_1)"),
    "lambda": _FOL.parse("(λx. P(x))(alice)"),
    "sorted": _MS.parse("∀x:Human (P(x) → Q(alice:Human))"),
    "luk": _FL.parse("¬P → (P ⊗ Q) → (P ⊕ Q) → (P ∧ Q) → (P ∨ Q) → (P ↔ Q)"),
    "modal": _MODAL.parse(
        "□P ∧ ◇Q ∧ ⒼR ∧ ⒻS ∧ ⓃP ∧ ⓄQ ∧ ⓅR ∧ K_alice P ∧ B_bob Q ∧ (P Ⓤ Q)"
    ),
    "second_order": _SO.parse("∀Z ∃W (Z(alice) ∧ W(alice, bob))"),
}

# Every node class the coverage set must exercise (old + the 0.5.0 additions).
TARGET_CLASSES = {
    "Atom", "Variable", "Constant", "Number", "Function",
    "Not", "And", "Or", "Xor", "Implies", "Iff", "Quantifier",
    "LukNegation", "WeakConjunction", "WeakDisjunction",
    "StrongConjunction", "StrongDisjunction", "LukImplication", "LukEquivalence",
    "Lambda", "LambdaVar", "Application",
    "SortedQuantifier", "SortedConstant",
    "Box", "Diamond", "Always", "Eventually", "Next", "Until",
    "Knows", "Believes", "Obligatory", "Permitted",
    "SecondOrderQuantifier",
}


def _tree_nodes(node):
    """Yield every node reachable through the ``_tree_parts`` (render) view."""
    yield node
    _, children = node._tree_parts()
    for child in children:
        yield from _tree_nodes(child)


def test_tree_str_and_to_dot_run_for_every_node_type():
    """tree_str/to_dot are structurally consistent for each coverage formula."""
    for name, formula in FORMULAS.items():
        nodes = list(_tree_nodes(formula))
        node_count = len(nodes)

        # tree_str: non-empty; first line is the root label; top-level branch
        # count equals the root's child count.
        label, children = formula._tree_parts()
        tree = formula.tree_str()
        lines = tree.split("\n")
        assert lines[0] == label, f"{name}: tree_str root line {lines[0]!r} != {label!r}"
        top_branches = sum(1 for ln in lines if ln.startswith(("├── ", "└── ")))
        assert top_branches == len(children), f"{name}: top branch count"

        # to_dot: one labelled node per _tree_parts node; a tree has nodes-1 edges.
        dot = formula.to_dot()
        assert dot.startswith("digraph AST {") and dot.rstrip().endswith("}")
        assert dot.count("[label=") == node_count, f"{name}: dot node count"
        assert dot.count(" -> ") == node_count - 1, f"{name}: dot edge count"

        # Every node carries a non-empty label (no node renders blank).
        for node in nodes:
            node_label, _ = node._tree_parts()
            assert node_label != "", f"{name}: empty label on {type(node).__name__}"


def test_every_target_node_class_is_covered():
    """The coverage formulas together instantiate every targeted node class."""
    seen = set()
    for formula in FORMULAS.values():
        for node in _tree_nodes(formula):
            seen.add(type(node).__name__)
    missing = TARGET_CLASSES - seen
    assert not missing, f"node classes never rendered by the coverage set: {sorted(missing)}"
