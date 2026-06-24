"""Second-order quantifier AST node: ∀P / ∃P binding a predicate variable.

This node extends the classical FOL AST with second-order quantification over a
predicate variable. It is purely syntactic in this phase: there is no semantics
yet, and it rejects the first-order export back-ends (to_z3/to_prover9/to_tptp) —
second-order quantification is not first-order and is not SMT-expressible, so a
formula must first be evaluated by the finite-model evaluator (a later phase).

SecondOrderQuantifier is a frozen dataclass (hashable) subclassing Node. The
bound symbol is a PREDICATE name (uppercase, e.g. ``P``), not an object variable,
so binding a predicate name leaves the object-level free variables untouched:
free_variables walks _child_nodes() (only the ``formula`` child) and the scalar
``predicate``/``arity`` fields are invisible to it. Structural methods
(to_msfol, _relativize, traversal) are inherited unchanged because
Node.map_children / Node._child_nodes treat ``formula`` as the single Node child
and copy the scalar ``type``/``predicate``/``arity`` fields verbatim. The Unicode
and LaTeX renderers live in _msfl_nodes.py and dispatch by class name;
serialisation, the tree label, and export-rejection live here.

The bound predicate's ``arity`` is INFERRED from its applications in the body at
parse time (see msflparser.SecondOrderTransformer); it is recorded on the node
for the semantics phase but is NOT printed by the renderers, because it is
re-inferred on re-parse — keeping the parse → to_unicode_str → parse round-trip
stable.
"""

from dataclasses import dataclass

from ._fol_nodes import Node, Z3Env, NODE_CLASSES, Atom, register_parser_op
from .naming import ParsingError


# Shared message for the export back-ends: second-order quantification has no
# first-order / SMT encoding.
_NO_EXPORT = (
    "Second-order quantification is not first-order and is not SMT-expressible; "
    "it has no direct to_z3/to_prover9/to_tptp export. Evaluate the formula with "
    "the finite-model evaluator instead."
)


@dataclass(frozen=True)
class SecondOrderQuantifier(Node):
    """A second-order quantifier ∀P / ∃P binding a predicate variable.

    type is "∀" (universal) or "∃" (existential). predicate is the bound
    predicate-variable NAME (uppercase, as it appears applied in the body).
    arity is that predicate variable's arity, inferred from its applications in
    the body (0 for a never-applied / propositional predicate variable).
    formula is the body.

    Semantics: ∀P φ asserts φ holds for every interpretation of the
    arity-``arity`` predicate P over the domain; ∃P φ for some interpretation.
    Evaluation is a later (finite-model) phase.
    """

    type: str
    predicate: str
    arity: int
    formula: Node

    def _tree_parts(self):
        """Return the ``∀ P/2`` style label and the single subformula child."""
        return f"{self.type} {self.predicate}/{self.arity}", [self.formula]

    def to_dict(self):
        """Serialise to dict with type tag, quantifier type, bound predicate, arity, and body."""
        return {
            "_type": "SecondOrderQuantifier",
            "type": self.type,
            "predicate": self.predicate,
            "arity": self.arity,
            "formula": self.formula.to_dict(),
        }

    @staticmethod
    def from_dict(d):
        """Deserialise a SecondOrderQuantifier from a dict produced by to_dict."""
        return SecondOrderQuantifier(
            d["type"],
            d["predicate"],
            d["arity"],
            Node.from_dict(d["formula"]),
        )

    def to_z3(self, env: Z3Env = None):
        """Reject Z3 export: second-order quantification is not SMT-expressible."""
        raise NotImplementedError(_NO_EXPORT)

    def to_prover9(self) -> str:
        """Reject Prover9 export: second-order quantification is not first-order."""
        raise NotImplementedError(_NO_EXPORT)

    def to_tptp(self) -> str:
        """Reject TPTP export: second-order quantification is not first-order."""
        raise NotImplementedError(_NO_EXPORT)


# =========================
# Registry extension
# =========================

NODE_CLASSES.update({
    "SecondOrderQuantifier": SecondOrderQuantifier,
})


# =========================
# Arity inference + parser registration (second-order mode)
# =========================
#
# The bound predicate variable's arity is not in the surface syntax; it is
# inferred from the predicate's applications in the body at parse time. These two
# names (the inference helper and its error) live here, next to the node, and are
# re-exported by msflparser for backward compatibility.


class ConflictingArityError(ParsingError):
    """Raised when a second-order-bound predicate is applied at conflicting arities.

    Subclasses ParsingError so callers catching the parser's error type also
    catch this inference-level failure. It is constructed directly (not from a
    Lark exception), so it bypasses ParsingError.__init__ and sets its own
    message.
    """

    def __init__(self, predname: str, arities):
        arities_str = ", ".join(str(a) for a in arities)
        message = (
            f"SYNTAX_ERROR: Second-order predicate variable '{predname}' is "
            f"applied at conflicting arities ({arities_str}); a bound predicate "
            f"variable must be used at a single, consistent arity."
        )
        self.args = (message,)

    def __str__(self):
        return self.args[0]


def _infer_so_arity(body: Node, predname: str) -> int:
    """Infer the arity of a second-order-bound predicate from its uses in body.

    Scans ``body`` for ``Atom(predname, args)`` occurrences and returns the
    common application arity (``len(args)``). All applications of ``predname``
    must share the same arity, else a ConflictingArityError is raised. A predicate
    that is never applied has arity 0 (a propositional / Boolean predicate
    variable).

    Shadowing: an inner ``SecondOrderQuantifier`` that rebinds the SAME predicate
    name introduces a fresh binding, so its body is NOT scanned for the outer
    binder's arity — the descent stops at such a rebinder. (An inner binder over a
    DIFFERENT name is descended into normally.)
    """
    arities: set = set()

    def visit(node: Node) -> None:
        if isinstance(node, SecondOrderQuantifier) and node.predicate == predname:
            return  # inner binder shadows predname; do not descend into its scope
        if isinstance(node, Atom) and node.predicate == predname:
            arities.add(len(node.args))
        for child in node._child_nodes():
            visit(child)

    visit(body)

    if len(arities) > 1:
        raise ConflictingArityError(predname, sorted(arities))
    return arities.pop() if arities else 0


def _second_order_quantifier_transform(items):
    """Build a SecondOrderQuantifier from [FORALL/EXISTS, PREDICATE, body].

    Mirrors the legacy SecondOrderTransformer.second_order_quantifier_ exactly:
    the PREDICATE token has no terminal handler (raw Token), the body is already a
    built AST node (Lark transforms bottom-up), and the bound predicate's arity is
    inferred from its applications in the body.
    """
    quant = str(items[0])
    predname = str(items[1])
    body = items[2]
    arity = _infer_so_arity(body, predname)
    return SecondOrderQuantifier(quant, predname, arity, body)


# ∀P / ∃P over a PREDICATE variable, at the quantifier level. The classical
# first-order quantifier (∀x / ∃x -> quantifier_) is registered for the
# "second_order" mode in _fol_nodes.py; this adds the second alternative, matching
# so.lark's two-alternative quantifier rule.
register_parser_op(SecondOrderQuantifier, "second_order", "quantifier",
                   "second_order_quantifier_",
                   "(FORALL | EXISTS) PREDICATE prefix",
                   _second_order_quantifier_transform)
