"""MSFL node classes (sorted quantifiers/constants, Łukasiewicz operators) and to_fol reduction."""

import logging
from dataclasses import dataclass, is_dataclass

from ._fol_nodes import (
    Node, Z3Env, Variable, Constant, Number, Function,
    Atom, Not, And, Or, Xor, Implies, Iff, Quantifier,
    NODE_CLASSES, OPERATORS, register_operator,
    register_parser_op, _fold_binary,
)

_logger = logging.getLogger(__name__)


# =========================
# MSFL Nodes
# =========================

@dataclass(frozen=True)
class SortedQuantifier(Node):
    """A sort-restricted quantifier binding a variable to a named sort.

    type is "∀" (universal) or "∃" (existential).
    Semantics: ∀x:S φ asserts φ holds for all elements of sort S;
    ∃x:S φ asserts φ holds for some element of sort S.
    Reduction to plain FOL is a later step.
    """

    type: str
    variable: Variable
    sort: str
    formula: Node

    def _tree_parts(self):
        return f"{self.type} {self.variable.name}:{self.sort}", [self.formula]

    def to_dict(self):
        return {
            "_type": "SortedQuantifier",
            "type": self.type,
            "variable": self.variable.to_dict(),
            "sort": self.sort,
            "formula": self.formula.to_dict(),
        }

    @staticmethod
    def from_dict(d):
        return SortedQuantifier(
            d["type"],
            Node.from_dict(d["variable"]),
            d["sort"],
            Node.from_dict(d["formula"]),
        )

    def to_msfol(self) -> "Node":
        return SortedQuantifier(self.type, self.variable, self.sort, self.formula.to_msfol())

    def _relativize(self, facts: list) -> "Node":
        body = self.formula._relativize(facts)
        sort_atom = Atom(self.sort, [self.variable])
        if self.type == "∀":
            return Quantifier("∀", self.variable, Implies(sort_atom, body))
        elif self.type == "∃":
            return Quantifier("∃", self.variable, And(sort_atom, body))
        raise ValueError(f"Unknown quantifier type: {self.type}")

    def to_z3(self, env: Z3Env = None):
        _logger.info("Auto-reducing %s to FOL for Z3 export.", type(self).__name__)
        return to_fol(self).to_z3(env)

    def to_prover9(self) -> str:
        _logger.info("Auto-reducing %s to FOL for Prover9 export.", type(self).__name__)
        return to_fol(self).to_prover9()

    def to_tptp(self) -> str:
        _logger.info("Auto-reducing %s to FOL for TPTP export.", type(self).__name__)
        return to_fol(self).to_tptp()


@dataclass(frozen=True)
class SortedConstant(Node):
    """A constant symbol annotated with a sort name, e.g. alice:Human.

    Semantics: a ground term that belongs to the named sort.
    Reduction to plain FOL is a later step.
    """

    name: str
    sort: str

    def _tree_parts(self):
        return f"{self.name}:{self.sort}", []

    def to_dict(self):
        return {"_type": "SortedConstant", "name": self.name, "sort": self.sort}

    @staticmethod
    def from_dict(d):
        return SortedConstant(d["name"], d["sort"])

    def to_msfol(self) -> "Node":
        return SortedConstant(self.name, self.sort)

    def _relativize(self, facts: list) -> "Node":
        facts.append(Atom(self.sort, [Constant(self.name)]))
        return Constant(self.name)

    def to_z3(self, env: Z3Env = None):
        _logger.info("Auto-reducing %s to FOL for Z3 export.", type(self).__name__)
        return to_fol(self).to_z3(env)

    def to_prover9(self) -> str:
        _logger.info("Auto-reducing %s to FOL for Prover9 export.", type(self).__name__)
        return to_fol(self).to_prover9()

    def to_tptp(self) -> str:
        _logger.info("Auto-reducing %s to FOL for TPTP export.", type(self).__name__)
        return to_fol(self).to_tptp()


@dataclass(frozen=True)
class WeakConjunction(Node):
    """Łukasiewicz weak conjunction (fuzzy min): min{x, y}.

    Uses the same glyph ∧ as classical And; distinct by class identity.
    """

    left: Node
    right: Node

    def _tree_parts(self):
        return "∧", [self.left, self.right]

    def to_dict(self):
        return {"_type": "WeakConjunction", "left": self.left.to_dict(), "right": self.right.to_dict()}

    @staticmethod
    def from_dict(d):
        return WeakConjunction(Node.from_dict(d["left"]), Node.from_dict(d["right"]))

    def to_msfol(self) -> "Node":
        return And(self.left.to_msfol(), self.right.to_msfol())

    def _relativize(self, facts: list) -> "Node":
        raise RuntimeError("WeakConjunction._relativize called; call to_msfol() before _relativize.")

    def to_z3(self, env: Z3Env = None):
        _logger.info("Auto-reducing %s to FOL for Z3 export.", type(self).__name__)
        return to_fol(self).to_z3(env)

    def to_prover9(self) -> str:
        _logger.info("Auto-reducing %s to FOL for Prover9 export.", type(self).__name__)
        return to_fol(self).to_prover9()

    def to_tptp(self) -> str:
        _logger.info("Auto-reducing %s to FOL for TPTP export.", type(self).__name__)
        return to_fol(self).to_tptp()


@dataclass(frozen=True)
class WeakDisjunction(Node):
    """Łukasiewicz weak disjunction (fuzzy max): max{x, y}.

    Uses the same glyph ∨ as classical Or; distinct by class identity.
    """

    left: Node
    right: Node

    def _tree_parts(self):
        return "∨", [self.left, self.right]

    def to_dict(self):
        return {"_type": "WeakDisjunction", "left": self.left.to_dict(), "right": self.right.to_dict()}

    @staticmethod
    def from_dict(d):
        return WeakDisjunction(Node.from_dict(d["left"]), Node.from_dict(d["right"]))

    def to_msfol(self) -> "Node":
        return Or(self.left.to_msfol(), self.right.to_msfol())

    def _relativize(self, facts: list) -> "Node":
        raise RuntimeError("WeakDisjunction._relativize called; call to_msfol() before _relativize.")

    def to_z3(self, env: Z3Env = None):
        _logger.info("Auto-reducing %s to FOL for Z3 export.", type(self).__name__)
        return to_fol(self).to_z3(env)

    def to_prover9(self) -> str:
        _logger.info("Auto-reducing %s to FOL for Prover9 export.", type(self).__name__)
        return to_fol(self).to_prover9()

    def to_tptp(self) -> str:
        _logger.info("Auto-reducing %s to FOL for TPTP export.", type(self).__name__)
        return to_fol(self).to_tptp()


@dataclass(frozen=True)
class StrongConjunction(Node):
    """Łukasiewicz strong conjunction (t-norm): max{0, x+y−1}."""

    left: Node
    right: Node

    def _tree_parts(self):
        return "⊗", [self.left, self.right]

    def to_dict(self):
        return {"_type": "StrongConjunction", "left": self.left.to_dict(), "right": self.right.to_dict()}

    @staticmethod
    def from_dict(d):
        return StrongConjunction(Node.from_dict(d["left"]), Node.from_dict(d["right"]))

    def to_msfol(self) -> "Node":
        return And(self.left.to_msfol(), self.right.to_msfol())

    def _relativize(self, facts: list) -> "Node":
        raise RuntimeError("StrongConjunction._relativize called; call to_msfol() before _relativize.")

    def to_z3(self, env: Z3Env = None):
        _logger.info("Auto-reducing %s to FOL for Z3 export.", type(self).__name__)
        return to_fol(self).to_z3(env)

    def to_prover9(self) -> str:
        _logger.info("Auto-reducing %s to FOL for Prover9 export.", type(self).__name__)
        return to_fol(self).to_prover9()

    def to_tptp(self) -> str:
        _logger.info("Auto-reducing %s to FOL for TPTP export.", type(self).__name__)
        return to_fol(self).to_tptp()


@dataclass(frozen=True)
class StrongDisjunction(Node):
    """Łukasiewicz strong disjunction (t-conorm): min{1, x+y}."""

    left: Node
    right: Node

    def _tree_parts(self):
        return "⊕", [self.left, self.right]

    def to_dict(self):
        return {"_type": "StrongDisjunction", "left": self.left.to_dict(), "right": self.right.to_dict()}

    @staticmethod
    def from_dict(d):
        return StrongDisjunction(Node.from_dict(d["left"]), Node.from_dict(d["right"]))

    def to_msfol(self) -> "Node":
        return Or(self.left.to_msfol(), self.right.to_msfol())

    def _relativize(self, facts: list) -> "Node":
        raise RuntimeError("StrongDisjunction._relativize called; call to_msfol() before _relativize.")

    def to_z3(self, env: Z3Env = None):
        _logger.info("Auto-reducing %s to FOL for Z3 export.", type(self).__name__)
        return to_fol(self).to_z3(env)

    def to_prover9(self) -> str:
        _logger.info("Auto-reducing %s to FOL for Prover9 export.", type(self).__name__)
        return to_fol(self).to_prover9()

    def to_tptp(self) -> str:
        _logger.info("Auto-reducing %s to FOL for TPTP export.", type(self).__name__)
        return to_fol(self).to_tptp()


@dataclass(frozen=True)
class LukNegation(Node):
    """Łukasiewicz negation: 1−x.

    Uses the same glyph ¬ as classical Not; distinct by class identity.
    """

    formula: Node

    def _tree_parts(self):
        return "¬", [self.formula]

    def to_dict(self):
        return {"_type": "LukNegation", "formula": self.formula.to_dict()}

    @staticmethod
    def from_dict(d):
        return LukNegation(Node.from_dict(d["formula"]))

    def to_msfol(self) -> "Node":
        return Not(self.formula.to_msfol())

    def _relativize(self, facts: list) -> "Node":
        raise RuntimeError("LukNegation._relativize called; call to_msfol() before _relativize.")

    def to_z3(self, env: Z3Env = None):
        _logger.info("Auto-reducing %s to FOL for Z3 export.", type(self).__name__)
        return to_fol(self).to_z3(env)

    def to_prover9(self) -> str:
        _logger.info("Auto-reducing %s to FOL for Prover9 export.", type(self).__name__)
        return to_fol(self).to_prover9()

    def to_tptp(self) -> str:
        _logger.info("Auto-reducing %s to FOL for TPTP export.", type(self).__name__)
        return to_fol(self).to_tptp()


@dataclass(frozen=True)
class LukImplication(Node):
    """Łukasiewicz implication: min{1, 1−x+y}.

    Uses the same glyph → as classical Implies; distinct by class identity.
    """

    left: Node
    right: Node

    def _tree_parts(self):
        return "→", [self.left, self.right]

    def to_dict(self):
        return {"_type": "LukImplication", "left": self.left.to_dict(), "right": self.right.to_dict()}

    @staticmethod
    def from_dict(d):
        return LukImplication(Node.from_dict(d["left"]), Node.from_dict(d["right"]))

    def to_msfol(self) -> "Node":
        return Implies(self.left.to_msfol(), self.right.to_msfol())

    def _relativize(self, facts: list) -> "Node":
        raise RuntimeError("LukImplication._relativize called; call to_msfol() before _relativize.")

    def to_z3(self, env: Z3Env = None):
        _logger.info("Auto-reducing %s to FOL for Z3 export.", type(self).__name__)
        return to_fol(self).to_z3(env)

    def to_prover9(self) -> str:
        _logger.info("Auto-reducing %s to FOL for Prover9 export.", type(self).__name__)
        return to_fol(self).to_prover9()

    def to_tptp(self) -> str:
        _logger.info("Auto-reducing %s to FOL for TPTP export.", type(self).__name__)
        return to_fol(self).to_tptp()


@dataclass(frozen=True)
class LukEquivalence(Node):
    """Łukasiewicz equivalence: 1−|x−y|.

    Uses the same glyph ↔ as classical Iff; distinct by class identity.
    """

    left: Node
    right: Node

    def _tree_parts(self):
        return "↔", [self.left, self.right]

    def to_dict(self):
        return {"_type": "LukEquivalence", "left": self.left.to_dict(), "right": self.right.to_dict()}

    @staticmethod
    def from_dict(d):
        return LukEquivalence(Node.from_dict(d["left"]), Node.from_dict(d["right"]))

    def to_msfol(self) -> "Node":
        return Iff(self.left.to_msfol(), self.right.to_msfol())

    def _relativize(self, facts: list) -> "Node":
        raise RuntimeError("LukEquivalence._relativize called; call to_msfol() before _relativize.")

    def to_z3(self, env: Z3Env = None):
        _logger.info("Auto-reducing %s to FOL for Z3 export.", type(self).__name__)
        return to_fol(self).to_z3(env)

    def to_prover9(self) -> str:
        _logger.info("Auto-reducing %s to FOL for Prover9 export.", type(self).__name__)
        return to_fol(self).to_prover9()

    def to_tptp(self) -> str:
        _logger.info("Auto-reducing %s to FOL for TPTP export.", type(self).__name__)
        return to_fol(self).to_tptp()


# =========================
# Operator registration
# =========================
#
# Self-register the Łukasiewicz operators with the central renderers. Each uses
# the same glyph/markup as its classical counterpart but is distinct by class
# identity (e.g. LukNegation renders ¬ like Not but lowers differently).

register_operator(LukNegation, "prefix", "¬", "\\lnot ", 4)
register_operator(WeakConjunction, "level2", "∧", "\\land", 3)
register_operator(WeakDisjunction, "level2", "∨", "\\lor", 3)
register_operator(StrongConjunction, "level2", "⊗", "\\otimes", 3)
register_operator(StrongDisjunction, "level2", "⊕", "\\oplus", 3)
register_operator(LukImplication, "binary_implies", "→", "\\rightarrow", 2)
register_operator(LukEquivalence, "binary_iff", "↔", "\\leftrightarrow", 1)


# =========================
# Parser registration (MSFL / FL Łukasiewicz + sorted quantifier/constant)
# =========================
#
# The Łukasiewicz connectives appear in both MSFL (sorted) and FL (unsorted)
# modes with identical grammar fragments; they register once per mode. The
# transforms mirror LukConnectivesMixin exactly. The sorted quantifier registers
# for MSFOL and MSFL (both sorted), the unsorted Łukasiewicz quantifier for FL,
# and sorted-constant handling rides on the SORTED term-layer flag (selected by
# build_grammar for msfol/msfl) plus the sorted_const_ transform here.


def _sorted_quantifier_transform(items):
    """Build a SortedQuantifier from [FORALL/EXISTS, Variable, SORT, body]."""
    quant_tok, var, sort_tok, formula = items
    sort = str(sort_tok)[1:]  # strip leading ':'
    return SortedQuantifier(str(quant_tok), var, sort, formula)


def _sorted_const_transform(items):
    """Build a SortedConstant from [NAME/CONSTANT, SORT]; NAME pre-converts to Constant."""
    first, sort_tok = items
    name = first.name if isinstance(first, Constant) else str(first)
    sort = str(sort_tok)[1:]  # strip leading ':'
    return SortedConstant(name, sort)


def _luk_quantifier_transform(items):
    """Build an unsorted Quantifier (FL mode) from [FORALL/EXISTS, Variable, body]."""
    return Quantifier(str(items[0]), items[1], items[2])


# --- prefix: ¬ (LukNegation) in MSFL and FL ---
for _m in ("msfl", "fl"):
    register_parser_op(LukNegation, _m, "prefix", "luk_not_", '"¬" prefix',
                       lambda items: LukNegation(items[0]))

# --- level2: ∧ ∨ ⊗ ⊕ (weak/strong) in MSFL and FL ---
for _m in ("msfl", "fl"):
    register_parser_op(WeakConjunction, _m, "level2", "weak_and_", '"∧"',
                       lambda items: _fold_binary(items, WeakConjunction),
                       only_name="only_weak_and")
    register_parser_op(WeakDisjunction, _m, "level2", "weak_or_", '"∨"',
                       lambda items: _fold_binary(items, WeakDisjunction),
                       only_name="only_weak_or")
    register_parser_op(StrongConjunction, _m, "level2", "strong_and_", '"⊗"',
                       lambda items: _fold_binary(items, StrongConjunction),
                       only_name="only_strong_and")
    register_parser_op(StrongDisjunction, _m, "level2", "strong_or_", '"⊕"',
                       lambda items: _fold_binary(items, StrongDisjunction),
                       only_name="only_strong_or")

# --- implication: → (LukImplication) in MSFL and FL ---
# Binary levels store just the glyph; build_grammar assembles the right-assoc rule.
for _m in ("msfl", "fl"):
    register_parser_op(LukImplication, _m, "implication", "luk_implies_", '"→"',
                       lambda items: LukImplication(items[0], items[1]))

# --- biimplication: ↔ (LukEquivalence) in MSFL and FL ---
for _m in ("msfl", "fl"):
    register_parser_op(LukEquivalence, _m, "biimplication", "luk_iff_", '"↔"',
                       lambda items: LukEquivalence(items[0], items[1]))

# --- quantifier: sorted ∀x:S / ∃x:S (MSFOL, MSFL); unsorted (FL) ---
register_parser_op(SortedQuantifier, "msfol", "quantifier", "sorted_quantifier_",
                   "(FORALL | EXISTS) VARIABLE SORT prefix", _sorted_quantifier_transform)
register_parser_op(SortedQuantifier, "msfl", "quantifier", "sorted_quantifier_",
                   "(FORALL | EXISTS) VARIABLE SORT prefix", _sorted_quantifier_transform)
register_parser_op(Quantifier, "fl", "quantifier", "quantifier_",
                   "(FORALL | EXISTS) VARIABLE prefix", _luk_quantifier_transform)

# --- sorted constant transform (term layer, MSFOL + MSFL via the SORTED flag) ---
# build_grammar emits the NAME SORT / CONSTANT SORT -> sorted_const_ rules for
# sorted modes; the transform is registered as a non-grammar-contributing handler
# so it is attached to the assembled Transformer for those modes.
for _m in ("msfol", "msfl"):
    register_parser_op(SortedConstant, _m, "quantifier", "sorted_const_",
                       "", _sorted_const_transform)


# =========================
# Lambda-Calculus Nodes
# =========================

@dataclass(frozen=True)
class LambdaVar(Node):
    """A lambda-bound variable, distinct from logical Variable.

    Kept separate so lambda binding and logical binding never get confused.
    """

    name: str

    def _tree_parts(self):
        return f"LambdaVar: {self.name}", []

    def to_dict(self):
        return {"_type": "LambdaVar", "name": self.name}

    @staticmethod
    def from_dict(d):
        return LambdaVar(d["name"])

    def to_msfol(self) -> "Node":
        raise NotImplementedError("Beta-reduce lambda terms before the MSFL export pipeline.")

    def _relativize(self, facts: list) -> "Node":
        raise NotImplementedError("Beta-reduce lambda terms before the MSFL export pipeline.")

    def to_z3(self, env: Z3Env = None):
        raise NotImplementedError("Lambda terms must be beta-reduced and lambda-eliminated before export.")

    def to_prover9(self) -> str:
        raise NotImplementedError("Lambda terms must be beta-reduced and lambda-eliminated before export.")

    def to_tptp(self) -> str:
        raise NotImplementedError("Lambda terms must be beta-reduced and lambda-eliminated before export.")


@dataclass(frozen=True)
class Lambda(Node):
    """A lambda abstraction λparam. body.

    param is a LambdaVar object, mirroring how Quantifier holds a Variable object.
    """

    param: LambdaVar
    body: Node

    def _tree_parts(self):
        return f"λ {self.param.name}", [self.body]

    def to_dict(self):
        return {"_type": "Lambda", "param": self.param.to_dict(), "body": self.body.to_dict()}

    @staticmethod
    def from_dict(d):
        return Lambda(LambdaVar.from_dict(d["param"]), Node.from_dict(d["body"]))

    def to_msfol(self) -> "Node":
        raise NotImplementedError("Beta-reduce lambda terms before the MSFL export pipeline.")

    def _relativize(self, facts: list) -> "Node":
        raise NotImplementedError("Beta-reduce lambda terms before the MSFL export pipeline.")

    def to_z3(self, env: Z3Env = None):
        raise NotImplementedError("Lambda terms must be beta-reduced and lambda-eliminated before export.")

    def to_prover9(self) -> str:
        raise NotImplementedError("Lambda terms must be beta-reduced and lambda-eliminated before export.")

    def to_tptp(self) -> str:
        raise NotImplementedError("Lambda terms must be beta-reduced and lambda-eliminated before export.")


@dataclass(frozen=True)
class Application(Node):
    """A lambda application func(arg)."""

    func: Node
    arg: Node

    def _tree_parts(self):
        return "App", [self.func, self.arg]

    def to_dict(self):
        return {"_type": "Application", "func": self.func.to_dict(), "arg": self.arg.to_dict()}

    @staticmethod
    def from_dict(d):
        return Application(Node.from_dict(d["func"]), Node.from_dict(d["arg"]))

    def to_msfol(self) -> "Node":
        raise NotImplementedError("Beta-reduce lambda terms before the MSFL export pipeline.")

    def _relativize(self, facts: list) -> "Node":
        raise NotImplementedError("Beta-reduce lambda terms before the MSFL export pipeline.")

    def to_z3(self, env: Z3Env = None):
        raise NotImplementedError("Lambda terms must be beta-reduced and lambda-eliminated before export.")

    def to_prover9(self) -> str:
        raise NotImplementedError("Lambda terms must be beta-reduced and lambda-eliminated before export.")

    def to_tptp(self) -> str:
        raise NotImplementedError("Lambda terms must be beta-reduced and lambda-eliminated before export.")


# =========================
# Free-variable computation
# =========================

def free_variables(node: Node) -> set:
    """Return the set of free Variable and LambdaVar occurrences in node.

    The returned set is mixed: it may contain Variable objects (bound by
    Quantifier / SortedQuantifier) and LambdaVar objects (bound by Lambda).
    The two kinds are kept distinct so that a lambda binder over LambdaVar("x")
    never accidentally removes a logical Variable("x") from the free set.
    """
    if isinstance(node, (Variable, LambdaVar)):
        return {node}
    if isinstance(node, (Constant, Number, SortedConstant)):
        return set()
    if isinstance(node, Lambda):
        return free_variables(node.body) - {node.param}
    if isinstance(node, (Quantifier, SortedQuantifier)):
        return free_variables(node.formula) - {node.variable}
    if not is_dataclass(node):
        raise TypeError(f"free_variables: unknown node type {type(node).__name__}")
    # Structural: for any non-binder, non-leaf node the free variables are the
    # union of its children's. Covers Atom, Function, Application, Not, and every
    # binary connective uniformly — and any future structural node type.
    result: set = set()
    for child in node._child_nodes():
        result |= free_variables(child)
    return result


# =========================
# Capture-avoiding beta-reduction
# =========================

BETA_REDUCTION_LIMIT = 10_000


class ReductionLimitError(Exception):
    """Raised when a lambda reduction exceeds its limit.

    ``beta_reduce`` raises it after ``BETA_REDUCTION_LIMIT`` (10 000) steps, and
    ``beta_eta_normalize`` after ``BETA_ETA_ROUND_LIMIT`` (100) alternation
    rounds — both signalling a term that is (likely) not strongly normalizing.
    """
    pass


def _names_in(node: Node) -> set:
    """Return all Variable and LambdaVar nodes appearing in node (free and bound)."""
    if isinstance(node, (Variable, LambdaVar)):
        return {node}
    if isinstance(node, (Constant, Number, SortedConstant)):
        return set()
    # Structural union over children. A binder's bound variable is itself a Node
    # child (Lambda.param, Quantifier.variable), so it is included here — exactly
    # what "names in, free and bound" requires.
    result: set = set()
    for child in node._child_nodes():
        result |= _names_in(child)
    return result


def _fresh_name(base: str, avoid: set) -> str:
    """Return the first name of the form base_N (N = 0, 1, …) not in {n.name for n in avoid}."""
    avoid_names = {n.name for n in avoid}
    i = 0
    while True:
        candidate = f"{base}_{i}"
        if candidate not in avoid_names:
            return candidate
        i += 1


def _rename(term: Node, old_var, new_var) -> Node:
    """Replace all free occurrences of old_var with new_var, stopping at shadowing binders.

    Caller guarantees new_var.name does not appear anywhere in term,
    so no capture check is needed here.
    """
    if term == old_var:
        return new_var
    if isinstance(term, (Variable, LambdaVar, Constant, Number, SortedConstant)):
        return term  # leaf that does not match old_var
    if isinstance(term, Lambda):
        if term.param == old_var:
            return term  # shadowed
        return Lambda(term.param, _rename(term.body, old_var, new_var))
    if isinstance(term, Quantifier):
        if term.variable == old_var:
            return term  # shadowed
        return Quantifier(term.type, term.variable, _rename(term.formula, old_var, new_var))
    if isinstance(term, SortedQuantifier):
        if term.variable == old_var:
            return term  # shadowed
        return SortedQuantifier(term.type, term.variable, term.sort,
                                _rename(term.formula, old_var, new_var))
    # Structural: Atom, Function, Application, Not, and the binary connectives —
    # none are binders, so recurse uniformly into every child.
    return term.map_children(lambda c: _rename(c, old_var, new_var))


def _subst(term: Node, target: LambdaVar, replacement: Node, fv_repl: set) -> Node:
    """Capture-avoiding substitution of target with replacement in term.

    fv_repl = free_variables(replacement), precomputed by the caller.
    target is a LambdaVar (beta-reduction) or a Variable (grounding a quantified
    object variable); replacement may be any Node. Substitution stops at a binder that
    rebinds the target (Lambda/Quantifier/SortedQuantifier) and alpha-renames any binder
    that would otherwise capture a free variable of replacement.
    """
    if term == target:
        return replacement
    if isinstance(term, (Variable, LambdaVar, Constant, Number, SortedConstant)):
        return term
    if isinstance(term, Lambda):
        if term.param == target:
            return term  # target rebound here — substitution stops
        if term.param in fv_repl:
            # Lambda binder would capture a free LambdaVar from replacement; alpha-convert.
            avoid = fv_repl | _names_in(term.body)
            fresh = LambdaVar(_fresh_name(term.param.name, avoid))
            new_body = _rename(term.body, term.param, fresh)
            return Lambda(fresh, _subst(new_body, target, replacement, fv_repl))
        return Lambda(term.param, _subst(term.body, target, replacement, fv_repl))
    if isinstance(term, Quantifier):
        # If the quantifier rebinds the target, the body is shadowed and substitution
        # stops here. This matters when target is a Variable (e.g. satisfies_modal
        # grounding an object quantifier); for a LambdaVar target the equality is always
        # False (distinct classes), so this is a no-op on the beta-reduction path.
        if term.variable == target:
            return term
        # Otherwise the quantifier variable may capture a free Variable from replacement.
        if term.variable in fv_repl:
            avoid = fv_repl | _names_in(term.formula)
            fresh = Variable(_fresh_name(term.variable.name, avoid))
            new_formula = _rename(term.formula, term.variable, fresh)
            return Quantifier(term.type, fresh,
                              _subst(new_formula, target, replacement, fv_repl))
        return Quantifier(term.type, term.variable,
                          _subst(term.formula, target, replacement, fv_repl))
    if isinstance(term, SortedQuantifier):
        if term.variable == target:
            return term  # target rebound here — substitution stops
        if term.variable in fv_repl:
            avoid = fv_repl | _names_in(term.formula)
            fresh = Variable(_fresh_name(term.variable.name, avoid))
            new_formula = _rename(term.formula, term.variable, fresh)
            return SortedQuantifier(term.type, fresh, term.sort,
                                    _subst(new_formula, target, replacement, fv_repl))
        return SortedQuantifier(term.type, term.variable, term.sort,
                                _subst(term.formula, target, replacement, fv_repl))
    # Structural: Atom, Function, Application, Not, and the binary connectives.
    # The binders above handle capture avoidance; these are not binders, so just
    # substitute into every child.
    return term.map_children(lambda c: _subst(c, target, replacement, fv_repl))


def substitute(term: Node, target, replacement: Node) -> Node:
    """Substitute target with replacement in term, with full capture avoidance.

    ``target`` is a LambdaVar (beta-reduction) or a Variable (grounding a quantified
    object variable into a Constant). Returns a new Node; the input is never mutated.
    """
    return _subst(term, target, replacement, free_variables(replacement))


def _beta_reduce(node: Node, steps: list) -> Node:
    # The Application case is iterative so that divergent terms (e.g. Omega) hit the step
    # counter before Python's recursion limit.  All other cases recurse normally.
    while True:
        if isinstance(node, Application):
            func = _beta_reduce(node.func, steps)
            if isinstance(func, Lambda):
                steps[0] += 1
                if steps[0] > BETA_REDUCTION_LIMIT:
                    raise ReductionLimitError(
                        f"beta-reduction exceeded {BETA_REDUCTION_LIMIT} steps; "
                        "term may not be strongly normalizing."
                    )
                node = substitute(func.body, func.param, node.arg)
                continue  # reduce the substituted result in the same frame
            return Application(func, _beta_reduce(node.arg, steps))
        if isinstance(node, (Variable, LambdaVar, Constant, Number, SortedConstant)):
            return node  # leaves
        # Structural (Lambda, Quantifier, SortedQuantifier, Atom, Function, Not,
        # and the binary connectives): reduce inside every child. Bound-variable
        # fields are leaves, so they pass through unchanged.
        return node.map_children(lambda c: _beta_reduce(c, steps))


def beta_reduce(node: Node) -> Node:
    """Reduce node to beta-normal form using normal-order strategy.

    Raises ReductionLimitError if more than BETA_REDUCTION_LIMIT steps are taken.
    Returns a new Node; the input is never mutated.
    """
    steps = [0]
    return _beta_reduce(node, steps)


# =========================
# Eta-reduction
# =========================

def _eta_reduce(node: Node) -> Node:
    """Single bottom-up pass contracting all eta-redexes.

    At each Lambda node, after recursing the body, checks three conditions:
    1. body is an Application,
    2. body.arg is the bound parameter (same LambdaVar),
    3. the parameter is NOT free in body.func.
    When all hold, contracts λp. f(p) → f.  One pass suffices because
    contraction returns body.func, which was already recursed.
    """
    if isinstance(node, (Variable, LambdaVar, Constant, Number, SortedConstant)):
        return node
    if isinstance(node, Lambda):
        reduced_body = _eta_reduce(node.body)
        if (isinstance(reduced_body, Application)
                and reduced_body.arg == node.param
                and node.param not in free_variables(reduced_body.func)):
            return reduced_body.func  # eta-contract: λp. f(p) → f
        return Lambda(node.param, reduced_body)
    # Structural (Application, Quantifier, SortedQuantifier, Atom, Function, Not,
    # and the binary connectives): recurse into every child. A Quantifier is
    # never an eta-redex; it is only recursed into.
    return node.map_children(_eta_reduce)


def eta_reduce(node: Node) -> Node:
    """Reduce node to eta-normal form (λx. f(x) → f when x ∉ fv(f)).

    Contracts all eta-redexes bottom-up in a single structural pass.
    Quantifiers are NOT treated as eta-redexes; they are only recursed into.
    Returns a new Node; the input is never mutated.
    """
    return _eta_reduce(node)


BETA_ETA_ROUND_LIMIT = 100


def beta_eta_normalize(node: Node) -> Node:
    """Reduce node to beta-eta normal form by alternating beta_reduce and eta_reduce.

    The alternation loop is a genuine necessity: eta-reduction can expose fresh
    beta-redexes (e.g. eta-contracting a func position turns an Application into
    a beta-redex), so the combined loop must iterate to a fixpoint rather than
    running each pass exactly once.

    Raises ReductionLimitError if beta_reduce internally exceeds
    BETA_REDUCTION_LIMIT steps, or if the alternation loop itself exceeds
    BETA_ETA_ROUND_LIMIT rounds (which only fires on pathological terms that
    are not strongly normalizing under beta-eta).
    Returns a new Node; the input is never mutated.
    """
    for _ in range(BETA_ETA_ROUND_LIMIT):
        after_beta = beta_reduce(node)   # may raise ReductionLimitError
        after_eta = eta_reduce(after_beta)
        if after_eta == node:
            return after_eta
        node = after_eta
    raise ReductionLimitError(
        f"beta-eta normalization exceeded {BETA_ETA_ROUND_LIMIT} rounds; "
        "term may not be strongly normalizing."
    )


# =========================
# Lambda scope resolution
# =========================

def _resolve(node: Node, bound: frozenset) -> Node:
    """Top-down resolver threading the frozenset of currently lambda-bound names."""
    if isinstance(node, Variable):
        return LambdaVar(node.name) if node.name in bound else node
    if isinstance(node, (LambdaVar, Constant, Number, SortedConstant)):
        return node
    if isinstance(node, Lambda):
        return Lambda(node.param, _resolve(node.body, bound | {node.param.name}))
    if isinstance(node, Quantifier):
        # quantifier shadows any outer lambda of the same name — remove from bound set
        return Quantifier(node.type, node.variable,
                          _resolve(node.formula, bound - {node.variable.name}))
    if isinstance(node, SortedQuantifier):
        return SortedQuantifier(node.type, node.variable, node.sort,
                                _resolve(node.formula, bound - {node.variable.name}))
    if isinstance(node, Atom):
        resolved_args = [_resolve(a, bound) for a in node.args]
        if node.predicate in bound:
            result: Node = LambdaVar(node.predicate)
            for arg in resolved_args:
                result = Application(result, arg)
            return result  # zero-arg → bare LambdaVar; n-arg → left-nested Application
        return Atom(node.predicate, resolved_args)
    if isinstance(node, Function):
        # Function names can be lambda-bound (e.g. λfoo. P(foo(x)) parses body as
        # Atom("P", [Function("foo", ...)]) because NAME "(" termlist ")" → function_).
        resolved_args = [_resolve(a, bound) for a in node.args]
        if node.name in bound:
            result = LambdaVar(node.name)
            for arg in resolved_args:
                result = Application(result, arg)
            return result
        return Function(node.name, resolved_args)
    if not is_dataclass(node):
        raise TypeError(f"resolve_lambda_scope: unknown node type {type(node).__name__}")
    # Structural: Not, the binary connectives, and Application introduce no
    # binders — recurse into every child with the same bound set.
    return node.map_children(lambda c: _resolve(c, bound))


def resolve_lambda_scope(node: Node) -> Node:
    """Rewrite body occurrences of lambda-bound names using lexical scope.

    After parsing, lambda parameters are LambdaVar but body occurrences keep
    their default parse types (Variable for single-letter params, Atom for
    predicate-class params). This pass performs two rewrites driven by the
    current lambda-bound set:

    1. Variable(name) whose name is lambda-bound → LambdaVar(name).
    2. Atom(pred, args) or Function(name, args) whose pred/name is lambda-bound
       → left-nested curried Application over LambdaVar(pred/name) and the
       recursively resolved args. Zero args → bare LambdaVar.

    Scope rules — innermost binder wins:
    - Lambda(p, body): p.name is ADDED to the bound set for body.
    - Quantifier / SortedQuantifier(_, v, _, body): v.name is REMOVED from the
      bound set for body. The quantifier shadows any outer lambda of the same
      name; inside the quantifier, the name is logical (Variable), not lambda-bound.

    Returns a new Node; the input is never mutated.
    """
    return _resolve(node, frozenset())


# =========================
# Unicode rendering (parser round-trip)
# =========================
#
# These functions render any node back to a Unicode formula string that, when
# re-parsed in the matching MSFLParser mode, yields a structurally equal AST.
# Dispatch is by class name so this single block covers both the FOL nodes
# (from _fol_nodes.py) and the MSFL/lambda nodes defined above.
#
# The regular formula operators (every connective/modal that the precedence-driven
# renderers below format) self-register an OperatorSpec in OPERATORS next to their
# class definition. The renderers read OPERATORS at call time, so adding an
# operator needs NO edit here. The fixed entries below are the NON-operator
# nodes the renderers still special-case explicitly — Lambda/Application and the
# three quantifier binders — together with their formula precedences.
#
# Formula precedence — higher binds tighter — mirrors the grammar layering
# (biimplication < implication < same-level binary < prefix < atomic). Operators
# carry their precedence in their spec; these are the base (non-operator) entries:
_UNI_BASE_PREC = {
    "Lambda": 0, "Application": 0,
    "Quantifier": 4, "SortedQuantifier": 4, "SecondOrderQuantifier": 4,
}

# The same-level binary group (∧ ∨ ⊗ ⊕, grammar precedence 3) is identified by
# its registered fixity == 'level2' — see the dispatch in _uni()/_latex(), which
# reads it straight off the operator's spec. Membership is therefore derived from
# the registry: a new same-level operator needs no edit here. Such operators
# cannot be mixed without parentheses, and chains are left-folded.

_UNI_INFIX_COMPARE = frozenset({"=", "≠", "<", ">", "≤", "≥"})
_UNI_ARITH_OPS = frozenset({"+", "-", "*", "/"})


def _uni_prec(node) -> float:
    """Formula precedence of a node; atomic nodes (atoms, terms) default to 5.

    Regular operators read their precedence from the registry; the binders,
    Lambda and Application fall back to the fixed base table; anything else
    (atoms, terms) is atomic at 5.
    """
    cls = type(node).__name__
    spec = OPERATORS.get(cls)
    if spec is not None:
        return spec.precedence
    return _UNI_BASE_PREC.get(cls, 5)


def _uni_wrap(node, min_prec: int) -> str:
    """Render node, parenthesising it when it binds looser than the slot allows."""
    s = _uni(node)
    return f"({s})" if _uni_prec(node) < min_prec else s


def _uni_level2_child(node, parent_cls: str, side: str) -> str:
    """Render a same-level (∧ ∨ ⊗ ⊕) operand with no-mixing / left-assoc parens.

    Left operand: a same-class chain stays flat (a ∧ b ∧ c); a different
    same-level operator is parenthesised (no silent mixing). Right operand:
    any same-level node is parenthesised, since the parser left-folds chains.
    """
    s = _uni(node)
    p = _uni_prec(node)
    if side == "left":
        need = p < 3 or (p == 3 and type(node).__name__ != parent_cls)
    else:
        need = p < 4
    return f"({s})" if need else s


def _uni_atom(node) -> str:
    """Render an Atom: infix comparison, nullary predicate, or applied predicate."""
    if node.predicate in _UNI_INFIX_COMPARE and len(node.args) == 2:
        return f"{_uni_term(node.args[0])} {node.predicate} {_uni_term(node.args[1])}"
    if not node.args:
        return node.predicate
    return f"{node.predicate}(" + ", ".join(_uni_term(a) for a in node.args) + ")"


def _uni_term_prec(node) -> int:
    """Arithmetic term precedence: + - → 1, * / → 2, everything atomic → 3."""
    if (type(node).__name__ == "Function"
            and node.name in _UNI_ARITH_OPS and len(node.args) == 2):
        return 2 if node.name in ("*", "/") else 1
    return 3


def _uni_term_wrap(node, parent_prec: int, is_right: bool) -> str:
    """Render an arithmetic operand, parenthesising per left-associative precedence."""
    s = _uni_term(node)
    p = _uni_term_prec(node)
    need = p < parent_prec or (p == parent_prec and is_right)
    return f"({s})" if need else s


def _uni_spine(node):
    """Uncurry a left-nested Application into (head, [arg0, arg1, …])."""
    args = []
    n = node
    while isinstance(n, Application):
        args.append(n.arg)
        n = n.func
    args.reverse()
    return n, args


def _uni_term(node) -> str:
    """Render a node occurring in term (argument) position.

    Higher-order applications produced by scope resolution (e.g. foo(x) under
    λfoo, parsed as a Function then rewritten to Application(LambdaVar, …)) are
    rendered back as function-call syntax so they re-parse and re-resolve to the
    same node.
    """
    cls = type(node).__name__
    if cls in ("Variable", "LambdaVar", "Constant"):
        return node.name
    if cls == "Number":
        return str(node.value)
    if cls == "SortedConstant":
        return f"{node.name}:{node.sort}"
    if cls == "Function":
        if node.name in _UNI_ARITH_OPS and len(node.args) == 2:
            p = _uni_term_prec(node)
            left = _uni_term_wrap(node.args[0], p, is_right=False)
            right = _uni_term_wrap(node.args[1], p, is_right=True)
            return f"{left} {node.name} {right}"
        return f"{node.name}(" + ", ".join(_uni_term(a) for a in node.args) + ")"
    if cls == "Application":
        head, args = _uni_spine(node)
        if isinstance(head, (LambdaVar, Variable, Constant)) and args:
            return f"{head.name}(" + ", ".join(_uni_term(a) for a in args) + ")"
        return f"({_uni(node.func)})({_uni(node.arg)})"
    # Atoms / other formula nodes are not valid terms; best-effort fall-through.
    return _uni(node)


def _uni(node) -> str:
    """Render node as a formula-level Unicode string (no surrounding parens)."""
    cls = type(node).__name__

    if cls in ("Variable", "LambdaVar", "Constant", "Number", "SortedConstant", "Function"):
        return _uni_term(node)
    if cls == "Atom":
        return _uni_atom(node)

    # Regular operators are driven entirely by the registry: the spec's fixity
    # selects the operand arrangement and spec.unicode supplies the glyph/prefix.
    spec = OPERATORS.get(cls)
    if spec is not None:
        fix = spec.fixity
        if fix == "prefix":
            # Prefix (¬ and the prefix modal/temporal ops) bind like ¬: operand
            # wrapped at the prefix level.
            return spec.unicode + _uni_wrap(node.formula, 4)
        if fix == "agent_prefix":
            # K_<agent> / B_<agent>: glyph, agent's name, space, then wrapped operand.
            # The agent is a term (Variable/Constant); a bare string is also accepted.
            agent = node.agent
            agent = agent if isinstance(agent, str) else getattr(agent, "name", None) or agent.to_unicode_str()
            return f"{spec.unicode}{agent} " + _uni_wrap(node.formula, 4)
        if fix == "binary_until":
            # Ⓤ right-assoc: left slot same_level_ops (≥3), right slot until (≥2.5).
            return f"{_uni_wrap(node.left, 3)} {spec.unicode} {_uni_wrap(node.right, 2.5)}"
        if fix == "binary_iff":
            # ↔ right-assoc: left slot is implication (≥2), right slot biimplication (≥1)
            return f"{_uni_wrap(node.left, 2)} {spec.unicode} {_uni_wrap(node.right, 1)}"
        if fix == "binary_implies":
            # → right-assoc: left slot same_level_ops (≥3), right slot implication (≥2)
            return f"{_uni_wrap(node.left, 3)} {spec.unicode} {_uni_wrap(node.right, 2)}"
        if fix == "level2":
            left = _uni_level2_child(node.left, cls, "left")
            right = _uni_level2_child(node.right, cls, "right")
            return f"{left} {spec.unicode} {right}"

    if cls == "Quantifier":
        return f"{node.type}{node.variable.name} " + _uni_wrap(node.formula, 4)
    if cls == "SortedQuantifier":
        return f"{node.type}{node.variable.name}:{node.sort} " + _uni_wrap(node.formula, 4)
    if cls == "SecondOrderQuantifier":
        # Arity is NOT printed: it is re-inferred from the body on re-parse, so
        # printing it would break the round-trip. e.g. ∀P P(x, y).
        return f"{node.type}{node.predicate} " + _uni_wrap(node.formula, 4)

    if cls == "Lambda":
        # Body extends rightward through the whole formula; never wrapped here.
        return f"λ{node.param.name}. " + _uni(node.body)
    if cls == "Application":
        # (func)(arg): both sides are delimited by parens in the grammar.
        return f"({_uni(node.func)})({_uni(node.arg)})"

    raise TypeError(f"to_unicode_str: unknown node type {cls}")


# =========================
# LaTeX rendering
# =========================
#
# Mirrors the Unicode renderer above but emits LaTeX math-mode markup. It reuses
# the same precedence machinery (the operator registry and _uni_prec) so the
# parenthesisation is identical; only the operator markup (spec.latex) and term
# formatting differ. Output is not parseable by MSFLParser (so no round-trip),
# hence tests assert on exact strings.

# The LaTeX markup for every regular operator now lives in its OperatorSpec.latex
# (read at call time below), so the per-operator LaTeX glyph tables are gone.
# Only the term-level / quantifier-level tables — which are NOT driven by the
# operator registry — remain here.

_LATEX_COMPARE = {
    "=": "=", "≠": "\\neq", "<": "<", ">": ">", "≤": "\\leq", "≥": "\\geq",
}

_LATEX_ARITH = {"+": "+", "-": "-", "*": "\\cdot", "/": "/"}

_LATEX_QUANT = {"∀": "\\forall", "forall": "\\forall", "∃": "\\exists", "exists": "\\exists"}


def _latex_escape(name: str) -> str:
    """Escape LaTeX math-mode specials in a verbatim symbol name.

    Only the underscore can occur in a grammar-produced name (a c_-prefixed
    constant such as ``c_zero``); left bare it would be read as the subscript
    operator, so it is backslash-escaped. Other name classes (variables,
    predicates, functions, sorts) cannot contain LaTeX specials.
    """
    return name.replace("_", "\\_")


def _latex_wrap(node, min_prec: int) -> str:
    s = _latex(node)
    return f"({s})" if _uni_prec(node) < min_prec else s


def _latex_level2_child(node, parent_cls: str, side: str) -> str:
    s = _latex(node)
    p = _uni_prec(node)
    if side == "left":
        need = p < 3 or (p == 3 and type(node).__name__ != parent_cls)
    else:
        need = p < 4
    return f"({s})" if need else s


def _latex_term(node) -> str:
    cls = type(node).__name__
    if cls in ("Variable", "LambdaVar", "Constant"):
        return _latex_escape(node.name)
    if cls == "Number":
        return str(node.value)
    if cls == "SortedConstant":
        return f"{_latex_escape(node.name)}{{:}}\\mathrm{{{node.sort}}}"
    if cls == "Function":
        if node.name in _UNI_ARITH_OPS and len(node.args) == 2:
            p = _uni_term_prec(node)
            left = node.args[0]
            right = node.args[1]
            ls = _latex_term(left)
            rs = _latex_term(right)
            if _uni_term_prec(left) < p:
                ls = f"({ls})"
            if _uni_term_prec(right) < p or (_uni_term_prec(right) == p):
                rs = f"({rs})"
            return f"{ls} {_LATEX_ARITH[node.name]} {rs}"
        return f"{node.name}(" + ", ".join(_latex_term(a) for a in node.args) + ")"
    if cls == "Application":
        head, args = _uni_spine(node)
        if isinstance(head, (LambdaVar, Variable, Constant)) and args:
            return f"{head.name}(" + ", ".join(_latex_term(a) for a in args) + ")"
        return f"({_latex(node.func)})({_latex(node.arg)})"
    return _latex(node)


def _latex_atom(node) -> str:
    if node.predicate in _UNI_INFIX_COMPARE and len(node.args) == 2:
        return f"{_latex_term(node.args[0])} {_LATEX_COMPARE[node.predicate]} {_latex_term(node.args[1])}"
    if not node.args:
        return node.predicate
    return f"{node.predicate}(" + ", ".join(_latex_term(a) for a in node.args) + ")"


def _latex(node) -> str:
    """Render node as a LaTeX math-mode string (no surrounding parens)."""
    cls = type(node).__name__

    if cls in ("Variable", "LambdaVar", "Constant", "Number", "SortedConstant", "Function"):
        return _latex_term(node)
    if cls == "Atom":
        return _latex_atom(node)

    # Regular operators are driven entirely by the registry: the spec's fixity
    # selects the operand arrangement and spec.latex supplies the markup (already
    # including any trailing space for the prefix forms).
    spec = OPERATORS.get(cls)
    if spec is not None:
        fix = spec.fixity
        if fix == "prefix":
            return spec.latex + _latex_wrap(node.formula, 4)
        if fix == "agent_prefix":
            agent = node.agent
            agent = agent if isinstance(agent, str) else getattr(agent, "name", None) or agent.to_unicode_str()
            return f"{spec.latex}_{{{agent}}} " + _latex_wrap(node.formula, 4)
        if fix == "binary_until":
            return f"{_latex_wrap(node.left, 3)} {spec.latex} {_latex_wrap(node.right, 2.5)}"
        if fix == "binary_iff":
            return f"{_latex_wrap(node.left, 2)} {spec.latex} {_latex_wrap(node.right, 1)}"
        if fix == "binary_implies":
            return f"{_latex_wrap(node.left, 3)} {spec.latex} {_latex_wrap(node.right, 2)}"
        if fix == "level2":
            left = _latex_level2_child(node.left, cls, "left")
            right = _latex_level2_child(node.right, cls, "right")
            return f"{left} {spec.latex} {right}"

    if cls == "Quantifier":
        return f"{_LATEX_QUANT[node.type]} {node.variable.name}\\, " + _latex_wrap(node.formula, 4)
    if cls == "SortedQuantifier":
        return (f"{_LATEX_QUANT[node.type]} {node.variable.name}{{:}}\\mathrm{{{node.sort}}}\\, "
                + _latex_wrap(node.formula, 4))
    if cls == "SecondOrderQuantifier":
        # Arity is not rendered (mirrors the Unicode renderer). e.g. \forall P\, P(x).
        return f"{_LATEX_QUANT[node.type]} {node.predicate}\\, " + _latex_wrap(node.formula, 4)

    if cls == "Lambda":
        return f"\\lambda {node.param.name}.\\, " + _latex(node.body)
    if cls == "Application":
        return f"({_latex(node.func)})({_latex(node.arg)})"

    raise TypeError(f"to_latex: unknown node type {cls}")


# =========================
# Registry extension
# =========================

NODE_CLASSES.update({
    "SortedQuantifier": SortedQuantifier,
    "SortedConstant": SortedConstant,
    "WeakConjunction": WeakConjunction,
    "WeakDisjunction": WeakDisjunction,
    "StrongConjunction": StrongConjunction,
    "StrongDisjunction": StrongDisjunction,
    "LukNegation": LukNegation,
    "LukImplication": LukImplication,
    "LukEquivalence": LukEquivalence,
    "LambdaVar": LambdaVar,
    "Lambda": Lambda,
    "Application": Application,
})


# =========================
# MSFL Reductions
# =========================

def to_fol(node: Node, include_sort_facts: bool = False) -> Node:
    """Reduce an MSFL (or plain FOL) node to a purely classical FOL node.

    Two-phase reduction:
    1. to_msfol() — replaces Łukasiewicz operators with classical boolean
       counterparts (And/Or/Not/Implies/Iff); sort annotations are preserved.
    2. _relativize() — replaces SortedQuantifier with a guarded plain
       Quantifier; replaces SortedConstant with a plain Constant and collects
       sort-membership atoms as a side-effect.

    Args:
        node: any Node (MSFL or classical FOL).
        include_sort_facts: if True, deduplicated sort-membership atoms are
            conjoined as a prefix block at the top level. Dedup is by
            (sort-predicate, constant-name) in first-occurrence order.

    Returns:
        A Node built from classical FOL constructs only.
    """
    msfol = node.to_msfol()
    facts: list = []
    fol = msfol._relativize(facts)
    if include_sort_facts and facts:
        seen: set = set()
        dedup = []
        for f in facts:
            key = (f.predicate, f.args[0].name)
            if key not in seen:
                seen.add(key)
                dedup.append(f)
        conj = dedup[0]
        for f in dedup[1:]:
            conj = And(conj, f)
        return And(conj, fol)
    return fol
