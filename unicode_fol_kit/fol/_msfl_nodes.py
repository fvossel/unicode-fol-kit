"""MSFL node classes (sorted quantifiers/constants, Łukasiewicz operators) and to_fol reduction."""

import logging
from dataclasses import dataclass

from ._fol_nodes import (
    Node, Z3Env, Variable, Constant, Number, Function,
    Atom, Not, And, Or, Xor, Implies, Iff, Quantifier,
    NODE_CLASSES,
)

_logger = logging.getLogger(__name__)


# =========================
# MSFL Nodes
# =========================

@dataclass
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


@dataclass
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


@dataclass
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


@dataclass
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


@dataclass
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


@dataclass
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


@dataclass
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


@dataclass
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


@dataclass
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


@dataclass
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


@dataclass
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
    if isinstance(node, (Atom, Function)):
        result: set = set()
        for a in node.args:
            result |= free_variables(a)
        return result
    if isinstance(node, (Not, LukNegation)):
        return free_variables(node.formula)
    if isinstance(node, (And, Or, Xor, Implies, Iff,
                          WeakConjunction, WeakDisjunction,
                          StrongConjunction, StrongDisjunction,
                          LukImplication, LukEquivalence)):
        return free_variables(node.left) | free_variables(node.right)
    if isinstance(node, Application):
        return free_variables(node.func) | free_variables(node.arg)
    if isinstance(node, Lambda):
        return free_variables(node.body) - {node.param}
    if isinstance(node, (Quantifier, SortedQuantifier)):
        return free_variables(node.formula) - {node.variable}
    raise TypeError(f"free_variables: unknown node type {type(node).__name__}")


# =========================
# Capture-avoiding beta-reduction
# =========================

BETA_REDUCTION_LIMIT = 10_000


class ReductionLimitError(Exception):
    pass


def _names_in(node: Node) -> set:
    """Return all Variable and LambdaVar nodes appearing in node (free and bound)."""
    if isinstance(node, (Variable, LambdaVar)):
        return {node}
    if isinstance(node, (Constant, Number, SortedConstant)):
        return set()
    if isinstance(node, (Atom, Function)):
        result: set = set()
        for a in node.args:
            result |= _names_in(a)
        return result
    if isinstance(node, (Not, LukNegation)):
        return _names_in(node.formula)
    if isinstance(node, (And, Or, Xor, Implies, Iff,
                          WeakConjunction, WeakDisjunction,
                          StrongConjunction, StrongDisjunction,
                          LukImplication, LukEquivalence)):
        return _names_in(node.left) | _names_in(node.right)
    if isinstance(node, Application):
        return _names_in(node.func) | _names_in(node.arg)
    if isinstance(node, Lambda):
        return {node.param} | _names_in(node.body)
    if isinstance(node, Quantifier):
        return {node.variable} | _names_in(node.formula)
    if isinstance(node, SortedQuantifier):
        return {node.variable} | _names_in(node.formula)
    return set()


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
    if isinstance(term, (Constant, Number, SortedConstant)):
        return term
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
    if isinstance(term, Atom):
        return Atom(term.predicate, [_rename(a, old_var, new_var) for a in term.args])
    if isinstance(term, Function):
        return Function(term.name, [_rename(a, old_var, new_var) for a in term.args])
    if isinstance(term, Application):
        return Application(_rename(term.func, old_var, new_var),
                           _rename(term.arg, old_var, new_var))
    if isinstance(term, (Not, LukNegation)):
        return type(term)(_rename(term.formula, old_var, new_var))
    if isinstance(term, (And, Or, Xor, Implies, Iff,
                          WeakConjunction, WeakDisjunction,
                          StrongConjunction, StrongDisjunction,
                          LukImplication, LukEquivalence)):
        return type(term)(_rename(term.left, old_var, new_var),
                          _rename(term.right, old_var, new_var))
    return term  # Variable/LambdaVar that don't match old_var; unknown types


def _subst(term: Node, target: LambdaVar, replacement: Node, fv_repl: set) -> Node:
    """Capture-avoiding substitution of target with replacement in term.

    fv_repl = free_variables(replacement), precomputed by the caller.
    target is always a LambdaVar; replacement may be any Node.
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
        # Quantifier binds a Variable; target is LambdaVar — can never shadow target.
        # But the quantifier variable may capture a free Variable from replacement.
        if term.variable in fv_repl:
            avoid = fv_repl | _names_in(term.formula)
            fresh = Variable(_fresh_name(term.variable.name, avoid))
            new_formula = _rename(term.formula, term.variable, fresh)
            return Quantifier(term.type, fresh,
                              _subst(new_formula, target, replacement, fv_repl))
        return Quantifier(term.type, term.variable,
                          _subst(term.formula, target, replacement, fv_repl))
    if isinstance(term, SortedQuantifier):
        if term.variable in fv_repl:
            avoid = fv_repl | _names_in(term.formula)
            fresh = Variable(_fresh_name(term.variable.name, avoid))
            new_formula = _rename(term.formula, term.variable, fresh)
            return SortedQuantifier(term.type, fresh, term.sort,
                                    _subst(new_formula, target, replacement, fv_repl))
        return SortedQuantifier(term.type, term.variable, term.sort,
                                _subst(term.formula, target, replacement, fv_repl))
    if isinstance(term, Atom):
        return Atom(term.predicate,
                    [_subst(a, target, replacement, fv_repl) for a in term.args])
    if isinstance(term, Function):
        return Function(term.name,
                        [_subst(a, target, replacement, fv_repl) for a in term.args])
    if isinstance(term, Application):
        return Application(_subst(term.func, target, replacement, fv_repl),
                           _subst(term.arg, target, replacement, fv_repl))
    if isinstance(term, (Not, LukNegation)):
        return type(term)(_subst(term.formula, target, replacement, fv_repl))
    if isinstance(term, (And, Or, Xor, Implies, Iff,
                          WeakConjunction, WeakDisjunction,
                          StrongConjunction, StrongDisjunction,
                          LukImplication, LukEquivalence)):
        return type(term)(_subst(term.left, target, replacement, fv_repl),
                          _subst(term.right, target, replacement, fv_repl))
    return term  # unknown types: pass through


def substitute(term: Node, target: LambdaVar, replacement: Node) -> Node:
    """Substitute target (a LambdaVar) with replacement in term, with full capture avoidance.

    Returns a new Node; the input is never mutated.
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
        if isinstance(node, Lambda):
            return Lambda(node.param, _beta_reduce(node.body, steps))
        if isinstance(node, Quantifier):
            return Quantifier(node.type, node.variable, _beta_reduce(node.formula, steps))
        if isinstance(node, SortedQuantifier):
            return SortedQuantifier(node.type, node.variable, node.sort,
                                    _beta_reduce(node.formula, steps))
        if isinstance(node, Atom):
            return Atom(node.predicate, [_beta_reduce(a, steps) for a in node.args])
        if isinstance(node, Function):
            return Function(node.name, [_beta_reduce(a, steps) for a in node.args])
        if isinstance(node, (Not, LukNegation)):
            return type(node)(_beta_reduce(node.formula, steps))
        if isinstance(node, (And, Or, Xor, Implies, Iff,
                              WeakConjunction, WeakDisjunction,
                              StrongConjunction, StrongDisjunction,
                              LukImplication, LukEquivalence)):
            return type(node)(_beta_reduce(node.left, steps), _beta_reduce(node.right, steps))
        return node  # leaves and unknown types


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
    if isinstance(node, Application):
        return Application(_eta_reduce(node.func), _eta_reduce(node.arg))
    if isinstance(node, Quantifier):
        # Recurse into the formula; Quantifier is NEVER an eta-redex.
        return Quantifier(node.type, node.variable, _eta_reduce(node.formula))
    if isinstance(node, SortedQuantifier):
        return SortedQuantifier(node.type, node.variable, node.sort,
                                _eta_reduce(node.formula))
    if isinstance(node, Atom):
        return Atom(node.predicate, [_eta_reduce(a) for a in node.args])
    if isinstance(node, Function):
        return Function(node.name, [_eta_reduce(a) for a in node.args])
    if isinstance(node, (Not, LukNegation)):
        return type(node)(_eta_reduce(node.formula))
    if isinstance(node, (And, Or, Xor, Implies, Iff,
                          WeakConjunction, WeakDisjunction,
                          StrongConjunction, StrongDisjunction,
                          LukImplication, LukEquivalence)):
        return type(node)(_eta_reduce(node.left), _eta_reduce(node.right))
    return node


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
    if isinstance(node, Application):
        return Application(_resolve(node.func, bound), _resolve(node.arg, bound))
    if isinstance(node, (Not, LukNegation)):
        return type(node)(_resolve(node.formula, bound))
    if isinstance(node, (And, Or, Xor, Implies, Iff,
                          WeakConjunction, WeakDisjunction,
                          StrongConjunction, StrongDisjunction,
                          LukImplication, LukEquivalence)):
        return type(node)(_resolve(node.left, bound), _resolve(node.right, bound))
    raise TypeError(f"resolve_lambda_scope: unknown node type {type(node).__name__}")


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
