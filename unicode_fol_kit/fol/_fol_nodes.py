"""Z3 environment, base Node class, classical FOL nodes, registry, and Lark transformer."""

from typing import List, Tuple, Union, Dict
from lark import Transformer
from dataclasses import dataclass, fields

import z3

_SORT = z3.DeclareSort("S")


# =========================
# Z3 Environment
# =========================

class Z3Env:
    """Tracks declared Z3 symbols. Single sort for all terms."""

    def __init__(self):
        """Initialise empty symbol, function, and predicate tables."""
        self.symbols: Dict[str, z3.ExprRef] = {}
        self.funcs: Dict[str, z3.FuncDeclRef] = {}
        self.preds: Dict[str, z3.FuncDeclRef] = {}

    def get_symbol(self, name: str) -> z3.ExprRef:
        """Get or create a Z3 constant (used for both variables and constants)."""
        if name not in self.symbols:
            self.symbols[name] = z3.Const(name, _SORT)
        return self.symbols[name]

    def get_func(self, name: str, arity: int) -> z3.FuncDeclRef:
        """Get or create an uninterpreted Z3 function of the given arity mapping S^arity -> S."""
        if name not in self.funcs:
            self.funcs[name] = z3.Function(name, *([_SORT] * arity), _SORT)
        return self.funcs[name]

    def get_pred(self, name: str, arity: int) -> z3.FuncDeclRef:
        """Get or create an uninterpreted Z3 predicate of the given arity mapping S^arity -> Bool."""
        if name not in self.preds:
            self.preds[name] = z3.Function(name, *([_SORT] * arity), z3.BoolSort())
        return self.preds[name]


# =========================
# Base Node
# =========================

class Node:
    """Base class for all AST nodes."""

    def to_dict(self) -> dict:
        """Serialise this node to a JSON-compatible dictionary."""
        raise NotImplementedError

    def to_z3(self, env: Z3Env = None) -> z3.ExprRef:
        """Translate this node into a Z3 expression using the given environment."""
        raise NotImplementedError

    def to_prover9(self) -> str:
        """Render this node as a Prover9-syntax string."""
        raise NotImplementedError

    def to_tptp(self) -> str:
        """Render this node as a TPTP-syntax string."""
        raise NotImplementedError

    @staticmethod
    def from_dict(d: dict) -> "Node":
        """Deserialise a node from a dictionary produced by to_dict."""
        t = d["_type"]
        if t not in NODE_CLASSES:
            raise ValueError(f"Unknown type: {t}")
        return NODE_CLASSES[t].from_dict(d)

    _TREE_LABELS = {
        "And": "∧", "Or": "∨", "Xor": "⊕",
        "Implies": "→", "Iff": "↔", "Not": "¬",
        "Contrast": "Ⓒ",
    }

    def _tree_parts(self):
        """Return (label, children) for tree rendering.

        Leaf terms render their value in the label and have no children.
        Atom and Function render the symbol in the label and expose their
        argument nodes. Quantifier shows its type and bound variable.
        Everything else falls back to its dataclass fields, treating any
        Node-valued field as a child.
        """
        cls = type(self).__name__
        if cls in ("Variable", "Constant"):
            return f"{cls}: {self.name}", []
        if cls == "Number":
            return f"Number: {self.value}", []
        if cls == "Atom":
            return f"Atom: {self.predicate}", list(self.args)
        if cls == "Function":
            return f"Function: {self.name}", list(self.args)
        if cls == "Quantifier":
            return f"{self.type} {self.variable.name}", [self.formula]

        label = self._TREE_LABELS.get(cls, cls)
        children = []
        for f in fields(self):
            value = getattr(self, f.name)
            if isinstance(value, Node):
                children.append(value)
            elif isinstance(value, (list, tuple)):
                children.extend(c for c in value if isinstance(c, Node))
        return label, children

    def to_unicode_str(self) -> str:
        """Render this node back to a parseable Unicode formula string.

        The result, re-parsed in the matching MSFLParser mode, yields a
        structurally equal AST (parser round-trip). The renderer lives in
        _msfl_nodes.py (imported lazily to avoid a circular import) because it
        dispatches over both the FOL nodes here and the MSFL/lambda nodes there.
        """
        from ._msfl_nodes import _uni
        return _uni(self)

    def to_latex(self) -> str:
        """Render this node as a LaTeX math-mode string (no surrounding $…$).

        Uses the same precedence-driven parenthesisation as to_unicode_str.
        Symbol/function/predicate names are emitted verbatim (no \\mathrm
        wrapping). The renderer lives in _msfl_nodes.py (imported lazily) so it
        can dispatch over both FOL and MSFL/lambda nodes.
        """
        from ._msfl_nodes import _latex
        return _latex(self)

    def tree_str(self) -> str:
        """Render the AST as a multi-line ASCII tree using ├──/└── connectors."""
        label, children = self._tree_parts()
        lines = [label]
        for i, child in enumerate(children):
            last = i == len(children) - 1
            branch = "└── " if last else "├── "
            prefix = "    " if last else "│   "
            sub = child.tree_str().split("\n")
            lines.append(branch + sub[0])
            lines.extend(prefix + s for s in sub[1:])
        return "\n".join(lines)

    def to_msfol(self) -> "Node":
        """Lower Łukasiewicz operators to classical counterparts; recurse into children.

        Classical and sort-annotated nodes return a structurally equal copy with
        children recursed. Fuzzy operator subclasses override this to substitute
        the corresponding classical node type.
        """
        return self.map_children(lambda c: c.to_msfol())

    def _relativize(self, facts: list) -> "Node":
        """Replace sorted nodes with plain FOL constructs; collect sort-membership atoms.

        Classical nodes return a structurally equal copy with children recursed.
        SortedQuantifier and SortedConstant override this with their specific rules.
        Fuzzy operator subclasses override to raise RuntimeError — they must be
        eliminated by to_msfol() before _relativize() is called.
        """
        return self.map_children(lambda c: c._relativize(facts))

    # ---------------------------------------------------------------
    # Traversal / inspection API
    # ---------------------------------------------------------------

    def _child_nodes(self) -> List["Node"]:
        """Return the immediate Node-valued children, in declaration order.

        Covers both single Node fields and lists of Nodes. Quantifier exposes
        its bound variable here (it is a Node); for a rendering-oriented child
        view see _tree_parts.
        """
        result: List["Node"] = []
        for f in fields(self):
            val = getattr(self, f.name)
            if isinstance(val, Node):
                result.append(val)
            elif isinstance(val, (list, tuple)):
                result.extend(c for c in val if isinstance(c, Node))
        return result

    def map_children(self, fn) -> "Node":
        """Rebuild this node with ``fn`` applied to each immediate Node child.

        The single point of structural recursion. Each dataclass field is
        handled by kind: a Node field becomes ``fn(value)``; a list/tuple field
        has ``fn`` mapped over its Node elements (non-Node elements pass
        through, container kind preserved); any other field is copied verbatim.
        The node type and field order are preserved.

        Binders (Lambda, Quantifier, SortedQuantifier) carry their bound
        variable as a plain Node field, so ``fn`` is applied to it too; callers
        that must treat a binder's scope specially should handle that case
        explicitly before delegating here. This is the shared engine behind the
        purely structural recursions (to_msfol, _relativize, beta/eta reduction,
        scope resolution, …), so a new structural node type is handled
        automatically without touching each traversal.
        """
        new_kwargs = {}
        for f in fields(self):
            val = getattr(self, f.name)
            if isinstance(val, Node):
                new_kwargs[f.name] = fn(val)
            elif isinstance(val, (list, tuple)):
                new_kwargs[f.name] = type(val)(
                    fn(c) if isinstance(c, Node) else c for c in val
                )
            else:
                new_kwargs[f.name] = val
        return type(self)(**new_kwargs)

    def walk(self):
        """Yield this node and every descendant in pre-order (depth-first)."""
        yield self
        for child in self._child_nodes():
            yield from child.walk()

    def subformulas(self):
        """Yield every sub-node that is a formula (i.e. not an atomic term).

        Terms (Variable, Constant, Number, Function, SortedConstant, LambdaVar)
        are excluded; everything else reachable is returned in pre-order.
        """
        return [n for n in self.walk() if type(n).__name__ not in _TERM_NAMES]

    def atoms(self):
        """Return all Atom nodes in pre-order (duplicates kept; comparisons included)."""
        return [n for n in self.walk() if isinstance(n, Atom)]

    def variables(self):
        """Return the set of logical Variable nodes occurring anywhere (free and bound)."""
        return {n for n in self.walk() if isinstance(n, Variable)}

    def count(self, cls=None) -> int:
        """Count nodes in the tree; if cls is given, only nodes of that type."""
        return sum(1 for n in self.walk() if cls is None or isinstance(n, cls))

    def depth(self) -> int:
        """Return the height of the tree; a leaf node has depth 1."""
        children = self._child_nodes()
        return 1 + max((c.depth() for c in children), default=0)

    def to_dot(self) -> str:
        """Render the AST as a Graphviz DOT digraph string.

        Uses the same label/child view as tree_str (the bound variable of a
        quantifier is folded into its node label, not shown as a child), so the
        graph mirrors the ASCII tree. No external dependency: returns the source.
        """
        lines = ["digraph AST {", "  node [shape=box];"]
        counter = [0]

        def emit(node: "Node") -> int:
            my_id = counter[0]
            counter[0] += 1
            label, children = node._tree_parts()
            safe = label.replace("\\", "\\\\").replace('"', '\\"')
            lines.append(f'  n{my_id} [label="{safe}"];')
            for child in children:
                child_id = emit(child)
                lines.append(f"  n{my_id} -> n{child_id};")
            return my_id

        emit(self)
        lines.append("}")
        return "\n".join(lines)


# Term node class names — used by Node.subformulas to exclude atomic terms.
# Measure and Cardinality are term-valued (they occur in argument position and
# are compared with </>); Cardinality additionally carries a formula child, which
# Node.walk still descends into, so its φ is still reported among subformulas.
_TERM_NAMES = frozenset({
    "Variable", "Constant", "Number", "Function", "SortedConstant", "LambdaVar",
    "Measure", "Cardinality",
})


# =========================
# Term Nodes
# =========================

@dataclass(frozen=True)
class Variable(Node):
    """A logical variable, represented by a single lowercase letter in the grammar."""

    name: str

    def to_dict(self):
        """Serialise to dict with type tag and variable name."""
        return {"_type": "Variable", "name": self.name}

    @staticmethod
    def from_dict(d):
        """Deserialise a Variable from a dict produced by to_dict."""
        return Variable(d["name"])

    def to_z3(self, env: Z3Env = None):
        """Translate to a Z3 constant in the uninterpreted sort S."""
        return (env or Z3Env()).get_symbol(self.name)

    def to_prover9(self) -> str:
        """Render the variable name in uppercase.

        The Prover9 driver enables ``set(prolog_style_variables)``, under which a
        symbol is a variable only if it begins with an uppercase letter or an
        underscore. Grammar variable names are always lowercase, so they are
        uppercased here; constants and predicate/function names stay as-is.
        """
        return self.name.upper()

    def to_tptp(self) -> str:
        """Render variable in TPTP syntax. TPTP requires variables to be uppercase; single lowercase letters are capitalized."""
        return self.name.upper()


@dataclass(frozen=True)
class Constant(Node):
    """A ground constant, produced by a bare NAME or by the c_-prefixed CONSTANT terminal."""

    name: str

    def to_dict(self):
        """Serialise to dict with type tag and constant name."""
        return {"_type": "Constant", "name": self.name}

    @staticmethod
    def from_dict(d):
        """Deserialise a Constant from a dict produced by to_dict."""
        return Constant(d["name"])

    def to_z3(self, env: Z3Env = None):
        """Translate to a Z3 constant in the uninterpreted sort S."""
        return (env or Z3Env()).get_symbol(self.name)

    def to_prover9(self) -> str:
        """Render the constant name as-is."""
        return self.name

    def to_tptp(self) -> str:
        """Render constant in TPTP syntax. TPTP requires constants to start with a lowercase letter."""
        return self.name.lower()


@dataclass(frozen=True)
class Number(Node):
    """A numeric literal node, produced by the NUMBER terminal in the grammar."""

    value: Union[int, float]

    def to_dict(self):
        """Serialise to dict with type tag and numeric value."""
        return {"_type": "Number", "value": self.value}

    @staticmethod
    def from_dict(d):
        """Deserialise a Number from a dict produced by to_dict."""
        return Number(d["value"])

    def to_z3(self, env: Z3Env = None):
        """Encode the number as a named constant in the uninterpreted sort S."""
        return (env or Z3Env()).get_symbol(str(self.value))

    def to_prover9(self) -> str:
        """Render the numeric value as a plain string."""
        return str(self.value)

    def to_tptp(self) -> str:
        """Render number in TPTP syntax as an integer or rational literal."""
        return str(self.value)


@dataclass(frozen=True)
class Function(Node):
    """A function application node, covering both named functions and arithmetic operators."""

    name: str
    args: Tuple[Node, ...]

    def __post_init__(self):
        """Coerce args to a tuple so this frozen node is hashable."""
        if not isinstance(self.args, tuple):
            object.__setattr__(self, "args", tuple(self.args))

    INFIX_OPS = {"+", "-", "*", "/"}

    def to_dict(self):
        """Serialise to dict with type tag, function name, and recursively serialised arguments."""
        return {
            "_type": "Function",
            "name": self.name,
            "args": [a.to_dict() for a in self.args]
        }

    @staticmethod
    def from_dict(d):
        """Deserialise a Function from a dict produced by to_dict."""
        return Function(d["name"], [Node.from_dict(a) for a in d["args"]])

    def to_z3(self, env: Z3Env = None):
        """Translate to an uninterpreted Z3 function application in sort S."""
        env = env or Z3Env()
        z3_args = [a.to_z3(env) for a in self.args]
        func = env.get_func(self.name, len(self.args))
        return func(*z3_args)

    def to_prover9(self) -> str:
        """Render in Prover9 syntax, using infix notation for arithmetic operators."""
        if self.name in self.INFIX_OPS and len(self.args) == 2:
            left = self.args[0].to_prover9()
            right = self.args[1].to_prover9()
            return f"({left} {self.name} {right})"

        args_str = ", ".join(a.to_prover9() for a in self.args)
        return f"{self.name}({args_str})"

    TPTP_ARITH_OPS = {
        "+": "$sum",
        "-": "$difference",
        "*": "$product",
        "/": "$quotient",
    }

    def to_tptp(self) -> str:
        """Render function application in TPTP syntax.

        Arithmetic operators (+, -, *, /) are mapped to their TPTP dollar-word
        equivalents ($sum, $difference, $product, $quotient) and emitted in
        prefix notation. All other functions are emitted as lowercase
        identifiers with a parenthesised argument list.
        """
        args_str = ",".join(a.to_tptp() for a in self.args)
        tptp_name = self.TPTP_ARITH_OPS.get(self.name, self.name.lower())
        return f"{tptp_name}({args_str})"


# =========================
# Formula Nodes
# =========================

@dataclass(frozen=True)
class Atom(Node):
    """An atomic formula: either a named predicate application or an infix comparison."""

    predicate: str
    args: Tuple[Node, ...]

    def __post_init__(self):
        """Coerce args to a tuple so this frozen node is hashable."""
        if not isinstance(self.args, tuple):
            object.__setattr__(self, "args", tuple(self.args))

    INFIX_PREDS_P9 = {
        "=": "=", "<": "<", ">": ">",
        "≤": "<=", "≥": ">=", "≠": "!=",
    }

    def to_dict(self):
        """Serialise to dict with type tag, predicate name, and recursively serialised arguments."""
        return {
            "_type": "Atom",
            "predicate": self.predicate,
            "args": [a.to_dict() for a in self.args]
        }

    @staticmethod
    def from_dict(d):
        """Deserialise an Atom from a dict produced by to_dict."""
        return Atom(d["predicate"], [Node.from_dict(a) for a in d["args"]])

    def to_z3(self, env: Z3Env = None):
        """Translate to a Z3 boolean expression.

        Equality and disequality map to native Z3 operators; all other
        predicates become uninterpreted Z3 functions returning Bool.
        """
        env = env or Z3Env()
        z3_args = [a.to_z3(env) for a in self.args]

        if self.predicate == "=" and len(self.args) == 2:
            return z3_args[0] == z3_args[1]
        if self.predicate == "≠" and len(self.args) == 2:
            return z3_args[0] != z3_args[1]

        pred = env.get_pred(self.predicate, len(self.args))
        return pred(*z3_args)

    def to_prover9(self) -> str:
        """Render in Prover9 syntax, using infix notation for comparison predicates.

        A nullary predicate renders as a bare propositional atom; Prover9 rejects
        an empty argument list (``P()``).
        """
        if self.predicate in self.INFIX_PREDS_P9 and len(self.args) == 2:
            left = self.args[0].to_prover9()
            right = self.args[1].to_prover9()
            op = self.INFIX_PREDS_P9[self.predicate]
            return f"({left} {op} {right})"

        if not self.args:
            return self.predicate

        args_str = ", ".join(a.to_prover9() for a in self.args)
        return f"{self.predicate}({args_str})"

    # The only genuine infix predicates in TPTP are equality and disequality.
    INFIX_PREDS_TPTP = {
        "=": "=",
        "≠": "!=",
    }

    # Arithmetic comparisons are TPTP dollar-word predicates, applied in
    # prefix/functor form ($less(a, b)) — they are NOT infix operators.
    PREFIX_PREDS_TPTP = {
        "<": "$less",
        ">": "$greater",
        "≤": "$lesseq",
        "≥": "$greatereq",
    }

    def to_tptp(self) -> str:
        """Render an atom in TPTP syntax.

        Equality (=) and disequality (!=) are emitted infix — the only genuine
        infix predicates in TPTP. The arithmetic comparisons (<, >, ≤, ≥) are
        TPTP dollar-word predicates and are emitted in prefix/functor form
        ($less(a, b), $greater(a, b), $lesseq(a, b), $greatereq(a, b)). All other
        predicates are emitted as lowercase identifiers with a parenthesised
        argument list; a nullary predicate becomes a bare propositional atom.
        """
        if self.predicate in self.INFIX_PREDS_TPTP and len(self.args) == 2:
            left = self.args[0].to_tptp()
            right = self.args[1].to_tptp()
            op = self.INFIX_PREDS_TPTP[self.predicate]
            return f"({left} {op} {right})"

        if self.predicate in self.PREFIX_PREDS_TPTP and len(self.args) == 2:
            left = self.args[0].to_tptp()
            right = self.args[1].to_tptp()
            op = self.PREFIX_PREDS_TPTP[self.predicate]
            return f"{op}({left},{right})"

        if not self.args:
            return f"{self.predicate.lower()}"

        args_str = ",".join(a.to_tptp() for a in self.args)
        return f"{self.predicate.lower()}({args_str})"


@dataclass(frozen=True)
class Not(Node):
    """Logical negation of a formula."""

    formula: Node

    def to_dict(self):
        """Serialise to dict with type tag and recursively serialised subformula."""
        return {"_type": "Not", "formula": self.formula.to_dict()}

    @staticmethod
    def from_dict(d):
        """Deserialise a Not from a dict produced by to_dict."""
        return Not(Node.from_dict(d["formula"]))

    def to_z3(self, env: Z3Env = None):
        """Translate to a Z3 Not expression."""
        return z3.Not(self.formula.to_z3(env or Z3Env()))

    def to_prover9(self) -> str:
        """Render negation in Prover9 syntax using the dash operator."""
        return f"-({self.formula.to_prover9()})"

    def to_tptp(self) -> str:
        """Render negation in TPTP syntax using the tilde operator."""
        return f"~({self.formula.to_tptp()})"


@dataclass(frozen=True)
class And(Node):
    """Conjunction of two formulas."""

    left: Node
    right: Node

    def to_dict(self):
        """Serialise to dict with type tag and recursively serialised operands."""
        return {"_type": "And", "left": self.left.to_dict(), "right": self.right.to_dict()}

    @staticmethod
    def from_dict(d):
        """Deserialise an And from a dict produced by to_dict."""
        return And(Node.from_dict(d["left"]), Node.from_dict(d["right"]))

    def to_z3(self, env: Z3Env = None):
        """Translate to a Z3 And expression."""
        env = env or Z3Env()
        return z3.And(self.left.to_z3(env), self.right.to_z3(env))

    def to_prover9(self) -> str:
        """Render conjunction in Prover9 syntax using the ampersand operator."""
        return f"({self.left.to_prover9()} & {self.right.to_prover9()})"

    def to_tptp(self) -> str:
        """Render conjunction in TPTP syntax using the ampersand operator."""
        return f"({self.left.to_tptp()} & {self.right.to_tptp()})"


@dataclass(frozen=True)
class Or(Node):
    """Disjunction of two formulas."""

    left: Node
    right: Node

    def to_dict(self):
        """Serialise to dict with type tag and recursively serialised operands."""
        return {"_type": "Or", "left": self.left.to_dict(), "right": self.right.to_dict()}

    @staticmethod
    def from_dict(d):
        """Deserialise an Or from a dict produced by to_dict."""
        return Or(Node.from_dict(d["left"]), Node.from_dict(d["right"]))

    def to_z3(self, env: Z3Env = None):
        """Translate to a Z3 Or expression."""
        env = env or Z3Env()
        return z3.Or(self.left.to_z3(env), self.right.to_z3(env))

    def to_prover9(self) -> str:
        """Render disjunction in Prover9 syntax using the pipe operator."""
        return f"({self.left.to_prover9()} | {self.right.to_prover9()})"

    def to_tptp(self) -> str:
        """Render disjunction in TPTP syntax using the pipe operator."""
        return f"({self.left.to_tptp()} | {self.right.to_tptp()})"


@dataclass(frozen=True)
class Xor(Node):
    """Exclusive disjunction of two formulas."""

    left: Node
    right: Node

    def to_dict(self):
        """Serialise to dict with type tag and recursively serialised operands."""
        return {"_type": "Xor", "left": self.left.to_dict(), "right": self.right.to_dict()}

    @staticmethod
    def from_dict(d):
        """Deserialise an Xor from a dict produced by to_dict."""
        return Xor(Node.from_dict(d["left"]), Node.from_dict(d["right"]))

    def to_z3(self, env: Z3Env = None):
        """Translate to a Z3 Xor expression."""
        env = env or Z3Env()
        return z3.Xor(self.left.to_z3(env), self.right.to_z3(env))

    def to_prover9(self) -> str:
        """Render exclusive or in Prover9 syntax by expanding to (l | r) & -(l & r)."""
        l = self.left.to_prover9()
        r = self.right.to_prover9()
        return f"(({l} | {r}) & -(({l}) & ({r})))"

    def to_tptp(self) -> str:
        """Render exclusive or in TPTP syntax using the non-equivalence operator (<~>).

        In TPTP ``~|`` is NOR, not XOR; ``<~>`` (non-equivalence) is the operator
        truth-functionally equal to exclusive or.
        """
        return f"({self.left.to_tptp()} <~> {self.right.to_tptp()})"


@dataclass(frozen=True)
class Implies(Node):
    """Material implication from left to right."""

    left: Node
    right: Node

    def to_dict(self):
        """Serialise to dict with type tag and recursively serialised operands."""
        return {"_type": "Implies", "left": self.left.to_dict(), "right": self.right.to_dict()}

    @staticmethod
    def from_dict(d):
        """Deserialise an Implies from a dict produced by to_dict."""
        return Implies(Node.from_dict(d["left"]), Node.from_dict(d["right"]))

    def to_z3(self, env: Z3Env = None):
        """Translate to a Z3 Implies expression."""
        env = env or Z3Env()
        return z3.Implies(self.left.to_z3(env), self.right.to_z3(env))

    def to_prover9(self) -> str:
        """Render implication in Prover9 syntax using the -> operator."""
        return f"({self.left.to_prover9()} -> {self.right.to_prover9()})"

    def to_tptp(self) -> str:
        """Render implication in TPTP syntax using the => operator."""
        return f"({self.left.to_tptp()} => {self.right.to_tptp()})"


@dataclass(frozen=True)
class Iff(Node):
    """Biconditional (if and only if) between two formulas."""

    left: Node
    right: Node

    def to_dict(self):
        """Serialise to dict with type tag and recursively serialised operands."""
        return {"_type": "Iff", "left": self.left.to_dict(), "right": self.right.to_dict()}

    @staticmethod
    def from_dict(d):
        """Deserialise an Iff from a dict produced by to_dict."""
        return Iff(Node.from_dict(d["left"]), Node.from_dict(d["right"]))

    def to_z3(self, env: Z3Env = None):
        """Translate to Z3 equality of the two boolean subexpressions."""
        env = env or Z3Env()
        return self.left.to_z3(env) == self.right.to_z3(env)

    def to_prover9(self) -> str:
        """Render biconditional in Prover9 syntax using the <-> operator."""
        return f"({self.left.to_prover9()} <-> {self.right.to_prover9()})"

    def to_tptp(self) -> str:
        """Render biconditional in TPTP syntax using the <=> operator."""
        return f"({self.left.to_tptp()} <=> {self.right.to_tptp()})"


@dataclass(frozen=True)
class Quantifier(Node):
    """A universally or existentially quantified formula over a single variable."""

    type: str
    variable: Variable
    formula: Node

    def to_dict(self):
        """Serialise to dict with type tag, quantifier type, variable, and recursively serialised body."""
        return {
            "_type": "Quantifier",
            "type": self.type,
            "variable": self.variable.to_dict(),
            "formula": self.formula.to_dict()
        }

    @staticmethod
    def from_dict(d):
        """Deserialise a Quantifier from a dict produced by to_dict."""
        return Quantifier(d["type"], Node.from_dict(d["variable"]), Node.from_dict(d["formula"]))

    def to_z3(self, env: Z3Env = None):
        """Translate to a Z3 ForAll or Exists expression over the bound variable."""
        env = env or Z3Env()
        z3_var = self.variable.to_z3(env)
        body = self.formula.to_z3(env)

        if self.type in ("forall", "∀"):
            return z3.ForAll([z3_var], body)
        elif self.type in ("exists", "∃"):
            return z3.Exists([z3_var], body)
        raise ValueError(f"Unknown quantifier: {self.type}")

    def to_prover9(self) -> str:
        """Render the quantified formula in Prover9 syntax using all/exists keywords."""
        var = self.variable.to_prover9()
        body = self.formula.to_prover9()

        if self.type in ("forall", "∀"):
            return f"(all {var} {body})"
        elif self.type in ("exists", "∃"):
            return f"(exists {var} {body})"
        raise ValueError(f"Unknown quantifier: {self.type}")

    def to_tptp(self) -> str:
        """Render a quantified formula in TPTP syntax.

        Universal quantification uses ! and existential uses ?,
        with the bound variable listed in brackets: ![X]: body or ?[X]: body.
        """
        var = self.variable.to_tptp()
        body = self.formula.to_tptp()

        if self.type in ("forall", "∀"):
            return f"(![{var}]: {body})"
        elif self.type in ("exists", "∃"):
            return f"(?[{var}]: {body})"
        raise ValueError(f"Unknown quantifier: {self.type}")


# =========================
# Counting quantifier, measure / cardinality terms, concessive connective
# =========================
#
# Classical, non-modal extensions used by natural-language → logic front-ends
# (e.g. CCG pipelines) to translate cardinal determiners, degree comparatives,
# counting comparisons, and concessive coordination:
#
#   * Count       — a cardinality quantifier ∃≥n / ∃≤n / ∃=n carrying its bound n
#                   SYMBOLICALLY (a Number, not expanded into single-letter
#                   variables), so an arbitrarily large n is represented exactly.
#                   It is first-order expressible; the exports lower it to the
#                   standard distinct-witnesses encoding via _expand().
#   * Measure     — a degree/measure term μ(entity, dimension) for bare quantity
#                   comparatives (μ(x, height) > μ(y, height)); an uninterpreted
#                   binary function on export.
#   * Cardinality — a set-cardinality term |{v : φ}| for counting comparisons
#                   (|{v : Votes(x, v)}| > |{v : Votes(y, v)}|). Set cardinality is
#                   a second-order notion, so it has NO first-order export.
#   * Contrast    — a concessive connective (whereas / although / but) that is
#                   truth-functionally ∧, but kept as a distinct node so the
#                   concession survives translation instead of flattening to ∧.
#
# Count and Cardinality BIND their variable, so the binder-aware passes in
# _msfl_nodes.py (free_variables / substitute / resolve_lambda_scope) special-case
# them alongside Quantifier, and the renderers special-case Count / Measure /
# Cardinality (binders/terms are not regular operators). Contrast IS a regular
# level2 operator and is driven entirely by the operator registry — it needs no
# renderer branch and no binder handling.

# op code -> the ∃-prefixed surface glyph (and its inverse, used by the parser).
_COUNT_OPS = {"ge": "∃≥", "le": "∃≤", "eq": "∃="}
_COUNT_TOKEN_TO_OP = {glyph: op for op, glyph in _COUNT_OPS.items()}

# Largest witness count Count._expand() will materialise. The distinct-witnesses
# encoding is O(n²) constraints under n nested quantifiers, so a large n produces a
# tree that is both huge and deeper than Python's recursion limit; the Count node
# itself keeps n symbolically and round-trips for ANY n, so only the to_z3 / to_prover9
# / to_tptp *expansion* is bounded.
_COUNT_EXPAND_MAX = 500
_COUNT_TOO_LARGE = (
    "Count.to_z3/to_prover9/to_tptp: n={n} is too large to expand to first-order "
    "(the distinct-witnesses encoding materialises O(n²) constraints under n nested "
    "quantifiers; the limit is n<={limit}). The Count node keeps n symbolically and "
    "round-trips via to_unicode_str / to_dict for any n — only this first-order "
    "lowering is bounded."
)


def _balanced_and(parts):
    """Fold a non-empty list of formulas into a *balanced* And tree (shallow depth).

    A left-associative fold would make an n-element conjunction n deep, so an
    O(n²)-conjunct counting expansion overflows Python's recursion limit on
    traversal; a balanced tree is only O(log n) deep.
    """
    while len(parts) > 1:
        merged = [And(parts[i], parts[i + 1]) for i in range(0, len(parts) - 1, 2)]
        if len(parts) % 2:
            merged.append(parts[-1])
        parts = merged
    return parts[0]


@dataclass(frozen=True)
class Count(Node):
    """A counting (cardinality) quantifier ∃≥n / ∃≤n / ∃=n over a single variable.

    ``op`` is ``"ge"`` / ``"le"`` / ``"eq"`` (at least / at most / exactly); ``n``
    is a :class:`Number` wrapping a non-negative integer bound — kept SYMBOLIC, not
    expanded into single-letter variables, so an arbitrarily large bound (e.g. 500)
    is represented exactly. ``variable`` is the bound counting variable and
    ``formula`` its matrix. Semantics: ``∃≥n x φ`` is true iff at least ``n``
    DISTINCT individuals satisfy ``φ`` (``∃≤n`` at most, ``∃=n`` exactly). The
    counting quantifier is first-order expressible; :meth:`to_z3` / :meth:`to_prover9`
    / :meth:`to_tptp` lower it to the standard distinct-witnesses encoding (see
    :meth:`_expand`).
    """

    op: str
    n: Number
    variable: Variable
    formula: Node

    def __post_init__(self):
        """Validate the op code and that n is a non-negative integer Number."""
        if self.op not in _COUNT_OPS:
            raise ValueError(
                f"Count: unknown op {self.op!r}; expected one of 'ge', 'le', 'eq'.")
        if not (isinstance(self.n, Number) and isinstance(self.n.value, int)
                and self.n.value >= 0):
            raise ValueError(
                "Count: n must be a Number wrapping a non-negative integer.")

    def _tree_parts(self):
        """Return the ∃≥n / ∃≤n / ∃=n label (with the bound variable) and the matrix."""
        return (f"{_COUNT_OPS[self.op]}{self.n.value} {self.variable.name}",
                [self.formula])

    def to_dict(self):
        """Serialise to dict with op, n, bound variable, and serialised matrix."""
        return {"_type": "Count", "op": self.op, "n": self.n.to_dict(),
                "variable": self.variable.to_dict(),
                "formula": self.formula.to_dict()}

    @staticmethod
    def from_dict(d):
        """Deserialise a Count from a dict produced by to_dict."""
        return Count(d["op"], Node.from_dict(d["n"]),
                     Node.from_dict(d["variable"]), Node.from_dict(d["formula"]))

    def _expand(self) -> "Node":
        """Lower to plain FOL via the standard distinct-witnesses counting encoding.

        ``∃≥m x φ`` becomes ``∃x_0 … ∃x_{m-1} (⋀ φ[x_i] ∧ ⋀_{i<j} x_i ≠ x_j)``;
        ``∃≤n`` is ``¬(∃≥n+1)``; ``∃=n`` is ``∃≥n ∧ ¬(∃≥n+1)``. Fresh witness
        variables are chosen to avoid the matrix's free variables, and the bound
        variable is substituted out capture-avoidingly, so the result is a closed,
        meaning-preserving classical formula.
        """
        from ._msfl_nodes import substitute, free_variables  # lazy: avoid import cycle
        if self.n.value > _COUNT_EXPAND_MAX:
            raise NotImplementedError(
                _COUNT_TOO_LARGE.format(n=self.n.value, limit=_COUNT_EXPAND_MAX))
        var, phi = self.variable, self.formula
        avoid = {v.name for v in free_variables(phi)} | {var.name}

        def fresh(k):
            """Return k fresh Variables not clashing with the matrix or each other."""
            out, i = [], 0
            while len(out) < k:
                cand = f"{var.name}_{i}"
                if cand not in avoid:
                    out.append(Variable(cand))
                    avoid.add(cand)
                i += 1
            return out

        def at_least(m):
            """Build the plain-FOL 'at least m distinct φ' formula."""
            if m <= 0:
                # '≥ 0' is vacuously true: ∃x (φ ∨ ¬φ), valid on a non-empty domain.
                w = fresh(1)[0]
                g = substitute(phi, var, w)
                return Quantifier("∃", w, Or(g, Not(g)))
            ws = fresh(m)
            conjuncts = [substitute(phi, var, w) for w in ws]
            conjuncts += [Atom("≠", [ws[i], ws[j]])
                          for i in range(m) for j in range(i + 1, m)]
            body = _balanced_and(conjuncts)        # balanced ⇒ shallow recursion
            for w in reversed(ws):
                body = Quantifier("∃", w, body)
            return body

        if self.op == "ge":
            return at_least(self.n.value)
        if self.op == "le":
            return Not(at_least(self.n.value + 1))
        return And(at_least(self.n.value), Not(at_least(self.n.value + 1)))

    def to_z3(self, env: Z3Env = None):
        """Lower to the distinct-witnesses encoding, then translate to Z3."""
        return self._expand().to_z3(env)

    def to_prover9(self) -> str:
        """Lower to the distinct-witnesses encoding, then render Prover9 syntax."""
        return self._expand().to_prover9()

    def to_tptp(self) -> str:
        """Lower to the distinct-witnesses encoding, then render TPTP syntax."""
        return self._expand().to_tptp()


@dataclass(frozen=True)
class Measure(Node):
    """A degree/measure term μ(entity, dimension): the degree to which ``entity`` has
    the gradable dimension ``dimension``.

    A first-class measure-function term, the clean argument for bare (standard-less)
    quantity comparatives — ``more water`` / ``taller`` become ``μ(x, dim) > μ(y, dim)``
    rather than a thin relational ``More(x, c)``. Both children are terms. On export it
    is the uninterpreted binary function ``measure(entity, dimension)`` (the ``μ`` glyph
    is ASCII-folded to ``measure`` so the first-order back-ends accept it), and ``>`` / ``<``
    over the resulting degrees use the back-end's ordering.
    """

    entity: Node
    dimension: Node

    def _tree_parts(self):
        """Return the μ label and the entity/dimension children."""
        return "μ", [self.entity, self.dimension]

    def to_dict(self):
        """Serialise to dict with serialised entity and dimension terms."""
        return {"_type": "Measure", "entity": self.entity.to_dict(),
                "dimension": self.dimension.to_dict()}

    @staticmethod
    def from_dict(d):
        """Deserialise a Measure from a dict produced by to_dict."""
        return Measure(Node.from_dict(d["entity"]), Node.from_dict(d["dimension"]))

    def to_z3(self, env: Z3Env = None):
        """Translate to an uninterpreted binary Z3 function ``measure`` in sort S."""
        env = env or Z3Env()
        return env.get_func("measure", 2)(self.entity.to_z3(env), self.dimension.to_z3(env))

    def to_prover9(self) -> str:
        """Render as the Prover9 function ``measure(entity, dimension)``."""
        return f"measure({self.entity.to_prover9()}, {self.dimension.to_prover9()})"

    def to_tptp(self) -> str:
        """Render as the TPTP function ``measure(entity, dimension)``."""
        return f"measure({self.entity.to_tptp()},{self.dimension.to_tptp()})"


# Shared rejection message: a set-cardinality term is not first-order definable.
_NO_CARDINALITY_EXPORT = (
    "Cardinality terms (|{v : φ}|) denote set cardinality, a second-order notion "
    "with no first-order counterpart — counting comparisons such as 'more …​ than …' "
    "are not first-order definable. Keep the term at the AST level, or express a "
    "fixed-bound count with the Count quantifier (∃≥n / ∃≤n / ∃=n)."
)


@dataclass(frozen=True)
class Cardinality(Node):
    """A set-cardinality term |{v : φ}|: the number of individuals ``v`` satisfying ``φ``.

    The first-class ``|S|`` term behind faithful counting comparisons — ``more votes
    than`` becomes ``|{v : Votes(x, v)}| > |{v : Votes(y, v)}|``. It BINDS ``variable``
    over the matrix ``formula``. Set cardinality is genuinely second-order, so it has
    no first-order export: :meth:`to_z3` / :meth:`to_prover9` / :meth:`to_tptp` reject.
    """

    variable: Variable
    formula: Node

    def _tree_parts(self):
        """Return the |v| cardinality label (with the bound variable) and the matrix."""
        return f"|{self.variable.name}|", [self.formula]

    def to_dict(self):
        """Serialise to dict with the bound variable and serialised matrix."""
        return {"_type": "Cardinality", "variable": self.variable.to_dict(),
                "formula": self.formula.to_dict()}

    @staticmethod
    def from_dict(d):
        """Deserialise a Cardinality from a dict produced by to_dict."""
        return Cardinality(Node.from_dict(d["variable"]), Node.from_dict(d["formula"]))

    def to_z3(self, env: Z3Env = None):
        """Reject Z3 export: set cardinality has no first-order counterpart."""
        raise NotImplementedError(_NO_CARDINALITY_EXPORT)

    def to_prover9(self) -> str:
        """Reject Prover9 export: set cardinality has no first-order counterpart."""
        raise NotImplementedError(_NO_CARDINALITY_EXPORT)

    def to_tptp(self) -> str:
        """Reject TPTP export: set cardinality has no first-order counterpart."""
        raise NotImplementedError(_NO_CARDINALITY_EXPORT)


@dataclass(frozen=True)
class Contrast(Node):
    """A concessive (contrastive) connective ``P Ⓒ Q`` — whereas / although / but.

    Truth-functionally identical to classical conjunction (concession is a discourse
    relation, not a truth-functional one), but kept as a distinct node so a front-end
    can preserve the contrast rather than flattening it to ∧. Exports therefore behave
    exactly like :class:`And`.
    """

    left: Node
    right: Node

    def to_dict(self):
        """Serialise to dict with type tag and recursively serialised operands."""
        return {"_type": "Contrast", "left": self.left.to_dict(), "right": self.right.to_dict()}

    @staticmethod
    def from_dict(d):
        """Deserialise a Contrast from a dict produced by to_dict."""
        return Contrast(Node.from_dict(d["left"]), Node.from_dict(d["right"]))

    def to_z3(self, env: Z3Env = None):
        """Translate like And (concession is truth-functionally conjunction)."""
        env = env or Z3Env()
        return z3.And(self.left.to_z3(env), self.right.to_z3(env))

    def to_prover9(self) -> str:
        """Render like And, using the Prover9 ampersand operator."""
        return f"({self.left.to_prover9()} & {self.right.to_prover9()})"

    def to_tptp(self) -> str:
        """Render like And, using the TPTP ampersand operator."""
        return f"({self.left.to_tptp()} & {self.right.to_tptp()})"


# =========================
# Registry
# =========================

NODE_CLASSES = {
    "Variable": Variable, "Constant": Constant, "Number": Number,
    "Function": Function, "Atom": Atom, "Not": Not, "And": And,
    "Or": Or, "Xor": Xor, "Implies": Implies, "Iff": Iff,
    "Quantifier": Quantifier,
    "Count": Count, "Measure": Measure, "Cardinality": Cardinality,
}


# =========================
# Operator registry (self-registration)
# =========================
#
# A formula operator (a connective/modal that the precedence-driven renderers in
# _msfl_nodes.py format) registers ONE OperatorSpec here next to its class
# definition. The renderers then drive every regular operator from this registry,
# so adding an operator no longer means editing the central rendering tables.
#
# Each spec records, byte-for-byte, what the renderer emits:
#   - unicode: the glyph or prefix string for to_unicode_str (e.g. '¬', '□', 'K_').
#   - latex:   the LaTeX markup for to_latex, including any trailing space that
#              the current renderer emits (e.g. '\\lnot ', '\\Box ', 'K').
#   - fixity:  how the renderer arranges the operand(s) and the glyph.
#   - precedence: the formula precedence (higher binds tighter): 4 for prefix /
#              agent_prefix, 1 for binary_iff, 2 for binary_implies, 2.5 for
#              binary_until, 3 for level2.
#
# The "binders" (Quantifier, SortedQuantifier, SecondOrderQuantifier), Lambda and
# Application keep their explicit handling in the renderers and a small static
# precedence table — they are NOT regular operators and do NOT register here.

_VALID_FIXITIES = frozenset({
    "prefix", "agent_prefix",
    "binary_iff", "binary_implies", "binary_until",
    "level2",
})


@dataclass(frozen=True)
class OperatorSpec:
    """A renderer-facing description of one formula operator.

    name is the node class ``__name__`` (the renderers dispatch by class name).
    fixity is one of 'prefix', 'agent_prefix', 'binary_iff', 'binary_implies',
    'binary_until', 'level2'. unicode/latex are the EXACT strings the
    to_unicode_str / to_latex renderers emit for the operator's glyph or prefix
    (latex includes any trailing space). precedence is the formula precedence
    used for parenthesisation (a float; .5 values let an operator sit between two
    integer levels, as Until does at 2.5).
    """

    name: str
    fixity: str
    unicode: str
    latex: str
    precedence: float


# name -> OperatorSpec. Populated by register_operator as each node module is
# imported. The renderers in _msfl_nodes.py read this dict directly.
OPERATORS: Dict[str, OperatorSpec] = {}


def register_operator(node_class, fixity: str, unicode: str, latex: str,
                      precedence: float) -> OperatorSpec:
    """Register ``node_class`` as a renderable formula operator.

    Records an OperatorSpec under ``node_class.__name__`` in OPERATORS and adds
    the class to NODE_CLASSES (so from_dict/serialisation see it too). Safe to
    call more than once for the same class — the latest call overwrites the
    previous spec (idempotent / overwrite-safe). Returns the stored OperatorSpec.

    A node registered here is driven entirely by the central renderers via its
    spec, so no edit to _msfl_nodes.py is needed to render a new operator.
    """
    if fixity not in _VALID_FIXITIES:
        raise ValueError(
            f"register_operator: unknown fixity {fixity!r}; "
            f"expected one of {sorted(_VALID_FIXITIES)}"
        )
    name = node_class.__name__
    spec = OperatorSpec(name, fixity, unicode, latex, float(precedence))
    OPERATORS[name] = spec
    NODE_CLASSES[name] = node_class
    return spec


# Register the classical operators next to their class definitions above.
register_operator(Not, "prefix", "¬", "\\lnot ", 4)
register_operator(And, "level2", "∧", "\\land", 3)
register_operator(Or, "level2", "∨", "\\lor", 3)
register_operator(Xor, "level2", "⊕", "\\oplus", 3)
register_operator(Implies, "binary_implies", "→", "\\rightarrow", 2)
register_operator(Iff, "binary_iff", "↔", "\\leftrightarrow", 1)


# =========================
# Parser registry (self-assembling grammar)
# =========================
#
# A SECOND, parser-facing registry sits alongside the renderer registry above.
# Where OperatorSpec records how a node is *rendered*, ParserOp records how an
# operator is *parsed*: which grammar mode it belongs to, which precedence level
# it slots into, the grammar fragment it contributes, and the transform that
# turns the matched tokens into a Node. MSFLParser reads this registry per mode
# to build BOTH the Lark grammar string and the Transformer — so adding an
# operator is a registry entry in the operator's own module, with no edit to
# msflparser.py or the grammar skeleton.
#
# The same glyph maps to different nodes in different modes (∧ → And in FOL but
# WeakConjunction in MSFL), so registration is PER (mode, operator): a node may
# register several ParserOps, one per mode it appears in.
#
# Levels mirror the grammar's precedence layering (loosest first):
#   biimplication  the right-assoc ↔ rule              (one op per mode)
#   implication    the right-assoc → rule              (one op per mode)
#   until          the right-assoc Ⓤ rule (modal only) (one op per mode)
#   level2         the no-mixing same-level group ∧∨⊕⊗ (one only_X rule each)
#   prefix         ¬ and the prefix modal/temporal ops (the prefix rule's alts)
#   quantifier     ∀/∃ over a variable or predicate    (the quantifier alts)
#
# The shared term/atom/lambda/application layer is NOT registry-driven; it lives
# verbatim in the base template, identical across every mode (the only term-layer
# variation, sorted vs. plain constants, is selected by the SORTED flag below).

_VALID_PARSE_LEVELS = frozenset({
    "prefix", "level2", "implication", "biimplication", "until", "quantifier",
})

_VALID_MODES = frozenset({"fol", "msfol", "msfl", "fl", "modal", "second_order",
                          "dependence", "linear", "lambek"})


@dataclass(frozen=True)
class ParserOp:
    """A parser-facing description of how one operator is parsed in one mode.

    mode      : the grammar mode this binding applies to (one of _VALID_MODES).
    level     : the precedence level it slots into (one of _VALID_PARSE_LEVELS).
    terminal_name : name of a named terminal to declare, or "" if the operator
                uses an inline string literal (the common case for the glyph
                connectives — kept inline so the error-path terminal patterns
                match the legacy grammars byte-for-byte).
    terminal_def  : the full terminal declaration line (e.g. 'BOX: "□"' or
                'KNOWS.5: /K_.../'), or "" when terminal_name is "".
    grammar  : the right-hand side of the grammar alternative this op contributes,
                already referencing the shared rule names (e.g. '"¬" prefix',
                'BOX prefix', or '(FORALL | EXISTS) VARIABLE prefix'). For a
                level2 op this is instead the glyph literal (e.g. '"∧"'), since
                level2 ops are spliced into the generated only_X / same_level_ops
                rules rather than contributing a free-standing alternative.
    rule_alias : the Lark rule alias (-> rule_alias) that names the parse node;
                the matching transform is attached to the assembled Transformer
                under this same name.
    transform  : function(items) -> Node implementing the alias's handler.
    node_class : the Node subclass produced (recorded for introspection/tests).
    only_name  : for level2 ops only, the generated only_X rule name (e.g.
                "only_and"); "" for every other level.
    """

    mode: str
    level: str
    terminal_name: str
    terminal_def: str
    grammar: str
    rule_alias: str
    transform: object
    node_class: object
    only_name: str = ""


# Append-only list of every parser binding, populated by register_parser_op as
# each node module imports. MSFLParser filters it by mode at construction time.
PARSER_OPS: List[ParserOp] = []


def register_parser_op(node_class, mode: str, level: str, rule_alias: str,
                       grammar: str, transform, *,
                       terminal_name: str = "", terminal_def: str = "",
                       only_name: str = "") -> ParserOp:
    """Register one parser binding for ``node_class`` in grammar mode ``mode``.

    Appends a ParserOp to PARSER_OPS. ``transform(items) -> Node`` is the handler
    Lark calls for the ``rule_alias`` reduction; ``grammar`` is the alternative's
    right-hand side (or, for a level2 op, the bare glyph literal). Named terminals
    are declared via ``terminal_name``/``terminal_def``; inline string operators
    leave both empty. Returns the stored ParserOp.

    This is additive to register_operator (which handles rendering): a fully
    self-describing operator calls both — register_operator for the renderers,
    register_parser_op (once per mode) for the parser.
    """
    if mode not in _VALID_MODES:
        raise ValueError(
            f"register_parser_op: unknown mode {mode!r}; "
            f"expected one of {sorted(_VALID_MODES)}"
        )
    if level not in _VALID_PARSE_LEVELS:
        raise ValueError(
            f"register_parser_op: unknown level {level!r}; "
            f"expected one of {sorted(_VALID_PARSE_LEVELS)}"
        )
    op = ParserOp(mode, level, terminal_name, terminal_def, grammar,
                  rule_alias, transform, node_class, only_name)
    PARSER_OPS.append(op)
    return op


def parser_ops_for_mode(mode: str) -> List[ParserOp]:
    """Return every registered ParserOp whose mode matches ``mode`` (in order)."""
    return [op for op in PARSER_OPS if op.mode == mode]


# ---------------------------------------------------------------------------
# Base grammar template
# ---------------------------------------------------------------------------
#
# ONE skeleton shared by every mode. The %%MARKERS%% are filled by
# build_grammar() from the mode's ParserOps. The structure: right-assoc ↔ and →,
# the optional Until sub-level, the no-mixing only_X same_level_ops group, the
# prefix level
# (¬ plus any prefix modal ops, then quantifier / atom / grouping), the tight
# quantifier binding (body is the prefix level), and the verbatim
# term/atom/lambda/application layer.
#
# Normalised internal rule names: the legacy grammars used negation /
# luk_negation / modal for the prefix level and biimplication / luk_biimplication
# (etc.) for the binary levels; because Lark inlines ?-rules and only the ->
# aliases name tree nodes, these internal names are irrelevant to the produced
# AST, so the template uses single uniform names (prefix, biimplication,
# implication, until, same_level_ops). The %%...%% markers:
#   %%TERMINAL_IMPORTS%%  the (...) list imported from .terminals
#   %%TERMINAL_DEFS%%     extra named-terminal declarations (modal ops)
#   %%BIIMPL_OPS%%        the ↔ alternative(s)
#   %%IMPL_OPS%%          the → alternative(s)
#   %%IMPL_BODY%%         rule the → level reduces to: "until" or "same_level_ops"
#   %%UNTIL_BLOCK%%       the whole until rule (modal) or empty
#   %%LEVEL2_ALTS%%       the same_level_ops alternation members (only_X | … )
#   %%ONLY_RULES%%        the only_X rule definitions
#   %%PREFIX_OPS%%        the prefix alternatives contributed by ops (¬, modal …)
#   %%QUANT_OPS%%         the quantifier alternative(s)
#   %%CONST_ALTS%%        the atom_term constant rules (plain vs. sorted)

_BASE_GRAMMAR_TEMPLATE = '''\
%import .terminals (%%TERMINAL_IMPORTS%%)
%import common.WS
%%TERMINAL_DEFS%%
?start: formula

?formula: biimplication
    | lambda_
    | application_

?biimplication: implication
%%BIIMPL_OPS%%

?implication: %%IMPL_BODY%%
%%IMPL_OPS%%
%%UNTIL_BLOCK%%
?same_level_ops: %%LEVEL2_ALTS%%
%%ONLY_RULES%%
?prefix: %%PREFIX_OPS%%
    | quantifier
    | atom
    | "(" formula ")"
    | "[" formula "]"

?quantifier: %%QUANT_OPS%%

?atom: infix_predicate
     | PREDICATE "(" termlist ")"           -> atom_
     | PREDICATE                            -> atom0_

?infix_predicate: term "<"  term            -> lt_
                | term ">"  term            -> gt_
                | term "="  term            -> eq_
                | term "≤" term            -> le_
                | term "≥" term            -> ge_
                | term "≠" term            -> ne_

?termlist: term ("," term)*

?term: sum

?sum: product
    | sum "+" product                       -> add_
    | sum "-" product                       -> sub_

?product: atom_term
    | product "*" atom_term                 -> mul_
    | product "/" atom_term                 -> div_

?atom_term: VARIABLE
    | NAME "(" termlist ")"                 -> function_
%%CONST_ALTS%%
    | NUMBER                                -> number_
%%TERM_EXTRA%%
    | "(" term ")"

lambda_: LAMBDA (VARIABLE | NAME | PREDICATE) "." formula
?app_arg: formula | atom_term
application_: "(" formula ")" "(" app_arg ")"

%ignore WS
'''


# The two constant-handling variants for the atom_term layer. Plain (FOL / FL /
# modal / second-order) treats a bare NAME as a Constant and c_-constants via
# const_; sorted (MSFOL / MSFL) requires a SORT annotation on each.
_CONST_ALTS_PLAIN = (
    "    | NAME\n"
    "    | CONSTANT                              -> const_"
)
_CONST_ALTS_SORTED = (
    "    | NAME SORT                             -> sorted_const_\n"
    "    | CONSTANT SORT                         -> sorted_const_"
)


# Per-mode grammar configuration that is NOT operator-specific: the terminal
# import list and whether constants are sorted. (The operators themselves come
# from the registry.)
_MODE_TERMINAL_IMPORTS = {
    "fol":   "PREDICATE, CONSTANT, NAME, VARIABLE, NUMBER, FORALL, EXISTS, LAMBDA",
    "msfol": "PREDICATE, CONSTANT, NAME, VARIABLE, NUMBER, SORT, FORALL, EXISTS, LAMBDA",
    "msfl":  "PREDICATE, CONSTANT, NAME, VARIABLE, NUMBER, SORT, FORALL, EXISTS, LAMBDA",
    "fl":    "PREDICATE, CONSTANT, NAME, VARIABLE, NUMBER, FORALL, EXISTS, LAMBDA",
    "modal": "PREDICATE, CONSTANT, NAME, VARIABLE, NUMBER, FORALL, EXISTS, LAMBDA",
    "second_order": "PREDICATE, CONSTANT, NAME, VARIABLE, NUMBER, FORALL, EXISTS, LAMBDA",
    "dependence": "PREDICATE, CONSTANT, NAME, VARIABLE, NUMBER, FORALL, EXISTS, LAMBDA",
    "linear": "PREDICATE, CONSTANT, NAME, VARIABLE, NUMBER, FORALL, EXISTS, LAMBDA",
    "lambek": "PREDICATE, CONSTANT, NAME, VARIABLE, NUMBER, FORALL, EXISTS, LAMBDA",
}

_SORTED_MODES = frozenset({"msfol", "msfl"})


# Per-mode atom_term extensions that are NOT registry-driven (the term layer is the
# one hand-written part of the template). The classical unsorted modes (fol, modal,
# second_order) gain the measure term μ(entity, dimension) and the set-cardinality
# term |{v : φ}|; the matching FOLTransformer.measure_ / .cardinality_ handlers
# (base-class methods, so available in every mode) turn them into Measure /
# Cardinality nodes. All three share the plain (unsorted) term layer, so the same
# fragment applies verbatim; modal / second-order are included so a measure or
# cardinality term can appear under their operators (e.g. ◇(μ(x, height) > μ(y,
# height)) or ∃P (|{v : P(v)}| > c)). The SORTED modes msfol/msfl are absent because
# the |{v : φ}| binder would need a sort annotation; a mode absent from this map
# gets no extra term form.
_TERM_EXTRA_CLASSICAL = (
    '    | "μ" "(" termlist ")"                  -> measure_\n'
    '    | "|" "{" VARIABLE ":" formula "}" "|"  -> cardinality_'
)
# Sorted variant (MSFOL): the measure term is unchanged (its args are the mode's
# termlist), but the cardinality binder carries a sort annotation on the bound
# variable — |{v:Sort : φ}| → SortedCardinality — to stay consistent with MSFOL's
# rule that every binder is sorted.
_TERM_EXTRA_SORTED = (
    '    | "μ" "(" termlist ")"                       -> measure_\n'
    '    | "|" "{" VARIABLE SORT ":" formula "}" "|"  -> sorted_cardinality_'
)
_MODE_TERM_EXTRA = {
    "fol": _TERM_EXTRA_CLASSICAL,
    "modal": _TERM_EXTRA_CLASSICAL,
    "second_order": _TERM_EXTRA_CLASSICAL,
    "msfol": _TERM_EXTRA_SORTED,
}


def build_grammar(mode: str) -> str:
    """Assemble the Lark grammar STRING for ``mode`` from the registry + template.

    Splices the mode's ParserOps into the base template's markers, preserving the
    exact precedence structure of the legacy hand-written grammar for that mode.
    Pure string assembly: no Lark object is built here (MSFLParser does that).
    """
    # Handler-only ops (empty grammar, e.g. sorted_const_ whose alternative lives
    # in the template's CONST_ALTS block) contribute a transform but no grammar
    # alternative, so they are excluded from every grammar-fragment join below.
    ops = [op for op in parser_ops_for_mode(mode) if op.grammar]

    # --- named-terminal declarations (modal operators; dedup, preserve order) ---
    seen_terms = set()
    term_defs = []
    for op in ops:
        if op.terminal_def and op.terminal_name not in seen_terms:
            seen_terms.add(op.terminal_name)
            term_defs.append(op.terminal_def)
    terminal_defs = ("\n".join(term_defs) + "\n") if term_defs else ""

    # --- until sub-level (modal only) ----------------------------------------
    # Determined first because it sets the implication body rule. ``op.grammar``
    # for an until op is just the operator glyph (literal or named terminal).
    until = [op for op in ops if op.level == "until"]
    if until:
        impl_body = "until"
        until_alts = "\n".join(
            f"    | same_level_ops {op.grammar} until            -> {op.rule_alias}"
            for op in until
        )
        until_block = f"\n?until: same_level_ops\n{until_alts}\n"
    else:
        impl_body = "same_level_ops"
        until_block = ""

    # --- biimplication (↔) — right-assoc; ``op.grammar`` is just the glyph ----
    biimpl = [op for op in ops if op.level == "biimplication"]
    biimpl_ops = "\n".join(
        f"    | implication {op.grammar} biimplication         -> {op.rule_alias}"
        for op in biimpl
    )

    # --- implication (→) — right-assoc; left operand is the implication body --
    impl = [op for op in ops if op.level == "implication"]
    impl_ops = "\n".join(
        f"    | {impl_body} {op.grammar} implication        -> {op.rule_alias}"
        for op in impl
    )

    # --- level2 (the no-mixing same_level_ops group) -------------------------
    level2 = [op for op in ops if op.level == "level2"]
    only_members = " | ".join(op.only_name for op in level2)
    level2_alts = f"{only_members} | prefix" if only_members else "prefix"
    only_rules = "\n".join(
        f"?{op.only_name}: prefix ({op.grammar} prefix)+         -> {op.rule_alias}"
        for op in level2
    )

    # --- prefix level (¬ and any prefix modal/temporal ops) ------------------
    prefix = [op for op in ops if op.level == "prefix"]
    prefix_ops = "\n    | ".join(f"{op.grammar}                     -> {op.rule_alias}" for op in prefix)

    # --- quantifier ----------------------------------------------------------
    quant = [op for op in ops if op.level == "quantifier"]
    quant_ops = "\n    | ".join(f"{op.grammar}   -> {op.rule_alias}" for op in quant)

    # --- term-layer constant handling ----------------------------------------
    const_alts = _CONST_ALTS_SORTED if mode in _SORTED_MODES else _CONST_ALTS_PLAIN

    # --- term-layer extensions (measure / cardinality; non-registry) ---------
    term_extra = _MODE_TERM_EXTRA.get(mode, "")

    grammar = _BASE_GRAMMAR_TEMPLATE
    grammar = grammar.replace("%%TERMINAL_IMPORTS%%", _MODE_TERMINAL_IMPORTS[mode])
    grammar = grammar.replace("%%TERMINAL_DEFS%%\n", terminal_defs)
    grammar = grammar.replace("%%BIIMPL_OPS%%", biimpl_ops)
    grammar = grammar.replace("%%IMPL_BODY%%", impl_body)
    grammar = grammar.replace("%%IMPL_OPS%%", impl_ops)
    grammar = grammar.replace("%%UNTIL_BLOCK%%\n", until_block)
    grammar = grammar.replace("%%LEVEL2_ALTS%%", level2_alts)
    grammar = grammar.replace("%%ONLY_RULES%%\n", (only_rules + "\n") if only_rules else "")
    # A mode may register NO quantifier ops (linear, lambek — propositional) or
    # NO prefix ops. Lark rejects a rule with an empty right-hand side, so the
    # empty level is excised from the template rather than left dangling: the
    # `| quantifier` alternative and the ?quantifier rule disappear together,
    # and an empty prefix level promotes the next alternative into first place.
    if not quant:
        grammar = grammar.replace("\n    | quantifier", "")
        grammar = grammar.replace("\n?quantifier: %%QUANT_OPS%%\n", "\n")
    if prefix_ops:
        grammar = grammar.replace("%%PREFIX_OPS%%", prefix_ops)
    else:
        grammar = grammar.replace("%%PREFIX_OPS%%\n    | ", "")
    grammar = grammar.replace("%%QUANT_OPS%%", quant_ops)
    grammar = grammar.replace("%%CONST_ALTS%%", const_alts)
    grammar = grammar.replace("%%TERM_EXTRA%%\n", (term_extra + "\n") if term_extra else "")
    return grammar


def build_transform_handlers(mode: str) -> Dict[str, object]:
    """Return ``{rule_alias: transform}`` for every ParserOp in ``mode``.

    MSFLParser attaches these to the assembled Transformer so each operator's
    parse handler lives next to its node definition, not in a hand-written
    Transformer subclass.
    """
    return {op.rule_alias: op.transform for op in parser_ops_for_mode(mode)}


# =========================
# Transformer
# =========================

class FOLTransformer(Transformer):
    """Transforms parsed tokens from Lark parser into AST nodes."""

    @staticmethod
    def _fold_binary(items, node_cls):
        """Left-fold a variable-length item list into nested binary nodes."""
        node = items[0]
        for item in items[1:]:
            node = node_cls(node, item)
        return node

    def atom0_(self, items):
        """Transform bare predicate symbol into a zero-arity Atom node."""
        pred = str(items[0])
        return Atom(pred, [])

    def VARIABLE(self, items):
        """Transform variable token into Variable node."""
        return Variable(str(items))

    def NAME(self, items):
        """Transform name token into Constant node."""
        return Constant(str(items))

    def const_(self, items):
        """Transform c_-prefixed constant token into Constant node."""
        return Constant(str(items[0]))

    def number_(self, items):
        """Transform numeric literal token into Number node."""
        text = str(items[0])
        value = float(text) if "." in text else int(text)
        return Number(value)

    def function_(self, items):
        """Transform function application into Function node."""
        head = items[0]
        name = head.name if isinstance(head, Constant) else str(head)
        args = items[1:]
        if args and isinstance(args[0], list):
            args = args[0]
        return Function(name, args)

    def add_(self, items):
        """Transform addition into Function node."""
        left, right = items
        return Function("+", [left, right])

    def sub_(self, items):
        """Transform subtraction into Function node."""
        left, right = items
        return Function("-", [left, right])

    def mul_(self, items):
        """Transform multiplication into Function node."""
        left, right = items
        return Function("*", [left, right])

    def div_(self, items):
        """Transform division into Function node."""
        left, right = items
        return Function("/", [left, right])

    def atom_term(self, items):
        """Pass through atom term."""
        return items[0]

    def term(self, items):
        """Pass through term."""
        return items[0]

    def sum(self, items):
        """Pass through sum expression."""
        return items[0]

    def product(self, items):
        """Pass through product expression."""
        return items[0]

    def termlist(self, items):
        """Transform term list."""
        return items

    def infix_predicate(self, items):
        """Pass through infix predicate."""
        return items[0]

    def atom(self, items):
        """Pass through atom."""
        return items[0]

    def atom_(self, items):
        """Transform predicate application into Atom node."""
        pred = str(items[0])
        if not isinstance(items[1], list):
            args = [items[1]]
        else:
            args = items[1]
        return Atom(pred, args)

    def lt_(self, items):
        """Transform less-than comparison into Atom node."""
        left, right = items
        return Atom("<", [left, right])

    def gt_(self, items):
        """Transform greater-than comparison into Atom node."""
        left, right = items
        return Atom(">", [left, right])

    def eq_(self, items):
        """Transform equality comparison into Atom node."""
        left, right = items
        return Atom("=", [left, right])

    def le_(self, items):
        """Transform less-than-or-equal comparison into Atom node."""
        left, right = items
        return Atom("≤", [left, right])

    def ge_(self, items):
        """Transform greater-than-or-equal comparison into Atom node."""
        left, right = items
        return Atom("≥", [left, right])

    def ne_(self, items):
        """Transform not-equal comparison into Atom node."""
        left, right = items
        return Atom("≠", [left, right])

    def not_(self, items):
        """Transform negation into Not node."""
        return Not(items[0])

    def and_(self, items):
        """Transform conjunction into And node."""
        return self._fold_binary(items, And)

    def or_(self, items):
        """Transform disjunction into Or node."""
        return self._fold_binary(items, Or)

    def xor_(self, items):
        """Transform exclusive or into Xor node."""
        return self._fold_binary(items, Xor)

    def implies_(self, items):
        """Transform implication into Implies node."""
        return Implies(items[0], items[1])

    def iff_(self, items):
        """Transform biconditional into Iff node."""
        return Iff(items[0], items[1])

    def quantifier_(self, items):
        """Transform quantifier expression into Quantifier node."""
        quant = items[0]
        var = items[1]
        formula = items[2]
        return Quantifier(str(quant), var, formula)

    def measure_(self, items):
        """Transform μ(entity, dimension) into a Measure term node (exactly 2 args)."""
        args = items[0] if items and isinstance(items[0], list) else list(items)
        if len(args) != 2:
            raise ValueError(
                f"μ(...) takes exactly two arguments (entity, dimension); got {len(args)}.")
        return Measure(args[0], args[1])

    def cardinality_(self, items):
        """Transform |{v : φ}| into a Cardinality term node binding v over φ."""
        return Cardinality(items[0], items[1])


# =========================
# Parser registration (FOL / MSFOL connectives + quantifier)
# =========================
#
# Self-register the classical connectives and the unsorted quantifier with the
# parser registry. Each transform mirrors the corresponding FOLTransformer method
# exactly (same items[…] handling, same node), so the assembled parser produces
# byte-identical ASTs. The connectives shared by FOL and MSFOL (∧ ∨ ¬ → ↔) and
# the quantifier register once per mode they appear in; FOL additionally has ⊕
# (Xor). The sorted quantifier and the Łukasiewicz/MSFL bindings live in
# _msfl_nodes.py; the modal/second-order bindings in their own modules.

def _fold_binary(items, node_cls):
    """Left-fold a variable-length item list into nested binary nodes (registry copy)."""
    node = items[0]
    for item in items[1:]:
        node = node_cls(node, item)
    return node


# Classical ∧ ∨ ¬ → ↔ are shared by FOL, MSFOL, modal, and second-order modes;
# ⊕ (Xor) by every CLASSICAL mode — FOL, MSFOL, modal, and second-order (the glyph ⊕
# is the Łukasiewicz strong disjunction in the fuzzy modes, so Xor stays out of those).
# The unsorted quantifier is shared by FOL, modal, and second-order (the sorted modes
# use SortedQuantifier). Each connective registers once per mode with the SAME grammar
# fragment and transform, so the assembled parser produces byte-identical ASTs.
_CLASSICAL_MODES = ("fol", "msfol", "modal", "second_order")
_XOR_MODES = ("fol", "msfol", "modal", "second_order")
_UNSORTED_QUANT_MODES = ("fol", "modal", "second_order")


def _quantifier_transform(items):
    """Build an unsorted Quantifier from [FORALL/EXISTS token, Variable, body]."""
    return Quantifier(str(items[0]), items[1], items[2])


# --- prefix: ¬ (Not) ---
for _m in _CLASSICAL_MODES:
    register_parser_op(Not, _m, "prefix", "not_", '"¬" prefix',
                       lambda items: Not(items[0]))

# --- level2: ∧ ∨ (And, Or) everywhere classical; ⊕ (Xor) where allowed ---
for _m in _CLASSICAL_MODES:
    register_parser_op(And, _m, "level2", "and_", '"∧"',
                       lambda items: _fold_binary(items, And), only_name="only_and")
    register_parser_op(Or, _m, "level2", "or_", '"∨"',
                       lambda items: _fold_binary(items, Or), only_name="only_or")
for _m in _XOR_MODES:
    register_parser_op(Xor, _m, "level2", "xor_", '"⊕"',
                       lambda items: _fold_binary(items, Xor), only_name="only_xor")

# --- implication: → (Implies) ---
# For binary levels (implication / biimplication / until) the ``grammar`` field
# holds JUST the operator glyph; build_grammar assembles the full right-assoc
# rule from it (the operand rule names are fixed by the level structure). This
# lets the → rule's left operand follow the mode's implication body (same_level_ops
# normally, or until in modal mode) without a mode-specific fragment.
for _m in _CLASSICAL_MODES:
    register_parser_op(Implies, _m, "implication", "implies_", '"→"',
                       lambda items: Implies(items[0], items[1]))

# --- biimplication: ↔ (Iff) ---
for _m in _CLASSICAL_MODES:
    register_parser_op(Iff, _m, "biimplication", "iff_", '"↔"',
                       lambda items: Iff(items[0], items[1]))

# --- quantifier: unsorted ∀x / ∃x (Quantifier) ---
for _m in _UNSORTED_QUANT_MODES:
    register_parser_op(Quantifier, _m, "quantifier", "quantifier_",
                       "(FORALL | EXISTS) VARIABLE prefix", _quantifier_transform)


# Modes that accept the NL / CCG translation-target nodes (Count, Contrast, and —
# via _MODE_TERM_EXTRA below — the Measure / Cardinality terms). These are the
# CLASSICAL, UNSORTED modes — every mode that is a conservative extension of
# classical unsorted FOL and therefore reads the constructs with IDENTICAL
# semantics: plain fol, modal (fol + modal operators), and second-order (fol +
# quantifiers over predicate variables). A CCG-derived form routinely nests one of
# these fol-level constructs under a modal or second-order operator — e.g. "every
# professor believes at least three students will pass" is Believes_x(∃≥3 y …) —
# so registering the same grammar fragment + transform across the family lets the
# whole mixed formula parse (and round-trip) as a single string, not only as a
# hand-built AST. (The SORTED classical modes msfol/msfl need sort-annotated
# binders, and the fuzzy modes fl/msfl reinterpret the connectives and reject
# comparison atoms, so neither is included here.)
_NL_NODE_MODES = ("fol", "modal", "second_order")


# --- counting quantifier: ∃≥n / ∃≤n / ∃=n (Count), fol + modal modes ---
# COUNTOP is one named terminal matching all three glyphs (∃ followed by ≥/≤/=),
# at lexer priority 5 so it wins over EXISTS (∃) on the longer match; the matched
# glyph in items[0] selects the op code. The bound NUMBER must be an integer.
def _count_transform(items):
    """Build a Count from [COUNTOP glyph token, NUMBER token, Variable, body]."""
    op = _COUNT_TOKEN_TO_OP[str(items[0])]
    text = str(items[1])
    if "." in text:
        raise ValueError(
            f"counting quantifier bound must be an integer, got {text!r}.")
    return Count(op, Number(int(text)), items[2], items[3])


for _m in _NL_NODE_MODES:
    register_parser_op(Count, _m, "quantifier", "count_",
                       "COUNTOP NUMBER VARIABLE prefix", _count_transform,
                       terminal_name="COUNTOP", terminal_def="COUNTOP.5: /∃[≥≤=]/")


# --- concessive connective: P Ⓒ Q (Contrast) — every CLASSICAL mode ---
# A regular level2 operator (same precedence as ∧ ∨ ⊕): self-registers with the
# renderers and the parser, so no renderer branch is needed (it dispatches on
# spec.fixity == "level2"). Truth-functionally conjunction; kept distinct in the AST.
# Unlike the counting binder it needs no sort annotation, so it drops into the sorted
# MSFOL mode too — hence the classical-mode list rather than _NL_NODE_MODES.
_CONTRAST_MODES = ("fol", "modal", "second_order", "msfol")
register_operator(Contrast, "level2", "Ⓒ", "\\mathbin{\\mathsf{C}}", 3)
for _m in _CONTRAST_MODES:
    register_parser_op(Contrast, _m, "level2", "contrast_", '"Ⓒ"',
                       lambda items: _fold_binary(items, Contrast),
                       only_name="only_contrast")
