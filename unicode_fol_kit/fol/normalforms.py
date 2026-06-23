"""Classical-FOL normal forms: NNF, PNF, CNF, Skolemization, and a Horn check.

All entry points first call ``to_fol`` to eliminate sort annotations and
Łukasiewicz operators, so they accept FOL, MSFOL, MSFL, and FL inputs. Lambda
terms must be beta-reduced and lambda-eliminated first (``to_fol`` will raise
otherwise).

- ``to_nnf``  — negation normal form (eliminate → ↔ ⊕, push ¬ to atoms).
- ``to_pnf``  — prenex normal form (quantifier prefix + quantifier-free NNF
  matrix), with bound variables standardised apart. Equivalence-preserving.
- ``to_cnf``  — prenex form whose matrix is a conjunction of clauses.
  Equivalence-preserving.
- ``to_dnf``  — prenex form whose matrix is a disjunction of conjunctive
  clauses (the dual of ``to_cnf``). Equivalence-preserving.
- ``to_tseitin_cnf`` — EQUISATISFIABLE CNF of the matrix via the Tseitin /
  definitional encoding (fresh 0-ary auxiliary predicates); avoids the
  exponential blow-up of the distributive ``to_cnf``. NOT equivalence-preserving.
- ``skolemize`` — prenex NNF with existentials replaced by Skolem terms over
  the universals in scope; universal prefix retained. Satisfiability-preserving
  (NOT equivalence-preserving).
- ``is_horn`` — True iff the clausal form (skolemise → drop ∀ → CNF) consists of
  Horn clauses (each clause has at most one positive literal).
"""

from .nodes import (
    Node, Atom, Not, And, Or, Xor, Implies, Iff, Quantifier,
    Variable, Constant, Number, Function, to_fol,
)
from ._msfl_nodes import _rename

_FORALL = ("∀", "forall")
_EXISTS = ("∃", "exists")


# ---------------------------------------------------------------------------
# Negation normal form
# ---------------------------------------------------------------------------

def to_nnf(node: Node) -> Node:
    """Return the negation normal form of node (after reducing to classical FOL)."""
    return _nnf(to_fol(node))


def _nnf(n: Node) -> Node:
    if isinstance(n, Atom):
        return n
    if isinstance(n, Not):
        return _nnf_neg(n.formula)
    if isinstance(n, And):
        return And(_nnf(n.left), _nnf(n.right))
    if isinstance(n, Or):
        return Or(_nnf(n.left), _nnf(n.right))
    if isinstance(n, Implies):
        return Or(_nnf(Not(n.left)), _nnf(n.right))
    if isinstance(n, Iff):
        return And(_nnf(Implies(n.left, n.right)), _nnf(Implies(n.right, n.left)))
    if isinstance(n, Xor):
        return Or(And(_nnf(n.left), _nnf(Not(n.right))),
                  And(_nnf(Not(n.left)), _nnf(n.right)))
    if isinstance(n, Quantifier):
        return Quantifier(n.type, n.variable, _nnf(n.formula))
    raise TypeError(f"to_nnf: unexpected node type {type(n).__name__}")


def _nnf_neg(n: Node) -> Node:
    """Return the NNF of ¬n."""
    if isinstance(n, Atom):
        return Not(n)
    if isinstance(n, Not):
        return _nnf(n.formula)  # ¬¬a → a
    if isinstance(n, And):
        return Or(_nnf_neg(n.left), _nnf_neg(n.right))
    if isinstance(n, Or):
        return And(_nnf_neg(n.left), _nnf_neg(n.right))
    if isinstance(n, Implies):  # ¬(a → b) ≡ a ∧ ¬b
        return And(_nnf(n.left), _nnf_neg(n.right))
    if isinstance(n, Iff):  # ¬(a ↔ b) ≡ (a ∧ ¬b) ∨ (¬a ∧ b)
        return Or(And(_nnf(n.left), _nnf_neg(n.right)),
                  And(_nnf_neg(n.left), _nnf(n.right)))
    if isinstance(n, Xor):  # ¬(a ⊕ b) ≡ a ↔ b
        return _nnf(Iff(n.left, n.right))
    if isinstance(n, Quantifier):
        dual = "∃" if n.type in _FORALL else "∀"
        return Quantifier(dual, n.variable, _nnf_neg(n.formula))
    raise TypeError(f"to_nnf: unexpected node type {type(n).__name__}")


# ---------------------------------------------------------------------------
# Fresh-name plumbing
# ---------------------------------------------------------------------------

def _all_names(node: Node) -> set:
    """Collect every predicate, function, constant, and variable name in node."""
    names = set()
    for n in node.walk():
        cls = type(n).__name__
        if cls == "Atom":
            names.add(n.predicate)
        elif cls == "Function":
            names.add(n.name)
        elif cls in ("Variable", "Constant"):
            names.add(n.name)
    return names


def _gensym(base: str, counter: list, used: set) -> str:
    """Return a fresh name base+N not already in used; record it in used."""
    while True:
        name = f"{base}{counter[0]}"
        counter[0] += 1
        if name not in used:
            used.add(name)
            return name


# ---------------------------------------------------------------------------
# Prenex normal form
# ---------------------------------------------------------------------------

def to_pnf(node: Node) -> Node:
    """Return the prenex normal form: quantifier prefix over a quantifier-free
    NNF matrix, with all bound variables standardised apart."""
    nnf = _nnf(to_fol(node))
    std = _standardize(nnf, [0], _all_names(nnf))
    prefix, matrix = _prenex_split(std)
    for qtype, qvar in reversed(prefix):
        matrix = Quantifier(qtype, qvar, matrix)
    return matrix


def _standardize(n: Node, counter: list, used: set) -> Node:
    """Rename every bound variable to a globally unique fresh name."""
    if isinstance(n, Quantifier):
        fresh = Variable(_gensym("v", counter, used))
        body = _rename(n.formula, n.variable, fresh)
        return Quantifier(n.type, fresh, _standardize(body, counter, used))
    if isinstance(n, (And, Or)):
        return type(n)(_standardize(n.left, counter, used),
                       _standardize(n.right, counter, used))
    if isinstance(n, Not):
        return Not(_standardize(n.formula, counter, used))
    return n  # Atom


def _prenex_split(n: Node):
    """Split a standardised-apart NNF formula into (prefix, quantifier-free matrix).

    prefix is a list of (quantifier_type, Variable) in outer-to-inner order.
    Sound because bound variables are disjoint, so quantifiers hoist freely.
    """
    if isinstance(n, Quantifier):
        prefix, matrix = _prenex_split(n.formula)
        return [(n.type, n.variable)] + prefix, matrix
    if isinstance(n, (And, Or)):
        pl, ml = _prenex_split(n.left)
        pr, mr = _prenex_split(n.right)
        return pl + pr, type(n)(ml, mr)
    return [], n  # Not(atom) or Atom


# ---------------------------------------------------------------------------
# Conjunctive normal form
# ---------------------------------------------------------------------------

def to_cnf(node: Node) -> Node:
    """Return prenex form whose matrix is a conjunction of clauses. Equivalence-preserving."""
    pnf = to_pnf(node)
    prefix, matrix = _prenex_split(pnf)
    cnf_matrix = _cnf(matrix)
    for qtype, qvar in reversed(prefix):
        cnf_matrix = Quantifier(qtype, qvar, cnf_matrix)
    return cnf_matrix


def _cnf(n: Node) -> Node:
    """Distribute ∨ over ∧ in a quantifier-free NNF formula."""
    if isinstance(n, (Atom, Not)):
        return n
    if isinstance(n, And):
        return And(_cnf(n.left), _cnf(n.right))
    if isinstance(n, Or):
        return _distribute(_cnf(n.left), _cnf(n.right))
    raise TypeError(f"to_cnf: unexpected node type {type(n).__name__}")


def _distribute(left: Node, right: Node) -> Node:
    if isinstance(left, And):
        return And(_distribute(left.left, right), _distribute(left.right, right))
    if isinstance(right, And):
        return And(_distribute(left, right.left), _distribute(left, right.right))
    return Or(left, right)


# ---------------------------------------------------------------------------
# Disjunctive normal form
# ---------------------------------------------------------------------------

def to_dnf(node: Node) -> Node:
    """Return prenex form whose matrix is a disjunction of conjunctive clauses.

    The dual of :func:`to_cnf`: reuse the prenex prefix from ``to_pnf`` and
    distribute ∧ over ∨ in the quantifier-free matrix (each conjunctive clause
    is a conjunction of literals). Equivalence-preserving.
    """
    pnf = to_pnf(node)
    prefix, matrix = _prenex_split(pnf)
    dnf_matrix = _dnf(matrix)
    for qtype, qvar in reversed(prefix):
        dnf_matrix = Quantifier(qtype, qvar, dnf_matrix)
    return dnf_matrix


def _dnf(n: Node) -> Node:
    """Distribute ∧ over ∨ in a quantifier-free NNF formula (dual of _cnf)."""
    if isinstance(n, (Atom, Not)):
        return n
    if isinstance(n, Or):
        return Or(_dnf(n.left), _dnf(n.right))
    if isinstance(n, And):
        return _distribute_and(_dnf(n.left), _dnf(n.right))
    raise TypeError(f"to_dnf: unexpected node type {type(n).__name__}")


def _distribute_and(left: Node, right: Node) -> Node:
    """Distribute ∧ over ∨ (dual of _distribute)."""
    if isinstance(left, Or):
        return Or(_distribute_and(left.left, right), _distribute_and(left.right, right))
    if isinstance(right, Or):
        return Or(_distribute_and(left, right.left), _distribute_and(left, right.right))
    return And(left, right)


# ---------------------------------------------------------------------------
# Tseitin (definitional) CNF
# ---------------------------------------------------------------------------

def to_tseitin_cnf(node: Node) -> Node:
    """Return an EQUISATISFIABLE CNF via the Tseitin/definitional encoding.

    Unlike :func:`to_cnf`, this is *not* equivalence-preserving: a fresh 0-ary
    auxiliary predicate Atom is introduced for every compound subformula of the
    quantifier-free NNF matrix, and the defining biconditionals (``aux ↔
    op(children)``) are expanded into clauses and conjoined with the unit clause
    asserting the root auxiliary. This avoids the exponential blow-up of the
    distributive :func:`to_cnf` while preserving satisfiability.

    The auxiliaries are *0-ary* (propositional) definitions, so they only
    faithfully capture a subformula whose truth value is fixed — i.e. the
    propositional / ground case the encoding targets. They are **not** sound
    inside a quantifier prefix: a single global ``aux`` cannot track a
    subformula such as ``P(x)`` whose truth value varies over the domain, which
    breaks equisatisfiability. This function therefore requires a quantifier-free
    (after prenexing) input and raises :class:`ValueError` otherwise.
    """
    pnf = to_pnf(node)
    prefix, matrix = _prenex_split(pnf)
    if prefix:
        raise ValueError(
            "to_tseitin_cnf only supports quantifier-free (propositional / "
            "ground) formulas: the 0-ary auxiliary predicates are not sound "
            "under a quantifier prefix. Eliminate quantifiers first (e.g. via "
            "skolemize and grounding) or use to_cnf for an equivalence-"
            "preserving prenex CNF."
        )
    used = _all_names(pnf)
    counter = [0]

    clauses = []                       # accumulated CNF clauses (each a Node)
    root = _tseitin(matrix, counter, used, clauses)
    clauses.append(root)               # unit clause asserting the root holds

    cnf_matrix = clauses[0]
    for clause in clauses[1:]:
        cnf_matrix = And(cnf_matrix, clause)
    return cnf_matrix


def _tseitin(n: Node, counter: list, used: set, clauses: list) -> Node:
    """Encode subformula n, appending its defining clauses; return its literal.

    A literal (Atom or ¬Atom) is returned unchanged — it needs no auxiliary.
    For each compound node a fresh 0-ary Atom ``aux`` is created and the clauses
    expressing ``aux ↔ op(children)`` are appended to ``clauses``.
    """
    if isinstance(n, Atom):
        return n
    if isinstance(n, Not):
        # Inputs are NNF, so this wraps an atom: it is already a literal.
        return n

    if isinstance(n, And):
        a = _tseitin(n.left, counter, used, clauses)
        b = _tseitin(n.right, counter, used, clauses)
        aux = Atom(_gensym("ts", counter, used), [])
        # aux ↔ (a ∧ b):
        #   (¬aux ∨ a) ∧ (¬aux ∨ b) ∧ (¬a ∨ ¬b ∨ aux)
        clauses.append(Or(Not(aux), a))
        clauses.append(Or(Not(aux), b))
        clauses.append(Or(Or(_neg(a), _neg(b)), aux))
        return aux

    if isinstance(n, Or):
        a = _tseitin(n.left, counter, used, clauses)
        b = _tseitin(n.right, counter, used, clauses)
        aux = Atom(_gensym("ts", counter, used), [])
        # aux ↔ (a ∨ b):
        #   (¬aux ∨ a ∨ b) ∧ (¬a ∨ aux) ∧ (¬b ∨ aux)
        clauses.append(Or(Not(aux), Or(a, b)))
        clauses.append(Or(_neg(a), aux))
        clauses.append(Or(_neg(b), aux))
        return aux

    raise TypeError(f"to_tseitin_cnf: unexpected node type {type(n).__name__}")


def _neg(lit: Node) -> Node:
    """Return the negation of a literal, collapsing ¬¬Atom back to Atom."""
    if isinstance(lit, Not):
        return lit.formula
    return Not(lit)


# ---------------------------------------------------------------------------
# Skolemization
# ---------------------------------------------------------------------------

def skolemize(node: Node) -> Node:
    """Return prenex NNF with existentials replaced by Skolem terms.

    Each ∃-bound variable becomes a Skolem function of the universals in scope
    (a Skolem constant if there are none); the existential quantifiers are
    dropped and the universal prefix is retained. Satisfiability-preserving.
    """
    pnf = to_pnf(node)
    prefix, matrix = _prenex_split(pnf)
    used = _all_names(pnf)
    sk_counter = [0]

    universals = []          # Variables of the ∀ seen so far, in order
    kept_prefix = []         # the ∀ Variables to re-wrap
    subst = {}               # existential var name -> Skolem term

    for qtype, qvar in prefix:
        if qtype in _FORALL:
            universals.append(qvar)
            kept_prefix.append(qvar)
        else:
            fname = _gensym("sk", sk_counter, used)
            term = Function(fname, list(universals)) if universals else Constant(fname)
            subst[qvar.name] = term

    result = matrix
    for name, term in subst.items():
        result = _subst_term(result, name, term)
    for qvar in reversed(kept_prefix):
        result = Quantifier("∀", qvar, result)
    return result


def _subst_term(n: Node, varname: str, term: Node) -> Node:
    """Replace every free Variable(varname) with term inside a formula/term."""
    if isinstance(n, Variable):
        return term if n.name == varname else n
    if isinstance(n, (Constant, Number)):
        return n
    if isinstance(n, Quantifier):
        if n.variable.name == varname:
            return n  # shadowed (cannot happen after standardising apart, but safe)
        return Quantifier(n.type, n.variable, _subst_term(n.formula, varname, term))
    # Structural: Function, Atom, Not, And, Or — substitute into every child.
    return n.map_children(lambda c: _subst_term(c, varname, term))


# ---------------------------------------------------------------------------
# Horn check
# ---------------------------------------------------------------------------

def is_horn(node: Node) -> bool:
    """Return True iff node's clausal form consists of Horn clauses.

    Syntactic/clausal definition: skolemise, drop the universal prefix, put the
    matrix into CNF, split into clauses, and check that every clause has at most
    one positive literal.
    """
    sk = skolemize(node)
    _, matrix = _prenex_split(sk)
    cnf = _cnf(matrix)
    for clause in _clauses(cnf):
        if sum(1 for lit in clause if isinstance(lit, Atom)) > 1:
            return False
    return True


def _conjuncts(n: Node) -> list:
    if isinstance(n, And):
        return _conjuncts(n.left) + _conjuncts(n.right)
    return [n]


def _disjuncts(n: Node) -> list:
    if isinstance(n, Or):
        return _disjuncts(n.left) + _disjuncts(n.right)
    return [n]


def _clauses(cnf: Node) -> list:
    """Split a CNF matrix into a list of clauses, each a list of literals."""
    return [_disjuncts(c) for c in _conjuncts(cnf)]
