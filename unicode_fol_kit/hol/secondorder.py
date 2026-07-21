"""Second-order logic → HOL/THF export (predicate quantification mapped natively).

Classical second-order logic (SOL) extends first-order logic with quantification
over *predicate* variables: ``∀P φ`` / ``∃P φ`` where ``P`` ranges over relations
of a fixed arity on the domain (the toolkit's finite-model partner is
:func:`unicode_fol_kit.semantics.secondorder.satisfies_so`, which brute-forces
every relation ``R ⊆ domain ** arity``). A higher-order logic prover already *has*
predicate quantification, so the embedding here is direct rather than the shallow
world-lifting used for modal logic:

- an object variable ``x`` has THF type ``$i`` (Isabelle: an uninterpreted ``i``);
- a predicate variable ``P`` of arity ``k`` has THF type ``$i > … > $i > $o``
  (``k`` copies of ``$i``), i.e. Isabelle ``i ⇒ … ⇒ i ⇒ bool``;
- a first-order atom ``A(t̄)`` is the application ``( a @ t1 @ … @ tk )``;
- an object quantifier ``∀x`` / ``∃x`` is a THF ``! [X:$i]`` / ``? [X:$i]``;
- a **second-order** quantifier ``∀P/k`` / ``∃P/k`` is a THF
  ``! [P: ($i>…>$i>$o)]`` / ``? [P: …]`` — a quantifier over a predicate-typed
  variable, exactly mirroring the SOL reading.

This is the **monadic-and-up relational** second order: predicate (relation)
variables of any arity, including arity 0 (a Boolean / propositional variable,
type ``$o``). It does NOT cover function-variable quantification or third order
and up — out of scope, matching ``satisfies_so``.

**Free symbols.** In the toolkit's ``second_order`` parser mode a bare lowercase
name parses to a :class:`~unicode_fol_kit.fol.nodes.Variable`. Any object
variable that is *not* bound by an enclosing object quantifier is a **free**
individual; in a closed THF problem / Isabelle theory a free variable is not
admissible, so such free variables are emitted as object **constants** (declared
``$i`` / ``consts … :: i``) — the natural reading of a free individual symbol, and
exactly how the finite-model evaluator would have to interpret it (via the
structure's ``constants``). Bound object variables render as THF uppercase
variables. A predicate name bound by some ``SecondOrderQuantifier`` is a bound
predicate variable everywhere it occurs (it is never declared as a problem
symbol); any *other* predicate is a free predicate and is declared in the
signature.

**Standard vs Henkin semantics.** In a real HOL prover the predicate quantifiers
range over the prover's full function space, i.e. **standard (full) second-order
semantics** — the same semantics ``satisfies_so`` realises on a finite domain.
SOL validity under standard semantics is **not semi-decidable** (no complete
proof procedure exists), so an external HOL prover (Leo-III, Satallax,
Sledgehammer) may fail to discharge a valid conjecture even though it is sound.
If you want Henkin (general-models) semantics instead — under which SOL is
effectively first-order and *is* axiomatisable — that is the user's job: add
comprehension axioms and restrict the predicate domain explicitly; this module
does not do it for you. The toolkit only **emits** the THF problem / Isabelle
theory; it does **not** run any prover.

Equality ``=`` / ``≠`` follows the toolkit convention used by the modal THF
export: an ordinary uninterpreted predicate over ``$i`` (rendered ``feq`` /
``fneq``), **not** primitive HOL identity. (The finite-model ``satisfies_so`` does
read ``=`` as identity via the structure; if you need that in the prover, add the
reflexivity / Leibniz axioms, or post-edit to primitive ``=``.)

Public API: :func:`to_thf_so`, :func:`to_isabelle_so`.
"""

from typing import Dict, FrozenSet, List

from ..fol.nodes import (
    Node, Variable, Constant, Number, Function,
    Atom, Not, And, Or, Xor, Implies, Iff, Quantifier,
    SecondOrderQuantifier, Cardinality, SortedCardinality,
)
from ..fol._symbol_names import dedupe as _dedupe  # shared de-collision helper

_FORALL = "∀"
_EXISTS = "∃"

# `=` / `≠` are uninterpreted structure-relative predicates in this toolkit, NOT
# primitive HOL identity. Give them valid distinct THF/Isabelle functors.
_PRED_ALIAS = {"=": "feq", "≠": "fneq"}


# ===========================================================================
# Name sanitising (shared spirit with qml._thf_name)
# ===========================================================================

def _functor(name: str) -> str:
    """Lower-camel a free predicate/constant/function name into a HOL functor."""
    if name in _PRED_ALIAS:
        return _PRED_ALIAS[name]
    safe = "".join(c if (c.isalnum() or c == "_") else "_" for c in name)
    return (safe[:1].lower() + safe[1:]) if safe else "p"


# ===========================================================================
# De-colliding name resolvers (THF only; the Isabelle path keeps _functor)
# ===========================================================================
#
# Two distinct collision hazards motivate these resolvers, and BOTH are specific
# to THF (where bound variables are uppercase and free symbols are lowercase
# functors, and every functor needs exactly one type):
#
# (1) FREE-SYMBOL COLLAPSE (soundness). A free predicate ``P`` and a free
#     individual ``p`` both pass through :func:`_functor` to the SAME functor
#     ``p`` but need DIFFERENT types (``$i>$o`` vs ``$i``); likewise ``Foo`` and
#     ``foo``. Emitting both yields a duplicate ``p_decl`` with conflicting types
#     and an ill-typed ``( p @ p )``. :class:`_FreeNames` assigns every free
#     symbol a globally UNIQUE functor across the predicate / individual /
#     function categories, and BOTH the declarations and the usages are routed
#     through it so they always agree.
#
# (2) BOUND-VARIABLE CAPTURE (faithfulness). A bound predicate variable renders
#     as ``name.upper()`` and a bound object variable renders as ``name.upper()``
#     too, so case-folding-equal names in nested binders collide: ``∃P ∀p P(p)``
#     would emit ``? [P:($i>$o)] : ! [P:$i] : ( P @ P )`` — the object binder
#     shadows the predicate binder and ``P @ P`` is ill-typed. :class:`_Scope`
#     gives bound predicate-variables and bound object-variables ONE shared,
#     never-reused pool of uppercase tokens, so distinct bound ``(kind, name)``
#     pairs always get distinct tokens.


class _FreeNames:
    """Resolve every FREE symbol to a globally-unique THF functor.

    Built once from :func:`_signature` so that declarations (:func:`_thf_signature`)
    and usages (:func:`_thf`, :func:`_thf_term`) draw the SAME functor for the
    same symbol. Predicates, individuals (constants / numbers / free object
    variables) and functions live in three lookup tables but share ONE pool of
    emitted functors, so a free predicate ``P`` and a free individual ``p`` — both
    naively ``_functor``-ing to ``p`` — get distinct functors (``p`` and, say,
    ``p_1``). Iteration is sorted within each category and categories are claimed
    predicate → individual → function, so the result is deterministic.
    """

    def __init__(self, formula: Node):
        pred_arity, const_names, func_arity = _signature(formula)
        used = set()
        self.pred: Dict[str, str] = {}
        self.ind: Dict[str, str] = {}
        self.func: Dict[str, str] = {}
        # Predicates first (they tend to keep the more meaningful name), then
        # individuals, then functions — each de-colliding against the shared pool.
        for name in sorted(pred_arity):
            self.pred[name] = _dedupe(_functor(name), used)
        for name in sorted(const_names):
            self.ind[name] = _dedupe(_functor(name), used)
        for name in sorted(func_arity):
            self.func[name] = _dedupe(_functor(name), used)


class _Scope:
    """A shared, never-reused token pool for bound predicate AND object variables.

    A binder calls :meth:`bind`, which returns a *new* :class:`_Scope` whose
    mapping is the parent's extended with a fresh uppercase token for this
    ``(kind, name)`` — fresh against EVERY token in scope, regardless of kind, so
    a predicate binder ``P`` and an inner object binder ``p`` never both render as
    ``P``. The token is looked up by ``(kind, name)`` so a bound variable resolves
    to the same token at its binder and at every applied occurrence.
    """

    __slots__ = ("_tokens", "_used")

    def __init__(self, tokens=None, used=None):
        self._tokens: Dict = dict(tokens or {})
        self._used = set(used or ())

    def bind(self, kind: str, name: str) -> "_Scope":
        used = set(self._used)
        base = _functor(name).upper() or "V"
        # An all-non-alnum name could upper-case to something starting with a
        # digit / underscore; guarantee a legal THF variable head.
        if not base[:1].isalpha():
            base = "V" + base
        token = _dedupe(base, used)
        tokens = dict(self._tokens)
        tokens[(kind, name)] = token
        return _Scope(tokens, used)

    def token(self, kind: str, name: str) -> str:
        return self._tokens[(kind, name)]


# ===========================================================================
# Scope analysis: bound predicate vars, bound object vars, free symbols
# ===========================================================================

def _bound_preds(formula: Node) -> FrozenSet[str]:
    """Names bound by some ``SecondOrderQuantifier`` (-> bound predicate vars)."""
    return frozenset(
        n.predicate for n in formula.walk()
        if isinstance(n, SecondOrderQuantifier)
    )


def _so_arity(formula: Node) -> Dict[str, int]:
    """Map each second-order-bound predicate name to its binder-recorded arity."""
    return {
        n.predicate: n.arity
        for n in formula.walk()
        if isinstance(n, SecondOrderQuantifier)
    }


def _free_object_vars(formula: Node, bound=frozenset()) -> FrozenSet[str]:
    """Object-variable names occurring free (not under an enclosing ∀x/∃x).

    Recurses tracking the enclosing object-quantifier scope. SecondOrderQuantifier
    binds a *predicate* name, not an object variable, so it does not change the
    object-binding scope.
    """
    if isinstance(formula, Variable):
        return frozenset() if formula.name in bound else frozenset({formula.name})
    if isinstance(formula, Quantifier):
        return _free_object_vars(formula.formula, bound | {formula.variable.name})
    if isinstance(formula, (Cardinality, SortedCardinality)):
        # |{v : φ}| BINDS v over its matrix — a generic child walk would report
        # the bound v as free (the binder-blind defect class fixed in 0.16.0).
        return _free_object_vars(formula.formula, bound | {formula.variable.name})
    free = set()
    for child in formula._child_nodes():
        free |= _free_object_vars(child, bound)
    return frozenset(free)


def _signature(formula: Node):
    """Collect free predicates, free constants/free-vars-as-constants, functions.

    Returns ``(pred_arity, const_names, func_arity)``:

    - ``pred_arity``: free predicate name -> arity (atoms whose predicate is not a
      bound second-order variable);
    - ``const_names``: explicit constants, number constants, AND free object
      variables (treated as individual constants in the closed export);
    - ``func_arity``: function name -> arity.
    """
    so_names = _bound_preds(formula)
    free_vars = _free_object_vars(formula)
    pred_arity: Dict[str, int] = {}
    const_names = set(free_vars)
    func_arity: Dict[str, int] = {}
    for n in formula.walk():
        if isinstance(n, Atom):
            if n.predicate in so_names:
                continue
            pred_arity[n.predicate] = len(n.args)
        elif isinstance(n, SortedCardinality):
            # The sort guard becomes a free unary predicate over the matrix.
            pred_arity.setdefault(n.sort, 1)
        elif isinstance(n, Constant):
            const_names.add(n.name)
        elif isinstance(n, Number):
            const_names.add("n" + str(n.value))
        elif isinstance(n, Function):
            func_arity[n.name] = len(n.args)
    return pred_arity, const_names, func_arity


# ===========================================================================
# (A) TPTP THF export
# ===========================================================================

def _thf_pred_type(arity: int) -> str:
    """THF type of an arity-``k`` predicate variable: ``$i > … > $i > $o``.

    Arity 0 is the Boolean case, type ``$o``.
    """
    return " > ".join(["$i"] * arity + ["$o"]) if arity else "$o"


def _thf_term(node: Node, scope: "_Scope", free: "_FreeNames") -> str:
    """Render an individual term in THF.

    A ``Variable`` bound by an enclosing object quantifier renders as its scope
    token (an uppercase THF variable, de-collided against every bound symbol);
    otherwise it is a free individual functor drawn from ``free``. Constants /
    numbers / functions resolve through ``free`` so a usage always matches its
    declaration.
    """
    if isinstance(node, Variable):
        try:
            return scope.token("obj", node.name)
        except KeyError:
            return free.ind[node.name]            # free individual functor
    if isinstance(node, Constant):
        return free.ind[node.name]
    if isinstance(node, Number):
        return free.ind["n" + str(node.value)]
    if isinstance(node, Function):
        head = free.func[node.name]
        return "( " + " @ ".join([head] + [_thf_term(a, scope, free) for a in node.args]) + " )"
    if isinstance(node, (Cardinality, SortedCardinality)):
        raise NotImplementedError(
            "to_thf_so: TH0 has no built-in finite-set theory, so a faithful "
            "cardinality encoding is not available here — use to_isabelle_so, "
            "which embeds |{v : φ}| as HOL's ``card {v. φ}``.")
    raise NotImplementedError(
        f"to_thf_so: unsupported term {type(node).__name__}.")


def _thf(node: Node, scope: "_Scope", free: "_FreeNames") -> str:
    """Render a second-order formula as a THF term of type ``$o``.

    ``scope`` resolves currently-bound predicate-variable and object-variable
    names to their (mutually de-collided) uppercase THF tokens; ``free`` resolves
    free symbols to their unique functors.
    """
    if isinstance(node, Atom):
        try:
            head = scope.token("pred", node.predicate)   # bound predicate VARIABLE
        except KeyError:
            head = free.pred[node.predicate]             # free predicate functor
        if not node.args:
            return head
        return "( " + " @ ".join([head] + [_thf_term(a, scope, free) for a in node.args]) + " )"
    if isinstance(node, Not):
        return f"( ~ {_thf(node.formula, scope, free)} )"
    if isinstance(node, And):
        return f"( {_thf(node.left, scope, free)} & {_thf(node.right, scope, free)} )"
    if isinstance(node, Or):
        return f"( {_thf(node.left, scope, free)} | {_thf(node.right, scope, free)} )"
    if isinstance(node, Xor):
        return f"( {_thf(node.left, scope, free)} <~> {_thf(node.right, scope, free)} )"
    if isinstance(node, Implies):
        return f"( {_thf(node.left, scope, free)} => {_thf(node.right, scope, free)} )"
    if isinstance(node, Iff):
        return f"( {_thf(node.left, scope, free)} <=> {_thf(node.right, scope, free)} )"
    if isinstance(node, Quantifier):
        x = node.variable.name
        q = "!" if node.type in (_FORALL, "forall") else "?"
        inner_scope = scope.bind("obj", x)
        inner = _thf(node.formula, inner_scope, free)
        return f"( {q} [{inner_scope.token('obj', x)}: $i] : {inner} )"
    if isinstance(node, SecondOrderQuantifier):
        # Predicate quantifier mapped DIRECTLY to a THF quantifier over a
        # predicate-typed variable of the inferred arity.
        p = node.predicate
        q = "!" if node.type in (_FORALL, "forall") else "?"
        typ = _thf_pred_type(node.arity)
        inner_scope = scope.bind("pred", p)
        inner = _thf(node.formula, inner_scope, free)
        return f"( {q} [{inner_scope.token('pred', p)}: ( {typ} )] : {inner} )"
    raise NotImplementedError(
        f"to_thf_so: {type(node).__name__} is outside the second-order fragment "
        "supported by the THF export.")


def _thf_signature(formula: Node, free: "_FreeNames") -> List[str]:
    """Type declarations for free predicates / constants / functions.

    Each free symbol is declared under the UNIQUE functor ``free`` assigned it, so
    a free predicate and a free individual that would otherwise both lower-case to
    the same name get distinct, single-typed declarations (no duplicate ``_decl``,
    no conflicting types). Second-order-bound predicate variables are omitted:
    they are THF bound variables introduced by their binders, not problem-level
    symbols.
    """
    pred_arity, const_names, func_arity = _signature(formula)
    decls = []
    for name, arity in sorted(pred_arity.items()):
        f = free.pred[name]
        typ = _thf_pred_type(arity)
        decls.append(f"thf({f}_decl, type, ( {f} : ( {typ} ) )).")
    for name in sorted(const_names):
        f = free.ind[name]
        decls.append(f"thf({f}_decl, type, ( {f} : $i )).")
    for name, arity in sorted(func_arity.items()):
        f = free.func[name]
        typ = " > ".join(["$i"] * (arity + 1))
        decls.append(f"thf({f}_decl, type, ( {f} : ( {typ} ) )).")
    return decls


def to_thf_so(formula: Node, conjecture: bool = True) -> str:
    """Emit a complete TPTP **THF** problem for a second-order formula.

    Object individuals inhabit ``$i``; a predicate variable ``P`` of arity ``k``
    is quantified at THF type ``$i > … > $i > $o``, so each ``∀P`` / ``∃P`` maps
    one-to-one to a higher-order quantifier — the natural SOL → HOL reading. The
    output declares every free predicate / constant / function symbol (free object
    variables are emitted as ``$i`` constants) and ends with the formula as a
    ``conjecture`` (``conjecture=True``) or an ``axiom`` (``conjecture=False``),
    ready for a higher-order ATP (Leo-III, Satallax).

    Semantics is **standard / full** second order in such a prover (predicate
    quantifiers range over the full function space), matching ``satisfies_so``.
    SOL validity under standard semantics is **not semi-decidable**, so a sound
    prover may still fail to close a valid conjecture; the toolkit only emits the
    problem, it does not run any prover. For Henkin (general-models) semantics,
    add your own comprehension axioms.

    Equality ``=`` / ``≠`` is emitted as an ordinary uninterpreted relation over
    ``$i`` (``feq`` / ``fneq``), not primitive HOL identity.
    """
    role = "conjecture" if conjecture else "axiom"
    lines = [
        "% Direct second-order -> HOL embedding (predicate quantifiers are native).",
        "% Standard (full) second-order semantics in a HOL prover; SOL validity is",
        "% NOT semi-decidable, so a sound prover may fail to close a valid goal.",
    ]
    free = _FreeNames(formula)
    lines += _thf_signature(formula, free)
    lines.append(f"thf(goal, {role}, ( {_thf(formula, _Scope(), free)} )).")
    return "\n".join(lines) + "\n"


# ===========================================================================
# (B) Isabelle/HOL export
# ===========================================================================

# Isabelle symbol macros (ASCII \<...> forms render as the Unicode glyphs).
_ISA = {
    "not": "\\<not>",
    "and": "\\<and>",
    "or": "\\<or>",
    "imp": "\\<longrightarrow>",
    "iff": "\\<longleftrightarrow>",
    "forall": "\\<forall>",
    "exists": "\\<exists>",
    "Rightarrow": "\\<Rightarrow>",
}
_ARROW = _ISA["Rightarrow"]


def _isa_pred_type(arity: int) -> str:
    """Isabelle type of an arity-``k`` predicate variable: ``i ⇒ … ⇒ i ⇒ bool``."""
    return (" " + _ARROW + " ").join(["i"] * arity + ["bool"]) if arity else "bool"


def _isa_fun_type(arity: int) -> str:
    """Isabelle type of an arity-``k`` function: ``i ⇒ … ⇒ i`` (k+1 copies of i)."""
    return (" " + _ARROW + " ").join(["i"] * (arity + 1))


def _isa_term(node: Node, bvars: FrozenSet[str], free: "_FreeNames") -> str:
    """Render an individual term in Isabelle (curried application, no commas).

    A bound object variable keeps its (lowercase) name; a free object variable is a
    declared individual constant whose functor is drawn from ``free`` — the SAME
    de-colliding resolver the declarations use, so a free individual never collides
    with a free predicate (which would emit two ``consts`` of the same name).
    """
    if isinstance(node, Variable):
        return node.name if node.name in bvars else free.ind[node.name]
    if isinstance(node, Constant):
        return free.ind[node.name]
    if isinstance(node, Number):
        return free.ind["n" + str(node.value)]
    if isinstance(node, Function):
        head = free.func[node.name]
        return "(" + " ".join([head] + [_isa_term(a, bvars, free) for a in node.args]) + ")"
    if isinstance(node, (Cardinality, SortedCardinality)):
        raise NotImplementedError(
            "to_isabelle_so: a cardinality term is supported only as an operand "
            "of a comparison (= ≠ < > ≤ ≥), where it embeds as HOL's "
            "``card {v. φ}``; as an argument of an uninterpreted predicate or "
            "function it would need type nat where individuals are expected.")
    raise NotImplementedError(
        f"to_isabelle_so: unsupported term {type(node).__name__}.")


#: HOL spellings of the numeric comparison operators used for cardinalities.
_CARD_COMPARE = {"=": "=", "<": "<", ">": ">",
                 "≤": "\\<le>", "≥": "\\<ge>"}


def _isa_card_operand(node: Node, bpreds: FrozenSet[str], bvars: FrozenSet[str],
                      free: "_FreeNames") -> str:
    """Render one operand of a numeric cardinality comparison (type ``nat``).

    A cardinality embeds as HOL's native finite-set cardinality
    ``card {v. φ}`` (``Finite_Set.card``, available from ``Main``); the sorted
    variant guards the matrix with its sort predicate. A number is a ``nat``
    literal. Anything else is a category error — the comparison is numeric, so
    an individual-typed operand cannot appear (the same rule the Tarskian
    evaluator enforces).
    """
    if isinstance(node, (Cardinality, SortedCardinality)):
        v = node.variable.name
        matrix = _isa(node.formula, bpreds, bvars | {v}, free)
        if isinstance(node, SortedCardinality):
            guard = free.pred[node.sort]
            matrix = f"(({guard} {v}) \\<and> {matrix})"
        return f"(card {{{v}. {matrix}}})"
    if isinstance(node, Number):
        return str(node.value)
    raise NotImplementedError(
        "to_isabelle_so: a comparison with a cardinality operand is NUMERIC — "
        "the other operand must be a Number or another cardinality term, not an "
        f"individual ({type(node).__name__}).")


def _isa(node: Node, bpreds: FrozenSet[str], bvars: FrozenSet[str], free: "_FreeNames") -> str:
    """Render a second-order formula as an Isabelle/HOL boolean term."""
    if isinstance(node, Atom):
        if (node.predicate in ("=", "≠") or node.predicate in _CARD_COMPARE) \
                and len(node.args) == 2 \
                and any(isinstance(a, (Cardinality, SortedCardinality))
                        for a in node.args):
            # Numeric reading: a cardinality IS a natural number (HOL's card),
            # so the comparison is arithmetic over nat, not an uninterpreted
            # relation over individuals — mirroring semantics.tarski.
            left = _isa_card_operand(node.args[0], bpreds, bvars, free)
            right = _isa_card_operand(node.args[1], bpreds, bvars, free)
            if node.predicate == "≠":
                return f"(\\<not> ({left} = {right}))"
            return f"({left} {_CARD_COMPARE[node.predicate]} {right})"
        head = node.predicate if node.predicate in bpreds else free.pred[node.predicate]
        if not node.args:
            return head
        return "(" + " ".join([head] + [_isa_term(a, bvars, free) for a in node.args]) + ")"
    if isinstance(node, Not):
        return f"({_ISA['not']} {_isa(node.formula, bpreds, bvars, free)})"
    if isinstance(node, And):
        return f"({_isa(node.left, bpreds, bvars, free)} {_ISA['and']} {_isa(node.right, bpreds, bvars, free)})"
    if isinstance(node, Or):
        return f"({_isa(node.left, bpreds, bvars, free)} {_ISA['or']} {_isa(node.right, bpreds, bvars, free)})"
    if isinstance(node, Xor):
        # x XOR y  ≡  ¬(x ↔ y)
        return f"({_ISA['not']} ({_isa(node.left, bpreds, bvars, free)} {_ISA['iff']} {_isa(node.right, bpreds, bvars, free)}))"
    if isinstance(node, Implies):
        return f"({_isa(node.left, bpreds, bvars, free)} {_ISA['imp']} {_isa(node.right, bpreds, bvars, free)})"
    if isinstance(node, Iff):
        return f"({_isa(node.left, bpreds, bvars, free)} {_ISA['iff']} {_isa(node.right, bpreds, bvars, free)})"
    if isinstance(node, Quantifier):
        x = node.variable.name
        q = _ISA["forall"] if node.type in (_FORALL, "forall") else _ISA["exists"]
        inner = _isa(node.formula, bpreds, bvars | {x}, free)
        return f"({q}{x}::i. {inner})"
    if isinstance(node, SecondOrderQuantifier):
        p = node.predicate
        q = _ISA["forall"] if node.type in (_FORALL, "forall") else _ISA["exists"]
        typ = _isa_pred_type(node.arity)
        inner = _isa(node.formula, bpreds | {p}, bvars, free)
        return f"({q}{p}::{typ}. {inner})"
    raise NotImplementedError(
        f"to_isabelle_so: {type(node).__name__} is outside the second-order "
        "fragment supported by the Isabelle export.")


def _isa_signature(formula: Node, free: "_FreeNames") -> List[str]:
    """``consts`` declarations for free predicates / constants / functions.

    Each symbol is declared under the unique functor ``free`` assigned it, so a free
    predicate and a free individual that both lower-case to the same name get two
    DISTINCT ``consts`` (Isabelle rejects duplicate constant declarations).
    """
    pred_arity, const_names, func_arity = _signature(formula)
    decls = []
    for name in sorted(const_names):
        decls.append(f"consts {free.ind[name]} :: \"i\"")
    for name, arity in sorted(func_arity.items()):
        decls.append(f"consts {free.func[name]} :: \"{_isa_fun_type(arity)}\"")
    for name, arity in sorted(pred_arity.items()):
        decls.append(f"consts {free.pred[name]} :: \"{_isa_pred_type(arity)}\"")
    return decls


def to_isabelle_so(formula: Node, name: str = "SO_Goal") -> str:
    """Emit a self-contained Isabelle/HOL theory for a second-order formula.

    Individuals inhabit an uninterpreted type ``i``; a predicate variable ``P`` of
    arity ``k`` is bound at type ``i ⇒ … ⇒ i ⇒ bool``, so each ``∀P`` / ``∃P``
    becomes a native HOL ``∀`` / ``∃`` over a predicate type — the direct SOL → HOL
    reading. Free predicate / constant / function symbols (and free object
    variables, as individual constants) are introduced with ``consts``; the
    formula is stated as a ``lemma`` left ``oops`` (replace with ``by auto`` /
    ``by blast`` / ``sledgehammer``).

    As with :func:`to_thf_so`, this is **standard (full)** second-order semantics
    in Isabelle/HOL; SOL validity is not semi-decidable, so Sledgehammer may fail
    on a valid lemma. The toolkit emits the theory only — it does not run
    Isabelle. Equality ``=`` / ``≠`` is an uninterpreted relation (``feq`` /
    ``fneq``), not HOL ``=``.

    ``name`` becomes the theory name; it must be a legal Isabelle identifier (it is
    also conventionally the ``.thy`` file's base name).
    """
    free = _FreeNames(formula)
    body = _isa(formula, frozenset(), frozenset(), free)
    lines = [
        "(* Direct second-order -> HOL embedding (predicate quantifiers native). *)",
        "(* Standard (full) second-order semantics; SOL validity is NOT *)",
        "(* semi-decidable, so Sledgehammer may fail on a valid lemma. *)",
        f"theory {name}",
        "  imports Main",
        "begin",
        "",
        "typedecl i  \\<comment> \\<open>individuals\\<close>",
    ]
    lines += _isa_signature(formula, free)
    lines.append("")
    lines.append(f"lemma \"{body}\"")
    lines.append("  oops  \\<comment> \\<open>try: by auto / by blast / sledgehammer\\<close>")
    lines.append("")
    lines.append("end")
    return "\n".join(lines) + "\n"
