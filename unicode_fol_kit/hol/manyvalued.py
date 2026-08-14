"""Finite many-valued propositional logic -> HOL export (K3 / LP / FDE / any TruthMatrix).

A many-valued *shallow semantical embedding* (SSE) in the Benzmueller/Steen
style, generalised over the toolkit's finite-matrix layer
:mod:`unicode_fol_kit.semantics.matrix`: any :class:`~unicode_fol_kit.semantics.matrix.TruthMatrix`
(the three-valued ``K3_MATRIX`` / ``LP_MATRIX``, the four-valued Belnap-Dunn
``FDE_MATRIX``, or a custom matrix built with ``TruthMatrix.from_functions``)
can be reified as an N-element HOL type, with the connectives defined as total
functions over that type matching the matrix's own operation tables, and
*validity* read as "the formula's value is **designated** under every
valuation". Concretely, for a matrix with values ``v1, ..., vN``:

  * ``N`` distinct, pairwise-**distinct** and jointly **exhaustive** constants
    reify the truth values (so an ATP/Isabelle can finitely case-split);
  * one **ground equation per truth-table cell** pins each connective the
    matrix actually tabulates (arity-1 for negation, arity-2 for the rest;
    only over connectives with a *non-empty* table -- a formula using a
    connective the matrix has no table for is rejected up front, not emitted
    as a dangling symbol);
  * a **designated** predicate ``des`` picks out the matrix's designated set;
  * the conjecture/lemma is ``! [valuation] : des @ eval(formula)``, a
    **Theorem** exactly when ``formula`` is valid in the matrix.

This is the data-driven core: :func:`to_thf_matrix` / :func:`to_isabelle_matrix`
(and their ``*_entailment`` counterparts) take **any** finite
:class:`~unicode_fol_kit.semantics.matrix.TruthMatrix` and need nothing hardcoded
about K3/LP/FDE. The legacy K3/LP-only entry points --
:func:`to_thf_k3lp`, :func:`to_isabelle_k3lp`, :func:`to_thf_k3lp_entailment`,
:func:`to_isabelle_k3lp_entailment` -- are now thin wrappers that look up
``K3_MATRIX`` / ``LP_MATRIX`` and delegate, passing the historical constant/
function names (``tT``/``tB``/``tF``, ``kneg``/``kand``/``kor``/``kimp``/
``kiff``/``kxor``) so their emitted text keeps its shape; this is a
compatibility convenience, not a promise about a specific matrix's naming.

Truth-value reification and naming.  Each matrix value gets a constant name:
a caller may pin exact names via ``value_names`` (a ``{value: name}`` dict --
used by the K3/LP wrappers to reproduce ``tT``/``tB``/``tF``), and any value
left unnamed gets the default ``"t" + sanitised(str(value))`` (e.g. FDE's
``"T"`` -> ``"tT"``, K3's ``0.5`` -> ``"t0_5"``), de-collided exactly like the
module's atom-variable naming (:func:`_assign_var_names`). Connective function/
predicate symbols are similarly overridable via ``conn_names`` (default: the
:class:`TruthMatrix` field name itself -- ``neg``/``conj``/``disj``/``impl``/
``iff``/``xor``).

Honesty / scope.  The toolkit *emits* a problem/theory; it does **not** run
Leo-III, Satallax, Isabelle, or Sledgehammer. Any *finite* matrix's validity is
**decidable** (finite truth tables), so the emitted problem is in principle
fully dischargeable by any sound+complete HOL prover -- and for the Isabelle
export the emit-time verdict (and, when invalid/non-entailing, the witness
used in the proof) comes from the toolkit's own oracle,
:func:`unicode_fol_kit.semantics.matrix.matrix_is_valid` /
:func:`~unicode_fol_kit.semantics.matrix.matrix_entails`, so the emitted lemma
cannot drift from the decision procedure it is meant to certify. This module
covers the **propositional** fragment only: quantifiers and all modal /
Lukasiewicz / sorted / lambda nodes are out of scope and raise
``NotImplementedError`` -- exactly the nodes the toolkit's evaluators reject,
plus ``Quantifier`` (a first-order many-valued validity problem is not a
finite truth table and is not handled by this propositional export).

Public API: :func:`to_thf_matrix`, :func:`to_isabelle_matrix`,
:func:`to_thf_matrix_entailment`, :func:`to_isabelle_matrix_entailment`, and
the K3/LP-specific :func:`to_thf_k3lp`, :func:`to_isabelle_k3lp`,
:func:`to_thf_k3lp_entailment`, :func:`to_isabelle_k3lp_entailment`, and the
constant :data:`SYSTEMS`.
"""

from itertools import product
from typing import Dict, List, Optional, Sequence, Type

from ..fol.nodes import (
    Node, Atom, Not, And, Or, Xor, Implies, Iff, Quantifier,
    Variable, Constant, Number, Function,
)
from ..semantics.matrix import (
    TruthMatrix, Value, matrix_value, matrix_is_valid, matrix_entails,
    K3_MATRIX, LP_MATRIX,
)

# The two legacy systems and their designated-value sets, kept in lock-step
# with unicode_fol_kit.semantics.manyvalued.DESIGNATED (K3 designates only
# "true"; LP designates "true" and "both") -- and, since 0.17, re-expressed as
# TruthMatrix instances (semantics.matrix.K3_MATRIX / LP_MATRIX).
SYSTEMS = ("K3", "LP")

_K3LP_MATRICES = {"K3": K3_MATRIX, "LP": LP_MATRIX}


def _check_system(system: str) -> str:
    if system not in SYSTEMS:
        raise ValueError(
            f"Unknown three-valued system {system!r}; choose one of {list(SYSTEMS)} "
            "(K3 designates {T}; LP designates {T, B}). For any other finite "
            "logical matrix (e.g. FDE), use to_thf_matrix / to_isabelle_matrix "
            "with a unicode_fol_kit.semantics.matrix.TruthMatrix directly."
        )
    return system


def _check_propositional(formula: Node) -> None:
    """Reject any node outside the propositional {neg,and,or,xor,imp,iff} fragment.

    Recurses the *connective* structure only, treating an ``Atom`` as a leaf:
    an atom's term arguments (Variable/Constant/Number/Function -- e.g. the ``a``
    in ``P(a)``) are legitimate and are not inspected; an atom is just a key into
    the valuation.

    Shared by every export in this module (K3/LP and the generic matrix
    exporters alike): a quantified or modal/Lukasiewicz/sorted/lambda node has
    no many-valued propositional reading here, and this export's validity is a
    finite truth table, so ``Quantifier`` is out of scope too.
    """
    if isinstance(formula, Atom):
        return
    if isinstance(formula, Not):
        _check_propositional(formula.formula)
        return
    if isinstance(formula, (And, Or, Xor, Implies, Iff)):
        _check_propositional(formula.left)
        _check_propositional(formula.right)
        return
    if isinstance(formula, Quantifier):
        raise NotImplementedError(
            "many-valued HOL export: Quantifier is outside the propositional "
            "fragment; first-order many-valued validity is not a finite truth "
            "table. Use unicode_fol_kit.semantics.manyvalued.is_valid or "
            "semantics.matrix.matrix_is_valid with a domain instead."
        )
    if isinstance(formula, (Variable, Constant, Number, Function)):
        raise NotImplementedError(
            f"many-valued HOL export: {type(formula).__name__} is a term, not "
            "a propositional formula."
        )
    raise NotImplementedError(
        f"many-valued HOL export: {type(formula).__name__} is not in the "
        "propositional fragment {not, and, or, xor, implies, iff}; this "
        "export has no many-valued reading for it."
    )


# ---------------------------------------------------------------------------
# Atom keys -> THF / Isabelle valuation-variable names
# ---------------------------------------------------------------------------
#
# An *atom* of the propositional formula is keyed by its canonical
# ``to_unicode_str()`` rendering -- EXACTLY the key the toolkit's evaluators use
# (e.g. ``valuation[atom.to_unicode_str()]`` in matrix_value). Distinct atoms
# become distinct universally-quantified valuation variables.

def _atom_keys(formula: Node) -> List[str]:
    """Distinct atom keys (canonical ``to_unicode_str``) in first-seen order."""
    keys: List[str] = []
    seen = set()
    for atom in formula.atoms():
        key = atom.to_unicode_str()
        if key not in seen:
            seen.add(key)
            keys.append(key)
    return keys


def _safe_name(key: str) -> str:
    """Turn an arbitrary key into a safe alnum/underscore suffix for a name."""
    return "".join(c if (c.isalnum() or c == "_") else "_" for c in key)


def _assign_var_names(keys: List[str]) -> dict:
    """Map each atom key to a distinct uppercase THF/Isabelle variable name.

    ``P(a)`` -> ``V_P_A`` etc.; on a collision after sanitisation a numeric
    suffix is appended so distinct atoms never share a valuation variable.
    """
    names_by_key = {}
    used = set()
    for key in keys:
        base = "V_" + _safe_name(key)
        base = base.upper()
        name = base
        i = 0
        while name in used:
            i += 1
            name = f"{base}_{i}"
        used.add(name)
        names_by_key[key] = name
    return names_by_key


# ===========================================================================
# Generic matrix machinery: naming, op-availability, and the emit-time oracle.
# ===========================================================================
#
# Canonical (node class, TruthMatrix field name, arity) triples, in the fixed
# order every export below declares/axiomatises them -- same order the K3/LP
# export always used (neg, conj, disj, impl, iff, xor).
_CANONICAL_OPS = [
    (Not, "neg", 1), (And, "conj", 2), (Or, "disj", 2),
    (Implies, "impl", 2), (Iff, "iff", 2), (Xor, "xor", 2),
]
_CANONICAL_OP_INFO = {cls: (attr, arity) for cls, attr, arity in _CANONICAL_OPS}
# Default connective symbol names are the TruthMatrix field name prefixed with
# "mv_" (many-valued) -- NOT the bare field name. Isabelle/HOL's prelude
# (`imports Main`) already binds `conj`/`disj` as the underlying constants of
# `\<and>`/`\<or>`; a bare `fun conj` or `fun disj` would collide with those.
# The legacy K3/LP export already dodged exactly this with its "k" prefix
# (kneg/kand/kor/kimp/kiff/kxor); "mv_" generalises the same precaution to any
# matrix's default names. A caller may still override via ``conn_names``.
_DEFAULT_CONN_NAMES = {cls: f"mv_{attr}" for cls, attr, _ in _CANONICAL_OPS}


def _matrix_defined_ops(matrix: TruthMatrix):
    """The canonical ``(node class, table attr, arity)`` triples ``matrix`` actually
    tabulates (a non-empty dict for that connective), in the fixed declaration order."""
    return [(cls, attr, arity) for cls, attr, arity in _CANONICAL_OPS if getattr(matrix, attr)]


def _collect_used_ops(node: Node, acc: set) -> None:
    """Record which connective *classes* appear in the propositional structure of ``node``."""
    if isinstance(node, Atom):
        return
    if isinstance(node, Not):
        acc.add(Not)
        _collect_used_ops(node.formula, acc)
        return
    if isinstance(node, (And, Or, Xor, Implies, Iff)):
        acc.add(type(node))
        _collect_used_ops(node.left, acc)
        _collect_used_ops(node.right, acc)
        return
    # Any other node class is already rejected by _check_propositional.


def _check_matrix_supports(formulas: Sequence[Node], matrix: TruthMatrix) -> None:
    """Raise ``ValueError`` if some formula uses a connective ``matrix`` has no table for.

    ``matrix``'s ``neg``/``conj``/``disj``/``impl``/``iff``/``xor`` fields are
    plain dicts; an empty dict means "this matrix does not define this
    connective" (``TruthMatrix.from_functions`` always fills all six, but a
    hand-built matrix may legitimately omit one). Emitting a THF/Isabelle
    symbol with no axioms would be unsound (an uninterpreted function the
    prover could give any meaning), so this is checked eagerly instead.
    """
    used: set = set()
    for f in formulas:
        _collect_used_ops(f, used)
    for cls in used:
        attr, _ = _CANONICAL_OP_INFO[cls]
        if not getattr(matrix, attr):
            raise ValueError(
                f"TruthMatrix {matrix.name!r} does not define {attr!r} (its "
                f"table is empty), but the formula uses {cls.__name__}. This "
                "export only reifies connectives the matrix actually "
                f"tabulates -- supply a matrix with a non-empty {attr!r} "
                f"table, or remove {cls.__name__} from the formula."
            )


def _default_value_name(value: Value, used: set) -> str:
    """Default constant name for a matrix value: ``"t" + sanitised(str(value))``,
    de-collided with a numeric suffix (mirrors :func:`_assign_var_names`)."""
    base = "t" + _safe_name(str(value))
    name = base
    i = 0
    while name in used:
        i += 1
        name = f"{base}_{i}"
    return name


def _resolve_value_names(matrix: TruthMatrix,
                          value_names: Optional[Dict[Value, str]]) -> Dict[Value, str]:
    """Merge caller-supplied constant names with defaults for the rest.

    The returned dict's iteration order is significant: it is the order
    constants/constructors are declared in the emitted text. It is the
    caller's ``value_names`` keys, in the order given (letting a caller pin a
    specific declaration order), followed by any remaining ``matrix.values``
    in the matrix's own order. Every value resolves to a distinct name.
    """
    provided = dict(value_names or {})
    for v in provided:
        if v not in matrix.values:
            raise ValueError(
                f"value_names key {v!r} is not one of matrix {matrix.name!r}'s "
                f"values {matrix.values!r}.")
    resolved: Dict[Value, str] = {}
    used = set()
    for v, nm in provided.items():
        resolved[v] = nm
        used.add(nm)
    for v in matrix.values:
        if v in resolved:
            continue
        name = _default_value_name(v, used)
        resolved[v] = name
        used.add(name)
    return resolved


def _resolve_conn_names(conn_names: Optional[Dict[Type[Node], str]]) -> Dict[Type[Node], str]:
    """Merge caller-supplied connective symbol names with the field-name defaults."""
    resolved = dict(_DEFAULT_CONN_NAMES)
    if conn_names:
        resolved.update(conn_names)
    return resolved


def _matrix_falsifying_assignment(formula: Node, matrix: TruthMatrix, keys: List[str]):
    """A ``matrix``-value assignment (in ``keys`` order) making ``formula`` non-designated.

    Only called after :func:`~unicode_fol_kit.semantics.matrix.matrix_is_valid`
    has already reported ``formula`` invalid (which enumerates the identical
    assignment space and bounds it by ``MAX_MODELS``), so a witness is
    guaranteed to exist and this re-enumeration is safe.
    """
    for combo in product(matrix.values, repeat=len(keys)):
        asg = dict(zip(keys, combo))
        if matrix_value(formula, asg, matrix) not in matrix.designated:
            return combo
    return None


def _matrix_entailment_countermodel(premises: Sequence[Node], conclusion: Node,
                                     matrix: TruthMatrix, keys: List[str]):
    """A ``matrix``-value assignment designating every premise but not the conclusion.

    Only called after :func:`~unicode_fol_kit.semantics.matrix.matrix_entails`
    has already reported non-entailment (same enumeration, same bound), so a
    countermodel is guaranteed to exist.
    """
    for combo in product(matrix.values, repeat=len(keys)):
        asg = dict(zip(keys, combo))
        if (all(matrix_value(p, asg, matrix) in matrix.designated for p in premises)
                and matrix_value(conclusion, asg, matrix) not in matrix.designated):
            return combo
    return None


# ===========================================================================
# (A) THF export
# ===========================================================================
#
# Type ``tv`` with |values| exhaustive, pairwise-distinct constants; connective
# functions matching the matrix's own tables, one ground equation per cell.


def _thf_preamble(matrix: TruthMatrix, names: Dict[Value, str], conns: Dict[Type[Node], str],
                   type_name: str, predicate_name: str) -> List[str]:
    """Type/constant/connective *declarations* plus distinctness + exhaustiveness."""
    ordered = list(names.keys())
    lines = [f"thf({type_name}_type, type, ( {type_name} : $tType ))."]
    for v in ordered:
        cname = names[v]
        lines.append(f"thf({cname}_decl, type, ( {cname} : {type_name} )).")
    lines.append(
        f"thf({predicate_name}_decl, type, ( {predicate_name} : ( {type_name} > $o ) )).")
    for cls, attr, arity in _matrix_defined_ops(matrix):
        cname = conns[cls]
        ty = (f"( {type_name} > {type_name} )" if arity == 1
              else f"( {type_name} > {type_name} > {type_name} )")
        lines.append(f"thf({cname}_decl, type, ( {cname} : {ty} )).")
    if len(ordered) > 1:
        pairs = [f"( {names[a]} != {names[b]} )"
                 for i, a in enumerate(ordered) for b in ordered[i + 1:]]
        lines.append(f"thf({type_name}_distinct, axiom, ( " + " & ".join(pairs) + " )).")
    disj = " | ".join(f"( X = {names[v]} )" for v in ordered)
    lines.append(
        f"thf({type_name}_exhaust, axiom, ( ! [X: {type_name}] : ( {disj} ) )).")
    return lines


def _thf_op_axioms(matrix: TruthMatrix, names: Dict[Value, str],
                    conns: Dict[Type[Node], str]) -> List[str]:
    """One THF ground equation per truth-table cell, for every op ``matrix`` defines."""
    ordered = list(names.keys())
    lines: List[str] = []
    for cls, attr, arity in _matrix_defined_ops(matrix):
        cname = conns[cls]
        table = getattr(matrix, attr)
        if arity == 1:
            for v in ordered:
                out = names[table[v]]
                lines.append(
                    f"thf({cname}_{names[v]}, axiom, "
                    f"( ( {cname} @ {names[v]} ) = {out} )).")
        else:
            for a in ordered:
                for b in ordered:
                    out = names[table[(a, b)]]
                    lines.append(
                        f"thf({cname}_{names[a]}_{names[b]}, axiom, "
                        f"( ( {cname} @ {names[a]} @ {names[b]} ) = {out} )).")
    return lines


def _thf_designated_predicate(matrix: TruthMatrix, names: Dict[Value, str],
                               type_name: str, predicate_name: str) -> str:
    """The ``des : tv > $o`` predicate, true exactly of the matrix's designated values."""
    ordered = list(names.keys())
    terms = [f"( D = {names[v]} )" for v in ordered if v in matrix.designated]
    if not terms:
        raise ValueError(f"TruthMatrix {matrix.name!r} has an empty designated set.")
    body = terms[0] if len(terms) == 1 else "( " + " | ".join(terms) + " )"
    return (f"thf({predicate_name}_def, definition, "
            f"( {predicate_name} = ( ^ [D: {type_name}] : {body} ) )).")


def _thf_eval_matrix(node: Node, names_by_key: dict, conns: Dict[Type[Node], str]) -> str:
    """Render the formula as a truth-value-typed THF term using the connective fns."""
    if isinstance(node, Atom):
        return names_by_key[node.to_unicode_str()]
    if isinstance(node, Not):
        return f"( {conns[Not]} @ {_thf_eval_matrix(node.formula, names_by_key, conns)} )"
    for cls in (And, Or, Xor, Implies, Iff):
        if isinstance(node, cls):
            return (f"( {conns[cls]} @ {_thf_eval_matrix(node.left, names_by_key, conns)} "
                    f"@ {_thf_eval_matrix(node.right, names_by_key, conns)} )")
    raise NotImplementedError(
        f"to_thf_matrix: unsupported node {type(node).__name__}.")


def to_thf_matrix(formula: Node, matrix: TruthMatrix, *,
                   value_names: Optional[Dict[Value, str]] = None,
                   conn_names: Optional[Dict[Type[Node], str]] = None,
                   type_name: str = "tv",
                   predicate_name: str = "des") -> str:
    """Emit a complete THF problem whose theorem-hood is ``matrix``-validity of ``formula``.

    Builds a self-contained TPTP **THF** problem: an ``|matrix.values|``-element
    truth-value type (one constant per value, distinctness + exhaustiveness
    axioms), the connective functions ``matrix`` tabulates -- defined by full
    case analysis, one ground equation per cell -- the designated predicate
    ``des`` (true of exactly ``matrix.designated``), and the conjecture
    ``! [valuation] : des @ <formula>`` where each propositional atom is a
    universally-quantified valuation variable. The conjecture is a **Theorem**
    iff ``formula`` is valid in ``matrix`` (:func:`~unicode_fol_kit.semantics.matrix.matrix_is_valid`).

    Propositional fragment only (``not/and/or/xor/implies/iff`` over atoms); a
    ``Quantifier`` or any modal/Lukasiewicz/sorted/lambda node raises
    ``NotImplementedError``. A formula using a connective ``matrix`` has no
    table for raises ``ValueError`` (see :func:`_check_matrix_supports`).

    ``value_names`` / ``conn_names`` let a caller pin exact constant/function
    names (and, via a dict's key order, the declaration order); anything
    unnamed gets a data-driven default. ``type_name`` / ``predicate_name``
    rename the truth-value type and the designated predicate.

    Note: the toolkit emits this problem; it does **not** run a prover. A
    finite matrix's validity is decidable, so a sound+complete HOL ATP
    (Leo-III, Satallax) can in principle discharge it.
    """
    _check_propositional(formula)
    _check_matrix_supports([formula], matrix)
    names = _resolve_value_names(matrix, value_names)
    conns = _resolve_conn_names(conn_names)
    keys = _atom_keys(formula)
    names_by_key = _assign_var_names(keys)

    designated_names = [names[v] for v in names if v in matrix.designated]
    lines = [
        f"% {matrix.name} many-valued shallow embedding of a propositional formula.",
        f"% Values: {[names[v] for v in names]}; designated: {designated_names}. "
        "Conjecture is 'Theorem' iff the formula is valid in this matrix.",
        f"% Formula: {formula.to_unicode_str()}",
    ]
    lines.extend(_thf_preamble(matrix, names, conns, type_name, predicate_name))
    lines.extend(_thf_op_axioms(matrix, names, conns))
    lines.append(_thf_designated_predicate(matrix, names, type_name, predicate_name))

    body = _thf_eval_matrix(formula, names_by_key, conns)
    if keys:
        binder = ", ".join(f"{names_by_key[k]}: {type_name}" for k in keys)
        conj = f"! [{binder}] : ( {predicate_name} @ {body} )"
    else:
        conj = f"( {predicate_name} @ {body} )"
    lines.append(f"thf(goal, conjecture, ( {conj} )).")
    return "\n".join(lines) + "\n"


def to_thf_matrix_entailment(premises: Sequence[Node], conclusion: Node, matrix: TruthMatrix, *,
                              value_names: Optional[Dict[Value, str]] = None,
                              conn_names: Optional[Dict[Type[Node], str]] = None,
                              type_name: str = "tv",
                              predicate_name: str = "des") -> str:
    """Emit a THF problem whose theorem-hood is ``matrix``-entailment of ``conclusion`` by ``premises``.

    Designation-preserving entailment: ``premises |= conclusion`` iff every
    valuation that designates **all** premises also designates the
    conclusion. The conjecture is
    ``! [valuation] : ( (des p1 & ... & des pn) => des c )``, matching
    :func:`~unicode_fol_kit.semantics.matrix.matrix_entails`.

    Same propositional fragment, rejection surface, and naming knobs as
    :func:`to_thf_matrix`.
    """
    premises = list(premises)
    for f in premises:
        _check_propositional(f)
    _check_propositional(conclusion)
    _check_matrix_supports([*premises, conclusion], matrix)
    names = _resolve_value_names(matrix, value_names)
    conns = _resolve_conn_names(conn_names)

    keys: List[str] = []
    seen = set()
    for f in [*premises, conclusion]:
        for k in _atom_keys(f):
            if k not in seen:
                seen.add(k)
                keys.append(k)
    names_by_key = _assign_var_names(keys)

    lines = [
        f"% {matrix.name} many-valued entailment.",
        "% Conjecture is 'Theorem' iff the premises entail the conclusion.",
        "% Premises: " + ("; ".join(p.to_unicode_str() for p in premises) or "(none)"),
        f"% Conclusion: {conclusion.to_unicode_str()}",
    ]
    lines.extend(_thf_preamble(matrix, names, conns, type_name, predicate_name))
    lines.extend(_thf_op_axioms(matrix, names, conns))
    lines.append(_thf_designated_predicate(matrix, names, type_name, predicate_name))

    concl = f"( {predicate_name} @ {_thf_eval_matrix(conclusion, names_by_key, conns)} )"
    if premises:
        prem = " & ".join(
            f"( {predicate_name} @ {_thf_eval_matrix(p, names_by_key, conns)} )" for p in premises)
        goal_body = f"( ( {prem} ) => {concl} )"
    else:
        goal_body = concl
    if keys:
        binder = ", ".join(f"{names_by_key[k]}: {type_name}" for k in keys)
        conj = f"! [{binder}] : {goal_body}"
    else:
        conj = goal_body
    lines.append(f"thf(goal, conjecture, ( {conj} )).")
    return "\n".join(lines) + "\n"


# ===========================================================================
# (B) Isabelle/HOL export
# ===========================================================================
#
# A self-contained, loadable theory: a datatype with |values| constructors,
# fun definitions for the connectives matching the matrix's tables, the
# designated predicate, and a lemma provable iff the formula is matrix-valid.
# Discharge with `by eval` / `by (cases ...)` / Sledgehammer.


def _isa_datatype_line(matrix: TruthMatrix, names: Dict[Value, str], type_name: str) -> str:
    ordered = list(names.keys())
    return f"datatype {type_name} = " + " | ".join(names[v] for v in ordered)


def _isa_neg_def_matrix(matrix: TruthMatrix, names: Dict[Value, str],
                         conns: Dict[Type[Node], str], type_name: str) -> str:
    cname = conns[Not]
    ordered = list(names.keys())
    eqs = [f'  "{cname} {names[v]} = {names[matrix.neg[v]]}"' for v in ordered]
    return (f'fun {cname} :: "{type_name} \\<Rightarrow> {type_name}" where\n'
            + " |\n".join(eqs))


def _isa_binop_def_matrix(matrix: TruthMatrix, names: Dict[Value, str], conns: Dict[Type[Node], str],
                           cls: type, attr: str, type_name: str) -> str:
    cname = conns[cls]
    table = getattr(matrix, attr)
    ordered = list(names.keys())
    eqs = []
    for a in ordered:
        for b in ordered:
            out = names[table[(a, b)]]
            eqs.append(f'  "{cname} {names[a]} {names[b]} = {out}"')
    return (f'fun {cname} :: "{type_name} \\<Rightarrow> {type_name} \\<Rightarrow> {type_name}" where\n'
            + " |\n".join(eqs))


def _isa_designated_def_matrix(matrix: TruthMatrix, names: Dict[Value, str],
                                predicate_name: str, type_name: str) -> str:
    ordered = list(names.keys())
    ds = [names[v] for v in ordered if v in matrix.designated]
    if not ds:
        raise ValueError(f"TruthMatrix {matrix.name!r} has an empty designated set.")
    rhs = f"(d = {ds[0]})" if len(ds) == 1 else "(" + " \\<or> ".join(f"d = {n}" for n in ds) + ")"
    return (f'definition {predicate_name} :: "{type_name} \\<Rightarrow> bool" where\n'
            f'  "{predicate_name} d \\<equiv> {rhs}"')


def _isa_matrix_prelude(theory_name: str, matrix: TruthMatrix, names: Dict[Value, str],
                         conns: Dict[Type[Node], str], type_name: str, predicate_name: str,
                         header_comments: List[str]) -> List[str]:
    """The shared theory header: datatype, connective funs, designated-predicate definition.

    Returns the lines from ``theory ... begin`` down to (and including) the
    designated-predicate definition; the caller appends its lemma(s) and the
    final ``end``.
    """
    parts = [
        f"theory {theory_name}",
        "  imports Main",
        "begin",
        "",
    ]
    parts += header_comments
    parts += ["", _isa_datatype_line(matrix, names, type_name), ""]
    for cls, attr, arity in _matrix_defined_ops(matrix):
        if arity == 1:
            parts.append(_isa_neg_def_matrix(matrix, names, conns, type_name))
        else:
            parts.append(_isa_binop_def_matrix(matrix, names, conns, cls, attr, type_name))
        parts.append("")
    parts.append(_isa_designated_def_matrix(matrix, names, predicate_name, type_name))
    parts.append("")
    return parts


def _isa_eval_matrix(node: Node, names_by_key: dict, conns: Dict[Type[Node], str]) -> str:
    if isinstance(node, Atom):
        return names_by_key[node.to_unicode_str()].lower()
    if isinstance(node, Not):
        return f"({conns[Not]} {_isa_eval_matrix(node.formula, names_by_key, conns)})"
    for cls in (And, Or, Xor, Implies, Iff):
        if isinstance(node, cls):
            return (f"({conns[cls]} {_isa_eval_matrix(node.left, names_by_key, conns)} "
                    f"{_isa_eval_matrix(node.right, names_by_key, conns)})")
    raise NotImplementedError(
        f"to_isabelle_matrix: unsupported node {type(node).__name__}.")


def _isa_forall_proof(isa_vars: List[str], predicate_name: str = "des") -> str:
    """Discharge ``\\<forall>vars. des (...)`` by exhausting the finite value-type cases.

    ``simp`` cannot reduce ``fn v`` while ``v`` is an abstract variable (e.g.
    on the LP-valid ``p \\<or> \\<not>p``), so a bare
    ``by (simp add: <predicate>_def)`` fails. Splitting every quantified
    variable into its constructors first makes each leaf ground, and
    ``simp_all`` then evaluates the ``fun`` tables.
    """
    if not isa_vars:
        return f"  by (simp add: {predicate_name}_def)"
    cases = "; ".join(f"case_tac {v}" for v in isa_vars)
    return ("  apply (intro allI)\n"
            f"  apply ({cases})\n"
            f"  by (simp_all add: {predicate_name}_def)")


def _isa_exists_proof(witness: List[str], predicate_name: str = "des") -> str:
    """Discharge ``\\<exists>vars. \\<not> des (...)`` by supplying the witness.

    ``witness`` is the counter-valuation (a value-type constructor per
    quantified variable, in binder order) computed at emit time; each
    ``rule exI`` instantiates one existential, then ``simp`` evaluates the
    now-ground body.
    """
    if not witness:
        return f"  by (simp add: {predicate_name}_def)"
    exs = ", ".join(f"rule exI[where x={w}]" for w in witness)
    return f"  by ({exs}, simp add: {predicate_name}_def)"


def to_isabelle_matrix(formula: Node, matrix: TruthMatrix, *,
                        name: str = "Matrix_Validity",
                        lemma_name: str = "matrix_validity",
                        value_names: Optional[Dict[Value, str]] = None,
                        conn_names: Optional[Dict[Type[Node], str]] = None,
                        type_name: str = "tv",
                        predicate_name: str = "des") -> str:
    """Emit a complete, loadable Isabelle/HOL theory text for ``matrix``-validity of ``formula``.

    Produces a ``theory <name> ... begin ... end`` snippet: an
    ``|matrix.values|``-constructor ``datatype``, ``fun`` definitions of every
    connective ``matrix`` tabulates, the designated predicate (true of exactly
    ``matrix.designated``), and a ``lemma`` that **always loads**:

      * if ``formula`` is valid in ``matrix``
        (:func:`~unicode_fol_kit.semantics.matrix.matrix_is_valid`), the
        lemma is ``\\<forall> valuation. des (<formula>)``;
      * if it is **invalid**, the lemma is the *refutation*
        ``\\<exists> valuation. \\<not> des (<formula>)`` (which then holds).

    Either way the lemma encodes the validity verdict and is **discharged by a
    real proof** Isabelle accepts: the ``\\<forall>`` form by exhausting each
    quantified variable's constructors (``case_tac`` + ``simp_all``); the
    ``\\<exists>`` refutation form by supplying the counter-valuation
    (computed by :func:`~unicode_fol_kit.semantics.matrix.matrix_is_valid`'s
    sibling enumeration) as ``rule exI`` witnesses, then ``simp``. A leading
    comment states the verdict so the reader knows which form was emitted.

    Same propositional fragment, rejection surface, and naming knobs
    (``value_names``/``conn_names``/``type_name``/``predicate_name``) as
    :func:`to_thf_matrix`; ``name`` is the Isabelle theory name and
    ``lemma_name`` the lemma's label.

    Note: the toolkit emits the theory; it does **not** run Isabelle. The
    verdict and witness come from the toolkit's own decision procedure
    (:mod:`unicode_fol_kit.semantics.matrix`), cross-checked in the tests.
    """
    _check_propositional(formula)
    _check_matrix_supports([formula], matrix)
    names = _resolve_value_names(matrix, value_names)
    conns = _resolve_conn_names(conn_names)
    keys = _atom_keys(formula)
    names_by_key = _assign_var_names(keys)
    isa_vars = [names_by_key[k].lower() for k in keys]

    valid = matrix_is_valid(formula, matrix)
    body = _isa_eval_matrix(formula, names_by_key, conns)
    if keys:
        binder = " ".join(isa_vars)
        if valid:
            lemma = f"  \"\\<forall>{binder}. {predicate_name} ({body})\""
            proof = _isa_forall_proof(isa_vars, predicate_name)
        else:
            lemma = f"  \"\\<exists>{binder}. \\<not> {predicate_name} ({body})\""
            witness_values = _matrix_falsifying_assignment(formula, matrix, keys)
            proof = _isa_exists_proof([names[v] for v in witness_values], predicate_name)
    else:
        lemma = (f"  \"{predicate_name} ({body})\"" if valid
                 else f"  \"\\<not> {predicate_name} ({body})\"")
        proof = f"  by (simp add: {predicate_name}_def)"

    verdict = "VALID" if valid else "INVALID (lemma is the refutation)"
    designated_names = [names[v] for v in names if v in matrix.designated]
    header = [
        f"(* {matrix.name} many-valued shallow embedding of a propositional formula. *)",
        f"(* Designated: {designated_names}. Verdict: {verdict}. *)",
        f"(* Formula: {formula.to_unicode_str()} *)",
    ]
    parts = _isa_matrix_prelude(name, matrix, names, conns, type_name, predicate_name, header)
    parts.append(f"lemma {lemma_name}:")
    parts.append(lemma)
    parts.append(proof)
    parts.append("")
    parts.append("end")
    return "\n".join(parts) + "\n"


def to_isabelle_matrix_entailment(premises: Sequence[Node], conclusion: Node, matrix: TruthMatrix, *,
                                   name: str = "Matrix_Entailment",
                                   lemma_name: str = "matrix_entailment",
                                   value_names: Optional[Dict[Value, str]] = None,
                                   conn_names: Optional[Dict[Type[Node], str]] = None,
                                   type_name: str = "tv",
                                   predicate_name: str = "des") -> str:
    """Emit a loadable Isabelle/HOL theory whose lemma is ``matrix``-entailment.

    Emits a lemma that **always loads**, mirroring
    :func:`~unicode_fol_kit.semantics.matrix.matrix_entails`:

      * if ``premises |= conclusion`` in ``matrix``, the lemma is
        ``\\<forall> valuation. (des p1 \\<and> ... ) \\<longrightarrow> des c``;
      * otherwise it is the countermodel statement
        ``\\<exists> valuation. (des p1 \\<and> ... ) \\<and> \\<not> des c``.

    The verdict and (when non-entailing) the countermodel witness come from
    :func:`~unicode_fol_kit.semantics.matrix.matrix_entails`'s enumeration.

    Same propositional fragment, rejection surface, and naming knobs as
    :func:`to_isabelle_matrix`.
    """
    premises = list(premises)
    for f in premises:
        _check_propositional(f)
    _check_propositional(conclusion)
    _check_matrix_supports([*premises, conclusion], matrix)
    names = _resolve_value_names(matrix, value_names)
    conns = _resolve_conn_names(conn_names)

    keys: List[str] = []
    seen = set()
    for f in [*premises, conclusion]:
        for k in _atom_keys(f):
            if k not in seen:
                seen.add(k)
                keys.append(k)
    names_by_key = _assign_var_names(keys)
    isa_vars = [names_by_key[k].lower() for k in keys]

    valid = matrix_entails(premises, conclusion, matrix)
    concl = f"{predicate_name} ({_isa_eval_matrix(conclusion, names_by_key, conns)})"
    if premises:
        prem = " \\<and> ".join(
            f"{predicate_name} ({_isa_eval_matrix(p, names_by_key, conns)})" for p in premises)
        if valid:
            body = f"({prem}) \\<longrightarrow> {concl}"
        else:
            body = f"({prem}) \\<and> \\<not> {concl}"
    else:
        body = concl if valid else f"\\<not> {concl}"
    if keys:
        binder = " ".join(isa_vars)
        q = "\\<forall>" if valid else "\\<exists>"
        lemma = f"  \"{q}{binder}. {body}\""
        if valid:
            proof = _isa_forall_proof(isa_vars, predicate_name)
        else:
            witness_values = _matrix_entailment_countermodel(premises, conclusion, matrix, keys)
            proof = _isa_exists_proof([names[v] for v in witness_values], predicate_name)
    else:
        lemma = f"  \"{body}\""
        proof = f"  by (simp add: {predicate_name}_def)"

    verdict = "ENTAILS" if valid else "DOES NOT ENTAIL (lemma is a countermodel)"
    header = [
        f"(* {matrix.name} many-valued entailment. *)",
        f"(* Verdict: {verdict}. *)",
        "(* Premises: " + ("; ".join(p.to_unicode_str() for p in premises) or "(none)") + " *)",
        f"(* Conclusion: {conclusion.to_unicode_str()} *)",
    ]
    parts = _isa_matrix_prelude(name, matrix, names, conns, type_name, predicate_name, header)
    parts.append(f"lemma {lemma_name}:")
    parts.append(lemma)
    parts.append(proof)
    parts.append("")
    parts.append("end")
    return "\n".join(parts) + "\n"


# ===========================================================================
# (C) Legacy K3/LP-only entry points: thin delegation to the generic exports.
# ===========================================================================
#
# K3_MATRIX / LP_MATRIX (semantics.matrix) reproduce the strong-Kleene tables
# exactly (cross-checked in tests/test_matrix.py); these wrappers just pin the
# historical constant/function names so the emitted text keeps its old shape.

_K3LP_VALUE_NAMES = {1.0: "tT", 0.5: "tB", 0.0: "tF"}
_K3LP_CONN_NAMES = {
    Not: "kneg", And: "kand", Or: "kor", Implies: "kimp", Iff: "kiff", Xor: "kxor",
}


def to_thf_k3lp(formula: Node, system: str = "K3") -> str:
    """Emit a complete THF problem whose theorem-hood is K3/LP validity of ``formula``.

    A thin wrapper around :func:`to_thf_matrix` with ``system``'s matrix
    (``K3_MATRIX`` / ``LP_MATRIX`` from :mod:`unicode_fol_kit.semantics.matrix`)
    and the historical constant/function names
    (``tT``/``tB``/``tF``, ``kneg``/``kand``/``kor``/``kimp``/``kiff``/``kxor``).
    See :func:`to_thf_matrix` for the full contract; ``system`` is ``"K3"``
    (designates {T}) or ``"LP"`` (designates {T, B}).
    """
    _check_system(system)
    return to_thf_matrix(formula, _K3LP_MATRICES[system],
                          value_names=_K3LP_VALUE_NAMES, conn_names=_K3LP_CONN_NAMES)


def to_thf_k3lp_entailment(premises, conclusion, system: str = "K3") -> str:
    """Emit a THF problem whose theorem-hood is the K3/LP *entailment* of ``conclusion`` by ``premises``.

    A thin wrapper around :func:`to_thf_matrix_entailment` with ``system``'s
    matrix and the historical K3/LP constant/function names. This is where K3
    and LP diverge: the explosion ``[P, ~P] |= Q`` is a **Theorem** under K3
    (vacuously -- P and ~P are never jointly designated) but **not** under LP
    (at P = B the premises are designated yet Q may be F), so LP is
    paraconsistent. Mirrors :func:`unicode_fol_kit.semantics.manyvalued.entails`.
    """
    _check_system(system)
    return to_thf_matrix_entailment(premises, conclusion, _K3LP_MATRICES[system],
                                     value_names=_K3LP_VALUE_NAMES, conn_names=_K3LP_CONN_NAMES)


def to_isabelle_k3lp(formula: Node, system: str = "K3") -> str:
    """Emit a complete, loadable Isabelle/HOL theory text for K3/LP validity.

    A thin wrapper around :func:`to_isabelle_matrix` with ``system``'s matrix,
    the historical K3/LP constant/function names, and the historical theory/
    lemma names (``K3LP_Validity`` / ``k3lp_validity``). See
    :func:`to_isabelle_matrix` for the full contract (verdict-dependent lemma
    shape, proof-by-case-split/witness, honesty note).
    """
    _check_system(system)
    return to_isabelle_matrix(formula, _K3LP_MATRICES[system],
                               name="K3LP_Validity", lemma_name="k3lp_validity",
                               value_names=_K3LP_VALUE_NAMES, conn_names=_K3LP_CONN_NAMES)


def to_isabelle_k3lp_entailment(premises, conclusion, system: str = "K3") -> str:
    """Emit a loadable Isabelle/HOL theory whose lemma is the K3/LP entailment.

    A thin wrapper around :func:`to_isabelle_matrix_entailment` with
    ``system``'s matrix, the historical K3/LP constant/function names, and the
    historical theory/lemma names (``K3LP_Entailment`` / ``k3lp_entailment``).
    The K3/LP split shows up here -- explosion ``[P, ~P] |= Q`` is valid under
    K3 (the ``\\<forall>``/``\\<longrightarrow>`` form) but invalid under LP
    (the ``\\<exists>`` countermodel form).
    """
    _check_system(system)
    return to_isabelle_matrix_entailment(
        premises, conclusion, _K3LP_MATRICES[system],
        name="K3LP_Entailment", lemma_name="k3lp_entailment",
        value_names=_K3LP_VALUE_NAMES, conn_names=_K3LP_CONN_NAMES)
