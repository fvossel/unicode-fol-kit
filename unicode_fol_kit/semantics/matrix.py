"""Finite-valued logical matrices: a generalisation of the K3 / LP three-valued layer.

A *logical matrix* is a finite set of truth values, a distinguished subset of
**designated** values (those that count as assertible), and a truth table for each
connective. Validity is "designated under every assignment", satisfiability is
"designated under some assignment", and Γ ⊨ φ is "every assignment that designates
all of Γ designates φ". This module makes that schema first-class so any finite
many-valued logic — not just the hard-wired ``{0, ½, 1}`` of
:mod:`unicode_fol_kit.semantics.manyvalued` — can be evaluated and decided.

Three matrices ship built in:

- :data:`K3_MATRIX` — Kleene's strong three-valued logic (designate ``{1}``);
- :data:`LP_MATRIX` — Priest's Logic of Paradox (designate ``{½, 1}``);
- :data:`FDE_MATRIX` — the Belnap–Dunn four-valued logic **FDE** (first-degree
  entailment), values ``T``/``F``/``N`` (neither)/``B`` (both), designate the
  *true-containing* values ``{T, B}``. FDE is both paraconsistent (``p ∧ ¬p ⊭ q``)
  and paracomplete (``p ⊭ q ∨ ¬q``), and — unlike K3/LP — has **no** logical
  truths at all (even ``p → p`` fails, taking value ``N`` at ``N``).

K3 and LP are re-expressed here as matrices, so this layer reproduces the existing
three-valued decisions exactly (cross-checked in the tests). Build your own with
:meth:`TruthMatrix.from_functions`.

Public API: :class:`TruthMatrix`, :func:`matrix_value`, :func:`matrix_is_valid`,
:func:`matrix_is_satisfiable`, :func:`matrix_entails`, and the matrices
:data:`K3_MATRIX`, :data:`LP_MATRIX`, :data:`FDE_MATRIX`. :data:`MATRICES` maps the
names ``"K3"`` / ``"LP"`` / ``"FDE"`` to them.
"""

from dataclasses import dataclass
from itertools import product
from typing import Callable, Dict, FrozenSet, Hashable, List, Optional, Sequence, Tuple

from ..fol.nodes import Node, Atom, Not, And, Or, Xor, Implies, Iff, Quantifier
from .manyvalued import _atom_keys, _instantiate, _ground, _reject_if_unsupported, MAX_MODELS

Value = Hashable


@dataclass(frozen=True)
class TruthMatrix:
    """A finite logical matrix: values, designated values, and connective tables.

    The connective tables are plain dicts (``neg[v]``, ``conj[(a, b)]``, …) so a
    matrix is fully data-driven; build one directly, or — more conveniently — with
    :meth:`from_functions` from value-level operations. ``∀`` / ``∃`` are read as the
    iterated ``conj`` / ``disj`` over a finite domain (a generalised min / max), so
    the matrix needs no separate quantifier tables.
    """

    name: str
    values: Tuple[Value, ...]
    designated: FrozenSet[Value]
    neg: Dict[Value, Value]
    conj: Dict[Tuple[Value, Value], Value]
    disj: Dict[Tuple[Value, Value], Value]
    impl: Dict[Tuple[Value, Value], Value]
    iff: Dict[Tuple[Value, Value], Value]
    xor: Dict[Tuple[Value, Value], Value]

    @staticmethod
    def from_functions(
        name: str,
        values: Sequence[Value],
        designated: Sequence[Value],
        neg: Callable[[Value], Value],
        conj: Callable[[Value, Value], Value],
        disj: Callable[[Value, Value], Value],
        impl: Optional[Callable[[Value, Value], Value]] = None,
    ) -> "TruthMatrix":
        """Materialise a matrix from value-level operations.

        ``impl`` defaults to the **material** conditional ``¬a ∨ b``; the
        biconditional is ``(a→b) ∧ (b→a)`` and exclusive-or is ``¬(a↔b)``. Every
        operation is checked to land back in ``values`` (a closed matrix), and every
        designated value to be a value, so a malformed table is caught at build time.
        """
        values = tuple(values)
        vset = set(values)
        if impl is None:
            impl = lambda a, b: disj(neg(a), b)
        iff = lambda a, b: conj(impl(a, b), impl(b, a))
        xor = lambda a, b: neg(iff(a, b))

        def _u(fn):
            return {v: _check(fn(v), vset, name) for v in values}

        def _b(fn):
            return {(a, b): _check(fn(a, b), vset, name) for a in values for b in values}

        for d in designated:
            if d not in vset:
                raise ValueError(f"TruthMatrix {name!r}: designated value {d!r} is not a value.")
        return TruthMatrix(
            name=name, values=values, designated=frozenset(designated),
            neg=_u(neg), conj=_b(conj), disj=_b(disj),
            impl=_b(impl), iff=_b(iff), xor=_b(xor),
        )

    def is_designated(self, v: Value) -> bool:
        """True iff ``v`` is a designated (assertible) value of this matrix."""
        return v in self.designated


def _check(v: Value, vset, name: str) -> Value:
    """Verify a connective result is a legal value of the matrix, else raise."""
    if v not in vset:
        raise ValueError(
            f"TruthMatrix {name!r}: a connective produced {v!r}, which is not one of "
            f"the matrix values {sorted(map(str, vset))}.")
    return v


def matrix_value(formula: Node, valuation: Dict[str, Value],
                 matrix: TruthMatrix, domain: Optional[Sequence[str]] = None) -> Value:
    """Evaluate ``formula`` to a matrix value under ``valuation``.

    ``valuation`` maps each ground atom's ``to_unicode_str()`` key to a value of
    ``matrix``. Quantifiers fold ``conj`` (∀) / ``disj`` (∃) over ``domain`` (a set
    of constant names), generalising min/max. A missing atom key raises ``KeyError``;
    a value outside the matrix raises ``ValueError``; a modal/fuzzy/sorted/lambda
    node is rejected with the same message :func:`kleene_value` uses.
    """
    if isinstance(formula, Atom):
        key = formula.to_unicode_str()
        if key not in valuation:
            raise KeyError(f"No value for ground atom {key!r} in the valuation.")
        v = valuation[key]
        return _check(v, set(matrix.values), matrix.name)
    if isinstance(formula, Not):
        return matrix.neg[matrix_value(formula.formula, valuation, matrix, domain)]
    if isinstance(formula, (And, Or, Xor, Implies, Iff)):
        a = matrix_value(formula.left, valuation, matrix, domain)
        b = matrix_value(formula.right, valuation, matrix, domain)
        table = {And: matrix.conj, Or: matrix.disj, Implies: matrix.impl,
                 Iff: matrix.iff, Xor: matrix.xor}[type(formula)]
        return table[(a, b)]
    if isinstance(formula, Quantifier):
        if not domain:
            raise ValueError("Evaluating a Quantifier requires a non-empty 'domain'.")
        vals = [matrix_value(_ground(formula.formula, formula.variable.name, d),
                             valuation, matrix, domain) for d in domain]
        combine = matrix.conj if formula.type in ("∀", "forall") else matrix.disj
        acc = vals[0]
        for nxt in vals[1:]:
            acc = combine[(acc, nxt)]
        return acc
    _reject_if_unsupported(formula)


def _prepare(formulas: Sequence[Node], matrix: TruthMatrix,
             domain: Optional[Sequence[str]]):
    """Ground quantifiers, collect ground-atom keys, and bound the enumeration."""
    grounded: List[Node] = []
    for f in formulas:
        if f.count(Quantifier):
            if not domain:
                raise ValueError("Deciding a quantified formula requires a non-empty 'domain'.")
            grounded.append(_instantiate(f, set(domain)))
        else:
            grounded.append(f)
    keys = _atom_keys(*grounded)
    total = len(matrix.values) ** len(keys)
    if total > MAX_MODELS:
        raise ValueError(
            f"Matrix enumeration would visit {len(matrix.values)}**{len(keys)} = "
            f"{total} assignments, above MAX_MODELS = {MAX_MODELS}. Reduce the number "
            "of distinct ground atoms, or raise manyvalued.MAX_MODELS.")
    return keys, grounded


def matrix_is_valid(formula: Node, matrix: TruthMatrix,
                    domain: Optional[Sequence[str]] = None) -> bool:
    """True iff ``formula`` is designated under *every* assignment over ``matrix``.

    Enumerates ``len(matrix.values) ** n`` assignments of the ``n`` distinct ground
    atoms (after grounding quantifiers over ``domain``). Exponential in ``n``; capped
    at :data:`manyvalued.MAX_MODELS`.
    """
    keys, (grounded,) = _prepare([formula], matrix, domain)
    return all(
        matrix_value(grounded, dict(zip(keys, combo)), matrix, domain) in matrix.designated
        for combo in product(matrix.values, repeat=len(keys))
    )


def matrix_is_satisfiable(formula: Node, matrix: TruthMatrix,
                          domain: Optional[Sequence[str]] = None) -> bool:
    """True iff ``formula`` is designated under *some* assignment over ``matrix``."""
    keys, (grounded,) = _prepare([formula], matrix, domain)
    return any(
        matrix_value(grounded, dict(zip(keys, combo)), matrix, domain) in matrix.designated
        for combo in product(matrix.values, repeat=len(keys))
    )


def matrix_entails(premises: Sequence[Node], conclusion: Node, matrix: TruthMatrix,
                   domain: Optional[Sequence[str]] = None) -> bool:
    """True iff every assignment designating all ``premises`` designates ``conclusion``.

    Matrix consequence: ``Γ ⊨ φ`` holds when no assignment over ``matrix`` makes every
    premise designated yet the conclusion undesignated.
    """
    formulas = list(premises) + [conclusion]
    keys, grounded = _prepare(formulas, matrix, domain)
    prem, concl = grounded[:-1], grounded[-1]
    for combo in product(matrix.values, repeat=len(keys)):
        val = dict(zip(keys, combo))
        if all(matrix_value(p, val, matrix, domain) in matrix.designated for p in prem):
            if matrix_value(concl, val, matrix, domain) not in matrix.designated:
                return False
    return True


# --------------------------------------------------------------------------- #
# Built-in matrices.
# --------------------------------------------------------------------------- #

# K3 / LP over {0, ½, 1} with the strong-Kleene tables — the same semantics as
# semantics.manyvalued, re-expressed as matrices (cross-checked in the tests).
_THREE = (0.0, 0.5, 1.0)
_k_neg = lambda x: 1.0 - x
_k_conj = min
_k_disj = max
_k_impl = lambda a, b: max(1.0 - a, b)

K3_MATRIX = TruthMatrix.from_functions(
    "K3", _THREE, designated=(1.0,),
    neg=_k_neg, conj=_k_conj, disj=_k_disj, impl=_k_impl)
LP_MATRIX = TruthMatrix.from_functions(
    "LP", _THREE, designated=(0.5, 1.0),
    neg=_k_neg, conj=_k_conj, disj=_k_disj, impl=_k_impl)


# Belnap–Dunn FDE: each value is a (has-true, has-false) bit pair.
#   T = told-true-only, F = told-false-only, N = told-neither, B = told-both.
_FDE_BITS = {"T": (1, 0), "F": (0, 1), "N": (0, 0), "B": (1, 1)}
_FDE_OF = {bits: name for name, bits in _FDE_BITS.items()}


def _fde_neg(x):
    t, f = _FDE_BITS[x]
    return _FDE_OF[(f, t)]


def _fde_conj(a, b):
    at, af = _FDE_BITS[a]
    bt, bf = _FDE_BITS[b]
    return _FDE_OF[(at & bt, af | bf)]


def _fde_disj(a, b):
    at, af = _FDE_BITS[a]
    bt, bf = _FDE_BITS[b]
    return _FDE_OF[(at | bt, af & bf)]


FDE_MATRIX = TruthMatrix.from_functions(
    "FDE", ("F", "N", "T", "B"), designated=("T", "B"),
    neg=_fde_neg, conj=_fde_conj, disj=_fde_disj)   # material → via ¬a ∨ b


MATRICES = {"K3": K3_MATRIX, "LP": LP_MATRIX, "FDE": FDE_MATRIX}
