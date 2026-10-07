"""Declared converse / argument-permutation axioms — an opt-in equivalence bridge.

Two predicates can denote the same relation with their arguments swapped —
``LovedBy(x, y)`` and ``Loves(y, x)`` — or, more generally, permuted for any
arity: ``Between(a, b, c)`` and ``BetweenRev(c, b, a)``. Neither
:func:`~unicode_logic_kit.eval.canonical.exact_match` (which never renames a
predicate) nor :func:`~unicode_logic_kit.eval.predicate_match.align_symbols`
(which renames predicate *names* but never touches argument *order* — see
that module's docstring) closes this gap, and deliberately so: automatically
GUESSING that ``LovedBy``/``Loves`` are converses from lexical similarity
alone is undecidable-from-the-AST and would just as happily "forgive" a
genuine subject/object-swap translation ERROR (see roadmap item C32's
rejection). This module takes the opposite approach: the CALLER declares the
bridge explicitly, per comparison, and only the solver level of
:func:`unicode_logic_kit.eval.equivalence.equivalent` ever consumes it — see
that module for how ``converses=`` is threaded through and tagged with its
own ``method_used`` value (``"solver_modulo_converses"``), never merged into
plain equivalence.

A declaration is a plain, JSON-friendly 3-tuple::

    (a_key, b_key, permutation)

where ``a_key`` / ``b_key`` are ``(name, arity)`` predicate keys — the same
convention :mod:`~unicode_logic_kit.eval.predicate_match` uses for its own
symbol inventories — and ``permutation`` is a tuple of ``arity`` distinct
indices into ``range(arity)``. :func:`converse_axioms` turns a list of these
into one closed biconditional sentence per declaration:

    ∀v0 … v_{n-1} (A(v0, …, v_{n-1}) ↔ B(v_perm[0], …, v_perm[n-1]))

so ``(("LovedBy", 2), ("Loves", 2), (1, 0))`` builds
``∀v0 ∀v1 (LovedBy(v0, v1) ↔ Loves(v1, v0))``. :func:`validate_converses`
runs the structural sanity checks (arity match, permutation validity,
no self-pair, no built-in predicate, no duplicate/contradictory pair) that
:func:`converse_axioms` also runs internally before building anything, so a
malformed declaration is refused with :class:`ValueError` before any Z3 call
is even attempted.

On the Z3-domain-sort question a caller might reasonably worry about: this
kit's whole classical export (:class:`~unicode_logic_kit.fol.nodes.Z3Env`) uses
exactly ONE Z3 sort for every term, always (``_SORT = z3.DeclareSort("S")`` in
``fol/_fol_nodes.py`` — confirmed by inspection, the only ``DeclareSort`` call
in the codebase), and a predicate is interned purely by ``(name, arity)`` —
its Z3 domain is always ``[_SORT] * arity``, regardless of whether the atom
sits under a plain :class:`~unicode_logic_kit.fol.nodes.Quantifier` or under a
:class:`~unicode_logic_kit.fol.nodes.SortedQuantifier` (which auto-relativises
to plain FOL over the SAME single sort, guarded by a unary sort-membership
predicate — see ``fol._msfl_nodes.to_fol``). So a plain, unsorted axiom built
here for a predicate pair ``(name, arity)`` interns to the IDENTICAL Z3
function declaration the compared formulas themselves use for that pair,
many-sorted or not — there is no second Z3 domain-sort family for it to
silently diverge into. See :mod:`unicode_logic_kit.eval.equivalence`'s
docstring for the differential test that proves this bridges correctly under
:class:`~unicode_logic_kit.fol.nodes.SortedQuantifier` input, not just for
unsorted formulas.
"""

from typing import Sequence, Tuple

from unicode_logic_kit.fol.nodes import Node, Atom, Iff, Quantifier, Variable
from .validate import _BUILTIN_PREDS

__all__ = ["ConverseDeclaration", "validate_converses", "converse_axioms"]

#: A predicate symbol key: ``(name, arity)`` — the same convention
#: :data:`unicode_logic_kit.eval.predicate_match._SymKey` uses.
_SymKey = Tuple[str, int]

#: One declared converse: ``A`` (natural argument order) is biconditional
#: with ``B`` applied to ``A``'s arguments permuted by ``permutation`` — see
#: the module docstring for the exact axiom shape.
ConverseDeclaration = Tuple[_SymKey, _SymKey, Tuple[int, ...]]


def validate_converses(declarations: Sequence[ConverseDeclaration]) -> None:
    """Raise :class:`ValueError` for any structurally invalid declaration.

    Checked per declaration, in this order:

    * ``a_key`` and ``b_key`` have the same arity (a converse cannot relate
      predicates of different arity — there is no argument permutation
      between them);
    * ``permutation`` has exactly ``arity`` entries;
    * ``permutation`` is a bijection on ``range(arity)`` (every position
      0..arity-1 appears exactly once — a real permutation, not a partial or
      repeating map that would silently drop or duplicate an argument);
    * ``a_key != b_key`` (a predicate cannot be declared its own converse);
    * neither predicate name is a built-in (``=``, ``≠``, ``<``, ``>``, ``≤``,
      ``≥`` — see :data:`unicode_logic_kit.eval.validate._BUILTIN_PREDS`), since
      those already have fixed Z3 semantics an extra biconditional cannot
      touch meaningfully and must not be allowed to appear to.

    Checked across the whole list: the same UNORDERED pair ``{a_key, b_key}``
    is never declared twice — this single check also catches two genuinely
    CONTRADICTORY declarations for the same pair (e.g. two different
    permutations for ``{LovedBy, Loves}``), since both shapes collide on the
    same unordered-pair key. A chain of declarations over DISTINCT pairs
    (``A~B``, ``B~C``) is explicitly allowed and composes correctly — each
    axiom is independent, so the solver sees both biconditionals as separate
    premises.

    Never touches Z3 or any other backend — pure structural validation over
    the declarations alone, so it is always safe (and cheap) to call before
    committing to a solver run.
    """
    seen_pairs: set = set()
    for a_key, b_key, permutation in declarations:
        a_name, a_arity = a_key
        b_name, b_arity = b_key

        if a_arity != b_arity:
            raise ValueError(
                f"validate_converses: arity mismatch between {a_key!r} and "
                f"{b_key!r} — a converse permutation needs equal arity")

        if len(permutation) != a_arity:
            raise ValueError(
                f"validate_converses: permutation {permutation!r} has "
                f"{len(permutation)} entries, expected {a_arity} for {a_key!r}")

        if sorted(permutation) != list(range(a_arity)):
            raise ValueError(
                f"validate_converses: permutation {permutation!r} for "
                f"{a_key!r} is not a bijection on range({a_arity})")

        if a_key == b_key:
            raise ValueError(
                f"validate_converses: {a_key!r} cannot be declared its own "
                "converse")

        for name in (a_name, b_name):
            if name in _BUILTIN_PREDS:
                raise ValueError(
                    f"validate_converses: {name!r} is a built-in predicate "
                    "and cannot be declared a converse")

        pair = frozenset((a_key, b_key))
        if pair in seen_pairs:
            raise ValueError(
                f"validate_converses: the pair {{{a_key!r}, {b_key!r}}} is "
                "already declared — a predicate pair may only be declared "
                "converses once (this also rejects two contradictory "
                "permutations for the same pair)")
        seen_pairs.add(pair)


def converse_axioms(declarations: Sequence[ConverseDeclaration]) -> Tuple[Node, ...]:
    """Build one closed biconditional sentence per declared converse.

    Validates first (:func:`validate_converses` — every declaration must be
    structurally sound before anything is built) and then, for each
    ``(a_key, b_key, permutation)`` with ``a_key = (a_name, arity)`` and
    ``b_key = (b_name, _)``, builds fresh bound variables ``v0 .. v_{n-1}``
    (fresh PER AXIOM — reused across axioms is fine, since each axiom is its
    own independently-scoped closed sentence, but never shared with the
    caller's own formulas) and the sentence::

        ∀v0 … v_{n-1} (A(v0, …, v_{n-1}) ↔ B(v_perm[0], …, v_perm[n-1]))

    i.e. ``A``'s arguments are the fresh variables in NATURAL order and
    ``B``'s are the same variables reordered by ``permutation`` — so
    ``permutation=(1, 0)`` for a binary pair yields
    ``A(v0, v1) ↔ B(v1, v0)``, the plain converse reading.

    Each returned sentence is a pure biconditional between two otherwise-
    unconstrained (uninterpreted) predicates — a DEFINITIONAL extension: for
    any valuation of one side there is always a valuation of the other that
    satisfies the axiom, so asserting it can never make a previously
    satisfiable axiom set unsatisfiable, and can never manufacture an
    entailment between predicates it does not mention (see
    :mod:`unicode_logic_kit.eval.equivalence`'s module docstring for the
    worked-through soundness argument this relies on).

    Returns:
        A tuple of closed :class:`~unicode_logic_kit.fol.nodes.Node` sentences,
        same length and order as ``declarations``, each ``.to_z3()``-able and
        ``.to_unicode_str()``-able like any other formula node.

    Raises:
        ValueError: via :func:`validate_converses`, if any declaration is
            structurally invalid.
    """
    validate_converses(declarations)

    axioms = []
    for a_key, b_key, permutation in declarations:
        a_name, arity = a_key
        b_name, _b_arity = b_key

        variables = tuple(Variable(f"v{j}") for j in range(arity))
        atom_a = Atom(a_name, variables)
        atom_b = Atom(b_name, tuple(variables[p] for p in permutation))

        axiom: Node = Iff(atom_a, atom_b)
        for v in reversed(variables):
            axiom = Quantifier("∀", v, axiom)
        axioms.append(axiom)

    return tuple(axioms)
