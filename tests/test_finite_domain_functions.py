"""Differential tests for Function-symbol support across the finite-domain
pipeline (the C26 closure) — checked against TWO independent routes at once,
per the roadmap item's own test_oracle:

1. :class:`~unicode_fol_kit.atp.clingo_backend.ClingoBackend` (a live
   solver, ``clingo`` 5.8.1 is installed) against
   :func:`~unicode_fol_kit.semantics.modelfinder.find_countermodel` — the
   kit's OWN from-scratch, brute-force, independent model finder, which is
   already Function-capable (``modelfinder._Signature.scan``'s ``Function``
   branch; ``modelfinder._interpretations``'s per-symbol enumeration
   includes function interpretations) — REFUTED-by-clingo must agree with
   "a countermodel exists"-by-modelfinder.
2. The reconstructed :class:`~unicode_fol_kit.semantics.structures.FiniteStructure`'s
   function extension, evaluated back through
   :func:`~unicode_fol_kit.semantics.model_eval.evaluate` (the actual
   checker :func:`~unicode_fol_kit.atp.finite_domain.verify_model` already
   ran internally), is cross-checked a THIRD way against
   :func:`~unicode_fol_kit.semantics.tarski.satisfies` over an EQUIVALENT
   :class:`~unicode_fol_kit.semantics.tarski.Structure` built from the same
   extension data (:func:`_to_tarski_structure`) — two independently
   implemented evaluators over the same ground facts must agree.

Three small, hand-checked algebraic theories — refuting commutativity,
associativity and idempotence of an explicit binary operation table named
``op`` (never ``+``/``-``/``*``/``/``, so the excluded-arithmetic-operator
carve-out never gets in the way; see ``atp.finite_domain``'s "Fragment
boundary" section) — are the test_oracle's own suggested shape, scaled down
from its illustrative "order-6 non-abelian" example to the SMALLEST domain
that can witness each failure: a binary function's brute-force candidate
count grows as ``size ** (size ** 2)`` (``modelfinder._candidate_count``),
so a size-2 domain (16 candidate tables) is comfortably fast while even
size 6 (``6 ** 36``) would never finish. All three properties below turn out
to already fail on a 2-element domain, so none of the three tests needs a
larger one — see each test's own hand-derivation.

:class:`~unicode_fol_kit.atp.minizinc_backend.MinizincBackend`'s OWN
Function-bearing ``decide()`` path is covered separately, offline (MiniZinc
is not installed in this environment — see that module's own docstring), in
``tests/test_minizinc_backend.py``'s
``test_decide_refuted_with_a_verified_function_bearing_countermodel``. This
file is ClingoBackend-only because it is the one LIVE solver available here,
and a live cross-solver differential needs a live solver on at least one
side to be worth running for real rather than against a canned fixture.
"""

import pytest

clingo = pytest.importorskip("clingo")

from unicode_fol_kit.fol.nodes import Variable, Constant, Function, Atom, Not, Quantifier
from unicode_fol_kit.fol.signature import Signature
from unicode_fol_kit.semantics import tarski
from unicode_fol_kit.semantics.structures import FiniteStructure, structure_from_dict
from unicode_fol_kit.semantics.model_eval import evaluate as evaluate_in_structure
from unicode_fol_kit.semantics.modelfinder import find_countermodel
from unicode_fol_kit.atp.clingo_backend import ClingoBackend
from unicode_fol_kit.atp.protocol import REFUTED

_backend = ClingoBackend()
_MAX_SIZE = 3   # generous relative to every hand-derived minimal size (2) below


def _to_tarski_structure(fs: FiniteStructure, signature: Signature) -> tarski.Structure:
    """Adapt a (stored-extension-only) FiniteStructure into an EQUIVALENT
    tarski.Structure — same domain, same constants, same ground facts —
    using ``signature`` to decide which ``(name, arity+1)`` extension keys
    are FUNCTIONS (converted to tarski's own ``{arg_tuple: result}`` dict
    convention) versus ordinary PREDICATES, exactly the distinction
    :func:`~unicode_fol_kit.atp.finite_domain.structure_from_solution` uses
    a :class:`Signature` to make. No new evaluation logic here — a data
    adapter between two independently implemented structure
    representations, so :func:`tarski.satisfies` can be run over the exact
    same facts :func:`evaluate_in_structure` already checked."""
    functions = {}
    for name, decl in signature.functions.items():
        key = (name, decl.arity + 1)
        functions[(name, decl.arity)] = {
            row[:-1]: row[-1] for row in fs.extensions.get(key, frozenset())
        }
    predicates = {
        (name, decl.arity): set(fs.extensions.get((name, decl.arity), frozenset()))
        for name, decl in signature.predicates.items()
    }
    return tarski.Structure(domain=fs.domain, constants=dict(fs.constants),
                            functions=functions, predicates=predicates)


def _assert_refuted_and_cross_checked(formula, premises, expected_min_size):
    """Shared assertion sequence for all three cases below:

    1. :meth:`ClingoBackend.decide` REFUTES at the hand-derived minimal size,
       verified internally (``detail is None``).
    2. :func:`~unicode_fol_kit.semantics.modelfinder.find_countermodel`
       independently agrees a countermodel of the SAME question exists —
       route #1 (see the module docstring).
    3. The reconstructed structure re-evaluates every searched sentence to
       TRUE through BOTH ``evaluate_in_structure`` and ``tarski.satisfies``
       over an equivalent ``tarski.Structure`` — route #2.
    """
    v = _backend.decide(formula, premises, max_size=_MAX_SIZE)
    assert v.status == REFUTED
    assert v.reason is None
    assert v.detail is None            # None => verify_model raised no objection

    structure = structure_from_dict(v.countermodel["data"])
    assert len(structure.domain) == expected_min_size

    sentences = tuple(premises) + (Not(formula),)
    signature = Signature.from_formulas(sentences)
    tstruct = _to_tarski_structure(structure, signature)
    for sentence in sentences:
        via_model_eval = evaluate_in_structure(sentence, structure)
        via_tarski = tarski.satisfies(sentence, tstruct, {})
        assert via_model_eval is True and via_tarski is True, (
            f"disagreement or false sentence: model_eval={via_model_eval} "
            f"tarski={via_tarski} sentence={sentence.to_unicode_str()!r}"
        )

    mf_countermodel = find_countermodel(premises, formula, max_size=_MAX_SIZE)
    assert mf_countermodel is not None, (
        "modelfinder disagrees with clingo: found NO countermodel of the "
        "same question up to the same size bound"
    )


def test_commutativity_refuted():
    """"Left projection", ``op(x,y) = x`` over ``{a,b}``, is the minimal
    non-commutative example: ``op(a,b)=a`` but ``op(b,a)=b``, and ``a≠b``, so
    commutativity fails at ``x=a, y=b``. Minimal countermodel size: 2 (``a≠b``
    already forces at least 2 individuals, and this exact table realises the
    failure there, so no larger domain is needed).
    """
    a, b = Constant("a"), Constant("b")
    x, y = Variable("x"), Variable("y")
    premises = [
        Atom("≠", [a, b]),
        Atom("=", [Function("op", [a, a]), a]),
        Atom("=", [Function("op", [a, b]), a]),
        Atom("=", [Function("op", [b, a]), b]),
        Atom("=", [Function("op", [b, b]), b]),
    ]
    commutative = Quantifier("forall", x, Quantifier(
        "forall", y, Atom("=", [Function("op", [x, y]), Function("op", [y, x])])))
    _assert_refuted_and_cross_checked(commutative, premises, expected_min_size=2)


def test_associativity_refuted():
    """"Negate-first", ``op(x,y) = NOT(x)`` (``op`` ignores its second
    argument and flips the first, over ``{a,b}`` with ``NOT(a)=b``,
    ``NOT(b)=a``), is non-associative for EVERY choice of ``x,y,z``: since
    ``op`` ignores its second argument, ``op(op(x,y),z) = NOT(NOT(x)) = x``
    (``NOT`` is its own inverse on 2 elements), while ``op(x,op(y,z)) =
    NOT(x)`` — and ``x = NOT(x)`` never holds (``NOT`` has no fixed point on
    ``{a,b}``). Concretely at ``x=y=z=a``: ``op(op(a,a),a) = op(b,a) = a``
    but ``op(a,op(a,a)) = op(a,b) = b``, and ``a≠b``. Minimal countermodel
    size: 2, by the same "``a≠b`` forces it, this table realises it there"
    argument as the commutativity case above.
    """
    a, b = Constant("a"), Constant("b")
    x, y, z = Variable("x"), Variable("y"), Variable("z")
    premises = [
        Atom("≠", [a, b]),
        Atom("=", [Function("op", [a, a]), b]),
        Atom("=", [Function("op", [a, b]), b]),
        Atom("=", [Function("op", [b, a]), a]),
        Atom("=", [Function("op", [b, b]), a]),
    ]
    associative = Quantifier("forall", x, Quantifier("forall", y, Quantifier(
        "forall", z,
        Atom("=", [Function("op", [Function("op", [x, y]), z]),
                  Function("op", [x, Function("op", [y, z])])]))))
    _assert_refuted_and_cross_checked(associative, premises, expected_min_size=2)


def test_idempotence_refuted():
    """``op(a,a) = b`` together with ``a≠b`` directly refutes ``∀x
    (op(x,x)=x)`` at ``x=a`` — the minimal possible case: only ONE ground
    function fact is needed at all (``op``'s OTHER values, at ``a,b``/``b,a``/
    ``b,b``, are left entirely unconstrained by the premises and simply
    picked freely by the solver). Minimal countermodel size: 2, forced by
    ``a≠b`` alone.
    """
    a, b = Constant("a"), Constant("b")
    x = Variable("x")
    premises = [
        Atom("≠", [a, b]),
        Atom("=", [Function("op", [a, a]), b]),
    ]
    idempotent = Quantifier("forall", x, Atom("=", [Function("op", [x, x]), x]))
    _assert_refuted_and_cross_checked(idempotent, premises, expected_min_size=2)
