"""ASP-backed finite-domain refutation search via `clingo <https://potassco.org>`_.

:class:`ClingoBackend` decides ``premises ⊨ formula`` by searching for a
finite model of ``premises ∧ ¬formula`` at increasing domain sizes, exactly
the :class:`~unicode_logic_kit.atp.finite_domain.FiniteDomainProblem` contract
:mod:`~unicode_logic_kit.atp.finite_domain` was built for — see that module's
docstring for the shared problem shape, the fragment gate
(:func:`~unicode_logic_kit.atp.finite_domain.fragment_check`), the countermodel
reconstruction (:func:`~unicode_logic_kit.atp.finite_domain.structure_from_solution`),
and the re-verification safety net
(:func:`~unicode_logic_kit.atp.finite_domain.verify_model`). This module is
solver-specific: :func:`to_asp` renders a
:class:`~unicode_logic_kit.atp.finite_domain.FiniteDomainProblem` into an ASP
program, and :class:`ClingoBackend` runs it through clingo's Python API.

Why compositional (Tseitin-style) translation, not a flat constraint
----------------------------------------------------------------------
An ASP rule body is a CONJUNCTION of literals; there is no direct way to
write "an arbitrary Boolean formula with ``∨``/``¬`` nested under other
connectives" as one rule. This module instead gives every subformula
occurrence its own DEFINED atom ``satK`` (``K`` a fresh, globally unique
counter — see ``_AspEncoder._fresh``), built bottom-up so a parent's rule
only ever references its children's already-defined atoms:

* ``And``/``Contrast`` — one rule ANDing both children's atoms.
* ``Or`` — TWO rules, one per disjunct (a predicate with two independent
  defining rules is true if EITHER fires — this is exactly disjunction under
  the stable-model semantics clingo implements).
* ``Not``/``Xor``/``Implies``/``Iff`` — combinations of the above plus
  default negation (``not satK``). This is safe (not merely convenient):
  every subformula tree here is FINITE and ACYCLIC, so negation only ever
  refers to a strictly smaller child — the whole program is stratified, and
  stratified negation is exactly classical two-valued evaluation, with no
  extra argument needed for why the stable model coincides with the
  intended truth table.
* ``Quantifier`` — ``∃`` is one rule with a fresh domain-ranging variable in
  the body (a positive occurrence proves existence by construction); ``∀``
  is the double-negation idiom (``violK`` holds if some individual violates
  the body; the quantifier's own atom holds if NOT violK) rather than a
  literal ASP ``∀`` (ASP has none — this is the standard encoding).
* ``Count``/``Cardinality`` — both map directly to a clingo ``#count``
  aggregate assigned to a fresh integer variable, compared arithmetically.
  This is a genuine improvement over
  :meth:`~unicode_logic_kit.fol.nodes.Count._expand`'s distinct-witnesses
  lowering (used by ``to_z3``/``to_prover9``/``to_tptp``): that expansion is
  O(n²) constraints under n nested quantifiers and refuses n > 500; the
  aggregate has no such bound, because clingo counts the guessed relation's
  extension directly rather than enumerating n Skolem witnesses.

**Each subformula's OWN free variables (via
:func:`~unicode_logic_kit.fol.nodes.free_variables`, not a hand-rolled scope
stack) are exactly its ``satK`` atom's argument tuple.** This single choice
is what makes quantifier SHADOWING correct for free: ``∀x(P(x) ∧ ∃x Q(x))``
gives the inner ``∃x`` its own atom with ARITY 0 (``free_variables`` already
subtracts its own bound ``x``, so the inner atom never mentions the outer
``x`` at all), and ASP's own per-RULE variable scoping means the outer and
inner rules can both legally use the ASP variable name ``Vx`` without
colliding — no manual alpha-renaming or explicit scope-stack bookkeeping is
needed anywhere in this module. Reusing ``free_variables`` (already
exercised elsewhere in the kit, e.g. by ``Count._expand``) also means this
encoder inherits a binder-correctness argument it did not have to make from
scratch — the rejected alternative (tracking a binder-scope stack by hand
through the recursion) is exactly the kind of bookkeeping most likely to
hide an off-by-one shadowing bug.

Comparison predicates — matching ``model_eval`` exactly
------------------------------------------------------------
``=``/``≠`` at arity 2 are lowered to NATIVE ASP term (in)equality on the
two operands' resolved domain-index variables — never a stored relation —
mirroring :func:`~unicode_logic_kit.semantics.model_eval.evaluate`'s own
special-case (identity via Python ``==``, never routed through the
structure). Every OTHER atom, INCLUDING ``<``/``>``/``≤``/``≥`` over plain
individuals, is lowered the same way ``model_eval`` reads it: as an ORDINARY
predicate the countermodel is free to interpret however it likes (see
``model_eval``'s module docstring — it special-cases only ``=``/``≠``;
``<`` etc. fall through to ``_holds``, i.e. a stored/looked-up relation,
NOT built-in arithmetic ordering — the domain individuals are opaque
labels, not numbers, so "less than" has no intrinsic meaning here). Because
:meth:`~unicode_logic_kit.fol.signature.Signature.from_formulas` deliberately
EXCLUDES the six comparison symbols from user vocabulary (they are the
kit's built-in operators — see that module's docstring), this encoder
tracks such "comparison-symbol-as-plain-relation" usages ITSELF and folds
them into a LOCAL, extended reconstruction Signature
(:attr:`_AspEncoder.reconstruction_signature`) used only for
:func:`~unicode_logic_kit.atp.finite_domain.structure_from_solution` — never
mutating or replacing ``problem.signature`` itself.

The one exception: when EITHER operand of a ``=``/``≠``/``<``/``>``/``≤``/
``≥`` comparison is a counting term (``Cardinality`` or ``Number``), the
comparison is arithmetic over NATURAL NUMBERS (a ``#count`` aggregate result,
or a literal), not over domain individuals — this is the counting fragment
this whole design exists to close (see
:mod:`~unicode_logic_kit.atp.finite_domain`'s module docstring, §1 of the
originating design note). Mixing a counting term against a plain
individual-denoting term on the other side of the same comparison has no
coherent reading and is refused loudly (``_EncodingError``) rather than
guessed at.

**Numerals.** That arithmetic reading belongs to a COUNT: a ``Number`` is read as a number
only as the bound a ``Cardinality`` is compared with (``|{x : P(x)}| ≥ 2``; a float with a
whole value is that integer). Everywhere else a numeral is, as on every other route, a
constant identified by its value (``1`` and ``1.0`` one constant, ``1 ≠ 2`` not valid), and
this encoder has no symbol for such a constant, so a ``Number`` used as an individual, and a
comparison of numerals with no cardinality in it, are refused by name (``UNKNOWN`` /
``"unsupported"``) — never read as a domain index or as arithmetic, which would make
``(∀x ∀y x = y) → 1 = 2`` (valid: one element) refutable.

Counting AND function comparisons now verify: the closed gaps, and the one that remains
-------------------------------------------------------------------------------------------
This section used to list four node types this backend could ground and
solve but never verify. That list is down to one, closed in two steps.

``Cardinality`` — and a ``Number`` compared as a counting term — used to be
on it: :func:`~unicode_logic_kit.atp.finite_domain.verify_model`'s underlying
evaluator raised ``UnsupportedNode`` for them, so a genuinely correct
countermodel was reported ``ERROR``/``"infra"`` instead of ``REFUTED``.
:func:`~unicode_logic_kit.semantics.model_eval.evaluate` reads a comparison
with a counting-term operand arithmetically (counting ``|{v :
φ}|`` over the domain — see that module's ``_numeric_value``/``_atom_value``
split), so :func:`~unicode_logic_kit.atp.finite_domain.verify_model` can check
these sentences and :meth:`ClingoBackend.decide` reports a verified
``REFUTED`` for them like any other. Example: ``|{x : P(x)}| >
|{y : Q(y)}|`` at ``max_size=4`` comes back ``REFUTED`` with
``countermodel={"kind": "finite_structure", ...}`` and ``detail=None`` (a
non-``None`` detail would mean verification failed or was skipped) — run
against this module directly on 2026-08-14, clingo 5.8.1.

``Function`` was on this list too, for a DIFFERENT reason: the gate itself
used to refuse every ``Function`` node BY NAME before this encoder ever ran
(``fragment_check`` reported ``UNKNOWN``/``"unsupported"`` straight from the
gate — "we correctly declined to look", not merely "we found a countermodel
we cannot vouch for"), because :func:`~unicode_logic_kit.semantics.model_eval.evaluate`
had no case for a ``Function`` TERM. That upstream refusal is gone:
:func:`~unicode_logic_kit.atp.finite_domain.fragment_check` now ADMITS
``Function`` generally (a *sorted* ``FunctionDecl`` stays refused — a
separate, narrower decision, see that module's "Sorted function symbols"
section), and ``evaluate_in_structure``'s new ``Function`` case reads
``f(t1,...,tk)`` off the SAME ``(name, arity+1)`` total-relation extension
:func:`~unicode_logic_kit.atp.finite_domain.structure_from_solution` already
built (:mod:`~unicode_logic_kit.semantics.model_eval`'s own docstring has the
full account), so this encoder's dormant ``Function`` branch in
:meth:`_AspEncoder._term` (already documented above — the choice-rule
total-relation encoding) is REACHABLE and its output is genuinely VERIFIED,
not merely produced. A function-bearing countermodel now goes through the
identical closure the counting fragment already got: solved by clingo,
reconstructed by :func:`~unicode_logic_kit.atp.finite_domain.structure_from_solution`,
confirmed by :func:`~unicode_logic_kit.atp.finite_domain.verify_model`, and
reported ``REFUTED`` with ``detail=None``. Example: ``∀x (f(f(x)) = x)``
("f is an involution") at ``max_size=4`` comes back ``REFUTED`` at the
hand-derivable minimal size 2 (the only total function on a 1-element domain
is forced to be the identity, so no countermodel exists there) with
``detail=None`` — run against this module directly on 2026-09-17, clingo
5.8.1 (see ``tests/test_clingo_backend.py``'s
``test_involution_claim_refuted_with_verified_countermodel``). The four
arithmetic operator names (``+``/``-``/``*``/``/``) stay refused regardless
— they are
``Function`` nodes like any other and pass ``fragment_check``, but
``Signature.from_formulas`` never declares them in ``functions`` (the
``_BUILTIN_FUNCS`` carve-out), so :meth:`_AspEncoder._term`'s existing
"function not declared in signature" ``_EncodingError`` catches them, with
no new special-casing needed in this module.

``Contrast`` is the one node type left on the list, genuinely unchanged:
:func:`~unicode_logic_kit.atp.finite_domain.fragment_check` still admits it
(truth-functionally ``And``, so this encoder's ``And``/``Contrast`` rule —
see above — grounds and solves it exactly like ``And``), but
:func:`~unicode_logic_kit.semantics.model_eval.evaluate` still raises
``UnsupportedNode`` for it (a scope decision made in that module, not this
one). :func:`~unicode_logic_kit.atp.finite_domain.verify_model` therefore
still reports "could not verify" for a ``Contrast``-bearing sentence, and
:meth:`ClingoBackend.decide` still reports ``ERROR``/``"infra"`` rather than
``REFUTED`` for it, EVEN THOUGH the countermodel this module found is
genuinely correct — the same trade this whole section used to describe for
all four node types, now narrowed to just this one. Per the ONE rule these
backends exist to protect (never hand back an unverified countermodel — see
:mod:`~unicode_logic_kit.atp.finite_domain`'s "Known verification gap"), that
trade is accepted rather than bypassed. Fixing it means extending
``model_eval`` (owned elsewhere) or redesigning ``verify_model`` (a decision
this module does not make unilaterally) — not this module's bug to fix.
Plain classical-FOL-plus-``Count``/``Cardinality`` sentences, including
counting comparisons, now verify and report ``REFUTED`` normally.

A free variable is a parameter of the problem
-------------------------------------------------------------------
:meth:`ClingoBackend.decide` reads a free variable as ONE unknown element, the same in
every premise and in the goal (the assignment-wise consequence relation: ``Γ ⊨ φ`` iff every
structure AND assignment that satisfies ``Γ`` satisfies ``φ``). Before anything else it replaces
every free variable of ``premises`` and ``formula`` together by a constant of its own name
(:func:`~unicode_logic_kit.fol._free_parameters.parameterize`), and only then forms
``premises ∧ ¬formula``. A premise is never closed universally: ``P(x)`` does not entail
``P(alpha)`` (universe ``{0, 1}``, ``x`` ↦ 1, ``alpha`` ↦ 0, ``P`` = ``{1}``), and the countermodel
reports the element under the variable's name, ``constants['x']``. A free variable spelled like a
constant of the problem is refused (``UNKNOWN``/``"unsupported"``): a structure holds one entry
per name.

The parameters are replaced BEFORE the goal is negated: ``¬∀x φ(x)`` (some assignment falsifies
φ) is NOT the same formula as ``∀x ¬φ(x)``, which a closure applied after the negation would
produce. For a problem with no premise the reading coincides with the universal closure of the
goal (``φ`` holds under every assignment iff ``∀x φ`` holds); with a premise it does not, since
closing every premise universally would read ``P(x)`` as ``∀x P(x)`` and find no countermodel of
``P(x) ⊢ P(alpha)``. Both the encoder and the independent checker
(:func:`~unicode_logic_kit.atp.finite_domain.verify_model`) are handed the identical sentences, so
they cannot disagree about what a free variable means: neither of them ever sees one.

``all_different`` (every CONSTANT denotes a pairwise-distinct individual) concerns the constants
of the problem, never a parameter: a variable may denote the same element as a constant, so the
distinctness constraint, and its re-check on the reconstructed structure, leave the parameters out.

Many-sorted input
-------------------
:meth:`ClingoBackend.decide` builds ``sentences`` (the premises, and the goal negated,
every free variable already read as a parameter per the section above) and then, before anything else,
calls :func:`~unicode_logic_kit.atp.finite_domain.lower_msfol` on the whole
batch — a no-op for every plain-FOL caller, and for a many-sorted one a
relativisation to classical FOL (plus one non-emptiness sentence per
distinct sort name) that lets :func:`~unicode_logic_kit.atp.finite_domain.fragment_check`,
:func:`to_asp`, and :func:`~unicode_logic_kit.atp.finite_domain.verify_model`
all stay entirely sort-blind. See
:mod:`~unicode_logic_kit.atp.finite_domain`'s own "Many-sorted input" section
for the full design, including why the non-emptiness sentence is required
for soundness against :mod:`~unicode_logic_kit.semantics.modelfinder`, the
oracle this is differentially tested against.

Availability and timeout
-------------------------------
``clingo`` (MIT, wheels bundle the solver) is a hard, non-external Python
dependency once installed — :func:`clingo_available` is pure discovery
(``importlib.util.find_spec``, mirroring
:meth:`~unicode_logic_kit.atp.cvc5_backend.Cvc5Backend.available`) and the
``clingo`` module itself is imported lazily inside the solve step so probing
availability never pays its load cost. A size's solve runs through clingo's
ASYNC handle (``Control.solve(async_=True)``) so the remaining millisecond
budget can be enforced with ``handle.wait(remaining)`` +
``handle.cancel()``; a cancellation that lands exactly as the solve
legitimately finished still yields the REAL (sat/unsat) answer rather than a
spurious timeout — ``handle.get()`` after ``cancel()`` returns whatever the
solver actually decided, and only a genuinely interrupted search comes back
with neither ``satisfiable`` nor ``unsatisfiable`` set (empirically verified
against clingo 5.8.1 before relying on it here).

This module never imports ``PROVED`` from
:mod:`~unicode_logic_kit.atp.protocol` — deliberately: a backend that cannot
even name the symbol cannot accidentally return it. First-order logic has
no finite model property, so "no countermodel up to ``max_size``" is
``UNKNOWN``/``"bound_hit"``, never a validity proof (the ONE rule these
finite-domain backends exist to protect — see
:mod:`~unicode_logic_kit.atp.finite_domain`'s module docstring).
"""

import importlib.util
import time
from typing import Dict, FrozenSet, List, Optional, Sequence, Set, Tuple

from ..fol._free_parameters import parameterize
from ..fol.nodes import (
    Node, Variable, Constant, Number, Function,
    Atom, Not, And, Or, Xor, Implies, Iff, Contrast, Quantifier,
    Count, Cardinality,
    free_variables,
)
from ..fol.signature import Signature, PredicateDecl
from .finite_domain import (
    FiniteDomainProblem, fragment_check, free_variable_reason, lower_msfol,
    structure_from_solution, verify_model,
)
from .protocol import ProverBackend, Verdict, REFUTED, UNKNOWN, ERROR

__all__ = ["ClingoBackend", "clingo_available", "to_asp"]

_FORALL = ("forall", "∀")
_EXISTS = ("exists", "∃")
_COMPARISON_SYMBOLS = frozenset({"=", "≠", "<", ">", "≤", "≥"})
_NUMERIC_ASP_OP = {"=": "=", "≠": "!=", "<": "<", ">": ">", "≤": "<=", "≥": ">="}


def clingo_available() -> bool:
    """Return whether the ``clingo`` package is importable (pure discovery).

    Never imports ``clingo`` itself — only checks
    ``importlib.util.find_spec`` — so calling this to decide whether to try
    :class:`ClingoBackend` never pays the solver binding's load cost, the
    same discipline
    :meth:`~unicode_logic_kit.atp.cvc5_backend.Cvc5Backend.available` follows
    for its own optional dependency.
    """
    return importlib.util.find_spec("clingo") is not None


# =============================================================================
# Refutation-goal construction
# =============================================================================

def _universal_closure(node: Node) -> Node:
    """Wrap ``node`` in a ∀ for each of its own free variables (deterministic order).

    The universal closure of ONE formula: it says the formula holds under every
    assignment, which is what a test of a countermodel needs when it re-evaluates a
    single formula's refutation goal ``¬∀x φ(x)``. It is not how :meth:`ClingoBackend.decide`
    reads a PROBLEM: a free variable there is a parameter shared by the premises and the
    goal (see the module docstring's "A free variable is a parameter of the problem"),
    because closing each premise on its own would read ``P(x)`` as ``∀x P(x)``.
    Variable names sorted, innermost-first, as
    :mod:`~unicode_logic_kit.semantics.modelfinder`'s module-private closure helper.
    """
    result = node
    for name in sorted({v.name for v in free_variables(node)}, reverse=True):
        result = Quantifier("∀", Variable(name), result)
    return result


def _repeated_constant(constants, parameters: FrozenSet[str]) -> Optional[str]:
    """A message naming two constants of ``constants`` that denote one individual, or ``None``.

    The parameters that stand for free variables are left out: ``all_different`` is the
    unique-names convention of the problem's constants, and a variable may denote the
    element of a constant.
    """
    seen: Dict[object, str] = {}
    for name in sorted(constants):
        if name in parameters:
            continue
        value = constants[name]
        if value in seen:
            return (f"structure_from_solution: all_different=True requires every constant to "
                    f"denote a distinct individual, but {name!r} and {seen[value]!r} both "
                    f"denote {value}.")
        seen[value] = name
    return None


class _EncodingError(ValueError):
    """A sentence passed ``fragment_check`` but this encoder still cannot lower it.

    ``fragment_check`` (:mod:`~unicode_logic_kit.atp.finite_domain`) only
    screens NODE TYPES — a shared, solver-agnostic gate the MiniZinc backend
    also consults, so it deliberately does not know about ASP-specific
    encodability. A few finer-grained shapes slip past it and are caught
    here instead: a non-integer ``Number``, a comparison mixing a counting
    term (``Cardinality``/``Number``) against a plain individual-denoting
    term, or a symbol a sentence uses but the problem's Signature does not
    declare (only reachable via a hand-built
    :class:`~unicode_logic_kit.atp.finite_domain.FiniteDomainProblem` whose
    ``signature=`` was supplied explicitly and does not match its
    ``sentences``). :class:`ClingoBackend` catches this subclass of
    ``ValueError`` and reports ``UNKNOWN``/``"unsupported"`` — the same
    honest verdict ``fragment_check`` itself would have given had its
    coarser gate been able to see this deep.
    """


def _is_numeric_term(node: Node) -> bool:
    """Whether ``node`` denotes a NATURAL NUMBER (a counting term), not an individual."""
    return isinstance(node, (Cardinality, Number))


def _atom_mode(atom: Atom) -> str:
    """Classify how ``atom`` must be lowered to ASP; see the module docstring's
    "Comparison predicates" section for the full rationale.

    Returns one of:

    * ``"identity"`` — ``=``/``≠`` at arity 2 over plain individual terms:
      native ASP term (in)equality, mirroring
      :func:`~unicode_logic_kit.semantics.model_eval.evaluate`'s own
      ``=``/``≠`` special-case exactly.
    * ``"numeric"`` — any of the six comparison symbols at arity 2 with a
      counting-term (``Cardinality``/``Number``) operand: arithmetic over
      natural numbers via a ``#count`` aggregate and/or a literal integer.
    * ``"relation"`` — any of the six comparison symbols used OUTSIDE the
      two cases above (individual-mode ``<``/``>``/``≤``/``≥``, or any of
      the six at an arity other than 2): an ORDINARY predicate the
      countermodel is free to interpret arbitrarily, exactly how
      ``model_eval`` reads them (it special-cases only 2-ary ``=``/``≠``).
    * ``"predicate"`` — every other symbol: must already be declared in the
      problem's Signature.

    Raises:
        _EncodingError: the comparison mixes a counting-term operand
            against a plain individual-denoting one — no coherent reading —
            or compares numerals with each other and with no cardinality:
            the arithmetic reading belongs to a count compared with a
            number, and a numeral that is no bound of a count is a
            constant of the kit (see :meth:`_AspEncoder._term`).
    """
    if atom.predicate in _COMPARISON_SYMBOLS and len(atom.args) == 2:
        left_numeric = _is_numeric_term(atom.args[0])
        right_numeric = _is_numeric_term(atom.args[1])
        if left_numeric or right_numeric:
            if not (left_numeric and right_numeric):
                raise _EncodingError(
                    f"{atom.predicate!r} compares a counting term "
                    "(Cardinality/Number) against a plain individual-denoting "
                    "term — both sides of a counting comparison must "
                    "themselves be counting terms."
                )
            if not any(isinstance(a, Cardinality) for a in atom.args):
                raise _EncodingError(
                    f"{atom.predicate!r} compares numerals without a cardinality. A numeral is a "
                    "constant identified by its value, and nothing else is known about it, so "
                    "such a comparison is a statement about constants ('1 ≠ 2' is not valid, "
                    "'(∀x ∀y x = y) → 1 = 2' is), which this encoder does not state: it reads a "
                    "number only as the bound a count |{v : φ}| is compared with, and a "
                    "refutation found under the arithmetic reading would be wrong for the "
                    "constants. Use a solver that reads numerals as constants (z3, the finite "
                    "model finder), or compare a cardinality.")
            return "numeric"
        if atom.predicate in ("=", "≠"):
            return "identity"
        return "relation"
    return "relation" if atom.predicate in _COMPARISON_SYMBOLS else "predicate"


# =============================================================================
# The encoder — shared by to_asp() and ClingoBackend.decide()
# =============================================================================

class _AspEncoder:
    """Lowers one :class:`FiniteDomainProblem` to ASP text, and back again.

    Built once per (sentences, size) pair. :meth:`render` produces the
    program text (what :func:`to_asp` returns); :meth:`decode_model` and
    :attr:`reconstruction_signature` are the matching REVERSE direction,
    used only by :class:`ClingoBackend` (never by :func:`to_asp`, which has
    no solver to hand a model back from) to turn clingo's shown atoms into
    the ``(name, args)`` shape
    :func:`~unicode_logic_kit.atp.finite_domain.structure_from_solution`
    expects. Kept as ONE class, not two free functions sharing module
    globals, so the symbol-name maps built while rendering are exactly what
    decoding reads back — a mismatch between the two directions cannot occur
    by construction, not by discipline.

    Deliberately rebuilt from scratch for every domain size a caller tries
    (see :meth:`ClingoBackend.decide`), even though the symbol-name
    assignments themselves do not depend on ``size`` — ``size`` is coupled
    into :class:`FiniteDomainProblem` itself, and re-deriving a few small
    dicts per size is cheap next to actually grounding and solving; the
    alternative (splitting a size-independent "skeleton" out for reuse
    across sizes) is a real optimisation this module deliberately does not
    attempt, in favour of one obviously-correct code path.
    """

    def __init__(self, problem: FiniteDomainProblem, parameters: FrozenSet[str] = frozenset()):
        """``parameters`` names the constants that stand for a free variable: the
        problem's ``all_different`` (every CONSTANT denotes a pairwise-distinct
        individual) leaves them out, since a variable may denote the element of a
        constant."""
        if not isinstance(problem, FiniteDomainProblem):
            raise TypeError(
                f"_AspEncoder: problem must be a FiniteDomainProblem, got "
                f"{type(problem).__name__}."
            )
        self.problem = problem
        self._parameters = frozenset(parameters)
        self.sig: Signature = problem.signature
        self._lines: List[str] = []
        self._fresh_n = 0
        self._pred_asp: Dict[Tuple[str, int], str] = {}
        self._func_asp: Dict[str, str] = {}
        self._const_asp: Dict[str, str] = {}
        self._built = False

    # -- naming -------------------------------------------------------

    def _fresh(self, prefix: str) -> str:
        """A globally unique name ``{prefix}{n}`` — see the class docstring's
        naming-collision argument in the module docstring (no two calls,
        regardless of prefix, ever share a counter value)."""
        self._fresh_n += 1
        return f"{prefix}{self._fresh_n}"

    @staticmethod
    def _asp_var(kit_name: str) -> str:
        """Map a kit variable name to an ASP variable name.

        ``"V" + name`` — ASP variables must start uppercase; kit variable
        names are always lowercase-initial identifiers (single letters, or
        ``x_0``-style fresh names), the same assumption
        :meth:`~unicode_logic_kit.fol.nodes.Variable.to_prover9` /
        :meth:`~unicode_logic_kit.fol.nodes.Variable.to_tptp` already make
        (both just ``.upper()`` the name with no further sanitisation) —
        this module does not attempt anything more general than the kit's
        own existing text-based exporters do for the same node type.
        """
        return f"V{kit_name}"

    @staticmethod
    def _format_atom(name: str, args: Sequence[str]) -> str:
        """Render an applied atom, or a bare name for an empty arg list.

        clingo does not accept ``name()`` for a nullary atom, so the empty
        case omits the parentheses entirely rather than emitting them empty.
        """
        return name if not args else f"{name}({','.join(args)})"

    def _call(self, asp_name: str, kit_var_names: Sequence[str]) -> str:
        return self._format_atom(asp_name, [self._asp_var(n) for n in kit_var_names])

    def _fv_tuple(self, node: Node) -> List[str]:
        """The sorted kit variable NAMES free in ``node`` — see the module
        docstring's shadowing argument for why sorted-by-name determinism
        plus per-rule ASP scoping is sufficient, with no scope stack."""
        return sorted({v.name for v in free_variables(node) if isinstance(v, Variable)})

    def _dom_prefix(self, kit_var_names: Sequence[str]) -> List[str]:
        return [f"dom({self._asp_var(n)})" for n in kit_var_names]

    def _rule(self, head: str, body: List[str]) -> None:
        if body:
            self._lines.append(f"{head} :- {', '.join(body)}.")
        else:
            self._lines.append(f"{head}.")

    # -- declarations ---------------------------------------------------

    def _discover_comparison_relations(self) -> Set[Tuple[str, int]]:
        """Every ``(symbol, arity)`` among the six comparison predicates that
        must become an ORDINARY guessed relation (see :func:`_atom_mode`'s
        ``"relation"`` case) — walked up front so its choice rule can be
        emitted alongside every other predicate's, in one deterministic pass.
        """
        found: Set[Tuple[str, int]] = set()
        for sentence in self.problem.sentences:
            for node in sentence.walk():
                if isinstance(node, Atom) and node.predicate in _COMPARISON_SYMBOLS:
                    if _atom_mode(node) == "relation":
                        found.add((node.predicate, len(node.args)))
        return found

    def _assign_names(self) -> None:
        sig_keys = {(name, decl.arity) for name, decl in self.sig.predicates.items()}
        for i, key in enumerate(sorted(sig_keys | self._discover_comparison_relations())):
            self._pred_asp[key] = f"pred{i}"
        for name, _decl in sorted(self.sig.functions.items()):
            self._func_asp[name] = f"func{len(self._func_asp)}"
        for name in sorted(self.sig.constants):
            self._const_asp[name] = f"const{len(self._const_asp)}"

    @staticmethod
    def _choice_rule(asp_name: str, arity: int) -> str:
        """A free choice over a relation's WHOLE extension.

        The standard ASP idiom for "the countermodel may interpret this
        predicate however it likes": ``{ p(X,Y) : dom(X), dom(Y) }``.
        """
        if arity == 0:
            return f"{{ {asp_name} }}."
        xs = [f"X{i}" for i in range(arity)]
        conds = ",".join(f"dom({x})" for x in xs)
        return f"{{ {asp_name}({','.join(xs)}) : {conds} }}."

    @staticmethod
    def _function_rule(asp_name: str, arity: int) -> str:
        """The total-relation encoding: exactly one result per input tuple,
        via a bounded cardinality choice ``1 { … } 1`` — enforces BOTH
        functionality and totality at once (see
        :func:`~unicode_logic_kit.atp.finite_domain.structure_from_solution`'s
        own docstring for why both matter to the reconstruction step)."""
        if arity == 0:
            return f"1 {{ {asp_name}(Y) : dom(Y) }} 1."
        xs = [f"X{i}" for i in range(arity)]
        conds = ",".join(f"dom({x})" for x in xs)
        return f"1 {{ {asp_name}({','.join(xs)},Y) : dom(Y) }} 1 :- {conds}."

    @staticmethod
    def _const_rule(asp_name: str) -> str:
        """A constant is the arity-0 case of the function idiom above: exactly
        one denotation, chosen freely."""
        return f"1 {{ {asp_name}(Y) : dom(Y) }} 1."

    # -- term translation -------------------------------------------------

    def _term(self, node: Node) -> Tuple[str, List[str]]:
        """Translate an INDIVIDUAL-denoting term to ``(asp_term, extra_body_literals)``.

        ``extra_body_literals`` must be conjoined into whichever rule body
        is being built around this term (a fresh constant/function-result
        variable is meaningless without the literal that binds it).
        """
        if isinstance(node, Variable):
            return self._asp_var(node.name), []
        if isinstance(node, Constant):
            if node.name not in self._const_asp:
                raise _EncodingError(
                    f"_AspEncoder: constant {node.name!r} is used in a sentence "
                    "but is not declared in the problem's signature."
                )
            v = self._fresh("Cst")
            return v, [f"{self._const_asp[node.name]}({v})"]
        if isinstance(node, Function):
            if node.name not in self._func_asp:
                raise _EncodingError(
                    f"_AspEncoder: function {node.name!r} is used in a sentence "
                    "but is not declared in the problem's signature."
                )
            arg_terms: List[str] = []
            extra: List[str] = []
            for a in node.args:
                t, ex = self._term(a)
                arg_terms.append(t)
                extra.extend(ex)
            v = self._fresh("Fn")
            extra.append(self._format_atom(self._func_asp[node.name], arg_terms + [v]))
            return v, extra
        if isinstance(node, Number):
            raise _EncodingError(
                f"_AspEncoder: the numeral {node.value!r} is used as an individual. A numeral "
                "is a constant identified by its value (1 and 1.0 are one constant), and this "
                "encoder has no symbol for it: it reads a number only as the bound a count "
                "|{v : φ}| is compared with, never as a domain element, because the "
                "index reading would make 1 and 2 two different elements that the kit's "
                "numerals need not be. Use a solver that reads numerals as constants (z3, the "
                "finite model finder), or name the individual with a constant.")
        raise _EncodingError(
            f"_AspEncoder: no individual-term translation for node type "
            f"{type(node).__name__} (fragment_check should have rejected this "
            "sentence before it reached the encoder)."
        )

    def _numeric_term(self, node: Node) -> Tuple[str, List[str]]:
        """Translate a COUNTING term (``Cardinality`` or ``Number``) to
        ``(asp_expr, extra_body_literals)`` — a natural-number VALUE, not an
        individual. See :func:`_atom_mode`'s ``"numeric"`` case."""
        if isinstance(node, Number):
            value = node.value
            if isinstance(value, float) and value.is_integer():
                value = int(value)      # one numeral per value: 2.0 is the bound 2
            if isinstance(value, bool) or not isinstance(value, int):
                raise _EncodingError(
                    f"_AspEncoder: Number({node.value!r}) is not a plain "
                    "non-negative integer — the counting fragment only "
                    "supports integer bounds."
                )
            return str(value), []
        if isinstance(node, Cardinality):
            inner_call = self._translate_formula(node.formula)
            v = self._asp_var(node.variable.name)
            c = self._fresh("Card")
            agg = f"{c} = #count {{ {v} : dom({v}), {inner_call} }}"
            return c, [agg]
        raise _EncodingError(
            f"_AspEncoder: {type(node).__name__} is not a counting term "
            "(expected Cardinality or Number)."
        )

    # -- atom / formula translation ----------------------------------------

    def _emit_atom(self, atom: Atom, head: str, dom_lits: List[str]) -> None:
        mode = _atom_mode(atom)
        if mode == "identity":
            t1, ex1 = self._term(atom.args[0])
            t2, ex2 = self._term(atom.args[1])
            op = "=" if atom.predicate == "=" else "!="
            self._rule(head, dom_lits + ex1 + ex2 + [f"{t1} {op} {t2}"])
            return
        if mode == "numeric":
            t1, ex1 = self._numeric_term(atom.args[0])
            t2, ex2 = self._numeric_term(atom.args[1])
            op = _NUMERIC_ASP_OP[atom.predicate]
            self._rule(head, dom_lits + ex1 + ex2 + [f"{t1} {op} {t2}"])
            return
        # mode in ("relation", "predicate"): an ordinary looked-up relation.
        key = (atom.predicate, len(atom.args))
        if key not in self._pred_asp:
            raise _EncodingError(
                f"_AspEncoder: predicate {atom.predicate!r}/{len(atom.args)} is "
                "used in a sentence but is not declared in the problem's "
                "signature."
            )
        asp_name = self._pred_asp[key]
        terms: List[str] = []
        extra: List[str] = []
        for a in atom.args:
            t, ex = self._term(a)
            terms.append(t)
            extra.extend(ex)
        self._rule(head, dom_lits + extra + [self._format_atom(asp_name, terms)])

    def _emit_quantifier(self, node: Quantifier, head: str, fv: List[str],
                         dom_lits: List[str]) -> None:
        inner_var = self._asp_var(node.variable.name)
        inner_call = self._translate_formula(node.formula)
        if node.type in _FORALL:
            viol = self._fresh("viol")
            viol_head = self._call(viol, fv)
            self._rule(viol_head, dom_lits + [f"dom({inner_var})", f"not {inner_call}"])
            self._rule(head, dom_lits + [f"not {viol_head}"])
        elif node.type in _EXISTS:
            self._rule(head, dom_lits + [f"dom({inner_var})", inner_call])
        else:
            raise _EncodingError(f"_AspEncoder: unknown quantifier type {node.type!r}.")

    def _translate_formula(self, node: Node) -> str:
        """Translate a FORMULA node to the ASP call for its freshly minted ``satK`` atom.

        Appends the atom's defining rule(s) to this encoder's line buffer as
        a side effect. See the module docstring for the per-connective
        encoding and the shadowing argument.
        """
        fv = self._fv_tuple(node)
        sat_name = self._fresh("sat")
        head = self._call(sat_name, fv)
        dom_lits = self._dom_prefix(fv)

        if isinstance(node, Atom):
            self._emit_atom(node, head, dom_lits)
        elif isinstance(node, Not):
            inner = self._translate_formula(node.formula)
            self._rule(head, dom_lits + [f"not {inner}"])
        elif isinstance(node, (And, Contrast)):
            left = self._translate_formula(node.left)
            right = self._translate_formula(node.right)
            self._rule(head, dom_lits + [left, right])
        elif isinstance(node, Or):
            left = self._translate_formula(node.left)
            right = self._translate_formula(node.right)
            self._rule(head, dom_lits + [left])
            self._rule(head, dom_lits + [right])
        elif isinstance(node, Xor):
            left = self._translate_formula(node.left)
            right = self._translate_formula(node.right)
            self._rule(head, dom_lits + [left, f"not {right}"])
            self._rule(head, dom_lits + [right, f"not {left}"])
        elif isinstance(node, Implies):
            left = self._translate_formula(node.left)
            right = self._translate_formula(node.right)
            self._rule(head, dom_lits + [f"not {left}"])
            self._rule(head, dom_lits + [right])
        elif isinstance(node, Iff):
            left = self._translate_formula(node.left)
            right = self._translate_formula(node.right)
            self._rule(head, dom_lits + [left, right])
            self._rule(head, dom_lits + [f"not {left}", f"not {right}"])
        elif isinstance(node, Quantifier):
            self._emit_quantifier(node, head, fv, dom_lits)
        elif isinstance(node, Count):
            inner_call = self._translate_formula(node.formula)
            v = self._asp_var(node.variable.name)
            c = self._fresh("Card")
            op = {"ge": ">=", "le": "<=", "eq": "="}[node.op]
            agg = f"{c} = #count {{ {v} : dom({v}), {inner_call} }}"
            self._rule(head, dom_lits + [agg, f"{c} {op} {node.n.value}"])
        else:
            raise _EncodingError(
                f"_AspEncoder: no ASP translation rule for node type "
                f"{type(node).__name__} used as a formula (fragment_check "
                "should have rejected this sentence before it reached the "
                "encoder, or this node type is a TERM used where a formula "
                "was expected)."
            )
        return head

    def _assert_sentence(self, sentence: Node) -> None:
        """Emit the top-level integrity constraint asserting ``sentence`` holds.

        Shape: ``:- dom(X)…, not satRoot(X)….`` — this ALSO auto-closes any
        of ``sentence``'s own free variables universally (a free ASP
        variable ranging over ``dom`` inside a constraint body IS a
        ∀-reading) — see the module docstring's "Refutation goal" section.
        """
        fv = self._fv_tuple(sentence)
        dom_lits = self._dom_prefix(fv)
        call = self._translate_formula(sentence)
        self._lines.append(f":- {', '.join(dom_lits + [f'not {call}'])}.")

    def _emit_show(self) -> None:
        self._lines.append("")
        # A bare "#show." disables clingo's DEFAULT "no #show directives present
        # -> show every atom" behaviour, which would otherwise leak dom/1 facts
        # and every satK/violK/CardK auxiliary atom into the model whenever a
        # problem happens to declare NO predicate/function/constant at all
        # (e.g. a sentence built only from "="/"≠" and Count/Cardinality, which
        # never register a guessed relation) — reproduced and confirmed against
        # clingo 5.8.1 before adding this line. Harmless when other #show
        # directives follow (verified: it only suppresses the default, never
        # an explicit #show that comes after it).
        self._lines.append("#show.")
        for key in sorted(self._pred_asp):
            name, arity = key
            self._lines.append(f"#show {self._pred_asp[key]}/{arity}.")
        for name, decl in sorted(self.sig.functions.items()):
            self._lines.append(f"#show {self._func_asp[name]}/{decl.arity + 1}.")
        for name in sorted(self._const_asp):
            self._lines.append(f"#show {self._const_asp[name]}/1.")

    # -- public surface -----------------------------------------------------

    def render(self) -> str:
        """The full ASP program text for this problem (memoised)."""
        if not self._built:
            n = self.problem.size
            self._lines.append(
                f"% finite-domain refutation search: |D| = {n}, "
                f"{len(self.problem.sentences)} sentence(s)"
            )
            self._lines.append(f"dom(0..{n - 1}).")
            self._lines.append("")

            self._assign_names()
            for key in sorted(self._pred_asp):
                self._lines.append(self._choice_rule(self._pred_asp[key], key[1]))
            for name, decl in sorted(self.sig.functions.items()):
                self._lines.append(self._function_rule(self._func_asp[name], decl.arity))
            for name in sorted(self._const_asp):
                self._lines.append(self._const_rule(self._const_asp[name]))

            distinct = [n2 for n2 in sorted(self._const_asp) if n2 not in self._parameters]
            if self.problem.all_different and len(distinct) >= 2:
                names = [self._const_asp[n2] for n2 in distinct]
                for i in range(len(names)):
                    for j in range(i + 1, len(names)):
                        self._lines.append(f":- {names[i]}(Y), {names[j]}(Y).")

            self._lines.append("")
            for sentence in self.problem.sentences:
                self._assert_sentence(sentence)

            self._emit_show()
            self._built = True
        return "\n".join(self._lines)

    @property
    def reconstruction_signature(self) -> Signature:
        """The problem's own Signature, extended with every comparison symbol
        this encoder registered as an ordinary guessed relation.

        See :func:`_atom_mode`'s ``"relation"`` case — this extension exists
        because
        :meth:`~unicode_logic_kit.fol.signature.Signature.from_formulas`
        deliberately never declares ``=``/``≠``/``<``/``>``/``≤``/``≥`` as
        user vocabulary (they are the kit's built-in operators), yet
        :func:`~unicode_logic_kit.atp.finite_domain.structure_from_solution`
        needs a declaration for every symbol name it is handed. Built fresh
        on every access rather than cached — it is cheap (a handful of dict
        entries) and this keeps the encoder's mutable build state in one
        place (:meth:`render`) rather than two.
        """
        if not self._built:
            self.render()
        preds = dict(self.sig.predicates)
        seen_arity: Dict[str, int] = {name: decl.arity for name, decl in self.sig.predicates.items()}
        for name, arity in self._pred_asp:
            if name in seen_arity:
                if seen_arity[name] != arity:
                    raise _EncodingError(
                        f"_AspEncoder: comparison predicate {name!r} is used at "
                        f"both arity {seen_arity[name]} and arity {arity} — a "
                        "Signature can only declare one arity per symbol."
                    )
                continue
            seen_arity[name] = arity
            preds[name] = PredicateDecl(name, arity)
        return Signature(predicates=preds, functions=self.sig.functions,
                         constants=self.sig.constants, sorts=self.sig.sorts)

    def decode_model(self, symbols) -> List[Tuple[str, Tuple[int, ...]]]:
        """Turn clingo's shown :class:`clingo.Symbol` objects into the
        ``(kit_name, args)`` pairs
        :func:`~unicode_logic_kit.atp.finite_domain.structure_from_solution`
        expects. Only ``pred*``/``func*``/``const*`` names are ever shown
        (see the ``#show`` directives :meth:`render` emits), so no
        ``dom``/``sat*``/``viol*``/``Card*`` auxiliary atom can reach this
        method at all — the filtering
        :func:`~unicode_logic_kit.atp.finite_domain.structure_from_solution`'s
        own docstring asks callers to do is performed by clingo's ``#show``
        machinery itself, not by a second pass here.
        """
        reverse_pred = {asp: name for (name, _arity), asp in self._pred_asp.items()}
        reverse_func = {asp: name for name, asp in self._func_asp.items()}
        reverse_const = {asp: name for name, asp in self._const_asp.items()}
        atoms: List[Tuple[str, Tuple[int, ...]]] = []
        for sym in symbols:
            asp_name = sym.name
            args = tuple(a.number for a in sym.arguments)
            if asp_name in reverse_pred:
                atoms.append((reverse_pred[asp_name], args))
            elif asp_name in reverse_func:
                atoms.append((reverse_func[asp_name], args))
            elif asp_name in reverse_const:
                atoms.append((reverse_const[asp_name], args))
            else:
                raise _EncodingError(
                    f"_AspEncoder: clingo returned a shown atom {asp_name!r} "
                    "this encoder does not recognise (internal encoder / "
                    "#show mismatch — this indicates a bug in this module, "
                    "not in the input formula)."
                )
        return atoms


def to_asp(problem: FiniteDomainProblem) -> str:
    """Render ``problem`` to ASP program text (clingo / gringo syntax).

    Pure text generation — never imports or touches ``clingo`` itself, so
    this can be tested, read, and pinned as a fixture with no solver
    installed. See the module docstring for the encoding this produces.

    Args:
        problem: the finite-domain problem to encode.

    Returns:
        The full program text: a ``dom/1`` domain declaration, one free-choice
        or total-relation rule per declared predicate/function/constant, the
        compositional ``satK``/``violK`` rules for every sentence, one
        top-level integrity constraint per sentence, and ``#show`` directives
        naming exactly the predicate/function/constant atoms.

    Raises:
        TypeError: ``problem`` is not a
            :class:`~unicode_logic_kit.atp.finite_domain.FiniteDomainProblem`.
        ValueError: a sentence, though accepted by
            :func:`~unicode_logic_kit.atp.finite_domain.fragment_check`, still
            cannot be lowered to ASP by this encoder (see
            :class:`_EncodingError`'s docstring for the exact cases); or a
            sentence has a free variable
            (:func:`~unicode_logic_kit.atp.finite_domain.free_variable_reason`:
            the program would read it as "every element", one sentence at a
            time, which is not what a free variable means on any route of
            this kit; :meth:`ClingoBackend.decide` replaces it by a parameter
            before it writes).
    """
    encoder = _AspEncoder(problem)
    reason = free_variable_reason(problem.sentences)
    if reason is not None:
        raise ValueError(f"to_asp: {reason}")
    return encoder.render()


# =============================================================================
# Solving
# =============================================================================

def _solve(program_text: str, remaining_seconds: Optional[float]):
    """Ground and solve ``program_text``, stopping at the first model.

    Returns ``("sat", shown_symbols)``, ``("unsat", None)``, or
    ``("timeout", None)``. ``remaining_seconds=None`` waits indefinitely
    (``clingo.SolveHandle.wait(None)`` blocks until the solve genuinely
    finishes — verified directly against clingo 5.8.1 rather than assumed).
    A timeout cancels the async handle; ``handle.get()`` afterwards still
    returns a genuine ``satisfiable``/``unsatisfiable`` result if the solve
    happened to finish right around the cancellation (also verified
    empirically), so only a truly interrupted search (``result.unknown``)
    reports ``"timeout"``.
    """
    import clingo

    ctl = clingo.Control(logger=lambda code, msg: None)
    ctl.configuration.solve.models = 1
    ctl.add("base", [], program_text)
    ctl.ground([("base", [])])

    captured: List[list] = []

    def on_model(model) -> None:
        captured.append(list(model.symbols(shown=True)))

    with ctl.solve(on_model=on_model, async_=True) as handle:
        finished = handle.wait(remaining_seconds)
        if not finished:
            handle.cancel()
        result = handle.get()

    if result.satisfiable:
        return "sat", (captured[0] if captured else [])
    if result.unsatisfiable:
        return "unsat", None
    return "timeout", None


# =============================================================================
# ClingoBackend
# =============================================================================

class ClingoBackend(ProverBackend):
    """Bounded finite-model search over classical FOL plus counting, via
    clingo — refutation-only (see the module docstring's ONE-rule note).
    Many-sorted input is accepted too: :func:`~unicode_logic_kit.atp.finite_domain.lower_msfol`
    relativises it to plain classical FOL before anything else in
    :meth:`decide` runs (see the module docstring's "Many-sorted input"
    section).

    Registered automatically by ``atp/protocol.py`` (this module does not
    touch the registry itself — see that module's bottom-of-registration
    import block).
    """

    name = "clingo"
    logics = frozenset({"fol"})
    external = False   # pip package (optional extra), not a spawned binary

    def available(self) -> bool:
        """Pure discovery: is the ``clingo`` package importable? (No import.)"""
        return clingo_available()

    def decide(self, formula: Node, premises: Sequence[Node] = (),
               timeout: int = 10000, **options) -> Verdict:
        """Search for a finite countermodel of ``premises ∧ ¬formula``.

        Args:
            formula: the goal.
            premises: entailment premises (``⊨ formula`` when empty). A free
                variable of the premises and the goal is a PARAMETER, one unknown
                element shared by all of them (see the module docstring), reported
                by a countermodel as the constant of the variable's own name; a free
                variable spelled like a constant of the problem is ``UNKNOWN`` /
                ``"unsupported"``.
            timeout: milliseconds for the WHOLE search (across every domain
                size tried); ``0``/negative disables the limit, matching
                :meth:`~unicode_logic_kit.atp.cvc5_backend.Cvc5Backend.decide`'s
                own convention for the same parameter.
            **options: ``max_size`` (default ``6``) — the largest domain
                size tried, sizes ``1 … max_size`` in turn (matches
                :func:`~unicode_logic_kit.semantics.modelfinder.find_countermodel`'s
                own parameter name; a larger default than that function's
                ``4`` is reasonable here since ASP grounding/solving is far
                faster per size than plain Python enumeration). ``all_different``
                (default ``False``) — forwarded to
                :class:`~unicode_logic_kit.atp.finite_domain.FiniteDomainProblem`
                (every constant denotes a pairwise-distinct individual).
                ``verify`` (default ``True``) — whether to run every
                candidate countermodel through
                :func:`~unicode_logic_kit.atp.finite_domain.verify_model`
                before reporting ``REFUTED``; ``False`` exists ONLY for
                measuring verification overhead (see
                :mod:`~unicode_logic_kit.atp.finite_domain`'s module
                docstring) — an unverified countermodel is still marked as
                such in the returned ``Verdict.detail``, never silently.

        Returns:
            A :class:`~unicode_logic_kit.atp.protocol.Verdict` with ``status``
            in ``{"refuted", "unknown", "error"}`` — NEVER ``"proved"`` (see
            the module docstring). ``REFUTED`` carries
            ``countermodel={"kind": "finite_structure", "data": structure.to_dict()}``.
            ``UNKNOWN`` reasons: ``"unsupported"`` (fragment gate or a
            deeper encoding-time rejection), ``"bound_hit"`` (no
            countermodel up to ``max_size``), ``"timeout"`` (the millisecond
            budget expired first). ``ERROR``/``"infra"`` covers a clingo/
            grounding failure, a solver output ``structure_from_solution``
            rejected, or (per the ONE rule) a candidate countermodel that
            failed re-verification.
        """
        max_size = options.pop("max_size", 6)
        if isinstance(max_size, bool) or not isinstance(max_size, int) or max_size < 1:
            raise ValueError(f"clingo: max_size must be an int >= 1, got {max_size!r}.")
        all_different = bool(options.pop("all_different", False))
        verify = bool(options.pop("verify", True))

        # A free variable is a PARAMETER of the problem (see the module docstring): every
        # one is replaced HERE, once, in the premises and the goal together, by a
        # constant of its own name, and only then is the goal negated (¬∀x φ(x) is not
        # ∀x ¬φ(x)). The ASP encoding reads a free variable in a constraint as
        # implicitly ∀-bound but `evaluate_in_structure` raises for a variable with no
        # assignment, so encoder and checker must see the same parameter-free sentences;
        # this is where that is guaranteed. No premise is closed universally.
        try:
            read, parameters = parameterize(list(premises) + [formula], after_variables=True)
        except NotImplementedError as exc:
            return Verdict(UNKNOWN, self.name, reason="unsupported", detail=str(exc))
        goal = Not(read[-1])
        sentences = tuple(read[:-1]) + (goal,)
        parameter_names = frozenset(parameters)
        # Many-sorted input (SortedQuantifier/SortedConstant/SortedCount/
        # SortedCardinality) is relativised to plain classical FOL HERE, once,
        # before fragment_check ever sees it -- see
        # finite_domain.lower_msfol's own docstring and finite_domain's module
        # docstring "Many-sorted input" section. A no-op for every
        # unsorted-only caller (the pre-existing test suite): returns
        # `sentences` untouched when nothing sorted is present.
        sentences = lower_msfol(sentences)

        problem_msg = fragment_check(sentences)
        if problem_msg is not None:
            return Verdict(UNKNOWN, self.name, reason="unsupported", detail=problem_msg)

        try:
            signature = Signature.from_formulas(sentences)
        except (TypeError, ValueError) as exc:
            return Verdict(UNKNOWN, self.name, reason="unsupported",
                           detail=f"signature inference failed: {exc}")

        start = time.perf_counter()
        deadline = None if timeout is None or timeout <= 0 else start + timeout / 1000.0

        for size in range(1, max_size + 1):
            if deadline is not None:
                remaining = deadline - time.perf_counter()
                if remaining <= 0:
                    return Verdict(UNKNOWN, self.name, reason="timeout",
                                   wall_time=time.perf_counter() - start,
                                   detail=f"no countermodel found up to size {size - 1} "
                                          f"before the {timeout}ms budget expired")
            else:
                remaining = None

            try:
                problem = FiniteDomainProblem(sentences, size, signature=signature,
                                              all_different=all_different)
                encoder = _AspEncoder(problem, parameter_names)
                program_text = encoder.render()
            except _EncodingError as exc:
                return Verdict(UNKNOWN, self.name, reason="unsupported",
                               wall_time=time.perf_counter() - start, detail=str(exc))

            try:
                outcome, symbols = _solve(program_text, remaining)
            except Exception as exc:   # noqa: BLE001 - clingo raises plain RuntimeError/etc.
                return Verdict(ERROR, self.name, reason="infra",
                               wall_time=time.perf_counter() - start,
                               detail=f"{type(exc).__name__}: {exc}")

            if outcome == "timeout":
                return Verdict(UNKNOWN, self.name, reason="timeout",
                               wall_time=time.perf_counter() - start,
                               detail=f"clingo did not finish size {size} within the "
                                      f"{timeout}ms budget")
            if outcome == "unsat":
                continue

            # outcome == "sat"
            try:
                atoms = encoder.decode_model(symbols)
                # the distinctness of the CONSTANTS is checked here when a parameter is
                # among them: a variable may denote the element of a constant
                structure = structure_from_solution(
                    encoder.reconstruction_signature, atoms, size,
                    all_different=all_different and not parameter_names)
                if all_different and parameter_names:
                    clash = _repeated_constant(structure.constants, parameter_names)
                    if clash is not None:
                        raise ValueError(clash)
            except (TypeError, ValueError) as exc:
                return Verdict(ERROR, self.name, reason="infra",
                               wall_time=time.perf_counter() - start,
                               detail=f"could not reconstruct clingo's own model at "
                                      f"size {size}: {exc}")

            if verify:
                unverified = verify_model(structure, sentences)
                if unverified is not None:
                    return Verdict(ERROR, self.name, reason="infra",
                                   wall_time=time.perf_counter() - start,
                                   detail=f"unverified countermodel at size {size}: "
                                          f"{unverified}")
                detail = None
            else:
                detail = "model not independently verified (verify=False)"

            return Verdict(REFUTED, self.name, wall_time=time.perf_counter() - start,
                           countermodel={"kind": "finite_structure", "data": structure.to_dict()},
                           detail=detail)

        return Verdict(UNKNOWN, self.name, reason="bound_hit",
                       wall_time=time.perf_counter() - start,
                       detail=f"no countermodel found up to size {max_size}")
