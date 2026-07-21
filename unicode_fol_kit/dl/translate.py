"""The **standard translation** of ALC into first-order logic.

ALC concepts denote unary relations over a domain, and roles denote binary
relations; the standard translation makes this concrete by rendering a
concept ``C`` as a first-order formula ``π(C, x)`` with one free variable
``x`` — "the individual currently under discussion" — such that ``d`` is in
the extension of ``C`` iff ``π(C, x)`` holds under ``x ↦ d``. Concretely:

- ``Atomic("C")``  ↦  ``C(x)``            (the concept becomes a unary predicate)
- ``⊤`` / ``⊥``     ↦  ``x = x`` / ``x ≠ x``  (see "Top and Bottom" below)
- ``¬C``            ↦  ``¬π(C, x)``
- ``C ⊓ D``         ↦  ``π(C, x) ∧ π(D, x)``
- ``C ⊔ D``         ↦  ``π(C, x) ∨ π(D, x)``
- ``∃r.C``          ↦  ``∃y (r(x, y) ∧ π(C, y))``
- ``∀r.C``          ↦  ``∀y (r(x, y) → π(C, y))``

with ``y`` a FRESH variable at every restriction, so nested restrictions
(``∃r.(∀s.C)``) never capture an outer variable (see "Variable freshness").
A role ``r`` becomes its own binary predicate ``r(·, ·)`` with no axioms
forced on it, which is exactly why the reduction is faithful: ALC roles are
arbitrary Kripke relations, and an uninterpreted FOL predicate is exactly
that (see also :func:`concept_to_modal` for the single-role reading through
propositional modal K instead of FOL).

Top and Bottom
--------------
The FOL node set has no first-class truth-constant (no ``⊤``/``⊥`` term
that ``Node.to_z3`` renders as Z3's literal ``True``/``False``); the closest
thing is the reserved falsum atom idiom used by :mod:`unicode_fol_kit.atp.fitch`
(``Atom("⊥", ())`` there, but that idiom is *propositional* and only means
something because the Fitch checker special-cases it — it does not carry to
an arbitrary Z3/Prover9/TPTP export, where a bare atom is just another
uninterpreted symbol that could be assigned False in some model). Rendering
``⊤`` as an uninterpreted atom (``P(x) ∨ ¬P(x)`` for some fresh ``P``) is
truth-functionally a tautology but is an ugly, semantically unmotivated
detour through a predicate the concept never mentions.

Instead this module renders ``⊤``/``⊥`` through **equality**, which the FOL
Atom node already treats natively (``Atom("=", …)`` / ``Atom("≠", …)`` map to
Z3's built-in ``==``/``!=``, Prover9's ``=``, TPTP's ``=``/``!=`` — see
``Atom.to_z3``/``to_prover9``/``to_tptp`` in ``fol/_fol_nodes.py``):

- ``⊤``  ↦  ``x = x``   — valid in every model (reflexivity), matching how the
  tableau treats ``⊤``: it never causes a clash and never needs expansion,
  i.e. it constrains nothing and holds of every individual.
- ``⊥``  ↦  ``x ≠ x``   — unsatisfiable in every model, matching how the
  tableau treats ``⊥``: ``x : ⊥`` is *itself* a clash condition (see
  ``_clash`` in :mod:`unicode_fol_kit.dl.tableau`), i.e. no individual can
  satisfy it.

This is the standard textbook rendering, adds no extra symbols to the
signature, and is a genuine validity/unsatisfiability rather than a
model-dependent coincidence.

Variable freshness
-------------------
Each ``∃r.C`` / ``∀r.C`` introduces a bound variable named ``f"{var}_{n}"``
for a strictly increasing ``n``, where ``var`` is the *original* free
variable name the translation was started with (``concept_to_fol``'s ``var``
argument, or the ABox individual's name for :func:`abox_to_fol`). Because
the generated name always has a non-empty numeric suffix that the seed name
lacks, it can never collide with the seed itself. A single top-level call
(one call to :func:`concept_to_fol`, or one of the two independent halves of
:func:`subsumption_to_fol`) shares ONE counter across its entire recursive
walk, so EVERY restriction anywhere in that call's concept tree — nested
*or* sibling — gets a pairwise-distinct name; in particular no two
restrictions nested along the same path can ever reuse a name, so
``∃r.(∀s.C)`` translates to ``∃x_1 (r(x, x_1) ∧ ∀x_2 (s(x_1, x_2) → π(C,
x_2)))`` with no risk of the inner ``∀`` accidentally binding the outer
``∃``'s variable. Two SEPARATE top-level calls each start their own counter
back at 1 and so may independently mint the same name (e.g.
``subsumption_to_fol``'s antecedent and consequent, translated by two
independent calls to the internal translator, may both use ``x_1``) — this
is not a capture risk because the two calls' quantifier scopes are siblings
under ``→``, not nested inside one another.

Multi-role concepts and modal K
--------------------------------
ALC is exactly multi-modal K: an ``∃r.C``/``∀r.C`` pair over a *single* role
``r`` is precisely ``◇C``/``□C`` in ordinary (single-relation) modal K. This
is what :func:`concept_to_modal` implements, generalising the single-role
``_to_modal`` test helper in ``tests/test_dl_alc.py`` from a hardcoded role to
any single role name. It genuinely cannot go further: propositional modal K
has exactly ONE accessibility relation, so a concept using two or more
*distinct* role names has no faithful Box/Diamond rendering — encoding role
identity into, say, an indexed modality (``Knows(Constant(role), …)``) would
silently reinterpret the DL role as an epistemic agent, which is a different
logic with different validities (KT45 vs K). :func:`concept_to_modal`
therefore raises :class:`NotImplementedError` for multi-role concepts and
points callers at :func:`concept_to_fol`, which has no such limitation — a
role is just another predicate name, so FOL scales to any number of roles
for free.

GCIs, TBoxes, ABoxes
---------------------
:func:`subsumption_to_fol` renders a general concept inclusion ``sub ⊑ sup``
as its universal closure ``∀x (π(sub, x) → π(sup, x))`` — the standard
reduction, matching :func:`unicode_fol_kit.dl.tableau.subsumes`'s own
``sub ⊓ ¬sup`` unsatisfiability reduction (they are interderivable: ``sub ⊑
sup`` iff ``∀x (π(sub,x) → π(sup,x))`` is valid iff ``π(sub,x) ∧ ¬π(sup,x)``
is unsatisfiable). :func:`tbox_to_fol` conjoins one such closure per GCI in a
:class:`unicode_fol_kit.dl.tableau.TBox`; :func:`abox_to_fol` renders a
:class:`unicode_fol_kit.dl.tableau.ABox`'s concept assertions (``a : C`` ↦
``π(C, a)`` with the individual ``a`` as a FOL *constant*, not a variable —
this matters for the ASCII-only Prover9/TPTP exporters, which uppercase
``Variable`` names into their variable syntax but leave ``Constant`` names
alone) and role assertions (``(a, b) : r`` ↦ ``r(a, b)``), conjoined
together. An empty TBox/ABox translates to the same equality tautology used
for ``⊤`` (over a nullary placeholder constant, since there is no ``x`` in
scope at that point) — vacuously true, matching "no axioms" / "no
assertions" imposing no constraint.
"""

from typing import List

from ..fol.nodes import (
    Node, Variable, Constant, Atom,
    Not as _FNot, And as _FAnd, Or as _FOr, Implies, Quantifier,
    Box, Diamond,
)
from .concepts import Concept, Top, Bottom, Atomic, Not, And, Or, Exists, ForAll
from .tableau import TBox, ABox

__all__ = [
    "concept_to_fol", "subsumption_to_fol", "tbox_to_fol", "abox_to_fol",
    "concept_to_modal",
]


# --------------------------------------------------------------------------- #
# Standard translation to FOL.
# --------------------------------------------------------------------------- #

def _fresh_var_factory(base: str):
    """Return a callable producing variable names distinct from ``base`` and
    from every name it has already produced (see "Variable freshness" above).
    """
    counter = [0]

    def fresh() -> str:
        counter[0] += 1
        return f"{base}_{counter[0]}"

    return fresh


def _translate(concept: Concept, term: Node, fresh) -> Node:
    """Render ``concept`` as a FOL formula with ``term`` (a Variable or
    Constant) standing for the individual under discussion; ``fresh`` mints
    the bound variable for each nested restriction (see :func:`_fresh_var_factory`).
    """
    if isinstance(concept, Top):
        return Atom("=", (term, term))
    if isinstance(concept, Bottom):
        return Atom("≠", (term, term))
    if isinstance(concept, Atomic):
        return Atom(concept.name, (term,))
    if isinstance(concept, Not):
        return _FNot(_translate(concept.concept, term, fresh))
    if isinstance(concept, And):
        return _FAnd(_translate(concept.left, term, fresh),
                     _translate(concept.right, term, fresh))
    if isinstance(concept, Or):
        return _FOr(_translate(concept.left, term, fresh),
                    _translate(concept.right, term, fresh))
    if isinstance(concept, Exists):
        w = Variable(fresh())
        return Quantifier("∃", w, _FAnd(
            Atom(concept.role, (term, w)), _translate(concept.concept, w, fresh)))
    if isinstance(concept, ForAll):
        w = Variable(fresh())
        return Quantifier("∀", w, Implies(
            Atom(concept.role, (term, w)), _translate(concept.concept, w, fresh)))
    raise TypeError(f"concept_to_fol: unsupported concept {type(concept).__name__}")


def concept_to_fol(concept: Concept, var: str = "x") -> Node:
    """Render ``concept`` as a FOL formula ``π(concept, var)`` with one free
    variable ``var`` (see the module docstring for the translation rules).

    ``concept`` is satisfiable (:func:`unicode_fol_kit.dl.tableau.concept_satisfiable`)
    iff ``∃var π(concept, var)`` is FOL-satisfiable — wrap the result in a
    ``Quantifier("∃", Variable(var), …)`` to test that directly (e.g. via
    :func:`unicode_fol_kit.is_satisfiable`).
    """
    return _translate(concept, Variable(var), _fresh_var_factory(var))


def subsumption_to_fol(sub: Concept, sup: Concept, var: str = "x") -> Node:
    """Render the GCI ``sub ⊑ sup`` as its universal closure
    ``∀var (π(sub, var) → π(sup, var))``.

    ``sub ⊑ sup`` holds (:func:`unicode_fol_kit.dl.tableau.subsumes`) iff this
    formula is FOL-valid — check via :func:`unicode_fol_kit.is_valid`.
    """
    v = Variable(var)
    antecedent = _translate(sub, v, _fresh_var_factory(var))
    consequent = _translate(sup, v, _fresh_var_factory(var))
    return Quantifier("∀", v, Implies(antecedent, consequent))


def _tautology() -> Node:
    """A closed, genuinely valid formula — the FOL image of "no constraint"
    (an empty TBox or ABox). See "GCIs, TBoxes, ABoxes" in the module docstring.
    """
    c = Constant("_")
    return Atom("=", (c, c))


def _conjoin(parts: List[Node]) -> Node:
    """Fold a (possibly empty) list of formulas into a single conjunction."""
    if not parts:
        return _tautology()
    result = parts[0]
    for p in parts[1:]:
        result = _FAnd(result, p)
    return result


def tbox_to_fol(tbox: TBox, var: str = "x") -> Node:
    """Render every GCI/equivalence in ``tbox`` as its universal closure
    (:func:`subsumption_to_fol`) and conjoin them.

    An empty TBox renders as a tautology (no axioms ⇒ no constraint). The
    TBox is entailment-consistent with :func:`unicode_fol_kit.dl.tableau.TBox`:
    equivalences are stored as the pair of inclusions they abbreviate
    (``TBox.add_equivalence``), so they fall out of ``tbox.inclusions`` with
    no special case needed here.
    """
    return _conjoin([subsumption_to_fol(sub, sup, var) for sub, sup in tbox.inclusions])


def abox_to_fol(abox: ABox) -> Node:
    """Render every assertion in ``abox`` as a FOL formula and conjoin them.

    A concept assertion ``a : C`` becomes ``π(C, a)`` with the individual
    ``a`` translated as a :class:`~unicode_fol_kit.fol.nodes.Constant` (not a
    Variable — see "GCIs, TBoxes, ABoxes" above for why this matters). A role
    assertion ``(a, b) : r`` becomes ``r(a, b)``. An ABox with no assertions
    at all renders as a tautology.
    """
    parts: List[Node] = []
    for individual, concept in abox.concept_assertions:
        term = Constant(individual)
        parts.append(_translate(concept, term, _fresh_var_factory(individual)))
    for a, b, role in abox.role_assertions:
        parts.append(Atom(role, (Constant(a), Constant(b))))
    return _conjoin(parts)


# --------------------------------------------------------------------------- #
# Single-role concepts as propositional modal K formulas.
# --------------------------------------------------------------------------- #

def _roles_used(concept: Concept) -> set:
    """Return the set of distinct role names occurring anywhere in ``concept``."""
    if isinstance(concept, (Top, Bottom, Atomic)):
        return set()
    if isinstance(concept, Not):
        return _roles_used(concept.concept)
    if isinstance(concept, (And, Or)):
        return _roles_used(concept.left) | _roles_used(concept.right)
    if isinstance(concept, (Exists, ForAll)):
        return {concept.role} | _roles_used(concept.concept)
    raise TypeError(f"concept_to_modal: unsupported concept {type(concept).__name__}")


# A reserved nullary atom used only to spell out a structural tautology/
# contradiction (mirrors the reserved-atom idiom in unicode_fol_kit.atp.fitch's
# falsum handling). Since `p ∨ ¬p` is valid — and `p ∧ ¬p` unsatisfiable — for
# ANY p, this is correct regardless of what this particular name denotes, even
# in the (harmless) case that a concept happens to be literally named "⊤".
_MODAL_TRUE_ATOM = Atom("⊤", ())


def _to_modal(concept: Concept) -> Node:
    """Translate a single-role concept to a propositional modal-K formula."""
    if isinstance(concept, Atomic):
        return Atom(concept.name, ())
    if isinstance(concept, Top):
        return _FOr(_MODAL_TRUE_ATOM, _FNot(_MODAL_TRUE_ATOM))
    if isinstance(concept, Bottom):
        return _FAnd(_MODAL_TRUE_ATOM, _FNot(_MODAL_TRUE_ATOM))
    if isinstance(concept, Not):
        return _FNot(_to_modal(concept.concept))
    if isinstance(concept, And):
        return _FAnd(_to_modal(concept.left), _to_modal(concept.right))
    if isinstance(concept, Or):
        return _FOr(_to_modal(concept.left), _to_modal(concept.right))
    if isinstance(concept, Exists):
        return Diamond(_to_modal(concept.concept))
    if isinstance(concept, ForAll):
        return Box(_to_modal(concept.concept))
    raise TypeError(f"concept_to_modal: unsupported concept {type(concept).__name__}")


_MULTI_ROLE_MSG = (
    "concept_to_modal: concept uses {n} distinct roles {roles}; propositional "
    "modal K has exactly ONE accessibility relation, so per-role restrictions "
    "(∃r.C / ∀r.C for different r) cannot be faithfully rendered as Box/Diamond "
    "— there is no honest way to recover which role a given □/◇ came from. Use "
    "concept_to_fol instead: it has no such limitation, since a role is just "
    "another binary FOL predicate r(x, y) and FOL scales to any number of them."
)


def concept_to_modal(concept: Concept) -> Node:
    """Translate a SINGLE-role concept to a propositional modal-K formula.

    ``∃r.C`` ↦ ``◇C``, ``∀r.C`` ↦ ``□C`` (ALC restricted to one role is
    exactly modal K — see "Multi-role concepts and modal K" in the module
    docstring). ``concept`` is satisfiable (:func:`unicode_fol_kit.dl.tableau.concept_satisfiable`)
    iff its image here is satisfiable in K, decidable via
    :func:`unicode_fol_kit.atp.modal_tableau.is_modal_valid` on the negation
    (``not is_modal_valid(Not(concept_to_modal(concept)), frame="K")``).

    Raises:
        NotImplementedError: ``concept`` mentions two or more distinct role
            names — see :func:`concept_to_fol` for the general (FOL) translation.
    """
    roles = _roles_used(concept)
    if len(roles) > 1:
        raise NotImplementedError(
            _MULTI_ROLE_MSG.format(n=len(roles), roles=sorted(roles)))
    return _to_modal(concept)
