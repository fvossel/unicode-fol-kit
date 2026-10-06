"""An external OWL 2 DL reasoner backend for ``dl/`` — ALCHQ **+ inverse roles
(I) + nominals (O)**, via `owlready2 <https://owlready2.readthedocs.io>`_'s
bundled HermiT.

:mod:`unicode_fol_kit.dl.tableau`'s in-house tableau decides ALCHQ (and
refuses :class:`~unicode_fol_kit.dl.concepts.InverseRole`/
:class:`~unicode_fol_kit.dl.concepts.Nominal` by name — see that module's
"Inverse roles and nominals (I, O)" section for why: inverse roles break its
subset-blocking termination argument, and nominals need an individual-merging
machinery it has none of). This module decides the FULL fragment — ALCHQ plus
both — by handing the same :class:`~unicode_fol_kit.dl.tableau.TBox`/
:class:`~unicode_fol_kit.dl.tableau.ABox`/:class:`~unicode_fol_kit.dl.concepts.Concept`
AST to `HermiT <http://www.hermit-reasoner.com/>`_, a mainstream,
OWL2-DL-complete, actively maintained tableau reasoner, via ``owlready2``'s
Python bindings and bundled ``HermiT.jar``. This is the intentionally
NON-in-house route C45 (an in-house SHIQ/SHOIQ tableau rewrite) was rejected
in favour of: the boundary this kit draws is "detect and refuse I/O by name",
never "attempt to decide them with a homegrown algorithm".

Optional dependency, availability check
------------------------------------------
``owlready2`` (`PyPI <https://pypi.org/project/owlready2/>`_) is an optional
extra — :func:`available` is PURE DISCOVERY (``importlib.util.find_spec``, no
import), mirroring :meth:`unicode_fol_kit.atp.cvc5_backend.Cvc5Backend.available`'s
exact convention, so probing it never pays the import cost. Every public
function in this module calls :func:`available` internally and raises
:class:`OwlReasonerError` (reusing
:class:`unicode_fol_kit.atp.protocol.BackendUnavailable` the way
:mod:`unicode_fol_kit.hets.docker` already imports across a subpackage
boundary — the same precedent this module follows for ``dl/``'s own first
``atp`` import) when it is missing, rather than silently skipping. A JVM is
also required (HermiT runs as a ``java`` subprocess, invoked BY owlready2,
not by this module): this kit assumes one is already on ``PATH`` (Java is
NOT probed by :func:`available`, since owlready2 only ever discovers it at
actual reasoner-invocation time — a JVM launch failure surfaces as
``OwlReadyJavaError``, re-raised here as :class:`OwlReasonerError` naming
what failed, never silently). On Windows, ``owlready2.JAVA_EXE`` (default
``"java"``) may need to be set explicitly if ``java`` is not literally on
``PATH`` under that name; this module never touches that setting itself.

Licensing
----------
``owlready2`` itself is **LGPL-3.0-or-later** (confirmed from the installed
package's own metadata: ``pip show owlready2`` prints
``License-Expression: LGPL-3.0-or-later``) — the first LGPL/copyleft optional
dependency this kit carries (see the ``owl`` extra note in ``pyproject.toml``,
added via this task's ``integration`` request). Its wheel ALSO bundles a
second reasoner, Pellet, which is dual-licensed **AGPL-3.0** (confirmed from
``owlready2/pellet/LICENSE.txt`` in the installed package) — this module
never calls ``owlready2.sync_reasoner_pellet``, only
``sync_reasoner_hermit`` (whose bundled ``HermiT.jar`` is LGPL, same as the
Python package), so no AGPL code path is ever exercised by this kit; the AGPL
jar merely ships, unused, inside the dependency's wheel.

Translation route — direct to owlready2's Python object model, not through
``owl_functional.py``'s text
------------------------------------------------------------------------------
:mod:`unicode_fol_kit.dl.owl_functional` is this kit's OWL 2 Functional-Style
Syntax document reader/writer, and stays the ALCHQ-only "document writer" for
that fragment (unchanged by this module — see its own docstring): it is NOT
extended to parse/render ``ObjectInverseOf``/``ObjectOneOf``, because
``owlready2`` has no Functional-Style Syntax reader at all (confirmed: it
reads only RDF/XML, OWL/XML and NTriples — see ``owlready2/namespace.py``'s
``Ontology.load``/``graph.parse``), so round-tripping through that text would
buy nothing here and risk a second, redundant, untested translation path.
Instead this module translates :class:`~unicode_fol_kit.dl.tableau.TBox`/
:class:`~unicode_fol_kit.dl.tableau.ABox`/:class:`~unicode_fol_kit.dl.concepts.Concept`
DIRECTLY into ``owlready2``'s own Python class-expression API
(``And``/``Or``/``Not``/``Inverse``/``OneOf``/``Restriction`` — see
``owlready2/class_construct.py``), the same object model ``owlready2``'s own
documentation builds ontologies with. Every entity (class/role/individual)
gets a FRESH, synthetic, opaque local name (``C1``, ``R1``, ``I1``, …), never
this kit's own name string verbatim: this kit's :class:`~unicode_fol_kit.dl.concepts.Atomic`/
role/individual names are arbitrary opaque strings that may contain
characters illegal in an OWL/RDF local name (whitespace, ``#``, non-ASCII
glyphs used elsewhere in this kit — see :mod:`unicode_fol_kit.dl.owl_functional`'s
own "IRIs and names" section for the identical concern there), and since
every query this module answers is a yes/no verdict (never "what is this
entity called back"), there is nothing to lose by never round-tripping the
original name through owlready2's IRI machinery at all.

Each of this module's ``external_*`` functions builds a FRESH ``owlready2.World()``
(never the shared global default world) and a fresh ``Ontology`` inside it, so
two calls never share reasoner state — confirmed empirically (see this
task's scratch notes): mutating one ``World``'s entities is invisible to
another. A **general concept inclusion** ``sub ⊑ sup`` (this kit's ``TBox``
is always a GENERAL TBox — see :mod:`unicode_fol_kit.dl.tableau`) is asserted
via ``owlready2.GeneralClassAxiom``, the native OWL 2 mechanism for a
``SubClassOf`` whose LEFT side is an arbitrary (possibly anonymous) class
expression — EXCEPT for the two antecedent shapes ``GeneralClassAxiom``
cannot take directly (confirmed empirically: its left side must be a genuine
``Construct``, e.g. ``And``/``Or``/``Not``/``Restriction``/``OneOf``, not a
plain named entity like ``owl:Thing`` — mutating ``owl:Thing`` itself would
also leak across every ``World`` at once, since it is a single shared Python
object, not a per-world one): ``sub = Bottom()`` is skipped outright (``∅ ⊑
sup`` is a tautology, exactly mirroring how the in-house tableau's own
``internalized()`` would trivially satisfy it too), and ``sub = Top()``
routes through a lazily-created per-ontology helper class equivalent to
``owl:Thing`` (``_Domain.equivalent_to = [Thing]``, then
``_Domain.is_a.append(translated sup)``) — which correctly forces every
individual into ``sup``, confirmed empirically, without ever touching the
shared ``Thing`` object itself. An ``Atomic`` antecedent uses the normal,
better-supported ``named_class.is_a.append(...)`` path instead of a
``GeneralClassAxiom`` at all (no anonymous left side needed when the
antecedent already names a class).

What each function decides
------------------------------
Every ``external_*`` function mirrors its :mod:`unicode_fol_kit.dl.tableau`
namesake's SIGNATURE and REDUCTION exactly (``external_subsumes`` reduces to
``external_concept_satisfiable`` exactly the way ``subsumes`` reduces to
``concept_satisfiable``, and so on) — this is deliberate: it is what makes
the differential test battery in ``tests/test_owl_reasoner.py`` meaningful
(every ALCHQ fixture in ``tests/test_dl_alc.py``/``test_dl_alcq.py``/
``test_dl_rbox.py``/``test_dl_classify.py`` decided through BOTH this
module's reduction chain and the tableau's own is comparing the SAME
question, not two differently-shaped ones), and it lets this module cover
the full I/O-extended fragment (concept/ABox consistency, subsumption,
equivalence, instance checking/retrieval, realization) with only ONE genuine
HermiT-invoking primitive underneath (:func:`_kb_consistent`), exactly the
way the in-house tableau has only ``_solve`` underneath ITS whole public API.

Each call to :func:`_kb_consistent` spawns a fresh ``java`` subprocess (via
``owlready2.sync_reasoner_hermit``), so this module is orders of magnitude
slower per call than the in-house tableau — expected and acceptable for an
occasional external cross-check, not a hot-path reasoner; the differential
test battery deliberately runs a curated, small fixture set rather than
every existing ALCHQ test file verbatim, to keep the live test run's JVM
subprocess count bounded.

Public API: :func:`available`, :func:`external_concept_satisfiable`,
:func:`external_concept_unsatisfiable`, :func:`external_subsumes`,
:func:`external_equivalent`, :func:`external_abox_consistent`,
:func:`external_instance_check`, :func:`external_instance_retrieval`,
:func:`external_realize`, :func:`external_realize_all`, :class:`OwlReasonerError`.
"""

import importlib.util
from typing import Dict, List, Optional, Set

from ..atp.protocol import BackendUnavailable
from .concepts import (
    Concept, Top, Bottom, Atomic, Not, And, Or, Exists, ForAll, AtLeast, AtMost,
    InverseRole, Nominal, HasValue, DATA_CONCEPTS,
)
from .tableau import (
    TBox, ABox, UnsupportedAxiomError, UnsupportedConceptError, _RBox,
    _abox_individual_names, _check_simple_role_box, _concept_individual_names,
    _data_layer_kinds, _reject_abox_roles, _reject_concept_role,
    _reject_concept_roles_deep, _tbox_class_expressions, _validate_data_box,
    _validate_role_box,
)

__all__ = [
    "available",
    "external_concept_satisfiable", "external_concept_unsatisfiable",
    "external_subsumes", "external_equivalent",
    "external_abox_consistent", "external_instance_check", "external_instance_retrieval",
    "external_realize", "external_realize_all",
    "OwlReasonerError",
]


class OwlReasonerError(BackendUnavailable):
    """``owlready2`` is not installed, or HermiT (invoked through it) failed to
    run — a missing/broken JVM, a HermiT crash, or any other reasoner-invocation
    failure that is not itself an ``OwlReadyInconsistentOntologyError`` (which
    this module treats as an ordinary, expected "inconsistent" verdict, not an
    error — see :func:`_kb_consistent`). Reuses
    :class:`unicode_fol_kit.atp.protocol.BackendUnavailable` (see the module
    docstring), so a caller that already handles that exception for the kit's
    other optional backends (cvc5, Hets/Docker, …) handles this one the same
    way for free.
    """


def available() -> bool:
    """True iff ``owlready2`` is importable — pure discovery, no import, no JVM
    probe (see the module docstring's "Optional dependency" section).
    """
    return importlib.util.find_spec("owlready2") is not None


def _require_available():
    """Return the imported ``owlready2`` module, or raise :class:`OwlReasonerError`
    naming the missing extra (see :func:`available`). The import itself stays
    lazy — done here, not at this module's top level — so importing
    ``dl.owl_reasoner`` never requires ``owlready2`` to be installed; only
    actually USING it does (see the module docstring's "Optional dependency"
    section).
    """
    if not available():
        raise OwlReasonerError(
            "dl.owl_reasoner: owlready2 is not installed — install the optional "
            "'owl' extra (`pip install unicode-fol-kit[owl]`, i.e. "
            "`pip install owlready2`) to use the external, HermiT-backed OWL 2 "
            "DL reasoner for InverseRole/Nominal (I/O) beyond this kit's "
            "in-house ALCHQ tableau (see dl.tableau's 'Inverse roles and "
            "nominals (I, O)' section).")
    import owlready2
    return owlready2


# --------------------------------------------------------------------------- #
# Translation: Concept/TBox/ABox -> a fresh owlready2 World/Ontology.
# --------------------------------------------------------------------------- #

class _Ctx:
    """Per-call translation state: the fresh ``owlready2``/``World``/``Ontology``
    triple, and lazily-populated name -> owlready2-entity maps (see the module
    docstring's "Translation route" section for why entities get fresh
    synthetic names rather than this kit's own name strings verbatim).
    """

    __slots__ = ("ow", "world", "onto", "characteristics",
                 "_classes", "_roles", "_individuals", "_domain", "_counter", "_below")

    def __init__(self, ow, world, onto, characteristics: Dict[str, Set[str]]):
        self.ow = ow
        self.world = world
        self.onto = onto
        # ``owlready2 base name -> the role names carrying that characteristic``
        # (see :data:`_CHARACTERISTIC_BASES`). All SIX characteristics, not just
        # transitivity: owlready2 needs every one of them among the property
        # class's BASES at creation time, so they cannot be added later and a
        # route that carried only one would silently drop the other five — and
        # this route is where the in-house tableau's own refusals send the user.
        self.characteristics = characteristics
        self._classes: Dict[str, object] = {}
        self._roles: Dict[str, object] = {}
        self._individuals: Dict[str, object] = {}
        self._domain = None
        self._counter = 0
        # ``("class" | "role") -> name -> the names directly above it`` for the inclusions
        # between two NAMED entities that were stated as owlready2 sub-class / sub-property
        # links (see :meth:`state_named_inclusion`).
        self._below: Dict[str, Dict[str, Set[str]]] = {"class": {}, "role": {}}

    def state_named_inclusion(self, kind: str, sub_name: str, sup_name: str,
                              sub_entity, sup_entity) -> None:
        """Assert ``sub ⊑ sup`` between two named classes (``kind="class"``) or two plain
        properties (``kind="role"``).

        owlready2 keeps a named class (property) under another as a Python base class, and
        Python refuses a cycle of bases with a ``TypeError``. Two named entities below each
        other, an entity below itself, a longer ring, ``EquivalentClasses`` and
        ``EquivalentObjectProperties`` all read as such a cycle. An inclusion that would close
        one is therefore stated as the equivalence ``sub ≡ sup``, which is what the ring says:
        ``sup`` is already below ``sub`` through the links stated so far, so ``sub ⊑ sup``
        makes every entity on the ring equivalent, and ``sub ≡ sup`` adds only the converse
        that the ring already gives. An entity below itself says nothing and is not stated.
        """
        if sub_name == sup_name:
            return
        links = self._below[kind]
        reachable, pending = set(), [sup_name]
        while pending:
            name = pending.pop()
            if name in reachable:
                continue
            reachable.add(name)
            pending.extend(links.get(name, ()))
        if sub_name in reachable:
            sub_entity.equivalent_to.append(sup_entity)
        else:
            links.setdefault(sub_name, set()).add(sup_name)
            sub_entity.is_a.append(sup_entity)

    def _fresh_name(self, prefix: str) -> str:
        self._counter += 1
        return f"{prefix}{self._counter}"

    def cls(self, name: str):
        """The owlready2 named class for this kit's ``Atomic`` name ``name``."""
        if name not in self._classes:
            self._classes[name] = self.ow.types.new_class(self._fresh_name("C"), (self.ow.Thing,))
        return self._classes[name]

    def _role_bases(self, name: str) -> tuple:
        """``(ObjectProperty, *every declared characteristic's owlready2 class)``
        for the role named ``name`` — the bases tuple ``role_obj`` creates it with.
        """
        bases = [self.ow.ObjectProperty]
        for base_name, roles in self.characteristics.items():
            if name in roles:
                bases.append(getattr(self.ow, base_name))
        return tuple(bases)

    def role_obj(self, name: str):
        """The owlready2 object property for this kit's role name ``name``, with
        every declared characteristic among its bases at CREATION time
        (owlready2 needs them up front, not added after the fact).
        """
        if name not in self._roles:
            self._roles[name] = self.ow.types.new_class(
                self._fresh_name("R"), self._role_bases(name))
        return self._roles[name]

    def role(self, role_field):
        """Resolve a ``role`` field (a plain ``str``, or an
        :class:`~unicode_fol_kit.dl.concepts.InverseRole`) to the owlready2
        property expression to use in a restriction: the property itself, or
        ``owlready2.Inverse(property)``.
        """
        if isinstance(role_field, InverseRole):
            return self.ow.Inverse(self.role_obj(role_field.role))
        return self.role_obj(role_field)

    def ind(self, name: str):
        """The owlready2 named individual for this kit's individual name ``name``."""
        if name not in self._individuals:
            self._individuals[name] = self.ow.Thing(self._fresh_name("I"))
        return self._individuals[name]

    def domain_class(self):
        """A per-ontology class equivalent to ``owl:Thing`` — see the module
        docstring's "Translation route" section for why a ``Top()`` GCI
        antecedent routes through this rather than ``owlready2.Thing`` itself.
        """
        if self._domain is None:
            self._domain = self.ow.types.new_class(self._fresh_name("D"), (self.ow.Thing,))
            self._domain.equivalent_to = [self.ow.Thing]
        return self._domain


def _translate_concept(concept: Concept, ctx: _Ctx):
    """Translate ``concept`` into an owlready2 class expression (see the module
    docstring's "Translation route" section). Covers the FULL ALCHQ + I + O
    fragment this module decides — every :class:`Concept` subtype, including
    :class:`InverseRole`-valued roles and :class:`Nominal`.

    An OWL 2 built-in property name as a restriction's role is refused by name
    (:func:`~unicode_fol_kit.dl.tableau._reject_concept_role`), exactly as the
    in-house tableau and the FOL image refuse it: owlready2 would create an
    ORDINARY property of that name, and an oracle that answers about a
    different restriction agrees with nothing for the right reason.
    """
    _reject_concept_role(concept, where="dl.owl_reasoner")
    if isinstance(concept, Top):
        return ctx.ow.Thing
    if isinstance(concept, Bottom):
        return ctx.ow.Nothing
    if isinstance(concept, Atomic):
        return ctx.cls(concept.name)
    if isinstance(concept, Nominal):
        return ctx.ow.OneOf([ctx.ind(concept.individual)])
    if isinstance(concept, HasValue):
        # owlready2 spells ObjectHasValue(P a) as `prop.value(individual)`.
        return ctx.role(concept.role).value(ctx.ind(concept.individual))
    if isinstance(concept, Not):
        return ctx.ow.Not(_translate_concept(concept.concept, ctx))
    if isinstance(concept, And):
        return ctx.ow.And([_translate_concept(concept.left, ctx),
                            _translate_concept(concept.right, ctx)])
    if isinstance(concept, Or):
        return ctx.ow.Or([_translate_concept(concept.left, ctx),
                           _translate_concept(concept.right, ctx)])
    if isinstance(concept, Exists):
        return ctx.role(concept.role).some(_translate_concept(concept.concept, ctx))
    if isinstance(concept, ForAll):
        return ctx.role(concept.role).only(_translate_concept(concept.concept, ctx))
    if isinstance(concept, AtLeast):
        return ctx.role(concept.role).min(concept.n, _translate_concept(concept.concept, ctx))
    if isinstance(concept, AtMost):
        return ctx.role(concept.role).max(concept.n, _translate_concept(concept.concept, ctx))
    if isinstance(concept, DATA_CONCEPTS):
        raise UnsupportedConceptError(
            f"dl.owl_reasoner: the data restriction {type(concept).__name__} "
            f"({concept.to_unicode()}) is not wired to this external route: "
            f"owlready2 could express it, but this module does not translate the "
            f"data layer, and an oracle that quietly dropped it would agree with "
            f"everything. Ask the FOL image: kb = dl.kb_to_fol(tbox, abox, "
            f"query=[concept]), then api.prove(kb.unsatisfiability_goal(concept), "
            f"kb.tbox_premises) (kb.subsumption_goal and kb.instance_goal are the "
            f"other two questions; 'proved' transfers to OWL 2, 'refuted' does not: "
            f"see kb.refutation_is_decisive) — or decide facet arithmetic over "
            f"the data ranges alone with atp.z3_arith.is_valid_arith.")
    raise TypeError(f"dl.owl_reasoner: unsupported concept {type(concept).__name__}")


def _add_gci(sub: Concept, sup: Concept, ctx: _Ctx) -> None:
    """Assert the general concept inclusion ``sub ⊑ sup`` into ``ctx``'s
    ontology, choosing the cheapest correct owlready2 encoding for the shape
    of ``sub`` (see the module docstring's "Translation route" section for
    why ``Top``/``Bottom``/``Atomic`` antecedents each need their own case).
    """
    if isinstance(sub, Bottom):
        return  # ∅ ⊑ sup is a tautology; nothing to assert
    if isinstance(sub, Top):
        ctx.domain_class().is_a.append(_translate_concept(sup, ctx))
        return
    if isinstance(sub, Atomic):
        if isinstance(sup, Atomic):
            ctx.state_named_inclusion("class", sub.name, sup.name, ctx.cls(sub.name), ctx.cls(sup.name))
        else:
            ctx.cls(sub.name).is_a.append(_translate_concept(sup, ctx))
        return
    gca = ctx.ow.GeneralClassAxiom(_translate_concept(sub, ctx))
    gca.is_a.append(_translate_concept(sup, ctx))


#: ``TBox field -> the owlready2 property class that expresses it as a BASE``.
#: owlready2 requires a characteristic among the property class's bases at
#: creation time, so ``_Ctx`` has to know all six BEFORE any role is built —
#: hence a table read by ``_characteristics`` rather than six inline tests.
_CHARACTERISTIC_BASES = {
    "transitive_roles": "TransitiveProperty",
    "symmetric_roles": "SymmetricProperty",
    "asymmetric_roles": "AsymmetricProperty",
    "reflexive_roles": "ReflexiveProperty",
    "irreflexive_roles": "IrreflexiveProperty",
    "functional_roles": "FunctionalProperty",
    "inverse_functional_roles": "InverseFunctionalProperty",
}


def _characteristics(tbox: TBox) -> Dict[str, Set[str]]:
    """``owlready2 base name -> the role names carrying it`` for ``tbox``."""
    return {base: set(getattr(tbox, field))
            for field, base in _CHARACTERISTIC_BASES.items()}


def _role_expr(role_field, ctx: _Ctx):
    """A role-box entry (a plain name, or an
    :class:`~unicode_fol_kit.dl.concepts.InverseRole`) as the owlready2
    property expression to use on either side of a sub-property axiom.

    ``ctx.role`` already does exactly this for a restriction's role; calling it
    here is what stops an ``InverseRole`` being used as a DICT KEY and coming
    back out as a brand-new atomic property — which is what ``_build_kb`` did
    until 0.30.0, making ``external_subsumes(…, TBox().add_role_inclusion('r',
    InverseRole('s')))`` answer a question about an ontology that never had the
    axiom.
    """
    return ctx.role(role_field)


def _plain_sub_role(sub_role, super_role):
    """``(sub_role, super_role)`` with a PLAIN role on the left — owlready2
    attaches a sub-property axiom to the property CLASS on the left
    (``is_a.append``), which an ``Inverse(...)`` expression is not (it crashed
    with an ``AttributeError`` for ``s⁻ ⊑ r``, while ``r ⊑ s⁻`` built).

    The rewrite is an equivalence, not an approximation: ``r⁻ ⊑ s`` says every
    ``r(y, x)`` is an ``s(x, y)``, i.e. every ``r(x, y)`` is an ``s(y, x)``,
    which is ``r ⊑ s⁻``; and ``r⁻ ⊑ s⁻`` is ``r ⊑ s``, the inverses cancelling.
    """
    if isinstance(sub_role, InverseRole):
        inner = (super_role.role if isinstance(super_role, InverseRole)
                 else InverseRole(super_role))
        return sub_role.role, inner
    return sub_role, super_role


def _add_inverse_pair(ctx: _Ctx, partner: Dict[str, str], p: str, q: str) -> None:
    """Assert ``InverseObjectProperties(p q)`` (``p ≡ q⁻``) into ``ctx``.

    owlready2's ``inverse_property`` holds ONE property, and assigning it a
    second time REPLACES the first — so ``Inv(p, q)`` together with ``Inv(p, r)``
    kept only one of them and the oracle reasoned over a weaker knowledge base.
    The second pair is not lost by being kept as an EQUIVALENCE instead: if ``p``
    already has the inverse ``q0`` then ``q0 ≡ q`` (both are ``p⁻``), and the
    symmetric case likewise. ``partner`` records the one inverse each property
    was given.
    """
    if p in partner:
        if partner[p] != q:
            ctx.role_obj(partner[p]).equivalent_to.append(ctx.role_obj(q))
    elif q in partner:
        if partner[q] != p:
            ctx.role_obj(partner[q]).equivalent_to.append(ctx.role_obj(p))
    else:
        ctx.role_obj(p).inverse_property = ctx.role_obj(q)
        partner[p], partner[q] = q, p


def _build_kb(ctx: _Ctx, tbox: TBox, abox: ABox) -> None:
    """Populate ``ctx``'s ontology with ``tbox``'s role box + GCIs and ``abox``'s
    assertions. Must run inside a ``with ctx.onto:`` block (every
    ``ctx.ow.types.new_class``/``GeneralClassAxiom`` call needs the current
    namespace set — see ``owlready2``'s own convention).

    EVERY role-box field is rendered. This module is one of the kit's two
    INDEPENDENT oracles, and it is the one the in-house tableau's own refusal
    messages send the user to — an oracle that silently dropped the axiom under
    test would agree with everything, and would make those messages dishonest.
    ``tests/test_dl_route_agreement.py`` checks a verdict per field that FLIPS
    when the field is dropped, which is what makes that claim checkable.
    """
    for sub_role, super_role in tbox.role_inclusions:
        sub_role, super_role = _plain_sub_role(sub_role, super_role)
        if isinstance(super_role, str):
            ctx.state_named_inclusion("role", sub_role, super_role,
                                      _role_expr(sub_role, ctx), _role_expr(super_role, ctx))
        else:
            _role_expr(sub_role, ctx).is_a.append(_role_expr(super_role, ctx))
    # APPEND, never assign: owlready2 stores a property's property chains,
    # domains and ranges as lists, and `role.domain = [...]` REPLACES what an
    # earlier axiom put there. Two ObjectPropertyDomain axioms on one role are
    # a CONJUNCTION (an element with an r-successor is in both classes), so
    # assigning kept only the last and the oracle reasoned over a weaker
    # knowledge base than the tableau and the FOL image -- silently, which is
    # the one thing an oracle must not do. The same for ranges and for two
    # chains with one super-property.
    for chain, super_role in tbox.role_chains:
        ctx.role_obj(super_role).property_chain.append(
            ctx.ow.PropertyChain([ctx.role_obj(role) for role in chain]))
    partner: Dict[str, str] = {}
    for p, q in tbox.inverse_role_pairs:
        _add_inverse_pair(ctx, partner, p, q)
    for left, right in tbox.disjoint_role_pairs:
        ctx.ow.AllDisjoint([ctx.role_obj(left), ctx.role_obj(right)])
    # The six characteristics need no statement here: they are already among
    # each property class's bases (see _Ctx.role_obj). A role that occurs ONLY
    # in a characteristic declaration still has to be created, though, or the
    # declaration would never reach the ontology at all.
    for roles in ctx.characteristics.values():
        for role in sorted(roles):
            ctx.role_obj(role)
    for role, filler in tbox.role_domains:
        ctx.role_obj(role).domain.append(_translate_concept(filler, ctx))
    for role, filler in tbox.role_ranges:
        ctx.role_obj(role).range.append(_translate_concept(filler, ctx))
    for sub, sup in tbox.inclusions:
        _add_gci(sub, sup, ctx)
    for individual, concept in abox.concept_assertions:
        ctx.ind(individual).is_a.append(_translate_concept(concept, ctx))
    for a, b, role in abox.role_assertions:
        role_obj = ctx.role_obj(role)
        if issubclass(role_obj, ctx.ow.FunctionalProperty):
            # owlready2 keeps the value of a FUNCTIONAL property as ONE attribute (None
            # while unset), not as a list to append to, and a second assignment would
            # REPLACE the first: two successors of one individual (which functionality
            # then identifies, or which `distinct_assertions` makes inconsistent) would
            # reach HermiT as one. The assertion r(a, b) is stated instead as the class
            # assertion a : ∃r.{b} (ObjectHasValue), which OWL 2 defines to mean the same
            # and which the negative assertions below already use. The test is the property
            # CLASS, not the role names the TBox declared functional: a sub-property of a
            # functional property is a Python subclass of it and holds one value as well.
            ctx.ind(a).is_a.append(role_obj.value(ctx.ind(b)))
        else:
            getattr(ctx.ind(a), role_obj.name).append(ctx.ind(b))
    for a, b in abox.distinct_assertions:
        ctx.ow.AllDifferent([ctx.ind(a), ctx.ind(b)])
    for a, b in abox.same_assertions:
        # owlready2's own spelling of SameIndividual: the two individuals
        # become one entity by equivalence, which is what HermiT then reads.
        ctx.ind(a).equivalent_to.append(ctx.ind(b))
    for a, b, role in abox.negative_role_assertions:
        role_obj = ctx.role_obj(role)
        ctx.ind(a).is_a.append(ctx.ow.Not(role_obj.value(ctx.ind(b))))


def _reject_data_layer(tbox: TBox, abox: ABox) -> None:
    """Refuse, by name, a knowledge base that carries a DATA axiom kind.

    This module is one of the kit's two INDEPENDENT oracles, and an oracle that
    silently dropped the axiom under test would agree with everything. owlready2
    has the machinery for data properties and datatypes, but this module's
    translation does not use it, so the honest answer is a refusal that names
    the kinds and the routes that DO answer (the FOL image; for facet arithmetic
    alone, ``atp.z3_arith``). Data CONCEPTS are refused at translation time, in
    :func:`_translate_concept`.
    """
    kinds = _data_layer_kinds(tbox, abox)
    if kinds:
        raise UnsupportedAxiomError(
            f"dl.owl_reasoner: this knowledge base carries data-layer axiom "
            f"kinds ({', '.join(kinds)}), which this external route does not "
            f"translate — it refuses them by name rather than answer for a "
            f"weaker knowledge base. The in-house tableau has no data domain "
            f"either, so the route that answers is the FOL image: "
            f"kb = dl.kb_to_fol(tbox, abox, query=[concept]), then "
            f"api.prove(kb.unsatisfiability_goal(concept), kb.tbox_premises) — "
            f"or kb.subsumption_goal / kb.instance_goal; 'proved' transfers to "
            f"OWL 2, 'refuted' does not (kb.refutation_is_decisive). Facet "
            f"arithmetic over the data ranges alone is decided by "
            f"atp.z3_arith.is_valid_arith.")


def _guard_inputs(tbox: Optional[TBox], abox: Optional[ABox],
                  concepts=()) -> None:
    """The refusals every ``external_*`` function owes BEFORE it builds
    anything — in ONE place, so an entry point that makes no HermiT call at all
    (``external_realize`` on an empty vocabulary, ``external_realize_all`` and
    ``external_instance_retrieval`` on an empty ABox) still runs them: those
    returned a quiet ``[]`` for a knowledge base the other seven refuse.

    The stored role box and data box must be well-formed — the SAME validation
    the in-house tableau and the FOL image run (:func:`_validate_role_box`) —;
    an ABox assertion must not carry an OWL 2 built-in property name; the data
    layer is refused by name; the role box must satisfy OWL 2's simple-role
    restriction; and no class expression may use a built-in property name as a
    role.
    """
    tbox = tbox if tbox is not None else TBox()
    _validate_role_box(tbox, where="dl.owl_reasoner")
    _validate_data_box(tbox, where="dl.owl_reasoner")
    _reject_abox_roles(abox, where="dl.owl_reasoner")
    _reject_data_layer(tbox, abox if abox is not None else ABox())
    _check_simple_role_box(tbox, _RBox.from_tbox(tbox))
    for concept in concepts:
        _reject_concept_roles_deep(concept, where="dl.owl_reasoner")
    for concept in _tbox_class_expressions(tbox):
        _reject_concept_roles_deep(concept, where="dl.owl_reasoner")
    if abox is not None:
        for _individual, concept in abox.concept_assertions:
            _reject_concept_roles_deep(concept, where="dl.owl_reasoner")


def _kb_consistent(tbox: Optional[TBox], abox: ABox) -> bool:
    """Build a fresh ``owlready2`` ``World``/``Ontology`` encoding ``(tbox,
    abox)``, run HermiT via ``sync_reasoner_hermit``, and return True iff the
    knowledge base is consistent. The ONE HermiT-invoking primitive every
    other function in this module reduces to (see the module docstring's
    "What each function decides" section).

    Raises:
        OwlReasonerError: owlready2 is missing, or HermiT/the JVM failed for
            a reason other than genuine inconsistency.
        ~unicode_fol_kit.dl.tableau.NonSimpleRoleError:
            the role box violates OWL 2's own SIMPLE-role
            restriction (Structural Specification §11). Checked with the KIT's
            own check, so the same role box is refused with the same message on
            EVERY route, rather than surfacing as a HermiT error here and as a
            tableau error there.
    """
    ow = _require_available()
    tbox = tbox if tbox is not None else TBox()
    _guard_inputs(tbox, abox)
    world = ow.World()
    onto = world.get_ontology("http://unicode-fol-kit.invalid/kb#")
    ctx = _Ctx(ow, world, onto, _characteristics(tbox))
    with onto:
        _build_kb(ctx, tbox, abox)
    try:
        ow.sync_reasoner_hermit(world, debug=0)
        return True
    except ow.OwlReadyInconsistentOntologyError:
        return False
    except ow.OwlReadyJavaError as exc:
        raise OwlReasonerError(
            f"dl.owl_reasoner: HermiT (invoked via owlready2, requires a JVM "
            f"on PATH) failed: {exc}") from exc


# --------------------------------------------------------------------------- #
# Public API — mirrors dl.tableau's, over the ALCHQ + I + O fragment.
# --------------------------------------------------------------------------- #

#: The name :func:`external_concept_satisfiable` gives its probe individual when
#: no individual of the question already has it.
_PROBE_INDIVIDUAL = "_probe"


def _fresh_individual(base: str, taken: Set[str]) -> str:
    """``base``, or ``base`` followed by the first number that makes it a name
    outside ``taken`` — an individual name the question does not already use.

    Individual names are compared exactly (they are case-sensitive strings), so
    exact membership in ``taken`` is the whole test.
    """
    name, number = base, 0
    while name in taken:
        number += 1
        name = f"{base}{number}"
    return name


def external_concept_satisfiable(concept: Concept, tbox: Optional[TBox] = None) -> bool:
    """Return True iff ``concept`` is satisfiable with respect to ``tbox`` —
    the external-reasoner twin of :func:`unicode_fol_kit.dl.tableau.concept_satisfiable`,
    but over the FULL ALCHQ + I + O fragment (inverse roles, nominals). Reduced
    to :func:`_kb_consistent` via a single probe individual, exactly the way
    the in-house tableau reduces it to one fresh branch node. The probe is
    called by a name that no nominal or value restriction of ``concept`` or of
    ``tbox`` mentions: a probe that shared the name of such an individual would
    BE that individual, and the question would be asked about it and not about
    some element.
    """
    _require_available()
    _guard_inputs(tbox, ABox().assert_concept(_PROBE_INDIVIDUAL, concept))
    probe = _fresh_individual(_PROBE_INDIVIDUAL, _concept_individual_names(concept).union(
        *(_concept_individual_names(expression)
          for expression in _tbox_class_expressions(tbox))))
    return _kb_consistent(tbox, ABox().assert_concept(probe, concept))


def external_concept_unsatisfiable(concept: Concept, tbox: Optional[TBox] = None) -> bool:
    """Return True iff ``concept`` is unsatisfiable with respect to ``tbox``."""
    return not external_concept_satisfiable(concept, tbox)


def external_subsumes(sub: Concept, sup: Concept, tbox: Optional[TBox] = None) -> bool:
    """Return True iff ``tbox`` entails ``sub ⊑ sup`` — the same ``sub ⊓ ¬sup``
    unsatisfiability reduction :func:`unicode_fol_kit.dl.tableau.subsumes` uses.
    """
    return not external_concept_satisfiable(And(sub, Not(sup)), tbox)


def external_equivalent(c: Concept, d: Concept, tbox: Optional[TBox] = None) -> bool:
    """Return True iff ``tbox`` entails ``c ≡ d`` (mutual subsumption)."""
    return external_subsumes(c, d, tbox) and external_subsumes(d, c, tbox)


def external_abox_consistent(abox: ABox, tbox: Optional[TBox] = None) -> bool:
    """Return True iff the knowledge base ``(tbox, abox)`` is consistent."""
    return _kb_consistent(tbox, abox)


def _abox_with(abox: ABox, individual: str, concept: Concept) -> ABox:
    """A copy of ``abox`` with one extra concept assertion ``individual : concept``
    (used by :func:`external_instance_check`'s entailment reduction, mirroring
    :func:`unicode_fol_kit.dl.tableau.instance_check`'s own copy-and-extend).

    :meth:`~unicode_fol_kit.dl.tableau.ABox.copy`, not a field-by-field
    reconstruction: this module is one of the kit's INDEPENDENT oracles, and
    an oracle that silently drops an assertion kind the caller supplied
    agrees with the in-house tableau for the wrong reason. (Field-by-field is
    what this did until 0.30.0, and it dropped ``same_assertions`` /
    ``negative_role_assertions`` the moment they existed.)
    """
    probe = abox.copy()
    probe.assert_concept(individual, concept)
    return probe


def external_instance_check(abox: ABox, individual: str, concept: Concept,
                             tbox: Optional[TBox] = None) -> bool:
    """Return True iff ``(tbox, abox)`` entails ``individual : concept`` — the
    same "does asserting the complement make it inconsistent" reduction
    :func:`unicode_fol_kit.dl.tableau.instance_check` uses. Open-world, exactly
    like that function: False means NOT entailed, not "entailed false".
    """
    return not external_abox_consistent(_abox_with(abox, individual, Not(concept)), tbox)


def _all_individuals(abox: ABox) -> Set[str]:
    """Every individual name mentioned in ``abox`` (ANY assertion list) — the
    SAME scan the tableau's sweeps and ``kb_to_fol(...).individuals`` read
    (:func:`~unicode_fol_kit.dl.tableau._abox_individual_names`, driven by the
    axiom-kind table), and NO anonymous fallback individual: an ABox that names
    nobody has no one to retrieve or realize. (This used to fall back to an
    invented ``"a"`` and report it as a member — ``TBox().add(Top(), A)`` over
    an empty ABox "retrieved" ``{"a"}`` — and its own hand-written scan missed
    the data assertions.)
    """
    return set(_abox_individual_names(abox))


def external_instance_retrieval(abox: ABox, concept: Concept,
                                 tbox: Optional[TBox] = None) -> Set[str]:
    """Return every individual of ``abox`` that ``(tbox, abox)`` entails is a
    ``concept`` — sweeps :func:`external_instance_check` exactly like
    :func:`unicode_fol_kit.dl.tableau.instance_retrieval` does.

    The shared refusals run FIRST (:func:`_guard_inputs`): an ABox that names
    nobody makes the sweep below call :func:`external_instance_check` zero
    times, and a knowledge base the other entry points refuse got ``set()``.
    """
    _guard_inputs(tbox, abox, [concept])
    return {ind for ind in sorted(_all_individuals(abox))
            if external_instance_check(abox, ind, concept, tbox)}


def external_realize(abox: ABox, individual: str, vocabulary: List[Concept],
                      tbox: Optional[TBox] = None) -> List[Concept]:
    """Return ``individual``'s most-specific concepts from ``vocabulary`` — the
    same filter-then-drop-non-minimal reduction
    :func:`unicode_fol_kit.dl.tableau.realize` uses. The shared refusals run
    first (:func:`_guard_inputs`), since an empty ``vocabulary`` reaches no
    HermiT call.
    """
    _guard_inputs(tbox, abox, vocabulary)
    candidates = [c for c in vocabulary if external_instance_check(abox, individual, c, tbox)]
    return [c for c in candidates
            if not any(external_subsumes(d, c, tbox) and not external_subsumes(c, d, tbox)
                       for d in candidates)]


def external_realize_all(abox: ABox, vocabulary: List[Concept],
                          tbox: Optional[TBox] = None) -> Dict[str, List[Concept]]:
    """Return :func:`external_realize` for every individual named in ``abox``
    (``{}`` for an ABox that names none; the shared refusals run first, see
    :func:`_guard_inputs`)."""
    _guard_inputs(tbox, abox, vocabulary)
    return {ind: external_realize(abox, ind, vocabulary, tbox)
            for ind in sorted(_all_individuals(abox))}
