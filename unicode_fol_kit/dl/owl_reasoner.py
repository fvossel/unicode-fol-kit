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
    InverseRole, Nominal,
)
from .tableau import TBox, ABox

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

    __slots__ = ("ow", "world", "onto", "transitive_roles",
                 "_classes", "_roles", "_individuals", "_domain", "_counter")

    def __init__(self, ow, world, onto, transitive_roles: Set[str]):
        self.ow = ow
        self.world = world
        self.onto = onto
        self.transitive_roles = transitive_roles
        self._classes: Dict[str, object] = {}
        self._roles: Dict[str, object] = {}
        self._individuals: Dict[str, object] = {}
        self._domain = None
        self._counter = 0

    def _fresh_name(self, prefix: str) -> str:
        self._counter += 1
        return f"{prefix}{self._counter}"

    def cls(self, name: str):
        """The owlready2 named class for this kit's ``Atomic`` name ``name``."""
        if name not in self._classes:
            self._classes[name] = self.ow.types.new_class(self._fresh_name("C"), (self.ow.Thing,))
        return self._classes[name]

    def role_obj(self, name: str):
        """The owlready2 object property for this kit's role name ``name``,
        declared transitive at CREATION time iff ``name in self.transitive_roles``
        (owlready2 needs ``TransitiveProperty`` among the class's bases up
        front, not added after the fact).
        """
        if name not in self._roles:
            bases = ((self.ow.ObjectProperty, self.ow.TransitiveProperty)
                      if name in self.transitive_roles else (self.ow.ObjectProperty,))
            self._roles[name] = self.ow.types.new_class(self._fresh_name("R"), bases)
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
    """
    if isinstance(concept, Top):
        return ctx.ow.Thing
    if isinstance(concept, Bottom):
        return ctx.ow.Nothing
    if isinstance(concept, Atomic):
        return ctx.cls(concept.name)
    if isinstance(concept, Nominal):
        return ctx.ow.OneOf([ctx.ind(concept.individual)])
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
        ctx.cls(sub.name).is_a.append(_translate_concept(sup, ctx))
        return
    gca = ctx.ow.GeneralClassAxiom(_translate_concept(sub, ctx))
    gca.is_a.append(_translate_concept(sup, ctx))


def _build_kb(ctx: _Ctx, tbox: TBox, abox: ABox) -> None:
    """Populate ``ctx``'s ontology with ``tbox``'s RBox + GCIs and ``abox``'s
    assertions. Must run inside a ``with ctx.onto:`` block (every
    ``ctx.ow.types.new_class``/``GeneralClassAxiom`` call needs the current
    namespace set — see ``owlready2``'s own convention).
    """
    for sub_role, super_role in tbox.role_inclusions:
        ctx.role_obj(sub_role).is_a.append(ctx.role_obj(super_role))
    for sub, sup in tbox.inclusions:
        _add_gci(sub, sup, ctx)
    for individual, concept in abox.concept_assertions:
        ctx.ind(individual).is_a.append(_translate_concept(concept, ctx))
    for a, b, role in abox.role_assertions:
        role_obj = ctx.role_obj(role)
        getattr(ctx.ind(a), role_obj.name).append(ctx.ind(b))
    for a, b in abox.distinct_assertions:
        ctx.ow.AllDifferent([ctx.ind(a), ctx.ind(b)])


def _kb_consistent(tbox: Optional[TBox], abox: ABox) -> bool:
    """Build a fresh ``owlready2`` ``World``/``Ontology`` encoding ``(tbox,
    abox)``, run HermiT via ``sync_reasoner_hermit``, and return True iff the
    knowledge base is consistent. The ONE HermiT-invoking primitive every
    other function in this module reduces to (see the module docstring's
    "What each function decides" section).

    Raises:
        OwlReasonerError: owlready2 is missing, or HermiT/the JVM failed for
            a reason other than genuine inconsistency.
    """
    ow = _require_available()
    tbox = tbox if tbox is not None else TBox()
    world = ow.World()
    onto = world.get_ontology("http://unicode-fol-kit.invalid/kb#")
    ctx = _Ctx(ow, world, onto, tbox.transitive_roles)
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

def external_concept_satisfiable(concept: Concept, tbox: Optional[TBox] = None) -> bool:
    """Return True iff ``concept`` is satisfiable with respect to ``tbox`` —
    the external-reasoner twin of :func:`unicode_fol_kit.dl.tableau.concept_satisfiable`,
    but over the FULL ALCHQ + I + O fragment (inverse roles, nominals). Reduced
    to :func:`_kb_consistent` via a single fresh probe individual, exactly the
    way the in-house tableau reduces it to one fresh branch node.
    """
    probe_abox = ABox().assert_concept("_probe", concept)
    return _kb_consistent(tbox, probe_abox)


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
    """
    return ABox(
        concept_assertions=abox.concept_assertions + [(individual, concept)],
        role_assertions=list(abox.role_assertions),
        distinct_assertions=list(abox.distinct_assertions),
    )


def external_instance_check(abox: ABox, individual: str, concept: Concept,
                             tbox: Optional[TBox] = None) -> bool:
    """Return True iff ``(tbox, abox)`` entails ``individual : concept`` — the
    same "does asserting the complement make it inconsistent" reduction
    :func:`unicode_fol_kit.dl.tableau.instance_check` uses. Open-world, exactly
    like that function: False means NOT entailed, not "entailed false".
    """
    return not external_abox_consistent(_abox_with(abox, individual, Not(concept)), tbox)


def _all_individuals(abox: ABox) -> Set[str]:
    """Every individual name mentioned in ``abox`` (either assertion list),
    falling back to a single anonymous ``"a"`` for a wholly empty ABox — the
    same convention :func:`unicode_fol_kit.dl.tableau._individuals` uses,
    reimplemented locally (rather than imported) to keep this module decoupled
    from that one's private internals.
    """
    individuals = {a for a, _ in abox.concept_assertions}
    for a, b, _ in abox.role_assertions:
        individuals.add(a)
        individuals.add(b)
    for a, b in abox.distinct_assertions:
        individuals.add(a)
        individuals.add(b)
    if not individuals:
        individuals = {"a"}
    return individuals


def external_instance_retrieval(abox: ABox, concept: Concept,
                                 tbox: Optional[TBox] = None) -> Set[str]:
    """Return every individual of ``abox`` that ``(tbox, abox)`` entails is a
    ``concept`` — sweeps :func:`external_instance_check` exactly like
    :func:`unicode_fol_kit.dl.tableau.instance_retrieval` does.
    """
    return {ind for ind in _all_individuals(abox)
            if external_instance_check(abox, ind, concept, tbox)}


def external_realize(abox: ABox, individual: str, vocabulary: List[Concept],
                      tbox: Optional[TBox] = None) -> List[Concept]:
    """Return ``individual``'s most-specific concepts from ``vocabulary`` — the
    same filter-then-drop-non-minimal reduction
    :func:`unicode_fol_kit.dl.tableau.realize` uses.
    """
    candidates = [c for c in vocabulary if external_instance_check(abox, individual, c, tbox)]
    return [c for c in candidates
            if not any(external_subsumes(d, c, tbox) and not external_subsumes(c, d, tbox)
                       for d in candidates)]


def external_realize_all(abox: ABox, vocabulary: List[Concept],
                          tbox: Optional[TBox] = None) -> Dict[str, List[Concept]]:
    """Return :func:`external_realize` for every individual named in ``abox``."""
    return {ind: external_realize(abox, ind, vocabulary, tbox)
            for ind in sorted(_all_individuals(abox))}
