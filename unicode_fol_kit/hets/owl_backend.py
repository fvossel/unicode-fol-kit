"""A second, independent external OWL 2 DL reasoner route — over Hets/Docker,
for the ALCHQ + I + O fragment (inverse roles, nominals) — via the ``Fact``
prover the ``spechub2/hets:latest`` image bundles.

This is C43 ("OWL2-DL reasoner fallback via Hets") as actually built, after a
live Phase-0 capability spike (see "Phase 0 spike findings" below) and after
re-checking the roadmap item's own claims against the code that shipped
since it was written (see "Deviations from the roadmap spec" below). The
short version: :mod:`unicode_fol_kit.dl.owl_reasoner` (added by C43's own
sibling item, N5) already gives this kit a full ALCHQ+I+O reasoner
(HermiT via ``owlready2``) and a full-ontology OWL 2 Functional-Style Syntax
writer (:mod:`unicode_fol_kit.dl.owl_functional`, ALCHQ only) — so the ONLY
thing left for a Hets route to add is a SECOND, INDEPENDENT oracle: a
different reasoner (FaCT++, not HermiT), reached a different way (a Docker
container's REST API, not an in-process JVM binding), so an agreement
between the two is not just one implementation checking itself twice.

Phase 0 spike findings (live, 2026-09-18, against the exact digest
``hets/docker.py`` already pins — see that module's own "Container image
quirks" section, which this module's findings were folded back into)
------------------------------------------------------------------------

1. The image DOES parse OWL 2: uploading a ``.omn`` (Manchester) or ``.ofn``
   (Functional-Style) file makes ``GET /dg/<iri>?format=json`` report
   ``"logic": "OWL"`` for the resulting development-graph node, alongside
   CASL nodes.
2. ``GET /provers/<iri>?format=json`` for an OWL-typed file lists
   ``Fact, eprover, darwin, darwin-non-fd, Vampire, MathServeBroker, SPASS,
   EProver, Darwin`` — **no** ``Pellet``, **no** ``HermiT``. Only ``Fact``
   (FaCT++, confirmed live inside the image: ``/usr/lib/hets/hets-owl-tools/
   lib/uk.ac.manchester.cs.owl.factplusplus-P5.0-v1.6.3.1.jar`` plus its
   native ``libFaCTPlusPlusJNI.so``, invoked as its own ``java`` subprocess by
   the Hets server, not by this Python process) is a genuine DL reasoner; the
   rest are the FOL provers :mod:`unicode_fol_kit.hets.docker`'s docstring
   already catalogues (some broken there too), reachable for OWL input only
   through a translation chain (``OWL22CASL:...``) that this module does NOT
   use — see point 3.
3. **Leaving ``reasoner`` unset (Hets's own default) is broken for OWL
   input**: ``POST /consistency-check`` with no explicit reasoner picks an
   ``OWL22CASL:CASL2SoftFOL``-family translation and then crashes outright —
   live-observed: ``*** Error: SuleCFOL2SoftFOL.transPREDSYMB: unknown pred:
   Qual_pred_name owl_uNothing ...`` — on an ontology as simple as one class
   asserted a subclass of ``owl:Nothing``. This module therefore ALWAYS
   passes ``reasoner="Fact"`` explicitly (see :data:`_REASONER`) and never
   lets Hets choose, unlike :mod:`unicode_fol_kit.atp.hets_backend`'s FOL
   route (where an unset reasoner is fine and used).
4. With ``reasoner="Fact"`` explicit, both directions verified live and
   correctly: an ontology whose ABox is genuinely inconsistent (an
   individual in two disjoint classes) answers ``"Inconsistent"`` with FaCT++
   provenance in ``prover_output``; a merely-unsatisfiable-but-unused named
   class (``C ⊑ owl:Nothing`` with no individual ever asserted into ``C``)
   correctly still answers ``"Consistent"`` (an empty class does not make the
   KB inconsistent) — i.e. this is not a reasoner that rubber-stamps
   "Consistent" the way the broken FOL provers rubber-stamp ``"Open"``
   (see :mod:`unicode_fol_kit.hets.docker`'s docstring for that precedent).
   A third result, ``"Timeout"``, is also live-confirmed (forced with
   ``timeLimit: 0``) — treated exactly like an unrecognised result: this
   module raises rather than guessing (see :class:`HetsOwlError`).
5. **No AGPL callout is needed.** The roadmap spec's Phase-0 instruction was
   conditional: add one "if a Pellet-backed route is what's actually live".
   It is not — the only live DL reasoner is FaCT++, whose kernel is
   **LGPL-2.1** (confirmed: FaCT++'s own project page,
   http://owl.cs.manchester.ac.uk/tools/fact/, and the FSF Free Software
   Directory both state LGPL for the reasoner kernel), and this kit reaches
   it over the same REST/Docker network boundary
   :mod:`unicode_fol_kit.hets` already draws for the whole subpackage (see
   its module docstring's "Architecture" section) — no different in kind
   from the SPASS/darwin route :mod:`unicode_fol_kit.atp.hets_backend`
   already ships uncommented-on. This is a genuine, recorded deviation from
   the roadmap spec's ``description``/``dependencies`` fields, which framed
   the AGPL callout as likely needed; it turned out not to apply.
6. A differential battery against BOTH existing routes — :mod:`unicode_fol_kit.dl.tableau`
   on ALCHQ (satisfiability, subsumption, the RBox, qualified number
   restrictions) and :mod:`unicode_fol_kit.dl.owl_reasoner` on the I/O
   fragment it alone decides — passed 21/21 live during this spike, reusing
   the SAME hand-checked fixtures ``tests/test_owl_reasoner.py`` already
   uses (see ``tests/test_hets_owl.py``, this module's test file, for the
   shipped, pytest-integrated version of that spike).

Deviations from the roadmap spec
----------------------------------
* **No ``dl/owl_export.py``.** The spec's Phase 1 asked for one; it does not
  exist because N5 already shipped the equivalent capability twice over —
  :func:`unicode_fol_kit.dl.owl_functional.to_owl_functional` (ALCHQ
  TBox+ABox -> OWL 2 Functional-Style Syntax text) and
  :mod:`unicode_fol_kit.dl.owl_reasoner` (the full ALCHQ+I+O reasoner
  itself). This module does not even reuse ``to_owl_functional`` for its own
  rendering, though — see "Why this module renders its own OWL text" below.
* **No ``DLHetsBackend`` class / ``atp.protocol.Verdict`` mapping.** The
  spec's Phase 2 sketch mirrored :class:`unicode_fol_kit.atp.hets_backend.HetsBackend`'s
  ``ProverBackend`` shape. This module instead mirrors
  :mod:`unicode_fol_kit.dl.owl_reasoner`'s shape (free functions returning
  plain ``bool``/``Set``/``List``/``Dict``, one per :mod:`unicode_fol_kit.dl.tableau`
  namesake, raising rather than returning an error-carrying envelope) — DL
  reasoning is not part of the ``atp`` FOL-prover registry (:mod:`unicode_fol_kit.dl`
  already draws that line: even ``owl_reasoner`` does not implement
  ``ProverBackend``), and the differential-testing story this task's own
  ``test_oracle`` asks for ("agree exactly with dl.tableau ... and with
  dl.owl_reasoner") is far more direct when all three routes share one
  calling convention.
* **No general ALCHQ FOL fallback via Hets.** The roadmap's own
  ``existing_coverage`` field already notes this exists in a different
  shape: :func:`unicode_fol_kit.dl.translate.concept_to_fol` feeds ALCHQ
  into the WHOLE ``atp`` backend stable, including
  :class:`unicode_fol_kit.atp.hets_backend.HetsBackend` itself (SPASS via
  CASL). This module adds nothing there; its only reason to exist is the
  I/O fragment neither the in-house tableau nor that FOL route can decide,
  PLUS a second, differently-implemented DL reasoner for the ALCHQ fragment
  as a cross-check.

Why this module renders its own OWL text (not ``dl.owl_functional``'s)
--------------------------------------------------------------------------
:mod:`unicode_fol_kit.dl.owl_functional` is deliberately ALCHQ-only — its
``to_owl_functional``/``to_owl_functional_class_expression`` RAISE
``TypeError`` on an :class:`~unicode_fol_kit.dl.concepts.InverseRole`-valued
role or a :class:`~unicode_fol_kit.dl.concepts.Nominal` (see that module's
own docstring), because ALCHQ-only round-tripping is its whole contract.
This module needs the FULL ALCHQ+I+O fragment in TEXT form (Hets's REST API
only takes uploaded file text, unlike ``owlready2``'s Python object API,
which is why :mod:`unicode_fol_kit.dl.owl_reasoner` could sidestep this
exact problem by never going through text at all — see that module's own
"Translation route" section). So :func:`_render_document` is a second,
small, ALCHQ+I+O-complete OWL 2 Functional-Style Syntax renderer, written
fresh rather than extending ``owl_functional.py`` (out of this task's file
ownership, and extending its ALCHQ-only contract would be the wrong change
for a module whose entire point is "round-trips exactly ALCHQ, nothing
more"). It reuses that module's naming-and-precedence-free INSIGHT
(``Keyword(arg arg ...)`` needs no precedence table — see
``owl_functional.py``'s "No ambiguity, no precedence" section) but not its
code, and it takes a different, simpler approach to names than either
sibling module:

Names: fresh synthetic local names, never round-tripped, exactly like
``dl.owl_reasoner``'s ``_Ctx``
-----------------------------------------------------------------------
OWL 2 Functional-Style Syntax has no "bare word" name token — every name is
either a full ``<IRI>`` or a *prefixed* name (``PNAME_LN``, e.g. ``:Doctor``
or ``ex:Doctor``); a bare ``Doctor`` with no prefix and no angle brackets is
a PARSE ERROR (live-confirmed: the OWL API's functional-syntax parser
reports ``Encountered " <PN_LOCAL> "Doctor "" ... Was expecting ... <PNAME_LN>``).
This kit's own :class:`~unicode_fol_kit.dl.concepts.Atomic`/role/individual
names are arbitrary opaque strings (may contain the kit's own Unicode DL
glyphs, whitespace, parentheses, ...) with no such restriction, and — just
as in ``dl.owl_reasoner``'s identical situation — every question this
module answers is a yes/no (or a `Set`/`List` of the CALLER's OWN concept
objects, for realize/retrieval — never "what is this entity called back"),
so there is nothing to lose by never sending the original name through
Hets's OWL/IRI machinery at all. :class:`_NameMap` allocates one fresh
``:C<n>``/``:R<n>``/``:I<n>`` PNAME_LN token per distinct kit name on first
use (a bare ``:`` DEFAULT-prefixed local name — declared once, via
``Prefix(:=<...>)``, per uploaded document — is a valid PNAME_LN and needs
no per-name IRI-safety reasoning at all, unlike ``owl_functional.py``'s
``to_owl_functional``, which instead renders a kit name back VERBATIM,
bracketed as a full IRI when it contains ``"://"`` — that module's contract
is "faithful round-trip of THIS name", this module's is "a yes/no verdict
Hets can compute", and the synthetic-name approach is simpler because it
does not need to be).

Wire fact this module relies on: the development-graph node name Hets
assigns an uploaded OWL file is exactly the ``Ontology(<iri> ...)`` IRI
declared inside it (live-confirmed against every probe file used in this
spike) — so :func:`_render_document` always declares the SAME fixed
:data:`_ONTOLOGY_IRI`, and every :meth:`~unicode_fol_kit.hets.client.HetsClient.consistency_check`
call in this module passes that same constant as ``node``, with no per-call
``GET /dg`` round trip needed to discover it (contrast
:mod:`unicode_fol_kit.hets.bridge`, which DOES need that round trip, because
its CASL input's node name is caller-chosen, not a constant this module
controls).

The data layer
----------------
FaCT++ is an SROIQ(D) reasoner, so unlike ``dl.owl_reasoner`` (whose HermiT
bridge refuses the data layer by name) THIS oracle can be asked about it:
:func:`_render_document` writes the data box and the data assertions, with
OWL 2's own datatype and facet names verbatim (``xsd:integer`` means the same
to FaCT++ as to us) and the same fresh synthetic names for data properties
(``:P<n>``) and user-defined datatypes (``:T<n>``) it gives classes and roles --
a LITERAL's datatype included: ``"5"^^:T1``, never the kit's own datatype name,
which the document does not declare.
The ``xsd``/``rdfs``/``rdf`` prefixes are declared only for a knowledge base
that mentions a datatype, so every data-free document is unchanged. This is an
independent check on the kit's own two-sorted FOL image, not a replacement for
it; no test here starts the container.

The one primitive: :func:`_kb_consistent`
--------------------------------------------
Every public ``external_*`` function reduces to it, exactly the way
``dl.owl_reasoner``'s whole public API reduces to its own ``_kb_consistent``,
and ``dl.tableau``'s to ``_solve`` — see "What each function decides" in
``dl.owl_reasoner``'s module docstring, which this module's reduction chain
mirrors call-for-call (``external_subsumes`` reduces to
``external_concept_satisfiable`` exactly the way ``subsumes`` reduces to
``concept_satisfiable``, and so on).

Opt-in, never in a default chain
-----------------------------------
Exactly :mod:`unicode_fol_kit.atp.hets_backend`'s cost-model discipline: a
Docker container start is minutes-expensive, so this module NEVER starts one
(:func:`hets_owl_available` and every ``external_*`` function only ever call
``discover_hets_url(start_container=False)``) and is never wired into any
automatic reasoning chain — a caller opts in by importing this module and
calling it directly, the same way ``dl.owl_reasoner`` is opt-in.

Public API: :func:`hets_owl_available`, :func:`external_concept_satisfiable`,
:func:`external_concept_unsatisfiable`, :func:`external_subsumes`,
:func:`external_equivalent`, :func:`external_abox_consistent`,
:func:`external_instance_check`, :func:`external_instance_retrieval`,
:func:`external_realize`, :func:`external_realize_all`, :class:`HetsOwlError`.
"""

from typing import Dict, List, Optional, Set

from ..dl.concepts import (
    Concept, Top, Bottom, Atomic, Not, And, Or, Exists, ForAll, AtLeast, AtMost,
    InverseRole, Nominal, HasValue, DataExists, DataForAll, DataHasValue,
    DataAtLeast, DataAtMost,
)
from ..dl.datatypes import (
    DataRange, Literal, is_builtin_datatype, render_datarange_fs, render_literal_fs,
)
from ..dl.tableau import (
    TBox, ABox, _abox_individual_names, _reject_abox_roles,
    _reject_concept_roles_deep, _tbox_class_expressions, _validate_data_box,
    _validate_role_box,
)
from ..dl.translate import _check_name_punning, _collect_vocabulary
from .client import HetsClient
from .docker import discover_hets_url, hets_available

__all__ = [
    "hets_owl_available",
    "external_concept_satisfiable", "external_concept_unsatisfiable",
    "external_subsumes", "external_equivalent",
    "external_abox_consistent", "external_instance_check", "external_instance_retrieval",
    "external_realize", "external_realize_all",
    "HetsOwlError",
]

#: The only prover identifier this module ever passes — see the module
#: docstring's "Phase 0 spike findings" point 3 for why an unset reasoner
#: (Hets's own default choice) is broken for OWL input, and point 2 for why
#: no other listed identifier is a genuine DL reasoner in this image.
_REASONER = "Fact"

#: Fixed ontology IRI every uploaded probe document declares — also the
#: development-graph node name passed to ``consistency_check`` (see the
#: module docstring's "Wire fact this module relies on").
_ONTOLOGY_IRI = "http://unicode-fol-kit.invalid/hets-owl-probe"

#: The default-prefix IRI backing every synthetic ``:C<n>``/``:R<n>``/``:I<n>``
#: PNAME_LN token (see the module docstring's "Names" section). Never
#: resolved or dereferenced — it exists only to make the ``Prefix(:=<...>)``
#: declaration well-formed.
_PREFIX_IRI = "http://unicode-fol-kit.invalid/owl#"

_FILENAME = "kit_owl_probe.ofn"


class HetsOwlError(RuntimeError):
    """A reachable Hets server could not decide a knowledge base: FaCT++
    reported ``"Timeout"`` (see the module docstring's point 4), an
    unrecognised result string, or a goal count other than one (this module
    always builds a single-goal ``consistency-check`` request, so anything
    else means the server answered a different question than asked — the
    same "infra" discipline :meth:`unicode_fol_kit.atp.hets_backend.HetsBackend.decide`
    already applies to its own single-conjecture case). Deliberately a plain
    ``RuntimeError`` (not :class:`~unicode_fol_kit.atp.protocol.BackendUnavailable`,
    which every ``external_*`` function here still raises UNCHANGED, via
    :func:`~unicode_fol_kit.hets.docker.discover_hets_url`, when no server is
    reachable at all): the server answering *something* unusable is a
    different failure mode than there being no server to ask, and callers
    that already special-case ``BackendUnavailable`` for "no Hets right now"
    must not have that same handling silently swallow "Hets is up but this
    query broke it".
    """


def hets_owl_available() -> bool:
    """True iff a Hets server answers right now — the DL/OWL route's twin of
    :func:`unicode_fol_kit.hets.docker.hets_available`.

    Literally delegates to it (same discovery, same never-start-a-container
    discipline): the "Fact" reasoner this module always requests is a fixed
    property of the digest-pinned image every part of :mod:`unicode_fol_kit.hets`
    already assumes (see :data:`unicode_fol_kit.hets.docker.HETS_IMAGE`), not
    something that needs its own per-call ``GET /provers`` re-verification —
    mirrors how :mod:`unicode_fol_kit.hets.docker`'s own docstring documents
    which FOL provers work in this image as a static fact, not a live probe.
    """
    return hets_available()


# --------------------------------------------------------------------------- #
# Rendering: Concept/TBox/ABox -> OWL 2 Functional-Style Syntax text, over the
# FULL ALCHQ + I + O fragment (see the module docstring's "Why this module
# renders its own OWL text" and "Names" sections).
# --------------------------------------------------------------------------- #

class _NameMap:
    """Per-call allocator of fresh, synthetic PNAME_LN tokens (``:C1``, ``:R1``,
    ``:I1``, ...) for this kit's class/role/individual names — never the kit's
    own name string verbatim (see the module docstring's "Names" section).
    """

    def __init__(self):
        self._classes: Dict[str, str] = {}
        self._roles: Dict[str, str] = {}
        self._individuals: Dict[str, str] = {}
        self._data_properties: Dict[str, str] = {}
        self._datatypes: Dict[str, str] = {}

    def cls(self, name: str) -> str:
        if name not in self._classes:
            self._classes[name] = f":C{len(self._classes) + 1}"
        return self._classes[name]

    def role(self, name: str) -> str:
        if name not in self._roles:
            self._roles[name] = f":R{len(self._roles) + 1}"
        return self._roles[name]

    def ind(self, name: str) -> str:
        if name not in self._individuals:
            self._individuals[name] = f":I{len(self._individuals) + 1}"
        return self._individuals[name]

    def dprop(self, name: str) -> str:
        """A fresh ``:P<n>`` token for a DATA property name."""
        if name not in self._data_properties:
            self._data_properties[name] = f":P{len(self._data_properties) + 1}"
        return self._data_properties[name]

    def dtype(self, name: str) -> str:
        """A datatype name as OWL 2 text: a BUILT-IN datatype keeps its own
        name (``xsd:integer`` means the same to Hets as to us), a user-defined
        one gets a fresh ``:T<n>`` token."""
        if is_builtin_datatype(name):
            return name
        if name not in self._datatypes:
            self._datatypes[name] = f":T{len(self._datatypes) + 1}"
        return self._datatypes[name]

    def class_tokens(self) -> List[str]:
        return list(self._classes.values())

    def role_tokens(self) -> List[str]:
        return list(self._roles.values())

    def individual_tokens(self) -> List[str]:
        return list(self._individuals.values())

    def data_property_tokens(self) -> List[str]:
        return list(self._data_properties.values())

    def datatype_tokens(self) -> List[str]:
        return list(self._datatypes.values())


def _render_datarange(datarange: DataRange, names: _NameMap) -> str:
    """A data range as OWL 2 Functional-Style text, with user-defined datatypes
    under their synthetic names."""
    return render_datarange_fs(datarange, names.dtype)


def _render_literal(literal: Literal, names: _NameMap) -> str:
    """A literal as OWL 2 Functional-Style text, its datatype under the SAME
    name :func:`_render_datarange` gives it: a user-defined datatype is declared
    as ``:T<n>``, so a literal written with the kit's own name would use a name
    the document never declared."""
    return render_literal_fs(literal, names.dtype)


def _render_role_expr(role_field, names: _NameMap) -> str:
    """Render a ``role`` field (a plain role name, or an :class:`InverseRole`)
    as an OWL 2 ``ObjectPropertyExpression`` — the one place this renderer
    covers a construct ``dl.owl_functional`` refuses outright (see the
    module docstring).
    """
    if isinstance(role_field, InverseRole):
        return f"ObjectInverseOf({names.role(role_field.role)})"
    return names.role(role_field)


def _render_ce(c: Concept, names: _NameMap) -> str:
    """Render ``c`` as an OWL 2 Functional-Style ``ClassExpression``, over the
    full ALCHQ + I + O fragment (see :mod:`unicode_fol_kit.dl.concepts` for
    the AST this mirrors, and the module docstring for why this duplicates a
    small amount of ``dl.owl_functional._render_ce``-shaped logic rather than
    reusing it).
    """
    if isinstance(c, Top):
        return "owl:Thing"
    if isinstance(c, Bottom):
        return "owl:Nothing"
    if isinstance(c, Atomic):
        return names.cls(c.name)
    if isinstance(c, Nominal):
        return f"ObjectOneOf({names.ind(c.individual)})"
    if isinstance(c, HasValue):
        return (f"ObjectHasValue({_render_role_expr(c.role, names)} "
                f"{names.ind(c.individual)})")
    if isinstance(c, Not):
        return f"ObjectComplementOf({_render_ce(c.concept, names)})"
    if isinstance(c, And):
        return f"ObjectIntersectionOf({_render_ce(c.left, names)} {_render_ce(c.right, names)})"
    if isinstance(c, Or):
        return f"ObjectUnionOf({_render_ce(c.left, names)} {_render_ce(c.right, names)})"
    if isinstance(c, Exists):
        return f"ObjectSomeValuesFrom({_render_role_expr(c.role, names)} {_render_ce(c.concept, names)})"
    if isinstance(c, ForAll):
        return f"ObjectAllValuesFrom({_render_role_expr(c.role, names)} {_render_ce(c.concept, names)})"
    if isinstance(c, AtLeast):
        return f"ObjectMinCardinality({c.n} {_render_role_expr(c.role, names)} {_render_ce(c.concept, names)})"
    if isinstance(c, AtMost):
        return f"ObjectMaxCardinality({c.n} {_render_role_expr(c.role, names)} {_render_ce(c.concept, names)})"
    if isinstance(c, DataExists):
        return f"DataSomeValuesFrom({names.dprop(c.prop)} {_render_datarange(c.datarange, names)})"
    if isinstance(c, DataForAll):
        return f"DataAllValuesFrom({names.dprop(c.prop)} {_render_datarange(c.datarange, names)})"
    if isinstance(c, DataHasValue):
        return f"DataHasValue({names.dprop(c.prop)} {_render_literal(c.value, names)})"
    if isinstance(c, DataAtLeast):
        return (f"DataMinCardinality({c.n} {names.dprop(c.prop)} "
                f"{_render_datarange(c.datarange, names)})")
    if isinstance(c, DataAtMost):
        return (f"DataMaxCardinality({c.n} {names.dprop(c.prop)} "
                f"{_render_datarange(c.datarange, names)})")
    raise TypeError(f"hets.owl_backend: unsupported concept {type(c).__name__}")


#: ``(TBox field, OWL 2 keyword)`` for the seven one-role characteristic
#: axioms, in the order ``dl.tableau._AXIOM_KINDS`` lists them. A table rather
#: than seven loops, for the same reason ``dl.owl_functional`` uses one: they
#: differ only in the keyword, and a FaCT++ oracle that silently dropped one
#: would agree with the in-house tableau for the wrong reason.
#: ``transitive_roles`` is NOT here: a transitivity declaration is rendered
#: with the role inclusions, ahead of everything else, which is the ordering
#: this module has had since the RBox landed and which several pinned
#: expected-document strings depend on.
_CHARACTERISTIC_AXIOMS = (
    ("asymmetric_roles", "AsymmetricObjectProperty"),
    ("irreflexive_roles", "IrreflexiveObjectProperty"),
    ("functional_roles", "FunctionalObjectProperty"),
    ("symmetric_roles", "SymmetricObjectProperty"),
    ("reflexive_roles", "ReflexiveObjectProperty"),
    ("inverse_functional_roles", "InverseFunctionalObjectProperty"),
)


def _guard_document(tbox: TBox, abox: ABox, concepts=()) -> None:
    """Refuse, by name, what no route may answer, BEFORE a word of the document
    is written.

    A renderer gives every name it meets a synthetic one of its own (``:R1``), so
    an OWL 2 built-in property name (``owl:topObjectProperty`` and the other
    three, and ``=`` / ``≠``) as the role of a class expression came out as an
    ordinary role, and FaCT++ was asked about a different restriction — while
    every other route refuses the same concept by name. These are the validations
    :func:`unicode_fol_kit.dl.owl_reasoner._guard_inputs` runs for the HermiT
    route, CALLED here and not copied, so one expression is refused with one
    message wherever it is asked: the stored role box and data box are validated
    before anything is unpacked (a hand-built wrong-arity pair is a
    :class:`~unicode_fol_kit.dl.tableau.RoleExpressionError`, not a bare
    ``ValueError``), no ABox assertion carries a built-in property name, and no
    class expression — in a TBox inclusion, in a domain or range filler, in a
    DATA property domain filler (a class expression this route renders; the
    HermiT route refuses the whole data box instead), in an ABox concept
    assertion (which is where every QUERY concept ends up) — uses one as a role,
    at any depth. A NAME used as both an object property and a data property, or
    as both a class and a datatype, is refused too
    (:func:`~unicode_fol_kit.dl.translate._check_name_punning`, the one the FOL
    image runs): this renderer would write the two kinds under separate tokens
    (``:R1`` / ``:P1``), so the oracle would answer a knowledge base the kit's own
    route refuses. Not run here: the data-layer refusal (FaCT++ is an SROIQ(D)
    reasoner and IS asked about the data layer) and the simple-role check.

    ``concepts`` are query concepts that are NOT yet in the ABox: an entry point
    that may make no Hets call at all (``external_realize`` over an empty
    vocabulary, ``external_realize_all`` and ``external_instance_retrieval`` over
    an empty ABox) runs the guard itself, as ``dl.owl_reasoner`` does, so that it
    does not return a quiet ``[]`` for a knowledge base every other route refuses.
    """
    where = "hets.owl_backend"
    _validate_role_box(tbox, where=where)
    _validate_data_box(tbox, where=where)
    _reject_abox_roles(abox, where=where)
    for concept in _tbox_class_expressions(tbox):
        _reject_concept_roles_deep(concept, where=where)
    for _prop, filler in tbox.data_property_domains:
        _reject_concept_roles_deep(filler, where=where)
    for _individual, concept in abox.concept_assertions:
        _reject_concept_roles_deep(concept, where=where)
    for concept in concepts:
        _reject_concept_roles_deep(concept, where=where)
    # Over the whole knowledge base, which includes every query concept (they
    # reach this renderer as ABox assertions).
    _check_name_punning(_collect_vocabulary(tbox, abox), where)


def _render_document(tbox: TBox, abox: ABox) -> str:
    """Render ``(tbox, abox)`` as one OWL 2 Functional-Style ``Ontology(...)``
    document under the fixed :data:`_ONTOLOGY_IRI`, with a ``Declaration(...)``
    for every synthetic name used (mirrors ``dl.owl_functional.to_owl_functional``'s
    own declaration-block convention, for the same reason: cheap, harmless,
    and matches what a hand-written OWL ontology looks like) — the whole role
    box first, then the TBox's inclusions, then the ABox's assertions, matching
    that sibling module's own axiom ordering.

    EVERY role-box field is rendered, including the ones
    ``dl.owl_functional`` cannot read back (an ``ObjectInverseOf`` on either
    side of a sub-property axiom): this module exists to be a SECOND,
    INDEPENDENT oracle, and an oracle that drops the axiom under test agrees
    with everything. What no route answers is refused first
    (:func:`_guard_document`).
    """
    _guard_document(tbox, abox)
    names = _NameMap()
    axiom_lines: List[str] = []
    for sub_role, super_role in tbox.role_inclusions:
        # _render_role_expr, not names.role: an InverseRole must come out as
        # ObjectInverseOf(...), and using it as a _NameMap KEY (what this did
        # until 0.30.0) invents a brand-new atomic property instead -- so an
        # inverse-role inclusion and a chain rendered CHARACTER-FOR-CHARACTER
        # identically, and FaCT++ was asked about neither of them.
        axiom_lines.append(f"SubObjectPropertyOf({_render_role_expr(sub_role, names)} "
                           f"{_render_role_expr(super_role, names)})")
    for role in sorted(tbox.transitive_roles):
        axiom_lines.append(f"TransitiveObjectProperty({names.role(role)})")
    # The remaining role-box fields, in the order dl.tableau._AXIOM_KINDS lists
    # them -- the same order dl.owl_functional._render_role_box uses, so the
    # two renderers' documents line up axiom for axiom.
    for left, right in tbox.disjoint_role_pairs:
        axiom_lines.append(
            f"DisjointObjectProperties({names.role(left)} {names.role(right)})")
    for field_name, keyword in _CHARACTERISTIC_AXIOMS:
        for role in sorted(getattr(tbox, field_name)):
            axiom_lines.append(f"{keyword}({names.role(role)})")
    for p, q in tbox.inverse_role_pairs:
        axiom_lines.append(
            f"InverseObjectProperties({names.role(p)} {names.role(q)})")
    for chain, super_role in tbox.role_chains:
        body = " ".join(_render_role_expr(role, names) for role in chain)
        axiom_lines.append(f"SubObjectPropertyOf(ObjectPropertyChain({body}) "
                           f"{names.role(super_role)})")
    for role, filler in tbox.role_domains:
        axiom_lines.append(f"ObjectPropertyDomain({names.role(role)} "
                           f"{_render_ce(filler, names)})")
    for role, filler in tbox.role_ranges:
        axiom_lines.append(f"ObjectPropertyRange({names.role(role)} "
                           f"{_render_ce(filler, names)})")
    # The DATA box: FaCT++ is an SROIQ(D) reasoner, so unlike the HermiT route
    # this oracle CAN be asked about the data layer. Datatype and facet names
    # are OWL 2's own and stay verbatim; a user-defined datatype and every data
    # property get fresh synthetic names, like classes and roles.
    for sub_prop, super_prop in tbox.data_property_inclusions:
        axiom_lines.append(f"SubDataPropertyOf({names.dprop(sub_prop)} {names.dprop(super_prop)})")
    for left, right in tbox.disjoint_data_property_pairs:
        axiom_lines.append(f"DisjointDataProperties({names.dprop(left)} {names.dprop(right)})")
    for prop in sorted(tbox.functional_data_properties):
        axiom_lines.append(f"FunctionalDataProperty({names.dprop(prop)})")
    for prop, filler in tbox.data_property_domains:
        axiom_lines.append(f"DataPropertyDomain({names.dprop(prop)} {_render_ce(filler, names)})")
    for prop, datarange in tbox.data_property_ranges:
        axiom_lines.append(f"DataPropertyRange({names.dprop(prop)} "
                           f"{_render_datarange(datarange, names)})")
    for name, datarange in tbox.datatype_definitions:
        axiom_lines.append(f"DatatypeDefinition({names.dtype(name)} "
                           f"{_render_datarange(datarange, names)})")
    for sub, sup in tbox.inclusions:
        axiom_lines.append(f"SubClassOf({_render_ce(sub, names)} {_render_ce(sup, names)})")
    for individual, concept in abox.concept_assertions:
        axiom_lines.append(f"ClassAssertion({_render_ce(concept, names)} {names.ind(individual)})")
    for a, b, role in abox.role_assertions:
        axiom_lines.append(
            f"ObjectPropertyAssertion({names.role(role)} {names.ind(a)} {names.ind(b)})")
    for a, b in abox.distinct_assertions:
        axiom_lines.append(f"DifferentIndividuals({names.ind(a)} {names.ind(b)})")
    for a, b in abox.same_assertions:
        axiom_lines.append(f"SameIndividual({names.ind(a)} {names.ind(b)})")
    for a, b, role in abox.negative_role_assertions:
        axiom_lines.append(f"NegativeObjectPropertyAssertion({names.role(role)} "
                           f"{names.ind(a)} {names.ind(b)})")
    for individual, prop, value in abox.data_assertions:
        axiom_lines.append(f"DataPropertyAssertion({names.dprop(prop)} "
                           f"{names.ind(individual)} {_render_literal(value, names)})")
    for individual, prop, value in abox.negative_data_assertions:
        axiom_lines.append(f"NegativeDataPropertyAssertion({names.dprop(prop)} "
                           f"{names.ind(individual)} {_render_literal(value, names)})")

    decl_lines = (
        [f"Declaration(Class({t}))" for t in names.class_tokens()]
        + [f"Declaration(ObjectProperty({t}))" for t in names.role_tokens()]
        + [f"Declaration(DataProperty({t}))" for t in names.data_property_tokens()]
        + [f"Declaration(Datatype({t}))" for t in names.datatype_tokens()]
        + [f"Declaration(NamedIndividual({t}))" for t in names.individual_tokens()]
    )
    body_lines = decl_lines + axiom_lines
    header = (f"Prefix(:=<{_PREFIX_IRI}>)\n"
              f"Prefix(owl:=<http://www.w3.org/2002/07/owl#>)\n")
    if _collect_vocabulary(tbox, abox).has_data():
        # The datatypes' own prefixes, declared so the document does not lean on
        # the implicit ones -- only for a knowledge base that mentions a
        # datatype at all, which leaves every data-free document as it was.
        header += ("Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)\n"
                   "Prefix(rdfs:=<http://www.w3.org/2000/01/rdf-schema#>)\n"
                   "Prefix(rdf:=<http://www.w3.org/1999/02/22-rdf-syntax-ns#>)\n")
    header += f"Ontology(<{_ONTOLOGY_IRI}>"
    if not body_lines:
        return header + ")"
    body = "\n".join(f"  {line}" for line in body_lines)
    return f"{header}\n{body}\n)"


# --------------------------------------------------------------------------- #
# The one HETS-invoking primitive.
# --------------------------------------------------------------------------- #

def _kb_consistent(tbox: Optional[TBox], abox: ABox, *,
                    time_limit: int, url: Optional[str]) -> bool:
    """Render ``(tbox, abox)``, upload it, and ask ``POST /consistency-check``
    with ``reasoner="Fact"``. The ONE Hets-invoking primitive every other
    function in this module reduces to (see the module docstring's "The one
    primitive" section).

    Raises:
        BackendUnavailable: no Hets server is reachable (from
            :func:`~unicode_fol_kit.hets.docker.discover_hets_url`, when
            ``url`` is not given).
        RuntimeError: the upload or the consistency-check call itself failed
            (:class:`~unicode_fol_kit.hets.client.HetsClient`'s own contract
            — an HTTP error, an HETS ``"*** Error"`` body, malformed JSON).
        HetsOwlError: the server answered, but not with a genuine
            ``"Consistent"``/``"Inconsistent"`` verdict (a ``"Timeout"``, an
            unrecognised result string, or other than exactly one goal
            result) — see :class:`HetsOwlError`.
    """
    tbox = tbox if tbox is not None else TBox()
    # Rendered BEFORE a server is looked for: a question that is refused by name
    # (see _guard_document) must not need a reachable Hets to be refused.
    text = _render_document(tbox, abox)
    if url is None:
        url, _container = discover_hets_url(start_container=False)
    client = HetsClient(url, timeout=float(time_limit + 30))
    iri = client.upload(text, _FILENAME)
    goals = client.consistency_check(iri, _ONTOLOGY_IRI, reasoner=_REASONER,
                                      time_limit=time_limit)
    if len(goals) != 1:
        raise HetsOwlError(
            f"hets.owl_backend: expected exactly 1 goal result from "
            f"consistency-check, got {len(goals)}: {goals!r}")
    result = (goals[0].get("result") or "").strip()
    if result == "Consistent":
        return True
    if result == "Inconsistent":
        return False
    raise HetsOwlError(
        f"hets.owl_backend: consistency-check returned an unusable result "
        f"{result!r} (never guessed as Consistent/Inconsistent — see "
        f"HetsOwlError's docstring): {goals[0]!r}")


# --------------------------------------------------------------------------- #
# Public API — mirrors dl.tableau's / dl.owl_reasoner's exactly, over the
# ALCHQ + I + O fragment (see the module docstring's "The one primitive").
# --------------------------------------------------------------------------- #

def external_concept_satisfiable(concept: Concept, tbox: Optional[TBox] = None, *,
                                  time_limit: int = 15, url: Optional[str] = None) -> bool:
    """Return True iff ``concept`` is satisfiable with respect to ``tbox`` —
    this module's twin of :func:`unicode_fol_kit.dl.tableau.concept_satisfiable`
    / :func:`unicode_fol_kit.dl.owl_reasoner.external_concept_satisfiable`,
    over the full ALCHQ + I + O fragment. Reduced to :func:`_kb_consistent`
    via a single fresh probe individual, exactly the way
    ``dl.owl_reasoner``'s own function does.
    """
    probe_abox = ABox().assert_concept("_probe", concept)
    return _kb_consistent(tbox, probe_abox, time_limit=time_limit, url=url)


def external_concept_unsatisfiable(concept: Concept, tbox: Optional[TBox] = None, *,
                                    time_limit: int = 15, url: Optional[str] = None) -> bool:
    """Return True iff ``concept`` is unsatisfiable with respect to ``tbox``."""
    return not external_concept_satisfiable(concept, tbox, time_limit=time_limit, url=url)


def external_subsumes(sub: Concept, sup: Concept, tbox: Optional[TBox] = None, *,
                       time_limit: int = 15, url: Optional[str] = None) -> bool:
    """Return True iff ``tbox`` entails ``sub ⊑ sup`` — the same ``sub ⊓ ¬sup``
    unsatisfiability reduction :func:`unicode_fol_kit.dl.tableau.subsumes` uses.
    """
    return not external_concept_satisfiable(And(sub, Not(sup)), tbox,
                                             time_limit=time_limit, url=url)


def external_equivalent(c: Concept, d: Concept, tbox: Optional[TBox] = None, *,
                         time_limit: int = 15, url: Optional[str] = None) -> bool:
    """Return True iff ``tbox`` entails ``c ≡ d`` (mutual subsumption)."""
    return (external_subsumes(c, d, tbox, time_limit=time_limit, url=url)
            and external_subsumes(d, c, tbox, time_limit=time_limit, url=url))


def external_abox_consistent(abox: ABox, tbox: Optional[TBox] = None, *,
                              time_limit: int = 15, url: Optional[str] = None) -> bool:
    """Return True iff the knowledge base ``(tbox, abox)`` is consistent."""
    return _kb_consistent(tbox, abox, time_limit=time_limit, url=url)


def _abox_with(abox: ABox, individual: str, concept: Concept) -> ABox:
    """A copy of ``abox`` with one extra concept assertion ``individual : concept``
    (used by :func:`external_instance_check`'s entailment reduction — mirrors
    :func:`unicode_fol_kit.dl.owl_reasoner._abox_with` exactly).

    :meth:`~unicode_fol_kit.dl.tableau.ABox.copy`, not a field-by-field
    reconstruction: this module is one of the kit's INDEPENDENT oracles, and a
    probe that silently drops an assertion kind the caller supplied asks FaCT++
    about a strictly WEAKER knowledge base than the one the caller has, so the
    two oracles would agree for the wrong reason. (Field-by-field is what this
    did until 0.30.0, and it dropped ``same_assertions`` and
    ``negative_role_assertions`` — and would have dropped the data assertions —
    the moment they existed.)
    """
    probe = abox.copy()
    probe.assert_concept(individual, concept)
    return probe


def external_instance_check(abox: ABox, individual: str, concept: Concept,
                             tbox: Optional[TBox] = None, *,
                             time_limit: int = 15, url: Optional[str] = None) -> bool:
    """Return True iff ``(tbox, abox)`` entails ``individual : concept`` — the
    same "does asserting the complement make it inconsistent" reduction
    :func:`unicode_fol_kit.dl.tableau.instance_check` uses. Open-world,
    exactly like that function: False means NOT entailed, not "entailed false".
    """
    return not external_abox_consistent(
        _abox_with(abox, individual, Not(concept)), tbox, time_limit=time_limit, url=url)


def _all_individuals(abox: ABox) -> Set[str]:
    """Every individual name mentioned in ``abox`` (ANY assertion list), and NO
    anonymous fallback: an ABox that names nobody has nobody to retrieve or
    realize.

    It IS :func:`unicode_fol_kit.dl.tableau._abox_individual_names`, the scan the
    tableau's two sweeps (``instance_retrieval``, ``realize_all``), the HermiT
    route and ``kb_to_fol(...).individuals`` all read, driven by ``dl.tableau.
    _AXIOM_KINDS``' ``individual_positions``: an assertion kind added to the
    table is enumerated by every route that sweeps individuals from its row
    alone. NOT ``dl.tableau._individuals``, which adds the anonymous ``"a"`` for
    an empty ABox because ``abox_consistent`` needs SOME node for the TBox to
    run on — that node is not an individual of the knowledge base, and sweeping
    it asked FaCT++ about a phantom and reported it as a member
    (``TBox().add(⊤, A)`` over an empty ABox retrieved ``{"a"}`` here and
    ``set()`` from the tableau and from HermiT). A local re-implementation of
    the scan is what this was until 0.30.0, and it omitted ``same_assertions``
    and ``negative_role_assertions``.
    """
    return set(_abox_individual_names(abox))


def external_instance_retrieval(abox: ABox, concept: Concept, tbox: Optional[TBox] = None, *,
                                 time_limit: int = 15, url: Optional[str] = None) -> Set[str]:
    """Return every individual of ``abox`` that ``(tbox, abox)`` entails is a
    ``concept`` — sweeps :func:`external_instance_check` exactly like
    :func:`unicode_fol_kit.dl.tableau.instance_retrieval` does.
    """
    _guard_document(tbox if tbox is not None else TBox(), abox, [concept])
    return {ind for ind in _all_individuals(abox)
            if external_instance_check(abox, ind, concept, tbox, time_limit=time_limit, url=url)}


def external_realize(abox: ABox, individual: str, vocabulary: List[Concept],
                      tbox: Optional[TBox] = None, *,
                      time_limit: int = 15, url: Optional[str] = None) -> List[Concept]:
    """Return ``individual``'s most-specific concepts from ``vocabulary`` — the
    same filter-then-drop-non-minimal reduction
    :func:`unicode_fol_kit.dl.tableau.realize` uses.
    """
    _guard_document(tbox if tbox is not None else TBox(), abox, vocabulary)
    candidates = [c for c in vocabulary
                  if external_instance_check(abox, individual, c, tbox,
                                              time_limit=time_limit, url=url)]
    return [c for c in candidates
            if not any(external_subsumes(d, c, tbox, time_limit=time_limit, url=url)
                       and not external_subsumes(c, d, tbox, time_limit=time_limit, url=url)
                       for d in candidates)]


def external_realize_all(abox: ABox, vocabulary: List[Concept], tbox: Optional[TBox] = None, *,
                          time_limit: int = 15, url: Optional[str] = None) -> Dict[str, List[Concept]]:
    """Return :func:`external_realize` for every individual named in ``abox``."""
    _guard_document(tbox if tbox is not None else TBox(), abox, vocabulary)
    return {ind: external_realize(abox, ind, vocabulary, tbox, time_limit=time_limit, url=url)
            for ind in sorted(_all_individuals(abox))}
