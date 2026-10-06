r"""Joining HETS' TPTP symbols back onto the OWL entities they came from.

What this module is for
-----------------------
HETS' ``OWL22CASL:CASL2TPTP_FOF`` route renders an OWL entity as a mangled
TPTP symbol::

    pred_https_u_u_uopenenergyplatform_uorg_uontology_uoeo_uOEO_00000072

and :func:`unicode_fol_kit.fol.tptp_input.parse_tptp` reads that back as the
kit predicate ``Pred_https_u_u_u...``. Neither form says which class that is,
so a disagreement between the HETS route and this kit's own
:mod:`unicode_fol_kit.dl` route cannot be reported in terms anyone can check.
This module builds the join: one row per declared entity, carrying HETS'
printed name, the full IRI, the TPTP symbol, the kit symbol, whether the
symbol occurs in the TPTP at all, and the entity's ``rdfs:label``\ s.

Everything here is a PURE function over a ``/dg`` dict and a TPTP string —
no network, no Docker, no subprocess. That is deliberate: it is what lets
every number below be asserted on a machine with no HETS at all. The
Docker/command-line half lives in :mod:`~unicode_fol_kit.hets.owl_cli`.

The mangling is a computation, not a guess
------------------------------------------
``/dg``'s ``Declarations[i]`` carries ``{kind, name, iri, Symbol}``, where
``iri`` is HETS' PRINTED form — a CURIE when the ontology declared a prefix
(``obo:BFO_0000001``) and the full IRI otherwise. That printed form is
exactly the mangling INPUT:

* replace every character outside ``[A-Za-z0-9_]`` with ``_u``;
* prefix ``op_`` for an ``Individual``, ``sort_`` for a ``Datatype``,
  ``pred_`` for everything else.

Measured on the real OEO pair (2099 declarations, 1667 printed as full IRIs
and 432 as CURIEs over 10 prefixes): this reproduces 2026 names that actually
occur in the TPTP text, with 0 collisions. So no prefix-map reconstruction is
needed for the forward direction. The prefix map is still read — by
:func:`hets_prefixes`, from HETS' own ``Prefix: p: <iri>`` output — but only
to EXPAND a CURIE to a full IRI, so the table can be joined with the OWL file
and with the ``dl`` route.

The mangling is not invertible (a printed form containing a literal ``_u`` is
indistinguishable from a mangled separator), so this module never inverts it:
the reverse indexes are built FROM the forward map, and
:class:`HetsSymbolCollisionError` is raised at build time if two printed forms
mangle to the same symbol, rather than silently keeping whichever came last.

The 73 declarations with no TPTP symbol are a FACT, not an error
----------------------------------------------------------------
On OEO: 68 ``AnnotationProperty`` (annotation properties carry no logical
content under OWL 2's direct semantics, so a comorphism legitimately never
emits them) and 5 ``ObjectProperty`` declared but used in no logical axiom.
They are reported as ``in_tptp=False`` rows, never dropped. The 21 TPTP
symbols with no declaration — CASL numerals ``op_0``..``op_9``, OWL built-ins
``pred_Thing``/``pred_Nothing``, HETS' sort predicates ``sort_DATA``/
``sort_Thing``/``sort_xsd_u*`` and the collapsed facet predicate
``pred_____`` — are reported as :attr:`HetsSymbolTable.unmapped_tptp`.

The omitted axioms are derivable exactly
----------------------------------------
HETS names every translated axiom ``ax_ax<N>`` where ``<N>`` is the index of
``/dg``'s axiom item ``Ax<N>``, so ``{Ax<N> in /dg} \ {N with an ax_ax<N>
formula}`` is computable — see :func:`untranslated_axioms`. On the real pair
that difference is 8997 axioms, of which 8991 are ``AnnotationAssertion`` and
4 are ``SubAnnotationPropertyOf`` (both annotation axiom kinds, which OWL 2's
direct semantics gives no consequence, hence excluded by default) and exactly
2 are ``DataPropertyRange`` — ``OEO_00390094`` and ``OEO_00390098``, the two
axioms the lossy ``-Y`` translation drops. That agrees with the requesting
project's own count, reached by a completely different method (diffing against
a hand-reduced ontology), which is what makes the 2 trustworthy.

Two routes, and why this module exists at all
---------------------------------------------
No ``dl`` file is touched and no construct reaches the description-logic
tableau. The two-route rule applies at the level the whole OEO request is
about: the HETS translation is the SECOND FOL image of an ontology, to be
compared against :func:`unicode_fol_kit.dl.tbox_to_fol` /
:func:`unicode_fol_kit.dl.kb_to_fol` plus :func:`unicode_fol_kit.api.prove`.
A comparison is only worth anything if neither side is presented as more
complete than it is, which is what ``in_tptp``, ``unmapped_tptp`` and
:func:`untranslated_axioms` are for.

HETS' own translation defects, measured on the real pair, so a disagreement is
attributable rather than blamed on this kit:

* an n-ary ``DifferentIndividuals`` is expanded to FEWER than all pairs
  (strictly weaker than OWL 2 requires; 2 axioms in OEO);
* ``DataPropertyRange(d xsd:string)`` renders as
  ``forall x. exists y:DATA. (d(x,y) => y in xsd:string)`` — the existential
  OVER the implication, which is near-vacuous (3 axioms);
* both facets of a ``DatatypeRestriction`` collapse to the same predicate
  ``pred_____`` (the 7 ``idrange`` datatype definitions);
* 19 ``ax_ax<N>`` formula names are DUPLICATED, so a caller must not key
  formulas by name. :func:`untranslated_axioms` is duplicate-safe by
  construction: it works from the SET of indices present.
"""

from __future__ import annotations

import collections
import re
from dataclasses import dataclass
from typing import Dict, Mapping, Optional, Tuple

# Imported rather than re-implemented ON PURPOSE: ``kit_name`` has to be what
# tptp_input's reader actually produces for a TPTP predicate, so if that
# convention ever changes this table changes with it instead of silently
# desynchronising.
from ..fol.tptp_input import _cap

__all__ = [
    "HetsSymbol",
    "HetsSymbolTable",
    "HetsSymbolCollisionError",
    "UntranslatedAxiom",
    "hets_symbol_table",
    "untranslated_axioms",
    "hets_prefixes",
]

#: HETS prefixes a TPTP symbol by the entity's role. ``Individual`` becomes a
#: CASL operation (a constant), ``Datatype`` a sort, and every class or
#: property a predicate.
_KIND_PREFIX = {"Individual": "op_", "Datatype": "sort_"}
_DEFAULT_PREFIX = "pred_"

#: Every character outside this set becomes ``_u`` in a HETS TPTP symbol.
_NON_SYMBOL_CHAR = re.compile(r"[^A-Za-z0-9_]")

#: A TPTP symbol HETS could have produced, for the ``unmapped_tptp`` census.
_TPTP_SYMBOL = re.compile(r"\b(?:pred|op|sort)_[A-Za-z0-9_]*")

#: ``fof(ax_ax4027, axiom, ...)`` -> the axiom index 4027.
_AX_FORMULA = re.compile(r"\b(?:fof|cnf|tff)\(\s*ax_ax(\d+)\s*,")

#: ``/dg``'s axiom item name, ``Ax4027``.
_AX_ITEM = re.compile(r"^Ax(\d+)$")

#: ``AnnotationAssertion( rdfs:label <subject> "text"@lang )``, with the
#: language tag optional. The literal body allows backslash escapes because
#: HETS prints OWL literals with them.
_LABEL_AXIOM = re.compile(
    r'^AnnotationAssertion\(\s*rdfs:label\s+(\S+)\s+'
    r'"((?:[^"\\]|\\.)*)"(?:@([A-Za-z0-9-]+))?\s*\)$')

#: ``Prefix: obo: <http://purl.obolibrary.org/obo/>``, as HETS writes it into
#: a ``pp.dol`` or ``/theory`` rendering. The prefix NAME may be empty.
_PREFIX_LINE = re.compile(
    r"^[ \t]*Prefix:[ \t]*([A-Za-z0-9_.-]*):[ \t]*<([^>]*)>", re.MULTILINE)

#: The five OWL 2 axiom kinds whose direct semantics is empty, so a
#: comorphism that drops them loses nothing. Excluded from
#: :func:`untranslated_axioms` by default — justified by the OWL 2
#: specification, not by a heuristic about what HETS happens to do.
_ANNOTATION_KINDS = frozenset({
    "AnnotationAssertion",
    "SubAnnotationPropertyOf",
    "AnnotationPropertyDomain",
    "AnnotationPropertyRange",
    "Declaration",
})

_LEADING_FUNCTOR = re.compile(r"\s*([A-Za-z][A-Za-z0-9]*)")


class HetsSymbolCollisionError(RuntimeError):
    """Two declared entities mangle to the same HETS TPTP symbol.

    Raised when the table is BUILT, not when it is queried, and it names both
    IRIs. The mangling ``[^A-Za-z0-9_] -> "_u"`` is not injective, so a
    collision is possible in principle (it does not occur in OEO). Keeping
    whichever declaration came last would make every later lookup for the
    other entity silently answer about the wrong one — which is the kind of
    quiet wrong answer this kit refuses.
    """


@dataclass(frozen=True)
class HetsSymbol:
    """One declared OWL entity and its images on the HETS TPTP route.

    Fields:

    * ``printed`` — HETS' printed name, exactly as ``/dg`` gives it, and the
      INPUT to the mangling (``"obo:BFO_0000001"``, or a full IRI when
      no prefix was declared for it).
    * ``iri`` — the full IRI — :attr:`printed` with its CURIE prefix expanded
      through the prefix map. Equal to :attr:`printed` when it was
      already a full IRI or the prefix is unknown.
    * ``name`` — the entity name as ``/dg`` reports it.
    * ``kind`` — ``Class`` | ``ObjectProperty`` | ``DataProperty`` |
      ``AnnotationProperty`` | ``Individual`` | ``Datatype``.
    * ``tptp_name`` — the symbol in HETS' TPTP text
      (``"pred_obo_uBFO_0000001"``).
    * ``kit_name`` — the symbol as :func:`unicode_fol_kit.fol.tptp_input.parse_tptp`
      reads it back (``"Pred_obo_uBFO_0000001"``).
    * ``in_tptp`` — whether :attr:`tptp_name` actually occurs in the TPTP text.
      ``False`` is a reported fact, not an error — see the module
      docstring on the 73 OEO declarations with no symbol.
    * ``labels`` — ``(label, language-tag)`` pairs from this entity's
      ``rdfs:label`` annotation assertions; the tag is ``""`` when the
      literal carried none.
    """

    printed: str
    iri: str
    name: str
    kind: str
    tptp_name: str
    kit_name: str
    in_tptp: bool
    labels: Tuple[Tuple[str, str], ...] = ()


@dataclass(frozen=True)
class HetsSymbolTable:
    """Every declared entity of one development-graph node, joined to its TPTP symbols.

    Fields:

    * ``symbols`` — one :class:`HetsSymbol` per ``/dg`` declaration, in
      declaration order.
    * ``prefixes`` — the prefix map used to expand CURIEs (possibly empty).
    * ``unmapped_tptp`` — sorted TPTP symbols that occur in the text with no
      declaration behind them — CASL numerals, OWL built-ins and HETS'
      own sort predicates. Reported rather than hidden, because a
      formula over one of these is a formula this table cannot explain.
    * ``unexpanded_prefixes`` — sorted CURIE prefixes that appear in a
      declaration but are absent from :attr:`prefixes`, so those rows'
      :attr:`HetsSymbol.iri` is still the CURIE. Reported for the same
      reason as the two fields above: an empty or wrong prefix map
      otherwise degrades the table silently, and a CURIE cannot be
      joined with the OWL file or with the ``dl`` route. Empty means
      every declaration's IRI is a full IRI.
    """

    symbols: Tuple[HetsSymbol, ...]
    prefixes: Mapping[str, str]
    unmapped_tptp: Tuple[str, ...]
    unexpanded_prefixes: Tuple[str, ...] = ()

    def by_iri(self, iri: str) -> Optional[HetsSymbol]:
        """The entity with this full IRI, or ``None``."""
        return self._index("iri").get(iri)

    def by_printed(self, printed: str) -> Optional[HetsSymbol]:
        """The entity with this printed (possibly CURIE) name, or ``None``."""
        return self._index("printed").get(printed)

    def by_tptp_name(self, name: str) -> Optional[HetsSymbol]:
        """The entity behind this HETS TPTP symbol, or ``None``."""
        return self._index("tptp_name").get(name)

    def by_kit_name(self, name: str) -> Optional[HetsSymbol]:
        """The entity behind this kit predicate/function name, or ``None``."""
        return self._index("kit_name").get(name)

    def by_label(self, label: str, *, lang: str = "en") -> Tuple[HetsSymbol, ...]:
        """Every entity carrying this ``rdfs:label`` in this language.

        A TUPLE, even though no OEO label is shared by two subjects:
        ``rdfs:label`` is not required to be unique in OWL 2, so a function
        that returned one symbol would be silently picking for the caller on
        the next ontology. Pass ``lang=""`` for the untagged literals.
        """
        return tuple(symbol for symbol in self.symbols
                     if (label, lang) in symbol.labels)

    def _index(self, field: str) -> Dict[str, HetsSymbol]:
        # Built lazily from the forward map and cached on the (frozen)
        # instance via object.__setattr__ -- never by inverting the mangling,
        # which is not injective.
        cache = getattr(self, "_indexes", None)
        if cache is None:
            cache = {}
            object.__setattr__(self, "_indexes", cache)
        if field not in cache:
            cache[field] = {getattr(s, field): s for s in self.symbols}
        return cache[field]


@dataclass(frozen=True)
class UntranslatedAxiom:
    """One ``/dg`` axiom with no formula in the TPTP translation.

    Fields:

    * ``name`` — the ``/dg`` axiom item name, ``"Ax4027"``.
    * ``owl`` — the axiom's OWL functional-syntax text, verbatim.
    * ``kind`` — its leading functor, ``"DataPropertyRange"``.
    """

    name: str
    owl: str
    kind: str


def hets_prefixes(theory_text: str) -> Dict[str, str]:
    """Read HETS' own ``Prefix: p: <iri>`` lines out of a rendering.

    Works on anything HETS prints with a prefix block — a ``pp.dol`` file or
    the native ``/theory`` text. The empty prefix (``Prefix: : <...>``) comes
    back under the key ``""``. A repeated prefix keeps the LAST binding, which
    is what a reader of the document would see.

    Args:
        theory_text: HETS output containing a prefix block (or not).

    Returns:
        ``{prefix-name: namespace-iri}``; empty when there is no block.

    Example:
        >>> hets_prefixes("     Prefix: obo: <http://purl.obolibrary.org/obo/>")
        {'obo': 'http://purl.obolibrary.org/obo/'}
    """
    return {match.group(1): match.group(2)
            for match in _PREFIX_LINE.finditer(theory_text)}


def _mangle(printed: str, kind: str) -> str:
    """HETS' printed name -> its TPTP symbol (the rule the module docstring states)."""
    prefix = _KIND_PREFIX.get(kind, _DEFAULT_PREFIX)
    return prefix + _NON_SYMBOL_CHAR.sub("_u", printed)


def _expand(printed: str, prefixes: Mapping[str, str]):
    """Expand a CURIE through the prefix map.

    A full IRI is recognised by its scheme separator ``://``, so
    ``https://example.org/x`` is never mistaken for the CURIE prefix
    ``https``.

    Returns:
        ``(iri, unexpanded_prefix)``. The second element is the CURIE prefix
        that could NOT be expanded, or ``None``; the caller collects those so
        an absent prefix map is reported instead of quietly leaving CURIEs in
        the table.
    """
    head, sep, tail = printed.partition(":")
    if not sep or tail.startswith("//"):
        return printed, None
    namespace = prefixes.get(head)
    if namespace is None:
        return printed, head
    return namespace + tail, None


def _pick_node(dg: Mapping, node: Optional[str]) -> Mapping:
    """The one ``DGNode`` to read, by name or by being the only one.

    Raises:
        ValueError: the graph has no node, or several and ``node`` was not
            given (or names one that is not there). Never picks for the
            caller: which node a symbol table is about changes every answer
            drawn from it.
    """
    graph = dg.get("DGraph") or {}
    nodes = graph.get("DGNode") or []
    if isinstance(nodes, dict):
        nodes = [nodes]
    if not nodes:
        raise ValueError(
            "hets: this development graph has no DGNode, so there are no "
            "declarations to build a symbol table from. If the response came "
            "from HetsClient.dg, check that the upload succeeded.")
    if node is not None:
        for candidate in nodes:
            if candidate.get("name") == node:
                return candidate
        raise ValueError(
            f"hets: no development-graph node named {node!r}; this graph has "
            f"{[n.get('name') for n in nodes]!r}.")
    if len(nodes) != 1:
        raise ValueError(
            "hets: this development graph has "
            f"{len(nodes)} nodes ({[n.get('name') for n in nodes]!r}) — pass "
            "node=<name> to say which one the symbol table is about. Guessing "
            "would make every lookup answer about an arbitrary ontology.")
    return nodes[0]


def _labels_by_subject(axioms) -> Dict[str, Tuple[Tuple[str, str], ...]]:
    """Collect ``rdfs:label`` assertions, keyed by HETS' printed subject name."""
    found = collections.defaultdict(list)
    for axiom in axioms:
        match = _LABEL_AXIOM.match(axiom.get("Axiom", "").strip())
        if match:
            subject, label, lang = match.groups()
            found[subject].append((label, lang or ""))
    return {subject: tuple(pairs) for subject, pairs in found.items()}


def hets_symbol_table(dg: Mapping, tptp: str, *,
                      prefixes: Optional[Mapping[str, str]] = None,
                      node: Optional[str] = None) -> HetsSymbolTable:
    """Join one ``/dg`` node's declarations onto the symbols of a TPTP translation.

    Args:
        dg: a development-graph dict, as
            :meth:`unicode_fol_kit.hets.client.HetsClient.dg` returns it.
        tptp: the TPTP text HETS produced for that node.
        prefixes: a prefix map for expanding CURIEs to full IRIs, e.g. from
            :func:`hets_prefixes`. Without it, :attr:`HetsSymbol.iri` equals
            :attr:`HetsSymbol.printed` for every CURIE — the table still
            works, the IRIs are just not expanded.
        node: which development-graph node. Required when the graph has more
            than one.

    Returns:
        A :class:`HetsSymbolTable`.

    Raises:
        HetsSymbolCollisionError: two declarations mangle to one symbol.
        ValueError: the node cannot be identified.
    """
    prefixes = dict(prefixes or {})
    chosen = _pick_node(dg, node)
    declarations = chosen.get("Declarations") or []
    axioms = chosen.get("Axioms") or []
    labels = _labels_by_subject(axioms)
    present = set(_TPTP_SYMBOL.findall(tptp))

    by_tptp_name = collections.defaultdict(list)
    unexpanded = set()
    symbols = []
    for declaration in declarations:
        printed = declaration.get("iri") or declaration.get("name") or ""
        kind = declaration.get("kind") or ""
        tptp_name = _mangle(printed, kind)
        by_tptp_name[tptp_name].append(printed)
        iri, missing_prefix = _expand(printed, prefixes)
        if missing_prefix is not None:
            unexpanded.add(missing_prefix)
        symbols.append(HetsSymbol(
            printed=printed,
            iri=iri,
            name=declaration.get("name") or printed,
            kind=kind,
            tptp_name=tptp_name,
            kit_name=_cap(tptp_name),
            in_tptp=tptp_name in present,
            labels=labels.get(printed, ()),
        ))

    clashes = {name: sorted(set(owners))
               for name, owners in by_tptp_name.items()
               if len(set(owners)) > 1}
    if clashes:
        detail = "; ".join(
            f"{name} <- {', '.join(owners)}" for name, owners in sorted(clashes.items()))
        raise HetsSymbolCollisionError(
            f"hets: {len(clashes)} HETS TPTP symbol(s) are claimed by more "
            f"than one declared entity: {detail}. HETS' mangling "
            "([^A-Za-z0-9_] -> '_u') is not injective, so this table cannot "
            "say which entity a formula over such a symbol is about. It "
            "refuses to build rather than keep whichever declaration came "
            "last and answer every later lookup about the wrong entity.")

    return HetsSymbolTable(
        symbols=tuple(symbols),
        prefixes=prefixes,
        unmapped_tptp=tuple(sorted(present - set(by_tptp_name))),
        unexpanded_prefixes=tuple(sorted(unexpanded)),
    )


def untranslated_axioms(dg: Mapping, tptp: str, *, node: Optional[str] = None,
                        include_annotations: bool = False
                        ) -> Tuple[UntranslatedAxiom, ...]:
    r"""The ``/dg`` axioms with no formula in the TPTP translation.

    HETS names a translated axiom ``ax_ax<N>`` after the ``/dg`` axiom item
    ``Ax<N>``, so the difference is computable. Duplicate formula names (19 of
    them in the real file — a HETS defect) cannot affect the result: the
    comparison is between SETS of indices.

    Args:
        dg: the development-graph dict.
        tptp: the TPTP text to compare against.
        node: which development-graph node; required when there is more
            than one.
        include_annotations: also report the OWL 2 annotation axiom kinds
            (``AnnotationAssertion``, ``SubAnnotationPropertyOf``,
            ``AnnotationPropertyDomain``, ``AnnotationPropertyRange``,
            ``Declaration``). They are excluded by default because OWL 2's
            direct semantics gives them no consequence, so a comorphism that
            drops them loses nothing — that exclusion is a SPEC fact, not a
            guess about this translation.

    Returns:
        One :class:`UntranslatedAxiom` per axiom with no image, in ``/dg``
        order. An EMPTY tuple means "computed, and nothing was omitted" — it
        never means "not computed".

    Raises:
        ValueError: the node cannot be identified.
    """
    chosen = _pick_node(dg, node)
    present = {int(index) for index in _AX_FORMULA.findall(tptp)}
    omitted = []
    for axiom in chosen.get("Axioms") or []:
        name = axiom.get("name") or ""
        item = _AX_ITEM.match(name)
        if not item or int(item.group(1)) in present:
            continue
        text = axiom.get("Axiom") or ""
        functor = _LEADING_FUNCTOR.match(text)
        kind = functor.group(1) if functor else ""
        if not include_annotations and kind in _ANNOTATION_KINDS:
            continue
        omitted.append(UntranslatedAxiom(name=name, owl=text, kind=kind))
    return tuple(omitted)
