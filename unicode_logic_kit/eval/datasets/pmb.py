"""Adapter for the Parallel Meaning Bank (PMB): SBN documents, read through
:mod:`unicode_logic_kit.drt` into gold FOL via :func:`~unicode_logic_kit.drt.parser.parse_sbn`
and :func:`~unicode_logic_kit.drt.export.drs_to_fol`.

Unlike every other adapter in this package, PMB carries no ready-made NL/FOL pair file:
its unit of data is ONE DIRECTORY PER DOCUMENT (``p<NN>/d<NNNN>/``), holding the DRS in
SBN notation (``<lang>.drs.sbn``) alongside the raw sentence(s) it annotates
(``<lang>.raw``) and a few other sibling files this adapter does not read. This module's
whole job is producing gold FOL from the SBN side; the NL side is carried through
best-effort, since that is what the sibling file happens to contain.

Source, release layout, and license (verified 2026-09-17 against a local pmb-5.1.0
extraction's own ``licenses/`` directory)
--------------------------------------------------------------------------------------
Source: https://pmb.let.rug.nl/data.php (releases, ``pmb-<version>.zip``). Like every
loader in this package, :func:`load_pmb` reads LOCAL files the caller already obtained —
nothing here downloads anything.

Each PMB release's ``data/<lang>/gold/p<NN>/d<NNNN>/`` directory is one annotated
document, ``<lang>`` a two-letter code (``en``, ``de``, ``it``, ``nl``, ...). This
adapter reads whichever ``<lang>.drs.sbn`` files it is given or finds; it does not
special-case English.

**License is TWO-LAYERED, and the two layers are NOT the same license** (the raw
proposal that motivated this module conflated them — corrected here):

* The PMB **annotations** (the DRS/SBN layer this module actually parses) are
  Open Data Commons Attribution License v1.0 (ODC-BY —
  https://opendatacommons.org/licenses/by/1.0/), stated plainly in the release's own
  ``licenses/PMB_LICENSE.txt``: share/create/adapt freely, attribution required.
* The **raw texts** (``<lang>.raw``, what :func:`load_pmb` puts in ``nl_conclusion``)
  are explicitly NOT covered by ODC-BY: the same ``PMB_LICENSE.txt`` says each is
  "published under their respective license terms, as noted in their accompanying .met
  files" — but in the actual pmb-5.1.0 release, a document's ``.met`` file records only
  a ``subcorpus:`` label (``Tatoeba``, ``SICK``, ``RTE``, ``TREC2002``/``TREC2003``,
  ``INTERSECT``, ``GMB``, ...) and a ``source:`` URL, never an explicit license string —
  so a caller who wants to REDISTRIBUTE ``nl_conclusion`` text must trace that source
  themselves (the release's ``licenses/*-README.txt`` files document several of the
  subcorpora's own terms, e.g. ``SICK-README.txt``, ``Tatoeba_LICENSE.txt``). This
  adapter reads a document's ``.met`` file for neither field (out of scope: neither the
  DRS nor the label this module produces depends on it) and copies no PMB file into this
  repository — a caller redistributing what :func:`load_pmb` yields is bound by the same
  two-layer license above, not a blanket statement this module could truthfully make.

How much of the SBN release does :func:`parse_sbn` actually accept? — measured, not
guessed
------------------------------------------------------------------------------------
Run against pmb-5.1.0's complete English gold release, all 12053
``data/en/gold/p*/d*/en.drs.sbn`` files (2026-09-17): **9624 / 12053 (79.8%) parse AND
round-trip** (``drs_to_fol(parse_sbn(text)[0]).to_unicode_str()`` re-parses via
:func:`unicode_logic_kit.api.parse_any` to the byte-identical string). Every one of the
remaining 2429 raises :class:`~unicode_logic_kit.drt.parser.SBNSyntaxError` naming an
out-of-scope construct — NONE raises anything else (no crash). By construct:

* 1123 — a WILDCARD role target (``?``, ``+``, or bare ``-``): boxer's own placeholder
  for a wh-question's unresolved filler ("which singer" -> ``Name ?``) or a vague
  comparative degree ("long hair" -> ``Value +``). Neither has a determinate DRS reading.
* 953 — a box-operator this subset does not support: the SDRT discourse relations
  (``CONTINUATION`` 448, ``CONTRAST`` 91, ``CONJUNCTION`` 78, ``CONSEQUENCE`` 50,
  ``EXPLANATION`` 42, ``CONDITION`` 5, ``PRECONDITION`` 4, ``RESULT`` 4,
  ``ALTERNATION`` 2, ``COMMENTARY`` 1, ``ELABORATION`` 1) and the two modal operators
  (``POSSIBILITY`` 174, ``NECESSITY`` 53) — this kit's DRS conditions have no
  discourse-relation or modal-box reading.
* 162 — a clock-time constant (``ClockTime 14:30``): a genuine PMB constant kind this
  subset's bare-constant widening (deictic words, integers) does not cover.
* 116 — a sense token not of the WordNet form ``lemma.pos.NN`` (this subset's
  ``LEMMA`` is ``[a-z][a-z_]*``, see :mod:`unicode_logic_kit.drt.parser`'s module
  docstring), split three ways: 95 with a hyphen inside the lemma (``ping-pong.n.01``,
  ``t-shirt.n.01``, ``well-known.a.01``, ...) — a real WordNet compounding convention
  this module does not widen ``LEMMA`` for, unlike the (deliberately narrower) role-name
  hyphen it does accept; 19 with an apostrophe/possessive inside the lemma
  (``parkinson's_disease.n.01``, ``ladies'_room.n.01``, ``alzheimer's.n.01``,
  ``old_wives'_tale.n.01``, ...) — a DIFFERENT WordNet convention from hyphenation, not
  a subcase of it; and 2 with a digit inside the lemma (``co2.n.01``, ``fiat_500.n.01``).
* a long tail (75) of one-off constants this subset does not parse: 10 ``YearOfCentury``
  decade constants (``'198X'``), 21 sports-score values (``6-2``), 16 day-of-week names
  (``monday``), 12 decimal and 4 fraction ``Quantity`` values (``3.4``, ``3/4``), 10
  single-letter grade values, one role-hook offset that points outside its document, and
  one DRS accessibility violation (:meth:`~unicode_logic_kit.drt.nodes.DRS.validate`
  refusing a role target that escapes its own negation scope).

This is a ROBUSTNESS/coverage measurement, not a translation-ACCURACY one: PMB ships no
independent gold FOL to compare the 9624 successes against, so "correct" here means
"parses under this subset's own documented grammar and round-trips through this kit's
FOL printer/parser" — see ``tests/test_datasets_pmb.py`` for the differential this
number comes from, gated behind the ``UFK_PMB_SBN_DIR`` environment variable so it never
runs without a real, locally-extracted release.
"""

from pathlib import Path
from typing import FrozenSet, Iterable, Iterator, Optional, Tuple, Union

from ._base import DatasetExample, _register_dataset_info
from ...drt.export import drs_to_fol
from ...drt.parser import SBNSyntaxError, parse_sbn

__all__ = ["load_pmb"]


_register_dataset_info(
    "pmb",
    license=(
        "TWO layers, not one (see the module docstring for the full derivation): the "
        "PMB ANNOTATIONS (the DRS/SBN layer this loader parses) are ODC-BY 1.0 "
        "(https://opendatacommons.org/licenses/by/1.0/, attribution required) per the "
        "release's own licenses/PMB_LICENSE.txt (verified 2026-09-17); the RAW TEXTS "
        "(nl_conclusion) are explicitly NOT ODC-BY -- PMB_LICENSE.txt defers to each "
        "document's own .met file, which in practice records only a subcorpus label "
        "and a source URL, never an explicit license string, so redistributing raw "
        "sentence text requires tracing that source yourself."
    ),
    source_url="https://pmb.let.rug.nl/data.php",
    citation_hint=(
        'Abzianidze et al., "The Parallel Meaning Bank: Towards a Multilingual Corpus '
        'of Translations Annotated with Compositional Meaning Representations", '
        "EACL 2017."
    ),
)


def _iter_sbn_paths(paths: Union[str, Path, Iterable[Union[str, Path]]]) -> Iterator[Path]:
    """Normalize ``paths`` (see :func:`load_pmb`) into a sorted stream of ``.drs.sbn``
    file paths: a single directory is WALKED for PMB's own release layout
    (``p<NN>/d<NNNN>/<lang>.drs.sbn``, any depth/part/language); anything else is
    treated as an iterable of file paths the caller already obtained."""
    if isinstance(paths, (str, Path)):
        root = Path(paths)
        if not root.is_dir():
            raise ValueError(
                f"pmb: {root} is not a directory to walk — pass an iterable of "
                f".drs.sbn file paths instead, or a real PMB release directory")
        yield from sorted(root.rglob("*.drs.sbn"))
        return
    for p in paths:
        yield Path(p)


def _doc_id(path: Path) -> Tuple[str, str, str]:
    """PMB's own ``p<NN>/d<NNNN>`` document identifier, read off ``path``'s two parent
    directories (the DOCUMENT directory, then the PART directory it sits in) — the
    release's own addressing scheme, not a positional fallback."""
    doc_dir = path.parent.name
    part_dir = path.parent.parent.name
    return f"{part_dir}/{doc_dir}", part_dir, doc_dir


def _sibling_raw_text(sbn_path: Path) -> Optional[str]:
    """The sentence(s) ``sbn_path`` annotates, read from the sibling ``<lang>.raw``
    file PMB ships alongside every ``<lang>.drs.sbn`` — BEST-EFFORT: ``None`` if that
    file is missing or empty (never raised; a missing raw sibling says nothing about
    whether the SBN itself, which is what this adapter is really reading, is usable)."""
    name = sbn_path.name
    if not name.endswith(".drs.sbn"):
        return None
    lang = name[: -len(".drs.sbn")]
    raw_path = sbn_path.with_name(f"{lang}.raw")
    if not raw_path.is_file():
        return None
    text = raw_path.read_text(encoding="utf-8").strip()
    return text or None


def load_pmb(paths: Union[str, Path, Iterable[Union[str, Path]]], *,
             known_bad_ids: Optional[FrozenSet[str]] = None,
             ) -> Iterator[DatasetExample]:
    """Read PMB SBN documents into :class:`DatasetExample` objects, one per document.

    Field mapping: ``id`` = the ``p<NN>/d<NNNN>`` fragment PMB itself addresses the
    document by; ``nl_premises``/``fol_premises`` are always ``()`` (PMB annotates
    single documents, not premise/conclusion pairs); ``nl_conclusion`` = the sibling
    ``<lang>.raw`` text (best-effort — see :func:`_sibling_raw_text` — ``None`` if
    absent); ``fol_conclusion`` = ``drs_to_fol(parse_sbn(text)[0]).to_unicode_str()``;
    ``label`` is always ``None`` (PMB carries no entailment/classification label).

    A document whose ``parse_sbn`` call raises
    :class:`~unicode_logic_kit.drt.parser.SBNSyntaxError` (see the module docstring for
    how common this is, and why) is NEVER silently dropped: it still yields a
    :class:`DatasetExample`, with ``fol_conclusion=None`` (the same "nothing to check"
    convention :mod:`~unicode_logic_kit.eval.datasets.fracas` uses for its four
    question-less problems) and the refusal's message recorded verbatim in
    ``meta["parse_error"]`` — the SAME "refuse loudly, never approximate" contract
    ``parse_sbn`` itself follows, carried one level up instead of raised out of this
    generator (which would abort the whole iteration on the FIRST bad document, useless
    for a corpus of thousands).

    ``meta`` also carries ``part``/``doc`` (the two path components ``id`` is built
    from), ``lang`` (the language code ``<lang>.drs.sbn`` was read from), and, on a
    successful parse, ``sbn_mapping`` (:meth:`~unicode_logic_kit.drt.parser.SBNMapping.to_dict`
    — the sense-token/quoted-constant sanitization :func:`parse_sbn` applied, ``None``
    when parsing failed).

    Args:
        paths: EITHER a single local directory to WALK for PMB's own release layout
            (``p<NN>/d<NNNN>/<lang>.drs.sbn``, any language/part, any depth), OR an
            iterable of local ``.drs.sbn`` file paths the caller already obtained.
            Nothing here downloads anything, matching every other adapter in this
            package.
        known_bad_ids: ids (in the ``"pNN/dNNNN"`` form) to flag as ``known_bad`` — the
            same caller-curated mechanic every adapter has; independent of, and not
            inferred from, a document's own ``parse_error``.

    Raises:
        ValueError: ``paths`` is a single path that is not a directory, or the same
            document id is produced twice (a caller data-integrity problem — e.g. two
            different release trees passed together — named rather than silently
            merged).
    """
    known_bad = frozenset(known_bad_ids) if known_bad_ids else frozenset()
    seen: set = set()

    for sbn_path in _iter_sbn_paths(paths):
        example_id, part, doc = _doc_id(sbn_path)
        if example_id in seen:
            raise ValueError(
                f"pmb: duplicate document id {example_id!r} (from {sbn_path}) — "
                f"the same p<NN>/d<NNNN> was produced twice")
        seen.add(example_id)

        lang = sbn_path.name[: -len(".drs.sbn")] if sbn_path.name.endswith(".drs.sbn") else None
        text = sbn_path.read_text(encoding="utf-8")
        nl_conclusion = _sibling_raw_text(sbn_path)

        meta: dict = {"part": part, "doc": doc, "lang": lang,
                     "sbn_mapping": None, "parse_error": None}
        fol_conclusion: Optional[str] = None
        try:
            drs, mapping = parse_sbn(text)
            fol_conclusion = drs_to_fol(drs).to_unicode_str()
            meta["sbn_mapping"] = mapping.to_dict()
        except SBNSyntaxError as e:
            meta["parse_error"] = str(e)

        yield DatasetExample(
            id=example_id,
            nl_premises=(),
            fol_premises=(),
            nl_conclusion=nl_conclusion,
            fol_conclusion=fol_conclusion,
            label=None,
            known_bad=example_id in known_bad,
            meta=meta,
        )
