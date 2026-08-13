"""Adapter for the WillowNLtoFOL dataset (Deveci, "A Diagnostic Framework for
Compositional Generalization via NL-to-FOL Translation", JLLI 2026; earlier
described in Deveci's 2024 METU master's thesis) — local JSONL only, no
network access.

Source and verified schema
---------------------------
Source: https://huggingface.co/datasets/iedeveci/WillowNLtoFOL (unauthenticated;
verified 2026-08-12 directly via the Hugging Face datasets-server ``splits``,
``first-rows``, and ``rows`` APIs, and by fetching the dataset's raw
``README.md`` — https://huggingface.co/datasets/iedeveci/WillowNLtoFOL/raw/main/README.md
— for its YAML metadata and licensing prose). The ``splits`` endpoint reports
exactly two splits under config ``"default"``: ``"train"`` (16014 rows) and
``"test"`` (90 rows). NOTE: the dataset card's prose additionally describes a
"``WillowNLtoFOL_extended``" 90-pair out-of-distribution stress-test subset —
that appears to BE the ``"test"`` split under a different name in the card's
prose than in the actual data (the ``splits``/``info`` APIs show no subset or
config named ``extended``); this loader reads whatever split you point it at
and does not depend on which of the two names is "correct".

Each verified row (``first-rows``/``rows`` APIs, both splits) is a flat JSON
object with EXACTLY two keys:

* ``"NL_sentence"``   — ``str``, one natural-language sentence.
* ``"FOL_expression"`` — ``str``, its FOL translation, written DIRECTLY in
  this kit's own unicode surface syntax (``∀``/``∃``/``∧``/``∨``/``¬``/``→``/
  ``↔``/``⊕`` all appear across the verified sample rows and the ``"fol"``
  dialect is what ``api.parse_any`` selects for every one that parses at
  all — no ASCII/LaTeX fallback notation was observed anywhere in the sample).

Like MALLS, WillowNLtoFOL has NO id field, NO premises/conclusion structure,
and NO entailment label — it is a flat bag of (sentence, formula) pairs. This
adapter maps that onto :class:`~unicode_fol_kit.eval.datasets.DatasetExample`
with the SAME convention :mod:`~unicode_fol_kit.eval.datasets.malls` uses for
MALLS (an equally-shaped translation-pair dataset):

* ``nl_conclusion`` / ``fol_conclusion`` carry ``"NL_sentence"`` /
  ``"FOL_expression"``.
* ``nl_premises`` / ``fol_premises`` are always ``()``.
* ``label`` is always ``None``.

Does the gold notation actually parse under this kit? — an honest, measured
answer, not a guess
--------------------------------------------------------------------------
The dataset card states the FOL annotations were "aggressively filtered using
``nltk.sem.logic``" to reject unparseable/unbound-variable formulas — but
``nltk.sem.logic`` accepts several things this kit's ``fol`` grammar
deliberately does not, so "filtered by nltk" does not imply "parses here".
To answer this honestly rather than assume it, a STRATIFIED sample of 2100 of
the 16014 real ``train`` rows (row offsets 0, 100, ..., 900, then 1500, 3000,
..., 15000, 15900 — spanning the whole file, fetched 2026-08-12 via the
``rows`` API) was run through ``unicode_fol_kit.api.parse_any`` and, for
whatever parsed, ``unicode_fol_kit.api.check``:

* 2075 / 2100 (98.8%) parse AND pass ``check()`` (closed, arity-consistent,
  lambda-free) outright.
* 25 / 2100 (1.2%) FAIL TO PARSE under every dialect ``parse_any`` tries. Two
  recurring, real causes accounted for all 25:

  1. (~21/25) Mixing ``∧``/``∨`` (or ``∧``/``⊕``) at the same nesting depth
     without disambiguating parentheses, e.g. row 148's
     ``"∀y (Bird(y) ∧ Predator(y) ↔ (Hunt(y) ∨ EatMeat(y) ∧ ¬EatSeeds(y)))"``
     (the ``Hunt(y) ∨ EatMeat(y) ∧ ¬EatSeeds(y)`` clause). This kit's ``fol``
     grammar deliberately refuses to guess a precedence between ``∧``, ``∨``,
     and ``⊕`` rather than silently pick one (see the parser's own
     ``SYNTAX_ERROR`` hint text) — a real, structural difference from
     ``nltk.sem.logic``'s (and most textbooks') convention of ``∧`` binding
     tighter than ``∨``.
  2. (remaining few) A predicate identifier that does not start with an
     uppercase ASCII letter, which this kit's ``fol`` grammar requires
     (predicate names match ``[A-Z][a-zA-Z0-9]*``; a lower-initial identifier
     is parsed as a TERM, not a predicate, so e.g. row 1554's
     ``"∀x (Device(x) → (Android(x) ∨ iOS(x)))"`` fails because ``iOS`` starts
     with a lowercase letter, and row 15071's ``"...∃y (Café(y) ∧ ...)"``
     fails because ``é`` is outside the grammar's ASCII letter class for
     predicate names.

* 1 / 2100 (0.05%) PARSES but fails ``check()``: row 15947,
  ``"∃x (Chef(x) ∧ ∃y (Cook(y) ∧ ∀z (Meal(z) ∧ CookedBy(z, y) → Cook(x, z))))"``
  uses the predicate ``Cook`` at TWO different arities in the same formula
  (``Cook(y)`` unary, ``Cook(x, z)`` binary) — a genuine annotation defect,
  not a kit limitation; ``check()`` reports it as an ``arity_conflict``.

None of this is hidden: the fixture below (``tests/fixtures/willow_mini.jsonl``)
deliberately includes real rows from BOTH failure classes above plus the one
``check()``-only failure, and ``tests/test_datasets_willow.py`` asserts
``audit_examples`` finds exactly them — so a caller loading the real 16014-row
file and running :func:`~unicode_fol_kit.eval.datasets.audit_examples` should
expect roughly this same ~98.8% clean rate, not 100%.

License — a discrepancy flagged, not silently resolved
--------------------------------------------------------
The iedeveci/WillowNLtoFOL Hugging Face card states, both in its YAML
frontmatter (``license: cc-by-4.0``) and in its "Licensing Information" prose
section: **CC-BY-4.0** ("You are free to share and adapt the material for any
purpose, even commercially, provided you give appropriate credit..."),
verified directly against the raw README.md on 2026-08-12.

This conflicts with a DIFFERENT, related dataset's card: fvossel/groves
(GROVES, which uses WillowNLtoFOL as one of two NL sources) states in its own
"Licensing" section that "WillowNLtoFOL ... originally licensed under
**CC BY-NC-ND 4.0**" (also verified 2026-08-12). This loader reads
iedeveci/WillowNLtoFOL directly, so :data:`~unicode_fol_kit.eval.datasets.DATASET_INFO`
below records what is VERIFIED AT THAT PRIMARY SOURCE TODAY (CC-BY-4.0) — not
the GROVES card's claim about an earlier state of it. The discrepancy (a more
restrictive license claimed elsewhere for what may be an earlier version of
the same data) is flagged here rather than silently resolved either way.
ADDITIONALLY, per this repository's author (stated 2026-08-12): explicit
usage permission for the GROVES/unicode-fol-kit use of WillowNLtoFOL was
obtained from the Willow authors — so whichever of the two license readings
applies, this repository's own use (including the real-rows test fixture
below) is covered by that direct permission. Third parties redistributing
Willow data should still confirm the applicable license themselves.

This module never downloads anything — obtain the data yourself (e.g. via the
``datasets`` library, ``load_dataset("iedeveci/WillowNLtoFOL", split="train").to_json("willow_train.jsonl")``,
which yields the one-JSON-object-per-line format this loader expects) and
pass its local JSONL path to :func:`load_willow`.
"""

import json
import re
import unicodedata
from pathlib import Path
from typing import Dict, FrozenSet, Iterator, Optional, Tuple, Union

from lark import Lark, Transformer
from lark.exceptions import LarkError, VisitError

from ...fol.nodes import (
    Node, Atom, Not, And, Or, Xor, Implies, Iff, Quantifier,
    Variable, Constant, Function, free_variables,
)
from ._base import DatasetExample, _register_dataset_info

__all__ = ["load_willow", "repair_willow_formula"]

_register_dataset_info(
    "willow",
    license=(
        "CC-BY-4.0, per the iedeveci/WillowNLtoFOL Hugging Face card (raw "
        "README.md frontmatter `license: cc-by-4.0` plus its 'Licensing "
        "Information' section, verified 2026-08-12). NOTE: the fvossel/groves "
        "dataset card (GROVES, built in part from WillowNLtoFOL) states this "
        "same source was 'originally licensed under CC BY-NC-ND 4.0' -- a "
        "more restrictive claim that conflicts with what iedeveci/WillowNLtoFOL "
        "publishes today; this record reflects what is verified AT THAT "
        "PRIMARY SOURCE, not the GROVES card's claim about an earlier state "
        "of it. Explicit usage permission for the GROVES/unicode-fol-kit use "
        "was additionally obtained from the Willow authors (per this "
        "repository's author, 2026-08-12). Third parties should confirm the "
        "applicable license themselves before redistributing."
    ),
    source_url="https://huggingface.co/datasets/iedeveci/WillowNLtoFOL",
    citation_hint=(
        "Deveci, İbrahim Ethem. \"A Diagnostic Framework for "
        "Compositional Generalization via NL-to-FOL Translation.\" Journal "
        "of Logic, Language and Information (2026). "
        "https://doi.org/10.1007/s10849-026-09480-0"
    ),
)


# --------------------------------------------------------------------------- #
# The Willow repair dialect: an import-time grammar for the ~1.2% tail
#
# ~98.8% of WillowNLtoFOL's gold formulas already parse under this kit's own
# grammar (measured — see the module docstring), so the loader touches
# nothing for those. The measured failure tail has exactly two structural
# causes, and this dedicated grammar exists to read PRECISELY those:
#
#   1. ∧/∨/⊕ mixed at one nesting depth without parentheses. The kit's own
#      grammar refuses to guess a precedence; Willow's formulas were filtered
#      through ``nltk.sem.logic``, whose convention is that ∧ binds tighter
#      than ∨ — so THIS grammar adopts the textbook/NLTK precedence
#      ¬ > ∧ > ∨ > ⊕ > → (right-assoc) > ↔, i.e. the reading the dataset's
#      own pipeline accepted. (∨-vs-⊕ mixing without parens never occurred
#      in the measured sample; the relative order chosen here is documented,
#      not observed.)
#   2. Predicate identifiers outside the kit's ``[A-Z][a-zA-Z0-9]*`` class
#      (``iOS``, ``Café``). The converter renames minimally: NFKD
#      transliteration for non-ASCII letters (``Café`` → ``Cafe``), then the
#      first letter upcased (``iOS`` → ``IOS``) — injectively per namespace,
#      with the mapping recorded in ``meta``.
#
# The loader (``convert_fol=True``, the default) first tries ``api.parse_any``
# — a formula the kit already accepts stays byte-for-byte verbatim — and only
# a formula the kit refuses goes through this repair grammar; whatever fails
# BOTH keeps its verbatim string plus a recorded ``fol_conversion_error``
# (e.g. a genuinely malformed formula), never a crash or a silent drop.
# --------------------------------------------------------------------------- #

_WILLOW_GRAMMAR = r"""
?start: formula
?formula: iff
?iff: implies ("↔" implies)*
?implies: xor "→" implies        -> implies
        | xor
?xor: disj ("⊕" disj)*
?disj: conj ("∨" conj)*
?conj: unary ("∧" unary)*
?unary: "¬" unary                -> neg
      | "∀" IDENT unary          -> forall
      | "∃" IDENT unary          -> exists
      | atom
      | "(" formula ")"
atom: IDENT "(" term ("," term)* ")"
?term: IDENT "(" term ("," term)* ")"   -> func
     | IDENT                            -> term_ident
IDENT: /[^\W\d]\w*/
%import common.WS
%ignore WS
"""

_KIT_PREDICATE_RE = re.compile(r"[A-Z][a-zA-Z0-9]*\Z")
_KIT_CONSTANT_RE = re.compile(r"[a-z][a-zA-Z0-9]*[a-zA-Z][a-zA-Z0-9]*\Z")
_KIT_VARIABLE_RE = re.compile(r"[a-z][0-9]*\Z")


def _ascii_fold(name: str) -> str:
    """NFKD-transliterate ``name`` to its ASCII-alnum core (``Café``→``Cafe``).

    Raises ``ValueError`` when nothing usable survives — a name with no Latin
    core has no honest ASCII rendering, and inventing one would make the
    recorded mapping unreadable.
    """
    folded = unicodedata.normalize("NFKD", name).encode("ascii", "ignore").decode()
    folded = re.sub(r"[^A-Za-z0-9]", "", folded)
    if not folded or folded[0].isdigit():
        raise ValueError(
            f"willow: identifier {name!r} has no usable ASCII-letter core "
            "to transliterate to — refusing to invent a name.")
    return folded


class _WillowNameConverter:
    """Minimal, injective renaming into kit conventions (see dialect block)."""

    def __init__(self) -> None:
        self.pred_map: Dict[str, str] = {}
        self.term_map: Dict[str, str] = {}
        self._final: Dict[str, Dict[str, str]] = {"predicate": {}, "term": {}}

    def _claim(self, namespace: str, source: str, target: str) -> str:
        owner = self._final[namespace].setdefault(target, source)
        if owner != source:
            raise ValueError(
                f"willow: {namespace} names {owner!r} and {source!r} would "
                f"both end up as {target!r} — the renaming must stay "
                "injective, so this formula cannot be repaired.")
        return target

    def predicate(self, name: str) -> str:
        if _KIT_PREDICATE_RE.match(name):
            return self._claim("predicate", name, name)
        folded = _ascii_fold(name)
        target = folded[0].upper() + folded[1:]
        if not _KIT_PREDICATE_RE.match(target):
            raise ValueError(
                f"willow: predicate {name!r} does not repair to a legal kit "
                f"predicate (got {target!r}).")
        self._claim("predicate", name, target)
        self.pred_map[name] = target
        return target

    def term_name(self, name: str) -> str:
        """A constant or function name (both live in the kit's NAME space)."""
        if _KIT_CONSTANT_RE.match(name) or _KIT_VARIABLE_RE.match(name):
            return name
        folded = _ascii_fold(name)
        target = folded[0].lower() + folded[1:]
        if _KIT_VARIABLE_RE.match(target):
            raise ValueError(
                f"willow: term name {name!r} would repair to {target!r}, "
                "which the kit lexes as a VARIABLE — refusing the silent "
                "semantics change.")
        if not _KIT_CONSTANT_RE.match(target):
            raise ValueError(
                f"willow: term name {name!r} does not repair to a legal kit "
                f"constant (got {target!r}).")
        self._claim("term", name, target)
        self.term_map[name] = target
        return target

    def mapping(self) -> Dict[str, Dict[str, str]]:
        return {"predicates": dict(self.pred_map), "terms": dict(self.term_map)}


class _WillowTransformer(Transformer):
    """Lark tree → kit :class:`~unicode_fol_kit.fol.nodes.Node`."""

    def __init__(self, converter: _WillowNameConverter) -> None:
        super().__init__()
        self._conv = converter

    def term_ident(self, children) -> Node:
        name = str(children[0])
        if _KIT_VARIABLE_RE.match(name):
            return Variable(name)
        return Constant(self._conv.term_name(name))

    def func(self, children) -> Node:
        name = self._conv.term_name(str(children[0]))
        return Function(name, tuple(children[1:]))

    def atom(self, children) -> Node:
        pred = self._conv.predicate(str(children[0]))
        return Atom(pred, tuple(children[1:]))

    def neg(self, children) -> Node:
        return Not(children[0])

    def _binder(self, token) -> Variable:
        name = str(token)
        if not _KIT_VARIABLE_RE.match(name):
            raise ValueError(
                f"willow: quantified variable {name!r} is not a kit variable "
                "token ([a-z][0-9]*) — refusing to rename a BOUND name.")
        return Variable(name)

    def forall(self, children) -> Node:
        return Quantifier("∀", self._binder(children[0]), children[1])

    def exists(self, children) -> Node:
        return Quantifier("∃", self._binder(children[0]), children[1])

    def _fold(self, children, cls) -> Node:
        node = children[0]
        for right in children[1:]:
            node = cls(node, right)
        return node

    def conj(self, children) -> Node:
        return self._fold(children, And)

    def disj(self, children) -> Node:
        return self._fold(children, Or)

    def xor(self, children) -> Node:
        return self._fold(children, Xor)

    def implies(self, children) -> Node:
        if len(children) == 1:
            return children[0]
        return Implies(children[0], children[1])

    def iff(self, children) -> Node:
        return self._fold(children, Iff)


_willow_parser = Lark(_WILLOW_GRAMMAR, parser="lalr")


def repair_willow_formula(text: str) -> Tuple[Node, Dict[str, Dict[str, str]]]:
    """Parse one kit-refused Willow formula with the repair dialect grammar.

    Returns ``(node, mapping)`` — the kit AST (NLTK-precedence reading, names
    repaired into kit conventions) and the changed-names-only mapping. The
    node is guaranteed CLOSED; a free variable raises.

    Raises:
        lark.exceptions.LarkError: ``text`` is outside even the repair
            dialect (genuinely malformed).
        ValueError: an identifier cannot be repaired without a collision or
            a constant→variable semantics change, or the result is not
            closed.
    """
    conv = _WillowNameConverter()
    tree = _willow_parser.parse(text)
    try:
        node = _WillowTransformer(conv).transform(tree)
    except VisitError as exc:
        if isinstance(exc.orig_exc, ValueError):
            raise exc.orig_exc from None
        raise
    free = free_variables(node)
    if free:
        raise ValueError(
            f"willow: repaired formula has free variable(s) {sorted(free)!r} "
            f"— refusing (source: {text!r}).")
    return node, conv.mapping()


def _example_from_record(record: dict, line_no: int,
                         known_bad_ids: FrozenSet[str],
                         convert_fol: bool) -> DatasetExample:
    nl = record.get("NL_sentence")
    fol = record.get("FOL_expression")
    # WillowNLtoFOL has no native id field (see module docstring); some
    # downstream re-export might add one, so honour it opportunistically
    # before falling back to a positional id (same convention as malls.py).
    raw_id = record.get("id")
    example_id = str(raw_id) if raw_id is not None else f"willow:{line_no}"

    meta = {k: v for k, v in record.items()
            if k not in ("NL_sentence", "FOL_expression", "id")}
    meta["line_no"] = line_no

    if convert_fol and fol is not None:
        from ... import api        # lazy: same cost/cycle rationale as _base

        if not api.parse_any(fol).ok:
            try:
                node, mapping = repair_willow_formula(fol)
            except (LarkError, ValueError) as exc:
                # Honest per-example fallback: verbatim string kept, failure
                # recorded — never swallowed, never a crash of the load.
                meta["fol_conversion_error"] = f"{type(exc).__name__}: {exc}"
            else:
                meta["original_fol_conclusion"] = fol
                meta["fol_name_mapping"] = mapping
                fol = node.to_unicode_str()

    return DatasetExample(
        id=example_id,
        nl_premises=(),
        fol_premises=(),
        nl_conclusion=nl,
        fol_conclusion=fol,
        label=None,
        known_bad=example_id in known_bad_ids,
        meta=meta,
    )


def load_willow(path: Union[str, Path], *,
                known_bad_ids: FrozenSet[str] = frozenset(),
                convert_fol: bool = True) -> Iterator[DatasetExample]:
    """Stream :class:`~unicode_fol_kit.eval.datasets.DatasetExample` from a
    local WillowNLtoFOL JSONL file.

    Args:
        path: path to a local ``.jsonl`` file — one
            ``{"NL_sentence": ..., "FOL_expression": ...}`` object per
            non-blank line (see module docstring for converting the upstream
            Hugging Face parquet distribution to this format). NEVER
            downloaded by this function.
        known_bad_ids: ids (the record's own ``"id"`` if present, else the
            positional fallback ``f"willow:{line_no}"``) whose
            ``"FOL_expression"`` translation is known to be broken. Every
            yielded example with a matching id gets ``known_bad=True``.
            Defaults to an empty set.
        convert_fol: with the default ``True``, a formula the kit's own
            grammar already accepts stays byte-for-byte verbatim, and ONLY a
            kit-refused formula goes through the repair dialect grammar
            (NLTK-precedence reading of unparenthesised ∧/∨/⊕ mixes, minimal
            injective renaming of out-of-class identifiers — see the dialect
            comment block); a repaired example records the verbatim original
            in ``meta["original_fol_conclusion"]`` and the changed names in
            ``meta["fol_name_mapping"]``, and a formula neither route can
            read keeps its verbatim string plus
            ``meta["fol_conversion_error"]``. ``False`` restores the raw
            pass-through (~98.8% kit-parse rate, see module docstring).

    Yields:
        One :class:`~unicode_fol_kit.eval.datasets.DatasetExample` per
        non-blank JSONL line, in file order, with ``nl_conclusion``/
        ``fol_conclusion`` set from ``"NL_sentence"``/``"FOL_expression"`` and
        ``nl_premises``/``fol_premises`` empty (see module docstring for why
        this dataset maps onto the "conclusion" slot, matching
        :func:`~unicode_fol_kit.eval.datasets.malls.load_malls`).

    Raises:
        FileNotFoundError: ``path`` does not exist.
        json.JSONDecodeError: a non-blank line is not valid JSON — raised,
            not swallowed (a malformed dataset file must fail loudly).
    """
    path = Path(path)
    with path.open("r", encoding="utf-8") as fh:
        for line_no, raw_line in enumerate(fh):
            line = raw_line.strip()
            if not line:
                continue
            record = json.loads(line)
            yield _example_from_record(record, line_no, known_bad_ids,
                                       convert_fol)
