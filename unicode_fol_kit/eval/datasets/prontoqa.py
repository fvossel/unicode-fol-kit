"""Adapter for the ProntoQA dataset (Logic-LM's GPT-4 DSL rendering of Saparov
& He's PrOntoQA benchmark) -- local JSONL only, no network access.

Source and verified schema
---------------------------
Source: https://huggingface.co/datasets/renma/ProntoQA (unauthenticated;
verified directly via the Hugging Face ``datasets-server`` ``splits``/
``first-rows``/``rows`` APIs, 2026-08-12). Config ``"default"``, and -- unlike
FOLIO -- exactly ONE split, ``"validation"`` (500 rows; verified via
``datasets-server``'s ``info`` endpoint, which also confirms the file behind
it: ``hf://datasets/renma/ProntoQA/ProntoQA_dev_gpt-4.json``). There is no
train/test split to worry about defensively: this dataset has only the one.

That backing filename is not a coincidence: it is the SAME path
(``outputs/logic_programs/ProntoQA_dev_gpt-4.json``) published in the
Logic-LM paper's own repository, https://github.com/teacherpeterpan/Logic-LLM
(fetched 2026-08-12 to cross-check the DSL grammar below against the
REFERENCE solver, ``models/symbolic_solvers/pyke_solver/pyke_solver.py``).
So ``renma/ProntoQA`` is a re-upload of Logic-LM's own GPT-4-generated
symbolic-program outputs for the original PrOntoQA benchmark -- see
"Honesty: raw_logic_programs is LLM output, not ground truth" below for why
that provenance matters to this adapter's correctness guarantees.

Each verified row is a flat JSON object with exactly these keys (confirmed
against real ``rows``-API records):

* ``"id"``                 -- ``str``, e.g. ``"ProntoQA_1"`` (always present
  in every row fetched; this adapter still falls back positionally if a
  record ever lacks it, mirroring :mod:`~unicode_fol_kit.eval.datasets.folio`).
* ``"answer"``              -- ``str``, always ``"A"`` or ``"B"`` in the
  fetched sample, matching ``"options"`` (see below). NOT ``"True"``/
  ``"False"`` text -- kept verbatim as the source's own vocabulary, exactly
  like FOLIO's ``"label"`` values are kept verbatim.
* ``"context"``             -- ``str``, the natural-language story (a single
  paragraph, NOT pre-split into sentences -- there is no verified 1:1
  mapping from an individual English sentence to a single DSL ``Rules:``
  line, so this adapter does not attempt one; it maps the whole paragraph to
  ONE ``nl_premises`` entry).
* ``"question"``            -- ``str``, e.g. ``"Is the following statement
  true or false? Max is sour."``.
* ``"options"``             -- ``list[str]``, always exactly
  ``["A) True", "B) False"]`` in the fetched sample.
* ``"raw_logic_programs"``  -- ``Sequence[str]`` per the HF feature schema;
  every row fetched while building this adapter carried EXACTLY one entry
  (the schema's ``Sequence`` typing is presumably shared with a sibling
  dataset that has more than one, not something ProntoQA itself exercises).
  Each entry is Logic-LM's DSL rendering of the story, LLM-generated (GPT-4)
  from the natural-language ``context`` -- see the grammar below, verified
  against real rows AND against the reference Pyke solver's own parser
  (``Pyke_Program.parse_logic_program``/``parse_forward_rule``/
  ``parse_query`` in ``pyke_solver.py``, cited above).

The Logic-LM DSL grammar (verified against real rows + the reference solver)
------------------------------------------------------------------------------
Four ``\\n\\n``-separated sections, in this fixed order (a fifth,
``"Predicates:"``, always comes first but this adapter IGNORES it entirely --
see below)::

    Predicates:
    Name($x, bool) ::: <english gloss>
    ...

    Facts:
    Predicate(Entity, True|False)
    ...

    Rules:
    Predicate($x, True|False) >>> Predicate($x, True|False)
    ...

    Query:
    Predicate(Entity, True|False)

* ``"Predicates:"`` lines just document a predicate's arity/gloss; VERIFIED
  to sometimes be INCOMPLETE (``ProntoQA_4`` in the validation split lists
  only 7 of the 17 predicate names its own ``Rules:``/``Facts:`` actually
  use -- a real data-quality defect, not a transcription error in this
  docstring). This adapter never reads this section: every predicate it
  needs is discoverable directly from ``Facts:``/``Rules:``/``Query:``.
* ``"Facts:"`` -- one or more GROUND signed literals (every row fetched had
  exactly one). ``Predicate(Entity, True)`` asserts the atom;
  ``Predicate(Entity, False)`` asserts its NEGATION -- the boolean is a
  SIGN, not a third truth value (confirmed by cross-reading ``context``,
  e.g. "Dumpuses are not wooden." renders as
  ``Dumpus($x, True) >>> Wooden($x, False)``).
* ``"Rules:"`` -- universally-quantified, single-variable Horn implications.
  The reference solver's own ``parse_forward_rule`` splits both sides of
  ``>>>`` on ``&&`` for a MULTI-conjunct premise/conclusion (used by its
  ProofWriter rules); ProntoQA rows verified here NEVER use ``&&`` --
  always exactly one premise atom and one conclusion atom per rule -- but
  this adapter still supports ``&&`` generically since it costs nothing and
  keeps faith with the shared DSL grammar. ``$x`` is the only variable
  placeholder ProntoQA rows were ever verified to use.
* ``"Query:"`` -- exactly one line, same ground-literal grammar as
  ``"Facts:"``.

Honesty: ``raw_logic_programs`` is LLM output, not ground truth
------------------------------------------------------------------
Because ``raw_logic_programs`` is a GPT-4 TRANSLATION of ``context`` (not a
hand-verified formalisation -- see the source discussion above), it can be,
and demonstrably sometimes is, internally defective in ways that are
INVISIBLE from ``answer`` alone. This was checked empirically: forward-
chaining ``Facts:``+``Rules:`` and comparing the derived value for the
``Query:`` predicate/subject against the ``Query:``'s own stated boolean --
exactly what the reference solver's ``answer_map_prontoqa`` computes (see
:func:`solve_example`) -- reproduces the gold ``answer`` on only 76 of a
100-row sample fetched from ``validation`` (row indices 0-99). The 24
mismatches split into two concretely identified classes:

1. A genuinely BROKEN derivation chain caused by an inconsistent predicate
   name inside ``raw_logic_programs`` itself. E.g. ``ProntoQA_19``'s
   ``Rules:`` mix ``"Wumpus"``/``"Wumpuses"`` and
   ``"Tumpus"``/``"Tumpuses"``/``"Zumpus"``/``"Zumpuses"`` -- different
   strings, so the chain the story clearly intends never actually connects,
   and forward-chaining (both this adapter's, via :func:`solve_example`, and
   presumably the reference Pyke solver's) derives NOTHING for the ``Query``
   predicate.
2. Rows where the chain IS clean (no naming defect, single unambiguous
   derivation) yet the derived value still does not match ``answer`` under
   the reference formula. E.g. ``ProntoQA_1``: ``Query: Sour(Max, False)``;
   forward-chaining ``Facts:``+``Rules:`` cleanly derives ``Sour(Max,
   False)`` too (via ``Tumpus($x, True) >>> Sour($x, False)``, and
   ``Tumpus(Max, True)`` is itself the unique derived value along the
   chain from the sole fact ``Yumpus(Max, True)``) -- so the reference
   formula predicts ``'A'``, but the gold ``answer`` is ``'B'``. This
   adapter does not know why (the original PrOntoQA generator and the exact
   Logic-LM GPT-4 prompting/parsing script were not inspected further to
   find out) and does NOT paper over it: :func:`solve_example` computes the
   reference formula honestly and can legitimately disagree with ``answer``
   on rows like this one.

Practical upshot: :func:`solve_example` is faithful to what
``raw_logic_programs`` literally entails -- it is NOT a guaranteed
reproducer of every gold ``answer`` in the full validation split. The
fixture shipped with this adapter (``tests/fixtures/prontoqa_mini.jsonl``)
was deliberately curated to 8 REAL rows (ids ProntoQA_4/9/18/22/31/39/45/52)
free of both defect classes above, so :func:`solve_example` DOES reproduce
``answer`` on every fixture row (see its own docstring for one fully
worked by hand).

This dataset does NOT have (being explicit, per this subpackage's honesty
rule)
------------------------------------------------------------------------
* No FOL annotation at all: nothing in ``raw_logic_programs`` is a string
  this kit's ``parse_any`` can parse (it is Logic-LM's own bracket DSL, not
  this kit's unicode/TPTP/Prover9 surface syntax). Accordingly
  ``fol_premises`` is ALWAYS ``()`` and ``fol_conclusion`` is ALWAYS
  ``None`` on every :class:`~unicode_fol_kit.eval.datasets.DatasetExample`
  this adapter yields -- the DSL text is preserved verbatim, unparsed, in
  ``meta["raw_logic_programs"]`` instead. A consequence:
  :func:`~unicode_fol_kit.eval.datasets.audit_examples` run over
  :func:`load_prontoqa`'s output is VACUOUSLY ``ok=True`` for every example
  (nothing in ``fol_premises``/``fol_conclusion`` to fail parsing or
  ``check()``) -- it finds no defects here by construction, not because the
  data has none (see the section above for where ProntoQA's real defects
  actually live: inside the LLM-generated DSL, which ``audit_examples``
  never looks at).
* No multi-hop branching or multi-entity relations: every ``Rules:`` line
  is unary (single ``$x``), every predicate application has exactly one
  argument, and every row verified here reasons about exactly one entity.
* Closed-world / deductively-complete WHEN THE DSL IS CLEAN: for a row
  without the naming defect described above, forward-chaining derives
  EXACTLY one signed literal for the ``Query``'s (predicate, subject) pair
  -- either the ``Query`` itself or its negation, never neither and never
  both. This is what lets :func:`solve_example` treat "not provable" and
  "negation provable" as the two exhaustive, mutually exclusive outcomes
  for a well-formed row (see its docstring) -- it is NOT a property this
  adapter can guarantee for an arbitrary row, only something verified to
  hold for the fixture.

License: **MIT**, per the Hugging Face repo's ``cardData.license`` field and
its ``license:mit`` tag (https://huggingface.co/api/datasets/renma/ProntoQA,
verified directly 2026-08-12). This loader only reads a LOCAL file the
caller already obtained; it never downloads or redistributes ProntoQA data.

This module never downloads anything -- obtain the JSONL file yourself from
the source above and pass its local path to :func:`load_prontoqa`.
"""

import re
from pathlib import Path
from typing import FrozenSet, Iterator, List, Sequence, Tuple, Union

from ._base import DatasetExample, _register_dataset_info
from ...fol.nodes import Node, Atom, Not, And, Implies, Quantifier, Variable, Constant
from ...atp.protocol import PROVED

__all__ = ["load_prontoqa", "parse_logic_program", "solve_example"]

_register_dataset_info(
    "prontoqa",
    license="MIT",
    source_url="https://huggingface.co/datasets/renma/ProntoQA",
    citation_hint=(
        "Saparov, Abulhair, and He He. \"Language Models Are Greedy Reasoners: "
        "A Systematic Formal Analysis of Chain-of-Thought.\" arXiv:2210.01240 "
        "(the original PrOntoQA benchmark). DSL renderings (raw_logic_programs) "
        "from Pan, Liangming, et al. \"Logic-LM: Empowering Large Language "
        "Models with Symbolic Solvers for Faithful Logical Reasoning.\" "
        "Findings of EMNLP 2023, arXiv:2305.12295 "
        "(https://github.com/teacherpeterpan/Logic-LLM)."
    ),
)


# ---------------------------------------------------------------------------
# load_prontoqa -- JSONL -> DatasetExample
# ---------------------------------------------------------------------------

def _resolve_id(record: dict, line_no: int) -> str:
    """The record's own ``"id"`` if present, else a positional fallback.

    Every row verified while building this adapter carried a native ``"id"``
    (e.g. ``"ProntoQA_1"``); the fallback mirrors
    :func:`~unicode_fol_kit.eval.datasets.folio._resolve_id` for a record
    that, contrary to everything observed, lacks one.
    """
    value = record.get("id")
    if value is not None:
        return str(value)
    return f"prontoqa:{line_no}"


def _example_from_record(record: dict, line_no: int,
                         known_bad_ids: FrozenSet[str]) -> DatasetExample:
    context = record.get("context")
    question = record.get("question")
    answer = record.get("answer")
    example_id = _resolve_id(record, line_no)

    meta = {k: v for k, v in record.items()
            if k not in ("id", "context", "question", "answer")}
    if meta.get("options") is not None:
        meta["options"] = tuple(meta["options"])
    if meta.get("raw_logic_programs") is not None:
        meta["raw_logic_programs"] = tuple(meta["raw_logic_programs"])
    meta["line_no"] = line_no

    return DatasetExample(
        id=example_id,
        nl_premises=(context,) if context is not None else (),
        fol_premises=(),                # see module docstring: DSL != FOL text
        nl_conclusion=question,
        fol_conclusion=None,            # see module docstring: DSL != FOL text
        label=answer,                   # kept verbatim ("A"/"B"), not translated
        known_bad=example_id in known_bad_ids,
        meta=meta,
    )


def load_prontoqa(path: Union[str, Path], *,
                  known_bad_ids: FrozenSet[str] = frozenset()) -> Iterator[DatasetExample]:
    """Stream :class:`~unicode_fol_kit.eval.datasets.DatasetExample` from a
    local ProntoQA (renma/ProntoQA, ``validation`` split) JSONL file.

    Args:
        path: path to a local ``.jsonl`` file in the verified schema (see
            module docstring) -- one JSON object per non-blank line. NEVER
            downloaded by this function; obtain the file from
            https://huggingface.co/datasets/renma/ProntoQA yourself.
        known_bad_ids: ids (the record's own ``"id"``, e.g. ``"ProntoQA_1"``,
            or the positional fallback ``f"prontoqa:{line_no}"``) whose
            ``raw_logic_programs``/``answer`` pairing is known to be
            unreliable (e.g. an :func:`~unicode_fol_kit.eval.datasets.prontoqa.solve_example`
            mismatch a caller has reviewed and wants flagged). Every yielded
            example with a matching id gets ``known_bad=True``. Defaults to
            an empty set.

    Yields:
        One :class:`~unicode_fol_kit.eval.datasets.DatasetExample` per
        non-blank JSONL line, in file order. ``fol_premises`` is always
        ``()`` and ``fol_conclusion`` is always ``None`` (see module
        docstring); the DSL text lives, verbatim and unparsed, in
        ``meta["raw_logic_programs"]``.

    Raises:
        FileNotFoundError: ``path`` does not exist.
        json.JSONDecodeError: a non-blank line is not valid JSON -- this is
            NOT swallowed; a malformed dataset file is a loud failure, not a
            silently-skipped row (matches
            :func:`~unicode_fol_kit.eval.datasets.folio.load_folio` /
            :func:`~unicode_fol_kit.eval.datasets.malls.load_malls`).
    """
    import json                       # local: mirrors folio.py/malls.py's own style

    path = Path(path)
    with path.open("r", encoding="utf-8") as fh:
        for line_no, raw_line in enumerate(fh):
            line = raw_line.strip()
            if not line:
                continue
            record = json.loads(line)
            yield _example_from_record(record, line_no, known_bad_ids)


# ---------------------------------------------------------------------------
# parse_logic_program -- the DSL -> kit-AST converter
# ---------------------------------------------------------------------------

_FORALL = "∀"                    # matches unicode_fol_kit.fol.modal_translation._FORALL

# A DSL atom: PredicateName(arg, True|False) -- arg is either a bare entity
# name (Facts:/Query:) or a "$x"-style variable placeholder (Rules:).
_ATOM_RE = re.compile(
    r'^(?P<pred>[A-Za-z_][A-Za-z0-9_]*)\(\s*(?P<arg>[^,()]+?)\s*,\s*(?P<val>True|False)\s*\)$'
)

# The kit's own grammar (unicode_fol_kit/fol/grammars/terminals.lark), used here only
# to decide whether a DSL name is ALREADY a legal kit token or needs the documented
# fallback: PREDICATE = [A-Z][a-zA-Z0-9]*; a bare NAME constant = lowercase, >=2 letters.
_LEGAL_PREDICATE_RE = re.compile(r'^[A-Z][a-zA-Z0-9]*$')
_LEGAL_CONSTANT_RE = re.compile(r'^[a-z][a-zA-Z0-9]*[a-zA-Z][a-zA-Z0-9]*$')

_SECTION_MARKERS = ("Facts:", "Rules:", "Query:")


def _alnum(s: str) -> str:
    return "".join(ch for ch in s if ch.isalnum())


def _sanitize_predicate(name: str) -> str:
    """DSL predicate names are already legal kit PREDICATE tokens
    (``[A-Z][a-zA-Z0-9]*``) in every row this adapter was verified against --
    this is a defensive fallback (force-capitalise, strip non-alnum) for
    anything that is not, never exercised by the shipped fixture."""
    if _LEGAL_PREDICATE_RE.match(name):
        return name
    base = _alnum(name) or "P"
    if not base[0].isalpha():
        base = "P" + base
    return base[0].upper() + base[1:]


def _sanitize_constant(name: str) -> str:
    """Lowercase the DSL's bare entity name into the kit's plain multi-letter
    NAME constant token: ``'Max' -> 'max'`` -- the convention this adapter
    follows throughout (see module docstring), verified to succeed for every
    entity name in the rows this adapter was built against (Max, Stella,
    Wren, Alex, Fae, Sam, Sally, Rex, Polly, ...). Falls back to the kit's
    explicit ``c_``-prefixed CONSTANT form for anything that would not
    lowercase into a legal >=2-letter NAME (e.g. a single-letter entity
    name) -- never exercised by the shipped fixture."""
    lowered = name[:1].lower() + name[1:] if name else name
    if _LEGAL_CONSTANT_RE.match(lowered):
        return lowered
    return "c_" + (_alnum(name) or "0")


def _nonblank_lines(text: str) -> List[str]:
    return [line.strip() for line in text.splitlines() if line.strip()]


def _split_sections(program: str) -> Tuple[str, str, str]:
    """Split ``program`` into (Facts text, Rules text, Query text).

    The leading ``"Predicates:"`` section (and anything else before
    ``"Facts:"``) is discarded -- see module docstring for why this adapter
    never reads it. Raises a clear ``ValueError`` naming the first missing
    marker rather than an opaque ``ValueError: not enough values to unpack``.
    """
    remainder = program
    sections: List[str] = []
    for marker in _SECTION_MARKERS:
        pieces = remainder.split(marker, 1)
        if len(pieces) != 2:
            raise ValueError(
                f"parse_logic_program: missing {marker!r} section marker "
                f"(expected 'Predicates:'/'Facts:'/'Rules:'/'Query:' sections "
                f"in that order); program started with: {program[:120]!r}")
        before, remainder = pieces
        sections.append(before)
    # sections[0] is the (discarded) Predicates section; sections[1]/[2] are
    # the Facts/Rules text; `remainder` is everything after 'Query:'.
    return sections[1], sections[2], remainder


def _parse_ground_literal(line: str) -> Tuple[Node, bool]:
    """Parse one ``Facts:``/``Query:`` line: ``Predicate(Entity, True|False)``.

    Returns ``(node, polarity)`` where ``node`` is ``Atom(...)`` (polarity
    True) or ``Not(Atom(...))`` (polarity False) and ``polarity`` is the raw
    parsed boolean, returned separately for callers that want it without
    re-inspecting the node (see :func:`parse_logic_program`).
    """
    m = _ATOM_RE.match(line)
    if not m:
        raise ValueError(f"parse_logic_program: cannot parse fact/query line: {line!r}")
    arg = m.group("arg").strip()
    if arg.startswith("$"):
        raise ValueError(
            f"parse_logic_program: expected a ground constant in a Facts:/"
            f"Query: line, found a Rules:-style variable placeholder {arg!r}: "
            f"{line!r}")
    predicate = _sanitize_predicate(m.group("pred"))
    atom = Atom(predicate, (Constant(_sanitize_constant(arg)),))
    polarity = m.group("val") == "True"
    return (atom if polarity else Not(atom)), polarity


_RULE_VARIABLE = Variable("x")


def _parse_rule_literal(chunk: str) -> Node:
    """Parse one ``&&``-conjunct of a ``Rules:`` line's premise/conclusion:
    ``Predicate($x, True|False)``. Only ``$x`` is a verified placeholder for
    ProntoQA (see module docstring); any other name raises rather than
    silently mis-binding it to the wrong (or a fresh) variable."""
    m = _ATOM_RE.match(chunk.strip())
    if not m:
        raise ValueError(f"parse_logic_program: cannot parse rule literal: {chunk!r}")
    arg = m.group("arg").strip()
    if arg != "$x":
        raise ValueError(
            f"parse_logic_program: unsupported rule variable {arg!r} -- every "
            f"renma/ProntoQA rule verified while building this adapter used "
            f"only '$x' as its single bound variable: {chunk!r}")
    predicate = _sanitize_predicate(m.group("pred"))
    atom = Atom(predicate, (_RULE_VARIABLE,))
    return atom if m.group("val") == "True" else Not(atom)


def _conjoin(nodes: Sequence[Node]) -> Node:
    result = nodes[0]
    for n in nodes[1:]:
        result = And(result, n)
    return result


def _parse_rule(line: str) -> Node:
    """``Pred1($x, V1) [&& Pred2($x, V2) ...] >>> Pred3($x, V3) [&& ...]``
    becomes ``∀x ( premise-conjunction(x) → conclusion-conjunction(x) )``.
    ``&&`` on either side is supported per the shared Logic-LM DSL grammar
    (see :mod:`unicode_fol_kit.eval.datasets.prontoqa`'s module docstring)
    though never observed in a verified ProntoQA row (only ever one premise,
    one conclusion)."""
    if ">>>" not in line:
        raise ValueError(f"parse_logic_program: rule line has no '>>>': {line!r}")
    premise_text, conclusion_text = line.split(">>>", 1)
    premises = [_parse_rule_literal(c) for c in premise_text.split("&&")]
    conclusions = [_parse_rule_literal(c) for c in conclusion_text.split("&&")]
    body = Implies(_conjoin(premises), _conjoin(conclusions))
    return Quantifier(_FORALL, _RULE_VARIABLE, body)


def parse_logic_program(program: str) -> Tuple[List[Node], Node, bool]:
    """Convert one ``raw_logic_programs`` DSL string into kit AST nodes.

    Args:
        program: one entry of ``example.meta["raw_logic_programs"]`` (the
            full ``"Predicates:\\n...\\n\\nFacts:\\n...\\n\\nRules:\\n...\\n\\n
            Query:\\n..."`` text -- see module docstring for the grammar).

    Returns:
        ``(premises, query, query_polarity)`` where:

        * ``premises`` is every ``Facts:`` ground literal followed by every
          ``Rules:`` implication, as kit :class:`~unicode_fol_kit.fol.nodes.Node`
          objects, in source order.
        * ``query`` is the ``Query:`` line's literal, AS STATED (its own
          sign included) -- e.g. ``Sour(Max, False)`` becomes
          ``Not(Atom("Sour", (Constant("max"),)))``, not the bare positive
          atom.
        * ``query_polarity`` is the raw parsed boolean from the ``Query:``
          line (``True`` for ``Sour(Max, True)``, ``False`` for
          ``Sour(Max, False)``), returned separately for convenience -- it
          is exactly ``isinstance(query, Atom)`` restated as a bool, kept as
          its own return value so a caller need not pattern-match the node.

    Raises:
        ValueError: a section marker is missing, a ``Facts:``/``Rules:``/
            ``Query:`` line does not match the DSL atom grammar, a
            ``Facts:``/``Query:`` line uses a ``$``-variable instead of a
            ground constant, a ``Rules:`` line has no ``>>>``, a ``Rules:``
            line uses a bound variable other than ``$x``, or the ``Query:``
            section does not have exactly one line. Every case names the
            offending text -- never a silent skip or a best-effort guess.

    Naming convention (see module docstring for the full rationale):
    predicates are used verbatim (already legal kit ``PREDICATE`` tokens in
    every verified row); entity names are lowercased into the kit's bare
    ``NAME`` constant token (``"Max"`` -> ``"max"``); the DSL's ``$x`` becomes
    the kit variable ``x``.
    """
    facts_text, rules_text, query_text = _split_sections(program)
    facts = [_parse_ground_literal(line)[0] for line in _nonblank_lines(facts_text)]
    rules = [_parse_rule(line) for line in _nonblank_lines(rules_text)]

    query_lines = _nonblank_lines(query_text)
    if len(query_lines) != 1:
        raise ValueError(
            f"parse_logic_program: expected exactly one Query: line, got "
            f"{len(query_lines)}: {query_lines!r}")
    query, query_polarity = _parse_ground_literal(query_lines[0])

    return facts + rules, query, query_polarity


# ---------------------------------------------------------------------------
# solve_example -- end to end via unicode_fol_kit.api.prove
# ---------------------------------------------------------------------------

def solve_example(example: DatasetExample, *, on_indefinite: str = "label",
                  **prove_kwargs) -> dict:
    """Decide one ProntoQA example end to end: DSL -> AST -> :func:`unicode_fol_kit.api.prove`.

    Parses ``example.meta["raw_logic_programs"][0]`` via
    :func:`parse_logic_program`, then asks
    :func:`unicode_fol_kit.api.prove` whether ``premises`` entail the
    ``query`` literal EXACTLY as the DSL states it (sign included -- see
    :func:`parse_logic_program`'s docstring). A row whose DSL is clean (see
    module docstring's "does NOT have" section) is deductively closed: EITHER
    the query or its negation is a classical consequence of ``premises``
    (these are plain universally-quantified single-variable Horn
    implications chained from one ground fact -- ordinary Modus Ponens,
    nothing closed-world/non-classical about it), so ``PROVED``/``REFUTED``
    are the two outcomes actually seen on the fixture. A row whose DSL has
    the naming defect documented in the module docstring can legitimately
    come back ``UNKNOWN`` instead (neither polarity is a consequence) --
    this function does NOT guess in that case, it reports ``predicted=None``.

    Worked example (``ProntoQA_45`` from the fixture, hand-verified):
    ``Facts: Dumpus(Fae, True)``. Chase the ``Rules:`` from that single
    fact: ``Dumpus->Numpus->Zumpus->Wumpus->Impus``, and
    ``Impus($x, True) >>> Wooden($x, True)`` fires, giving the unique
    derived literal ``Wooden(Fae, True)`` (the OTHER ``Wooden`` rule,
    ``Tumpus($x, True) >>> Wooden($x, False)``, never fires -- Fae is never
    derived to be a Tumpus). ``Query: Wooden(Fae, True)`` is EXACTLY that
    derived literal, so ``premises ⊨ query`` classically (a straight
    Modus Ponens chain) -- ``api.prove`` returns ``PROVED``, this function
    maps that to ``predicted="A"``, and the fixture's gold ``answer`` for
    ``ProntoQA_45`` is indeed ``"A"``.

    Args:
        example: a :class:`~unicode_fol_kit.eval.datasets.DatasetExample`
            from :func:`load_prontoqa`.
        **prove_kwargs: forwarded verbatim to
            :func:`unicode_fol_kit.api.prove` (e.g. ``backends=[...]``,
            ``timeout=...``); with none given, ``prove`` uses its own
            default chain, which is what the fixture was validated against.

    Returns:
        ``{"predicted": "A" | "B" | None, "query_polarity": bool,
        "verdict": Verdict.to_dict(), "verdict_negated": ... | None}``.
        ``predicted`` is ``"A"`` when ``premises ⊨ query`` is PROVED, ``"B"``
        when ``premises ⊨ ¬query`` is PROVED (a SECOND prove call — a mere
        REFUTED on the first call only witnesses that the entailment fails,
        which is NOT a proof of the negation and is never coerced into
        ``"B"``), and ``None`` when neither direction closes
        (``UNKNOWN``/``ERROR``/broken derivation chains -- never coerced
        into a guess). ``verdict_negated`` carries the second call's verdict
        dict, or ``None`` when the first call already settled it.
        ``query_polarity`` is :func:`parse_logic_program`'s third return
        value, included so a caller can see the DSL's stated sign without
        re-parsing.

        ``on_indefinite``: ProntoQA has only the two labels A/B, so a
        neither-proved outcome is ALWAYS ``predicted=None`` — under
        ``"label"`` (default) and ``"abstain"`` alike (they coincide here,
        unlike in the three-label ProverQA/ProofWriter solvers).
        ``"raise"`` additionally raises ``ValueError`` when a leg is
        INDEFINITE (prover ``unknown``/``error`` — timeout, bound); it does
        NOT raise when both directions are definitively REFUTED, since
        "provably neither entailed" is an established (if unlabelable)
        answer, not a prover failure.

    Raises:
        ValueError: ``example.meta["raw_logic_programs"]`` is missing, empty,
            or has more than one entry (every row verified while building
            this adapter carried exactly one -- see module docstring); or
            :func:`parse_logic_program` itself raises on malformed DSL text.
    """
    if on_indefinite not in ("label", "abstain", "raise"):
        raise ValueError(
            f"solve_example: on_indefinite must be 'label', 'abstain' or "
            f"'raise', got {on_indefinite!r}")
    programs = example.meta.get("raw_logic_programs") or ()
    if len(programs) != 1:
        raise ValueError(
            f"solve_example: expected exactly one raw_logic_programs entry "
            f"for {example.id!r}, got {len(programs)} (every renma/ProntoQA "
            f"validation row inspected while building this adapter carried "
            f"exactly one)")

    premises, query, query_polarity = parse_logic_program(programs[0])

    from ... import api               # lazy: avoid import-time cost/cycles

    verdict = api.prove(query, premises, **prove_kwargs)
    if verdict.status == PROVED:
        return {
            "predicted": "A",
            "query_polarity": query_polarity,
            "verdict": verdict.to_dict(),
            "verdict_negated": None,
        }
    # A REFUTED here only witnesses that premises ⊨ query FAILS (a
    # countermodel to the entailment exists) — it is not a proof of the
    # negation. "B" requires actually PROVING premises ⊨ ¬query.
    negated = api.prove(Not(query), premises, **prove_kwargs)
    if (negated.status != PROVED and on_indefinite == "raise"
            and not (verdict.status == "refuted"
                     and negated.status == "refuted")):
        raise ValueError(
            f"solve_example: example {example.id}: indefinite prover outcome "
            f"(query: {verdict.status}/{verdict.reason}, negated: "
            f"{negated.status}/{negated.reason}) with on_indefinite='raise'.")
    return {
        "predicted": "B" if negated.status == PROVED else None,
        "query_polarity": query_polarity,
        "verdict": verdict.to_dict(),
        "verdict_negated": negated.to_dict(),
    }
