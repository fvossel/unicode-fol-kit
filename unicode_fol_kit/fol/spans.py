"""Source-span tracking for :meth:`MSFLParser.parse_with_spans`.

WHY THIS IS A SIDE TABLE, NOT A NODE FIELD
-------------------------------------------
Every AST node (``_fol_nodes.py`` and the sibling ``_*_nodes.py`` modules) is a
frozen dataclass with structural equality and hashing: dedup, ``canonical_key``
caches, sets of nodes, the harvest cache in ``semantics/model_eval.py``, and
every test that compares a parsed formula to a hand-built one all depend on
that. A span FIELD would make two structurally identical formulas parsed from
different source text compare unequal and hash apart — so spans live in a
side table, never on the node itself.

WHY THE TABLE IS KEYED BY PATH, NOT BY id() (AND NOT BY THE NODE ITSELF)
--------------------------------------------------------------------------
Two occurrences of the SAME subformula are structurally equal and hash
together (``P(x)`` in ``P(x) ∧ P(x)``), so keying by node value/equality would
silently merge their two different spans into one entry — wrong by
construction. Keying by ``id()`` looks like the fix (two equal-but-distinct
objects have distinct ids) but is unstable: ``MSFLParser.parse`` runs
:func:`~unicode_fol_kit.fol._msfl_nodes.resolve_lambda_scope` (and, in modal
mode, :func:`~unicode_fol_kit.fol._modal_nodes.resolve_agent_variables`)
AFTER the Lark transform, and BOTH passes rebuild every node they touch —
:meth:`Node.map_children` always constructs a fresh ``type(self)(**new_kwargs)``,
and ``dataclasses.replace`` likewise — even when NOTHING about that node
actually changed (verified: for a lambda-free classical formula,
``resolve_lambda_scope`` still rebuilds every node top to bottom, it just
never changes any field). So the id() a node had during transform is gone by
the time ``parse()`` returns, and an id()-keyed table built during transform
cannot be looked up against the AST the caller actually holds.

The fix is a key that names a node by its STRUCTURAL POSITION in the tree
rather than by its identity or its value: a :data:`Path` — a tuple of child
indices from the root, using the SAME deterministic child order the
traversal API (:func:`traverse`), lookup, and :func:`replace_at` all agree
on (see "PATH CONVENTION" below). A path is stable across any REBUILD that
preserves tree shape (same node type, same number and order of children at
every level) even when it changes VALUES — which is exactly what
``resolve_lambda_scope``/``resolve_agent_variables`` do for the classical FOL
fragment (no lambda in the input ⇒ shape is always preserved, only object
identity changes) and for :mod:`unicode_fol_kit.chem.interop`'s renaming
rewrite (only an ``Atom.predicate``/``Function.name`` string changes).
:func:`project_spans` carries a path-keyed table across a rewrite explicitly,
by walking the OLD and NEW trees in lockstep; see its docstring for the one
case that is a genuine reshaping (a higher-order lambda application rewritten
into a fresh ``Application``/``LambdaVar`` chain) and how that is reported as
:data:`UNKNOWN` rather than mis-mapped.

PATH CONVENTION
----------------
A :data:`Path` is a ``Tuple[int, ...]``; the empty tuple ``()`` addresses the
root itself. Given a node, its PATH CHILDREN — the sequence a path index 0,
1, 2, … selects into — are:

* For every node EXCEPT :class:`~unicode_fol_kit.fol._fol_nodes.Quantifier`:
  exactly :meth:`Node._child_nodes` — i.e. every dataclass field that is a
  ``Node`` (in field-declaration order), with a ``Node``-list/tuple field
  contributing its elements in order. This is the SAME child view
  ``map_children``/``walk`` already use, so path indices for an ordinary
  formula node line up with "the child at position N" the way any other
  traversal over this AST already means it.
* For a ``Quantifier``: path child 0 is its ``formula`` (the matrix) and
  ONLY that — the bound ``variable`` is deliberately NOT a path child (see
  "WHY THE BOUND VARIABLE IS EXCLUDED" below). ``∀x P(x)`` therefore has
  exactly one path child, at index 0: ``P(x)``.

This SAME rule (``_fol_nodes._path_children`` — living next to ``Node`` and
``Quantifier`` themselves, alongside ``node_at``/``replace_at``, and
re-exported from this module) is what :func:`traverse`,
:func:`node_at`, :func:`replace_at`, and :func:`project_spans` all call, so a
path produced by one of them is always valid input to any of the others, on
the same tree — that agreement is the whole point of making paths opaque,
kit-issued values (never hand-constructed by a caller against some OTHER
child-ordering assumption). ``replace_at`` predates this module (see its own
docstring in ``_fol_nodes.py``) and was originally built against the WIDER
``_child_nodes()`` view, flagging the Quantifier exclusion as an open
reconciliation; that reconciliation is what fixed both functions to the one
rule described here.

WHY THE BOUND VARIABLE IS EXCLUDED FROM QUANTIFIER'S PATH CHILDREN
-----------------------------------------------------------------------
A quantifier's HEAD span (see "TWO SPANS PER NODE" below) already covers the
symbol AND the bound variable together (``"∀ x"``), so the variable's source
text is already accounted for by its binder's head — exposing it AGAIN as a
separately addressable path child would double-count that occurrence and
give it two different "correct" spans (the identifier text sitting inside
the parent's head span, and its own leaf span) with no principled way to
prefer one. A term occurring in ARGUMENT position (an ``Atom``/``Function``
argument) is NOT covered by any enclosing head, so it stays a normal,
separately path-addressable child with its own leaf span — the exclusion is
specific to a BINDER's own bound-variable field, not to variables in general.
(Other binder node types — ``Count``, ``Cardinality``, ``SortedQuantifier``,
``Lambda``, … — are outside this change's target fragment and are left on
the default, unexcluded child view; see the module docstring of
``msflparser.py``'s span-capturing transform for the full list of what this
change does and does not cover.)

TWO SPANS PER NODE: EXTENT AND HEAD
--------------------------------------
:class:`NodeSpans` bundles both:

* ``extent`` — the minimal span covering the node's own tokens. Redundant
  OUTER parentheses are never part of it: Lark's grammar wraps a formula in
  parentheses via an UN-aliased, ``?``-prefixed alternative
  (``?prefix: … | "(" formula ")"``) that Lark auto-inlines away whenever it
  reduces to a single child, so the position Lark actually reports for the
  inner node's own rule (via ``propagate_positions``) already excludes any
  number of wrapping parens — ``((P(x)))`` reports the same extent as
  ``P(x)`` (verified; see msflparser.py's span-capturing transform, and
  ``tests/test_spans.py``).
* ``head`` — the head-TOKEN occurrence: a quantifier's symbol together with
  its bound variable INCLUDING the whitespace between them (``"∀ x"``), a
  negation sign, a binary connective's own occurrence, an atom's predicate
  name (or its infix comparison symbol), a function's name. A leaf TERM node
  (``Variable``/``Constant``/``Number``) has ``head == extent`` — it IS its
  own single token.

Either field individually may be :data:`UNKNOWN` — see "UNKNOWN" below.

UNKNOWN
--------
:data:`UNKNOWN` is an explicit, documented sentinel for "this span could not
be recovered" — never a guessed or interpolated stand-in, and never silently
absent (:meth:`SpanMap.get` always returns a :class:`NodeSpans`, defaulting
individual fields to ``UNKNOWN`` rather than raising or omitting the entry).
For the pure classical FOL fragment (∀ ∃ ¬ ∧ ∨ → ↔ ⊕, predicates over
constants/variables/function terms) both fields are recovered EXACTLY for
every node reachable via :func:`traverse` — see ``tests/test_spans.py`` and
the FOLIO-corpus test for the zero-``UNKNOWN`` claim. Outside that fragment
(modal/temporal/epistemic operators, lambda, second-order, counting/
cardinality binders, sorted quantifiers, …) ``head`` may legitimately be
``UNKNOWN`` — those operators are out of this change's target scope; two
narrow, specific, already-documented gaps besides:

* An agent prefix (``K_a``, ``B_a``, …) is lexed as a SINGLE combined token
  (the agent name is sliced out of it inside a handler, never its own
  token), so the agent sub-node has no token of its own — its ``Knows``/
  ``Believes``/… PARENT node's own span is unaffected.
* A higher-order lambda application is rewritten, post-parse, into a fresh
  ``Application``/``LambdaVar`` chain the original grammar never produced —
  see :func:`project_spans`.
"""

from dataclasses import dataclass
from typing import Dict, Iterator, List, Tuple

from ._fol_nodes import Node, _path_children, node_at, replace_at  # noqa: F401 (node_at, replace_at re-exported)


# =========================
# Span / UNKNOWN
# =========================

@dataclass(frozen=True)
class Span:
    """A slice of the ORIGINAL source text that one AST node (or one node's
    head token) was parsed from.

    ``start``/``end`` are character offsets into the source string, in Python
    slice convention (``text[start:end] == span.text``) — and, because a
    Python ``str`` already indexes by Unicode CODEPOINT (not UTF-16 unit or
    byte), these offsets are codepoint indices with no further conversion
    needed, satisfied by construction rather than by extra bookkeeping.
    ``line``/``column`` and ``end_line``/``end_column`` are 1-based, matching
    Lark's own ``Meta``/``Token`` convention: ``column`` is the 1-based
    offset of ``start`` within ``line``; ``end_column`` is one past the last
    character on ``end_line``. ``text`` is the exact slice, so a caller can
    quote the source directly without re-slicing by hand (and risking an
    off-by-one).
    """

    start: int
    end: int
    line: int
    column: int
    end_line: int
    end_column: int
    text: str


def _unknown_singleton():
    """``__reduce__`` target for :data:`UNKNOWN` — always returns the one
    module-level instance, so pickling (including across a process boundary,
    e.g. a ``ProcessPoolExecutor`` worker) reconstructs the SAME sentinel
    rather than depending on ``_UnknownSpan.__new__``'s caching to line up
    with pickle's own object-construction protocol."""
    return UNKNOWN


class _UnknownSpan:
    """Sentinel: a span could not be recovered (see module docstring).

    Falsy and distinct from every real :class:`Span`, so callers can write
    ``if span:`` or ``if span is UNKNOWN:`` — never a guessed or interpolated
    stand-in span.
    """

    _instance = None

    def __new__(cls):
        if cls._instance is None:
            cls._instance = super().__new__(cls)
        return cls._instance

    def __repr__(self) -> str:
        return "UNKNOWN"

    def __bool__(self) -> bool:
        return False

    def __reduce__(self):
        return (_unknown_singleton, ())


UNKNOWN = _UnknownSpan()


@dataclass(frozen=True)
class NodeSpans:
    """The two spans recorded for one AST node occurrence: see the module
    docstring's "TWO SPANS PER NODE". Either field may independently be
    :data:`UNKNOWN`."""

    extent: object  # Span or UNKNOWN
    head: object    # Span or UNKNOWN


_UNKNOWN_NODE_SPANS = NodeSpans(UNKNOWN, UNKNOWN)


# =========================
# Path convention: traversal, lookup, replace_at all agree on this
# =========================

#: A path from a tree's root to one of its nodes: a tuple of child indices,
#: ``()`` addressing the root itself. See the module docstring's "PATH
#: CONVENTION". Opaque — always produced by :func:`traverse` or accepted back
#: by :func:`node_at`/:func:`replace_at`/:meth:`SpanMap.get`, never
#: hand-built by a caller against some other assumption about child order.
Path = Tuple[int, ...]


def traverse(root: Node) -> Iterator[Tuple[Path, Node]]:
    """Yield ``(path, node)`` for every node in ``root``'s tree, pre-order.

    This is the documented traversal API: it covers every node reachable via
    :func:`_path_children` — every formula node AND every term node (a
    variable/constant/number, and a function/atom argument in general) — but,
    for a :class:`Quantifier`, NOT its bound variable a second time (see the
    module docstring). A :class:`SpanMap` built by
    :meth:`MSFLParser.parse_with_spans` is populated by exactly this walk, so
    ``spans.get(path)`` for any ``path`` this function yields is meaningful.
    """
    def _walk(node: Node, path: Path) -> Iterator[Tuple[Path, Node]]:
        yield path, node
        for i, child in enumerate(_path_children(node)):
            yield from _walk(child, path + (i,))
    yield from _walk(root, ())


# node_at and replace_at themselves live in _fol_nodes.py, next to Node and
# Quantifier (the one node type the path convention special-cases) — imported
# above and re-exported here so `fol.spans.replace_at`/`fol.spans.node_at`
# work too, since a caller reasoning about spans is exactly who needs them.
# See _fol_nodes.py's own "Public tree editing (path-addressed replacement)
# and PATH CONVENTION" section for their implementation and the reasoning
# behind excluding a Quantifier's bound variable from its path children.


# =========================
# SpanMap: path -> NodeSpans, with an identity-based convenience index
# =========================

class SpanMap:
    """``Path -> NodeSpans`` table returned alongside an AST by
    :meth:`MSFLParser.parse_with_spans`.

    The PATH-keyed table (``.get(path)``) is the primary, spec-correct
    interface (see the module docstring) and is exactly what survives
    pickling — see "PICKLING" below.

    ``.for_node(node)`` is a CONVENIENCE lookup for a caller that is holding
    an actual node object rather than a path (e.g. after some OTHER pass
    found a specific node by walking the tree itself, the way
    :mod:`unicode_fol_kit.semantics.model_eval`'s blame-finder does — see
    :mod:`unicode_fol_kit.mcp.chem_tools`). It works by IDENTITY against
    whichever tree this ``SpanMap`` was last :meth:`rebind`-ed to (a
    ``SpanMap`` returned by ``parse_with_spans`` is already bound to the AST
    it is returned alongside). A node that is not part of that exact tree —
    even one that is structurally ``==`` to a node that IS — reports
    :data:`UNKNOWN` for both fields, same as an absent path.
    """

    __slots__ = ("_table", "_by_id")

    def __init__(self, table: Dict[Path, NodeSpans]):
        self._table: Dict[Path, NodeSpans] = dict(table)
        self._by_id: Dict[int, Path] = {}

    # -- path-keyed access (primary) -----------------------------------

    def get(self, path: Path) -> NodeSpans:
        """The :class:`NodeSpans` recorded at ``path``, or a
        ``NodeSpans(UNKNOWN, UNKNOWN)`` if ``path`` has no entry."""
        return self._table.get(path, _UNKNOWN_NODE_SPANS)

    def __getitem__(self, path: Path) -> NodeSpans:
        return self.get(path)

    def __contains__(self, path: Path) -> bool:
        return path in self._table

    def __len__(self) -> int:
        return len(self._table)

    def __iter__(self) -> Iterator[Path]:
        return iter(self._table)

    def paths(self):
        """Every path with a recorded entry (dict_keys view, like a plain dict)."""
        return self._table.keys()

    def items(self):
        """``(path, NodeSpans)`` pairs for every recorded entry (dict_items view)."""
        return self._table.items()

    # -- identity-based convenience -------------------------------------

    def rebind(self, root: Node) -> "SpanMap":
        """Return a :class:`SpanMap` with the SAME path->NodeSpans data, but
        with :meth:`for_node`'s identity index rebuilt against ``root``.

        Use this after a shape-preserving rewrite that produced fresh node
        objects at the same paths (e.g.
        :func:`unicode_fol_kit.chem.interop.rename_with_spans` calls
        :func:`project_spans`, which already returns a rebound map) — or any
        time a caller wants ``.for_node`` to work against a specific tree it
        is holding. Cheap: one traversal of ``root`` (``O(n)``).
        """
        new = SpanMap(self._table)
        new._by_id = {id(node): path for path, node in traverse(root)}
        return new

    def for_node(self, node: Node) -> NodeSpans:
        """:meth:`get`, but looking ``node`` up by identity against whichever
        tree this map was last :meth:`rebind`-ed to (see the class
        docstring)."""
        path = self._by_id.get(id(node))
        if path is None:
            return _UNKNOWN_NODE_SPANS
        return self.get(path)

    # -- pickling ---------------------------------------------------------
    # Only `_table` is meaningful across a process boundary: it is keyed by
    # PATH (plain tuples of int — portable data, no dependence on this
    # process's object graph). `_by_id` is, by construction, scoped to
    # whichever tree object this map was last rebind()ed to IN THIS PROCESS
    # — those id()s mean nothing once unpickled elsewhere, so rather than
    # pickle stale, silently-never-matching ids, unpickling starts with an
    # empty identity index; call .rebind(root) again against the AST as
    # reconstructed on the receiving end to restore .for_node().

    def __getstate__(self):
        return {"table": self._table}

    def __setstate__(self, state):
        self._table = state["table"]
        self._by_id = {}


def build_span_map(root: Node, id_extent: Dict[int, Span],
                   id_head: Dict[int, Span]) -> SpanMap:
    """Build a path-keyed :class:`SpanMap` over ``root`` from two id()-keyed
    tables of (extent, head) spans captured DURING a single parse/transform.

    The id()-keying of ``id_extent``/``id_head`` is a TRANSIENT bookkeeping
    device local to the caller (see ``msflparser.py``'s span-capturing
    transform) — object identity is only relied on for the lifetime of that
    one transform call, never stored or exposed. This function is the one
    place that translates it into the stable, path-keyed representation:
    it walks ``root`` via :func:`traverse` (so the resulting keys are
    exactly the paths :func:`traverse` yields) and looks each node's spans
    up by ``id()`` while ``root`` is still the very AST the transform just
    produced (ids are still live and unambiguous at this point). Returns a
    map already :meth:`~SpanMap.rebind`-ed to ``root``.
    """
    table: Dict[Path, NodeSpans] = {}
    for path, node in traverse(root):
        ext = id_extent.get(id(node), UNKNOWN)
        head = id_head.get(id(node), UNKNOWN)
        table[path] = NodeSpans(ext, head)
    return SpanMap(table).rebind(root)


def project_spans(old_root: Node, new_root: Node, old_map: SpanMap) -> SpanMap:
    """Carry ``old_map`` (built over ``old_root``) forward onto ``new_root``,
    the result of a rewrite over ``old_root``.

    Because the table is PATH-keyed, this needs no per-node identity
    tracking: a path denotes the SAME structural position in any tree with
    matching shape, so a shape-preserving rewrite (:func:`resolve_lambda_scope`
    for a lambda-free formula; :mod:`unicode_fol_kit.chem.interop`'s
    predicate/function renaming, which only ever changes a string field) does
    not need its span table "carried" at all in the old id()-based sense —
    every path in ``old_map`` simply still means the same thing in
    ``new_root``.

    What this function actually guards against is a rewrite that is NOT
    shape-preserving somewhere: :func:`resolve_lambda_scope` rewrites a
    higher-order use of a lambda-bound predicate/function symbol (e.g. the
    body of ``λP. P(x) ∧ Q(y)``) from an n-ary ``Atom``/``Function`` into a
    fresh, LEFT-NESTED chain of ``Application`` nodes wrapping a synthesized
    ``LambdaVar`` — a node whose TYPE or child count differs from what sat at
    that path in ``old_root``, with no original span to carry (the original
    grammar never produced these nodes at all). Walking ``old_root`` and
    ``new_root`` in lockstep via :func:`_path_children`, a divergence (type
    or child-count mismatch) at some path stops descent on the ``new_root``
    side — that path and everything below it in ``new_root`` is left absent
    from the result, which :meth:`SpanMap.get`/:meth:`SpanMap.for_node`
    report as :data:`UNKNOWN`, never a guessed span. A LEAF-to-leaf step
    (both sides childless) always carries its recorded spans forward even if
    the node's TYPE changed (``Variable`` -> ``LambdaVar``, or a free
    epistemic/doxastic agent ``Variable`` -> ``Constant`` under
    :func:`~unicode_fol_kit.fol._modal_nodes.resolve_agent_variables`) — both
    cover the exact same source characters, just reinterpreted.

    Returns a new :class:`SpanMap`, already :meth:`~SpanMap.rebind`-ed to
    ``new_root``.
    """
    table: Dict[Path, NodeSpans] = {}

    def _walk(old: Node, new: Node, path: Path) -> None:
        old_children = _path_children(old)
        new_children = _path_children(new)
        if not old_children and not new_children:
            entry = old_map._table.get(path)
            if entry is not None:
                table[path] = entry
            return
        if type(old) is not type(new) or len(old_children) != len(new_children):
            return  # genuine restructuring — leave this subtree unmapped
        entry = old_map._table.get(path)
        if entry is not None:
            table[path] = entry
        for i, (oc, nc) in enumerate(zip(old_children, new_children)):
            _walk(oc, nc, path + (i,))

    _walk(old_root, new_root, ())
    return SpanMap(table).rebind(new_root)


@dataclass(frozen=True)
class SpannedFormula:
    """The result of :meth:`MSFLParser.parse_with_spans`: an AST plus its spans.

    ``formula`` is exactly what :meth:`MSFLParser.parse` would have returned
    for the same text (same node values, same structure) — ``parse_with_spans``
    changes nothing about how the formula is built. ``spans`` maps its nodes
    back to the source text; see :class:`SpanMap`.
    """

    formula: Node
    spans: SpanMap


# =========================
# Lark meta/token -> Span
# =========================

def span_from_meta(meta, text: str) -> Span:
    """Build a :class:`Span` from a Lark ``Tree.meta`` (propagate_positions=True)."""
    return Span(meta.start_pos, meta.end_pos, meta.line, meta.column,
                meta.end_line, meta.end_column, text[meta.start_pos:meta.end_pos])


def span_from_token(token, text: str) -> Span:
    """Build a :class:`Span` from a Lark ``Token`` (position attrs are always set)."""
    return Span(token.start_pos, token.end_pos, token.line, token.column,
                token.end_line, token.end_column,
                text[token.start_pos:token.end_pos])


def _line_col(text: str, pos: int) -> Tuple[int, int]:
    """1-based ``(line, column)`` for codepoint offset ``pos`` into ``text``,
    matching Lark's ``Meta``/``Token`` convention."""
    line = text.count("\n", 0, pos) + 1
    last_nl = text.rfind("\n", 0, pos)
    column = pos - last_nl  # last_nl == -1 (no preceding newline) -> pos + 1
    return line, column


def make_span(text: str, start: int, end: int) -> Span:
    """Build a :class:`Span` for the codepoint range ``[start, end)`` of
    ``text`` directly from the text — no Lark ``Meta``/``Token`` involved.

    Used for spans this module derives itself rather than reads off Lark:
    a synthesized HEAD span (an operator glyph located by :func:`find_glyph`,
    or a quantifier's symbol+variable) and a synthesized EXTENT for a
    same-level operator-chain intermediate (see msflparser.py's
    span-capturing transform).
    """
    l1, c1 = _line_col(text, start)
    l2, c2 = _line_col(text, end)
    return Span(start, end, l1, c1, l2, c2, text[start:end])


def find_glyph(text: str, start: int, end: int, glyph: str) -> Tuple[int, int]:
    """Locate the exact occurrence of ``glyph`` within ``text[start:end]``.

    Used to find an operator's own token position when Lark filters the
    operator out of the tree as an anonymous literal (every classical
    connective — ``¬ ∧ ∨ → ↔ ⊕`` — and every infix comparison — ``= < > ≤ ≥
    ≠`` — is declared this way; see msflparser.py's span-capturing
    transform). ``[start, end)`` is deliberately allowed to be WIDER than
    the true minimal gap around the operator (e.g. it may include an
    operand's own redundant wrapping parentheses, which are not part of
    that operand's reported EXTENT — see this module's docstring): searching
    for the operator's exact glyph text rather than "the first non-whitespace
    run" is what makes that safe, since none of the punctuation the grammar
    can otherwise place in that window (parentheses, whitespace) can equal
    the glyph itself, and the grammar guarantees exactly one genuine
    occurrence of it between two adjacent operands.

    Returns ``(glyph_start, glyph_end)``. Raises ``ValueError`` if ``glyph``
    does not occur in the window — a grammar/assumption violation, not a
    guessable situation.
    """
    idx = text.find(glyph, start, end)
    if idx == -1:
        raise ValueError(
            f"spans.find_glyph: expected to find {glyph!r} within "
            f"{text[start:end]!r} (codepoints [{start}, {end})); none found")
    return idx, idx + len(glyph)


def trim_ws_backward(text: str, pos: int) -> int:
    """The largest index ``<= pos`` such that ``text[index:pos]`` is all
    whitespace — i.e. ``pos`` scanned backward past any trailing whitespace."""
    while pos > 0 and text[pos - 1].isspace():
        pos -= 1
    return pos


def trim_ws_forward(text: str, pos: int) -> int:
    """The smallest index ``>= pos`` such that ``text[pos:index]`` is all
    whitespace — i.e. ``pos`` scanned forward past any leading whitespace."""
    while pos < len(text) and text[pos].isspace():
        pos += 1
    return pos


# =========================
# Gap filling: best-effort EXTENT fallback for a node this module has no
# precise rule for (out-of-scope operators; never used for HEAD, which is
# never fabricated — see the module docstring's UNKNOWN section)
# =========================

def fill_gap_spans(node: Node, id_extent: Dict[int, Span], text: str) -> None:
    """Post-order, id()-keyed (see :func:`build_span_map`'s docstring for why
    that is fine as a same-call-only bookkeeping device): derive an EXTENT
    for any node this module's span-capturing transform did not directly
    assign one to.

    Mutates ``id_extent`` in place. The derived span is the union of the
    node's OWN children's (already-known) extents — exact for a node whose
    every child extent is itself exact AND whose own true extent has no
    tokens outside its children's spans (true for the same-level
    operator-chain case this originally targeted, where the omitted node is
    itself later given a precise extent inline by the level2 fold — see
    msflparser.py — so in practice this fallback now only fires for
    out-of-scope node types). For anything with a mix of parenthesised and
    unparenthesised children, this union CAN include stray wrapping
    parentheses the same way an unprincipled union always would (see this
    module's docstring on why ``find_glyph`` searches for the operator glyph
    itself rather than assuming the gap is clean) — this fallback is
    consequently a best-effort EXTENT only, never used for HEAD, and never
    claimed exact outside the cases enumerated above.

    A node with no children already in ``id_extent`` (a genuine leaf this
    transform never captured — e.g. an agent variable sliced out of a
    combined ``K_a``-style token) is left absent, which reports
    :data:`UNKNOWN` once the id-table is turned into a path-keyed
    :class:`SpanMap` by :func:`build_span_map`.
    """
    children = node._child_nodes()
    for child in children:
        fill_gap_spans(child, id_extent, text)
    if id(node) in id_extent:
        return
    known: List[Span] = [id_extent[id(c)] for c in children if id(c) in id_extent]
    if not known:
        return
    start = min(s.start for s in known)
    end = max(s.end for s in known)
    id_extent[id(node)] = make_span(text, start, end)
