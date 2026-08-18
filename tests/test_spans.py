"""Acceptance tests for the path-keyed span layer (``fol/spans.py``,
``MSFLParser.parse_with_spans``) — spec items T1-T4, T6, T8, plus the
FOLIO-corpus test (T5) and cross-process picklability.

See ``fol/spans.py``'s module docstring for the design this pins down: a
``SpanMap`` keyed by :data:`~unicode_fol_kit.fol.spans.Path` (a tuple of
child indices from the root — the SAME convention
:func:`~unicode_fol_kit.fol.spans.traverse`, :func:`~unicode_fol_kit.fol.spans.node_at`,
and :func:`~unicode_fol_kit.fol.spans.replace_at` all agree on), never by
node identity or node value, with TWO spans per node (``extent``/``head``).
"""

import pickle
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path as FsPath

import pytest

from unicode_fol_kit.fol.msflparser import MSFLParser
from unicode_fol_kit.fol.spans import (
    UNKNOWN, SpanMap, traverse, node_at, replace_at,
)
from unicode_fol_kit.fol.nodes import (
    Node, Variable, Constant, Number, Function,
    Atom, And, Quantifier,
)

FOL = MSFLParser()
_TERM_LEAF_TYPES = (Variable, Constant, Number)
_FIXTURES = FsPath(__file__).parent / "fixtures"


# ---------------------------------------------------------------------------
# Shared helpers — reused by the hand-picked-formula tests and the FOLIO
# corpus sweep (T5), so both exercise EXACTLY the same T2/T3 checks.
# ---------------------------------------------------------------------------

def _assert_t2(text: str, formula: Node, spans: SpanMap) -> None:
    """T2 — slice-reparse: for every FORMULA-valued node, ``text[extent]``
    parses and is structurally equal to the subformula; for a leaf TERM node
    (Variable/Constant/Number), ``text[span]`` is character-equal to the
    identifier. A compound term (Function) is checked by the analogous
    reparse-as-term rule (wrapped as a single-argument atom, since the
    grammar's ``?start`` is formula-only)."""
    for path, node in traverse(formula):
        ns = spans.get(path)
        assert ns.extent is not UNKNOWN, f"{path} ({type(node).__name__}): extent is UNKNOWN"
        ext = ns.extent
        assert text[ext.start:ext.end] == ext.text
        if isinstance(node, _TERM_LEAF_TYPES):
            ident = node.name if hasattr(node, "name") else str(node.value)
            assert text[ext.start:ext.end] == ident, (
                f"{path} ({type(node).__name__}): extent slice "
                f"{text[ext.start:ext.end]!r} != identifier {ident!r}")
        elif isinstance(node, Function):
            sub = text[ext.start:ext.end]
            reparsed = FOL.parse(f"Q({sub})")
            assert reparsed.args[0] == node, (
                f"{path}: Function extent {sub!r} does not reparse to {node!r}")
        else:
            sub = text[ext.start:ext.end]
            reparsed = FOL.parse(sub)
            assert reparsed == node, (
                f"{path} ({type(node).__name__}): extent {sub!r} reparses to "
                f"{reparsed!r}, not the original {node!r}")


def _assert_t3(text: str, formula: Node, spans: SpanMap) -> None:
    """T3 — coverage: every occurrence of ∀ ∃ ¬ ∧ ∨ → ↔ ⊕ and every
    identifier is assigned to exactly one HEAD span; parentheses, commas,
    and whitespace may stay unassigned.

    Implemented as the stronger, direct invariant this reduces to for the
    classical fragment: every node's head is KNOWN (never UNKNOWN), no two
    heads overlap, and every character in ``text`` that is not punctuation
    (``()[],``) or whitespace is covered by exactly one head span — because
    a head span is exactly "an operator glyph" or "an identifier occurrence"
    (a quantifier's head additionally covers its bound variable — see
    ``fol/spans.py``'s module docstring — so the variable's own identifier
    is covered there, not double-counted anywhere else).
    """
    heads = []
    for path, node in traverse(formula):
        ns = spans.get(path)
        assert ns.head is not UNKNOWN, f"{path} ({type(node).__name__}): head is UNKNOWN"
        heads.append((ns.head.start, ns.head.end, path, type(node).__name__))
    heads.sort()
    for (s1, e1, p1, t1), (s2, e2, p2, t2) in zip(heads, heads[1:]):
        assert e1 <= s2, (
            f"overlapping head spans: {t1}@{p1} [{s1},{e1}) and "
            f"{t2}@{p2} [{s2},{e2}) in {text!r}")
    covered = set()
    for s, e, _, _ in heads:
        covered.update(range(s, e))
    for i, ch in enumerate(text):
        if ch in "()[],":
            continue
        if ch.isspace():
            continue
        assert i in covered, (
            f"character {ch!r} at codepoint {i} in {text!r} is not covered "
            "by any head span")


def _assert_t2_t3(text: str) -> "SpannedResult":
    spanned = FOL.parse_with_spans(text)
    _assert_t2(text, spanned.formula, spanned.spans)
    _assert_t3(text, spanned.formula, spanned.spans)
    return spanned


# ---------------------------------------------------------------------------
# T1 — occurrence: structurally-equal, equal-hashing atoms with DIFFERENT
# spans (P(x) ∧ P(x)).
# ---------------------------------------------------------------------------

class TestT1Occurrence:
    def test_equal_atoms_get_different_spans(self):
        text = "P(x) ∧ P(x)"
        spanned = FOL.parse_with_spans(text)
        a1, a2 = spanned.formula.left, spanned.formula.right

        assert a1 == a2
        assert hash(a1) == hash(a2)
        assert {a1, a2} == {a1}          # structural set: one element
        assert a1 is not a2              # but two distinct occurrences

        e1 = spanned.spans.for_node(a1).extent
        e2 = spanned.spans.for_node(a2).extent
        assert e1 != e2
        assert (e1.start, e1.end, e1.text) == (0, 4, "P(x)")
        assert (e2.start, e2.end, e2.text) == (7, 11, "P(x)")

    def test_same_path_keying_via_get(self):
        """The primary interface: two different PATHS resolve to two
        different NodeSpans for the two occurrences, without ever touching
        node identity."""
        text = "P(x) ∧ P(x)"
        spanned = FOL.parse_with_spans(text)
        left_span = spanned.spans.get((0,)).extent
        right_span = spanned.spans.get((1,)).extent
        assert (left_span.start, left_span.end) == (0, 4)
        assert (right_span.start, right_span.end) == (7, 11)

    def test_three_occurrences_in_a_fold(self):
        text = "P(x) ∧ P(x) ∧ P(x)"
        spanned = FOL.parse_with_spans(text)
        atoms = spanned.formula.left.left, spanned.formula.left.right, spanned.formula.right
        assert len({a for a in atoms}) == 1  # structurally one atom
        spans = [spanned.spans.for_node(a).extent for a in atoms]
        assert len({(s.start, s.end) for s in spans}) == 3  # three distinct spans


# ---------------------------------------------------------------------------
# T2 / T3 — hand-picked formulas spanning the target fragment, including the
# "redundant outer parens" and "operand carries its own parens inside a
# same-level fold" edge cases.
# ---------------------------------------------------------------------------

class TestT2SliceReparseAndT3Coverage:
    FORMULAS = [
        "P(x)",
        "((P(x)))",
        "¬P(x)",
        "¬ ¬ P(x)",
        "¬(P(x) ∧ Q(x))",
        "P(x) ∧ Q(x)",
        "P(x) ∧ Q(x) ∧ R(x)",
        "(P(x)) ∧ (Q(x)) ∧ (R(x))",          # each fold operand individually parenthesised
        "((P(x)) ∧ (Q(x))) ∧ R(x)",
        "P(x) ∨ Q(x) ∨ R(x)",
        "P(x) → Q(x)",
        "P(x) ↔ Q(x) → R(x)",
        "∀x P(x)",
        "∀ x P(x)",                            # whitespace between symbol and bound variable
        "∃x (P(x) ∧ Q(x))",
        "x = y",
        "x ≠ y",
        "x < y",
        "x ≤ y",
        "x ≥ y",
        "f(x) = g(y)",
        "P(f(x), a)",
        "P(x) ⊕ Q(x)",
        "((P(x) ∧ Q(x)) → (R(x) ∨ S(x)))",
        "∀x ∃y (P(x, y) → Q(y))",
        "∀x (P(x) → Q(x)) ∧ ∃y R(y)",
        "θ = a",                                # Greek CONSTANT token
        "x + y = z",                            # arithmetic term operators
        "x - y * z / w = a",
    ]

    @pytest.mark.parametrize("text", FORMULAS)
    def test_t2_and_t3(self, text):
        _assert_t2_t3(text)

    def test_redundant_outer_parens_excluded_from_extent(self):
        spanned = FOL.parse_with_spans("((P(x)))")
        ext = spanned.spans.get(()).extent
        assert (ext.start, ext.end) == (2, 6)
        assert ext.text == "P(x)"

    def test_fold_intermediate_extent_includes_operand_own_parens(self):
        """An intermediate fold node's extent is NOT the naive union of its
        operands' (paren-excluded) inner extents — it correctly widens to
        include an individually-parenthesised operand's own wrapping
        parens, since dropping them would slice through into an
        unparseable fragment (see msflparser.py's _fold_level2 docstring)."""
        text = "(P(x)) ∧ (Q(x)) ∧ (R(x))"
        spanned = FOL.parse_with_spans(text)
        # left-fold: path (0,) is And(P(x), Q(x)) -- the first intermediate.
        inter = spanned.spans.get((0,)).extent
        assert inter.text == "(P(x)) ∧ (Q(x))"
        assert FOL.parse(inter.text) == node_at(spanned.formula, (0,))

    def test_quantifier_head_includes_whitespace_to_the_variable(self):
        spanned = FOL.parse_with_spans("∀   x P(x)")
        head = spanned.spans.get(()).head
        assert head.text == "∀   x"


# ---------------------------------------------------------------------------
# T4 — codepoints: T2 on unicode-only formulas, with offsets verified as
# codepoint (not UTF-8 byte, not UTF-16 code-unit) indices.
# ---------------------------------------------------------------------------

class TestT4Codepoints:
    def test_offsets_survive_multibyte_operators_and_constants(self):
        # Every glyph here (∀ ¬ ∧ ∨ → ↔ ⊕ θ) is >1 byte in UTF-8 and would
        # give WRONG slice results under byte-indexed offsets; θ additionally
        # is outside Latin-1. Codepoint indices, which Python str slicing
        # always uses, give the right answer regardless.
        text = "∀x (¬P(x) ∧ (Q(x) ∨ R(x)) → (θ = x ↔ P(x) ⊕ Q(x)))"
        spanned = _assert_t2_t3(text)
        # Spot-check a few offsets by hand-counting codepoints (not bytes).
        assert text.encode("utf-8") != text.encode("latin-1", errors="ignore")
        assert len(text.encode("utf-8")) > len(text)  # proves it's genuinely multi-byte
        atom_p = node_at(spanned.formula, (0, 0, 0, 0))  # ∀x -> Implies.left(And).left(Not) -> P(x)
        assert atom_p == Atom("P", (Variable("x"),))
        span_p = spanned.spans.get((0, 0, 0, 0)).extent
        assert text[span_p.start:span_p.end] == "P(x)"

    def test_theta_constant_offset(self):
        text = "∀x (θ = x)"
        spanned = FOL.parse_with_spans(text)
        eq_atom = spanned.formula.formula
        theta = eq_atom.args[0]
        assert theta == Constant("θ")
        span = spanned.spans.for_node(theta).extent
        assert text[span.start:span.end] == "θ"
        # θ sits right after "∀x (" -- 4 codepoints in, not 4 UTF-8 bytes in
        # (∀ alone is 3 UTF-8 bytes), which would misalign the slice.
        assert span.start == 4


# ---------------------------------------------------------------------------
# T6 — invariant: whitespace variants of the same formula are equal,
# equal-hashing; repr is unchanged from 0.22.0 (plain dataclass repr, never
# touched by this change).
# ---------------------------------------------------------------------------

class TestT6Invariant:
    @pytest.mark.parametrize("a, b", [
        ("P(x)∧Q(x)", "P(x) ∧ Q(x)"),
        ("∀x P(x)", "∀   x   P(x)"),
        ("P(x)  →  Q(x)", "P(x)→Q(x)"),
        ("¬P(x)", "¬  P(x)"),
    ])
    def test_whitespace_variants_are_equal_and_hash_together(self, a, b):
        na, nb = FOL.parse(a), FOL.parse(b)
        assert na == nb
        assert hash(na) == hash(nb)
        # The span layer must not change what parse() itself returns.
        assert FOL.parse_with_spans(a).formula == na
        assert FOL.parse_with_spans(b).formula == nb

    def test_repr_unchanged(self):
        # Plain dataclass repr -- fields in declaration order, unquoted
        # class name, unmodified since 0.22.0 (this change adds no node
        # fields and no __repr__ override anywhere).
        assert repr(Atom("P", (Variable("x"),))) == \
            "Atom(predicate='P', args=(Variable(name='x'),))"
        assert repr(Quantifier("∀", Variable("x"), Atom("P", (Variable("x"),)))) == \
            "Quantifier(type='∀', variable=Variable(name='x'), " \
            "formula=Atom(predicate='P', args=(Variable(name='x'),)))"
        assert repr(And(Atom("P", ()), Atom("Q", ()))) == \
            "And(left=Atom(predicate='P', args=()), right=Atom(predicate='Q', args=()))"

    def test_span_map_does_not_affect_node_equality_or_hash(self):
        """Structural equality/hashing must be blind to spans entirely --
        two SEPARATE parses of the same text are still `==`/hash-equal even
        though their SpanMaps are for different SpanMap objects."""
        text = "P(x) ∧ Q(x)"
        s1 = FOL.parse_with_spans(text)
        s2 = FOL.parse_with_spans(text)
        assert s1.formula == s2.formula
        assert hash(s1.formula) == hash(s2.formula)
        assert s1.formula is not s2.formula
        assert s1.spans is not s2.spans


# ---------------------------------------------------------------------------
# T8 — edit stability: replace_at at path p; every path NOT running through
# p keeps its span on the ORIGINAL tree unchanged, and addresses the SAME
# node in the mutated tree.
# ---------------------------------------------------------------------------

class TestT8EditStability:
    def test_untouched_paths_keep_their_original_span_and_node(self):
        text = "∀x ((P(x) ∧ Q(x)) → (R(x) ∨ S(x)))"
        spanned = FOL.parse_with_spans(text)
        original = spanned.formula
        spans = spanned.spans

        # Snapshot every (path, node, NodeSpans) BEFORE the edit.
        before = {path: (node, spans.get(path)) for path, node in traverse(original)}

        p = (0, 0, 0)  # -> P(x), inside the And, inside the Implies, under ∀x
        assert node_at(original, p) == Atom("P", (Variable("x"),))
        mutated = replace_at(original, p, Atom("T", (Variable("x"),)))

        # (a) span lookup on the ORIGINAL tree/table is byte-for-byte unchanged.
        after_original_lookup = {path: (node, spans.get(path)) for path, node in traverse(original)}
        assert after_original_lookup == before

        # (b) every path that does not run through p addresses the SAME
        # node object in the mutated tree as it did in the original.
        def runs_through(q, path):
            return q == path or path[:len(q)] == q or q[:len(path)] == path

        for path, (node, _spans) in before.items():
            if runs_through(p, path):
                continue
            assert node_at(mutated, path) is node, (
                f"path {path} should still address the same object after "
                f"replacing at {p}")

        assert node_at(mutated, p) == Atom("T", (Variable("x"),))

    def test_spans_rebound_to_mutated_tree_still_resolve_untouched_nodes(self):
        text = "P(x) ∧ Q(x) ∧ R(x)"
        spanned = FOL.parse_with_spans(text)
        original = spanned.formula
        spans = spanned.spans

        q_atom = node_at(original, (0, 1))  # Q(x), untouched by the edit below
        q_extent_before = spans.for_node(q_atom).extent

        mutated = replace_at(original, (1,), Atom("T", (Variable("x"),)))
        rebound = spans.rebind(mutated)

        # Q(x) is the SAME object in `mutated` (off the replace_at spine),
        # so its extent resolves identically once rebound.
        assert node_at(mutated, (0, 1)) is q_atom
        assert rebound.for_node(q_atom).extent == q_extent_before


# ---------------------------------------------------------------------------
# A7 — picklability: nodes and the SpanMap survive a REAL ProcessPoolExecutor
# round trip, not just pickle.dumps/loads.
# ---------------------------------------------------------------------------

def _pickle_roundtrip_worker(formula: Node, spans: SpanMap):
    """Module-level (importable) worker: runs in a SEPARATE process, so
    ``formula``/``spans`` have been pickled to get here and whatever this
    returns is pickled back. Exercises the whole path-keyed table AND the
    node graph across a genuine process boundary."""
    table_len = len(spans)
    root_extent = spans.get(()).extent
    # .for_node needs a fresh rebind in this process -- its OWN id() index
    # is deliberately not picklable (see SpanMap.__getstate__'s docstring).
    rebound = spans.rebind(formula)
    left_extent = rebound.for_node(formula.left).extent
    return formula, table_len, root_extent, left_extent


class TestPicklability:
    def test_span_map_pickle_dumps_loads_roundtrip(self):
        spanned = FOL.parse_with_spans("P(x) ∧ Q(x)")
        blob = pickle.dumps(spanned.spans)
        restored = pickle.loads(blob)
        assert restored.get(()) == spanned.spans.get(())
        assert restored.get((0,)) == spanned.spans.get((0,))
        assert len(restored) == len(spanned.spans)
        # The identity index is deliberately NOT preserved across pickling.
        assert restored.for_node(spanned.formula).extent is UNKNOWN

    def test_unknown_sentinel_survives_pickling_as_the_same_singleton(self):
        from unicode_fol_kit.fol.spans import UNKNOWN as U
        assert pickle.loads(pickle.dumps(U)) is U

    def test_node_and_spanmap_survive_a_real_process_pool_round_trip(self):
        spanned = FOL.parse_with_spans("P(x) ∧ Q(x)")
        with ProcessPoolExecutor(max_workers=1) as pool:
            fut = pool.submit(_pickle_roundtrip_worker, spanned.formula, spanned.spans)
            formula_back, table_len, root_extent, left_extent = fut.result(timeout=60)

        assert formula_back == spanned.formula
        assert table_len == len(spanned.spans)
        assert root_extent == spanned.spans.get(()).extent
        assert left_extent == spanned.spans.get((0,)).extent


# ---------------------------------------------------------------------------
# T5 — FOLIO corpus: every PARSABLE line passes T2/T3 with zero UNKNOWN.
# Back-channel: the non-parsable lines, committed as
# tests/fixtures/folio_fol_strings_nonparsable.txt (line number + error).
# ---------------------------------------------------------------------------

_FOLIO_PATH = _FIXTURES / "folio_fol_strings.txt"
_FOLIO_NONPARSABLE_PATH = _FIXTURES / "folio_fol_strings_nonparsable.txt"


def _folio_lines():
    return [
        (i, line) for i, line in enumerate(_FOLIO_PATH.read_text(encoding="utf-8").splitlines(), start=1)
        if line.strip()
    ]


@pytest.mark.skipif(not _FOLIO_PATH.exists(), reason="FOLIO fixture not present")
class TestT5FolioCorpus:
    def test_every_parsable_line_passes_t2_t3_with_zero_unknown(self):
        failures = []
        parsable = 0
        for lineno, text in _folio_lines():
            try:
                spanned = FOL.parse_with_spans(text)
            except Exception:
                continue  # non-parsable lines are the back-channel below
            parsable += 1
            try:
                _assert_t2(text, spanned.formula, spanned.spans)
                _assert_t3(text, spanned.formula, spanned.spans)
            except AssertionError as e:
                failures.append(f"line {lineno}: {e}")
        assert parsable > 1000, f"only {parsable} FOLIO lines parsed -- fixture looks wrong"
        assert not failures, (
            f"{len(failures)} FOLIO line(s) failed T2/T3:\n" + "\n".join(failures[:20]))

    def test_nonparsable_lines_match_the_committed_artifact(self):
        """Regenerates the non-parsable-line list fresh and compares it
        against the checked-in artifact — a change to the parser/grammar
        that starts (or stops) accepting a FOLIO line shows up here as a
        deliberate, reviewable diff to that file, not a silent drift."""
        current = []
        for lineno, text in _folio_lines():
            try:
                FOL.parse_with_spans(text)
            except Exception as e:
                current.append(f"{lineno}\t{type(e).__name__}\t{e}")

        committed_lines = [
            l for l in _FOLIO_NONPARSABLE_PATH.read_text(encoding="utf-8").splitlines()
            if l and not l.startswith("#")
        ]
        assert current == committed_lines, (
            "the FOLIO non-parsable-line list has drifted from "
            f"{_FOLIO_NONPARSABLE_PATH.name} -- regenerate and review the diff "
            "if this is an intentional parser/grammar change"
        )
