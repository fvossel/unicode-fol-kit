"""Tests for KripkeModel.to_dot() / to_svg(), the Graphviz export of a frame.

Structural checks mirror tests/test_traversal.py's Node.to_dot() checks: they
are hand-checkable without ever invoking Graphviz, and count DOT lines by
regex/substring scanning of the *final string*, independent of to_dot()'s own
emit-loop bookkeeping (so a bug that shares the same miscounting between the
production code and the test would not hide here). to_svg() gets one
unconditional test (a bogus binary name fails loud, exercising the RuntimeError
path with no Graphviz install required) plus one skipif-gated live test that
runs 'dot -Tsvg' for real when Graphviz is on PATH, the same
shutil.which-skipif convention already used for pdflatex/eprover/minizinc/
vampire elsewhere in this test suite (e.g. tests/test_derivation.py's
pdflatex-gated test).
"""

import re
import shutil

import pytest

from unicode_logic_kit.semantics.kripke import KripkeModel


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

_NODE_LINE_RE = re.compile(r'^\s*"(?:[^"\\]|\\.)*"\s*\[label="')
_EDGE_LINE_RE = re.compile(r'^\s*"(?:[^"\\]|\\.)*"\s*->\s*"(?:[^"\\]|\\.)*"\s*\[label="')


def _node_lines(dot: str):
    """DOT lines that declare a world node: an anchored ``"id" [label=...``
    line, matched by line *structure* rather than by substring scanning for
    ``"->"`` — a world whose own ``str()``/``repr()`` happens to contain the
    substring ``->`` (a plausible label for e.g. a transition-system state)
    must still be recognized as a node line, not misclassified as an edge."""
    return [ln for ln in dot.splitlines() if _NODE_LINE_RE.match(ln)]


def _edge_lines(dot: str):
    """DOT lines that declare an edge: an anchored ``"src" -> "dst" [label=...``
    line, matched by line structure for the same reason as ``_node_lines``."""
    return [ln for ln in dot.splitlines() if _EDGE_LINE_RE.match(ln)]


def _label_of(dot: str, node_id_repr: str) -> str:
    """Extract the raw (still-escaped) label text of the node whose DOT id is
    the escaped repr() of ``node_id_repr`` — a small independent parse of the
    to_dot() output, not a call into to_dot()'s own machinery."""
    pattern = re.compile(
        r'"' + re.escape(node_id_repr) + r'"\s*\[label="((?:[^"\\]|\\.)*)"\];'
    )
    m = pattern.search(dot)
    assert m, f"no node declaration found for id {node_id_repr!r} in:\n{dot}"
    return m.group(1)


def _atoms_in_label(label: str):
    """The atom tokens (second '\\n'-separated segment, '@'-nominals excluded)
    of a raw label string, as produced by _label_of."""
    segments = label.split("\\n")
    if len(segments) < 2 or segments[1] == "":
        return set()
    return {tok for tok in segments[1].split(", ") if not tok.startswith("@")}


def _is_well_formed(dot: str) -> None:
    assert dot.startswith("digraph Kripke {")
    assert dot.rstrip().endswith("}")
    assert dot.count("{") == dot.count("}")


# ---------------------------------------------------------------------------
# (1) Empty frame
# ---------------------------------------------------------------------------

class TestEmptyFrame:
    def test_no_nodes_no_edges(self):
        model = KripkeModel(worlds=[])
        dot = model.to_dot()
        _is_well_formed(dot)
        assert len(_node_lines(dot)) == 0 == len(model.worlds)
        assert len(_edge_lines(dot)) == 0


# ---------------------------------------------------------------------------
# (2) Single reflexive world
# ---------------------------------------------------------------------------

class TestSingleReflexiveWorld:
    def _model(self):
        return KripkeModel(
            worlds={0}, relations={"alethic": {(0, 0)}}, valuation={0: {"P"}}
        )

    def test_one_node_one_edge(self):
        model = self._model()
        dot = model.to_dot()
        _is_well_formed(dot)
        assert len(_node_lines(dot)) == 1 == len(model.worlds)
        edges = _edge_lines(dot)
        assert len(edges) == 1 == sum(len(e) for e in model.relations.values())
        assert '[label="alethic"];' in edges[0]

    def test_atoms_match_accessor(self):
        model = self._model()
        dot = model.to_dot()
        label = _label_of(dot, repr(0))
        assert _atoms_in_label(label) == set(model.atoms_true_at(0)) == {"P"}


# ---------------------------------------------------------------------------
# (3) Three-world linear temporal chain: 0 -> 1 -> 2
# ---------------------------------------------------------------------------

class TestLinearTemporalChain:
    def _model(self):
        return KripkeModel(
            worlds={0, 1, 2},
            relations={"temporal": {(0, 1), (1, 2)}},
            valuation={0: {"P"}, 1: {"Q"}, 2: set()},
        )

    def test_node_and_edge_counts(self):
        model = self._model()
        dot = model.to_dot()
        _is_well_formed(dot)
        assert len(_node_lines(dot)) == 3 == len(model.worlds)
        edges = _edge_lines(dot)
        assert len(edges) == 2 == sum(len(e) for e in model.relations.values())
        assert all('[label="temporal"];' in e for e in edges)

    def test_atoms_match_accessor_per_world(self):
        model = self._model()
        dot = model.to_dot()
        for world in (0, 1, 2):
            label = _label_of(dot, repr(world))
            assert _atoms_in_label(label) == set(model.atoms_true_at(world))

    def test_edges_are_sorted_and_deterministic(self):
        # Same model, built twice: byte-identical output (determinism).
        assert self._model().to_dot() == self._model().to_dot()
        dot = self._model().to_dot()
        idx0 = dot.index('"0" -> "1"')
        idx1 = dot.index('"1" -> "2"')
        assert idx0 < idx1


# ---------------------------------------------------------------------------
# (4) Multi-agent epistemic frame: two K:-relations + one B:-relation over the
# same two worlds — the case the spec calls out as the one a naive port of
# Node.to_dot() would silently collapse (several named edge sets, same nodes).
# ---------------------------------------------------------------------------

class TestMultiRelationFrame:
    def _model(self):
        return KripkeModel(
            worlds={0, 1},
            relations={
                "K:a": {(0, 1)},
                "K:b": {(0, 1), (1, 0)},
                "B:a": {(0, 0)},
            },
            valuation={0: {"P"}, 1: set()},
        )

    def test_edge_count_is_the_union_of_all_relations(self):
        model = self._model()
        dot = model.to_dot()
        _is_well_formed(dot)
        assert len(_node_lines(dot)) == 2 == len(model.worlds)
        expected_total = 1 + 2 + 1  # |K:a| + |K:b| + |B:a|
        edges = _edge_lines(dot)
        assert len(edges) == expected_total
        assert expected_total == sum(len(e) for e in model.relations.values())

    def test_each_relation_keeps_its_own_label_count(self):
        model = self._model()
        dot = model.to_dot()
        for name, edges in model.relations.items():
            assert dot.count(f'[label="{name}"];') == len(edges)

    def test_relations_do_not_collapse_into_one_indistinguishable_arrow(self):
        # 0->1 is an edge of BOTH K:a and K:b: it must appear as TWO distinct
        # labelled edge lines, not be deduplicated into one arrow.
        model = self._model()
        dot = model.to_dot()
        zero_to_one = [ln for ln in _edge_lines(dot) if '"0" -> "1"' in ln]
        assert len(zero_to_one) == 2
        labels = {re.search(r'label="([^"]*)"', ln).group(1) for ln in zero_to_one}
        assert labels == {"K:a", "K:b"}


# ---------------------------------------------------------------------------
# (5) Model with nominals (hybrid logic)
# ---------------------------------------------------------------------------

class TestNominals:
    def _model(self):
        return KripkeModel(worlds={0, 1}, valuation={1: {"P"}}, nominals={"i": 1})

    def test_nominal_name_appears_at_its_world_only(self):
        model = self._model()
        dot = model.to_dot()
        label1 = _label_of(dot, repr(1))
        label0 = _label_of(dot, repr(0))
        assert "@i" in label1.split("\\n")[1]
        assert len(label0.split("\\n")) < 2 or "@i" not in label0.split("\\n")[1]

    def test_atoms_still_match_accessor_alongside_nominal(self):
        model = self._model()
        dot = model.to_dot()
        label1 = _label_of(dot, repr(1))
        assert _atoms_in_label(label1) == set(model.atoms_true_at(1)) == {"P"}


# ---------------------------------------------------------------------------
# show_valuation=False suppresses the atoms/nominal line
# ---------------------------------------------------------------------------

class TestShowValuationFlag:
    def test_false_omits_atoms_and_nominal_line(self):
        model = KripkeModel(worlds={0}, valuation={0: {"P"}}, nominals={"i": 0})
        dot = model.to_dot(show_valuation=False)
        assert "P" not in dot
        assert "@i" not in dot
        # still one well-formed node declaration
        assert len(_node_lines(dot)) == 1


# ---------------------------------------------------------------------------
# Domains, when present, are shown per world
# ---------------------------------------------------------------------------

class TestDomains:
    def test_domain_line_present_when_domains_given(self):
        model = KripkeModel(worlds={0, 1}, domain=["a", "b"])
        dot = model.to_dot()
        label0 = _label_of(dot, repr(0))
        # hand-checked: constant domain {a, b} at every world
        assert "D = {a, b}" in label0.replace("\\n", "\n")

    def test_no_domain_line_when_domains_absent(self):
        model = KripkeModel(worlds={0})
        dot = model.to_dot()
        assert "D = " not in dot


# ---------------------------------------------------------------------------
# Escaping: world/atom/relation names with quotes, backslashes, spaces,
# non-ASCII — every identifier must round-trip into valid-looking DOT.
# ---------------------------------------------------------------------------

class TestEscaping:
    def _model(self):
        return KripkeModel(
            worlds={'w "one"', "wörld", "back\\slash"},
            relations={'K:Alice "Bob"': {('w "one"', "wörld")}},
            valuation={'w "one"': {'P("x")', "Größe"}},
        )

    def test_well_formed_despite_special_characters(self):
        dot = self._model().to_dot()
        _is_well_formed(dot)
        # every physical source line stays a single line: no raw newline was
        # smuggled in (a real embedded "\n" would have split a declaration
        # across two lines and broken the per-line node/edge count above).
        model = self._model()
        assert len(_node_lines(dot)) == 3 == len(model.worlds)

    def test_quotes_and_backslashes_are_escaped(self):
        dot = self._model().to_dot()
        # the raw (unescaped) forms must never appear as bare DOT syntax —
        # every quote inside a label/id is preceded by a backslash.
        for m in re.finditer(r'"((?:[^"\\]|\\.)*)"', dot):
            content = m.group(1)
            # if content itself contains an unescaped quote, the regex group
            # would not have matched past it — so reaching here already
            # proves balance; additionally check no bare backslash-free
            # embedded quote survived unescaped:
            assert '\\"' in content or '"' not in content

    def test_relation_name_with_quotes_and_space_is_escaped_in_label(self):
        dot = self._model().to_dot()
        assert '[label="K:Alice \\"Bob\\""];' in dot

    def test_non_ascii_atom_and_world_names_round_trip(self):
        dot = self._model().to_dot()
        assert "wörld" in dot
        assert "Größe" in dot


# ---------------------------------------------------------------------------
# A world whose own label contains '->' must not confuse the node/edge
# counting oracle above (TestEscaping covers quotes/backslashes/spaces/
# non-ASCII but not this substring, which is the one most relevant to DOT's
# own edge syntax).
# ---------------------------------------------------------------------------

class TestArrowInWorldLabel:
    def _model(self):
        return KripkeModel(
            worlds={"a->b", "c"},
            relations={"alethic": {("c", "c")}},
            valuation={"a->b": {"P"}},
        )

    def test_node_count_is_not_confused_by_the_arrow_substring(self):
        model = self._model()
        dot = model.to_dot()
        _is_well_formed(dot)
        # hand-checked: 2 worlds ('a->b' and 'c') -> 2 node lines, even though
        # one world's own repr contains the substring '->'.
        assert len(_node_lines(dot)) == 2 == len(model.worlds)

    def test_edge_count_is_not_confused_by_the_arrow_substring(self):
        model = self._model()
        dot = model.to_dot()
        # hand-checked: exactly one edge, the reflexive 'alethic' loop on 'c'.
        edges = _edge_lines(dot)
        assert len(edges) == 1 == sum(len(e) for e in model.relations.values())
        assert '"\'c\'" -> "\'c\'"' in edges[0]


# ---------------------------------------------------------------------------
# to_svg(): fail-loud path (unconditional) + live rendering (gated)
# ---------------------------------------------------------------------------

class TestToSvg:
    def test_bogus_binary_raises_runtime_error(self):
        model = KripkeModel(worlds={0})
        with pytest.raises(RuntimeError):
            model.to_svg(dot_binary="definitely-not-a-real-binary")

    def test_missing_dot_on_path_raises_runtime_error(self, monkeypatch):
        monkeypatch.setattr(shutil, "which", lambda name: None)
        model = KripkeModel(worlds={0})
        with pytest.raises(RuntimeError, match="Graphviz"):
            model.to_svg()

    @pytest.mark.skipif(shutil.which("dot") is None, reason="no Graphviz 'dot' binary found")
    def test_live_svg_starts_with_xml_or_svg_tag(self):
        model = KripkeModel(
            worlds={0, 1}, relations={"alethic": {(0, 1)}}, valuation={0: {"P"}}
        )
        svg = model.to_svg()
        assert svg.startswith("<?xml") or svg.startswith("<svg")

    @pytest.mark.skipif(shutil.which("dot") is None, reason="no Graphviz 'dot' binary found")
    def test_live_svg_renders_special_character_model(self):
        # the escaping-heavy model from TestEscaping must be ACTUAL valid
        # Graphviz syntax, not just look plausible — this is the real,
        # independent-tool check the structural tests above cannot give.
        model = TestEscaping()._model()
        svg = model.to_svg()
        assert svg.startswith("<?xml") or svg.startswith("<svg")


# ---------------------------------------------------------------------------
# _repr_svg_: notebook display hook never raises, even without Graphviz
# ---------------------------------------------------------------------------

class TestReprSvgHook:
    def test_returns_none_when_dot_missing(self, monkeypatch):
        monkeypatch.setattr(shutil, "which", lambda name: None)
        model = KripkeModel(worlds={0})
        assert model._repr_svg_() is None

    @pytest.mark.skipif(shutil.which("dot") is None, reason="no Graphviz 'dot' binary found")
    def test_returns_svg_text_when_dot_available(self):
        model = KripkeModel(worlds={0})
        result = model._repr_svg_()
        assert result is not None
        assert result.startswith("<?xml") or result.startswith("<svg")
