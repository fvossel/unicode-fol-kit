"""``to_markdown()``/``to_html()`` on :class:`~unicode_fol_kit.eval.theory_check.TheoryReport`
and :class:`~unicode_fol_kit.eval.chem_batch.ChemBatchResult` — a pure display layer over
already-verified data (no new proof/model-finding logic, so no soundness risk).

Every fixture below is HAND-BUILT (the dataclasses constructed directly, no live
prover/RDKit call needed for ``TheoryReport``; a handful of RDKit-backed rows for the one
``ChemBatchResult`` test that exercises the real ``check_definitions`` entry point) so the
exact strings this file asserts on are known up front, not read back from a run. Three
things every renderer here is checked against:

1. Content fidelity — a hand-picked fact (a cycle's name chain, an unsatisfiable name, a
   subsumption's own pre-computed ``.explanation``) must appear verbatim in the rendered
   text, and every ``to_dict()`` key must have SOME corresponding substring in the
   Markdown (catches a field silently dropped by a future schema change).
2. Determinism — calling either renderer twice on the same object returns a
   byte-identical string.
3. HTML well-formedness (an independent ``html.parser`` tag-balance check, mirroring
   ``tests/test_fitch_html.py``'s ``_TagBalanceChecker``) and Markdown-table safety: a
   hostile string (containing ``|`` or a newline) must not corrupt a table's row/column
   structure, and must come back HTML-escaped rather than raw markup.
"""

import html.parser

import pytest

from unicode_fol_kit.fol.nodes import Atom, And, Not
from unicode_fol_kit.eval.explain import explain_countermodel
from unicode_fol_kit.eval.theory_check import (
    SatisfiabilityResult, SubsumptionResult, TheoryReport,
)
from unicode_fol_kit.eval.chem_batch import (
    ChemBatchResult, check_definitions, _md_cell as _chem_md_cell,
    _gloss_chem_witness, _cell as _chem_cell,
)
from unicode_fol_kit.eval.theory_check import _md_cell as _theory_md_cell
from unicode_fol_kit.eval.theory_check import (
    _witness_gloss, _z3_satisfiability_gloss, _generic_satisfiability_gloss,
    _subsumption_explanation,
)
from unicode_fol_kit.eval.chem_batch import _sample_rows


def P(name="p"):
    return Atom(name, [])


# ---------------------------------------------------------------------------
# Well-formedness helper (independent of the renderer's own bookkeeping) —
# same idiom as tests/test_fitch_html.py's _TagBalanceChecker.
# ---------------------------------------------------------------------------

class _TagBalanceChecker(html.parser.HTMLParser):
    _VOID = {"meta", "br", "hr", "img", "input", "link"}

    def __init__(self):
        super().__init__()
        self.stack = []

    def handle_starttag(self, tag, attrs):
        if tag not in self._VOID:
            self.stack.append(tag)

    def handle_endtag(self, tag):
        assert self.stack and self.stack[-1] == tag, (
            f"unbalanced </{tag}>; open stack was {self.stack}")
        self.stack.pop()


def _assert_balanced(html_text: str) -> None:
    parser = _TagBalanceChecker()
    parser.feed(html_text)
    parser.close()
    assert parser.stack == [], f"unclosed tags at end of document: {parser.stack}"


# ===========================================================================
# TheoryReport
# ===========================================================================

def _theory_fixture() -> TheoryReport:
    """One cycle, one unsatisfiable definition (no witness — see
    :class:`SatisfiabilityResult`'s own docstring: ``"unsatisfiable"`` never
    carries one), one satisfiable definition WITH a witness (the shape
    :class:`SatisfiabilityResult` documents: identical to
    ``Verdict.countermodel``), and one refuted subsumption carrying a
    pre-computed ``.explanation`` — one instance of every kind
    :attr:`TheoryReport.proved_problems` recognises, so the counts below are
    hand-countable: cycle(1) + unsatisfiable(1) + refuted(1) = 3 proved
    problems, 0 undecided (nothing here has status ``"unknown"``).
    """
    sat_dead = SatisfiabilityResult(
        name="dead", status="unsatisfiable",
        unfolded=And(P("p"), Not(P("p"))), witness=None, backend="z3",
        detail="dead can hold of no object: its unfolded definition is a "
               "contradiction, proved by z3.")
    sat_ok = SatisfiabilityResult(
        name="okClass", status="satisfiable", unfolded=P("p"),
        witness={"kind": "z3_model", "assignment": {"p": "True"}}, backend="z3",
        detail="a model satisfying okClass was found by z3.")
    sub_refuted = SubsumptionResult(
        sub="sub", sup="sup", status="refuted",
        verdict={"status": "refuted", "backend": "z3"},
        countermodel={"kind": "z3_model", "assignment": {"p": "True", "q": "False"}},
        explanation="sub's author forgot the q conjunct sup requires.")
    return TheoryReport(
        cycles=(("cycA", "cycB", "cycA"),),
        satisfiability={"dead": sat_dead, "okClass": sat_ok},
        subsumptions=(sub_refuted,),
    )


class TestTheoryReportMarkdown:
    def test_summary_counts_are_hand_checked(self):
        report = _theory_fixture()
        assert len(report.proved_problems) == 3   # cycle + unsat + refuted
        assert len(report.undecided) == 0
        md = report.to_markdown()
        assert "**3** proved problem(s), **0** undecided." in md

    def test_cycle_chain_appears_verbatim(self):
        md = _theory_fixture().to_markdown()
        assert "cycA -> cycB -> cycA" in md

    def test_unsatisfiable_name_and_detail_appear(self):
        md = _theory_fixture().to_markdown()
        assert "### unsatisfiable" in md
        assert "dead" in md
        assert "contradiction, proved by z3" in md

    def test_satisfiable_witness_is_glossed_honestly(self):
        """A satisfiability witness is NOT an implication countermodel:
        check_satisfiable proves Not(unfolded) REFUTED with EMPTY premises,
        so the model is a single-formula existential witness, not a model
        where two sides of an implication differ. explain_countermodel's
        Z3-assignment branch is hardcoded to that implication wording ("...
        the two sides differ"), which would misstate what was computed here
        -- see _witness_gloss's own docstring -- so it must NOT appear, while
        the assignment itself and an honest closing clause must."""
        report = _theory_fixture()
        md = report.to_markdown()
        assert "p := True" in md   # the underlying assignment, hand-known
        # hand-checked: _z3_satisfiability_gloss({"p": "True"}) formats
        # exactly this sentence (one assignment, sorted trivially)
        assert "Under the assignment p := True, the definition is satisfied." in md
        assert "the two sides differ" not in md
        # explain_countermodel's own wording for the SAME witness dict is the
        # thing this must differ from -- confirms the report does not just
        # happen to produce the same text by coincidence
        assert explain_countermodel(report.satisfiability["okClass"].witness) not in md

    def test_refuted_subsumption_explanation_is_rendered_verbatim(self):
        md = _theory_fixture().to_markdown()
        assert "sub's author forgot the q conjunct sup requires." in md
        assert "### refuted" in md
        assert "| sub | sup |" in md

    def test_every_to_dict_key_has_a_markdown_counterpart(self):
        """Coverage check: catches a field silently dropped by a future
        schema change. Normalises 'a_b' -> 'a b' and strips one trailing 's'
        so a plural/singular wording choice ('undecided' vs '0 undecided',
        'proved_problems' vs 'proved problem(s)') still counts as covered."""
        report = _theory_fixture()
        md = report.to_markdown().lower()
        for key in report.to_dict():
            stem = key.replace("_", " ").rstrip("s")
            assert stem in md, f"to_dict() key {key!r} has no counterpart in to_markdown()"

    def test_determinism(self):
        report = _theory_fixture()
        assert report.to_markdown() == report.to_markdown()

    def test_hostile_strings_do_not_break_the_table(self):
        # A name containing a pipe and a newline -- both would otherwise
        # corrupt a Markdown table's row/column structure.
        hostile = SatisfiabilityResult(
            name="wei|rd\nname", status="unsatisfiable", unfolded=P(),
            witness=None, backend="z3", detail="contains | a pipe\nand a newline")
        report = TheoryReport(cycles=(), satisfiability={"wei|rd\nname": hostile},
                              subsumptions=())
        md = report.to_markdown()
        lines = md.splitlines()
        row_lines = [l for l in lines if l.startswith("| wei")]
        assert len(row_lines) == 1                       # not split across lines
        assert row_lines[0].startswith("| ") and row_lines[0].endswith(" |")
        assert "\\|" in row_lines[0]                      # the pipe was escaped
        assert "\n" not in row_lines[0]

    def test_md_cell_escapes_pipes_and_collapses_newlines(self):
        assert _theory_md_cell("a|b") == "a\\|b"
        assert _theory_md_cell("a\nb") == "a b"
        assert _theory_md_cell("a\r\nb") == "a b"
        assert _theory_md_cell(None) == ""

    def test_z3_satisfiability_gloss_directly(self):
        # hand-checked: one assignment, sorted trivially, honest closing clause
        assert (_z3_satisfiability_gloss({"p": "True"})
                == "Under the assignment p := True, the definition is satisfied.")
        # sorted by name, not insertion order
        assert (_z3_satisfiability_gloss({"b": "1", "a": "0"})
                == "Under the assignment a := 0, b := 1, the definition is satisfied.")
        assert (_z3_satisfiability_gloss({})
                == "a model was found, but it recorded no variable assignments.")
        assert "two sides differ" not in _z3_satisfiability_gloss({"p": "True"})

    def test_witness_gloss_dispatch(self):
        assert _witness_gloss(None) is None
        # z3_model kind -> the local, honest gloss (not explain_countermodel's
        # implication wording)
        z3_gloss = _witness_gloss({"kind": "z3_model", "assignment": {"p": "True"}})
        assert z3_gloss == _z3_satisfiability_gloss({"p": "True"})
        assert "two sides differ" not in z3_gloss
        # bare {name: value} dict (no "kind" key) is treated the same way
        bare_gloss = _witness_gloss({"p": "True"})
        assert bare_gloss == _z3_satisfiability_gloss({"p": "True"})
        # any other kind that DOES carry a "repr" fallback (no implication
        # wording to strip) still goes through explain_countermodel as-is
        repr_gloss = _witness_gloss({"kind": "finite_structure", "repr": "<Structure X>"})
        assert repr_gloss == explain_countermodel(
            {"kind": "finite_structure", "repr": "<Structure X>"})

    def test_witness_gloss_covers_non_z3_model_assignment_shapes(self):
        """Regression for the adversarial-review blocker: any backend's
        ``{"kind": ..., "assignment": {...}}`` witness must be glossed
        honestly, not just ``"z3_model"``. cvc5 is a real, installed member
        of :func:`unicode_fol_kit.atp.protocol.default_chain` and
        :mod:`unicode_fol_kit.atp.cvc5_backend` emits exactly this shape
        (``countermodel={"kind": "cvc5_model", "assignment": ...}``) -- it
        must NOT be routed to :func:`explain_countermodel`, which only
        special-cases ``kind == "z3_model"`` and would raise ``ValueError``
        for any other kind lacking a ``"repr"`` key.
        """
        cvc5_gloss = _witness_gloss({"kind": "cvc5_model", "assignment": {"p": "true"}})
        assert cvc5_gloss == _z3_satisfiability_gloss({"p": "true"})
        assert "two sides differ" not in cvc5_gloss
        # explain_countermodel itself would raise ValueError on this shape
        # (no "assignment" recognised for a non-z3_model kind, no "repr")
        with pytest.raises(ValueError):
            explain_countermodel({"kind": "cvc5_model", "assignment": {"p": "true"}})

    def test_witness_gloss_does_not_crash_on_data_only_finite_structure(self):
        """Regression for the adversarial-review blocker: the clingo/minizinc
        backends emit ``{"kind": "finite_structure", "data": {...}}`` (a
        "data" key, not the modelfinder's own "repr" key of the same
        "kind") -- this has neither an "assignment" dict nor a "repr"
        fallback, so :func:`explain_countermodel` raises ``ValueError`` on
        it. :func:`_witness_gloss` must fall back to
        :func:`_generic_satisfiability_gloss` instead of letting that
        exception propagate out of a report-rendering method.
        """
        witness = {"kind": "finite_structure",
                   "data": {"domain": ["0"], "extensions": {"p/0": [[]]},
                            "computed": [], "constants": {}}}
        with pytest.raises(ValueError):
            explain_countermodel(witness)   # confirms this shape really is the crash case
        gloss = _witness_gloss(witness)
        assert gloss == _generic_satisfiability_gloss(witness)
        assert "finite_structure" in gloss
        assert "satisfied" in gloss

    def test_generic_satisfiability_gloss_directly(self):
        assert (_generic_satisfiability_gloss({"kind": "finite_structure", "data": {}})
                == 'A "finite_structure" model was found; the definition is satisfied.')
        # no "kind" key at all (defensive; _witness_gloss never reaches this
        # branch for a bare dict, since a bare dict is always an assignment)
        assert (_generic_satisfiability_gloss({"data": {}})
                == 'A "unlabelled" model was found; the definition is satisfied.')

    def test_satisfiable_witness_from_cvc5_and_clingo_backends_renders_end_to_end(self):
        """End-to-end: a whole TheoryReport containing a cvc5-shaped and a
        clingo/minizinc-shaped satisfiability witness renders without
        raising, in both formats -- mirroring
        TestChemBatchResultMarkdown's real-check_definitions coverage.
        """
        sat_cvc5 = SatisfiabilityResult(
            name="cvc5Class", status="satisfiable", unfolded=P("p"),
            witness={"kind": "cvc5_model", "assignment": {"p": "true"}},
            backend="cvc5", detail="a model satisfying cvc5Class was found by cvc5.")
        sat_clingo = SatisfiabilityResult(
            name="clingoClass", status="satisfiable", unfolded=P("q"),
            witness={"kind": "finite_structure",
                     "data": {"domain": ["0"], "extensions": {"q/0": [[]]},
                              "computed": [], "constants": {}}},
            backend="clingo", detail="a model satisfying clingoClass was found by clingo.")
        report = TheoryReport(
            cycles=(), satisfiability={"cvc5Class": sat_cvc5, "clingoClass": sat_clingo},
            subsumptions=())
        md = report.to_markdown()          # must not raise
        html_text = report.to_html()       # must not raise
        assert "p := true" in md
        assert "finite_structure" in md
        assert "the two sides differ" not in md
        assert "p := true" in html_text
        assert "finite_structure" in html_text
        _assert_balanced(html_text)

    def test_empty_report_renders_the_empty_sections_honestly(self):
        report = TheoryReport(cycles=(), satisfiability={}, subsumptions=())
        md = report.to_markdown()
        assert "No cycles." in md
        assert "No definitions." in md
        assert "No subsumption checks." in md
        assert "**0** proved problem(s), **0** undecided." in md

    def test_refuted_subsumption_with_no_explanation_and_unhandled_countermodel_does_not_crash(self):
        """Regression for the adversarial-review blocker: SubsumptionResult's
        __post_init__ only requires countermodel is not None when
        status == "refuted" -- it never requires explanation to be set, so a
        caller building one by hand (as this test does) can reach a
        status="refuted", explanation=None object whose countermodel is a
        shape explain_countermodel cannot handle (no "assignment" dict for a
        non-z3_model kind, no "repr" fallback). Unlike a SatisfiabilityResult
        witness, a SubsumptionResult countermodel genuinely IS an implication
        countermodel, so explain_countermodel's wording would be right IF it
        could render this shape -- the fix is only to not crash when it
        can't, mirroring check_subsumption's own try/except fallback.
        """
        cvc5_shaped = SubsumptionResult(
            sub="sub", sup="sup", status="refuted",
            verdict={"status": "refuted", "backend": "cvc5"},
            countermodel={"kind": "cvc5_model", "assignment": {"p": "true"}},
            explanation=None)
        with pytest.raises(ValueError):
            explain_countermodel(cvc5_shaped.countermodel)   # confirms the crash case
        report = TheoryReport(cycles=(), satisfiability={}, subsumptions=(cvc5_shaped,))
        md = report.to_markdown()          # must not raise
        html_text = report.to_html()       # must not raise
        assert "cvc5 found a countermodel: sub holds but sup does not." in md
        assert "cvc5 found a countermodel: sub holds but sup does not." in html_text
        _assert_balanced(html_text)

        data_only = SubsumptionResult(
            sub="sub2", sup="sup2", status="refuted",
            verdict={"status": "refuted", "backend": "clingo"},
            countermodel={"kind": "finite_structure",
                          "data": {"domain": ["0"], "extensions": {},
                                   "computed": [], "constants": {}}},
            explanation=None)
        with pytest.raises(ValueError):
            explain_countermodel(data_only.countermodel)     # confirms the crash case
        report2 = TheoryReport(cycles=(), satisfiability={}, subsumptions=(data_only,))
        md2 = report2.to_markdown()        # must not raise
        html_text2 = report2.to_html()     # must not raise
        assert "clingo found a countermodel: sub2 holds but sup2 does not." in md2
        assert "clingo found a countermodel: sub2 holds but sup2 does not." in html_text2
        _assert_balanced(html_text2)

    def test_subsumption_explanation_directly(self):
        # explicit explanation always wins, untouched
        explicit = SubsumptionResult(
            sub="a", sup="b", status="refuted",
            verdict={"status": "refuted", "backend": "z3"},
            countermodel={"kind": "z3_model", "assignment": {"x": "1"}},
            explanation="already set")
        assert _subsumption_explanation(explicit) == "already set"

        # no explanation, no countermodel -> None (nothing to compute from)
        no_cm = SubsumptionResult(
            sub="a", sup="b", status="unknown",
            verdict={"status": "unknown"}, countermodel=None, explanation=None)
        assert _subsumption_explanation(no_cm) is None

        # no explanation, a countermodel explain_countermodel CAN handle ->
        # routed through it, same as check_subsumption's own success path
        z3_result = SubsumptionResult(
            sub="a", sup="b", status="refuted",
            verdict={"status": "refuted", "backend": "z3"},
            countermodel={"kind": "z3_model", "assignment": {"x": "1"}},
            explanation=None)
        assert _subsumption_explanation(z3_result) == explain_countermodel(
            z3_result.countermodel)

        # no explanation, no "backend" key in verdict -> generic "a backend"
        no_backend = SubsumptionResult(
            sub="a", sup="b", status="refuted",
            verdict={"status": "refuted"},
            countermodel={"kind": "cvc5_model", "assignment": {"x": "1"}},
            explanation=None)
        assert (_subsumption_explanation(no_backend)
                == "a backend found a countermodel: a holds but b does not.")

    def test_non_refuted_countermodel_is_never_glossed_as_a_refutation(self):
        """Regression for the adversarial-review blocker on top of the
        crash-guard fix: SubsumptionResult.__post_init__ only requires a
        countermodel when status == "refuted" -- it never FORBIDS one
        alongside status in ("unknown", "entailed", "cyclic") on a hand-built
        instance (the same construction pattern this file's own tests use
        throughout). The module's own docstring promises status="unknown" is
        NEVER reported as "refuted", so _subsumption_explanation must not
        compute the countermodel-based fallback (explain_countermodel's
        prose, or the generic "found a countermodel" sentence) for any
        status other than "refuted" -- explanation=None must stay None, and
        the rendered report must not mention a countermodel at all.
        """
        for status, verdict in (
            ("unknown", {"status": "unknown", "backend": "z3"}),
            ("entailed", {"status": "entailed", "backend": "z3"}),
            ("cyclic", None),
        ):
            stray_cm = SubsumptionResult(
                sub="sub", sup="sup", status=status, verdict=verdict,
                countermodel={"kind": "z3_model", "assignment": {"p": "True", "q": "False"}},
                explanation=None)
            assert _subsumption_explanation(stray_cm) is None, status

            report = TheoryReport(cycles=(), satisfiability={}, subsumptions=(stray_cm,))
            md = report.to_markdown()
            html_text = report.to_html()
            for rendered in (md, html_text):
                assert "the two sides differ" not in rendered, (status, rendered)
                assert "found a countermodel" not in rendered, (status, rendered)
                assert "sub" in rendered and "sup" in rendered
            _assert_balanced(html_text)

    def test_satisfiability_witness_only_glossed_when_status_is_satisfiable(self):
        """Regression for the adversarial-review major finding:
        SatisfiabilityResult's docstring says only status="satisfiable" is
        documented to carry a witness, but __post_init__ does not enforce
        that on a hand-built instance (as this test does). A witness present
        alongside "unsatisfiable"/"unknown"/"cyclic" must never be glossed --
        the module must not render self-contradicting prose like
        "contradiction proved" together with "the definition is satisfied"
        in the same cell.
        """
        stray_witness = {"kind": "z3_model", "assignment": {"p": "True"}}
        for status, detail in (
            ("unsatisfiable", "dead can hold of no object: contradiction proved by z3."),
            ("unknown", "neither proved unsatisfiable nor witnessed satisfiable "
                        "within the given backend budget"),
            ("cyclic", "dead is part of a definitional cycle"),
        ):
            result = SatisfiabilityResult(
                name="dead", status=status,
                unfolded=(And(P("p"), Not(P("p"))) if status != "cyclic" else None),
                witness=stray_witness, backend="z3", detail=detail)
            report = TheoryReport(cycles=(), satisfiability={"dead": result}, subsumptions=())
            md = report.to_markdown()
            html_text = report.to_html()
            for rendered in (md, html_text):
                assert "the definition is satisfied" not in rendered, (status, rendered)
                assert detail in rendered, (status, rendered)
            _assert_balanced(html_text)


class TestTheoryReportHtml:
    def test_well_formed_and_self_contained(self):
        html_text = _theory_fixture().to_html()
        assert html_text.startswith("<!doctype html>")
        assert "<style>" in html_text and "</style>" in html_text
        assert "prefers-color-scheme:dark" in html_text
        assert "http://" not in html_text and "https://" not in html_text
        _assert_balanced(html_text)

    def test_default_and_custom_title(self):
        assert "<title>Theory report</title>" in _theory_fixture().to_html()
        assert "<title>My audit</title>" in _theory_fixture().to_html(title="My audit")

    def test_content_matches_markdown_fixture(self):
        report = _theory_fixture()
        html_text = report.to_html()
        assert "cycA -&gt; cycB -&gt; cycA" in html_text or "cycA -> cycB -> cycA" in html_text
        assert "sub&#x27;s author forgot the q conjunct sup requires." in html_text \
            or "sub's author forgot the q conjunct sup requires." in html_text

    def test_satisfiable_witness_is_glossed_honestly(self):
        """Same honesty requirement as the Markdown side (see
        TestTheoryReportMarkdown.test_satisfiable_witness_is_glossed_honestly):
        a satisfiability witness must not carry the implication-countermodel
        wording "the two sides differ"."""
        html_text = _theory_fixture().to_html()
        assert "p := True" in html_text
        assert "the definition is satisfied" in html_text
        assert "the two sides differ" not in html_text

    def test_escapes_hostile_markup_in_names(self):
        hostile = SatisfiabilityResult(
            name="A<script>&B", status="unsatisfiable", unfolded=P(),
            witness=None, backend="z3", detail="<img src=x>")
        report = TheoryReport(cycles=(), satisfiability={"A<script>&B": hostile},
                              subsumptions=())
        html_text = report.to_html()
        assert "A&lt;script&gt;&amp;B" in html_text
        assert "<script>" not in html_text
        assert "<img src=x>" not in html_text
        _assert_balanced(html_text)

    def test_determinism(self):
        report = _theory_fixture()
        assert report.to_html() == report.to_html()


# ===========================================================================
# ChemBatchResult
# ===========================================================================

def _chem_fixture(n_bad: int = 3) -> ChemBatchResult:
    ok_row = {"def_id": "amide", "smiles": "CCO", "status": "ok", "holds": True,
              "steps": 3, "exhausted": False, "witness": {"C": "c1"},
              "error_kind": None, "error_msg": None, "ms": 1.0, "cached": True}
    bad_rows = [
        {"def_id": f"amide{i}", "smiles": "not-a-molecule(((", "status": "structure_error",
         "holds": None, "steps": None, "exhausted": None, "witness": None,
         "error_kind": "StructureBuildError", "error_msg": "RDKit refused this SMILES",
         "ms": 0.5, "cached": False}
        for i in range(n_bad)
    ]
    rows = tuple([ok_row] + bad_rows)
    counts = {"ok": 1, "exhausted": 0, "structure_error": n_bad,
             "parse_error": 0, "eval_error": 0}
    cache_stats = {"entries": n_bad + 1, "hits": 0, "misses": n_bad + 1,
                  "evictions": 0, "hit_rate": 0.0, "max_entries": 100000}
    return ChemBatchResult(rows=rows, counts=counts, cache_stats=cache_stats,
                           seconds=1.234, skipped=2)


class TestChemBatchResultMarkdown:
    def test_summary_table_matches_counts_exactly(self):
        result = _chem_fixture()
        md = result.to_markdown()
        for status, count in result.counts.items():
            assert f"| {status} | {count} |" in md

    def test_seconds_and_skipped_appear(self):
        md = _chem_fixture().to_markdown()
        assert "1.234" in md
        assert "**2** skipped" in md

    def test_truncation_note_matches_min_max_rows_and_total(self):
        result = _chem_fixture(n_bad=40)
        non_ok_total = sum(1 for r in result.rows if r["status"] != "ok")
        assert non_ok_total == 40

        default_md = result.to_markdown()                 # default max_rows=25
        assert "showing 25 of 40 non-ok row(s)" in default_md

        capped_md = result.to_markdown(max_rows=5)
        assert "showing 5 of 5" not in capped_md
        assert "showing 5 of 40 non-ok row(s)" in capped_md

        uncapped_md = result.to_markdown(max_rows=1000)
        assert "showing 40 of 40 non-ok row(s)" in uncapped_md

    def test_negative_max_rows_is_clamped_to_zero_not_a_negative_slice(self):
        """Regression for the adversarial-review blocker: non_ok[:max_rows]
        with a negative max_rows (e.g. a caller's limit - offset arithmetic
        going wrong) would use Python's negative-slice semantics and drop
        elements from the END of the list instead of capping the sample to
        zero -- the opposite of what a cap parameter should do, while
        "showing N of M" still looked like a plausible, not obviously wrong,
        count. A negative max_rows must render zero sampled rows.
        """
        result = _chem_fixture(n_bad=5)
        for bad_max_rows in (-1, -5, -1000):
            md = result.to_markdown(max_rows=bad_max_rows)
            sample_section = md.split("## Sample of non-ok rows")[1]
            table_lines = [l for l in sample_section.splitlines() if l.startswith("|")]
            assert len(table_lines) == 2                   # header + separator only
            assert "showing 0 of 5 non-ok row(s)" in md

    def test_sample_rows_directly_clamps_negative_max_rows(self):
        result = _chem_fixture(n_bad=5)
        sample, total = _sample_rows(result, -1)
        assert sample == []
        assert total == 5
        sample0, total0 = _sample_rows(result, 0)
        assert sample0 == []
        assert total0 == 5

    def test_error_msg_is_shown_for_a_sampled_row(self):
        md = _chem_fixture().to_markdown()
        assert "RDKit refused this SMILES" in md

    def test_ok_rows_are_never_in_the_sample(self):
        md = _chem_fixture().to_markdown()
        # the one "ok" row's def_id must not appear inside the sample table
        # (it legitimately appears nowhere else in this fixture's rendering)
        sample_section = md.split("## Sample of non-ok rows")[1]
        assert "| amide |" not in sample_section

    def test_witness_gloss_does_not_attribute_to_z3(self):
        """Deviation from the literal build spec: a chem row's witness is a
        model_eval existential binding, never a Z3 assignment, so it is
        glossed by this module's own honest helper rather than
        eval.explain.explain_countermodel (whose bare-dict branch is
        hardcoded Z3 wording) -- see _gloss_chem_witness's docstring.

        Note: this row is HAND-BUILT with status='exhausted' AND a non-None
        witness together -- a combination check_definitions() itself cannot
        produce today, since it only ever sets row['witness'] in the branch
        that leaves status='ok' (see _row_detail's docstring). This test
        exercises the rendering function's handling of that row shape in
        isolation, not a claim that real campaign data reaches it."""
        row = {"def_id": "w", "smiles": "N", "status": "exhausted", "holds": None,
               "steps": 9, "exhausted": True, "witness": {"C": "c1", "N": "n2"},
               "error_kind": None, "error_msg": None, "ms": 1.0, "cached": False}
        result = ChemBatchResult(
            rows=(row,), counts={"ok": 0, "exhausted": 1, "structure_error": 0,
                                 "parse_error": 0, "eval_error": 0},
            cache_stats={}, seconds=0.1, skipped=0)
        md = result.to_markdown()
        assert "witness C=c1, N=n2" in md
        assert "Z3" not in md

    def test_gloss_chem_witness_directly(self):
        assert _gloss_chem_witness(None) == ""
        assert _gloss_chem_witness({}) == ""
        assert _gloss_chem_witness({"N": "n2", "C": "c1"}) == "witness C=c1, N=n2"

    def test_cell_directly(self):
        assert _chem_cell(None) == ""
        assert _chem_cell("x") == "x"
        assert _chem_cell(0) == "0"        # falsy but not None -- must not blank out

    def test_every_to_dict_summary_key_has_a_markdown_counterpart(self):
        result = _chem_fixture()
        md = result.to_markdown().lower()
        for key in ("seconds", "skipped"):
            assert key in md
        for status in result.counts:
            assert status in md

    def test_determinism(self):
        result = _chem_fixture()
        assert result.to_markdown() == result.to_markdown()

    def test_hostile_strings_do_not_break_the_table(self):
        row = {"def_id": "d|1\nX", "smiles": "C|C\n<b>", "status": "eval_error",
               "holds": None, "steps": None, "exhausted": None, "witness": None,
               "error_kind": "X", "error_msg": "bad | thing\nwith a newline",
               "ms": 1.0, "cached": False}
        result = ChemBatchResult(
            rows=(row,), counts={"ok": 0, "exhausted": 0, "structure_error": 0,
                                 "parse_error": 0, "eval_error": 1},
            cache_stats={}, seconds=0.1, skipped=0)
        md = result.to_markdown()
        sample_section = md.split("## Sample of non-ok rows")[1]
        table_lines = [l for l in sample_section.splitlines() if l.startswith("|")]
        # header + separator + exactly one data row -- an unescaped embedded
        # newline would have split the one data row across two lines.
        assert len(table_lines) == 3
        data_line = table_lines[2]
        assert data_line.startswith("| ") and data_line.endswith(" |")
        assert "\\|" in data_line
        assert "\n" not in data_line

    def test_md_cell_escapes_pipes_and_collapses_newlines(self):
        assert _chem_md_cell("a|b") == "a\\|b"
        assert _chem_md_cell("a\nb") == "a b"
        assert _chem_md_cell(None) == ""

    def test_no_non_ok_rows_is_rendered_honestly_not_omitted(self):
        result = ChemBatchResult(
            rows=({"def_id": "a", "smiles": "CCO", "status": "ok", "holds": True,
                  "steps": 1, "exhausted": False, "witness": None,
                  "error_kind": None, "error_msg": None, "ms": 1.0, "cached": True},),
            counts={"ok": 1, "exhausted": 0, "structure_error": 0,
                   "parse_error": 0, "eval_error": 0},
            cache_stats={}, seconds=0.1, skipped=0)
        md = result.to_markdown()
        assert "showing 0 of 0 non-ok row(s)" in md


class TestChemBatchResultHtml:
    def test_well_formed_and_self_contained(self):
        html_text = _chem_fixture().to_html()
        assert html_text.startswith("<!doctype html>")
        assert "<style>" in html_text and "</style>" in html_text
        assert "prefers-color-scheme:dark" in html_text
        assert "http://" not in html_text and "https://" not in html_text
        _assert_balanced(html_text)

    def test_default_and_custom_title(self):
        assert "<title>Chem batch result</title>" in _chem_fixture().to_html()
        assert "<title>Run 42</title>" in _chem_fixture().to_html(title="Run 42")

    def test_escapes_hostile_markup(self):
        row = {"def_id": "<script>alert(1)</script>", "smiles": "C&O", "status": "eval_error",
               "holds": None, "steps": None, "exhausted": None, "witness": None,
               "error_kind": "X", "error_msg": "<img src=x onerror=alert(1)>",
               "ms": 1.0, "cached": False}
        result = ChemBatchResult(
            rows=(row,), counts={"ok": 0, "exhausted": 0, "structure_error": 0,
                                 "parse_error": 0, "eval_error": 1},
            cache_stats={}, seconds=0.1, skipped=0)
        html_text = result.to_html()
        assert "&lt;script&gt;alert(1)&lt;/script&gt;" in html_text
        assert "<script>alert(1)</script>" not in html_text
        assert "&lt;img src=x onerror=alert(1)&gt;" in html_text
        assert "<img src=x" not in html_text
        _assert_balanced(html_text)

    def test_max_rows_applies_to_html_too(self):
        result = _chem_fixture(n_bad=40)
        html_text = result.to_html(max_rows=3)
        assert "showing 3 of 40 non-ok row(s)" in html_text
        _assert_balanced(html_text)

    def test_negative_max_rows_is_clamped_to_zero(self):
        result = _chem_fixture(n_bad=5)
        html_text = result.to_html(max_rows=-1)
        assert "showing 0 of 5 non-ok row(s)" in html_text
        _assert_balanced(html_text)

    def test_none_valued_field_renders_blank_not_the_literal_string_none(self):
        """check_definitions() always sets smiles=None on a parse_error row
        (the formula itself failed to parse, before any molecule is looked
        at) -- str(None) would render the misleading literal text "None" in
        the cell; it must come back blank, matching the Markdown renderer's
        _md_cell(None) == "" behaviour exactly."""
        row = {"def_id": "bad", "smiles": None, "status": "parse_error",
               "holds": None, "steps": None, "exhausted": None, "witness": None,
               "error_kind": "TokenizeError", "error_msg": "unexpected end of input",
               "ms": None, "cached": None}
        result = ChemBatchResult(
            rows=(row,), counts={"ok": 0, "exhausted": 0, "structure_error": 0,
                                 "parse_error": 1, "eval_error": 0},
            cache_stats={}, seconds=0.1, skipped=0)
        html_text = result.to_html()
        assert "<td>bad</td><td></td><td>parse_error</td>" in html_text
        assert "None" not in html_text
        _assert_balanced(html_text)
        # the two renderers must agree on the same input
        md = result.to_markdown()
        assert "| bad |  | parse_error |" in md

    def test_determinism(self):
        result = _chem_fixture()
        assert result.to_html() == result.to_html()


# ===========================================================================
# End-to-end against the real check_definitions() entry point (RDKit-backed),
# tying the renderer to actual campaign rows rather than only hand-built ones.
# ===========================================================================

pytest.importorskip("rdkit", reason="the end-to-end fixture builds real structures")

AMIDE = "?[C,O,N]: (c(C) & o(O) & n(N) & bDOUBLE(C,O) & bSINGLE(C,N))"


def test_real_check_definitions_result_renders_without_error():
    result = check_definitions(
        [{"id": "amide", "formula": AMIDE}],
        ["NCC(=O)NCC(=O)O", "CCO", "not-a-molecule((("],
    )
    assert result.counts["structure_error"] == 1     # hand-known: one bad SMILES

    md = result.to_markdown(max_rows=5)
    assert "showing 1 of 1 non-ok row(s)" in md        # the one structure_error
    assert "| ok | 2 |" in md
    assert "| structure_error | 1 |" in md

    html_text = result.to_html(max_rows=5)
    _assert_balanced(html_text)
    assert "showing 1 of 1 non-ok row(s)" in html_text
