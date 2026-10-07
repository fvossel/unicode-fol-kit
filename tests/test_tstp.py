"""Tests for :mod:`atp.tstp` and the additive Vampire SZS/TSTP route.

Every fixture snippet below is either (a) captured verbatim from a real
``vampire --proof tptp`` run (Vampire 5.0.1, local WSL install) during
development of this module, or (b) hand-built to match the syntax documented
at the primary sources this module's docstring cites:

    * SZS status line + full status ontology — https://tptp.org/UserDocs/SZSOntology/
    * TSTP annotated-formula / inference(rule, info, parents) syntax —
      https://tptp.org/UserDocs/QuickGuide/Derivations.html

The two captured-from-a-real-run snippets are marked below; everything else is
hand-built and reasoned about in each test's docstring/comment (no snapshot
tests — every expected value has a stated reason).
"""

from pathlib import Path
from typing import Tuple

import pytest

from unicode_logic_kit import MSFLParser
from unicode_logic_kit.atp import protocol as P
from unicode_logic_kit.atp.tstp import (
    TstpDerivation, TstpStep,
    extract_szs_status, parse_tstp_derivation, szs_to_verdict_fields,
)
from unicode_logic_kit.atp.vampire_entailment import check_entailment_vampire_detailed

_FOL = MSFLParser()


def _recorded(name: str) -> str:
    """Verbatim stdout of a real E 3.5.1 run, shared with
    test_eprover_zipperposition.py's identical helper (see
    tests/fixtures/eprover_3_5_1_*.txt — captured under EProverBackend's own
    ``--auto --tstp-format --proof-object -s --cpu-limit=N`` arguments)."""
    path = Path(__file__).parent / "fixtures" / f"eprover_3_5_1_{name}.txt"
    return path.read_text(encoding="utf-8")

# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

# Captured verbatim from `vampire --proof tptp` (Vampire 5.0.1) proving
# {∀x(Human(x) => Mortal(x)), Human(socrates)} ⊢ Mortal(socrates); only the
# temp-file path inside the two `file(...)` source records was shortened to
# 'mp.p' for readability (the syntax around it — quoted path, 'unknown'
# position — is exactly as Vampire printed it).
_THEOREM_OUTPUT = """\
% Running in auto input_syntax mode. Trying TPTP
% Refutation found. Thanks to Tanya!
% SZS status Theorem for mp
% SZS output start Proof for mp
fof(f1,axiom,(
  ! [X0] : (human(X0) => mortal(X0))),
  file('mp.p',unknown)).
fof(f2,axiom,(
  human(socrates)),
  file('mp.p',unknown)).
fof(f3,conjecture,(
  mortal(socrates)),
  file('mp.p',unknown)).
fof(f4,negated_conjecture,(
  ~mortal(socrates)),
  inference(negated_conjecture,[status(cth)],[f3])).
fof(f5,plain,(
  ~mortal(socrates)),
  inference(flattening,[],[f4])).
fof(f6,plain,(
  ! [X0] : (mortal(X0) | ~human(X0))),
  inference(ennf_transformation,[],[f1])).
fof(f7,plain,(
  ( ! [X0] : (~human(X0) | mortal(X0)) )),
  inference(cnf_transformation,[],[f6])).
fof(f8,plain,(
  human(socrates)),
  inference(cnf_transformation,[],[f2])).
fof(f9,plain,(
  ~mortal(socrates)),
  inference(cnf_transformation,[],[f5])).
fof(f10,plain,(
  mortal(socrates)),
  inference(resolution,[],[f7,f8])).
fof(f11,plain,(
  $false),
  inference(forward_subsumption_resolution,[],[f10,f9])).
% SZS output end Proof for mp
% ------------------------------
% Termination reason: Refutation
% Time elapsed: 0.030 s
% ------------------------------
"""

# Captured verbatim from `vampire --proof tptp` on {Human(socrates)} with
# conjecture Mortal(socrates): the premise does not force mortality, so
# Vampire finds a finite countermodel (human(X)=true, mortal(X)=false for
# all X) instead of a proof, and prints NO fof/cnf derivation lines at all
# (`--proof tptp` only formats a found *proof*; a model report is a
# different output section) -- exercises "SZS line present, zero fof/cnf
# statements" (derivation must come back as an EMPTY TstpDerivation, still
# non-None, from parse_tstp_derivation itself; the caller-level "empty ->
# None" collapse only happens in check_entailment_vampire_detailed).
_COUNTERSAT_OUTPUT = """\
% Running in auto input_syntax mode. Trying TPTP
% SZS status CounterSatisfiable for cs
% SZS output start Saturation.
% SZS output end Saturation.
% SZS output start Definitions and Model Updates.
for all inputs,
    define human(X0) := $true
for all inputs,
    define mortal(X0) := $false
% SZS output end Definitions and Model Updates.
% ------------------------------
% Termination reason: Satisfiable
% Time elapsed: 0.016 s
% ------------------------------
"""

# Hand-built per the SZS ontology's "Timeout" definition ("Software stopped
# because the CPU time limit ran out") -- Vampire prints exactly this shape
# (a bare status line, no proof section, a "Time limit" termination reason)
# when it exhausts its wall-clock budget without a decision.
_TIMEOUT_OUTPUT = """\
% Running in auto input_syntax mode. Trying TPTP
% SZS status Timeout for hard
% ------------------------------
% Termination reason: Time limit
% ------------------------------
"""

_NO_SZS_LINE_OUTPUT = "Some prover crashed before printing anything useful.\n"

_MODUS_PONENS_PREMISES = [
    _FOL.parse("∀x (Human(x) → Mortal(x))"),
    _FOL.parse("Human(socrates)"),
]
_MORTAL = _FOL.parse("Mortal(socrates)")


# ---------------------------------------------------------------------------
# extract_szs_status
# ---------------------------------------------------------------------------

class TestExtractSzsStatus:
    def test_plain_status_line(self):
        assert extract_szs_status("% SZS status Theorem for foo") == "Theorem"

    def test_first_line_wins_when_several_present(self):
        """A proof's status line always precedes any status line INSIDE the
        proof's own useful_info records (none occur in practice, but the
        contract is "first line", not "any line"), and the theorem-output
        fixture's real status line must be what's picked out of full output."""
        assert extract_szs_status(_THEOREM_OUTPUT) == "Theorem"
        assert extract_szs_status(_COUNTERSAT_OUTPUT) == "CounterSatisfiable"
        assert extract_szs_status(_TIMEOUT_OUTPUT) == "Timeout"

    def test_tolerates_doubled_percent_and_leading_whitespace(self):
        assert extract_szs_status("   %% SZS status GaveUp for x") == "GaveUp"

    def test_hash_comment_marker_as_printed_by_eprover(self):
        """E prefixes its TSTP comments with '#', not '%': the real E line is
        '# SZS status Theorem' — the extractor accepts both marker styles."""
        assert extract_szs_status("# SZS status Theorem") == "Theorem"
        assert extract_szs_status("  ## SZS status ResourceOut for x") == "ResourceOut"

    def test_ignores_trailing_free_text_after_the_value(self):
        """'% SZS status GaveUp for SYN075+1 : Could not complete CNF
        conversion' is the documented shape for software-specific detail
        appended after the problem name; only the bare value is extracted."""
        line = "% SZS status GaveUp for SYN075+1 : Could not complete CNF conversion"
        assert extract_szs_status(line) == "GaveUp"

    def test_no_szs_line_returns_none(self):
        assert extract_szs_status(_NO_SZS_LINE_OUTPUT) is None
        assert extract_szs_status("") is None

    def test_szs_shaped_text_inside_a_comment_body_is_not_required_context(self):
        """A line that merely CONTAINS 'SZS status' after other text on the
        same line (not at the start, ignoring '%'/whitespace) is not the
        recognised shape and must not match."""
        assert extract_szs_status("this is not a % SZS status Theorem line") is None


# ---------------------------------------------------------------------------
# szs_to_verdict_fields
# ---------------------------------------------------------------------------

class TestSzsToVerdictFields:
    """Full table, both query framings -- every branch reasoned about inline."""

    @pytest.mark.parametrize("szs, expected", [
        # All models of Ax model the conjecture -> entailment established.
        ("Theorem", (P.PROVED, None)),
        # A model of Ax models the conjecture's negation -> genuine countermodel.
        ("CounterSatisfiable", (P.REFUTED, None)),
        # Ax alone has no model -> Ax |= C for every C (ex falso quodlibet):
        # a degenerate but classically correct proof of the entailment.
        ("ContradictoryAxioms", (P.PROVED, None)),
        # These two are the NO-conjecture branch's success values; seeing
        # them under a conjecture query is a framing mismatch this module
        # refuses to resolve by guessing proved/refuted.
        ("Satisfiable", (P.UNKNOWN, "incomplete")),
        ("Unsatisfiable", (P.UNKNOWN, "incomplete")),
        # Shared no-success values.
        ("Timeout", (P.UNKNOWN, "timeout")),
        ("ResourceOut", (P.UNKNOWN, "bound_hit")),
        ("GaveUp", (P.UNKNOWN, "incomplete")),
        ("Inappropriate", (P.UNKNOWN, "unsupported")),
        ("Error", (P.ERROR, "infra")),
        ("InputError", (P.ERROR, "infra")),
        ("SyntaxError", (P.ERROR, "infra")),
        ("Unknown", (P.UNKNOWN, None)),
        ("Open", (P.UNKNOWN, None)),
        ("Assumed", (P.UNKNOWN, None)),
        # A value outside the whole SZS ontology as this module knows it:
        # never guessed, always (unknown, None).
        ("TotallyMadeUpValue", (P.UNKNOWN, None)),
    ])
    def test_conjecture_query(self, szs, expected):
        assert szs_to_verdict_fields(szs, query="conjecture") == expected

    @pytest.mark.parametrize("szs, expected", [
        # No model of (premises AND NOT conclusion) -> entailment holds.
        ("Unsatisfiable", (P.PROVED, None)),
        # A model of (premises AND NOT conclusion) exists -> countermodel.
        ("Satisfiable", (P.REFUTED, None)),
        # These three are the WITH-conjecture branch's success values; a
        # mismatch under a refutation query, same treatment as above.
        ("Theorem", (P.UNKNOWN, "incomplete")),
        ("CounterSatisfiable", (P.UNKNOWN, "incomplete")),
        ("ContradictoryAxioms", (P.UNKNOWN, "incomplete")),
        # Shared no-success values, identical to the conjecture framing.
        ("Timeout", (P.UNKNOWN, "timeout")),
        ("ResourceOut", (P.UNKNOWN, "bound_hit")),
        ("GaveUp", (P.UNKNOWN, "incomplete")),
        ("Inappropriate", (P.UNKNOWN, "unsupported")),
        ("Error", (P.ERROR, "infra")),
        ("Unknown", (P.UNKNOWN, None)),
        ("TotallyMadeUpValue", (P.UNKNOWN, None)),
    ])
    def test_refutation_query(self, szs, expected):
        assert szs_to_verdict_fields(szs, query="refutation") == expected

    def test_unknown_status_never_yields_a_definitive_verdict(self):
        """An unrecognised SZS token must never come back proved/refuted --
        that would be inventing a result the prover never actually reported."""
        status, _ = szs_to_verdict_fields("SomeFutureSzsValue", query="conjecture")
        assert status == P.UNKNOWN

    def test_bad_query_raises(self):
        with pytest.raises(ValueError):
            szs_to_verdict_fields("Theorem", query="nonsense")

    def test_reason_is_none_only_for_definitive_or_unknown_no_more_info(self):
        """Verdict's contract: reason is non-None only for UNKNOWN/ERROR, and
        even then only when there IS more to say than 'we don't know'."""
        for szs in ("Theorem", "CounterSatisfiable", "ContradictoryAxioms"):
            status, reason = szs_to_verdict_fields(szs, query="conjecture")
            assert status in (P.PROVED, P.REFUTED)
            assert reason is None


# ---------------------------------------------------------------------------
# parse_tstp_derivation
# ---------------------------------------------------------------------------

class TestParseTstpDerivation:
    def test_theorem_derivation_shape(self):
        """The real captured Vampire proof: 11 steps, in source order, with
        the exact rule/parent DAG Vampire produced (hand-checked against the
        fixture text above)."""
        d = parse_tstp_derivation(_THEOREM_OUTPUT)
        assert isinstance(d, TstpDerivation)
        assert [s.name for s in d.steps] == [f"f{i}" for i in range(1, 12)]
        assert all(s.language == "fof" for s in d.steps)

        by_name = {s.name: s for s in d.steps}

        # Leaves: sourced from `file(...)`, not `inference(...)` -> no rule,
        # no parents, even though a source field IS present.
        for name in ("f1", "f2", "f3"):
            assert by_name[name].rule is None
            assert by_name[name].parents == ()
        assert by_name["f1"].role == "axiom"
        assert by_name["f3"].role == "conjecture"

        # The negation-of-conjecture step and its rule/parent chain.
        assert by_name["f4"].role == "negated_conjecture"
        assert by_name["f4"].rule == "negated_conjecture"
        assert by_name["f4"].parents == ("f3",)

        assert by_name["f10"].rule == "resolution"
        assert by_name["f10"].parents == ("f7", "f8")

        # The refutation's final empty clause: two parents, both prior steps.
        assert by_name["f11"].rule == "forward_subsumption_resolution"
        assert by_name["f11"].parents == ("f10", "f9")

    def test_theorem_formulas_parse_back_to_nodes(self):
        """Every step's formula_text is well-formed TPTP FOF, so `formula`
        must be a Node (not None) for all 11 steps, and f2's node must be
        exactly Human(socrates) re-rendered through to_tptp (round-trip
        sanity, not a snapshot -- this is the one formula simple enough to
        hand-verify directly)."""
        d = parse_tstp_derivation(_THEOREM_OUTPUT)
        assert all(s.formula is not None for s in d.steps)
        f2 = next(s for s in d.steps if s.name == "f2")
        assert f2.formula.to_tptp() == "human(socrates)"

    def test_countersatisfiable_output_has_no_derivation_steps(self):
        """--proof tptp only formats a found PROOF; Vampire's model report
        (printed instead, on CounterSatisfiable) contains no fof/cnf lines,
        so parse_tstp_derivation must return an EMPTY (not None -- that
        collapse is check_entailment_vampire_detailed's job) TstpDerivation."""
        d = parse_tstp_derivation(_COUNTERSAT_OUTPUT)
        assert d.steps == ()

    def test_timeout_output_has_no_derivation_steps(self):
        assert parse_tstp_derivation(_TIMEOUT_OUTPUT).steps == ()

    def test_text_with_no_fof_or_cnf_statements_at_all(self):
        assert parse_tstp_derivation(_NO_SZS_LINE_OUTPUT).steps == ()
        assert parse_tstp_derivation("").steps == ()

    def test_unparseable_formula_keeps_raw_text_with_formula_none(self):
        """`$distinct` is a TPTP dollar-word this codebase's TPTP grammar does
        not implement (only $less/$greater/$lesseq/$greatereq are wired to
        atoms in fol.tptp_input's _DOLLAR_PRED table) -- parse_tptp_formula
        raises ParsingError on it, so formula must fall back to None while
        formula_text keeps the exact source."""
        text = "fof(f1,axiom,$distinct(a,b,c))."
        d = parse_tstp_derivation(text)
        assert len(d.steps) == 1
        step = d.steps[0]
        assert step.formula is None
        assert step.formula_text == "$distinct(a,b,c)"

    def test_nested_inference_parents_that_are_compound_terms_are_dropped(self):
        """E-prover-style output nests unnamed inference(...) steps and/or
        theory(equality) markers directly inside the parents list instead of
        naming them. Neither is a bare parent NAME this module can report,
        so parents comes back empty rather than fabricating names -- the
        rule itself is still read correctly."""
        text = (
            "cnf(175,lemma,(rsymProp(ib,sk_c3)|sk_c4=sk_c3),"
            "inference(factor_simp,[status(thm)],"
            "[inference(para_into,[status(thm)],[96,78,theory(equality)])]))."
        )
        d = parse_tstp_derivation(text)
        assert len(d.steps) == 1
        step = d.steps[0]
        assert step.language == "cnf"
        assert step.rule == "factor_simp"
        assert step.parents == ()

    def test_plain_numeric_parents_are_kept(self):
        """A parent list of bare numeric refs (E-prover's own naming scheme)
        -- these ARE valid bare names, so they must be kept verbatim."""
        text = "fof(96,plain,mortal(socrates),inference(cnf_transformation,[],[7,8]))."
        d = parse_tstp_derivation(text)
        assert d.steps[0].parents == ("7", "8")

    def test_statement_with_no_source_field_at_all(self):
        """A bare 3-field statement (name, role, formula, no 4th field) is
        legal TSTP (this is exactly the shape tests/test_tptp_header.py's
        underlying grammar already accepts) -- rule/parents both empty."""
        d = parse_tstp_derivation("fof(ax1, axiom, p(a)).")
        assert len(d.steps) == 1
        assert d.steps[0].rule is None
        assert d.steps[0].parents == ()

    def test_multiple_statements_and_intervening_comment_noise(self):
        """Banner lines, SZS lines, and %-comments between statements are all
        skipped; only the two fof( ) statements become steps, in order."""
        text = (
            "% Running in auto input_syntax mode. Trying TPTP\n"
            "% SZS status Theorem for x\n"
            "fof(f1,axiom,p(a)).\n"
            "% a comment in between\n"
            "fof(f2,plain,q(a),inference(foo,[],[f1])).\n"
            "% SZS output end Proof for x\n"
        )
        d = parse_tstp_derivation(text)
        assert [s.name for s in d.steps] == ["f1", "f2"]
        assert d.steps[1].parents == ("f1",)

    def test_cnf_language_is_recorded_distinctly_from_fof(self):
        d = parse_tstp_derivation("cnf(c1, axiom, human(x)|~mortal(x)).")
        assert d.steps[0].language == "cnf"

    def test_to_dict_is_json_compatible(self):
        import json
        d = parse_tstp_derivation(_THEOREM_OUTPUT)
        # Must not raise -- every value in the tree is a JSON primitive.
        dumped = json.dumps(d.to_dict())
        assert "f11" in dumped
        assert "forward_subsumption_resolution" in dumped


# ---------------------------------------------------------------------------
# C11's TSTP-derivation leg: _deep_ancestor_names and relevant_premises_from_tstp
# -- all offline, on RECORDED and hand-built TSTP text, per the roadmap spec's
# own requirement that the ancestor walk be tested this way (independent of
# any live prover run).
# ---------------------------------------------------------------------------

from unicode_logic_kit.atp.tstp import _deep_ancestor_names, _relevant_axiom_names
from unicode_logic_kit.atp.tstp import relevant_premises_from_tstp


class TestDeepAncestorNames:
    def test_non_inference_source_is_a_leaf(self):
        assert _deep_ancestor_names(None) == frozenset()
        assert _deep_ancestor_names("file('mp.p',unknown)") == frozenset()

    def test_flat_bare_name_parents_agree_with_parse_source(self):
        """When nothing is nested, the deep walk must read the SAME bare
        names _parse_source already does (see test_plain_numeric_parents_are_kept
        above) -- it is a strict SUPERSET only when something is nested."""
        assert (_deep_ancestor_names("inference(cnf_transformation,[],[7,8])")
               == frozenset({"7", "8"}))

    def test_compound_theory_marker_contributes_no_name_but_does_not_drop_siblings(self):
        """The exact shape _parse_source drops WHOLESALE (pinned by
        test_nested_inference_parents_that_are_compound_terms_are_dropped
        above): here the sibling bare names in the SAME list must still come
        through, unlike _parse_source's all-or-nothing behaviour."""
        text = "inference(para,[status(thm)],[96,78,theory(equality)])"
        assert _deep_ancestor_names(text) == frozenset({"96", "78"})

    def test_recurses_into_a_singly_nested_inference(self):
        text = "inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_7,c_0_8])])"
        assert _deep_ancestor_names(text) == frozenset({"c_0_7", "c_0_8"})

    def test_recurses_through_three_levels_exactly_like_e_prover_c_0_6(self):
        """Verbatim shape from tests/fixtures/eprover_3_5_1_theorem.txt's
        c_0_6 statement (E's own fof_nnf/variable_rename administrative
        chain, which never gets its own c_0_N name at each level) -- this is
        EXACTLY the case _parse_source drops to () entirely."""
        text = ("inference(fof_nnf,[status(thm)],"
               "[inference(variable_rename,[status(thm)],"
               "[inference(fof_nnf,[status(thm)],[premise_2])])])")
        assert _deep_ancestor_names(text) == frozenset({"premise_2"})

    def test_mixed_nested_and_bare_siblings(self):
        text = ("inference(cn,[status(thm)],"
               "[inference(rw,[status(thm)],[inference(spm,[status(thm)],"
               "[c_0_7, c_0_8]), c_0_9])])")
        # Verbatim shape of the recorded fixture's sink step (c_0_10) --
        # hand-traced in this module's docstring comment.
        assert _deep_ancestor_names(text) == frozenset({"c_0_7", "c_0_8", "c_0_9"})


class TestRelevantAxiomNamesAndPremises:
    def test_recorded_e_prover_theorem_fixture_both_premises_needed(self):
        """The real, recorded E 3.5.1 derivation (tests/fixtures/
        eprover_3_5_1_theorem.txt) -- both premise_1 and premise_2 feed the
        sink through E's own nested administrative inference chain (c_0_6
        especially, hand-traced above); this is the exact live-shape
        regression the spec's TSTP leg exists to fix (TstpStep.parents alone
        would lose premise_2 behind that nesting)."""
        text = _recorded("theorem")
        assert _relevant_axiom_names(text) == frozenset({"premise_1", "premise_2"})
        assert relevant_premises_from_tstp(text, n_premises=2) == (0, 1)

    def test_vampire_style_leaf_names_are_not_premise_named_so_none(self):
        """Vampire renames every statement to its OWN f1/f2/... scheme --
        verified live against Vampire 5.0.1 -- so even though f1/f2 ARE genuinely the two axiom
        leaves the refutation needed, relevant_premises_from_tstp must
        refuse (None), not guess that f1↦premise_1/f2↦premise_2 by position."""
        assert _relevant_axiom_names(_THEOREM_OUTPUT) == frozenset({"f1", "f2"})
        assert relevant_premises_from_tstp(_THEOREM_OUTPUT, n_premises=2) is None

    def test_no_fof_or_cnf_statements_is_none(self):
        assert _relevant_axiom_names("") is None
        assert relevant_premises_from_tstp("no proof here", n_premises=2) is None

    def test_countersatisfiable_fixture_is_not_a_refutation_so_none(self):
        """No $false step exists: E printed a Saturation report for a
        non-theorem, not a refutation, so no premise can be relevant to a
        proof -- even though the report's own clauses do descend from
        premise_1."""
        text = _recorded("countersatisfiable")
        assert _relevant_axiom_names(text) is None
        assert relevant_premises_from_tstp(text, n_premises=2) is None

    def test_a_derivation_without_false_is_none_however_it_is_shaped(self):
        """A chain premise_1 -> derived that never reaches $false derives
        nothing contradictory; guessing an "end of the DAG" instead would
        report premise_1 as relevant to a proof that is not there."""
        text = (
            "fof(premise_1, axiom, (human(socrates)), file('x.p', premise_1)).\n"
            "fof(premise_2, axiom, (bird(tweety)), file('x.p', premise_2)).\n"
            "fof(derived, plain, (mortal(socrates)),"
            "inference(resolution,[status(thm)],[premise_1])).\n"
        )
        assert _relevant_axiom_names(text) is None
        assert relevant_premises_from_tstp(text, n_premises=2) is None

    def test_two_disjoint_refutations_report_the_union(self):
        """Two $false steps resting on different premises: premise_1 and
        premise_2 both state p, the negated conjecture is ~p, and each sink
        resolves one of them against it -- two genuine refutations. Each leaf
        set is sufficient, so their union is too; the result is documented as
        sufficient, not minimal. Picking one of them would be a choice the
        text gives no ground for; refusing would discard a correct answer."""
        text = (
            "fof(premise_1, axiom, (p), file('x.p', premise_1)).\n"
            "fof(premise_2, axiom, (p), file('x.p', premise_2)).\n"
            "fof(neg, negated_conjecture, (~ p), file('x.p', neg)).\n"
            "fof(sink1, plain, $false,"
            "inference(resolution,[status(thm)],[premise_1,neg])).\n"
            "fof(sink2, plain, $false,"
            "inference(resolution,[status(thm)],[premise_2,neg])).\n"
        )
        assert _relevant_axiom_names(text) == frozenset({"premise_1", "premise_2"})
        assert relevant_premises_from_tstp(text, n_premises=2) == (0, 1)

    def test_a_cited_but_undefined_step_name_is_none(self):
        """A derivation excerpt that cites a step name never itself defined
        anywhere in the text -- an incomplete/truncated excerpt -- must
        refuse rather than silently treat the missing name as a dead end."""
        text = ("fof(sink,plain,$false,"
               "inference(r,[status(thm)],[missing_step])).")
        assert relevant_premises_from_tstp(text, n_premises=1) is None

    def test_axiom_leaf_outside_the_premise_naming_convention_is_none(self):
        text = ("fof(weird_axiom_name,axiom,p(a),file('x.p',unknown)).\n"
               "fof(sink,plain,$false,"
               "inference(r,[status(thm)],[weird_axiom_name])).")
        assert relevant_premises_from_tstp(text, n_premises=1) is None

    def test_out_of_range_premise_index_is_none(self):
        """premise_5 with only 2 premises supplied means this module's own
        naming convention was evidently not what produced this text (a stale
        n_premises, or text from an unrelated run) -- refuse, don't clamp."""
        text = ("fof(premise_5,axiom,p(a),file('x.p',unknown)).\n"
               "fof(sink,plain,$false,"
               "inference(r,[status(thm)],[premise_5])).")
        assert relevant_premises_from_tstp(text, n_premises=2) is None

    def test_hand_built_two_of_three_with_a_red_herring(self):
        """Independent, offline pin of the ancestor-walk ALGORITHM itself
        (not going through any recorded prover run): three premise_N
        axioms, premise_3 never cited by anything -- a textbook red herring,
        the same fixture shape used for z3_relevant_premises/cvc5's
        minimality tests, expressed directly as TSTP text."""
        text = (
            "fof(goal,conjecture,mortal(socrates),file('x.p',goal)).\n"
            "fof(premise_1,axiom,![X]:(human(X)=>mortal(X)),file('x.p',premise_1)).\n"
            "fof(premise_2,axiom,human(socrates),file('x.p',premise_2)).\n"
            "fof(premise_3,axiom,bird(tweety),file('x.p',premise_3)).\n"
            "fof(neg,negated_conjecture,~mortal(socrates),"
            "inference(negated_conjecture,[status(cth)],[goal])).\n"
            "cnf(c1,plain,mortal(socrates),"
            "inference(resolution,[status(thm)],[premise_1,premise_2])).\n"
            "fof(sink,plain,$false,"
            "inference(cn,[status(thm)],[c1,neg])).\n"
        )
        assert relevant_premises_from_tstp(text, n_premises=3) == (0, 1)

    def test_hand_built_redundant_premises_neither_forced_alone(self):
        """Two premise_N axioms that are each cited directly by the sink --
        the walk must report BOTH names that ARE reachable, without
        fabricating a preference; this pins the walk's behaviour on a
        derivation shape where the SINK itself already names two leaves
        directly (as opposed to Z3/cvc5's solver-level 'need not use both'
        minimality, which is a property of THEIR search, not of this purely
        structural graph walk)."""
        text = (
            "fof(premise_1,axiom,mortal(socrates),file('x.p',premise_1)).\n"
            "fof(premise_2,axiom,human(socrates),file('x.p',premise_2)).\n"
            "fof(sink,plain,$false,"
            "inference(cn,[status(thm)],[premise_1,premise_2])).\n"
        )
        assert relevant_premises_from_tstp(text, n_premises=2) == (0, 1)


# ---------------------------------------------------------------------------
# check_entailment_vampire_detailed (additive) -- via monkeypatched
# _spawn_vampire, so these run with no Vampire binary present.
# ---------------------------------------------------------------------------

class TestCheckEntailmentVampireDetailed:
    def _patch(self, monkeypatch, stdout: str, timed_out: bool = False):
        def fake_spawn(input_str, vampire_path, timeout=30, use_wsl=False, extra_args=()):
            # --proof tptp must always be requested by this route (the whole
            # point is to get a TSTP-parseable proof out of Vampire).
            assert extra_args == ("--proof", "tptp")
            return stdout, timed_out
        monkeypatch.setattr(
            "unicode_logic_kit.atp.vampire_entailment._spawn_vampire", fake_spawn)

    def test_theorem_with_derivation(self, monkeypatch):
        self._patch(monkeypatch, _THEOREM_OUTPUT)
        result = check_entailment_vampire_detailed(
            _MODUS_PONENS_PREMISES, _MORTAL, vampire_path="vampire")
        assert result["szs_status"] == "Theorem"
        assert result["status"] == P.PROVED
        assert result["reason"] is None
        assert result["derivation"] is not None
        assert len(result["derivation"]["steps"]) == 11
        assert result["output_excerpt"]  # non-empty, real output was short

    def test_countersatisfiable_has_no_derivation(self, monkeypatch):
        self._patch(monkeypatch, _COUNTERSAT_OUTPUT)
        result = check_entailment_vampire_detailed(
            [_FOL.parse("Human(socrates)")], _MORTAL, vampire_path="vampire")
        assert result["szs_status"] == "CounterSatisfiable"
        assert result["status"] == P.REFUTED
        assert result["reason"] is None
        # Vampire's model report has no fof/cnf lines -> caller-level None,
        # distinct from parse_tstp_derivation's own empty-tuple result.
        assert result["derivation"] is None

    def test_timeout_status_line(self, monkeypatch):
        self._patch(monkeypatch, _TIMEOUT_OUTPUT)
        result = check_entailment_vampire_detailed(
            _MODUS_PONENS_PREMISES, _MORTAL, vampire_path="vampire")
        assert result["szs_status"] == "Timeout"
        assert result["status"] == P.UNKNOWN
        assert result["reason"] == "timeout"
        assert result["derivation"] is None

    def test_subprocess_timeout_before_any_output(self, monkeypatch):
        """A hard subprocess.TimeoutExpired (Vampire killed mid-run, nothing
        printed) is distinct from Vampire choosing to print its OWN 'SZS
        status Timeout' line -- both must land on UNKNOWN/timeout, but this
        path never touches SZS/derivation parsing at all."""
        self._patch(monkeypatch, "", timed_out=True)
        result = check_entailment_vampire_detailed(
            _MODUS_PONENS_PREMISES, _MORTAL, vampire_path="vampire")
        assert result["szs_status"] is None
        assert result["status"] == P.UNKNOWN
        assert result["reason"] == "timeout"
        assert result["output_excerpt"] == ""
        assert result["derivation"] is None

    def test_no_szs_line_falls_back_to_substring_heuristic(self, monkeypatch):
        """A build/mode that never prints an SZS line at all still yields a
        defensible verdict via the same 'Refutation found' substring test
        check_logical_entailment_vampire uses -- this function is never
        STRICTLY less informative than the old bool-returning one. Output that
        says NEITHER (no SZS line, no refutation) while nothing cut Vampire off
        is not 'incomplete': Vampire refused the problem or died, so it is an
        ERROR/infra carrying Vampire's own text (see tests/test_prover_rejection.py,
        which pins that decision for every prover)."""
        # (1) the substring fallback: 'Refutation found' is a proof.
        self._patch(monkeypatch, "Refutation found. Thanks to Tanya!\n")
        result = check_entailment_vampire_detailed(
            _MODUS_PONENS_PREMISES, _MORTAL, vampire_path="vampire")
        assert result["szs_status"] is None
        assert result["status"] == P.PROVED
        assert result["reason"] is None

        # (2) the equivalent signal check_logical_entailment_vampire also
        # accepts: the words 'SZS status Theorem' without the comment marker the
        # SZS line reader requires, so there is no SZS line but still a verdict.
        self._patch(monkeypatch, "SZS status Theorem for problem\n")
        result = check_entailment_vampire_detailed(
            _MODUS_PONENS_PREMISES, _MORTAL, vampire_path="vampire")
        assert result["szs_status"] is None
        assert result["status"] == P.PROVED
        assert result["reason"] is None

        # (3) output that says nothing: no SZS line, no refutation, not timed
        # out -> the prover refused or died. ERROR/infra, and the prover's own
        # words stay in the excerpt so the refusal is never filed with the
        # problems that merely ran out of time.
        self._patch(monkeypatch, "Nothing found.\n")
        result = check_entailment_vampire_detailed(
            _MODUS_PONENS_PREMISES, _MORTAL, vampire_path="vampire")
        assert result["szs_status"] is None
        assert result["status"] == P.ERROR
        assert result["reason"] == "infra"
        assert "Nothing found." in result["output_excerpt"]

        # (4) and the empty output of a process that was NOT timed out is the
        # same refusal, not a timeout (a timeout is the separate, tested
        # UNKNOWN/timeout path of test_subprocess_timeout_before_any_output).
        self._patch(monkeypatch, "")
        result = check_entailment_vampire_detailed(
            _MODUS_PONENS_PREMISES, _MORTAL, vampire_path="vampire")
        assert result["szs_status"] is None
        assert result["status"] == P.ERROR
        assert result["reason"] == "infra"

    def test_output_excerpt_is_bounded_to_the_tail(self, monkeypatch):
        long_output = ("x" * 5000) + "\n% SZS status Theorem for x\n"
        self._patch(monkeypatch, long_output)
        result = check_entailment_vampire_detailed(
            _MODUS_PONENS_PREMISES, _MORTAL, vampire_path="vampire")
        assert len(result["output_excerpt"]) <= 4000
        # The tail (where the status line lives) must be kept, not the head.
        assert "SZS status Theorem" in result["output_excerpt"]

    def test_result_is_json_compatible(self, monkeypatch):
        import json
        self._patch(monkeypatch, _THEOREM_OUTPUT)
        result = check_entailment_vampire_detailed(
            _MODUS_PONENS_PREMISES, _MORTAL, vampire_path="vampire")
        json.dumps(result)  # must not raise

    def test_bad_vampire_path_raises_file_not_found(self):
        """No monkeypatch here: a genuinely wrong path must still surface
        FileNotFoundError, exactly like check_logical_entailment_vampire."""
        with pytest.raises(FileNotFoundError):
            check_entailment_vampire_detailed(
                _MODUS_PONENS_PREMISES, _MORTAL,
                vampire_path="definitely_not_a_real_vampire_binary_xyz")

    def test_non_first_order_input_is_rejected_before_running(self):
        modal_premise = MSFLParser(modal=True).parse("□Human(socrates)")
        with pytest.raises(NotImplementedError):
            check_entailment_vampire_detailed(
                [modal_premise], _MORTAL, vampire_path="vampire")


# ---------------------------------------------------------------------------
# Integration -- only when a Vampire binary is actually reachable, exercising
# the real subprocess path end to end (extra_args plumbing included).
# ---------------------------------------------------------------------------

import shutil
import subprocess

_VAMPIRE = shutil.which("vampire")


@pytest.mark.skipif(_VAMPIRE is None, reason="no Vampire binary on PATH")
def test_check_entailment_vampire_detailed_live():
    result = check_entailment_vampire_detailed(
        _MODUS_PONENS_PREMISES, _MORTAL, vampire_path=_VAMPIRE)
    assert result["status"] == P.PROVED
    assert result["szs_status"] == "Theorem"
    assert result["derivation"] is not None
    assert len(result["derivation"]["steps"]) > 0

    result = check_entailment_vampire_detailed(
        [_FOL.parse("Human(socrates)")], _MORTAL, vampire_path=_VAMPIRE)
    assert result["status"] == P.REFUTED
    assert result["szs_status"] == "CounterSatisfiable"


def _wsl_vampire_ok():
    try:
        result = subprocess.run(["wsl.exe", "vampire", "--version"],
                                capture_output=True, text=True, timeout=20)
        return result.returncode == 0 and "Vampire" in result.stdout
    except Exception:  # noqa: BLE001 -- any failure means "not available"
        return False


_WSL_VAMPIRE = _wsl_vampire_ok()


@pytest.mark.skipif(not _WSL_VAMPIRE, reason="no Vampire reachable via 'wsl vampire'")
def test_check_entailment_vampire_detailed_via_wsl_live():
    result = check_entailment_vampire_detailed(
        _MODUS_PONENS_PREMISES, _MORTAL, vampire_path="vampire", use_wsl=True)
    assert result["status"] == P.PROVED
    assert result["szs_status"] == "Theorem"
    assert result["derivation"] is not None
    steps = result["derivation"]["steps"]
    # The final step of a found refutation is the empty clause $false,
    # derived from at least one earlier named step.
    last = steps[-1]
    assert last["rule"] is not None
    assert len(last["parents"]) >= 1
