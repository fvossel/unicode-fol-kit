"""Tests for the MCP server layer (unicode_fol_kit.mcp).

The tool implementations are plain functions, so most tests call them
directly and assert against hand-derived expectations; two tests go through
the real MCP layer (``list_tools`` / ``call_tool``) to pin schema generation
and the wire path without spawning a transport. The whole module skips when
the optional ``mcp`` SDK is absent (the kit's ``[mcp]`` extra).
"""

import asyncio

import pytest

pytest.importorskip("mcp", reason="optional [mcp] extra not installed")

from unicode_fol_kit.mcp.server import (   # noqa: E402
    check_consistency,
    check_equivalence,
    check_formula,
    compare_formulas,
    create_server,
    detect_dialect,
    diagnose,
    dl_abox_consistent,
    dl_classify,
    dl_concept_satisfiable,
    dl_equivalent,
    dl_instance_check,
    dl_instance_retrieval,
    dl_parse_manchester,
    dl_subsumes,
    drs_to_fol,
    find_countermodel,
    get_signature,
    get_syntax_spec,
    list_backends,
    list_translations,
    normalize,
    parse_formula,
    probability_bounds,
    probability_query,
    prove,
    render,
    repair_formula,
    score_batch,
    translate,
    truth_table,
    verbalize,
)


def test_parse_formula_roundtrips_unicode():
    """∀x (P(x) → P(x)) parses in the fol dialect; the tool adds the unicode
    rendering next to the JSON AST so an LLM can read the result back."""
    result = parse_formula("∀x (P(x) → P(x))")
    assert result["ok"] is True
    assert result["dialect"] == "fol"
    assert result["unicode"] == "∀x (P(x) → P(x))"


def test_parse_formula_error_lists_every_dialect_attempt():
    """'P(' parses nowhere: ok=False and the errors list carries one entry
    per attempted dialect — the payload a repair loop feeds its fixer."""
    result = parse_formula("P(")
    assert result["ok"] is False
    assert result["errors"], "attempt list must not be empty"
    assert all("dialect" in e and "message" in e for e in result["errors"])


def test_check_formula_reports_free_variables():
    """P(x) is well-formed but open: is_closed False, x listed free —
    hand-checked against api.check's documented fields."""
    result = check_formula("P(x)")
    assert result["is_closed"] is False
    assert result["free_variables"] == ["x"]


def test_prove_tautology_via_default_chain():
    """∀x (P(x) → P(x)) is valid: the default fol chain answers proved at
    its first member (z3)."""
    verdict = prove("∀x (P(x) → P(x))")
    assert verdict["status"] == "proved"
    assert verdict["backend"] == "z3"


def test_prove_with_premises():
    """Modus ponens: P(alice), ∀x (P(x) → Q(x)) |= Q(alice)."""
    verdict = prove("Q(alice)",
                    premises=["P(alice)", "∀x (P(x) → Q(x))"])
    assert verdict["status"] == "proved"


def test_prove_unknown_backend_is_structured_error():
    """An unknown backend name raises ValueError inside the API; the tool
    surfaces it as a structured error dict, never a traceback string."""
    result = prove("P(alice)", backends=["no-such-prover"])
    assert result["error"]["type"] == "ValueError"
    assert "no-such-prover" in result["error"]["message"]


def test_prove_parse_failure_names_the_bad_premise():
    """Uniform error shape (review-hardened): EVERY parse failure is
    {"ok": False, "argument": <which input>, "errors": [...]} — a generic
    client checks result.get("ok") is False and reads "argument"."""
    result = prove("P(alice)", premises=["Q(alice)", "R("])
    assert result["ok"] is False
    assert result["argument"] == "premise[1]"
    assert result["errors"]


def test_all_multi_argument_tools_share_the_error_shape():
    """The conclusion, formula1/2 and countermodel-formula positions all
    answer with the SAME top-level shape — no per-tool nesting."""
    for result, argument in (
        (prove("R(", premises=[]), "conclusion"),
        (find_countermodel("R("), "formula"),
        (check_equivalence("R(", "P"), "formula1"),
        (check_equivalence("P", "R("), "formula2"),
    ):
        assert result["ok"] is False
        assert result["argument"] == argument
        assert result["errors"]


def test_translate_alc_concept_via_the_dl_grammar():
    """ALC concepts (⊓/∃-role syntax) parse via dl.parse_concept — the
    registered alc→modal edge is reachable through MCP (review-fixed: the
    FOL grammars can never produce a Concept)."""
    result = translate("Human ⊓ ∃hasChild.Doctor", "alc", "modal")
    assert result.get("ok") is not False
    assert result["path"] == ["concept_to_modal"]
    assert result["unicode"] == "Human ∧ ◇Doctor"


def test_find_countermodel_for_non_theorem():
    """P(alice) is not valid: a countermodel (P(alice) false) exists and the
    result carries the English explanation field."""
    result = find_countermodel("P(alice)")
    assert result.get("model") or result.get("witness")
    assert "explanation_nl" in result


def test_check_equivalence_commuted_conjunction():
    """P ∧ Q vs Q ∧ P: not syntax-equal, but equivalent — the ladder
    settles it at the canonical level (commutative operands sort), so the
    tri-state solver level need not run (logically_equivalent stays None)."""
    result = check_equivalence("P ∧ Q", "Q ∧ P")
    assert result["equivalent"] is True
    assert result["method_used"] == "canonical"
    assert result["syntax_equal"] is False
    assert result["structurally_equal"] is True
    assert result["logically_equivalent"] is None


def test_diagnose_one_round_with_suggestion():
    """'P(' cannot parse: ok False, converged False, and a non-empty
    suggestion — the MCP client is the fixer and iterates itself."""
    step = diagnose("P(")
    assert step["ok"] is False
    assert step["converged"] is False
    assert step["suggestion"]
    assert step["attempt"] == 1


def test_diagnose_clean_text_converges_immediately():
    step = diagnose("P(alice)")
    assert step["ok"] is True
    assert step["converged"] is True


def test_translate_modal_to_fol_standard_translation():
    """□P from modal to fol is the standard translation — hand-derived:
    ∀w0 (R(w, w0) → P(w0)) with the free anchor world w."""
    result = translate("□P", "modal", "fol")
    assert result["path"] == ["standard_translation"]
    assert result["unicode"] == "∀w0 (R(w, w0) → P(w0))"


def test_verbalize_renders_english():
    """Hand-checked against fol.to_english's deterministic phrasing."""
    result = verbalize("∀x (P(x) → Q(x))")
    assert result["english"] == "for every x, if x is p, then x is q"


def test_list_backends_names_registry_and_chains():
    """The introspection tool reflects the real registry: all seventeen
    backends registered (hets included), and the default chains never
    contain the expensive externals (isabelle, hets)."""
    result = list_backends()
    assert "z3" in result["registered"]
    assert "hets" in result["registered"]
    assert "isabelle" in result["registered"]
    assert "hets" not in result["default_chains"]["fol"]
    assert "isabelle" not in result["default_chains"]["fol"]


# ---------------------------------------------------------------------------
# The error-analysis / conversion wave
# ---------------------------------------------------------------------------

def test_normalize_nnf_de_morgan():
    """¬(P ∧ Q) in NNF is ¬P ∨ ¬Q (De Morgan) — hand-derived."""
    result = normalize("¬(P ∧ Q)", form="nnf")
    assert result["ok"] is True
    assert result["unicode"] == "¬P ∨ ¬Q"
    assert result["semantics"] == "equivalent"


def test_normalize_cnf_distributes_and_reports_horn():
    """P ∨ (Q ∧ R) distributes to (P ∨ Q) ∧ (P ∨ R); both clauses carry two
    POSITIVE literals, so the clausal form is not Horn — hand-derived."""
    result = normalize("P ∨ (Q ∧ R)", form="cnf")
    assert result["unicode"] == "(P ∨ Q) ∧ (P ∨ R)"
    assert result["is_horn"] is False


def test_normalize_skolemize_names_its_semantics():
    """∃x P(x) skolemizes to P(sk0); the result is only satisfiability-
    preserving and the semantics key must say so."""
    result = normalize("∃x P(x)", form="skolemize")
    assert result["unicode"] == "P(sk0)"
    assert result["semantics"] == "satisfiability-preserving"


def test_normalize_unknown_form_is_structured_error():
    result = normalize("P", form="no-such-form")
    assert result["error"]["type"] == "ValueError"
    assert "no-such-form" in result["error"]["message"]


def test_render_tptp_and_prover9_hand_pinned():
    """The kit's TPTP rendering lower-cases predicates and upper-cases
    variables (TPTP conventions); Prover9 keeps the kit's names."""
    assert render("∀x (P(x) → Q(x))", to="tptp")["rendered"] == \
        "(![X]: (p(X) => q(X)))"
    assert render("∀x (P(x) → Q(x))", to="prover9")["rendered"] == \
        "(all X (P(X) -> Q(X)))"


def test_render_casl_and_json_and_english():
    """casl embeds the default sort; json is the versioned serialize
    envelope (the one dict-valued target); english matches verbalize."""
    assert render("∀x (P(x) → Q(x))", to="casl")["rendered"] == \
        "forall x : Thing . (P(x) => Q(x))"
    envelope = render("P(alice)", to="json")["rendered"]
    assert envelope["schema_version"]
    assert envelope["root"]["_type"] == "Atom"
    assert render("∀x (P(x) → Q(x))", to="english")["rendered"] == \
        "for every x, if x is p, then x is q"


def test_render_smtlib_hand_pinned():
    """P(a) is one declare-sort/declare-fun preamble (Z3's own
    Solver.to_smt2(), deterministic for this single-symbol input) plus one
    (assert (P a)) and a trailing (set-logic ALL)/(check-sat) — hand-run and
    pinned; the round-trip/adversarial-name/refusal contract itself is
    covered by tests/test_smtlib_export.py, not re-tested here."""
    assert render("P(a)", to="smtlib")["rendered"] == (
        "(set-logic ALL)\n"
        "; benchmark generated from python API\n"
        "(set-info :status unknown)\n"
        "(declare-sort S 0)\n"
        "(declare-fun P (S) Bool)\n"
        "(declare-fun a () S)\n"
        "(assert\n"
        " (P a))\n"
        "(check-sat)\n"
    )


def test_render_smtlib_refuses_second_order_naming_the_construct():
    """A family without the requested rendering surfaces its OWN refusal —
    here to_z3's second-order rejection, reused (not reimplemented) by
    to_smtlib, plus the one sentence to_smtlib appends."""
    result = render("∃P P(a)", to="smtlib", dialect="second_order")
    assert result["error"]["type"] == "NotImplementedError"
    assert "econd-order" in result["error"]["message"]
    assert "SMT-LIB2 export is first-order only" in result["error"]["message"]


def test_render_unknown_target_is_structured_error():
    result = render("P", to="klingon")
    assert result["error"]["type"] == "ValueError"
    assert "smtlib" in result["error"]["message"]


def test_detect_dialect_tptp_and_unicode():
    """Annotated TPTP is nominated and parses as tptp; a unicode formula
    falls through to the mode ladder and parses as fol; candidates always
    end in the unicode catch-all."""
    tptp = detect_dialect("fof(a, axiom, ![X]: (p(X) => q(X))).")
    assert tptp["ok"] is True
    assert tptp["parsed_as"] == "tptp"
    assert tptp["candidates"][0] == "tptp"
    uni = detect_dialect("∀x (P(x) → Q(x))")
    assert uni["parsed_as"] == "fol"
    assert uni["candidates"][-1] == "unicode"


def test_compare_formulas_typo_prediction_full_breakdown():
    """Doog vs Dog: structurally and canonically different, but the
    namespace-aware aligner repairs the typo (aligned_exact_match True) and
    the vocabulary diff names exactly the two mismatched predicate symbols
    — the error-analysis answer an NL→FOL researcher wants."""
    result = compare_formulas("∀x (Doog(x) → Animal(x))",
                              "∀y (Dog(y) → Animal(y))")
    assert result["ok"] is True
    assert result["structural_equal"] is False
    assert result["canonical_exact_match"] is False
    assert result["aligned_exact_match"] is True
    assert result["aligned_predicted"] == "∀x (Dog(x) → Animal(x))"
    assert result["equivalence"]["equivalent"] is True
    vocab = result["vocabulary"]["predicates"]
    assert vocab["only_in_predicted"] == ["Doog/1"]
    assert vocab["only_in_gold"] == ["Dog/1"]
    assert vocab["shared"] == ["Animal/1"]


def test_compare_formulas_alpha_variants_match_canonically():
    """∀x P(x) vs ∀y P(y): different ASTs, same canonical form."""
    result = compare_formulas("∀x P(x)", "∀y P(y)")
    assert result["structural_equal"] is False
    assert result["canonical_exact_match"] is True


def test_compare_formulas_parse_failure_names_the_side():
    result = compare_formulas("P(", "Q")
    assert result["ok"] is False
    assert result["argument"] == "predicted"
    result = compare_formulas("P", "Q(")
    assert result["argument"] == "gold"


def test_score_batch_half_right_corpus():
    """[P(alice), Q(bob)] vs [P(alice), R(bob)]: first pair AST-equal,
    second pair provably NOT equivalent (Q vs R too far to align, solver
    refutes) — exact_match and equivalence_accuracy both 0.5."""
    result = score_batch(["P(alice)", "Q(bob)"], ["P(alice)", "R(bob)"])
    assert result["ok"] is True
    assert result["n"] == 2
    assert result["exact_match"] == 0.5
    assert result["equivalence_accuracy"] == 0.5
    assert result["parse_failure_rate"] == 0.0


def test_score_batch_length_mismatch_is_structured_error():
    result = score_batch(["P"], [])
    assert result["error"]["type"] == "ValueError"


# ---------------------------------------------------------------------------
# converses: declared converse/argument-permutation bridging axioms.
# ---------------------------------------------------------------------------

_LOVED_BY_JSON = [{"a": ["LovedBy", 2], "b": ["Loves", 2], "permutation": [1, 0]}]
_LOVED_BY_TUPLE = (("LovedBy", 2), ("Loves", 2), (1, 0))


def test_compare_formulas_converses_json_form_matches_python_tuple_form():
    """The JSON-dict declaration round-trips to the SAME verdict the
    Python-tuple form gives directly through eval.equivalent — the wire
    shape is just a re-spelling, not a different code path."""
    from unicode_fol_kit import equivalent as _equivalent
    from unicode_fol_kit.mcp.server import _parse

    result = compare_formulas("Loves(a, b)", "LovedBy(b, a)",
                              converses=_LOVED_BY_JSON)
    assert result["equivalence"]["equivalent"] is True
    assert result["equivalence"]["method_used"] == "solver_modulo_converses"
    assert result["converse_axioms_applied"] == [
        "∀v0 ∀v1 (LovedBy(v0, v1) ↔ Loves(v1, v0))"]

    pred, _ = _parse("Loves(a, b)", None)
    gold, _ = _parse("LovedBy(b, a)", None)
    direct = _equivalent(pred, gold, converses=[_LOVED_BY_TUPLE])
    assert direct.equivalent == result["equivalence"]["equivalent"]
    assert direct.method_used == result["equivalence"]["method_used"]


def test_compare_formulas_converses_none_leaves_field_none():
    result = compare_formulas("P(a)", "P(a)")
    assert result["converse_axioms_applied"] is None


def test_compare_formulas_malformed_converses_json_is_top_level_error():
    """A malformed WIRE shape (missing "permutation") is caught before
    api.equivalent is even called -- the top-level {"error": {...}} shape,
    per the JSON-normalisation/field-scoped error split documented on
    compare_formulas."""
    result = compare_formulas("Loves(a, b)", "LovedBy(b, a)",
                              converses=[{"a": ["LovedBy", 2], "b": ["Loves", 2]}])
    assert "ok" not in result                       # top-level {"error": {...}} shape
    assert result["error"]["type"] == "ValueError"
    assert "converses[0]" in result["error"]["message"]


def test_compare_formulas_invalid_converse_declaration_is_field_scoped_error():
    """A well-shaped but semantically invalid declaration (self-pair) is a
    ValueError raised INSIDE the equivalence computation, so it lands in
    equivalence.error, not the top-level error -- the correction the
    roadmap review made versus the original spec."""
    result = compare_formulas(
        "Loves(a, b)", "Loves(b, a)",
        converses=[{"a": ["Loves", 2], "b": ["Loves", 2], "permutation": [1, 0]}])
    assert "error" not in result
    assert "own converse" in result["equivalence"]["error"]


def test_score_batch_converses_adds_converse_matched_rate():
    result = score_batch(["Loves(a, b)"], ["LovedBy(b, a)"], method="solver",
                         converses=_LOVED_BY_JSON)
    assert result["ok"] is True
    assert result["converse_matched_rate"] == 1.0
    assert result["equivalence_accuracy"] == 1.0


def test_score_batch_converses_none_keeps_six_key_dict():
    result = score_batch(["P(a)"], ["P(a)"])
    assert "converse_matched_rate" not in result


_MODAL_CONVERSE = [{"a": ["P", 0], "b": ["Q", 0], "permutation": []}]


def test_compare_formulas_modal_pair_with_converses_is_field_scoped_error():
    """eval.equivalent() deliberately raises NotImplementedError for a modal
    pair with non-empty converses (no modal bridging route exists -- see
    tests/test_converses.py's test_modal_pair_with_converses_raises_not_implemented
    for the direct-call proof). Through this tool that must land in
    equivalence.error, the SAME structured shape a ValueError gets here (see
    test_compare_formulas_invalid_converse_declaration_is_field_scoped_error
    above) -- never escape as a raw, uncaught exception."""
    result = compare_formulas("□P", "□Q", converses=_MODAL_CONVERSE)
    assert "error" not in result                    # not the top-level shape
    assert result["ok"] is True
    assert "modal" in result["equivalence"]["error"]


def test_score_batch_modal_pair_with_converses_is_structured_error():
    """Same NotImplementedError case as compare_formulas above, through
    score_batch: must come back as the tool's {"error": {...}} shape, not a
    raw exception."""
    result = score_batch(["□P"], ["□Q"], method="solver",
                         converses=_MODAL_CONVERSE)
    assert "ok" not in result
    assert result["error"]["type"] == "NotImplementedError"
    assert "modal" in result["error"]["message"]


def test_call_tool_compare_formulas_modal_converses_over_the_wire_path():
    """The in-process function calls above prove the exception is caught;
    this proves it survives the REAL MCP call_tool dispatch too -- the
    reviewer's concern was specifically that an uncaught NotImplementedError
    would surface as a protocol-level crash rather than a normal tool
    response over the wire, which the in-process calls alone cannot show."""
    import json

    server = create_server()
    result = asyncio.run(server.call_tool(
        "compare_formulas",
        {"predicted": "□P", "gold": "□Q", "converses": _MODAL_CONVERSE}))
    payload = getattr(result, "structured_content", None)
    if payload is None:
        payload = json.loads(result.content[0].text)
    assert payload["ok"] is True
    assert "modal" in payload["equivalence"]["error"]


def test_check_consistency_satisfiable_set_carries_model():
    """{P(alice), ∀x (P(x) → Q(x))} is satisfiable: a model witness comes
    back with the English gloss."""
    result = check_consistency(["P(alice)", "∀x (P(x) → Q(x))"])
    assert result["consistent"] is True
    assert result["method"] == "model"
    assert result["model"] is not None


def test_check_consistency_contradictory_set_is_refuted():
    """{P(alice), ¬P(alice)} entails the fresh contradiction — consistent
    False with the proving verdict attached."""
    result = check_consistency(["P(alice)", "¬P(alice)"])
    assert result["consistent"] is False
    assert result["method"] == "refutation"
    assert result["verdict"]["status"] == "proved"


def test_check_consistency_fresh_atom_dodges_the_vocabulary():
    """A theory that already uses the ufk_absurd predicate name (expressible
    via the TPTP dialect — the unicode surface grammar has no underscores)
    must not confuse the encoding: the fresh atom picks a longer name."""
    result = check_consistency(["fof(a, axiom, ufk_absurd)."])
    assert result["consistent"] is True


def test_get_signature_extracts_vocabulary():
    """Two formulas about dogs: predicates Dog/1 + Animal/1, constant rex —
    the dict is ready to feed back as check_formula's signature."""
    result = get_signature(["∀x (Dog(x) → Animal(x))", "Dog(rex)"])
    assert result["ok"] is True
    sig = result["signature"]
    arities = {name: decl["arity"] for name, decl in sig["predicates"].items()}
    assert arities == {"Dog": 1, "Animal": 1}
    assert list(sig["constants"]) == ["rex"]


def test_truth_table_classical_conditional():
    """P → Q: four rows in value order (1,1),(1,0),(0,1),(0,0) with values
    1,0,1,1 — hand-derived; satisfiable but no tautology."""
    result = truth_table("P → Q")
    assert result["atoms"] == ["P", "Q"]
    assert [row["value"] for row in result["rows"]] == [1.0, 0.0, 1.0, 1.0]
    assert result["is_tautology"] is False
    assert result["is_satisfiable"] is True
    assert result["markdown"].startswith("| P | Q |")


def test_truth_table_excluded_middle_k3_vs_lp():
    """P ∨ ¬P valued ½ at P=½: NOT a K3 tautology (½ undesignated) but an
    LP tautology (½ designated) — the classic three-valued contrast."""
    assert truth_table("P ∨ ¬P", logic="K3")["is_tautology"] is False
    assert truth_table("P ∨ ¬P", logic="LP")["is_tautology"] is True


def test_truth_table_refuses_non_propositional_nodes_structurally():
    """A modal formula walks past the atom collector (only quantifiers are
    caught there) and dies in the Kleene evaluator — that refusal must be
    the structured error shape, never a leaked traceback (review-hardened)."""
    result = truth_table("□P")
    assert result.get("ok") is not True
    assert "error" in result


def test_probability_bounds_refuses_json_booleans():
    """bool is an int subclass, but JSON true is not a probability — the
    adapter must refuse it loudly instead of reading it as 1
    (review-hardened)."""
    result = probability_bounds(
        "A", [{"formula": "A", "probability": True}])
    assert result["error"]["type"] == "ValueError"
    assert "bool" in result["error"]["message"]


def test_truth_table_refuses_quantifiers_and_blowups():
    assert truth_table("∀x P(x)")["error"]["type"] == "ValueError"
    wide = " ∨ ".join(f"P{i}" for i in range(1, 14))     # 2^13 = 8192 rows
    result = truth_table(wide)
    assert result["error"]["type"] == "ValueError"
    assert "cap" in result["error"]["message"]


def test_drs_to_fol_donkey_sentence():
    """The classic donkey box: the indefinite in the conditional's
    antecedent comes out UNIVERSAL — the reading plain compositional FOL
    gets wrong and DRT's standard translation gets right."""
    result = drs_to_fol(
        "[x, y | Farmer(x), Donkey(y), Owns(x, y)] -> [ | Beats(x, y)]")
    assert result["ok"] is True
    assert result["unicode"] == \
        "∀x ∀y (Farmer(x) ∧ Donkey(y) ∧ Owns(x, y) → Beats(x, y))"


def test_drs_to_fol_resolves_pronouns_when_asked():
    """A PRONOUN-marked referent with exactly one accessible antecedent
    resolves to an equality before translation."""
    result = drs_to_fol("[x, y | Farmer(x), PRONOUN(y), Sleeps(y)]",
                        resolve_pronouns=True)
    assert result["ok"] is True
    assert len(result["resolutions"]) == 1
    assert result["resolutions"][0]["antecedent"] == "x"


def test_drs_to_fol_error_shapes():
    """A syntax error keeps the uniform {ok, argument, errors} parse-error
    shape; an unknown format is a structured error."""
    bad = drs_to_fol("[x | Farmer(x)")
    assert bad["ok"] is False
    assert bad["argument"] == "text"
    assert bad["errors"][0]["dialect"] == "drs_box"
    assert drs_to_fol("[ | P(a)]", format="klingon")["error"]["type"] == \
        "ValueError"


def test_probability_bounds_nilsson_classic():
    """P(A)=0.7, P(A→B)=0.8 entail P(B) ∈ [1/2, 4/5] — Nilsson's classic,
    hand-derived over the four worlds (w_A¬B is pinned to 1/5, w_AB to
    1/2, the remaining 3/10 floats between the two ¬A worlds). Fraction
    strings and JSON floats must land on the same exact answer."""
    for probs in (("7/10", "4/5"), (0.7, 0.8)):
        result = probability_bounds(
            "B", [{"formula": "A", "probability": probs[0]},
                  {"formula": "A → B", "probability": probs[1]}])
        assert result["ok"] is True
        assert result["lower"] == "1/2"
        assert result["upper"] == "4/5"
    assert result["n_worlds"] == 4


def test_probability_bounds_conditional_and_inconsistency():
    """P(B|A)=9/10 with P(A)=1/2 forces P(A∧B)=9/20 exactly; contradictory
    point constraints are refused as probabilistically inconsistent."""
    result = probability_bounds(
        "A ∧ B", [{"formula": "A", "probability": "1/2"},
                  {"formula": "B", "given": "A", "probability": "9/10"}])
    assert result["lower"] == "9/20"
    assert result["upper"] == "9/20"
    bad = probability_bounds(
        "A", [{"formula": "A", "probability": 1},
              {"formula": "¬A", "probability": 1}])
    assert bad["error"]["type"] == "ValueError"
    assert "inconsistent" in bad["error"]["message"]


def test_probability_bounds_strategy_passthrough_matches_direct():
    """strategy/max_columns travel through to
    prob.nilsson.entailment_bounds unchanged: column_generation must land
    on the SAME hand-derived bounds as the direct strategy on the classic
    P(A)=0.7, P(A→B)=0.8 ⊢ P(B) ∈ [1/2, 4/5] example (see
    test_probability_bounds_nilsson_classic above) -- exactly the
    differential the two algorithms are held to agree on exactly, never a
    tolerance (tests/test_nilsson_colgen.py)."""
    constraints = [{"formula": "A", "probability": "7/10"},
                  {"formula": "A → B", "probability": "4/5"}]
    direct = probability_bounds("B", constraints)
    colgen = probability_bounds("B", constraints, strategy="column_generation")
    assert direct["ok"] is True and colgen["ok"] is True
    assert colgen["lower"] == direct["lower"] == "1/2"
    assert colgen["upper"] == direct["upper"] == "4/5"


def test_probability_bounds_strategy_bypasses_max_atoms():
    """13 distinct atoms exceed the direct strategy's max_atoms=12 default
    (refused loudly, the O(2^n) brake); column_generation is exactly the
    escape hatch. Hand-derived like tests/test_nilsson_colgen.py's own
    thirteen-atom case: P(S0)=1/2 forces the OR-of-13 conclusion's
    probability into [1/2, 1] regardless of which strategy answers it
    (atom0=True forces the OR true; atom0=False mass can be routed onto an
    all-remaining-false world for the min, or an OR-true world for the
    max)."""
    conclusion = " ∨ ".join(f"S{i}" for i in range(13))
    constraints = [{"formula": "S0", "probability": "1/2"}]
    refused = probability_bounds(conclusion, constraints)
    assert refused["error"]["type"] == "ValueError"
    assert "max_atoms" in refused["error"]["message"]
    colgen = probability_bounds(conclusion, constraints,
                                strategy="column_generation")
    assert colgen["ok"] is True
    assert colgen["lower"] == "1/2"
    assert colgen["upper"] == "1"
    assert colgen["n_worlds"] == 2 ** 13


def test_probability_bounds_max_columns_brake():
    """max_columns travels through too: capped at 1 on a problem that
    needs more, column_generation refuses rather than ever returning an
    unproven bound (mirrors tests/test_nilsson_colgen.py's own brake
    test)."""
    result = probability_bounds(
        "B", [{"formula": "A", "probability": "7/10"},
              {"formula": "A → B", "probability": "4/5"}],
        strategy="column_generation", max_columns=1)
    assert result["error"]["type"] == "ValueError"
    assert "max_columns" in result["error"]["message"]


def test_probability_bounds_refuses_unknown_strategy():
    result = probability_bounds(
        "A", [{"formula": "A", "probability": "1"}], strategy="bogus")
    assert result["error"]["type"] == "ValueError"
    assert "bogus" in result["error"]["message"]


def test_probability_query_alarm_classic():
    """burglary 1/10, earthquake 1/5, alarm from either: P(alarm) =
    1 − (9/10)(4/5) = 7/25 — the distribution-semantics classic."""
    result = probability_query(
        "Alarm",
        facts=[{"atom": "Burglary", "prob": "1/10"},
               {"atom": "Earthquake", "prob": "1/5"}],
        rules=["Burglary → Alarm", "Earthquake → Alarm"])
    assert result["ok"] is True
    assert result["probability"] == "7/25"
    assert result["probability_float"] == 0.28


def test_probability_query_refuses_non_definite_rules():
    """Negation in a rule body is outside the definite fragment — loud
    structured refusal, never a silent approximation."""
    result = probability_query(
        "Alarm", facts=[{"atom": "Burglary", "prob": "1/10"}],
        rules=["¬Burglary → Alarm"])
    assert result["error"]["type"] == "ValueError"


def test_list_translations_names_the_default_edges():
    result = list_translations()
    names = {e["name"] for e in result["edges"]}
    assert {"concept_to_fol", "concept_to_modal", "standard_translation",
            "dependence_to_eso"} <= names
    assert all(set(e) == {"name", "source", "target", "lossy", "note"}
               for e in result["edges"])


# ---------------------------------------------------------------------------
# Description logic (dl_*): ALCHQ tableau reasoning + OWL Manchester Syntax.
#
# The family ontology below is docs/guide/description-logic.md's own
# "End-to-end: a small family ontology" (Parent ≡ Person ⊓ ∃hasChild.Person,
# Mother ≡ Parent ⊓ Female, Father ≡ Parent ⊓ Male, Male ⊑ ¬Female) —
# hand-checked there (and independently re-derived below) precisely so
# these tests are the second, TEXT-in/JSON-out route to already-known
# answers, not a tautological check of the wrapper against itself.
# ---------------------------------------------------------------------------

_FAMILY_TBOX = [
    {"equiv": ["Parent", "Person ⊓ ∃hasChild.Person"]},
    {"equiv": ["Mother", "Parent ⊓ Female"]},
    {"equiv": ["Father", "Parent ⊓ Male"]},
    {"sub": "Male", "sup": "¬Female"},
]


def test_dl_concept_satisfiable_hand_checked_contradiction():
    """'A ⊓ ¬A' is the textbook unsatisfiable concept; a bare atomic concept
    is trivially satisfiable. Differential-checked against calling
    dl.concept_satisfiable directly on the identically-parsed Concept, per
    this item's own test_oracle."""
    import unicode_fol_kit.dl as dl

    contradiction = dl_concept_satisfiable("A ⊓ ¬A")
    assert contradiction == {"ok": True, "satisfiable": False,
                             "concept_unicode": "A ⊓ ¬A"}
    assert contradiction["satisfiable"] == dl.concept_satisfiable(
        dl.parse_concept("A ⊓ ¬A"))

    trivial = dl_concept_satisfiable("Person")
    assert trivial["satisfiable"] is True


def test_dl_concept_satisfiable_manchester_syntax():
    """The same contradiction, spelled in OWL Manchester Syntax
    (syntax='manchester') rather than the ALC glyph default."""
    result = dl_concept_satisfiable("Person and not Person", syntax="manchester")
    assert result == {"ok": True, "satisfiable": False,
                      "concept_unicode": "Person ⊓ ¬Person"}


def test_dl_subsumes_family_ontology_hand_checked():
    """Mother ⊑ Parent ⊑ Person (both True — Mother ≡ Parent ⊓ Female, so
    every Mother is a Parent, hence a Person); the converse Parent ⊑ Mother
    is False (not every parent is a mother). Same three cases as the docs
    guide's worked example."""
    mother_parent = dl_subsumes("Mother", "Parent", tbox=_FAMILY_TBOX)
    assert mother_parent == {"ok": True, "subsumes": True,
                             "sub_unicode": "Mother", "sup_unicode": "Parent"}
    assert dl_subsumes("Mother", "Person", tbox=_FAMILY_TBOX)["subsumes"] is True
    assert dl_subsumes("Parent", "Mother", tbox=_FAMILY_TBOX)["subsumes"] is False


def test_dl_subsumes_differential_against_the_dl_module_directly():
    """The MCP wrapper's verdict must agree with calling dl.subsumes on the
    identically-built TBox/Concepts (the differential half of this item's
    test_oracle)."""
    import unicode_fol_kit.dl as dl

    Person, Female, Male = dl.Atomic("Person"), dl.Atomic("Female"), dl.Atomic("Male")
    Parent, Mother, Father = dl.Atomic("Parent"), dl.Atomic("Mother"), dl.Atomic("Father")
    t = (dl.TBox()
         .add_equivalence(Parent, dl.And(Person, dl.Exists("hasChild", Person)))
         .add_equivalence(Mother, dl.And(Parent, Female))
         .add_equivalence(Father, dl.And(Parent, Male))
         .add(Male, dl.Not(Female)))
    for sub, sup in (("Mother", "Parent"), ("Mother", "Person"), ("Parent", "Mother")):
        via_tool = dl_subsumes(sub, sup, tbox=_FAMILY_TBOX)["subsumes"]
        via_dl = dl.subsumes(dl.Atomic(sub), dl.Atomic(sup), t)
        assert via_tool == via_dl


def test_dl_concept_satisfiable_mother_and_father_are_disjoint():
    """Mother ⊓ Father is unsatisfiable: a Mother is Female, a Father is
    Male, and Male ⊑ ¬Female rules out both at once — the docs guide's own
    disjointness check."""
    result = dl_concept_satisfiable("Mother ⊓ Father", tbox=_FAMILY_TBOX)
    assert result["satisfiable"] is False


def test_dl_equivalent_de_morgan():
    """¬(A ⊓ B) ≡ ¬A ⊔ ¬B — De Morgan, decided by mutual subsumption over
    the empty TBox."""
    result = dl_equivalent("¬(A ⊓ B)", "¬A ⊔ ¬B")
    assert result == {"ok": True, "equivalent": True,
                      "c_unicode": "¬(A ⊓ B)", "d_unicode": "¬A ⊔ ¬B"}
    # A non-equivalence: ⊓ is not ⊔.
    assert dl_equivalent("A ⊓ B", "A ⊔ B")["equivalent"] is False


def test_dl_abox_consistent_family_ontology_hand_checked():
    """Alice a Mother with child Bob a Person is consistent; asserting Alice
    is ALSO Male is inconsistent (Male ⊑ ¬Female, but Mother ⊑ Female) —
    the docs guide's own two ABox cases."""
    ok_kb = dl_abox_consistent(
        [["alice", "Mother"], ["bob", "Person"]],
        roles=[["alice", "bob", "hasChild"]], tbox=_FAMILY_TBOX)
    assert ok_kb == {"ok": True, "consistent": True}

    bad_kb = dl_abox_consistent(
        [["alice", "Mother"], ["alice", "Male"]], tbox=_FAMILY_TBOX)
    assert bad_kb == {"ok": True, "consistent": False}


def test_dl_abox_consistent_no_unique_name_assumption():
    """Without an explicit distinctness assertion, two hasChild-successors of
    alice are free to denote the SAME individual, so a ≤1 hasChild.⊤ bound is
    satisfied by merging them (consistent); asserting bob ≠ carol blocks that
    merge and the same KB becomes inconsistent — dl.tableau's own 'no unique
    name assumption' contract (see its module docstring), reached here purely
    through the ABox JSON shape's 'distinct' rows."""
    roles = [["alice", "bob", "hasChild"], ["alice", "carol", "hasChild"]]
    tbox = [{"sub": "⊤", "sup": "≤1 hasChild.⊤"}]
    mergeable = dl_abox_consistent([], roles=roles, tbox=tbox)
    assert mergeable["consistent"] is True
    blocked = dl_abox_consistent([], roles=roles, tbox=tbox,
                                 distinct=[["bob", "carol"]])
    assert blocked["consistent"] is False


def test_dl_instance_check_and_retrieval_family_ontology():
    """Alice (a Mother, hence Parent, hence Person) and Bob (asserted Person
    directly) are both entailed Person; instance_retrieval finds exactly
    both, in sorted order."""
    concepts = [["alice", "Mother"], ["bob", "Person"]]
    roles = [["alice", "bob", "hasChild"]]
    check = dl_instance_check("alice", "Person", concepts, roles=roles,
                              tbox=_FAMILY_TBOX)
    assert check == {"ok": True, "entailed": True, "individual": "alice",
                     "concept_unicode": "Person"}
    retrieval = dl_instance_retrieval("Person", concepts, roles=roles,
                                      tbox=_FAMILY_TBOX)
    assert retrieval == {"ok": True, "individuals": ["alice", "bob"],
                         "concept_unicode": "Person"}
    # Open-world: nothing entails alice is a Father.
    assert dl_instance_check("alice", "Father", concepts, roles=roles,
                             tbox=_FAMILY_TBOX)["entailed"] is False


def test_dl_classify_family_ontology_hierarchy():
    """Reproduces docs/guide/description-logic.md's own classify() values
    exactly: Person's only direct child is Parent; Parent's direct children
    are Father/Mother; Mother's direct parents are Female and Parent (Person
    is only an ancestor, reached via Parent); Mother's full ancestor set adds
    Person on top."""
    result = dl_classify(_FAMILY_TBOX)
    assert result["ok"] is True
    assert result["children"]["Person"] == ["Parent"]
    assert result["children"]["Parent"] == ["Father", "Mother"]
    assert result["parents"]["Mother"] == ["Female", "Parent"]
    assert result["ancestors"]["Mother"] == ["Female", "Parent", "Person"]
    assert result["equivalents"]["Mother"] == ["Mother"]     # no synonyms


def test_dl_classify_differential_against_the_dl_module_directly():
    """classify()'s tool payload must agree with calling dl.classify on the
    identically-built TBox (this item's differential test_oracle, applied to
    classify as well as the four core reasoning tools)."""
    import unicode_fol_kit.dl as dl

    Person, Female, Male = dl.Atomic("Person"), dl.Atomic("Female"), dl.Atomic("Male")
    Parent, Mother, Father = dl.Atomic("Parent"), dl.Atomic("Mother"), dl.Atomic("Father")
    t = (dl.TBox()
         .add_equivalence(Parent, dl.And(Person, dl.Exists("hasChild", Person)))
         .add_equivalence(Mother, dl.And(Parent, Female))
         .add_equivalence(Father, dl.And(Parent, Male))
         .add(Male, dl.Not(Female)))
    via_dl = dl.classify(t)
    via_tool = dl_classify(_FAMILY_TBOX)
    assert via_tool["children"]["Parent"] == sorted(via_dl.children["Parent"])
    assert via_tool["ancestors"]["Mother"] == sorted(via_dl.ancestors["Mother"])


def test_dl_parse_manchester_concept_and_roundtrip():
    """'hasChild some (Doctor and not Rich)' — the W3C-style example from
    dl.owl_manchester's own docstring. Round-tripping the reported
    'manchester' text back through the same tool reproduces the identical
    concept_unicode (parse_manchester(to_manchester(c)) == c, checked
    structurally at the dl level too)."""
    import unicode_fol_kit.dl as dl

    first = dl_parse_manchester("hasChild some (Doctor and not Rich)")
    assert first == {"ok": True,
                     "concept_unicode": "∃hasChild.(Doctor ⊓ ¬Rich)",
                     "manchester": "hasChild some (Doctor and not Rich)"}
    second = dl_parse_manchester(first["manchester"])
    assert second["concept_unicode"] == first["concept_unicode"]
    assert dl.parse_manchester(first["manchester"]) == dl.parse_manchester(
        "hasChild some (Doctor and not Rich)")


def test_dl_parse_manchester_axiom_and_role_axiom():
    """kind='axiom' reaches parse_manchester_axiom; kind='role_axiom' reaches
    parse_manchester_role_axiom — both of dl.owl_manchester's own hand-
    checked docstring examples."""
    axiom = dl_parse_manchester(
        "Doctor SubClassOf hasChild some owl:Thing", kind="axiom")
    assert axiom == {"ok": True, "kind": "subclass",
                     "sub_unicode": "Doctor", "sup_unicode": "∃hasChild.⊤"}

    subprop = dl_parse_manchester(
        "hasChild SubPropertyOf hasDescendant", kind="role_axiom")
    assert subprop == {"ok": True, "kind": "subproperty",
                       "sub_role": "hasChild", "super_role": "hasDescendant"}

    trans = dl_parse_manchester(
        "hasDescendant Characteristics: Transitive", kind="role_axiom")
    assert trans == {"ok": True, "kind": "transitive", "role": "hasDescendant"}


def test_dl_parse_manchester_unknown_kind_is_structured_error():
    result = dl_parse_manchester("Person", kind="nope")
    assert result["error"]["type"] == "ValueError"


def test_dl_tools_report_bad_concept_text_in_the_uniform_shape():
    """A syntax error in ANY concept-text argument comes back ok=False, with
    'argument' naming which one and spec_topic pointing at the dedicated
    description-logic topic — the same uniform shape every other tool's
    text arguments use (see the module docstring)."""
    for result, argument in (
        (dl_concept_satisfiable("Person ⊓"), "concept"),
        (dl_subsumes("Person ⊓", "Person"), "sub"),
        (dl_subsumes("Person", "Person ⊓"), "sup"),
        (dl_equivalent("Person ⊓", "Person"), "c"),
        (dl_equivalent("Person", "Person ⊓"), "d"),
    ):
        assert result["ok"] is False
        assert result["argument"] == argument
        assert result["errors"][0]["dialect"] == "alc"
        assert result["spec_topic"] == "description-logic"


def test_dl_parse_manchester_rejects_constructs_outside_alc():
    """'value' restrictions are real Manchester syntax but outside ALCHQ —
    dl.owl_manchester rejects them by NAME (see its own module docstring's
    'Rejected constructs'); the tool surfaces that as the uniform ok=False
    shape, naming the construct in the message."""
    result = dl_parse_manchester("hasChild value Doctor")
    assert result["ok"] is False
    assert result["argument"] == "text"
    assert "value restrictions" in result["errors"][0]["message"]
    assert result["spec_topic"] == "description-logic"


def test_dl_non_simple_role_error_is_a_structured_error():
    """A qualified number restriction on a transitive role is refused by
    dl.tableau's own NonSimpleRoleError (undecidable otherwise — see its
    module docstring) — reported as {"error": {...}}, not the text-parse
    ok=False shape, since the CONCEPT parsed fine and it is the REASONING
    step that refuses the combination."""
    result = dl_concept_satisfiable(
        "≥2 hasChild.Person", tbox=[{"transitive": "hasChild"}])
    assert result["error"]["type"] == "NonSimpleRoleError"
    assert "hasChild" in result["error"]["message"]


def test_dl_unknown_syntax_is_a_structured_error():
    result = dl_concept_satisfiable("Person", syntax="bogus")
    assert result["error"]["type"] == "ValueError"
    assert "bogus" in result["error"]["message"]


def test_dl_unknown_syntax_is_refused_even_when_no_row_ever_parses():
    """dl_classify() and dl_abox_consistent(concepts=[]) can both run their
    entire row-building loop zero times (no tbox rows, no concepts/roles/
    distinct rows), so an invalid ``syntax`` is never seen by _parse_dl.
    Both tools must still refuse it unconditionally, not silently succeed."""
    classify_result = dl_classify(syntax="bogus")
    assert classify_result["error"]["type"] == "ValueError"
    assert "bogus" in classify_result["error"]["message"]

    abox_result = dl_abox_consistent(concepts=[], syntax="bogus")
    assert abox_result["error"]["type"] == "ValueError"
    assert "bogus" in abox_result["error"]["message"]

    # Same for the "everything omitted" call shapes, which hit the identical
    # empty-loop path via the parameters' own defaults.
    assert dl_classify(syntax="bogus")["error"]["type"] == "ValueError"
    assert dl_abox_consistent([], syntax="bogus")["error"]["type"] == "ValueError"


def test_dl_tbox_row_shapes_and_a_malformed_row_is_structured_error():
    """All four TBox row shapes (sub/sup, equiv, subrole/suprole,
    transitive) build a working TBox; a row matching none of them is a
    caller/config mistake, {"error": {"type": "ValueError", ...}}."""
    tbox = [
        {"sub": "A", "sup": "B"},
        {"equiv": ["C", "D"]},
        {"subrole": "r", "suprole": "s"},
        {"transitive": "s"},
    ]
    # r ⊑ s, Trans(s): an r-successor chain counts as an s-successor chain.
    result = dl_subsumes("∃r.∃r.A", "∃s.A", tbox=tbox)
    assert result["subsumes"] is True

    malformed = dl_concept_satisfiable("A", tbox=[{"nonsense": "row"}])
    assert malformed["error"]["type"] == "ValueError"
    assert "nonsense" in malformed["error"]["message"]      # names the KEYS
    assert "'sub'+'sup'" in malformed["error"]["message"]   # and the valid ones


def test_dl_abox_row_shapes_and_a_malformed_row_is_structured_error():
    good = dl_abox_consistent(
        concepts=[["a", "P"]], roles=[["a", "b", "r"]], distinct=[["a", "b"]])
    assert good["ok"] is True

    bad_concepts = dl_abox_consistent(concepts=[["a", "P", "extra"]])
    assert bad_concepts["error"]["type"] == "ValueError"
    bad_roles = dl_abox_consistent(concepts=[], roles=[["a", "b"]])
    assert bad_roles["error"]["type"] == "ValueError"
    bad_distinct = dl_abox_consistent(concepts=[], distinct=[["a"]])
    assert bad_distinct["error"]["type"] == "ValueError"


def test_get_syntax_spec_description_logic_topic():
    """The dedicated DL topic: hand-checked constructor table, TBox/ABox row
    shapes matching what the dl_* tools above actually parse, and examples
    parsed via dl.parse_concept/dl.parse_manchester (NOT api.parse_any,
    which cannot read either grammar — see DL_EXAMPLES's own docstring in
    syntax_spec.py) so the spec cannot silently drift from the real parser."""
    import unicode_fol_kit.dl as dl

    spec = get_syntax_spec("description-logic")
    assert spec["ok"] is True
    assert spec["topic"] == "description-logic"
    tbox_shapes = " ".join(row["shape"] for row in spec["tool_json_shapes"]["tbox_rows"])
    assert "sub" in tbox_shapes and "sup" in tbox_shapes  # sanity: field present
    assert spec["examples"], "must ship at least one worked example"
    for example in spec["examples"]:
        parser = dl.parse_concept if example["syntax"] == "alc" else dl.parse_manchester
        concept = parser(example["input"])
        assert concept.to_unicode() == example["renders_as"], example["label"]


def test_get_syntax_spec_description_logic_dialect_filter():
    """dialect='manchester' narrows description-logic's own examples using
    their 'syntax' key (not 'dialect', which those examples do not carry —
    see syntax_spec.syntax_spec's own filtering fallback)."""
    spec = get_syntax_spec("description-logic", dialect="manchester")
    assert spec["filtered_to_dialect"] == "manchester"
    assert spec["examples"]
    assert all(e["syntax"] == "manchester" for e in spec["examples"])


def test_dl_topic_is_a_valid_spec_topic_target():
    from unicode_fol_kit.mcp.syntax_spec import SPEC_TOPICS

    assert "description-logic" in SPEC_TOPICS


# ---------------------------------------------------------------------------
# Through the MCP layer proper
# ---------------------------------------------------------------------------

def test_server_registers_all_thirtyseven_tools():
    server = create_server()
    tools = asyncio.run(server.list_tools())
    assert sorted(t.name for t in tools) == [
        "check_consistency", "check_equivalence", "check_formula",
        "check_molecule", "check_molecules", "chemical_signature",
        "compare_formulas", "detect_dialect", "diagnose",
        "dl_abox_consistent", "dl_classify", "dl_concept_satisfiable",
        "dl_equivalent", "dl_instance_check", "dl_instance_retrieval",
        "dl_parse_manchester", "dl_subsumes", "drs_to_fol",
        "explain_molecule_failure", "find_countermodel", "get_signature",
        "get_syntax_spec", "list_backends", "list_translations",
        "molecule_to_structure", "normalize", "parse_formula",
        "probability_bounds", "probability_query", "prove", "render",
        "repair_formula", "score_batch", "simplify_definition", "translate",
        "truth_table", "verbalize",
    ]


def test_parse_failures_point_at_a_syntax_spec_topic():
    """The self-correction loop: a rejection names the topic to look up, and
    the topic must be one get_syntax_spec actually serves."""
    from unicode_fol_kit.mcp.syntax_spec import SPEC_TOPICS

    result = prove("P(")
    assert result["ok"] is False
    assert result["spec_topic"] in SPEC_TOPICS


def test_wrong_dialect_for_a_chemical_formula_routes_to_naming():
    """The realistic evaluation failure: a chemical definition (lowercase
    predicates) submitted as unicode. The parser rejects it on the uppercase
    argument, and the hint must send the model to 'naming', which is the
    topic that explains the inverted TPTP convention. Case-insensitive
    matching matters here — the parsers capitalise inconsistently."""
    result = prove("c(A1) ∧ o(A2)")
    assert result["ok"] is False
    assert result["spec_topic"] == "naming"


def test_mixed_connectives_route_to_operators_not_naming():
    """The kit's unicode grammar refuses 'A ∧ B ∨ C' instead of resolving it
    by precedence, so the fix is brackets and the topic is 'operators'.

    The parser stops on the ∨ with the predicate 'B' in hand, which makes the
    message mention a predicate and an unexpected character — the two things
    the 'naming' needles look for. Routing a generator to the naming rules
    here is a dead end: every name in the formula is already well formed, so
    it would rewrite them and be rejected again in exactly the same place.
    """
    for text in ("A ∧ B ∨ C", "P(x) ∧ Q(x) ∨ R(x)", "P(x) ⊗ Q(x) ∨ R(x)"):
        result = prove(text)
        assert result["ok"] is False, text
        assert result["spec_topic"] == "operators", text


def test_a_dialect_that_gave_up_early_does_not_decide_the_topic():
    """'∀x (P(x) ∧ Q(x) ⊕ R(x))' is a mixing failure, and saying so requires
    reading as far as the ⊕.

    Five of the nine dialects never get there — the ones without quantifiers
    stop at position 1, the many-sorted ones at the first '(' — and they are
    the majority, so a plain vote over the messages would answer 'naming'.
    The dialects that read furthest are the ones that saw the real cause.
    """
    result = prove("∀x (P(x) ∧ Q(x) ⊕ R(x))")
    assert result["ok"] is False
    assert result["spec_topic"] == "operators"


def test_a_lone_far_reading_does_not_outvote_an_agreeing_majority():
    """'∀ P(x)' is a quantifier left without its bound variable, which six
    dialects report at position 3 — while the second-order dialect reads the
    whole string as a term and reports an incomplete formula, getting
    'further' than any of them. Distance alone would hand the answer to that
    single outlier, so agreement has to count too."""
    result = prove("∀ P(x)")
    assert result["ok"] is False
    assert result["spec_topic"] == "quantifiers"


def test_an_incomplete_formula_still_beats_a_near_naming_complaint():
    """The other side of the same trade-off: in '∀x P(x) ∧' four dialects
    read to the end and call it incomplete, and one without quantifiers
    stumbles over the bound variable at position 4. Here the far reading is
    both the majority and the correct one."""
    result = prove("∀x P(x) ∧")
    assert result["ok"] is False
    assert result["spec_topic"] == "operators"


def test_diagnose_carries_the_topic_and_the_farthest_message():
    """`diagnose` is the correction loop's own entry point, so it has to hand
    back both halves: WHAT broke and WHICH rule to look up.

    The suggestion must come from the dialect that read furthest. Errors
    arrive one per candidate dialect in detection order, and the specialised
    dialects at the end of it give up earliest on ordinary input — for
    'A ∧ B ∨ C' the last entry blames the predicate 'A' at position 3, while
    the dialects that reached the ∨ name the mixing.
    """
    result = diagnose("A ∧ B ∨ C")
    assert result["ok"] is False
    assert result["spec_topic"] == "operators"
    assert "Cannot mix" in result["suggestion"]
    assert "Invalid predicate" not in result["suggestion"]


def test_repair_formula_fixes_the_name_and_refuses_the_bracket():
    """`repair_formula` is `diagnose`'s counterpart: it applies the fixes that
    have one right answer and reports the one that does not.

    A name no symbol class accepts is renamed invertibly (the original stays
    in `names`); a mix of ∧ and ∨ at one level is NOT bracketed, because the
    two readings are different formulas — that comes back ok=False, routed to
    the operators topic like every other rejection.
    """
    fixed = repair_formula("∀x (1,2-diacyl(x) → Lipid(x))")
    assert fixed["ok"] is True
    assert fixed["names"] == [{"original": "1,2-diacyl", "legal": "P12diacyl"}]
    assert fixed["repaired_text"] == "∀x (P12diacyl(x) → Lipid(x))"

    refused = repair_formula("A(x) ∧ B(x) ∨ C(x)")
    assert refused["ok"] is False
    assert refused["issues"][0]["kind"] == "mixed_connectives"
    assert refused["spec_topic"] == "operators"


def test_diagnose_adds_no_topic_when_the_text_parses():
    """A converged step is not a failure and must not carry a repair hint."""
    result = diagnose("∀x (P(x) → Q(x))")
    assert result["ok"] is True and result["converged"] is True
    assert "spec_topic" not in result


def test_every_routed_topic_is_one_the_spec_serves():
    """Whatever the weighting decides, it must name a topic get_syntax_spec
    can answer — an unroutable hint would break the correction loop harder
    than no hint at all."""
    from unicode_fol_kit.mcp.syntax_spec import SPEC_TOPICS

    # "P(1x)" used to be the naming-error example here (digit-leading names
    # were illegal), but a digit-leading identifier is now legal NAME syntax
    # (see tests/test_identifier_widening.py) and "P(1x)" parses today; "@"
    # is not a legal continuation character for anything, so "P(1@)" is the
    # naming-error example instead.
    for text in ("A ∧ B ∨ C", "∀ P(x)", "P(1@)", "c(A1) ∧ o(A2)", "P(",
                 "∀x P(x) ∧", "P(x) ∧ Q(x) ∨ R(x)", "∃≥ x P(x)"):
        result = prove(text)
        assert result["ok"] is False, text
        assert result["spec_topic"] in SPEC_TOPICS, text


def test_get_syntax_spec_serves_topics_and_refuses_unknown_ones():
    spec = get_syntax_spec("naming")
    assert spec["ok"] is True
    assert spec["topic"] == "naming"
    assert spec["rules"]
    assert get_syntax_spec("nope")["error"]["type"] == "ValueError"


def test_get_syntax_spec_chemistry_names_the_dialect_requirement():
    """The chemical signature uses lowercase predicates, which the unicode
    dialect cannot express — the spec must say so, or an evaluation run
    would silently mis-parse every definition."""
    spec = get_syntax_spec("chemistry")
    assert "TPTP" in spec["critical_dialect_note"]
    assert "c" in spec["signature"]["atom_types"]


def test_call_tool_prove_over_the_wire_path():
    """call_tool exercises schema validation + result serialisation: the
    same modus ponens as above must come back proved through the MCP layer
    (the SDK returns a CallToolResult whose first content item is the JSON
    text of the tool's dict)."""
    import json

    server = create_server()
    result = asyncio.run(server.call_tool(
        "prove", {"conclusion": "Q(alice)",
                  "premises": ["P(alice)", "∀x (P(x) → Q(x))"]}))
    payload = getattr(result, "structured_content", None)
    if payload is None:
        payload = json.loads(result.content[0].text)
    assert payload["status"] == "proved"
    assert payload["backend"] == "z3"


def test_call_tool_dl_subsumes_over_the_wire_path():
    """Same wire-path check as above, for a description-logic tool: schema
    validation must accept a 'tbox' argument that is a list of JSON row
    dicts (not a Python TBox object), and the result must still be Mother ⊑
    Parent = True."""
    import json

    server = create_server()
    result = asyncio.run(server.call_tool(
        "dl_subsumes", {"sub": "Mother", "sup": "Parent", "tbox": _FAMILY_TBOX}))
    payload = getattr(result, "structured_content", None)
    if payload is None:
        payload = json.loads(result.content[0].text)
    assert payload["ok"] is True
    assert payload["subsumes"] is True
