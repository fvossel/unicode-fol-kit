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


def test_render_unknown_target_is_structured_error():
    result = render("P", to="klingon")
    assert result["error"]["type"] == "ValueError"


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
# Through the MCP layer proper
# ---------------------------------------------------------------------------

def test_server_registers_all_twentyeight_tools():
    server = create_server()
    tools = asyncio.run(server.list_tools())
    assert sorted(t.name for t in tools) == [
        "check_consistency", "check_equivalence", "check_formula",
        "check_molecule", "check_molecules", "chemical_signature",
        "compare_formulas", "detect_dialect", "diagnose", "drs_to_fol",
        "explain_molecule_failure", "find_countermodel", "get_signature",
        "get_syntax_spec", "list_backends", "list_translations",
        "molecule_to_structure", "normalize", "parse_formula",
        "probability_bounds", "probability_query", "prove", "render",
        "score_batch", "simplify_definition", "translate", "truth_table",
        "verbalize",
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

    for text in ("A ∧ B ∨ C", "∀ P(x)", "P(1x)", "c(A1) ∧ o(A2)", "P(",
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
