"""Every tool of the MCP server answers a refusal with its structured error, and never with an exception.

A printer or a writer of the kit refuses, by name, what it would otherwise write wrongly: a description-logic
concept whose glyph text would read back as another concept, a numeral next to a constant spelled like it, a
truth constant in a logic that has no reading of it, a free variable in a TPTP problem, a typed (TF0) text that
would not mean the same, a node of another logic in a substructural sequent. A tool wraps those calls, and a
refusal that is not caught leaves the tool as an exception, which a client reads as a crashed server.

The refusals that CAN reach a tool, as the text of a formula or a concept (each family is one input):

* a ``Number`` next to a ``Constant`` or a ``Function`` spelled like its numeral (TPTP text, where ``'1'`` is a
  constant named 1);
* the truth constants ``$true`` / ``$false`` / ``⊤`` / ``⊥``, which ILL, the Lambek calculus and relevant logic
  refuse;
* a free variable, which a TPTP problem refuses;
* a counting quantifier, a sorted constant, a constant with two sorts, a name that is not a TPTP word;
* a node of another logic (modal, hybrid, linear, Lambek, second order, third order) in a tool for a logic that
  has no rule for it;
* a description-logic class or role named like a connective (``<A⊓B>``), which has no glyph spelling.

Each family is sent to every tool that takes formula text, with every parameter value that selects a different
route (the render target, the normal form, the truth-table logic, the logic and backend of the provers, every edge
of the translation registry). The assertion is that no exception leaves the tool and that what comes back is a
dict; a refusal comes back as ``{"error": {"type", "message"}}`` or as the uniform ``{"ok": False, ...}``.
"""

import asyncio

import pytest

pytest.importorskip("mcp", reason="optional [mcp] extra not installed")

from unicode_fol_kit.mcp.server import (   # noqa: E402
    check_consistency, check_equivalence, check_formula, compare_formulas, create_server, detect_dialect,
    diagnose, dl_abox_consistent, dl_classify, dl_concept_satisfiable, dl_equivalent, dl_instance_check,
    dl_instance_retrieval, dl_parse_manchester, dl_subsumes, drs_to_fol, find_countermodel, get_signature,
    get_syntax_spec, list_backends, list_translations, normalize, parse_formula, probability_bounds,
    probability_query, prove, render, repair_formula, score_batch, translate, truth_table, verbalize,
)

FAMILIES = {
    "numeral_vs_constant": "fof(f,axiom,(p(1) & q('1'))).",
    "numeral_vs_function": "fof(f,axiom,(p(1) & q('1'(c)))).",
    "truth_true": "$true",
    "truth_false": "$false",
    "truth_in_formula": "P → ⊥",
    "truth_top_glyph": "⊤",
    "free_variable": "P(x)",
    "free_in_conjunct": "(∀x P(x)) ∧ Q(y)",
    "count_at_least": "∃≥2 x P(x)",
    "count_exactly_none": "∃=0 x P(x)",
    "sorted_constant": "∀x:Human Mortal(x) → Mortal(carl:Human)",
    "unsorted_constant_in_sort": "∀x:Human Mortal(x) → Mortal(bob)",
    "constant_with_two_sorts": "P(carl:A) ∧ Q(carl:B)",
    "digit_leading_name": "P(2008x)",
    "non_ascii_name": "P(sókrates)",
    "modal": "□P → P",
    "modal_with_truth": "□⊤",
    "hybrid": "@i P → P",
    "linear": "(A ⊗ B) ⊸ (B ⊗ A)",
    "lambek": "NP • (NP \\ S)",
    "quantifier": "∀x P(x)",
    "second_order": "∀P P(a)",
    "third_order": "Positive(G)",
    "arithmetic": "x + 1 > x",
    "equality": "a = b",
}

#: Backends that need no external program, by the logic they decide.
IN_HOUSE_FOL = ["z3", "cvc5", "tableau", "resolution", "modelfinder", "clingo"]
IN_HOUSE_MODAL = ["modal-tableau", "kripke-enum", "qml", "ltl-tableau"]
OTHER_LOGICS = ["ill", "lambek", "intuitionistic", "relevant", "hybrid"]


def _every_call(text):
    """``(label, zero-argument call)`` for every tool that takes formula text, sent ``text``."""
    from unicode_fol_kit.comorphism import DEFAULT_REGISTRY

    yield "parse_formula", lambda: parse_formula(text)
    yield "check_formula", lambda: check_formula(text)
    yield "diagnose", lambda: diagnose(text)
    yield "repair_formula", lambda: repair_formula(text)
    yield "detect_dialect", lambda: detect_dialect(text)
    yield "verbalize", lambda: verbalize(text)
    yield "get_signature", lambda: get_signature([text])
    for target in ("unicode", "tptp", "prover9", "latex", "smtlib", "casl", "json", "english"):
        yield f"render to={target}", lambda target=target: render(text, target)
    for form in ("nnf", "pnf", "cnf", "dnf", "canonical", "tseitin_cnf", "skolemize"):
        yield f"normalize form={form}", lambda form=form: normalize(text, form)
    for logic in ("classical", "K3", "LP"):
        yield f"truth_table logic={logic}", lambda logic=logic: truth_table(text, logic)
    for method in ("auto", "solver", "canonical", "exact"):
        yield f"check_equivalence {method}", lambda method=method: check_equivalence(text, "P(a)", method, 3000)
        yield f"check_equivalence {method} (itself)", lambda method=method: check_equivalence(text, text, method, 3000)
    yield "compare_formulas", lambda: compare_formulas(text, "P(a)", 3000)
    yield "compare_formulas (itself)", lambda: compare_formulas(text, text, 3000)
    yield "score_batch", lambda: score_batch([text], ["P(a)"], "auto", 3000)
    yield "probability_bounds", lambda: probability_bounds(text, [{"formula": text, "probability": "1/2"}])
    yield "probability_query", lambda: probability_query(text, [{"atom": "P(alice)", "prob": "1/2"}])
    for edge in DEFAULT_REGISTRY.edges():
        if edge.source in ("fol", "modal", "msfol", "qml", "fuzzy", "team"):
            yield f"translate {edge.source}->{edge.target}", lambda edge=edge: translate(text, edge.source, edge.target)
    for backend in IN_HOUSE_FOL:
        yield f"prove fol {backend} (goal)", lambda backend=backend: prove(text, [], "fol", [backend], 3000)
        yield f"prove fol {backend} (premise)", lambda backend=backend: prove("P(a)", [text], "fol", [backend], 3000)
    for backend in IN_HOUSE_MODAL:
        yield f"prove modal {backend}", lambda backend=backend: prove(text, [], "modal", [backend], 3000)
    for logic in OTHER_LOGICS:
        yield f"prove {logic} (goal)", lambda logic=logic: prove(text, [], logic, [logic], 3000)
        yield f"prove {logic} (premise)", lambda logic=logic: prove("A", [text], logic, [logic], 3000)
    yield "prove default chain", lambda: prove(text, [], "auto", None, 3000)
    for logic in ("auto", "fol", "modal", "ill", "lambek", "intuitionistic", "relevant", "hybrid"):
        yield f"find_countermodel logic={logic}", lambda logic=logic: find_countermodel(text, [], logic)
        yield f"check_consistency logic={logic}", lambda logic=logic: check_consistency([text], logic, 3000)


@pytest.mark.parametrize("family", sorted(FAMILIES))
def test_no_tool_lets_an_exception_out_for_a_refusal_family(family):
    escaped = []
    answered = 0
    for label, call in _every_call(FAMILIES[family]):
        try:
            result = call()
        except Exception as exc:                                        # noqa: BLE001
            escaped.append(f"{label}: {type(exc).__name__}: {str(exc)[:100]}")
            continue
        assert isinstance(result, dict), label
        answered += 1
    assert not escaped, "an exception left the tool for " + family + ":\n" + "\n".join(escaped)
    assert answered >= 80                                                # the sweep did run: 87 calls per family


def test_the_tools_without_a_formula_text_never_raise_either():
    for topic in ("overview", "naming", "dialects", "operators", "quantifiers", "counting", "chemistry",
                  "description-logic", "errors", "no such topic"):
        assert isinstance(get_syntax_spec(topic), dict)
    assert isinstance(list_backends(), dict) and isinstance(list_translations(), dict)
    for text in ("[x | Farmer(x), Runs(x)]", "[x | Farmer(x), x = 1]", "[x | $true]", "[x | P(1), Q(2.5)]"):
        assert isinstance(drs_to_fol(text), dict)


def test_the_table_covers_every_tool_the_server_registers():
    covered = {"parse_formula", "check_formula", "diagnose", "repair_formula", "detect_dialect", "verbalize",
               "get_signature", "render", "normalize", "truth_table", "check_equivalence", "compare_formulas",
               "score_batch", "probability_bounds", "probability_query", "translate", "prove",
               "find_countermodel", "check_consistency",
               "get_syntax_spec", "list_backends", "list_translations", "drs_to_fol",
               "dl_abox_consistent", "dl_classify", "dl_concept_satisfiable", "dl_equivalent",
               "dl_instance_check", "dl_instance_retrieval", "dl_parse_manchester", "dl_subsumes",
               # the chemistry tools take a SMILES string and a TPTP class definition; see test_mcp_chem_tools
               "check_molecule", "check_molecules", "chemical_signature", "explain_molecule_failure",
               "molecule_to_structure", "simplify_definition"}
    registered = {tool.name for tool in asyncio.run(create_server().list_tools())}
    assert registered == covered


# ---------------------------------------------------------------------------
# A concept whose glyph text would read back as another concept
# ---------------------------------------------------------------------------

#: A class named ``<A⊓B>`` (one IRI-style name in Manchester syntax). Its glyph text ``<A⊓B>`` is read back by the
#: glyph grammar as the intersection of the classes ``<A`` and ``B>``: another concept, so no faithful text exists.
MISREAD = "<A⊓B>"

MISREAD_CALLS = {
    "dl_concept_satisfiable": lambda: dl_concept_satisfiable(MISREAD, syntax="manchester"),
    "dl_subsumes (sub)": lambda: dl_subsumes(MISREAD, "A", syntax="manchester"),
    "dl_subsumes (sup)": lambda: dl_subsumes("A", MISREAD, syntax="manchester"),
    "dl_equivalent (c)": lambda: dl_equivalent(MISREAD, "A", syntax="manchester"),
    "dl_equivalent (d)": lambda: dl_equivalent("A", MISREAD, syntax="manchester"),
    "dl_instance_check": lambda: dl_instance_check("a", MISREAD, [["a", "A"]], syntax="manchester"),
    "dl_instance_retrieval": lambda: dl_instance_retrieval(MISREAD, [["a", "A"]], syntax="manchester"),
    "dl_parse_manchester concept": lambda: dl_parse_manchester(MISREAD, "concept"),
    "dl_parse_manchester axiom (sub)": lambda: dl_parse_manchester(f"{MISREAD} SubClassOf Doctor", "axiom"),
    "dl_parse_manchester axiom (sup)": lambda: dl_parse_manchester(f"Doctor SubClassOf {MISREAD}", "axiom"),
    "dl_parse_manchester domain": lambda: dl_parse_manchester(f"Covers Domain: {MISREAD}", "role_axiom"),
    "dl_parse_manchester range": lambda: dl_parse_manchester(f"HasUnit Range: {MISREAD}", "role_axiom"),
}


@pytest.mark.parametrize("label", sorted(MISREAD_CALLS))
def test_a_concept_with_no_faithful_glyph_text_is_a_structured_error(label):
    result = MISREAD_CALLS[label]()
    assert set(result) == {"error"}
    assert result["error"]["type"] == "ValueError"
    assert "reads back as" in result["error"]["message"] and MISREAD in result["error"]["message"]


@pytest.mark.parametrize("text", ["<A⊔B>", "r some <A⊓B>", "<A⊓B> and C"])
def test_every_misreading_name_is_refused_in_every_position_of_a_concept(text):
    # ⊔ for ⊓; the name as a filler; the name as one operand of an intersection.
    result = dl_concept_satisfiable(text, syntax="manchester")
    assert set(result) == {"error"} and result["error"]["type"] == "ValueError"


def test_the_refusal_comes_before_the_reasoning(monkeypatch):
    # The text of the concept is needed for the answer, so a concept with no faithful text is refused before a
    # tableau is started on it.
    import unicode_fol_kit.dl as dl

    def must_not_run(*args, **kwargs):
        raise AssertionError("the tableau was started for a concept the tool cannot report")

    monkeypatch.setattr(dl, "concept_satisfiable", must_not_run)
    monkeypatch.setattr(dl, "subsumes", must_not_run)
    result = dl_concept_satisfiable(MISREAD, [{"sub": "A", "sup": "B"}], syntax="manchester")
    assert set(result) == {"error"} and "reads back as" in result["error"]["message"]
    assert set(dl_subsumes(MISREAD, "A", syntax="manchester")) == {"error"}


@pytest.mark.parametrize("call", [
    lambda: dl_concept_satisfiable("Person", syntax="manchester"),
    lambda: dl_concept_satisfiable("<http://example.org/Person>", syntax="manchester"),
    lambda: dl_subsumes("Dog", "Animal", [{"sub": "Dog", "sup": "Animal"}], syntax="manchester"),
    lambda: dl_equivalent("Person", "Person", syntax="manchester"),
    lambda: dl_instance_check("a", "Person", [["a", "Person"]], syntax="manchester"),
    lambda: dl_instance_retrieval("Person", [["a", "Person"]], syntax="manchester"),
    lambda: dl_parse_manchester("Doctor SubClassOf Person", "axiom"),
    lambda: dl_parse_manchester("Covers Domain: Study", "role_axiom"),
    lambda: dl_parse_manchester("Person", "concept"),
], ids=["satisfiable", "iri-name", "subsumes", "equivalent", "instance_check", "instance_retrieval",
        "axiom", "role_axiom", "concept"])
def test_a_concept_with_a_faithful_glyph_text_is_answered_as_before(call):
    result = call()
    assert result.get("ok") is True and "error" not in result


def test_translate_answers_a_result_with_no_faithful_text_as_a_structured_error(monkeypatch):
    # No edge of the registry ends in a description-logic concept today; an edge that does must not make
    # the tool raise when its result has no glyph text.
    from types import SimpleNamespace

    from unicode_fol_kit.comorphism import DEFAULT_REGISTRY
    from unicode_fol_kit.dl import Atomic

    stub = SimpleNamespace(to_dict=lambda: {"result": "stub"}, result=Atomic("<A⊓B>"), axioms=[])
    monkeypatch.setattr(DEFAULT_REGISTRY, "translate", lambda *args, **kwargs: stub)
    result = translate("P", "fol", "modal")
    assert set(result) == {"error"} and result["error"]["type"] == "ValueError"
    assert "reads back as" in result["error"]["message"]
