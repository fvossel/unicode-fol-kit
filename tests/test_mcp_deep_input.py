"""No tool of the MCP server lets an exception out for a text that the parser reads, however deep.

Two texts are sent to every registered tool that takes text, through the server's own wire path
(``call_tool``): a chain of four hundred quantifiers, ``∀x ∀x … ∀x P(x)``, and a chain of three thousand
negations, ``¬¬…¬P``. Each tool comes back with an answer or with the structured refusal that every other
refusal of the server is (``{"error": …}`` or ``{"ok": False, …}``); an exception is the failure, and so is a
refusal that says the recursion limit ran out where the deep worker of :mod:`unicode_logic_kit.api` could have
read the input.

The quantifier chain is read by the parser. ``∀x ∀x … ∀x P(x)`` binds the one variable ``x`` four hundred
times; it is closed, its one predicate is ``P/1``, and it is equivalent to ``∀x P(x)``: whatever is true of
every element is true of every element. What the tools answer for it is derived by hand below, from that.

The answer of ``parse_formula`` is the syntax tree of the formula, nested as deep as the formula, and the MCP
SDK writes JSON only up to a nesting of its own. Such an answer is refused by name instead of ending in the SDK's own
error (which speaks of a circular reference), and an answer the SDK can write is left as it is.
"""

import asyncio
import json

import pytest

pytest.importorskip("mcp", reason="optional [mcp] extra not installed")

from unicode_logic_kit.mcp import server as tools   # noqa: E402
from unicode_logic_kit.mcp.server import create_server   # noqa: E402

CHAIN = "∀x " * 400 + "P(x)"
SHAPES = {
    "quantifier-chain": dict(
        text=CHAIN, concept="∃r." * 40 + "A", manchester="r some " * 40 + "A",
        smiles="C" + "(C" * 400 + ")" * 400, tptp="! [X] : " * 400 + "p(X)"),
    "negation-chain": dict(
        text="¬" * 3000 + "P", concept="¬" * 3000 + "A", manchester="not " * 3000 + "A",
        smiles="C" + "(C" * 3000 + ")" * 3000, tptp="~" * 3000 + "p"),
}

#: ``tool -> arguments`` for every registered tool that takes text, as a function of the shape.
CALLS = {
    "parse_formula": lambda s: {"text": s["text"]},
    "check_formula": lambda s: {"text": s["text"]},
    "prove": lambda s: {"conclusion": s["text"]},
    "prove (as a premise)": lambda s: {"conclusion": "P(a)", "premises": [s["text"]], "backends": ["z3"]},
    "find_countermodel": lambda s: {"formula": s["text"]},
    "check_equivalence": lambda s: {"formula1": s["text"], "formula2": s["text"]},
    "diagnose": lambda s: {"text": s["text"]},
    "repair_formula": lambda s: {"text": s["text"]},
    "translate": lambda s: {"term": s["text"], "from_logic": "fol", "to_logic": "tptp"},
    "verbalize": lambda s: {"text": s["text"]},
    "normalize": lambda s: {"text": s["text"], "form": "nnf"},
    "normalize (cnf)": lambda s: {"text": s["text"], "form": "cnf"},
    "render": lambda s: {"text": s["text"], "to": "smtlib"},
    "render (tptp)": lambda s: {"text": s["text"], "to": "tptp"},
    "detect_dialect": lambda s: {"text": s["text"]},
    "compare_formulas": lambda s: {"predicted": s["text"], "gold": s["text"]},
    "score_batch": lambda s: {"predictions": [s["text"]], "references": [s["text"]]},
    "check_consistency": lambda s: {"formulas": [s["text"]]},
    "get_signature": lambda s: {"formulas": [s["text"]]},
    "truth_table": lambda s: {"text": s["text"]},
    "drs_to_fol": lambda s: {"text": s["text"]},
    "probability_bounds": lambda s: {"conclusion": s["text"],
                                      "constraints": [{"formula": s["text"], "probability": "1/2"}]},
    "probability_query": lambda s: {"goal": s["text"], "facts": [{"atom": "P", "prob": "1/2"}]},
    "dl_concept_satisfiable": lambda s: {"concept": s["concept"]},
    "dl_subsumes": lambda s: {"sub": s["concept"], "sup": "A"},
    "dl_equivalent": lambda s: {"c": s["concept"], "d": s["concept"]},
    "dl_abox_consistent": lambda s: {"concepts": [["a", s["concept"]]]},
    "dl_instance_check": lambda s: {"individual": "a", "concept": s["concept"], "concepts": [["a", "A"]]},
    "dl_instance_retrieval": lambda s: {"concept": s["concept"], "concepts": [["a", "A"]]},
    "dl_classify": lambda s: {"concepts": [s["concept"]]},
    "dl_parse_manchester": lambda s: {"text": s["manchester"]},
    "dl_concept_satisfiable (formula text)": lambda s: {"concept": s["text"]},
    "molecule_to_structure": lambda s: {"smiles": s["smiles"]},
    "check_molecule": lambda s: {"formula": s["tptp"], "smiles": "C"},
    "check_molecules": lambda s: {"formula": s["tptp"], "smiles_list": ["C"]},
    "explain_molecule_failure": lambda s: {"formula": s["tptp"], "smiles": "C"},
    "simplify_definition": lambda s: {"formula": s["tptp"]},
}

#: The registered tools that take no text: nothing about them depends on a deep input.
WITHOUT_TEXT = {"list_backends", "list_translations", "get_syntax_spec", "chemical_signature"}


@pytest.fixture(scope="module")
def server():
    return create_server()


def _tool_name(label):
    return label.split(" (")[0]


def _on_the_wire(server, label, shape):
    """What ``call_tool`` hands a client for ``label`` and ``shape``: the dict the tool answered with.

    An exception in the tool is raised by ``call_tool`` as the SDK's ``ToolError``: that is the failure.
    """
    result = asyncio.run(server.call_tool(_tool_name(label), CALLS[label](SHAPES[shape])))
    payload = getattr(result, "structured_content", None)
    if payload is None:
        payload = json.loads(result.content[0].text)
    if isinstance(payload, dict) and set(payload) == {"result"}:
        payload = payload["result"]
    return payload


def test_the_table_covers_every_tool_that_takes_text(server):
    registered = {tool.name for tool in asyncio.run(server.list_tools())}
    assert {_tool_name(label) for label in CALLS} == registered - WITHOUT_TEXT


@pytest.mark.parametrize("shape", sorted(SHAPES))
@pytest.mark.parametrize("label", sorted(CALLS))
def test_a_deep_text_is_answered_or_refused_by_name(server, label, shape):
    payload = _on_the_wire(server, label, shape)
    assert isinstance(payload, dict)
    refusal = payload.get("error")
    if refusal is not None:
        assert set(refusal) == {"type", "message"} and refusal["message"]
        assert refusal["type"] != "RecursionError", refusal["message"]
    elif payload.get("ok") is False:
        # the uniform parse refusal (``errors``) or the repair loop's own report (``issues`` or
        # ``diagnostics``): what the parser said about each dialect
        assert payload.get("errors") or payload.get("issues") or payload.get("diagnostics"), payload


# ---------------------------------------------------------------------------
# What the tools answer for the quantifier chain, derived by hand
# ---------------------------------------------------------------------------

class TestAnswersForTheQuantifierChain:
    def test_it_is_a_closed_formula_of_one_unary_predicate(self):
        answer = tools.check_formula(CHAIN)
        assert answer["ok"] is True and answer["is_closed"] is True
        assert answer["predicates"] == ["P/1"] and answer["free_variables"] == []

    def test_it_is_equivalent_to_itself_and_to_one_quantifier(self):
        assert tools.check_equivalence(CHAIN, CHAIN)["equivalent"] is True
        assert tools.check_equivalence(CHAIN, "∀x P(x)")["equivalent"] is True

    def test_it_is_not_valid(self):
        # The universe {0} with P empty falsifies ∀x P(x).
        assert tools.prove(CHAIN, backends=["z3"])["status"] == "refuted"

    def test_a_comparison_with_itself_is_an_exact_match(self):
        answer = tools.compare_formulas(CHAIN, CHAIN)
        assert answer["structural_equal"] is True and answer["canonical_exact_match"] is True
        scores = tools.score_batch([CHAIN], [CHAIN])
        assert scores["exact_match"] == 1.0 and scores["equivalence_accuracy"] == 1.0

    def test_a_formula_in_negation_normal_form_is_its_own_normal_form(self):
        answer = tools.normalize(CHAIN, "nnf")
        assert answer["ok"] is True and answer["unicode"] == CHAIN

    def test_the_prenex_form_keeps_the_four_hundred_quantifiers(self):
        # The prefix is the quantifiers of the formula, and the matrix is the one atom.
        answer = tools.normalize(CHAIN, "pnf")
        assert answer["ok"] is True
        assert answer["unicode"].count("∀") == 400 and answer["unicode"].count("P(") == 1

    def test_the_smtlib_text_has_one_quantifier_for_each_of_them(self):
        rendered = tools.render(CHAIN, "smtlib")["rendered"]
        assert rendered.count("(forall ((x S) )") == 400

    def test_the_vocabulary_is_the_one_predicate(self):
        assert tools.get_signature([CHAIN])["signature"]["predicates"] == {"P": {"arity": 1, "arg_sorts": None}}


# ---------------------------------------------------------------------------
# The answer that the transport cannot write
# ---------------------------------------------------------------------------

class TestAnAnswerTheTransportCannotWrite:
    def test_a_shallow_answer_is_written_as_it_is(self, server):
        text = "∀x ∀y P(x, y)"
        result = asyncio.run(server.call_tool("parse_formula", {"text": text}))
        payload = getattr(result, "structured_content", None) or json.loads(result.content[0].text)
        assert payload == tools.parse_formula(text)
        assert payload["ok"] is True

    def test_a_deep_answer_is_refused_by_name_with_the_depth_and_a_way_out(self, server):
        payload = _on_the_wire(server, "parse_formula", "quantifier-chain")
        assert set(payload) == {"error"} and payload["error"]["type"] == "ValueError"
        message = payload["error"]["message"]
        assert "parse_formula" in message and "levels deep" in message and "render" in message
        assert "circular" not in message.lower()

    def test_a_call_from_python_still_gets_the_deep_answer(self):
        answer = tools.parse_formula(CHAIN)
        assert answer["ok"] is True and "error" not in answer

    def test_the_depth_is_counted_in_containers(self):
        assert tools._nesting({"a": [{"b": 1}, 2], "c": 3}) == 3
        assert tools._nesting("text") == 0 and tools._nesting({}) == 1


# ---------------------------------------------------------------------------
# The guard itself
# ---------------------------------------------------------------------------

def _recurse(levels):
    return 0 if levels == 0 else 1 + _recurse(levels - 1)


class TestTheGuardForADeepInput:
    def test_a_call_that_runs_out_of_stack_is_made_again_where_a_deep_formula_is_read(self):
        # A text of 3000 characters can be nested 3000 deep; the recursion below goes that deep, which
        # is more than the 1000 frames of the calling thread and fewer than the worker is given.
        def walk(text):
            return {"levels": _recurse(len(text))}

        guarded = tools._answers_deep_input(walk)
        assert guarded("x" * 3000) == {"levels": 3000}
        assert guarded.answers_deep_input is True

    def test_a_call_that_cannot_be_read_even_there_is_the_structured_error(self):
        def endless(text):
            return _recurse(10 ** 9)

        answer = tools._answers_deep_input(endless)("x" * 300)
        assert set(answer) == {"error"} and answer["error"]["type"] == "RecursionError"
        assert "endless" in answer["error"]["message"] and "nested" in answer["error"]["message"]

    def test_a_shallow_call_is_made_once(self):
        calls = []

        def tool(text):
            calls.append(text)
            return {"ok": True}

        assert tools._answers_deep_input(tool)("short") == {"ok": True}
        assert calls == ["short"]

    def test_the_longest_text_of_the_arguments_bounds_the_nesting(self):
        assert tools._text_size("abc") == 3
        assert tools._text_size({"formulas": ["a", "abcd"], "n": 7, "deep": [["xy"]]}) == 4
        assert tools._text_size(None) == 0

    def test_the_schema_of_a_guarded_tool_is_the_schema_of_the_tool(self, server):
        listed = {tool.name: tool for tool in asyncio.run(server.list_tools())}
        schema = listed["normalize"].input_schema
        assert schema["required"] == ["text"]
        assert set(schema["properties"]) == {"text", "form", "dialect"}
