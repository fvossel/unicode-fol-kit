"""The MCP tools that check or compare vocabulary read the truth constants and signatures right.

``check_formula``, ``diagnose`` and ``compare_formulas`` list the predicates a formula uses.
``⊤`` / ``$true`` and ``⊥`` / ``$false`` are logical constants, not predicates, so a formula
that mentions one must neither list it nor be flagged for it, whichever of the four texts
(unicode, LaTeX, TPTP, SMT-LIB) spelled it; and the signature that ``get_signature`` returns
must pass ``check_formula`` / ``diagnose`` unchanged, which is what its docstring promises.

Hand-derived: the vocabulary of ``P ∧ ⊤`` is one predicate, ``P`` of arity 0; of
``P(alpha) ∧ ⊤`` it is ``P`` of arity 1 and the constant ``alpha``.
"""

import pytest

pytest.importorskip("mcp", reason="optional [mcp] extra not installed")

from unicode_fol_kit import api                                        # noqa: E402
from unicode_fol_kit.fol._identifiers import symbol_names              # noqa: E402
from unicode_fol_kit.mcp import server as tools                        # noqa: E402

#: One formula per spelling, each with the constant true or false and ONE predicate of arity 0.
#: (The TPTP reader upper-cases the predicate, the SMT-LIB reader keeps ``p``.)
SPELLED = {
    "unicode": ["P ∧ ⊤", "P → ⊥"],
    "latex": [r"P \land \top", r"P \rightarrow \bot"],
    "tptp": ["fof(a, axiom, (p & $true)).", "fof(a, axiom, (p => $false))."],
    "smtlib": ["(declare-const p Bool)(assert (and p true))",
               "(declare-const p Bool)(assert (=> p false))"],
}
TEXTS = [text for texts in SPELLED.values() for text in texts]


def _symbols(inventory):
    return sorted(entry.rpartition("/")[0] for entry in inventory)


@pytest.mark.parametrize("text", TEXTS)
def test_a_formula_with_a_constant_lists_only_its_own_predicate(text):
    result = tools.check_formula(text)
    assert result["ok"] is True
    assert result["predicates"] in (["P/0"], ["p/0"])
    assert tools.get_signature([text])["signature"]["predicates"] in ({"P": {"arity": 0, "arg_sorts": None}},
                                                                      {"p": {"arity": 0, "arg_sorts": None}})


@pytest.mark.parametrize("text", TEXTS)
def test_what_get_signature_returns_passes_check_formula_and_diagnose_unchanged(text):
    signature = tools.get_signature([text])["signature"]
    checked = tools.check_formula(text, signature=signature)
    assert checked["ok"] is True and checked["signature_errors"] == []
    step = tools.diagnose(text, signature=signature)
    assert step["converged"] is True and step["suggestion"] is None


@pytest.mark.parametrize("text", TEXTS)
def test_a_loose_signature_that_names_the_predicate_is_enough(text):
    loose = {"predicates": {"P": 0, "p": 0}}
    assert tools.check_formula(text, signature=loose)["ok"] is True
    assert tools.diagnose(text, signature=loose)["converged"] is True


def test_the_signature_round_trip_keeps_functions_constants_and_sorts():
    texts = ["∀x (Dog(x) → Animal(father(x)))", "Dog(rex) ∧ ⊤"]
    signature = tools.get_signature(texts)["signature"]
    assert signature["functions"] == {"father": {"arity": 1, "arg_sorts": None, "result_sort": None}}
    for text in texts:
        assert tools.check_formula(text, signature=signature)["ok"] is True
    # The signature still constrains: a predicate it does not declare is flagged, and only that one.
    flagged = tools.check_formula("Cat(rex) ∧ ⊤", signature=signature)
    assert flagged["ok"] is False
    assert [(e["kind"], e["symbol"]) for e in flagged["signature_errors"]] == [("unknown_predicate", "Cat")]

    sorted_signature = tools.get_signature(["P(carl:A)"])["signature"]
    assert sorted_signature["constants"] == {"carl": "A"} and sorted_signature["sorts"] == ["A"]
    assert tools.check_formula("P(carl:A)", signature=sorted_signature)["ok"] is True


def test_compare_formulas_shows_no_vocabulary_difference_for_a_constant():
    result = tools.compare_formulas("P(alpha) ∧ ⊤", "P(alpha)")
    assert result["vocabulary"]["predicates"] == {"only_in_predicted": [], "only_in_gold": [],
                                                  "shared": ["P/1"]}
    assert result["equivalence"]["equivalent"] is True
    result = tools.compare_formulas("P(alpha) → ⊥", "¬P(alpha)")
    assert result["vocabulary"]["predicates"]["only_in_predicted"] == []
    assert result["vocabulary"]["predicates"]["only_in_gold"] == []


@pytest.mark.parametrize("spelled", sorted(SPELLED))
def test_compare_formulas_reads_each_spelling_alike(spelled):
    true_text, false_text = SPELLED[spelled]
    for text in (true_text, false_text):
        same = tools.compare_formulas(text, text)
        for section in same["vocabulary"].values():
            assert section["only_in_predicted"] == [] and section["only_in_gold"] == []
        assert all(not name.startswith(("$", "⊤", "⊥"))
                   for name in same["vocabulary"]["predicates"]["shared"])


def test_a_predicate_spelled_like_a_constant_but_applied_is_still_vocabulary():
    # ⊤(alpha) is no formula the grammar reads, so build it: the node is a user predicate.
    from unicode_fol_kit.eval.validate import validate
    from unicode_fol_kit.fol.nodes import Atom, Constant
    assert validate(Atom("⊤", (Constant("alpha"),))).predicates == ("⊤/1",)


# ---------------------------------------------------------------------------
# A malformed signature is a structured error, never an exception out of a tool
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("signature,needle", [
    ({"predicates": 5}, "predicates"),
    ({"predicates": {"P": "one"}}, "'P'"),
    ({"constants": "alpha"}, "constants"),
    ({"predicate": {"P": 0}}, "predicate"),
    ({"subsorts": {"A": "B"}}, "subsorts"),
])
def test_a_malformed_signature_is_a_structured_error(signature, needle):
    for result in (tools.check_formula("P", signature=signature),
                   tools.diagnose("P", signature=signature),
                   tools.diagnose("P(", signature=signature)):          # also for text that does not parse
        assert set(result) == {"error"}
        assert result["error"]["type"] in ("TypeError", "ValueError")
        assert needle in result["error"]["message"]


# ---------------------------------------------------------------------------
# check_consistency: its contradiction is built from a name that no symbol of the input has
# ---------------------------------------------------------------------------

def test_the_contradiction_check_consistency_asks_about_uses_a_fresh_name(monkeypatch):
    """Constants spelled like the name the tool would pick first (and like the name it would pick
    next) must not be confused with the proposition it builds the contradiction from."""
    captured = {}
    real = api.countermodel

    def spy(formula, premises=(), **kwargs):
        captured["formula"], captured["premises"] = formula, list(premises)
        return real(formula, premises, **kwargs)

    monkeypatch.setattr(api, "countermodel", spy)
    formulas = ["P(ufk_absurd)", "R(ufk_absurd_, alpha)"]
    result = tools.check_consistency(formulas)
    assert result["ok"] is True
    names = symbol_names(*captured["premises"])
    contradiction = captured["formula"]
    letter = contradiction.left.predicate                      # the proposition q of  q ∧ ¬q
    assert contradiction.right.formula.predicate == letter
    assert letter not in names                                  # fresh against every kind of name
    assert {"ufk_absurd", "ufk_absurd_"} <= names               # the names it had to avoid are there


# ---------------------------------------------------------------------------
# What the side axioms of a translation are, as the tool texts say it
# ---------------------------------------------------------------------------

def test_the_side_axioms_of_the_many_sorted_translation_are_two_kinds_and_the_texts_say_so():
    term = "∀x:Human Mortal(x) → Mortal(socrates:Human)"
    result = tools.translate(term, "msfol", "fol")
    axioms = result["axioms_unicode"]
    assert len(axioms) == 2
    assert sum(text.startswith("∃") for text in axioms) == 1          # the sort Human is not empty
    assert "Human(socrates)" in axioms                                # socrates is an element of Human
    for text in (tools.translate.__doc__, tools._INSTRUCTIONS, api._unwrap_sentences.__doc__):
        assert "membership" in text and "non-empt" in text
