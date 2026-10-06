"""``check_formula`` and ``diagnose`` take what ``get_signature`` returns, as their docstrings promise.

``get_signature`` returns ``{"ok": True, "signature": {...}}``. The two tools that hold a text to a
vocabulary accept that whole result as their ``signature`` argument, and accept its ``signature`` value;
both are the same vocabulary. Anything that is not exactly such a result is read as it was before: the loose
form ``{"predicates": {...}, ...}`` is a vocabulary, and a dict with another shape is a structured refusal.

The vocabulary used throughout comes from two formulas: ``∀x (Dog(x) → Animal(x))`` and ``Dog(rex)``. It has
the predicates ``Dog/1`` and ``Animal/1`` and the constant ``rex``; so ``Dog(rex)`` conforms, and
``Cat(rex)`` uses the predicate ``Cat``, which is not in it.
"""

import pytest

pytest.importorskip("mcp", reason="optional [mcp] extra not installed")

from unicode_fol_kit.mcp.server import check_formula, diagnose, get_signature   # noqa: E402

SOURCES = ["∀x (Dog(x) → Animal(x))", "Dog(rex)"]


@pytest.fixture(scope="module")
def returned():
    result = get_signature(SOURCES)
    assert set(result) == {"ok", "signature"} and result["ok"] is True
    return result


class TestCheckFormula:
    def test_the_whole_result_is_the_vocabulary_its_value_is(self, returned):
        whole = check_formula("Dog(rex)", signature=returned)
        value = check_formula("Dog(rex)", signature=returned["signature"])
        assert whole == value
        assert whole["ok"] is True and whole["signature_errors"] == []

    def test_the_whole_result_still_holds_a_text_to_the_vocabulary(self, returned):
        flagged = check_formula("Cat(rex)", signature=returned)
        assert flagged["ok"] is False
        assert [(e["kind"], e["symbol"]) for e in flagged["signature_errors"]] == [("unknown_predicate", "Cat")]
        assert flagged == check_formula("Cat(rex)", signature=returned["signature"])

    def test_the_loose_form_is_a_vocabulary_as_before(self):
        assert check_formula("Dog(rex)", signature={"predicates": {"Dog": 1}, "constants": ["rex"]})["ok"] is True

    @pytest.mark.parametrize("shape", [
        {"ok": True, "signature": {"predicates": {"Dog": 1}}, "note": "extra key"},
        {"ok": False, "signature": {"predicates": {"Dog": 1}}},
        {"ok": True, "signature": "not a dict"},
        {"ok": True},
    ], ids=["extra-key", "not-ok", "value-not-a-dict", "no-value"])
    def test_a_dict_that_is_not_exactly_such_a_result_is_refused_by_name(self, shape):
        result = check_formula("Dog(rex)", signature=shape)
        assert set(result) == {"error"} and result["error"]["type"] in ("ValueError", "TypeError")


class TestDiagnose:
    def test_the_whole_result_is_the_vocabulary_its_value_is(self, returned):
        whole = diagnose("Dog(rex)", signature=returned)
        assert whole["converged"] is True and whole["suggestion"] is None
        assert whole == diagnose("Dog(rex)", signature=returned["signature"])

    def test_a_text_outside_the_vocabulary_does_not_converge(self, returned):
        step = diagnose("Cat(rex)", signature=returned)
        assert step["converged"] is False
        assert step == diagnose("Cat(rex)", signature=returned["signature"])

    def test_a_result_that_is_not_ok_is_refused_by_name(self):
        result = diagnose("Dog(rex)", signature={"ok": False, "argument": "formula[0]", "errors": []})
        assert set(result) == {"error"}
