"""The truth constants are logical constants, not vocabulary.

``⊤`` / ``$true`` and ``⊥`` / ``$false`` read to the nullary atoms ``$true`` and ``$false``
(the TPTP reader, the SMT-LIB reader, the LaTeX reader and the unicode grammar all
produce them), and an atom NAMED like a glyph (``Atom('⊤', ())``) is the same constant.
None of them is a predicate of the user's, so the vocabulary layer must neither list them
nor flag them: ``P → ⊥`` mentions one predicate, ``P`` of arity 0.

Hand-derived expectations: the inventory of ``P → ⊥`` is ``('P/0',)``; of ``∀x (P(x) → ⊥)``
it is ``('P/1',)``; of ``⊤ ∧ ⊤(alpha)`` (the constant and a user predicate that is spelled
like it and takes an argument) it is ``('$true/1',)``, and the two never conflict, because
the constant is not a predicate.
"""

import pytest

from unicode_logic_kit import api
from unicode_logic_kit.eval.validate import validate
from unicode_logic_kit.fol.nodes import And, Atom, Constant, Implies, Quantifier, Variable
from unicode_logic_kit.fol.signature import Signature

#: The four spellings that reach the vocabulary layer as nodes: the two atoms the readers
#: produce, and the two atoms named like the glyphs.
TRUE_SPELLINGS = [Atom("$true", ()), Atom("⊤", ())]
FALSE_SPELLINGS = [Atom("$false", ()), Atom("⊥", ())]
P = Atom("P", ())


@pytest.mark.parametrize("constant", TRUE_SPELLINGS + FALSE_SPELLINGS, ids=repr)
def test_the_inventory_does_not_list_a_truth_constant(constant):
    report = validate(Implies(P, constant))
    assert report.predicates == ("P/0",)
    assert report.arity_consistent and report.arity_conflicts == {}
    assert validate(constant).predicates == ()


@pytest.mark.parametrize("constant", FALSE_SPELLINGS, ids=repr)
def test_a_constant_under_a_quantifier_is_not_listed_either(constant):
    x = Variable("x")
    formula = Quantifier("∀", x, Implies(Atom("P", (x,)), constant))
    assert validate(formula).predicates == ("P/1",)


def test_a_user_predicate_spelled_like_a_constant_is_a_predicate_and_never_conflicts():
    both = And(Atom("$true", ()), Atom("$true", (Constant("alpha"),)))
    report = validate(both)
    assert report.predicates == ("$true/1",)           # the one with an argument is the user's
    assert report.arity_consistent
    assert report.arity_conflicts == {}


@pytest.mark.parametrize("constant", TRUE_SPELLINGS + FALSE_SPELLINGS, ids=repr)
def test_check_does_not_flag_a_constant_against_any_form_of_signature(constant):
    formula = Implies(P, constant)
    declared = {"predicates": {"P": 0}}
    for signature in (Signature.from_formulas([formula]), declared,
                      Signature.from_formulas([formula]).to_dict()):
        result = api.check(formula, signature=signature)
        assert result.ok, result.signature_errors
        assert result.signature_errors == ()
        assert result.predicates == ("P/0",)
    # A signature that really lacks P still flags it, and names only P.
    result = api.check(formula, signature={"predicates": {"Q": 0}})
    assert not result.ok
    assert [(e["kind"], e["symbol"]) for e in result.signature_errors] == [("unknown_predicate", "P")]


def test_the_signature_of_a_formula_with_a_constant_passes_check_unchanged():
    formula = api.parse_any("∀x (P(x) → ⊥)").formula
    assert api.check(formula, signature=Signature.from_formulas([formula])).ok
    assert api.check("∀x (P(x) → ⊥)", signature={"predicates": {"P": 1}}).ok


# ---------------------------------------------------------------------------
# What Signature.to_dict() returns is accepted by check, unchanged
# ---------------------------------------------------------------------------

def test_the_rich_dict_is_read_as_the_signature_it_describes():
    formula = api.parse_any("∀x (Dog(x) → Animal(x)) ∧ Dog(rex)").formula
    rich = Signature.from_formulas([formula]).to_dict()
    assert rich["predicates"]["Dog"] == {"arity": 1, "arg_sorts": None}      # the shape that was misread
    assert api.check(formula, signature=rich).ok
    other = api.parse_any("Cat(rex)").formula
    kinds = [e["kind"] for e in api.check(other, signature=rich).signature_errors]
    assert kinds == ["unknown_predicate"]


def test_the_rich_dict_keeps_the_arity_and_the_sorts_it_declares():
    wrong_arity = {"predicates": {"P": {"arity": 2, "arg_sorts": None}}, "constants": {"alpha": None}}
    (error,) = api.check("P(alpha)", signature=wrong_arity).signature_errors
    assert (error["kind"], error["symbol"], error["expected"], error["seen"]) == ("wrong_arity", "P", [2], 1)

    declared = {"sorts": ["A", "B"], "constants": {"carl": "B"}}
    # carl is declared in B but written carl:A: one constant, two sorts, and the signature says B.
    result = api.check("P(carl:A)", signature={**declared, "predicates": {"P": {"arity": 1, "arg_sorts": None}}})
    assert not result.ok
    assert [e["kind"] for e in result.signature_errors] == ["sort_mismatch"]
    agreeing = {**declared, "constants": {"carl": "A"}, "predicates": {"P": {"arity": 1, "arg_sorts": None}}}
    assert api.check("P(carl:A)", signature=agreeing).ok


# ---------------------------------------------------------------------------
# A malformed signature is the caller's mistake, named, never a verdict about the formula
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("signature,error,needle", [
    # a dict whose content is invalid: ValueError, the kind the command line reports cleanly
    ({"predicates": 5}, ValueError, "predicates"),
    ({"predicates": {"P": "one"}}, ValueError, "'P'"),
    ({"predicates": {"P": 1.5}}, ValueError, "'P'"),
    ({"functions": ["f"]}, ValueError, "functions"),
    ({"constants": "alpha"}, ValueError, "constants"),
    ({"constants": [1, 2]}, ValueError, "constants"),
    ({"predicate": {"P": 0}}, ValueError, "predicate"),
    ({"predicates": {"P": {"arity": "x"}}}, ValueError, "arity"),
    ({"subsorts": {"A": "B"}}, ValueError, "subsorts"),
    # an argument that is not a dict or a Signature at all: TypeError
    (["P"], TypeError, "list"),
    (42, TypeError, "int"),
])
def test_a_malformed_signature_raises_and_names_what_is_wrong(signature, error, needle):
    with pytest.raises(error, match=needle):
        api.check("P", signature=signature)
    with pytest.raises(error, match=needle):                 # also for text that does not parse
        api.check("P(", signature=signature)


def test_the_loose_forms_that_were_always_read_still_are():
    assert api.check("P(alpha) ∧ Q(alpha, beta)", signature={"predicates": {"P": 1, "Q": [1, 2]},
                                                              "constants": ["alpha", "beta"]}).ok
    assert api.check("P(alpha)", signature={}).ok            # nothing declared, nothing constrained
    wrong = api.check("P(alpha, beta)", signature={"predicates": {"P": [1]}})
    assert [e["kind"] for e in wrong.signature_errors] == ["wrong_arity"]
    assert wrong.signature_errors[0]["expected"] == [1]


def test_the_command_line_reads_a_signature_file_in_either_form(tmp_path, capsys):
    import json
    from unicode_logic_kit.__main__ import main

    rich = Signature.from_formulas([Implies(P, Atom("$false", ()))]).to_dict()
    for name, content, exit_code in (("rich.json", rich, 0), ("loose.json", {"predicates": {"P": 0}}, 0),
                                     ("other.json", {"predicates": {"Q": 0}}, 1)):
        path = tmp_path / name
        path.write_text(json.dumps(content), encoding="utf-8")
        assert main(["check", "P → ⊥", "--signature", str(path), "--json"]) == exit_code
    capsys.readouterr()
    bad = tmp_path / "bad.json"
    bad.write_text(json.dumps({"predicates": 5}), encoding="utf-8")
    assert main(["check", "P → ⊥", "--signature", str(bad)]) == 3          # one clean message, no traceback
    assert "predicates" in capsys.readouterr().err


def test_repair_refuses_a_malformed_signature_before_any_round():
    with pytest.raises(ValueError, match="predicates"):
        next(api.repair("P(", signature={"predicates": 5}))     # text that does not parse
