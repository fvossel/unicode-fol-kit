"""The kit's ``truth_constants`` rule in TSTP: its name, its writer and its independent checker.

The resolution checker licenses ``truth_constants`` (one parent: the stated clause is the parent
without some literals that hold in no interpretation, ``$false`` and ``¬$true``). TSTP has a
rule for exactly that: Vampire 5.0.1 prints ``true_and_false_elimination`` (captured live in
``tests/fixtures/tstp_check/vampire_true_and_false_elimination.txt``: ``p | $false`` gives
``p`` and ``~p | q | ~$true`` gives ``~p | q``). The writer gives the kit's rule that name, and
:func:`~unicode_fol_kit.atp.tstp_check.check_tstp_derivation` re-derives it from the parent.

Every accept and every reject below is worked by hand from the rule: a literal that holds in
no interpretation may be dropped, and nothing else may be dropped or added.
"""

import shutil
from pathlib import Path

import pytest

from unicode_fol_kit.fol.nodes import Atom, Not, Or
from unicode_fol_kit.fol.tptp_input import parse_tptp_formula
from unicode_fol_kit.atp.resolution_check import (
    _RULE_ARITY, ResolutionDerivation, ResolutionStep, verify_resolution_proof,
)
from unicode_fol_kit.atp.tstp import _KIT_RULE_TO_TSTP, parse_tstp_derivation, to_tstp
from unicode_fol_kit.atp.tstp_check import (
    EPROVER_CHECKED_RULES, VAMPIRE_CHECKED_RULES, _CHECKED_DISPATCH, _node_to_clause,
    check_tstp_derivation,
)

TRUE = Atom("$true", ())
FALSE = Atom("$false", ())
P = Atom("P", ())
Q = Atom("Q", ())

_FIXTURES = Path(__file__).parent / "fixtures" / "tstp_check"


def _check(text, premise_texts):
    """The checker's verdict on a derivation whose leaves are exactly ``premise_texts``."""
    premises = [parse_tptp_formula(t) for t in premise_texts]
    return check_tstp_derivation(parse_tstp_derivation(text), premises, None, query="refutation")


# ---------------------------------------------------------------------------
# The name
# ---------------------------------------------------------------------------

def test_the_kit_rule_is_written_under_vampires_name_for_it():
    assert _KIT_RULE_TO_TSTP["truth_constants"] == "true_and_false_elimination"


def test_every_kit_rule_has_a_tstp_name_the_checker_re_derives():
    assert set(_KIT_RULE_TO_TSTP) == set(_RULE_ARITY) - {"input"}
    checked = VAMPIRE_CHECKED_RULES | EPROVER_CHECKED_RULES
    for kit_rule, tstp_rule in _KIT_RULE_TO_TSTP.items():
        assert tstp_rule in checked, kit_rule
        assert tstp_rule in _CHECKED_DISPATCH, kit_rule
    assert set(_CHECKED_DISPATCH) == checked


def test_the_rule_takes_one_parent():
    assert _CHECKED_DISPATCH["true_and_false_elimination"][0] == 1
    assert _RULE_ARITY["truth_constants"] == 1


# ---------------------------------------------------------------------------
# The writer
# ---------------------------------------------------------------------------

def _kit_derivation(first, first_reduced, second, second_reduced):
    """``first`` and ``second`` as input clauses, each reduced by ``truth_constants``, and the
    two reductions resolved to the empty clause."""
    steps = (
        ResolutionStep(1, first, "input"),
        ResolutionStep(2, second, "input"),
        ResolutionStep(3, first_reduced, "truth_constants", (1,)),
        ResolutionStep(4, second_reduced, "truth_constants", (2,)),
        ResolutionStep(5, frozenset(), "resolve", (3, 4)),
    )
    return ResolutionDerivation((first, second), steps)


@pytest.mark.parametrize("false_literal, true_negated", [
    (FALSE, Not(TRUE)),
    (Atom("⊥", ()), Not(Atom("⊤", ()))),
], ids=["tptp-words", "glyph-atoms"])
def test_the_writer_names_the_rule_and_the_checker_verifies_what_it_writes(false_literal, true_negated):
    derivation = _kit_derivation(frozenset({P, false_literal}), frozenset({P}),
                                 frozenset({Not(P), true_negated}), frozenset({Not(P)}))
    assert verify_resolution_proof(derivation).ok
    text = to_tstp(derivation)
    assert "$false" in text and "⊥" not in text and "⊤" not in text
    assert "inference(true_and_false_elimination, [status(thm)], [c1])" in text
    assert "inference(true_and_false_elimination, [status(thm)], [c2])" in text
    parsed = parse_tstp_derivation(text)
    assert [s.rule for s in parsed.steps] == [None, None, "true_and_false_elimination",
                                              "true_and_false_elimination", "resolution"]
    leaves = [s.formula for s in parsed.steps if s.rule is None]
    result = check_tstp_derivation(parsed, leaves, None, query="refutation")
    assert result.verified, result.error
    assert result.refuted
    assert [s.tier for s in result.steps] == ["leaf", "leaf", "checked", "checked", "checked"]


# ---------------------------------------------------------------------------
# The checker: what it accepts
# ---------------------------------------------------------------------------

_ELIMINATION = (
    "cnf(c1, axiom, {parent}).\n"
    "cnf(c2, plain, {child}, inference(true_and_false_elimination,[],[c1])).\n"
)


@pytest.mark.parametrize("parent, child", [
    ("(p | $false)", "p"),                                   # $false is dropped
    ("(~p | q | ~$true)", "(~p | q)"),                       # ~$true is dropped
    ("($false | $false)", "$false"),                         # both are, and nothing is left
    ("(p | q | $false | ~$true)", "(p | q)"),                # several at once
    ("(p | $false | ~$true)", "(p | ~$true)"),               # only one of two (still sound)
    ("(q(X,Y) | $false)", "q(A,B)"),                         # variables are renamed by the prover
    ("(p | q)", "(p | q)"),                                  # nothing to drop: the clause itself
    ("($false)", "$false"),                                  # the empty clause from itself
], ids=["false", "not-true", "empty", "several", "one-of-two", "variants", "identity", "empty-clause"])
def test_a_clause_without_some_false_literals_is_licensed(parent, child):
    text = _ELIMINATION.format(parent=parent, child=child)
    result = _check(text, [parent])
    assert result.verified, result.error
    assert result.steps[1].tier == "checked"


def test_deriving_the_empty_clause_by_the_rule_counts_as_a_refutation():
    result = _check(_ELIMINATION.format(parent="($false | $false)", child="$false"),
                    ["($false | $false)"])
    assert result.verified and result.refuted


# ---------------------------------------------------------------------------
# The checker: what it rejects
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("parent, child, why", [
    ("(p | q | $false)", "p", "dropping an ordinary literal besides the constant"),
    ("(p | q)", "p", "dropping an ordinary literal and no constant"),
    ("(p | $true)", "p", "$true holds in every interpretation: it is not a literal to drop"),
    ("(p | ~$false)", "p", "~$false holds in every interpretation: it is not a literal to drop"),
    ("p", "(p | $false)", "keeping a constant literal the parent does not have"),
    ("(p | $false)", "(p | q)", "adding a literal the parent does not have"),
    ("(p | $false)", "$false", "dropping the ordinary literal and keeping the constant"),
    ("(p | $false)", "q", "a clause that is another clause altogether"),
    ("(p(X) | $false)", "p(a)", "an instance is not a variant"),
    ("(p | ~$true)", "(p | $true)", "a constant that is not among the parent's literals"),
], ids=["extra-dropped", "plain-dropped", "true-dropped", "not-false-dropped", "constant-added",
        "literal-added", "wrong-literal-kept", "other-clause", "instance", "swapped-constant"])
def test_any_other_change_to_the_clause_is_rejected(parent, child, why):
    text = _ELIMINATION.format(parent=parent, child=child)
    result = _check(text, [parent])
    assert not result.verified, why
    assert "true_and_false_elimination" in result.error, why
    assert result.steps[1].tier == "checked" and not result.steps[1].ok


def test_a_parent_that_is_not_a_flat_clause_is_not_approximately_checked():
    # Vampire also prints the rule on whole formulas; only a clause is re-derived here
    text = ("fof(c1, axiom, ((p & q) | $false)).\n"
            "fof(c2, plain, (p & q), inference(true_and_false_elimination,[],[c1])).\n")
    result = check_tstp_derivation(
        parse_tstp_derivation(text), [parse_tptp_formula("((p & q) | $false)")], None,
        query="refutation")
    assert not result.verified
    assert "flat clausal" in result.error


def test_the_rule_cites_exactly_one_parent():
    text = ("cnf(c1, axiom, (p | $false)).\n"
            "cnf(c2, axiom, (q | $false)).\n"
            "cnf(c3, plain, p, inference(true_and_false_elimination,[],[c1,c2])).\n")
    result = _check(text, ["(p | $false)", "(q | $false)"])
    assert not result.verified
    assert "takes 1 parent" in result.error


def test_a_parent_that_failed_to_verify_is_not_built_on():
    # c1 is not one of the caller's premises, so the leaf is refused and nothing stands on it
    text = _ELIMINATION.format(parent="(p | $false)", child="p")
    result = _check(text, ["(q | $false)"])
    assert not result.verified
    assert result.steps[0].tier == "leaf" and not result.steps[0].ok
    assert not result.steps[1].ok


# ---------------------------------------------------------------------------
# The clause reading that keeps the constants
# ---------------------------------------------------------------------------

def test_the_clause_reading_keeps_the_constants_only_on_request():
    formula = parse_tptp_formula("(p | $false)")
    assert _node_to_clause(formula) is None                       # not a clause of letters
    assert _node_to_clause(formula, keep_constants=True) == frozenset({P, FALSE})
    negated = parse_tptp_formula("(~p | ~$true)")
    assert _node_to_clause(negated, keep_constants=True) == frozenset({Not(P), Not(TRUE)})
    # the formula $false alone is the empty clause either way
    assert _node_to_clause(FALSE) == frozenset()
    assert _node_to_clause(FALSE, keep_constants=True) == frozenset()


# ---------------------------------------------------------------------------
# A proof Vampire printed
# ---------------------------------------------------------------------------

def test_a_real_vampire_proof_that_eliminates_constants_verifies_end_to_end():
    text = (_FIXTURES / "vampire_true_and_false_elimination.txt").read_text(encoding="utf-8")
    premises = [parse_tptp_formula("p | $false"), parse_tptp_formula("~p | q | ~$true")]
    result = check_tstp_derivation(parse_tstp_derivation(text), premises,
                                   parse_tptp_formula("q"))
    assert result.verified, result.error
    assert result.refuted
    tiers = {s.name: s.tier for s in result.steps}
    assert tiers["f5"] == "checked" and tiers["f6"] == "checked"


def test_the_same_proof_with_one_step_tampered_is_rejected():
    text = (_FIXTURES / "vampire_true_and_false_elimination.txt").read_text(encoding="utf-8")
    # f5 states p, from f1 = p | $false; claim q instead
    tampered = text.replace("fof(f5,plain,(\n  p),", "fof(f5,plain,(\n  q),")
    assert tampered != text
    premises = [parse_tptp_formula("p | $false"), parse_tptp_formula("~p | q | ~$true")]
    result = check_tstp_derivation(parse_tstp_derivation(tampered), premises,
                                   parse_tptp_formula("q"))
    assert not result.verified
    assert "f5" in result.error and "true_and_false_elimination" in result.error


# ---------------------------------------------------------------------------
# A live Vampire
# ---------------------------------------------------------------------------

def _vampire_path():
    import os
    if os.environ.get("UFK_VAMPIRE_WSL") == "1":
        return os.environ.get("UFK_VAMPIRE", "vampire"), True
    found = os.environ.get("UFK_VAMPIRE") or shutil.which("vampire")
    return (found, False) if found else (None, False)


def test_live_vampire_eliminates_the_constants_and_the_checker_agrees():
    from unicode_fol_kit.atp._tptp_problem import generate_tptp_problem
    from unicode_fol_kit.atp.protocol import VampireBackend
    from unicode_fol_kit.atp.vampire_entailment import _spawn_vampire
    path, use_wsl = _vampire_path()
    if path is None or not VampireBackend().available_for({"vampire_path": path, "use_wsl": use_wsl}):
        pytest.skip("no Vampire reachable here")
    premises = [Or(P, FALSE), Or(Or(Not(P), Q), Not(TRUE))]
    problem = generate_tptp_problem(premises, Q)
    stdout, timed_out = _spawn_vampire(problem, path, timeout=30, use_wsl=use_wsl,
                                       extra_args=("--proof", "tptp"))
    assert not timed_out
    parsed = parse_tstp_derivation(stdout)
    eliminations = [s.name for s in parsed.steps if s.rule == "true_and_false_elimination"]
    if not eliminations:
        pytest.skip("this Vampire proves the problem without a true_and_false_elimination step")
    checked = check_tstp_derivation(parsed, premises, Q)
    by_name = {s.name: s for s in checked.steps}
    for name in eliminations:
        assert by_name[name].tier == "checked" and by_name[name].ok, (name, by_name[name].detail)
