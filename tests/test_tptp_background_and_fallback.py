"""What the TPTP writers and the prover adapters do with problems they cannot write as asked.

Four things are pinned, each with the answer worked out by hand:

* **The automatic fallback.** With ``tff=None`` the typed (TF0) writer is tried when a sorted
  node occurs, and EVERY refusal of it is answered with the ``fof`` problem, which asks the
  kit's question: also the refusal of a node the typed writer does not cover and the ``fof``
  writer does (a counting quantifier, ``Contrast``, ``Measure``). Only a problem both writers
  refuse stays refused. ``∃≥2 x:S P(x) ⊢ ∃≥2 x P(x)`` is valid: two elements of ``S`` that
  satisfy ``P`` are two elements that satisfy ``P``.
* **Premise names and background.** ``api.prove(signature=..., premise_names=...)`` names the
  premises the caller passed; the sentences a signature adds (and the side axioms of a
  ``Sentence``) are background and are named by the writer.
* **The typed arithmetic writer's refusals** reach ``api.prove`` as ``unknown`` /
  ``unsupported`` with the writer's message, never as an exception.
* **Truth constants and nullary functions.** ``$true`` and ``$false`` are written unquoted by
  the repair tool, and a function of no arguments is the constant of its name.
"""

import shutil

import pytest

from unicode_logic_kit import api
from unicode_logic_kit.atp._tff_problem import TfaRefusal, generate_tff_arith_problem
from unicode_logic_kit.atp._tptp_problem import (
    generate_tptp_problem, generate_tptp_problem_for_prover, generate_tptp_problem_with_mapping,
)
from unicode_logic_kit.atp._writer_support import name_background_premises
from unicode_logic_kit.atp.eprover_backend import eprover_available
from unicode_logic_kit.atp.protocol import get_backend
from unicode_logic_kit.atp.vampire_entailment import check_logical_entailment_vampire
from unicode_logic_kit.fol._msfl_nodes import signature_axioms
from unicode_logic_kit.fol.nodes import (
    Atom, Box, Constant, Contrast, Count, Function, Measure, Number, SortedConstant,
    SortedCount, SortedQuantifier, Variable,
)
from unicode_logic_kit.fol.signature import Signature
from unicode_logic_kit.fol.tptp_repair import repair_tptp_formula, repair_tptp_problem
from unicode_logic_kit.logic import Sentence

_X = Variable("x")

_NATIVE_VAMPIRE = shutil.which("vampire")
VAMPIRE = (dict(vampire_path=_NATIVE_VAMPIRE, use_wsl=False) if _NATIVE_VAMPIRE
           else dict(vampire_path="vampire", use_wsl=True))
HAVE_VAMPIRE = get_backend("vampire").available_for(VAMPIRE)
needs_vampire = pytest.mark.skipif(not HAVE_VAMPIRE, reason="no Vampire the kit can run")
needs_eprover = pytest.mark.skipif(not eprover_available(), reason="no eprover binary found")


def atom(name, *args):
    return Atom(name, list(args))


# =============================================================================
# The automatic mode falls back to fof for every refusal of the typed writer
# =============================================================================

def _two_s_that_are_p():
    """``∃≥2 x:S P(x)  ⊢  ∃≥2 x P(x)``."""
    return Count("ge", Number(2), _X, atom("P", _X)), [
        SortedCount("ge", Number(2), _X, "S", atom("P", _X))]


def _contrast_of_a_member():
    """``∀x:S P(x)  ⊢  P(c:S) Ⓒ P(c:S)``: Ⓒ is conjunction, and ``c`` is in ``S``."""
    c = SortedConstant("c", "S")
    return Contrast(atom("P", c), atom("P", c)), [SortedQuantifier("∀", _X, "S", atom("P", _X))]


def _a_measure_that_is_a_premise():
    """``P(measure(alp, kg)), ∀y:Ss Q(y)  ⊢  P(measure(alp, kg))``: the goal is a premise."""
    held = atom("P", Measure(Constant("alp"), Constant("kg")))
    return held, [held, SortedQuantifier("∀", Variable("y"), "Ss", atom("Q", Variable("y")))]


def _a_count_that_is_a_premise():
    """``∃≥2 x P(x), ∀y:Ss Q(y)  ⊢  ∃≥2 x P(x)``: the goal is a premise."""
    held = Count("ge", Number(2), _X, atom("P", _X))
    return held, [held, SortedQuantifier("∀", Variable("y"), "Ss", atom("Q", Variable("y")))]


FALLBACK_PROBLEMS = [
    pytest.param(_two_s_that_are_p, "Count", id="a counting quantifier next to a sorted one"),
    pytest.param(_contrast_of_a_member, "Contrast", id="Contrast next to a sorted quantifier"),
    pytest.param(_a_measure_that_is_a_premise, "Measure", id="Measure next to a sorted quantifier"),
    pytest.param(_a_count_that_is_a_premise, "Count", id="an unsorted count next to a sorted quantifier"),
]


@pytest.mark.parametrize("build, node", FALLBACK_PROBLEMS)
def test_a_node_only_the_fof_writer_covers_is_written_as_fof_in_the_automatic_mode(build, node):
    goal, premises = build()
    built = generate_tptp_problem_for_prover(premises, goal)
    assert built.dialect == "fof"
    assert node in built.tff_refusal and "TF0" in built.tff_refusal
    assert "typed (TF0) writer refused" in built.fallback_note and node in built.fallback_note
    assert built.text.startswith("fof(")
    # what the problem says is what the forced fof route says
    assert built.text == generate_tptp_problem_for_prover(premises, goal, tff=False).text


@pytest.mark.parametrize("build, node", FALLBACK_PROBLEMS)
def test_the_forced_typed_route_and_the_forced_fof_route_are_unchanged(build, node):
    goal, premises = build()
    with pytest.raises(NotImplementedError, match=node):
        generate_tptp_problem_for_prover(premises, goal, tff=True)
    forced = generate_tptp_problem_for_prover(premises, goal, tff=False)
    assert forced.dialect == "fof" and forced.tff_refusal is None and forced.fallback_note is None


def test_a_problem_both_writers_refuse_stays_refused_with_the_typed_refusal_as_its_cause():
    premises = [SortedQuantifier("∀", _X, "S", atom("P", _X))]
    goal = Box(atom("P", Constant("aa")))
    with pytest.raises(NotImplementedError, match="Modal") as refused:
        generate_tptp_problem_for_prover(premises, goal)
    assert isinstance(refused.value.__cause__, NotImplementedError)
    assert "native TF0" in str(refused.value.__cause__)


def test_a_problem_without_a_sorted_node_is_written_as_fof_without_a_refusal():
    built = generate_tptp_problem_for_prover([Count("ge", Number(2), _X, atom("P", _X))],
                                             Count("ge", Number(2), _X, atom("P", _X)))
    assert built.dialect == "fof" and built.tff_refusal is None


@needs_vampire
@pytest.mark.parametrize("build, node", FALLBACK_PROBLEMS)
def test_live_vampire_proves_what_the_fallback_writes(build, node):
    goal, premises = build()
    verdict = api.prove(goal, premises, backends=["vampire"], timeout=60000, **VAMPIRE)
    assert verdict.status == "proved", (verdict.reason, verdict.detail)
    assert "typed (TF0) writer refused" in verdict.detail
    assert api.prove(goal, premises, backends=["z3"], timeout=30000).status == "proved"


@needs_eprover
@pytest.mark.parametrize("build, node", FALLBACK_PROBLEMS)
def test_live_e_proves_what_the_fallback_writes(build, node):
    goal, premises = build()
    verdict = api.prove(goal, premises, backends=["eprover"], timeout=60000)
    assert verdict.status == "proved", (verdict.reason, verdict.detail)
    assert "typed (TF0) writer refused" in verdict.detail


@needs_vampire
def test_live_the_typed_route_alone_reports_the_refusal_as_unsupported_with_its_message():
    goal, premises = _two_s_that_are_p()
    verdict = api.prove(goal, premises, backends=["vampire"], timeout=60000, tff=True, **VAMPIRE)
    assert verdict.status == "unknown"
    assert "unsupported" in verdict.detail and "'Count'" in verdict.detail


# =============================================================================
# premise_names= and the sentences a signature adds
# =============================================================================

SIGNATURE = Signature.from_dict({"sorts": ["Human"], "constants": {"socrates": "Human"},
                                 "predicates": {"Mortal": 1}})
ALL_MORTAL = SortedQuantifier("∀", _X, "Human", atom("Mortal", _X))
RAIN = atom("Rain")
SOCRATES_IS_MORTAL = atom("Mortal", SortedConstant("socrates", "Human"))


def test_the_background_of_a_signature_gets_names_of_the_writers_next_to_the_callers():
    """``∃x Human(x)`` and ``Human(socrates)`` are the two sentences the signature adds."""
    assert len(signature_axioms(SIGNATURE)) == 2
    assert name_background_premises(["allmortal", "rain"], 2, 4, where="prove") == (
        "allmortal", "rain", "background_1", "background_2")
    assert name_background_premises(["a"], 1, 1, where="prove") == ("a",)


def test_a_generated_background_name_is_never_one_of_the_callers():
    names = name_background_premises(["background_1", "background_2_"], 2, 4, where="prove")
    assert names[:2] == ("background_1", "background_2_")
    assert len(set(names)) == 4 and "background_1" not in names[2:]


@pytest.mark.parametrize("names, error, text", [
    (["only one"], ValueError, "there are 2 premises and 1 name"),
    (["a", "b", "c", "d"], ValueError, "there are 2 premises and 4 names"),
    ("ab", TypeError, "single str"),
    (["a", 3], TypeError, r"premise_names\[1\] must be a string"),
    (["same", "same"], ValueError, "pairwise distinct"),
])
def test_the_names_are_checked_against_the_premises_the_caller_passed(names, error, text):
    with pytest.raises(error, match=text):
        name_background_premises(names, 2, 4, where="prove")


def test_the_problem_written_for_the_padded_names_names_every_line():
    options = {"premise_names": ["allmortal", "rain"]}
    from unicode_logic_kit.api import _name_background
    padded = _name_background(options, 2, 4, "prove")["premise_names"]
    premises = [ALL_MORTAL, RAIN] + list(signature_axioms(SIGNATURE))
    text, record = generate_tptp_problem_with_mapping(premises, SOCRATES_IS_MORTAL, premise_names=padded)
    for name in ("allmortal", "rain", "background_1", "background_2"):
        assert f"fof({name}, axiom," in text
    assert record.premises == ("allmortal", "rain", "background_1", "background_2")


def test_nothing_is_padded_without_names_or_without_background():
    from unicode_logic_kit.api import _name_background
    assert _name_background({}, 2, 4, "prove") == {}
    assert _name_background({"premise_names": None}, 2, 4, "prove") == {"premise_names": None}
    names = ["a", "b"]
    assert _name_background({"premise_names": names}, 2, 2, "prove")["premise_names"] is names


@needs_vampire
@pytest.mark.parametrize("names", [["allmortal", "rain"], ["it's a premise", "ünï"]],
                         ids=["plain names", "a space, a quote, a non-ASCII letter"])
def test_live_vampire_reads_the_callers_premises_back_through_a_signature(names):
    """``∀x:Human Mortal(x)`` and ``socrates:Human`` prove ``Mortal(socrates)``; ``Rain`` is
    not needed. The signature's sentences are background: the indices are the caller's."""
    verdict = api.prove(SOCRATES_IS_MORTAL, [ALL_MORTAL, RAIN], backends=["vampire"],
                        signature=SIGNATURE, premise_names=names, relevant_premises=True,
                        timeout=60000, **VAMPIRE)
    assert verdict.status == "proved", (verdict.reason, verdict.detail)
    assert verdict.relevant_premises == (0,)


@needs_eprover
@pytest.mark.parametrize("names", [["allmortal", "rain"], ["it's a premise", "ünï"]],
                         ids=["plain names", "a space, a quote, a non-ASCII letter"])
def test_live_e_reads_the_callers_premises_back_through_a_signature(names):
    verdict = api.prove(SOCRATES_IS_MORTAL, [ALL_MORTAL, RAIN], backends=["eprover"],
                        signature=SIGNATURE, premise_names=names, relevant_premises=True,
                        timeout=60000)
    assert verdict.status == "proved", (verdict.reason, verdict.detail)
    assert verdict.relevant_premises == (0,)


@needs_vampire
def test_live_the_side_axioms_of_a_sentence_are_background_for_the_names_too():
    """The goal as a Sentence carries the axiom ``Qq(aa)`` of its own; the caller names its one
    premise only."""
    goal = Sentence(term=atom("Qq", Constant("aa")), logic="fol", axioms=(atom("Qq", Constant("aa")),))
    verdict = api.prove(goal, [atom("Rr", Constant("bb"))], backends=["vampire"],
                        premise_names=["unused"], timeout=60000, **VAMPIRE)
    assert verdict.status == "proved", (verdict.reason, verdict.detail)


def test_a_wrong_number_of_names_is_refused_against_the_premises_the_caller_passed():
    with pytest.raises(ValueError, match="there are 2 premises and 4 names"):
        api.prove(SOCRATES_IS_MORTAL, [ALL_MORTAL, RAIN], backends=["vampire"], signature=SIGNATURE,
                  premise_names=["a", "b", "c", "d"], **VAMPIRE)


# =============================================================================
# The typed arithmetic writer's refusals are refusals
# =============================================================================

TFA_REFUSALS = [
    pytest.param(atom("Pp", Constant("alp"), Constant("bet")), [atom("Pp", Constant("alp"))],
                 "conflicting arities 1 and 2", id="a predicate at two arities"),
    pytest.param(atom("Pp", Constant("alp")), [atom("Pp", Function("alp", [Constant("bet")]))],
                 "both as a constant and as a function", id="a name that is a constant and a function"),
    pytest.param(atom("Pp", _X), [atom("Pp", Constant("alp"))],
                 "free variable", id="a free variable in the goal"),
    pytest.param(atom("Pp", Constant("alp")), [atom("Pp", _X)],
                 "free variable", id="a free variable in a premise"),
    pytest.param(atom("Pp", Function("ff", [Constant("alp")])),
                 [atom("Pp", Function("ff", [Constant("alp"), Constant("bet")]))],
                 "function 'ff' used with conflicting arities", id="a function at two arities"),
]


@pytest.mark.parametrize("goal, premises, message", TFA_REFUSALS)
def test_the_typed_arithmetic_writer_refuses_by_name_with_an_error_of_both_kinds(goal, premises, message):
    with pytest.raises(TfaRefusal, match=message) as refused:
        generate_tff_arith_problem(premises, goal, sort="int")
    assert isinstance(refused.value, ValueError) and isinstance(refused.value, NotImplementedError)
    with pytest.raises(NotImplementedError, match="generate_tff_arith_problem"):
        check_logical_entailment_vampire(premises, goal, "vampire", sort="real")


def test_an_invalid_sort_is_still_a_plain_value_error():
    with pytest.raises(ValueError, match="must be 'real' or 'int'") as refused:
        generate_tff_arith_problem([], atom("Pp", Constant("alp")), sort="complex")
    assert not isinstance(refused.value, NotImplementedError)


@needs_vampire
@pytest.mark.parametrize("sort", ["int", "real"])
@pytest.mark.parametrize("goal, premises, message", TFA_REFUSALS)
def test_live_vampire_through_api_prove_answers_unknown_unsupported_for_a_refusal(
        goal, premises, message, sort):
    verdict = api.prove(goal, premises, backends=["vampire"], sort=sort, timeout=60000, **VAMPIRE)
    assert verdict.status == "unknown"
    assert "vampire:unknown/unsupported" in verdict.detail and message in verdict.detail


@needs_eprover
@pytest.mark.parametrize("sort", ["int", "real"])
@pytest.mark.parametrize("goal, premises, message", TFA_REFUSALS)
def test_live_e_through_api_prove_answers_unknown_unsupported_for_a_refusal(
        goal, premises, message, sort):
    verdict = api.prove(goal, premises, backends=["eprover"], sort=sort, timeout=60000)
    assert verdict.status == "unknown"
    assert "eprover:unknown/unsupported" in verdict.detail and message in verdict.detail


# =============================================================================
# A function of no arguments is the constant of its name
# =============================================================================

def test_the_fof_writer_writes_a_function_of_no_arguments_as_the_constant_of_its_name():
    held = atom("Pp", Function("fzero", []))
    text = generate_tptp_problem([held], held)
    assert "pp(fzero)" in text and "fzero()" not in text
    # one symbol: the function and the constant of that name are written alike
    same = generate_tptp_problem([held], atom("Pp", Constant("fzero")))
    assert same.count("pp(fzero)") == 2


def test_a_function_of_no_arguments_deep_in_a_formula_is_written_without_brackets():
    nullary = Function("fzero", [])
    formula = Atom("=", [Function("gg", [nullary, Function("hh", [nullary])]), nullary])
    text = generate_tptp_problem([], formula)
    assert "fzero(" not in text and "gg(fzero,hh(fzero)) = fzero" in text


@needs_vampire
@pytest.mark.parametrize("options", [{}, {"tff": False}, {"tff": True}], ids=["auto", "fof", "tf0"])
def test_live_vampire_proves_a_goal_that_is_a_premise_about_a_function_of_no_arguments(options):
    held = atom("Pp", Function("fzero", []))
    verdict = api.prove(held, [held], backends=["vampire"], timeout=60000, **options, **VAMPIRE)
    assert verdict.status == "proved", (verdict.reason, verdict.detail)


# =============================================================================
# tptp_repair keeps TPTP's own propositions
# =============================================================================

@pytest.mark.parametrize("text", [
    "fof(b,axiom,$false).\nfof(c,conjecture,q).\n",
    "fof(a,axiom,($true & p)).\nfof(c,conjecture,$true).\n",
    "cnf(a,axiom,($false | p)).\n",
])
def test_a_problem_with_truth_constants_needs_no_repair_and_keeps_them(text):
    """``'$false'`` in single quotes is an ordinary atom to Vampire (``$false`` as an axiom is
    contradictory, the atom is not), so the text must not change."""
    repaired = repair_tptp_problem(text)
    assert repaired.repaired_text == text
    assert repaired.changed is False


@pytest.mark.parametrize("text, expected", [
    ("p => $true", "(p => $true)"),
    ("$false", "$false"),
    ("$true | q", "($true | q)"),
    ("![X]: (p(X) => $false)", "(![X]: (p(X) => $false))"),
])
def test_a_formula_with_truth_constants_is_written_back_with_them_unquoted(text, expected):
    assert repair_tptp_formula(text).repaired_text == expected
    assert "'$" not in repair_tptp_formula(text).repaired_text
