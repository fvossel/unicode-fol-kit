"""What the TPTP problem writers refuse, and in whose name they say so.

* A refusal names the entry point the caller called. The whole-problem checks used to say
  ``generate_tptp_problem:`` (or ``generate_tff_problem:``) whichever of the writers, the
  ``*_with_mapping`` variants, the arithmetic writer or the prover adapters raised it.
* A free variable is refused by the writer, by name, in an unsorted problem and in a
  sorted one alike. The fof writer used to write it (a sorted problem is written as fof when
  the typed writer refuses it), and the prover then answered with its own parse error:
  Vampire ``unquantified variable``, E ``Formula has free variables``. That came back as
  ``error`` / ``infra``, which reads as a failure of the prover.
* The NXF writer refuses a sort whose name starts with ``$``. ``$i`` is the type of the
  individuals that it gives every unsorted quantifier and constant, so a user sort ``$i`` would
  be one type with them; the other ``$`` words are TPTP's own (``$o``, ``$int``, ``$tType``,
  ...).
"""

import re

import pytest

from unicode_logic_kit.atp import (
    generate_tff_arith_problem, generate_tff_problem, generate_tff_problem_with_mapping,
    generate_tptp_problem, generate_tptp_problem_with_mapping,
)
from unicode_logic_kit.atp._tff_problem import formula_to_tff_arith
from unicode_logic_kit.atp._tptp_problem import generate_tptp_problem_for_prover
from unicode_logic_kit.atp.eprover_backend import check_entailment_eprover_detailed
from unicode_logic_kit.atp.tptp_ncl import to_tptp_ncl
from unicode_logic_kit.atp.tptp_tff import Tf0Refusal, formula_to_tff
from unicode_logic_kit.atp.vampire_entailment import (
    check_entailment_vampire_detailed, check_logical_entailment_vampire,
)
from unicode_logic_kit.fol.nodes import (
    And, Atom, Box, Constant, Function, Implies, Number, Quantifier, SortedConstant,
    SortedQuantifier, Variable,
)

_X, _Y = Variable("x"), Variable("y")


def _p(term):
    return Atom("P", [term])


_A = Constant("a")
_GOAL = _p(_A)


# ---------------------------------------------------------------------------
# A refusal names the entry point that was called
# ---------------------------------------------------------------------------

#: ``Foo(a)`` and ``foo(a)``: two predicate names that one TPTP word would stand for
_NAME_CLASH = [Atom("Foo", [_A]), Atom("foo", [_A])]
#: ``∀x ∃X R(x, X)``: two variable names that one TPTP variable would stand for
_VARIABLE_CLASH = [Quantifier("∀", _X, Quantifier("∃", Variable("X"),
                                                    Atom("R", [_X, Variable("X")])))]

_WRITERS = {
    "generate_tptp_problem": generate_tptp_problem,
    "generate_tptp_problem_with_mapping": generate_tptp_problem_with_mapping,
    "generate_tff_problem": generate_tff_problem,
    "generate_tff_problem_with_mapping": generate_tff_problem_with_mapping,
    "generate_tff_arith_problem": generate_tff_arith_problem,
}


@pytest.mark.parametrize("premises", [_NAME_CLASH, _VARIABLE_CLASH], ids=["names", "variables"])
@pytest.mark.parametrize("name", sorted(_WRITERS))
def test_a_whole_problem_refusal_opens_with_the_writer_that_was_called(name, premises):
    with pytest.raises(NotImplementedError) as caught:
        _WRITERS[name](list(premises), Atom("Q", [_A]))
    assert str(caught.value).startswith(name + ":"), str(caught.value)[:120]


@pytest.mark.parametrize("premises", [_NAME_CLASH, _VARIABLE_CLASH], ids=["names", "variables"])
def test_a_single_formula_refusal_opens_with_the_renderer_that_was_called(premises):
    formula = And(premises[0], premises[-1]) if len(premises) > 1 else premises[0]
    for name, render in (("formula_to_tff", formula_to_tff),
                         ("formula_to_tff_arith", formula_to_tff_arith)):
        with pytest.raises(NotImplementedError) as caught:
            render(formula)
        assert str(caught.value).startswith(name + ":"), str(caught.value)[:120]


@pytest.mark.parametrize("premises", [_NAME_CLASH, _VARIABLE_CLASH], ids=["names", "variables"])
def test_the_prover_adapters_name_the_writer_they_call_not_another_one(premises):
    """The adapters write the problem before they look for a binary, so the refusal comes
    from the fof writer they call, and says so (it used to name ``generate_tptp_problem``,
    which none of them called)."""
    conclusion = Atom("Q", [_A])
    for refuse in (
            lambda: check_logical_entailment_vampire(list(premises), conclusion, "no-such-vampire"),
            lambda: check_entailment_vampire_detailed(list(premises), conclusion, "no-such-vampire"),
            lambda: check_entailment_eprover_detailed(list(premises), conclusion,
                                                      command="no-such-eprover"),
            lambda: generate_tptp_problem_for_prover(list(premises), conclusion, tff=False)):
        with pytest.raises(NotImplementedError) as caught:
            refuse()
        assert str(caught.value).startswith("generate_tptp_problem_with_mapping:"), \
            str(caught.value)[:120]


#: one formula for each of the other refusals of the typed writers
_TYPED_REFUSALS = {
    "a modal operator": Box(_p(_A)),
    "one predicate at two arities": And(_p(_A), Atom("P", [_A, _A])),
    "a name used as constant and as function": And(
        _p(Constant("f")), Atom("Q", [Function("f", [_A])])),
    # A numeral is written as a constant of its own (it used to be refused here); what is
    # still refused is a constant spelled like one, and a numeral that the inference would
    # put into a sort.
    "a numeral spelled like a constant": And(_p(Number(1)), Atom("Q", [Constant("1")])),
    "a numeral typed into a sort": And(
        SortedQuantifier("∀", _X, "Srt", Atom("Q", [_X])), Atom("Q", [Number(1)])),
    "a sort and a predicate of one name": And(
        SortedQuantifier("∀", _X, "Human", Atom("Q", [_X])), Atom("Human", [_A, _A])),
    "a constant of two sorts": And(_p(SortedConstant("c", "A")), Atom("Q", [SortedConstant("c", "B")])),
}


@pytest.mark.parametrize("label", sorted(_TYPED_REFUSALS))
@pytest.mark.parametrize("name", ["generate_tff_problem", "generate_tff_problem_with_mapping"])
def test_every_refusal_of_the_typed_writer_opens_with_the_writer_that_was_called(name, label):
    writer = {"generate_tff_problem": generate_tff_problem,
              "generate_tff_problem_with_mapping": generate_tff_problem_with_mapping}[name]
    with pytest.raises(NotImplementedError) as caught:
        writer([_TYPED_REFUSALS[label]], Atom("R", [_A]))
    assert str(caught.value).startswith(name + ":"), str(caught.value)[:120]


@pytest.mark.parametrize("label", sorted(_TYPED_REFUSALS))
def test_every_refusal_of_the_single_formula_renderer_opens_with_its_own_name(label):
    with pytest.raises(NotImplementedError) as caught:
        formula_to_tff(_TYPED_REFUSALS[label])
    assert str(caught.value).startswith("formula_to_tff:"), str(caught.value)[:120]


# ---------------------------------------------------------------------------
# A free variable: the writer refuses, in an unsorted and in a sorted problem
# ---------------------------------------------------------------------------

#: P(x) with x bound by nothing
_FREE_UNSORTED = _p(_X)
#: (∀y:Human Q(y)) → P(x): the sort makes it a sorted problem; x is free all the same
_FREE_SORTED = Implies(SortedQuantifier("∀", _Y, "Human", Atom("Q", [_Y])), _p(_X))

_FOF_WRITERS = {
    "generate_tptp_problem": generate_tptp_problem,
    "generate_tptp_problem_with_mapping": generate_tptp_problem_with_mapping,
}


@pytest.mark.parametrize("name", sorted(_FOF_WRITERS))
@pytest.mark.parametrize("premise", [_FREE_UNSORTED, _FREE_SORTED], ids=["unsorted", "sorted"])
def test_the_fof_writer_refuses_a_free_variable_in_a_premise_by_name(name, premise):
    with pytest.raises(NotImplementedError) as caught:
        _FOF_WRITERS[name]([premise], _GOAL)
    message = str(caught.value)
    assert message.startswith(name + ":"), message[:100]
    assert "free variable 'x' in premise 1" in message


@pytest.mark.parametrize("premise", [_FREE_UNSORTED, _FREE_SORTED], ids=["unsorted", "sorted"])
def test_the_fof_writer_names_the_premise_that_has_the_free_variable(premise):
    with pytest.raises(NotImplementedError, match="free variable 'x' in premise 2"):
        generate_tptp_problem_with_mapping([_p(_A), premise], _GOAL)


def test_the_fof_writer_refuses_a_free_variable_in_the_conclusion_too():
    with pytest.raises(NotImplementedError, match="free variable 'x' in the conclusion"):
        generate_tptp_problem_with_mapping([_p(_A)], _p(_X))
    with pytest.raises(NotImplementedError, match="free variable 'x' in the conclusion"):
        generate_tptp_problem_with_mapping(
            [_p(_A)], Implies(SortedQuantifier("∀", _Y, "Human", Atom("Q", [_Y])), _p(_X)))


def test_every_free_variable_of_a_formula_is_named():
    two_free = Atom("R", [_X, _Y])
    with pytest.raises(NotImplementedError, match=r"free variables 'x', 'y' in premise 1"):
        generate_tptp_problem_with_mapping([two_free], _GOAL)


def test_a_variable_bound_elsewhere_is_still_free_where_nothing_binds_it():
    """``(∀x P(x)) ∧ Q(x)``: the quantifier ends before the second ``x``."""
    formula = And(Quantifier("∀", _X, _p(_X)), Atom("Q", [_X]))
    with pytest.raises(NotImplementedError, match="free variable 'x' in premise 1"):
        generate_tptp_problem_with_mapping([formula], _GOAL)


def test_a_closed_problem_is_still_written():
    """Nothing that is closed is refused: nested and repeated binders, a sorted binder, an
    equality, a function term."""
    premises = [
        Quantifier("∀", _X, Quantifier("∃", _Y, Atom("R", [_X, _Y]))),
        Quantifier("∀", _X, Quantifier("∀", _X, _p(_X))),
        SortedQuantifier("∃", _X, "Human", Atom("=", [_X, _A])),
        Quantifier("∀", _Y, Atom("S", [Function("f", [_Y])])),
    ]
    text, _ = generate_tptp_problem_with_mapping(premises, _GOAL)
    assert "fof(premise_4," in text
    assert "fof(goal, conjecture," in text


@pytest.mark.parametrize("premise", [_FREE_UNSORTED, _FREE_SORTED], ids=["unsorted", "sorted"])
def test_the_typed_writers_refuse_a_free_variable_as_well(premise):
    with pytest.raises(Tf0Refusal, match="free variable 'x'"):
        generate_tff_problem_with_mapping([premise], _GOAL)
    with pytest.raises(ValueError, match=r"^generate_tff_arith_problem: free variable\(s\) x"):
        generate_tff_arith_problem([_FREE_UNSORTED], _GOAL)


@pytest.mark.parametrize("premise", [_FREE_UNSORTED, _FREE_SORTED], ids=["unsorted", "sorted"])
def test_e_answers_a_free_variable_as_unsupported_with_the_writers_message(monkeypatch, premise):
    """The adapter reports what the writer said (unknown / unsupported), not the prover's parse
    error as an infrastructure failure; the prover is not run."""
    from unicode_logic_kit.atp import eprover_backend as _eb
    from unicode_logic_kit.atp.protocol import get_backend

    def never_run(*args, **kwargs):
        raise AssertionError("the prover must not be run on a problem the writer refuses")

    monkeypatch.setattr(_eb, "_discover", lambda binary, env_var: ("eprover", False))
    monkeypatch.setattr(_eb, "_binary_version", lambda *a, **k: None)
    monkeypatch.setattr(_eb, "_run_tptp_prover", never_run)
    verdict = get_backend("eprover").decide(_GOAL, [premise], timeout=5000)
    assert (verdict.status, verdict.reason) == ("unknown", "unsupported")
    assert "free variable 'x' in premise 1" in verdict.detail


@pytest.mark.parametrize("premise", [_FREE_UNSORTED, _FREE_SORTED], ids=["unsorted", "sorted"])
def test_vampire_answers_a_free_variable_as_unsupported_with_the_writers_message(
        monkeypatch, premise):
    from unicode_logic_kit.atp import protocol as _protocol
    from unicode_logic_kit.atp import vampire_entailment as _ve
    from unicode_logic_kit.atp.protocol import get_backend

    def never_run(*args, **kwargs):
        raise AssertionError("the prover must not be run on a problem the writer refuses")

    monkeypatch.setattr(_ve, "_spawn_vampire", never_run)
    monkeypatch.setattr(_protocol, "_binary_version", lambda *a, **k: None)
    verdict = get_backend("vampire").decide(_GOAL, [premise], timeout=5000,
                                            vampire_path="vampire", use_wsl=False)
    assert (verdict.status, verdict.reason) == ("unknown", "unsupported")
    assert "free variable 'x' in premise 1" in verdict.detail


# ---------------------------------------------------------------------------
# NXF: a sort whose name starts with $
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("sort", ["$i", "$o", "$tType", "$int", "$rat", "$real", "$true", "$foo"])
def test_the_nxf_writer_refuses_a_sort_named_like_a_tptp_word(sort):
    """A bound variable, a sorted constant and a sorted binder under a modality are all sorts of
    the user's, and none of them may be spelled ``$...``."""
    shown = re.escape(f"'{sort}'")
    bound = SortedQuantifier("∀", _X, sort, _p(_X))
    for formula in (bound, Box(bound), _p(SortedConstant("c", sort))):
        with pytest.raises(NotImplementedError, match=shown) as caught:
            to_tptp_ncl(formula)
        assert "to_tptp_ncl" in str(caught.value)
        assert "'$'" in str(caught.value)


def test_the_nxf_writer_still_writes_a_sort_with_an_ordinary_name():
    text = to_tptp_ncl(Box(SortedQuantifier("∀", _X, "Person", _p(_X))))
    assert "person: $tType" in text
    assert "! [X: person]" in text


def test_the_nxf_writer_still_writes_an_unsorted_quantifier_at_the_type_of_individuals():
    text = to_tptp_ncl(Box(Quantifier("∀", _X, _p(_X))))
    assert "! [X: $i]" in text


@pytest.mark.parametrize("sort", ["$i", "$o", "$tType", "$int", "$real", "$foo"])
def test_the_fof_writer_refuses_a_sort_named_like_a_tptp_word(sort):
    with pytest.raises(NotImplementedError, match=re.escape(f"'{sort}'")):
        generate_tptp_problem_with_mapping([SortedQuantifier("∀", _X, sort, _p(_X))],
                                           SortedQuantifier("∃", _X, sort, _p(_X)))


def test_the_tf0_writer_refuses_the_individuals_type_and_renames_the_other_dollar_words():
    """``$i`` would be one type with every unsorted term, so it is refused. Another ``$`` word is
    written under a name that is not TPTP's (``u0024int``), so the type ``$int`` is never
    declared, or used, by accident."""
    with pytest.raises(NotImplementedError, match=re.escape("'$i'")):
        generate_tff_problem_with_mapping([SortedQuantifier("∀", _X, "$i", _p(_X))],
                                          SortedQuantifier("∃", _X, "$i", _p(_X)))
    text, _ = generate_tff_problem_with_mapping([SortedQuantifier("∀", _X, "$int", _p(_X))],
                                                SortedQuantifier("∃", _X, "$int", _p(_X)))
    assert "u0024int: $tType" in text
    assert "X: $int" not in text
