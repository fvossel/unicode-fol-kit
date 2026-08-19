"""The ACE DRS reader: 1:1 fidelity against the recorded corpus.

Everything here is OFFLINE — the reader is a pure function on strings, and
the strings are the fixture recorded from APE at the pinned commit. The
heart of the file is the round-trip test: parse each recorded DRS and
render it back BYTE-IDENTICAL. A reader that survives that on all 49
non-trivial corpus DRSs demonstrably lost nothing on any shape APE actually
produces — which is the entire claim the reader makes (interpretation is
the mapping layer's claim, tested separately).
"""

import json
from pathlib import Path

import pytest

from unicode_fol_kit.ace import (
    AceAtom, AceCommand, AceCondList, AceDrs, AceDrsUnreadError, AceExpr,
    AceImpl, AceInt, AceModal, AceNamed, AceNeg, AceOr, AceQuestion,
    AceString, AceVar, parse_ape_drs,
)

FIXTURES = Path(__file__).parent / "fixtures"
ROWS = json.loads((FIXTURES / "ape_5f4d535_corpus_v1.json").read_text(
    encoding="utf-8"))
NONTRIVIAL = [r for r in ROWS if r["drs"] != "drs([],[])"]


# ---------------------------------------------------------------------------
# The round-trip: every recorded DRS, byte-identical back
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("row", NONTRIVIAL, ids=[r["tag"] for r in NONTRIVIAL])
def test_every_corpus_drs_round_trips_byte_identical(row):
    assert parse_ape_drs(row["drs"]).render() == row["drs"]


def test_the_corpus_actually_exercises_every_condition_shape():
    """Guard on the guard: the round-trip above only proves fidelity on
    shapes that OCCUR — so pin that they all do. If a corpus edit drops the
    last instance of a shape, this fails rather than the reader's coverage
    silently shrinking."""
    seen = set()
    for row in NONTRIVIAL:
        for cond in parse_ape_drs(row["drs"]).walk_conditions():
            seen.add(type(cond).__name__)
    assert seen == {"AceAtom", "AceNeg", "AceNaf", "AceImpl", "AceOr",
                    "AceModal", "AceQuestion", "AceCommand", "AceCondList"}


# ---------------------------------------------------------------------------
# Hand-checked structures
# ---------------------------------------------------------------------------

def test_the_donkey_sentence_by_hand():
    drs = parse_ape_drs(
        "drs([],[=>(drs([A,B,C],[object(A,farmer,countable,na,eq,1)-1/2,"
        "object(B,donkey,countable,na,eq,1)-1/6,predicate(C,own,A,B)-1/4]),"
        "drs([D],[predicate(D,beat,A,B)-1/7]))])")
    assert drs.referents == ()
    (impl,) = drs.conditions
    assert isinstance(impl, AceImpl)
    assert impl.antecedent.referents == (AceVar("A"), AceVar("B"), AceVar("C"))
    own = impl.antecedent.conditions[2]
    assert own == AceAtom("predicate", (AceVar("C"), "own", AceVar("A"),
                                        AceVar("B")), 1, 4)
    (beat,) = impl.consequent.conditions
    # The donkey binding: the consequent's atom reuses A and B from the
    # ANTECEDENT box — exactly what the reader must preserve verbatim.
    assert beat.args[2:] == (AceVar("A"), AceVar("B"))


def test_an_implicit_condition_has_no_token_index():
    drs = parse_ape_drs("drs([A],[has_part(A,named('John'))-1/''])")
    (cond,) = drs.conditions
    assert cond.sentence == 1 and cond.token is None
    assert cond.args == (AceVar("A"), AceNamed("John"))


def test_wrapped_value_terms_specialize():
    drs = parse_ape_drs(
        "drs([A],[predicate(A,be,named('John'),int(30))-1/5,"
        "formula(expr(+,int(1),int(2)),=,int(3))-1/4,"
        "predicate(A,be,named('O''Brien'),string('Johnny'))-1/5])")
    be30, formula, bestr = drs.conditions
    assert be30.args[3] == AceInt(30)
    assert isinstance(formula.args[0], AceExpr)
    assert formula.args[0].op == "+"
    assert formula.args[1] == "="
    # A doubled quote inside a quoted atom is ONE literal quote.
    assert bestr.args[2] == AceNamed("O'Brien")
    assert bestr.args[3] == AceString("Johnny")


def test_modal_question_command_boxes_classify():
    drs = parse_ape_drs(
        "drs([],[must(drs([A],[predicate(A,wait,named('John'))-1/3])),"
        "question(drs([B],[predicate(B,wait,named('John'))-1/3])),"
        "command(drs([C],[predicate(C,wait,named('John'))-1/3]))])")
    must, question, command = drs.conditions
    assert isinstance(must, AceModal) and must.modality == "must"
    assert isinstance(question, AceQuestion)
    assert isinstance(command, AceCommand)


def test_a_v_atom_with_referent_args_stays_an_atom():
    """Classification is semantic, not lexical: ``v`` is only a disjunction
    when BOTH arguments are boxes — a hypothetical ``v(A,B)`` over referents
    must stay an ordinary atomic condition."""
    drs = parse_ape_drs("drs([A,B],[v(A,B)-1/2])")
    (cond,) = drs.conditions
    assert isinstance(cond, AceAtom) and cond.functor == "v"
    both = parse_ape_drs("drs([],[v(drs([A],[p(A)-1/1]),drs([B],[p(B)-1/2]))])")
    assert isinstance(both.conditions[0], AceOr)


def test_the_exactly_list_condition_nests():
    drs = parse_ape_drs(
        "drs([A,B],[[predicate(B,bark,A)-1/4,"
        "object(A,dog,countable,na,exactly,2)-1/3]])")
    (group,) = drs.conditions
    assert isinstance(group, AceCondList)
    assert [c.functor for c in group.conditions] == ["predicate", "object"]


def test_walks_visit_nested_boxes():
    drs = parse_ape_drs(
        "drs([],[=>(drs([A],[object(A,man,countable,na,eq,1)-1/2]),"
        "drs([],[-(drs([B],[predicate(B,wait,A)-1/3]))]))])")
    assert len(list(drs.walk_boxes())) == 4  # top, antecedent, consequent, neg
    functors = [c.functor for c in drs.walk_conditions()
                if isinstance(c, AceAtom)]
    assert functors == ["object", "predicate"]


# ---------------------------------------------------------------------------
# Refusals
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("bad", [
    "not a term at all",
    "drs([A],[predicate(A,wait])",          # unbalanced
    "drs([A],[predicate(A,wait,B)-x/y])",   # non-numeric index
    "drs([A],[predicate(A,wait,B)-1/'a'])", # a non-empty quoted token index
    "drs([a],[p(a)-1/1])",                  # lowercase referent in the domain
    "",
])
def test_malformed_input_raises_with_context(bad):
    with pytest.raises(AceDrsUnreadError):
        parse_ape_drs(bad)


def test_an_unseen_functor_still_parses():
    """Future-APE tolerance: novelty must land in the REPORT (mapping layer),
    not crash the reader."""
    drs = parse_ape_drs("drs([A],[newthing(A,foo,bar)-2/7])")
    (cond,) = drs.conditions
    assert cond == AceAtom("newthing", (AceVar("A"), "foo", "bar"), 2, 7)
