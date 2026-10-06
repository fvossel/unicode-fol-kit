r"""The caller's names for the premises of a TPTP problem, and reading them back from a proof.

``premise_names=`` names the ``axiom`` lines of a written problem (``fof``, TF0 and TFA) instead of
``premise_<i>``. A name is written as a TPTP ``<name>``: a lower word or an unsigned integer as it
is, anything else single-quoted with ``\`` and ``'`` escaped. The writer returns a name map that
records the names in order, and what a prover prints about the axioms of its proof is read back
through that record.

Every expected text and index below is derived by hand from those rules. The prover output used
by the offline tests is the shape Vampire 5.0.1 and E 3.5.1 print (recorded; two details matter
and are measured: Vampire echoes an axiom's name only under ``--output_axiom_names on``, in the
second argument of the ``file(path, name)`` source of its numbered ``f<N>`` statements; E names the
statement after the axiom, and reads a backslash plus the character after it as one backslash, so
it prints the apostrophe of ``it's`` as a backslash). The live tests run the real provers where
they are reachable and are skipped, never weakened, where they are not.
"""

import shutil
import subprocess
from typing import List, Optional, Tuple

import pytest

from unicode_fol_kit.atp._tptp_problem import (
    TptpNameMap, generate_tptp_problem, generate_tptp_problem_for_prover,
    generate_tptp_problem_with_mapping,
)
from unicode_fol_kit.atp._tff_problem import generate_tff_arith_problem
from unicode_fol_kit.atp.eprover_backend import (
    EProverBackend, check_entailment_eprover_detailed, eprover_available,
    eprover_relevant_premises,
)
from unicode_fol_kit.atp.tptp_tff import Tf0Refusal, generate_tff_problem, generate_tff_problem_with_mapping
from unicode_fol_kit.atp.tstp import relevant_premises_from_tstp
from unicode_fol_kit.atp.vampire_entailment import check_entailment_vampire_detailed
from unicode_fol_kit.fol.nodes import (
    Atom, Constant, Implies, Quantifier, SortedConstant, SortedQuantifier, Variable,
)

X = Variable("x")


def p(name, *args):
    return Atom(name, list(args))


A, B, C = Constant("a"), Constant("b"), Constant("c")

#: ∀x (P(x) → Q(x)), R(b), P(a), S(c)  ⊢  Q(a): the first and the third premise are the proof.
RULE = Quantifier("∀", X, Implies(p("P", X), p("Q", X)))
FOF_PREMISES = [RULE, p("R", B), p("P", A), p("S", C)]
FOF_GOAL = p("Q", A)
FOF_USED = (0, 2)

#: ∀x:Human Mortal(x), Q(socrates:Human), R(socrates:Human)  ⊢  Mortal(socrates:Human): only the
#: first premise is the proof (typed text), and in the fof text also socrates ∈ Human.
SOCRATES = SortedConstant("socrates", "Human")
SORTED_PREMISES = [p("Q", SOCRATES), SortedQuantifier("∀", X, "Human", p("Mortal", X)), p("R", SOCRATES)]
SORTED_GOAL = p("Mortal", SOCRATES)

NAMES = ["it's Sókrates 1", "Dröge a b", "ß ' \\ q", "unused one"]


def lines_of(text: str) -> List[str]:
    return [ln for ln in text.splitlines() if ln.strip()]


# =============================================================================
# How a name is written
# =============================================================================

@pytest.mark.parametrize("name, token", [
    ("my_axiom", "my_axiom"),                    # a lower word: as it is
    ("a", "a"),
    ("ax1_b2", "ax1_b2"),
    ("42", "42"),                                # an unsigned integer: as it is
    ("0", "0"),
    ("007", "'007'"),                            # a leading zero is no integer
    ("-3", "'-3'"),                              # a sign neither
    ("Upper", "'Upper'"),                        # not a LOWER word
    ("my premise", "'my premise'"),
    ("it's", "'it\\'s'"),                        # ' is escaped
    ("back\\slash", "'back\\\\slash'"),          # \ is escaped
    ("it's \\", "'it\\'s \\\\'"),                # both, the backslash last
    ("Sókrates", "'Sókrates'"),                  # a non-ASCII letter is written as it is
    ("ß", "'ß'"),
    ("a.b", "'a.b'"),
    ("$dollar", "'$dollar'"),
    ("%percent", "'%percent'"),
])
def test_a_premise_name_is_written_as_a_tptp_name(name, token):
    from unicode_fol_kit.atp._writer_support import decode_tptp_name, tptp_name_token
    assert tptp_name_token(name) == token
    assert decode_tptp_name(token) == name           # and reads back to what it was


@pytest.mark.parametrize("writer", [generate_tptp_problem, generate_tff_problem])
def test_the_writers_write_the_names_the_caller_gave(writer):
    premises = [p("P", A), p("Q", A), p("R", A)]
    text = writer(premises, p("S", A), premise_names=["my_axiom", "it's Sókrates", "42"])
    lines = lines_of(text)
    # a TF0 text has its declarations first; the axiom lines come after them, in premise order
    axioms = [ln for ln in lines if ", axiom," in ln]
    assert [ln.split("(", 1)[1].split(", axiom,")[0] for ln in axioms] == ["my_axiom", "'it\\'s Sókrates'", "42"]
    assert lines[-1].startswith(("fof(goal, conjecture,", "tff(goal, conjecture,"))


def test_the_arithmetic_writer_writes_the_names_the_caller_gave():
    text, name_map = generate_tff_arith_problem(
        [p("P", A), p("Q", A)], p("R", A), "int", premise_names=["x y", "z"])
    assert "tff('x y', axiom," in text and "tff(z, axiom," in text
    assert name_map.premises == ("x y", "z")


def test_without_names_every_writer_keeps_premise_i():
    premises = [p("P", A), p("Q", A)]
    assert "fof(premise_1, axiom," in generate_tptp_problem(premises, p("R", A))
    assert "fof(premise_2, axiom," in generate_tptp_problem(premises, p("R", A))
    assert "tff(premise_2, axiom," in generate_tff_problem(premises, p("R", A))
    assert generate_tptp_problem(premises, p("R", A)) == generate_tptp_problem(
        premises, p("R", A), premise_names=["premise_1", "premise_2"])


def test_a_problem_without_a_conclusion_is_named_too():
    text = generate_tptp_problem([p("P", A)], None, premise_names=["only one"])
    assert lines_of(text) == ["fof('only one', axiom, p(a))."]


# =============================================================================
# What the returned name map records
# =============================================================================

def test_the_name_map_records_the_premise_names_in_order_also_the_default_ones():
    _text, given = generate_tptp_problem_with_mapping(FOF_PREMISES, FOF_GOAL, premise_names=NAMES)
    assert given.premises == tuple(NAMES)
    _text, default = generate_tptp_problem_with_mapping(FOF_PREMISES, FOF_GOAL)
    assert default.premises == ("premise_1", "premise_2", "premise_3", "premise_4")
    _text, typed = generate_tff_problem_with_mapping(SORTED_PREMISES, SORTED_GOAL, premise_names=["a", "b", "c"])
    assert typed.premises == ("a", "b", "c")
    _text, typed_default = generate_tff_problem_with_mapping(SORTED_PREMISES, SORTED_GOAL)
    assert typed_default.premises == ("premise_1", "premise_2", "premise_3")
    _text, arith = generate_tff_arith_problem([p("P", A)], p("P", A), "int")
    assert arith.premises == ("premise_1",)


def test_the_name_map_records_the_background_axioms_the_fof_writer_adds_with_their_meaning():
    # Human is not empty (one non-emptiness line) and socrates is in Human (one membership line).
    _text, name_map = generate_tptp_problem_with_mapping(SORTED_PREMISES, SORTED_GOAL)
    assert name_map.background == (
        ("nonempty_sort_1", "the sort Human is not empty"),
        ("sort_member_1", "socrates is in the sort Human"),
    )
    _text, plain = generate_tptp_problem_with_mapping(FOF_PREMISES, FOF_GOAL)
    assert plain.background == ()


def test_the_premise_record_is_no_rename_so_two_maps_that_rename_alike_are_equal():
    _t1, first = generate_tptp_problem_with_mapping([p("P", A)], p("P", A), premise_names=["one"])
    _t2, second = generate_tptp_problem_with_mapping([p("P", A)], p("P", A), premise_names=["two"])
    assert first == second and first.premises != second.premises
    assert first == TptpNameMap(predicate={"P": "P"}, term={"a": "a"})


def test_the_dialect_helper_passes_the_names_to_the_dialect_it_writes():
    typed = generate_tptp_problem_for_prover(SORTED_PREMISES, SORTED_GOAL, premise_names=["x y", "z", "w"])
    assert typed.dialect == "tff" and typed.name_map.premises == ("x y", "z", "w")
    assert "tff('x y', axiom," in typed.text
    fof = generate_tptp_problem_for_prover(FOF_PREMISES, FOF_GOAL, premise_names=NAMES)
    assert fof.dialect == "fof" and fof.name_map.premises == tuple(NAMES)
    forced = generate_tptp_problem_for_prover(SORTED_PREMISES, SORTED_GOAL, tff=False, premise_names=["a", "b", "c"])
    assert forced.dialect == "fof" and "fof(a, axiom," in forced.text


# =============================================================================
# What is refused
# =============================================================================

def refusal(call, kind=ValueError) -> str:
    with pytest.raises(kind) as caught:
        call()
    return str(caught.value)


@pytest.mark.parametrize("writer", [generate_tptp_problem_with_mapping, generate_tff_problem_with_mapping])
def test_one_name_per_premise_else_a_value_error_that_says_how_many(writer):
    premises = [p("P", A), p("Q", A)]
    message = refusal(lambda: writer(premises, p("R", A), premise_names=["only"]))
    assert "one name per premise" in message and "2 premises" in message and "1 name" in message
    message = refusal(lambda: writer(premises[:1], p("R", A), premise_names=["x", "y", "z"]))
    assert "1 premise " in message and "3 names" in message


@pytest.mark.parametrize("writer", [generate_tptp_problem_with_mapping, generate_tff_problem_with_mapping])
def test_a_name_no_tptp_name_spells_is_refused(writer):
    premises = [p("P", A)]
    assert "is empty" in refusal(lambda: writer(premises, None, premise_names=[""]))
    # a line break would end the statement; a tab is below the space, which a quoted word cannot hold
    for bad in ("a\nb", "a\tb", "a\x00b", "a\x7fb"):
        message = refusal(lambda bad=bad: writer(premises, None, premise_names=[bad]))
        assert "control character" in message and "premise_names[0]" in message
    assert "UTF-8" in refusal(lambda: writer(premises, None, premise_names=["a\ud800b"]))


@pytest.mark.parametrize("writer", [generate_tptp_problem_with_mapping, generate_tff_problem_with_mapping])
def test_two_premises_with_one_name_are_refused_naming_both(writer):
    premises = [p("P", A), p("Q", A), p("R", A)]
    message = refusal(lambda: writer(premises, None, premise_names=["same", "other", "same"]))
    assert "premise_names[0] and premise_names[2]" in message and "'same'" in message


def test_a_premise_named_like_a_line_the_fof_writer_writes_itself_is_refused_naming_both():
    # With a conclusion the writer writes ``goal``; with a sorted constant it writes
    # nonempty_sort_1 (Human) and sort_member_1 (socrates in Human).
    sorted_premises = SORTED_PREMISES[:2]
    for clashing, what in (("goal", "the conjecture"), ("nonempty_sort_1", "non-emptiness axiom of the sort 'Human'"),
                           ("sort_member_1", "socrates is in the sort Human")):
        message = refusal(lambda c=clashing: generate_tptp_problem_with_mapping(
            sorted_premises, SORTED_GOAL, premise_names=["fine", c]))
        assert "premise_names[1]" in message and repr(clashing) in message and what in message, message


def test_a_name_the_writer_does_not_write_is_not_a_clash():
    # No conclusion, so no ``goal`` line; one sort and one membership line, so nonempty_sort_2 is free.
    text = generate_tptp_problem([p("P", A)], None, premise_names=["goal"])
    assert text == "fof(goal, axiom, p(a)).\n"
    sorted_text = generate_tptp_problem([p("P", SOCRATES)], p("P", SOCRATES), premise_names=["nonempty_sort_2"])
    assert "fof(nonempty_sort_2, axiom," in sorted_text and "fof(nonempty_sort_1, axiom," in sorted_text
    assert generate_tptp_problem([p("P", A)], p("P", A), premise_names=["premise_2"]).startswith("fof(premise_2,")


def test_the_typed_writers_refuse_a_premise_named_like_one_of_their_declarations():
    # TF0 writes sort_decl_1, const_decl_2, pred_decl_3 for this problem; TFA writes const_decl_1, pred_decl_2.
    message = refusal(lambda: generate_tff_problem(
        SORTED_PREMISES[:1], SORTED_GOAL, premise_names=["sort_decl_1"]))
    assert "sort_decl_1" in message and "type declaration" in message
    with pytest.raises(Tf0Refusal):      # a typed-text refusal, so the automatic mode can write fof instead
        generate_tff_problem(SORTED_PREMISES[:1], SORTED_GOAL, premise_names=["goal"])
    message = refusal(lambda: generate_tff_arith_problem(
        [p("P", A)], p("P", A), "int", premise_names=["const_decl_1"]))
    assert "const_decl_1" in message and "type declaration" in message


def test_the_automatic_mode_falls_back_to_fof_when_only_the_typed_text_would_clash():
    # The typed text accepts this problem and writes sort_decl_1 itself, so a premise of that name
    # clashes with it; the fof text writes no such line, so it takes the name.
    premises = [SortedQuantifier("∀", X, "Human", p("Mortal", X))]
    built = generate_tptp_problem_for_prover(premises, SORTED_GOAL, premise_names=["sort_decl_1"])
    assert built.dialect == "fof" and built.text.startswith("fof(sort_decl_1, axiom,")
    assert "sort_decl_1" in built.tff_refusal
    with pytest.raises(Tf0Refusal):
        generate_tptp_problem_for_prover(premises, SORTED_GOAL, tff=True, premise_names=["sort_decl_1"])


def test_a_single_string_or_a_non_string_is_a_type_error_not_one_name_per_character():
    assert "single str" in refusal(lambda: generate_tptp_problem([p("P", A)], None, premise_names="abc"), TypeError)
    assert "premise_names[1] must be a string" in refusal(
        lambda: generate_tptp_problem([p("P", A), p("Q", A)], None, premise_names=["a", 7]), TypeError)


# =============================================================================
# Reading a proof back: offline, on the text the provers print
# =============================================================================

#: E 3.5.1 proof of ∀x (P(x) → Q(x)), P(a) ⊢ Q(a), the premises named "it's Sókrates 1" and
#: "ß ' \ q". E prints the apostrophes as backslashes ("it\s Sókrates 1": a backslash is printed
#: doubled), and the statement name is the axiom's name.
E_PROOF = r"""
# SZS status Theorem
# SZS output start CNFRefutation
fof(goal, conjecture, q(a), file('/tmp/x.p', goal)).
fof('it\\s Sókrates 1', axiom, ![X1]:((p(X1)=>q(X1))), file('/tmp/x.p', 'it\\s Sókrates 1')).
fof('ß \\ \\ q', axiom, p(a), file('/tmp/x.p', 'ß \\ \\ q')).
fof(c_0_3, negated_conjecture, ~(q(a)), inference(assume_negation,[status(cth)],[goal])).
fof(c_0_6, plain, ![X2]:((~p(X2)|q(X2))), inference(fof_nnf,[status(thm)],[inference(variable_rename,[status(thm)],['it\\s Sókrates 1'])])).
cnf(c_0_7, negated_conjecture, (~q(a)), inference(split_conjunct,[status(thm)],[c_0_3])).
cnf(c_0_8, plain, (q(X1)|~p(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
cnf(c_0_9, plain, (p(a)), inference(split_conjunct,[status(thm)],['ß \\ \\ q'])).
cnf(c_0_10, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_8]), c_0_9])]), ['proof']).
# SZS output end CNFRefutation
"""

#: Vampire 5.0.1 under --output_axiom_names on: the leaves are f1, f2, ... and the axiom's name is the
#: second argument of the file(...) source, quoted and escaped as written (an apostrophe as \').
VAMPIRE_PROOF = r"""
% SZS status Theorem for x
% SZS output start Proof for x
fof(f1,axiom,(
  ! [X0] : (p(X0) => q(X0))),
  file('x.p','it\'s Sókrates 1')).
fof(f2,axiom,(
  p(a)),
  file('x.p','ß \' \\ q')).
fof(f4,conjecture,(
  q(a)),
  file('x.p',goal)).
fof(f5,negated_conjecture,(
  ~q(a)),
  inference(negated_conjecture,[status(cth)],[f4])).
fof(f9,plain,(
  ( ! [X0] : (~p(X0) | q(X0)) )),
  inference(cnf_transformation,[],[f1])).
fof(f10,plain,(
  p(a)),
  inference(cnf_transformation,[],[f2])).
fof(f11,plain,(
  ~q(a)),
  inference(cnf_transformation,[],[f5])).
fof(f12,plain,(
  q(a)),
  inference(resolution,[],[f9,f10])).
fof(f13,plain,(
  $false),
  inference(forward_subsumption_resolution,[],[f12,f11])).
% SZS output end Proof for x
"""

#: the same proof, Vampire run WITHOUT --output_axiom_names: it prints the word unknown for every axiom
VAMPIRE_PROOF_WITHOUT_NAMES = VAMPIRE_PROOF.replace("'it\\'s Sókrates 1'", "unknown").replace("'ß \\' \\\\ q'", "unknown")


def name_map_of(names) -> TptpNameMap:
    """The record of a problem with one premise per name (what they say does not matter)."""
    _text, name_map = generate_tptp_problem_with_mapping(
        [p("P", Constant(f"c{i}")) for i in range(len(names))], None, premise_names=list(names))
    return name_map


def test_vampire_names_read_back_through_the_record():
    name_map = name_map_of(NAMES)
    assert relevant_premises_from_tstp(VAMPIRE_PROOF, 4, name_map) == (0, 2)


def test_e_names_read_back_through_the_record_although_e_prints_an_apostrophe_as_a_backslash():
    name_map = name_map_of(NAMES)
    assert relevant_premises_from_tstp(E_PROOF, 4, name_map, eprover=True) == (0, 2)
    # Read as a faithful prover's output, E's text names no premise: "it\s Sókrates 1" is not "it's Sókrates 1".
    assert relevant_premises_from_tstp(E_PROOF, 4, name_map) is None


def test_the_default_names_are_read_without_a_record_too():
    text = ("fof(premise_1,axiom,p(a),file('x.p',premise_1)).\n"
            "fof(premise_3,axiom,q(a),file('x.p',premise_3)).\n"
            "fof(sink,plain,$false,inference(r,[status(thm)],[premise_1,premise_3])).\n")
    assert relevant_premises_from_tstp(text, 3) == (0, 2)
    _t, record = generate_tptp_problem_with_mapping([p("P", A)] * 3, None)
    assert relevant_premises_from_tstp(text, 3, record) == (0, 2)


def test_a_record_of_other_names_does_not_read_premise_i_leaves():
    text = ("fof(premise_1,axiom,p(a),file('x.p',premise_1)).\n"
            "fof(sink,plain,$false,inference(r,[status(thm)],[premise_1])).\n")
    assert relevant_premises_from_tstp(text, 1, name_map_of(["alpha"])) is None
    assert relevant_premises_from_tstp(text, 1, name_map_of(["premise_1"])) == (0,)


def test_vampire_without_axiom_names_says_nothing_so_the_answer_is_none_not_a_guess():
    name_map = name_map_of(NAMES)
    assert relevant_premises_from_tstp(VAMPIRE_PROOF_WITHOUT_NAMES, 4, name_map) is None
    # ... and the default names are no guess either: the leaves are called f1 and f2
    assert relevant_premises_from_tstp(VAMPIRE_PROOF_WITHOUT_NAMES, 4) is None


def test_a_premise_named_unknown_cannot_be_told_from_vampires_placeholder():
    # Vampire without the option prints file('x.p',unknown) for every axiom, so a premise really
    # named unknown could not be told from the placeholder. The writer used to accept the name and the
    # reader to answer None; a premise called f2 next to it made the answer wrong (see
    # test_a_premise_name_a_prover_uses_for_something_else_is_refused), so the writer refuses the name.
    with pytest.raises(ValueError, match="'unknown'.*another name"):
        name_map_of(["unknown", "other"])
    # A record that holds the name anyway (one the writer would not write) is still not read as the
    # placeholder: Vampire's leaf is called f1, which is no name of the record.
    record = name_map_of(["alpha", "other"])
    record.premises = ("unknown", "other")
    text = ("fof(f1,axiom,p(a),file('x.p',unknown)).\n"
            "fof(f2,plain,$false,inference(r,[],[f1])).\n")
    assert relevant_premises_from_tstp(text, 2, record) is None
    # E names the statement itself, so the same name is read from E's text
    e_text = ("fof(unknown,axiom,p(a),file('x.p',unknown)).\n"
              "fof(sink,plain,$false,inference(r,[],[unknown])).\n")
    assert relevant_premises_from_tstp(e_text, 2, record, eprover=True) == (0,)


@pytest.mark.parametrize("name", ["unknown", "f1", "f27", "c_0_5", "i_12_3"])
def test_a_premise_name_a_prover_uses_for_something_else_is_refused(name):
    """Vampire prints ``unknown`` for an axiom whose name it does not know and calls its own
    statements ``f1``, ``f2``, ...; E calls the clauses it derives ``c_0_5`` (and ``i_0_5``). A
    premise with one of these names could be read back as another formula, so the writer refuses
    it, by name and in every dialect."""
    from unicode_fol_kit.atp._tff_problem import generate_tff_arith_problem
    premises = [p("P", Constant("c1")), p("P", Constant("c2"))]
    for write in (generate_tptp_problem_with_mapping, generate_tff_problem_with_mapping,
                  lambda ps, c, premise_names: generate_tff_arith_problem(ps, c, "int",
                                                                          premise_names=premise_names)):
        with pytest.raises(ValueError, match=f"premise_names\\[1\\] = '{name}'"):
            write(premises, None, premise_names=["fine", name])


@pytest.mark.parametrize("name", ["f", "fact1", "f1x", "g1", "c_5", "c_0_5_1", "premise_1", "Unknown", "s1"])
def test_a_premise_name_that_only_looks_like_a_prover_name_is_written(name):
    """Only the names the provers use are refused: ``f`` alone, ``fact1``, ``c_0_5_1`` are not."""
    text, record = generate_tptp_problem_with_mapping([p("P", Constant("c1"))], None, premise_names=[name])
    assert record.premises == (name,)


def test_the_conflict_in_vampires_own_names_no_longer_gives_the_wrong_premise():
    """Premise 0 is called f2, premise 1 unknown, and only premise 1 proves the goal. Vampire printed
    its placeholder for the second and the reader fell back to the statement name f2, which is the
    first premise's name: the used premise came back as (0,). The names are refused now, before
    any prover is started (so no binary is needed here)."""
    rr, pp = p("Rr", Constant("bet")), p("Pp", Constant("alp"))
    with pytest.raises(ValueError, match=r"premise_names\[0\] = 'f2'"):
        check_entailment_vampire_detailed([rr, pp], pp, "vampire", premise_names=["f2", "unknown"])
    with pytest.raises(ValueError, match=r"premise_names\[1\] = 'unknown'"):
        check_entailment_eprover_detailed([rr, pp], pp, command="eprover",
                                          premise_names=["first", "unknown"])
    # the same two premises under names no prover uses: the proof used the second only
    text, record = generate_tptp_problem_with_mapping([rr, pp], pp, premise_names=["first", "second"])
    assert record.premises == ("first", "second")


def test_a_leaf_the_record_does_not_know_makes_the_answer_none():
    name_map = name_map_of(["one", "two"])
    text = ("fof(stray,axiom,p(a),file('x.p',stray)).\n"
            "fof(sink,plain,$false,inference(r,[],[stray])).\n")
    assert relevant_premises_from_tstp(text, 2, name_map) is None
    assert relevant_premises_from_tstp(text, 3, name_map) is None      # the record is of two premises


def test_e_does_not_choose_between_two_names_it_prints_alike():
    # "it's" is printed by E as it\s, and so is the name it\s. Which premise a leaf it\s is, is not said.
    name_map = name_map_of(["it's", "it\\s"])
    text = ("fof('it\\\\s',axiom,p(a),file('x.p','it\\\\s')).\n"
            "fof(sink,plain,$false,inference(r,[],['it\\\\s'])).\n")
    assert relevant_premises_from_tstp(text, 2, name_map, eprover=True) is None
    # a faithful prover prints the two names differently, and each is read as itself
    faithful = ("fof(f1,axiom,p(a),file('x.p','it\\'s')).\n"
                "fof(f2,plain,$false,inference(r,[],[f1])).\n")
    assert relevant_premises_from_tstp(faithful, 2, name_map) == (0,)
    other = faithful.replace("'it\\'s'", "'it\\\\s'")
    assert relevant_premises_from_tstp(other, 2, name_map) == (1,)


@pytest.mark.parametrize("label, names, expected", [
    ("it's", ["it's", "x"], 0),
    ("x", ["it's", "x"], 1),
    ("missing", ["it's", "x"], None),
])
def test_a_label_is_matched_to_the_premise_of_that_name(label, names, expected):
    from unicode_fol_kit.atp._writer_support import match_premise_label
    assert match_premise_label(label, names) == expected


def test_the_label_of_a_leaf_is_the_name_in_its_file_source_else_its_own_name():
    from unicode_fol_kit.atp._writer_support import axiom_leaf_label
    assert axiom_leaf_label("f3", "file('x.p','my premise')") == "my premise"
    assert axiom_leaf_label("f3", "file('x.p',my_premise)") == "my_premise"
    assert axiom_leaf_label("'my premise'", "file('x.p', 'my premise')") == "my premise"
    assert axiom_leaf_label("f3", "file('x.p',unknown)") == "f3"
    assert axiom_leaf_label("premise_2", None) == "premise_2"
    assert axiom_leaf_label("f3", "inference(r,[],[f1])") == "f3"


def test_a_typed_proof_is_read_like_a_fof_one():
    # E and Vampire print the proof of a TF0 / TFA problem as tff / tcf statements.
    text = ("tff(decl_sort1, type, human: $tType).\n"
            "tff('só 1', axiom, ![X1:human]:(mortal(X1)), file('x.p', 'só 1')).\n"
            "tff('other', axiom, q(socrates), file('x.p', 'other')).\n"
            "tcf(c_0_7, plain, ![X1:human]:(mortal(X1)), inference(split_conjunct,[status(thm)],['só 1'])).\n"
            "cnf(c_0_8, negated_conjecture, ($false), inference(cn,[status(thm)],[c_0_7])).\n")
    assert relevant_premises_from_tstp(text, 2, name_map_of(["só 1", "other"]), eprover=True) == (0,)


# =============================================================================
# Background leaves are not premises (the fof reading of a sorted problem)
# =============================================================================

def test_a_proof_that_uses_a_sort_fact_has_the_premises_among_its_leaves_and_names_the_background():
    # The fof text of SORTED_PREMISES has Human non-empty (nonempty_sort_1) and socrates in Human
    # (sort_member_1). A proof that rests on premise 2 and on socrates being a Human uses one premise
    # and one background fact; neither the unused premises nor the unused fact are reported.
    from unicode_fol_kit.atp.tstp import _premise_use_from_tstp
    _text, name_map = generate_tptp_problem_with_mapping(SORTED_PREMISES, SORTED_GOAL, premise_names=["q", "rule", "r"])
    proof = ("fof(rule,axiom,![X]:(human(X)=>mortal(X)),file('x.p',rule)).\n"
             "fof(sort_member_1,axiom,human(socrates),file('x.p',sort_member_1)).\n"
             "fof(sink,plain,$false,inference(r,[],[rule,sort_member_1])).\n")
    assert relevant_premises_from_tstp(proof, 3, name_map) == (1,)
    assert _premise_use_from_tstp(proof, 3, name_map) == ((1,), (("sort_member_1", "socrates is in the sort Human"),))
    with_nonempty = proof.replace("[rule,sort_member_1]", "[rule,sort_member_1,nonempty_sort_1]").replace(
        "fof(sink", "fof(nonempty_sort_1,axiom,?[X]:human(X),file('x.p',nonempty_sort_1)).\nfof(sink")
    used = _premise_use_from_tstp(with_nonempty, 3, name_map)
    assert used == ((1,), (("nonempty_sort_1", "the sort Human is not empty"),
                           ("sort_member_1", "socrates is in the sort Human")))


def test_without_a_record_the_writers_own_background_names_are_recognised_by_their_shape():
    from unicode_fol_kit.atp.tstp import _premise_use_from_tstp
    proof = ("fof(premise_2,axiom,p(a),file('x.p',premise_2)).\n"
             "fof(sort_member_3,axiom,human(a),file('x.p',sort_member_3)).\n"
             "fof(nonempty_sort_1,axiom,?[X]:human(X),file('x.p',nonempty_sort_1)).\n"
             "fof(sink,plain,$false,inference(r,[],[premise_2,sort_member_3,nonempty_sort_1])).\n")
    assert relevant_premises_from_tstp(proof, 2) == (1,)
    assert _premise_use_from_tstp(proof, 2) == ((1,), (("nonempty_sort_1", ""), ("sort_member_3", "")))


def test_a_background_name_the_record_does_not_hold_is_not_background():
    # The record of this problem has no sort, so a leaf called sort_member_1 is not one of its lines.
    _text, name_map = generate_tptp_problem_with_mapping([p("P", A)], None, premise_names=["one"])
    proof = ("fof(sort_member_1,axiom,human(a),file('x.p',sort_member_1)).\n"
             "fof(sink,plain,$false,inference(r,[],[sort_member_1])).\n")
    assert relevant_premises_from_tstp(proof, 1, name_map) is None


# =============================================================================
# Live: the real provers
# =============================================================================

def _live_vampire() -> Optional[Tuple[str, bool]]:
    found = shutil.which("vampire")
    if found:
        return found, False
    try:
        probe = subprocess.run(["wsl.exe", "vampire", "--version"], capture_output=True, text=True, timeout=30)
        if probe.returncode == 0 and "Vampire" in probe.stdout:
            return "vampire", True
    except Exception:                                      # noqa: BLE001 -- any failure means "absent"
        pass
    return None


_VAMPIRE = _live_vampire()
needs_vampire = pytest.mark.skipif(_VAMPIRE is None, reason="no Vampire reachable (PATH, or 'wsl vampire')")
needs_eprover = pytest.mark.skipif(not eprover_available(), reason="no eprover binary found")

#: (label, premises, goal, writer options, the premises the proof rests on)
LIVE_CASES = [
    ("fof", FOF_PREMISES, FOF_GOAL, {"tff": False}, (0, 2)),
    ("tf0", SORTED_PREMISES, SORTED_GOAL, {"tff": True}, (1,)),
    ("tfa", [p("Z", Constant("u")), p("P", A), p("Z", Constant("w")), p("T", B)], p("P", A), {"sort": "int"}, (1,)),
    ("fof of a sorted problem", SORTED_PREMISES, SORTED_GOAL, {"tff": False}, (1,)),
]


@needs_vampire
@pytest.mark.parametrize("label, premises, goal, options, expected", LIVE_CASES, ids=[c[0] for c in LIVE_CASES])
def test_live_vampire_gives_back_the_name_with_a_space_a_quote_and_a_non_ascii_letter(
        label, premises, goal, options, expected):
    path, use_wsl = _VAMPIRE
    result = check_entailment_vampire_detailed(
        premises, goal, path, timeout=60, use_wsl=use_wsl, premise_names=NAMES[:len(premises)], **options)
    assert result["status"] == "proved", result
    assert result["relevant_premises"] == expected, result["relevant_premises"]


@needs_eprover
@pytest.mark.parametrize("label, premises, goal, options, expected", LIVE_CASES, ids=[c[0] for c in LIVE_CASES])
def test_live_eprover_gives_back_the_name_with_a_space_a_quote_and_a_non_ascii_letter(
        label, premises, goal, options, expected):
    result = check_entailment_eprover_detailed(
        premises, goal, timeout=60, premise_names=NAMES[:len(premises)], **options)
    assert result["status"] == "proved", result
    assert result["relevant_premises"] == expected, result["relevant_premises"]
    assert eprover_relevant_premises(premises, goal, timeout=60, premise_names=NAMES[:len(premises)],
                                     **options) == expected


@needs_vampire
def test_live_vampire_does_not_ask_for_axiom_names_unless_the_caller_does():
    path, use_wsl = _VAMPIRE
    result = check_entailment_vampire_detailed(FOF_PREMISES, FOF_GOAL, path, timeout=60, use_wsl=use_wsl, tff=False)
    assert result["status"] == "proved" and result["relevant_premises"] is None and result["background_used"] == ()
    asked = check_entailment_vampire_detailed(FOF_PREMISES, FOF_GOAL, path, timeout=60, use_wsl=use_wsl,
                                              tff=False, axiom_names=True)
    assert asked["relevant_premises"] == FOF_USED


# a sorted problem on which the fof reading needs a background fact: ∀x:Human Mortal(x), Q(zed) ⊢ ∃x:Human Mortal(x)
# is valid only because Human is not empty (the first premise is the proof); with socrates in Human it also needs
# the membership line.
NONEMPTY_PREMISES = [SortedQuantifier("∀", X, "Human", p("Mortal", X)), p("Q", Constant("zed"))]
NONEMPTY_GOAL = SortedQuantifier("∃", X, "Human", p("Mortal", X))
MEMBERSHIP_PREMISES = [p("R", Constant("zed")), SortedQuantifier("∀", X, "Human", p("Mortal", X))]
MEMBERSHIP_GOAL = p("Mortal", SOCRATES)


@needs_eprover
@pytest.mark.parametrize("premises, goal, relevant, background_name", [
    (NONEMPTY_PREMISES, NONEMPTY_GOAL, (0,), "nonempty_sort_1"),
    (MEMBERSHIP_PREMISES, MEMBERSHIP_GOAL, (1,), "sort_member_1"),
], ids=["non-emptiness of a sort", "membership of a sorted constant"])
def test_live_eprover_proof_that_uses_a_sort_fact_has_relevant_premises_and_names_the_fact(
        premises, goal, relevant, background_name):
    assert eprover_relevant_premises(premises, goal, timeout=60, tff=False) == relevant
    result = check_entailment_eprover_detailed(premises, goal, timeout=60, tff=False)
    assert [name for name, _meaning in result["background_used"]] == [background_name]
    verdict = EProverBackend().decide(goal, premises, timeout=60000, tff=False)
    assert verdict.status == "proved"
    assert "background facts" in verdict.detail and background_name in verdict.detail
    assert "not premises" in verdict.detail


@needs_vampire
@pytest.mark.parametrize("premises, goal, relevant, background_name", [
    (NONEMPTY_PREMISES, NONEMPTY_GOAL, (0,), "nonempty_sort_1"),
    (MEMBERSHIP_PREMISES, MEMBERSHIP_GOAL, (1,), "sort_member_1"),
], ids=["non-emptiness of a sort", "membership of a sorted constant"])
def test_live_vampire_proof_that_uses_a_sort_fact_has_relevant_premises_and_names_the_fact(
        premises, goal, relevant, background_name):
    path, use_wsl = _VAMPIRE
    result = check_entailment_vampire_detailed(premises, goal, path, timeout=60, use_wsl=use_wsl,
                                               tff=False, axiom_names=True)
    assert result["status"] == "proved"
    assert result["relevant_premises"] == relevant
    assert background_name in [name for name, _meaning in result["background_used"]]
