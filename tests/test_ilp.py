"""Tests for :mod:`unicode_fol_kit.ilp`.

Every expected file, AST and refusal is hand-derived from the input, never
copied from a run. The structures are built by hand rather than from SMILES so
the whole file runs without RDKit — what is being tested is the ENCODING, and
that is chemistry-independent.

Two things carry most of the weight, because they are the two mistakes the
package exists to make impossible (see its docstring):

* every individual's Prolog name pins down its own example, and
* the example argument appears on the membership predicate and nowhere else.

Both are checked by reading the emitted file back and looking, not by trusting
that the emitter meant well.
"""

import doctest
import os
import re

import pytest

from unicode_fol_kit.fol.nodes import And, Atom, Quantifier, Variable
from unicode_fol_kit.fol.prolog_input import PrologParsingError
from unicode_fol_kit.ilp import (
    Example, IlpEncodingError, IlpTask, check_separation, clause_to_formula,
    hypothesis_to_formulas, task_from_structures, to_prolog_atom,
)
from unicode_fol_kit.ilp import readback as readback_module
from unicode_fol_kit.ilp import separation as separation_module
from unicode_fol_kit.ilp import task as task_module
from unicode_fol_kit.semantics import FiniteStructure


# ---------------------------------------------------------------------------
# Fixtures: three-atom structures with the amide / acid skeleton
# ---------------------------------------------------------------------------

def amide_like():
    """``c1=o1``, ``c1-n1`` — carbon double-bonded to oxygen and single-bonded
    to nitrogen. Bonds are stored symmetrically, as
    :func:`~unicode_fol_kit.chem.mol_to_structure` stores them."""
    return FiniteStructure(
        domain=("c1", "o1", "n1"),
        extensions={
            ("c", 1): [("c1",)], ("o", 1): [("o1",)], ("n", 1): [("n1",)],
            ("bDOUBLE", 2): [("c1", "o1"), ("o1", "c1")],
            ("bSINGLE", 2): [("c1", "n1"), ("n1", "c1")],
        })


def acid_like():
    """``c1=o1``, ``c1-o2`` — the same skeleton with a second oxygen where the
    nitrogen was. The interesting negative: it has a C=O and a C-single-bond,
    so only the ATOM TYPE separates it."""
    return FiniteStructure(
        domain=("c1", "o1", "o2"),
        extensions={
            ("c", 1): [("c1",)], ("o", 1): [("o1",), ("o2",)], ("n", 1): [],
            ("bDOUBLE", 2): [("c1", "o1"), ("o1", "c1")],
            ("bSINGLE", 2): [("c1", "o2"), ("o2", "c1")],
        })


def a_task(**kwargs):
    return task_from_structures("amide", {"m1": amide_like()},
                                {"m2": acid_like()}, **kwargs)


FACT_RE = re.compile(r"^([a-z][A-Za-z0-9_]*)\(([^)]*)\)\.$")


def facts_of(text):
    """``[(functor, [arg, …]), …]`` from an emitted ``bk.pl``, comments and
    directives dropped."""
    out = []
    for line in text.splitlines():
        line = line.strip()
        if not line or line.startswith("%") or line.startswith(":-"):
            continue
        match = FACT_RE.match(line)
        assert match, f"not a fact: {line!r}"
        out.append((match.group(1), match.group(2).split(",")))
    return out


# ---------------------------------------------------------------------------
# Naming
# ---------------------------------------------------------------------------

def test_only_the_first_character_is_folded():
    """``bSINGLE`` is already a legal Prolog atom. Folding the whole name to
    ``bsingle`` would destroy a distinction ChemLog's vocabulary makes and
    could not be undone on the way back — the round trip would land on
    ``Bsingle``."""
    assert to_prolog_atom("bSINGLE") == "bSINGLE"
    assert to_prolog_atom("Amide") == "amide"
    assert to_prolog_atom("c") == "c"


def test_a_name_that_cannot_become_an_atom_is_refused_not_quoted():
    with pytest.raises(IlpEncodingError) as info:
        to_prolog_atom("1,2-diacyl")
    assert "legal Prolog atom" in str(info.value)


@pytest.mark.parametrize("name", ["m1\n", "c1\n", "amide\n"])
def test_a_trailing_newline_does_not_sneak_through_the_name_check(name):
    """``$`` in Python also matches immediately BEFORE a final newline, so
    ``re.match`` would accept ``"m1\\n"`` — and in Prolog a newline is
    whitespace, which makes ``m1`` and ``m1\\n`` one atom while every
    uniqueness check here still sees two. A name read from a file with
    unstripped lines hits this directly."""
    with pytest.raises(IlpEncodingError):
        to_prolog_atom(name)


def test_a_trailing_newline_in_an_individual_is_refused_too():
    odd = FiniteStructure(domain=("c1", "c1\n"),
                          extensions={("c", 1): [("c1",)]})
    with pytest.raises(IlpEncodingError):
        IlpTask("t", [Example("m1", odd, True),
                      Example("m2", acid_like(), False)])


def test_an_illegal_example_id_is_refused_at_construction():
    with pytest.raises(IlpEncodingError):
        Example("CHEBI:15377", amide_like(), True)


# ---------------------------------------------------------------------------
# Guarantee 1: an individual's name pins down its own example
# ---------------------------------------------------------------------------

def test_every_individual_carries_its_example_prefix():
    """``c1`` exists in both structures and denotes a different atom in each.
    Emitted raw, a learner joins across examples through the shared name."""
    text = a_task().background_text()

    assert "c(m1_c1)." in text
    assert "c(m2_c1)." in text
    for functor, args in facts_of(text):
        for arg in args:
            if functor == "atom_in" and arg == args[0]:
                continue                      # the example itself
            assert arg.startswith(("m1_", "m2_")), (functor, arg)


def test_two_pairs_that_would_spell_the_same_constant_are_refused():
    """Example ``m1`` with individual ``c_c1`` and example ``m1_c`` with
    individual ``c1`` both spell ``m1_c_c1``. The prefix alone is not enough;
    the injectivity has to be CHECKED, and it is, before any file exists."""
    left = FiniteStructure(domain=("c_c1",), extensions={("c", 1): [("c_c1",)]})
    right = FiniteStructure(domain=("c1",), extensions={("c", 1): []})

    with pytest.raises(IlpEncodingError) as info:
        IlpTask("t", [Example("m1", left, True), Example("m1_c", right, False)])
    message = str(info.value)
    assert "m1_c_c1" in message and "m1_c" in message and "m1" in message


def test_an_individual_constant_colliding_with_an_EXAMPLE_name_is_refused():
    """Individuals and example names share one namespace in the file. Example
    ``m1`` with individual ``a`` spells ``m1_a`` — which is also the name of an
    example called ``m1_a``, so one constant would denote an atom of one
    molecule and a whole other molecule."""
    left = FiniteStructure(domain=("a",), extensions={("c", 1): [("a",)]})
    right = FiniteStructure(domain=("b",), extensions={("c", 1): []})

    with pytest.raises(IlpEncodingError) as info:
        IlpTask("t", [Example("m1", left, True), Example("m1_a", right, False)])
    message = str(info.value)
    assert "m1_a" in message and "the example 'm1_a'" in message


def test_two_examples_with_the_same_prolog_name_are_refused():
    """``M1`` and ``m1`` fold to one atom, so they are one example in the file
    and two in the caller's head."""
    with pytest.raises(IlpEncodingError) as info:
        IlpTask("t", [Example("M1", amide_like(), True),
                      Example("m1", acid_like(), False)])
    assert "both name the example 'm1'" in str(info.value)


def test_an_individual_that_is_not_word_characters_is_refused():
    odd = FiniteStructure(domain=("c-1",), extensions={("c", 1): [("c-1",)]})
    with pytest.raises(IlpEncodingError) as info:
        IlpTask("t", [Example("m1", odd, True),
                      Example("m2", acid_like(), False)])
    assert "'c-1'" in str(info.value)


# ---------------------------------------------------------------------------
# Guarantee 2: the example argument lives on the membership predicate alone
# ---------------------------------------------------------------------------

def test_no_predicate_but_membership_mentions_an_example():
    """The emitter has no way to put the example anywhere else, and this is
    the check that says so about the actual bytes."""
    task = a_task()
    examples = {e.atom for e in task.examples}

    for functor, args in facts_of(task.background_text()):
        mentioned = [a for a in args if a in examples]
        if functor == "atom_in":
            assert mentioned == [args[0]], args
        else:
            assert mentioned == [], (functor, args)


def test_membership_facts_cover_the_whole_domain_once():
    task = a_task()
    membership = [args for functor, args in facts_of(task.background_text())
                  if functor == "atom_in"]

    assert membership == [["m1", "m1_c1"], ["m1", "m1_o1"], ["m1", "m1_n1"],
                          ["m2", "m2_c1"], ["m2", "m2_o1"], ["m2", "m2_o2"]]


def test_a_body_predicate_colliding_with_membership_is_refused():
    structure = FiniteStructure(
        domain=("a",), extensions={("c", 1): [("a",)], ("atom_in", 2): []})
    with pytest.raises(IlpEncodingError) as info:
        IlpTask("t", [Example("m1", structure, True),
                      Example("m2", acid_like(), False)],
                body_predicates=[("atom_in", 2)])
    assert "exactly one predicate" in str(info.value)


def test_a_colliding_symbol_is_left_out_of_an_INFERRED_vocabulary_visibly():
    """Inference offers what it can encode; what it cannot is reported, not
    dropped in silence — and the reason ends up in the emitted file."""
    structure = FiniteStructure(
        domain=("a",), extensions={("c", 1): [("a",)], ("atom_in", 2): []})
    task = IlpTask("t", [Example("m1", structure, True),
                         Example("m2", acid_like(), False)])

    assert (("atom_in", 2), "collides with the membership predicate") \
        in task.excluded_predicates
    assert ("atom_in", 2) not in task.body_predicates
    assert "left out: atom_in/2" in task.background_text()


# ---------------------------------------------------------------------------
# Guarantee 3: a 0-ary predicate cannot be attached to an example
# ---------------------------------------------------------------------------

def test_an_explicit_zero_ary_body_predicate_is_refused():
    """``neutral.`` emitted for one example is a fact about the whole file, so
    it would hold for every example at once."""
    structure = FiniteStructure(
        domain=("a",),
        extensions={("c", 1): [("a",)], ("neutral", 0): [()]})
    with pytest.raises(IlpEncodingError) as info:
        IlpTask("t", [Example("m1", structure, True),
                      Example("m2", acid_like(), False)],
                body_predicates=[("neutral", 0)])
    assert "0-ary" in str(info.value)


def test_a_zero_ary_predicate_is_left_out_of_an_inferred_vocabulary():
    structure = FiniteStructure(
        domain=("a",),
        extensions={("c", 1): [("a",)], ("neutral", 0): [()]})
    task = IlpTask("t", [Example("m1", structure, True),
                         Example("m2", acid_like(), False)])

    assert (("neutral", 0), "0-ary: cannot be attached to one example") \
        in task.excluded_predicates
    assert "left out: neutral/0" in task.background_text()


# ---------------------------------------------------------------------------
# The facts are the extension
# ---------------------------------------------------------------------------

def test_facts_are_exactly_the_stored_extension_in_both_directions():
    """A bond is stored symmetrically, so both directions are emitted — not
    because the emitter knows bonds are symmetric, but because both tuples are
    in the extension. An asymmetric relation gets the one direction it has."""
    task = a_task()
    facts = facts_of(task.background_text())

    assert [args for functor, args in facts if functor == "bDOUBLE"] == [
        ["m1_c1", "m1_o1"], ["m1_o1", "m1_c1"],
        ["m2_c1", "m2_o1"], ["m2_o1", "m2_c1"]]


def test_an_asymmetric_relation_is_not_symmetrised():
    directed = FiniteStructure(
        domain=("a", "b"),
        extensions={("c", 1): [("a",)], ("before", 2): [("a", "b")]})
    task = IlpTask("t", [Example("m1", directed, True),
                         Example("m2", acid_like(), False)],
                   body_predicates=[("before", 2)])

    assert [args for functor, args in facts_of(task.background_text())
            if functor == "before"] == [["m1_a", "m1_b"]]


def test_an_empty_extension_emits_no_facts_but_still_declares_the_predicate():
    """``n/1`` is empty in the acid structure. The predicate is interpreted
    there — it is just false of everything — so it stays declared."""
    text = a_task().background_text()

    assert ":- discontiguous n/1." in text
    assert [args for functor, args in facts_of(text) if functor == "n"] \
        == [["m1_n1"]]


def test_a_computed_predicate_is_materialised():
    computed = FiniteStructure(
        domain=("a", "b"),
        extensions={("c", 1): [("a",)]},
        computed={("odd", 1): lambda x: x == "b"})
    task = IlpTask("t", [Example("m1", computed, True),
                         Example("m2", acid_like(), False)],
                   body_predicates=[("odd", 1)])

    assert [args for functor, args in facts_of(task.background_text())
            if functor == "odd"] == [["m1_b"]]


def test_materialising_a_computed_predicate_is_refused_above_the_bound():
    computed = FiniteStructure(
        domain=tuple(f"a{i}" for i in range(10)),
        extensions={("c", 1): []},
        computed={("near", 2): lambda x, y: x == y})
    task = IlpTask("t", [Example("m1", computed, True),
                         Example("m2", acid_like(), False)],
                   body_predicates=[("near", 2)], max_computed_tuples=99)

    with pytest.raises(IlpEncodingError) as info:
        task.background_text()
    assert "100 calls" in str(info.value)
    assert "max_computed_tuples=99" in str(info.value)


def test_a_predicate_no_structure_interprets_is_refused():
    with pytest.raises(IlpEncodingError) as info:
        a_task(body_predicates=[("c", 1), ("halogen", 1)])
    assert "halogen/1" in str(info.value)


def test_two_symbols_folding_to_one_functor_are_refused_not_merged():
    """Only the first character is folded, so ``N/1`` and ``n/1`` are two
    symbols and one Prolog predicate. Emitted, their extensions would be
    unioned under that functor — background knowledge describing a relation no
    structure has. Same class of collision as two individuals spelling one
    constant."""
    both = FiniteStructure(
        domain=("a", "b"),
        extensions={("N", 1): [("a",)], ("n", 1): [("b",)]})

    with pytest.raises(IlpEncodingError) as info:
        IlpTask("t", [Example("m1", both, True),
                      Example("m2", acid_like(), False)])
    assert "both emit as n/1" in str(info.value)


def test_the_same_functor_at_different_arities_is_fine():
    """``p/1`` and ``p/2`` are DISTINCT Prolog predicates, so there is nothing
    to refuse — and the readback can still tell them apart."""
    structure = FiniteStructure(
        domain=("a", "b"),
        extensions={("p", 1): [("a",)], ("p", 2): [("a", "b")]})
    task = IlpTask("t", [Example("m1", structure, True),
                         Example("m2", acid_like(), False)],
                   body_predicates=[("p", 1), ("p", 2)])

    assert ":- discontiguous p/1." in task.background_text()
    assert ":- discontiguous p/2." in task.background_text()
    assert task.read_clause("t(A) :- p(C), p(C,D), atom_in(A,C)."
                            ).to_unicode_str() == "∃c ∃d (p(c) ∧ p(c, d))"


def test_extra_bias_as_a_bare_string_is_refused():
    """A string is iterable, so it would become one bias line per character —
    a broken bias file the learner rejects far from the cause."""
    with pytest.raises(IlpEncodingError) as info:
        a_task(extra_bias="enable_recursion.")
    assert "one bias line per character" in str(info.value)


def test_a_note_containing_a_bare_cr_is_refused():
    """`newline="\\n"` disables translation but validates nothing, so a note
    ending in CR — the normal residue of stripping only ``\\n`` from a CRLF
    file — would put a literal CRLF into a file this module promises is
    LF-only."""
    with pytest.raises(IlpEncodingError):
        Example("m1", amide_like(), True, "CCO\r")


def test_a_refused_rendering_leaves_no_directory_behind(tmp_path):
    """The three files are rendered before the directory is created, for the
    same reason the parent must already exist."""
    computed = FiniteStructure(
        domain=tuple(f"a{i}" for i in range(10)),
        extensions={("c", 1): []},
        computed={("near", 2): lambda x, y: x == y})
    task = IlpTask("t", [Example("m1", computed, True),
                         Example("m2", acid_like(), False)],
                   body_predicates=[("near", 2)], max_computed_tuples=99)

    with pytest.raises(IlpEncodingError):
        task.write(str(tmp_path / "amide"))
    assert not (tmp_path / "amide").exists()


# ---------------------------------------------------------------------------
# The other two files, and writing
# ---------------------------------------------------------------------------

def test_examples_file_labels_each_example():
    assert a_task().examples_text() == "pos(amide(m1)).\nneg(amide(m2)).\n"


def test_notes_become_comments_and_are_never_parsed():
    task = IlpTask("amide", [Example("m1", amide_like(), True, "NCC(=O)NCC(=O)O"),
                             Example("m2", acid_like(), False, "CC(=O)O")])

    assert task.examples_text() == (
        "pos(amide(m1)).  % NCC(=O)NCC(=O)O\n"
        "neg(amide(m2)).  % CC(=O)O\n")
    assert "% m1 (pos): NCC(=O)NCC(=O)O" in task.background_text()


def test_bias_declares_the_head_the_membership_and_every_body_predicate():
    assert a_task().bias_text() == (
        "head_pred(amide,1).\n"
        "body_pred(atom_in,2).\n"
        "body_pred(bDOUBLE,2).\n"
        "body_pred(bSINGLE,2).\n"
        "body_pred(c,1).\n"
        "body_pred(n,1).\n"
        "body_pred(o,1).\n"
        "max_vars(6).\n"
        "max_body(8).\n"
        "max_clauses(1).\n")


def test_extra_bias_lines_go_through_verbatim():
    task = a_task(extra_bias=["enable_recursion.", "type(c,(atom,))."])

    assert task.bias_text().endswith(
        "max_clauses(1).\nenable_recursion.\ntype(c,(atom,)).\n")


def test_rendering_is_byte_identical_across_calls_and_across_tasks():
    """A task directory that differs run to run cannot be diffed or committed,
    and a spurious diff hides a real one."""
    first, second = a_task(), a_task()

    assert first.background_text() == second.background_text()
    assert first.background_text() == first.background_text()


def test_write_produces_the_three_files_with_lf_endings(tmp_path):
    paths = a_task().write(str(tmp_path / "amide"))

    assert sorted(os.path.basename(p) for p in paths.values()) == [
        "bias.pl", "bk.pl", "exs.pl"]
    for path in paths.values():
        with open(path, "rb") as handle:
            assert b"\r\n" not in handle.read()


def test_write_refuses_a_path_whose_parent_does_not_exist(tmp_path):
    with pytest.raises(IlpEncodingError) as info:
        a_task().write(str(tmp_path / "nope" / "amide"))
    assert "parent directory" in str(info.value)


def test_counts_report_what_the_learner_will_see():
    """6 membership facts + 3 unary + 4 bDOUBLE + 4 bSINGLE + 3 o-facts, all
    counted from the extensions above: 3+3 individuals, c(m1_c1)/c(m2_c1),
    n(m1_n1), o(m1_o1)/o(m2_o1)/o(m2_o2)."""
    assert a_task().counts == {"positive": 1, "negative": 1, "predicates": 5,
                               "facts": 6 + 2 + 1 + 3 + 4 + 4}


# ---------------------------------------------------------------------------
# Refusals about the example sets themselves
# ---------------------------------------------------------------------------

def test_a_task_without_negatives_is_refused():
    """With no negatives the empty body is already perfect, so any result
    would be vacuous — a fact about the task, not about the learner."""
    with pytest.raises(IlpEncodingError) as info:
        IlpTask("t", [Example("m1", amide_like(), True)])
    assert "no negative examples" in str(info.value)


def test_a_task_without_positives_is_refused():
    with pytest.raises(IlpEncodingError) as info:
        IlpTask("t", [Example("m1", amide_like(), False)])
    assert "nothing to learn" in str(info.value)


@pytest.mark.parametrize("kwargs", [{"max_vars": 0}, {"max_body": -1},
                                    {"max_clauses": 0},
                                    {"max_computed_tuples": 0}])
def test_nonsensical_bounds_are_refused(kwargs):
    with pytest.raises(IlpEncodingError):
        a_task(**kwargs)


# ---------------------------------------------------------------------------
# Reading the answer back
# ---------------------------------------------------------------------------

def test_the_membership_atom_is_dropped_and_the_rest_closed_existentially():
    """Hand-derived from ``amide(A) :- bDOUBLE(C,B), n(C), atom_in(A,B).``:
    the importer capitalises predicates and lower-cases variables, the
    membership atom goes, and b/c — including ``b``, which only the membership
    atom introduced — are existentially closed alphabetically
    outermost-first, in the body's own order."""
    b, c = Variable("b"), Variable("c")
    expected = Quantifier("∃", b, Quantifier("∃", c, And(
        Atom("BDOUBLE", [c, b]), Atom("N", [c]))))

    assert clause_to_formula(
        "amide(A) :- bDOUBLE(C,B), n(C), atom_in(A,B).") == expected


# ---------------------------------------------------------------------------
# Guarantee 4: every goal must reach the example
# ---------------------------------------------------------------------------

def test_a_goal_the_membership_atoms_never_reached_is_refused():
    """In ``t(A) :- n(C), atom_in(A,B), o(B).`` nothing connects ``C`` to
    ``B``, so in Prolog ``n(C)`` ranges over the whole fact base: it succeeds
    if ANY example has a nitrogen, making the clause true of every example.
    Reading it as ``∃c N(c)`` over one structure would turn that global claim
    into a local one — and a clause covering a negative example would come
    back scoring perfectly."""
    with pytest.raises(IlpEncodingError) as info:
        clause_to_formula("t(A) :- n(C), atom_in(A,B), o(B).")
    message = str(info.value)
    assert "not linked to the example" in message
    assert "nothing connects c" in message


def test_linkage_propagates_through_positive_goals():
    """``C`` is linked to the example through ``bDOUBLE(C,B)``, and ``D``
    through ``bSINGLE(C,D)`` — one hop further out. Both are accepted."""
    formula = clause_to_formula(
        "t(A) :- n(D), bSINGLE(C,D), bDOUBLE(C,B), atom_in(A,B).")

    assert formula.to_unicode_str() == (
        "∃b ∃c ∃d (N(d) ∧ BSINGLE(c, d) ∧ BDOUBLE(c, b))")


def test_linkage_does_NOT_propagate_through_a_negated_goal():
    """``\\+`` binds nothing in SLDNF, so ``\\+ bSINGLE(C,D)`` cannot be what
    links ``D`` to the example. Were it allowed to, ``D`` would be closed with
    a top-level ``∃`` outside the negation — ``∃d ¬…`` instead of ``¬∃d …``,
    which is a far weaker claim than the clause was scored under."""
    with pytest.raises(IlpEncodingError) as info:
        clause_to_formula("t(A) :- bDOUBLE(C,B), \\+ bSINGLE(C,D), atom_in(A,B).",
                          negation_as_failure="classical")
    assert "nothing connects d" in str(info.value)


def test_a_variable_bound_positively_may_also_appear_under_a_negation():
    """The normal shape: ``C`` is bound by a positive goal first, so ``∃c (…
    ∧ ¬O(c))`` is exactly the SLDNF reading."""
    formula = clause_to_formula("t(A) :- n(C), \\+ o(C), atom_in(A,C).",
                                negation_as_failure="classical")

    assert formula.to_unicode_str() == "∃c (N(c) ∧ ¬O(c))"


def test_a_clause_with_no_membership_atom_at_all_is_refused():
    with pytest.raises(IlpEncodingError) as info:
        clause_to_formula("t(A) :- n(C).")
    assert "no atom_in atom is present at all" in str(info.value)


def test_a_ground_goal_is_refused():
    """A ground goal is decided against the whole fact base — it names one
    example's individual by name."""
    with pytest.raises(IlpEncodingError) as info:
        clause_to_formula("t(A) :- n(m1_c1), atom_in(A,B), o(B).")
    assert "no variables" in str(info.value)


def test_predicates_restore_the_spelling_the_task_emitted():
    """The importer's capitalisation is right for a clause from anywhere and
    wrong for one that came from our own structures, whose symbols are
    lower-case. Naming the vocabulary makes the round trip name-exact."""
    formula = clause_to_formula("amide(A) :- n(C), bSINGLE(C,B), atom_in(A,B).",
                                predicates=["n", ("bSINGLE", 2)])

    assert formula.to_unicode_str() == "∃b ∃c (n(c) ∧ bSINGLE(c, b))"


def test_read_clause_uses_the_tasks_own_vocabulary():
    task = a_task()
    formula = task.read_clause("amide(A) :- n(C), bSINGLE(C,B), atom_in(A,B).")

    assert formula.to_unicode_str() == "∃b ∃c (n(c) ∧ bSINGLE(c, b))"


def test_two_predicates_that_capitalise_alike_are_refused():
    """``bond`` and ``Bond`` both arrive as ``Bond``; restoring either would
    be a coin flip."""
    with pytest.raises(IlpEncodingError) as info:
        clause_to_formula("t(A) :- bond(B,C), atom_in(A,B).",
                          predicates=["bond", "Bond"])
    assert "undecidable" in str(info.value)


def test_the_same_functor_at_two_arities_is_not_a_clash():
    """``P/1`` and ``p/2`` emit as ``p/1`` and ``p/2``, which Prolog and the
    importer both keep apart — so the vocabulary must be keyed by arity, or
    every readback on such a task would raise on every clause."""
    formula = clause_to_formula("t(A) :- p(C), p(C,D), atom_in(A,C).",
                                predicates=[("P", 1), ("p", 2)])

    assert formula.to_unicode_str() == "∃c ∃d (P(c) ∧ p(c, d))"


def test_a_membership_atom_naming_a_second_example_is_refused():
    """``atom_in(B,C)`` in a clause headed ``t(A)`` is the learner joining two
    examples. No formula about one structure means the same thing."""
    with pytest.raises(IlpEncodingError) as info:
        clause_to_formula("t(A) :- n(C), atom_in(B,C).")
    assert "SECOND example" in str(info.value)


def test_the_example_variable_surviving_the_drop_is_refused():
    with pytest.raises(IlpEncodingError) as info:
        clause_to_formula("t(A) :- n(A), atom_in(A,B).")
    assert "still occurs" in str(info.value)


def test_a_membership_atom_inside_a_disjunction_is_refused():
    """Dropping a literal out of a disjunct changes what the clause says, so
    it is refused rather than approximated."""
    with pytest.raises(IlpEncodingError) as info:
        clause_to_formula("t(A) :- n(C), (atom_in(A,B) ; o(B)).")
    assert "top-level condition" in str(info.value)


def test_a_clause_that_is_only_membership_is_refused():
    with pytest.raises(IlpEncodingError) as info:
        clause_to_formula("t(A) :- atom_in(A,B).")
    assert "no content besides" in str(info.value)


def test_a_fact_is_refused():
    with pytest.raises(IlpEncodingError) as info:
        clause_to_formula("t(m1).")
    assert "is a fact, not a rule" in str(info.value)


def test_a_ground_head_is_refused():
    with pytest.raises(IlpEncodingError) as info:
        clause_to_formula("t(m1) :- n(C), atom_in(m1,C).")
    assert "must be a VARIABLE" in str(info.value)


def test_a_multi_argument_head_is_refused():
    with pytest.raises(IlpEncodingError) as info:
        clause_to_formula("t(A,B) :- n(C), atom_in(A,C).")
    assert "exactly" in str(info.value)


def test_a_clause_outside_the_prolog_fragment_still_raises_the_importers_error():
    """The refusal belongs to the importer and keeps its type — this module
    does not relabel someone else's diagnosis."""
    with pytest.raises(PrologParsingError):
        clause_to_formula("t(A) :- n(C), !, atom_in(A,C).")


def test_a_custom_membership_name_is_honoured():
    formula = clause_to_formula("t(A) :- n(C), in_mol(A,C).",
                                membership="in_mol")

    assert formula.to_unicode_str() == "∃c N(c)"


def test_negation_as_failure_stays_opt_in_through_this_layer():
    clause = "t(A) :- n(C), \\+ o(C), atom_in(A,C)."
    with pytest.raises(PrologParsingError):
        clause_to_formula(clause)

    opted_in = clause_to_formula(clause, negation_as_failure="classical")
    assert opted_in.to_unicode_str() == "∃c (N(c) ∧ ¬O(c))"


def test_the_opt_in_survives_the_target_check(tmp_path):
    """The head check re-parses the clause, so it has to be given the same
    setting — otherwise supplying ``target=`` (which ``read_hypothesis``
    always does) makes the opt-in unreachable, and the refusal tells the
    caller to pass the flag they just passed."""
    clause = "amide(A) :- n(C), \\+ o(C), atom_in(A,C)."

    formulas = hypothesis_to_formulas(clause, target="amide",
                                      negation_as_failure="classical")
    assert [f.to_unicode_str() for f in formulas] == ["∃c (N(c) ∧ ¬O(c))"]

    assert [f.to_unicode_str() for f in
            a_task().read_hypothesis(clause, negation_as_failure="classical")
            ] == ["∃c (n(c) ∧ ¬o(c))"]


# ---------------------------------------------------------------------------
# Whole hypotheses
# ---------------------------------------------------------------------------

def test_a_hypothesis_comes_back_as_separate_formulas_never_disjoined():
    """Two clauses with one head are alternatives only under the COMPLETION of
    the program — an assumption about the whole program, so the caller states
    it, not the reader. The learner's banner is a Prolog comment and is
    skipped."""
    text = ("% Precision:1.00, Recall:1.00, TP:6, FN:0, TN:8, FP:0\n"
            "amide(A) :- n(C), atom_in(A,C).\n"
            "amide(A) :- o(C), atom_in(A,C).\n")
    formulas = hypothesis_to_formulas(text)

    assert [f.to_unicode_str() for f in formulas] == ["∃c N(c)", "∃c O(c)"]


def test_a_hypothesis_with_a_foreign_head_is_refused_when_a_target_is_given():
    text = ("amide(A) :- n(C), atom_in(A,C).\n"
            "helper(A) :- o(C), atom_in(A,C).\n")

    assert len(hypothesis_to_formulas(text)) == 2       # no target: no opinion
    with pytest.raises(IlpEncodingError) as info:
        hypothesis_to_formulas(text, target="amide")
    assert "'Helper'" in str(info.value)


def test_read_hypothesis_checks_the_tasks_own_target():
    task = a_task()
    with pytest.raises(IlpEncodingError):
        task.read_hypothesis("acid(A) :- o(C), atom_in(A,C).")


# ---------------------------------------------------------------------------
# Separation
# ---------------------------------------------------------------------------

def test_a_reference_formula_that_separates_the_sets():
    """``∃c∃o∃n (c(c) ∧ o(o) ∧ n(n) ∧ bDOUBLE(c,o) ∧ bSINGLE(c,n))`` holds in
    the amide structure and fails in the acid one, which has no nitrogen."""
    task = a_task()
    reference = task.read_clause(
        "amide(A) :- c(C), o(O), n(N), bDOUBLE(C,O), bSINGLE(C,N), atom_in(A,C).")

    report = check_separation(reference, task)
    assert report.separates
    assert report.counts["true_positive"] == 1
    assert report.counts["true_negative"] == 1
    assert report.precision == 1.0 and report.recall == 1.0
    assert report.misclassified == ()


def test_an_over_general_formula_shows_its_false_positive():
    """A learner returns the SMALLEST hypothesis consistent with its examples.
    ``∃c∃o (c(c) ∧ bDOUBLE(c,o))`` is true of both structures — the negatives
    never forced it to say anything about nitrogen."""
    task = a_task()
    over_general = task.read_clause(
        "amide(A) :- c(C), bDOUBLE(C,O), atom_in(A,C).")

    report = check_separation(over_general, task)
    assert not report.separates
    assert report.counts["false_positive"] == 1
    assert [row["id"] for row in report.misclassified] == ["m2"]
    assert report.precision == 0.5


def test_a_vocabulary_mismatch_is_an_eval_error_not_a_false():
    """Without ``predicates=``, the importer's capitalisation survives and the
    structure interprets none of those symbols. That is a naming bug, and
    reporting it as "the definition does not hold" would send the reader
    looking in the wrong place."""
    task = a_task()
    kit_spelling = clause_to_formula("amide(A) :- n(C), atom_in(A,C).")

    report = check_separation(kit_spelling, task)
    assert [row["status"] for row in report.rows] == ["eval_error"] * 2
    assert "'N'/1 is not interpreted" in report.rows[0]["error"]
    assert not report.separates
    assert report.counts["true_positive"] == 0


def test_an_exhausted_budget_is_undecided_and_never_counted_as_false():
    task = a_task()
    formula = task.read_clause("amide(A) :- n(C), atom_in(A,C).")

    report = check_separation(formula, task, budget=1)
    assert [row["status"] for row in report.rows] == ["exhausted"] * 2
    assert all(row["holds"] is None for row in report.rows)
    assert report.counts["exhausted"] == 2
    assert report.counts["false_negative"] == 0
    assert not report.separates


def test_undefined_ratios_are_none_not_zero():
    """A formula that holds nowhere has no precision — reporting 0.0 would
    make an unasked question look answered."""
    task = a_task()
    nowhere = task.read_clause("amide(A) :- n(C), o(C), atom_in(A,C).")

    report = check_separation(nowhere, task)
    assert report.precision is None
    assert report.recall == 0.0


def test_all_different_is_the_callers_choice_and_it_changes_the_answer():
    """``∃c∃x∃y (bDOUBLE(c,x) ∧ bDOUBLE(c,y))`` looks like "two double bonds"
    and is not: with x and y allowed to coincide, one double bond satisfies
    it, so it holds in both fixtures. Require distinctness and it holds in
    neither — each has exactly one. The flag decides the verdict, so a
    check_separation that dropped it would fail this test."""
    task = a_task()
    formula = task.read_clause(
        "amide(A) :- bDOUBLE(C,X), bDOUBLE(C,Y), atom_in(A,C).")

    lenient = check_separation(formula, task).counts
    strict = check_separation(formula, task, all_different=True).counts

    assert (lenient["true_positive"], lenient["false_positive"]) == (1, 1)
    assert (strict["false_negative"], strict["true_negative"]) == (1, 1)


def test_check_separation_refuses_text_rather_than_guessing_a_dialect():
    with pytest.raises(TypeError) as info:
        check_separation("?[X]: c(X)", a_task())
    assert "parse it first" in str(info.value)


def test_an_empty_report_does_not_claim_to_separate_anything():
    """``all()`` over nothing is ``True``; answering "yes, it separates" about
    a report that decided nothing is a vacuous yes."""
    from unicode_fol_kit.ilp import SeparationReport

    assert SeparationReport(()).separates is False


# ---------------------------------------------------------------------------
# The round trip, end to end
# ---------------------------------------------------------------------------

def test_the_loop_closes(tmp_path):
    """structures → task files → (a learner would go here) → clause → formula
    → verdicts, with nothing hand-translated in between."""
    task = a_task()
    paths = task.write(str(tmp_path / "amide"))
    with open(paths["bk"], encoding="utf-8") as handle:
        assert "bSINGLE(m1_c1,m1_n1)." in handle.read()

    learned = "amide(A) :- n(C), bSINGLE(C,B), bDOUBLE(B,D), atom_in(A,B)."
    report = check_separation(task.read_clause(learned), task)

    assert report.separates
    assert report.rows[0]["steps"] is not None


# ---------------------------------------------------------------------------
# The docstrings' own examples
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("module", [task_module, readback_module,
                                    separation_module])
def test_module_doctests(module):
    """``attempted > 0`` as well as ``failed == 0``: ``testmod`` reports zero
    failures for a module with no examples at all, so the weaker assertion
    would stay green if every example this section is named after were
    deleted."""
    results = doctest.testmod(module, verbose=False)
    assert results.attempted > 0
    assert results.failed == 0


def test_package_doctests():
    import unicode_fol_kit.ilp as package

    results = doctest.testmod(package, verbose=False)
    assert results.attempted > 0
    assert results.failed == 0
