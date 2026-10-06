"""Small refusals that used to differ by the entry point that met them.

Each case below was a route that answered, or failed with a bare Python error,
where its neighbours refuse by name. The expectations are derived from what the
construct IS, not from what the code printed.
"""
import pytest

import unicode_fol_kit.dl as dl
from unicode_fol_kit.dl import tableau

A, B = dl.Atomic("A"), dl.Atomic("B")
TOP_OBJECT_PROPERTY = "http://www.w3.org/2002/07/owl#topObjectProperty"


# --- an individual spelled like a numeral, in Manchester Syntax ------------------------------

@pytest.mark.parametrize("individual", ["1", "-3", "1.5", "1.5f", "2F", "1.0e+2f"])
def test_the_manchester_writer_refuses_an_individual_it_could_not_read_back(individual):
    # `r value 1.5f` is, to the reader, a DATA value restriction to the float
    # literal 1.5 (and `r value 1` one to the integer 1). So the object value
    # restriction ∃r.{1.5f} has no Manchester spelling that reads back as itself,
    # and the writer says so instead of printing a different concept.
    with pytest.raises(ValueError, match="numeral") as refusal:
        dl.to_manchester(dl.HasValue("r", individual))
    assert individual in str(refusal.value)
    # the other writer has no such ambiguity and still writes it
    text = dl.to_owl_functional_class_expression(dl.HasValue("r", individual))
    assert dl.parse_owl_functional_class_expression(text) == dl.HasValue("r", individual)


@pytest.mark.parametrize("individual", ["alice", "a1", "1e5", "x0"])
def test_an_ordinary_individual_still_round_trips_through_manchester(individual):
    concept = dl.HasValue("r", individual)
    assert dl.parse_manchester(dl.to_manchester(concept)) == concept


# --- classify: a nominal and an inverse role are refused like everywhere else ----------------

@pytest.mark.parametrize("concept, word", [
    (dl.Nominal("a"), "Nominal"),
    (dl.Exists(dl.InverseRole("r"), B), "nverse"),
])
def test_classify_refuses_what_the_tableau_refuses_with_the_same_error(concept, word):
    # With ONE named concept the reduction to subsumes() is never reached, so
    # classify has to refuse on its own; it used to raise a bare TypeError, which
    # the MCP tools do not turn into a structured error.
    tbox = dl.TBox().add(A, concept)
    with pytest.raises(dl.UnsupportedConceptError) as refusal:
        dl.classify(tbox)
    assert word in str(refusal.value)
    with pytest.raises(dl.UnsupportedConceptError):
        dl.concept_satisfiable(concept, tbox)            # the same refusal, the same class


# --- the sweeps with nothing to sweep still read the ABox ------------------------------------

def test_realize_reads_a_value_restriction_asserted_in_the_abox_even_with_no_vocabulary():
    # realize(…, vocabulary=[]) makes no instance check at all. The value
    # restriction in the ABox is something the in-house tableau refuses, so the
    # honest answer is the refusal, not an empty list about a knowledge base it
    # never read.
    abox = dl.ABox().assert_concept("a", dl.HasValue("r", "b"))
    with pytest.raises(dl.UnsupportedConceptError, match="ObjectHasValue"):
        dl.realize(abox, "a", [])
    with pytest.raises(dl.UnsupportedConceptError, match="ObjectHasValue"):
        dl.realize_all(abox, [])
    # the control: without the value restriction the empty sweep is an empty answer
    plain = dl.ABox().assert_concept("a", A)
    assert dl.realize(plain, "a", []) == []
    assert dl.realize_all(plain, []) == {"a": []}


# --- a built-in property name that still carries its angle brackets --------------------------

def test_a_bracketed_built_in_property_name_is_the_same_built_in_property():
    # Both OWL readers store an IRI without its brackets; a hand-built name may
    # still carry them. <IRI> and IRI are one name in OWL, so the universal
    # property is refused as a role whichever way it is spelled.
    bare = tableau.reserved_role(TOP_OBJECT_PROPERTY)
    assert bare is not None
    assert tableau.reserved_role(f"<{TOP_OBJECT_PROPERTY}>") == bare
    assert tableau.reserved_role("<hasPart>") is None and tableau.reserved_role("<>") is None
    for name in (TOP_OBJECT_PROPERTY, f"<{TOP_OBJECT_PROPERTY}>", "owl:topObjectProperty"):
        with pytest.raises(dl.RoleExpressionError):
            dl.concept_satisfiable(dl.Exists(name, A))
        with pytest.raises(dl.RoleExpressionError):
            dl.concept_to_fol(dl.Exists(name, A))


# --- the Vampire backend reads tff= or says why not ------------------------------------------

def test_the_vampire_backend_refuses_a_tff_option_that_is_not_a_boolean():
    from unicode_fol_kit.atp.protocol import VampireBackend
    from unicode_fol_kit.fol.nodes import Atom, Constant
    goal = Atom("P", (Constant("a"),))
    # 'yes' is truthy; forwarding it would silently mean tff=True. sort='float'
    # is refused by name already, and so is this.
    with pytest.raises(ValueError, match="tff="):
        VampireBackend().decide(goal, [], tff="yes", vampire_path="vampire")


# --- a sort named like TPTP's built-in type of individuals ------------------------------------

def test_the_tf0_writer_refuses_a_sort_named_like_the_built_in_individual_type():
    # $i is the type TF0 gives every UNSORTED term. A user sort of that name would
    # be merged with it: ∀x:$i R(x) would be written as ∀x R(x), and
    # "∀x:$i R(x) ⊢ ∀y R(y)" — which does not hold, a sort being a part of the
    # universe — would be proved.
    from unicode_fol_kit.atp.tptp_tff import generate_tff_problem
    from unicode_fol_kit.fol.nodes import Atom, Quantifier, SortedQuantifier, Variable
    x, y = Variable("x"), Variable("y")
    premise = SortedQuantifier("∀", x, "$i", Atom("R", (x,)))
    with pytest.raises(NotImplementedError, match=r"\$i"):
        generate_tff_problem([premise], Quantifier("∀", y, Atom("R", (y,))))
    # the control: any other sort name is written as a sort of its own (asked
    # of the same sort — TF0 refuses to mix a sorted and an unsorted use of R)
    text = generate_tff_problem([SortedQuantifier("∀", x, "Human", Atom("R", (x,)))],
                                SortedQuantifier("∃", y, "Human", Atom("R", (y,))))
    assert "human: $tType" in text
