"""A property slot holds a relation on individuals; a predicate of properties does not fit in one.

``Pos(G)`` makes ``Pos`` a predicate of properties: its slot holds the property ``G``, which is
a relation on individuals. ``Meta(Pos)`` puts ``Pos`` itself in a slot of ``Meta``. Together,
``Meta(Pos) ∧ Pos(G)`` makes ``Meta`` a predicate of predicates of properties (fourth order).
The signature analysis types a slot as an individual or as ``("p", k)``, a property of
individuals of arity ``k``; it has no type for a property of properties. Typing ``Meta``'s slot
as ``("p", 1)`` because ``Pos`` has arity 1 would make the HOL writers declare
``Meta :: (i ⇒ bool) ⇒ bool`` and apply it to ``Pos :: (i ⇒ bool) ⇒ bool``: ill-typed text.
The analysis refuses the typing by name instead, as it refuses a slot used for an individual and
a property, or a predicate applied at two arities.

Every expectation is derived by hand from the definition above.
"""

import itertools
import random

import pytest

from unicode_fol_kit import MSFLParser, analyse_signatures, to_isabelle_to, to_thf_to
from unicode_fol_kit.fol.naming import ParsingError
from unicode_fol_kit.hol import HoAxiom, HoGoal, isabelle_ho_modal_theory, to_thf_ho_modal

parse = MSFLParser(third_order=True).parse
parse_modal = MSFLParser(third_order=True, modal=True).parse


def nested_error():
    from unicode_fol_kit.fol._ho_nodes import NestedPropertySlotError
    return NestedPropertySlotError


def test_a_predicate_of_properties_in_a_property_slot_is_refused_at_parse_time():
    with pytest.raises(ParsingError) as raised:
        parse("Meta(Pos) ∧ Pos(G)")
    assert isinstance(raised.value, nested_error())
    message = str(raised.value)
    assert "'Meta'" in message and "'Pos'" in message
    assert "argument slot 0" in message
    assert "fourth order" in message


def test_the_order_of_the_conjuncts_does_not_matter():
    with pytest.raises(ParsingError, match="fourth order"):
        parse("Pos(G) ∧ Meta(Pos)")


def test_the_error_is_a_parsing_error_like_the_other_typing_errors():
    assert issubclass(nested_error(), ParsingError)


def test_a_predicate_taking_itself_as_a_property_is_refused():
    # Pos(Pos): Pos takes a property (slot 0) and is the property in that very slot.
    with pytest.raises(ParsingError, match="fourth order") as raised:
        parse("Pos(Pos)")
    assert "'Pos'" in str(raised.value)


def test_a_bound_predicate_variable_that_takes_a_property_is_refused_in_a_property_slot():
    with pytest.raises(ParsingError, match="fourth order"):
        parse("∀Phi (Meta(Phi) ∧ Phi(G))")


def test_a_predicate_that_takes_a_lambda_is_a_predicate_of_properties_too():
    # Pos(λx. G(x)) puts a property in Pos's slot, so Pos cannot sit in Meta's slot.
    with pytest.raises(ParsingError, match="fourth order"):
        parse("Meta(Pos) ∧ Pos(λx. G(x))")


def test_the_typing_is_refused_across_formulas_that_are_each_fine_alone():
    # Each formula parses alone: in Meta(Pos) nothing determines the arity of Pos (it defaults to 1),
    # and Pos(G) says Pos takes a property. Together they are the fourth-order typing.
    first, second = parse("Meta(Pos)"), parse("Pos(G)")
    analyse_signatures([first])
    analyse_signatures([second])
    with pytest.raises(ParsingError, match="fourth order") as raised:
        analyse_signatures([first, second])
    assert isinstance(raised.value, nested_error())


@pytest.mark.parametrize("writer", [to_isabelle_to, to_thf_to])
def test_the_third_order_writers_refuse_the_typing_instead_of_writing_an_ill_typed_theory(writer):
    first, second = parse("Meta(Pos)"), parse("Pos(G)")
    with pytest.raises(ParsingError, match="fourth order"):
        writer(first, assumptions=[second])


def test_the_third_order_modal_route_refuses_it_at_parse_time_and_in_the_writers():
    with pytest.raises(ParsingError, match="fourth order"):
        parse_modal("Meta(Pos) ∧ □Pos(G)")
    first, second = parse_modal("Meta(Pos)"), parse_modal("□Pos(G)")
    with pytest.raises(ParsingError, match="fourth order"):
        to_thf_ho_modal(first, axioms=[HoAxiom("a1", second)])
    with pytest.raises(ParsingError, match="fourth order"):
        isabelle_ho_modal_theory("Nested", [HoAxiom("a1", second)], [HoGoal("g", first)])


# ---------------------------------------------------------------------------------------------
# what is still third order is typed as before
# ---------------------------------------------------------------------------------------------

def test_a_predicate_applied_to_individuals_fits_in_a_property_slot():
    # Pos is applied to the individual aa, so it is a property of arity 1: Meta's slot holds it,
    # and Pos's own slot is an individual.
    slots = analyse_signatures([parse("Meta(Pos) ∧ Pos(aa)")]).slots
    assert slots == {"Meta": (("p", 1),), "Pos": ("i",)}


def test_one_property_slot_with_two_occupants_is_typed_by_the_one_that_is_applied():
    slots = analyse_signatures([parse("Pos(G) ∧ Pos(H) ∧ H(aa) ∧ G(bb)")]).slots
    assert slots == {"Pos": (("p", 1),), "H": ("i",), "G": ("i",)}


def test_a_quantified_property_that_is_applied_to_individuals_is_unchanged():
    slots = analyse_signatures([parse("∀Phi (Pos(Phi) → ∃x Phi(x))")]).slots
    assert slots == {"Pos": (("p", 1),), "Phi": ("i",)}


def test_a_lambda_in_a_property_slot_is_unchanged():
    slots = analyse_signatures([parse("Pos(λx. G(x))")]).slots
    assert slots == {"Pos": (("p", 1),), "G": ("i",)}


def test_a_relation_between_two_properties_is_unchanged():
    # Rel takes a property of arity 1 and one of arity 2; neither occupant takes a property.
    slots = analyse_signatures([parse("Rel(G, H) ∧ G(aa) ∧ H(aa, bb)")]).slots
    assert slots == {"Rel": (("p", 1), ("p", 2)), "G": ("i",), "H": ("i", "i")}


def test_the_third_order_writers_still_write_a_third_order_theory():
    formula = parse("Meta(Pos) ∧ Pos(aa)")
    isabelle = to_isabelle_to(formula)
    assert 'consts Meta :: "(i \\<Rightarrow> bool) \\<Rightarrow> bool"' in isabelle
    assert 'consts Pos :: "i \\<Rightarrow> bool"' in isabelle
    thf = to_thf_to(formula)
    assert "( meta : ( $i > $o ) > $o )" in thf
    assert "( pos : $i > $o )" in thf


# ---------------------------------------------------------------------------------------------
# the analysis against a declarative search for a typing
# ---------------------------------------------------------------------------------------------
#
# A typing gives every predicate name an arity and, for each argument slot, a type: "i" (an
# individual) or ("p", k) (a property of individuals of arity k). A list of atoms is consistent
# with a typing iff
#   * every application of X has as many arguments as X has slots;
#   * an individual argument sits in a slot of type "i";
#   * a predicate name Q as an argument sits in a slot ("p", arity of Q), and Q takes only
#     individuals (all its slots are "i"): a property of properties has no slot type;
#   * a λ of depth k sits in a slot ("p", k), and its body L(x) applies L to an individual.
# The analysis must accept exactly the atom lists for which some typing exists.

NAMES = ["A", "B", "C", "D"]
SLOT_TYPES = ["i", ("p", 0), ("p", 1), ("p", 2)]


def _random_atom(rng):
    head = rng.choice(NAMES)
    arguments = []
    for _ in range(rng.choice([0, 1, 1, 2, 2])):
        kind = rng.random()
        if kind < 0.4:
            arguments.append(("individual", rng.choice(["aa", "bb"])))
        elif kind < 0.85:
            arguments.append(("predicate", rng.choice(NAMES)))
        else:
            arguments.append(("lambda", 1))
    return head, arguments


def _text(atom):
    head, arguments = atom
    texts = [value if kind != "lambda" else "λx. L(x)" for kind, value in arguments]
    return f"{head}({', '.join(texts)})" if texts else head


def _consistent(atoms, typing):
    for head, arguments in atoms:
        arity, slots = typing[head]
        if arity != len(arguments):
            return False
        for slot, (kind, value) in zip(slots, arguments):
            if kind == "individual":
                ok = slot == "i"
            elif kind == "predicate":
                occupant_arity, occupant_slots = typing[value]
                ok = slot == ("p", occupant_arity) and all(s == "i" for s in occupant_slots)
            else:
                ok = slot == ("p", value)
            if not ok:
                return False
    return True


def _with_lambda_bodies(atoms):
    uses_lambda = any(kind == "lambda" for _, arguments in atoms for kind, _ in arguments)
    return atoms + [("L", [("individual", "x")])] if uses_lambda else atoms


def _a_typing_exists(atoms):
    atoms = _with_lambda_bodies(atoms)
    names = sorted({head for head, _ in atoms}
                   | {value for _, arguments in atoms for kind, value in arguments
                      if kind == "predicate"})
    applied = {}
    for head, arguments in atoms:
        applied.setdefault(head, set()).add(len(arguments))
    domains = []
    for name in names:
        arities = applied.get(name, {0, 1, 2})
        if len(arities) > 1 and name in applied:
            return False
        domains.append([(arity, slots) for arity in sorted(arities)
                        for slots in itertools.product(SLOT_TYPES, repeat=arity)])
    return any(_consistent(atoms, dict(zip(names, choice)))
               for choice in itertools.product(*domains))


def test_the_analysis_accepts_exactly_the_atom_lists_that_have_a_typing():
    rng = random.Random(20261006)
    accepted = refused = 0
    for _ in range(150):
        atoms = [_random_atom(rng) for _ in range(rng.choice([1, 2, 3, 3, 4]))]
        texts = [_text(atom) for atom in atoms]
        try:
            signatures = analyse_signatures([parse(text) for text in texts])
        except ParsingError:
            assert not _a_typing_exists(atoms), texts
            refused += 1
            continue
        assert _a_typing_exists(atoms), texts
        typing = {name: (len(slots), slots) for name, slots in signatures.slots.items()}
        assert _consistent(_with_lambda_bodies(atoms), typing), (texts, signatures.slots)
        accepted += 1
    assert accepted >= 30 and refused >= 30
