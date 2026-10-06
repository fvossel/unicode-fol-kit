"""``parse_concept(c.to_unicode()) == c`` for every concept the glyph syntax reads.

The reader folds a flat chain of one connective to the LEFT, ``A ⊓ B ⊓ C`` being
``(A ⊓ B) ⊓ C``, and the AST is binary. A chain therefore has one spelling that
keeps its tree: a nested operand of the same connective may stay unparenthesised
on the LEFT only. On the right it needs parentheses, or ``And(A, And(B, C))``
prints ``A ⊓ B ⊓ C`` and reads back as ``And(And(A, B), C)`` -- an equivalent
concept, another tree.

Hand-derived spellings (precedence ``⊔`` < ``⊓`` < ``¬`` / restrictions < names,
each nested operand parenthesised exactly when it binds looser than its slot,
the right operand of the SAME connective counting as looser):

* ``And(And(A, B), C)``  ->  ``A ⊓ B ⊓ C``     (the flat chain)
* ``And(A, And(B, C))``  ->  ``A ⊓ (B ⊓ C)``
* ``Or(A, Or(B, C))``    ->  ``A ⊔ (B ⊔ C)``
* ``Or(A, And(B, C))``   ->  ``A ⊔ B ⊓ C``     (``⊓`` binds tighter)
* ``And(A, Or(B, C))``   ->  ``A ⊓ (B ⊔ C)``
"""

import random

import pytest

import unicode_fol_kit.dl as dl
from unicode_fol_kit.dl.concepts import Concept, InverseRole
from unicode_fol_kit.dl.parser import ConceptSyntaxError, parse_concept

A, B, C, D = dl.Atomic("A"), dl.Atomic("B"), dl.Atomic("C"), dl.Atomic("D")


SPELLINGS = [
    (dl.And(dl.And(A, B), C), "A ⊓ B ⊓ C"),
    (dl.And(A, dl.And(B, C)), "A ⊓ (B ⊓ C)"),
    (dl.Or(dl.Or(A, B), C), "A ⊔ B ⊔ C"),
    (dl.Or(A, dl.Or(B, C)), "A ⊔ (B ⊔ C)"),
    (dl.Or(A, dl.And(B, C)), "A ⊔ B ⊓ C"),
    (dl.And(A, dl.Or(B, C)), "A ⊓ (B ⊔ C)"),
    (dl.Or(dl.And(A, B), dl.And(C, D)), "A ⊓ B ⊔ C ⊓ D"),
    (dl.And(dl.Or(A, B), dl.Or(C, D)), "(A ⊔ B) ⊓ (C ⊔ D)"),
    (dl.And(dl.And(A, B), dl.And(C, D)), "A ⊓ B ⊓ (C ⊓ D)"),
    (dl.Not(dl.And(A, dl.And(B, C))), "¬(A ⊓ (B ⊓ C))"),
    (dl.Exists("r", dl.And(A, dl.And(B, C))), "∃r.(A ⊓ (B ⊓ C))"),
    (dl.And(A, dl.Not(dl.And(B, C))), "A ⊓ ¬(B ⊓ C)"),
    (dl.And(dl.AtLeast(2, "r", A), dl.And(dl.AtMost(1, "r", A), B)), "≥2 r.A ⊓ (≤1 r.A ⊓ B)"),
    (dl.Or(A, dl.Or(B, dl.Or(C, D))), "A ⊔ (B ⊔ (C ⊔ D))"),
]


@pytest.mark.parametrize("concept, text", SPELLINGS, ids=[text for _, text in SPELLINGS])
def test_the_spelling_of_a_nesting_and_its_reading_back(concept, text):
    assert concept.to_unicode() == text
    assert parse_concept(text) == concept


def test_the_flat_chain_reads_left_and_the_parenthesised_one_reads_right():
    # the two trees of A, B, C under one connective are different, and each has its text
    assert parse_concept("A ⊓ B ⊓ C") == dl.And(dl.And(A, B), C)
    assert parse_concept("A ⊓ (B ⊓ C)") == dl.And(A, dl.And(B, C))
    assert parse_concept("A ⊔ B ⊔ C") == dl.Or(dl.Or(A, B), C)
    assert parse_concept("A ⊔ (B ⊔ C)") == dl.Or(A, dl.Or(B, C))
    assert dl.And(dl.And(A, B), C).to_unicode() != dl.And(A, dl.And(B, C)).to_unicode()
    assert dl.Or(dl.Or(A, B), C).to_unicode() != dl.Or(A, dl.Or(B, C)).to_unicode()


# --------------------------------------------------------------------------- #
# Every constructor the printer knows, as the root and in every child slot.
# --------------------------------------------------------------------------- #

#: The constructors the glyph reader reads back, by the name of their class.
READABLE = {"Top", "Bottom", "Atomic", "Not", "And", "Or", "Exists", "ForAll", "AtLeast", "AtMost"}
#: Printed by ``to_unicode`` and refused BY NAME by ``parse_concept``: the glyph
#: syntax has no individual-name layer and no data-range layer.
RENDER_ONLY = {"Nominal", "HasValue", "DataExists", "DataForAll", "DataHasValue", "DataAtLeast",
               "DataAtMost"}


def _one_per_constructor(x, y):
    """One expression of each readable constructor, over the operands ``x`` and ``y``."""
    return {
        "Top": dl.Top(),
        "Bottom": dl.Bottom(),
        "Atomic": x,
        "Not": dl.Not(x),
        "And": dl.And(x, y),
        "Or": dl.Or(x, y),
        "Exists": dl.Exists("r", x),
        "ForAll": dl.ForAll("r", x),
        "AtLeast": dl.AtLeast(2, "r", x),
        "AtMost": dl.AtMost(1, "r", x),
    }


def test_the_enumeration_covers_every_class_expression_constructor():
    # a constructor added to dl.concepts without a line here fails this test, instead
    # of silently escaping the round trip
    def subclasses(cls):
        for sub in cls.__subclasses__():
            yield sub
            yield from subclasses(sub)

    known = {cls.__name__ for cls in subclasses(Concept)}
    assert known == READABLE | RENDER_ONLY
    assert set(_one_per_constructor(A, B)) == READABLE


_SLOT_CASES = []
for _root in sorted(READABLE - {"Top", "Bottom", "Atomic"}):
    for _child in sorted(READABLE):
        for _slot in (("left", "right") if _root in ("And", "Or") else ("only",)):
            _SLOT_CASES.append((_root, _child, _slot))


@pytest.mark.parametrize("root, child, slot", _SLOT_CASES,
                         ids=["-".join(case) for case in _SLOT_CASES])
def test_every_constructor_reads_back_as_itself_in_every_child_slot(root, child, slot):
    operand = _one_per_constructor(A, B)[child]
    x, y = (operand, B) if slot in ("left", "only") else (A, operand)
    concept = _one_per_constructor(x, y)[root]
    text = concept.to_unicode()
    assert parse_concept(text) == concept, text


def _random_concept(rng, depth):
    if depth == 0 or rng.random() < 0.15:
        return rng.choice([A, B, dl.Top(), dl.Bottom()])
    kind = rng.choice(["Not", "And", "And", "Or", "Or", "Exists", "ForAll", "AtLeast", "AtMost"])
    x, y = _random_concept(rng, depth - 1), _random_concept(rng, depth - 1)
    role = rng.choice(["r", "hasChild", "s2"])
    if kind == "Not":
        return dl.Not(x)
    if kind == "And":
        return dl.And(x, y)
    if kind == "Or":
        return dl.Or(x, y)
    if kind == "Exists":
        return dl.Exists(role, x)
    if kind == "ForAll":
        return dl.ForAll(role, x)
    if kind == "AtLeast":
        return dl.AtLeast(rng.randint(0, 3), role, x)
    return dl.AtMost(rng.randint(0, 3), role, x)


def test_random_nestings_read_back_as_the_same_tree():
    # exact equality, not render-idempotence: right-nested chains are in the sample
    rng = random.Random(20260705)
    right_nested = 0
    for _ in range(400):
        concept = _random_concept(rng, 5)
        text = concept.to_unicode()
        assert parse_concept(text) == concept, text
        right_nested += "⊓ (" in text or "⊔ (" in text
    assert right_nested > 50       # the sample does contain the shapes that used to misread


@pytest.mark.parametrize("concept", [
    dl.Nominal("a"),
    dl.HasValue("r", "a"),
    dl.DataExists("d", dl.Datatype("xsd:integer")),
    dl.DataHasValue("d", dl.Literal("5", "xsd:integer")),
    dl.DataAtLeast(1, "d", dl.Datatype("xsd:integer")),
])
def test_a_constructor_the_glyph_syntax_cannot_read_is_printed_and_refused(concept):
    with pytest.raises(ConceptSyntaxError):
        parse_concept(concept.to_unicode())


# --------------------------------------------------------------------------- #
# An inverse role prints as r⁻ and is not read back as a role of that name.
# --------------------------------------------------------------------------- #

def test_an_inverse_role_is_printed_and_the_reader_refuses_the_text():
    # ``∃r⁻.A`` read as a role NAMED "r⁻" would be a plain role, which is a
    # different concept (and in the FOL image a different predicate)
    concept = dl.Exists(InverseRole("r"), A)
    assert concept.to_unicode() == "∃r⁻.A"
    with pytest.raises(ConceptSyntaxError, match="INVERSE"):
        parse_concept("∃r⁻.A")


@pytest.mark.parametrize("text", ["∀r⁻.A", "≥2 r⁻.A", "≤1 r⁻.A", "A ⊓ ∃r⁻.B"])
def test_a_role_name_ending_in_the_inverse_glyph_is_refused_in_every_restriction(text):
    with pytest.raises(ConceptSyntaxError, match="INVERSE"):
        parse_concept(text)


def test_the_inverse_glyph_inside_a_class_name_is_still_a_name():
    assert parse_concept("A⁻ ⊓ ∃r.B⁻") == dl.And(dl.Atomic("A⁻"), dl.Exists("r", dl.Atomic("B⁻")))


# --------------------------------------------------------------------------- #
# Names: a text that would read back as ANOTHER concept is not printed.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("concept, reads_as", [
    # "A ⊓ B ⊓ C" is the intersection of three classes
    (dl.And(dl.Atomic("A ⊓ B"), C), dl.And(dl.And(A, B), C)),
    # "¬a" is the complement of the class a
    (dl.Atomic("¬a"), dl.Not(dl.Atomic("a"))),
    (dl.Atomic("⊤"), dl.Top()),
    (dl.Atomic("⊥"), dl.Bottom()),
    # "¬a ⊔ b": the complement binds tighter than the union, so it is (¬a) ⊔ b
    (dl.Not(dl.Atomic("a ⊔ b")), dl.Or(dl.Not(dl.Atomic("a")), dl.Atomic("b"))),
    # a role name that closes its own restriction: "∃a .⊤ ⊓ ∃b.B" is two restrictions
    (dl.Exists("a .⊤ ⊓ ∃b", B), dl.And(dl.Exists("a", dl.Top()), dl.Exists("b", B))),
])
def test_a_name_that_reads_back_as_another_concept_is_refused(concept, reads_as):
    # the display form still shows the text, and the reader does read that text as `reads_as`
    assert parse_concept(str(concept)) == reads_as
    with pytest.raises(ValueError, match="reads back as"):
        concept.to_unicode()


def test_str_is_display_only_and_never_raises():
    concept = dl.And(dl.Atomic("A ⊓ B"), C)
    assert str(concept) == "A ⊓ B ⊓ C"


@pytest.mark.parametrize("concept", [
    dl.Atomic("a b"),                          # whitespace: the reader refuses the text
    dl.Atomic("http://x.org/A"),               # a dot: the reader refuses the text
    dl.Exists("http://x.org/r", dl.Atomic("http://x.org/A")),
    dl.Atomic("f(x)"),                         # parentheses
    dl.Atomic(""),
])
def test_a_name_the_reader_refuses_is_printed_as_it_is(concept):
    # nothing reads this text as another concept, so it is a display text, as it was
    text = concept.to_unicode()
    assert text == str(concept)
    with pytest.raises(ConceptSyntaxError):
        parse_concept(text)


def test_an_ordinary_name_reads_back_without_asking_the_reader():
    # names of ordinary characters, including non-ASCII ones and digits
    for concept in (dl.Atomic("Person"), dl.Atomic("θ"), dl.Atomic("A_1"), dl.Atomic("42"),
                    dl.Exists("hasChild", dl.Atomic("Doctor42"))):
        assert parse_concept(concept.to_unicode()) == concept
