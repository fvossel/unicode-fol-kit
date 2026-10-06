"""``parse_manchester(to_manchester(c)) == c`` for every class-expression constructor.

The W3C grammar writes a conjunction (a disjunction) as a FLAT chain,
``primary ('and' primary)*``, and the kit's AST is binary, so the reader folds a
chain of three or more to the LEFT: ``A and B and C`` is ``(A and B) and C``. The
printer therefore has one way to write a chain without changing the tree: a nested
operand of the same connective may stay unparenthesised on the LEFT only. On the
right it needs parentheses, or ``And(A, And(B, C))`` prints ``A and B and C`` and
reads back as ``And(And(A, B), C)`` — an equivalent concept, another tree.

Hand-derived spellings (precedence ``or`` < ``and`` < ``not``/restrictions <
names, each nested operand parenthesised exactly when it binds looser than its
slot, a right operand of the SAME connective counting as looser):

* ``And(And(A, B), C)``           ->  ``A and B and C``        (the flat chain)
* ``And(A, And(B, C))``           ->  ``A and (B and C)``
* ``Or(A, Or(B, C))``             ->  ``A or (B or C)``
* ``Or(A, And(B, C))``            ->  ``A or B and C``         (``and`` binds tighter)
* ``And(A, Or(B, C))``            ->  ``A and (B or C)``
"""

import random

import pytest

import unicode_fol_kit.dl as dl
from unicode_fol_kit.dl import datatypes as dt
from unicode_fol_kit.dl.concepts import Concept
from unicode_fol_kit.dl.owl_manchester import (
    ManchesterSyntaxError, parse_manchester, to_manchester,
)

A, B, C, D = dl.Atomic("A"), dl.Atomic("B"), dl.Atomic("C"), dl.Atomic("D")


SPELLINGS = [
    (dl.And(dl.And(A, B), C), "A and B and C"),
    (dl.And(A, dl.And(B, C)), "A and (B and C)"),
    (dl.Or(dl.Or(A, B), C), "A or B or C"),
    (dl.Or(A, dl.Or(B, C)), "A or (B or C)"),
    (dl.Or(A, dl.And(B, C)), "A or B and C"),
    (dl.And(A, dl.Or(B, C)), "A and (B or C)"),
    (dl.Or(dl.And(A, B), dl.And(C, D)), "A and B or C and D"),
    (dl.And(dl.Or(A, B), dl.Or(C, D)), "(A or B) and (C or D)"),
    (dl.And(dl.And(A, B), dl.And(C, D)), "A and B and (C and D)"),
    (dl.Not(dl.And(A, dl.And(B, C))), "not (A and (B and C))"),
    (dl.Exists("r", dl.And(A, dl.And(B, C))), "r some (A and (B and C))"),
    (dl.And(A, dl.Not(dl.And(B, C))), "A and not (B and C)"),
    (dl.And(dl.AtLeast(2, "r", A), dl.And(dl.AtMost(1, "r", A), B)),
     "r min 2 A and (r max 1 A and B)"),
    (dl.And(dl.AtLeast(2, "r", dl.Top()), dl.And(B, C)), "r min 2 and (B and C)"),
]


@pytest.mark.parametrize("concept, text", SPELLINGS, ids=[text for _, text in SPELLINGS])
def test_the_spelling_of_a_nesting_and_its_reading_back(concept, text):
    assert to_manchester(concept) == text
    assert parse_manchester(text) == concept


def test_the_flat_chain_reads_left_and_the_parenthesised_one_reads_right():
    # the two trees of A, B, C under ``and`` are different, and each has its text
    assert parse_manchester("A and B and C") == dl.And(dl.And(A, B), C)
    assert parse_manchester("A and (B and C)") == dl.And(A, dl.And(B, C))
    assert parse_manchester("A or B or C") == dl.Or(dl.Or(A, B), C)
    assert parse_manchester("A or (B or C)") == dl.Or(A, dl.Or(B, C))


# --------------------------------------------------------------------------- #
# Every constructor the printer knows, as the root and in every child slot.
# --------------------------------------------------------------------------- #

INT, STRING, DECIMAL = dt.Datatype("xsd:integer"), dt.Datatype("xsd:string"), dt.Datatype("xsd:decimal")


def _integer(n):
    return dt.Literal(str(n), "xsd:integer")


#: Data ranges of every shape, plain and compound, for the data restrictions.
DATA_RANGES = [
    INT,
    dt.DatatypeRestriction(INT, (("xsd:minInclusive", _integer(1)), ("xsd:maxExclusive", _integer(9)))),
    dt.DataOneOf((_integer(1), _integer(2))),
    dt.DataComplementOf(INT),
    dt.DataIntersectionOf((INT, STRING)),
    dt.DataUnionOf((INT, STRING)),
    dt.DataUnionOf((INT, STRING, DECIMAL)),
    dt.DataIntersectionOf((dt.DataUnionOf((INT, STRING)), dt.DataComplementOf(DECIMAL))),
]

#: The constructors a reader reads back, by the name of their class. Every
#: ``Concept`` subclass is either here or in ``RENDER_ONLY``.
READABLE = {
    "Top", "Bottom", "Atomic", "Not", "And", "Or", "Exists", "ForAll", "AtLeast",
    "AtMost", "HasValue", "DataExists", "DataForAll", "DataHasValue", "DataAtLeast",
    "DataAtMost",
}
#: Printed by ``to_manchester``, refused by name by ``parse_manchester``: reading
#: either back would admit what the ALCHQ reader keeps out.
RENDER_ONLY = {"Nominal"}


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
        "HasValue": dl.HasValue("r", "a"),
        "DataExists": dl.DataExists("d", DATA_RANGES[3]),
        "DataForAll": dl.DataForAll("d", DATA_RANGES[7]),
        "DataHasValue": dl.DataHasValue("d", _integer(5)),
        "DataAtLeast": dl.DataAtLeast(2, "d", DATA_RANGES[1]),
        "DataAtMost": dl.DataAtMost(1, "d", INT),
    }


def test_the_enumeration_covers_every_class_expression_constructor():
    # A constructor added to dl.concepts without a line in _one_per_constructor (or
    # in RENDER_ONLY) fails here, instead of silently escaping the round trip.
    def subclasses(cls):
        for sub in cls.__subclasses__():
            yield sub
            yield from subclasses(sub)

    known = {cls.__name__ for cls in subclasses(Concept)}
    assert known == READABLE | RENDER_ONLY
    assert set(_one_per_constructor(A, B)) == READABLE


_SLOT_CASES = []
for _root in sorted(set(READABLE) - {"Top", "Bottom", "Atomic"}):
    for _child in sorted(READABLE):
        for _slot in (("left", "right") if _root in ("And", "Or") else ("only",)):
            _SLOT_CASES.append((_root, _child, _slot))


@pytest.mark.parametrize("root, child, slot", _SLOT_CASES,
                         ids=["-".join(case) for case in _SLOT_CASES])
def test_every_constructor_reads_back_as_itself_in_every_child_slot(root, child, slot):
    # ``root`` over a ``child`` in each of its operand slots, the other operand an
    # atom: 13 roots x 16 children, both sides of the two binary connectives.
    operand = _one_per_constructor(A, B)[child]
    x, y = (operand, B) if slot in ("left", "only") else (A, operand)
    concept = _one_per_constructor(x, y)[root]
    text = to_manchester(concept)
    assert parse_manchester(text) == concept, text


def _random_concept(rng, depth):
    """A random readable class expression; roles, properties and individuals from
    small fixed lists, so that ``rng`` alone decides the tree."""
    if depth == 0 or rng.random() < 0.15:
        return rng.choice([A, B, dl.Top(), dl.Bottom()])
    kind = rng.choice(["Not", "And", "And", "Or", "Or", "Exists", "ForAll", "HasValue",
                       "AtLeast", "AtMost", "DataExists", "DataForAll", "DataHasValue",
                       "DataAtLeast", "DataAtMost"])
    x = _random_concept(rng, depth - 1)
    y = _random_concept(rng, depth - 1)
    role, prop = rng.choice(["r", "s"]), rng.choice(["d", "e"])
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
    if kind == "HasValue":
        return dl.HasValue(role, rng.choice(["a", "b"]))
    if kind == "AtLeast":
        return dl.AtLeast(rng.randint(0, 3), role, x)
    if kind == "AtMost":
        return dl.AtMost(rng.randint(0, 3), role, x)
    data_range = rng.choice(DATA_RANGES)
    if kind == "DataExists":
        return dl.DataExists(prop, data_range)
    if kind == "DataForAll":
        return dl.DataForAll(prop, data_range)
    if kind == "DataHasValue":
        return dl.DataHasValue(prop, _integer(rng.randint(0, 9)))
    if kind == "DataAtLeast":
        return dl.DataAtLeast(rng.randint(0, 3), prop, data_range)
    return dl.DataAtMost(rng.randint(0, 3), prop, data_range)


def _subexpressions(concept):
    """``concept`` and every class expression nested in it."""
    yield concept
    for name in ("concept", "left", "right"):
        child = getattr(concept, name, None)
        if isinstance(child, Concept):
            yield from _subexpressions(child)


def _nests_its_own_connective_on_the_right(concept):
    return any(isinstance(inner, (dl.And, dl.Or)) and isinstance(inner.right, type(inner))
               for inner in _subexpressions(concept))


def test_random_expressions_over_every_constructor_read_back_as_themselves():
    rng = random.Random(20261004)
    nested = 0
    for _ in range(2000):
        concept = _random_concept(rng, 4)
        text = to_manchester(concept)
        assert parse_manchester(text) == concept, text
        nested += _nests_its_own_connective_on_the_right(concept)
    # the battery reaches the case this file is about, many times over
    assert nested >= 100


# --------------------------------------------------------------------------- #
# The constructors the printer writes and the reader refuses.
# --------------------------------------------------------------------------- #

def test_a_nominal_and_an_inverse_role_print_and_are_refused_by_name_on_the_way_back():
    nominal = dl.Nominal("a")
    inverse = dl.Exists(dl.InverseRole("r"), A)
    assert to_manchester(nominal) == "{a}"
    assert to_manchester(inverse) == "inverse r some A"
    with pytest.raises(ManchesterSyntaxError, match="nominal"):
        parse_manchester("{a}")
    with pytest.raises(ManchesterSyntaxError, match="inverse"):
        parse_manchester("inverse r some A")
    # and the nesting rule holds for them as operands
    assert to_manchester(dl.And(A, dl.And(nominal, B))) == "A and ({a} and B)"
