"""Tests for the OWL 2 Manchester Syntax parser/renderer, ALC fragment
(unicode_fol_kit.dl.owl_manchester).

Round-trip is the primary correctness property, exactly as in
tests/test_dl_parser.py for the glyph syntax: `parse_manchester(to_manchester(c))
== c` must hold for every constructor and every precedence-sensitive nesting.
Each precedence case below is worked out by hand against the W3C grammar's
own stated resolution rule ("later productions... bind more tightly": `or` >
`and` > `not`/restrictions(`some`/`only`) > atomic) -- see
https://www.w3.org/TR/owl2-manchester-syntax/#Class_Expressions -- which is
exactly the lattice unicode_fol_kit.dl.concepts._PREC already uses
(Or=1 < And=2 < Not=Exists=ForAll=3 < Atomic=4), so parser and renderer here
apply the identical resolution/parenthesisation rule as the existing glyph
parser, just spelling operators as keywords.

Every rejection test below exercises real OWL 2 Manchester Syntax that is
NOT ALC-expressible (cardinalities, value/Self restrictions, inverse roles,
nominals, datatype facets); the kit's honesty convention requires a loud,
precise ValueError naming the construct rather than a silent
mistranslation, so each test asserts the offending construct's name (not
just "some error") appears in the message.
"""

import pytest

import unicode_fol_kit.dl as dl
from unicode_fol_kit.dl.owl_manchester import (
    parse_manchester, to_manchester, parse_manchester_axiom, ManchesterSyntaxError,
)

A, B, C = dl.Atomic("A"), dl.Atomic("B"), dl.Atomic("C")


# --------------------------------------------------------------------------- #
# Round-trip: one case per constructor.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("concept", [
    dl.Top(),
    dl.Bottom(),
    dl.Atomic("Person"),
    dl.Not(A),
    dl.And(A, B),
    dl.Or(A, B),
    dl.Exists("r", A),
    dl.ForAll("r", A),
], ids=lambda c: c.to_unicode())
def test_round_trip_one_case_per_constructor(concept):
    rendered = to_manchester(concept)
    assert parse_manchester(rendered) == concept


def test_top_and_bottom_render_as_owl_prefixed_names():
    # owl:Thing / owl:Nothing are the W3C spelling for the universal/empty
    # class -- see the module docstring's "Top and Bottom".
    assert to_manchester(dl.Top()) == "owl:Thing"
    assert to_manchester(dl.Bottom()) == "owl:Nothing"


# --------------------------------------------------------------------------- #
# Round-trip: precedence-sensitive nesting, hand-resolved against the W3C
# grammar's binding order (or < and < not/some/only < atomic).
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("concept, rendered", [
    # not not A: 'not' recurses into 'primary', which can itself be 'not
    # primary' again -- no parens needed since Not's own precedence (3)
    # never triggers Not's paren threshold (3 < 3 is false).
    (dl.Not(dl.Not(A)), "not not A"),
    (dl.Not(dl.Not(dl.Not(A))), "not not not A"),
    # r some s only A: a restriction filler is itself 'primary', so nested
    # restrictions chain with no parens (mirrors ∃r.∀s.A in the glyph parser).
    (dl.Exists("r", dl.ForAll("s", A)), "r some s only A"),
    (dl.Exists("r", dl.Exists("s", dl.Exists("t", A))), "r some s some t some A"),
    # r some (A and not B): the restriction filler A ⊓ ¬B has precedence 2
    # (And), which is below the filler slot's threshold of 3, so it needs
    # parens -- the module docstring's own worked example.
    (dl.Exists("r", dl.And(A, dl.Not(B))), "r some (A and not B)"),
    (dl.Exists("hasChild", dl.And(dl.Atomic("Doctor"), dl.Not(dl.Atomic("Rich")))),
     "hasChild some (Doctor and not Rich)"),
    # (A or B) and C: Or has precedence 1, below And's operand threshold of
    # 2, so the left 'and' operand needs parens.
    (dl.And(dl.Or(A, B), C), "(A or B) and C"),
    # A and B or C: And (prec 2) sits fine unparenthesised inside Or's
    # threshold of 1 (2 < 1 is false) -- 'and' already binds tighter, so no
    # parens are needed for parse_manchester to recover the same tree.
    (dl.Or(dl.And(A, B), C), "A and B or C"),
    # not (A and B): And's precedence (2) is below Not's operand threshold
    # (3), so it needs parens -- otherwise 'not A and B' would (correctly)
    # parse back as (not A) and B, a different tree.
    (dl.Not(dl.And(A, B)), "not (A and B)"),
    # not r some A: Exists's precedence (3) is NOT below Not's threshold
    # (3), so no parens -- 'not' scopes over the whole restriction. This is
    # the ARBEITSKONTEXT precedence dispute: 'not' binds WEAKER than
    # 'some', so this is ¬∃r.A, never "(not r) some A" (which isn't even a
    # legal parse -- 'not' can only prefix a 'primary', and a bare role name
    # is not one).
    (dl.Not(dl.Exists("r", A)), "not r some A"),
    (dl.Exists("r", dl.Not(dl.And(A, B))), "r some not (A and B)"),
    (dl.ForAll("r", dl.Exists("s", dl.Or(A, dl.Not(B)))), "r only s some (A or not B)"),
    # (r some A) and (r only not A): both conjuncts are restrictions (prec
    # 3), which never trips And's threshold of 2 -- siblings, no outer parens.
    (dl.And(dl.Exists("r", A), dl.ForAll("r", dl.Not(A))), "r some A and r only not A"),
    # Chained same-precedence operators fold LEFT in the AST (the W3C
    # grammar's 'primary (and primary)*' / 'conjunction (or conjunction)*'
    # productions are flat lists over a binary AST) -- mirrors
    # test_dl_parser.py's identical claim for the glyph syntax.
    (dl.Or(dl.Or(dl.Not(A), B), C), "not A or B or C"),
    (dl.And(dl.And(dl.Not(A), B), C), "not A and B and C"),
    (dl.And(dl.Top(), dl.Or(dl.Bottom(), A)), "owl:Thing and (owl:Nothing or A)"),
], ids=lambda x: x if isinstance(x, str) else None)
def test_round_trip_precedence_cases(concept, rendered):
    assert to_manchester(concept) == rendered
    assert parse_manchester(rendered) == concept


def test_and_binds_tighter_than_or_across_a_restriction():
    # "A and r some B or C" -- restrictions ('some') bind tighter than
    # 'and', which binds tighter than 'or' (W3C: "p some a and p only b is
    # parsed as (p some a) and (p only b)"). So this is
    # (A and (r some B)) or C, not A and ((r some B) or C).
    got = parse_manchester("A and r some B or C")
    assert got == dl.Or(dl.And(A, dl.Exists("r", B)), C)


def test_not_binds_weaker_than_some():
    # "not r some A": 'not' is a prefix on the WHOLE 'primary' production,
    # and a restriction ('r some A') is itself a 'primary' -- so 'not'
    # scopes over the entire restriction: ¬∃r.A. There is no reading where
    # 'not' applies to the bare role 'r' alone ("(not r) some A"), because
    # 'not' can only ever prefix a primary (restriction|atomic), and a role
    # name standing alone is neither.
    got = parse_manchester("not r some A")
    assert got == dl.Not(dl.Exists("r", A))


def test_explicit_redundant_parens_are_accepted():
    assert parse_manchester("(A)") == A
    assert parse_manchester("((A))") == A
    assert parse_manchester("(A and B) and C") == dl.And(dl.And(A, B), C)
    assert parse_manchester("A and (B and C)") == dl.And(A, dl.And(B, C))
    # These two differ structurally despite being classically equivalent.
    assert parse_manchester("(A and B) and C") != parse_manchester("A and (B and C)")


def test_whitespace_between_tokens_is_insignificant():
    assert parse_manchester("A   and   B") == dl.And(A, B)
    assert parse_manchester("r   some   A") == dl.Exists("r", A)


# --------------------------------------------------------------------------- #
# Rejections: real Manchester/OWL 2 syntax outside the ALC fragment. Every
# case names its construct explicitly in the raised message.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("text, needle", [
    ("r min 2 C", "min"),          # cardinality: at least 2 r-successors in C
    ("r max 3 C", "max"),          # cardinality: at most 3
    ("r exactly 1 C", "exactly"),  # cardinality: exactly 1
])
def test_cardinality_restrictions_are_rejected(text, needle):
    with pytest.raises(ManchesterSyntaxError) as exc:
        parse_manchester(text)
    msg = str(exc.value)
    assert "cardinality" in msg
    assert needle in msg


def test_value_restriction_is_rejected():
    with pytest.raises(ManchesterSyntaxError) as exc:
        parse_manchester("hasFriend value John")
    assert "value" in str(exc.value)


def test_self_restriction_is_rejected():
    with pytest.raises(ManchesterSyntaxError) as exc:
        parse_manchester("hasChild Self")
    assert "Self" in str(exc.value)


def test_nominal_concept_is_rejected():
    with pytest.raises(ManchesterSyntaxError) as exc:
        parse_manchester("{a, b}")
    msg = str(exc.value)
    assert "nominal" in msg
    assert "{" in msg


def test_inverse_role_is_rejected():
    with pytest.raises(ManchesterSyntaxError) as exc:
        parse_manchester("inverse hasChild some Person")
    assert "inverse" in str(exc.value)


def test_datatype_facet_restriction_is_rejected():
    with pytest.raises(ManchesterSyntaxError) as exc:
        parse_manchester("hasAge some xsd:integer[>= 18]")
    msg = str(exc.value)
    assert "facet" in msg or "datatype" in msg


# --------------------------------------------------------------------------- #
# Sensible errors on malformed input (mirrors test_dl_parser.py's coverage).
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("text", [
    "",                # empty input
    "(A",              # unbalanced: missing ')'
    "A)",              # unbalanced: stray ')'
    "A and",           # missing right operand
    "and A",           # missing left operand / stray keyword
    "A B",             # two concepts with no connective between them
    "A and (B",        # unbalanced inside a subexpression
    "not",             # missing operand for negation
    "r some (A",       # unbalanced after a restriction
    "r some",          # missing filler
])
def test_malformed_input_raises_manchester_syntax_error(text):
    with pytest.raises(ManchesterSyntaxError):
        parse_manchester(text)


def test_error_message_is_informative():
    with pytest.raises(ManchesterSyntaxError, match="position"):
        parse_manchester("A and")


# --------------------------------------------------------------------------- #
# parse_manchester_axiom: "C SubClassOf D" -> ("subclass", C, D);
# "C EquivalentTo D" -> ("equivalent", C, D).
# --------------------------------------------------------------------------- #

def test_parse_axiom_subclass():
    got = parse_manchester_axiom("Doctor SubClassOf Person")
    assert got == ("subclass", dl.Atomic("Doctor"), dl.Atomic("Person"))


def test_parse_axiom_equivalent_with_restriction():
    got = parse_manchester_axiom("Doctor EquivalentTo Person and hasChild some Doctor")
    expected = ("equivalent", dl.Atomic("Doctor"),
                dl.And(dl.Atomic("Person"), dl.Exists("hasChild", dl.Atomic("Doctor"))))
    assert got == expected


def test_parse_axiom_accepts_optional_trailing_colon():
    # The W3C frame header is colon-terminated ("SubClassOf:"); this module
    # accepts both spellings identically (see the module docstring).
    with_colon = parse_manchester_axiom("Doctor SubClassOf: Person")
    without_colon = parse_manchester_axiom("Doctor SubClassOf Person")
    assert with_colon == without_colon


def test_parse_axiom_top_and_bottom():
    got = parse_manchester_axiom("owl:Nothing SubClassOf owl:Thing")
    assert got == ("subclass", dl.Bottom(), dl.Top())


@pytest.mark.parametrize("text", [
    "Doctor",                              # no keyword at all
    "SubClassOf Person",                   # missing left-hand side
    "Doctor SubClassOf",                   # missing right-hand side
    "A SubClassOf B SubClassOf C",         # two keywords -- no chaining
    "A SubClassOf (B",                     # unbalanced on the right side
])
def test_parse_axiom_malformed_raises(text):
    with pytest.raises(ManchesterSyntaxError):
        parse_manchester_axiom(text)


# --------------------------------------------------------------------------- #
# Integration: parse_manchester feeds directly into the existing ALC tableau.
# --------------------------------------------------------------------------- #

def test_parsed_concept_feeds_the_tableau_unsatisfiable():
    # "A and not A" is the textbook clash: {x:A, x:¬A} is a clash by
    # definition (tableau.py's _clash), so it is unsatisfiable in EVERY
    # model, independent of any TBox.
    concept = parse_manchester("A and not A")
    assert dl.concept_satisfiable(concept) is False


def test_parsed_concept_feeds_the_tableau_satisfiable():
    concept = parse_manchester("A or not A")
    assert dl.concept_satisfiable(concept) is True


def test_parsed_concept_matches_hand_checked_tableau_clash():
    # Same shape as test_dl_alc.py's hand-checked case:
    # (∃r.A ⊓ ∀r.¬A, False) -- "∃r.A ⊓ ∀r.¬A clashes": any r-successor
    # forced into both A (by the ∃) and ¬A (by the ∀ on that same
    # successor) is itself a clash, so no model exists.
    concept = parse_manchester("r some A and r only not A")
    assert concept == dl.And(dl.Exists("r", A), dl.ForAll("r", dl.Not(A)))
    assert dl.concept_satisfiable(concept) is False
