"""Tests for the OWL 2 Manchester Syntax parser/renderer, ALCHQ fragment
(unicode_logic_kit.dl.owl_manchester).

Round-trip is the primary correctness property, exactly as in
tests/test_dl_parser.py for the glyph syntax: `parse_manchester(to_manchester(c))
== c` must hold for every constructor and every precedence-sensitive nesting.
Each precedence case below is worked out by hand against the W3C grammar's
own stated resolution rule ("later productions... bind more tightly": `or` >
`and` > `not`/restrictions(`some`/`only`) > atomic) -- see
https://www.w3.org/TR/owl2-manchester-syntax/#Class_Expressions -- which is
exactly the lattice unicode_logic_kit.dl.concepts._PREC already uses
(Or=1 < And=2 < Not=Exists=ForAll=3 < Atomic=4), so parser and renderer here
apply the identical resolution/parenthesisation rule as the existing glyph
parser, just spelling operators as keywords.

Qualified cardinalities are ALCQ and parse to number restrictions. Every
rejection test below exercises real OWL 2 Manchester Syntax outside the
supported fragment (value/Self restrictions, inverse roles, nominals, datatype
facets); the kit's honesty convention requires a loud, precise ValueError
naming the construct rather than a silent mistranslation, so each test asserts
the offending construct's name (not just "some error") appears in the message.
"""

import pytest

import unicode_logic_kit.dl as dl
from unicode_logic_kit.dl.owl_manchester import (
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
# Cardinalities, then rejections: real Manchester/OWL 2 syntax outside the
# supported fragment. Every rejection names its construct in the message.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("text, expected", [
    # Qualified number restrictions are ALCQ, supported since the tableau learned
    # them; `exactly n` is the conjunction of `min n` and `max n`, and an omitted
    # filler is owl:Thing.
    ("r min 2 C", dl.AtLeast(2, "r", dl.Atomic("C"))),
    ("r max 3 C", dl.AtMost(3, "r", dl.Atomic("C"))),
    ("r exactly 1 C", dl.And(dl.AtLeast(1, "r", dl.Atomic("C")),
                             dl.AtMost(1, "r", dl.Atomic("C")))),
    ("r min 2", dl.AtLeast(2, "r", dl.Top())),
])
def test_cardinality_restrictions_parse_to_number_restrictions(text, expected):
    assert parse_manchester(text) == expected
    assert parse_manchester(to_manchester(expected)) == expected


def test_value_restriction_parses_to_has_value():
    # `r value a` is read since 0.30.0: ObjectHasValue(r a) is an axiom KIND the
    # kit carries (the in-house tableau refuses it by name, as a nominal in
    # disguise; the FOL image and the external reasoner decide it), and a
    # parser never refuses a kind a later route can answer. The round trip and
    # the still-refused `r some {a}` sibling are in
    # tests/test_dl_has_value.py; this is the former refusal's place-holder, so
    # the change of behaviour is visible where the old assertion stood.
    assert parse_manchester("hasFriend value John") == dl.HasValue("hasFriend", "John")
    assert to_manchester(dl.HasValue("hasFriend", "John")) == "hasFriend value John"


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


def test_datatype_facet_restriction_is_read_when_it_has_an_image():
    # Until the data layer this was refused. An ordering facet on an exact-number
    # base has a first-order image (a comparison atom), so it is READ: the
    # restriction keeps its facets as written, `>=` being xsd:minInclusive.
    assert parse_manchester("hasAge some xsd:integer[>= 18]") == dl.DataExists(
        "hasAge", dl.DatatypeRestriction(
            dl.Datatype("xsd:integer"),
            (("xsd:minInclusive", dl.Literal("18", "xsd:integer")),)))


@pytest.mark.parametrize("text, facet", [
    ('hasName some xsd:string[length 3]', "xsd:length"),
    ('hasName some xsd:string[pattern "a+"]', "xsd:pattern"),
    ('hasName some xsd:string[>= "a"]', "xsd:minInclusive"),
])
def test_a_facet_without_a_first_order_image_is_refused_by_name(text, facet):
    # String length and regular expressions are not first-order, and an
    # ordering facet on a non-numeric base has no order to compare by: the
    # reader names the facet instead of keeping an axiom that constrains nothing.
    with pytest.raises(ManchesterSyntaxError) as exc:
        parse_manchester(text)
    assert facet in str(exc.value)


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


# --------------------------------------------------------------------------- #
# role_axiom_to_manchester never writes text the reader would not take back.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("axiom", [
    ("subproperty", "r", dl.InverseRole("s")),
    ("subproperty", dl.InverseRole("r"), "s"),
    ("domain", dl.InverseRole("r"), A),
    ("functional", dl.InverseRole("r")),
])
def test_an_inverse_role_has_no_one_line_spelling_and_is_refused_by_name(axiom):
    # The reader (parse_manchester_role_axiom) takes a role NAME in every slot
    # and has no `inverse` spelling for a role axiom, so the only text the writer
    # could produce for an InverseRole is its dataclass repr,
    # "r SubPropertyOf InverseRole(role='s')" -- which reads back as a role
    # literally named "InverseRole(role='s')". A ValueError naming the role and
    # the remedy (dl.to_owl_functional writes ObjectInverseOf) is the honest
    # answer; the old behaviour printed the repr.
    with pytest.raises(ValueError, match="role NAME") as caught:
        dl.role_axiom_to_manchester(*axiom)
    assert "ObjectInverseOf" in str(caught.value)


@pytest.mark.parametrize("axiom", [
    ("subproperty", "r", "owl:topObjectProperty"),
    ("subproperty", "owl:bottomObjectProperty", "s"),
    ("functional", "owl:topObjectProperty"),
    ("range", "owl:bottomObjectProperty", A),
])
def test_a_built_in_property_name_is_not_written_where_the_reader_refuses_it(axiom):
    # parse_manchester_role_axiom refuses every built-in name in every position,
    # so a writer that printed one would produce text the reader rejects. The
    # pre-fix writer did print it: "r SubPropertyOf owl:topObjectProperty".
    with pytest.raises(ManchesterSyntaxError, match="BUILT-IN"):
        dl.parse_manchester_role_axiom({
            "subproperty": f"{axiom[1]} SubPropertyOf {axiom[2] if len(axiom) > 2 else ''}",
            "functional": f"{axiom[1]} Characteristics: Functional",
            "range": f"{axiom[1]} Range: A",
        }[axiom[0]])
    with pytest.raises(ValueError, match="BUILT-IN"):
        dl.role_axiom_to_manchester(*axiom)


def test_a_plain_role_axiom_still_writes_and_reads_back():
    # Control: the guard is on the operand, not the shape.
    for axiom in [("subproperty", "r", "s"), ("domain", "r", A),
                  ("functional", "r"), ("inverse", "p", "q")]:
        text = dl.role_axiom_to_manchester(*axiom)
        assert dl.parse_manchester_role_axiom(text) == axiom


# --------------------------------------------------------------------------- #
# A floating-point literal after `value` is a LITERAL, never an individual.
#
# The W3C Manchester grammar (§2.1) has three unquoted literal forms:
#   integerLiteral       ::= ['+'|'-'] digits                          xsd:integer
#   decimalLiteral       ::= ['+'|'-'] digits '.' digits               xsd:decimal
#   floatingPointLiteral ::= ['+'|'-'] (digits ['.' digits] [exponent]
#                                       | '.' digits [exponent]) ('f'|'F')
#                                                                     xsd:float
#   exponent             ::= ('e'|'E') ['+'|'-'] digits
# and the lexical form of the float is the text WITHOUT the f/F suffix. This
# kit's data layer has no first-order image of xsd:float (its value space has
# NaN and a signed zero, which the exact-number order does not), so a float is
# REFUSED BY NAME wherever it is translated -- the quoted spelling
# "1.5"^^xsd:float and the Functional-Style reader already do exactly that.
# Reading `d value 1.5f` as ObjectHasValue(d, the individual "1.5f") instead
# silently turned d into an object role: two routes, two answers, one of them
# silent.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("text, lexical", [
    ("d value 1.5f", "1.5"),        # digits '.' digits, f
    ("d value 2f", "2"),            # digits, f (no point, no exponent)
    ("d value 2F", "2"),            # F as well as f
    ("d value 1.0e+2f", "1.0e+2"),  # digits '.' digits exponent, f
    ("d value -1.5F", "-1.5"),      # a sign
    ("d value +3e2f", "+3e2"),      # digits exponent (no point), a plus sign
    ("d value .5f", ".5"),          # '.' digits
])
def test_a_floating_point_literal_after_value_is_an_xsd_float(text, lexical):
    expected = dl.DataHasValue("d", dl.Literal(lexical, "xsd:float"))
    assert parse_manchester(text) == expected
    # ... and it is the SAME restriction as the quoted spelling.
    assert parse_manchester(f'd value "{lexical}"^^xsd:float') == expected


def test_a_floating_point_literal_is_refused_by_name_at_translation_like_the_quoted_one():
    # Two spellings, one refusal: each names the literal and says it has no
    # first-order image. The Functional-Style route refuses the same literal
    # with the same text (it does so while reading).
    spelled = parse_manchester("d value 1.5f")
    with pytest.raises(dl.UnsupportedDatatypeError) as bare:
        dl.concept_to_fol(spelled)
    with pytest.raises(dl.UnsupportedDatatypeError) as quoted:
        dl.concept_to_fol(parse_manchester('d value "1.5"^^xsd:float'))
    assert str(bare.value) == str(quoted.value)
    assert '"1.5"^^xsd:float' in str(bare.value)
    assert "no first-order image" in str(bare.value)
    with pytest.raises(ValueError) as functional:
        dl.parse_owl_functional_class_expression('DataHasValue(d "1.5"^^xsd:float)')
    assert '"1.5"^^xsd:float has no first-order image' in str(functional.value)


@pytest.mark.parametrize("text, expected", [
    # The other two bare forms keep their meaning (the control).
    ("d value 1", dl.DataHasValue("d", dl.Literal("1", "xsd:integer"))),
    ("d value -3", dl.DataHasValue("d", dl.Literal("-3", "xsd:integer"))),
    ("d value 1.5", dl.DataHasValue("d", dl.Literal("1.5", "xsd:decimal"))),
    # A name is an individual. None of these is a floatingPointLiteral: the
    # grammar requires the f/F, and nothing may follow it.
    ("d value a", dl.HasValue("d", "a")),
    ("d value f", dl.HasValue("d", "f")),
    ("d value 1e5", dl.HasValue("d", "1e5")),      # exponent without f
    ("d value 1.5d", dl.HasValue("d", "1.5d")),    # d is not a float suffix
    ("d value 1.5fx", dl.HasValue("d", "1.5fx")),  # something follows the f
])
def test_the_other_value_slots_are_unchanged(text, expected):
    assert parse_manchester(text) == expected


def test_a_floating_point_literal_is_a_literal_in_the_other_literal_slots_too():
    # A literal read after `value` is a literal everywhere the grammar has a
    # `literal` slot: the literal reader, a data one-of and a facet bound.
    assert dl.parse_manchester_literal("1.5f") == dl.Literal("1.5", "xsd:float")
    assert parse_manchester("d some {1.5f, 2}") == dl.DataExists(
        "d", dl.DataOneOf((dl.Literal("1.5", "xsd:float"), dl.Literal("2", "xsd:integer"))))
    # A float bound on an exact-number base is not an exact number: refused by
    # name (it was refused before, as an "expected a literal"; now the reader
    # says what is wrong), identically to the quoted spelling.
    for bound in ("1.5f", '"1.5"^^xsd:float'):
        with pytest.raises(ManchesterSyntaxError) as exc:
            parse_manchester(f"d some xsd:integer[>= {bound}]")
        assert "xsd:minInclusive" in str(exc.value)
        assert '"1.5"^^xsd:float' in str(exc.value)


# --------------------------------------------------------------------------- #
# The writer refuses where the reader does.
#
# An OWL 2 built-in property name (owl:topObjectProperty and the other three) or
# the name of an equality atom (``=`` / ``≠``) as the role of a restriction is
# refused by name by the Manchester READER, by the Functional-Style writer and by
# every other route; ``to_manchester`` used to print ``owl:topObjectProperty some
# A`` for it, text its own reader refuses (and a different restriction if some
# other tool read it: the universal property is not an ordinary role). All of them
# refuse through ONE function, dl.tableau._reject_concept_role, so the words differ
# only in the ``where:`` prefix.
# --------------------------------------------------------------------------- #

_BUILT_IN_ROLE_NAMES = ["owl:topObjectProperty", "owl:bottomObjectProperty",
                        "owl:topDataProperty", "owl:bottomDataProperty", "=", "≠"]


@pytest.mark.parametrize("name", _BUILT_IN_ROLE_NAMES)
def test_the_writer_refuses_the_concept_its_reader_refuses_the_text_of(name):
    concept = dl.Exists(name, A)
    # the text the old writer produced, and what the reader says of it
    with pytest.raises(ManchesterSyntaxError):
        parse_manchester(f"{name} some A")
    # the writer no longer prints it ...
    with pytest.raises(dl.RoleExpressionError) as written:
        to_manchester(concept)
    # ... and is the same refusal the Functional-Style writer gives
    with pytest.raises(dl.RoleExpressionError) as functional:
        dl.to_owl_functional_class_expression(concept)
    assert str(written.value).replace("to_manchester", "X") == \
        str(functional.value).replace("to_owl_functional_class_expression", "X")
    assert name in str(written.value)


@pytest.mark.parametrize("make", [
    lambda n: dl.ForAll(n, A),
    lambda n: dl.AtLeast(2, n, A),
    lambda n: dl.AtMost(1, n, A),
    lambda n: dl.HasValue(n, "b"),
    lambda n: dl.DataExists(n, dl.Datatype("xsd:integer")),
    lambda n: dl.DataAtLeast(1, n, dl.Datatype("xsd:integer")),
    # at depth: under not, and, or and a filler
    lambda n: dl.And(A, dl.Not(dl.Or(B, dl.Exists("r", dl.Exists(n, A))))),
])
def test_the_writer_refuses_every_restriction_and_every_depth(make):
    for name in _BUILT_IN_ROLE_NAMES:
        with pytest.raises(dl.RoleExpressionError, match="to_manchester"):
            to_manchester(make(name))


@pytest.mark.parametrize("tag", ["domain", "range"])
def test_the_role_axiom_writer_refuses_a_filler_with_a_built_in_role(tag):
    for name in _BUILT_IN_ROLE_NAMES:
        with pytest.raises(dl.RoleExpressionError, match=r"role_axiom_to_manchester"):
            dl.role_axiom_to_manchester(tag, "r", dl.Not(dl.Exists(name, A)))


def test_the_writer_still_writes_what_the_reader_reads():
    # The control: only a built-in or equality name is refused. An ordinary role,
    # an inverse role (render-only, as always) and a nominal are written as before.
    for concept, text in [
        (dl.Exists("hasChild", A), "hasChild some A"),
        (dl.AtLeast(2, "r", A), "r min 2 A"),
        (dl.Exists(dl.InverseRole("r"), A), "inverse r some A"),
        (dl.Nominal("a"), "{a}"),
    ]:
        assert to_manchester(concept) == text
    assert dl.role_axiom_to_manchester("domain", "r", dl.Exists("s", A)) == "r Domain: s some A"
    # a role merely NAMED like a built-in is not one
    assert to_manchester(dl.Exists("topObjectProperty", A)) == "topObjectProperty some A"
