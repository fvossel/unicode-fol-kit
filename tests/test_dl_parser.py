"""Tests for the ALC concept string parser (unicode_fol_kit.dl.parser).

Round-trip is the primary correctness property: `parse_concept(c.to_unicode())
== c` must hold for every constructor, deeply nested, and with multi-char /
non-ASCII role and concept names — since `to_unicode` is precedence-aware
(parenthesises only where needed, per concepts.py's `_PREC` table), a parser
that gets precedence wrong would still fail this even though it "looks
right" on any single hand-written example.
"""

import random

import pytest

import unicode_fol_kit.dl as dl
from unicode_fol_kit.dl.parser import parse_concept, parse_gci, ConceptSyntaxError

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
    rendered = concept.to_unicode()
    assert parse_concept(rendered) == concept


# --------------------------------------------------------------------------- #
# Round-trip: deep nesting, mixed precedence, parentheses required/omitted.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("concept", [
    dl.Not(dl.Not(A)),                                            # ¬¬A: no parens needed
    dl.Exists("r", dl.ForAll("s", A)),                            # ∃r.∀s.A: no parens needed
    dl.Exists("r", dl.And(A, dl.Not(B))),                         # ∃r.(A ⊓ ¬B): the docstring's own example
    dl.And(dl.Or(A, B), C),                                       # (A ⊔ B) ⊓ C: left needs parens (Or < And)
    dl.Or(dl.And(A, B), C),                                       # A ⊓ B ⊔ C: no parens needed (And > Or)
    dl.Not(dl.And(A, B)),                                         # ¬(A ⊓ B): parens needed (And < Not's level)
    dl.Not(dl.Exists("r", A)),                                    # ¬∃r.A: no parens (Exists == Not's level)
    dl.Exists("r", dl.Not(dl.And(A, B))),                         # ∃r.¬(A ⊓ B): nested parens
    dl.ForAll("r", dl.Exists("s", dl.Or(A, dl.Not(B)))),          # ∀r.∃s.(A ⊔ ¬B)
    dl.And(dl.Exists("r", A), dl.ForAll("r", dl.Not(A))),         # (∃r.A) ⊓ (∀r.¬A): siblings, no outer parens
    dl.Or(dl.Or(dl.Not(A), B), C),                                # ¬A ⊔ B ⊔ C, LEFT-associative (see note below)
    dl.And(dl.And(dl.Not(A), B), C),                              # ¬A ⊓ B ⊓ C, LEFT-associative
    dl.Exists("r", dl.Exists("s", dl.Exists("t", A))),            # triple nesting, same op
    dl.Not(dl.Not(dl.Not(A))),                                    # triple negation
    dl.And(dl.Top(), dl.Or(dl.Bottom(), A)),                      # ⊤/⊥ mixed with restrictions
    dl.Exists("hasChild", dl.And(dl.Atomic("Doctor"), dl.Not(dl.Atomic("Rich")))),
    dl.ForAll("r", dl.ForAll("r", dl.ForAll("r", dl.Bottom()))),  # deep same-role nesting
    dl.Or(dl.And(A, dl.Not(B)), dl.And(dl.Not(A), B)),            # XOR-shaped
], ids=lambda c: c.to_unicode())
def test_round_trip_deep_nesting(concept):
    rendered = concept.to_unicode()
    assert parse_concept(rendered) == concept, rendered


def test_parser_associates_chained_same_precedence_operators_to_the_left():
    # parse_concept folds a flat chain LEFT (the standard choice for a
    # straightforward recursive-descent "while op: left = Op(left, right)"
    # loop), so "A ⊔ B ⊔ C" is Or(Or(A,B),C). The renderer used to give both
    # operands of ⊓/⊔ the SAME precedence threshold, so the right-nested chain
    # Or(A,Or(B,C)) was written "A ⊔ B ⊔ C" as well -- the TEXT could not tell
    # the two trees apart, and reading it back gave the left-nested one, another
    # tree. A right operand of the same connective is now parenthesised, so each
    # tree has its own text (tests/test_dl_glyph_round_trip.py has every shape).
    left_nested = dl.Or(dl.Or(A, B), C)
    right_nested = dl.Or(A, dl.Or(B, C))
    assert left_nested.to_unicode() == "A ⊔ B ⊔ C"
    assert right_nested.to_unicode() == "A ⊔ (B ⊔ C)"
    assert parse_concept("A ⊔ B ⊔ C") == left_nested
    assert parse_concept("A ⊔ B ⊔ C") != right_nested
    assert parse_concept("A ⊔ (B ⊔ C)") == right_nested


# --------------------------------------------------------------------------- #
# Round-trip: multi-char and non-ASCII role/concept names.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("concept", [
    dl.Atomic("Person"),
    dl.Atomic("VeryLongConceptName123"),
    dl.Exists("hasChild", dl.Atomic("Doctor")),
    dl.ForAll("hasSibling", dl.Not(dl.Atomic("OnlyChild"))),
    dl.Exists("θ", dl.Atomic("φ")),                # Greek names (both role and concept)
    dl.And(dl.Atomic("A_1"), dl.Atomic("B_2")),    # underscores/digits in names
    dl.Exists("r1", dl.Exists("r2", dl.Atomic("C3"))),
], ids=lambda c: c.to_unicode())
def test_round_trip_multichar_and_nonascii_names(concept):
    rendered = concept.to_unicode()
    assert parse_concept(rendered) == concept, rendered


def test_round_trip_random_deeply_nested_concepts():
    # Same shape of generator as test_dl_alc.py's _rand_concept / the
    # translate differential tests, but purely exercising the parser here.
    #
    # Properties checked: RENDER-IDEMPOTENCE, parse_concept(rendered).to_unicode()
    # == rendered, and, since a right operand of the same connective is
    # parenthesised (so a randomly right-nested chain such as Or(A, Or(B, C)) no
    # longer renders like its left-nested counterpart), EXACT structural
    # equality against the generator's own tree. The first alone used to be all
    # that could hold: the two trees shared one text, and a check for equality
    # failed on that ambiguity of the renderer.
    atoms = [dl.Atomic("A"), dl.Atomic("B"), dl.Atomic("C")]
    roles = ["r", "hasChild", "s2"]

    def rand_concept(depth, rng):
        if depth <= 0 or rng.random() < 0.25:
            choice = rng.random()
            if choice < 0.1:
                return dl.Top()
            if choice < 0.2:
                return dl.Bottom()
            return rng.choice(atoms)
        k = rng.random()
        if k < 0.14:
            return dl.Not(rand_concept(depth - 1, rng))
        if k < 0.34:
            return dl.And(rand_concept(depth - 1, rng), rand_concept(depth - 1, rng))
        if k < 0.54:
            return dl.Or(rand_concept(depth - 1, rng), rand_concept(depth - 1, rng))
        if k < 0.77:
            return dl.Exists(rng.choice(roles), rand_concept(depth - 1, rng))
        return dl.ForAll(rng.choice(roles), rand_concept(depth - 1, rng))

    rng = random.Random(424242)
    checked = 0
    for _ in range(60):
        concept = rand_concept(5, rng)
        rendered = concept.to_unicode()
        reparsed = parse_concept(rendered)
        assert reparsed.to_unicode() == rendered, rendered
        assert reparsed == concept, rendered
        checked += 1
    assert checked == 60


def test_round_trip_random_left_associative_concepts_is_exact():
    # A variant of the fuzz generator above that always folds chained ⊓/⊔
    # LEFT-associatively (matching the parser's own convention exactly), so
    # here exact structural equality is a meaningful, always-valid check --
    # complementing the render-idempotence check above with a stronger
    # guarantee on the subset of trees where the two conventions agree.
    atoms = [dl.Atomic("A"), dl.Atomic("B"), dl.Atomic("C")]
    roles = ["r", "hasChild", "s2"]

    def rand_leaf_or_unary(depth, rng):
        if depth <= 0 or rng.random() < 0.4:
            choice = rng.random()
            if choice < 0.1:
                return dl.Top()
            if choice < 0.2:
                return dl.Bottom()
            return rng.choice(atoms)
        k = rng.random()
        if k < 0.4:
            return dl.Not(rand_leaf_or_unary(depth - 1, rng))
        if k < 0.7:
            return dl.Exists(rng.choice(roles), rand_leaf_or_unary(depth - 1, rng))
        return dl.ForAll(rng.choice(roles), rand_leaf_or_unary(depth - 1, rng))

    def rand_chain(depth, rng):
        # Build a left-associative chain of 1-3 unary/leaf terms joined by a
        # single, consistently-chosen connective (⊓ or ⊔) at this level.
        n = rng.randint(1, 3)
        op = dl.And if rng.random() < 0.5 else dl.Or
        acc = rand_leaf_or_unary(depth, rng)
        for _ in range(n - 1):
            acc = op(acc, rand_leaf_or_unary(depth, rng))
        return acc

    rng = random.Random(13579)
    checked = 0
    for _ in range(40):
        concept = rand_chain(4, rng)
        rendered = concept.to_unicode()
        assert parse_concept(rendered) == concept, rendered
        checked += 1
    assert checked == 40


# --------------------------------------------------------------------------- #
# Explicit parentheses are accepted even where to_unicode() would omit them.
# --------------------------------------------------------------------------- #

def test_explicit_redundant_parens_are_accepted():
    assert parse_concept("(A)") == A
    assert parse_concept("((A))") == A
    assert parse_concept("(A ⊓ B) ⊓ C") == dl.And(dl.And(A, B), C)
    assert parse_concept("A ⊓ (B ⊓ C)") == dl.And(A, dl.And(B, C))
    # These two differ structurally despite being classically equivalent --
    # explicit parens must be respected, not silently normalised away.
    assert parse_concept("(A ⊓ B) ⊓ C") != parse_concept("A ⊓ (B ⊓ C)")


def test_whitespace_is_insignificant_between_tokens():
    assert parse_concept("A⊓B") == dl.And(A, B)
    assert parse_concept("A   ⊓   B") == dl.And(A, B)
    assert parse_concept("∃r.A") == dl.Exists("r", A)
    assert parse_concept("∃ r . A") == dl.Exists("r", A)  # tokenizer skips whitespace anywhere


# --------------------------------------------------------------------------- #
# Precedence is honoured, matching concepts.py's _PREC exactly.
# --------------------------------------------------------------------------- #

def test_and_binds_tighter_than_or():
    # A ⊓ B ⊔ C must parse as (A ⊓ B) ⊔ C, not A ⊓ (B ⊔ C).
    assert parse_concept("A ⊓ B ⊔ C") == dl.Or(dl.And(A, B), C)


def test_not_binds_tighter_than_and():
    assert parse_concept("¬A ⊓ B") == dl.And(dl.Not(A), B)


def test_exists_operand_stops_at_and_or_without_parens():
    # ∃r.A ⊓ B: the restriction's operand is a single unary-level concept (A),
    # so this parses as (∃r.A) ⊓ B, not ∃r.(A ⊓ B).
    assert parse_concept("∃r.A ⊓ B") == dl.And(dl.Exists("r", A), B)


# --------------------------------------------------------------------------- #
# Sensible errors on malformed input.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("text", [
    "",                  # empty input
    "(A",                # unbalanced: missing ')'
    "A)",                # unbalanced: stray ')'
    "∃r A",              # missing '.' after role name
    "∃r.",               # missing operand after '.'
    "A ⊓",               # missing right operand
    "⊓ A",               # missing left operand / stray operator
    "A B",               # two concepts with no connective between them
    "A ⊓ (B",            # unbalanced inside a subexpression
    "¬",                 # missing operand for negation
    "∃r.(A",             # unbalanced after a restriction
])
def test_malformed_input_raises_concept_syntax_error(text):
    with pytest.raises(ConceptSyntaxError):
        parse_concept(text)


def test_error_message_is_informative():
    with pytest.raises(ConceptSyntaxError, match="position"):
        parse_concept("A ⊓")
    with pytest.raises(ConceptSyntaxError, match=r"'\.'"):
        parse_concept("∃r A")


# --------------------------------------------------------------------------- #
# parse_gci: 'C ⊑ D' -> (C, D).
# --------------------------------------------------------------------------- #

def test_parse_gci_basic():
    assert parse_gci("A ⊑ B") == (A, B)


def test_parse_gci_with_restrictions():
    got = parse_gci("Doctor ⊑ ∃hasChild.⊤")
    assert got == (dl.Atomic("Doctor"), dl.Exists("hasChild", dl.Top()))


def test_parse_gci_with_nested_concepts_both_sides():
    got = parse_gci("A ⊓ B ⊑ ¬C ⊔ ∀r.A")
    expected = (dl.And(A, B), dl.Or(dl.Not(C), dl.ForAll("r", A)))
    assert got == expected


@pytest.mark.parametrize("text", [
    "A",             # no '⊑' at all
    "A ⊑",           # missing right-hand side
    "⊑ B",           # missing left-hand side
    "A ⊑ B ⊑ C",     # a second '⊑' is not part of this grammar (no chaining)
])
def test_parse_gci_malformed_raises(text):
    with pytest.raises(ConceptSyntaxError):
        parse_gci(text)


def test_parse_gci_matches_tbox_add_semantics():
    # parse_gci's (sub, sup) pair should be exactly what TBox.add expects.
    sub, sup = parse_gci("A ⊑ ∃r.B")
    t = dl.TBox().add(sub, sup)
    assert t.inclusions == [(dl.Atomic("A"), dl.Exists("r", dl.Atomic("B")))]


# --------------------------------------------------------------------------- #
# F1: braces are RESERVED, and a nominal-shaped text is refused BY NAME.
#
# Until 0.30.0 `{` and `}` were ordinary NAME characters, so `{a}` was a legal
# concept NAME and `parse_concept("{a}")` returned `Atomic("{a}")` -- a concept
# with a bogus class name, silently, for text this module's own siblings PRINT
# (`dl.Nominal("a").to_unicode()` is `{a}`). `dl.parse_manchester` already
# refused the same text by name; now so does this.
#
# Teaching it to BUILD a nominal was the alternative and was rejected: `∃r.{a}`
# is AMBIGUOUS between dl.HasValue("r", "a") and dl.Exists("r", dl.Nominal("a"))
# -- the glyph syntax has no individual-name layer to tell them apart, and both
# print identically -- so always picking one would be a silent normalisation of
# the other, which is what house rule 1 forbids.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("text", [
    "{a}",                  # the bare nominal, as dl.Nominal prints it
    "∃r.{a}",               # as dl.HasValue AND dl.Exists(r, Nominal(a)) print
    "¬{a}",
    "A ⊓ {a}",
    "{a} ⊔ B",
    "∀r.{a}",
    "≥2 r.{a}",
    "{a, b}",               # Manchester's multi-individual spelling
    "{",                    # an unbalanced brace is refused the same way
    "}",
])
def test_a_nominal_shaped_text_is_refused_by_name(text):
    with pytest.raises(ConceptSyntaxError) as info:
        parse_concept(text)
    message = str(info.value)
    assert "nominal" in message, message
    # the refusal must point at what to do instead -- the two readers that DO
    # tell the pair apart, and the constructors
    for pointer in ("dl.Nominal", "dl.HasValue", "parse_manchester",
                    "ObjectHasValue"):
        assert pointer in message, f"the refusal must name {pointer}: {message}"


def test_the_old_silent_reading_is_gone():
    # The control: the pre-0.30.0 behaviour was `Atomic("{a}")`, so a test that
    # only checked "it does not crash" would have passed. This asserts the
    # concept is not BUILT at all.
    with pytest.raises(ConceptSyntaxError):
        parse_concept("{a}")
    assert dl.Atomic("{a}") != dl.Nominal("a")      # it never was the same thing


def test_a_gci_mentioning_a_nominal_is_refused_too():
    with pytest.raises(ConceptSyntaxError, match="nominal"):
        parse_gci("A ⊑ ∃r.{a}")


def test_the_two_render_only_constructors_are_the_documented_exceptions():
    # The round-trip claim in this module's docstring holds for every
    # constructor EXCEPT the two that name an individual: both render, neither
    # re-parses, and the refusal is loud. The same render-only asymmetry
    # dl.to_manchester already has for a nominal.
    for concept in (dl.Nominal("a"), dl.HasValue("r", "a")):
        text = concept.to_unicode()
        assert "{" in text and "}" in text
        with pytest.raises(ConceptSyntaxError, match="nominal"):
            parse_concept(text)
    # ... and they really do print the same text, which is why neither can be
    # read back: there is nothing in the glyph syntax to distinguish them.
    assert dl.HasValue("r", "a").to_unicode() == \
        dl.Exists("r", dl.Nominal("a")).to_unicode()


def test_a_brace_inside_a_name_is_the_accepted_cost():
    # The narrowing this is, stated: a concept NAME containing a literal brace
    # stops parsing. There is no such name in the kit, its tests or the Open
    # Energy Ontology this was measured against, but it is a real change to a
    # documented "any characters outside the reserved set" grammar rule.
    with pytest.raises(ConceptSyntaxError):
        parse_concept("Has{Value}")
    # every OTHER non-reserved character still works, unchanged
    for name in ("Doctor42", "θ", "has_child", "A-B", "名前"):
        assert parse_concept(name) == dl.Atomic(name)
