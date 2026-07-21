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
    # concepts.py's renderer gives both operands of ⊓/⊔ the SAME precedence
    # threshold (_paren(c.left, prec) and _paren(c.right, prec), both using
    # "<" not "<="), so a left-nested chain (Or(Or(A,B),C)) and a right-nested
    # chain (Or(A,Or(B,C))) render to the IDENTICAL string "A ⊔ B ⊔ C" -- the
    # rendering genuinely cannot tell them apart. parse_concept must therefore
    # pick ONE convention; it picks left-associative (the standard choice for
    # a straightforward recursive-descent "while op: left = Op(left, right)"
    # loop), so a chain always reparses to the left-nested shape regardless of
    # which shape produced the string.
    left_nested = dl.Or(dl.Or(A, B), C)
    right_nested = dl.Or(A, dl.Or(B, C))
    assert left_nested.to_unicode() == right_nested.to_unicode() == "A ⊔ B ⊔ C"
    assert parse_concept("A ⊔ B ⊔ C") == left_nested
    assert parse_concept("A ⊔ B ⊔ C") != right_nested


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
    # Property checked: RENDER-IDEMPOTENCE, i.e. parse_concept(rendered).to_unicode()
    # == rendered, rather than exact structural equality against the
    # generator's own (possibly right-nested) tree. As
    # test_parser_associates_chained_same_precedence_operators_to_the_left
    # demonstrates, a randomly right-nested chain of the same operator (e.g.
    # Or(A, Or(B, C))) renders identically to its left-nested counterpart, so
    # a fuzz generator that builds arbitrary (not necessarily left-associative)
    # trees cannot be checked against exact structural equality without
    # spuriously failing on that (harmless, renderer-inherent) ambiguity.
    # Render-idempotence is the property that must ALWAYS hold regardless of
    # which shape parse_concept recovers: it proves the parser reconstructed a
    # concept that is a faithful reading of the string (round-trips the TEXT
    # exactly), which is what parse_concept is actually for.
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
