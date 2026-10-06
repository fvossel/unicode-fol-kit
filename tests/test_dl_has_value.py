r"""A1: ``ObjectHasValue(P a)`` as ``dl.HasValue(role, individual)``.

The biggest single gap the Open Energy Ontology hit: 95 of its 4041 axioms use
a value restriction, and before 0.30.0 the only way to express one in this kit
was ``dl.Exists(role, dl.Nominal(a))`` — which the in-house tableau refuses
outright (a ``Nominal`` would need equality machinery over named individuals),
and whose FOL image ``∃x0 (r(x, x0) ∧ x0 = a)`` the kit's own parser then
rejected.

``HasValue`` is a concept kind of its OWN rather than that rewrite. Two
reasons, and this file tests both:

* it ROUND-TRIPS — ``ObjectHasValue(r a)`` and the still-refused
  ``ObjectSomeValuesFrom(r ObjectOneOf(a))`` are two distinct OWL 2 structural
  objects, as are Manchester's ``r value a`` and ``r some {a}``;
* its FOL image is the GROUND ATOM ``r(x, a)`` — the one-point reduction of
  ``∃y (r(x, y) ∧ y = a)``, which is a FOL validity, so the two have the same
  models and the reduced one mints no variable.

It is NOT decided by the in-house tableau. A value restriction is a nominal in
disguise: a tableau value-rule was built for 0.30.0, appeared sound, and was
removed again, because a value restriction gives a GENERATED node an edge back
to a NAMED one and subset blocking does not cover that. The two-axiom
counterexample is the last section of this file, and the "Value restrictions
(ObjectHasValue)" section of ``dl.tableau`` has the argument and the repair
that would have to be proved before anyone builds it. So every verdict about a
value restriction below is the FOL route's (and, where HermiT is installed,
HermiT's), derived by hand from the OWL 2 direct semantics first and written out
in the comment above it; the tableau half of each such test is that it RAISES
``UnsupportedConceptError`` rather than answer.

Two defects found while the value-rule existed are kept as tests, because the
decisions behind them outlived the rule: a NAMED node may not block a generated
one (F3, ``_blocked`` — now needed by negative role assertions) and
``concept_satisfiable``'s anonymous root is not called ``"a"`` (F4).

Z3-backed calls take their ``timeout`` in MILLISECONDS and it is never shrunk:
a tiny budget makes a backend answer "unknown", which several APIs report as
"not valid", so a non-theorem test with a 2 ms budget asserts nothing at all.
"""

import pytest

import unicode_fol_kit.dl as dl
from unicode_fol_kit import api
from unicode_fol_kit.dl import owl_reasoner as _owl_reasoner
from unicode_fol_kit.fol.nodes import (
    Atom, Constant, Iff, Not as FNot, Quantifier, Variable)

# Wide enough that a slow machine cannot turn an agreement into a
# disagreement, and never shrunk to make a test fast -- see the module
# docstring.
TIMEOUT_MS = 20000

A, B, C, D = (dl.Atomic("A"), dl.Atomic("B"), dl.Atomic("C"), dl.Atomic("D"))


def _status(goal, premises) -> str:
    return api.prove(goal, list(premises), timeout=TIMEOUT_MS).status


def _fol_says_satisfiable(concept, tbox=None) -> bool:
    """The FOL route's answer to ``concept_satisfiable(concept, tbox)``.

    ``∃x π(concept, x)`` is unsatisfiable w.r.t. the TBox iff its negation is
    PROVED from the TBox premises — which is the reduction ``kb_to_fol``'s own
    docstring spells out. "unknown" is a failure, not a pass.
    """
    kb = dl.kb_to_fol(tbox) if tbox is not None else dl.kb_to_fol()
    goal = FNot(Quantifier("∃", Variable("x"), dl.concept_to_fol(concept)))
    status = _status(goal, kb.tbox_premises)
    assert status in ("proved", "refuted"), (
        f"the FOL route gave {status!r}, so this test measured nothing")
    return status == "refuted"


# --------------------------------------------------------------------------- #
# The AST: negation normal form treats it as a LITERAL.
# --------------------------------------------------------------------------- #

def test_nnf_passes_a_value_restriction_through_in_both_polarities():
    # ¬∃r.{a} has no dual CONCEPT to push the negation into: "does not have a
    # as an r-successor" is a condition on an EDGE. So both polarities are
    # literals, exactly like Atomic and Not(Atomic).
    positive = dl.HasValue("R", "a")
    assert dl.nnf(positive) is positive
    negative = dl.Not(positive)
    assert dl.nnf(negative) is negative
    # double negation still cancels, through the generic Not(Not(...)) branch
    assert dl.nnf(dl.Not(negative)) == positive
    # and a complementary pair survives nnf intact, so the clash condition can
    # see it
    assert dl.nnf(dl.And(positive, negative)) == dl.And(positive, negative)


def test_nnf_reaches_a_value_restriction_nested_under_a_negated_quantifier():
    # ¬∃R.(∃S.{a}) = ∀R.¬∃S.{a}: the De Morgan/modal duality is unchanged, and
    # the inner literal comes out negated.
    assert dl.nnf(dl.Not(dl.Exists("R", dl.HasValue("S", "a")))) == \
        dl.ForAll("R", dl.Not(dl.HasValue("S", "a")))


# --------------------------------------------------------------------------- #
# Rendering: the textbook DL spelling, at restriction precedence.
# --------------------------------------------------------------------------- #

def test_a_value_restriction_renders_as_the_textbook_glyph_form():
    # There is no glyph of its own for a value restriction; ∃r.{a} IS the
    # textbook spelling, and it is identical to Exists(r, Nominal(a))'s -- which
    # is honest, because the two concepts have the same models.
    assert dl.HasValue("HasStateOfMatter", "Liquid").to_unicode() == \
        "∃HasStateOfMatter.{Liquid}"
    assert dl.HasValue("R", "a").to_unicode() == dl.Exists("R", dl.Nominal("a")).to_unicode()


def test_a_value_restriction_binds_as_tightly_as_a_restriction():
    # _PREC[HasValue] = 3, the restriction level, so it needs no parentheses as
    # an operand of ⊓ (precedence 2) and ¬ (3) ...
    assert dl.And(A, dl.HasValue("R", "a")).to_unicode() == "A ⊓ ∃R.{a}"
    assert dl.Not(dl.HasValue("R", "a")).to_unicode() == "¬∃R.{a}"
    # ... and takes them as the operand of nothing, since its own operand is a
    # NAME, never a nested description.
    assert dl.Exists("S", dl.HasValue("R", "a")).to_unicode() == "∃S.∃R.{a}"


def test_the_glyph_text_is_refused_on_the_way_back_in_by_name():
    # The documented asymmetry: ∃R.{a} renders but does not re-parse, because
    # the glyph syntax cannot tell HasValue("R", "a") from
    # Exists("R", Nominal("a")) -- and picking one would silently normalise the
    # other. See tests/test_dl_parser.py for the full refusal battery.
    with pytest.raises(dl.ConceptSyntaxError, match="nominal"):
        dl.parse_concept(dl.HasValue("R", "a").to_unicode())


# --------------------------------------------------------------------------- #
# The FOL image: the GROUND ATOM, hand-derived.
# --------------------------------------------------------------------------- #

def test_the_image_is_the_ground_atom():
    # OWL 2 direct semantics: (ObjectHasValue(P a))^C = { x | <x, a^I> ∈ P^OP }.
    # The standard translation of the equivalent ∃P.{a} is
    # ∃y (P(x, y) ∧ y = a), and one-point elimination of the equality-bounded
    # existential (y occurs only in the conjunction) gives P(x, a).
    assert dl.concept_to_fol(
        dl.HasValue("HasStateOfMatter", "Liquid")).to_unicode_str() == \
        "HasStateOfMatter(x, Liquid)"
    assert dl.concept_to_fol(
        dl.Not(dl.HasValue("HasStateOfMatter", "Liquid"))).to_unicode_str() == \
        "¬HasStateOfMatter(x, Liquid)"


def test_the_image_of_the_oeo_subsumption_axiom():
    # ax01856 SubClassOf(Sirup ObjectHasValue(HasStateOfMatter Liquid)):
    # the universal closure of the inclusion, antecedent Sirup(x), consequent
    # the ground atom.
    assert dl.subsumption_to_fol(
        dl.Atomic("Sirup"),
        dl.HasValue("HasStateOfMatter", "Liquid")).to_unicode_str() == \
        "∀x (Sirup(x) → HasStateOfMatter(x, Liquid))"


def test_the_image_of_the_oeo_nested_axiom():
    # ax00335 SubClassOf(GasFiredPowerUnit ObjectSomeValuesFrom(Uses
    #   ObjectIntersectionOf(Fuel ObjectHasValue(HasNormalStateOfMatter Gaseous))))
    # The ∃ mints ONE variable (x0, stepping over the individual name), the
    # value restriction mints none, and the individual lands in the argument
    # position at the minted variable -- not at x.
    assert dl.subsumption_to_fol(
        dl.Atomic("GasFiredPowerUnit"),
        dl.Exists("Uses", dl.And(dl.Atomic("Fuel"),
                                 dl.HasValue("HasNormalStateOfMatter", "Gaseous")))
    ).to_unicode_str() == (
        "∀x (GasFiredPowerUnit(x) → ∃x0 (Uses(x, x0) ∧ "
        "(Fuel(x0) ∧ HasNormalStateOfMatter(x0, Gaseous))))")


def test_the_image_of_the_oeo_equivalence_axiom():
    # ax00672 EquivalentClasses(LiquidAir ObjectIntersectionOf(Air
    #   ObjectHasValue(HasStateOfMatter Liquid))) -- stored as the PAIR of
    # inclusions it abbreviates, so the image is their conjunction.
    tbox = dl.TBox().add_equivalence(
        dl.Atomic("LiquidAir"),
        dl.And(dl.Atomic("Air"), dl.HasValue("HasStateOfMatter", "Liquid")))
    assert dl.tbox_to_fol(tbox).to_unicode_str() == (
        "∀x (LiquidAir(x) → Air(x) ∧ HasStateOfMatter(x, Liquid)) ∧ "
        "∀x (Air(x) ∧ HasStateOfMatter(x, Liquid) → LiquidAir(x))")


def test_the_individual_cannot_be_captured_by_a_minted_variable():
    # THE regression for _individual_names. That function collects the names
    # the translation will render as CONSTANTS, and _fresh_var_factory avoids
    # them -- because Variable("x0") and Constant("x0") print the same text and
    # are the same Z3 expression, so a minted x0 would CAPTURE the individual
    # and it would stop denoting itself. _individual_names walks dataclass
    # FIELDS generically, so a concept kind missing from its explicit check is
    # a SILENT miss: it is the one isinstance chain in the package that does
    # not end in a raise.
    image = dl.concept_to_fol(dl.And(dl.HasValue("r", "x0"),
                                     dl.Exists("s", dl.Atomic("A"))))
    assert image.to_unicode_str() == "r(x, x0) ∧ ∃x1 (s(x, x1) ∧ A(x1))"
    assert "x0" in {t.name for t in image.walk() if type(t).__name__ == "Constant"}


def test_an_inverse_role_swaps_the_atoms_arguments():
    # π(∃r⁻.{a}, x) = r(a, x): the standard translation of an inverse role
    # swaps the atom's argument order and nothing else. The FOL route renders
    # it; the tableau refuses it (see the refusal tests below).
    assert dl.concept_to_fol(
        dl.HasValue(dl.InverseRole("r"), "a")).to_unicode_str() == "r(a, x)"


def test_the_image_is_equivalent_to_the_rewrite_it_replaces():
    # The SECOND oracle for the one-point elimination: ∀x (P(x, a) ↔
    # ∃x0 (P(x, x0) ∧ x0 = a)) is a FOL validity, so the new image and the
    # caller's old rewrite have exactly the same models. Z3, 20 s.
    reduced = dl.concept_to_fol(dl.HasValue("R", "a"))
    rewrite = dl.concept_to_fol(dl.Exists("R", dl.Nominal("a")))
    goal = Quantifier("∀", Variable("x"), Iff(reduced, rewrite))
    assert _status(goal, ()) == "proved"


# --------------------------------------------------------------------------- #
# Round trips: the two concrete syntaxes that DO tell the pair apart.
# --------------------------------------------------------------------------- #

def test_the_functional_syntax_class_expression_round_trips():
    assert dl.parse_owl_functional_class_expression("ObjectHasValue(r a)") == \
        dl.HasValue("r", "a")
    assert dl.to_owl_functional_class_expression(dl.HasValue("r", "a")) == \
        "ObjectHasValue(r a)"


def test_the_full_iri_form_round_trips_with_its_brackets():
    expression = "ObjectHasValue(<http://x/r> <http://x/a>)"
    concept = dl.parse_owl_functional_class_expression(expression)
    assert concept == dl.HasValue("http://x/r", "http://x/a")
    assert dl.to_owl_functional_class_expression(concept) == expression


def test_a_whole_document_round_trips_and_declares_the_individual():
    # The individual appears ONLY inside a TBox class expression, which is the
    # shape every one of OEO's 95 value-restriction axioms has -- so
    # _collect_names must reach it, or the Declaration block would omit it.
    tbox, abox = dl.parse_owl_functional(
        "Ontology(SubClassOf(Sirup ObjectHasValue(HasStateOfMatter Liquid)))")
    assert tbox == dl.TBox().add(dl.Atomic("Sirup"),
                                 dl.HasValue("HasStateOfMatter", "Liquid"))
    assert abox == dl.ABox()
    text = dl.to_owl_functional(tbox, abox)
    assert "Declaration(NamedIndividual(Liquid))" in text
    assert "SubClassOf(Sirup ObjectHasValue(HasStateOfMatter Liquid))" in text
    assert dl.parse_owl_functional(text) == (tbox, abox)


def test_the_other_owl_spelling_is_still_refused_by_name():
    # ObjectSomeValuesFrom(r ObjectOneOf(a)) is a DIFFERENT OWL 2 structural
    # object, and collapsing the two into one AST shape is exactly what having
    # a node of our own avoids.
    with pytest.raises(dl.OwlFunctionalSyntaxError, match="ObjectOneOf"):
        dl.parse_owl_functional_class_expression(
            "ObjectSomeValuesFrom(r ObjectOneOf(a))")


def test_the_manchester_syntax_round_trips():
    assert dl.parse_manchester("r value a") == dl.HasValue("r", "a")
    assert dl.to_manchester(dl.HasValue("r", "a")) == "r value a"
    # and inside a conjunction, where precedence 3 means no parentheses
    assert dl.parse_manchester("A and r value a") == \
        dl.And(A, dl.HasValue("r", "a"))
    assert dl.to_manchester(dl.And(A, dl.HasValue("r", "a"))) == "A and r value a"


def test_the_manchester_nominal_spelling_is_still_refused_by_name():
    with pytest.raises(dl.ManchesterSyntaxError, match="nominal"):
        dl.parse_manchester("r some {a}")


def test_a_missing_individual_is_a_syntax_error_in_both_syntaxes():
    with pytest.raises(dl.ManchesterSyntaxError, match="individual"):
        dl.parse_manchester("r value")
    with pytest.raises(dl.OwlFunctionalSyntaxError):
        dl.parse_owl_functional_class_expression("ObjectHasValue(r)")


# --------------------------------------------------------------------------- #
# The tableau REFUSES a value restriction; every verdict is the FOL route's.
# --------------------------------------------------------------------------- #
#
# A value restriction is a nominal in disguise, and a tableau value-rule that
# decided it was removed again: see "Value restrictions (ObjectHasValue)" in
# the module docstring of dl.tableau, and the last section of this file for the
# two-axiom counterexample that no patch to the rule could repair. Each test
# below keeps the verdict it was written with, hand-derived, and asks it of the
# route that answers (the FOL image); the tableau half is that it RAISES.

def _fol_answers_tableau_refuses(concept, tbox=None, *, satisfiable: bool) -> None:
    """The hand-derived verdict, from the FOL route; and the in-house tableau's
    refusal to give one."""
    assert _fol_says_satisfiable(concept, tbox) is satisfiable, "the FOL route disagrees"
    with pytest.raises(dl.UnsupportedConceptError, match="HasValue"):
        dl.concept_satisfiable(concept, tbox)


def _refuses(call) -> None:
    with pytest.raises(dl.UnsupportedConceptError, match="HasValue"):
        call()


def test_a_value_restriction_alone_is_satisfiable():
    # ∃r.{a} is satisfied by Δ = {d, e}, a = e, r = {(d, e)}, d the witness.
    _fol_answers_tableau_refuses(dl.HasValue("r", "a"), satisfiable=True)


def test_a_value_restriction_and_its_negation_clash():
    # ∃r.{a} ⊓ ¬∃r.{a} is C ⊓ ¬C: no model.
    _fol_answers_tableau_refuses(
        dl.And(dl.HasValue("r", "a"), dl.Not(dl.HasValue("r", "a"))),
        satisfiable=False)


def test_a_value_restriction_against_an_empty_value_restriction_clashes():
    # ∃r.{a} ⊓ ∀r.⊥: x has the r-successor a, and ∀r.⊥ puts a in ⊥^I = ∅.
    # No model.
    _fol_answers_tableau_refuses(
        dl.And(dl.HasValue("r", "a"), dl.ForAll("r", dl.Bottom())),
        satisfiable=False)


def test_the_value_restriction_forces_the_individuals_class():
    # ∃r.{a} ⊓ ∀r.C entails C(a) -- so asserting a : ¬C alongside is
    # inconsistent.
    abox = (dl.ABox()
            .assert_concept("x", dl.And(dl.HasValue("r", "a"), dl.ForAll("r", C)))
            .assert_concept("a", dl.Not(C)))
    kb = dl.kb_to_fol(None, abox)
    assert _status(FNot(kb.formula), kb.axioms) == "proved"
    _refuses(lambda: dl.abox_consistent(abox))
    # and the entailment itself
    positive = (dl.ABox()
                .assert_concept("x", dl.And(dl.HasValue("r", "a"), dl.ForAll("r", C))))
    kb2 = dl.kb_to_fol(None, positive)
    goal = dl.abox_to_fol(dl.ABox().assert_concept("a", C))
    assert _status(goal, kb2.premises) == "proved"
    _refuses(lambda: dl.instance_check(positive, "a", C))
    # Not vacuous: nothing makes x itself a C (Δ = {x, a}, r = {(x, a)}, a ∈ C,
    # x ∉ C).
    assert _status(dl.abox_to_fol(dl.ABox().assert_concept("x", C)),
                   kb2.premises) == "refuted"


def test_the_edge_check_is_role_hierarchy_aware():
    # With s ⊑ r, every s-edge IS an r-edge in every model, so
    # ∃s.{a} ⊓ ¬∃r.{a} has none.
    tbox = dl.TBox().add_role_inclusion("s", "r")
    _fol_answers_tableau_refuses(
        dl.And(dl.HasValue("s", "a"), dl.Not(dl.HasValue("r", "a"))),
        tbox, satisfiable=False)
    # The CONVERSE does not hold: an r-edge need not be an s-edge, so
    # ∃r.{a} ⊓ ¬∃s.{a} is satisfiable -- Δ = {d, e}, a = e, r = {(d, e)},
    # s = ∅.
    _fol_answers_tableau_refuses(
        dl.And(dl.HasValue("r", "a"), dl.Not(dl.HasValue("s", "a"))),
        tbox, satisfiable=True)


def test_the_at_most_rule_merges_the_fresh_witness_into_the_named_node():
    # ≤1 r.⊤ ⊓ ∃r.{a} ⊓ ∃r.C: the one r-successor is a, and it is in C.
    # Satisfiable: Δ = {d, a}, r = {(d, a)}, a ∈ C.
    _fol_answers_tableau_refuses(
        dl.And(dl.And(dl.AtMost(1, "r", dl.Top()), dl.HasValue("r", "a")),
               dl.Exists("r", C)),
        satisfiable=True)


def test_but_a_forced_distinct_second_successor_cannot_merge():
    # ... and the same restriction with a SECOND, explicitly distinct named
    # successor has no model: x has r-successors a and b with a ≠ b, so two
    # pairwise-distinct ones, against ≤1 r.⊤.
    abox = (dl.ABox()
            .assert_concept("x", dl.And(dl.AtMost(1, "r", dl.Top()),
                                        dl.HasValue("r", "a")))
            .assert_role("x", "b", "r")
            .assert_distinct("a", "b"))
    kb = dl.kb_to_fol(None, abox)
    assert _status(FNot(kb.formula), kb.axioms) == "proved"
    _refuses(lambda: dl.abox_consistent(abox))
    # Drop the distinctness and a and b may denote one element again.
    mergeable = (dl.ABox()
                 .assert_concept("x", dl.And(dl.AtMost(1, "r", dl.Top()),
                                             dl.HasValue("r", "a")))
                 .assert_role("x", "b", "r"))
    kb2 = dl.kb_to_fol(None, mergeable)
    assert _status(FNot(kb2.formula), kb2.axioms) == "refuted"
    _refuses(lambda: dl.abox_consistent(mergeable))


def test_a_tbox_gci_applies_to_the_individual_a_value_restriction_names():
    # The element a value restriction names is a DOMAIN ELEMENT, so every GCI
    # applies to it. With ⊤ ⊑ C and x : ∃r.{a}, a is in C.
    tbox = dl.TBox().add(dl.Top(), C)
    abox = dl.ABox().assert_concept("x", dl.HasValue("r", "a"))
    kb = dl.kb_to_fol(tbox, abox)
    goal = dl.abox_to_fol(dl.ABox().assert_concept("a", C))
    assert _status(goal, kb.premises) == "proved"
    _refuses(lambda: dl.instance_check(abox, "a", C, tbox))


# --------------------------------------------------------------------------- #
# Non-simple roles: the FOL verdicts, and which refusal the tableau gives.
# --------------------------------------------------------------------------- #

def test_a_value_restriction_on_a_transitive_role_is_refused_as_a_value_restriction():
    # Before the value-rule was removed, a NEGATED value restriction on a
    # transitive role was refused as NonSimpleRoleError and the positive form was
    # decided. Both are now the value restriction's own refusal: the construct
    # check runs before simplicity is asked, so NonSimpleRoleError is never the
    # answer for a HasValue.
    #
    # The verdicts, hand-derived, are the FOL route's. ¬∃r.{a} with Trans(r) is
    # satisfiable (r = ∅ is transitive and has no edge to a); so is the same with
    # Trans(s), s ⊑ r (r = s = ∅); so is ∃r.{a} with Trans(r) (one edge is
    # transitive: Δ = {d, e}, r = {(d, e)}); and C ⊑ ¬∃r.{a} with Trans(r), asked
    # of C, again r = ∅.
    transitive = dl.TBox().add_transitive_role("r")
    sub_transitive = dl.TBox().add_transitive_role("s").add_role_inclusion("s", "r")
    inclusion = dl.TBox().add_transitive_role("r").add(C, dl.Not(dl.HasValue("r", "a")))
    cases = [
        (dl.Not(dl.HasValue("r", "a")), transitive),
        (dl.Not(dl.HasValue("r", "a")), sub_transitive),
        (dl.HasValue("r", "a"), transitive),
        (C, inclusion),
    ]
    for concept, tbox in cases:
        assert _fol_says_satisfiable(concept, tbox) is True
        with pytest.raises(dl.UnsupportedConceptError, match="HasValue"):
            dl.concept_satisfiable(concept, tbox)
    with pytest.raises(dl.UnsupportedConceptError, match="HasValue"):
        dl.abox_consistent(dl.ABox(), inclusion)


def test_an_inverse_role_valued_value_restriction_is_refused_as_i_too():
    # The role field is as untyped here as in any restriction, so the message
    # says BOTH things true of it: it is a value restriction, and its role is an
    # InverseRole -- the I of SHIQ.
    with pytest.raises(dl.UnsupportedConceptError) as info:
        dl.concept_satisfiable(dl.HasValue(dl.InverseRole("r"), "a"))
    message = str(info.value)
    assert "InverseRole" in message and "HasValue" in message
    # ... while the FOL route renders it, which is why the message points there
    assert dl.concept_to_fol(
        dl.HasValue(dl.InverseRole("r"), "a")).to_unicode_str() == "r(a, x)"


# --------------------------------------------------------------------------- #
# F4: concept_satisfiable's anonymous root is not called "a".
# --------------------------------------------------------------------------- #

def test_the_anonymous_root_does_not_collide_with_an_individual_named_a():
    # Hand-derived counterexample. tbox = D ⊑ ¬C, query =
    # C ⊓ ∃r.{a} ⊓ ∀r.D. It IS satisfiable: take Δ = {d, a} with d ∈ C,
    # r = {(d, a)}, a ∈ D, a ∉ C -- every axiom holds and d witnesses the
    # query.
    #
    # With the root node literally named "a" (what concept_satisfiable did
    # until 0.30.0) a value-rule would have added the SELF-LOOP (a, r, a), ∀r.D
    # would have put D on a, D ⊑ ¬C would have put ¬C on a, and ¬C would clash
    # with the query's C -- reported UNSATISFIABLE. The root stands for "SOME
    # element", existentially quantified; an individual name denotes a FIXED
    # one, and identifying the two adds an equation the query never stated.
    #
    # The FOL route answers it; the tableau refuses the value restriction. The
    # root's name is still not "a" (next test), so that no later rule that names
    # an individual can meet the collision.
    tbox = dl.TBox().add(D, dl.Not(C))
    query = dl.And(dl.And(C, dl.HasValue("r", "a")), dl.ForAll("r", D))
    _fol_answers_tableau_refuses(query, tbox, satisfiable=True)


def test_the_root_is_named_apart_from_individuals_and_from_generated_nodes():
    from unicode_fol_kit.dl.tableau import _ROOT_NAME, _Branch, _blocked

    assert _ROOT_NAME == "_root"
    assert _ROOT_NAME != "a"
    # a named node (a str), not a generated one, so _blocked treats it as the named
    # node it is: never blocked, however small its label and however large an
    # earlier generated node's.
    assert isinstance(_ROOT_NAME, str)
    branch = _Branch()
    first = branch.fresh()                              # a generated node
    branch.label[first].update({A, B})
    branch.add_node(_ROOT_NAME)
    branch.label[_ROOT_NAME].add(A)
    assert _blocked(branch, _ROOT_NAME) is False


# --------------------------------------------------------------------------- #
# F3: a NAMED node may not block a generated one.
# --------------------------------------------------------------------------- #

def test_a_named_node_may_not_block_a_generated_one():
    # Subset blocking's soundness argument is about the UNRAVELLING: a blocked
    # node is interpreted by its BLOCKER. That is legitimate only while no
    # formula can distinguish two elements satisfying the same concepts -- and a
    # negative role assertion ¬r(x, a) can: it names two elements. If a
    # generated successor of x were collapsed onto the NAMED node a, x would
    # acquire an r-edge to a in the model while no such edge was ever added to
    # the graph, so no clash would fire.
    #
    # The knowledge base: ⊤ ⊑ ∃r.⊤ forces every element to have an
    # r-successor, and ¬r(x, a) forbids x's successor being a. a is a named
    # node whose label is a superset of the generated successor's (both carry
    # only the internalised GCI), so before 0.30.0 a was an eligible blocker.
    #
    # It IS consistent: Δ = {x, a, m} with r = {(x, m), (m, m), (a, a)}
    # satisfies ⊤ ⊑ ∃r.⊤ and leaves x with no r-edge to a. Both routes must
    # say so.
    #
    # Said plainly, because it matters for what this test is worth: the
    # VERDICT here is the same under the old condition too. Subset blocking
    # stops an expansion whose every concept the blocker already carries, so
    # a clash hidden at the blocked node fires at the blocker instead; what
    # the old condition broke is the MODEL the branch stands for, not the
    # yes/no. This case is therefore a regression guard over the scenario and
    # over the two routes agreeing on it; the test that DISCRIMINATES the two
    # conditions is the next one, which asks _blocked directly.
    tbox = dl.TBox().add(dl.Top(), dl.Exists("r", dl.Top()))
    abox = (dl.ABox()
            .assert_negative_role("x", "a", "r")
            .assert_concept("a", dl.Top()))
    assert dl.abox_consistent(abox, tbox) is True
    kb = dl.kb_to_fol(tbox, abox)
    assert _status(FNot(kb.formula), kb.axioms) == "refuted"
    # And the INCONSISTENT sibling, so the condition is not vacuous: make the
    # forbidden edge one the branch really has.
    clash = (dl.ABox()
             .assert_negative_role("x", "a", "r")
             .assert_role("x", "a", "r"))
    assert dl.abox_consistent(clash, tbox) is False
    kb2 = dl.kb_to_fol(tbox, clash)
    assert _status(FNot(kb2.formula), kb2.axioms) == "proved"


def test_only_a_generated_node_is_an_eligible_blocker():
    # The condition itself, at the level it is written: _blocked never reports
    # a generated node blocked by a NAMED one, however large that node's label.
    from unicode_fol_kit.dl.tableau import _Branch, _blocked

    branch = _Branch()
    branch.add_node("alice")                      # a named ABox individual
    branch.label["alice"].update({A, B})
    generated = branch.fresh()                    # a generated node
    branch.label[generated].add(A)
    assert _blocked(branch, generated) is False, (
        "a NAMED node must not block a generated one -- see _blocked")
    # ... while an earlier GENERATED node with a superset label still does,
    # which is what keeps termination unchanged.
    other = branch.fresh()                        # a later generated node
    branch.label[other].add(A)
    assert _blocked(branch, other) is True
    # and a named node is itself never blocked, as before
    assert _blocked(branch, "alice") is False


def test_a_value_fillers_individual_is_in_the_formula_but_not_in_individuals():
    """The TBox can name an individual, and ``kb.individuals`` still means the
    ABox's.

    Hand-derived from the direct semantics. ``C ⊑ ∃r.{a}`` with ``C(b)`` is
    ``∀x (C(x) → r(x, a)) ∧ C(b)``: the constant ``a`` stands in the formula,
    yet nothing in the knowledge base ASSERTS anything of ``a`` — it is a name
    the terminology mentions, not an individual the ABox describes. Three
    consequences, all checked here:

    * ``kb.individuals == ("b",)``, the field's documented scope (the
      ``individual_positions`` scan over the ABox), even though the formula
      carries both constants — and the tableau's own scan of the ABox
      (``_abox_individual_names``, what ``instance_retrieval`` and
      ``realize_all`` sweep) is that same set, ``{"b"}``: enumerating ``a`` as
      well would make a sweep answer a retrieval question the FOL route cannot
      be asked, since the ABox entails nothing about ``a``'s membership;
    * the edge is nonetheless ENTAILED, and the FOL route says so: ``r(b, a)``
      is proved from the premises, ``r(a, b)`` is refuted, and ``b : ∃r.{a}`` is
      proved;
    * the in-house tableau does not decide the question — the TBox holds a
      value restriction — and every entry point raises.

    This is also why ``tests/test_owl_corpus.py`` scopes its read-back scan
    on the image's own constants rather than on ``kb.individuals``: that field
    is empty for a value restriction, so a guard reading it would hand the
    read-back check a CamelCase name the documented vocabulary limit covers.
    """
    from unicode_fol_kit.dl.tableau import _abox_individual_names

    tbox = dl.TBox().add(C, dl.HasValue("r", "a"))
    abox = dl.ABox().assert_concept("b", C)
    kb = dl.kb_to_fol(tbox, abox)
    assert kb.formula.to_unicode_str() == "∀x (C(x) → r(x, a)) ∧ C(b)"
    assert kb.individuals == ("b",)
    assert sorted(_abox_individual_names(abox)) == ["b"]
    assert sorted({node.name for node in kb.formula.walk()
                   if isinstance(node, Constant)}) == ["a", "b"]
    assert _status(Atom("r", (Constant("b"), Constant("a"))),
                   kb.premises) == "proved"
    assert _status(Atom("r", (Constant("a"), Constant("b"))),
                   kb.premises) == "refuted"
    member = dl.abox_to_fol(dl.ABox().assert_concept("b", dl.HasValue("r", "a")))
    assert _status(member, kb.premises) == "proved"
    _refuses(lambda: dl.instance_check(abox, "b", dl.HasValue("r", "a"), tbox))
    _refuses(lambda: dl.instance_retrieval(abox, dl.HasValue("r", "a"), tbox))
    _refuses(lambda: dl.realize_all(abox, [C], tbox))


# --------------------------------------------------------------------------- #
# The refusal itself: everywhere a value restriction can sit, every entry point.
# --------------------------------------------------------------------------- #

HV = dl.HasValue("r", "a")

#: (label, call) — each puts a value restriction in a different POSITION.
_POSITIONS = [
    ("the queried concept", lambda: dl.concept_satisfiable(HV)),
    ("nested in the queried concept",
     lambda: dl.concept_satisfiable(dl.Exists("s", dl.And(A, dl.ForAll("s", HV))))),
    ("negated in the queried concept", lambda: dl.concept_satisfiable(dl.Not(HV))),
    ("the sub-concept of an inclusion",
     lambda: dl.concept_satisfiable(A, dl.TBox().add(HV, B))),
    ("the super-concept of an inclusion",
     lambda: dl.concept_satisfiable(A, dl.TBox().add(A, HV))),
    ("an equivalence",
     lambda: dl.concept_satisfiable(A, dl.TBox().add_equivalence(A, HV))),
    ("a domain filler",
     lambda: dl.concept_satisfiable(A, dl.TBox().add_role_domain("p", HV))),
    ("a range filler",
     lambda: dl.concept_satisfiable(A, dl.TBox().add_role_range("p", HV))),
    ("an inclusion, asked of abox_consistent",
     lambda: dl.abox_consistent(dl.ABox(), dl.TBox().add(A, dl.Not(HV)))),
    ("a domain filler, asked of abox_consistent",
     lambda: dl.abox_consistent(dl.ABox(), dl.TBox().add_role_domain("p", HV))),
    ("a range filler, asked of abox_consistent",
     lambda: dl.abox_consistent(dl.ABox(), dl.TBox().add_role_range("p", HV))),
    ("a positive ABox assertion",
     lambda: dl.abox_consistent(dl.ABox().assert_concept("x", HV))),
    ("a negated ABox assertion",
     lambda: dl.abox_consistent(dl.ABox().assert_concept("x", dl.Not(HV)))),
    ("a nested ABox assertion",
     lambda: dl.abox_consistent(
         dl.ABox().assert_concept("x", dl.And(A, dl.AtLeast(2, "s", HV))))),
]

#: (label, call) — each ENTRY POINT, with the value restriction where that
#: entry point would first meet it.
_ENTRY_POINTS = [
    ("concept_satisfiable", lambda: dl.concept_satisfiable(A, dl.TBox().add(A, HV))),
    ("concept_unsatisfiable", lambda: dl.concept_unsatisfiable(HV)),
    ("subsumes", lambda: dl.subsumes(HV, A)),
    ("subsumes, in the TBox", lambda: dl.subsumes(A, B, dl.TBox().add(A, HV))),
    ("equivalent", lambda: dl.equivalent(A, HV)),
    ("abox_consistent", lambda: dl.abox_consistent(dl.ABox().assert_concept("x", HV))),
    ("instance_check, the concept",
     lambda: dl.instance_check(dl.ABox().assert_concept("x", A), "x", HV)),
    ("instance_check, the ABox",
     lambda: dl.instance_check(dl.ABox().assert_concept("x", HV), "x", A)),
    ("instance_retrieval", lambda: dl.instance_retrieval(dl.ABox(), HV)),
    ("instance_retrieval, the TBox",
     lambda: dl.instance_retrieval(dl.ABox(), A, dl.TBox().add(A, HV))),
    ("realize, the vocabulary", lambda: dl.realize(dl.ABox(), "x", [HV])),
    ("realize_all, the vocabulary", lambda: dl.realize_all(dl.ABox(), [HV])),
    ("classify, no names", lambda: dl.classify(dl.TBox().add_role_range("p", HV))),
    ("classify, one name", lambda: dl.classify(dl.TBox().add(A, HV))),
    ("classify, two names", lambda: dl.classify(dl.TBox().add(A, B).add(B, HV))),
    ("classify, an extra concept", lambda: dl.classify(dl.TBox().add(A, B), [HV])),
]


@pytest.mark.parametrize("label, call", _POSITIONS + _ENTRY_POINTS,
                         ids=[c[0] for c in _POSITIONS + _ENTRY_POINTS])
def test_the_tableau_refuses_a_value_restriction_wherever_it_sits(label, call):
    with pytest.raises(dl.UnsupportedConceptError) as info:
        call()
    message = str(info.value)
    assert "HasValue" in message and "ObjectHasValue" in message, message


def test_the_refusal_says_why_and_names_only_routes_that_decide_it():
    # Same wording style as the Nominal refusal (named construct, "outside
    # ALCHQ", "no in-house tableau rule decides"), plus the reason -- a nominal
    # whose edge back to a named node subset blocking does not cover -- and the
    # two routes that DO decide a value restriction: the FOL image, and the
    # external reasoner (the test below runs every dl.external_* entry point).
    with pytest.raises(dl.UnsupportedConceptError) as info:
        dl.concept_satisfiable(HV)
    message = str(info.value)
    for fragment in ("outside ALCHQ", "no in-house tableau rule decides it",
                     "NOMINAL", "subset blocking", "'a'", "∃r.{a}",
                     "dl.kb_to_fol", "api.prove", "dl.external_"):
        assert fragment in message, f"the refusal lacks {fragment!r}: {message}"
    with pytest.raises(dl.UnsupportedConceptError) as nominal:
        dl.concept_satisfiable(dl.Nominal("a"))
    assert "outside ALCHQ" in str(nominal.value)
    assert "no in-house tableau rule decides" in str(nominal.value)


def test_a_value_restriction_over_a_built_in_property_keeps_its_own_refusal():
    # The built-in role is the more specific diagnosis (and has a rewrite):
    # ∃owl:topObjectProperty.{a} holds of EVERY element, so it is ⊤. The role
    # check runs before the value-restriction refusal. (See
    # tests/test_dl_reserved_roles.py for the whole battery.)
    with pytest.raises(dl.RoleExpressionError, match="dl.Top"):
        dl.concept_satisfiable(dl.HasValue("owl:topObjectProperty", "a"))


def test_the_construct_itself_is_untouched_by_the_refusal():
    # Only the in-house DECISION is gone: the node, its image, both readers and
    # both writers (tested above) and the external route all still work, and a
    # value-restriction-free question about the same TBox is still decided.
    tbox = dl.TBox().add(C, dl.Not(D))
    assert dl.concept_satisfiable(dl.And(C, D), tbox) is False
    assert dl.HasValue("r", "a") == dl.HasValue("r", "a")
    assert dl.concept_to_fol(HV).to_unicode_str() == "r(x, a)"


# --------------------------------------------------------------------------- #
# The counterexample that no patch to the removed value-rule could repair.
# --------------------------------------------------------------------------- #

def test_the_two_axiom_counterexample_the_fol_route_proves_and_the_tableau_refuses():
    # Two axioms:  Asym(s)   and   range(s) = ∃s.∃s.{b}.
    #
    # Hand-derived, in ANY model. Take an s-edge x → y. The range axiom puts y
    # in ∃s.∃s.{b}, so there are y → z and z → b (z is in ∃s.{b}). The edge
    # z → b is an s-edge too, so the range axiom puts its target b in
    # ∃s.∃s.{b} as well: b → w and w → b. That is s(b, w) together with
    # s(w, b), which asymmetry forbids (w = b would be the loop s(b, b), which
    # asymmetry entails to be absent). So NO s-edge exists and ∃s.⊤ is
    # UNSATISFIABLE with respect to the two axioms.
    #
    # The tableau with a value-rule answered "satisfiable": among what it built
    # was _root → _x1 → _x2 → b → _x3, and _x3's label equals _x2's, so _x3 is
    # BLOCKED; the value-rule never fired on it, the edge _x3 → b was never
    # added, and the asymmetry clash s(b, _x3), s(_x3, b) was never seen. A
    # value restriction gives a generated node an edge BACK to a named one, and
    # subset blocking (and the exactness argument for the role box's clash
    # conditions, which reads the model off the unravelled tree) assumes that
    # never happens. See "Value restrictions (ObjectHasValue)" in dl.tableau.
    range_filler = dl.Exists("s", dl.HasValue("s", "b"))           # ∃s.∃s.{b}
    tbox = dl.TBox().add_asymmetric_role("s").add_role_range("s", range_filler)
    query = dl.Exists("s", dl.Top())

    # The FOL route proves the hand-derived verdict: ∃s.⊤ is unsatisfiable ...
    assert _fol_says_satisfiable(query, tbox) is False
    # ... and so is the knowledge base that asserts a witness.
    abox = dl.ABox().assert_concept("x", query)
    kb = dl.kb_to_fol(tbox, abox)
    assert _status(FNot(kb.formula), kb.axioms) == "proved"
    # The in-house tableau refuses, as a value restriction, both questions.
    _refuses(lambda: dl.concept_satisfiable(query, tbox))
    _refuses(lambda: dl.abox_consistent(abox, tbox))

    # Both axioms are needed. Without the asymmetry, one reflexive element is a
    # model (Δ = {b}, s = {(b, b)}: b has an s-successor b that is in ∃s.{b},
    # so b ∈ ∃s.∃s.{b}); without the range axiom a single s-edge is one.
    assert _fol_says_satisfiable(query, dl.TBox().add_role_range("s", range_filler)) is True
    assert _fol_says_satisfiable(query, dl.TBox().add_asymmetric_role("s")) is True
    # ... and the tableau still decides the half that holds no value restriction.
    assert dl.concept_satisfiable(query, dl.TBox().add_asymmetric_role("s")) is True


# --------------------------------------------------------------------------- #
# The second independent oracle: every external entry point answers it.
# --------------------------------------------------------------------------- #

_HERMIT = pytest.mark.skipif(not _owl_reasoner.available(),
                             reason="owlready2 is not installed ([owl] extra)")


@_HERMIT
@pytest.mark.parametrize("concept, satisfiable", [
    (dl.HasValue("r", "a"), True),
    (dl.And(dl.HasValue("r", "a"), dl.Not(dl.HasValue("r", "a"))), False),
    (dl.And(dl.HasValue("r", "a"), dl.ForAll("r", dl.Bottom())), False),
], ids=["alone", "with-its-negation", "with-an-empty-value-restriction"])
def test_hermit_decides_what_the_tableau_refuses(concept, satisfiable):
    # owlready2 spells a value restriction `prop.value(individual)`. An oracle
    # that silently dropped the construct would agree with everything, so the
    # check is the same hand-derived verdict asked of HermiT -- and of the FOL
    # route -- while the in-house tableau raises.
    assert dl.external_concept_satisfiable(concept) is satisfiable
    assert _fol_says_satisfiable(concept) is satisfiable
    _refuses(lambda: dl.concept_satisfiable(concept))


@_HERMIT
def test_hermit_agrees_on_the_two_axiom_counterexample():
    # ∃s.⊤ is unsatisfiable wrt Asym(s) and range(s) = ∃s.∃s.{b}: derived in
    # test_the_two_axiom_counterexample_... above. The oracle independent of
    # both the tableau and the FOL image says the same.
    tbox = (dl.TBox().add_asymmetric_role("s")
            .add_role_range("s", dl.Exists("s", dl.HasValue("s", "b"))))
    assert dl.external_concept_satisfiable(dl.Exists("s", dl.Top()), tbox) is False


def _positive_abox():
    """``x : ∃r.{a} ⊓ ∀r.C`` — x has the r-successor a, and every r-successor is
    a C, so a ∈ C; nothing makes x a C."""
    return dl.ABox().assert_concept(
        "x", dl.And(dl.HasValue("r", "a"), dl.ForAll("r", C)))


#: Every ``dl.external_*`` entry point, with the hand-derived answer to a
#: question about a value restriction. The refusal message names
#: ``dl.external_*`` as a route that decides one; this is what makes it true of
#: ALL nine and not just the one the message was written next to.
_EXTERNAL = [
    ("external_concept_satisfiable",
     lambda: dl.external_concept_satisfiable(dl.HasValue("r", "a")), True),
    ("external_concept_unsatisfiable",
     lambda: dl.external_concept_unsatisfiable(
         dl.And(dl.HasValue("r", "a"), dl.ForAll("r", dl.Bottom()))), True),
    ("external_subsumes",
     # x has the r-successor a, every r-successor is a C, so x has an r-successor
     # in C.
     lambda: dl.external_subsumes(
         dl.And(dl.HasValue("r", "a"), dl.ForAll("r", C)), dl.Exists("r", C)), True),
    ("external_equivalent",
     # the one-point reduction: ∃r.{a} and ∃r.{a}-as-a-nominal have the same
     # models
     lambda: dl.external_equivalent(dl.HasValue("r", "a"),
                                    dl.Exists("r", dl.Nominal("a"))), True),
    ("external_abox_consistent",
     lambda: dl.external_abox_consistent(
         _positive_abox().assert_concept("a", dl.Not(C))), False),
    ("external_instance_check",
     lambda: dl.external_instance_check(_positive_abox(), "a", C), True),
    ("external_instance_retrieval",
     # a is named inside a concept of the ABox, and an individual named in an
     # assertion is an individual of the ABox wherever it stands, so a IS swept:
     # a is a C (derived above), x is not.
     lambda: dl.external_instance_retrieval(_positive_abox(), C), {"a"}),
    ("external_realize",
     lambda: dl.external_realize(_positive_abox(), "a", [A, C]), [C]),
    ("external_realize_all",
     # x belongs to neither A nor C; a is a C and is not entailed to be an A
     lambda: dl.external_realize_all(_positive_abox(), [A, C]), {"x": [], "a": [C]}),
]


def test_the_external_table_covers_every_external_entry_point():
    # "dl.external_*" in the refusal message is a claim about ALL of them, so the
    # table above must not be a hand-kept subset: a tenth external entry point
    # added later fails HERE until it is given a value-restriction question.
    # (No reasoner is started: this reads the names only.)
    assert {entry[0] for entry in _EXTERNAL} == {
        name for name in dl.__all__ if name.startswith("external_")}


@_HERMIT
@pytest.mark.parametrize("name, call, expected", _EXTERNAL, ids=[c[0] for c in _EXTERNAL])
def test_every_external_entry_point_decides_a_value_restriction(name, call, expected):
    assert call() == expected
