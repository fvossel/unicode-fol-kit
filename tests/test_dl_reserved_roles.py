r"""A role the kit cannot read as an ordinary role is refused, by name, everywhere.

Four families of "not an ordinary role name" used to be refused on SOME routes
and answered as if they were ordinary on the others, which is the one thing two
routes of this kit must never do to the same question:

* the OWL 2 BUILT-IN property names (``owl:topObjectProperty`` — the universal
  property, every pair — and ``owl:bottomObjectProperty`` — the empty one, both
  spellings, plus the two data twins). ``parse_owl_functional`` and the
  ``TBox.add_*`` builders refused them; a class expression, an ABox assertion,
  the glyph parser and the Manchester class-expression parser treated them as an
  uninterpreted role of that name, so ``A ⊓ ∀owl:topObjectProperty.¬A`` was
  satisfiable (under the universal reading every element is related to itself,
  so it is not);
* a role called ``=`` or ``≠``, which the FOL image renders as the equality atom;
* an ``InverseRole`` where a plain name is required — and the advice for it, which
  said "pass r instead" for every axiom although that is the SAME axiom only
  for five of them;
* a stored role-box entry that is no role at all (a ``TBox`` built through the
  dataclass constructor, or mutated in place), which only the FOL route checked.

The policy: builders never refuse an axiom KIND; the QUERY (the tableau's shared
guard) and the TRANSLATION (``kb_to_fol`` and friends) refuse a role they cannot
read, and the parsers refuse it on the way in. Every expected value below is
hand-derived from the OWL 2 direct semantics in the comment above it.
"""

import pytest

import unicode_logic_kit.dl as dl
from unicode_logic_kit import api
from unicode_logic_kit.dl import owl_reasoner as _owl
from unicode_logic_kit.dl.tableau import RESERVED_ROLE_SPELLINGS
from unicode_logic_kit.fol.nodes import (
    And as FAnd, Atom, Implies, Iff, Not as Not_, Quantifier, Variable,
)

A = dl.Atomic("A")
TIMEOUT_MS = 30000

# Every spelling of the two OBJECT built-ins: the abbreviation and the full IRI.
TOPS = ["owl:topObjectProperty", "http://www.w3.org/2002/07/owl#topObjectProperty"]
BOTTOMS = ["owl:bottomObjectProperty", "http://www.w3.org/2002/07/owl#bottomObjectProperty"]


def test_the_spellings_under_test_are_all_reserved():
    # Guards the parametrisation: a name that stopped being reserved would make
    # every case below pass for the wrong reason.
    assert all(name in RESERVED_ROLE_SPELLINGS for name in TOPS + BOTTOMS)


# --------------------------------------------------------------------------- #
# Query time: the tableau's shared guard, over every place a role can occur.
# --------------------------------------------------------------------------- #

# (constructor, what the message must say to use instead).
#
# The universal property U relates every pair. So  ∃U.C  and  ≥n U.C  and
# ∀U.C  and  ≤n U.C  talk about the WHOLE domain — a global statement no ALCHQ
# concept makes — and the global "every element is in C" is the GCI ⊤ ⊑ C.
# The one exception is HasValue: every element is related to the individual by
# U, so ∃U.{a} holds of EVERY element (⊤).
# The empty property E relates no pair. So ∃E.C, ≥n E.C (n ≥ 1) and ∃E.{a} are
# unsatisfiable (⊥), while ∀E.C, ≤n E.C and ≥0 E.C hold of everything (⊤).
_TOP_SHAPES = [
    (lambda r: dl.Exists(r, A), "WHOLE domain"),
    (lambda r: dl.ForAll(r, A), "WHOLE domain"),
    (lambda r: dl.AtLeast(2, r, A), "WHOLE domain"),
    (lambda r: dl.AtMost(1, r, A), "WHOLE domain"),
    (lambda r: dl.HasValue(r, "a"), "dl.Top()"),
]
_BOTTOM_SHAPES = [
    (lambda r: dl.Exists(r, A), "dl.Bottom()"),
    (lambda r: dl.AtLeast(1, r, A), "dl.Bottom()"),
    (lambda r: dl.HasValue(r, "a"), "dl.Bottom()"),
    (lambda r: dl.ForAll(r, A), "dl.Top()"),
    (lambda r: dl.AtMost(3, r, A), "dl.Top()"),
    (lambda r: dl.AtLeast(0, r, A), "dl.Top()"),
]


@pytest.mark.parametrize("name", TOPS)
@pytest.mark.parametrize("build, remedy", _TOP_SHAPES)
def test_the_universal_property_is_refused_in_a_restriction(name, build, remedy):
    concept = build(name)
    with pytest.raises(dl.RoleExpressionError) as info:
        dl.concept_satisfiable(concept)
    message = str(info.value)
    assert "BUILT-IN" in message and repr(name) in message
    assert remedy in message, message


@pytest.mark.parametrize("name", BOTTOMS)
@pytest.mark.parametrize("build, remedy", _BOTTOM_SHAPES)
def test_the_empty_property_is_refused_in_a_restriction(name, build, remedy):
    concept = build(name)
    with pytest.raises(dl.RoleExpressionError) as info:
        dl.concept_satisfiable(concept)
    message = str(info.value)
    assert "BUILT-IN" in message and repr(name) in message
    assert remedy in message, message


def test_the_measured_wrong_answer_is_now_a_refusal():
    # A ⊓ ∀U.¬A with U the universal property: every element is U-related to
    # itself, so the element in A must be in ¬A as well — UNSATISFIABLE. As an
    # ordinary role the same text was satisfiable (True), the wrong answer.
    concept = dl.And(A, dl.ForAll("owl:topObjectProperty", dl.Not(A)))
    with pytest.raises(dl.RoleExpressionError, match="owl:topObjectProperty"):
        dl.concept_satisfiable(concept)


_EVERY_ENTRY_POINT = [
    ("concept_satisfiable", lambda c, t, ab: dl.concept_satisfiable(c, t)),
    ("concept_unsatisfiable", lambda c, t, ab: dl.concept_unsatisfiable(c, t)),
    ("subsumes", lambda c, t, ab: dl.subsumes(c, A, t)),
    ("equivalent", lambda c, t, ab: dl.equivalent(A, c, t)),
    ("abox_consistent", lambda c, t, ab: dl.abox_consistent(ab, t)),
    ("instance_check", lambda c, t, ab: dl.instance_check(ab, "a", A, t)),
    ("instance_retrieval", lambda c, t, ab: dl.instance_retrieval(ab, A, t)),
    ("realize", lambda c, t, ab: dl.realize(ab, "a", [A], t)),
    ("realize_all", lambda c, t, ab: dl.realize_all(ab, [A], t)),
    ("classify", lambda c, t, ab: dl.classify(t if t is not None else dl.TBox())),
]
_BAD = dl.Exists("owl:bottomObjectProperty", dl.Top())
_TAKES_NO_QUERY_CONCEPT = {"abox_consistent", "instance_check", "instance_retrieval",
                           "realize", "realize_all", "classify"}
_READS_NO_ABOX = {"concept_satisfiable", "concept_unsatisfiable", "subsumes",
                  "equivalent", "classify"}


@pytest.mark.parametrize("where", ["query", "inclusion", "domain", "range", "assertion"])
@pytest.mark.parametrize("entry, call", _EVERY_ENTRY_POINT, ids=[e[0] for e in _EVERY_ENTRY_POINT])
def test_every_entry_point_refuses_a_built_in_wherever_it_is_stored(where, entry, call):
    # The same bad class expression, stored in each place a class expression can
    # be stored, and asked of every public entry point of the package. (classify
    # reads the TBox alone, and a query concept is not stored anywhere, so those
    # two skip the cells they cannot reach.)
    tbox, abox, concept = dl.TBox(), dl.ABox().assert_concept("a", A), A
    if where == "query":
        concept = _BAD
        tbox.add(A, A)
    elif where == "inclusion":
        tbox.add(A, _BAD)
    elif where == "domain":
        tbox.add_role_domain("r", _BAD)
    elif where == "range":
        tbox.add_role_range("r", _BAD)
    else:
        abox.assert_concept("b", _BAD)
    if where == "query" and entry in _TAKES_NO_QUERY_CONCEPT:
        pytest.skip("this entry point takes no query concept")
    if where == "assertion" and entry in _READS_NO_ABOX:
        pytest.skip("this entry point reads no ABox")
    with pytest.raises(dl.RoleExpressionError, match="BUILT-IN"):
        call(concept, tbox, abox)


# --------------------------------------------------------------------------- #
# ABox assertions.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("name", BOTTOMS)
def test_asserting_the_empty_property_is_refused_with_its_consequence(name):
    # (a, b) : E with E the EMPTY property holds in no interpretation, so the
    # knowledge base is INCONSISTENT. As an ordinary role it was consistent.
    abox = dl.ABox().assert_role("a", "b", name)
    with pytest.raises(dl.RoleExpressionError) as info:
        dl.abox_consistent(abox)
    assert "INCONSISTENT" in str(info.value)
    assert "assert_concept('a', dl.Bottom())" in str(info.value)


@pytest.mark.parametrize("name", TOPS)
def test_denying_the_universal_property_is_refused_with_its_consequence(name):
    # ¬U(a, b) with U the universal property holds in no interpretation either.
    abox = dl.ABox().assert_negative_role("a", "b", name)
    with pytest.raises(dl.RoleExpressionError) as info:
        dl.abox_consistent(abox)
    assert "INCONSISTENT" in str(info.value)


@pytest.mark.parametrize("build", [
    # U(a, b) and ¬E(a, b) hold in EVERY interpretation: they constrain nothing.
    lambda: dl.ABox().assert_role("a", "b", "owl:topObjectProperty"),
    lambda: dl.ABox().assert_negative_role("a", "b", "owl:bottomObjectProperty"),
])
def test_an_assertion_that_always_holds_is_refused_as_a_no_op_to_drop(build):
    with pytest.raises(dl.RoleExpressionError, match="constrains nothing: drop it"):
        dl.abox_consistent(build())


def test_a_data_assertion_over_a_built_in_is_refused_too():
    # The data layer is covered the same way: owl:topDataProperty relates every
    # object to every data value, so "a has the value 1 for it" always holds.
    abox = dl.ABox().assert_data("a", "owl:topDataProperty",
                                 dl.Literal("1", "xsd:integer"))
    with pytest.raises(dl.RoleExpressionError, match="constrains nothing"):
        dl.abox_consistent(abox)
    with pytest.raises(dl.RoleExpressionError, match="constrains nothing"):
        dl.kb_to_fol(None, abox)


def test_an_inverse_role_in_an_assertion_is_refused_with_the_true_remedy():
    # r⁻(a, b) holds iff r(b, a): the remedy is to swap the individuals, and it
    # is exactly equivalent.
    abox = dl.ABox().assert_role("a", "b", dl.InverseRole("r"))
    with pytest.raises(dl.RoleExpressionError, match="swap the two individuals"):
        dl.abox_consistent(abox)


# --------------------------------------------------------------------------- #
# Translation time: the FOL image refuses the same names.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("call", [
    lambda: dl.concept_to_fol(_BAD),
    lambda: dl.subsumption_to_fol(A, _BAD),
    lambda: dl.subsumption_to_fol(_BAD, A),
    lambda: dl.tbox_to_fol(dl.TBox().add(A, _BAD)),
    lambda: dl.kb_to_fol(dl.TBox().add(A, _BAD)),
    lambda: dl.kb_to_fol(dl.TBox().add_role_range("r", _BAD)),
    lambda: dl.kb_to_fol(None, dl.ABox().assert_concept("a", _BAD)),
    lambda: dl.abox_to_fol(dl.ABox().assert_role("a", "b", "owl:bottomObjectProperty")),
    lambda: dl.kb_to_fol(None, dl.ABox().assert_negative_role("a", "b", "owl:topObjectProperty")),
    lambda: dl.concept_to_modal(dl.Exists("owl:topObjectProperty", A)),
    lambda: dl.concept_to_fol(dl.DataExists("owl:topDataProperty", dl.Datatype("xsd:integer"))),
])
def test_the_translation_refuses_a_built_in(call):
    # Before: concept_to_fol printed '∃x0 (owl:bottomObjectProperty(x, x0) ∧ x0
    # = x0)', an uninterpreted predicate — satisfiable, where the restriction
    # over the EMPTY property is not.
    with pytest.raises(dl.RoleExpressionError, match="BUILT-IN"):
        call()


# --------------------------------------------------------------------------- #
# The parsers refuse it on the way in, as parse_owl_functional always did.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("text", [
    "∃owl:topObjectProperty.A", "∀owl:bottomObjectProperty.A",
    "≥2 owl:topObjectProperty.A", "≤1 owl:bottomObjectProperty.A",
])
def test_the_glyph_parser_refuses_a_built_in(text):
    with pytest.raises(dl.ConceptSyntaxError, match="BUILT-IN"):
        dl.parse_concept(text)
    assert dl.parse_concept(text.replace("owl:topObjectProperty", "r")
                            .replace("owl:bottomObjectProperty", "r")) is not None


@pytest.mark.parametrize("text", [
    "owl:topObjectProperty some A", "owl:bottomObjectProperty only A",
    "owl:topObjectProperty min 2 A", "owl:bottomObjectProperty max 1 A",
    "owl:topObjectProperty exactly 1 A", "owl:topObjectProperty value a",
    "owl:topDataProperty some xsd:integer",
])
def test_the_manchester_class_expression_parser_refuses_a_built_in(text):
    with pytest.raises(dl.ManchesterSyntaxError, match="BUILT-IN"):
        dl.parse_manchester(text)


@pytest.mark.parametrize("text", [
    "ObjectSomeValuesFrom(owl:topObjectProperty A)",
    "ObjectHasValue(owl:bottomObjectProperty a)",
])
def test_the_functional_parser_still_refuses_a_built_in(text):
    with pytest.raises(dl.OwlFunctionalUnsupportedError, match="BUILT-IN"):
        dl.parse_owl_functional_class_expression(text)


def test_one_expression_is_refused_by_every_route():
    # "The SAME expression is refused by one route and answered by another" was
    # the finding. One expression, every route that reads or decides it.
    expression = "owl:bottomObjectProperty"
    routes = [
        (dl.RoleExpressionError, lambda: dl.concept_satisfiable(dl.Exists(expression, A))),
        (dl.RoleExpressionError, lambda: dl.concept_to_fol(dl.Exists(expression, A))),
        (dl.RoleExpressionError, lambda: dl.to_owl_functional_class_expression(
            dl.Exists(expression, A))),
        (dl.ConceptSyntaxError, lambda: dl.parse_concept(f"∃{expression}.A")),
        (dl.ManchesterSyntaxError, lambda: dl.parse_manchester(f"{expression} some A")),
        (dl.OwlFunctionalUnsupportedError, lambda: dl.parse_owl_functional_class_expression(
            f"ObjectSomeValuesFrom({expression} A)")),
        # The external route's guard runs BEFORE any HermiT call (an empty
        # vocabulary reaches none), so this starts no JVM.
        (dl.RoleExpressionError, lambda: dl.external_realize(
            dl.ABox(), "a", [], dl.TBox().add(A, dl.Exists(expression, A)))),
    ]
    for exception, call in routes:
        with pytest.raises(exception, match="BUILT-IN"):
            call()


def test_the_writer_refuses_what_the_reader_would_refuse():
    # A document this module wrote must be one it reads. The reader refuses a
    # built-in in every restriction and assertion position, so the writer does.
    with pytest.raises(dl.RoleExpressionError, match="BUILT-IN"):
        dl.to_owl_functional(dl.TBox().add(A, _BAD), dl.ABox())
    with pytest.raises(dl.RoleExpressionError, match="BUILT-IN"):
        dl.to_owl_functional(dl.TBox(), dl.ABox().assert_role("a", "b", "owl:topObjectProperty"))


# --------------------------------------------------------------------------- #
# A role called "=" or "≠".
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("name", ["=", "≠"])
@pytest.mark.parametrize("call", [
    lambda n: dl.TBox().add_functional_role(n),
    lambda n: dl.TBox().add_role_inclusion(n, "Q"),
    lambda n: dl.TBox().add_role_inclusion("Q", n),
    lambda n: dl.TBox().add_role_domain(n, A),
    lambda n: dl.TBox().add_role_chain([n, "Q"], "R"),
    lambda n: dl.concept_to_fol(dl.HasValue(n, "a")),
    lambda n: dl.concept_satisfiable(dl.Exists(n, A)),
    lambda n: dl.abox_to_fol(dl.ABox().assert_role("a", "b", n)),
    lambda n: dl.abox_consistent(dl.ABox().assert_negative_role("a", "b", n)),
])
def test_a_role_named_like_an_equality_atom_is_refused(name, call):
    # The FOL image renders an atom named '=' as the equality of its arguments
    # (that is how ⊤ is spelled): add_functional_role('=') printed
    # ∀x ∀y ∀z (x = y ∧ x = z → y = z), a different axiom entirely, and
    # HasValue('=', 'a') printed 'x = a'.
    with pytest.raises(dl.RoleExpressionError, match="EQUALITY atom|DISEQUALITY atom"):
        call(name)


# --------------------------------------------------------------------------- #
# What to use INSTEAD of an inverse role: true per axiom.
# --------------------------------------------------------------------------- #

R_INV = dl.InverseRole("r")
Q = "q"

# (label, builder call, a phrase the message MUST contain, a phrase it must NOT).
_INVERSE_ADVICE = [
    # preserved by taking the converse: the plain spelling IS the same axiom
    ("transitive", lambda: dl.TBox().add_transitive_role(R_INV), "pass 'r' instead", None),
    ("symmetric", lambda: dl.TBox().add_symmetric_role(R_INV), "pass 'r' instead", None),
    ("asymmetric", lambda: dl.TBox().add_asymmetric_role(R_INV), "pass 'r' instead", None),
    ("irreflexive", lambda: dl.TBox().add_irreflexive_role(R_INV), "pass 'r' instead", None),
    ("reflexive", lambda: dl.TBox().add_reflexive_role(R_INV), "pass 'r' instead", None),
    # NOT preserved: Func(r⁻) is InvFunc(r) and the other way round
    ("functional", lambda: dl.TBox().add_functional_role(R_INV),
     "add_inverse_functional_role('r')", "pass 'r' instead"),
    ("inverse functional", lambda: dl.TBox().add_inverse_functional_role(R_INV),
     "add_functional_role('r')", "pass 'r' instead"),
    # Dom(r⁻, C) is Rng(r, C) and the other way round
    ("domain", lambda: dl.TBox().add_role_domain(R_INV, A),
     "add_role_range('r', C)", "pass 'r' instead"),
    ("range", lambda: dl.TBox().add_role_range(R_INV, A),
     "add_role_domain('r', C)", "pass 'r' instead"),
    # no plain-name spelling exists
    ("disjoint", lambda: dl.TBox().add_disjoint_roles("p", dl.InverseRole("q")),
     "∀x ∀y ¬(p(x, y) ∧ q(y, x))", "pass 'q' instead"),
    ("chain", lambda: dl.TBox().add_role_chain(["p", dl.InverseRole("q")], "s"),
     "∀x ∀y ∀z (p(x, y) ∧ q(z, y) → s(x, z))", "pass 'q' instead"),
    # inverses cancel
    ("inverse pair", lambda: dl.TBox().add_inverse_roles("p", dl.InverseRole("q")),
     "add_equivalent_roles", "pass 'q' instead"),
    ("equivalent", lambda: dl.TBox().add_equivalent_roles("p", dl.InverseRole("q")),
     "add_role_inclusion", "pass 'q' instead"),
    # a data property has no inverse at all
    ("data functional", lambda: dl.TBox().add_functional_data_property(R_INV),
     "no inverse", "pass 'r' instead"),
]


@pytest.mark.parametrize("label, call, must, must_not", _INVERSE_ADVICE,
                         ids=[c[0] for c in _INVERSE_ADVICE])
def test_the_advice_for_an_inverse_role_is_true_of_that_axiom(label, call, must, must_not):
    with pytest.raises(dl.RoleExpressionError) as info:
        call()
    message = str(info.value)
    assert must in message, message
    if must_not is not None:
        assert must_not not in message, (
            f"{label}: the message advises something that is a DIFFERENT axiom: {message}")


def _equivalent(left, right) -> bool:
    """Z3 proves ``left ↔ right`` valid (both closed formulas)."""
    return api.prove(Iff(left, right), [], timeout=TIMEOUT_MS).status == "proved"


def _forall(*variables, body):
    for variable in reversed(variables):
        body = Quantifier("∀", variable, body)
    return body


def test_the_remedies_the_messages_give_are_the_axioms_they_claim():
    # The advice is CHECKED, not asserted. The axiom over r⁻ is built from the
    # kit's own atom for an inverse role (r⁻(u, v) is the atom r(v, u) — the
    # standard translation's argument swap) and compared, by Z3, with the image
    # of the builder the message points at, and with the plain spelling the old
    # message advised. Each equivalence is derived by hand in its comment.
    from unicode_logic_kit.dl.translate import _chain_axiom, _role_atom

    x, y, z = Variable("x"), Variable("y"), Variable("z")
    inv = dl.InverseRole

    def image(builder, *args):
        return dl.kb_to_fol(getattr(dl.TBox(), builder)(*args)).axioms[0]

    # Func(r⁻) = ∀x∀y∀z (r⁻(x, y) ∧ r⁻(x, z) → y = z) = (r(y, x) ∧ r(z, x) → y = z)
    # = InvFunc(r), and it is NOT Func(r) (r(x, y) ∧ r(x, z) → y = z).
    func_of_inverse = _forall(x, y, z, body=Implies(
        FAnd(_role_atom(inv("r"), x, y), _role_atom(inv("r"), x, z)), Atom("=", (y, z))))
    assert _equivalent(func_of_inverse, image("add_inverse_functional_role", "r"))
    assert not _equivalent(func_of_inverse, image("add_functional_role", "r"))
    # InvFunc(r⁻) = (r⁻(y, x) ∧ r⁻(z, x) → y = z) = (r(x, y) ∧ r(x, z) → y = z) = Func(r).
    invfunc_of_inverse = _forall(x, y, z, body=Implies(
        FAnd(_role_atom(inv("r"), y, x), _role_atom(inv("r"), z, x)), Atom("=", (y, z))))
    assert _equivalent(invfunc_of_inverse, image("add_functional_role", "r"))
    assert not _equivalent(invfunc_of_inverse, image("add_inverse_functional_role", "r"))
    # Dom(r⁻, C) = ∀x∀y (r⁻(x, y) → C(x)) = (r(y, x) → C(x)) = Rng(r, C) = ∀x∀y (r(x, y) → C(y))
    # (renaming x↔y), and it is NOT Dom(r, C).
    c = dl.Atomic("C")
    domain_of_inverse = _forall(x, y, body=Implies(_role_atom(inv("r"), x, y), Atom("C", (x,))))
    assert _equivalent(domain_of_inverse, image("add_role_range", "r", c))
    assert not _equivalent(domain_of_inverse, image("add_role_domain", "r", c))
    # Rng(r⁻, C) = (r⁻(x, y) → C(y)) = (r(y, x) → C(y)) = Dom(r, C) (renaming), not Rng(r, C).
    range_of_inverse = _forall(x, y, body=Implies(_role_atom(inv("r"), x, y), Atom("C", (y,))))
    assert _equivalent(range_of_inverse, image("add_role_domain", "r", c))
    assert not _equivalent(range_of_inverse, image("add_role_range", "r", c))
    # InverseObjectProperties(p, q⁻) = ∀x∀y (p(x, y) ↔ (q⁻)(y, x)) = (p(x, y) ↔ q(x, y)),
    # i.e. p ≡ q: the two role inclusions.
    inverse_of_inverse = _forall(x, y, body=Iff(Atom("p", (x, y)), _role_atom(inv("q"), y, x)))
    equal_roles = FAnd(image("add_role_inclusion", "p", "q"),
                       dl.kb_to_fol(dl.TBox().add_role_inclusion("q", "p")).axioms[0])
    assert _equivalent(inverse_of_inverse, equal_roles)
    # Disjoint(p, q⁻) = ∀x∀y ¬(p(x, y) ∧ q⁻(x, y)) = ¬(p(x, y) ∧ q(y, x)): exactly the
    # premise the message hands api.prove, and NOT Disjoint(p, q).
    disjoint_with_inverse = _forall(x, y, body=Not_(FAnd(Atom("p", (x, y)),
                                                         _role_atom(inv("q"), x, y))))
    message_premise = _forall(x, y, body=Not_(FAnd(Atom("p", (x, y)), Atom("q", (y, x)))))
    assert _equivalent(disjoint_with_inverse, message_premise)
    assert not _equivalent(disjoint_with_inverse, image("add_disjoint_roles", "p", "q"))
    # The chain p ∘ q⁻ ⊑ s the message spells out: p(x, y) ∧ q⁻(y, z) → s(x, z)
    # with q⁻(y, z) = q(z, y).
    chain_premise = _forall(x, y, z, body=Implies(
        FAnd(Atom("p", (x, y)), Atom("q", (z, y))), Atom("s", (x, z))))
    assert _equivalent(chain_premise, _chain_axiom(("p", inv("q")), "s", "x", "y", "z"))


# --------------------------------------------------------------------------- #
# The second line of defence: ONE validation, reached from both routes.
# --------------------------------------------------------------------------- #

_BAD_STORED = [
    ("tuple role in an inclusion", lambda: dl.TBox(role_inclusions=[(("r", "s"), "t")])),
    ("tuple role in a domain", lambda: dl.TBox(role_domains=[(("r", "s"), A)])),
    ("tuple role in a range", lambda: dl.TBox(role_ranges=[(("r", "s"), A)])),
    ("tuple functional role", lambda: dl.TBox(functional_roles={("r", "s")})),
    ("tuple irreflexive role", lambda: dl.TBox(irreflexive_roles={("r", "s")})),
    ("inverse role asymmetric", lambda: dl.TBox(asymmetric_roles={dl.InverseRole("r")})),
    ("three-tuple disjoint pair", lambda: dl.TBox(disjoint_role_pairs=[("R", "S", "T")])),
    ("one-tuple inverse pair", lambda: dl.TBox(inverse_role_pairs=[("R",)])),
    ("one-tuple domain", lambda: dl.TBox(role_domains=[("R",)])),
    ("str chain", lambda: dl.TBox(role_chains=[("rs", "t")])),
    ("empty chain", lambda: dl.TBox(role_chains=[((), "t")])),
    ("one-role chain", lambda: dl.TBox(role_chains=[(("r",), "t")])),
    ("built-in in a stored set", lambda: dl.TBox(symmetric_roles={"owl:topObjectProperty"})),
    ("equality name stored", lambda: dl.TBox(role_inclusions=[("=", "Q")])),
]


@pytest.mark.parametrize("label, build", _BAD_STORED, ids=[c[0] for c in _BAD_STORED])
def test_a_malformed_stored_role_box_is_refused_by_both_routes(label, build):
    # A TBox built through the dataclass constructor skips every builder. The
    # FOL route refused it (rbox_to_fol, kb_to_fol); the TABLEAU answered, so a
    # role inclusion between two tuples was "False" for a question the image
    # rejects. One validation now, reached from both, with one exception type —
    # RoleExpressionError — rather than a bare ValueError from unpacking.
    tbox = build()
    with pytest.raises(dl.RoleExpressionError):
        dl.rbox_to_fol(tbox)
    with pytest.raises(dl.RoleExpressionError):
        dl.kb_to_fol(tbox)
    with pytest.raises(dl.RoleExpressionError):
        dl.concept_satisfiable(dl.Exists("r", A), tbox)
    with pytest.raises(dl.RoleExpressionError):
        dl.abox_consistent(dl.ABox(), tbox)
    with pytest.raises(dl.RoleExpressionError):
        dl.subsumes(A, A, tbox)
    # the external route checks the same thing before any HermiT call
    with pytest.raises(dl.RoleExpressionError):
        dl.external_realize(dl.ABox(), "a", [], tbox)


def test_the_original_wrong_answer_of_a_hand_built_tbox():
    # The measured shape: a role inclusion between two tuples. The tableau said
    # "not subsumed" (False); the FOL route said "malformed". Hand-derived: there
    # is NO role inclusion here to answer a question about — only a malformed
    # value — so the only honest answer is the refusal.
    tbox = dl.TBox(role_inclusions=[(("r", "s"), "t")])
    with pytest.raises(dl.RoleExpressionError, match="add_role_chain"):
        dl.subsumes(dl.Exists("r", A), dl.Exists("t", A), tbox)


# --------------------------------------------------------------------------- #
# Property chains: a str is not a sequence of roles.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("chain", ["rs", "PartOf", b"rs"])
def test_a_str_is_refused_as_a_chain(chain):
    # tuple("rs") is ("r", "s"): the builder stored the two roles r and s that
    # nobody named, and 'PartOf' became six single-letter roles.
    with pytest.raises(dl.RoleExpressionError, match="SEQUENCE of role names"):
        dl.TBox().add_role_chain(chain, "t")


@pytest.mark.parametrize("chain", [{"r", "s"}, frozenset({"r", "s"}), 3, None])
def test_an_unordered_or_non_sequence_chain_is_refused(chain):
    with pytest.raises(dl.RoleExpressionError, match="SEQUENCE"):
        dl.TBox().add_role_chain(chain, "t")


def test_a_tuple_or_a_list_is_still_a_chain():
    assert dl.TBox().add_role_chain(("r", "s"), "t").role_chains == [(("r", "s"), "t")]
    assert dl.TBox().add_role_chain(["r", "s"], "t").role_chains == [(("r", "s"), "t")]
