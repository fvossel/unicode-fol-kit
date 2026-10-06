r"""A bound variable never shares a name with an individual.

``Variable("x")`` and ``Constant("x")`` print the same text and are the SAME
constant to Z3, so a quantifier that binds ``x`` captures an individual called
``x``. Until 0.30.0 only the variables the translation MINTED (``x0``, ``x1``,
...) avoided the individuals; the FIXED ones — the GCI's prefix variable ``x``,
the role axioms' ``x``/``y``/``z``, the data axioms' ``x``/``v``/``w`` — did not,
so ``∃r.{x} ⊑ A`` printed ``∀x (r(x, x) → A(x))`` and ``api.prove`` over it called
a consistent knowledge base inconsistent while the tableau (which has no
variables to capture) said consistent. ``Nominal`` had the same defect.

Every expected value below is derived by hand from the OWL 2 direct semantics,
in the comment above it, and never read off what the code prints:

* ``(∃r.{a})^C = { d | <d, a^I> ∈ r^I }`` (ObjectHasValue);
* ``({a})^C = { a^I }`` (ObjectOneOf with one individual);
* ``ObjectPropertyDomain(r C)`` is ``∀x ∀y (r(x, y) → C(x))``, the range axiom is
  the same with ``C(y)``.

Each semantic test is asked of the FOL route (``api.prove`` over the nodes
``kb_to_fol`` builds). The in-house tableau REFUSES a value restriction (a nominal
in disguise: see "Value restrictions (ObjectHasValue)" in ``dl.tableau``), so for
those the hand-derived verdict is the FOL route's, and the tableau half of the
test is that it RAISES ``UnsupportedConceptError`` rather than answer. Z3-backed
calls take their timeout in MILLISECONDS and it is never shrunk: ``"unknown"`` is
not a verdict.
"""

import pytest

import unicode_fol_kit.dl as dl
from unicode_fol_kit import api
from unicode_fol_kit.fol._identifiers import variable_names
from unicode_fol_kit.fol.nodes import Atom, Constant, Not as FNot

TIMEOUT_MS = 30000
A = dl.Atomic("A")


def _status(goal, premises) -> str:
    return api.prove(goal, list(premises), timeout=TIMEOUT_MS).status


def _inconsistent(kb) -> str:
    """``"proved"`` iff the image is INCONSISTENT, ``"refuted"`` iff it has a model."""
    return _status(FNot(kb.formula), kb.axioms)


def _entailed(kb, individual, concept) -> str:
    """The FOL answer to ``kb |= individual : concept``."""
    goal = dl.abox_to_fol(dl.ABox().assert_concept(individual, concept))
    return _status(goal, kb.premises)


def _refused(call) -> None:
    """The in-house tableau does not answer a value restriction: it raises."""
    with pytest.raises(dl.UnsupportedConceptError, match="HasValue"):
        call()


# --------------------------------------------------------------------------- #
# The wrong answer: one case per binder the capture could reach.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("name", ["x", "y", "z", "v", "w"])
def test_a_gci_over_a_value_restriction_is_not_captured_by_the_prefix_variable(name):
    # TBox: ∃r.{name} ⊑ A.   ABox: r(b, name).
    # Semantics: b has the r-successor name^I, so b ∈ (∃r.{name})^C, and the GCI
    # puts every such element in A: the knowledge base entails b : A.
    tbox = dl.TBox().add(dl.HasValue("r", name), A)
    abox = dl.ABox().assert_role("b", name, "r")
    kb = dl.kb_to_fol(tbox, abox)
    assert _entailed(kb, "b", A) == "proved"                           # the FOL image
    _refused(lambda: dl.instance_check(abox, "b", A, tbox))            # the tableau
    # The twin that must NOT be entailed: an r-edge to ANOTHER individual says
    # nothing about the value restriction over `name`.
    other = dl.ABox().assert_role("b", "c", "r")
    assert _entailed(dl.kb_to_fol(tbox, other), "b", A) == "refuted"
    _refused(lambda: dl.instance_check(other, "b", A, tbox))


def test_the_inconsistency_that_the_capture_invented():
    # TBox: ∃r.{x} ⊑ ⊥  (nothing may have an r-edge INTO the individual x).
    # ABox: r(a, a), a ≠ x.
    # Semantics: the only r-edge is a -> a and a ≠ x, so no r-edge reaches x:
    # the knowledge base is CONSISTENT. (The capture read the axiom as
    # ∀x (r(x, x) → ⊥), "no element is r-related to itself", which r(a, a)
    # violates — an inconsistency the knowledge base does not have.)
    tbox = dl.TBox().add(dl.HasValue("r", "x"), dl.Bottom())
    abox = dl.ABox().assert_role("a", "a", "r").assert_distinct("a", "x")
    assert _inconsistent(dl.kb_to_fol(tbox, abox)) == "refuted"
    _refused(lambda: dl.abox_consistent(abox, tbox))
    # The twin with an edge INTO x: r(a, x) violates the axiom, so inconsistent.
    # (The capture missed this one: r(a, x) is not r(x', x').)
    bad = dl.ABox().assert_role("a", "x", "r")
    assert _inconsistent(dl.kb_to_fol(tbox, bad)) == "proved"
    _refused(lambda: dl.abox_consistent(bad, tbox))
    # And an identity: a = x makes r(a, a) an edge into x as well.
    same = dl.ABox().assert_role("a", "a", "r").assert_same("a", "x")
    assert _inconsistent(dl.kb_to_fol(tbox, same)) == "proved"
    _refused(lambda: dl.abox_consistent(same, tbox))


def test_a_nominal_is_not_captured():
    # TBox: {x} ⊑ A, i.e. x^I ∈ A and nothing else is forced into A.
    # (Nominals are outside the tableau, so this is a FOL-only check.)
    # The capture read it as ∀x (x = x → A(x)), "everything is an A", which
    # also entails b : A for an unrelated individual b.
    kb = dl.kb_to_fol(dl.TBox().add(dl.Nominal("x"), A))
    assert _entailed(kb, "x", A) == "proved"
    assert _entailed(kb, "b", A) == "refuted"


def test_a_range_axiom_over_a_nominal_named_like_its_second_variable():
    # Range(P, {y}) with P(a, b): b ∈ {y}^I, so b = y is entailed.
    # The capture printed ∀x ∀y (P(x, y) → y = y), which entails nothing.
    tbox = dl.TBox().add_role_range("P", dl.Nominal("y"))
    abox = dl.ABox().assert_role("a", "b", "P")
    kb = dl.kb_to_fol(tbox, abox)
    assert _status(Atom("=", (Constant("b"), Constant("y"))), kb.premises) == "proved"
    # a is NOT in the range, so a = y is not entailed.
    assert _status(Atom("=", (Constant("a"), Constant("y"))), kb.premises) == "refuted"


@pytest.mark.parametrize("name", ["x", "y"])
def test_domain_and_range_over_a_value_restriction_are_not_captured(name):
    # Domain(P, ∃R.{name}) with P(a, b): a ∈ ∃R.{name}, i.e. R(a, name).
    # Range(P, ∃R.{name}) with P(a, b): b ∈ ∃R.{name}, i.e. R(b, name).
    # The capture bound `name` in the first variable (x) or the second (y) and
    # turned the filler into R(x, x) / R(y, y). The FOL route answers; the
    # tableau refuses (the value restriction sits in a domain / range filler).
    abox = dl.ABox().assert_role("a", "b", "P")
    filler = dl.HasValue("R", name)
    domain = dl.TBox().add_role_domain("P", filler)
    kb = dl.kb_to_fol(domain, abox)
    assert _entailed(kb, "a", filler) == "proved"
    assert _entailed(kb, "b", filler) == "refuted"
    _refused(lambda: dl.instance_check(abox, "a", filler, domain))
    _refused(lambda: dl.instance_check(abox, "b", filler, domain))
    rng = dl.TBox().add_role_range("P", filler)
    kb = dl.kb_to_fol(rng, abox)
    assert _entailed(kb, "b", filler) == "proved"
    assert _entailed(kb, "a", filler) == "refuted"
    _refused(lambda: dl.instance_check(abox, "b", filler, rng))
    _refused(lambda: dl.instance_check(abox, "a", filler, rng))


def test_a_data_property_domain_over_a_value_restriction_is_not_captured():
    # DataPropertyDomain(d, ∃R.{v}) with d(a, 1): a ∈ ∃R.{v}, i.e. R(a, v).
    # The data axiom's value variable is `v`, so an individual called v was
    # captured: ∀x ∀v (d(x, v) → R(x, v)) says R(a, 1) instead. FOL-only (the
    # tableau has no data domain).
    tbox = dl.TBox().add_data_property_domain("d", dl.HasValue("R", "v"))
    abox = dl.ABox().assert_data("a", "d", dl.Literal("1", "xsd:integer"))
    kb = dl.kb_to_fol(tbox, abox)
    assert _entailed(kb, "a", dl.HasValue("R", "v")) == "proved"
    # Not vacuous (an inconsistent image would "prove" anything): an individual
    # the data axiom says nothing about is not forced into the restriction.
    assert _entailed(kb, "b", dl.HasValue("R", "v")) == "refuted"


# --------------------------------------------------------------------------- #
# The invariant, over every axiom kind that binds a variable.
# --------------------------------------------------------------------------- #

def _kb_with_every_binder(individuals):
    """A knowledge base over the given individual names whose image has a
    quantifier in every kind of axiom that binds a prefix variable: a GCI, a
    role-box axiom of each arity, a domain and a range with a value
    restriction, a property chain long enough to mint further variables, and a
    data property domain. ``individuals[0]`` is the one the fillers name."""
    first = individuals[0]
    tbox = (dl.TBox()
            .add(dl.HasValue("r", first), dl.Exists("s", A))
            .add_transitive_role("t")
            .add_asymmetric_role("u")
            .add_irreflexive_role("u2")
            .add_functional_role("f")
            .add_inverse_functional_role("g")
            .add_role_inclusion("p", "q")
            .add_role_chain(["c1", "c2", "c3", "c4", "c5"], "c6")
            .add_role_domain("P", dl.HasValue("R", first))
            .add_role_range("P", dl.HasValue("R", first))
            .add_data_property_domain("d", dl.HasValue("R", first)))
    abox = dl.ABox().assert_data(individuals[-1], "d", dl.Literal("1", "xsd:integer"))
    for name in individuals:
        abox.assert_concept(name, A)
    return tbox, abox


@pytest.mark.parametrize("individuals", [
    ["x"], ["y"], ["z"], ["v"], ["w"], ["t"],
    ["x", "y", "z"],
    ["x", "x0", "x1"],           # an individual named like a MINTED variable
    ["y", "x0", "t", "v", "w"],
])
def test_no_bound_variable_of_the_image_is_named_like_an_individual(individuals):
    # The invariant, stated once over the whole bundle: the variables of every
    # formula kb_to_fol builds — bound ones, the only ones a closed axiom has —
    # are disjoint from the individuals, which are listed here BY HAND.
    tbox, abox = _kb_with_every_binder(individuals)
    kb = dl.kb_to_fol(tbox, abox)
    variables = set(variable_names(*kb.formulas, *kb.axioms))
    assert variables, "the image has no variables at all: the test is vacuous"
    assert variables.isdisjoint(individuals), (
        f"a bound variable captures an individual: {sorted(variables & set(individuals))}")


# --------------------------------------------------------------------------- #
# What the rename looks like (hand-derived text), and consistency across a call.
# --------------------------------------------------------------------------- #

def test_the_prefix_variable_steps_over_the_individual():
    # GCI ∃r.{x} ⊑ A.  The preferred prefix variable is x; the individual x
    # takes it, so the first free `letter + digits` of x is x0, and the
    # sentence is  ∀x0 (r(x0, x) → A(x0))  with x the CONSTANT.
    image = dl.subsumption_to_fol(dl.HasValue("r", "x"), A)
    assert image.to_unicode_str() == "∀x0 (r(x0, x) → A(x0))"
    assert {t.name for t in image.walk() if type(t).__name__ == "Constant"} == {"x"}
    # tbox_to_fol and kb_to_fol print the same sentence.
    tbox = dl.TBox().add(dl.HasValue("r", "x"), A)
    assert dl.tbox_to_fol(tbox).to_unicode_str() == "∀x0 (r(x0, x) → A(x0))"
    assert dl.kb_to_fol(tbox).tbox.to_unicode_str() == "∀x0 (r(x0, x) → A(x0))"
    # A name that does not clash is left exactly as it was.
    assert (dl.subsumption_to_fol(dl.HasValue("r", "a"), A).to_unicode_str()
            == "∀x (r(x, a) → A(x))")


def test_the_fixed_prefix_variables_of_the_role_box_step_over_the_individuals():
    # Range(P, {y}): preferred names x, y, z; y clashes with the individual y,
    # so it becomes y0, x and z are untouched:  ∀x ∀y0 (P(x, y0) → y0 = y).
    rng = dl.TBox().add_role_range("P", dl.Nominal("y"))
    assert dl.rbox_to_fol(rng).to_unicode_str() == "∀x ∀y0 (P(x, y0) → y0 = y)"
    # Domain(P, ∃R.{x}): x clashes, so x0:  ∀x0 ∀y (P(x0, y) → R(x0, x)).
    dom = dl.TBox().add_role_domain("P", dl.HasValue("R", "x"))
    assert dl.rbox_to_fol(dom).to_unicode_str() == "∀x0 ∀y (P(x0, y) → R(x0, x))"
    # Data property domain over an individual called v: preferred x, v, w, so v
    # becomes v0:  ∀x ∀v0 (d(x, v0) → R(x, v)).
    data = dl.TBox().add_data_property_domain("d", dl.HasValue("R", "v"))
    assert dl.databox_to_fol(data).to_unicode_str() == "∀x ∀v0 (d(x, v0) → R(x, v))"


def test_one_kb_to_fol_call_uses_one_set_of_binder_names_for_every_axiom():
    # The ABox names an individual x that no concept does. The whole knowledge
    # base's individuals are avoided in EVERY axiom of one call — so even a GCI
    # and a transitivity axiom that mention no individual rename their x, and
    # the image of an axiom does not depend on which others are in the call.
    tbox = dl.TBox().add(A, dl.Atomic("B")).add_transitive_role("r")
    abox = dl.ABox().assert_concept("x", A)
    kb = dl.kb_to_fol(tbox, abox)
    assert kb.tbox.to_unicode_str() == "∀x0 (A(x0) → B(x0))"
    assert kb.axioms[0].to_unicode_str() == "∀x0 ∀y ∀z (r(x0, y) ∧ r(y, z) → r(x0, z))"
    # Without the individual nothing changes: the same call, byte for byte.
    plain = dl.kb_to_fol(tbox, dl.ABox().assert_concept("a", A))
    assert plain.tbox.to_unicode_str() == "∀x (A(x) → B(x))"
    assert plain.axioms[0].to_unicode_str() == "∀x ∀y ∀z (r(x, y) ∧ r(y, z) → r(x, z))"


def test_an_individual_named_like_a_minted_variable_after_the_prefix_was_renamed():
    # Individuals x and x0.  TBox:  ∃r.{x} ⊑ ∃s.(A ⊓ ∃t.{x0}).
    # The prefix x is taken, so it becomes the first free x-name, x1 (x0 is an
    # individual too). The ∃s restriction needs a minted variable, which must
    # step over x0 (an individual), x1 (the prefix) AND x, so it is x2:
    #     ∀x1 (r(x1, x) → ∃x2 (s(x1, x2) ∧ A(x2) ∧ t(x2, x0)))
    # The bound names, derived by hand, are exactly {x1, x2}.
    concept = dl.Exists("s", dl.And(A, dl.HasValue("t", "x0")))
    tbox = dl.TBox().add(dl.HasValue("r", "x"), concept)
    image = dl.kb_to_fol(tbox).tbox
    assert set(variable_names(image)) == {"x1", "x2"}
    assert {t.name for t in image.walk() if type(t).__name__ == "Constant"} == {"x", "x0"}
    # And the semantics: a has an r-edge to x, so it must have an s-successor
    # with t(·, x0). The image entails a : ∃s.(A ⊓ ∃t.{x0}); the tableau
    # refuses the question (it names value restrictions).
    abox = dl.ABox().assert_role("a", "x", "r")
    assert _entailed(dl.kb_to_fol(tbox, abox), "a", concept) == "proved"
    _refused(lambda: dl.instance_check(abox, "a", concept, tbox))


# --------------------------------------------------------------------------- #
# The FREE variable is the caller's: refused on a clash, not renamed.
# --------------------------------------------------------------------------- #

def test_concept_to_fol_refuses_a_free_variable_named_like_an_individual():
    # concept_to_fol's `var` is the one FREE variable of the result — callers
    # quantify over it (∃var π(C, var)) — so renaming it behind their back would
    # leave their quantifier binding nothing. And leaving it would capture the
    # individual. So it is refused, by name, with the remedy.
    with pytest.raises(ValueError, match="free variable 'x'.*var="):
        dl.concept_to_fol(dl.HasValue("r", "x"))
    with pytest.raises(ValueError, match="free variable 'x'"):
        dl.concept_to_fol(dl.Nominal("x"))
    # π(∃r.{x}, y) = r(y, x)   and   π({x}, y) = (y = x)
    assert dl.concept_to_fol(dl.HasValue("r", "x"), "y").to_unicode_str() == "r(y, x)"
    assert dl.concept_to_fol(dl.Nominal("x"), "y").to_unicode_str() == "y = x"
