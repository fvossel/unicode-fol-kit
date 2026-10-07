r"""A2: ``ObjectPropertyDomain(P C)`` and ``ObjectPropertyRange(P C)``.

218 of the Open Energy Ontology's 4041 axioms — the two biggest kinds after
``SubClassOf`` itself. Both were refused outright before 0.30.0, and the
caller's workaround was to desugar them into the GCIs they are equivalent to
(``∃P.⊤ ⊑ C`` and ``⊤ ⊑ ∀P.C``), which produces a logically correct image
carrying a tautological ``x0 = x0`` filler — the thing the requesting project
complained about.

They are stored NATIVELY in the role box instead. Three reasons, one test each
below: the image must be the direct two-variable sentence
``∀x ∀y (P(x, y) → π(C, x))``, which no GCI can produce; ``to_owl_functional``
must round-trip the axiom to itself, which a desugared GCI cannot be
re-detected to do; and it is an axiom ABOUT A ROLE, so its image belongs in
``KnowledgeBaseFOL.axioms`` (a premise) rather than inside the knowledge-base
formula.

The TABLEAU, by contrast, does treat them as the GCIs they are: both are
internalised in ``_new_branch`` and decided by the existing ⊓/⊔/∃/∀ rules, so
there is no new completion rule and nothing about subset blocking's termination
argument changes. That the two readings agree is not assumed here — it is
PROVED, both directions, with ``api.prove``.

Every image and verdict below is hand-derived from the OWL 2 direct semantics
first (written out in the comment above it) and then compared with the code.
Z3-backed calls take their ``timeout`` in MILLISECONDS and it is never shrunk.
"""

import pytest

import unicode_logic_kit.dl as dl
from unicode_logic_kit import api
from unicode_logic_kit.dl import owl_reasoner as _owl_reasoner
from unicode_logic_kit.fol.nodes import Iff, Not as FNot, Quantifier, Variable

TIMEOUT_MS = 20000

A, C, D = dl.Atomic("A"), dl.Atomic("C"), dl.Atomic("D")


def _status(goal, premises) -> str:
    return api.prove(goal, list(premises), timeout=TIMEOUT_MS).status


def _both_routes_subsume(sub, sup, tbox, *, holds: bool) -> None:
    assert dl.subsumes(sub, sup, tbox) is holds, "the tableau disagrees"
    status = _status(dl.subsumption_to_fol(sub, sup), dl.kb_to_fol(tbox).tbox_premises)
    assert status == ("proved" if holds else "refuted"), (
        f"the FOL route said {status!r} where the hand-derived answer is {holds}")


# --------------------------------------------------------------------------- #
# The images, as exact strings.
# --------------------------------------------------------------------------- #

def test_the_domain_image_is_the_direct_two_variable_sentence():
    # ObjectPropertyDomain(P C) is satisfied iff for all <x, y> ∈ P^OP we have
    # x ∈ C^C -- literally ∀x ∀y (P(x, y) → π(C, x)). ax03128 is
    # ObjectPropertyDomain(Covers Study).
    assert dl.rbox_to_fol(
        dl.TBox().add_role_domain("Covers", dl.Atomic("Study"))).to_unicode_str() == \
        "∀x ∀y (Covers(x, y) → Study(x))"


def test_the_range_image_translates_the_filler_at_the_second_variable():
    # ObjectPropertyRange(P C): for all <x, y> ∈ P^OP, y ∈ C^C. The filler at
    # the SECOND variable is the only difference from the domain axiom.
    # ax03327 is ObjectPropertyRange(HasUnit Unit).
    assert dl.rbox_to_fol(
        dl.TBox().add_role_range("HasUnit", dl.Atomic("Unit"))).to_unicode_str() == \
        "∀x ∀y (HasUnit(x, y) → Unit(y))"


def test_a_complex_filler_goes_through_the_full_translation():
    # 12 of OEO's 110 domain axioms have a non-atomic filler, all ObjectUnionOf:
    # ObjectPropertyDomain(HasClient ObjectUnionOf(InformationContentEntity
    # Model)) is ∀x ∀y (HasClient(x, y) → ICE(x) ∨ Model(x)) -- the filler is a
    # class EXPRESSION, so it must go through _translate, not be rendered as a
    # bare predicate.
    assert dl.rbox_to_fol(dl.TBox().add_role_domain(
        "HasClient", dl.Or(dl.Atomic("InformationContentEntity"),
                           dl.Atomic("Model")))).to_unicode_str() == \
        "∀x ∀y (HasClient(x, y) → InformationContentEntity(x) ∨ Model(x))"
    # 10 of the 108 range axioms likewise; a nested restriction mints its own
    # bound variable, at the SECOND variable for a range axiom.
    assert dl.rbox_to_fol(dl.TBox().add_role_range(
        "HasAuthor", dl.Exists("HasRole", dl.Atomic("Author")))).to_unicode_str() == \
        "∀x ∀y (HasAuthor(x, y) → ∃x0 (HasRole(y, x0) ∧ Author(x0)))"


def test_a_value_restriction_filler_renders_as_the_ground_atom():
    # The two kinds this package added, composed: the filler's individual lands
    # in the argument position at the range axiom's SECOND variable.
    assert dl.rbox_to_fol(dl.TBox().add_role_range(
        "P", dl.HasValue("Q", "A"))).to_unicode_str() == \
        "∀x ∀y (P(x, y) → Q(y, A))"


def test_a_minted_variable_steps_over_an_individual_of_the_same_name():
    # The avoid set must carry every individual name in the FILLER: a minted x0
    # colliding with an individual named x0 would CAPTURE it (a Variable and a
    # Constant of the same name print the same text and are the same Z3
    # expression), so the individual would stop denoting itself. Here the
    # nested ∃ must mint x1.
    assert dl.rbox_to_fol(dl.TBox().add_role_domain(
        "P", dl.Exists("Q", dl.HasValue("R", "x0")))).to_unicode_str() == \
        "∀x ∀y (P(x, y) → ∃x1 (Q(x, x1) ∧ R(x1, x0)))"


def test_the_caller_can_choose_the_quantified_variable_names():
    # ... and the minted name follows the chosen LETTER, avoiding all three, so
    # no nested variable collides with the axiom's own y or z.
    assert dl.rbox_to_fol(dl.TBox().add_role_range(
        "P", dl.Exists("Q", A)), x="u", y="v", z="w").to_unicode_str() == \
        "∀u ∀v (P(u, v) → ∃u0 (Q(v, u0) ∧ A(u0)))"


def test_the_images_read_back_through_the_kits_own_parser():
    # Neither image contains an INDIVIDUAL, so unlike A1's and A8's these two
    # read back cleanly in the plain `fol` dialect -- see
    # tests/test_printed_text_reads_back.py for the limit that applies when one
    # does.
    for tbox in (dl.TBox().add_role_domain("Covers", dl.Atomic("Study")),
                 dl.TBox().add_role_range("HasUnit", dl.Atomic("Unit"))):
        text = dl.rbox_to_fol(tbox).to_unicode_str()
        assert api.parse_any(text).ok, text


# --------------------------------------------------------------------------- #
# Where the image LANDS: a side axiom, never a conjunct of the formula.
# --------------------------------------------------------------------------- #

def test_the_images_are_side_axioms_and_not_part_of_the_formula():
    tbox = (dl.TBox()
            .add_role_inclusion("A1", "B1")
            .add_transitive_role("T1")
            .add_role_domain("P", C)
            .add_role_range("Q", D))
    kb = dl.kb_to_fol(tbox)
    # The order is _AXIOM_KINDS': role inclusions, sorted transitive roles,
    # then the rest of the role box, with the two class-expression kinds last.
    assert [axiom.kind for axiom in kb.side_axioms] == [
        "SubObjectPropertyOf", "TransitiveObjectProperty",
        "ObjectPropertyDomain", "ObjectPropertyRange"]
    assert all(axiom.group == "rbox" for axiom in kb.side_axioms)
    assert kb.axioms_of_kind("ObjectPropertyDomain")[0].to_unicode_str() == \
        "∀x ∀y (P(x, y) → C(x))"
    assert kb.axioms_of_kind("ObjectPropertyRange")[0].to_unicode_str() == \
        "∀x ∀y (Q(x, y) → D(y))"
    # The TBox has no concept inclusion at all, so `formula` is the
    # "no constraint" tautology and every axiom is in `axioms`.
    assert kb.formula.to_unicode_str() == "c_tautology = c_tautology"
    assert kb.premises == (kb.formula, *kb.axioms)


def test_tbox_to_fol_refuses_a_tbox_that_carries_only_a_domain_axiom():
    # THE regression guard for the trap the requesting project fell into: 218
    # OEO axioms would otherwise be dropped SILENTLY, since tbox_to_fol renders
    # the concept inclusions and these are not among them. The condition is
    # derived from the axiom-kind table, so it fires for a kind nobody
    # remembered to add to a hand-written `or`.
    tbox = dl.TBox().add_role_domain("P", C).add_role_range("Q", D)
    with pytest.raises(dl.RoleBoxOmittedError) as info:
        dl.tbox_to_fol(tbox)
    message = str(info.value)
    assert "1 ObjectPropertyDomain axiom(s)" in message
    assert "1 ObjectPropertyRange axiom(s)" in message
    for pointer in ("kb_to_fol", "rbox_to_fol", "concept_inclusions_only"):
        assert pointer in message
    # ... and the explicit opt-out still works
    assert dl.tbox_to_fol(tbox, concept_inclusions_only=True).to_unicode_str() == \
        "c_tautology = c_tautology"


# --------------------------------------------------------------------------- #
# The tableau: internalised, no new rule, and the two routes agree.
# --------------------------------------------------------------------------- #

def test_a_domain_axiom_classifies_anything_with_a_successor():
    # The internalisation is ∀r.⊥ ⊔ C -- "either no r-successor at all, or in
    # C" -- forced on every element. So ∃r.⊤ ⊑ C is entailed: an element with
    # an r-successor cannot take the ∀r.⊥ disjunct.
    tbox = dl.TBox().add_role_domain("r", C)
    _both_routes_subsume(dl.Exists("r", dl.Top()), C, tbox, holds=True)
    # The same fact as an unsatisfiability: ¬C ⊓ ∃r.⊤ has no model.
    assert dl.concept_satisfiable(dl.And(dl.Not(C), dl.Exists("r", dl.Top())),
                                  tbox) is False
    goal = FNot(Quantifier("∃", Variable("x"), dl.concept_to_fol(
        dl.And(dl.Not(C), dl.Exists("r", dl.Top())))))
    assert _status(goal, dl.kb_to_fol(tbox).tbox_premises) == "proved"
    # ... and it says nothing about an element with NO r-successor:
    # Δ = {d}, r = ∅, C = ∅ satisfies the axiom and leaves d outside C.
    _both_routes_subsume(dl.Top(), C, tbox, holds=False)


def test_a_range_axiom_classifies_every_successor():
    # ⊤ ⊑ ∀r.C internalises to ∀r.C on every element, so the successor d
    # already has is itself in C: ∃r.⊤ ⊑ ∃r.C.
    tbox = dl.TBox().add_role_range("r", C)
    _both_routes_subsume(dl.Exists("r", dl.Top()), dl.Exists("r", C), tbox, holds=True)
    # And the stronger reading too: EVERY r-successor is in C.
    _both_routes_subsume(dl.Top(), dl.ForAll("r", C), tbox, holds=True)
    # But nothing about the element itself: Δ = {d, e}, r = {(d, e)},
    # C = {e} satisfies the axiom and leaves d outside C.
    _both_routes_subsume(dl.Exists("r", dl.Top()), C, tbox, holds=False)


def test_the_range_axiom_travels_down_the_role_hierarchy():
    # The ∀-rule's sub-role closure gives this for free: a sub-r edge IS an
    # r-edge, so its target is in the range too.
    tbox = dl.TBox().add_role_range("r", C).add_role_inclusion("s", "r")
    _both_routes_subsume(dl.Exists("s", dl.Top()), dl.Exists("s", C), tbox, holds=True)


def test_the_native_image_and_the_gci_rewrite_are_interderivable():
    # THE claim that makes "internalise the GCI, render the direct sentence"
    # honest, proved rather than assumed, both directions, by Z3.
    #
    # Domain: ∀x ∀y (r(x, y) → C(x))  <->  ∀x (∃x0 (r(x, x0) ∧ x0 = x0) → C(x))
    # -- pull the ∃ out of the antecedent as a ∀ and drop the reflexivity filler.
    native = dl.rbox_to_fol(dl.TBox().add_role_domain("r", C))
    rewrite = dl.subsumption_to_fol(dl.Exists("r", dl.Top()), C)
    assert _status(Iff(native, rewrite), ()) == "proved"
    # Range: ∀x ∀y (r(x, y) → C(y))  <->  ∀x (x = x → ∀x0 (r(x, x0) → C(x0))).
    native_range = dl.rbox_to_fol(dl.TBox().add_role_range("r", C))
    rewrite_range = dl.subsumption_to_fol(dl.Top(), dl.ForAll("r", C))
    assert _status(Iff(native_range, rewrite_range), ()) == "proved"


def test_an_abox_assertion_meets_a_domain_and_a_range_axiom():
    # The whole knowledge base, both routes: Dom(r, C) and Rng(r, D) with the
    # ground fact r(a, b) entail C(a) and D(b).
    tbox = dl.TBox().add_role_domain("r", C).add_role_range("r", D)
    abox = dl.ABox().assert_role("a", "b", "r")
    kb = dl.kb_to_fol(tbox, abox)
    for individual, concept in (("a", C), ("b", D)):
        assert dl.instance_check(abox, individual, concept, tbox) is True
        goal = dl.abox_to_fol(dl.ABox().assert_concept(individual, concept))
        assert _status(goal, kb.premises) == "proved"
    # and the crossed pair is NOT entailed: Δ = {d, e}, r = {(d, e)},
    # C = {d}, D = {e} is a model with d ∉ D and e ∉ C.
    for individual, concept in (("a", D), ("b", C)):
        assert dl.instance_check(abox, individual, concept, tbox) is False
        goal = dl.abox_to_fol(dl.ABox().assert_concept(individual, concept))
        assert _status(goal, kb.premises) == "refuted"


def test_a_domain_or_range_axiom_on_a_transitive_role_is_legal():
    # Neither introduces an AtLeast/AtMost, so OWL 2's SIMPLE-role restriction
    # (Structural Specification §11) does not apply and the combination with
    # transitivity stays decidable. OEO has both shapes.
    tbox = (dl.TBox().add_transitive_role("r")
            .add_role_domain("r", C).add_role_range("r", D))
    assert dl.concept_satisfiable(dl.Top(), tbox) is True
    assert dl.abox_consistent(dl.ABox().assert_role("a", "b", "r"), tbox) is True


def test_a_nominal_hiding_in_a_filler_is_refused_by_name():
    # A domain/range filler is an ordinary class expression, so the I/O guard
    # has to walk it too -- otherwise the Nominal would reach the tableau
    # through _new_branch's internalisation unchecked. (nnf would then raise
    # its own TypeError, which is a crash rather than the precise refusal.)
    for tbox in (dl.TBox().add_role_domain("r", dl.Nominal("a")),
                 dl.TBox().add_role_range("r", dl.Nominal("a")),
                 dl.TBox().add_role_domain("r", dl.And(C, dl.Nominal("a")))):
        with pytest.raises(dl.UnsupportedConceptError, match="Nominal"):
            dl.concept_satisfiable(C, tbox)
        with pytest.raises(dl.UnsupportedConceptError, match="Nominal"):
            dl.abox_consistent(dl.ABox(), tbox)


def test_an_inverse_role_hiding_in_a_filler_is_refused_by_name():
    tbox = dl.TBox().add_role_range("r", dl.Exists(dl.InverseRole("s"), C))
    with pytest.raises(dl.UnsupportedConceptError, match="InverseRole"):
        dl.concept_satisfiable(C, tbox)


def test_the_builder_refuses_only_a_malformed_ROLE():
    # Builders never refuse a KIND -- but a malformed ARGUMENT is refused on
    # the spot, like every other role-box builder's.
    with pytest.raises(dl.RoleExpressionError):
        dl.TBox().add_role_domain(("r", "s"), C)
    with pytest.raises(dl.RoleExpressionError):
        dl.TBox().add_role_range("owl:topObjectProperty", C)


# --------------------------------------------------------------------------- #
# Round trips.
# --------------------------------------------------------------------------- #

def test_the_functional_syntax_round_trips():
    tbox, abox = dl.parse_owl_functional(
        "Ontology(ObjectPropertyDomain(Covers Study) "
        "ObjectPropertyRange(HasUnit Unit))")
    assert tbox.role_domains == [("Covers", dl.Atomic("Study"))]
    assert tbox.role_ranges == [("HasUnit", dl.Atomic("Unit"))]
    assert tbox.inclusions == []           # stored natively, not desugared
    text = dl.to_owl_functional(tbox, abox)
    assert "ObjectPropertyDomain(Covers Study)" in text
    assert "ObjectPropertyRange(HasUnit Unit)" in text
    assert dl.parse_owl_functional(text) == (tbox, abox)


def test_a_complex_filler_round_trips_through_the_functional_syntax():
    document = ("Ontology(ObjectPropertyDomain(HasClient "
                "ObjectUnionOf(InformationContentEntity Model)))")
    tbox, abox = dl.parse_owl_functional(document)
    assert tbox.role_domains == [("HasClient", dl.Or(
        dl.Atomic("InformationContentEntity"), dl.Atomic("Model")))]
    assert dl.parse_owl_functional(dl.to_owl_functional(tbox, abox)) == (tbox, abox)


def test_the_filler_names_are_declared():
    # _collect_names must walk the filler, or a class occurring ONLY in a
    # domain/range axiom would get no Declaration line.
    tbox = dl.TBox().add_role_domain("Covers", dl.Atomic("Study"))
    text = dl.to_owl_functional(tbox, dl.ABox())
    assert "Declaration(Class(Study))" in text
    assert "Declaration(ObjectProperty(Covers))" in text


@pytest.mark.parametrize("text, expected", [
    ("r Domain: A", ("domain", "r", dl.Atomic("A"))),
    ("r Domain A", ("domain", "r", dl.Atomic("A"))),
    ("r Range: A", ("range", "r", dl.Atomic("A"))),
    ("r Range A", ("range", "r", dl.Atomic("A"))),
    # the right-hand side is a class EXPRESSION, parsed by the same
    # _description() every other class-expression position uses
    ("r Domain: A and C", ("domain", "r", dl.And(dl.Atomic("A"), C))),
    ("r Range: s some A", ("range", "r", dl.Exists("s", dl.Atomic("A")))),
], ids=["domain", "domain-no-colon", "range", "range-no-colon",
        "complex-domain", "complex-range"])
def test_the_manchester_role_axiom_frames_read(text, expected):
    assert dl.parse_manchester_role_axiom(text) == expected


@pytest.mark.parametrize("axiom", [
    ("domain", "r", dl.Atomic("A")),
    ("range", "r", dl.And(dl.Atomic("A"), C)),
], ids=["domain", "range-complex"])
def test_the_manchester_role_axiom_frames_round_trip(axiom):
    text = dl.role_axiom_to_manchester(*axiom)
    assert dl.parse_manchester_role_axiom(text) == axiom


def test_the_manchester_renderer_keeps_the_frame_colon():
    assert dl.role_axiom_to_manchester("domain", "Covers", dl.Atomic("Study")) == \
        "Covers Domain: Study"
    assert dl.role_axiom_to_manchester("range", "r", dl.And(dl.Atomic("A"), C)) == \
        "r Range: A and C"


def test_an_empty_manchester_filler_is_a_syntax_error():
    with pytest.raises(dl.ManchesterSyntaxError, match="Domain"):
        dl.parse_manchester_role_axiom("r Domain:")


def test_the_manchester_fallback_message_names_the_two_new_frames():
    with pytest.raises(dl.ManchesterSyntaxError) as info:
        dl.parse_manchester_role_axiom("r Bogus A")
    message = str(info.value)
    for keyword in ("'SubPropertyOf'", "'Domain:'", "'Range:'",
                    "'Characteristics:'"):
        assert keyword in message


def test_the_mcp_row_shapes_build_both_axioms():
    from unicode_logic_kit.mcp.server import _build_dl_tbox

    tbox, err = _build_dl_tbox(
        [{"domainrole": "Covers", "domain": "Study"},
         {"rangerole": "HasUnit", "range": "Unit ⊓ Measurable"}], "alc")
    assert err is None
    assert tbox.role_domains == [("Covers", dl.Atomic("Study"))]
    assert tbox.role_ranges == [("HasUnit", dl.And(dl.Atomic("Unit"),
                                                   dl.Atomic("Measurable")))]
    # a row missing its ROLE key is a caller mistake, named
    _tbox, err = _build_dl_tbox([{"domain": "Study"}], "alc")
    assert err is not None and "domainrole" in err["error"]["message"]


@pytest.mark.skipif(not _owl_reasoner.available(),
                    reason="owlready2 is not installed ([owl] extra)")
@pytest.mark.parametrize("build, sub, sup, holds", [
    (lambda: dl.TBox().add_role_domain("r", C),
     dl.Exists("r", dl.Top()), C, True),
    (lambda: dl.TBox().add_role_domain("r", C), dl.Top(), C, False),
    (lambda: dl.TBox().add_role_range("r", C),
     dl.Exists("r", dl.Top()), dl.Exists("r", C), True),
    (lambda: dl.TBox().add_role_range("r", C),
     dl.Exists("r", dl.Top()), C, False),
], ids=["domain-holds", "domain-does-not", "range-holds", "range-does-not"])
def test_hermit_agrees_on_the_same_hand_derived_pairs(build, sub, sup, holds):
    # An oracle that silently dropped the axiom would agree with everything, so
    # the check is the same pair asked of HermiT (owlready2 spells the two as a
    # property's `domain`/`range`).
    tbox = build()
    assert dl.external_subsumes(sub, sup, tbox) is holds
    assert dl.subsumes(sub, sup, tbox) is holds
