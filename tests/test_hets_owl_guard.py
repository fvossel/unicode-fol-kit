"""The Hets route refuses what every other route refuses.

``hets.owl_backend`` renders a knowledge base as an OWL 2 document, and a
renderer that meets a name it does not know gives it a synthetic one of its own
(``:R1``). An OWL 2 built-in property name -- ``owl:topObjectProperty``,
``owl:bottomObjectProperty`` and the two data ones -- or the name of an equality
atom (``=`` / ``≠``) as the ROLE of a class expression was therefore written as an
ordinary role: ``SubClassOf(:C1 ObjectSomeValuesFrom(:R1 :C1))`` for
``A ⊑ ∃owl:bottomObjectProperty.A``. OWL 2 says that property is EMPTY, so the
restriction is unsatisfiable and ``A`` is empty; the reasoner behind Hets was
asked about a different restriction and answered satisfiable. Every other route
(the FOL image, the in-house tableau, the HermiT route) refuses the same concept
by name, and so must this one -- by calling the same dl function, so that it is the
SAME refusal.

Each test below uses a fake Hets client: nothing is sent anywhere, and the point of
most of them is exactly that nothing was.
"""

import pytest

import unicode_fol_kit.dl as dl
import unicode_fol_kit.hets.owl_backend as owl_backend
from unicode_fol_kit.atp.protocol import BackendUnavailable
from unicode_fol_kit.dl import owl_reasoner

A = dl.Atomic("A")
INTEGER = dl.Datatype("xsd:integer")


class _FakeClient:
    """Stands in for HetsClient: records an upload, answers 'Consistent'."""

    def __init__(self):
        self.uploaded = None

    def upload(self, text, filename):
        self.uploaded = text
        return "/tmp/fake/kit_owl_probe.ofn"

    def consistency_check(self, iri, node, *, reasoner, time_limit):
        return [{"result": "Consistent"}]


@pytest.fixture
def fake(monkeypatch):
    client = _FakeClient()
    monkeypatch.setattr(owl_backend, "HetsClient", lambda url, timeout: client)
    monkeypatch.setattr(owl_backend, "discover_hets_url",
                        lambda *, start_container: ("http://fake:8000", None))
    return client


#: Every spelling of a built-in the dl layer refuses: the four OWL 2 names
#: (abbreviated), one in its full-IRI spelling, and the two equality atom names.
_NAMES = [
    "owl:topObjectProperty", "owl:bottomObjectProperty",
    "owl:topDataProperty", "owl:bottomDataProperty",
    "http://www.w3.org/2002/07/owl#bottomObjectProperty",
    "=", "≠",
]

#: The class-expression constructors whose ROLE field a name can occupy.
_CONSTRUCTS = {
    "Exists": lambda name: dl.Exists(name, A),
    "ForAll": lambda name: dl.ForAll(name, A),
    "AtLeast": lambda name: dl.AtLeast(2, name, A),
    "AtMost": lambda name: dl.AtMost(1, name, A),
    "HasValue": lambda name: dl.HasValue(name, "b"),
    "DataExists": lambda name: dl.DataExists(name, INTEGER),
    "nested": lambda name: dl.And(A, dl.Not(dl.Or(A, dl.Exists(name, dl.Not(A))))),
}

#: Where the concept can stand: ``(label, ask)``; ``ask(concept)`` puts it there and
#: asks the Hets route a question. Every place a concept can stand in a question.
_PLACES = {
    "gci-sub": lambda c: owl_backend.external_concept_satisfiable(
        A, dl.TBox().add(c, A)),
    "gci-sup": lambda c: owl_backend.external_concept_satisfiable(
        A, dl.TBox().add(A, c)),
    "object-domain-filler": lambda c: owl_backend.external_concept_satisfiable(
        A, dl.TBox().add_role_domain("r", c)),
    "object-range-filler": lambda c: owl_backend.external_concept_satisfiable(
        A, dl.TBox().add_role_range("r", c)),
    "data-domain-filler": lambda c: owl_backend.external_concept_satisfiable(
        A, dl.TBox().add_data_property_domain("d", c)),
    "abox-assertion": lambda c: owl_backend.external_abox_consistent(
        dl.ABox().assert_concept("a", c)),
    "query-satisfiable": lambda c: owl_backend.external_concept_satisfiable(c),
    "query-subsumes": lambda c: owl_backend.external_subsumes(c, A),
    "query-instance": lambda c: owl_backend.external_instance_check(
        dl.ABox().assert_concept("a", A), "a", c),
}


@pytest.mark.parametrize("place", sorted(_PLACES))
@pytest.mark.parametrize("construct", sorted(_CONSTRUCTS))
@pytest.mark.parametrize("name", _NAMES)
def test_a_built_in_property_name_as_a_role_is_refused_by_name_and_nothing_is_sent(
        fake, name, construct, place):
    concept = _CONSTRUCTS[construct](name)
    with pytest.raises(dl.RoleExpressionError) as refused:
        _PLACES[place](concept)
    message = str(refused.value)
    assert name in message, message
    assert message.startswith("hets.owl_backend:"), message
    assert fake.uploaded is None, "a refused question must not be uploaded"


@pytest.mark.parametrize("name", _NAMES)
def test_it_is_the_same_refusal_the_hermit_route_gives(name):
    # Hand-derived: one function (dl.tableau._reject_concept_role) decides what a
    # role may be; the Hets route CALLS it, so its text differs from the HermiT
    # route's in the ``where:`` prefix and nowhere else.
    tbox = dl.TBox().add(A, dl.Exists(name, A))
    with pytest.raises(dl.RoleExpressionError) as hets:
        owl_backend._render_document(tbox, dl.ABox())
    with pytest.raises(dl.RoleExpressionError) as hermit:
        owl_reasoner._guard_inputs(tbox, dl.ABox())
    assert str(hets.value).replace("hets.owl_backend", "dl.owl_reasoner") == str(hermit.value)


def test_a_built_in_property_name_in_an_abox_role_assertion_is_refused_too(fake):
    # owl:bottomObjectProperty(a, b) holds in NO interpretation: the knowledge base
    # is inconsistent in OWL 2. As an ordinary role it is consistent.
    abox = dl.ABox().assert_role("a", "b", "owl:bottomObjectProperty")
    with pytest.raises(dl.RoleExpressionError, match="owl:bottomObjectProperty"):
        owl_backend.external_abox_consistent(abox)
    assert fake.uploaded is None


def test_the_refusal_needs_no_hets_server(monkeypatch):
    # A question refused by name is refused BEFORE a server is looked for.
    def no_server(*, start_container):
        raise BackendUnavailable("hets: no server discovered")

    monkeypatch.setattr(owl_backend, "discover_hets_url", no_server)
    with pytest.raises(dl.RoleExpressionError):
        owl_backend.external_concept_satisfiable(dl.Exists("owl:bottomObjectProperty", A))
    # ... while a question that is not refused still reports the missing server.
    with pytest.raises(BackendUnavailable):
        owl_backend.external_concept_satisfiable(dl.Exists("hasChild", A))


# --------------------------------------------------------------------------- #
# A hand-mutated TBox: the shared validation runs before any unpacking.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("field", [
    "disjoint_role_pairs", "inverse_role_pairs", "role_inclusions",
    "data_property_inclusions", "disjoint_data_property_pairs",
])
def test_a_wrong_arity_pair_is_a_role_expression_error_not_a_bare_value_error(fake, field):
    tbox = dl.TBox()
    getattr(tbox, field).append(("R", "S", "T"))
    with pytest.raises(dl.RoleExpressionError, match="PAIR of two values"):
        owl_backend._render_document(tbox, dl.ABox())
    with pytest.raises(dl.RoleExpressionError):
        owl_backend.external_concept_satisfiable(A, tbox)
    assert fake.uploaded is None
    # The same TBox is refused with the same words by the HermiT route.
    with pytest.raises(dl.RoleExpressionError) as hermit:
        owl_reasoner._guard_inputs(tbox, dl.ABox())
    with pytest.raises(dl.RoleExpressionError) as hets:
        owl_backend._render_document(tbox, dl.ABox())
    assert str(hets.value).replace("hets.owl_backend", "dl.owl_reasoner") == str(hermit.value)


# --------------------------------------------------------------------------- #
# Controls: what is a question still reaches the server, document unchanged.
# --------------------------------------------------------------------------- #

def test_an_ordinary_role_is_still_rendered_and_uploaded(fake):
    assert owl_backend.external_concept_satisfiable(dl.Exists("hasChild", A)) is True
    assert "ObjectSomeValuesFrom(:R1 :C1)" in fake.uploaded
    assert "owl:bottomObjectProperty" not in fake.uploaded


def test_the_data_layer_is_still_asked_of_hets(fake):
    # Unlike the HermiT route, FaCT++ IS asked about the data layer: the guard
    # must not refuse it (a data property under an ordinary name, a data range).
    tbox = dl.TBox().add_data_property_range("age", INTEGER)
    concept = dl.DataExists("age", INTEGER)
    assert owl_backend.external_concept_satisfiable(concept, tbox) is True
    assert "DataSomeValuesFrom(:P1 xsd:integer)" in fake.uploaded
    assert "DataPropertyRange(:P1 xsd:integer)" in fake.uploaded


# --------------------------------------------------------------------------- #
# One name for two kinds OWL 2 DL keeps apart: refused, as the FOL image does.
#
# An object property and a data property (or a class and a datatype) with one name
# are forbidden by OWL 2 DL (Structural Specification 5.8.1). The renderer wrote
# them under separate synthetic tokens (:R1 / :P1), so the oracle answered a
# knowledge base the kit's own route refuses.
# --------------------------------------------------------------------------- #

def _pun_object_and_data_property():
    tbox = dl.TBox().add_role_domain("P", A)             # P an OBJECT property ...
    return dl.DataExists("P", INTEGER), tbox              # ... and a DATA property in the query


def _pun_in_the_tbox_alone():
    tbox = dl.TBox().add(A, dl.Exists("P", A)).add_data_property_range("P", INTEGER)
    return A, tbox


def _pun_class_and_datatype():
    tbox = dl.TBox().add(dl.Atomic("xsd:integer"), A)    # a CLASS named like a datatype ...
    return dl.DataExists("d", INTEGER), tbox              # ... and that datatype in the query


@pytest.mark.parametrize("build, kinds", [
    (_pun_object_and_data_property, "an object property and a data property"),
    (_pun_in_the_tbox_alone, "an object property and a data property"),
    (_pun_class_and_datatype, "a class and a datatype"),
])
def test_a_name_used_for_two_kinds_is_refused_as_the_fol_image_refuses_it(fake, build, kinds):
    query, tbox = build()
    with pytest.raises(dl.UnsupportedDatatypeError) as hets:
        owl_backend.external_concept_satisfiable(query, tbox)
    assert fake.uploaded is None
    assert "is used as both" in str(hets.value) and "OWL 2 DL forbids that" in str(hets.value)
    # The same error, the same wording: only the ``where:`` prefix differs from
    # what the FOL image says of the same knowledge base (the query concept
    # joins the knowledge base, as it does in the document).
    probe = dl.ABox().assert_concept("_probe", query)
    with pytest.raises(dl.UnsupportedDatatypeError) as fol:
        dl.kb_to_fol(tbox, probe)
    assert str(hets.value).replace("hets.owl_backend", "dl.kb_to_fol") == str(fol.value)


def test_the_renderer_refuses_the_pun_without_a_client(fake):
    tbox = dl.TBox().add(A, dl.Exists("P", A)).add_data_property_range("P", INTEGER)
    with pytest.raises(dl.UnsupportedDatatypeError, match="'P' is used as both"):
        owl_backend._render_document(tbox, dl.ABox())


def test_a_data_property_and_an_object_role_with_two_names_still_render(fake):
    # The control: the SAME knowledge base with the data property renamed.
    tbox = dl.TBox().add(A, dl.Exists("P", A)).add_data_property_range("PD", INTEGER)
    assert owl_backend.external_concept_satisfiable(A, tbox) is True
    assert "ObjectSomeValuesFrom(:R1 :C1)" in fake.uploaded
    assert "DataPropertyRange(:P1 xsd:integer)" in fake.uploaded


# --------------------------------------------------------------------------- #
# An entry point that makes no Hets call still refuses what the others refuse.
# --------------------------------------------------------------------------- #

_BAD_TBOX = dl.TBox().add(A, dl.Exists("owl:bottomObjectProperty", A))


def test_the_sweeps_that_may_ask_nothing_refuse_the_knowledge_base_all_the_same(fake):
    # Hand-derived: owl:bottomObjectProperty is the EMPTY property, so the
    # inclusion A ⊑ ∃⊥.A makes A empty; asked as an ordinary role it does not.
    # With nobody to ask about (an empty vocabulary, an empty ABox) the sweep made
    # no call and returned a quiet [] / set() / {} -- the HermiT route refuses.
    abox = dl.ABox().assert_concept("a", A)
    with pytest.raises(dl.RoleExpressionError, match="owl:bottomObjectProperty"):
        owl_backend.external_realize(abox, "a", [], _BAD_TBOX)
    with pytest.raises(dl.RoleExpressionError, match="owl:bottomObjectProperty"):
        owl_backend.external_realize_all(abox, [], _BAD_TBOX)
    with pytest.raises(dl.RoleExpressionError, match="owl:bottomObjectProperty"):
        owl_backend.external_instance_retrieval(dl.ABox(), A, _BAD_TBOX)
    with pytest.raises(dl.RoleExpressionError, match="owl:topObjectProperty"):
        owl_backend.external_instance_retrieval(
            dl.ABox(), dl.Exists("owl:topObjectProperty", A), dl.TBox())
    with pytest.raises(dl.RoleExpressionError, match="owl:topObjectProperty"):
        owl_backend.external_realize(abox, "a", [dl.Exists("owl:topObjectProperty", A)])
    assert fake.uploaded is None


def test_the_sweeps_still_return_their_quiet_answers_for_an_ordinary_knowledge_base(fake):
    ok = dl.TBox().add(A, dl.Exists("hasChild", A))
    assert owl_backend.external_realize(dl.ABox().assert_concept("a", A), "a", [], ok) == []
    assert owl_backend.external_realize_all(dl.ABox(), [A], ok) == {}
    assert owl_backend.external_instance_retrieval(dl.ABox(), A, ok) == set()
    assert fake.uploaded is None
