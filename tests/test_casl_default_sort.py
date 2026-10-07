"""The sort the CASL export gives every unsorted position, and a sort of the same name.

The exporter types every unsorted quantifier and every symbol position no sort annotation
reaches with a default sort, ``Thing`` unless the caller says otherwise. A sort that the
formulas write with the SAME name (``∀x:Thing``, ``c:Thing``) or that ``subsorts`` declares
would be one sort with it, so an unsorted position silently became a position of the
caller's sort: ``∀x:Thing P(x) ⊢ ∀y P(y)`` was exported as ``forall y : Thing . P(y)``, which
is a different claim than the kit's (a sort is a part of the universe, and an unsorted
variable ranges over all of it). The export now refuses that by name and says which keyword
picks another default sort, and the Hets backend picks a default sort that no sort of the
problem has. Where the default sort is not used at all, a sort called ``Thing`` is the
caller's and nothing is refused.
"""

import pytest

from unicode_logic_kit import hets as hets_pkg
from unicode_logic_kit.atp.hets_backend import HetsBackend
from unicode_logic_kit.atp.protocol import get_backend
from unicode_logic_kit.fol.casl_export import formula_to_casl, to_casl_spec
from unicode_logic_kit.fol.nodes import (
    And, Atom, Constant, Function, Quantifier, SortedConstant, SortedQuantifier, Variable,
)
from unicode_logic_kit.hets.docker import hets_available

_X, _Y, _Z = Variable("x"), Variable("y"), Variable("z")


def _all_in(sort, variable, body):
    return SortedQuantifier("∀", variable, sort, body)


def _ex_in(sort, variable, body):
    return SortedQuantifier("∃", variable, sort, body)


def _p(term):
    return Atom("P", [term])


def _q(term):
    return Atom("Q", [term])


# ∀x:Thing P(x)
_ALL_THING_P = _all_in("Thing", _X, _p(_X))
# ∃y Q(y), the quantifier typed by the default sort
_EX_Q = Quantifier("∃", _Y, _q(_Y))


# ---------------------------------------------------------------------------
# The export
# ---------------------------------------------------------------------------

def test_an_unsorted_quantifier_beside_a_sort_called_thing_is_refused_by_name():
    """``∀x:Thing P(x) ⊢ ∀y P(y)`` is not valid in the kit's reading, and the export used to
    write the conjecture as ``forall y : Thing . P(y)``, which is."""
    with pytest.raises(ValueError) as caught:
        to_casl_spec([_ALL_THING_P], conjectures=[Quantifier("∀", _Y, _p(_Y))])
    message = str(caught.value)
    assert "'Thing'" in message
    assert "default_sort=" in message
    assert "'Thing1'" in message


def test_a_single_formula_with_both_is_refused_as_well():
    formula = _all_in("Thing", _X, And(_p(_X), _EX_Q))
    with pytest.raises(ValueError, match="default_sort="):
        formula_to_casl(formula)


def test_another_default_sort_keeps_the_two_apart():
    formula = _all_in("Thing", _X, And(_p(_X), _EX_Q))
    text = formula_to_casl(formula, default_sort="Individual")
    assert "forall x : Thing" in text
    assert "exists y : Individual . Q(y)" in text
    spec = to_casl_spec([_ALL_THING_P, _EX_Q], default_sort="Individual")
    assert "sorts Individual, Thing" in spec
    assert "P : Thing" in spec
    assert "Q : Individual" in spec
    assert ". forall x : Thing . P(x)" in spec
    assert ". exists y : Individual . Q(y)" in spec


def test_the_refusal_follows_the_default_sort_that_was_asked_for():
    """With ``default_sort="Individual"`` it is a sort called ``Individual`` that clashes, and
    the refusal suggests ``Individual1``; a sort called ``Thing`` is then simply a sort."""
    individual = _all_in("Individual", _X, _p(_X))
    with pytest.raises(ValueError) as caught:
        to_casl_spec([individual, _EX_Q], default_sort="Individual")
    assert "'Individual'" in str(caught.value)
    assert "'Individual1'" in str(caught.value)
    spec = to_casl_spec([_ALL_THING_P, _EX_Q], default_sort="Individual")
    assert "sorts Individual, Thing" in spec


def test_a_sort_called_thing_is_the_callers_own_when_no_position_needs_the_default():
    """Every position is typed by the formulas themselves: nothing is defaulted, so nothing
    is shared and nothing is refused."""
    spec = to_casl_spec([_ALL_THING_P], conjectures=[_ex_in("Thing", _Z, _p(_Z))])
    assert "sorts Thing" in spec
    assert ". forall x : Thing . P(x)" in spec
    assert ". exists z : Thing . P(z) %implied" in spec


def test_a_constant_that_is_connected_to_the_sort_is_not_a_defaulted_position():
    """``P(alice)`` puts ``alice`` where ``∀x:Thing P(x)`` puts ``x``: it is of sort ``Thing`` by
    the formulas, not by default."""
    spec = to_casl_spec([_ALL_THING_P, _p(Constant("alice"))])
    assert "ops alice : Thing" in spec


def test_a_constant_no_annotation_reaches_is_a_defaulted_position():
    """``R(alice)`` has no sort anywhere but the default one, so it would silently be a ``Thing``
    of the caller's."""
    with pytest.raises(ValueError, match="default_sort="):
        to_casl_spec([_ALL_THING_P, Atom("R", [Constant("alice")])])


def test_a_function_value_no_annotation_reaches_is_a_defaulted_position():
    value = Function("f", [Constant("alice")])
    with pytest.raises(ValueError, match="default_sort="):
        to_casl_spec([_ALL_THING_P, Atom("R", [value])])


def test_without_any_sort_of_the_callers_the_default_sort_is_as_before():
    spec = to_casl_spec([_EX_Q])
    assert "sorts Thing" in spec
    assert "preds Q : Thing" in spec
    assert ". exists y : Thing . Q(y)" in spec


@pytest.mark.parametrize("subsorts", [{"Entity": ["Thing"]}, {"Thing": ["Entity"]}])
def test_a_subsort_declaration_with_the_default_sorts_name_is_refused_when_the_default_is_used(
        subsorts):
    formulas = [_all_in("Entity", _X, _p(_X)), _EX_Q]
    with pytest.raises(ValueError, match="default_sort="):
        to_casl_spec(formulas, subsorts=subsorts)
    spec = to_casl_spec(formulas, subsorts=subsorts, default_sort="Individual")
    assert ". exists y : Individual . Q(y)" in spec


@pytest.mark.parametrize("subsorts, edge", [({"Entity": ["Thing"]}, "sort Entity < Thing"),
                                            ({"Thing": ["Entity"]}, "sort Thing < Entity")])
def test_a_subsort_declaration_with_the_default_sorts_name_is_the_callers_when_the_default_is_unused(
        subsorts, edge):
    spec = to_casl_spec([_all_in("Entity", _X, _p(_X))], subsorts=subsorts)
    assert edge in spec


# ---------------------------------------------------------------------------
# The Hets backend picks a default sort nobody has
# ---------------------------------------------------------------------------

def test_the_default_sort_is_thing_unless_a_sort_of_the_problem_is_called_thing():
    from unicode_logic_kit.atp.hets_backend import _default_sort_for
    assert _default_sort_for([]) == "Thing"
    assert _default_sort_for([_EX_Q]) == "Thing"
    assert _default_sort_for([_all_in("Entity", _X, _p(_X))]) == "Thing"
    assert _default_sort_for([_ALL_THING_P]) == "Thing1"
    assert _default_sort_for([_EX_Q, _p(SortedConstant("alice", "Thing"))]) == "Thing1"


def test_the_first_free_numbered_default_sort_is_taken():
    from unicode_logic_kit.atp.hets_backend import _default_sort_for
    thing, thing1 = _all_in("Thing", _X, _p(_X)), _all_in("Thing1", _X, _p(_X))
    assert _default_sort_for([thing, thing1]) == "Thing2"
    assert _default_sort_for([thing1]) == "Thing"
    assert _default_sort_for([thing, _all_in("Thing2", _Y, _q(_Y))]) == "Thing1"


class _FakeClient:
    """HetsClient stand-in that records the specification it is sent and finds every goal Open."""

    last_spec = None

    def __init__(self, base_url, *, timeout=30.0):
        pass

    def upload(self, text, filename):
        _FakeClient.last_spec = text
        return "/tmp/fake/kit_problem.casl"

    def _goals(self):
        return [{"name": "Ax1", "result": "Open",
                 "used_prover": {"identifier": "SPASS", "name": "SPASS"},
                 "used_translation": "CASL2TPTP_FOF", "prover_output": "",
                 "used_time": None, "tactic_script": None}]

    def prove(self, iri, node, *, reasoner=None, translation=None, time_limit=10):
        return self._goals()

    def consistency_check(self, iri, node, *, reasoner="darwin-non-fd", time_limit=10):
        return self._goals()


@pytest.fixture()
def stubbed_server(monkeypatch):
    _FakeClient.last_spec = None
    monkeypatch.setattr(hets_pkg, "HetsClient", _FakeClient)
    monkeypatch.setattr(hets_pkg, "discover_hets_url",
                        lambda **kw: ("http://fake:8000", None))
    return _FakeClient


def test_a_problem_with_a_sort_called_thing_is_sent_with_another_default_sort(stubbed_server):
    """``∀x:Thing P(x), ∃y Q(y) ⊢ ∃z:Thing P(z)``: the sort ``Thing`` is the user's, so the
    unsorted ``∃y`` is typed by ``Thing1``."""
    verdict = get_backend("hets").decide(_ex_in("Thing", _Z, _p(_Z)), [_ALL_THING_P, _EX_Q])
    assert verdict.reason == "incomplete", verdict.detail       # reached the server
    spec = stubbed_server.last_spec
    assert "sorts Thing, Thing1" in spec
    assert "Q : Thing1" in spec
    assert ". exists y : Thing1 . Q(y)" in spec
    assert ". forall x : Thing . P(x)" in spec


def test_a_problem_without_such_a_sort_keeps_thing(stubbed_server):
    get_backend("hets").decide(Quantifier("∃", _Z, _q(_Z)), [_EX_Q])
    spec = stubbed_server.last_spec
    assert "sorts Thing\n" in spec
    assert "Thing1" not in spec
    assert ". exists y : Thing . Q(y)" in spec


def test_the_consistency_route_picks_the_default_sort_the_same_way(stubbed_server):
    result = HetsBackend().check_consistency([_ALL_THING_P, _EX_Q])
    assert result["result"] == "Open"
    spec = stubbed_server.last_spec
    assert "sorts Thing, Thing1" in spec
    assert ". exists y : Thing1 . Q(y)" in spec


def test_a_problem_that_equates_the_user_sort_with_the_universe_is_still_not_sent(stubbed_server):
    """``∀x:Thing P(x) ⊢ ∀y P(y)`` asks about the whole universe; the typed text has no way to
    say that, so it is unsupported and nothing goes over the wire."""
    verdict = get_backend("hets").decide(Quantifier("∀", _Y, _p(_Y)), [_ALL_THING_P])
    assert (verdict.status, verdict.reason) == ("unknown", "unsupported")
    assert stubbed_server.last_spec is None


# ---------------------------------------------------------------------------
# Live
# ---------------------------------------------------------------------------

@pytest.mark.hets_live
@pytest.mark.skipif(not hets_available(), reason="no running hets-server")
def test_live_a_problem_with_a_sort_called_thing_is_proved_with_a_free_default_sort():
    """``∀x:Thing P(x), ∃y Q(y) ⊢ ∃z:Thing P(z)`` holds (the premise gives ``P`` of every member
    of ``Thing`` and ``Thing`` is non-empty); SPASS proves the text with ``Thing1``."""
    verdict = get_backend("hets").decide(_ex_in("Thing", _Z, _p(_Z)), [_ALL_THING_P, _EX_Q],
                                         reasoner="SPASS")
    assert verdict.status == "proved", verdict.detail
