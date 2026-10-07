"""The portfolio takes ``subsorts=`` as any mapping, a signature's read-only one included.

``Signature.subsorts`` is a read-only view, and ``subsorts=sig.subsorts`` is how a caller hands the subsort
edges on. In a race the options travel to worker processes, and the view could not be sent: the member that
reads the option ended ``error`` / ``infra`` and the race had no answer, while the same call with ``jobs=1``
answered.

By hand, with the edge ``Human ⊆ Animal``: ``Human(soc) ⊢ Animal(soc)`` has no countermodel (``soc`` is in
Human, Human is inside Animal), so the model finder finds none and is not ``refuted``. Without the edge the
structure with ``Human = {soc}`` and ``Animal = ∅`` is a countermodel: ``refuted``.
"""

import types

import pytest

from unicode_logic_kit.atp.portfolio import _as_plain_data, portfolio_prove
from unicode_logic_kit.fol.nodes import Atom, Constant
from unicode_logic_kit.fol.signature import Signature

PREMISE = Atom("Human", [Constant("soc")])
GOAL = Atom("Animal", [Constant("soc")])
SIGNATURE = Signature.from_dict({"sorts": ["Human", "Animal"], "subsorts": {"Human": ["Animal"]}})


def member(verdict, name):
    """The part of a no-verdict summary that speaks about the member ``name``."""
    [part] = [part for part in (verdict.detail or "").split("; ") if part.startswith(name + ":")]
    return part


def test_the_signature_hands_out_a_read_only_view():
    assert isinstance(SIGNATURE.subsorts, types.MappingProxyType)
    assert dict(SIGNATURE.subsorts) == {"Human": frozenset({"Animal"})}


def test_a_read_only_mapping_becomes_a_dict_with_the_same_entries():
    plain = _as_plain_data(SIGNATURE.subsorts)
    assert type(plain) is dict and plain == {"Human": frozenset({"Animal"})}
    assert _as_plain_data({"Human": ["Animal"]}) == {"Human": ["Animal"]}
    assert _as_plain_data("constant") == "constant" and _as_plain_data(None) is None


@pytest.mark.parametrize("jobs", [1, 2])
def test_with_the_edge_no_countermodel_is_found_whichever_way_the_members_are_run(jobs):
    verdict = portfolio_prove(GOAL, [PREMISE], backends=["z3", "modelfinder"], jobs=jobs,
                              subsorts=SIGNATURE.subsorts, timeout=8000)
    assert verdict.status == "unknown", verdict
    assert "pickle" not in verdict.detail and "error/infra" not in verdict.detail
    assert member(verdict, "modelfinder").startswith("modelfinder:unknown/")


@pytest.mark.parametrize("jobs", [1, 2])
def test_the_view_and_a_dict_of_the_same_edges_give_the_same_answer(jobs):
    as_view = portfolio_prove(GOAL, [PREMISE], backends=["z3", "modelfinder"], jobs=jobs,
                              subsorts=SIGNATURE.subsorts, timeout=8000)
    as_dict = portfolio_prove(GOAL, [PREMISE], backends=["z3", "modelfinder"], jobs=jobs,
                              subsorts={"Human": ["Animal"]}, timeout=8000)
    assert as_view.status == as_dict.status == "unknown"
    assert member(as_view, "modelfinder") == member(as_dict, "modelfinder")


@pytest.mark.parametrize("jobs", [1, 2])
def test_without_the_edge_the_question_is_refuted(jobs):
    verdict = portfolio_prove(GOAL, [PREMISE], backends=["z3", "modelfinder"], jobs=jobs, timeout=8000)
    assert verdict.status == "refuted", verdict
