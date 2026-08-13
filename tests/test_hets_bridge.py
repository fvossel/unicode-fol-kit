"""Tests for the Hets comorphism bridge (unicode_fol_kit.hets.bridge).

The bridge turns a running hets-server's ``GET /translations`` list into
``hets:<Name>`` edges in the kit's comorphism registry. Offline tests stub
:class:`HetsClient` so registration and edge behaviour are checked without a
server; the live class (``hets_live`` marker, serial) registers against the
real container and replays the translation whose output syntax was verified
by hand during the wire-protocol probing (``CASL2SoftFOL`` renders SoftFOL/
DFG text with ``list_of_symbols``/``formula(...)`` items).

Registry hygiene: offline tests register only clearly-fake edge names
(``hets:TestOnly…``) whose source label ``"casl"`` no native edge shares, so
the deliberately-global DEFAULT_REGISTRY keeps working for every other test
in the process; the live test registers the server's real edges, which is
exactly what a user would do.
"""

import pytest

from unicode_fol_kit import api
from unicode_fol_kit.comorphism import DEFAULT_REGISTRY
from unicode_fol_kit.hets import bridge
from unicode_fol_kit.hets.bridge import (
    HETS_EDGE_PREFIX,
    register_hets_comorphisms,
)
from unicode_fol_kit.hets.docker import hets_available


class _FakeClient:
    """Stands in for HetsClient: canned translations, recorded theory calls."""

    #: (base_url, timeout) of every construction, for assertion.
    constructed = []

    def __init__(self, base_url, *, timeout=30.0):
        _FakeClient.constructed.append((base_url, timeout))
        self.base_url = base_url

    def upload(self, text, filename):
        self.last_upload = (text, filename)
        return f"/tmp/fake/{filename}"

    def translations(self, iri):
        return ["TestOnlyB", "TestOnlyA", "TestOnlyA"]   # dupe on purpose

    def dg(self, iri):
        return {"DGraph": {"DGNode": [{"name": "KitExport"}]}}

    def theory(self, iri, *, node=None, translation=None):
        return f"translated({translation}) of {iri} at {node}"


@pytest.fixture()
def fake_client(monkeypatch):
    _FakeClient.constructed = []
    monkeypatch.setattr(bridge, "HetsClient", _FakeClient)
    return _FakeClient


def test_register_returns_sorted_deduplicated_edge_names(fake_client):
    """The fake server lists TestOnlyB, TestOnlyA, TestOnlyA; registration
    must come back deduplicated and sorted: hets:TestOnlyA, hets:TestOnlyB."""
    names = register_hets_comorphisms(url="http://fake:1")
    assert names == ["hets:TestOnlyA", "hets:TestOnlyB"]


def test_registered_edge_shape_and_note(fake_client):
    """Each edge runs casl -> hets:<Name> (unique target label — deliberate,
    see the module docstring) and its note names the backing server."""
    register_hets_comorphisms(url="http://fake:1")
    (edge,) = DEFAULT_REGISTRY.find_path("casl", "hets:TestOnlyA")
    assert edge.name == "hets:TestOnlyA"
    assert edge.source == "casl"
    assert edge.target == "hets:TestOnlyA"
    assert edge.lossy is False
    assert "http://fake:1" in edge.note


def test_edge_apply_routes_spec_text_through_theory(fake_client):
    """apply() must upload the GIVEN spec text, resolve the single
    development-graph node, and fetch /theory with the edge's own comorphism
    name — checked through api.translate so the whole seven-verb path is
    exercised, term type str included."""
    register_hets_comorphisms(url="http://fake:1")
    result = api.translate("spec X = end", "casl", "hets:TestOnlyB")
    assert result.result == ("translated(TestOnlyB) of "
                             "/tmp/fake/kit_translate.casl at KitExport")
    assert result.path == ("hets:TestOnlyB",)
    assert result.lossy is False


def test_reregistration_replaces_instead_of_raising(fake_client):
    """Pointing the bridge at a server twice must not raise (replace=True):
    the second registration simply rebinds the edges."""
    register_hets_comorphisms(url="http://fake:1")
    names = register_hets_comorphisms(url="http://fake:2")
    assert names == ["hets:TestOnlyA", "hets:TestOnlyB"]
    (edge,) = DEFAULT_REGISTRY.find_path("casl", "hets:TestOnlyA")
    assert "http://fake:2" in edge.note


def test_edge_prefix_constant():
    assert HETS_EDGE_PREFIX == "hets:"


def test_refresh_unregisters_edges_the_new_server_dropped(fake_client, monkeypatch):
    """Review-hardened refresh contract: after re-registering against a
    server that no longer offers TestOnlyB, the stale edge must be GONE
    from the registry (not left as a closure bound to the old URL)."""
    register_hets_comorphisms(url="http://fake:1")
    assert DEFAULT_REGISTRY.find_path("casl", "hets:TestOnlyB")

    monkeypatch.setattr(_FakeClient, "translations",
                        lambda self, iri: ["TestOnlyA"])
    names = register_hets_comorphisms(url="http://fake:2")
    assert names == ["hets:TestOnlyA"]
    with pytest.raises(ValueError):
        DEFAULT_REGISTRY.find_path("casl", "hets:TestOnlyB")


@pytest.mark.hets_live
@pytest.mark.skipif(not hets_available(), reason="no running hets-server")
class TestBridgeLive:
    """Against the real container (serial; see hets_live convention)."""

    def test_real_registration_contains_casl2softfol(self):
        names = register_hets_comorphisms()
        assert "hets:CASL2SoftFOL" in names

    def test_casl2softfol_translation_renders_softfol_text(self):
        """The hand-verified wire fact: translating the probe spec through
        CASL2SoftFOL yields SoftFOL/DFG concrete syntax — symbol list plus
        formula items (the exact strings observed live on 2026-08-12)."""
        register_hets_comorphisms()
        result = api.translate(bridge._PROBE_SPEC, "casl", "hets:CASL2SoftFOL")
        assert "list_of_symbols" in result.result
        assert "formula(" in result.result
