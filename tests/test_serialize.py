"""Tests for the versioned JSON envelope (fol/serialize.py).

Hand-checked expectations:

* ``serialize`` wraps the UNCHANGED ``to_dict()`` tree — the bare node format
  is not touched, so pre-envelope consumers (from_dict) keep working.
* ``deserialize`` accepts envelope dicts, bare node dicts, and JSON strings of
  either; it must reject future schema versions LOUDLY (silently misreading
  newer data would be worse than failing).
* Round-trip through json.dumps/loads reconstructs an equal Node for every
  parser mode's flagship constructs (nodes are frozen dataclasses, so ``==``
  is structural equality).
"""

import json

import pytest

from unicode_fol_kit import (
    MSFLParser, Node, SCHEMA_VERSION, serialize, deserialize,
)


def _roundtrip(node: Node) -> Node:
    """serialize → json text → deserialize."""
    return deserialize(json.loads(json.dumps(serialize(node))))


def test_envelope_shape_and_version():
    """The envelope carries schema_version and the bare tree under 'root'."""
    node = MSFLParser().parse("P(x) ∧ Q(x)")
    env = serialize(node)
    assert env["schema_version"] == SCHEMA_VERSION == 1
    assert env["root"] == node.to_dict()          # bare format unchanged
    assert set(env.keys()) == {"schema_version", "root"}


@pytest.mark.parametrize("mode_kwargs, text", [
    ({}, "∀x (P(x) → Q(x))"),
    ({}, "∃x (P(x) ∧ ¬Q(f(x, c)))"),
    ({"many_sorted": True}, "∀x:Nat P(x)"),
    ({"fuzzy": True}, "P(x) ⊗ Q(x)"),
    ({"modal": True}, "□P → ◇P"),
    ({"modal": True}, "K_alice P ∧ Ⓞ Q"),
    ({"second_order": True}, "∀X X(c)"),
    ({"dependence": True}, "∀x ∃y (=(x, y) ∧ P(y))"),
])
def test_roundtrip_across_parser_modes(mode_kwargs, text):
    """serialize/deserialize round-trips flagship constructs of each mode."""
    node = MSFLParser(**mode_kwargs).parse(text)
    assert _roundtrip(node) == node


def test_deserialize_accepts_bare_node_dict():
    """Pre-envelope data (bare to_dict output) keeps loading."""
    node = MSFLParser().parse("P(a) ∨ Q(b)")
    assert deserialize(node.to_dict()) == node


def test_deserialize_accepts_json_string():
    """A JSON string of the envelope is accepted directly."""
    node = MSFLParser().parse("¬P(x)")
    assert deserialize(json.dumps(serialize(node))) == node


def test_deserialize_rejects_future_version():
    """A newer schema_version must raise, not silently misread."""
    node = MSFLParser().parse("P(c)")
    env = serialize(node)
    env["schema_version"] = SCHEMA_VERSION + 1
    with pytest.raises(ValueError, match="newer"):
        deserialize(env)


def test_deserialize_rejects_garbage():
    """Neither envelope nor bare node dict → ValueError; non-dict → TypeError."""
    with pytest.raises(ValueError):
        deserialize({"foo": "bar"})
    with pytest.raises(TypeError):
        deserialize(42)
    with pytest.raises(ValueError):
        deserialize({"schema_version": 1})        # envelope without root
    with pytest.raises(ValueError):
        deserialize({"schema_version": 0, "root": {}})  # invalid version


def test_serialize_rejects_non_node():
    """serialize is for Nodes only — a dict is not silently re-wrapped."""
    with pytest.raises(TypeError):
        serialize({"_type": "Atom"})
