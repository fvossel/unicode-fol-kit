"""Versioned JSON serialisation envelope for AST nodes.

``Node.to_dict()`` / ``Node.from_dict()`` produce and consume the *bare* node
dictionaries (``{"_type": ..., ...}``) and remain unversioned — they are the
recursive building blocks. This module adds the STABLE, VERSIONED envelope that
external consumers (pipelines, dataset tooling, MCP clients, the CLI's
``--to json``) should exchange:

    {"schema_version": 1, "root": {"_type": "Atom", ...}}

``schema_version`` is bumped only when the bare node format itself changes
incompatibly (a renamed ``_type``, a removed field, a changed field meaning) —
NOT on ordinary releases, and never for purely additive node types (an old
reader that meets an unknown ``_type`` fails loudly either way).
``deserialize`` accepts both the envelope and a bare node dict, so data written
before this module existed keeps loading.
"""

from typing import Union

from .nodes import Node

__all__ = ["SCHEMA_VERSION", "serialize", "deserialize"]

# History:
#   1 — first versioned format (0.20.0). Identical bare-node dicts to every
#       release since to_dict()/from_dict() were introduced; the envelope is new.
SCHEMA_VERSION = 1


def serialize(node: Node) -> dict:
    """Wrap ``node.to_dict()`` in the versioned envelope.

    The result is JSON-compatible (``json.dumps`` works on it directly) and is
    the format all new external consumers should store and exchange.
    """
    if not isinstance(node, Node):
        raise TypeError(f"serialize expects a Node, got {type(node).__name__}")
    return {"schema_version": SCHEMA_VERSION, "root": node.to_dict()}


def deserialize(data: Union[dict, str]) -> Node:
    """Reconstruct a node from :func:`serialize` output (or a bare node dict).

    Accepts three shapes, in order of preference:

    * the versioned envelope ``{"schema_version": n, "root": {...}}`` —
      rejected with ``ValueError`` if ``n`` is newer than this library
      understands (reading data from the future silently would be worse);
    * a bare ``{"_type": ...}`` node dict (pre-envelope data keeps loading);
    * a JSON string of either of the above.
    """
    if isinstance(data, str):
        import json
        data = json.loads(data)
    if not isinstance(data, dict):
        raise TypeError(f"deserialize expects a dict or JSON string, got {type(data).__name__}")

    if "schema_version" in data:
        version = data["schema_version"]
        if not isinstance(version, int) or version < 1:
            raise ValueError(f"deserialize: invalid schema_version {version!r}")
        if version > SCHEMA_VERSION:
            raise ValueError(
                f"deserialize: schema_version {version} is newer than this "
                f"unicode-fol-kit understands (max {SCHEMA_VERSION}) — upgrade the library."
            )
        root = data.get("root")
        if not isinstance(root, dict):
            raise ValueError("deserialize: envelope is missing its 'root' node dict.")
        return Node.from_dict(root)

    if "_type" in data:
        return Node.from_dict(data)

    raise ValueError(
        "deserialize: dict is neither a versioned envelope (schema_version/root) "
        "nor a bare node dict (_type)."
    )
