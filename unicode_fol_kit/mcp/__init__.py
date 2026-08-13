"""MCP server exposing the kit's seven-verb API as tools.

The Model Context Protocol (MCP) is the 2025/26 integration standard for
giving LLM agents typed tool access. This subpackage puts the kit's core
verbs (:mod:`unicode_fol_kit.api`) behind an MCP server so any MCP client —
Claude Code/Desktop, an agent framework, an editor — can parse, check,
prove, refute, diagnose, translate and verbalize formulas without writing a
line of Python. The repair loop inverts naturally: the kit deliberately
never rewrites formula text itself, and over MCP the CLIENT LLM is the
fixer — call ``diagnose``, apply the suggestion yourself, call again.

Optional dependency: ``pip install unicode-fol-kit[mcp]`` (the ``mcp``
Python SDK, >= 2.0). This subpackage is therefore NOT imported by
``unicode_fol_kit/__init__``; import it explicitly
(``from unicode_fol_kit.mcp import create_server``) or run the server with
``python -m unicode_fol_kit.mcp``.

Every tool takes formula TEXT (any supported dialect, auto-detected via
``api.parse_any``) and returns the same JSON-compatible dicts the Python
API returns — nothing is invented at this layer; it is a thin, faithful
projection of :mod:`unicode_fol_kit.api` plus one introspection tool
(``list_backends``).
"""

from .server import create_server, main

__all__ = ["create_server", "main"]
