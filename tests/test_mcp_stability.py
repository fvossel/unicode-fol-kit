"""Enforcement tests for the MCP tool-surface and comorphism-registry
STABILITY POLICY (see :mod:`unicode_fol_kit.mcp.server`'s and
:mod:`unicode_fol_kit.comorphism`'s module docstrings for the prose).

Three baselines are pinned here, each hand-transcribed from ONE real call to
the introspection API it describes:

* ``TOOL_SCHEMA_BASELINE`` -- every registered tool's ``(sorted(required),
  {property: type-signature})``, obtained by calling
  ``asyncio.run(create_server().list_tools())`` once (independently
  reproducible: any reviewer can re-run that call and diff the printed
  dict by eye). This is strictly stronger than
  ``test_mcp_server.py::test_server_registers_all_thirtyseven_tools``,
  which pins tool NAMES only -- a parameter rename, a type flip, an
  optional parameter silently turned mandatory, or a required parameter
  silently turned optional would still pass that test, and is exactly what
  this one is for.
* ``COMORPHISM_EDGE_BASELINE`` -- ``sorted((name, source, target, lossy)
  for e in DEFAULT_REGISTRY.edges())`` for the registry's current 9 edges,
  strengthening ``test_mcp_server.py::test_list_translations_names_the_
  default_edges``'s name-only ``<=`` check to also pin each edge's
  source/target/lossy, all three of which comorphism.py's own STABILITY
  POLICY docstring names as stable. The five edges after the original four
  (``to_fol``, ``qml_translate``, ``to_msfol``, ``drs_to_fol``,
  ``fol_to_drs``) were added, never changed: the original four are pinned
  exactly as they were before the registry grew.
* ``RESULT_KEYS_BASELINE`` -- the top-level keys of what ``translate`` and
  ``list_translations`` return (and of each ``list_translations`` edge row).
  The tool layer promises "dict keys only ever gain siblings"; the schema
  baseline cannot see that, because a result's shape is not in the input
  schema. ``axioms`` / ``axioms_unicode`` / ``guarantee`` (translate) and
  ``logics`` / ``guarantee`` / ``options`` / ``side_axioms``
  (list_translations) are the siblings gained when the registry started
  carrying side axioms; the keys that were there before are still pinned.

All three checks are SUBSET checks in the allowed direction (a new tool, a new
optional parameter, a new comorphism edge, or a new result key must never fail
them) and EQUALITY-grade in the forbidden direction (a pinned
tool/parameter/edge/key disappearing, a parameter's required-ness changing in
EITHER direction, a parameter's type changing, or an edge's
``source``/``target``/``lossy`` changing must all fail them). The
``_..._violations`` helpers below are exercised directly against small,
hand-built MCPServer / ComorphismRegistry / dict fixtures ("a monkeypatched
server") to prove they actually draw that line, not just that today's real
registry happens to be clean.
"""

import asyncio
from typing import Optional

import pytest

pytest.importorskip("mcp", reason="optional [mcp] extra not installed")

from unicode_fol_kit.comorphism import (   # noqa: E402
    Comorphism,
    ComorphismRegistry,
    DEFAULT_REGISTRY,
)
from unicode_fol_kit.mcp.server import create_server   # noqa: E402

# ---------------------------------------------------------------------------
# Pinned baseline #1: every tool's input_schema, reduced to required-set +
# a per-property type signature. Transcribed from one
# ``asyncio.run(create_server().list_tools())`` call (2026, after the
# probability_bounds strategy/max_columns passthrough landed -- both
# already appear below as optional ``integer``/``string`` parameters; and
# again for ``translate`` once it forwarded the comorphism edges' own options
# -- ``frame``/``systems``/``temporal_closure``/``signature``/``mode``/
# ``bridges``, every one optional).
# ---------------------------------------------------------------------------

TOOL_SCHEMA_BASELINE = {
    "check_consistency": (["formulas"], {
        "dialect": "anyOf[null,string]", "formulas": "array[string]",
        "logic": "string", "timeout_ms": "integer"}),
    "check_equivalence": (["formula1", "formula2"], {
        "dialect": "anyOf[null,string]", "formula1": "string",
        "formula2": "string", "method": "string", "timeout_ms": "integer"}),
    "check_formula": (["text"], {
        "dialect": "anyOf[null,string]", "signature": "anyOf[null,object]",
        "text": "string"}),
    "check_molecule": (["formula", "smiles"], {
        "all_different": "boolean", "budget": "anyOf[integer,null]",
        "dialect": "string", "formula": "string",
        "include_computed": "boolean", "smiles": "string",
        "with_spans": "boolean"}),
    "check_molecules": (["formula", "smiles_list"], {
        "all_different": "boolean", "budget": "anyOf[integer,null]",
        "dialect": "string", "formula": "string",
        "include_computed": "boolean", "smiles_list": "array[string]",
        "with_spans": "boolean"}),
    "chemical_signature": ([], {}),
    "compare_formulas": (["gold", "predicted"], {
        "converses": "anyOf[array,null]", "dialect": "anyOf[null,string]",
        "gold": "string", "predicted": "string", "timeout_ms": "integer"}),
    "detect_dialect": (["text"], {"text": "string"}),
    "diagnose": (["text"], {
        "dialect": "anyOf[null,string]", "signature": "anyOf[null,object]",
        "text": "string"}),
    "dl_abox_consistent": (["concepts"], {
        "concepts": "array[array]", "distinct": "anyOf[array,null]",
        "roles": "anyOf[array,null]", "syntax": "string",
        "tbox": "anyOf[array,null]"}),
    "dl_classify": ([], {
        "concepts": "anyOf[array,null]", "syntax": "string",
        "tbox": "anyOf[array,null]"}),
    "dl_concept_satisfiable": (["concept"], {
        "concept": "string", "syntax": "string",
        "tbox": "anyOf[array,null]"}),
    "dl_equivalent": (["c", "d"], {
        "c": "string", "d": "string", "syntax": "string",
        "tbox": "anyOf[array,null]"}),
    "dl_instance_check": (["concept", "concepts", "individual"], {
        "concept": "string", "concepts": "array[array]",
        "distinct": "anyOf[array,null]", "individual": "string",
        "roles": "anyOf[array,null]", "syntax": "string",
        "tbox": "anyOf[array,null]"}),
    "dl_instance_retrieval": (["concept", "concepts"], {
        "concept": "string", "concepts": "array[array]",
        "distinct": "anyOf[array,null]", "roles": "anyOf[array,null]",
        "syntax": "string", "tbox": "anyOf[array,null]"}),
    "dl_parse_manchester": (["text"], {"kind": "string", "text": "string"}),
    "dl_subsumes": (["sub", "sup"], {
        "sub": "string", "sup": "string", "syntax": "string",
        "tbox": "anyOf[array,null]"}),
    "drs_to_fol": (["text"], {
        "format": "string", "resolve_pronouns": "boolean", "text": "string"}),
    "explain_molecule_failure": (["formula", "smiles"], {
        "all_different": "boolean", "budget": "anyOf[integer,null]",
        "dialect": "string", "formula": "string",
        "include_computed": "boolean", "smiles": "string",
        "with_spans": "boolean"}),
    "find_countermodel": (["formula"], {
        "dialect": "anyOf[null,string]", "formula": "string",
        "logic": "string", "premises": "anyOf[array,null]"}),
    "get_signature": (["formulas"], {
        "dialect": "anyOf[null,string]", "formulas": "array[string]"}),
    "get_syntax_spec": ([], {
        "dialect": "anyOf[null,string]", "topic": "string"}),
    "list_backends": ([], {}),
    "list_translations": ([], {}),
    "molecule_to_structure": (["smiles"], {
        "include_computed": "boolean", "naming": "string",
        "smiles": "string"}),
    "normalize": (["text"], {
        "dialect": "anyOf[null,string]", "form": "string", "text": "string"}),
    "parse_formula": (["text"], {
        "dialect": "anyOf[null,string]", "text": "string"}),
    "probability_bounds": (["conclusion", "constraints"], {
        "conclusion": "string", "constraints": "array[object]",
        "dialect": "anyOf[null,string]", "max_atoms": "integer",
        "max_columns": "integer", "strategy": "string"}),
    "probability_query": (["facts", "goal"], {
        "dialect": "anyOf[null,string]", "facts": "array[object]",
        "goal": "string", "hard_facts": "anyOf[array,null]",
        "max_choice_facts": "integer", "rules": "anyOf[array,null]"}),
    "prove": (["conclusion"], {
        "backends": "anyOf[array,null]", "conclusion": "string",
        "dialect": "anyOf[null,string]", "logic": "string",
        "premises": "anyOf[array,null]", "timeout_ms": "integer"}),
    "render": (["text"], {
        "dialect": "anyOf[null,string]", "text": "string", "to": "string"}),
    "repair_formula": (["text"], {
        "close_free_variables": "boolean", "dialect": "anyOf[null,string]",
        "sanitize_invalid_names": "boolean", "text": "string"}),
    "score_batch": (["predictions", "references"], {
        "converses": "anyOf[array,null]", "method": "string",
        "predictions": "array[string]", "references": "array[string]",
        "timeout_ms": "integer"}),
    "simplify_definition": (["formula"], {
        "all_different": "boolean", "dialect": "string",
        "formula": "string"}),
    "translate": (["from_logic", "term", "to_logic"], {
        "bridges": "anyOf[array,null]", "dialect": "anyOf[null,string]",
        "frame": "anyOf[null,string]", "from_logic": "string",
        "mode": "anyOf[null,string]", "signature": "anyOf[null,object]",
        "systems": "anyOf[null,object]",
        "temporal_closure": "anyOf[boolean,null]", "term": "string",
        "to_logic": "string"}),
    "truth_table": (["text"], {
        "dialect": "anyOf[null,string]", "logic": "string",
        "text": "string"}),
    "verbalize": (["text"], {
        "dialect": "anyOf[null,string]", "text": "string"}),
}

# ---------------------------------------------------------------------------
# Pinned baseline #2: the comorphism DEFAULT_REGISTRY's 9 edges, by
# (name, source, target, lossy) -- ``lossy`` is part of the STABILITY POLICY
# comorphism.py's own docstring states ("no edge ... has its
# source/target/lossy changed"), so it is pinned alongside source/target,
# not just the two. Transcribed from one
# ``sorted((e.name, e.source, e.target, e.lossy) for e in
# DEFAULT_REGISTRY.edges())`` call. The first four are the edges the registry
# had before it grew side axioms; the last five are new, and ``to_msfol``
# (fuzzy -> msfol, a two-valued projection) is the registry's first lossy
# edge.
# ---------------------------------------------------------------------------

COMORPHISM_EDGE_BASELINE = sorted([
    ("concept_to_fol", "alc", "fol", False),
    ("concept_to_modal", "alc", "modal", False),
    ("dependence_to_eso", "team", "eso", False),
    ("standard_translation", "modal", "fol", False),
    ("drs_to_fol", "drs", "fol", False),
    ("fol_to_drs", "fol", "drs", False),
    ("qml_translate", "qml", "fol", False),
    ("to_fol", "msfol", "fol", False),
    ("to_msfol", "fuzzy", "msfol", True),
])

# The edges that predate the side-axiom work, kept apart so a test can say
# "these four are unchanged" rather than only "these nine exist".
_ORIGINAL_EDGES = frozenset({
    "concept_to_fol", "concept_to_modal", "dependence_to_eso",
    "standard_translation"})

# ---------------------------------------------------------------------------
# Pinned baseline #3: the top-level keys the translation tools return.
# ``translate`` before the side-axiom work returned exactly
# {result, source, target, path, lossy, note, unicode}; its siblings
# ``axioms`` / ``axioms_unicode`` / ``guarantee`` came with it.
# ``list_translations`` returned {edges}, each row {name, source, target,
# lossy, note}; ``logics`` and the three per-row keys came with it.
# ---------------------------------------------------------------------------

RESULT_KEYS_BASELINE = {
    "translate": {"result", "source", "target", "path", "lossy", "note",
                  "unicode", "axioms", "axioms_unicode", "guarantee"},
    "list_translations": {"edges", "logics"},
    "list_translations.edge": {"name", "source", "target", "lossy", "note",
                               "guarantee", "options", "side_axioms"},
}


# ---------------------------------------------------------------------------
# Introspection + diffing helpers (exercised on both the real registries and
# small hand-built fixtures below).
# ---------------------------------------------------------------------------

def _prop_type_signature(schema: dict) -> str:
    """A coarse, stable fingerprint of a JSON-schema property's TYPE shape.

    Deliberately ignores ``title``/``default`` (cosmetic, regenerated from
    the property name and the function's default value) and keeps only
    ``type`` -- or, for ``Optional[X]``'s ``anyOf: [{type: X}, {type:
    null}]`` encoding, the sorted set of member types -- plus an array's
    item type. That is exactly the structural information a schema-based
    client's request validation depends on.
    """
    if "type" in schema:
        t = schema["type"]
        if t == "array" and "items" in schema and "type" in schema["items"]:
            return f"array[{schema['items']['type']}]"
        return t
    if "anyOf" in schema:
        return "anyOf[" + ",".join(
            sorted(s.get("type", "?") for s in schema["anyOf"])) + "]"
    return "?"


def _schema_dict(tools) -> dict:
    """``{tool_name: (sorted(required), {property: type_signature})}`` for
    a ``list_tools()`` result -- the same shape as ``TOOL_SCHEMA_BASELINE``."""
    out = {}
    for t in tools:
        schema = t.input_schema
        required = sorted(schema.get("required", []))
        props = schema.get("properties", {})
        types = {name: _prop_type_signature(sub) for name, sub in props.items()}
        out[t.name] = (required, types)
    return out


def _tool_schema_violations(baseline: dict, current: dict) -> list:
    """Human-readable STABILITY POLICY violations; ``[]`` means clean.

    A tool present in ``current`` but not ``baseline`` (a genuinely new
    tool) is never a violation -- additions are the whole point of the
    policy. Per PINNED tool: removal/rename, a vanished parameter, a
    parameter newly required that was not pinned required, a required
    parameter silently demoted to optional, and a changed parameter type
    are all violations (the docstring's "name, type and required/optional
    flag are stable" is a BIDIRECTIONAL claim, so both required->optional
    and optional->required drift are checked); a parameter that gained an
    entry in ``current`` but was absent from the pinned tool's property set
    (a new optional parameter) is not.
    """
    violations = []
    for name, (req, types) in baseline.items():
        if name not in current:
            violations.append(f"tool {name!r}: removed or renamed")
            continue
        cur_req, cur_types = current[name]
        vanished = sorted(set(types) - set(cur_types))
        if vanished:
            violations.append(
                f"tool {name!r}: parameter(s) {vanished} disappeared "
                f"(pinned properties {sorted(types)}, now {sorted(cur_types)})")
        newly_required = sorted(set(cur_req) - set(req))
        if newly_required:
            violations.append(
                f"tool {name!r}: parameter(s) {newly_required} became "
                f"required (pinned required={req}, now required={cur_req})")
        # Restricted to properties still present in ``cur_types`` -- a
        # required parameter that also vanished entirely is already
        # reported above (as "disappeared") and should not additionally be
        # reported here as "became optional".
        formerly_required = sorted(
            (set(req) - set(cur_req)) & set(cur_types))
        if formerly_required:
            violations.append(
                f"tool {name!r}: parameter(s) {formerly_required} became "
                f"optional (pinned required={req}, now required={cur_req})")
        for prop in sorted(set(types) & set(cur_types)):
            if types[prop] != cur_types[prop]:
                violations.append(
                    f"tool {name!r}: parameter {prop!r} changed type "
                    f"{types[prop]!r} -> {cur_types[prop]!r}")
    return violations


def _comorphism_violations(baseline, current) -> list:
    """``[]`` iff every pinned ``(name, source, target, lossy)`` edge is
    still present, unchanged, in ``current``.

    Looked up by NAME (not by whole-tuple membership, unlike the tuple-set
    subset check this replaced) so a source/target change and a lossy
    change are reported as two distinct, readable diffs rather than one
    opaque "missing" line -- comorphism.py's own STABILITY POLICY docstring
    names all three of ``source``/``target``/``lossy`` as stable, so all
    three are checked, not just the two that (name, source, target) alone
    would catch.
    """
    current_by_name = {name: (source, target, lossy)
                        for name, source, target, lossy in current}
    violations = []
    for name, source, target, lossy in baseline:
        cur = current_by_name.get(name)
        if cur is None:
            violations.append(f"comorphism edge {name!r}: missing or renamed")
            continue
        cur_source, cur_target, cur_lossy = cur
        if (cur_source, cur_target) != (source, target):
            violations.append(
                f"comorphism edge {name!r}: source/target changed "
                f"{(source, target)!r} -> {(cur_source, cur_target)!r}")
        if cur_lossy != lossy:
            violations.append(
                f"comorphism edge {name!r}: lossy changed "
                f"{lossy!r} -> {cur_lossy!r}")
    return violations


def _result_key_violations(baseline: dict, current: dict) -> list:
    """``[]`` iff every pinned result key is still present.

    A key that GAINED a sibling is never a violation (that is the whole
    point of "keys only ever gain siblings"); a pinned key that vanished is.
    ``baseline`` / ``current`` map a result name to its set of keys.
    """
    violations = []
    for name, keys in baseline.items():
        if name not in current:
            violations.append(f"result {name!r}: no longer produced")
            continue
        vanished = sorted(set(keys) - set(current[name]))
        if vanished:
            violations.append(
                f"result {name!r}: key(s) {vanished} disappeared "
                f"(pinned {sorted(keys)}, now {sorted(current[name])})")
    return violations


def _current_result_keys() -> dict:
    """The key sets the real tools return today (one real call each)."""
    from unicode_fol_kit.mcp.server import list_translations, translate

    translated = translate("□P", "modal", "fol")
    assert "error" not in translated, translated
    listing = list_translations()
    return {
        "translate": set(translated),
        "list_translations": set(listing),
        "list_translations.edge": set(listing["edges"][0]),
    }


# ---------------------------------------------------------------------------
# The pinned checks against the REAL, current registries.
# ---------------------------------------------------------------------------

def test_tool_schema_baseline_holds_against_the_real_registry():
    server = create_server()
    tools = asyncio.run(server.list_tools())
    current = _schema_dict(tools)
    violations = _tool_schema_violations(TOOL_SCHEMA_BASELINE, current)
    assert violations == []


def test_comorphism_edge_baseline_holds_against_the_real_registry():
    current = sorted((e.name, e.source, e.target, e.lossy)
                     for e in DEFAULT_REGISTRY.edges())
    violations = _comorphism_violations(COMORPHISM_EDGE_BASELINE, current)
    assert violations == []


def test_the_original_four_edges_are_unchanged_by_the_registry_growing():
    """The promise is about edges that EXISTED: name, source, target and
    lossy of the original four must read exactly as they did before the
    registry gained side axioms, guarantees and five more edges. (Their
    ``guarantee`` is new vocabulary and is deliberately not pinned: declaring
    a weaker one is a correction, not a break.)"""
    originals = {(e.name, e.source, e.target, e.lossy)
                 for e in DEFAULT_REGISTRY.edges()
                 if e.name in _ORIGINAL_EDGES}
    assert originals == {
        ("concept_to_fol", "alc", "fol", False),
        ("concept_to_modal", "alc", "modal", False),
        ("dependence_to_eso", "team", "eso", False),
        ("standard_translation", "modal", "fol", False),
    }


def test_result_key_baseline_holds_against_the_real_tools():
    violations = _result_key_violations(RESULT_KEYS_BASELINE,
                                        _current_result_keys())
    assert violations == []


# ---------------------------------------------------------------------------
# Both directions, on hand-built fixtures ("a monkeypatched server") rather
# than the real registry -- proving the checking functions above actually
# draw the allowed/forbidden line, not merely that today's real registry is
# clean.
# ---------------------------------------------------------------------------

def _widget_v1(item: str, count: int = 1) -> dict:
    """Synthetic tool, v1: required=['item'], optional count:int."""
    return {"item": item, "count": count}


def _fixture_schema(fns_with_names) -> dict:
    """Build a standalone MCPServer, register ``fns_with_names`` (a list of
    ``(name, fn)``) on it, and return its real SDK-derived ``_schema_dict``
    -- exercising the actual introspection path, not a hand-typed stand-in."""
    from mcp.server import MCPServer

    server = MCPServer("stability-fixture")
    for name, fn in fns_with_names:
        server.tool(name=name)(fn)
    return _schema_dict(asyncio.run(server.list_tools()))


_WIDGET_BASELINE = _fixture_schema([("widget", _widget_v1)])


def test_new_optional_parameter_passes():
    def widget_v2(item: str, count: int = 1, label: Optional[str] = None) -> dict:
        return {"item": item, "count": count, "label": label}

    current = _fixture_schema([("widget", widget_v2)])
    assert _tool_schema_violations(_WIDGET_BASELINE, current) == []


def test_a_brand_new_tool_alongside_the_old_one_passes():
    def gadget(x: int) -> dict:
        return {"x": x}

    current = _fixture_schema([("widget", _widget_v1), ("gadget", gadget)])
    assert _tool_schema_violations(_WIDGET_BASELINE, current) == []


def test_a_removed_tool_fails_with_a_readable_diff():
    current = _fixture_schema([])
    violations = _tool_schema_violations(_WIDGET_BASELINE, current)
    assert len(violations) == 1
    assert "widget" in violations[0] and "removed" in violations[0]


def test_a_renamed_tool_fails_with_a_readable_diff():
    current = _fixture_schema([("widget_renamed", _widget_v1)])
    violations = _tool_schema_violations(_WIDGET_BASELINE, current)
    assert len(violations) == 1 and "widget" in violations[0]


def test_a_parameter_type_change_fails_with_a_readable_diff():
    def widget_bad_type(item: str, count: str = "1") -> dict:
        return {"item": item, "count": count}

    current = _fixture_schema([("widget", widget_bad_type)])
    violations = _tool_schema_violations(_WIDGET_BASELINE, current)
    assert len(violations) == 1
    assert "count" in violations[0] and "integer" in violations[0] \
        and "string" in violations[0]


def test_an_optional_parameter_turned_required_fails_with_a_readable_diff():
    def widget_bad_required(item: str, count: int) -> dict:
        return {"item": item, "count": count}

    current = _fixture_schema([("widget", widget_bad_required)])
    violations = _tool_schema_violations(_WIDGET_BASELINE, current)
    assert len(violations) == 1
    assert "count" in violations[0] and "required" in violations[0]


def _widget_all_required(item: str, count: int) -> dict:
    """Synthetic tool, all-required variant: item and count both
    required -- the baseline against which "silently demoted to optional"
    is checked (``_WIDGET_BASELINE`` above already has ``count`` optional,
    so it cannot exercise a required->optional transition)."""
    return {"item": item, "count": count}


_WIDGET_ALL_REQUIRED_BASELINE = _fixture_schema([("widget", _widget_all_required)])


def test_a_required_parameter_turned_optional_fails_with_a_readable_diff():
    # The docstring's "required/optional flag are stable" is bidirectional:
    # a pinned-required parameter silently gaining a default (so an old,
    # strict client that always sent it keeps working, but a client relying
    # on the server always REQUIRING it -- e.g. to reject an incomplete
    # request itself -- would silently stop getting that) must fail too,
    # not just the optional->required tightening the previous test covers.
    def widget_now_optional(item: str, count: int = 1) -> dict:
        return {"item": item, "count": count}

    current = _fixture_schema([("widget", widget_now_optional)])
    violations = _tool_schema_violations(_WIDGET_ALL_REQUIRED_BASELINE, current)
    assert len(violations) == 1
    assert "count" in violations[0] and "optional" in violations[0]


def test_a_vanished_parameter_fails_with_a_readable_diff():
    def widget_dropped_param(item: str) -> dict:
        return {"item": item}

    current = _fixture_schema([("widget", widget_dropped_param)])
    violations = _tool_schema_violations(_WIDGET_BASELINE, current)
    assert len(violations) == 1
    assert "count" in violations[0] and "disappeared" in violations[0]


def _comorphism_fixture(quadruples):
    """A standalone ComorphismRegistry with one no-op edge per
    ``(name, source, target, lossy)`` quadruple -- real
    ``ComorphismRegistry.register``/``.edges()``, not a mock."""
    registry = ComorphismRegistry()
    for name, source, target, lossy in quadruples:
        registry.register(Comorphism(name=name, source=source, target=target,
                                     lossy=lossy, apply=lambda term: term))
    return sorted((e.name, e.source, e.target, e.lossy)
                  for e in registry.edges())


def test_comorphism_check_passes_when_a_new_edge_is_added():
    current = _comorphism_fixture(
        list(COMORPHISM_EDGE_BASELINE) + [("new_edge", "fol", "eso", False)])
    assert _comorphism_violations(COMORPHISM_EDGE_BASELINE, current) == []


def test_comorphism_check_fails_when_an_edge_is_removed():
    remaining = list(COMORPHISM_EDGE_BASELINE)[1:]
    current = _comorphism_fixture(remaining)
    violations = _comorphism_violations(COMORPHISM_EDGE_BASELINE, current)
    assert len(violations) == 1
    assert COMORPHISM_EDGE_BASELINE[0][0] in violations[0]


def test_comorphism_check_fails_when_an_edge_is_renamed():
    renamed = [("renamed_edge",) + t[1:] for t in COMORPHISM_EDGE_BASELINE[:1]] \
        + list(COMORPHISM_EDGE_BASELINE[1:])
    current = _comorphism_fixture(renamed)
    violations = _comorphism_violations(COMORPHISM_EDGE_BASELINE, current)
    assert len(violations) == 1
    assert COMORPHISM_EDGE_BASELINE[0][0] in violations[0]


def test_comorphism_check_fails_when_an_edges_target_changes():
    name, source, target, lossy = COMORPHISM_EDGE_BASELINE[0]
    changed = [(name, source, target + "_v2", lossy)] \
        + list(COMORPHISM_EDGE_BASELINE[1:])
    current = _comorphism_fixture(changed)
    violations = _comorphism_violations(COMORPHISM_EDGE_BASELINE, current)
    assert len(violations) == 1
    assert name in violations[0]


def test_comorphism_check_fails_when_an_edges_lossy_flag_changes():
    # Same name/source/target as the pinned edge, only ``lossy`` flipped --
    # a (name, source, target)-only check (the baseline's shape before this
    # test was added) would miss this entirely, since that triple still
    # matches. This is the case the STABILITY POLICY docstring in
    # comorphism.py explicitly promises ("... or has its
    # source/target/lossy changed"), so it must be caught here.
    name, source, target, lossy = COMORPHISM_EDGE_BASELINE[0]
    flipped = [(name, source, target, not lossy)] \
        + list(COMORPHISM_EDGE_BASELINE[1:])
    current = _comorphism_fixture(flipped)
    violations = _comorphism_violations(COMORPHISM_EDGE_BASELINE, current)
    assert len(violations) == 1
    assert name in violations[0] and "lossy" in violations[0]


def test_result_key_check_passes_when_a_key_is_added():
    baseline = {"translate": {"result", "path"}}
    current = {"translate": {"result", "path", "axioms"}}
    assert _result_key_violations(baseline, current) == []


def test_result_key_check_fails_when_a_key_disappears():
    baseline = {"translate": {"result", "path", "note"}}
    current = {"translate": {"result", "path"}}
    violations = _result_key_violations(baseline, current)
    assert len(violations) == 1
    assert "translate" in violations[0] and "note" in violations[0]


def test_result_key_check_fails_when_a_result_is_no_longer_produced():
    violations = _result_key_violations({"translate": {"result"}}, {})
    assert len(violations) == 1 and "translate" in violations[0]
