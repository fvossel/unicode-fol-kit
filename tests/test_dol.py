r"""Tests for :mod:`unicode_fol_kit.hets.dol` (DOL library emission over
:mod:`unicode_fol_kit.fol.casl_export`).

Two tiers, mirroring ``tests/test_hets_client.py``'s split:

OFFLINE (default run, no server needed) — the golden library text (hand-
derived against ``to_casl_spec``'s own documented, already-tested emission
rules, never by running the code and copying its output), the ``extends``
header shape, export/import consistency against
:func:`unicode_fol_kit.fol.casl_import.parse_casl_spec` per spec block, name
refusals, and refusals propagated unchanged from ``to_casl_spec``.

LIVE (``@pytest.mark.hets_live`` on ``TestDolLive``, gated by
:func:`~unicode_fol_kit.hets.docker.hets_available` exactly like
``TestHetsLive`` in ``test_hets_client.py``) — uploads a real 2-spec
library (``B`` extends ``A``, ``B``'s ``%implied`` goal follows from
``A + B``) to a real Hets server, checks ``/dg?format=json`` names BOTH
development-graph nodes, and proves ``B``'s goal with SPASS. Run explicitly
and SERIALLY::

    pytest -m hets_live tests/test_dol.py

Every test in ``TestDolLive`` is also individually gated by the module-level
``skipif`` below, so a machine with no reachable Hets server just skips them
— never a silent pass, always a visible "skipped: <reason>" naming what was
missing (this kit's "loud failures, never a silent skip" convention).

Wire facts this file relies on for the live tier (verified live against
``spechub2/hets:latest``, see ``unicode_fol_kit/hets/client.py``'s own
module docstring for the full account):
  * the stored-path IRI returned by ``upload`` must be percent-encoded
    (including ``/``) for every later endpoint — handled internally by
    :class:`~unicode_fol_kit.hets.client.HetsClient`, never done by hand
    here;
  * ``/dg/<iri>?format=json`` lists every development-graph node under
    ``DGraph.DGNode``, each with its own ``name`` — one node per ``spec`` in
    the uploaded library, so a 2-spec library must show exactly ``{"A",
    "B"}``;
  * SPASS (via Hets's default ``CASL2TPTP_FOF`` translation) is the reliably
    working reasoner in the shipped image — eprover/Vampire are broken there
    (always ``Open``, see ``unicode_fol_kit/hets/docker.py``'s docstring),
    so the live proof check uses SPASS, never those two;
  * a node with zero ``%implied`` goals answers the plain-text "nothing to
    prove" rather than JSON — irrelevant to this file's own live test (node
    ``B`` always has exactly one goal), but noted here since a caller
    reusing this pattern for an axiom-only node must expect it.
"""

from collections import OrderedDict

import pytest

from unicode_fol_kit import MSFLParser
from unicode_fol_kit.fol.casl_export import to_casl_spec
from unicode_fol_kit.fol.casl_import import parse_casl_spec
from unicode_fol_kit.fol.nodes import Atom, Box
from unicode_fol_kit.hets.dol import to_dol_library, DolSpec
from unicode_fol_kit.hets.docker import discover_hets_url, hets_available
from unicode_fol_kit.hets.client import HetsClient

FOL = MSFLParser()

# The entailment this file's golden test AND live test both use: universal
# instantiation + modus ponens. P(elem) and forall x (P(x) -> Q(x)) together
# entail Q(elem); 'elem' (not 'c') because the kit's own grammar requires a
# bare constant NAME to have at least two letters (see
# tests/test_casl_export.py's grammar-facts note) — a single letter would
# parse as a VARIABLE instead.
_AX1 = FOL.parse("∀x (P(x) → Q(x))")
_AX2 = FOL.parse("P(elem)")
_GOAL = FOL.parse("Q(elem)")


def _entailment_library(lib_name: str = "EntailLib") -> "OrderedDict[str, DolSpec]":
    specs: "OrderedDict[str, DolSpec]" = OrderedDict()
    specs["A"] = DolSpec(axioms=[_AX1, _AX2])
    specs["B"] = DolSpec(axioms=[], conjectures=[_GOAL], extends="A")
    return specs


# =============================================================================
# OFFLINE: golden text
# =============================================================================

def test_golden_two_spec_library_with_extends():
    """Hand-derivation, spec by spec:

    Header: 'library EntailLib' then 'logic CASL' then a blank line (this
    module's own fixed preamble, independent of the specs).

    Spec A (DolSpec(axioms=[ax1, ax2]), no extends, default_sort='Thing'):
    calling to_casl_spec([ax1, ax2], spec_name='A') on its own would produce
    (by the SAME reasoning as test_golden_pure_fol_one_sort in
    test_casl_export.py, just with predicate names P/Q and constant 'elem'
    instead of Human/Mortal/socrates — identical mechanics): a 'sorts
    Thing' line (the one plain forall contributes default_sort); 'ops elem
    : Thing' (elem's slot unions with P's arg-0 slot via 'P(elem)', which
    is itself unioned with x's 'Thing' slot via the SAME argument position
    in the quantified axiom); 'preds P : Thing; Q : Thing' (alphabetical,
    both arg-0 slots equal x's 'Thing' slot via the quantified axiom); then
    the two axiom lines. Slicing off 'spec A =' / 'end' and re-wrapping
    under the SAME plain header (no extends) reproduces that block
    byte-for-byte.

    Spec B (DolSpec(axioms=[], conjectures=[goal], extends='A')): its OWN
    to_casl_spec([], conjectures=[goal], spec_name='B') call (only 'goal' =
    Q(elem) exists in this call — A's axioms are NOT passed here) infers,
    independently: 'sorts Thing' (elem's slot has no direct annotation, so
    it resolves to default_sort); 'ops elem : Thing'; 'preds Q : Thing'
    (arity 1, arg 0 resolves to default_sort since nothing pins it down
    within B's own formula alone); one conjecture line 'Q(elem) %implied'.
    Re-wrapped under 'spec B = A then' instead of the plain header (the
    'extends' rendering rule) — note B's ops/preds INTENTIONALLY re-declare
    'elem'/'Q', which A already declares identically (harmless under CASL's
    'then' — see the module's own docstring).

    Blank line between A's 'end' and B's 'spec' header (this module always
    separates consecutive spec blocks); no blank line / trailing newline
    after B's own final 'end' (matches to_casl_spec's own no-trailing-
    newline convention).
    """
    text = to_dol_library("EntailLib", _entailment_library())
    expected = (
        "library EntailLib\n"
        "logic CASL\n"
        "\n"
        "spec A =\n"
        "  sorts Thing\n"
        "  ops elem : Thing\n"
        "  preds P : Thing;\n"
        "        Q : Thing\n"
        "  . forall x : Thing . (P(x) => Q(x))\n"
        "  . P(elem)\n"
        "end\n"
        "\n"
        "spec B = A then\n"
        "  sorts Thing\n"
        "  ops elem : Thing\n"
        "  preds Q : Thing\n"
        "  . Q(elem) %implied\n"
        "end"
    )
    assert text == expected


def test_golden_single_spec_no_extends():
    """A single-spec library (no 'then' anywhere): 'library X' / 'logic
    CASL' / one blank line / the plain spec block / no trailing blank line
    or newline. The spec block itself is byte-identical to what
    to_casl_spec(spec_name='Only') would produce directly (this module adds
    nothing to a single, non-extending spec's own text beyond the
    library/logic preamble)."""
    specs = OrderedDict()
    specs["Only"] = DolSpec(axioms=[_AX2])
    text = to_dol_library("SingleLib", specs)
    direct_spec_text = to_casl_spec([_AX2], spec_name="Only")
    expected = "library SingleLib\nlogic CASL\n\n" + direct_spec_text
    assert text == expected
    assert "then" not in text


def test_extends_header_shape_is_exactly_spec_equals_extends_then():
    """The 'extends' rendering rule, isolated: the header line must be
    EXACTLY 'spec <name> = <extends> then', not e.g. 'spec <name> =' on one
    line and 'A then' on the next."""
    specs = OrderedDict()
    specs["A"] = DolSpec(axioms=[_AX2])
    specs["B"] = DolSpec(axioms=[], conjectures=[_GOAL], extends="A")
    text = to_dol_library("L", specs)
    lines = text.split("\n")
    assert "spec B = A then" in lines


# =============================================================================
# OFFLINE: export/import consistency (each spec block through parse_casl_spec)
# =============================================================================

def test_non_extending_spec_block_round_trips_through_casl_import():
    """Spec A's own block (no 'then') is exactly one 'spec ... end' unit —
    parse_casl_spec must accept it and recover A's own axioms exactly.

    Each spec block is separated from its neighbours (and from the
    'library'/'logic CASL' preamble) by exactly one blank line (this
    module's own fixed formatting — see the golden test above), so
    splitting the whole library text on a double newline cleanly yields
    ['library ...\\nlogic CASL', "<A's block>", "<B's block>"] without
    depending on any particular line COUNT (which would make this test
    fragile against unrelated formatting changes)."""
    text = to_dol_library("Lib", _entailment_library())
    preamble, a_block, b_block = text.split("\n\n")
    assert a_block.startswith("spec A =\n") and a_block.endswith("\nend")
    spec = parse_casl_spec(a_block)
    assert spec.name == "A"
    assert spec.axioms == (_AX1, _AX2)


def test_extending_spec_bodys_own_formulas_round_trip_through_casl_import():
    """casl_import.parse_casl_spec explicitly refuses 'then' structuring
    (see its own module docstring's 'Scope' section) — consistent with this
    module's own 'no parse_dol_library' scope decision, both modules agree
    that ONE flat spec is the importable unit. So spec B's block as emitted
    (with its 'A then' header) is NOT directly parseable — asserted below,
    to document the boundary rather than leave it implicit. What IS checked
    first: B's own BODY (its formulas, independent of the extends wrapper)
    round-trips correctly — built by rendering the SAME DolSpec content
    with extends=None (a plain header), which is byte-identical to B's
    actual block except for the header line, and IS directly parseable."""
    plain_b = OrderedDict()
    plain_b["B"] = DolSpec(axioms=[], conjectures=[_GOAL], extends=None)
    _, plain_b_block = to_dol_library("Lib", plain_b).split("\n\n")
    assert plain_b_block.startswith("spec B =\n")
    spec = parse_casl_spec(plain_b_block)
    assert spec.conjectures == (_GOAL,)

    text = to_dol_library("Lib", _entailment_library())
    _, _, b_actual_block = text.split("\n\n")
    assert b_actual_block.startswith("spec B = A then\n")
    with pytest.raises(Exception):
        parse_casl_spec(b_actual_block)


# =============================================================================
# OFFLINE: DolSpec defaults
# =============================================================================

def test_dolspec_defaults():
    spec = DolSpec(axioms=[_AX2])
    assert spec.conjectures == ()
    assert spec.extends is None
    assert spec.default_sort == "Thing"


# =============================================================================
# OFFLINE: refusals
# =============================================================================

def test_refuses_empty_specs_mapping():
    with pytest.raises(ValueError, match="at least one spec"):
        to_dol_library("Lib", OrderedDict())


def test_refuses_library_name_with_bad_characters():
    specs = OrderedDict({"A": DolSpec(axioms=[_AX2])})
    with pytest.raises(ValueError, match="not a simple CASL identifier"):
        to_dol_library("2Bad", specs)


def test_refuses_library_name_that_is_a_casl_keyword():
    specs = OrderedDict({"A": DolSpec(axioms=[_AX2])})
    with pytest.raises(ValueError, match="reserved CASL keyword 'spec'"):
        to_dol_library("spec", specs)


def test_refuses_extends_name_with_bad_characters():
    specs = OrderedDict()
    specs["A"] = DolSpec(axioms=[_AX2])
    specs["B"] = DolSpec(axioms=[], conjectures=[_GOAL], extends="2Bad")
    with pytest.raises(ValueError, match="not a simple CASL identifier"):
        to_dol_library("Lib", specs)


def test_refuses_extends_name_that_is_a_casl_keyword():
    specs = OrderedDict()
    specs["A"] = DolSpec(axioms=[_AX2])
    specs["B"] = DolSpec(axioms=[], conjectures=[_GOAL], extends="then")
    with pytest.raises(ValueError, match="reserved CASL keyword 'then'"):
        to_dol_library("Lib", specs)


def test_refuses_bad_spec_name_via_to_casl_spec_passthrough():
    """A spec's own dict KEY becomes to_casl_spec's spec_name and is
    validated there, not duplicated in this module — see the module
    docstring's 'Name validation' section."""
    specs = OrderedDict({"2Bad": DolSpec(axioms=[_AX2])})
    with pytest.raises(ValueError, match="not a simple CASL identifier"):
        to_dol_library("Lib", specs)


def test_propagates_notimplementederror_for_out_of_fragment_node():
    """A Box (modal) node is outside to_casl_spec's classical fragment;
    to_dol_library adds no formula-level checking of its own, so this
    propagates unchanged (see the module docstring's 'What is NOT
    re-checked here' section)."""
    specs = OrderedDict({"A": DolSpec(axioms=[Box(Atom("P", ()))])})
    with pytest.raises(NotImplementedError, match="Box"):
        to_dol_library("Lib", specs)


def test_propagates_valueerror_for_empty_axioms_and_conjectures():
    """A DolSpec with neither axioms nor conjectures makes its own
    to_casl_spec call fail its 'needs at least one formula' check —
    propagated unchanged."""
    specs = OrderedDict({"A": DolSpec(axioms=[], conjectures=[])})
    with pytest.raises(ValueError, match="at least one axiom or conjecture"):
        to_dol_library("Lib", specs)


# =============================================================================
# LIVE: real HTTP calls against a real Hets server
# =============================================================================

@pytest.mark.hets_live
@pytest.mark.skipif(
    not hets_available(),
    reason="no reachable HETS server (set $UFK_HETS_URL, or run "
           "`docker run -d --rm -p 8000:8000 spechub2/hets:latest`)")
class TestDolLive:
    """Real calls against a real Hets server. Run serially: -m hets_live (no -n)."""

    @pytest.fixture(scope="class")
    def uploaded(self):
        url, container = discover_hets_url(start_container=False)
        client = HetsClient(url)
        text = to_dol_library("EntailLib", _entailment_library())
        iri = client.upload(text, "ufk_entail_lib.dol")
        try:
            yield {"client": client, "iri": iri}
        finally:
            if container is not None:
                container.stop()

    def test_dg_lists_both_named_nodes(self, uploaded):
        dgraph = uploaded["client"].dg(uploaded["iri"])["DGraph"]
        node_names = {n["name"] for n in dgraph["DGNode"]}
        assert {"A", "B"} <= node_names

    def test_prove_bs_goal_with_spass_proves_it(self, uploaded):
        goals = uploaded["client"].prove(uploaded["iri"], "B", reasoner="SPASS")
        assert len(goals) == 1
        assert goals[0]["result"] == "Proved"
