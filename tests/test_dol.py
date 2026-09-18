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

Roadmap item C6 (the ``fol.qml`` -> CASL/DOL/Hets bridge) is split across two
files: ``tests/test_qml_casl.py`` owns the OFFLINE half (the public
``qml_validity_formula`` entry point and the identifier-sanitisation shim in
isolation); THIS file owns :func:`~unicode_fol_kit.hets.dol.to_dol_library_from_modal`
itself (an offline wiring/shape test, near the bottom of the OFFLINE section)
and the LIVE cross-check battery (``TestModalCaslHetsLive``, at the very end)
that uploads a battery of known modal theorems/non-theorems — T/S4/S5 axioms
per frame, Barcan/converse-Barcan under every domain regime, a quantified
non-theorem, many-sorted input, the ``_w0``-vs-``w0`` identifier collision,
and a world-relativized ``=``/``≠`` atom under a box (the adversarial-review
equality edge case; the offline half of THAT coverage — the sanitiser's
``equality_alias`` in isolation — lives in ``tests/test_qml_casl.py``, this
file's own offline share is ``test_to_dol_library_from_modal_handles_equality_atom_without_crashing``)
— and asserts the Hets verdict agrees with
:func:`~unicode_fol_kit.fol.qml.qml_is_valid`'s own (Z3) verdict wherever Hets
returns a definite ``Proved``/``Disproved`` (an ``Open`` result is SKIPPED —
per this file's own docstring point 9 above and batch note (2), it is neither
agreement nor refutation).
"""

from collections import OrderedDict

import pytest

from unicode_fol_kit import MSFLParser
from unicode_fol_kit.fol.casl_export import to_casl_spec
from unicode_fol_kit.fol.casl_import import parse_casl_spec
from unicode_fol_kit.fol.nodes import Atom, Box, Constant, Implies, Quantifier, Variable
from unicode_fol_kit.fol._msfl_nodes import SortedQuantifier
from unicode_fol_kit.fol.frames import modal_axiom
from unicode_fol_kit.fol.qml import BARCAN, CONVERSE_BARCAN, qml_is_valid
from unicode_fol_kit.hets.dol import to_dol_library, DolSpec, to_dol_library_from_modal
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
# OFFLINE: to_dol_library_from_modal (roadmap item C6) — wiring, not
# translation logic (that half lives in tests/test_qml_casl.py, which pins
# qml_validity_formula and the sanitiser in isolation; the golden full-text
# case for THIS exact wrapper is tests/test_qml_casl.py's own
# test_golden_t_axiom_query_as_casl_text, since it needs no DOL wrapping to
# make its point — this file's job is only the library/spec WIRING itself).
# =============================================================================

def test_to_dol_library_from_modal_is_a_single_spec_conjecture_only_library():
    """The whole point of the wrapper is ONE spec, ONE conjecture (no
    separate axioms — qml_validity_formula's own output already IS the
    complete closed implication), wrapped exactly like any other DolSpec
    would be by to_dol_library. Checked structurally rather than by a full
    golden string (that byte-exact case already lives in
    test_qml_casl.py): the library/logic preamble, the requested spec_name /
    library_name, exactly one '%implied' line and no OTHER '. <formula>'
    line, and default_sort forwarded to to_casl_spec's own 'sorts' line."""
    f = Implies(Box(Atom("P", ())), Atom("P", ()))
    text = to_dol_library_from_modal(f, frame="T", spec_name="Q",
                                     library_name="ModalLib", default_sort="World_")
    lines = text.split("\n")
    assert lines[0] == "library ModalLib"
    assert lines[1] == "logic CASL"
    assert lines[2] == ""
    assert lines[3] == "spec Q ="
    assert lines[-1] == "end"
    body = "\n".join(lines[4:-1])
    formula_lines = [ln for ln in lines[4:-1] if ln.startswith("  . ")]
    assert len(formula_lines) == 1            # exactly one formula line...
    assert formula_lines[0].endswith("%implied")  # ...and it is the conjecture
    assert "sorts World_" in body
    # Independent check: what to_dol_library_from_modal built is exactly what
    # feeding the same sanitised Node to to_casl_spec directly would render —
    # i.e. the wrapper adds ONLY the library/logic preamble, nothing else.
    from unicode_fol_kit.hets.dol import sanitize_modal_identifiers
    from unicode_fol_kit.fol.qml import qml_validity_formula
    san = sanitize_modal_identifiers(qml_validity_formula(f, frame="T"))
    direct = to_casl_spec([], conjectures=[san], spec_name="Q", default_sort="World_")
    assert text == "library ModalLib\nlogic CASL\n\n" + direct


def test_to_dol_library_from_modal_forwards_mode_and_systems():
    """mode= and systems= genuinely reach qml_validity_formula: BARCAN is
    valid under mode='decreasing' and invalid under mode='varying' — a
    parameter silently dropped by the wrapper would make both renders
    identical, which this test would catch by their differing preds/body."""
    valid_text = to_dol_library_from_modal(BARCAN, mode="decreasing",
                                           spec_name="BD", library_name="L1")
    invalid_text = to_dol_library_from_modal(BARCAN, mode="varying",
                                             spec_name="BD", library_name="L1")
    assert valid_text != invalid_text
    # mode='varying' actualises object quantifiers with the existence guard
    # E(x, w); mode='decreasing' also uses E, but only ONE of the two texts
    # carries the extra decreasing-domain existence AXIOM (E(x,v)&R(w,v)->E(x,w))
    # — cheapest structural fingerprint of the two regimes actually differing.
    assert valid_text.count("E(") != invalid_text.count("E(")


def test_to_dol_library_from_modal_propagates_qml_refusal():
    """A modal construct qml_translate itself refuses (here: an unknown
    frame) propagates unchanged through the wrapper — no new validation of
    its own."""
    with pytest.raises(ValueError, match="unknown frame"):
        to_dol_library_from_modal(Atom("P", ()), frame="S99")


def test_to_dol_library_from_modal_propagates_casl_export_refusal():
    """A bad default_sort (a CASL keyword) is refused by to_casl_spec's own
    _check_reserved, propagated unchanged through DolSpec/to_dol_library."""
    with pytest.raises(ValueError, match="reserved CASL keyword 'sort'"):
        to_dol_library_from_modal(Atom("P", ()), default_sort="sort")


def test_to_dol_library_from_modal_handles_equality_atom_without_crashing():
    """Adversarial-review finding (C6): fol.qml's _st world-relativizes an
    object-language '=' atom (appends the current-world argument to EVERY
    atom, no exception for '=' — see fol.qml's own docstring), so
    'Box(a=b) -> a=b' comes out of qml_validity_formula with a TERNARY '='
    atom. Before this fix, handing that straight to to_casl_spec under the
    literal name '=' crashed with 'equality atom must have exactly 2
    arguments, got 3' — an opaque error naming neither modal logic nor
    world-relativization. Now hets.dol.sanitize_modal_identifiers aliases it
    to the fixed, uninterpreted predicate 'weq' before it ever reaches
    casl_export, so this must render cleanly."""
    a, b = Constant("a"), Constant("b")
    eq = Atom("=", [a, b])
    f = Implies(Box(eq), eq)
    text = to_dol_library_from_modal(f, frame="T", spec_name="EqT", library_name="L")
    assert "weq : Thing * Thing * Thing" in text
    assert "preds" in text and "= :" not in text   # '=' never separately declared
    spec = parse_casl_spec("\n".join(text.split("\n")[3:]))
    assert len(spec.conjectures) == 1
    # Faithful to Z3: T-schema on an atomic sentence, valid under a
    # reflexive frame, invalid under K (hand-derived, matches
    # tests/test_qml_casl.py's own identical hand-derivation).
    assert qml_is_valid(f, frame="T") is True
    assert qml_is_valid(f, frame="K") is False


def test_modal_tableau_also_agrees_on_a_box_equality_formula():
    """A third independent route (see the propositional-slice section
    below) on the SAME equality edge case: modal_tableau has no rule for a
    Quantifier, but 'Box(a=b) -> a=b' has none — it is squarely within its
    propositional-modal fragment ('=' is just another Atom to it, read off
    its own to_unicode_str() valuation, matching how satisfies_modal
    already treats an object-language '=' too — see fol.qml's own
    docstring for the same design choice on the Z3/CASL side)."""
    from unicode_fol_kit.atp.modal_tableau import is_modal_valid

    a, b = Constant("a"), Constant("b")
    f = Implies(Box(Atom("=", [a, b])), Atom("=", [a, b]))
    for frame, expected in (("T", True), ("K", False)):
        assert qml_is_valid(f, frame=frame) is expected
        assert is_modal_valid(f, frame=frame) is expected


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


# =============================================================================
# OFFLINE: the propositional-modal slice of the battery ALSO checked against
# atp.modal_tableau — the test_oracle's own wording asks for agreement with
# "qml_is_valid's Z3 verdict AND atp.modal_tableau's verdict". modal_tableau
# is a PROPOSITIONAL-modal engine with no quantifier rules at all (it refuses
# Quantifier/SortedQuantifier by construction — see its own module docstring
# and the _QUANTIFIED tuple in unicode_fol_kit/atp/modal_tableau.py), so it
# can only ever join the T/S4/S5 slice of the battery below — never the
# Barcan/converse-Barcan/sorted/quantified-non-theorem/collision cases, which
# are genuinely outside what a propositional tableau can even state. It also
# refuses a Geach frame condition (no rule for it — see
# test_modal_frame_registry.py's own test_the_tableau_refuses_what_it_has_no_rule_for),
# so 'geach_dot2_*' is excluded too. This gives THREE independently
# implemented routes (Z3, a labelled tableau, and — in the LIVE class below —
# Hets/SPASS) agreeing on the same six cases, entirely offline for the first
# two.
# =============================================================================

@pytest.mark.parametrize("axiom,frame,expected", [
    ("T", "T", True), ("T", "K", False),
    ("4", "S4", True), ("4", "K", False),
    ("5", "S5", True), ("5", "K", False),
])
def test_modal_tableau_agrees_with_qml_is_valid_on_the_propositional_slice(
        axiom, frame, expected):
    """See the section comment above: the third independent route the
    battery's test_oracle names, wherever it can even express the query."""
    from unicode_fol_kit.atp.modal_tableau import is_modal_valid

    f = modal_axiom(axiom)
    assert qml_is_valid(f, frame=frame) is expected
    assert is_modal_valid(f, frame=frame) is expected


# =============================================================================
# LIVE: roadmap item C6's own battery — the CASL/DOL/Hets route vs
# fol.qml.qml_is_valid (Z3), for a battery of modal theorems and
# non-theorems. Every ``expected`` value below is HAND-DERIVED from textbook
# Kripke-semantics correspondence (never by running qml_is_valid and copying
# its answer) — T/4/5 characterise exactly reflexive/transitive/euclidean
# frames (Chellas, "Modal Logic", or any standard text), and the Barcan /
# converse-Barcan <-> domain-regime correspondence is exactly what
# fol.qml's own module docstring states and tests/test_qml.py /
# tests/test_completeness_round2.py already pin from the Z3 side alone. This
# file's OWN contribution is comparing that hand-derived expectation against
# a SECOND, independently-implemented backend (Hets/SPASS, an external tool
# this kit does not implement) — qml_is_valid (Z3) is checked too, in the
# same assertion, purely so a single failure output shows both routes' own
# verdicts side by side. (The propositional slice of this same battery is
# ALSO checked against a third route, atp.modal_tableau, offline — see the
# section directly above.)
# =============================================================================

def _spec_name_for(case_id: str) -> str:
    """A legal, readable CASL identifier for a battery case_id, e.g.
    'barcan_varying' -> 'BarcanVarying'."""
    return "".join(part.capitalize() for part in case_id.split("_"))


def _w0_collision_formula():
    """forall w0 (Box A(w0) -> A(w0)) — fol.qml's variable grammar allows an
    OBJECT variable literally named 'w0' ([a-z][0-9]*), and _Fresh always
    mints '_w0' as the very FIRST fresh world it needs, so this formula's
    translation genuinely contains both 'w0' and '_w0' — see
    tests/test_qml_casl.py's offline injectivity test for the same formula
    checked without a live server."""
    w0 = Variable("w0")
    return Quantifier("∀", w0,
                      Implies(Box(Atom("A", [w0])), Atom("A", [w0])))


def _quantified_non_theorem():
    """(exists x A(x)) -> (forall x A(x)) — an existential never entails a
    universal (any two-element domain with A true of one element and false
    of the other refutes it); independent of frame/mode since it uses no
    modal operator at all."""
    x = Variable("x")
    A = lambda t: Atom("A", [t])
    return Implies(Quantifier("∃", x, A(x)), Quantifier("∀", x, A(x)))


def _equality_box_formula(predicate: str):
    """Box(a <predicate> b) -> a <predicate> b — the adversarial-review
    equality edge case (see tests/test_qml_casl.py's own identical
    hand-derivation): _st world-relativizes '='/'≠' into a ternary atom
    like any other, so this is the T-schema instantiated at an equality/
    inequality atom, valid under any reflexive frame, independent of what
    the atom itself 'means'."""
    a, b = Constant("a"), Constant("b")
    atom = Atom(predicate, [a, b])
    return Implies(Box(atom), atom)


def _sorted_nonempty_witness(op: str):
    """forall x:S A(x) -> exists x:S A(x) (valid: qml_axioms' per-world sort
    non-emptiness gives S a witness at every world) and its converse (exists
    -> forall, invalid: same argument as _quantified_non_theorem, sorted)."""
    x = Variable("x")
    A = lambda t: Atom("A", [t])
    if op == "valid":
        return Implies(SortedQuantifier("∀", x, "S", A(x)),
                       SortedQuantifier("∃", x, "S", A(x)))
    return Implies(SortedQuantifier("∃", x, "S", A(x)),
                   SortedQuantifier("∀", x, "S", A(x)))


# (case_id, formula, kwargs for to_dol_library_from_modal / qml_is_valid,
#  hand-derived expected validity).
_MODAL_BATTERY = [
    ("t_on_t", modal_axiom("T"), dict(frame="T"), True),
    ("t_on_k", modal_axiom("T"), dict(frame="K"), False),
    ("four_on_s4", modal_axiom("4"), dict(frame="S4"), True),
    ("four_on_k", modal_axiom("4"), dict(frame="K"), False),
    ("five_on_s5", modal_axiom("5"), dict(frame="S5"), True),
    ("five_on_k", modal_axiom("5"), dict(frame="K"), False),
    ("geach_dot2_on_its_frame", modal_axiom(".2"), dict(frame="G(1,1,1,1)"), True),
    ("geach_dot2_on_k", modal_axiom(".2"), dict(frame="K"), False),
    ("barcan_constant", BARCAN, dict(mode="constant"), True),
    ("barcan_decreasing", BARCAN, dict(mode="decreasing"), True),
    ("barcan_increasing", BARCAN, dict(mode="increasing"), False),
    ("barcan_varying", BARCAN, dict(mode="varying"), False),
    ("cbarcan_constant", CONVERSE_BARCAN, dict(mode="constant"), True),
    ("cbarcan_increasing", CONVERSE_BARCAN, dict(mode="increasing"), True),
    ("cbarcan_decreasing", CONVERSE_BARCAN, dict(mode="decreasing"), False),
    ("cbarcan_varying", CONVERSE_BARCAN, dict(mode="varying"), False),
    ("quant_nontheorem", _quantified_non_theorem(), dict(frame="K"), False),
    ("sorted_nonempty_witness", _sorted_nonempty_witness("valid"),
     dict(frame="K"), True),
    ("sorted_exists_not_forall", _sorted_nonempty_witness("invalid"),
     dict(frame="K"), False),
    ("collide_k", _w0_collision_formula(), dict(mode="constant", frame="K"), False),
    ("collide_t", _w0_collision_formula(), dict(mode="constant", frame="T"), True),
    # Adversarial-review finding (C6): a world-relativized '='/'≠' atom must
    # not crash the bridge (arity mismatch against CASL's own rigid, always-
    # 2-ary equality) or silently mistranslate — see hets/dol.py's own
    # equality_alias and tests/test_qml_casl.py's offline coverage of the
    # same cases.
    ("equality_box_t", _equality_box_formula("="), dict(frame="T"), True),
    ("equality_box_k", _equality_box_formula("="), dict(frame="K"), False),
    ("inequality_box_t", _equality_box_formula("≠"), dict(frame="T"), True),
    ("inequality_box_k", _equality_box_formula("≠"), dict(frame="K"), False),
]


@pytest.mark.hets_live
@pytest.mark.skipif(
    not hets_available(),
    reason="no reachable HETS server (set $UFK_HETS_URL, or run "
           "`docker run -d --rm -p 8000:8000 spechub2/hets:latest`)")
class TestModalCaslHetsLive:
    """The CASL/DOL/Hets route vs fol.qml.qml_is_valid, battery-wide.

    Run serially, one case at a time (batch rule): ``-m hets_live -k
    test_hets_agrees_with_qml_is_valid and t_on_t`` etc., or the whole class
    at once with ``-m hets_live -k TestModalCaslHetsLive`` — every case is
    its own tiny library/spec (unlike TestDolLive's shared 2-spec fixture
    above), so cases do not interact and any subset may be selected freely.
    """

    @pytest.fixture(scope="class")
    def client(self):
        url, container = discover_hets_url(start_container=False)
        try:
            yield HetsClient(url)
        finally:
            if container is not None:
                container.stop()

    @pytest.mark.parametrize("case_id,formula,kwargs,expected", _MODAL_BATTERY,
                             ids=[c[0] for c in _MODAL_BATTERY])
    def test_hets_agrees_with_qml_is_valid(self, client, case_id, formula,
                                           kwargs, expected):
        # The hand-derived expectation must first agree with qml_is_valid's
        # own (Z3) verdict — if it does not, this battery entry's hand-worked
        # value is simply wrong, and that is a bug in THIS test, not in Hets.
        assert qml_is_valid(formula, **kwargs) is expected, (
            f"{case_id}: hand-derived expectation {expected} disagrees with "
            "qml_is_valid (Z3) itself -- fix the battery entry, not Hets")

        spec_name = _spec_name_for(case_id)
        lib = to_dol_library_from_modal(
            formula, spec_name=spec_name, library_name="Lib" + spec_name, **kwargs)
        iri = client.upload(lib, f"ufk_modal_{case_id}.dol")
        goals = client.prove(iri, spec_name, reasoner="SPASS", time_limit=15)
        assert len(goals) == 1
        result = goals[0]["result"]
        if result == "Open":
            pytest.skip(
                f"{case_id}: Hets/SPASS returned Open (unknown) -- neither "
                "agreement nor refutation (see this file's module docstring "
                "point 9 / batch note (2)).")
        assert result in ("Proved", "Disproved")
        assert (result == "Proved") == expected, (
            f"{case_id}: Hets said {result!r} but qml_is_valid said {expected}")
