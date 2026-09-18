r"""Tests for the fol.qml -> fol.casl_export / hets.dol bridge (roadmap item C6).

This file owns the OFFLINE half of the bridge: :func:`~unicode_fol_kit.fol.qml.qml_validity_formula`
(the public, documented entry point onto the SAME Node
:func:`~unicode_fol_kit.fol.qml.qml_is_valid` already feeds to Z3), and
:mod:`unicode_fol_kit.hets.dol`'s identifier-sanitisation shim
(:func:`~unicode_fol_kit.hets.dol.sanitize_modal_identifiers`,
:class:`~unicode_fol_kit.hets.dol._CaslIdentifierShim`) that fixes the ONE concrete
gap the roadmap review measured: ``fol.qml``'s own auto-generated fresh variables
(``_w0``, the Geach axiom's ``_gz0``/``_gw``/``_gu``/``_gv``/``_gt``, …) are not
legal CASL identifiers ([A-Za-z][A-Za-z0-9_]*).

``tests/test_dol.py`` owns the other half: :func:`~unicode_fol_kit.hets.dol.to_dol_library_from_modal`
(the thin wrapper that composes ``qml_validity_formula`` + the sanitiser + the
EXISTING, unmodified :func:`~unicode_fol_kit.fol.casl_export.to_casl_spec` /
:func:`~unicode_fol_kit.hets.dol.to_dol_library`) and the live Hets battery that
cross-checks the CASL/DOL route's verdict against
:func:`~unicode_fol_kit.fol.qml.qml_is_valid`'s own (Z3) verdict for a battery of
modal theorems and non-theorems.

No changes to ``fol.qml``'s or ``fol.casl_export``'s own translation/rendering
LOGIC anywhere in this file's target code — :func:`qml_validity_formula` is a
literal delegation to the already-tested, unchanged private ``_validity_formula``
(``tests/test_qml.py`` / ``tests/test_qml_bridges.py`` / ``tests/test_lj_search.py``
already pin its axiom-construction behaviour byte-exact; this file does not
re-derive that), and the sanitiser only ever renames identifiers, never
restructures a formula.
"""

import re

import pytest

from unicode_fol_kit.fol.nodes import (
    Atom, Box, Constant, Implies, Knows, Not, Quantifier, Until, Variable,
)
from unicode_fol_kit.fol._msfl_nodes import SortedQuantifier
from unicode_fol_kit.fol.frames import modal_axiom
from unicode_fol_kit.fol.qml import (
    BARCAN, CONVERSE_BARCAN, _validity_formula, qml_is_valid, qml_validity_formula,
)
from unicode_fol_kit.fol.casl_export import to_casl_spec
from unicode_fol_kit.fol.casl_import import parse_casl_spec
from unicode_fol_kit.hets.dol import (
    _CaslIdentifierShim, _casl_sanitize_stem, sanitize_modal_identifiers,
)

# Mirrors casl_export._SIMPLE_ID_RE / dol._SIMPLE_ID_RE: a legal CASL SIMPLE-ID.
_SIMPLE_ID_RE = re.compile(r"[A-Za-z][A-Za-z0-9_]*")


def _var_names(node):
    return {n.name for n in node.walk() if type(n).__name__ == "Variable"}


def _all_identifiers(node):
    """Every Variable/Constant/Function-name/Atom-predicate text ``node`` uses
    (equality '=' excluded — it is never a declared symbol)."""
    names = set()
    for n in node.walk():
        cls = type(n).__name__
        if cls in ("Variable", "Constant", "SortedConstant", "Function"):
            names.add(n.name)
        elif cls == "Atom" and n.predicate != "=":
            names.add(n.predicate)
    return names


# =============================================================================
# qml_validity_formula: public delegation to the unchanged _validity_formula
# =============================================================================

def test_qml_validity_formula_delegates_to_private_validity_formula_unchanged():
    """The new public function must return EXACTLY what the private,
    already-tested ``_validity_formula`` builds — batch note (4) requires every
    existing call to ``_validity_formula`` (positional, 3-arg, from
    ``atp.resolution`` and several test files) to stay byte-identical, so this
    is a pure additive wrapper, never a rename or a signature change."""
    P = Atom("P", ())
    f = Implies(_validity_formula(Not(Not(P)), "constant", "K"),
               _validity_formula(Not(Not(P)), "constant", "K"))
    assert f.left == f.right  # sanity: _validity_formula is itself deterministic

    for kwargs in (
        dict(mode="constant", frame="K"),
        dict(mode="decreasing", frame="S5"),
        dict(mode="varying", frame="T", systems={"epistemic": "S5"}),
        dict(mode="constant", frame="K", temporal_closure=False),
    ):
        formula = Knows(Constant("alice"), P)
        assert qml_validity_formula(formula, **kwargs) == _validity_formula(
            formula, kwargs.get("mode", "constant"), kwargs.get("frame", "K"),
            kwargs.get("systems"), bridges=kwargs.get("bridges"),
            temporal_closure=kwargs.get("temporal_closure", True))


def test_qml_validity_formula_output_is_pure_classical_fragment():
    """The Node qml_validity_formula returns must already sit inside
    casl_export's classical fragment (only Atom/Not/And/Or/Xor/Implies/Iff/
    Quantifier and the term classes Variable/Constant/Function) — no
    SortedQuantifier/SortedConstant survives (qml_translate relativises them
    away up front) and obviously no Box/Diamond/Knows/... survives (that is
    the whole point of the standard translation). Exercises several modal
    families plus systems= and bridges= at once, since those are exactly the
    places a NEW node type could leak through unnoticed."""
    from unicode_fol_kit.fol.nodes import Box, Obligatory, Always, Believes
    a = Constant("alice")
    P, Q = Atom("P", ()), Atom("Q", ())
    x = Variable("x")
    # Exercises Box/Knows/Obligatory/Always and a SortedQuantifier all at once.
    formula1 = Implies(
        Knows(a, Box(P)),
        Implies(Obligatory(Q), Always(SortedQuantifier("∀", x, "S", Atom("R", [x])))))
    node1 = qml_validity_formula(formula1, systems={"epistemic": "S5"})
    # A second formula that satisfies knowledge_implies_belief's own
    # precondition (both Knows AND Believes must occur) to exercise bridges=.
    formula2 = Implies(Knows(a, P), Believes(a, P))
    node2 = qml_validity_formula(formula2, systems={"epistemic": "S5"},
                                 bridges=["knowledge_implies_belief"])
    allowed = {"Atom", "Not", "And", "Or", "Xor", "Implies", "Iff", "Quantifier",
              "Variable", "Constant", "Function"}
    for n in list(node1.walk()) + list(node2.walk()):
        assert type(n).__name__ in allowed, type(n).__name__


# =============================================================================
# The identifier-sanitisation shim: stems, injectivity, legality
# =============================================================================

def test_casl_sanitize_stem_strips_qmls_own_leading_underscore_convention():
    """Hand-worked: every shape fol.qml's own _Fresh / Geach helper /
    _signature_typing_facts actually mint. Stripping the leading underscore(s)
    alone already makes each one a legal, human-readable CASL identifier."""
    assert _casl_sanitize_stem("_w0") == "w0"
    assert _casl_sanitize_stem("_w12") == "w12"
    assert _casl_sanitize_stem("_gz0") == "gz0"
    assert _casl_sanitize_stem("_gw") == "gw"
    assert _casl_sanitize_stem("_a0") == "a0"
    assert _casl_sanitize_stem("_world0") == "world0"


def test_casl_sanitize_stem_defensive_edge_cases():
    """Names fol.qml itself never generates, but the stem function must still
    turn into SOMETHING matching [A-Za-z][A-Za-z0-9_]* (hand-derived, not
    copied from running the code): an all-underscore name has nothing left
    after stripping, so it falls back to 'id'; a digit-leading remainder (a
    hypothetical '_3x') is not a letter, so it is 'v'-prefixed; an already
    letter-first name with no underscore passes through unchanged (dead code
    for THIS function's only real caller, which pre-filters on "not already
    legal" — see _CaslIdentifierShim._resolve — but the stem function itself
    must still behave correctly in isolation)."""
    assert _casl_sanitize_stem("___") == "id"
    assert _casl_sanitize_stem("_3x") == "v3x"
    assert _casl_sanitize_stem("already_legal") == "already_legal"
    for candidate in (_casl_sanitize_stem("___"), _casl_sanitize_stem("_3x"),
                     _casl_sanitize_stem("_w0")):
        assert _SIMPLE_ID_RE.fullmatch(candidate)


def test_sanitize_modal_identifiers_leaves_already_legal_names_untouched():
    """qml_validity_formula(T axiom, frame='K') mints exactly ONE fresh
    variable (the box's '_w0' — 'K' has no reflexivity axiom to add a second
    quantifier). Every OTHER identifier (P, World, Object, R, E, and the
    hand-picked object/world variables t, w, v, x qml_axioms/_st themselves
    use) is already legal and must come out of sanitize_modal_identifiers
    byte-for-byte unchanged — only '_w0' is renamed, to 'w0'."""
    from unicode_fol_kit.fol.nodes import Box
    P = Atom("P", ())
    node = qml_validity_formula(Implies(Box(P), P), frame="K")
    before = _var_names(node)
    assert "_w0" in before
    san = sanitize_modal_identifiers(node)
    after = _var_names(san)
    assert after == {"t", "w", "v", "x", "w0"}
    assert _all_identifiers(node) - {"_w0"} == _all_identifiers(san) - {"w0"}


def test_sanitizer_is_injective_on_a_real_w0_underscore_w0_collision():
    """The load-bearing collision batch note (3) names explicitly: fol.qml's
    own variable grammar allows an OBJECT variable literally named 'w0'
    ([a-z][0-9]*), and _Fresh's counter ALWAYS tries '_w0' first for the very
    first fresh world it mints — so 'forall w0 (Box A(w0) -> A(w0))' is a
    REAL, not contrived, formula whose translation contains both 'w0' (the
    user's own variable) and the fresh '_w0' the Box mints. Two distinct
    source names must map to two distinct output names."""
    from unicode_fol_kit.fol.nodes import Box
    w0 = Variable("w0")
    f = Quantifier("∀", w0, Implies(Box(Atom("A", [w0])), Atom("A", [w0])))
    node = qml_validity_formula(f, mode="constant", frame="K")
    before = _var_names(node)
    assert {"_w0", "w0"} <= before  # the collision is genuinely present

    san = sanitize_modal_identifiers(node)
    after = _var_names(san)
    assert len(after) == len(before), "two distinct names collapsed onto one"
    assert "w0" in after                    # the already-legal name is untouched
    assert all(_SIMPLE_ID_RE.fullmatch(n) for n in after)

    # And the renaming preserves MEANING, not just syntax: qml_is_valid (Z3,
    # never touched by this shim) disagrees between frame K and frame T for
    # this exact formula, so a corrupting rename that merged the two 'w'
    # variables would be a semantic bug this comparison would expose — see
    # tests/test_dol.py's live TestModalCaslHetsLive for the SAME two cases
    # ('collide_k' / 'collide_t') cross-checked against a real Hets server.
    assert qml_is_valid(f, mode="constant", frame="K") is False
    assert qml_is_valid(f, mode="constant", frame="T") is True


def test_sanitizer_injective_regardless_of_which_name_the_walk_meets_first():
    """Same collision, built directly (not through qml) so the object
    variable 'w0' is visited BEFORE '_w0' in Node.walk()'s pre-order — the
    two-pass design (seed every already-legal name first, in a WHOLE-tree
    pass, before resolving any illegal one) must make injectivity independent
    of which one the walk happens to meet first; a naive single-pass,
    seed-as-you-go renamer would only get this right by accident of order."""
    from unicode_fol_kit.fol.nodes import And
    f = And(Atom("A", [Variable("w0")]), Atom("B", [Variable("_w0")]))
    san = sanitize_modal_identifiers(f)
    names = _var_names(san)
    assert len(names) == 2
    assert "w0" in names


def test_sanitizer_of_geach_axiom_fresh_names_is_injective_and_legal():
    """A Geach frame (G(1,1,1,1), the '.2' axiom's own frame) exercises the
    OTHER fresh-name source: _geach_axiom's '_gz{n}'/'_gw'/'_gu'/'_gv'/'_gt',
    alongside _Fresh's own '_w0'.._w3' (one per Box/Diamond nesting level in
    the '.2' schema). All eight must come out distinct and legal."""
    node = qml_validity_formula(modal_axiom(".2"), frame="G(1,1,1,1)")
    before = _var_names(node)
    assert len(before) >= 8 and all(n.startswith("_") for n in
                                    (before - {"t", "v", "w", "x"}))
    san = sanitize_modal_identifiers(node)
    after = _var_names(san)
    assert len(after) == len(before)
    assert all(_SIMPLE_ID_RE.fullmatch(n) for n in after)


def test_sanitize_modal_identifiers_is_a_noop_on_an_already_legal_formula():
    """A plain classical formula with no qml-generated names at all must be
    returned structurally UNCHANGED (every name already legal)."""
    f = Implies(Quantifier("∀", Variable("x"), Atom("P", [Variable("x")])),
               Atom("Q", (Constant("alice"),)))
    assert sanitize_modal_identifiers(f) == f


def test_shim_predicate_and_term_namespaces_are_independent_of_variables():
    """A predicate and a variable sharing a spelling are DIFFERENT CASL
    namespaces (see _CaslIdentifierShim's own docstring) — sanitising a
    formula whose predicate happens to be named the same as a variable must
    not force either off its own name."""
    shim = _CaslIdentifierShim(Atom("_a0", [Variable("_a0")]))
    # both start illegal (leading underscore); each namespace resolves
    # independently, so both may perfectly well land on the SAME text 'a0'
    # (no cross-namespace collision check — see the class docstring).
    assert shim.predicate("_a0") == "a0"
    assert shim.variable("_a0") == "a0"


# =============================================================================
# World-relativized '=' / '≠' atoms (adversarial-review finding, C6):
# fol.qml's _st appends the current-world argument to EVERY atom it visits,
# including an object-language '=' or '≠' — so a genuinely binary user atom
# comes out of qml_translate as a TERNARY atom named '=' (or '≠'). CASL's own
# '=' is a fixed, always-exactly-2-ary, rigid built-in, so that ternary atom
# is not CASL identity at all (see fol.qml.qml_validity_formula's own
# docstring and hets.dol's module-level section comment for the full
# reasoning) — it must be aliased to a fresh, uninterpreted predicate, the
# same non-rigid reading Node.to_z3 / satisfies_modal / hol.isabelle_modal /
# hol.thf_modal already give it, never crash casl_export's arity-2 check and
# never silently collapse onto an arbitrary, meaningless name either.
# =============================================================================

def test_sanitize_modal_identifiers_aliases_world_relativized_equality_atom():
    """The reviewer's exact reproduction: Box(a=b) -> a=b under frame='T'.
    Before this fix, sanitize_modal_identifiers preserved the ternary '='
    atom under the literal name '=', which crashed casl_export's own
    exactly-2-ary check with a message that never mentioned modal logic.
    Now it must be renamed to the fixed alias 'weq' (mirroring
    hol.isabelle_modal._PRED_ALIAS's own '=' -> 'feq') and round-trip
    cleanly through to_casl_spec / casl_import."""
    a, b = Constant("a"), Constant("b")
    eq = Atom("=", [a, b])
    f = Implies(Box(eq), eq)
    node = qml_validity_formula(f, frame="T")
    # Pre-condition: the translation really did produce a ternary '=' atom
    # (arity 2 + the appended world argument) — otherwise this test would
    # not be exercising the bug at all.
    eq_atoms = [n for n in node.walk() if type(n).__name__ == "Atom" and n.predicate == "="]
    assert eq_atoms and all(len(n.args) == 3 for n in eq_atoms)

    san = sanitize_modal_identifiers(node)
    san_preds = {(n.predicate, len(n.args)) for n in san.walk()
                if type(n).__name__ == "Atom"}
    assert ("=", 3) not in san_preds          # never the literal name at arity != 2
    assert ("weq", 3) in san_preds
    assert all(_SIMPLE_ID_RE.fullmatch(p) for p, _ in san_preds)

    # Faithful to what Z3 already computes for this exact atom (Atom.to_z3
    # only special-cases an EXACTLY-2-ary '=' — a ternary one already becomes
    # an ordinary uninterpreted Z3 predicate, so aliasing it to an ordinary
    # CASL predicate changes nothing Z3-observable): hand-derived, this is
    # the T-schema (Box phi -> phi) instantiated at an ATOMIC sentence, valid
    # under any reflexive frame regardless of what that sentence "means".
    assert qml_is_valid(f, frame="T") is True
    assert qml_is_valid(f, frame="K") is False   # K has no reflexivity axiom

    # No longer crashes casl_export's own exactly-2-ary check — round-trips.
    text = to_casl_spec([], conjectures=[san], spec_name="EqT")
    assert "weq" in text
    assert parse_casl_spec(text).conjectures == (san,)


def test_sanitize_modal_identifiers_aliases_world_relativized_inequality_atom():
    """The evidence case the review also flagged: '≠' is never CASL-native
    (casl_export has no special handling for it at all — see
    fol/casl_export.py, which never mentions '≠'), so BEFORE this fix a
    world-relativized '≠' atom silently fell through to the ordinary
    predicate-renaming path and landed on an arbitrary, meaningless legal id
    ('v_'), carrying no trace that it ever denoted inequality. Now it gets
    the SAME fixed-alias treatment as '=', under its own distinct stem
    ('wneq' -> mirrors hol.isabelle_modal._PRED_ALIAS's '≠' -> 'fneq'), so
    the rename is at least principled and, being fixed rather than
    input-order-dependent, predictable."""
    a, b = Constant("a"), Constant("b")
    neq = Atom("≠", [a, b])
    f = Implies(Box(neq), neq)
    node = qml_validity_formula(f, frame="T")
    san = sanitize_modal_identifiers(node)
    san_preds = {(n.predicate, len(n.args)) for n in san.walk()
                if type(n).__name__ == "Atom"}
    assert ("wneq", 3) in san_preds
    assert ("weq", 3) not in san_preds        # '=' and '≠' never share a stem
    assert all(_SIMPLE_ID_RE.fullmatch(p) for p, _ in san_preds)
    assert qml_is_valid(f, frame="T") is True
    assert qml_is_valid(f, frame="K") is False


def test_equality_alias_leaves_a_genuinely_binary_equality_as_casl_native():
    """A genuinely 2-ary '=' atom untouched by _st — qml_axioms's own
    first_step axiom (emitted when T and N both occur) compares two WORLD
    variables directly, 'w = v', never world-relativized itself — must stay
    CASL's own literal, rigid '=', coexisting with an aliased ternary '='
    from the user's OWN formula in the SAME query without either being
    renamed onto the other."""
    from unicode_fol_kit.fol.nodes import Always, Next, And
    a, b = Constant("a"), Constant("b")
    eq = Atom("=", [a, b])
    f = And(Always(eq), Next(eq))   # both T and N occur -> first_step axiom fires
    node = qml_validity_formula(f, frame="K")
    san = sanitize_modal_identifiers(node)
    san_preds = {(n.predicate, len(n.args)) for n in san.walk()
                if type(n).__name__ == "Atom"}
    assert ("=", 2) in san_preds     # the first_step axiom's genuine world identity
    assert ("weq", 3) in san_preds   # the user's own, world-relativized equality
    # Round-trips: casl_export declares 'weq' but never '=' (CASL built-in).
    text = to_casl_spec([], conjectures=[san], spec_name="Combo")
    assert "weq :" in text
    assert "= :" not in text
    assert parse_casl_spec(text).conjectures == (san,)


def test_equality_alias_is_shared_across_repeated_occurrences_in_one_formula():
    """Every world-relativized '=' atom in ONE formula denotes the SAME
    single uninterpreted relation (mirroring Z3Env.get_pred's own cache,
    keyed by name alone — every ternary '=' atom qml_translate ever produces
    from one call already collapses onto ONE Z3 predicate today), so two
    occurrences of Box(a=b) in the same query must alias to the SAME CASL
    predicate name, not two different ones."""
    from unicode_fol_kit.fol.nodes import And
    a, b = Constant("a"), Constant("b")
    eq = Atom("=", [a, b])
    f = And(Box(eq), Box(eq))
    node = qml_validity_formula(f, frame="K")
    san = sanitize_modal_identifiers(node)
    eq_names = {n.predicate for n in san.walk()
               if type(n).__name__ == "Atom" and len(n.args) == 3
               and n.args[0] == Constant("a") and n.args[1] == Constant("b")}
    assert eq_names == {"weq"}


def test_equality_alias_is_injective_against_a_colliding_user_predicate():
    """If the formula ALSO happens to define a genuine predicate spelled
    'weq' (the SAME stem this shim would otherwise pick for a translated
    '='), the two must never collapse onto one name: the already-legal user
    predicate is seeded FIRST (see _CaslIdentifierShim's own two-pass
    docstring), so it keeps 'weq' and the ALIAS is the one bumped to
    'weq_2' — the same seed-before-resolve invariant the '_w0'-vs-'w0'
    variable collision test already pins, now checked for the equality
    alias's OWN, separate namespace collision."""
    from unicode_fol_kit.fol.nodes import And
    a, b = Constant("a"), Constant("b")
    eq = Atom("=", [a, b])
    user_weq = Atom("weq", [a, b])   # becomes ternary too, after _st's world append
    f = And(user_weq, Implies(Box(eq), eq))
    node = qml_validity_formula(f, frame="T")
    san = sanitize_modal_identifiers(node)
    san_preds = {(n.predicate, len(n.args)) for n in san.walk()
                if type(n).__name__ == "Atom"}
    assert ("weq", 3) in san_preds
    assert ("weq_2", 3) in san_preds
    assert len(san_preds) == len({p for p, _ in san_preds})  # no accidental merge


def test_equality_alias_refuses_a_genuinely_binary_inequality_atom_loudly():
    """Adversarial-review follow-up finding (C6): unlike '=', '≠' is never
    CASL-native at ANY arity (fol/casl_export.py never mentions it — grepped,
    confirmed) and fol.qml's '_st' never produces a '≠' atom at arity 2 (a
    world-relativized one is always 3-ary or more, since '_st' unconditionally
    appends the current-world argument). So a genuinely 2-ary '≠' can only
    reach sanitize_modal_identifiers via a call that bypasses
    qml_validity_formula/to_dol_library_from_modal entirely (the case this
    test exercises, matching the review's own reproduction) or a malformed
    pre-translation atom.

    BEFORE this fix, such an atom silently fell through to the ordinary
    predicate-renaming path and came out as the arbitrary, meaningless legal
    identifier 'v_' (reproduced by the review) -- indistinguishable from an
    unrelated predicate fact and carrying no trace that it ever denoted
    inequality, which is exactly the silent-approximation the project's own
    refuse-loudly rule forbids. It must now refuse loudly instead, naming
    '≠', mirroring how fol.casl_export.to_casl_spec already refuses the SAME
    atom when it is handed directly, bypassing this bridge entirely (that
    existing, unrelated refusal is the second assertion below)."""
    a, b = Constant("a"), Constant("b")
    ne = Atom("≠", [a, b])
    assert len(ne.args) == 2  # genuinely binary -- not yet world-relativized

    with pytest.raises(NotImplementedError, match="≠"):
        sanitize_modal_identifiers(ne)

    # The pre-existing, unrelated refusal this mirrors: casl_export itself
    # has never accepted '≠' at any arity, with or without this bridge.
    with pytest.raises(ValueError, match="not a simple CASL identifier"):
        to_casl_spec([], conjectures=[ne], spec_name="X")


def test_equality_alias_never_refuses_inequality_reached_through_qml_translation():
    """The documented, tested pipeline (qml_validity_formula ->
    sanitize_modal_identifiers) never triggers the refusal above: '_st'
    world-relativizes EVERY '≠' atom it visits to arity 3 (or more, under a
    many-sorted signature with extra typing arguments), so the genuinely
    2-ary case the previous test exercises is only reachable by bypassing
    qml_validity_formula, not through the ordinary route this pipeline is
    built for -- this is the same 'inequality_box_t'/'inequality_box_k'
    battery the roadmap item's own live Hets tests exercise, checked here
    offline for the refusal's absence specifically."""
    a, b = Constant("a"), Constant("b")
    ne = Atom("≠", [a, b])
    f = Implies(Box(ne), ne)
    node = qml_validity_formula(f, frame="T")
    san = sanitize_modal_identifiers(node)  # must not raise
    assert any(n.predicate == "wneq" for n in san.walk()
               if type(n).__name__ == "Atom")


# =============================================================================
# Round trip through casl_export / casl_import (an independent offline check
# that the sanitised Node is not just "legal text" but PARSES BACK to the
# exact same AST — casl_import.parse_casl_spec is a genuinely separate code
# path from casl_export.to_casl_spec, so this is a real cross-check, not a
# tautology).
# =============================================================================

@pytest.mark.parametrize("build_formula,kwargs", [
    (lambda: Implies(*(2 * [modal_axiom("T")])), dict(frame="T")),
    (lambda: modal_axiom(".2"), dict(frame="G(1,1,1,1)")),
    (lambda: Implies(Knows(Constant("alice"), Atom("P", ())), Atom("P", ())),
     dict(systems={"epistemic": "S5"})),
    (lambda: Implies(Box(Atom("=", [Constant("a"), Constant("b")])),
                     Atom("=", [Constant("a"), Constant("b")])),
     dict(frame="T")),
], ids=["t_axiom", "geach_axiom", "epistemic_with_systems", "equality_under_box"])
def test_sanitized_query_round_trips_through_casl_import(build_formula, kwargs):
    node = qml_validity_formula(build_formula(), **kwargs)
    san = sanitize_modal_identifiers(node)
    text = to_casl_spec([], conjectures=[san], spec_name="X")
    spec = parse_casl_spec(text)
    assert spec.conjectures == (san,)


# =============================================================================
# Golden CASL text (fully hand-derived) — the T axiom under a reflexive frame
# =============================================================================

def test_golden_t_axiom_query_as_casl_text():
    """Hand-derivation. qml_axioms('constant', 'T', formula=Box(P)->P) is
    ALREADY tested byte-exact elsewhere (tests/test_qml.py,
    tests/test_qml_bridges.py's gating tests) to emit, in order: sort
    discipline (t disjoint, world/object nonempty), R's typing, E's typing,
    R reflexivity (frame='T' is exactly {'refl'} — see fol.frames.FRAMES).
    qml_translate(Implies(Box(P), P), 'constant', world='w') is
    'World(w) -> ((forall _w0 (World(_w0) & R(w,_w0) -> P(_w0))) -> P(w))'
    (Box's own translation rule, _st's Atom rule appending the world arg to
    P). _validity_formula conjoins the axioms (there are no
    _signature_typing_facts here -- P is a 0-ary predicate, not a constant)
    and closes over w. THIS test's own job -- the only NEW behaviour --
    is that (1) qml_validity_formula returns that exact Node, (2)
    sanitize_modal_identifiers renames ONLY '_w0' (every other name --
    t, w, v, x, P, R, E, Object, World -- is already legal), to 'w0' (no
    collision in this formula), and (3) casl_export's own already-tested
    sort-inference/rendering (predicates alphabetical, one default sort
    'Thing' since nothing here is many-sorted) renders the result verbatim,
    wrapped by to_dol_library_from_modal / to_casl_spec exactly like any
    other single-conjecture spec."""
    from unicode_fol_kit.fol.nodes import Box
    P = Atom("P", ())
    f = Implies(Box(P), P)
    node = qml_validity_formula(f, mode="constant", frame="T")
    san = sanitize_modal_identifiers(node)
    text = to_casl_spec([], conjectures=[san], spec_name="TAxiom")
    expected = (
        "spec TAxiom =\n"
        "  sorts Thing\n"
        "  preds E : Thing * Thing;\n"
        "        Object : Thing;\n"
        "        P : Thing;\n"
        "        R : Thing * Thing;\n"
        "        World : Thing\n"
        "  . ((((((((forall t : Thing . not (World(t) /\\ Object(t))) /\\ "
        "(exists w : Thing . World(w))) /\\ (exists x : Thing . Object(x))) /\\ "
        "(forall w : Thing . forall v : Thing . (R(w, v) => "
        "(World(w) /\\ World(v))))) /\\ (forall x : Thing . forall w : Thing . "
        "(E(x, w) => (Object(x) /\\ World(w))))) /\\ (forall w : Thing . "
        "(World(w) => R(w, w)))) /\\ (forall x : Thing . forall w : Thing . "
        "forall v : Thing . (((Object(x) /\\ World(w)) /\\ (World(v) /\\ "
        "(E(x, w) /\\ R(w, v)))) => E(x, v)))) /\\ (forall x : Thing . "
        "forall w : Thing . forall v : Thing . (((Object(x) /\\ World(w)) /\\ "
        "(World(v) /\\ (E(x, v) /\\ R(w, v)))) => E(x, w)))) => "
        "(forall w : Thing . (World(w) => ((forall w0 : Thing . "
        "((World(w0) /\\ R(w, w0)) => P(w0))) => P(w)))) %implied\n"
        "end"
    )
    assert text == expected
    # Independent second check: re-parsing recovers the exact sanitised AST.
    assert parse_casl_spec(text).conjectures == (san,)


# =============================================================================
# Refusals propagate unchanged from qml.py / casl_export.py
# =============================================================================

def test_qml_validity_formula_propagates_until_refusal():
    """Until is not first-order definable — _st (and so
    _validity_formula/qml_validity_formula) refuses it by name, unchanged."""
    P, Q = Atom("P", ()), Atom("Q", ())
    with pytest.raises(NotImplementedError, match="Until"):
        qml_validity_formula(Until(P, Q))


def test_qml_validity_formula_propagates_unknown_mode():
    with pytest.raises(ValueError, match="unknown mode"):
        qml_validity_formula(Atom("P", ()), mode="nonsense")


def test_qml_validity_formula_propagates_non_first_order_frame():
    """GL/S4.1/Grz need a condition (Loeb/McKinsey/Grz) this first-order
    route cannot express — refused by name, same as qml_is_valid/qml_axioms."""
    from unicode_fol_kit.fol.nodes import Box
    with pytest.raises(NotImplementedError, match="Grz"):
        qml_validity_formula(Box(Atom("P", ())), frame="Grz")
