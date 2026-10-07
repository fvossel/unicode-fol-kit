r"""Tests for the fol.qml -> fol.casl_export / hets.dol bridge (roadmap item C6).

This file owns the OFFLINE half of the bridge: :func:`~unicode_logic_kit.fol.qml.qml_validity_formula`
(the public, documented entry point onto the SAME Node
:func:`~unicode_logic_kit.fol.qml.qml_is_valid` already feeds to Z3), and
:mod:`unicode_logic_kit.hets.dol`'s identifier-sanitisation shim
(:func:`~unicode_logic_kit.hets.dol.sanitize_modal_identifiers`,
:class:`~unicode_logic_kit.hets.dol._CaslIdentifierShim`).

The gap the shim was written for was ``fol.qml``'s own auto-generated fresh
variables (``_w0``, the Geach axiom's ``_gz0``/``_gw``/``_gu``/``_gv``/``_gt``, …),
which are not legal CASL identifiers ([A-Za-z][A-Za-z0-9_]*). Since 0.30.0 those
names are minted by :func:`~unicode_logic_kit.fol._identifiers.fresh_variables` and
are plain ``w0`` / ``v0`` / ``x0``, because an underscore-prefixed name is not a
legal identifier for the KIT's own parser either — so on that source the shim is
now a no-op, which the tests below assert instead of the old renaming. It stays
load-bearing for the OTHER source of illegal identifiers, which no renaming of
variables can remove: ``fol.qml``'s ``·`` user-predicate mark (a user atom named
like one of the embedding's own relations becomes ``R·``), U+00B7 being
punctuation CASL has no place for.

``tests/test_dol.py`` owns the other half: :func:`~unicode_logic_kit.hets.dol.to_dol_library_from_modal`
(the thin wrapper that composes ``qml_validity_formula`` + the sanitiser + the
EXISTING, unmodified :func:`~unicode_logic_kit.fol.casl_export.to_casl_spec` /
:func:`~unicode_logic_kit.hets.dol.to_dol_library`) and the live Hets battery that
cross-checks the CASL/DOL route's verdict against
:func:`~unicode_logic_kit.fol.qml.qml_is_valid`'s own (Z3) verdict for a battery of
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

from _bound_names import same_up_to_bound_names
from unicode_logic_kit.fol.nodes import (
    Always, And, Atom, Box, Constant, Diamond, Implies, Knows, Next, Not,
    Quantifier, Until, Variable,
)
from unicode_logic_kit.fol._msfl_nodes import SortedQuantifier
from unicode_logic_kit.fol.frames import modal_axiom
from unicode_logic_kit.fol.qml import (
    BARCAN, CONVERSE_BARCAN, _validity_formula, qml_is_valid, qml_validity_formula,
)
from unicode_logic_kit.fol.msflparser import MSFLParser
from unicode_logic_kit.fol.casl_export import to_casl_spec
from unicode_logic_kit.fol.casl_import import parse_casl_spec
from unicode_logic_kit.hets.dol import (
    _CaslIdentifierShim, _casl_sanitize_stem, sanitize_modal_identifiers,
)

# Mirrors casl_export._SIMPLE_ID_RE / dol._SIMPLE_ID_RE: a legal CASL SIMPLE-ID.
_SIMPLE_ID_RE = re.compile(r"[A-Za-z][A-Za-z0-9_]*")


def _var_names(node):
    return {n.name for n in node.walk() if type(n).__name__ == "Variable"}


def _predicate_names(node):
    return {n.predicate for n in node.walk() if type(n).__name__ == "Atom"}


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
    from unicode_logic_kit.fol.nodes import Box, Obligatory, Always, Believes
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

def test_casl_sanitize_stem_strips_a_leading_underscore_convention():
    """Hand-worked: every shape fol.qml's own _Fresh / Geach helper /
    _signature_typing_facts used to mint (they are plain 'w0'/'v0'/'x0' since
    0.30.0). Stripping the leading underscore(s) alone already makes each one a
    legal, human-readable CASL identifier, and the stem function has to keep
    doing that for any OTHER caller that hands it such a name."""
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


def test_sanitize_modal_identifiers_is_a_noop_on_a_plain_qml_translation():
    """qml_validity_formula(T axiom, frame='K') mints exactly ONE fresh variable
    (the box's world — 'K' has no reflexivity axiom to add a second quantifier),
    and it is named 'w0'. Together with every other identifier it emits (P,
    World, Object, R, E, and the hand-picked t, w, v, x) that is already a legal
    CASL identifier, so the whole formula must come back IDENTICAL — the same
    node, not merely the same name set. Before 0.30.0 the fresh world was '_w0',
    and this is where the shim earned its keep."""
    from unicode_logic_kit.fol.nodes import Box
    P = Atom("P", ())
    node = qml_validity_formula(Implies(Box(P), P), frame="K")
    before = _var_names(node)
    assert before == {"t", "w", "v", "x", "w0"}
    assert not any(n.startswith("_") for n in _all_identifiers(node))
    san = sanitize_modal_identifiers(node)
    assert san == node
    assert _all_identifiers(san) == _all_identifiers(node)


def test_an_object_variable_named_like_a_fresh_world_no_longer_collides():
    """fol.qml's own variable grammar allows an OBJECT variable literally named
    'w0' ([a-z][0-9]*), which is the name _Fresh would otherwise mint for the
    first fresh world. _Fresh is seeded with the formula's object-variable
    names, so it skips it and takes 'w1' — there is nothing for the shim to
    rename, and no two names to keep apart. (Before 0.30.0 the fresh world was
    '_w0', which collided with 'w0' only AFTER the shim stripped the underscore;
    that is the case this test used to drive.)"""
    from unicode_logic_kit.fol.nodes import Box
    w0 = Variable("w0")
    f = Quantifier("∀", w0, Implies(Box(Atom("A", [w0])), Atom("A", [w0])))
    node = qml_validity_formula(f, mode="constant", frame="K")
    before = _var_names(node)
    assert {"w0", "w1"} <= before            # the user's own, and the minted one
    assert not any(n.startswith("_") for n in before)
    assert sanitize_modal_identifiers(node) == node

    # The world variable really is a DIFFERENT variable from the object one:
    # qml_is_valid (Z3, never touched by this shim) disagrees between frame K
    # and frame T for this exact formula, which it could not do if the box's
    # world had been captured by the object quantifier — see tests/test_dol.py's
    # live TestModalCaslHetsLive for the SAME two cases ('collide_k' /
    # 'collide_t') cross-checked against a real Hets server.
    assert qml_is_valid(f, mode="constant", frame="K") is False
    assert qml_is_valid(f, mode="constant", frame="T") is True


def test_sanitizer_is_injective_on_the_user_mark_collision_qml_still_emits():
    """The collision the shim is still needed for. A user atom named like one of
    the embedding's own relations is renamed by fol.qml itself, by appending
    U+00B7 ('R' -> 'R·'), and U+00B7 is no CASL identifier character: the stem
    function folds it to '_', landing on 'R_'. A formula that ALSO contains a
    user predicate literally named 'R_' therefore hands the shim two distinct
    source names with one candidate, and they must stay two."""
    parse = MSFLParser(modal=True).parse
    f = parse("(R(alice) ∧ R_(alice)) → ◇(R(alice) ∧ R_(alice))")
    node = qml_validity_formula(f, mode="constant", frame="K")
    before = _predicate_names(node)
    assert {"R·", "R_"} <= before             # qml emitted both
    san = sanitize_modal_identifiers(node)
    after = _predicate_names(san)
    assert len(after) == len(before), "two distinct names collapsed onto one"
    assert "R_" in after                      # the already-legal name is untouched
    assert "R·" not in after
    assert all(_SIMPLE_ID_RE.fullmatch(n) for n in after)


def test_sanitizer_injective_regardless_of_which_name_the_walk_meets_first():
    """Same collision, built directly (not through qml) so the object
    variable 'w0' is visited BEFORE '_w0' in Node.walk()'s pre-order — the
    two-pass design (seed every already-legal name first, in a WHOLE-tree
    pass, before resolving any illegal one) must make injectivity independent
    of which one the walk happens to meet first; a naive single-pass,
    seed-as-you-go renamer would only get this right by accident of order."""
    from unicode_logic_kit.fol.nodes import And
    f = And(Atom("A", [Variable("w0")]), Atom("B", [Variable("_w0")]))
    san = sanitize_modal_identifiers(f)
    names = _var_names(san)
    assert len(names) == 2
    assert "w0" in names


def test_geach_axiom_fresh_names_are_already_legal_and_distinct():
    """A Geach frame (G(1,1,1,1), the '.2' axiom's own frame) exercises the
    OTHER fresh-name source: _geach_axiom's own bound worlds, alongside
    _Fresh's (one per Box/Diamond nesting level in the '.2' schema). All of
    them are minted, all must be distinct, and all must already be legal CASL
    identifiers — they used to be '_gz0'/'_gw'/'_gu'/'_gv'/'_gt' and
    '_w0'..'_w3', and the shim had to rename every one."""
    node = qml_validity_formula(modal_axiom(".2"), frame="G(1,1,1,1)")
    before = _var_names(node)
    assert len(before) >= 8
    assert all(_SIMPLE_ID_RE.fullmatch(n) for n in before)
    assert sanitize_modal_identifiers(node) == node


def test_sanitize_modal_identifiers_is_a_noop_on_an_already_legal_formula():
    """A plain classical formula with no qml-generated names at all must be
    returned structurally UNCHANGED (every name already legal)."""
    f = Implies(Quantifier("∀", Variable("x"), Atom("P", [Variable("x")])),
               Atom("Q", (Constant("alice"),)))
    assert sanitize_modal_identifiers(f) == f


def test_shim_names_it_mints_are_fresh_across_the_kinds_of_symbol():
    """A predicate and a variable that both start illegal (leading underscore) and
    sanitise to the same stem 'a0' are given two spellings. CASL writes a bound
    variable, a constant and a predicate as one identifier, so a name the shim
    mints is fresh against every symbol of the formula and not only against the
    symbols of its own kind (the old expectation, both 'a0', let a minted
    variable meet a minted predicate of that spelling).

    Hand-derived: the first name resolved takes the stem, the second is pushed to
    the next free suffix 'a0_2'; both are legal and they differ."""
    shim = _CaslIdentifierShim(Atom("_a0", [Variable("_a0")]))
    assert shim.predicate("_a0") == "a0"
    assert shim.variable("_a0") == "a0_2"


# =============================================================================
# Object identity through the bridge. fol.qml translates ``a = b`` to the same
# binary ``a = b`` over the object terms with NO world argument, and ``a ≠ b``
# to ``¬(a = b)`` (its "Equality is rigid" section). That binary '=' is CASL's
# own built-in, rigid identity, so the bridge has nothing to rename: it arrives
# native, casl_export renders it infix without declaring it, and casl_import
# reads the same Atom back. (Earlier, '=' was world-relativised into a ternary
# uninterpreted atom and hets.dol aliased it to 'weq'/'wneq'; the tests below
# replaced the ones that pinned that alias, and the alias is gone.)
# =============================================================================

# The predicate vocabulary of any qml query over constants a, b: the four
# symbols qml's axioms and typing facts use, plus CASL's built-in '=' (arity 2).
_QML_GUARDS = {("World", 1), ("Object", 1), ("R", 2), ("E", 2)}
_PREDS_BLOCK = (
    "preds E : Thing * Thing;\n"
    "        Object : Thing;\n"
    "        R : Thing * Thing;\n"
    "        World : Thing\n"
)


def _atoms(node):
    return [n for n in node.walk() if type(n).__name__ == "Atom"]


def _vocabulary(node):
    """{(predicate, arity)} over every Atom of ``node``, '=' included."""
    return {(n.predicate, len(n.args)) for n in _atoms(node)}


def test_modal_equality_arrives_binary_and_is_left_as_casl_native():
    """The reviewer's reproduction, □(a = b) → a = b under T.

    Hand-derived: frame T adds R-reflexivity and no temporal operator occurs,
    so there is no first_step axiom; the only '=' atoms in the query are the
    two occurrences in the formula, each translated to the SAME binary a = b
    (no world argument). Nothing is renamed: the vocabulary is qml's four
    guards plus the built-in '=', '=' is never declared, and the text reads
    back as the identical AST."""
    a, b = Constant("a"), Constant("b")
    eq = Atom("=", [a, b])
    f = Implies(Box(eq), eq)
    node = qml_validity_formula(f, frame="T")
    assert [n for n in _atoms(node) if n.predicate == "="] == [eq, eq]

    san = sanitize_modal_identifiers(node)
    assert _vocabulary(san) == _QML_GUARDS | {("=", 2)}

    text = to_casl_spec([], conjectures=[san], spec_name="EqT")
    assert _PREDS_BLOCK in text            # '=' is CASL-built-in: not declared
    assert text.count("a = b") == 2        # rendered infix, once per occurrence
    assert parse_casl_spec(text).conjectures == (san,)

    # Reason for the verdicts: the T-schema on an atomic sentence is valid on a
    # reflexive frame; in K a dead-end world makes the box vacuously true while
    # a and b may differ (fol.qml's "Equality is rigid", second bullet).
    assert qml_is_valid(f, frame="T") is True
    assert qml_is_valid(f, frame="K") is False


def test_modal_inequality_arrives_as_negated_native_equality():
    """□(a ≠ b) → a ≠ b under T.

    Hand-derived: ST writes '≠' as ¬(a = b) at every world, so the query
    contains two Not(a = b), no '≠' atom, and the same vocabulary as the
    equality case. CASL has no disequality, and needs none: casl_export
    renders the negation as 'not a = b' (two occurrences) and the text reads
    back as the identical AST."""
    a, b = Constant("a"), Constant("b")
    eq, neq = Atom("=", [a, b]), Atom("≠", [a, b])
    f = Implies(Box(neq), neq)
    node = qml_validity_formula(f, frame="T")
    assert not [n for n in _atoms(node) if n.predicate == "≠"]
    assert len([n for n in node.walk() if isinstance(n, Not) and n.formula == eq]) == 2

    san = sanitize_modal_identifiers(node)
    assert _vocabulary(san) == _QML_GUARDS | {("=", 2)}

    text = to_casl_spec([], conjectures=[san], spec_name="NeqT")
    assert _PREDS_BLOCK in text
    assert text.count("not a = b") == 2
    assert parse_casl_spec(text).conjectures == (san,)

    assert qml_is_valid(f, frame="T") is True    # T-schema, as above
    assert qml_is_valid(f, frame="K") is False   # dead end, as above


def test_user_identity_and_world_identity_share_the_one_native_equality():
    """A query with both Always and Next gets qml's first_step axiom, which
    contains the WORLD identity w = v (two world variables); the user's own
    a = b sits in the same query. Hand-derived: Always(eq) and Next(eq)
    contribute one a = b each, the axiom contributes one w = v, so there are
    exactly three '=' atoms, all binary and all CASL's one built-in '=' — the
    two kinds of identity are told apart by their operands (and the World /
    Object guards), not by the symbol."""
    a, b = Constant("a"), Constant("b")
    eq = Atom("=", [a, b])
    world_identity = Atom("=", [Variable("w"), Variable("v")])
    node = qml_validity_formula(And(Always(eq), Next(eq)), frame="K")
    san = sanitize_modal_identifiers(node)
    eq_atoms = [n for n in _atoms(san) if n.predicate == "="]
    assert len(eq_atoms) == 3
    assert eq_atoms.count(world_identity) == 1
    assert eq_atoms.count(eq) == 2

    text = to_casl_spec([], conjectures=[san], spec_name="Combo")
    assert "= :" not in text and "weq" not in text   # never declared, never renamed
    assert parse_casl_spec(text).conjectures == (san,)


def test_repeated_identity_occurrences_stay_one_unrenamed_equality():
    """Two □(a = b) in one query. Hand-derived: each box contributes one
    a = b, no temporal operator means no first_step axiom, so the '=' atoms are
    exactly [a = b, a = b], identical to the source atom — no occurrence gets a
    name of its own — and the whole predicate vocabulary is qml's guards plus
    '='."""
    a, b = Constant("a"), Constant("b")
    eq = Atom("=", [a, b])
    node = qml_validity_formula(And(Box(eq), Box(eq)), frame="K")
    san = sanitize_modal_identifiers(node)
    assert [n for n in _atoms(san) if n.predicate == "="] == [eq, eq]
    assert _vocabulary(san) == _QML_GUARDS | {("=", 2)}


def test_a_user_predicate_named_weq_is_an_ordinary_predicate():
    """'weq' was once the name this bridge gave a translated identity, so a
    user predicate spelled 'weq' had to be bumped to 'weq_2'. Identity is no
    longer renamed, so nothing can collide with it. Hand-derived: the user's
    binary weq(a, b) is an ordinary atom, so ST appends the world and it
    becomes the ternary weq(a, b, w) and keeps its name; the identity in the
    same query stays the binary built-in '='; the predicate vocabulary is qml's
    guards, weq/3 and '=' — no 'weq_2' anywhere."""
    a, b = Constant("a"), Constant("b")
    eq = Atom("=", [a, b])
    f = And(Atom("weq", [a, b]), Implies(Box(eq), eq))
    node = qml_validity_formula(f, frame="T")
    san = sanitize_modal_identifiers(node)
    assert _vocabulary(san) == _QML_GUARDS | {("weq", 3), ("=", 2)}
    text = to_casl_spec([], conjectures=[san], spec_name="UserWeq")
    assert "weq : Thing * Thing * Thing" in text
    assert "weq_2" not in text
    assert parse_casl_spec(text).conjectures == (san,)


def test_sanitizer_refuses_a_disequality_atom_of_any_arity_loudly():
    """'≠' is never CASL-native at any arity (fol/casl_export.py has no rule for
    it) and the bridge's qml_validity_formula never leaves one in its output,
    so a '≠' atom reaches sanitize_modal_identifiers only in a Node built by
    hand (or parsed from classical text) and handed to it directly. The old
    behaviour, relabelling it onto an arbitrary legal identifier ('v_') that
    carries no trace of 'not equal', is the silent approximation this package
    refuses; so it must refuse loudly, by name, and say what to write instead:
    'Not(Atom("=", ...))', which is what fol.qml itself writes. Arity does not
    matter: a unary or ternary '≠' is no more renderable than a binary one."""
    a, b, c = Constant("a"), Constant("b"), Constant("c")
    for args in ([a], [a, b], [a, b, c]):
        ne = Atom("≠", args)
        with pytest.raises(NotImplementedError, match="≠") as excinfo:
            sanitize_modal_identifiers(ne)
        assert 'Not(Atom("=", [a, b]))' in str(excinfo.value)

    # The pre-existing, unrelated refusal this mirrors: casl_export itself has
    # never accepted '≠', with or without this bridge.
    with pytest.raises(ValueError, match="not a simple CASL identifier"):
        to_casl_spec([], conjectures=[Atom("≠", [a, b])], spec_name="X")


@pytest.mark.parametrize("case_id,formula,kwargs", [
    ("box", lambda: Box(Atom("≠", [Constant("a"), Constant("b")])), {}),
    ("diamond", lambda: Diamond(Atom("≠", [Constant("a"), Constant("b")])), {}),
    ("always", lambda: Always(Atom("≠", [Constant("a"), Constant("b")])), {}),
    ("knows", lambda: Knows(Constant("alice"), Atom("≠", [Constant("a"), Constant("b")])),
     dict(systems={"epistemic": "S5"})),
    ("under_forall", lambda: Quantifier("∀", Variable("x"), Atom("≠", [Variable("x"), Constant("a")])), {}),
], ids=["box", "diamond", "always", "knows", "under_forall"])
def test_inequality_reached_through_qml_translation_is_lowered_never_refused(
        case_id, formula, kwargs):
    """The documented pipeline never reaches the refusal above: whatever
    construct the '≠' sits under (a box, a diamond, a temporal operator, an
    agent's knowledge, a quantifier), ST writes it as ¬(=) at that world, so no
    '≠' atom survives qml_validity_formula, the sanitiser has nothing to
    refuse, and casl_export accepts the result and reads it back."""
    node = qml_validity_formula(formula(), **kwargs)
    assert not [n for n in _atoms(node) if n.predicate == "≠"], case_id
    assert any(n.predicate == "=" for n in _atoms(node)), case_id
    san = sanitize_modal_identifiers(node)           # must not raise
    text = to_casl_spec([], conjectures=[san], spec_name="Neq")
    read = parse_casl_spec(text).conjectures
    # The text means the query up to the names of its bound variables. The epistemic
    # axioms bind a variable 'a' (the agent) and this query names a constant 'a'; CASL
    # reads a bound variable spelled like a declared operation of the spec as
    # ambiguous, so the writer renames those binders (a0, a1, ...) and the formula
    # reads back as an alpha-variant of the query. Where no binder clashes the text
    # reads back as the very same formula.
    assert len(read) == 1 and same_up_to_bound_names(read[0], san)
    if case_id != "knows":
        assert read == (san,)


@pytest.mark.parametrize("args", [
    [Constant("a")], [Constant("a"), Constant("b"), Constant("c")]],
    ids=["unary", "ternary"])
def test_a_non_binary_equals_atom_is_not_aliased_and_is_refused_by_name(args):
    """What an atom literally named '=' with an arity other than 2 — the case
    the old 'weq' alias existed for — can still do. It can only be BUILT by
    hand: Atom does not check arity, but no text front-end parses to one (the
    next test) and fol.qml refuses it. Hand-derived consequences: the sanitiser
    keeps it under the literal name '=' (nothing to alias to), CASL's exactly-
    two-terms check then refuses it by name, and the modal route refuses it
    earlier, in qml, with a message that says '=' is reserved for identity and
    to rename the predicate if a different relation was meant."""
    from unicode_logic_kit.hets.dol import to_dol_library_from_modal
    t = Atom("=", args)
    assert sanitize_modal_identifiers(t) == t
    with pytest.raises(ValueError, match="exactly 2 arguments"):
        to_casl_spec([], conjectures=[t], spec_name="X")
    with pytest.raises(ValueError, match="exactly two terms"):
        qml_validity_formula(Box(t))
    with pytest.raises(ValueError, match="exactly two terms"):
        to_dol_library_from_modal(Box(t))


def _identity_arities(parse, text):
    """Arities of every '='/'≠' atom ``parse(text)`` yields (empty if it
    refuses the text outright)."""
    try:
        result = parse(text)
    except Exception:
        return set()
    return {len(n.args) for r in (result if isinstance(result, list) else [result])
            for n in r.walk()
            if isinstance(n, Atom) and n.predicate in ("=", "≠")}


def test_no_text_front_end_builds_a_non_binary_identity_atom():
    """The reachability claim behind deleting the alias: a '='/'≠' atom whose
    arity is not 2 cannot come out of any text front-end. Each parser either
    refuses the prefix spelling =(a, b, c) outright or yields only binary atoms;
    SMT-LIB's chainable (= a b c) / (distinct a b c) are expanded pairwise by
    the importer into binary atoms (hand-derived: a=b, b=c and a≠b, a≠c, b≠c)."""
    from unicode_logic_kit import MSFLParser
    from unicode_logic_kit.atp.z3_input import parse_smtlib
    from unicode_logic_kit.fol.latex_input import parse_latex
    from unicode_logic_kit.fol.prolog_input import parse_prolog_clause
    from unicode_logic_kit.fol.prover9_input import parse_prover9
    from unicode_logic_kit.fol.tptp_input import parse_tptp_formula

    prefix = "=(a, b, c)"
    for parse in (MSFLParser().parse, parse_latex, parse_prolog_clause,
                  parse_prover9, parse_tptp_formula):
        assert _identity_arities(parse, prefix) <= {2}, parse
    for parse, text in ((MSFLParser().parse, "a = b"), (MSFLParser().parse, "a ≠ b"),
                        (parse_tptp_formula, "a != b"), (parse_prover9, "a = b")):
        assert _identity_arities(parse, text) == {2}, (parse, text)

    decls = "(declare-const a Int)(declare-const b Int)(declare-const c Int)"
    assert _identity_arities(parse_smtlib, decls + "(assert (= a b c))") == {2}
    assert _identity_arities(parse_smtlib, decls + "(assert (distinct a b c))") == {2}


@pytest.mark.parametrize("case_id,build,kwargs,expected", [
    # Rigidity: identity does not vary by world, so necessity of identity and of
    # distinctness hold in K, the weakest frame.
    ("identity_necessity_k",
     lambda a, b: Implies(Atom("=", [a, b]), Box(Atom("=", [a, b]))), dict(frame="K"), True),
    ("distinctness_necessity_k",
     lambda a, b: Implies(Atom("≠", [a, b]), Box(Atom("≠", [a, b]))), dict(frame="K"), True),
    # ◇(a = b) → a = b is the contrapositive of distinctness necessity.
    ("possible_identity_k",
     lambda a, b: Implies(Diamond(Atom("=", [a, b])), Atom("=", [a, b])), dict(frame="K"), True),
    # The converse direction needs a successor-or-self: dead end in K, reflexive in T.
    ("box_identity_k",
     lambda a, b: Implies(Box(Atom("=", [a, b])), Atom("=", [a, b])), dict(frame="K"), False),
    ("box_identity_t",
     lambda a, b: Implies(Box(Atom("=", [a, b])), Atom("=", [a, b])), dict(frame="T"), True),
    # Identity is reflexive, with no axiom for it: a = a, even where a may not exist.
    ("reflexive_varying",
     lambda a, b: Atom("=", [a, a]), dict(mode="varying"), True),
    # a = b alone is contingent: two constants may denote two objects.
    ("identity_not_valid",
     lambda a, b: Atom("=", [a, b]), dict(), False),
], ids=["identity_necessity_k", "distinctness_necessity_k", "possible_identity_k",
        "box_identity_k", "box_identity_t", "reflexive_varying", "identity_not_valid"])
def test_identity_query_round_trips_and_carries_qmls_rigid_verdict(
        case_id, build, kwargs, expected):
    """End to end, one row per hand-derived fact of fol.qml's "Equality is
    rigid": (1) the expectation equals Z3's verdict on the modal formula
    (qml_is_valid); (2) the CASL query for it round-trips — sanitize ->
    to_casl_spec -> parse_casl_spec returns an AST equal to the sanitised
    query — and contains only binary '=' atoms and no '≠' or renamed
    equality."""
    f = build(Constant("a"), Constant("b"))
    assert qml_is_valid(f, **kwargs) is expected, case_id
    san = sanitize_modal_identifiers(qml_validity_formula(f, **kwargs))
    assert {len(n.args) for n in _atoms(san) if n.predicate == "="} == {2}
    assert not any(n.predicate in ("≠", "weq", "wneq") for n in _atoms(san))
    text = to_casl_spec([], conjectures=[san], spec_name="Rigid")
    assert parse_casl_spec(text).conjectures == (san,)


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
    from unicode_logic_kit.fol.nodes import Box
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
    from unicode_logic_kit.fol.nodes import Box
    with pytest.raises(NotImplementedError, match="Grz"):
        qml_validity_formula(Box(Atom("P", ())), frame="Grz")
