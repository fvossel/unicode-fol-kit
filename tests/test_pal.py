"""Tests for Public Announcement Logic (PAL): the Announce/AnnounceDiamond AST
nodes (unicode_fol_kit.fol._modal_nodes), their parser syntax, the syntactic
reduction unicode_fol_kit.fol.pal.reduce_announcements, direct Kripke evaluation
(unicode_fol_kit.semantics.kripke.satisfies_modal), and the atp.modal_tableau
decision procedure over PAL formulas.

Correctness anchor: satisfies_modal interprets Announce/AnnounceDiamond directly
via the restricted-model semantics (semantics.dynamic_epistemic.announce) — this
is the ORACLE that reduce_announcements (a purely syntactic elimination) is
differentially tested against, both in hand-picked cases and over ~100 random PAL
formulas across several small Kripke models (test_reduce_announcements_differential).
"""

import random

import pytest

from unicode_fol_kit.fol.nodes import (
    Node,
    Atom, Not, And, Or, Xor, Implies, Iff, Constant, Variable,
    Knows, Believes, Says, Wants, Box, Diamond, Obligatory, Permitted,
    Always, Eventually, Next, Until, Historically, Once, Previous, Since,
    Would, Might, Nominal, At, Quantifier,
)
from unicode_fol_kit.fol._modal_nodes import Announce, AnnounceDiamond
from unicode_fol_kit.fol.pal import reduce_announcements
from unicode_fol_kit.fol.msflparser import MSFLParser
from unicode_fol_kit.fol.verbalize import to_english
from unicode_fol_kit.semantics.kripke import KripkeModel, satisfies_modal
from unicode_fol_kit.semantics.dynamic_epistemic import (
    announce, box_announce, diamond_announce,
)
from unicode_fol_kit.atp.modal_tableau import (
    has_modal, is_modal_valid, modal_decide, modal_countermodel,
)
from unicode_fol_kit.hol.isabelle_modal import to_isabelle_modal

p = Atom("P", [])
q = Atom("Q", [])
r = Atom("R", [])
a = Constant("a")

_MODAL_PARSER = MSFLParser(modal=True)


# --------------------------------------------------------------------------- #
# AST contract: to_dict/from_dict, to_z3/to_prover9/to_tptp rejection, tree
# --------------------------------------------------------------------------- #

def test_announce_to_dict_round_trip():
    """to_dict/from_dict round-trips through Node.from_dict, including nesting."""
    f = Announce(p, AnnounceDiamond(q, Knows(a, r)))
    assert Node.from_dict(f.to_dict()) == f


def test_announce_diamond_to_dict_round_trip():
    f = AnnounceDiamond(And(p, q), Not(r))
    assert Node.from_dict(f.to_dict()) == f


@pytest.mark.parametrize("cls", [Announce, AnnounceDiamond])
def test_export_rejections_point_at_reduce_announcements(cls):
    """to_z3/to_prover9/to_tptp reject with a message naming the sanctioned route."""
    f = cls(p, q)
    for method in ("to_z3", "to_prover9", "to_tptp"):
        with pytest.raises(NotImplementedError, match="reduce_announcements"):
            getattr(f, method)()


def test_tree_parts_expose_both_operands():
    """_tree_parts (tree_str/to_dot) shows announcement and formula as children,
    in that order — a purely structural check independent of the fixity-registry
    gap documented on to_unicode_str (tree_str/_tree_parts are per-node overrides,
    dispatched polymorphically by tree_str itself, so nesting is never a problem
    here — see test_announce_nested_under_registry_operator_render_gap).
    """
    f = Announce(p, q)
    label, children = f._tree_parts()
    assert label == "[!]"
    assert children == [p, q]
    tree = f.tree_str()
    assert "Atom: P" in tree and "Atom: Q" in tree


# --------------------------------------------------------------------------- #
# Parser round-trips: parse ∘ to_unicode_str = id
# --------------------------------------------------------------------------- #

def _round_trip(f: Node) -> Node:
    s = f.to_unicode_str()
    return _MODAL_PARSER.parse(s)


def test_round_trip_basic_announce():
    f = Announce(p, q)
    assert f.to_unicode_str() == "[P!]Q"
    assert _round_trip(f) == f


def test_round_trip_basic_announce_diamond():
    f = AnnounceDiamond(p, Not(q))
    assert f.to_unicode_str() == "⟨P!⟩¬Q"
    assert _round_trip(f) == f


def test_round_trip_nested_announcement_in_post_condition():
    """[φ!][χ!]ψ — an announcement nested inside the outer's post-condition."""
    f = Announce(p, Announce(q, r))
    assert f.to_unicode_str() == "[P!][Q!]R"
    assert _round_trip(f) == f


def test_round_trip_nested_announcement_in_announcement_position():
    """[[χ!]ψ!]φ — an announcement nested inside the outer's ANNOUNCED formula
    (the φ slot uses the full `formula` grammar rule precisely so this parses).
    """
    f = Announce(Announce(q, r), p)
    assert f.to_unicode_str() == "[[Q!]R!]P"
    assert _round_trip(f) == f


def test_round_trip_diamond_nested_in_box():
    f = AnnounceDiamond(Announce(p, q), r)
    assert _round_trip(f) == f


def test_round_trip_announcement_containing_knows():
    """The ANNOUNCED formula (φ) itself contains K_a — a natural PAL formula
    ("after announcing that a knows P, Q holds")."""
    f = Announce(Knows(a, p), q)
    assert f.to_unicode_str() == "[K_a P!]Q"
    assert _round_trip(f) == f


def test_round_trip_post_condition_containing_knows():
    f = Announce(p, Knows(a, q))
    assert f.to_unicode_str() == "[P!]K_a Q"
    assert _round_trip(f) == f


def test_precedence_post_condition_binds_tightly():
    """[p!]q ∧ r groups as ([p!]q) ∧ r — the post-condition parses at the PREFIX
    level (as tightly as ¬ / □ / K_a), so it does NOT swallow the following ∧ r.
    Hand-derivation: since Announce is a `prefix`-level alternative, the WHOLE
    `[p!]q` block is one `prefix`, and `prefix ∧ atom` is exactly how `p ∧ q`
    itself parses — so the ∧ must attach ABOVE the announcement, not inside it.

    The string is built BY HAND here (not via Announce(...).to_unicode_str())
    because ``And(Announce(...), r)`` is exactly the documented registry-render
    gap (see test_announce_nested_under_registry_operator_render_gap) — this
    test is purely about PARSER precedence, independent of that renderer gap.
    """
    parsed = _MODAL_PARSER.parse("[P!]Q ∧ R")
    assert parsed == And(Announce(p, q), r)
    # The wrong reading would be Announce(p, And(q, r)); confirm we did NOT get it.
    assert parsed != Announce(p, And(q, r))


def test_plain_bracket_grouping_unaffected():
    """The pre-existing "[" formula "]" grouping rule still parses as plain P —
    the PAL syntax shares the "[" / "]" anonymous terminal (documented as the
    least-intrusive choice in _modal_nodes.py) but requires a literal "!" that
    bracket-grouping never produces, so the two never collide on any input.
    """
    assert _MODAL_PARSER.parse("[P]") == p
    assert _MODAL_PARSER.parse("[P ∧ Q]") == And(p, q)


def test_announce_syntax_requires_bang_not_confused_with_grouping():
    """"[P!]Q" is unambiguously Announce, never bracket-grouping (which has no
    rule that could consume a stray "!")."""
    parsed = _MODAL_PARSER.parse("[P!]Q")
    assert parsed == Announce(p, q)


def test_announce_nested_under_registry_operator_renders_and_reparses():
    """Integration closed the one-time rendering gap: the central
    _msfl_nodes._uni/_latex dispatchers now delegate Announce/AnnounceDiamond
    to their bracket-delimited renderers (with prefix-level precedence in
    _UNI_BASE_PREC), so an announcement nested as the CHILD of a registry-driven
    operator renders — and round-trips — like any other node.
    """
    cases = [
        Not(Announce(p, q)),
        And(Announce(p, q), r),
        Knows(a, AnnounceDiamond(p, q)),
        Implies(Announce(p, q), AnnounceDiamond(q, r)),
    ]
    for f in cases:
        assert _MODAL_PARSER.parse(f.to_unicode_str()) == f, f.to_unicode_str()
    # to_latex goes through the same dispatcher and must not raise either.
    assert "mathbin{!}" in Not(Announce(p, q)).to_latex()
    # Announce as the outermost node, nested inside itself, stays as before:
    assert Announce(p, Announce(q, r)).to_unicode_str() == "[P!][Q!]R"


def test_to_latex_exact_strings():
    """LaTeX is not parseable (documented codebase-wide), so assert exact text."""
    assert Announce(p, q).to_latex() == "[P\\mathbin{!}]Q"
    assert AnnounceDiamond(p, q).to_latex() == "\\langle P\\mathbin{!}\\rangle Q"


def test_to_english_verbalizes_and_recurses_either_direction():
    """verbalize.to_english is a single recursive function (not the closed
    registry _uni/_latex depend on), so — unlike to_unicode_str — it has NO
    nesting gap in either direction."""
    assert "P" in to_english(Announce(p, q))
    assert "Q" in to_english(Announce(p, q))
    # Announce nested under Knows (the exact shape that breaks to_unicode_str)
    # verbalizes fine:
    text = to_english(Knows(a, Announce(p, q)))
    assert "knows" in text and "P" in text and "Q" in text


# --------------------------------------------------------------------------- #
# Direct Kripke evaluation (the oracle) — hand-derived truth values
# --------------------------------------------------------------------------- #

def test_announce_vacuously_true_when_announcement_false():
    """[φ!]ψ is vacuously true wherever φ is false — an untruthful announcement
    is simply not made. Model: single world, P false, so [P!]anything holds."""
    m = KripkeModel({0}, {}, {0: set()})
    assert satisfies_modal(Announce(p, q), m, 0) is True
    assert satisfies_modal(Announce(p, Not(q)), m, 0) is True  # even a contradiction


def test_announce_diamond_false_when_announcement_false():
    """Dual of the above: ⟨φ!⟩ψ is false whenever φ itself is false."""
    m = KripkeModel({0}, {}, {0: set()})
    assert satisfies_modal(AnnounceDiamond(p, q), m, 0) is False


def test_announce_matches_box_announce_helper():
    """satisfies_modal(Announce(...)) agrees with dynamic_epistemic.box_announce
    (its own implementation) at every world of a small model — by construction
    they call the same announce(); this pins that satisfies_modal's Announce case
    is exactly a thin wrapper around it, not a parallel re-implementation."""
    m = KripkeModel({0, 1}, {"K:a": {(0, 0), (0, 1), (1, 0), (1, 1)}},
                    {0: {"P"}, 1: set()})
    f = Announce(p, Knows(a, p))
    fd = AnnounceDiamond(p, Knows(a, p))
    for w in (0, 1):
        assert satisfies_modal(f, m, w) == box_announce(m, w, p, Knows(a, p))
        assert satisfies_modal(fd, m, w) == diamond_announce(m, w, p, Knows(a, p))


def test_moore_sentence_box_announcement_is_not_valid_hand_derived():
    """The classic Moore-sentence countermodel: worlds {0,1}, agent a fully
    uncertain (K:a = total relation), P true at 0 and false at 1.

    φ = P ∧ ¬K_a P ("P is true, but a doesn't know it") is true at world 0 (P
    true; a considers world 1 possible, where P is false, so a doesn't know P)
    and false at world 1 (P false there).

    HAND DERIVATION of [φ!]K_a φ at world 0:
      M,0 ⊨ φ, so we must check M|φ,0 ⊨ K_a φ.
      M|φ keeps only world 0 (the sole φ-world), with K:a restricted to {(0,0)}.
      In M|φ: P is still true at 0 (valuation copied), and K_a P is now TRUE
      (0's only surviving K:a-successor is 0 itself, where P holds) — so ¬K_a P
      is FALSE in M|φ, hence φ = P ∧ ¬K_a P is FALSE at 0 in M|φ.
      So K_a φ requires φ at every K:a-successor of 0 in M|φ (just 0 itself) —
      but φ is false there — so K_a φ is FALSE in M|φ at 0.
      Hence M,0 ⊨ [φ!]K_a φ is FALSE — announcing the Moore sentence DESTROYS
      its own truth (the textbook PAL phenomenon: "P ∧ ¬K_a P" is unannounceable).
    """
    m = KripkeModel({0, 1}, {"K:a": {(0, 0), (0, 1), (1, 0), (1, 1)}},
                    {0: {"P"}, 1: set()})
    phi = And(p, Not(Knows(a, p)))
    box_moore = Announce(phi, Knows(a, phi))
    assert satisfies_modal(box_moore, m, 0) is False
    # And it agrees with the syntactic reduction (differential spot-check):
    assert satisfies_modal(reduce_announcements(box_moore), m, 0) is False
    # At world 1, φ is false, so the box announcement is vacuously true there.
    assert satisfies_modal(box_moore, m, 1) is True


def test_moore_sentence_diamond_announcement_is_satisfiable_hand_derived():
    """⟨φ!⟩⊤ (φ = P ∧ ¬K_a P) IS true at world 0 — the announcement itself is
    truthful there (φ true) and ⊤ trivially holds afterwards; false at world 1
    (φ false there, so the diamond form fails outright)."""
    m = KripkeModel({0, 1}, {"K:a": {(0, 0), (0, 1), (1, 0), (1, 1)}},
                    {0: {"P"}, 1: set()})
    phi = And(p, Not(Knows(a, p)))
    top = Or(p, Not(p))
    diamond_moore = AnnounceDiamond(phi, top)
    assert satisfies_modal(diamond_moore, m, 0) is True
    assert satisfies_modal(diamond_moore, m, 1) is False


# --------------------------------------------------------------------------- #
# reduce_announcements: hand-checked reduction axiom cases
# --------------------------------------------------------------------------- #

def test_reduce_atom_is_identity():
    assert reduce_announcements(p) == p


def test_reduce_box_announcement_atomic():
    """[P!]Q reduces to P → Q (atoms relativize to themselves)."""
    assert reduce_announcements(Announce(p, q)) == Implies(p, q)


def test_reduce_diamond_announcement_atomic():
    """⟨P!⟩Q reduces to P ∧ Q."""
    assert reduce_announcements(AnnounceDiamond(p, q)) == And(p, q)


def test_reduce_knows_reduction_axiom():
    """(K_a ψ)^φ = K_a(φ → ψ^φ); ψ atomic so ψ^φ = ψ."""
    f = Announce(p, Knows(a, q))
    expected = Implies(p, Knows(a, Implies(p, q)))
    assert reduce_announcements(f) == expected


def test_reduce_diamond_modality_reduction_axiom():
    """(◇ψ)^φ = ◇(φ ∧ ψ^φ) — the diamond-wise (existential) axiom, distinct
    from the box-wise one Knows/Believes/Box/Obligatory use."""
    f = Announce(p, Diamond(q))
    expected = Implies(p, Diamond(And(p, q)))
    assert reduce_announcements(f) == expected


def test_reduce_classical_connectives_are_structural():
    """(ψ∘χ)^φ = ψ^φ ∘ χ^φ for ∘ ∈ {∧,∨,→,↔,⊕}, and (¬ψ)^φ = ¬ψ^φ."""
    body = And(Or(q, r), Xor(Iff(q, r), Not(q)))
    f = Announce(p, body)
    # Every leaf atom is unaffected by relativization (they're all atomic), so
    # the reduction should be exactly `p → body`, with the connective SHAPE of
    # body preserved unchanged (only wrapped, never restructured).
    assert reduce_announcements(f) == Implies(p, body)


def test_reduce_nested_announcement_in_post_condition_innermost_first():
    """([χ!]ψ)^φ reduces the INNER announcement first, then relativizes the
    (announcement-free) result — see the module docstring's proof.
    Hand derivation: [P!][Q!]R -> inner [Q!]R reduces to Q→R first; then the
    outer box axiom gives P → (Q→R)^P = P → (Q → R) (atoms unaffected).
    """
    f = Announce(p, Announce(q, r))
    assert reduce_announcements(f) == Implies(p, Implies(q, r))


def test_reduce_nested_announcement_in_announcement_position():
    """[[Q!]R!]P: the ANNOUNCED formula is itself reduced first ([Q!]R -> Q→R),
    then used as-is for phi: (Q→R) -> P."""
    f = Announce(Announce(q, r), p)
    assert reduce_announcements(f) == Implies(Implies(q, r), p)


def test_reduce_is_idempotent_on_announcement_free_formula():
    body = Implies(Knows(a, p), Box(Or(q, Not(r))))
    assert reduce_announcements(body) == body
    assert reduce_announcements(reduce_announcements(body)) == body


@pytest.mark.parametrize("temporal_op,arity", [
    (Always, 1), (Eventually, 1), (Next, 1),
    (Historically, 1), (Once, 1), (Previous, 1),
])
def test_reduce_rejects_unary_temporal_under_announcement(temporal_op, arity):
    """Ⓖ Ⓕ Ⓝ ⒣ ⒫ ⒴ under an announcement raise — restriction of a closure is not
    the closure of the restriction (see the module docstring)."""
    f = Announce(p, temporal_op(q))
    with pytest.raises(NotImplementedError, match="temporal operator"):
        reduce_announcements(f)


@pytest.mark.parametrize("temporal_op", [Until, Since])
def test_reduce_rejects_binary_temporal_under_announcement(temporal_op):
    """Ⓤ ⒮ under an announcement likewise raise."""
    f = Announce(p, temporal_op(q, r))
    with pytest.raises(NotImplementedError, match="temporal operator"):
        reduce_announcements(f)


@pytest.mark.parametrize("cf_op", [Would, Might])
def test_reduce_rejects_counterfactual_under_announcement(cf_op):
    f = Announce(p, cf_op(q, r))
    with pytest.raises(NotImplementedError, match="counterfactual"):
        reduce_announcements(f)


def test_reduce_rejects_nominal_under_announcement():
    f = Announce(p, Nominal("i"))
    with pytest.raises(NotImplementedError, match="hybrid-logic"):
        reduce_announcements(f)


def test_reduce_rejects_at_under_announcement():
    f = Announce(p, At(Nominal("i"), q))
    with pytest.raises(NotImplementedError, match="hybrid-logic"):
        reduce_announcements(f)


def test_reduce_rejects_quantifier_under_announcement():
    f = Announce(p, Quantifier("forall", Variable("x"), Atom("R", [Variable("x")])))
    with pytest.raises(NotImplementedError, match="quantifier"):
        reduce_announcements(f)


def test_reduce_rejects_temporal_buried_deep_under_announcement():
    """The forbidden construct need not be the IMMEDIATE child of the
    announcement — it is caught however deeply it is buried inside the
    relativized formula."""
    buried = Knows(a, And(q, Always(r)))
    f = Announce(p, buried)
    with pytest.raises(NotImplementedError, match="temporal operator"):
        reduce_announcements(f)


def test_reduce_does_not_reject_temporal_outside_announcement_scope():
    """A temporal operator that is NOT under any announcement passes through
    reduce_announcements untouched — only relativization is unsound, not the
    mere presence of a temporal operator anywhere in the formula."""
    f = Always(Announce(p, q))  # announcement is INSIDE the temporal scope, not
    # the reverse: Always itself is never relativized here.
    assert reduce_announcements(f) == Always(Implies(p, q))


# --------------------------------------------------------------------------- #
# Differential test: reduce_announcements vs. the satisfies_modal oracle
# --------------------------------------------------------------------------- #

_ATOMS = [p, q, r]
_AGENT = a

# Node types reduce_announcements can always eliminate soundly (excludes the
# rejected families: temporal, Would/Might, Nominal/At, quantifiers).
def _random_pal_formula(rng: random.Random, depth: int) -> Node:
    """Build a random formula of tree depth <= `depth` over the box/diamond
    modal family (Knows/Believes/Says/Wants/Box/Diamond/Obligatory/Permitted),
    classical connectives, and (nested) Announce/AnnounceDiamond."""
    if depth <= 0:
        return rng.choice(_ATOMS)
    choice = rng.randrange(17)
    if choice == 0:
        return rng.choice(_ATOMS)
    sub = lambda: _random_pal_formula(rng, depth - 1)
    if choice == 1:
        return Not(sub())
    if choice == 2:
        return And(sub(), sub())
    if choice == 3:
        return Or(sub(), sub())
    if choice == 4:
        return Implies(sub(), sub())
    if choice == 5:
        return Iff(sub(), sub())
    if choice == 6:
        return Xor(sub(), sub())
    if choice == 7:
        return Knows(_AGENT, sub())
    if choice == 8:
        return Believes(_AGENT, sub())
    if choice == 9:
        return Says(_AGENT, sub())
    if choice == 10:
        return Wants(_AGENT, sub())
    if choice == 11:
        return Box(sub())
    if choice == 12:
        return Diamond(sub())
    if choice == 13:
        return Obligatory(sub())
    if choice == 14:
        return Permitted(sub())
    if choice == 15:
        return Announce(sub(), sub())
    return AnnounceDiamond(sub(), sub())


def _kitchen_sink_relations(worlds, rng: random.Random, density: float):
    names = ("K:a", "B:a", "Say:a", "Want:a", "alethic", "deontic")
    return {name: {(x, y) for x in worlds for y in worlds if rng.random() < density}
            for name in names}


def _random_models(rng: random.Random):
    """Several small Kripke models (1, 2, and 3 worlds) carrying every relation
    the generator's operators read, with random edges/valuations."""
    models = []
    for n_worlds, density in ((1, 0.9), (2, 0.5), (3, 0.35)):
        worlds = list(range(n_worlds))
        relations = _kitchen_sink_relations(worlds, rng, density)
        valuation = {w: {atom.predicate for atom in _ATOMS if rng.random() < 0.5}
                    for w in worlds}
        models.append(KripkeModel(worlds, relations, valuation))
    return models


def test_reduce_announcements_differential():
    """reduce_announcements(f) is truth-equivalent to f, at EVERY world of
    EVERY model, for ~100 random PAL formulas (depth <= 3, 3 atoms, including
    nested announcements) — the formal-correctness anchor for this module.
    Also checks the reduced formula is genuinely announcement-free.
    """
    rng = random.Random(20260721)
    models = _random_models(rng)
    n_formulas = 100
    n_checks = 0
    for _ in range(n_formulas):
        f = _random_pal_formula(rng, depth=3)
        reduced = reduce_announcements(f)
        assert not any(isinstance(n, (Announce, AnnounceDiamond)) for n in reduced.walk())
        for model in models:
            for w in model.worlds:
                n_checks += 1
                assert satisfies_modal(f, model, w) == satisfies_modal(reduced, model, w), (
                    f"mismatch for {f.to_unicode_str()!r} at world {w} of {model!r}")
    assert n_checks >= 100 * 6  # 1+2+3 worlds per model, sanity on coverage


# --------------------------------------------------------------------------- #
# atp.modal_tableau: PAL formulas are DECIDED via the reduce_announcements pre-pass
# --------------------------------------------------------------------------- #

def test_has_modal_counts_announce():
    assert has_modal(Announce(p, q)) is True
    assert has_modal(AnnounceDiamond(p, q)) is True
    assert has_modal(Knows(a, Announce(p, q))) is True
    assert has_modal(And(p, q)) is False


def test_announcement_reduction_axiom_for_knows_is_k_valid():
    """[φ!]K_aψ ↔ (φ → K_a[φ!]ψ) is a K-validity — literally the Knows reduction
    axiom applied to itself: relativizing [φ!]K_aψ gives φ → K_a(φ→ψ^φ), and the
    RHS, after ITS OWN [φ!]ψ is reduced to φ→ψ^φ, is syntactically identical."""
    lhs = Announce(p, Knows(a, q))
    rhs = Implies(p, Knows(a, Announce(p, q)))
    assert is_modal_valid(Iff(lhs, rhs), frame="K") is True


def test_announcement_learning_is_not_valid_famous_non_theorem():
    """[φ!]K_aψ → K_a[φ!]ψ is NOT valid — "if after announcing φ, a would know
    ψ, then a already knows [φ!]ψ" fails: an agent can be BROUGHT to know ψ by
    the announcement without having, beforehand, known the CONDITIONAL fact
    "[φ!]ψ". This is the standard PAL non-theorem (successful formulas need not
    be known in advance). modal_decide must return "invalid" with a genuine,
    satisfies_modal-verified countermodel (not merely a bounded-search "unknown").
    """
    lhs = Announce(p, Knows(a, q))
    rhs = Knows(a, Announce(p, q))
    formula = Implies(lhs, rhs)
    assert is_modal_valid(formula, frame="K") is False
    verdict = modal_decide(formula, frame="K")
    assert verdict == "invalid"
    model = modal_countermodel(formula, frame="K")
    assert model is not None
    # modal_countermodel only ever returns a VERIFIED counter-model (satisfies_modal
    # confirms the formula is false at world 0) — re-check directly on the reduced
    # formula (what the tableau actually reasoned about) for good measure.
    assert satisfies_modal(reduce_announcements(formula), model, 0) is False


def test_moore_sentence_box_announcement_not_k_valid_via_tableau():
    """[φ!]K_a φ (φ = P ∧ ¬K_a P) is not K-valid — matches the hand-derived
    Kripke countermodel in test_moore_sentence_box_announcement_is_not_valid_hand_derived."""
    phi = And(p, Not(Knows(a, p)))
    formula = Announce(phi, Knows(a, phi))
    assert is_modal_valid(formula, frame="K") is False


def test_moore_sentence_diamond_announcement_is_satisfiable_via_tableau():
    """⟨φ!⟩⊤ (φ = P ∧ ¬K_a P) is satisfiable: its NEGATION is not valid, i.e.
    ¬⟨φ!⟩⊤ has a countermodel (equivalently, ⟨φ!⟩⊤ itself is not K-unsatisfiable)."""
    phi = And(p, Not(Knows(a, p)))
    top = Or(p, Not(p))
    formula = AnnounceDiamond(phi, top)
    assert is_modal_valid(Not(formula), frame="K") is False


def test_temporal_under_announcement_raises_through_tableau_entry_points():
    """A temporal operator under an announcement's scope raises pal.py's own
    clean error EVEN WHEN reached through modal_decide/is_modal_valid (the
    reduce_announcements pre-pass in atp.modal_tableau._run propagates it
    unchanged — this module adds no PAL-specific wrapping)."""
    f = Announce(p, Always(q))
    with pytest.raises(NotImplementedError, match="temporal operator"):
        is_modal_valid(f)
    with pytest.raises(NotImplementedError, match="temporal operator"):
        modal_decide(f)


# --------------------------------------------------------------------------- #
# Export route: exporters reject Announce directly; succeed after reduction
# --------------------------------------------------------------------------- #

def test_to_isabelle_modal_rejects_raw_announce():
    """The generic "unsupported node type" fallback in isabelle_modal.py fires
    for Announce, naming it (no bespoke PAL handling exists there — out of
    scope for this stream, per pal.py's module docstring)."""
    f = Announce(p, Knows(a, p))
    with pytest.raises(NotImplementedError, match="Announce"):
        to_isabelle_modal(f)


def test_to_isabelle_modal_rejects_raw_announce_diamond():
    f = AnnounceDiamond(p, q)
    with pytest.raises(NotImplementedError, match="AnnounceDiamond"):
        to_isabelle_modal(f)


def test_to_isabelle_modal_succeeds_after_reduce_announcements():
    """The sanctioned export route: reduce_announcements first, then export —
    for an epistemic PAL example ([P!]K_a P)."""
    f = Announce(p, Knows(a, p))
    reduced = reduce_announcements(f)
    theory = to_isabelle_modal(reduced)
    assert isinstance(theory, str) and "theory" in theory
    assert "lemma" in theory
