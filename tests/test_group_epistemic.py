"""Tests for the group-epistemic operators E_G/D_G/C_G (roadmap K3):

- ``fol._modal_nodes.EverybodyKnows`` / ``DistributedKnowledge`` / ``CommonKnowledge``
  (the AST nodes) and their ``E_{a,b,...}``/``D_{a,b,...}``/``C_{a,b,...}`` MSFL
  surface syntax (``fol.msflparser`` "modal" mode),
- their dispatch through ``semantics.kripke.satisfies_modal`` into
  ``semantics.action_models.everybody_knows`` /
  ``distributed_knowledge_holds`` / ``common_knowledge_holds``,
- their standard-translation (``fol.modal_translation.standard_translation``),
  and
- their handling by the labelled modal tableau (``atp.modal_tableau``).

Sections, matching the roadmap's test_oracle:

1. AST construction / coercion / refusals / to_dict roundtrip.
2. Parser: surface syntax, LALR/Earley agreement, and the parse ->
   to_unicode_str -> parse roundtrip.
3. (a)/(b) Direct semantics: singleton group == Knows, monotonicity.
4. (d) AST route vs. direct function-call route agree exactly.
5. (e) modal_to_fol soundness cross-check (Tarski Structure, mirroring
   tests/test_modal_translation.py's own pattern) plus the two refusals
   (E_∅, CommonKnowledge).
6. (f) Muddy Children acceptance scenario through the parsed syntax.
7. The labelled tableau (atp.modal_tableau): E_G/D_G positive-occurrence
   validities/countermodels under the default K frame AND under a non-trivial
   epistemic system (S5 factivity), and CommonKnowledge / negated D_G staying
   "unknown" (never a wrong verdict).
8. Safety net: every OTHER visitor this new AST reaches (to_z3/to_prover9/
   to_tptp, qml, the HOL exporters) refuses loudly by name rather than
   silently mishandling the new nodes.
"""

import random

import pytest

from unicode_fol_kit.fol.nodes import (
    Node, Atom, Constant, Variable, Not, And, Or, Implies,
    Knows,
)
from unicode_fol_kit.fol._modal_nodes import (
    EverybodyKnows, DistributedKnowledge, CommonKnowledge,
)
from unicode_fol_kit.fol.msflparser import MSFLParser
from unicode_fol_kit.fol.modal_translation import standard_translation
from unicode_fol_kit.semantics.kripke import KripkeModel, satisfies_modal
from unicode_fol_kit.semantics.action_models import (
    everybody_knows, distributed_knowledge_holds, common_knowledge_holds,
)
from unicode_fol_kit.semantics.dynamic_epistemic import announce
from unicode_fol_kit.semantics.tarski import Structure, satisfies
from unicode_fol_kit.atp.modal_tableau import (
    is_modal_valid, modal_decide, modal_countermodel, has_modal,
)

P = Atom("P", [])
Q = Atom("Q", [])
MODAL = MSFLParser(modal=True)


# ---------------------------------------------------------------------------
# 1. AST construction / coercion / refusals / to_dict roundtrip
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("cls", [EverybodyKnows, CommonKnowledge])
def test_group_node_coerces_bare_strings_to_constants(cls):
    node = cls(("a", "b"), P)
    assert node.group == (Constant("a"), Constant("b"))


def test_distributed_knowledge_refuses_empty_group_at_construction():
    with pytest.raises(ValueError, match="D_∅"):
        DistributedKnowledge((), P)


@pytest.mark.parametrize("cls,label", [
    (EverybodyKnows, "E"), (DistributedKnowledge, "D"), (CommonKnowledge, "C"),
])
def test_to_dict_from_dict_roundtrip(cls, label):
    node = cls(("a", "b", "c"), Implies(P, Q))
    d = node.to_dict()
    assert d["_type"] == cls.__name__
    assert len(d["group"]) == 3
    assert Node.from_dict(d) == node


@pytest.mark.parametrize("cls", [EverybodyKnows, DistributedKnowledge, CommonKnowledge])
def test_classical_export_is_refused(cls):
    group = ("a", "b") if cls is not DistributedKnowledge else ("a", "b")
    node = cls(group, P)
    for method in ("to_z3", "to_prover9", "to_tptp"):
        with pytest.raises(NotImplementedError):
            getattr(node, method)()


# ---------------------------------------------------------------------------
# 2. Parser: surface syntax, LALR/Earley agreement, roundtrip
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("text,cls,n_agents", [
    ("C_{a,b,c} P", CommonKnowledge, 3),
    ("D_{a,b} P", DistributedKnowledge, 2),
    ("E_{a,b,c} P", EverybodyKnows, 3),
    ("C_{a} P", CommonKnowledge, 1),          # singleton group
    ("E_{alice,bob} P", EverybodyKnows, 2),   # multi-letter (NAME-shaped) agents
])
def test_parses_to_expected_node_shape(text, cls, n_agents):
    node = MODAL.parse(text)
    assert isinstance(node, cls)
    assert len(node.group) == n_agents
    assert node.formula == P


def test_group_syntax_requires_at_least_one_agent():
    """C_{} is not valid surface syntax -- the grammar requires >=1 agent, so
    the parser can never hand an empty group to CommonKnowledge/EverybodyKnows
    either (even though their Python constructors would accept one)."""
    from unicode_fol_kit.fol.naming import NamingError, ParsingError
    with pytest.raises((NamingError, ParsingError)):
        MODAL.parse("C_{} P")


def test_round_trip_parse_to_unicode_str_parse():
    for text in ("C_{a,b,c} P", "D_{a,b} P", "E_{a,b,c} P",
                 "C_{a} (P → Q)", "D_{a,b} ¬P"):
        node = MODAL.parse(text)
        rendered = node.to_unicode_str()
        reparsed = MODAL.parse(rendered)
        assert reparsed == node, (text, rendered)


def test_group_agent_bound_by_enclosing_quantifier_stays_a_variable():
    """resolve_agent_variables: a group member sharing the name of an
    enclosing object quantifier's bound variable stays a Variable (reachable
    for substitution when the quantifier is instantiated); a free one is
    demoted to a Constant -- mirrors Knows'/Believes' own contract."""
    node = MODAL.parse("∀x (Student(x) → E_{x,b} Q)")
    group = node.formula.right.group
    assert group[0] == Variable("x")
    assert group[1] == Constant("b")


def test_existing_syntax_unaffected_by_the_new_group_terminals():
    """The new C_{/D_{/E_{ terminals cannot change how set-builder braces,
    Knows/Believes agent prefixes, or a plain 'C_...' predicate name parse."""
    assert MODAL.parse("K_alice P") == Knows("alice", P)
    card = MODAL.parse("|{x : P(x)}| = 3")
    assert card.to_unicode_str() == "|{x : P(x)}| = 3"
    # A predicate literally named "C_alpha" (an ordinary uppercase-first
    # identifier with an underscore continuation) still lexes as PREDICATE,
    # not as the start of a CommonKnowledge group.
    atom = MODAL.parse("C_alpha(x)")
    assert atom.predicate == "C_alpha"


def test_lalr_and_earley_agree_on_group_syntax():
    """The soundness contract test_modal_lalr_fallback.py proves at scale:
    spot-checked here directly against the raw LALR/Earley Lark parsers for
    the exact new syntax (see that file for the seeded fuzz corpus this
    syntax is now also woven into)."""
    from unicode_fol_kit.fol._fol_nodes import build_grammar
    from unicode_fol_kit.fol.msflparser import (
        _allow_single_letter_function_calls, _GRAMMARS_DIR, _REGISTRY_MODE,
    )
    from lark import Lark

    grammar = _allow_single_letter_function_calls(build_grammar(_REGISTRY_MODE["modal"]))
    earley = Lark(grammar, parser="earley", import_paths=[str(_GRAMMARS_DIR)],
                  propagate_positions=True)
    for text in ("C_{a,b,c} P", "D_{a,b} P", "E_{alice,bob,carol} P",
                 "¬ C_{a,b} P ∧ D_{a} Q", "C_{a}(P → Q)"):
        lalr_tree = MODAL.parser.parse(text)
        earley_tree = earley.parse(text)
        assert lalr_tree == earley_tree, text


# ---------------------------------------------------------------------------
# 3. (a)/(b) Direct semantics on small hand-built frames
# ---------------------------------------------------------------------------

def _small_frame():
    """3 worlds; K:a and K:b disagree from 0 (a sees {0,1}, b sees {0,2}) --
    the SAME frame test_action_models.py's union-vs-intersection contrast
    test uses, reused here for the AST-vs-function differential below."""
    return KripkeModel(
        worlds={0, 1, 2},
        relations={
            "K:a": {(0, 0), (0, 1), (1, 0), (1, 1)},
            "K:b": {(0, 0), (0, 2), (2, 0), (2, 2)},
        },
        valuation={0: {"P"}, 1: {"P"}, 2: set()},
    )


def test_distributed_knowledge_ast_singleton_group_equals_knows():
    """(a) D_{a} P reduces to plain K_a P -- direct equality against Knows/
    satisfies_modal on the same model, through the AST route this time."""
    model = _small_frame()
    node = DistributedKnowledge(("a",), P)
    for w in model.worlds:
        assert satisfies_modal(node, model, w) == satisfies_modal(Knows("a", P), model, w)


def test_distributed_knowledge_ast_monotone_in_group_size():
    """(b) brute-forced on small hand-built frames: D_G P true implies
    D_{G+b} P true for an added agent b, through the AST route."""
    rng = random.Random(20260919)
    agents = ["a", "b", "c"]
    for _ in range(50):
        n_worlds = rng.randint(1, 4)
        worlds = list(range(n_worlds))
        relations = {
            f"K:{ag}": {(x, y) for x in worlds for y in worlds if rng.random() < 0.5}
            for ag in agents
        }
        valuation = {w: ({"P"} if rng.random() < 0.5 else set()) for w in worlds}
        model = KripkeModel(worlds=worlds, relations=relations, valuation=valuation)
        for group in (("a",), ("b",), ("a", "b")):
            extra = next(a for a in agents if a not in group)
            bigger = tuple(sorted(group + (extra,)))
            for w in worlds:
                if satisfies_modal(DistributedKnowledge(group, P), model, w):
                    assert satisfies_modal(DistributedKnowledge(bigger, P), model, w) is True


# ---------------------------------------------------------------------------
# 4. (d) AST route vs. direct function-call route agree exactly
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("text,cls,fn", [
    ("C_{a,b} P", CommonKnowledge, common_knowledge_holds),
    ("D_{a,b} P", DistributedKnowledge, distributed_knowledge_holds),
    ("E_{a,b} P", EverybodyKnows, everybody_knows),
])
def test_ast_route_agrees_with_direct_function_call(text, cls, fn):
    """Parse the surface syntax, run satisfies_modal, and differentially test
    against calling the semantics.action_models function directly -- mirrors
    the Announce-vs-reduce_announcements differential pattern documented in
    dynamic_epistemic.py."""
    model = _small_frame()
    node = MODAL.parse(text)
    assert isinstance(node, cls)
    agents = [a.name for a in node.group]
    for w in model.worlds:
        assert satisfies_modal(node, model, w) == fn(model, w, agents, P)


# ---------------------------------------------------------------------------
# 5. (e) modal_to_fol soundness cross-check + the two refusals
# ---------------------------------------------------------------------------

_R_KNOWS_PREFIX = "Rk_"  # must match fol.modal_translation's own naming


def _structure_from_kripke(model, atom_names):
    """A first-order Structure matching a Kripke model's "K:"+agent relations
    (as Rk_<agent> binary predicates) and propositional atoms (as unary
    predicates) -- the SAME construction tests/test_modal_translation.py's
    own _structure_from_kripke uses, kept local here so this file stays
    self-contained."""
    predicates = {}
    for rel_name, edges in model.relations.items():
        if rel_name.startswith("K:"):
            predicates[(_R_KNOWS_PREFIX + rel_name[2:], 2)] = set(edges)
    for name in atom_names:
        ext = {(w,) for w in model.worlds if name in model.atoms_true_at(w)}
        predicates[(name, 1)] = ext
    return Structure(domain=set(model.worlds), predicates=predicates)


def test_everybody_knows_translation_soundness_cross_check():
    """(e) standard_translation(EverybodyKnows) checked against
    satisfies_modal, via the Tarski finite-model evaluator, exactly as
    test_modal_translation.py's own soundness cross-check does for Knows
    (several hand-built models, every world)."""
    rng = random.Random(20260920)
    agents = ["a", "b", "c"]
    formulas = [
        EverybodyKnows(("a", "b"), P),
        EverybodyKnows(("a", "b", "c"), Implies(P, Q)),
        EverybodyKnows(("a",), P),
        Implies(EverybodyKnows(("a", "b"), P), Q),
    ]
    for _ in range(15):
        n_worlds = rng.randint(1, 4)
        worlds = list(range(n_worlds))
        relations = {
            f"K:{ag}": {(x, y) for x in worlds for y in worlds if rng.random() < 0.5}
            for ag in agents
        }
        valuation = {w: ({a for a in ("P", "Q") if rng.random() < 0.5}) for w in worlds}
        model = KripkeModel(worlds=worlds, relations=relations, valuation=valuation)
        structure = _structure_from_kripke(model, ["P", "Q"])
        for formula in formulas:
            translated = standard_translation(formula, "w")
            for w in worlds:
                kripke_truth = satisfies_modal(formula, model, w)
                tarski_truth = satisfies(translated, structure, {"w": w})
                assert kripke_truth == tarski_truth, (
                    f"mismatch for {formula.to_unicode_str()} at {w}: "
                    f"kripke={kripke_truth} tarski={tarski_truth}"
                )


def test_distributed_knowledge_translation_soundness_cross_check():
    """(e) standard_translation(DistributedKnowledge), same method."""
    rng = random.Random(20260921)
    agents = ["a", "b", "c"]
    formulas = [
        DistributedKnowledge(("a", "b"), P),
        DistributedKnowledge(("a", "b", "c"), Implies(P, Q)),
        DistributedKnowledge(("a",), P),
        Implies(DistributedKnowledge(("a", "b"), P), Knows("a", P)),
    ]
    for _ in range(15):
        n_worlds = rng.randint(1, 4)
        worlds = list(range(n_worlds))
        relations = {
            f"K:{ag}": {(x, y) for x in worlds for y in worlds if rng.random() < 0.5}
            for ag in agents
        }
        valuation = {w: ({a for a in ("P", "Q") if rng.random() < 0.5}) for w in worlds}
        model = KripkeModel(worlds=worlds, relations=relations, valuation=valuation)
        structure = _structure_from_kripke(model, ["P", "Q"])
        for formula in formulas:
            translated = standard_translation(formula, "w")
            for w in worlds:
                kripke_truth = satisfies_modal(formula, model, w)
                tarski_truth = satisfies(translated, structure, {"w": w})
                assert kripke_truth == tarski_truth, (
                    f"mismatch for {formula.to_unicode_str()} at {w}: "
                    f"kripke={kripke_truth} tarski={tarski_truth}"
                )


def test_common_knowledge_translation_is_refused():
    """CommonKnowledge.to_fol is NOT first-order definable -- refused with the
    same 'closure' framing already used for Until (tested only for the
    refusal, matching the existing Until rejection test)."""
    with pytest.raises(NotImplementedError, match="not first-order definable"):
        standard_translation(CommonKnowledge(("a", "b"), P))


def test_everybody_knows_empty_group_translation_is_refused():
    with pytest.raises(NotImplementedError, match="E_∅"):
        standard_translation(EverybodyKnows((), P))


# ---------------------------------------------------------------------------
# 6. (f) Muddy Children acceptance scenario through the parsed syntax
# ---------------------------------------------------------------------------

import itertools as _itertools  # local, keeps this file's imports self-explaining per section

_CHILDREN = ["anne", "bert", "carla"]
_M_ANNE = Atom("Muddy", [Constant("anne")])
_M_BERT = Atom("Muddy", [Constant("bert")])
_M_CARLA = Atom("Muddy", [Constant("carla")])
_ACTUAL_WORLD = (True, True, False)
_AT_LEAST_ONE_MUDDY = Or(Or(_M_ANNE, _M_BERT), _M_CARLA)


def _build_muddy_children_model():
    """8 worlds = every muddiness triple; each child's K: relation agrees with
    w on the OTHER TWO children's muddiness (you see everyone but yourself) --
    identical construction to test_action_models.py's own fixture (see that
    file's docstring for the reflexive-edges rationale), reproduced here
    self-contained so this acceptance test does not reach into another test
    module's private helpers."""
    worlds = list(_itertools.product([True, False], repeat=3))

    def edges_for(index):
        return {
            (w, w2) for w in worlds for w2 in worlds
            if all(w[i] == w2[i] for i in range(3) if i != index)
        }

    relations = {f"K:{name}": edges_for(i) for i, name in enumerate(_CHILDREN)}
    valuation = {}
    for w in worlds:
        atoms = set()
        if w[0]:
            atoms.add(_M_ANNE.to_unicode_str())
        if w[1]:
            atoms.add(_M_BERT.to_unicode_str())
        if w[2]:
            atoms.add(_M_CARLA.to_unicode_str())
        valuation[w] = atoms
    return KripkeModel(worlds=worlds, relations=relations, valuation=valuation)


def test_muddy_children_common_knowledge_via_parsed_syntax_matches_raw_route():
    """(f) 'at least one muddy' becomes common knowledge after the round-0
    public announcement (the existing hand-derived 8-world -> 7-world-
    surviving trace, see test_action_models.py's own version of this test),
    now checked by PARSING 'C_{anne,bert,carla} (Muddy(anne) ∨ Muddy(bert)
    ∨ Muddy(carla))' instead of calling common_knowledge_holds directly --
    and cross-checked to still agree with the raw function-call route on the
    SAME restricted model."""
    text = ("C_{anne,bert,carla} "
            "(Muddy(anne) ∨ Muddy(bert) ∨ Muddy(carla))")
    node = MODAL.parse(text)
    assert isinstance(node, CommonKnowledge)
    assert node.formula == _AT_LEAST_ONE_MUDDY

    model = _build_muddy_children_model()
    round0 = announce(model, _AT_LEAST_ONE_MUDDY)

    parsed_after = satisfies_modal(node, round0, _ACTUAL_WORLD)
    raw_after = common_knowledge_holds(round0, _ACTUAL_WORLD, _CHILDREN, _AT_LEAST_ONE_MUDDY)
    assert parsed_after == raw_after is True

    parsed_before = satisfies_modal(node, model, _ACTUAL_WORLD)
    raw_before = common_knowledge_holds(model, _ACTUAL_WORLD, _CHILDREN, _AT_LEAST_ONE_MUDDY)
    assert parsed_before == raw_before is False


def test_muddy_children_everybody_knows_via_parsed_syntax():
    """The same model's round-0-surviving worlds: E_{anne,bert,carla} 'at
    least one muddy' also holds there (one step already suffices, since
    every immediate successor of the actual world also satisfies it) --
    cross-checked against everybody_knows directly."""
    text = ("E_{anne,bert,carla} "
            "(Muddy(anne) ∨ Muddy(bert) ∨ Muddy(carla))")
    node = MODAL.parse(text)
    model = _build_muddy_children_model()
    round0 = announce(model, _AT_LEAST_ONE_MUDDY)
    assert (satisfies_modal(node, round0, _ACTUAL_WORLD)
            == everybody_knows(round0, _ACTUAL_WORLD, _CHILDREN, _AT_LEAST_ONE_MUDDY)
            is True)


# ---------------------------------------------------------------------------
# 7. The labelled modal tableau (atp.modal_tableau)
# ---------------------------------------------------------------------------

def test_has_modal_recognises_the_group_operators():
    for node in (EverybodyKnows(("a",), P), DistributedKnowledge(("a",), P),
                 CommonKnowledge(("a",), P)):
        assert has_modal(node) is True


def test_everybody_knows_implies_single_agent_knowledge_is_valid():
    """E_G P -> K_a P (a in G) is a genuine K-validity: alpha-reduced into a
    per-agent conjunction of boxes, so the ordinary K-tableau rules decide it
    outright (no closure/induction rule needed -- see the module comment)."""
    f = Implies(EverybodyKnows(("a", "b"), P), Knows("a", P))
    assert is_modal_valid(f) is True
    assert modal_decide(f) == "valid"


def test_distributed_knowledge_does_not_imply_single_agent_knowledge():
    """The WRONG-direction implication D_G P -> K_a P is genuinely INVALID
    (D_G is the logically weakest of the group notions, entailed BY K_a, not
    entailing it -- see action_models.distributed_knowledge_holds's
    docstring) -- decided outright with a VERIFIED countermodel, since both
    occurrences here (D_G positive, K_a negative) are within the tableau's
    documented scope."""
    f = Implies(DistributedKnowledge(("a", "b"), P), Knows("a", P))
    assert is_modal_valid(f) is False
    assert modal_decide(f) == "invalid"
    cm = modal_countermodel(f)
    assert cm is not None
    # cross-check the returned countermodel actually falsifies f via satisfies_modal
    assert satisfies_modal(f, cm, 0) is False


def test_distributed_knowledge_factivity_under_s5_is_valid():
    """D_G P -> P is a genuine S5-validity even when every agent in G is
    mentioned NOWHERE ELSE in the formula: intersecting reflexive relations
    stays reflexive (if (w,w) in every R_a, then (w,w) is in their
    intersection too), so S5's T axiom lifts from each K_a straight to D_G.
    HAND-CHECKED: for a SINGLETON group {a}, D_{a} P is semantically
    identical to K_a P (see the AST-singleton-equals-Knows tests above), and
    Knows(a,P) -> P under S5 is the textbook T axiom -- asserted below as the
    control, and again for a 2-agent group.

    Regression coverage for a tableau bug: `_close_distributed` used to
    recompute a D_G box's synthetic intersection relation from its
    constituent "K:"+agent relations WITHOUT ever registering those
    constituents as 'live' for `_frame_close` (atp/modal_tableau.py) -- so an
    agent mentioned only inside a D_G box never had the caller's requested
    epistemic frame conditions (S5 reflexivity here) applied to its own
    relation, and this formula was wrongly decided 'invalid'."""
    control = Implies(Knows("a", P), P)
    assert is_modal_valid(control, systems={"epistemic": "S5"}) is True

    singleton = Implies(DistributedKnowledge(("a",), P), P)
    assert is_modal_valid(singleton, systems={"epistemic": "S5"}) is True
    assert modal_decide(singleton, systems={"epistemic": "S5"}) == "valid"

    group = Implies(DistributedKnowledge(("a", "b"), P), P)
    assert is_modal_valid(group, systems={"epistemic": "S5"}) is True
    assert modal_decide(group, systems={"epistemic": "S5"}) == "valid"

    # Sanity: the SAME singleton formula is genuinely NOT valid without
    # factivity (plain K) -- confirms the S5 result above comes from the
    # requested frame conditions actually reaching "a"'s relation, not from a
    # bug that makes D_G vacuously true regardless of the requested frame.
    assert is_modal_valid(singleton, systems={"epistemic": "K"}) is False
    cm = modal_countermodel(singleton, systems={"epistemic": "K"})
    assert cm is not None
    assert satisfies_modal(singleton, cm, 0) is False


def test_distributed_knowledge_still_does_not_imply_single_agent_knowledge_under_s5():
    """Confirms the S5 fix above does not overshoot: pooling agents'
    relations via INTERSECTION only ever shrinks what D_G quantifies over
    relative to any single K_a (see action_models.distributed_knowledge_holds's
    docstring), so D_G P -> K_a P stays genuinely INVALID even once every
    constituent relation is S5-reflexive -- and the returned countermodel
    must itself respect S5 (every "K:"+agent relation reflexive at every
    world), or it would not be a legitimate S5 counterexample."""
    f = Implies(DistributedKnowledge(("a", "b"), P), Knows("a", P))
    assert is_modal_valid(f, systems={"epistemic": "S5"}) is False
    assert modal_decide(f, systems={"epistemic": "S5"}) == "invalid"
    cm = modal_countermodel(f, systems={"epistemic": "S5"})
    assert cm is not None
    assert satisfies_modal(f, cm, 0) is False
    for w in cm.worlds:
        assert (w, w) in cm.relations.get("K:a", set())
        assert (w, w) in cm.relations.get("K:b", set())


def test_common_knowledge_in_the_tableau_is_honestly_unknown_not_wrong():
    """CommonKnowledge has no tableau rule (needs an induction/fixpoint rule
    this labelled tableau does not have); modal_decide must say 'unknown',
    NEVER a wrong 'valid'/'invalid' verdict, for a formula whose truth
    actually depends on the closure."""
    # C_{a} P -> P is valid on a REFLEXIVE frame but not decidable here without
    # frame axioms this tableau does not assert for group relations, so the
    # honest answer is "unknown", not a guess either way.
    f = Implies(CommonKnowledge(("a", "b"), P), P)
    assert modal_decide(f) == "unknown"
    assert is_modal_valid(f) is False  # "not proven valid", not "proven invalid"


def test_negated_distributed_knowledge_is_honestly_unknown():
    """The one direction this tableau's D_G support does NOT cover (see the
    module comment above _distributed_relname): a formula needing D_G to be
    REFUTED never wrongly closes or wrongly opens -- it stays 'unknown'."""
    f = Implies(Knows("a", P), DistributedKnowledge(("a", "b"), P))  # true in fact, but not provable here
    assert modal_decide(f) == "unknown"
    assert modal_countermodel(f) is None  # and it never invents a bogus countermodel either


# ---------------------------------------------------------------------------
# 8. Safety net: every OTHER visitor refuses loudly by name
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("cls", [EverybodyKnows, DistributedKnowledge, CommonKnowledge])
def test_qml_refuses_the_group_operators_by_name(cls):
    from unicode_fol_kit.fol.qml import qml_translate
    with pytest.raises(NotImplementedError, match=cls.__name__):
        qml_translate(cls(("a", "b"), P))


@pytest.mark.parametrize("cls", [EverybodyKnows, DistributedKnowledge, CommonKnowledge])
def test_hol_exporters_refuse_the_group_operators_by_name(cls):
    from unicode_fol_kit.hol.isabelle_modal import to_isabelle_modal
    from unicode_fol_kit.hol.thf_modal import to_thf_modal_full
    for fn in (to_isabelle_modal, to_thf_modal_full):
        with pytest.raises(NotImplementedError, match=cls.__name__):
            fn(cls(("a", "b"), P))


@pytest.mark.parametrize("cls", [EverybodyKnows, DistributedKnowledge, CommonKnowledge])
@pytest.mark.parametrize("wrap", [
    pytest.param(lambda g: Not(g), id="Not"),
    pytest.param(lambda g: And(g, Q), id="And"),
    pytest.param(lambda g: Or(Q, g), id="Or"),
    pytest.param(lambda g: Implies(g, Q), id="Implies"),
    pytest.param(lambda g: Knows("a", g), id="Knows"),
])
def test_nested_group_operator_renders_and_round_trips(cls, wrap):
    """A group operator under another operator renders through the shared
    renderer (it used to raise TypeError there) and parses back to the same
    tree; its prefix binds like Knows, so ``E_{a,b} P ∧ Q`` is a conjunction."""
    outer = wrap(cls(("a", "b"), P))
    text = outer.to_unicode_str()
    assert MODAL.parse(text) == outer
    assert r"_{\{a, b\}}" in outer.to_latex()


def test_group_prefix_scope_is_the_next_prefix_level_operand():
    # Hand-checked: the prefix takes the atom, not the conjunction.
    conj = MODAL.parse("E_{a,b} P ∧ Q")
    assert conj == And(EverybodyKnows(("a", "b"), P), Q)
    scoped = MODAL.parse("E_{a,b} (P ∧ Q)")
    assert scoped == EverybodyKnows(("a", "b"), And(P, Q))
    assert scoped.to_unicode_str() == "E_{a,b} (P ∧ Q)"
    assert conj.to_unicode_str() == "E_{a,b} P ∧ Q"


# ---------------------------------------------------------------------------
# 9. atp.fitch and atp.kripke_enum keep their OWN scan of "which relation
#    families does this formula use"; both must count the members of a group
#    operator, or the agent's relation silently goes missing.
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("cls", [EverybodyKnows, DistributedKnowledge])
def test_fitch_factivity_reit_through_group_operator(cls):
    """HAND-CHECKED: from ``cls({a}, P)`` (a singleton group, semantically
    Knows(a, P)) the step ``P`` by Reit is a valid S5 consequence (axiom T for
    the epistemic relation). Before the fix fitch added no frame axioms for
    an agent that occurs only inside a group operator and rejected the step."""
    from unicode_fol_kit.atp.fitch import Proof, premise, line, verify_proof

    a = Constant("a")
    control = Proof(premises=(premise(1, Knows(a, P)),),
                    steps=(line(2, P, "Reit", 1),), logic="s5")
    assert verify_proof(control).ok is True
    grouped = Proof(premises=(premise(1, cls((a,), P)),),
                    steps=(line(2, P, "Reit", 1),), logic="s5")
    assert verify_proof(grouped).ok is True


def test_kripke_enum_finds_countermodel_for_group_operator():
    """HAND-CHECKED: E_{a}P is not K-valid (K:a={(0,1)}, P false at world 1)."""
    from unicode_fol_kit.atp.kripke_enum import modal_enum_search

    a = Constant("a")
    control = modal_enum_search(Knows(a, P), frame="K", max_worlds=2)
    assert control.model is not None
    grouped = modal_enum_search(EverybodyKnows((a,), P), frame="K", max_worlds=2)
    assert grouped.model is not None


@pytest.mark.parametrize("cls", [EverybodyKnows, DistributedKnowledge, CommonKnowledge])
def test_kripke_enum_applies_the_epistemic_system_to_group_members(cls):
    """Regression for an UNSOUND refutation: with the member's relation left
    out of the search, every candidate had an empty "K:a" -- not an S5 frame
    -- and the valid ``cls({a}, P) → P`` got a "countermodel", which
    KripkeEnumBackend reports as REFUTED. Under S5 (reflexive) it is valid
    for all three operators; under K it is invalid for E and D and, since C_G
    reads the REFLEXIVE-transitive closure, valid for C."""
    from unicode_fol_kit.atp.kripke_enum import modal_enum_search
    from unicode_fol_kit.atp.protocol import get_backend, REFUTED

    a = Constant("a")
    formula = Implies(cls((a,), P), P)
    s5 = modal_enum_search(formula, frame="K", systems={"epistemic": "S5"}, max_worlds=3)
    assert s5.model is None
    verdict = get_backend("kripke-enum").decide(formula, systems={"epistemic": "S5"})
    assert verdict.status != REFUTED
    k = modal_enum_search(formula, frame="K", max_worlds=2)
    assert (k.model is not None) == (cls is not CommonKnowledge)
