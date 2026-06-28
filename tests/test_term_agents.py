"""Term agents: the epistemic/doxastic agent is a first-class term (Variable/Constant).

The motivating corpus case has a *quantified subject* — "every student who thinks that…"
— so the agent of ``K``/``B`` is a **bound variable**, e.g. ``∀x (Student(x) → K_x φ)``.
This requires the agent to be a substitutable term position (reached by free_variables /
substitution / β-reduction) rather than a baked-in relation-name suffix. These tests pin:

* the AST mechanics (substitution grounds the agent; binding removes it from free vars);
* the Kripke evaluator using PER-AGENT accessibility relations (so one agent can know
  what another does not);
* the first-order shallow embedding emitting an AGENT-INDEXED ternary ``Rk(agent, w, v)``;
* the parser convention (a free ``K_a`` is a named agent → Constant; a bound ``K_x`` stays
  a Variable);
* backward compatibility (a bare string agent is coerced to a Constant).
"""

import pytest

from unicode_fol_kit.fol.nodes import (
    Knows, Believes, Variable, Constant, Atom, And, Not, Implies, Quantifier, Node,
    free_variables, substitute,
)
from unicode_fol_kit.semantics.kripke import KripkeModel, satisfies_modal
from unicode_fol_kit.fol.qml import qml_is_valid, qml_translate
from unicode_fol_kit import MSFLParser

x = Variable("x")
A = lambda t: Atom("A", [t])
St = lambda t: Atom("Student", [t])
P = lambda t: Atom("P", [t])
ALL = lambda f: Quantifier("∀", x, f)
P0, Q0 = Atom("P0", []), Atom("Q0", [])


# ---------------------------------------------------------------------------
# AST mechanics: the agent is a structural child term
# ---------------------------------------------------------------------------

def test_string_agent_coerced_to_constant():
    k = Knows("alice", P0)
    assert isinstance(k.agent, Constant) and k.agent.name == "alice"
    assert Knows("alice", P0) == Knows(Constant("alice"), P0)


def test_variable_agent_is_free():
    k = Knows(x, A(x))
    assert Variable("x") in free_variables(k)


def test_enclosing_quantifier_binds_agent():
    f = ALL(Implies(St(x), Knows(x, P(x))))
    assert free_variables(f) == set()  # x (incl. the agent) is bound by ∀x


def test_substitution_grounds_agent():
    # x := bob reaches the agent position (a child term), giving a named agent.
    k = substitute(Knows(x, P(x)), x, Constant("bob"))
    assert isinstance(k.agent, Constant) and k.agent.name == "bob"
    assert k == Knows(Constant("bob"), P(Constant("bob")))


def test_dict_round_trip_with_term_agent():
    for agent in (Variable("x"), Constant("alice")):
        k = Knows(agent, A(agent))
        assert Node.from_dict(k.to_dict()) == k
    # a legacy string-agent dict still deserialises.
    legacy = {"_type": "Believes", "agent": "bob", "formula": Q0.to_dict()}
    assert Node.from_dict(legacy) == Believes("bob", Q0)


# ---------------------------------------------------------------------------
# Kripke evaluation with PER-AGENT accessibility relations
# ---------------------------------------------------------------------------

def test_kripke_quantified_agent_holds():
    # Every student knows P of themselves; both agents' relations stay where P holds.
    phi = ALL(Implies(St(x), Knows(x, P(x))))
    m = KripkeModel(
        worlds={0}, relations={"K:alice": {(0, 0)}, "K:bob": {(0, 0)}},
        valuation={0: {"Student(alice)", "Student(bob)", "P(alice)", "P(bob)"}},
        domain={"alice", "bob"})
    assert satisfies_modal(phi, m, 0) is True


def test_kripke_quantified_agent_fails_when_one_agent_ignorant():
    # bob's epistemic relation reaches a world where P(bob) is false → bob does NOT
    # know P(bob), so the universally-quantified knowledge claim fails. This only comes
    # out right because the relation is keyed PER AGENT.
    phi = ALL(Implies(St(x), Knows(x, P(x))))
    m = KripkeModel(
        worlds={0, 1}, relations={"K:alice": {(0, 0)}, "K:bob": {(0, 1)}},
        valuation={0: {"Student(alice)", "Student(bob)", "P(alice)", "P(bob)"}, 1: set()},
        domains={0: {"alice", "bob"}, 1: {"alice", "bob"}})
    assert satisfies_modal(phi, m, 0) is False


# ---------------------------------------------------------------------------
# First-order shallow embedding: agent-indexed ternary relation Rk(agent, w, v)
# ---------------------------------------------------------------------------

def test_fo_embedding_agent_indexed_relation():
    fo = qml_translate(Knows(x, P0), mode="constant")
    rk = [n for n in fo.walk() if isinstance(n, Atom) and n.predicate == "Rk"]
    assert rk and len(rk[0].args) == 3            # Rk(agent, w, v)
    assert rk[0].args[0] == x                     # the agent is a real first argument
    fo.to_z3()                                    # the translation is classical FOL


def test_fo_embedding_k_axiom_per_agent_valid():
    # The K distribution axiom holds for every agent: ∀x ((K_x P0 ∧ K_x(P0→Q0)) → K_x Q0).
    kax = ALL(Implies(And(Knows(x, P0), Knows(x, Implies(P0, Q0))), Knows(x, Q0)))
    assert qml_is_valid(kax, mode="constant", frame="K") is True


def test_fo_embedding_factivity_not_valid_in_K():
    # Epistemic relations carry no frame axioms by DEFAULT (plain K), so factivity
    # K_x P0 → P0 is NOT valid — knowledge is not forced reflexive. (Documents the default.)
    assert qml_is_valid(ALL(Implies(Knows(x, P0), P0)), mode="constant", frame="K") is False


def test_fo_embedding_epistemic_system_makes_knowledge_factive():
    # With an S5 (or T) epistemic SYSTEM, the agent-indexed relation is reflexive per
    # agent, so factivity ∀x (K_x P0 → P0) becomes valid — symmetric to the THF exporter.
    fact = ALL(Implies(Knows(x, P0), P0))
    assert qml_is_valid(fact, mode="constant", frame="K", systems={"epistemic": "S5"}) is True
    assert qml_is_valid(fact, mode="constant", frame="K", systems={"epistemic": "T"}) is True


def test_fo_embedding_doxastic_system_makes_belief_consistent():
    # Belief consistency (the D axiom) ∀x (B_x P0 → ¬B_x ¬P0) holds under a serial
    # doxastic system (KD45) but not under plain K.
    cons = ALL(Implies(Believes(x, P0), Not(Believes(x, Not(P0)))))
    assert qml_is_valid(cons, mode="constant", frame="K") is False
    assert qml_is_valid(cons, mode="constant", frame="K", systems={"doxastic": "KD45"}) is True


def test_fo_embedding_unknown_system_or_family_raises():
    f = ALL(Implies(Knows(x, P0), P0))
    with pytest.raises(ValueError):
        qml_is_valid(f, systems={"alethic": "S5"})        # not an agent family
    with pytest.raises(ValueError):
        qml_is_valid(f, systems={"epistemic": "Bogus"})   # not a frame system


# ---------------------------------------------------------------------------
# Parser convention: free K_a → Constant, bound K_x → Variable
# ---------------------------------------------------------------------------

@pytest.fixture(scope="module")
def mp():
    return MSFLParser(modal=True)


def test_parser_free_agent_is_constant(mp):
    k = mp.parse("K_a (P ∧ Q)")
    assert isinstance(k.agent, Constant) and k.agent.name == "a"


def test_parser_bound_agent_is_variable(mp):
    f = mp.parse("∀x (Student(x) → K_x Smart(x))")
    assert free_variables(f) == set()
    ks = [n for n in f.walk() if isinstance(n, Knows)][0]
    assert isinstance(ks.agent, Variable) and ks.agent.name == "x"


def test_parser_mixed_bound_and_free_agents(mp):
    g = mp.parse("∀x (K_x P(x) ∧ K_b Q)")
    by_name = {n.agent.name: n.agent for n in g.walk() if isinstance(n, Knows)}
    assert isinstance(by_name["x"], Variable)     # bound by ∀x
    assert isinstance(by_name["b"], Constant)     # free → named agent
