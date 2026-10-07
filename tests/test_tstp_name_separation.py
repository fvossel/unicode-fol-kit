r"""``to_tstp`` separates a predicate from a function/constant that render as one word.

``Node.to_tptp`` folds only the FIRST letter, so the class ``Agent`` (a predicate)
and the role function ``agent`` are both written ``agent``. A prover then sees one
symbol used as a predicate and as a function. The ``fof`` writer
(``atp._tptp_problem._separate_term_names``) renames the TERM side
(``agent_term``) and records the rename in the returned ``TptpNameMap``; ``to_tstp``
used to do that only when it was handed such a map, and wrote
``cnf(c1, plain, agent(agent(a)))`` when it was not. It now applies the same pass
over the literals of the whole derivation either way.

Every expected text below is derived by hand: a predicate ``Agent`` prints as
``agent``; a function or constant ``agent`` clashes with it and becomes
``agent_term``; ``a`` clashes with nothing; a ground literal and its negation
resolve to the empty clause.
"""

from unicode_logic_kit.atp._tptp_problem import generate_tptp_problem_with_mapping
from unicode_logic_kit.atp.resolution_check import (
    ResolutionDerivation, ResolutionStep, verify_resolution_proof,
)
from unicode_logic_kit.atp.tstp import (
    parse_tstp_derivation, reverse_map_derivation, to_tstp,
)
from unicode_logic_kit.fol.nodes import Atom, Constant, Function, Not

a = Constant("a")


def _refutation(literal):
    """{L}, {¬L} resolve to the empty clause."""
    steps = (
        ResolutionStep(1, frozenset({literal}), "input"),
        ResolutionStep(2, frozenset({Not(literal)}), "input"),
        ResolutionStep(3, frozenset(), "resolve", (1, 2)),
    )
    derivation = ResolutionDerivation((frozenset({literal}), frozenset({Not(literal)})), steps)
    assert verify_resolution_proof(derivation).ok
    return derivation


# Agent(agent(a)): the predicate Agent applied to the function agent.
_CLASH = Atom("Agent", [Function("agent", [a])])

_SEPARATED = (
    "cnf(c1, plain, agent(agent_term(a))).\n"
    "cnf(c2, plain, ~(agent(agent_term(a)))).\n"
    "cnf(c3, plain, $false, inference(resolution, [status(thm)], [c1, c2])).\n"
)


def test_a_map_less_call_separates_the_predicate_from_the_function():
    assert to_tstp(_refutation(_CLASH)) == _SEPARATED


def test_the_map_less_text_is_the_text_the_fof_writers_map_gives():
    derivation = _refutation(_CLASH)
    _, writer_map = generate_tptp_problem_with_mapping([_CLASH], Not(_CLASH))
    # The writer's map already carries the rename (original kit name -> token).
    assert writer_map.term["agent"] == "agent_term"
    assert to_tstp(derivation, name_map=writer_map) == _SEPARATED
    assert to_tstp(derivation) == to_tstp(derivation, name_map=writer_map)


def test_reverse_map_derivation_restores_the_original_names():
    from unicode_logic_kit.atp.tstp import _to_tstp_with_mapping

    text, final_map = _to_tstp_with_mapping(_refutation(_CLASH))
    assert text == _SEPARATED
    assert final_map.predicate == {"Agent": "Agent"}
    assert final_map.term == {"agent": "agent_term", "a": "a"}

    parsed = parse_tstp_derivation(text)
    # As the text says it: the function is called agent_term...
    assert parsed.steps[0].formula == Atom("Agent", [Function("agent_term", [a])])
    # ...and the final map hands the original name back.
    restored = reverse_map_derivation(parsed, final_map)
    assert restored.steps[0].formula == _CLASH
    assert restored.steps[1].formula == Not(_CLASH)
    assert [(s.rule, s.parents) for s in restored.steps] == [(s.rule, s.parents) for s in parsed.steps]


def test_a_constant_and_a_predicate_of_one_word_are_separated_too():
    clash = Atom("Agent", [Constant("agent")])           # class Agent, individual agent
    assert to_tstp(_refutation(clash)) == (
        "cnf(c1, plain, agent(agent_term)).\n"
        "cnf(c2, plain, ~(agent(agent_term))).\n"
        "cnf(c3, plain, $false, inference(resolution, [status(thm)], [c1, c2])).\n"
    )


def test_the_clash_is_found_across_clauses_not_only_inside_one():
    # The predicate Agent occurs only in c1 and c2's first literal, the function
    # agent only in Q(agent(a)): no single clause is a problem, the derivation is.
    q = Atom("Q", [Function("agent", [a])])
    agent_a = Atom("Agent", [a])
    steps = (
        ResolutionStep(1, frozenset({agent_a}), "input"),
        ResolutionStep(2, frozenset({Not(agent_a), q}), "input"),
        ResolutionStep(3, frozenset({Not(q)}), "input"),
        ResolutionStep(4, frozenset({q}), "resolve", (1, 2)),
        ResolutionStep(5, frozenset(), "resolve", (3, 4)),
    )
    derivation = ResolutionDerivation(
        (frozenset({agent_a}), frozenset({Not(agent_a), q}), frozenset({Not(q)})), steps)
    assert verify_resolution_proof(derivation).ok
    # Literals of c2 are in the writer's _lit_key order: "Q(agent(a))" sorts before
    # "¬Agent(a)" (U+0051 < U+00AC), the same order the existing golden tests derive.
    assert to_tstp(derivation) == (
        "cnf(c1, plain, agent(a)).\n"
        "cnf(c2, plain, q(agent_term(a)) | ~(agent(a))).\n"
        "cnf(c3, plain, ~(q(agent_term(a)))).\n"
        "cnf(c4, plain, q(agent_term(a)), inference(resolution, [status(thm)], [c1, c2])).\n"
        "cnf(c5, plain, $false, inference(resolution, [status(thm)], [c3, c4])).\n"
    )


def test_a_name_map_without_the_clash_is_extended_not_mutated():
    from unicode_logic_kit.atp.tstp import _to_tstp_with_mapping

    # A map built from an unrelated problem that has only the TERM agent.
    _, other = generate_tptp_problem_with_mapping(
        [Atom("P", [Constant("agent")])], Atom("P", [Constant("agent")]))
    assert other.term == {"agent": "agent"}
    text, final_map = _to_tstp_with_mapping(_refutation(_CLASH), name_map=other)
    assert text == _SEPARATED
    assert final_map.term["agent"] == "agent_term"
    assert other.term == {"agent": "agent"}               # the caller's map is not touched


def test_a_derivation_with_no_clash_is_written_exactly_as_before():
    plain = Atom("P", [Function("f", [a])])
    assert to_tstp(_refutation(plain)) == (
        "cnf(c1, plain, p(f(a))).\n"
        "cnf(c2, plain, ~(p(f(a)))).\n"
        "cnf(c3, plain, $false, inference(resolution, [status(thm)], [c1, c2])).\n"
    )
