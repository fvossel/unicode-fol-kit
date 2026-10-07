"""A predicate and a function/constant that fold to one TPTP name are written apart.

The kit writes a predicate Capitalised (``Agent``) and a function or constant
lower-case (``agent``, ``car``); ``Node.to_tptp`` lower-cases only the FIRST
character of either, so the class ``Agent`` and the role function ``agent`` both
become ``agent``. The ``fof`` writer used to argue this was harmless because a
reader resolves a bare identifier by its syntactic position. Real provers do
not: measured on this machine, Vampire 5.0.1 answers ``Non-boolean term
agent(X0) of sort $i is used in a formula context`` and E 3.5.1 stops with a
parse error, so ``agent(agent(X))`` never reached an SZS status; the kit's own
backends then reported a problem the prover refused to read as "undecided".
The TF0 writer was worse, declaring ``agent`` at two types.

Decision implemented here (D1-D4 of the work order):

* D1 — two LEGAL names of ONE kind that fold together (``car``/``Car``) stay
  REFUSED, by name. The cross-kind rename must never dodge that refusal.
* D2 — a function/constant whose rendered name equals a predicate's is renamed
  to ``<name>_term`` (numeric suffix if taken) by the WRITERS, whatever the
  arities, and the rename is recorded in the returned ``TptpNameMap``.
* D3 — single-formula ``to_tptp`` is not this module's business.
* D4 — the asymmetry is documented (docs/guide/classical-reasoning.md).

Every expected string below is derived by hand from those rules (the semantic
clause is stated in each docstring), never copied from what the code printed.
Two independent oracles are used on top of the strings: the problem text is READ
BACK with the kit's own TPTP reader and mapped through ``apply_reverse_tptp``
(it must equal the sources), and real provers' verdicts through the kit's
backends must equal z3's verdict on the nodes.
"""

import os
import random
import shutil
import subprocess
import sys

import pytest

from unicode_logic_kit.atp import (
    TptpNameMap, apply_reverse_tptp, generate_tff_arith_problem,
    generate_tff_problem, generate_tff_problem_with_mapping,
    generate_tptp_problem, generate_tptp_problem_with_mapping, to_tptp_ncl,
)
from unicode_logic_kit.atp._ascii_names import reverse_map_text
from unicode_logic_kit.atp._tptp_problem import _separate_term_names
from unicode_logic_kit.atp.tptp_tff import formula_to_tff
from unicode_logic_kit.atp.z3_models import is_valid
from unicode_logic_kit.fol.nodes import (
    And, Atom, Box, Constant, Function, Implies, Not, Quantifier,
    SortedConstant, SortedQuantifier, Variable,
)
from unicode_logic_kit.fol.tptp_input import parse_tff_problem, parse_tptp

X = Variable("x")


def _all(var, body):
    return Quantifier("∀", var, body)


def _ex(var, body):
    return Quantifier("∃", var, body)


# The reporter's shape: the class Agent and the role function agent.
AGENT_PREMISE = _all(X, Atom("Agent", [Function("agent", [X])]))
AGENT_THEOREM = _ex(X, Atom("Agent", [X]))          # follows: take any individual
AGENT_NON_THEOREM = _all(X, Atom("Agent", [X]))     # does not: agent need not be onto


# =============================================================================
# fof: hand-derived text and map
# =============================================================================

def test_fof_function_clash_renames_the_term_side_and_records_it():
    """Predicate ``Agent`` renders ``agent``; function ``agent`` renders
    ``agent``: one name in two kinds, so the function (the term side) becomes
    ``agent_term`` and the predicate keeps its natural name. The map records
    ``agent -> agent_term`` under ``term`` and ``Agent -> Agent`` under
    ``predicate``."""
    text, name_map = generate_tptp_problem_with_mapping([AGENT_PREMISE], AGENT_THEOREM)
    assert text == (
        "fof(premise_1, axiom, (![X]: agent(agent_term(X)))).\n"
        "fof(goal, conjecture, (?[X]: agent(X))).\n")
    assert name_map == TptpNameMap(predicate={"Agent": "Agent"},
                                   term={"agent": "agent_term"})
    assert generate_tptp_problem([AGENT_PREMISE], AGENT_THEOREM) == text


def test_fof_constant_clash_renames_the_constant():
    """Predicate ``Car`` and constant ``car`` both render ``car``."""
    atom = Atom("Car", [Constant("car")])
    text, name_map = generate_tptp_problem_with_mapping([atom], atom)
    assert text == ("fof(premise_1, axiom, car(car_term)).\n"
                    "fof(goal, conjecture, car(car_term)).\n")
    assert name_map.term == {"car": "car_term"}


def test_fof_clash_is_independent_of_arity():
    """A propositional letter ``P`` (0-ary predicate, renders ``p``) and a
    constant ``p`` clash although neither takes arguments."""
    formula = And(Atom("P", []), Atom("Q", [Constant("p")]))
    text, name_map = generate_tptp_problem_with_mapping([formula], formula)
    assert text == ("fof(premise_1, axiom, (p & q(p_term))).\n"
                    "fof(goal, conjecture, (p & q(p_term))).\n")
    assert name_map.term == {"p": "p_term"}


def test_fof_replacement_is_decollided_against_every_name_in_the_problem():
    """Terms: ``agent`` and ``agent_term``; predicate ``Agent``. ``agent``
    clashes, its first candidate ``agent_term`` is taken by the other term, so
    it becomes ``agent_term2``; ``agent_term`` itself is untouched."""
    atom = Atom("Agent", [Function("agent", [Constant("agent_term")])])
    text, name_map = generate_tptp_problem_with_mapping([atom], atom)
    assert text == ("fof(premise_1, axiom, agent(agent_term2(agent_term))).\n"
                    "fof(goal, conjecture, agent(agent_term2(agent_term))).\n")
    assert name_map.term == {"agent": "agent_term2", "agent_term": "agent_term"}


def test_fof_replacement_also_avoids_predicate_names():
    """Predicate ``Agent_term`` renders ``agent_term``: the first candidate for
    the clashing constant ``agent`` is therefore taken by a PREDICATE, and the
    constant becomes ``agent_term2``."""
    formula = And(Atom("Agent", [Constant("agent")]), Atom("Agent_term", [Constant("agent")]))
    text, _ = generate_tptp_problem_with_mapping([formula], formula)
    assert text == (
        "fof(premise_1, axiom, (agent(agent_term2) & agent_term(agent_term2))).\n"
        "fof(goal, conjecture, (agent(agent_term2) & agent_term(agent_term2))).\n")


def test_fof_without_a_clash_is_untouched():
    """No predicate shares a rendered name with a term: the text is exactly
    what ``Node.to_tptp`` writes and the map is the identity."""
    premises = [Atom("Human", [Constant("socrates")]),
                _all(X, Implies(Atom("Human", [X]), Atom("Mortal", [X])))]
    conclusion = Atom("Mortal", [Constant("socrates")])
    text, name_map = generate_tptp_problem_with_mapping(premises, conclusion)
    assert text == (
        "fof(premise_1, axiom, human(socrates)).\n"
        "fof(premise_2, axiom, (![X]: (human(X) => mortal(X)))).\n"
        "fof(goal, conjecture, mortal(socrates)).\n")
    assert name_map.term == {"socrates": "socrates"}


def test_separate_term_names_returns_its_inputs_when_nothing_clashes():
    formulas = [Atom("Human", [Constant("socrates")])]
    mapping = TptpNameMap(predicate={"Human": "Human"}, term={"socrates": "socrates"})
    out_formulas, out_mapping = _separate_term_names(formulas, mapping)
    assert out_formulas is formulas and out_mapping is mapping


def test_fof_result_does_not_depend_on_formula_order():
    """Which symbols clash decides the names, not where they first occur."""
    a = Atom("Agent", [Function("agent", [Constant("alice")])])
    c = Atom("Car", [Constant("car")])
    forward, _ = generate_tptp_problem_with_mapping([a], c)
    backward, _ = generate_tptp_problem_with_mapping([c], a)
    assert "agent_term(alice)" in forward and "car(car_term)" in forward
    assert "agent_term(alice)" in backward and "car(car_term)" in backward


# --- D1: the same-kind refusal is unchanged and cannot be dodged -------------

def test_same_kind_refusal_survives_even_when_both_names_also_clash_with_a_predicate():
    """Constants ``car`` and ``Car`` both render ``car`` (same kind: refused),
    and the predicate ``Car`` also renders ``car`` (cross kind: would be
    renamed). The cross-kind rename would give the two constants DIFFERENT new
    names and thereby hide the same-kind collision; the refusal must still
    fire, naming both, exactly as before."""
    formula = And(Atom("Car", [Constant("car")]), Atom("Car", [Constant("Car")]))
    with pytest.raises(NotImplementedError) as excinfo:
        generate_tptp_problem_with_mapping([formula], formula)
    message = str(excinfo.value)
    assert "'car'" in message and "'Car'" in message
    assert "would both render as the TPTP identifier 'car'" in message


def test_same_kind_refusal_for_two_functions_is_unchanged():
    formula = Atom("=", [Function("bar", [Constant("a1")]), Function("Bar", [Constant("a1")])])
    with pytest.raises(NotImplementedError, match="distinct function names"):
        generate_tptp_problem([formula], formula)


# --- SortedConstant was invisible to the fof sanitiser and guard -------------

def test_fof_sorted_constants_get_the_same_same_kind_refusal_as_constants():
    """``gaseous:S`` and ``Gaseous:S`` both rendered ``p(gaseous)`` with no
    refusal (a tautology out of a non-theorem); they are constants like any
    other and are refused by name."""
    left = Atom("P", [SortedConstant("gaseous", "S")])
    right = Atom("P", [SortedConstant("Gaseous", "S")])
    with pytest.raises(NotImplementedError, match="'gaseous' and 'Gaseous'"):
        generate_tptp_problem([left], right)


def test_fof_sorted_constant_with_an_illegal_name_is_sanitised():
    """A digit-leading sorted constant used to reach the file as ``p(9lives)``,
    which TPTP's lower_word grammar forbids; it gets ``n9lives`` like a plain
    constant."""
    atom = Atom("P", [SortedConstant("9lives", "S")])
    text, name_map = generate_tptp_problem_with_mapping([atom], atom)
    assert "p(n9lives)" in text and "9lives)" not in text.replace("n9lives", "")
    assert name_map.term == {"9lives": "n9lives"}


def test_fof_sorted_constant_clashing_with_a_predicate_is_renamed():
    atom = Atom("Car", [SortedConstant("car", "S")])
    text, name_map = generate_tptp_problem_with_mapping([atom], atom)
    assert text.splitlines()[0] == "fof(premise_1, axiom, car(car_term))."
    assert name_map.term == {"car": "car_term"}


def test_fof_sort_guard_predicate_counts_as_a_predicate():
    """``∀x:Human Mortal(x)`` lowers to ``human(X) => mortal(X)``: ``human`` is
    a predicate the source never wrote. The constant ``human`` therefore clashes
    with it and becomes ``human_term`` (the non-emptiness axiom
    ``∃x human(x)`` keeps the guard's name)."""
    sorted_premise = SortedQuantifier("∀", X, "Human", Atom("Mortal", [X]))
    fact = Atom("Mortal", [Constant("human")])
    text, name_map = generate_tptp_problem_with_mapping([sorted_premise, fact], fact)
    assert text == (
        "fof(premise_1, axiom, (![X]: (human(X) => mortal(X)))).\n"
        "fof(premise_2, axiom, mortal(human_term)).\n"
        "fof(nonempty_sort_1, axiom, (?[X0]: human(X0))).\n"
        "fof(goal, conjecture, mortal(human_term)).\n")
    assert name_map.term == {"human": "human_term"}


# =============================================================================
# Oracle (i): read the text back with the kit's own reader, undo the map
# =============================================================================

def _predicates_and_terms(formulas):
    preds, terms = set(), set()
    for formula in formulas:
        for node in formula.walk():
            if isinstance(node, Atom) and node.predicate not in ("=", "≠"):
                preds.add(node.predicate[:1].lower() + node.predicate[1:])
            elif isinstance(node, (Function, Constant, SortedConstant)):
                terms.add(node.name)
    return preds, terms


def test_fof_round_trip_through_the_kit_reader_restores_the_sources():
    premises = [AGENT_PREMISE, Atom("Car", [Constant("car")])]
    conclusion = And(AGENT_THEOREM, Atom("Car", [Function("agent", [Constant("car")])]))
    text, name_map = generate_tptp_problem_with_mapping(premises, conclusion)
    read = [item.formula for item in parse_tptp(text)]
    preds, terms = _predicates_and_terms(read)
    assert preds.isdisjoint(terms), (preds, terms)
    restored = [apply_reverse_tptp(f, name_map) for f in read]
    assert restored == premises + [conclusion]


def test_tff_round_trip_through_the_kit_reader_restores_the_sources():
    # (TF0 declares one type per symbol, so no name is both a constant and a function here)
    premises = [AGENT_PREMISE, Atom("Car", [Constant("auto")])]
    conclusion = And(AGENT_THEOREM, Atom("Car", [Function("agent", [Constant("auto")])]))
    text, name_map = generate_tff_problem_with_mapping(premises, conclusion)
    _signature, items = parse_tff_problem(text)
    read = [item.formula for item in items]
    preds, terms = _predicates_and_terms(read)
    assert preds.isdisjoint(terms), (preds, terms)
    assert [apply_reverse_tptp(f, name_map) for f in read] == premises + [conclusion]


def test_free_text_reverse_map_translates_prover_output_back():
    """A prover echoes the RENDERED names. ``agent`` there is the predicate and
    ``agent_term`` the function, and the map's rendered reverse tables say so
    without ambiguity."""
    _text, name_map = generate_tptp_problem_with_mapping([AGENT_PREMISE], AGENT_THEOREM)
    pred_rev, term_rev = name_map.reverse_rendered()
    assert reverse_map_text("agent(agent_term(X0))", pred_rev, term_rev) == "Agent(agent(X0))"
    assert not set(pred_rev) & set(term_rev)


def test_names_the_writers_mint_read_back_as_kit_text():
    """The writers mint ``<name>_term``. A formula read back from the TPTP text
    (which carries that name) must print as kit text the kit parses again as
    the same formula — the property tests/test_printed_text_reads_back.py gates
    for every generator, applied to this one. The writers mint no bound
    variable (they only rename function/constant symbols), so there is nothing
    to route through ``fresh_variables``; the check that matters is that the
    minted symbol is a legal kit NAME."""
    from unicode_logic_kit import api
    from unicode_logic_kit.atp.tstp_check import _formula_alpha_equal

    text, _ = generate_tptp_problem_with_mapping([AGENT_PREMISE], AGENT_THEOREM)
    for item in parse_tptp(text):
        printed = item.formula.to_unicode_str()
        reparsed = api.parse_any(printed)
        assert reparsed.ok, (printed, reparsed.errors)
        assert _formula_alpha_equal(item.formula, reparsed.formula), printed
    assert "agent_term" in parse_tptp(text)[0].formula.to_unicode_str()


# =============================================================================
# TF0
# =============================================================================

def test_tff_function_clash_declares_each_identifier_once():
    """Before: ``agent: $i > $i`` and ``agent: $i > $o`` (one identifier, two
    types). Now the function is ``agent_term``. Order: sorts, functions,
    constants, predicates (alphabetical within each)."""
    text, name_map = generate_tff_problem_with_mapping([AGENT_PREMISE], AGENT_THEOREM)
    assert text == (
        "tff(func_decl_1, type, agent_term: $i > $i ).\n"
        "tff(pred_decl_2, type, agent: $i > $o ).\n"
        "tff(premise_1, axiom, (![X: $i]: agent(agent_term(X))) ).\n"
        "tff(goal, conjecture, (?[X: $i]: agent(X)) ).\n")
    assert name_map == TptpNameMap(predicate={"Agent": "Agent"},
                                   term={"agent": "agent_term"})
    assert generate_tff_problem([AGENT_PREMISE], AGENT_THEOREM) == text


def test_tff_constant_clash():
    atom = Atom("Car", [Constant("car")])
    text, name_map = generate_tff_problem_with_mapping([atom], atom)
    assert text == (
        "tff(const_decl_1, type, car_term: $i ).\n"
        "tff(pred_decl_2, type, car: $i > $o ).\n"
        "tff(premise_1, axiom, car(car_term) ).\n"
        "tff(goal, conjecture, car(car_term) ).\n")
    assert name_map.term == {"car": "car_term"}


def test_tff_sort_named_like_a_predicate_is_refused_not_declared_twice():
    """Sort ``Agent`` and predicate ``Agent`` both render ``agent``. Vampire and
    E read ``agent: $tType`` next to ``agent: agent > $o`` (measured), but the
    kit's semantics of a sort is the guard predicate of its name, so TF0 would
    answer another question than the fof route and z3 do (see
    ``tests/test_tptp_writer_names.py``). The pair is refused, naming both,
    and nothing is renamed to dodge it: the sorted constant ``agent`` is not
    consulted first."""
    premise = SortedQuantifier("∀", X, "Agent", Atom("Agent", [X]))
    conclusion = Atom("Agent", [SortedConstant("agent", "Agent")])
    with pytest.raises(NotImplementedError) as excinfo:
        generate_tff_problem_with_mapping([premise], conclusion)
    message = str(excinfo.value)
    assert "the sort 'Agent' and the predicate 'Agent'" in message
    assert "TF0 identifier 'agent'" in message
    assert "generate_tptp_problem_with_mapping" in message      # says what to use instead


def test_tff_sort_and_constant_named_alike_are_separated_while_the_predicate_differs():
    """The same problem with the predicate called ``Likes``: only the sorted
    constant ``agent`` shares a word with the sort ``Agent``, so it moves to
    ``agent_term`` and the sort keeps its name."""
    premise = SortedQuantifier("∀", X, "Agent", Atom("Likes", [X]))
    conclusion = Atom("Likes", [SortedConstant("agent", "Agent")])
    text, name_map = generate_tff_problem_with_mapping([premise], conclusion)
    assert text == (
        "tff(sort_decl_1, type, agent: $tType ).\n"
        "tff(const_decl_2, type, agent_term: agent ).\n"
        "tff(pred_decl_3, type, likes: agent > $o ).\n"
        "tff(premise_1, axiom, (![X: agent]: likes(X)) ).\n"
        "tff(goal, conjecture, likes(agent_term) ).\n")
    assert name_map.term == {"agent": "agent_term"}


SORTED_PREMISE = SortedQuantifier("∀", X, "Human", Atom("Mortal", [X]))
SORTED_CONCLUSION = Atom("Mortal", [SortedConstant("human", "Human")])


def test_tff_constant_named_like_a_sort_is_renamed():
    """Sort ``Human`` renders ``human: $tType``; the sorted constant ``human``
    would also be ``human``. Vampire resolves such a term's name to the TYPE and
    refuses the problem (measured: ``The sort $tType of the intended term
    argument human ... is not an instance of sort human``), so the constant
    becomes ``human_term``. Predicate ``Mortal`` is not involved."""
    text, name_map = generate_tff_problem_with_mapping([SORTED_PREMISE], SORTED_CONCLUSION)
    assert text == (
        "tff(sort_decl_1, type, human: $tType ).\n"
        "tff(const_decl_2, type, human_term: human ).\n"
        "tff(pred_decl_3, type, mortal: human > $o ).\n"
        "tff(premise_1, axiom, (![X: human]: mortal(X)) ).\n"
        "tff(goal, conjecture, mortal(human_term) ).\n")
    assert name_map.term == {"human": "human_term"}


def test_tff_same_kind_refusal_is_unchanged():
    with pytest.raises(NotImplementedError, match="Foo.*foo|foo.*Foo"):
        generate_tff_problem([Atom("Foo", [Constant("a1")])], Not(Atom("foo", [Constant("a1")])))


def test_tff_single_formula_uses_the_same_names():
    assert formula_to_tff(AGENT_PREMISE) == "(![X: $i]: agent(agent_term(X)))"


def test_tfa_errors_still_name_the_symbol_the_caller_wrote():
    """The renaming must not leak ``agent_term`` into an error about a symbol
    the caller never wrote. ``agent`` used as a constant and as a function is
    refused naming 'agent'; so is a function ``agent`` with two arities. (The
    validation runs before the term side is renamed.)"""
    clash = And(Atom("Agent", [Constant("agent")]), Atom("Q", [Function("agent", [Constant("b")])]))
    with pytest.raises(ValueError) as constant_and_function:
        generate_tff_arith_problem([], clash)
    assert "'agent'" in str(constant_and_function.value)
    assert "agent_term" not in str(constant_and_function.value)

    arities = And(Atom("Agent", [Function("agent", [Constant("b")])]),
                  Atom("Q", [Function("agent", [Constant("b"), Constant("c")])]))
    with pytest.raises(ValueError) as conflicting_arities:
        generate_tff_arith_problem([], arities)
    assert "'agent'" in str(conflicting_arities.value)
    assert "agent_term" not in str(conflicting_arities.value)


def test_tfa_writer_renames_too():
    """The arithmetic writer shares the sanitiser; it used to refuse this."""
    formula = _all(X, Atom("=", [Function("price", [X]), Function("price", [X])]))
    formula = And(formula, _all(X, Atom("Price", [X])))
    text, name_map = generate_tff_arith_problem([], formula, sort="int")
    assert "price_term: $int > $int" in text and "price: $int > $o" in text
    assert name_map.term == {"price": "price_term"}


# =============================================================================
# NXF: no name map, so it refuses — by name
# =============================================================================

def test_ncl_refuses_a_cross_kind_clash_naming_both_kit_symbols():
    formula = Box(Atom("Car", [Constant("car")]))
    with pytest.raises(NotImplementedError) as excinfo:
        to_tptp_ncl(formula)
    message = str(excinfo.value)
    assert "a constant ('car')" in message and "a predicate ('Car')" in message
    assert "generate_tptp_problem_with_mapping" in message   # says what to use instead


# =============================================================================
# Public surface
# =============================================================================

def test_the_checked_writers_are_public():
    import unicode_logic_kit.atp as atp
    import unicode_logic_kit.atp._tptp_problem as module
    for name in ("generate_tptp_problem", "generate_tptp_problem_with_mapping",
                 "TptpNameMap", "apply_reverse_tptp", "generate_tff_problem",
                 "generate_tff_problem_with_mapping"):
        assert name in atp.__all__, name
        assert getattr(atp, name) is getattr(module, name), name


# =============================================================================
# Determinism across hash seeds
# =============================================================================

_SEED_SCRIPT = """
from unicode_logic_kit.atp import generate_tptp_problem_with_mapping, generate_tff_problem_with_mapping
from unicode_logic_kit.fol.nodes import Atom, Constant, Function
a = Atom('Agent', [Function('agent', [Constant('alice')])])
b = Atom('Car', [Constant('car')])
c = Atom('Human', [Constant('human')])
d = Atom('Car', [Function('agent', [Constant('human')])])
print(generate_tptp_problem_with_mapping([a, b, c], d)[0], end='')
print(generate_tff_problem_with_mapping([a, b, c], d)[0], end='')
"""

_SEED_EXPECTED = (
    "fof(premise_1, axiom, agent(agent_term(alice))).\n"
    "fof(premise_2, axiom, car(car_term)).\n"
    "fof(premise_3, axiom, human(human_term)).\n"
    "fof(goal, conjecture, car(agent_term(human_term))).\n"
    "tff(func_decl_1, type, agent_term: $i > $i ).\n"
    "tff(const_decl_2, type, alice: $i ).\n"
    "tff(const_decl_3, type, car_term: $i ).\n"
    "tff(const_decl_4, type, human_term: $i ).\n"
    "tff(pred_decl_5, type, agent: $i > $o ).\n"
    "tff(pred_decl_6, type, car: $i > $o ).\n"
    "tff(pred_decl_7, type, human: $i > $o ).\n"
    "tff(premise_1, axiom, agent(agent_term(alice)) ).\n"
    "tff(premise_2, axiom, car(car_term) ).\n"
    "tff(premise_3, axiom, human(human_term) ).\n"
    "tff(goal, conjecture, car(agent_term(human_term)) ).\n")


@pytest.mark.parametrize("hash_seed", ["0", "1", "4242"])
def test_the_text_does_not_depend_on_the_string_hash_seed(hash_seed):
    """Terms agent/alice/car/human; predicates Agent/Car/Human. Clashing terms
    (sorted): agent, car, human -> ``agent_term``, ``car_term``,
    ``human_term``; ``alice`` is untouched. TF0 declares functions, then
    constants, then predicates, each in the alphabetical order of its kit
    name."""
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    env = dict(os.environ, PYTHONHASHSEED=hash_seed, PYTHONPATH=root)
    result = subprocess.run([sys.executable, "-c", _SEED_SCRIPT], env=env,
                            capture_output=True, text=True, timeout=300)
    assert result.returncode == 0, result.stderr
    assert result.stdout == _SEED_EXPECTED


# =============================================================================
# Property test: the second oracle at scale
# =============================================================================

_PRED_POOL = [("Agent", 1), ("Car", 1), ("Human", 1), ("Loves", 2), ("Mortal", 1)]
_FUNC_POOL = [("agent", 1), ("loves", 2), ("human", 1)]
_CONST_POOL = ["car", "alice", "mortal", "bob"]


def _random_term(rng, depth, bound):
    roll = rng.random()
    if roll < 0.3 and bound:
        return Variable(rng.choice(sorted(bound)))
    if roll < 0.65 or depth <= 0:
        return Constant(rng.choice(_CONST_POOL))
    name, arity = rng.choice(_FUNC_POOL)
    return Function(name, [_random_term(rng, depth - 1, bound) for _ in range(arity)])


def _random_formula(rng, depth, bound):
    roll = rng.random()
    if depth <= 0 or roll < 0.3:
        name, arity = rng.choice(_PRED_POOL)
        return Atom(name, [_random_term(rng, 1, bound) for _ in range(arity)])
    if roll < 0.45:
        return Not(_random_formula(rng, depth - 1, bound))
    if roll < 0.7:
        op = rng.choice([And, Implies])
        return op(_random_formula(rng, depth - 1, bound), _random_formula(rng, depth - 1, bound))
    var = rng.choice(["x", "y"])
    maker = rng.choice([_all, _ex])
    return maker(Variable(var), _random_formula(rng, depth - 1, bound | {var}))


def _random_problem(seed):
    rng = random.Random(seed)
    premises = [_random_formula(rng, 3, set()) for _ in range(rng.choice([0, 1, 2]))]
    return premises, _random_formula(rng, 3, set())


@pytest.mark.parametrize("seed", range(120))
def test_fof_text_never_uses_a_name_in_two_kinds_and_reads_back_to_the_sources(seed):
    premises, conclusion = _random_problem(seed)
    text, name_map = generate_tptp_problem_with_mapping(premises, conclusion)
    read = [item.formula for item in parse_tptp(text)]
    preds, terms = _predicates_and_terms(read)
    assert preds.isdisjoint(terms), (text, preds & terms)
    assert [apply_reverse_tptp(f, name_map) for f in read] == premises + [conclusion]


@pytest.mark.parametrize("seed", range(120))
def test_tff_text_never_uses_a_name_in_two_kinds_and_reads_back_to_the_sources(seed):
    premises, conclusion = _random_problem(seed)
    # The pools keep constants and functions apart, arities fixed and every
    # variable bound, so TF0 has nothing to refuse and a refusal is a failure.
    text, name_map = generate_tff_problem_with_mapping(premises, conclusion)
    _signature, items = parse_tff_problem(text)
    read = [item.formula for item in items]
    preds, terms = _predicates_and_terms(read)
    assert preds.isdisjoint(terms), (text, preds & terms)
    assert [apply_reverse_tptp(f, name_map) for f in read] == premises + [conclusion]


# =============================================================================
# Oracle (ii): real provers' verdicts equal z3's on the nodes
# =============================================================================

def _conjoin(premises):
    out = premises[0]
    for p in premises[1:]:
        out = And(out, p)
    return out


def _vampire_kwargs():
    """How to reach a Vampire on this machine, or None. Mirrors
    tests/test_vampire_entailment.py: a native binary on PATH, else the Linux
    build behind ``wsl vampire``."""
    found = shutil.which("vampire")
    if found:
        return dict(vampire_path=found, use_wsl=False)
    try:
        probe = subprocess.run(["wsl.exe", "vampire", "--version"], capture_output=True,
                               text=True, timeout=30)
        if probe.returncode == 0 and "Vampire" in probe.stdout:
            return dict(vampire_path="vampire", use_wsl=True)
    except Exception:                              # noqa: BLE001 — any failure means "absent"
        pass
    return None


_VAMPIRE = _vampire_kwargs()


def _eprover_ready():
    from unicode_logic_kit.atp import eprover_available
    return eprover_available()


_EPROVER = _eprover_ready()

#: (id, premises, conclusion, hand-derived verdict). Measured before the fix,
#: on both routes and with both provers: the function cases and the two
#: propositional-vs-constant cases were REJECTED (no SZS status at all); the two
#: unary-predicate-vs-constant cases were accepted — a unary predicate and a
#: constant of one name are told apart by arity — and are here so that the
#: rename is shown not to change a verdict that was already right. Derivations:
#:
#: * function-theorem: ``forall x Agent(agent(x)) |= exists x Agent(x)``. The
#:   domain is non-empty, so instantiate x with any element e; ``Agent(agent(e))``
#:   is the witness.
#: * function-non-theorem: ``... |= forall x Agent(x)``. Domain {0,1}, agent
#:   constantly 0, Agent = {0}: the premise holds, ``Agent(1)`` fails.
#: * constant-theorem: ``Car(car) |= exists x Car(x)``; witness the constant.
#: * constant-non-theorem: ``Car(car) |= Car(truck)``. Domain {0,1}, car is 0,
#:   truck is 1, Car = {0}.
#: * propositional-vs-constant-theorem: ``P & Q(p) |= exists x Q(x)``; witness p.
#: * propositional-vs-constant-non-theorem: ``Q(p) |= P & Q(p)``; P may be false.
VERDICT_CASES = [
    ("function-theorem", [AGENT_PREMISE], AGENT_THEOREM, "proved"),
    ("function-non-theorem", [AGENT_PREMISE], AGENT_NON_THEOREM, "refuted"),
    ("constant-theorem", [Atom("Car", [Constant("car")])], _ex(X, Atom("Car", [X])), "proved"),
    ("constant-non-theorem", [Atom("Car", [Constant("car")])],
     Atom("Car", [Constant("truck")]), "refuted"),
    ("propositional-vs-constant-theorem",
     [And(Atom("P", []), Atom("Q", [Constant("p")]))], _ex(X, Atom("Q", [X])), "proved"),
    ("propositional-vs-constant-non-theorem",
     [Atom("Q", [Constant("p")])], And(Atom("P", []), Atom("Q", [Constant("p")])), "refuted"),
]


def _z3_status(premises, conclusion):
    return "proved" if is_valid(Implies(_conjoin(premises), conclusion)) else "refuted"


@pytest.mark.parametrize("case_id, premises, conclusion, expected", VERDICT_CASES,
                         ids=[c[0] for c in VERDICT_CASES])
def test_z3_on_the_nodes_gives_the_hand_derived_verdict(case_id, premises, conclusion, expected):
    """z3 is the oracle the provers are held to, so it is first held to the
    hand derivation above; a mislabelled case cannot make the live tests
    vacuous."""
    assert _z3_status(premises, conclusion) == expected


@pytest.mark.skipif(_VAMPIRE is None, reason="no Vampire reachable (PATH, or 'wsl vampire')")
def test_vampire_proves_the_sorted_problem_whose_constant_is_named_like_its_sort():
    """``forall x:Human Mortal(x) |= Mortal(human:Human)`` is a theorem under TF0
    semantics (the constant is annotated as a Human). Before the sort-vs-term
    separation Vampire refused the problem (status error) because the constant
    and the sort were both ``human``."""
    from unicode_logic_kit.atp.vampire_entailment import check_entailment_vampire_detailed
    result = check_entailment_vampire_detailed([SORTED_PREMISE], SORTED_CONCLUSION, timeout=30,
                                               tff=True, **_VAMPIRE)
    assert result["status"] == "proved", result


@pytest.mark.skipif(_EPROVER is not True, reason="no eprover reachable (PATH, WSL, $UFK_EPROVER_CMD)")
def test_eprover_proves_the_sorted_problem_whose_constant_is_named_like_its_sort():
    from unicode_logic_kit.atp.eprover_backend import check_entailment_eprover_detailed
    result = check_entailment_eprover_detailed([SORTED_PREMISE], SORTED_CONCLUSION, timeout=30, tff=True)
    assert result["status"] == "proved", result


@pytest.mark.skipif(_EPROVER is not True, reason="no eprover reachable (PATH, WSL, $UFK_EPROVER_CMD)")
@pytest.mark.parametrize("route", ["fof", "tff"])
@pytest.mark.parametrize("case_id, premises, conclusion, expected", VERDICT_CASES,
                         ids=[c[0] for c in VERDICT_CASES])
def test_eprover_verdict_equals_z3_on_the_nodes(case_id, premises, conclusion, expected, route):
    from unicode_logic_kit.atp.eprover_backend import check_entailment_eprover_detailed
    result = check_entailment_eprover_detailed(premises, conclusion, timeout=30, tff=(route == "tff"))
    assert result["status"] == expected == _z3_status(premises, conclusion), result


@pytest.mark.skipif(_VAMPIRE is None, reason="no Vampire reachable (PATH, or 'wsl vampire')")
@pytest.mark.parametrize("route", ["fof", "tff"])
@pytest.mark.parametrize("case_id, premises, conclusion, expected", VERDICT_CASES,
                         ids=[c[0] for c in VERDICT_CASES])
def test_vampire_verdict_equals_z3_on_the_nodes(case_id, premises, conclusion, expected, route):
    from unicode_logic_kit.atp.vampire_entailment import check_entailment_vampire_detailed
    result = check_entailment_vampire_detailed(premises, conclusion, timeout=30,
                                               tff=(route == "tff"), **_VAMPIRE)
    assert result["status"] == expected == _z3_status(premises, conclusion), result
