"""Defects found by an independent check of the TPTP writers, the Prover9
renderer and the prover runners, each pinned by a test that was RED before the
fix and is green after it.

Every expected value below is derived by hand first (the semantic clause is in the
comment or docstring above it), never copied from what the code printed. Two
independent oracles stand behind the strings: z3 on the nodes, and the real
Vampire 5.0.1 / E 3.5.1 / Twee 2.6.1 (through WSL where that is where they are),
which are held to the hand verdict AND to z3. A test that needs a binary skips,
visibly, where none is reachable.

What is covered: ``$true`` / ``$false``; a rewritten predicate that lands on a sort
guard; the Prover9 writer's case-variant variable merge; E's own time limit and
Vampire's timeout detail; a variable with no TPTP spelling; ``Atom.to_prover9`` of an
upper-case nullary atom; two refusal labels; Twee's one-line ``Reflexivity.`` proof.
"""

import shutil
import subprocess

import pytest
import z3

from unicode_logic_kit import MSFLParser
from unicode_logic_kit.atp import (
    generate_tff_arith_problem, generate_tff_problem, generate_tptp_problem,
    generate_tptp_problem_with_mapping,
)
from unicode_logic_kit.atp._tff_problem import formula_to_tff_arith
from unicode_logic_kit.atp.tptp_tff import formula_to_tff
from unicode_logic_kit.atp.z3_models import is_satisfiable, is_valid
from unicode_logic_kit.fol.nodes import (
    And, Atom, Constant, Count, Function, Implies, Not, Number, Or, Quantifier,
    SortedQuantifier, Variable,
)
from unicode_logic_kit.fol.tptp_input import parse_tptp

X, Y = Variable("x"), Variable("y")
a, b = Constant("a"), Constant("b")
TRUE, FALSE = Atom("$true", []), Atom("$false", [])


def P(*args):
    return Atom("P", list(args))


def _all(var, body):
    return Quantifier("∀", var, body)


def _ex(var, body):
    return Quantifier("∃", var, body)


# =============================================================================
# Reaching the real provers
# =============================================================================

def _vampire_kwargs():
    """A native Vampire on PATH, else the Linux build behind ``wsl vampire``."""
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


def _twee_ready():
    try:
        from unicode_logic_kit.atp.twee_entailment import twee_available
        return bool(twee_available())
    except Exception:                              # noqa: BLE001
        return False


_TWEE = _twee_ready()

needs_vampire = pytest.mark.skipif(_VAMPIRE is None, reason="no Vampire reachable (PATH, or 'wsl vampire')")
needs_eprover = pytest.mark.skipif(_EPROVER is not True,
                                   reason="no eprover reachable (PATH, WSL, $UFK_EPROVER_CMD)")
needs_twee = pytest.mark.skipif(not _TWEE, reason="no twee reachable (WSL ~/.local/bin/twee, $UFK_TWEE_CMD)")


def _vampire(premises, conclusion, **kw):
    from unicode_logic_kit.atp.vampire_entailment import check_entailment_vampire_detailed
    return check_entailment_vampire_detailed(premises, conclusion, timeout=30, **_VAMPIRE, **kw)["status"]


def _eprover(premises, conclusion, **kw):
    from unicode_logic_kit.atp.eprover_backend import check_entailment_eprover_detailed
    return check_entailment_eprover_detailed(premises, conclusion, timeout=30, **kw)["status"]


def _conjoin(premises):
    out = premises[0]
    for p in premises[1:]:
        out = And(out, p)
    return out


def _z3(premises, conclusion):
    """z3 on the nodes: ``proved`` iff ``premises ⊨ conclusion`` (default budget, in ms)."""
    if not premises:
        return "proved" if is_valid(conclusion) else "refuted"
    return "proved" if is_valid(Implies(_conjoin(premises), conclusion)) else "refuted"


def _verdict_of_text(prover, text):
    """The prover's verdict on the TPTP TEXT itself, mapped through the SZS table."""
    from unicode_logic_kit.atp.tstp import extract_szs_status, szs_to_verdict_fields
    if prover == "vampire":
        from unicode_logic_kit.atp.vampire_entailment import _spawn_vampire
        out, timed_out = _spawn_vampire(text, timeout=30, **_VAMPIRE)
    else:
        from unicode_logic_kit.atp.eprover_backend import _discover, _run_tptp_prover
        command, use_wsl = _discover("eprover", "UFK_EPROVER_CMD")
        out, timed_out = _run_tptp_prover(text, command, ["--auto", "-s", "--cpu-limit=30"],
                                          use_wsl, timeout_s=40)
    assert not timed_out
    szs = extract_szs_status(out)
    assert szs is not None, out
    return szs_to_verdict_fields(szs, query="conjecture")[0]


# =============================================================================
# $true and $false are TPTP's DEFINED propositions
# =============================================================================
#
# The kit's own reader produces them as the nullary atoms Atom('$true') /
# Atom('$false'). The general rule "a name must be a TPTP word" would turn them into
# fresh uninterpreted propositions (``u0024false``) in every writer and make
# Node.to_tptp() refuse them, so a problem read with parse_tptp and written back
# would change its meaning silently. They are written verbatim, never declared, never
# counted as a symbol, and to_z3 reads them as the constants true and false.

#: (id, TPTP text, hand-derived verdict of premises ⊨ conjecture)
BOOL_CASES = [
    # $false is false in every model, so the axioms are inconsistent and entail ANYTHING.
    ("false-axiom", "fof(a1,axiom,$false).\nfof(c,conjecture,p(a)).\n", "proved"),
    # $true is true in every model, so any axiom set entails it.
    ("true-conjecture", "fof(a1,axiom,p(a)).\nfof(c,conjecture,$true).\n", "proved"),
    # p(a) has a model and $false has none: a model of p(a) is a countermodel.
    ("false-conjecture", "fof(a1,axiom,p(a)).\nfof(c,conjecture,$false).\n", "refuted"),
    # $true says nothing, so it cannot entail p(a), which is false in some model.
    ("true-axiom", "fof(a1,axiom,$true).\nfof(c,conjecture,p(a)).\n", "refuted"),
    # p(a) | $false is equivalent to p(a), which entails p(a).
    ("or-false", "fof(a1,axiom,(p(a) | $false)).\nfof(c,conjecture,p(a)).\n", "proved"),
    # ~$true is $false: inconsistent axioms again.
    ("not-true", "fof(a1,axiom,~$true).\nfof(c,conjecture,p(a)).\n", "proved"),
]


def _read_problem(text):
    items = parse_tptp(text)
    premises = [i.formula for i in items if i.role == "axiom"]
    conclusion = [i.formula for i in items if i.role == "conjecture"][0]
    return premises, conclusion


def test_the_kit_reads_the_defined_propositions_as_nullary_atoms():
    premises, conclusion = _read_problem("fof(a1,axiom,$false).\nfof(c,conjecture,$true).\n")
    assert premises == [FALSE] and conclusion == TRUE


def test_single_formula_writes_the_defined_propositions_verbatim():
    # ``(left & right)`` is Node.to_tptp's conjunction; p(a) is Atom P folded.
    assert TRUE.to_tptp() == "$true" and FALSE.to_tptp() == "$false"
    assert And(TRUE, P(a)).to_tptp() == "($true & p(a))"
    assert Not(FALSE).to_tptp() == "~($false)"


def test_what_the_single_formula_writes_reads_back_as_the_same_formula():
    from unicode_logic_kit import api
    formula = And(TRUE, Or(P(a), FALSE))
    result = api.parse_any(formula.to_tptp(), hint="tptp_bare")
    assert result.ok and result.formula == formula


def test_the_fof_writer_writes_them_verbatim_and_records_nothing():
    text, name_map = generate_tptp_problem_with_mapping([FALSE], P(a))
    assert text == "fof(premise_1, axiom, $false).\nfof(goal, conjecture, p(a)).\n"
    assert name_map.predicate == {"P": "P"}          # only the user's predicate, no '$false'
    text, name_map = generate_tptp_problem_with_mapping([P(a)], Or(TRUE, FALSE))
    assert text == "fof(premise_1, axiom, p(a)).\nfof(goal, conjecture, ($true | $false)).\n"


def test_the_tf0_writer_writes_them_verbatim_and_declares_nothing():
    # Declarations come first (sorts, functions, constants, predicates; one counter),
    # then the formulas. $true is declared by nobody: no ``$true: $o`` line.
    text = generate_tff_problem([P(a)], TRUE)
    assert text == ("tff(const_decl_1, type, a: $i ).\n"
                    "tff(pred_decl_2, type, p: $i > $o ).\n"
                    "tff(premise_1, axiom, p(a) ).\n"
                    "tff(goal, conjecture, $true ).\n")
    assert "$true:" not in generate_tff_problem([FALSE], P(a))
    assert formula_to_tff(And(TRUE, FALSE)) == "($true & $false)"


def test_the_tfa_writer_writes_them_verbatim_and_declares_nothing():
    text, _ = generate_tff_arith_problem([P(a)], TRUE, "int")
    assert text == ("tff(const_decl_1, type, a: $int ).\n"
                    "tff(pred_decl_2, type, p: $int > $o ).\n"
                    "tff(premise_1, axiom, p(a) ).\n"
                    "tff(goal, conjecture, $true ).\n")
    assert formula_to_tff_arith(Or(TRUE, FALSE), "real") == "($true | $false)"


def test_z3_reads_them_as_true_and_false():
    assert z3.is_true(z3.simplify(TRUE.to_z3())) and z3.is_false(z3.simplify(FALSE.to_z3()))
    assert is_valid(TRUE) and not is_satisfiable(FALSE)
    assert not is_valid(P(a)) and is_valid(Implies(FALSE, P(a)))
    # $true as the antecedent adds nothing: (true -> P(a)) is as valid as P(a), i.e. not.
    assert not is_valid(Implies(TRUE, P(a)))


def test_prover9_writes_the_defined_propositions_as_its_own_constants():
    assert TRUE.to_prover9() == "$T" and FALSE.to_prover9() == "$F"
    assert And(TRUE, P(a)).to_prover9() == "($T & P(a))"


def test_the_defined_propositions_are_not_symbols_for_the_collision_checks():
    # A user predicate TRUE / true next to them is a different word and no clash.
    text = generate_tptp_problem([And(TRUE, Atom("true", [a])), FALSE], None)
    assert text == ("fof(premise_1, axiom, ($true & true(a))).\n"
                    "fof(premise_2, axiom, $false).\n")


@pytest.mark.parametrize("atom", [Atom("$foo", [a]), Atom("$foo", []), Atom("$true", [a])],
                         ids=["dollar-word-with-args", "other-nullary-dollar-word", "$true-with-args"])
def test_any_other_dollar_word_is_refused_as_a_reserved_word(atom):
    # Only the NULLARY atoms $true / $false are TPTP's propositions the kit writes
    # verbatim. Any other word that starts with '$' is one of TPTP's own: refused,
    # and the message must say so (it used to say "not a TPTP word", which is false).
    with pytest.raises(NotImplementedError) as info:
        atom.to_tptp()
    message = str(info.value)
    assert repr(atom.predicate) in message and "RESERVED TPTP word" in message
    assert "is not a TPTP word" not in message


def test_the_writers_rewrite_a_dollar_word_like_any_other_illegal_name():
    # '$' is not a word character, so it becomes the code-point escape u0024.
    assert generate_tptp_problem([Atom("$foo", [a])], None) == "fof(premise_1, axiom, u0024foo(a)).\n"
    # ... and the nullary $true next to a UNARY predicate of that name is two things.
    text = generate_tptp_problem([And(TRUE, Atom("$true", [a]))], None)
    assert text == "fof(premise_1, axiom, ($true & u0024true(a))).\n"


def test_to_tstp_writes_a_defined_proposition_verbatim():
    from unicode_logic_kit.atp.resolution_check import ResolutionDerivation, ResolutionStep
    from unicode_logic_kit.atp.tstp import to_tstp
    # {$true} and {~$true} resolve to the empty clause; to_tstp writes each clause
    # as ``cnf(c<i>, plain, <literals>)`` and the empty clause as $false.
    steps = (ResolutionStep(1, frozenset({TRUE}), "input"),
             ResolutionStep(2, frozenset({Not(TRUE)}), "input"),
             ResolutionStep(3, frozenset(), "resolve", (1, 2)))
    derivation = ResolutionDerivation((frozenset({TRUE}), frozenset({Not(TRUE)})), steps)
    assert to_tstp(derivation) == ("cnf(c1, plain, $true).\n"
                                   "cnf(c2, plain, ~($true)).\n"
                                   "cnf(c3, plain, $false, inference(resolution, "
                                   "[status(thm)], [c1, c2])).\n")


@pytest.mark.parametrize("case_id, text, expected", BOOL_CASES, ids=[c[0] for c in BOOL_CASES])
def test_z3_on_the_nodes_gives_the_hand_verdict_for_the_defined_propositions(case_id, text, expected):
    premises, conclusion = _read_problem(text)
    assert _z3(premises, conclusion) == expected


@needs_vampire
@pytest.mark.parametrize("case_id, text, expected", BOOL_CASES, ids=[c[0] for c in BOOL_CASES])
def test_vampire_on_the_original_text_and_on_the_kit_round_trip_agree_with_z3(case_id, text, expected):
    premises, conclusion = _read_problem(text)
    assert _verdict_of_text("vampire", text) == expected              # the ORIGINAL text
    assert _vampire(premises, conclusion, tff=False) == expected      # parse_tptp -> fof writer
    assert _vampire(premises, conclusion, tff=True) == expected       # ... -> TF0 writer
    assert _z3(premises, conclusion) == expected


@needs_eprover
@pytest.mark.parametrize("case_id, text, expected", BOOL_CASES, ids=[c[0] for c in BOOL_CASES])
def test_eprover_on_the_original_text_and_on_the_kit_round_trip_agree_with_z3(case_id, text, expected):
    premises, conclusion = _read_problem(text)
    assert _verdict_of_text("eprover", text) == expected
    assert _eprover(premises, conclusion, tff=False) == expected
    assert _eprover(premises, conclusion, tff=True) == expected
    assert _z3(premises, conclusion) == expected


@needs_vampire
def test_vampire_agrees_with_z3_on_the_typed_arithmetic_route_too():
    # p(a) ⊨ $true: valid, over an integer individual as over any other.
    assert _vampire([P(a)], TRUE, sort="int") == "proved" == _z3([P(a)], TRUE)
    # $false ⊨ p(a): inconsistent premise.
    assert _vampire([FALSE], P(a), sort="int") == "proved" == _z3([FALSE], P(a))


# =============================================================================
# A predicate that has to be rewritten must not land on the word of a sort
# =============================================================================
#
# The fof writer reads the sort S as its guard predicate s. The sanitiser walked only
# the formulas, so it did not know the guard's word, and a predicate rewritten to
# that word was merged with the sort in the whole-problem check. Premises
# ``∀x:S R(x)`` and ``∀x P(x)`` with the conclusion ``∀y R(y)``, where the predicate
# P is spelled so that its rewrite is the sort's own name:
#
#   guard reading: ∀x (S(x) → R(x)), ∃x S(x), ∀x P(x)  ⊭  ∀y R(y)
#   (domain {0,1}, S = R = {0}, P = {0,1}: the premises hold, R(1) fails).
#
# so the verdict is REFUTED. With S and P merged the second premise is ∀x S(x), and
# S(x) → R(x) gives ∀x R(x): proved, wrongly.

SORT_REWRITE_CASES = [
    # (sort, predicate, token the predicate must get: base + "2" because the base is the guard's)
    ("Hasu002dpart", "has-part", "Hasu002dpart2"),       # '-' is the escape u002d
    ("Gru00f6u00dfe", "Größe", "Gru00f6u00dfe2"),         # ö, ß are u00f6, u00df
    ("P2008x", "2008x", "P2008x2"),                      # digit-leading: prefix p, upper-initial
]


def _sort_case(sort, predicate):
    premises = [SortedQuantifier("∀", X, sort, Atom("R", [X])), _all(X, Atom(predicate, [X]))]
    return premises, _all(Y, Atom("R", [Y]))


@pytest.mark.parametrize("sort, predicate, token", SORT_REWRITE_CASES,
                         ids=[c[1] for c in SORT_REWRITE_CASES])
def test_the_rewritten_predicate_gets_a_word_that_is_not_the_sorts(sort, predicate, token):
    premises, conclusion = _sort_case(sort, predicate)
    text, name_map = generate_tptp_problem_with_mapping(premises, conclusion)
    guard, written = sort[0].lower() + sort[1:], token[0].lower() + token[1:]
    assert text == (f"fof(premise_1, axiom, (![X]: ({guard}(X) => r(X)))).\n"
                    f"fof(premise_2, axiom, (![X]: {written}(X))).\n"
                    f"fof(nonempty_sort_1, axiom, (?[X0]: {guard}(X0))).\n"
                    f"fof(goal, conjecture, (![Y]: r(Y))).\n")
    assert name_map.predicate[predicate] == token
    assert sort not in name_map.predicate                 # a guard is not renamed, nor recorded
    # and the map still undoes the rewrite for text a prover echoes back
    assert name_map.reverse_rendered()[0][written] == predicate


@pytest.mark.parametrize("sort, predicate, token", SORT_REWRITE_CASES,
                         ids=[c[1] for c in SORT_REWRITE_CASES])
def test_z3_on_the_nodes_refutes_the_sort_rewrite_problem(sort, predicate, token):
    premises, conclusion = _sort_case(sort, predicate)
    assert _z3(premises, conclusion) == "refuted"


@needs_vampire
@pytest.mark.parametrize("sort, predicate, token", SORT_REWRITE_CASES,
                         ids=[c[1] for c in SORT_REWRITE_CASES])
def test_vampire_agrees_with_z3_on_the_sort_rewrite_problem(sort, predicate, token):
    premises, conclusion = _sort_case(sort, predicate)
    assert _vampire(premises, conclusion, tff=False) == _z3(premises, conclusion) == "refuted"


@needs_eprover
@pytest.mark.parametrize("sort, predicate, token", SORT_REWRITE_CASES,
                         ids=[c[1] for c in SORT_REWRITE_CASES])
def test_eprover_agrees_with_z3_on_the_sort_rewrite_problem(sort, predicate, token):
    premises, conclusion = _sort_case(sort, predicate)
    assert _eprover(premises, conclusion, tff=False) == _z3(premises, conclusion) == "refuted"


def test_the_text_of_the_sort_rewrite_problem_reads_back_to_the_original_names():
    from unicode_logic_kit.atp import apply_reverse_tptp
    premises, conclusion = _sort_case("Hasu002dpart", "has-part")
    text, name_map = generate_tptp_problem_with_mapping(premises, conclusion)
    items = parse_tptp(text)
    # premise_2 is ∀x hasu002dpart2(x); the reader capitalises it, the map undoes the
    # rewrite, and what comes back is the premise the caller wrote.
    assert apply_reverse_tptp(items[1].formula, name_map) == premises[1]
    assert apply_reverse_tptp(items[3].formula, name_map) == conclusion


def test_a_predicate_rewrite_without_a_sort_is_written_as_before():
    # Control: with no sort of that name nothing is reserved, so the rewrite is the
    # base token itself (``hasu002dpart``), exactly the text the writer produced before.
    assert (generate_tptp_problem([Atom("has-part", [a])], None)
            == "fof(premise_1, axiom, hasu002dpart(a)).\n")


def test_every_occurrence_of_the_rewritten_predicate_gets_the_same_token():
    premises = [SortedQuantifier("∀", X, "Hasu002dpart", Atom("R", [X])),
                _all(X, Atom("has-part", [X]))]
    text = generate_tptp_problem(premises, Atom("has-part", [a]))
    assert text.count("hasu002dpart2(") == 2 and text.count("hasu002dpart(") == 2


def test_an_illegal_sort_is_refused_as_a_sort_not_as_a_predicate():
    # The fof writer reads a sort as its guard predicate and does not rewrite it,
    # so an illegal sort name is refused; the message must say it is a SORT and what
    # its guard predicate is, not report "the predicate name" the user never wrote.
    with pytest.raises(NotImplementedError) as info:
        generate_tptp_problem([SortedQuantifier("∀", X, "Größe", Atom("R", [X]))], None)
    message = str(info.value)
    assert message.startswith("generate_tptp_problem: the sort 'Größe' (its guard predicate 'größe')")
    assert "the predicate name" not in message


# =============================================================================
# The Prover9 writer merges x and X, the TPTP writers refuse them
# =============================================================================
#
# A variable is written as the upper-case of its name, so ``∀x ∃X R(x, X)`` is
# written ``(all X (exists X R(X, X)))``: one variable where the formula has two.
# z3 on the nodes keeps them apart: ∀x ∃X R(x,X) ⊭ ∀x R(x,x) (domain {0,1},
# R = {(0,1),(1,0)} makes the premise true and the conclusion false).

def test_z3_keeps_x_and_X_apart():
    x, big_x = Variable("x"), Variable("X")
    premise = _all(x, _ex(big_x, Atom("R", [x, big_x])))
    assert _z3([premise], _all(x, Atom("R", [x, x]))) == "refuted"


def test_the_prover9_writer_refuses_two_variables_it_would_write_as_one():
    from unicode_logic_kit.atp.prover9_entailment import generate_prover9_input_with_mapping
    x, big_x = Variable("x"), Variable("X")
    formula = _all(x, _ex(big_x, Atom("R", [x, big_x])))
    with pytest.raises(NotImplementedError) as info:
        generate_prover9_input_with_mapping([formula], P(a))
    message = str(info.value)
    assert message.startswith("generate_prover9_input_with_mapping: ")
    assert "'x'" in message and "'X'" in message and "Prover9 identifier 'X'" in message
    assert "TPTP" not in message                        # it is the Prover9 writer speaking
    # the conclusion is checked too
    with pytest.raises(NotImplementedError, match="'x'.*'X'"):
        generate_prover9_input_with_mapping([P(a)], formula)


def test_the_prover9_writer_checks_each_formula_alone():
    # x binds in one premise and X in another: two quantifiers that bind separately.
    from unicode_logic_kit.atp.prover9_entailment import generate_prover9_input_with_mapping
    text, _ = generate_prover9_input_with_mapping(
        [_all(Variable("x"), P(Variable("x"))), _all(Variable("X"), Atom("Q", [Variable("X")]))],
        P(a))
    assert "(all X P(X))." in text and "(all X Q(X))." in text


def test_a_single_node_has_no_whole_problem_view_and_says_so():
    from unicode_logic_kit.fol.nodes import Node
    x, big_x = Variable("x"), Variable("X")
    # The outermost call sees the whole NODE: Prover9 writes both variables in upper case, so the inner
    # binder is written under a fresh name and the two variables of the node stay two in the text (the old
    # text, ``(all X (exists X R(X, X)))``, had one variable where the node has two). What a single node
    # still cannot see is the rest of a problem, and the docstring says so.
    assert _all(x, _ex(big_x, Atom("R", [x, big_x]))).to_prover9() == "(all X (exists X0 R(X, X0)))"
    assert "whole-problem view" in Node.to_prover9.__doc__


# =============================================================================
# E's own time limit is the call running out of time
# =============================================================================

class _FakeRun:
    """``subprocess.run`` answering a ``--version`` probe quietly and every other call
    with ONE canned outcome, which is a ``(returncode, stdout, stderr)`` or an
    exception to raise."""

    def __init__(self):
        self.outcome = None

    def respond(self, returncode=0, stdout="", stderr=""):
        self.outcome = (returncode, stdout, stderr)

    def __call__(self, cmd, *args, **kwargs):
        cmd = list(cmd)
        if cmd and cmd[-1] == "--version":
            return subprocess.CompletedProcess(cmd, 0, stdout="fake-prover 1.0\n", stderr="")
        if isinstance(self.outcome, BaseException):
            raise self.outcome
        returncode, stdout, stderr = self.outcome
        return subprocess.CompletedProcess(cmd, returncode, stdout=stdout, stderr=stderr)


@pytest.fixture()
def run(monkeypatch):
    from unicode_logic_kit.atp import eprover_backend as eb
    from unicode_logic_kit.atp import protocol as proto
    monkeypatch.setattr(proto, "_VERSION_CACHE", {})
    monkeypatch.setattr(eb, "_DISCOVERY_CACHE", {})
    monkeypatch.setenv("UFK_VAMPIRE", "fake-vampire")
    monkeypatch.delenv("UFK_VAMPIRE_WSL", raising=False)
    monkeypatch.setenv("UFK_EPROVER_CMD", "fake-eprover")
    fake = _FakeRun()
    monkeypatch.setattr(subprocess, "run", fake)
    return fake


# E 3.5.1, run live through WSL under the kit's own arguments on 10 pigeons into 9
# holes with ``--cpu-limit=1``: exit code 8, stdout begins with an empty line, the
# failure is announced twice (stdout) and ``eprover: CPU time limit exceeded,
# terminating`` is on stderr. The statistics block is cut away.
_E_AT_ITS_CPU_LIMIT = ("\n%% Failure: Resource limit exceeded (time)\n"
                       "%% SZS status ResourceOut\n"
                       "% Preprocessing class: FSLSSMSMSSSNFFN.\n"
                       "% Search class: FGHNF-FSLM00-SFFFFFNN\n")
_E_CPU_LIMIT_STDERR = "eprover: CPU time limit exceeded, terminating\n"

# The same E on the same problem under ``--memory-limit=20`` (recorded):
_E_AT_ITS_MEMORY_LIMIT = ("% Preprocessing class: FSLSSMSMSSSNFFN.\n"
                          "% Search class: FGHNF-FSLM00-SFFFFFNN\n"
                          "% Failure: Resource limit exceeded (memory)\n"
                          "% SZS status ResourceOut\n")

# ... and under ``--processed-clauses-limit=50`` / ``--soft-cpu-limit=1`` (recorded;
# the kit passes neither):
_E_AT_A_USER_LIMIT = ("% Preprocessing class: FSLSSMSMSSSNFFN.\n"
                      "% Failure: User resource limit exceeded!\n"
                      "% SZS status ResourceOut\n")

_GOAL = Atom("Q", [Constant("z")])
_PREMISES = [Atom("P", [Constant("z")])]


def _decide(name, **options):
    from unicode_logic_kit.atp.protocol import get_backend
    return get_backend(name).decide(_GOAL, _PREMISES, **options)


def test_e_stopping_at_the_cpu_limit_of_the_call_is_a_timeout(run):
    # The kit passes --cpu-limit=<the call's budget in seconds> and nothing else, so E
    # stopping with "Resource limit exceeded (time)" IS the budget used up.
    run.respond(returncode=8, stdout=_E_AT_ITS_CPU_LIMIT, stderr=_E_CPU_LIMIT_STDERR)
    verdict = _decide("eprover", timeout=1000)
    assert (verdict.status, verdict.reason) == ("unknown", "timeout")
    assert verdict.szs_status == "ResourceOut"             # E's own line, verbatim
    assert "--cpu-limit of 1 s" in verdict.detail and "budget of this call" in verdict.detail


@pytest.mark.parametrize("stdout", [_E_AT_ITS_MEMORY_LIMIT, _E_AT_A_USER_LIMIT,
                                    "# SZS status ResourceOut\n"],
                         ids=["memory-limit", "a-limit-the-kit-never-passes", "no-failure-line"])
def test_a_resourceout_that_is_not_the_cpu_limit_stays_bound_hit(run, stdout):
    run.respond(returncode=8, stdout=stdout)
    verdict = _decide("eprover", timeout=1000)
    assert (verdict.status, verdict.reason) == ("unknown", "bound_hit")


def test_the_detailed_e_route_classifies_its_own_time_limit_the_same_way(run):
    from unicode_logic_kit.atp.eprover_backend import check_entailment_eprover_detailed
    run.respond(returncode=8, stdout=_E_AT_ITS_CPU_LIMIT, stderr=_E_CPU_LIMIT_STDERR)
    result = check_entailment_eprover_detailed(_PREMISES, _GOAL, timeout=1)
    assert (result["status"], result["reason"], result["szs_status"]) == (
        "unknown", "timeout", "ResourceOut")
    run.respond(returncode=8, stdout=_E_AT_ITS_MEMORY_LIMIT)
    result = check_entailment_eprover_detailed(_PREMISES, _GOAL, timeout=1)
    assert (result["status"], result["reason"]) == ("unknown", "bound_hit")


def test_the_zipperposition_backend_keeps_its_resourceout_mapping(run, monkeypatch):
    # The re-reading is E's alone: another prover's ResourceOut is not E's limit.
    monkeypatch.setenv("UFK_ZIPPERPOSITION_CMD", "fake-zipperposition")
    run.respond(returncode=1, stdout="Failure: Resource limit exceeded (time)\n% SZS status ResourceOut\n")
    verdict = _decide("zipperposition", timeout=1000)
    assert (verdict.status, verdict.reason) == ("unknown", "bound_hit")


# Vampire 5.0.1 stopped by its OWN ``--time_limit 1`` (recorded; no SZS line):
_VAMPIRE_TIME_LIMIT = ("% Running in auto input_syntax mode. Trying TPTP\n"
                       "% Time limit reached! \n"
                       "% Termination reason: Time limit\n"
                       "% Termination phase: Saturation\n"
                       "% Time elapsed: 1.0000 s\n")


def test_the_detail_of_a_vampire_the_kit_stopped_says_what_happened(run):
    run.outcome = subprocess.TimeoutExpired(cmd="fake-vampire", timeout=1)
    verdict = _decide("vampire", timeout=1000)
    assert (verdict.status, verdict.reason) == ("unknown", "timeout")
    assert verdict.detail == ("the budget of this call (1 s) ran out and the kit stopped "
                              "Vampire before it printed a verdict")
    assert "no SZS status line" not in verdict.detail


def test_the_detail_of_an_e_the_kit_stopped_says_what_happened(run):
    # E gets the call's budget as --cpu-limit and 10 s of grace on the wall clock; the
    # kit stops it only when both have passed.
    run.outcome = subprocess.TimeoutExpired(cmd="fake-eprover", timeout=11)
    verdict = _decide("eprover", timeout=1000)
    assert (verdict.status, verdict.reason) == ("unknown", "timeout")
    assert verdict.detail == ("eprover had not stopped when the budget of this call (1 s) plus "
                              "10 s of grace had passed, so the kit stopped it before it "
                              "printed a verdict")


def test_the_detail_of_a_vampire_that_hit_its_own_time_limit_says_what_happened(run):
    run.respond(returncode=1, stdout=_VAMPIRE_TIME_LIMIT)
    verdict = _decide("vampire", timeout=1000)
    assert (verdict.status, verdict.reason) == ("unknown", "timeout")
    assert verdict.detail == "Vampire's search ended on its own (Termination reason: Time limit)"
    assert "no SZS status line" not in verdict.detail


def _pigeonhole(holes):
    """``holes + 1`` pigeons into ``holes`` holes: unsatisfiable, and exponentially hard for
    resolution (Haken 1985), so no prover decides ``holes = 10`` within a second."""
    pigeons = [Constant(f"p{i}") for i in range(holes + 1)]
    hole = [Constant(f"h{j}") for j in range(holes)]
    premises = []
    for p in pigeons:
        placed = Atom("In", [p, hole[0]])
        for h in hole[1:]:
            placed = Or(placed, Atom("In", [p, h]))
        premises.append(placed)
    for h in hole:
        for i in range(len(pigeons)):
            for k in range(i + 1, len(pigeons)):
                premises.append(Not(And(Atom("In", [pigeons[i], h]), Atom("In", [pigeons[k], h]))))
    return premises


@needs_eprover
def test_the_real_e_that_uses_up_the_budget_of_the_call_is_a_timeout():
    from unicode_logic_kit.atp.protocol import EProverBackend
    verdict = EProverBackend().decide(_GOAL, _pigeonhole(10), timeout=1000)
    assert (verdict.status, verdict.reason) == ("unknown", "timeout"), verdict.detail
    assert verdict.szs_status == "ResourceOut"


@needs_vampire
def test_the_real_vampire_that_uses_up_the_budget_of_the_call_is_a_timeout(monkeypatch):
    monkeypatch.setenv("UFK_VAMPIRE", _VAMPIRE["vampire_path"])
    monkeypatch.setenv("UFK_VAMPIRE_WSL", "1" if _VAMPIRE["use_wsl"] else "0")
    from unicode_logic_kit.atp.protocol import VampireBackend
    verdict = VampireBackend().decide(_GOAL, _pigeonhole(10), timeout=1000)
    assert (verdict.status, verdict.reason) == ("unknown", "timeout"), verdict.detail
    assert "no SZS status line" not in verdict.detail
    assert "ran out" in verdict.detail or "Time limit" in verdict.detail


# =============================================================================
# A variable that has no TPTP spelling
# =============================================================================
#
# A variable is written as the upper-case of its name; a TPTP variable is an
# upper-case letter followed by letters, digits and underscores. ``ä`` is written
# ``Ä``, ``x-1`` ``X-1`` and ``1x`` ``1X``: every prover rejects the text (and the
# kit's own parser reads ``∀ä P(ä)``). A variable is bound, so the writers rename
# it to a fresh legal one without recording anything; the single formula refuses.

PARSER = MSFLParser()


def test_the_kits_own_parser_reads_a_variable_with_no_tptp_spelling():
    formula = PARSER.parse("∀ä P(ä)")
    assert formula == _all(Variable("ä"), P(Variable("ä")))


def test_the_single_formula_refuses_it_by_name():
    with pytest.raises(NotImplementedError) as info:
        PARSER.parse("∀ä P(ä)").to_tptp()
    message = str(info.value)
    assert message.startswith("Node.to_tptp: the variable name 'ä' would be written as 'Ä'")
    assert "not a TPTP variable" in message


@pytest.mark.parametrize("name", ["x-1", "1x", "x.y"])
def test_the_single_formula_refuses_a_hand_built_name(name):
    formula = _all(Variable(name), P(Variable(name)))
    with pytest.raises(NotImplementedError, match="not a TPTP variable"):
        formula.to_tptp()


def test_the_fof_writer_renames_it_to_the_first_fresh_variable():
    # No legal variable is in the way, so the fresh name is the first of x0, x1, ...
    # (a variable name is ONE letter then digits, minted through fol._identifiers),
    # written upper-case: X0.
    assert (generate_tptp_problem([PARSER.parse("∀ä P(ä)")], P(a))
            == "fof(premise_1, axiom, (![X0]: p(X0))).\nfof(goal, conjecture, p(a)).\n")


def test_the_text_with_a_renamed_variable_reads_back_as_the_same_formula():
    # What the kit prints must read back: the kit's reader reads X0 as the variable x0
    # and p as the predicate P, so the text is the premise up to the (bound) name.
    text = generate_tptp_problem([PARSER.parse("∀ä P(ä)")], P(a))
    items = parse_tptp(text)
    assert items[0].formula == _all(Variable("x0"), P(Variable("x0")))
    assert items[1].formula == P(a)


def test_the_renaming_is_injective_two_variables_stay_two():
    # ä and Ä are both written Ä: before, ``![Ä]: ?[Ä]: r(Ä,Ä)``. They are different
    # variables (z3 keeps them apart), so they get different fresh names, in the
    # order of their first occurrence: ä -> x0, Ä -> x1.
    formula = _all(Variable("ä"), _ex(Variable("Ä"), Atom("R", [Variable("ä"), Variable("Ä")])))
    assert (generate_tptp_problem([formula], Atom("Q", [a]))
            == "fof(premise_1, axiom, (![X0]: (?[X1]: r(X0,X1)))).\nfof(goal, conjecture, q(a)).\n")
    # ... which z3 agrees is not "r(x,x)":
    assert _z3([formula], _all(X, Atom("R", [X, X]))) == "refuted"


def test_the_renaming_never_takes_a_legal_variable_over():
    # x0 is taken by the user: the fresh name for ä must be x1, not x0.
    formula = _all(Variable("x0"), _all(Variable("ä"), Atom("R", [Variable("x0"), Variable("ä")])))
    assert (generate_tptp_problem([formula], None)
            == "fof(premise_1, axiom, (![X0]: (![X1]: r(X0,X1)))).\n")
    # A user variable spelled X0 is written X0 too: it blocks x0 just the same.
    formula = _all(Variable("X0"), _all(Variable("ä"), Atom("R", [Variable("X0"), Variable("ä")])))
    assert (generate_tptp_problem([formula], None)
            == "fof(premise_1, axiom, (![X0]: (![X1]: r(X0,X1)))).\n")


def test_two_legal_variables_written_as_one_are_still_refused():
    # x and X are both legal; their refusal is unchanged (the asymmetry is deliberate).
    formula = _all(Variable("x"), _ex(Variable("X"), Atom("R", [Variable("x"), Variable("X")])))
    with pytest.raises(NotImplementedError, match="variable 'x' and the variable 'X'"):
        generate_tptp_problem([formula], None)


def test_a_formula_whose_variables_are_all_legal_is_passed_on_as_the_same_object():
    from unicode_logic_kit.fol._tptp_symbols import legalise_variables
    formula = _all(X, _ex(Variable("y1"), Atom("R", [X, Variable("y1")])))
    assert legalise_variables(formula) is formula


def test_a_counting_quantifier_over_an_illegal_variable_is_written_with_legal_names():
    # ∃≥2 ä P(ä) is lowered to a witness encoding whose variables derive from the
    # counting variable's name; renamed first, they are legal too.
    formula = Count("ge", Number(2), Variable("ä"), P(Variable("ä")))
    text = generate_tptp_problem([formula], None)
    assert text.isascii() and "![" not in text and "?[X" in text


def test_the_tf0_writer_renames_it():
    text = generate_tff_problem([_all(Variable("ä"), P(Variable("ä")))], P(a), )
    assert "(![X0: $i]: p(X0))" in text and "Ä" not in text
    sorted_text = generate_tff_problem(
        [SortedQuantifier("∀", Variable("ä"), "S", P(Variable("ä")))], None)
    assert "(![X0: s]: p(X0))" in sorted_text and "Ä" not in sorted_text
    assert formula_to_tff(_all(Variable("ä"), P(Variable("ä")))) == "(![X0: $i]: p(X0))"


def test_the_tfa_writer_renames_it():
    text, _ = generate_tff_arith_problem([_all(Variable("ä"), P(Variable("ä")))], P(a), "int")
    assert "(![X0: $int]: p(X0))" in text and "Ä" not in text
    assert formula_to_tff_arith(_all(Variable("ä"), P(Variable("ä"))), "int") == "(![X0: $int]: p(X0))"


#: (id, premise, conclusion, hand verdict). ∀ä P(ä) ⊨ P(a): instantiate. ∃ä P(ä) ⊭ P(a):
#: a domain {0,1} with P = {1} and a = 0.
VARIABLE_CASES = [
    ("universal-entails-instance", "∀ä P(ä)", P(a), "proved"),
    ("existential-does-not", "∃ä P(ä)", P(a), "refuted"),
]


@pytest.mark.parametrize("case_id, source, conclusion, expected", VARIABLE_CASES,
                         ids=[c[0] for c in VARIABLE_CASES])
def test_z3_gives_the_hand_verdict_on_the_parsed_variable_problem(case_id, source, conclusion, expected):
    assert _z3([PARSER.parse(source)], conclusion) == expected


@needs_vampire
@pytest.mark.parametrize("case_id, source, conclusion, expected", VARIABLE_CASES,
                         ids=[c[0] for c in VARIABLE_CASES])
def test_vampire_reads_the_renamed_variable_and_agrees_with_z3(case_id, source, conclusion, expected):
    premise = PARSER.parse(source)
    assert _vampire([premise], conclusion, tff=False) == expected
    assert _vampire([premise], conclusion, tff=True) == expected
    if expected == "proved":
        # Over $int Vampire can prove but gives up on a non-theorem (no SZS line).
        assert _vampire([premise], conclusion, sort="int") == expected


@needs_eprover
@pytest.mark.parametrize("case_id, source, conclusion, expected", VARIABLE_CASES,
                         ids=[c[0] for c in VARIABLE_CASES])
def test_eprover_reads_the_renamed_variable_and_agrees_with_z3(case_id, source, conclusion, expected):
    premise = PARSER.parse(source)
    assert _eprover([premise], conclusion, tff=False) == expected
    assert _eprover([premise], conclusion, tff=True) == expected


@needs_vampire
def test_vampire_keeps_two_illegal_variables_apart():
    formula = _all(Variable("ä"), _ex(Variable("Ä"), Atom("R", [Variable("ä"), Variable("Ä")])))
    conclusion = _all(X, Atom("R", [X, X]))
    assert _vampire([formula], conclusion, tff=False) == "refuted" == _z3([formula], conclusion)


# =============================================================================
# An upper-case proposition through the single renderer: CLI and MCP
#
# The single renderer writes `Rain` in double quotes (see Atom.to_prover9): Prover9
# reads a bare upper-case atom as a variable and refuses the file, and a quoted
# symbol is never a variable. The PROBLEM writer renames it instead; that is pinned
# in tests/test_prover9_variable_rule.py.
# =============================================================================

def test_the_cli_renders_an_upper_case_proposition_for_prover9(capsys):
    from unicode_logic_kit.__main__ import main
    assert main(["Rain ∧ Wind", "--to", "prover9"]) == 0
    captured = capsys.readouterr()
    assert captured.out.strip() == '("Rain" & "Wind")' and captured.err == ""


def test_the_cli_still_renders_the_formula_for_tptp(capsys):
    from unicode_logic_kit.__main__ import main
    assert main(["Rain ∧ Wind", "--to", "tptp"]) == 0
    assert capsys.readouterr().out.strip() == "(rain & wind)"


def test_the_mcp_render_tool_renders_it_too():
    pytest.importorskip("mcp", reason="optional [mcp] extra not installed")
    from unicode_logic_kit.mcp.server import render
    result = render("Rain ∧ Wind", to="prover9")
    assert "error" not in result
    assert '("Rain" & "Wind")' in str(result)


# =============================================================================
# The TFA writer names itself
# =============================================================================

def test_the_tfa_writer_names_itself_in_a_variable_collision():
    formula = _all(Variable("x"), _ex(Variable("X"), Atom("R", [Variable("x"), Variable("X")])))
    with pytest.raises(NotImplementedError) as info:
        generate_tff_arith_problem([formula], None, "int")
    assert str(info.value).startswith("generate_tff_arith_problem: the variable 'x' and the variable 'X'")
    assert str(info.value).endswith("before exporting this problem.")
    with pytest.raises(NotImplementedError) as info:
        formula_to_tff_arith(formula, "int")
    # The refusal names the function that was called. (It used to open with the name of
    # the whole-problem writer, which this caller never called.)
    assert str(info.value).startswith("formula_to_tff_arith: ")
    assert str(info.value).endswith("before exporting this formula.")


def test_the_tfa_writer_names_itself_in_a_name_collision():
    with pytest.raises(NotImplementedError, match="^generate_tff_arith_problem: distinct predicate names"):
        generate_tff_arith_problem([Atom("Foo", [a]), Atom("foo", [a])], None, "int")


def test_to_tstp_names_itself_in_a_collision():
    from unicode_logic_kit.atp.resolution_check import ResolutionDerivation, ResolutionStep
    from unicode_logic_kit.atp.tstp import to_tstp
    # A name map that already carries the constant Foo (written foo) meets a derivation
    # that introduces the distinct constant foo: one word for two symbols.
    _, mapping = generate_tptp_problem_with_mapping(
        [Atom("P", [Constant("Foo")])], Atom("P", [Constant("Foo")]))
    inputs = (frozenset({P(Constant("foo"))}), frozenset({Atom("Q", [Constant("foo")])}))
    steps = (ResolutionStep(1, inputs[0], "input"), ResolutionStep(2, inputs[1], "input"))
    with pytest.raises(NotImplementedError, match="^to_tstp: distinct constant/function names 'Foo' and 'foo'"):
        to_tstp(ResolutionDerivation(inputs, steps), name_map=mapping)


def test_the_fof_writer_still_names_itself():
    with pytest.raises(NotImplementedError, match="^generate_tptp_problem: distinct predicate names"):
        generate_tptp_problem([Atom("Foo", [a]), Atom("foo", [a])], None)


# =============================================================================
# Twee's one-line "Reflexivity." proof
# =============================================================================
#
# Twee 2.6.1 proves a goal that is an instance of x = x with no rewrite step at all
# (recorded live, ``twee --quiet`` on ``fof(goal, conjecture, a = a)``):
#
_TWEE_REFLEXIVITY = ("The conjecture is true! Here is a proof.\n"
                     "\n"
                     "\n"
                     "Goal 1 (goal): a = a.\n"
                     "Proof:\n"
                     "Reflexivity.\n"
                     "\n"
                     "RESULT: Theorem (the conjecture is true).\n")


@pytest.fixture()
def twee_says(monkeypatch):
    """Make the Twee runner return a canned stdout."""
    from unicode_logic_kit.atp import twee_entailment as te

    def install(stdout):
        monkeypatch.setattr(te, "_spawn_twee", lambda *args, **kwargs: (stdout, "", False))
    return install


def _equation(left, right):
    return Atom("=", [left, right])


def test_a_reflexivity_proof_of_a_reflexive_goal_is_proved_with_a_zero_step_chain(twee_says):
    from unicode_logic_kit.atp.twee_backend import TweeBackend
    twee_says(_TWEE_REFLEXIVITY)
    verdict = TweeBackend().decide(_equation(a, a), [])
    # a = a is an instance of x = x: valid whatever the premises, so PROVED is sound.
    assert verdict.status == "proved" and verdict.reason is None
    assert "independently verified by atp.twee_check" in verdict.detail
    assert "Reflexivity" in verdict.detail
    goal = verdict.proof["goal"]
    assert goal["chain"]["citations"] == [] and len(goal["chain"]["terms"]) == 1
    assert goal["equation"]["lhs"] == goal["equation"]["rhs"] == {"_type": "Constant", "name": "a"}


def test_a_reflexivity_proof_of_a_goal_that_is_not_the_requested_conclusion_is_not_proved(twee_says):
    from unicode_logic_kit.atp.twee_backend import TweeBackend
    # Twee printed ``Goal: a = a`` for the question ``a = b``: the proved goal does not
    # restate the conclusion, so the second check fails and the verdict is ERROR.
    twee_says(_TWEE_REFLEXIVITY)
    verdict = TweeBackend().decide(_equation(a, b), [])
    assert verdict.status == "error" and verdict.reason == "infra"
    assert "goal_matches_conclusion" in verdict.detail


def test_a_reflexivity_proof_whose_two_sides_differ_is_not_proved(twee_says):
    from unicode_logic_kit.atp.twee_backend import TweeBackend
    # A corrupted proof: a zero-step chain cannot connect a to b, and the kit says so.
    twee_says(_TWEE_REFLEXIVITY.replace("Goal 1 (goal): a = a.", "Goal 1 (goal): a = b."))
    verdict = TweeBackend().decide(_equation(a, b), [])
    assert verdict.status == "error" and verdict.reason == "infra"
    assert "chain does not end at its stated right-hand side" in verdict.detail


@pytest.mark.parametrize("stdout", [
    _TWEE_REFLEXIVITY.replace("Proof:\nReflexivity.\n", "Proof:\nReflexivity.\nReflexivity.\n"),
    _TWEE_REFLEXIVITY.replace("Goal 1 (goal): a = a.\n", "Axiom 1 (premise_1): a = b.\n\nGoal 1 (goal): a = a.\n"),
    _TWEE_REFLEXIVITY.replace("Reflexivity.", "Symmetry."),
], ids=["extra-line", "an-axiom-is-listed", "another-word"])
def test_anything_but_the_exact_five_line_shape_is_still_refused(twee_says, stdout):
    from unicode_logic_kit.atp.twee_backend import TweeBackend
    twee_says(stdout)
    verdict = TweeBackend().decide(_equation(a, a), [])
    assert verdict.status == "error" and verdict.reason == "infra"
    assert "unparseable" in verdict.detail


@needs_twee
@pytest.mark.parametrize("premises, conclusion", [
    ([], _equation(a, a)),
    ([], _equation(Function("f", [a]), Function("f", [a]))),
    ([], And(_equation(a, a), _equation(b, b))),
    ([], _all(X, _all(Y, _equation(Function("f", [X]), Function("f", [X]))))),
    ([_equation(a, b)], _equation(a, a)),
], ids=["a=a", "f(a)=f(a)", "conjunction", "quantified", "with-a-premise"])
def test_the_real_twee_proves_a_reflexive_goal(premises, conclusion):
    from unicode_logic_kit.atp.twee_backend import TweeBackend
    verdict = TweeBackend().decide(conclusion, premises, timeout=30000)
    assert verdict.status == "proved", (verdict.status, verdict.reason, verdict.detail)
    # z3 on the nodes: an instance of x = x is valid
    assert _z3(premises, conclusion) == "proved"


@needs_twee
def test_the_real_twee_still_refutes_a_non_theorem():
    from unicode_logic_kit.atp.twee_backend import TweeBackend
    assert TweeBackend().decide(_equation(a, b), [], timeout=30000).status == "refuted"
