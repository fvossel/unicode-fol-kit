"""What a Twee goal may call its Skolem constants and its conjunction encoding.

The checker of a Twee proof (``atp.twee_check``) answers two questions about ONE proof: is
every step a rewrite the cited axiom licenses (:func:`check_twee_proof`), and is the goal
the conclusion that was asked for (:func:`goal_matches_conclusion`). The second has to read
a proof of ``f(c) = g(c)`` as a proof of ``∀x f(x) = g(x)`` and a proof of
``tuple(a, b) = tuple(c, d)`` as a proof of ``a = c ∧ b = d``. Both readings are right ONLY
for names of Twee's own:

* ``Γ ⊢ φ(c)`` is ``Γ ⊢ ∀x φ(x)`` when ``c`` occurs nowhere in ``Γ`` and nowhere in
  ``φ``. A goal that is an INSTANCE of the claim (at a constant of the premises, at a
  compound term, at a numeral) is a weaker statement.
* ``tuple(s1, s2) = tuple(t1, t2)`` is ``s1 = t1 ∧ s2 = t2`` when ``tuple`` is a symbol
  that occurs in no axiom and not in the conclusion (``tuple`` need not be injective).
  Twee names its encoding ``tuple`` unless the problem already has that name, and then
  ``tuple2`` (``tuple3``, ...): the name is not assumed, it is checked.

Each tampered proof below is a proof whose steps are all right (the checker accepts its
chain) for a statement that does not follow, and each countermodel is written down. Every
verbatim proof text is a ``twee --quiet`` stdout captured on this machine (Twee 2.6.1,
WSL).
"""

import dataclasses

import pytest

from unicode_fol_kit import api
from unicode_fol_kit.atp.twee_backend import TweeBackend
from unicode_fol_kit.atp.twee_check import (
    check_twee_proof, goal_matches_conclusion, goal_mismatch,
)
from unicode_fol_kit.atp.twee_entailment import (
    TweeAxiom, TweeChain, TweeCitation, TweeEquation, TweeGoal, TweeProof,
    parse_twee_proof, twee_available,
)
from unicode_fol_kit.fol.nodes import And, Atom, Constant, Function, Number, Quantifier, Variable

_X, _Y = Variable("x"), Variable("y")
_AA, _BB, _CC, _DD, _EE, _FF = (Constant(name) for name in ("aa", "bb", "cc", "dd", "ee", "ff"))


def _app(name, *args):
    return Function(name, list(args))


def _eq(left, right):
    return Atom("=", [left, right])


def _all(variable, body):
    return Quantifier("∀", variable, body)


def _and(*parts):
    result = parts[0]
    for part in parts[1:]:
        result = And(result, part)
    return result


def _one_step_proof(axiom_lhs, axiom_rhs, goal_lhs, goal_rhs):
    """The proof whose single axiom is ``axiom_lhs = axiom_rhs`` (its variables spelt as Twee
    spells them, upper case) and whose goal ``goal_lhs = goal_rhs`` is one step of it."""
    return TweeProof(
        axioms=(TweeAxiom(1, "premise_1", TweeEquation(axiom_lhs, axiom_rhs)),),
        lemmas=(),
        goal=TweeGoal(1, "goal", TweeEquation(goal_lhs, goal_rhs),
                      TweeChain((goal_lhs, goal_rhs), (TweeCitation("axiom", 1, "premise_1"),))))


# Premise ∀x aa = x (every element is aa: a universe of ONE element), conclusion
# tuple(bb, cc) = dd ∧ ee = ff, where `tuple` is a function of the problem.
_PROOF_TUPLE_IS_A_USER_FUNCTION = """\
The conjecture is true! Here is a proof.

Axiom 1 (premise_1): aa = X.

Goal 1 (goal): tuple2(tuple(bb, cc), ee) = tuple2(dd, ff).
Proof:
  tuple2(tuple(bb, cc), ee)
= { by axiom 1 (premise_1) R->L }
  aa
= { by axiom 1 (premise_1) }
  tuple2(dd, ff)

RESULT: Theorem (the conjecture is true).
"""

# The same problem with `tuple` and `tuple2` both functions of the problem.
_PROOF_TUPLE_AND_TUPLE2_ARE_USER_FUNCTIONS = """\
The conjecture is true! Here is a proof.

Axiom 1 (premise_1): aa = X.

Goal 1 (goal): tuple3(tuple(bb, cc), tuple2(bb, cc), ee) = tuple3(dd, dd, ff).
Proof:
  tuple3(tuple(bb, cc), tuple2(bb, cc), ee)
= { by axiom 1 (premise_1) R->L }
  aa
= { by axiom 1 (premise_1) }
  tuple3(dd, dd, ff)

RESULT: Theorem (the conjecture is true).
"""

# Premise ∀y f(y) = g(y), conclusion ∀x f(x) = g(x): the Skolem constant is x.
_PROOF_SKOLEM_CONSTANT = """\
The conjecture is true! Here is a proof.

Axiom 1 (premise_1): f(X) = g(X).

Goal 1 (goal): f(x) = g(x).
Proof:
  f(x)
= { by axiom 1 (premise_1) }
  g(x)

RESULT: Theorem (the conjecture is true).
"""

_CONJUNCTION_WITH_USER_TUPLE = _and(_eq(_app("tuple", _BB, _CC), _DD), _eq(_EE, _FF))
_EVERYTHING_IS_AA = _all(_X, _eq(_AA, _X))


# ---------------------------------------------------------------------------
# A goal that is an instance of a universal claim is not the claim
# ---------------------------------------------------------------------------

def test_the_proof_of_a_ground_instance_is_not_a_proof_of_the_universal_claim():
    """Premise ``f(aa) = g(aa)``; the goal ``f(aa) = g(aa)`` is proved by it. The claim
    ``∀x f(x) = g(x)`` does not follow: universe ``{0, 1}``, ``aa`` ↦ 0, ``f`` ↦ (0, 0),
    ``g`` ↦ (0, 1) satisfy the premise (both give 0 at ``aa``) and ``f(1) = 0 ≠ 1 = g(1)``."""
    premise = _eq(_app("f", _AA), _app("g", _AA))
    proof = _one_step_proof(_app("f", _AA), _app("g", _AA), _app("f", _AA), _app("g", _AA))
    claim = _all(_X, _eq(_app("f", _X), _app("g", _X)))
    assert check_twee_proof(proof, [premise]).ok
    assert goal_matches_conclusion(proof, claim) is False
    assert "aa" in goal_mismatch(proof, claim)
    assert goal_matches_conclusion(proof, premise) is True
    assert goal_mismatch(proof, premise) is None


def test_the_proof_of_an_instance_at_a_compound_term_is_not_a_proof_of_the_universal_claim():
    """Premise ``g(f(aa)) = h(f(aa))``; the claim ``∀x g(x) = h(x)`` does not follow:
    universe ``{0, 1}``, ``aa`` ↦ 0, ``f`` ↦ (0, 0), ``g(0) = h(0) = 0``, ``g(1) = 0``,
    ``h(1) = 1`` satisfy the premise (``f(aa) = 0``) and ``g(1) ≠ h(1)``."""
    instance = _app("f", _AA)
    premise = _eq(_app("g", instance), _app("h", instance))
    proof = _one_step_proof(_app("g", instance), _app("h", instance),
                            _app("g", instance), _app("h", instance))
    claim = _all(_X, _eq(_app("g", _X), _app("h", _X)))
    assert check_twee_proof(proof, [premise]).ok
    assert goal_matches_conclusion(proof, claim) is False
    assert "not a constant" in goal_mismatch(proof, claim)


def test_the_proof_of_an_instance_at_a_numeral_is_not_a_proof_of_the_universal_claim():
    """The same countermodel as for the constant, with the numeral ``1`` for ``aa``."""
    one = Number(1)
    premise = _eq(_app("f", one), _app("g", one))
    proof = _one_step_proof(_app("f", one), _app("g", one), _app("f", one), _app("g", one))
    claim = _all(_X, _eq(_app("f", _X), _app("g", _X)))
    assert check_twee_proof(proof, [premise]).ok
    assert goal_matches_conclusion(proof, claim) is False


def test_the_proof_of_an_instance_at_a_constant_of_the_claim_itself_is_not_the_claim():
    """Premise ``∀y f(y) = y`` proves ``f(kk) = kk``, but the claim ``∀x f(x) = kk`` does not
    follow: universe ``{0, 1}``, ``f`` the identity, ``kk`` ↦ 0 satisfy the premise and
    ``f(1) = 1 ≠ 0``. ``kk`` occurs in no axiom of the proof; it occurs in the claim."""
    premise = _all(_Y, _eq(_app("f", _Y), _Y))
    kk = Constant("kk")
    proof = _one_step_proof(_app("f", Variable("X")), Variable("X"), _app("f", kk), kk)
    claim = _all(_X, _eq(_app("f", _X), kk))
    assert check_twee_proof(proof, [premise]).ok
    assert goal_matches_conclusion(proof, claim) is False
    assert "kk" in goal_mismatch(proof, claim)


def test_a_variable_in_the_goal_is_not_read_as_a_skolem_constant():
    """Twee prints Skolem CONSTANTS; a variable in the goal is not what it prints, and it is
    not read as one (the proof is refused, not misread)."""
    premise = _all(_Y, _eq(_app("f", _Y), _app("g", _Y)))
    proof = _one_step_proof(_app("f", Variable("X")), _app("g", Variable("X")),
                            _app("f", Variable("Z")), _app("g", Variable("Z")))
    claim = _all(_X, _eq(_app("f", _X), _app("g", _X)))
    assert check_twee_proof(proof, [premise]).ok
    assert goal_matches_conclusion(proof, claim) is False


def test_a_constant_that_is_fresh_is_the_skolem_constant_of_the_claim():
    """What the refusals above are NOT: premise ``∀y f(y) = g(y)`` and a goal at a constant
    ``c`` that occurs nowhere else is the claim ``∀x f(x) = g(x)`` (verbatim Twee output)."""
    proof = parse_twee_proof(_PROOF_SKOLEM_CONSTANT)
    premise = _all(_Y, _eq(_app("f", _Y), _app("g", _Y)))
    claim = _all(_X, _eq(_app("f", _X), _app("g", _X)))
    assert check_twee_proof(proof, [premise]).ok
    assert goal_matches_conclusion(proof, claim) is True
    # a different name for the Skolem constant is as good, and a renamed variable is the same claim
    renamed = _all(Variable("w"), _eq(_app("f", Variable("w")), _app("g", Variable("w"))))
    assert goal_matches_conclusion(proof, renamed) is True


def test_one_fresh_constant_for_two_variables_is_still_not_the_claim_about_two_elements():
    """The goal ``f(c) = g(c)`` at a fresh ``c`` (it IS the claim ``∀x f(x) = g(x)``) is not
    ``∀x ∀y f(x) = g(y)``: universe ``{0, 1}`` with ``f`` and ``g`` the identity satisfies
    the premise ``∀z f(z) = g(z)`` and ``f(0) = 0 ≠ 1 = g(1)``. Only the injectivity of the
    binding tells the two claims apart here: the constant is fresh."""
    premise = _all(Variable("z"), _eq(_app("f", Variable("z")), _app("g", Variable("z"))))
    fresh = Constant("c")
    proof = _one_step_proof(_app("f", Variable("X")), _app("g", Variable("X")),
                            _app("f", fresh), _app("g", fresh))
    one_variable = _all(_X, _eq(_app("f", _X), _app("g", _X)))
    two_variables = _all(_X, _all(_Y, _eq(_app("f", _X), _app("g", _Y))))
    assert check_twee_proof(proof, [premise]).ok
    assert goal_matches_conclusion(proof, one_variable) is True
    assert goal_matches_conclusion(proof, two_variables) is False


def test_a_constant_that_is_a_symbol_of_an_axiom_is_not_fresh_whatever_its_kind():
    """A function symbol and a constant of one name are one name: premise ``kk(aa) = aa``
    proves its own instance, and the claim ``∀x kk(x) = x`` does not follow (universe
    ``{0, 1}``, ``aa`` ↦ 0, ``kk`` ↦ (0, 0))."""
    premise = _eq(_app("kk", _AA), _AA)
    proof = _one_step_proof(_app("kk", _AA), _AA, _app("kk", _AA), _AA)
    claim = _all(_X, _eq(_app("kk", _X), _X))
    assert check_twee_proof(proof, [premise]).ok
    assert goal_matches_conclusion(proof, claim) is False


# ---------------------------------------------------------------------------
# The conjunction encoding is a symbol of Twee's own
# ---------------------------------------------------------------------------

def test_a_proof_of_the_callers_own_tuple_equation_is_not_a_proof_of_a_conjunction():
    """Premise ``tuple(f(aa), g(aa)) = tuple(bb, cc)``; its own proof is a proof of the
    conjunction ``f(aa) = bb ∧ g(aa) = cc`` only if ``tuple`` is injective, which nothing
    says: universe ``{0, 1}``, ``tuple`` constantly 0, ``f(aa) = g(aa) = 0``, ``bb = cc =
    1`` satisfy the premise (0 = 0) and ``f(aa) = 0 ≠ 1 = bb``."""
    left = _app("tuple", _app("f", _AA), _app("g", _AA))
    right = _app("tuple", _BB, _CC)
    premise = _eq(left, right)
    proof = _one_step_proof(left, right, left, right)
    conjunction = _and(_eq(_app("f", _AA), _BB), _eq(_app("g", _AA), _CC))
    assert check_twee_proof(proof, [premise]).ok
    assert goal_matches_conclusion(proof, conjunction) is False
    assert "tuple" in goal_mismatch(proof, conjunction)
    assert goal_matches_conclusion(proof, premise) is True


def test_the_encoding_symbol_may_not_be_a_symbol_of_the_conclusion_either():
    """The genuine proof for premise ``∀x aa = x`` and conclusion ``tuple(bb, cc) = dd ∧
    ee = ff`` calls its encoding ``tuple2``. The same proof text with the encoding called
    ``tuple`` is a statement about the conclusion's own function, not about the conjuncts."""
    genuine = parse_twee_proof(_PROOF_TUPLE_IS_A_USER_FUNCTION)
    assert check_twee_proof(genuine, [_EVERYTHING_IS_AA]).ok
    assert goal_matches_conclusion(genuine, _CONJUNCTION_WITH_USER_TUPLE) is True
    renamed = parse_twee_proof(_PROOF_TUPLE_IS_A_USER_FUNCTION.replace("tuple2", "tuple"))
    assert check_twee_proof(renamed, [_EVERYTHING_IS_AA]).ok
    assert goal_matches_conclusion(renamed, _CONJUNCTION_WITH_USER_TUPLE) is False
    assert "tuple" in goal_mismatch(renamed, _CONJUNCTION_WITH_USER_TUPLE)


def test_the_encoding_symbol_is_whatever_fresh_name_twee_chose():
    """With ``tuple`` taken Twee says ``tuple2``, with ``tuple`` and ``tuple2`` taken it says
    ``tuple3``; both are read as the encoding of the conjunction, and a name that is not
    taken is as good as any other."""
    pair = parse_twee_proof(_PROOF_TUPLE_IS_A_USER_FUNCTION)
    assert goal_matches_conclusion(pair, _CONJUNCTION_WITH_USER_TUPLE) is True
    triple = parse_twee_proof(_PROOF_TUPLE_AND_TUPLE2_ARE_USER_FUNCTIONS)
    conjunction = _and(_eq(_app("tuple", _BB, _CC), _DD), _eq(_app("tuple2", _BB, _CC), _DD),
                       _eq(_EE, _FF))
    assert check_twee_proof(triple, [_EVERYTHING_IS_AA]).ok
    assert goal_matches_conclusion(triple, conjunction) is True
    other_name = parse_twee_proof(_PROOF_TUPLE_IS_A_USER_FUNCTION.replace("tuple2", "pairing"))
    assert goal_matches_conclusion(other_name, _CONJUNCTION_WITH_USER_TUPLE) is True


def test_the_two_sides_of_an_encoded_goal_are_applications_of_one_symbol():
    pair = parse_twee_proof(_PROOF_TUPLE_IS_A_USER_FUNCTION)
    left, right = pair.goal.equation.lhs, pair.goal.equation.rhs
    mixed = dataclasses.replace(
        pair, goal=dataclasses.replace(
            pair.goal, equation=TweeEquation(left, Function("pairing", list(right.args)))))
    assert goal_matches_conclusion(mixed, _CONJUNCTION_WITH_USER_TUPLE) is False


def test_a_goal_that_wraps_a_single_conjunct_in_an_encoding_is_not_that_conjunct():
    """A conclusion of one equation is never encoded; ``tuple(f(aa)) = tuple(bb)`` is a
    different equation, though a congruence step proves it from ``f(aa) = bb``."""
    premise = _eq(_app("f", _AA), _BB)
    wrapped_lhs, wrapped_rhs = _app("tuple", _app("f", _AA)), _app("tuple", _BB)
    proof = _one_step_proof(_app("f", _AA), _BB, wrapped_lhs, wrapped_rhs)
    # the chain is not a rewrite of the cited axiom at the root, but one inside the wrapper
    assert goal_matches_conclusion(proof, premise) is False


def test_the_encoding_symbol_is_not_a_name_a_variable_of_the_conclusion_is_bound_to():
    """Premises ``∀y f(y) = y`` and ``∀y g(y) = y``; the conclusion ``∀x (f(x) = x ∧ g(x) =
    x)`` is proved by the goal at a constant ``c``. With ``c`` also the name of the encoding
    symbol the goal's two roles of one name are told apart by nobody."""
    premises = [_all(_Y, _eq(_app("f", _Y), _Y)), _all(_Y, _eq(_app("g", _Y), _Y))]
    claim = _all(_X, _and(_eq(_app("f", _X), _X), _eq(_app("g", _X), _X)))
    c = Constant("kt")

    def encoded(symbol):
        left = _app(symbol, _app("f", c), _app("g", c))
        middle = _app(symbol, c, _app("g", c))
        right = _app(symbol, c, c)
        return TweeProof(
            axioms=(TweeAxiom(1, "premise_1", TweeEquation(_app("f", Variable("X")), Variable("X"))),
                    TweeAxiom(2, "premise_2", TweeEquation(_app("g", Variable("X")), Variable("X")))),
            lemmas=(),
            goal=TweeGoal(1, "goal", TweeEquation(left, right), TweeChain(
                (left, middle, right),
                (TweeCitation("axiom", 1, "premise_1"), TweeCitation("axiom", 2, "premise_2")))))

    assert check_twee_proof(encoded("pairing"), premises).ok
    assert goal_matches_conclusion(encoded("pairing"), claim) is True
    assert check_twee_proof(encoded("kt"), premises).ok
    assert goal_matches_conclusion(encoded("kt"), claim) is False


# ---------------------------------------------------------------------------
# A free variable is one unknown element, in a premise and in a conclusion
# ---------------------------------------------------------------------------

def test_a_conclusion_with_a_free_variable_is_refused_by_name():
    """Premise ``f(aa) = aa``, conclusion ``f(x) = x`` with ``x`` free (one unknown element):
    it does not follow, universe ``{0, 1}``, ``x`` ↦ 1, ``aa`` ↦ 0, ``f`` ↦ (0, 0). The goal
    ``f(aa) = aa`` is its instance at ``aa``."""
    premise = _eq(_app("f", _AA), _AA)
    proof = _one_step_proof(_app("f", _AA), _AA, _app("f", _AA), _AA)
    free_claim = _eq(_app("f", _X), _X)
    assert goal_matches_conclusion(proof, free_claim) is False
    assert "free variable" in goal_mismatch(proof, free_claim)
    assert goal_matches_conclusion(proof, premise) is True


def test_a_premise_with_a_free_variable_is_not_a_universal_axiom():
    """The premise ``f(x) = x`` with ``x`` free says something about one element. The axiom
    ``f(X) = X`` Twee would restate says it of every element, and proves ``f(aa) = aa``,
    which the premise does not: universe ``{0, 1}``, ``x`` ↦ 0, ``f`` ↦ (0, 0), ``aa`` ↦ 1."""
    premise = _eq(_app("f", _X), _X)
    proof = _one_step_proof(_app("f", Variable("X")), Variable("X"), _app("f", _AA), _AA)
    result = check_twee_proof(proof, [premise])
    assert result.ok is False
    assert "free variable" in result.error
    assert check_twee_proof(proof, [_all(_X, premise)]).ok


# ---------------------------------------------------------------------------
# Real Twee, through WSL
# ---------------------------------------------------------------------------

_TWEE = twee_available()
needs_twee = pytest.mark.skipif(not _TWEE, reason="no Twee binary reachable via WSL")


@needs_twee
def test_live_a_conjunction_over_a_function_named_tuple_is_proved_as_z3_proves_it():
    """Premise ``∀x aa = x`` makes the universe one element, so every equation holds."""
    verdict = api.prove(_CONJUNCTION_WITH_USER_TUPLE, [_EVERYTHING_IS_AA], backends=["twee"],
                        timeout=30000)
    assert verdict.status == "proved", (verdict.reason, verdict.detail)
    z3_verdict = api.prove(_CONJUNCTION_WITH_USER_TUPLE, [_EVERYTHING_IS_AA], backends=["z3"],
                           timeout=30000)
    assert z3_verdict.status == "proved"


@needs_twee
def test_live_a_conjunction_over_functions_named_tuple_and_tuple2_is_proved():
    conjunction = _and(_eq(_app("tuple", _BB, _CC), _DD), _eq(_app("tuple2", _BB, _CC), _DD),
                       _eq(_EE, _FF))
    verdict = api.prove(conjunction, [_EVERYTHING_IS_AA], backends=["twee"], timeout=30000)
    assert verdict.status == "proved", (verdict.reason, verdict.detail)


@needs_twee
def test_live_a_universal_claim_whose_skolem_name_is_taken_is_still_proved():
    """The premises already have a function ``x``, so Twee calls its Skolem constant ``x2``:
    ``∀y f(f(y)) = y`` proves ``∀x f(f(x)) = x`` by instantiation."""
    premises = [_all(_Y, _eq(_app("f", _app("f", _Y)), _Y)), _eq(_app("x", _AA), _AA)]
    claim = _all(_X, _eq(_app("f", _app("f", _X)), _X))
    verdict = api.prove(claim, premises, backends=["twee"], timeout=30000)
    assert verdict.status == "proved", (verdict.reason, verdict.detail)


@needs_twee
def test_live_the_instance_is_not_proved_for_the_universal_claim():
    """Twee answers the two problems of the tampered proofs above as the countermodels do:
    never proved."""
    ground = api.prove(_all(_X, _eq(_app("f", _X), _app("g", _X))),
                       [_eq(_app("f", _AA), _app("g", _AA))], backends=["twee"], timeout=30000)
    assert ground.status == "refuted", (ground.reason, ground.detail)
    pair = _and(_eq(_app("f", _AA), _BB), _eq(_app("g", _AA), _CC))
    encoded = api.prove(pair, [_eq(_app("tuple", _app("f", _AA), _app("g", _AA)),
                                   _app("tuple", _BB, _CC))], backends=["twee"], timeout=30000)
    assert encoded.status == "refuted", (encoded.reason, encoded.detail)


# ---------------------------------------------------------------------------
# The backend says which name made it refuse
# ---------------------------------------------------------------------------

def test_the_verdict_for_a_goal_at_a_constant_of_the_problem_names_the_constant(monkeypatch):
    premise = _eq(_app("f", _AA), _app("g", _AA))
    proof = _one_step_proof(_app("f", _AA), _app("g", _AA), _app("f", _AA), _app("g", _AA))
    monkeypatch.setattr(
        "unicode_fol_kit.atp.twee_entailment.check_entailment_twee_detailed",
        lambda *args, **kwargs: {"status": "Theorem", "raw_output": "stub", "proof": proof,
                                 "timed_out": False})
    verdict = TweeBackend().decide(_all(_X, _eq(_app("f", _X), _app("g", _X))), [premise])
    assert verdict.status == "error" and verdict.reason == "infra"
    assert "does not restate" in verdict.detail
    assert "aa" in verdict.detail


# ---------------------------------------------------------------------------
# A function of no arguments is the constant of its name
# ---------------------------------------------------------------------------

def test_a_proof_about_a_constant_checks_against_premises_that_write_it_as_a_function_of_no_arguments():
    """The problem writer writes ``fzero()`` as the constant ``fzero`` and Twee prints it so: the
    premise ``fzero() = aa`` is the equation of the proof's axiom ``fzero = aa``."""
    premise = _eq(Function("fzero", []), _AA)
    proof = _one_step_proof(Constant("fzero"), _AA, Constant("fzero"), _AA)
    assert check_twee_proof(proof, [premise]).ok
    assert goal_matches_conclusion(proof, premise) is True
    assert goal_matches_conclusion(proof, _eq(Constant("fzero"), _AA)) is True


@needs_twee
def test_live_twee_reads_a_function_of_no_arguments_as_the_constant_of_its_name():
    """``fzero() = aa`` and ``aa = bb`` give ``fzero = bb``, and not ``fzero = cc``."""
    zero = Function("fzero", [])
    premises = [_eq(zero, _AA), _eq(_AA, _BB)]
    assert api.prove(_eq(zero, _BB), premises, backends=["twee"], timeout=30000).status == "proved"
    assert api.prove(_eq(Constant("fzero"), _BB), premises, backends=["twee"],
                     timeout=30000).status == "proved"
    assert api.prove(_eq(zero, _CC), premises, backends=["twee"], timeout=30000).status == "refuted"
