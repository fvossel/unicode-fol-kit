"""Tests for the Fitch-style natural-deduction checker (unicode_fol_kit.atp.fitch).

The soundness backbone mirrors the resolution suite: every proof the checker
ACCEPTS is cross-checked against an independent oracle, and the critical invariant
is ``not (accepted and not oracle_valid)`` — the checker must never license a step
that the oracle reports invalid.

- Classical FOL/MSFOL: the oracle is Z3 ``is_valid`` (with ⊥ desugared to a genuine
  contradiction) AND the resolution prover; every ACCEPTED proof is audited
  line-by-line — each derived line's open assumptions must entail it.
- K3/LP: the oracle is the three-valued decision procedure ``manyvalued.entails``;
  the headline paraconsistency facts are pinned (LP rejects modus ponens, the
  disjunctive syllogism, and explosion; K3 has no tautologies).
- Modal: the standard-translation/Z3 certifier is exercised on the characteristic
  axioms and the factivity discipline (Knows factive; Believes/Obligatory not).

Single lowercase letters are VARIABLES in this kit, so ground constants are built
explicitly as ``Constant("a")`` and proofs use closed sentences.
"""

import random

import pytest

from unicode_fol_kit import MSFLParser
from unicode_fol_kit.fol.nodes import (
    Atom, Not, And, Or, Xor, Implies, Iff, Quantifier, Variable, Constant,
    Box, Diamond, Knows, Believes, Obligatory, Permitted,
)
from unicode_fol_kit.atp.fitch import (
    Proof, Subproof, Justification, Line, ProofResult,
    premise, assume, line, flag, FALSUM,
    check_proof, verify_proof, render_fitch, render_latex_fitch,
    _classical_valid, _index, _open_assumptions, _subst_var, _free_vars,
)
from unicode_fol_kit.atp.resolution import prove as res_prove

P = Atom("P", [])
Q = Atom("Q", [])
R = Atom("R", [])
S = Atom("S", [])

_FOL = MSFLParser()


def parse(s):
    """Parse a Unicode formula string (uppercase atoms are propositional letters)."""
    return _FOL.parse(s)


def ALL(v, f):
    """Build ``∀v f`` for a Variable v."""
    return Quantifier("∀", v, f)


def EX(v, f):
    """Build ``∃v f`` for a Variable v."""
    return Quantifier("∃", v, f)


# ---------------------------------------------------------------------------
# Soundness audit helper: every derived line must follow from its open assumptions
# ---------------------------------------------------------------------------

def audit_classical_sound(proof):
    """Return True iff every derived line is a classical consequence of its open
    assumptions (the per-line soundness condition), via the Z3 oracle.

    A correct checker that ACCEPTS a proof must satisfy this for every line; the
    randomized tests assert ``check_proof(proof) ⇒ audit_classical_sound(proof)``.
    """
    order, lines, subs, sub_by_sid = _index(proof)
    premise_formulas = [p.formula for p in proof.premises]
    for rec in order:
        if rec.role == "derived":
            oa = _open_assumptions(rec, sub_by_sid, premise_formulas)
            if not _classical_valid(oa, rec.formula):
                return False
    return True


# ---------------------------------------------------------------------------
# Curated valid classical proofs (each hand-verified)
# ---------------------------------------------------------------------------

def _hs_proof():
    """P→Q, Q→R ⊢ P→R (hypothetical syllogism via nested →I)."""
    return Proof(
        premises=[premise(1, Implies(P, Q)), premise(2, Implies(Q, R))],
        steps=[
            Subproof(assumption=assume(3, P),
                     body=[line(4, Q, "→E", 1, 3), line(5, R, "→E", 2, 4)]),
            line(6, Implies(P, R), "→I", (3, 5)),
        ],
    )


def _lem_proof():
    """⊢ P ∨ ¬P (excluded middle via RAA + ⊥I)."""
    return Proof(
        steps=[
            Subproof(
                assumption=assume(1, Not(Or(P, Not(P)))),
                body=[
                    Subproof(assumption=assume(2, P),
                             body=[line(3, Or(P, Not(P)), "∨I", 2),
                                   line(4, FALSUM, "⊥I", 3, 1)]),
                    line(5, Not(P), "¬I", (2, 4)),
                    line(6, Or(P, Not(P)), "∨I", 5),
                    line(7, FALSUM, "⊥I", 6, 1),
                ],
            ),
            line(8, Or(P, Not(P)), "RAA", (1, 7)),
        ],
    )


def _demorgan_proof():
    """¬(P ∨ Q) ⊢ ¬P ∧ ¬Q (one De Morgan direction)."""
    return Proof(
        premises=[premise(1, Not(Or(P, Q)))],
        steps=[
            Subproof(assumption=assume(2, P),
                     body=[line(3, Or(P, Q), "∨I", 2), line(4, FALSUM, "⊥I", 3, 1)]),
            line(5, Not(P), "¬I", (2, 4)),
            Subproof(assumption=assume(6, Q),
                     body=[line(7, Or(P, Q), "∨I", 6), line(8, FALSUM, "⊥I", 7, 1)]),
            line(9, Not(Q), "¬I", (6, 8)),
            line(10, And(Not(P), Not(Q)), "∧I", 5, 9),
        ],
    )


def _disjunctive_syllogism_proof():
    """P∨Q, ¬P ⊢ Q (∨E with ⊥E in the impossible branch)."""
    return Proof(
        premises=[premise(1, Or(P, Q)), premise(2, Not(P))],
        steps=[
            Subproof(assumption=assume(3, P),
                     body=[line(4, FALSUM, "⊥I", 3, 2), line(5, Q, "⊥E", 4)]),
            Subproof(assumption=assume(6, Q), body=[line(7, Q, "Reit", 6)]),
            line(8, Q, "∨E", 1, (3, 5), (6, 7)),
        ],
    )


def _biconditional_proof():
    """P→Q, Q→P ⊢ P↔Q (↔I from two subproofs)."""
    return Proof(
        premises=[premise(1, Implies(P, Q)), premise(2, Implies(Q, P))],
        steps=[
            Subproof(assumption=assume(3, P), body=[line(4, Q, "→E", 1, 3)]),
            Subproof(assumption=assume(5, Q), body=[line(6, P, "→E", 2, 5)]),
            line(7, Iff(P, Q), "↔I", (3, 4), (5, 6)),
        ],
    )


def _dne_proof():
    """¬¬P ⊢ P (double-negation elimination)."""
    return Proof(premises=[premise(1, Not(Not(P)))], steps=[line(2, P, "¬E", 1)])


CURATED_VALID = [
    _hs_proof, _lem_proof, _demorgan_proof,
    _disjunctive_syllogism_proof, _biconditional_proof, _dne_proof,
]


@pytest.mark.parametrize("builder", CURATED_VALID, ids=lambda b: b.__name__)
def test_curated_valid_accepted(builder):
    proof = builder()
    result = verify_proof(proof)
    assert result.ok, result.error


@pytest.mark.parametrize("builder", CURATED_VALID, ids=lambda b: b.__name__)
def test_curated_valid_is_z3_sound(builder):
    # Every accepted proof's sequent (premises ⊢ conclusion) is genuinely Z3-valid,
    # and every individual line follows from its open assumptions.
    proof = builder()
    result = verify_proof(proof)
    assert result.ok
    assert _classical_valid(list(result.premises), result.conclusion)
    assert audit_classical_sound(proof)


@pytest.mark.parametrize("builder", CURATED_VALID, ids=lambda b: b.__name__)
def test_curated_valid_agrees_with_resolution(builder):
    # The whole-proof sequent must also be provable by the independent resolution
    # prover (no equality involved in these proofs).
    proof = builder()
    result = verify_proof(proof)
    assert res_prove(list(result.premises), result.conclusion) is True


# ---------------------------------------------------------------------------
# Soundness guards: deliberately broken proofs must be REJECTED
# ---------------------------------------------------------------------------

def test_reject_wrong_modus_ponens_antecedent():
    bad = Proof(premises=[premise(1, Implies(P, Q)), premise(2, R)],
                steps=[line(3, Q, "→E", 1, 2)])
    assert check_proof(bad) is False


def test_reject_citation_into_closed_subproof():
    # Line 3 lives inside a closed subproof and is not accessible at line 4.
    bad = Proof(
        premises=[premise(1, P)],
        steps=[
            Subproof(assumption=assume(2, Q), body=[line(3, And(P, Q), "∧I", 1, 2)]),
            line(4, And(P, Q), "Reit", 3),
        ],
    )
    r = verify_proof(bad)
    assert r.ok is False
    assert "not in scope" in r.error


def test_reject_forward_reference():
    bad = Proof(premises=[premise(1, P)],
                steps=[line(2, P, "Reit", 3), line(3, P, "Reit", 1)])
    assert check_proof(bad) is False


def test_reject_bad_numbering():
    bad = Proof(premises=[premise(1, P)], steps=[line(3, P, "Reit", 1)])
    r = verify_proof(bad)
    assert r.ok is False
    assert "1..N" in r.error


def test_reject_falsum_intro_without_contradiction():
    bad = Proof(premises=[premise(1, P), premise(2, Q)],
                steps=[line(3, FALSUM, "⊥I", 1, 2)])
    assert check_proof(bad) is False


def test_reject_andi_wrong_order():
    bad = Proof(premises=[premise(1, P), premise(2, Q)],
                steps=[line(3, And(Q, P), "∧I", 1, 2)])
    assert check_proof(bad) is False


def test_reject_imp_intro_wrong_consequent():
    bad = Proof(
        steps=[
            Subproof(assumption=assume(1, P), body=[line(2, P, "Reit", 1)]),
            line(3, Implies(P, Q), "→I", (1, 2)),
        ],
    )
    assert check_proof(bad) is False


def test_reject_unknown_rule():
    bad = Proof(premises=[premise(1, P)], steps=[line(2, P, "Hocus", 1)])
    r = verify_proof(bad)
    assert r.ok is False
    assert "unknown rule" in r.error


def test_malformed_premise_returns_error_not_crash():
    # Audit regression: a non-Line in proof.premises yields ok=False, not AttributeError.
    sp = Subproof(assumption=assume(1, P), body=[line(2, P, "Reit", 1)])
    bad = Proof(premises=[sp], steps=[line(1, Q, "Reit")])
    r = verify_proof(bad)
    assert r.ok is False and "premises must contain Line" in r.error


def test_malformed_subproof_assumption_returns_error_not_crash():
    # Audit regression: a non-Line Subproof.assumption yields ok=False, not a crash.
    sp = Subproof(assumption=5, body=[line(2, Atom("A", ()), "Reit", 1)])
    bad = Proof(premises=[premise(1, Atom("A", ()))], steps=[sp])
    r = verify_proof(bad)
    assert r.ok is False and "assumption must be a Line" in r.error


def test_mixed_quantifier_spelling_accepted():
    # Audit regression: 'forall'/'∀' (and 'exists'/'∃') must be treated as equal so a
    # valid proof that mixes the spellings is not falsely rejected.
    x, a = Variable("x"), Variable("a")
    word = Quantifier("forall", x, Atom("P", (x,)))
    glyph = Quantifier("∀", x, Atom("P", (x,)))
    p1 = Proof(premises=[premise(1, word)],
               steps=[line(2, Atom("P", (a,)), "∀E", 1, extra=(a,))])
    assert verify_proof(p1).ok
    p2 = Proof(premises=[premise(1, word)], steps=[line(2, glyph, "Reit", 1)])
    assert verify_proof(p2).ok


def test_reject_no_conclusion():
    bad = Proof(premises=[premise(1, P)],
                steps=[Subproof(assumption=assume(2, Q), body=[line(3, Q, "Reit", 2)])])
    r = verify_proof(bad)
    assert r.ok is False


# ---------------------------------------------------------------------------
# Quantifier rules + capture-avoiding substitution
# ---------------------------------------------------------------------------

def test_subst_var_respects_shadowing():
    x = Variable("x")
    a = Constant("a")
    # ∀x Q(x) inside shadows the outer x; only the free P(x) is substituted.
    body = And(Atom("P", [x]), ALL(x, Atom("Q", [x])))
    assert _subst_var(body, x, a) == And(Atom("P", [a]), ALL(x, Atom("Q", [x])))


def test_subst_var_avoids_capture():
    x, y = Variable("x"), Variable("y")
    # Substituting x:=y into ∀y P(x) must NOT capture y; the bound y is renamed.
    captured = ALL(y, And(Atom("P", [x]), Atom("Q", [y])))
    result = _subst_var(captured, x, y)
    assert result != ALL(y, And(Atom("P", [y]), Atom("Q", [y])))


def test_subst_var_respects_count_shadowing():
    # Regression: ∃=n binds its variable exactly as ∀/∃ do. Substituting x:=a must
    # stop at the ∃=2 x binder — walking into it structurally rewrote the bound
    # occurrences AND the binder slot itself, yielding the malformed "∃=2 a Q(a)".
    body = _FOL.parse("P(x) ∧ ∃=2 x (Q(x))")
    result = _subst_var(body, Variable("x"), Constant("c_a"))
    assert result == _FOL.parse("P(c_a) ∧ ∃=2 x (Q(x))")


def test_subst_var_avoids_capture_under_count_and_cardinality():
    # Regression: substituting x:=v must α-rename the binder of ∃=n / |{v : …}|,
    # otherwise the replacement's free v is captured by the counting binder.
    x, v = Variable("x"), Variable("v")
    for src in ("∃=2 v (Votes(x, v))", "|{v : Votes(x, v)}| = 3"):
        result = _subst_var(_FOL.parse(src), x, v)
        assert result != _FOL.parse(src.replace("x", "v"))   # not captured
        assert v in _free_vars(result)                       # the new v stayed free


def test_subst_var_rewrites_slashed_existential_like_the_core():
    # Regression: the IF-logic ∃x/{y} binds x AND carries a slash set naming ENCLOSING
    # binders. The core substitution in fol._msfl_nodes already specifies the three
    # cases; it is the oracle here, so the two implementations cannot drift apart.
    from unicode_fol_kit.fol._msfl_nodes import _subst
    f = MSFLParser(dependence=True).parse("∃x/{y} (R(x, y, z))")
    cases = [
        (Variable("y"), Variable("w")),      # slash name → variable: entry renamed
        (Variable("y"), Constant("c_a")),    # slash name → ground term: entry dropped
        (Variable("z"), Variable("x")),      # matrix var whose replacement the binder
                                             # would capture: binder α-renamed
    ]
    for target, repl in cases:
        fv = {repl} if isinstance(repl, Variable) else set()
        assert _subst_var(f, target, repl) == _subst(f, target, repl, fv)


def test_subst_var_slash_set_survives_shadowing_and_degrades_when_emptied():
    # The slash set is NOT shadowed by the binder's own variable (it names enclosing
    # binders), and SlashedExists requires a non-empty slash set — so emptying it must
    # degrade the node to a plain ∃ rather than build an invalid one.
    f = MSFLParser(dependence=True).parse("∃x/{y} (R(x, y))")
    renamed = _subst_var(f, Variable("y"), Variable("w"))
    assert renamed.slashed == ("w",)                      # rewritten, not shadowed
    degraded = _subst_var(f, Variable("y"), Constant("c_a"))
    assert isinstance(degraded, Quantifier) and degraded.type == "∃"
    assert degraded == MSFLParser().parse("∃x (R(x, c_a))")


def test_universal_elimination_rejects_capturing_instance_under_count():
    # Soundness regression, end-to-end: ∀x ∃=2 y R(x, y) does NOT entail
    # ∃=2 y R(y, y) — countermodel: domain {0,1,2} with R(x, y) iff y ≠ x, where
    # every x has exactly two R-successors but the diagonal is empty. Before the
    # binder fix ∀E computed the captured instance and licensed exactly this step.
    proof = Proof(
        premises=[premise(1, _FOL.parse("∀x (∃=2 y (R(x, y)))"))],
        steps=[line(2, _FOL.parse("∃=2 y (R(y, y))"), "∀E", 1, extra=[Variable("y")])],
    )
    result = verify_proof(proof)
    assert result.ok is False


def test_socrates_universal_instantiation():
    x = Variable("x")
    soc = Constant("socrates")
    proof = Proof(
        premises=[premise(1, ALL(x, Implies(Atom("Human", [x]), Atom("Mortal", [x])))),
                  premise(2, Atom("Human", [soc]))],
        steps=[line(3, Implies(Atom("Human", [soc]), Atom("Mortal", [soc])),
                    "∀E", 1, extra=[soc]),
               line(4, Atom("Mortal", [soc]), "→E", 3, 2)],
    )
    result = verify_proof(proof)
    assert result.ok, result.error
    assert _classical_valid(list(result.premises), result.conclusion)


def test_mixed_quantifier_spelling_accepted():
    # Regression: a ∀E step whose premise spells the quantifier 'forall' (not '∀')
    # must still be accepted — _canon_q normalises the spelling before structural ==.
    x, c = Variable("x"), Constant("c")
    word_form = Quantifier("forall", x, Atom("P", [x]))
    proof = Proof(premises=[premise(1, word_form)],
                  steps=[line(2, Atom("P", [c]), "∀E", 1, extra=[c])])
    assert verify_proof(proof).ok is True


def test_non_line_premise_returns_clean_error():
    # Regression: a non-Line in proof.premises must yield ProofResult(ok=False),
    # not an uncaught AttributeError.
    r = verify_proof(Proof(premises=["not a line"], steps=[line(1, P, "Reit", 1)]))
    assert r.ok is False
    assert "Line" in r.error


def test_non_line_subproof_assumption_returns_clean_error():
    # Regression: a non-Line Subproof.assumption must yield ProofResult(ok=False).
    r = verify_proof(Proof(premises=[], steps=[Subproof(assumption="nope", body=[])]))
    assert r.ok is False
    assert "Line" in r.error


def test_existential_elimination():
    x = Variable("x")
    proof = Proof(
        premises=[premise(1, EX(x, Atom("P", [x]))),
                  premise(2, ALL(x, Implies(Atom("P", [x]), Atom("Q", [x]))))],
        steps=[
            Subproof(
                assumption=assume(3, Atom("P", [x])), flag=x,
                body=[
                    line(4, Implies(Atom("P", [x]), Atom("Q", [x])), "∀E", 2, extra=[x]),
                    line(5, Atom("Q", [x]), "→E", 4, 3),
                    line(6, EX(x, Atom("Q", [x])), "∃I", 5, extra=[x]),
                ],
            ),
            line(7, EX(x, Atom("Q", [x])), "∃E", 1, (3, 6)),
        ],
    )
    result = verify_proof(proof)
    assert result.ok, result.error
    assert _classical_valid(list(result.premises), result.conclusion)


def test_reject_universal_intro_eigenvariable_in_premise():
    x = Variable("x")
    bad = Proof(
        premises=[premise(1, Atom("P", [x]))],
        steps=[
            Subproof(assumption=flag(2, x), flag=x, body=[line(3, Atom("P", [x]), "Reit", 1)]),
            line(4, ALL(x, Atom("P", [x])), "∀I", (2, 3)),
        ],
    )
    r = verify_proof(bad)
    assert r.ok is False
    assert "eigenvariable" in r.error


def test_reject_forall_intro_box_that_discharges_hypothesis():
    # Regression: a ∀I box that ALSO discharges a hypothesis P(e) mentioning the
    # eigenvariable must be rejected. Otherwise ⊢ ∀x P(x) is "provable" from nothing
    # (the hypothesis is invisible to the freshness check, which runs outside the box).
    x, e = Variable("x"), Variable("e")
    unsound = Proof(
        steps=[
            Subproof(
                assumption=assume(1, Atom("P", [e])),  # an Assume head, not a Flag head
                body=[line(2, Atom("P", [e]), "Reit", 1)],
                flag=e,
            ),
            line(3, ALL(x, Atom("P", [x])), "∀I", (1, 2)),
        ],
    )
    r = verify_proof(unsound)
    assert r.ok is False
    assert "pure eigenvariable box" in r.error
    # And the "conclusion" really is invalid, so accepting it would be unsound.
    from unicode_fol_kit import is_valid
    assert is_valid(ALL(x, Atom("P", [x]))) is False


def test_reject_existential_elim_eigenvariable_in_conclusion():
    x = Variable("x")
    bad = Proof(
        premises=[premise(1, EX(x, Atom("P", [x])))],
        steps=[
            Subproof(assumption=assume(2, Atom("P", [x])), flag=x,
                     body=[line(3, Atom("P", [x]), "Reit", 2)]),
            line(4, Atom("P", [x]), "∃E", 1, (2, 3)),
        ],
    )
    r = verify_proof(bad)
    assert r.ok is False
    assert "eigenvariable" in r.error


# ---------------------------------------------------------------------------
# Equality rules (Z3-certified)
# ---------------------------------------------------------------------------

def test_equality_reflexivity():
    a = Constant("a")
    assert check_proof(Proof(steps=[line(1, Atom("=", [a, a]), "=I")])) is True


def test_equality_elimination():
    a, b = Constant("a"), Constant("b")
    proof = Proof(
        premises=[premise(1, Atom("=", [a, b])), premise(2, Atom("P", [a]))],
        steps=[line(3, Atom("P", [b]), "=E", 1, 2)],
    )
    assert check_proof(proof) is True


def test_equality_elimination_unsound_rejected():
    a, b, c = Constant("a"), Constant("b"), Constant("c")
    bad = Proof(
        premises=[premise(1, Atom("=", [a, b])), premise(2, Atom("P", [a]))],
        steps=[line(3, Atom("P", [c]), "=E", 1, 2)],
    )
    assert check_proof(bad) is False


# ---------------------------------------------------------------------------
# Randomized soundness audit (the heart of the soundness check)
# ---------------------------------------------------------------------------

_ATOMS = [P, Q, R, S]


def _rand_formula(rng, depth=2):
    """A random propositional formula over P, Q, R, S (sometimes ⊥)."""
    if depth <= 0 or rng.random() < 0.45:
        a = rng.choice(_ATOMS)
        return Not(a) if rng.random() < 0.3 else a
    choice = rng.choice([And, Or, Implies, Iff, "not", "falsum"])
    if choice == "not":
        return Not(_rand_formula(rng, depth - 1))
    if choice == "falsum":
        return FALSUM
    return choice(_rand_formula(rng, depth - 1), _rand_formula(rng, depth - 1))


_PROP_RULES = ["Reit", "∧I", "∧E", "∨I", "∨E", "→E", "↔E", "⊥I", "⊥E", "¬E"]


def _constructed_valid_step(rng, num, visible):
    """Try to build a genuinely-valid derived line from ``visible`` (num, formula)s.

    Returns a Line or None. These guarantee the random batch contains accepted
    proofs (so the soundness audit is non-vacuous) while still being checked by
    the independent oracle.
    """
    if not visible:
        return None
    forms = {n: f for n, f in visible}
    nums = list(forms)
    kind = rng.choice(["reit", "andi", "ande", "ori", "impe", "bote"])
    if kind == "reit":
        n = rng.choice(nums)
        return line(num, forms[n], "Reit", n)
    if kind == "andi":
        n1, n2 = rng.choice(nums), rng.choice(nums)
        return line(num, And(forms[n1], forms[n2]), "∧I", n1, n2)
    if kind == "ande":
        ands = [n for n in nums if isinstance(forms[n], And)]
        if ands:
            n = rng.choice(ands)
            side = forms[n].left if rng.random() < 0.5 else forms[n].right
            return line(num, side, "∧E", n)
    if kind == "ori":
        n = rng.choice(nums)
        other = _rand_formula(rng, 1)
        if rng.random() < 0.5:
            return line(num, Or(forms[n], other), "∨I", n)
        return line(num, Or(other, forms[n]), "∨I", n)
    if kind == "impe":
        for n in nums:
            f = forms[n]
            if isinstance(f, Implies):
                anteced = [m for m in nums if forms[m] == f.left]
                if anteced:
                    return line(num, f.right, "→E", n, rng.choice(anteced))
    if kind == "bote":
        bots = [n for n in nums if n is not None and forms[n] == FALSUM]
        if bots:
            return line(num, _rand_formula(rng, 1), "⊥E", rng.choice(bots))
    return None


def _random_flat_proof(rng):
    """A random flat proof (premises + derived lines), biased to be accept-able."""
    num = 1
    premises = []
    for _ in range(rng.randint(1, 3)):
        premises.append(premise(num, _rand_formula(rng)))
        num += 1
    visible = [(p.number, p.formula) for p in premises]
    steps = []
    for _ in range(rng.randint(1, 4)):
        st = None
        if rng.random() < 0.6:
            st = _constructed_valid_step(rng, num, visible)
        if st is None:
            cites = tuple(rng.sample([n for n, _ in visible],
                                     rng.randint(0, min(2, len(visible)))))
            st = line(num, _rand_formula(rng), rng.choice(_PROP_RULES), *cites)
        steps.append(st)
        visible.append((st.number, st.formula))
        num += 1
    return Proof(premises=premises, steps=steps)


def _random_subproof_proof(rng):
    """A random proof containing one subproof, sometimes a valid →I/¬I discharge."""
    num = 1
    premises = []
    for _ in range(rng.randint(0, 2)):
        premises.append(premise(num, _rand_formula(rng)))
        num += 1
    outer_visible = [(p.number, p.formula) for p in premises]

    assum = _rand_formula(rng)
    a_num = num
    num += 1
    inner_visible = list(outer_visible) + [(a_num, assum)]
    body = []
    for _ in range(rng.randint(1, 2)):
        st = None
        if rng.random() < 0.6:
            st = _constructed_valid_step(rng, num, inner_visible)
        if st is None:
            cites = tuple(rng.sample([n for n, _ in inner_visible],
                                     rng.randint(0, min(2, len(inner_visible)))))
            st = line(num, _rand_formula(rng), rng.choice(_PROP_RULES), *cites)
        body.append(st)
        inner_visible.append((st.number, st.formula))
        num += 1
    sub = Subproof(assumption=assume(a_num, assum), body=body)
    span = (a_num, body[-1].number)
    steps = [sub]
    last_concl = body[-1].formula

    # A genuinely valid discharge sometimes; otherwise a random discharge.
    if rng.random() < 0.5:
        discharge = line(num, Implies(assum, last_concl), "→I", span)
    elif rng.random() < 0.5 and last_concl == FALSUM:
        discharge = line(num, Not(assum), "¬I", span)
    else:
        discharge = line(num, _rand_formula(rng), rng.choice(["→I", "¬I", "RAA"]), span)
    steps.append(discharge)
    return Proof(premises=premises, steps=steps)


def test_random_flat_proofs_are_sound():
    rng = random.Random(20260626)
    accepted = 0
    for _ in range(1500):
        proof = _random_flat_proof(rng)
        if check_proof(proof):
            accepted += 1
            assert audit_classical_sound(proof), ("UNSOUND:\n" + render_fitch(proof))
    assert accepted > 0  # the audit is non-vacuous


def test_random_subproof_proofs_are_sound():
    rng = random.Random(13371337)
    accepted = 0
    for _ in range(1500):
        proof = _random_subproof_proof(rng)
        if check_proof(proof):
            accepted += 1
            assert audit_classical_sound(proof), ("UNSOUND:\n" + render_fitch(proof))
    assert accepted > 0  # genuine discharge proofs were accepted and audited


# ---------------------------------------------------------------------------
# K3 / LP (three-valued) — paraconsistency facts
# ---------------------------------------------------------------------------

def test_lp_rejects_modus_ponens():
    proof = Proof(premises=[premise(1, P), premise(2, Implies(P, Q))],
                  steps=[line(3, Q, "→E", 2, 1)], logic="LP")
    assert check_proof(proof) is False


def test_lp_rejects_disjunctive_syllogism():
    proof = Proof(premises=[premise(1, Or(P, Q)), premise(2, Not(P))],
                  steps=[line(3, Q, "DS", 1, 2)], logic="LP")
    assert check_proof(proof) is False


def test_lp_rejects_explosion():
    proof = Proof(premises=[premise(1, P), premise(2, Not(P))],
                  steps=[line(3, Q, "explosion")], logic="LP")
    assert check_proof(proof) is False


def test_k3_rejects_excluded_middle_theorem():
    proof = Proof(steps=[line(1, Or(P, Not(P)), "LEM")], logic="K3")
    assert check_proof(proof) is False


def test_lp_accepts_excluded_middle():
    proof = Proof(steps=[line(1, Or(P, Not(P)), "LEM")], logic="LP")
    assert check_proof(proof) is True


def test_classical_modus_ponens_still_accepted():
    proof = Proof(premises=[premise(1, P), premise(2, Implies(P, Q))],
                  steps=[line(3, Q, "→E", 2, 1)], logic="fol")
    assert check_proof(proof) is True


def test_k3_lp_accept_lattice_rules():
    andi = Proof(premises=[premise(1, P), premise(2, Q)],
                 steps=[line(3, And(P, Q), "∧I", 1, 2)], logic="LP")
    ande = Proof(premises=[premise(1, And(P, Q))],
                 steps=[line(2, P, "∧E", 1)], logic="K3")
    assert check_proof(andi) is True
    assert check_proof(ande) is True


def test_k3_lp_reject_quantified():
    x = Variable("x")
    proof = Proof(premises=[premise(1, ALL(x, Atom("P", [x])))],
                  steps=[line(2, Atom("P", [Constant("a")]), "∀E", 1, extra=[Constant("a")])],
                  logic="K3")
    r = verify_proof(proof)
    assert r.ok is False
    assert "propositional" in r.error


# ---------------------------------------------------------------------------
# Modal family
# ---------------------------------------------------------------------------

def test_modal_T_factivity():
    proof = Proof(premises=[premise(1, Box(P))], steps=[line(2, P, "□E", 1)], logic="T")
    assert check_proof(proof) is True


def test_modal_K_lacks_factivity():
    proof = Proof(premises=[premise(1, Box(P))], steps=[line(2, P, "□E", 1)], logic="K")
    assert check_proof(proof) is False


def test_modal_S4_axiom4():
    proof = Proof(steps=[line(1, Implies(Box(P), Box(Box(P))), "Ax4")], logic="S4")
    assert check_proof(proof) is True


def test_modal_K_lacks_axiom4():
    proof = Proof(steps=[line(1, Implies(Box(P), Box(Box(P))), "Ax4")], logic="K")
    assert check_proof(proof) is False


def test_modal_K_distribution_axiom():
    ax = Implies(Box(Implies(P, Q)), Implies(Box(P), Box(Q)))
    assert check_proof(Proof(steps=[line(1, ax, "K")], logic="K")) is True


def test_modal_necessitation_of_tautology():
    assert check_proof(Proof(steps=[line(1, Box(Or(P, Not(P))), "Nec")], logic="K")) is True


def test_modal_contingent_necessitation_rejected():
    proof = Proof(premises=[premise(1, P)], steps=[line(2, Box(P), "Nec")], logic="S5")
    assert check_proof(proof) is False


def test_epistemic_knowledge_is_factive():
    proof = Proof(premises=[premise(1, Knows("a", P))], steps=[line(2, P, "T", 1)], logic="S5")
    assert check_proof(proof) is True


def test_doxastic_belief_is_not_factive():
    proof = Proof(premises=[premise(1, Believes("a", P))], steps=[line(2, P, "T?", 1)], logic="S5")
    assert check_proof(proof) is False


def test_doxastic_consistency_axiom():
    proof = Proof(premises=[premise(1, Believes("a", P))],
                  steps=[line(2, Not(Believes("a", Not(P))), "D", 1)], logic="K")
    assert check_proof(proof) is True


def test_deontic_obligation_not_factive():
    proof = Proof(premises=[premise(1, Obligatory(P))], steps=[line(2, P, "T?", 1)], logic="K")
    assert check_proof(proof) is False


def test_deontic_ought_implies_permitted():
    proof = Proof(premises=[premise(1, Obligatory(P))],
                  steps=[line(2, Permitted(P), "D", 1)], logic="K")
    assert check_proof(proof) is True


def test_modal_predicate_name_collision_rejected():
    # Regression: a user predicate named like an accessibility relation ("R") must
    # be rejected with a clear message, not crash the Z3 backend.
    r_atom = Atom("R", [Constant("a")])
    proof = Proof(premises=[premise(1, Box(r_atom))],
                  steps=[line(2, r_atom, "□E", 1)], logic="T")
    r = verify_proof(proof)
    assert r.ok is False
    assert "collides" in r.error


def test_modal_rejects_temporal_operators():
    from unicode_fol_kit.fol.nodes import Always
    proof = Proof(steps=[line(1, Implies(Always(P), P), "?")], logic="S4")
    r = verify_proof(proof)
    assert r.ok is False
    assert "temporal" in r.error


# ---------------------------------------------------------------------------
# Serialization round-trip and rendering
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("builder", CURATED_VALID, ids=lambda b: b.__name__)
def test_proof_dict_round_trip(builder):
    proof = builder()
    assert Proof.from_dict(proof.to_dict()) == proof


def test_render_fitch_structure():
    text = render_fitch(_hs_proof())
    lines = text.splitlines()
    # Six numbered lines + two Fitch bars (under premises, under the assumption).
    numbered = [ln for ln in lines if ln.lstrip()[:1].isdigit()]
    bars = [ln for ln in lines if "├" in ln]
    assert len(numbered) == 6
    assert len(bars) == 2
    # The subproof body lines carry two scope bars; top-level lines carry one.
    assert "│ │ Q" in text and "│ P → R" in text


def test_render_fitch_ascii_uses_ascii_bars():
    text = render_fitch(_hs_proof(), ascii=True)
    assert "│" not in text and "├" not in text
    assert "|" in text and "+" in text


def test_render_latex_fitch_exact():
    expected = (
        "\\[\n"
        "\\begin{array}{r|l@{\\qquad}l}\n"
        "1 & \\mid P & \\text{Assume} \\\\\n"
        "\\cline{2-2}\n"
        "2 & \\mid P & \\text{Reit 1} \\\\\n"
        "3 & P \\rightarrow P & \\text{$\\rightarrow$I 1$--$2} \\\\\n"
        "\\end{array}\n"
        "\\]"
    )
    proof = Proof(steps=[
        Subproof(assumption=assume(1, P), body=[line(2, P, "Reit", 1)]),
        line(3, Implies(P, P), "→I", (1, 2)),
    ])
    assert render_latex_fitch(proof) == expected


# ---------------------------------------------------------------------------
# Public exports
# ---------------------------------------------------------------------------

def test_top_level_exports():
    import unicode_fol_kit as u
    for name in ("Proof", "Line", "Subproof", "Justification", "ProofResult",
                 "premise", "assume", "line", "flag", "FALSUM",
                 "check_proof", "verify_proof", "render_fitch", "render_latex_fitch"):
        assert hasattr(u, name), name
        assert name in u.__all__, name
