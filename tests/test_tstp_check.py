"""Tests for the independent TSTP-derivation checker (unicode_fol_kit.atp.tstp_check).

Three families, matching the module's own three-tier design (see
``tstp_check.py``'s module docstring):

1. **End-to-end integration against REAL captured prover output** — the
   fixtures in ``tests/fixtures/tstp_check/`` (captured live via
   ``vampire --proof tptp --avatar off``, Vampire 5.0.1, WSL, during this
   module's development) and the pre-existing
   ``tests/fixtures/eprover_3_5_1_theorem.txt`` (real E 3.5.1 output, already
   used by ``tests/test_tstp.py``).
2. **Hand-built accept/reject unit tests per core-checked rule** — a genuine
   small derivation the checker must ACCEPT, and a copy with one thing
   tampered (a flipped literal, a swapped premise, a wrong conclusion) the
   checker must REJECT, for resolution, factoring, superposition,
   demodulation, equality resolution, and subsumption resolution.
3. **Differential tests against `atp.resolution_check`** — two of that
   module's own hand-derived fixtures (part (a)'s end-to-end refutation,
   part (b)'s classic Robinson factoring example), translated to synthetic
   TSTP text by hand, must get the SAME accept/reject verdict from
   :func:`check_tstp_derivation` as :func:`atp.resolution_check
   .verify_resolution_proof` gets from the original :class:`ResolutionDerivation`
   — the same "independent implementation, same answer" oracle
   ``resolution_check.py`` itself already uses against ``fol.unification``.

Every expected value below is hand-derived (see the comment above each
assertion) rather than taken from running the checker first.
"""

from pathlib import Path

import pytest

from unicode_fol_kit.fol.nodes import Atom, Not, Or, Variable, Constant, Function
from unicode_fol_kit.fol.tptp_input import parse_tptp_formula
from unicode_fol_kit.atp.resolution_check import (
    ResolutionStep, ResolutionDerivation, verify_resolution_proof,
)
from unicode_fol_kit.atp.tstp import parse_tstp_derivation
from unicode_fol_kit.atp.tstp_check import (
    check_tstp_derivation,
    VAMPIRE_CHECKED_RULES,
    EPROVER_CLAUSIFICATION_RULES, EPROVER_CHECKED_RULES,
    _node_to_clause, _formula_alpha_equal, _all_positions,
)


def P(*args):
    return Atom("P", list(args))


def Q(*args):
    return Atom("Q", list(args))


x, y, u, v = Variable("x"), Variable("y"), Variable("u"), Variable("v")
a, b = Constant("a"), Constant("b")


def f(t):
    return Function("f", [t])


_FIXTURES = Path(__file__).parent / "fixtures" / "tstp_check"


def _read_fixture(name: str) -> str:
    return (_FIXTURES / name).read_text(encoding="utf-8")


def _eprover_theorem() -> str:
    """Real E 3.5.1 output, shared with test_tstp.py's/
    test_eprover_zipperposition.py's identical `_recorded` helper."""
    path = Path(__file__).parent / "fixtures" / "eprover_3_5_1_theorem.txt"
    return path.read_text(encoding="utf-8")


# ---------------------------------------------------------------------------
# 1. Integration against real captured Vampire output
# ---------------------------------------------------------------------------

class TestVampireRealFixtures:
    def test_superposition_fixture_fully_verifies(self):
        """{! [X,Y]:(r(X,Y) => f(X)=f(Y)), r(a,b), p(f(a))} |- p(f(b)): a
        genuine 'resolution' step (f12) and a genuine 'superposition' step
        (f13, rewriting f(b)->f(a) inside ~p(f(b)) via f(a)=f(b), direction
        'rl') -- every step (leaf/trusted/checked) must verify."""
        d = parse_tstp_derivation(_read_fixture("vampire_superposition.txt"))
        premises = [
            parse_tptp_formula("! [X,Y] : (r(X,Y) => f(X) = f(Y))"),
            parse_tptp_formula("r(a,b)"),
            parse_tptp_formula("p(f(a))"),
        ]
        conclusion = parse_tptp_formula("p(f(b))")
        r = check_tstp_derivation(d, premises, conclusion)
        assert r.verified, r.error
        assert r.refuted is True
        assert bool(r) is True
        assert all(s.ok for s in r.steps)
        tiers = {s.name: s.tier for s in r.steps}
        assert tiers["f12"] == "checked" and tiers["f13"] == "checked"

    def test_equality_resolution_fixture_fully_verifies(self):
        """{! [X]:(X=a => q(X))} |- q(a): a genuine 'equality_resolution'
        step (f8, 1 parent) dropping the negative equation a!=X0 under
        X0|->a."""
        d = parse_tstp_derivation(_read_fixture("vampire_equality_resolution.txt"))
        premises = [parse_tptp_formula("! [X] : (X = a => q(X))")]
        conclusion = parse_tptp_formula("q(a)")
        r = check_tstp_derivation(d, premises, conclusion)
        assert r.verified, r.error
        assert r.refuted is True
        step_by_name = {s.name: s for s in r.steps}
        assert step_by_name["f8"].tier == "checked"

    def test_definition_unfolding_is_refused_loudly(self):
        """{a=b, p(a)} |- p(b): Vampire's own preprocessing uses
        'definition_unfolding' (f9), a rule outside both this module's
        tables -- the WHOLE derivation must come back unverified, naming it,
        never silently accepted."""
        d = parse_tstp_derivation(_read_fixture("vampire_definition_unfolding.txt"))
        premises = [parse_tptp_formula("a = b"), parse_tptp_formula("p(a)")]
        conclusion = parse_tptp_formula("p(b)")
        r = check_tstp_derivation(d, premises, conclusion)
        assert r.verified is False
        assert "definition_unfolding" in r.error
        step_by_name = {s.name: s for s in r.steps}
        assert step_by_name["f9"].tier == "unchecked"
        assert step_by_name["f9"].ok is False

    def test_skolemisation_of_existential_premise_is_honestly_unverified(self):
        """{? [X] : ! [Y] : r(X,Y)} |- ? [X] : r(X,X): Vampire's
        'skolemisation' step (f6) cites, besides the real premise, a second
        parent (f5) sourced `introduced(definition, ...)` stating the
        Skolem-definition implication itself -- a leaf (its source is not
        inference(...)) that is NOT one of the caller's premises. The
        skolemisation step itself is refused by name (tier 'unchecked'): a
        Skolemized formula is not ENTAILED by its parent, only
        equisatisfiable with it, so the entailment check that licenses every
        other clausification step cannot license it (see the module
        docstring, tier 2). The derivation correctly comes back unverified,
        not because anything is actually unsound, but because this checker
        does not certify Skolemization."""
        d = parse_tstp_derivation(_read_fixture("vampire_skolemisation.txt"))
        premises = [parse_tptp_formula("? [X] : ! [Y] : r(X,Y)")]
        conclusion = parse_tptp_formula("? [X] : r(X,X)")
        r = check_tstp_derivation(d, premises, conclusion)
        assert r.verified is False
        step_by_name = {s.name: s for s in r.steps}
        assert step_by_name["f6"].tier == "unchecked"
        assert step_by_name["f6"].ok is False
        assert "only preserves satisfiability" in step_by_name["f6"].detail

    def test_original_theorem_output_resolution_and_subsumption_resolution(self):
        """The exact fixture tests/test_tstp.py's own _THEOREM_OUTPUT carries
        (real vampire --proof tptp, Vampire 5.0.1): {! [X](human(X) =>
        mortal(X)), human(socrates)} |- mortal(socrates), via 'resolution'
        (f10) then 'forward_subsumption_resolution' (f11, -> $false)."""
        text = (
            "fof(f1,axiom,(\n  ! [X0] : (human(X0) => mortal(X0))),\n"
            "  file('mp.p',unknown)).\n"
            "fof(f2,axiom,(\n  human(socrates)),\n  file('mp.p',unknown)).\n"
            "fof(f3,conjecture,(\n  mortal(socrates)),\n  file('mp.p',unknown)).\n"
            "fof(f4,negated_conjecture,(\n  ~mortal(socrates)),\n"
            "  inference(negated_conjecture,[status(cth)],[f3])).\n"
            "fof(f5,plain,(\n  ~mortal(socrates)),\n  inference(flattening,[],[f4])).\n"
            "fof(f6,plain,(\n  ! [X0] : (mortal(X0) | ~human(X0))),\n"
            "  inference(ennf_transformation,[],[f1])).\n"
            "fof(f7,plain,(\n  ( ! [X0] : (~human(X0) | mortal(X0)) )),\n"
            "  inference(cnf_transformation,[],[f6])).\n"
            "fof(f8,plain,(\n  human(socrates)),\n  inference(cnf_transformation,[],[f2])).\n"
            "fof(f9,plain,(\n  ~mortal(socrates)),\n  inference(cnf_transformation,[],[f5])).\n"
            "fof(f10,plain,(\n  mortal(socrates)),\n  inference(resolution,[],[f7,f8])).\n"
            "fof(f11,plain,(\n  $false),\n"
            "  inference(forward_subsumption_resolution,[],[f10,f9])).\n"
        )
        d = parse_tstp_derivation(text)
        premises = [
            parse_tptp_formula("! [X] : (human(X) => mortal(X))"),
            parse_tptp_formula("human(socrates)"),
        ]
        conclusion = parse_tptp_formula("mortal(socrates)")
        r = check_tstp_derivation(d, premises, conclusion)
        assert r.verified, r.error
        assert r.refuted is True
        step_by_name = {s.name: s for s in r.steps}
        assert step_by_name["f10"].tier == "checked"
        assert step_by_name["f11"].tier == "checked"

    def test_wrong_conclusion_makes_leaf_mismatch_fail(self):
        """Same fixture as above, but a WRONG conclusion is supplied: the
        conjecture-role leaf f3 must fail to alpha-match it."""
        text = _read_fixture("vampire_equality_resolution.txt")
        d = parse_tstp_derivation(text)
        premises = [parse_tptp_formula("! [X] : (X = a => q(X))")]
        wrong_conclusion = parse_tptp_formula("q(b)")
        r = check_tstp_derivation(d, premises, wrong_conclusion)
        assert r.verified is False
        assert "leaf" in r.error and "conclusion" in r.error


class TestEproverRealFixture:
    def test_eprover_real_fixture_is_not_fully_verified(self):
        """{! [X](p(X) => q(X)), p(alice)} |- q(alice): E's own 'split_conjunct'
        (trusted) and leaf steps verify, but E nests several intermediate
        rules (fof_nnf/variable_rename/spm/rw) inside ONE compound
        inference(...) parent-list entry that atp.tstp._parse_source
        deliberately does not expand into flat TstpStep.parents (see that
        module's own comment on _deep_ancestor_names) -- so this checker
        honestly cannot resolve those steps' parents, and the whole
        derivation comes back unverified. This is the intentional, documented
        outcome (tstp_check.py's module docstring), not a bug."""
        d = parse_tstp_derivation(_eprover_theorem())
        premises = [
            parse_tptp_formula("![X1]:((p(X1)=>q(X1)))"),
            parse_tptp_formula("p(alice)"),
        ]
        conclusion = parse_tptp_formula("q(alice)")
        r = check_tstp_derivation(d, premises, conclusion)
        assert r.verified is False
        step_by_name = {s.name: s for s in r.steps}
        # The genuine leaves and the two real split_conjunct/negated_conjecture
        # chains DO verify -- only the nested-inference steps fail.
        assert step_by_name["goal"].ok is True
        assert step_by_name["premise_1"].ok is True
        assert step_by_name["premise_2"].ok is True
        assert step_by_name["c_0_9"].ok is True  # split_conjunct <- premise_1, a real leaf
        assert step_by_name["c_0_10"].tier == "unchecked"  # 'cn', never registered
        assert step_by_name["c_0_10"].ok is False


# ---------------------------------------------------------------------------
# 2. Hand-built accept/reject per core-checked rule
# ---------------------------------------------------------------------------

def _refutation_check(text, premises):
    return check_tstp_derivation(parse_tstp_derivation(text), premises, None, query="refutation")


class TestResolutionRule:
    # {p(a)}, {~p(X)|q(X)} -resolution-> {q(a)}, mgu X|->a.
    _TEXT = (
        "cnf(c1, axiom, p(a)).\n"
        "cnf(c2, axiom, (~p(X) | q(X))).\n"
        "cnf(c3, plain, q(a), inference(resolution,[],[c1,c2])).\n"
    )
    _PREMISES = [P(a), Or(Not(P(x)), Q(x))]

    def test_genuine_resolvent_accepted(self):
        r = _refutation_check(self._TEXT, self._PREMISES)
        assert r.verified, r.error

    def test_wrong_resolvent_rejected(self):
        # q(b) is an unrelated ground atom, not the mgu-instantiated q(a).
        bad = self._TEXT.replace("q(a), inference(resolution", "q(b), inference(resolution")
        r = _refutation_check(bad, self._PREMISES)
        assert r.verified is False
        assert "resolution" in r.error


class TestFactoringRule:
    # {p(X)|p(Y)} -factoring-> {p(X)}, mgu X|->Y.
    _TEXT = (
        "cnf(c1, axiom, (p(X) | p(Y))).\n"
        "cnf(c2, plain, p(X), inference(factoring,[],[c1])).\n"
    )
    _PREMISES = [Or(P(x), P(y))]

    def test_genuine_factor_accepted(self):
        r = _refutation_check(self._TEXT, self._PREMISES)
        assert r.verified, r.error

    def test_non_factorable_clause_rejected(self):
        # p(a) does not follow from {p(X)|p(Y)} by factoring at all.
        bad = self._TEXT.replace("plain, p(X), inference(factoring", "plain, p(a), inference(factoring")
        r = _refutation_check(bad, self._PREMISES)
        assert r.verified is False
        assert "factoring" in r.error


class TestSuperpositionRule:
    # {f(a)=f(b)}, {~p(f(b))} -superposition (target first, equation
    # second)-> {~p(f(a))}, direction 'rl' rewriting f(b)->f(a) at position (0,).
    _TEXT = (
        "cnf(c1, axiom, ~p(f(b))).\n"
        "cnf(c2, axiom, (f(a) = f(b))).\n"
        "cnf(c3, plain, ~p(f(a)), inference(superposition,[],[c1,c2])).\n"
    )
    _PREMISES = [Not(P(f(b))), Atom("=", [f(a), f(b)])]

    def test_genuine_rewrite_accepted(self):
        r = _refutation_check(self._TEXT, self._PREMISES)
        assert r.verified, r.error

    def test_rewrite_into_wrong_side_rejected(self):
        # ~p(f(b)) would claim NO rewrite happened at all -- not licensed.
        bad = self._TEXT.replace(
            "plain, ~p(f(a)), inference(superposition", "plain, ~p(f(b)), inference(superposition")
        r = _refutation_check(bad, self._PREMISES)
        assert r.verified is False
        assert "superposition" in r.error


class TestDemodulationRule:
    # {f(g(X))=X} (a unit rewrite rule, oriented left-to-right: f(g(X)) is
    # strictly heavier than X under the term-weight order), {p(f(g(a)))}
    # -forward_demodulation-> {p(a)}.
    _TEXT = (
        "cnf(c1, axiom, (f(g(X)) = X)).\n"
        "cnf(c2, axiom, p(f(g(a)))).\n"
        "cnf(c3, plain, p(a), inference(forward_demodulation,[],[c2,c1])).\n"
    )
    _PREMISES = [Atom("=", [f(Function("g", [x])), x]), P(f(Function("g", [a])))]

    def test_genuine_rewrite_accepted(self):
        r = _refutation_check(self._TEXT, self._PREMISES)
        assert r.verified, r.error

    def test_wrong_target_rejected(self):
        bad = self._TEXT.replace(
            "plain, p(a), inference(forward_demodulation", "plain, p(b), inference(forward_demodulation")
        r = _refutation_check(bad, self._PREMISES)
        assert r.verified is False
        assert "demodulation" in r.error

    def test_reversed_orientation_rejected(self):
        # X -> f(g(X)) is the WRONG direction (X is strictly LIGHTER than
        # f(g(X)), so this does not strictly decrease under the term order);
        # rewriting p(f(g(a))) "backwards" into p(f(g(f(g(a))))) must be
        # rejected by the orientation check, independent of what the
        # derivation claims the direction is.
        bad_text = (
            "cnf(c1, axiom, (f(g(X)) = X)).\n"
            "cnf(c2, axiom, p(f(g(a)))).\n"
            "cnf(c3, plain, p(f(g(f(g(a))))), inference(forward_demodulation,[],[c2,c1])).\n"
        )
        r = _refutation_check(bad_text, self._PREMISES)
        assert r.verified is False
        assert "demodulation" in r.error


class TestEqualityResolutionRule:
    # {q(X)|a!=X} -equality_resolution-> {q(a)}, unifying the negated
    # equation's two sides (a, X) under X|->a and dropping the literal.
    _TEXT = (
        "cnf(c1, axiom, (q(X) | a != X)).\n"
        "cnf(c2, plain, q(a), inference(equality_resolution,[],[c1])).\n"
    )
    _PREMISES = [Or(Q(x), Atom("≠", [a, x]))]

    def test_genuine_drop_accepted(self):
        r = _refutation_check(self._TEXT, self._PREMISES)
        assert r.verified, r.error

    def test_wrong_witness_rejected(self):
        bad = self._TEXT.replace(
            "plain, q(a), inference(equality_resolution", "plain, q(b), inference(equality_resolution")
        r = _refutation_check(bad, self._PREMISES)
        assert r.verified is False
        assert "equality_resolution" in r.error

    def test_clause_with_no_negative_equality_rejected(self):
        bad_text = (
            "cnf(c1, axiom, (q(X) | p(X))).\n"
            "cnf(c2, plain, q(a), inference(equality_resolution,[],[c1])).\n"
        )
        r = _refutation_check(bad_text, [Or(Q(x), P(x))])
        assert r.verified is False
        assert "no negative equality literal" in r.error


class TestSubsumptionResolutionRule:
    # target {p(a)|q(b)}, subsumer {~p(X)} -forward_subsumption_resolution->
    # {q(b)}: p(a)'s complement (~p(X)) one-sided-matches ~p(X) under X|->a,
    # and the subsumer has no other literal to also place -- p(a) is dropped.
    _TEXT = (
        "cnf(c1, axiom, (p(a) | q(b))).\n"
        "cnf(c2, axiom, ~p(X)).\n"
        "cnf(c3, plain, q(b), inference(forward_subsumption_resolution,[],[c1,c2])).\n"
    )
    _PREMISES = [Or(P(a), Q(b)), Not(P(x))]

    def test_genuine_subsumption_resolution_accepted(self):
        r = _refutation_check(self._TEXT, self._PREMISES)
        assert r.verified, r.error

    def test_dropping_the_wrong_literal_rejected(self):
        # Dropping q(b) instead (leaving p(a)) is not licensed: the
        # subsumer's only literal ~p(X) has no complement in {p(a)|q(b)}
        # that would justify removing q(b).
        bad = self._TEXT.replace(
            "plain, q(b), inference(forward_subsumption_resolution",
            "plain, p(a), inference(forward_subsumption_resolution")
        r = _refutation_check(bad, self._PREMISES)
        assert r.verified is False
        assert "subsumption_resolution" in r.error

    def test_backward_variant_same_licensing(self):
        # 'backward_subsumption_resolution' is registered against the exact
        # same checker -- only the rule-name string differs.
        text = self._TEXT.replace("forward_subsumption_resolution", "backward_subsumption_resolution")
        r = _refutation_check(text, self._PREMISES)
        assert r.verified, r.error

    def test_genuine_multi_literal_subsumer_matches_into_other_literal(self):
        # target {p(a)|q(a)|r(b)}, subsumer {~p(X)|q(X)}
        # -forward_subsumption_resolution-> {q(a)|r(b)}: p(a)'s complement
        # (~p(X)) one-sided-matches p(a) under X|->a (so M = p(a)), and the
        # subsumer's OTHER literal q(X)sigma = q(a) must then match some
        # target literal OTHER than M -- here q(a) -- leaving r(b)
        # untouched. Every earlier case in this class uses a single-literal
        # subsumer (empty 'rest_c'); this is the first to actually exercise
        # the "rest_c matches into the target" path of
        # _check_tstp_subsumption_resolution.
        text = (
            "cnf(c1, axiom, (p(a) | q(a) | r(b))).\n"
            "cnf(c2, axiom, (~p(X) | q(X))).\n"
            "cnf(c3, plain, (q(a) | r(b)), inference(forward_subsumption_resolution,[],[c1,c2])).\n"
        )
        premises = [Or(Or(P(a), Q(a)), Atom("R", [b])), Or(Not(P(x)), Q(x))]
        r = _refutation_check(text, premises)
        assert r.verified, r.error

    def test_tautologous_subsumer_cannot_launder_an_arbitrary_literal_drop(self):
        # Adversarial: subsumer {~p(X)|p(X)} is a TAUTOLOGY, carrying no
        # information. {~p(x)|p(x), p(a)|r(b)} does NOT entail r(b): the
        # model p(a)=True, r(b)=False (the first premise is a tautology,
        # always true; the second holds via p(a)) satisfies both premises
        # yet falsifies r(b). A checker that let the subsumer's OTHER
        # literal (p(X), sigma X|->a = p(a)) re-match the very literal M
        # (p(a)) being dropped would wrongly ACCEPT this step -- see
        # _check_tstp_subsumption_resolution's docstring for why 'rest_c'
        # must match into target MINUS M, never the full target.
        text = (
            "cnf(c1, axiom, (~p(X) | p(X))).\n"
            "cnf(c2, axiom, (p(a) | r(b))).\n"
            "cnf(c3, plain, r(b), inference(forward_subsumption_resolution,[],[c2,c1])).\n"
        )
        premises = [Or(Not(P(x)), P(x)), Or(P(a), Atom("R", [b]))]
        r = _refutation_check(text, premises)
        assert r.verified is False
        assert "subsumption_resolution" in r.error


class TestUnrecognizedRule:
    def test_avatar_style_unknown_rule_refused_loudly(self):
        # No real AVATAR fixture was captured (this module's fixtures all use
        # --avatar off), but the "refuse loudly, naming the rule" contract is
        # rule-name-driven, not fixture-driven -- any name outside both
        # tables must be refused the same way, hand-built or not.
        text = (
            "cnf(c1, axiom, p(a)).\n"
            "cnf(c2, plain, p(a), inference(avatar_component_clause,[],[c1])).\n"
        )
        r = _refutation_check(text, [P(a)])
        assert r.verified is False
        assert "avatar_component_clause" in r.error
        step_by_name = {s.name: s for s in r.steps}
        assert step_by_name["c2"].tier == "unchecked"

    def test_equality_factoring_deliberately_unchecked(self):
        # See tstp_check.py's module docstring: equality factoring is a
        # conscious scope decision, not an oversight.
        assert "equality_factoring" not in VAMPIRE_CHECKED_RULES
        text = (
            "cnf(c1, axiom, (a = b) | (c = d)).\n"
            "cnf(c2, plain, (a = b) | (c = d), inference(equality_factoring,[],[c1])).\n"
        )
        r = _refutation_check(text, [Or(Atom("=", [Constant("a"), Constant("b")]),
                                       Atom("=", [Constant("c"), Constant("d")]))])
        assert r.verified is False
        assert "equality_factoring" in r.error


# ---------------------------------------------------------------------------
# 3. Differential: translated resolution_check.py fixtures must agree
# ---------------------------------------------------------------------------

class TestDifferentialAgainstResolutionCheck:
    def test_part_a_end_to_end_refutation_agrees(self):
        """resolution_check.py's own part (a): {P(a)}, {~P(x)|Q(x)}, {~Q(a)}
        is unsatisfiable via resolve(1,2) then resolve(3,4)."""
        inputs = (frozenset({P(a)}), frozenset({Not(P(x)), Q(x)}), frozenset({Not(Q(a))}))
        steps = (
            ResolutionStep(1, frozenset({P(a)}), "input"),
            ResolutionStep(2, frozenset({Not(P(x)), Q(x)}), "input"),
            ResolutionStep(3, frozenset({Not(Q(a))}), "input"),
            ResolutionStep(4, frozenset({Q(a)}), "resolve", (1, 2)),
            ResolutionStep(5, frozenset(), "resolve", (3, 4)),
        )
        rc_result = verify_resolution_proof(ResolutionDerivation(inputs, steps))
        assert rc_result.ok and rc_result.refuted  # sanity: resolution_check itself accepts

        text = (
            "cnf(c1, axiom, p(a)).\n"
            "cnf(c2, axiom, (~p(X) | q(X))).\n"
            "cnf(c3, axiom, ~q(a)).\n"
            "cnf(c4, plain, q(a), inference(resolution,[],[c2,c1])).\n"
            "cnf(c5, plain, $false, inference(resolution,[],[c3,c4])).\n"
        )
        r = _refutation_check(text, [P(a), Or(Not(P(x)), Q(x)), Not(Q(a))])
        assert r.verified == rc_result.ok
        assert r.refuted == rc_result.refuted

    def test_part_b_robinson_factoring_then_resolution_agrees(self):
        """resolution_check.py's classic Robinson example: {P(x),P(y)} and
        {~P(u),~P(v)} need BOTH clauses factored to units before resolution
        empties -- direct resolution alone leaves a genuine 2-literal clause
        (see resolution_check.py's own module comment on this fixture)."""
        inputs = (frozenset({P(x), P(y)}), frozenset({Not(P(u)), Not(P(v))}))
        steps = (
            ResolutionStep(1, frozenset({P(x), P(y)}), "input"),
            ResolutionStep(2, frozenset({Not(P(u)), Not(P(v))}), "input"),
            ResolutionStep(3, frozenset({P(x)}), "factor", (1,)),
            ResolutionStep(4, frozenset({Not(P(u))}), "factor", (2,)),
            ResolutionStep(5, frozenset(), "resolve", (3, 4)),
        )
        rc_result = verify_resolution_proof(ResolutionDerivation(inputs, steps))
        assert rc_result.ok and rc_result.refuted

        text = (
            "cnf(c1, axiom, (p(X) | p(Y))).\n"
            "cnf(c2, axiom, (~p(U) | ~p(V))).\n"
            "cnf(c3, plain, p(X), inference(factoring,[],[c1])).\n"
            "cnf(c4, plain, ~p(U), inference(factoring,[],[c2])).\n"
            "cnf(c5, plain, $false, inference(resolution,[],[c3,c4])).\n"
        )
        r = _refutation_check(text, [Or(P(x), P(y)), Or(Not(P(u)), Not(P(v)))])
        assert r.verified == rc_result.ok
        assert r.refuted == rc_result.refuted

    def test_part_b_direct_resolution_without_factoring_also_agrees(self):
        """The SAME clauses, but claiming the empty clause directly from
        resolve(1,2) with NO factoring -- resolution_check.py rejects this
        (test_robinson_direct_empty_clause_claim_is_rejected); this module
        must too, for the identical reason."""
        inputs = (frozenset({P(x), P(y)}), frozenset({Not(P(u)), Not(P(v))}))
        steps = (
            ResolutionStep(1, frozenset({P(x), P(y)}), "input"),
            ResolutionStep(2, frozenset({Not(P(u)), Not(P(v))}), "input"),
            ResolutionStep(3, frozenset(), "resolve", (1, 2)),
        )
        rc_result = verify_resolution_proof(ResolutionDerivation(inputs, steps))
        assert rc_result.ok is False

        text = (
            "cnf(c1, axiom, (p(X) | p(Y))).\n"
            "cnf(c2, axiom, (~p(U) | ~p(V))).\n"
            "cnf(c3, plain, $false, inference(resolution,[],[c1,c2])).\n"
        )
        r = _refutation_check(text, [Or(P(x), P(y)), Or(Not(P(u)), Not(P(v)))])
        assert r.verified == rc_result.ok


# ---------------------------------------------------------------------------
# Direct unit tests for the small internal helpers
# ---------------------------------------------------------------------------

class TestNodeToClause:
    def test_bare_false_is_the_empty_clause(self):
        assert _node_to_clause(parse_tptp_formula("$false")) == frozenset()

    def test_true_is_not_a_valid_clause(self):
        assert _node_to_clause(parse_tptp_formula("$true")) is None

    def test_leading_universal_quantifiers_are_stripped(self):
        got = _node_to_clause(parse_tptp_formula("! [X,Y] : (p(X) | ~q(Y))"))
        assert got == frozenset({P(x), Not(Q(y))})

    def test_leading_existential_is_not_a_clause(self):
        assert _node_to_clause(parse_tptp_formula("? [X] : p(X)")) is None

    def test_conjunction_is_not_a_clause(self):
        assert _node_to_clause(parse_tptp_formula("p(a) & q(a)")) is None

    def test_disequality_is_normalized_to_negative_equality(self):
        got = _node_to_clause(parse_tptp_formula("a != b"))
        assert got == frozenset({Not(Atom("=", [a, b]))})


class TestFormulaAlphaEqual:
    def test_bound_variable_renaming_matches(self):
        left = parse_tptp_formula("! [X] : p(X)")
        right = parse_tptp_formula("! [Y] : p(Y)")
        assert _formula_alpha_equal(left, right)

    def test_different_predicate_does_not_match(self):
        left = parse_tptp_formula("p(a)")
        right = parse_tptp_formula("q(a)")
        assert not _formula_alpha_equal(left, right)

    def test_swapped_implication_sides_do_not_match(self):
        left = parse_tptp_formula("p(a) => q(a)")
        right = parse_tptp_formula("q(a) => p(a)")
        assert not _formula_alpha_equal(left, right)


class TestAllPositions:
    def test_nested_function_positions(self):
        term = f(Function("g", [a]))  # f(g(a))
        # position (0,) addresses g(a); (0, 0) addresses a.
        assert set(_all_positions(term)) == {(0,), (0, 0)}

    def test_constant_has_no_positions(self):
        assert _all_positions(a) == []


# ---------------------------------------------------------------------------
# Contract checks
# ---------------------------------------------------------------------------

def test_bad_query_raises():
    with pytest.raises(ValueError):
        check_tstp_derivation(parse_tstp_derivation(""), [], None, query="nonsense")


def test_result_to_dict_round_trips_shape():
    text = "cnf(c1, axiom, p(a)).\n"
    r = check_tstp_derivation(parse_tstp_derivation(text), [P(a)], None, query="refutation")
    d = r.to_dict()
    assert d["verified"] is True
    assert d["steps"][0]["name"] == "c1"
    assert d["steps"][0]["tier"] == "leaf"


def test_rule_tables_do_not_register_equality_factoring_or_cn():
    assert "equality_factoring" not in VAMPIRE_CHECKED_RULES
    assert "cn" not in EPROVER_CHECKED_RULES and "cn" not in EPROVER_CLAUSIFICATION_RULES


# ---------------------------------------------------------------------------
# Regression: the clausification tier is checked by entailment, and the
# conjecture may only be used negated. Each derivation below is a FAKE proof
# of a non-theorem that an earlier, provenance-only version of this tier
# reported verified=True.
# ---------------------------------------------------------------------------

_HEAD = "% SZS status Theorem for x\n% SZS output start Proof for x\n"
_TAIL = "% SZS output end Proof for x\n"


def _check_text(body: str, premises, conclusion):
    d = parse_tstp_derivation(_HEAD + body + _TAIL)
    return check_tstp_derivation(d, [parse_tptp_formula(p) for p in premises],
                                 parse_tptp_formula(conclusion))


class TestClausificationIsCheckedByEntailment:
    def test_a_clausification_step_cannot_state_what_its_parent_does_not_entail(self):
        """p(a) |- p(b) is not a theorem (take a model with p(a) true, p(b)
        false). The fake proof lies in f4: cnf_transformation of ~p(b) cannot
        yield ~p(a), since ~p(b) does not entail ~p(a) -- after which the
        resolution of f4 with p(a) is itself a perfectly valid step."""
        body = (
            "fof(f1,axiom,(p(a)),file('x.p',unknown)).\n"
            "fof(f2,conjecture,(p(b)),file('x.p',unknown)).\n"
            "fof(f3,negated_conjecture,(~p(b)),inference(negated_conjecture,[status(cth)],[f2])).\n"
            "fof(f4,plain,(~p(a)),inference(cnf_transformation,[],[f3])).\n"
            "fof(f5,plain,(p(a)),inference(cnf_transformation,[],[f1])).\n"
            "fof(f6,plain,($false),inference(resolution,[],[f4,f5])).\n")
        r = _check_text(body, ["p(a)"], "p(b)")
        assert r.verified is False
        steps = {s.name: s for s in r.steps}
        assert steps["f4"].tier == "entailed" and steps["f4"].ok is False
        assert "not entailed by its parents" in steps["f4"].detail
        # the honest steps around the lie still check out on their own
        assert steps["f3"].ok and steps["f5"].ok

    def test_a_clausification_step_cannot_assume_the_conjecture(self):
        """{q(a)} |- p(b) is not a theorem. f4 re-states the CONJECTURE p(b)
        as if it were a premise; entailment alone would pass it (p(b) entails
        p(b)), which is why citing the conjecture is refused outright unless
        the rule is the negation step."""
        body = (
            "fof(f2,conjecture,(p(b)),file('x.p',unknown)).\n"
            "fof(f3,negated_conjecture,(~p(b)),inference(negated_conjecture,[status(cth)],[f2])).\n"
            "fof(f4,plain,(p(b)),inference(cnf_transformation,[],[f2])).\n"
            "fof(f5,plain,($false),inference(resolution,[],[f3,f4])).\n")
        r = _check_text(body, ["q(a)"], "p(b)")
        assert r.verified is False
        steps = {s.name: s for s in r.steps}
        assert steps["f4"].ok is False
        assert "cites the conjecture 'f2' itself" in steps["f4"].detail

    def test_a_core_rule_cannot_cite_the_conjecture_either(self):
        """Same non-theorem, with resolution citing the conjecture leaf f2
        directly instead of going through a clausification step."""
        body = (
            "fof(f2,conjecture,(p(b)),file('x.p',unknown)).\n"
            "fof(f3,negated_conjecture,(~p(b)),inference(negated_conjecture,[status(cth)],[f2])).\n"
            "fof(f5,plain,($false),inference(resolution,[],[f3,f2])).\n")
        r = _check_text(body, ["q(a)"], "p(b)")
        assert r.verified is False
        steps = {s.name: s for s in r.steps}
        assert steps["f5"].tier == "checked" and steps["f5"].ok is False
        assert "cites the conjecture 'f2' itself" in steps["f5"].detail

    def test_negated_conjecture_must_actually_negate_the_conjecture(self):
        """negated_conjecture of p(b) stating ~p(c): ~p(b) does not entail
        ~p(c), so the step fails even though its rule name is right."""
        body = (
            "fof(f1,axiom,(p(a)),file('x.p',unknown)).\n"
            "fof(f2,conjecture,(p(b)),file('x.p',unknown)).\n"
            "fof(f3,negated_conjecture,(~p(c)),inference(negated_conjecture,[status(cth)],[f2])).\n")
        r = _check_text(body, ["p(a)"], "p(b)")
        steps = {s.name: s for s in r.steps}
        assert steps["f3"].ok is False
        assert "negated conjecture" in steps["f3"].detail

    def test_negation_rule_may_not_cite_anything_but_the_conjecture(self):
        body = (
            "fof(f1,axiom,(p(a)),file('x.p',unknown)).\n"
            "fof(f2,conjecture,(p(b)),file('x.p',unknown)).\n"
            "fof(f3,negated_conjecture,(~p(b)),inference(negated_conjecture,[status(cth)],[f2,f1])).\n")
        r = _check_text(body, ["p(a)"], "p(b)")
        steps = {s.name: s for s in r.steps}
        assert steps["f3"].ok is False
        assert "may only negate the conjecture" in steps["f3"].detail

    def test_a_sound_clausification_with_free_clause_variables_verifies(self):
        """The accepting side of the same check: a cnf step whose clause has
        implicitly universal variables (X0) is entailed by its closed parent,
        and $false as the final clause is read as falsum, not as an atom.
        {!X (h(X) => m(X)), h(s)} |- m(s) is a genuine theorem."""
        body = (
            "fof(f1,axiom,(! [X0] : (h(X0) => m(X0))),file('x.p',unknown)).\n"
            "fof(f2,axiom,(h(s)),file('x.p',unknown)).\n"
            "fof(f3,conjecture,(m(s)),file('x.p',unknown)).\n"
            "fof(f4,negated_conjecture,(~m(s)),inference(negated_conjecture,[status(cth)],[f3])).\n"
            "fof(f5,plain,(~h(X0) | m(X0)),inference(cnf_transformation,[],[f1])).\n"
            "fof(f6,plain,(m(s)),inference(resolution,[],[f5,f2])).\n"
            "fof(f7,plain,($false),inference(resolution,[],[f6,f4])).\n")
        r = _check_text(body, ["! [X] : (h(X) => m(X))", "h(s)"], "m(s)")
        assert r.verified is True, r.error
        assert r.refuted is True
        assert {s.name: s.tier for s in r.steps}["f5"] == "entailed"
