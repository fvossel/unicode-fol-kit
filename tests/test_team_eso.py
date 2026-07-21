"""Tests for the dependence-logic -> ESO translation
(unicode_fol_kit.semantics.team_translation.dependence_to_eso).

The formal anchor is DIFFERENTIAL: for each hand-picked sentence of the
supported fragment, ``team_models(structure, sentence)`` (the independent
brute-force team-semantics oracle) must agree with
``holds(dependence_to_eso(sentence), structure)`` (the independent brute-force
second-order oracle) on EVERY structure of a small enumerated or seeded-random
family — any disagreement is a translation bug. A handful of cases are also
hand-derived in comments and checked directly (not just against each other),
so the two oracles cannot simply be "wrong together".

Domain-size notes: most sentences are checked exhaustively up to |domain| = 4.
A sentence with a NESTED pair of nontrivial Skolem functions (two independent
``∃F`` searches multiplied together) is checked up to |domain| = 3 only —
larger is still correct (this is a translation-faithfulness suite, not a
performance one) but the two independent brute-force oracles both get
expensive there (team.py's own MAX_TEAM_SEARCH and secondorder.py's
MAX_RELATIONS document exactly this brute-force cost), so exercising it at
|domain| = 4 would make the suite slow without adding fragment coverage.
"""

import itertools
import random

import pytest

from unicode_fol_kit import (
    MSFLParser, Structure, Atom, Not, And, Or, Implies, Iff, Xor,
    Quantifier, Variable, Dependence, SlashedExists,
)
from unicode_fol_kit.semantics.team import team_models
from unicode_fol_kit.semantics.secondorder import holds
from unicode_fol_kit.semantics.team_translation import dependence_to_eso

DEP = MSFLParser(dependence=True)
p = DEP.parse


# ---------------------------------------------------------------------------
# Structure enumeration / sampling helpers.
# ---------------------------------------------------------------------------

def _powerset(items):
    n = len(items)
    for mask in range(1 << n):
        yield frozenset(items[i] for i in range(n) if mask >> i & 1)


def _enum_structures(pred_sig, sizes):
    """Yield EVERY Structure over each size in ``sizes`` for the given predicate
    signature ``[(name, arity), ...]`` (all constants/functions empty)."""
    for n in sizes:
        dom = tuple(range(n))
        per_pred_options = [
            list(_powerset(list(itertools.product(dom, repeat=ar))))
            for (_, ar) in pred_sig
        ]
        for combo in itertools.product(*per_pred_options):
            preds = {sig: ext for sig, ext in zip(pred_sig, combo)}
            yield Structure(domain=dom, predicates=preds)


def _sample_structures(rng, pred_sig, sizes, count):
    """Yield ``count`` random Structures per size (Bernoulli(1/2) per tuple)."""
    for n in sizes:
        dom = tuple(range(n))
        for _ in range(count):
            preds = {}
            for name, ar in pred_sig:
                tuples = list(itertools.product(dom, repeat=ar))
                preds[(name, ar)] = {t for t in tuples if rng.random() < 0.5}
            yield Structure(domain=dom, predicates=preds)


def _check_agreement(text, structures):
    """Assert team_models(S, f) == holds(translate(f), S) for every S; return the verdicts."""
    f = p(text)
    translated = dependence_to_eso(f)
    verdicts = []
    for S in structures:
        tm = team_models(S, f)
        so = holds(translated, S)
        assert tm == so, (
            f"dependence_to_eso disagreement for {text!r} on {S!r}: "
            f"team_models={tm}, holds(translation)={so}"
        )
        verdicts.append(tm)
    return verdicts


# ---------------------------------------------------------------------------
# Group 1 — plain FOL (dependence/slash-free): ∨ fully supported anywhere,
# and the translation must be classically equivalent (Skolemisation), so this
# group ALSO cross-checks against the independent classical Tarski evaluator.
# ---------------------------------------------------------------------------

class TestPlainFOL:
    def test_reflexive_witness_is_a_tautology(self):
        # ∀x∃y(y=x): y=x always witnesses. True in EVERY structure, including
        # the domain-1 through domain-4 empty-signature ones.
        text = "∀x ∃y (y = x)"
        structures = [Structure(domain=list(range(n))) for n in (1, 2, 3, 4)]
        verdicts = _check_agreement(text, structures)
        assert all(verdicts)

    def test_or_of_two_plain_fo_parts(self):
        # ∀x∃y R(x,y) ∨ ∀x¬R(x,x): plain-FO ∨ at the very top. Hand check on
        # the total relation (R = everything): left disjunct trivially True
        # (y=x always works) -> whole sentence True regardless of the right
        # disjunct's value on that same structure.
        text = "∀x ∃y R(x, y) ∨ ∀x ¬R(x, x)"
        n = 3
        dom = tuple(range(n))
        total = Structure(domain=dom, predicates={("R", 2): set(itertools.product(dom, repeat=2))})
        f = p(text)
        assert team_models(total, f) is True
        assert holds(dependence_to_eso(f), total) is True
        # Full differential over every R-extension. y is UNGUARDED here, so
        # its Skolem function has arity 2 (2**(n**2) relations to search) --
        # capped at |domain|<=3 for the same runtime reason documented at the
        # top of the module (matches test_guard_arity_ignores_a_non_determinant
        # below, and test_asymmetric_successor_mixed_verdicts).
        structures = list(_enum_structures([("R", 2)], (1, 2, 3)))
        verdicts = _check_agreement(text, structures)
        assert any(verdicts) and not all(verdicts)  # non-vacuous both ways

    def test_quantifier_nested_under_conjunction(self):
        # ∃x(P(x) ∧ ∀y(¬R(x,y) ∨ P(y))): a plain ∃ NOT at the front of a
        # prenex block (it has a sibling conjunct P(x), and its own body hides
        # a further ∀ nested one level down) — exercises the "float SO ∃'s
        # out from ANY position" part of the translation, not just a strict
        # quantifier prefix. Hand check: if P is EVERYTHING and R is anything,
        # x=(any element) satisfies P(x), and ∀y(¬R(x,y)∨P(y)) holds since
        # P(y) is always true -> whole sentence True.
        text = "∃x (P(x) ∧ ∀y (¬R(x, y) ∨ P(y)))"
        n = 3
        dom = tuple(range(n))
        all_p = Structure(domain=dom, predicates={("P", 1): {(d,) for d in dom}, ("R", 2): set()})
        f = p(text)
        assert team_models(all_p, f) is True
        assert holds(dependence_to_eso(f), all_p) is True
        structures = list(_enum_structures([("P", 1), ("R", 2)], (1, 2, 3)))
        verdicts = _check_agreement(text, structures)
        assert any(verdicts) and not all(verdicts)

    def test_asymmetric_successor_mixed_verdicts(self):
        # ∀x∃y(R(x,y) ∧ ¬R(y,x)): needs, for every x, a strictly-one-way
        # R-related y. Hand check: R empty -> no y at all satisfies R(x,y) ->
        # False. R = the full "less-than" relation on {0,1,2} (i<j) -> every
        # x<2 has such a y (any j>x), but x=2 has none -> False. R = the
        # 3-cycle {(0,1),(1,2),(2,0)} -> every x has R(x,succ(x)) and NOT
        # R(succ(x),x) (a 3-cycle is not 2-cycle-symmetric anywhere) -> True.
        text = "∀x ∃y (R(x, y) ∧ ¬R(y, x))"
        f = p(text)
        dom3 = tuple(range(3))
        empty = Structure(domain=dom3, predicates={("R", 2): set()})
        cycle = Structure(domain=dom3, predicates={("R", 2): {(0, 1), (1, 2), (2, 0)}})
        assert team_models(empty, f) is False and holds(dependence_to_eso(f), empty) is False
        assert team_models(cycle, f) is True and holds(dependence_to_eso(f), cycle) is True
        # y is UNGUARDED (arity-2 Skolem, 2**(n**2) relations) -- capped at
        # |domain|<=3, as above.
        structures = list(_enum_structures([("R", 2)], (1, 2, 3)))
        verdicts = _check_agreement(text, structures)
        assert any(verdicts) and not all(verdicts)

    def test_top_level_or_tautology(self):
        # ∀x(P(x) ∨ ¬P(x)): the law of excluded middle, no quantifier needs a
        # Skolem function at all (∨ of two literals) -> True everywhere.
        text = "∀x (P(x) ∨ ¬P(x))"
        structures = list(_enum_structures([("P", 1)], (1, 2, 3, 4)))
        verdicts = _check_agreement(text, structures)
        assert all(verdicts)


# ---------------------------------------------------------------------------
# Group 2 — dependence-atom-guarded existentials (canonical Väänänen pattern).
# ---------------------------------------------------------------------------

class TestDependenceGuarded:
    def test_constant_witness_forces_singleton_domain(self):
        # ∀x∃y(=(y) ∧ y=x): a SINGLE y must equal every x -> only possible when
        # |domain| = 1. (Reasoning: after ∀x the team has one row per domain
        # element; =(y) forces one shared y-value c across the whole team, and
        # y=x forces c = a for every a in the domain.)
        text = "∀x ∃y (=(y) ∧ y = x)"
        structures = [Structure(domain=list(range(n))) for n in (1, 2, 3, 4)]
        verdicts = _check_agreement(text, structures)
        assert verdicts == [True, False, False, False]

    def test_universal_sink_via_dependence_atom(self):
        # ∀x∃y(=(y) ∧ Edge(x,y)): one SHARED y must be an Edge-target of every
        # x -- a "universal sink". Hand check: the sink structure with c
        # receiving an edge from every vertex (incl. itself) -> True with
        # y=c; the 3-cycle (out-degree 1 each, no common target) -> False.
        text = "∀x ∃y (=(y) ∧ Edge(x, y))"
        f = p(text)
        sink = Structure(domain=["a", "b", "c"],
                         predicates={("Edge", 2): {("a", "c"), ("b", "c"), ("c", "c"), ("a", "b")}})
        no_sink = Structure(domain=["a", "b", "c"],
                            predicates={("Edge", 2): {("a", "b"), ("b", "c"), ("c", "a")}})
        assert team_models(sink, f) is True and holds(dependence_to_eso(f), sink) is True
        assert team_models(no_sink, f) is False and holds(dependence_to_eso(f), no_sink) is False
        structures = list(_enum_structures([("Edge", 2)], (1, 2, 3)))
        rng = random.Random(303)
        structures += list(_sample_structures(rng, [("Edge", 2)], (4,), 20))
        verdicts = _check_agreement(text, structures)
        assert any(verdicts) and not all(verdicts)

    def test_bare_dependence_guarded_existential_at_sentence_root(self):
        # ∃y(=(y) ∧ P(y)): the singleton starting team makes =(y) automatic —
        # this reduces to plain ∃y P(y). True iff P is non-empty.
        text = "∃y (=(y) ∧ P(y))"
        f = p(text)
        empty_p = Structure(domain=[0, 1], predicates={("P", 1): set()})
        nonempty_p = Structure(domain=[0, 1], predicates={("P", 1): {(0,)}})
        assert team_models(empty_p, f) is False and holds(dependence_to_eso(f), empty_p) is False
        assert team_models(nonempty_p, f) is True and holds(dependence_to_eso(f), nonempty_p) is True
        structures = list(_enum_structures([("P", 1)], (1, 2, 3, 4)))
        verdicts = _check_agreement(text, structures)
        assert any(verdicts) and not all(verdicts)

    def test_guard_arity_ignores_a_non_determinant_enclosing_forall(self):
        # ∀x∀z∃y(=(x,y) ∧ R(x,y) ∧ Edge(z,y)): the GUARD lists only x as
        # y's determinant, so y = f(x) must be chosen WITHOUT looking at z,
        # yet must satisfy Edge(z,y) for the SPECIFIC z bound by the outer
        # ∀z, i.e. for EVERY z. So this sentence says: ∃f (∀x (R(x,f(x)) ∧
        # ∀z Edge(z,f(x)))) — f(x) must be an Edge-target of EVERY vertex.
        # Hand check: take R = everything, Edge = everything -> f(x)=x works
        # trivially (target of every z since Edge is total) -> True. Take
        # Edge = empty -> no y can be an Edge-target of ANY z (unless
        # domain has size 0, excluded) -> False regardless of R.
        text = "∀x ∀z ∃y (=(x, y) ∧ R(x, y) ∧ Edge(z, y))"
        f = p(text)
        dom = (0, 1, 2)
        total = Structure(domain=dom, predicates={
            ("R", 2): set(itertools.product(dom, repeat=2)),
            ("Edge", 2): set(itertools.product(dom, repeat=2)),
        })
        no_edge = Structure(domain=dom, predicates={
            ("R", 2): set(itertools.product(dom, repeat=2)), ("Edge", 2): set(),
        })
        assert team_models(total, f) is True and holds(dependence_to_eso(f), total) is True
        assert team_models(no_edge, f) is False and holds(dependence_to_eso(f), no_edge) is False
        # Random sample (two binary predicates -> full enumeration is huge);
        # |domain| capped at 3 -- team.py's own MAX_TEAM_SEARCH bound (two
        # ∀'s duplicate the team to n^2 rows before the ∃y witness search).
        rng = random.Random(404)
        structures = [total, no_edge] + list(
            _sample_structures(rng, [("R", 2), ("Edge", 2)], (1, 2, 3), 15))
        verdicts = _check_agreement(text, structures)
        assert any(verdicts) and not all(verdicts)

    def test_two_nested_dependence_guarded_existentials(self):
        # ∀x∃y(=(x,y) ∧ ∃z(=(x,z) ∧ R(y,z))): BOTH y and z are functions of x
        # alone (f, g resp.), needing ∀x R(f(x),g(x)). Hand check: R = the
        # diagonal {(a,a)} -> f=g=identity works -> True. R = empty -> no pair
        # ever satisfies R -> False regardless of f,g.
        text = "∀x ∃y (=(x, y) ∧ ∃z (=(x, z) ∧ R(y, z)))"
        f = p(text)
        dom = (0, 1, 2)
        diagonal = Structure(domain=dom, predicates={("R", 2): {(a, a) for a in dom}})
        empty_r = Structure(domain=dom, predicates={("R", 2): set()})
        assert team_models(diagonal, f) is True and holds(dependence_to_eso(f), diagonal) is True
        assert team_models(empty_r, f) is False and holds(dependence_to_eso(f), empty_r) is False
        # Two NESTED Skolem functions of arity 2 each -> capped at |domain|<=3
        # (see module docstring on runtime cost); exhaustive at 1-2, sampled at 3.
        structures = list(_enum_structures([("R", 2)], (1, 2)))
        rng = random.Random(505)
        structures += list(_sample_structures(rng, [("R", 2)], (3,), 4))
        verdicts = _check_agreement(text, structures)
        assert any(verdicts) and not all(verdicts)

    def test_constant_wrapping_a_dependent_existential(self):
        # ∃y(=(y) ∧ ∀x∃z(=(x,z) ∧ Edge(y,z) ∧ Edge(z,x))): y is a GLOBAL
        # constant (not depending on x, despite x being in scope when z's
        # guard is checked -- only z's OWN guard =(x,z) matters for z's
        # arity, y stays whatever the outer guard says: arity 0), and for
        # every x there is a z = g(x) with Edge(y,z) and Edge(z,x) — a
        # length-2 path from the fixed y to every vertex. Hand check: the
        # 3-cycle Edge = {(0,1),(1,2),(2,0)} with y=0: for x=0 need
        # z=Edge(0,-)∩Edge(-,0)-target = 1, check Edge(1,0)? No (only
        # Edge(0,1),(1,2),(2,0) exist) -- so y=0 fails at x=0; by the cycle's
        # symmetry no y works -> False. The COMPLETE graph (Edge = all pairs
        # incl. self-loops) -> any y, any z (e.g. z=y) always satisfies both
        # Edge(y,z) and Edge(z,x) -> True.
        text = "∃y (=(y) ∧ ∀x ∃z (=(x, z) ∧ Edge(y, z) ∧ Edge(z, x)))"
        f = p(text)
        dom = (0, 1, 2)
        cycle = Structure(domain=dom, predicates={("Edge", 2): {(0, 1), (1, 2), (2, 0)}})
        complete = Structure(domain=dom, predicates={("Edge", 2): set(itertools.product(dom, repeat=2))})
        assert team_models(cycle, f) is False and holds(dependence_to_eso(f), cycle) is False
        assert team_models(complete, f) is True and holds(dependence_to_eso(f), complete) is True
        # A constant (arity-0) Skolem function nested around an arity-2 one;
        # capped at |domain|<=3 for the same runtime reason as above.
        structures = list(_enum_structures([("Edge", 2)], (1, 2)))
        rng = random.Random(606)
        structures += list(_sample_structures(rng, [("Edge", 2)], (3,), 10))
        verdicts = _check_agreement(text, structures)
        assert any(verdicts) and not all(verdicts)

    def test_two_independent_top_level_constants(self):
        # ∃y(=(y)∧P(y)) ∧ ∃w(=(w)∧Q(w)): two SIBLING (not nested) guarded
        # existentials conjoined at the top -- exercises floating TWO
        # independent SO ∃'s out of separate ∧-branches. True iff both P and
        # Q are non-empty.
        text = "∃y (=(y) ∧ P(y)) ∧ ∃w (=(w) ∧ Q(w))"
        f = p(text)
        dom = (0, 1)
        both = Structure(domain=dom, predicates={("P", 1): {(0,)}, ("Q", 1): {(1,)}})
        neither = Structure(domain=dom, predicates={("P", 1): set(), ("Q", 1): set()})
        assert team_models(both, f) is True and holds(dependence_to_eso(f), both) is True
        assert team_models(neither, f) is False and holds(dependence_to_eso(f), neither) is False
        structures = list(_enum_structures([("P", 1), ("Q", 1)], (1, 2, 3, 4)))
        verdicts = _check_agreement(text, structures)
        assert any(verdicts) and not all(verdicts)


# ---------------------------------------------------------------------------
# Group 3 — slashed (independence-friendly) existentials.
# ---------------------------------------------------------------------------

class TestSlashed:
    def test_slashed_independence_forces_singleton_domain(self):
        # ∀x∃y/{x}(y=x): the IF-logic equivalent of the =(y) constancy case
        # (Väänänen 2007): y must be chosen uniformly in x, forcing the SAME
        # constant witness. True iff |domain| = 1.
        text = "∀x ∃y/{x} (y = x)"
        structures = [Structure(domain=list(range(n))) for n in (1, 2, 3, 4)]
        verdicts = _check_agreement(text, structures)
        assert verdicts == [True, False, False, False]

    def test_slashing_only_x_leaves_z_dependency_free(self):
        # ∀x∀z∃y/{x}(y=z): y is independent of x but MAY depend on z (only x
        # is slashed) -- witness y=z always works, regardless of x. True in
        # EVERY structure (no predicate needed at all).
        text = "∀x ∀z ∃y/{x} (y = z)"
        structures = [Structure(domain=list(range(n))) for n in (1, 2, 3, 4)]
        verdicts = _check_agreement(text, structures)
        assert all(verdicts)

    def test_slashing_both_enclosing_universals_forces_singleton_domain(self):
        # ∀x∀z∃y/{x,z}(y=x): y independent of BOTH x and z -- back to a pure
        # constant, same singleton-domain requirement as the single-∀ case.
        text = "∀x ∀z ∃y/{x, z} (y = x)"
        structures = [Structure(domain=list(range(n))) for n in (1, 2, 3, 4)]
        verdicts = _check_agreement(text, structures)
        assert verdicts == [True, False, False, False]

    def test_universal_sink_via_slash(self):
        # ∀x∃y/{x}(R(x,y)): the SAME universal-sink property as the
        # dependence-atom version, expressed with a slash instead.
        text = "∀x ∃y/{x} (R(x, y))"
        f = p(text)
        sink = Structure(domain=["a", "b", "c"],
                         predicates={("R", 2): {("a", "c"), ("b", "c"), ("c", "c"), ("a", "b")}})
        no_sink = Structure(domain=["a", "b", "c"],
                            predicates={("R", 2): {("a", "b"), ("b", "c"), ("c", "a")}})
        assert team_models(sink, f) is True and holds(dependence_to_eso(f), sink) is True
        assert team_models(no_sink, f) is False and holds(dependence_to_eso(f), no_sink) is False
        structures = list(_enum_structures([("R", 2)], (1, 2, 3)))
        rng = random.Random(707)
        structures += list(_sample_structures(rng, [("R", 2)], (4,), 20))
        verdicts = _check_agreement(text, structures)
        assert any(verdicts) and not all(verdicts)

    def test_signalling_restores_the_witness(self):
        # ∀x∃z(z=x ∧ ∃y/{x}(y=x)): an intermediate ∃z (deterministically
        # equal to x) is NOT itself slashed, so it stays visible to y's
        # witness function and leaks x's value back in -- the classic
        # signalling phenomenon (Väänänen 2007 §4). True in EVERY structure,
        # in contrast to test_slashed_independence_forces_singleton_domain
        # above (no such intervening z there).
        # Both z (unguarded, arity 1) and y (slashed, arity 1) become NESTED
        # arity-2 Skolem predicates -- the same expensive double-search class
        # as test_two_nested_dependence_guarded_existentials, so this is
        # capped at |domain| <= 3 for the same runtime reason (see module
        # docstring).
        text = "∀x ∃z (z = x ∧ ∃y/{x} (y = x))"
        structures = [Structure(domain=list(range(n))) for n in (1, 2, 3)]
        verdicts = _check_agreement(text, structures)
        assert all(verdicts)


# ---------------------------------------------------------------------------
# Rejections: shapes explicitly outside the fragment.
# ---------------------------------------------------------------------------

class TestRejections:
    def test_or_combined_with_dependence_atom_rejected(self):
        f = p("=(x) ∨ P(x)")
        with pytest.raises(NotImplementedError, match="split disjunction"):
            dependence_to_eso(f)

    def test_or_combined_with_dependence_atom_elsewhere_in_the_tree_rejected(self):
        # The ∨ and the dependence atom are in UNRELATED branches -- still
        # rejected (the coarse, conservative rule: no ∨ ANYWHERE once a
        # dependence/slash construct occurs ANYWHERE in the sentence).
        f = p("(P(x) ∨ Q(x)) ∧ ∃y (=(y) ∧ y = x)")
        with pytest.raises(NotImplementedError, match="split disjunction"):
            dependence_to_eso(f)

    def test_or_combined_with_slashed_exists_rejected(self):
        f = p("∃y/{x} (y = x) ∨ P(x)")
        with pytest.raises(NotImplementedError, match="split disjunction"):
            dependence_to_eso(f)

    def test_dependence_atom_guarding_a_forall_bound_variable_rejected(self):
        # =(x) here guards x, which is ∀-bound, not the immediate body of the
        # ∃ that binds it (x is not existential at all) -- a "loose" atom.
        f = p("∀x (=(x) ∧ P(x))")
        with pytest.raises(NotImplementedError, match="does not guard its own existential"):
            dependence_to_eso(f)

    def test_dependence_atom_naming_the_wrong_variable_rejected(self):
        # ∃y(=(x) ∧ P(x,y)): the guard's dependent variable is x, not y (the
        # ∃'s own bound variable) -- not adjacent to its own binder.
        f = p("∃y (=(x) ∧ P(x, y))")
        with pytest.raises(NotImplementedError, match="does not guard its own existential"):
            dependence_to_eso(f)

    def test_dependence_atom_not_a_top_level_conjunct_of_its_own_exists_rejected(self):
        # The guard for y sits inside the NESTED ∃z's body, not y's own —
        # so y itself is unguarded (fine) but the loose =(y) further down,
        # naming an already-closed-over variable, is still surfaced and
        # rejected once generic recursion reaches it.
        f = p("∃y (P(y) ∧ ∃z (=(y) ∧ Q(z)))")
        with pytest.raises(NotImplementedError, match="does not guard its own existential"):
            dependence_to_eso(f)

    def test_negation_of_non_atom_rejected(self):
        f = Not(And(Atom("P", (Variable("x"),)), Atom("Q", (Variable("x"),))))
        with pytest.raises(NotImplementedError, match="¬ applies only to atoms"):
            dependence_to_eso(f)

    def test_shadowed_forall_inside_exists_rejected(self):
        # ∃x∀x P(x): x is rebound by the inner ∀ -- the translation reuses
        # bound names as-is, which requires no shadowing along one chain.
        f = Quantifier("∃", Variable("x"),
                       Quantifier("∀", Variable("x"), Atom("P", (Variable("x"),))))
        with pytest.raises(NotImplementedError, match="bound twice"):
            dependence_to_eso(f)

    def test_shadowed_slashed_exists_rejected(self):
        f = Quantifier("∀", Variable("x"),
                       SlashedExists(Variable("x"), ("x",), Atom("P", (Variable("x"),))))
        # Slashing a variable by ITS OWN name is nonsensical (SlashedExists
        # itself does not forbid it), but shadowing (x rebound by the inner
        # binder) is still what trips the check.
        with pytest.raises(NotImplementedError, match="bound twice"):
            dependence_to_eso(f)

    def test_shadowed_sibling_reuse_is_not_rejected(self):
        # ∃x P(x) ∧ ∃x Q(x): "x" reused in SIBLING (non-nested) branches is
        # NOT shadowing -- this must translate without raising.
        f = And(Quantifier("∃", Variable("x"), Atom("P", (Variable("x"),))),
               Quantifier("∃", Variable("x"), Atom("Q", (Variable("x"),))))
        dependence_to_eso(f)  # must not raise

    def test_implication_outside_the_team_fragment_rejected(self):
        f = Implies(Atom("P", (Variable("x"),)), Atom("Q", (Variable("x"),)))
        with pytest.raises(NotImplementedError):
            dependence_to_eso(f)

    def test_iff_outside_the_team_fragment_rejected(self):
        f = Iff(Atom("P", (Variable("x"),)), Atom("Q", (Variable("x"),)))
        with pytest.raises(NotImplementedError):
            dependence_to_eso(f)

    def test_xor_outside_the_team_fragment_rejected(self):
        f = Xor(Atom("P", (Variable("x"),)), Atom("Q", (Variable("x"),)))
        with pytest.raises(NotImplementedError):
            dependence_to_eso(f)


# ---------------------------------------------------------------------------
# Structural sanity: the translation is headed by SecondOrderQuantifier nodes
# whenever the sentence has an existential, and by nothing else otherwise.
# ---------------------------------------------------------------------------

class TestResultShape:
    def test_headed_by_second_order_quantifier_when_existentials_present(self):
        from unicode_fol_kit.fol.nodes import SecondOrderQuantifier
        f = p("∀x ∃y (=(y) ∧ y = x)")
        assert isinstance(dependence_to_eso(f), SecondOrderQuantifier)

    def test_no_second_order_wrapper_without_any_existential(self):
        from unicode_fol_kit.fol.nodes import SecondOrderQuantifier
        f = p("∀x (P(x) ∨ ¬P(x))")
        assert not isinstance(dependence_to_eso(f), SecondOrderQuantifier)

    def test_round_trips_through_holds_without_error_for_every_group(self):
        # A quick "doesn't crash and returns a bool" smoke test across the
        # whole battery, independent of the differential loops above.
        S = Structure(domain=[0, 1], predicates={
            ("P", 1): {(0,)}, ("Q", 1): {(1,)}, ("R", 2): {(0, 1)},
            ("Edge", 2): {(0, 1), (1, 0)},
        })
        texts = [
            "∀x ∃y (y = x)",
            "∀x ∃y (=(y) ∧ y = x)",
            "∀x ∃y/{x} (y = x)",
            "∃y (=(y) ∧ P(y))",
            "∀x ∃z (z = x ∧ ∃y/{x} (y = x))",
        ]
        for text in texts:
            f = p(text)
            assert isinstance(holds(dependence_to_eso(f), S), bool)
