"""Tests for the single-block second-order ASP checker
(unicode_fol_kit.semantics.asp_models.asp_holds_so — roadmap C24), and the
opt-in ``fast=`` wiring into secondorder.holds / so_find_model /
so_find_countermodel / so_is_satisfiable_finite / so_is_valid_finite and
team_translation.dependence_holds_eso.

The formal anchor is DIFFERENTIAL, mirroring test_asp_models.py's own
discipline: ``asp_holds_so`` and ``secondorder.satisfies_so``/``holds`` are two
INDEPENDENT implementations of the same second-order semantics (one grounded
via clingo's propagation-pruned choice rules, one brute-force powerset
enumeration in Python) restricted to the same fragment, so any disagreement
between them is an implementation bug, not an ambiguity in the target
semantics. This file checks that agreement four ways:

1. Hand-derived textbook cases (McCarthy's bird/penguin circumscription, and
   two of team_translation's own IF-logic slashed-existential examples),
   worked out by hand in a comment BEFORE either oracle is consulted.
2. The real outputs of the two producers this ticket targets —
   ``nonmonotonic.circumscription_formula``/``circumscription_entails_so`` and
   ``team_translation.dependence_to_eso`` — fed through both oracles on every
   structure of a small enumerated family.
3. A seeded-random battery of single-block sentences of BOTH polarities,
   arity 0/1/2, over random small structures (domain size 1..3), including
   equality, constants, and function symbols.
4. A fragment-gate battery: every shape this module's docstring says is
   outside the single-block fragment (alternation, mixed polarity, a second
   disconnected block, an SO block whose body has a free object variable
   bound outside it) raises ValueError naming the construct, rather than
   silently returning a wrong answer.

A scale check (test_oracle item (d)) shows asp_holds_so still returns at an
arity-2 domain size where secondorder.MAX_RELATIONS already blocks
satisfies_so outright.
"""

import itertools
import random

import pytest

# clingo is the [asp] extra, not a test dependency -- same module-level guard
# as test_asp_models.py / test_clingo_backend.py: skip, don't fail, when it is
# not installed.
pytest.importorskip("clingo")

from unicode_fol_kit import (
    MSFLParser, Atom, Not, And, Or, Implies, Iff, Quantifier, Variable, Constant,
    Function, SecondOrderQuantifier, Dependence, SlashedExists,
)
from unicode_fol_kit.semantics.tarski import Structure, satisfies
from unicode_fol_kit.semantics.secondorder import (
    satisfies_so, holds, MAX_RELATIONS,
    so_find_countermodel, so_is_satisfiable_finite, so_is_valid_finite,
)
from unicode_fol_kit.semantics.asp_models import asp_holds_so, _so_quantifier_chain
from unicode_fol_kit.semantics.nonmonotonic import (
    minimal_entails, circumscription_formula, circumscription_entails_so,
)
from unicode_fol_kit.semantics.team_translation import dependence_to_eso, dependence_holds_eso

X, Y = Variable("x"), Variable("y")
A, B, C = Constant("a"), Constant("b"), Constant("c")
TWEETY, OPUS = Constant("tweety"), Constant("opus")

DEP = MSFLParser(dependence=True)
dep_parse = DEP.parse


def _tuples(domain, arity):
    if arity == 0:
        return [()]
    return list(itertools.product(domain, repeat=arity))


# ---------------------------------------------------------------------------
# 1. Hand-derived textbook cases.
# ---------------------------------------------------------------------------

class TestHandDerivedCircumscription:
    """McCarthy's bird/penguin abnormality pattern (see test_circumscription_so.py
    for the same premises with a fuller derivation in the comments there).
    """

    _PENGUIN_BIRD = Quantifier("∀", X, Implies(Atom("Penguin", (X,)), Atom("Bird", (X,))))
    _PENGUIN_AB = Quantifier("∀", X, Implies(Atom("Penguin", (X,)), Atom("Ab", (X,))))
    _BIRD_TWEETY = Atom("Bird", (TWEETY,))
    _NOT_PENGUIN_TWEETY = Not(Atom("Penguin", (TWEETY,)))
    _BASE = [_PENGUIN_BIRD, _PENGUIN_AB, _BIRD_TWEETY, _NOT_PENGUIN_TWEETY]

    def test_non_penguin_bird_is_not_abnormal(self):
        # Ab circumscribed; Penguin(tweety) is explicitly false, so the
        # Penguin->Ab premise never fires for tweety and nothing else forces
        # Ab(tweety) -- every minimal model has Ab(tweety) = False, so the
        # circumscription axiom entails ¬Ab(tweety): True.
        axiom = circumscription_entails_so(self._BASE, {"Ab"}, Not(Atom("Ab", (TWEETY,))))
        me = minimal_entails(self._BASE, Not(Atom("Ab", (TWEETY,))), {"Ab"}, max_size=3)
        assert me is True
        for size in (1, 2, 3):
            structure = _every_structure_for(axiom, size)
            for s in structure:
                assert asp_holds_so(axiom, s) == satisfies_so(axiom, s)

    def test_penguin_is_abnormal(self):
        # Adding Penguin(opus) FORCES Ab(opus) true in every model (not just
        # minimal ones) via the Penguin->Ab premise -- entailed regardless.
        premises = self._BASE + [Atom("Penguin", (OPUS,))]
        axiom = circumscription_entails_so(premises, {"Ab"}, Atom("Ab", (OPUS,)))
        me = minimal_entails(premises, Atom("Ab", (OPUS,)), {"Ab"}, max_size=3)
        assert me is True
        for size in (1, 2, 3):
            for s in _every_structure_for(axiom, size):
                assert asp_holds_so(axiom, s) == satisfies_so(axiom, s)


def _every_structure_for(sentence, size):
    """Every Structure of ``size`` over the (small, hand-picked) signature the
    bird/penguin axiom above uses -- exhaustive, not sampled, since the
    signature (2 unary predicates, 2 constants) is small enough at size<=3."""
    domain = tuple(range(size))
    preds = [("Bird", 1), ("Penguin", 1), ("Ab", 1)]
    per_pred = [list(_powerset(_tuples(domain, ar))) for (_, ar) in preds]
    out = []
    for combo in itertools.product(*per_pred):
        predicates = {sig: set(ext) for sig, ext in zip(preds, combo)}
        for t_val in domain:
            for o_val in domain:
                out.append(Structure(domain, constants={"tweety": t_val, "opus": o_val},
                                     predicates=predicates))
    return out


def _powerset(items):
    n = len(items)
    for mask in range(1 << n):
        yield [items[i] for i in range(n) if mask >> i & 1]


class TestHandDerivedDependence:
    """Two of team_translation's own worked IF-logic examples (module
    docstring / test_team_eso.py), hand-derived independently of both oracles.
    """

    def test_slashed_independence_forces_singleton_domain(self):
        # ∀x ∃y/{x} (y = x): y must be chosen UNIFORMLY in x (independent of
        # it), so the SAME y must equal every x -- possible only when the
        # domain has exactly one element.
        f = dep_parse("∀x ∃y/{x} (y = x)")
        translated = dependence_to_eso(f)
        expected = {1: True, 2: False, 3: False, 4: False}
        for n, exp in expected.items():
            s = Structure(tuple(range(n)))
            so_val = satisfies_so(translated, s)
            asp_val = asp_holds_so(translated, s)
            assert so_val == asp_val == exp, (n, so_val, asp_val, exp)

    def test_signalling_restores_the_witness(self):
        # ∀x ∃z(z = x ∧ ∃y/{x}(y = x)): z (unslashed) leaks x's value back to
        # y (only x, not z, is slashed) -- true in EVERY domain, unlike the
        # case above with no intervening z. Two nested ∃-Skolem predicates
        # (F_z, F_y), still a single ∃-block by construction.
        f = dep_parse("∀x ∃z (z = x ∧ ∃y/{x} (y = x))")
        translated = dependence_to_eso(f)
        for n in (1, 2, 3):
            s = Structure(tuple(range(n)))
            so_val = satisfies_so(translated, s)
            asp_val = asp_holds_so(translated, s)
            assert so_val is True and asp_val is True


# ---------------------------------------------------------------------------
# 2. Real producer outputs, differential over exhaustive small structures.
# ---------------------------------------------------------------------------

class TestCircumscriptionProducerDifferential:
    def test_two_circumscribed_predicates_every_structure_up_to_2(self):
        # circumscription_formula with TWO circumscribed predicates builds a
        # genuine 2-level ∀-chain (∀P'∀Q'(...)), nested inside an And -- the
        # exact shape that broke a naive "strip + negate the whole sentence"
        # encoding (see asp_holds_so's own docstring); this is the regression
        # guard for that.
        premises = [Atom("P", (A,)), Atom("Q", (B,))]
        axiom = circumscription_entails_so(premises, {"P", "Q"}, Not(Atom("P", (B,))))
        preds = [("P", 1), ("Q", 1)]
        for size in (1, 2):
            domain = tuple(range(size))
            per_pred = [list(_powerset(_tuples(domain, ar))) for (_, ar) in preds]
            for combo in itertools.product(*per_pred):
                predicates = {sig: set(ext) for sig, ext in zip(preds, combo)}
                for a_val, b_val in itertools.product(domain, repeat=2):
                    s = Structure(domain, constants={"a": a_val, "b": b_val}, predicates=predicates)
                    assert asp_holds_so(axiom, s) == satisfies_so(axiom, s)

    def test_circumscription_formula_bare_and_wrapped_in_implies(self):
        # circumscription_formula's own output (no outer conclusion-Implies)
        # -- the ∀-block sits right under a top-level And (or bare, if
        # premises is empty).
        f1 = circumscription_formula([Atom("P", (A,))], {"P"})
        f2 = circumscription_formula([], {("P", 1)})  # bare SecondOrderQuantifier
        for f in (f1, f2):
            for size in (1, 2, 3):
                domain = tuple(range(size))
                for ext in _powerset(_tuples(domain, 1)):
                    for a_val in domain:
                        s = Structure(domain, constants={"a": a_val}, predicates={("P", 1): set(ext)})
                        assert asp_holds_so(f, s) == satisfies_so(f, s)


class TestDependenceProducerDifferential:
    def test_plain_fo_and_dependence_guarded_existential(self):
        sentences = [
            dep_parse("∀x ∃y (Q(x, y))"),                       # flat FOL, vacuous Skolem
            dep_parse("∀x ∃y (=(x, y) ∧ Q(x, y))"),              # y determined by x
        ]
        for f in sentences:
            translated = dependence_to_eso(f)
            for size in (1, 2, 3):
                domain = tuple(range(size))
                for ext in _powerset(_tuples(domain, 2)):
                    s = Structure(domain, predicates={("Q", 2): set(ext)})
                    assert asp_holds_so(translated, s) == satisfies_so(translated, s)
                    assert dependence_holds_eso(f, s, fast=True) == dependence_holds_eso(f, s, fast=False)


# ---------------------------------------------------------------------------
# 3. Seeded-random single-block battery: both polarities, arity 0/1/2,
#    equality, constants, function symbols, non-integer domains.
# ---------------------------------------------------------------------------

_CONNECTIVES = [And, Or, Implies]


def _rand_term(rng, consts, funcs, bound_vars):
    choice = rng.random()
    if bound_vars and choice < 0.35:
        return Variable(rng.choice(bound_vars))
    if funcs and choice > 0.75:
        fname, arity = rng.choice(funcs)
        return Function(fname, tuple(_rand_term(rng, consts, funcs, bound_vars) for _ in range(arity)))
    return Constant(rng.choice(consts))


def _rand_atom(rng, preds, consts, funcs, bound_vars, so_name, so_arity):
    if rng.random() < 0.15:
        t1 = _rand_term(rng, consts, funcs, bound_vars)
        t2 = _rand_term(rng, consts, funcs, bound_vars)
        return Atom("=", (t1, t2))
    options = list(preds) + [(so_name, so_arity)]
    name, arity = rng.choice(options)
    args = tuple(_rand_term(rng, consts, funcs, bound_vars) for _ in range(arity))
    return Atom(name, args)


def _rand_block_body(rng, preds, consts, funcs, bound_vars, so_name, so_arity, depth):
    if depth <= 0 or rng.random() < 0.4:
        return _rand_atom(rng, preds, consts, funcs, bound_vars, so_name, so_arity)
    choice = rng.random()
    if choice < 0.15:
        return Not(_rand_block_body(rng, preds, consts, funcs, bound_vars, so_name, so_arity, depth - 1))
    if choice < 0.75:
        conn = rng.choice(_CONNECTIVES)
        return conn(
            _rand_block_body(rng, preds, consts, funcs, bound_vars, so_name, so_arity, depth - 1),
            _rand_block_body(rng, preds, consts, funcs, bound_vars, so_name, so_arity, depth - 1),
        )
    v = rng.choice(["u", "w"])
    qtype = rng.choice(["∀", "∃"])
    return Quantifier(qtype, Variable(v),
                      _rand_block_body(rng, preds, consts, funcs, bound_vars + [v], so_name, so_arity, depth - 1))


def _rand_closed_fo(rng, preds, consts, funcs, depth):
    """A random CLOSED classical formula that never mentions the SO predicate
    (used as the "other side" of a connective the SO block is nested in)."""
    return _rand_block_body(rng, preds, consts, funcs, [], "__never__", 0, depth)


def _rand_structure(rng, domain, preds, consts, funcs):
    predicates = {(name, ar): {t for t in _tuples(domain, ar) if rng.random() < 0.5}
                 for name, ar in preds}
    constants = {c: rng.choice(domain) for c in consts}
    functions = {(fname, ar): {t: rng.choice(domain) for t in _tuples(domain, ar)}
                for fname, ar in funcs}
    return Structure(domain, constants=constants, functions=functions, predicates=predicates)


def _random_single_block_cases(seed, n):
    rng = random.Random(seed)
    preds = [("Q", 1), ("R", 2)]
    consts = ["a", "b"]
    funcs = [("f", 1)]
    cases = []
    for _ in range(n):
        so_arity = rng.choice([0, 1, 2])
        polarity = rng.choice(["∀", "∃"])
        body = _rand_block_body(rng, preds, consts, funcs, [], "P", so_arity, rng.choice([1, 2, 3]))
        block = SecondOrderQuantifier(polarity, "P", so_arity, body)
        shape = rng.choice(["bare", "not", "connective"])
        if shape == "bare":
            sentence = block
        elif shape == "not":
            sentence = Not(block)
        else:
            other = _rand_closed_fo(rng, preds, consts, funcs, rng.choice([0, 1, 2]))
            conn = rng.choice(_CONNECTIVES)
            sentence = conn(block, other) if rng.random() < 0.5 else conn(other, block)
        domain_size = rng.choice([1, 2, 3])
        domain = tuple(range(domain_size))
        structure = _rand_structure(rng, domain, preds, consts, funcs)
        cases.append((sentence, structure))
    return cases


@pytest.mark.parametrize("i,sentence,structure",
                         [(i, s, st) for i, (s, st) in enumerate(_random_single_block_cases(20260918, 200))])
def test_random_single_block_agrees_with_brute_force(i, sentence, structure):
    assert asp_holds_so(sentence, structure) == satisfies_so(sentence, structure)


def test_random_single_block_battery_is_not_vacuous():
    # Sanity on the generator itself: both True and False verdicts, and both
    # polarities, actually occur across the seeded battery (otherwise the
    # differential check above could pass trivially).
    cases = _random_single_block_cases(20260918, 200)
    verdicts = {satisfies_so(s, st) for s, st in cases}
    assert verdicts == {True, False}
    polarities = {_so_quantifier_chain(s)[0] for s, _ in cases}
    assert polarities == {"forall", "exists"}


class TestOrderComparisonNumericFallback:
    """Regression for the C24 review finding: an order comparison
    (``< > ≤ ≥``) with NO declared extension over a NUMERIC domain must fall
    back to the real numeric relation (tarski._order_value's rule 3), not to
    "no extension declared means empty" -- see asp_models._AspEncoder's
    _order_numeric_extension and its callers' docstrings for the fix.
    """

    def test_forall_block_over_undeclared_less_than(self):
        # Hand-derived: a<b with a=0, b=1 on domain {0,1,2} is numerically
        # TRUE (0<1), and no structure declares '<' -- so both the real
        # evaluator and asp_holds_so must agree it holds, regardless of the
        # (here vacuous, arity-0) SO block wrapped around it.
        body = Atom("<", (A, B))
        f = SecondOrderQuantifier("∀", "P", 0, body)
        s = Structure((0, 1, 2), constants={"a": 0, "b": 1})
        assert satisfies_so(f, s) is True
        assert asp_holds_so(f, s) is True

    def test_exists_block_over_undeclared_greater_than_false_case(self):
        # Hand-derived: a>b with a=0, b=1 is numerically FALSE (0 is not > 1).
        body = Atom(">", (A, B))
        f = SecondOrderQuantifier("∃", "P", 0, body)
        s = Structure((0, 1, 2), constants={"a": 0, "b": 1})
        assert satisfies_so(f, s) is False
        assert asp_holds_so(f, s) is False

    def test_declared_extension_still_overrides_the_numeric_fallback(self):
        # A DECLARED (even empty) extension for '<' wins over the numeric
        # reading -- 0<1 numerically, but the structure says otherwise.
        body = Atom("<", (A, B))
        f = SecondOrderQuantifier("∀", "P", 0, body)
        s = Structure((0, 1, 2), constants={"a": 0, "b": 1}, predicates={("<", 2): set()})
        assert satisfies_so(f, s) is False
        assert asp_holds_so(f, s) is False

    def test_order_comparison_inside_the_isolated_block_body_itself(self):
        # Unlike the cases above (the order comparison sits OUTSIDE the SO
        # predicate's own occurrence), this puts '<' genuinely inside the
        # quantified body: P(x) is chosen to hold only where x < b also
        # holds -- exercises _order_numeric_extension on a body the SO
        # choice rule and the order-comparison pinning coexist in.
        f = SecondOrderQuantifier(
            "∃", "P", 1,
            Quantifier("∀", X, Iff(Atom("P", (X,)), Atom("<", (X, B)))),
        )
        for n in (1, 2, 3):
            s = Structure(tuple(range(n)), constants={"b": n - 1})
            assert asp_holds_so(f, s) == satisfies_so(f, s) is True  # P={0..b-1} always exists

    def test_random_order_comparisons_agree(self):
        # A SEPARATE, self-contained random battery (not reusing
        # _random_single_block_cases's generator, which never emits an order
        # comparison and whose seeded output other tests depend on staying
        # fixed) that specifically targets '<','>','≤','≥' both with and
        # WITHOUT a declared extension, over numeric domains of varied size.
        rng = random.Random(20260918)
        ops = ["<", ">", "≤", "≥"]
        mismatches = []
        for _ in range(80):
            n = rng.choice([1, 2, 3, 4])
            domain = tuple(range(n))
            op = rng.choice(ops)
            a_val, b_val = rng.choice(domain), rng.choice(domain)
            predicates = {}
            if rng.random() < 0.3:  # sometimes declare an (arbitrary) extension
                predicates[(op, 2)] = {t for t in itertools.product(domain, repeat=2)
                                       if rng.random() < 0.5}
            s = Structure(domain, constants={"a": a_val, "b": b_val}, predicates=predicates)
            polarity = rng.choice(["∀", "∃"])
            f = SecondOrderQuantifier(polarity, "P", 0, Atom(op, (A, B)))
            so_val = satisfies_so(f, s)
            asp_val = asp_holds_so(f, s)
            if so_val != asp_val:
                mismatches.append((op, a_val, b_val, predicates, polarity, so_val, asp_val))
        assert not mismatches


def test_non_integer_domain_is_handled():
    # asp_holds_so builds its own domain index -- confirm it is not secretly
    # assuming an int/tuple(range(n)) domain the way asp_find_model's OWN
    # output always is.
    f = SecondOrderQuantifier("∃", "P", 1, Quantifier("∀", X, Atom("P", (X,))))
    s = Structure(("alice", "bob", "carol"))
    assert asp_holds_so(f, s) == satisfies_so(f, s) == True
    f2 = SecondOrderQuantifier("∀", "P", 1, Atom("P", (Constant("k"),)))
    s2 = Structure(("alice", "bob"), constants={"k": "alice"})
    assert asp_holds_so(f2, s2) == satisfies_so(f2, s2) == False


# ---------------------------------------------------------------------------
# 4. Fragment gate: every out-of-scope shape raises ValueError, not a wrong
#    answer.
# ---------------------------------------------------------------------------

class TestFragmentGate:
    def test_alternating_quantifiers_rejected(self):
        f = SecondOrderQuantifier("∀", "P", 1,
                                  SecondOrderQuantifier("∃", "R", 1, Atom("P", (X,))))
        with pytest.raises(ValueError, match="∀ and ∃|alternat"):
            asp_holds_so(f, Structure((0, 1)))

    def test_two_disconnected_blocks_rejected(self):
        f = And(SecondOrderQuantifier("∀", "P", 0, Atom("P", ())),
               SecondOrderQuantifier("∀", "R", 0, Atom("R", ())))
        with pytest.raises(ValueError):
            asp_holds_so(f, Structure((0,)))

    def test_block_nested_under_an_outer_object_quantifier_rejected(self):
        # ∀x (∀P (Iff(P(x), P(x)))) -- the block's own body has a free x
        # bound OUTSIDE the block; asp_holds_so evaluates the block as an
        # isolated closed sub-computation (see its own docstring) and does
        # not support this shape. secondorder.satisfies_so has no such
        # restriction (used elsewhere, e.g. Leibniz equality, in
        # test_secondorder_search.py).
        inner = SecondOrderQuantifier("∀", "P", 1, Atom("P", (X,)))
        f = Quantifier("∀", X, inner)
        with pytest.raises(ValueError, match="free object variable"):
            asp_holds_so(f, Structure((0, 1)))

    def test_unknown_quantifier_spelling_rejected(self):
        f = SecondOrderQuantifier("bogus", "P", 0, Atom("P", ()))
        with pytest.raises(ValueError, match="unknown"):
            asp_holds_so(f, Structure((0,)))

    def test_no_second_order_quantifier_is_accepted_as_plain_classical(self):
        f = Atom("Q", (A,))
        s = Structure((0, 1), constants={"a": 0}, predicates={("Q", 1): {(0,)}})
        assert asp_holds_so(f, s) is True
        assert asp_holds_so(f, s) == satisfies(f, s)


# ---------------------------------------------------------------------------
# Scale: an arity-2 domain size where MAX_RELATIONS already blocks
# satisfies_so outright, but asp_holds_so (propagation, not enumeration)
# still returns -- same spirit as asp_minimal_models's own scale tests.
# ---------------------------------------------------------------------------

def test_scale_beyond_max_relations():
    n = 5
    assert 2 ** (n ** 2) > MAX_RELATIONS  # sanity: this really is past the brute-force cap
    f = SecondOrderQuantifier("∃", "P", 2,
                              Quantifier("∀", X, Quantifier("∀", Y, Atom("P", (X, Y)))))
    s = Structure(tuple(range(n)))
    with pytest.raises(ValueError, match="MAX_RELATIONS"):
        satisfies_so(f, s)
    # Hand-derived: choosing P = the full domain**2 relation makes ∀x∀y P(x,y)
    # true, so the ∃-block holds -- True, and asp_holds_so must still return
    # (not raise) at this size.
    assert asp_holds_so(f, s) is True


# ---------------------------------------------------------------------------
# Wiring: the opt-in `fast=` parameter on secondorder.holds / so_find_model /
# so_find_countermodel / so_is_satisfiable_finite / so_is_valid_finite, and
# team_translation.dependence_holds_eso. Default False must be byte-identical
# to the pre-C24 behaviour; True must agree with it wherever the fast path
# does not raise.
# ---------------------------------------------------------------------------

class TestFastWiring:
    _PENGUIN_BIRD = Quantifier("∀", X, Implies(Atom("Penguin", (X,)), Atom("Bird", (X,))))
    _PENGUIN_AB = Quantifier("∀", X, Implies(Atom("Penguin", (X,)), Atom("Ab", (X,))))
    _BASE = [_PENGUIN_BIRD, _PENGUIN_AB, Atom("Bird", (TWEETY,)), Not(Atom("Penguin", (TWEETY,)))]

    def test_holds_default_is_byte_identical_to_before(self):
        f = SecondOrderQuantifier("∃", "P", 1, Quantifier("∀", X, Atom("P", (X,))))
        s = Structure((0, 1))
        assert holds(f, s) == holds(f, s, fast=False) == satisfies_so(f, s, {}, {})

    def test_holds_fast_agrees_with_default(self):
        f = SecondOrderQuantifier("∃", "P", 1, Quantifier("∀", X, Atom("P", (X,))))
        s = Structure((0, 1))
        assert holds(f, s, fast=True) == holds(f, s, fast=False)

    def test_so_is_valid_finite_fast_agrees_on_circumscription(self):
        axiom = circumscription_entails_so(self._BASE, {"Ab"}, Not(Atom("Ab", (TWEETY,))))
        slow = so_is_valid_finite(axiom, max_size=3, fast=False)
        fast = so_is_valid_finite(axiom, max_size=3, fast=True)
        assert slow is True and fast is True

    def test_so_find_countermodel_fast_witness_is_genuine(self):
        # An invalid SO sentence: not every relation is empty.
        f = SecondOrderQuantifier("∀", "P", 0, Not(Atom("P", ())))
        cm = so_find_countermodel(f, max_size=2, fast=True)
        assert cm is not None
        assert holds(f, cm, fast=True) is False
        assert holds(f, cm, fast=False) is False

    def test_so_is_satisfiable_finite_fast_agrees(self):
        f = SecondOrderQuantifier("∃", "P", 1, Quantifier("∀", X, Atom("P", (X,))))
        assert (so_is_satisfiable_finite(f, max_size=2, fast=True)
               == so_is_satisfiable_finite(f, max_size=2, fast=False) is True)

    def test_dependence_holds_eso_default_equals_holds_of_translation(self):
        f = dep_parse("∀x ∃y (=(x, y) ∧ Q(x, y))")
        s = Structure((0, 1), predicates={("Q", 2): {(0, 0), (1, 1)}})
        assert dependence_holds_eso(f, s) == holds(dependence_to_eso(f), s)

    def test_dependence_holds_eso_fast_agrees_with_default(self):
        f = dep_parse("∀x ∃y (=(x, y) ∧ Q(x, y))")
        for preds in ({(0, 0), (1, 1)}, {(0, 0), (0, 1)}, set()):
            s = Structure((0, 1), predicates={("Q", 2): preds})
            assert dependence_holds_eso(f, s, fast=True) == dependence_holds_eso(f, s, fast=False)


# ---------------------------------------------------------------------------
# emit_fixed_facts error paths (missing interpretation, non-total function).
# ---------------------------------------------------------------------------

class TestFixedFactsErrors:
    def test_missing_constant_interpretation_raises(self):
        f = SecondOrderQuantifier("∃", "P", 1, Atom("P", (Constant("k"),)))
        s = Structure((0, 1))  # "k" never interpreted
        with pytest.raises(ValueError, match="constant"):
            asp_holds_so(f, s)

    def test_non_total_function_raises(self):
        # The ∀x is INSIDE the block's own body (bound by the block, not
        # leaking in from an enclosing quantifier), so this exercises
        # emit_fixed_facts's function-totality check, not the free-variable
        # gate above.
        f = SecondOrderQuantifier("∃", "P", 1,
                                  Quantifier("∀", X, Atom("P", (Function("f", (X,)),))))
        s = Structure((0, 1), functions={("f", 1): {(0,): 1}})  # undefined at 1
        with pytest.raises(ValueError, match="total"):
            asp_holds_so(f, s)

    def test_predicate_value_outside_domain_raises(self):
        f = SecondOrderQuantifier("∃", "P", 1, Quantifier("∀", X, Atom("Q", (X,))))
        s = Structure((0, 1), predicates={("Q", 1): {(5,)}})  # 5 not in domain
        with pytest.raises(ValueError, match="domain"):
            asp_holds_so(f, s)
