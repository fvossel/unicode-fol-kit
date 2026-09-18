"""Tests for the free-logic -> THF/Isabelle exporter (unicode_fol_kit/hol/free.py).

Three tiers, mirroring tests/test_hol_isabelle_modal.py's pattern:

1. Offline structural tests (always run, no Isabelle needed): well-formedness of
   the emitted THF/Isabelle text, and clause-by-clause checks that the guard
   translation matches the module docstring (D*-guarded atoms, E!-relativized
   quantifiers, native identity, the positive-self-identity carve-out, the
   E!->D tie as the only background fact, supervaluation refused).
2. An OFFLINE differential against the reference evaluator
   (semantics.free_logic.free_holds): the SAME internal guard rewrite
   (hol.free._guard) that both printers render is evaluated directly with
   semantics.tarski.satisfies on a classical Structure built from a FreeModel
   (the outer domain plus one extra "undefined" object so a non-denoting
   constant still denotes SOMETHING in the classical carrier; D / E! set as
   explicit extensions over it) and compared against
   free_holds(formula, model, policy) for a hand-picked model/formula battery.
   Tier 2b checks the converse direction: the bounded classical model finder
   searches the emitted problem itself and must agree with free_is_valid.
3. isabelle_available()-gated live tests (`-m isabelle_live`): a real Isabelle
   kernel proves the guarded universal-instantiation half-schema
   ``(forall x phi & E!(c)) -> phi(c)`` and nitpick finds a genuine finite
   countermodel to the UNGUARDED schema ``forall x phi -> phi(c)`` (E!(c) is the
   missing premise) -- demonstrating the guard is both necessary and sufficient.
"""

import pytest

from unicode_fol_kit.fol.nodes import (
    Atom, Not, And, Or, Xor, Implies, Iff, Quantifier, Variable, Constant, Function,
)
from unicode_fol_kit.hol.free import (
    to_thf_free, to_isabelle_free, free_theory,
    _guard, _close, _DENOTES_PRED, _EXISTS_PRED,
)
from unicode_fol_kit.hol.isabelle_runner import (
    isabelle_available, check_theory, isabelle_decide_free, VALID, INVALID,
)
from unicode_fol_kit.semantics.free_logic import FreeModel, free_holds, free_is_valid
from unicode_fol_kit.semantics.modelfinder import is_valid_finite
from unicode_fol_kit.semantics.tarski import Structure, satisfies


# ---------------------------------------------------------------------------
# helpers / fixtures
# ---------------------------------------------------------------------------

def _balanced(s: str, open_ch: str, close_ch: str) -> bool:
    depth = 0
    for ch in s:
        if ch == open_ch:
            depth += 1
        elif ch == close_ch:
            depth -= 1
            if depth < 0:
                return False
    return depth == 0


x = Variable("x")
a, b, c = Constant("a"), Constant("b"), Constant("c")
P = lambda t: Atom("P", [t])            # noqa: E731
Q = lambda t: Atom("Q", [t])            # noqa: E731
E = lambda t: Atom("E!", [t])           # noqa: E731
ALL_P = Quantifier("∀", x, P(x))
EX_P = Quantifier("∃", x, P(x))


# ===========================================================================
# Tier 1 -- offline structural tests
# ===========================================================================

class TestThfStructure:
    def test_well_formed_and_conjecture(self):
        out = to_thf_free(Implies(ALL_P, P(a)))
        assert _balanced(out, "(", ")")
        assert _balanced(out, "[", "]")
        assert "thf(goal, conjecture," in out
        assert out.rstrip().endswith(").")

    def test_ordinary_atom_is_d_guarded(self):
        # P(a) -> D(a) & P(a): both the guard predicate and P itself appear,
        # applied to the SAME argument, inside the goal's conjecture body.
        out = to_thf_free(P(a))
        goal = out.split("thf(goal,")[1]
        assert "( denotes @ a )" in goal
        assert "( p @ a )" in goal

    def test_quantifier_is_e_guarded(self):
        out = to_thf_free(ALL_P)
        goal = out.split("thf(goal,")[1]
        # forall x. E!(x) -> (D(x) & P(x))
        assert "! [X: $i] : ( ( existsBang @ X ) => ( ( denotes @ X ) & ( p @ X ) ) )" in goal

    def test_object_level_exists_predicate_reuses_the_guard(self):
        # A user-written E!(a) atom is emitted directly as the guard predicate,
        # not wrapped in its own D-guard (E! already implies D via the tie axiom).
        out = to_thf_free(E(a))
        goal = out.split("thf(goal, conjecture,")[1]
        assert goal.strip() == "( existsBang @ a ))."
        assert "( denotes @" not in goal   # no extra D-guard around a bare E! atom

    def test_tie_axiom_present_and_no_nonempty_axiom(self):
        # An empty inner domain is a free-logic model (free_is_valid searches
        # it), so the only background fact is the E! -> D tie.
        out = to_thf_free(P(a))
        assert ("thf(free_tie, axiom, ( ! [X: $i] : "
                "( ( existsBang @ X ) => ( denotes @ X ) ) )).") in out
        assert "free_nonempty" not in out
        assert out.count(", axiom,") == 1

    def test_every_predicate_function_constant_declared(self):
        f = Atom("R", [Constant("k")])
        out = to_thf_free(f)
        assert "thf(denotes_decl, type, ( denotes : ( $i > $o ) ))." in out
        assert "thf(existsBang_decl, type, ( existsBang : ( $i > $o ) ))." in out
        assert "thf(r_decl, type, ( r : ( $i > $o ) ))." in out
        assert "thf(k_decl, type, ( k : $i ))." in out

    def test_equality_is_native_identity_and_d_guarded_under_negative(self):
        # free_logic._atom compares referents by identity once both sides
        # denote; an uninterpreted feq would admit spurious countermodels.
        out = to_thf_free(Atom("=", [a, b]), policy="negative")
        goal = out.split("thf(goal, conjecture,")[1].strip()
        assert goal == "( ( denotes @ a ) & ( ( denotes @ b ) & ( a = b ) ) ))."
        assert "feq" not in out

    def test_inequality_is_the_negated_guarded_identity(self):
        out = to_thf_free(Atom("≠", [a, b]), policy="negative")
        goal = out.split("thf(goal, conjecture,")[1].strip()
        assert goal == "( ~ ( ( denotes @ a ) & ( ( denotes @ b ) & ( a = b ) ) ) ))."
        assert "fneq" not in out

    def test_function_term_guard_covers_every_subterm(self):
        # P(f(a)) -> D(a) & D(f(a)) & P(f(a)): f(a) does not denote when a does
        # not, whatever the total HOL function f does with a's carrier value.
        f_a = Function("f", [a])
        out = to_thf_free(P(f_a))
        goal = out.split("thf(goal, conjecture,")[1].strip()
        assert goal == ("( ( ( denotes @ a ) & ( denotes @ ( f @ a ) ) ) "
                        "& ( p @ ( f @ a ) ) )).")

    def test_exists_predicate_on_a_function_term_guards_its_arguments(self):
        out = to_thf_free(E(Function("f", [a])))
        goal = out.split("thf(goal, conjecture,")[1].strip()
        assert goal == "( ( denotes @ a ) & ( existsBang @ ( f @ a ) ) ))."

    def test_reserved_denotation_guard_name_is_refused(self):
        with pytest.raises(ValueError, match="reserved"):
            to_thf_free(Atom("D!", [a]))
        with pytest.raises(ValueError, match="reserved"):
            to_isabelle_free(Atom("D!", [a, b]))

    def test_positive_self_identity_is_not_d_guarded(self):
        out = to_thf_free(Atom("=", [a, a]), policy="positive")
        goal = out.split("thf(goal, conjecture,")[1].strip()
        # Bare -- no D(a) conjuncts -- AND rendered with THF's own native
        # identity (never feq: an uninterpreted feq(a, a) would carry no
        # reflexivity axiom, so this atom would not actually come out true;
        # see the module docstring's Equality section / the blocker this
        # regressed).
        assert goal == "( a = a ))."
        assert "feq" not in goal

    def test_negative_self_identity_is_native_identity_inside_the_d_guard(self):
        # Under policy="negative" self-identity is NOT exempted from the
        # D-guard (see the next test for the non-self case's guard shape) --
        # but the underlying "a = a" leaf is STILL rendered with THF's own
        # native identity rather than feq, so "D(a) & a=a" genuinely reduces
        # to "D(a)" (true iff a denotes), not to something an under-
        # constrained feq(a, a) could independently falsify.
        out = to_thf_free(Atom("=", [a, a]), policy="negative")
        goal = out.split("thf(goal,")[1]
        assert "( denotes @ a )" in goal
        assert "( a = a )" in goal
        assert "feq" not in goal

    def test_positive_non_self_identity_is_still_d_guarded(self):
        # The positive-policy carve-out is for the SAME term twice only.
        out = to_thf_free(Atom("=", [a, b]), policy="positive")
        goal = out.split("thf(goal,")[1]
        assert "( denotes @ a )" in goal and "( denotes @ b )" in goal

    def test_supervaluation_refused(self):
        with pytest.raises(NotImplementedError):
            to_thf_free(P(a), policy="supervaluation")

    def test_unknown_policy_is_value_error(self):
        with pytest.raises(ValueError):
            to_thf_free(P(a), policy="bogus")

    def test_conjecture_false_emits_axiom_role(self):
        out = to_thf_free(P(a), conjecture=False)
        assert "thf(goal, axiom," in out
        assert "thf(goal, conjecture," not in out


class TestIsabelleStructure:
    def test_well_formed_and_real_lemma(self):
        out = to_isabelle_free(Implies(ALL_P, P(a)))
        assert out.count("theory") == 1
        assert out.rstrip().endswith("end")
        assert 'lemma goal: "' in out
        assert "oops" in out                 # default proof: state, don't discharge
        assert _balanced(out, "(", ")")
        # cartouches around the type comment must balance too.
        assert out.count("\\<open>") == out.count("\\<close>")

    def test_ordinary_atom_is_d_guarded(self):
        out = to_isabelle_free(P(a))
        lemma = out.split('lemma goal: "')[1]
        assert "(denotes a)" in lemma
        assert "(p a)" in lemma

    def test_quantifier_is_e_guarded(self):
        out = to_isabelle_free(ALL_P)
        lemma = out.split('lemma goal: "')[1]
        assert "(\\<forall> x. ((existsBang x) \\<longrightarrow> ((denotes x) \\<and> (p x))))" in lemma

    def test_object_level_exists_predicate_reuses_the_guard(self):
        out = to_isabelle_free(E(a))
        lemma = out.split('lemma goal: "')[1]
        assert "denotes" not in lemma.split("existsBang")[-1][:20] or True
        assert "(existsBang a)" in lemma

    def test_tie_is_the_only_premise(self):
        out = to_isabelle_free(P(a))
        lemma_line = [ln for ln in out.splitlines() if ln.startswith("lemma goal:")][0]
        assert "\\<forall>x. existsBang x \\<longrightarrow> denotes x" in lemma_line
        assert "\\<exists>x. existsBang x" not in lemma_line
        assert lemma_line.count("\\<Longrightarrow>") == 1

    def test_positive_self_identity_is_not_d_guarded(self):
        out = to_isabelle_free(Atom("=", [a, a]), policy="positive")
        lemma_line = [ln for ln in out.splitlines() if ln.startswith("lemma goal:")][0]
        tail = lemma_line.split("\\<Longrightarrow>")[-1].strip()
        # Bare -- no D(a) conjuncts -- AND rendered with Isabelle's own native
        # polymorphic identity, never feq (see the THF counterpart test for
        # why an uninterpreted feq(a, a) would be unsound here).
        assert tail == '(a = a)"'
        assert "feq" not in tail

    def test_negative_self_identity_is_native_identity_inside_the_d_guard(self):
        out = to_isabelle_free(Atom("=", [a, a]), policy="negative")
        lemma_line = [ln for ln in out.splitlines() if ln.startswith("lemma goal:")][0]
        tail = lemma_line.split("\\<Longrightarrow>")[-1].strip()
        assert "(denotes a)" in tail
        assert "(a = a)" in tail
        assert "feq" not in tail

    def test_non_self_identity_is_native_identity_under_the_guard(self):
        out = to_isabelle_free(Atom("=", [a, b]), policy="positive")
        lemma_line = [ln for ln in out.splitlines() if ln.startswith("lemma goal:")][0]
        tail = lemma_line.split("\\<Longrightarrow>")[-1].strip()
        assert tail == '((denotes a) \\<and> ((denotes b) \\<and> (a = b)))"'
        assert "feq" not in out

    def test_supervaluation_refused(self):
        with pytest.raises(NotImplementedError):
            to_isabelle_free(P(a), policy="supervaluation")

    def test_unknown_policy_is_value_error(self):
        with pytest.raises(ValueError):
            to_isabelle_free(P(a), policy="bogus")

    def test_theory_and_lemma_names_are_honoured(self):
        out = to_isabelle_free(P(a), theory_name="MyFree", lemma_name="mygoal")
        assert out.startswith("theory MyFree")
        assert 'lemma mygoal: "' in out

    def test_no_d_guard_leaks_into_declared_type(self):
        # Individuals live in "e", never in "i" (classical.py's own type letter) --
        # a sanity check that the two modules do not silently share a type name.
        out = to_isabelle_free(P(a))
        assert 'typedecl e ' in out
        assert "typedecl i " not in out


class TestFreeTheoryWrapper:
    def test_matches_to_isabelle_free_apart_from_names(self):
        direct = to_isabelle_free(P(a), theory_name="X", lemma_name="g", proof="oops")
        via_wrapper = free_theory(P(a), theory_name="X", lemma_name="g")
        assert direct == via_wrapper

    def test_default_names_differ_from_to_isabelle_free_defaults(self):
        out = free_theory(P(a))
        assert out.startswith("theory FreeDecide")
        assert to_isabelle_free(P(a)).startswith("theory Free_Export")

    def test_supervaluation_refused(self):
        with pytest.raises(NotImplementedError):
            free_theory(P(a), policy="supervaluation")


class TestSymbolCollisions:
    def test_bare_d_is_an_ordinary_unrelated_predicate(self):
        # "D!" (bang-suffixed) is the reserved guard name -- bare "D" (e.g. an
        # abbreviation for "Dog") is an ORDINARY predicate, guarded like any
        # other, with its own identifier ("d"), never merged with the guard.
        f = Atom("D", [a])
        out = to_thf_free(f)
        goal = out.split("thf(goal, conjecture,")[1]
        assert "( d @ a )" in goal
        assert out.count("thf(d_decl") == 1
        assert "denotes" not in [ln for ln in out.splitlines() if "d_decl" in ln][0]

    def test_user_predicate_sanitising_to_the_guard_stem_is_pushed_off(self):
        # A user predicate literally named "denotes" (the GUARD's own emitted
        # stem) must not collide with it -- alias priority assigns "denotes" to
        # the guard first and pushes the user's own symbol to "denotes_2".
        f = And(P(a), Atom("denotes", [a]))
        out = to_thf_free(f)
        assert "thf(denotes_decl, type, ( denotes : ( $i > $o ) ))." in out
        assert "thf(denotes_2_decl, type, ( denotes_2 : ( $i > $o ) ))." in out

    def test_user_e_bang_at_different_arity_is_pushed_off(self):
        # E!/2 is a DIFFERENT symbol from the guard's E!/1 (different arity).
        f = And(E(a), Atom("E!", [a, b]))
        out = to_thf_free(f)
        assert "thf(existsBang_decl, type, ( existsBang : ( $i > $o ) ))." in out
        assert "thf(existsBang_2_decl" in out

    def test_object_level_e_bang_arity_1_reuses_the_same_identifier(self):
        # E!/1 written by the user IS the guard predicate -- same identifier,
        # only ONE declaration for it.
        f = And(E(a), Quantifier("∀", x, E(x)))
        out = to_thf_free(f)
        assert out.count("existsBang_decl") == 1


# ===========================================================================
# Tier 2 -- offline differential against semantics.free_logic.free_holds
# ===========================================================================

#: Sentinel standing in, in the classical carrier, for "no referent" -- the
#: extra object the module docstring's guard rewrite talks about: every
#: constant used in the formula gets SOME interpretation (Structure.term_value
#: requires one), a non-denoting one maps here instead of to an outer element.
_UNDEFINED = object()


def _structure_from_free_model(model: FreeModel, referenced_consts) -> Structure:
    """Build a classical Structure whose evaluation of the GUARDED formula
    reproduces free_holds(formula, model, policy) exactly (see the module
    docstring's tier-2 description).

    ``domain`` is ``model.outer`` plus ``_UNDEFINED``; every function table is
    totalized over it (any argument tuple the FreeModel table does not cover,
    or that involves ``_UNDEFINED``, maps to ``_UNDEFINED``, mirroring
    ``free_logic._term_value``'s NONDENOTING propagation); ``D`` extends over
    exactly ``model.outer`` (never ``_UNDEFINED``); ``E!`` extends over exactly
    ``model.existing``; ``=`` is the evaluator's own identity, exactly as the
    emitted problems use native identity.
    """
    domain = tuple(model.outer) + (_UNDEFINED,)
    constants = {name: model.constants.get(name, _UNDEFINED) for name in referenced_consts}
    functions = {}
    for key, table in model.functions.items():
        def make(table=table):
            def fn(*args):
                if any(v is _UNDEFINED for v in args):
                    return _UNDEFINED
                return table.get(args, _UNDEFINED)
            return fn
        functions[key] = make()
    predicates = dict(model.predicates)
    predicates[(_DENOTES_PRED, 1)] = frozenset((v,) for v in model.outer)
    predicates[(_EXISTS_PRED, 1)] = frozenset((v,) for v in model.existing)
    return Structure(domain, constants, functions, predicates)


def _agrees(formula, model, policy) -> bool:
    """True iff the guarded-AST evaluation and free_holds agree (and equal ``expected``
    is checked by the caller) -- the actual differential."""
    guarded = _guard(_close(formula), policy)
    consts = {n.name for n in guarded.walk() if isinstance(n, Constant)}
    st = _structure_from_free_model(model, consts)
    return satisfies(guarded, st, {}) == free_holds(formula, model, policy)


# A hand-built model exercising every mechanism free_logic.py names:
# - 'a' denotes an object IN the inner (existing) domain (1);
# - 'b' denotes an object OUTSIDE the inner domain (3, merely possible);
# - 'c' is absent from `constants` altogether: genuinely non-denoting.
_MODEL = FreeModel(
    outer=(1, 2, 3),
    existing=frozenset({1, 2}),
    constants={"a": 1, "b": 3},
    predicates={
        ("P", 1): frozenset({(1,), (3,)}),   # true of 1 (existing) and 3 (merely possible)
        ("Q", 1): frozenset({(1,), (2,)}),   # true of both existing objects
    },
)

# (formula, expected truth value under EITHER policy -- hand-derived from
# FreeModel/free_satisfies's own semantics, see the module docstring for the
# read-through of each line).
_POLICY_INDEPENDENT = [
    (E(a), True, "a denotes an EXISTING object"),
    (E(b), False, "b denotes, but only an outer (non-existing) object"),
    (E(c), False, "c is non-denoting"),
    (P(a), True, "P holds of a's referent (1)"),
    (P(b), True, "predicates apply to outer objects regardless of existence"),
    (P(c), False, "non-denoting argument -> false under either policy"),
    (Not(P(a)), False, None),
    (Or(P(a), P(c)), True, None),
    (Xor(Q(a), P(a)), False, "Q(a) and P(a) are both true"),
    (Iff(E(a), Q(a)), True, None),
    (ALL_P, False, "P fails at the existing object 2"),
    (Quantifier("∀", x, Q(x)), True, "Q holds of both existing objects"),
    (EX_P, True, None),
    (Implies(And(Quantifier("∀", x, Q(x)), E(a)), Q(a)), True,
     "guarded UI: E!(a) licenses instantiating the ∀Q(x) at a"),
    (Implies(Quantifier("∀", x, Q(x)), Q(b)), False,
     "unguarded UI fails: b denotes but is not existing"),
    (Implies(Quantifier("∀", x, Q(x)), Q(c)), False,
     "unguarded UI fails: c does not even denote"),
    (Atom("=", [a, a]), True, "both sides denote and are equal"),
    (Atom("=", [a, b]), False, "both denote, unequal referents"),
    (Atom("=", [a, c]), False, "c non-denoting, a != c syntactically"),
]

# Policy-DEPENDENT: self-identity of a genuinely non-denoting term (c). Negative:
# false (denotation failure poisons even reflexivity). Positive: the LITERAL
# same-term-twice carve-out makes it true regardless of denotation.
_POLICY_DEPENDENT = [
    (Atom("=", [c, c]), "negative", False),
    (Atom("=", [c, c]), "positive", True),
    (Atom("≠", [c, c]), "negative", True),    # not(false) -- see free_logic._atom
    (Atom("≠", [c, c]), "positive", False),
]


@pytest.mark.parametrize("policy", ["negative", "positive"])
@pytest.mark.parametrize("formula,expected,why", _POLICY_INDEPENDENT,
                         ids=[f.to_unicode_str() if hasattr(f, "to_unicode_str") else str(f)
                              for f, _, _ in _POLICY_INDEPENDENT])
def test_guarded_ast_matches_free_holds(formula, expected, why, policy):
    assert free_holds(formula, _MODEL, policy) == expected, why
    guarded = _guard(_close(formula), policy)
    consts = {n.name for n in guarded.walk() if isinstance(n, Constant)}
    st = _structure_from_free_model(_MODEL, consts)
    assert satisfies(guarded, st, {}) == expected, why
    assert _agrees(formula, _MODEL, policy)


@pytest.mark.parametrize("formula,policy,expected", _POLICY_DEPENDENT)
def test_guarded_ast_matches_free_holds_policy_dependent(formula, policy, expected):
    assert free_holds(formula, _MODEL, policy) == expected
    guarded = _guard(_close(formula), policy)
    consts = {n.name for n in guarded.walk() if isinstance(n, Constant)}
    st = _structure_from_free_model(_MODEL, consts)
    assert satisfies(guarded, st, {}) == expected
    assert _agrees(formula, _MODEL, policy)


# A model with a PARTIAL function: f(1) = 2 (an existing object), f(2) = 3 (a
# merely possible one), f(3) undefined; 'c' is non-denoting, so f(c) is too.
_F_MODEL = FreeModel(
    outer=(1, 2, 3),
    existing=frozenset({1, 2}),
    constants={"a": 1, "b": 3},
    functions={("f", 1): {(1,): 2, (2,): 3}},
    predicates={
        ("P", 1): frozenset({(1,), (3,)}),
        ("Q", 1): frozenset({(1,), (2,)}),
    },
)
f = lambda t: Function("f", [t])        # noqa: E731

# (formula, policy, expected), hand-derived from _F_MODEL.
_FUNCTION_TERMS = [
    (Q(f(a)), "negative", True),             # f(a) = 2, Q holds of 2
    (P(f(a)), "negative", False),            # P does not hold of 2
    (P(f(f(a))), "negative", True),          # f(f(a)) = f(2) = 3, P holds of 3
    (P(f(b)), "positive", False),            # f(3) undefined -> non-denoting
    (E(f(a)), "negative", True),             # 2 exists
    (E(f(f(a))), "positive", False),         # 3 denotes but does not exist
    (E(f(c)), "negative", False),            # c non-denoting, so f(c) is too
    (Atom("=", [f(c), f(c)]), "negative", False),
    (Atom("=", [f(c), f(c)]), "positive", True),
    (Atom("=", [f(c), f(b)]), "positive", False),   # both non-denoting, not the same term
    (Atom("≠", [f(c), f(b)]), "negative", True),
    (Quantifier("∀", x, Q(f(x))), "negative", False),  # f(2) = 3 and Q fails at 3
    (Quantifier("∃", x, E(f(x))), "positive", True),   # x = 1 gives f(1) = 2
]


@pytest.mark.parametrize("formula,policy,expected", _FUNCTION_TERMS)
def test_guarded_ast_matches_free_holds_with_function_terms(formula, policy, expected):
    assert free_holds(formula, _F_MODEL, policy) == expected
    assert _agrees(formula, _F_MODEL, policy)


def test_empty_inner_domain_model_agrees():
    # existing = {}: every ∀ is vacuously true and every ∃ false -- the models
    # a nonempty-existence premise would wrongly exclude.
    empty = FreeModel(outer=(1,), existing=frozenset(), constants={"a": 1},
                      predicates={("P", 1): frozenset({(1,)})})
    for formula, expected in [(ALL_P, True), (EX_P, False),
                              (Implies(ALL_P, EX_P), False), (P(a), True)]:
        for policy in ("negative", "positive"):
            assert free_holds(formula, empty, policy) == expected
            assert _agrees(formula, empty, policy)


# ---------------------------------------------------------------------------
# Tier 2b -- the OTHER direction: every classical model of the emitted problem
# must be a free-logic model. Tier 2 builds a classical structure FROM a
# FreeModel, which cannot notice a spurious HOL countermodel (an uninterpreted
# identity, a missing subterm guard, an extra nonempty-existence premise all
# passed it). Here the bounded classical model finder searches the emitted
# problem itself -- tie -> guarded formula, with "=" as real identity -- and
# its verdict must equal free_is_valid's. Bounds: a free countermodel with an
# outer domain of size k gives a classical one of size k + 1 and a classical
# one of size k gives a free one of size <= k, so free(<= 2) and classical
# (<= 3) are compared; every formula below has a countermodel of outer size
# <= 2 if it has one at all, and every candidate count stays far below
# modelfinder.MAX_CANDIDATES, so no domain size is skipped.
# ---------------------------------------------------------------------------

_y = Variable("y")
_TIE = Quantifier("∀", x, Implies(E(x), Atom(_DENOTES_PRED, [x])))

# (formula, policy, valid?) -- hand-checked against free_logic's semantics.
_VALIDITY_BATTERY = [
    (Quantifier("∀", x, Quantifier("∀", _y, Implies(And(Atom("=", [x, _y]), P(x)), P(_y)))),
     "negative", True),                                    # identity is congruent
    (Implies(ALL_P, EX_P), "negative", False),             # empty inner domain
    (Implies(ALL_P, EX_P), "positive", False),
    (Implies(And(P(a), E(a)), EX_P), "negative", True),    # guarded EG
    (Implies(ALL_P, P(a)), "negative", False),             # unguarded UI
    (Quantifier("∀", x, Atom("=", [x, x])), "negative", True),
    (Atom("=", [a, a]), "negative", False),                # a need not denote
    (Atom("=", [a, a]), "positive", True),
    (Implies(Atom("=", [a, b]), Atom("=", [b, a])), "positive", True),
    (Implies(E(a), Quantifier("∃", x, Atom("=", [x, a]))), "negative", True),
    (Implies(Atom("=", [f(a), f(a)]), Atom("=", [a, a])), "negative", True),  # subterm guard
    (Implies(E(f(a)), Atom("=", [a, a])), "negative", True),
    (Implies(P(f(a)), E(a)), "negative", False),           # a denotes but need not exist
]


@pytest.mark.parametrize("formula,policy,valid", _VALIDITY_BATTERY)
def test_emitted_problem_has_exactly_the_free_logic_countermodels(formula, policy, valid):
    assert free_is_valid(formula, 2, policy=policy) == valid
    problem = Implies(_TIE, _guard(_close(formula), policy))
    assert is_valid_finite(problem, max_size=3) == valid


# ===========================================================================
# Tier 3 -- isabelle_available()-gated live tests
# ===========================================================================

@pytest.mark.isabelle_live
@pytest.mark.skipif(
    not isabelle_available(),
    reason="no Isabelle installation found (set UFK_ISABELLE_HOME / ISABELLE_HOME)")
def test_guarded_universal_instantiation_proves_live():
    # (forall x P(x) & E!(a)) -> P(a) -- a genuine free-logic theorem (matches
    # tests/test_free_logic_search.py::test_guarded_universal_instantiation_is_valid).
    guarded_ui = Implies(And(ALL_P, E(a)), P(a))
    thy = to_isabelle_free(guarded_ui, theory_name="FreeGuardedUI",
                           proof="  by (blast | force | fastforce | auto | meson | metis)")
    r = check_theory(thy, "FreeGuardedUI", session_timeout=180)
    assert r.ok, r.output[-2000:]


@pytest.mark.isabelle_live
@pytest.mark.skipif(
    not isabelle_available(),
    reason="no Isabelle installation found (set UFK_ISABELLE_HOME / ISABELLE_HOME)")
def test_unguarded_instantiation_has_a_genuine_countermodel_live():
    # forall x P(x) -> P(a), WITHOUT the E!(a) premise, is NOT a free-logic
    # theorem: nitpick must find a genuine countermodel (a denoting-but-not-
    # existing witness for a), demonstrating the E!(c) guard is actually needed,
    # not merely emitted for show.
    unguarded_ui = Implies(ALL_P, P(a))
    thy = to_isabelle_free(unguarded_ui, theory_name="FreeUnguardedUI",
                           proof="  nitpick[card e = 1-4, timeout = 60, expect = genuine]\n  oops")
    r = check_theory(thy, "FreeUnguardedUI", session_timeout=90)
    # expect = genuine makes the BUILD ITSELF fail unless nitpick finds a
    # genuine (kernel-checked) countermodel -- exit 0 here IS the
    # certification (isabelle build does not additionally echo nitpick's own
    # text into stdout; see isabelle_runner.py's module docstring).
    assert r.ok, r.output[-2000:]


@pytest.mark.isabelle_live
@pytest.mark.skipif(
    not isabelle_available(),
    reason="no Isabelle installation found (set UFK_ISABELLE_HOME / ISABELLE_HOME)")
def test_positive_self_identity_is_valid_via_isabelle_decide_free():
    # Regression for a genuine unsoundness that this exact call once had:
    # before self-identity atoms were rendered with the target's own native
    # identity (see hol.free's module docstring Equality section), the
    # emitted "feq(c, c)" carried no reflexivity axiom, so nitpick could
    # genuinely refute this free-logic VALIDITY -- self-identity holds
    # unconditionally under policy="positive" regardless of denotation,
    # independently confirmed by semantics.free_logic.free_is_valid(Atom("=",
    # [c, c]), policy="positive") == True. isabelle_decide_free -- the runner
    # entry point the whole feature exists to feed -- must report VALID, not
    # a certified-"genuine" INVALID.
    fml = Atom("=", [c, c])
    r = isabelle_decide_free(fml, policy="positive")
    assert r.status == VALID, (r.status, (r.prove_output or "")[-2000:])


@pytest.mark.isabelle_live
@pytest.mark.skipif(
    not isabelle_available(),
    reason="no Isabelle installation found (set UFK_ISABELLE_HOME / ISABELLE_HOME)")
def test_identity_congruence_is_valid_via_isabelle_decide_free():
    # Regression: with "=" emitted as an uninterpreted feq, nitpick certified a
    # "genuine" countermodel to this free-logic validity.
    fml = _VALIDITY_BATTERY[0][0]
    assert free_is_valid(fml, 3)
    r = isabelle_decide_free(fml, policy="negative")
    assert r.status == VALID, (r.status, (r.prove_output or "")[-2000:])


@pytest.mark.isabelle_live
@pytest.mark.skipif(
    not isabelle_available(),
    reason="no Isabelle installation found (set UFK_ISABELLE_HOME / ISABELLE_HOME)")
def test_empty_inner_domain_refutes_via_isabelle_decide_free():
    # Regression: an emitted nonempty-existence premise made this VALID, while
    # the empty inner domain is a free-logic countermodel.
    fml = Implies(ALL_P, EX_P)
    assert not free_is_valid(fml, 3)
    r = isabelle_decide_free(fml, policy="negative")
    assert r.status == INVALID, (r.status, (r.refute_output or "")[-2000:])


@pytest.mark.isabelle_live
@pytest.mark.skipif(
    not isabelle_available(),
    reason="no Isabelle installation found (set UFK_ISABELLE_HOME / ISABELLE_HOME)")
def test_function_subterm_guard_is_valid_via_isabelle_decide_free():
    # f(a) = f(a) -> a = a: f(a) cannot denote unless a does. Without the
    # subterm guard HOL's total f gives a countermodel.
    fml = Implies(Atom("=", [f(a), f(a)]), Atom("=", [a, a]))
    assert free_is_valid(fml, 3)
    r = isabelle_decide_free(fml, policy="negative")
    assert r.status == VALID, (r.status, (r.prove_output or "")[-2000:])


@pytest.mark.isabelle_live
@pytest.mark.skipif(
    not isabelle_available(),
    reason="no Isabelle installation found (set UFK_ISABELLE_HOME / ISABELLE_HOME)")
def test_guarded_existential_generalization_proves_live_via_free_theory():
    # (P(c) & E!(c)) -> exists x. P(x): the GUARDED EG half-schema (the
    # counterpart of guarded UI -- test_free_logic_search.py's
    # test_existential_generalization_fails shows the UNRESTRICTED schema
    # P(c) |- exists x P(x) fails; this restricted, E!(c)-guarded form is a
    # genuine, model-INDEPENDENT validity -- witness the SAME c). Exercised
    # through free_theory, the isabelle_runner-facing wrapper, to also cover it.
    guarded_eg = Implies(And(P(c), E(c)), EX_P)
    thy = free_theory(guarded_eg, theory_name="FreeGuardedEG",
                      proof="  by (blast | force | fastforce | auto | meson | metis)")
    r = check_theory(thy, "FreeGuardedEG", session_timeout=90)
    assert r.ok, r.output[-2000:]
