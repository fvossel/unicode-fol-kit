"""Tests for the substructural provers: ILL (atp.linear) and the Lambek calculus L (atp.lambek).

Every derivability claim below is hand-checked against the sequent rules. On top of
the curated facts, three differential oracles keep the provers honest:

- **Classical soundness (Z3).** The forgetful collapse ILL→classical (⊗,& → ∧;
  ⊕ → ∨; ⊸ → →; !A → A; 𝟙 → ⊤) and Lambek→classical (• → ∧; A\\B and B/A → A → B)
  turns every derivable sequent ``Γ ⊢ C`` into a classically valid ``⋀Γ → C``
  (the collapse interprets each proof rule as a classical entailment). Checked with
  ``unicode_fol_kit.is_valid`` for every curated *and* seeded-random derivable
  sequent — a prover bug that derives too much gets caught here.
- **L embeds in ILL.** Forgetting order (• → ⊗; A\\B → A⊸B; B/A → A⊸B) maps every
  L rule to an admissible ILL rule, so every Lambek-derivable sequent must be
  ILL-derivable; the !-free ILL search is a decision procedure, so this is exact.
- **Prover/checker agreement.** Every derivation the provers return is re-validated
  by the step-by-step checkers, and hand-broken derivations are rejected.
"""

import random
from collections import Counter
from functools import reduce

import pytest

from unicode_fol_kit import (
    MSFLParser, is_valid,
    Atom, Not, And, Or, Implies, Iff,
    Tensor, With, OPlus, LinearImplies, OfCourse, One,
    Product, Under, Over,
)
# Top/Zero are not yet re-exported by the top-level package / fol.nodes (that
# wiring lands centrally); render_ill_formula is _linear_nodes' safe
# substitute for Node.to_unicode_str() on a formula that may contain them
# (see that module's comment above its register_operator calls).
from unicode_fol_kit.fol._linear_nodes import Top, Zero, render_ill_formula
from unicode_fol_kit.atp.linear import (
    ILLDerivation, ILLSequent, check_ill_proof, ill_derivable, ill_prove,
    render_ill_proof, verify_ill_proof,
)
from unicode_fol_kit.atp.lambek import (
    LambekDerivation, LambekSequent, check_lambek_proof, lambek_derivable,
    lambek_prove, render_lambek_proof, verify_lambek_proof,
)

_pl = MSFLParser(linear=True).parse
_pk = MSFLParser(lambek=True).parse


# ---------------------------------------------------------------------------
# The forgetful classical collapses (test-local: deliberately NOT part of the
# package API — see the "no classical export" tests at the bottom)
# ---------------------------------------------------------------------------

_TOP = Iff(Atom("_unit", ()), Atom("_unit", ()))  # a classically true closed formula
_BOTTOM = Not(_TOP)                               # a classically false closed formula


def _ill_collapse(f):
    """ILL → classical: ⊗,& → ∧; ⊕ → ∨; ⊸ → →; !A → A; 𝟙,⊤ → ⊤; 𝟘 → ⊥.

    ⊤ → classical True and 𝟘 → classical False keep the collapse sound: ⊤R's
    ``Γ ⊢ ⊤`` becomes ``... → ⊤`` (always valid) and 0L's ``Γ, 𝟘 ⊢ C`` becomes
    ``(... ∧ ⊥) → ...`` (vacuously valid) — exactly mirroring why 𝟙 → ⊤ is
    sound for 1R's ``⊢ 𝟙``.
    """
    if isinstance(f, (Tensor, With)):
        return And(_ill_collapse(f.left), _ill_collapse(f.right))
    if isinstance(f, OPlus):
        return Or(_ill_collapse(f.left), _ill_collapse(f.right))
    if isinstance(f, LinearImplies):
        return Implies(_ill_collapse(f.left), _ill_collapse(f.right))
    if isinstance(f, OfCourse):
        return _ill_collapse(f.formula)
    if isinstance(f, (One, Top)):
        return _TOP
    if isinstance(f, Zero):
        return _BOTTOM
    return f  # atomic


def _lambek_collapse(f):
    """Lambek → classical: • → ∧; A\\B → A → B; B/A → A → B (order forgotten)."""
    if isinstance(f, Product):
        return And(_lambek_collapse(f.left), _lambek_collapse(f.right))
    if isinstance(f, Under):   # fields as written: left=A, right=B in A\B
        return Implies(_lambek_collapse(f.left), _lambek_collapse(f.right))
    if isinstance(f, Over):    # fields as written: left=B, right=A in B/A
        return Implies(_lambek_collapse(f.right), _lambek_collapse(f.left))
    return f  # atomic category


def _classical_sequent(collapse, antecedents, goal):
    """The classical reading ``⋀Γ → C`` of a sequent under the given collapse."""
    body = collapse(goal)
    if not antecedents:
        return body
    return Implies(reduce(And, [collapse(a) for a in antecedents]), body)


def _lambek_to_ill(f):
    """The order-forgetting embedding L → ILL: • → ⊗; A\\B → A⊸B; B/A → A⊸B."""
    if isinstance(f, Product):
        return Tensor(_lambek_to_ill(f.left), _lambek_to_ill(f.right))
    if isinstance(f, Under):
        return LinearImplies(_lambek_to_ill(f.left), _lambek_to_ill(f.right))
    if isinstance(f, Over):
        return LinearImplies(_lambek_to_ill(f.right), _lambek_to_ill(f.left))
    return f


# ---------------------------------------------------------------------------
# Curated ILL facts (each hand-checked against the rules)
# ---------------------------------------------------------------------------

ILL_DERIVABLE = [
    (["A"], "A"),                       # Ax
    (["A", "B"], "A ⊗ B"),              # ⊗R splitting the context
    (["A", "A ⊸ B"], "B"),              # ⊸L (modus ponens, resources consumed)
    (["A ⊸ B", "A"], "B"),              # exchange is implicit (multiset)
    (["A & B"], "A"),                   # &L1
    (["A"], "A ⊕ B"),                   # ⊕R1
    (["!A"], "A"),                      # !D (dereliction)
    (["!A"], "!A ⊗ !A"),                # !C then ⊗R: the bank duplicates
    ([], "𝟙"),                          # 1R
    (["A"], "𝟙 ⊗ A"),                   # ⊗R with an empty split for 1R
    (["A ⊗ B"], "B ⊗ A"),               # ⊗ commutes: ⊗L then ⊗R (exchange)
    ([], "A ⊸ A"),                      # ⊸R then Ax
    (["A ⊗ (B ⊗ C)"], "(A ⊗ B) ⊗ C"),   # ⊗ reassociates via ⊗L, ⊗L, ⊗R, ⊗R
    (["A", "B"], "⊤"),                  # ⊤R: holds for ANY context, no premise
    (["A ⊗ 𝟘"], "B"),                   # ⊗L exposes 𝟘, then 0L (ex falso) for any B
]

ILL_NOT_DERIVABLE = [
    (["A"], "A ⊗ A"),      # no contraction: one A is not two
    (["A", "B"], "A"),     # no weakening: B cannot be discarded
    (["A & B"], "A ⊗ B"),  # a choice of one is not both
    (["A ⊗ B"], "A"),      # both resources must be used
    (["A"], "!A"),         # a single A is not an unlimited supply (!P needs !Γ)
    (["A ⊕ B"], "A"),      # the provider chooses, not you
    ([], "A"),             # nothing comes from nothing
    (["A ⊸ B"], "B"),      # the lollipop alone: no A to feed it
    (["⊤"], "A"),          # ⊤ carries no information: no ⊤L to consume it
]


def _parse_ill(antecedents, goal):
    return [_pl(a) for a in antecedents], _pl(goal)


@pytest.mark.parametrize("antecedents,goal", ILL_DERIVABLE,
                         ids=[f"{','.join(a)}⊢{g}" for a, g in ILL_DERIVABLE])
def test_ill_derivable_curated(antecedents, goal):
    ants, g = _parse_ill(antecedents, goal)
    d = ill_prove(ants, g)
    assert d is not None, "expected a derivation"
    assert ill_derivable(ants, g)
    # The derivation's end-sequent is the queried sequent (antecedent as multiset).
    assert Counter(d.conclusion.antecedent) == Counter(ants)
    assert d.conclusion.succedent == g
    # The checker re-validates every step.
    result = verify_ill_proof(d)
    assert result.ok, result.error
    # Classical soundness: the collapse of ⋀Γ → C is Z3-valid.
    assert is_valid(_classical_sequent(_ill_collapse, ants, g)), \
        f"collapse of derivable sequent not classically valid: {d.conclusion}"


@pytest.mark.parametrize("antecedents,goal", ILL_NOT_DERIVABLE,
                         ids=[f"{','.join(a)}⊬{g}" for a, g in ILL_NOT_DERIVABLE])
def test_ill_not_derivable_curated(antecedents, goal):
    ants, g = _parse_ill(antecedents, goal)
    assert ill_prove(ants, g) is None
    assert not ill_derivable(ants, g)


def test_ill_resource_vs_truth_contrast():
    # A&B ⊢ A⊗B is NOT ILL-derivable, yet its classical collapse (A∧B)→(A∧B) is
    # valid — the collapse is sound but forgets exactly the resource distinction.
    ants, g = _parse_ill(["A & B"], "A ⊗ B")
    assert not ill_derivable(ants, g)
    assert is_valid(_classical_sequent(_ill_collapse, ants, g))


def test_ill_bang_depth_bound_is_honest():
    # With ! the search is bounded: too small a bound just fails to find,
    # and the default bound recovers the derivation.
    bang_a, goal = _pl("!A"), _pl("!A ⊗ !A")
    assert ill_prove([bang_a], goal, max_depth=1) is None
    assert ill_derivable([bang_a], goal)


def test_ill_render_modus_ponens():
    d = ill_prove([_pl("A"), _pl("A ⊸ B")], _pl("B"))
    text = render_ill_proof(d)
    assert text == d.render()
    assert "⊢ B" in text and "[⊸L]" in text and "[Ax]" in text


def test_ill_checker_rejects_contraction():
    # A hand-built "proof" of A ⊢ A⊗A duplicating the axiom premise: the ⊗R
    # split must partition the antecedent, and {A} ≠ {A, A}.
    a = _pl("A")
    ax = ILLDerivation(ILLSequent((a,), a), "Ax")
    bad = ILLDerivation(ILLSequent((a,), Tensor(a, a)), "⊗R", (ax, ax))
    result = verify_ill_proof(bad)
    assert not result.ok
    assert result.error_rule == "⊗R"
    assert not check_ill_proof(bad)


def test_ill_checker_rejects_swapped_premise():
    a, b = _pl("A"), _pl("B")
    concl = ILLSequent((a, b), Tensor(a, b))
    ax_a = ILLDerivation(ILLSequent((a,), a), "Ax")
    ax_b = ILLDerivation(ILLSequent((b,), b), "Ax")
    good = ILLDerivation(concl, "⊗R", (ax_a, ax_b))
    assert check_ill_proof(good)
    # Swap one premise for the wrong axiom: the split no longer covers {A, B}.
    bad = ILLDerivation(concl, "⊗R", (ax_b, ax_b))
    assert not check_ill_proof(bad)
    assert verify_ill_proof(bad).error_rule == "⊗R"


def test_ill_checker_rejects_unknown_rule_and_weakening():
    a, b = _pl("A"), _pl("B")
    unknown = ILLDerivation(ILLSequent((a,), a), "Zap")
    assert not check_ill_proof(unknown)
    # Plain (un-banked) weakening dressed up as !W must be rejected: B is not !B.
    ax = ILLDerivation(ILLSequent((a,), a), "Ax")
    bad_w = ILLDerivation(ILLSequent((a, b), a), "!W", (ax,))
    assert not check_ill_proof(bad_w)


# ---------------------------------------------------------------------------
# Curated Lambek facts (each hand-checked against the rules)
# ---------------------------------------------------------------------------

LAMBEK_DERIVABLE = [
    (["A"], "A"),                            # Ax
    (["A", "A \\ B"], "B"),                  # \L: the argument on the LEFT
    (["B / A", "A"], "B"),                   # /L: the argument on the RIGHT
    (["A"], "B / (A \\ B)"),                 # type lifting (rightward)
    (["A"], "(B / A) \\ B"),                 # type lifting (leftward)
    (["A / B", "B / C"], "A / C"),           # composition
    (["A", "B"], "A • B"),                   # •R
    (["A • (B • C)"], "(A • B) • C"),        # L is associative ...
    (["(A • B) • C"], "A • (B • C)"),        # ... in both directions
    (["NP", "(NP \\ S) / NP", "NP"], "S"),   # "Alice sees Bob"
]

LAMBEK_NOT_DERIVABLE = [
    (["A \\ B", "A"], "B"),   # ORDER: \ wants its argument on the left
    (["A", "B / A"], "B"),    # ORDER: / wants its argument on the right
    (["A"], "A • A"),         # no contraction
    (["A • B"], "B • A"),     # no exchange
    (["B / A"], "A \\ B"),    # the two directions are distinct types
]


def _parse_lambek(antecedents, goal):
    return [_pk(a) for a in antecedents], _pk(goal)


@pytest.mark.parametrize("antecedents,goal", LAMBEK_DERIVABLE,
                         ids=[f"{','.join(a)}⊢{g}" for a, g in LAMBEK_DERIVABLE])
def test_lambek_derivable_curated(antecedents, goal):
    ants, g = _parse_lambek(antecedents, goal)
    d = lambek_prove(ants, g)
    assert d is not None, "expected a derivation"
    assert lambek_derivable(ants, g)
    # The end-sequent is the queried sequent, order preserved exactly.
    assert d.conclusion.antecedent == tuple(ants)
    assert d.conclusion.succedent == g
    result = verify_lambek_proof(d)
    assert result.ok, result.error
    # Classical soundness: the collapse of ⋀Γ → C is Z3-valid.
    assert is_valid(_classical_sequent(_lambek_collapse, ants, g))
    # L embeds in ILL: forgetting order must keep the sequent derivable
    # (the !-free ILL search is a decision procedure, so this is exact).
    assert ill_derivable([_lambek_to_ill(a) for a in ants], _lambek_to_ill(g))


@pytest.mark.parametrize("antecedents,goal", LAMBEK_NOT_DERIVABLE,
                         ids=[f"{','.join(a)}⊬{g}" for a, g in LAMBEK_NOT_DERIVABLE])
def test_lambek_not_derivable_curated(antecedents, goal):
    ants, g = _parse_lambek(antecedents, goal)
    assert lambek_prove(ants, g) is None
    assert not lambek_derivable(ants, g)


def test_lambek_order_sensitivity_vs_ill_exchange():
    # The SAME resources in the wrong order fail in L but succeed in ILL,
    # where exchange is implicit — the exact boundary between the two systems.
    ants, g = _parse_lambek(["A \\ B", "A"], "B")
    assert not lambek_derivable(ants, g)
    assert ill_derivable([_lambek_to_ill(a) for a in ants], _lambek_to_ill(g))


def test_lambek_empty_antecedent_rejected():
    with pytest.raises(ValueError):
        lambek_prove([], _pk("S"))
    with pytest.raises(ValueError):
        lambek_derivable([], _pk("S"))


def test_lambek_nl_example_render():
    # "Alice sees Bob": NP, (NP\S)/NP, NP ⊢ S — the transitive verb consumes the
    # object NP on its right, then the subject NP on its left.
    ants, g = _parse_lambek(["NP", "(NP \\ S) / NP", "NP"], "S")
    d = lambek_prove(ants, g)
    text = render_lambek_proof(d)
    assert text == d.render()
    assert "⊢ S" in text and "[/L]" in text and "[\\L]" in text


def test_lambek_checker_rejects_swapped_premises():
    a, b = _pk("A"), _pk("B")
    concl = LambekSequent((a, b), Product(a, b))
    ax_a = LambekDerivation(LambekSequent((a,), a), "Ax")
    ax_b = LambekDerivation(LambekSequent((b,), b), "Ax")
    good = LambekDerivation(concl, "•R", (ax_a, ax_b))
    assert check_lambek_proof(good)
    # Swap the premises: in L the split is ordered, so this is NOT a proof.
    bad = LambekDerivation(concl, "•R", (ax_b, ax_a))
    assert not check_lambek_proof(bad)
    assert verify_lambek_proof(bad).error_rule == "•R"


def test_lambek_checker_rejects_exchange_smuggling():
    # A hand-built "proof" of A•B ⊢ B•A whose •R premises read the context
    # backwards; the ordered concatenation check must reject it.
    a, b = _pk("A"), _pk("B")
    inner = LambekDerivation(
        LambekSequent((a, b), Product(b, a)), "•R",
        (LambekDerivation(LambekSequent((b,), b), "Ax"),
         LambekDerivation(LambekSequent((a,), a), "Ax")))
    outer = LambekDerivation(LambekSequent((Product(a, b),), Product(b, a)),
                             "•L", (inner,))
    assert not check_lambek_proof(outer)


def test_lambek_checker_rejects_empty_antecedent_node():
    a = _pk("A")
    bad = LambekDerivation(LambekSequent((), a), "Ax")
    result = verify_lambek_proof(bad)
    assert not result.ok
    assert "nonempty" in result.error


# ---------------------------------------------------------------------------
# Seeded random differential: classical soundness of everything derivable
# ---------------------------------------------------------------------------

def _rand_ill_formula(rng, depth):
    """A random small ILL formula over the atoms A / B."""
    if depth <= 0 or rng.random() < 0.35:
        return _pl(rng.choice("AB"))
    k = rng.randrange(12)
    if k < 3:
        return Tensor(_rand_ill_formula(rng, depth - 1), _rand_ill_formula(rng, depth - 1))
    if k < 5:
        return With(_rand_ill_formula(rng, depth - 1), _rand_ill_formula(rng, depth - 1))
    if k < 7:
        return OPlus(_rand_ill_formula(rng, depth - 1), _rand_ill_formula(rng, depth - 1))
    if k < 10:
        return LinearImplies(_rand_ill_formula(rng, depth - 1),
                             _rand_ill_formula(rng, depth - 1))
    if k < 11:
        return OfCourse(_rand_ill_formula(rng, depth - 1))
    return One()


def test_ill_random_derivable_collapse_is_classically_valid():
    """~60 seeded random ILL sequents the prover derives → Z3-valid collapses.

    Executable soundness: each cut-free ILL rule is classically valid under the
    forgetful collapse, so a derivable sequent whose collapse Z3 refutes would
    pinpoint a prover bug.
    """
    rng = random.Random(0x5E0)
    found = 0
    for _ in range(4000):
        ants = [_rand_ill_formula(rng, 2) for _ in range(rng.randrange(0, 3))]
        goal = _rand_ill_formula(rng, 2)
        # Tight bounds keep the sampling fast; they can only make the prover
        # miss derivable sequents (skipped), never derive extra ones — which is
        # all this soundness test is about.
        d = ill_prove(ants, goal, max_depth=14, max_steps=4000)
        if d is None:
            continue
        assert check_ill_proof(d)
        assert is_valid(_classical_sequent(_ill_collapse, ants, goal)), \
            f"unsound: derived {d.conclusion} but the collapse is not valid"
        found += 1
        if found >= 60:
            break
    assert found >= 60, f"only {found} derivable random ILL sequents found"


def _rand_lambek_formula(rng, depth):
    """A random small Lambek type over the atomic categories A / B."""
    if depth <= 0 or rng.random() < 0.4:
        return _pk(rng.choice("AB"))
    k = rng.randrange(3)
    l, r = _rand_lambek_formula(rng, depth - 1), _rand_lambek_formula(rng, depth - 1)
    return (Product, Under, Over)[k](l, r)


def test_lambek_random_derivable_collapse_and_ill_embedding():
    """~30 seeded random L sequents the prover derives → Z3-valid collapses AND
    ILL-derivable order-forgetting images (two independent oracles)."""
    rng = random.Random(20260703)
    found = 0
    for _ in range(6000):
        ants = [_rand_lambek_formula(rng, 2) for _ in range(rng.randrange(1, 4))]
        goal = _rand_lambek_formula(rng, 2)
        d = lambek_prove(ants, goal)
        if d is None:
            continue
        assert check_lambek_proof(d)
        assert is_valid(_classical_sequent(_lambek_collapse, ants, goal)), \
            f"unsound: derived {d.conclusion} but the collapse is not valid"
        assert ill_derivable([_lambek_to_ill(a) for a in ants], _lambek_to_ill(goal)), \
            f"L-derivable but not ILL-derivable after forgetting order: {d.conclusion}"
        found += 1
        if found >= 30:
            break
    assert found >= 30, f"only {found} derivable random Lambek sequents found"


# ---------------------------------------------------------------------------
# The deliberate no-classical-export boundary
# ---------------------------------------------------------------------------

def test_linear_and_lambek_have_no_classical_export():
    with pytest.raises(NotImplementedError):
        _pl("A ⊗ B").to_z3()
    with pytest.raises(NotImplementedError):
        _pl("!A").to_prover9()
    with pytest.raises(NotImplementedError):
        _pk("A \\ B").to_z3()
    with pytest.raises(NotImplementedError):
        _pk("A • B").to_tptp()


# ---------------------------------------------------------------------------
# The ILL additive units ⊤ (Top) and 𝟘 (Zero) — hand-checked.
# ---------------------------------------------------------------------------

def _ill_tree(d):
    """Yield every node of an ILLDerivation tree (pre-order)."""
    yield d
    for p in d.premises:
        yield from _ill_tree(p)


def test_top_derivable_for_several_contexts():
    # ⊤R holds unconditionally: Γ ⊢ ⊤ for ANY Γ — no premise, so it carries no
    # information about how Γ was built (contrast with 𝟙, which must be
    # consumed exactly).
    for ants in ([], ["A"], ["A", "B"], ["!C"], ["A ⊗ B"], ["A & B"], ["𝟙"]):
        a = [_pl(x) for x in ants]
        d = ill_prove(a, _pl("⊤"))
        assert d is not None, f"expected {ants} ⊢ ⊤ derivable"
        assert d.rule == "⊤R"
        assert not d.premises
        result = verify_ill_proof(d)
        assert result.ok, result.error
        assert Counter(d.conclusion.antecedent) == Counter(a)


def test_tensor_zero_derivable():
    # A ⊗ 𝟘 ⊢ B: ⊗L exposes the 𝟘, then 0L (ex falso quodlibet) closes it for
    # an ARBITRARY B — the proof must genuinely route through both rules.
    d = ill_prove([_pl("A ⊗ 𝟘")], _pl("B"))
    assert d is not None
    result = verify_ill_proof(d)
    assert result.ok, result.error
    rules = {n.rule for n in _ill_tree(d)}
    assert "0L" in rules and "⊗L" in rules


def test_top_implies_a_not_derivable():
    # ⊤ carries no information: there is no ⊤L rule to consume a ⊤ hypothesis,
    # and Ax needs the antecedent to equal the goal exactly — so ⊤ ⊸ A is NOT
    # derivable in general (for a genuinely distinct atom A), unlike ⊤ ⊸ ⊤.
    assert ill_prove([_pl("⊤")], _pl("A")) is None
    assert not ill_derivable([_pl("⊤")], _pl("A"))
    assert ill_prove([], _pl("⊤ ⊸ A")) is None
    # But ⊤ ⊸ ⊤ IS derivable (⊤R needs no hypothesis about ⊤ at all).
    assert ill_derivable([_pl("⊤")], _pl("⊤"))


def test_zero_alone_derives_anything():
    # 𝟘 ⊢ C for an arbitrary C — ILL's ex falso quodlibet. (For C = ⊤, ⊤R is
    # checked before 0L in the search and fires first — either rule proves the
    # sequent, so only the "⊤R or 0L" disjunction is asserted for that case.)
    for goal in ["Q", "A ⊗ B", "A ⊸ B", "!A", "⊤", "𝟙", "A & B", "A ⊕ B"]:
        d = ill_prove([_pl("𝟘")], _pl(goal))
        assert d is not None, f"expected 𝟘 ⊢ {goal} derivable"
        assert d.rule in ("0L", "⊤R") if goal == "⊤" else d.rule == "0L"
        result = verify_ill_proof(d)
        assert result.ok, result.error


def test_top_zero_checker_rejects_malformed_steps():
    # ⊤R's succedent must actually be ⊤.
    a = _pl("A")
    bad_top = ILLDerivation(ILLSequent((a,), a), "⊤R")
    result = verify_ill_proof(bad_top)
    assert not result.ok
    assert result.error_rule == "⊤R"
    assert not check_ill_proof(bad_top)
    # ⊤R takes no premises.
    ax = ILLDerivation(ILLSequent((a,), a), "Ax")
    bad_top_prem = ILLDerivation(ILLSequent((a,), _pl("⊤")), "⊤R", (ax,))
    assert not check_ill_proof(bad_top_prem)
    # 0L needs 𝟘 somewhere in the antecedent.
    bad_zero = ILLDerivation(ILLSequent((a,), _pl("Q")), "0L")
    result = verify_ill_proof(bad_zero)
    assert not result.ok
    assert result.error_rule == "0L"
    assert not check_ill_proof(bad_zero)


def test_top_zero_parse_round_trip():
    # render_ill_formula(parse(text)) re-parses to a structurally equal AST
    # (Node.to_unicode_str() cannot render Top/Zero yet — see the import
    # comment above; MSFLParser accepts the fully-parenthesised output either
    # way, since redundant parens are always legal).
    for text in ["⊤", "𝟘", "A ⊗ 𝟘 ⊸ B"]:
        node = _pl(text)
        rendered = render_ill_formula(node)
        again = _pl(rendered)
        assert again == node, f"{text!r} round-trip failed via {rendered!r}"

    assert isinstance(_pl("⊤"), Top)
    assert isinstance(_pl("𝟘"), Zero)
    mix = _pl("A ⊗ 𝟘 ⊸ B")
    assert isinstance(mix, LinearImplies)
    assert isinstance(mix.left, Tensor)
    assert isinstance(mix.left.left, Atom) and mix.left.left.predicate == "A"
    assert isinstance(mix.left.right, Zero)
    assert isinstance(mix.right, Atom) and mix.right.predicate == "B"


def test_top_zero_have_no_classical_export():
    with pytest.raises(NotImplementedError):
        _pl("⊤").to_z3()
    with pytest.raises(NotImplementedError):
        _pl("𝟘").to_prover9()
    with pytest.raises(NotImplementedError):
        _pl("A ⊗ 𝟘").to_tptp()
