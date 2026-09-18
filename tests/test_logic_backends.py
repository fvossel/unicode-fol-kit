"""Tests for the five per-logic ``ProverBackend`` adapters (atp/logic_backends.py).

Each backend is checked against its OWN honesty contract (never claiming more
than its underlying routine actually establishes), on hand-checked theorems
and non-theorems, and — where the kit has one — differentially against an
independent evaluator for that logic:

* intuitionistic — cross-checked against
  ``semantics.intuitionistic.int_valid`` (a different code path: it tries the
  bounded Kripke search first, G4ip only as the fallback);
* lambek/ILL — the search itself re-validates every PROVED result with its
  own checker (``check_lambek_proof`` / ``check_ill_proof``), so the sharpest
  external regression is the order-sensitivity pair that a classical
  And-fold would silently break;
* relevant — the "never PROVED" contract is asserted directly, and a REFUTED
  witness is round-tripped back through ``rel_satisfies``;
* hybrid — cross-checked against ``hybrid_is_valid`` (a different Z3 call
  shape: bare ``is_valid`` vs. this backend's own tracked ``Solver()``).

The last section covers the registry wiring: the five singleton default
chains, ``available_backends`` per new logic key, and — the routing
regression note (4) asks for explicitly — that ``api.prove(logic="auto")``
sends every PRE-EXISTING classical/modal input through the exact same
backend it did before these five were added, while newly routing
lambek/ill/hybrid syntax to the new ones.
"""

import pytest

from unicode_fol_kit import (
    MSFLParser,
    Atom, Not, And, Or, Implies, Iff, Quantifier, Variable,
    Nominal, At, Product, Under, Over,
    Tensor, With, OPlus, LinearImplies, OfCourse, One,
    RelevantModel, rel_satisfies,
    Verdict, get_backend, available_backends, default_chain, run_backend,
)
from unicode_fol_kit import api
from unicode_fol_kit.atp.protocol import PROVED, REFUTED, UNKNOWN
from unicode_fol_kit.fol.modal_translation import hybrid_is_valid
from unicode_fol_kit.semantics.intuitionistic import IntKripkeModel, int_valid

_P = MSFLParser()
_MP = MSFLParser(modal=True)
_LAM = MSFLParser(lambek=True)
_LIN = MSFLParser(linear=True)

P = Atom("P", [])
Q = Atom("Q", [])
R = Atom("R", [])


# ---------------------------------------------------------------------------
# IntBackend — propositional intuitionistic logic (Dyckhoff's G4ip)
# ---------------------------------------------------------------------------

# Classical non-theorems that intuitionistic logic famously rejects (each
# hand-checked: none of these three has an LJ/G4ip derivation — the Kripke
# semantics' "future worlds may add information" reading is exactly what
# blocks excluded middle, double-negation elimination, and Peirce's law).
_INT_NONTHEOREMS = [
    ("EM", Or(P, Not(P))),
    ("DNE", Implies(Not(Not(P)), P)),
    ("Peirce", Implies(Implies(Implies(P, Q), P), P)),
]

# Closure theorems every intuitionistic (indeed every sub-classical) logic
# proves: modus ponens and identity.
_INT_THEOREMS = [
    ("identity", [], Implies(P, P)),
    ("modus_ponens", [Implies(P, Q), P], Q),
]


@pytest.mark.parametrize("name,formula", _INT_NONTHEOREMS)
def test_int_backend_refutes_classical_nontheorems_with_a_witness(name, formula):
    v = run_backend("intuitionistic", formula)
    assert v.status == REFUTED, name
    assert v.logic == "intuitionistic"
    assert v.countermodel is not None and v.countermodel["kind"] == "intuitionistic_kripke"
    # Round-trip: rebuild the IntKripkeModel from the serialized witness and
    # independently confirm it really fails to force the formula — the
    # witness is not just present, it is CORRECT.
    d = v.countermodel
    model = IntKripkeModel(
        upset={int(w): frozenset(ws) for w, ws in d["upset"].items()},
        valuation={k: frozenset(ws) for k, ws in d["valuation"].items()})
    assert model.forces(d["world"], formula) is False


@pytest.mark.parametrize("name,premises,formula", _INT_THEOREMS)
def test_int_backend_proves_closure_theorems(name, premises, formula):
    v = run_backend("intuitionistic", formula, premises)
    assert v.status == PROVED, name
    assert v.logic == "intuitionistic"


def test_int_backend_quantified_input_is_unsupported_not_a_crash():
    quantified = Quantifier("∀", Variable("x"), Atom("P", [Variable("x")]))
    v = run_backend("intuitionistic", quantified)
    assert v.status == UNKNOWN and v.reason == "unsupported"


def test_int_backend_agrees_with_int_valid_differentially():
    """int_valid is a genuinely different code path for the REFUTED cases
    below (it finds a countermodel via the bounded Kripke search directly,
    never touching int_prove), so agreement here is a real cross-check, not
    the same code asked twice."""
    battery = [Or(P, Not(P)), Implies(Not(Not(P)), P), Implies(P, P),
              Implies(And(P, Q), P), Implies(P, Implies(Q, P))]
    for f in battery:
        v = run_backend("intuitionistic", f)
        assert (v.status == PROVED) == int_valid(f), f.to_unicode_str()


# ---------------------------------------------------------------------------
# LambekBackend — the Lambek calculus L
# ---------------------------------------------------------------------------

def test_lambek_backend_is_order_sensitive():
    """The textbook regression: A, A\\B |- B holds, A\\B, A |- B does not.
    This is exactly what silently breaks if premises were ever folded
    through a classical (order-blind) ∧, which is why LambekBackend bypasses
    the shared _implication helper entirely (see its docstring)."""
    A, B = _LAM.parse("A"), _LAM.parse("B")
    a_under_b = Under(A, B)   # A\B

    ok = run_backend("lambek", B, [A, a_under_b])
    assert ok.status == PROVED and ok.logic == "lambek"

    bad = run_backend("lambek", B, [a_under_b, A])
    assert bad.status == REFUTED
    assert bad.countermodel is None   # syntactic refutation, no model theory here


def test_lambek_backend_rejects_empty_premises():
    B = _LAM.parse("B")
    with pytest.raises(ValueError, match="nonempty"):
        run_backend("lambek", B, [])


def test_lambek_backend_over_and_product():
    # B/A, A |- B: /L then Ax — the mirror image of the \\ case above.
    A, B = _LAM.parse("A"), _LAM.parse("B")
    b_over_a = Over(B, A)   # B/A
    v = run_backend("lambek", B, [b_over_a, A])
    assert v.status == PROVED

    # A, B |- A•B: the product introduction rule (•R), trivially derivable.
    v2 = run_backend("lambek", Product(A, B), [A, B])
    assert v2.status == PROVED


# ---------------------------------------------------------------------------
# IllBackend — intuitionistic linear logic
# ---------------------------------------------------------------------------

def test_ill_backend_refutes_weakening_definitively():
    # A⊗B |- A is NOT derivable: B is a resource that must be USED, not
    # discarded. Neither side has "!", so this is the complete !-free
    # decision procedure: the False is a genuine REFUTED, not a bound.
    A, B = _LIN.parse("A"), _LIN.parse("B")
    v = run_backend("ill", A, [Tensor(A, B)])
    assert v.status == REFUTED
    assert v.logic == "ill"
    assert v.countermodel is None    # syntactic refutation, no model theory here


def test_ill_backend_proves_tensor_commutativity():
    # A⊗B |- B⊗A: ⊗L unfolds the antecedent to {A,B}, then ⊗R re-splits it
    # in the swapped order — a genuine !-free ILL theorem.
    A, B = _LIN.parse("A"), _LIN.parse("B")
    v = run_backend("ill", Tensor(B, A), [Tensor(A, B)])
    assert v.status == PROVED


def test_ill_backend_underdepth_bound_hit_never_refuted_even_bang_free():
    """A⊗B |- B⊗A is provable (test_ill_backend_proves_tensor_commutativity,
    same sequent) — a genuine !-free ILL theorem, so the safe/complete depth
    (the sequent's total node size) is >= the derivation's actual height. A
    caller-supplied max_depth BELOW that safe bound must never be read as a
    definitive refutation: the search fails only because the budget was cut
    short, not because no derivation exists, so this must come back
    UNKNOWN(bound_hit), matching the '!'-bearing bound_hit path even though
    no '!' occurs anywhere in this sequent. (Regression for the bug where
    IllBackend reported REFUTED here — gated only on the absence of '!',
    never on whether max_depth actually reached the safe bound.)"""
    A, B = _LIN.parse("A"), _LIN.parse("B")
    v = run_backend("ill", Tensor(B, A), [Tensor(A, B)], max_depth=1)
    assert v.status == UNKNOWN and v.reason == "bound_hit"
    assert v.status != REFUTED
    # Sanity: the same sequent at (or above) the safe default depth is a
    # genuine PROVED, confirming max_depth=1 alone was the truncation.
    v_default = run_backend("ill", Tensor(B, A), [Tensor(A, B)])
    assert v_default.status == PROVED


def test_ill_backend_bang_bound_hit_never_refuted():
    """!A ⊸ !A⊗!A IS provable via contraction (!C) at the default depth —
    hand-verified separately below — so to exercise the HONEST-incompleteness
    path deterministically we force an insufficient max_depth: the search
    then fails not because the sequent is refuted but because the budget ran
    out, and since '!' is present the backend must report UNKNOWN(bound_hit),
    never REFUTED."""
    A = _LIN.parse("A")
    bang_formula = LinearImplies(OfCourse(A), Tensor(OfCourse(A), OfCourse(A)))
    v = run_backend("ill", bang_formula, max_depth=0)
    assert v.status == UNKNOWN and v.reason == "bound_hit"


def test_ill_backend_bang_theorem_provable_at_default_depth():
    # !A ⊸ !A⊗!A: contraction (!C) duplicates !A, then ⊗R splits the two
    # copies and each closes by Ax — a genuine ILL theorem, well within the
    # default depth bound (2*total_size + 4).
    A = _LIN.parse("A")
    bang_formula = LinearImplies(OfCourse(A), Tensor(OfCourse(A), OfCourse(A)))
    v = run_backend("ill", bang_formula)
    assert v.status == PROVED


# ---------------------------------------------------------------------------
# RelevantBackend — the relevant logic B
# ---------------------------------------------------------------------------

# Genuine B-theorems (see tests/test_relevant.py's VALID_IN_B for the full
# hand-derived justification battery; identity is pointwise trivial).
_B_THEOREMS = [Implies(P, P), Implies(And(P, Q), P)]

# Genuine B-NON-theorems, each with a textbook 2-world Routley–Meyer
# countermodel (hand-derived in tests/test_relevant.py's INVALID_IN_B):
# positive paradox (irrelevant antecedent) and ex falso quodlibet.
_B_NONTHEOREMS = [Implies(P, Implies(Q, P)), Implies(And(P, Not(P)), Q)]


@pytest.mark.parametrize("formula", _B_THEOREMS)
def test_relevant_backend_never_proves_even_a_genuine_theorem(formula):
    """The standing invariant: rel_countermodel/rel_valid are sound but
    INCOMPLETE, so even a real B-theorem (no countermodel exists at all,
    let alone within the bound) must come back UNKNOWN(bound_hit), never
    PROVED — the honest B ⊨ φ answer needs a real Isabelle proof, out of
    scope here (see the backend's own docstring)."""
    v = run_backend("relevant", formula)
    assert v.status != PROVED
    assert v.status == UNKNOWN and v.reason == "bound_hit"


@pytest.mark.parametrize("formula", _B_NONTHEOREMS)
def test_relevant_backend_refutes_with_a_verified_witness(formula):
    v = run_backend("relevant", formula)
    assert v.status == REFUTED
    assert v.logic == "relevant"
    d = v.countermodel
    assert d["kind"] == "relevant_routley_meyer"
    # Round-trip: rebuild the RelevantModel from the serialized dict and
    # independently re-confirm the refutation with rel_satisfies — the
    # exact "round-trips through rel_satisfies" check the spec calls for.
    model = RelevantModel(worlds=d["worlds"], normal=d["normal"], star=d["star"],
                          R=[tuple(t) for t in d["R"]],
                          valuation={k: set(vs) for k, vs in d["valuation"].items()})
    assert rel_satisfies(model, d["world"], formula) is False


def test_relevant_backend_never_proves_across_a_wider_battery():
    """A second, broader sweep of the "never PROVED" invariant (distinct
    from the parametrized theorem check above), covering formulas that mix
    proved-elsewhere connectives."""
    battery = [Implies(P, P), Iff(P, P), Implies(Or(P, Q), Or(P, Q)),
              Implies(Not(Not(P)), P), Implies(P, Not(Not(P)))]
    for f in battery:
        assert run_backend("relevant", f).status != PROVED


def test_relevant_backend_unsupported_node_is_unknown_not_a_crash():
    quantified = Quantifier("∀", Variable("x"), Atom("P", [Variable("x")]))
    v = run_backend("relevant", quantified)
    assert v.status == UNKNOWN and v.reason == "unsupported"


def test_relevant_backend_entailment_with_premises():
    # P, P→Q |- Q folds (via the shared classical ∧ helper — legitimate
    # here, B has a real ∧) into (P ∧ (P→Q)) → Q. This is genuinely
    # REFUTED at the default max_worlds=2, by a hand-checkable 2-world
    # countermodel that exploits B's non-normal-world "→" semantics
    # (vacuous truth when R is empty): normal world w0 with nothing true;
    # non-normal w1 with P true, Q false, R(w1, ., .) empty.
    #   w0 ⊨ P?        no (P only holds at w1)
    #   w0 ⊨ P→Q?      no — w0 is normal, so P→Q needs P⇒Q at EVERY world,
    #                  and w1 ⊨ P but w1 ⊭ Q
    #   => w0 ⊭ P∧(P→Q), so the antecedent fails at w0
    #   w1 ⊨ P?        yes
    #   w1 ⊨ P→Q?      yes — w1 is non-normal and R(w1,·,·) is empty, so
    #                  "for all x,y with R(w1,x,y): ..." holds vacuously
    #   => w1 ⊨ P∧(P→Q), but w1 ⊭ Q
    #   so the outer → fails at w0 (x=w1 is a counterexample to the
    #   universal reading normal worlds use) — REFUTED, not UNKNOWN.
    # This exercises the premise fold itself (not just the standing "never
    # PROVED" invariant, which this formula alone would not distinguish
    # from a broken fold): dropping or misordering a premise changes the
    # antecedent and would not reliably reproduce this exact witness.
    v = run_backend("relevant", Q, [P, Implies(P, Q)])
    assert v.status == REFUTED
    assert v.status != PROVED
    d = v.countermodel
    assert d["kind"] == "relevant_routley_meyer"
    model = RelevantModel(worlds=d["worlds"], normal=d["normal"], star=d["star"],
                          R=[tuple(t) for t in d["R"]],
                          valuation={k: set(vs) for k, vs in d["valuation"].items()})
    goal = Implies(And(P, Implies(P, Q)), Q)
    assert rel_satisfies(model, d["world"], goal) is False


# ---------------------------------------------------------------------------
# HybridBackend — hybrid modal logic H(@)
# ---------------------------------------------------------------------------

# Reuses the hand-checked H(@) validities/non-validities from
# tests/test_hybrid.py's VALID_K / INVALID_K batteries (each justified there
# by direct appeal to the Kripke/@ semantics); kept here as a differential
# cross-check against hybrid_is_valid, the pre-existing (bare-bool) route.
_HYBRID_VALID_K = [
    "@i i",                              # @ is reflexive: i holds at its own world.
    "@i (P → Q) → (@i P → @i Q)",        # @ is a normal modality (K-distribution).
    "(◇i ∧ @i P) → ◇P",                  # bridge law.
]
_HYBRID_INVALID_K = [
    "@i P → P",     # P may hold at the i-world but fail at the evaluation world.
    "i",            # a nominal fails at every world other than the one it names.
]


@pytest.mark.parametrize("text", _HYBRID_VALID_K)
def test_hybrid_backend_proves_hand_checked_validities(text):
    formula = _MP.parse(text)
    v = run_backend("hybrid", formula)
    assert v.status == PROVED
    assert v.logic == "hybrid"
    # Differential cross-check: hybrid_is_valid goes through a bare
    # is_valid() bool via a *different* Z3 call shape (untracked Solver, no
    # assert_and_track) than this backend's _z3_track_and_check.
    assert hybrid_is_valid(formula, frame="K") is True


@pytest.mark.parametrize("text", _HYBRID_INVALID_K)
def test_hybrid_backend_refutes_with_a_distinct_witness(text):
    formula = _MP.parse(text)
    v = run_backend("hybrid", formula)
    assert v.status == REFUTED
    assert v.countermodel is not None and v.countermodel["kind"] == "z3_model"
    assert hybrid_is_valid(formula, frame="K") is False


def test_hybrid_backend_frame_sensitivity():
    # (□P ∧ i) → P is the T schema pinned at a named world: it needs
    # reflexivity, so K refutes it but T/S4/S5 prove it (hand-checked in
    # tests/test_hybrid.py's test_frame_sensitivity_with_a_nominal).
    formula = _MP.parse("(□P ∧ i) → P")
    assert run_backend("hybrid", formula, frame="K").status == REFUTED
    assert run_backend("hybrid", formula, frame="T").status == PROVED
    assert run_backend("hybrid", formula, frame="S4").status == PROVED


def test_hybrid_backend_entailment_with_premises():
    # From ◇i and @i P, ◇P follows (the bridge law's premise form) — PROVED.
    # From just 'i', P does NOT follow (no link between i and P) — REFUTED.
    diamond_i = _MP.parse("◇i")
    at_i_p = _MP.parse("@i P")
    v = run_backend("hybrid", _MP.parse("◇P"), [diamond_i, at_i_p])
    assert v.status == PROVED

    v2 = run_backend("hybrid", P, [_MP.parse("i")])
    assert v2.status == REFUTED


def test_hybrid_backend_unsupported_construct_is_unknown():
    until_formula = _MP.parse("P Ⓤ Q")   # strong Until: not first-order definable
    v = run_backend("hybrid", until_formula)
    assert v.status == UNKNOWN and v.reason == "unsupported"


def test_hybrid_backend_unknown_frame_is_unknown_not_a_crash():
    v = run_backend("hybrid", _MP.parse("@i i"), frame="S99")
    assert v.status == UNKNOWN and v.reason == "unsupported"


# ---------------------------------------------------------------------------
# Registry wiring: default chains, availability, and prove() auto-routing
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("logic,backend_name", [
    ("intuitionistic", "intuitionistic"),
    ("lambek", "lambek"),
    ("ill", "ill"),
    ("relevant", "relevant"),
    ("hybrid", "hybrid"),
])
def test_new_default_chains_are_singletons(logic, backend_name):
    assert default_chain(logic) == (backend_name,)
    assert backend_name in available_backends(logic)
    assert get_backend(backend_name).available()


class TestAutoRoutingNewLogics:
    """logic="auto" must pick up the three logics with an unambiguous
    syntactic marker (lambek/ill/hybrid) without being told, exactly as
    C10's spec requires."""

    def test_lambek_syntax_routes_to_lambek(self):
        A, B = _LAM.parse("A"), _LAM.parse("B")
        v = api.prove(B, [A, Under(A, B)])
        assert v.logic == "lambek" and v.backend == "lambek" and v.status == PROVED

    def test_linear_syntax_routes_to_ill(self):
        A, B = _LIN.parse("A"), _LIN.parse("B")
        v = api.prove(Tensor(B, A), [Tensor(A, B)])
        assert v.logic == "ill" and v.backend == "ill" and v.status == PROVED

    def test_hybrid_syntax_routes_to_hybrid_not_modal(self):
        v = api.prove(_MP.parse("@i i"))
        assert v.logic == "hybrid" and v.backend == "hybrid" and v.status == PROVED


class TestAutoRoutingNeverGuessesIntuitionisticOrRelevant:
    """Intuitionistic and relevant logic reuse the plain classical AST with
    no marker of their own — auto-detection must never guess either
    reading; a bare classical formula keeps routing to "fol"."""

    def test_plain_atom_stays_fol(self):
        v = api.prove(P)
        assert v.logic == "fol"

    def test_classical_tautology_stays_fol(self):
        v = api.prove(Or(P, Not(P)))
        assert v.logic == "fol" and v.status == PROVED

    def test_explicit_logic_still_reaches_the_new_backends(self):
        assert api.prove(P, logic="intuitionistic").backend == "intuitionistic"
        assert api.prove(P, logic="relevant").backend == "relevant"


class TestPreExistingRoutingIsUnchanged:
    """Regression (batch note 4): adding the five new default chains must
    not change which backend answers for a formula that was already routed
    through "fol"/"modal" before this change — pinned against the SAME
    backend name each of these used to resolve to."""

    def test_plain_fol_formula_still_goes_to_z3(self):
        f = _P.parse("∀x (P(x) → Q(x)) ∧ P(a) → Q(a)")
        v = api.prove(f)
        assert v.logic == "fol" and v.backend == "z3" and v.status == PROVED

    def test_fol_entailment_with_premises_unchanged(self):
        premises = [_P.parse("∀x (P(x) → Q(x))"), _P.parse("P(a)")]
        v = api.prove(_P.parse("Q(a)"), premises)
        assert v.logic == "fol" and v.backend == "z3" and v.status == PROVED

    def test_refutable_fol_formula_still_goes_through_the_fol_chain(self):
        v = api.prove(_P.parse("∀x P(x)"))
        assert v.logic == "fol" and v.status == REFUTED
        assert v.backend in default_chain("fol")

    def test_plain_modal_formula_still_goes_to_modal_tableau(self):
        f = _MP.parse("□(P → Q) → (□P → □Q)")
        v = api.prove(f)
        assert v.logic == "modal" and v.backend == "modal-tableau" and v.status == PROVED

    def test_modal_t_axiom_refuted_over_k_still_via_modal_tableau(self):
        f = _MP.parse("□P → P")
        v = api.prove(f)
        assert v.logic == "modal" and v.backend == "modal-tableau" and v.status == REFUTED

    def test_temporal_closure_still_falls_through_to_kripke_enum(self):
        # G/F have no modal-tableau rule (reported unsupported there); the
        # chain moves on to kripke-enum, exactly as before hybrid/lambek/
        # ill/intuitionistic/relevant existed.
        f = _MP.parse("Ⓖ P → P")
        v = api.prove(f)
        assert v.logic == "modal"
        assert v.backend in ("kripke-enum", "qml", "chain")


# ---------------------------------------------------------------------------
# HybridBackend on the ↓ binder, H(@,↓)
# ---------------------------------------------------------------------------

# Each verdict worked out by hand from the ↓ clause (↓x.φ holds at w iff φ
# holds at w with x naming w) and confirmed against a brute-force sweep over
# every frame and valuation with 1..3 worlds (_brute_force_down_countermodel):
# a PROVED formula must have no countermodel there, and each REFUTED one
# below has one of that size.
_DOWN_VALID_K = [
    "↓x.(@x P ↔ P)",                 # @x reads the world ↓ just named.
    "↓x.(P → □↓y.(P → @x P))",       # @x P is fixed across successors.
    "↓x.□(P → ↓y.@x ◇y)",            # every successor y is seen from x.
]
_DOWN_INVALID_K = [
    "↓x.□¬x",    # irreflexivity: a reflexive point refutes it.
    "↓x.◇x",     # reflexivity: a dead end refutes it.
    "↓x.□x",     # a point with a successor other than itself refutes it.
    "↓x.↓x.□x",  # the inner ↓ rebinds x; same countermodel.
]


def _brute_force_down_countermodel(node, max_worlds=3):
    from itertools import product
    from unicode_fol_kit.semantics.kripke import KripkeModel, satisfies_modal
    for n in range(1, max_worlds + 1):
        worlds = list(range(n))
        pairs = [(u, v) for u in worlds for v in worlds]
        for bits in product([0, 1], repeat=len(pairs)):
            rel = {p for p, b in zip(pairs, bits) if b}
            for val in product([0, 1], repeat=n):
                model = KripkeModel(worlds=set(worlds), relations={"alethic": rel},
                                    valuation={w: ({"P"} if val[w] else set()) for w in worlds})
                for w in worlds:
                    if not satisfies_modal(node, model, w):
                        return (n, w)
    return None


@pytest.mark.parametrize("text", _DOWN_VALID_K)
def test_hybrid_backend_proves_valid_down_formulas(text):
    node = MSFLParser(modal=True).parse(text)
    assert _brute_force_down_countermodel(node) is None
    assert get_backend("hybrid").decide(node, frame="K").status == PROVED


@pytest.mark.parametrize("text", _DOWN_INVALID_K)
def test_hybrid_backend_refutes_invalid_down_formulas(text):
    node = MSFLParser(modal=True).parse(text)
    assert _brute_force_down_countermodel(node) is not None
    assert get_backend("hybrid").decide(node, frame="K").status == REFUTED
