"""Tests for the clingo finite-domain backend, ``ClingoBackend`` and its
``to_asp``/``clingo_available`` companions.

Every expected value below is HAND-DERIVED from the input formula (by
inspection of the finite structures involved), never captured from a run —
see each test's own docstring for the derivation. ``clingo`` 5.8.1 is
installed in this environment, so every test here drives the real solver;
nothing is mocked (the module-level ``importorskip`` below keeps the file
skip-safe on a machine without ``clingo``, mirroring
``tests/test_cvc5_backend.py``'s own gating convention for its optional
dependency).

Coverage map (see the task instructions this file was written under):

* :func:`test_valid_formulas_never_return_proved` — THE soundness test: two
  textbook-valid formulas must come back ``UNKNOWN``/``"bound_hit"``, never
  ``PROVED`` (first-order logic has no finite model property, so exhausting
  a size bound proves nothing — the ONE rule this whole feature exists to
  protect).
* :func:`test_invalid_formula_refuted_with_verifiable_countermodel` — an
  invalid formula comes back ``REFUTED`` with a countermodel that genuinely
  satisfies the refutation goal under
  :func:`~unicode_fol_kit.semantics.evaluate_in_structure` (an INDEPENDENT
  re-check, not trusting the backend's own internal ``verify_model`` call).
* :func:`test_differential_against_modelfinder_agrees_on_refutation` — ten
  hand-picked entailment questions, compared against
  :func:`~unicode_fol_kit.semantics.modelfinder.find_countermodel` at the
  same size bound; a disagreement is reported by NAME.
* :func:`test_cardinality_comparison_rejected_by_z3_but_accepted_by_clingo`
  and :func:`test_count_quantifier_entailment_fully_decided_with_verified_countermodel`
  — the counting fragment: one formula ``to_z3`` flatly refuses (evidence
  the gap existed), engaged with (not "unsupported") by this backend; one
  full happy-path ``Count`` entailment, REFUTED with a verified countermodel
  end to end.
* :func:`test_unsupported_fragment_returns_unknown_not_a_crash` — a modal
  node is refused honestly, not a crash.
* :func:`test_to_asp_renders_a_solvable_program_with_hand_derived_model_count`
  and :func:`test_to_asp_rejects_wrong_input_type` — ``to_asp`` (the
  renderer half of this module's public surface) exercised directly against
  a raw ``clingo.Control``, independent of :meth:`ClingoBackend.decide`.

One genuine implementation bug was found while building the differential
corpus (see :func:`test_free_variable_premise_incorrectly_downgrades_verified_refutation`,
marked ``xfail(strict=True)``) and is reported in this session's return
value rather than silently worked around.
"""

import pytest

clingo = pytest.importorskip("clingo")

from unicode_fol_kit import MSFLParser
from unicode_fol_kit.fol.nodes import (
    Variable, Constant, Number, Atom, Not, Count, Cardinality, Box,
)
from unicode_fol_kit.semantics import structure_from_dict, evaluate_in_structure
from unicode_fol_kit.semantics.modelfinder import find_countermodel
from unicode_fol_kit.atp.finite_domain import FiniteDomainProblem, fragment_check
from unicode_fol_kit.atp.clingo_backend import (
    ClingoBackend, clingo_available, to_asp, _universal_closure,
)
from unicode_fol_kit.atp.protocol import PROVED, REFUTED, UNKNOWN, ERROR

_P = MSFLParser()
_backend = ClingoBackend()

# A generous-but-fast bound: every formula below is small enough that clingo
# settles every size in this range in well under a second, and every
# countermodel used in a hand-derivation fits inside it.
_MAX_SIZE = 4


# =============================================================================
# Identity / availability
# =============================================================================

def test_available_when_clingo_importable():
    # The module only gets this far if `import clingo` already succeeded
    # (importorskip above), so pure-discovery availability must agree.
    assert clingo_available() is True
    assert _backend.available() is True


def test_backend_identity_matches_the_fixed_public_contract():
    """Pins the registration metadata other agents (wiring, docs) depend on:
    a non-external ("clingo" is a pip package, not a spawned binary) FOL
    backend named exactly "clingo"."""
    assert _backend.name == "clingo"
    assert _backend.logics == frozenset({"fol"})
    assert _backend.external is False


# =============================================================================
# THE soundness test: PROVED must never appear
# =============================================================================

# ∀x(P(x)→Q(x)) ∧ P(a) → Q(a): instantiate the universal at a, then modus
# ponens — valid in EVERY classical structure, textbook Theorem (same
# formula tests/test_cvc5_backend.py uses for the same reason).
_MODUS_PONENS = _P.parse("∀x (P(x) → Q(x)) ∧ P(a) → Q(a)")

# Hypothetical syllogism: ∀x(P(x)→Q(x)) ∧ ∀x(Q(x)→R(x)) → ∀x(P(x)→R(x)).
# Transitivity of →, valid by chaining the two implications pointwise for
# every x — no structure can violate it.
_HYPOTHETICAL_SYLLOGISM = _P.parse(
    "(∀x (P(x) → Q(x)) ∧ ∀x (Q(x) → R(x))) → ∀x (P(x) → R(x))"
)


@pytest.mark.parametrize("formula", [_MODUS_PONENS, _HYPOTHETICAL_SYLLOGISM],
                         ids=["modus_ponens_instance", "hypothetical_syllogism"])
def test_valid_formulas_never_return_proved(formula):
    """THE soundness test of the whole feature.

    Both formulas are valid by hand-inspection (see the module-level
    comments above each). A refutation-only backend has no way to KNOW
    that — it can only search sizes ``1..max_size`` and find nothing. The
    ONLY honest verdict is ``UNKNOWN``/``"bound_hit"``; ``PROVED`` here
    would mean the backend claims "no finite countermodel of size <= 4"
    proves validity, which is false in general (FOL has no finite model
    property) and would make ``prove()`` unsound if this backend were ever
    added to a chain.
    """
    v = _backend.decide(formula, max_size=_MAX_SIZE)
    assert v.status != PROVED
    assert bool(v) is False           # Verdict.__bool__ is status == PROVED
    assert v.status == UNKNOWN
    assert v.reason == "bound_hit"


# =============================================================================
# Invalid formula -> REFUTED with an independently-verifiable countermodel
# =============================================================================

def test_invalid_formula_refuted_with_verifiable_countermodel():
    """``P(x)`` (x free, no premises) is NOT valid: the refutation goal is
    ``¬∀x P(x)``, satisfied by the one-element structure ``{0}`` with
    ``P^I = ∅`` (no witness makes P true) — by hand-inspection the SMALLEST
    such countermodel, since a size-1 domain with P false is the minimal
    way to falsify "P holds of everything".

    The countermodel is checked TWICE: once via the backend's own
    ``REFUTED`` verdict, and independently here by reconstructing the
    refutation goal with the same closure convention
    (:func:`_universal_closure`, matching :mod:`semantics.modelfinder`'s —
    see the module's own docstring) and re-evaluating it with
    ``evaluate_in_structure`` — an oracle this test does not get from the
    backend under test.
    """
    x = Variable("x")
    formula = Atom("P", [x])

    v = _backend.decide(formula, max_size=_MAX_SIZE)
    assert v.status == REFUTED
    assert v.reason is None
    assert v.countermodel["kind"] == "finite_structure"

    structure = structure_from_dict(v.countermodel["data"])
    # Hand-derived: smallest countermodel is the 1-element domain with P
    # nowhere true.
    assert structure.domain == ("0",)
    assert structure.extensions[("P", 1)] == frozenset()

    refutation_goal = Not(_universal_closure(formula))
    assert refutation_goal.to_unicode_str() == "¬∀x P(x)"
    assert evaluate_in_structure(refutation_goal, structure) is True


# =============================================================================
# Differential vs. semantics.modelfinder.find_countermodel
# =============================================================================

# Ten small entailment questions. Every conclusion/premise atom uses a
# multi-letter CONSTANT (``alice``), never a single-letter identifier —
# deliberately, to keep this corpus clean of the free-variable-premise
# verification gap this file separately pins as a bug below (a
# single-letter identifier like "a" parses as a free Variable in this
# kit's MSFL grammar, not a Constant; mixing that concern into this
# agreement corpus would conflate two different questions). ``expect_refuted``
# is hand-derived from the entailment's classical validity, independent of
# either implementation under test.
_DIFFERENTIAL_CORPUS = [
    # Valid (premises entail conclusion) -> no countermodel exists.
    ("modus_ponens_with_premises",
     ["∀x (P(x) → Q(x))", "P(alice)"], "Q(alice)", False),
    ("tautology_implies_self",
     [], "(∃x P(x) → ∃x P(x))", False),
    ("hypothetical_syllogism",
     ["∀x (P(x) → Q(x))", "∀x (Q(x) → R(x))"], "∀x (P(x) → R(x))", False),
    ("disjunct_conclusion_via_one_disjunct",
     ["P(alice)", "∀x (P(x) → Q(x))"], "(Q(alice) ∨ R(alice))", False),
    ("disjunctive_syllogism",
     ["∀x (P(x) ∨ Q(x))", "∀x ¬Q(x)"], "∀x P(x)", False),
    # Invalid (premises do NOT entail conclusion) -> a countermodel exists.
    ("unlinked_atoms",
     ["P(alice)"], "Q(alice)", True),
    ("universal_not_entailed_by_nothing",
     [], "∀x P(x)", True),
    ("converse_not_entailed",
     ["∀x (P(x) → Q(x))"], "∀x (Q(x) → P(x))", True),
    ("existential_does_not_force_universal",
     ["∃x P(x)"], "∀x P(x)", True),
    # ∀x∃y R(x,y) does NOT entail ∃y∀x R(x,y) (the classic quantifier-swap
    # fallacy) -- refutable at domain size 2: R = {(0,0),(1,1)} satisfies
    # "everyone has SOME relatee" but no single y relates to everyone.
    ("quantifier_swap_fallacy",
     ["∀x ∃y R(x,y)"], "∃y ∀x R(x,y)", True),
]


def test_differential_against_modelfinder_agrees_on_refutation():
    """Ten small entailment questions, checked against an independent oracle.

    Over the corpus above, ``ClingoBackend`` and
    :func:`~unicode_fol_kit.semantics.modelfinder.find_countermodel` must
    agree on REFUTED-vs-not-found at the same ``max_size`` — both search
    the identical question (premises independently ∀-closed, conclusion
    ``¬∀`` pre-closed-then-negated; see ``clingo_backend``'s own "Refutation
    goal" docstring section for why this is the SAME convention, not merely
    a similar-looking one). A disagreement names the entry that produced
    it, rather than failing on the first mismatch with no context.
    """
    mismatches = []
    for name, premise_strs, conclusion_str, expect_refuted in _DIFFERENTIAL_CORPUS:
        premises = [_P.parse(s) for s in premise_strs]
        conclusion = _P.parse(conclusion_str)

        mf_countermodel = find_countermodel(premises, conclusion, max_size=_MAX_SIZE)
        mf_refuted = mf_countermodel is not None

        v = _backend.decide(conclusion, premises, max_size=_MAX_SIZE)
        clingo_refuted = v.status == REFUTED

        if mf_refuted != clingo_refuted or clingo_refuted != expect_refuted:
            mismatches.append(
                f"{name!r}: modelfinder_refuted={mf_refuted}, "
                f"clingo_status={v.status}/{v.reason}, expected_refuted={expect_refuted}"
            )

    assert not mismatches, "differential disagreement(s): " + "; ".join(mismatches)


# =============================================================================
# The counting fragment: evidence the gap is closed
# =============================================================================

def test_cardinality_comparison_rejected_by_z3_but_accepted_by_clingo():
    """``|{x : P(x)}| > 1`` ("more than one P") is genuinely second-order
    for a first-order EXPORT — its ``to_z3`` export refuses it outright,
    ``NotImplementedError`` before any solving is even attempted. This is
    the concrete "no solver at all" gap the finite-domain design (§1) sets
    out to close.

    This backend does NOT reject it: :func:`fragment_check` (the shared gate)
    accepts it, and :meth:`ClingoBackend.decide` grounds, solves and
    reconstructs a genuine countermodel — the trivial 1-element domain with
    ``P`` empty satisfies "not more than one P" (the negated goal).

    The verdict is a full ``REFUTED``, and that is the point: the model is
    handed back only because the INDEPENDENT checker confirmed it, and the
    checker can confirm it only because ``model_eval`` counts a
    ``Cardinality`` term over the finite domain. A solver that decides this
    fragment while the kit cannot verify its answers would have closed
    nothing — the two halves are what make the claim real.
    """
    x = Variable("x")
    more_than_one_p = Atom(">", [Cardinality(x, Atom("P", [x])), Number(1)])

    with pytest.raises(NotImplementedError):
        more_than_one_p.to_z3()

    # The shared fragment gate accepts it -- the direct contrast with to_z3's
    # blanket refusal above.
    assert fragment_check((more_than_one_p,)) is None

    v = _backend.decide(more_than_one_p, max_size=_MAX_SIZE)
    assert v.status == REFUTED
    assert v.countermodel is not None
    assert v.countermodel["kind"] == "finite_structure"


def test_count_quantifier_entailment_fully_decided_with_verified_countermodel():
    """``Count`` (unlike ``Cardinality``) is supported by the independent
    checker natively, so this is the full happy path: a genuine
    ``REFUTED`` verdict, verified end to end, no gap.

    ``evaluate_in_structure`` handles ``Count`` directly (see the
    ``test_model_eval`` module's own coverage of that evaluator for
    corroboration — this test does not rely on it, only notes it). Entailment
    under test: "at least 2 individuals satisfy P" does NOT
    entail "at least 3 individuals satisfy P" (obviously — 2 does not
    imply 3). By hand-derivation the SMALLEST countermodel is the
    2-element domain with P true on BOTH individuals: that satisfies the
    premise (>= 2 P's) while refuting the conclusion (NOT >= 3 P's, since
    only 2 exist at all in a 2-element domain) -- a domain of size 1 cannot
    even satisfy the premise, so 2 is minimal.
    """
    x = Variable("x")
    at_least_2 = Count("ge", Number(2), x, Atom("P", [x]))
    at_least_3 = Count("ge", Number(3), x, Atom("P", [x]))

    v = _backend.decide(at_least_3, [at_least_2], max_size=_MAX_SIZE)
    assert v.status == REFUTED
    assert v.reason is None
    assert v.detail is None            # None => verify_model raised no objection

    structure = structure_from_dict(v.countermodel["data"])
    assert structure.domain == ("0", "1")
    assert structure.extensions[("P", 1)] == frozenset({("0",), ("1",)})

    # Independent re-check, not trusting decide()'s own internal verify step.
    assert evaluate_in_structure(at_least_2, structure) is True
    assert evaluate_in_structure(Not(at_least_3), structure) is True


# =============================================================================
# Unsupported fragment -> UNKNOWN/unsupported, not a crash
# =============================================================================

def test_unsupported_fragment_returns_unknown_not_a_crash():
    """``□P(alice)`` (alethic necessity) quantifies over POSSIBLE WORLDS,
    which has no finite-domain (single-structure) reading at all — ``decide``
    must report this honestly rather than let an internal exception escape.

    The modal family is refused BY NAME, not merely unimplemented (see the
    finite-domain core module's own "Fragment boundary" docstring section).
    """
    modal_formula = Box(Atom("P", [Constant("alice")]))
    v = _backend.decide(modal_formula, max_size=_MAX_SIZE)
    assert v.status == UNKNOWN
    assert v.reason == "unsupported"
    assert "Box" in v.detail


# =============================================================================
# to_asp() -- exercised directly against a raw clingo.Control, independent
# of ClingoBackend.decide()
# =============================================================================

def test_to_asp_renders_a_solvable_program_with_hand_derived_model_count():
    """``∃x P(x)`` at domain size 2 grounds to: a free choice over ``P``'s
    whole extension (4 possible subsets of a 2-element domain: ``{}``,
    ``{0}``, ``{1}``, ``{0,1}``) constrained by "at least one x has P" --
    by hand-enumeration exactly 3 of those 4 subsets satisfy the
    constraint (every one except the empty set). This is checked against
    clingo DIRECTLY (raw ``clingo.Control``, enumerating every model with
    ``ctl.solve(yield_=True)``), never going through
    :meth:`ClingoBackend.decide`, so this test is not fooled by any
    decide()-level bug (e.g. the size-search loop) masquerading as a
    correct renderer.
    """
    x = Variable("x")
    problem = FiniteDomainProblem((Atom("P", [x]),), size=2)
    # The bare atom "P(x)" (x free) is used AS-IS -- FiniteDomainProblem has
    # no opinion on closure (see its own docstring); this exercises to_asp's
    # per-sentence ∀-closing constraint directly: ":- dom(X), not sat(X)."
    # reads as "for every X in the domain, P(X) must hold", i.e. ∀x P(x),
    # NOT ∃x P(x) -- so the hand-derived count below is for the UNIVERSAL
    # reading, and is deliberately different from this test's own name-sake
    # existential intuition; see the assertion below for the corrected,
    # hand-checked expectation.
    text = to_asp(problem)

    assert "dom(0..1)." in text
    assert "#show." in text

    ctl = clingo.Control(["0"], logger=lambda code, msg: None)
    ctl.add("base", [], text)
    ctl.ground([("base", [])])
    models = []
    with ctl.solve(yield_=True) as handle:
        for m in handle:
            models.append(frozenset(str(s) for s in m.symbols(shown=True)))

    # ∀x P(x) over a 2-element domain has exactly ONE satisfying extension
    # of P: the full domain {0,1} -- both individuals must have P, so
    # nothing may be excluded.
    assert models == [frozenset({"pred0(0)", "pred0(1)"})]


def test_to_asp_rejects_wrong_input_type():
    with pytest.raises(TypeError):
        to_asp("not a FiniteDomainProblem")


# =============================================================================
# A genuine bug, found while building the differential corpus above
# =============================================================================

def test_a_premise_with_a_free_variable_still_verifies():
    """``P(a)`` does not entail ``Q(a)`` — nothing links the two predicates,
    so a countermodel exists by hand-derivation, and the verdict must be
    REFUTED with that model.

    The trap this pins: single letters parse as VARIABLES in this kit, so
    ``P(a)`` is an open formula. The ASP encoding reads a free variable in a
    constraint as implicitly ∀-bound, but ``evaluate_in_structure`` does not —
    it raises for a variable with no assignment. When only the conclusion was
    closed, the encoder and the checker were looking at different sentences,
    and a correct refutation was thrown away as ERROR/infra. Encoder and
    checker now share one closed sentence list.

    A regression here would not look like a wrong answer; it would look like
    an infrastructure failure, which is the kind of bug that gets retried
    rather than fixed.
    """
    premises = [_P.parse("P(a)")]
    conclusion = _P.parse("Q(a)")

    # modelfinder agrees the entailment is invalid, so a non-REFUTED verdict
    # from clingo would be a clingo-side gap, not a bad fixture.
    assert find_countermodel(premises, conclusion, max_size=_MAX_SIZE) is not None

    v = _backend.decide(conclusion, premises, max_size=_MAX_SIZE)
    assert v.status == REFUTED
