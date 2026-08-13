"""Tests for unicode_fol_kit.eval.generality — logical generality analysis.

Every assertion's expected value is worked out BY HAND in the comment next to
it (never copied from a program run) — see each test's docstring/comments for
the derivation. Two tests (``test_undecided_...`` and the Kleene short-circuit
test) deliberately monkeypatch ``unicode_fol_kit.api.prove`` rather than
relying on a real solver call: the point of those two tests is to pin down
THIS module's own tri-state combination logic (:func:`_kleene_and`,
:func:`is_vacuous_specialisation`'s classification), not to find a formula
that happens to make Z3 (or whichever backend the default chain currently
prefers) report "unknown" — that would be flaky across kit/solver versions
and would not actually be testing code this module owns.
"""

import pytest

import unicode_fol_kit.api as api_module
from unicode_fol_kit.atp.protocol import PROVED, REFUTED, UNKNOWN, Verdict
from unicode_fol_kit.eval import generality
from unicode_fol_kit.fol.nodes import Atom, And, Not, Or, Quantifier, Variable
from unicode_fol_kit.fol.signature import PredicateDecl, Signature

X, Y, Z = Variable("x"), Variable("y"), Variable("z")

# ---------------------------------------------------------------------------
# Fixtures — a chemical class definition body, and two hand-derivable
# calibration formulas.
# ---------------------------------------------------------------------------

# The degenerate class definition "molecule <=> net_charge_neutral" — the
# definitional BODY under test is just the right-hand side.
NET_CHARGE_NEUTRAL = Atom("net_charge_neutral", [])

# ∃x∃y∃z (c(x) ∧ c(y) ∧ c(z) ∧ x≠y ∧ x≠z ∧ y≠z) — "there are three pairwise
# distinct carbons".
THREE_DISTINCT_CARBONS = Quantifier(
    "exists", X, Quantifier(
        "exists", Y, Quantifier(
            "exists", Z,
            And(Atom("c", [X]),
                And(Atom("c", [Y]),
                    And(Atom("c", [Z]),
                        And(Atom("≠", [X, Y]),
                            And(Atom("≠", [X, Z]),
                                Atom("≠", [Y, Z]))))))
        )
    )
)

# p ∧ ¬p — a nullary contradiction, unsatisfiable independent of domain size.
CONTRADICTION = And(Atom("p", []), Not(Atom("p", [])))


# ---------------------------------------------------------------------------
# minimal_model_size
# ---------------------------------------------------------------------------

class TestMinimalModelSize:
    def test_net_charge_neutral_has_minimal_size_1(self):
        # By hand: a FiniteStructure's domain is never empty (tarski.Structure
        # raises on an empty domain, and modelfinder.find_model's own search
        # starts at k=1 -- see modelfinder.py), so domain size 1 is the
        # smallest size that is EVER tried at all. At k=1, the interpretation
        # that sets the nullary predicate net_charge_neutral/0 TRUE (its
        # extension = {()}) makes the bare atom net_charge_neutral hold
        # trivially -- no other symbol is even mentioned. So the search
        # succeeds on its very first (smallest possible) domain size.
        result = generality.minimal_model_size(NET_CHARGE_NEUTRAL)
        assert result.size == 1
        assert result.exhausted is False
        assert result.model is not None
        assert len(result.model.domain) == 1

    def test_three_distinct_carbons_has_minimal_size_3(self):
        # By hand:
        #  k=1: only one domain element exists, so x, y, z (however chosen)
        #       must all be assigned that SAME element -- then x≠y evaluates
        #       to False no matter how the predicate c is interpreted. No
        #       interpretation at k=1 can satisfy the formula.
        #  k=2: pigeonhole -- 3 variables, only 2 available domain elements,
        #       so at least two of x, y, z necessarily coincide; the same
        #       ≠-conjunct failure as above. No interpretation at k=2 works.
        #  k=3: assign x, y, z to the three distinct domain elements and
        #       interpret c as the WHOLE domain (all three are carbons) --
        #       every conjunct (c(x), c(y), c(z), x≠y, x≠z, y≠z) is now true,
        #       so the formula holds. This interpretation is one of the
        #       (only 2**3 = 8, trivially enumerated) candidates the finder
        #       tries at k=3, so it is found.
        # Hence the true minimum is exactly 3.
        result = generality.minimal_model_size(THREE_DISTINCT_CARBONS)
        assert result.size == 3
        assert result.exhausted is False
        assert len(result.model.domain) == 3

    def test_unsatisfiable_formula_reports_size_none_and_exhausted(self):
        # By hand: p ∧ ¬p is a plain propositional contradiction over a
        # 0-ary predicate -- its truth does not depend on the domain size at
        # all, only on whether p is interpreted True or False, and NEITHER
        # choice satisfies "p and not p". So no domain size (1, 2, or 3, the
        # bound used here) ever yields a satisfying interpretation.
        # honesty check: this must read as "no small satisfying structure
        # found", not as a claim of unsatisfiability -- exactly what
        # exhausted=True / size=None is documented to mean.
        result = generality.minimal_model_size(CONTRADICTION, max_size=3)
        assert result.size is None
        assert result.exhausted is True
        assert result.model is None
        assert result.max_size_tried == 3

    def test_signature_refuses_undeclared_vocabulary(self):
        # By hand: the signature declares ONLY net_charge_neutral/0, but the
        # formula also uses the unary predicate c/1 -- Signature.validate
        # reports that occurrence as "undeclared predicate 'c' (arity 1)"
        # (see fol/signature.py's documented violation vocabulary), and
        # minimal_model_size must refuse loudly before running any search.
        sig = Signature(predicates={
            "net_charge_neutral": PredicateDecl("net_charge_neutral", 0),
        })
        formula = And(NET_CHARGE_NEUTRAL, Atom("c", [X]))
        with pytest.raises(ValueError, match="undeclared predicate 'c'"):
            generality.minimal_model_size(formula, signature=sig)

    def test_to_dict_is_json_compatible_shape(self):
        result = generality.minimal_model_size(NET_CHARGE_NEUTRAL)
        d = result.to_dict()
        assert d["size"] == 1
        assert d["exhausted"] is False
        assert d["model"]["kind"] == "finite_structure"
        assert isinstance(d["model"]["repr"], str)

        none_result = generality.minimal_model_size(CONTRADICTION, max_size=2)
        assert none_result.to_dict()["model"] is None


# ---------------------------------------------------------------------------
# generality_report
# ---------------------------------------------------------------------------

class TestGeneralityReport:
    def test_reported_only_without_expected_min_size(self):
        # No expectation given -> the module must not invent a threshold; it
        # only reports the fact (size 1, see the derivation above).
        report = generality.generality_report("molecule", NET_CHARGE_NEUTRAL)
        assert report.verdict == generality.REPORTED_ONLY
        assert report.minimal_model.size == 1
        assert report.expected_min_size is None
        # A witness was found, so a readable description must be present.
        assert report.witness_description is not None
        assert "individual" in report.witness_description

    def test_underdetermined_when_size_below_expectation(self):
        # size=1 (hand-derived above) is below an expectation of 5 -> flagged
        # as an INDICATION of under-determination.
        report = generality.generality_report(
            "molecule", NET_CHARGE_NEUTRAL, expected_min_size=5)
        assert report.verdict == generality.UNDERDETERMINED
        assert "INDICATION" in report.narrative
        assert "not a proof" in report.narrative.lower() or "NOT a proof" in report.narrative

    def test_meets_expectation_when_size_at_expectation(self):
        # size=3 (hand-derived above) meets an expectation of exactly 3.
        report = generality.generality_report(
            "threeDistinctCarbons", THREE_DISTINCT_CARBONS, expected_min_size=3)
        assert report.verdict == generality.MEETS_EXPECTATION

    def test_no_small_model_found_for_unsatisfiable_formula(self):
        report = generality.generality_report("contradiction", CONTRADICTION, max_size=3)
        assert report.verdict == generality.NO_SMALL_MODEL_FOUND
        assert report.minimal_model.size is None
        assert report.witness_description is None

    def test_to_dict_round_trips_the_formula(self):
        report = generality.generality_report("molecule", NET_CHARGE_NEUTRAL)
        d = report.to_dict()
        assert d["name"] == "molecule"
        assert d["verdict"] == generality.REPORTED_ONLY
        assert d["formula"] == NET_CHARGE_NEUTRAL.to_dict()


# ---------------------------------------------------------------------------
# is_vacuous_specialisation / strictly_stronger
# ---------------------------------------------------------------------------

class TestVacuousSpecialisation:
    def test_syntactically_different_but_equivalent_is_recognised(self):
        # By hand: A ∧ B and B ∧ A are logically equivalent by commutativity
        # of conjunction -- both directions are classically VALID
        # entailments, so Z3 proves both. syntactically the two ASTs differ
        # (the operands of And are swapped), so this genuinely exercises
        # semantic equivalence checking, not a trivial `==`.
        sub_body = And(Atom("A", []), Atom("B", []))
        sup_body = And(Atom("B", []), Atom("A", []))
        result = generality.is_vacuous_specialisation(sub_body, sup_body)
        assert result.classification == generality.EQUIVALENT
        assert result.detail.forward is True
        assert result.detail.backward is True
        assert result.detail.stronger is False  # equivalent, not STRICTLY stronger

    def test_genuine_specialisation_with_extra_conjunct_is_recognised(self):
        # By hand: sub_body = B ∧ A, sup_body = B.
        #  forward:  (B ∧ A) |= B            -- trivially VALID (weakening).
        #  backward: B |= (B ∧ A)             -- INVALID: the assignment
        #            B=True, A=False satisfies B but not B ∧ A, so Z3 must
        #            refute this direction and hand back that very
        #            countermodel.
        # A and B are two independent nullary atoms (no shared vocabulary
        # forces any relation between them), so this is the cleanest possible
        # "extra conjunct that does not follow" case.
        sup_body = Atom("B", [])
        sub_body = And(Atom("B", []), Atom("A", []))
        result = generality.is_vacuous_specialisation(sub_body, sup_body)
        assert result.classification == generality.STRICTLY_STRONGER
        assert result.detail.forward is True
        assert result.detail.backward is False
        assert result.detail.stronger is True
        assert result.detail.countermodel is not None

    def test_sub_not_entailing_sup_is_not_a_specialisation(self):
        # By hand: sub_body = A, sup_body = B, two unrelated nullary atoms.
        # A does NOT entail B (assignment A=True, B=False is a countermodel),
        # so this is not a specialisation of B at all, regardless of the
        # reverse direction.
        result = generality.is_vacuous_specialisation(Atom("A", []), Atom("B", []))
        assert result.classification == generality.NOT_A_SPECIALISATION
        assert result.detail.forward is False
        assert result.detail.stronger is False

    def test_undecided_case_reports_undecided_not_a_guess(self, monkeypatch):
        # This exercises is_vacuous_specialisation's OWN classification
        # logic for the "the chain could not decide" branch, deterministically
        # -- not any particular solver's actual incompleteness on some
        # formula (which would be flaky across kit/solver versions). Both
        # entailment directions are forced to report UNKNOWN.
        def fake_prove(formula, premises=(), **kwargs):
            return Verdict(UNKNOWN, "test-mock")

        monkeypatch.setattr(api_module, "prove", fake_prove)
        result = generality.is_vacuous_specialisation(Atom("A", []), Atom("B", []))
        assert result.classification == generality.UNDECIDED
        assert result.detail.forward is None
        assert result.detail.backward is None
        assert result.detail.stronger is None


class TestStrictlyStrongerKleeneLogic:
    def test_backward_proved_true_forces_stronger_false_even_if_forward_unknown(self,
                                                                                 monkeypatch):
        # Hand derivation of the three-valued combination
        # stronger = forward AND (NOT backward):
        #   backward is PROVED True  ->  NOT backward = False (definite)
        #   forward  is UNKNOWN      ->  unknown AND False = False regardless
        #                                of what "unknown" would resolve to
        #                                (Kleene strong conjunction: False
        #                                short-circuits even against None).
        # So stronger must be the DEFINITE value False here, not None --
        # reporting None would silently downgrade a proven deduction to
        # "unknown", which this module's docstring explicitly forbids.
        calls = []

        def fake_prove(formula, premises=(), **kwargs):
            calls.append((formula, tuple(premises)))
            if len(calls) == 1:
                return Verdict(UNKNOWN, "test-mock")   # forward: sub|=sup undecided
            return Verdict(PROVED, "test-mock")         # backward: sup|=sub proved

        monkeypatch.setattr(api_module, "prove", fake_prove)
        result = generality.strictly_stronger(Atom("A", []), Atom("B", []))
        assert result.forward is None
        assert result.backward is True
        assert result.stronger is False
        assert len(calls) == 2

    def test_to_dict_shape(self):
        sup_body = Atom("B", [])
        sub_body = And(Atom("B", []), Atom("A", []))
        result = generality.strictly_stronger(sub_body, sup_body)
        d = result.to_dict()
        assert d["stronger"] is True
        assert d["forward"] is True
        assert d["backward"] is False
        assert d["countermodel"] is not None
        assert d["forward_countermodel"] is None


# ---------------------------------------------------------------------------
# all_different — ChemLog's convention as a formula transformation
# ---------------------------------------------------------------------------

class TestAllDifferent:
    """The switch exists because plain semantics cannot see these definitions.

    Under plain FOL semantics a definition built only from ∃, ∧ and ∨ — which
    is what an LLM writes for a chemical class — is satisfied by a ONE-element
    structure interpreting every predicate as universally true. That is not a
    quirk of the finder: it is what the formula says. So the measurement is
    constant 1 and separates nothing, which the first test pins down.
    """

    # ∃x∃y∃z (c(x) ∧ o(y) ∧ n(z)) — three atoms demanded, no ≠ written.
    THREE_ATOMS = Quantifier(
        "exists", X, Quantifier(
            "exists", Y, Quantifier(
                "exists", Z,
                And(Atom("c", [X]), And(Atom("o", [Y]), Atom("n", [Z]))))))

    def test_plain_semantics_reports_1_for_every_positive_definition(self):
        """By hand: domain {d}, x=y=z=d, c/o/n all true of d. One individual
        satisfies a definition 'about' three atoms — and equally satisfies the
        one-atom definition, so the two are indistinguishable this way."""
        one_atom = Quantifier("exists", X, Atom("c", [X]))
        assert generality.minimal_model_size(self.THREE_ATOMS).size == 1
        assert generality.minimal_model_size(one_atom).size == 1

    def test_all_different_recovers_the_number_of_atoms_demanded(self):
        """Under the convention the three variables denote distinct
        individuals, so no structure smaller than 3 can satisfy it — and 3
        does (assign one variable each, let every predicate hold)."""
        result = generality.minimal_model_size(self.THREE_ATOMS, all_different=True)
        assert result.size == 3
        assert result.exhausted is False

    def test_the_closed_form_agrees_with_the_search_it_replaces(self):
        """The fast path is only sound if it answers what the search would.

        Both are computed here for formulas small enough that the search
        actually terminates: the closed form directly, and the search over the
        ≠-augmented formula that carries the same convention.
        """
        from unicode_fol_kit.semantics.modelfinder import find_model

        formulas = [
            Quantifier("exists", X, Atom("c", [X])),                        # 1
            Quantifier("exists", X, Quantifier(                             # 2
                "exists", Y, And(Atom("c", [X]), Atom("o", [Y])))),
            Quantifier("exists", X, Quantifier(                             # 2, ∨
                "exists", Y, Or(Atom("c", [X]), Atom("o", [Y])))),
            self.THREE_ATOMS,                                               # 3
            NET_CHARGE_NEUTRAL,                                             # 1
        ]
        for formula in formulas:
            closed = generality._closed_form_size(formula)
            assert closed is not None, formula
            augmented = generality._with_all_different(formula)
            searched = next(
                (k for k in range(1, 7)
                 if find_model([augmented], max_size=k) is not None), None)
            assert closed == searched, formula

    def test_the_constraints_land_inside_the_binder(self):
        """Regression: conjoining ``x ≠ y`` to the formula as a WHOLE leaves
        both variables free, and the finder reads a free variable as
        universally quantified — 'every individual differs from itself'.
        Every such formula would come back unsatisfiable, and a generality
        report would silently call every definition unsatisfiable."""
        from unicode_fol_kit.semantics.modelfinder import find_model

        augmented = generality._with_all_different(self.THREE_ATOMS)
        assert isinstance(augmented, Quantifier)          # still ∃-led, not And(...)
        assert find_model([augmented], max_size=3) is not None

    def test_both_spellings_of_the_existential_are_recognised(self):
        """``Quantifier`` normalises neither 'exists' nor '∃'; the parsers emit
        one and hand-built ASTs the other. Matching only one would answer an
        all_different question under plain semantics without saying so."""
        unicode_spelling = Quantifier(
            "∃", X, Quantifier("∃", Y, And(Atom("c", [X]), Atom("o", [Y]))))
        ascii_spelling = Quantifier(
            "exists", X, Quantifier("exists", Y, And(Atom("c", [X]), Atom("o", [Y]))))
        assert generality._closed_form_size(unicode_spelling) == 2
        assert generality._closed_form_size(ascii_spelling) == 2

    def test_out_of_fragment_falls_back_to_the_search(self):
        """A negation breaks the closed form's proof (an atom being true no
        longer makes the matrix true), so there is no fast answer — but there
        is still an answer."""
        with_negation = Quantifier("exists", X, And(Atom("c", [X]),
                                                    Not(Atom("o", [X]))))
        assert generality._closed_form_size(with_negation) is None
        assert generality.minimal_model_size(with_negation, all_different=True).size == 1

    def test_an_explicit_inequality_is_out_of_fragment_but_still_answered(self):
        """A definition may write its ≠ atoms out instead of relying on the
        convention. Those are comparisons, so the closed form declines — and
        the search returns the 3 the formula demands."""
        assert generality._closed_form_size(THREE_DISTINCT_CARBONS) is None
        result = generality.minimal_model_size(THREE_DISTINCT_CARBONS,
                                               max_size=4, all_different=True)
        assert result.size == 3

    def test_the_closed_form_returns_a_witness_that_really_satisfies_it(self):
        """A size without a witness is a claim; with one it is a fact."""
        from unicode_fol_kit.semantics.tarski import satisfies

        result = generality.minimal_model_size(self.THREE_ATOMS, all_different=True)
        assert result.model is not None
        assert len(result.model.domain) == 3
        # …and it satisfies the convention too, which is what the ≠-augmented
        # formula says in plain semantics.
        assert satisfies(generality._with_all_different(self.THREE_ATOMS),
                         result.model) is True

    def test_a_formula_without_nested_existentials_is_untouched(self):
        """The convention costs nothing where it says nothing."""
        assert generality._with_all_different(NET_CHARGE_NEUTRAL) == NET_CHARGE_NEUTRAL
        single = Quantifier("exists", X, Atom("c", [X]))
        assert generality._with_all_different(single) == single
