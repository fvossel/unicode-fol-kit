"""Tests for the uniform prover protocol (atp/protocol.py).

The semantic contracts under test, each hand-checked:

* every route answers through the SAME Verdict type with correct status
  semantics — in particular the sound-but-bounded routes (resolution, qml,
  modelfinder) must NEVER report REFUTED/PROVED beyond what they actually
  established;
* the status/reason split keeps budget exhaustion (bound_hit) distinguishable
  from honest incompleteness and from timeouts;
* the availability contract: unknown name → ValueError, known-but-missing
  backend → BackendUnavailable, never a silent skip;
* an in-backend crash becomes an ERROR verdict, not a batch-killing exception.
"""

import json

import pytest

from unicode_fol_kit import (
    MSFLParser,
    Verdict, BackendUnavailable, ProverBackend,
    register_backend, get_backend, available_backends, default_chain,
    run_backend,
)
from unicode_fol_kit.atp.protocol import (
    PROVED, REFUTED, UNKNOWN, ERROR, Z3Backend, z3_relevant_premises,
)

_P = MSFLParser()
_MP = MSFLParser(modal=True)

_VALID = _P.parse("∀x (P(x) → Q(x)) ∧ P(a) → Q(a)")     # modus ponens, valid
_INVALID = _P.parse("∀x P(x)")                           # refutable
_ENTAILMENT = (_P.parse("∀x (P(x) → Q(x))"), _P.parse("P(a)"))  # premises for Q(a)


# ---------------------------------------------------------------------------
# Verdict semantics
# ---------------------------------------------------------------------------

def test_verdict_truthiness_and_szs_derivation():
    assert bool(Verdict("proved", "z3")) is True
    assert bool(Verdict("refuted", "z3")) is False
    assert Verdict("proved", "z3").szs_status == "Theorem"
    assert Verdict("refuted", "z3").szs_status == "CounterSatisfiable"
    assert Verdict("unknown", "z3", reason="bound_hit").szs_status == "ResourceOut"
    assert Verdict("unknown", "z3", reason="timeout").szs_status == "Timeout"
    assert Verdict("unknown", "z3", reason="incomplete").szs_status == "GaveUp"
    assert Verdict("unknown", "z3", reason="unsupported").szs_status == "Inappropriate"
    assert Verdict("error", "z3", reason="infra").szs_status == "Error"


def test_verdict_rejects_unknown_status():
    with pytest.raises(ValueError, match="unknown status"):
        Verdict("maybe", "z3")


def test_verdict_to_dict_is_json_compatible():
    v = run_backend("z3", _INVALID)
    d = v.to_dict()
    json.dumps(d)
    assert d["status"] == "refuted" and d["agreement"] == ["z3"]


# ---------------------------------------------------------------------------
# Internal backends, route by route
# ---------------------------------------------------------------------------

def test_z3_proves_refutes_and_witnesses():
    assert run_backend("z3", _VALID).status == PROVED
    v = run_backend("z3", _INVALID)
    assert v.status == REFUTED
    assert v.countermodel["kind"] == "z3_model"


def test_z3_entailment_with_premises():
    premises = list(_ENTAILMENT)
    conclusion = _P.parse("Q(a)")
    assert run_backend("z3", conclusion, premises).status == PROVED


def test_tableau_proves_and_reports_bound_honestly():
    assert run_backend("tableau", _VALID).status == PROVED
    v = run_backend("tableau", _INVALID)
    assert v.status == UNKNOWN and v.reason == "bound_hit"   # never REFUTED


def test_resolution_proves_and_never_claims_refutation():
    assert run_backend("resolution", _VALID).status == PROVED
    v = run_backend("resolution", _INVALID)
    assert v.status == UNKNOWN and v.reason == "bound_hit"


def test_modelfinder_refutes_with_structure_and_never_proves():
    v = run_backend("modelfinder", _INVALID)
    assert v.status == REFUTED
    assert v.countermodel["kind"] == "finite_structure"
    v2 = run_backend("modelfinder", _VALID)
    assert v2.status == UNKNOWN and v2.reason == "bound_hit"  # cannot prove validity


def test_modal_tableau_tristate_and_frame_option():
    t_axiom = _MP.parse("□P → P")
    assert run_backend("modal-tableau", t_axiom).status == REFUTED       # K
    assert run_backend("modal-tableau", t_axiom, frame="T").status == PROVED
    v = run_backend("modal-tableau", t_axiom)
    assert v.logic == "modal" and v.countermodel["kind"] == "kripke"


def test_qml_proves_but_reports_incomplete_not_refuted():
    barcan_free = _MP.parse("□(P ∧ Q) → □P")
    assert run_backend("qml", barcan_free).status == PROVED
    v = run_backend("qml", _MP.parse("□P → P"))                          # K: not valid
    assert v.status == UNKNOWN and v.reason == "incomplete"              # sound, incomplete


def test_temporal_closure_operator_is_reported_unsupported_by_modal_tableau():
    """G/F/U have no tableau rule — the verdict must say so, not guess."""
    always = _MP.parse("Ⓖ P → P")
    v = run_backend("modal-tableau", always)
    assert v.status == UNKNOWN and v.reason == "unsupported"


# ---------------------------------------------------------------------------
# Registry and availability contract
# ---------------------------------------------------------------------------

def test_unknown_backend_name_raises_value_error():
    with pytest.raises(ValueError, match="unknown backend"):
        run_backend("nope", _VALID)


def test_default_chains_cover_their_logics():
    import importlib.util
    if importlib.util.find_spec("cvc5") is not None:
        # The one documented availability-dependent member: the optional
        # cvc5 extra joins right after z3 (see default_chain's docstring).
        assert default_chain("fol") == ("z3", "cvc5", "tableau",
                                        "resolution", "modelfinder")
    else:
        assert default_chain("fol") == ("z3", "tableau", "resolution",
                                        "modelfinder")
    assert default_chain("modal") == ("modal-tableau", "kripke-enum", "qml")
    # C10: five singleton chains, one per substructural/non-classical logic —
    # see logic_backends' module docstring for why each is a lone entry
    # rather than a multi-backend race.
    assert default_chain("intuitionistic") == ("intuitionistic",)
    assert default_chain("lambek") == ("lambek",)
    assert default_chain("ill") == ("ill",)
    assert default_chain("relevant") == ("relevant",)
    assert default_chain("hybrid") == ("hybrid",)
    with pytest.raises(ValueError):
        default_chain("astrology")


def test_internal_backends_are_always_available():
    all_chains = (default_chain("fol") + default_chain("modal")
                 + default_chain("intuitionistic") + default_chain("lambek")
                 + default_chain("ill") + default_chain("relevant")
                 + default_chain("hybrid"))
    for name in all_chains:
        assert get_backend(name).available()
        assert name in available_backends()


def test_unavailable_backend_raises_backend_unavailable():
    """A registered backend whose discovery fails must raise, not skip."""
    class NeverThere(ProverBackend):
        name = "never-there"
        logics = frozenset({"fol"})
        external = True

        def available(self):
            return False

        def decide(self, formula, premises=(), timeout=10000, **options):
            raise AssertionError("decide must not be reached")

    register_backend(NeverThere())
    try:
        with pytest.raises(BackendUnavailable, match="never-there"):
            run_backend("never-there", _VALID)
    finally:
        from unicode_fol_kit.atp.protocol import _REGISTRY
        del _REGISTRY["never-there"]


def test_backend_crash_becomes_error_verdict():
    """An unexpected in-backend exception is recorded, not propagated."""
    class Crashy(ProverBackend):
        name = "crashy"
        logics = frozenset({"fol"})

        def available(self):
            return True

        def decide(self, formula, premises=(), timeout=10000, **options):
            raise RuntimeError("boom")

    register_backend(Crashy())
    try:
        v = run_backend("crashy", _VALID)
        assert v.status == ERROR and v.reason == "infra" and "boom" in v.detail
    finally:
        from unicode_fol_kit.atp.protocol import _REGISTRY
        del _REGISTRY["crashy"]


# ---------------------------------------------------------------------------
# C12: Z3Backend's per-Solver assert_and_track unsat-core certificate
# ---------------------------------------------------------------------------
#
# Z3Backend.decide now tracks each premise (tag "p<i>") and the negated goal
# (tag "goal") individually instead of asserting one flat implication, so a
# PROVED verdict carries Verdict.proof = {"kind": "z3_unsat_core", "core":
# [...]} — an unsat CORE (sound, not necessarily minimal; see
# z3_relevant_premises's docstring for the same caveat).

_z3 = Z3Backend()


def test_z3_proved_verdict_carries_an_unsat_core_proof():
    v = run_backend("z3", _VALID)
    assert v.status == PROVED
    assert v.proof["kind"] == "z3_unsat_core"
    # _VALID has no premises, so the only thing that CAN be tracked is the
    # negated goal itself.
    assert v.proof["core"] == ["goal"]


def test_z3_refuted_and_unknown_verdicts_carry_no_proof():
    assert run_backend("z3", _INVALID).proof is None                 # REFUTED
    timed_out = run_backend("z3", _VALID, timeout=0)
    # timeout=0 means "no budget" to Z3 -- must not raise, must not fabricate
    # a proof either way.
    assert timed_out.proof is None or timed_out.status == PROVED


def test_z3_refuted_countermodel_never_leaks_the_tracking_tags():
    """Regression: assert_and_track's own "goal"/"p<i>" tracking booleans are
    themselves 0-ary Bool-sorted Z3 declarations, so a naive
    `{d.name(): model[d] for d in model.decls()}` would leak them into the
    countermodel witness as spurious extra keys indistinguishable from a
    real symbol. _z3_model_assignment must filter them out by declaration
    shape (name AND Bool-sort AND arity 0), never by hoping premises/formula
    happen not to use those names."""
    v = run_backend("z3", _INVALID)
    assert v.status == REFUTED
    assert set(v.countermodel["assignment"]) == {"P"}

    premises = [_P.parse("P(a)")]
    v2 = run_backend("z3", _P.parse("Q(a)"), premises)
    assert v2.status == REFUTED
    assert "goal" not in v2.countermodel["assignment"]
    assert "p0" not in v2.countermodel["assignment"]

    # Pathological but must not corrupt: a genuine kit-level CONSTANT named
    # "goal" is lowercase-initial (legal per fol._identifiers) and therefore
    # never Bool-sorted (constants live in the uninterpreted sort S, not
    # Bool -- see Z3Env.get_symbol), so it is NEVER the same Z3 declaration
    # shape as the tracking tag and must survive in the witness untouched.
    weird_goal = _P.parse("Q(goal)")
    v3 = run_backend("z3", weird_goal, [_P.parse("P(goal)")])
    assert v3.status == REFUTED
    assert "goal" in v3.countermodel["assignment"]           # the CONSTANT
    assert v3.countermodel["assignment"]["goal"] != "True"   # not the tag's bool value


class TestZ3RelevantPremises:
    """C11's Z3-native leg: which premises did Z3 actually need?

    Every expected value below was independently verified with a direct
    ``z3.Solver().assert_and_track``/``unsat_core()`` experiment before being
    pinned here (not derived from reading z3_relevant_premises's own code) --
    see the function's docstring for the "sound, not necessarily minimal"
    caveat these numbers respect.
    """

    def test_red_herring_premise_is_excluded(self):
        # ∀x(Human(x)→Mortal(x)) and Human(socrates) are the textbook modus-
        # ponens derivation of Mortal(socrates); Bird(tweety) shares no
        # symbol with the rest of the problem, so no sound unsat core can
        # ever need it.
        premises = [_P.parse("∀x (Human(x) → Mortal(x))"),
                   _P.parse("Human(socrates)"),
                   _P.parse("Bird(tweety)")]
        goal = _P.parse("Mortal(socrates)")
        assert z3_relevant_premises(goal, premises) == (0, 1)

    def test_syntactically_similar_but_irrelevant_premise_is_excluded(self):
        # A THIRD premise sharing the Human(x) antecedent (∀x(Human(x)→Wise(x)))
        # is syntactically close to the premise that IS needed but proves
        # nothing about Mortal(socrates) -- a harder distractor than a
        # disjoint-vocabulary red herring, stressing that exclusion is by
        # actual logical necessity, not by "shares no symbols".
        premises = [_P.parse("∀x (Human(x) → Mortal(x))"),
                   _P.parse("Human(socrates)"),
                   _P.parse("∀x (Human(x) → Wise(x))")]
        goal = _P.parse("Mortal(socrates)")
        assert z3_relevant_premises(goal, premises) == (0, 1)

    def test_redundant_premise_never_forces_both(self):
        # Mortal(socrates) alone already contradicts the negated goal; the
        # second premise (a strictly STRONGER, independently sufficient
        # restatement) is never required alongside it.
        premises = [_P.parse("Mortal(socrates)"),
                   _P.parse("Mortal(socrates) ∧ Human(socrates)")]
        goal = _P.parse("Mortal(socrates)")
        indices = z3_relevant_premises(goal, premises)
        assert indices == (0,)   # never both -- see the docstring's caveat

    def test_no_premises_needed_is_the_empty_tuple(self):
        assert z3_relevant_premises(_VALID, []) == ()

    def test_not_entailed_is_none_not_an_empty_or_full_set(self):
        # P(a) alone does not entail Q(a) -- there is no "premises used"
        # answer for a non-theorem.
        assert z3_relevant_premises(_P.parse("Q(a)"), [_P.parse("P(a)")]) is None

    def test_unsupported_fragment_is_none(self):
        linear = MSFLParser(linear=True).parse("A ⊗ B")
        assert z3_relevant_premises(linear, []) is None

    def test_soundness_self_check_reproving_just_the_reported_subset(self):
        """The independent second route the spec's test_oracle names: take
        the reported subset, re-run Z3 (fresh, unrelated call) on ONLY those
        premises plus the conclusion, and require it still PROVED -- catches
        an unsound over-pruning bug regardless of which extraction path
        produced the subset."""
        premises = [_P.parse("∀x (Human(x) → Mortal(x))"),
                   _P.parse("Human(socrates)"),
                   _P.parse("Bird(tweety)")]
        goal = _P.parse("Mortal(socrates)")
        indices = z3_relevant_premises(goal, premises)
        subset = [premises[i] for i in indices]
        assert _z3.decide(goal, subset).status == PROVED


def test_z3_backend_proof_core_agrees_with_z3_relevant_premises():
    """The premise-only side of Z3Backend's own proof["core"] (its "p<i>"
    tags, stripped of the always-present "goal" tag) must name exactly the
    same premises z3_relevant_premises reports for the identical query --
    both read the exact same _z3_track_and_check call shape (see that
    function's docstring), so they must never drift apart."""
    premises = [_P.parse("∀x (Human(x) → Mortal(x))"),
               _P.parse("Human(socrates)"),
               _P.parse("Bird(tweety)")]
    goal = _P.parse("Mortal(socrates)")
    v = _z3.decide(goal, premises)
    assert v.status == PROVED
    core_indices = tuple(sorted(
        int(tag[1:]) for tag in v.proof["core"] if tag != "goal"))
    assert core_indices == z3_relevant_premises(goal, premises) == (0, 1)
