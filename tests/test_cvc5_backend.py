"""Tests for the cvc5 backend (atp/cvc5_backend.py).

Hand-checked contracts, each justified inline:

* PROVED / REFUTED are exactly as trustworthy as Z3Backend's — a modus-ponens
  instance is a textbook valid formula (Theorem), ``∀x P(x)`` is refutable by
  the one-element structure where ``P`` holds nowhere (a genuine
  countermodel, not a guess);
* an entailment with premises folds to the same ``(∧ premises) → φ`` shape
  Z3Backend uses, so a premise set that classically forces ``Q(a)`` must come
  back PROVED;
* linear-logic connectives have NO classical ``to_z3`` export by design (see
  ``fol/_linear_nodes.py``'s ``_NO_LINEAR_EXPORT``) — the backend must report
  that honestly as UNKNOWN/"unsupported", not silently drop to some other
  answer;
* every Verdict carries backend="cvc5", a derived szs_status, and a positive
  wall_time (the backend actually ran cvc5, it did not short-circuit).

Skipped entirely (module-level ``importorskip``) on a machine without the
``cvc5`` package installed — ``available()``/``decide()`` handle that
gracefully at runtime, but exercising PROVED/REFUTED/etc. genuinely needs a
working cvc5 binding.
"""

import pytest

cvc5 = pytest.importorskip("cvc5")

from unicode_fol_kit import MSFLParser
from unicode_fol_kit.atp.cvc5_backend import Cvc5Backend
from unicode_fol_kit.atp.protocol import PROVED, REFUTED, UNKNOWN, ERROR

_P = MSFLParser()
_LIN = MSFLParser(linear=True)

# Modus-ponens instance: ∀x(P(x)→Q(x)) ∧ P(a) → Q(a) is valid in every
# classical structure (instantiate the universal at a, then modus ponens) —
# a textbook Theorem, independent of any prover's search strategy.
_VALID = _P.parse("∀x (P(x) → Q(x)) ∧ P(a) → Q(a)")

# ∀x P(x) is refutable: the one-element structure {e} with P^I = ∅ satisfies
# ¬∀x P(x) (there is no witness making P true), so this is CounterSatisfiable,
# not a Theorem.
_INVALID = _P.parse("∀x P(x)")

_backend = Cvc5Backend()


def test_available_when_cvc5_importable():
    # The test module only gets this far if `import cvc5` already succeeded
    # (importorskip above), so pure-discovery availability must agree.
    assert _backend.available() is True


def test_proved_modus_ponens_instance():
    v = _backend.decide(_VALID)
    assert v.status == PROVED
    assert v.backend == "cvc5"
    assert v.szs_status == "Theorem"
    assert v.wall_time > 0


def test_refuted_universal_with_model_witness():
    v = _backend.decide(_INVALID)
    assert v.status == REFUTED
    assert v.szs_status == "CounterSatisfiable"
    assert v.countermodel["kind"] == "cvc5_model"
    # The negated goal ∃x ¬P(x) declares exactly one uninterpreted symbol
    # (the predicate P — x is existentially bound, not a free declaration),
    # so the witness assignment must name it; cvc5 must interpret P as false
    # somewhere (a constant-true P would satisfy the original ∀x P(x) and
    # this formula would not be refutable at all).
    assignment = v.countermodel["assignment"]
    assert "P" in assignment
    assert "false" in assignment["P"].lower()


def test_entailment_with_premises_forces_conclusion():
    # ∀x(P(x)→Q(x)) and P(a) classically entail Q(a) (universal instantiation
    # at a, then modus ponens) — the same textbook derivation as _VALID, just
    # split across the premises argument instead of folded into one formula.
    premises = [_P.parse("∀x (P(x) → Q(x))"), _P.parse("P(a)")]
    conclusion = _P.parse("Q(a)")
    v = _backend.decide(conclusion, premises)
    assert v.status == PROVED
    assert v.agreement == ("cvc5",)


def test_entailment_with_premises_that_do_not_force_conclusion_is_refuted():
    # P(a) alone does NOT entail Q(a) (no link between P and Q is asserted) —
    # the structure {a} with P(a) true and Q(a) false is a countermodel to
    # the entailment, so this must be REFUTED, not UNKNOWN.
    premises = [_P.parse("P(a)")]
    conclusion = _P.parse("Q(a)")
    v = _backend.decide(conclusion, premises)
    assert v.status == REFUTED


def test_unsupported_linear_logic_formula_reports_honestly():
    # A ⊗ B (multiplicative conjunction) has no classical collapse — Node.to_z3
    # raises NotImplementedError by design (fol/_linear_nodes.py), so the
    # backend must surface UNKNOWN/"unsupported", never guess PROVED/REFUTED
    # and never let the NotImplementedError escape decide().
    tensor = _LIN.parse("A ⊗ B")
    v = _backend.decide(tensor)
    assert v.status == UNKNOWN
    assert v.reason == "unsupported"
    assert v.szs_status == "Inappropriate"


def test_verdict_fields_are_fully_populated():
    v = _backend.decide(_VALID)
    d = v.to_dict()
    assert d["backend"] == "cvc5"
    assert d["logic"] == "fol"
    assert d["status"] == "proved"
    assert d["wall_time"] > 0
    assert d["agreement"] == ["cvc5"]


def test_decide_never_raises_on_a_crash_inducing_bad_option():
    # A garbage `logic=` string is rejected by cvc5's own option validation —
    # the backend must convert that into an ERROR/"infra" Verdict rather than
    # letting the exception propagate (the ProverBackend contract: decide()
    # must never raise for an in-contract Node).
    v = _backend.decide(_VALID, logic="NOT_A_REAL_SMTLIB_LOGIC")
    assert v.status == ERROR
    assert v.reason == "infra"


# ---------------------------------------------------------------------------
# C12: an Alethe proof term + unsat core on every PROVED verdict
# ---------------------------------------------------------------------------

def test_proved_verdict_carries_an_alethe_proof():
    v = _backend.decide(_VALID)
    assert v.status == PROVED
    assert v.proof["kind"] == "cvc5_alethe"
    # A real Alethe proof step line, not an empty/placeholder string --
    # every Alethe proof is a sequence of "(step ... :rule ...)" forms.
    assert v.proof["text"] and ":rule" in v.proof["text"]
    assert v.proof["unsat_core"]        # non-empty: at least the negated goal


def test_refuted_and_unknown_verdicts_carry_no_proof():
    assert _backend.decide(_INVALID).proof is None                       # REFUTED
    v = _backend.decide(_VALID, logic="NOT_A_REAL_SMTLIB_LOGIC")
    assert v.status == ERROR and v.proof is None


def test_unsat_core_minimality_sanity_excludes_the_irrelevant_premise():
    """A hand-built entailment with one deliberately irrelevant extra
    premise: the returned core must name the forall/Human(socrates)
    premises actually used and must NOT mention the unrelated Bird(tweety)
    premise anywhere -- catching a core that is technically sound but
    trivially 'the whole premise set' (a useless certificate), which is
    exactly what asserting each premise as a SEPARATE SMT-LIB2 command
    (rather than one folded implication) fixes -- see
    Cvc5Backend._run's docstring.
    """
    premises = [_P.parse("∀x (Human(x) → Mortal(x))"),
               _P.parse("Human(socrates)"),
               _P.parse("Bird(tweety)")]
    goal = _P.parse("Mortal(socrates)")
    v = _backend.decide(goal, premises)
    assert v.status == PROVED
    core_text = " ".join(v.proof["unsat_core"])
    assert "Bird" not in core_text and "tweety" not in core_text
    assert "Human" in core_text and "Mortal" in core_text


def test_unsat_core_never_requires_both_of_a_redundant_pair():
    premises = [_P.parse("Mortal(socrates)"),
               _P.parse("Mortal(socrates) ∧ Human(socrates)")]
    goal = _P.parse("Mortal(socrates)")
    v = _backend.decide(goal, premises)
    assert v.status == PROVED
    # Exactly two entries: the negated goal, plus (at most) ONE of the two
    # independently-sufficient premises -- never a term mentioning BOTH
    # Mortal(socrates) alone AND the stronger conjunctive restatement.
    assert len(v.proof["unsat_core"]) == 2


def test_unsat_core_soundness_self_check_reproving_just_the_reported_subset():
    """The independent second route the spec's test_oracle names: since the
    core is TEXT (SMT-LIB2 term strings, not indices — see
    Cvc5Backend._run's docstring), re-parsing it back into terms is its own
    can of worms, so this drives the same property through the kit's own
    premise list instead: for THIS fixture each premise's own vocabulary is
    disjoint from the others' (Human/Mortal vs. Bird), so "does the core
    text mention this premise's own symbol" is a sound per-premise
    membership test. The reduced subset must still reprove the goal on a
    second, independent decide() call — an unsound over-pruning bug in the
    core would make that second call fail.
    """
    premises = [_P.parse("∀x (Human(x) → Mortal(x))"),
               _P.parse("Human(socrates)"),
               _P.parse("Bird(tweety)")]
    goal = _P.parse("Mortal(socrates)")
    v = _backend.decide(goal, premises)
    core_text = " ".join(v.proof["unsat_core"])
    own_symbol = {0: "Human", 1: "Human", 2: "Bird"}    # each premise's distinguishing symbol
    subset = [p for i, p in enumerate(premises) if own_symbol[i] in core_text]
    assert subset == premises[:2]        # sanity: Bird(tweety) alone got dropped
    assert _backend.decide(goal, subset).status == PROVED


def test_unsat_core_excludes_the_synthetic_non_emptiness_axiom():
    """Many-sorted PROVED verdicts add ``nonempty_sort_axioms(...)`` (see the
    class docstring's "Many-sorted (MSFOL) soundness" paragraph) as an
    extra, unconditional assertion alongside the caller's own premises --
    but that synthetic axiom is background MSFOL convention, never one of
    the caller's own premises, so it must never show up in the REPORTED
    unsat core, mirroring ``atp.protocol.Z3Backend``'s ``z3_unsat_core``
    (whose ``_z3_track_and_check`` keeps the identical axiom untracked for
    exactly this reason -- see ``Cvc5Backend._run``'s docstring for how this
    backend does the analogous exclusion without an ``assert_and_track``-
    style tag to lean on). Hand-checked: ``(∀x:Ghost P(x)) ⊨ (∃x:Ghost
    P(x))`` is a textbook tautology once ``Ghost`` is known non-empty
    (universal instantiation at the witness, then existential
    generalisation), so this comes back PROVED with exactly two core
    entries -- the premise and the negated goal -- never a third one for
    the synthetic ``∃x (Ghost(x))`` axiom nonempty_sort_axioms adds.
    """
    MSFOL = MSFLParser(many_sorted=True)
    premise = MSFOL.parse("∀x:Ghost P(x)")
    goal = MSFOL.parse("∃x:Ghost P(x)")
    v = _backend.decide(goal, [premise])
    assert v.status == PROVED
    core = v.proof["unsat_core"]
    assert len(core) == 2          # exactly the caller's premise and negated goal
    core_text = " ".join(core)
    # nonempty_sort_axioms names its bound variable "_msfol_<Sort>_witness"
    # (fol/_msfl_nodes.py) -- that token appearing here would mean the
    # synthetic axiom leaked into the reported core.
    assert "_msfol_Ghost_witness" not in core_text
    assert "Ghost" in core_text and "P" in core_text


def test_reported_sorted_premise_was_really_needed_not_just_padding():
    """The independent second-route sanity check for the sorted case,
    mirroring
    ``test_unsat_core_soundness_self_check_reproving_just_the_reported_subset``:
    the fix only removes the SYNTHETIC non-emptiness axiom from the report,
    never the caller's own premise, so the ``∀x:Ghost P(x)`` premise the
    core names as used must genuinely be load-bearing -- dropping it must
    turn the same goal from PROVED to NOT-PROVED, since "some Ghost exists"
    (``nonempty_sort_axioms``'s own witness, still asserted unconditionally)
    does not by itself entail "some Ghost is a P".
    """
    MSFOL = MSFLParser(many_sorted=True)
    goal = MSFOL.parse("∃x:Ghost P(x)")
    assert _backend.decide(goal, []).status != PROVED


def test_alethe_proof_checks_with_carcara_when_installed():
    """Optional, fully independent verification pass — gated on the external
    Carcara checker being on PATH, the same discipline test_hol_isabelle.py
    etc. already use for Isabelle/Vampire/Prover9 (skip, never fake a pass,
    when the tool is absent)."""
    import shutil
    import subprocess
    import tempfile

    carcara = shutil.which("carcara")
    if carcara is None:
        pytest.skip("no carcara binary found — this check is opt-in only")

    v = _backend.decide(_VALID)
    assert v.status == PROVED
    with tempfile.NamedTemporaryFile(mode="w", suffix=".alethe", delete=False,
                                     encoding="utf-8") as tmp:
        tmp.write(v.proof["text"])
        path = tmp.name
    try:
        result = subprocess.run([carcara, "check", path],
                                capture_output=True, text=True, timeout=30)
        assert result.returncode == 0, result.stdout + result.stderr
    finally:
        import os
        os.unlink(path)


# ---------------------------------------------------------------------------
# ASCII/legality sanitisation — digit-leading names, which used to SEGFAULT
# the whole process (Z3's own to_smt2() does not quote a pure-ASCII
# digit-leading name, so the replayed SMT-LIB2 text was malformed, and cvc5's
# native parser crashed on it rather than raising a catchable Python
# exception — reproduced live before this fix, exit code 139). Every claim
# below is EXECUTED, never just asserted: against the real cvc5 backend
# (module-level importorskip already gates the whole file on cvc5 being
# importable) and, separately, against z3.parse_smt2_string as the R5
# ground truth for "is this SMT-LIB2 text actually legal".
# ---------------------------------------------------------------------------

from unicode_fol_kit.fol.msflparser import MSFLParser as _MSFLParser
from unicode_fol_kit.fol.nodes import Constant as _Constant
from unicode_fol_kit.atp.cvc5_backend import _sanitize_for_smtlib, _implication

_UPARSE = _MSFLParser().parse


class TestDigitLeadingNamesNoLongerCrash:
    def test_digit_leading_constant_does_not_segfault_and_returns_a_verdict(self):
        # Historically this line never returned at all (the process died) —
        # simply completing without an OS-level crash IS the regression
        # test; the assertions below check the answer is also correct.
        f = _UPARSE("P(2008SummerOlympics)")
        v = _backend.decide(f)
        assert v.status in ("proved", "refuted", "unknown", "error")

    def test_digit_leading_constant_reports_a_genuine_countermodel(self):
        f = _UPARSE("∀x P(x)")  # refutable, same shape as _INVALID
        premises = [_UPARSE("Q(2008SummerOlympics)")]  # forces the sort non-empty, name in scope
        v = _backend.decide(f, premises)
        assert v.status == REFUTED
        assert "2008SummerOlympics" in v.countermodel["assignment"]

    def test_digit_leading_predicate_name_does_not_crash_either(self):
        # A digit-leading identifier is ALWAYS term-valued in the grammar
        # (see fol._identifiers's module docstring: predicate-hood needs an
        # uppercase-signalling first character, which a digit cannot carry),
        # so this is reachable only via a programmatically built node, not
        # through the parser — exactly the pre-existing reachability path
        # the task's STAND note describes for every one of these gaps.
        from unicode_fol_kit.fol.nodes import Atom, Constant
        f = Atom("2008Wins", [Constant("alice")])
        v = _backend.decide(f)
        assert v.status in ("proved", "refuted", "unknown", "error")


class TestSmtlib2TextIsValidPerZ3sOwnParser:
    """R5: the sanitised SMT-LIB2 text round-trips through z3.parse_smt2_string
    — the actual bug reproduction/fix, independent of cvc5 being installed."""

    def test_digit_leading_name_smt2_text_parses(self):
        import z3

        f = _UPARSE("P(2008SummerOlympics)")
        goal = _implication(f, [])
        sanitised, mapping = _sanitize_for_smtlib(goal)
        assert mapping.mapping["2008SummerOlympics"][0].isalpha()
        z3_goal = sanitised.to_z3()
        solver = z3.Solver()
        solver.add(z3.Not(z3_goal))
        text = solver.to_smt2()
        z3.parse_smt2_string(text)  # must not raise

    def test_unsanitised_digit_leading_name_smt2_text_does_NOT_parse(self):
        # Negative control: confirms the bug this module fixes is real and
        # that the test above is actually exercising the fix, not a formula
        # that was never broken.
        import z3

        f = _UPARSE("P(2008SummerOlympics)")
        goal = _implication(f, [])          # UNSANITISED goal
        z3_goal = goal.to_z3()
        solver = z3.Solver()
        solver.add(z3.Not(z3_goal))
        text = solver.to_smt2()
        with pytest.raises(z3.Z3Exception):
            z3.parse_smt2_string(text)


class TestReservedWordNamesAreAlsoSanitised:
    """Extends R5's coverage: an SMT-LIB2 <reserved> word (``let``, ...) used
    as a predicate/function/constant name is a SECOND legality gap Z3's own
    ``to_smt2()`` does not close on its own (found live while building the
    public ``to_smtlib`` writer that reuses this module's sanitiser — see
    the module docstring's sanitisation section, updated to cover it)."""

    def test_reserved_word_predicate_name_smt2_text_parses(self):
        import z3
        from unicode_fol_kit.fol.nodes import Atom, Constant

        # "let" is a legal lower-case-initial NAME in the kit's own grammar
        # (predicate-hood needs an UPPER-case initial) but an SMT-LIB2
        # <reserved> word, so it is reachable as a predicate only via a
        # programmatically built node — same reachability shape as
        # TestDigitLeadingNamesNoLongerCrash's "2008Wins" predicate case.
        f = Atom("let", [Constant("x")])
        goal = _implication(f, [])
        sanitised, mapping = _sanitize_for_smtlib(goal)
        assert mapping.mapping["let"] != "let"
        z3_goal = sanitised.to_z3()
        solver = z3.Solver()
        solver.add(z3.Not(z3_goal))
        text = solver.to_smt2()
        z3.parse_smt2_string(text)  # must not raise

    def test_unsanitised_reserved_word_name_smt2_text_does_NOT_parse(self):
        # Negative control, same shape as R5's: Z3's own to_smt2() does not
        # quote "let" either, so an uninterpreted predicate named "let"
        # prints as the undecorated head of "(let x)", which Z3's OWN
        # parser then reads as the let-BINDING form and rejects.
        import z3
        from unicode_fol_kit.fol.nodes import Atom, Constant

        f = Atom("let", [Constant("x")])
        goal = _implication(f, [])          # UNSANITISED goal
        z3_goal = goal.to_z3()
        solver = z3.Solver()
        solver.add(z3.Not(z3_goal))
        text = solver.to_smt2()
        with pytest.raises(z3.Z3Exception):
            z3.parse_smt2_string(text)

    def test_reserved_word_predicate_name_decides_through_cvc5_too(self):
        from unicode_fol_kit.fol.nodes import Atom, Constant

        f = Atom("let", [Constant("x")])
        v = _backend.decide(f)
        assert v.status in ("proved", "refuted", "unknown", "error")


class TestSixReservedGrammarWordsZ3DoesNotSpecialCase:
    """R1 negative control for the review finding on ``_SMTLIB_RESERVED_WORDS``:
    the SMT-LIB2 v2.6 grammar (Sec. 3.1) lists 13 ``<reserved>`` words, but
    Z3's own parser only actually treats 7 of them specially as syntax. The
    other 6 (``BINARY``, ``DECIMAL``, ``HEXADECIMAL``, ``NUMERAL``, ``par``,
    ``STRING``) already round-trip correctly through Z3's own SMT-LIB2
    serialisation with no help from this module, in EVERY role a kit name
    can be emitted in (bare declaration, applied predicate/function head,
    argument) — so ``_sanitize_for_smtlib`` must leave them identity-mapped,
    exactly like R1's non-ASCII case below, not rename something that
    already worked."""

    _WORDS = ["BINARY", "DECIMAL", "HEXADECIMAL", "NUMERAL", "par", "STRING"]

    @pytest.mark.parametrize("word", _WORDS)
    def test_identity_mapped_by_the_sanitiser(self, word):
        from unicode_fol_kit.fol.nodes import Atom, Constant

        f = Atom("P", [Constant(word)])
        goal = _implication(f, [])
        _, mapping = _sanitize_for_smtlib(goal)
        assert mapping.mapping[word] == word

    @pytest.mark.parametrize("word", _WORDS)
    def test_applied_as_a_predicate_head_parses_via_z3_unsanitised(self, word):
        # Positive control proving these six are safe even in the ONE role
        # ("applied as a function/predicate head") where digit-leading names
        # and the true 7 reserved words actually break Z3's own parser —
        # confirms sanitising them would be pure unforced renaming, not a
        # fix for anything.
        import z3
        from unicode_fol_kit.fol.nodes import Atom, Constant

        f = Atom(word, [Constant("x")])
        z3_goal = f.to_z3()
        solver = z3.Solver()
        solver.add(z3_goal)
        text = solver.to_smt2()
        z3.parse_smt2_string(text)  # must not raise


class TestNonAsciiNamesAlreadyWorkedAndStayUntouched:
    """R1: a non-ASCII name already round-trips through Z3's own SMT-LIB2
    quoting correctly (verified live before this module's sanitisation
    existed) — _sanitize_for_smtlib must leave it identity-mapped, not
    rename something that already worked."""

    def test_non_ascii_constant_is_identity_mapped(self):
        f = _UPARSE("P(świątek)")
        goal = _implication(f, [])
        _, mapping = _sanitize_for_smtlib(goal)
        assert mapping.mapping["świątek"] == "świątek"

    def test_non_ascii_constant_still_decides_and_names_itself_in_countermodel(self):
        f = _UPARSE("∀x P(x)")
        premises = [_UPARSE("Q(świątek)")]
        v = _backend.decide(f, premises)
        assert v.status == REFUTED
        # R3 polish: the pipe-quoting cvc5's str(term) reproduces
        # ("|świątek|") is stripped, so the caller sees the TRUE original
        # name, not SMT-LIB2 quoting syntax wrapped around it.
        assert "świątek" in v.countermodel["assignment"]
        assert "|świątek|" not in v.countermodel["assignment"]


class TestR2CollisionAvoidance:
    def test_two_different_digit_leading_names_get_distinct_tokens(self):
        from unicode_fol_kit.fol.nodes import Atom
        goal = _implication(
            Atom("=", [_Constant("2008SummerOlympics"), _Constant("2012London")]), [])
        _, mapping = _sanitize_for_smtlib(goal)
        assert mapping.mapping["2008SummerOlympics"] != mapping.mapping["2012London"]

    def test_synthesised_token_never_collides_with_an_already_legal_name(self):
        from unicode_fol_kit.fol.nodes import Atom
        # "n2008x" is what a naive synthesis of "2008x" would target; a
        # literal constant ALREADY named "n2008x" must not be clobbered,
        # regardless of which one this walk reaches first.
        for args in ([_Constant("n2008x"), _Constant("2008x")],
                    [_Constant("2008x"), _Constant("n2008x")]):
            goal = _implication(Atom("=", args), [])
            _, mapping = _sanitize_for_smtlib(goal)
            assert mapping.mapping["n2008x"] == "n2008x"
            assert mapping.mapping["2008x"] != "n2008x"
