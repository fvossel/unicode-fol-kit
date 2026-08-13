"""Tests for unicode_fol_kit.eval.theory_check — the deductive verification
layer for a collection of predicate definitions (see the module docstring for
the motivation: model checking alone cannot see that a definition is dead,
cyclic, or missing a superclass conjunct).

Every expected value below is worked out by hand in the comment next to the
assertion — never copied from a program run. Backends are pinned to
``["z3"]`` wherever the test only needs *a* fast, deterministic decision
(Z3's SMT search on these toy 0-ary/small-existential formulas is essentially
instant and, with the fixed ``random_seed=42`` the kit's ``Z3Backend`` sets,
deterministic run to run); the one test that needs an ``"unknown"`` verdict
gets it by starving the tableau backend of search budget (``max_steps=1``),
which is deterministic and fast by construction — never by racing a
wall-clock timeout.
"""

import pytest

from unicode_fol_kit.fol.nodes import Atom, Not, And, Or, Implies, Quantifier, Variable
from unicode_fol_kit.eval.theory_check import (
    Definitions,
    CyclicDefinition, UnfoldDepthExceeded, NonClosedDefinition,
    dependency_graph, find_cycles, unfold,
    SatisfiabilityResult, check_satisfiable,
    SubsumptionResult, check_subsumption,
    TheoryReport, check_theory,
)


def P(name="p"):
    return Atom(name, [])


def Q(name="q"):
    return Atom(name, [])


# ---------------------------------------------------------------------------
# dependency_graph / find_cycles
# ---------------------------------------------------------------------------

class TestDependencyGraphAndCycles:
    def test_direct_self_cycle(self):
        # A <=> A: A's body IS the bare atom A -> A depends on itself.
        defs = {"A": Atom("A", [])}
        assert dependency_graph(defs) == {"A": frozenset({"A"})}
        # Cycle sequence: A -> A (first==last), the direct self-reference.
        assert find_cycles(defs) == (("A", "A"),)

    def test_indirect_cycle_a_b_a(self):
        # A <=> B, B <=> A: A depends on {B}, B depends on {A}; the only
        # cycle is A -> B -> A (reported once, deduplicated regardless of
        # which node the internal DFS starts from — see _normalize_cycle).
        defs = {"A": Atom("B", []), "B": Atom("A", [])}
        deps = dependency_graph(defs)
        assert deps == {"A": frozenset({"B"}), "B": frozenset({"A"})}
        assert find_cycles(defs) == (("A", "B", "A"),)

    def test_no_cycle_in_acyclic_chain(self):
        # A <=> B, B <=> primitive p: no cycle anywhere.
        defs = {"A": Atom("B", []), "B": P()}
        assert find_cycles(defs) == ()
        # B uses no defined name (p is primitive, not a key of defs).
        assert dependency_graph(defs) == {"A": frozenset({"B"}), "B": frozenset()}

    def test_dependency_graph_ignores_nonzero_arity_same_name_atom(self):
        # A body mentioning "B" applied to an argument is a DIFFERENT symbol
        # (arity 1) from the defined 0-ary predicate "B" — not a dependency.
        x = Variable("x")
        defs = {"A": Atom("B", [x]), "B": P()}
        assert dependency_graph(defs) == {"A": frozenset(), "B": frozenset()}

    def test_chemical_definitions_dependency_graph(self):
        # molecule depends on nothing (net_charge_neutral is primitive);
        # organicMolecularEntity depends on {molecule}; thioester depends on
        # {organicMolecularEntity}; carboxylicAcid depends on {carbonOxoacid}.
        a1 = Variable("a1")
        defs = {
            "molecule": Atom("net_charge_neutral", []),
            "organicMolecularEntity": Quantifier(
                "exists", a1, And(Atom("molecule", []), Atom("c", [a1]))),
            "thioester": And(Atom("organicMolecularEntity", []), Atom("s", [a1])),
            "carboxylicAcid": And(Atom("carbonOxoacid", []), Atom("c", [a1])),
        }
        deps = dependency_graph(defs)
        assert deps["molecule"] == frozenset()
        assert deps["organicMolecularEntity"] == frozenset({"molecule"})
        assert deps["thioester"] == frozenset({"organicMolecularEntity"})
        # carbonOxoacid is not itself a key here, so it is simply not counted
        # as a "defined name used" — dependency_graph only reports edges INTO
        # this definitions dict's own keys.
        assert deps["carboxylicAcid"] == frozenset()
        assert find_cycles(defs) == ()


# ---------------------------------------------------------------------------
# unfold
# ---------------------------------------------------------------------------

class TestUnfold:
    def test_unfold_matches_hand_written_expansion(self):
        # A <=> p ∧ B,  B <=> q ∨ r.
        # unfold("A") substitutes B's body in place of the atom B:
        #   p ∧ (q ∨ r)  -- written out by hand, not derived from the code.
        defs = {
            "A": And(P("p"), Atom("B", [])),
            "B": Or(P("q"), P("r")),
        }
        result = unfold("A", defs)
        expected = And(P("p"), Or(P("q"), P("r")))
        assert result == expected

    def test_unfold_two_levels_deep(self):
        # A <=> B, B <=> C, C <=> p.  unfold("A") must reach all the way to
        # the primitive: p.
        defs = {"A": Atom("B", []), "B": Atom("C", []), "C": P()}
        assert unfold("A", defs) == P()

    def test_unfold_sibling_reuse_is_not_a_cycle(self):
        # A <=> B ∧ B  (the SAME defined name used twice, as siblings, not
        # nested inside its own expansion) -- this is NOT circular: each
        # occurrence is independently substituted.
        # B <=> p.  Expected: p ∧ p.
        defs = {"A": And(Atom("B", []), Atom("B", [])), "B": P()}
        assert unfold("A", defs) == And(P(), P())

    def test_unfold_leaves_primitive_predicates_untouched(self):
        # A <=> exists x exists y (c(x) & o(y)): c/o are not keys of defs, so
        # nothing changes. Wrapped in quantifiers (rather than the bare free
        # x/y this test used before) because a definition body is now
        # required to be a CLOSED sentence (see TestUnfoldRefusesNonClosed
        # DefinitionBodies below and NonClosedDefinition's docstring) --
        # the property this test checks (primitive atoms pass through
        # untouched) is unaffected by that wrapping.
        x, y = Variable("x"), Variable("y")
        body = Quantifier("exists", x, Quantifier("exists", y,
                          And(Atom("c", [x]), Atom("o", [y]))))
        defs = {"A": body}
        assert unfold("A", defs) == body

    def test_unfold_raises_on_direct_cycle(self):
        defs = {"A": Atom("A", [])}
        with pytest.raises(CyclicDefinition):
            unfold("A", defs)

    def test_unfold_raises_on_indirect_cycle(self):
        defs = {"A": Atom("B", []), "B": Atom("A", [])}
        with pytest.raises(CyclicDefinition):
            unfold("A", defs)
        with pytest.raises(CyclicDefinition):
            unfold("B", defs)

    def test_unfold_raises_on_depth_exceeded(self):
        # A chain of 4 definitional layers (A->B->C->D->p) but max_depth=2:
        # expanding A needs 4 substitutions to reach the primitive p, so a
        # budget of 2 must be refused, not silently truncated.
        defs = {"A": Atom("B", []), "B": Atom("C", []),
                "C": Atom("D", []), "D": P()}
        with pytest.raises(UnfoldDepthExceeded):
            unfold("A", defs, max_depth=2)
        # The same chain unfolds fine with enough budget.
        assert unfold("A", defs, max_depth=10) == P()

    def test_unfold_unknown_name_raises_key_error(self):
        with pytest.raises(KeyError):
            unfold("nosuch", {"A": P()})


# ---------------------------------------------------------------------------
# Regression tests for Finding 3: unfold() must refuse a non-closed
# definition body rather than silently capture its free variable in an
# unrelated enclosing binder of the same name.
# ---------------------------------------------------------------------------

class TestUnfoldRefusesNonClosedDefinitionBodies:
    def test_unfold_refuses_a_non_closed_definition_body(self):
        # A <=> p(a1): a1 is FREE in A's body -- not a well-formed 0-ary
        # definition (this module's data model requires every definition
        # body to be a CLOSED sentence; see the module docstring's "Data
        # model" section). B <=> exists a1 (q(a1) & A) uses A (0-ary) inside
        # its OWN "exists a1" scope, with the SAME variable name.
        #
        # Hand-derived: before the fix, unfold("B", defs) performed plain
        # (non-capture-avoiding) substitution, replacing the atom A with A's
        # body p(a1) VERBATIM at the point where it occurs -- i.e. INSIDE
        # B's "exists a1" scope. The free a1 in A's body would then be
        # silently CAPTURED by B's own binder, producing
        # "exists a1 (q(a1) & p(a1))" -- as if A's free a1 always meant "B's
        # own witness", even though nothing in A's definition says that (A
        # was defined completely independently of B, and a free variable in
        # a 0-ary definition's body is not a parameter any caller is
        # entitled to bind). That silent identification is exactly the
        # soundness bug: two occurrences of "a1" that do not denote the same
        # thing get conflated. The fix refuses up front instead.
        a1 = Variable("a1")
        defs: Definitions = {
            "A": Atom("p", [a1]),
            "B": Quantifier("exists", a1, And(Atom("q", [a1]), Atom("A", []))),
        }
        with pytest.raises(NonClosedDefinition):
            unfold("B", defs)

    def test_unfold_refuses_even_when_the_offending_definition_itself_is_the_target(self):
        # Same malformed set, but unfold("A", ...) directly -- A's own body
        # is non-closed regardless of which name is being unfolded, so this
        # must refuse too (not just when reached transitively through B).
        a1 = Variable("a1")
        defs: Definitions = {
            "A": Atom("p", [a1]),
            "B": Quantifier("exists", a1, And(Atom("q", [a1]), Atom("A", []))),
        }
        with pytest.raises(NonClosedDefinition):
            unfold("A", defs)

    def test_check_satisfiable_refuses_a_non_closed_definition_body(self):
        a1 = Variable("a1")
        defs: Definitions = {
            "A": Atom("p", [a1]),
            "B": Quantifier("exists", a1, And(Atom("q", [a1]), Atom("A", []))),
        }
        with pytest.raises(NonClosedDefinition):
            check_satisfiable("B", defs, backends=["z3"])

    def test_check_subsumption_refuses_a_non_closed_definition_body(self):
        a1 = Variable("a1")
        defs: Definitions = {
            "A": Atom("p", [a1]),
            "B": Quantifier("exists", a1, And(Atom("q", [a1]), Atom("A", []))),
            "C": P("c"),
        }
        with pytest.raises(NonClosedDefinition):
            check_subsumption("B", "C", defs, backends=["z3"])

    def test_check_theory_refuses_a_non_closed_definition_body(self):
        a1 = Variable("a1")
        defs: Definitions = {
            "A": Atom("p", [a1]),
            "B": Quantifier("exists", a1, And(Atom("q", [a1]), Atom("A", []))),
        }
        with pytest.raises(NonClosedDefinition):
            check_theory(defs, backends=["z3"])

    def test_closed_definitions_are_never_affected_by_the_precondition(self):
        # Sanity check: the new precondition never fires for well-formed
        # (closed-body) definitions -- every ordinary unfold/check_* call
        # keeps working exactly as before.
        a1 = Variable("a1")
        defs: Definitions = {
            "A": Quantifier("exists", a1, Atom("p", [a1])),
            "B": Atom("A", []),
        }
        assert unfold("B", defs) == Quantifier("exists", a1, Atom("p", [a1]))
        result = check_satisfiable("B", defs, backends=["z3"])
        assert result.status == "satisfiable"


# ---------------------------------------------------------------------------
# check_satisfiable
# ---------------------------------------------------------------------------

class TestCheckSatisfiable:
    def test_unsatisfiable_zero_ary_contradiction(self):
        # deadClass <=> p ∧ ¬p: a plain propositional contradiction,
        # independent of any object — deadClass can hold of nothing.
        defs = {"deadClass": And(P(), Not(P()))}
        result = check_satisfiable("deadClass", defs, backends=["z3"])
        assert result.status == "unsatisfiable"
        assert result.backend == "z3"

    def test_unsatisfiable_quantified_contradiction(self):
        # badRing <=> ∃a1 (c(a1) ∧ ¬c(a1)): for EVERY a1, c(a1) ∧ ¬c(a1) is
        # false, so the existential is false regardless of domain -- UNSAT.
        a1 = Variable("a1")
        defs = {"badRing": Quantifier(
            "exists", a1, And(Atom("c", [a1]), Not(Atom("c", [a1]))))}
        result = check_satisfiable("badRing", defs, backends=["z3"])
        assert result.status == "unsatisfiable"

    def test_satisfiable_definition_gets_a_witness(self):
        # okClass <=> p: trivially satisfiable (p := True).
        defs = {"okClass": P()}
        result = check_satisfiable("okClass", defs, backends=["z3"])
        assert result.status == "satisfiable"
        assert result.witness is not None

    def test_cyclic_definition_reported_as_cyclic_not_unknown(self):
        defs = {"A": Atom("A", [])}
        result = check_satisfiable("A", defs)
        assert result.status == "cyclic"
        assert result.unfolded is None

    def test_depth_exceeded_reported_as_unknown_not_cyclic(self):
        # Regression test for Finding 2: a chain of 4 nested definitional
        # layers (A->B->C->D->p) but max_depth=2. unfold("A", defs,
        # max_depth=2) needs 4 substitutions to reach the primitive p (see
        # TestUnfold.test_unfold_raises_on_depth_exceeded, which pins down
        # that it raises UnfoldDepthExceeded, NOT CyclicDefinition, for this
        # exact defs/max_depth) -- and find_cycles(defs) below PROVES there
        # is no cycle anywhere in this definition set at all.
        #
        # Before the fix, check_satisfiable caught CyclicDefinition and
        # UnfoldDepthExceeded in the SAME except clause and reported both as
        # status="cyclic" -- a status this module documents (see
        # TheoryReport.proved_problems) as a PROVEN defect, on the same
        # footing as an unsatisfiable definition. That is wrong here: this
        # definition set is PROVABLY acyclic (find_cycles == ()), so
        # reporting "cyclic" would assert a proven defect that provably does
        # not exist -- a budget exhaustion must be "unknown" instead.
        defs = {"A": Atom("B", []), "B": Atom("C", []),
                "C": Atom("D", []), "D": P()}
        assert find_cycles(defs) == ()  # provably acyclic
        result = check_satisfiable("A", defs, max_depth=2)
        assert result.status == "unknown"
        assert result.unfolded is None

    def test_unknown_name_raises_key_error(self):
        with pytest.raises(KeyError):
            check_satisfiable("nosuch", {"A": P()})

    def test_result_to_dict_is_json_shaped(self):
        defs = {"okClass": P()}
        result = check_satisfiable("okClass", defs, backends=["z3"])
        d = result.to_dict()
        assert d["status"] == "satisfiable"
        assert d["unfolded"]["_type"] == "Atom"

    def test_invalid_status_rejected(self):
        with pytest.raises(ValueError):
            SatisfiabilityResult(name="x", status="bogus", unfolded=None,
                                 witness=None, backend=None, detail=None)


# ---------------------------------------------------------------------------
# check_subsumption
# ---------------------------------------------------------------------------

class TestCheckSubsumption:
    def test_real_definitions_carboxylic_acid_entails_carbon_oxoacid(self):
        """A realistic set of chemical class definitions, verbatim FOL:

            molecule <=> net_charge_neutral
            organicMolecularEntity <=> ?[A1]: (molecule & c(A1))
            thioester <=> (organicMolecularEntity &
                ?[A1,A2,A3]: (c(A1) & o(A2) & s(A3) &
                              bDOUBLE(A1,A2) & bSINGLE(A1,A3)))
            carboxylicAcid <=> (carbonOxoacid &
                ?[A1,A2,A3]: (c(A1) & o(A2) & o(A3) & has_1_hs(A3) &
                              bDOUBLE(A1,A2) & bSINGLE(A1,A3)))

        carbonOxoacid's own body is not part of the excerpt this module was
        built from, so it is stood in here as a small, honestly labelled
        placeholder (``carbonOxoacid <=> organicMolecularEntity``) —
        the point being tested does not depend on what that body actually
        is: carboxylicAcid's unfolded definition is LITERALLY
        ``carbonOxoacid's-unfolded-body ∧ (more stuff)``, so
        carboxylicAcid -> carbonOxoacid is entailed BY CONSTRUCTION (a
        tautology of propositional shape (P ∧ Q) -> P, however large P and Q
        are) — exactly the claim the task requires this test to pin down.
        """
        a1, a2, a3 = Variable("a1"), Variable("a2"), Variable("a3")

        def c(t): return Atom("c", [t])
        def o(t): return Atom("o", [t])
        def s(t): return Atom("s", [t])
        def bDOUBLE(x, y): return Atom("bDOUBLE", [x, y])
        def bSINGLE(x, y): return Atom("bSINGLE", [x, y])
        def has_1_hs(t): return Atom("has_1_hs", [t])

        defs: Definitions = {
            "molecule": Atom("net_charge_neutral", []),
            "organicMolecularEntity": Quantifier(
                "exists", a1, And(Atom("molecule", []), c(a1))),
            "carbonOxoacid": Atom("organicMolecularEntity", []),  # placeholder, see docstring
            "thioester": And(
                Atom("organicMolecularEntity", []),
                Quantifier("exists", a1, Quantifier("exists", a2, Quantifier(
                    "exists", a3,
                    And(c(a1), And(o(a2), And(s(a3), And(
                        bDOUBLE(a1, a2), bSINGLE(a1, a3))))))))),
            "carboxylicAcid": And(
                Atom("carbonOxoacid", []),
                Quantifier("exists", a1, Quantifier("exists", a2, Quantifier(
                    "exists", a3,
                    And(c(a1), And(o(a2), And(o(a3), And(has_1_hs(a3), And(
                        bDOUBLE(a1, a2), bSINGLE(a1, a3)))))))))),
        }

        result = check_subsumption("carboxylicAcid", "carbonOxoacid", defs,
                                   backends=["z3"])
        assert result.status == "entailed"
        assert result.countermodel is None
        assert result.verdict["status"] == "proved"

    def test_constructed_violation_is_refuted_with_countermodel(self):
        # sub <=> p            (only requires primitive p)
        # sup <=> p ∧ q        (requires p AND primitive q)
        # sub's author forgot the q conjunct that sup (the intended
        # superclass) requires -> sub does NOT entail sup.
        # Hand-derived countermodel requirement: ANY witness must have
        # sub=True (so p=True, since sub IS p) and sup=False (so, since
        # p=True already, q must be False) -- this is forced by the logic
        # of the goal itself, not by which solver happens to answer.
        defs: Definitions = {"sub": P(), "sup": And(P(), Q())}
        result = check_subsumption("sub", "sup", defs, backends=["z3"])
        assert result.status == "refuted"
        assert result.countermodel is not None
        assignment = result.countermodel["assignment"]
        assert assignment["p"] == "True"
        assert assignment["q"] == "False"
        assert result.explanation  # a non-empty plain-English gloss

    def test_timeout_like_case_is_unknown_never_refuted(self):
        # Same violation as above, but the ONLY backend allowed is the
        # tableau prover starved to max_steps=1 -- far too little budget to
        # close or saturate anything, so it MUST come back bound_hit/unknown.
        # This is deterministic (a step-count bound, not a wall clock), so
        # the test is fast and never flaky.
        defs: Definitions = {"sub": P(), "sup": And(P(), Q())}
        result = check_subsumption("sub", "sup", defs,
                                   backends=["tableau"], max_steps=1)
        assert result.status == "unknown"
        assert result.countermodel is None

    def test_cyclic_sub_reported_as_cyclic(self):
        defs: Definitions = {"A": Atom("A", []), "B": P()}
        result = check_subsumption("A", "B", defs)
        assert result.status == "cyclic"
        assert result.verdict is None

    def test_cyclic_sup_reported_as_cyclic(self):
        defs: Definitions = {"A": P(), "B": Atom("B", [])}
        result = check_subsumption("A", "B", defs)
        assert result.status == "cyclic"

    def test_depth_exceeded_reported_as_unknown_not_cyclic(self):
        # Regression test for Finding 2 (check_subsumption's copy of the same
        # bug as TestCheckSatisfiable.
        # test_depth_exceeded_reported_as_unknown_not_cyclic): "sub" needs 4
        # nested substitutions to reach a primitive but max_depth=2, and the
        # whole definition set is provably acyclic (find_cycles == ()) --
        # unfolding "sub" must raise UnfoldDepthExceeded (not
        # CyclicDefinition), which check_subsumption must report as
        # status="unknown", not the PROVEN-defect status "cyclic".
        defs: Definitions = {"sub": Atom("B", []), "B": Atom("C", []),
                             "C": Atom("D", []), "D": P(), "sup": P("q")}
        assert find_cycles(defs) == ()  # provably acyclic
        result = check_subsumption("sub", "sup", defs, max_depth=2)
        assert result.status == "unknown"
        assert result.verdict is None

    def test_unknown_names_raise_key_error(self):
        defs: Definitions = {"A": P()}
        with pytest.raises(KeyError):
            check_subsumption("nosuch", "A", defs)
        with pytest.raises(KeyError):
            check_subsumption("A", "nosuch", defs)

    def test_refuted_result_without_countermodel_is_rejected_by_constructor(self):
        # SubsumptionResult's own invariant: status="refuted" must always
        # carry a witness (see check_subsumption's defensive downgrade to
        # "unknown" instead of ever constructing one of these).
        with pytest.raises(ValueError):
            SubsumptionResult(sub="a", sup="b", status="refuted",
                              verdict=None, countermodel=None, explanation=None)

    def test_invalid_status_rejected(self):
        with pytest.raises(ValueError):
            SubsumptionResult(sub="a", sup="b", status="bogus",
                              verdict=None, countermodel=None, explanation=None)


# ---------------------------------------------------------------------------
# check_theory
# ---------------------------------------------------------------------------

class TestCheckTheory:
    def test_combined_report_classifies_every_finding(self):
        # A definition set exercising every proved-problem kind at once:
        #   - "cycA"/"cycB" form a cycle (cycA <=> cycB, cycB <=> cycA)
        #   - "dead" is unsatisfiable (p ∧ ¬p)
        #   - "sub"/"sup" is a genuine (constructed) subsumption violation
        #   - "carboxylicAcid"/"carbonOxoacid"-style pair ("small"/"big")
        #     is a genuine entailment (small <=> big ∧ extra)
        defs: Definitions = {
            "cycA": Atom("cycB", []),
            "cycB": Atom("cycA", []),
            "dead": And(P(), Not(P())),
            "sub": P(),
            "sup": And(P(), Q()),
            "big": P(),
            "small": And(Atom("big", []), Q("extra")),
        }
        report = check_theory(
            defs,
            subsumptions=[("sub", "sup"), ("small", "big")],
            backends=["z3"],
        )

        assert report.cycles == (("cycA", "cycB", "cycA"),)

        # Satisfiability: "dead" unsatisfiable, "cycA"/"cycB" cyclic, the
        # rest satisfiable (p, and p∧q are both trivially satisfiable).
        assert report.satisfiability["dead"].status == "unsatisfiable"
        assert report.satisfiability["cycA"].status == "cyclic"
        assert report.satisfiability["cycB"].status == "cyclic"
        assert report.satisfiability["sub"].status == "satisfiable"
        assert report.satisfiability["sup"].status == "satisfiable"

        # Subsumptions: sub->sup refuted (missing q conjunct), small->big
        # entailed (small IS big ∧ extra, a tautological (P∧Q)->P).
        by_pair = {(r.sub, r.sup): r for r in report.subsumptions}
        assert by_pair[("sub", "sup")].status == "refuted"
        assert by_pair[("sub", "sup")].countermodel is not None
        assert by_pair[("small", "big")].status == "entailed"

        # proved_problems must contain exactly: the one cycle, "dead"
        # unsatisfiable, and the sub/sup refutation -- nothing else, and no
        # "unknown" leaks in here.
        kinds = sorted(p["kind"] for p in report.proved_problems)
        assert kinds == ["cycle", "subsumption_refuted", "unsatisfiable"]
        assert report.undecided == ()

    def test_depth_exceeded_name_lands_in_undecided_not_proved_problems(self):
        # Regression test for Finding 2 at the whole-theory level: "A"'s
        # chain (A->B->C->D->p) needs 4 substitutions but max_depth=2, and
        # this definition set is provably acyclic (find_cycles == ()) --
        # so check_theory must classify "A" as undecided ("unknown"), and
        # proved_problems (a PROVEN-defect list) must NOT contain a "cycle"
        # entry that find_cycles itself disproves.
        defs: Definitions = {"A": Atom("B", []), "B": Atom("C", []),
                             "C": Atom("D", []), "D": P()}
        report = check_theory(defs, max_depth=2, backends=["z3"])
        assert report.cycles == ()
        assert report.satisfiability["A"].status == "unknown"
        assert all(p["kind"] != "cycle" for p in report.proved_problems)
        assert any(item["kind"] == "satisfiability" and item["name"] == "A"
                   for item in report.undecided)

    def test_to_dict_shape(self):
        defs: Definitions = {"okClass": P()}
        report = check_theory(defs, backends=["z3"])
        d = report.to_dict()
        assert d["cycles"] == []
        assert d["satisfiability"]["okClass"]["status"] == "satisfiable"
        assert d["subsumptions"] == []
        assert d["proved_problems"] == []
        assert d["undecided"] == []

    def test_undecided_split_from_hand_built_report(self):
        # Directly exercises TheoryReport's proved_problems/undecided
        # splitting logic (independent of any live prover call) to pin down
        # that an "unknown" entry NEVER shows up in proved_problems and a
        # proved entry NEVER shows up in undecided.
        sat_unknown = SatisfiabilityResult(
            name="mystery", status="unknown", unfolded=P(), witness=None,
            backend=None, detail="ran out of budget")
        sat_unsat = SatisfiabilityResult(
            name="dead", status="unsatisfiable", unfolded=And(P(), Not(P())),
            witness=None, backend="z3", detail="contradiction")
        sub_unknown = SubsumptionResult(
            sub="x", sup="y", status="unknown", verdict={"status": "unknown"},
            countermodel=None, explanation="timeout")
        sub_entailed = SubsumptionResult(
            sub="a", sup="b", status="entailed", verdict={"status": "proved"},
            countermodel=None, explanation="proved by z3")

        report = TheoryReport(
            cycles=(),
            satisfiability={"mystery": sat_unknown, "dead": sat_unsat},
            subsumptions=(sub_unknown, sub_entailed),
        )
        problems = report.proved_problems
        undecided = report.undecided
        assert {"kind": "unsatisfiable", "name": "dead",
                "detail": "contradiction"} in problems
        assert all(p.get("name") != "mystery" for p in problems)
        assert all(p.get("sub") != "a" for p in problems)  # entailed, not a problem
        assert {"kind": "satisfiability", "name": "mystery",
                "detail": "ran out of budget"} in undecided
        assert {"kind": "subsumption", "sub": "x", "sup": "y",
                "detail": "timeout"} in undecided
