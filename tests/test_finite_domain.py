"""Tests for unicode_fol_kit.atp.finite_domain — the solver-independent core
shared by ClingoBackend and MinizincBackend.

Four things this module is responsible for, four test classes below:

* ``TestFiniteDomainProblem`` — the dataclass's own validation (non-empty
  sentences, ``size >= 1``, type checks on every field, and the default
  ``Signature.from_formulas`` inference when ``signature=None``).
* ``TestFragmentCheck`` — the single allow/refuse gate. Every REFUSED family
  is checked BY NAME (the exact ``"<NodeType> is not encodable: ..."``
  message the module docstring promises), not just "raises" or "is not
  None" — a gate that silently changed WHICH family it refuses, or reordered
  which offending node it reports first, would be a real regression a vaguer
  assertion would miss.
* ``TestStructureFromSolution`` — the reconstruction, round-tripped by hand:
  a fixed signature and a fixed list of ``(name, args)`` atoms produce an
  EXACT, hand-computed :class:`FiniteStructure` (domain strings, extension
  sets, constants dict), plus every documented failure mode (functionality/
  totality violated, an unknown symbol, a wrong arity, an out-of-range or
  non-int index, ``all_different`` violated).
* ``TestVerifyModel`` — the §3 safety net. A structure that genuinely
  satisfies a sentence must verify clean; a structure DELIBERATELY built to
  violate one (not a solver output — hand-built wrong on purpose) must be
  caught and named; and the module's own documented verification gap
  (``Cardinality``/``Function``/``Number``-as-comparison-operand/``Contrast``
  make ``evaluate_in_structure`` itself raise) must degrade to "could not
  verify", never silently read as "verified false" or "verified true".

Every expected value below is worked out from the input by hand in the
comment next to the assertion (never captured from a run of the module under
test) — the one exception, per the assignment's own instructions, is a
``pytest.mark.xfail(strict=True)`` case where a hand-derived expectation
DISAGREES with what the implementation actually does; that disagreement is
the finding, not a bug in the test.
"""

from dataclasses import dataclass

import pytest

from unicode_fol_kit.atp.finite_domain import (
    FiniteDomainProblem, fragment_check, structure_from_solution, verify_model,
)
from unicode_fol_kit.fol.nodes import (
    Node,
    Variable, Constant, Number, Function,
    Atom, Not, And, Or, Implies, Quantifier,
    Count, Cardinality, Contrast, Measure,
    SortedQuantifier, Box, SecondOrderQuantifier, Tensor, Lambda, LambdaVar,
    Dependence, WeakConjunction,
)
from unicode_fol_kit.fol.signature import Signature, PredicateDecl, FunctionDecl, ConstantDecl
from unicode_fol_kit.semantics.structures import FiniteStructure

X, Y = Variable("x"), Variable("y")


# =============================================================================
# FiniteDomainProblem
# =============================================================================

class TestFiniteDomainProblem:
    def test_valid_construction_infers_signature_and_coerces_sentences_to_tuple(self):
        # A list, not a tuple, is passed in on purpose: __post_init__ must
        # coerce it (Signature.from_formulas et al. downstream assume a
        # tuple), and signature=None must trigger the documented
        # Signature.from_formulas inference rather than leaving it None.
        sentence = Atom("P", [Constant("a")])
        problem = FiniteDomainProblem([sentence], 2)
        assert problem.sentences == (sentence,)
        assert isinstance(problem.sentences, tuple)
        # Hand-derived signature: one unary predicate P, one constant a,
        # exactly what Signature.from_formulas would produce from this
        # single atom (see fol/signature.py's own from_formulas contract).
        assert set(problem.signature.predicates) == {"P"}
        assert problem.signature.predicates["P"].arity == 1
        assert set(problem.signature.constants) == {"a"}
        assert problem.all_different is False  # documented default

    def test_explicit_signature_is_kept_verbatim_not_recomputed(self):
        # Passing an explicit Signature must short-circuit inference
        # entirely (the object identity check proves __post_init__ never
        # calls from_formulas again over it).
        sig = Signature.from_formulas([Atom("P", [Constant("a")])])
        problem = FiniteDomainProblem((Atom("P", [Constant("a")]),), 2, signature=sig)
        assert problem.signature is sig

    def test_empty_sentences_is_rejected(self):
        # "no goal to search for" per the class docstring — an empty
        # conjunction is vacuously true and searching for a countermodel of
        # it is meaningless, not merely trivial.
        with pytest.raises(ValueError, match="non-empty"):
            FiniteDomainProblem((), 2)

    def test_size_below_one_is_rejected(self):
        with pytest.raises(ValueError, match="size"):
            FiniteDomainProblem((Atom("P", [X]),), 0)
        with pytest.raises(ValueError, match="size"):
            FiniteDomainProblem((Atom("P", [X]),), -1)

    def test_size_must_be_a_plain_int_not_a_bool(self):
        # bool is an int subclass in Python; __post_init__ explicitly guards
        # against True/False being silently read as size=1/size=0 (the
        # kit's loud-refusal-on-accidental-bool convention, matched
        # elsewhere in this file's own fol/signature.py counterpart).
        with pytest.raises(ValueError, match="size"):
            FiniteDomainProblem((Atom("P", [X]),), True)

    def test_non_node_sentence_is_rejected(self):
        with pytest.raises(TypeError, match="Node"):
            FiniteDomainProblem((Atom("P", [X]), "not a formula"), 2)

    def test_signature_of_wrong_type_is_rejected(self):
        with pytest.raises(TypeError, match="Signature"):
            FiniteDomainProblem((Atom("P", [X]),), 2, signature="not a signature")

    def test_all_different_of_wrong_type_is_rejected(self):
        with pytest.raises(TypeError, match="all_different"):
            FiniteDomainProblem((Atom("P", [X]),), 2, all_different="not a bool")

    def test_all_different_true_is_accepted_and_recorded(self):
        problem = FiniteDomainProblem((Atom("P", [X]),), 2, all_different=True)
        assert problem.all_different is True


# =============================================================================
# fragment_check — the single allow/refuse gate
# =============================================================================

class TestFragmentCheckAccepts:
    """Every node type the module docstring's "Fragment boundary: IN" list
    names must pass with fragment_check(...) is None — checked individually
    so a future narrowing of the allow-list fails here, at the exact symbol,
    rather than surfacing as a mysterious UNKNOWN/"unsupported" three layers
    away in a backend."""

    def test_plain_atom(self):
        assert fragment_check([Atom("P", [X])]) is None

    def test_not_and_or_implies(self):
        f = Implies(And(Atom("P", [X]), Not(Atom("Q", [X]))), Or(Atom("R", [X]), Atom("S", [X])))
        assert fragment_check([f]) is None

    def test_contrast_is_encodable(self):
        # Contrast is truth-functionally And per its own docstring — the
        # module explicitly puts it IN the fragment despite it not being a
        # "classical" connective name.
        assert fragment_check([Contrast(Atom("P", [X]), Atom("Q", [X]))]) is None

    def test_quantifiers_unsorted(self):
        f = Quantifier("forall", X, Quantifier("exists", Y, Atom("R", [X, Y])))
        assert fragment_check([f]) is None

    def test_count(self):
        assert fragment_check([Count("ge", Number(2), X, Atom("P", [X]))]) is None

    def test_cardinality_inside_a_comparison(self):
        card = Cardinality(X, Atom("P", [X]))
        assert fragment_check([Atom(">", [card, Number(1)])]) is None

    def test_function_terms_are_refused_because_no_structure_can_hold_one(self):
        """A solver can happily find a model containing a function symbol —
        but ``FiniteStructure`` has fields ``domain``/``extensions``/
        ``computed``/``constants`` and no slot for a function interpretation,
        so that model could never be checked back with ``verify_model``. This
        layer does not hand out countermodels it cannot verify, so the gate
        refuses the fragment outright and says why, rather than letting the
        backend engage and fail late with an opaque infra error."""
        f = Atom("P", [Function("f", [Constant("a"), Variable("x")])])

        message = fragment_check([f])
        assert message is not None
        assert "Function" in message
        assert "FiniteStructure" in message

    def test_multiple_sentences_all_in_fragment(self):
        s1 = Atom("P", [Constant("a")])
        s2 = Quantifier("forall", X, Implies(Atom("P", [X]), Atom("Q", [X])))
        assert fragment_check([s1, s2]) is None


class TestFragmentCheckRefuses:
    """Every excluded family named in the module docstring, refused BY NAME
    (exact node-type name and the family's stated reason substring) —
    one representative member per family is enough to pin the family's own
    reason text; the family lists themselves are exercised structurally via
    _REJECTED_NODE_REASONS in the implementation, not duplicated here."""

    def test_measure(self):
        msg = fragment_check([Measure(Constant("a"), Constant("height"))])
        assert msg == (
            "Measure is not encodable: Measure denotes a degree on an "
            "uninterpreted ORDERED codomain, not a set to count — nothing "
            "for #count/sum to range over"
        )

    def test_sorted_family(self):
        f = SortedQuantifier("forall", X, "Human", Atom("P", [X]))
        msg = fragment_check([f])
        assert msg.startswith("SortedQuantifier is not encodable:")
        assert "per-sort subdomains" in msg

    def test_modal_family(self):
        msg = fragment_check([Box(Atom("P", []))])
        assert msg.startswith("Box is not encodable:")
        assert "POSSIBLE WORLDS" in msg

    def test_second_order(self):
        f = SecondOrderQuantifier("forall", "P", 1, Atom("P", [X]))
        msg = fragment_check([f])
        assert msg.startswith("SecondOrderQuantifier is not encodable:")
        assert "relations, not individuals" in msg

    def test_substructural_family(self):
        msg = fragment_check([Tensor(Atom("P", []), Atom("Q", []))])
        assert msg.startswith("Tensor is not encodable:")
        assert "RESOURCE USE" in msg

    def test_lambda_family(self):
        f = Lambda(LambdaVar("x"), Atom("P", [Variable("x")]))
        msg = fragment_check([f])
        assert msg.startswith("Lambda is not encodable:")
        assert "higher-order" in msg

    def test_team_semantic_family(self):
        msg = fragment_check([Dependence((X, Y))])
        assert msg.startswith("Dependence is not encodable:")
        assert "TEAM" in msg

    def test_fuzzy_family(self):
        msg = fragment_check([WeakConjunction(Atom("P", [X]), Atom("Q", [X]))])
        assert msg.startswith("WeakConjunction is not encodable:")
        assert "many-valued" in msg

    def test_unknown_future_node_type_gets_the_generic_reason(self):
        # A node type this module has never heard of (simulating a future
        # AST addition) must be refused by the documented default-deny
        # fallback, not silently accepted just because it is absent from
        # BOTH the allow-list and the named-reject table.
        @dataclass
        class _FutureNode(Node):
            formula: Node

        weird = _FutureNode(Atom("P", []))
        msg = fragment_check([weird])
        assert msg == (
            "_FutureNode is not encodable: not part of the "
            "unsorted-classical-FOL-plus-Count/Cardinality fragment these "
            "backends encode"
        )

    def test_disallowed_node_buried_under_an_allowed_one_is_still_caught(self):
        # Box nested two levels inside an otherwise entirely encodable And —
        # fragment_check walks EVERY descendant (Node.walk(), pre-order),
        # so this must not be missed just because the top-level connective
        # is fine.
        buried = And(Atom("P", [X]), Box(Atom("Q", [])))
        msg = fragment_check([buried])
        assert msg.startswith("Box is not encodable:")

    def test_reports_first_offender_in_sentence_order_then_preorder(self):
        # Two sentences: the FIRST is entirely in-fragment, the SECOND
        # starts with the offending node. Node.walk() yields a node itself
        # before its children (pre-order) and children in field-declaration
        # order, so within the second sentence Box (the sentence's own root)
        # is visited before Q even though Q is a plain Atom that would
        # otherwise pass.
        clean = Atom("P", [Constant("a")])
        offender_first = Box(Atom("Q", []))
        msg = fragment_check([clean, offender_first])
        assert msg.startswith("Box is not encodable:")

        # Symmetric check: put an allowed node ahead of Box WITHIN one
        # sentence — And(left=Atom, right=Box) — Box must still be the one
        # reported, and reported as Box (not e.g. And, which IS allowed).
        f = And(Atom("R", [X, Y]), Box(Atom("S", [])))
        msg2 = fragment_check([f])
        assert msg2.startswith("Box is not encodable:")

    def test_non_node_sentence_raises_type_error(self):
        with pytest.raises(TypeError, match="Node"):
            fragment_check(["not a formula"])


# =============================================================================
# structure_from_solution — the shared reconstruction
# =============================================================================

class TestStructureFromSolution:
    # Shared fixture signature for the round-trip test: P/1, R/2, a function
    # f/1 (total-relation encoding needs arity+1 = 2 args per atom), and a
    # constant a.
    _SIG = Signature(
        predicates={"P": PredicateDecl("P", 1), "R": PredicateDecl("R", 2)},
        functions={"f": FunctionDecl("f", 1)},
        constants={"a": ConstantDecl("a")},
    )

    def test_hand_derived_round_trip(self):
        # Domain size 3 -> individuals "0","1","2". Chosen solution, worked
        # out by hand into the expected FiniteStructure below:
        #   P = {0, 2}                         (2 true atoms)
        #   R = {(0,1), (1,2)}
        #   f: 0->1, 1->1, 2->0                (one atom per domain element,
        #                                        satisfying totality)
        #   a = 1
        atoms = [
            ("P", (0,)), ("P", (2,)),
            ("R", (0, 1)), ("R", (1, 2)),
            ("f", (0, 1)), ("f", (1, 1)), ("f", (2, 0)),
            ("a", (1,)),
        ]
        s = structure_from_solution(self._SIG, atoms, size=3)

        assert s.domain == ("0", "1", "2")
        # Predicate extension: individual indices stringified, order-free.
        assert s.extensions[("P", 1)] == {("0",), ("2",)}
        assert s.extensions[("R", 2)] == {("0", "1"), ("1", "2")}
        # Function stored as the arity+1 total relation (inputs, then result).
        assert s.extensions[("f", 2)] == {("0", "1"), ("1", "1"), ("2", "0")}
        assert s.constants == {"a": "1"}

    def test_predicate_with_zero_true_atoms_gets_an_empty_extension(self):
        # P/1 is declared but no atom mentions it: this must be a genuine
        # EMPTY relation (present in `extensions` as `set()`), never simply
        # absent — FiniteStructure.holds() reads "absent key" as
        # uninterpreted (KeyError), which would be a different, wrong
        # answer for a predicate the solver correctly decided is false
        # everywhere. f/g must still be given a total, functional graph for
        # every input, or the totality check below rejects the solution.
        sig = Signature(predicates={"P": PredicateDecl("P", 1)},
                        functions={"f": FunctionDecl("f", 1)})
        atoms = [("f", (0, 0)), ("f", (1, 0))]
        s = structure_from_solution(sig, atoms, size=2)
        assert s.extensions[("P", 1)] == set()

    def test_all_different_true_with_genuinely_distinct_constants_succeeds(self):
        sig = Signature(constants={"a": ConstantDecl("a"), "b": ConstantDecl("b")})
        atoms = [("a", (0,)), ("b", (1,))]
        s = structure_from_solution(sig, atoms, size=2, all_different=True)
        assert s.constants == {"a": "0", "b": "1"}

    def test_all_different_true_with_colliding_constants_is_rejected(self):
        sig = Signature(constants={"a": ConstantDecl("a"), "b": ConstantDecl("b")})
        atoms = [("a", (0,)), ("b", (0,))]  # both denote the SAME individual
        with pytest.raises(ValueError, match="all_different"):
            structure_from_solution(sig, atoms, size=2, all_different=True)

    def test_all_different_false_default_permits_the_same_collision(self):
        # The identical colliding solution as above is perfectly legal when
        # all_different is not requested — this is the flag doing its job,
        # not an inconsistency.
        sig = Signature(constants={"a": ConstantDecl("a"), "b": ConstantDecl("b")})
        atoms = [("a", (0,)), ("b", (0,))]
        s = structure_from_solution(sig, atoms, size=2, all_different=False)
        assert s.constants == {"a": "0", "b": "0"}

    def test_function_functionality_violation_is_rejected(self):
        # f(0) is claimed to be BOTH 1 and 2 — a solver/encoding bug the
        # reconstruction must catch, not silently pick one.
        sig = Signature(functions={"f": FunctionDecl("f", 1)})
        atoms = [("f", (0, 1)), ("f", (0, 2))]
        with pytest.raises(ValueError, match="functionality violated"):
            structure_from_solution(sig, atoms, size=3)

    def test_function_totality_violation_is_rejected(self):
        # Domain {0,1}, f/1 needs a result for BOTH inputs; only f(0) is
        # supplied, so f(1) is silently missing -- the total-relation
        # reconstruction must refuse this rather than hand back a partial
        # function.
        sig = Signature(functions={"f": FunctionDecl("f", 1)})
        atoms = [("f", (0, 1))]
        with pytest.raises(ValueError, match="totality violated"):
            structure_from_solution(sig, atoms, size=2)

    def test_constant_functionality_violation_is_rejected(self):
        sig = Signature(constants={"a": ConstantDecl("a")})
        atoms = [("a", (0,)), ("a", (1,))]  # a claimed to denote both 0 and 1
        with pytest.raises(ValueError, match="functionality violated"):
            structure_from_solution(sig, atoms, size=2)

    def test_constant_never_assigned_is_rejected(self):
        sig = Signature(constants={"a": ConstantDecl("a")})
        with pytest.raises(ValueError, match="never assigned"):
            structure_from_solution(sig, [], size=1)

    def test_unknown_symbol_is_rejected(self):
        # "Q" is not declared as a predicate, function, or constant in the
        # signature -- a leaked helper atom (or a genuine solver/encoder
        # bug) must surface loudly here, per the function's own docstring.
        sig = Signature(predicates={"P": PredicateDecl("P", 1)})
        with pytest.raises(ValueError, match="does not declare"):
            structure_from_solution(sig, [("Q", (0,))], size=1)

    def test_predicate_arity_mismatch_is_rejected(self):
        sig = Signature(predicates={"P": PredicateDecl("P", 1)})
        with pytest.raises(ValueError, match="arity"):
            structure_from_solution(sig, [("P", (0, 1))], size=2)

    def test_function_arity_mismatch_is_rejected(self):
        # f/1's total-relation atoms need exactly 2 entries (1 input + 1
        # result); a 3-tuple is wrong regardless of what it would mean.
        sig = Signature(functions={"f": FunctionDecl("f", 1)})
        with pytest.raises(ValueError, match="arity"):
            structure_from_solution(sig, [("f", (0, 1, 1))], size=2)

    def test_constant_arity_mismatch_is_rejected(self):
        sig = Signature(constants={"a": ConstantDecl("a")})
        with pytest.raises(ValueError, match="exactly one individual"):
            structure_from_solution(sig, [("a", (0, 1))], size=2)

    def test_out_of_range_individual_index_is_rejected(self):
        sig = Signature(predicates={"P": PredicateDecl("P", 1)})
        with pytest.raises(ValueError, match="outside the domain"):
            structure_from_solution(sig, [("P", (5,))], size=2)

    def test_non_int_individual_index_is_rejected(self):
        # bool is an int subclass -- explicitly excluded (matching
        # FiniteDomainProblem's own size check) so a stray True/False from a
        # solver output can never be silently read as the index 1/0.
        sig = Signature(predicates={"P": PredicateDecl("P", 1)})
        with pytest.raises(TypeError, match="non-int"):
            structure_from_solution(sig, [("P", (True,))], size=2)

    def test_size_below_one_is_rejected(self):
        sig = Signature(predicates={"P": PredicateDecl("P", 1)})
        with pytest.raises(ValueError, match="size"):
            structure_from_solution(sig, [], size=0)

    def test_signature_of_wrong_type_is_rejected(self):
        with pytest.raises(TypeError, match="Signature"):
            structure_from_solution("not a signature", [], size=1)


# =============================================================================
# verify_model — the safety net
# =============================================================================

class TestVerifyModel:
    def test_structure_that_genuinely_satisfies_the_sentence_verifies_clean(self):
        # Domain {0,1}, P true only at 0: ∃x P(x) genuinely holds here.
        s = FiniteStructure(domain=("0", "1"), extensions={("P", 1): {("0",)}})
        sentence = Quantifier("exists", X, Atom("P", [X]))
        assert verify_model(s, [sentence]) is None

    def test_wrong_structure_built_deliberately_is_caught(self):
        # Deliberately WRONG countermodel, built by hand (not a solver
        # output): the sentence claims P holds of EVERY individual, but this
        # structure makes P false at "1" -- ∀x P(x) does NOT hold here, and
        # verify_model must say so rather than silently accepting it.
        wrong = FiniteStructure(domain=("0", "1"), extensions={("P", 1): {("0",)}})
        sentence = Quantifier("forall", X, Atom("P", [X]))
        message = verify_model(wrong, [sentence])
        assert message is not None
        assert "does not hold" in message

    def test_first_failing_sentence_in_order_is_the_one_named(self):
        # Two sentences: the first genuinely holds, the second does not --
        # the reported failure must be the SECOND one (order matters: a
        # verifier that reported the wrong sentence would misdirect a
        # caller trying to debug an encoder).
        s = FiniteStructure(domain=("0", "1"), extensions={("P", 1): {("0",)}})
        holds_sentence = Quantifier("exists", X, Atom("P", [X]))
        fails_sentence = Quantifier("forall", X, Atom("P", [X]))
        message = verify_model(s, [holds_sentence, fails_sentence])
        assert message is not None
        assert "does not hold" in message

    def test_uninterpreted_symbol_downgrades_to_could_not_verify(self):
        # The sentence mentions "Q", which this structure has no
        # interpretation for at all -- a vocabulary mismatch, not a false
        # sentence, so the message must read as "could not verify", never
        # as "does not hold" (which would misleadingly imply the checker
        # actually evaluated it to False).
        s = FiniteStructure(domain=("0",), extensions={("P", 1): {("0",)}})
        sentence = Atom("Q", [Constant("a")])
        s_with_a = FiniteStructure(domain=("0",), extensions={("P", 1): {("0",)}},
                                   constants={"a": "0"})
        message = verify_model(s_with_a, [sentence])
        assert message is not None
        assert "could not verify" in message

    def test_cardinality_is_verified_not_waved_through(self):
        """The counting fragment is the reason these backends exist, so it is
        the one fragment ``verify_model`` must actually be able to check — a
        solver that decides a cardinality comparison is worthless if the kit
        cannot confirm the model it hands back.

        Hand-derived: the domain is two individuals and ``P`` holds of exactly
        one of them, so ``|{x : P(x)}| = 1`` is TRUE here and ``= 2`` is
        FALSE. Both directions are pinned: a checker that returned "verified"
        for everything would pass the first assertion alone."""
        s = FiniteStructure(domain=("0", "1"), extensions={("P", 1): {("0",)}})

        holds = Atom("=", [Cardinality(X, Atom("P", [X])), Number(1)])
        assert verify_model(s, [holds]) is None

        fails = Atom("=", [Cardinality(X, Atom("P", [X])), Number(2)])
        message = verify_model(s, [fails])
        assert message is not None
        assert "could not verify" not in message      # refuted, not unevaluable

    def test_function_term_hits_the_documented_gap(self):
        # A FiniteStructure interprets predicates, not functions (see
        # semantics/model_eval.py's own docstring) -- P(f(a)) must degrade
        # to "could not verify", not silently pass or fail.
        s = FiniteStructure(domain=("0", "1"), extensions={("P", 1): {("0",)}},
                            constants={"a": "0"})
        sentence = Atom("P", [Function("f", [Constant("a")])])
        message = verify_model(s, [sentence])
        assert message is not None
        assert "could not verify" in message
        assert "Function" in message

    def test_contrast_is_verified_as_the_conjunction_it_is(self):
        """``Contrast`` was the last node the gate admitted but the checker
        could not evaluate. It is truth-functionally ``And`` — concession is a
        discourse relation, and the node's own docstring says every export
        treats it as ``∧`` — so evaluating it as conjunction restores an
        omission rather than inventing a semantics.

        Hand-derived over a one-element domain where ``P`` holds and ``Q``
        does not: ``P Ⓒ P`` is true, ``P Ⓒ Q`` is false. Both directions are
        pinned, so a checker that waved everything through would still fail
        the second."""
        a = Constant("a")
        s = FiniteStructure(domain=("0",),
                            extensions={("P", 1): {("0",)}, ("Q", 1): set()},
                            constants={"a": "0"})

        assert verify_model(s, [Contrast(Atom("P", [a]), Atom("P", [a]))]) is None

        message = verify_model(s, [Contrast(Atom("P", [a]), Atom("Q", [a]))])
        assert message is not None
        assert "could not verify" not in message      # refuted, not unevaluable

    def test_comparing_an_individual_with_a_number_is_still_refused(self):
        """``∀x (x = 1)`` compares a domain individual with a numeral. The
        evaluator now reads a comparison numerically as soon as one operand is
        numeric — but a ``Variable`` denotes an opaque domain individual, not a
        number, so the pair has no reading and must be refused.

        This is the boundary of the counting support: admitting numeric terms
        in COMPARISONS is not the same as admitting them everywhere, and a
        structure whose individuals happen to be named ``"0"``/``"1"`` must not
        tempt anyone into reading those names as integers."""
        s = FiniteStructure(domain=("0", "1"), extensions={})
        sentence = Quantifier("forall", X, Atom("=", [X, Number(1)]))

        message = verify_model(s, [sentence])
        assert message is not None
        assert "could not verify" in message
        assert "does not denote a number" in message

    def test_empty_sentences_verifies_vacuously(self):
        # No sentences to check -> nothing can fail -> None. (verify_model
        # itself has no non-empty precondition, unlike FiniteDomainProblem;
        # this pins that it does not error out on an empty iterable.)
        s = FiniteStructure(domain=("0",), extensions={})
        assert verify_model(s, []) is None
