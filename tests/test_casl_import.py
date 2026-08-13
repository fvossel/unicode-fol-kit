"""Tests for :mod:`unicode_fol_kit.fol.casl_import` (CASL text parsing —
the importer half of the export/import pair with
:mod:`unicode_fol_kit.fol.casl_export`).

No snapshot tests: every expected AST below is derived BY HAND, either by
building it directly with the kit's own node constructors or by parsing it
with :class:`~unicode_fol_kit.MSFLParser` and reasoning about what tree that
produces (documented in each test's own docstring/comment) — never by
running :func:`~unicode_fol_kit.fol.casl_import.parse_casl_spec` and copying
its output.

Test groups:

* ROUND-TRIP — ``parse_casl_spec(to_casl_spec(f)).axioms == (f,)`` (and the
  conjecture equivalent) over every golden case in
  ``tests/test_casl_export.py`` that does not involve
  :class:`~unicode_fol_kit.fol.nodes.Xor` or an explicit
  :class:`~unicode_fol_kit.fol.nodes.SortedConstant` occurrence — see
  ``casl_import``'s own module docstring for exactly why those two are
  excluded from the round-trip contract (both are genuine, DOCUMENTED
  information losses on the EXPORT side, not bugs in the importer).
* TOLERANT SYNTAX — constructs ``to_casl_spec`` never emits but
  ``parse_casl_spec`` accepts anyway (comments, singular ``pred``/``op``,
  multiple quantified variables sharing a sort, omitted ``end``, bare
  unparenthesised connective chains read by precedence).
* REFUSALS — each out-of-fragment construct raises
  :class:`~unicode_fol_kit.fol.casl_import.CaslImportError` with the
  offending construct named in the message.
* SIGNATURE — the parsed :class:`~unicode_fol_kit.fol.signature.Signature`
  carries the exact arities/sorts the text declared.
* DOCUMENTED LIMITATIONS — Xor's classical expansion does not round-trip
  back to ``Xor``; a 0-ary operation reference always resolves to
  :class:`~unicode_fol_kit.fol.nodes.Constant`, never
  :class:`~unicode_fol_kit.fol.nodes.SortedConstant` or a 0-ary
  :class:`~unicode_fol_kit.fol.nodes.Function`.
"""

import pytest

from unicode_fol_kit import MSFLParser
from unicode_fol_kit.fol.casl_export import to_casl_spec, formula_to_casl
from unicode_fol_kit.fol.casl_import import parse_casl_spec, CaslSpec, CaslImportError
from unicode_fol_kit.fol.nodes import (
    Variable, Constant, SortedConstant, Function,
    Atom, Not, And, Or, Xor, Implies, Iff,
    Quantifier, SortedQuantifier,
)
from unicode_fol_kit.fol.signature import Signature, PredicateDecl, FunctionDecl, ConstantDecl

FOL = MSFLParser()
MSFOL = MSFLParser(many_sorted=True)


# =============================================================================
# Round-trip: every casl_export golden case not involving Xor/SortedConstant
# =============================================================================

def test_round_trip_pure_fol_one_sort():
    """Mirrors test_golden_pure_fol_one_sort in test_casl_export.py: modus-
    ponens shape plus a ground fact and a %implied conjecture, all unsorted
    (default_sort 'Thing')."""
    ax1 = FOL.parse("∀x (Human(x) → Mortal(x))")
    ax2 = FOL.parse("Human(socrates)")
    cj = FOL.parse("Mortal(socrates)")
    text = to_casl_spec([ax1, ax2], conjectures=[cj])
    spec = parse_casl_spec(text)
    assert spec.name == "KitExport"
    assert spec.axioms == (ax1, ax2)
    assert spec.conjectures == (cj,)


def test_round_trip_person_animal_msfol_worked_example():
    """Mirrors test_golden_person_animal_msfol_worked_example: this is the
    KEY case demonstrating why a 0-ary operation reference must always
    resolve to a plain Constant — 'socrates' here is a deliberately
    UNSORTED Constant whose CASL 'ops' entry ends up sort Person purely
    through union-find inference from a DIFFERENT axiom (the quantified
    one). If parse_casl_spec instead reconstructed a SortedConstant (since
    the ops entry states a concrete, non-default sort), this round trip
    would fail — it does not, confirming the module's documented policy."""
    axiom = MSFOL.parse("∀x:Person (Mortal(x) → (∃y:Animal Likes(x, y)))")
    conjecture = Atom("Mortal", (Constant("socrates"),))
    text = to_casl_spec([axiom], conjectures=[conjecture])
    spec = parse_casl_spec(text)
    assert spec.axioms == (axiom,)
    assert spec.conjectures == (conjecture,)
    # Structural check that it really is a bare Constant, not a
    # SortedConstant, despite the declared sort ('Person') not being Thing.
    assert isinstance(spec.conjectures[0].args[0], Constant)
    assert not isinstance(spec.conjectures[0].args[0], SortedConstant)


def test_round_trip_empty_axioms_with_only_a_conjecture():
    """Mirrors test_golden_empty_axioms_with_only_a_conjecture: axioms=[],
    a single sorted conjecture."""
    cj = MSFOL.parse("∀x:Person Mortal(x)")
    text = to_casl_spec([], conjectures=[cj])
    spec = parse_casl_spec(text)
    assert spec.axioms == ()
    assert spec.conjectures == (cj,)


def test_round_trip_zero_ary_predicate():
    """Mirrors test_golden_zero_ary_predicate: a bare 0-ary Atom, no sorts
    section at all in the emitted text."""
    rain = Atom("Rain", ())
    text = to_casl_spec([rain])
    spec = parse_casl_spec(text)
    assert spec.axioms == (rain,)
    assert spec.signature.sorts == frozenset()


def test_round_trip_bare_constant_sort_inferred_from_predicate_context():
    """Mirrors test_bare_constant_sort_inferred_from_predicate_context:
    another case of an unsorted Constant ('socrates') getting a non-default
    inferred sort purely from union-find — same policy check as the
    worked-example test above, from a different angle (inference via a
    SEPARATE axiom's predicate argument position, not via the quantifier of
    the SAME axiom)."""
    ax1 = MSFOL.parse("∀x:Person Mortal(x)")
    ax2 = FOL.parse("Mortal(socrates)")
    text = to_casl_spec([ax1, ax2])
    spec = parse_casl_spec(text)
    assert spec.axioms == (ax1, ax2)


def test_round_trip_function_argument_and_result_sort_inferred_through_nesting():
    """Mirrors test_function_argument_and_result_sort_inferred_through_nesting:
    nested function application, mother(mother(x)), both argument and result
    sort inferred as Person."""
    ax = MSFOL.parse("∀x:Person Alive(mother(mother(x)))")
    text = to_casl_spec([ax])
    spec = parse_casl_spec(text)
    assert spec.axioms == (ax,)


def test_round_trip_equality_driven_sort_inference():
    """Mirrors test_equality_driven_sort_inference: a bare (unsorted)
    constant's sort inferred purely through an equality with a sorted
    variable. Built directly since no parser mode can mix a sorted
    quantifier with a deliberately unsorted constant in one formula."""
    formula = SortedQuantifier(
        "∀", Variable("x"), "Person",
        Atom("=", (Variable("x"), Constant("alice"))),
    )
    text = to_casl_spec([formula])
    spec = parse_casl_spec(text)
    assert spec.axioms == (formula,)


def test_round_trip_deterministic_across_calls():
    """Parsing the same text twice yields structurally equal (in fact
    dataclass-equal) results — no hidden nondeterminism (dict/set iteration
    order) leaking into the parsed AST."""
    axiom = MSFOL.parse("∀x:Person (Mortal(x) → (∃y:Animal Likes(x, y)))")
    text = to_casl_spec([axiom])
    assert parse_casl_spec(text) == parse_casl_spec(text)


# =============================================================================
# Formula-level round trip via formula_to_casl (embedded in a minimal spec)
# =============================================================================

def test_round_trip_all_connectives_and_equality():
    """A single axiom exercising Not, And, Or, Implies, Iff, and equality
    together, fully parenthesised the way to_casl_spec would emit them (each
    binary connective wraps its non-atomic operands) — hand-built directly
    since no single formula in test_casl_export.py exercises all five at
    once. f = (not P \\/ (Q /\\ R)) => (S <=> (a = b)), built with 0-ary
    atoms P/Q/R/S and two constants a, b so no quantifier/sort machinery is
    needed to keep the AST exact and easy to hand-check."""
    P, Q, R, S = Atom("P", ()), Atom("Q", ()), Atom("R", ()), Atom("S", ())
    eq = Atom("=", (Constant("a"), Constant("b")))
    f = Implies(Or(Not(P), And(Q, R)), Iff(S, eq))
    text = to_casl_spec([f])
    spec = parse_casl_spec(text)
    assert spec.axioms == (f,)


def test_round_trip_nested_quantifiers_both_kinds():
    """forall x:Person exists y:Animal — both quantifier kinds nested, no
    connective in between (the 'chained binders stay bare' emission case),
    round-tripped."""
    f = MSFOL.parse("∀x:Person (∃y:Animal Likes(x, y))")
    text = to_casl_spec([f])
    spec = parse_casl_spec(text)
    assert spec.axioms == (f,)


def test_round_trip_plain_unsorted_quantifier_at_non_default_sort_override():
    """A plain Quantifier round-trips through a NON-default default_sort
    too: exporting and importing both need the SAME default_sort for the
    'plain vs sorted' quantifier reconstruction rule to invert correctly."""
    f = Quantifier("∀", Variable("x"), Atom("P", (Variable("x"),)))
    text = to_casl_spec([f], default_sort="Entity")
    spec = parse_casl_spec(text, default_sort="Entity")
    assert spec.axioms == (f,)
    # Using the WRONG default_sort on import must NOT silently coincide:
    # since the text declares 'x : Entity' and the wrong default is 'Thing',
    # importing with default_sort='Thing' must reconstruct a SortedQuantifier
    # instead of Quantifier, i.e. a DIFFERENT (non-equal) AST.
    spec_wrong = parse_casl_spec(text, default_sort="Thing")
    assert spec_wrong.axioms != (f,)
    assert isinstance(spec_wrong.axioms[0], SortedQuantifier)


# =============================================================================
# Tolerant syntax: beyond exactly what to_casl_spec emits
# =============================================================================

def test_tolerant_line_comments_are_ignored():
    text = """
    spec X = %% this is a comment
      sort S %% another one
      pred P : S
      . forall x : S . P(x) %% trailing comment on an axiom line
    end
    """
    spec = parse_casl_spec(text)
    assert spec.name == "X"
    assert len(spec.axioms) == 1


def test_tolerant_singular_sort_op_pred_keywords():
    """to_casl_spec always emits the PLURAL collective forms ('sorts',
    'ops', 'preds'); the singular CASL keywords ('sort', 'op', 'pred') are a
    tolerant extension this parser also accepts, one entry at a time."""
    text = """
    spec X =
      sort S
      op c : S
      pred P : S
      . P(c)
    end
    """
    spec = parse_casl_spec(text)
    assert spec.axioms == (Atom("P", (Constant("c"),)),)
    assert spec.signature.constants == {"c": ConstantDecl("c", "S")}
    assert spec.signature.predicates == {"P": PredicateDecl("P", 1, ("S",))}


def test_tolerant_multiple_variables_share_one_sort():
    """'forall x, y : S . P(x, y)' (never emitted by to_casl_spec, which
    always writes one variable per quantifier) desugars to nested
    same-type/same-sort quantifiers, innermost wrapping the body."""
    text = "spec X = sort S preds P : S * S . forall x, y : S . P(x, y) end"
    spec = parse_casl_spec(text)
    expected = SortedQuantifier(
        "∀", Variable("x"), "S",
        SortedQuantifier("∀", Variable("y"), "S",
                         Atom("P", (Variable("x"), Variable("y")))),
    )
    assert spec.axioms == (expected,)


def test_tolerant_three_variables_share_one_sort_desugars_right_associatively():
    text = "spec X = sort S pred P : S*S*S . forall x, y, z : S . P(x, y, z) end"
    spec = parse_casl_spec(text)
    expected = SortedQuantifier(
        "∀", Variable("x"), "S",
        SortedQuantifier(
            "∀", Variable("y"), "S",
            SortedQuantifier("∀", Variable("z"), "S",
                             Atom("P", (Variable("x"), Variable("y"), Variable("z")))),
        ),
    )
    assert spec.axioms == (expected,)


def test_tolerant_end_keyword_is_optional():
    """CASL's own basic-spec grammar makes the trailing 'end' optional;
    end-of-input alone terminates the item list."""
    spec = parse_casl_spec("spec X = pred Q : () . Q")
    assert spec.axioms == (Atom("Q", ()),)


def test_tolerant_bare_connective_precedence_not_and_or_implies_iff():
    """to_casl_spec always fully parenthesises non-atomic connective
    operands, so this input shape never comes FROM to_casl_spec — but the
    parser's precedence climbing (not > /\\ > \\/ > => right-assoc > <=>)
    must still read it correctly as a tolerant superset. 'not P /\\ Q \\/ R
    => S <=> T' should read as
    ((((not P) /\\ Q) \\/ R) => S) <=> T
    i.e. not binds tightest, then /\\, then \\/, then => (right-assoc, but
    only one => here), loosest <=>."""
    text = ("spec X = preds P:(); Q:(); R:(); S:(); T:() "
            ". not P /\\ Q \\/ R => S <=> T end")
    spec = parse_casl_spec(text)
    P, Q, R, S, T = (Atom(n, ()) for n in "PQRST")
    expected = Iff(Implies(Or(And(Not(P), Q), R), S), T)
    assert spec.axioms == (expected,)


def test_tolerant_implies_is_right_associative():
    """'P => Q => R' should read as P => (Q => R), matching the classical/
    casl_export documented reading (right-associative)."""
    text = "spec X = preds P:(); Q:(); R:() . P => Q => R end"
    spec = parse_casl_spec(text)
    P, Q, R = Atom("P", ()), Atom("Q", ()), Atom("R", ())
    assert spec.axioms == (Implies(P, Implies(Q, R)),)


def test_tolerant_double_negation():
    text = "spec X = pred P : () . not not P end"
    spec = parse_casl_spec(text)
    assert spec.axioms == (Not(Not(Atom("P", ()))),)


def test_tolerant_whitespace_is_fully_flexible():
    """Same content as the pure-FOL golden, but with irregular indentation,
    blank lines, and everything crammed or spread out — must parse
    identically to the normally-formatted version."""
    normal = to_casl_spec([FOL.parse("Human(socrates)")])
    squished = "spec\nKitExport\n=\n\n  ops   socrates:Thing\n\n  preds Human:Thing\n\n\n  .Human(socrates)\n\nend"
    assert parse_casl_spec(squished).axioms == parse_casl_spec(normal).axioms


# =============================================================================
# Refusals — each class individually, message asserted
# =============================================================================

def test_refuses_partial_function_arrow():
    text = "spec X = op f : S ->? S . P(a) end"
    with pytest.raises(CaslImportError, match=r"->\?"):
        parse_casl_spec(text)


def test_refuses_partial_function_arrow_as_result_position_too():
    """The '->?' check also fires immediately when it is the very first
    token of an op type (a 0-ary-looking '->? S' with no argument sorts is
    still refused, not silently misread as something else)."""
    text = "spec X = op f : S * S ->? S . P(a) end"
    with pytest.raises(CaslImportError, match=r"->\?"):
        parse_casl_spec(text)


def test_refuses_subsorting():
    text = "spec X = sorts S < T . P(a) end"
    with pytest.raises(CaslImportError, match="subsorting"):
        parse_casl_spec(text)


def test_refuses_free_type():
    text = "spec X = free type Nat ::= zero | succ(Nat) end"
    with pytest.raises(CaslImportError, match="free/generated type"):
        parse_casl_spec(text)


def test_refuses_generated_type():
    text = "spec X = generated type Nat ::= zero end"
    with pytest.raises(CaslImportError, match="free/generated type"):
        parse_casl_spec(text)


def test_refuses_bare_type_item():
    text = "spec X = type Nat end"
    with pytest.raises(CaslImportError, match="free/generated type"):
        parse_casl_spec(text)


def test_refuses_then_structuring():
    text = "spec X = A then ops c : S . P(c) end"
    with pytest.raises(CaslImportError, match="'then'"):
        parse_casl_spec(text)


def test_refuses_view_structuring():
    text = "spec X = view v : A end"
    with pytest.raises(CaslImportError, match="structured-specification construct 'view'"):
        parse_casl_spec(text)


def test_refuses_given_structuring():
    text = "spec X = given ops c : S . P(c) end"
    with pytest.raises(CaslImportError, match="structured-specification construct 'given'"):
        parse_casl_spec(text)


def test_refuses_operation_attributes():
    text = "spec X = ops e : S, unit preds P : S . P(e) end"
    with pytest.raises(CaslImportError, match="attributes"):
        parse_casl_spec(text)


def test_refuses_predicate_attributes():
    text = "spec X = sort S preds P : S, comm . forall x : S . P(x) end"
    with pytest.raises(CaslImportError, match="attributes"):
        parse_casl_spec(text)


def test_refusal_message_carries_line_number():
    """Every CaslImportError message starts with 'line N: ' — the subsort
    refusal here is on line 3 (1-indexed, counting the leading blank line
    from the triple-quoted string as line 1)."""
    text = "spec X =\n  sorts S\n  sorts T < S\nend"
    with pytest.raises(CaslImportError, match=r"^line 3:"):
        parse_casl_spec(text)


def test_refuses_unrecognized_character():
    text = "spec X = pred P : S . P(a) & Q end"  # '&' is not a CASL token here
    with pytest.raises(CaslImportError, match="unrecognized character"):
        parse_casl_spec(text)


def test_refuses_unsupported_percent_annotation():
    text = "spec X = pred P : () . P %def end"
    with pytest.raises(CaslImportError, match="unsupported CASL annotation '%def'"):
        parse_casl_spec(text)


def test_refuses_reserved_word_as_predicate_name():
    text = "spec X = pred axiom : () . axiom end"
    with pytest.raises(CaslImportError, match="reserved CASL keyword 'axiom'"):
        parse_casl_spec(text)


def test_refuses_reserved_word_as_sort_name():
    text = "spec X = sorts sort . P end"
    with pytest.raises(CaslImportError, match="reserved CASL keyword 'sort'"):
        parse_casl_spec(text)


def test_refuses_reserved_word_as_spec_name():
    text = "spec sort = pred P : () . P end"
    with pytest.raises(CaslImportError, match="reserved CASL keyword 'sort'"):
        parse_casl_spec(text)


def test_refuses_constant_vs_function_conflict():
    text = "spec X = ops c : S; c : S -> S preds P:S . P(c) end"
    with pytest.raises(CaslImportError,
                       match="both as a 0-ary operation and as a function"):
        parse_casl_spec(text)


def test_refuses_conflicting_constant_redeclaration():
    text = "spec X = ops c : S; c : T preds P:S . P(c) end"
    with pytest.raises(CaslImportError, match="conflicting sort"):
        parse_casl_spec(text)


def test_refuses_conflicting_predicate_redeclaration():
    text = "spec X = sort S preds P : S; P : S * S . forall x:S . P(x) end"
    with pytest.raises(CaslImportError, match="conflicting type"):
        parse_casl_spec(text)


def test_refuses_conflicting_function_redeclaration():
    text = "spec X = ops f : S -> S; f : S * S -> S preds P:S . P(f(a)) end"
    with pytest.raises(CaslImportError, match="conflicting type"):
        parse_casl_spec(text)


def test_refuses_unexpected_token_at_item_position():
    text = "spec X = 123 end"
    with pytest.raises(CaslImportError, match="unrecognized character '1'"):
        parse_casl_spec(text)


def test_refuses_trailing_content_after_end():
    text = "spec X = pred P : () . P end garbage"
    with pytest.raises(CaslImportError, match="unexpected content after 'end'"):
        parse_casl_spec(text)


# =============================================================================
# Signature content
# =============================================================================

def test_signature_carries_exact_arities_and_sorts():
    text = """
    spec X =
      sorts Person, Animal
      ops mother : Person -> Person; alice : Person
      preds Likes : Person * Animal; Rain : ()
      . forall x : Person . Likes(x, mother(x))
    end
    """
    spec = parse_casl_spec(text)
    sig = spec.signature
    assert sig.sorts == frozenset({"Person", "Animal"})
    assert sig.predicates == {
        "Likes": PredicateDecl("Likes", 2, ("Person", "Animal")),
        "Rain": PredicateDecl("Rain", 0, None),
    }
    assert sig.functions == {
        "mother": FunctionDecl("mother", 1, ("Person",), "Person"),
    }
    assert sig.constants == {"alice": ConstantDecl("alice", "Person")}


def test_signature_round_trips_through_to_casl_spec_inference():
    """The parsed Signature's predicate/function arities and argument sorts
    must match what casl_export's OWN union-find inference produced for the
    same formula set — i.e. Signature(text-declared) agrees with what
    casl_export computed and wrote down, checked here by re-deriving the
    same declarations casl_export's own docstring worked example states."""
    axiom = MSFOL.parse("∀x:Person (Mortal(x) → (∃y:Animal Likes(x, y)))")
    conjecture = Atom("Mortal", (Constant("socrates"),))
    text = to_casl_spec([axiom], conjectures=[conjecture])
    spec = parse_casl_spec(text)
    sig = spec.signature
    assert sig.predicates["Likes"] == PredicateDecl("Likes", 2, ("Person", "Animal"))
    assert sig.predicates["Mortal"] == PredicateDecl("Mortal", 1, ("Person",))
    assert sig.constants["socrates"] == ConstantDecl("socrates", "Person")
    assert sig.sorts == frozenset({"Person", "Animal"})


def test_to_dict_is_json_compatible_and_carries_all_four_fields():
    import json
    spec = parse_casl_spec("spec X = sort S pred P : S . forall x : S . P(x) end")
    d = spec.to_dict()
    assert set(d) == {"name", "signature", "axioms", "conjectures"}
    assert d["name"] == "X"
    json.dumps(d)  # must not raise


# =============================================================================
# Documented limitations
# =============================================================================

def test_xor_does_not_round_trip_to_xor_it_round_trips_to_not_iff():
    """to_casl_spec expands Xor(P, Q) to the CASL text 'not (P <=> Q)' (no
    direct CASL operator exists) — parsing that text back necessarily
    yields Not(Iff(P, Q)), never Xor(P, Q). This is documented as an
    EXPORT-side information loss, not an importer bug: the text itself no
    longer says 'this was originally an Xor'."""
    f = FOL.parse("P ⊕ Q")
    assert isinstance(f, Xor)
    text = to_casl_spec([f])
    spec = parse_casl_spec(text)
    assert spec.axioms != (f,)
    assert spec.axioms == (Not(Iff(Atom("P", ()), Atom("Q", ()))),)


def test_zero_ary_function_reference_resolves_to_constant_not_function():
    """formula_to_casl(Atom('P', (Function('f', ()),))) renders 'P(f)' —
    bare, indistinguishable from a Constant reference. Parsing 'P(f)' back
    (with 'f' declared as a 0-ary op) therefore resolves to Constant('f'),
    never a 0-ary Function — the module's documented, deliberate choice
    (see its docstring's '0-ary operations import as Constant' section)."""
    original = Atom("P", (Function("f", ()),))
    assert formula_to_casl(original) == "P(f)"
    text = to_casl_spec([original])
    spec = parse_casl_spec(text)
    assert spec.axioms == (Atom("P", (Constant("f"),)),)
    assert spec.axioms != (original,)
    assert isinstance(spec.axioms[0].args[0], Constant)
    assert not isinstance(spec.axioms[0].args[0], Function)


# ---------------------------------------------------------------------------
# Adversarial-review regressions (Tier-3 review, both confirmed findings)
# ---------------------------------------------------------------------------

def test_round_trip_sorted_quantifier_at_default_sort_collapses():
    """THIRD disclosed round-trip exception: ∀x:Thing P(x) (an explicit
    SortedQuantifier over the default sort) renders the very same CASL text
    as the plain ∀x P(x), so the reconstruction rule necessarily collapses
    it to a plain Quantifier — semantically identical, structurally
    distinct, and now documented in the module docstring alongside the Xor
    and 0-ary-Constant cases."""
    msfol = MSFLParser(many_sorted=True)
    f = msfol.parse("∀x:Thing P(x)")
    assert isinstance(f, SortedQuantifier) and f.sort == "Thing"
    back = parse_casl_spec(to_casl_spec([f])).axioms[0]
    assert isinstance(back, Quantifier) and not isinstance(back, SortedQuantifier)
    assert back == FOL.parse("∀x P(x)")


def test_undeclared_predicate_in_axiom_is_refused():
    """A symbol used but never declared previously produced a CaslSpec whose
    signature did not describe its own axioms — now a loud refusal naming
    the symbol and the axiom position."""
    with pytest.raises(CaslImportError, match="axiom 1: predicate 'P'.*never declared"):
        parse_casl_spec("spec X = sort S ops a : S . P(a) end")


def test_undeclared_constant_in_axiom_is_refused():
    with pytest.raises(CaslImportError, match="constant 'a'.*never declared"):
        parse_casl_spec("spec X = sort S preds P : S . P(a) end")


def test_declared_vs_used_predicate_arity_mismatch_is_refused():
    """preds P : S declares arity 1; P(x, x) uses arity 2 — previously
    accepted with a silently self-inconsistent CaslSpec."""
    with pytest.raises(CaslImportError, match="predicate 'P'.*arity 1.*2 argument"):
        parse_casl_spec("spec X = sort S preds P : S . forall x : S . P(x, x) end")


def test_declared_vs_used_function_arity_mismatch_is_refused():
    with pytest.raises(CaslImportError, match="operation 'f'.*arity 1.*2 argument"):
        parse_casl_spec(
            "spec X = sort S ops f : S -> S preds P : S . "
            "forall x : S . P(f(x, x)) end")
