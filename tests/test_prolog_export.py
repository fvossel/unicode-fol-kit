"""Tests for :mod:`unicode_logic_kit.fol.prolog_export`.

Every positive case round-trips against
:func:`~unicode_logic_kit.fol.prolog_input.parse_prolog_clause` — the SECOND,
already hand-checked route the module docstring names as the oracle — through
two independent checks: structural equality up to alpha-renaming
(:func:`~unicode_logic_kit.eval.canonical.canonicalize`), and a full semantic
equivalence proof against the kit's own resolution prover, in
mutual-entailment form (``prove([node], reparsed) and prove([reparsed],
node)`` — see :func:`_mutually_entail` for why that form is used instead of
the equivalent single ``is_valid_resolution(Iff(node, reparsed))`` call).
Every negative case is hand-picked to exercise one named refusal reason, not
derived from the implementation.
"""

import pytest

from unicode_logic_kit.eval.canonical import canonicalize
from unicode_logic_kit.atp.resolution import prove
from unicode_logic_kit.fol.nodes import (
    And, Atom, Box, Constant, Function, Iff, Implies, Not, Number, Or,
    Quantifier, Variable, Xor,
)
from unicode_logic_kit.fol.prolog_input import parse_prolog_clause, parse_prolog_program
from unicode_logic_kit.fol.prolog_export import (
    PrologExportError, formula_to_prolog_clause, formula_to_prolog_program,
)


def _mutually_entail(a, b, max_steps=20000) -> bool:
    """Logical equivalence via TWO separate resolution refutations rather
    than one ``is_valid_resolution(Iff(a, b))`` call.

    Both certify the same thing (``a ⊨ b`` and ``b ⊨ a`` together ARE
    ``a ↔ b``) and ``is_valid_resolution`` is exactly
    ``prove([], formula)`` under the hood — but empirically, wrapping two
    multi-literal ∀-closed clauses in one ``Iff`` before refuting sends the
    combined clause set (``(a ∧ ¬b) ∨ (¬a ∧ b)``, doubly skolemised) into a
    search that does not close within tens of thousands of steps even for
    clauses this small and OBVIOUSLY equivalent (verified by hand while
    writing this suite: a 2-literal body already times out that way, while
    the two-``prove``-calls form below closes INSTANTLY up to at least 4
    literals). ``prove`` clausifies and Skolemises each side once, so the
    combined search space stays linear rather than doubling.
    """
    return prove([a], b, max_steps=max_steps) and prove([b], a, max_steps=max_steps)


def _assert_round_trips(text, **kwargs):
    """``text`` -> AST (oracle) -> Prolog text (this module) -> AST again.

    Asserts BOTH that the reparsed result is the same formula up to bound
    -variable renaming (structural oracle) and that it is logically
    equivalent to the original (semantic oracle, via the kit's own
    resolution prover, in mutual-entailment form — see
    :func:`_mutually_entail` — independent of both parsers). Returns the
    emitted text so callers can additionally inspect its surface shape.
    """
    node = parse_prolog_clause(text, **kwargs)
    emitted = formula_to_prolog_clause(node, **kwargs)
    reparsed = parse_prolog_clause(emitted, **kwargs)

    assert canonicalize(reparsed) == canonicalize(node), (
        f"{text!r} -> {emitted!r} did not reparse to the same formula: "
        f"{node.to_unicode_str()!r} vs {reparsed.to_unicode_str()!r}")
    assert _mutually_entail(node, reparsed), (
        f"{text!r} -> {emitted!r} reparsed to a formula the resolution "
        "prover cannot show equivalent to the original")
    return emitted


# ---------------------------------------------------------------------------
# Facts
# ---------------------------------------------------------------------------

def test_a_ground_fact_round_trips():
    """``carbon(a).`` has no variables to rename at all."""
    emitted = _assert_round_trips("carbon(a).")
    assert emitted == "carbon(a)."


def test_a_fact_with_a_variable_round_trips():
    """``p(X).`` reads back as ``∀x P(x)``; re-exporting must produce a
    text that reads back to the SAME closed formula, under a fresh name."""
    emitted = _assert_round_trips("p(X).")
    assert emitted == "p(V0)."


def test_a_zero_arity_fact_round_trips_without_parentheses():
    emitted = _assert_round_trips("flag.")
    assert emitted == "flag."


# ---------------------------------------------------------------------------
# Rules: conjunctive and disjunctive bodies
# ---------------------------------------------------------------------------

def test_a_single_body_rule_round_trips():
    """Hand-derived: ``h(A) :- b(A, B).`` is ∀a∀b (B(a,b) → H(a)) — the head
    variable renamed first (it sorts first alphabetically as ``a``), the
    body-only variable second, matching parse_prolog_clause's own
    alphabetical closing order exactly."""
    emitted = _assert_round_trips("h(A) :- b(A, B).")
    assert emitted == "h(V0) :- b(V0, V1)."


def test_a_conjunctive_body_round_trips():
    _assert_round_trips("amide(A) :- carbon(C), nitrogen(N), bond(C, N), in(A, C).")


def test_a_disjunctive_body_round_trips():
    emitted = _assert_round_trips("p(A) :- q(A) ; r(A).")
    assert " ; " in emitted


def test_comma_binds_tighter_than_semicolon_on_export_too():
    """The mixed body ``q(A), r(A) ; s(A)`` — (Q∧R)∨S — must round-trip
    without needing help, since ',' already binds tighter than ';' with no
    parentheses required."""
    emitted = _assert_round_trips("p(A) :- q(A), r(A) ; s(A).")
    assert emitted == "p(V0) :- q(V0), r(V0) ; s(V0)."


def test_an_or_nested_inside_an_and_needs_parentheses_on_export():
    """The opposite nesting — Or as an operand of And — is where Prolog's
    precedence would otherwise mis-group the text, so the exporter must add
    parentheses a human writing ``q(A), (r(A) ; s(A))`` would also need."""
    node = parse_prolog_clause("p(A) :- q(A), (r(A) ; s(A)).")
    emitted = formula_to_prolog_clause(node)
    assert "(" in emitted
    reparsed = parse_prolog_clause(emitted)
    assert canonicalize(reparsed) == canonicalize(node)
    assert _mutually_entail(node, reparsed)


# ---------------------------------------------------------------------------
# Terms: compound functions, numbers, quoted atoms, the anonymous variable
# ---------------------------------------------------------------------------

def test_a_compound_term_and_a_number_round_trip():
    _assert_round_trips("p(A) :- q(A, f(a), 3).")


def test_a_negative_and_a_float_number_round_trip():
    _assert_round_trips("p(A) :- q(A, -3, 1.5).")


def test_a_plain_large_integer_and_an_ordinary_float_still_round_trip():
    """Guards against over-refusing: an arbitrary-precision Python ``int``
    never prints in scientific notation (only ``float`` does), so a large
    but PLAIN integer literal must still round trip after the numeral-
    grammar check below is added."""
    _assert_round_trips("p(A) :- q(A, 123456789012345, 0.5).")


def test_a_float_too_large_to_have_a_fraction_prints_as_the_integer_it_equals():
    """Hand-checked: ``str(1e20) == '1e+20'`` in Python, and
    parse_prolog_clause's own numeral grammar is ``-?\\d+(\\.\\d+)?`` — no
    ``e``, so the float's own text could not be read back. But a float with a
    whole value is the integer it equals in a ``Number`` (a value has one
    spelling: ``Number(1e20)`` IS ``Number(100000000000000000000)``), so there
    is no exponent text to refuse at this end of the scale and the clause is
    the integer's, which the importer reads back as the very node. (The
    other end, ``1e-10``, has a fractional part and is still refused, below.)"""
    node = Atom("P", [Number(1e20)])
    assert node.args[0].value == 10 ** 20 and isinstance(node.args[0].value, int)
    text = formula_to_prolog_clause(node)
    assert text == "p(100000000000000000000)."
    assert parse_prolog_clause(text) == node


def test_a_number_that_would_print_in_small_scientific_notation_is_refused():
    """Same failure mode at the other end of the magnitude scale:
    ``str(1e-10) == '1e-10'``, also outside the numeral grammar."""
    node = Atom("P", [Number(1e-10)])
    with pytest.raises(PrologExportError, match="numeral grammar"):
        formula_to_prolog_clause(node)


@pytest.mark.parametrize("value", [float("nan"), float("inf"), float("-inf")])
def test_nan_and_infinity_are_refused_not_silently_misread(value):
    """Worse than a parse error: unrefused, 'p(nan).'/'p(inf).' reparse
    SILENTLY with the kit's own importer as ``Constant('nan')``/
    ``Constant('inf')`` — a different node type, no error raised at all —
    since parse_prolog_clause's numeral grammar does not recognise
    ``nan``/``inf`` either, so the tail end of its name-token rule catches
    it as a bare atom instead. Refusing up front is what this module's own
    'nothing else is rendered, it is REFUSED' claim requires."""
    node = Atom("P", [Number(value)])
    with pytest.raises(PrologExportError, match="numeral grammar"):
        formula_to_prolog_clause(node)


def test_a_quoted_atom_round_trips():
    """A constant with characters no bare Prolog atom can carry must come
    back out quoted, the exact inverse of how it went in."""
    emitted = _assert_round_trips("cls(A) :- q(A), 'has-a-hyphen'(A).")
    assert "'has-a-hyphen'" in emitted


def test_two_anonymous_variables_stay_distinct_after_a_round_trip():
    """``_`` twice means two independent positions; the exporter must not
    accidentally collapse the two fresh variables the importer made."""
    node = parse_prolog_clause("p(A) :- q(A, _), r(A, _).")
    emitted = formula_to_prolog_clause(node)
    reparsed = parse_prolog_clause(emitted)
    assert canonicalize(reparsed) == canonicalize(node)
    assert _mutually_entail(node, reparsed)
    # Two DISTINCT bound variables besides the head's — not one shared.
    bound = [q.variable.name for q in reparsed.walk()
             if isinstance(q, Quantifier)]
    assert len(bound) == 3
    assert len(set(bound)) == 3


def test_a_zero_arity_function_term_is_refused():
    """Prolog syntax cannot write ``f()`` distinct from the bare atom ``f``,
    so ``parse_prolog_clause`` would read the emitted text back as
    ``Constant('f')``, not ``Function('f', [])`` — a genuine change of node
    type. Confirmed with the kit's own resolution prover (the SAME oracle
    every positive test in this suite uses) that the two are NOT logically
    equivalent in either direction, so silently collapsing one into the
    other would be exactly the kind of approximation this module forbids."""
    node = Atom("P", [Function("f", [])])
    with pytest.raises(PrologExportError, match="0-arity"):
        formula_to_prolog_clause(node)

    # The failure-mode this refusal prevents, spelled out: without it,
    # 'p(f).' reparses to Atom('P', [Constant('f')]), which the resolution
    # prover shows is NOT mutually entailed with the original.
    reparsed = parse_prolog_clause("p(f).")
    assert isinstance(reparsed.args[0], Constant)
    assert not (prove([node], reparsed) and prove([reparsed], node))


def test_a_zero_arity_function_nested_inside_a_compound_term_is_also_refused():
    node = Atom("P", [Function("g", [Function("f", [])])])
    with pytest.raises(PrologExportError, match="0-arity"):
        formula_to_prolog_clause(node)


# ---------------------------------------------------------------------------
# Negation as failure, opted in
# ---------------------------------------------------------------------------

def test_naf_round_trips_only_with_the_opt_in():
    emitted = _assert_round_trips(
        "p(A) :- q(A), \\+ r(A).", negation_as_failure="classical")
    assert "\\+ " in emitted


def test_naf_without_the_opt_in_is_refused_naming_the_closed_world_assumption():
    node = parse_prolog_clause("p(A) :- q(A), \\+ r(A).",
                               negation_as_failure="classical")
    with pytest.raises(PrologExportError, match="closed world assumption"):
        formula_to_prolog_clause(node)  # default: negation_as_failure="refuse"


def test_naf_agrees_with_classical_negation_exactly_when_the_program_is_complete():
    """Documented in the module: '\\+ G' agrees with '¬G' when the program is
    COMPLETE for G — every true ground instance is also derivable. Here the
    program states carbon(a) and NOTHING ELSE about carbon/1, and 'a' is
    genuinely not carbon: \\+ carbon(a) at V0=b succeeds and matches ¬Carbon(b)
    exactly, because the (tiny, complete) program has decided carbon/1 fully
    for every constant it mentions."""
    text = "not_carbon(A) :- \\+ carbon(A)."
    node = parse_prolog_clause(text, negation_as_failure="classical")
    assert node.to_unicode_str() == "∀a (¬Carbon(a) → Not_carbon(a))"
    emitted = formula_to_prolog_clause(node, negation_as_failure="classical")
    reparsed = parse_prolog_clause(emitted, negation_as_failure="classical")
    assert canonicalize(reparsed) == canonicalize(node)


def test_naf_disagrees_with_classical_negation_on_an_incomplete_program():
    """The disagreement case the module docstring promises a test for.

    Take the SAME rule, ``p(A) :- \\+ q(A).``, and an EMPTY fact base for
    q/1 (the program asserts nothing at all about q). Two independent,
    hand-checkable routes then diverge:

    * Prolog's own reading (simulated here by the textbook definition of
      negation-as-failure over ground atoms: '\\+ G' succeeds iff G is not
      among the derivable facts) says '\\+ q(a)' SUCCEEDS — nothing proved
      q(a), so failure-to-prove holds trivially, for EVERY constant, known
      or not.
    * The classical reading this exporter produces under
      ``negation_as_failure="classical"`` is ``¬Q(a) → P(a)``, which only
      lets you conclude P(a) if ¬Q(a) is an actual logical consequence of
      the program's facts. From an EMPTY set of facts about q/1, ¬Q(a) is
      NOT a consequence (q(a) is simply undetermined, not false) — checked
      here with the kit's own resolution prover, independently of both
      Prolog readers in this module.

    So the same empty program licenses p(a) under Prolog's closed-world
    '\\+', but the classical formula this exporter emits for
    ``negation_as_failure="classical"`` does NOT license Classical-P(a) from
    the same empty premise set. That gap is exactly why the opt-in exists.
    """
    facts = set()  # the empty q/1 program

    def naf_succeeds(constant: str) -> bool:
        """Textbook SLD negation-as-failure for a ground query against a
        FACTS-ONLY, RULE-FREE database: '\\+ q(X)' succeeds iff q(X) is not
        one of the asserted facts — there is nothing else to try proving it
        with."""
        return constant not in facts

    a = Constant("a")
    assert naf_succeeds("a") is True  # Prolog: \+ q(a) succeeds

    # Classical: is ¬Q(a) actually entailed by the (empty) fact base?
    entailed = prove([], Not(Atom("Q", [a])))
    assert entailed is False  # NOT entailed — Q(a) is simply undetermined

    # The disagreement, stated as a single boolean: Prolog's closed-world
    # verdict and the classical entailment verdict for the SAME query,
    # over the SAME (empty) program, are opposite.
    assert naf_succeeds("a") != entailed

    # Tie that conclusion to the module's ACTUAL output, not just the
    # textbook NAF simulation above: this is exactly the clause
    # test_a_real_swipl_confirms_the_naf_disagreement_case feeds to a real
    # swipl for the same empty-q/1 scenario, so the disagreement is checked
    # against formula_to_prolog_clause's real code path even on a CI runner
    # where that skip-gated swipl test does not run at all.
    av = Variable("a")
    node = Quantifier("∀", av, Implies(Not(Atom("Q", [av])), Atom("P", [av])))
    emitted = formula_to_prolog_clause(node, negation_as_failure="classical")
    assert emitted == "p(V0) :- \\+ q(V0)."


# ---------------------------------------------------------------------------
# A chemistry-flavoured example (matches the kit's own predicate spellings,
# mirroring tests/test_prolog_input.py's convention)
# ---------------------------------------------------------------------------

def test_a_chemistry_flavoured_clause_round_trips():
    """Mixed-case predicate spellings (as ChemLog uses, e.g. ``bSINGLE``)
    fold on only their first character in both directions."""
    text = "amide(A) :- bSINGLE(C, D), bDOUBLE(D, B), n(C), in(A, C)."
    emitted = _assert_round_trips(text)
    node = parse_prolog_clause(text)
    assert "BSINGLE" in node.to_unicode_str()  # sanity: the oracle folds
    assert "bSINGLE" in emitted                # only the first character


# ---------------------------------------------------------------------------
# Programs (several clauses)
# ---------------------------------------------------------------------------

def test_formula_to_prolog_program_splits_on_the_outer_conjunction():
    from unicode_logic_kit.fol.nodes import free_variables
    a = Variable("a")
    fact = Atom("Carbon", [Constant("c1")])
    rule = Quantifier("∀", a, Implies(Atom("Carbon", [a]), Atom("Atomic", [a])))
    program_text = formula_to_prolog_program(And(fact, rule))

    lines = program_text.splitlines()
    assert len(lines) == 2
    clauses = parse_prolog_program(program_text)
    assert len(clauses) == 2
    assert canonicalize(clauses[0]) == canonicalize(fact)
    assert canonicalize(clauses[1]) == canonicalize(rule)


def test_formula_to_prolog_program_also_accepts_a_plain_iterable():
    a = Variable("a")
    fact = Atom("Carbon", [Constant("c1")])
    rule = Quantifier("∀", a, Implies(Atom("Carbon", [a]), Atom("Atomic", [a])))
    from_and = formula_to_prolog_program(And(fact, rule))
    from_list = formula_to_prolog_program([fact, rule])
    assert from_and == from_list


def test_formula_to_prolog_program_names_which_clause_failed():
    """A failure in the middle of a multi-clause program must name which
    conjunct triggered it (position and text), not just the reason — the
    same discipline :func:`~unicode_logic_kit.fol.prolog_input.parse_prolog_program`
    already applies on the way in with its ``"(in clause: ...)"`` suffix."""
    fact = Atom("Fact", [Constant("a")])
    bad = Atom("lowercase", [Constant("x")])
    a = Variable("a")
    rule = Quantifier("∀", a, Implies(Atom("Carbon", [a]), Atom("Atomic", [a])))

    with pytest.raises(PrologExportError) as excinfo:
        formula_to_prolog_program([fact, bad, rule])

    message = str(excinfo.value)
    # The underlying single-clause reason must still be present...
    assert "does not start with an upper-case letter" in message
    # ...plus which clause of how many, and its own text, pinpointing it.
    assert "in clause 2 of 3" in message
    assert bad.to_unicode_str() in message


def test_formula_to_prolog_program_names_the_last_clause_too():
    """The clause-position count is 1-indexed and covers the LAST clause,
    not just an off-by-one-friendly middle one."""
    fact = Atom("Fact", [Constant("a")])
    bad = Atom("lowercase", [Constant("x")])

    with pytest.raises(PrologExportError, match=r"in clause 2 of 2"):
        formula_to_prolog_program([fact, bad])


# ---------------------------------------------------------------------------
# What it refuses, and why
# ---------------------------------------------------------------------------

def test_unknown_negation_as_failure_is_refused_before_anything_else():
    with pytest.raises(PrologExportError, match="unknown negation_as_failure"):
        formula_to_prolog_clause(Atom("P", []), negation_as_failure="nonsense")


def test_iff_is_refused():
    x = Variable("x")
    node = Quantifier("∀", x, Iff(Atom("P", [x]), Atom("Q", [x])))
    with pytest.raises(PrologExportError, match="Iff"):
        formula_to_prolog_clause(node)


def test_xor_is_refused():
    x = Variable("x")
    node = Quantifier("∀", x, Xor(Atom("P", [x]), Atom("Q", [x])))
    with pytest.raises(PrologExportError, match="Xor"):
        formula_to_prolog_clause(node)


def test_an_existential_quantifier_is_refused():
    x = Variable("x")
    node = Quantifier("∃", x, Atom("P", [x]))
    with pytest.raises(PrologExportError, match="Quantifier"):
        formula_to_prolog_clause(node)


def test_a_nested_quantifier_inside_the_body_is_refused():
    x, y = Variable("x"), Variable("y")
    body = Quantifier("∃", y, Atom("Q", [x, y]))
    node = Quantifier("∀", x, Implies(body, Atom("P", [x])))
    with pytest.raises(PrologExportError, match="Quantifier"):
        formula_to_prolog_clause(node)


def test_a_disjunctive_head_is_refused():
    x = Variable("x")
    node = Quantifier("∀", x, Implies(
        Atom("Q", [x]), Or(Atom("P", [x]), Atom("R", [x]))))
    with pytest.raises(PrologExportError, match="single atom"):
        formula_to_prolog_clause(node)


def test_a_non_range_restricted_head_variable_is_refused():
    """``∀x∀y (Q(x) → P(x, y))`` — y appears only in the head. Prolog would
    leave ``Y`` in ``p(X, Y) :- q(X).`` ranging over every value bound
    elsewhere in the clause; that is not what the universally-quantified
    formula said."""
    x, y = Variable("x"), Variable("y")
    node = Quantifier("∀", x, Quantifier("∀", y, Implies(
        Atom("Q", [x]), Atom("P", [x, y]))))
    with pytest.raises(PrologExportError, match="do not occur in the body"):
        formula_to_prolog_clause(node)


def test_negation_of_a_compound_goal_is_refused_even_with_the_opt_in():
    """The importer's own grammar lets '\\+' wrap an arbitrary goal
    (``\\+ (a, b)`` is legal Prolog); this exporter deliberately narrows to
    '\\+ Atom' only (see the module docstring), so the wider shape is
    refused rather than silently narrowed or mis-rendered."""
    x = Variable("x")
    node = Quantifier("∀", x, Implies(
        Not(And(Atom("Q", [x]), Atom("R", [x]))), Atom("P", [x])))
    with pytest.raises(PrologExportError, match=r"\\\+.*applied to a single atom"):
        formula_to_prolog_clause(node, negation_as_failure="classical")


@pytest.mark.parametrize("predicate", ["=", "≠", "<", ">", "≤", "≥"])
def test_comparison_and_equality_predicates_are_refused(predicate):
    """``parse_prolog_clause`` has no reading for any of these (see its own
    module docstring: arithmetic comparison is refused on the way in too),
    so there is nothing to round trip."""
    x = Variable("x")
    node = Atom(predicate, [x, Constant("a")])
    with pytest.raises(PrologExportError, match="comparison/equality"):
        formula_to_prolog_clause(node)


def test_a_predicate_that_does_not_start_upper_case_is_refused():
    """Every kit predicate is parsed starting upper-case (the kit's own
    signal for predicate-hood); a hand-built ``Atom`` that breaks that
    convention cannot be folded back to itself, so it is refused rather
    than exported under a spelling that would misread on the way back."""
    node = Atom("lowercase", [Constant("a")])
    with pytest.raises(PrologExportError, match="does not start with an "
                       "upper-case letter"):
        formula_to_prolog_clause(node)


def test_a_modal_operator_is_refused_with_the_normalforms_pointer():
    """Reuses :func:`unicode_logic_kit.fol.normalforms._unsupported_hint`'s
    own routing, so a modal formula gets the SAME pointer
    ``to_cnf``/``is_horn`` already give for it."""
    x = Variable("x")
    node = Quantifier("∀", x, Box(Atom("P", [x])))
    with pytest.raises(PrologExportError, match="standard_translation"):
        formula_to_prolog_clause(node)


def test_horn_but_not_directly_shaped_is_refused_with_the_soundness_note():
    """The key soundness fix this module's roadmap item exists for: a
    formula whose SKOLEMISED/CNF clausal form happens to be Horn
    (``is_horn`` is True) but which is not directly a fact or a
    ``body -> head`` implication. A naive ``is_horn``-gated exporter would
    have clausified and silently emitted it — satisfiability-preserving,
    not equivalence-preserving. This one refuses instead, and says why.
    """
    x = Variable("x")
    # ∀x (¬P(x) ∨ Q(x)) — an Or, not an Implies, though it clausifies to
    # exactly the single Horn clause {¬P(x), Q(x)}.
    node = Quantifier("∀", x, Or(Not(Atom("P", [x])), Atom("Q", [x])))
    from unicode_logic_kit.fol.normalforms import is_horn
    assert is_horn(node) is True  # confirms this really is the near-miss case
    with pytest.raises(PrologExportError, match="is_horn"):
        formula_to_prolog_clause(node)


def test_a_naked_negation_without_the_naf_opt_in_names_the_reason():
    """Even though ``¬Q(x) → P(x)`` clausifies to a NON-Horn clause
    (``Q(x) ∨ P(x)``, two positive literals — so it could ALSO be refused as
    'not Horn'), the message actually raised must point at the real,
    actionable reason: classical negation with no negation-as-failure
    opt-in — the same "closed world assumption" wording
    ``parse_prolog_clause`` itself uses on the way in."""
    x = Variable("x")
    node = Quantifier("∀", x, Implies(Not(Atom("Q", [x])), Atom("P", [x])))
    with pytest.raises(PrologExportError, match="closed world assumption"):
        formula_to_prolog_clause(node)


# ---------------------------------------------------------------------------
# Optional: a real SWI-Prolog consults the emitted program (skip-gated)
# ---------------------------------------------------------------------------

def _find_swipl():
    """``(argv_prefix, to_wsl_path)`` for invoking swipl, or ``None``.

    Mirrors the discovery convention every optional external prover in this
    kit already uses (``shutil.which`` -> WSL probe; see e.g.
    ``unicode_logic_kit.atp.eprover_backend._discover``): native PATH first,
    then a WSL install, never assumed.
    """
    import shutil
    import subprocess

    if shutil.which("swipl"):
        return (["swipl"], False)
    try:
        probe = subprocess.run(["wsl.exe", "which", "swipl"],
                               capture_output=True, text=True, timeout=20)
        if probe.returncode == 0 and probe.stdout.strip():
            return (["wsl.exe", "swipl"], True)
    except (OSError, FileNotFoundError):
        pass
    return None


def _to_wsl_path(windows_path: str) -> str:
    import subprocess

    result = subprocess.run(
        ["wsl.exe", "wslpath", "-u", windows_path.replace("\\", "/")],
        capture_output=True, text=True, timeout=20)
    wsl_path = result.stdout.strip()
    if not wsl_path:
        raise RuntimeError(f"wslpath could not translate {windows_path!r}")
    return wsl_path


_SWIPL = _find_swipl()


def _run_swipl_query(program_text: str, goal: str, tmp_path) -> str:
    import subprocess

    swipl_argv, use_wsl = _SWIPL
    path = tmp_path / "program.pl"
    path.write_text(program_text, encoding="utf-8")
    consult_path = _to_wsl_path(str(path)) if use_wsl else str(path)
    result = subprocess.run(
        [*swipl_argv, "-q", "-g",
         f"consult('{consult_path}'), {goal}, halt.", "-g", "halt."],
        capture_output=True, text=True, timeout=30)
    return (result.stdout or "") + (result.stderr or "")


@pytest.mark.skipif(_SWIPL is None, reason="swipl not found on PATH or in WSL")
def test_a_real_swipl_consults_the_emitted_program(tmp_path):
    """The emitted text is not just re-readable by this kit's OWN Prolog
    reader — it is legal input to a real Prolog engine, which is the whole
    point of exporting to Prolog in the first place."""
    a = Variable("a")
    fact = Atom("Carbon", [Constant("c1")])
    rule = Quantifier("∀", a, Implies(Atom("Carbon", [a]), Atom("Amide_atom", [a])))
    program_text = formula_to_prolog_program(And(fact, rule))

    out = _run_swipl_query(
        program_text,
        "(amide_atom(c1) -> writeln(yes) ; writeln(no)), "
        "(amide_atom(c2) -> writeln(yes) ; writeln(no))",
        tmp_path)
    assert out.splitlines()[:2] == ["yes", "no"]


@pytest.mark.skipif(_SWIPL is None, reason="swipl not found on PATH or in WSL")
def test_a_real_swipl_confirms_the_naf_disagreement_case(tmp_path):
    """Runs the SAME disagreement scenario as
    ``test_naf_disagrees_with_classical_negation_on_an_incomplete_program``
    through an actual Prolog engine instead of the hand-written NAF
    simulator: an EMPTY ``q/1`` and the rule
    ``p(A) :- \\+ q(A).`` must make ``p(a)`` succeed for a NEVER-MENTIONED
    constant — the closed-world reading, which the classical formula this
    module emits under ``negation_as_failure="classical"`` does not license
    from the same empty premise set (see the resolution-based half of that
    test)."""
    a = Variable("a")
    node = Quantifier("∀", a, Implies(
        Not(Atom("Q", [a])), Atom("P", [a])))
    program_text = formula_to_prolog_clause(node, negation_as_failure="classical")
    # One clause only — no separate q/1 facts were added, so the program is
    # silent about q entirely. SWI-Prolog raises an existence_error for a
    # goal on a predicate with NO clauses at all (its default "unknown"
    # safety net against typos, not classical closed-world failure) unless
    # the predicate is declared `dynamic` — the standard way to say "this
    # predicate legitimately has zero clauses" rather than "undefined".
    # That declaration is Prolog engineering, not part of what this
    # exporter's own clause translation needs to say, so it is added here,
    # at the test level, rather than emitted by formula_to_prolog_clause.
    assert program_text.count("\n") == 0
    assert program_text == "p(V0) :- \\+ q(V0)."
    full_program = ":- dynamic q/1.\n" + program_text

    out = _run_swipl_query(
        full_program, "(p(a) -> writeln(yes) ; writeln(no))", tmp_path)
    assert out.splitlines()[:1] == ["yes"]
