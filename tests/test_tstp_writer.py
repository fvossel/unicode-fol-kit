"""Tests for :func:`atp.tstp.to_tstp` — the write-side companion to
:func:`atp.tstp.parse_tstp_derivation` (roadmap item K7).

Every fixture below is either lifted verbatim from an already hand-checked
derivation in ``tests/test_resolution_check.py`` / ``tests/test_superposition.py``
(each already independently re-verified there by
:func:`atp.resolution_check.verify_resolution_proof`) or built fresh and
hand-derived in the comment above it — no expected value is taken from
running :func:`to_tstp` first and pasting its output back in.

Two independent routes back-check every rendered derivation (per this
item's batch notes):

1. **The kit's own reader** (:func:`atp.tstp.parse_tstp_derivation`): the
   text must parse back into a :class:`~atp.tstp.TstpDerivation` whose
   per-step ``.rule``/``.parents`` match the TSTP tokens :func:`to_tstp`
   chose and whose ``.formula`` (mapped back through
   :func:`atp.tstp.apply_reverse_tptp`, then read as a clause via
   :func:`atp.tstp_check._node_to_clause`) is a variant
   (:func:`atp.resolution_check._is_variant`) of the original step's clause.
2. **The independently-checked semantics**
   (:func:`atp.tstp_check.check_tstp_derivation`): every kit rule this
   writer emits (``resolve``/``factor``/``paramodulate``/``demodulate``/
   ``reflexivity``) maps to a TSTP token registered in that module's
   ``VAMPIRE_CHECKED_RULES``/``EPROVER_CHECKED_RULES`` tables — see
   :data:`atp.tstp._KIT_RULE_TO_TSTP`'s own docstring/comment for exactly
   why each token was chosen (not always the most "obvious" TSTP name) — so
   a rendered derivation must come back fully ``verified`` under Z3-backed,
   from-scratch re-derivation, not merely "parses". There is, at present,
   no kit rule this writer emits that check_tstp_derivation cannot check:
   ``"input"`` steps go through that module's ``"leaf"`` tier (an
   alpha-variant check against the supplied premises) instead, which is
   likewise a genuine independent check, just not a "checked"-tier rule
   re-derivation.
"""

import pytest

from unicode_logic_kit.fol.nodes import Atom, Constant, Function, Not, Variable
from unicode_logic_kit.fol.tptp_input import parse_tptp_formula
from unicode_logic_kit.atp._tptp_problem import (
    generate_tptp_problem_with_mapping, _sanitize_for_tptp,
)
from unicode_logic_kit.atp.resolution_check import (
    ResolutionStep, ResolutionDerivation, _RULE_ARITY, _is_variant,
    verify_resolution_proof,
)
from unicode_logic_kit.atp.tstp import (
    TptpNameMap, _KIT_RULE_TO_TSTP, _render_clause_tptp,
    _extend_name_map_for_derivation,
    apply_reverse_tptp, parse_tstp_derivation, to_tstp,
)
from unicode_logic_kit.atp.tstp_check import (
    EPROVER_CHECKED_RULES, VAMPIRE_CHECKED_RULES,
    _node_to_clause, check_tstp_derivation,
)


def P(*args):
    return Atom("P", list(args))


def Q(*args):
    return Atom("Q", list(args))


def EQ(s, t):
    return Atom("=", [s, t])


x, y, u, v = Variable("x"), Variable("y"), Variable("u"), Variable("v")
a, b = Constant("a"), Constant("b")


def f(t):
    return Function("f", [t])


# ---------------------------------------------------------------------------
# Shared helpers for the independent second route (check_tstp_derivation):
# a premise Node for an "input" step must come from parsing the EXACT same
# text to_tstp itself emits for that clause -- built via the same private
# _render_clause_tptp helper to_tstp uses internally, so the two parses of
# identical text are structurally identical (not merely alpha-equal),
# guaranteeing the "leaf" tier's alpha-equivalence check succeeds whenever
# the writer's own rendering is self-consistent.
# ---------------------------------------------------------------------------

def _clause_text(clause, mapping):
    literals = _render_clause_tptp(clause, mapping)
    return "$false" if not literals else " | ".join(lit.to_tptp() for lit in literals)


def _input_premises(derivation, mapping):
    return [parse_tptp_formula(_clause_text(step.clause, mapping))
            for step in derivation.steps if step.rule == "input"]


# ---------------------------------------------------------------------------
# 1. Golden text -- hand-checked byte-for-byte, including the two shape
#    edge cases the mapping spec calls out explicitly: an "input" step (no
#    source annotation) and the empty-clause sink ("$false").
# ---------------------------------------------------------------------------

def test_golden_two_clause_refutation_to_empty_clause():
    # {P(a)}, {¬P(a)} resolve directly (mgu {}, both ground) to the empty
    # clause -- the exact example named in this item's spec.
    inputs = (frozenset({P(a)}), frozenset({Not(P(a))}))
    steps = (
        ResolutionStep(1, frozenset({P(a)}), "input"),
        ResolutionStep(2, frozenset({Not(P(a))}), "input"),
        ResolutionStep(3, frozenset(), "resolve", (1, 2)),
    )
    d = ResolutionDerivation(inputs, steps)
    assert verify_resolution_proof(d).ok
    expected = (
        "cnf(c1, plain, p(a)).\n"
        "cnf(c2, plain, ~(p(a))).\n"
        "cnf(c3, plain, $false, inference(resolution, [status(thm)], [c1, c2])).\n"
    )
    assert to_tstp(d) == expected


def test_golden_resolve_chain_two_steps():
    # Matches test_resolution_check.py's own _part_a_derivation exactly:
    #   {P(a)}, {¬P(x) ∨ Q(x)}, {¬Q(a)} -- resolve(1,2) on P(a)/¬P(x) [x↦a]
    #   gives {Q(a)}; resolve(3,4) on ¬Q(a)/Q(a) gives the empty clause.
    # Literal order within clause 2 is by _lit_key (to_unicode_str()): "Q(x)"
    # (U+0051) sorts before "¬P(x)" (U+00AC) codepoint-wise -- the exact
    # ordering test_render_resolution_proof_pinned already hand-derives for
    # this same clause.
    inputs = (frozenset({P(a)}), frozenset({Not(P(x)), Q(x)}), frozenset({Not(Q(a))}))
    steps = (
        ResolutionStep(1, frozenset({P(a)}), "input"),
        ResolutionStep(2, frozenset({Not(P(x)), Q(x)}), "input"),
        ResolutionStep(3, frozenset({Not(Q(a))}), "input"),
        ResolutionStep(4, frozenset({Q(a)}), "resolve", (1, 2)),
        ResolutionStep(5, frozenset(), "resolve", (3, 4)),
    )
    d = ResolutionDerivation(inputs, steps)
    assert verify_resolution_proof(d).ok
    expected = (
        "cnf(c1, plain, p(a)).\n"
        "cnf(c2, plain, q(X) | ~(p(X))).\n"
        "cnf(c3, plain, ~(q(a))).\n"
        "cnf(c4, plain, q(a), inference(resolution, [status(thm)], [c1, c2])).\n"
        "cnf(c5, plain, $false, inference(resolution, [status(thm)], [c3, c4])).\n"
    )
    assert to_tstp(d) == expected


def test_input_step_edge_case_no_source_annotation():
    # Dedicated edge case: a lone "input" step has NO inference(...) field at
    # all -- exactly the shape parse_tstp_derivation reads as a leaf
    # (TstpStep.rule is None, TstpStep.parents == ()).
    d = ResolutionDerivation((frozenset({P(a)}),),
                             (ResolutionStep(1, frozenset({P(a)}), "input"),))
    assert verify_resolution_proof(d).ok
    text = to_tstp(d)
    assert text == "cnf(c1, plain, p(a)).\n"
    assert "inference(" not in text
    parsed = parse_tstp_derivation(text)
    assert len(parsed.steps) == 1
    assert parsed.steps[0].rule is None
    assert parsed.steps[0].parents == ()


def test_empty_clause_edge_case_renders_as_dollar_false():
    # Dedicated edge case: the empty clause is the literal text "$false",
    # never an empty literal list joined by " | " (which would render "").
    d = ResolutionDerivation(
        (frozenset({P(a)}), frozenset({Not(P(a))})),
        (ResolutionStep(1, frozenset({P(a)}), "input"),
         ResolutionStep(2, frozenset({Not(P(a))}), "input"),
         ResolutionStep(3, frozenset(), "resolve", (1, 2))),
    )
    lines = to_tstp(d).splitlines()
    assert lines[2] == "cnf(c3, plain, $false, inference(resolution, [status(thm)], [c1, c2]))."


def test_empty_derivation_serialises_to_empty_text():
    d = ResolutionDerivation((), ())
    assert verify_resolution_proof(d).ok
    assert to_tstp(d) == ""


# ---------------------------------------------------------------------------
# 2. Round trip via the kit's OWN reader (independent route 1):
#    parse_tstp_derivation(to_tstp(d)) must reconstruct .rule/.parents and a
#    .formula that is a variant of the original step's clause, for every
#    rule kind this writer covers.
# ---------------------------------------------------------------------------

def _assert_roundtrips(d: ResolutionDerivation):
    assert verify_resolution_proof(d).ok
    text = to_tstp(d)
    parsed = parse_tstp_derivation(text)
    assert len(parsed.steps) == len(d.steps)
    identity_map = TptpNameMap()  # every fixture below uses plain ASCII names
    for orig, pstep in zip(d.steps, parsed.steps):
        assert pstep.name == f"c{orig.index}"
        assert pstep.formula is not None
        back = apply_reverse_tptp(pstep.formula, identity_map)
        got_clause = _node_to_clause(back)
        assert got_clause is not None, f"step {orig.index}: not clausal after round trip"
        assert _is_variant(got_clause, orig.clause), (
            f"step {orig.index}: {got_clause} is not a variant of {orig.clause}")
        if orig.rule == "input":
            assert pstep.rule is None
            assert pstep.parents == ()
        else:
            assert pstep.rule == _KIT_RULE_TO_TSTP[orig.rule]
            assert pstep.parents == tuple(f"c{p}" for p in orig.parents)


def test_roundtrip_resolve_chain():
    inputs = (frozenset({P(a)}), frozenset({Not(P(x)), Q(x)}), frozenset({Not(Q(a))}))
    steps = (
        ResolutionStep(1, frozenset({P(a)}), "input"),
        ResolutionStep(2, frozenset({Not(P(x)), Q(x)}), "input"),
        ResolutionStep(3, frozenset({Not(Q(a))}), "input"),
        ResolutionStep(4, frozenset({Q(a)}), "resolve", (1, 2)),
        ResolutionStep(5, frozenset(), "resolve", (3, 4)),
    )
    _assert_roundtrips(ResolutionDerivation(inputs, steps))


def test_roundtrip_factor_and_resolve():
    # Matches test_resolution_check.py's test_robinson_factored_refutation_accepted.
    inputs = (frozenset({P(x), P(y)}), frozenset({Not(P(u)), Not(P(v))}))
    steps = (
        ResolutionStep(1, frozenset({P(x), P(y)}), "input"),
        ResolutionStep(2, frozenset({Not(P(u)), Not(P(v))}), "input"),
        ResolutionStep(3, frozenset({P(x)}), "factor", (1,)),
        ResolutionStep(4, frozenset({Not(P(u))}), "factor", (2,)),
        ResolutionStep(5, frozenset(), "resolve", (3, 4)),
    )
    _assert_roundtrips(ResolutionDerivation(inputs, steps))


def test_roundtrip_paramodulate_and_reflexivity():
    # Matches test_superposition.py's test_roundtrip_congruence.
    C1 = frozenset({EQ(a, b)})
    C2 = frozenset({Not(EQ(f(a), f(b)))})
    steps = (
        ResolutionStep(1, C1, "input"),
        ResolutionStep(2, C2, "input"),
        ResolutionStep(3, frozenset({Not(EQ(f(a), f(a)))}), "paramodulate", (1, 2),
                        eq_literal=EQ(a, b), target_literal=Not(EQ(f(a), f(b))),
                        direction="rl", position=(1, 0)),
        ResolutionStep(4, frozenset(), "reflexivity", (3,),
                        eq_literal=Not(EQ(f(a), f(a)))),
    )
    _assert_roundtrips(ResolutionDerivation((C1, C2), steps))


def test_roundtrip_demodulate():
    # Matches test_superposition.py's test_roundtrip_demodulate.
    target = frozenset({P(f(b))})
    unit_eq = frozenset({EQ(f(x), a)})
    steps = (
        ResolutionStep(1, target, "input"),
        ResolutionStep(2, unit_eq, "input"),
        ResolutionStep(3, frozenset({P(a)}), "demodulate", (1, 2),
                        eq_literal=EQ(f(x), a), target_literal=P(f(b)),
                        direction="lr", position=(0,)),
    )
    _assert_roundtrips(ResolutionDerivation((target, unit_eq), steps))


# ---------------------------------------------------------------------------
# 3. Independent second route: atp.tstp_check.check_tstp_derivation, Z3-
#    backed re-derivation of the "checked" tier plus the "leaf" tier for
#    "input" steps. query="refutation" throughout: a resolution derivation
#    already folds premises + negated conclusion into its clause inputs, so
#    there is no separate conjecture leaf (see atp.tstp's own module
#    docstring on the conjecture/refutation framings).
# ---------------------------------------------------------------------------

def _assert_checked(d: ResolutionDerivation):
    assert verify_resolution_proof(d).ok
    all_literals = [lit for step in d.steps for lit in step.clause]
    _, mapping = _sanitize_for_tptp(all_literals)
    text = to_tstp(d, name_map=mapping)
    parsed = parse_tstp_derivation(text)
    premises = _input_premises(d, mapping)
    result = check_tstp_derivation(parsed, premises, None, query="refutation")
    assert result.verified, result.error
    for orig, step_result in zip(d.steps, result.steps):
        if orig.rule == "input":
            assert step_result.tier == "leaf"
        else:
            assert step_result.tier == "checked"
        assert step_result.ok, step_result.detail


def test_checked_route_resolve_chain():
    inputs = (frozenset({P(a)}), frozenset({Not(P(x)), Q(x)}), frozenset({Not(Q(a))}))
    steps = (
        ResolutionStep(1, frozenset({P(a)}), "input"),
        ResolutionStep(2, frozenset({Not(P(x)), Q(x)}), "input"),
        ResolutionStep(3, frozenset({Not(Q(a))}), "input"),
        ResolutionStep(4, frozenset({Q(a)}), "resolve", (1, 2)),
        ResolutionStep(5, frozenset(), "resolve", (3, 4)),
    )
    _assert_checked(ResolutionDerivation(inputs, steps))


def test_checked_route_factor_and_resolve():
    inputs = (frozenset({P(x), P(y)}), frozenset({Not(P(u)), Not(P(v))}))
    steps = (
        ResolutionStep(1, frozenset({P(x), P(y)}), "input"),
        ResolutionStep(2, frozenset({Not(P(u)), Not(P(v))}), "input"),
        ResolutionStep(3, frozenset({P(x)}), "factor", (1,)),
        ResolutionStep(4, frozenset({Not(P(u))}), "factor", (2,)),
        ResolutionStep(5, frozenset(), "resolve", (3, 4)),
    )
    _assert_checked(ResolutionDerivation(inputs, steps))


def test_checked_route_paramodulate_and_reflexivity():
    C1 = frozenset({EQ(a, b)})
    C2 = frozenset({Not(EQ(f(a), f(b)))})
    steps = (
        ResolutionStep(1, C1, "input"),
        ResolutionStep(2, C2, "input"),
        ResolutionStep(3, frozenset({Not(EQ(f(a), f(a)))}), "paramodulate", (1, 2),
                        eq_literal=EQ(a, b), target_literal=Not(EQ(f(a), f(b))),
                        direction="rl", position=(1, 0)),
        ResolutionStep(4, frozenset(), "reflexivity", (3,),
                        eq_literal=Not(EQ(f(a), f(a)))),
    )
    _assert_checked(ResolutionDerivation((C1, C2), steps))


def test_checked_route_demodulate():
    target = frozenset({P(f(b))})
    unit_eq = frozenset({EQ(f(x), a)})
    steps = (
        ResolutionStep(1, target, "input"),
        ResolutionStep(2, unit_eq, "input"),
        ResolutionStep(3, frozenset({P(a)}), "demodulate", (1, 2),
                        eq_literal=EQ(f(x), a), target_literal=P(f(b)),
                        direction="lr", position=(0,)),
    )
    _assert_checked(ResolutionDerivation((target, unit_eq), steps))


def test_every_kit_rule_token_is_in_tstp_checks_checked_tables():
    # Documents (and enforces) the choice behind _KIT_RULE_TO_TSTP: every
    # token it emits must be one atp.tstp_check actually dispatches to a
    # "checked"-tier re-derivation, not merely a name that PARSES back.
    # "paramodulation" and "eq_resolution" -- the more obvious-looking
    # tokens for paramodulate/reflexivity -- are deliberately NOT chosen
    # here precisely because neither is in either table below (they would
    # make the emitted step come back "unchecked").
    checked = VAMPIRE_CHECKED_RULES | EPROVER_CHECKED_RULES
    for kit_rule, tstp_rule in _KIT_RULE_TO_TSTP.items():
        assert tstp_rule in checked, f"{kit_rule!r} -> {tstp_rule!r} is not a checked TSTP rule"
    assert "paramodulation" not in checked
    assert "eq_resolution" not in checked


def test_kit_rule_to_tstp_covers_every_non_input_rule():
    # Safety net against a future resolution_check.py rule addition silently
    # having no TSTP token at all (to_tstp would KeyError on it instead of
    # refusing cleanly) -- every rule _RULE_ARITY knows about except "input"
    # (handled separately, as a leaf) must have an entry.
    assert set(_KIT_RULE_TO_TSTP) == set(_RULE_ARITY) - {"input"}


# ---------------------------------------------------------------------------
# 4. Symbol sanitisation -- mirrors TestHinwegNonAsciiAndDigitLeadingNames /
#    TestR2ConsistencyAndCollisionAvoidance in tests/test_tptp_problem.py,
#    using the SAME "świątek" / "2008SummerOlympics" example names TPTP
#    would reject unsanitised.
# ---------------------------------------------------------------------------

def test_non_ascii_and_digit_leading_names_sanitise_and_round_trip():
    # "Świątek" -- a non-ASCII predicate name -- and "2008SummerOlympics" --
    # a digit-leading constant -- would both be illegal raw TPTP identifiers
    # (lower_word: [a-z][A-Za-z0-9_]*); to_tstp must not emit them verbatim,
    # and the sanitised derivation must still round-trip to the ORIGINAL
    # kit-level names via apply_reverse_tptp.
    won = Atom("Świątek", [Constant("2008SummerOlympics")])
    C1 = frozenset({won})
    C2 = frozenset({Not(won)})
    steps = (
        ResolutionStep(1, C1, "input"),
        ResolutionStep(2, C2, "input"),
        ResolutionStep(3, frozenset(), "resolve", (1, 2)),
    )
    d = ResolutionDerivation((C1, C2), steps)
    assert verify_resolution_proof(d).ok

    text = to_tstp(d)  # name_map=None -- built fresh from the derivation's own symbols
    assert "Świątek" not in text
    assert "(2008SummerOlympics)" not in text  # not left digit-leading
    assert text.isascii()

    all_literals = [lit for step in d.steps for lit in step.clause]
    _, mapping = _sanitize_for_tptp(all_literals)
    parsed = parse_tstp_derivation(to_tstp(d, name_map=mapping))
    for orig, pstep in zip(d.steps, parsed.steps):
        back = apply_reverse_tptp(pstep.formula, mapping)
        got_clause = _node_to_clause(back)
        assert _is_variant(got_clause, orig.clause)


def test_lowercase_predicate_name_is_case_sanitised_not_identity_mapped():
    # Reviewer-found blocker: a lower-case predicate such as "bar" is
    # TPTP-legal on its own (matches lower_word: [a-z][A-Za-z0-9_]*) but is
    # NOT already in the predicate namespace's own round-trip-safe case (kit
    # predicates are conventionally upper-case-initial, _predicate_base_case)
    # -- so treating it as an untouched identity is unsafe: Node.to_tptp
    # folds only the first character on export, and tptp_input._cap
    # UNCONDITIONALLY upper-cases a parsed predicate's first character on
    # import regardless of what was actually exported, so an identity-mapped
    # "bar" comes back as "Bar" (a DIFFERENT kit-level name), never "bar",
    # via apply_reverse_tptp -- with no error raised anywhere.
    C1 = frozenset({Atom("bar", [a])})
    C2 = frozenset({Not(Atom("bar", [a]))})
    d = ResolutionDerivation((C1, C2), (
        ResolutionStep(1, C1, "input"),
        ResolutionStep(2, C2, "input"),
        ResolutionStep(3, frozenset(), "resolve", (1, 2)),
    ))
    assert verify_resolution_proof(d).ok

    # Hand-derived: the predicate namespace starts empty, so collecting
    # "bar" finds case_fix("bar") == "Bar" != "bar" -> queued for synthesis;
    # finalize's base is case_fix(ascii_safe_base("bar", "p")) == "Bar",
    # whose fold "bar" is not yet reserved by anything else -> token "Bar"
    # itself, no de-collision bump needed.
    extended = _extend_name_map_for_derivation(d, None)
    assert extended.predicate == {"bar": "Bar"}

    # The rendered TEXT is unaffected either way (Node.to_tptp always folds
    # "Bar" back down to "bar") -- the bug was invisible in the forward
    # direction, only on round trip, which is exactly why it went unnoticed.
    text = to_tstp(d)
    assert text == (
        "cnf(c1, plain, bar(a)).\n"
        "cnf(c2, plain, ~(bar(a))).\n"
        "cnf(c3, plain, $false, inference(resolution, [status(thm)], [c1, c2])).\n"
    )

    # Route 1: the kit's own reader must recover the ORIGINAL "bar".
    parsed = parse_tstp_derivation(text)
    for orig, pstep in zip(d.steps, parsed.steps):
        back = apply_reverse_tptp(pstep.formula, extended)
        got_clause = _node_to_clause(back)
        assert _is_variant(got_clause, orig.clause)

    # Route 2: independently re-derived too, not merely parseable.
    premises = _input_premises(d, extended)
    result = check_tstp_derivation(parsed, premises, None, query="refutation")
    assert result.verified, result.error


def test_uppercase_initial_constant_name_is_case_sanitised_not_identity_mapped():
    # The symmetric blocker case for the TERM (function/constant) namespace:
    # an upper-case-initial constant such as "Foo" is TPTP-legal on its own
    # but not already in that namespace's round-trip-safe case (kit
    # constants/functions are conventionally lower-case-initial,
    # _term_base_case) -- and unlike a predicate, tptp_input has NO
    # compensating cap-on-import step for constants AT ALL, so an
    # unconditioned identity here would be silently unrecoverable, not
    # merely differently-cased.
    C1 = frozenset({Atom("P", [Constant("Foo")])})
    C2 = frozenset({Not(Atom("P", [Constant("Foo")]))})
    d = ResolutionDerivation((C1, C2), (
        ResolutionStep(1, C1, "input"),
        ResolutionStep(2, C2, "input"),
        ResolutionStep(3, frozenset(), "resolve", (1, 2)),
    ))
    assert verify_resolution_proof(d).ok

    # Hand-derived exactly as above, mirrored into the term namespace:
    # case_fix("Foo") == "foo" != "Foo" -> queued; finalize's base
    # case_fix(ascii_safe_base("Foo", "n")) == "foo", not yet reserved -> "foo".
    extended = _extend_name_map_for_derivation(d, None)
    assert extended.term == {"Foo": "foo"}

    text = to_tstp(d)
    assert text == (
        "cnf(c1, plain, p(foo)).\n"
        "cnf(c2, plain, ~(p(foo))).\n"
        "cnf(c3, plain, $false, inference(resolution, [status(thm)], [c1, c2])).\n"
    )

    parsed = parse_tstp_derivation(text)
    for orig, pstep in zip(d.steps, parsed.steps):
        back = apply_reverse_tptp(pstep.formula, extended)
        got_clause = _node_to_clause(back)
        assert _is_variant(got_clause, orig.clause)

    premises = _input_premises(d, extended)
    result = check_tstp_derivation(parsed, premises, None, query="refutation")
    assert result.verified, result.error


def test_reuses_a_pre_built_name_map_from_the_problem_export():
    # The motivating use case for the name_map parameter: a caller already
    # exported a TPTP problem for (premises, conclusion) via
    # generate_tptp_problem_with_mapping and now wants a TSTP proof over the
    # SAME clauses to use IDENTICAL symbol spellings.
    premise = Atom("Świątek", [Constant("a")])
    conclusion = Atom("Świątek", [Constant("a")])
    problem_text, mapping = generate_tptp_problem_with_mapping([premise], conclusion)

    C1 = frozenset({premise})
    C2 = frozenset({Not(premise)})
    d = ResolutionDerivation(
        (C1, C2),
        (ResolutionStep(1, C1, "input"),
         ResolutionStep(2, C2, "input"),
         ResolutionStep(3, frozenset(), "resolve", (1, 2))))
    assert verify_resolution_proof(d).ok
    proof_text = to_tstp(d, name_map=mapping)

    # mapping.predicate stores the RAW (pre-fold) token; Node.to_tptp()
    # folds only its first character (tptp_fold_first_letter) -- the same
    # fold _predicate_base_case already forces upper-case-initial for, so
    # this reproduces exactly what both generate_tptp_problem_with_mapping
    # and to_tstp actually printed.
    raw_token = mapping.predicate["Świątek"]
    rendered_token = raw_token[0].lower() + raw_token[1:]
    assert rendered_token in problem_text
    assert rendered_token in proof_text


def test_name_map_missing_a_symbol_is_sanitised_not_passed_through_unsafe():
    # Regression for a real gap: a caller-supplied name_map that simply never
    # saw some symbol the derivation uses must NOT make to_tstp pass that
    # symbol through verbatim when it is TPTP-illegal -- it must be
    # sanitised exactly as a name_map=None call would sanitise it. "9lives"
    # (digit-leading, illegal under TPTP's lower_word grammar) is used by
    # the derivation but absent from a real mapping built over "Foo"/"a"
    # only, via the SAME generate_tptp_problem_with_mapping entry point
    # test_reuses_a_pre_built_name_map_from_the_problem_export exercises.
    _, mapping = generate_tptp_problem_with_mapping(
        [Atom("Foo", [a])], Atom("Foo", [a])
    )
    assert "9lives" not in mapping.term  # the gap this test targets

    nine = Constant("9lives")
    C1 = frozenset({P(nine)})
    C2 = frozenset({Not(P(nine))})
    d = ResolutionDerivation(
        (C1, C2),
        (ResolutionStep(1, C1, "input"),
         ResolutionStep(2, C2, "input"),
         ResolutionStep(3, frozenset(), "resolve", (1, 2))))
    assert verify_resolution_proof(d).ok

    text = to_tstp(d, name_map=mapping)
    assert "(9lives)" not in text  # never emitted verbatim, digit-leading

    # Route 1: the kit's own reader must parse every step's formula back --
    # the exact failure mode the old unconditional passthrough produced
    # silently (formula_text present, formula=None).
    parsed = parse_tstp_derivation(text)
    assert all(step.formula is not None for step in parsed.steps)

    # _extend_name_map_for_derivation is what to_tstp used internally to
    # decide the token for "9lives" -- recomputing it here (same inputs) is
    # the only way a caller could reconstruct that decision to reverse it,
    # since to_tstp itself only returns text, not the extended mapping.
    extended = _extend_name_map_for_derivation(d, mapping)
    for orig, pstep in zip(d.steps, parsed.steps):
        back = apply_reverse_tptp(pstep.formula, extended)
        got_clause = _node_to_clause(back)
        assert _is_variant(got_clause, orig.clause)

    # The caller's own mapping object must be left untouched -- to_tstp only
    # ever extends a COPY, never the mapping the caller still holds a
    # reference to.
    assert "9lives" not in mapping.term
    assert mapping.term == {"a": "a"}
    assert mapping.predicate == {"Foo": "Foo"}

    # Route 2: check_tstp_derivation must independently re-derive the
    # refutation too, not merely parse it.
    premises = _input_premises(d, extended)
    result = check_tstp_derivation(parsed, premises, None, query="refutation")
    assert result.verified, result.error


def test_name_map_missing_a_non_ascii_symbol_is_sanitised_not_passed_through():
    # Same gap, non-ASCII predicate variant (the reviewer's second repro):
    # a name_map covering only "Foo"/"a" must not let a "Świątek" predicate
    # the derivation introduces reach the output un-transliterated.
    _, mapping = generate_tptp_problem_with_mapping(
        [Atom("Foo", [a])], Atom("Foo", [a])
    )
    won = Atom("Świątek", [a])
    C1 = frozenset({won})
    C2 = frozenset({Not(won)})
    d = ResolutionDerivation(
        (C1, C2),
        (ResolutionStep(1, C1, "input"),
         ResolutionStep(2, C2, "input"),
         ResolutionStep(3, frozenset(), "resolve", (1, 2))))
    assert verify_resolution_proof(d).ok

    text = to_tstp(d, name_map=mapping)
    assert "Świątek" not in text
    assert text.isascii()

    parsed = parse_tstp_derivation(text)
    assert all(step.formula is not None for step in parsed.steps)
    extended = _extend_name_map_for_derivation(d, mapping)
    for orig, pstep in zip(d.steps, parsed.steps):
        back = apply_reverse_tptp(pstep.formula, extended)
        got_clause = _node_to_clause(back)
        assert _is_variant(got_clause, orig.clause)


def test_case_variant_names_used_directly_are_disambiguated_not_merged():
    # "Foo" and "foo" both fold to the TPTP identifier "foo" under a plain
    # is-ASCII-and-letter-initial legality test -- but only "Foo" is already
    # in the PREDICATE namespace's own round-trip-safe case (upper-case
    # initial, _predicate_base_case); "foo" is not, so it is no longer
    # treated as an untouched identity (see _collect_name_case_safe) and is
    # routed through synthesis instead, exactly like a genuinely illegal
    # name would be. Hand-derived: predicates start empty; "Foo" collects as
    # an identity (used = {"foo"}, the fold of "Foo"); "foo" fails the case
    # check and queues for synthesis; finalize's case_fix("foo") = "Foo",
    # whose own fold "foo" is already in `used`, so reserve_rendered bumps
    # it to "Foo2" (fold "foo2", not colliding) -- "foo" |-> "Foo2".
    inputs = (frozenset({Atom("Foo", [a])}), frozenset({Atom("foo", [a])}))
    steps = (
        ResolutionStep(1, frozenset({Atom("Foo", [a])}), "input"),
        ResolutionStep(2, frozenset({Atom("foo", [a])}), "input"),
    )
    d = ResolutionDerivation(inputs, steps)
    assert verify_resolution_proof(d).ok  # each restates its own input; nothing to resolve
    text = to_tstp(d)
    assert text == "cnf(c1, plain, foo(a)).\ncnf(c2, plain, foo2(a)).\n"

    # Both routes: the kit's own reader recovers the two ORIGINAL, distinct
    # names -- neither is lost nor conflated with the other.
    extended = _extend_name_map_for_derivation(d, None)
    assert extended.predicate == {"Foo": "Foo", "foo": "Foo2"}
    parsed = parse_tstp_derivation(text)
    for original_name, pstep in zip(("Foo", "foo"), parsed.steps):
        back = apply_reverse_tptp(pstep.formula, extended)
        assert back == Atom(original_name, [a])


def test_symbol_collision_via_seeded_name_map_is_refused_loudly():
    # A case-variant collision that DOES remain genuinely unavoidable (and
    # therefore must still be refused, not disambiguated): a caller-supplied
    # name_map, reused from an unrelated problem export, already carries a
    # case-UNSAFE identity entry -- a residual, pre-existing gap in
    # atp._tptp_problem's own _Renamer.collect (confirmed still present by
    # the assertion below; outside this item's file ownership to fix there,
    # see _name_map_sentinel_nodes' own docstring) that this module cannot
    # close at its source. generate_tptp_problem_with_mapping on a bare
    # Constant("Foo") hands back mapping.term == {"Foo": "Foo"} -- "Foo" is
    # TPTP-legal but upper-case-initial, which _term_base_case says a
    # constant/function name never should be. A derivation that separately
    # introduces the genuinely distinct constant "foo" (lower-case,
    # case-correct, so IT takes to_tstp's own fast identity path
    # unconditionally) folds to the exact same TPTP token as name_map's
    # "Foo" (only the first character is folded) -- and the two are never
    # even compared to each other unless the collision check also looks at
    # name_map's own tokens, not just the derivation's (see
    # _name_map_sentinel_nodes).
    _, mapping = generate_tptp_problem_with_mapping(
        [Atom("P", [Constant("Foo")])], Atom("P", [Constant("Foo")])
    )
    assert mapping.term == {"Foo": "Foo"}  # the pre-existing case-unsafe seed

    inputs = (frozenset({P(Constant("foo"))}), frozenset({Q(Constant("foo"))}))
    steps = (
        ResolutionStep(1, frozenset({P(Constant("foo"))}), "input"),
        ResolutionStep(2, frozenset({Q(Constant("foo"))}), "input"),
    )
    d = ResolutionDerivation(inputs, steps)
    assert verify_resolution_proof(d).ok  # each restates its own input; nothing to resolve
    with pytest.raises(NotImplementedError, match="Foo.*foo|foo.*Foo"):
        to_tstp(d, name_map=mapping)


# ---------------------------------------------------------------------------
# 5. Certification requirement (batch note 2): to_tstp refuses loudly
#    whatever verify_resolution_proof itself does not certify.
# ---------------------------------------------------------------------------

def test_refuses_an_uncertified_derivation():
    # Step 3 claims a bogus resolvent {Q} that no mgu of {P(a)}/{¬P(a)}
    # actually produces -- verify_resolution_proof rejects it, so to_tstp
    # must refuse to serialise it at all.
    inputs = (frozenset({P(a)}), frozenset({Not(P(a))}))
    steps = (
        ResolutionStep(1, frozenset({P(a)}), "input"),
        ResolutionStep(2, frozenset({Not(P(a))}), "input"),
        ResolutionStep(3, frozenset({Q()}), "resolve", (1, 2)),
    )
    d = ResolutionDerivation(inputs, steps)
    assert not verify_resolution_proof(d).ok
    with pytest.raises(ValueError, match="not certified"):
        to_tstp(d)


def test_refuses_a_derivation_with_out_of_order_index():
    # A structurally malformed derivation (index != position) is likewise
    # never certified, so likewise refused.
    d = ResolutionDerivation(
        (frozenset({P(a)}),),
        (ResolutionStep(2, frozenset({P(a)}), "input"),))
    assert not verify_resolution_proof(d).ok
    with pytest.raises(ValueError, match="not certified"):
        to_tstp(d)
