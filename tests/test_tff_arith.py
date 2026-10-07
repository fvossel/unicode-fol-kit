"""Tests for :mod:`unicode_logic_kit.atp._tff_problem` (the single-numeric-sort
typed TFA exporter, C14) and its opt-in integration into the Vampire/E
backends.

Test groups:

* WRITER UNIT TESTS (no external tool) — exact, hand-computed expected TFF
  text for small golden cases; numeric-literal rendering per sort; refusals
  (out-of-fragment nodes, free variables, an invalid ``sort``, an arity
  conflict, a constant-vs-function clash, a name-folding collision) each
  raising the right exception naming the construct.
* BACKEND INTEGRATION (no external tool, monkeypatched subprocess) —
  ``sort=`` takes priority over ``tff=`` in ``vampire_entailment``/
  ``eprover_backend``'s problem-generation helpers, and the ``sort`` route's
  ``TptpNameMap`` genuinely reverse-maps prover output (unlike the
  many-sorted ``tff`` route, which returns no mapping at all).
* LIVE DIFFERENTIAL TESTS (Vampire + E, ``skipif``-gated exactly like
  ``test_vampire_entailment.py``/``test_eprover_zipperposition.py`` already
  gate their own live tests) — a hand-picked battery of linear/simple
  nonlinear arithmetic formulas with textbook truth values, checked against
  the kit's OWN independent arithmetic route (``atp.z3_arith
  .is_valid_arith``/``is_satisfiable_arith``, same sort) as the oracle, then
  run through Vampire/E via the new typed TFA export. A prover's "Theorem"
  must never be reported for a formula ``z3_arith`` refutes, and vice versa;
  ``GaveUp``/``Timeout`` stay UNKNOWN/inconclusive rather than asserted
  against — see ``_classify`` below, which encodes exactly that tolerance.
  For E the battery has one more outcome: an entry with an arithmetic function
  symbol or, under ``sort='real'``, a numeral is REFUSED by name before E runs
  (see the environment note), and the test says which entries those are.
  Includes the flagship $int-vs-$real pin (batch note 3): ``∀x (x > 0 → x ≥
  1)`` is valid over $int, invalid over $real.

Environment note (observed 2026-09, WSL Vampire 5.0.1 / E 3.5.1): Vampire's
default saturation strategy reliably PROVES a valid arithmetic goal (its
Z3-linked theory reasoning activates), but can take much longer than a
short test timeout to positively confirm a genuinely INVALID one (proving
CounterSatisfiable over an infinite domain is not what saturation-based
search is built for) — this is why the invalid-side assertions below accept
UNKNOWN/timeout rather than requiring a decisive CounterSatisfiable, exactly
per the "GaveUp/Timeout stays UNKNOWN" rule. E 3.5.1 does not do TFA arithmetic
at all (measured): ANY use of the ``$sum``/``$difference``/... built-ins (even
fully ground, e.g. ``3 + 4 = 7``) makes E's own type-checker report ``terms
...: $i and ...: $int should have the same sort`` and abort before reaching an
SZS status, because it types them as functions into the individuals; it reads
a ``$real`` literal only approximately (``0.1 = 0.1000001`` is a theorem for
it); and it reads ``$less`` and the other comparisons as predicates that it
never evaluates, so it answers ``GaveUp`` for whatever needs their meaning.
The writer's type declarations are correct TFA (Vampire proves the same
texts), so the E route refuses by name what E cannot read or reads wrongly (an
arithmetic function symbol, a numeral under ``sort='real'``) and asks E the rest,
where ``_classify`` accepts GaveUp/Timeout as an honest "don't know". One
decisive proof that needs no arithmetic is still asserted to confirm the route's
wiring end-to-end.
"""

import shutil
import subprocess

import pytest

from unicode_logic_kit.fol.msflparser import MSFLParser
from unicode_logic_kit.fol.nodes import (
    Atom, And, Constant, Function, Implies, Not, Number, Or, Quantifier, Variable,
)
from unicode_logic_kit.atp._tff_problem import (
    generate_tff_arith_problem, formula_to_tff_arith, TFA_SORT_TOKENS,
)
from unicode_logic_kit.atp.z3_arith import is_valid_arith, is_satisfiable_arith
from unicode_logic_kit.atp import vampire_entailment as _ve
from unicode_logic_kit.atp import eprover_backend as _eb
from unicode_logic_kit.atp.vampire_entailment import (
    _generate_vampire_input, check_logical_entailment_vampire,
    check_entailment_vampire_detailed,
)
from unicode_logic_kit.atp.eprover_backend import (
    _generate_tptp_problem as _eprover_generate_input,
    check_entailment_eprover_detailed, eprover_available, EProverBackend,
)

FOL = MSFLParser()
MODAL = MSFLParser(modal=True)
MSFOL = MSFLParser(many_sorted=True)


# =============================================================================
# Writer unit tests — exact, hand-computed expected text
# =============================================================================

def test_generate_tff_arith_problem_exact_text_real():
    """Hand-checked: every quantifier carries ``: $real``, ``+``/``>`` render
    as ``$sum``/``$greater`` (reused verbatim from Function.TPTP_ARITH_OPS /
    Atom.PREFIX_PREDS_TPTP — no new arithmetic mapping is invented here)."""
    conclusion = FOL.parse("∀x (x > 0 → x + 1 > 1)")
    text, name_map = generate_tff_arith_problem([], conclusion, sort="real")
    lines = [ln for ln in text.splitlines() if ln.strip()]
    assert lines == [
        "tff(goal, conjecture, (![X: $real]: "
        "($greater(X,0.0) => $greater($sum(X,1.0),1.0))) )."
    ]
    assert name_map.predicate == {}
    assert name_map.term == {}


def test_generate_tff_arith_problem_exact_text_int_with_declarations():
    """Constants/predicates get declared over $int; ordering is func, const,
    pred, alphabetically within each (matches atp.tptp_tff's own ordering)."""
    premises = [FOL.parse("Prime(seven) ∧ seven + 3 = 10")]
    conclusion = FOL.parse("Prime(seven)")
    text, name_map = generate_tff_arith_problem(premises, conclusion, sort="int")
    lines = [ln for ln in text.splitlines() if ln.strip()]
    assert lines == [
        "tff(const_decl_1, type, seven: $int ).",
        "tff(pred_decl_2, type, prime: $int > $o ).",
        "tff(premise_1, axiom, (prime(seven) & ($sum(seven,3) = 10)) ).",
        "tff(goal, conjecture, prime(seven) ).",
    ]
    # Both names were already TPTP-legal, so the map records them unchanged
    # (mirrors atp._tptp_problem's "already-legal name maps to itself" rule).
    assert name_map.predicate == {"Prime": "Prime"}
    assert name_map.term == {"seven": "seven"}


def test_binary_predicate_and_function_product_domain():
    conclusion = FOL.parse("∀x (Between(zero, x, ten) ∨ add(x, x) = x)")
    text, _ = generate_tff_arith_problem([], conclusion, sort="int")
    lines = text.splitlines()
    assert "tff(func_decl_1, type, add: ($int * $int) > $int )." in lines
    assert "tff(pred_decl_4, type, between: ($int * $int * $int) > $o )." in lines


def test_no_premises_is_just_the_conjecture():
    conclusion = FOL.parse("∀x ∃y (y = x + 1)")
    text, _ = generate_tff_arith_problem([], conclusion, sort="int")
    lines = [ln for ln in text.splitlines() if ln.strip()]
    assert lines == [
        "tff(goal, conjecture, (![X: $int]: (?[Y: $int]: (Y = $sum(X,1)))) )."
    ]


def test_formula_to_tff_arith_matches_generate_for_single_formula():
    f = FOL.parse("∀x (x ≥ 0 ∨ x < 0)")
    assert (formula_to_tff_arith(f, sort="real")
            == "(![X: $real]: ($greatereq(X,0.0) | $less(X,0.0)))")


class TestNumericLiteralRendering:
    """Every case wraps the literal in '∀x (...)' -- a bare 'x = 3' has a
    genuinely free 'x' (see test_refuses_free_variable), which is beside
    the point being tested here (how a Number node itself renders)."""

    def test_int_whole_number_renders_plain(self):
        text = formula_to_tff_arith(FOL.parse("∀x (x = 3)"), sort="int")
        assert text == "(![X: $int]: (X = 3))"

    def test_real_whole_number_gets_decimal_point(self):
        # 3 (no decimal point in the source) still renders as 3.0 for $real —
        # TPTP's $real literal grammar requires a decimal point.
        text = formula_to_tff_arith(FOL.parse("∀x (x = 3)"), sort="real")
        assert text == "(![X: $real]: (X = 3.0))"

    def test_real_decimal_literal_renders_exactly(self):
        text = formula_to_tff_arith(FOL.parse("∀x (x = 1.5)"), sort="real")
        assert text == "(![X: $real]: (X = 1.5))"

    def test_int_refuses_a_decimal_point_literal(self):
        with pytest.raises(NotImplementedError, match=r"1\.5"):
            formula_to_tff_arith(FOL.parse("∀x (x = 1.5)"), sort="int")

    def test_negative_number_node_renders_with_sign(self):
        # The parser has no unary minus, so build the Number node directly
        # (mirrors how negative literals are tested elsewhere in the kit).
        f = Atom("=", [Variable("x"), Number(-2)])
        f = Quantifier("∀", Variable("x"), Or(f, Not(f)))
        assert "-2" in formula_to_tff_arith(f, sort="int")


# =============================================================================
# Refusals
# =============================================================================

def test_refuses_invalid_sort_string():
    with pytest.raises(ValueError, match="'complex'"):
        formula_to_tff_arith(FOL.parse("x = x"), sort="complex")


def test_refuses_free_variable():
    with pytest.raises(ValueError, match="free variable"):
        formula_to_tff_arith(FOL.parse("x > 0"))


def test_refuses_sorted_quantifier_by_name():
    """A SortedQuantifier introduces a genuinely different (not necessarily
    numeric) sort -- refused rather than guessed at (see module docstring's
    'Design rule')."""
    with pytest.raises(NotImplementedError, match="SortedQuantifier"):
        formula_to_tff_arith(MSFOL.parse("∀x:Human Mortal(x)"))


def test_refuses_modal_node_by_name():
    with pytest.raises(NotImplementedError, match="Box"):
        formula_to_tff_arith(MODAL.parse("□P(a)"))


def test_refuses_count_by_name():
    with pytest.raises(NotImplementedError, match="Count"):
        formula_to_tff_arith(FOL.parse("∃≥2 x P(x)"))


def test_refuses_arity_conflict_naming_the_predicate():
    node = And(Atom("P", [Constant("a")]),
              Atom("P", [Constant("a"), Constant("b")]))
    with pytest.raises(ValueError, match="'P'"):
        generate_tff_arith_problem([], node)


def test_refuses_constant_vs_function_name_clash():
    """The bug this test pins: formula_to_tff_arith must run the SAME
    signature validation generate_tff_arith_problem does, even though it
    renders no type declarations -- a name used as both a 0-ary Constant and
    a Function elsewhere is unsound either way (see module docstring's
    _CONST_VS_FUNCTION contract)."""
    node = And(Atom("P", [Constant("a")]),
              Atom("Q", [Function("a", [Constant("b")])]))
    with pytest.raises(ValueError, match="'a'"):
        formula_to_tff_arith(node)
    with pytest.raises(ValueError, match="'a'"):
        generate_tff_arith_problem([], node)


def test_refuses_predicate_name_folding_collision():
    """'Foo' and 'foo' both fold to the TFF identifier 'foo' -- the grammar
    itself cannot produce this (predicate names are always uppercase-initial
    at parse time), so the nodes are constructed directly, mirroring
    test_tptp_tff.py's identical collision test."""
    with pytest.raises(NotImplementedError, match="Foo.*foo|foo.*Foo"):
        generate_tff_arith_problem(
            [Atom("Foo", [Constant("a")])], Not(Atom("foo", [Constant("a")])))


def test_predicate_vs_function_cross_namespace_collision_is_renamed_and_recorded():
    """'Price' (a predicate) and 'price' (a function) both fold to the TFF
    identifier 'price'. TFF has ONE flat symbol table: emitting both
    'tff(func_decl_1, type, price: $real > $real ).' and
    'tff(pred_decl_2, type, price: $real > $o ).' is two conflicting type
    declarations for one identifier, which real Vampire/E builds reject
    outright ('Non-boolean term price(X0) of sort $real is used in a
    formula context') before reaching any SZS status -- confirmed live
    against WSL Vampire 5.0.1 and WSL E 3.5.1 during triage. This used to be
    REFUSED at export time; the writers now rename the TERM side (the function
    or constant, never the predicate) to '<name>_term' and record it in the
    returned TptpNameMap, exactly as the fof and TF0 writers do.

    Hand-derived: predicate Price -> 'price'; function price -> 'price'; the
    function is the term side, so it becomes 'price_term'. Functions are
    declared before predicates; the goal is the lone formula."""
    formula = FOL.parse("∀x (Price(x) → price(x) = 1)")
    text, name_map = generate_tff_arith_problem([], formula, sort="real")
    assert text == (
        "tff(func_decl_1, type, price_term: $real > $real ).\n"
        "tff(pred_decl_2, type, price: $real > $o ).\n"
        "tff(goal, conjecture, (![X: $real]: (price(X) => (price_term(X) = 1.0))) ).\n")
    assert name_map.term == {"price": "price_term"}
    assert name_map.predicate == {"Price": "Price"}
    assert formula_to_tff_arith(formula, sort="real") == (
        "(![X: $real]: (price(X) => (price_term(X) = 1.0)))")


def test_predicate_vs_constant_cross_namespace_collision_is_renamed_and_recorded():
    """Same clash as the Price/price test above, but against a 0-ary Constant
    rather than a Function. Hand-derived: constants are declared in the sorted
    order of their (sanitised) names, 'c1' < 'price_term', then predicates
    'price', 'q'."""
    node = And(Atom("Price", [Constant("c1")]), Atom("Q", [Constant("price")]))
    text, name_map = generate_tff_arith_problem([], node)
    assert text == (
        "tff(const_decl_1, type, c1: $real ).\n"
        "tff(const_decl_2, type, price_term: $real ).\n"
        "tff(pred_decl_3, type, price: $real > $o ).\n"
        "tff(pred_decl_4, type, q: $real > $o ).\n"
        "tff(goal, conjecture, (price(c1) & q(price_term)) ).\n")
    assert name_map.term == {"c1": "c1", "price": "price_term"}


def test_the_flat_table_backstop_still_refuses_a_clash_the_rename_did_not_see():
    """_check_no_predicate_function_collision is now a BACKSTOP behind
    _separate_term_names; calling _analyze directly on an unseparated pair
    (what the entry points can no longer produce) must still refuse by name."""
    from unicode_logic_kit.atp._tff_problem import _analyze
    node = And(Atom("Price", [Constant("c1")]), Atom("Q", [Constant("price")]))
    with pytest.raises(NotImplementedError, match="Price.*price|price.*Price"):
        _analyze([node])


# =============================================================================
# Backend integration (no external tool; monkeypatched subprocess)
# =============================================================================

def test_generate_vampire_input_sort_route_produces_typed_text():
    text = _generate_vampire_input([], FOL.parse("∀x (x > 0 → x ≥ 1)"), sort="int")
    assert text.startswith("tff(")
    assert "$int" in text
    assert "$greater" in text and "$greatereq" in text


def test_generate_vampire_input_sort_takes_priority_over_tff():
    """sort= wins even when tff=True/False is ALSO passed -- an explicit,
    documented priority (see _generate_vampire_input's docstring), not an
    accidental one."""
    conclusion = FOL.parse("∀x (x > 0 → x ≥ 1)")
    text_a = _generate_vampire_input([], conclusion, sort="int", tff=False)
    text_b = _generate_vampire_input([], conclusion, sort="int", tff=True)
    assert text_a == text_b
    assert "$int" in text_a


def test_generate_vampire_input_without_sort_is_unaffected():
    """The default (sort=None) path is byte-identical to before this item --
    a plain classical formula still exports as fof, not tff."""
    premises = [FOL.parse("∀x (Human(x) → Mortal(x))")]
    conclusion = FOL.parse("Mortal(socrates)")
    text = _generate_vampire_input(premises, conclusion)
    assert text.startswith("fof(")


def test_eprover_generate_input_sort_route():
    text = _eprover_generate_input([], FOL.parse("∀x (x * 2 = x + x)"), sort="real")
    assert text.startswith("tff(")
    assert "$real" in text


def test_check_entailment_vampire_detailed_sort_route_reverse_maps_output(monkeypatch):
    """The sort= route's name_map is a genuine TptpNameMap, so a non-ASCII
    constant comes back reverse-mapped in output_excerpt -- as it does on the
    many-sorted tff route (see test_tptp_tff.py's 'is reverse mapped' test),
    which keeps its name map as well since 0.30.0."""
    def fake_spawn(input_str, vampire_path, timeout=30, use_wsl=False, extra_args=()):
        assert "tff(" in input_str
        assert "theta" in input_str    # the writer already sanitised θ -> theta
        stdout = (
            "tff(f1,axiom,(theta > 0.0)).\n"
            "% SZS status Theorem for problem\n"
        )
        return stdout, False

    monkeypatch.setattr(_ve, "_spawn_vampire", fake_spawn)
    conclusion = Atom(">", [Constant("θ"), Number(0)])
    result = check_entailment_vampire_detailed(
        [], conclusion, vampire_path="unused", sort="real")
    assert result["status"] == "proved"
    assert "theta" not in result["output_excerpt"]
    assert "θ" in result["output_excerpt"]


def test_check_entailment_eprover_detailed_sort_route_reverse_maps_output(monkeypatch):
    # sort='int': E reads an integer literal exactly, but a numeral under sort='real' is refused
    # (E reads a $real literal approximately), so the numeral 0 is an integer here.
    def fake_run(problem, command, args, use_wsl, timeout_s):
        assert "tff(" in problem
        assert "theta" in problem
        return ("tff(f1,axiom,($greater(theta,0))).\n"
                "# SZS status Theorem for problem\n"), False

    monkeypatch.setattr(_eb, "_run_tptp_prover", fake_run)
    conclusion = Atom(">", [Constant("θ"), Number(0)])
    result = check_entailment_eprover_detailed(
        [], conclusion, command="unused", sort="int")
    assert result["status"] == "proved"
    assert "theta" not in result["raw"]
    assert "θ" in result["raw"]


def test_tptp_szs_backend_decide_reads_sort_option(monkeypatch):
    """EProverBackend.decide forwards **options, so sort= reaches
    generate_tff_arith_problem through the SAME **options channel other
    backends use for e.g. frame= (see ProverBackend.decide's docstring)."""
    captured = {}

    def fake_generate(premises, conclusion, sort="real"):
        captured["sort"] = sort
        return "tff(goal, conjecture, (X > 0.0)) .\n", None

    def fake_discover(name, env_var):
        return ("eprover", False)

    def fake_run(problem, command, args, use_wsl, timeout_s):
        return "# SZS status Theorem for problem\n", False

    monkeypatch.setattr(_eb, "generate_tff_arith_problem", fake_generate)
    monkeypatch.setattr(_eb, "_discover", fake_discover)
    monkeypatch.setattr(_eb, "_run_tptp_prover", fake_run)
    monkeypatch.setattr(_eb, "_binary_version", lambda *a, **k: None)

    backend = EProverBackend()
    # sort='int': a numeral under sort='real' is refused for E (see the module docstring).
    verdict = backend.decide(FOL.parse("x > 0"), timeout=1000, sort="int")
    assert captured["sort"] == "int"
    assert verdict.status == "proved"


# =============================================================================
# Live differential tests -- Vampire + E, skipif-gated
# =============================================================================

def _wsl_vampire_ok() -> bool:
    try:
        result = subprocess.run(["wsl.exe", "vampire", "--version"],
                                capture_output=True, text=True, timeout=20)
        return result.returncode == 0 and "Vampire" in result.stdout
    except Exception:  # noqa: BLE001 -- any failure means "not available"
        return False


_VAMPIRE = shutil.which("vampire")
_WSL_VAMPIRE = _wsl_vampire_ok()
_HAVE_VAMPIRE = _VAMPIRE is not None or _WSL_VAMPIRE


def _vampire_kwargs():
    if _VAMPIRE is not None:
        return dict(vampire_path=_VAMPIRE, use_wsl=False)
    return dict(vampire_path="vampire", use_wsl=True)


def _classify(status: str, expected_valid: bool, label: str) -> None:
    """The one invariant every live-prover result must satisfy (batch note
    1): 'Theorem' is never reported for a z3_arith-invalid formula, and
    'CounterSatisfiable'/refuted is never reported for a z3_arith-valid one.
    Anything else (unknown/timeout/error/GaveUp) is an honest "don't know"
    and asserts nothing.
    """
    if status == "proved":
        assert expected_valid, f"{label}: prover said Theorem but z3_arith says invalid"
    elif status == "refuted":
        assert not expected_valid, f"{label}: prover said CounterSatisfiable but z3_arith says valid"
    # else: unknown / error / timeout -- no assertion, honest "don't know".


# Battery: (formula text, sort, expected z3_arith validity, label, fast).
# Every expected value is worked out BY HAND (see each comment) and
# cross-checked against atp.z3_arith.is_valid_arith below, independently of
# anything this exporter does -- the actual "second, independent route"
# test_oracle asks for. ``fast`` marks an entry Vampire's DEFAULT saturation
# strategy is observed (2026-09, WSL Vampire 5.0.1) to decide within a few
# seconds; it is False for the one genuinely nonlinear entry, which Vampire
# still hasn't decided after 40s under default settings even though it IS
# valid -- proving a real-domain nonlinear goal isn't what saturation-based
# search is built for by default (see module docstring); it still
# participates in the tolerant '_classify' check below (never wrongly
# REFUTED), just not in the "must be positively confirmed" one.
_BATTERY = [
    # x*2 = x+x is a true arithmetic identity, both sorts.
    ("∀x (x * 2 = x + x)", "real", True, "doubling identity (real)", True),
    ("∀x (x * 2 = x + x)", "int", True, "doubling identity (int)", True),
    # Every number has a successor, both sorts.
    ("∀x ∃y (y = x + 1)", "real", True, "successor exists (real)", True),
    ("∀x ∃y (y = x + 1)", "int", True, "successor exists (int)", True),
    # A square is never negative -- true, nonlinear, over the reals (the
    # kind of goal Z3's nlsat is known-complete for) -- see 'fast' above.
    ("∀x (x * x ≥ 0)", "real", True, "square is nonnegative (nonlinear, real)", False),
    # Transitivity of strict order.
    ("∀x ∀y ∀z ((x < y ∧ y < z) → x < z)", "real", True, "transitivity of <", True),
    # THE FLAGSHIP $int-vs-$real pin (batch note 3): every integer greater
    # than 0 is at least 1 -- true over the integers (no integer strictly
    # between 0 and 1), false over the reals (x = 0.5 is a counterexample).
    ("∀x (x > 0 → x ≥ 1)", "int", True, "int has no gap between 0 and 1", True),
    ("∀x (x > 0 → x ≥ 1)", "real", False, "real DOES have a gap between 0 and 1", False),
    # A false identity.
    ("∀x (x + 1 = x)", "real", False, "x+1=x is never true", False),
]


#: The battery entries E is asked, worked out by hand. Every other entry has an arithmetic function
#: symbol (``+ - * /``: E 3.5.1 stops with a type error on one) or, under ``sort='real'``, a numeral
#: (E reads a ``$real`` literal approximately), and is refused by name. Transitivity of ``<`` has
#: neither; ``x > 0 → x ≥ 1`` has the integer literals 0 and 1, which E reads exactly under
#: ``sort='int'``.
_E_IS_ASKED = {"transitivity of <", "int has no gap between 0 and 1"}


def _e_refuses(label: str) -> bool:
    return label not in _E_IS_ASKED


@pytest.mark.skipif(not _HAVE_VAMPIRE, reason="no Vampire binary reachable (native or WSL)")
class TestVampireLiveDifferential:
    @pytest.mark.parametrize("text, sort, expected, label, fast", _BATTERY)
    def test_battery_agrees_with_z3_arith(self, text, sort, expected, label, fast):
        f = FOL.parse(text)
        # The oracle: an entirely independent route (atp.z3_arith), decided
        # BEFORE looking at what Vampire says.
        assert is_valid_arith(f, sort=sort) is expected, f"battery entry mislabelled: {label}"
        result = check_entailment_vampire_detailed(
            [], f, timeout=8 if fast else 3, sort=sort, **_vampire_kwargs())
        _classify(result["status"], expected, f"vampire: {label}")

    def test_valid_fast_cases_are_positively_confirmed(self):
        """Beyond '_classify's one-directional tolerance: every VALID, FAST
        entry in the battery must come back decisively proved, not merely
        'not-refuted' -- Vampire's own Z3-linked theory reasoning is known
        (see module docstring) to close these quickly."""
        for text, sort, expected, label, fast in _BATTERY:
            if not (expected and fast):
                continue
            f = FOL.parse(text)
            result = check_entailment_vampire_detailed(
                [], f, timeout=8, sort=sort, **_vampire_kwargs())
            assert result["status"] == "proved", f"{label}: {result}"
            assert result["szs_status"] == "Theorem", f"{label}: {result}"

    def test_mixed_arithmetic_and_uninterpreted_predicate(self):
        """An uninterpreted predicate (Prime) over the SAME numeric sort as
        the arithmetic facts -- z3_arith.is_valid_arith agrees this is valid
        (Prime(seven) is asserted, so it trivially follows), demonstrating
        the single-sort design does not stop ordinary predicates from
        coexisting with arithmetic (see module docstring)."""
        f = FOL.parse("(Prime(seven) ∧ seven + 3 = 10) → Prime(seven)")
        assert is_valid_arith(f, sort="int") is True
        result = check_entailment_vampire_detailed([], f, timeout=8, sort="int", **_vampire_kwargs())
        assert result["status"] == "proved", result

    def test_check_logical_entailment_vampire_bool_route_with_sort(self):
        """The original bool-returning entry point also accepts sort=."""
        f = FOL.parse("∀x (x * 2 = x + x)")
        assert check_logical_entailment_vampire([], f, sort="real", **_vampire_kwargs()) is True


@pytest.mark.skipif(not eprover_available(), reason="no eprover binary found")
class TestEProverLiveDifferential:
    def test_route_wiring_works_end_to_end(self):
        """A decisive proof NOT stressing E's arithmetic engine (see module
        docstring's environment note) -- confirms the whole pipeline
        (typed TFA export -> E subprocess -> SZS parse -> reverse-mapped
        Verdict) works with a real E, independent of E's own arithmetic
        completeness."""
        f = FOL.parse("∀x (P(x) → P(x))")
        result = check_entailment_eprover_detailed([], f, sort="int", timeout=10)
        assert result["status"] == "proved", result
        assert result["szs_status"] == "Theorem"

    @pytest.mark.parametrize("text, sort, expected, label, fast", _BATTERY)
    def test_battery_never_disagrees_with_z3_arith(self, text, sort, expected, label, fast):
        """Weaker than the Vampire battery test: E does no arithmetic (see module
        docstring), so GaveUp is common and tolerated -- but E must NEVER
        positively contradict the z3_arith oracle. An entry E cannot read is refused
        by name instead (see ``_e_refuses``)."""
        f = FOL.parse(text)
        if _e_refuses(label):
            with pytest.raises(NotImplementedError, match="eprover"):
                check_entailment_eprover_detailed([], f, sort=sort, timeout=8)
            return
        result = check_entailment_eprover_detailed([], f, sort=sort, timeout=8)
        _classify(result["status"], expected, f"eprover: {label}")

    @pytest.mark.parametrize("text, sort, operator", [
        ("∀x (x * 2 = x + x)", "int", "'*'"),
        ("∀x ∃y (y = x + 1)", "real", "'+'"),
        ("∀x (x + 1 = x)", "real", "'+'"),
    ])
    def test_an_arithmetic_function_is_refused_by_name_and_is_unknown_unsupported(
            self, text, sort, operator):
        """E 3.5.1 stops with a type error on every ``$sum``/``$product`` (measured), so the
        route says what it cannot read: ``unknown`` / ``unsupported`` naming the operator,
        not an infrastructure failure."""
        verdict = EProverBackend().decide(FOL.parse(text), timeout=8000, sort=sort)
        assert (verdict.status, verdict.reason) == ("unknown", "unsupported"), verdict
        assert operator in verdict.detail and "E 3.5.1" in verdict.detail

    def test_a_real_numeral_is_refused_because_e_reads_a_real_literal_approximately(self):
        """Hand-derived: ``0.1`` and ``0.1000001`` are two different reals, and ``0.1 = 0.1000001``
        is not valid; E 3.5.1 proves it (measured), so the route must not hand it over."""
        goal = Atom("=", [Number(0.1), Number(0.1000001)])
        verdict = EProverBackend().decide(goal, timeout=8000, sort="real")
        assert (verdict.status, verdict.reason) == ("unknown", "unsupported"), verdict
        assert "0.1" in verdict.detail and "sort='real'" in verdict.detail

    def test_backend_registry_decide_with_sort_live(self):
        backend = EProverBackend()
        verdict = backend.decide(FOL.parse("∀x (P(x) → P(x))"), timeout=10000, sort="int")
        assert verdict.status == "proved", verdict.detail
