"""Tests for :mod:`unicode_fol_kit.atp.tptp_tff` (the native TF0 writer) and
its opt-in integration into the Vampire/E backends.

Test groups:

* WRITER UNIT TESTS (no external tool) — exact, hand-computed expected TFF
  text for small golden cases (never derived by running the writer and
  copying its own output back in); ``SortedCount``'s typed distinct-
  witnesses lowering, hand-expanded; refusals (out-of-fragment nodes, free
  variables, arithmetic operators, sort/name-folding collisions) each
  raising the right exception naming the construct.
* ROUND TRIP — ``parse_tff_problem(generate_tff_problem(f)) == f`` for a
  battery of golden many-sorted formulas (the writer/reader pairing).
* BACKEND INTEGRATION (no external tool) — :func:`problem_needs_tff`'s
  auto-select signal, and that ``vampire_entailment``/``eprover_backend``
  actually route through it (or a forced ``tff=`` override).
* LIVE DIFFERENTIAL TESTS (Vampire + E, ``skipif``-gated exactly like
  ``test_vampire_entailment.py``/``test_eprover_zipperposition.py`` already
  gate their own live tests) — the TF0 route and the classical guard-
  predicate ``fof`` route must agree on the SAME SZS verdict for an ordinary
  battery of sorted entailments, INCLUDING one where the guard/type
  threading through a function symbol is load-bearing ("sort-relativisation
  matters"), AND on a formula whose validity rests purely on sort
  non-emptiness (no witness constant of the sort anywhere in the problem).
  That last pair of tests used to be a DELIBERATE non-agreement pin: TF0
  quantifiers range over non-empty types by TPTP semantics (matching this
  kit's own many-sorted model theory — see ``semantics/modelfinder.py``'s
  "Each sort gets a non-empty universe"), but the guard-predicate ``fof``
  route did not add a matching non-emptiness axiom, so the two routes
  provably DISAGREED there — a known gap this file's C2 module explicitly
  left unfixed (``SortedQuantifier._relativize``/``to_fol`` core behaviour
  shared by ~29 call sites, out of that item's scope). Roadmap item S1
  closed that gap kit-wide (``unicode_fol_kit.fol._msfl_nodes
  .nonempty_sort_axioms``, added by :func:`atp._tptp_problem
  .generate_tptp_problem_with_mapping` — the shared builder both
  ``vampire_entailment``'s and ``eprover_backend``'s ``fof`` route already
  used) — see :mod:`atp._tptp_problem`'s own module docstring — so those two
  tests now assert AGREEMENT like every other test in this group.
"""

import shutil
import subprocess

import pytest

from unicode_fol_kit import MSFLParser
from unicode_fol_kit.fol.nodes import (
    Atom, And, Constant, Function, Iff, Implies, Not, Number, Or, Quantifier,
    SortedCardinality, SortedConstant, SortedCount, SortedQuantifier, Variable,
    Box,
)
from unicode_fol_kit.fol.signature import Signature, PredicateDecl, FunctionDecl, ConstantDecl
from unicode_fol_kit.fol.tptp_input import parse_tff_problem
from unicode_fol_kit.atp.tptp_tff import (
    generate_tff_problem, formula_to_tff, infer_tff_signature,
    problem_needs_tff, TFF_INDIVIDUAL_SORT,
)
from unicode_fol_kit.atp import vampire_entailment as _ve
from unicode_fol_kit.atp import eprover_backend as _eb
from unicode_fol_kit.atp.vampire_entailment import (
    _generate_vampire_input, check_logical_entailment_vampire,
    check_entailment_vampire_detailed,
)
from unicode_fol_kit.atp.eprover_backend import (
    _generate_tptp_problem as _eprover_generate_input,
    check_entailment_eprover_detailed, eprover_available,
)

MSFOL = MSFLParser(many_sorted=True)
FOL = MSFLParser()


# =============================================================================
# Writer unit tests — exact, hand-computed expected text
# =============================================================================

def test_generate_tff_problem_socrates_syllogism_exact_text():
    """Hand-checked: sorts/functions/constants/predicates each render
    alphabetically within their own section, sorts -> funcs -> consts ->
    preds -> premises -> goal (declaration-before-use ordering, matching
    casl_export.to_casl_spec's own convention)."""
    premises = [MSFOL.parse("∀x:Human Mortal(x)"), MSFOL.parse("Human(socrates:Human)")]
    conclusion = MSFOL.parse("Mortal(socrates:Human)")
    text = generate_tff_problem(premises, conclusion)
    lines = [ln for ln in text.splitlines() if ln.strip()]
    assert lines == [
        "tff(sort_decl_1, type, human: $tType ).",
        "tff(const_decl_2, type, socrates: human ).",
        "tff(pred_decl_3, type, human: human > $o ).",
        "tff(pred_decl_4, type, mortal: human > $o ).",
        "tff(premise_1, axiom, (![X: human]: mortal(X)) ).",
        "tff(premise_2, axiom, human(socrates) ).",
        "tff(goal, conjecture, mortal(socrates) ).",
    ]


def test_generate_tff_problem_binary_predicate_product_domain():
    """A 2-ary predicate's TYPE needs the parenthesised product domain
    (no inner padding -- _render_map_type joins with " * " but does not pad
    the surrounding parens)."""
    premises = [MSFOL.parse("Owns(alice:Human, rex:Dog)")]
    conclusion = MSFOL.parse("Owns(alice:Human, rex:Dog)")
    text = generate_tff_problem(premises, conclusion)
    assert "tff(pred_decl_5, type, owns: (human * dog) > $o )." in text.splitlines()


def test_generate_tff_problem_no_premises_is_just_the_conjecture():
    """Every symbol still gets its own type declaration even when every sort
    involved is the implicit $i (TFF requires an explicit type per symbol,
    unlike untyped fof) -- an entirely classical, unsorted formula routed
    through the tff writer still renders correctly, at $i throughout."""
    conclusion = FOL.parse("P(socrates) ∨ ¬P(socrates)")
    text = generate_tff_problem([], conclusion)
    lines = [ln for ln in text.splitlines() if ln.strip()]
    assert lines == [
        "tff(const_decl_1, type, socrates: $i ).",
        "tff(pred_decl_2, type, p: $i > $o ).",
        "tff(goal, conjecture, (p(socrates) | ~(p(socrates))) ).",
    ]


def test_formula_to_tff_plain_quantifier_uses_dollar_i():
    """A plain (unsorted) Quantifier renders as an explicitly-$i-typed
    variable -- TPTP's own "no type given" default, made explicit."""
    node = Quantifier("∀", Variable("x"), Atom("P", [Variable("x")]))
    assert formula_to_tff(node) == "(![X: $i]: p(X))"


def test_formula_to_tff_sorted_quantifier_and_equality():
    node = SortedQuantifier(
        "∀", Variable("x"), "Human",
        Iff(Atom("Mortal", [Variable("x")]), Not(Atom("Immortal", [Variable("x")]))))
    assert formula_to_tff(node) == "(![X: human]: (mortal(X) <=> ~(immortal(X))))"


def test_formula_to_tff_sorted_count_at_least_two_hand_expanded():
    """∃≥2 x:Human Mortal(x) -- "at least 2 distinct Humans are Mortal" --
    hand-expanded: ∃x0:Human ∃x1:Human (Mortal(x0) ∧ Mortal(x1) ∧ x0≠x1),
    witnesses TYPED to the SAME sort (not guard-atom-restricted -- the whole
    point of the native encoding). Fresh witness names are "x_0"/"x_1"
    (Count._expand's own naming scheme, reused here), upper-cased for TPTP.
    """
    node = MSFOL.parse("∃≥2 x:Human Mortal(x)")
    assert isinstance(node, SortedCount)
    text = formula_to_tff(node)
    assert text == (
        "(?[X_0: human]: (?[X_1: human]: "
        "((mortal(X_0) & mortal(X_1)) & X_0 != X_1)))"
    )


def test_formula_to_tff_sorted_count_exactly_one_hand_expanded():
    """∃=1 x:Human Mortal(x) = at_least(1) ∧ ¬at_least(2); the SAME shared
    "avoid" name pool as at_least(1) is threaded into at_least(2), so its
    fresh witnesses continue "x_1"/"x_2" rather than restarting at "x_0"."""
    node = MSFOL.parse("∃=1 x:Human Mortal(x)")
    text = formula_to_tff(node)
    assert text == (
        "((?[X_0: human]: mortal(X_0)) & "
        "~((?[X_1: human]: (?[X_2: human]: "
        "((mortal(X_1) & mortal(X_2)) & X_1 != X_2)))))"
    )


def test_infer_tff_signature_pins_every_argument_position():
    """Unlike Signature.from_formulas (which leaves arg_sorts=None
    everywhere), every argument/result position here is pinned -- None only
    where the formulas never connect it to a declared sort (an implicit $i).

    father_of's RESULT sort is a genuinely SEPARATE union-find slot from its
    own argument slot (see module docstring) -- a formula that only ever
    applies father_of to a Human and only ever applies Mortal to
    father_of(...) does NOT by itself pin father_of's result (hand-verified:
    it stays None/$i, since nothing else in a formula that small connects it
    to a concrete sort). Adult's OWN direct sorted binder ("∀y:Human
    Adult(y)") is what closes the loop here: Adult's argument slot is
    unioned with BOTH y (directly Human) and father_of(x)'s result, which is
    what pins father_of's result to Human too -- multi-occurrence
    unification across the whole batch, not single-position inference.
    """
    formulas = [
        MSFOL.parse("∀x:Human Adult(father_of(x))"),
        MSFOL.parse("∀y:Human Adult(y)"),
        MSFOL.parse("Human(alice:Human)"),
    ]
    sig = infer_tff_signature(formulas)
    assert sig == Signature(
        predicates={"Adult": PredicateDecl("Adult", 1, ("Human",)),
                    "Human": PredicateDecl("Human", 1, ("Human",))},
        functions={"father_of": FunctionDecl("father_of", 1, ("Human",), "Human")},
        constants={"alice": ConstantDecl("alice", "Human")},
        sorts=frozenset({"Human"}),
    )


# =============================================================================
# Writer refusals
# =============================================================================

def test_refuses_modal_node_by_name():
    with pytest.raises(NotImplementedError, match="Box"):
        formula_to_tff(Box(Atom("P", [])))


def test_refuses_sorted_cardinality_by_name():
    node = SortedCardinality(Variable("x"), "Human", Atom("P", [Variable("x")]))
    with pytest.raises(NotImplementedError, match="SortedCardinality"):
        formula_to_tff(node)


def test_refuses_number_literal_by_name():
    node = Atom("P", [Number(3)])
    with pytest.raises(NotImplementedError, match="arithmetic"):
        formula_to_tff(node)


@pytest.mark.parametrize("op", ["<", ">", "≤", "≥"])
def test_refuses_arithmetic_comparison_predicate_by_name(op):
    node = SortedQuantifier("∀", Variable("x"), "Human",
                            Atom(op, [Variable("x"), Variable("x")]))
    with pytest.raises(NotImplementedError, match="arithmetic"):
        formula_to_tff(node)


@pytest.mark.parametrize("op", ["+", "-", "*", "/"])
def test_refuses_arithmetic_function_by_name(op):
    node = SortedQuantifier("∀", Variable("x"), "Human",
                            Atom("P", [Function(op, [Variable("x"), Variable("x")])]))
    with pytest.raises(NotImplementedError, match="arithmetic"):
        formula_to_tff(node)


def test_refuses_free_variable():
    """A free variable is refused rather than silently closed at $i (see
    module docstring 'Free variables are refused, not implicitly closed')."""
    node = Atom("P", [Variable("x")])
    with pytest.raises(ValueError, match="free variable"):
        formula_to_tff(node)


def test_refuses_sort_conflict_naming_both_sorts():
    """The same predicate applied at two textually-distinct sorts across one
    problem is refused loudly, not silently resolved to one -- test_oracle
    (3)'s "union-find would need to merge two distinct sorts" case."""
    p1 = SortedQuantifier("∀", Variable("x"), "Human", Atom("Mortal", [Variable("x")]))
    conclusion = Atom("Mortal", [SortedConstant("gru", "Robot")])
    with pytest.raises(ValueError, match="Human.*Robot|Robot.*Human"):
        generate_tff_problem([p1], conclusion)


def test_refuses_predicate_function_name_collision():
    """'Foo' and 'foo' both fold to the TFF identifier 'foo' (only the
    FIRST character is folded -- 'FOO' would fold to 'fOO', a DIFFERENT,
    non-colliding token; the exact pair matters here)."""
    with pytest.raises(NotImplementedError, match="Foo.*foo|foo.*Foo"):
        generate_tff_problem(
            [Atom("Foo", [Constant("a")])], Not(Atom("foo", [Constant("a")])))


def test_refuses_constant_vs_function_name_clash():
    node = And(Atom("P", [Constant("a")]), Atom("Q", [Function("a", [Constant("b")])]))
    with pytest.raises(ValueError, match="'a'"):
        formula_to_tff(node)


# =============================================================================
# Round trip: writer -> reader, alpha-equivalent (here: structurally equal --
# no variable renaming happens on the way through) AST recovered
# =============================================================================

@pytest.mark.parametrize("premises_txt, conclusion_txt", [
    (["∀x:Human Mortal(x)", "Human(socrates:Human)"], "Mortal(socrates:Human)"),
    (["Owns(alice:Human, rex:Dog)"], "Owns(alice:Human, rex:Dog)"),
    (["∀x:Human Mortal(father_of(x))", "Human(alice:Human)"],
     "Mortal(father_of(alice:Human))"),
    (["∃≥2 x:Human Mortal(x)"], "∃≥1 x:Human Mortal(x)"),
])
def test_writer_reader_round_trip(premises_txt, conclusion_txt):
    premises = [MSFOL.parse(t) for t in premises_txt]
    conclusion = MSFOL.parse(conclusion_txt)
    text = generate_tff_problem(premises, conclusion)
    _sig, formulas = parse_tff_problem(text)
    # SortedCount is lowered by the WRITER before rendering (native TFF has
    # no counting-quantifier syntax of its own), so the reader recovers the
    # EXPANDED typed form, not the original SortedCount node -- expand the
    # expected side identically via the same writer-side helper so the
    # comparison is apples to apples.
    from unicode_fol_kit.atp.tptp_tff import _expand_all_sorted_counts
    expected = [_expand_all_sorted_counts(p) for p in premises] + \
               [_expand_all_sorted_counts(conclusion)]
    assert [f.formula for f in formulas] == expected


# =============================================================================
# Backend integration (no external tool)
# =============================================================================

def test_problem_needs_tff_true_only_with_a_sorted_node():
    plain = [FOL.parse("∀x (Human(x) → Mortal(x))")], FOL.parse("Mortal(socrates)")
    assert problem_needs_tff(*plain) is False

    sorted_premise = MSFOL.parse("∀x:Human Mortal(x)")
    assert problem_needs_tff([sorted_premise], FOL.parse("Mortal(socrates)")) is True

    # A SortedConstant buried only in the CONCLUSION still counts.
    assert problem_needs_tff(
        [FOL.parse("P(socrates)")],
        Atom("Mortal", [SortedConstant("socrates", "Human")])) is True


def test_generate_vampire_input_auto_selects_tff_when_sorted():
    sorted_premise = MSFOL.parse("∀x:Human Mortal(x)")
    conclusion = MSFOL.parse("Mortal(socrates:Human)")
    text = _generate_vampire_input([sorted_premise], conclusion)
    assert text.startswith("tff(")
    assert "$tType" in text


def test_generate_vampire_input_stays_fof_without_sorts():
    premises = [FOL.parse("∀x (Human(x) → Mortal(x))")]
    conclusion = FOL.parse("Mortal(socrates)")
    text = _generate_vampire_input(premises, conclusion)
    assert text.startswith("fof(")
    assert "$tType" not in text


def test_generate_vampire_input_tff_override_forces_typed_route():
    """tff=True forces the typed route even for an all-classical problem."""
    premises = [FOL.parse("∀x (Human(x) → Mortal(x))")]
    conclusion = FOL.parse("Mortal(socrates)")
    text = _generate_vampire_input(premises, conclusion, tff=True)
    assert text.startswith("tff(")


def test_eprover_generate_input_auto_selects_tff_when_sorted():
    sorted_premise = MSFOL.parse("∀x:Human Mortal(x)")
    conclusion = MSFOL.parse("Mortal(socrates:Human)")
    text = _eprover_generate_input([sorted_premise], conclusion)
    assert text.startswith("tff(")


def test_check_entailment_vampire_detailed_tff_route_excerpt_not_reverse_mapped(monkeypatch):
    """The tff route's ``output_excerpt`` is NOT reverse-mapped (documented
    non-goal -- see module docstring).

    Uses a constant whose kit-level name is non-ASCII (``θ``), so the tff
    writer genuinely ASCII-transliterates it to ``theta`` (see
    ``constant_name_to_ascii``'s Greek-letter table) -- a REAL sanitised
    token, not a stand-in. The fake stdout echoes that same sanitised
    ``theta`` token back, exactly as a real Vampire proof would. On the
    classical fof route this token would come back through
    ``reverse_map_text`` and turn back into ``θ``; on the tff route
    ``name_map`` is unconditionally ``None`` (see
    ``check_entailment_vampire_detailed``'s source), so no such lookup is
    attempted at all and ``theta`` must survive untouched in
    ``output_excerpt`` -- this is the concrete, observable behaviour the
    docstring's "un-reversed" claim describes, not just the status field."""
    def fake_spawn(input_str, vampire_path, timeout=30, use_wsl=False, extra_args=()):
        assert "tff(" in input_str
        assert "theta" in input_str    # the writer already sanitised θ -> theta
        stdout = (
            "tff(f1,axiom,(![X: human] : mortal(X))).\n"
            "tff(f2,conjecture,(mortal(theta))).\n"
            "% SZS status Theorem for problem\n"
        )
        return stdout, False

    monkeypatch.setattr(_ve, "_spawn_vampire", fake_spawn)
    sorted_premise = MSFOL.parse("∀x:Human Mortal(x)")
    conclusion = Atom("Mortal", [SortedConstant("θ", "Human")])
    result = check_entailment_vampire_detailed(
        [sorted_premise], conclusion, vampire_path="unused")
    assert result["status"] == "proved"
    assert "theta" in result["output_excerpt"]
    assert "θ" not in result["output_excerpt"]    # no reverse mapping attempted


def test_check_entailment_vampire_detailed_tff_route_derivation_currently_always_none(monkeypatch):
    """KNOWN GAP, documented rather than hidden (see
    ``check_entailment_vampire_detailed``'s docstring): even for a genuine,
    successful proof whose stdout contains well-formed TSTP ``tff(...)``
    proof lines (the shape real Vampire/E output for a tff-route proof --
    see e.g. Vampire's ``--proof tptp`` output), ``derivation`` comes back
    ``None`` today, because ``atp.tstp.parse_tstp_derivation`` only
    recognises ``fof``/``cnf`` statement keywords (its own docstring says
    so), never ``tff``/``tcf``. ``atp/tstp.py`` is a shared module outside
    this item's ownership (C2 owns the writer/reader pair and the backend
    opt-in, not the shared TSTP scanner), so extending its statement
    scanner to ``tff``/``tcf`` is follow-up work, not a C2 fix -- this test
    exists so that follow-up has a red test to turn green, instead of the
    gap staying silently undocumented."""
    def fake_spawn(input_str, vampire_path, timeout=30, use_wsl=False, extra_args=()):
        assert "tff(" in input_str
        stdout = (
            "tff(f1,axiom,(![X: human] : mortal(X))).\n"
            "tff(f2,conjecture,(mortal(socrates))).\n"
            "tff(f3,plain,($false),inference(resolution,[],[f1,f2])).\n"
            "% SZS status Theorem for problem\n"
        )
        return stdout, False

    monkeypatch.setattr(_ve, "_spawn_vampire", fake_spawn)
    sorted_premise = MSFOL.parse("∀x:Human Mortal(x)")
    conclusion = MSFOL.parse("Mortal(socrates:Human)")
    result = check_entailment_vampire_detailed(
        [sorted_premise], conclusion, vampire_path="unused")
    assert result["status"] == "proved"
    assert result["derivation"] is None    # not "no proof" -- the scanner can't see tff(...) yet


def test_check_entailment_eprover_detailed_tff_route_derivation_currently_always_none(monkeypatch):
    """E-backend twin of the Vampire gap above: same underlying cause
    (``atp.tstp.parse_tstp_derivation`` is ``fof``/``cnf``-only), same
    "documented gap, not a silent hole" rationale."""
    def fake_run(problem, command, args, use_wsl, timeout_s):
        assert problem.startswith("tff(")
        stdout = (
            "tff(f1,axiom,(![X: human] : mortal(X))).\n"
            "tff(f2,conjecture,(mortal(socrates))).\n"
            "tff(f3,plain,($false),inference(resolution,[],[f1,f2])).\n"
            "# SZS status Theorem for problem\n"
        )
        return stdout, False

    monkeypatch.setattr(_eb, "_run_tptp_prover", fake_run)
    sorted_premise = MSFOL.parse("∀x:Human Mortal(x)")
    conclusion = MSFOL.parse("Mortal(socrates:Human)")
    result = check_entailment_eprover_detailed(
        [sorted_premise], conclusion, command="unused")
    assert result["status"] == "proved"
    assert result["derivation"] is None    # not "no proof" -- the scanner can't see tff(...) yet


# =============================================================================
# Live differential tests: Vampire + E, gated like the existing live tests
# (test_vampire_entailment.py's _wsl_vampire_ok / test_eprover_zipperposition
# .py's eprover_available()). Neither a native Windows Vampire/E nor a bare
# WSL PATH entry is assumed -- both are driven via use_wsl=True/wsl-discovery
# exactly as those existing modules already do.
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


# Battery of sorted entailments, each (premises, conclusion, expect) -- the
# expected SZS/bool verdict was worked out BY HAND (see each comment) before
# being checked against Vampire live.
_BATTERY = [
    # Textbook syllogism, with an explicit witness constant.
    (["∀x:Human Mortal(x)", "Human(socrates:Human)"], "Mortal(socrates:Human)", True,
     "modus ponens over a sorted universal, witnessed"),
    # Sort-relativisation THREADED across formulas via a function symbol:
    # father_of's RESULT sort is pinned to Human only through Adult's own
    # direct sorted binder ("∀y:Human Adult(y)") unifying with Adult's use
    # over father_of(x) -- see test_infer_tff_signature_pins_every_argument
    # _position's docstring for the hand-worked union-find trace. If sort
    # info were dropped anywhere along that chain the exported tff problem
    # would type father_of's result at plain $i instead of human (still
    # sound, just LESS typed) -- this is the concrete, load-bearing case
    # where relativisation threading multi-occurrence across the batch
    # (not just one binder) actually matters for what gets declared.
    (["∀x:Human Adult(father_of(x))", "∀y:Human Adult(y)", "Human(alice:Human)"],
     "Adult(father_of(alice:Human))", True,
     "sort-relativisation matters: threaded via a shared predicate across formulas"),
    # A sorted existential witnessed by an explicit sorted constant.
    (["∀x:Human Mortal(x)", "Human(alice:Human)"], "∃x:Human Mortal(x)", True,
     "existential witnessed by a sorted constant"),
    # Two disjoint sorts peacefully coexisting in one problem: the Robot
    # fact is irrelevant to the Human conclusion, and must stay irrelevant.
    (["∀x:Human Mortal(x)", "Human(alice:Human)", "Robot(gru:Robot)"],
     "Mortal(alice:Human)", True, "unrelated second sort does not interfere"),
    # A genuine non-entailment: no premise connects Human-hood to Rich-hood.
    (["∀x:Human Mortal(x)", "Human(alice:Human)"], "∃x:Human Rich(x)", False,
     "unrelated predicate is correctly NOT entailed"),
]


@pytest.mark.skipif(not _HAVE_VAMPIRE, reason="no Vampire binary reachable (native or WSL)")
@pytest.mark.parametrize("premises_txt, conclusion_txt, expect, _label", _BATTERY)
def test_tff_and_fof_routes_agree_via_vampire(premises_txt, conclusion_txt, expect, _label):
    premises = [MSFOL.parse(t) for t in premises_txt]
    conclusion = MSFOL.parse(conclusion_txt)
    kwargs = _vampire_kwargs()
    tff_verdict = check_logical_entailment_vampire(premises, conclusion, tff=True, **kwargs)
    fof_verdict = check_logical_entailment_vampire(premises, conclusion, tff=False, **kwargs)
    assert tff_verdict == expect, f"tff route: {_label}"
    assert fof_verdict == expect, f"fof route: {_label}"


@pytest.mark.skipif(not _HAVE_VAMPIRE, reason="no Vampire binary reachable (native or WSL)")
def test_tff_and_fof_routes_agree_on_non_emptiness_via_vampire():
    """The soundness fix roadmap item S1 closed, live-verified against Vampire.

    "∀x:Ghost P(x) ⊢ ∃x:Ghost P(x)" is valid ONLY because sort Ghost is
    non-empty (no witness constant of sort Ghost is declared anywhere in
    this problem, so nothing else could establish it). TPTP TF0 semantics
    guarantee every declared type is non-empty (this kit's own MSFOL model
    theory agrees — semantics/modelfinder.py: "Each sort gets a non-empty
    universe"), so the NATIVE tff route correctly proves it: Theorem.

    The guard-predicate fof route relativises "∀x:Ghost P(x)" to "∀x
    (Ghost(x) => P(x))" and "∃x:Ghost P(x)" to "∃x (Ghost(x) & P(x))"
    (SortedQuantifier._relativize) — before S1, WITHOUT separately asserting
    "∃x Ghost(x)" for a sort that has no SortedConstant witness anywhere in
    the formula, so a model with Ghost(x) false everywhere used to satisfy
    the premise vacuously while refuting the conclusion, and Vampire
    reported CounterSatisfiable / False for the fof-relativised export — a
    genuine, live-verified (2026-09) divergence from the tff route, tracked
    as a known gap by the C2 item that first found it (out of that item's
    scope; ``SortedQuantifier._relativize``/``to_fol`` core behaviour shared
    by ~29 call sites across the kit).

    S1 (see ``unicode_fol_kit.fol._msfl_nodes.nonempty_sort_axioms`` and
    ``atp._tptp_problem``'s module docstring) adds exactly that missing
    ``∃x Ghost(x)`` axiom to the fof export too, so Vampire now proves the
    fof route's Theorem as well — both routes agree, live-verified again
    here (2026-09).
    """
    premise = MSFOL.parse("∀x:Ghost P(x)")
    conclusion = MSFOL.parse("∃x:Ghost P(x)")
    kwargs = _vampire_kwargs()
    assert check_logical_entailment_vampire([premise], conclusion, tff=True, **kwargs) is True
    assert check_logical_entailment_vampire([premise], conclusion, tff=False, **kwargs) is True


@pytest.mark.skipif(not eprover_available(), reason="no eprover binary found")
@pytest.mark.parametrize("premises_txt, conclusion_txt, expect, _label", _BATTERY)
def test_tff_and_fof_routes_agree_via_eprover(premises_txt, conclusion_txt, expect, _label):
    premises = [MSFOL.parse(t) for t in premises_txt]
    conclusion = MSFOL.parse(conclusion_txt)
    expected_status = "proved" if expect else "refuted"
    tff_result = check_entailment_eprover_detailed(premises, conclusion, tff=True)
    fof_result = check_entailment_eprover_detailed(premises, conclusion, tff=False)
    assert tff_result["status"] == expected_status, f"tff route: {_label}"
    assert fof_result["status"] == expected_status, f"fof route: {_label}"


@pytest.mark.skipif(not eprover_available(), reason="no eprover binary found")
def test_tff_and_fof_routes_agree_on_non_emptiness_via_eprover():
    """Same S1 soundness case as the Vampire test above, cross-checked against
    an entirely independent prover (E) -- see that test's docstring."""
    premise = MSFOL.parse("∀x:Ghost P(x)")
    conclusion = MSFOL.parse("∃x:Ghost P(x)")
    tff_result = check_entailment_eprover_detailed([premise], conclusion, tff=True)
    fof_result = check_entailment_eprover_detailed([premise], conclusion, tff=False)
    assert tff_result["status"] == "proved"
    assert fof_result["status"] == "proved"
