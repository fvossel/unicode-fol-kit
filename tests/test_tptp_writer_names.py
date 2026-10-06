r"""The TPTP writers: guard predicates across formulas, a Measure's
function name, a sort that is also a predicate, symbols the guard could not see,
illegal names, problems without a conclusion, and the numbers a repair prints.

Every expected value below is derived by hand from the semantic clause named in
its test, never copied from what the code printed. Two oracles stand next to the
strings: z3 on the NODES (the kit's own semantics of a sort is the guard
predicate of its name, and z3, the fof writer and the Prover9 writer all read it
so) and, where installed, real Vampire 5.0.1 and E 3.5.1 (through ``wsl`` on
this machine), whose verdicts must equal z3's. A test that needs a prover is
skipped, never weakened, when none is reachable.

What is covered: sort guards across formulas, the Measure node, a sort named like
a predicate in TF0, numbers / dollar-words / variables the single-formula guard
could not see, no conclusion, names that are not TPTP words, one predicate at two
arities, the guard's stack cost, a number written without an exponent by the repair
layer.
"""

import functools
import gc
import inspect
import random
import re
import shutil
import subprocess
import sys
from typing import List, Optional

import pytest

from unicode_fol_kit import api
from unicode_fol_kit.atp import (
    TptpNameMap, apply_reverse_tptp, generate_tff_arith_problem,
    generate_tff_problem, generate_tff_problem_with_mapping,
    generate_tptp_problem, generate_tptp_problem_with_mapping,
)
from unicode_fol_kit.atp.tptp_tff import formula_to_tff
from unicode_fol_kit.atp.z3_arith import is_satisfiable_arith
from unicode_fol_kit.atp.z3_models import is_satisfiable
from unicode_fol_kit.fol import _tptp_symbols as symbols
from unicode_fol_kit.fol.nodes import (
    And, Atom, Constant, Contrast, Count, Function, Iff, Implies, Measure, Node,
    Not, Number, Or, Quantifier, SortedConstant, SortedCount, SortedQuantifier,
    Variable, Xor, nonempty_sort_axioms,
)
from unicode_fol_kit.fol.tptp_input import parse_tptp, parse_tptp_formula
from unicode_fol_kit.fol.tptp_repair import repair_tptp_formula

X, Y, Z = Variable("x"), Variable("y"), Variable("z")
A, B, D = Constant("a"), Constant("b"), Constant("d")


def raises_not_implemented(call) -> str:
    with pytest.raises(NotImplementedError) as excinfo:
        call()
    return str(excinfo.value)


# ---------------------------------------------------------------------------
# Real provers, reached the way the repository's other live tests reach them.
# ---------------------------------------------------------------------------

def _vampire_command() -> Optional[List[str]]:
    found = shutil.which("vampire")
    if found:
        return [found]
    try:
        probe = subprocess.run(["wsl.exe", "vampire", "--version"], capture_output=True,
                               text=True, timeout=30)
        if probe.returncode == 0 and "Vampire" in probe.stdout:
            return ["wsl.exe", "vampire"]
    except Exception:                                  # noqa: BLE001 — any failure means "absent"
        pass
    return None


_VAMPIRE = _vampire_command()
needs_vampire = pytest.mark.skipif(_VAMPIRE is None, reason="no Vampire reachable (PATH, or 'wsl vampire')")


def vampire_kwargs() -> dict:
    if shutil.which("vampire"):
        return dict(vampire_path=shutil.which("vampire"), use_wsl=False)
    return dict(vampire_path="vampire", use_wsl=True)


def szs_status(problem: str, seconds: int = 30) -> str:
    """The SZS status Vampire prints for ``problem`` (read on stdin)."""
    result = subprocess.run(_VAMPIRE + ["--input_syntax", "tptp", "-t", str(seconds)],
                            input=problem, capture_output=True, text=True,
                            timeout=seconds + 90)
    found = re.search(r"% SZS status (\w+)", result.stdout)
    return found.group(1) if found else "NO-SZS: " + result.stdout[-200:]


def _eprover_ready():
    from unicode_fol_kit.atp import eprover_available
    return eprover_available()


needs_eprover = pytest.mark.skipif(_eprover_ready() is not True,
                                   reason="no eprover reachable (PATH, WSL, $UFK_EPROVER_CMD)")


def z3_status(conclusion: Node, premises) -> str:
    return api.prove(conclusion, list(premises), backends=["z3"], timeout=30000).status


def prover_statuses(premises, conclusion, **options):
    """``(vampire, eprover)`` statuses through the kit's own backends."""
    from unicode_fol_kit.atp.eprover_backend import check_entailment_eprover_detailed
    from unicode_fol_kit.atp.vampire_entailment import check_entailment_vampire_detailed
    out = []
    if _VAMPIRE is not None:
        out.append(check_entailment_vampire_detailed(
            premises, conclusion, timeout=30, **vampire_kwargs(), **options)["status"])
    if _eprover_ready() is True:
        out.append(check_entailment_eprover_detailed(premises, conclusion, timeout=30, **options)["status"])
    return out


# ===========================================================================
# A sort guard is a predicate, across formulas too
# ===========================================================================

def test_a_sort_guard_and_a_predicate_of_another_spelling_are_refused_across_formulas():
    """``∀x:Foo P(x)`` is written with the guard predicate ``Foo`` (``foo``), and
    its non-emptiness axiom ``∃x Foo(x)``; the predicate ``foo`` of the conclusion
    is a different symbol of the kit (``Foo`` /= ``foo``, both for z3 and for the
    kit's reader) that TPTP writes as the same word. Within one formula the guard
    refuses this; the whole-problem check must too."""
    premise = SortedQuantifier("∀", X, "Foo", Atom("P", (X,)))
    message = raises_not_implemented(lambda: generate_tptp_problem([premise], Atom("foo", (A,))))
    assert "distinct predicate names" in message
    assert "'Foo'" in message and "'foo'" in message and "TPTP identifier 'foo'" in message
    # the same two formulas written as ONE formula are refused by the single-formula guard
    single = raises_not_implemented(lambda: And(premise, Atom("foo", (A,))).to_tptp())
    assert "distinct predicate names" in single


GUARD_FOLD_PREMISES = [SortedQuantifier("∀", X, "Foo", Atom("R", (X,))), Quantifier("∀", X, Atom("foo", (X,)))]
GUARD_FOLD_CONCLUSION = Quantifier("∀", Y, Atom("R", (Y,)))

# What the writer used to write for this problem, spelled out: the two predicates merged.
GUARD_FOLD_OLD_TEXT = (
    "fof(premise_1, axiom, (![X]: (foo(X) => r(X)))).\n"
    "fof(premise_2, axiom, (![X]: foo(X))).\n"
    "fof(nonempty_sort_1, axiom, (?[X0]: foo(X0))).\n"
    "fof(goal, conjecture, (![Y]: r(Y))).\n")


def test_the_premises_do_not_entail_the_conclusion_so_a_proof_of_the_old_text_was_wrong():
    """Hand derivation: domain {e1, e2}, ``Foo`` = {e1}, ``R`` = {e1}, ``foo`` = both.
    ``∀x (Foo(x) → R(x))`` and ``∀x foo(x)`` hold, ``∀y R(y)`` does not: NOT
    entailed. z3 on the nodes says so. The text the writer used to write merged
    ``Foo`` and ``foo``, and a prover proved it. The writer now refuses."""
    assert z3_status(GUARD_FOLD_CONCLUSION, GUARD_FOLD_PREMISES) == "refuted"
    raises_not_implemented(lambda: generate_tptp_problem(GUARD_FOLD_PREMISES, GUARD_FOLD_CONCLUSION))
    raises_not_implemented(lambda: generate_tptp_problem_with_mapping(GUARD_FOLD_PREMISES, GUARD_FOLD_CONCLUSION))


@needs_vampire
def test_the_merged_text_really_is_proved_by_vampire():
    """The old text is a theorem (premise 2 gives ``foo`` everywhere, premise 1 turns
    that into ``r`` everywhere): the refusal above prevents a false 'proved'."""
    assert szs_status(GUARD_FOLD_OLD_TEXT) == "Theorem"


def test_a_sort_and_a_predicate_of_the_same_spelling_are_one_symbol_and_written_as_before():
    """``Foo`` as sort and as predicate IS one symbol of the guard reading, so there
    is nothing to refuse. Hand-derived text: the premise is
    ``∀x (Foo(x) → P(x))``; the axiom names its witness ``X0`` (the first fresh
    variable avoiding ``x``)."""
    premise = SortedQuantifier("∀", X, "Foo", Atom("P", (X,)))
    assert generate_tptp_problem([premise], Atom("Foo", (A,))) == (
        "fof(premise_1, axiom, (![X]: (foo(X) => p(X)))).\n"
        "fof(nonempty_sort_1, axiom, (?[X0]: foo(X0))).\n"
        "fof(goal, conjecture, foo(a)).\n")


def test_a_sort_used_only_by_a_sorted_constant_still_writes_its_guard_axiom():
    """``P(a:Foo)`` has no guard predicate in its own text, but the problem asserts
    ``∃x Foo(x)`` (the sort is non-empty), which writes ``foo``: a predicate ``foo``
    in the conclusion is a different symbol that would be merged with it.
    Hand derivation: kit semantics (z3 adds the same axiom) ``P(a), ∃x Foo(x) ⊭
    ∃x foo(x)``; the merged text would prove it."""
    premise = Atom("P", (SortedConstant("a", "Foo"),))
    conclusion = Quantifier("∃", X, Atom("foo", (X,)))
    assert z3_status(conclusion, [premise]) == "refuted"
    message = raises_not_implemented(lambda: generate_tptp_problem([premise], conclusion))
    assert "'Foo'" in message and "'foo'" in message


def _random_sorted_formula(rng: random.Random, depth: int = 3) -> Node:
    predicates = ["Foo", "foo", "Bar", "P", "Q"]
    sorts = ["Foo", "foo", "Bar", "S"]
    functions = ["f", "F"]
    variables = [X, Y]

    def term(d):
        roll = rng.random()
        if d <= 0 or roll < 0.4:
            return rng.choice(variables) if rng.random() < 0.5 else Constant(rng.choice(["a", "b"]))
        if roll < 0.5:
            return SortedConstant(rng.choice(["a", "b"]), rng.choice(sorts))
        if roll < 0.6:
            return Measure(term(d - 1), term(d - 1))
        return Function(rng.choice(functions), (term(d - 1),))

    def form(d):
        roll = rng.random()
        if d <= 0 or roll < 0.3:
            return Atom(rng.choice(predicates), tuple(term(1) for _ in range(rng.randint(0, 2))))
        if roll < 0.4:
            return Not(form(d - 1))
        if roll < 0.5:
            return Quantifier(rng.choice("∀∃"), rng.choice(variables), form(d - 1))
        if roll < 0.62:
            return SortedQuantifier(rng.choice("∀∃"), rng.choice(variables), rng.choice(sorts), form(d - 1))
        if roll < 0.68:
            return SortedCount(rng.choice(["ge", "le", "eq"]), Number(rng.randint(1, 2)),
                               rng.choice(variables), rng.choice(sorts), form(d - 1))
        if roll < 0.72:
            return Count(rng.choice(["ge", "le"]), Number(rng.randint(1, 2)), rng.choice(variables), form(d - 1))
        return rng.choice([And, Or, Implies, Iff, Xor, Contrast])(form(d - 1), form(d - 1))

    return form(depth)


_SAME_KIND = re.compile(r"distinct (predicate|function|constant/function) names")


def _refused_same_kind(call) -> bool:
    try:
        call()
    except NotImplementedError as exc:
        return bool(_SAME_KIND.search(str(exc)))
    return False


def test_the_whole_problem_check_and_the_single_formula_guard_agree_on_random_problems():
    """ONE implementation: the guard records what is RENDERED, the writer's check is
    fed the formulas that reach the problem text (the premises, the conclusion and
    the non-emptiness axioms). Whatever the guard refuses for the conjunction of all
    of them, the writer must refuse for the problem, and nothing else.

    ``And`` of everything is one formula, so the guard sees the guard predicates the
    sorted nodes lower to directly; the writer sees them through the axioms."""
    rng = random.Random(20261004)
    refused = clean = cross_only = 0
    for _ in range(700):
        formulas = [_random_sorted_formula(rng) for _ in range(rng.randint(1, 3))]
        premises, conclusion = formulas[:-1], formulas[-1]
        everything = functools.reduce(And, formulas + list(nonempty_sort_axioms(*formulas)))
        by_guard = _refused_same_kind(everything.to_tptp)
        by_writer = _refused_same_kind(lambda: generate_tptp_problem(premises, conclusion))
        assert by_guard == by_writer, (formulas, by_guard, by_writer)
        refused += by_writer
        clean += not by_writer
        # a problem refused only because of a name met in ANOTHER formula
        if by_writer and not any(_refused_same_kind(f.to_tptp) for f in formulas):
            cross_only += 1
    assert refused > 100 and clean > 100 and cross_only > 20, (refused, clean, cross_only)


# ===========================================================================
# A Measure writes the function `measure`
# ===========================================================================

# The predicate is BINARY like the function `measure/2`: a prover tells a predicate and a
# function of one name apart by arity, so only a same-arity pair is rejected by Vampire
# ("Non-boolean term measure(measure(X0,d),d) of sort $i is used in a formula context").
MEASURE_PREMISE = Quantifier("∀", X, Atom("Measure", (Measure(X, D), D)))
MEASURE_THEOREM = Quantifier("∃", X, Quantifier("∃", Y, Atom("Measure", (X, Y))))
MEASURE_NON_THEOREM = Quantifier("∀", X, Quantifier("∀", Y, Atom("Measure", (X, Y))))


def test_a_measure_node_is_separated_from_a_predicate_named_measure():
    """``Measure(x, d)`` is the function ``measure`` (``to_z3`` declares ``measure/2``
    for it); the predicate ``Measure`` is the word ``measure`` too. The TERM side
    moves, as for every function/constant: ``measure_term``. The constant ``d`` is
    untouched. The map says ``measure -> measure_term``."""
    text, name_map = generate_tptp_problem_with_mapping([MEASURE_PREMISE], MEASURE_THEOREM)
    assert text == ("fof(premise_1, axiom, (![X]: measure(measure_term(X,d),d))).\n"
                    "fof(goal, conjecture, (?[X]: (?[Y]: measure(X,Y)))).\n")
    assert name_map == TptpNameMap(predicate={"Measure": "Measure"},
                                   term={"d": "d", "measure": "measure_term"})
    assert generate_tptp_problem([MEASURE_PREMISE], MEASURE_THEOREM) == text


def test_a_measure_without_a_clash_is_written_exactly_as_before():
    atom = Atom("P", (Measure(A, D),))
    text, name_map = generate_tptp_problem_with_mapping([atom], atom)
    assert text == "fof(premise_1, axiom, p(measure(a,d))).\nfof(goal, conjecture, p(measure(a,d))).\n"
    assert name_map.term == {"a": "a", "d": "d"}                # no entry for `measure`


def test_the_renamed_measure_reads_back_as_the_function_it_was_written_as():
    text, name_map = generate_tptp_problem_with_mapping([MEASURE_PREMISE], MEASURE_THEOREM)
    assert "measure_term(" in text
    read = [apply_reverse_tptp(item.formula, name_map) for item in parse_tptp(text)]
    # a Measure node IS the binary function `measure`, and that is what the reader reads
    expected_premise = Quantifier("∀", X, Atom("Measure", (Function("measure", (X, D)), D)))
    assert read == [expected_premise, MEASURE_THEOREM]


def test_measure_cross_kind_verdicts_are_hand_derived():
    """``∀x Measure(μ(x,d), d) ⊨ ∃x ∃y Measure(x, y)``: any element e gives the witness
    (μ(e,d), d). ``⊨ ∀x ∀y Measure(x, y)`` fails: domain {0,1}, μ(x,d) = 0, d = 0,
    ``Measure`` = {(0,0)} satisfies the premise only."""
    assert z3_status(MEASURE_THEOREM, [MEASURE_PREMISE]) == "proved"
    assert z3_status(MEASURE_NON_THEOREM, [MEASURE_PREMISE]) == "refuted"


@pytest.mark.skipif(_VAMPIRE is None and _eprover_ready() is not True, reason="no prover reachable")
@pytest.mark.parametrize("conclusion, expected", [(MEASURE_THEOREM, "proved"), (MEASURE_NON_THEOREM, "refuted")],
                         ids=["theorem", "non-theorem"])
def test_provers_answer_the_measure_problem_like_z3(conclusion, expected):
    """Before: ``measure(measure(X,d),d)`` — Vampire answered ``Non-boolean term ... is
    used in a formula context`` and E stopped on a parse error, so no verdict."""
    assert z3_status(conclusion, [MEASURE_PREMISE]) == expected
    statuses = prover_statuses([MEASURE_PREMISE], conclusion)
    assert statuses                                  # (a prover is reachable)
    for status in statuses:
        assert status == expected


def test_tf0_and_tfa_refuse_a_measure_node_by_name():
    atom = Atom("P", (Measure(A, D),))
    assert "'Measure'" in raises_not_implemented(lambda: generate_tff_problem([atom], atom))
    assert "'Measure'" in raises_not_implemented(lambda: generate_tff_arith_problem([atom], atom))


# --- the general question, answered by enumeration ----------------------------

def all_node_classes() -> List[type]:
    """Every node class of the PACKAGE (a test module may define node classes of its own
    that render, which is not what the tables below classify)."""
    gc.collect()
    seen, stack = set(), [Node]
    while stack:
        for sub in stack.pop().__subclasses__():
            if sub not in seen:
                seen.add(sub)
                stack.append(sub)
    return sorted((c for c in seen if c.__module__.startswith("unicode_fol_kit")),
                  key=lambda c: (c.__module__, c.__qualname__))


def renders_something(cls: type) -> bool:
    """Whether ``cls.to_tptp`` is more than a refusal (its source never raises
    ``NotImplementedError``): every modal, second-order, lambda, hybrid, team,
    linear, Lambek and Łukasiewicz class says so, by name, and writes nothing."""
    method = inspect.getattr_static(cls, "to_tptp")
    return "NotImplementedError" not in inspect.getsource(method.__wrapped__)


#: The classes that write a predicate, function or constant NAME (or the word of
#: a numeral or a variable) into TPTP text, and what each writes. Atom, Function,
#: Constant and SortedConstant are the four the writers rename; the rest are the
#: answer to "which others?": Measure writes the function `measure`;
#: SortedQuantifier and SortedCount write the guard predicate of their sort; Number
#: writes a numeral, Variable a variable.
WRITES_A_SYMBOL = {
    "Atom": "a predicate", "Function": "a function", "Constant": "a constant",
    "SortedConstant": "a constant", "Measure": "the function measure",
    "SortedQuantifier": "the guard predicate of its sort", "SortedCount": "the guard predicate of its sort",
    "Number": "a numeral", "Variable": "a variable",
}
#: Classes that render only structure: connectives, a quantifier, and a Count, whose
#: witnesses are fresh variables and whose only atoms are `=`/`!=`.
WRITES_NO_SYMBOL = {"And", "Contrast", "Count", "Iff", "Implies", "Not", "Or", "Quantifier", "Xor"}


def test_every_node_class_that_renders_is_classified_by_what_it_writes():
    """The enumeration behind the Measure case, derived from the classes rather than remembered. A
    class added later that renders but is in neither table fails this test: say what
    symbol it writes (and add it to the two tests below) or that it writes none."""
    classes = all_node_classes()
    assert len(classes) >= 60
    rendering = {cls.__name__ for cls in classes if renders_something(cls)}
    assert rendering == set(WRITES_A_SYMBOL) | WRITES_NO_SYMBOL, \
        sorted(rendering ^ (set(WRITES_A_SYMBOL) | WRITES_NO_SYMBOL))


def test_a_class_that_writes_no_symbol_reports_none_and_a_class_that_does_reports_one():
    samples = {
        "Atom": Atom("P", (A,)), "Function": Function("f", (A,)), "Constant": A,
        "SortedConstant": SortedConstant("a", "S"), "Measure": Measure(A, D),
        "Number": Number(1), "Variable": X,
        "And": And(Atom("P", ()), Atom("Q", ())), "Contrast": Contrast(Atom("P", ()), Atom("Q", ())),
        "Iff": Iff(Atom("P", ()), Atom("Q", ())), "Implies": Implies(Atom("P", ()), Atom("Q", ())),
        "Not": Not(Atom("P", ())), "Or": Or(Atom("P", ()), Atom("Q", ())),
        "Xor": Xor(Atom("P", ()), Atom("Q", ())),
        "Quantifier": Quantifier("∀", X, Atom("P", ())),
        "Count": Count("ge", Number(2), X, Atom("P", (X,))),
        "SortedQuantifier": SortedQuantifier("∀", X, "S", Atom("P", (X,))),
        "SortedCount": SortedCount("ge", Number(2), X, "S", Atom("P", (X,))),
    }
    assert set(samples) == set(WRITES_A_SYMBOL) | WRITES_NO_SYMBOL
    for name, node in samples.items():
        names_itself = node._tptp_symbol() is not None
        # a node that LOWERS to others (a sorted quantifier, a count) names nothing by
        # itself; the symbols it writes are those of the nodes it is rendered as
        lowers = name in ("SortedQuantifier", "SortedCount")
        assert names_itself == (name in WRITES_A_SYMBOL and not lowers), name
    # ... and what a lowering node writes is seen by the guard through the nodes it lowers to
    log = symbols._RenderLog()
    token = symbols._RENDERING.set(log)
    try:
        samples["SortedQuantifier"].to_tptp()
    finally:
        symbols._RENDERING.reset(token)
    written = {symbols._resolve(w)[1] for w in log.symbols if symbols._resolve(w) is not None}
    assert "S" in {w.upper() for w in written}        # the guard predicate `s`


# One row per class that writes a NAME: how to build a formula in which the class
# writes the symbol `spelling`, a formula that writes the SAME KIND of symbol under a
# differently-spelled name, and one that writes the other kind under the same word.
def _atom(spelling):                        # Atom
    return Atom(spelling, (A,))


def _function(spelling):                    # Function
    return Atom("P", (Function(spelling, (A,)),))


def _constant(spelling):                    # Constant
    return Atom("P", (Constant(spelling),))


def _sorted_constant(spelling):             # SortedConstant
    return Atom("P", (SortedConstant(spelling, "S"),))


def _measure(_spelling):                    # Measure: always the function `measure`
    return Atom("P", (Measure(A, D),))


def _sorted_quantifier(spelling):           # the sort is the guard predicate
    return SortedQuantifier("∀", X, spelling, Atom("Q", (X,)))


def _sorted_count(spelling):
    return SortedCount("ge", Number(2), X, spelling, Atom("Q", (X,)))


#: class -> (builder, spelling, same-kind partner builder + spelling, other-kind partner)
NAME_WRITERS = {
    "Atom": (_atom, "Foo", (_atom, "foo"), lambda spelling: _constant(spelling[:1].lower() + spelling[1:])),
    "Function": (_function, "Bar", (_function, "bar"), lambda spelling: Atom(spelling[:1].upper() + spelling[1:], (A,))),
    "Constant": (_constant, "Baz", (_constant, "baz"), lambda spelling: Atom(spelling[:1].upper() + spelling[1:], (A,))),
    "SortedConstant": (_sorted_constant, "Qux", (_sorted_constant, "qux"), lambda spelling: Atom(spelling[:1].upper() + spelling[1:], (A,))),
    "Measure": (_measure, "measure", (_function, "Measure"), lambda spelling: Atom("Measure", (A, A))),
    "SortedQuantifier": (_sorted_quantifier, "Foo", (_atom, "foo"), lambda spelling: _constant("foo")),
    "SortedCount": (_sorted_count, "Foo", (_atom, "foo"), lambda spelling: _constant("foo")),
}


def _words(formulas):
    predicates, terms = set(), set()
    for formula in formulas:
        for node in formula.walk():
            if isinstance(node, Atom) and node.predicate not in ("=", "≠"):
                predicates.add(node.predicate[:1].lower() + node.predicate[1:])
            elif isinstance(node, (Function, Constant, SortedConstant)):
                terms.add(node.name)
    return predicates, terms


@pytest.mark.parametrize("class_name", sorted(NAME_WRITERS))
def test_every_class_that_writes_a_name_is_seen_by_the_same_kind_check(class_name):
    """Two spellings of one kind that fold to one word are refused, whichever of the
    two classes writes which, by the guard (one formula) AND by the writer (the two in
    two formulas). Hand derivation: ``Foo``/``foo`` are two predicates, so
    ``Q(a) ↔ ...``-style merging would write a tautology out of a non-theorem."""
    build, spelling, (partner_build, partner_spelling), _ = NAME_WRITERS[class_name]
    mine, partner = build(spelling), partner_build(partner_spelling)
    single = raises_not_implemented(lambda: And(mine, partner).to_tptp())
    assert _SAME_KIND.search(single) and "TPTP identifier" in single
    written = raises_not_implemented(lambda: generate_tptp_problem([mine], partner))
    assert _SAME_KIND.search(written)
    reversed_order = raises_not_implemented(lambda: generate_tptp_problem([partner], mine))
    assert _SAME_KIND.search(reversed_order)


@pytest.mark.parametrize("class_name", sorted(NAME_WRITERS))
def test_every_class_that_writes_a_name_is_seen_by_the_cross_kind_separation(class_name):
    """A predicate and a function/constant that share a word are not refused, and
    the writer separates them: no word is both a predicate and a term in the text,
    the text reads back through the kit's reader, and the map undoes the rename."""
    build, spelling, _, other_kind = NAME_WRITERS[class_name]
    mine, partner = build(spelling), other_kind(spelling)
    And(mine, partner).to_tptp()                                  # one formula: not refused
    text, name_map = generate_tptp_problem_with_mapping([mine], partner)
    read = [item.formula for item in parse_tptp(text)]
    predicates, terms = _words(read)
    assert predicates.isdisjoint(terms), (text, predicates & terms)
    assert any(token.endswith("_term") or token.endswith("_term2") for token in
               list(name_map.term.values()) + list(name_map.predicate.values())), (text, name_map)
    assert [apply_reverse_tptp(f, name_map) for f in read][-1] is not None


# ===========================================================================
# TF0 cannot read a sort as its guard predicate: the pair is refused
# ===========================================================================

CAR_SORT_PREMISE = SortedQuantifier("∀", X, "Car", Atom("Car", (X,)))
CAR_SORT_CONCLUSION = SortedQuantifier("∃", Y, "Car", Atom("Car", (Y,)))


def test_tf0_refuses_a_sort_and_a_predicate_that_render_as_one_identifier():
    """``∃y:Car Car(y)``: under the guard reading (z3, the fof writer, Prover9) it is
    ``∃y (Car(y) ∧ Car(y))`` with the sort non-empty, so it IS valid. TF0 would
    declare the type ``car`` and an unrelated predicate ``car`` over it; with
    ``Car`` false everywhere the formula fails, so TF0 answered 'refuted' for what
    the other routes prove. The pair is refused, naming both."""
    for write in (generate_tff_problem, generate_tff_problem_with_mapping):
        message = raises_not_implemented(lambda: write([], CAR_SORT_CONCLUSION))
        assert "the sort 'Car' and the predicate 'Car'" in message and "TF0 identifier 'car'" in message
        assert "rename one of the two" in message and "fof writer" in message
    assert "the sort 'Car'" in raises_not_implemented(lambda: formula_to_tff(CAR_SORT_CONCLUSION))
    assert z3_status(CAR_SORT_CONCLUSION, []) == "proved"


def test_a_sort_and_a_predicate_of_another_spelling_or_arity_are_refused_too():
    # ``car`` (sort) and ``Car`` (predicate) are one word; so are a unary sort and a binary predicate
    spelled = SortedQuantifier("∀", X, "car", Atom("Car", (X,)))
    assert "the sort 'car' and the predicate 'Car'" in raises_not_implemented(lambda: generate_tff_problem([], spelled))
    binary = SortedQuantifier("∀", X, "Car", Atom("Car", (X, X)))
    assert "the sort 'Car' and the predicate 'Car'" in raises_not_implemented(lambda: generate_tff_problem([], binary))


def test_the_message_does_not_depend_on_the_order_of_the_formulas():
    one = SortedQuantifier("∀", X, "Zed", Atom("Q", (X,)))
    two = SortedQuantifier("∀", X, "Zed", Atom("Zed", (X,)))
    first = raises_not_implemented(lambda: generate_tff_problem([one], two))
    second = raises_not_implemented(lambda: generate_tff_problem([two], one))
    assert first == second


def test_a_sort_next_to_a_differently_named_predicate_is_written_as_before():
    """Control. Sort ``Car``, predicate ``Truck``: two names, hand-derived text."""
    text = generate_tff_problem([], SortedQuantifier("∃", Y, "Car", Atom("Truck", (Y,))))
    assert text == ("tff(sort_decl_1, type, car: $tType ).\n"
                    "tff(pred_decl_2, type, truck: car > $o ).\n"
                    "tff(goal, conjecture, (?[Y: car]: truck(Y)) ).\n")


@needs_vampire
def test_the_refused_tf0_text_would_have_answered_a_different_question_than_z3():
    """The text the TF0 writer used to write, spelled out, is not a theorem for
    Vampire (``CounterSatisfiable``), while z3 and Vampire on the fof route prove the
    entailment: that disagreement is why the pair is refused."""
    old_tf0_text = ("tff(sort_decl_1, type, car: $tType ).\n"
                    "tff(pred_decl_2, type, car: car > $o ).\n"
                    "tff(goal, conjecture, (?[Y: car]: car(Y)) ).\n")
    assert szs_status(old_tf0_text) == "CounterSatisfiable"
    assert z3_status(CAR_SORT_CONCLUSION, []) == "proved"
    assert generate_tptp_problem([], CAR_SORT_CONCLUSION).startswith("fof(nonempty_sort_1")
    for status in prover_statuses([], CAR_SORT_CONCLUSION, tff=False):
        assert status == "proved"


def test_the_tfa_writer_has_no_sorts_so_the_pair_cannot_arise_and_a_sorted_node_is_refused_by_name():
    sorted_formula = SortedQuantifier("∃", Y, "Car", Atom("Car", (Y,)))
    message = raises_not_implemented(lambda: generate_tff_arith_problem([], sorted_formula, sort="int"))
    assert "'SortedQuantifier'" in message


# ===========================================================================
# What the single-formula guard could not see
# ===========================================================================

def test_a_number_and_a_constant_spelled_like_it_are_refused():
    """``Number(1)`` and ``Constant('1')`` are two symbols of the kit (a number, and a
    constant that the kit's own TPTP reader makes of ``'1'``) written as the one word
    ``1``: ``¬(1 = '1')`` is satisfiable, its image ``~((1 = 1))`` is not."""
    atom = Atom("R", (Number(1), Constant("1")))
    message = raises_not_implemented(atom.to_tptp)
    assert "the number 1 and the constant '1'" in message and "TPTP identifier '1'" in message
    assert "the constant '1' and the number 1" in raises_not_implemented(Atom("R", (Constant("1"), Number(1))).to_tptp)
    assert "the number 1.5 and the constant '1.5'" in raises_not_implemented(
        Atom("R", (Number(1.5), Constant("1.5"))).to_tptp)


def test_the_kits_own_reader_produces_the_numeral_constant_pair():
    parsed = parse_tptp_formula("r(1, '1')")
    assert parsed == Atom("R", (Number(1), Constant("1")))
    assert "the number 1 and the constant '1'" in raises_not_implemented(parsed.to_tptp)


def test_numbers_alone_and_the_same_number_twice_are_not_refused():
    assert Atom("R", (Number(1), Number(1.5), Number(1))).to_tptp() == "r(1,1.5,1)"
    # 1 and 1.0 are ONE numeral (a value has one spelling: Number(1.0) is Number(1)), so they are
    # one word, written twice; they used to print as '1' and '1.0'
    assert Atom("R", (Number(1), Number(1.0))).to_tptp() == "r(1,1)"


def test_an_arithmetic_symbol_and_a_symbol_written_like_it_are_refused():
    """``+`` is written ``$sum``; a function named ``$sum`` is written ``$sum`` too, so
    ``a + b = $sum(a, b)`` — satisfiable, not valid — would be written as a tautology.
    The same holds for ``<`` (``$less``) and a predicate named ``$less``."""
    clash = Atom("=", (Function("+", (A, B)), Function("$sum", (A, B))))
    message = raises_not_implemented(clash.to_tptp)
    assert "the arithmetic function '+' and the function '$sum'" in message
    assert "TPTP identifier '$sum'" in message
    assert "the arithmetic function '+' and the constant '$sum'" in raises_not_implemented(
        Atom("=", (Function("+", (A, B)), Constant("$sum"))).to_tptp)
    assert "the comparison '<' and the predicate '$less'" in raises_not_implemented(
        And(Atom("<", (A, B)), Atom("$less", (A, B))).to_tptp)
    # the reader makes the pair out of text
    parsed = parse_tptp_formula("'$sum'(a,b) = $sum(a,b)")
    assert "TPTP identifier '$sum'" in raises_not_implemented(parsed.to_tptp)


def test_arithmetic_and_comparison_symbols_alone_are_written_as_before():
    formula = And(Atom("=", (A, B)), And(Atom("≠", (A, B)), And(Atom("<", (A, B)), Atom("≥", (A, B)))))
    assert formula.to_tptp() == "((a = b) & ((a != b) & ($less(a,b) & $greatereq(a,b))))"
    assert Atom("=", (Function("+", (A, B)), Function("*", (A, B)))).to_tptp() == "($sum(a,b) = $product(a,b))"


def test_two_variables_that_are_one_tptp_variable_are_refused():
    """A TPTP variable is the upper-case word, so ``x`` and ``X`` are one. ``∀x ∃X
    R(x, X)`` is satisfiable-not-valid (``R`` = 'differs' on two elements holds of
    every x for some X); written ``![X]: ?[X]: r(X,X)`` it says ``∃X R(X, X)``,
    which that ``R`` falsifies."""
    nested = Quantifier("∀", Variable("x"), Quantifier("∃", Variable("X"),
                                                       Atom("R", (Variable("x"), Variable("X")))))
    message = raises_not_implemented(nested.to_tptp)
    assert "the variable 'x' and the variable 'X'" in message and "TPTP identifier 'X'" in message
    # ı (dotless i) and i are one variable too: both upper-case to I
    dotless = Quantifier("∀", Variable("ı"), Quantifier("∃", Variable("i"), Atom("R", (Variable("ı"), Variable("i")))))
    assert "TPTP identifier 'I'" in raises_not_implemented(dotless.to_tptp)


def test_variables_that_differ_and_one_variable_reused_are_not_refused():
    nested = Quantifier("∀", X, Quantifier("∃", Y, Quantifier("∃", X, Atom("R", (X, Y)))))
    assert nested.to_tptp() == "(![X]: (?[Y]: (?[X]: r(X,Y))))"


def test_the_writers_refuse_two_variables_of_one_formula_and_not_of_two_formulas():
    nested = Quantifier("∀", Variable("x"), Quantifier("∃", Variable("X"),
                                                       Atom("R", (Variable("x"), Variable("X")))))
    for write in (lambda: generate_tptp_problem([], nested), lambda: generate_tptp_problem_with_mapping([nested], nested),
                  lambda: generate_tff_problem([], nested), lambda: generate_tff_problem_with_mapping([nested]),
                  lambda: generate_tff_arith_problem([], nested, sort="int"),
                  lambda: formula_to_tff(nested)):
        message = raises_not_implemented(write)
        assert "the variable 'x' and the variable 'X'" in message
    # Two quantifiers in two premises bind separately: x in one, X in the other is fine.
    first = Quantifier("∀", Variable("x"), Atom("P", (Variable("x"),)))
    second = Quantifier("∀", Variable("X"), Atom("Q", (Variable("X"),)))
    assert generate_tptp_problem([first], second) == (
        "fof(premise_1, axiom, (![X]: p(X))).\nfof(goal, conjecture, (![X]: q(X))).\n")
    assert generate_tff_problem([first], second) == (
        "tff(pred_decl_1, type, p: $i > $o ).\ntff(pred_decl_2, type, q: $i > $o ).\n"
        "tff(premise_1, axiom, (![X: $i]: p(X)) ).\ntff(goal, conjecture, (![X: $i]: q(X)) ).\n")


def test_the_reader_cannot_produce_the_variable_pair_so_only_hand_built_nodes_meet_it():
    # TPTP's X is read as the kit's lower-case variable: the pair needs hand-built nodes
    assert parse_tptp_formula("![X]: ?[Y]: r(X, Y)") == Quantifier(
        "∀", X, Quantifier("∃", Y, Atom("R", (X, Y))))


# --- a name that is not a TPTP word is not a rendering (single formula) ------------

@pytest.mark.parametrize("formula, name, word", [
    (Atom("has-part", (A,)), "has-part", "has-part"),
    (Atom("P", (Constant("has-part"),)), "has-part", "has-part"),
    (Atom("P", (Function("has.part", (A,)),)), "has.part", "has.part"),
    (Atom("P", (Constant("2008SummerOlympics"),)), "2008SummerOlympics", "2008SummerOlympics"),
    (Atom("P", (Constant("_x"),)), "_x", "_x"),
    (Atom("Größe", (A,)), "Größe", "größe"),
    (Atom("P", (Function("größe", (A,)),)), "größe", "größe"),
])
def test_a_name_that_is_not_a_tptp_word_is_refused_by_name_never_written_as_it_is(formula, name, word):
    """An unquoted TPTP name is ``[a-z][A-Za-z0-9_]*`` after the fold; Vampire and E
    reject text with anything else (``has-part``: 'just read -'), so the text of such a
    rendering helps nobody. (A constant is transliterated, ``θ`` is ``theta``.)"""
    message = raises_not_implemented(formula.to_tptp)
    assert f"name {name!r} would be written as {word!r}" in message
    assert "not a TPTP word" in message and "generate_tptp_problem_with_mapping" in message


def test_a_constant_with_a_greek_letter_is_transliterated_and_not_refused():
    assert Atom("P", (Constant("θ"),)).to_tptp() == "p(theta)"
    assert Atom("P", (Constant("Ünï"),)).to_tptp() == "p(u00dcnu00ef)"


def test_the_collision_wins_over_the_legality_refusal():
    clash = Iff(Atom("P", (Constant("has-part"),)), Atom("P", (Constant("Has-part"),)))
    message = raises_not_implemented(clash.to_tptp)
    assert "distinct constant/function names 'has-part' and 'Has-part'" in message


# ===========================================================================
# A problem without a conclusion
# ===========================================================================

SAT_PREMISES = [Quantifier("∀", X, Implies(Atom("P", (X,)), Atom("Q", (X,)))), Atom("P", (A,))]
UNSAT_PREMISES = SAT_PREMISES + [Not(Atom("Q", (A,)))]


def test_no_conclusion_writes_no_conjecture_in_the_three_writers():
    """Hand-derived texts: one axiom line per premise and nothing else."""
    premises = [Atom("P", (A,))]
    assert generate_tptp_problem(premises) == "fof(premise_1, axiom, p(a)).\n"
    assert generate_tptp_problem(premises, None) == "fof(premise_1, axiom, p(a)).\n"
    text, name_map = generate_tptp_problem_with_mapping(premises, None)
    assert text == "fof(premise_1, axiom, p(a)).\n" and name_map == TptpNameMap(
        predicate={"P": "P"}, term={"a": "a"})
    assert generate_tff_problem(premises) == (
        "tff(const_decl_1, type, a: $i ).\ntff(pred_decl_2, type, p: $i > $o ).\n"
        "tff(premise_1, axiom, p(a) ).\n")
    tff_text, tff_map = generate_tff_problem_with_mapping(premises, None)
    assert "conjecture" not in tff_text and tff_map.predicate == {"P": "P"}
    tfa_text, tfa_map = generate_tff_arith_problem(premises, sort="int")
    assert tfa_text == ("tff(const_decl_1, type, a: $int ).\ntff(pred_decl_2, type, p: $int > $o ).\n"
                        "tff(premise_1, axiom, p(a) ).\n")
    assert isinstance(tfa_map, TptpNameMap)


def test_every_check_and_rename_works_on_the_premises_alone():
    # a rename (cross kind) and its map
    text, name_map = generate_tptp_problem_with_mapping([Atom("Car", (Constant("car"),))])
    assert text == "fof(premise_1, axiom, car(car_term)).\n" and name_map.term == {"car": "car_term"}
    # same-kind refusal between two premises
    assert "distinct predicate names" in raises_not_implemented(
        lambda: generate_tptp_problem([Atom("Foo", (A,)), Atom("foo", (A,))]))
    # the non-emptiness axiom of a sort, and no goal
    sorted_only = generate_tptp_problem([SortedQuantifier("∀", X, "S", Atom("P", (X,)))])
    assert sorted_only == ("fof(premise_1, axiom, (![X]: (s(X) => p(X)))).\n"
                           "fof(nonempty_sort_1, axiom, (?[X0]: s(X0))).\n")
    # illegal names are rewritten
    assert generate_tptp_problem([Atom("P", (Constant("9lives"),))]) == "fof(premise_1, axiom, p(n9lives)).\n"
    # TF0: a sort and a predicate of one word are refused with no conclusion too
    assert "the sort 'Car'" in raises_not_implemented(lambda: generate_tff_problem([CAR_SORT_PREMISE]))
    # no formulas at all: nothing to write
    assert generate_tptp_problem([]) == "\n"


@needs_vampire
@pytest.mark.parametrize("premises, szs, satisfiable", [
    (SAT_PREMISES, "Satisfiable", True), (UNSAT_PREMISES, "Unsatisfiable", False)],
    ids=["satisfiable", "unsatisfiable"])
def test_vampire_reports_satisfiability_of_a_fof_problem_without_a_conclusion_like_z3(premises, szs, satisfiable):
    """Hand derivation: ``P ⊆ Q``, ``P(a)`` has the model P = Q = {a}; adding ``¬Q(a)``
    contradicts ``Q(a)`` (modus ponens)."""
    assert is_satisfiable(functools.reduce(And, premises)) is satisfiable
    assert szs_status(generate_tptp_problem(premises)) == szs


@needs_vampire
@pytest.mark.parametrize("premises, szs", [
    ([SortedQuantifier("∀", X, "S", Atom("P", (X,)))], "Satisfiable"),
    ([SortedQuantifier("∀", X, "S", Atom("P", (X,))), SortedQuantifier("∃", Y, "S", Not(Atom("P", (Y,))))],
     "Unsatisfiable")], ids=["satisfiable", "unsatisfiable"])
def test_vampire_reports_satisfiability_of_a_tf0_problem_without_a_conclusion_like_z3(premises, szs):
    """Hand derivation: one sorted universal is satisfied by S = {e}, P = {e}; with a
    sorted witness of ``¬P`` it is not. z3's oracle conjoins the sort's non-emptiness
    (the kit's definition)."""
    oracle = functools.reduce(And, list(premises) + list(nonempty_sort_axioms(*premises)))
    assert is_satisfiable(oracle) is (szs == "Satisfiable")
    assert szs_status(generate_tff_problem(premises)) == szs


@needs_vampire
def test_vampire_reports_an_unsatisfiable_tfa_problem_and_never_calls_a_satisfiable_one_unsatisfiable():
    """Over the integers nothing lies strictly between 1 and 2, so ``a > 1 ∧ a < 2`` is
    unsatisfiable; over the reals ``a = 1.5`` satisfies it. (Vampire cannot WITNESS
    satisfiability of an arithmetic problem, so that half is 'not Unsatisfiable'.)"""
    between = [Atom(">", (A, Number(1))), Atom("<", (A, Number(2)))]
    conjunction = functools.reduce(And, between)
    assert is_satisfiable_arith(conjunction, "int") is False
    assert is_satisfiable_arith(conjunction, "real") is True
    assert szs_status(generate_tff_arith_problem(between, sort="int")[0]) == "Unsatisfiable"
    assert szs_status(generate_tff_arith_problem(between, sort="real")[0], seconds=10) != "Unsatisfiable"


# ===========================================================================
# An ASCII name with a character that is not a TPTP word character
# ===========================================================================

def test_the_fof_writer_rewrites_a_hyphenated_name_and_records_it():
    """``-`` is U+002D, the code-point escape ``u002d`` the sanitiser already uses for
    a non-ASCII character. The predicate ``has-part`` is ``Hasu002dpart`` (kit
    predicates are capitalised; written, the first letter is folded)."""
    premises = [Quantifier("∀", X, Implies(Atom("has-part", (X,)), Atom("Bar", (X,)))),
                Atom("has-part", (Constant("c1"),))]
    conclusion = Atom("Bar", (Constant("c1"),))
    text, name_map = generate_tptp_problem_with_mapping(premises, conclusion)
    assert text == ("fof(premise_1, axiom, (![X]: (hasu002dpart(X) => bar(X)))).\n"
                    "fof(premise_2, axiom, hasu002dpart(c1)).\n"
                    "fof(goal, conjecture, bar(c1)).\n")
    assert name_map == TptpNameMap(predicate={"has-part": "Hasu002dpart", "Bar": "Bar"}, term={"c1": "c1"})
    # the map undoes the rewrite: the text reads back as the original, hyphenated formulas
    read = [apply_reverse_tptp(item.formula, name_map) for item in parse_tptp(text)]
    assert read == premises + [conclusion]


def test_distinct_names_stay_distinct_after_the_rewrite():
    """``has-part``, ``has_part`` and a name that is itself spelled ``hasu002dpart`` are
    three symbols. The legal ones keep their spelling; the rewritten one takes the
    first free spelling (``hasu002dpart2``)."""
    formula = And(Atom("has-part", (A,)), And(Atom("has_part", (A,)), Atom("hasu002dpart", (A,))))
    text, name_map = generate_tptp_problem_with_mapping([formula])
    assert text == "fof(premise_1, axiom, (hasu002dpart2(a) & (has_part(a) & hasu002dpart(a)))).\n"
    assert name_map.predicate == {"has-part": "Hasu002dpart2", "has_part": "has_part",
                                  "hasu002dpart": "hasu002dpart"}
    constants = Atom("P", (Function("f", (Constant("has-part"), Constant("has_part"), Constant("hasu002dpart"))),))
    text, name_map = generate_tptp_problem_with_mapping([constants])
    assert "f(hasu002dpart2,has_part,hasu002dpart)" in text
    assert len(set(name_map.term.values())) == len(name_map.term)


def test_names_with_other_non_word_characters_and_a_leading_underscore_are_rewritten():
    """``:`` is U+003A, ``.`` U+002E, ``$`` U+0024; a name that starts with an underscore
    is not letter-initial and gets the constant prefix ``n``."""
    cases = [(Atom("owl:Thing", (A,)), "owlu003aThing(a)"),
             (Atom("P", (Constant("a.b"),)), "p(au002eb)"),
             (Atom("P", (Function("$f", (A,)),)), "p(u0024f(a))"),
             (Atom("P", (Constant("_x"),)), "p(n_x)")]
    for formula, expected in cases:
        assert generate_tptp_problem([formula]) == f"fof(premise_1, axiom, {expected}).\n"


def test_tf0_and_tfa_rewrite_such_names_too():
    atom = Atom("has-part", (Constant("a.b"),))
    tf0, tf0_map = generate_tff_problem_with_mapping([atom])
    assert tf0 == ("tff(const_decl_1, type, au002eb: $i ).\n"
                   "tff(pred_decl_2, type, hasu002dpart: $i > $o ).\n"
                   "tff(premise_1, axiom, hasu002dpart(au002eb) ).\n")
    assert tf0_map == TptpNameMap(predicate={"has-part": "Hasu002dpart"}, term={"a.b": "au002eb"})
    tfa, tfa_map = generate_tff_arith_problem([atom], sort="int")
    assert tfa == ("tff(const_decl_1, type, au002eb: $int ).\n"
                   "tff(pred_decl_2, type, hasu002dpart: $int > $o ).\n"
                   "tff(premise_1, axiom, hasu002dpart(au002eb) ).\n")
    assert tfa_map == tf0_map
    # a sort name is rewritten in TF0 as well (its own namespace, no map)
    sorted_formula = SortedQuantifier("∀", X, "Is-a", Atom("P", (X,)))
    assert generate_tff_problem([], sorted_formula).splitlines()[0] == "tff(sort_decl_1, type, isu002da: $tType )."


HAS_PART_PREMISES = [Quantifier("∀", X, Implies(Atom("has-part", (X,)), Atom("Bar", (X,)))),
                     Atom("has-part", (Constant("c1"),))]


@pytest.mark.skipif(_VAMPIRE is None and _eprover_ready() is not True, reason="no prover reachable")
@pytest.mark.parametrize("conclusion, expected", [
    (Atom("Bar", (Constant("c1"),)), "proved"),            # modus ponens
    (Atom("Bar", (Constant("c2"),)), "refuted"),           # c2 need not have the part
], ids=["entailed", "not-entailed"])
@pytest.mark.parametrize("route", ["fof", "tff"])
def test_provers_accept_the_rewritten_names_and_answer_like_z3(conclusion, expected, route):
    """Before: the text was ``has-part(X) => ...``; Vampire: parse error, E: 'just read -'."""
    assert z3_status(conclusion, HAS_PART_PREMISES) == expected
    for status in prover_statuses(HAS_PART_PREMISES, conclusion, tff=(route == "tff")):
        assert status == expected


@needs_vampire
def test_vampire_proves_a_tfa_problem_with_a_dotted_constant():
    """``a.b = 1 ⊢ a.b + 1 = 2`` over the integers."""
    constant = Constant("a.b")
    premises = [Atom("=", (constant, Number(1)))]
    conclusion = Atom("=", (Function("+", (constant, Number(1))), Number(2)))
    from unicode_fol_kit.atp.vampire_entailment import check_entailment_vampire_detailed
    result = check_entailment_vampire_detailed(premises, conclusion, timeout=30, sort="int", **vampire_kwargs())
    assert result["status"] == "proved"


# ===========================================================================
# One predicate at two arities is two symbols, here and in z3
# ===========================================================================

def test_one_predicate_at_two_arities_is_written_as_two_symbols():
    """``Zed(a)`` and ``Zed(a, b)``: a reader of the text sees ``zed/1`` and ``zed/2``,
    two symbols, and the writer says nothing about it. The kit's z3 route reads them
    so too, across formulas (the next test: each formula is translated in its own
    environment, and z3 overloads a name by its arity)."""
    assert generate_tptp_problem([Atom("Zed", (A,)), Atom("Zed", (A, B))], Atom("Zed", (A,))) == (
        "fof(premise_1, axiom, zed(a)).\nfof(premise_2, axiom, zed(a,b)).\nfof(goal, conjecture, zed(a)).\n")


@pytest.mark.parametrize("premises, conclusion, expected", [
    # two symbols: nothing relates Zed/1 to Zed/2
    ([Atom("Zed", (A,))], Atom("Zed", (A, B)), "refuted"),
    ([Atom("Zed", (A, B))], Atom("Zed", (A,)), "refuted"),
    # each symbol is itself entailed by its own premise
    ([Atom("Zed", (A,)), Atom("Zed", (A, B))], Atom("Zed", (A, B)), "proved"),
], ids=["one-to-two", "two-to-one", "both-given"])
def test_the_provers_and_z3_read_one_predicate_at_two_arities_alike(premises, conclusion, expected):
    """Hand derivation under the two-symbol reading: ``Zed/1`` and ``Zed/2`` are free to
    differ, so neither entails the other, and each follows from itself."""
    assert z3_status(conclusion, premises) == expected
    for status in prover_statuses(premises, conclusion):
        assert status == expected


# ===========================================================================
# The guard costs one stack frame, not none
# ===========================================================================

def _deepest_rendering_conjunction(guarded: bool) -> int:
    def renders(depth: int) -> bool:
        formula: Node = Atom("P", (A,))
        for _ in range(depth):
            formula = And(formula, Atom("Q", (B,)))
        token = None if guarded else symbols._RENDERING.set(symbols._RenderLog())
        try:
            formula.to_tptp()
            return True
        except RecursionError:
            return False
        finally:
            if token is not None:
                symbols._RENDERING.reset(token)

    low, high = 50, sys.getrecursionlimit()
    while low + 1 < high:                      # the largest depth that still renders
        middle = (low + high) // 2
        if renders(middle):
            low = middle
        else:
            high = middle
    return low


def test_the_guard_costs_one_frame_and_the_documentation_says_so():
    """Measured, not claimed: the largest left-nested conjunction that renders is the
    same with and without the guard, give or take the single wrapper frame of the
    outermost call (a wrapper on EVERY level would halve it)."""
    guarded, unguarded = _deepest_rendering_conjunction(True), _deepest_rendering_conjunction(False)
    assert 0 <= unguarded - guarded <= 2, (guarded, unguarded)
    assert "plus ONE frame" in symbols.__doc__ and "exactly the stack depth" not in symbols.__doc__


# ===========================================================================
# The repair layer writes a number without an exponent
# ===========================================================================

def test_the_repair_layer_prints_a_small_number_in_positional_notation():
    """``1e-07`` is not text any reader of the kit reads back. Its repr digits are
    ``1e-07``, so the positional text is ``0.0000001``; a repair that has to re-print
    the formula writes that, and the text reads back as the SAME number."""
    result = repair_tptp_formula("p(0.0000001) <=> q & r")
    assert result.repaired_text == "(p(0.0000001) <=> (q & r))"
    assert parse_tptp_formula("p(0.0000001)").args == (Number(1e-07),)
    assert parse_tptp_formula(result.repaired_text).left.args == (Number(1e-07),)
    # A float with a whole value is the integer it equals (Number(15000000000000000.0) is
    # Number(15000000000000000)), so a repair that re-prints it writes the integer.
    big = repair_tptp_formula("p(15000000000000000.0) <=> q & r")
    assert big.repaired_text == "(p(15000000000000000) <=> (q & r))"
    assert parse_tptp_formula(big.repaired_text).left.args == (Number(15000000000000000.0),)


# ===========================================================================
# The TSTP writer shares the sanitiser and the check
# ===========================================================================

def _derivation(clauses, steps):
    from unicode_fol_kit.atp.resolution_check import (
        ResolutionDerivation, ResolutionStep, verify_resolution_proof)
    built = tuple(ResolutionStep(*step) for step in steps)
    derivation = ResolutionDerivation(tuple(frozenset(c) for c in clauses), built)
    assert verify_resolution_proof(derivation).ok
    return derivation


def test_to_tstp_rewrites_a_name_that_is_not_a_tptp_word():
    """A ground literal and its negation resolve to the empty clause; the predicate
    ``has-part`` is written ``hasu002dpart`` like it is in a problem."""
    from unicode_fol_kit.atp.tstp import to_tstp
    literal = Atom("has-part", (A,))
    derivation = _derivation([{literal}, {Not(literal)}], [
        (1, frozenset({literal}), "input"), (2, frozenset({Not(literal)}), "input"),
        (3, frozenset(), "resolve", (1, 2))])
    assert to_tstp(derivation) == (
        "cnf(c1, plain, hasu002dpart(a)).\n"
        "cnf(c2, plain, ~(hasu002dpart(a))).\n"
        "cnf(c3, plain, $false, inference(resolution, [status(thm)], [c1, c2])).\n")


def test_to_tstp_refuses_two_variables_of_one_clause_that_are_one_tptp_variable():
    """The clause ``{P(x), Q(X)}`` has TWO variables; written ``p(X) | q(X)`` it has one,
    and the 'derivation' of ``Q(X)`` from it would be a different clause set. Variables
    of different clauses bind separately (``x`` in one, ``X`` in another is fine)."""
    from unicode_fol_kit.atp.tstp import to_tstp
    big = Variable("X")
    p, q = Atom("P", (X,)), Atom("Q", (big,))
    derivation = _derivation([{p, q}, {Not(p)}, {Not(q)}], [
        (1, frozenset({p, q}), "input"), (2, frozenset({Not(p)}), "input"),
        (3, frozenset({Not(q)}), "input"), (4, frozenset({q}), "resolve", (1, 2)),
        (5, frozenset(), "resolve", (3, 4))])
    assert "the variable 'x' and the variable 'X'" in raises_not_implemented(lambda: to_tstp(derivation))
    # x in one clause and X in ANOTHER bind separately: nothing to refuse, and both are ``X``
    other = Not(Atom("P", (big,)))
    separate = _derivation([{p}, {other}], [
        (1, frozenset({p}), "input"), (2, frozenset({other}), "input"),
        (3, frozenset(), "resolve", (1, 2))])
    assert to_tstp(separate) == (
        "cnf(c1, plain, p(X)).\n"
        "cnf(c2, plain, ~(p(X))).\n"
        "cnf(c3, plain, $false, inference(resolution, [status(thm)], [c1, c2])).\n")


# ===========================================================================
# What the writers mint reads back as kit text
# ===========================================================================

def test_names_the_writers_mint_for_illegal_names_read_back_as_kit_text():
    """The rewritten names are symbols of the TEXT; a formula read back from it must print
    as kit text that ``api.parse_any`` reads as the same formula (the property
    tests/test_printed_text_reads_back.py gates for every generator). The writers mint no
    bound variable here, so the check that matters is that each minted name is a legal kit
    NAME / PREDICATE."""
    from unicode_fol_kit.atp.tstp_check import _formula_alpha_equal
    premises = [Quantifier("∀", X, Implies(Atom("has-part", (X,)), Atom("Bar", (X,)))),
                Atom("Bar", (Constant("a.b"),)), Atom("Bar", (Constant("_x"),)),
                Atom("owl:Thing", (Constant("9lives"),))]
    text, _ = generate_tptp_problem_with_mapping(premises, Atom("Bar", (Constant("carl"),)))
    for item in parse_tptp(text):
        printed = item.formula.to_unicode_str()
        reparsed = api.parse_any(printed)
        assert reparsed.ok, (printed, reparsed.errors)
        assert _formula_alpha_equal(item.formula, reparsed.formula), printed
