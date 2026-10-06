"""The typed (TF0) writer asks the kit's question, or refuses.

THE KIT'S READING OF A SORT. There is ONE universe. A sort ``S`` is a non-empty subset of
it (the extension of the unary predicate ``S``) and sorts may overlap. A constant written
``c:S`` is an element of ``S`` (``c:A`` and ``c:B`` put it in both, and ``c:S`` here with a
plain ``c`` there is ONE constant). An unannotated constant, an unsorted variable and the
value of a function may be ANY element of the universe: a function has no declared result
sort. A predicate is a relation over the whole universe.

TF0 has disjoint types and the writer infers the type of every symbol position, so its text
can ask another question. The writer refuses (:class:`Tf0Refusal`) the two situations in
which it does, and one-position-two-sorts and sort-named-like-a-predicate as before:

* an unannotated constant, or a function VALUE, that the inference puts into a user sort;
* an equation with a bare variable bound by an UNSORTED quantifier, in a problem that has
  a user sort.

Every verdict below was derived BY HAND from the definition (the structure is written in
the table), never taken from a prover. The live tests then check the other direction: the
``fof`` text answers every problem as the definition says, and whatever the writer still
accepts is answered the same on the TF0 text.
"""

import itertools
import random
import shutil
from typing import List, NamedTuple, Optional, Tuple

import pytest

from unicode_fol_kit import api
from unicode_fol_kit.atp import eprover_backend as _eb
from unicode_fol_kit.atp import protocol as _protocol
from unicode_fol_kit.atp import vampire_entailment as _ve
from unicode_fol_kit.atp._tptp_problem import (
    generate_tptp_problem_for_prover, generate_tptp_problem_with_mapping,
)
from unicode_fol_kit.atp.eprover_backend import (
    check_entailment_eprover_detailed, eprover_available,
)
from unicode_fol_kit.atp.protocol import VampireBackend, get_backend
from unicode_fol_kit.atp.tptp_ncl import to_tptp_ncl
from unicode_fol_kit.atp.tptp_tff import (
    Tf0Refusal, check_typed_reading, formula_to_tff, generate_tff_problem,
    generate_tff_problem_with_mapping, infer_tff_signature, problem_needs_tff,
)
from unicode_fol_kit.atp.vampire_entailment import (
    _generate_vampire_input, check_entailment_vampire_detailed,
    check_logical_entailment_vampire,
)
from unicode_fol_kit.fol._msfl_nodes import SortedConstant, SortedQuantifier
from unicode_fol_kit.fol.nodes import (
    And, Atom, Constant, Function, Iff, Implies, Not, Or, Quantifier, Variable,
)


def parse(text):
    """Text in, formula out. A formula that mixes a sorted and an unsorted binder, or a plain
    and a sorted constant in one equation, is not one the text grammars read (a text is
    either all sorted or all unsorted): those problems are built as trees below."""
    result = api.parse_any(text)
    assert result.formula is not None, text
    return result.formula


CONTRA = "Contra ∧ ¬Contra"     # the premises are unsatisfiable iff they entail this


def _x(name="x"):
    return Variable(name)


def unsorted_equation():
    """``∀x ∀y x = y`` -- the universe has one element."""
    return Quantifier("∀", _x("x"), Quantifier("∀", _x("y"), Atom("=", [_x("x"), _x("y")])))


def sorted_equation(sort="A"):
    """``∀x:A ∀z:A x = z`` -- any two elements of A are equal."""
    return SortedQuantifier("∀", _x("x"), sort, SortedQuantifier(
        "∀", _x("z"), sort, Atom("=", [_x("x"), _x("z")])))


class Case(NamedTuple):
    name: str
    premises: Tuple[object, ...]          # text, or a formula tree where the grammar cannot say it
    conclusion: Optional[object]          # None: the premises alone (satisfiable or not?)
    verdict: str                   # "valid" | "invalid" | "unsat" | "sat", by the definition
    tf0: str                       # "accepted" or the Tf0Refusal.reason
    why: str                       # the structure or the argument, by hand
    mentions: Tuple[str, ...] = ()  # what the refusal message must name


CASES: List[Case] = [
    # ---- an unannotated constant that the inference puts into a sort -----------------------
    Case("unannotated constant at a sorted position, invalid",
         ("∀x:Human Mortal(x)",), "Mortal(socrates)", "invalid", "unsorted_term_in_sort",
         "U={0,1}, Human={0}, Mortal={0}, socrates=1: the premise holds, Mortal(socrates) does not",
         ("'socrates'", "'Human'", "written with a sort nowhere", "socrates:Human", "fof writer")),
    Case("unannotated constant, sorted only by the conclusion's binder, invalid",
         ("Mortal(socrates)",), "∃x:Human Mortal(x)", "invalid", "unsorted_term_in_sort",
         "U={0,1}, Human={1}, Mortal={0}, socrates=0: Mortal(socrates) holds, no Human is Mortal",
         ("'socrates'", "'Human'", "socrates:Human", "fof writer")),
    Case("unannotated constant tied to a sorted one by an equation, valid but refused",
         ("∀x:S P(x)", Atom("=", [Constant("carol"), SortedConstant("dora", "S")])),
         "P(carol)", "valid", "unsorted_term_in_sort",
         "dora is in S, carol = dora, so carol is in S and P(carol): valid. The condition is "
         "sufficient, not necessary, and the fof route answers it",
         ("'carol'", "'S'", "carol:S", "fof writer")),
    Case("constant annotated in one occurrence only",
         ("P(carl)", "Q(carl:A)"), "∃x:A P(x)", "valid", "accepted",
         "carl is ONE constant and the sorted occurrence puts it in A, so x=carl witnesses"),
    Case("unannotated constant that meets only an unsorted position",
         ("∀x:A P(x)", "∀y Q(y)", "Q(socrates)"), "∃z:A P(z)", "valid", "accepted",
         "A is not empty and every A is P; socrates is only in Q's unsorted position"),
    # ---- the value of a function that the inference puts into a sort -----------------------
    Case("function value at a sorted position, invalid",
         ("∀x:Foo R(x)", "Q(g(alpha))"), "R(g(alpha))", "invalid", "unsorted_term_in_sort",
         "U={0,1}, Foo={0}, R={0}, alpha=0, g(0)=1, Q={1}: both premises hold, R(g(alpha)) does not",
         ("'g'", "'Foo'", "function", "fof writer")),
    Case("function value threaded into a sort by another premise, valid but refused",
         ("∀x:A P(g(x))", "∀y:A P(y)"), "∃z:A P(g(z))", "valid", "unsorted_term_in_sort",
         "A is not empty: take a in A, P(g(a)) by the first premise. The inference types g's "
         "value as A, so the writer refuses it, and the fof route answers it",
         ("'g'", "'A'", "fof writer")),
    Case("function argument is a sort, the value is not",
         ("∀x:A P(g(x))",), "∃y:A P(g(y))", "valid", "accepted",
         "take a in A (non-empty): P(g(a)); the witness is y=a"),
    Case("function of a sorted constant",
         ("P(g(carl:A))",), "∃x:A P(g(x))", "valid", "accepted",
         "carl is in A and P(g(carl)): the witness is x=carl"),
    # ---- an equation over an unsorted variable, next to a sort -----------------------------
    Case("unsorted equation, then a sorted one: valid",
         ("∀x ∀y x = y",), "∀x:A ∀z:A x = z", "valid", "unsorted_equality",
         "the universe has ONE element and A is a subset of it, so any two elements of A are equal",
         ("x = y", "UNSORTED", "'A'", "fof writer")),
    Case("unsorted equation, then a sorted disequality: unsatisfiable",
         ("∀x ∀y x = y", "∃x:A ∃z:A ¬(x = z)"), None, "unsat",  "unsorted_equality",
         "A would need two elements of a one-element universe",
         ("UNSORTED", "'A'", "fof writer")),
    Case("unsorted disequality with a constant, valid conclusion, refused",
         ("∃x ¬(x = alpha)",), "(∃y:A P(y)) ∨ ¬(∃y:A P(y))", "valid", "unsorted_equality",
         "the conclusion is a tautology. A disequality counts as an equation, and the writer "
         "refuses it though the typed text happens to answer it correctly",
         ("UNSORTED", "'A'")),
    Case("equation between sorted variables only",
         ("∀x:A ∀y:A x = y",), "∀z:A ∀w:A w = z", "valid", "accepted",
         "the premise says any two A's are equal, and so does the conclusion"),
    Case("equation between constants only",
         ("carl:A = dora:A", "P(carl:A)"), "P(dora:A)", "valid", "accepted",
         "carl = dora, so P(dora)"),
    Case("unsorted equation without any sort",
         ("∀x ∀y x = y",), "∀z ∀w z = w", "valid", "accepted",
         "no user sort occurs: the unsorted variables are the whole universe in both readings"),
    Case("counting alone: the witnesses are sorted",
         ("∃≥2 x:A P(x)",), None, "sat", "accepted",
         "U={0,1}, A={0,1}, P={0,1}: two distinct A's that are P"),
    Case("counting next to an unsorted equation",
         ("∀x ∀y x = y", "∃≥2 x:A P(x)"), None, "unsat", "unsorted_equality",
         "a one-element universe has no two distinct A's",
         ("UNSORTED", "'A'")),
    # ---- the refusals that were there before ------------------------------------------------
    Case("one constant, two sorts",
         ("P(carl:A)", "Q(carl:B)"), "∃x:A Q(x)", "valid", "sort_conflict",
         "carl is in A and in B and Q(carl): the witness is x=carl",
         ("'A'", "'B'", "fof writer")),
    Case("one position holding a sort and the unsorted type",
         ("∀x:A P(x)", "∀y P(y)"), "∀z:A P(z)", "valid", "sort_conflict",
         "the second premise already says every element is P",
         ("'A'", "$i", "fof writer")),
    Case("a sort and a predicate of one name",
         (), "∃y:Car Car(y)", "valid", "sort_predicate_name",
         "the sort Car and the predicate Car are ONE symbol, and the sort is not empty",
         ("'Car'", "sort", "predicate", "fof writer")),
]


def _node(value):
    return parse(value) if isinstance(value, str) else value


def _problem(case: Case):
    premises = [_node(t) for t in case.premises]
    conclusion = None if case.conclusion is None else _node(case.conclusion)
    return premises, conclusion


def _ids(cases):
    return [c.name for c in cases]


# =============================================================================
# The writer, by hand
# =============================================================================

def test_tf0_refusal_is_both_a_value_error_and_a_not_implemented_error():
    """Code that caught the sort conflict as a ValueError or the sort-and-predicate clash as a
    NotImplementedError keeps working."""
    assert issubclass(Tf0Refusal, ValueError) and issubclass(Tf0Refusal, NotImplementedError)
    with pytest.raises(ValueError):
        generate_tff_problem([parse("P(carl:A)"), parse("Q(carl:B)")], parse("∃x:A Q(x)"))
    with pytest.raises(NotImplementedError):
        generate_tff_problem([], parse("∃y:Car Car(y)"))


@pytest.mark.parametrize("case", CASES, ids=_ids(CASES))
def test_the_writer_accepts_or_refuses_each_boundary_case_as_derived(case):
    premises, conclusion = _problem(case)
    if case.tf0 == "accepted":
        text, _ = generate_tff_problem_with_mapping(premises, conclusion)
        assert text.startswith("tff(")
        check_typed_reading(premises + ([] if conclusion is None else [conclusion]))
    else:
        with pytest.raises(Tf0Refusal) as refused:
            generate_tff_problem_with_mapping(premises, conclusion)
        assert refused.value.reason == case.tf0
        # the shared check refuses the same problems (with the same reasons), except that
        # it does not read the spelling of names, so a refusal that only the writer's
        # name folding finds is not its business
        with pytest.raises(Tf0Refusal) as shared:
            check_typed_reading(premises + ([] if conclusion is None else [conclusion]))
        assert shared.value.reason == case.tf0


@pytest.mark.parametrize("case", [c for c in CASES if c.tf0 != "accepted"],
                         ids=_ids([c for c in CASES if c.tf0 != "accepted"]))
def test_each_refusal_names_the_term_the_sort_the_reason_and_what_to_write_instead(case):
    premises, conclusion = _problem(case)
    with pytest.raises(Tf0Refusal) as refused:
        generate_tff_problem_with_mapping(premises, conclusion)
    message = str(refused.value)
    for needle in case.mentions:
        assert needle in message, (needle, message)
    # The refusal names the entry point that was called (it used to open with the name of
    # the shared body, ``generate_tff_problem``, whichever of the writers was called).
    assert message.startswith("generate_tff_problem_with_mapping:")


def test_a_refusal_does_not_depend_on_the_order_of_the_premises():
    """The checks run over sorted names, so the same problem is refused for the same
    reason and about the same term whichever way round the premises are given."""
    for first, second in itertools.permutations(
            [parse("∀x:Foo R(x)"), parse("Q(g(alpha))")]):
        with pytest.raises(Tf0Refusal) as refused:
            generate_tff_problem([first, second], parse("R(g(alpha))"))
        assert refused.value.reason == "unsorted_term_in_sort"
        assert "'g'" in str(refused.value)


def test_a_problem_without_a_sort_is_never_refused_for_its_equations_or_terms():
    """No user sort, no refusal: tff=True on a plain problem writes all-$i TF0 (the typed
    writer's own contract), whatever the equations and function values look like."""
    premises = [parse("∀x ∀y x = y"), parse("P(f(alpha))")]
    text = generate_tff_problem(premises, parse("∃z P(z)"))
    assert "$tType" not in text and text.startswith("tff(")


def test_the_quantifier_that_binds_the_variable_of_an_equation_is_the_innermost_one():
    """Scoping. ``∀x (R(x) → ∀y:A ∀x:A x = y)``: the equation's x is bound by the SORTED inner
    quantifier (it shadows the unsorted outer x, which only R(x) uses), so both sides are
    sorted variables and the writer accepts the problem. ``∀x:A (R(x) ∧ ∀x x = carol)`` is the
    other way round: the equation's x is bound by the UNSORTED inner quantifier, a bare
    unsorted variable next to the sort A, and the writer refuses it."""
    x, y = Variable("x"), Variable("y")
    shadowed_by_a_sorted_binder = Quantifier("∀", x, Implies(
        Atom("R", [x]),
        SortedQuantifier("∀", y, "A", SortedQuantifier("∀", x, "A", Atom("=", [x, y])))))
    text = generate_tff_problem([shadowed_by_a_sorted_binder], parse("∃z R(z)"))
    assert "(![Y: a]: (![X: a]: X = Y))" in text            # the equation is between two a's
    shadowed_by_an_unsorted_binder = SortedQuantifier("∀", x, "A", And(
        Atom("R", [x]), Quantifier("∀", x, Atom("=", [x, Constant("carol")]))))
    with pytest.raises(Tf0Refusal) as refused:
        generate_tff_problem([shadowed_by_an_unsorted_binder], parse("P(carol)"))
    assert refused.value.reason == "unsorted_equality"


def test_formula_to_tff_refuses_like_the_problem_writer():
    """``(∀x:Human Mortal(x)) → Mortal(socrates)`` as ONE formula, built as a tree (the text
    grammars read an all-sorted or an all-unsorted text, not this mixture): the single-formula
    writer types the constant ``socrates`` as Human through Mortal's argument position, and
    refuses it, as the problem writer does. In the kit's reading socrates may be anything."""
    one_formula = Implies(
        SortedQuantifier("∀", _x(), "Human", Atom("Mortal", [_x()])),
        Atom("Mortal", [Constant("socrates")]))
    with pytest.raises(Tf0Refusal) as refused:
        formula_to_tff(one_formula)
    assert refused.value.reason == "unsorted_term_in_sort" and "'socrates'" in str(refused.value)


def test_signature_inference_keeps_inferring_what_the_writer_refuses():
    """``infer_tff_signature`` reports the types the writers' union-find assigns; it is not a
    decision route, so a function value that the writer would refuse is still reported as
    the sort it is inferred to have."""
    formulas = [parse("∀x:Human Adult(father_of(x))"), parse("∀y:Human Adult(y)")]
    assert infer_tff_signature(formulas).functions["father_of"].result_sort == "Human"
    with pytest.raises(Tf0Refusal):
        generate_tff_problem(formulas, parse("∃x:Human Adult(father_of(x))"))


@pytest.mark.parametrize("premises, conclusion, reason", [
    ([And(Atom("P", [Constant("a")]), Atom("Q", [Function("a", [Constant("b")])]))],
     Atom("R", []), "constant_function_clash"),
    ([Atom("P", [Constant("a")]), Atom("P", [Constant("a"), Constant("b")])],
     Atom("R", []), "arity_conflict"),
    ([Atom("P", [Function("f", [Constant("a")])]), Atom("Q", [Function("f", [])])],
     Atom("R", []), "arity_conflict"),
    ([SortedQuantifier("∀", Variable("x"), "A", Atom("P", [Variable("x"), Variable("y")]))],
     Atom("R", []), "free_variable"),
])
def test_the_other_refusals_of_the_writer_are_refusals_of_the_same_class(premises, conclusion, reason):
    """A free variable, one symbol at two arities and a name that is both a constant and a
    function cannot be written in TF0 either; they are the same class of refusal, so that a
    backend in its automatic mode writes fof instead of letting a ValueError escape."""
    with pytest.raises(Tf0Refusal) as refused:
        generate_tff_problem(premises, conclusion)
    assert refused.value.reason == reason


# =============================================================================
# The automatic mode falls back to fof, with the reason; tff=True reports the refusal
# =============================================================================

def test_the_dialect_helper_falls_back_in_the_automatic_mode_and_says_why():
    premises = [parse("∀x:Human Mortal(x)")]
    conclusion = parse("Mortal(socrates)")
    built = generate_tptp_problem_for_prover(premises, conclusion)          # tff=None
    assert built.dialect == "fof" and built.text.startswith("fof(")
    assert "'socrates'" in built.tff_refusal
    assert built.fallback_note.startswith("the typed (TF0) writer refused this problem")
    assert built.tff_refusal in built.fallback_note
    with pytest.raises(Tf0Refusal):
        generate_tptp_problem_for_prover(premises, conclusion, tff=True)
    forced = generate_tptp_problem_for_prover(premises, conclusion, tff=False)
    assert forced.dialect == "fof" and forced.tff_refusal is None and forced.fallback_note is None
    accepted = generate_tptp_problem_for_prover(
        [parse("∀x:Human Mortal(x)")], parse("Mortal(socrates:Human)"))
    assert accepted.dialect == "tff" and accepted.tff_refusal is None
    # (a constant: the fof writer refuses an unbound variable such as the ``a`` of ``P(a)``)
    unsorted = generate_tptp_problem_for_prover([parse("P(carl)")], parse("P(carl)"))
    assert unsorted.dialect == "fof" and unsorted.tff_refusal is None


def test_generate_vampire_input_writes_fof_for_a_refused_problem_unless_tff_is_forced():
    premises, conclusion = [parse("∀x:Human Mortal(x)")], parse("Mortal(socrates)")
    assert _generate_vampire_input(premises, conclusion).startswith("fof(")
    assert _generate_vampire_input(premises, conclusion, tff=False).startswith("fof(")
    with pytest.raises(Tf0Refusal):
        _generate_vampire_input(premises, conclusion, tff=True)
    with pytest.raises(Tf0Refusal):
        _eb._generate_tptp_problem(premises, conclusion, tff=True)
    assert _eb._generate_tptp_problem(premises, conclusion).startswith("fof(")


class _FakeVampire:
    """Stands in for the Vampire process: records the problem, answers with a canned SZS line."""

    def __init__(self, monkeypatch, szs="CounterSatisfiable"):
        self.problem = None
        self.szs = szs
        monkeypatch.setattr(_ve, "_spawn_vampire", self._spawn)
        monkeypatch.setattr(_protocol, "_binary_version", lambda *a, **k: None)
        monkeypatch.setattr(VampireBackend, "_binary", staticmethod(lambda: "fake-vampire"))
        # The fake is a binary on this host. With the WSL switch on in the environment the kit would look
        # for "fake-vampire" inside WSL (available() answers for the route the runner takes), so the
        # switch is off for as long as the fake stands in.
        monkeypatch.delenv("UFK_VAMPIRE_WSL", raising=False)

    def _spawn(self, input_str, vampire_path, timeout=30, use_wsl=False, extra_args=()):
        self.problem = input_str
        return f"% SZS status {self.szs} for the problem\n", False


class _FakeE:
    def __init__(self, monkeypatch, szs="CounterSatisfiable"):
        self.problem = None
        self.szs = szs
        monkeypatch.setattr(_eb, "_discover", lambda *a: ("eprover", False))
        monkeypatch.setattr(_eb, "_binary_version", lambda *a, **k: None)
        monkeypatch.setattr(_eb, "_run_tptp_prover", self._run)

    def _run(self, problem, command, args, use_wsl, timeout_s):
        self.problem = problem
        return f"# SZS status {self.szs}\n", False


def test_vampire_backend_automatic_mode_falls_back_to_fof_and_the_detail_says_so(monkeypatch):
    fake = _FakeVampire(monkeypatch)
    verdict = get_backend("vampire").decide(
        parse("Mortal(socrates)"), [parse("∀x:Human Mortal(x)")])
    assert fake.problem.startswith("fof(")                       # what Vampire was given
    assert verdict.status == "refuted"                           # CounterSatisfiable, by the fake
    assert "SZS status CounterSatisfiable" in verdict.detail
    assert "typed (TF0) writer refused this problem" in verdict.detail
    assert "'socrates'" in verdict.detail and "written with a sort nowhere" in verdict.detail
    result = check_entailment_vampire_detailed(
        [parse("∀x:Human Mortal(x)")], parse("Mortal(socrates)"), "fake", tff=None)
    assert result["dialect"] == "fof" and "'socrates'" in result["tff_fallback"]


def test_vampire_backend_without_a_refusal_runs_tf0_and_has_no_fallback_note(monkeypatch):
    fake = _FakeVampire(monkeypatch, szs="Theorem")
    verdict = get_backend("vampire").decide(
        parse("Mortal(socrates:Human)"), [parse("∀x:Human Mortal(x)")])
    assert fake.problem.startswith("tff(") and verdict.status == "proved"
    assert "refused" not in verdict.detail


def test_vampire_backend_tff_true_reports_the_refusal_not_an_exception(monkeypatch):
    _FakeVampire(monkeypatch)
    verdict = get_backend("vampire").decide(
        parse("Mortal(socrates)"), [parse("∀x:Human Mortal(x)")], tff=True)
    assert (verdict.status, verdict.reason) == ("unknown", "unsupported")
    assert "'socrates'" in verdict.detail and "fof writer" in verdict.detail


def test_vampire_backend_tff_false_is_fof_without_a_note(monkeypatch):
    fake = _FakeVampire(monkeypatch)
    verdict = get_backend("vampire").decide(
        parse("Mortal(socrates)"), [parse("∀x:Human Mortal(x)")], tff=False)
    assert fake.problem.startswith("fof(") and "refused" not in verdict.detail


@pytest.mark.parametrize("backend", ["eprover", "zipperposition"])
def test_e_and_zipperposition_fall_back_to_fof_and_say_so(monkeypatch, backend):
    fake = _FakeE(monkeypatch)
    verdict = get_backend(backend).decide(
        parse("Mortal(socrates)"), [parse("∀x:Human Mortal(x)")])
    assert fake.problem.startswith("fof(") and verdict.status == "refuted"
    assert "typed (TF0) writer refused this problem" in verdict.detail
    assert "'socrates'" in verdict.detail


@pytest.mark.parametrize("backend", ["eprover", "zipperposition"])
def test_e_and_zipperposition_tff_true_report_the_refusal(monkeypatch, backend):
    _FakeE(monkeypatch)
    verdict = get_backend(backend).decide(
        parse("Mortal(socrates)"), [parse("∀x:Human Mortal(x)")], tff=True)
    assert (verdict.status, verdict.reason) == ("unknown", "unsupported")
    assert "'socrates'" in verdict.detail


def test_e_detailed_result_names_the_dialect_and_the_fallback(monkeypatch):
    _FakeE(monkeypatch)
    refused = check_entailment_eprover_detailed(
        [parse("∀x:Human Mortal(x)")], parse("Mortal(socrates)"))
    assert refused["dialect"] == "fof" and "'socrates'" in refused["tff_fallback"]
    accepted = check_entailment_eprover_detailed(
        [parse("∀x:Human Mortal(x)")], parse("Mortal(socrates:Human)"))
    assert accepted["dialect"] == "tff" and accepted["tff_fallback"] is None


def _arity_conflict():
    return ([SortedQuantifier("∀", Variable("x"), "A", Atom("P", [Variable("x")])),
             Atom("Q", [Constant("c")]), Atom("Q", [Constant("c"), Constant("d")])],
            Atom("P", [SortedConstant("e", "A")]))


def _free_variable():
    return ([SortedQuantifier("∀", Variable("x"), "A",
                              Atom("P", [Variable("x"), Variable("y")]))],
            Atom("Q", [Constant("c")]))


def _constant_function():
    return ([SortedQuantifier("∀", Variable("x"), "A", Atom("P", [Variable("x")])),
             Atom("Q", [Constant("c")]), Atom("R", [Function("c", [Constant("d")])])],
            Atom("P", [SortedConstant("e", "A")]))


@pytest.mark.parametrize("make", [
    lambda: ([parse("P(carl:A)"), parse("Q(carl:B)")], parse("∃x:A Q(x)")),
    lambda: ([parse("∀x:A P(x)"), parse("∀y P(y)")], parse("∀z:A P(z)")),
    lambda: ([], parse("∃y:Car Car(y)")),
    lambda: ([parse("∀x ∀y x = y")], parse("∀x:A ∀z:A x = z")),
    _arity_conflict, _free_variable, _constant_function,
], ids=["two sorts", "sorted and unsorted position", "sort named like a predicate",
        "unsorted equation", "arity", "free variable", "constant and function"])
def test_no_value_error_leaves_api_prove_for_a_sorted_problem(monkeypatch, make):
    """With Vampire or E in its automatic mode the refusal of the typed writer is a fallback to
    fof, never a ValueError out of ``api.prove``; with ``tff=True`` it is an unknown /
    unsupported verdict that carries the writer's message (the chain summary quotes it)."""
    premises, conclusion = make()
    _FakeVampire(monkeypatch)
    for backend, options in (("vampire", {}), ("eprover", {})):
        if backend == "eprover":
            _FakeE(monkeypatch)
        verdict = api.prove(conclusion, premises, backends=[backend], **options)
        assert verdict.status in ("refuted", "proved", "unknown", "error")
        forced = api.prove(conclusion, premises, backends=[backend], tff=True)
        assert forced.status == "unknown"
        assert f"{backend}:unknown/unsupported" in forced.detail
        assert "generate_tff_problem" in forced.detail, forced.detail     # the writer's own message
        assert "fof writer" in forced.detail


# =============================================================================
# NXF (the Leo-III route): an unsorted equation next to a sort
# =============================================================================

def _nxf_formulas():
    """Implications that mix sorted and unsorted binders, built as trees (a text is all sorted
    or all unsorted). By the definition: the first is valid (a one-element universe, A a subset
    of it) and is not a theorem of the typed text, where the unsorted variables range over $i."""
    z, w = _x("z"), _x("w")
    return [
        (Implies(unsorted_equation(), sorted_equation()), "refused",
         "valid in the kit (a one-element universe), and the typed text bounds $i, not A"),
        (Implies(unsorted_equation(),
                 SortedQuantifier("∀", z, "A", SortedQuantifier(
                     "∀", w, "A", Atom("P", [z, w])))), "refused",
         "an unsorted equation anywhere, with a sort anywhere"),
        (Implies(sorted_equation(),
                 SortedQuantifier("∀", z, "A", SortedQuantifier(
                     "∀", w, "A", Atom("=", [w, z])))), "accepted",
         "the equations are between sorted variables only: valid, and well typed"),
        (Implies(unsorted_equation(),
                 Quantifier("∀", z, Quantifier("∀", w, Atom("=", [z, w])))), "accepted",
         "no user sort: both sides range over $i, the whole universe"),
        (Implies(SortedQuantifier("∃", _x(), "A", Atom("P", [_x()])),
                 SortedQuantifier("∃", _x("y"), "A", Atom("P", [_x("y")]))), "accepted",
         "no equation at all"),
        (Implies(Quantifier("∃", _x(), Atom("≠", [_x(), Constant("alpha")])),
                 SortedQuantifier("∃", _x("y"), "A", Atom("P", [_x("y")]))), "refused",
         "a disequality with an unsorted variable counts as an equation"),
    ]


@pytest.mark.parametrize("formula, outcome, why", _nxf_formulas(),
                         ids=[f"{i}-{o}" for i, (_, o, _) in enumerate(_nxf_formulas())])
def test_nxf_refuses_an_unsorted_equation_next_to_a_sort(formula, outcome, why):
    if outcome == "accepted":
        assert to_tptp_ncl(formula).strip().endswith(").")
    else:
        with pytest.raises(Tf0Refusal) as refused:
            to_tptp_ncl(formula)
        assert refused.value.reason == "unsorted_equality"
        message = str(refused.value)
        assert message.startswith("to_tptp_ncl:") and "'A'" in message and "UNSORTED" in message
        assert "fof writer" in message
        with pytest.raises(NotImplementedError):
            to_tptp_ncl(formula)


# =============================================================================
# The Hets backend: a decision route, so a different typed reading is refused
# =============================================================================

def test_hets_refuses_a_typed_reading_that_differs_before_any_network(monkeypatch):
    from unicode_fol_kit import hets as hets_pkg

    def _boom(**kw):
        raise AssertionError("discovery must not run for a problem the backend refuses")

    monkeypatch.setattr(hets_pkg, "discover_hets_url", _boom)
    backend = get_backend("hets")
    for premises, conclusion, needle in [
            ([parse("∀x:Human Mortal(x)")], parse("Mortal(socrates)"), "'socrates'"),
            ([parse("∀x:Foo R(x)"), parse("Q(g(alpha))")], parse("R(g(alpha))"), "'g'"),
            ([parse("∀x ∀y x = y")], parse("∀x:A ∀z:A x = z"), "UNSORTED"),
            ([], parse("∃y:Car Car(y)"), "'Car'")]:
        verdict = backend.decide(conclusion, premises)
        assert (verdict.status, verdict.reason) == ("unknown", "unsupported")
        assert needle in verdict.detail and "hets:" in verdict.detail, verdict.detail


def test_hets_consistency_check_refuses_the_same_problems(monkeypatch):
    from unicode_fol_kit import hets as hets_pkg

    monkeypatch.setattr(hets_pkg, "discover_hets_url",
                        lambda **kw: (_ for _ in ()).throw(AssertionError("no network")))
    with pytest.raises(Tf0Refusal):
        get_backend("hets").check_consistency(
            [parse("∀x ∀y x = y"), parse("∃x:A ∃z:A ¬(x = z)")])


def test_the_casl_export_itself_keeps_writing_the_typed_reading():
    """``to_casl_spec`` is an export into a typed language, a designed feature: it still
    declares the unannotated constant at the sort of the position it is used in. Only a
    decision with the text is refused."""
    from unicode_fol_kit.fol.casl_export import to_casl_spec
    spec = to_casl_spec([parse("∀x:Human Mortal(x)")], conjectures=[parse("Mortal(socrates)")])
    assert "socrates : Human" in spec


# =============================================================================
# Live: Vampire and E on the boundary table, and on generated problems
# =============================================================================

_VAMPIRE = shutil.which("vampire")
_vampire = (dict(vampire_path=_VAMPIRE, use_wsl=False) if _VAMPIRE
            else dict(vampire_path="vampire", use_wsl=True))
# Whether Vampire can be run is the kit's answer for exactly the options the calls below
# pass (a native binary, else one inside WSL); the skip condition does not probe on its own,
# so a test that is skipped is one the kit would also refuse with BackendUnavailable.
_HAVE_VAMPIRE = get_backend("vampire").available_for(_vampire)

_expected_status = {"valid": "proved", "invalid": "refuted", "unsat": "proved", "sat": "refuted"}


def _goes_tff(case: Case) -> bool:
    premises, conclusion = _question(case)
    return case.tf0 == "accepted" and problem_needs_tff(premises, conclusion)


def _question(case: Case):
    """The problem as a prover is asked: a problem without a conclusion is asked whether its
    premises entail ``Contra ∧ ¬Contra`` (proved exactly when they are unsatisfiable)."""
    premises, conclusion = _problem(case)
    return premises, (parse(CONTRA) if conclusion is None else conclusion)


@pytest.mark.skipif(not _HAVE_VAMPIRE, reason="no Vampire binary reachable (native or WSL)")
@pytest.mark.parametrize("case", CASES, ids=_ids(CASES))
def test_vampire_answers_every_boundary_case_as_derived_on_the_fof_text_and_on_an_accepted_tf0_text(case):
    premises, conclusion = _question(case)
    on_fof = check_entailment_vampire_detailed(
        premises, conclusion, timeout=60, tff=False, **_vampire)
    assert on_fof["dialect"] == "fof"
    assert on_fof["status"] == _expected_status[case.verdict], (case.why, on_fof["szs_status"])
    if case.tf0 == "accepted":
        on_tf0 = check_entailment_vampire_detailed(
            premises, conclusion, timeout=60, tff=True, **_vampire)
        assert on_tf0["dialect"] == "tff"
        assert on_tf0["status"] == _expected_status[case.verdict], (case.why, on_tf0["szs_status"])
    # the automatic mode answers as the definition says, falling back where it must
    auto = check_entailment_vampire_detailed(premises, conclusion, timeout=60, **_vampire)
    assert auto["status"] == _expected_status[case.verdict]
    # TF0 is tried only for a problem with a sorted node, and used when the writer accepts it
    assert (auto["dialect"] == "tff") == _goes_tff(case)
    assert (auto["tff_fallback"] is None) == (case.tf0 == "accepted")


@pytest.mark.skipif(not eprover_available(), reason="no eprover binary found")
@pytest.mark.parametrize("case", CASES, ids=_ids(CASES))
def test_eprover_answers_every_boundary_case_as_derived_on_the_fof_text_and_on_an_accepted_tf0_text(case):
    premises, conclusion = _question(case)
    on_fof = check_entailment_eprover_detailed(premises, conclusion, tff=False, timeout=30)
    assert on_fof["status"] == _expected_status[case.verdict], (case.why, on_fof["szs_status"])
    if case.tf0 == "accepted":
        on_tf0 = check_entailment_eprover_detailed(premises, conclusion, tff=True, timeout=30)
        assert on_tf0["status"] == _expected_status[case.verdict], (case.why, on_tf0["szs_status"])
    auto = check_entailment_eprover_detailed(premises, conclusion, timeout=30)
    assert auto["status"] == _expected_status[case.verdict]
    assert (auto["dialect"] == "tff") == _goes_tff(case)


@pytest.mark.skipif(not _HAVE_VAMPIRE, reason="no Vampire binary reachable (native or WSL)")
def test_a_sorted_problem_through_api_prove_is_answered_as_the_definition_says_and_the_detail_says_how():
    """``api.prove(backends=['vampire'])`` on ``∀x:Human Mortal(x) ⊢ Mortal(socrates)``, invalid
    by the definition (U={0,1}, Human={0}, Mortal={0}, socrates=1): refuted, from the fof text,
    and the detail names the constant and says that the typed writer refused."""
    verdict = api.prove(parse("Mortal(socrates)"), [parse("∀x:Human Mortal(x)")],
                        backends=["vampire"], timeout=60000, **_vampire)
    assert verdict.status == "refuted"
    assert "typed (TF0) writer refused this problem" in verdict.detail
    assert "'socrates'" in verdict.detail
    forced = api.prove(parse("Mortal(socrates)"), [parse("∀x:Human Mortal(x)")],
                       backends=["vampire"], tff=True, timeout=60000, **_vampire)
    assert forced.status == "unknown" and "written with a sort nowhere" in forced.detail


# ---- the oracle and the generator ------------------------------------------------------------
#
# A finite-model search written from the definition above (it shares no code with the kit's
# evaluators): every structure with one or two elements, evaluated here. A countermodel it
# finds is definitive ("invalid"); finding none proves nothing.

_SORTS = ("A", "B")
_PLAIN = ("alpha", "beta", "carl")             # carl also occurs sorted: ONE constant
_SORTED = (("carl", "A"), ("dora", "B"), ("emil", "A"), ("dora", "A"))      # dora has two sorts
_VARS = ("x", "y", "z")


def _term(rng, scope, depth=0):
    roll = rng.random()
    if scope and roll < 0.45:
        return Variable(rng.choice(scope))
    if roll < 0.65:
        return Constant(rng.choice(_PLAIN))
    if roll < 0.88:
        name, sort = rng.choice(_SORTED)
        return SortedConstant(name, sort)
    if depth == 0:
        return Function("f", [_term(rng, scope, 1)])
    return Constant(rng.choice(_PLAIN))


def _atom(rng, scope):
    if rng.random() < 0.25:
        return Atom("=", [_term(rng, scope), _term(rng, scope)])
    return Atom(rng.choice(("P", "Q")), [_term(rng, scope)])


def _formula(rng, scope, depth):
    if depth == 0 or rng.random() < 0.18:
        return _atom(rng, scope)
    roll = rng.random()
    if roll < 0.14:
        return Not(_formula(rng, scope, depth - 1))
    if roll < 0.46:
        op = rng.choice((And, Or, Implies, Iff))
        return op(_formula(rng, scope, depth - 1), _formula(rng, scope, depth - 1))
    free = [v for v in _VARS if v not in scope]
    if not free:
        return _atom(rng, scope)
    var, kind = free[0], rng.choice("∀∃")
    body = _formula(rng, scope + [var], depth - 1)
    if rng.random() < 0.6:
        return SortedQuantifier(kind, Variable(var), rng.choice(_SORTS), body)
    return Quantifier(kind, Variable(var), body)


def _substitute(node, name, term):
    """``node`` with the free variable ``name`` replaced by ``term`` (the generator never rebinds a name)."""
    if isinstance(node, Variable):
        return term if node.name == name else node
    if isinstance(node, (Constant, SortedConstant)):
        return node
    if isinstance(node, Function):
        return Function(node.name, [_substitute(a, name, term) for a in node.args])
    if isinstance(node, Atom):
        return Atom(node.predicate, [_substitute(a, name, term) for a in node.args])
    if isinstance(node, Not):
        return Not(_substitute(node.formula, name, term))
    if isinstance(node, (And, Or, Implies, Iff)):
        return type(node)(_substitute(node.left, name, term), _substitute(node.right, name, term))
    if isinstance(node, SortedQuantifier):
        return SortedQuantifier(node.type, node.variable, node.sort,
                                _substitute(node.formula, name, term))
    return Quantifier(node.type, node.variable, _substitute(node.formula, name, term))


#: Sentences about how many elements there are, with a sort and without one: the family in which
#: an unsorted equation meets a sort, so that the equation check of the writer is exercised.
_UNSORTED_COUNTING = ("∀x ∀y x = y", "∃x ∃y ¬(x = y)", "∃x ∀y x = y",
                      "∀x ∀y (P(x) → (P(y) → x = y))", "∃x ∀y (P(y) → y = x)",
                      "∀x (P(x) ↔ x = alpha)", "∃x ¬(x = alpha)")
_SORTED_COUNTING = ("∃x:A ∃y:A ¬(x = y)", "∀x:A ∀y:A x = y", "∃x:A P(x)", "∃x:A ∀y:A x = y",
                    "∀x:A ∀y:A (P(x) → (P(y) → x = y))", "∃x:A ¬P(x)", "∃x:A ∃y:B ¬(x = y)")


def _counting_problem(rng):
    pick = lambda pool: parse(rng.choice(pool))          # noqa: E731 -- a local shorthand
    premises = [pick(rng.choice((_UNSORTED_COUNTING, _SORTED_COUNTING)))
                for _ in range(rng.choice((1, 2, 2)))]
    conclusion = pick(rng.choice((_UNSORTED_COUNTING, _SORTED_COUNTING)))
    if rng.random() < 0.3:
        conclusion = Not(conclusion)
    return premises, conclusion


def _problem_of(seed):
    """A third of the problems are sentences about the size of the universe (equations over
    sorted and unsorted variables); of the rest, half are random formulas and half have the SHAPE
    of an entailment, so that valid ones are common: instantiation of a sorted or an unsorted
    universal by a sorted constant, an unannotated constant or a function value, and
    generalisation from one of those. Which of them are valid is for the oracle and the provers
    to say, not for this generator."""
    rng = random.Random(seed)
    roll = rng.random()
    if roll < 0.35:
        return _counting_problem(rng)
    if roll < 0.65:
        premises = [_formula(rng, [], rng.choice((1, 2, 2, 3))) for _ in range(rng.choice((0, 1, 1, 2)))]
        return premises, _formula(rng, [], rng.choice((1, 2, 2, 3)))
    body = _formula(rng, ["w"], rng.choice((0, 1, 1, 2)))
    sort = rng.choice(_SORTS)
    name, own_sort = rng.choice(_SORTED)
    witness = rng.choice((SortedConstant(name, own_sort), SortedConstant(name, own_sort),
                          Constant(rng.choice(_PLAIN)),
                          Function("f", [Constant(rng.choice(_PLAIN))])))
    w = Variable("w")
    extra = [_formula(rng, [], 1)] if rng.random() < 0.3 else []
    shape = rng.random()
    if shape < 0.4:          # ∀w:S φ(w)  ⊢  φ(t)
        return [SortedQuantifier("∀", w, sort, body)] + extra, _substitute(body, "w", witness)
    if shape < 0.55:         # ∀w φ(w)  ⊢  φ(t)
        return [Quantifier("∀", w, body)] + extra, _substitute(body, "w", witness)
    if shape < 0.9:          # φ(t)  ⊢  ∃w:S φ(w)
        return [_substitute(body, "w", witness)] + extra, SortedQuantifier("∃", w, sort, body)
    return [_substitute(body, "w", witness)] + extra, Quantifier("∃", w, body)   # φ(t)  ⊢  ∃w φ(w)


def _symbols(formulas):
    plain, sorted_, sorts, preds, funcs = set(), {}, set(), set(), set()
    for formula in formulas:
        for node in formula.walk():
            if isinstance(node, SortedConstant):
                sorted_.setdefault(node.name, set()).add(node.sort)
                sorts.add(node.sort)
            elif isinstance(node, Constant):
                plain.add(node.name)
            elif isinstance(node, SortedQuantifier):
                sorts.add(node.sort)
            elif isinstance(node, Atom) and node.predicate != "=":
                preds.add(node.predicate)
            elif isinstance(node, Function):
                funcs.add(node.name)
    return sorted(plain | set(sorted_)), sorted_, sorted(sorts), sorted(preds), sorted(funcs)


def _value(term, model, env):
    if isinstance(term, Variable):
        return env[term.name]
    if isinstance(term, (Constant, SortedConstant)):
        return model["const"][term.name]
    return model["func"][term.name][_value(term.args[0], model, env)]


def _holds(node, model, env):
    if isinstance(node, Atom):
        if node.predicate == "=":
            return _value(node.args[0], model, env) == _value(node.args[1], model, env)
        return _value(node.args[0], model, env) in model["pred"][node.predicate]
    if isinstance(node, Not):
        return not _holds(node.formula, model, env)
    if isinstance(node, And):
        return _holds(node.left, model, env) and _holds(node.right, model, env)
    if isinstance(node, Or):
        return _holds(node.left, model, env) or _holds(node.right, model, env)
    if isinstance(node, Implies):
        return (not _holds(node.left, model, env)) or _holds(node.right, model, env)
    if isinstance(node, Iff):
        return _holds(node.left, model, env) == _holds(node.right, model, env)
    domain = model["sort"][node.sort] if isinstance(node, SortedQuantifier) else model["universe"]
    results = (_holds(node.formula, model, {**env, node.variable.name: d}) for d in domain)
    return all(results) if node.type == "∀" else any(results)


def _countermodel(premises, conclusion, max_size=2):
    consts, sorted_consts, sorts, preds, funcs = _symbols(list(premises) + [conclusion])
    for size in range(1, max_size + 1):
        universe = tuple(range(size))
        subsets = [frozenset(c) for r in range(size + 1) for c in itertools.combinations(universe, r)]
        func_tables = [dict(zip(universe, image)) for image in itertools.product(universe, repeat=size)]
        nonempty = [frozenset(c) for r in range(1, size + 1) for c in itertools.combinations(universe, r)]
        for sort_choice in itertools.product(nonempty, repeat=len(sorts)):
            sort_map = dict(zip(sorts, sort_choice))
            ranges = []
            for name in consts:
                allowed = set(universe)
                for sort in sorted_consts.get(name, ()):      # c:S is an element of EVERY sort it is given
                    allowed &= sort_map[sort]
                ranges.append(sorted(allowed))
            for const_choice in itertools.product(*ranges):
                for pred_choice in itertools.product(subsets, repeat=len(preds)):
                    for func_choice in itertools.product(func_tables, repeat=len(funcs)):
                        model = {"universe": universe, "sort": sort_map,
                                 "const": dict(zip(consts, const_choice)),
                                 "pred": dict(zip(preds, pred_choice)),
                                 "func": dict(zip(funcs, func_choice))}
                        if all(_holds(p, model, {}) for p in premises) and not _holds(conclusion, model, {}):
                            return model
    return None


_DEFINITIVE_VALID = {"Theorem", "ContradictoryAxioms", "Unsatisfiable"}
_DEFINITIVE_INVALID = {"CounterSatisfiable", "Satisfiable"}


def _kind(szs):
    if szs in _DEFINITIVE_VALID:
        return "valid"
    if szs in _DEFINITIVE_INVALID:
        return "invalid"
    return None


def _writes_tf0(premises, conclusion):
    try:
        return generate_tff_problem_with_mapping(premises, conclusion)[0] is not None
    except Tf0Refusal:
        return False


def test_the_generator_produces_accepted_and_refused_problems_of_every_kind():
    """The differential below is only worth something if the writer accepts a good share of
    the generated problems and refuses another share for each of its reasons."""
    reasons = {}
    accepted = 0
    for seed in range(400):
        premises, conclusion = _problem_of(seed)
        try:
            generate_tff_problem_with_mapping(premises, conclusion)
            accepted += 1
        except Tf0Refusal as exc:
            reasons[exc.reason] = reasons.get(exc.reason, 0) + 1
    assert accepted >= 80, (accepted, reasons)
    for reason in ("unsorted_term_in_sort", "unsorted_equality", "sort_conflict"):
        assert reasons.get(reason, 0) >= 5, (reason, reasons)


@pytest.mark.skipif(not _HAVE_VAMPIRE, reason="no Vampire binary reachable (native or WSL)")
def test_what_the_writer_accepts_is_answered_the_same_on_the_tf0_text_and_the_fof_text():
    """A differential over generated problems. For every problem: Vampire on the fof text must
    not call it valid when the definition's countermodel search (written above, one or two
    elements) finds a countermodel; and when the writer accepts the problem, Vampire on the
    TF0 text must give the same definitive answer as on the fof text. An answer that is not
    definitive (a timeout, GaveUp) is skipped, never counted as agreement."""
    compared = accepted = 0
    wrong = []
    for seed in range(1000, 1300):
        premises, conclusion = _problem_of(seed)
        counter = _countermodel(premises, conclusion)
        on_fof = check_entailment_vampire_detailed(
            premises, conclusion, timeout=60, tff=False, **_vampire)["szs_status"]
        if counter is not None and _kind(on_fof) == "valid":
            wrong.append(("fof says valid, a countermodel exists", seed, on_fof, counter))
        if not _writes_tf0(premises, conclusion):
            continue
        accepted += 1
        on_tf0 = check_entailment_vampire_detailed(
            premises, conclusion, timeout=60, tff=True, **_vampire)["szs_status"]
        if counter is not None and _kind(on_tf0) == "valid":
            wrong.append(("tf0 says valid, a countermodel exists", seed, on_tf0, counter))
        if _kind(on_fof) and _kind(on_tf0):
            compared += 1
            if _kind(on_fof) != _kind(on_tf0):
                wrong.append(("fof and tf0 differ", seed, on_fof, on_tf0))
    assert not wrong, wrong[:3]
    # (measured on these seeds: 113 accepted, all 113 answered definitively on both texts; with
    # the writer's check removed the same seeds give 14 differences and 10 answers "valid" against
    # a countermodel, so the numbers below are not slack)
    assert accepted >= 90 and compared >= 90, (accepted, compared)


@pytest.mark.skipif(not _HAVE_VAMPIRE, reason="no Vampire binary reachable (native or WSL)")
def test_a_function_value_in_a_sort_is_refused_by_tf0_and_answered_by_fof():
    """The problem the battery of ``test_tptp_tff.py`` used to hold: ``∀x:Human Adult(father_of(x)),
    ∀y:Human Adult(y) ⊢ ∃x:Human Adult(father_of(x))``. It is valid (take h in Human, which is
    not empty: Adult(father_of(h)); the witness is x=h), and the writer refuses it, because the
    inference types father_of's value as Human through Adult's argument position."""
    premises = [parse("∀x:Human Adult(father_of(x))"), parse("∀y:Human Adult(y)")]
    conclusion = parse("∃x:Human Adult(father_of(x))")
    assert not _writes_tf0(premises, conclusion)
    assert check_logical_entailment_vampire(premises, conclusion, tff=False, **_vampire) is True
    with pytest.raises(Tf0Refusal):
        check_logical_entailment_vampire(premises, conclusion, tff=True, **_vampire)


def test_problem_needs_tff_is_a_signal_to_try_not_a_promise():
    assert problem_needs_tff([parse("∀x:Human Mortal(x)")], parse("Mortal(socrates)")) is True
    assert problem_needs_tff([parse("∀x:Human Mortal(x)")]) is True
    assert problem_needs_tff([parse("P(a)")]) is False
