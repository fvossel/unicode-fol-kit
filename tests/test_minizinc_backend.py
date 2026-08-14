"""Tests for the MiniZinc/CP finite-domain backend (atp/minizinc_backend.py).

MiniZinc is **not installed** on this machine (see the module docstring of
``atp.minizinc_backend`` — deliberate, and not expected to change), so this
file follows the kit's established pattern for tool-absent integrations
(``tests/test_eprover_zipperposition.py``, ``tests/test_twee.py``): every
piece the module can control without a solver is exercised for real, and the
subprocess boundary alone is stubbed.

* **Renderer** (:func:`to_minizinc`) — every hand-derived formula below is
  built directly from :mod:`unicode_fol_kit.fol.nodes` (never parsed then
  eyeballed) and its rendered ``.mzn`` text is compared BYTE-FOR-BYTE against
  the checked-in fixtures under ``tests/fixtures/minizinc/`` — this both pins
  the encoder's output and, read the other way, doubles as a hand-check that
  the fixtures the wiring/differential tests rely on actually mean what their
  names claim.
* **Parser** (:func:`_parse_minizinc_solution` / :func:`_atoms_from_solution`)
  — exercised against the recorded ``sample_stdout_*.txt`` fixtures, which
  are themselves plain hand-written text (no live run produced them; the
  wire format is this module's own invention — see its docstring).
* **Discovery** (:func:`minizinc_available` / :func:`_minizinc_binary`) —
  ``$UFK_MINIZINC`` / ``PATH`` precedence, exercised entirely through
  ``monkeypatch`` (env var and ``shutil.which``), never assuming anything
  about this machine's actual PATH.
* **Subprocess plumbing** (:func:`_run_minizinc`) — argument construction and
  the ``subprocess.TimeoutExpired`` backstop, exercised with
  ``subprocess.run`` replaced by a recording fake.
* **``MinizincBackend.decide()``** — the ``BackendUnavailable`` guard (no
  binary reachable) is exercised for real (no patching of availability, per
  the task's own instruction not to "pretend"); the REST of ``decide()``'s
  per-size search/parse/reconstruct/verify pipeline is exercised offline by
  passing ``minizinc_path=`` (the documented discovery override) together
  with a monkeypatched :func:`~unicode_fol_kit.atp.minizinc_backend._run_minizinc`
  that inspects the generated ``.mzn`` text for ``int: n = <size>;`` to decide
  what to answer at each size — this is the SAME technique
  ``tests/test_eprover_zipperposition.py``'s ``fake_run`` fixture uses for a
  stubbed subprocess runner, adapted for a search that tries several sizes.
* **Live** end-to-end tests are ``@pytest.mark.skipif(not minizinc_available(),
  ...)`` and will not run here, per the module's own documentation that
  MiniZinc is absent and will stay absent in this environment.
"""

import pathlib
import re
import subprocess

import pytest

from unicode_fol_kit.atp import minizinc_backend as mb
from unicode_fol_kit.atp.finite_domain import (
    FiniteDomainProblem, fragment_check, verify_model,
)
from unicode_fol_kit.atp.minizinc_backend import (
    MinizincBackend, minizinc_available, to_minizinc,
)
from unicode_fol_kit.atp.protocol import (
    BackendUnavailable, ERROR, REFUTED, UNKNOWN,
)
from unicode_fol_kit.fol.nodes import (
    Atom, And, Box, Cardinality, Constant, Contrast, Count, Function, Iff,
    Implies, Node, Not, Number, Or, Quantifier, Variable, Xor,
)
from unicode_fol_kit.fol.signature import Signature
from unicode_fol_kit.semantics.structures import structure_from_dict

FIXDIR = pathlib.Path(__file__).parent / "fixtures" / "minizinc"


def _read_fixture(name: str) -> str:
    return (FIXDIR / name).read_text(encoding="utf-8")


# =============================================================================
# Identifier scheme (offline, hand-derived)
# =============================================================================

def test_mzn_pred_name_prefixes_with_p():
    assert mb._mzn_pred_name("Loves") == "p_Loves"


def test_mzn_func_name_prefixes_with_f():
    assert mb._mzn_func_name("f") == "f_f"


def test_mzn_var_name_prefixes_with_v():
    assert mb._mzn_var_name("x") == "v_x"


def test_mzn_const_name_ascii_passthrough_prefixed():
    assert mb._mzn_const_name("alice") == "k_alice"


def test_mzn_const_name_transliterates_non_ascii():
    # theta (Greek U+03B8) -> "theta" via constant_name_to_ascii, then prefixed.
    assert mb._mzn_const_name("θ") == "k_theta"


def test_mzn_const_name_ascii_and_greek_collide_before_prefixing():
    # The exact collision to_minizinc's own guard exists to catch (see
    # module docstring "Identifier scheme" section): a literal "theta" and
    # the Greek letter both fold to the SAME MiniZinc identifier. This
    # function itself does not check for the collision (no sibling
    # visibility) -- to_minizinc does, tested separately below.
    assert mb._mzn_const_name("theta") == mb._mzn_const_name("θ") == "k_theta"


# =============================================================================
# _number_int
# =============================================================================

def test_number_int_accepts_plain_int():
    assert mb._number_int(Number(3)) == 3


def test_number_int_accepts_zero_and_negative():
    # Number's own dataclass type is Union[int, float] with no non-negativity
    # constraint (unlike Count.n) -- a negative comparison bound is a
    # perfectly legal MiniZinc literal, just an odd one.
    assert mb._number_int(Number(0)) == 0
    assert mb._number_int(Number(-5)) == -5


def test_number_int_rejects_bool():
    # bool is an int subclass in Python; True/False silently read as 1/0
    # would be exactly the accidental-acceptance bug the kit's loud-refusal
    # convention exists to catch (see e.g. fol.signature._require_arity).
    with pytest.raises(NotImplementedError, match="not an integer"):
        mb._number_int(Number(True))


def test_number_int_rejects_float():
    with pytest.raises(NotImplementedError, match="not an integer"):
        mb._number_int(Number(1.5))


# =============================================================================
# to_minizinc -- top-level refusals
# =============================================================================

def test_to_minizinc_rejects_non_problem_type():
    with pytest.raises(TypeError, match="FiniteDomainProblem"):
        to_minizinc("not a problem")


def test_to_minizinc_rejects_fragment_check_failure():
    # Box has no finite-domain reading (see atp.finite_domain's "Fragment
    # boundary" section) -- fragment_check must refuse it before to_minizinc
    # tries to render anything.
    goal = Box(Atom("P", (Constant("a"),)))
    with pytest.raises(NotImplementedError, match="Box is not encodable"):
        to_minizinc(FiniteDomainProblem((goal,), 2))


def test_arithmetic_function_symbol_is_refused_by_the_gate():
    """``+`` is a Function node like any other, so the shared gate stops it
    for the same reason it stops ``f``: no structure can hold its
    interpretation. The renderer keeps its own arithmetic refusal as a second
    line of defence for a caller that builds a FiniteDomainProblem by hand and
    skips the gate, but that path is no longer reachable through decide()."""
    x = Variable("x")
    goal = Quantifier("forall", x, Atom("=", (Function("+", (x, x)), x)))

    assert fragment_check((goal,)) is not None
    with pytest.raises(NotImplementedError):
        to_minizinc(FiniteDomainProblem((goal,), 2))


def test_to_minizinc_rejects_non_integer_number_reachable_through_a_comparison():
    x = Variable("x")
    goal = Quantifier("exists", x, Atom("=", (x, Number(1.5))))
    with pytest.raises(NotImplementedError, match="not an integer"):
        to_minizinc(FiniteDomainProblem((goal,), 2))


def test_to_minizinc_rejects_undeclared_symbol_against_a_mismatched_signature():
    # A hand-built signature that never declares 'P' -- to_minizinc must
    # name exactly the offending symbol, not silently drop the sentence.
    goal = Atom("P", (Constant("a"),))
    mismatched_sig = Signature.from_formulas([Atom("Q", (Constant("a"),))])
    problem = FiniteDomainProblem((goal,), 2, signature=mismatched_sig)
    with pytest.raises(NotImplementedError, match="predicate 'P' is not declared"):
        to_minizinc(problem)


def test_to_minizinc_rejects_constant_name_collision():
    # 'theta' and Greek 'θ' both fold to k_theta (see the module docstring's
    # "Identifier scheme" section) -- refusing to silently merge two
    # distinct constants into one MiniZinc variable.
    goal = Atom("=", (Constant("theta"), Constant("θ")))
    with pytest.raises(NotImplementedError) as exc_info:
        to_minizinc(FiniteDomainProblem((goal,), 2))
    msg = str(exc_info.value)
    assert "'theta'" in msg and "'θ'" in msg and "k_theta" in msg


# =============================================================================
# to_minizinc -- golden fixture comparisons (byte-for-byte, hand-derived
# formulas -- see the module docstring for how each was reconstructed)
# =============================================================================

def test_render_forall_exists_matches_fixture():
    """∀x ∃y Loves(x,y), |D|=2: one binary predicate, one nested-quantifier
    constraint -- the simplest quantifier-nesting case."""
    x, y = Variable("x"), Variable("y")
    goal = Quantifier("forall", x, Quantifier("exists", y, Atom("Loves", (x, y))))
    rendered = to_minizinc(FiniteDomainProblem((goal,), 2))
    assert rendered == _read_fixture("forall_exists_loves_size2.mzn")


def test_render_refutation_goal_wraps_in_not():
    """The exact same formula, negated -- the shape decide() actually feeds
    to_minizinc when searching for a countermodel of the ORIGINAL formula
    (sentences = premises + (Not(formula),))."""
    x, y = Variable("x"), Variable("y")
    inner = Quantifier("forall", x, Quantifier("exists", y, Atom("Loves", (x, y))))
    goal = Not(inner)
    rendered = to_minizinc(FiniteDomainProblem((goal,), 2))
    assert rendered == _read_fixture("refutation_goal_not_loves_size2.mzn")


def test_render_counting_fragment_matches_fixture():
    """Count and a Cardinality-vs-Cardinality comparison, |D|=3 -- the exact
    fragment Z3/Prover9/TPTP reject (see the design note's §1) that this
    backend exists to decide."""
    x, v, w = Variable("x"), Variable("v"), Variable("w")
    count_sentence = Count("ge", Number(2), x, Atom("P", (x,)))
    card_cmp = Atom(">", (
        Cardinality(v, Atom("Q", (v,))),
        Cardinality(w, Atom("R", (w,))),
    ))
    problem = FiniteDomainProblem((count_sentence, card_cmp), 3)
    rendered = to_minizinc(problem)
    assert rendered == _read_fixture("counting_fragment_size3.mzn")


def test_render_connectives_and_alldifferent_matches_fixture():
    """All five two-place connectives plus all_different=True over two
    constants, |D|=3 -- pins alldifferent.mzn inclusion, the `!=` builtin
    comparison, and the connective operator table (xor/<->/->//\\//\\/) all
    at once."""
    a, b = Constant("a"), Constant("b")
    sentences = (
        Atom("≠", (a, b)),
        Xor(Atom("P", (a,)), Atom("Q", (a,))),
        Iff(Atom("P", (a,)), Atom("Q", (b,))),
        And(Atom("Rain", ()), Or(Atom("P", (a,)), Not(Atom("Q", (b,))))),
        Implies(Atom("Rain", ()), Atom("P", (a,))),
    )
    problem = FiniteDomainProblem(sentences, 3, all_different=True)
    rendered = to_minizinc(problem)
    assert rendered == _read_fixture("connectives_and_alldifferent_size3.mzn")


def test_functions_never_reach_the_renderer():
    """The renderer COULD encode a unary function as ``array[DOM] of var
    DOM`` — but it is never asked to. The shared gate refuses function
    symbols upstream, because ``FiniteStructure`` has no slot for a function
    interpretation and a model containing one could therefore never be
    checked back. An encoder that produced a model nobody can verify is worse
    than one that declines, so the refusal is the feature."""
    x = Variable("x")
    goal = Quantifier("exists", x, Atom("=", (Function("f", (x,)), x)))

    message = fragment_check((goal,))
    assert message is not None
    assert "Function" in message and "FiniteStructure" in message


def test_render_contrast_matches_fixture():
    """Contrast renders identically to And (truth-functional equivalence --
    see Contrast's own docstring in _fol_nodes.py)."""
    a, b = Constant("a"), Constant("b")
    goal = Contrast(Atom("P", (a,)), Atom("Q", (b,)))
    rendered = to_minizinc(FiniteDomainProblem((goal,), 2))
    assert rendered == _read_fixture("contrast_verification_gap_size2.mzn")


def test_to_minizinc_is_deterministic_across_calls():
    """Two calls on structurally-equal problems agree byte-for-byte -- the
    property the fixture comparisons above rely on to be meaningful at all
    (symbols are declared in SORTED name order, not dict-iteration order)."""
    a, b = Constant("b"), Constant("a")  # built out of alphabetical order
    sentences = (Atom("Q", (b,)), Atom("P", (a,)))
    problem = FiniteDomainProblem(sentences, 2)
    assert to_minizinc(problem) == to_minizinc(problem)


def test_to_minizinc_declares_predicates_in_sorted_order_not_construction_order():
    a = Constant("a")
    sentences = (Atom("Zed", (a,)), Atom("Alpha", (a,)))
    rendered = to_minizinc(FiniteDomainProblem(sentences, 2))
    assert rendered.index("p_Alpha") < rendered.index("p_Zed")


# =============================================================================
# _flatten_expr
# =============================================================================

def test_flatten_expr_arity_zero_is_bare_show():
    assert mb._flatten_expr("p_Rain", 0) == "show(p_Rain)"


def test_flatten_expr_arity_one():
    assert mb._flatten_expr("f_f", 1) == "show([f_f[i0] | i0 in DOM])"


def test_flatten_expr_arity_two_last_generator_fastest():
    assert (mb._flatten_expr("p_Loves", 2)
            == "show([p_Loves[i0, i1] | i0 in DOM, i1 in DOM])")


# =============================================================================
# _parse_mzn_value
# =============================================================================

@pytest.mark.parametrize("text, expected", [
    ("true", True),
    ("false", False),
    ("0", 0),
    ("42", 42),
    ("-3", -3),
    ("[]", []),
    ("[true, false, true]", [True, False, True]),
    ("[0, 1, 1]", [0, 1, 1]),
])
def test_parse_mzn_value_recognised_shapes(text, expected):
    assert mb._parse_mzn_value(text) == expected


def test_parse_mzn_value_rejects_unrecognised_text():
    with pytest.raises(ValueError, match="unrecognised"):
        mb._parse_mzn_value("bogus")


def test_parse_mzn_value_recurses_harmlessly_on_a_nested_bracket():
    # to_minizinc never actually EMITS a nested bracket (every array is
    # flattened to one dimension before show() sees it -- see the module
    # docstring's "Output" section), so this input never arises from this
    # module's own renderer. But the comma-split-then-recurse implementation
    # has no explicit depth guard, so it is worth hand-deriving what it
    # ACTUALLY does rather than assuming a raise: "[[true]]" strips to inner
    # "[true]" (one comma-separated part, itself still bracketed), which
    # recurses to "true" -> True, giving [[True]] -- a harmlessly-nested
    # list, not a ValueError. Pinned as documented behaviour of dead code,
    # not a defect: nothing in this module's Raises contract promises a
    # rejection here.
    assert mb._parse_mzn_value("[[true]]") == [[True]]


# =============================================================================
# _parse_minizinc_solution -- against the recorded stdout fixtures
# =============================================================================

def test_parse_solution_sat_loves_fixture():
    text = _read_fixture("sample_stdout_sat_loves.txt")
    solution = mb._parse_minizinc_solution(text)
    assert solution == {"p_Loves": [True, False, False, False], "k_a": 0}


def test_parse_solution_sat_connectives_fixture():
    text = _read_fixture("sample_stdout_sat_connectives.txt")
    solution = mb._parse_minizinc_solution(text)
    assert solution == {
        "p_P": [True, False, False],
        "p_Q": [False, True, False],
        "p_Rain": True,
        "k_a": 0,
        "k_b": 1,
    }


def test_parse_solution_sat_function_gap_fixture():
    text = _read_fixture("sample_stdout_sat_function_gap.txt")
    assert mb._parse_minizinc_solution(text) == {"f_f": [0, 1]}


def test_parse_solution_unsat_fixture_returns_none():
    # No UFK-SOLUTION-BEGIN/END sentinel pair -- the caller's signal that
    # minizinc never reached the output item at all.
    assert mb._parse_minizinc_solution(_read_fixture("sample_stdout_unsat.txt")) is None


def test_parse_solution_unknown_timelimit_fixture_returns_none():
    assert mb._parse_minizinc_solution(
        _read_fixture("sample_stdout_unknown_timelimit.txt")) is None


def test_parse_solution_returns_none_for_arbitrary_text():
    assert mb._parse_minizinc_solution("nothing relevant here\n") is None


# =============================================================================
# _atoms_from_solution -- happy path (against the same fixtures, paired with
# hand-built signatures) and error paths (hand-derived malformed inputs)
# =============================================================================

def test_atoms_from_solution_loves_extracts_true_atom_only():
    solution = mb._parse_minizinc_solution(_read_fixture("sample_stdout_sat_loves.txt"))
    sig = Signature.from_formulas([Atom("Loves", (Variable("x"), Variable("y")))])
    atoms = mb._atoms_from_solution(sig, solution, 2)
    # [true, false, false, false] over DOM x DOM = (0,0),(0,1),(1,0),(1,1):
    # only index 0 (the (0,0) tuple) is true.
    assert atoms == [("Loves", (0, 0))]


def test_atoms_from_solution_connectives_extracts_predicates_and_constants():
    solution = mb._parse_minizinc_solution(_read_fixture("sample_stdout_sat_connectives.txt"))
    a, b = Constant("a"), Constant("b")
    sig = Signature.from_formulas([
        Atom("P", (Variable("x"),)), Atom("Q", (Variable("x"),)), Atom("Rain", ()),
        Atom("=", (a, b)),
    ])
    atoms = mb._atoms_from_solution(sig, solution, 3)
    assert sorted(atoms) == [
        ("P", (0,)), ("Q", (1,)), ("Rain", ()), ("a", (0,)), ("b", (1,)),
    ]


def test_atoms_from_solution_function_produces_k_plus_1_tuples():
    solution = mb._parse_minizinc_solution(_read_fixture("sample_stdout_sat_function_gap.txt"))
    x = Variable("x")
    sig = Signature.from_formulas([Atom("=", (Function("f", (x,)), x))])
    atoms = mb._atoms_from_solution(sig, solution, 2)
    # f_f = [0, 1]: f(0)=0, f(1)=1 -- the total-relation (input..., result)
    # shape structure_from_solution requires.
    assert sorted(atoms) == [("f", (0, 0)), ("f", (1, 1))]


def test_atoms_from_solution_missing_declared_symbol_raises():
    sig = Signature.from_formulas([Atom("P", (Variable("x"),))])
    with pytest.raises(ValueError, match="missing 'p_P'"):
        mb._atoms_from_solution(sig, {}, 2)


def test_atoms_from_solution_scalar_where_list_expected_raises():
    sig = Signature.from_formulas([Atom("P", (Variable("x"),))])
    with pytest.raises(ValueError, match="expects a flat list"):
        mb._atoms_from_solution(sig, {"p_P": True}, 2)


def test_atoms_from_solution_wrong_list_length_raises():
    sig = Signature.from_formulas([Atom("P", (Variable("x"),))])
    with pytest.raises(ValueError, match="expects 2 entries"):
        mb._atoms_from_solution(sig, {"p_P": [True]}, 2)


def test_atoms_from_solution_constant_bool_where_int_expected_raises():
    # isinstance(True, int) is True in Python -- the explicit bool exclusion
    # this function's own docstring calls out must actually be enforced.
    sig = Signature.from_formulas([Atom("P", (Constant("a"),))])
    with pytest.raises(ValueError, match="constant 'a' expects an int"):
        mb._atoms_from_solution(sig, {"p_P": [True, False], "k_a": True}, 2)


def test_atoms_from_solution_function_arity_zero_scalar_where_list_given_raises():
    x = Variable("x")
    sig = Signature.from_formulas([Atom("=", (Function("f", (x,)), x))])
    with pytest.raises(ValueError, match="function 'f' \\(arity 1\\) expects a flat list"):
        mb._atoms_from_solution(sig, {"f_f": True}, 2)


# =============================================================================
# _run_minizinc -- subprocess plumbing (subprocess.run replaced by a
# recording fake; nothing here spawns a real process)
# =============================================================================

class _FakeCompletedProcess:
    def __init__(self, stdout, stderr):
        self.stdout = stdout
        self.stderr = stderr


def test_run_minizinc_builds_expected_cli_args(monkeypatch):
    captured = {}

    def fake_run(args, capture_output, text, timeout):
        captured["args"] = args
        captured["timeout"] = timeout
        return _FakeCompletedProcess("some stdout", "some stderr")

    monkeypatch.setattr(mb.subprocess, "run", fake_run)
    stdout, stderr, timed_out = mb._run_minizinc("model.mzn", "minizinc", "gecode", 5000)

    assert captured["args"] == [
        "minizinc", "--solver", "gecode", "--time-limit", "5000", "model.mzn",
    ]
    # (5000 ms / 1000) + 10s backstop, per the function's own docstring.
    assert captured["timeout"] == pytest.approx(15.0)
    assert (stdout, stderr, timed_out) == ("some stdout", "some stderr", False)


def test_run_minizinc_normalises_none_stdout_stderr_to_empty_string(monkeypatch):
    monkeypatch.setattr(
        mb.subprocess, "run",
        lambda *a, **k: _FakeCompletedProcess(None, None))
    stdout, stderr, timed_out = mb._run_minizinc("model.mzn", "minizinc", "gecode", 1000)
    assert (stdout, stderr, timed_out) == ("", "", False)


def test_run_minizinc_reports_timed_out_on_subprocess_timeout(monkeypatch):
    def fake_run(*a, **k):
        raise subprocess.TimeoutExpired(cmd="minizinc", timeout=1)

    monkeypatch.setattr(mb.subprocess, "run", fake_run)
    stdout, stderr, timed_out = mb._run_minizinc("model.mzn", "minizinc", "gecode", 1000)
    assert (stdout, stderr, timed_out) == ("", "", True)


# =============================================================================
# Discovery -- $UFK_MINIZINC / PATH precedence, entirely via monkeypatch
# =============================================================================

def test_minizinc_binary_prefers_env_var_over_path(monkeypatch):
    monkeypatch.setenv("UFK_MINIZINC", "/opt/custom/minizinc")
    monkeypatch.setattr(mb.shutil, "which", lambda name: "/usr/bin/minizinc")
    assert mb._minizinc_binary() == "/opt/custom/minizinc"


def test_minizinc_binary_falls_back_to_path_when_env_unset(monkeypatch):
    monkeypatch.delenv("UFK_MINIZINC", raising=False)
    monkeypatch.setattr(mb.shutil, "which",
                        lambda name: "/usr/bin/minizinc" if name == "minizinc" else None)
    assert mb._minizinc_binary() == "/usr/bin/minizinc"


def test_minizinc_binary_none_when_neither_reachable(monkeypatch):
    monkeypatch.delenv("UFK_MINIZINC", raising=False)
    monkeypatch.setattr(mb.shutil, "which", lambda name: None)
    assert mb._minizinc_binary() is None


def test_minizinc_available_reflects_binary_discovery(monkeypatch):
    monkeypatch.delenv("UFK_MINIZINC", raising=False)
    monkeypatch.setattr(mb.shutil, "which", lambda name: None)
    assert minizinc_available() is False

    monkeypatch.setenv("UFK_MINIZINC", "/some/path/minizinc")
    assert minizinc_available() is True


def test_minizinc_binary_reads_env_fresh_every_call(monkeypatch):
    # Not cached -- repointing the env var mid-process takes effect
    # immediately (mirrors Prover9Backend/VampireBackend's own discovery;
    # see the function's own docstring).
    monkeypatch.delenv("UFK_MINIZINC", raising=False)
    monkeypatch.setattr(mb.shutil, "which", lambda name: None)
    assert mb._minizinc_binary() is None
    monkeypatch.setenv("UFK_MINIZINC", "/now/it/exists")
    assert mb._minizinc_binary() == "/now/it/exists"


# =============================================================================
# MinizincBackend -- class-level contract
# =============================================================================

def test_backend_name_logics_external():
    backend = MinizincBackend()
    assert backend.name == "minizinc"
    assert backend.logics == frozenset({"fol"})
    assert backend.external is True


def test_backend_available_delegates_to_minizinc_available(monkeypatch):
    monkeypatch.delenv("UFK_MINIZINC", raising=False)
    monkeypatch.setattr(mb.shutil, "which", lambda name: None)
    assert MinizincBackend().available() is False
    monkeypatch.setenv("UFK_MINIZINC", "/some/path/minizinc")
    assert MinizincBackend().available() is True


# =============================================================================
# decide() -- BackendUnavailable when no binary is reachable (exercised for
# REAL, per the task's instruction not to pretend availability here)
# =============================================================================

def test_decide_raises_backend_unavailable_when_no_binary_reachable(monkeypatch):
    monkeypatch.delenv("UFK_MINIZINC", raising=False)
    monkeypatch.setattr(mb.shutil, "which", lambda name: None)
    backend = MinizincBackend()
    with pytest.raises(BackendUnavailable, match="UFK_MINIZINC"):
        backend.decide(Atom("P", (Constant("a"),)), [])


def test_decide_minizinc_path_option_bypasses_discovery(monkeypatch):
    # minizinc_path= is the documented override (see decide()'s own
    # docstring) -- passing it must skip _minizinc_binary() discovery
    # entirely, even when no binary is reachable via env/PATH.
    monkeypatch.delenv("UFK_MINIZINC", raising=False)
    monkeypatch.setattr(mb.shutil, "which", lambda name: None)
    monkeypatch.setattr(mb, "_run_minizinc",
                        lambda *a, **k: ("=====UNSATISFIABLE=====\n", "", False))
    backend = MinizincBackend()
    v = backend.decide(Atom("P", (Constant("a"),)), [], max_size=1,
                       minizinc_path="/definitely/not/on/path/minizinc")
    assert v.status == UNKNOWN
    assert v.reason == "bound_hit"


# =============================================================================
# decide() -- the rest of the pipeline, offline, via minizinc_path= plus a
# monkeypatched _run_minizinc that answers per-size by reading the
# generated model's own "int: n = <size>;" line (see module docstring).
# =============================================================================

def _size_of(model_path: str) -> int:
    text = pathlib.Path(model_path).read_text(encoding="utf-8")
    match = re.search(r"int: n = (\d+);", text)
    assert match is not None, "generated .mzn is missing its own 'int: n = ...;' line"
    return int(match.group(1))


def _fake_run_at_size(target_size: int, stdout_at_target: str,
                      stdout_below: str = "=====UNSATISFIABLE=====\n"):
    """A stand-in for :func:`~unicode_fol_kit.atp.minizinc_backend._run_minizinc`
    that answers UNSAT below ``target_size`` and ``stdout_at_target`` exactly
    at it -- so ``decide()``'s size-1..max_size loop genuinely walks through
    the smaller, unsatisfiable sizes before reaching the one under test,
    exactly as a real solver run would (rather than returning the SAME
    canned answer at every size, which would silently mask a bug in the
    loop's own size bookkeeping)."""
    def fake_run(model_path, binary, solver, time_limit_ms):
        if _size_of(model_path) == target_size:
            return stdout_at_target, "", False
        return stdout_below, "", False
    return fake_run


def _loves_formula() -> Node:
    x, y = Variable("x"), Variable("y")
    return Quantifier("forall", x, Quantifier("exists", y, Atom("Loves", (x, y))))


def test_decide_refuted_at_the_correct_size_with_verified_countermodel(monkeypatch):
    """A genuine end-to-end pass: size 1 answers UNSAT, size 2 answers the
    recorded sat_loves fixture, and the reconstructed structure must
    independently verify against ¬∀x∃y Loves(x,y) (the actual sentence
    searched, per decide()'s own premises+(Not(formula),) convention)."""
    monkeypatch.setattr(
        mb, "_run_minizinc",
        _fake_run_at_size(2, _read_fixture("sample_stdout_sat_loves.txt")))
    backend = MinizincBackend()
    v = backend.decide(_loves_formula(), [], max_size=2, minizinc_path="FAKE")
    assert v.status == REFUTED
    assert v.reason is None
    assert v.countermodel["kind"] == "finite_structure"

    # Round-trips through structure_from_dict, and independently re-verifies
    # against the exact goal decide() searched -- not just trusting the
    # backend's own say-so.
    structure = structure_from_dict(v.countermodel["data"])
    assert structure.domain == ("0", "1")
    assert structure.extensions[("Loves", 2)] == frozenset({("0", "0")})
    assert verify_model(structure, (Not(_loves_formula()),)) is None


def test_decide_bound_hit_when_unsat_at_every_size(monkeypatch):
    monkeypatch.setattr(
        mb, "_run_minizinc", lambda *a, **k: ("=====UNSATISFIABLE=====\n", "", False))
    backend = MinizincBackend()
    v = backend.decide(_loves_formula(), [], max_size=2, minizinc_path="FAKE")
    assert v.status == UNKNOWN
    assert v.reason == "bound_hit"


def test_decide_timeout_when_minizincs_own_time_limit_expires(monkeypatch):
    # =====UNKNOWN===== is MiniZinc's OWN --time-limit expiring mid-search --
    # deliberately mapped to reason="timeout", NOT "bound_hit" (see the
    # class docstring: only bound_hit means every size up to max_size was
    # actually covered).
    monkeypatch.setattr(
        mb, "_run_minizinc", lambda *a, **k: ("=====UNKNOWN=====\n", "", False))
    backend = MinizincBackend()
    v = backend.decide(_loves_formula(), [], max_size=2, minizinc_path="FAKE")
    assert v.status == UNKNOWN
    assert v.reason == "timeout"


def test_decide_timeout_when_subprocess_itself_times_out(monkeypatch):
    monkeypatch.setattr(mb, "_run_minizinc", lambda *a, **k: ("", "", True))
    backend = MinizincBackend()
    v = backend.decide(_loves_formula(), [], max_size=2, minizinc_path="FAKE")
    assert v.status == UNKNOWN
    assert v.reason == "timeout"


def test_decide_infra_when_no_recognised_status_or_solution(monkeypatch):
    monkeypatch.setattr(mb, "_run_minizinc", lambda *a, **k: ("garbage output\n", "", False))
    backend = MinizincBackend()
    v = backend.decide(_loves_formula(), [], max_size=2, minizinc_path="FAKE")
    assert v.status == ERROR
    assert v.reason == "infra"


def test_decide_infra_when_verify_model_cannot_confirm_a_function_bearing_solution(monkeypatch):
    """A Function-bearing sentence is refused BEFORE the solver runs, and the
    refusal is `unsupported` rather than a late `infra` error.

    The distinction matters to a caller: `unsupported` says "this fragment is
    outside the backend" and is stable across machines, while `infra` says
    "something went wrong here and now" and invites a retry. Nothing about a
    function symbol will ever succeed on a retry, so reporting it as infra
    would be misleading."""
    x = Variable("x")
    func_goal = Quantifier("exists", x, Atom("=", (Function("f", (x,)), x)))
    monkeypatch.setattr(
        mb, "_run_minizinc",
        _fake_run_at_size(2, _read_fixture("sample_stdout_sat_function_gap.txt")))
    backend = MinizincBackend()
    # formula = Not(func_goal) so the searched sentence Not(formula) contains
    # the Function occurrence (a double negation -- irrelevant to the gap,
    # which is about the Function node, not the negation depth).
    v = backend.decide(Not(func_goal), [], max_size=2, minizinc_path="FAKE")
    assert v.status == UNKNOWN
    assert v.reason == "unsupported"
    assert "Function" in v.detail


def test_decide_infra_when_all_different_is_violated_by_the_solution(monkeypatch):
    """all_different=True is forwarded all the way to structure_from_solution
    (see FiniteDomainProblem.all_different) -- a solver that (per this test's
    fake) returns two constants denoting the SAME individual despite the
    flag is a solver/encoding bug, and must surface as ERROR/infra, not a
    silently-wrong REFUTED."""
    goal = Atom("=", (Constant("a"), Constant("b")))
    bad_stdout = (
        "UFK-SOLUTION-BEGIN\nUFK k_a 0 0\nUFK k_b 0 0\nUFK-SOLUTION-END\n----------\n"
    )
    monkeypatch.setattr(mb, "_run_minizinc", _fake_run_at_size(2, bad_stdout))
    backend = MinizincBackend()
    v = backend.decide(Not(goal), [], max_size=2, minizinc_path="FAKE", all_different=True)
    assert v.status == ERROR
    assert v.reason == "infra"
    assert "all_different" in v.detail


def test_decide_unsupported_short_circuits_before_any_run_call(monkeypatch):
    """to_minizinc's NotImplementedError depends only on `sentences`, never
    on `size` -- decide() must return UNKNOWN/unsupported on the FIRST size
    without ever calling _run_minizinc (asserted here by making a call an
    error)."""
    def _must_not_be_called(*a, **k):
        raise AssertionError("decide() should not have invoked _run_minizinc")
    monkeypatch.setattr(mb, "_run_minizinc", _must_not_be_called)

    x = Variable("x")
    plus_goal = Quantifier("forall", x, Atom("=", (Function("+", (x, x)), x)))
    backend = MinizincBackend()
    v = backend.decide(plus_goal, [], max_size=3, minizinc_path="FAKE")
    assert v.status == UNKNOWN
    assert v.reason == "unsupported"


def test_decide_unsupported_when_premises_and_formula_conflict_in_arity(monkeypatch):
    """Signature.from_formulas itself can raise (a symbol used at two
    different arities across premises+formula) -- decide() must catch that
    and report unsupported, not propagate."""
    premise = Atom("P", (Constant("a"), Constant("b")))    # P/2
    goal = Atom("P", (Constant("a"),))                      # P/1 -- conflict
    backend = MinizincBackend()
    v = backend.decide(goal, [premise], minizinc_path="FAKE")
    assert v.status == UNKNOWN
    assert v.reason == "unsupported"
    assert "conflicting arities" in v.detail


def test_decide_reports_countermodel_size_and_solver_in_detail(monkeypatch):
    monkeypatch.setattr(
        mb, "_run_minizinc",
        _fake_run_at_size(2, _read_fixture("sample_stdout_sat_loves.txt")))
    backend = MinizincBackend()
    v = backend.decide(_loves_formula(), [], max_size=2, minizinc_path="FAKE", solver="chuffed")
    assert v.status == REFUTED
    assert "size 2" in v.detail
    assert "chuffed" in v.detail


def test_decide_passes_the_requested_solver_to_run_minizinc(monkeypatch):
    captured = {}

    def fake_run(model_path, binary, solver, time_limit_ms):
        captured["solver"] = solver
        return "=====UNSATISFIABLE=====\n", "", False

    monkeypatch.setattr(mb, "_run_minizinc", fake_run)
    backend = MinizincBackend()
    backend.decide(_loves_formula(), [], max_size=1, minizinc_path="FAKE", solver="chuffed")
    assert captured["solver"] == "chuffed"


# =============================================================================
# Live -- only when a real minizinc binary is actually reachable. Per the
# module's own docstring, MiniZinc is not installed in this environment and
# is not expected to become so; this block documents the intended coverage
# and will simply be skipped here.
# =============================================================================

_MINIZINC_AVAILABLE = minizinc_available()


@pytest.mark.skipif(not _MINIZINC_AVAILABLE, reason="no minizinc binary reachable")
def test_live_refuted_forall_exists_loves_not_valid():
    backend = MinizincBackend()
    v = backend.decide(_loves_formula(), [], max_size=3, timeout=30000)
    assert v.status == REFUTED


@pytest.mark.skipif(not _MINIZINC_AVAILABLE, reason="no minizinc binary reachable")
def test_live_bound_hit_for_a_valid_syllogism():
    # ∀x(H(x)->M(x)), H(a) ⊨ M(a) is genuinely valid -- no countermodel
    # exists at ANY size, so an honest search must report bound_hit, NEVER
    # "proved" (the ONE RULE this whole backend exists to respect).
    x = Variable("x")
    a = Constant("a")
    premises = [
        Quantifier("forall", x, Implies(Atom("H", (x,)), Atom("M", (x,)))),
        Atom("H", (a,)),
    ]
    goal = Atom("M", (a,))
    backend = MinizincBackend()
    v = backend.decide(goal, premises, max_size=3, timeout=30000)
    assert v.status == UNKNOWN
    assert v.reason == "bound_hit"
