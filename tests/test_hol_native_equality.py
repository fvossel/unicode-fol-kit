"""``native_equality`` on the classical HOL/THF exporters (`hol.classical`).

By default ``to_thf_fol`` / ``to_isabelle_fol`` emit ``=`` / ``≠`` as the
uninterpreted predicates ``feq`` / ``fneq`` (see the module docstring of
``hol.classical``) — nothing forces them to be reflexive, symmetric,
transitive, or to respect the congruence of any declared function/predicate.
``native_equality=True`` instead renders ``=`` / ``≠`` as the target format's
own built-in HOL identity (THF's infix ``=``/``!=``, Isabelle's polymorphic
``=``/``\\<noteq>``), for which all four properties are free — no axioms
needed, because genuine identity validates them definitionally.

Three independent lines of evidence for that claim, from weakest to strongest:

1. **Z3 differential** (below, always runs): the kit's OWN semantics already
   distinguish the two readings — ``Atom.to_z3`` treats ``=`` as Z3's native
   equality, so ``is_valid`` on a formula written with literal ``=`` measures
   exactly the "native identity" reading, while the SAME formula shape written
   with an arbitrary uninterpreted binary predicate measures exactly what the
   DEFAULT export's ``feq`` means semantically (an uninterpreted predicate is
   in no way privileged over any other). This is hand-checked reasoning, not
   circular: it does not consult ``hol.classical`` at all.
2. **Live Vampire via THF** (``test_vampire_*``): the actual exported THF text
   is fed to a real higher-order ATP.
3. **Live Isabelle** (``test_isabelle_*``, ``-m isabelle_live``): the actual
   exported theory is fed to a real Isabelle/HOL build.
"""

import re
import subprocess

import pytest

from unicode_fol_kit.fol.nodes import Atom, Variable, And, Implies
from unicode_fol_kit.hol.classical import to_thf_fol, to_isabelle_fol
from unicode_fol_kit.atp.z3_models import is_valid

x, y, z = Variable("x"), Variable("y"), Variable("z")
P = lambda t: Atom("P", [t])  # noqa: E731 - short local alias, used throughout

# The four formula SHAPES this module checks throughout, built once so the
# Z3/Vampire/Isabelle sections all exercise literally the same formulas.
CONGRUENCE = Implies(And(Atom("=", [x, y]), P(x)), P(y))     # x=y ∧ P(x) → P(y)
REFLEXIVITY = Atom("=", [x, x])                               # x=x
SYMMETRY = Implies(Atom("=", [x, y]), Atom("=", [y, x]))      # x=y → y=x
TRANSITIVITY = Implies(And(Atom("=", [x, y]), Atom("=", [y, z])), Atom("=", [x, z]))


def _as_uninterpreted(formula):
    """Rewrite every '=' atom in ``formula`` to the ordinary predicate 'R'.

    This is what the DEFAULT export's semantics amount to: 'feq'/'fneq' are
    literally just uninterpreted binary predicates, no different in meaning
    from any other symbol the user might have named 'R'. Only Atom nodes with
    predicate '=' are touched, and only by walking the (small, hand-built)
    formulas above, so this is a direct, obviously-correct substitution.
    """
    if isinstance(formula, Atom):
        if formula.predicate == "=":
            return Atom("R", formula.args)
        return formula
    if isinstance(formula, And):
        return And(_as_uninterpreted(formula.left), _as_uninterpreted(formula.right))
    if isinstance(formula, Implies):
        return Implies(_as_uninterpreted(formula.left), _as_uninterpreted(formula.right))
    raise TypeError(f"unsupported shape in this test helper: {type(formula).__name__}")


# ---------------------------------------------------------------------------
# (1) Z3 differential / soundness: hand-checked, no external prover needed.
#
# Each pair below is hand-verified: standard first-order model theory says an
# arbitrary binary relation need not be reflexive, symmetric, transitive, or
# congruent with an arbitrary unary predicate P — a countermodel for each is
# trivial to write down by hand (e.g. for symmetry, R = "<" on {0,1}: R(0,1)
# holds, R(1,0) does not). Z3's `is_valid` (via `Atom.to_z3`, independent of
# `hol.classical`) is the second, mechanised route confirming the same thing.
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("name,formula", [
    ("congruence", CONGRUENCE),
    ("reflexivity", REFLEXIVITY),
    ("symmetry", SYMMETRY),
    ("transitivity", TRANSITIVITY),
], ids=["congruence", "reflexivity", "symmetry", "transitivity"])
def test_native_identity_reading_is_valid(name, formula):
    # Under Z3's native '=' (the reading native_equality=True asks the target
    # format for), all four properties are tautologies.
    assert is_valid(formula) is True, name


@pytest.mark.parametrize("name,formula", [
    ("congruence", CONGRUENCE),
    ("reflexivity", REFLEXIVITY),
    ("symmetry", SYMMETRY),
    ("transitivity", TRANSITIVITY),
], ids=["congruence", "reflexivity", "symmetry", "transitivity"])
def test_uninterpreted_reading_is_not_valid(name, formula):
    # Under the DEFAULT export's reading (an ordinary uninterpreted binary
    # predicate — exactly what 'feq' is), none of the four hold in general.
    assert is_valid(_as_uninterpreted(formula)) is False, name


# ---------------------------------------------------------------------------
# (2) Live: Vampire (5.0.1, via WSL) reads the actual exported THF text.
# Same invocation convention as tests/test_ho_thf_names.py.
# ---------------------------------------------------------------------------

def _wsl_vampire_ok() -> bool:
    try:
        result = subprocess.run(["wsl.exe", "vampire", "--version"],
                                capture_output=True, text=True, timeout=20)
        return result.returncode == 0 and "Vampire" in result.stdout
    except Exception:  # noqa: BLE001 - any failure means "not available"
        return False


live_vampire = pytest.mark.skipif(not _wsl_vampire_ok(),
                                  reason="no Vampire reachable via 'wsl vampire'")


def _szs_status(problem: str, seconds: int) -> str:
    from unicode_fol_kit.atp.vampire_entailment import _spawn_vampire
    out, timed_out = _spawn_vampire(problem, "vampire", timeout=seconds + 15,
                                    use_wsl=True, extra_args=("-t", str(seconds)))
    assert "parse error" not in out and "User error" not in out, out[-2000:]
    match = re.search(r"SZS status (\w+)", out)
    if match:
        return match.group(1)
    return "TimedOut" if timed_out else "NoStatus"


@live_vampire
@pytest.mark.parametrize("formula", [CONGRUENCE, REFLEXIVITY, SYMMETRY, TRANSITIVITY],
                         ids=["congruence", "reflexivity", "symmetry", "transitivity"])
def test_vampire_proves_with_native_equality(formula):
    # native_equality=True: THF's own '=' — Vampire's built-in equality
    # reasoning (paramodulation) closes all four immediately.
    assert _szs_status(to_thf_fol(formula, native_equality=True), seconds=10) == "Theorem"


@live_vampire
@pytest.mark.parametrize("formula", [CONGRUENCE, REFLEXIVITY, SYMMETRY, TRANSITIVITY],
                         ids=["congruence", "reflexivity", "symmetry", "transitivity"])
def test_vampire_does_not_prove_with_default_uninterpreted_equality(formula):
    # Default: 'feq' is an ordinary uninterpreted predicate to Vampire too, so
    # none of these is a theorem — Vampire exhausts a short time budget
    # without reporting 'Theorem' (it neither proves nor is expected to).
    assert _szs_status(to_thf_fol(formula, native_equality=False), seconds=5) != "Theorem"


# ---------------------------------------------------------------------------
# (3) Live: Isabelle/HOL build (gated the same way as
# tests/test_hol_isabelle_nonmodal_live.py). Skipped unless a real Isabelle
# install is found (UFK_ISABELLE_HOME / ISABELLE_HOME / PATH / standard scan).
# ---------------------------------------------------------------------------

from unicode_fol_kit.hol.isabelle_runner import isabelle_available, check_theory  # noqa: E402

# Applied per-function (not as a module-level `pytestmark`) so only the
# Isabelle tests below are gated/marked — the Z3 and Vampire tests above run
# unconditionally.
_isabelle_live = pytest.mark.skipif(
    not isabelle_available(),
    reason="no Isabelle installation found (set UFK_ISABELLE_HOME / ISABELLE_HOME)")


def _build_ok(theory_text, theory_name):
    r = check_theory(theory_text, theory_name, session_timeout=90)
    assert r.ok, f"build failed (exit {r.exit_code}):\n{r.output[-1200:]}"


def _build_fails(theory_text, theory_name):
    r = check_theory(theory_text, theory_name, session_timeout=90)
    assert not r.ok, ("expected this build to FAIL (no axioms for an uninterpreted "
                      "predicate should not let congruence close) but it succeeded")


@pytest.mark.isabelle_live
@_isabelle_live
def test_isabelle_congruence_discharges_with_native_equality():
    # by auto: congruence needs more than a single simp step (rewriting under
    # the implication's antecedent), but is free once '=' is real HOL identity.
    theory = to_isabelle_fol(CONGRUENCE, theory_name="NativeEqCongruence",
                             proof="by auto", native_equality=True)
    _build_ok(theory, "NativeEqCongruence")


@pytest.mark.isabelle_live
@_isabelle_live
def test_isabelle_congruence_does_not_discharge_by_default():
    # Same tactic, same formula, default reading: 'feq' carries no congruence,
    # so 'by auto' cannot close it — this is the single most convincing proof
    # that the axiom-generator half of the original C21 proposal is
    # unnecessary: the difference between these two tests IS the axiom.
    theory = to_isabelle_fol(CONGRUENCE, theory_name="DefaultEqCongruence",
                             proof="by auto", native_equality=False)
    _build_fails(theory, "DefaultEqCongruence")


@pytest.mark.isabelle_live
@_isabelle_live
@pytest.mark.parametrize("name,formula", [
    ("Refl", REFLEXIVITY), ("Sym", SYMMETRY), ("Trans", TRANSITIVITY),
], ids=["reflexivity", "symmetry", "transitivity"])
def test_isabelle_reflexivity_symmetry_transitivity_discharge_with_native_equality(name, formula):
    theory = to_isabelle_fol(formula, theory_name=f"NativeEq{name}",
                             proof="by simp", native_equality=True)
    _build_ok(theory, f"NativeEq{name}")
