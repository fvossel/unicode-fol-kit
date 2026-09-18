"""THF names emitted by the third-order exporters (hol.thirdorder, hol.ho_modal).

TPTP reads a token with an upper-case initial as a VARIABLE, so a constant and
the name of an annotated formula have to be lower words. The exporters used to
write the kit's predicate names through verbatim — ``thf(G_type, type, ( G :
$i > $o ))`` — which no THF parser accepts. The offline tests pin the lexical
shape and the collision handling; where Vampire (which reads THF) is reachable
through WSL, the live tests check that the problems parse and that classical
third-order goals come out right.
"""

import re
import subprocess

import pytest

from unicode_fol_kit import MSFLParser
from unicode_fol_kit.atp.vampire_entailment import _spawn_vampire
from unicode_fol_kit.hol import goedel
from unicode_fol_kit.hol.ho_modal import HoAxiom, to_thf_ho_modal
from unicode_fol_kit.hol.thirdorder import to_thf_to

TO = MSFLParser(third_order=True)
TOM = MSFLParser(third_order=True, modal=True)

_DECLARATION = re.compile(r"^thf\(([^,]+), type, \( (\S+) : (.*) \)\)\.$")
_UNIT = re.compile(r"^thf\(([^,]+),")
_LOWER_WORD = re.compile(r"^[a-z][A-Za-z0-9_]*$")


def _declarations(problem):
    """``{constant: type}`` for every type declaration of a constant."""
    found = {}
    for line in problem.splitlines():
        match = _DECLARATION.match(line)
        if match and match.group(3) != "$tType":
            assert match.group(2) not in found, f"{match.group(2)} declared twice"
            found[match.group(2)] = match.group(3)
    return found


def _units(problem):
    return [m.group(1) for m in map(_UNIT.match, problem.splitlines()) if m]


def _assert_lexically_valid(problem):
    units = _units(problem)
    assert len(units) == len(set(units)), units
    for unit in units:
        assert _LOWER_WORD.match(unit), unit
    for constant in _declarations(problem):
        assert _LOWER_WORD.match(constant), constant


# ---------------------------------------------------------------------------
# Offline: lexical shape and collisions.
# ---------------------------------------------------------------------------

def test_classical_export_spells_predicates_as_lower_words():
    problem = to_thf_to(TO.parse("∀x (G(x) ↔ ∀P (Pos(P) → P(x)))"),
                        assumptions=[TO.parse("Pos(G)")])
    _assert_lexically_valid(problem)
    assert _declarations(problem) == {"g": "$i > $o", "pos": "( $i > $o ) > $o"}
    assert "( pos @ g )" in problem


def test_modal_export_of_goedels_axioms_is_lexically_valid():
    # Axiom names such as "A1" and "D2" are not lower words either.
    axioms = [HoAxiom(name, formula) for name, formula in goedel.axioms("scott").items()]
    problem = to_thf_ho_modal(goedel.conclusions()["T3"], frame="S5", axioms=axioms)
    _assert_lexically_valid(problem)
    units = _units(problem)
    assert {"a1", "d1", "a5"} <= set(units)
    # NE keeps its case after the initial: "nE" is a lower word.
    assert {"g", "pos", "ess", "nE"} <= set(_declarations(problem))


def test_symbols_that_share_a_stem_get_distinct_constants():
    # The predicate Pos and the individual pos both reduce to "pos"; THF has one
    # namespace, so they must not become one constant at two types.
    problem = to_thf_to(TO.parse("Pos(G) ∧ Q(pos)"))
    declared = _declarations(problem)
    assert declared["pos"] == "( $i > $o ) > $o"
    assert declared["pos_2"] == "$i"
    assert "( q @ pos_2 )" in problem


def test_a_user_symbol_cannot_take_an_embedding_functor():
    # R and r would both land on the accessibility relation r, Mu and mu on the
    # world type mu.
    problem = to_thf_ho_modal(TOM.parse("R(r) ∧ Mu(mu)"), frame="K")
    declared = _declarations(problem)
    assert declared["r"] == "mu > mu > $o"
    assert declared["r_2"] == "$i > mu > $o"
    assert declared["r_3"] == "$i"
    assert declared["mu_2"] == "$i > mu > $o"
    assert declared["mu_3"] == "$i"
    assert "( r_2 @ r_3 )" in problem and "( mu_2 @ mu_3 )" in problem


def test_an_axiom_named_goal_does_not_clash_with_the_conjecture():
    problem = to_thf_ho_modal(TOM.parse("∃x G(x)"), axioms=[HoAxiom("goal", TOM.parse("G(a)"))])
    _assert_lexically_valid(problem)
    assert "thf(goal, axiom, " in problem
    assert "thf(goal_2, conjecture, " in problem


def test_the_modal_export_declares_its_comparison_relations():
    problem = to_thf_ho_modal(TOM.parse("∀x ∀y (x = y → □(x = y))"))
    assert _declarations(problem)["feq"] == "$i > $i > mu > $o"


# ---------------------------------------------------------------------------
# Live: Vampire reads THF.
# ---------------------------------------------------------------------------

def _wsl_vampire_ok() -> bool:
    try:
        result = subprocess.run(["wsl.exe", "vampire", "--version"],
                                capture_output=True, text=True, timeout=20)
        return result.returncode == 0 and "Vampire" in result.stdout
    except Exception:  # noqa: BLE001 - any failure means "not available"
        return False


live = pytest.mark.skipif(not _wsl_vampire_ok(), reason="no Vampire reachable via 'wsl vampire'")


def _szs_status(problem: str, seconds: int = 20) -> str:
    out, _timed_out = _spawn_vampire(problem, "vampire", timeout=seconds + 30,
                                     use_wsl=True, extra_args=("-t", str(seconds)))
    assert "parse error" not in out and "User error" not in out, out[-2000:]
    match = re.search(r"SZS status (\w+)", out)
    return match.group(1) if match else "none"


@live
def test_vampire_proves_a_classical_third_order_goal():
    # Pos(G) → ∃P Pos(P): the witness is G itself.
    assert _szs_status(to_thf_to(TO.parse("Pos(G) → ∃P Pos(P)"))) == "Theorem"


@live
def test_vampire_does_not_prove_a_classical_non_theorem():
    # Pos(G) → Pos(H) fails in a model where Pos holds of G's extension only.
    assert _szs_status(to_thf_to(TO.parse("Pos(G) → Pos(H)")), seconds=10) != "Theorem"


@live
@pytest.mark.parametrize("source, frame", [
    ("∀x (□G(x) → G(x))", "S5"),
    ("Pos(G) ∧ Q(pos) ∧ R(r) ∧ Mu(mu)", "K"),
    ("∀x ∀y (x = y → □(x = y))", "GL"),
])
def test_vampire_parses_the_modal_export(source, frame):
    # Parsing only: this Vampire build does not close goals through the
    # definitional modal embedding within a test budget (it times out even on
    # the T axiom over S5), so the embedding's meaning stays covered by the
    # Isabelle route. What this pins is the part the old export got wrong.
    _szs_status(to_thf_ho_modal(TOM.parse(source), frame=frame), seconds=5)


@live
def test_vampire_parses_goedels_argument():
    axioms = [HoAxiom(name, formula) for name, formula in goedel.axioms("scott").items()]
    problem = to_thf_ho_modal(goedel.conclusions()["T3"], frame="S5", axioms=axioms)
    _szs_status(problem, seconds=5)
