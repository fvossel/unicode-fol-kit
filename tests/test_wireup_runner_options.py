"""The Isabelle runner must forward the WHOLE logic selection to every theory.

``isabelle_decide_counterfactual`` and ``isabelle_decide_modal`` each build more than
one theory: a prove theory (whose battery has to see through the premises / have the
axiom names in its ``using`` list) and a nitpick theory. The two steps decide OPPOSITE
questions, so an option that reached only one of them would answer about a logic nobody
asked for:

- reaching only the prove step  -> the refutation is searched in the wrong class, and a
  nitpick "genuine" counter-model outside the requested class is a **false INVALID**;
- reaching only the refute step -> the battery cannot discharge the goal, which degrades
  to UNKNOWN (harmless but useless).

Isabelle itself is not needed to test this, and these tests deliberately do NOT need it:
what is under test is the *emission wiring*, so ``check_theory`` is replaced by a capture
that records every theory text the decision would have built. (The end-to-end verdicts
are covered by the ``isabelle_live`` suites.)

The second half pins the export registry — the new public names have to be reachable
from the packages that own them, and the three routes' bridge-name lists have to stay
identical, since the option value is a bare string the user copies between routes.
"""

import re
from pathlib import Path

import pytest

from unicode_fol_kit.fol.nodes import (
    And, Atom, Believes, Box, Diamond, Implies, Knows, Obligatory, Would,
)
from unicode_fol_kit.hol import isabelle_runner as R

P, Q = Atom("P", ()), Atom("Q", ())

#: ``(P ∧ (P □→ Q)) → Q`` — modus ponens for the counterfactual: the schema the
#: centering default exists for (invalid in Lewis V, valid in VW and VC). Built from
#: the AST classes rather than from the glyphs, to keep the file encoding-agnostic.
CF_MODUS_PONENS = Implies(And(P, Would(P, Q)), Q)


class _FakeInstall:
    """Stands in for an IsabelleInstall; never dereferenced by the capture."""


@pytest.fixture
def captured(monkeypatch):
    """Replace ``check_theory`` with a capture; every build "fails", so the decision
    always runs BOTH steps and we see every theory it would have emitted."""
    seen = []

    def fake_check_theory(theory_text, theory_name, **kwargs):
        seen.append(theory_text)
        return R.BuildResult(ok=False, exit_code=1, output="", session="s",
                             theory_name=theory_name, elapsed=0.0)

    monkeypatch.setattr(R, "check_theory", fake_check_theory)
    monkeypatch.setattr(R, "find_isabelle", lambda *a, **k: _FakeInstall())
    return seen


# --------------------------------------------------------------------------- #
# isabelle_decide_counterfactual: centering reaches all three emission sites.
# --------------------------------------------------------------------------- #

_PREMISE = {"none": None, "weak": "weakly_centered Sel", "strong": "strongly_centered Sel"}
_UNFOLD = {"none": None, "weak": "weakly_centered_def", "strong": "strongly_centered_def"}


@pytest.mark.parametrize("level", ["none", "weak", "strong"])
def test_counterfactual_centering_premise_in_both_theories(captured, level):
    R.isabelle_decide_counterfactual(CF_MODUS_PONENS, centering=level)
    assert len(captured) == 2, "prove theory + nitpick theory"
    for text in captured:
        assert f"centering = {level}" in text          # the provenance line
        for other, premise in _PREMISE.items():
            if premise is None:
                continue
            assert (premise in text) is (other == level), (other, level)


@pytest.mark.parametrize("level", ["none", "weak", "strong"])
def test_counterfactual_battery_unfolds_the_level_it_assumed(captured, level):
    R.isabelle_decide_counterfactual(CF_MODUS_PONENS, centering=level)
    prove_theory = captured[0]
    line = next(ln for ln in prove_theory.splitlines()
                if ln.strip().startswith("unfolding"))
    for other, definition in _UNFOLD.items():
        if definition is None:
            continue
        assert (definition in line) is (other == level), (other, level, line)


def test_counterfactual_default_is_weak(captured):
    R.isabelle_decide_counterfactual(CF_MODUS_PONENS)
    assert all("weakly_centered Sel" in t for t in captured)


def test_counterfactual_custom_methods_still_get_the_level(captured):
    """A caller-supplied battery must not silently lose the unfold list."""
    R.isabelle_decide_counterfactual(CF_MODUS_PONENS, methods=["blast"],
                                     centering="strong")
    assert "strongly_centered_def" in captured[0] and "blast" in captured[0]


def test_counterfactual_unknown_centering_raises_before_the_install_lookup():
    """Reported as a typo even where no Isabelle exists — not IsabelleNotAvailable."""
    with pytest.raises(ValueError, match="centering must be one of"):
        R.isabelle_decide_counterfactual(CF_MODUS_PONENS, centering="weakly")


# --------------------------------------------------------------------------- #
# isabelle_decide_modal: bridges reach the axiom list AND both theories.
# --------------------------------------------------------------------------- #

_KB = Implies(Knows("a", P), Believes("a", P))


def test_modal_bridge_axiom_in_both_theories_and_in_the_using_list(captured):
    R.isabelle_decide_modal(_KB, bridges=["knowledge_implies_belief"])
    assert len(captured) == 2
    for text in captured:
        assert "rb_in_rk" in text
    # The prove theory must also NAME the axiom in the proof: an axiomatization fact
    # is not in the default claset, so `by blast` alone would never see it.
    proof_part = captured[0].split("lemma", 1)[1]
    assert "using" in proof_part and "rb_in_rk" in proof_part


def test_modal_no_bridge_by_default(captured):
    R.isabelle_decide_modal(_KB)
    assert all("rb_in_rk" not in t for t in captured)


def test_modal_ought_implies_can_is_the_exact_correspondent(captured):
    R.isabelle_decide_modal(Implies(Obligatory(P), Diamond(P)),
                            bridges=["ought_implies_can"])
    for text in captured:
        assert "d_meets_r" in text
        assert "d_in_r" not in text        # never the folklore inclusion


def test_modal_unknown_bridge_raises_before_any_build(captured):
    with pytest.raises(ValueError, match="unknown bridge"):
        R.isabelle_decide_modal(_KB, bridges=["no_such_bridge"])
    assert not captured, "a typo must not cost a JVM start"


def test_modal_absent_family_raises_before_any_build(captured):
    with pytest.raises(ValueError, match="ought_implies_can"):
        R.isabelle_decide_modal(Implies(Box(P), Diamond(P)),
                                bridges=["ought_implies_can"])
    assert not captured


def test_modal_bridge_suppresses_the_reconstructed_witness(monkeypatch):
    """An INVALID under bridges= must not carry a witness from an evaluator that
    knows nothing about cross-family frame conditions."""
    calls = []
    monkeypatch.setattr(R, "find_isabelle", lambda *a, **k: _FakeInstall())
    monkeypatch.setattr(R, "_find_alethic_countermodel",
                        lambda *a, **k: calls.append(a) or "WITNESS")

    def fake_check_theory(theory_text, theory_name, **kwargs):
        ok = "nitpick" in theory_text          # prove fails, refute succeeds
        return R.BuildResult(ok=ok, exit_code=0 if ok else 1, output="", session="s",
                             theory_name=theory_name, elapsed=0.0)

    monkeypatch.setattr(R, "check_theory", fake_check_theory)

    v = R.isabelle_decide_modal(_KB, bridges=["knowledge_implies_belief"])
    assert v.status == R.INVALID and v.countermodel is None and not calls

    # ...while the alethic fragment without bridges still gets its witness.
    v2 = R.isabelle_decide_modal(Implies(Box(P), P), frame="K")
    assert v2.status == R.INVALID and v2.countermodel == "WITNESS"


# --------------------------------------------------------------------------- #
# Export registry.
# --------------------------------------------------------------------------- #

def test_new_public_names_are_exported():
    import unicode_fol_kit as u
    import unicode_fol_kit.fol as fol
    import unicode_fol_kit.hol as hol
    import unicode_fol_kit.semantics as sem

    for module, name in ((u, "CENTERING_LEVELS"), (sem, "CENTERING_LEVELS"),
                         (u, "QML_BRIDGES"), (fol, "QML_BRIDGES"),
                         (hol, "BRIDGES")):
        assert hasattr(module, name), f"{module.__name__}.{name}"
        assert name in module.__all__, f"{module.__name__}.__all__ misses {name}"


@pytest.mark.parametrize("module_name", [
    "unicode_fol_kit", "unicode_fol_kit.fol", "unicode_fol_kit.hol",
    "unicode_fol_kit.semantics", "unicode_fol_kit.atp",
])
def test_every_exported_name_resolves(module_name):
    """__all__ is a promise: `from <pkg> import *` must not raise."""
    import importlib
    module = importlib.import_module(module_name)
    missing = [n for n in module.__all__ if not hasattr(module, n)]
    assert not missing, f"{module_name}.__all__ names nothing: {missing}"


def test_bridge_names_agree_across_every_route():
    """The option value is a bare string a user copies between routes; if the three
    lists drifted, a name valid on one route would be a ValueError on another."""
    from unicode_fol_kit.atp.modal_tableau import _KNOWN_BRIDGES
    from unicode_fol_kit.fol.qml import QML_BRIDGES
    from unicode_fol_kit.hol.isabelle_modal import BRIDGES

    assert set(QML_BRIDGES) == set(BRIDGES) == set(_KNOWN_BRIDGES)


def test_version_is_consistent_across_the_release_artefacts():
    """A release bumps __version__, pyproject and the CHANGELOG together; docs/conf.py
    reads __version__, so those three are the whole set."""
    import unicode_fol_kit as u

    root = Path(__file__).resolve().parent.parent
    pyproject = (root / "pyproject.toml").read_text(encoding="utf-8")
    declared = re.search(r'^version = "([^"]+)"', pyproject, re.M).group(1)
    changelog = (root / "CHANGELOG.md").read_text(encoding="utf-8")
    latest = re.search(r"^## \[([0-9][^\]]*)\]", changelog, re.M).group(1)

    assert u.__version__ == declared == latest
