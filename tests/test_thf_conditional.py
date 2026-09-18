# -*- coding: utf-8 -*-
"""THF export for the Lewis counterfactual conditionals ``□→`` / ``◇→``.

Structure tests always run. The live tests hand the emitted THF problems to a
real Vampire (5.0.1, inside WSL) and certify the verdicts against the SAME
Lewis sphere condition ``cf_satisfies`` evaluates, at every centering level --
Theorem must match ``cf_valid`` for every valid row of ``_LEWIS_FACTS`` below
(minus ``_VAMPIRE_SLOW``), and for every invalid row (minus
``_VAMPIRE_SLOW_INVALID``) a SEPARATE ground-model check (the toolkit's own
``cf_countermodel``, translated to closed-domain THF facts characterising
``sel`` directly) must independently re-derive the refutation. This is a
property of the battery below, not a proof that ``to_thf_conditional`` faces
no ATP-timeout class at all: ``_VAMPIRE_SLOW_INVALID`` documents one such
class (refuting a ``□→`` whose antecedent is satisfiable within some sphere
needs Vampire to synthesise a higher-order witness for the countermodel's own
``sel`` existential) that is real -- it is not a soundness gap (Vampire
reports ``Timeout``, never a wrong verdict, so a real occurrence in the
shipped battery would fail loudly, not pass silently), but it does mean an
ARBITRARY invalid Lewis formula is not guaranteed to close in the time this
suite budgets.

See :mod:`unicode_fol_kit.hol.isabelle_conditional`'s comment above
``_THF_PRELUDE`` for why the emitted term threads the current world through
the recursion, and why ``nested``/``weakly_centered``/``strongly_centered`` are
nullary facts about the one fixed ``sel`` rather than a schema over an
arbitrary sphere-function: that choice was made BECAUSE the alternative (a
line-for-line THF transcription of the Isabelle ``_PREAMBLE``, with named
NegC/AndC/OrC/ImpC/IffC/CondC combinators applied to already-built ``tau``
terms) measurably could not be discharged by Vampire's default portfolio, as
found -- and first fixed -- on the relevant-logic sibling
(:mod:`tests.test_thf_relevant`); this module hit the identical issue and got
the identical fix.
"""

import os
import re
import subprocess
import tempfile

import pytest

from unicode_fol_kit.fol.msflparser import MSFLParser
from unicode_fol_kit.hol._ho_common import ThfNames
from unicode_fol_kit.hol.isabelle_conditional import (
    to_thf_conditional, _thf_encode, _thf_would_at, _THF_RESERVED,
)
from unicode_fol_kit.semantics.conditional import (
    cf_valid, cf_countermodel, cf_satisfies, CounterfactualModel,
)

_MODAL = MSFLParser(modal=True)
p = _MODAL.parse


# --------------------------------------------------------------------------- #
# Structure tests (always run).
# --------------------------------------------------------------------------- #

class TestEncoder:
    def test_atom_becomes_applied_to_the_world(self):
        assert _thf_encode(p("A"), "X", ThfNames()) == "( a @ X )"

    def test_would_becomes_the_sphere_conditional(self):
        term = _thf_encode(p("A □→ B"), "X", ThfNames())
        assert "( sel @ X @ S0 )" in term       # the sphere is around X
        assert "( a @ U0 )" in term             # antecedent at the sphere member
        assert "( a @ U0 ) => ( b @ U0 )" in term       # consequent throughout it
        assert "~ ( a @ U0 )" in term            # the vacuous disjunct

    def test_might_desugars_to_the_dual(self):
        # ◇→ gets no case of its own, so the emitted term cannot drift from
        # the evaluator's derivation ¬(A □→ ¬B): it must be the literal
        # negation of _thf_would_at(A, ¬B, ...).
        expected = f"( ~ {_thf_would_at(p('A'), p('¬B'), 'X', ThfNames(), 0)} )"
        term = _thf_encode(p("A ◇→ B"), "X", ThfNames())
        assert term == expected
        assert "~ ( b @ U0 ) )" in term          # the negated consequent, ¬B

    def test_propositional_connectives_encode(self):
        term = _thf_encode(p("(A ∧ B) → (A ∨ ¬B)"), "X", ThfNames())
        assert term == ("( ( ( a @ X ) & ( b @ X ) ) => "
                        "( ( a @ X ) | ( ~ ( b @ X ) ) ) )")

    def test_iff_and_xor(self):
        assert _thf_encode(p("A ↔ B"), "X", ThfNames()) == "( ( a @ X ) <=> ( b @ X ) )"
        assert _thf_encode(p("A ⊕ B"), "X", ThfNames()) == "( ~ ( ( a @ X ) <=> ( b @ X ) ) )"

    def test_modal_operators_are_rejected(self):
        # □/◇ range over an accessibility relation, not a similarity
        # ordering -- the boundary cf_satisfies enforces, mirrored here.
        for src in ["□A □→ B", "A □→ ◇B"]:
            with pytest.raises(NotImplementedError, match="thf_modal"):
                _thf_encode(p(src), "X", ThfNames())

    def test_quantifiers_are_rejected(self):
        fol = MSFLParser()
        with pytest.raises(NotImplementedError, match="propositional"):
            _thf_encode(fol.parse("∀x P(x)"), "X", ThfNames())

    def test_nested_would_gets_fresh_tokens_per_depth(self):
        # Importation-shaped nesting: (A □→ (B □→ C)). The inner B□→C is
        # reached through the outer Would's `right`, so it is recursed at
        # depth 1 and must use S1/U1, distinct from the outer's S0/U0.
        term = _thf_encode(p("A □→ (B □→ C)"), "X", ThfNames())
        assert "S0" in term and "S1" in term
        assert "S0" != "S1"


class TestProblem:
    def test_every_referenced_functor_is_declared(self):
        thy = to_thf_conditional(p("A □→ B"))
        for functor in ("w", "sel", "a", "b"):
            assert f"thf({functor}_type, type," in thy, functor

    def test_nesting_is_a_premise_not_an_axiom(self):
        thy = to_thf_conditional(p("A □→ A"))
        assert ", axiom," not in thy
        assert "thf(goal, conjecture, ( nested =>" in thy

    def test_nested_and_centering_definitions_are_iffs_not_lambda_equalities(self):
        # See the module comment: `<=>` is what Vampire's default portfolio
        # actually discharges.
        thy = to_thf_conditional(p("A □→ A"))
        for name in ("nested", "weakly_centered"):
            assert f"{name}_def, definition, ( {name} <=>" in thy
            assert f"{name}_def, definition, ( {name} = (" not in thy

    def test_no_freestanding_connective_combinators(self):
        thy = to_thf_conditional(p("(A ∧ B) □→ (A ∨ ¬B)"))
        for stray in ("negc_type", "andc_type", "orc_type", "impc_type",
                     "iffc_type", "condc_type"):
            assert stray not in thy

    def test_centering_none_has_no_extra_premise(self):
        # weakly_centered/strongly_centered are always DEFINED (an unused
        # definition is inert -- see isabelle_conditional.py's own preamble
        # comment), but at "none" the GOAL must not reference either -- only
        # its own conjecture line is checked here.
        thy = to_thf_conditional(p("A □→ B"), centering="none")
        goal_line = next(line for line in thy.splitlines() if line.startswith("thf(goal,"))
        assert goal_line.startswith("thf(goal, conjecture, ( nested => ( ! [X: w] :")
        assert "weakly_centered" not in goal_line
        assert "strongly_centered" not in goal_line

    def test_centering_weak_and_strong_add_their_own_premise(self):
        weak = to_thf_conditional(p("A □→ B"), centering="weak")
        assert "( nested => ( weakly_centered =>" in weak
        strong = to_thf_conditional(p("A □→ B"), centering="strong")
        assert "( nested => ( strongly_centered =>" in strong

    def test_unknown_centering_rejected(self):
        with pytest.raises(ValueError):
            to_thf_conditional(p("A □→ A"), centering="weakly")

    def test_unsupported_node_propagates(self):
        with pytest.raises(NotImplementedError):
            to_thf_conditional(p("□A □→ B"))


# --------------------------------------------------------------------------- #
# Hand-checked Lewis facts, cross-checked against cf_valid at each centering
# level (same battery as tests/test_isabelle_conditional.py's _LEWIS_FACTS,
# plus the two centering-separating schemas the module docstring of
# semantics/conditional.py names by name: modus ponens fails at V but holds at
# VW, and strong centering separates VC from VW).
# --------------------------------------------------------------------------- #

_LEWIS_FACTS = [
    ("A □→ A", "weak", True),                                        # identity
    ("((A □→ B) ∧ (A □→ C)) → (A □→ (B ∧ C))", "weak", True),        # agglomeration
    ("(A □→ B) → (A □→ (B ∨ C))", "weak", True),                     # weakened consequent
    ("(A ◇→ B) → ¬(A □→ ¬B)", "weak", True),                         # duality
    ("(A □→ B) → ((A ∧ C) □→ B)", "weak", False),                    # antecedent strengthening
    ("(A □→ B) → (¬B □→ ¬A)", "weak", False),                        # contraposition
    ("(P ∧ (P □→ Q)) → Q", "none", False),                           # MP fails at bare V
    ("(P ∧ (P □→ Q)) → Q", "weak", True),                            # MP holds once centered
    ("(P ∧ Q) → (P □→ Q)", "weak", False),                           # strong-centering schema...
    ("(P ∧ Q) → (P □→ Q)", "strong", True),                          # ...separates VC from VW
    # Both rows below are the minimal one-world, empty-valuation countermodel
    # (worlds=(0,), spheres={0: [{0}]}, valuation={}) -- weak centering is
    # trivially satisfied (the sole sphere IS {0}), the antecedent holds AT
    # THE ONLY WORLD (not vacuously: ¬B is true since B is false; A → A is a
    # tautology), and the consequent fails there. Hand-checked directly, no
    # oracle needed to see it. They are also the two counterexamples found
    # while chasing the ATP-timeout class documented at _VAMPIRE_SLOW_INVALID
    # below, so they are recorded rather than a similar pair invented fresh.
    ("¬B □→ (A ∧ B)", "weak", False),                                 # non-vacuous antecedent, both consequent conjuncts false
    ("(A → A) □→ (A ∨ B)", "weak", False),                            # tautologous antecedent, both consequent disjuncts false
]


class TestDifferentialTextBattery:
    @pytest.mark.parametrize("src,centering,expected_valid", _LEWIS_FACTS)
    def test_oracle_agrees_with_the_hand_check(self, src, centering, expected_valid):
        assert cf_valid(p(src), centering=centering) == expected_valid, (src, centering)

    @pytest.mark.parametrize("src,centering,expected_valid", _LEWIS_FACTS)
    def test_emitted_problem_is_well_formed(self, src, centering, expected_valid):
        formula = p(src)
        thy = to_thf_conditional(formula, centering=centering)
        assert thy.startswith("%")
        assert "thf(goal, conjecture," in thy
        names = ThfNames(reserved=_THF_RESERVED)
        for atom in formula.atoms():
            functor = names.functor("predicate", atom.to_unicode_str())
            assert f"thf({functor}_type, type, ( {functor} : w > $o ))." in thy


# --------------------------------------------------------------------------- #
# Live tests: a real Vampire 5.0.1, inside WSL.
# --------------------------------------------------------------------------- #

def _to_wsl_path(win_path: str) -> str:
    posix = win_path.replace("\\", "/")
    if len(posix) > 1 and posix[1] == ":":
        return f"/mnt/{posix[0].lower()}{posix[2:]}"
    return posix


def _vampire_available() -> bool:
    try:
        result = subprocess.run(
            ["wsl", "-e", "bash", "-lc", "command -v vampire"],
            capture_output=True, text=True, timeout=10)
        return result.returncode == 0 and result.stdout.strip() != ""
    except (OSError, subprocess.TimeoutExpired):
        return False


def _run_vampire(problem_text: str, timeout: int = 15) -> str:
    fd, path = tempfile.mkstemp(suffix=".p")
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as f:
            f.write(problem_text)
        wsl_path = _to_wsl_path(path)
        result = subprocess.run(
            ["wsl", "-e", "bash", "-lc", f"vampire -t {timeout} '{wsl_path}'"],
            capture_output=True, text=True, timeout=timeout + 20)
        m = re.search(r"SZS status (\w+)", result.stdout)
        return m.group(1) if m else f"NoStatus(rc={result.returncode})"
    finally:
        os.unlink(path)


requires_vampire = pytest.mark.skipif(
    not _vampire_available(), reason="no WSL Vampire installation found")


def _sel_fact(model: CounterfactualModel, wid: dict) -> str:
    """A ground ``sel`` characterisation: ``sel(w, S)`` iff ``S`` IS one of
    ``w``'s spheres, with ``S`` pinned down by its membership over the
    (closed, finite) domain -- the same trick :mod:`tests.test_thf_relevant`
    uses for the ternary ``R``, generalised to an arbitrary-arity "set"."""
    worlds = list(model.worlds)
    disjuncts = []
    for w in worlds:
        for sphere in model.sphere_system(w):
            membership = " & ".join(
                f"( S @ {wid[u]} )" if u in sphere else f"( ~ ( S @ {wid[u]} ) )"
                for u in worlds)
            disjuncts.append(f"( ( X = {wid[w]} ) & ( {membership} ) )")
    rhs = " | ".join(disjuncts) if disjuncts else "$false"
    return f"thf(sel_fact, axiom, ( ! [X: w, S: w > $o] : ( ( sel @ X @ S ) <=> ( {rhs} ) ) ))."


def _model_facts(model: CounterfactualModel, atom_functors: dict) -> tuple:
    """Ground, domain-closed THF axioms characterising ``model`` exactly."""
    worlds = list(model.worlds)
    wid = {w: f"w{i}" for i, w in enumerate(worlds)}
    lines = [f"thf({wid[w]}, type, ( {wid[w]} : w ))." for w in worlds]
    if len(worlds) > 1:
        distinct = " & ".join(f"( {wid[a]} != {wid[b]} )"
                              for i, a in enumerate(worlds) for b in worlds[i + 1:])
        lines.append(f"thf(distinct, axiom, ( {distinct} )).")
    domain = " | ".join(f"( X = {wid[w]} )" for w in worlds)
    lines.append(f"thf(domain_closure, axiom, ( ! [X: w] : ( {domain} ) )).")
    lines.append(_sel_fact(model, wid))
    for label, functor in sorted(atom_functors.items()):
        terms = [wid[w] for w in worlds if label in model.valuation.get(w, frozenset())]
        rhs = " | ".join(f"( X = {t} )" for t in terms) if terms else "$false"
        lines.append(f"thf({functor}_fact, axiom, ( ! [X: w] : "
                     f"( ( {functor} @ X ) <=> ( {rhs} ) ) )).")
    return lines, wid


#: _LEWIS_FACTS' valid rows minus the strong-centering schema at "strong".
#: Empirically (measured by hand, with a 15s single-strategy run and a 60s /
#: CASC-schedule portfolio run, both in the scratchpad): proving it needs
#: Vampire to SYNTHESISE a higher-order witness for the goal's own ``?[S:w>$o]``
#: from the abstract hypothesis ``strongly_centered`` (``sel@X@(^[U]:(U=X))``
#: is available only after unfolding a universally-quantified premise, not
#: sitting in a hypothesis-side existential the way modus ponens's witness
#: is), which neither run closed. It is still covered by the text-only
#: TestDifferentialTextBattery above (cf_valid, no prover needed) and by
#: to_isabelle_conditional's own existing Isabelle-side coverage; only the
#: live cross-check here is skipped, the same convention
#: tests/test_isabelle_relevant.py uses for its own slow Iff case.
_VAMPIRE_SLOW = {("(P ∧ Q) → (P □→ Q)", "strong")}

#: _LEWIS_FACTS' invalid rows minus the two rows added for exactly this
#: reason. This is NOT one special schema the way ``_VAMPIRE_SLOW`` above is:
#: measured by hand (a 90s run for the first row, a 30s CASC-portfolio run for
#: the second, both in the scratchpad), refuting ``¬(A □→ C)`` needs Vampire to
#: synthesise a higher-order witness for the countermodel's own ``sel``
#: existential whenever the antecedent ``A`` is satisfiable within SOME
#: sphere (the "non-vacuous" disjunct of ``_thf_would_at`` is itself an
#: existential over ``S: w > $o``, negated) -- the same shape of difficulty as
#: ``_VAMPIRE_SLOW``, just met from the refutation side rather than the proof
#: side, and NOT specific to strong centering or to these two formulas: any
#: ``□→`` whose antecedent is not universally false in the countermodel is a
#: candidate. Both rows are still covered by the text-only
#: TestDifferentialTextBattery above (cf_valid, no prover needed); only the
#: live cross-check is skipped here. See also the caveat in this module's
#: docstring and in docs/guide/higher-order.md's "THF route: to_thf_conditional"
#: section, which used to claim this cross-check covers every invalid schema
#: unconditionally -- it covers every invalid schema IN THIS BATTERY, and this
#: is the documented gap between the two.
_VAMPIRE_SLOW_INVALID = {
    ("¬B □→ (A ∧ B)", "weak"),
    ("(A → A) □→ (A ∨ B)", "weak"),
}

_VALID_FACTS = [(s, c, v) for s, c, v in _LEWIS_FACTS if v]
_INVALID_FACTS = [(s, c, v) for s, c, v in _LEWIS_FACTS if not v]
_VALID_LIVE_FACTS = [(s, c, v) for s, c, v in _VALID_FACTS if (s, c) not in _VAMPIRE_SLOW]
_INVALID_LIVE_FACTS = [(s, c, v) for s, c, v in _INVALID_FACTS
                       if (s, c) not in _VAMPIRE_SLOW_INVALID]


@requires_vampire
@pytest.mark.parametrize("src,centering,expected_valid", _VALID_LIVE_FACTS)
def test_vampire_proves_every_valid_fact(src, centering, expected_valid):
    thy = to_thf_conditional(p(src), centering=centering)
    status = _run_vampire(thy)
    assert status == "Theorem", (
        f"{src} @ {centering}: Vampire said {status}, expected Theorem\n{thy}")


@requires_vampire
@pytest.mark.parametrize("src,centering,expected_valid", _INVALID_LIVE_FACTS)
def test_vampire_confirms_every_invalid_facts_countermodel(src, centering, expected_valid):
    # Second direction: the toolkit's own bounded countermodel search
    # (verified by cf_satisfies, as tests/test_counterfactual_centering.py and
    # tests/test_isabelle_conditional.py already do), translated to
    # closed-domain ground THF facts and independently re-derived by Vampire
    # through the SAME _thf_encode the shipped exporter uses.
    formula = p(src)
    result = cf_countermodel(formula, centering=centering)
    assert result is not None, f"no countermodel found for {src} @ {centering}"
    model, world = result
    assert not cf_satisfies(formula, model, world)        # the existing oracle

    names = ThfNames(reserved=_THF_RESERVED)
    atom_functors = {a.to_unicode_str(): names.functor("predicate", a.to_unicode_str())
                     for a in formula.atoms()}
    lines = [
        "thf(w_type, type, ( w : $tType )).",
        "thf(sel_type, type, ( sel : w > ( w > $o ) > $o )).",
    ]
    lines += [f"thf({functor}_type, type, ( {functor} : w > $o ))."
             for _, functor in sorted(atom_functors.items())]
    facts, wid = _model_facts(model, atom_functors)
    lines += facts
    body = _thf_encode(formula, wid[world], names)
    lines.append(f"thf(goal, conjecture, ( ~ {body} )).")
    problem = "\n".join(lines) + "\n"

    status = _run_vampire(problem)
    assert status == "Theorem", (
        f"{src} @ {centering}: Vampire could not confirm the countermodel "
        f"(status {status})\n{problem}")
