# -*- coding: utf-8 -*-
"""THF export for relevant logic B (simplified Routley-Meyer semantics).

Structure tests always run. The live tests hand the emitted THF problems to a
real Vampire (5.0.1, inside WSL) and certify the verdicts against the SAME
simplified Routley-Meyer clauses ``rel_satisfies`` evaluates -- Theorem must
match ``rel_valid``, and for every non-theorem a SEPARATE ground-model check
(the toolkit's own ``rel_countermodel``, translated to closed-domain THF facts)
must independently re-derive the refutation, so both directions of the
translation (valid source -> proved target; invalid source's countermodel ->
target still refutes it) are exercised, not just term-shape comparison.

See :mod:`unicode_fol_kit.hol.isabelle_relevant`'s comment above
``_THF_PRELUDE`` for why the emitted term threads the current world through
the recursion instead of routing through NegC/AndC/OrC/ImpC/IffC combinators:
that choice was made BECAUSE the combinator form (a line-for-line THF
transcription of the Isabelle ``_PREAMBLE``) measurably could not be discharged
by Vampire's default portfolio even for "P -> P" (60s / a 150-strategy CASC
sweep at 30s), while the world-threaded form the shipped code emits closes in
well under a second -- measured by hand with a battery of THF micro-examples,
kept in the scratchpad, before this test file was written.
"""

import os
import re
import subprocess
import tempfile

import pytest

from unicode_fol_kit import MSFLParser, Atom, Box
from unicode_fol_kit.hol._ho_common import ThfNames
from unicode_fol_kit.hol.isabelle_relevant import (
    to_thf_relevant, _thf_encode, _THF_RESERVED,
)
from unicode_fol_kit.semantics.relevant import rel_valid, rel_countermodel, rel_satisfies

p = MSFLParser().parse


# --------------------------------------------------------------------------- #
# Structure tests (always run).
# --------------------------------------------------------------------------- #

class TestEncoder:
    def test_atom_becomes_applied_to_the_world(self):
        assert _thf_encode(p("P"), "X", ThfNames()) == "( p @ X )"

    def test_connectives_thread_the_same_world(self):
        # Not/And/Or all apply their subterms AT THE SAME world token (unlike
        # relevant.py's Not, which substitutes `star @ world` -- see below).
        assert _thf_encode(p("P ∧ Q"), "X", ThfNames()) == "( ( p @ X ) & ( q @ X ) )"
        assert _thf_encode(p("P ∨ Q"), "X", ThfNames()) == "( ( p @ X ) | ( q @ X ) )"

    def test_not_routes_through_the_routley_star(self):
        # w |= ¬A iff w* |=/ A: the recursive call must receive `( star @ X )`,
        # not `X`, matching semantics.relevant's Not clause exactly.
        assert _thf_encode(p("¬P"), "X", ThfNames()) == "( ~ ( p @ ( star @ X ) ) )"

    def test_implies_is_the_n_r_case_split(self):
        term = _thf_encode(p("P → Q"), "X", ThfNames())
        # N-branch: every P-world of the WHOLE model is a Q-world.
        assert "( n @ X )" in term
        assert "! [Y0: w] : ( ( p @ Y0 ) => ( q @ Y0 ) )" in term
        # R-branch: every R-triple from X routes P to Q.
        assert "( ~ ( n @ X ) )" in term
        assert "! [Y0: w, Z0: w] : ( ( r @ X @ Y0 @ Z0 )" in term
        assert "( p @ Y0 ) => ( q @ Z0 )" in term

    def test_iff_is_two_implies_branches_anded(self):
        term = _thf_encode(p("P ↔ Q"), "X", ThfNames())
        # Both directions reuse Y0/Z0 (siblings, same depth) -- see the
        # docstring of _thf_implies_at for why that is sound, not a collision.
        # (Each direction contributes one POSITIVE "(n @ X) =>" use and one
        # NEGATIVE "~ (n @ X) =>" use, and "~ ( n @ X )" also contains the
        # substring "( n @ X )", so count the positive form specifically.)
        assert term.count("( n @ X ) =>") == 2
        assert term.count("( ~ ( n @ X ) ) =>") == 2

    def test_nested_implies_gets_fresh_tokens_per_depth(self):
        # Contraction: (P -> (P -> Q)) -> (P -> Q). The inner P->Q (inside the
        # antecedent) is reached through the outer Implies's `left`, so it is
        # recursed at depth 1 and must use Y1/Z1, distinct from the outer
        # Implies's own Y0/Z0 -- otherwise the outer `! [Y0,Z0]` would capture
        # the inner implication's own bound variables.
        term = _thf_encode(p("(P → (P → Q)) → (P → Q)"), "X", ThfNames())
        assert "Y0" in term and "Y1" in term
        assert "Y0" != "Y1"

    def test_xor_is_rejected(self):
        # B has no Xor reading: semantics.relevant._reject_non_propositional
        # only allows Not/And/Or/Implies/Iff.
        with pytest.raises(TypeError, match="B semantics"):
            _thf_encode(p("P ⊕ Q"), "X", ThfNames())

    def test_non_nullary_atom_is_rejected(self):
        fol = MSFLParser()
        with pytest.raises(TypeError, match="nullary"):
            _thf_encode(fol.parse("P(a)"), "X", ThfNames())

    def test_quantifiers_are_rejected(self):
        fol = MSFLParser()
        with pytest.raises(TypeError, match="B semantics"):
            _thf_encode(fol.parse("∀x P(x)"), "X", ThfNames())

    def test_modal_operators_are_rejected(self):
        with pytest.raises(TypeError, match="B semantics"):
            _thf_encode(Box(Atom("P", ())), "X", ThfNames())

    def test_shared_atom_gets_one_functor(self):
        names = ThfNames()
        _thf_encode(p("P"), "X", names)
        assert _thf_encode(p("P"), "Y", names) == "( p @ Y )"
        assert names.functor("predicate", "P") == "p"


class TestProblem:
    def test_every_referenced_functor_is_declared(self):
        thy = to_thf_relevant(p("P → Q"))
        for functor in ("w", "n", "star", "r", "p", "q"):
            assert f"thf({functor}_type, type," in thy, functor

    def test_wellformed_is_a_premise_not_an_axiom(self):
        # Same reasoning as the Isabelle side: nitpick / a model finder run on
        # the negation should still build its own N/star/R, not trust an
        # axiomatised triple.
        thy = to_thf_relevant(p("P → P"))
        assert ", axiom," not in thy
        assert "thf(goal, conjecture, ( wellformed =>" in thy

    def test_wellformed_definition_is_an_iff_not_a_lambda_equality(self):
        # See the comment above _THF_PRELUDE: `<=>` is what Vampire's default
        # portfolio actually discharges; `=` against a `^`-headed term is not.
        thy = to_thf_relevant(p("P → P"))
        assert "wellformed_def, definition, ( wellformed <=>" in thy
        assert "wellformed_def, definition, ( wellformed = (" not in thy
        assert "wellformed = ( ^" not in thy

    def test_no_freestanding_connective_combinators(self):
        # This export does NOT declare NegC/AndC/OrC/ImpC/IffC as separate THF
        # constants (see the module comment) -- the connectives are inlined.
        thy = to_thf_relevant(p("(P ∧ Q) → (P ∨ ¬Q)"))
        for stray in ("negc_type", "andc_type", "orc_type", "impc_type", "iffc_type"):
            assert stray not in thy

    def test_frame_conditions_match_relevant_model_post_init(self):
        thy = to_thf_relevant(p("P → P"))
        assert "? [X: w] : ( n @ X )" in thy                    # N nonempty
        assert "( star @ ( star @ X ) ) = X" in thy              # involution
        assert "( r @ X @ Y @ Z ) => ( ~ ( n @ X ) )" in thy      # R off N

    def test_goal_shape(self):
        thy = to_thf_relevant(p("P → P"))
        assert "! [X: w] : ( ( n @ X ) => " in thy

    def test_unsupported_node_propagates_as_type_error(self):
        with pytest.raises(TypeError):
            to_thf_relevant(Box(Atom("P", ())))

    def test_reserved_functors_cannot_be_shadowed_by_a_user_atom(self):
        # An atom literally named "N" must not collide with the frame
        # predicate `n`.
        thy = to_thf_relevant(p("N → N"))
        assert "n_2" in thy or thy.count("thf(n_type") == 1
        names = ThfNames(reserved=_THF_RESERVED)
        assert names.functor("predicate", "N") != "n"


# --------------------------------------------------------------------------- #
# Hand-checked B facts, cross-checked against rel_valid (same battery as
# tests/test_relevant.py's VALID_IN_B / INVALID_IN_B).
# --------------------------------------------------------------------------- #

_B_FACTS = [
    ("P → P", True),
    ("(P ∧ Q) → P", True),
    ("(P ∧ Q) → Q", True),
    ("P → (P ∨ Q)", True),
    ("Q → (P ∨ Q)", True),
    ("(P ∧ (Q ∨ R)) → ((P ∧ Q) ∨ (P ∧ R))", True),
    ("¬¬P → P", True),
    ("P → ¬¬P", True),
    ("P ↔ P", True),
    ("(P ↔ Q) → (P → Q)", True),
    ("P → (Q → P)", False),                      # positive paradox
    ("(P ∧ ¬P) → Q", False),                     # explosion / ECQ
    ("P → (Q ∨ ¬Q)", False),                      # irrelevant tautological consequent
    ("((P → Q) → P) → P", False),                 # Peirce
    ("P ∨ ¬P", False),                            # LEM
    ("((P ∨ Q) ∧ ¬P) → Q", False),                # disjunctive syllogism
    ("(P → (P → Q)) → (P → Q)", False),           # contraction
]


class TestDifferentialTextBattery:
    """Emit + inspect the THF problem for every fact in _B_FACTS (no prover needed)."""

    @pytest.mark.parametrize("src,expected_valid", _B_FACTS)
    def test_oracle_agrees_with_the_hand_check(self, src, expected_valid):
        assert rel_valid(p(src), max_worlds=2) == expected_valid, src

    @pytest.mark.parametrize("src,expected_valid", _B_FACTS)
    def test_emitted_problem_is_well_formed(self, src, expected_valid):
        formula = p(src)
        thy = to_thf_relevant(formula)
        assert thy.startswith("%")
        assert "thf(goal, conjecture," in thy
        # Every atom the source formula uses gets its own declaration, under
        # whatever functor ThfNames assigned it (an atom named "R" collides
        # with the frame relation's own reserved "r" and gets de-collided to
        # "r_2" -- see test_reserved_functors_cannot_be_shadowed_by_a_user_atom).
        names = ThfNames(reserved=_THF_RESERVED)
        for atom in formula.atoms():
            functor = names.functor("predicate", atom.to_unicode_str())
            assert f"thf({functor}_type, type, ( {functor} : w > $o ))." in thy


# --------------------------------------------------------------------------- #
# Live tests: a real Vampire 5.0.1, inside WSL.
# --------------------------------------------------------------------------- #

def _to_wsl_path(win_path: str) -> str:
    """``C:\\Users\\...`` -> ``/mnt/c/Users/...`` (the default WSL2 drive mount)."""
    posix = win_path.replace("\\", "/")
    if len(posix) > 1 and posix[1] == ":":
        return f"/mnt/{posix[0].lower()}{posix[2:]}"
    return posix


def _vampire_available() -> bool:
    """True if ``wsl vampire --version`` succeeds: Windows + WSL + Vampire on PATH there."""
    try:
        result = subprocess.run(
            ["wsl", "-e", "bash", "-lc", "command -v vampire"],
            capture_output=True, text=True, timeout=10)
        return result.returncode == 0 and result.stdout.strip() != ""
    except (OSError, subprocess.TimeoutExpired):
        return False


def _run_vampire(problem_text: str, timeout: int = 15) -> str:
    """Write ``problem_text`` to a temp file, run it through WSL Vampire, return the SZS word."""
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


def _model_facts(model, atom_functors, names) -> tuple:
    """Ground, domain-closed THF axioms characterising ``model`` exactly.

    ``atom_functors`` maps every atom label the formula uses to its THF
    functor (so an atom absent from ``model.valuation`` -- false everywhere --
    still gets a defining fact). Returns ``(lines, world_id)`` where
    ``world_id`` maps each Python world label to its THF constant name.
    """
    worlds = list(model.worlds)
    wid = {w: f"w{i}" for i, w in enumerate(worlds)}
    lines = [f"thf({wid[w]}, type, ( {wid[w]} : w ))." for w in worlds]
    if len(worlds) > 1:
        distinct = " & ".join(f"( {wid[a]} != {wid[b]} )"
                              for i, a in enumerate(worlds) for b in worlds[i + 1:])
        lines.append(f"thf(distinct, axiom, ( {distinct} )).")
    domain = " | ".join(f"( X = {wid[w]} )" for w in worlds)
    lines.append(f"thf(domain_closure, axiom, ( ! [X: w] : ( {domain} ) )).")

    def _char(name: str, true_worlds) -> str:
        terms = [wid[w] for w in worlds if w in true_worlds]
        rhs = " | ".join(f"( X = {t} )" for t in terms) if terms else "$false"
        return f"thf({name}_fact, axiom, ( ! [X: w] : ( ( {name} @ X ) <=> ( {rhs} ) ) ))."

    lines.append(_char("n", model.normal))
    lines.append("thf(star_fact, axiom, ( " +
                 " & ".join(f"( ( star @ {wid[w]} ) = {wid[model.star[w]]} )" for w in worlds) +
                 " )).")
    triples = [(a, b, c) for a in worlds for b in worlds for c in worlds if (a, b, c) in model.R]
    if triples:
        r_rhs = " | ".join(f"( ( X = {wid[a]} ) & ( Y = {wid[b]} ) & ( Z = {wid[c]} ) )"
                           for a, b, c in triples)
    else:
        r_rhs = "$false"
    lines.append("thf(r_fact, axiom, ( ! [X: w, Y: w, Z: w] : "
                 f"( ( r @ X @ Y @ Z ) <=> ( {r_rhs} ) ) )).")
    for label, functor in sorted(atom_functors.items()):
        lines.append(_char(functor, model.valuation.get(label, frozenset())))
    return lines, wid


_VALID_FACTS = [(s, v) for s, v in _B_FACTS if v]
_INVALID_FACTS = [(s, v) for s, v in _B_FACTS if not v]


@requires_vampire
@pytest.mark.parametrize("src,expected_valid", _VALID_FACTS)
def test_vampire_proves_every_valid_fact(src, expected_valid):
    thy = to_thf_relevant(p(src))
    status = _run_vampire(thy)
    assert status == "Theorem", f"{src}: Vampire said {status}, expected Theorem\n{thy}"


@requires_vampire
@pytest.mark.parametrize("src,expected_valid", _INVALID_FACTS)
def test_vampire_confirms_every_invalid_facts_countermodel(src, expected_valid):
    # Second direction: take the toolkit's OWN bounded countermodel search
    # (already hand-checked in tests/test_relevant.py via rel_satisfies), turn
    # it into closed-domain ground THF facts, and ask Vampire to independently
    # re-derive -- using the SAME _thf_encode the shipped exporter uses -- that
    # the formula is false at the refuting normal world. A shape comparison
    # with the Isabelle term would not catch a wrong truth condition; this
    # does, because Vampire has to actually perform the deduction.
    formula = p(src)
    result = rel_countermodel(formula, max_worlds=2)
    assert result is not None, f"no countermodel found for {src}"
    model, world = result
    assert world in model.normal
    assert not rel_satisfies(model, world, formula)     # the existing oracle

    names = ThfNames(reserved=_THF_RESERVED)
    atom_functors = {a.to_unicode_str(): names.functor("predicate", a.to_unicode_str())
                     for a in formula.atoms()}
    lines = [
        "thf(w_type, type, ( w : $tType )).",
        "thf(n_type, type, ( n : w > $o )).",
        "thf(star_type, type, ( star : w > w )).",
        "thf(r_type, type, ( r : w > w > w > $o )).",
    ]
    lines += [f"thf({functor}_type, type, ( {functor} : w > $o ))."
             for _, functor in sorted(atom_functors.items())]
    facts, wid = _model_facts(model, atom_functors, names)
    lines += facts
    body = _thf_encode(formula, wid[world], names)
    lines.append(f"thf(goal, conjecture, ( ~ {body} )).")
    problem = "\n".join(lines) + "\n"

    status = _run_vampire(problem)
    assert status == "Theorem", (
        f"{src}: Vampire could not confirm the countermodel (status {status})\n{problem}")
