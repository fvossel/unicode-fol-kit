"""GL / S4.1 / Grz at THIRD order: the schema-over-propositions frames in ``hol.ho_modal``.

``hol.ho_modal`` used to refuse ``frame="GL"``/``"S4.1"``/``"Grz"`` outright
(no first-order axiom over ``R`` exists for Löb/McKinsey/Grz — see
``tests/test_hol_thirdorder.py`` for the structural + capture-safety pins).
This module is the third-order counterpart of ``tests/test_modal_frames.py``'s
own GL battery: the fast checks there confirm the STRUCTURE of what gets
emitted, and the live tests here confirm a real Isabelle kernel actually
discharges it — a real proof, not a string match — on the exact theories this
module's live-checked GL/Grz functions build.

Two things this file adds beyond the first-order battery:

1. a cross-check against :mod:`unicode_fol_kit.atp.kripke_enum`'s bounded
   finite-frame search on the SAME propositional Box/Diamond formulas, so the
   third-order route's refutation of T under GL (and non-refutation under
   Grz) is independently confirmed by a completely different verified
   evaluator (:func:`~unicode_fol_kit.semantics.kripke.satisfies_modal`), not
   just by Nitpick;
2. a THF well-formedness check on the new ``frame_loeb``/``frame_mckinsey``/
   ``frame_grz`` clauses, plus an OPTIONAL live parse through a real Leo-III
   when ``$UFK_LEO3`` is set (mirroring ``atp.leo3_backend``'s own discovery
   convention) — the kit has no in-repo THF grammar checker to lean on
   otherwise, so a real higher-order ATP is the only genuine "does this
   parse" oracle available; the balanced-delimiter check runs unconditionally
   and catches the same class of malformed-term bug a real parser would.
"""

import os
import shutil
import subprocess
import tempfile

import pytest

from unicode_fol_kit import MSFLParser
from unicode_fol_kit.atp.kripke_enum import modal_enum_search
from unicode_fol_kit.atp.tstp import extract_szs_status
from unicode_fol_kit.fol.nodes import (
    Atom, Box, Diamond, Implies, Knows, Obligatory, Permitted, Always, Next,
    Nominal, At, Constant,
)
from unicode_fol_kit.hol.ho_modal import HoGoal, isabelle_ho_modal_theory, to_thf_ho_modal
from unicode_fol_kit.hol.isabelle_runner import (
    check_theory, isabelle_available, isabelle_decide_modal,
)
from unicode_fol_kit.semantics.kripke import KripkeModel, satisfies_modal

TOM = MSFLParser(third_order=True, modal=True)

_p = Atom("p", ())
_T_PROP = Implies(Box(_p), _p)                    # T (□p → p) — fails in GL, holds in Grz


# --------------------------------------------------------------------------- #
# Cross-check: the refutation direction against atp.kripke_enum, on the SAME
# propositional formula the live Isabelle tests below use at third order.
# --------------------------------------------------------------------------- #

def test_kripke_enum_refutes_t_under_gl():
    """GL is irreflexive: a 1-world dead end (R = ∅) falsifies T (□p → p).

    Hand-checked: at the lone world w, □p holds vacuously (no accessible
    world to fail p at) while p itself is false there, so □p → p fails at w.
    That single-world relation is trivially transitive and converse
    well-founded, so it is a genuine GL frame — the smallest one there is.
    """
    result = modal_enum_search(_T_PROP, frame="GL", max_worlds=3)
    assert result.model is not None, result.detail
    assert len(list(result.model.worlds)) == 1
    assert result.model.relations["alethic"] == set()


def test_kripke_enum_does_not_refute_t_under_grz():
    """Grz includes reflexivity, so T holds on every Grz frame -- no countermodel.

    ``exhausted=True`` is not a validity proof by itself (see
    ``modal_enum_search``'s own docstring), but paired with
    ``test_grz_battery_discharges_in_isabelle`` proving the SAME formula
    below, the two routes agree.
    """
    result = modal_enum_search(_T_PROP, frame="Grz", max_worlds=3)
    assert result.model is None
    assert result.exhausted


# --------------------------------------------------------------------------- #
# Live Isabelle: the emitted third-order theories actually prove / refute.
# --------------------------------------------------------------------------- #

_isa = pytest.mark.skipif(not isabelle_available(),
                          reason="no Isabelle installation found")
_isa_live = pytest.mark.isabelle_live


@_isa_live
@_isa
def test_gl_battery_discharges_in_isabelle():
    """Under GL: the Löb schema instance and axiom 4 are theorems, T is not.

    ``loeb_thm`` is literally an instance of ``R_loeb`` (the schema
    ``□(□P→P)→□P`` at an arbitrary world), so ``using R_loeb by blast``
    discharges it directly. ``four`` (``□P→□□P``) follows from transitivity
    alone, independently of Löb. ``t_fails`` is the negative control: Nitpick
    is asked for a GENUINE countermodel (``expect = genuine`` fails the whole
    build if none is found), and ``user_axioms`` is required so Nitpick
    checks the model against the ``axiomatization``-introduced frame axioms
    themselves rather than treating them as opaque -- without it Nitpick
    reports the countermodel merely "quasi genuine" and the build fails
    (checked by hand while writing this test).
    """
    goals = [
        HoGoal("loeb_thm", TOM.parse("□(□P→P)→□P"), proof="using R_loeb by blast"),
        HoGoal("four", TOM.parse("□P→□□P"), proof="using R_trans by blast"),
        HoGoal("t_fails", TOM.parse("□P→P"),
              proof="nitpick [user_axioms, expect = genuine]\n  oops"),
        HoGoal("consistency", statement="True", kind="lemma",
              proof="nitpick [satisfy, user_axioms, expect = genuine]\n  oops"),
    ]
    thy = isabelle_ho_modal_theory("GLBattery", (), goals, frame="GL")
    r = check_theory(thy, "GLBattery", session_timeout=300)
    assert r.ok, f"GL battery did not discharge (exit {r.exit_code}):\n{r.output[-2000:]}"


@_isa_live
@_isa
def test_grz_battery_discharges_in_isabelle():
    """Under Grz: the Grz schema itself, T and 4 are all theorems, and the axioms have a model.

    ``grz_thm`` is an instance of ``R_grz``; ``t_thm`` follows from
    reflexivity, ``four_thm`` from transitivity -- neither needs the Grz
    schema itself. ``consistency`` mirrors ``hol.goedel``'s own
    ``nitpick [satisfy, user_axioms, expect = genuine]`` pattern: it finds a
    model of the accumulated ``refl``/``trans``/``grz`` axioms, so the three
    theorems above hold because they follow from a SATISFIABLE frame, not
    because the frame is secretly empty.
    """
    goals = [
        HoGoal("grz_thm", TOM.parse("□(□(P→□P)→P)→P"), proof="using R_grz by blast"),
        HoGoal("t_thm", TOM.parse("□P→P"), proof="using R_refl by blast"),
        HoGoal("four_thm", TOM.parse("□P→□□P"), proof="using R_trans by blast"),
        HoGoal("consistency", statement="True", kind="lemma",
              proof="nitpick [satisfy, user_axioms, expect = genuine]\n  oops"),
    ]
    thy = isabelle_ho_modal_theory("GrzBattery", (), goals, frame="Grz")
    r = check_theory(thy, "GrzBattery", session_timeout=300)
    assert r.ok, f"Grz battery did not discharge (exit {r.exit_code}):\n{r.output[-2000:]}"


@_isa_live
@_isa
def test_s4_1_mckinsey_battery_discharges_in_isabelle():
    """Bonus coverage: S4.1 = refl + trans + mckinsey; the schema and T both hold."""
    goals = [
        HoGoal("mckinsey_thm", TOM.parse("□◇P→◇□P"), proof="using R_mckinsey by blast"),
        HoGoal("t_thm", TOM.parse("□P→P"), proof="using R_refl by blast"),
        HoGoal("consistency", statement="True", kind="lemma",
              proof="nitpick [satisfy, user_axioms, expect = genuine]\n  oops"),
    ]
    thy = isabelle_ho_modal_theory("S41Battery", (), goals, frame="S4.1")
    r = check_theory(thy, "S41Battery", session_timeout=300)
    assert r.ok, f"S4.1 battery did not discharge (exit {r.exit_code}):\n{r.output[-2000:]}"


# --------------------------------------------------------------------------- #
# THF: well-formedness (always run) plus an optional live Leo-III parse.
# --------------------------------------------------------------------------- #

def _balanced(text: str, open_ch: str, close_ch: str) -> bool:
    """True iff every ``open_ch``/``close_ch`` in ``text`` is properly nested."""
    depth = 0
    for ch in text:
        if ch == open_ch:
            depth += 1
        elif ch == close_ch:
            depth -= 1
            if depth < 0:
                return False
    return depth == 0


@pytest.mark.parametrize("frame", ["GL", "S4.1", "Grz"])
def test_the_schema_thf_clauses_are_delimiter_balanced(frame):
    """A generic structural check, independent of what ``_THF_FRAME`` is meant to say.

    Every ``(``/``)`` and every ``[``/``]`` in the WHOLE emitted problem must
    balance -- true of any well-formed THF file regardless of content, so
    this catches a stray/missing paren in the hand-written schema strings the
    same way an actual parser would, without re-deriving the formula the way
    the implementation does.
    """
    problem = to_thf_ho_modal(TOM.parse("P"), frame=frame)
    assert _balanced(problem, "(", ")")
    assert _balanced(problem, "[", "]")


def _leo3_jar():
    return os.environ.get("UFK_LEO3")


_leo3_live = pytest.mark.skipif(
    not (_leo3_jar() and shutil.which("java")),
    reason="no Leo-III install found (set UFK_LEO3 to a leo3.jar or wrapper)")


@_leo3_live
@pytest.mark.parametrize("frame", ["GL", "S4.1", "Grz"])
def test_the_schema_thf_problem_parses_in_leo3(frame):
    """Live, optional: feed the raw THF problem to a real Leo-III and read its SZS status.

    Unlike ``atp.leo3_backend.Leo3Backend`` (which only ever builds its OWN
    NXF problem via ``to_tptp_ncl`` for the mono-modal fragment), this talks
    to Leo-III directly with the THIRD-order TH0 problem
    ``to_thf_ho_modal`` emits -- there is no in-kit backend for that fragment
    to route through. Any SZS status line at all (Theorem, CounterSatisfiable,
    GaveUp, ...) means Leo-III accepted the problem syntactically; a parse
    failure prints no SZS status, which is exactly what this asserts against.
    Skipped whenever no local Leo-III is configured -- exactly the same
    ``$UFK_LEO3`` + ``java`` discovery ``atp.leo3_backend`` uses, and, like
    that module, NOT independently verified against a real Leo-III on the
    machine this was written on.
    """
    problem = to_thf_ho_modal(TOM.parse("P"), frame=frame)
    jar = _leo3_jar()
    with tempfile.NamedTemporaryFile(mode="w", suffix=".p", delete=False,
                                     encoding="utf-8") as f:
        f.write(problem)
        path = f.name
    try:
        if jar.lower().endswith(".jar"):
            command = ["java", "-jar", jar, path, "-t", "20"]
        else:
            command = [jar, path, "-t", "20"]
        result = subprocess.run(command, capture_output=True, text=True, timeout=30)
    finally:
        try:
            os.unlink(path)
        except OSError:
            pass
    output = result.stdout + "\n" + result.stderr
    status = extract_szs_status(output)
    assert status is not None, f"no SZS status from Leo-III -- syntax problem?\n{output[-2000:]}"


# --------------------------------------------------------------------------- #
# C18 (axis 2/3): the widened modal family -- K_a/B_a/Say_a/Want_a, O/P,
# temporal (with the tnext-subset-of-t* linking), and hybrid nominals/@.
#
# Two independent routes per family, same pattern as the GL/Grz battery above:
# (1) a hand-built Kripke COUNTERMODEL, checked against satisfies_modal (the
#     kit's own ground-truth evaluator), showing what goes wrong WITHOUT the
#     frame/linking axiom this module now emits; (2) a live Isabelle run
#     proving the schema WITH the axiom in scope, and (for epistemic)
#     refuting it (nitpick) without one -- so both directions are checked,
#     not just "it type-checks".
# --------------------------------------------------------------------------- #

_AGENT_A = Constant("a")


def test_epistemic_t_axiom_countermodel_without_reflexivity():
    """Hand-checked: K_a P -> P FAILS at world 0 when K:a is not reflexive.

    worlds {0, 1}, K:a = {(0, 1)}, P true only at 1. At 0: Knows(a, P) holds
    (its one K:a-successor, 1, satisfies P) while P itself is false at 0 --
    so the T schema fails. This is exactly why ``systems={"epistemic": "T"}``
    (reflexivity) is needed for K_a P -> P to become a theorem, matching the
    live proof/refutation pair below.
    """
    model = KripkeModel(worlds={0, 1}, relations={"K:a": {(0, 1)}},
                        valuation={1: {"P"}})
    formula = Implies(Knows(_AGENT_A, Atom("P", ())), Atom("P", ()))
    assert satisfies_modal(formula, model, 0) is False
    # Add reflexivity at 0: now Knows(a, P) itself becomes false at 0 (P must
    # hold at 0 too, and it does not), so the implication holds vacuously --
    # consistent with (not a proof of) T's reflexive-relation reading.
    reflexive = KripkeModel(worlds={0, 1}, relations={"K:a": {(0, 0), (0, 1)}},
                            valuation={1: {"P"}})
    assert satisfies_modal(formula, reflexive, 0) is True


def test_deontic_seriality_countermodel():
    """Hand-checked: O(P) -> P(P) FAILS at a world with no deontic successor.

    worlds {0}, deontic = {} (not serial). At 0: Obligatory(P) is vacuously
    TRUE (universal over the empty successor set); Permitted(P) is FALSE
    (existential over the empty set). Standard Deontic Logic's ``D`` axiom
    needs seriality -- exactly what ``Rd_serial`` supplies in the embedding.
    """
    empty = KripkeModel(worlds={0}, relations={}, valuation={})
    formula = Implies(Obligatory(Atom("P", ())), Permitted(Atom("P", ())))
    assert satisfies_modal(formula, empty, 0) is False
    serial = KripkeModel(worlds={0}, relations={"deontic": {(0, 0)}},
                         valuation={0: {"P"}})
    assert satisfies_modal(formula, serial, 0) is True


def test_hybrid_at_is_world_independent():
    """``@i φ`` reads φ AT the world nominal ``i`` names, regardless of the
    current world -- so its verdict must be the SAME evaluated from world 0
    or from world 1, matching this module's ``(λv. body nom_i)`` rendering
    (a function of v that never actually uses v)."""
    model = KripkeModel(worlds={0, 1}, valuation={1: {"P"}}, nominals={"i": 1})
    formula = At(Nominal("i"), Atom("P", ()))
    assert satisfies_modal(formula, model, 0) is True
    assert satisfies_modal(formula, model, 1) is True
    # And the plain (non-@) P is world-DEPENDENT, for contrast.
    assert satisfies_modal(Atom("P", ()), model, 0) is False


def test_always_implies_next_holds_in_the_ground_truth_evaluator():
    """Sanity check for WHY the Rn_in_Rt link matters: satisfies_modal reads
    Always/Next over the SAME one-step "temporal" relation (Always over its
    reflexive-transitive closure, Next over one step directly), so Always(P)
    -> Next(P) is a theorem of satisfies_modal on EVERY model -- there is no
    countermodel to find. A shallow embedding cannot express "the same
    relation, closed", so it needs the explicit Rn_in_Rt axiom to match; the
    live test below confirms the embedded theory actually has it.
    """
    model = KripkeModel(worlds={0, 1, 2}, relations={"temporal": {(0, 1), (1, 2)}},
                        valuation={1: {"P"}, 2: {"P"}})
    formula = Implies(Always(Atom("P", ())), Next(Atom("P", ())))
    assert satisfies_modal(formula, model, 0) is True


# --------------------------------------------------------------------------- #
# Live Isabelle: proof + refutation pairs for the new families.
# --------------------------------------------------------------------------- #

@_isa_live
@_isa
def test_epistemic_t_axiom_proves_under_t_and_is_refuted_under_k():
    """Both directions of test_epistemic_t_axiom_countermodel_without_reflexivity,
    live: K_a P -> P discharges WITH ``systems={"epistemic": "T"}`` (reflexivity)
    and Nitpick finds a genuine countermodel WITHOUT it (plain K)."""
    formula = TOM.parse("K_a Pos(G) → Pos(G)")
    proved = isabelle_ho_modal_theory(
        "EpiT", (), [HoGoal("t_thm", formula, proof="using Rk_refl by blast")],
        systems={"epistemic": "T"})
    r1 = check_theory(proved, "EpiT", session_timeout=240)
    assert r1.ok, f"T-axiom did not discharge under systems={{'epistemic': 'T'}}:\n{r1.output[-2000:]}"

    refuted = isabelle_ho_modal_theory(
        "EpiK", (), [HoGoal("t_fails", formula,
                            proof="nitpick [user_axioms, expect = genuine]\n  oops")])
    r2 = check_theory(refuted, "EpiK", session_timeout=240)
    assert r2.ok, f"T-axiom unexpectedly not refuted under plain K:\n{r2.output[-2000:]}"


@_isa_live
@_isa
def test_deontic_d_axiom_proves_live():
    formula = TOM.parse("Ⓞ Pos(G) → Ⓟ Pos(G)")
    thy = isabelle_ho_modal_theory("DeoD", (), [HoGoal("d_thm", formula,
                                                        proof="using Rd_serial by blast")])
    r = check_theory(thy, "DeoD", session_timeout=240)
    assert r.ok, f"deontic D axiom did not discharge:\n{r.output[-2000:]}"


@_isa_live
@_isa
def test_temporal_always_implies_next_needs_and_gets_the_linking_axiom():
    formula = TOM.parse("Ⓖ Pos(G) → Ⓝ Pos(G)")
    thy = isabelle_ho_modal_theory("TempLink", (), [HoGoal("g", formula,
                                                            proof="using Rn_in_Rt by blast")])
    assert "axiomatization where Rn_in_Rt:" in thy
    r = check_theory(thy, "TempLink", session_timeout=240)
    assert r.ok, f"Always -> Next did not discharge via Rn_in_Rt:\n{r.output[-2000:]}"


@_isa_live
@_isa
def test_until_base_case_proves_live():
    """``psi -> (phi Ⓤ psi)`` is exactly ``muntil_base``, the least fixpoint's
    own base rule -- discharges by a one-step ``metis`` unfolding of it."""
    formula = TOM.parse("Pos(G) → (Pos(H) Ⓤ Pos(G))")
    thy = isabelle_ho_modal_theory("UntilBase", (), [HoGoal(
        "g", formula, proof="by (metis muntil_base)")])
    r = check_theory(thy, "UntilBase", session_timeout=240)
    assert r.ok, f"Until base case did not discharge:\n{r.output[-2000:]}"


@_isa_live
@_isa
def test_hybrid_at_is_rigid_live():
    """``@i φ -> □(@i φ)`` -- @ is world-independent, so it is necessarily
    whatever it is, with NO frame axiom needed at all."""
    formula = TOM.parse("@i Pos(G) → □@i Pos(G)")
    thy = isabelle_ho_modal_theory("Rigid", (), [HoGoal("g", formula, proof="by blast")])
    r = check_theory(thy, "Rigid", session_timeout=240)
    assert r.ok, f"@ rigidity did not discharge:\n{r.output[-2000:]}"


@_isa_live
@_isa
def test_two_agent_indexed_systems_at_once_type_check_live():
    """Regression for the euclidean-schema bug caught while writing this
    battery (see test_hol_thirdorder's
    test_the_euclidean_per_agent_axiom_keeps_the_agent_in_its_conclusion):
    TWO agent-indexed relations declared together (epistemic S5, doxastic
    KD45 -- the latter includes "eucl") used to fail to even TYPE-CHECK
    (Isabelle rejected the theory with a real type clash between Rk's and
    Rb's world slots), because the euclidean axiom's conclusion dropped the
    agent argument. K_a P -> B_a P is not a theorem of two independent
    relations, so this is a NITPICK refutation, not a proof -- the live
    assertion here is that the theory loads and Nitpick runs at all.
    """
    formula = TOM.parse("K_a Pos(G) → B_a Pos(G)")
    thy = isabelle_ho_modal_theory(
        "TwoSystems", (),
        [HoGoal("g", formula, proof="nitpick [user_axioms, expect = genuine]\n  oops")],
        systems={"epistemic": "S5", "doxastic": "KD45"})
    r = check_theory(thy, "TwoSystems", session_timeout=240)
    assert r.ok, f"two-system theory did not even type-check:\n{r.output[-2000:]}"


# --------------------------------------------------------------------------- #
# Identity: rigid HOL equality, decided the same way by the modal routes that read it.
#
# `=` between individuals is HOL's own identity over the individual type `i`, with no
# world argument, so it cannot vary with the world - the reading of
# `fol.qml.qml_is_valid`, `hol.thf_modal` and `hol.isabelle_modal`. This route used to
# declare an uninterpreted world-relativised `feq` instead and so called `a = a`
# INVALID. Every verdict below is derived by hand from this semantics, never read off
# the code:
#
#   a model is a frame <W, R>, a non-empty set `i` of individuals (the same at every
#   world: constant domain, unless the row says `varying`), constants a, b, c denoting
#   elements of `i`, and an arbitrary world-indexed extension for every predicate;
#   `a = b` is true at a world iff a and b are the same element - at EVERY world alike.
#
# A countermodel is named in each INVALID row; each VALID row says why none exists.
# Three independent checks then run against the table: Z3 on the first-order shallow
# embedding (`qml_is_valid`), the third-order finite-model evaluator for the rows with a
# property argument, and - live - a real Isabelle kernel on this route's own theories.
# --------------------------------------------------------------------------- #

_MP = MSFLParser(modal=True)

# (label, text, frame, mode, valid, why).  In the `why` column a, b, c stand for the named
# constants alice, bob, carol of the formula (constants, not free variables: whether a
# constant lies in the quantifiers' range is exactly what the `varying` rows are about).
_IDENTITY_TABLE = [
    ("refl", "alice = alice", "K", "constant", True,
     "reflexivity of identity: the atom names no world, so it is true at every one"),
    ("distinct", "alice = bob", "K", "constant", False,
     "countermodel: one world, i = {e1, e2}, a = e1, b = e2 - identity is false"),
    ("necessity", "alice = bob → □(alice = bob)", "K", "constant", True,
     "necessity of identity: if a = b then the atom is true at every world, so at every "
     "successor - no frame condition needed"),
    ("necessity-neq", "alice ≠ bob → □(alice ≠ bob)", "K", "constant", True,
     "necessity of distinctness: ¬(a = b) is world-independent for the same reason"),
    ("possibly", "◇(alice = bob) → alice = bob", "K", "constant", True,
     "a successor satisfies a = b; identity is world-independent, so it holds here too"),
    ("box-dead-end", "□(alice = bob) → alice = bob", "K", "constant", False,
     "countermodel: one world with NO successor (R empty): □(a = b) is vacuously true "
     "while a = e1 and b = e2 are different"),
    ("box-reflexive", "□(alice = bob) → alice = bob", "T", "constant", True,
     "reflexive frame: w is its own successor, so □(a = b) gives a = b at w"),
    ("necessity-reflexive", "alice = bob → □(alice = bob)", "T", "constant", True,
     "extra frame axioms cannot remove a theorem of K, and unlike the row above this one "
     "does not lean on reflexivity: an uninterpreted relation would not satisfy it"),
    ("box-serial", "□(alice = bob) → alice = bob", "KD", "constant", True,
     "serial frame: some successor v exists, a = b holds there, and identity is rigid"),
    ("leibniz", "alice = bob → (G(alice) → G(bob))", "K", "constant", True,
     "Leibniz's law for a predicate: substitution of equals - a and b are one element"),
    ("leibniz-box", "alice = bob → □(G(alice) → G(bob))", "K", "constant", True,
     "the same under □: a and b are one element at every world"),
    ("quantified", "∀x ∀y (x = y → □(x = y))", "K", "constant", True,
     "necessity of identity for quantified variables"),
    ("exists-constant", "∃x (x = carol)", "K", "constant", True,
     "constant domain: c itself is the witness"),
    ("exists-varying", "∃x (x = carol)", "K", "varying", False,
     "countermodel: one world, i = {e1, e2}, D(w) = {e1}, c = e2 - c exists nowhere"),
    ("refl-varying", "alice = alice", "K", "varying", True,
     "identity is not existence-guarded: a = a holds even where a does not exist"),
    # third order: a predicate whose argument is a property DEFINED by identity
    ("congruence-third", "alice = bob → (Pos(λx. x = alice) → Pos(λx. x = bob))", "K", "constant", True,
     "if a = b the two λ-terms denote the SAME property, and Pos - an uninterpreted "
     "predicate of properties - gives equal results on equal arguments"),
    ("distinct-third", "Pos(λx. x = alice) → Pos(λx. x = bob)", "K", "constant", False,
     "countermodel: one world, i = {e1, e2}, a = e1, b = e2, Pos true of exactly the "
     "property {e1}: Pos('is a') holds and Pos('is b') does not"),
    ("leibniz-quantified", "alice = bob → ∀P (P(alice) ↔ P(bob))", "K", "constant", True,
     "Leibniz's law quantified over every property: a and b are one element"),
    ("indiscernibles", "∀P (P(alice) → P(bob)) → alice = bob", "K", "constant", True,
     "the converse. ∀P ranges over EVERY function i ⇒ world ⇒ bool, so P := 'is a' "
     "(true of a at every world, by a = a) is among them; then P(b) says b = a"),
]


def _has_property_argument(text):
    return "Pos" in text or "∀P" in text


@pytest.mark.parametrize("label,text,frame,mode,valid,why", [
    pytest.param(*row, id=row[0]) for row in _IDENTITY_TABLE
    if not _has_property_argument(row[1])])
def test_identity_table_agrees_with_the_first_order_oracle(label, text, frame, mode,
                                                           valid, why):
    """Z3 on the first-order shallow embedding gives the hand-derived verdict, with a
    DEFINITE answer both ways: a valid row is unsat on its negation, and an invalid row
    is sat - a Z3 'unknown' would satisfy neither, so it cannot pass as 'not valid'."""
    from unicode_fol_kit.atp.z3_models import is_satisfiable, is_valid
    from unicode_fol_kit.fol.nodes import Not
    from unicode_fol_kit.fol.qml import qml_validity_formula
    query = qml_validity_formula(_MP.parse(text), mode=mode, frame=frame)
    if valid:
        assert is_valid(query), why
    else:
        assert not is_valid(query), why
        assert is_satisfiable(Not(query)), f"Z3 found no countermodel and no proof: {why}"


def _refuted_by_a_small_structure(text, max_size=2):
    """True iff some classical structure with at most ``max_size`` individuals refutes
    ``text`` (a modal-free third-order formula over the constants ``alice``, ``bob``,
    which may denote any elements; the unary predicate ``G`` and the predicate of
    properties ``Pos`` range over EVERYTHING).

    A modal-free formula holds at every world of every model iff it holds in every
    classical structure (a model with one world IS a structure, and the truth of such a
    formula at a world depends on that world's extensions alone), so this is the
    third-order evaluator's independent verdict for the rows without □/◇. Identity is
    Python's own ``==`` on the domain elements there.
    """
    from itertools import combinations, product
    from unicode_fol_kit.semantics import Structure
    from unicode_fol_kit.semantics.thirdorder import satisfies_to
    formula = TOM.parse(text)
    for n in range(1, max_size + 1):
        domain = tuple(range(n))
        properties = [frozenset((d,) for d in subset)
                      for r in range(n + 1) for subset in combinations(domain, r)]
        for pos_choice in product((False, True), repeat=len(properties)):
            pos = {(prop,) for prop, chosen in zip(properties, pos_choice) if chosen}
            for g in properties:
                for alice, bob in product(domain, repeat=2):
                    structure = Structure(
                        domain, constants={"alice": alice, "bob": bob},
                        predicates={("Pos", 1): pos, ("G", 1): set(g)})
                    if not satisfies_to(formula, structure):
                        return True
    return False


@pytest.mark.parametrize("label,text,frame,mode,valid,why", [
    pytest.param(*row, id=row[0]) for row in _IDENTITY_TABLE
    if _has_property_argument(row[1])])
def test_property_rows_agree_with_the_third_order_finite_model_evaluator(
        label, text, frame, mode, valid, why):
    """The rows qml cannot read (a property argument) against `semantics.thirdorder`,
    which interprets `=` as real identity on a finite domain. A refutation is a
    definite countermodel; the absence of one below three individuals is consistent
    with validity (not a proof of it - the live Isabelle test supplies that)."""
    assert (not _refuted_by_a_small_structure(text)) is valid, why


# --- live: this route's own theories, run by a real Isabelle ---------------- #

_IDENTITY_TACTIC = {
    "T": "using R_refl by blast",
    "KD": "using R_serial by blast",
}
# The one row automation cannot close unaided: it must INSTANTIATE the property
# quantifier at 'is a' (blast / auto / metis all time out). The proof says exactly that.
_INSTANTIATE_AT_IS_A = r"""proof (intro allI impI)
    fix v
    assume H: "\<forall>P::i \<Rightarrow> sigma. P alice v \<longrightarrow> P bob v"
    have "(\<lambda>(x::i) (_::world). x = alice) alice v \<longrightarrow> (\<lambda>(x::i) (_::world). x = alice) bob v"
      using H by (rule spec)
    thus "alice = bob" by simp
  qed"""
_IDENTITY_PROOF = {"indiscernibles": _INSTANTIATE_AT_IS_A}
_PROVE = "by (blast | auto | metis)"
_REFUTE = "nitpick [user_axioms, expect = genuine]\n  oops"


def _identity_groups():
    groups = {}
    for label, text, frame, mode, valid, why in _IDENTITY_TABLE:
        groups.setdefault((frame, mode), []).append((label, text, valid))
    return groups


@_isa_live
@_isa
@pytest.mark.parametrize("frame,mode", sorted(_identity_groups()),
                         ids=lambda v: str(v))
def test_identity_table_is_decided_by_isabelle_as_derived(frame, mode):
    """Every row of this (frame, mode) group in ONE theory: a VALID row is closed by a
    proof, an INVALID row by ``nitpick [expect = genuine]`` - which FAILS the whole build
    if nitpick finds no genuine countermodel. So the build succeeds iff every row came
    out exactly as derived above."""
    rows = _identity_groups()[(frame, mode)]
    default = _IDENTITY_TACTIC.get(frame, _PROVE)
    goals = [HoGoal("row_" + label.replace("-", "_"), TOM.parse(text),
                    proof=_IDENTITY_PROOF.get(label, default) if valid else _REFUTE)
             for label, text, valid in rows]
    name = f"Identity_{frame}_{mode}"
    theory = isabelle_ho_modal_theory(name, (), goals, frame=frame, mode=mode)
    result = check_theory(theory, name, session_timeout=300)
    assert result.ok, (f"frame={frame} mode={mode}: a row did not come out as derived "
                       f"(exit {result.exit_code}):\n{result.output[-2500:]}")


@_isa_live
@_isa
def test_the_live_identity_check_can_fail_in_both_directions():
    """Negative controls, so the test above is not vacuous: a build that claims a proof
    of the NON-theorem ``a = b`` must fail, and so must one that claims a genuine
    countermodel of the theorem ``a = a``."""
    wrong_proof = isabelle_ho_modal_theory(
        "WrongProof", (), [HoGoal("g", TOM.parse("a = b"), proof=_PROVE)])
    assert not check_theory(wrong_proof, "WrongProof", session_timeout=240).ok
    wrong_refutation = isabelle_ho_modal_theory(
        "WrongRefutation", (), [HoGoal("g", TOM.parse("a = a"), proof=_REFUTE)])
    assert not check_theory(wrong_refutation, "WrongRefutation", session_timeout=240).ok


@_isa_live
@_isa
def test_isabelle_decide_modal_keeps_its_verdict_on_identity():
    """The runner decides identity on the FIRST-order route and used to raise after it
    already held nitpick's verdict (it asked ``satisfies_modal`` for a witness, which
    refuses an identity atom). ``a = b`` is invalid, ``a = b → □(a = b)`` valid, and
    neither call may raise; there is no propositional Kripke witness to exhibit for
    identity, so ``countermodel`` stays ``None``."""
    a_is_b = Atom("=", [Constant("a"), Constant("b")])
    invalid = isabelle_decide_modal(a_is_b)
    assert invalid.is_invalid, invalid
    assert invalid.countermodel is None
    valid = isabelle_decide_modal(Implies(a_is_b, Box(a_is_b)))
    assert valid.is_valid, valid
