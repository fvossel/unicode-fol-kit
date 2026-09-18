"""Structural + live-elaboration tests for the Lean 4 exporter (``hol.lean``).

Two tiers, mirroring ``tests/test_hol_classical.py`` /
``tests/test_hol_isabelle_nonmodal_live.py``:

* **Offline / always-on** — string-structural checks on the emitted Lean
  source (balanced brackets, one ``axiom`` per distinct symbol, the
  ``Nonempty`` witness, equality as ``feq``/``fneq`` vs. native ``=``,
  reserved-word de-collision, rejected fragments) plus a differential test
  that reconstructs each symbol's expected identifier from a FRESH
  ``hol.classical._SymbolResolver`` instance and checks it is actually the
  one declared in BOTH ``to_lean_fol``'s and ``to_thf_fol``'s own output —
  both exporters route every declaration through that same shared resolver
  class, so this fails if either one stops doing so (a real regression
  guard, not a tautology).
* **Live** (``@pytest.mark.lean_live``, skipped when no Lean 4 toolchain is
  found — see ``pyproject.toml``'s ``lean_live`` marker): feeds the emitted
  file to a real ``lean`` and checks elaboration / proof outcomes, and
  validates the modal-K Kripke encoding two ways against
  ``atp.tableau.is_valid_tableau`` (which decides propositional modal
  formulas over system K via ``atp.modal_tableau.is_modal_valid`` — an
  independently, separately tested route): the K axiom is provable AND
  kernel-checked (no ``sorry``), and a known non-theorem of K is not only
  unprovable but a decision tactic (``decide``) POSITIVELY refutes a
  concrete, decidable instantiation of it.
"""

import re

import pytest

from unicode_fol_kit.fol.nodes import (
    Variable, Constant, Number, Function, Atom, Not, And, Or, Xor, Implies, Iff,
    Quantifier, SortedQuantifier, Box, Diamond, Knows,
)
from unicode_fol_kit.hol.classical import (
    to_thf_fol, _signature, _SymbolResolver, _CAT_PRED, _CAT_FUNC, _CAT_CONST,
)
from unicode_fol_kit.hol import lean
from unicode_fol_kit.atp.tableau import is_valid_tableau

X = Variable("x")
Y = Variable("y")
P0 = Atom("p", ())
Q0 = Atom("q", ())


def _balanced(s: str) -> bool:
    depth = 0
    for ch in s:
        if ch in "(⟨":
            depth += 1
        elif ch in ")⟩":
            depth -= 1
            if depth < 0:
                return False
    return depth == 0


# ---------------------------------------------------------------------------
# Classical FOL: structural well-formedness
# ---------------------------------------------------------------------------

def test_lean_fol_basic_structure():
    f = Quantifier("∀", X, Implies(Atom("Human", [X]), Atom("Mortal", [X])))
    out = lean.to_lean_fol(f)
    assert "axiom Ind : Type" in out
    assert "axiom Ind_nonempty : Nonempty Ind" in out
    assert "instance : Nonempty Ind := Ind_nonempty" in out
    assert "axiom human : Ind → Prop" in out
    assert "axiom mortal : Ind → Prop" in out
    assert "theorem goal :" in out
    assert ":=" in out
    assert "sorry" in out           # emit-only default: honest, never claims a proof
    assert "∀ x : Ind," in out
    assert "(human x) → (mortal x)" in out
    assert _balanced(out)


def test_lean_fol_every_symbol_declared():
    # predicate P/2, function f/1, constant a, number 7 must each get one axiom.
    f = Atom("P", [Function("f", [Constant("a")]), Number(7)])
    out = lean.to_lean_fol(f)
    for needle in [
        "axiom p : Ind → Ind → Prop",   # predicate P, arity 2
        "axiom f : Ind → Ind",          # function f, arity 1
        "axiom a : Ind",                # constant a
        "axiom n7 : Ind",               # number 7 -> n7
    ]:
        assert needle in out, needle
    assert "(p (f a) n7)" in out
    assert _balanced(out)


def test_lean_fol_nullary_predicate_is_bare_prop():
    f = Or(Atom("A", []), Not(Atom("B", [])))
    out = lean.to_lean_fol(f)
    assert "axiom a : Prop" in out
    assert "axiom b : Prop" in out
    assert "(a ∨ (¬ b))" in out


def test_lean_fol_equality_is_uninterpreted():
    f = Atom("=", [Constant("a"), Constant("b")])
    out = lean.to_lean_fol(f)
    assert "axiom feq : Ind → Ind → Prop" in out
    assert "(feq a b)" in out
    # No primitive Lean '=' anywhere in the goal body.
    body = out.split("theorem goal :")[1]
    assert " = " not in body


def test_lean_fol_native_equality_is_lean_identity():
    f = Atom("=", [Constant("a"), Constant("b")])
    out = lean.to_lean_fol(f, native_equality=True)
    assert "feq" not in out
    assert "(a = b)" in out.split("theorem goal :")[1]
    assert "no axioms needed" in out


def test_lean_fol_native_inequality():
    f = Atom("≠", [Constant("a"), Constant("b")])
    out = lean.to_lean_fol(f, native_equality=True)
    assert "fneq" not in out
    assert "(a ≠ b)" in out.split("theorem goal :")[1]


def test_lean_fol_connectives_mapping():
    f = Iff(Or(Atom("A", []), Not(Atom("B", []))), Xor(Atom("A", []), Atom("B", [])))
    out = lean.to_lean_fol(f)
    body = out.split("theorem goal :")[1]
    assert "↔" in body
    assert "∨" in body
    assert "¬" in body
    assert "(¬ (a ↔ b))" in body   # Xor := not-iff, matching hol.classical's Isabelle rendering


def test_lean_fol_free_variables_are_closed():
    f = Atom("P", [X, Y])
    out = lean.to_lean_fol(f)
    body = out.split("theorem goal :")[1]
    assert "∀ x : Ind," in body
    assert "∀ y : Ind," in body


def test_lean_fol_axiom_role_no_proof_needed():
    f = Atom("A", [])
    out = lean.to_lean_fol(f, conjecture=False)
    assert "axiom goal : a" in out
    assert "sorry" not in out
    assert "theorem" not in out


def test_lean_fol_rejects_modal():
    f = Box(Atom("A", []))
    with pytest.raises(NotImplementedError):
        lean.to_lean_fol(f)


def test_lean_fol_custom_proof_text():
    f = Implies(P0, P0)
    out = lean.to_lean_fol(f, proof="exact fun h => h")
    assert ":= by" in out
    assert "exact fun h => h" in out
    assert out.count("sorry") == 0


def test_lean_fol_predicate_and_bound_variable_of_same_name_are_distinct():
    # Regression for a _LeanNames bug: a nullary predicate 'Foo' and a bound
    # variable ALSO named 'Foo' independently sanitise to the same stem
    # ('foo') through two SEPARATE resolvers (_SymbolResolver / _VarResolver,
    # each with its own de-collision namespace) -- _LeanNames must still
    # de-collide the SECOND request away from the first rather than silently
    # handing back the identical identifier (which would make the bound
    # variable shadow the predicate's `axiom`: Lean elaborates a shadowed
    # binder without error, just reading the WRONG declaration inside the
    # shadowed scope -- a silent semantic bug, not a build failure). See
    # TestLeanLive.test_predicate_variable_name_collision_elaborates for the
    # live counterpart (this exact formula used to fail to type-check).
    f = Quantifier("∀", Variable("Foo"),
                   And(Atom("Foo", []), Atom("Bar", [Variable("Foo")])))
    out = lean.to_lean_fol(f)
    assert "axiom foo : Prop" in out
    bound = re.search(r"∀ (\w+) : Ind,", out)
    assert bound is not None
    assert bound.group(1) != "foo"          # NOT the predicate's own identifier
    assert _balanced(out)


# ---------------------------------------------------------------------------
# Classical MSFOL: guard relativization (delegates to to_lean_fol, like the
# existing THF/Isabelle MSFOL wrappers)
# ---------------------------------------------------------------------------

def test_lean_msfol_sorted_quantifier_relativized():
    f = SortedQuantifier("∀", X, "Human", Atom("Mortal", [X]))
    out = lean.to_lean_msfol(f)
    body = out.split("theorem goal :")[1]
    # ∀x:Human Mortal(x)  ==>  ∀x. Human(x) -> Mortal(x)
    assert "human x" in body and "mortal x" in body
    assert "→" in body
    assert _balanced(out)


def test_lean_msfol_no_nonemptiness_forced_on_the_sort_itself():
    # Matches to_isabelle_msfol / to_thf_msfol: ONLY Ind is forced nonempty;
    # the sort guard predicate is not additionally asserted nonempty here.
    f = SortedQuantifier("∀", X, "Human", Atom("Mortal", [X]))
    out = lean.to_lean_msfol(f)
    assert out.count("Nonempty") == 2   # the Ind_nonempty axiom + the instance line
    assert "human_nonempty" not in out.lower()


# ---------------------------------------------------------------------------
# Reserved-word de-collision
# ---------------------------------------------------------------------------

def test_lean_fol_reserved_word_predicate_is_renamed():
    # A predicate literally named 'in' (a plausible NL preposition) must not
    # collide with Lean's `in` keyword.
    f = Atom("in", [Constant("a")])
    out = lean.to_lean_fol(f)
    assert "axiom in " not in out          # never declared as the bare keyword
    assert re.search(r"axiom in_\d* : Ind", out)


def test_lean_fol_reserved_scaffold_name_is_renamed():
    # A user constant literally named 'goal' (`_sanitize` always lower-cases
    # only the FIRST letter, so a source symbol can never collide with the
    # capitalised scaffold names `Ind`/`Ind_nonempty` -- but an all-lowercase
    # one like the theorem name `goal` is a real, reachable collision) must
    # not collide with this module's own theorem name.
    f = Atom("P", [Constant("goal")])
    out = lean.to_lean_fol(f)
    assert "theorem goal :" in out            # the module's own goal, untouched
    assert re.search(r"axiom goal_\d* : Ind", out)   # the user's constant, de-collided


# ---------------------------------------------------------------------------
# Differential: to_lean_fol and to_thf_fol extract the SAME signature
# (both call hol.classical._signature — shared code, a real regression guard)
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("f", [
    Quantifier("∀", X, Implies(Atom("Human", [X]), Atom("Mortal", [X]))),
    Atom("P", [Function("f", [Constant("a")]), Number(7)]),
    And(Atom("=", [Constant("a"), Constant("b")]), Atom("<", [Constant("a"), Constant("c")])),
    Or(Atom("A", []), Not(Atom("B", []))),
])
def test_lean_and_thf_share_the_same_signature(f):
    # Real regression guard (not a tautology): reconstruct, from a FRESH
    # _SymbolResolver instance built directly from hol.classical, the exact
    # identifier each symbol is supposed to get -- the SAME resolver class
    # both to_lean_fol (imports it from hol.classical) and to_thf_fol (uses
    # it internally) route every declaration through -- then check that
    # identifier is actually the one DECLARED in EACH exporter's own output.
    # If either exporter stopped routing through the shared resolver (e.g.
    # reimplemented its own sanitisation, or forgot to apply it to some
    # symbol), the reconstructed identifier would no longer appear in that
    # exporter's declarations and this would fail -- unlike comparing
    # `_signature(f) == _signature(f)`, which cannot fail for any input.
    preds, funcs, consts = _signature(f)
    resolver = _SymbolResolver(f)   # native_equality=False, both exporters' default
    lean_out = lean.to_lean_fol(f)
    thf_out = to_thf_fol(f)
    for name, arity in preds:
        ident = resolver.name(_CAT_PRED, name, arity)
        assert f"axiom {ident} : " in lean_out, (name, arity, ident)
        assert f"thf({ident}_decl, type" in thf_out, (name, arity, ident)
    for name, arity in funcs:
        ident = resolver.name(_CAT_FUNC, name, arity)
        assert f"axiom {ident} : " in lean_out, (name, arity, ident)
        assert f"thf({ident}_decl, type" in thf_out, (name, arity, ident)
    for name in consts:
        ident = resolver.name(_CAT_CONST, name, 0)
        assert f"axiom {ident} : " in lean_out, (name, ident)
        assert f"thf({ident}_decl, type" in thf_out, (name, ident)
    # And a coarser, output-based sanity check: the DECLARATION COUNT in each
    # emitted problem matches (one axiom / thf decl per declared symbol).
    expected = len(preds) + len(funcs) + len(consts)
    assert lean_out.count("axiom ") - 2 == expected   # minus Ind / Ind_nonempty
    assert thf_out.count("_decl") == expected


# ---------------------------------------------------------------------------
# Propositional modal K: structural well-formedness
# ---------------------------------------------------------------------------

def test_lean_modal_k_basic_structure():
    k_axiom = Implies(Box(Implies(P0, Q0)), Implies(Box(P0), Box(Q0)))
    out = lean.to_lean_modal_k(k_axiom)
    assert "axiom World : Type" in out
    assert "axiom World_nonempty : Nonempty World" in out
    assert "instance : Nonempty World := World_nonempty" in out
    assert "axiom R : World → World → Prop" in out
    assert "axiom p : World → Prop" in out
    assert "axiom q : World → Prop" in out
    assert "theorem goal : ∀ w0 : World," in out
    assert "sorry" in out
    assert _balanced(out)
    # Box unfolds to a universal over a FRESH world, guarded by R.
    assert "∀ w1 : World, R w0 w1 →" in out


def test_lean_modal_k_diamond_unfolds_existential():
    f = Diamond(P0)
    out = lean.to_lean_modal_k(f)
    body = out.split("theorem goal :")[1]
    assert "∃ w1 : World, R w0 w1 ∧ (p w1)" in body


def test_lean_modal_k_distinct_ground_atoms_get_distinct_valuations():
    f = And(Atom("Likes", [Constant("a"), Constant("b")]),
           Atom("Likes", [Constant("a"), Constant("c")]))
    out = lean.to_lean_modal_k(Box(f))
    # Two DIFFERENT ground atoms -> two DIFFERENT valuation axioms, even though
    # both come from the same predicate name. (Excludes R's own declaration,
    # `axiom R : World -> World -> Prop`, which also contains the substring
    # "World -> Prop" as its tail.)
    assert len(re.findall(r"axiom \w+ : World → Prop", out)) == 2


def test_lean_modal_k_atom_named_w0_does_not_collide_with_world_binder():
    # Regression for a _LeanNames bug: an atom literally named 'w0' is
    # exactly the stem the OUTER Kripke-world binder wants too -- both are
    # resolved through separate namespaces (_ModalAtomNames for the atom, the
    # local `w{n}` counter for world binders) that can independently produce
    # the same string. The declared axiom and every bound world variable must
    # come out as textually DISTINCT tokens (Lean tolerates a local binder
    # shadowing a top-level axiom without erroring at parse time, but here it
    # goes further: the shadowed 'w0' has type World, not World -> Prop, so
    # applying it to a world argument is a hard elaboration error -- see
    # TestLeanLive.test_modal_k_atom_named_w0_elaborates for the live check).
    f = Box(Atom("w0", ()))
    out = lean.to_lean_modal_k(f)
    assert "axiom w0 : World → Prop" in out
    bound_worlds = re.findall(r"[∀∃] (\w+) : World", out)
    assert "w0" not in bound_worlds
    assert len(bound_worlds) == len(set(bound_worlds))   # every binder token distinct
    assert _balanced(out)


def test_lean_modal_k_atom_named_w1_does_not_collide_with_nested_world_binder():
    # Same collision, one Box deeper: the FIRST fresh world token the
    # depth-1 counter allocates is also 'w1'.
    f = Box(Box(Atom("w1", ())))
    out = lean.to_lean_modal_k(f)
    assert "axiom w1 : World → Prop" in out
    bound_worlds = re.findall(r"[∀∃] (\w+) : World", out)
    assert "w1" not in bound_worlds
    assert len(bound_worlds) == len(set(bound_worlds))
    assert _balanced(out)


def test_lean_modal_k_rejects_quantifiers():
    f = Quantifier("∀", X, Box(Atom("P", [X])))
    with pytest.raises(NotImplementedError):
        lean.to_lean_modal_k(f)


def test_lean_modal_k_rejects_agent_indexed_modality():
    f = Knows(Constant("alice"), P0)
    with pytest.raises(NotImplementedError):
        lean.to_lean_modal_k(f)


def test_lean_modal_k_axiom_role_no_proof_needed():
    out = lean.to_lean_modal_k(P0, conjecture=False)
    assert "axiom goal : ∀ w0 : World, (p w0)" in out
    assert "sorry" not in out


# ---------------------------------------------------------------------------
# Live tier: LeanInstall / LeanNotAvailable plumbing (no toolchain required)
# ---------------------------------------------------------------------------

def test_lean_not_available_raised_when_no_install(monkeypatch):
    monkeypatch.setattr(lean, "find_lean", lambda *a, **k: None)
    with pytest.raises(lean.LeanNotAvailable):
        lean.check_theory("theorem t : True := trivial", "t")
    with pytest.raises(lean.LeanNotAvailable):
        lean.lean_decide_fol(P0)


def test_lean_build_result_truthiness_requires_sorry_free():
    ok_with_sorry = lean.LeanBuildResult(
        ok=True, exit_code=0, output="warning: declaration uses `sorry`",
        theory_name="t", elapsed=0.0, uses_sorry=True)
    ok_clean = lean.LeanBuildResult(
        ok=True, exit_code=0, output="", theory_name="t", elapsed=0.0, uses_sorry=False)
    failed = lean.LeanBuildResult(
        ok=False, exit_code=1, output="error", theory_name="t", elapsed=0.0)
    assert not ok_with_sorry          # elaborates, but must NOT count as proved
    assert ok_with_sorry.ok and not ok_with_sorry.proved
    assert bool(ok_clean) and ok_clean.proved
    assert not failed


# ---------------------------------------------------------------------------
# LIVE tier: real Lean 4 elaboration / proof (skipped without a toolchain)
# ---------------------------------------------------------------------------

@pytest.mark.lean_live
@pytest.mark.skipif(not lean.lean_available(), reason="no Lean 4 toolchain found")
class TestLeanLive:

    # -- classical FOL -------------------------------------------------- #

    def test_emit_only_fol_elaborates_with_sorry(self):
        f = Quantifier("∀", X, Implies(Atom("Human", [X]), Atom("Mortal", [X])))
        r = lean.check_theory(lean.to_lean_fol(f), "emit_fol")
        assert r.ok and r.uses_sorry and not r.proved

    def test_law_of_excluded_middle_is_kernel_checked_and_matches_tableau(self):
        # Hand-checked: LEM is a classical tautology (Classical.em IS its proof).
        lem = Or(P0, Not(P0))
        assert is_valid_tableau(lem) is True   # independent oracle agrees
        src = lean.to_lean_fol(lem, proof="exact Classical.em p")
        r = lean.check_theory(src, "lem")
        assert r.ok and not r.uses_sorry and r.proved

    def test_contradiction_is_never_falsely_proved(self):
        # p ∧ ¬p is NOT valid -- the battery must never report VALID for it,
        # cross-checked against the independent tableau oracle.
        contradiction = And(P0, Not(P0))
        assert is_valid_tableau(contradiction) is False
        v = lean.lean_decide_fol(contradiction)
        assert v.status == lean.UNKNOWN   # never lean.VALID

    def test_nonempty_domain_witness_makes_all_implies_exists_provable(self):
        # HAND-CHECKED textbook fact: (forall x, P x) -> (exists x, P x) is
        # valid IFF the domain is nonempty -- exactly the semantic trap the
        # module docstring calls out. Proved here using the SAME Ind_nonempty
        # witness the emitter declares.
        f = Implies(Quantifier("∀", X, Atom("P", [X])),
                    Quantifier("∃", X, Atom("P", [X])))
        proof = "intro h\nobtain ⟨w⟩ := Ind_nonempty\nexact ⟨w, h w⟩"
        src = lean.to_lean_fol(f, proof=proof)
        r = lean.check_theory(src, "nonempty_domain")
        assert r.ok and not r.uses_sorry and r.proved

    def test_native_equality_reflexivity_is_kernel_checked(self):
        # HAND-CHECKED: ∀x. x = x is valid with Lean's own (reflexive) '='.
        f = Quantifier("∀", X, Atom("=", [X, X]))
        src = lean.to_lean_fol(f, native_equality=True, proof="intro x\nrfl")
        r = lean.check_theory(src, "eq_refl")
        assert r.ok and not r.uses_sorry and r.proved

    def test_uninterpreted_equality_reflexivity_is_not_assumed(self):
        # By contrast: WITHOUT native_equality, feq is a bare uninterpreted
        # predicate, so its "reflexivity" is not derivable from the emitted
        # axioms alone -- sorry-closed still elaborates, but no proof exists.
        f = Quantifier("∀", X, Atom("=", [X, X]))
        src = lean.to_lean_fol(f)   # native_equality=False (default)
        r = lean.check_theory(src, "feq_refl_open")
        assert r.ok and r.uses_sorry   # elaborates only because of the default `sorry`

    def test_msfol_elaborates(self):
        f = SortedQuantifier("∀", X, "Human", Implies(Atom("Mortal", [X]), Atom("Mortal", [X])))
        r = lean.check_theory(lean.to_lean_msfol(f), "msfol_reflexive")
        assert r.ok

    def test_predicate_variable_name_collision_elaborates(self):
        # Live counterpart of test_lean_fol_predicate_and_bound_variable_of_
        # same_name_are_distinct: before the _LeanNames key-based fix, this
        # formula emitted a bound variable that silently reused the nullary
        # predicate 'foo's own axiom identifier, and Lean's elaborator
        # rejected the result ("Application type mismatch: ... has type Ind
        # but is expected to have type Prop").
        f = Quantifier("∀", Variable("Foo"),
                       And(Atom("Foo", []), Atom("Bar", [Variable("Foo")])))
        r = lean.check_theory(lean.to_lean_fol(f), "foo_collision")
        assert r.ok

    # -- propositional modal K ------------------------------------------ #

    def test_k_axiom_is_kernel_checked_and_matches_tableau(self):
        # HAND-CHECKED: the K axiom Box(p->q) -> (Box p -> Box q) is valid in
        # every normal modal logic, K included. Independent oracle: the
        # kit's own labelled modal tableau (atp.tableau / atp.modal_tableau).
        k_axiom = Implies(Box(Implies(P0, Q0)), Implies(Box(P0), Box(Q0)))
        assert is_valid_tableau(k_axiom) is True
        proof = "intro w h1 h2 v hRv\nexact h1 v hRv (h2 v hRv)"
        src = lean.to_lean_modal_k(k_axiom, proof=proof)
        r = lean.check_theory(src, "k_axiom")
        assert r.ok and not r.uses_sorry and r.proved

    def test_t_axiom_is_not_a_theorem_of_k(self):
        # HAND-CHECKED: Box p -> p (reflexivity) needs the T frame condition,
        # which K does NOT have -- it is emit-only-elaborable but the battery
        # must never certify it, and the independent tableau oracle agrees.
        t_axiom = Implies(Box(P0), P0)
        assert is_valid_tableau(t_axiom) is False
        r_emit = lean.check_theory(lean.to_lean_modal_k(t_axiom), "t_axiom_emit")
        assert r_emit.ok and r_emit.uses_sorry     # elaborates, not proved
        v = lean.lean_decide_modal_k(t_axiom)
        assert v.status == lean.UNKNOWN            # never lean.VALID

    def test_t_axiom_is_refuted_by_decide_on_a_concrete_two_world_model(self):
        # Validation of the Kripke encoding, part 2 (module docstring): a
        # CONCRETE, two-world, decidable instantiation of "Box p -> p" --
        # world `false` R-sees only world `true`, and `p` holds only at
        # `true` -- makes Box p TRUE and p FALSE at world `false`. Lean's own
        # `decide` tactic must not just fail to prove this, it must POSITIVELY
        # report the proposition is FALSE (soundness of the decision route).
        src = (
            "theorem not_t_axiom :\n"
            "    ∀ w : Bool, (∀ v : Bool, (w = false ∧ v = true) → v = true) → w = true := by\n"
            "  decide\n"
        )
        r = lean.check_theory(src, "t_axiom_concrete_refutation")
        assert not r.ok
        assert "is false" in r.output

    def test_modal_k_reserved_atom_name_elaborates(self):
        # A ground atom literally named 'World' (collides with the emitter's
        # own Kripke carrier type) must still elaborate cleanly.
        f = Box(Atom("World", ()))
        r = lean.check_theory(lean.to_lean_modal_k(f), "modal_reserved")
        assert r.ok

    def test_modal_k_atom_named_w0_elaborates(self):
        # Live counterpart of test_lean_modal_k_atom_named_w0_does_not_
        # collide_with_world_binder: before the _LeanNames key-based fix,
        # this formula's declared atom 'w0' and its bound outer-world
        # variable resolved to the SAME string, so the emitted 'theorem'
        # applied a World-typed local binder as if it had type World -> Prop
        # -- "Function expected at w0 but this term has type World".
        f = Box(Atom("w0", ()))
        r = lean.check_theory(lean.to_lean_modal_k(f), "w0_collision")
        assert r.ok

    def test_modal_k_atom_named_w1_under_nested_box_elaborates(self):
        # Same collision, one Box deeper -- the first FRESH world token the
        # depth-1 Box/Diamond counter allocates is also 'w1'.
        f = Box(Box(Atom("w1", ())))
        r = lean.check_theory(lean.to_lean_modal_k(f), "w1_collision")
        assert r.ok
