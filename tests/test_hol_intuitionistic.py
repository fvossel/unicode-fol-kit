"""Tests for the intuitionistic → HOL export (Gödel–McKinsey–Tarski into S4 + SSE).

Three things are pinned:

- the **GMT box-translation** ``gmt_translate`` is checked structurally, clause by
  clause (T(p)=□p, T(¬A)=□¬T(A), T(A→B)=□(T(A)→T(B)), ∧/∨ structural);
- the **faithfulness** of the GMT→S4 embedding: its S4-validity verdict
  (``gmt_is_s4_valid``, decided inside the toolkit by the alethic SSE + Z3 under an
  S4 frame) is checked to AGREE with the toolkit's native intuitionistic decision
  procedure ``int_valid`` on a hand-checked battery AND on an exhaustive enumeration
  of small formulas — an end-to-end correctness witness needing no external prover;
- the **emitted artifacts** (THF problem, Isabelle theory) are checked structurally
  (balanced, S4 frame present, conjecture present); running them needs Leo-III /
  Satallax / Sledgehammer, which the toolkit does not invoke.
"""

import pytest

from unicode_fol_kit.fol.nodes import (
    Atom, Not, And, Or, Xor, Implies, Iff, Box, Quantifier, Variable,
)
from unicode_fol_kit.semantics.intuitionistic import int_valid
from unicode_fol_kit.hol.intuitionistic import (
    gmt_translate, gmt_is_s4_valid, gmt_validity_matches_int_valid,
    to_thf_intuitionistic, to_isabelle_intuitionistic,
)

p = Atom("p", ())
q = Atom("q", ())
r = Atom("r", ())
BOT = Atom("⊥", ())


# ---------------------------------------------------------------------------
# GMT box-translation: structural clause-by-clause checks
# ---------------------------------------------------------------------------

def test_gmt_atom_is_boxed():
    # T(p) = □p
    assert gmt_translate(p) == Box(p)


def test_gmt_negation():
    # T(¬p) = □¬T(p) = □¬□p
    assert gmt_translate(Not(p)) == Box(Not(Box(p)))


def test_gmt_implication():
    # T(p→q) = □(T(p)→T(q)) = □(□p → □q)
    assert gmt_translate(Implies(p, q)) == Box(Implies(Box(p), Box(q)))


def test_gmt_conjunction_disjunction_structural():
    # ∧ and ∨ are structural (no extra box on top).
    assert gmt_translate(And(p, q)) == And(Box(p), Box(q))
    assert gmt_translate(Or(p, q)) == Or(Box(p), Box(q))


def test_gmt_iff_expands_to_two_implications():
    # T(p↔q) = T((p→q)∧(q→p)) = □(□p→□q) ∧ □(□q→□p)
    expected = And(Box(Implies(Box(p), Box(q))), Box(Implies(Box(q), Box(p))))
    assert gmt_translate(Iff(p, q)) == expected


def test_gmt_xor_expands_to_int_clause():
    # T(p⊕q) = T((p∨q)∧¬(p∧q)); matches IntKripkeModel.forces' ⊕ clause.
    expected = And(Or(Box(p), Box(q)), Box(Not(And(Box(p), Box(q)))))
    assert gmt_translate(Xor(p, q)) == expected


def test_gmt_falsum_is_ordinary_atom():
    # The toolkit has no primitive propositional falsum: int_valid treats "⊥" as an
    # ordinary atom, so to stay faithful the GMT boxes it like any atom (T(⊥)=□⊥),
    # NOT as a logical constant. (See the module's FALSUM note.)
    assert gmt_translate(BOT) == Box(BOT)
    assert int_valid(Not(BOT)) is False          # ⊥ behaves as an atom, not false
    assert int_valid(Implies(BOT, p)) is False   # so ex-falso is NOT valid here


def test_gmt_idempotent_on_modal_free_only():
    # quantified formulas are rejected (propositional only).
    with pytest.raises(ValueError):
        gmt_translate(Quantifier("∀", Variable("x"), Atom("P", [Variable("x")])))


def test_gmt_result_is_modal_node_no_quantifiers():
    # The translation introduces only Box + Booleans; no object quantifiers appear.
    t = gmt_translate(Implies(Implies(Implies(p, q), p), p))  # Peirce
    assert any(isinstance(n, Box) for n in t.walk())
    assert not any(isinstance(n, Quantifier) for n in t.walk())


# ---------------------------------------------------------------------------
# Faithfulness: the classic intuitionistic (in)validities
# ---------------------------------------------------------------------------

_INVALID = [
    ("LEM p∨¬p", Or(p, Not(p))),
    ("DNE ¬¬p→p", Implies(Not(Not(p)), p)),
    ("Peirce ((p→q)→p)→p", Implies(Implies(Implies(p, q), p), p)),
    ("¬(p∧q)→(¬p∨¬q)", Implies(Not(And(p, q)), Or(Not(p), Not(q)))),
    ("(p→q)∨(q→p)", Or(Implies(p, q), Implies(q, p))),  # Dummett's LC, not intuit.
]

_VALID = [
    ("p→p", Implies(p, p)),
    ("p→¬¬p", Implies(p, Not(Not(p)))),
    ("p→(q→p)", Implies(p, Implies(q, p))),
    ("p∧q→p", Implies(And(p, q), p)),
    ("¬¬¬p→¬p", Implies(Not(Not(Not(p))), Not(p))),
    ("¬(p∧¬p)", Not(And(p, Not(p)))),
    ("contrapos (p→q)→(¬q→¬p)", Implies(Implies(p, q), Implies(Not(q), Not(p)))),
    ("deMorgan ¬(p∨q)↔(¬p∧¬q)", Iff(Not(Or(p, q)), And(Not(p), Not(q)))),
    ("¬¬(p∨¬p)", Not(Not(Or(p, Not(p))))),
    ("∧-comm p∧q→q∧p", Implies(And(p, q), And(q, p))),
]


@pytest.mark.parametrize("name,f", _INVALID, ids=[n for n, _ in _INVALID])
def test_gmt_invalidities_are_non_theorems(name, f):
    # Intuitionistically INVALID ⇒ the GMT→S4 embedding is a non-theorem,
    # and that matches int_valid.
    assert int_valid(f) is False
    assert gmt_is_s4_valid(f) is False


@pytest.mark.parametrize("name,f", _VALID, ids=[n for n, _ in _VALID])
def test_gmt_validities_are_theorems(name, f):
    # Intuitionistically VALID ⇒ the GMT→S4 embedding is a theorem.
    assert int_valid(f) is True
    assert gmt_is_s4_valid(f) is True


@pytest.mark.parametrize("name,f", _INVALID + _VALID, ids=[n for n, _ in _INVALID + _VALID])
def test_gmt_matches_int_valid_oracle(name, f):
    assert gmt_validity_matches_int_valid(f) is True


# ---------------------------------------------------------------------------
# Exhaustive differential: GMT-S4-validity == int_valid on every small formula
# ---------------------------------------------------------------------------

def _small_formulas(depth):
    """All formulas up to ``depth`` over {p, q}, de-duplicated by surface form."""
    base = [p, q]
    if depth == 0:
        return base
    sub = _small_formulas(depth - 1)
    out = list(sub)
    out += [Not(a) for a in sub]
    for a in sub:
        for b in sub:
            out += [And(a, b), Or(a, b), Implies(a, b)]
    uniq = {}
    for f in out:
        uniq.setdefault(f.to_unicode_str(), f)
    return list(uniq.values())


def test_gmt_matches_int_valid_exhaustive_small():
    # Depth-1 keeps the suite fast; we additionally fold in the depth-2 formulas that
    # are the classic classical/intuitionistic divergence points (LEM, DNE, Peirce,
    # the failing De Morgan, Dummett's LC), so the sweep exercises real non-theorems
    # of IPL. A full depth-2 sweep was run offline (786 formulas, 0 mismatches); it is
    # too slow for CI here.
    forms = list(_small_formulas(1))
    forms += [
        Or(p, Not(p)), Implies(Not(Not(p)), p),
        Implies(Implies(Implies(p, q), p), p),
        Implies(Not(And(p, q)), Or(Not(p), Not(q))),
        Or(Implies(p, q), Implies(q, p)),
        Implies(p, Not(Not(p))), Not(And(p, Not(p))),
    ]
    assert len(forms) >= 20
    for f in forms:
        assert gmt_is_s4_valid(f) == int_valid(f), f.to_unicode_str()


# ---------------------------------------------------------------------------
# Emitted THF problem (structural; running needs Leo-III / Satallax)
# ---------------------------------------------------------------------------

def test_thf_export_structure():
    thf = to_thf_intuitionistic(Implies(Not(Not(p)), p))
    assert thf.count("(") == thf.count(")")
    # S4 frame: reflexive + transitive must both be present.
    assert "thf(refl, axiom" in thf
    assert "thf(trans, axiom" in thf
    # the lifted operators and the conjecture.
    for block in ("thf(mbox", "thf(mvalid", "thf(goal, conjecture"):
        assert block in thf, block
    # the GMT output is box-heavy: at least one mbox application in the conjecture.
    assert "mbox @" in thf


def test_thf_lem_uses_mor_and_mbox():
    # T(p∨¬p) = □p ∨ □¬□p → the conjecture applies mor and mbox.
    thf = to_thf_intuitionistic(Or(p, Not(p)))
    assert "mor @" in thf and "mbox @" in thf
    assert thf.count("(") == thf.count(")")


# ---------------------------------------------------------------------------
# Emitted Isabelle theory (complete + loadable, unlike the alethic skeleton)
# ---------------------------------------------------------------------------

def test_isabelle_export_is_complete_theory():
    out = to_isabelle_intuitionistic(Implies(Not(Not(p)), p))
    # A real theory, not a skeleton with the lemma in a comment.
    assert out.startswith("theory ")
    assert out.rstrip().endswith("end")
    # S4 frame axioms present (reflexive + transitive).
    assert "r_refl" in out and "r_trans" in out
    # full operator set (the qml skeleton defines only mnot/mbox/mvalid).
    for op in ("mnot", "mand", "mor", "mimp", "mbox", "mvalid"):
        assert op in out, op
    # a genuine lemma statement (not commented out).
    assert "lemma gmt_goal:" in out
    # the atom is declared.
    assert "consts p ::" in out


def test_isabelle_custom_theory_name():
    out = to_isabelle_intuitionistic(Implies(p, p), theory_name="MyIPL")
    assert out.startswith("theory MyIPL")


def test_isabelle_declares_all_atoms():
    out = to_isabelle_intuitionistic(And(Implies(p, q), r))
    # p, q pass through; the atom `r` collides with the accessibility relation `r`,
    # so it is de-collided to `p_r` — the theory must NOT emit a second `consts r`.
    assert "consts p ::" in out
    assert "consts q ::" in out
    assert "consts p_r ::" in out
    assert out.count("consts r ::") == 1          # only the relation, not the atom


# ---------------------------------------------------------------------------
# Public API surface
# ---------------------------------------------------------------------------

def test_public_api_present():
    import unicode_fol_kit.hol.intuitionistic as m
    for name in ("gmt_translate", "to_thf_intuitionistic", "to_isabelle_intuitionistic",
                 "gmt_is_s4_valid", "gmt_validity_matches_int_valid"):
        assert hasattr(m, name), name


# ---------------------------------------------------------------------------
# Verdict-dependent Isabelle proof: a valid formula gets a real (Isabelle-checked)
# proof; an invalid one is left `oops`. The S4 frame facts must be `using`-d, else
# `blast`/`auto`/`metis` cannot see the bare `axiomatization` facts. (The proof is
# actually discharged by Isabelle in test_hol_isabelle_nonmodal_live.py.)
# ---------------------------------------------------------------------------

def test_isabelle_valid_formula_emits_real_proof():
    f = Implies(p, p)                       # IPL-valid
    assert int_valid(f)
    out = to_isabelle_intuitionistic(f)
    assert "using r_refl r_trans" in out
    assert "by (metis r_refl r_trans" in out
    assert "\n  oops" not in out


def test_isabelle_invalid_formula_left_as_oops():
    f = Or(p, Not(p))                       # IPL-invalid (excluded middle)
    assert not int_valid(f)
    out = to_isabelle_intuitionistic(f)
    assert "\n  oops" in out
    assert "by (metis" not in out


def test_isabelle_proof_gating_uses_decidable_oracle_not_bounded_int_valid():
    # (p→q)∨(q→r)∨(r→p) is IPL-INVALID but needs 4 worlds to refute, so int_valid's
    # DEFAULT 3-world bound wrongly calls it valid. Proof emission must follow the
    # DECIDABLE gmt_is_s4_valid (False) and leave `oops`, never emit a real proof for a
    # non-theorem (which would fail to build). Regression for the audit finding.
    f = Or(Or(Implies(p, q), Implies(q, r)), Implies(r, p))
    assert int_valid(f) is True                      # bounded oracle is WRONG here
    assert int_valid(f, max_worlds=4) is False       # genuine refutation at 4 worlds
    assert gmt_is_s4_valid(f) is False               # decidable oracle is right
    out = to_isabelle_intuitionistic(f)
    assert "\n  oops" in out
    assert "by (metis" not in out


# ---------------------------------------------------------------------------
# Regression: Isabelle atom-name sanitisation must never emit the bare reserved
# '_' token, and distinct source atoms must map to distinct legal consts names.
# (Previously ⊥/⊤/=/≠ all collapsed to the reserved wildcard '_' — unloadable.)
# ---------------------------------------------------------------------------

from unicode_fol_kit.hol.intuitionistic import _isa_atom_name


def _is_legal_isabelle_const(name: str) -> bool:
    # A bare leading '_' or the lone '_' is Isabelle's reserved wildcard; reject both.
    # The rest must be a normal identifier: letter-start, then alnum/underscore.
    if not name or name == "_" or name[0] == "_":
        return False
    if not name[0].isalpha():
        return False
    return all(c.isalnum() or c == "_" for c in name)


def test_isa_atom_name_reserved_atoms_are_distinct_and_legal():
    names = {sym: _isa_atom_name(sym) for sym in ("⊥", "⊤", "=", "≠")}
    # Each is a legal, non-'_' identifier.
    for sym, nm in names.items():
        assert nm != "_", sym
        assert _is_legal_isabelle_const(nm), (sym, nm)
    # All four are pairwise distinct.
    assert len(set(names.values())) == 4, names
    # And the documented dedicated aliases.
    assert names == {"⊥": "bottom", "⊤": "top", "=": "feq", "≠": "fneq"}


def test_isa_atom_name_never_bare_underscore():
    # Any all-symbolic atom that would sanitise to '_' must be re-prefixed, never bare.
    for sym in ("⊥", "⊤", "=", "≠", "→", "∧", "*", "#"):
        nm = _isa_atom_name(sym)
        assert nm != "_", sym
        assert nm[0] != "_", (sym, nm)
        assert _is_legal_isabelle_const(nm), (sym, nm)


def test_isa_atom_name_ordinary_atoms_unchanged():
    # Regular (non-reserved) propositional letters pass through untouched.
    for nm in ("p", "q", "abc", "P1"):
        assert _isa_atom_name(nm) == nm


def test_isa_atom_name_reserves_structural_identifiers():
    # An atom colliding with a structural identifier (the relation `r`, an axiom
    # variable `w`/`v`/`u`, the world type `i`, a lifted operator) must be de-collided
    # to a DISTINCT, legal id — else a duplicate `consts r` (or an ill-typed frame
    # axiom from an atom `w`) breaks the theory. Regression for the audit finding.
    reserved = {"i", "r", "w", "v", "u", "mnot", "mand", "mor", "mimp", "mbox", "mvalid"}
    for nm in sorted(reserved):
        out = _isa_atom_name(nm)
        assert out != nm and out not in reserved, (nm, out)   # de-collided
        assert _is_legal_isabelle_const(out) and out[-1] != "_", (nm, out)
    # Distinct reserved atoms still map to distinct names.
    assert len({_isa_atom_name(nm) for nm in reserved}) == len(reserved)


def test_isabelle_falsum_no_bare_consts_underscore():
    # to_isabelle_intuitionistic on a ⊥-containing formula must not emit 'consts _'
    # nor a bare '\<box>_' token (which would be the reserved wildcard under the box).
    out = to_isabelle_intuitionistic(Implies(BOT, p))
    assert "consts _ ::" not in out
    assert "consts _::" not in out
    # ⊥ is rendered via its alias, not the bare wildcard.
    assert "consts bottom ::" in out
    # In the lemma body the boxed ⊥ renders as the alias under the box, never as a
    # bare reserved wildcard. (Note: '\<box>_' DOES legitimately occur once in the
    # mbox mixfix notation declaration as an argument placeholder, so we look at the
    # rendered lemma line specifically.)
    lemma_line = next(ln for ln in out.splitlines() if "lemma gmt_goal:" in ln)
    assert "\\<box>bottom" in lemma_line
    assert "\\<box>_" not in lemma_line


def test_isabelle_distinct_atoms_distinct_consts():
    # Two distinct symbolic atoms must produce two distinct consts declarations.
    out = to_isabelle_intuitionistic(And(Atom("⊥", ()), Atom("⊤", ())))
    assert "consts bottom ::" in out
    assert "consts top ::" in out
    # And neither is the reserved wildcard.
    consts_lines = [ln for ln in out.splitlines() if ln.startswith("consts ")
                    and "::" in ln]
    decl_names = [ln.split()[1] for ln in consts_lines]
    # No duplicate consts names, and none is '_'.
    assert "_" not in decl_names
    assert len(decl_names) == len(set(decl_names)), decl_names
