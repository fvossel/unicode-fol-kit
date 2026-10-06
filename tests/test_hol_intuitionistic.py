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
from unicode_fol_kit.atp.lj import int_prove
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


def test_gmt_falsum_is_the_constant():
    # "⊥" is the falsity constant: int_valid forces it at no world, so ¬⊥ and ex falso
    # are valid, and the GMT keeps it as it is (T(⊥)=⊥, the textbook rule), with no box
    # round it. (See the module's FALSUM note.)
    assert gmt_translate(BOT) == BOT
    assert int_valid(Not(BOT)) is True           # no world forces ⊥
    assert int_valid(Implies(BOT, p)) is True    # so ex falso is valid here
    assert int_valid(BOT) is False               # and ⊥ alone is not
    assert gmt_validity_matches_int_valid(Implies(BOT, p))


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
    # (p→q)∨(q→r)∨(r→p) is IPL-INVALID but needs 4 worlds to refute. int_valid's
    # 3-world DEFAULT bound used to call it valid; since the G4ip proof search
    # became the propositional positive oracle, int_valid is correct at default
    # arguments too (see tests/test_lj_search.py). Proof emission follows the
    # DECIDABLE gmt_is_s4_valid (False) and leaves `oops`, never emitting a real
    # proof for a non-theorem (which would fail to build).
    f = Or(Or(Implies(p, q), Implies(q, r)), Implies(r, p))
    assert int_valid(f) is False                     # G4ip fallback: fixed
    assert int_valid(f, max_worlds=4) is False       # genuine refutation at 4 worlds
    assert gmt_is_s4_valid(f) is False               # decidable oracle agrees
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
    # ⊥ is the falsity constant: Isabelle's own False, lifted to a world-independent
    # proposition, and no symbol is declared for it (no `consts bottom`).
    assert "consts bottom ::" not in out
    # In the lemma body the constant renders as the lifted False, never as a bare
    # reserved wildcard under a box. (Note: '\<box>_' DOES legitimately occur once in
    # the mbox mixfix notation declaration as an argument placeholder, so we look at the
    # rendered lemma line specifically.)
    lemma_line = next(ln for ln in out.splitlines() if "lemma gmt_goal:" in ln)
    assert "(\\<lambda>_. False)" in lemma_line
    assert "\\<box>_" not in lemma_line


def test_isabelle_truth_constants_declare_no_consts():
    # ⊥ and ⊤ are the two truth constants, the one False and the other True; neither is
    # a symbol of the theory, so the only constant declared is the accessibility
    # relation, and neither is the reserved wildcard. (The distinct, legal NAMES that a
    # symbolic predicate gets are pinned on the name function itself, above.)
    out = to_isabelle_intuitionistic(And(Atom("⊥", ()), Atom("⊤", ())))
    assert "consts bottom ::" not in out
    assert "consts top ::" not in out
    lemma_line = next(ln for ln in out.splitlines() if "lemma gmt_goal:" in ln)
    assert "(\\<lambda>_. False)" in lemma_line
    assert "(\\<lambda>_. True)" in lemma_line
    consts_lines = [ln for ln in out.splitlines() if ln.startswith("consts ")
                    and "::" in ln]
    decl_names = [ln.split()[1] for ln in consts_lines]
    assert decl_names == ["r"], decl_names


# ---------------------------------------------------------------------------
# Equality is REFUSED, not approximated.
#
# This module is the PROPOSITIONAL one: int_valid keys an atom by its rendered form
# (``a = a`` is just another variable, so it is not valid there), while the S4 side
# of the GMT embedding runs through fol.qml, which reads ``=`` as RIGID identity
# (``a = a`` valid). Fed an identity atom the module's own differential
# (gmt_validity_matches_int_valid and friends) would therefore compare answers to two
# different questions, and to_isabelle_intuitionistic would emit a real proof about an
# uninterpreted constant. gmt_translate refuses an ``=`` / ``≠`` atom by name, scanning
# the whole formula; every other function goes through it.
#
# None of these tests compares two independently timed solver runs (see the note at
# the top of tests/test_lj_search.py): the refusals never reach Z3, and the one place
# that does asks it a single question whose answer is a PROOF, against int_valid, which
# has no solver in it.
# ---------------------------------------------------------------------------

from unicode_fol_kit.fol.nodes import Constant
from unicode_fol_kit.hol.intuitionistic import _gmt

_ca, _cb = Constant("a"), Constant("b")
EQ = Atom("=", (_ca, _cb))
EQ_AA = Atom("=", (_ca, _ca))
NEQ = Atom("≠", (_ca, _cb))
_EQ_REFUSAL = (r"equality is not interpreted by the propositional "
               r"Gödel–McKinsey–Tarski embedding.*qml_is_valid")

_ENTRY_POINTS = {
    "gmt_translate": gmt_translate,
    "gmt_is_s4_valid": gmt_is_s4_valid,
    "gmt_validity_matches_int_valid": gmt_validity_matches_int_valid,
    "to_thf_intuitionistic": to_thf_intuitionistic,
    "to_isabelle_intuitionistic": to_isabelle_intuitionistic,
}


def test_the_s4_side_reads_identity_and_the_ipl_side_has_no_reading_to_give():
    """The REASON for the refusal, measured on the raw translation (``_gmt``,
    which skips the guard).

    The S4 target DOES interpret an identity atom — ``fol.qml`` reads ``=`` as rigid
    identity — so the box-translation of ``a = a`` and of ``¬(a = a) → p`` is valid
    there. The IPL source has no reading to compare it with: a world's valuation is
    a monotone set of atom KEYS, so ``a = a`` could only be an unconstrained letter.
    Until 0.30.0 ``int_valid`` answered anyway and said False for both formulas,
    which is the opposite verdict — so a differential between the two sides on an
    identity atom measured nothing, "green" or "red". Since 0.30.0 the IPL side
    refuses too (``semantics.intuitionistic`` and ``atp.lj``, same shared helper as
    here), so the two sides agree on what they will not answer, which is the only
    agreement available without a term semantics for intuitionistic equality.
    """
    from unicode_fol_kit.fol.qml import qml_is_valid
    for f in (EQ_AA, Implies(Not(EQ_AA), p)):
        # the S4 side: a single solver question whose answer is a PROOF (a generous
        # budget, because True is the only answer a timeout could turn into False)
        assert qml_is_valid(_gmt(f), mode="constant", frame="S4",
                            timeout=60000) is True, f.to_unicode_str()
        # the IPL side refuses rather than answering False
        with pytest.raises(NotImplementedError, match="refused by name"):
            int_valid(f)
        with pytest.raises(NotImplementedError, match="refused by name"):
            int_prove([], f)
    # and a formula WITHOUT identity still gets a real differential, both ways
    assert int_valid(Implies(p, p)) is True
    assert qml_is_valid(_gmt(Implies(p, p)), mode="constant", frame="S4") is True
    assert int_valid(Or(p, Not(p))) is False
    assert qml_is_valid(_gmt(Or(p, Not(p))), mode="constant", frame="S4") is False


@pytest.mark.parametrize("entry", sorted(_ENTRY_POINTS))
@pytest.mark.parametrize("name,f", [
    ("bare a=a", EQ_AA),
    ("a=b", EQ),
    ("a≠b", NEQ),
    ("¬(a=b)", Not(EQ)),
    ("p→(a=b)", Implies(p, EQ)),
    ("(a=b)→p", Implies(EQ, p)),
    ("p↔(a=b)", Iff(p, EQ)),
    ("p⊕(a≠b)", Xor(p, NEQ)),
    ("(a=b)∨¬(a=b)", Or(EQ, Not(EQ))),
    ("deep", Implies(Implies(p, And(q, Or(r, Not(Implies(q, EQ))))), p)),
], ids=lambda v: v if isinstance(v, str) else None)
def test_every_entry_point_refuses_an_equality_atom(entry, name, f):
    with pytest.raises(NotImplementedError, match=_EQ_REFUSAL):
        _ENTRY_POINTS[entry](f)


def test_the_scan_is_the_whole_formula_not_the_part_an_oracle_would_look_at():
    # (p ∧ ¬p) → (a = b) is intuitionistically valid whatever the right-hand atom is
    # (ex falso from a genuine contradiction), so int_valid, G4ip and the S4 oracle
    # all used to "agree" on it without ever interpreting the identity atom — the
    # case a lazy check would wave through. It is refused on every entry point, and
    # the propositional instance of the same schema is still decided, so the refusal
    # is about the atom and not about ex falso.
    f = Implies(And(p, Not(p)), EQ)
    for fn in _ENTRY_POINTS.values():
        with pytest.raises(NotImplementedError, match=_EQ_REFUSAL):
            fn(f)
    assert int_valid(Implies(And(p, Not(p)), q)) is True
    assert gmt_is_s4_valid(Implies(And(p, Not(p)), q)) is True


def test_equality_refusal_names_the_atom_the_route_and_where_to_go():
    with pytest.raises(NotImplementedError) as info:
        gmt_translate(Implies(p, EQ))
    msg = str(info.value)
    assert msg.startswith("intuitionistic GMT:")        # the module's own refusal style
    assert "'a = b'" in msg and "'='" in msg             # the atom, by name
    assert "Gödel–McKinsey–Tarski" in msg and "int_valid" in msg
    assert "fol.qml.qml_is_valid" in msg and "rigid identity" in msg
    with pytest.raises(NotImplementedError) as info:
        gmt_translate(NEQ)
    assert "disequality" in str(info.value) and "'≠'" in str(info.value)


def test_a_quantifier_is_still_a_value_error_even_around_an_equality_atom():
    x = Variable("x")
    with pytest.raises(ValueError, match="only propositional"):
        gmt_translate(Quantifier("∀", x, Atom("=", (x, x))))


def test_differential_over_an_alphabet_that_contains_an_equality_atom():
    """The exhaustive small-formula differential, with ``a = b`` added to the alphabet:
    every formula that mentions it is refused by every entry point, and every formula
    that does not still agrees with ``int_valid`` — nothing in between."""
    letters = [p, EQ]
    pool = list(letters) + [Not(x) for x in letters]
    for x in letters:
        for y in letters:
            pool += [And(x, y), Or(x, y), Implies(x, y)]
    uniq = {}
    for f in pool:
        uniq.setdefault(f.to_unicode_str(), f)
    with_eq = [f for f in uniq.values() if "=" in f.to_unicode_str()]
    without = [f for f in uniq.values() if "=" not in f.to_unicode_str()]
    assert len(with_eq) >= 10 and len(without) >= 4
    for f in with_eq:
        for fn in (gmt_translate, gmt_is_s4_valid, gmt_validity_matches_int_valid):
            with pytest.raises(NotImplementedError, match=_EQ_REFUSAL):
                fn(f)
    for f in without:
        assert gmt_validity_matches_int_valid(f) is True, f.to_unicode_str()


@pytest.mark.parametrize("name,f,valid", [
    # atoms WITH arguments, and infix atoms other than '=' / '≠', are ordinary
    # propositional letters on both sides exactly as before
    ("P(a)→P(a)", Implies(Atom("P", (_ca,)), Atom("P", (_ca,))), True),
    ("P(a)→(Q(a,b)→P(a))", Implies(Atom("P", (_ca,)),
                                   Implies(Atom("Q", (_ca, _cb)), Atom("P", (_ca,)))), True),
    ("a<b→¬¬(a<b)", Implies(Atom("<", (_ca, _cb)), Not(Not(Atom("<", (_ca, _cb))))), True),
    ("a≤b→(a≤b)", Implies(Atom("≤", (_ca, _cb)), Atom("≤", (_ca, _cb))), True),
    ("eq(a,b)→eq(a,b)", Implies(Atom("eq", (_ca, _cb)), Atom("eq", (_ca, _cb))), True),
    ("P(a)∨¬P(a)", Or(Atom("P", (_ca,)), Not(Atom("P", (_ca,)))), False),
    ("¬¬(a<b)→(a<b)", Implies(Not(Not(Atom("<", (_ca, _cb)))), Atom("<", (_ca, _cb))), False),
    # P(a) and P(b) are DIFFERENT letters, however the constants relate
    ("P(a)→P(b)", Implies(Atom("P", (_ca,)), Atom("P", (_cb,))), False),
], ids=lambda v: v if isinstance(v, str) else None)
def test_non_equality_atoms_with_arguments_stay_ordinary_letters(name, f, valid):
    assert int_valid(f) is valid
    # a valid formula gets a generous budget (a timeout can only turn a proof into a
    # False); an invalid one needs none, where a timeout IS the expected answer
    assert gmt_is_s4_valid(f, timeout=60000 if valid else 10000) is valid
    assert gmt_validity_matches_int_valid(f, timeout=60000 if valid else 10000) is True
