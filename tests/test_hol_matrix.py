"""Tests for the generic finite-matrix -> HOL export (unicode_fol_kit.hol.manyvalued).

Covers the functions that generalise the many-valued THF/Isabelle export beyond
the hardcoded K3/LP pair to ANY finite ``TruthMatrix``
(:mod:`unicode_fol_kit.semantics.matrix`): :func:`to_thf_matrix`,
:func:`to_isabelle_matrix`, :func:`to_thf_matrix_entailment`,
:func:`to_isabelle_matrix_entailment`. Three matrices are exercised:

  * ``K3_MATRIX`` / ``LP_MATRIX`` -- the strong-Kleene three-valued matrices
    (values ``{0.0, 0.5, 1.0}``), so the generic path is cross-checked against
    the SAME semantics the legacy ``to_thf_k3lp``/``to_isabelle_k3lp`` cover
    (tests/test_hol_manyvalued.py, kept green separately -- unchanged
    behaviour is asserted there);
  * ``FDE_MATRIX`` -- Belnap-Dunn four-valued FDE (values ``F``/``N``/``T``/``B``,
    designated ``{T, B}``), which has genuinely different structure: 4 values
    (not 3), and famously **no valid formulas at all** (verified against the
    oracle below, not assumed).

The strategy mirrors test_hol_manyvalued.py: (1) the emitted THF's ground
equations, extracted straight from the text by regex, must equal the matrix's
own tables cell-for-cell; (2) validity/entailment decided *purely from the
emitted text* must agree with the toolkit's own decision procedure
(:func:`unicode_fol_kit.semantics.matrix.matrix_is_valid` /
:func:`~unicode_fol_kit.semantics.matrix.matrix_entails`) on a hand-checked
battery; (3) structural well-formedness (declarations, distinctness/
exhaustiveness, designated set, conjecture/lemma shape); (4) the rejection
surface (propositional-only, and a connective the matrix has no table for).
"""
import re
from itertools import product

import pytest

from unicode_fol_kit.fol.msflparser import MSFLParser
from unicode_fol_kit.fol import nodes as N
from unicode_fol_kit.semantics.matrix import (
    TruthMatrix, matrix_is_valid, matrix_entails, K3_MATRIX, LP_MATRIX, FDE_MATRIX,
)
from unicode_fol_kit.hol.manyvalued import (
    to_thf_matrix, to_isabelle_matrix,
    to_thf_matrix_entailment, to_isabelle_matrix_entailment,
)

P = MSFLParser()

# Explicit, human-chosen naming used throughout the differential tests below,
# so the text-parsing regexes are predictable and decoupled from whatever the
# module's own default naming happens to produce (that default is exercised
# separately, in the "default naming" section).
K3LP_VALUE_NAMES = {0.0: "vF", 0.5: "vB", 1.0: "vT"}
FDE_VALUE_NAMES = {"F": "vF", "N": "vN", "T": "vT", "B": "vB"}
CONN_NAMES = {
    N.Not: "tneg", N.And: "tconj", N.Or: "tdisj",
    N.Implies: "timpl", N.Iff: "tiff", N.Xor: "txor",
}
_BINARY_CLASSES = [
    (N.And, "conj"), (N.Or, "disj"), (N.Implies, "impl"), (N.Iff, "iff"), (N.Xor, "xor"),
]


# ---------------------------------------------------------------------------
# Helpers: read the emitted THF text's semantics back out and decide with it.
# ---------------------------------------------------------------------------
def _parse_thf_semantics(thf: str, value_names: dict, conn_names: dict):
    """Recover (neg-table, {cls: table}, designated-set) from emitted THF text.

    Reads ONLY what the text says (ground equations + the ``D = <name>``
    disjuncts of the designated predicate) -- it does not consult the
    ``TruthMatrix`` at all, so a text/matrix mismatch shows up as a test
    failure rather than being masked by shared code.
    """
    name_to_value = {name: v for v, name in value_names.items()}
    neg_name = conn_names[N.Not]
    neg = {}
    for m in re.finditer(rf"\( {re.escape(neg_name)} @ (\w+) \) = (\w+)", thf):
        neg[name_to_value[m.group(1)]] = name_to_value[m.group(2)]
    bins = {}
    for cls, _ in _BINARY_CLASSES:
        op = conn_names[cls]
        table = {}
        for m in re.finditer(rf"\( {re.escape(op)} @ (\w+) @ (\w+) \) = (\w+)", thf):
            table[(name_to_value[m.group(1)], name_to_value[m.group(2)])] = name_to_value[m.group(3)]
        bins[cls] = table
    des = {name_to_value[nm] for nm in re.findall(r"\( D = (\w+) \)", thf)}
    return neg, bins, des


def _eval_with(neg, bins, node, asg):
    if isinstance(node, N.Atom):
        return asg[node.to_unicode_str()]
    if isinstance(node, N.Not):
        return neg[_eval_with(neg, bins, node.formula, asg)]
    for cls, table in bins.items():
        if isinstance(node, cls):
            return table[(_eval_with(neg, bins, node.left, asg),
                          _eval_with(neg, bins, node.right, asg))]
    raise AssertionError(f"unexpected node {type(node).__name__}")


def _atom_keys(*formulas):
    keys, seen = [], set()
    for f in formulas:
        for atom in f.atoms():
            k = atom.to_unicode_str()
            if k not in seen:
                seen.add(k)
                keys.append(k)
    return keys


def _value_names_for(matrix: TruthMatrix) -> dict:
    return K3LP_VALUE_NAMES if matrix.name in ("K3", "LP") else FDE_VALUE_NAMES


def _valid_from_thf_text(formula, matrix) -> bool:
    """Decide validity using ONLY the axioms/predicate read out of the emitted THF text."""
    vn = _value_names_for(matrix)
    thf = to_thf_matrix(formula, matrix, value_names=vn, conn_names=CONN_NAMES)
    neg, bins, des = _parse_thf_semantics(thf, vn, CONN_NAMES)
    keys = _atom_keys(formula)
    for combo in product(matrix.values, repeat=len(keys)):
        asg = dict(zip(keys, combo))
        if _eval_with(neg, bins, formula, asg) not in des:
            return False
    return True


def _entails_from_thf_text(premises, conclusion, matrix) -> bool:
    vn = _value_names_for(matrix)
    thf = to_thf_matrix_entailment(premises, conclusion, matrix, value_names=vn, conn_names=CONN_NAMES)
    neg, bins, des = _parse_thf_semantics(thf, vn, CONN_NAMES)
    keys = _atom_keys(*premises, conclusion)
    for combo in product(matrix.values, repeat=len(keys)):
        asg = dict(zip(keys, combo))
        if all(_eval_with(neg, bins, p, asg) in des for p in premises):
            if _eval_with(neg, bins, conclusion, asg) not in des:
                return False
    return True


# ---------------------------------------------------------------------------
# A hand-checked battery of propositional formulas (same shape as
# tests/test_hol_manyvalued.py's BATTERY, so the two suites are comparable).
# ---------------------------------------------------------------------------
BATTERY = [
    "P",
    "P ∨ ¬P",                        # law of excluded middle (LEM)
    "(P ∧ ¬P) → Q",                  # explosion as an implication
    "P → P",
    "P → (Q → P)",
    "(P ∧ Q) → P",
    "¬¬P → P",
    "¬(P ∧ ¬P)",                     # non-contradiction
    "P ⊕ ¬P",
    "((P → Q) ∧ (Q → R)) → (P → R)",  # hypothetical syllogism
]

MATRICES = [K3_MATRIX, LP_MATRIX, FDE_MATRIX]


# ===========================================================================
# 1. Emitted truth tables are byte-faithful to the matrix's OWN tables.
# ===========================================================================
@pytest.mark.parametrize("matrix", MATRICES, ids=lambda m: m.name)
def test_emitted_tables_match_matrix_exactly(matrix):
    # A bare atom still forces ALL of the matrix's defined connectives to be
    # axiomatised (axioms are emitted for every op the matrix tabulates,
    # independent of what the particular formula uses).
    vn = _value_names_for(matrix)
    thf = to_thf_matrix(N.Atom("P", []), matrix, value_names=vn, conn_names=CONN_NAMES)
    neg, bins, des = _parse_thf_semantics(thf, vn, CONN_NAMES)
    assert neg == dict(matrix.neg)
    for cls, attr in _BINARY_CLASSES:
        assert bins[cls] == dict(getattr(matrix, attr)), (matrix.name, cls.__name__)
    assert des == set(matrix.designated)


@pytest.mark.parametrize("matrix", MATRICES, ids=lambda m: m.name)
def test_cell_equation_count_is_sum_over_defined_ops(matrix):
    # cell-equation count = sum over defined ops of |values|^arity (neg is
    # arity 1, the five binary connectives are arity 2). Every matrix here
    # (built via TruthMatrix.from_functions) defines all six.
    n = len(matrix.values)
    expected = n + 5 * (n * n)   # neg: n^1;  5 binops: n^2 each
    vn = _value_names_for(matrix)
    thf = to_thf_matrix(N.Atom("P", []), matrix, value_names=vn, conn_names=CONN_NAMES)
    neg, bins, _ = _parse_thf_semantics(thf, vn, CONN_NAMES)
    total = len(neg) + sum(len(t) for t in bins.values())
    assert total == expected


# ===========================================================================
# 2. FDE-specific structure: 4 constants, distinctness, exhaustiveness,
#    the {T, B} designated set (read straight off FDE_MATRIX, not guessed).
# ===========================================================================
def test_fde_structure():
    assert FDE_MATRIX.values == ("F", "N", "T", "B")
    assert FDE_MATRIX.designated == frozenset({"T", "B"})

    thf = to_thf_matrix(P.parse("P ∨ ¬P"), FDE_MATRIX)  # default naming: "t" + value
    assert "thf(tv_type, type, ( tv : $tType ))." in thf
    for c in ("tF", "tN", "tT", "tB"):
        assert f"thf({c}_decl, type, ( {c} : tv ))." in thf
    # distinctness: C(4,2) = 6 pairwise-distinct clauses joined by "&".
    distinct_line = [ln for ln in thf.splitlines() if "tv_distinct" in ln][0]
    assert distinct_line.count("!=") == 6
    # exhaustiveness: all 4 constants disjoined.
    exhaust_line = [ln for ln in thf.splitlines() if "tv_exhaust" in ln][0]
    assert exhaust_line.count("X =") == 4
    # designated set {T, B} -> the des predicate disjoins exactly 2 constants.
    des_line = [ln for ln in thf.splitlines() if ln.startswith("thf(des_def")][0]
    assert des_line.count("D =") == 2
    assert "tT" in des_line and "tB" in des_line
    assert "tF" not in des_line and "tN" not in des_line  # F/N are not designated
    # one conjecture, balanced parens.
    assert thf.count("conjecture") == 1
    assert thf.count("(") == thf.count(")")


def test_fde_isabelle_structure():
    isa = to_isabelle_matrix(P.parse("P ∨ ¬P"), FDE_MATRIX, name="FDE_Validity")
    assert isa.startswith("theory FDE_Validity")
    assert isa.rstrip().endswith("end")
    assert "datatype tv = tF | tN | tT | tB" in isa
    assert "lemma matrix_validity:" in isa
    for fn in ("mv_neg", "mv_conj", "mv_disj", "mv_impl", "mv_iff", "mv_xor"):
        assert fn in isa
    assert "des d \\<equiv> (d = tT \\<or> d = tB)" in isa


# ===========================================================================
# 3. Validity decided FROM THE EMITTED TEXT == the toolkit's oracle
#    (matrix_is_valid), for all three matrices.
# ===========================================================================
@pytest.mark.parametrize("formula_str", BATTERY)
@pytest.mark.parametrize("matrix", MATRICES, ids=lambda m: m.name)
def test_thf_validity_matches_oracle(formula_str, matrix):
    f = P.parse(formula_str)
    assert _valid_from_thf_text(f, matrix) == matrix_is_valid(f, matrix)


# ===========================================================================
# 4. Hand-checked headline contrasts (verdicts stated explicitly, confirmed
#    against matrix_is_valid at write time -- see the reasoning comments).
# ===========================================================================
def test_fde_has_no_valid_formulas_at_all():
    # FDE_MATRIX docstring (semantics/matrix.py): FDE has NO logical truths,
    # not even P -> P (it takes value N -- "neither" -- when P is N, and N is
    # not designated). Confirmed against the oracle for the whole battery,
    # including LEM (P v ~P) and P -> P themselves.
    for s in ["P ∨ ¬P", "P → P", "¬(P ∧ ¬P)", "(P ∧ ¬P) → Q"]:
        f = P.parse(s)
        assert matrix_is_valid(f, FDE_MATRIX) is False
        assert _valid_from_thf_text(f, FDE_MATRIX) is False
    # The export still emits a well-formed, loadable REFUTATION lemma for it
    # (an *-exists*-form witness), not a malformed/empty theory.
    isa = to_isabelle_matrix(P.parse("P ∨ ¬P"), FDE_MATRIX)
    assert "\\<exists>" in isa and "\\<not> des" in isa and "INVALID" in isa
    assert isa.rstrip().endswith("end")


def test_k3_has_no_tautologies():
    # Same headline fact as tests/test_hol_manyvalued.py, re-derived here via
    # the generic path: assigning every atom "both" (0.5) makes any formula
    # 0.5, which is NOT K3-designated ({1.0} only).
    for s in ["P ∨ ¬P", "(P ∧ ¬P) → Q", "P → P", "¬(P ∧ ¬P)"]:
        f = P.parse(s)
        assert matrix_is_valid(f, K3_MATRIX) is False
        assert _valid_from_thf_text(f, K3_MATRIX) is False


def test_lp_validates_classical_tautologies():
    for s in ["P ∨ ¬P", "(P ∧ ¬P) → Q", "P → P", "¬(P ∧ ¬P)"]:
        f = P.parse(s)
        assert matrix_is_valid(f, LP_MATRIX) is True
        assert _valid_from_thf_text(f, LP_MATRIX) is True


# ===========================================================================
# 5. Entailment: FDE/K3/LP differential battery + the paraconsistency split.
# ===========================================================================
ENTAILMENTS = [
    (["P", "¬P"], "Q"),             # explosion
    (["P", "P → Q"], "Q"),          # modus ponens
    (["P"], "P ∨ Q"),               # addition
    (["P ∧ Q"], "P"),               # simplification
]


@pytest.mark.parametrize("prem_strs,con_str", ENTAILMENTS)
@pytest.mark.parametrize("matrix", MATRICES, ids=lambda m: m.name)
def test_entailment_matches_oracle(prem_strs, con_str, matrix):
    prem = [P.parse(s) for s in prem_strs]
    con = P.parse(con_str)
    assert _entails_from_thf_text(prem, con, matrix) == matrix_entails(prem, con, matrix)


def test_explosion_and_modus_ponens_headline_split():
    p, notp, q = P.parse("P"), P.parse("¬P"), P.parse("Q")
    # Explosion [P, ~P] |= Q:
    #   K3  -- True  (vacuous: P and ~P are never BOTH designated in K3).
    #   LP  -- False (at P="both"=0.5, both premises designated, Q=0.0 not).
    #   FDE -- False (at P="B", both premises designated, Q="F" not) --
    #          FDE is paraconsistent, same headline as LP (verified against
    #          the oracle; test_matrix.py's test_fde_paraconsistent_no_explosion
    #          checks the same fact directly on the matrix layer).
    assert matrix_entails([p, notp], q, K3_MATRIX) is True
    assert matrix_entails([p, notp], q, LP_MATRIX) is False
    assert matrix_entails([p, notp], q, FDE_MATRIX) is False
    for m in MATRICES:
        assert _entails_from_thf_text([p, notp], q, m) == matrix_entails([p, notp], q, m)

    # Modus ponens [P, P -> Q] |= Q:
    #   K3  -- True. The only K3-designated value is 1.0, so P designated
    #          forces P=1.0; P->Q = max(1-P, Q) = max(0, Q) = Q, so P->Q
    #          designated forces Q=1.0 too -- no countermodel exists.
    #   LP  -- False, via the countermodel P=0.5 ("both"), Q=0.0 ("false"):
    #          P is designated (0.5 in {0.5, 1.0}); P->Q = max(1-0.5, 0.0) =
    #          max(0.5, 0.0) = 0.5, ALSO designated; yet Q = 0.0 is not. So
    #          both premises are designated while the conclusion is not --
    #          LP is well known to fail modus ponens despite validating every
    #          classical tautology (the material "->" is not detachable).
    #   FDE -- False, by the FDE analogue of the same shape: at P="B" (both),
    #          P->Q = ~B v Q = B v Q, which is designated even at Q="F"
    #          (B v F = B, and B is designated); Q="F" itself is not.
    pq = P.parse("P → Q")
    assert matrix_entails([p, pq], q, K3_MATRIX) is True
    assert matrix_entails([p, pq], q, LP_MATRIX) is False
    assert matrix_entails([p, pq], q, FDE_MATRIX) is False
    for m in MATRICES:
        assert _entails_from_thf_text([p, pq], q, m) == matrix_entails([p, pq], q, m)


def test_thf_entailment_structure():
    thf = to_thf_matrix_entailment([P.parse("P"), P.parse("¬P")], P.parse("Q"), FDE_MATRIX)
    assert thf.count("conjecture") == 1
    assert "=>" in thf
    assert thf.count("(") == thf.count(")")


def test_isabelle_entailment_structure_branches():
    # K3: explosion ENTAILS -> forall/longrightarrow form.
    val = to_isabelle_matrix_entailment(
        [P.parse("P"), P.parse("¬P")], P.parse("Q"), K3_MATRIX, name="K3_Ent")
    assert val.startswith("theory K3_Ent")
    assert "\\<forall>" in val and "\\<longrightarrow>" in val and "Verdict: ENTAILS" in val
    assert val.rstrip().endswith("end")
    # FDE: explosion DOES NOT ENTAIL -> exists/countermodel form.
    inv = to_isabelle_matrix_entailment(
        [P.parse("P"), P.parse("¬P")], P.parse("Q"), FDE_MATRIX, name="FDE_Ent")
    assert "\\<exists>" in inv and "\\<not> des" in inv and "DOES NOT ENTAIL" in inv
    assert inv.rstrip().endswith("end")


# ===========================================================================
# 6. K3-via-generic: the generic path with NO K3/LP-specific overrides is
#    still a well-formed, loadable-shaped theory/problem, cross-checked
#    against the oracle exactly like the FDE/LP cases above.
# ===========================================================================
def test_k3_via_generic_default_naming_is_well_formed():
    f = P.parse("P → (Q → P)")   # K3-invalid (see BATTERY cross-check above)
    thf = to_thf_matrix(f, K3_MATRIX)   # no overrides: default "t0_0"/"t0_5"/"t1_0" etc.
    assert thf.count("conjecture") == 1
    assert thf.count("(") == thf.count(")")
    assert thf.rstrip().endswith(")).")

    isa = to_isabelle_matrix(f, K3_MATRIX, name="K3_Generic", lemma_name="k3_generic")
    assert isa.startswith("theory K3_Generic")
    assert "lemma k3_generic:" in isa
    assert isa.rstrip().endswith("end")
    # K3-invalid -> refutation form, and it must be a REAL discharge (exists +
    # witness), not a bare simp (the same proof-bug class the K3/LP suite
    # regression-tests for).
    assert matrix_is_valid(f, K3_MATRIX) is False
    assert "\\<exists>" in isa and "rule exI[where x=" in isa


# ===========================================================================
# 7. Rejection surface.
# ===========================================================================
def test_rejects_quantifier():
    f = P.parse("∀x P(x)")
    with pytest.raises(NotImplementedError):
        to_thf_matrix(f, FDE_MATRIX)
    with pytest.raises(NotImplementedError):
        to_isabelle_matrix(f, FDE_MATRIX)


def test_rejects_modal():
    f = MSFLParser(modal=True).parse("□P")
    with pytest.raises(NotImplementedError):
        to_thf_matrix(f, FDE_MATRIX)


def test_rejects_lukasiewicz():
    f = MSFLParser(fuzzy=True).parse("P ⊗ Q")  # StrongConjunction
    with pytest.raises(NotImplementedError):
        to_thf_matrix(f, FDE_MATRIX)


def test_rejects_connective_the_matrix_has_no_table_for():
    # Build a matrix just like K3 but with an EMPTY xor table (simulating a
    # matrix that legitimately does not define exclusive-or).
    no_xor = TruthMatrix(
        name="K3Sub", values=K3_MATRIX.values, designated=K3_MATRIX.designated,
        neg=K3_MATRIX.neg, conj=K3_MATRIX.conj, disj=K3_MATRIX.disj,
        impl=K3_MATRIX.impl, iff=K3_MATRIX.iff, xor={},
    )
    ok_formula = P.parse("P ∧ ¬P")           # no xor used -> fine
    bad_formula = P.parse("P ⊕ Q")           # uses xor -> the matrix can't reify it

    to_thf_matrix(ok_formula, no_xor)        # does not raise
    with pytest.raises(ValueError, match="xor"):
        to_thf_matrix(bad_formula, no_xor)
    with pytest.raises(ValueError, match="xor"):
        to_isabelle_matrix(bad_formula, no_xor)

    # The un-defined op's axioms are simply absent (not emitted as
    # dangling/uninterpreted symbols) from the OK formula's export.
    thf = to_thf_matrix(ok_formula, no_xor)
    assert "mv_xor" not in thf and "xor_decl" not in thf


def test_bad_value_names_key_rejected():
    with pytest.raises(ValueError):
        to_thf_matrix(P.parse("P"), K3_MATRIX, value_names={99.0: "bogus"})


def test_empty_designated_set_rejected():
    empty_des = TruthMatrix(
        name="EmptyDes", values=K3_MATRIX.values, designated=frozenset(),
        neg=K3_MATRIX.neg, conj=K3_MATRIX.conj, disj=K3_MATRIX.disj,
        impl=K3_MATRIX.impl, iff=K3_MATRIX.iff, xor=K3_MATRIX.xor,
    )
    with pytest.raises(ValueError):
        to_thf_matrix(P.parse("P"), empty_des)
    with pytest.raises(ValueError):
        to_isabelle_matrix(P.parse("P"), empty_des)


# ===========================================================================
# 8. Naming knobs: value_names / conn_names overrides and de-collision.
# ===========================================================================
def test_value_names_pin_exact_constant_names_and_order():
    thf = to_thf_matrix(P.parse("P"), FDE_MATRIX,
                        value_names={"B": "one", "T": "two"})  # partial override
    assert "thf(one_decl, type, ( one : tv ))." in thf
    assert "thf(two_decl, type, ( two : tv ))." in thf
    # unnamed values (F, N) still get sensible defaults.
    assert "thf(tF_decl, type, ( tF : tv ))." in thf
    assert "thf(tN_decl, type, ( tN : tv ))." in thf


def test_conn_names_override_applies_to_eval_and_axioms():
    f = P.parse("P ∧ Q")
    thf = to_thf_matrix(f, K3_MATRIX, conn_names={N.And: "myand"})
    assert "myand" in thf
    assert "( myand @" in thf
    # unmapped connectives keep the (collision-safe) default -- neg's axioms
    # are still emitted (every matrix-defined op is axiomatised regardless of
    # what the particular formula uses), just under its default name.
    assert "mv_neg" in thf
    isa = to_isabelle_matrix(f, K3_MATRIX, conn_names={N.And: "myand"})
    assert "myand" in isa


def test_default_connective_names_do_not_shadow_hol_conj_disj():
    # HOL.conj / HOL.disj underlie \<and>/\<or> in Isabelle's prelude (`imports
    # Main`); a bare `fun conj`/`fun disj` would collide with those. The
    # default names must NOT be the bare field names.
    isa = to_isabelle_matrix(P.parse("(P ∧ Q) ∨ ¬P"), K3_MATRIX)
    assert 'fun conj ::' not in isa
    assert 'fun disj ::' not in isa
    assert 'fun mv_conj ::' in isa
    assert 'fun mv_disj ::' in isa


# ===========================================================================
# 9. Optional live check: build one FDE theory with a real Isabelle install.
# ===========================================================================
try:
    from unicode_fol_kit.hol.isabelle_runner import isabelle_available, check_theory
    _HAVE_ISABELLE = isabelle_available()
except Exception:   # pragma: no cover - isabelle_runner should always import
    _HAVE_ISABELLE = False


@pytest.mark.isabelle_live
@pytest.mark.skipif(not _HAVE_ISABELLE, reason="no Isabelle installation found")
def test_fde_theory_loads_in_real_isabelle():
    # FDE has no valid formulas, so this is always the *-exists*-refutation
    # form; the interesting thing being checked is that Isabelle's kernel
    # actually accepts the `rule exI[where x=...], simp` discharge -- the
    # same proof-bug class test_hol_isabelle_nonmodal_live.py regression-tests
    # for the K3/LP export.
    theory = to_isabelle_matrix(P.parse("P ∨ ¬P"), FDE_MATRIX, name="FDE_Live")
    r = check_theory(theory, "FDE_Live", session_timeout=60)
    assert r.ok, f"build failed (exit {r.exit_code}):\n{r.output[-1200:]}"


@pytest.mark.isabelle_live
@pytest.mark.skipif(not _HAVE_ISABELLE, reason="no Isabelle installation found")
def test_fde_entailment_theory_loads_in_real_isabelle():
    # [P, ~P] does NOT entail Q in FDE (paraconsistent) -> countermodel form.
    theory = to_isabelle_matrix_entailment(
        [P.parse("P"), P.parse("¬P")], P.parse("Q"), FDE_MATRIX, name="FDE_Ent_Live")
    r = check_theory(theory, "FDE_Ent_Live", session_timeout=60)
    assert r.ok, f"build failed (exit {r.exit_code}):\n{r.output[-1200:]}"
