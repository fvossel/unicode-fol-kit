"""Tests for the K3/LP three-valued -> HOL export (unicode_fol_kit.hol.manyvalued).

The export emits a many-valued shallow embedding (THF problem / Isabelle theory)
whose theorem-hood encodes K3 / LP propositional validity (and, for the
entailment variants, K3/LP entailment). These tests assert:

  * structural well-formedness of the emitted artifacts (declarations, the
    three-valued type, the exhaustiveness/distinctness axioms, the conjecture);
  * that the emitted strong-Kleene truth tables are byte-faithful to the
    toolkit's own evaluator (unicode_fol_kit.semantics.manyvalued.kleene_value)
    on EVERY truth-table cell; and
  * that validity / entailment decided *purely from the emitted text's axioms*
    agrees with manyvalued.is_valid / manyvalued.entails on a hand-checked
    battery — i.e. the emitted HOL problem is semantically faithful (modulo a
    sound+complete HOL prover, which the toolkit does not run).
"""
import re
from itertools import product

import pytest

from unicode_fol_kit.fol.msflparser import MSFLParser
from unicode_fol_kit.fol import nodes as N
from unicode_fol_kit.semantics import manyvalued as MV
from unicode_fol_kit.hol.manyvalued import (
    to_thf_k3lp, to_isabelle_k3lp,
    to_thf_k3lp_entailment, to_isabelle_k3lp_entailment,
    SYSTEMS,
)

P = MSFLParser()
TV_FROM_NAME = {"tT": 1.0, "tB": 0.5, "tF": 0.0}
VALUES = (0.0, 0.5, 1.0)


# ---------------------------------------------------------------------------
# Helpers: read the emitted THF text's semantics back out and decide with it.
# ---------------------------------------------------------------------------
def _parse_thf_semantics(thf: str):
    """Recover (neg-table, {op: table}, designated-set) from emitted THF text."""
    neg = {}
    for m in re.finditer(r"\( kneg @ (\w+) \) = (\w+)", thf):
        neg[TV_FROM_NAME[m.group(1)]] = TV_FROM_NAME[m.group(2)]
    bins = {op: {} for op in ("kand", "kor", "kimp", "kiff", "kxor")}
    for op in bins:
        for m in re.finditer(rf"\( {op} @ (\w+) @ (\w+) \) = (\w+)", thf):
            key = (TV_FROM_NAME[m.group(1)], TV_FROM_NAME[m.group(2)])
            bins[op][key] = TV_FROM_NAME[m.group(3)]
    des = {1.0, 0.5} if "( D = tT ) | ( D = tB )" in thf else {1.0}
    return neg, bins, des


_BINMAP = {N.And: "kand", N.Or: "kor", N.Xor: "kxor",
           N.Implies: "kimp", N.Iff: "kiff"}


def _eval_with(neg, bins, node, asg):
    if isinstance(node, N.Atom):
        return asg[node.to_unicode_str()]
    if isinstance(node, N.Not):
        return neg[_eval_with(neg, bins, node.formula, asg)]
    for cls, op in _BINMAP.items():
        if isinstance(node, cls):
            return bins[op][(_eval_with(neg, bins, node.left, asg),
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


def _valid_from_thf_text(formula, system):
    """Decide validity using ONLY the axioms read out of the emitted THF text."""
    neg, bins, des = _parse_thf_semantics(to_thf_k3lp(formula, system))
    assert len(neg) == 3
    for op in bins:
        assert len(bins[op]) == 9, op
    keys = _atom_keys(formula)
    for combo in product(VALUES, repeat=len(keys)):
        asg = dict(zip(keys, combo))
        if _eval_with(neg, bins, formula, asg) not in des:
            return False
    return True


def _entails_from_thf_text(premises, conclusion, system):
    neg, bins, des = _parse_thf_semantics(
        to_thf_k3lp_entailment(premises, conclusion, system))
    keys = _atom_keys(*premises, conclusion)
    for combo in product(VALUES, repeat=len(keys)):
        asg = dict(zip(keys, combo))
        if all(_eval_with(neg, bins, p, asg) in des for p in premises):
            if _eval_with(neg, bins, conclusion, asg) not in des:
                return False
    return True


# ---------------------------------------------------------------------------
# A hand-checked battery of propositional formulas.
# ---------------------------------------------------------------------------
BATTERY = [
    "P",
    "P ∨ ¬P",                       # law of excluded middle
    "(P ∧ ¬P) → Q",                 # explosion as an implication
    "P → P",
    "P → (Q → P)",
    "(P ∧ Q) → P",
    "¬¬P → P",
    "P → ¬¬P",
    "¬(P ∧ ¬P)",                    # non-contradiction
    "P ↔ P",
    "(P → Q) ↔ (¬Q → ¬P)",          # contraposition
    "P ⊕ ¬P",
    "((P → Q) ∧ (Q → R)) → (P → R)",  # hypothetical syllogism
    "P ∨ Q ∨ ¬P",
    "(P ∨ Q) ↔ (Q ∨ P)",
]


# ===========================================================================
# 1. Emitted truth tables are byte-faithful to the toolkit's evaluator.
# ===========================================================================
@pytest.mark.parametrize("system", SYSTEMS)
def test_emitted_unary_table_matches_kleene(system):
    p = N.Atom("P", [])
    neg, _, _ = _parse_thf_semantics(to_thf_k3lp(p, system))
    for v in VALUES:
        assert neg[v] == MV.kleene_value(N.Not(p), {"P": v})


@pytest.mark.parametrize("system", SYSTEMS)
@pytest.mark.parametrize("cls,op", list(_BINMAP.items()))
def test_emitted_binary_tables_match_kleene(system, cls, op):
    p, q = N.Atom("P", []), N.Atom("Q", [])
    _, bins, _ = _parse_thf_semantics(to_thf_k3lp(cls(p, q), system))
    for a in VALUES:
        for b in VALUES:
            assert bins[op][(a, b)] == MV.kleene_value(cls(p, q), {"P": a, "Q": b}), (op, a, b)


@pytest.mark.parametrize("system,expected", [("K3", {1.0}), ("LP", {1.0, 0.5})])
def test_designated_set(system, expected):
    _, _, des = _parse_thf_semantics(to_thf_k3lp(N.Atom("P", []), system))
    assert des == expected


# ===========================================================================
# 2. Validity decided FROM THE EMITTED TEXT == the toolkit's decision procedure.
# ===========================================================================
@pytest.mark.parametrize("formula_str", BATTERY)
@pytest.mark.parametrize("system", SYSTEMS)
def test_thf_validity_matches_toolkit(formula_str, system):
    f = P.parse(formula_str)
    assert _valid_from_thf_text(f, system) == MV.is_valid(f, system)


# ===========================================================================
# 3. The verified headline contrasts (these were hypotheses to CHECK).
# ===========================================================================
def test_k3_has_no_tautologies():
    # Assigning every atom B makes any formula B, which is NOT K3-designated, so
    # NO propositional formula is K3-valid — LEM, explosion, even P → P.
    for s in ["P ∨ ¬P", "(P ∧ ¬P) → Q", "P → P", "¬(P ∧ ¬P)"]:
        f = P.parse(s)
        assert MV.is_valid(f, "K3") is False
        assert _valid_from_thf_text(f, "K3") is False


def test_lp_validates_classical_tautologies():
    # LP designates B, so every classical tautology is LP-valid.
    for s in ["P ∨ ¬P", "(P ∧ ¬P) → Q", "P → P", "¬(P ∧ ¬P)"]:
        f = P.parse(s)
        assert MV.is_valid(f, "LP") is True
        assert _valid_from_thf_text(f, "LP") is True


def test_bare_atom_invalid_in_both():
    f = P.parse("P")
    for system in SYSTEMS:
        assert MV.is_valid(f, system) is False
        assert _valid_from_thf_text(f, system) is False


# ===========================================================================
# 4. Entailment exports: faithful to manyvalued.entails; the paraconsistency split.
# ===========================================================================
ENTAILMENTS = [
    (["P", "¬P"], "Q"),            # explosion
    (["P", "P → Q"], "Q"),         # modus ponens
    (["P"], "P ∨ Q"),              # addition
    (["P ∧ Q"], "P"),              # simplification
    (["P → Q", "Q → R"], "P → R"),  # hypothetical syllogism
]


@pytest.mark.parametrize("prem_strs,con_str", ENTAILMENTS)
@pytest.mark.parametrize("system", SYSTEMS)
def test_entailment_matches_toolkit(prem_strs, con_str, system):
    prem = [P.parse(s) for s in prem_strs]
    con = P.parse(con_str)
    assert _entails_from_thf_text(prem, con, system) == MV.entails(prem, con, system)


def test_explosion_paraconsistency_split():
    prem = [P.parse("P"), P.parse("¬P")]
    con = P.parse("Q")
    # K3: explosion is valid (vacuous — premises never jointly designated).
    assert MV.entails(prem, con, "K3") is True
    assert _entails_from_thf_text(prem, con, "K3") is True
    # LP: explosion FAILS (P = B designates both premises yet Q = F is not).
    assert MV.entails(prem, con, "LP") is False
    assert _entails_from_thf_text(prem, con, "LP") is False


# ===========================================================================
# 5. Structural well-formedness of the emitted artifacts.
# ===========================================================================
@pytest.mark.parametrize("system", SYSTEMS)
def test_thf_structure(system):
    thf = to_thf_k3lp(P.parse("P ∨ ¬P"), system)
    # the three-valued type, its constants, distinctness + exhaustiveness.
    assert "thf(tv_type, type, ( tv : $tType ))." in thf
    for c in ("tT", "tB", "tF"):
        assert f"thf({c}_decl, type, ( {c} : tv ))." in thf
    assert "tv_distinct" in thf and "tv_exhaust" in thf
    # one conjecture, balanced parens, ends cleanly.
    assert thf.count("conjecture") == 1
    assert thf.count("(") == thf.count(")")
    assert thf.rstrip().endswith(")).")
    # the universally-quantified valuation variable for the atom P.
    assert re.search(r"! \[V_P: tv\] : \( des @", thf)


@pytest.mark.parametrize("system", SYSTEMS)
def test_isabelle_structure(system):
    isa = to_isabelle_k3lp(P.parse("(P ∧ ¬P) → Q"), system)
    assert isa.startswith("theory K3LP_Validity")
    assert isa.rstrip().endswith("end")
    assert "datatype tv = tT | tB | tF" in isa
    assert "lemma k3lp_validity:" in isa
    # all five binary connective funs and kneg are defined.
    for fn in ("kneg", "kand", "kor", "kimp", "kiff", "kxor"):
        assert f" {fn} " in isa or isa.count(fn) >= 1
    # designated definition reflects the system.
    if system == "K3":
        assert "des d \\<equiv> (d = tT)" in isa
    else:
        assert "des d \\<equiv> (d = tT \\<or> d = tB)" in isa


def test_isabelle_entailment_structure_valid():
    # explosion is K3-valid -> the lemma is the entailment (\<longrightarrow>).
    isa = to_isabelle_k3lp_entailment([P.parse("P"), P.parse("¬P")], P.parse("Q"), "K3")
    assert isa.startswith("theory K3LP_Entailment")
    assert "lemma k3lp_entailment:" in isa
    assert "\\<forall>" in isa and "\\<longrightarrow>" in isa
    assert "Verdict: ENTAILS" in isa
    assert isa.rstrip().endswith("end")


def test_isabelle_entailment_structure_invalid():
    # explosion is LP-invalid -> the lemma is a countermodel (\<exists> ... \<not>).
    isa = to_isabelle_k3lp_entailment([P.parse("P"), P.parse("¬P")], P.parse("Q"), "LP")
    assert "\\<exists>" in isa and "\\<not> des" in isa
    assert "DOES NOT ENTAIL" in isa
    assert isa.rstrip().endswith("end")


def test_isabelle_validity_branches():
    # LEM: K3-invalid (refutation form), LP-valid (validity form).
    k3 = to_isabelle_k3lp(P.parse("P ∨ ¬P"), "K3")
    assert "\\<exists>" in k3 and "\\<not> des" in k3 and "INVALID" in k3
    lp = to_isabelle_k3lp(P.parse("P ∨ ¬P"), "LP")
    assert "\\<forall>" in lp and "Verdict: VALID" in lp


def test_isabelle_proof_discharges_not_bare_simp():
    # A bare `by (simp add: des_def)` does NOT close these goals (simp cannot
    # reduce `kneg v` while v is abstract). The fixed emitter discharges the
    # \<forall> form by exhausting the tv cases and the \<exists> form with an
    # exI witness. (The proofs are actually run in test_hol_isabelle_*_live.py.)
    lp = to_isabelle_k3lp(P.parse("P ∨ ¬P"), "LP")          # valid -> forall
    assert "intro allI" in lp and "case_tac" in lp and "simp_all add: des_def" in lp
    k3 = to_isabelle_k3lp(P.parse("P ∨ ¬P"), "K3")          # invalid -> exists
    assert "rule exI[where x=" in k3
    # entailment forms use the same discharge machinery.
    val = to_isabelle_k3lp_entailment([P.parse("P"), P.parse("¬P")], P.parse("Q"), "K3")
    assert "intro allI" in val and "case_tac" in val
    inv = to_isabelle_k3lp_entailment([P.parse("P"), P.parse("¬P")], P.parse("Q"), "LP")
    assert "rule exI[where x=" in inv


def test_thf_entailment_structure():
    thf = to_thf_k3lp_entailment([P.parse("P"), P.parse("¬P")], P.parse("Q"), "K3")
    assert thf.count("conjecture") == 1
    assert "=>" in thf  # premises => conclusion
    assert thf.count("(") == thf.count(")")


# ===========================================================================
# 6. Rejection surface: only the propositional fragment is in scope.
# ===========================================================================
def test_rejects_quantifier():
    f = P.parse("∀x P(x)")
    with pytest.raises(NotImplementedError):
        to_thf_k3lp(f)
    with pytest.raises(NotImplementedError):
        to_isabelle_k3lp(f)


def test_rejects_modal():
    f = MSFLParser(modal=True).parse("□P")
    with pytest.raises(NotImplementedError):
        to_thf_k3lp(f)


def test_rejects_lukasiewicz():
    f = MSFLParser(fuzzy=True).parse("P ⊗ Q")  # StrongConjunction
    with pytest.raises(NotImplementedError):
        to_thf_k3lp(f)


def test_rejects_unknown_system():
    with pytest.raises(ValueError):
        to_thf_k3lp(P.parse("P"), system="K4")
    with pytest.raises(ValueError):
        to_isabelle_k3lp(P.parse("P"), system="foo")


# ===========================================================================
# 7. Atom keys with arguments get distinct, collision-free valuation variables.
# ===========================================================================
def test_predicate_atoms_distinct_variables():
    f = P.parse("P(a) ∨ ¬P(b)")  # two distinct ground atoms P(a), P(b)
    thf = to_thf_k3lp(f, "K3")
    # both atoms are bound as distinct tv valuation variables in the conjecture.
    goal = [ln for ln in thf.splitlines() if ln.startswith("thf(goal,")][0]
    binder = re.search(r"! \[([^\]]+)\] : \( des @", goal).group(1)
    var_names = [v.split(":")[0].strip() for v in binder.split(",")]
    assert len(var_names) == 2 and len(set(var_names)) == 2
