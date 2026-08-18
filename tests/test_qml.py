"""Tests for quantified modal logic: per-world-domain Kripke semantics + shallow embeddings.

Three layers, cross-checked against each other:
- the **Kripke evaluator** with per-world domains (``satisfies_modal``) is the ground
  truth; the Barcan / converse-Barcan facts are pinned by hand-built models;
- the **first-order shallow embedding** (``qml_is_valid``, decided by Z3) is checked to
  AGREE with exhaustive small-Kripke-model enumeration over every domain regime — a
  differential test independent of the embedding's own Z3 path;
- the **THF shallow embedding** (``to_thf_modal``) is checked structurally (it is faithful
  by construction, using the same SSE clauses; running it needs Leo-III / Satallax).
"""

from itertools import product, combinations

import pytest

from unicode_fol_kit.fol.msflparser import MSFLParser
from unicode_fol_kit.fol.nodes import (
    Atom, Not, And, Or, Implies, Box, Diamond, Quantifier, Variable,
)
from unicode_fol_kit.semantics.kripke import KripkeModel, satisfies_modal
from unicode_fol_kit import (
    qml_is_valid, qml_equivalent, qml_translate, to_thf_modal, to_isabelle_modal,
    BARCAN, CONVERSE_BARCAN,
)

x = Variable("x")


def A(t):
    return Atom("A", [t])


def EX(f):
    return Quantifier("∃", x, f)


def ALL(f):
    return Quantifier("∀", x, f)


# ---------------------------------------------------------------------------
# Kripke ground truth (per-world domains, actualist quantifiers)
# ---------------------------------------------------------------------------

_REL = {"alethic": {(0, 1)}}
_VAL = {1: {"A(b)"}}


def test_kripke_barcan_ground_truth():
    const = KripkeModel(worlds={0, 1}, relations=_REL, valuation=_VAL, domain={"a", "b"})
    incr = KripkeModel(worlds={0, 1}, relations=_REL, valuation=_VAL,
                       domains={0: {"a"}, 1: {"a", "b"}})
    decr = KripkeModel(worlds={0, 1}, relations=_REL, valuation=_VAL,
                       domains={0: {"a", "b"}, 1: {"a"}})
    # BF (◇∃A → ∃◇A): valid constant & decreasing, fails increasing.
    assert satisfies_modal(BARCAN, const, 0) is True
    assert satisfies_modal(BARCAN, decr, 0) is True
    assert satisfies_modal(BARCAN, incr, 0) is False
    # CBF (∃◇A → ◇∃A): valid constant & increasing, fails decreasing.
    assert satisfies_modal(CONVERSE_BARCAN, const, 0) is True
    assert satisfies_modal(CONVERSE_BARCAN, incr, 0) is True
    assert satisfies_modal(CONVERSE_BARCAN, decr, 0) is False


def test_kripke_propositional_still_works():
    prop = KripkeModel(worlds={0, 1}, relations=_REL, valuation={1: {"P"}})
    assert satisfies_modal(Box(Atom("P", ())), prop, 0) is True


def test_kripke_quantifier_without_domain_errors():
    prop = KripkeModel(worlds={0}, relations={}, valuation={})
    with pytest.raises(ValueError):
        satisfies_modal(ALL(A(x)), prop, 0)


# ---------------------------------------------------------------------------
# FO shallow embedding: Barcan litmus (Z3) — must match the Kripke ground truth
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("formula,mode,expected", [
    (BARCAN, "constant", True), (BARCAN, "increasing", False), (BARCAN, "decreasing", True),
    (CONVERSE_BARCAN, "constant", True), (CONVERSE_BARCAN, "increasing", True),
    (CONVERSE_BARCAN, "decreasing", False),
])
def test_fo_embedding_barcan_litmus(formula, mode, expected):
    assert qml_is_valid(formula, mode=mode, frame="K") is expected


def test_fo_embedding_frame_sensitivity():
    # T axiom □A0 → A0 (nullary A0): valid in T, not in K — regime-independent.
    a0 = Atom("A0", ())
    t_axiom = Implies(Box(a0), a0)
    assert qml_is_valid(t_axiom, mode="constant", frame="T") is True
    assert qml_is_valid(t_axiom, mode="constant", frame="K") is False


def test_fo_embedding_nonempty_domain():
    # ∀x A(x) → ∃x A(x) is valid under the non-empty-local-domain convention, in every
    # regime (every world has at least one existing individual).
    f = Implies(ALL(A(x)), EX(A(x)))
    assert qml_is_valid(f, mode="constant", frame="K") is True
    assert qml_is_valid(f, mode="varying", frame="K") is True


# ---------------------------------------------------------------------------
# Differential: FO embedding (Z3) vs exhaustive Kripke enumeration
# ---------------------------------------------------------------------------

_INDIV = ("a", "b")


def _domain_choices(worlds, rel, regime):
    """Yield per-world domain assignments {w: frozenset} respecting the regime over rel.

    Local domains are required NON-EMPTY (the standard classical-QML convention the
    embedding adopts via its nonempty-local-domain axiom).
    """
    subsets = [frozenset(c) for r in range(1, len(_INDIV) + 1) for c in combinations(_INDIV, r)]
    for assignment in product(subsets, repeat=len(worlds)):
        dom = dict(zip(worlds, assignment))
        ok = True
        for (w, v) in rel:
            if regime == "constant" and dom[w] != dom[v]:
                ok = False
            elif regime == "increasing" and not dom[w] <= dom[v]:
                ok = False
            elif regime == "decreasing" and not dom[v] <= dom[w]:
                ok = False
        if ok:
            yield dom


def _valuations(worlds):
    """Yield per-world valuations of the ground atoms A(a), A(b)."""
    atoms = [f"A({d})" for d in _INDIV]
    cells = [frozenset(c) for r in range(len(atoms) + 1) for c in combinations(atoms, r)]
    for assignment in product(cells, repeat=len(worlds)):
        yield dict(zip(worlds, assignment))


def qml_valid_by_enumeration(formula, regime, max_worlds=2):
    """True iff ``formula`` holds at every world of every small (frame-K) model of the regime."""
    for n in range(1, max_worlds + 1):
        worlds = list(range(n))
        all_edges = [(i, j) for i in worlds for j in worlds]
        for r_mask in product((False, True), repeat=len(all_edges)):
            rel = {e for e, inc in zip(all_edges, r_mask) if inc}
            for dom in _domain_choices(worlds, rel, regime):
                for val in _valuations(worlds):
                    model = KripkeModel(worlds=worlds, relations={"alethic": rel},
                                        valuation=val, domains=dom)
                    if any(not satisfies_modal(formula, model, w) for w in worlds):
                        return False
    return True


_BATTERY = [BARCAN, CONVERSE_BARCAN, Implies(ALL(A(x)), EX(A(x))),
            Implies(Box(ALL(A(x))), ALL(Box(A(x)))),   # CBF□
            Implies(ALL(Box(A(x))), Box(ALL(A(x))))]   # BF□


@pytest.mark.parametrize("regime", ["constant", "increasing", "decreasing", "varying"])
@pytest.mark.parametrize("formula", _BATTERY, ids=lambda f: f.to_unicode_str()[:24])
def test_fo_embedding_matches_kripke_enumeration(formula, regime):
    z3_says = qml_is_valid(formula, mode=regime, frame="K")
    kripke_says = qml_valid_by_enumeration(formula, regime)
    assert z3_says == kripke_says, (
        f"{formula.to_unicode_str()} [{regime}]: Z3={z3_says}, Kripke-enum={kripke_says}")


# ---------------------------------------------------------------------------
# qml_equivalent + translation
# ---------------------------------------------------------------------------

def test_qml_equivalent():
    # □(A0 ∧ B0) ≡ □A0 ∧ □B0 holds in K.
    a0, b0 = Atom("A0", ()), Atom("B0", ())
    assert qml_equivalent(Box(And(a0, b0)), And(Box(a0), Box(b0)), frame="K") is True
    # ◇∃A and ∃◇A are NOT equivalent under varying domains.
    assert qml_equivalent(Diamond(EX(A(x))), EX(Diamond(A(x))), mode="varying") is False


def test_qml_translate_is_classical_fo():
    # The translation is a plain FOL node (no modal/quantified-modal nodes left) → exports.
    fo = qml_translate(Box(A(Variable("c"))), mode="constant")
    fo.to_z3()  # must not raise — it is classical FOL


# ---------------------------------------------------------------------------
# Variable capture: an object variable spelled like the world parameter ("w")
# must NOT be captured by the appended world argument (regression).
# ---------------------------------------------------------------------------

def _bf_with(varname):
    z = Variable(varname)
    a = lambda t: Atom("A", [t])
    return Implies(Diamond(Quantifier("∃", z, a(z))),
                   Quantifier("∃", z, Diamond(a(z))))


def _cbf_with(varname):
    z = Variable(varname)
    a = lambda t: Atom("A", [t])
    return Implies(Quantifier("∃", z, Diamond(a(z))),
                   Diamond(Quantifier("∃", z, a(z))))


def test_translate_no_world_capture():
    # ∃w A(w): the appended world must be a FRESH variable, not the bound object w,
    # i.e. the atom is A(w, <fresh>) — never the collapsed A(w, w).
    w = Variable("w")
    tr = qml_translate(Quantifier("∃", w, A(w)), mode="constant", world="w")
    atoms = [n for n in tr.walk() if isinstance(n, Atom) and n.predicate == "A"]
    assert atoms, "expected the translated A atom"
    a = atoms[0]
    assert len(a.args) == 2 and a.args[0].name == "w"
    assert a.args[1].name != "w", f"world arg captured by object var: {a.to_unicode_str()}"


@pytest.mark.parametrize("mode", ["constant", "increasing", "decreasing", "varying"])
@pytest.mark.parametrize("build", [_bf_with, _cbf_with], ids=["BF", "CBF"])
def test_validity_invariant_under_bound_var_rename(mode, build):
    # Validity must not depend on the SPELLING of the bound object variable; in
    # particular spelling it "w" (the default world name) must agree with "x".
    assert qml_is_valid(build("x"), mode=mode, frame="K") == \
           qml_is_valid(build("w"), mode=mode, frame="K")


# ---------------------------------------------------------------------------
# Input validation: an unknown / mis-capitalised mode must NOT be silently
# reinterpreted as constant-domain (which would give a wrong validity verdict).
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("bad", ["Increasing", "incr", "bogus", "Constant", ""])
def test_unknown_mode_raises(bad):
    with pytest.raises(ValueError):
        qml_is_valid(BARCAN, mode=bad, frame="K")
    with pytest.raises(ValueError):
        qml_translate(BARCAN, mode=bad)


def test_known_modes_accepted():
    # every documented mode is accepted on the FO path (no exception).
    for mode in ("constant", "possibilist", "varying", "increasing", "cumulative", "decreasing"):
        qml_is_valid(Implies(ALL(A(x)), EX(A(x))), mode=mode, frame="K")


# ---------------------------------------------------------------------------
# THF possibilist must match the FO embedding: possibilist ≡ constant domain,
# so the export carries const_dom (not a bare varying domain).
# ---------------------------------------------------------------------------

def test_thf_possibilist_emits_const_dom():
    # FO treats possibilist as constant (BF valid); the THF export must agree by
    # emitting const_dom, else its actualist mforall/mexists would model varying.
    assert qml_is_valid(BARCAN, mode="possibilist", frame="K") is True
    thf = to_thf_modal(BARCAN, mode="possibilist", frame="K")
    assert "const_dom" in thf


def test_thf_equality_is_uninterpreted_predicate():
    # `=` / `≠` must be emitted as ordinary uninterpreted world-relativized predicates
    # (NOT primitive HOL identity), so the THF export agrees with satisfies_modal and
    # the FO embedding: `∀x. x=x` is NOT valid (= is keyed, not identity).
    eq = Atom("=", [Variable("x"), Variable("x")])
    phi = Quantifier("∀", Variable("x"), eq)
    thf = to_thf_modal(phi, "constant", "K")
    assert "feq" in thf and "feq_decl" in thf      # declared as a predicate
    assert "X = X" not in thf and " != " not in thf  # no primitive identity
    # all three layers agree it is NOT valid:
    m = KripkeModel({"w"}, domain=["a", "b"], valuation={"w": set()})
    assert satisfies_modal(phi, m, "w") is False
    assert qml_is_valid(phi, mode="constant", frame="K") is False
    # ≠ maps to its own distinct uninterpreted functor.
    thf_ne = to_thf_modal(Atom("≠", [Variable("x"), Variable("y")]), "constant", "K")
    assert "fneq" in thf_ne


def test_thf_distinct_predicates_not_collapsed():
    # Distinct predicates that sanitise to the same functor (Ab / ab) must get DISTINCT
    # functors — otherwise the non-valid □Ab → □ab would emit as the tautology □ab → □ab
    # (a soundness hole). Regression.
    import re
    thf = to_thf_modal(Implies(Box(Atom("Ab", [])), Box(Atom("ab", []))), "constant", "K")
    assert "( mbox @ ab ) @ ( mbox @ ab )" not in thf       # not collapsed to a tautology
    ab_decls = re.findall(r"thf\((ab\w*)_decl, type", thf)
    assert len(ab_decls) == 2 and len(set(ab_decls)) == 2   # two distinct decls


def test_thf_predicate_two_arities_distinct_functors():
    # A predicate name used at two arities is two distinct symbols: each gets its own,
    # correctly-typed declaration (else the THF would be ill-typed). Regression.
    f = And(Atom("P", [Variable("x")]), Atom("P", [Variable("x"), Variable("y")]))
    thf = to_thf_modal(f, "constant", "K")
    assert "( p : ( $i > mu > $o ) )" in thf
    assert "( p_2 : ( $i > $i > mu > $o ) )" in thf


# ---------------------------------------------------------------------------
# THF / Isabelle export (structural; running needs an external HOL prover)
# ---------------------------------------------------------------------------

def test_thf_export_structure():
    thf = to_thf_modal(BARCAN, mode="constant", frame="T")
    assert thf.count("(") == thf.count(")")
    for block in ("thf(mu_type", "thf(mbox", "thf(mdia", "thf(mforall", "thf(mexists",
                  "thf(mvalid", "thf(refl", "thf(const_dom", "thf(goal, conjecture"):
        assert block in thf, block
    # the Barcan conjecture applies mdia / mexists (it has no ∀)
    assert "mdia @" in thf and "mexists @" in thf and "mvalid @" in thf


def test_thf_domain_axiom_per_mode():
    assert "const_dom" in to_thf_modal(BARCAN, "constant")
    assert "cumulative_dom" in to_thf_modal(BARCAN, "increasing")
    assert "decreasing_dom" in to_thf_modal(BARCAN, "decreasing")


def test_isabelle_export_smoke():
    out = to_isabelle_modal(BARCAN, "constant", "T")
    assert "typedecl i" in out and "mbox" in out


def test_qml_exports():
    import unicode_fol_kit as u
    for name in ("qml_translate", "qml_is_valid", "qml_equivalent",
                 "to_thf_modal", "to_isabelle_modal", "BARCAN", "CONVERSE_BARCAN"):
        assert hasattr(u, name) and name in u.__all__, name


# ---------------------------------------------------------------------------
# Non-ASCII / digit-leading identifiers reaching the modal THF/Isabelle
# exporters (fol.qml._thf_name / _ThfNames.variable and
# hol.isabelle_modal._safe_name / _IsaNames.variable). These now
# transliterate via constant_name_to_ascii and digit-guard their result --
# mirroring the classical to_tptp()/to_prover9() fix for the same widened
# grammar -- but until this regression suite existed, nothing exercised a
# non-ASCII or digit-leading name through EITHER modal exporter: every
# to_thf_modal/to_isabelle_modal call anywhere else in the suite uses plain
# ASCII, letter-initial predicate/constant names.
# ---------------------------------------------------------------------------

_MODAL_PARSE = MSFLParser(modal=True).parse


def test_thf_non_ascii_predicate_and_constants_are_ascii_legal():
    f = _MODAL_PARSE("□ Świątek(świątek, 2008SummerOlympics)")
    thf = to_thf_modal(f, "constant", "K")
    assert thf.isascii()
    assert thf.count("(") == thf.count(")")
    # the transliterated, digit-guarded tokens must actually appear -- hand
    # computed from constant_name_to_ascii("Świątek")/("świątek") plus the
    # 'p'-digit-guard _thf_name applies.
    assert "u015awiu0105tek" in thf      # Świątek (predicate)
    assert "u015bwiu0105tek" in thf      # świątek (constant)
    assert "p2008SummerOlympics" in thf  # digit-leading -> 'p'-prefixed
    # no raw non-ASCII character or a bare digit-leading identifier survives.
    assert "Świątek" not in thf and "świątek" not in thf
    assert "thf(2008SummerOlympics_decl" not in thf


def test_thf_non_ascii_variable_is_ascii_legal_and_deduped():
    # A bound variable whose name is itself non-ASCII (reachable the same
    # widened-grammar way a predicate/constant name is, and directly
    # constructible regardless) must come out as an ASCII, upper-cased THF
    # variable token too (_ThfNames.variable), not the raw Unicode letter
    # merely upper-cased.
    v = Variable("świątek")
    f = Quantifier("∀", v, Atom("Above", [v]))
    thf = to_thf_modal(f, "constant", "K")
    assert thf.isascii()
    assert "U015BWIU0105TEK" in thf
    assert "ŚWIĄTEK" not in thf


def test_isabelle_non_ascii_predicate_and_constants_are_ascii_legal():
    f = _MODAL_PARSE("□ Świątek(świątek, 2008SummerOlympics)")
    isa = to_isabelle_modal(f, mode="constant", frame="K")
    consts_lines = [ln for ln in isa.splitlines() if ln.startswith("consts")]
    lemma_lines = [ln for ln in isa.splitlines() if ln.startswith("lemma")]
    assert all(ln.isascii() for ln in consts_lines + lemma_lines)
    assert any("u015awiu0105tek" in ln for ln in consts_lines)       # Świątek
    assert any("u015bwiu0105tek" in ln for ln in consts_lines)       # świątek
    assert any("c_2008SummerOlympics" in ln for ln in consts_lines)  # digit-leading -> 'c_'-prefixed
    assert not any("Świątek" in ln or "świątek" in ln
                  for ln in consts_lines + lemma_lines)
