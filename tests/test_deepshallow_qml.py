"""Deep + maximal/minimal shallow QML embedding with faithfulness proofs — Tier 2:
K frame, constant domain, alethic ``□``/``◇`` only.

Structure tests (always run) pin the emitted theory text, the AST -> deep de
Bruijn encoder, and the refusal of everything outside this fragment's scope.
The battery test (always run, no Isabelle) cross-checks HAND-WORKED validity
verdicts against two independent routes: ``fol.qml.qml_is_valid`` (Z3, constant
domain, frame K) and a brute-force scan of every small constant-domain K Kripke
model (1-2 worlds, 1-2 objects) through ``semantics.kripke.satisfies_modal``.
The live tests are gated on a real Isabelle/HOL install: they actually build the
emitted theory, so exit 0 certifies that Isabelle's kernel discharged all five
faithfulness theorems (faithful1a/1b/2/3, sound_min) and that a grounded
``definition example :: qml`` type-checks — NOT that any battery formula's own
True/False verdict is Isabelle-certified (no lemma about ``validD example`` is
ever emitted). That two-way verdict cross-check is entirely between the Z3 and
brute-force-Kripke routes above; Isabelle's contribution is embedding
faithfulness plus type-checking, a distinct and narrower guarantee.
"""

import itertools
import re

import pytest

from unicode_fol_kit.fol.nodes import (
    Atom, Not, And, Or, Xor, Implies, Iff, Box, Diamond, Variable, Constant,
    Quantifier, Knows, Always, Function, Number,
    Obligatory, Permitted, Nominal, At, SortedQuantifier, SortedConstant,
)
from unicode_fol_kit.fol.qml import qml_is_valid, BARCAN, CONVERSE_BARCAN
from unicode_fol_kit.semantics.kripke import KripkeModel, satisfies_modal
from unicode_fol_kit.hol.deepshallow.qml import (
    qml_to_deep, qml_deep_faithfulness_theory, _QML_BODY,
)
from unicode_fol_kit.hol.deepshallow._common import AtomConsts, sanitize_atom, wrap_theory
from unicode_fol_kit.hol.isabelle_runner import isabelle_available, check_theory

x = Variable("x")
A = lambda t: Atom("A", [t])
B = lambda t: Atom("B", [t])
P = Atom("P", [])
c = Constant("c")

FORALL, EXISTS = "∀", "∃"


def _shared_consts(atoms: AtomConsts) -> AtomConsts:
    """Object-constant resolver sharing ``atoms``'s de-collision pool.

    ``consts`` is a required argument of ``qml_to_deep`` (no silent
    auto-create — see that function's docstring for why); this is the
    pool-sharing pattern every caller, including this test file and
    ``qml_deep_faithfulness_theory`` itself, follows by hand.
    """
    consts = AtomConsts()
    consts._used = atoms._used
    return consts

# --------------------------------------------------------------------------- #
# The curated battery (spec: Barcan pair, ∀x□P(x)→□∀xP(x) and its converse, a
# couple of nested quantifier/modality schemas, a formula with a constant, a
# K-invalid formula). Every expected value below is HAND-WORKED, not derived
# from any of the three routes it is checked against.
# --------------------------------------------------------------------------- #

# BF (◇∃/∃◇ form): ◇∃x A(x) → ∃x ◇A(x). Valid whenever the domain does not grow
# along R (constant/decreasing) — under a CONSTANT domain this is a theorem of
# plain K, no frame conditions needed: if some accessible world has an
# A-witness, that same individual (same domain everywhere) IS the witness that
# makes ∃x◇A(x) hold at the current world.
_BARCAN_EXPECTED = True

# CBF (∃◇/◇∃ form): ∃x ◇A(x) → ◇∃x A(x). Valid whenever the domain does not
# shrink (increasing/constant) — again a plain theorem under constant domain:
# whichever individual witnesses ◇A(x), THAT witness (existing everywhere)
# witnesses ◇∃xA(x) too.
_CONVERSE_BARCAN_EXPECTED = True

# NESTED_CBF (∀/□ form of CBF): □∀x A(x) → ∀x □A(x). If ∀xA(x) holds at every
# R-successor, then in particular A(d) holds at every R-successor for each
# FIXED d in the (constant) domain — i.e. □A(d) — for every d, i.e. ∀x□A(x).
# A theorem of plain K under constant domain; no frame condition needed.
NESTED_CBF = Implies(Box(Quantifier(FORALL, x, A(x))), Quantifier(FORALL, x, Box(A(x))))
_NESTED_CBF_EXPECTED = True

# NESTED_BF (∀/□ form of BF): ∀x □A(x) → □∀x A(x). If EVERY d in the (constant,
# so same at every world) domain has A(d) at every R-successor, then at each
# R-successor A(d) holds for every d, i.e. ∀xA(x) there, i.e. □∀xA(x). Also a
# theorem under constant domain (this is exactly the direction that FAILS under
# an increasing/varying domain — see the varying-domain sanity check below).
NESTED_BF = Implies(Quantifier(FORALL, x, Box(A(x))), Box(Quantifier(FORALL, x, A(x))))
_NESTED_BF_EXPECTED = True

# K-invalid: ◇P → □P has no reason to hold over an arbitrary (non-functional)
# K frame — a world with two DIFFERENT-valued successors refutes it: ◇P holds
# via the P-successor, □P fails via the ¬P one.
K_INVALID = Implies(Diamond(P), Box(P))
_K_INVALID_EXPECTED = False

# A ground (quantifier-free) formula naming a constant: the K axiom itself,
# instantiated at the rigid constant c. Valid in EVERY K frame (no quantifiers,
# no domain regime involved at all): □(A(c)→B(c)) ∧ □A(c) ⊢ □B(c) by
# distributing □ over the successors and applying modus ponens pointwise.
K_CONST = Implies(Box(Implies(A(c), B(c))), Implies(Box(A(c)), Box(B(c))))
_K_CONST_EXPECTED = True

# Quantifier/modality nesting, invalid: ∀x(A(x) → ◇A(x)) fails at a DEAD END
# (a world with no R-successors at all): ◇A(d) is vacuously false there for
# every d, while A(d) can be true for some d in the (non-empty) domain.
DEAD_END_INVALID = Quantifier(FORALL, x, Implies(A(x), Diamond(A(x))))
_DEAD_END_INVALID_EXPECTED = False

BATTERY = [
    ("BARCAN", BARCAN, _BARCAN_EXPECTED),
    ("CONVERSE_BARCAN", CONVERSE_BARCAN, _CONVERSE_BARCAN_EXPECTED),
    ("NESTED_CBF", NESTED_CBF, _NESTED_CBF_EXPECTED),
    ("NESTED_BF", NESTED_BF, _NESTED_BF_EXPECTED),
    ("K_INVALID", K_INVALID, _K_INVALID_EXPECTED),
    ("K_CONST", K_CONST, _K_CONST_EXPECTED),
    ("DEAD_END_INVALID", DEAD_END_INVALID, _DEAD_END_INVALID_EXPECTED),
]

# Formulas that use an object quantifier (need domain(s) to brute-force); the
# two ground formulas (K_INVALID, K_CONST) are checked separately below since
# an empty/irrelevant domain suffices for them.
_QUANTIFIED_BATTERY = [(n, f, e) for n, f, e in BATTERY
                       if n not in ("K_INVALID", "K_CONST")]


def _all_relations(worlds):
    pairs = [(w, v) for w in worlds for v in worlds]
    for bits in itertools.product((0, 1), repeat=len(pairs)):
        yield {pairs[i] for i in range(len(pairs)) if bits[i]}


def _all_valuations(worlds, keys):
    for bits in itertools.product((0, 1), repeat=len(keys) * len(worlds)):
        val, idx = {}, 0
        for w in worlds:
            true_keys = set()
            for k in keys:
                if bits[idx]:
                    true_keys.add(k)
                idx += 1
            val[w] = true_keys
        yield val


def _brute_force_valid_quantified(formula, n_worlds, n_objs):
    """True iff ``formula`` holds at every world of EVERY small constant-domain
    K model with ``n_worlds`` worlds and an ``n_objs``-element domain (unary
    predicates A/B over the objects). Exhaustive over relations and valuations."""
    worlds = list(range(n_worlds))
    objs = [f"o{i}" for i in range(n_objs)]
    keys = [f"{pred}({o})" for pred in ("A", "B") for o in objs]
    for R in _all_relations(worlds):
        for val in _all_valuations(worlds, keys):
            model = KripkeModel(worlds, relations={"alethic": R}, valuation=val, domain=objs)
            if not all(satisfies_modal(formula, model, w0) for w0 in worlds):
                return False
    return True


def _brute_force_valid_ground(formula, n_worlds, keys):
    """Like above but for a quantifier-free formula: no domain needed at all."""
    worlds = list(range(n_worlds))
    for R in _all_relations(worlds):
        for val in _all_valuations(worlds, keys):
            model = KripkeModel(worlds, relations={"alethic": R}, valuation=val, domain=[])
            if not all(satisfies_modal(formula, model, w0) for w0 in worlds):
                return False
    return True


# --------------------------------------------------------------------------- #
# Route 1 vs the hand-worked expectation: fol.qml.qml_is_valid (Z3).
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("name, formula, expected", BATTERY)
def test_z3_route_matches_hand_worked_expectation(name, formula, expected):
    assert qml_is_valid(formula, mode="constant", frame="K") is expected, name


# --------------------------------------------------------------------------- #
# Route 2 vs the hand-worked expectation: brute-force satisfies_modal over
# every small (1-2 worlds, 1-2 objects) constant-domain K model.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("name, formula, expected", _QUANTIFIED_BATTERY)
@pytest.mark.parametrize("n_worlds", [1, 2])
@pytest.mark.parametrize("n_objs", [1, 2])
def test_brute_force_kripke_matches_hand_worked_expectation(
    name, formula, expected, n_worlds, n_objs):
    assert _brute_force_valid_quantified(formula, n_worlds, n_objs) is expected, \
        f"{name} worlds={n_worlds} objs={n_objs}"


@pytest.mark.parametrize("n_worlds, expected", [
    # A single-world model can never refute ◇P→□P: with no self-loop both
    # sides are vacuously true, and with a self-loop both sides reduce to the
    # SAME fact P(w0) — a genuine countermodel needs at least two worlds
    # (one P-successor, one ¬P-successor), matching K_INVALID's invalidity.
    (1, True),
    (2, _K_INVALID_EXPECTED),
])
def test_brute_force_kripke_k_invalid(n_worlds, expected):
    assert _brute_force_valid_ground(K_INVALID, n_worlds, ["P"]) is expected


@pytest.mark.parametrize("n_worlds", [1, 2])
def test_brute_force_kripke_k_const(n_worlds):
    keys = [f"A({c.to_unicode_str()})", f"B({c.to_unicode_str()})"]
    assert _brute_force_valid_ground(K_CONST, n_worlds, keys) is _K_CONST_EXPECTED


def test_nested_bf_flips_under_varying_domain():
    """Sanity check that NESTED_BF genuinely depends on the constant-domain
    choice (batch requirement): it must go INVALID under 'varying', the direct
    opposite of the constant-domain verdict asserted above. Independent of the
    deep embedding — exercises the existing Z3 route in a different mode."""
    assert qml_is_valid(NESTED_BF, mode="constant", frame="K") is True
    assert qml_is_valid(NESTED_BF, mode="varying", frame="K") is False


# --------------------------------------------------------------------------- #
# Encoder (structure only — no Isabelle).
# --------------------------------------------------------------------------- #

def test_encoder_maps_barcan():
    ac = AtomConsts()
    term = qml_to_deep(BARCAN, ac, _shared_consts(ac))
    assert term == (
        "(ImpD (DiaD (ExD (Atm p_A [(BVar 0)]))) (ExD (DiaD (Atm p_A [(BVar 0)]))))")
    assert ac.decls() == ['consts p_A :: "s"']


def test_encoder_de_bruijn_index_is_innermost_binder():
    # ∀x ∀x' A(x') — the INNER binder shadows: A's argument resolves to the
    # inner ∀ (index 0), never the outer one (index 1).
    x2 = Variable("x2")
    nested = Quantifier(FORALL, x, Quantifier(FORALL, x2, A(x2)))
    ac = AtomConsts()
    assert qml_to_deep(nested, ac, _shared_consts(ac)) == "(AllD (AllD (Atm p_A [(BVar 0)])))"


def test_encoder_de_bruijn_index_reaches_outer_binder():
    # ∀x ∃y A(x) — A's argument is the OUTER variable x, one level up (index 1).
    y = Variable("y")
    nested = Quantifier(FORALL, x, Quantifier(EXISTS, y, A(x)))
    ac = AtomConsts()
    assert qml_to_deep(nested, ac, _shared_consts(ac)) == "(AllD (ExD (Atm p_A [(BVar 1)])))"


def test_encoder_constant_becomes_fvar_with_own_namespace():
    ac = AtomConsts()
    cc = _shared_consts(ac)
    term = qml_to_deep(K_CONST, ac, cc)
    assert "(FVar" in term
    # a constant and a predicate never collapse onto the same Isabelle name,
    # even though both are of type s (they reach different functions, V/C).
    names = {d.split()[1] for d in ac.decls() + cc.decls()}
    assert len(names) == len(ac.decls()) + len(cc.decls())
    # the object constant itself is declared in cc, NOT lost in ac — this is
    # the exact completeness check the major C54-review finding was missing:
    # qml_to_deep used to silently auto-create an unreachable consts resolver
    # when the caller passed only atoms, so cc.decls() below would previously
    # have been empty/inaccessible from this call site. consts is now a
    # required parameter, so that silent loss can no longer happen.
    assert cc.decls() == ['consts p_c :: "s"']


def test_qml_to_deep_requires_consts_argument():
    """The atoms-only call pattern that lost object-constant declarations
    (C54 review, major finding) is no longer even callable: ``consts`` has no
    default, so omitting it is a loud ``TypeError`` at the call site, not a
    silent runtime data loss."""
    with pytest.raises(TypeError):
        qml_to_deep(K_CONST, AtomConsts())


def test_hand_assembled_theory_declares_every_name_the_term_uses():
    """Structural completeness check for the pattern the module docstring now
    documents: encode via qml_to_deep(formula, atoms, consts) with a
    pool-shared consts, then a hand-assembled theory emitting BOTH
    atoms.decls() and consts.decls() actually declares every ``Atm``/``FVar``
    name the encoded term refers to (no undeclared name left over, which is
    exactly what made Isabelle reject the old atoms-only pattern with
    'Extra variables on rhs')."""
    ac = AtomConsts()
    cc = _shared_consts(ac)
    term = qml_to_deep(K_CONST, ac, cc)
    declared = {d.split()[1] for d in ac.decls() + cc.decls()}
    used = set(re.findall(r"\(?Atm (\w+)", term)) | set(re.findall(r"\(FVar (\w+)\)", term))
    assert used, "sanity: K_CONST does exercise both Atm and FVar"
    assert used <= declared


@pytest.mark.parametrize("node, head", [
    (Not(P), "NegD"), (And(P, P), "AndD"), (Or(P, P), "OrD"),
    (Implies(P, P), "ImpD"), (Iff(P, P), "IffD"),
    (Box(P), "BoxD"), (Diamond(P), "DiaD"),
])
def test_encoder_constructor_heads(node, head):
    ac = AtomConsts()
    assert qml_to_deep(node, ac, _shared_consts(ac)).startswith(f"({head} ")


@pytest.mark.parametrize("node, head", [
    (Quantifier(FORALL, x, A(x)), "AllD"),
    (Quantifier(EXISTS, x, A(x)), "ExD"),
])
def test_encoder_quantifier_heads(node, head):
    ac = AtomConsts()
    assert qml_to_deep(node, ac, _shared_consts(ac)).startswith(f"({head} ")


def test_distinct_atoms_get_distinct_consts():
    ac = AtomConsts()
    qml_to_deep(And(A(c), B(c)), ac, _shared_consts(ac))
    assert ac.decls() == ['consts p_A :: "s"', 'consts p_B :: "s"']


def test_sanitize_atom_is_legal_and_prefixed():
    assert sanitize_atom("A") == "p_A"


# --------------------------------------------------------------------------- #
# Refusals (unsupported fragment, named).
# --------------------------------------------------------------------------- #

def test_encoder_rejects_equality():
    ac = AtomConsts()
    with pytest.raises(NotImplementedError, match="equality"):
        qml_to_deep(Atom("=", [x, x]), ac, _shared_consts(ac))


def test_encoder_rejects_free_variable():
    ac = AtomConsts()
    with pytest.raises(NotImplementedError, match="free variable"):
        qml_to_deep(A(x), ac, _shared_consts(ac))


def test_encoder_rejects_function_term():
    f = Function("f", [c])
    ac = AtomConsts()
    with pytest.raises(NotImplementedError, match="unsupported term"):
        qml_to_deep(Quantifier(FORALL, x, Atom("A", [f])), ac, _shared_consts(ac))


def test_encoder_rejects_number_term():
    ac = AtomConsts()
    with pytest.raises(NotImplementedError, match="unsupported term"):
        qml_to_deep(Atom("A", [Number(1)]), ac, _shared_consts(ac))


def test_encoder_rejects_epistemic_operator():
    ac = AtomConsts()
    with pytest.raises(NotImplementedError, match="unsupported node type"):
        qml_to_deep(Knows(c, P), ac, _shared_consts(ac))


def test_encoder_rejects_temporal_operator():
    ac = AtomConsts()
    with pytest.raises(NotImplementedError, match="unsupported node type"):
        qml_to_deep(Always(P), ac, _shared_consts(ac))


def test_encoder_rejects_xor():
    ac = AtomConsts()
    with pytest.raises(NotImplementedError, match="unsupported node type"):
        qml_to_deep(Xor(P, P), ac, _shared_consts(ac))


@pytest.mark.parametrize("node", [Obligatory(P), Permitted(P)])
def test_encoder_rejects_deontic_operator(node):
    # neither Obligatory nor Permitted subclasses Box/Diamond/the five
    # connectives, so _encode's catch-all refuses them by name — deontic
    # necessity/possibility is outside this module's alethic-only scope.
    ac = AtomConsts()
    with pytest.raises(NotImplementedError, match="unsupported node type"):
        qml_to_deep(node, ac, _shared_consts(ac))


@pytest.mark.parametrize("node", [Nominal("i"), At(Nominal("i"), P)])
def test_encoder_rejects_hybrid_operator(node):
    # a bare Nominal and the @ satisfaction operator are both refused the
    # same way: hybrid logic is outside this module's scope entirely.
    ac = AtomConsts()
    with pytest.raises(NotImplementedError, match="unsupported node type"):
        qml_to_deep(node, ac, _shared_consts(ac))


def test_encoder_rejects_many_sorted_quantifier():
    node = SortedQuantifier(FORALL, x, "S", A(x))
    ac = AtomConsts()
    with pytest.raises(NotImplementedError, match="unsupported node type"):
        qml_to_deep(node, ac, _shared_consts(ac))


def test_encoder_rejects_many_sorted_constant():
    # a SortedConstant reaches _obj_to_deep's term-level catch-all (neither a
    # Variable nor a plain Constant), the same path Function/Number take.
    node = Atom("A", [SortedConstant("c", "S")])
    ac = AtomConsts()
    with pytest.raises(NotImplementedError, match="unsupported term"):
        qml_to_deep(node, ac, _shared_consts(ac))


def test_faithfulness_theory_grounds_and_reraises_encoder_errors():
    with pytest.raises(NotImplementedError):
        qml_deep_faithfulness_theory("Bad", formula=Knows(c, P))


# --------------------------------------------------------------------------- #
# Emitted theory text (structure only).
# --------------------------------------------------------------------------- #

def _balanced(s: str, op: str, cl: str) -> bool:
    depth = 0
    for ch in s:
        if ch == op:
            depth += 1
        elif ch == cl:
            depth -= 1
            if depth < 0:
                return False
    return depth == 0


def _quotes_balanced(s: str) -> bool:
    return s.count('"') % 2 == 0


def test_theory_has_all_three_embeddings_and_faithfulness():
    t = qml_deep_faithfulness_theory("QmlFaithfulness")
    assert t.startswith("theory QmlFaithfulness\n  imports Main\nbegin")
    assert t.rstrip().endswith("end")
    # deep (with the de Bruijn obj datatype), maximal, minimal
    assert "datatype obj = BVar nat | FVar s" in t
    assert "datatype qml" in t and "primrec truthD" in t
    assert "type_synonym sigma" in t and "definition BoxS" in t
    assert "consts Racc" in t and "definition BoxM" in t
    assert "consts Dset" in t and "consts Cint" in t
    # the five faithfulness theorems, each with a real proof
    for thm in ("faithful1a", "faithful1b", "faithful2", "faithful3", "sound_min"):
        assert f"theorem {thm}:" in t
    assert "oops" not in t and "sorry" not in t


def test_no_sorry_or_oops_anywhere_in_shipped_theory():
    """Mandatory per the C54 batch requirement: the shipped theory text must
    contain no 'sorry' and no 'oops' — the faithfulness meta-theorem must
    actually be PROVED, not admitted. Checked both ungrounded and grounded."""
    for formula in (None, BARCAN, K_CONST):
        t = qml_deep_faithfulness_theory("QmlNoSorry", formula=formula)
        assert "sorry" not in t
        assert "oops" not in t


def test_truthd_clauses_match_satisfies_modal_semantics():
    """Box = universal over R-successors, Diamond = existential, ∀ = bounded
    universal over the (constant) domain D, ∃ = bounded existential — exactly
    satisfies_modal's own box/diamond/quantifier clauses."""
    t = qml_deep_faithfulness_theory("QmlClauses")
    assert ("(BoxD f)     = (\\<forall>y. R x y \\<longrightarrow> "
            "truthD e c W R D V y f)") in t
    assert ("(DiaD f)     = (\\<exists>y. R x y \\<and> "
            "truthD e c W R D V y f)") in t
    assert ("(AllD f)     = (\\<forall>d. D d \\<longrightarrow> "
            "truthD (case_nat d e) c W R D V x f)") in t
    assert ("(ExD f)      = (\\<exists>d. D d \\<and> "
            "truthD (case_nat d e) c W R D V x f)") in t


def test_theory_with_formula_appends_definition_and_atom_consts():
    t = qml_deep_faithfulness_theory("QmlFaithfulnessEx", formula=K_CONST)
    assert 'consts p_A :: "s"' in t and 'consts p_B :: "s"' in t
    assert 'consts p_c :: "s"' in t
    assert 'definition example :: qml where "example =' in t


def test_illegal_theory_name_rejected():
    with pytest.raises(ValueError):
        qml_deep_faithfulness_theory("1bad name")


@pytest.mark.parametrize("formula", [None, BARCAN, CONVERSE_BARCAN,
                                     NESTED_CBF, NESTED_BF, K_CONST,
                                     DEAD_END_INVALID])
def test_balanced_parens_and_quotes(formula):
    t = (qml_deep_faithfulness_theory("QmlBal") if formula is None
         else qml_deep_faithfulness_theory("QmlBal", formula=formula))
    assert _balanced(t, "(", ")"), formula
    assert _quotes_balanced(t), formula
    assert t.count("\\<open>") == t.count("\\<close>")


# --------------------------------------------------------------------------- #
# LIVE: Isabelle machine-checks the faithfulness proofs. Run serially (one
# check_theory build at a time) — this module is the only Isabelle item in its
# roadmap batch.
# --------------------------------------------------------------------------- #

@pytest.mark.isabelle_live
@pytest.mark.skipif(not isabelle_available(), reason="no Isabelle installation found")
def test_faithfulness_theory_verifies_in_isabelle():
    t = qml_deep_faithfulness_theory("QmlFaithfulness")
    r = check_theory(t, "QmlFaithfulness", session_timeout=180)
    assert r.ok, (
        "Isabelle failed to discharge the QML faithfulness proofs:\n"
        + r.output[-2000:])


@pytest.mark.isabelle_live
@pytest.mark.skipif(not isabelle_available(), reason="no Isabelle installation found")
def test_faithfulness_theory_with_barcan_verifies_in_isabelle():
    # exercises DiaD/ExD nesting in the grounded ``example`` term.
    t = qml_deep_faithfulness_theory("QmlFaithfulnessBarcan", formula=BARCAN)
    r = check_theory(t, "QmlFaithfulnessBarcan", session_timeout=180)
    assert r.ok, r.output[-2000:]


@pytest.mark.isabelle_live
@pytest.mark.skipif(not isabelle_available(), reason="no Isabelle installation found")
def test_faithfulness_theory_with_nested_cbf_verifies_in_isabelle():
    # exercises BoxD/AllD nesting in the grounded ``example`` term.
    t = qml_deep_faithfulness_theory("QmlFaithfulnessCbf", formula=NESTED_CBF)
    r = check_theory(t, "QmlFaithfulnessCbf", session_timeout=180)
    assert r.ok, r.output[-2000:]


@pytest.mark.isabelle_live
@pytest.mark.skipif(not isabelle_available(), reason="no Isabelle installation found")
def test_faithfulness_theory_with_constant_verifies_in_isabelle():
    # exercises the FVar (rigid object constant) path in the grounded term.
    t = qml_deep_faithfulness_theory("QmlFaithfulnessConst", formula=K_CONST)
    r = check_theory(t, "QmlFaithfulnessConst", session_timeout=180)
    assert r.ok, r.output[-2000:]


@pytest.mark.isabelle_live
@pytest.mark.skipif(not isabelle_available(), reason="no Isabelle installation found")
def test_hand_assembled_theory_with_required_consts_verifies_in_isabelle():
    """Positive confirmation of the C54-review major-finding fix: build a
    theory the way a caller who does NOT go through
    qml_deep_faithfulness_theory must now (consts is required, no silent
    auto-create) — encode via qml_to_deep(formula, atoms, consts) with an
    explicit, pool-shared consts, then emit BOTH atoms.decls() and
    consts.decls(). Before the fix, this exact caller pattern (qml_to_deep
    called with only ``atoms``, an auto-created ``consts`` silently
    swallowing the FVar declaration) made Isabelle reject the theory with
    'Extra variables on rhs' — reproduced independently during review. Since
    the pattern below now declares BOTH namespaces explicitly, Isabelle must
    accept it.
    """
    atoms = AtomConsts()
    consts = _shared_consts(atoms)
    term = qml_to_deep(K_CONST, atoms, consts)
    extra = "\n".join(
        ["", "section \\<open>Hand-assembled, caller-declared consts\\<close>", ""]
        + atoms.decls() + consts.decls()
        + [f'definition example :: qml where "example = {term}"'])
    t = wrap_theory("QmlHandAssembled", _QML_BODY, extra)
    r = check_theory(t, "QmlHandAssembled", session_timeout=180)
    assert r.ok, r.output[-2000:]
