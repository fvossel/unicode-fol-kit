"""Structural + LIVE tests for the ILL / Lambek Isabelle export
(unicode_fol_kit.hol.isabelle_substructural).

Every case below is hand-checked in three independent ways, none of which needs a
local Isabelle install:

- **Derivability is independently confirmed**: every curated sequent is checked
  with ``ill_prove`` / ``lambek_prove`` (the toolkit's own decision procedures —
  see ``tests/test_substructural.py``'s module docstring for why they are trusted)
  before asking the emitter to replay it.
- **The deep embedding is complete**: the emitted ``datatype`` has exactly the
  9 (ILL) / 4 (Lambek) constructors the grammar needs, and the ``inductive
  derivable`` block has exactly the 20 (ILL: 19 Python rules + the structural
  ``Exch`` — see the module docstring for why) / 7 (Lambek) intro rules —
  counted, not eyeballed.
- **The replay is self-consistent**: every ``(rule X)`` the proof invokes names
  a rule the theory itself just declared (a replay could not silently invent a
  rule name and still "look" like it worked), and the ``lemma`` statement's
  antecedent/succedent are reconstructed independently here (a second,
  hand-written lift function, not imported from the module under test) and
  checked to match verbatim.

On top of the text-level checks, two ``@pytest.mark.isabelle_live`` tests (skipped
unless a real Isabelle/HOL install is found) actually load one emitted ILL theory
and one emitted Lambek theory with a real ``isabelle build``.
"""

import re

import pytest

from unicode_fol_kit import MSFLParser, Atom, Tensor, With, OPlus, LinearImplies, OfCourse, One
from unicode_fol_kit import Product, Under, Over
from unicode_fol_kit.fol._linear_nodes import Top, Zero
from unicode_fol_kit.atp.linear import ill_prove, ILLDerivation, ILLSequent
from unicode_fol_kit.atp.lambek import lambek_prove, LambekDerivation, LambekSequent
from unicode_fol_kit.hol.isabelle_substructural import (
    to_isabelle_ill, ill_derivation_theory,
    to_isabelle_lambek, lambek_derivation_theory,
)
from unicode_fol_kit.hol.isabelle_runner import isabelle_available, check_theory

_pl = MSFLParser(linear=True).parse
_pk = MSFLParser(lambek=True).parse


# ---------------------------------------------------------------------------
# Text-level structural helpers (parse the EMITTED THEORY TEXT; no Isabelle).
# ---------------------------------------------------------------------------

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


def _datatype_constructors(thy: str, type_name: str):
    m = re.search(rf"datatype {type_name} = (.+)", thy)
    assert m, f"no 'datatype {type_name} = ...' line found in:\n{thy}"
    return [part.strip().split(" ")[0] for part in m.group(1).split("|")]


def _intro_names(thy: str):
    """Names declared in the 'inductive derivable ... where' block, in order."""
    m = re.search(r'inductive derivable ::.*?where\n(.*?)\n\n', thy, re.S)
    assert m, f"no 'inductive derivable ... where' block found in:\n{thy}"
    names = re.findall(r'^\s*\|?\s*(\w+):', m.group(1), re.M)
    assert names, "no intro rules parsed out of the inductive block"
    return names


def _rule_references(thy: str):
    """Every '(rule X)' the replay proof invokes, in order (duplicates kept)."""
    return re.findall(r'\(rule (\w+)\)', thy)


# The exact 20 / 7 intro names this module is contracted to emit, in emission
# order — pinning both the SET (nothing missing, nothing extra) and the ORDER.
EXPECTED_ILL_INTROS = [
    "Ax", "Exch", "OneR", "OneL", "TensorL", "TensorR", "LImpL", "LImpR",
    "WithL1", "WithL2", "WithR", "OPlusL", "OPlusR1", "OPlusR2",
    "BangW", "BangC", "BangD", "BangP", "TopR", "ZeroL",
]
EXPECTED_LAMBEK_INTROS = ["Ax", "ProdL", "ProdR", "UnderL", "UnderR", "OverL", "OverR"]


# ---------------------------------------------------------------------------
# Independent (hand-written, NOT imported from the module under test) lift
# functions, used only to build the EXPECTED lemma text.
# ---------------------------------------------------------------------------

def _lift_ill(f):
    if isinstance(f, Atom):
        return f"(IAtom ''{f.to_unicode_str()}'')"
    if isinstance(f, Tensor):
        return f"(ITensor {_lift_ill(f.left)} {_lift_ill(f.right)})"
    if isinstance(f, With):
        return f"(IWith {_lift_ill(f.left)} {_lift_ill(f.right)})"
    if isinstance(f, OPlus):
        return f"(IOPlus {_lift_ill(f.left)} {_lift_ill(f.right)})"
    if isinstance(f, LinearImplies):
        return f"(ILImp {_lift_ill(f.left)} {_lift_ill(f.right)})"
    if isinstance(f, OfCourse):
        return f"(IBang {_lift_ill(f.formula)})"
    if isinstance(f, One):
        return "IOne"
    if isinstance(f, Top):
        return "ITop"
    if isinstance(f, Zero):
        return "IZero"
    raise AssertionError(f"unexpected ILL node {type(f).__name__}")


def _flat_ill(fs):
    return "[" + ", ".join(_lift_ill(f) for f in fs) + "]" if fs else "[]"


def _lift_lambek(f):
    if isinstance(f, Atom):
        return f"(LAtom ''{f.to_unicode_str()}'')"
    if isinstance(f, Product):
        return f"(LProduct {_lift_lambek(f.left)} {_lift_lambek(f.right)})"
    if isinstance(f, Under):
        return f"(LUnder {_lift_lambek(f.left)} {_lift_lambek(f.right)})"
    if isinstance(f, Over):
        return f"(LOver {_lift_lambek(f.left)} {_lift_lambek(f.right)})"
    raise AssertionError(f"unexpected Lambek node {type(f).__name__}")


def _flat_lambek(fs):
    return "[" + ", ".join(_lift_lambek(f) for f in fs) + "]" if fs else "[]"


# ---------------------------------------------------------------------------
# Curated ILL sequents (>= 6, each hand-confirmed derivable with ill_prove
# before asking to_isabelle_ill to replay it).
# ---------------------------------------------------------------------------

ILL_CASES = [
    ("implies_self", [], "A ⊸ A"),                    # ⊸R then Ax
    ("tensor_comm", ["A ⊗ B"], "B ⊗ A"),               # exchange IS available (⊗L,⊗R)
    ("tensor_comm_implies", [], "(A ⊗ B) ⊸ (B ⊗ A)"),  # ⊸R over the above
    ("bang_duplicates", ["!A"], "A ⊗ A"),              # !C then !D,!D + ⊗R
    ("unit_intro", [], "𝟙"),                           # 1R
    ("top_any_context", ["A", "B"], "⊤"),              # ⊤R: holds regardless of Γ
    ("zero_ex_falso", ["A", "𝟘", "B"], "Q"),           # 0L: holds regardless of C
    ("top_zero_mixed", ["A ⊗ 𝟘"], "B"),                # ⊗L exposes 𝟘, then 0L
]


@pytest.mark.parametrize("name,antecedents,goal", ILL_CASES,
                         ids=[c[0] for c in ILL_CASES])
def test_ill_isabelle_replay_structural(name, antecedents, goal):
    ants = [_pl(a) for a in antecedents]
    g = _pl(goal)
    d = ill_prove(ants, g)
    assert d is not None, f"{name}: expected derivable"

    thy = to_isabelle_ill(ants, g, theory_name="T")

    # (1) Deep embedding is complete: exactly the 9 ill constructors.
    ctors = _datatype_constructors(thy, "ill")
    assert ctors == ["IAtom", "ITensor", "IWith", "IOPlus", "ILImp", "IBang",
                     "IOne", "ITop", "IZero"]

    # (2) Exactly one intro rule per Python rule, plus Exch — counted.
    assert _intro_names(thy) == EXPECTED_ILL_INTROS
    assert len(EXPECTED_ILL_INTROS) == 20

    # (3) The replay references only declared intros.
    declared = set(_intro_names(thy))
    refs = _rule_references(thy)
    assert refs, f"{name}: the replay used no (rule ...) step at all"
    assert set(refs) <= declared, f"{name}: referenced undeclared rule(s) {set(refs) - declared}"

    # (4) The lemma states EXACTLY the queried sequent (antecedent order as
    # ill_prove itself returned it — to_isabelle_ill/ill_derivation_theory
    # re-order the replay's own working order to match it).
    expected = (f'lemma ill_goal: "derivable {_flat_ill(d.conclusion.antecedent)} '
               f'{_lift_ill(d.conclusion.succedent)}"')
    assert expected in thy, f"{name}: lemma line not found verbatim:\n{thy}"

    # (5) Well-formed text.
    assert _balanced(thy, "(", ")")
    assert thy.count('"') % 2 == 0
    assert thy.rstrip().endswith("end")
    assert thy.startswith("theory T\n")


def test_ill_derivation_theory_matches_to_isabelle_ill():
    ants, g = [_pl("A"), _pl("A ⊸ B")], _pl("B")
    d = ill_prove(ants, g)
    assert ill_derivation_theory(d, theory_name="Same") == to_isabelle_ill(
        ants, g, theory_name="Same")


def test_to_isabelle_ill_rejects_underivable():
    # No weakening: B cannot be discarded (see tests/test_substructural.py).
    with pytest.raises(ValueError, match="ill_prove|ill_derivable"):
        to_isabelle_ill([_pl("A"), _pl("B")], _pl("A"))


def test_ill_derivation_theory_rejects_bad_derivation():
    a = _pl("A")
    ax = ILLDerivation(ILLSequent((a,), a), "Ax")
    bad = ILLDerivation(ILLSequent((a,), Tensor(a, a)), "⊗R", (ax, ax))  # duplicates a premise
    with pytest.raises(ValueError, match="check_ill_proof|verify_ill_proof"):
        ill_derivation_theory(bad)


# ---------------------------------------------------------------------------
# Curated Lambek sequents (>= 4, each hand-confirmed derivable with
# lambek_prove first).
# ---------------------------------------------------------------------------

LAMBEK_CASES = [
    ("ax", ["A"], "A"),
    ("composition", ["A / B", "B / C"], "A / C"),        # /L then /R
    ("assoc_right_to_left", ["A • (B • C)"], "(A • B) • C"),
    ("assoc_left_to_right", ["(A • B) • C"], "A • (B • C)"),
    ("transitive_verb", ["NP", "(NP \\ S) / NP", "NP"], "S"),  # "Alice sees Bob"
    ("type_lifting", ["A"], "B / (A \\ B)"),
]


@pytest.mark.parametrize("name,sequence,goal", LAMBEK_CASES,
                         ids=[c[0] for c in LAMBEK_CASES])
def test_lambek_isabelle_replay_structural(name, sequence, goal):
    seq = [_pk(a) for a in sequence]
    g = _pk(goal)
    d = lambek_prove(seq, g)
    assert d is not None, f"{name}: expected derivable"

    thy = to_isabelle_lambek(seq, g, theory_name="T")

    ctors = _datatype_constructors(thy, "lam")
    assert ctors == ["LAtom", "LProduct", "LUnder", "LOver"]

    assert _intro_names(thy) == EXPECTED_LAMBEK_INTROS
    assert len(EXPECTED_LAMBEK_INTROS) == 7

    declared = set(_intro_names(thy))
    refs = _rule_references(thy)
    assert refs, f"{name}: the replay used no (rule ...) step at all"
    assert set(refs) <= declared, f"{name}: referenced undeclared rule(s) {set(refs) - declared}"

    expected = (f'lemma lambek_goal: "derivable {_flat_lambek(d.conclusion.antecedent)} '
               f'{_lift_lambek(d.conclusion.succedent)}"')
    assert expected in thy, f"{name}: lemma line not found verbatim:\n{thy}"

    assert _balanced(thy, "(", ")")
    assert thy.count('"') % 2 == 0
    assert thy.rstrip().endswith("end")


def test_lambek_derivation_theory_matches_to_isabelle_lambek():
    seq, g = [_pk("A"), _pk("A \\ B")], _pk("B")
    d = lambek_prove(seq, g)
    assert lambek_derivation_theory(d, theory_name="Same") == to_isabelle_lambek(
        seq, g, theory_name="Same")


def test_to_isabelle_lambek_rejects_underivable():
    # ORDER: \ wants its argument on the left (see tests/test_substructural.py).
    with pytest.raises(ValueError, match="lambek_prove|lambek_derivable"):
        to_isabelle_lambek([_pk("A \\ B"), _pk("A")], _pk("B"))


def test_lambek_derivation_theory_rejects_bad_derivation():
    a, b = _pk("A"), _pk("B")
    concl = LambekSequent((a, b), Product(a, b))
    ax_a = LambekDerivation(LambekSequent((a,), a), "Ax")
    ax_b = LambekDerivation(LambekSequent((b,), b), "Ax")
    bad = LambekDerivation(concl, "•R", (ax_b, ax_a))  # premises swapped: order matters in L
    with pytest.raises(ValueError, match="check_lambek_proof|verify_lambek_proof"):
        lambek_derivation_theory(bad)


def test_lambek_empty_sequence_rejected():
    with pytest.raises(ValueError):
        to_isabelle_lambek([], _pk("S"))


# ---------------------------------------------------------------------------
# LIVE: actually load one ILL theory and one Lambek theory in a real Isabelle.
# ---------------------------------------------------------------------------

@pytest.mark.isabelle_live
@pytest.mark.skipif(
    not isabelle_available(),
    reason="no Isabelle installation found (set UFK_ISABELLE_HOME / ISABELLE_HOME)")
def test_ill_theory_loads_and_proves_live():
    ants, g = [_pl("!A")], _pl("!(A ⊗ A)")   # exercises !C/!D/⊗R/!P — the deepest ILL rule
    d = ill_prove(ants, g)
    assert d is not None
    thy = ill_derivation_theory(d, theory_name="IllReplayLive")
    r = check_theory(thy, "IllReplayLive", session_timeout=180)
    assert r.ok, r.output[-3000:]


@pytest.mark.isabelle_live
@pytest.mark.skipif(
    not isabelle_available(),
    reason="no Isabelle installation found (set UFK_ISABELLE_HOME / ISABELLE_HOME)")
def test_lambek_theory_loads_and_proves_live():
    seq, g = [_pk("NP"), _pk("(NP \\ S) / NP"), _pk("NP")], _pk("S")
    d = lambek_prove(seq, g)
    assert d is not None
    thy = lambek_derivation_theory(d, theory_name="LambekReplayLive")
    r = check_theory(thy, "LambekReplayLive", session_timeout=180)
    assert r.ok, r.output[-3000:]
