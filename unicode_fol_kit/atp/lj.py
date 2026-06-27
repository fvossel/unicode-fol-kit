"""Intuitionistic sequent calculus **LJ** — a derivation checker.

Gentzen's **LJ** is the sequent calculus for intuitionistic logic. Structurally it is
the classical **LK** of :mod:`unicode_fol_kit.atp.sequent` with one decisive
restriction: a sequent's **succedent holds at most one formula**. That single change
blocks the classical theorems that fail intuitionistically — the ``→L`` rule's left
premise is ``Γ ⊢ A`` (the succedent is *replaced* by ``A``, not kept alongside ``Δ``),
so excluded middle, double-negation elimination, and Peirce's law have no LJ
derivation, exactly as the Kripke semantics in
:mod:`unicode_fol_kit.semantics.intuitionistic` confirms.

It reuses the LK :class:`~unicode_fol_kit.atp.sequent.Sequent` /
:class:`~unicode_fol_kit.atp.sequent.Derivation` data model and the ``sequent`` /
``derive`` / ``axiom`` helpers; only the rule set and the checker are new.
``render_sequent_proof`` renders an LJ derivation unchanged.

Rules: ``Ax``, the structural ``WL`` / ``WR`` / ``CL`` / ``Cut``, the connective rules
``¬L`` / ``¬R``, ``∧L`` / ``∧R``, ``∨L`` / ``∨R1`` / ``∨R2`` (disjunction-right is split,
unlike LK), ``→L`` / ``→R``, ``↔L`` / ``↔R``, and the quantifier rules ``∀L`` / ``∀R``,
``∃L`` / ``∃R`` (with the eigenvariable condition on ``∀R`` / ``∃L``).

Public API: :func:`check_lj_proof`, :func:`verify_lj_proof`.
"""

from typing import Dict, List, Optional

from ..fol.nodes import Node, Not, And, Or, Implies, Iff, Variable
from .sequent import (
    Sequent, Derivation, SequentResult, sequent, derive, axiom,
    _ms_eq, _seq_eq, _candidates, _two_match, _canon_derivation, _eigenvar_not_free,
)
from .fitch import _subst_var, _q_kind, _is_term


# ---------------------------------------------------------------------------
# Rule checkers (single-conclusion: every succedent has length ≤ 1)
# ---------------------------------------------------------------------------

def _r_axiom(concl, prems, extra):
    """Ax: ``Γ, A ⊢ A`` — the one succedent formula occurs in the antecedent."""
    if prems:
        return "Ax takes no premises"
    if len(concl.succedent) != 1:
        return "an LJ axiom has exactly one succedent formula"
    if concl.succedent[0] not in concl.antecedent:
        return "Ax: the succedent formula must occur in the antecedent"
    return None


def _r_weaken_l(concl, prems, extra):
    """WL: from ``Γ ⊢ Δ`` infer ``Γ, A ⊢ Δ``."""
    if len(prems) != 1:
        return "WL has one premise"
    for _, rest in _candidates(concl.antecedent, lambda f: True):
        if _seq_eq(prems[0], rest, concl.succedent):
            return None
    return "WL: the premise must be the conclusion minus one antecedent formula"


def _r_weaken_r(concl, prems, extra):
    """WR: from ``Γ ⊢`` (empty succedent) infer ``Γ ⊢ A``."""
    if len(prems) != 1:
        return "WR has one premise"
    if len(concl.succedent) != 1:
        return "WR concludes a single succedent formula"
    if _seq_eq(prems[0], concl.antecedent, ()):
        return None
    return "WR: the premise must have an empty succedent (Γ ⊢)"


def _r_contract_l(concl, prems, extra):
    """CL: from ``Γ, A, A ⊢ Δ`` infer ``Γ, A ⊢ Δ``."""
    if len(prems) != 1:
        return "CL has one premise"
    for principal, _ in _candidates(concl.antecedent, lambda f: True):
        if _seq_eq(prems[0], concl.antecedent + (principal,), concl.succedent):
            return None
    return "CL: the premise must duplicate one antecedent formula"


def _r_cut(concl, prems, extra):
    """Cut: from ``Γ ⊢ A`` and ``Γ, A ⊢ Δ`` infer ``Γ ⊢ Δ``."""
    if len(prems) != 2:
        return "Cut has two premises"
    g, d = concl.antecedent, concl.succedent
    for left, right in ((prems[0], prems[1]), (prems[1], prems[0])):
        if len(left.succedent) != 1 or not _ms_eq(left.antecedent, g):
            continue
        a = left.succedent[0]
        if _seq_eq(right, g + (a,), d):
            return None
    return "Cut: premises must be Γ⊢A and Γ,A⊢Δ sharing the context"


def _r_not_l(concl, prems, extra):
    """¬L: from ``Γ ⊢ A`` infer ``Γ, ¬A ⊢`` (empty succedent)."""
    if len(prems) != 1:
        return "¬L has one premise"
    if len(concl.succedent) != 0:
        return "¬L concludes an empty succedent"
    for principal, rest in _candidates(concl.antecedent, lambda f: isinstance(f, Not)):
        if _seq_eq(prems[0], rest, (principal.formula,)):
            return None
    return "¬L: needs ¬A on the left; premise Γ ⊢ A"


def _r_not_r(concl, prems, extra):
    """¬R: from ``Γ, A ⊢`` (empty succedent) infer ``Γ ⊢ ¬A``."""
    if len(prems) != 1:
        return "¬R has one premise"
    if len(concl.succedent) != 1 or not isinstance(concl.succedent[0], Not):
        return "¬R must conclude a single negation"
    a = concl.succedent[0].formula
    if _seq_eq(prems[0], concl.antecedent + (a,), ()):
        return None
    return "¬R: the premise must be Γ, A ⊢ (empty succedent)"


def _r_and_l(concl, prems, extra):
    """∧L: from ``Γ, A, B ⊢ Δ`` infer ``Γ, A∧B ⊢ Δ``."""
    if len(prems) != 1:
        return "∧L has one premise"
    for principal, rest in _candidates(concl.antecedent, lambda f: isinstance(f, And)):
        if _seq_eq(prems[0], rest + (principal.left, principal.right), concl.succedent):
            return None
    return "∧L: needs A∧B on the left; premise Γ, A, B ⊢ Δ"


def _r_and_r(concl, prems, extra):
    """∧R: from ``Γ ⊢ A`` and ``Γ ⊢ B`` infer ``Γ ⊢ A∧B``."""
    if len(prems) != 2:
        return "∧R has two premises"
    if len(concl.succedent) != 1 or not isinstance(concl.succedent[0], And):
        return "∧R must conclude a single conjunction"
    p = concl.succedent[0]
    if _two_match(prems, (concl.antecedent, (p.left,)), (concl.antecedent, (p.right,))):
        return None
    return "∧R: premises Γ⊢A and Γ⊢B"


def _r_or_l(concl, prems, extra):
    """∨L: from ``Γ, A ⊢ Δ`` and ``Γ, B ⊢ Δ`` infer ``Γ, A∨B ⊢ Δ``."""
    if len(prems) != 2:
        return "∨L has two premises"
    for principal, rest in _candidates(concl.antecedent, lambda f: isinstance(f, Or)):
        w1 = (rest + (principal.left,), concl.succedent)
        w2 = (rest + (principal.right,), concl.succedent)
        if _two_match(prems, w1, w2):
            return None
    return "∨L: needs A∨B on the left; premises Γ,A⊢Δ and Γ,B⊢Δ"


def _r_or_r1(concl, prems, extra):
    """∨R1: from ``Γ ⊢ A`` infer ``Γ ⊢ A∨B``."""
    if len(prems) != 1:
        return "∨R1 has one premise"
    if len(concl.succedent) != 1 or not isinstance(concl.succedent[0], Or):
        return "∨R1 must conclude a single disjunction"
    if _seq_eq(prems[0], concl.antecedent, (concl.succedent[0].left,)):
        return None
    return "∨R1: the premise must be Γ ⊢ A (the left disjunct)"


def _r_or_r2(concl, prems, extra):
    """∨R2: from ``Γ ⊢ B`` infer ``Γ ⊢ A∨B``."""
    if len(prems) != 1:
        return "∨R2 has one premise"
    if len(concl.succedent) != 1 or not isinstance(concl.succedent[0], Or):
        return "∨R2 must conclude a single disjunction"
    if _seq_eq(prems[0], concl.antecedent, (concl.succedent[0].right,)):
        return None
    return "∨R2: the premise must be Γ ⊢ B (the right disjunct)"


def _r_imp_l(concl, prems, extra):
    """→L: from ``Γ ⊢ A`` and ``Γ, B ⊢ Δ`` infer ``Γ, A→B ⊢ Δ`` (the LJ restriction)."""
    if len(prems) != 2:
        return "→L has two premises"
    for principal, rest in _candidates(concl.antecedent, lambda f: isinstance(f, Implies)):
        w1 = (rest, (principal.left,))               # Γ ⊢ A — succedent is just A
        w2 = (rest + (principal.right,), concl.succedent)
        if _two_match(prems, w1, w2):
            return None
    return "→L: needs A→B on the left; premises Γ⊢A and Γ,B⊢Δ"


def _r_imp_r(concl, prems, extra):
    """→R: from ``Γ, A ⊢ B`` infer ``Γ ⊢ A→B``."""
    if len(prems) != 1:
        return "→R has one premise"
    if len(concl.succedent) != 1 or not isinstance(concl.succedent[0], Implies):
        return "→R must conclude a single implication"
    p = concl.succedent[0]
    if _seq_eq(prems[0], concl.antecedent + (p.left,), (p.right,)):
        return None
    return "→R: the premise must be Γ, A ⊢ B"


def _r_iff_l(concl, prems, extra):
    """↔L: from ``Γ, A→B, B→A ⊢ Δ`` infer ``Γ, A↔B ⊢ Δ``."""
    if len(prems) != 1:
        return "↔L has one premise"
    for principal, rest in _candidates(concl.antecedent, lambda f: isinstance(f, Iff)):
        a, b = principal.left, principal.right
        if _seq_eq(prems[0], rest + (Implies(a, b), Implies(b, a)), concl.succedent):
            return None
    return "↔L: needs A↔B on the left; premise Γ, A→B, B→A ⊢ Δ"


def _r_iff_r(concl, prems, extra):
    """↔R: from ``Γ ⊢ A→B`` and ``Γ ⊢ B→A`` infer ``Γ ⊢ A↔B``."""
    if len(prems) != 2:
        return "↔R has two premises"
    if len(concl.succedent) != 1 or not isinstance(concl.succedent[0], Iff):
        return "↔R must conclude a single biconditional"
    p = concl.succedent[0]
    a, b = p.left, p.right
    if _two_match(prems, (concl.antecedent, (Implies(a, b),)),
                  (concl.antecedent, (Implies(b, a),))):
        return None
    return "↔R: premises Γ⊢A→B and Γ⊢B→A"


def _r_forall_l(concl, prems, extra):
    """∀L: from ``Γ, A[x:=t] ⊢ Δ`` infer ``Γ, ∀x A ⊢ Δ`` (t any term, in extra)."""
    if len(prems) != 1:
        return "∀L has one premise"
    if len(extra) != 1 or not _is_term(extra[0]):
        return "∀L needs the instantiation term in extra"
    t = extra[0]
    for principal, rest in _candidates(concl.antecedent, lambda f: _q_kind(f) == "∀"):
        inst = _subst_var(principal.formula, principal.variable, t)
        if _seq_eq(prems[0], rest + (inst,), concl.succedent):
            return None
    return "needs ∀x A on the left and premise Γ, A[x:=t] ⊢ Δ"


def _r_exists_r(concl, prems, extra):
    """∃R: from ``Γ ⊢ A[x:=t]`` infer ``Γ ⊢ ∃x A`` (t any term, in extra)."""
    if len(prems) != 1:
        return "∃R has one premise"
    if len(concl.succedent) != 1 or _q_kind(concl.succedent[0]) != "∃":
        return "∃R must conclude a single existential"
    if len(extra) != 1 or not _is_term(extra[0]):
        return "∃R needs the witness term in extra"
    p = concl.succedent[0]
    inst = _subst_var(p.formula, p.variable, extra[0])
    if _seq_eq(prems[0], concl.antecedent, (inst,)):
        return None
    return "∃R: the premise must be Γ ⊢ A[x:=t]"


def _r_forall_r(concl, prems, extra):
    """∀R: from ``Γ ⊢ A[x:=a]`` infer ``Γ ⊢ ∀x A`` (eigenvariable a, in extra)."""
    if len(prems) != 1:
        return "∀R has one premise"
    if len(concl.succedent) != 1 or _q_kind(concl.succedent[0]) != "∀":
        return "∀R must conclude a single universal"
    if len(extra) != 1 or not isinstance(extra[0], Variable):
        return "∀R needs the eigenvariable in extra"
    a = extra[0]
    p = concl.succedent[0]
    inst = _subst_var(p.formula, p.variable, a)
    if _seq_eq(prems[0], concl.antecedent, (inst,)):
        err = _eigenvar_not_free(a, concl)
        return err if err else None
    return "∀R: the premise must be Γ ⊢ A[x:=a]"


def _r_exists_l(concl, prems, extra):
    """∃L: from ``Γ, A[x:=a] ⊢ Δ`` infer ``Γ, ∃x A ⊢ Δ`` (eigenvariable a, in extra)."""
    if len(prems) != 1:
        return "∃L has one premise"
    if len(extra) != 1 or not isinstance(extra[0], Variable):
        return "∃L needs the eigenvariable in extra"
    a = extra[0]
    for principal, rest in _candidates(concl.antecedent, lambda f: _q_kind(f) == "∃"):
        inst = _subst_var(principal.formula, principal.variable, a)
        if _seq_eq(prems[0], rest + (inst,), concl.succedent):
            err = _eigenvar_not_free(a, concl)
            return err if err else None
    return "needs ∃x A on the left and premise Γ, A[x:=a] ⊢ Δ"


_LJ_RULES: Dict[str, "callable"] = {
    "Ax": _r_axiom,
    "WL": _r_weaken_l, "WR": _r_weaken_r, "CL": _r_contract_l, "Cut": _r_cut,
    "¬L": _r_not_l, "¬R": _r_not_r,
    "∧L": _r_and_l, "∧R": _r_and_r,
    "∨L": _r_or_l, "∨R1": _r_or_r1, "∨R2": _r_or_r2,
    "→L": _r_imp_l, "→R": _r_imp_r,
    "↔L": _r_iff_l, "↔R": _r_iff_r,
    "∀L": _r_forall_l, "∀R": _r_forall_r,
    "∃L": _r_exists_l, "∃R": _r_exists_r,
}


# ---------------------------------------------------------------------------
# The checker
# ---------------------------------------------------------------------------

def _multi_succedent(deriv: "Derivation") -> Optional["Sequent"]:
    """Return the first sequent with more than one succedent formula, or None."""
    if len(deriv.conclusion.succedent) > 1:
        return deriv.conclusion
    for child in deriv.premises:
        bad = _multi_succedent(child)
        if bad is not None:
            return bad
    return None


def _verify(deriv: "Derivation"):
    """Recursive worker: return ``(rule, error)`` or ``(None, None)`` on success."""
    if not isinstance(deriv, Derivation):
        return ("?", f"expected a Derivation, got {type(deriv).__name__}")
    for child in deriv.premises:
        rule, err = _verify(child)
        if err is not None:
            return rule, err
    fn = _LJ_RULES.get(deriv.rule)
    if fn is None:
        return deriv.rule, f"unknown LJ rule {deriv.rule!r}"
    err = fn(deriv.conclusion, [c.conclusion for c in deriv.premises], deriv.extra)
    if err is not None:
        return deriv.rule, err if err.startswith(deriv.rule) else f"{deriv.rule}: {err}"
    return None, None


def verify_lj_proof(derivation: "Derivation") -> SequentResult:
    """Check an intuitionistic **LJ** derivation and return a :class:`SequentResult`.

    Enforces the single-conclusion restriction (every succedent has at most one
    formula) and then the LJ rule of each node, returning the end-sequent and, on
    failure, the first offending rule and reason.
    """
    if isinstance(derivation, Derivation):
        derivation = _canon_derivation(derivation)
    bad = _multi_succedent(derivation)
    if bad is not None:
        return SequentResult(
            False, derivation.conclusion if isinstance(derivation, Derivation) else None,
            "LJ", "intuitionistic (LJ) sequents have at most one succedent formula; "
                  f"found {len(bad.succedent)} in '{bad}'")
    err_rule, err = _verify(derivation)
    end = derivation.conclusion if isinstance(derivation, Derivation) else None
    return SequentResult(err is None, end, err_rule, err)


def check_lj_proof(derivation: "Derivation") -> bool:
    """Return True iff ``derivation`` is a valid intuitionistic LJ derivation (sound)."""
    return verify_lj_proof(derivation).ok
