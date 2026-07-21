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

FALSUM. This toolkit has **no primitive propositional falsum**: the reserved atom
``"⊥"`` is, throughout — the LJ checker above, :func:`int_prove` below, and
:func:`unicode_fol_kit.semantics.intuitionistic.int_valid` (the ground truth both are
checked against) — an *ordinary propositional variable*. There is no ``⊥L`` rule (no
"``Γ, ⊥ ⊢ Δ`` is an axiom" step) and no ex-falso-quodlibet baked in for it: ``⊥→p`` and
``¬⊥`` are both *not* derivable. Express ex falso explicitly instead, e.g. via
``P ∧ ¬P`` (from which anything intuitionistically follows: ``¬(P∧¬P)`` is a theorem,
but a bare context containing the atom ``⊥`` proves nothing extra). This mirrors
:mod:`unicode_fol_kit.hol.intuitionistic`'s FALSUM note, which makes the same choice
for the same reason (faithfulness to ``int_valid``).

``int_prove`` / ``int_decide`` (below) add a **decision procedure** — Dyckhoff's
contraction-free **G4ip** calculus — alongside this derivation *checker*; see their
docstrings.

Public API: :func:`check_lj_proof`, :func:`verify_lj_proof`, :func:`int_prove`,
:func:`int_decide`.
"""

from typing import Dict, FrozenSet, List, Optional, Tuple

from ..fol.nodes import (
    Node, Atom, Not, And, Or, Xor, Implies, Iff, Variable,
    Quantifier, SortedQuantifier,
)
from ..fol._so_nodes import SecondOrderQuantifier
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

    Malformed input (``None``, a bare :class:`~unicode_fol_kit.fol.nodes.Node`, a bare
    :class:`Sequent` not wrapped in a :class:`Derivation`, …) is reported the same clean
    way as :func:`~unicode_fol_kit.atp.sequent.verify_sequent_proof` does: ``ok=False``
    with ``error_rule="?"`` and an ``error`` saying what type was expected — never a raw
    ``AttributeError`` from probing a ``.conclusion`` that is not there.
    """
    if isinstance(derivation, Derivation):
        derivation = _canon_derivation(derivation)
        bad = _multi_succedent(derivation)
        if bad is not None:
            return SequentResult(
                False, derivation.conclusion,
                "LJ", "intuitionistic (LJ) sequents have at most one succedent formula; "
                      f"found {len(bad.succedent)} in '{bad}'")
    # Non-Derivation input (None, a bare Node, a bare Sequent, ...) skips the
    # multi-succedent probe above (it needs a real Derivation tree) and falls through
    # to _verify, whose own isinstance check reports the same clean "expected a
    # Derivation" shape that atp.sequent._verify uses -- never an AttributeError.
    err_rule, err = _verify(derivation)
    end = derivation.conclusion if isinstance(derivation, Derivation) else None
    return SequentResult(err is None, end, err_rule, err)


def check_lj_proof(derivation: "Derivation") -> bool:
    """Return True iff ``derivation`` is a valid intuitionistic LJ derivation (sound)."""
    return verify_lj_proof(derivation).ok


# ---------------------------------------------------------------------------
# int_prove / int_decide: Dyckhoff's G4ip -- a terminating DECISION PROCEDURE
# ---------------------------------------------------------------------------
#
# Everything above this point CHECKS a given derivation. G4ip (Dyckhoff, "Contraction-
# free sequent calculi for intuitionistic logic", J. Symbolic Logic 57(3), 1992 — also
# called LJT) is a different, contraction-free presentation of LJ whose left rules are
# keyed on the SHAPE of the principal formula rather than being freely applicable, which
# is exactly what makes naive backward proof search in ordinary LJ loop (``A→B`` on the
# left can always fire again on the same formula). Dyckhoff's four ``→L`` variants each
# strictly shrink a well-founded complexity measure, so backward search terminates —
# this is a genuine decision procedure, not a bounded search.
#
# Internal formula representation. Proof search works over a small IR, deliberately
# NOT unicode_fol_kit.fol.nodes.Node, so that the ex-falso sentinel used to encode ``¬A``
# (see below) can never be confused with a Node the caller wrote:
#   ('atom', key)     -- key = the atom's to_unicode_str(); opaque to G4ip
#   ('and', L, R) / ('or', L, R) / ('imp', L, R)
#   _BOT               -- the internal "always false" ex-falso sentinel (see _desugar)
# A sequent is (ctx: FrozenSet[IR], goal: IR); ctx is a SET, not a multiset — G4ip is
# "contraction-free" precisely because none of its rules ever need two copies of a
# hypothesis for completeness (unlike naive LJ, which needs an explicit CL rule).

_BOT: Tuple[str] = ('bot',)  # the ex-falso sentinel; never equal to any ('atom', ...)


def _desugar(f: Node):
    """Rewrite ``¬`` / ``↔`` / ``⊕`` away into the ``('and'|'or'|'imp'|'atom', ...)`` IR
    plus the internal ``_BOT`` sentinel, matching :meth:`IntKripkeModel.forces`'s clauses
    exactly (:mod:`unicode_fol_kit.semantics.intuitionistic`), so ``int_prove`` decides
    exactly the semantics ``int_valid`` checks.

    ``¬A`` is encoded the standard way, ``A→⊥`` (Dyckhoff's own presentation), but ``⊥``
    here is ``_BOT`` — an internal sentinel object, DISTINCT from the reserved surface
    atom ``"⊥"`` (which desugars via the plain ``Atom`` case below, to ``('atom', '⊥')``,
    an ordinary variable with no special treatment — see the module docstring's FALSUM
    paragraph). This is what makes ``¬A`` behave like the *primitive* Kripke clause "no
    reachable world forces A" — which quantifies over worlds, not over any particular
    atom's valuation — rather than like material implication into a fellow proposition
    that could itself be forced somewhere. ``_BOT`` gets a genuine ex-falso rule inside
    the prover (:func:`_prove`); the surface atom ``"⊥"`` never does.
    """
    if isinstance(f, Atom):
        return ('atom', f.to_unicode_str())
    if isinstance(f, Not):
        # ¬A := A→_BOT ("no future world forces A"); _BOT is the INTERNAL ex-falso
        # sentinel, never the surface atom "⊥" (see the docstring above).
        return ('imp', _desugar(f.formula), _BOT)
    if isinstance(f, And):
        return ('and', _desugar(f.left), _desugar(f.right))
    if isinstance(f, Or):
        return ('or', _desugar(f.left), _desugar(f.right))
    if isinstance(f, Implies):
        return ('imp', _desugar(f.left), _desugar(f.right))
    if isinstance(f, Iff):
        # A↔B ≡ (A→B)∧(B→A) -- matches IntKripkeModel.forces' ↔ clause.
        left, right = _desugar(f.left), _desugar(f.right)
        return ('and', ('imp', left, right), ('imp', right, left))
    if isinstance(f, Xor):
        # A⊕B ≡ (A∨B)∧¬(A∧B) -- matches IntKripkeModel.forces' ⊕ clause exactly.
        left, right = _desugar(f.left), _desugar(f.right)
        return ('and', ('or', left, right), ('imp', ('and', left, right), _BOT))
    raise NotImplementedError(
        f"int_prove: unsupported node {type(f).__name__} "
        "(propositional ∧/∨/→/¬/↔/⊕ and atoms only; see int_valid/int_countermodel "
        "for first-order input)."
    )


def _reject_quantified(formula: Node) -> None:
    """Raise if ``formula`` contains a quantifier -- ``int_prove`` decides the
    PROPOSITIONAL fragment only."""
    for node in formula.walk():
        if isinstance(node, (Quantifier, SortedQuantifier, SecondOrderQuantifier)):
            raise NotImplementedError(
                "int_prove: quantified input is out of scope. Dyckhoff's G4ip decides "
                "PROPOSITIONAL intuitionistic logic only. For a first-order formula, use "
                "the bounded Kripke search "
                "unicode_fol_kit.semantics.intuitionistic.int_valid / int_countermodel "
                "(a returned counter-model genuinely refutes validity; a clean search "
                "does NOT prove it, since first-order intuitionistic logic is "
                "undecidable), or, for the propositional fragment specifically, emit a "
                "HOL problem via unicode_fol_kit.hol.intuitionistic (the "
                "Gödel–McKinsey–Tarski box-translation into modal S4)."
            )


_MAX_STEPS = 200000  # a defensive circuit-breaker, not a completeness bound -- see _prove


def _prove(ctx: FrozenSet, goal, cache: Dict, steps: List[int]) -> bool:
    """Decide the G4ip sequent ``ctx ⊢ goal`` (both in the IR of :func:`_desugar`).

    ``cache`` memoizes by ``(ctx, goal)`` (both hashable: ``ctx`` a frozenset, ``goal`` a
    tuple), which keeps the differential test battery fast; it does not change the
    result (this is a pure function of ``ctx``/``goal``). ``steps`` is a one-element
    mutable counter: Dyckhoff's calculus is *provably* terminating on its own (every
    rule strictly decreases a well-founded complexity measure), so this counter should
    never come close to firing — it exists purely to fail loudly with a diagnosable
    error instead of hanging if a bug is ever introduced here, not as a soundness- or
    completeness-affecting bound (contrast ``int_countermodel``'s ``max_steps``, which
    genuinely bounds an incomplete first-order search).
    """
    key = (ctx, goal)
    cached = cache.get(key)
    if cached is not None:
        return cached
    steps[0] += 1
    if steps[0] > _MAX_STEPS:
        raise RuntimeError(
            "int_prove: internal step budget exceeded. Dyckhoff's G4ip is a provably "
            "terminating calculus, so this should be unreachable -- please report a bug "
            "against unicode_fol_kit.atp.lj._prove (formula too large is not expected "
            "to be the cause)."
        )
    result = _prove_uncached(ctx, goal, cache, steps)
    cache[key] = result
    return result


def _prove_uncached(ctx: FrozenSet, goal, cache: Dict, steps: List[int]) -> bool:
    """One step of :func:`_prove`, assuming ``(ctx, goal)`` was not already cached."""
    kind = goal[0]

    # --- right rules on the goal: invertible, so always safe to apply first. ---
    if kind == 'and':
        # ∧R: Γ⊢A∧B  iff  Γ⊢A and Γ⊢B.
        return (_prove(ctx, goal[1], cache, steps)
                and _prove(ctx, goal[2], cache, steps))
    if kind == 'imp':
        # →R: Γ⊢A→B  iff  Γ,A⊢B.
        return _prove(ctx | {goal[1]}, goal[2], cache, steps)

    # goal is now 'atom', 'bot', or 'or' -- consult ctx.
    if _BOT in ctx:
        return True  # ex falso quodlibet -- ONLY for the internal sentinel.
    if kind == 'atom' and goal in ctx:
        return True  # Ax: Γ,P⊢P for atomic P.

    # --- cheap left rules: each is an unconditional equivalence (holds regardless of
    # the rest of ctx), so firing the FIRST one found and recursing is complete; the
    # other hypotheses remain in ctx for later rounds (or the L⊃4 pass below). ---
    for h in ctx:
        if h[0] == 'and':
            # ∧L: Γ,A∧B⊢C  iff  Γ,A,B⊢C.
            return _prove((ctx - {h}) | {h[1], h[2]}, goal, cache, steps)
        if h[0] == 'or':
            # ∨L: Γ,A∨B⊢C  iff  Γ,A⊢C and Γ,B⊢C.
            rest = ctx - {h}
            return (_prove(rest | {h[1]}, goal, cache, steps)
                    and _prove(rest | {h[2]}, goal, cache, steps))
        if h[0] == 'imp':
            a, b = h[1], h[2]
            if a[0] == 'atom' and a in ctx:
                # atom→L: Γ,P,P→B⊢C  iff  Γ,P,B⊢C (P atomic, present separately).
                return _prove((ctx - {h}) | {b}, goal, cache, steps)
            if a[0] == 'and':
                # ∧→L (currying): Γ,(A∧B)→C⊢D  iff  Γ,A→(B→C)⊢D.
                x, y = a[1], a[2]
                return _prove((ctx - {h}) | {('imp', x, ('imp', y, b))}, goal, cache, steps)
            if a[0] == 'or':
                # ∨→L: Γ,(A∨B)→C⊢D  iff  Γ,A→C,B→C⊢D.
                x, y = a[1], a[2]
                return _prove((ctx - {h}) | {('imp', x, b), ('imp', y, b)}, goal, cache, steps)
            # a[0] == 'imp' (an L⊃4 candidate) or an atom not (yet) present: no cheap
            # move on this h; leave it in ctx and keep scanning.

    # ctx is now saturated w.r.t. the cheap rules. Two backtracking choice points remain.
    if kind == 'or':
        # ∨R: try each disjunct (not invertible -- the only genuine "which one" choice
        # besides L⊃4). Both sub-calls reuse the same saturated ctx.
        return (_prove(ctx, goal[1], cache, steps)
                or _prove(ctx, goal[2], cache, steps))

    # →→L (L⊃4), the one genuinely two-premise rule: for a hypothesis (A→B)→C, decide
    #   Γ,(A→B)→C⊢D  iff  (Γ,B→C⊢A→B)  and  (Γ,C⊢D).
    # This is an EQUIVALENCE over the full (h-including) Γ (Dyckhoff 1992), so trying
    # each L⊃4-shaped hypothesis in turn -- and, for a given one, requiring BOTH
    # premises -- is complete; a failed candidate is simply skipped in favour of the
    # next (the rest of ctx, including any other hypothesis, is retained in "rest" and
    # tried by both premises, so nothing here is lost by moving on).
    for h in ctx:
        if h[0] == 'imp' and h[1][0] == 'imp':
            x, y = h[1][1], h[1][2]
            b = h[2]
            rest = ctx - {h}
            if _prove(rest | {('imp', y, b)}, ('imp', x, y), cache, steps):
                if _prove(rest | {b}, goal, cache, steps):
                    return True
    return False


def int_prove(premises: List[Node], conclusion: Node) -> bool:
    """Decide ``premises ⊢ conclusion`` in **propositional intuitionistic logic** —
    a genuine, terminating decision procedure via Dyckhoff's contraction-free **G4ip**
    calculus (unlike :func:`verify_lj_proof`, which only checks a *given* derivation).

    Connectives: ``∧`` ``∨`` ``→`` ``↔`` ``⊕`` ``¬`` and atoms — ``↔`` is expanded to two
    implications and ``⊕`` to ``(A∨B)∧¬(A∧B)``, exactly the clauses
    :meth:`~unicode_fol_kit.semantics.intuitionistic.IntKripkeModel.forces` uses, so
    ``int_prove`` decides exactly what
    :func:`~unicode_fol_kit.semantics.intuitionistic.int_valid` checks (the differential
    test battery in ``tests/test_lj_search.py`` cross-checks this). The reserved atom
    ``"⊥"`` is an ORDINARY atom here too (see the module docstring's FALSUM paragraph):
    ``int_prove([], Implies(BOT, p))`` and ``int_prove([], Not(BOT))`` are both False,
    exactly like ``int_valid``.

    Quantified input raises ``NotImplementedError`` — see :func:`_reject_quantified` for
    where to go instead (the bounded first-order Kripke search, or the propositional
    GMT/S4 HOL route).
    """
    for p in premises:
        _reject_quantified(p)
    _reject_quantified(conclusion)
    ctx = frozenset(_desugar(p) for p in premises)
    goal = _desugar(conclusion)
    return _prove(ctx, goal, {}, [0])


def int_decide(formula: Node) -> bool:
    """Return True iff ``formula`` is a propositional intuitionistic tautology.

    ``int_decide(f)`` is exactly ``int_prove([], f)``; see :func:`int_prove`.
    """
    return int_prove([], formula)
