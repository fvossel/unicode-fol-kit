"""Gentzen sequent calculus (LK) for second-order logic: a derivation *checker*.

Where :mod:`unicode_fol_kit.atp.fitch` checks a Fitch-style natural-deduction
proof, this module checks a **two-sided sequent-calculus derivation** — a tree of
sequents ``Γ ⊢ Δ`` (multisets of formulas on each side, read as
``⋀Γ → ⋁Δ``), each obtained from its premises by a named inference rule. It is the
classical Gentzen system **LK** extended with the first-order quantifier rules and
the **second-order** quantifier rules (∀²/∃² over predicate variables), so it
covers the propositional, first-order, and second-order fragments of the kit.

``check_sequent_proof`` is *sound*: it returns ``True`` only when every node of the
derivation genuinely follows from its premises by the stated rule. It is NOT a
prover, and for full second-order logic it *cannot* be completed into one — by
Gödel, standard second-order validity is not recursively enumerable, so every
sound second-order calculus is incomplete. The checker therefore verifies a
*given* derivation; soundness of the rules is by the LK metatheory, cross-checked
in the test-suite against Z3 (for the first-order-expressible sequents) and the
finite-model evaluator ``satisfies_so`` (for the genuinely second-order ones).

Design notes:

- **Additive (context-sharing) LK.** The side contexts ``Γ`` / ``Δ`` are shared
  between a rule's premises and conclusion; weakening and contraction are explicit
  structural rules. Contexts are compared as **multisets** (formula order does not
  matter; multiplicity does).
- **Eigenvariable conditions.** ``∀R`` / ``∃L`` carry an object eigenvariable that
  must not occur free in the lower sequent; ``∀²R`` / ``∃²L`` carry a *predicate*
  eigenvariable with the analogous condition. Both are enforced.
- **Comprehension.** ``∀²L`` / ``∃²R`` instantiate the bound predicate variable
  ``X`` with a comprehension term ``λx̄.ψ`` (arity = ``X``'s arity), replacing each
  ``X(t̄)`` by ``ψ[x̄ := t̄]`` via a fresh, capture-avoiding predicate substitution.

Public API: :class:`Sequent`, :class:`Derivation`, :class:`SequentResult`, the
helpers :func:`sequent`, :func:`derive`, :func:`axiom`, the comprehension wrapper
:class:`Comprehension`, and the checkers :func:`check_sequent_proof` /
:func:`verify_sequent_proof`, plus :func:`render_sequent_proof`.
"""

from collections import Counter
from dataclasses import dataclass
from typing import Callable, Dict, List, Optional, Tuple

from ..fol.nodes import (
    Node, Atom, Not, And, Or, Xor, Implies, Iff, Quantifier,
    Variable,
    SortedQuantifier, SecondOrderQuantifier,
)
from ..fol._msfl_nodes import _rename, _fresh_name
from .fitch import _subst_var, _free_vars, _is_term, _q_kind


# ---------------------------------------------------------------------------
# Sequents and derivations
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class Sequent:
    """A two-sided sequent ``antecedent ⊢ succedent`` (each a multiset of formulas).

    Read as ``⋀antecedent → ⋁succedent``. Both sides are tuples of :class:`Node`
    formulas; their *order* is irrelevant (compared as multisets) but their
    *multiplicity* matters (contraction/weakening are explicit rules). Frozen and
    hashable.
    """

    antecedent: Tuple[Node, ...] = ()
    succedent: Tuple[Node, ...] = ()

    def __post_init__(self):
        """Coerce both sides to tuples so the sequent stays hashable."""
        object.__setattr__(self, "antecedent", tuple(self.antecedent))
        object.__setattr__(self, "succedent", tuple(self.succedent))

    def to_dict(self) -> dict:
        """Serialise to a JSON-compatible dict."""
        return {
            "antecedent": [f.to_dict() for f in self.antecedent],
            "succedent": [f.to_dict() for f in self.succedent],
        }

    @staticmethod
    def from_dict(d: dict) -> "Sequent":
        """Deserialise a Sequent produced by :meth:`to_dict`."""
        return Sequent(
            tuple(Node.from_dict(f) for f in d.get("antecedent", ())),
            tuple(Node.from_dict(f) for f in d.get("succedent", ())),
        )

    def __str__(self) -> str:
        """Render as ``A, B ⊢ C`` using each formula's Unicode form."""
        left = ", ".join(f.to_unicode_str() for f in self.antecedent)
        right = ", ".join(f.to_unicode_str() for f in self.succedent)
        return f"{left} ⊢ {right}".strip()


@dataclass(frozen=True)
class Comprehension:
    """A second-order comprehension term ``λx̄.ψ`` for ∀²L / ∃²R instantiation.

    ``params`` is the tuple of object Variables ``x̄`` abstracted; ``body`` is the
    formula ``ψ``. Instantiating a predicate variable ``X`` of arity ``len(params)``
    with this replaces each ``X(t̄)`` by ``ψ[x̄ := t̄]``.
    """

    params: Tuple[Variable, ...]
    body: Node

    def __post_init__(self):
        """Coerce ``params`` to a tuple so the comprehension stays hashable."""
        object.__setattr__(self, "params", tuple(self.params))

    @property
    def arity(self) -> int:
        """The arity of the abstracted relation (the number of parameters)."""
        return len(self.params)

    def to_dict(self) -> dict:
        """Serialise to a JSON-compatible dict."""
        return {
            "params": [p.to_dict() for p in self.params],
            "body": self.body.to_dict(),
        }

    @staticmethod
    def from_dict(d: dict) -> "Comprehension":
        """Deserialise a Comprehension produced by :meth:`to_dict`."""
        return Comprehension(
            tuple(Node.from_dict(p) for p in d["params"]),
            Node.from_dict(d["body"]),
        )


@dataclass(frozen=True)
class Derivation:
    """A node of a sequent-calculus derivation tree.

    ``conclusion`` is the sequent this node derives; ``rule`` is the inference rule
    name (``"Ax"``, ``"∧R"``, ``"∀L"``, ``"∀²R"``, …); ``premises`` are the
    sub-derivations whose conclusions are this rule's premises (empty for an
    axiom). ``extra`` carries rule-specific data: the instantiation term of
    ``∀L``/``∃R``, the eigenvariable of ``∀R``/``∃L``, the predicate eigenvariable
    of ``∀²R``/``∃²L``, or the :class:`Comprehension` of ``∀²L``/``∃²R``.
    """

    conclusion: Sequent
    rule: str
    premises: Tuple["Derivation", ...] = ()
    extra: Tuple = ()

    def __post_init__(self):
        """Coerce ``premises``/``extra`` to tuples so the derivation stays hashable."""
        object.__setattr__(self, "premises", tuple(self.premises))
        object.__setattr__(self, "extra", tuple(self.extra))

    def to_dict(self) -> dict:
        """Serialise the derivation tree to a JSON-compatible dict."""
        return {
            "conclusion": self.conclusion.to_dict(),
            "rule": self.rule,
            "premises": [p.to_dict() for p in self.premises],
            "extra": [_extra_to_dict(e) for e in self.extra],
        }

    @staticmethod
    def from_dict(d: dict) -> "Derivation":
        """Deserialise a Derivation produced by :meth:`to_dict`."""
        return Derivation(
            Sequent.from_dict(d["conclusion"]),
            d["rule"],
            tuple(Derivation.from_dict(p) for p in d.get("premises", ())),
            tuple(_extra_from_dict(e) for e in d.get("extra", ())),
        )

    def render(self) -> str:
        """Render this derivation as an indented proof tree."""
        return render_sequent_proof(self)


def _extra_to_dict(e):
    """Serialise one ``extra`` item (a Node, a Comprehension, or a scalar)."""
    if isinstance(e, Comprehension):
        return {"_extra": "comprehension", **e.to_dict()}
    if isinstance(e, Node):
        return {"_extra": "node", **e.to_dict()}
    return {"_extra": "scalar", "value": e}


def _extra_from_dict(d):
    """Deserialise one ``extra`` item produced by :func:`_extra_to_dict`."""
    kind = d.get("_extra")
    if kind == "comprehension":
        return Comprehension.from_dict(d)
    if kind == "node":
        return Node.from_dict(d)
    return d["value"]


@dataclass(frozen=True)
class SequentResult:
    """The outcome of checking a derivation: ``ok`` plus the first failure."""

    ok: bool
    endsequent: Optional[Sequent]
    error_rule: Optional[str]
    error: Optional[str]

    def __bool__(self) -> bool:
        """A SequentResult is truthy iff the derivation checked out."""
        return self.ok


# ---------------------------------------------------------------------------
# Authoring helpers
# ---------------------------------------------------------------------------

def sequent(antecedent, succedent) -> Sequent:
    """Build a :class:`Sequent` from two iterables of formulas."""
    return Sequent(tuple(antecedent), tuple(succedent))


def derive(conclusion: Sequent, rule: str, *premises, extra=()) -> Derivation:
    """Build a :class:`Derivation` node with the given rule and sub-derivations."""
    return Derivation(conclusion, rule, tuple(premises), tuple(extra))


def axiom(conclusion: Sequent) -> Derivation:
    """Build an axiom leaf ``Γ, A ⊢ A, Δ`` (rule ``"Ax"``, no premises)."""
    return Derivation(conclusion, "Ax", (), ())


# ---------------------------------------------------------------------------
# Multiset helpers
# ---------------------------------------------------------------------------

def _ms(formulas: Tuple[Node, ...]) -> Counter:
    """Return the multiset (Counter) of a tuple of formulas."""
    return Counter(formulas)


def _ms_eq(a: Tuple[Node, ...], b: Tuple[Node, ...]) -> bool:
    """Return True iff two formula tuples are equal as multisets."""
    return _ms(a) == _ms(b)


def _seq_eq(s: Sequent, antecedent: Tuple[Node, ...], succedent: Tuple[Node, ...]) -> bool:
    """Return True iff sequent ``s`` equals ``antecedent ⊢ succedent`` (multiset)."""
    return _ms_eq(s.antecedent, antecedent) and _ms_eq(s.succedent, succedent)


def _candidates(formulas: Tuple[Node, ...], pred: Callable[[Node], bool]):
    """Yield ``(principal, rest)`` for each occurrence satisfying ``pred``.

    ``rest`` is ``formulas`` with that one occurrence removed (order preserved for
    the others; multiplicity respected). Distinct positions holding equal formulas
    each yield once, which is harmless — the caller accepts on the first match.
    """
    seen_positions = set()
    for i, f in enumerate(formulas):
        if i in seen_positions or not pred(f):
            continue
        rest = formulas[:i] + formulas[i + 1:]
        yield f, rest


# ---------------------------------------------------------------------------
# Rule checkers — propositional LK (additive / context-sharing)
# ---------------------------------------------------------------------------
#
# Each checker has signature (conclusion: Sequent, premises: List[Sequent],
# extra: tuple) and returns None when the step is licensed, or an error string.
# A rule picks its principal formula from the conclusion (a connective on the
# left for an L-rule, on the right for an R-rule), and the premises must equal the
# shared context plus the introduced sub-formulas (compared as multisets). Several
# occurrences of a matching principal are tried; the rule succeeds if ANY works.

RuleFn = Callable[[Sequent, List[Sequent], tuple], Optional[str]]


def _r_axiom(concl, prems, extra):
    """Ax: ``Γ, A ⊢ A, Δ`` — some formula occurs on both sides."""
    if prems:
        return "Ax takes no premises"
    shared = set(concl.antecedent) & set(concl.succedent)
    if not shared:
        return "Ax: no formula occurs on both sides of the sequent"
    return None


def _r_weaken_l(concl, prems, extra):
    """WL: from ``Γ ⊢ Δ`` infer ``Γ, A ⊢ Δ`` (A arbitrary)."""
    if len(prems) != 1:
        return "WL has one premise"
    for _, rest in _candidates(concl.antecedent, lambda f: True):
        if _seq_eq(prems[0], rest, concl.succedent):
            return None
    return "WL: the premise must be the conclusion minus one antecedent formula"


def _r_weaken_r(concl, prems, extra):
    """WR: from ``Γ ⊢ Δ`` infer ``Γ ⊢ Δ, A`` (A arbitrary)."""
    if len(prems) != 1:
        return "WR has one premise"
    for _, rest in _candidates(concl.succedent, lambda f: True):
        if _seq_eq(prems[0], concl.antecedent, rest):
            return None
    return "WR: the premise must be the conclusion minus one succedent formula"


def _r_contract_l(concl, prems, extra):
    """CL: from ``Γ, A, A ⊢ Δ`` infer ``Γ, A ⊢ Δ``."""
    if len(prems) != 1:
        return "CL has one premise"
    for principal, _ in _candidates(concl.antecedent, lambda f: True):
        if _seq_eq(prems[0], concl.antecedent + (principal,), concl.succedent):
            return None
    return "CL: the premise must duplicate one antecedent formula of the conclusion"


def _r_contract_r(concl, prems, extra):
    """CR: from ``Γ ⊢ Δ, A, A`` infer ``Γ ⊢ Δ, A``."""
    if len(prems) != 1:
        return "CR has one premise"
    for principal, _ in _candidates(concl.succedent, lambda f: True):
        if _seq_eq(prems[0], concl.antecedent, concl.succedent + (principal,)):
            return None
    return "CR: the premise must duplicate one succedent formula of the conclusion"


def _r_cut(concl, prems, extra):
    """Cut: from ``Γ ⊢ Δ, A`` and ``Γ, A ⊢ Δ`` infer ``Γ ⊢ Δ``."""
    if len(prems) != 2:
        return "Cut has two premises"
    g, d = concl.antecedent, concl.succedent
    for left, right in ((prems[0], prems[1]), (prems[1], prems[0])):
        # left = Γ ⊢ Δ, A  ;  right = Γ, A ⊢ Δ
        for a, rest_succ in _candidates(left.succedent, lambda f: True):
            if not _ms_eq(rest_succ, d):
                continue
            if not _ms_eq(left.antecedent, g):
                continue
            if _seq_eq(right, g + (a,), d):
                return None
    return "Cut: premises must be Γ⊢Δ,A and Γ,A⊢Δ sharing the conclusion's context"


def _r_not_l(concl, prems, extra):
    """¬L: from ``Γ ⊢ Δ, A`` infer ``Γ, ¬A ⊢ Δ``."""
    if len(prems) != 1:
        return "¬L has one premise"
    for principal, rest in _candidates(concl.antecedent, lambda f: isinstance(f, Not)):
        if _seq_eq(prems[0], rest, concl.succedent + (principal.formula,)):
            return None
    return "¬L: needs ¬A on the left; premise Γ ⊢ Δ, A"


def _r_not_r(concl, prems, extra):
    """¬R: from ``Γ, A ⊢ Δ`` infer ``Γ ⊢ Δ, ¬A``."""
    if len(prems) != 1:
        return "¬R has one premise"
    for principal, rest in _candidates(concl.succedent, lambda f: isinstance(f, Not)):
        if _seq_eq(prems[0], concl.antecedent + (principal.formula,), rest):
            return None
    return "¬R: needs ¬A on the right; premise Γ, A ⊢ Δ"


def _r_and_l(concl, prems, extra):
    """∧L: from ``Γ, A, B ⊢ Δ`` infer ``Γ, A∧B ⊢ Δ``."""
    if len(prems) != 1:
        return "∧L has one premise"
    for principal, rest in _candidates(concl.antecedent, lambda f: isinstance(f, And)):
        if _seq_eq(prems[0], rest + (principal.left, principal.right), concl.succedent):
            return None
    return "∧L: needs A∧B on the left; premise Γ, A, B ⊢ Δ"


def _r_and_r(concl, prems, extra):
    """∧R: from ``Γ ⊢ Δ, A`` and ``Γ ⊢ Δ, B`` infer ``Γ ⊢ Δ, A∧B``."""
    if len(prems) != 2:
        return "∧R has two premises"
    for principal, rest in _candidates(concl.succedent, lambda f: isinstance(f, And)):
        w1 = (concl.antecedent, rest + (principal.left,))
        w2 = (concl.antecedent, rest + (principal.right,))
        if _two_match(prems, w1, w2):
            return None
    return "∧R: needs A∧B on the right; premises Γ⊢Δ,A and Γ⊢Δ,B"


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


def _r_or_r(concl, prems, extra):
    """∨R: from ``Γ ⊢ Δ, A, B`` infer ``Γ ⊢ Δ, A∨B``."""
    if len(prems) != 1:
        return "∨R has one premise"
    for principal, rest in _candidates(concl.succedent, lambda f: isinstance(f, Or)):
        if _seq_eq(prems[0], concl.antecedent, rest + (principal.left, principal.right)):
            return None
    return "∨R: needs A∨B on the right; premise Γ ⊢ Δ, A, B"


def _r_imp_l(concl, prems, extra):
    """→L: from ``Γ ⊢ Δ, A`` and ``Γ, B ⊢ Δ`` infer ``Γ, A→B ⊢ Δ``."""
    if len(prems) != 2:
        return "→L has two premises"
    for principal, rest in _candidates(concl.antecedent, lambda f: isinstance(f, Implies)):
        w1 = (rest, concl.succedent + (principal.left,))
        w2 = (rest + (principal.right,), concl.succedent)
        if _two_match(prems, w1, w2):
            return None
    return "→L: needs A→B on the left; premises Γ⊢Δ,A and Γ,B⊢Δ"


def _r_imp_r(concl, prems, extra):
    """→R: from ``Γ, A ⊢ Δ, B`` infer ``Γ ⊢ Δ, A→B``."""
    if len(prems) != 1:
        return "→R has one premise"
    for principal, rest in _candidates(concl.succedent, lambda f: isinstance(f, Implies)):
        if _seq_eq(prems[0], concl.antecedent + (principal.left,), rest + (principal.right,)):
            return None
    return "→R: needs A→B on the right; premise Γ, A ⊢ Δ, B"


def _r_iff_l(concl, prems, extra):
    """↔L: from ``Γ, A, B ⊢ Δ`` and ``Γ ⊢ Δ, A, B`` infer ``Γ, A↔B ⊢ Δ``."""
    if len(prems) != 2:
        return "↔L has two premises"
    for principal, rest in _candidates(concl.antecedent, lambda f: isinstance(f, Iff)):
        a, b = principal.left, principal.right
        w1 = (rest + (a, b), concl.succedent)
        w2 = (rest, concl.succedent + (a, b))
        if _two_match(prems, w1, w2):
            return None
    return "↔L: needs A↔B on the left; premises Γ,A,B⊢Δ and Γ⊢Δ,A,B"


def _r_iff_r(concl, prems, extra):
    """↔R: from ``Γ, A ⊢ Δ, B`` and ``Γ, B ⊢ Δ, A`` infer ``Γ ⊢ Δ, A↔B``."""
    if len(prems) != 2:
        return "↔R has two premises"
    for principal, rest in _candidates(concl.succedent, lambda f: isinstance(f, Iff)):
        a, b = principal.left, principal.right
        w1 = (concl.antecedent + (a,), rest + (b,))
        w2 = (concl.antecedent + (b,), rest + (a,))
        if _two_match(prems, w1, w2):
            return None
    return "↔R: needs A↔B on the right; premises Γ,A⊢Δ,B and Γ,B⊢Δ,A"


def _r_xor_l(concl, prems, extra):
    """⊕L: from ``Γ, A ⊢ Δ, B`` and ``Γ, B ⊢ Δ, A`` infer ``Γ, A⊕B ⊢ Δ``.

    ``A⊕B ≡ ¬(A↔B)``, so ⊕L mirrors ↔R (one side negated).
    """
    if len(prems) != 2:
        return "⊕L has two premises"
    for principal, rest in _candidates(concl.antecedent, lambda f: isinstance(f, Xor)):
        a, b = principal.left, principal.right
        w1 = (rest + (a,), concl.succedent + (b,))
        w2 = (rest + (b,), concl.succedent + (a,))
        if _two_match(prems, w1, w2):
            return None
    return "⊕L: needs A⊕B on the left; premises Γ,A⊢Δ,B and Γ,B⊢Δ,A"


def _r_xor_r(concl, prems, extra):
    """⊕R: from ``Γ, A, B ⊢ Δ`` and ``Γ ⊢ Δ, A, B`` infer ``Γ ⊢ Δ, A⊕B``.

    ``A⊕B ≡ ¬(A↔B)``, so ⊕R mirrors ↔L.
    """
    if len(prems) != 2:
        return "⊕R has two premises"
    for principal, rest in _candidates(concl.succedent, lambda f: isinstance(f, Xor)):
        a, b = principal.left, principal.right
        w1 = (concl.antecedent + (a, b), rest)
        w2 = (concl.antecedent, rest + (a, b))
        if _two_match(prems, w1, w2):
            return None
    return "⊕R: needs A⊕B on the right; premises Γ,A,B⊢Δ and Γ⊢Δ,A,B"


def _two_match(prems: List[Sequent], w1, w2) -> bool:
    """Return True iff the two premises equal sequents w1 and w2 in either order."""
    a, b = prems
    return ((_seq_eq(a, *w1) and _seq_eq(b, *w2))
            or (_seq_eq(a, *w2) and _seq_eq(b, *w1)))


_PROP_RULES: Dict[str, RuleFn] = {
    "Ax": _r_axiom,
    "WL": _r_weaken_l, "WR": _r_weaken_r,
    "CL": _r_contract_l, "CR": _r_contract_r,
    "Cut": _r_cut,
    "¬L": _r_not_l, "¬R": _r_not_r,
    "∧L": _r_and_l, "∧R": _r_and_r,
    "∨L": _r_or_l, "∨R": _r_or_r,
    "→L": _r_imp_l, "→R": _r_imp_r,
    "↔L": _r_iff_l, "↔R": _r_iff_r,
    "⊕L": _r_xor_l, "⊕R": _r_xor_r,
}


# ---------------------------------------------------------------------------
# Rule checkers — first-order quantifiers
# ---------------------------------------------------------------------------

def _eigenvar_not_free(a: Variable, seq: Sequent) -> Optional[str]:
    """Return an error if object eigenvariable ``a`` occurs free in the lower sequent."""
    for f in seq.antecedent + seq.succedent:
        if a in _free_vars(f):
            return (f"eigenvariable {a.name} occurs free in the lower sequent "
                    f"({f.to_unicode_str()})")
    return None


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
    """∃R: from ``Γ ⊢ Δ, A[x:=t]`` infer ``Γ ⊢ Δ, ∃x A`` (t any term, in extra)."""
    if len(prems) != 1:
        return "∃R has one premise"
    if len(extra) != 1 or not _is_term(extra[0]):
        return "∃R needs the witness term in extra"
    t = extra[0]
    for principal, rest in _candidates(concl.succedent, lambda f: _q_kind(f) == "∃"):
        inst = _subst_var(principal.formula, principal.variable, t)
        if _seq_eq(prems[0], concl.antecedent, rest + (inst,)):
            return None
    return "needs ∃x A on the right and premise Γ ⊢ Δ, A[x:=t]"


def _r_forall_r(concl, prems, extra):
    """∀R: from ``Γ ⊢ Δ, A[x:=a]`` infer ``Γ ⊢ Δ, ∀x A`` (eigenvariable a, in extra)."""
    if len(prems) != 1:
        return "∀R has one premise"
    if len(extra) != 1 or not isinstance(extra[0], Variable):
        return "∀R needs the eigenvariable in extra"
    a = extra[0]
    for principal, rest in _candidates(concl.succedent, lambda f: _q_kind(f) == "∀"):
        inst = _subst_var(principal.formula, principal.variable, a)
        if _seq_eq(prems[0], concl.antecedent, rest + (inst,)):
            err = _eigenvar_not_free(a, concl)
            return err if err else None
    return "needs ∀x A on the right and premise Γ ⊢ Δ, A[x:=a]"


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


_FO_RULES: Dict[str, RuleFn] = {
    "∀L": _r_forall_l, "∀R": _r_forall_r,
    "∃L": _r_exists_l, "∃R": _r_exists_r,
}


# ---------------------------------------------------------------------------
# Second-order machinery: predicate substitution + free predicate variables
# ---------------------------------------------------------------------------

def _so_kind(node: Node) -> Optional[str]:
    """Normalise a SecondOrderQuantifier to '∀' / '∃', or None for other nodes."""
    if isinstance(node, SecondOrderQuantifier):
        if node.type in ("∀", "forall"):
            return "∀"
        if node.type in ("∃", "exists"):
            return "∃"
    return None


def _free_pred_vars(node: Node, bound: frozenset = frozenset()) -> set:
    """Return predicate names applied free in ``node`` (not bound by an enclosing ∀²/∃²).

    ``=`` / ``≠`` are excluded (built-in identity, never a predicate variable). Used
    for the second-order eigenvariable freshness condition.
    """
    if isinstance(node, SecondOrderQuantifier):
        return _free_pred_vars(node.formula, bound | {node.predicate})
    result: set = set()
    if isinstance(node, Atom):
        if node.predicate not in ("=", "≠") and node.predicate not in bound:
            result.add(node.predicate)
    for child in node._child_nodes():
        result |= _free_pred_vars(child, bound)
    return result


def _all_pred_names(node: Node) -> set:
    """Return every predicate name occurring in ``node`` (applied or as an ∀²/∃² binder).

    Includes bound predicate names (needed for freshness), excludes ``=`` / ``≠``.
    """
    names: set = set()
    for n in node.walk():
        if isinstance(n, Atom) and n.predicate not in ("=", "≠"):
            names.add(n.predicate)
        elif isinstance(n, SecondOrderQuantifier):
            names.add(n.predicate)
    return names


def _fresh_pred_name(base: str, avoid: set) -> str:
    """Return the first ``base_N`` (N = 0, 1, …) not in ``avoid``."""
    i = 0
    while True:
        candidate = f"{base}_{i}"
        if candidate not in avoid:
            return candidate
        i += 1


def _rename_pred(node: Node, x_name: str, y_name: str) -> Node:
    """Rename the (free) predicate variable ``x_name`` to ``y_name`` throughout ``node``.

    Capture-avoiding in BOTH directions: it stops at an inner ∀²/∃² that rebinds the
    SOURCE ``x_name`` (shadowing), and α-renames an inner ∀²/∃² that binds the
    TARGET ``y_name`` to a fresh predicate name first, so the introduced ``Y(…)``
    atoms are never captured by an inner binder of the same name. Used for the
    predicate-eigenvariable instantiation A[X:=Y] of ∀²R / ∃²L.
    """
    if isinstance(node, SecondOrderQuantifier):
        if node.predicate == x_name:
            return node  # source rebound here: occurrences below are shadowed
        if node.predicate == y_name and x_name != y_name:
            # The inner binder would capture the introduced target name; α-rename it.
            avoid = _all_pred_names(node.formula) | {x_name, y_name}
            fresh = _fresh_pred_name(y_name, avoid)
            renamed_body = _rename_pred(node.formula, y_name, fresh)
            return SecondOrderQuantifier(node.type, fresh, node.arity,
                                         _rename_pred(renamed_body, x_name, y_name))
        return SecondOrderQuantifier(node.type, node.predicate, node.arity,
                                     _rename_pred(node.formula, x_name, y_name))
    if isinstance(node, Atom) and node.predicate == x_name and x_name not in ("=", "≠"):
        return Atom(y_name, node.args)
    return node.map_children(lambda c: _rename_pred(c, x_name, y_name))


def _subst_simultaneous(psi: Node, params: Tuple[Variable, ...], args) -> Node:
    """Return ``ψ[x̄ := t̄]`` — simultaneous capture-avoiding object substitution.

    Each parameter is first routed through a fresh temporary so that a later
    argument mentioning an earlier parameter's name cannot interfere.
    """
    if not params:
        return psi
    avoid = _free_vars(psi)
    for arg in args:
        avoid = avoid | _free_vars(arg)
    avoid = avoid | set(params)
    result = psi
    temps: List[Variable] = []
    for p in params:
        tmp = Variable(_fresh_name("_c", avoid))
        avoid = avoid | {tmp}
        result = _subst_var(result, p, tmp)
        temps.append(tmp)
    for tmp, arg in zip(temps, args):
        result = _subst_var(result, tmp, arg)
    return result


def _subst_pred(node: Node, x_name: str, params: Tuple[Variable, ...], psi: Node) -> Node:
    """Return ``A[X := λx̄.ψ]`` — capture-avoiding comprehension instantiation.

    Replaces each free application ``X(t̄)`` by ``ψ[x̄ := t̄]``. Stops at an inner
    ∀²/∃² that rebinds ``X``; α-renames an object binder of ``A`` that would capture
    a free OBJECT variable of ``ψ``, and an inner ∀²/∃² binder of ``A`` that would
    capture a free PREDICATE variable of ``ψ``. Raises ValueError on an application
    of ``X`` whose arity differs from ``len(params)``.
    """
    psi_fv = _free_vars(psi) - set(params)
    psi_pred_fv = _free_pred_vars(psi)
    return _subst_pred_inner(node, x_name, params, psi, psi_fv, psi_pred_fv)


def _subst_pred_inner(node, x_name, params, psi, psi_fv, psi_pred_fv):
    """Recursive worker for :func:`_subst_pred`."""
    if isinstance(node, SecondOrderQuantifier) and node.predicate == x_name:
        return node  # inner binder shadows X
    if isinstance(node, Atom) and node.predicate == x_name and x_name not in ("=", "≠"):
        if len(node.args) != len(params):
            raise ValueError(
                f"comprehension arity {len(params)} does not match an application "
                f"of {x_name} at arity {len(node.args)}"
            )
        return _subst_simultaneous(psi, params, node.args)
    if isinstance(node, (Quantifier, SortedQuantifier)):
        y = node.variable
        body = node.formula
        if y in psi_fv:
            # An object binder of A would capture a free object variable of ψ.
            avoid = psi_fv | _free_vars(body) | {y}
            fresh = Variable(_fresh_name(y.name, avoid))
            body = _rename(body, y, fresh)
            y = fresh
        inner = _subst_pred_inner(body, x_name, params, psi, psi_fv, psi_pred_fv)
        if isinstance(node, Quantifier):
            return Quantifier(node.type, y, inner)
        return SortedQuantifier(node.type, y, node.sort, inner)
    if isinstance(node, SecondOrderQuantifier):
        pred = node.predicate
        body = node.formula
        if pred in psi_pred_fv:
            # A second-order binder of A would capture a free predicate variable of ψ.
            avoid = psi_pred_fv | _all_pred_names(body) | {x_name, pred}
            fresh = _fresh_pred_name(pred, avoid)
            body = _rename_pred(body, pred, fresh)
            pred = fresh
        return SecondOrderQuantifier(
            node.type, pred, node.arity,
            _subst_pred_inner(body, x_name, params, psi, psi_fv, psi_pred_fv))
    return node.map_children(
        lambda c: _subst_pred_inner(c, x_name, params, psi, psi_fv, psi_pred_fv))


def _pred_eigenvar_not_free(y_name: str, seq: Sequent) -> Optional[str]:
    """Return an error if predicate eigenvariable ``y_name`` occurs free in the sequent."""
    for f in seq.antecedent + seq.succedent:
        if y_name in _free_pred_vars(f):
            return (f"predicate eigenvariable {y_name} occurs free in the lower "
                    f"sequent ({f.to_unicode_str()})")
    return None


# ---------------------------------------------------------------------------
# Rule checkers — second-order quantifiers
# ---------------------------------------------------------------------------

def _r_so_forall_l(concl, prems, extra):
    """∀²L: from ``Γ, A[X:=λx̄.ψ] ⊢ Δ`` infer ``Γ, ∀X A ⊢ Δ`` (Comprehension in extra)."""
    if len(prems) != 1:
        return "∀²L has one premise"
    if len(extra) != 1 or not isinstance(extra[0], Comprehension):
        return "∀²L needs a Comprehension λx̄.ψ in extra"
    comp = extra[0]
    for principal, rest in _candidates(concl.antecedent, lambda f: _so_kind(f) == "∀"):
        if comp.arity != principal.arity:
            continue
        try:
            inst = _subst_pred(principal.formula, principal.predicate, comp.params, comp.body)
        except ValueError:
            continue
        if _seq_eq(prems[0], rest + (inst,), concl.succedent):
            return None
    return "needs ∀X A on the left and premise Γ, A[X:=λx̄.ψ] ⊢ Δ (arity must match)"


def _r_so_exists_r(concl, prems, extra):
    """∃²R: from ``Γ ⊢ Δ, A[X:=λx̄.ψ]`` infer ``Γ ⊢ Δ, ∃X A`` (Comprehension in extra)."""
    if len(prems) != 1:
        return "∃²R has one premise"
    if len(extra) != 1 or not isinstance(extra[0], Comprehension):
        return "∃²R needs a Comprehension λx̄.ψ in extra"
    comp = extra[0]
    for principal, rest in _candidates(concl.succedent, lambda f: _so_kind(f) == "∃"):
        if comp.arity != principal.arity:
            continue
        try:
            inst = _subst_pred(principal.formula, principal.predicate, comp.params, comp.body)
        except ValueError:
            continue
        if _seq_eq(prems[0], concl.antecedent, rest + (inst,)):
            return None
    return "needs ∃X A on the right and premise Γ ⊢ Δ, A[X:=λx̄.ψ] (arity must match)"


def _r_so_forall_r(concl, prems, extra):
    """∀²R: from ``Γ ⊢ Δ, A[X:=Y]`` infer ``Γ ⊢ Δ, ∀X A`` (predicate eigenvariable Y)."""
    if len(prems) != 1:
        return "∀²R has one premise"
    if len(extra) != 1 or not isinstance(extra[0], str):
        return "∀²R needs the predicate-eigenvariable name (a str) in extra"
    y_name = extra[0]
    for principal, rest in _candidates(concl.succedent, lambda f: _so_kind(f) == "∀"):
        inst = _rename_pred(principal.formula, principal.predicate, y_name)
        if _seq_eq(prems[0], concl.antecedent, rest + (inst,)):
            err = _pred_eigenvar_not_free(y_name, concl)
            return err if err else None
    return "needs ∀X A on the right and premise Γ ⊢ Δ, A[X:=Y]"


def _r_so_exists_l(concl, prems, extra):
    """∃²L: from ``Γ, A[X:=Y] ⊢ Δ`` infer ``Γ, ∃X A ⊢ Δ`` (predicate eigenvariable Y)."""
    if len(prems) != 1:
        return "∃²L has one premise"
    if len(extra) != 1 or not isinstance(extra[0], str):
        return "∃²L needs the predicate-eigenvariable name (a str) in extra"
    y_name = extra[0]
    for principal, rest in _candidates(concl.antecedent, lambda f: _so_kind(f) == "∃"):
        inst = _rename_pred(principal.formula, principal.predicate, y_name)
        if _seq_eq(prems[0], rest + (inst,), concl.succedent):
            err = _pred_eigenvar_not_free(y_name, concl)
            return err if err else None
    return "needs ∃X A on the left and premise Γ, A[X:=Y] ⊢ Δ"


_SO_RULES: Dict[str, RuleFn] = {
    "∀²L": _r_so_forall_l, "∀²R": _r_so_forall_r,
    "∃²L": _r_so_exists_l, "∃²R": _r_so_exists_r,
}


_RULES: Dict[str, RuleFn] = {**_PROP_RULES, **_FO_RULES, **_SO_RULES}


# ---------------------------------------------------------------------------
# The checker
# ---------------------------------------------------------------------------

def _canon(node: Node) -> Node:
    """Canonicalise quantifier spellings ('forall'/'exists' → '∀'/'∃') throughout.

    Quantifier nodes are keyed on the raw ``type`` string, so the multiset ``==``
    the sequent rules rely on would falsely reject a derivation that mixed the glyph
    and word spellings. Normalising every formula entering the checker prevents that.
    """
    node = node.map_children(_canon)
    if isinstance(node, Quantifier) and node.type in ("forall", "exists"):
        return Quantifier("∀" if node.type == "forall" else "∃", node.variable, node.formula)
    if isinstance(node, SortedQuantifier) and node.type in ("forall", "exists"):
        return SortedQuantifier("∀" if node.type == "forall" else "∃",
                                node.variable, node.sort, node.formula)
    if isinstance(node, SecondOrderQuantifier) and node.type in ("forall", "exists"):
        return SecondOrderQuantifier("∀" if node.type == "forall" else "∃",
                                     node.predicate, node.arity, node.formula)
    return node


def _canon_extra(item):
    """Canonicalise one ``extra`` payload (Comprehension body / Node), else pass through."""
    if isinstance(item, Comprehension):
        return Comprehension(item.params, _canon(item.body))
    if isinstance(item, Node):
        return _canon(item)
    return item


def _canon_derivation(d: "Derivation") -> "Derivation":
    """Rebuild a derivation tree with every sequent formula quantifier-canonicalised."""
    conclusion = Sequent(tuple(_canon(f) for f in d.conclusion.antecedent),
                         tuple(_canon(f) for f in d.conclusion.succedent))
    premises = tuple(_canon_derivation(p) for p in d.premises)
    extra = tuple(_canon_extra(e) for e in d.extra)
    return Derivation(conclusion, d.rule, premises, extra)


def verify_sequent_proof(derivation: "Derivation") -> SequentResult:
    """Check ``derivation`` and return a :class:`SequentResult`.

    Recursively verifies that every node's conclusion follows from its premises'
    conclusions by the node's rule, returning the end-sequent and, on failure, the
    first offending rule and reason.
    """
    if isinstance(derivation, Derivation):
        derivation = _canon_derivation(derivation)
    err_rule, err = _verify(derivation)
    end = derivation.conclusion if derivation is not None else None
    return SequentResult(err is None, end, err_rule, err)


def _verify(deriv: "Derivation"):
    """Recursive worker: return ``(rule, error)`` or ``(None, None)`` on success."""
    if not isinstance(deriv, Derivation):
        return ("?", f"expected a Derivation, got {type(deriv).__name__}")
    # Children first, so the deepest error surfaces.
    for child in deriv.premises:
        rule, err = _verify(child)
        if err is not None:
            return rule, err
    fn = _RULES.get(deriv.rule)
    if fn is None:
        return deriv.rule, f"unknown rule {deriv.rule!r}"
    premise_sequents = [c.conclusion for c in deriv.premises]
    err = fn(deriv.conclusion, premise_sequents, deriv.extra)
    if err is not None:
        return deriv.rule, f"{deriv.rule}: {err}" if not err.startswith(deriv.rule) else err
    return None, None


def check_sequent_proof(derivation: "Derivation") -> bool:
    """Return True iff ``derivation`` is a valid sequent-calculus derivation (sound)."""
    return verify_sequent_proof(derivation).ok


# ---------------------------------------------------------------------------
# Rendering
# ---------------------------------------------------------------------------

def _fmt_extra(extra: tuple) -> str:
    """Render a rule's ``extra`` payload as a short annotation."""
    if not extra:
        return ""
    parts = []
    for e in extra:
        if isinstance(e, Comprehension):
            params = ",".join(p.name for p in e.params)
            parts.append(f"λ{params}.{e.body.to_unicode_str()}")
        elif isinstance(e, Node):
            parts.append(e.to_unicode_str())
        else:
            parts.append(str(e))
    return " " + ", ".join(parts)


def render_sequent_proof(derivation: "Derivation", indent: int = 0) -> str:
    """Render a derivation as an indented proof tree (conclusion first, premises below).

    Each line is ``Γ ⊢ Δ   [rule extra]``; a rule's premises are nested one level
    deeper. (The visual sequent-calculus convention draws premises *above* the
    conclusion; this indented form is the same tree, easier to read in a terminal.)
    """
    pad = "  " * indent
    label = f"   [{derivation.rule}{_fmt_extra(derivation.extra)}]"
    lines = [f"{pad}{derivation.conclusion}{label}"]
    for premise in derivation.premises:
        lines.append(render_sequent_proof(premise, indent + 1))
    return "\n".join(lines)
