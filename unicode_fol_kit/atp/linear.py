"""Intuitionistic linear logic (ILL) — cut-free backward proof search + a checker.

The single-succedent two-sided sequent calculus for propositional ILL: a sequent is
``Γ ⊢ C`` with ``Γ`` a **multiset** of formulas (exchange is implicit; weakening and
contraction are NOT available on plain formulas — that is the whole point) and ``C``
a single formula. The connectives are the ``linear`` parser mode's
(:mod:`unicode_fol_kit.fol._linear_nodes`): ``⊗`` / ``&`` / ``⊕`` / ``⊸`` / ``!`` / ``𝟙``.

Rules (Girard's ILL, cut-free)::

    Ax:  A ⊢ A
    1R:  ⊢ 𝟙                    1L:  Γ ⊢ C          ⇒  Γ, 𝟙 ⊢ C
    ⊗L:  Γ, A, B ⊢ C            ⇒  Γ, A⊗B ⊢ C
    ⊗R:  Γ ⊢ A   and  Δ ⊢ B     ⇒  Γ, Δ ⊢ A⊗B          (the context SPLITS)
    ⊸L:  Γ ⊢ A   and  Δ, B ⊢ C  ⇒  Γ, Δ, A⊸B ⊢ C       (the context SPLITS)
    ⊸R:  Γ, A ⊢ B               ⇒  Γ ⊢ A⊸B
    &L1: Γ, A ⊢ C               ⇒  Γ, A&B ⊢ C     (&L2 likewise with B)
    &R:  Γ ⊢ A   and  Γ ⊢ B     ⇒  Γ ⊢ A&B            (the context is SHARED)
    ⊕L:  Γ, A ⊢ C and Γ, B ⊢ C  ⇒  Γ, A⊕B ⊢ C
    ⊕R1: Γ ⊢ A                  ⇒  Γ ⊢ A⊕B      (⊕R2 likewise with B)
    !W:  Γ ⊢ C                  ⇒  Γ, !A ⊢ C     (weakening — only under !)
    !C:  Γ, !A, !A ⊢ C          ⇒  Γ, !A ⊢ C     (contraction — only under !)
    !D:  Γ, A ⊢ C               ⇒  Γ, !A ⊢ C     (dereliction)
    !P:  !Γ ⊢ A                 ⇒  !Γ ⊢ !A       (promotion: every antecedent !-prefixed)

**Decidability status.** For the **!-free fragment** every rule's premises have
strictly smaller total size (node count) than its conclusion, so the backward search
below — exhaustive over rule instances, memoised on ``(antecedent multiset, goal)`` —
is a **complete, terminating decision procedure**: ``ill_prove`` returning ``None``
*proves* underivability, and the default depth bound (the sequent's total size, which
no cut-free proof of it can exceed) is never the reason a proof is missed. When ``!``
occurs, the ``!C`` rule *grows* sequents and the naive search space is infinite; the
search is then depth- and step-bounded and ``None`` means only "no proof found within
the bound" — honest, but not a refutation.

Deliberately, there is **no classical export**: the collapse ⊗,& → ∧, ⊕ → ∨, ⊸ → →,
drop ! erases exactly the resource distinctions ILL draws (it is *sound* — every ILL
theorem collapses to a classical one, which the test-suite checks against Z3 — but
wildly incomplete in reverse).

Public API: :class:`ILLSequent`, :class:`ILLDerivation`, :func:`ill_prove`,
:func:`ill_derivable`, :func:`check_ill_proof`, :func:`verify_ill_proof`,
:func:`render_ill_proof`.
"""

from collections import Counter
from dataclasses import dataclass
from itertools import product as _iproduct
from typing import Callable, Dict, Iterable, List, Optional, Tuple

from ..fol.nodes import Node, Tensor, With, OPlus, LinearImplies, OfCourse, One
from .sequent import SequentResult


# ---------------------------------------------------------------------------
# Sequents and derivations
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class ILLSequent:
    """A single-succedent linear sequent ``antecedent ⊢ succedent``.

    ``antecedent`` is a tuple of formulas read as a **multiset** (order never
    matters, multiplicity always does — there is no weakening or contraction on
    plain formulas); ``succedent`` is one formula. Frozen and hashable.
    """

    antecedent: Tuple[Node, ...]
    succedent: Node

    def __post_init__(self):
        """Coerce the antecedent to a tuple so the sequent stays hashable."""
        object.__setattr__(self, "antecedent", tuple(self.antecedent))

    def __str__(self) -> str:
        """Render as ``A, B ⊢ C`` using each formula's Unicode form."""
        left = ", ".join(f.to_unicode_str() for f in self.antecedent)
        return f"{left} ⊢ {self.succedent.to_unicode_str()}".strip()


@dataclass(frozen=True)
class ILLDerivation:
    """A node of an ILL derivation tree.

    ``conclusion`` is the sequent this node derives; ``rule`` is the rule name
    (``"Ax"``, ``"⊗R"``, ``"!C"``, …); ``premises`` are the sub-derivations whose
    conclusions are this rule's premises (empty for ``Ax`` / ``1R``).
    """

    conclusion: ILLSequent
    rule: str
    premises: Tuple["ILLDerivation", ...] = ()

    def __post_init__(self):
        """Coerce ``premises`` to a tuple so the derivation stays hashable."""
        object.__setattr__(self, "premises", tuple(self.premises))

    def render(self) -> str:
        """Render this derivation as an indented proof tree."""
        return render_ill_proof(self)


def render_ill_proof(derivation: "ILLDerivation", indent: int = 0) -> str:
    """Render a derivation as an indented tree (conclusion first, premises below)."""
    pad = "  " * indent
    lines = [f"{pad}{derivation.conclusion}   [{derivation.rule}]"]
    for premise in derivation.premises:
        lines.append(render_ill_proof(premise, indent + 1))
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Multiset helpers
# ---------------------------------------------------------------------------

def _norm(cnt: Counter) -> Counter:
    """Return ``cnt`` with non-positive entries stripped (Counter == is dict ==)."""
    return Counter({k: v for k, v in cnt.items() if v > 0})


def _cnt_of(formulas: Iterable[Node]) -> Counter:
    """Return the multiset (Counter) of an iterable of formulas."""
    return Counter(formulas)


def _minus(cnt: Counter, f: Node) -> Counter:
    """Return ``cnt`` with one occurrence of ``f`` removed (caller ensures presence)."""
    out = Counter(cnt)
    out[f] -= 1
    return _norm(out)


def _plus(cnt: Counter, *fs: Node) -> Counter:
    """Return ``cnt`` with one occurrence of each of ``fs`` added."""
    out = Counter(cnt)
    for f in fs:
        out[f] += 1
    return out


def _tuple_of(cnt: Counter) -> Tuple[Node, ...]:
    """Expand a multiset to a deterministic tuple (sorted by Unicode rendering)."""
    out: List[Node] = []
    for f in sorted(cnt.keys(), key=lambda n: (n.to_unicode_str(), repr(n))):
        out.extend([f] * cnt[f])
    return tuple(out)


def _key(cnt: Counter, goal: Node):
    """Return a hashable memo key for the sequent ``cnt ⊢ goal``."""
    return (frozenset(_norm(cnt).items()), goal)


def _splits(cnt: Counter):
    """Yield every split ``(Γ, Δ)`` of a multiset with ``Γ ⊎ Δ = cnt`` (both may be empty)."""
    items = sorted(cnt.items(), key=lambda kv: (kv[0].to_unicode_str(), repr(kv[0])))
    ranges = [range(c + 1) for _, c in items]
    for take in _iproduct(*ranges):
        left = Counter({f: k for (f, _), k in zip(items, take) if k > 0})
        right = Counter({f: c - k for (f, c), k in zip(items, take) if c - k > 0})
        yield left, right


def _size(f: Node) -> int:
    """Return the node count of a formula (atoms and 𝟙 count 1)."""
    return 1 + sum(_size(c) for c in f._child_nodes())


def _has_bang(f: Node) -> bool:
    """Return True iff ``!`` occurs anywhere in the formula."""
    return any(isinstance(n, OfCourse) for n in f.walk())


# ---------------------------------------------------------------------------
# Backward proof search
# ---------------------------------------------------------------------------

class _IllSearch:
    """Holds the memo tables and the (optional) step budget of one search run."""

    def __init__(self, budget: Optional[int]):
        self.proven: Dict = {}      # key -> ILLDerivation
        self.failed: Dict = {}      # key -> largest depth budget it failed with
        self.steps = budget         # None = unbounded (the !-free decision procedure)

    def spend(self) -> bool:
        """Consume one step of the budget; return False when it is exhausted."""
        if self.steps is None:
            return True
        if self.steps <= 0:
            return False
        self.steps -= 1
        return True


def _attempts(cnt: Counter, goal: Node):
    """Yield ``(rule, [premise (multiset, goal) pairs])`` for every rule instance.

    Backward reading of every ILL rule whose conclusion matches ``cnt ⊢ goal``.
    Ordered cheapest-first (non-branching size reducers before context splits;
    the sequent-growing ``!C`` last), which is a heuristic only — the search
    tries them all.
    """
    distinct = sorted(cnt.keys(), key=lambda n: (n.to_unicode_str(), repr(n)))

    # Non-branching left rules that strictly shrink the sequent.
    for f in distinct:
        if isinstance(f, One):
            yield "1L", [(_minus(cnt, f), goal)]
        elif isinstance(f, Tensor):
            yield "⊗L", [(_plus(_minus(cnt, f), f.left, f.right), goal)]
        elif isinstance(f, OfCourse):
            yield "!D", [(_plus(_minus(cnt, f), f.formula), goal)]

    # Right rules on the goal's main connective.
    if isinstance(goal, LinearImplies):
        yield "⊸R", [(_plus(cnt, goal.left), goal.right)]
    elif isinstance(goal, With):
        yield "&R", [(cnt, goal.left), (cnt, goal.right)]
    elif isinstance(goal, OPlus):
        yield "⊕R1", [(cnt, goal.left)]
        yield "⊕R2", [(cnt, goal.right)]
    elif isinstance(goal, Tensor):
        for left, right in _splits(cnt):
            yield "⊗R", [(left, goal.left), (right, goal.right)]
    elif isinstance(goal, OfCourse):
        if all(isinstance(f, OfCourse) for f in cnt):
            yield "!P", [(cnt, goal.formula)]

    # Branching / choice left rules.
    for f in distinct:
        if isinstance(f, With):
            rest = _minus(cnt, f)
            yield "&L1", [(_plus(rest, f.left), goal)]
            yield "&L2", [(_plus(rest, f.right), goal)]
        elif isinstance(f, OPlus):
            rest = _minus(cnt, f)
            yield "⊕L", [(_plus(rest, f.left), goal), (_plus(rest, f.right), goal)]
        elif isinstance(f, LinearImplies):
            rest = _minus(cnt, f)
            for left, right in _splits(rest):
                yield "⊸L", [(left, f.left), (_plus(right, f.right), goal)]

    # The remaining exponential structure: weakening, then sequent-growing contraction.
    for f in distinct:
        if isinstance(f, OfCourse):
            yield "!W", [(_minus(cnt, f), goal)]
    for f in distinct:
        if isinstance(f, OfCourse):
            yield "!C", [(_plus(cnt, f), goal)]


def _prove(cnt: Counter, goal: Node, depth: int, search: _IllSearch) -> Optional[ILLDerivation]:
    """Backward search for a derivation of ``cnt ⊢ goal`` within ``depth`` rule steps."""
    cnt = _norm(cnt)
    key = _key(cnt, goal)
    hit = search.proven.get(key)
    if hit is not None:
        return hit
    if search.failed.get(key, -1) >= depth:
        return None
    if not search.spend():
        return None

    # Leaves.
    if sum(cnt.values()) == 1 and next(iter(cnt)) == goal:
        d = ILLDerivation(ILLSequent(_tuple_of(cnt), goal), "Ax")
        search.proven[key] = d
        return d
    if not cnt and isinstance(goal, One):
        d = ILLDerivation(ILLSequent((), goal), "1R")
        search.proven[key] = d
        return d

    if depth > 0:
        for rule, premises in _attempts(cnt, goal):
            subs: List[ILLDerivation] = []
            for (pc, pg) in premises:
                sub = _prove(pc, pg, depth - 1, search)
                if sub is None:
                    break
                subs.append(sub)
            else:
                d = ILLDerivation(ILLSequent(_tuple_of(cnt), goal), rule, tuple(subs))
                search.proven[key] = d
                return d

    if search.failed.get(key, -1) < depth:
        search.failed[key] = depth
    return None


def ill_prove(antecedents: Iterable[Node], goal: Node,
              max_depth: Optional[int] = None,
              max_steps: int = 200000) -> Optional[ILLDerivation]:
    """Search for a cut-free ILL derivation of ``antecedents ⊢ goal``.

    Returns an :class:`ILLDerivation` (which :func:`check_ill_proof` re-validates
    before it is handed back, so a search bug can only lose proofs, never invent
    them) or ``None``.

    **What ``None`` means.** For a **!-free** sequent the search is a complete,
    terminating decision procedure — every rule's premises are strictly smaller
    than its conclusion, so with the default ``max_depth`` (the sequent's total
    node count, which no cut-free derivation's height can exceed) and no step
    budget, ``None`` *proves* the sequent underivable. When ``!`` occurs the
    contraction rule ``!C`` grows sequents, so the search is bounded (default
    depth ``2·size + 4`` and ``max_steps`` expansions) and ``None`` means only
    "no derivation found within the bound".

    ``max_depth`` counts rule applications along a branch; pass it explicitly to
    search deeper !-sequents. ``max_steps`` bounds total node expansions and is
    ignored for !-free sequents (where it could otherwise break completeness).
    """
    ants = tuple(antecedents)
    cnt = _cnt_of(ants)
    total = sum(_size(f) for f in ants) + _size(goal)
    bang = any(_has_bang(f) for f in ants) or _has_bang(goal)
    if max_depth is None:
        max_depth = 2 * total + 4 if bang else total
    search = _IllSearch(max_steps if bang else None)
    derivation = _prove(cnt, goal, max_depth, search)
    if derivation is not None and not check_ill_proof(derivation):
        raise RuntimeError(
            "internal error: the ILL search assembled a derivation its own "
            "checker rejects — please report this")
    return derivation


def ill_derivable(antecedents: Iterable[Node], goal: Node,
                  max_depth: Optional[int] = None,
                  max_steps: int = 200000) -> bool:
    """Return True iff :func:`ill_prove` finds a derivation of ``antecedents ⊢ goal``.

    Decides derivability for !-free sequents; for sequents containing ``!`` a
    ``False`` means only "no derivation within the bound" (see :func:`ill_prove`).
    """
    return ill_prove(antecedents, goal, max_depth=max_depth, max_steps=max_steps) is not None


# ---------------------------------------------------------------------------
# The checker
# ---------------------------------------------------------------------------
#
# Each rule checker has signature (conclusion: ILLSequent, premises:
# List[ILLSequent]) and returns None when the step is licensed, or an error
# string. Antecedents are compared as multisets throughout.

def _c_eq(a: Counter, b: Counter) -> bool:
    """Multiset equality with zero entries stripped."""
    return _norm(a) == _norm(b)


def _r_ax(concl, prems):
    """Ax: ``A ⊢ A`` — a single antecedent formula equal to the succedent."""
    if prems:
        return "Ax takes no premises"
    if len(concl.antecedent) != 1 or concl.antecedent[0] != concl.succedent:
        return "Ax: the antecedent must be exactly the succedent formula"
    return None


def _r_one_r(concl, prems):
    """1R: ``⊢ 𝟙`` — empty antecedent, unit succedent."""
    if prems:
        return "1R takes no premises"
    if concl.antecedent or not isinstance(concl.succedent, One):
        return "1R: the conclusion must be ⊢ 𝟙 with an empty antecedent"
    return None


def _r_one_l(concl, prems):
    """1L: from ``Γ ⊢ C`` infer ``Γ, 𝟙 ⊢ C``."""
    if len(prems) != 1:
        return "1L has one premise"
    c = _cnt_of(concl.antecedent)
    if not any(isinstance(f, One) for f in c):
        return "1L: needs 𝟙 in the antecedent"
    p = prems[0]
    if p.succedent == concl.succedent and _c_eq(_cnt_of(p.antecedent), _minus(c, One())):
        return None
    return "1L: the premise must be the conclusion minus one 𝟙"


def _r_tensor_l(concl, prems):
    """⊗L: from ``Γ, A, B ⊢ C`` infer ``Γ, A⊗B ⊢ C``."""
    if len(prems) != 1:
        return "⊗L has one premise"
    c, p = _cnt_of(concl.antecedent), prems[0]
    for f in c:
        if isinstance(f, Tensor):
            want = _plus(_minus(c, f), f.left, f.right)
            if p.succedent == concl.succedent and _c_eq(_cnt_of(p.antecedent), want):
                return None
    return "⊗L: needs A⊗B on the left; premise Γ, A, B ⊢ C"


def _r_tensor_r(concl, prems):
    """⊗R: from ``Γ ⊢ A`` and ``Δ ⊢ B`` infer ``Γ, Δ ⊢ A⊗B`` (context splits)."""
    if len(prems) != 2:
        return "⊗R has two premises"
    g = concl.succedent
    if not isinstance(g, Tensor):
        return "⊗R must conclude a tensor A⊗B"
    c = _cnt_of(concl.antecedent)
    for p1, p2 in ((prems[0], prems[1]), (prems[1], prems[0])):
        if (p1.succedent == g.left and p2.succedent == g.right
                and _c_eq(_cnt_of(p1.antecedent) + _cnt_of(p2.antecedent), c)):
            return None
    return "⊗R: premises Γ⊢A and Δ⊢B with Γ⊎Δ the conclusion's antecedent"


def _r_limp_l(concl, prems):
    """⊸L: from ``Γ ⊢ A`` and ``Δ, B ⊢ C`` infer ``Γ, Δ, A⊸B ⊢ C`` (context splits)."""
    if len(prems) != 2:
        return "⊸L has two premises"
    c = _cnt_of(concl.antecedent)
    for f in c:
        if not isinstance(f, LinearImplies):
            continue
        rest = _minus(c, f)
        for p1, p2 in ((prems[0], prems[1]), (prems[1], prems[0])):
            if p1.succedent != f.left or p2.succedent != concl.succedent:
                continue
            p2c = _cnt_of(p2.antecedent)
            if p2c[f.right] < 1:
                continue
            if _c_eq(_cnt_of(p1.antecedent) + _minus(p2c, f.right), rest):
                return None
    return "⊸L: needs A⊸B on the left; premises Γ⊢A and Δ,B⊢C with Γ⊎Δ the rest"


def _r_limp_r(concl, prems):
    """⊸R: from ``Γ, A ⊢ B`` infer ``Γ ⊢ A⊸B``."""
    if len(prems) != 1:
        return "⊸R has one premise"
    g = concl.succedent
    if not isinstance(g, LinearImplies):
        return "⊸R must conclude a linear implication A⊸B"
    p = prems[0]
    if (p.succedent == g.right
            and _c_eq(_cnt_of(p.antecedent), _plus(_cnt_of(concl.antecedent), g.left))):
        return None
    return "⊸R: the premise must be Γ, A ⊢ B"


def _with_l(concl, prems, take_left: bool):
    """Shared worker for &L1 / &L2."""
    name = "&L1" if take_left else "&L2"
    if len(prems) != 1:
        return f"{name} has one premise"
    c, p = _cnt_of(concl.antecedent), prems[0]
    for f in c:
        if isinstance(f, With):
            kept = f.left if take_left else f.right
            if (p.succedent == concl.succedent
                    and _c_eq(_cnt_of(p.antecedent), _plus(_minus(c, f), kept))):
                return None
    return f"{name}: needs A&B on the left; premise keeps the chosen component"


def _r_with_l1(concl, prems):
    """&L1: from ``Γ, A ⊢ C`` infer ``Γ, A&B ⊢ C``."""
    return _with_l(concl, prems, True)


def _r_with_l2(concl, prems):
    """&L2: from ``Γ, B ⊢ C`` infer ``Γ, A&B ⊢ C``."""
    return _with_l(concl, prems, False)


def _r_with_r(concl, prems):
    """&R: from ``Γ ⊢ A`` and ``Γ ⊢ B`` infer ``Γ ⊢ A&B`` (context shared)."""
    if len(prems) != 2:
        return "&R has two premises"
    g = concl.succedent
    if not isinstance(g, With):
        return "&R must conclude A&B"
    c = _cnt_of(concl.antecedent)
    for p1, p2 in ((prems[0], prems[1]), (prems[1], prems[0])):
        if (p1.succedent == g.left and p2.succedent == g.right
                and _c_eq(_cnt_of(p1.antecedent), c) and _c_eq(_cnt_of(p2.antecedent), c)):
            return None
    return "&R: premises Γ⊢A and Γ⊢B sharing the conclusion's antecedent"


def _r_oplus_l(concl, prems):
    """⊕L: from ``Γ, A ⊢ C`` and ``Γ, B ⊢ C`` infer ``Γ, A⊕B ⊢ C``."""
    if len(prems) != 2:
        return "⊕L has two premises"
    c = _cnt_of(concl.antecedent)
    for f in c:
        if not isinstance(f, OPlus):
            continue
        rest = _minus(c, f)
        wa, wb = _plus(rest, f.left), _plus(rest, f.right)
        for p1, p2 in ((prems[0], prems[1]), (prems[1], prems[0])):
            if (p1.succedent == concl.succedent and p2.succedent == concl.succedent
                    and _c_eq(_cnt_of(p1.antecedent), wa)
                    and _c_eq(_cnt_of(p2.antecedent), wb)):
                return None
    return "⊕L: needs A⊕B on the left; premises Γ,A⊢C and Γ,B⊢C"


def _oplus_r(concl, prems, take_left: bool):
    """Shared worker for ⊕R1 / ⊕R2."""
    name = "⊕R1" if take_left else "⊕R2"
    if len(prems) != 1:
        return f"{name} has one premise"
    g = concl.succedent
    if not isinstance(g, OPlus):
        return f"{name} must conclude A⊕B"
    p = prems[0]
    want = g.left if take_left else g.right
    if p.succedent == want and _c_eq(_cnt_of(p.antecedent), _cnt_of(concl.antecedent)):
        return None
    return f"{name}: the premise must be Γ ⊢ {'A' if take_left else 'B'}"


def _r_oplus_r1(concl, prems):
    """⊕R1: from ``Γ ⊢ A`` infer ``Γ ⊢ A⊕B``."""
    return _oplus_r(concl, prems, True)


def _r_oplus_r2(concl, prems):
    """⊕R2: from ``Γ ⊢ B`` infer ``Γ ⊢ A⊕B``."""
    return _oplus_r(concl, prems, False)


def _r_bang_w(concl, prems):
    """!W: from ``Γ ⊢ C`` infer ``Γ, !A ⊢ C``."""
    if len(prems) != 1:
        return "!W has one premise"
    c, p = _cnt_of(concl.antecedent), prems[0]
    for f in c:
        if isinstance(f, OfCourse):
            if (p.succedent == concl.succedent
                    and _c_eq(_cnt_of(p.antecedent), _minus(c, f))):
                return None
    return "!W: needs !A on the left; the premise drops it"


def _r_bang_c(concl, prems):
    """!C: from ``Γ, !A, !A ⊢ C`` infer ``Γ, !A ⊢ C``."""
    if len(prems) != 1:
        return "!C has one premise"
    c, p = _cnt_of(concl.antecedent), prems[0]
    for f in c:
        if isinstance(f, OfCourse):
            if (p.succedent == concl.succedent
                    and _c_eq(_cnt_of(p.antecedent), _plus(c, f))):
                return None
    return "!C: needs !A on the left; the premise duplicates it"


def _r_bang_d(concl, prems):
    """!D: from ``Γ, A ⊢ C`` infer ``Γ, !A ⊢ C``."""
    if len(prems) != 1:
        return "!D has one premise"
    c, p = _cnt_of(concl.antecedent), prems[0]
    for f in c:
        if isinstance(f, OfCourse):
            if (p.succedent == concl.succedent
                    and _c_eq(_cnt_of(p.antecedent), _plus(_minus(c, f), f.formula))):
                return None
    return "!D: needs !A on the left; the premise derelicts it to A"


def _r_bang_p(concl, prems):
    """!P: from ``!Γ ⊢ A`` infer ``!Γ ⊢ !A`` (every antecedent formula !-prefixed)."""
    if len(prems) != 1:
        return "!P has one premise"
    g = concl.succedent
    if not isinstance(g, OfCourse):
        return "!P must conclude !A"
    if not all(isinstance(f, OfCourse) for f in concl.antecedent):
        return "!P: every antecedent formula must be !-prefixed"
    p = prems[0]
    if (p.succedent == g.formula
            and _c_eq(_cnt_of(p.antecedent), _cnt_of(concl.antecedent))):
        return None
    return "!P: the premise must be !Γ ⊢ A with the same antecedent"


_ILL_RULES: Dict[str, Callable] = {
    "Ax": _r_ax, "1R": _r_one_r, "1L": _r_one_l,
    "⊗L": _r_tensor_l, "⊗R": _r_tensor_r,
    "⊸L": _r_limp_l, "⊸R": _r_limp_r,
    "&L1": _r_with_l1, "&L2": _r_with_l2, "&R": _r_with_r,
    "⊕L": _r_oplus_l, "⊕R1": _r_oplus_r1, "⊕R2": _r_oplus_r2,
    "!W": _r_bang_w, "!C": _r_bang_c, "!D": _r_bang_d, "!P": _r_bang_p,
}


def _verify(deriv: "ILLDerivation"):
    """Recursive worker: return ``(rule, error)`` or ``(None, None)`` on success."""
    if not isinstance(deriv, ILLDerivation):
        return ("?", f"expected an ILLDerivation, got {type(deriv).__name__}")
    for child in deriv.premises:
        rule, err = _verify(child)
        if err is not None:
            return rule, err
    fn = _ILL_RULES.get(deriv.rule)
    if fn is None:
        return deriv.rule, f"unknown ILL rule {deriv.rule!r}"
    err = fn(deriv.conclusion, [c.conclusion for c in deriv.premises])
    if err is not None:
        return deriv.rule, err if err.startswith(deriv.rule) else f"{deriv.rule}: {err}"
    return None, None


def verify_ill_proof(derivation: "ILLDerivation") -> SequentResult:
    """Check an ILL derivation and return a
    :class:`~unicode_fol_kit.atp.sequent.SequentResult`.

    Recursively re-validates that every node's conclusion follows from its
    premises' conclusions by the node's rule (antecedents compared as multisets),
    returning the end-sequent and, on failure, the first offending rule and reason.
    """
    err_rule, err = _verify(derivation)
    end = derivation.conclusion if isinstance(derivation, ILLDerivation) else None
    return SequentResult(err is None, end, err_rule, err)


def check_ill_proof(derivation: "ILLDerivation") -> bool:
    """Return True iff ``derivation`` is a valid cut-free ILL derivation (sound)."""
    return verify_ill_proof(derivation).ok
