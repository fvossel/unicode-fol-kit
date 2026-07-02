"""The Lambek calculus **L** — a complete, terminating decision procedure + a checker.

The Lambek calculus (Lambek 1958) is the sequent calculus of **ordered** resources:
on top of dropping weakening and contraction (as linear logic does) it drops
**exchange**, so a sequent's antecedent is a *sequence* of formulas, not a multiset,
and ``A, A\\B ⊢ B`` is derivable while ``A\\B, A ⊢ B`` is not. Antecedents must be
**nonempty** (Lambek's restriction — the version relevant to categorial grammar).
The connectives are the ``lambek`` parser mode's
(:mod:`unicode_fol_kit.fol._lambek_nodes`): ``•`` / ``\\`` / ``/``.

Rules (cut-free; ``Γ``, ``Δ`` range over sequences, ``Γ`` nonempty where stated)::

    Ax:  A ⊢ A
    •L:  Γ, A, B, Δ ⊢ C                ⇒  Γ, A•B, Δ ⊢ C
    •R:  Γ ⊢ A   and  Δ ⊢ B            ⇒  Γ, Δ ⊢ A•B      (contiguous split, in order)
    \\L:  Γ ⊢ A   and  Δ1, B, Δ2 ⊢ C    ⇒  Δ1, Γ, A\\B, Δ2 ⊢ C   (Γ nonempty)
    \\R:  A, Γ ⊢ B                      ⇒  Γ ⊢ A\\B        (Γ nonempty; A prepended)
    /L:  Γ ⊢ A   and  Δ1, B, Δ2 ⊢ C    ⇒  Δ1, B/A, Γ, Δ2 ⊢ C   (Γ nonempty)
    /R:  Γ, A ⊢ B                      ⇒  Γ ⊢ B/A        (Γ nonempty; A appended)

**Decidability.** Every rule's premises have strictly smaller total size (node
count) than its conclusion, and there are finitely many rule instances per sequent,
so the backward search below — exhaustive, memoised on ``(sequence, goal)`` — is a
**complete, terminating decision procedure**: L is decidable, and
``lambek_prove(...) is None`` *proves* underivability. No depth bound is needed.

Deliberately, there is **no classical export**: collapsing ``A\\B`` and ``B/A`` to
``A → B`` forgets word order, which is the calculus's entire point. (The collapse is
*sound* — every L theorem collapses to a classical one, which the test-suite checks
against Z3 — but it identifies types L keeps apart.)

Public API: :class:`LambekSequent`, :class:`LambekDerivation`, :func:`lambek_prove`,
:func:`lambek_derivable`, :func:`check_lambek_proof`, :func:`verify_lambek_proof`,
:func:`render_lambek_proof`.
"""

from dataclasses import dataclass
from typing import Callable, Dict, Iterable, Optional, Tuple

from ..fol.nodes import Node, Product, Under, Over
from .sequent import SequentResult


# ---------------------------------------------------------------------------
# Sequents and derivations
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class LambekSequent:
    """A Lambek sequent ``antecedent ⊢ succedent``.

    ``antecedent`` is a **nonempty sequence** (tuple) of formulas — order matters,
    there is no exchange; ``succedent`` is one formula. Frozen and hashable.
    """

    antecedent: Tuple[Node, ...]
    succedent: Node

    def __post_init__(self):
        """Coerce the antecedent to a tuple so the sequent stays hashable."""
        object.__setattr__(self, "antecedent", tuple(self.antecedent))

    def __str__(self) -> str:
        """Render as ``A, B ⊢ C`` using each formula's Unicode form."""
        left = ", ".join(f.to_unicode_str() for f in self.antecedent)
        return f"{left} ⊢ {self.succedent.to_unicode_str()}"


@dataclass(frozen=True)
class LambekDerivation:
    """A node of a Lambek-calculus derivation tree.

    ``conclusion`` is the sequent this node derives; ``rule`` is the rule name
    (``"Ax"``, ``"•R"``, ``"\\L"``, …); ``premises`` are the sub-derivations whose
    conclusions are this rule's premises, **in the rule's written order** (for the
    two-premise ``\\L`` / ``/L`` the argument premise ``Γ ⊢ A`` comes first; for
    ``•R`` the left part of the split comes first).
    """

    conclusion: LambekSequent
    rule: str
    premises: Tuple["LambekDerivation", ...] = ()

    def __post_init__(self):
        """Coerce ``premises`` to a tuple so the derivation stays hashable."""
        object.__setattr__(self, "premises", tuple(self.premises))

    def render(self) -> str:
        """Render this derivation as an indented proof tree."""
        return render_lambek_proof(self)


def render_lambek_proof(derivation: "LambekDerivation", indent: int = 0) -> str:
    """Render a derivation as an indented tree (conclusion first, premises below)."""
    pad = "  " * indent
    lines = [f"{pad}{derivation.conclusion}   [{derivation.rule}]"]
    for premise in derivation.premises:
        lines.append(render_lambek_proof(premise, indent + 1))
    return "\n".join(lines)


def _size(f: Node) -> int:
    """Return the node count of a formula (atomic categories count 1)."""
    return 1 + sum(_size(c) for c in f._child_nodes())


# ---------------------------------------------------------------------------
# Backward proof search (a decision procedure — see the module docstring)
# ---------------------------------------------------------------------------

def _prove(seq: Tuple[Node, ...], goal: Node,
           memo: Dict) -> Optional[LambekDerivation]:
    """Exhaustive backward search for a derivation of ``seq ⊢ goal``.

    Terminates because every premise's total node count is strictly smaller than
    its conclusion's; memoised on ``(seq, goal)`` (both successes and failures —
    sound here precisely because the search is unbounded and exhaustive).
    """
    key = (seq, goal)
    if key in memo:
        return memo[key]
    memo[key] = None  # pre-set: harmless (no rule can revisit an equal sequent)

    result = None

    # Ax
    if len(seq) == 1 and seq[0] == goal:
        result = LambekDerivation(LambekSequent(seq, goal), "Ax")

    # Right rules on the goal's main connective.
    if result is None and isinstance(goal, Product):
        for i in range(1, len(seq)):        # both parts nonempty
            p1 = _prove(seq[:i], goal.left, memo)
            if p1 is None:
                continue
            p2 = _prove(seq[i:], goal.right, memo)
            if p2 is not None:
                result = LambekDerivation(LambekSequent(seq, goal), "•R", (p1, p2))
                break
    if result is None and isinstance(goal, Under):
        # goal = A\B: prepend A on the LEFT.
        p = _prove((goal.left,) + seq, goal.right, memo)
        if p is not None:
            result = LambekDerivation(LambekSequent(seq, goal), "\\R", (p,))
    if result is None and isinstance(goal, Over):
        # goal = B/A: append A on the RIGHT (fields: left=B, right=A).
        p = _prove(seq + (goal.right,), goal.left, memo)
        if p is not None:
            result = LambekDerivation(LambekSequent(seq, goal), "/R", (p,))

    # Left rules on each antecedent position.
    if result is None:
        for i, f in enumerate(seq):
            if isinstance(f, Product):
                p = _prove(seq[:i] + (f.left, f.right) + seq[i + 1:], goal, memo)
                if p is not None:
                    result = LambekDerivation(LambekSequent(seq, goal), "•L", (p,))
                    break
            elif isinstance(f, Under):
                # f = A\B at position i: a nonempty Γ ending just before i derives A.
                for j in range(i - 1, -1, -1):
                    p_arg = _prove(seq[j:i], f.left, memo)
                    if p_arg is None:
                        continue
                    p_main = _prove(seq[:j] + (f.right,) + seq[i + 1:], goal, memo)
                    if p_main is not None:
                        result = LambekDerivation(LambekSequent(seq, goal), "\\L",
                                                  (p_arg, p_main))
                        break
                if result is not None:
                    break
            elif isinstance(f, Over):
                # f = B/A at position i: a nonempty Γ starting just after i derives A.
                for j in range(i + 2, len(seq) + 1):
                    p_arg = _prove(seq[i + 1:j], f.right, memo)
                    if p_arg is None:
                        continue
                    p_main = _prove(seq[:i] + (f.left,) + seq[j:], goal, memo)
                    if p_main is not None:
                        result = LambekDerivation(LambekSequent(seq, goal), "/L",
                                                  (p_arg, p_main))
                        break
                if result is not None:
                    break

    memo[key] = result
    return result


def lambek_prove(sequence: Iterable[Node], goal: Node) -> Optional[LambekDerivation]:
    """Decide ``sequence ⊢ goal`` in the Lambek calculus L; return a derivation or None.

    This is a genuine **decision procedure** (see the module docstring): a
    ``None`` *proves* the sequent underivable in L. The returned derivation is
    re-validated by :func:`check_lambek_proof` before it is handed back, so a
    search bug can only lose proofs, never invent them.

    Raises ``ValueError`` on an empty ``sequence`` — L requires nonempty
    antecedents (Lambek's restriction).
    """
    seq = tuple(sequence)
    if not seq:
        raise ValueError(
            "the Lambek calculus requires a nonempty antecedent sequence "
            "(Lambek's restriction)")
    derivation = _prove(seq, goal, {})
    if derivation is not None and not check_lambek_proof(derivation):
        raise RuntimeError(
            "internal error: the Lambek search assembled a derivation its own "
            "checker rejects — please report this")
    return derivation


def lambek_derivable(sequence: Iterable[Node], goal: Node) -> bool:
    """Return True iff ``sequence ⊢ goal`` is derivable in L (a decision procedure)."""
    return lambek_prove(sequence, goal) is not None


# ---------------------------------------------------------------------------
# The checker
# ---------------------------------------------------------------------------
#
# Each rule checker has signature (conclusion: LambekSequent, premises:
# List[LambekSequent]) and returns None when the step is licensed, or an error
# string. Antecedents are compared as SEQUENCES — order is the whole point.

def _r_ax(concl, prems):
    """Ax: ``A ⊢ A`` — a single antecedent formula equal to the succedent."""
    if prems:
        return "Ax takes no premises"
    if len(concl.antecedent) != 1 or concl.antecedent[0] != concl.succedent:
        return "Ax: the antecedent must be exactly the succedent formula"
    return None


def _r_prod_l(concl, prems):
    """•L: from ``Γ, A, B, Δ ⊢ C`` infer ``Γ, A•B, Δ ⊢ C``."""
    if len(prems) != 1:
        return "•L has one premise"
    ant, p = concl.antecedent, prems[0]
    for i, f in enumerate(ant):
        if isinstance(f, Product):
            want = ant[:i] + (f.left, f.right) + ant[i + 1:]
            if p.succedent == concl.succedent and p.antecedent == want:
                return None
    return "•L: needs A•B in the antecedent; the premise unfolds it in place"


def _r_prod_r(concl, prems):
    """•R: from ``Γ ⊢ A`` and ``Δ ⊢ B`` infer ``Γ, Δ ⊢ A•B`` (in order, both nonempty)."""
    if len(prems) != 2:
        return "•R has two premises"
    g = concl.succedent
    if not isinstance(g, Product):
        return "•R must conclude a product A•B"
    p1, p2 = prems
    if not p1.antecedent or not p2.antecedent:
        return "•R: both parts of the split must be nonempty"
    if (p1.succedent == g.left and p2.succedent == g.right
            and p1.antecedent + p2.antecedent == concl.antecedent):
        return None
    return "•R: premises Γ⊢A then Δ⊢B with Γ,Δ the conclusion's antecedent in order"


def _r_under_l(concl, prems):
    """\\L: from ``Γ ⊢ A`` and ``Δ1, B, Δ2 ⊢ C`` infer ``Δ1, Γ, A\\B, Δ2 ⊢ C``."""
    if len(prems) != 2:
        return "\\L has two premises"
    p_arg, p_main = prems
    if not p_arg.antecedent:
        return "\\L: the argument premise's antecedent Γ must be nonempty"
    if p_main.succedent != concl.succedent:
        return "\\L: the main premise must share the conclusion's succedent"
    ant, g = concl.antecedent, p_arg.antecedent
    for i, f in enumerate(ant):
        if not isinstance(f, Under) or f.left != p_arg.succedent:
            continue
        # Γ must sit immediately LEFT of the A\B occurrence.
        if i - len(g) < 0 or ant[i - len(g):i] != g:
            continue
        d1, d2 = ant[:i - len(g)], ant[i + 1:]
        if p_main.antecedent == d1 + (f.right,) + d2:
            return None
    return "\\L: needs Δ1, Γ, A\\B, Δ2 with Γ ⊢ A and Δ1, B, Δ2 ⊢ C"


def _r_under_r(concl, prems):
    """\\R: from ``A, Γ ⊢ B`` infer ``Γ ⊢ A\\B`` (Γ nonempty)."""
    if len(prems) != 1:
        return "\\R has one premise"
    g = concl.succedent
    if not isinstance(g, Under):
        return "\\R must conclude A\\B"
    if not concl.antecedent:
        return "\\R: the conclusion's antecedent Γ must be nonempty"
    p = prems[0]
    if p.succedent == g.right and p.antecedent == (g.left,) + concl.antecedent:
        return None
    return "\\R: the premise must be A, Γ ⊢ B (A prepended on the LEFT)"


def _r_over_l(concl, prems):
    """/L: from ``Γ ⊢ A`` and ``Δ1, B, Δ2 ⊢ C`` infer ``Δ1, B/A, Γ, Δ2 ⊢ C``."""
    if len(prems) != 2:
        return "/L has two premises"
    p_arg, p_main = prems
    if not p_arg.antecedent:
        return "/L: the argument premise's antecedent Γ must be nonempty"
    if p_main.succedent != concl.succedent:
        return "/L: the main premise must share the conclusion's succedent"
    ant, g = concl.antecedent, p_arg.antecedent
    for i, f in enumerate(ant):
        if not isinstance(f, Over) or f.right != p_arg.succedent:
            continue
        # Γ must sit immediately RIGHT of the B/A occurrence.
        if ant[i + 1:i + 1 + len(g)] != g:
            continue
        d1, d2 = ant[:i], ant[i + 1 + len(g):]
        if p_main.antecedent == d1 + (f.left,) + d2:
            return None
    return "/L: needs Δ1, B/A, Γ, Δ2 with Γ ⊢ A and Δ1, B, Δ2 ⊢ C"


def _r_over_r(concl, prems):
    """/R: from ``Γ, A ⊢ B`` infer ``Γ ⊢ B/A`` (Γ nonempty)."""
    if len(prems) != 1:
        return "/R has one premise"
    g = concl.succedent
    if not isinstance(g, Over):
        return "/R must conclude B/A"
    if not concl.antecedent:
        return "/R: the conclusion's antecedent Γ must be nonempty"
    p = prems[0]
    if p.succedent == g.left and p.antecedent == concl.antecedent + (g.right,):
        return None
    return "/R: the premise must be Γ, A ⊢ B (A appended on the RIGHT)"


_LAMBEK_RULES: Dict[str, Callable] = {
    "Ax": _r_ax,
    "•L": _r_prod_l, "•R": _r_prod_r,
    "\\L": _r_under_l, "\\R": _r_under_r,
    "/L": _r_over_l, "/R": _r_over_r,
}


def _verify(deriv: "LambekDerivation"):
    """Recursive worker: return ``(rule, error)`` or ``(None, None)`` on success."""
    if not isinstance(deriv, LambekDerivation):
        return ("?", f"expected a LambekDerivation, got {type(deriv).__name__}")
    if not deriv.conclusion.antecedent:
        return (deriv.rule, "Lambek sequents require a nonempty antecedent "
                            "(Lambek's restriction)")
    for child in deriv.premises:
        rule, err = _verify(child)
        if err is not None:
            return rule, err
    fn = _LAMBEK_RULES.get(deriv.rule)
    if fn is None:
        return deriv.rule, f"unknown Lambek rule {deriv.rule!r}"
    err = fn(deriv.conclusion, [c.conclusion for c in deriv.premises])
    if err is not None:
        return deriv.rule, err if err.startswith(deriv.rule) else f"{deriv.rule}: {err}"
    return None, None


def verify_lambek_proof(derivation: "LambekDerivation") -> SequentResult:
    """Check a Lambek derivation and return a
    :class:`~unicode_fol_kit.atp.sequent.SequentResult`.

    Recursively re-validates that every node's conclusion follows from its
    premises' conclusions by the node's rule — antecedents compared as **ordered
    sequences** and required nonempty throughout — returning the end-sequent and,
    on failure, the first offending rule and reason.
    """
    err_rule, err = _verify(derivation)
    end = derivation.conclusion if isinstance(derivation, LambekDerivation) else None
    return SequentResult(err is None, end, err_rule, err)


def check_lambek_proof(derivation: "LambekDerivation") -> bool:
    """Return True iff ``derivation`` is a valid cut-free L derivation (sound)."""
    return verify_lambek_proof(derivation).ok
