"""Recursive backtracking proof *search* for Fitch natural deduction.

Where :mod:`unicode_fol_kit.atp.fitch` *checks* a hand-written proof, this module
*finds* one: a goal-directed, depth-bounded backtracking search that builds an
actual :class:`~unicode_fol_kit.atp.fitch.Proof` for the classical propositional
and first-order fragment.

**Soundness is free.** Whatever the search assembles is handed to ``check_proof``
before it is returned, so a bug in the search or the proof-assembly can only make
it *fail to find* a proof — never return an unsound one. Like
:func:`resolution.prove`, the search is sound and, under its depth bound,
*incomplete*: ``find_fitch_proof`` returning ``None`` means "no proof found within
the bound", never "not a theorem".

Strategy (classical natural deduction):

1. **Forward saturation** — cheap eliminations (∧E, →E, ↔E, ¬¬E, ⊥I, and bounded
   ∀E instantiation) are applied to a fixpoint, so anything directly derivable is
   found before any branching.
2. **Goal-directed introduction** — for a goal with a main connective, the matching
   introduction rule (∧I, →I via an assumption box, ¬I, ∨I, ↔I, ∀I via an
   eigenvariable box, ∃I via a witness term).
3. **Elimination by case split** — ∨E over an available disjunction, ∃E over an
   available existential (with a fresh eigenvariable).
4. **Reductio (RAA)** — assume ¬goal and derive ⊥; this is what makes the search
   classically complete for the propositional fragment (it proves goals, such as
   ``P ∨ ¬P``, that no introduction rule reaches).

Public API: :func:`find_fitch_proof`, :func:`fitch_prove`, :func:`is_valid_fitch`.
"""

from typing import Dict, List, Optional, Tuple

from ..fol.nodes import (
    Node, Atom, Not, And, Or, Implies, Iff, Quantifier, Variable, Constant, Function,
)
from .fitch import (
    Proof, Subproof, Line, premise, assume, line, flag,
    FALSUM, is_falsum, verify_proof, _canon_q, _subst_var, _free_vars, _q_kind, _is_term,
)


# A search result is an abstract derivation term — a tagged tuple describing HOW a
# formula is obtained, with no line numbers yet (the assembler adds those):
#   ("ref",  f)                              — cite an in-scope line holding f
#   ("rule", tag, f, [deriv...], extra)      — a flat rule (∧I/∧E/∨I/→E/↔E/¬E/⊥I/⊥E/∀E/∃I)
#   ("impI", A, B, body)                     — →I: box [assume A ⊢ B]
#   ("notI", A, body)                        — ¬I: box [assume A ⊢ ⊥]
#   ("raa",  goal, body)                     — RAA: box [assume ¬goal ⊢ ⊥]
#   ("iffI", A, B, body1, body2)             — ↔I: boxes [A⊢B], [B⊢A]
#   ("orE",  disj_deriv, A, B, body1, body2, goal)  — ∨E
#   ("allI", x, phi, e, body)                — ∀I: flag box [e ⊢ phi[x:=e]]
#   ("exE",  ex_deriv, e, phi_e, body, goal) — ∃E: box [assume phi_e flag e ⊢ goal]

Deriv = tuple


# ---------------------------------------------------------------------------
# Terms and fresh variables
# ---------------------------------------------------------------------------

def _ground_terms(node: Node, acc: set) -> None:
    """Collect closed (variable-free) constant/function terms occurring in ``node``."""
    if isinstance(node, (Constant,)):
        acc.add(node)
    elif isinstance(node, Function):
        if not _free_vars(node):
            acc.add(node)
        for a in node.args:
            _ground_terms(a, acc)
    elif isinstance(node, Atom):
        for a in node.args:
            _ground_terms(a, acc)
    else:
        for child in node._child_nodes():
            _ground_terms(child, acc)


def _all_names(node: Node, acc: set) -> None:
    """Collect every variable name (free or bound) occurring in ``node``."""
    if isinstance(node, Variable):
        acc.add(node.name)
    if isinstance(node, Quantifier):
        acc.add(node.variable.name)
    for child in node._child_nodes():
        _all_names(child, acc)


class _Search:
    """Holds the immutable problem context (term pool, fresh-name source, budget)."""

    def __init__(self, premises: List[Node], goal: Node, max_depth: int):
        self.max_depth = max_depth
        self.budget = [60000]                 # per-attempt step backstop
        names: set = set()
        terms: set = set()
        for f in list(premises) + [goal]:
            _all_names(f, names)
            _ground_terms(f, terms)
        if not terms:
            terms.add(Constant("a"))          # a witness/instantiation term must exist
        self.used_names = names
        self.base_terms = sorted(terms, key=lambda t: t.to_unicode_str())
        self._eigen = [0]

    def fresh_var(self) -> Variable:
        """Return a globally fresh eigenvariable not occurring anywhere in the problem."""
        while True:
            name = f"_e{self._eigen[0]}"
            self._eigen[0] += 1
            if name not in self.used_names:
                self.used_names.add(name)
                return Variable(name)


# ---------------------------------------------------------------------------
# Forward saturation
# ---------------------------------------------------------------------------

def _saturate(derivs: Dict[Node, Deriv], terms: List[Node]) -> None:
    """Close ``derivs`` under cheap eliminations (mutates it in place)."""
    pool = terms
    changed = True
    rounds = 0
    while changed and rounds < 40:
        changed = False
        rounds += 1
        for f in list(derivs):
            if isinstance(f, And):
                for part in (f.left, f.right):
                    if part not in derivs:
                        derivs[part] = ("rule", "∧E", part, [derivs[f]], ())
                        changed = True
            elif isinstance(f, Not) and isinstance(f.formula, Not):
                inner = f.formula.formula
                if inner not in derivs:
                    derivs[inner] = ("rule", "¬E", inner, [derivs[f]], ())
                    changed = True
            elif isinstance(f, Iff):
                if f.left in derivs and f.right not in derivs:
                    derivs[f.right] = ("rule", "↔E", f.right, [derivs[f], derivs[f.left]], ())
                    changed = True
                if f.right in derivs and f.left not in derivs:
                    derivs[f.left] = ("rule", "↔E", f.left, [derivs[f], derivs[f.right]], ())
                    changed = True
            elif isinstance(f, Implies):
                if f.left in derivs and f.right not in derivs:
                    derivs[f.right] = ("rule", "→E", f.right, [derivs[f], derivs[f.left]], ())
                    changed = True
            elif _q_kind(f) == "∀":
                for t in pool:
                    inst = _subst_var(f.formula, f.variable, t)
                    if inst not in derivs:
                        derivs[inst] = ("rule", "∀E", inst, [derivs[f]], (t,))
                        changed = True
        if FALSUM not in derivs:
            for f in list(derivs):
                if Not(f) in derivs:
                    derivs[FALSUM] = ("rule", "⊥I", FALSUM, [derivs[f], derivs[Not(f)]], ())
                    changed = True
                    break


def _extend(derivs: Dict[Node, Deriv], formula: Node) -> Dict[Node, Deriv]:
    """Return a copy of ``derivs`` with ``formula`` added as a base (Ref) fact."""
    new = dict(derivs)
    if formula not in new:
        new[formula] = ("ref", formula)
    return new


# ---------------------------------------------------------------------------
# The search
# ---------------------------------------------------------------------------

def _search(derivs: Dict[Node, Deriv], goal: Node, depth: int,
            ctx: "_Search", terms: List[Node]) -> Optional[Deriv]:
    """Find an abstract derivation of ``goal`` from ``derivs``, or None within bounds.

    ``terms`` is the instantiation/witness term set in scope on this branch — the
    problem's ground terms plus the eigenvariables of enclosing ∀I / ∃E boxes. It is
    threaded (not global) so the universal-instantiation pool stays bounded per path.
    """
    if ctx.budget[0] <= 0:
        return None
    ctx.budget[0] -= 1

    derivs = dict(derivs)
    _saturate(derivs, terms)
    if goal in derivs:
        return derivs[goal]
    # Ex falso quodlibet: once a contradiction is in scope, any goal follows.
    if FALSUM in derivs and not is_falsum(goal):
        return ("rule", "⊥E", goal, [derivs[FALSUM]], ())
    if depth <= 0:
        return None

    found = _try_intro(derivs, goal, depth, ctx, terms)
    if found is not None:
        return found

    # Elimination by case split on an available disjunction.
    for f in list(derivs):
        if isinstance(f, Or):
            d1 = _search(_extend(derivs, f.left), goal, depth - 1, ctx, terms)
            if d1 is None:
                continue
            d2 = _search(_extend(derivs, f.right), goal, depth - 1, ctx, terms)
            if d2 is None:
                continue
            return ("orE", derivs[f], f.left, f.right, d1, d2, goal)

    # ∃-elimination over an available existential (fresh eigenvariable).
    for f in list(derivs):
        if _q_kind(f) == "∃":
            e = ctx.fresh_var()
            phi_e = _subst_var(f.formula, f.variable, e)
            body = _search(_extend(derivs, phi_e), goal, depth - 1, ctx, terms + [e])
            if body is not None and e not in _free_vars(goal) and e not in _free_vars(f):
                return ("exE", derivs[f], e, phi_e, body, goal)

    # Backward chaining: prove ``goal`` via an available implication X → goal.
    for f in list(derivs):
        if isinstance(f, Implies) and f.right == goal and f.left != goal:
            d = _search(derivs, f.left, depth - 1, ctx, terms)
            if d is not None:
                return ("rule", "→E", goal, [derivs[f], d], ())

    # Reductio ad absurdum (classical completeness for the propositional fragment).
    if not is_falsum(goal):
        body = _search(_extend(derivs, Not(goal)), FALSUM, depth - 1, ctx, terms)
        if body is not None:
            return ("raa", goal, body)

    return None


def _try_intro(derivs: Dict[Node, Deriv], goal: Node, depth: int,
               ctx: "_Search", terms: List[Node]) -> Optional[Deriv]:
    """Try the introduction rule for ``goal``'s main connective."""
    if isinstance(goal, And):
        d1 = _search(derivs, goal.left, depth - 1, ctx, terms)
        if d1 is None:
            return None
        d2 = _search(derivs, goal.right, depth - 1, ctx, terms)
        if d2 is None:
            return None
        return ("rule", "∧I", goal, [d1, d2], ())

    if isinstance(goal, Implies):
        body = _search(_extend(derivs, goal.left), goal.right, depth - 1, ctx, terms)
        if body is not None:
            return ("impI", goal.left, goal.right, body)
        return None

    if isinstance(goal, Not):
        body = _search(_extend(derivs, goal.formula), FALSUM, depth - 1, ctx, terms)
        if body is not None:
            return ("notI", goal.formula, body)
        return None

    if isinstance(goal, Iff):
        d1 = _search(_extend(derivs, goal.left), goal.right, depth - 1, ctx, terms)
        if d1 is None:
            return None
        d2 = _search(_extend(derivs, goal.right), goal.left, depth - 1, ctx, terms)
        if d2 is None:
            return None
        return ("iffI", goal.left, goal.right, d1, d2)

    if isinstance(goal, Or):
        d = _search(derivs, goal.left, depth - 1, ctx, terms)
        if d is not None:
            return ("rule", "∨I", goal, [d], ())
        d = _search(derivs, goal.right, depth - 1, ctx, terms)
        if d is not None:
            return ("rule", "∨I", goal, [d], ())
        return None

    if _q_kind(goal) == "∀":
        e = ctx.fresh_var()
        phi_e = _subst_var(goal.formula, goal.variable, e)
        body = _search(derivs, phi_e, depth - 1, ctx, terms + [e])
        if body is not None:
            return ("allI", goal.variable, goal.formula, e, body)
        return None

    if _q_kind(goal) == "∃":
        for t in terms:
            witness = _subst_var(goal.formula, goal.variable, t)
            d = _search(derivs, witness, depth - 1, ctx, terms)
            if d is not None:
                return ("rule", "∃I", goal, [d], (t,))
        return None

    if is_falsum(goal):
        # Prove ⊥ from a fact f by proving its negation, or from ¬g by proving g.
        for f in list(derivs):
            if isinstance(f, Not):
                proven = _search(derivs, f.formula, depth - 1, ctx, terms)
                if proven is not None:
                    return ("rule", "⊥I", FALSUM, [proven, derivs[f]], ())
            else:
                neg = _search(derivs, Not(f), depth - 1, ctx, terms)
                if neg is not None:
                    return ("rule", "⊥I", FALSUM, [derivs[f], neg], ())
        return None

    return None


# ---------------------------------------------------------------------------
# Assembly: abstract derivation -> a numbered Fitch Proof
# ---------------------------------------------------------------------------

class _Asm:
    """Mutable assembly context: a shared line counter + the in-scope fact→line map."""

    def __init__(self, counter: List[int], available: Dict[Node, int]):
        self.counter = counter
        self.available = available
        self.out: List = []

    def fresh(self) -> int:
        self.counter[0] += 1
        return self.counter[0]


def _emit(deriv: Deriv, asm: "_Asm") -> int:
    """Emit the lines for ``deriv`` into ``asm`` and return the line number of its result."""
    tag = deriv[0]

    if tag == "ref":
        return asm.available[deriv[1]]

    if tag == "rule":
        _, rule, formula, subs, extra = deriv
        if formula in asm.available:
            return asm.available[formula]
        cites = [_emit(s, asm) for s in subs]
        num = asm.fresh()
        asm.out.append(line(num, formula, rule, *cites, extra=extra))
        asm.available[formula] = num
        return num

    if tag == "impI":
        _, ante, cons, body = deriv
        span = _emit_box(asm, ante, None, body, cons)
        num = asm.fresh()
        asm.out.append(line(num, Implies(ante, cons), "→I", span))
        asm.available[Implies(ante, cons)] = num
        return num

    if tag == "notI":
        _, phi, body = deriv
        span = _emit_box(asm, phi, None, body, FALSUM)
        num = asm.fresh()
        asm.out.append(line(num, Not(phi), "¬I", span))
        asm.available[Not(phi)] = num
        return num

    if tag == "raa":
        _, goal, body = deriv
        span = _emit_box(asm, Not(goal), None, body, FALSUM)
        num = asm.fresh()
        asm.out.append(line(num, goal, "RAA", span))
        asm.available[goal] = num
        return num

    if tag == "iffI":
        _, a, b, body1, body2 = deriv
        span1 = _emit_box(asm, a, None, body1, b)
        span2 = _emit_box(asm, b, None, body2, a)
        num = asm.fresh()
        asm.out.append(line(num, Iff(a, b), "↔I", span1, span2))
        asm.available[Iff(a, b)] = num
        return num

    if tag == "orE":
        _, disj_deriv, a, b, body1, body2, goal = deriv
        disj_line = _emit(disj_deriv, asm)
        span1 = _emit_box(asm, a, None, body1, goal)
        span2 = _emit_box(asm, b, None, body2, goal)
        num = asm.fresh()
        asm.out.append(line(num, goal, "∨E", disj_line, span1, span2))
        asm.available[goal] = num
        return num

    if tag == "allI":
        _, x, phi, e, body = deriv
        phi_e = _subst_var(phi, x, e)
        span = _emit_box(asm, None, e, body, phi_e)
        num = asm.fresh()
        asm.out.append(line(num, Quantifier("∀", x, phi), "∀I", span))
        asm.available[Quantifier("∀", x, phi)] = num
        return num

    if tag == "exE":
        _, ex_deriv, e, phi_e, body, goal = deriv
        ex_line = _emit(ex_deriv, asm)
        span = _emit_box(asm, phi_e, e, body, goal)
        num = asm.fresh()
        asm.out.append(line(num, goal, "∃E", ex_line, span))
        asm.available[goal] = num
        return num

    raise AssertionError(f"unknown derivation tag {tag!r}")


def _emit_box(asm: "_Asm", assumption: Optional[Node], flag_var: Optional[Variable],
              body: Deriv, body_goal: Node) -> Tuple[int, int]:
    """Emit a subproof box and append it to ``asm.out``; return its (start, end) span."""
    child = _Asm(asm.counter, dict(asm.available))
    head_num = child.fresh()
    if assumption is None and flag_var is not None:
        head = flag(head_num, flag_var)            # ∀I: pure eigenvariable box
    else:
        head = assume(head_num, assumption)         # →I/¬I/RAA/∨E/↔I (and ∃E, with a flag)
        child.available[assumption] = head_num

    result = _emit(body, child)
    # The box's last line must be body_goal; if it is not, reiterate it.
    if not (child.out and isinstance(child.out[-1], Line)
            and child.out[-1].formula == body_goal):
        rnum = child.fresh()
        child.out.append(line(rnum, body_goal, "Reit", result))

    end_num = child.counter[0]
    box = Subproof(assumption=head, body=tuple(child.out), flag=flag_var)
    asm.out.append(box)
    return (head_num, end_num)


def _assemble(premises: List[Node], goal: Node, deriv: Deriv) -> Proof:
    """Turn an abstract derivation into a numbered :class:`Proof`."""
    premise_lines = [premise(i, f) for i, f in enumerate(premises, start=1)]
    available: Dict[Node, int] = {}
    for i, f in enumerate(premises, start=1):
        available.setdefault(f, i)
    counter = [len(premises)]
    asm = _Asm(counter, available)
    result = _emit(deriv, asm)
    # Ensure the proof's last top-level line is the goal.
    if not (asm.out and isinstance(asm.out[-1], Line) and asm.out[-1].formula == goal):
        num = asm.fresh()
        asm.out.append(line(num, goal, "Reit", result))
    return Proof(premises=tuple(premise_lines), steps=tuple(asm.out), logic="fol")


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------

def find_fitch_proof(premises, conclusion: Node, max_depth: int = 8) -> Optional[Proof]:
    """Search for a Fitch proof of ``premises ⊢ conclusion``; return it or ``None``.

    Goal-directed backtracking over the classical propositional + first-order rules.
    The returned proof is re-validated by ``check_proof`` before it is handed back,
    so the result is always a genuinely valid proof (or ``None``). ``None`` means "no
    proof found within ``max_depth``", never "not a theorem" — the search is sound
    but, under its depth bound, incomplete (first-order provability is undecidable).

    ``Contrast`` and ``Count`` are reduced to their classical readings up front
    (∧ and the distinct-witnesses expansion), so the returned proof derives the
    reduced formula. A MODAL input is rejected with a pointer — this search has
    no modal rules, and silently treating a modal operator as an opaque atom
    used to return a misleading ``None`` for valid entailments like
    ``□(P→Q), □P ⊢ □Q``; :func:`fitch_prove` / :func:`is_valid_fitch` instead
    route modal input to the modal tableau automatically.

    Raises:
        NotImplementedError: on modal/temporal/hybrid/counterfactual input, and on
            substructural (ILL/Lambek), team-semantic, second-order, or Łukasiewicz
            input — each with a pointer at its own decision procedure (an opaque-atom
            treatment would silently return None for genuine theorems like the
            ILL axiom ``A ⊸ A``).
    """
    from ..fol._msfl_nodes import _reduce_nl_nodes
    from .modal_tableau import has_modal
    from .tableau import _reject_exotic
    _reject_exotic(list(premises) + [conclusion], "find_fitch_proof")
    premises = [_reduce_nl_nodes(p) for p in premises]
    conclusion = _reduce_nl_nodes(conclusion)
    if any(has_modal(f) for f in premises + [conclusion]):
        raise NotImplementedError(
            "find_fitch_proof: no proof search over the modal natural-deduction "
            "rules (a modal operator treated as an opaque atom would silently "
            "yield None for valid modal entailments). Decide validity with "
            "fitch_prove / is_valid_fitch (which route to the modal tableau), or "
            "check a hand-written modal Fitch proof with check_proof.")
    premises = [_canon_q(p) for p in premises]
    goal = _canon_q(conclusion)
    base = {p: ("ref", p) for p in premises}
    # Iterative deepening: try increasing depth bounds so a shallow proof is found
    # before the search explores deep, fruitless branches. Each level gets a fresh
    # step budget and eigenvariable counter.
    for depth in range(1, max_depth + 1):
        ctx = _Search(premises, goal, depth)
        deriv = _search(base, goal, depth, ctx, ctx.base_terms)
        if deriv is not None:
            proof = _assemble(premises, goal, deriv)
            if verify_proof(proof).ok:
                return proof
    return None


def fitch_prove(premises, conclusion: Node, max_depth: int = 8) -> bool:
    """Return True iff ``premises ⊢ conclusion`` is established (sound, bounded).

    Classical input is decided by the Fitch proof search. MODAL input is routed
    to the modal tableau's local consequence over the system **K**
    (:func:`~unicode_fol_kit.atp.modal_tableau.modal_prove`) — previously a
    modal operator was treated as an opaque atom and e.g. the K-axiom instance
    ``□(P→Q), □P ⊢ □Q`` silently came back False. Either path is sound: a True
    is a verified Fitch proof or a closed modal tableau.
    """
    from .modal_tableau import has_modal, modal_prove
    from .tableau import _reject_exotic
    premises = list(premises)
    # Substructural / team / SO / fuzzy input must not degrade to "opaque atom →
    # silent False" (the exact bug class the modal routing below already fixed:
    # is_valid_fitch(A ⊸ A) returned False for a genuine ILL theorem).
    _reject_exotic(premises + [conclusion], "fitch_prove")
    if any(has_modal(f) for f in premises + [conclusion]):
        return modal_prove(premises, conclusion)
    return find_fitch_proof(premises, conclusion, max_depth) is not None


def is_valid_fitch(formula: Node, max_depth: int = 8) -> bool:
    """Return True iff ``formula`` is provable from no premises (a found-theorem check).

    Modal input is decided by the modal tableau over **K** (see
    :func:`fitch_prove`); classical input by the Fitch search.
    """
    return fitch_prove([], formula, max_depth)
