"""Dependence logic -> existential second-order logic (Skolem/Henkin translation).

Väänänen's team semantics (:mod:`unicode_fol_kit.semantics.team`) evaluates a
dependence-logic SENTENCE by brute-force search over teams; this module instead
*translates* a sentence into an ordinary classical formula headed by existential
second-order (ESO) quantifiers, whose truth in a structure — checked by
:func:`unicode_fol_kit.semantics.secondorder.satisfies_so` / :func:`holds` — is
PROVABLY EQUIVALENT to the team-semantic truth of the original sentence, for the
fragment described below. This realises half of Väänänen's headline theorem that
dependence logic captures exactly ESO (the other half, ESO -> D, is not needed
here): every sentence of the *SKOLEM-NORMAL fragment* is equivalent to the
existence of a family of SKOLEM FUNCTIONS obeying the dependence/independence
constraints written into the sentence.

THE TRANSLATION (Skolemisation with restricted dependency)
------------------------------------------------------------
Each existential — plain ``∃u``, an independence-friendly ``∃u/{V}``, or a
plain ``∃u`` immediately guarded by a dependence atom ``=(t̄,u)`` — is replaced
by a fresh GRAPH PREDICATE ``F_u`` of arity ``|args| + 1`` (the last argument is
``u``'s value), existentially quantified at the very front of the formula,
together with two first-order axioms making ``F_u`` TOTAL and FUNCTIONAL in its
first ``|args|`` positions (so it really is the graph of a function
``args -> u``):

- **unguarded** ``∃u φ`` (no dependence atom, not slashed): ``args`` = every
  ``∀``-bound variable enclosing this ``∃`` (in order) — the ordinary
  first-order Skolem function of the full universal prefix. (Any INTERVENING
  ``∃``-bound variable is safely omittable here: it is itself already a
  function of those same ``∀``'s, so it carries no information an unrestricted
  witness could not already reconstruct.)
- **slashed** ``∃u/{V} φ``: ``args`` = every variable BOUND SO FAR — ``∀`` or
  ``∃`` alike, in binding order — EXCEPT those named in the slash set ``V``.
  Note this is *every enclosing binder*, not just the ``∀``'s: independence is
  a constraint on the witness function's visible ARGUMENT NAMES, and a
  variable not literally in ``V`` stays visible even if it happens to be a
  deterministic function of one that is — which is exactly the SIGNALLING
  phenomenon (Väänänen 2007 §4): ``∀x∃z(z=x ∧ ∃y/{x}(y=x))`` lets ``y``
  recover ``x`` via ``z``, and IS true everywhere, unlike ``∀x∃y/{x}(y=x)``
  with no such intervening ``z``.
- **dependence-atom-guarded** ``∃u(=(t̄,u) ∧ φ)`` (the dependence atom a
  top-level conjunct in the IMMEDIATE body of the ``∃`` binding its dependent
  variable ``u``, the canonical Väänänen normal form): ``args`` = exactly
  ``t̄`` — the atom's own determinant terms override the default.

Every occurrence is then rewritten in place, innermost, as the classical
``∃u(F_u(args, u) ∧ φ')`` (``φ'`` = the (recursively translated) rest of the
guard's body, or bare ``F_u(args,u)`` if the guard was the whole body) — an
ORDINARY first-order ``∃u``, not a team-semantic one. Every ``F_u`` and its two
axioms then float to the front: ``(χ ∧ ∃F ρ) ≡ ∃F(χ ∧ ρ)`` for ``F`` fresh is
an unconditional second-order equivalence, so nesting position never matters.
``∀`` is passed through unchanged; literals (atoms, negated atoms) are passed
through unchanged (they are already classical).

FAITHFULNESS — exactly what is (and is not) covered
------------------------------------------------------
1. **Plain FO ∃, in any position.** ``⊨ ∀x̄∃u ψ(x̄,u) ↔ ∃F(∀x̄ ψ(x̄,F(x̄)))`` is a
   basic, unconditional second-order validity (given a witness for every
   ``x̄``, PICK one — a purely combinatorial choice on a finite domain, no
   axiom of choice needed) — the ordinary Skolemisation identity. Dependence
   logic makes this exact: Väänänen 2007, Prop. 3.9 (flatness), shows every
   formula with NO dependence atom and NO slash is FLAT — team truth equals
   ordinary classical truth pointwise — so classical Skolemisation of a
   dependence/slash-FREE sentence, in ANY connective shape (``∧``/``∨`` mixed
   with quantifiers arbitrarily — not just prenex), is faithful to its team
   truth. This is why a *plain FOL* sentence translates to something classically
   equivalent to itself (mod the vacuous Skolem layer if it has any ``∃`` at
   all).
2. **A dependence-atom-guarded or slashed ∃, PROVIDED no ``∨`` is anywhere in
   the sentence.** This is exactly the classical Hintikka–Sandu Skolem/game
   semantics of independence-friendly logic, which Väänänen 2007 (Thm. 4.10 and
   surrounding discussion) shows AGREES with the compositional team semantics
   for a quantifier-and-conjunction prefix over a quantifier-free (dependence
   atoms aside) matrix — the shape this module accepts (arbitrary ``∀``/``∃``/
   ``∃/{…}`` nesting through ``∧``, since ``∧`` commutes freely with an
   existential's Skolem function exactly as in case 1).
3. **``∨`` (the split disjunction) is REJECTED outright whenever the sentence
   contains ANY dependence atom or slashed existential**, even in a part of the
   tree that looks "far away" from the ``∨``. Team-semantic ``∨`` lets the team
   split into ANY partition, and once a non-flat construct (dependence atom,
   slash) is in play this split is exactly the source of dependence logic's
   extra expressive power (Väänänen 2007 §4) — establishing a Skolem-normal-form
   equivalence for ``∨`` mixed with non-flat constructs needs a case analysis
   this module does not attempt. This is the CONSERVATIVE choice the module
   commits to: soundness over coverage. (``∨`` remains fully supported, in any
   position, for a dependence/slash-FREE sentence — case 1 above.)
4. **A "loose" dependence atom** — one that is not a top-level conjunct of the
   IMMEDIATE body of the ``∃`` binding its own dependent variable (e.g. it
   guards a ``∀``-bound variable, sits several ``∧``-levels away from its own
   binder, or names a variable other than the enclosing ``∃``'s) — is rejected:
   the guard extraction only ever looks at an ``∃``'s own immediate (flattened)
   conjunct list, so any dependence atom not consumed there surfaces, unchanged,
   to the generic recursion, which raises.
5. **Shadowing** (the same variable name bound twice along one ancestor chain,
   e.g. ``∀x∃x…``) is rejected: the translation reuses each bound name as-is
   (no fresh-renaming pass), which is sound only when names are not reused
   along a single scope chain. Reuse across SIBLING branches (``∃x φ ∧ ∃x ψ``)
   is unaffected — it is not shadowing.
6. **``¬``** is accepted only in front of an atom (mirroring
   :mod:`unicode_fol_kit.semantics.team`'s own restriction); ``→``/``↔`` are
   not part of the team fragment at all and are rejected immediately (as any
   node outside the recognised shapes is).

The INPUT must already be a SENTENCE (no free object variables) — the same
assumption :func:`unicode_fol_kit.semantics.team.team_models` makes for
starting from the singleton empty-assignment team.

Every rejection raises :class:`NotImplementedError` naming the offending shape
and pointing back at ``team_satisfies`` / ``team_models`` as the fallback
(brute-force, but total over the whole team fragment).

Public API: :func:`dependence_to_eso`.
"""

from typing import FrozenSet, List, Optional, Tuple

from ..fol.nodes import (
    Node, Variable, Atom, Not, And, Or, Implies, Quantifier,
    Dependence, SlashedExists, SecondOrderQuantifier,
)

_FORALL = ("∀", "forall")
_EXISTS = ("∃", "exists")


# ===========================================================================
# And-tree flattening (to locate a guard adjacent to its own ∃, regardless of
# the parser's left-associative nesting) and rebuilding.
# ===========================================================================

def _flatten_and(node: Node) -> List[Node]:
    """Return the list of top-level conjuncts of an (arbitrarily nested) And-tree."""
    if isinstance(node, And):
        return _flatten_and(node.left) + _flatten_and(node.right)
    return [node]


def _rebuild_and(conjuncts: List[Node]) -> Node:
    """Left-fold a non-empty conjunct list back into a binary And-tree."""
    result = conjuncts[0]
    for c in conjuncts[1:]:
        result = And(result, c)
    return result


def _extract_guard(body: Node, var: str) -> Tuple[Optional[Dependence], Optional[Node]]:
    """Find a dependence atom ``=(t̄,var)`` among ``body``'s top-level conjuncts.

    Returns ``(guard, rest)`` where ``rest`` is the And of the remaining
    conjuncts (``None`` if the guard was the ONLY conjunct), or ``(None, None)``
    if no conjunct is a dependence atom whose dependent (last) argument is
    exactly the variable ``var``. Only the FIRST matching conjunct is used.
    """
    conjuncts = _flatten_and(body)
    for i, c in enumerate(conjuncts):
        if (isinstance(c, Dependence) and isinstance(c.args[-1], Variable)
                and c.args[-1].name == var):
            rest_conjuncts = conjuncts[:i] + conjuncts[i + 1:]
            rest = _rebuild_and(rest_conjuncts) if rest_conjuncts else None
            return c, rest
    return None, None


# ===========================================================================
# Totality / functionality axiom for a Skolem graph predicate.
# ===========================================================================

def _forall_chain(vs: List[Variable], body: Node) -> Node:
    """Fold ``∀v1 ∀v2 … body`` over ``vs`` (``body`` unchanged if ``vs`` is empty)."""
    result = body
    for v in reversed(vs):
        result = Quantifier("∀", v, result)
    return result


def _wf_axiom(fname: str, arity: int) -> Node:
    """``F`` is TOTAL and FUNCTIONAL in its first ``arity`` arguments.

    Totality: ``∀x̄ ∃y F(x̄,y)`` (a bare ``∃y F(y)`` when ``arity == 0``, i.e.
    ``F`` is non-empty). Functionality: ``∀x̄∀y1∀y2((F(x̄,y1)∧F(x̄,y2))→y1=y2)``.
    Together these make ``F``'s graph exactly the graph of a total function
    ``dom^arity -> dom`` (a single constant when ``arity == 0``).
    """
    xs = [Variable(f"_{fname}_x{i}") for i in range(arity)]
    y0, y1, y2 = Variable(f"_{fname}_y0"), Variable(f"_{fname}_y1"), Variable(f"_{fname}_y2")
    totality = _forall_chain(xs, Quantifier("∃", y0, Atom(fname, tuple(xs) + (y0,))))
    functionality = _forall_chain(
        xs + [y1, y2],
        Implies(
            And(Atom(fname, tuple(xs) + (y1,)), Atom(fname, tuple(xs) + (y2,))),
            Atom("=", (y1, y2)),
        ),
    )
    return And(totality, functionality)


# ===========================================================================
# The translation
# ===========================================================================

def _contains_any(node: Node, classes) -> bool:
    """Whether any descendant of ``node`` (``node`` included) is an instance of ``classes``."""
    return any(isinstance(n, classes) for n in node.walk())


def _fragment_error(node: Node) -> NotImplementedError:
    """The generic rejection for a node/shape outside the covered fragment."""
    return NotImplementedError(
        f"dependence_to_eso: {type(node).__name__} is outside the fragment this "
        "translation is proven faithful for (literals, ∧, split ∨ in dependence/"
        "slash-FREE sub-formulas, ∀/∃, a dependence atom that is a top-level "
        "conjunct in the immediate body of the ∃ binding its own dependent "
        "variable, and slashed ∃x/{…}); evaluate with "
        "unicode_fol_kit.semantics.team.team_satisfies / team_models instead."
    )


def dependence_to_eso(sentence: Node) -> Node:
    """Translate a dependence-logic SENTENCE to an equivalent ESO formula.

    Returns a classical :class:`~unicode_fol_kit.fol.nodes.Node`, headed by one
    ``∃``-:class:`SecondOrderQuantifier` per Skolemised existential in
    ``sentence`` (zero if ``sentence`` has no existential at all — then the
    result is just the classically-translated formula, unwrapped). The result
    is meant for :func:`unicode_fol_kit.semantics.secondorder.satisfies_so` /
    :func:`holds`, or for :func:`unicode_fol_kit.hol.secondorder.to_isabelle_so`
    / :func:`to_thf_so`. See the module docstring for the exact supported
    grammar and the faithfulness argument.

    Raises:
        NotImplementedError: for any node/shape outside the covered fragment —
            ``∨`` combined (anywhere) with a dependence atom or slashed
            existential, a dependence atom not guarding its own ``∃``, ``¬`` of
            a non-atom, a shadowed (re-bound) variable name, or any node type
            the team fragment itself does not recognise (``→``, ``↔``, …).
    """
    if _contains_any(sentence, (Or,)) and _contains_any(sentence, (Dependence, SlashedExists)):
        raise NotImplementedError(
            "dependence_to_eso: the split disjunction ∨ is combined with a "
            "dependence atom or slashed existential somewhere in this sentence. "
            "∨ lets a team split into ANY partition, and once a non-flat "
            "construct (dependence atom / slash) is present that split is "
            "exactly the source of dependence logic's extra expressive power "
            "(Väänänen 2007 §4) — no Skolem-normal-form equivalence is "
            "established here for that combination, so it is rejected rather "
            "than silently mistranslated. ∨ IS supported anywhere in a "
            "dependence/slash-FREE (plain first-order) sentence. Evaluate the "
            "full sentence with team_satisfies / team_models instead."
        )

    used_preds = {n.predicate for n in sentence.walk() if isinstance(n, Atom)}
    skolems: List[Tuple[str, int]] = []
    wf_axioms: List[Node] = []

    def fresh_pred(base: str) -> str:
        name, candidate, i = f"F_{base}", f"F_{base}", 0
        while candidate in used_preds:
            candidate = f"{name}_{i}"
            i += 1
        used_preds.add(candidate)
        return candidate

    def introduce_skolem(var: Variable, args: Tuple[Node, ...]) -> Atom:
        """Register a fresh Skolem predicate for ``var`` over ``args`` and return its atom."""
        fname = fresh_pred(var.name)
        arity = len(args)
        skolems.append((fname, arity + 1))
        wf_axioms.append(_wf_axiom(fname, arity))
        return Atom(fname, args + (var,))

    def translate(node: Node, foralls: Tuple[str, ...], scope: Tuple[str, ...],
                  bound: FrozenSet[str]) -> Node:
        if isinstance(node, Atom):
            return node

        if isinstance(node, Not):
            if not isinstance(node.formula, Atom):
                raise NotImplementedError(
                    f"dependence_to_eso: ¬ applies only to atoms in the team "
                    f"fragment (found ¬ of a {type(node.formula).__name__}); "
                    "evaluate with team_satisfies / team_models instead."
                )
            return node

        if isinstance(node, Dependence):
            raise NotImplementedError(
                f"dependence_to_eso: the dependence atom {node.to_unicode_str()!r} "
                "does not guard its own existential. The supported canonical "
                "pattern is ∃u(=(t̄,u) ∧ …), where the dependence atom is a "
                "TOP-LEVEL conjunct in the IMMEDIATE body of the ∃ binding its "
                "own dependent variable u; evaluate with team_satisfies / "
                "team_models instead."
            )

        if isinstance(node, And):
            return And(translate(node.left, foralls, scope, bound),
                      translate(node.right, foralls, scope, bound))

        if isinstance(node, Or):
            # Reachable only for a dependence/slash-FREE sentence (checked up
            # front), where ∨ is fully flat and safe in any position.
            return Or(translate(node.left, foralls, scope, bound),
                     translate(node.right, foralls, scope, bound))

        if isinstance(node, Quantifier):
            name = node.variable.name
            if name in bound:
                raise NotImplementedError(
                    f"dependence_to_eso: variable {name!r} is bound twice along "
                    "one scope chain (shadowing); the translation reuses each "
                    "bound name as-is, which requires distinct names along any "
                    "single nesting path. Rename the inner binder."
                )
            new_bound = bound | {name}
            new_scope = scope + (name,)

            if node.type in _FORALL:
                return Quantifier("∀", node.variable,
                                  translate(node.formula, foralls + (name,), new_scope, new_bound))

            if node.type not in _EXISTS:
                raise ValueError(f"dependence_to_eso: unknown quantifier type {node.type!r}.")

            guard, rest = _extract_guard(node.formula, name)
            if guard is not None:
                args = tuple(guard.args[:-1])
            else:
                args = tuple(Variable(n) for n in foralls)
                rest = node.formula
            graph_atom = introduce_skolem(node.variable, args)
            body = (graph_atom if rest is None
                   else And(graph_atom, translate(rest, foralls, new_scope, new_bound)))
            return Quantifier("∃", node.variable, body)

        if isinstance(node, SlashedExists):
            name = node.variable.name
            if name in bound:
                raise NotImplementedError(
                    f"dependence_to_eso: variable {name!r} is bound twice along "
                    "one scope chain (shadowing); the translation reuses each "
                    "bound name as-is, which requires distinct names along any "
                    "single nesting path. Rename the inner binder."
                )
            new_bound = bound | {name}
            new_scope = scope + (name,)
            # Uniformity ("independent of V") is a constraint on the WITNESS
            # FUNCTION'S visible ARGUMENTS, checked by NAME against every
            # variable bound so far (∀ or ∃) — not just the enclosing ∀'s. An
            # intervening ∃ that happens to be a deterministic function of a
            # slashed ∀ (e.g. ∃z(z=x ∧ ∃y/{x} …)) is NOT itself named in the
            # slash set, so it stays visible and the "independent" witness can
            # still depend on it — the signalling phenomenon (Väänänen 2007
            # §4; Hodges' compositional semantics for IF logic). Using `scope`
            # (every bound name so far) rather than `foralls` here is what
            # makes this case translate faithfully.
            args = tuple(Variable(n) for n in scope if n not in node.slashed)
            graph_atom = introduce_skolem(node.variable, args)
            body = And(graph_atom, translate(node.formula, foralls, new_scope, new_bound))
            return Quantifier("∃", node.variable, body)

        raise _fragment_error(node)

    core = translate(sentence, foralls=(), scope=(), bound=frozenset())
    combined = _rebuild_and(list(wf_axioms) + [core])
    result = combined
    for fname, arity in skolems:
        result = SecondOrderQuantifier("∃", fname, arity, result)
    return result
