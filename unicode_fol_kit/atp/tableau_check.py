"""Independent classical-tableau proof CHECKER (not a searcher).

Where :mod:`unicode_fol_kit.atp.tableau` SEARCHES for a closed tableau
(``prove_tableau`` / ``prove_tableau_detailed``), this module CERTIFIES one that
was produced elsewhere: given a :class:`~unicode_fol_kit.atp.tableau.TableauProof`
(the flat, node-ID-addressed rule-application tree ``prove_tableau_detailed``
records), :func:`check_tableau_proof` decides, independently, whether it
genuinely refutes ``premises ∪ {¬conclusion}`` — the same division of labour as
:mod:`atp.resolution_check` (resolution refutations) and :mod:`atp.twee_check`
(Twee proofs): a proof produced by a search procedure is only as trustworthy as
an INDEPENDENT re-check of it, so the tableau *search* is trusted only to
search, never for soundness.

Four things are checked, none of them by trusting a flag the search itself set:

1. **Root** — ``proof.root_formulas`` must be EXACTLY ``premises`` followed by
   ``¬conclusion``, structurally, in that order. This is the boundary that
   catches a proof that is internally flawless but answers a different
   question (e.g. the conclusion left un-negated).
2. **Every step is a genuine rule instance, RE-DERIVED from scratch** —
   first, the step's ``principal_formula`` must GENUINELY BE ON THE BRANCH it
   extends (a root formula, or produced by an ancestor step — for a β split,
   on the branch down to the split node): without this membership check a
   fabricated proof could "decompose" an invented contradiction unrelated to
   the premises/conclusion, close on its components, and pass every shape
   check (found by the Tier-3 adversarial review). Then
   :func:`_expected_shape` reclassifies ``step.principal_formula`` by the same
   α/β/γ/δ case split :mod:`atp.tableau`'s own ``_rule`` makes, but as an
   independent re-implementation (never imported — see below): α must
   decompose into exactly its declared components; β's two sibling steps (same
   ``parent_id``, same ``principal_formula``, both ``branch_split=True``) must
   be exactly its two alternatives, in either order; γ's ``produced``/``terms``
   must be the matrix substituted by each declared term — the substitution is
   RECOMPUTED here, not trusted; δ's ``produced`` must be the matrix
   substituted by the declared ``fresh_constant``, AND that constant must not
   occur anywhere earlier on the same branch (nor in the root formulas) —
   re-checked independently, since a reused "fresh" constant is the classical
   soundness hole in this rule: it lets a witness for one existential silently
   stand for an already-constrained individual, licensing an unsound proof.
3. **Every closed branch's pair is really on that branch** — a
   :class:`~atp.tableau.TableauClosure` names the two branch nodes where its
   literal and complement supposedly occur; the checker walks the ACTUAL
   parent-chain from the closure's leaf back to the root and verifies both
   cited nodes are genuinely on it, and that the named formula really is in
   that node's own ``produced`` (or, at the root, ``root_formulas``) — trusting
   neither the node-ID citation nor the formula label without this.
   Complementarity itself (``φ`` vs ``¬φ``, or a bare ⊥) is re-derived
   structurally, not read off any flag on the closure.
4. **Completeness** — every LEAF of the recorded tree (a node no step cites as
   its ``parent_id``) must carry a closure. One open leaf means the tableau
   never actually closed, no matter how many other branches did.

Independence, concretely (mirrors :mod:`atp.resolution_check`'s module
docstring): the α/β/γ/δ case split is RE-IMPLEMENTED from scratch here
(:func:`_expected_shape`) rather than importing :mod:`atp.tableau`'s ``_rule``
— a bug shared between the search's own rule dispatch and the checker's would
be invisible to both. Substitution reuses
:func:`unicode_fol_kit.fol.nodes.substitute` — the generic, capture-avoiding
MSFL-level substitution already used elsewhere in the kit for beta-reduction
and quantifier grounding — rather than :mod:`atp.tableau`'s own ``_subst_var``:
a DIFFERENT implementation of the same specification, which is exactly the
independence a checker needs (the same principle behind ``atp.twee_check``
reusing only the generic, direction-agnostic ``apply_subst`` while
re-implementing the direction-SENSITIVE rewrite matching itself).
Complementarity (``_is_complement``) and falsum recognition (``_is_falsum``)
are likewise re-implemented locally here, not imported from
``atp.fitch``/``atp.tableau``.

Public API: :class:`TableauCheckError`, :func:`check_tableau_proof`,
:func:`check_entailment_tableau_detailed`.
"""

from typing import Dict, List, Optional, Sequence, Tuple

from ..fol.nodes import (
    Node, Atom, Not, And, Or, Xor, Implies, Iff, Quantifier, Variable, Constant,
    Contrast, Count, substitute,
)
from .tableau import TableauProof, TableauStep, TableauClosure, prove_tableau_detailed

__all__ = ["TableauCheckError", "check_tableau_proof", "check_entailment_tableau_detailed"]


class TableauCheckError(ValueError):
    """Raised by :func:`check_tableau_proof` when a proof does not check out."""


# ---------------------------------------------------------------------------
# Independent structural predicates — NOT imported from atp.tableau/atp.fitch
# (see module docstring: falsum recognition and complementarity are the
# kind of "small vocabulary" a shared bug could hide in, so they are
# re-implemented here from the reserved-symbol/shape definitions directly).
# ---------------------------------------------------------------------------

def _is_falsum(f: Node) -> bool:
    """True iff ``f`` is the reserved nullary falsum atom ``⊥``."""
    return isinstance(f, Atom) and f.predicate == "⊥" and not f.args


def _is_complement(a: Node, b: Node) -> bool:
    """True iff ``a`` and ``b`` are ``φ`` / ``¬φ`` for some ``φ``, in either order."""
    if isinstance(a, Not) and a.formula == b:
        return True
    if isinstance(b, Not) and b.formula == a:
        return True
    return False


def _is_forall(f: Node) -> bool:
    """True iff ``f`` is an (unsorted) universal quantifier."""
    return isinstance(f, Quantifier) and f.type in ("forall", "∀")


def _is_exists(f: Node) -> bool:
    """True iff ``f`` is an (unsorted) existential quantifier."""
    return isinstance(f, Quantifier) and f.type in ("exists", "∃")


# ---------------------------------------------------------------------------
# Independent rule re-derivation — see module docstring, independence
# requirement 1. A structural twin of atp.tableau._rule, written from
# scratch here rather than imported.
# ---------------------------------------------------------------------------

def _expected_shape(f: Node):
    """Re-derive which tableau rule applies to ``f``, and its expansion.

    Returns ``("alpha", [comp, ...])``, ``("beta", [[...], [...]])``,
    ``("gamma", var, body, neg)``, or ``("delta", var, body, neg)`` — the same
    shapes :mod:`atp.tableau`'s own (unimported) ``_rule`` computes, for the
    same node families it handles. Raises :class:`TableauCheckError` if no
    tableau rule applies to ``f`` (e.g. it is already a literal, or an
    exotic/second-order node family a genuine proof could never have
    decomposed this way).
    """
    if isinstance(f, And):
        return ("alpha", [f.left, f.right])
    if isinstance(f, Contrast):
        return ("alpha", [f.left, f.right])
    if isinstance(f, Or):
        return ("beta", [[f.left], [f.right]])
    if isinstance(f, Implies):
        return ("beta", [[Not(f.left)], [f.right]])
    if isinstance(f, Iff):
        return ("beta", [[f.left, f.right], [Not(f.left), Not(f.right)]])
    if isinstance(f, Xor):
        return ("beta", [[f.left, Not(f.right)], [Not(f.left), f.right]])
    if isinstance(f, Count):
        return ("alpha", [f._expand()])
    if _is_exists(f):
        return ("delta", (f.variable, f.formula, False))
    if _is_forall(f):
        return ("gamma", (f.variable, f.formula, False))
    if isinstance(f, Not):
        g = f.formula
        if isinstance(g, Not):
            return ("alpha", [g.formula])
        if isinstance(g, And):
            return ("beta", [[Not(g.left)], [Not(g.right)]])
        if isinstance(g, Contrast):
            return ("beta", [[Not(g.left)], [Not(g.right)]])
        if isinstance(g, Or):
            return ("alpha", [Not(g.left), Not(g.right)])
        if isinstance(g, Implies):
            return ("alpha", [g.left, Not(g.right)])
        if isinstance(g, Iff):
            return ("beta", [[g.left, Not(g.right)], [Not(g.left), g.right]])
        if isinstance(g, Xor):
            return ("beta", [[g.left, g.right], [Not(g.left), Not(g.right)]])
        if isinstance(g, Count):
            return ("alpha", [Not(g._expand())])
        if _is_forall(g):
            return ("delta", (g.variable, g.formula, True))
        if _is_exists(g):
            return ("gamma", (g.variable, g.formula, True))
    raise TableauCheckError(
        f"no tableau rule applies to principal formula {f.to_unicode_str()!r} "
        "(it is already a literal, or an exotic node family)")


def _expected_instance(var: Variable, body: Node, neg: bool, term: Node) -> Node:
    """Independently recompute ``body[var := term]`` (negated when ``neg``).

    Uses :func:`unicode_fol_kit.fol.nodes.substitute` — capture-avoiding, but a
    DIFFERENT implementation from :mod:`atp.tableau`'s own ``_subst_var`` (see
    module docstring, independence requirement 2).
    """
    inst = substitute(body, var, term)
    return Not(inst) if neg else inst


def _same_formula_list(a: Sequence[Node], b: Sequence[Node]) -> bool:
    """True iff the two SEQUENCES are pairwise equal, position by position."""
    return len(a) == len(b) and all(x == y for x, y in zip(a, b))


# ---------------------------------------------------------------------------
# Branch bookkeeping: a step's ancestor chain via its own recorded
# parent_id, and the formulas actually visible on a branch up to a node.
# ---------------------------------------------------------------------------

def _ancestor_chain(node_id: int, steps_by_id: Dict[int, TableauStep]) -> List[int]:
    """Step IDs from ``node_id`` (inclusive, if nonzero) up to (excluding) the root."""
    chain = []
    cur = node_id
    while cur != 0:
        chain.append(cur)
        cur = steps_by_id[cur].parent_id
    return chain


def _formulas_up_to(node_id: int, steps_by_id: Dict[int, TableauStep],
                    root_formulas: Tuple[Node, ...]) -> List[Node]:
    """All formulas on the branch from the root down to and including ``node_id``."""
    chain = _ancestor_chain(node_id, steps_by_id)
    formulas = list(root_formulas)
    for sid in reversed(chain):
        formulas.extend(steps_by_id[sid].produced)
    return formulas


def _occurs_anywhere(term: Node, formulas: Sequence[Node]) -> bool:
    """True iff ``term`` occurs as a subterm (structurally) anywhere in ``formulas``."""
    return any(node == term for f in formulas for node in f.walk())


# ---------------------------------------------------------------------------
# Per-step / per-split verification. Each returns None (licensed) or an
# error string (WITHOUT any "step N"/"node N" prefix — added by the caller).
# ---------------------------------------------------------------------------

def _verify_alpha_gamma_delta(step: TableauStep, expected_kind: str, payload,
                              steps_by_id: Dict[int, TableauStep],
                              root_formulas: Tuple[Node, ...]) -> Optional[str]:
    """Check a non-branching step's ``produced``/``terms``/``fresh_constant``."""
    if expected_kind == "alpha":
        if not _same_formula_list(step.produced, payload):
            return ("'alpha' step's produced formulas are not the principal "
                    "formula's own components")
        return None
    if expected_kind == "gamma":
        var, body, neg = payload
        if not step.terms or len(step.terms) != len(step.produced):
            return "'gamma' step must record exactly one term per produced formula"
        for p, t in zip(step.produced, step.terms):
            if p != _expected_instance(var, body, neg, t):
                return (f"'gamma' step's substitution does not check out: "
                        f"instantiating at {t.to_unicode_str()!r} does not "
                        f"produce {p.to_unicode_str()!r}")
        return None
    if expected_kind == "delta":
        var, body, neg = payload
        if len(step.produced) != 1:
            return "'delta' step must produce exactly one formula"
        c = step.fresh_constant
        if not isinstance(c, Constant):
            return "'delta' step must record its witnessing constant"
        if step.produced[0] != _expected_instance(var, body, neg, c):
            return (f"'delta' step's substitution does not check out: witnessing "
                    f"with {c.to_unicode_str()!r} does not produce "
                    f"{step.produced[0].to_unicode_str()!r}")
        prior = _formulas_up_to(step.parent_id, steps_by_id, root_formulas)
        if _occurs_anywhere(c, prior):
            return (f"'delta' step's witnessing constant {c.to_unicode_str()!r} "
                    "already occurs earlier on this branch (or in the root "
                    "formulas) — it is not fresh")
        return None
    raise AssertionError(expected_kind)


def _verify_beta_pair(parent_id: int, children: List[TableauStep],
                      expected_kind: str, payload) -> Optional[str]:
    """Check a beta split's two sibling steps against the rule's two alternatives."""
    if expected_kind != "beta":
        return (f"node {parent_id} has two children sharing a principal formula, "
                f"but that formula is a {expected_kind!r}-rule formula, not a beta")
    if len(children) != 2:
        return f"node {parent_id}: a 'beta' split must have exactly 2 children, got {len(children)}"
    a, b = children
    if not (a.branch_split and b.branch_split):
        return f"node {parent_id}: both children of a 'beta' split must have branch_split=True"
    if a.principal_formula != b.principal_formula:
        return f"node {parent_id}: the two 'beta' children cite different principal formulas"
    alt1, alt2 = payload
    if ((_same_formula_list(a.produced, alt1) and _same_formula_list(b.produced, alt2)) or
            (_same_formula_list(a.produced, alt2) and _same_formula_list(b.produced, alt1))):
        return None
    return (f"node {parent_id}: the 'beta' children's produced formulas are not "
            "the principal formula's two alternatives")


# ---------------------------------------------------------------------------
# The checker
# ---------------------------------------------------------------------------

def check_tableau_proof(proof: TableauProof, premises, conclusion: Node) -> None:
    """Independently verify ``proof`` refutes ``premises ∪ {¬ conclusion}``.

    Raises :class:`TableauCheckError` naming the first problem found (see the
    module docstring for the four things checked). Returns ``None`` (no
    exception) iff every check passes.
    """
    if not isinstance(proof, TableauProof):
        raise TableauCheckError(f"expected a TableauProof, got {type(proof).__name__}")

    expected_root = tuple(premises) + (Not(conclusion),)
    if not _same_formula_list(proof.root_formulas, expected_root):
        raise TableauCheckError(
            "root formulas are not exactly premises followed by the negated "
            "conclusion (structurally) — got "
            f"{[f.to_unicode_str() for f in proof.root_formulas]}, expected "
            f"{[f.to_unicode_str() for f in expected_root]}")

    # --- structural validity of every step, and the parent/child skeleton ---
    steps_by_id: Dict[int, TableauStep] = {}
    for pos, step in enumerate(proof.steps):
        expected_id = pos + 1
        if not isinstance(step, TableauStep):
            raise TableauCheckError(f"step {expected_id}: expected a TableauStep, got {type(step).__name__}")
        if step.step_id != expected_id:
            raise TableauCheckError(
                f"step {step.step_id}: step_id must equal its 1-based position "
                f"in the derivation (expected {expected_id})")
        if step.rule not in ("alpha", "beta", "gamma", "delta"):
            raise TableauCheckError(f"step {step.step_id}: unknown rule {step.rule!r}")
        if not (0 <= step.parent_id < step.step_id):
            raise TableauCheckError(
                f"step {step.step_id}: parent_id {step.parent_id} must be 0 (root) "
                "or a strictly earlier step")
        if step.rule == "beta" and not step.branch_split:
            raise TableauCheckError(f"step {step.step_id}: a 'beta' step must have branch_split=True")
        if step.rule != "beta" and step.branch_split:
            raise TableauCheckError(f"step {step.step_id}: only a 'beta' step may have branch_split=True")
        steps_by_id[step.step_id] = step

    children_of: Dict[int, List[TableauStep]] = {}
    for step in proof.steps:
        children_of.setdefault(step.parent_id, []).append(step)

    # --- re-derive and check every non-beta step's rule instance ---
    for step in proof.steps:
        if step.rule == "beta":
            continue  # verified once per SPLIT below, together with its sibling
        # The principal formula must GENUINELY be on the branch being
        # extended (root formulas + every ancestor's produced formulas) —
        # without this, a fabricated proof could "decompose" an invented
        # formula unrelated to the premises/conclusion, manufacture a
        # trivial closure from its components, and pass every shape check
        # (adversarial review, Tier 3: the checker certified exactly such
        # a fabrication before this membership check existed).
        on_branch = _formulas_up_to(step.parent_id, steps_by_id,
                                    proof.root_formulas)
        if not any(step.principal_formula == f for f in on_branch):
            raise TableauCheckError(
                f"step {step.step_id}: principal formula "
                f"{step.principal_formula.to_unicode_str()!r} is not on the "
                "branch it extends (neither a root formula nor produced by "
                "an ancestor step)")
        try:
            expected_kind, payload = _expected_shape(step.principal_formula)
        except TableauCheckError as exc:
            raise TableauCheckError(f"step {step.step_id}: {exc}") from exc
        if expected_kind != step.rule:
            raise TableauCheckError(
                f"step {step.step_id}: declared rule {step.rule!r} does not match "
                f"the principal formula's actual shape ({expected_kind!r} expected)")
        err = _verify_alpha_gamma_delta(step, expected_kind, payload, steps_by_id, proof.root_formulas)
        if err is not None:
            raise TableauCheckError(f"step {step.step_id}: {err}")

    # --- check the branching shape at every node (0, 1, or exactly-2-as-beta children) ---
    all_ids = {0} | set(steps_by_id)
    for node_id in all_ids:
        kids = children_of.get(node_id, [])
        if len(kids) == 0:
            continue
        if len(kids) == 1:
            child = kids[0]
            if child.branch_split:
                raise TableauCheckError(
                    f"node {node_id}: has a single child but that child has branch_split=True")
            continue
        principal = kids[0].principal_formula
        # Same branch-membership requirement as for non-beta steps: the
        # split's shared principal formula must live on the branch down to
        # the common parent (the split node itself).
        on_branch = _formulas_up_to(node_id, steps_by_id, proof.root_formulas)
        if not any(principal == f for f in on_branch):
            raise TableauCheckError(
                f"node {node_id}: the 'beta' split's principal formula "
                f"{principal.to_unicode_str()!r} is not on the branch it "
                "splits (neither a root formula nor produced by an ancestor "
                "step)")
        try:
            expected_kind, payload = _expected_shape(principal)
        except TableauCheckError as exc:
            raise TableauCheckError(f"node {node_id}: {exc}") from exc
        err = _verify_beta_pair(node_id, kids, expected_kind, payload)
        if err is not None:
            raise TableauCheckError(err)

    # --- closures: every cited node/formula pair must genuinely be on the branch ---
    closures_by_leaf: Dict[int, List[TableauClosure]] = {}
    for closure in proof.closures:
        if closure.leaf_id not in all_ids:
            raise TableauCheckError(f"closure cites unknown node {closure.leaf_id}")
        if children_of.get(closure.leaf_id):
            raise TableauCheckError(
                f"closure cites node {closure.leaf_id}, which is not a leaf "
                "(it has further steps)")
        eligible = {0} | set(_ancestor_chain(closure.leaf_id, steps_by_id))

        def _on_branch(formula: Node, step_id: int, label: str) -> Optional[str]:
            if step_id not in eligible:
                return (f"{label} cites node {step_id}, which is not on the "
                        f"branch ending at {closure.leaf_id}")
            source = proof.root_formulas if step_id == 0 else steps_by_id[step_id].produced
            if not any(formula == f for f in source):
                return f"{label} formula does not actually occur at cited node {step_id}"
            return None

        err = _on_branch(closure.literal, closure.literal_step_id, "closure's literal")
        if err is not None:
            raise TableauCheckError(err)

        if closure.complement is None:
            if not _is_falsum(closure.literal):
                raise TableauCheckError(
                    f"closure at node {closure.leaf_id} has no complement but its "
                    "literal is not ⊥")
        else:
            if closure.complement_step_id is None:
                raise TableauCheckError(
                    f"closure at node {closure.leaf_id} has a complement but no complement_step_id")
            err = _on_branch(closure.complement, closure.complement_step_id, "closure's complement")
            if err is not None:
                raise TableauCheckError(err)
            if not _is_complement(closure.literal, closure.complement):
                raise TableauCheckError(
                    f"closure at node {closure.leaf_id}: "
                    f"{closure.literal.to_unicode_str()!r} and "
                    f"{closure.complement.to_unicode_str()!r} are not complementary")
        closures_by_leaf.setdefault(closure.leaf_id, []).append(closure)

    # --- completeness: every leaf must be closed ---
    for node_id in all_ids:
        if children_of.get(node_id):
            continue  # not a leaf
        if not closures_by_leaf.get(node_id):
            raise TableauCheckError(f"branch ending at node {node_id} has no recorded closure (open branch)")


def check_entailment_tableau_detailed(premises, conclusion: Node, max_steps: int = 20000,
                                      max_terms: int = 8) -> dict:
    """Search AND independently check a tableau proof of ``premises ⊨ conclusion``.

    Runs :func:`unicode_fol_kit.atp.tableau.prove_tableau_detailed`, then — iff
    it found a closed tableau — :func:`check_tableau_proof`. Returns a dict:

    * ``proved``: True iff a closed tableau was found within the budget (the
      raw search verdict — mirrors ``prove_tableau``'s own bool, so this is
      never a claim of invalidity when False; see that function's docstring).
    * ``proof``: the :class:`~atp.tableau.TableauProof`, or ``None``.
    * ``check_passed``: True/False iff a proof was found and independently
      (re-)verified; ``None`` if no proof was found (nothing to check).
    * ``check_error``: the :class:`TableauCheckError` message when
      ``check_passed`` is False, else ``None``.
    """
    proof = prove_tableau_detailed(premises, conclusion, max_steps=max_steps, max_terms=max_terms)
    if proof is None:
        return {"proved": False, "proof": None, "check_passed": None, "check_error": None}
    try:
        check_tableau_proof(proof, premises, conclusion)
    except TableauCheckError as exc:
        return {"proved": True, "proof": proof, "check_passed": False, "check_error": str(exc)}
    return {"proved": True, "proof": proof, "check_passed": True, "check_error": None}
