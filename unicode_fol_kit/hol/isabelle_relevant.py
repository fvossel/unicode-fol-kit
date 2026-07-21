r"""Isabelle/HOL export for relevant logic B (simplified Routley-Meyer semantics).

The modal exporter (:mod:`unicode_fol_kit.hol.isabelle_modal`) embeds a formula
over a single accessibility relation and reads truth as box/diamond over it. B's
``->`` is not that: it is the Priest-Sylvan **simplified** Routley-Meyer clause
implemented by :mod:`unicode_fol_kit.semantics.relevant` -- normal worlds get a
"material" reading (quantify over the WHOLE model), non-normal worlds route
through a ternary relation ``R`` -- so it needs its own embedding, which is what
this module emits.

Like :mod:`unicode_fol_kit.hol.isabelle_conditional`, the embedding is
*lightweight shallow*: a formula becomes a predicate on worlds (``tau = w =>
bool``) and each propositional atom is an uninterpreted ``w => bool`` constant.
The frame structure -- the normal-worlds predicate ``N``, the Routley star
``star`` and the ternary relation ``R`` -- are uninterpreted consts, and the
frame conditions :class:`~unicode_fol_kit.semantics.relevant.RelevantModel`
enforces in its ``__post_init__`` are bundled into a single ``wellformed``
proposition that is a **premise of the goal**, never an ``axiomatization``:

- ``N`` is nonempty (``relevant.py`` lines 121-122: ``if not normal: raise
  ValueError``);
- ``star`` is a total involution on ``W`` (lines 126-135: ``star[star[w]] ==
  w`` for every ``w``) -- totality of the ``w`` -> ``w`` map is free in HOL's
  total function type, so only involution needs stating;
- ``R`` is sourced only at NON-normal worlds, i.e. ``R subseteq (W \ N) x W x
  W`` (lines 142-145: ``if a in normal: raise ValueError``).

As a premise (mirroring ``nested Sel`` in ``isabelle_conditional``), nitpick
constructs ``N``/``star``/``R`` itself and can certify a countermodel as
*genuine* -- axiomatising them instead would downgrade nitpick's verdict to
``quasi_genuine`` and lose the refutation half of the decision procedure.

No hereditariness / persistence condition is encoded because
:class:`~unicode_fol_kit.semantics.relevant.RelevantModel` does not impose one:
its ``__post_init__`` places no monotonicity constraint on ``valuation``
(unlike, say, an intuitionistic Kripke model) -- this is exactly the
"simplified" in "simplified Routley-Meyer semantics" (Priest & Sylvan 1992),
which drops the compatibility/heredity apparatus of the original relational
semantics for B. So atoms are plain uninterpreted ``tau`` constants here, same
as in ``isabelle_conditional``.

``AndC``/``OrC``/``NegC``/``ImpC``/``IffC`` are the same truth conditions as
:func:`unicode_fol_kit.semantics.relevant.rel_satisfies`'s ``_sat`` clauses, so
what Isabelle certifies here is what the toolkit's own evaluator computes:

- ``w |= A /\ B`` / ``w |= A \/ B`` pointwise (``_sat`` And/Or clauses);
- ``w |= ~A`` iff ``w* |=/ A`` -- the Routley star (``_sat`` Not clause);
- ``w |= A -> B``, ``w`` normal, iff every ``A``-world of the WHOLE model is a
  ``B``-world (``_sat`` Implies clause, ``world in model.normal`` branch);
- ``w |= A -> B``, ``w`` non-normal, iff for every triple ``R(w, x, y)``,
  ``x |= A`` implies ``y |= B`` (``_sat`` Implies clause, ``else`` branch);
- ``w |= A <-> B`` iff ``w |= A -> B`` and ``w |= B -> A`` at the SAME world
  (``_sat`` Iff clause: it recurses on ``Implies(left, right)`` /
  ``Implies(right, left)``, not a primitive biconditional clause) -- so
  ``IffC`` is defined via ``AndC``/``ImpC``, not as its own case split.

Only ``Not``/``And``/``Or``/``Implies``/``Iff`` over nullary atoms are accepted,
matching :func:`unicode_fol_kit.semantics.relevant._reject_non_propositional`
exactly (no quantifiers, modalities, lambda terms, ``Xor``, or non-nullary
atoms -- there is no B reading for them here either).
"""

from typing import Optional, Sequence, Tuple

from ..fol.nodes import Node, Atom, Not, And, Or, Implies, Iff
from .deepshallow._common import AtomConsts, theory_name_ok

#: The Isabelle type of an embedded formula: a predicate on worlds.
_TAU = r"w \<Rightarrow> bool"

#: Definitions the goal has to unfold before a proof method can see through it.
_DEFS = ("wellformed_def", "NegC_def", "AndC_def", "OrC_def", "ImpC_def", "IffC_def")

#: Proof methods tried in order, as a ``by (... | ...)`` battery. ``smt (verit)``
#: is tried first as a precaution, not a measured choice: house rules forbid
#: running ``isabelle build`` from this toolkit, so this ordering has not been
#: benchmarked. It mirrors ``isabelle_conditional.DEFAULT_METHODS``, whose
#: verit-first order *was* measured necessary there because ``blast`` diverges
#: on a goal that needs the sphere-nesting premise. ``ImpC`` here has an
#: analogous shape -- a case split on ``N x`` with a nested ``forall y z. R x y
#: z -> ...`` on one branch -- so the same defensive ordering is used rather
#: than assuming ``blast``-first is safe.
DEFAULT_METHODS: Tuple[str, ...] = ("smt (verit)", "blast", "force", "metis")

_PREAMBLE = r'''typedecl w  \<comment> \<open>worlds\<close>
type_synonym tau = "w \<Rightarrow> bool"

consts N :: "w \<Rightarrow> bool"              \<comment> \<open>N w: w is a NORMAL world\<close>
consts star :: "w \<Rightarrow> w"             \<comment> \<open>the Routley star w |-> w*\<close>
consts R :: "w \<Rightarrow> w \<Rightarrow> w \<Rightarrow> bool"  \<comment> \<open>the ternary relation R w x y\<close>

text \<open>The three well-formedness conditions RelevantModel.__post_init__ enforces
(semantics/relevant.py lines 121-145): N is nonempty, star is a total involution
on W (totality is free in HOL's total function type w => w, so only involution
is stated), and R is sourced only at NON-normal worlds. Bundled as a single
premise of the goal rather than baked into N/star/R by fiat, so nitpick builds
N/star/R itself and can certify a counter-model as genuine.\<close>

definition wellformed :: "bool" where
  "wellformed \<equiv> (\<exists>x. N x) \<and> (\<forall>x. star (star x) = x)
                \<and> (\<forall>x y z. R x y z \<longrightarrow> \<not> N x)"

definition NegC :: "tau \<Rightarrow> tau" where "NegC f \<equiv> \<lambda>x. \<not> f (star x)"
definition AndC :: "tau \<Rightarrow> tau \<Rightarrow> tau" where "AndC f g \<equiv> \<lambda>x. f x \<and> g x"
definition OrC  :: "tau \<Rightarrow> tau \<Rightarrow> tau" where "OrC f g \<equiv> \<lambda>x. f x \<or> g x"

text \<open>A -> B at a NORMAL world w: every A-world of the WHOLE model is a B-world
(relevant.py _sat, the ``world in model.normal`` branch). At a NON-normal world:
for every R-triple R w x y, x |= A implies y |= B (the ``else`` branch).\<close>

definition ImpC :: "tau \<Rightarrow> tau \<Rightarrow> tau" where
  "ImpC f g \<equiv> \<lambda>x.
     (N x \<longrightarrow> (\<forall>y. f y \<longrightarrow> g y))
     \<and> (\<not> N x \<longrightarrow> (\<forall>y z. R x y z \<longrightarrow> f y \<longrightarrow> g z))"

text \<open>A <-> B is (A -> B) /\ (B -> A) at the SAME world (relevant.py _sat's Iff
clause recurses on Implies(left,right)/Implies(right,left) -- not a primitive
biconditional clause), so IffC is built from ImpC/AndC rather than case-split
directly.\<close>

definition IffC :: "tau \<Rightarrow> tau \<Rightarrow> tau" where
  "IffC f g \<equiv> AndC (ImpC f g) (ImpC g f)"
'''


def _encode(formula: Node, atoms: AtomConsts) -> str:
    """Recursive worker for :func:`to_isabelle_relevant`.

    Mirrors :func:`unicode_fol_kit.semantics.relevant._reject_non_propositional`
    exactly: only nullary :class:`Atom`\\ s and the connectives Not/And/Or/
    Implies/Iff are accepted; everything else -- quantifiers, modalities, lambda
    terms, ``Xor``, non-nullary atoms -- raises :class:`TypeError`, the same
    exception type the oracle raises for the same inputs.
    """
    if isinstance(formula, Atom):
        if formula.args:
            raise TypeError(
                "to_isabelle_relevant: only nullary propositional atoms are "
                f"supported; got {formula.to_unicode_str()!r} with arguments -- "
                "matching semantics.relevant._reject_non_propositional's "
                "rejection of non-nullary atoms.")
        return atoms.name(formula.to_unicode_str())
    if isinstance(formula, And):
        return f"(AndC {_encode(formula.left, atoms)} {_encode(formula.right, atoms)})"
    if isinstance(formula, Or):
        return f"(OrC {_encode(formula.left, atoms)} {_encode(formula.right, atoms)})"
    if isinstance(formula, Not):
        return f"(NegC {_encode(formula.formula, atoms)})"
    if isinstance(formula, Implies):
        return f"(ImpC {_encode(formula.left, atoms)} {_encode(formula.right, atoms)})"
    if isinstance(formula, Iff):
        return f"(IffC {_encode(formula.left, atoms)} {_encode(formula.right, atoms)})"
    raise TypeError(
        f"to_isabelle_relevant: unsupported node type {type(formula).__name__} "
        f"in {formula.to_unicode_str()!r}. The B semantics "
        "(semantics.relevant) interprets only the propositional connectives "
        "not/and/or/implies/iff over nullary atoms -- no quantifiers, "
        "modalities, lambda terms, or Xor; see "
        "semantics.relevant._reject_non_propositional.")


def battery_proof(methods: Sequence[str] = DEFAULT_METHODS) -> str:
    """An ``unfolding ...`` + ``by (m1 | m2 | ...)`` proof over the shallow definitions."""
    if not methods:
        raise ValueError("battery_proof: need at least one proof method.")
    alts = " | ".join(methods)
    return f"  unfolding {' '.join(_DEFS)}\n  by ({alts})"


def nitpick_proof(card: str = "1-3", timeout: int = 60) -> str:
    """A ``nitpick[expect = genuine]`` refutation attempt over the world type ``w``."""
    return (f"  nitpick[card w = {card}, timeout = {int(timeout)}, "
            f"expect = genuine]\n  oops")


def to_isabelle_relevant(formula: Node, *,
                         theory_name: str = "RelDecide",
                         proof: Optional[str] = None,
                         lemma_name: str = "goal") -> str:
    r"""Emit a self-contained theory asserting ``formula``'s validity in B.

    The goal is ``wellformed \<Longrightarrow> \<forall>x. N x \<longrightarrow> phi x`` --
    truth at every NORMAL world of every interpretation satisfying the frame
    conditions bundled into ``wellformed`` (see the module docstring), matching
    :func:`unicode_fol_kit.semantics.relevant.rel_valid`'s "true at every normal
    world of every interpretation" contract. ``wellformed`` is a premise rather
    than an axiom so that nitpick can build ``N``/``star``/``R`` itself and
    certify a counter-model as genuine.

    Args:
        formula: the AST node to decide -- the propositional connectives
            ``¬ ∧ ∨ → ↔`` over nullary atoms.
        theory_name: the Isabelle theory identifier.
        proof: the proof text under the lemma; defaults to :func:`battery_proof`.
            Pass :func:`nitpick_proof` to emit the refutation theory instead.
        lemma_name: the lemma identifier.

    Raises:
        ValueError: on an illegal theory name.
        TypeError: propagated from :func:`_encode` -- a quantifier, modality,
            lambda term, ``Xor``, or non-nullary atom, mirroring
            :func:`unicode_fol_kit.semantics.relevant._reject_non_propositional`.
    """
    if not theory_name_ok(theory_name):
        raise ValueError(f"illegal theory name {theory_name!r}.")
    atoms = AtomConsts()
    term = _encode(formula, atoms)
    body = [f"theory {theory_name}", "  imports Main", "begin", "", _PREAMBLE]
    decls = atoms.decls(_TAU)
    if decls:
        body.append("\n".join(decls))
        body.append("")
    body.append(
        f'lemma {lemma_name}: "wellformed \\<Longrightarrow> '
        f'\\<forall>x. N x \\<longrightarrow> ({term}) x"')
    body.append(proof if proof is not None else battery_proof())
    body.append("")
    body.append("end")
    return "\n".join(body) + "\n"
