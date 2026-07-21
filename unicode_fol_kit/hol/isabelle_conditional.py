r"""Isabelle/HOL export for the Lewis counterfactual conditionals ``□→`` / ``◇→``.

The modal exporter (:mod:`unicode_fol_kit.hol.isabelle_modal`) embeds ``□``/``◇``
over an **accessibility relation**; a counterfactual is not evaluated that way. Its
truth condition reads a **similarity ordering** — Lewis's system of spheres — so it
needs its own embedding, which is what this module emits.

The embedding is the *lightweight shallow* one: a formula becomes a predicate on
worlds (``tau = w ⇒ bool``), the sphere system is the uninterpreted constant
``Sel``, and each propositional atom is an uninterpreted ``w ⇒ bool`` constant.
Validity is ``nested Sel ⟹ ∀x. φ x``.

``nested`` appears as a **premise of the goal**, never as an ``axiomatization``.
That is deliberate: nitpick cannot certify a model as *genuine* while axiomatised
constants are in play (it has no way to check the axioms are consistent) and
downgrades the verdict to ``quasi_genuine``, which would lose us the refutation
half of the decision procedure. As a premise, nitpick constructs ``Sel`` itself.

``CondC`` is the same truth condition as
:func:`unicode_fol_kit.semantics.conditional.cf_satisfies` and as the ``CondM``
clause of :mod:`unicode_fol_kit.hol.deepshallow.conditional`, so what Isabelle
certifies here is what the toolkit's own evaluator computes.
"""

from typing import Dict, List, Optional, Sequence, Tuple, Type

from ..fol.nodes import (
    Node, Atom, Not, And, Or, Xor, Implies, Iff, Would, Might,
    Variable, Quantifier,
)
from .deepshallow._common import AtomConsts, theory_name_ok

#: The Isabelle type of an embedded formula: a predicate on worlds.
_TAU = r"w \<Rightarrow> bool"

#: Toolkit node type -> (shallow constant, arity). ``Xor`` and ``Might`` are
#: desugared rather than given constants of their own, matching the way the
#: evaluator derives them.
_CONNECTIVES: Dict[Type[Node], Tuple[str, int]] = {
    Not: ("NegC", 1),
    And: ("AndC", 2),
    Or: ("OrC", 2),
    Implies: ("ImpC", 2),
    Iff: ("IffC", 2),
    Would: ("CondC", 2),
}

#: Definitions the goal has to unfold before a proof method can see through it.
_DEFS = ("nested_def", "NegC_def", "AndC_def", "OrC_def", "ImpC_def", "IffC_def",
         "CondC_def")

#: Proof methods tried in order, as a ``by (… | …)`` battery. ``smt (verit)``
#: comes FIRST, not as a fallback: the ``|`` combinator has no per-method timeout,
#: and ``blast`` does not terminate on agglomeration
#: ``(A □→ B) ∧ (A □→ C) → (A □→ (B ∧ C))`` — the validity whose proof actually
#: uses the nesting premise — so a blast-first battery hangs before ever reaching
#: verit (measured: blast-first 97s and fails; verit-first closes it in ~9s, and
#: is no slower on the easy goals).
DEFAULT_METHODS: Tuple[str, ...] = ("smt (verit)", "blast", "force", "metis")

_PREAMBLE = r'''typedecl w  \<comment> \<open>worlds\<close>
type_synonym tau = "w \<Rightarrow> bool"
type_synonym sph = "w \<Rightarrow> (w \<Rightarrow> bool) \<Rightarrow> bool"

consts Sel :: sph  \<comment> \<open>Sel x S: S is a sphere around x (innermost = closest)\<close>

definition nested :: "sph \<Rightarrow> bool" where
  "nested Sp \<equiv> \<forall>x S T. Sp x S \<longrightarrow> Sp x T \<longrightarrow> (\<forall>u. S u \<longrightarrow> T u) \<or> (\<forall>u. T u \<longrightarrow> S u)"

definition NegC :: "tau \<Rightarrow> tau" where "NegC f \<equiv> \<lambda>x. \<not> f x"
definition AndC :: "tau \<Rightarrow> tau \<Rightarrow> tau" where "AndC f g \<equiv> \<lambda>x. f x \<and> g x"
definition OrC  :: "tau \<Rightarrow> tau \<Rightarrow> tau" where "OrC f g \<equiv> \<lambda>x. f x \<or> g x"
definition ImpC :: "tau \<Rightarrow> tau \<Rightarrow> tau" where "ImpC f g \<equiv> \<lambda>x. f x \<longrightarrow> g x"
definition IffC :: "tau \<Rightarrow> tau \<Rightarrow> tau" where "IffC f g \<equiv> \<lambda>x. f x = g x"

text \<open>The Lewis sphere condition: either the smallest antecedent-permitting sphere
has the consequent throughout its antecedent-worlds, or no sphere holds an
antecedent-world at all (the vacuous case).\<close>

definition CondC :: "tau \<Rightarrow> tau \<Rightarrow> tau" where
  "CondC f g \<equiv> \<lambda>x.
     (\<exists>S. Sel x S \<and> (\<exists>u. S u \<and> f u) \<and> (\<forall>u. S u \<longrightarrow> f u \<longrightarrow> g u))
     \<or> (\<forall>S. Sel x S \<longrightarrow> (\<forall>u. S u \<longrightarrow> \<not> f u))"
'''


def _atom_is_propositional(node: Atom) -> bool:
    """True unless an argument carries a :class:`Variable` (⇒ genuinely first-order)."""
    return not any(isinstance(n, Variable) for a in node.args for n in a.walk())


def to_isabelle_conditional(formula: Node,
                            atoms: Optional[AtomConsts] = None) -> str:
    r"""Encode a propositional/counterfactual formula as a shallow ``tau`` term.

    ``□→`` becomes ``CondC``; ``◇→`` desugars to ``NegC (CondC a (NegC b))`` and
    ``Xor`` to ``NegC (IffC …)``, exactly as the evaluator derives them. Each
    distinct ground atom becomes an uninterpreted ``w ⇒ bool`` constant, collected
    into ``atoms``.

    Args:
        formula: the AST node to encode.
        atoms: the constant resolver to accumulate into; a fresh one is used when
            omitted (pass your own to emit the matching ``consts`` declarations).

    Raises:
        NotImplementedError: on a quantifier, a first-order atom, or a modal
            operator. ``□``/``◇`` range over an accessibility relation and have no
            reading in the sphere semantics — the same boundary
            :func:`~unicode_fol_kit.semantics.conditional.cf_satisfies` enforces —
            so they are rejected rather than silently reinterpreted.
    """
    atoms = AtomConsts() if atoms is None else atoms
    return _encode(formula, atoms)


def _encode(formula: Node, atoms: AtomConsts) -> str:
    """Recursive worker for :func:`to_isabelle_conditional`."""
    if isinstance(formula, Atom):
        if not _atom_is_propositional(formula):
            raise NotImplementedError(
                "to_isabelle_conditional: atom with a free variable is first-order; "
                "the sphere embedding is propositional.")
        return atoms.name(formula.to_unicode_str())
    if isinstance(formula, (Quantifier, Variable)):
        raise NotImplementedError(
            "to_isabelle_conditional: quantifiers/variables are first-order; the "
            "sphere embedding is propositional.")
    if isinstance(formula, Xor):
        return (f"(NegC (IffC {_encode(formula.left, atoms)} "
                f"{_encode(formula.right, atoms)}))")
    if isinstance(formula, Might):
        # ◇→ is the dual ¬(A □→ ¬B) — no constant of its own, so the emitted theory
        # cannot drift from the evaluator's derivation of it.
        return (f"(NegC (CondC {_encode(formula.left, atoms)} "
                f"(NegC {_encode(formula.right, atoms)})))")
    spec = _CONNECTIVES.get(type(formula))
    if spec is None:
        raise NotImplementedError(
            f"to_isabelle_conditional: unsupported node type "
            f"{type(formula).__name__}. The sphere semantics reads a similarity "
            "ordering, not an accessibility relation, so the modal operators belong "
            "to hol.isabelle_modal instead.")
    name, arity = spec
    if arity == 1:
        return f"({name} {_encode(formula.formula, atoms)})"
    return (f"({name} {_encode(formula.left, atoms)} "
            f"{_encode(formula.right, atoms)})")


def battery_proof(methods: Sequence[str] = DEFAULT_METHODS) -> str:
    """A ``unfolding …`` + ``by (m1 | m2 | …)`` proof over the shallow definitions."""
    if not methods:
        raise ValueError("battery_proof: need at least one proof method.")
    alts = " | ".join(methods)
    return f"  unfolding {' '.join(_DEFS)}\n  by ({alts})"


def nitpick_proof(card: str = "1-3", timeout: int = 60) -> str:
    """A ``nitpick[expect = genuine]`` refutation attempt over the world type ``w``."""
    return (f"  nitpick[card w = {card}, timeout = {int(timeout)}, "
            f"expect = genuine]\n  oops")


def isabelle_conditional_theory(formula: Node, *,
                                theory_name: str = "CondDecide",
                                proof: Optional[str] = None,
                                lemma_name: str = "goal") -> str:
    r"""Emit a self-contained theory asserting ``formula``'s counterfactual validity.

    The goal is ``nested Sel ⟹ ∀x. φ x`` — validity over every **nested** sphere
    system, which is the class Lewis's semantics (and the toolkit's
    :class:`~unicode_fol_kit.semantics.conditional.CounterfactualModel` contract)
    intends. Nesting is a premise rather than an axiom so that nitpick can build
    ``Sel`` itself and certify a counter-model as genuine.

    Args:
        formula: the AST node to decide.
        theory_name: the Isabelle theory identifier.
        proof: the proof text under the lemma; defaults to :func:`battery_proof`.
            Pass :func:`nitpick_proof` to emit the refutation theory instead.
        lemma_name: the lemma identifier.

    Raises:
        ValueError: on an illegal theory name.
        NotImplementedError: propagated from :func:`to_isabelle_conditional`.
    """
    if not theory_name_ok(theory_name):
        raise ValueError(f"illegal theory name {theory_name!r}.")
    atoms = AtomConsts()
    term = to_isabelle_conditional(formula, atoms)
    body = [f"theory {theory_name}", "  imports Main", "begin", "", _PREAMBLE]
    decls = atoms.decls(_TAU)
    if decls:
        body.append("\n".join(decls))
        body.append("")
    body.append(
        f'lemma {lemma_name}: "nested Sel \\<Longrightarrow> \\<forall>x. ({term}) x"')
    body.append(proof if proof is not None else battery_proof())
    body.append("")
    body.append("end")
    return "\n".join(body) + "\n"
