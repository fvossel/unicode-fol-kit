r"""Isabelle/HOL export for the Lewis counterfactual conditionals ``□→`` / ``◇→``.

The modal exporter (:mod:`unicode_fol_kit.hol.isabelle_modal`) embeds ``□``/``◇``
over an **accessibility relation**; a counterfactual is not evaluated that way. Its
truth condition reads a **similarity ordering** — Lewis's system of spheres — so it
needs its own embedding, which is what this module emits.

The embedding is the *lightweight shallow* one: a formula becomes a predicate on
worlds (``tau = w ⇒ bool``), the sphere system is the uninterpreted constant
``Sel``, and each propositional atom is an uninterpreted ``w ⇒ bool`` constant.
Validity is ``nested Sel ⟹ <centering premise> ⟹ ∀x. φ x``.

``nested`` appears as a **premise of the goal**, never as an ``axiomatization``.
That is deliberate: nitpick cannot certify a model as *genuine* while axiomatised
constants are in play (it has no way to check the axioms are consistent) and
downgrades the verdict to ``quasi_genuine``, which would lose us the refutation
half of the decision procedure. As a premise, nitpick constructs ``Sel`` itself.
The centering premise is added the same way, for the same reason.

``CondC`` is the same truth condition as
:func:`unicode_fol_kit.semantics.conditional.cf_satisfies` and as the ``CondM``
clause of :mod:`unicode_fol_kit.hol.deepshallow.conditional`, so what Isabelle
certifies here is what the toolkit's own evaluator computes.

CENTERING — the premise denotes the Python class exactly
--------------------------------------------------------
``centering`` (``"none"`` = Lewis V, ``"weak"`` = VW and the default, ``"strong"``
= VC — the level names come from
:data:`~unicode_fol_kit.semantics.conditional.CENTERING_LEVELS`, imported rather
than duplicated) selects one extra premise. That premise denotes *exactly* the
class of models :func:`~unicode_fol_kit.semantics.conditional.cf_countermodel`
enumerates at the same level, which is what makes the two routes comparable
verdict by verdict; the argument, for a finite world set ``W`` and the family
``F(x) = {S ⊆ W : Sel x S}``:

1. SHAPE — ``nested Sel`` makes ``F(x)`` a ⊆-chain, and over a finite ``W`` a chain
   is exactly a finite strictly increasing sequence: the ``List[FrozenSet]``,
   innermost-first shape ``_sphere_chains`` emits.
2. ``∅`` IS INERT — ``CondC``'s non-vacuous disjunct needs ``∃u. S u ∧ f u``, which
   ``∅`` never supplies, and its vacuous disjunct holds of ``∅`` outright. So
   ``F(x)`` and ``F(x) \ {∅}`` agree on every ``CondC f g x``, and the Python pool
   ranging over non-empty subsets only loses nothing.
3. TRUTH CONDITION — HOL takes the ∃-form ("SOME sphere permits the antecedent and
   has the consequent throughout"); Python takes the FIRST permitting chain member.
   On a chain these coincide: the ⊆-least permitting member is contained in any
   permitting witness, so its antecedent-worlds are among that witness's. This part
   is centering-independent and is why the two routes already agreed at what is now
   called ``"none"``.
4. THE LEVELS — ``"none"``: no premise; Python additionally emits the empty chain,
   matching ``F(x) = ∅`` (equivalently ``{∅}``, by 2). ``"weak"``:
   ``weakly_centered Sel`` says some sphere of ``x`` contains ``x`` and every
   non-empty sphere of ``x`` contains ``x``; Python emits exactly the non-empty
   chains all of whose members contain ``x``, and deleting ``∅`` from any HOL
   witness by (2) lands back in that set. ``"strong"``: ``strongly_centered Sel``
   says ``{x}`` is a sphere, which with nesting makes it the ⊆-least non-empty one;
   Python pins ``chain[0] = {x}``.
5. QUANTIFIER STRUCTURE — the HOL conditions are ``∀x. …`` and the Python search
   assigns an independent chain per world, imposing the level per world.

The two routes also bound the search differently — ``cf_valid`` by ``max_worlds``,
this route by nitpick's ``card`` (default ``1-3``) — but at the centered levels the
defaults now coincide at three worlds
(:data:`~unicode_fol_kit.semantics.conditional.DEFAULT_MAX_WORLDS`), which is what
lets both routes refute the two bound-sensitive schemas (conditional excluded middle
at VC, importation at VW) rather than only this one. At ``centering="none"`` the
Python bound stays 2, its enumeration being an order of magnitude larger per world,
so a ``True`` from ``cf_valid`` there is the weaker claim of the two.
"""

from typing import Dict, List, Optional, Sequence, Tuple, Type

from ..fol.nodes import (
    Node, Atom, Not, And, Or, Xor, Implies, Iff, Would, Might,
    Variable, Quantifier,
)
from .deepshallow._common import AtomConsts, theory_name_ok
from ..semantics.conditional import CENTERING_LEVELS, check_centering  # noqa: F401

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
_BASE_DEFS = ("nested_def", "NegC_def", "AndC_def", "OrC_def", "ImpC_def",
              "IffC_def", "CondC_def")

#: The centering definition each level's premise needs unfolded, if any. The
#: unfold list is level-dependent on purpose: ``unfolding`` is CHANGED-wrapped over
#: the whole batch, so an unconditional list naming both predicates would happen to
#: work today only because ``nested_def`` always fires — an accident, not a
#: guarantee. An unfolded-but-absent premise is a silent proof-failure generator.
_CENTERING_DEFS: Dict[str, Tuple[str, ...]] = {
    "none": (),
    "weak": ("weakly_centered_def",),
    "strong": ("strongly_centered_def",),
}

#: The extra goal premise per level. ``"none"`` is Lewis's bare V: nesting only.
_CENTERING_PREMISE: Dict[str, Tuple[str, ...]] = {
    "none": (),
    "weak": ("weakly_centered Sel",),
    "strong": ("strongly_centered Sel",),
}

#: Level -> Lewis's own name for the system, recorded in the emitted theory so a
#: reader (and a structure test) can see which logic was decided.
_CENTERING_SYSTEM: Dict[str, str] = {"none": "V", "weak": "VW", "strong": "VC"}


def _defs_for(centering: str) -> Tuple[str, ...]:
    """The ``unfolding`` list for ``centering`` — nesting, the level's centering
    definition (if it has one), then the connective definitions."""
    check_centering(centering)
    return (_BASE_DEFS[0],) + _CENTERING_DEFS[centering] + _BASE_DEFS[1:]

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

text \<open>Centering. Nesting alone is Lewis's system V; VW adds weak centering, VC
strong centering. Both predicates are defined at every level and only the emitted
lemma's premise selects one -- an unused definition is inert, so the preamble stays a
single constant string.

weakly_centered is stated in two clauses: SOME sphere of x contains x, and EVERY
NON-EMPTY sphere of x contains x. The first clause must mention S x rather than merely
assert that x has some sphere, or a system whose only sphere is the empty one would
satisfy it -- and that system is exactly the vacuity that makes modus ponens for the
conditional fail. The second clause is guarded by an emptiness test because Lewis's own
sphere systems contain the empty set (it is the union of the empty family); the
unguarded form would denote a strictly smaller class of Sel with the same validities,
since the empty sphere is truth-value inert for CondC.

strongly_centered says "the singleton of x IS a sphere around x", not "the innermost
sphere is that singleton": together with the nested premise that always accompanies it,
every sphere S around x is comparable with it, hence S is empty or contains x, so the
singleton is the smallest non-empty sphere. That also makes strong centering entail weak
centering, which is why the strong goal does not carry both premises.\<close>

definition weakly_centered :: "sph \<Rightarrow> bool" where
  "weakly_centered Sp \<equiv> \<forall>x. (\<exists>S. Sp x S \<and> S x)
     \<and> (\<forall>S. Sp x S \<longrightarrow> (\<exists>u. S u) \<longrightarrow> S x)"

definition strongly_centered :: "sph \<Rightarrow> bool" where
  "strongly_centered Sp \<equiv> \<forall>x. Sp x (\<lambda>u. u = x)"

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


def battery_proof(methods: Sequence[str] = DEFAULT_METHODS, *,
                  centering: str = "weak") -> str:
    """A ``unfolding …`` + ``by (m1 | m2 | …)`` proof over the shallow definitions.

    ``centering`` must be the SAME level the goal's premise was built with (see
    :func:`isabelle_conditional_theory`): the unfold list is what lets the proof
    battery see through that premise, so a mismatch does not produce a wrong
    verdict but a failed proof, which the runner reports as UNKNOWN or INVALID.
    Keyword-only, so ``battery_proof(methods)`` positional callers keep working.

    Raises:
        ValueError: on an empty method battery or an unknown ``centering`` level.
    """
    if not methods:
        raise ValueError("battery_proof: need at least one proof method.")
    alts = " | ".join(methods)
    return f"  unfolding {' '.join(_defs_for(centering))}\n  by ({alts})"


def nitpick_proof(card: str = "1-3", timeout: int = 60) -> str:
    """A ``nitpick[expect = genuine]`` refutation attempt over the world type ``w``."""
    return (f"  nitpick[card w = {card}, timeout = {int(timeout)}, "
            f"expect = genuine]\n  oops")


def isabelle_conditional_theory(formula: Node, *,
                                theory_name: str = "CondDecide",
                                proof: Optional[str] = None,
                                lemma_name: str = "goal",
                                centering: str = "weak") -> str:
    r"""Emit a self-contained theory asserting ``formula``'s counterfactual validity.

    The goal is ``nested Sel ⟹ <centering premise> ⟹ ∀x. φ x`` — validity over
    every nested sphere system meeting the requested centering level. Both premises
    are premises rather than axioms so that nitpick can build ``Sel`` itself and
    certify a counter-model as genuine.

    Args:
        formula: the AST node to decide.
        theory_name: the Isabelle theory identifier.
        proof: the proof text under the lemma; defaults to
            ``battery_proof(centering=centering)``. Pass :func:`nitpick_proof` to
            emit the refutation theory instead. If you pass your own
            :func:`battery_proof` text, build it at THIS level — the unfold list
            has to match the premise.
        lemma_name: the lemma identifier.
        centering: ``"none"`` (V) / ``"weak"`` (VW, default) / ``"strong"`` (VC).
            The default matches
            :func:`~unicode_fol_kit.semantics.conditional.cf_valid`'s, so the
            Isabelle route and the internal evaluator decide the same question
            unless told otherwise. See the module docstring for why the emitted
            premise denotes exactly the class the Python search enumerates.

    Raises:
        ValueError: on an illegal theory name or an unknown ``centering`` level.
        NotImplementedError: propagated from :func:`to_isabelle_conditional`.
    """
    check_centering(centering)
    if not theory_name_ok(theory_name):
        raise ValueError(f"illegal theory name {theory_name!r}.")
    atoms = AtomConsts()
    term = to_isabelle_conditional(formula, atoms)
    body = [f"theory {theory_name}", "  imports Main", "begin", "", _PREAMBLE]
    decls = atoms.decls(_TAU)
    if decls:
        body.append("\n".join(decls))
        body.append("")
    # Provenance: the emitted theory records which sphere class it decided. At
    # centering="none" the lemma line is byte-identical to a pre-centering one, so
    # without this the level would be unrecoverable from the artefact.
    body.append(f"text \\<open>centering = {centering} "
                f"(Lewis {_CENTERING_SYSTEM[centering]})\\<close>")
    body.append("")
    arrow = " \\<Longrightarrow> "
    prems = ("nested Sel",) + _CENTERING_PREMISE[centering]
    body.append(
        f'lemma {lemma_name}: "{arrow.join(prems)}{arrow}\\<forall>x. ({term}) x"')
    body.append(proof if proof is not None
                else battery_proof(centering=centering))
    body.append("")
    body.append("end")
    return "\n".join(body) + "\n"
