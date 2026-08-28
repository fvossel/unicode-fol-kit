r"""Gödel's ontological argument, as the third-order modal machinery's proving ground.

Gödel's argument for the existence of a God-like being is the standard worked
example of THIRD-ORDER MODAL logic, because it cannot be stated in anything
less: its axioms are about a predicate ``Positive`` whose argument is a
PROPERTY, inside modal operators. That makes it the sharpest available test of
:mod:`unicode_fol_kit.fol` third-order modal syntax and
:mod:`unicode_fol_kit.hol.ho_modal`'s embedding — the axioms are written here in
the kit's own Unicode syntax, exported by the kit's own emitter, and discharged
by a real prover; nothing about it is special-cased.

**Two variants, one conjunct apart.** ::

    D2 (Scott)     Ess(P, x) ↔ P(x) ∧ ∀Q (Q(x) → □∀y (P(y) → Q(y)))
    D2 (Gödel)     Ess(P, x) ↔        ∀Q (Q(x) → □∀y (P(y) → Q(y)))

Everything else is identical. Scott's reading is the one that is usually
presented; Gödel's own notes lack the ``P(x)`` conjunct, and that omission is
fatal — first noticed mechanically by Benzmüller and Woltzenlogel Paleo (2013).
Without it, the EMPTY property is vacuously an essence of everything (there is
no ``y`` with ``⊥(y)``, so ``□∀y (⊥(y) → Q(y))`` holds outright), and necessary
existence then demands that the empty property be instantiated in every
accessible world. Both halves of that are proved here, from the axioms, by the
prover — not asserted.

What the two theories establish, each as a lemma the prover discharges:

*Scott's version* — ``T1`` every positive property is possibly instantiated;
``C`` a God-like being is possible; ``T2`` God-likeness is an essence of any
God-like being; ``T3`` necessarily, a God-like being exists; ``MC`` **modal
collapse**, ``φ → □φ`` for every proposition, which is the argument's
best-known and least comfortable consequence. Plus ``consistency``: Nitpick
finds a genuine model of the axioms, so the theory proves those things because
they follow, not because it proves everything.

*Gödel's original* — ``emptyEssence`` the empty property is an essence of every
individual, and ``inconsistent``: ``False``. The control that makes that
meaningful lives on the other side: in Scott's theory
``essenceImpliesInstance`` (``Ess(P, x) → P(x)``) is provable, so there the
empty property is an essence of NOTHING and the step is blocked by exactly the
conjunct Gödel omitted.

**The proofs are data, not search.** The Isar proof scripts below are written
out by hand and shipped as text; the kit emits the theory and
:func:`check_variant` hands it to Isabelle. Nothing here calls a prover to
*find* a proof, and nothing claims a result the caller has not run. Without a
local Isabelle the module still gives you the axioms as kit formulas and the
theory as text.

**Frame.** S5, the setting the argument is standardly stated in; ``T3`` needs
symmetry, and the inconsistency needs only reflexivity.
"""

from typing import Dict, List, Optional

from ..fol.msflparser import MSFLParser
from ..fol.nodes import Node
from .ho_modal import HoAxiom, HoGoal, isabelle_ho_modal_theory

_PARSER = MSFLParser(third_order=True, modal=True)


def _f(text: str) -> Node:
    """Parse one axiom in the kit's third-order modal syntax."""
    return _PARSER.parse(text)


#: The axioms shared by both variants, in the kit's own Unicode syntax. ``Pos``
#: is Gödel's ``P`` (positiveness), ``G`` is God-likeness, ``Ess(P, x)`` is
#: "``P`` is an essence of ``x``", ``NE`` is necessary existence. ``P`` is
#: renamed because a predicate OF properties and a property variable both
#: spelled ``P`` would be needlessly hard to read, not because the kit needs it.
_SHARED = {
    "A1": "∀P (Pos(λx. ¬P(x)) ↔ ¬Pos(P))",
    "A2": "∀P ∀Q (Pos(P) ∧ □∀x (P(x) → Q(x)) → Pos(Q))",
    "D1": "∀x (G(x) ↔ ∀P (Pos(P) → P(x)))",
    "A3": "Pos(G)",
    "A4": "∀P (Pos(P) → □Pos(P))",
    "D3": "∀x (NE(x) ↔ ∀P (Ess(P, x) → □∃y P(y)))",
    "A5": "Pos(NE)",
}

#: The one axiom the two variants disagree about — see the module docstring.
_D2 = {
    "scott": "∀P ∀x (Ess(P, x) ↔ P(x) ∧ ∀Q (Q(x) → □∀y (P(y) → Q(y))))",
    "goedel": "∀P ∀x (Ess(P, x) ↔ ∀Q (Q(x) → □∀y (P(y) → Q(y))))",
}

_COMMENTS = {
    "A1": "A1  a property is positive iff its complement is not",
    "A2": "A2  positiveness is closed under necessary entailment",
    "D1": "D1  God-like: having every positive property",
    "A3": "A3  being God-like is positive",
    "A4": "A4  positiveness is necessary",
    "D2": "D2  essence",
    "D3": "D3  necessary existence: every essence is necessarily instantiated",
    "A5": "A5  necessary existence is positive",
}

VARIANTS = ("scott", "goedel")

#: The conclusions, in the kit's syntax. Stated separately from the axioms
#: because they are what the prover has to EARN.
_CONCLUSIONS = {
    "T1": "∀P (Pos(P) → ◇∃x P(x))",
    "C": "◇∃x G(x)",
    "T2": "∀x (G(x) → Ess(G, x))",
    "T3": "□∃x G(x)",
    "MC": "∀Q (Q → □Q)",
}


def _order(variant: str) -> List[str]:
    """Axiom names in presentation order (Gödel's own numbering interleaves definitions)."""
    return ["A1", "A2", "D1", "A3", "A4", "D2", "D3", "A5"]


def axiom_texts(variant: str = "scott") -> Dict[str, str]:
    """Return ``{name: source text}`` for ``variant``'s axioms, in the kit's syntax.

    ``variant`` is ``"scott"`` (the consistent reading) or ``"goedel"`` (Gödel's
    own, which is inconsistent). The two differ in ``D2`` and nowhere else —
    which :func:`variant_difference` states outright.
    """
    if variant not in VARIANTS:
        raise ValueError(f"goedel: unknown variant {variant!r}; expected one of {VARIANTS}.")
    texts = dict(_SHARED)
    texts["D2"] = _D2[variant]
    return {name: texts[name] for name in _order(variant)}


def axioms(variant: str = "scott") -> Dict[str, Node]:
    """Return ``{name: formula}`` for ``variant``'s axioms, parsed."""
    return {name: _f(text) for name, text in axiom_texts(variant).items()}


def conclusions() -> Dict[str, Node]:
    """Return ``{name: formula}`` for the argument's conclusions, parsed.

    ``T1``, ``C``, ``T2``, ``T3`` are the argument's own steps; ``MC`` is modal
    collapse, which is not a step of the argument but a consequence of it.
    """
    return {name: _f(text) for name, text in _CONCLUSIONS.items()}


def variant_difference() -> str:
    """Return a one-line statement of what separates the two variants."""
    return (f"D2 scott : {_D2['scott']}\n"
            f"D2 goedel: {_D2['goedel']}\n"
            f"(the missing 'P(x)' conjunct is what makes the empty property an "
            f"essence of everything, and the axiom set inconsistent)")


# --------------------------------------------------------------------------
# Isar proof scripts — written by hand, shipped as data
# --------------------------------------------------------------------------
#
# Each is a complete Isabelle proof for the goal directly above it in the
# emitted theory. They are structured rather than one-line automation calls on
# purpose: the one-liners either fail or search unboundedly at this order, and a
# proof that takes ten minutes to not finish is not a check. Every step names
# the facts it uses, so what carries a lemma is readable off the script.

_T1_PROOF = r"""proof -
  { fix v :: world and Q :: "i \<Rightarrow> sigma"
    assume pos: "Pos Q v"
    have "\<exists>u. R v u \<and> (\<exists>x. Q x u)"
    proof (rule ccontr)
      assume "\<not> (\<exists>u. R v u \<and> (\<exists>x. Q x u))"
      hence empty: "\<forall>u. R v u \<longrightarrow> (\<forall>x. Q x u \<longrightarrow> \<not> Q x u)" by blast
      have "Pos (\<lambda>x u. \<not> Q x u) v" using A2 pos empty by blast
      moreover have "Pos (\<lambda>x u. \<not> Q x u) v = (\<not> Pos Q v)" using A1 by blast
      ultimately show False using pos by blast
    qed
  }
  thus ?thesis by blast
qed"""

_C_PROOF = "using T1 A3 by blast"

_T2_PROOF = r"""proof -
  { fix v :: world and x :: i
    assume gx: "G x v"
    have allpos: "\<forall>P. Pos P v \<longrightarrow> P x v" using gx D1 by blast
    { fix Q :: "i \<Rightarrow> sigma"
      assume qx: "Q x v"
      have posq: "Pos Q v"
      proof (rule ccontr)
        assume "\<not> Pos Q v"
        hence "Pos (\<lambda>y u. \<not> Q y u) v" using A1 by blast
        hence "\<not> Q x v" using allpos by blast
        thus False using qx by blast
      qed
      hence "\<forall>u. R v u \<longrightarrow> Pos Q u" using A4 by blast
      hence "\<forall>u. R v u \<longrightarrow> (\<forall>y. G y u \<longrightarrow> Q y u)" using D1 by blast
    }
    hence "Ess G x v" using gx D2 by blast
  }
  thus ?thesis by blast
qed"""

_T3_PROOF = r"""proof -
  have step: "\<forall>v x. G x v \<longrightarrow> (\<forall>u. R v u \<longrightarrow> (\<exists>y. G y u))"
  proof -
    { fix v :: world and x :: i
      assume gx: "G x v"
      hence ne: "NE x v" using A5 D1 by blast
      have "Ess G x v" using gx T2 by blast
      hence "\<forall>u. R v u \<longrightarrow> (\<exists>y. G y u)" using ne D3 by blast
    }
    thus ?thesis by blast
  qed
  { fix w :: world
    obtain u x where ru: "R w u" and gx: "G x u" using C by blast
    { fix z assume rz: "R w z"
      have "R u z" using ru rz R_sym R_trans by blast
      hence "\<exists>y. G y z" using gx step by blast
    }
    hence "\<forall>z. R w z \<longrightarrow> (\<exists>y. G y z)" by blast
  }
  thus ?thesis by blast
qed"""

_MC_PROOF = r"""proof -
  { fix v :: world and Phi :: sigma
    assume phi: "Phi v"
    obtain x where gx: "G x v" using T3 R_refl by blast
    have allpos: "\<forall>P. Pos P v \<longrightarrow> P x v" using gx D1 by blast
    have "Pos (\<lambda>y::i. Phi) v"
    proof (rule ccontr)
      assume "\<not> Pos (\<lambda>y::i. Phi) v"
      hence "Pos (\<lambda>y::i. \<lambda>z. \<not> Phi z) v" using A1 by blast
      hence "\<not> Phi v" using allpos by blast
      thus False using phi by blast
    qed
    hence "\<forall>u. R v u \<longrightarrow> Pos (\<lambda>y::i. Phi) u" using A4 by blast
    hence "\<forall>u. R v u \<longrightarrow> Phi u" using T3 D1 by blast
  }
  thus ?thesis by blast
qed"""

_INCONSISTENT_PROOF = r"""proof -
  have ess: "\<forall>v x. Ess (\<lambda>y::i. \<lambda>z. False) x v" using D2 by blast
  \<comment> \<open>C holds at EVERY world, so any world will do to start from;
     a typedecl type is inhabited, which is all `undefined` is used for\<close>
  obtain u x where ru: "R (undefined::world) u" and gx: "G x u" using C by blast
  have ne: "NE x u" using gx A5 D1 by blast
  have "\<forall>z. R u z \<longrightarrow> (\<exists>y::i. False)" using ne ess D3 by blast
  moreover have "R u u" using R_refl by blast
  ultimately show False by blast
qed"""

#: The empty property, as an Isabelle term: no individual has it at any world.
_EMPTY = r"(\<lambda>y::i. \<lambda>z. False)"


def _scott_goals() -> List[HoGoal]:
    """The four steps of the argument, plus modal collapse, the block, and consistency."""
    conc = conclusions()
    return [
        HoGoal("T1", conc["T1"], _T1_PROOF,
               "T1  every positive property is possibly instantiated"),
        HoGoal("C", conc["C"], _C_PROOF,
               "C   a God-like being is possible"),
        HoGoal("T2", conc["T2"], _T2_PROOF,
               "T2  God-likeness is an essence of every God-like being"),
        HoGoal("T3", conc["T3"], _T3_PROOF,
               "T3  necessarily, a God-like being exists"),
        HoGoal("MC", conc["MC"], _MC_PROOF,
               "MC  modal collapse: everything true is necessarily true"),
        HoGoal("essenceImpliesInstance", proof="using D2 by blast",
               statement=r"\<forall>v P x. Ess P x v \<longrightarrow> P x v",
               comment="Scott's conjunct, isolated: an essence of x is a property x HAS"),
        HoGoal("emptyNotEssence", proof="using essenceImpliesInstance by blast",
               statement=rf"\<forall>v x. \<not> Ess {_EMPTY} x v",
               comment="so the empty property is an essence of nothing "
                       "-- exactly the step Goedel's D2 leaves open"),
        HoGoal("consistency", statement="True", kind="lemma",
               proof="nitpick [satisfy, user_axioms, expect = genuine]\n  oops",
               comment="Nitpick finds a genuine model: the axioms are consistent, "
                       "so the theorems above hold because they FOLLOW"),
    ]


def _goedel_goals() -> List[HoGoal]:
    """The collapse of Gödel's own reading: the empty property is an essence, hence falsity."""
    conc = conclusions()
    return [
        HoGoal("T1", conc["T1"], _T1_PROOF,
               "T1  every positive property is possibly instantiated"),
        HoGoal("C", conc["C"], _C_PROOF,
               "C   a God-like being is possible"),
        HoGoal("emptyEssence", proof="using D2 by blast",
               statement=rf"\<forall>v x. Ess {_EMPTY} x v",
               comment="without the P(x) conjunct the empty property is "
                       "vacuously an essence of EVERY individual"),
        HoGoal("inconsistent", statement="False", proof=_INCONSISTENT_PROOF,
               comment="and necessary existence then demands it be instantiated"),
    ]


def goedel_theory(variant: str = "scott", name: Optional[str] = None,
                  frame: str = "S5") -> str:
    """Emit the complete Isabelle theory for one variant of the argument.

    ``variant`` is ``"scott"`` or ``"goedel"``; ``name`` defaults to
    ``GoedelScott`` / ``GoedelOriginal``. The axioms come from
    :func:`axioms`, the embedding from
    :func:`unicode_fol_kit.hol.ho_modal.isabelle_ho_modal_theory`, and the
    proofs from this module's scripts — so the emitted text is the kit's, end to
    end, and can be read, edited or run outside it.
    """
    if variant not in VARIANTS:
        raise ValueError(f"goedel: unknown variant {variant!r}; expected one of {VARIANTS}.")
    name = name or ("GoedelScott" if variant == "scott" else "GoedelOriginal")
    formulas = axioms(variant)
    axiom_list = [HoAxiom(key, formulas[key], _COMMENTS[key]) for key in formulas]
    goals = _scott_goals() if variant == "scott" else _goedel_goals()
    return isabelle_ho_modal_theory(name, axiom_list, goals, frame=frame)


def check_variant(variant: str = "scott", frame: str = "S5",
                  timeout: int = 600):
    """Emit ``variant``'s theory and run it through the local Isabelle.

    Returns the :class:`~unicode_fol_kit.hol.isabelle_runner.BuildResult`;
    ``result.ok`` means every lemma in the theory was discharged — for
    ``"scott"`` that the argument goes through and its axioms have a model, for
    ``"goedel"`` that they prove falsity. Raises
    :class:`~unicode_fol_kit.hol.isabelle_runner.IsabelleNotAvailable` if no
    Isabelle is installed; the kit does not ship one.
    """
    from .isabelle_runner import check_theory
    name = "GoedelScott" if variant == "scott" else "GoedelOriginal"
    theory = goedel_theory(variant, name, frame=frame)
    return check_theory(theory, name, session_timeout=timeout, wall_timeout=timeout)
