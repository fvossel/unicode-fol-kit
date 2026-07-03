r"""Deep + maximal-shallow + minimal-shallow embeddings of **relevant logic B**
(simplified Routley–Meyer semantics), with machine-checked faithfulness proofs.

An interpretation is ``\<langle>W, N, *, R, V\<rangle>``: worlds ``W``, a set of *normal*
worlds ``N``, the Routley star ``*`` (involutive, interpreting ``\<not>``), a ternary
relation ``R`` sourced only at non-normal worlds (interpreting ``\<rightarrow>`` there), and a
valuation ``V`` — the simplified Priest–Sylvan semantics of
:mod:`unicode_fol_kit.semantics.relevant`. Truth: ``\<not>A`` at ``x`` is ``A`` false at
``x*``; ``A \<rightarrow> B`` at a *normal* world is universal (``\<forall>y\<in>W. y \<Turnstile> A \<longrightarrow> y \<Turnstile> B``), at a
non-normal world via ``R``. Validity is truth at every *normal* world of every
interpretation whose star is involutive and whose ``R`` is sourced at non-normal
worlds — sound and complete for **B**. ``\<leftrightarrow>`` desugars to ``(A \<rightarrow> B) \<and> (B \<rightarrow> A)``.
"""

from typing import Optional

from unicode_fol_kit.fol.nodes import Node, Atom, Not, And, Or, Implies, Iff, Variable
from ._common import AtomConsts, wrap_theory, formula_section

# --------------------------------------------------------------------------- #
# Verified theory body (checked verbatim by the Isabelle-gated tests).
# --------------------------------------------------------------------------- #

_REL_BODY = r'''typedecl w  \<comment> \<open>worlds\<close>
typedecl s  \<comment> \<open>signature: propositional symbols (shared by all three embeddings)\<close>
type_synonym wset = "w \<Rightarrow> bool"
type_synonym nrm  = "w \<Rightarrow> bool"          \<comment> \<open>the normal worlds N\<close>
type_synonym star = "w \<Rightarrow> w"             \<comment> \<open>the Routley star (interprets negation)\<close>
type_synonym tern = "w \<Rightarrow> w \<Rightarrow> w \<Rightarrow> bool" \<comment> \<open>the ternary relation R (interprets \<rightarrow>)\<close>
type_synonym val  = "s \<Rightarrow> w \<Rightarrow> bool"

definition involutive :: "star \<Rightarrow> bool" where "involutive st \<equiv> \<forall>x. st (st x) = x"
definition rsource :: "nrm \<Rightarrow> tern \<Rightarrow> bool" where
  "rsource N R \<equiv> \<forall>x y z. R x y z \<longrightarrow> \<not> N x"   \<comment> \<open>R sourced only at non-normal worlds\<close>

section \<open>Deep embedding: object syntax as a datatype + recursive truth\<close>

datatype rpl =
    Atm s | TopD | BotD
  | NegD rpl | AndD rpl rpl | OrD rpl rpl | ImpD rpl rpl

primrec truthD :: "wset \<Rightarrow> nrm \<Rightarrow> star \<Rightarrow> tern \<Rightarrow> val \<Rightarrow> w \<Rightarrow> rpl \<Rightarrow> bool" where
  "truthD W N st R V x (Atm p)    = V p x"
| "truthD W N st R V x TopD       = True"
| "truthD W N st R V x BotD       = False"
| "truthD W N st R V x (NegD f)   = (\<not> truthD W N st R V (st x) f)"
| "truthD W N st R V x (AndD f g) = (truthD W N st R V x f \<and> truthD W N st R V x g)"
| "truthD W N st R V x (OrD f g)  = (truthD W N st R V x f \<or> truthD W N st R V x g)"
| "truthD W N st R V x (ImpD f g) =
     ((N x \<longrightarrow> (\<forall>y. W y \<longrightarrow> truthD W N st R V y f \<longrightarrow> truthD W N st R V y g))
    \<and> (\<not> N x \<longrightarrow> (\<forall>y z. R x y z \<longrightarrow> truthD W N st R V y f \<longrightarrow> truthD W N st R V z g)))"

definition validD :: "rpl \<Rightarrow> bool" where
  "validD f \<equiv> \<forall>W N st R V. involutive st \<longrightarrow> rsource N R \<longrightarrow>
                (\<forall>x. W x \<longrightarrow> N x \<longrightarrow> truthD W N st R V x f)"

section \<open>Maximal (heavyweight) shallow embedding: every parameter explicit\<close>

type_synonym sigma = "wset \<Rightarrow> nrm \<Rightarrow> star \<Rightarrow> tern \<Rightarrow> val \<Rightarrow> w \<Rightarrow> bool"
definition AtmS :: "s \<Rightarrow> sigma" where "AtmS p \<equiv> \<lambda>W N st R V x. V p x"
definition TopS :: "sigma" where "TopS \<equiv> \<lambda>W N st R V x. True"
definition BotS :: "sigma" where "BotS \<equiv> \<lambda>W N st R V x. False"
definition NegS :: "sigma \<Rightarrow> sigma" where
  "NegS f \<equiv> \<lambda>W N st R V x. \<not> f W N st R V (st x)"
definition AndS :: "sigma \<Rightarrow> sigma \<Rightarrow> sigma" where
  "AndS f g \<equiv> \<lambda>W N st R V x. f W N st R V x \<and> g W N st R V x"
definition OrS :: "sigma \<Rightarrow> sigma \<Rightarrow> sigma" where
  "OrS f g \<equiv> \<lambda>W N st R V x. f W N st R V x \<or> g W N st R V x"
definition ImpS :: "sigma \<Rightarrow> sigma \<Rightarrow> sigma" where
  "ImpS f g \<equiv> \<lambda>W N st R V x.
     (N x \<longrightarrow> (\<forall>y. W y \<longrightarrow> f W N st R V y \<longrightarrow> g W N st R V y))
   \<and> (\<not> N x \<longrightarrow> (\<forall>y z. R x y z \<longrightarrow> f W N st R V y \<longrightarrow> g W N st R V z))"
definition validS :: "sigma \<Rightarrow> bool" where
  "validS f \<equiv> \<forall>W N st R V. involutive st \<longrightarrow> rsource N R \<longrightarrow>
                (\<forall>x. W x \<longrightarrow> N x \<longrightarrow> f W N st R V x)"

section \<open>Minimal (lightweight) shallow embedding: N, *, R, V fixed as consts\<close>

consts Nrm :: "nrm"
consts Star :: "star"
consts Rrel :: "tern"
consts Vval :: "val"
type_synonym tau = "w \<Rightarrow> bool"
definition AtmM :: "s \<Rightarrow> tau" where "AtmM p \<equiv> \<lambda>x. Vval p x"
definition TopM :: "tau" where "TopM \<equiv> \<lambda>x. True"
definition BotM :: "tau" where "BotM \<equiv> \<lambda>x. False"
definition NegM :: "tau \<Rightarrow> tau" where "NegM f \<equiv> \<lambda>x. \<not> f (Star x)"
definition AndM :: "tau \<Rightarrow> tau \<Rightarrow> tau" where "AndM f g \<equiv> \<lambda>x. f x \<and> g x"
definition OrM :: "tau \<Rightarrow> tau \<Rightarrow> tau" where "OrM f g \<equiv> \<lambda>x. f x \<or> g x"
definition ImpM :: "tau \<Rightarrow> tau \<Rightarrow> tau" where
  "ImpM f g \<equiv> \<lambda>x.
     (Nrm x \<longrightarrow> (\<forall>y. f y \<longrightarrow> g y))
   \<and> (\<not> Nrm x \<longrightarrow> (\<forall>y z. Rrel x y z \<longrightarrow> f y \<longrightarrow> g z))"
definition validM :: "tau \<Rightarrow> bool" where "validM f \<equiv> \<forall>x. Nrm x \<longrightarrow> f x"

section \<open>Mappings between the embeddings\<close>

primrec dpToMax :: "rpl \<Rightarrow> sigma" where
  "dpToMax (Atm p)    = AtmS p"
| "dpToMax TopD       = TopS"
| "dpToMax BotD       = BotS"
| "dpToMax (NegD f)   = NegS (dpToMax f)"
| "dpToMax (AndD f g) = AndS (dpToMax f) (dpToMax g)"
| "dpToMax (OrD f g)  = OrS (dpToMax f) (dpToMax g)"
| "dpToMax (ImpD f g) = ImpS (dpToMax f) (dpToMax g)"

primrec dpToMin :: "rpl \<Rightarrow> tau" where
  "dpToMin (Atm p)    = AtmM p"
| "dpToMin TopD       = TopM"
| "dpToMin BotD       = BotM"
| "dpToMin (NegD f)   = NegM (dpToMin f)"
| "dpToMin (AndD f g) = AndM (dpToMin f) (dpToMin g)"
| "dpToMin (OrD f g)  = OrM (dpToMin f) (dpToMin g)"
| "dpToMin (ImpD f g) = ImpM (dpToMin f) (dpToMin g)"

section \<open>Faithfulness (machine-checked by Isabelle's kernel)\<close>

lemmas maxdefs = AtmS_def TopS_def BotS_def NegS_def AndS_def OrS_def ImpS_def
lemmas mindefs = AtmM_def TopM_def BotM_def NegM_def AndM_def OrM_def ImpM_def

text \<open>Deep truth coincides pointwise with maximal-shallow truth.\<close>
theorem faithful1a: "truthD W N st R V x f = dpToMax f W N st R V x"
  by (induct f arbitrary: x) (simp_all add: maxdefs)

text \<open>Hence deep validity coincides with maximal-shallow validity.\<close>
theorem faithful1b: "validD f = validS (dpToMax f)"
  by (simp add: validD_def validS_def faithful1a)

text \<open>Deep truth in the fixed model coincides with minimal-shallow truth.\<close>
theorem faithful2: "truthD (\<lambda>_. True) Nrm Star Rrel Vval x f = dpToMin f x"
  by (induct f arbitrary: x) (simp_all add: mindefs)

text \<open>Maximal- and minimal-shallow truth coincide in that fixed model.\<close>
theorem faithful3: "dpToMax f (\<lambda>_. True) Nrm Star Rrel Vval x = dpToMin f x"
  by (induct f arbitrary: x) (simp_all add: maxdefs mindefs)

text \<open>Soundness of the minimal embedding for deep validity (under the frame
      assumptions the minimal embedding fixes as consts: involutive star,
      R sourced at non-normal worlds).  Validity is truth at NORMAL worlds.\<close>
theorem sound_min:
  "involutive Star \<Longrightarrow> rsource Nrm Rrel \<Longrightarrow> validD f \<Longrightarrow> validM (dpToMin f)"
proof -
  assume inv: "involutive Star" and rs: "rsource Nrm Rrel" and *: "validD f"
  have "Nrm x \<longrightarrow> truthD (\<lambda>_. True) Nrm Star Rrel Vval x f" for x
    using * inv rs by (simp add: validD_def)
  then show "validM (dpToMin f)"
    by (simp add: validM_def faithful2)
qed'''


# --------------------------------------------------------------------------- #
# Encoder + public entry point.
# --------------------------------------------------------------------------- #

_ARROW = {And: "AndD", Or: "OrD", Implies: "ImpD"}


def rel_to_deep(formula: Node, atoms: AtomConsts) -> str:
    r"""Encode a **propositional relevant** formula as a deep ``rpl`` term.

    Handles atoms, ``\<not> \<and> \<or> \<rightarrow>`` and ``\<leftrightarrow>`` (which desugars to
    ``(A \<rightarrow> B) \<and> (B \<rightarrow> A)``, matching :mod:`unicode_fol_kit.semantics.relevant`).
    Raises :class:`NotImplementedError` on any other node (modalities, ``Xor``,
    quantifiers, free variables).
    """
    if isinstance(formula, Atom):
        if any(isinstance(n, Variable) for a in formula.args for n in a.walk()):
            raise NotImplementedError(
                "rel_to_deep: atom with a free variable is first-order; the deep "
                "embedding is propositional.")
        return f"(Atm {atoms.name(formula.to_unicode_str())})"
    if isinstance(formula, Not):
        return f"(NegD {rel_to_deep(formula.formula, atoms)})"
    if isinstance(formula, Iff):
        a = rel_to_deep(formula.left, atoms)
        b = rel_to_deep(formula.right, atoms)
        return f"(AndD (ImpD {a} {b}) (ImpD {b} {a}))"
    if type(formula) in _ARROW:
        ctor = _ARROW[type(formula)]
        a = rel_to_deep(formula.left, atoms)
        b = rel_to_deep(formula.right, atoms)
        return f"({ctor} {a} {b})"
    raise NotImplementedError(
        f"rel_to_deep: unsupported node type {type(formula).__name__} "
        "(propositional relevant fragment: atoms, ¬ ∧ ∨ → ↔).")


def relevant_faithfulness_theory(
    theory_name: str = "RelFaithfulness",
    formula: Optional[Node] = None,
) -> str:
    r"""Emit the self-contained relevant-B deep/maximal/minimal + faithfulness theory.

    When ``formula`` is given, its deep encoding is appended as
    ``definition example :: rpl``. With a local Isabelle/HOL the theory is verified
    end to end by :func:`unicode_fol_kit.hol.isabelle_runner.check_theory`.
    """
    extra = ""
    if formula is not None:
        atoms = AtomConsts()
        term = rel_to_deep(formula, atoms)
        extra = formula_section(term, atoms, "rpl")
    return wrap_theory(theory_name, _REL_BODY, extra)
