r"""Deep + maximal-shallow + minimal-shallow embeddings of **quantified** modal logic
(QML), Tier 2 — scoped to the base frame K, the CONSTANT domain regime only, and
the alethic ``□``/``◇`` modalities, with machine-checked faithfulness proofs.

This is the binder-carrying sibling of :mod:`unicode_logic_kit.hol.deepshallow.modal`:
where Tier 1 embeds *propositional* logics (no quantifiers, so induction over the
syntax datatype is the whole story), this module embeds a genuinely *quantified*
one. Object variables are represented **de Bruijn-indexed** (``obj = BVar nat |
FVar s``, ``FVar`` naming a rigid object CONSTANT) rather than by name, which is
what lets ``truthD`` be a plain ``primrec`` with no separate capture-avoiding
substitution: a bound variable is interpreted by looking up its index in an
explicit assignment stack ``env = nat ⇒ i``, and going under ``∀``/``∃`` simply
*prepends* one entry to that stack (``case_nat d e``, Isabelle's standard ``nat``
case-combinator). Every faithfulness theorem below is still a **one-line
``induct``** — the "extra step" a binder-carrying structural induction needs,
beyond Tier 1's ``induct f arbitrary: x``, is generalizing the environment too
(``induct f arbitrary: e x``), so the induction hypothesis is available at the
*shifted* environment each quantifier clause recurses into.

The domain is a single set ``D :: i ⇒ bool`` shared by every world (the constant-
domain simplification) rather than a family ``D_w`` indexed by world — this is
what makes "K + constant domain" a fact about the **types**, not a runtime
frame/mode parameter to check and possibly reject: there is no way to *ask* this
module for a varying/increasing/decreasing domain or a T/S4/S5 frame, unlike
:mod:`unicode_logic_kit.hol.isabelle_modal` (which offers all four domain regimes,
every named frame, and the whole non-counterfactual modal family). ``R`` is left
completely arbitrary — as in :mod:`~unicode_logic_kit.hol.deepshallow.modal`, this
is what makes faithfulness hold for base K (and so, a fortiori, under any *stronger*
frame conditions one might separately assert on top of it — this module simply
never does).

Deliberately out of scope (raise :class:`NotImplementedError` **naming the
construct**, not approximated): equality/disequality (``=``/``≠``), function terms
(only object variables and 0-ary constants are terms here), and every operator
outside alethic ``□``/``◇`` — epistemic ``K_a``/doxastic ``B_a``/assertive/
bouletic, deontic ``Ⓞ``/``Ⓟ``, the whole temporal family, hybrid nominals/``@``,
and many-sorted ``SortedQuantifier``/``SortedConstant``. Use
:mod:`unicode_logic_kit.hol.isabelle_modal` / :mod:`unicode_logic_kit.hol.thf_modal`
for any of those — this module trades their breadth for a genuine, machine-checked
**meta-theorem** relating three embeddings of the fragment it does cover.

Public API: :func:`qml_to_deep`, :func:`qml_deep_faithfulness_theory`.
"""

from typing import List, Optional

from unicode_logic_kit.fol.nodes import (
    Node, Atom, Not, And, Or, Implies, Iff, Box, Diamond, Quantifier,
    Variable, Constant,
)
from unicode_logic_kit.fol._truth_constants import refuse_truth_constants
from ._common import AtomConsts, wrap_theory, NO_CONSTANT_WHY

# --------------------------------------------------------------------------- #
# The verified theory body (everything between ``begin`` and ``end``).
#
# This text is checked verbatim by the Isabelle-gated tests: exit 0 from
# ``check_theory`` means Isabelle's kernel discharged all five faithfulness
# theorems. Do not edit a clause without re-running that check — the ``induct``
# proofs depend on the exact operator definitions and the ``maxdefs`` / ``mindefs``
# simp bundles, exactly as in ``modal.py``.
# --------------------------------------------------------------------------- #

_QML_BODY = r'''typedecl w  \<comment> \<open>worlds\<close>
typedecl i  \<comment> \<open>individuals: the ONE constant domain shared by every world\<close>
typedecl s  \<comment> \<open>signature: predicate symbols and object-constant symbols\<close>
type_synonym wset = "w \<Rightarrow> bool"        \<comment> \<open>a set of worlds W\<close>
type_synonym dom  = "i \<Rightarrow> bool"        \<comment> \<open>the constant domain D\<close>
type_synonym acc  = "w \<Rightarrow> w \<Rightarrow> bool"   \<comment> \<open>accessibility relation R\<close>
type_synonym val  = "s \<Rightarrow> i list \<Rightarrow> w \<Rightarrow> bool"  \<comment> \<open>valuation V\<close>
type_synonym cint = "s \<Rightarrow> i"           \<comment> \<open>rigid interpretation of object constants\<close>
type_synonym env  = "nat \<Rightarrow> i"         \<comment> \<open>de Bruijn assignment stack\<close>

section \<open>Object terms: de Bruijn-indexed bound variables plus rigid constants\<close>

datatype obj = BVar nat | FVar s

primrec objD :: "env \<Rightarrow> cint \<Rightarrow> obj \<Rightarrow> i" where
  "objD e c (BVar n) = e n"
| "objD e c (FVar a) = c a"

section \<open>Deep embedding: object syntax as a datatype + recursive truth\<close>

datatype qml =
    Atm s "obj list" | TopD | BotD
  | NegD qml | AndD qml qml | OrD qml qml | ImpD qml qml | IffD qml qml
  | BoxD qml | DiaD qml
  | AllD qml | ExD qml

primrec truthD :: "env \<Rightarrow> cint \<Rightarrow> wset \<Rightarrow> acc \<Rightarrow> dom \<Rightarrow> val \<Rightarrow> w \<Rightarrow> qml \<Rightarrow> bool" where
  "truthD e c W R D V x (Atm p args) = V p (map (objD e c) args) x"
| "truthD e c W R D V x TopD         = True"
| "truthD e c W R D V x BotD         = False"
| "truthD e c W R D V x (NegD f)     = (\<not> truthD e c W R D V x f)"
| "truthD e c W R D V x (AndD f g)   = (truthD e c W R D V x f \<and> truthD e c W R D V x g)"
| "truthD e c W R D V x (OrD f g)    = (truthD e c W R D V x f \<or> truthD e c W R D V x g)"
| "truthD e c W R D V x (ImpD f g)   = (truthD e c W R D V x f \<longrightarrow> truthD e c W R D V x g)"
| "truthD e c W R D V x (IffD f g)   = (truthD e c W R D V x f = truthD e c W R D V x g)"
| "truthD e c W R D V x (BoxD f)     = (\<forall>y. R x y \<longrightarrow> truthD e c W R D V y f)"
| "truthD e c W R D V x (DiaD f)     = (\<exists>y. R x y \<and> truthD e c W R D V y f)"
| "truthD e c W R D V x (AllD f)     = (\<forall>d. D d \<longrightarrow> truthD (case_nat d e) c W R D V x f)"
| "truthD e c W R D V x (ExD f)      = (\<exists>d. D d \<and> truthD (case_nat d e) c W R D V x f)"

definition validD :: "qml \<Rightarrow> bool" where
  "validD f \<equiv> \<forall>e c W R D V x. W x \<longrightarrow> truthD e c W R D V x f"

section \<open>Maximal (heavyweight) shallow embedding: every parameter explicit\<close>

type_synonym sigma = "env \<Rightarrow> cint \<Rightarrow> wset \<Rightarrow> acc \<Rightarrow> dom \<Rightarrow> val \<Rightarrow> w \<Rightarrow> bool"

definition AtmS :: "s \<Rightarrow> obj list \<Rightarrow> sigma" where
  "AtmS p args \<equiv> \<lambda>e c W R D V x. V p (map (objD e c) args) x"
definition TopS :: "sigma" where "TopS \<equiv> \<lambda>e c W R D V x. True"
definition BotS :: "sigma" where "BotS \<equiv> \<lambda>e c W R D V x. False"
definition NegS :: "sigma \<Rightarrow> sigma" where
  "NegS f \<equiv> \<lambda>e c W R D V x. \<not> f e c W R D V x"
definition AndS :: "sigma \<Rightarrow> sigma \<Rightarrow> sigma" where
  "AndS f g \<equiv> \<lambda>e c W R D V x. f e c W R D V x \<and> g e c W R D V x"
definition OrS :: "sigma \<Rightarrow> sigma \<Rightarrow> sigma" where
  "OrS f g \<equiv> \<lambda>e c W R D V x. f e c W R D V x \<or> g e c W R D V x"
definition ImpS :: "sigma \<Rightarrow> sigma \<Rightarrow> sigma" where
  "ImpS f g \<equiv> \<lambda>e c W R D V x. f e c W R D V x \<longrightarrow> g e c W R D V x"
definition IffS :: "sigma \<Rightarrow> sigma \<Rightarrow> sigma" where
  "IffS f g \<equiv> \<lambda>e c W R D V x. f e c W R D V x = g e c W R D V x"
definition BoxS :: "sigma \<Rightarrow> sigma" where
  "BoxS f \<equiv> \<lambda>e c W R D V x. \<forall>y. R x y \<longrightarrow> f e c W R D V y"
definition DiaS :: "sigma \<Rightarrow> sigma" where
  "DiaS f \<equiv> \<lambda>e c W R D V x. \<exists>y. R x y \<and> f e c W R D V y"
definition AllS :: "sigma \<Rightarrow> sigma" where
  "AllS f \<equiv> \<lambda>e c W R D V x. \<forall>d. D d \<longrightarrow> f (case_nat d e) c W R D V x"
definition ExS :: "sigma \<Rightarrow> sigma" where
  "ExS f \<equiv> \<lambda>e c W R D V x. \<exists>d. D d \<and> f (case_nat d e) c W R D V x"
definition validS :: "sigma \<Rightarrow> bool" where
  "validS f \<equiv> \<forall>e c W R D V x. W x \<longrightarrow> f e c W R D V x"

section \<open>Minimal (lightweight) shallow embedding: R, D, V, C fixed as metalogical consts\<close>

consts Racc :: "acc"
consts Dset :: "dom"
consts Vval :: "val"
consts Cint :: "cint"
type_synonym tau = "env \<Rightarrow> w \<Rightarrow> bool"

definition AtmM :: "s \<Rightarrow> obj list \<Rightarrow> tau" where
  "AtmM p args \<equiv> \<lambda>e x. Vval p (map (objD e Cint) args) x"
definition TopM :: "tau" where "TopM \<equiv> \<lambda>e x. True"
definition BotM :: "tau" where "BotM \<equiv> \<lambda>e x. False"
definition NegM :: "tau \<Rightarrow> tau" where "NegM f \<equiv> \<lambda>e x. \<not> f e x"
definition AndM :: "tau \<Rightarrow> tau \<Rightarrow> tau" where "AndM f g \<equiv> \<lambda>e x. f e x \<and> g e x"
definition OrM  :: "tau \<Rightarrow> tau \<Rightarrow> tau" where "OrM f g \<equiv> \<lambda>e x. f e x \<or> g e x"
definition ImpM :: "tau \<Rightarrow> tau \<Rightarrow> tau" where "ImpM f g \<equiv> \<lambda>e x. f e x \<longrightarrow> g e x"
definition IffM :: "tau \<Rightarrow> tau \<Rightarrow> tau" where "IffM f g \<equiv> \<lambda>e x. f e x = g e x"
definition BoxM :: "tau \<Rightarrow> tau" where "BoxM f \<equiv> \<lambda>e x. \<forall>y. Racc x y \<longrightarrow> f e y"
definition DiaM :: "tau \<Rightarrow> tau" where "DiaM f \<equiv> \<lambda>e x. \<exists>y. Racc x y \<and> f e y"
definition AllM :: "tau \<Rightarrow> tau" where
  "AllM f \<equiv> \<lambda>e x. \<forall>d. Dset d \<longrightarrow> f (case_nat d e) x"
definition ExM :: "tau \<Rightarrow> tau" where
  "ExM f \<equiv> \<lambda>e x. \<exists>d. Dset d \<and> f (case_nat d e) x"
definition validM :: "tau \<Rightarrow> bool" where "validM f \<equiv> \<forall>e x. f e x"

section \<open>Mappings between the embeddings\<close>

primrec dpToMax :: "qml \<Rightarrow> sigma" where
  "dpToMax (Atm p args) = AtmS p args"
| "dpToMax TopD         = TopS"
| "dpToMax BotD         = BotS"
| "dpToMax (NegD f)     = NegS (dpToMax f)"
| "dpToMax (AndD f g)   = AndS (dpToMax f) (dpToMax g)"
| "dpToMax (OrD f g)    = OrS (dpToMax f) (dpToMax g)"
| "dpToMax (ImpD f g)   = ImpS (dpToMax f) (dpToMax g)"
| "dpToMax (IffD f g)   = IffS (dpToMax f) (dpToMax g)"
| "dpToMax (BoxD f)     = BoxS (dpToMax f)"
| "dpToMax (DiaD f)     = DiaS (dpToMax f)"
| "dpToMax (AllD f)     = AllS (dpToMax f)"
| "dpToMax (ExD f)      = ExS (dpToMax f)"

primrec dpToMin :: "qml \<Rightarrow> tau" where
  "dpToMin (Atm p args) = AtmM p args"
| "dpToMin TopD         = TopM"
| "dpToMin BotD         = BotM"
| "dpToMin (NegD f)     = NegM (dpToMin f)"
| "dpToMin (AndD f g)   = AndM (dpToMin f) (dpToMin g)"
| "dpToMin (OrD f g)    = OrM (dpToMin f) (dpToMin g)"
| "dpToMin (ImpD f g)   = ImpM (dpToMin f) (dpToMin g)"
| "dpToMin (IffD f g)   = IffM (dpToMin f) (dpToMin g)"
| "dpToMin (BoxD f)     = BoxM (dpToMin f)"
| "dpToMin (DiaD f)     = DiaM (dpToMin f)"
| "dpToMin (AllD f)     = AllM (dpToMin f)"
| "dpToMin (ExD f)      = ExM (dpToMin f)"

section \<open>Faithfulness (machine-checked by Isabelle's kernel)\<close>

lemmas maxdefs = AtmS_def TopS_def BotS_def NegS_def AndS_def OrS_def
                 ImpS_def IffS_def BoxS_def DiaS_def AllS_def ExS_def
lemmas mindefs = AtmM_def TopM_def BotM_def NegM_def AndM_def OrM_def
                 ImpM_def IffM_def BoxM_def DiaM_def AllM_def ExM_def

text \<open>Deep truth coincides pointwise with maximal-shallow truth. The extra
generalization beyond the propositional Tier 1 proofs (``arbitrary: e`` alongside
``x``) is exactly the "binder-carrying structural induction" step: it makes the
induction hypothesis available at the SHIFTED environment ``case_nat d e`` each
``AllD``/``ExD`` clause recurses into.\<close>
theorem faithful1a: "truthD e c W R D V x f = dpToMax f e c W R D V x"
  by (induct f arbitrary: e x) (simp_all add: maxdefs)

text \<open>Hence deep validity coincides with maximal-shallow validity.\<close>
theorem faithful1b: "validD f = validS (dpToMax f)"
  by (simp add: validD_def validS_def faithful1a)

text \<open>Deep truth in the fixed model coincides with minimal-shallow truth.\<close>
theorem faithful2: "truthD e Cint (\<lambda>_. True) Racc Dset Vval x f = dpToMin f e x"
  by (induct f arbitrary: e x) (simp_all add: mindefs)

text \<open>Maximal- and minimal-shallow truth coincide in that fixed model.\<close>
theorem faithful3: "dpToMax f e Cint (\<lambda>_. True) Racc Dset Vval x = dpToMin f e x"
  by (induct f arbitrary: e x) (simp_all add: maxdefs mindefs)

text \<open>Soundness of the minimal embedding for deep validity.\<close>
theorem sound_min: "validD f \<Longrightarrow> validM (dpToMin f)"
proof -
  assume *: "validD f"
  have "truthD e Cint (\<lambda>_. True) Racc Dset Vval x f" for e x
    using * by (simp add: validD_def)
  then show "validM (dpToMin f)"
    by (simp add: validM_def faithful2)
qed'''


# --------------------------------------------------------------------------- #
# Encoder:  toolkit QML AST  ->  deep ``qml`` term (de Bruijn-indexed).
# --------------------------------------------------------------------------- #

# Node type -> (deep constructor, arity 1 or 2). Quantifiers and Box/Diamond are
# handled separately below (they thread the bound-variable stack / recurse on
# ``.formula`` under a differently-named constructor).
_CONNECTIVES = {
    Not: ("NegD", 1), And: ("AndD", 2), Or: ("OrD", 2),
    Implies: ("ImpD", 2), Iff: ("IffD", 2),
}

_EQUALITY_PREDS = frozenset({"=", "≠"})

_UNSUPPORTED_HINT = (
    "this deep embedding is scoped to K + constant domain + alethic □/◇ "
    "only (Tier 2 of hol.deepshallow) — no epistemic/doxastic/assertive/"
    "bouletic, deontic, temporal, hybrid or many-sorted operators, no equality, "
    "no function terms. Use hol.isabelle_modal.to_isabelle_modal / "
    "hol.thf_modal.to_thf_modal_full for the full modal family and the other "
    "three domain regimes."
)


def _obj_to_deep(term: Node, bound: List[str], consts: AtomConsts) -> str:
    """Encode an object TERM as a deep ``obj`` value: ``BVar`` (de Bruijn index
    into ``bound``, innermost binder = index 0) or ``FVar`` (a rigid constant).

    ``bound`` lists the quantifiers currently in scope, outermost first, so a
    shadowed name resolves to the innermost (most recently pushed) binder —
    exactly the de Bruijn convention ``truthD``'s ``AllD``/``ExD`` clauses
    implement via ``case_nat``. A free (unbound) :class:`Variable` is refused:
    this deep embedding requires a closed formula, every object variable bound
    by some ``∀``/``∃`` in the formula itself.
    """
    if isinstance(term, Variable):
        if term.name not in bound:
            raise NotImplementedError(
                f"qml_to_deep: free variable {term.name!r} is not bound by any "
                "quantifier in the formula — the deep embedding requires a "
                "closed formula (every object variable bound).")
        idx = bound[::-1].index(term.name)
        return f"(BVar {idx})"
    if isinstance(term, Constant):
        return f"(FVar {consts.name(term.name)})"
    raise NotImplementedError(
        f"qml_to_deep: unsupported term {type(term).__name__} — this "
        "fragment has object variables and 0-ary constants only (no function "
        f"terms, no Number literals). {_UNSUPPORTED_HINT}")


def _encode(node: Node, bound: List[str], atoms: AtomConsts, consts: AtomConsts) -> str:
    """Encode a **K + constant-domain + alethic** QML formula as a deep ``qml`` term."""
    if isinstance(node, Atom):
        refuse_truth_constants([node], "qml_to_deep", NO_CONSTANT_WHY)
        if node.predicate in _EQUALITY_PREDS:
            raise NotImplementedError(
                f"qml_to_deep: {node.predicate!r} (equality) is outside this "
                f"fragment's scope, refused by name. {_UNSUPPORTED_HINT}")
        objs = ", ".join(_obj_to_deep(a, bound, consts) for a in node.args)
        return f"(Atm {atoms.name(node.predicate)} [{objs}])"
    if isinstance(node, Box):
        return f"(BoxD {_encode(node.formula, bound, atoms, consts)})"
    if isinstance(node, Diamond):
        return f"(DiaD {_encode(node.formula, bound, atoms, consts)})"
    if isinstance(node, Quantifier):
        inner = _encode(node.formula, bound + [node.variable.name], atoms, consts)
        if node.type in ("∀", "forall"):
            return f"(AllD {inner})"
        if node.type in ("∃", "exists"):
            return f"(ExD {inner})"
        raise ValueError(f"qml_to_deep: unknown quantifier type {node.type!r}.")
    spec = _CONNECTIVES.get(type(node))
    if spec is not None:
        name, arity = spec
        if arity == 1:
            return f"({name} {_encode(node.formula, bound, atoms, consts)})"
        left = _encode(node.left, bound, atoms, consts)
        right = _encode(node.right, bound, atoms, consts)
        return f"({name} {left} {right})"
    raise NotImplementedError(
        f"qml_to_deep: unsupported node type {type(node).__name__}. "
        f"{_UNSUPPORTED_HINT}")


def qml_to_deep(formula: Node, atoms: AtomConsts, consts: AtomConsts) -> str:
    r"""Encode a **K + constant-domain + alethic □/◇** QML formula as a deep
    ``qml`` term (de Bruijn-indexed bound variables, ``FVar`` for constants).

    ``atoms`` collects PREDICATE-symbol constants, exactly like the Tier 1
    encoders (:func:`~unicode_logic_kit.hol.deepshallow.modal.modal_to_deep` and
    siblings). ``consts`` collects OBJECT-constant symbols and is a REQUIRED
    argument, on purpose: a resolver this function created and the caller
    never got back would be a resolver whose declarations a hand-assembled
    theory can silently drop (an earlier version of this function made
    exactly that mistake, defaulting ``consts=None`` and fabricating one
    internally — a caller who then emitted only ``atoms.decls()`` produced an
    ill-typed Isabelle theory with no error raised on the Python side). To
    keep a predicate and a constant that sanitise to the same identifier from
    colliding on the one Isabelle type ``s`` both use, share the
    de-collision pool the way :func:`qml_deep_faithfulness_theory` itself
    does::

        atoms = AtomConsts()
        consts = AtomConsts()
        consts._used = atoms._used
        term = qml_to_deep(formula, atoms, consts)

    Any theory built from ``term`` — by hand, or via
    :func:`qml_deep_faithfulness_theory` — must emit BOTH ``atoms.decls()``
    and ``consts.decls()``; omitting either produces an ill-typed theory
    (Isabelle rejects the undeclared name with "Extra variables on rhs").

    Raises :class:`NotImplementedError` on equality/disequality, a function
    term or a Number literal, a free (unbound) variable, or any operator
    outside alethic ``□``/``◇`` (epistemic/doxastic/deontic/temporal/hybrid/
    many-sorted) — every refusal names the offending construct. There is no
    ``frame=``/``mode=`` parameter: this module structurally commits to K
    (``R`` left arbitrary) and the constant domain (one shared ``D``); use
    :mod:`unicode_logic_kit.hol.isabelle_modal` for the other frames/regimes.
    """
    return _encode(formula, [], atoms, consts)


# --------------------------------------------------------------------------- #
# Public entry points.
# --------------------------------------------------------------------------- #

def _qml_formula_section(term: str, atoms: AtomConsts, consts: AtomConsts) -> str:
    """The ``consts`` + ``definition example`` block grounding a concrete formula.

    Like :func:`unicode_logic_kit.hol.deepshallow._common.formula_section`, but
    emitting TWO ``consts`` groups (predicate symbols, then object constants) —
    ``qml_to_deep`` needs both namespaces, which ``_common.formula_section``'s
    single-``AtomConsts`` signature cannot express.
    """
    lines = ["", "section \\<open>A concrete embedded formula\\<close>", ""]
    lines += atoms.decls()
    lines += consts.decls()
    lines.append(f'definition example :: qml where "example = {term}"')
    return "\n".join(lines)


def qml_deep_faithfulness_theory(
    theory_name: str = "QmlFaithfulness",
    formula: Optional[Node] = None,
) -> str:
    r"""Emit the self-contained QML deep/maximal/minimal + faithfulness theory
    (Tier 2: K frame, constant domain, alethic □/◇ only).

    The returned string is a full ``theory <theory_name> imports Main begin ... end``
    containing the three embeddings and the five faithfulness theorems
    (``faithful1a/1b/2/3``, ``sound_min``), each closed by Isabelle. With a local
    Isabelle/HOL it is verified end to end by
    :func:`unicode_logic_kit.hol.isabelle_runner.check_theory` — exit 0 means
    Isabelle's kernel discharged every one; the theory text itself contains
    neither ``sorry`` nor ``oops``.

    Args:
        theory_name: the Isabelle theory / file name (a legal identifier).
        formula: an optional QML formula within this fragment. When given, its
            deep encoding is appended as ``definition example :: qml`` (with
            ``consts`` for its predicate and object-constant symbols), so the
            certificate is grounded in a concrete formula. Raises
            :class:`NotImplementedError` if ``formula`` uses a construct outside
            K + constant domain + alethic □/◇ (see :func:`qml_to_deep`).

    Returns:
        The theory text (newline-terminated).
    """
    extra = ""
    if formula is not None:
        atoms = AtomConsts()
        consts = AtomConsts()
        consts._used = atoms._used
        term = qml_to_deep(formula, atoms, consts)
        extra = _qml_formula_section(term, atoms, consts)
    return wrap_theory(theory_name, _QML_BODY, extra)
