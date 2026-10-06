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
from ..fol._truth_constants import refuse_truth_constants
from .deepshallow._common import AtomConsts, theory_name_ok

#: Why the B embeddings have no reading of ``$true`` / ``$false`` (the reason the
#: refusal names, the same one :mod:`unicode_fol_kit.semantics.relevant` gives).
_NO_CONSTANT_WHY = (
    "relevant logic has two truths and two falsities, an additive pair and a "
    "multiplicative pair, which differ in B, and TPTP's $true / $false names "
    "neither pair")
from ._ho_common import ThfNames

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
        refuse_truth_constants([formula], "to_isabelle_relevant", _NO_CONSTANT_WHY,
                               error=TypeError)
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


# --------------------------------------------------------------------------
# THF
# --------------------------------------------------------------------------
#
# The THF sibling of the theory above: the same shallow embedding (a formula
# is true or false AT A WORLD; ``N``/``star``/``R`` uninterpreted; the frame
# conditions bundled into ``wellformed``), for a higher-order ATP (Leo-III,
# Vampire-THF, Satallax) instead of Isabelle. The conjecture is
# ``wellformed => ![X:w] : ((N @ X) => φ_at(X))``, matching the Isabelle goal's
# "true at every NORMAL world of every interpretation" contract exactly.
#
# UNLIKE the Isabelle encoding (and an earlier draft of this function), ``φ``
# is NOT built from separately-declared ``NegC``/``AndC``/``OrC``/``ImpC``/
# ``IffC`` *combinators* that :func:`_thf_encode` would apply to already-built
# ``tau``-typed subterms (``impc @ (andc @ p @ q) @ p``, mirroring the
# Isabelle term exactly). :func:`_thf_encode` instead THREADS the current
# world through the recursion and emits ``φ``, at that world, as one native
# THF formula (``&``/``|``/``~``/``=>``/``!``/``?`` applied to already-a-world
# atoms) -- the same "world-relativised connective, no free-standing
# constant" style :mod:`unicode_fol_kit.hol.ho_modal`'s box/diamond nesting
# uses. This is NOT a change of meaning: a combinator applied to arguments and
# the fully-inlined, world-threaded reading of the same formula are
# beta-equivalent term for term (only ``ImpC``'s two case-split branches are
# genuinely new content per node, and those are exactly the N/R clauses below,
# transcribed unchanged from ``_PREAMBLE``). It is a change of PROOF-SEARCH
# DIFFICULTY: measured by hand with a battery of THF micro-examples in the
# scratchpad, Vampire 5.0.1's default portfolio needs real higher-order
# UNIFICATION to match a combinator's parameter against another combinator's
# PARTIAL APPLICATION (``F := (andc @ p @ q)`` to unfold ``impc``'s body) and
# failed to close even ``(P∧Q)→P`` in 60s / a 150-strategy CASC sweep in 30s;
# feeding it the same formula already reduced to ordinary quantified
# first-order-shaped THF over ``w`` (no function-valued arguments passed
# between macros at all) closes in well under a second. ``wellformed`` stays a
# single named, ARGUMENT-FREE ``$o`` ``definition`` (unfolding a nullary
# biconditional needs no higher-order unification either way) and stays a
# PREMISE of the conjecture rather than an ``axiom``, for the reason given in
# the module docstring: a model finder run on this problem's negation should
# still be free to build its own N/star/R rather than trusting an axiomatised
# triple.

#: The embedding's own functors, pre-claimed so no user atom's THF stem can
#: collide with them (see hol._ho_common.ThfNames).
_THF_RESERVED = ("w", "n", "star", "r", "wellformed")

_THF_PRELUDE = [
    "% Relevant logic B (simplified Routley-Meyer semantics) -> THF.",
    "% Shallow embedding: a formula is true/false AT A WORLD; N/star/R are",
    "% uninterpreted and their frame conditions are bundled into `wellformed`,",
    "% a PREMISE of the conjecture (never an axiom) -- see isabelle_relevant.py's",
    "% module docstring, _PREAMBLE, and the comment above _THF_PRELUDE for why",
    "% the connectives below are inlined at each world rather than routed",
    "% through separately-declared NegC/AndC/OrC/ImpC/IffC combinators.",
    "thf(w_type, type, ( w : $tType )).",
    "thf(n_type, type, ( n : w > $o )).",
    "thf(star_type, type, ( star : w > w )).",
    "thf(r_type, type, ( r : w > w > w > $o )).",
    "thf(wellformed_type, type, ( wellformed : $o )).",
    "thf(wellformed_def, definition, ( wellformed <=> "
    "( ( ? [X: w] : ( n @ X ) ) "
    "& ( ! [X: w] : ( ( star @ ( star @ X ) ) = X ) ) "
    "& ( ! [X: w, Y: w, Z: w] : ( ( r @ X @ Y @ Z ) => ( ~ ( n @ X ) ) ) ) ) )).",
]


def _thf_implies_at(left: Node, right: Node, world: str,
                    names: ThfNames, depth: int) -> str:
    """The world-threaded rendering of ``left -> right`` at ``world``.

    ImpC's own case split (:func:`_encode`'s ``ImpC`` clause, unchanged): at a
    NORMAL world every ``left``-world of the WHOLE model is a ``right``-world;
    at a non-normal world, every R-triple routes ``left`` to ``right``. ``Y``/
    ``Z`` are named from ``depth`` (not a running total) so that two SIBLING
    ``->`` nodes may freely reuse the same token -- each ``!`` binds only its
    own subformula -- while a NESTED ``->`` (reached through ``left``/
    ``right``, always recursed at ``depth + 1``) never reuses an ancestor's.

    This deliberately parallels :mod:`unicode_fol_kit.hol.ho_modal`'s OWN
    Kripke-world binders (``f"W{depth}"`` in its ``_thf``/``_thf_arg``), not
    :func:`~unicode_fol_kit.hol._ho_common.bound_token`: ``bound_token`` renames
    a USER-level binder apart from other in-scope user binders of the SAME
    source name (``thirdorder.py``/``ho_modal.py`` call it for the caller's own
    ``Quantifier``/``SecondOrderQuantifier``/``Lambda`` nodes), and no such node
    ever reaches this encoder -- ``_thf_encode`` accepts only nullary atoms and
    the propositional connectives, so there is no user binder to rename apart
    from anything. ``Y{depth}``/``Z{depth}`` name this EMBEDDING's own frame
    quantifiers instead, exactly the role ``ho_modal.py``'s plain ``W{depth}``
    plays for its own world binders (see the comment above its ``_thf``).
    """
    y, z = f"Y{depth}", f"Z{depth}"
    left_at_y = _thf_encode(left, y, names, depth + 1)
    right_at_y = _thf_encode(right, y, names, depth + 1)
    right_at_z = _thf_encode(right, z, names, depth + 1)
    return (f"( ( ( n @ {world} ) => ( ! [{y}: w] : "
            f"( {left_at_y} => {right_at_y} ) ) ) "
            f"& ( ( ~ ( n @ {world} ) ) => ( ! [{y}: w, {z}: w] : "
            f"( ( r @ {world} @ {y} @ {z} ) => "
            f"( {left_at_y} => {right_at_z} ) ) ) ) )")


def _thf_encode(formula: Node, world: str, names: ThfNames, depth: int = 0) -> str:
    """Recursive worker for :func:`to_thf_relevant`: ``formula`` rendered TRUE AT ``world``.

    Structurally identical to :func:`_encode`'s own recursion -- only nullary
    :class:`Atom`\\ s and Not/And/Or/Implies/Iff are accepted, everything else
    raises :class:`TypeError`, the same refusal :func:`_encode` makes,
    mirroring :func:`unicode_fol_kit.semantics.relevant._reject_non_propositional`
    -- but threading ``world`` (a THF term, not a fixed variable: ``¬`` passes
    down ``( star @ world )``) instead of building a free-standing ``tau``
    term. See the comment above ``_THF_PRELUDE`` for why.
    """
    if isinstance(formula, Atom):
        refuse_truth_constants([formula], "to_thf_relevant", _NO_CONSTANT_WHY,
                               error=TypeError)
        if formula.args:
            raise TypeError(
                "to_thf_relevant: only nullary propositional atoms are "
                f"supported; got {formula.to_unicode_str()!r} with arguments -- "
                "matching semantics.relevant._reject_non_propositional's "
                "rejection of non-nullary atoms.")
        functor = names.functor("predicate", formula.to_unicode_str())
        return f"( {functor} @ {world} )"
    if isinstance(formula, And):
        return (f"( {_thf_encode(formula.left, world, names, depth)} & "
                f"{_thf_encode(formula.right, world, names, depth)} )")
    if isinstance(formula, Or):
        return (f"( {_thf_encode(formula.left, world, names, depth)} | "
                f"{_thf_encode(formula.right, world, names, depth)} )")
    if isinstance(formula, Not):
        return f"( ~ {_thf_encode(formula.formula, f'( star @ {world} )', names, depth)} )"
    if isinstance(formula, Implies):
        return _thf_implies_at(formula.left, formula.right, world, names, depth)
    if isinstance(formula, Iff):
        return (f"( {_thf_implies_at(formula.left, formula.right, world, names, depth)} "
                f"& {_thf_implies_at(formula.right, formula.left, world, names, depth)} )")
    raise TypeError(
        f"to_thf_relevant: unsupported node type {type(formula).__name__} "
        f"in {formula.to_unicode_str()!r}. The B semantics "
        "(semantics.relevant) interprets only the propositional connectives "
        "not/and/or/implies/iff over nullary atoms -- no quantifiers, "
        "modalities, lambda terms, or Xor; see "
        "semantics.relevant._reject_non_propositional.")


def to_thf_relevant(formula: Node) -> str:
    r"""Emit a self-contained THF (TH0) problem asserting ``formula``'s validity in B.

    The THF sibling of :func:`to_isabelle_relevant`: the same shallow embedding
    (a formula is true/false at a world; ``N``/``star``/``R`` uninterpreted;
    the frame conditions bundled into ``wellformed``), for a higher-order ATP
    (Leo-III, Vampire-THF, Satallax) instead of Isabelle. The conjecture is
    ``wellformed => ![X:w] : ((N @ X) => φ_at(X))`` -- truth at every NORMAL
    world of every interpretation satisfying the frame conditions, matching
    :func:`unicode_fol_kit.semantics.relevant.rel_valid`'s "true at every
    normal world of every interpretation" contract, exactly as
    :func:`to_isabelle_relevant`'s goal does (see the comment above
    ``_THF_PRELUDE`` for why ``φ_at(X)`` is rendered inline rather than as a
    combinator applied to ``X``). As elsewhere in the toolkit, this function
    only emits the problem; it does not run a prover.

    Args:
        formula: the AST node to encode -- the propositional connectives
            ``¬ ∧ ∨ → ↔`` over nullary atoms.

    Raises:
        TypeError: propagated from :func:`_thf_encode` -- a quantifier,
            modality, lambda term, ``Xor``, or non-nullary atom, mirroring
            :func:`to_isabelle_relevant`'s own refusal and
            :func:`unicode_fol_kit.semantics.relevant._reject_non_propositional`.
    """
    names = ThfNames(reserved=_THF_RESERVED)
    body = _thf_encode(formula, "X", names)
    lines = list(_THF_PRELUDE)
    for label in sorted({atom.to_unicode_str() for atom in formula.atoms()}):
        functor = names.functor("predicate", label)
        lines.append(f"thf({functor}_type, type, ( {functor} : w > $o )).")
    lines.append(
        "thf(goal, conjecture, ( wellformed => "
        f"( ! [X: w] : ( ( n @ X ) => {body} ) ) )).")
    return "\n".join(lines) + "\n"
