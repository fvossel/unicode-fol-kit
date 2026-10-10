r"""Third-order MODAL logic → HOL: the shallow embedding, worlds made explicit.

Third-order modal logic is where a formula can say ``Positive(G)`` — a predicate
of a PROPERTY — inside a ``□``. Nothing first-order carries it and no
propositional modal calculus reaches it, but a higher-order prover does, through
the same shallow (Benzmüller-style) embedding the rest of this package uses: a
proposition is not a truth value but a FUNCTION FROM WORLDS to truth values, and
every connective is lifted to act pointwise on those functions. The modal
operators then become ordinary quantifiers over the accessibility relation, and
what a HOL prover sees is plain higher-order logic.

The three levels get three types::

    i                       individuals
    world                   worlds
    sigma = world => bool   propositions   (a "truth value" per world)
    i => sigma              properties     (the third order's argument type)
    (i => sigma) => sigma   predicates OF properties  -- e.g. Positive

and the lifted vocabulary is emitted as Isabelle ``abbreviation``\ s rather than
``definition``\ s **on purpose**: an abbreviation is unfolded by the parser, so
`blast`/`metis`/`auto` see through the embedding to plain HOL without being told
to unfold anything. A ``definition`` would hide the goal behind a constant and
turn every proof into an unfolding exercise.

``mall`` / ``mex`` are polymorphic (``('a => sigma) => sigma``), so ONE pair of
binders serves individual quantification and property quantification alike —
which is the embedding's own reason for existing: the object logic's orders are
distinguished by the TYPE at the binder, not by separate machinery.

**What this module emits, and what it does not.** It emits a self-contained
Isabelle theory (or a THF problem) — types, lifted vocabulary, the frame axioms
for the chosen system, the signature read off the formulas, the axioms, and the
goals with whatever proof text the caller supplies. It does not run a prover;
:func:`unicode_logic_kit.hol.isabelle_runner.check_theory` does that.

**Fragment.** Alethic ``□`` / ``◇``, agent-indexed epistemic/doxastic/assertive/
bouletic (``K_a`` / ``B_a`` / ``Say_a`` / ``Want_a``), deontic (``O`` / ``P``,
serial), temporal (``Always`` / ``Eventually`` / ``Next`` / ``Until`` / ``Since``
and their past mirrors ``Historically`` / ``Once`` / ``Previous``) and hybrid
(nominals / ``@``) — the same non-counterfactual family
:mod:`unicode_logic_kit.hol.thf_modal` / :mod:`unicode_logic_kit.hol.isabelle_modal`
carry at first order, ported here to the third-order shallow embedding rather
than reinvented. Two things stay refused BY NAME rather than approximated: the
Lewis counterfactuals ``Would`` / ``Might`` (they read a similarity ordering of
worlds, not an accessibility relation — see
:mod:`unicode_logic_kit.hol.isabelle_conditional`), and the GROUP-epistemic
operators ``EverybodyKnows`` / ``DistributedKnowledge`` / ``CommonKnowledge``
(``C_G`` needs a transitive closure this embedding does not attempt).

**Equality is rigid, or refused.** ``t₁ = t₂`` / ``t₁ ≠ t₂`` between INDIVIDUALS is
read exactly as :func:`unicode_logic_kit.fol.qml.qml_is_valid`,
:mod:`unicode_logic_kit.hol.thf_modal` and :mod:`unicode_logic_kit.hol.isabelle_modal`
read it: HOL's own ``=`` over the individual type ``i`` with NO world argument
(Isabelle ``(\<lambda>_. a = b)``, THF the ``meq`` macro of ``thf_modal``), so it
cannot vary with the world. ``a = a`` and ``a = b → □(a = b)`` are theorems,
``□(a = b) → a = b`` holds exactly on a SERIAL frame (every world has a successor,
which every reflexive frame does), and ``a = a`` holds under every ``mode=``
(identity is not existence-guarded). ``≠`` is lowered to
``¬(=)`` first, by :func:`unicode_logic_kit.hol.isabelle_modal._lower_identity` — which is
:func:`unicode_logic_kit.fol.qml._st_equality` — and nothing is declared for either: no
``feq`` / ``fneq`` exists in the emitted theory or problem. Two cases are refused, both
loudly, both before anything is rendered:

* a ``=`` / ``≠`` atom that does not have exactly two terms raises ``ValueError``
  (``qml``'s rule: the glyphs are reserved for identity and are never a world-relative
  predicate);
* identity at a PROPERTY type — a predicate name or a λ-abstraction as a term of ``=`` —
  raises ``NotImplementedError`` through
  :func:`unicode_logic_kit.semantics._modal_reject.reject_equality`. That is not rigid
  OBJECT identity but a different question. The grammar cannot even write it, the
  signature analysis types the two slots of ``=`` independently (so ``G = H`` with ``G``
  unary and ``H`` binary would pass and be ill-typed), and HOL's ``=`` at ``i ⇒ σ`` is
  one particular answer — necessary coextension — to a question the kit has no oracle
  for. State the relation you mean (``∀x □(P(x) ↔ Q(x))``) instead.

The ordering atoms ``<`` ``>`` ``≤`` ``≥`` stay ordinary uninterpreted relations,
world-relativised, as in ``qml``.

**Constants and free variables.** A constant is a particular individual that its name
stands for; a free variable is a parameter of the problem, one unknown element shared by
every formula (see :mod:`unicode_logic_kit.fol._free_parameters`). The two are different
symbols even when they are spelled alike, so ``P(x)`` with a free ``x`` and ``P('x')`` are
two statements: each is declared under a name of its own (``x`` for the variable, ``x_2``
for the constant) and a constant is never looked up among the bound variables, so no binder
of any name captures it. A constant of any name has a legal identifier in both targets (a
name that is an Isabelle identifier is written as it is, any other name under the kit's ASCII
stem of it; THF always uses the stem), and every symbol of the problem — predicate, function,
free variable, constant, and the embedding's own vocabulary (``R``, ``mall``, ``Rk``, ``nom_i``,
…) — gets a name of its own, so two names that share a stem are still two symbols.

**Sorts.** A many-sorted formula (``many_sorted=True`` next to ``modal=True`` at
second or third order) is read as :mod:`unicode_logic_kit.hol.isabelle_modal`
reads one at first order. The sort ``S`` is a WORLD-RELATIVE unary predicate of
type ``i ⇒ sigma``, ``∀x:S φ`` is ``∀x (S(x) → φ)`` and ``c:S`` is the constant
``c``. Two families of axioms, valid at every world, state what that rewriting
drops: ``nonempty_sort<i>`` (the sort has an element at every world; under an
actualist ``mode=`` one that exists there, because the witness goes through the
guarded binder like any ``∃x``) and ``sort_member<i>`` (a sorted constant is in
its sort at every world; a constant is a rigid designator, and this fact is not
guarded by existence). A property and a predicate quantifier are not sorted. A
bound predicate variable named like a sort is refused: the sort and the predicate
of its name are one symbol. So is an axiom or goal of the caller that has the name
of one of the axioms written for the sorts of its problem.

**Domains — two independent axes.** ``mode=`` (default ``"constant"``, i.e.
possibilist) accepts the same domain-regime vocabulary as
:mod:`unicode_logic_kit.hol.isabelle_modal`'s ``_ACTUALIST_MODES``: ``"varying"``,
``"increasing"``, ``"cumulative"``, ``"decreasing"``, on top of the
constant/possibilist default. The **one genuinely new judgment call this port
makes** (first order has no property quantifier to decide about): the
``existsAt``-guard an actualist mode adds applies ONLY to the
INDIVIDUAL-typed use of the polymorphic binder (a :class:`~unicode_logic_kit.fol.nodes.Quantifier`
node, ranging over type ``i``) — a PROPERTY quantifier
(:class:`~unicode_logic_kit.fol.nodes.SecondOrderQuantifier`, type ``i ⇒ sigma``)
always stays ``mall``/``mex``, unguarded, constant across worlds, matching how
the ontological-argument literature and Fitting-style actualist QML treat
properties (an object may cease to exist; the property "being golden" does not
along with it). Under the default constant mode, individual quantification is
`mall`/`mex` too — textually and semantically identical to today, so
``hol.goedel`` and this module's own docs example are unaffected; only an
actualist ``mode=`` pays for the ``existsAt :: i ⇒ world ⇒ bool`` guard's
extra vocabulary and axioms, reusing the pattern of isabelle_modal.py's
``_quant_block``/``_domain_axioms`` (Isabelle abbreviations) and thf_modal.py's
``mforall``/``mexists`` THF definitions plus their domain axioms.
"""

from dataclasses import dataclass
from typing import Dict, List, Optional, Sequence, Tuple

from ..fol.nodes import (
    Node, Atom, Not, And, Or, Xor, Implies, Iff, Quantifier,
    SecondOrderQuantifier, PredicateTerm,
    Variable, Constant, Function, LambdaVar, Lambda,
    Box, Diamond,
    Knows, Believes, Says, Wants,
    Obligatory, Permitted,
    Always, Eventually, Next, Until, Since,
    Historically, Once, Previous,
    Nominal, At,
    analyse_signatures,
)
# Down (the ↓ binder, N1) is not yet re-exported through fol.nodes / fol's
# public __init__ / the top-level unicode_logic_kit package (that three-file
# edit is outside this change's file ownership — see the change's own
# report); imported directly from its defining module in the meantime, the
# same class object either import path would give.
from ..fol._hybrid_nodes import Down
from ..fol._ho_nodes import INDIVIDUAL
from ..fol._truth_constants import truth_value
from ..fol.frames import FRAMES, resolve_frame, UnsupportedFrameCondition
from ._ho_common import (
    UnsupportedHigherOrderNode, ORDERING, FREE_VARIABLE, CONSTANT, ISABELLE_BUILT_IN,
    peel_lambdas, rename_apart, bound_pred_names, atom_predicates,
    function_symbols, individual_symbols, ThfNames, IsabelleNames, bound_token,
    sorted_reading,
)
from ._isabelle_binders import (
    PREDICATE, VARIABLE, BinderScope, binder_tokens, collect_binders, declared_names,
)
from ..semantics._modal_reject import (
    EQUALITY_PREDICATES, is_equality_atom, reject_equality,
)
# Single-sourced domain-regime vocabulary: importing the frozensets (not the
# axiom TEXT, which stays local -- see the module docstring) keeps this
# module's ``mode=`` meaning the same set of names as the first-order sibling
# it ports the actualist guard from, so the two can never drift apart about
# what "varying" or "constant" means.
from .isabelle_modal import _ACTUALIST_MODES, _CONSTANT_MODES
# Rigid identity is single-sourced the same way: the lowering (``≠`` -> ``¬(=)``,
# a non-binary atom refused) is fol.qml._st_equality reached through
# isabelle_modal._lower_identity, and the THF macro that lifts HOL's own ``=``
# is thf_modal's -- so the first-order, second-order and third-order modal routes
# cannot disagree about what an identity atom is.
from .isabelle_modal import _has_identity, _lower_identity
from .thf_modal import _THF_RIGID_EQ, _THF_RIGID_EQ_DEF


# Isabelle's ASCII escapes, spelled once.
_ALL = r"\<forall>"
_EX = r"\<exists>"
_AND = r"\<and>"
_OR = r"\<or>"
_IMP = r"\<longrightarrow>"
_NOT = r"\<not>"
_LAM = r"\<lambda>"
_FUN = r"\<Rightarrow>"
_EQUIV = r"\<equiv>"
_NEQ = r"\<noteq>"


# --------------------------------------------------------------------------
# The lifted vocabulary
# --------------------------------------------------------------------------

_DEFINITIONS = [
    'typedecl i  \\<comment> \\<open>individuals\\<close>',
    'typedecl world  \\<comment> \\<open>worlds\\<close>',
    f'type_synonym sigma = "world {_FUN} bool"'
    '  \\<comment> \\<open>a proposition: one truth value per world\\<close>',
    '',
    f'consts R :: "world {_FUN} world {_FUN} bool"'
    '  \\<comment> \\<open>accessibility\\<close>',
    '',
    '\\<comment> \\<open>Abbreviations, not definitions: the automation must see '
    'THROUGH the embedding.\\<close>',
    f'abbreviation mnot :: "sigma {_FUN} sigma"'
    f' where "mnot p {_EQUIV} {_LAM}v. {_NOT} p v"',
    f'abbreviation mand :: "sigma {_FUN} sigma {_FUN} sigma"'
    f' where "mand p q {_EQUIV} {_LAM}v. p v {_AND} q v"',
    f'abbreviation mor :: "sigma {_FUN} sigma {_FUN} sigma"'
    f' where "mor p q {_EQUIV} {_LAM}v. p v {_OR} q v"',
    f'abbreviation mimp :: "sigma {_FUN} sigma {_FUN} sigma"'
    f' where "mimp p q {_EQUIV} {_LAM}v. p v {_IMP} q v"',
    f'abbreviation miff :: "sigma {_FUN} sigma {_FUN} sigma"'
    f' where "miff p q {_EQUIV} {_LAM}v. p v = q v"',
    f'abbreviation mxor :: "sigma {_FUN} sigma {_FUN} sigma"'
    f' where "mxor p q {_EQUIV} {_LAM}v. p v {_NEQ} q v"',
    f'abbreviation mbox :: "sigma {_FUN} sigma"'
    f' where "mbox p {_EQUIV} {_LAM}v. {_ALL}u. R v u {_IMP} p u"',
    f'abbreviation mdia :: "sigma {_FUN} sigma"'
    f' where "mdia p {_EQUIV} {_LAM}v. {_EX}u. R v u {_AND} p u"',
    f'abbreviation mall :: "(\'a {_FUN} sigma) {_FUN} sigma"'
    f' where "mall P {_EQUIV} {_LAM}v. {_ALL}x. P x v"',
    f'abbreviation mex :: "(\'a {_FUN} sigma) {_FUN} sigma"'
    f' where "mex P {_EQUIV} {_LAM}v. {_EX}x. P x v"',
    f'abbreviation mvalid :: "sigma {_FUN} bool"'
    f' where "mvalid p {_EQUIV} {_ALL}v. p v"',
]


def ho_modal_definitions() -> str:
    """Return the Isabelle preamble: the three types, ``R``, and the lifted vocabulary.

    Emitted verbatim by :func:`isabelle_ho_modal_theory`; exposed separately so a
    caller writing its own theory around the same embedding can reuse exactly
    the vocabulary the kit's emitted goals are stated in.
    """
    return "\n".join(_DEFINITIONS)


# --------------------------------------------------------------------------
# Modal-family usage scan
# --------------------------------------------------------------------------
#
# What relations/vocabulary a theory needs is a property of the FORMULAS, not
# of a caller-supplied flag -- so it is read off the AST once, the same way
# hol.isabelle_modal's ``_Sig``/``_scan`` do at first order. Unlike that
# scanner this one does not ALSO collect the free signature (analyse_signatures
# / _signature_lines already do that, over the SAME third-order AST both HOL
# exporters share); it only answers "which modal families occur", which is
# what decides which relation consts / abbreviations / axioms this theory
# needs.

class _FamilyUsage:
    """Which non-alethic modal families a formula set uses, and whether it quantifies."""

    def __init__(self):
        self.epistemic = False   # Knows      -- relation Rk
        self.doxastic = False    # Believes   -- relation Rb
        self.assertive = False   # Says       -- relation Rs
        self.bouletic = False    # Wants      -- relation Rw
        self.deontic = False     # Obligatory / Permitted -- relation Rd (serial)
        self.temporal = False    # Always / Eventually / Historically / Once -- Rt
        self.next_ = False       # Next                                    -- Rn
        self.previous = False    # Previous (converse-of-Rn reader)
        self.until = False       # Until (inductive muntil over Rn)
        self.since = False       # Since  (inductive msince over converse Rn)
        self.hybrid = False      # Nominal / At -- world constants Nom_<name>
        self.has_quant = False   # a plain individual Quantifier occurs

    @property
    def needs_next_rel(self) -> bool:
        """Whether the one-step relation ``Rn`` must be declared.

        Needed by ``Next`` (mnext), ``Previous`` (mprevious -- its converse),
        and the inductive ``muntil`` / ``msince`` (one-step forward/backward
        path search) -- exactly mirroring
        :attr:`unicode_logic_kit.hol.isabelle_modal._Sig.needs_next_rel`.
        """
        return self.next_ or self.previous or self.until or self.since


# The four agent-indexed families a ``systems=`` dict may name -- each is
# also the exact attribute name on _FamilyUsage that reports whether the
# formula set uses it (see _validate_systems).
_AGENT_FAMILIES = frozenset({"epistemic", "doxastic", "assertive", "bouletic"})


def _isa_family_rel(family: str) -> str:
    """The Isabelle relation constant for an agent-indexed family."""
    return {"epistemic": "Rk", "doxastic": "Rb",
            "assertive": "Rs", "bouletic": "Rw"}[family]


def _scan_family_usage(formulas: Sequence[Node]) -> _FamilyUsage:
    """Walk ``formulas`` and report which modal families / quantifiers occur.

    Uses the generic :meth:`~unicode_logic_kit.fol._fol_nodes.Node.walk`, which
    reaches every structural child regardless of node type (including a
    :class:`~unicode_logic_kit.fol.nodes.Knows`/``Obligatory``/... node's own
    ``agent``/``formula`` fields) -- so a new node type nested anywhere in the
    tree is still visited; only the classification below is by hand.
    """
    usage = _FamilyUsage()
    for formula in formulas:
        for node in formula.walk():
            if isinstance(node, Down):
                # Checked FIRST (ahead of even the generic walk classification
                # below) so a ↓-formula is refused before any vocab/signature
                # work happens on it — never let it fall through to the
                # generic "hybrid" bucket (True for Down too, for free, since
                # Down.variable is itself a Nominal) unnoticed.
                raise UnsupportedHigherOrderNode(_NO_DOWN)
            if isinstance(node, Knows):
                usage.epistemic = True
            elif isinstance(node, Believes):
                usage.doxastic = True
            elif isinstance(node, Says):
                usage.assertive = True
            elif isinstance(node, Wants):
                usage.bouletic = True
            elif isinstance(node, (Obligatory, Permitted)):
                usage.deontic = True
            elif isinstance(node, (Always, Eventually)):
                usage.temporal = True
            elif isinstance(node, (Historically, Once)):
                usage.temporal = True
            elif isinstance(node, Next):
                usage.next_ = True
            elif isinstance(node, Previous):
                usage.previous = True
            elif isinstance(node, Until):
                usage.until = True
            elif isinstance(node, Since):
                usage.since = True
            elif isinstance(node, (Nominal, At)):
                usage.hybrid = True
            elif isinstance(node, Quantifier):
                usage.has_quant = True
    return usage


# --------------------------------------------------------------------------
# Agent-indexed per-system frame axioms (K_a / B_a / Say_a / Want_a)
# --------------------------------------------------------------------------
#
# Ported verbatim (same five Horn schemas, same "leave the agent schematic"
# reading) from hol.isabelle_modal's _AGENT_CONDS -- kept as its own local
# copy rather than imported so the schema text stays self-contained in this
# file like everything else here, the same choice thf_modal.py makes for its
# own _agent_frame_axioms rather than importing isabelle_modal's Isabelle text.
_ISA_AGENT_CONDS = {
    "refl": '{tag}_refl: "{_ALL}a w. {rel} a w w"',
    "trans": ('{tag}_trans: "{_ALL}a w v u. {rel} a w v {_IMP} '
              '{rel} a v u {_IMP} {rel} a w u"'),
    "sym": '{tag}_sym: "{_ALL}a w v. {rel} a w v {_IMP} {rel} a v w"',
    "serial": '{tag}_serial: "{_ALL}a w. {_EX}v. {rel} a w v"',
    "eucl": ('{tag}_eucl: "{_ALL}a w v u. {rel} a w v {_IMP} '
             '{rel} a w u {_IMP} {rel} a v u"'),
}


def _agent_system_axioms(family: str, system: str) -> List[str]:
    """Per-agent frame axioms constraining ``family``'s relation under ``system``.

    Each axiom universally quantifies the agent explicitly (``\\<forall>a``), so
    the property holds for EVERY agent -- matching
    :func:`unicode_logic_kit.hol.isabelle_modal._agent_system_axioms`'s reading
    and, semantically, the per-agent relations of
    :func:`unicode_logic_kit.semantics.kripke.satisfies_modal`. Only systems
    whose conditions are plain Horn frame properties are accepted; a system
    needing Löb / directedness / connectedness has no per-agent schema here
    and raises rather than silently emitting a WEAKER logic than requested --
    the same refusal :func:`~unicode_logic_kit.hol.isabelle_modal._agent_system_axioms`
    makes.
    """
    if system not in FRAMES:
        raise ValueError(
            f"isabelle_ho_modal_theory: unknown system {system!r} for "
            f"{family} (use one of {sorted(FRAMES)})."
        )
    conditions = resolve_frame(system)
    unsupported = [c for c in conditions if c not in _ISA_AGENT_CONDS]
    if unsupported:
        raise NotImplementedError(
            f"isabelle_ho_modal_theory: system {system!r} for {family} needs "
            f"the frame condition(s) {unsupported}, which have no per-agent "
            f"axiom schema here; use frame= on the alethic relation for those "
            f"systems."
        )
    rel = _isa_family_rel(family)
    return [
        "axiomatization where " + _ISA_AGENT_CONDS[c].format(
            rel=rel, tag=rel, _ALL=_ALL, _EX=_EX, _IMP=_IMP)
        for c in conditions
    ]


def _validate_systems(usage: _FamilyUsage, systems: Optional[dict],
                      caller: str = "isabelle_ho_modal_theory") -> dict:
    """Validate ``systems=`` and return it (``{}`` if ``None``).

    Every key must be one of the four agent-indexed families; a family named
    that the formula set never actually uses is refused (the axiom would be
    dead weight the caller never asked to constrain, and silently accepting
    it risks a typo -- e.g. ``"epistemc"`` -- going unnoticed). Shared between
    :func:`isabelle_ho_modal_theory` and :func:`to_thf_ho_modal` (``caller``
    only changes what the error names), so the two HOL routes can never
    accept a different ``systems=`` for the same input.
    """
    if not systems:
        return {}
    unknown = sorted(set(systems) - set(_AGENT_FAMILIES))
    if unknown:
        raise ValueError(
            f"{caller}: unknown systems= famil{'y' if len(unknown) == 1 else 'ies'} "
            f"{unknown} (use any of {sorted(_AGENT_FAMILIES)})."
        )
    unused = [fam for fam in systems if not getattr(usage, fam)]
    if unused:
        raise ValueError(
            f"{caller}: systems= names {sorted(unused)}, but "
            f"the formula set contains no matching operator "
            f"(K_a / B_a / Say_a / Want_a respectively)."
        )
    return dict(systems)


# --------------------------------------------------------------------------
# Extended vocabulary: agent-indexed / deontic / temporal / hybrid families
# --------------------------------------------------------------------------
#
# Emitted CONDITIONALLY (only the relations/abbreviations a formula set
# actually needs), matching hol.isabelle_modal's own conditional emission --
# unlike this module's THF side (see _THF_FAMILY_DEFS below), which follows
# thf_modal.py's convention of declaring every relation unconditionally.
# Isabelle keeps the conditional discipline the ALETHIC frame axioms already
# use here (``if frame_lines: ...``), so a theory that never mentions K_a
# never declares Rk either.

def _family_vocab_lines(usage: _FamilyUsage) -> List[str]:
    """``consts``/``abbreviation`` lines for every family ``usage`` reports used."""
    out: List[str] = []
    for family in ("epistemic", "doxastic", "assertive", "bouletic"):
        if not getattr(usage, family):
            continue
        rel = _isa_family_rel(family)
        macro = {"epistemic": "mknows", "doxastic": "mbelieves",
                 "assertive": "msays", "bouletic": "mwants"}[family]
        out.append(f'consts {rel} :: "i {_FUN} world {_FUN} world {_FUN} bool"')
        out.append(f'abbreviation {macro} :: "i {_FUN} sigma {_FUN} sigma" where')
        out.append(f'  "{macro} a p {_EQUIV} {_LAM}v. {_ALL}u. {rel} a v u {_IMP} p u"')
    if usage.deontic:
        out += [
            f'consts Rd :: "world {_FUN} world {_FUN} bool"',
            f'abbreviation mobl :: "sigma {_FUN} sigma"'
            f' where "mobl p {_EQUIV} {_LAM}v. {_ALL}u. Rd v u {_IMP} p u"',
            f'abbreviation mperm :: "sigma {_FUN} sigma"'
            f' where "mperm p {_EQUIV} {_LAM}v. {_EX}u. Rd v u {_AND} p u"',
        ]
    if usage.temporal:
        out += [
            f'consts Rt :: "world {_FUN} world {_FUN} bool"'
            '  \\<comment> \\<open>henceforth (reflexive-transitive) reader for Always/Eventually\\<close>',
            f'abbreviation malways :: "sigma {_FUN} sigma"'
            f' where "malways p {_EQUIV} {_LAM}v. {_ALL}u. Rt v u {_IMP} p u"',
            f'abbreviation meventually :: "sigma {_FUN} sigma"'
            f' where "meventually p {_EQUIV} {_LAM}v. {_EX}u. Rt v u {_AND} p u"',
            f'abbreviation mhistorically :: "sigma {_FUN} sigma"'
            f' where "mhistorically p {_EQUIV} {_LAM}v. {_ALL}u. Rt u v {_IMP} p u"',
            f'abbreviation monce :: "sigma {_FUN} sigma"'
            f' where "monce p {_EQUIV} {_LAM}v. {_EX}u. Rt u v {_AND} p u"',
        ]
    if usage.needs_next_rel:
        out.append(
            f'consts Rn :: "world {_FUN} world {_FUN} bool"'
            '  \\<comment> \\<open>one-step reader for Next/Previous/Until/Since\\<close>')
    if usage.next_:
        out.append(f'abbreviation mnext :: "sigma {_FUN} sigma"'
                   f' where "mnext p {_EQUIV} {_LAM}v. {_ALL}u. Rn v u {_IMP} p u"')
    if usage.previous:
        out.append(f'abbreviation mprevious :: "sigma {_FUN} sigma"'
                   f' where "mprevious p {_EQUIV} {_LAM}v. {_ALL}u. Rn u v {_IMP} p u"')
    if usage.until:
        # Strong Until as a least-fixpoint INDUCTIVE predicate over Rn -- not
        # an abbreviation, because it is a genuine recursive definition, the
        # same reason hol.isabelle_modal's own ``inductive muntil`` is not one
        # either (see that module's _until_block). ``phi``/``psi`` are
        # world-indexed (type sigma, i.e. exactly isabelle_modal's "i =>
        # bool" reading at THAT module's world type), so muntil phi psi
        # partially applied already has type sigma.
        out += [
            'inductive muntil :: "sigma \\<Rightarrow> sigma \\<Rightarrow> world \\<Rightarrow> bool"',
            '  for phi :: sigma and psi :: sigma where',
            '  muntil_base: "psi w \\<Longrightarrow> muntil phi psi w"',
            '| muntil_step: "phi w \\<Longrightarrow> Rn w v \\<Longrightarrow> muntil phi psi v '
            '\\<Longrightarrow> muntil phi psi w"',
        ]
    if usage.since:
        out += [
            'inductive msince :: "sigma \\<Rightarrow> sigma \\<Rightarrow> world \\<Rightarrow> bool"',
            '  for phi :: sigma and psi :: sigma where',
            '  msince_base: "psi w \\<Longrightarrow> msince phi psi w"',
            '| msince_step: "phi w \\<Longrightarrow> Rn v w \\<Longrightarrow> msince phi psi v '
            '\\<Longrightarrow> msince phi psi w"',
        ]
    return out


def _hybrid_vocab_lines(nominal_consts: Sequence[str]) -> List[str]:
    """``consts nom_<name> :: world`` -- one world constant per nominal (H(@))."""
    return [f'consts {c} :: "world"'
           '  \\<comment> \\<open>the world named by a hybrid nominal\\<close>'
           for c in nominal_consts]


def _family_axiom_lines(usage: _FamilyUsage, systems: dict,
                        temporal_closure: bool) -> List[str]:
    """``axiomatization`` lines for every family/system ``usage``/``systems`` need.

    Order mirrors :func:`unicode_logic_kit.hol.isabelle_modal._collect_axioms`:
    per-agent systems, then deontic seriality, then the temporal
    closure/linking axioms -- so the two HOL routes read the same way.
    """
    lines: List[str] = []
    for family in sorted(systems):
        lines += _agent_system_axioms(family, systems[family])
    if usage.deontic:
        lines.append('axiomatization where Rd_serial: "{0}v. {1}u. Rd v u"'
                     .format(_ALL, _EX))
    if usage.temporal and temporal_closure:
        lines += [
            f'axiomatization where Rt_refl: "{_ALL}w. Rt w w"',
            f'axiomatization where Rt_trans: "{_ALL}w v u. Rt w v {_IMP} '
            f'Rt v u {_IMP} Rt w u"',
        ]
    # tnext ⊆ t*: every one-step Rn-successor (what Next/Previous/Until/Since
    # read) is henceforth-reachable (what Always/Eventually read) -- without
    # this link Always(P) -> Next(P), valid for satisfies_modal (X and G/F
    # both close over the SAME one-step "temporal" relation there), would be
    # a non-theorem of the embedding (Rt and Rn otherwise unconstrained
    # relative to each other). Mirrors isabelle_modal.py's n_in_t /
    # thf_modal.py's tnext_in_t exactly.
    if usage.temporal and usage.needs_next_rel:
        lines.append(f'axiomatization where Rn_in_Rt: "{_ALL}w v. Rn w v '
                     f'{_IMP} Rt w v"')
    return lines


# Frame condition -> its Isabelle axiom over R, universally quantified so the
# axiom is a schema about R and cannot be narrowed by a constant that happens to
# share a variable's name (see hol/isabelle_modal.py's note on that trap).
#
# "loeb"/"mckinsey"/"grz" are schemas over PROPOSITIONS, not conditions on R
# alone (there is no first-order frame correspondence for any of the three),
# so each states the Löb / McKinsey / Grzegorczyk schema directly, exactly as
# hol.isabelle_modal's r_loeb/r_mckinsey/r_grz do at first order -- with ONE
# difference in how the schema predicate P is written: it is bound EXPLICITLY
# here (`\<forall>P::sigma.`) rather than left a free/schematic variable the
# way isabelle_modal's first-order port leaves it. That first-order module
# gets away with a free P only via a side convention (_safe_name lower-cases
# every user predicate's leading character, so a free schematic `P` can never
# collide with a user symbol); this module carries no such convention, and
# does not need one for a different reason: isabelle_ho_modal_theory always
# emits the frame axioms (this dict) BEFORE the signature's `consts`
# declarations (see its body), so at the point a free P in, say, R_loeb would
# be elaborated, no user-declared `consts P` exists yet for it to resolve to
# -- Isar turns a free identifier with no existing constant of that name into
# a schematic variable of the statement, which is exactly the generalisation
# a bound `\<forall>P` gives explicitly. (Reversing that emission order would
# reintroduce a real capture: verified live against local Isabelle by moving
# `consts P` before a free-variable R_loeb and watching a proof for a
# DIFFERENT proposition Q, which should need R_loeb's full generality, stall
# instead of discharging.) The explicit binder is kept anyway, as
# defense-in-depth against that emission order ever changing and because it
# makes the schema's universal scope visible in the source text rather than
# resting on an unstated fact about Isar's free-variable elaboration. The THF
# side keeps the same explicit binder for the same reason; there a user's own
# ``P`` is a constant, spelled as the lower word ``p`` (see
# _ho_common.ThfNames), so it could not meet the schema variable in any case.
_FRAME_AXIOMS = {
    "refl": f'"{_ALL}x. R x x"',
    "sym": f'"{_ALL}x y. R x y {_IMP} R y x"',
    "trans": f'"{_ALL}x y z. R x y {_IMP} R y z {_IMP} R x z"',
    "serial": f'"{_ALL}x. {_EX}y. R x y"',
    "eucl": f'"{_ALL}x y z. R x y {_IMP} R x z {_IMP} R y z"',
    "directed": f'"{_ALL}x y z. R x y {_IMP} R x z {_IMP} ({_EX}u. R y u {_AND} R z u)"',
    "connected": f'"{_ALL}x y z. R x y {_IMP} R x z {_IMP} (R y z {_OR} R z y)"',
    "functional": f'"{_ALL}x y z. R x y {_IMP} R x z {_IMP} y = z"',
    "dense": f'"{_ALL}x y. R x y {_IMP} ({_EX}z. R x z {_AND} R z y)"',
    "shift_refl": f'"{_ALL}x y. R x y {_IMP} R y y"',
    "empty": f'"{_ALL}x y. {_NOT} R x y"',
    # Löb: box(box P -> P) -> box P, i.e. (∀y. Rxy -> ((∀z. Ryz -> Pz) -> Py))
    # -> (∀y. Rxy -> Py), for every world x and every proposition P.
    "loeb": (f'"{_ALL}P::sigma. {_ALL}x. ({_ALL}y. R x y {_IMP} '
             f'(({_ALL}z. R y z {_IMP} P z) {_IMP} P y)) {_IMP} '
             f'({_ALL}y. R x y {_IMP} P y)"'),
    # McKinsey: box(diamond P) -> diamond(box P).
    "mckinsey": (f'"{_ALL}P::sigma. {_ALL}x. ({_ALL}y. R x y {_IMP} '
                 f'({_EX}z. R y z {_AND} P z)) {_IMP} '
                 f'({_EX}y. R x y {_AND} ({_ALL}z. R y z {_IMP} P z))"'),
    # Grzegorczyk: box(box(P -> box P) -> P) -> P.
    "grz": (f'"{_ALL}P::sigma. {_ALL}x. ({_ALL}y. R x y {_IMP} '
            f'(({_ALL}z. R y z {_IMP} (P z {_IMP} ({_ALL}u. R z u {_IMP} P u))) '
            f'{_IMP} P y)) {_IMP} P x"'),
}


def _frame_axiom_lines(frame: str) -> List[str]:
    """Return the ``axiomatization`` lines constraining ``R`` for ``frame``.

    Reads :data:`unicode_logic_kit.fol.frames.FRAMES` like every other modal route
    in the kit, so a system means the same thing here as it does there. Every
    condition the registry lists has an entry in ``_FRAME_AXIOMS`` — including
    Löb, McKinsey and Grz, which have no first-order correspondence and are
    instead stated as schemas over propositions, each with its schema variable
    bound explicitly (see the comment above ``_FRAME_AXIOMS``). A name the
    registry itself does not know is caught earlier, by ``resolve_frame``; this
    loop's own raise is a defence against ``_FRAME_AXIOMS`` and the registry
    drifting apart, not a live refusal path for any currently-registered
    condition.
    """
    conditions = resolve_frame(frame)
    lines = []
    for condition in conditions:
        if condition not in _FRAME_AXIOMS:
            raise UnsupportedFrameCondition(
                f"ho_modal: frame condition {condition!r} (system {frame!r}) has no "
                f"axiom registered in this embedding's _FRAME_AXIOMS; "
                f"fol.frames.resolve_frame accepted it but this module does not "
                f"yet state it."
            )
        lines.append(f'axiomatization where R_{condition}: {_FRAME_AXIOMS[condition]}')
    return lines


# --------------------------------------------------------------------------
# Rigid identity
# --------------------------------------------------------------------------
#
# Object identity is NOT a world-relativised predicate (fol.qml's "Equality is
# rigid"). It is HOL's own ``=`` over the individual type ``i``, lifted to the
# type of a proposition by a world binder it never uses, so it cannot vary with the
# world. Both exporters read an identity atom through the two helpers below and
# nowhere else, so a formula is lowered and checked ONCE, up front -- never lazily
# at the atom, where a route that short-circuits could skip it.

#: How the refusal of a PROPERTY-typed identity speaks (see :func:`_rigid_identity`).
_PROPERTY_IDENTITY_ROUTE = "the third-order modal embedding at a property type"
_PROPERTY_IDENTITY_ATOM_READING = (
    "'=' is read between INDIVIDUALS only, as HOL's own identity over the type i; "
    "a property is a world-indexed function i => ... => sigma, and whether two of "
    "them are 'identical' (necessarily coextensive? coextensive at one world?) is a "
    "choice this embedding does not make for you"
)
#: Not the propositional routes' failure. They key an atom by its rendered form
#: and so get 'a = a' FALSE — a wrong answer. Here there is no single right
#: answer to give: HOL's own ``=`` at a property type IS one reading (necessary
#: coextension), and picking it silently would answer a question the caller did
#: not ask rather than the one they did.
_PROPERTY_IDENTITY_CONSEQUENCE = (
    "so reading it as HOL's own identity at that type would silently pick "
    "necessary coextension as what 'the same property' means"
)

_PROPERTY_IDENTITY_INSTEAD = (
    "State the relation you mean between the properties instead: necessary "
    "coextension is ∀x □(P(x) ↔ Q(x)), coextension at the current world is "
    "∀x (P(x) ↔ Q(x)). Identity of INDIVIDUALS (a = b) is supported, and rigid."
)


def _rigid_identity(formulas: Sequence[Node], caller: str) -> List[Node]:
    """Read every identity atom of ``formulas`` as rigid identity, or refuse it by name.

    Two steps, both BEFORE any signature analysis or rendering:

    1. An identity atom with a PROPERTY-typed term (a predicate name or a
       λ-abstraction, i.e. identity at type ``i ⇒ … ⇒ σ`` rather than ``i``) is
       refused by name through
       :func:`~unicode_logic_kit.semantics._modal_reject.reject_equality`. This is not
       rigid identity gone missing but a different question: the grammar cannot even
       write it (``G = H`` does not parse), :func:`~unicode_logic_kit.fol.nodes.analyse_signatures`
       types the two slots of ``=`` independently (so ``G = H`` with ``G`` unary and
       ``H`` binary would be accepted and ill-typed in HOL), and HOL's ``=`` at a
       function type is one particular answer -- necessary coextension -- to a question
       the kit has no oracle for. Rather than guess, the case is refused. It is checked
       BEFORE the lowering so the message names the atom as the caller wrote it
       (``≠``, not the ``¬(=)`` it would have become).
    2. :func:`~unicode_logic_kit.hol.isabelle_modal._lower_identity` -- the very rule
       :func:`unicode_logic_kit.fol.qml.qml_translate` applies (``t₁ ≠ t₂`` becomes
       ``¬(t₁ = t₂)``) -- and a non-binary ``=`` / ``≠`` raises ``ValueError``, as in
       ``qml``. A formula without an identity atom is returned unchanged.

    The returned list is parallel to ``formulas``.
    """
    for formula in formulas:
        for node in formula.walk():
            # A non-binary atom is step 2's ValueError, whatever its terms are.
            if is_equality_atom(node) and len(node.args) == 2 and any(
                    isinstance(arg, (PredicateTerm, Lambda)) for arg in node.args):
                reject_equality(node, caller, _PROPERTY_IDENTITY_ROUTE,
                                atom_reading=_PROPERTY_IDENTITY_ATOM_READING,
                                consequence=_PROPERTY_IDENTITY_CONSEQUENCE,
                                instead=_PROPERTY_IDENTITY_INSTEAD)
    return [_lower_identity(f, caller) for f in formulas]


def _identity_sides(node: Atom):
    """The two individual terms of an identity atom that :func:`_rigid_identity` accepted.

    The renderers call this on every ``=`` atom. An atom that is not a binary ``=``
    has bypassed the lowering (``≠`` becomes ``¬(=)`` there, a non-binary atom is
    refused there); rendering it anyway would route it through the generic predicate
    path, where THF's name resolver turns ``≠`` into ``fneq`` -- an uninterpreted
    reading of identity, which is exactly what this embedding refuses. So it raises.
    """
    if node.predicate != "=" or len(node.args) != 2:
        raise UnsupportedHigherOrderNode(
            f"ho_modal: the identity atom {node.to_unicode_str()!r} reached the renderer "
            f"without being lowered (≠ becomes ¬(=), and a non-binary =/≠ is refused, "
            f"before any rendering). Render through isabelle_ho_modal_theory / "
            f"to_thf_ho_modal, which do that; identity is never rendered as a "
            f"world-relative predicate."
        )
    return node.args


# --------------------------------------------------------------------------
# Isabelle rendering
# --------------------------------------------------------------------------


def _prop_type(arity: int) -> str:
    """Return the Isabelle type of a property of ``arity`` arguments: ``i => … => sigma``."""
    return "".join(f"i {_FUN} " for _ in range(arity)) + "sigma"


def _nominal_const(name: str) -> str:
    """The Isabelle ``world`` constant naming a hybrid nominal (``i`` -> ``nom_i``).

    A plain prefix, not a full de-collision registry: nominal names are
    already legal (lowercase) identifiers, so two distinct source names stay
    distinct after prefixing, and ``nom_<name>`` cannot coincide with any of
    this module's own fixed identifiers (``R``, ``Rk``, ``mall``, a bound
    ``w``/``v``/``u``/``x``, …) or with a free individual/predicate constant
    (a DIFFERENT Isabelle type, ``world`` rather than ``i``/``sigma``, so even
    a same-spelled clash would be a type error caught at load time, not a
    silent misreading).
    """
    return f"nom_{name}"


def _domain_vocab_lines() -> List[str]:
    """``existsAt`` + the existsAt-guarded ``mforall``/``mexists`` (actualist modes only).

    Ported from hol.isabelle_modal.py's ``_quant_block`` (see the module
    docstring's "Domains" section for the one judgment call this makes): the
    guard is typed ``i => world => bool`` (an INDIVIDUAL exists at a WORLD),
    matching ho_modal.py's own type names rather than isabelle_modal.py's
    (there ``i``/``e`` mean world/individual, the reverse of here). Emitted
    only when an actualist ``mode=`` is combined with an actual individual
    ``Quantifier`` — never for the default constant/possibilist mode, which
    keeps using the existing, unguarded ``mall``/``mex`` exactly as before.
    """
    return [
        f'consts existsAt :: "i {_FUN} world {_FUN} bool"'
        '  \\<comment> \\<open>individual x exists at world w\\<close>',
        f'abbreviation mforall :: "(i {_FUN} sigma) {_FUN} sigma" where',
        f'  "mforall P {_EQUIV} {_LAM}v. {_ALL}x. existsAt x v {_IMP} P x v"',
        f'abbreviation mexists :: "(i {_FUN} sigma) {_FUN} sigma" where',
        f'  "mexists P {_EQUIV} {_LAM}v. {_EX}x. existsAt x v {_AND} P x v"',
    ]


def _domain_axiom_lines(mode: str) -> List[str]:
    """``existsAt`` domain-regime axioms for an actualist ``mode`` — ported from
    :func:`unicode_logic_kit.hol.isabelle_modal._domain_axioms`, over ``R`` (this
    module's alethic relation) rather than ``r``. Never called for a constant
    mode (see :func:`_domain_vocab_lines`): there, quantification stays plain
    ``mall``/``mex`` and no ``existsAt`` axiom is needed at all.
    """
    out = [f'axiomatization where nonempty_dom: "{_EX}x. existsAt x w"']
    if mode in ("increasing", "cumulative"):
        out.append(f'axiomatization where cumul_dom: "existsAt x w {_IMP} '
                   f'R w v {_IMP} existsAt x v"')
    elif mode == "decreasing":
        out.append(f'axiomatization where decr_dom: "existsAt x v {_IMP} '
                   f'R w v {_IMP} existsAt x w"')
    # "varying": nonempty_dom only, no monotonicity axiom.
    return out


def _isa_arg(node: Node, bound_arity: Dict[str, int],
             display: Dict[str, str], mode: str,
             scope: Optional[BinderScope] = None,
             symbols: Optional[IsabelleNames] = None) -> str:
    """Render a node standing in ARGUMENT position — an individual or a property.

    ``scope`` holds the binders that enclose the node and the names they are printed under: a
    variable or a lambda variable bound by one of them is printed under its binder's name. A
    free variable and a constant are not bound by any binder, whatever their spelling: each is
    printed under the name ``symbols`` gives it, and the two have two names. Without a ``scope``
    every binder is printed under its own name.
    """
    if scope is None:
        scope = BinderScope({})
    if symbols is None:
        symbols = IsabelleNames(ISABELLE_BUILT_IN)
    if isinstance(node, (Variable, LambdaVar)):
        # a binder's token is never empty, so "" means: no binder of this name encloses the node
        return scope.token(VARIABLE, node.name, default="") or symbols.symbol(FREE_VARIABLE, node.name)
    if isinstance(node, Constant):
        return symbols.symbol(CONSTANT, node.name)
    if isinstance(node, PredicateTerm):
        return display.get(node.name) or symbols.symbol("predicate", node.name)
    if isinstance(node, Lambda):
        names, body = peel_lambdas(node)
        binders = []
        for name in names:
            token, scope = scope.enter(VARIABLE, name)
            binders.append(f"{_LAM}{token}::i.")
        return f"({' '.join(binders)} {_isa_sigma(body, bound_arity, display, mode, scope, symbols)})"
    if isinstance(node, Function):
        head = symbols.symbol("function", node.name)
        args = " ".join(_isa_arg(a, bound_arity, display, mode, scope, symbols) for a in node.args)
        return f"({head} {args})" if args else head
    raise UnsupportedHigherOrderNode(
        f"ho_modal: {type(node).__name__} cannot stand in argument position; an "
        f"argument is an individual term, a predicate name, or a λ-abstraction."
    )


_BINARY_ISA = {And: "mand", Or: "mor", Implies: "mimp", Iff: "miff", Xor: "mxor"}

#: Node types this embedding EXPLICITLY refuses by name rather than folding
#: into the generic "no reading for ..." fallback -- each needs its own
#: pointed message naming where the construct DOES belong.
_NO_COUNTERFACTUAL = (
    "ho_modal: the counterfactuals □→/◇→ (Would/Might) read a similarity "
    "ordering of worlds (Lewis spheres), not an accessibility relation, and "
    "are not shallow-embeddable the way □/◇/K_a/... are. Use "
    "hol.isabelle_conditional / isabelle_decide_counterfactual instead."
)

#: N1: the ↓ binder is not supported by this third-order HOL embedding —
#: H(@,↓) validity is undecidable, and this emitter's job (a theory/theorem
#: for a human or ATP proof search) assumes a goal shape that search can be
#: expected to close, not an open research question.
_NO_DOWN = (
    "ho_modal: the ↓ binder is not supported by this third-order HOL "
    "embedding — H(@,↓) validity is undecidable. Use "
    "unicode_logic_kit.fol.modal_translation.down_is_valid (propositional "
    "H(@,↓), Z3, PROVED-only) or unicode_logic_kit.atp.kripke_enum.KripkeEnumBackend "
    "/ modal_enum_search (bounded search, REFUTED-only) instead."
)


def _isa_sigma(node: Node, bound_arity: Dict[str, int],
               display: Dict[str, str], mode: str,
               scope: Optional[BinderScope] = None,
               symbols: Optional[IsabelleNames] = None) -> str:
    """Render ``node`` as an Isabelle term of type ``sigma`` (a world-indexed proposition).

    ``display`` gives each bound predicate variable the name it is printed under, ``scope`` each
    enclosing object binder (see :mod:`unicode_logic_kit.hol._isabelle_binders`); without a
    ``scope`` every binder is printed under its own name. ``symbols`` names the free symbols
    (predicates, functions, free variables, constants) and is the one the declarations were
    written under."""
    if scope is None:
        scope = BinderScope({})
    if symbols is None:
        symbols = IsabelleNames(ISABELLE_BUILT_IN)
    if isinstance(node, Not):
        return f"(mnot {_isa_sigma(node.formula, bound_arity, display, mode, scope, symbols)})"
    op = _BINARY_ISA.get(type(node))
    if op is not None:
        left = _isa_sigma(node.left, bound_arity, display, mode, scope, symbols)
        right = _isa_sigma(node.right, bound_arity, display, mode, scope, symbols)
        return f"({op} {left} {right})"
    if isinstance(node, Box):
        return f"(mbox {_isa_sigma(node.formula, bound_arity, display, mode, scope, symbols)})"
    if isinstance(node, Diamond):
        return f"(mdia {_isa_sigma(node.formula, bound_arity, display, mode, scope, symbols)})"
    if isinstance(node, Quantifier):
        # The one judgment call this port makes (see the module docstring):
        # ONLY the individual-typed binder is existsAt-guarded under an
        # actualist mode; a property binder (SecondOrderQuantifier, below)
        # never is.
        if mode in _ACTUALIST_MODES:
            binder = "mforall" if node.type == "∀" else "mexists"
        else:
            binder = "mall" if node.type == "∀" else "mex"
        token, inner = scope.enter(VARIABLE, node.variable.name)
        body = _isa_sigma(node.formula, bound_arity, display, mode, inner, symbols)
        return f"({binder} ({_LAM}{token}::i. {body}))"
    if isinstance(node, SecondOrderQuantifier):
        binder = "mall" if node.type == "∀" else "mex"
        arity = bound_arity.get(node.predicate, node.arity)
        name = display.get(node.predicate, node.predicate)
        body = _isa_sigma(node.formula, bound_arity, display, mode, scope, symbols)
        return (f"({binder} ({_LAM}{name}::{_prop_type(arity)}. {body}))")
    if isinstance(node, (Knows, Believes, Says, Wants)):
        macro = {Knows: "mknows", Believes: "mbelieves",
                Says: "msays", Wants: "mwants"}[type(node)]
        agent = _isa_arg(node.agent, bound_arity, display, mode, scope, symbols)
        body = _isa_sigma(node.formula, bound_arity, display, mode, scope, symbols)
        return f"({macro} {agent} {body})"
    if isinstance(node, Obligatory):
        return f"(mobl {_isa_sigma(node.formula, bound_arity, display, mode, scope, symbols)})"
    if isinstance(node, Permitted):
        return f"(mperm {_isa_sigma(node.formula, bound_arity, display, mode, scope, symbols)})"
    if isinstance(node, Always):
        return f"(malways {_isa_sigma(node.formula, bound_arity, display, mode, scope, symbols)})"
    if isinstance(node, Eventually):
        return f"(meventually {_isa_sigma(node.formula, bound_arity, display, mode, scope, symbols)})"
    if isinstance(node, Next):
        return f"(mnext {_isa_sigma(node.formula, bound_arity, display, mode, scope, symbols)})"
    if isinstance(node, Historically):
        return f"(mhistorically {_isa_sigma(node.formula, bound_arity, display, mode, scope, symbols)})"
    if isinstance(node, Once):
        return f"(monce {_isa_sigma(node.formula, bound_arity, display, mode, scope, symbols)})"
    if isinstance(node, Previous):
        return f"(mprevious {_isa_sigma(node.formula, bound_arity, display, mode, scope, symbols)})"
    if isinstance(node, Until):
        left = _isa_sigma(node.left, bound_arity, display, mode, scope, symbols)
        right = _isa_sigma(node.right, bound_arity, display, mode, scope, symbols)
        return f"(muntil {left} {right})"
    if isinstance(node, Since):
        left = _isa_sigma(node.left, bound_arity, display, mode, scope, symbols)
        right = _isa_sigma(node.right, bound_arity, display, mode, scope, symbols)
        return f"(msince {left} {right})"
    if isinstance(node, Nominal):
        return f"({_LAM}v::world. v = {_nominal_const(node.name)})"
    if isinstance(node, At):
        # The world binder is anonymous: ``body`` holds the caller's own symbols, and a binder
        # named ``v`` would capture a constant, a function or a predicate called ``v`` there.
        body = _isa_sigma(node.formula, bound_arity, display, mode, scope, symbols)
        return f"({_LAM}_. {body} {_nominal_const(node.nominal.name)})"
    if isinstance(node, Down):
        raise UnsupportedHigherOrderNode(_NO_DOWN)
    if isinstance(node, Atom):
        constant = truth_value(node)
        if constant is not None:
            # `$true` / `$false`: HOL's True / False under the anonymous world binder.
            return f"({_LAM}_. True)" if constant else f"({_LAM}_. False)"
        if is_equality_atom(node):
            # Rigid identity: HOL's own ``=`` under a world binder it never uses, so
            # it cannot vary by world. The binder is the anonymous ``_`` rather than a
            # name so a user variable called ``w`` can never be captured by it. The
            # same text isabelle_modal emits for the same atom.
            left, right = _identity_sides(node)
            return (f"({_LAM}_. {_isa_arg(left, bound_arity, display, mode, scope, symbols)} = "
                    f"{_isa_arg(right, bound_arity, display, mode, scope, symbols)})")
        if node.predicate in ORDERING:
            name = ORDERING[node.predicate]
        else:
            name = display.get(node.predicate) or symbols.symbol("predicate", node.predicate)
        if not node.args:
            return name
        args = " ".join(_isa_arg(a, bound_arity, display, mode, scope, symbols) for a in node.args)
        return f"({name} {args})"
    if type(node).__name__ in ("Would", "Might"):
        raise UnsupportedHigherOrderNode(_NO_COUNTERFACTUAL)
    raise UnsupportedHigherOrderNode(
        f"ho_modal: no reading for {type(node).__name__}. This embedding covers "
        f"alethic □/◇, agent-indexed epistemic/doxastic/assertive/bouletic "
        f"(K_a/B_a/Say_a/Want_a), deontic O/P, temporal (Always/Eventually/Next/"
        f"Until/Since and their past mirrors) and hybrid (nominals/@) over "
        f"third-order syntax. The Lewis counterfactuals (Would/Might) and the "
        f"GROUP-epistemic operators (EverybodyKnows/DistributedKnowledge/"
        f"CommonKnowledge) are not carried by any HOL route in this kit yet."
    )


def _used_ordering(apart: Sequence[Node]) -> List[str]:
    """The names of the ordering relations (``flt``, ...) that the formulas use, sorted."""
    return sorted({ORDERING[p] for f in apart for p in atom_predicates(f) if p in ORDERING})


def _signature_lines(apart: Sequence[Node], signatures, symbols: IsabelleNames) -> List[str]:
    """Return the ``consts`` declarations for every free symbol of ``apart``.

    ``apart`` are the formulas with their bound predicate variables renamed apart and
    ``signatures`` is the analysis over them TOGETHER, because that is the scope on which a
    free predicate's argument types are determined: ``Positive(G)`` in one axiom and ``G(x)``
    in another jointly say that ``Positive`` takes a property of arity 1.

    Every symbol is declared under the name ``symbols`` gives it, and ``symbols`` is the one
    the formulas are rendered with. A theory has one namespace for its constants, so a
    predicate, a function, a free variable and a constant that are spelled alike are four
    constants with four names, and none takes a name of the embedding's own vocabulary.
    """
    bound = set()
    for formula in apart:
        bound |= bound_pred_names(formula)
    predicates = [pred for pred in sorted(signatures.slots)
                  if not (pred in bound or pred in EQUALITY_PREDICATES or pred in ORDERING
                          or pred in ORDERING.values())]
    # Free individual symbols: a bare NAME parses to a Constant, and a variable left unbound
    # by any quantifier denotes a particular individual too. Both are individuals of type i,
    # but a free variable is a parameter and a constant a particular element: two symbols.
    individuals = individual_symbols(apart)
    functions = sorted(function_symbols(apart).items())
    symbols.claim([("predicate", pred) for pred in predicates]
                  + [("function", name) for name, _ in functions] + individuals)

    lines: List[str] = []
    for pred in predicates:
        parts = []
        for kind in signatures.slots[pred]:
            parts.append("i" if kind == INDIVIDUAL else f"({_prop_type(kind[1])})")
        arrow = "".join(f"{p} {_FUN} " for p in parts)
        lines.append(f'consts {symbols.symbol("predicate", pred)} :: "{arrow}sigma"')

    for kind, name in individuals:
        lines.append(f'consts {symbols.symbol(kind, name)} :: "i"')

    # Ordering predicates actually used, as world-relativised relations. Identity is
    # NOT among them: it is HOL's own ``=`` (see _rigid_identity) and is declared
    # nowhere.
    for name in _used_ordering(apart):
        lines.append(f'consts {name} :: "i {_FUN} i {_FUN} sigma"')

    # Function symbols in term position.
    for name, arity in functions:
        arrow = "".join(f"i {_FUN} " for _ in range(arity))
        lines.append(f'consts {symbols.symbol("function", name)} :: "{arrow}i"')
    return lines


# --------------------------------------------------------------------------
# Theory assembly
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class HoAxiom:
    """One named axiom of an emitted theory.

    ``comment`` is printed above it, so a theory can carry the argument's own
    numbering (``A1``, ``D2``, …) and say what each line is meant to assert.
    """

    name: str
    formula: Node
    comment: str = ""


@dataclass(frozen=True)
class HoGoal:
    """One named goal, with the proof text to attempt it with.

    ``proof`` is Isabelle proof text (``by blast``, ``using A1 A2 by metis``,
    ``nitpick [expect = genuine]``, …). The kit does not invent proofs: what is
    written here is what the theory will try. ``oops`` leaves the goal
    explicitly unproved, which is what :func:`to_isabelle_ho_modal` emits when
    no proof is supplied.

    A goal is stated EITHER as a ``formula`` of the object logic — asserted
    valid, i.e. ``mvalid φ`` — OR, for the one thing the object logic cannot
    say about itself, as a raw Isabelle ``statement`` such as ``"False"``. That
    second form is what lets a theory record that an axiom set is INCONSISTENT:
    "these axioms prove falsity" is a claim about the theory, not a formula in
    it. Exactly one of the two must be given.
    """

    name: str
    formula: Optional[Node] = None
    proof: str = "oops"
    comment: str = ""
    kind: str = "theorem"
    statement: Optional[str] = None

    def __post_init__(self):
        """Reject a goal that states nothing, or states itself twice over."""
        if (self.formula is None) == (self.statement is None):
            raise ValueError(
                f"HoGoal({self.name!r}): give exactly one of formula= (an object-logic "
                f"formula, asserted valid) or statement= (a raw Isabelle proposition)."
            )


def _refuse_a_sort_fact_name(facts: Sequence[Tuple[str, Node]], names: Sequence[str],
                             route: str) -> None:
    """Refuse an axiom or goal whose name is the name of a fact written for a sort.

    The facts of a many-sorted problem are written as axioms named ``nonempty_sort<i>`` and
    ``sort_member<i>``. A caller's axiom or goal of one of those names would be a second
    statement under one name, which Isabelle rejects as a duplicate fact and which leaves a
    THF problem with two formulas of one name. An unsorted problem has no facts and takes
    any name.

    Raises:
        ValueError: a name in ``names`` is the name of one of ``facts``.
    """
    stated = {fact_name for fact_name, _ in facts}
    for name in names:
        if name in stated:
            raise ValueError(
                f"{route}: the name {name!r} is taken by the axiom this writer states for a "
                f"sort of the problem (nonempty_sort<i>: a sort is not empty; "
                f"sort_member<i>: a sorted constant lies in its sort). Give the axiom or "
                f"goal another name.")


def isabelle_ho_modal_theory(name: str,
                             axioms: Sequence[HoAxiom] = (),
                             goals: Sequence[HoGoal] = (),
                             frame: str = "K",
                             preamble: Sequence[str] = (),
                             mode: str = "constant",
                             systems: Optional[dict] = None,
                             temporal_closure: bool = True) -> str:
    """Emit a complete Isabelle theory for a third-order modal axiom set and its goals.

    ``axioms`` are asserted as ``axiomatization where <name>: "mvalid φ"`` — valid at
    every world, which is what an axiom of the object logic means. ``goals`` are
    stated the same way and followed by their own proof text.

    ``frame`` names a system from :data:`unicode_logic_kit.fol.frames.FRAMES` and
    constrains ``R`` accordingly; ``"K"`` leaves ``R`` arbitrary. ``preamble``
    lines are inserted after the vocabulary and before the axioms, for anything
    the caller wants to add in Isabelle's own syntax.

    ``mode`` selects the domain regime for INDIVIDUAL quantification (see the
    module docstring): the default ``"constant"``/``"possibilist"`` behaves
    exactly as before this parameter existed; ``"varying"``/``"increasing"``/
    ``"cumulative"``/``"decreasing"`` add the ``existsAt``-guarded reading.
    ``systems`` optionally constrains one or more of the agent-indexed
    families -- ``{"epistemic": "S5", "doxastic": "KD45", ...}`` -- a family
    named that the formula set never uses is refused, and an unnamed one
    stays unconstrained (plain K). ``temporal_closure`` (default ``True``)
    adds the reflexive+transitive axioms that make ``Rt`` the henceforth
    relation ``Always``/``Eventually`` need, exactly mirroring
    :func:`unicode_logic_kit.hol.isabelle_modal.isabelle_modal_theory`'s own
    parameter of the same name.

    The signature is read off the axioms and goals together, so a symbol used in
    a goal but not in any axiom is still declared. Property-argument slots whose
    arity nothing in the theory determines are reported as a comment rather than
    silently defaulted — see :mod:`unicode_logic_kit.fol._ho_nodes`.

    Identity ``=`` / ``≠`` between individuals is RIGID HOL equality (``≠`` is ``¬(=)``),
    declared nowhere; a ``=`` / ``≠`` atom without exactly two terms raises
    ``ValueError`` and identity between PROPERTIES raises ``NotImplementedError`` — the
    module docstring's "Equality is rigid, or refused" has the reasons.
    """
    if frame not in FRAMES:
        raise ValueError(
            f"isabelle_ho_modal_theory: unknown frame {frame!r}; "
            f"known systems are {sorted(FRAMES)}."
        )
    if mode not in _ACTUALIST_MODES and mode not in _CONSTANT_MODES:
        raise ValueError(
            f"isabelle_ho_modal_theory: unknown mode {mode!r} "
            f"(use one of {sorted(_ACTUALIST_MODES | _CONSTANT_MODES)})."
        )
    # A goal stated raw (statement=) contributes no formula to type-check.
    typed_goals = [g for g in goals if g.formula is not None]
    # A many-sorted theory is read as its relativised formulas plus the facts about its
    # sorts, and a fact is an axiom of the object logic like any other: valid at every
    # world. An unsorted theory has no facts and its formulas are taken as they are.
    facts, relativised = sorted_reading(
        [a.formula for a in axioms] + [g.formula for g in typed_goals],
        "isabelle_ho_modal_theory")
    _refuse_a_sort_fact_name(facts, [a.name for a in axioms] + [g.name for g in goals],
                             "isabelle_ho_modal_theory")
    axioms = [HoAxiom(fact_name, fact) for fact_name, fact in facts] + list(axioms)
    # Identity is read ONCE, up front, as rigid HOL ``=`` (``≠`` -> ``¬(=)``, a
    # non-binary atom or a property-typed one refused by name) -- before the signature
    # analysis, so nothing downstream ever sees a ``≠``.
    formulas = _rigid_identity(
        [fact for _, fact in facts] + relativised, "isabelle_ho_modal_theory")
    apart, display = rename_apart(formulas)
    signatures = analyse_signatures(apart)
    # Arities come from the theory-wide analysis, not from each node's own
    # parse-time field: a binder whose arity only the OTHER axioms determine is
    # exactly the case a per-formula answer gets wrong.
    bound_arity = signatures.arity
    axiom_bodies = apart[:len(axioms)]
    typed_bodies = dict(zip((g.name for g in typed_goals), apart[len(axioms):]))
    usage = _scan_family_usage(apart)
    resolved_systems = _validate_systems(usage, systems)
    nominal_consts = sorted({_nominal_const(n.name) for f in apart for n in f.walk()
                            if isinstance(n, Nominal)})

    lines = [
        "(* Third-order modal logic in HOL: shallow (Benzmuller-style) embedding. *)",
        f"(* Frame: {frame}. Domain mode: {mode}. *)",
        f"theory {name}",
        "  imports Main",
        "begin",
        "",
        ho_modal_definitions(),
    ]
    extra_vocab = (_family_vocab_lines(usage) + _hybrid_vocab_lines(nominal_consts))
    if mode in _ACTUALIST_MODES and usage.has_quant:
        extra_vocab = _domain_vocab_lines() + extra_vocab
    if extra_vocab:
        lines.append("")
        lines += extra_vocab
    lines.append("")
    # The symbols of the formulas share one namespace with the vocabulary above (R, mall,
    # mnot, Rk, existsAt, nom_i, ...): none of them may take one of those names, and none
    # takes the name of another symbol, whatever its kind.
    fixed = declared_names([ho_modal_definitions()] + extra_vocab)
    symbols = IsabelleNames((fixed - declared_names(())) | ISABELLE_BUILT_IN
                            | set(_used_ordering(apart)))
    signature = _signature_lines(apart, signatures, symbols)
    frame_lines = _frame_axiom_lines(frame)
    frame_lines += _family_axiom_lines(usage, resolved_systems, temporal_closure)
    if mode in _ACTUALIST_MODES and usage.has_quant:
        frame_lines += _domain_axiom_lines(mode)
    if frame_lines:
        lines.append(f"\\<comment> \\<open>frame/domain conditions for {frame}/{mode}\\<close>")
        lines += frame_lines
        lines.append("")
    if signature:
        lines += signature
        lines.append("")
    if signatures.defaulted:
        pairs = ", ".join(f"{p}[{i}]" for p, i in sorted(signatures.defaulted))
        lines.append(
            f"\\<comment> \\<open>arity defaulted to 1 (nothing in the theory "
            f"fixes it): {pairs}\\<close>")
        lines.append("")
    lines += list(preamble)
    if preamble:
        lines.append("")

    # A binder shadows a constant of its own spelling inside its scope, and the lifted
    # operators (mand, mall, ...) are constants too: every binder (object quantifier, lambda
    # parameter, bound predicate variable) is printed under a name that nothing declared above
    # has. ``display`` gives each renamed-apart predicate variable that name.
    tokens = binder_tokens(collect_binders(formulas), declared_names(lines))
    display = {fresh: tokens[(PREDICATE, original)] for fresh, original in display.items()}
    scope = BinderScope(tokens)

    for axiom, renamed in zip(axioms, axiom_bodies):
        if axiom.comment:
            lines.append(f"\\<comment> \\<open>{axiom.comment}\\<close>")
        body = _isa_sigma(renamed, bound_arity, display, mode, scope, symbols)
        lines.append(f'axiomatization where {axiom.name}: "mvalid {body}"')
    if axioms:
        lines.append("")

    for goal in goals:
        if goal.comment:
            lines.append(f"\\<comment> \\<open>{goal.comment}\\<close>")
        if goal.statement is not None:
            proposition = goal.statement
        else:
            body = _isa_sigma(typed_bodies[goal.name], bound_arity, display, mode, scope, symbols)
            proposition = f"mvalid {body}"
        lines.append(f'{goal.kind} {goal.name}: "{proposition}"')
        lines.append(f"  {goal.proof}")
        lines.append("")

    lines.append("end")
    return "\n".join(lines) + "\n"


def to_isabelle_ho_modal(formula: Node, name: str = "HO_Modal_Goal",
                         frame: str = "K", proof: Optional[str] = None,
                         mode: str = "constant",
                         systems: Optional[dict] = None,
                         temporal_closure: bool = True) -> str:
    """Emit a theory whose single goal is ``formula``, valid on every world.

    The one-formula convenience over :func:`isabelle_ho_modal_theory`. Without a
    ``proof`` the goal is left ``oops`` — the kit states the problem, it does not
    invent a proof for it. ``mode``/``systems``/``temporal_closure`` pass
    through unchanged; see :func:`isabelle_ho_modal_theory`.
    """
    goal = HoGoal("goal", formula, proof or "oops")
    return isabelle_ho_modal_theory(name, (), (goal,), frame=frame, mode=mode,
                                    systems=systems,
                                    temporal_closure=temporal_closure)


# --------------------------------------------------------------------------
# THF
# --------------------------------------------------------------------------

_THF_PRELUDE = [
    "% Third-order modal logic in THF: shallow (Benzmuller-style) embedding.",
    "% mu = worlds; $i = individuals; (mu > $o) = propositions;",
    "% ($i > mu > $o) = properties; (($i > mu > $o) > mu > $o) = predicates of properties.",
    "thf(mu_type, type, ( mu : $tType )).",
    "thf(r_type, type, ( r : mu > mu > $o )).",
    "thf(mnot_type, type, ( mnot : ( mu > $o ) > mu > $o )).",
    "thf(mnot_def, definition, ( mnot = ( ^ [P: mu > $o, W: mu] : ( ~ ( P @ W ) ) ) )).",
    "thf(mand_type, type, ( mand : ( mu > $o ) > ( mu > $o ) > mu > $o )).",
    "thf(mand_def, definition, ( mand = ( ^ [P: mu > $o, Q: mu > $o, W: mu] : "
    "( ( P @ W ) & ( Q @ W ) ) ) )).",
    "thf(mor_type, type, ( mor : ( mu > $o ) > ( mu > $o ) > mu > $o )).",
    "thf(mor_def, definition, ( mor = ( ^ [P: mu > $o, Q: mu > $o, W: mu] : "
    "( ( P @ W ) | ( Q @ W ) ) ) )).",
    "thf(mimp_type, type, ( mimp : ( mu > $o ) > ( mu > $o ) > mu > $o )).",
    "thf(mimp_def, definition, ( mimp = ( ^ [P: mu > $o, Q: mu > $o, W: mu] : "
    "( ( P @ W ) => ( Q @ W ) ) ) )).",
    "thf(miff_type, type, ( miff : ( mu > $o ) > ( mu > $o ) > mu > $o )).",
    "thf(miff_def, definition, ( miff = ( ^ [P: mu > $o, Q: mu > $o, W: mu] : "
    "( ( P @ W ) <=> ( Q @ W ) ) ) )).",
    "thf(mbox_type, type, ( mbox : ( mu > $o ) > mu > $o )).",
    "thf(mbox_def, definition, ( mbox = ( ^ [P: mu > $o, W: mu] : "
    "( ! [V: mu] : ( ( r @ W @ V ) => ( P @ V ) ) ) ) )).",
    "thf(mdia_type, type, ( mdia : ( mu > $o ) > mu > $o )).",
    "thf(mdia_def, definition, ( mdia = ( ^ [P: mu > $o, W: mu] : "
    "( ? [V: mu] : ( ( r @ W @ V ) & ( P @ V ) ) ) ) )).",
    "thf(mvalid_type, type, ( mvalid : ( mu > $o ) > $o )).",
    "thf(mvalid_def, definition, ( mvalid = "
    "( ^ [P: mu > $o] : ( ! [W: mu] : ( P @ W ) ) ) )).",
]

_THF_FRAME = {
    "refl": "( ! [W: mu] : ( r @ W @ W ) )",
    "sym": "( ! [W: mu, V: mu] : ( ( r @ W @ V ) => ( r @ V @ W ) ) )",
    "trans": "( ! [W: mu, V: mu, U: mu] : ( ( ( r @ W @ V ) & ( r @ V @ U ) ) "
             "=> ( r @ W @ U ) ) )",
    "serial": "( ! [W: mu] : ( ? [V: mu] : ( r @ W @ V ) ) )",
    "eucl": "( ! [W: mu, V: mu, U: mu] : ( ( ( r @ W @ V ) & ( r @ W @ U ) ) "
            "=> ( r @ V @ U ) ) )",
    "directed": "( ! [W: mu, V: mu, U: mu] : ( ( ( r @ W @ V ) & ( r @ W @ U ) ) "
                "=> ( ? [Z: mu] : ( ( r @ V @ Z ) & ( r @ U @ Z ) ) ) ) )",
    "connected": "( ! [W: mu, V: mu, U: mu] : ( ( ( r @ W @ V ) & ( r @ W @ U ) ) "
                 "=> ( ( r @ V @ U ) | ( r @ U @ V ) ) ) )",
    "functional": "( ! [W: mu, V: mu, U: mu] : ( ( ( r @ W @ V ) & ( r @ W @ U ) ) "
                  "=> ( V = U ) ) )",
    "dense": "( ! [W: mu, V: mu] : ( ( r @ W @ V ) "
             "=> ( ? [U: mu] : ( ( r @ W @ U ) & ( r @ U @ V ) ) ) ) )",
    "shift_refl": "( ! [W: mu, V: mu] : ( ( r @ W @ V ) => ( r @ V @ V ) ) )",
    "empty": "( ! [W: mu, V: mu] : ( ~ ( r @ W @ V ) ) )",
    # Löb / McKinsey / Grz: schemas over propositions, with the schema
    # variable P bound explicitly by a THF `! [P: mu > $o]`, matching the
    # explicit `\<forall>P::sigma.` on the Isabelle side (see the comment above
    # _FRAME_AXIOMS). A user symbol named P is a constant spelled `p`, so it
    # cannot capture the binder.
    "loeb": "( ! [P: mu > $o] : ( ! [W: mu] : ( ( ! [V: mu] : ( ( r @ W @ V ) => "
            "( ( ! [U: mu] : ( ( r @ V @ U ) => ( P @ U ) ) ) => ( P @ V ) ) ) ) "
            "=> ( ! [V: mu] : ( ( r @ W @ V ) => ( P @ V ) ) ) ) ) )",
    "mckinsey": "( ! [P: mu > $o] : ( ! [W: mu] : ( ( ! [V: mu] : ( ( r @ W @ V ) => "
                "( ? [U: mu] : ( ( r @ V @ U ) & ( P @ U ) ) ) ) ) "
                "=> ( ? [V: mu] : ( ( r @ W @ V ) & ( ! [U: mu] : ( ( r @ V @ U ) "
                "=> ( P @ U ) ) ) ) ) ) ) )",
    "grz": "( ! [P: mu > $o] : ( ! [W: mu] : ( ( ! [V: mu] : ( ( r @ W @ V ) => "
           "( ( ! [U: mu] : ( ( r @ V @ U ) => ( ( P @ U ) => "
           "( ! [Z: mu] : ( ( r @ U @ Z ) => ( P @ Z ) ) ) ) ) ) => ( P @ V ) ) ) ) "
           "=> ( P @ W ) ) ) )",
}

# The extended vocabulary (epistemic/doxastic/assertive/bouletic, deontic,
# temporal, hybrid) -- unconditionally declared, matching thf_modal.py's own
# ``_THF_DEFS_FULL`` convention (a bridge/family whose relation is never used
# stays merely unconstrained, not absent; see that module's own comment on
# why "declared unconditionally" is the honest, THF-idiomatic choice) rather
# than this module's own conditional Isabelle side. ``existsAt``/``mforall``/
# ``mexists`` are the ONE exception (see _thf_domain_lines below): they stay
# conditional, so the DEFAULT constant-mode THF output is unchanged.
_THF_FAMILY_PRELUDE = [
    "thf(rk_type, type, ( rk : $i > mu > mu > $o )).",
    "thf(mknows_type, type, ( mknows : $i > ( mu > $o ) > mu > $o )).",
    "thf(mknows_def, definition, ( mknows = ( ^ [A: $i, P: mu > $o, W: mu] : "
    "( ! [V: mu] : ( ( rk @ A @ W @ V ) => ( P @ V ) ) ) ) )).",
    "thf(rb_type, type, ( rb : $i > mu > mu > $o )).",
    "thf(mbelieves_type, type, ( mbelieves : $i > ( mu > $o ) > mu > $o )).",
    "thf(mbelieves_def, definition, ( mbelieves = ( ^ [A: $i, P: mu > $o, W: mu] : "
    "( ! [V: mu] : ( ( rb @ A @ W @ V ) => ( P @ V ) ) ) ) )).",
    "thf(rs_type, type, ( rs : $i > mu > mu > $o )).",
    "thf(msays_type, type, ( msays : $i > ( mu > $o ) > mu > $o )).",
    "thf(msays_def, definition, ( msays = ( ^ [A: $i, P: mu > $o, W: mu] : "
    "( ! [V: mu] : ( ( rs @ A @ W @ V ) => ( P @ V ) ) ) ) )).",
    "thf(rw_type, type, ( rw : $i > mu > mu > $o )).",
    "thf(mwants_type, type, ( mwants : $i > ( mu > $o ) > mu > $o )).",
    "thf(mwants_def, definition, ( mwants = ( ^ [A: $i, P: mu > $o, W: mu] : "
    "( ! [V: mu] : ( ( rw @ A @ W @ V ) => ( P @ V ) ) ) ) )).",
    "thf(d_type, type, ( d : mu > mu > $o )).",
    "thf(mobl_type, type, ( mobl : ( mu > $o ) > mu > $o )).",
    "thf(mobl_def, definition, ( mobl = ( ^ [P: mu > $o, W: mu] : "
    "( ! [V: mu] : ( ( d @ W @ V ) => ( P @ V ) ) ) ) )).",
    "thf(mperm_type, type, ( mperm : ( mu > $o ) > mu > $o )).",
    "thf(mperm_def, definition, ( mperm = ( ^ [P: mu > $o, W: mu] : "
    "( ? [V: mu] : ( ( d @ W @ V ) & ( P @ V ) ) ) ) )).",
    "thf(t_type, type, ( t : mu > mu > $o )).",
    "thf(malways_type, type, ( malways : ( mu > $o ) > mu > $o )).",
    "thf(malways_def, definition, ( malways = ( ^ [P: mu > $o, W: mu] : "
    "( ! [V: mu] : ( ( t @ W @ V ) => ( P @ V ) ) ) ) )).",
    "thf(meventually_type, type, ( meventually : ( mu > $o ) > mu > $o )).",
    "thf(meventually_def, definition, ( meventually = ( ^ [P: mu > $o, W: mu] : "
    "( ? [V: mu] : ( ( t @ W @ V ) & ( P @ V ) ) ) ) )).",
    "thf(mhistorically_type, type, ( mhistorically : ( mu > $o ) > mu > $o )).",
    "thf(mhistorically_def, definition, ( mhistorically = ( ^ [P: mu > $o, W: mu] : "
    "( ! [V: mu] : ( ( t @ V @ W ) => ( P @ V ) ) ) ) )).",
    "thf(monce_type, type, ( monce : ( mu > $o ) > mu > $o )).",
    "thf(monce_def, definition, ( monce = ( ^ [P: mu > $o, W: mu] : "
    "( ? [V: mu] : ( ( t @ V @ W ) & ( P @ V ) ) ) ) )).",
    "thf(tnext_type, type, ( tnext : mu > mu > $o )).",
    "thf(mnext_type, type, ( mnext : ( mu > $o ) > mu > $o )).",
    "thf(mnext_def, definition, ( mnext = ( ^ [P: mu > $o, W: mu] : "
    "( ! [V: mu] : ( ( tnext @ W @ V ) => ( P @ V ) ) ) ) )).",
    "thf(mprevious_type, type, ( mprevious : ( mu > $o ) > mu > $o )).",
    "thf(mprevious_def, definition, ( mprevious = ( ^ [P: mu > $o, W: mu] : "
    "( ! [V: mu] : ( ( tnext @ V @ W ) => ( P @ V ) ) ) ) )).",
    "thf(muntil_type, type, ( muntil : ( mu > $o ) > ( mu > $o ) > mu > $o )).",
    "thf(muntil_def, definition, ( muntil = ( ^ [Phi: mu>$o, Psi: mu>$o, W: mu] : "
    "! [S: mu>$o] : ( ( ( ! [V: mu] : ( ( Psi @ V ) => ( S @ V ) ) ) & "
    "( ! [V: mu, U: mu] : ( ( ( Phi @ V ) & ( tnext @ V @ U ) & ( S @ U ) ) "
    "=> ( S @ V ) ) ) ) => ( S @ W ) ) ) )).",
    "thf(msince_type, type, ( msince : ( mu > $o ) > ( mu > $o ) > mu > $o )).",
    "thf(msince_def, definition, ( msince = ( ^ [Phi: mu>$o, Psi: mu>$o, W: mu] : "
    "! [S: mu>$o] : ( ( ( ! [V: mu] : ( ( Psi @ V ) => ( S @ V ) ) ) & "
    "( ! [V: mu, U: mu] : ( ( ( Phi @ V ) & ( tnext @ U @ V ) & ( S @ U ) ) "
    "=> ( S @ V ) ) ) ) => ( S @ W ) ) ) )).",
]

# Per-agent frame axioms for the four agent-indexed relations, keyed the same
# way as _ISA_AGENT_CONDS's Isabelle counterpart (ported from the same five
# Horn schemas thf_modal.py's own _agent_frame_axioms states in THF).
_THF_AGENT_CONDS = {
    "refl": "thf({tag}_refl, axiom, ( ! [A: $i, W: mu] : ( {rel} @ A @ W @ W ) )).",
    "trans": ("thf({tag}_trans, axiom, ( ! [A: $i, W: mu, V: mu, U: mu] : "
              "( ( ( {rel} @ A @ W @ V ) & ( {rel} @ A @ V @ U ) ) "
              "=> ( {rel} @ A @ W @ U ) ) ))."),
    "sym": ("thf({tag}_sym, axiom, ( ! [A: $i, W: mu, V: mu] : "
            "( ( {rel} @ A @ W @ V ) => ( {rel} @ A @ V @ W ) ) ))."),
    "serial": ("thf({tag}_serial, axiom, ( ! [A: $i, W: mu] : "
               "( ? [V: mu] : ( {rel} @ A @ W @ V ) ) ))."),
    "eucl": ("thf({tag}_eucl, axiom, ( ! [A: $i, W: mu, V: mu, U: mu] : "
             "( ( ( {rel} @ A @ W @ V ) & ( {rel} @ A @ W @ U ) ) "
             "=> ( {rel} @ A @ V @ U ) ) )).")
}

_THF_FAMILY_REL = {"epistemic": "rk", "doxastic": "rb",
                   "assertive": "rs", "bouletic": "rw"}


def _thf_agent_system_axioms(family: str, system: str) -> List[str]:
    """THF counterpart of :func:`_agent_system_axioms` -- same systems, same refusals."""
    if system not in FRAMES:
        raise ValueError(
            f"to_thf_ho_modal: unknown system {system!r} for {family} "
            f"(use one of {sorted(FRAMES)})."
        )
    conditions = resolve_frame(system)
    unsupported = [c for c in conditions if c not in _THF_AGENT_CONDS]
    if unsupported:
        raise NotImplementedError(
            f"to_thf_ho_modal: system {system!r} for {family} needs the frame "
            f"condition(s) {unsupported}, which have no per-agent axiom schema "
            f"here; use frame= on the alethic relation for those systems."
        )
    rel = _THF_FAMILY_REL[family]
    return [_THF_AGENT_CONDS[c].format(rel=rel, tag=rel) for c in conditions]


def _thf_family_axiom_lines(usage: "_FamilyUsage", systems: dict,
                            temporal_closure: bool) -> List[str]:
    """THF ``axiom`` lines for every family/system ``usage``/``systems`` need.

    Mirrors :func:`_family_axiom_lines`'s order and gating exactly, so the
    Isabelle and THF routes constrain the same relations under the same call.
    """
    lines: List[str] = []
    for family in sorted(systems):
        lines += _thf_agent_system_axioms(family, systems[family])
    if usage.deontic:
        lines.append("thf(d_serial, axiom, ( ! [W: mu] : ( ? [V: mu] : "
                     "( d @ W @ V ) ) )).")
    if usage.temporal and temporal_closure:
        lines += [
            "thf(t_refl, axiom, ( ! [W: mu] : ( t @ W @ W ) )).",
            "thf(t_trans, axiom, ( ! [W: mu, V: mu, U: mu] : "
            "( ( ( t @ W @ V ) & ( t @ V @ U ) ) => ( t @ W @ U ) ) )).",
        ]
    if usage.temporal and usage.needs_next_rel:
        lines.append("thf(tnext_in_t, axiom, ( ! [W: mu, V: mu] : "
                     "( ( tnext @ W @ V ) => ( t @ W @ V ) ) )).")
    return lines


def _thf_domain_lines() -> List[str]:
    """``existsAt`` typed, unconditionally -- the ONLY family piece kept
    conditional in this module's THF export (see the module docstring and
    _domain_vocab_lines's Isabelle counterpart): emitted only for an
    actualist ``mode=`` combined with an actual individual quantifier, so the
    default constant-mode THF problem is unchanged from before this port.
    """
    return ["thf(existsat_type, type, ( existsat : $i > mu > $o ))."]


def _thf_domain_axiom_lines(mode: str) -> List[str]:
    """THF counterpart of :func:`_domain_axiom_lines`, over the alethic ``r``."""
    out = ["thf(nonempty_dom, axiom, ( ! [W: mu] : "
          "( ? [X: $i] : ( existsat @ X @ W ) ) ))."]
    if mode in ("increasing", "cumulative"):
        out.append("thf(cumul_dom, axiom, ( ! [X: $i, W: mu, V: mu] : "
                   "( ( ( existsat @ X @ W ) & ( r @ W @ V ) ) "
                   "=> ( existsat @ X @ V ) ) )).")
    elif mode == "decreasing":
        out.append("thf(decr_dom, axiom, ( ! [X: $i, W: mu, V: mu] : "
                   "( ( ( existsat @ X @ V ) & ( r @ W @ V ) ) "
                   "=> ( existsat @ X @ W ) ) )).")
    return out


def _thf_type(kind) -> str:
    """Return the THF type of an argument slot: ``$i`` or a property type."""
    if kind == INDIVIDUAL:
        return "$i"
    return "( " + " > ".join(["$i"] * kind[1] + ["mu", "$o"]) + " )"


def _thf_arg(node: Node, upper: Dict[str, str], display: Dict[str, str],
             depth: int, names: ThfNames, mode: str) -> str:
    """Render an argument-position node in THF — an individual or a property.

    ``upper`` maps each source name bound in scope to its THF variable token;
    a variable that is not in it is free and spelled through ``names``. A constant
    is never looked up in ``upper``: no binder captures it, whatever its spelling.
    """
    if isinstance(node, (Variable, LambdaVar)):
        return upper.get(node.name) or names.functor(FREE_VARIABLE, node.name)
    if isinstance(node, Constant):
        return names.functor(CONSTANT, node.name)
    if isinstance(node, PredicateTerm):
        return upper.get(node.name) or names.functor("predicate", node.name)
    if isinstance(node, Lambda):
        params, body = peel_lambdas(node)
        fresh = dict(upper)
        for n in params:
            fresh[n] = bound_token(n, "_V", fresh)
        world = f"W{depth}"
        binders = ", ".join(f"{fresh[n]}: $i" for n in params)
        return (f"( ^ [{binders}, {world}: mu] : "
                f"( {_thf(body, fresh, display, depth + 1, names, mode)} @ {world} ) )")
    if isinstance(node, Function):
        functor = names.functor("function", node.name)
        args = " @ ".join(_thf_arg(a, upper, display, depth, names, mode)
                          for a in node.args)
        return f"( {functor} @ {args} )" if node.args else functor
    raise UnsupportedHigherOrderNode(
        f"ho_modal: {type(node).__name__} cannot stand in argument position.")


_BINARY_THF = {And: "mand", Or: "mor", Implies: "mimp", Iff: "miff"}

#: The embedding's own functors, pre-claimed so no user symbol can take them.
_THF_RESERVED = ("mu", "r", "mnot", "mand", "mor", "mimp", "miff", "mbox", "mdia",
                 "mvalid", "rk", "rb", "rs", "rw", "d", "t", "tnext",
                 "mknows", "mbelieves", "msays", "mwants", "mobl", "mperm",
                 "malways", "meventually", "mnext", "mhistorically", "monce",
                 "mprevious", "muntil", "msince",
                 "existsat", "mforall", "mexists", "feq", "fneq") + tuple(ORDERING.values())
# ``feq`` / ``fneq`` name nothing in this embedding any more (identity is rigid: the
# ``meq`` macro below, not an uninterpreted functor), but they stay claimed so a user
# predicate that sanitises onto one of them is still pushed to ``feq_2`` -- the same
# choice hol.thf_modal makes -- rather than reading as the old identity alias. ``meq``
# is claimed only when the problem contains identity (see to_thf_ho_modal), so an
# identity-free problem names its symbols exactly as before.

#: The identity macro (emitted only when a formula contains identity): the name and the
#: DEFINITION are hol.thf_modal's, verbatim -- ``meq = ^ [A: $i, B: $i, W: mu] : ( A = B )``,
#: THF's own ``=`` over the individual sort with a world binder the body never mentions
#: -- plus the type line every other macro of this prelude carries.
_THF_RIGID_EQ_LINES = [
    f"thf({_THF_RIGID_EQ}_type, type, ( {_THF_RIGID_EQ} : $i > $i > mu > $o )).",
    _THF_RIGID_EQ_DEF,
]

#: Refusal text for the counterfactuals, THF side (see the module docstring).
_NO_THF_COUNTERFACTUAL = (
    "to_thf_ho_modal: the counterfactuals □→/◇→ (Would/Might) "
    "read a similarity ordering of worlds (Lewis spheres), not an "
    "accessibility relation. Use hol.isabelle_conditional instead."
)

#: N1: ↓, THF side (see _NO_DOWN above for the Isabelle-side twin).
_NO_THF_DOWN = (
    "to_thf_ho_modal: the ↓ binder is not supported by this third-order THF "
    "embedding — H(@,↓) validity is undecidable. Use "
    "unicode_logic_kit.fol.modal_translation.down_is_valid (propositional "
    "H(@,↓), Z3, PROVED-only) or unicode_logic_kit.atp.kripke_enum.KripkeEnumBackend "
    "/ modal_enum_search (bounded search, REFUTED-only) instead."
)


def _thf(node: Node, upper: Dict[str, str], display: Dict[str, str],
         depth: int, names: ThfNames, mode: str) -> str:
    """Render ``node`` as a THF term of type ``mu > $o``.

    ``depth`` numbers the world binders this rendering introduces (``W0``,
    ``W1``, …). Shadowing would be sound — each application picks up its own
    innermost binder — but a distinct name per level is what makes the emitted
    problem readable, and readable is what gets a mis-embedding noticed. User
    variable tokens always carry a ``_V``/``_P`` suffix, so they never meet a
    world binder.
    """
    if isinstance(node, Not):
        return f"( mnot @ {_thf(node.formula, upper, display, depth, names, mode)} )"
    op = _BINARY_THF.get(type(node))
    if op is not None:
        left = _thf(node.left, upper, display, depth, names, mode)
        right = _thf(node.right, upper, display, depth, names, mode)
        return f"( {op} @ {left} @ {right} )"
    if isinstance(node, Box):
        return f"( mbox @ {_thf(node.formula, upper, display, depth, names, mode)} )"
    if isinstance(node, Diamond):
        return f"( mdia @ {_thf(node.formula, upper, display, depth, names, mode)} )"
    if isinstance(node, Quantifier):
        var = bound_token(node.variable.name, "_V", upper)
        fresh = dict(upper, **{node.variable.name: var})
        quant = "!" if node.type == "∀" else "?"
        world = f"W{depth}"
        body = f"( {_thf(node.formula, fresh, display, depth + 1, names, mode)} @ {world} )"
        if mode in _ACTUALIST_MODES:
            # The individual binder becomes existsAt-guarded; a property
            # binder (below) never is -- the one judgment call this port
            # makes, see the module docstring.
            guard = f"( existsat @ {var} @ {world} )"
            connective = "=>" if quant == "!" else "&"
            inner = f"( {quant} [{var}: $i] : ( {guard} {connective} {body} ) )"
        else:
            inner = f"( {quant} [{var}: $i] : {body} )"
        return f"( ^ [{world}: mu] : {inner} )"
    if isinstance(node, SecondOrderQuantifier):
        var = bound_token(display.get(node.predicate, node.predicate), "_P", upper)
        fresh = dict(upper, **{node.predicate: var})
        quant = "!" if node.type == "∀" else "?"
        ptype = " > ".join(["$i"] * node.arity + ["mu", "$o"])
        world = f"W{depth}"
        return (f"( ^ [{world}: mu] : ( {quant} [{var}: {ptype}] : "
                f"( {_thf(node.formula, fresh, display, depth + 1, names, mode)} @ {world} ) ) )")
    if isinstance(node, (Knows, Believes, Says, Wants)):
        macro = {Knows: "mknows", Believes: "mbelieves",
                Says: "msays", Wants: "mwants"}[type(node)]
        agent = _thf_arg(node.agent, upper, display, depth, names, mode)
        body = _thf(node.formula, upper, display, depth, names, mode)
        return f"( {macro} @ {agent} @ {body} )"
    if isinstance(node, Obligatory):
        return f"( mobl @ {_thf(node.formula, upper, display, depth, names, mode)} )"
    if isinstance(node, Permitted):
        return f"( mperm @ {_thf(node.formula, upper, display, depth, names, mode)} )"
    if isinstance(node, Always):
        return f"( malways @ {_thf(node.formula, upper, display, depth, names, mode)} )"
    if isinstance(node, Eventually):
        return f"( meventually @ {_thf(node.formula, upper, display, depth, names, mode)} )"
    if isinstance(node, Next):
        return f"( mnext @ {_thf(node.formula, upper, display, depth, names, mode)} )"
    if isinstance(node, Historically):
        return f"( mhistorically @ {_thf(node.formula, upper, display, depth, names, mode)} )"
    if isinstance(node, Once):
        return f"( monce @ {_thf(node.formula, upper, display, depth, names, mode)} )"
    if isinstance(node, Previous):
        return f"( mprevious @ {_thf(node.formula, upper, display, depth, names, mode)} )"
    if isinstance(node, Until):
        left = _thf(node.left, upper, display, depth, names, mode)
        right = _thf(node.right, upper, display, depth, names, mode)
        return f"( muntil @ {left} @ {right} )"
    if isinstance(node, Since):
        left = _thf(node.left, upper, display, depth, names, mode)
        right = _thf(node.right, upper, display, depth, names, mode)
        return f"( msince @ {left} @ {right} )"
    if isinstance(node, Nominal):
        return f"( ^ [W: mu] : ( W = {names.functor('nominal', node.name)} ) )"
    if isinstance(node, At):
        body = _thf(node.formula, upper, display, depth, names, mode)
        return f"( ^ [W: mu] : ( {body} @ {names.functor('nominal', node.nominal.name)} ) )"
    if isinstance(node, Down):
        raise UnsupportedHigherOrderNode(_NO_THF_DOWN)
    if isinstance(node, Atom):
        constant = truth_value(node)
        if constant is not None:
            # `$true` / `$false`: the proposition true (false) at every world.
            return "( ^ [W: mu] : $true )" if constant else "( ^ [W: mu] : $false )"
        if is_equality_atom(node):
            _identity_sides(node)
            name = _THF_RIGID_EQ
        elif node.predicate in ORDERING:
            name = ORDERING[node.predicate]
        else:
            name = upper.get(node.predicate) or names.functor("predicate", node.predicate)
        if not node.args:
            return name
        args = " @ ".join(_thf_arg(a, upper, display, depth, names, mode)
                          for a in node.args)
        return f"( {name} @ {args} )"
    if type(node).__name__ in ("Would", "Might"):
        raise UnsupportedHigherOrderNode(_NO_THF_COUNTERFACTUAL)
    raise UnsupportedHigherOrderNode(
        f"ho_modal: no THF reading for {type(node).__name__}; this embedding "
        f"covers alethic, agent-indexed epistemic/doxastic/assertive/bouletic, "
        f"deontic, temporal and hybrid families over third-order syntax -- not "
        f"the Lewis counterfactuals or the group-epistemic operators.")


def to_thf_ho_modal(formula: Node, frame: str = "K",
                    axioms: Sequence[HoAxiom] = (), mode: str = "constant",
                    systems: Optional[dict] = None,
                    temporal_closure: bool = True) -> str:
    """Emit a THF (TH0) problem: ``axioms`` as hypotheses, ``formula`` as the conjecture.

    The THF counterpart of :func:`isabelle_ho_modal_theory`, for a higher-order
    ATP (Leo-III, Satallax) rather than Isabelle. Same embedding, same fragment,
    same refusals, same ``mode=``/``systems=``/``temporal_closure=`` meaning;
    the toolkit emits the problem and does not run a prover.

    Identity ``=`` / ``≠`` between individuals is the rigid ``meq`` macro (HOL's own ``=``,
    no world argument; ``≠`` is ``¬(=)``), emitted only when a formula contains identity;
    a non-binary atom raises ``ValueError`` and identity between PROPERTIES raises
    ``NotImplementedError`` — see the module docstring's "Equality is rigid, or refused".
    """
    if frame not in FRAMES:
        raise ValueError(f"to_thf_ho_modal: unknown frame {frame!r}.")
    if mode not in _ACTUALIST_MODES and mode not in _CONSTANT_MODES:
        raise ValueError(
            f"to_thf_ho_modal: unknown mode {mode!r} "
            f"(use one of {sorted(_ACTUALIST_MODES | _CONSTANT_MODES)})."
        )
    # Sorts as in isabelle_ho_modal_theory: the facts about them are axioms of the problem.
    facts, relativised = sorted_reading(
        [a.formula for a in axioms] + [formula], "to_thf_ho_modal")
    _refuse_a_sort_fact_name(facts, [a.name for a in axioms], "to_thf_ho_modal")
    axioms = [HoAxiom(fact_name, fact) for fact_name, fact in facts] + list(axioms)
    # Identity is read ONCE, up front, as rigid ``=`` (see _rigid_identity).
    formulas = _rigid_identity([fact for _, fact in facts] + relativised, "to_thf_ho_modal")
    apart, display = rename_apart(formulas)
    signatures = analyse_signatures(apart)
    bound = set()
    for f in apart:
        bound |= bound_pred_names(f)
    usage = _scan_family_usage(apart)
    resolved_systems = _validate_systems(usage, systems, caller="to_thf_ho_modal")

    identity = any(_has_identity(f) for f in apart)
    names = ThfNames(reserved=_THF_RESERVED + ((_THF_RIGID_EQ,) if identity else ()))
    lines = list(_THF_PRELUDE) + list(_THF_FAMILY_PRELUDE)
    if identity:
        lines += _THF_RIGID_EQ_LINES
    if mode in _ACTUALIST_MODES and usage.has_quant:
        lines += _thf_domain_lines()
    for pred in sorted(signatures.slots):
        if pred in bound or pred in EQUALITY_PREDICATES or pred in ORDERING:
            continue
        parts = [_thf_type(k) for k in signatures.slots[pred]]
        thf_type = " > ".join(parts + ["mu", "$o"]) if parts else "mu > $o"
        functor = names.functor("predicate", pred)
        lines.append(f"thf({functor}_type, type, ( {functor} : {thf_type} )).")
    for kind, name in individual_symbols(apart):
        functor = names.functor(kind, name)
        lines.append(f"thf({functor}_type, type, ( {functor} : $i )).")
    # An ordering atom is a world-dependent uninterpreted relation here, as in qml.
    # Identity is not: it is the ``meq`` macro above, declared nowhere else.
    for symbol in sorted({ORDERING[p] for f in apart for p in atom_predicates(f)
                          if p in ORDERING}):
        lines.append(f"thf({symbol}_type, type, ( {symbol} : $i > $i > mu > $o )).")
    for name, arity in sorted(function_symbols(apart).items()):
        functor = names.functor("function", name)
        ftype = " > ".join(["$i"] * (arity + 1))
        lines.append(f"thf({functor}_type, type, ( {functor} : {ftype} )).")
    # Hybrid nominals: one `mu`-typed constant per distinct nominal NAME across
    # the whole problem, declared up front (like every other free symbol) so
    # every later reference -- in an axiom or in the goal -- resolves to the
    # SAME world constant.
    nominal_names = sorted({n.name for f in apart for n in f.walk()
                            if isinstance(n, Nominal)})
    for name in nominal_names:
        functor = names.functor("nominal", name)
        lines.append(f"thf({functor}_type, type, ( {functor} : mu )).")

    for condition in resolve_frame(frame):
        if condition not in _THF_FRAME:
            raise UnsupportedFrameCondition(
                f"to_thf_ho_modal: frame condition {condition!r} (system "
                f"{frame!r}) has no axiom registered in this embedding's "
                f"_THF_FRAME.")
        lines.append(f"thf(frame_{condition}, axiom, {_THF_FRAME[condition]}).")
    lines += _thf_family_axiom_lines(usage, resolved_systems, temporal_closure)
    if mode in _ACTUALIST_MODES and usage.has_quant:
        lines += _thf_domain_axiom_lines(mode)

    # Annotated-formula names share one namespace; an axiom called "A1" is not
    # a lower word, and one called "goal" or "mu_type" would clash.
    for line in lines:
        if line.startswith("thf("):
            names.unit(line[4:line.index(",")])
    for axiom, renamed in zip(axioms, apart):
        lines.append(f"thf({names.unit(axiom.name)}, axiom, ( mvalid @ "
                     f"{_thf(renamed, {}, display, 0, names, mode)} )).")
    goal = names.unit("goal")
    lines.append(f"thf({goal}, conjecture, "
                 f"( mvalid @ {_thf(apart[-1], {}, display, 0, names, mode)} )).")
    return "\n".join(lines) + "\n"
