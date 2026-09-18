"""Export to TPTP's Non-Classical Logic dialect (NXF) for the mono-modal alethic fragment,
now including its native QUANTIFIED sub-fragment.

TPTP's *classical* ``fof``/``tff`` syntax (:meth:`Node.to_tptp`) has no way to say
"this problem is modal" — a non-classical prover needs a companion **logic
specification** naming the logic and its parameters, plus new connective syntax
for the modal operators themselves. That companion dialect is **NXF**
("Non-Classical TFF"), defined by Steen & Sutcliffe's TPTP-World infrastructure
for non-classical logics. This module renders one Unicode-kit modal formula as a
complete, self-contained NXF problem: a ``logic`` role statement, one type
declaration per sort/constant/predicate the formula actually uses, and a
``conjecture`` role statement.

Sources (verified against primary/gold material BEFORE writing a line of this
module — see the individual choices below for what each one settled):

* Steen & Sutcliffe, "TPTP World Infrastructure for Non-classical Logics"
  (arXiv:2508.09318, fetched 2026-08-12, re-fetched and cross-checked against
  real ``.p`` files 2026-09-18 — see the correction note below) — the
  logic-specification shape ``tff(name, logic, $modal == [ $domains == ...,
  $designation == ..., $terms == ..., $modalities == ... ] ).`` with those
  four EXACT key names; the long-form connective application
  ``{connective_name} @ (arg1, ..., argn)`` (so ``{$box} @ (p)`` / ``{$dia} @
  (p)``); the SHORT forms for the unparameterised unary modal connectives,
  ``[.]`` for box and ``<.>`` for diamond, used exactly like a classical
  prefix connective; and Table 2's ``$modal_system_X`` literal-token list.
* ``github.com/TPTPWorld/NonClassicalLogic`` (cloned locally 2026-09-18 to
  read full, real, prover-exercised ``.p`` files rather than a paper's
  abbreviated excerpts — every claim below was checked against this clone,
  not assumed from the paper alone):
    - ``LogicSpecifications/CorrectSpecifications.p`` — confirms the four-key
      logic-spec form is accepted verbatim (``$domains == $constant,
      $designation == $rigid, $terms == $local/$global, $modalities ==
      $modal_system_S5``), and that ``$modal_system_S5`` / ``$modal_axiom_K``
      / ``$modal_axiom_T`` / ``$modal_axiom_5`` are literal system/axiom
      names.
    - ``ProblemBuilding/Archive/ClaudiaNalon/IJCAR2022-TPTP/k45_branch_p/
      k45_branch_p.0001.p`` (a real K45 benchmark, i.e. actually fed to
      provers) — the model this module follows for the PROPOSITIONAL modal
      fragment: ``tff(name,logic, $modal == [ $modalities ==
      $modal_system_K45 ] ).`` (``$domains``/``$designation``/``$terms``
      omitted — moot with no quantifiers/individual terms present), one
      ``tff(<p>_decl,type,<p>: $o).`` per propositional letter, and the
      short-form connectives used as plain prefix operators (``[.] z100``,
      ``<.> [.] y100`` chained with no parens between them) — i.e.
      ``[.]``/``<.>`` sit in the grammar at exactly the same position ``~``
      does (see :mod:`fol.tptp_input`'s ``?unary: "~" unary | ...`` rule).
    - ``ProblemBuilding/QMLTP/7_QMLTPTP/SYM/SYM001_1.p`` — a GENUINE,
      QMLTP-sourced NXF translation of the Barcan-scheme problem this
      module's own test suite uses as a fixture, confirming the NATIVE
      quantified syntax this release adds: ``! [X: $i] : ( {$box} @ (f(X)) )
      => ( {$box} @ (! [X: $i] : f(X)) )`` — a bound variable with NO
      explicit sort defaults to TPTP's BUILT-IN ``$i`` (never a user-declared
      ``$tType``), and a non-nullary predicate gets its own
      ``tff(f_decl,type, f: $i > $o ).`` declaration, confirming NXF/NTF
      stays a genuinely TYPED (TFF-based) dialect even for a
      previously-untyped-looking QMLTP source.
    - ``ProblemBuilding/QMLTP/7_QMLTPTP/APM/APM002_1.p`` — confirms (a) a
      FREE constant of the default sort still needs its own explicit
      declaration (``tff(a_decl,type, a: $i ).`` for a bare constant ``a``,
      not merely left implicit), and (b) ``$modal_system_D`` is the literal
      token for the serial (D/KD) system — the exact evidence this release's
      ``"D"`` addition (see below) is built on.
    - ``Logics/LOG001_4.l`` — the corpus's OWN canonical modal-system-name
      DEFINITIONS file (TPTP v9.0.0): ``tff(modal_system_T,definition, (
      $modal_system_T == ( $modal_system_K & $modal_axiom_T ) ) ).`` --
      confirming ``$modal_system_T`` (not ``$modal_system_M``) is the
      correct, canonical token for the reflexive ("T") frame. No
      ``modal_system_M`` definition exists anywhere in this file or the rest
      of the corpus (checked directly, see below) -- ``$modal_system_M``
      appears only as a USAGE, and only inside
      ``ProblemBuilding/QMLTP/8_QMLTP``, which
      ``ProblemBuilding/QMLTP/README`` itself describes as "expanded
      versions of 7_QMLTP with all combinations of the specification
      parameters" (a derived/generated subtree, not the corpus's canonical
      naming source) -- so those files reference a token this same corpus
      never defines, almost certainly a generator artefact rather than a
      legitimate alternate spelling. ``Tooling/generateSemantics.py`` (the
      corpus's own canonical semantics-specification generator) confirms the
      same thing independently: its ``all_modalities`` tuple is exactly
      ``("$modal_system_K", "$modal_system_T", "$modal_system_D",
      "$modal_system_S4", "$modal_system_S5")`` -- five names, matching this
      exporter's five supported frames one-to-one, with ``$modal_system_M``
      absent. ``ProblemBuilding/QMLTP/SemanticSpecifications/t_*.p`` (all
      eight ``t_<domain>_<designation>.p`` files) likewise all read
      ``$modalities == $modal_system_T``. A prior revision of this module
      briefly "corrected" this token to ``$modal_system_M`` on the strength
      of ``ProblemBuilding/Archive/.../kt_branch_p.0001.p`` and
      ``ProblemBuilding/QMLTP/8_QMLTP/SYM/SYM074_3.121.p`` alone, and a
      docstring claim that a corpus-wide search for ``modal_system_T``
      returned zero hits; that search was not actually re-run against the
      real corpus before being written -- ``modal_system_T`` in fact appears
      in dozens of files including the three canonical sources named above.
      That revision was wrong and is reverted here (adversarial review); the
      accompanying golden test is corrected back to match (see
      ``tests/test_tptp_ncl.py``).
    - ``SampleProblems/PUZ087_1.p`` — a ``$epistemic_modal`` problem using the
      INDEXED long form ``{$knows(#agent)} @ (...)``, confirming that a
      future INDEXED multi-modal export (Knows/Believes/agent-indexed
      alethic box(i)/dia(i)/... — still explicitly out of scope here, see
      "Scope" below) would need the long, not short, connective form. Also
      re-confirms the ``$tType``-declared-sort pattern
      (``tff(agent_type,type,wiseman: $tType).``) this release's
      :class:`~fol.nodes.SortedQuantifier`/:class:`~fol.nodes.SortedConstant`
      support follows.
* ``fol/_modal_nodes.py`` — confirms ``Box``/``Diamond`` (and every other
  modal-family node) reject the classical ``to_tptp()`` outright, so this
  module cannot delegate to ``Node.to_tptp`` for a formula containing one and
  must render the propositional connectives itself (mirroring their existing
  ``to_tptp`` shape exactly — see :func:`_render`).
* ``fol/tptp_input.py`` / ``fol/_fol_nodes.py`` — the kit's existing name
  convention (predicate/constant/function names lower-cased on their first
  letter only, a 0-ary atom is a bare lower-case identifier) is reused
  verbatim via ``Node.to_tptp()`` for every propositional letter, term and
  non-nullary atom, rather than re-implementing it here — this release's
  quantified-fragment additions extend that same reuse to
  :class:`~fol.nodes.Quantifier`/``SortedQuantifier``/``SortedConstant``
  arguments (see :func:`_render` / :func:`_term_sort`).

Scope — deliberately narrow, and narrowed FURTHER than a "cover everything"
reading of the sources above once each fragment was checked against real,
prover-exercised files rather than guessed from the paper's grammar alone:

* Supported: :class:`~fol.nodes.Box`, :class:`~fol.nodes.Diamond`,
  :class:`~fol.nodes.Not`, :class:`~fol.nodes.And`, :class:`~fol.nodes.Or`,
  :class:`~fol.nodes.Implies`, :class:`~fol.nodes.Iff`, over an
  :class:`~fol.nodes.Atom` of ANY arity (0-ary propositional letters, and
  now non-nullary ``P(x, y, ...)`` atoms too, PLUS equality/disequality —
  see below) whose arguments are :class:`~fol.nodes.Variable` (bound by a
  :class:`~fol.nodes.Quantifier` / ``SortedQuantifier`` — this module
  renders NATIVE NXF quantifiers, ``! [X: <sort>] : (...)`` / ``? [X:
  <sort>] : (...)``, per ``SYM001_1.p``/PUZ087_1.p above), or
  :class:`~fol.nodes.Constant` / :class:`~fol.nodes.SortedConstant` (each
  free constant gets its own ``tff(<name>_decl,type, <name>: <sort> ).``,
  per ``APM002_1.p`` above) — the mono-modal ALETHIC fragment (the frame
  system is K/T/S4/S5/D; no other modal family). An equality/disequality
  atom (``=``/``≠``) is accepted ONLY when both operands compute to the
  SAME NXF sort token — see the next bullet for why.
* NOT supported, each raising :class:`NotImplementedError` with a message
  naming the reason (never a silently weaker translation):
    - A free (unbound) :class:`~fol.nodes.Variable` — an Atom/equality
      argument naming a variable with no enclosing
      :class:`~fol.nodes.Quantifier` / ``SortedQuantifier`` (found by
      adversarial review) is refused rather than defaulted to ``$i``: TPTP
      reads a free variable in a ``conjecture`` role as EXISTENTIALLY
      quantified, not universally, so silently typing it would silently
      change the meaning of the exported problem, not merely under-specify
      its sort (see :data:`_UNSUPPORTED_FREE_VARIABLE`).
    - :class:`~fol.nodes.Function` arguments (``P(f(x))``) — a genuine
      function SYMBOL's own NXF type declaration
      (``<name>: (<arg-sorts>) > <result-sort>``) was never found in any
      real file of the cloned corpus (every QMLTP-derived problem checked
      uses only 0-ary/N-ary PREDICATES and free CONSTANTS, never a compound
      function term), so its exact shape is inferred-by-grammar-pattern
      only, not confirmed — refused by name rather than emitted unverified,
      pending a primary-source example.
    - A cross-sort equality/disequality atom (found by adversarial review):
      the kit's own SortedQuantifier/SortedConstant semantics is
      guard-predicate based (one shared classical domain, a sort is just a
      unary predicate over it — see ``fol._msfl_nodes.SortedQuantifier.
      _relativize``), so a cross-sort equality is perfectly meaningful
      there, but native TFF/NXF sorts are disjoint and TFF's polymorphic
      ``=`` requires both operands to share ONE declared type, with no
      subtyping/coercion — emitting one anyway would be TYPE-INCORRECT NXF/
      TFF text, not merely a false formula, so it is refused rather than
      silently emitted (see :data:`_UNSUPPORTED_CROSS_SORT_EQUALITY`).
    - The arithmetic comparison predicates (``<``/``>``/``≤``/``≥``) and a
      bare :class:`~fol.nodes.Number` literal anywhere in the formula
      (found by adversarial review) — both need one of TPTP's arithmetic
      sorts (``$int``/``$rat``/``$real``), which this exporter never
      declares; defaulting a ``Number`` to ``$i`` (the previous behaviour)
      or applying ``$less``/``$greater``/... to ``$i``-typed operands would
      likewise be type-incorrect NXF/TFF text. Mirrors
      :mod:`atp.tptp_tff`'s identical TF0-only refusal of the same two
      constructs (see that module's ``_ARITH_OUT_OF_SCOPE``) rather than
      inventing a new policy here.
    - Every other modal family (epistemic ``Knows``/``Believes``, doxastic,
      temporal, deontic, counterfactual, PAL) and INDEXED multi-modal
      (agent-/index-indexed box(i)/dia(i)) — each needs the INDEXED
      long-form connective (PUZ087_1.p's ``{{$knows(#a)}} @ (...)``, or the
      generic ``{{$box(#i)}} @ (...)`` form the arXiv paper's Section 2/5
      describe for FOMML) and the corresponding multi-entry
      ``$modalities`` logic-spec list — real examples of the latter show at
      least two non-equivalent accepted spellings for the per-index key
      (``[#a] == system`` in ``CorrectSpecifications.p`` vs.
      ``{{$necessary(#a)}} == system`` in the same file), which is not
      settled precisely enough to commit to one shape here; a follow-up, not
      guessed.
    - Any frame other than K/T/S4/S5/D (:class:`ValueError`, not
      ``NotImplementedError`` — this is a caller input error, not a missing
      feature: these are exactly the frames the rest of this kit's modal
      backends already know how to reason about, K/T/S4/S5 via
      :func:`modal_prove` and D via :func:`~fol.qml.qml_is_valid`'s
      ``frame="D"``/``"KD"``).
"""

from typing import Dict, List, Tuple

from ..fol.nodes import (
    Atom, And, Box, Constant, Diamond, Function, Iff, Implies, Node, Not,
    Number, Or, Quantifier, SortedConstant, SortedQuantifier, Variable,
)
from ..fol._fol_nodes import tptp_fold_first_letter

__all__ = ["to_tptp_ncl"]

# The frame names this kit's OWN modal routes already reason about (K/T/S4/S5
# via atp.modal_tableau, D via fol.qml.qml_is_valid(frame="D"/"KD")) map onto
# the literal $modal_system_<X> tokens — each individually confirmed against
# the corpus's OWN canonical sources (Logics/LOG001_4.l's definitions,
# Tooling/generateSemantics.py's all_modalities tuple, and
# ProblemBuilding/QMLTP/SemanticSpecifications/t_*.p), not merely some
# prover-exercised .p file from github.com/TPTPWorld/NonClassicalLogic (see
# the module docstring's "Sources" section for exactly which file proves
# which token).
_FRAME_TO_SYSTEM: Dict[str, str] = {
    "K": "$modal_system_K",
    "T": "$modal_system_T",
    "S4": "$modal_system_S4",
    "S5": "$modal_system_S5",
    # D (serial K, a.k.a. KD) -- the alethic SERIALITY axiom ∀w∃v R(w,v),
    # confirmed as $modal_system_D by APM002_1.p / kd_branch_p/*.p in the
    # cloned corpus (see module docstring). NOT to be confused with
    # fol.qml's *deontic* accessibility relation also spelled "D" (qml.py's
    # _R_DEONTIC): that is a wholly different relation this exporter never
    # touches -- this "D" names the ALETHIC frame's seriality condition,
    # the same one fol.qml.qml_is_valid(frame="D") / frame="KD" already
    # reasons about for □/◇.
    "D": "$modal_system_D",
}

# $domains values, confirmed by CorrectSpecifications.p's $domains ==
# $constant / [$constant, plushie == $varying] examples and the arXiv
# infrastructure paper's Table 1 enumeration of
# $constant/$varying/$cumulative/$decreasing. Only the bare (non-per-type)
# form is exposed here — a per-type domain list is a further extension this
# module does not implement.
#
# What changing this value DOES and does NOT do to the emitted problem, now
# that native quantifiers exist (this release): NOTHING changes in how a
# Quantifier/SortedQuantifier is RENDERED -- every value renders the exact
# same native ``! [X: <sort>] : (...)`` / ``? [X: <sort>] : (...)`` form,
# with no kit-side existence-guard atom of any kind. That is deliberate, not
# an oversight: NXF's $domains property is read by the CONSUMING PROVER to
# constrain how per-world domains relate to each other (SYM001_1.p's own
# $domains == $constant is exactly what makes its Barcan-scheme conjecture a
# Theorem for that prover) -- it is declarative logic-specification
# metadata, not a term-level transformation this exporter would have to
# perform itself. This is why :func:`to_tptp_ncl` does NOT reuse
# :func:`fol.qml.qml_translate` (which DOES perform such a transformation,
# via an explicit existence predicate E(x,w), for its own DIFFERENT
# technique: a shallow embedding into CLASSICAL logic decided by Z3, not a
# native non-classical export at all) -- the two routes solve the domain
# regime in different places on purpose, and conflating them would either
# double-guard the quantifiers (wrong syntax for NXF, which expects native
# ``!``/``?``) or silently drop the qml.py guard machinery's own soundness
# story. So every one of the four values is equally "wired": each selects
# a distinct token in the emitted ``$domains == ...`` line, which is the
# ONLY place this parameter has any effect.
_DOMAIN_WORDS: Dict[str, str] = {
    "constant": "$constant",
    "varying": "$varying",
    "cumulative": "$cumulative",
    "decreasing": "$decreasing",
}

# TPTP's built-in "individual" type -- always available, never separately
# declared, and non-empty BY TPTP SEMANTICS (the TF0/TFF standard fixes $i to
# denote a single non-empty domain of individuals; see the TPTP syntax BNF
# cited in fol/tptp_input.py's own docstring). An untyped Quantifier / a bare
# Constant defaults to this sort -- confirmed by SYM001_1.p's ``! [X: $i]``
# and APM002_1.p's ``a: $i`` (see module docstring). A user-declared sort
# (SortedQuantifier / SortedConstant) instead gets its own
# ``tff(<name>_type,type, <name>: $tType ).`` declaration -- and a $tType
# declaration is ITSELF non-empty by the same TPTP semantics (a $tType is a
# non-empty domain by definition; TPTP has no notion of an empty type), so
# this exporter never needs -- and does not emit -- a separate
# "sort S is non-empty" axiom the way fol.qml.qml_axioms's
# nonempty_sort_axioms does for the classical/shallow-embedding routes: the
# TYPED DECLARATION ITSELF already carries that guarantee for any consumer
# that honours TF0/TFF semantics.
_DEFAULT_SORT = "$i"

_UNSUPPORTED_FUNCTION = (
    "to_tptp_ncl: a compound function term {name!r}(...) is outside this "
    "exporter's supported fragment -- a genuine NXF function-SYMBOL type "
    "declaration (as opposed to a predicate's) was never found in any real "
    "problem of the checked github.com/TPTPWorld/NonClassicalLogic corpus, "
    "so its exact shape is not confirmed (see module docstring 'Scope'); "
    "refusing rather than emitting an unverified declaration. Only "
    "Variable/Constant/SortedConstant terms are supported as atom arguments "
    "in this release."
)

_UNSUPPORTED_NUMBER = (
    "to_tptp_ncl: a bare numeral literal ({value!r}) is outside this "
    "exporter's supported fragment -- TPTP types a numeral intrinsically as "
    "an arithmetic sort ($int/$rat/$real), never as the individual sort $i "
    "(or a user sort) this exporter's quantifiers/constants use, and this "
    "exporter never declares an arithmetic sort (mirrors atp.tptp_tff's "
    "identical TF0-only refusal for a Number term -- see that module's "
    "docstring 'Scope: TF0 only'); refusing rather than mistyping the "
    "literal as $i. Only Variable/Constant/SortedConstant terms are "
    "supported as atom arguments in this release."
)

_UNSUPPORTED_FREE_VARIABLE = (
    "to_tptp_ncl: variable {name!r} is not bound by an enclosing Quantifier/"
    "SortedQuantifier (found by adversarial review) -- refusing rather than "
    "defaulting it to $i, because an emitted NXF conjecture with a genuinely "
    "free variable is not equivalent to the source formula: TPTP treats a "
    "free variable in a conjecture role as EXISTENTIALLY quantified, not "
    "universally, which silently changes the meaning of the exported "
    "problem rather than merely defaulting its sort. Bind every variable "
    "with a Quantifier/SortedQuantifier before calling to_tptp_ncl."
)

_UNSUPPORTED_ARITHMETIC_PRED = (
    "to_tptp_ncl: the arithmetic comparison {name!r} is outside this "
    "exporter's supported fragment -- it needs TPTP's arithmetic sorts "
    "($int/$rat/$real), which this exporter never declares (mirrors "
    "atp.tptp_tff's identical TF0-only refusal of the same predicate -- see "
    "that module's docstring 'Scope: TF0 only'); refusing rather than "
    "emitting a $less/$greater/$lesseq/$greatereq atom whose operands are "
    "typed $i (or a user sort) instead of an arithmetic sort."
)

_UNSUPPORTED_CROSS_SORT_EQUALITY = (
    "to_tptp_ncl: an equality/disequality atom ({pred!r}) between an "
    "operand of sort {left!r} and one of sort {right!r} is outside this "
    "exporter's supported fragment -- the kit's own SortedQuantifier/"
    "SortedConstant semantics is guard-predicate based (S(x) is a unary "
    "predicate over one shared classical domain, so cross-sort equality is "
    "meaningful there -- see fol._msfl_nodes.SortedQuantifier._relativize), "
    "but native TFF/NXF types are disjoint and TFF's polymorphic '=' "
    "requires both operands to share the SAME declared type, with no "
    "subtyping/coercion; refusing rather than emitting a type-incorrect "
    "NXF/TFF problem. Give both sides of the equality the same sort."
)

_UNSUPPORTED_NODE = (
    "to_tptp_ncl: {name} is outside the supported mono-modal alethic "
    "fragment (Box/Diamond/¬/∧/∨/→/↔ over atoms, with native ∀/∃ "
    "quantifiers). Every other modal family (epistemic Knows/Believes, "
    "doxastic, temporal, deontic, counterfactual, PAL), and INDEXED "
    "multi-modal box(i)/dia(i), are documented, not-yet-implemented "
    "extensions -- see module docstring 'Scope'."
)


def _sort_token(sort_name: str) -> str:
    """The NXF identifier for a kit sort NAME (``SortedQuantifier.sort`` /
    ``SortedConstant.sort``) -- the same first-letter fold every other NXF
    identifier in this module goes through (see :func:`_term_sort` /
    :meth:`_NxfSymbols.note_predicate`), so a sort name follows the exact
    same TPTP lower_word convention as everything else this exporter emits.
    """
    return tptp_fold_first_letter(sort_name)


class _NxfSymbols:
    """Collects every sort / constant / predicate this export's formula uses,
    in first-occurrence order, while :func:`_render` walks the tree once --
    and refuses (NotImplementedError), rather than silently aliasing, any
    case where two DISTINCT kit symbols would render as the SAME NXF
    identifier, or the same kit symbol would need two DIFFERENT NXF types.
    Both are genuine soundness holes for an emitted problem: a duplicate
    ``type`` declaration for one name, or a real ambiguity a consuming
    prover would resolve arbitrarily, silently changing what is being
    proved. Mirrors the collision-refusal :func:`to_tptp_ncl` already
    applied to 0-ary propositional letters before this release, generalised
    to sorts/constants/predicates of any arity.
    """

    def __init__(self):
        self.sort_order: List[str] = []
        self.sort_sig: Dict[str, str] = {}                # token -> kit sort name
        self.const_order: List[str] = []
        self.const_sig: Dict[str, Tuple[str, str]] = {}   # token -> (kit name, sort token)
        self.pred_order: List[str] = []
        self.pred_sig: Dict[str, Tuple[str, tuple]] = {}  # token -> (kit name, arg sort tokens)

    def note_sort(self, name: str, token: str) -> None:
        """Register one kit sort NAME (``SortedQuantifier.sort`` /
        ``SortedConstant.sort``) under its folded NXF ``token``, refusing
        (NotImplementedError) rather than silently merging when two
        DISTINCT kit sort names would fold to the SAME token -- mirrors
        :meth:`note_constant`/:meth:`note_predicate` exactly (this is the
        sort-level counterpart of both; before this check, two sorts like
        ``"Human"``/``"human"`` collapsed into one ``$tType`` declaration,
        contradicting this class's own docstring)."""
        if token in self.sort_sig:
            prev_name = self.sort_sig[token]
            if prev_name != name:
                raise NotImplementedError(
                    f"to_tptp_ncl: distinct sorts {prev_name!r} and {name!r} "
                    f"would both render as the NXF identifier {token!r} "
                    "(TPTP lower-cases the first letter) -- refusing to "
                    "alias them; rename one of the sorts so the export "
                    "stays faithful.")
        else:
            self.sort_sig[token] = name
            self.sort_order.append(token)

    def note_constant(self, name: str, sort_token: str) -> None:
        token = Constant(name).to_tptp()
        if token in self.const_sig:
            prev_name, prev_sort = self.const_sig[token]
            if prev_name != name:
                raise NotImplementedError(
                    f"to_tptp_ncl: distinct constants {prev_name!r} and {name!r} "
                    f"would both render as the NXF identifier {token!r} (TPTP "
                    "lower-cases the first letter) -- refusing to alias them; "
                    "rename one of the constants so the export stays faithful.")
            if prev_sort != sort_token:
                raise NotImplementedError(
                    f"to_tptp_ncl: the constant {name!r} is used with two "
                    f"different sorts ({prev_sort!r} and {sort_token!r}) in "
                    "this formula -- TPTP requires one fixed type per symbol; "
                    "give it a single, consistent sort throughout.")
        else:
            self.const_sig[token] = (name, sort_token)
            self.const_order.append(token)

    def note_predicate(self, name: str, arg_sorts: tuple) -> None:
        token = tptp_fold_first_letter(name)
        if token in self.pred_sig:
            prev_name, prev_sorts = self.pred_sig[token]
            if prev_name != name:
                raise NotImplementedError(
                    f"to_tptp_ncl: distinct propositional/predicate letters "
                    f"{prev_name!r} and {name!r} would both render as the NXF "
                    f"identifier {token!r} (TPTP lower-cases the first "
                    "letter) -- refusing to alias them; rename one of the "
                    "atoms so the export stays faithful.")
            if prev_sorts != arg_sorts:
                raise NotImplementedError(
                    f"to_tptp_ncl: the predicate {name!r} is used at two "
                    f"different argument types/arities ({prev_sorts!r} and "
                    f"{arg_sorts!r}) in this formula -- TPTP requires one "
                    "fixed type per symbol; give it a single, consistent "
                    "signature throughout.")
        else:
            self.pred_sig[token] = (name, arg_sorts)
            self.pred_order.append(token)

    def check_no_cross_namespace_collision(self) -> None:
        """Refuse an NXF identifier used as more than one KIND of symbol
        (e.g. a sort named the same as a predicate) -- TPTP identifiers are
        a single flat namespace of ``lower_word`` tokens, so two DIFFERENT
        kit symbols folding to the same token would collide even if neither
        alone triggered :meth:`note_constant` / :meth:`note_predicate`."""
        kinds: Dict[str, set] = {}
        for token in self.sort_order:
            kinds.setdefault(token, set()).add("a sort")
        for token in self.const_order:
            kinds.setdefault(token, set()).add("a constant")
        for token in self.pred_order:
            kinds.setdefault(token, set()).add("a predicate")
        for token, seen in kinds.items():
            if len(seen) > 1:
                raise NotImplementedError(
                    f"to_tptp_ncl: the NXF identifier {token!r} would be "
                    f"declared as both {' and '.join(sorted(seen))} -- TPTP "
                    "identifiers share one flat namespace; rename one of the "
                    "colliding symbols so the export stays faithful.")


# Atom predicates TPTP renders as the genuinely INFIX built-in ('='/'!=') --
# never user-declared, so _render walks their arguments (for nested
# constants) without registering the predicate itself, but (unlike a plain
# user predicate) DOES require both operands to share one NXF sort token,
# since native TFF's polymorphic '=' has no subtyping/coercion (see
# _UNSUPPORTED_CROSS_SORT_EQUALITY). Reuses Atom's own table rather than
# re-listing it, so this set can never drift from what Atom.to_tptp()
# actually treats as infix.
_EQUALITY_PREDS = frozenset(Atom.INFIX_PREDS_TPTP)

# Arithmetic comparisons (TPTP's $less/$greater/$lesseq/$greatereq
# dollar-word PREFIX predicates) need TPTP's arithmetic sorts ($int/$rat/
# $real), which this exporter never declares -- refused by name rather than
# emitted over $i (or a user sort), mirroring atp.tptp_tff's identical
# TF0-only refusal of the same predicate set (see that module's
# _ARITH_OUT_OF_SCOPE). Reuses Atom's own table rather than re-listing it.
_ARITHMETIC_PREDS = frozenset(Atom.PREFIX_PREDS_TPTP)


def _term_sort(term: Node, scope: Dict[str, str], symbols: _NxfSymbols) -> str:
    """The NXF sort token of one TERM occurrence, registering any
    constant/sort it introduces into ``symbols`` as a side effect.

    ``scope`` maps a bound Variable's kit NAME to its NXF sort token (set by
    the enclosing Quantifier/SortedQuantifier in :func:`_render`). A
    Variable absent from ``scope`` is a genuinely FREE variable -- directly
    reachable through the public entry point (:func:`to_tptp_ncl` starts
    rendering with an empty scope, so any Atom/equality argument that is a
    Variable with no enclosing Quantifier/SortedQuantifier hits this case,
    found by adversarial review) -- and is refused rather than defaulted to
    ``$i``: TPTP reads a free variable in a conjecture role as EXISTENTIALLY
    quantified, not universally, so silently defaulting its sort would
    silently change the meaning of the exported problem, not merely under-
    specify its type.

    Raises:
        NotImplementedError: ``term`` is a free (unbound) Variable, a
            :class:`~fol.nodes.Function` (compound function term), or a
            :class:`~fol.nodes.Number` -- see module docstring 'Scope'.
    """
    if isinstance(term, Variable):
        if term.name not in scope:
            raise NotImplementedError(
                _UNSUPPORTED_FREE_VARIABLE.format(name=term.name))
        return scope[term.name]
    if isinstance(term, SortedConstant):
        token = _sort_token(term.sort)
        symbols.note_sort(term.sort, token)
        symbols.note_constant(term.name, token)
        return token
    if isinstance(term, Constant):
        symbols.note_constant(term.name, _DEFAULT_SORT)
        return _DEFAULT_SORT
    if isinstance(term, Number):
        # A bare numeral literal (e.g. "42") is TPTP's own built-in numeral
        # syntax, but it is intrinsically typed to an ARITHMETIC sort
        # ($int/$rat/$real) by the TPTP standard itself -- never to $i (the
        # individual sort) or to any user-declared $tType. This exporter
        # never declares an arithmetic sort (see _UNSUPPORTED_NUMBER /
        # module docstring 'Scope'), so defaulting a Number to $i the way an
        # untyped Constant/Quantifier does would emit a type-incorrect NXF/
        # TFF problem (found by adversarial review; the previous version of
        # this function did exactly that) -- refused instead, mirroring
        # atp.tptp_tff's identical TF0-only refusal of a Number term.
        raise NotImplementedError(_UNSUPPORTED_NUMBER.format(value=term.value))
    if isinstance(term, Function):
        raise NotImplementedError(_UNSUPPORTED_FUNCTION.format(name=term.name))
    raise NotImplementedError(
        f"to_tptp_ncl: unsupported term {type(term).__name__} in the "
        "quantified fragment -- see module docstring 'Scope'.")


def _quantifier_prefix(qtype: str, var_token: str, sort_token: str) -> str:
    if qtype in ("∀", "forall"):
        q = "!"
    elif qtype in ("∃", "exists"):
        q = "?"
    else:
        raise ValueError(f"to_tptp_ncl: unknown quantifier type {qtype!r}.")
    return f"{q} [{var_token}: {sort_token}]"


def _render(node: Node, scope: Dict[str, str], symbols: _NxfSymbols) -> str:
    """Render one node of the supported fragment as an NXF formula string,
    registering every sort/constant/predicate it introduces into ``symbols``.

    Mirrors the shape :meth:`Node.to_tptp` already uses for the classical
    connectives (``~(...)``, ``(l & r)``, ``(l | r)``, ``(l => r)``,
    ``(l <=> r)`` — see ``fol/_fol_nodes.py``), and extends it with the two
    NXF short-form modal prefix connectives, ``[.]``/``<.>``, and NATIVE NXF
    quantifiers ``! [X: <sort>] : (...)`` / ``? [X: <sort>] : (...)`` (see
    module docstring). Every branch's own output is already a self-delimited
    ``unary`` production (a bare atom, a ``~(...)``-wrapped formula, a fully
    parenthesised binary formula, ``[.]``/``<.>`` applied to one of those, or
    a quantifier whose OWN body is parenthesised — ``! [X: S] : (unary)`` is
    itself exactly the grammar's ``"!" "[" varlist "]" ":" unary`` alternative,
    matching :mod:`fol.tptp_input`'s ``?unary: ... | "!" "[" varlist "]" ":"
    unary | ...`` rule), so nesting one under another NEVER needs extra
    wrapping parentheses.

    Raises:
        NotImplementedError: ``node`` (or a descendant) is outside the
            supported fragment — a compound function-term, Number, or free
            (unbound) Variable argument, an arithmetic comparison predicate,
            a cross-sort equality, a quantifier of unknown type, or any
            modal-family node other than Box/Diamond.
    """
    if isinstance(node, Atom):
        if node.predicate in _ARITHMETIC_PREDS:
            raise NotImplementedError(
                _UNSUPPORTED_ARITHMETIC_PRED.format(name=node.predicate))
        if node.predicate in _EQUALITY_PREDS:
            if len(node.args) != 2:
                raise ValueError(
                    f"to_tptp_ncl: an equality/disequality atom "
                    f"({node.predicate!r}) must have exactly 2 arguments, "
                    f"got {len(node.args)}.")
            left_sort = _term_sort(node.args[0], scope, symbols)
            right_sort = _term_sort(node.args[1], scope, symbols)
            if left_sort != right_sort:
                raise NotImplementedError(_UNSUPPORTED_CROSS_SORT_EQUALITY.format(
                    pred=node.predicate, left=left_sort, right=right_sort))
            return node.to_tptp()
        if node.predicate.startswith("$"):
            for arg in node.args:
                _term_sort(arg, scope, symbols)
            return node.to_tptp()
        arg_sorts = tuple(_term_sort(arg, scope, symbols) for arg in node.args)
        symbols.note_predicate(node.predicate, arg_sorts)
        return node.to_tptp()
    if isinstance(node, Not):
        return f"~({_render(node.formula, scope, symbols)})"
    if isinstance(node, And):
        return f"({_render(node.left, scope, symbols)} & {_render(node.right, scope, symbols)})"
    if isinstance(node, Or):
        return f"({_render(node.left, scope, symbols)} | {_render(node.right, scope, symbols)})"
    if isinstance(node, Implies):
        return f"({_render(node.left, scope, symbols)} => {_render(node.right, scope, symbols)})"
    if isinstance(node, Iff):
        return f"({_render(node.left, scope, symbols)} <=> {_render(node.right, scope, symbols)})"
    if isinstance(node, Box):
        return f"[.] {_render(node.formula, scope, symbols)}"
    if isinstance(node, Diamond):
        return f"<.> {_render(node.formula, scope, symbols)}"
    if isinstance(node, (Quantifier, SortedQuantifier)):
        sort = node.sort if isinstance(node, SortedQuantifier) else None
        sort_token = _sort_token(sort) if sort is not None else _DEFAULT_SORT
        if sort is not None:
            symbols.note_sort(sort, sort_token)
        var_token = Variable(node.variable.name).to_tptp()
        new_scope = dict(scope)
        new_scope[node.variable.name] = sort_token
        body = _render(node.formula, new_scope, symbols)
        prefix = _quantifier_prefix(node.type, var_token, sort_token)
        return f"{prefix} : ({body})"
    raise NotImplementedError(_UNSUPPORTED_NODE.format(name=type(node).__name__))


def to_tptp_ncl(formula: Node, *, frame: str = "K", domains: str = "constant",
                conjecture_name: str = "c") -> str:
    """Render ``formula`` as a complete NXF (TPTP Non-Classical Logic) problem.

    Covers the mono-modal ALETHIC fragment: Box/Diamond over
    ``¬``/``∧``/``∨``/``→``/``↔``, atoms of any arity, and native
    ``∀``/``∃`` quantifiers (:class:`~fol.nodes.Quantifier` /
    :class:`~fol.nodes.SortedQuantifier`). See the module docstring for the
    verified syntax sources and the exact scope boundary (compound function
    terms, and non-alethic modal families, are documented, not-yet-
    implemented extensions, not silently mistranslated).

    The emitted problem is, in order:

    1. A ``logic`` role statement fixing the four NXF modal parameters —
       ``$designation`` is fixed to ``$rigid`` and ``$terms`` to ``$global``
       (the only combination the alethic fragment needs); ``$flexible``/
       ``$local`` are not exposed as they would only matter for a
       flexible-designation extension this module does not attempt.
    2. One ``tff(<sort>_type,type, <sort>: $tType ).`` per DISTINCT
       user-declared sort the formula uses (``SortedQuantifier``/
       ``SortedConstant``), in first-occurrence order — TPTP's built-in
       ``$i`` (the default for every untyped Quantifier/Constant) needs no
       such declaration and gets none (see :data:`_DEFAULT_SORT`).
    3. One ``tff(<name>_decl,type, <name>: <sort> ).`` per DISTINCT free
       constant the formula uses, in first-occurrence order.
    4. One ``tff(<name>_decl,type, ...).`` per DISTINCT predicate the
       formula uses, in first-occurrence order — ``<name>: $o`` for a 0-ary
       (propositional) letter, ``<name>: <sort> > $o`` for one argument, or
       ``<name>: (<s1> * <s2> * ...) > $o`` for several — required because
       NXF/NTF is a typed (TFF-based) dialect; an undeclared bare atom is
       not accepted.
    5. One ``conjecture`` role statement holding the translated ``formula``.

    Args:
        formula: a modal formula built from Box/Diamond/Not/And/Or/Implies/
            Iff/Quantifier/SortedQuantifier over Atom nodes (the supported
            fragment — see module docstring). Typically the result of
            folding ``premises ⊨ conclusion`` into ``(∧premises) →
            conclusion`` first (:func:`atp.leo3_backend`'s ``decide()`` does
            this), since NXF has no separate premise list — one conjecture
            is the whole problem.
        frame: the alethic modal system — one of ``"K"``, ``"T"``, ``"S4"``,
            ``"S5"``, ``"D"`` (:class:`ValueError` listing the valid names
            otherwise).
        domains: the NXF ``$domains`` value — one of ``"constant"``,
            ``"varying"``, ``"cumulative"``, ``"decreasing"``
            (:class:`ValueError` listing the valid names otherwise). Every
            value selects a distinct ``$domains == ...`` token; NONE of them
            changes how a quantifier is RENDERED (native ``!``/``?`` either
            way) — see :data:`_DOMAIN_WORDS`'s docstring for exactly why
            that is the correct, non-approximated behaviour rather than a
            silent no-op.
        conjecture_name: the TPTP statement name used for the ``conjecture``
            role formula; the ``logic`` role statement is named
            ``<conjecture_name>_logic``.

    Returns:
        The complete NXF problem text, newline-terminated, ready to write to
        a ``.p`` file for an NXF-aware prover (e.g. Leo-III via
        :class:`atp.leo3_backend.Leo3Backend`).

    Raises:
        ValueError: ``frame`` or ``domains`` is not one of the recognised
            values, or a Quantifier/SortedQuantifier has an unrecognised
            ``type``.
        NotImplementedError: ``formula`` (or a descendant) is outside the
            supported fragment, or two distinct kit symbols would collide
            under NXF's identifier folding — see :func:`_render` /
            :class:`_NxfSymbols`.
    """
    if frame not in _FRAME_TO_SYSTEM:
        raise ValueError(
            f"to_tptp_ncl: unknown frame {frame!r} (use one of {sorted(_FRAME_TO_SYSTEM)})")
    if domains not in _DOMAIN_WORDS:
        raise ValueError(
            f"to_tptp_ncl: unknown domains {domains!r} (use one of {sorted(_DOMAIN_WORDS)})")

    # _render walks the WHOLE tree, collecting every sort/constant/predicate
    # into `symbols` and raising before anything is emitted if any node (or
    # term) is outside the supported fragment.
    symbols = _NxfSymbols()
    body = _render(formula, {}, symbols)
    symbols.check_no_cross_namespace_collision()

    lines = [
        f"tff({conjecture_name}_logic,logic,",
        "    $modal ==",
        f"      [ $domains == {_DOMAIN_WORDS[domains]},",
        "        $designation == $rigid,",
        "        $terms == $global,",
        f"        $modalities == {_FRAME_TO_SYSTEM[frame]} ] ).",
        "",
    ]
    for token in symbols.sort_order:
        lines.append(f"tff({token}_type,type,")
        lines.append(f"    {token}: $tType ).")
        lines.append("")
    for token in symbols.const_order:
        _, sort_token = symbols.const_sig[token]
        lines.append(f"tff({token}_decl,type,")
        lines.append(f"    {token}: {sort_token} ).")
        lines.append("")
    for token in symbols.pred_order:
        _, arg_sorts = symbols.pred_sig[token]
        lines.append(f"tff({token}_decl,type,")
        if not arg_sorts:
            lines.append(f"    {token}: $o ).")
        elif len(arg_sorts) == 1:
            lines.append(f"    {token}: {arg_sorts[0]} > $o ).")
        else:
            domain = " * ".join(arg_sorts)
            lines.append(f"    {token}: ({domain}) > $o ).")
        lines.append("")
    lines.append(f"tff({conjecture_name},conjecture,")
    lines.append(f"    {body} ).")
    return "\n".join(lines) + "\n"
