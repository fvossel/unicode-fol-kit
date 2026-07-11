r"""Isabelle/HOL shallow semantical embedding (SSE) of quantified modal logic.

This module *emits* a complete, loadable Isabelle/HOL theory (``theory NAME
imports Main begin ... end``) that shallow-embeds a modal formula in the
Benzmüller style and states it as a **real** ``lemma`` (not a comment). It is the
faithful Isabelle counterpart of the THF export
:func:`unicode_fol_kit.fol.qml.to_thf_modal` and is kept consistent with the
ground-truth Kripke evaluator
:func:`unicode_fol_kit.semantics.kripke.satisfies_modal`.

What it covers
--------------
The full modal family handled by the AST:

- **alethic** ``Box`` □ / ``Diamond`` ◇ over an accessibility relation ``r``;
- **epistemic** ``Knows`` and **doxastic** ``Believes`` over **agent-indexed**
  relations ``rk`` / ``rb`` of type ``'a \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool`` — the
  agent is a first-class *term* (``Variable`` or ``Constant``), so a bound object
  variable in agent position (``∀x (Student(x) → K_x φ)``) quantifies over agents,
  exactly as in :func:`satisfies_modal`;
- **deontic** ``Obligatory`` / ``Permitted`` over a (serial) relation ``d``;
- **temporal** ``Always`` / ``Eventually`` over the henceforth relation ``t`` and
  ``Next`` over the one-step relation ``n``, plus the binary interval operators
  ``Until`` / ``Since`` as inductive least fixpoints over ``n`` (see below).

The embedding is **faithful to** :func:`satisfies_modal` on the overlapping
fragment: every modality is read as a box/diamond over the corresponding
relation, object quantifiers are ``existsAt``-guarded (actualist), and equality
``=`` / ``≠`` is an **uninterpreted, world-relativized predicate** (NOT primitive
HOL identity), matching the toolkit convention.

Temporal caveat (henceforth / transitive closure)
-------------------------------------------------
``satisfies_modal`` reads ``Always``/``Eventually`` over the **reflexive-transitive
closure** of the one-step ``"temporal"`` relation, whereas a plain shallow
abbreviation can only quantify over the relation it is given. This module emits
the **box/diamond-over-``t`` reading** and, when ``temporal_closure=True`` (the
default), additionally constrains ``t`` to be a *reflexive + transitive* relation
via frame axioms, so ``t`` denotes the henceforth relation directly and the
embedding matches the closure semantics. ``Next`` is the genuine one-step box over
the one-step successor relation ``n``. In ``satisfies_modal`` ``Always`` /
``Eventually`` close over the **same** one-step ``"temporal"`` relation that
``Next`` reads, so every one-step successor is henceforth-reachable and
``Always(P) → Next(P)`` is valid. To keep the embedding faithful, when ``Next``
co-occurs with ``Always`` / ``Eventually`` (both ``n`` and ``t`` declared) this
module emits the linking axiom ``n_in_t : "⋀w v. n w v ⟹ t w v"`` (one-step
successor ⟹ henceforth-reachable), so ``Always(P) → Next(P)`` is likewise a
theorem of the emitted theory.

Binary interval operators ``Until`` / ``Since``
-----------------------------------------------
``Until`` and ``Since`` are emitted as **inductive least-fixpoint predicates**
``muntil`` / ``msince`` over the one-step relation ``n`` (not as box/diamond
abbreviations). ``muntil phi psi`` is the least predicate closed under
``psi w ⟹ muntil w`` and ``phi w ∧ n w v ∧ muntil v ⟹ muntil w``, so it denotes
exactly the **finite forward ``n``-paths** with ``psi`` at the endpoint and
``phi`` at every earlier point — the faithful counterpart of the depth-first path
search in :func:`satisfies_modal` (``_until_holds``); ``msince`` is the backward
mirror over the converse of ``n`` (``_since_holds``). A plain interval reading over
the closure ``t`` would *not* be faithful on branching / short-cut frames (it asks
``phi`` at every ``t``-intermediate world, the path search only along one path); the
least fixpoint is faithful on **every** frame. Because these read the one-step
relation ``n``, using ``Until`` / ``Since`` declares ``n`` (as ``Next`` does) and,
when ``Always`` / ``Eventually`` also occur, links ``n`` into the henceforth ``t``
so the two agree. The Isabelle-verified characterization (the strong-Until /
Since fixpoint equation and reachability) lives in ``tests/test_hol_isabelle_modal``
and the live ``check_theory`` gate.

Honesty
-------
The toolkit *emits* a theory; it does **not** run Isabelle, Sledgehammer, or any
prover. First-order modal logic, like FOL, is **undecidable but semi-decidable**
(validity is recursively enumerable; full second-order logic is *not even
semi-decidable*), so a successful emission means "here is a sound problem an
external prover *may* discharge", never "the formula is decided". Propositional
modal K/T/S4/S5 *are* decidable, but this emitter does not itself decide them.
The default proof tactic is a Sledgehammer hook followed by an ``oops`` fallback
so the emitted theory always loads even when no automatic proof is found.

Public API
----------
:func:`to_isabelle_modal` (the real ``to_isabelle_modal`` replacement),
:func:`isabelle_modal_theory` (alias with an explicit ``theory_name``),
and the constant :data:`ISABELLE_TACTICS`.
"""

import re
from typing import List, Optional

from unicode_fol_kit.fol.nodes import (
    Node, Variable, Constant, Number, Function,
    Atom, Not, And, Or, Xor, Implies, Iff, Quantifier,
    Box, Diamond, Knows, Believes,
    Always, Eventually, Next, Until, Since,
    Obligatory, Permitted, SortedQuantifier,
)
from unicode_fol_kit.fol._symbol_names import SymbolNames

# --------------------------------------------------------------------------- #
# Configuration tables (kept in sync with qml.py / satisfies_modal).
# --------------------------------------------------------------------------- #

# Frame systems for the ALETHIC relation r (mirrors qml._FRAMES).
_FRAMES = {
    "K": (),
    "T": ("refl",),
    "S4": ("refl", "trans"),
    "S5": ("refl", "trans", "sym"),
    "KD": ("serial",),
    "KD45": ("serial", "trans", "eucl"),
    "B": ("refl", "sym"),                          # Brouwer
    "S4.2": ("refl", "trans", "directed"),         # convergent (.2)
    "S4.3": ("refl", "trans", "connected"),        # no-branching / linear (.3)
    "GL": ("trans", "loeb"),                       # Gödel–Löb provability (Löb schema)
}

_ACTUALIST_MODES = frozenset({"varying", "increasing", "cumulative", "decreasing"})
_CONSTANT_MODES = frozenset({"constant", "possibilist"})

_FORALL = ("∀", "forall")
_EXISTS = ("∃", "exists")

# Available proof-tactic presets for the emitted lemma. Each maps to the Isabelle
# proof text placed after the lemma statement. ``sledgehammer`` is the honest
# default: it inserts a Sledgehammer invitation and an ``oops`` so the theory
# always loads (Isabelle treats ``oops`` as "abandon this goal" — syntactically
# valid, nothing claimed proved).
ISABELLE_TACTICS = {
    "sledgehammer": "  sledgehammer\n  oops",
    "auto": "  by auto",
    "blast": "  by blast",
    "metis": "  by (metis (full_types))",
    "smt": "  by (smt (verit))",
    "simp": "  by simp",
    "force": "  by force",
    "oops": "  oops",
    "sorry": "  sorry",
}

# Tactics whose ``by ...`` proof needs the frame / domain axioms brought into the
# proof context: a bare ``axiomatization where r_refl: ...`` fact is NOT in the
# default claset/simpset, so ``by blast`` / ``by auto`` / ``by (metis ...)`` cannot
# see it and any axiom-dependent validity (T/S4/S5/KD/KD45, temporal closure, a
# domain regime) fails to discharge even though the formula is valid and the theory
# sound. For these tactics we emit ``using <axioms> by <tactic>``. ``sledgehammer``
# finds its own facts; ``oops`` / ``sorry`` prove nothing, so they are excluded.
_BY_TACTICS = frozenset({"auto", "blast", "metis", "smt", "simp", "force"})

_AXIOM_NAME_RE = re.compile(r"axiomatization where (\w+):")


def _axiom_names(axiom_lines: List[str]) -> List[str]:
    """Read the fact names out of emitted ``axiomatization where NAME: ...`` lines."""
    out: List[str] = []
    for ln in axiom_lines:
        m = _AXIOM_NAME_RE.search(ln)
        if m:
            out.append(m.group(1))
    return out

# Equality / inequality are uninterpreted, world-relativized predicates here (NOT
# primitive HOL `=`), matching satisfies_modal and the THF export. These aliases
# give them valid, distinct Isabelle constant names.
_PRED_ALIAS = {"=": "feq", "≠": "fneq", "<": "flt", ">": "fgt", "≤": "fle", "≥": "fge"}


# --------------------------------------------------------------------------- #
# Name sanitising.
# --------------------------------------------------------------------------- #

# Built-in identifiers of the emitted theory — the world type, the accessibility
# relations / existence predicate, and every lifted-operator abbreviation. A user
# predicate / constant / function whose sanitised name lands here would shadow the
# embedding and break loadability, so _safe_name disambiguates it with a trailing "_".
_RESERVED = frozenset({
    "i", "existsAt",
    "r", "rk", "rb", "d", "t", "n",
    "mnot", "mand", "mor", "mimp", "miff", "mvalid", "mbox", "mdia",
    "knows", "believes", "obl", "perm", "malways", "meventually", "mnext",
    "mforall", "mexists",
})


def _safe_name(name: str) -> str:
    """Turn a predicate/constant/function name into a legal lowercase Isabelle id.

    Disambiguates names that would collide with a built-in embedding identifier
    (a relation, the existence predicate, the world type, or a lifted operator).
    """
    if name in _PRED_ALIAS:
        return _PRED_ALIAS[name]
    out = "".join(c if (c.isalnum() or c == "_") else "_" for c in str(name))
    if not out:
        out = "p"
    if not (out[0].isalpha() or out[0] == "_"):
        out = "c_" + out
    # Lower-case the leading char so it cannot collide with a bound type/var.
    out = out[0].lower() + out[1:]
    while out in _RESERVED:
        out = out + "_"
    return out


def _var_name(name: str) -> str:
    """Isabelle term-variable name (object variables stay lowercase, legal)."""
    out = "".join(c if (c.isalnum() or c == "_") else "_" for c in str(name))
    if not out or not (out[0].isalpha() or out[0] == "_"):
        out = "x_" + out
    return out


class _IsaNames(SymbolNames):
    """Per-formula Isabelle constant-name resolver (the shared :class:`SymbolNames` over
    ``_safe_name`` + the equality aliases), so distinct source symbols that sanitise
    alike (``Ab`` / ``ab``) — or a predicate used at two arities — get DISTINCT
    ``consts``. Without it ``□Ab → □ab`` could collapse to a tautology and emit duplicate
    ``consts`` (which Isabelle rejects).
    """

    def __init__(self, formula: Node):
        super().__init__(formula, _safe_name, _PRED_ALIAS)


# --------------------------------------------------------------------------- #
# Term rendering.
# --------------------------------------------------------------------------- #

def _term(node: Node, names: "_IsaNames") -> str:
    """Render an individual term (used as an argument to a lifted predicate)."""
    if isinstance(node, Variable):
        return _var_name(node.name)
    if isinstance(node, Constant):
        return names.constant(node.name)
    if isinstance(node, Number):
        return names.constant("n" + str(node.value))
    if isinstance(node, Function):
        head = names.function(node)
        if not node.args:
            return head
        return "(" + head + " " + " ".join(_term(a, names) for a in node.args) + ")"
    raise NotImplementedError(
        f"to_isabelle_modal: unsupported term {type(node).__name__}.")


# --------------------------------------------------------------------------- #
# Formula lifting:  Node  ->  Isabelle term of type  i => bool.
# --------------------------------------------------------------------------- #

def _atom(node: Atom, names: "_IsaNames") -> str:
    """Lift an atom to ``(pred a1 ... an)`` — a value of type ``i => bool``."""
    head = names.atom(node)
    if not node.args:
        return head
    return "(" + head + " " + " ".join(_term(a, names) for a in node.args) + ")"


def _lift(node: Node, names: "_IsaNames") -> str:
    r"""Lift a modal formula to an Isabelle term of type ``i \<Rightarrow> bool``.

    Mirrors the THF ``_thf_lift`` and stays faithful to ``satisfies_modal``: every
    modality becomes a box/diamond over the matching relation, object quantifiers
    are existsAt-guarded, and the agent of Knows/Believes is carried as a real term.
    """
    if isinstance(node, Atom):
        return _atom(node, names)
    if isinstance(node, Not):
        return f"(mnot {_lift(node.formula, names)})"
    if isinstance(node, And):
        return f"(mand {_lift(node.left, names)} {_lift(node.right, names)})"
    if isinstance(node, Or):
        return f"(mor {_lift(node.left, names)} {_lift(node.right, names)})"
    if isinstance(node, Xor):
        # Xor ≡ ¬(φ ↔ ψ); satisfies_modal reads Xor as truth-value inequality.
        return f"(mnot (miff {_lift(node.left, names)} {_lift(node.right, names)}))"
    if isinstance(node, Implies):
        return f"(mimp {_lift(node.left, names)} {_lift(node.right, names)})"
    if isinstance(node, Iff):
        return f"(miff {_lift(node.left, names)} {_lift(node.right, names)})"

    if isinstance(node, Box):
        return f"(mbox {_lift(node.formula, names)})"
    if isinstance(node, Diamond):
        return f"(mdia {_lift(node.formula, names)})"

    if isinstance(node, Knows):
        return f"(knows {_term(node.agent, names)} {_lift(node.formula, names)})"
    if isinstance(node, Believes):
        return f"(believes {_term(node.agent, names)} {_lift(node.formula, names)})"

    if isinstance(node, Obligatory):
        return f"(obl {_lift(node.formula, names)})"
    if isinstance(node, Permitted):
        return f"(perm {_lift(node.formula, names)})"

    if isinstance(node, Always):
        return f"(malways {_lift(node.formula, names)})"
    if isinstance(node, Eventually):
        return f"(meventually {_lift(node.formula, names)})"
    if isinstance(node, Next):
        return f"(mnext {_lift(node.formula, names)})"

    if isinstance(node, Quantifier):
        x = _var_name(node.variable.name)
        binder = "mforall" if node.type in _FORALL else "mexists"
        return f"({binder} (\\<lambda>{x}. {_lift(node.formula, names)}))"

    if isinstance(node, Until):
        # Strong "left until right" as the inductive predicate ``muntil`` (least
        # fixpoint over the one-step relation n), matching satisfies_modal's finite
        # forward-path search exactly. See _until_block.
        return f"(muntil {_lift(node.left, names)} {_lift(node.right, names)})"
    if isinstance(node, Since):
        # Past-tense "left since right" as ``msince`` (least fixpoint over the CONVERSE
        # of n), the backward mirror of muntil — matching satisfies_modal's backward
        # path search. See _since_block.
        return f"(msince {_lift(node.left, names)} {_lift(node.right, names)})"
    if isinstance(node, SortedQuantifier):
        raise NotImplementedError(
            "to_isabelle_modal: SortedQuantifier is not supported; use a plain ∀x/∃x.")
    raise NotImplementedError(
        f"to_isabelle_modal: unsupported node type {type(node).__name__}.")


# --------------------------------------------------------------------------- #
# Signature discovery (which operators / relations / typed consts are needed).
# --------------------------------------------------------------------------- #

class _Sig:
    """Collected signature: predicates, constants, functions, and used modalities."""

    def __init__(self):
        self.preds = {}     # safe_name -> arity (object args)
        self.consts = set()  # safe_name
        self.funcs = {}     # safe_name -> arity
        self.uses_alethic = False
        self.uses_epistemic = False
        self.uses_doxastic = False
        self.uses_deontic = False
        self.uses_temporal = False   # Always / Eventually  (relation t)
        self.uses_next = False       # Next                 (relation n)
        self.uses_until = False      # Until (inductive muntil over n)
        self.uses_since = False      # Since (inductive msince over converse n)
        self.has_quant = False

    @property
    def needs_next_rel(self) -> bool:
        """Whether the one-step relation ``n`` must be declared.

        ``n`` is needed by ``Next`` (mnext) and by the inductive ``muntil`` / ``msince``
        (which do a one-step forward / backward path search over it).
        """
        return self.uses_next or self.uses_until or self.uses_since


def _scan_term(node: Node, sig: _Sig) -> None:
    if isinstance(node, Constant):
        sig.consts.add(_safe_name(node.name))
    elif isinstance(node, Number):
        sig.consts.add(_safe_name("n" + str(node.value)))
    elif isinstance(node, Function):
        sig.funcs[_safe_name(node.name)] = len(node.args)
        for a in node.args:
            _scan_term(a, sig)
    # Variables contribute nothing to the signature.


def _scan(node: Node, sig: _Sig) -> None:
    """Walk the formula collecting the signature and which modalities are used."""
    if isinstance(node, Atom):
        sig.preds[_safe_name(node.predicate)] = len(node.args)
        for a in node.args:
            _scan_term(a, sig)
        return
    if isinstance(node, (Not,)):
        _scan(node.formula, sig)
        return
    if isinstance(node, (And, Or, Xor, Implies, Iff)):
        _scan(node.left, sig)
        _scan(node.right, sig)
        return
    if isinstance(node, Box):
        sig.uses_alethic = True
        _scan(node.formula, sig)
        return
    if isinstance(node, Diamond):
        sig.uses_alethic = True
        _scan(node.formula, sig)
        return
    if isinstance(node, Knows):
        sig.uses_epistemic = True
        _scan_term(node.agent, sig)
        _scan(node.formula, sig)
        return
    if isinstance(node, Believes):
        sig.uses_doxastic = True
        _scan_term(node.agent, sig)
        _scan(node.formula, sig)
        return
    if isinstance(node, (Obligatory, Permitted)):
        sig.uses_deontic = True
        _scan(node.formula, sig)
        return
    if isinstance(node, (Always, Eventually)):
        sig.uses_temporal = True
        _scan(node.formula, sig)
        return
    if isinstance(node, Next):
        sig.uses_next = True
        _scan(node.formula, sig)
        return
    if isinstance(node, Quantifier):
        sig.has_quant = True
        _scan(node.formula, sig)
        return
    if isinstance(node, Until):
        sig.uses_until = True
        _scan(node.left, sig)
        _scan(node.right, sig)
        return
    if isinstance(node, Since):
        sig.uses_since = True
        _scan(node.left, sig)
        _scan(node.right, sig)
        return
    if isinstance(node, SortedQuantifier):
        raise NotImplementedError(
            "to_isabelle_modal: SortedQuantifier is not supported; use a plain ∀x/∃x.")
    raise NotImplementedError(
        f"to_isabelle_modal: unsupported node type {type(node).__name__}.")


# --------------------------------------------------------------------------- #
# Fixed building blocks of the theory.
# --------------------------------------------------------------------------- #

# World type and the propositional/connective abbreviations are ALWAYS emitted.
_CORE_ABBREVS = [
    'abbreviation mnot :: "(i \\<Rightarrow> bool) \\<Rightarrow> (i \\<Rightarrow> bool)" where',
    '  "mnot \\<phi> \\<equiv> \\<lambda>w. \\<not> \\<phi> w"',
    'abbreviation mand :: "(i \\<Rightarrow> bool) \\<Rightarrow> (i \\<Rightarrow> bool) \\<Rightarrow> (i \\<Rightarrow> bool)" where',
    '  "mand \\<phi> \\<psi> \\<equiv> \\<lambda>w. \\<phi> w \\<and> \\<psi> w"',
    'abbreviation mor :: "(i \\<Rightarrow> bool) \\<Rightarrow> (i \\<Rightarrow> bool) \\<Rightarrow> (i \\<Rightarrow> bool)" where',
    '  "mor \\<phi> \\<psi> \\<equiv> \\<lambda>w. \\<phi> w \\<or> \\<psi> w"',
    'abbreviation mimp :: "(i \\<Rightarrow> bool) \\<Rightarrow> (i \\<Rightarrow> bool) \\<Rightarrow> (i \\<Rightarrow> bool)" where',
    '  "mimp \\<phi> \\<psi> \\<equiv> \\<lambda>w. \\<phi> w \\<longrightarrow> \\<psi> w"',
    'abbreviation miff :: "(i \\<Rightarrow> bool) \\<Rightarrow> (i \\<Rightarrow> bool) \\<Rightarrow> (i \\<Rightarrow> bool)" where',
    '  "miff \\<phi> \\<psi> \\<equiv> \\<lambda>w. \\<phi> w \\<longleftrightarrow> \\<psi> w"',
]

# validity: truth at every world.
_VALID_ABBREV = [
    'abbreviation mvalid :: "(i \\<Rightarrow> bool) \\<Rightarrow> bool" ("\\<lfloor>_\\<rfloor>") where',
    '  "\\<lfloor>\\<phi>\\<rfloor> \\<equiv> \\<forall>w. \\<phi> w"',
]


def _alethic_block() -> List[str]:
    return [
        'consts r :: "i \\<Rightarrow> i \\<Rightarrow> bool"  \\<comment> \\<open>alethic accessibility\\<close>',
        'abbreviation mbox :: "(i \\<Rightarrow> bool) \\<Rightarrow> (i \\<Rightarrow> bool)" where',
        '  "mbox \\<phi> \\<equiv> \\<lambda>w. \\<forall>v. r w v \\<longrightarrow> \\<phi> v"',
        'abbreviation mdia :: "(i \\<Rightarrow> bool) \\<Rightarrow> (i \\<Rightarrow> bool)" where',
        '  "mdia \\<phi> \\<equiv> \\<lambda>w. \\<exists>v. r w v \\<and> \\<phi> v"',
    ]


def _epistemic_block() -> List[str]:
    return [
        'consts rk :: "\'a \\<Rightarrow> i \\<Rightarrow> i \\<Rightarrow> bool"  \\<comment> \\<open>agent-indexed epistemic accessibility\\<close>',
        'abbreviation knows :: "\'a \\<Rightarrow> (i \\<Rightarrow> bool) \\<Rightarrow> (i \\<Rightarrow> bool)" where',
        '  "knows a \\<phi> \\<equiv> \\<lambda>w. \\<forall>v. rk a w v \\<longrightarrow> \\<phi> v"',
    ]


def _doxastic_block() -> List[str]:
    return [
        'consts rb :: "\'a \\<Rightarrow> i \\<Rightarrow> i \\<Rightarrow> bool"  \\<comment> \\<open>agent-indexed doxastic accessibility\\<close>',
        'abbreviation believes :: "\'a \\<Rightarrow> (i \\<Rightarrow> bool) \\<Rightarrow> (i \\<Rightarrow> bool)" where',
        '  "believes a \\<phi> \\<equiv> \\<lambda>w. \\<forall>v. rb a w v \\<longrightarrow> \\<phi> v"',
    ]


def _deontic_block() -> List[str]:
    return [
        'consts d :: "i \\<Rightarrow> i \\<Rightarrow> bool"  \\<comment> \\<open>deontic accessibility (serial)\\<close>',
        'abbreviation obl :: "(i \\<Rightarrow> bool) \\<Rightarrow> (i \\<Rightarrow> bool)" where',
        '  "obl \\<phi> \\<equiv> \\<lambda>w. \\<forall>v. d w v \\<longrightarrow> \\<phi> v"',
        'abbreviation perm :: "(i \\<Rightarrow> bool) \\<Rightarrow> (i \\<Rightarrow> bool)" where',
        '  "perm \\<phi> \\<equiv> \\<lambda>w. \\<exists>v. d w v \\<and> \\<phi> v"',
    ]


def _temporal_block() -> List[str]:
    return [
        'consts t :: "i \\<Rightarrow> i \\<Rightarrow> bool"  \\<comment> \\<open>temporal henceforth relation (refl+trans closure)\\<close>',
        'abbreviation malways :: "(i \\<Rightarrow> bool) \\<Rightarrow> (i \\<Rightarrow> bool)" where',
        '  "malways \\<phi> \\<equiv> \\<lambda>w. \\<forall>v. t w v \\<longrightarrow> \\<phi> v"',
        'abbreviation meventually :: "(i \\<Rightarrow> bool) \\<Rightarrow> (i \\<Rightarrow> bool)" where',
        '  "meventually \\<phi> \\<equiv> \\<lambda>w. \\<exists>v. t w v \\<and> \\<phi> v"',
    ]


def _temporal_def_block() -> List[str]:
    r"""Temporal block with ``t`` **defined** as ``rtranclp n`` (the refl-trans closure
    of the one-step relation), not a ``consts`` constrained by axioms.

    Used by the runner's refute step: with ``t`` determined by ``n``, nitpick searches
    a candidate ``n`` and computes ``t`` itself, so it can actually find a finite
    counter-model to a non-theorem of the Always/Next closure fragment (a ``consts t``
    with an ``rtranclp`` *axiom* leaves nitpick unable to construct the closure).
    Requires the next block (``consts n``) to be emitted first.
    """
    return [
        'definition t :: "i \\<Rightarrow> i \\<Rightarrow> bool" where "t = rtranclp n"  '
        '\\<comment> \\<open>henceforth = reflexive-transitive closure of the one-step n\\<close>',
        'abbreviation malways :: "(i \\<Rightarrow> bool) \\<Rightarrow> (i \\<Rightarrow> bool)" where',
        '  "malways \\<phi> \\<equiv> \\<lambda>w. \\<forall>v. t w v \\<longrightarrow> \\<phi> v"',
        'abbreviation meventually :: "(i \\<Rightarrow> bool) \\<Rightarrow> (i \\<Rightarrow> bool)" where',
        '  "meventually \\<phi> \\<equiv> \\<lambda>w. \\<exists>v. t w v \\<and> \\<phi> v"',
    ]


def _next_consts_block() -> List[str]:
    """Declare the one-step successor relation ``n`` (needed by Next / Until / Since)."""
    return [
        'consts n :: "i \\<Rightarrow> i \\<Rightarrow> bool"  \\<comment> \\<open>one-step temporal successor\\<close>',
    ]


def _next_abbrev_block() -> List[str]:
    """The ``mnext`` box-over-``n`` abbreviation (emitted only when Next occurs)."""
    return [
        'abbreviation mnext :: "(i \\<Rightarrow> bool) \\<Rightarrow> (i \\<Rightarrow> bool)" where',
        '  "mnext \\<phi> \\<equiv> \\<lambda>w. \\<forall>v. n w v \\<longrightarrow> \\<phi> v"',
    ]


def _until_block() -> List[str]:
    r"""``muntil`` — strong "left until right" as a least fixpoint over ``n``.

    Defined inductively so it denotes exactly the FINITE forward paths
    ``w = w0 \<rightarrow> ... \<rightarrow> wn`` (one-step ``n`` edges, n \<ge> 0) with ``psi`` at the
    endpoint and ``phi`` at every earlier point — the faithful counterpart of
    :func:`unicode_fol_kit.semantics.kripke._until_holds` (its depth-first path
    search). A plain box/diamond-over-``t`` abbreviation could NOT capture "phi all
    the way along the path" (on a branching/short-cut frame the interval reading
    over the closure ``t`` differs from the path search); the least fixpoint does,
    so this is faithful to ``satisfies_modal`` on every frame, not just linear ones.
    ``n`` (the one-step relation) must be declared first.
    """
    return [
        'inductive muntil :: "(i \\<Rightarrow> bool) \\<Rightarrow> (i \\<Rightarrow> bool) \\<Rightarrow> i \\<Rightarrow> bool"',
        '  for phi :: "i \\<Rightarrow> bool" and psi :: "i \\<Rightarrow> bool" where',
        '  muntil_base: "psi w \\<Longrightarrow> muntil phi psi w"',
        '| muntil_step: "phi w \\<Longrightarrow> n w v \\<Longrightarrow> muntil phi psi v '
        '\\<Longrightarrow> muntil phi psi w"',
    ]


def _since_block() -> List[str]:
    r"""``msince`` — past-tense "left since right", the backward mirror of ``muntil``.

    Same least fixpoint but stepping along the CONVERSE of ``n`` (``n v w``: ``v`` is a
    one-step predecessor of ``w``), so it denotes the finite BACKWARD paths matching
    :func:`unicode_fol_kit.semantics.kripke._since_holds`. ``n`` must be declared first.
    """
    return [
        'inductive msince :: "(i \\<Rightarrow> bool) \\<Rightarrow> (i \\<Rightarrow> bool) \\<Rightarrow> i \\<Rightarrow> bool"',
        '  for phi :: "i \\<Rightarrow> bool" and psi :: "i \\<Rightarrow> bool" where',
        '  msince_base: "psi w \\<Longrightarrow> msince phi psi w"',
        '| msince_step: "phi w \\<Longrightarrow> n v w \\<Longrightarrow> msince phi psi v '
        '\\<Longrightarrow> msince phi psi w"',
    ]


def _quant_block(mode: str) -> List[str]:
    """existsAt + actualist mforall/mexists (constant mode makes existsAt total)."""
    return [
        'consts existsAt :: "\'a \\<Rightarrow> i \\<Rightarrow> bool"  \\<comment> \\<open>object x exists at world w\\<close>',
        'abbreviation mforall :: "(\'a \\<Rightarrow> (i \\<Rightarrow> bool)) \\<Rightarrow> (i \\<Rightarrow> bool)" where',
        '  "mforall \\<Phi> \\<equiv> \\<lambda>w. \\<forall>x. existsAt x w \\<longrightarrow> \\<Phi> x w"',
        'abbreviation mexists :: "(\'a \\<Rightarrow> (i \\<Rightarrow> bool)) \\<Rightarrow> (i \\<Rightarrow> bool)" where',
        '  "mexists \\<Phi> \\<equiv> \\<lambda>w. \\<exists>x. existsAt x w \\<and> \\<Phi> x w"',
    ]


# --------------------------------------------------------------------------- #
# Frame / domain axioms.
# --------------------------------------------------------------------------- #

def _frame_axioms(frame: str) -> List[str]:
    """Alethic-frame axioms on r for the chosen frame system."""
    conds = _FRAMES[frame]
    out = []
    if "refl" in conds:
        out.append('axiomatization where r_refl: "r w w"')
    if "trans" in conds:
        out.append('axiomatization where r_trans: "r w v \\<Longrightarrow> r v u \\<Longrightarrow> r w u"')
    if "sym" in conds:
        out.append('axiomatization where r_sym: "r w v \\<Longrightarrow> r v w"')
    if "serial" in conds:
        out.append('axiomatization where r_serial: "\\<exists>v. r w v"')
    if "eucl" in conds:
        out.append('axiomatization where r_eucl: "r w v \\<Longrightarrow> r w u \\<Longrightarrow> r v u"')
    if "directed" in conds:
        out.append('axiomatization where r_directed: '
                   '"r w v \\<Longrightarrow> r w u \\<Longrightarrow> \\<exists>z. r v z \\<and> r u z"')
    if "connected" in conds:
        out.append('axiomatization where r_conn: '
                   '"r w v \\<Longrightarrow> r w u \\<Longrightarrow> r v u \\<or> r u v"')
    if "loeb" in conds:
        # Gödel–Löb provability: the Löb schema □(□P → P) → □P (P, w free, i.e.
        # universally generalised). Stated over r directly so it needs no abbreviation;
        # transitivity (4) is derivable from it but emitted too for a faithful frame.
        out.append('axiomatization where r_loeb: '
                   '"(\\<forall>v. r w v \\<longrightarrow> '
                   '(\\<forall>u. r v u \\<longrightarrow> P u) \\<longrightarrow> P v) '
                   '\\<Longrightarrow> (\\<forall>v. r w v \\<longrightarrow> P v)"')
    return out


def _temporal_axioms() -> List[str]:
    """t is the refl+trans (henceforth) relation, matching satisfies_modal's closure."""
    return [
        'axiomatization where t_refl: "t w w"',
        'axiomatization where t_trans: "t w v \\<Longrightarrow> t v u \\<Longrightarrow> t w u"',
    ]


def _next_in_temporal_axiom() -> List[str]:
    """Link the one-step successor n to the henceforth relation t.

    In ``satisfies_modal`` ``Always`` / ``Eventually`` close over the *same*
    one-step ``"temporal"`` relation that ``Next`` reads, so every one-step
    successor is henceforth-reachable and ``Always(P) → Next(P)`` is valid.
    Without this axiom the emitted ``n`` and ``t`` are decoupled and that
    entailment fails, breaking faithfulness; the axiom restores it.
    """
    return ['axiomatization where n_in_t: "n w v \\<Longrightarrow> t w v"']


def _temporal_next_closure_axiom() -> List[str]:
    r"""Pin the henceforth relation ``t`` to the reflexive-transitive CLOSURE of ``n``.

    ``n_in_t`` gives ``n ⊆ t`` and the temporal axioms make ``t`` reflexive+transitive,
    so ``n** ⊆ t``. This adds the converse ``t ⊆ n**`` (``rtranclp n``), so ``t = n**``
    EXACTLY — matching :func:`satisfies_modal`, which reads ``Always`` / ``Eventually``
    over the reflexive-transitive *closure* of the one-step ``"temporal"`` relation.
    Without it ``t`` may be any refl-trans superset of ``n``, and a formula valid only
    because ``t = closure(n)`` (e.g. the temporal induction ``(p ∧ G(p→Xp)) → Gp``) is
    spuriously refutable in the embedding — a **false INVALID** under the runner.
    """
    return ['axiomatization where t_in_nstar: "t w v \\<Longrightarrow> rtranclp n w v"']


def _deontic_axioms() -> List[str]:
    """Standard Deontic Logic KD: the deontic relation is serial."""
    return ['axiomatization where d_serial: "\\<exists>v. d w v"']


def _domain_axioms(mode: str) -> List[str]:
    """existsAt domain-regime axioms (only meaningful when quantifiers occur)."""
    out = []
    if mode in _CONSTANT_MODES:
        out.append('axiomatization where const_dom: "existsAt x w"')
    else:
        # actualist: keep every world's domain non-empty (matches qml nonempty_dom).
        out.append('axiomatization where nonempty_dom: "\\<exists>x. existsAt x w"')
        if mode in ("increasing", "cumulative"):
            out.append('axiomatization where cumul_dom: "existsAt x w \\<Longrightarrow> r w v \\<Longrightarrow> existsAt x v"')
        elif mode == "decreasing":
            out.append('axiomatization where decr_dom: "existsAt x v \\<Longrightarrow> r w v \\<Longrightarrow> existsAt x w"')
        # "varying": no monotonicity axiom.
    return out


def _collect_axioms(sig: "_Sig", frame: str, mode: str,
                    temporal_closure: bool, temporal_def: bool = False) -> List[str]:
    """All ``axiomatization where ...`` lines the theory emits, in emission order.

    Centralised so the proof emitter and :func:`modal_axiom_names` agree on exactly
    which axioms are in scope (the proof must ``using`` precisely these to discharge
    an axiom-dependent validity). When ``temporal_def`` makes ``t = rtranclp n`` a
    definition (Always/Eventually + Next), the temporal/next closure axioms become
    theorems and are omitted.
    """
    use_temporal_def = temporal_def and sig.uses_temporal and sig.needs_next_rel
    axioms: List[str] = []
    if sig.uses_alethic:
        axioms += _frame_axioms(frame)
    if sig.uses_deontic:
        axioms += _deontic_axioms()
    if not use_temporal_def:
        if sig.uses_temporal and temporal_closure:
            axioms += _temporal_axioms()
        # When the one-step relation n co-occurs with Always/Eventually (t) — because
        # Next, Until, or Since is present — link n into t so t and the n-based
        # operators agree (t denotes the closure of the SAME one-step relation the
        # path-search Until/Since and Next read), keeping the oracle-valid
        # Always(P) -> Next(P) and the Always/Until interplay theorems of the theory...
        if sig.uses_temporal and sig.needs_next_rel:
            axioms += _next_in_temporal_axiom()
            # ...and, when t is the closure relation, pin t = n** exactly (not merely a
            # refl-trans superset of n), so satisfies_modal-valid temporal-induction
            # formulas are not spuriously refuted (false INVALID).
            if temporal_closure:
                axioms += _temporal_next_closure_axiom()
    if sig.has_quant:
        axioms += _domain_axioms(mode)
    return axioms


def _proof_lines(tactic: str, axiom_ids: List[str]) -> List[str]:
    """The proof block for ``tactic``, bringing the frame/domain axioms into scope.

    For a ``by``-style tactic (:data:`_BY_TACTICS`) we prepend ``using <axioms>`` so
    ``blast`` / ``auto`` / ``metis`` can actually use them; ``sledgehammer`` / ``oops``
    / ``sorry`` are emitted verbatim.
    """
    body = ISABELLE_TACTICS[tactic]
    if tactic in _BY_TACTICS and axiom_ids:
        return ["  using " + " ".join(axiom_ids), body]
    return [body]


# --------------------------------------------------------------------------- #
# Type declarations for the discovered signature.
# --------------------------------------------------------------------------- #

def _signature_decls(names: "_IsaNames") -> List[str]:
    """Emit ``consts`` declarations for predicates, object constants, functions.

    Draws each constant's name from the de-colliding resolver, so distinct source
    symbols never share a ``consts`` declaration (Isabelle rejects duplicate consts).
    """
    out = []
    for (name, arity), c in sorted(names.pred.items(), key=lambda kv: kv[1]):
        typ = " \\<Rightarrow> ".join(["'a"] * arity + ["i \\<Rightarrow> bool"])
        out.append(f'consts {c} :: "{typ}"')
    for name, c in sorted(names.const.items(), key=lambda kv: kv[1]):
        out.append(f'consts {c} :: "\'a"')
    for (name, arity), c in sorted(names.func.items(), key=lambda kv: kv[1]):
        typ = " \\<Rightarrow> ".join(["'a"] * (arity + 1))
        out.append(f'consts {c} :: "{typ}"')
    return out


# --------------------------------------------------------------------------- #
# Public entry points.
# --------------------------------------------------------------------------- #

def _validate(mode: str, frame: str, tactic: str) -> None:
    if frame not in _FRAMES:
        raise ValueError(
            f"to_isabelle_modal: unknown frame {frame!r} (use one of {sorted(_FRAMES)}).")
    if mode not in _ACTUALIST_MODES and mode not in _CONSTANT_MODES:
        raise ValueError(
            f"to_isabelle_modal: unknown mode {mode!r} "
            f"(use one of {sorted(_ACTUALIST_MODES | _CONSTANT_MODES)}).")
    if tactic not in ISABELLE_TACTICS:
        raise ValueError(
            f"to_isabelle_modal: unknown tactic {tactic!r} "
            f"(use one of {sorted(ISABELLE_TACTICS)}).")


def isabelle_modal_theory(
    formula: Node,
    mode: str = "constant",
    frame: str = "K",
    tactic: str = "sledgehammer",
    theory_name: str = "ModalEmbedding",
    temporal_closure: bool = True,
    proof: Optional[str] = None,
    temporal_def: bool = False,
) -> str:
    """Emit a complete, loadable Isabelle/HOL theory shallow-embedding ``formula``.

    The returned string is a full ``theory <theory_name> imports Main begin ... end``
    that:

    - declares the world type ``i`` and the accessibility relations actually used
      (alethic ``r``; **agent-indexed** epistemic ``rk`` / doxastic ``rb`` of type
      ``'a \\<Rightarrow> i \\<Rightarrow> i \\<Rightarrow> bool``; deontic ``d``; temporal henceforth ``t`` and
      one-step ``n``);
    - defines every lifted operator (``mnot mand mor mimp miff mbox mdia``, the
      agent-indexed ``knows`` / ``believes``, ``obl`` / ``perm``, ``malways`` /
      ``meventually`` / ``mnext``, the ``existsAt``-guarded ``mforall`` / ``mexists``,
      and ``mvalid``) as Isabelle abbreviations;
    - emits the frame axioms for ``frame`` (K/T/S4/S5/KD/KD45), the domain-regime
      axioms for ``mode``, and (when ``temporal_closure``) the refl+trans axioms on
      the temporal relation ``t`` so it denotes the henceforth (closure) relation,
      faithfully to :func:`satisfies_modal`;
    - states the formula as a **real** ``lemma "\\<lfloor> ... \\<rfloor>"`` whose body is the
      *lifted* embedding (not a ``to_unicode_str`` dump in a comment), followed by
      the proof text for ``tactic``.

    Args:
        formula: the modal AST node to embed.
        mode: object-quantifier domain regime — ``constant`` / ``possibilist`` or
            ``varying`` / ``increasing`` / ``cumulative`` / ``decreasing``.
        frame: alethic frame system in {K, T, S4, S5, KD, KD45}.
        tactic: a key of :data:`ISABELLE_TACTICS`. The default ``"sledgehammer"``
            emits a Sledgehammer hook plus ``oops`` so the theory loads without
            claiming a proof; ``"metis"`` / ``"auto"`` / ``"blast"`` / ``"smt"`` emit a
            ``by ...`` proof. For these ``by``-style tactics the proof is prefixed
            with ``using <frame/domain axioms>`` so an axiom-dependent validity
            (T/S4/S5/KD/KD45, temporal closure, domain regime) can actually
            discharge — a bare ``axiomatization`` fact is not in the default claset.
            ``"sorry"`` admits the goal.
        theory_name: the Isabelle theory name (must match the .thy filename).
        proof: an explicit proof block to emit verbatim in place of the ``tactic``
            preset (used by the Isabelle runner to splice in a prove-battery or a
            ``nitpick`` invocation). When ``None`` the ``tactic`` preset is used.
        temporal_closure: when True, constrain ``t`` to be reflexive+transitive so
            ``Always`` / ``Eventually`` denote the henceforth (refl-trans-closure)
            reading of :func:`satisfies_modal`. ``Next`` always uses the one-step
            relation ``n`` regardless.

    Returns:
        The theory text (newline-terminated).

    Note:
        The toolkit only *emits* this theory — it does not run Isabelle or
        Sledgehammer. First-order modal logic is undecidable, so emission proves
        nothing; an external prover must discharge the lemma.
    """
    _validate(mode, frame, tactic)

    sig = _Sig()
    _scan(formula, sig)               # which modalities occur (relation/operator blocks)
    names = _IsaNames(formula)        # de-colliding constant names (decls + usages agree)
    body = _lift(formula, names)  # may raise on SortedQuantifier — do before emitting.

    lines: List[str] = []
    lines.append(f"theory {theory_name}")
    lines.append("  imports Main")
    lines.append("begin")
    lines.append("")
    lines.append("(* Shallow semantical embedding (Benzmüller-style) of a quantified modal *)")
    lines.append(f"(* formula. mode={mode}, frame={frame}, tactic={tactic}. *)")
    lines.append("(* The toolkit EMITS this theory; it does not run Isabelle/Sledgehammer.  *)")
    lines.append("(* First-order modal logic is undecidable: an external prover must close  *)")
    lines.append("(* the lemma. Equality =/<> is an uninterpreted world-relativized         *)")
    lines.append("(* predicate (feq/fneq), NOT primitive HOL identity.                      *)")
    lines.append("")
    lines.append("typedecl i  \\<comment> \\<open>the type of worlds\\<close>")
    lines.append("")

    # Relations + lifted operators for the modalities that actually occur.
    if sig.uses_alethic:
        lines += _alethic_block()
        lines.append("")
    if sig.uses_epistemic:
        lines += _epistemic_block()
        lines.append("")
    if sig.uses_doxastic:
        lines += _doxastic_block()
        lines.append("")
    if sig.uses_deontic:
        lines += _deontic_block()
        lines.append("")
    # When ``temporal_def`` and BOTH Always/Eventually (t) and Next (n) occur, the
    # henceforth relation is DEFINED as the reflexive-transitive closure of n
    # (``t = rtranclp n``) rather than a ``consts`` constrained by axioms — so nitpick
    # can determine t from a candidate n and actually refute non-theorems of the
    # closure fragment. n must be declared before t's definition references it.
    use_temporal_def = temporal_def and sig.uses_temporal and sig.needs_next_rel
    # The one-step relation n is declared once when Next, Until, or Since needs it;
    # the mnext abbreviation only when Next actually occurs.
    if sig.needs_next_rel:
        lines += _next_consts_block()
        if sig.uses_next:
            lines += _next_abbrev_block()
        lines.append("")
    if sig.uses_temporal:
        lines += _temporal_def_block() if use_temporal_def else _temporal_block()
        lines.append("")
    # Inductive least-fixpoint definitions for the binary interval operators; they
    # step over n (declared above), so they follow it.
    if sig.uses_until:
        lines += _until_block()
        lines.append("")
    if sig.uses_since:
        lines += _since_block()
        lines.append("")

    # Connectives + validity (always present).
    lines += _CORE_ABBREVS
    lines.append("")
    if sig.has_quant:
        lines += _quant_block(mode)
        lines.append("")
    lines += _VALID_ABBREV
    lines.append("")

    # Signature of the user's predicates / constants / functions.
    decls = _signature_decls(names)
    if decls:
        lines += decls
        lines.append("")

    # Axioms.
    axioms = _collect_axioms(sig, frame, mode, temporal_closure, temporal_def)
    if axioms:
        lines += axioms
        lines.append("")

    # The real lemma. Its proof brings the frame/domain axioms into scope (see
    # _proof_lines) so an axiom-dependent validity actually discharges; an explicit
    # ``proof`` override (used by the runner's prove-battery / nitpick) wins.
    lines.append(f'lemma modal_goal: "\\<lfloor> {body} \\<rfloor>"')
    if proof is not None:
        lines.append(proof.rstrip("\n"))
    else:
        lines += _proof_lines(tactic, _axiom_names(axioms))
    lines.append("")
    lines.append("end")
    return "\n".join(lines) + "\n"


def modal_axiom_names(
    formula: Node,
    mode: str = "constant",
    frame: str = "K",
    temporal_closure: bool = True,
) -> List[str]:
    """The names of the ``axiomatization`` facts the emitted theory would declare.

    These are exactly the frame / domain / temporal-link axioms in scope for the
    proof of ``modal_goal``. The Isabelle runner needs them to build a ``using
    <axioms> by <method>`` proof (or to know none are required), so this exposes the
    same computation :func:`isabelle_modal_theory` uses internally.
    """
    _validate(mode, frame, "oops")
    sig = _Sig()
    _scan(formula, sig)
    return _axiom_names(_collect_axioms(sig, frame, mode, temporal_closure))


def to_isabelle_modal(
    formula: Node,
    mode: str = "constant",
    frame: str = "K",
    tactic: str = "sledgehammer",
    temporal_closure: bool = True,
    proof: Optional[str] = None,
) -> str:
    """Emit a complete, loadable Isabelle/HOL theory embedding ``formula`` (real lemma).

    This is the genuine replacement for the old skeleton stub: it returns a full
    ``theory ModalEmbedding imports Main begin ... end`` with all lifted operators
    defined as abbreviations and the formula stated as a **real** ``lemma`` (not a
    comment). See :func:`isabelle_modal_theory` for the parameters; this thin
    wrapper fixes ``theory_name="ModalEmbedding"`` to match the historical
    signature ``to_isabelle_modal(formula, mode, frame)``.

    Honesty: the toolkit emits the theory but never runs Isabelle/Sledgehammer.
    First-order modal logic is undecidable, so emission proves nothing — an
    external prover must discharge the lemma. Propositional modal K/T/S4/S5 are
    decidable, but this emitter does not itself decide them.
    """
    return isabelle_modal_theory(
        formula, mode=mode, frame=frame, tactic=tactic,
        theory_name="ModalEmbedding", temporal_closure=temporal_closure, proof=proof)
