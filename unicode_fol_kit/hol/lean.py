r"""Classical FOL/MSFOL and propositional modal-K → **Lean 4** exporter, plus an
optional LIVE elaboration tier through a local Lean 4 toolchain.

This is the Lean counterpart of :mod:`unicode_fol_kit.hol.classical` (THF /
Isabelle) — a first vertical slice, structured the same way, and deliberately
**not** parity with the full Isabelle/THF pair (no relevant/substructural/
many-valued/second-third-order/deepshallow Lean routes yet; those are separate
follow-on items once this pattern is proven). It covers exactly two fragments:

* classical **FOL / MSFOL** (:func:`to_lean_fol`, :func:`to_lean_msfol`), and
* the propositional **modal-K** fragment — Box/Diamond + connectives over
  ground atoms, no frame conditions on the accessibility relation
  (:func:`to_lean_modal_k`).

**Emit-only is the honest scope.** Like :mod:`~unicode_fol_kit.hol.classical`,
the functions above only *emit* a self-contained ``.lean`` source that always
elaborates (the goal is ``sorry``-closed by default): "here is a well-typed
statement", never "proved". The optional live tier below is the other half —
if a local Lean 4 toolchain is installed, :func:`check_theory` actually
*elaborates* the emitted file (catching syntax/typing bugs no string test
can), and :func:`lean_decide_fol` / :func:`lean_decide_modal_k` additionally
try a small tactic battery for a genuine, kernel-checked proof. A file this
module PRESENTS as checked never contains ``sorry``: :class:`LeanBuildResult`
tracks ``uses_sorry`` separately from ``ok`` (a ``sorry``-closed file still
*elaborates*, exit 0), and every ``*_decide_*`` verdict is **VALID only when
the proof is genuinely sorry-free** — never a false "proved". There is no
``INVALID`` verdict here (unlike :mod:`~unicode_fol_kit.hol.isabelle_runner`'s
nitpick-backed refutation): only ``VALID`` / ``UNKNOWN``, exactly the two
outcomes the tactic battery can honestly support without a model finder.

Faithfulness of the encoding
-----------------------------
**The uninterpreted individual type is non-empty by construction, exactly
like Isabelle's ``typedecl``.** A bare Lean ``axiom Ind : Type`` is *not*
non-empty by fiat (unlike Isabelle/HOL's ``typedecl``, which always denotes a
non-empty type) — omitting a witness would silently invalidate classical
schemas that depend on a non-empty domain (e.g. ``(∀x, P x) → ∃x, P x``),
exactly the "approximate silently" failure this project refuses to ship. Every
emitted theory therefore declares

.. code-block:: lean

    axiom Ind : Type
    axiom Ind_nonempty : Nonempty Ind
    instance : Nonempty Ind := Ind_nonempty

— an explicit witness *axiom*, registered as a type-class ``instance`` too so
downstream tactics that need ``Nonempty``/``Inhabited`` search find it. The
propositional modal-K embedding does the same for its Kripke world type
(``World`` / ``World_nonempty``).

**Many-sorted input.** :func:`to_lean_msfol` reduces a many-sorted formula
with :func:`~unicode_fol_kit.fol.nodes.to_fol` (each sort becomes a unary
guard predicate over the single flat ``Ind``, each sorted quantifier is
relativised — ``∀x:S φ ↦ ∀x (S(x) → φ)``, ``∃x:S φ ↦ ∃x (S(x) ∧ φ)``) and
then emits the resulting plain-FOL formula with :func:`to_lean_fol`, **exactly
like** :func:`~unicode_fol_kit.hol.classical.to_isabelle_msfol` /
:func:`~unicode_fol_kit.hol.classical.to_thf_msfol` — this module adds no new
semantics beyond that existing pair. ``Ind`` itself is guaranteed non-empty
(above); an individual per-sort guard predicate is **not** additionally
forced non-empty (the sort could still denote the empty guard in a model), the
same reading the two existing MSFOL exporters already have — sort
non-emptiness is a caller concern (:func:`~unicode_fol_kit.fol.nonempty_sort_axioms`
for the callers that want it, e.g. ``api.prove``), never assumed silently
inside a single-formula translation (see
:func:`~unicode_fol_kit.semantics.kripke.satisfies_modal`'s module docstring
for why: an extra existential baked into a polarity-blind per-node
translation would land under the wrong polarity whenever the sorted node
occurs negated).

**Equality.** By default ``=`` / ``≠`` are the *uninterpreted* predicates
``feq`` / ``fneq`` (not Lean's own ``=``), matching the toolkit-wide HOL
convention (:mod:`~unicode_fol_kit.hol.classical`, ``qml.to_thf_modal``). Pass
``native_equality=True`` to emit Lean's own built-in, congruence-free ``=`` /
``≠`` instead — genuine identity at ``Ind``, so no axioms are needed for it.

**Propositional modal-K.** :func:`to_lean_modal_k` is a Benzmüller-style
shallow embedding, faithful to
:func:`~unicode_fol_kit.semantics.kripke.satisfies_modal` restricted to the
propositional fragment (``Box``/``Diamond`` + connectives over ground atoms
only — no quantifiers, agent-indexed modalities, deontic, or temporal
operators; those raise ``NotImplementedError`` naming the construct) over an
**unconstrained** accessibility relation ``R`` — frame **K**, no ``refl`` /
``trans`` / ... conditions, since this vertical slice covers only K. Box/
Diamond translate the standard clauses ``⟦□φ⟧w = ∀v, R w v → ⟦φ⟧v`` /
``⟦◇φ⟧w = ∃v, R w v ∧ ⟦φ⟧v``, and every distinct ground atom becomes its own
``World → Prop`` valuation axiom. ``tests/test_lean.py`` validates this
encoding two ways: (a) the modal **K axiom** ``□(p→q) → (□p → □q)`` elaborates
*and* has a hand-written, kernel-checked proof (no ``sorry``) — live-checked
against a real Lean 4 install; (b) a known **non**-theorem of K (``□p → p``,
the ``T`` axiom, which needs reflexivity K does not have) is refuted: a
concrete, decidable, two-world instantiation makes Lean's own ``decide``
tactic *prove the goal is false* (not merely "fails to prove it") — so the
encoding is never one Isabelle-style ``INVALID`` verdict shy of a false
positive.

**Lean 4 core only — no Mathlib.** Every fragment above (classical FOL/MSFOL
over ``Classical`` reasoning, propositional modal K) is expressible in bare
Lean 4 core + the ``Classical`` namespace it ships with (``Classical.em`` and
friends — confirmed by hand: this module's own live tests run against a real,
Mathlib-free Lean 4.34 toolchain). Emitted theories always ``open Classical``
so a later, more elaborate hand proof can reach for it. The optional
:data:`DEFAULT_METHODS` battery (``decide`` / ``tauto`` / ``aesop``) reflects
this honestly: ``tauto`` and ``aesop`` are *Mathlib* tactics, so without it
they simply fail to parse ("unknown tactic") and the battery moves on to the
next method — never a crash, never a false ``VALID``. ``decide`` only closes
a goal Lean can find a computable ``Decidable`` instance for; the axiom-based
shallow embeddings above are intentionally *not* decidable (``Ind`` / ``World``
are opaque, uninterpreted types), so in a Mathlib-free environment
:func:`lean_decide_fol` / :func:`lean_decide_modal_k` will typically report
``UNKNOWN`` for a nontrivial goal even when it IS valid — exactly the honest,
incomplete-but-sound behaviour :mod:`~unicode_fol_kit.hol.isabelle_runner`
already documents for its own battery, never a false "proved".

Locating Lean
--------------
:func:`find_lean` looks, in order, at an explicit path, the env var
``UFK_LEAN_HOME``, ``lean`` on ``PATH``, and the standard ``elan`` install
location ``~/.elan/bin`` — the same discovery shape
:func:`~unicode_fol_kit.hol.isabelle_runner.find_isabelle` uses for Isabelle.
:func:`lean_available` is the cheap predicate tests gate on. Nothing in this
module modifies ``PATH`` or a shell profile; a toolchain installed via
``elan-init --no-modify-path`` is still found through ``~/.elan/bin`` or
``UFK_LEAN_HOME``.
"""

from __future__ import annotations

import os
import re
import shutil
import subprocess
import tempfile
import time
import uuid
from dataclasses import dataclass
from typing import Dict, List, Optional, Sequence, Tuple

from ..fol._msfl_nodes import _reduce_nl_nodes
from ..fol._symbol_names import dedupe
from ..fol.nodes import (
    Node, Variable, Constant, Number, Function, Measure,
    Atom, Not, And, Or, Xor, Implies, Iff, Quantifier,
    Box, Diamond, to_fol,
)
from .classical import (
    _signature, _sanitize, _SymbolResolver, _VarResolver, _free_variables,
    _CAT_PRED, _CAT_FUNC, _CAT_CONST, _is_native_eq, _FORALL,
)

__all__ = [
    "to_lean_fol", "to_lean_msfol", "to_lean_modal_k",
    "LeanInstall", "LeanNotAvailable", "LeanBuildResult", "LeanVerdict",
    "find_lean", "lean_available", "check_theory",
    "lean_decide_fol", "lean_decide_modal_k",
    "DEFAULT_METHODS", "VALID", "UNKNOWN",
]


# ===========================================================================
# Lean 4 identifier safety: reserved words + this module's own scaffold names
# ===========================================================================

# Lean 4 keywords / predeclared core identifiers a sanitised source-symbol
# name (e.g. a natural-language predicate literally called "in" or "at")
# could otherwise collide with. Not claimed to be exhaustive of every Lean
# parser token, but covers every keyword class (binders, declarations, macro/
# syntax machinery, control flow, placeholders) plus the handful of lowercase
# core names (`true`/`false`/...) most likely to appear in a translated
# natural-language formula.
_LEAN_RESERVED = frozenset({
    "fun", "let", "in", "do", "at", "with", "where", "from", "have", "show",
    "suffices", "calc", "this", "match", "if", "then", "else", "by",
    "forall", "exists", "nomatch", "rec", "generalizing", "deriving",
    "def", "theorem", "lemma", "axiom", "opaque", "constant", "abbrev",
    "instance", "class", "structure", "inductive", "mutual", "partial",
    "unsafe", "noncomputable", "private", "protected", "scoped", "local",
    "variable", "variables", "universe", "universes", "namespace", "section",
    "end", "open", "import", "extends", "attribute",
    "macro", "macro_rules", "syntax", "elab", "elab_rules", "notation",
    "infix", "infixl", "infixr", "prefix", "postfix",
    "set_option", "run_cmd",
    "sorry", "admit", "native_decide", "stop",
    "for", "while", "return", "try", "catch", "finally", "break", "continue",
    "mut",
    "true", "false", "and", "or", "not", "iff", "eq", "ne",
})


class _LeanNames:
    """Wrap an already-de-collided identifier (from :class:`_SymbolResolver`,
    :class:`_VarResolver`, or a locally synthesised name) into one that ALSO
    avoids Lean 4 reserved words and this emission's own scaffold identifiers
    (``Ind`` / ``World`` / ``R`` / ``goal`` / ...), while staying globally
    injective: two distinct LOGICAL symbols never map to the same output.

    Memoisation is keyed on an explicit, caller-supplied ``key`` that
    identifies the *logical* symbol requesting a name — e.g. ``(category,
    raw_name, arity)`` for a predicate/function/constant (the same key
    :class:`_SymbolResolver` itself uses), ``("var", raw_name)`` for a bound
    variable, or ``("atom", atom_key)`` / ``("world", depth)`` for the modal
    encoding — NEVER the candidate string itself. This distinguishes "the
    same logical symbol requested twice" (which must be idempotent: the
    second request returns the identifier already assigned) from "two
    DIFFERENT logical symbols whose independently-sanitised candidate
    strings just happen to coincide" (which must still be de-collided against
    each other). Caching on the candidate string alone cannot tell these
    apart — a predicate resolved by :class:`_SymbolResolver` and a bound
    variable resolved by the entirely separate :class:`_VarResolver` (or the
    ``w{n}`` Kripke-world counter in :func:`to_lean_modal_k`) run their OWN
    de-collision within their own namespace, so they can and do produce the
    identical candidate string for two distinct symbols (e.g. a predicate
    named ``Foo`` and a bound variable also named ``Foo`` both sanitise to
    ``"foo"``; an atom literally named ``w1`` and the Kripke-world binder at
    depth 1 both produce ``"w1"``) — exactly the scenario this class exists
    to rule out.

    One instance is threaded through a whole emission (declarations first,
    then the formula body), so a synthesised bound-variable name is checked
    against every symbol identifier already declared, not just against other
    bound-variable names — Lean itself tolerates a local binder shadowing a
    top-level ``axiom`` (verified by hand: it elaborates, just silently reads
    the wrong one inside the shadowed scope, or in the modal case fails to
    elaborate at all because the shadowed ``axiom``'s function type is gone),
    so keying only by logical identity, never by the rendered string, is what
    keeps that from being a silent semantic bug.
    """

    def __init__(self, reserved=frozenset()):
        self._used = set(_LEAN_RESERVED) | set(reserved)
        self._map: Dict[object, str] = {}

    def safe(self, key: object, ident: str) -> str:
        """Return the unique Lean identifier for the logical symbol ``key``.

        ``ident`` is that symbol's already-sanitised candidate string (from
        the appropriate resolver). The SAME ``key`` always returns the SAME
        identifier (idempotent); a DIFFERENT ``key`` whose ``ident`` collides
        with one already assigned is de-collided via :func:`dedupe` instead
        of silently reusing it.
        """
        if key in self._map:
            return self._map[key]
        cand = dedupe(ident, self._used)
        self._map[key] = cand
        return cand


# ===========================================================================
# (A) Classical FOL / MSFOL -> Lean 4
# ===========================================================================

_LEAN_BINOP = {And: "∧", Or: "∨", Implies: "→", Iff: "↔"}

_FOL_RESERVED = frozenset({"Ind", "Ind_nonempty", "goal"})


def _lean_term(node: Node, syms: "_SymbolResolver", vars_: "_VarResolver",
               names: "_LeanNames") -> str:
    """Render an individual (``Ind``) term in Lean prefix-application syntax."""
    if isinstance(node, Variable):
        return names.safe(("var", node.name), vars_.token(node.name))
    if isinstance(node, Constant):
        return names.safe((_CAT_CONST, node.name, 0), syms.name(_CAT_CONST, node.name, 0))
    if isinstance(node, Number):
        raw = "n" + str(node.value)
        return names.safe((_CAT_CONST, raw, 0), syms.name(_CAT_CONST, raw, 0))
    if isinstance(node, Function):
        key = (_CAT_FUNC, node.name, len(node.args))
        head = names.safe(key, syms.name(_CAT_FUNC, node.name, len(node.args)))
        args = [_lean_term(a, syms, vars_, names) for a in node.args]
        return "(" + " ".join([head] + args) + ")"
    if isinstance(node, Measure):
        key = (_CAT_FUNC, "measure", 2)
        head = names.safe(key, syms.name(_CAT_FUNC, "measure", 2))
        return ("(" + " ".join([head, _lean_term(node.entity, syms, vars_, names),
                                _lean_term(node.dimension, syms, vars_, names)]) + ")")
    raise NotImplementedError(
        f"to_lean_fol: unsupported term {type(node).__name__} (classical FOL terms only)."
    )


def _lean_formula(node: Node, syms: "_SymbolResolver", vars_: "_VarResolver",
                  names: "_LeanNames", native_equality: bool = False) -> str:
    """Render a classical FOL formula as a Lean ``Prop`` term.

    Connectives use Lean 4's own Unicode notation (``¬ ∧ ∨ → ↔``, all part of
    core, no import needed); quantifiers bind ``Ind`` variables (``∀ x : Ind,
    …`` / ``∃ x : Ind, …``); atoms apply their declared predicate by plain
    juxtaposition. Every predicate / function / constant / variable name is
    routed through the resolvers AND :class:`_LeanNames`, so distinct source
    symbols stay distinct and none collides with a Lean keyword or this
    emission's own scaffold names. Anything outside the classical fragment
    (modal, second-order, many-valued, substructural, lambda) raises
    ``NotImplementedError``.

    With ``native_equality=True``, a binary ``=``/``≠`` atom renders as
    Lean's own infix ``(a = b)`` / ``(a ≠ b)`` instead of the ``feq``/``fneq``
    functor — genuine, axiom-free Lean identity.
    """
    def f(n):
        return _lean_formula(n, syms, vars_, names, native_equality)
    if isinstance(node, Atom):
        if _is_native_eq(node.predicate, len(node.args), native_equality):
            op = "=" if node.predicate == "=" else "≠"
            left = _lean_term(node.args[0], syms, vars_, names)
            right = _lean_term(node.args[1], syms, vars_, names)
            return f"({left} {op} {right})"
        key = (_CAT_PRED, node.predicate, len(node.args))
        head = names.safe(key, syms.name(_CAT_PRED, node.predicate, len(node.args)))
        if not node.args:
            return head
        return "(" + " ".join([head] + [_lean_term(a, syms, vars_, names)
                                        for a in node.args]) + ")"
    if isinstance(node, Not):
        return f"(¬ {f(node.formula)})"
    if type(node) in _LEAN_BINOP:
        op = _LEAN_BINOP[type(node)]
        return f"({f(node.left)} {op} {f(node.right)})"
    if isinstance(node, Xor):
        return f"(¬ ({f(node.left)} ↔ {f(node.right)}))"
    if isinstance(node, Quantifier):
        x = names.safe(("var", node.variable.name), vars_.token(node.variable.name))
        binder = "∀" if node.type in (_FORALL, "forall") else "∃"
        return f"({binder} {x} : Ind, {f(node.formula)})"
    raise NotImplementedError(
        f"to_lean_fol: {type(node).__name__} is outside the classical FOL fragment "
        "supported by the Lean export (no modal / second-order / many-valued / "
        "substructural / lambda). Propositional modal K -> hol.lean.to_lean_modal_k; "
        "every other non-classical logic has no Lean route yet (see the module "
        "docstring: this is a first vertical slice)."
    )


def _lean_signature_decls(formula: Node, syms: "_SymbolResolver", names: "_LeanNames",
                          native_equality: bool = False) -> List[str]:
    """``axiom`` declarations for every predicate / function / constant.

    Individuals live in the single uninterpreted, explicitly-``Nonempty`` type
    ``Ind``; a k-ary predicate has type ``Ind → … → Prop`` and a k-ary
    function ``Ind → … → Ind``. Each declaration uses the resolver-assigned,
    then :class:`_LeanNames`-wrapped identifier, so no two declarations share
    a name and every name matches its usages. A binary ``=``/``≠`` skips its
    declaration when ``native_equality=True`` — Lean's own polymorphic ``=``
    needs no ``axiom``.
    """
    preds, funcs, consts = _signature(formula)
    decls: List[str] = []
    for name, arity in sorted(preds):
        if _is_native_eq(name, arity, native_equality):
            continue
        key = (_CAT_PRED, name, arity)
        ident = names.safe(key, syms.name(_CAT_PRED, name, arity))
        typ = " → ".join(["Ind"] * arity + ["Prop"]) if arity else "Prop"
        decls.append(f"axiom {ident} : {typ}")
    for name, arity in sorted(funcs):
        key = (_CAT_FUNC, name, arity)
        ident = names.safe(key, syms.name(_CAT_FUNC, name, arity))
        typ = " → ".join(["Ind"] * (arity + 1))
        decls.append(f"axiom {ident} : {typ}")
    for name in sorted(consts):
        key = (_CAT_CONST, name, 0)
        ident = names.safe(key, syms.name(_CAT_CONST, name, 0))
        decls.append(f"axiom {ident} : Ind")
    return decls


def to_lean_fol(formula: Node, conjecture: bool = True, native_equality: bool = False,
                proof: str = "sorry") -> str:
    """Emit a complete, self-contained **Lean 4** source for a classical FOL ``formula``.

    Declares the uninterpreted individual type ``Ind`` (with an explicit
    ``Nonempty`` witness — see the module docstring on why that is the one
    real semantic trap here), a typed ``axiom`` for every predicate / function
    / constant in the signature, ``open Classical`` (for a later hand proof
    that needs ``Classical.em`` / ``Classical.byContradiction``), and the
    formula itself as ``theorem goal : … := by`` / ``  <proof>`` (default
    ``proof="sorry"`` — the file always elaborates without claiming a proof,
    Lean's analogue of Isabelle's ``oops``). ``proof`` is the TACTIC BLOCK
    BODY (no leading ``by`` — this function supplies it), one or more
    newline-separated tactics, each re-indented two spaces so a multi-line
    hand proof parses regardless of how the caller indented it. With
    ``conjecture=False`` the formula is instead emitted as ``axiom goal : …``
    — no proof needed, useful for asserting the formula as a hypothesis in a
    larger hand-written problem.

    Free variables in ``formula`` are universally closed before emission
    (matching :func:`~unicode_fol_kit.hol.classical.to_thf_fol` /
    :func:`~unicode_fol_kit.hol.classical.to_isabelle_fol`, which do the
    same). By default, equality ``=`` / ``≠`` becomes the uninterpreted
    predicate ``feq`` / ``fneq`` (see module docstring); pass
    ``native_equality=True`` to instead emit Lean's own built-in ``=`` / ``≠``.

    Classical FOL is *semi-decidable only*: no tactic is guaranteed to close
    every valid goal. This function only emits the file; it does not run
    Lean — see :func:`check_theory` / :func:`lean_decide_fol` for the optional
    live tier.
    """
    formula = _reduce_nl_nodes(formula)   # Contrast -> And, Count -> witnesses
    closed = formula
    for name in reversed(_free_variables(formula)):
        closed = Quantifier(_FORALL, Variable(name), closed)
    syms = _SymbolResolver(closed, native_equality=native_equality)
    vars_ = _VarResolver(_sanitize)
    names = _LeanNames(_FOL_RESERVED)

    lines = [
        "-- Classical FOL embedded into Lean 4 core (no Mathlib) over an",
        "-- uninterpreted, EXPLICITLY NONEMPTY individual type `Ind` and",
        "-- uninterpreted predicates/functions/constants declared as `axiom`s.",
    ]
    preds, _, _ = _signature(closed)
    if any(_is_native_eq(n, a, native_equality) for n, a in preds):
        lines.append("-- '=' / '≠' are Lean's own built-in identity (no axioms needed).")
    else:
        lines.append("-- '=' / '≠' are the uninterpreted predicates feq / fneq, NOT Lean's `=`.")
    lines += [
        "",
        "axiom Ind : Type",
        "axiom Ind_nonempty : Nonempty Ind",
        "instance : Nonempty Ind := Ind_nonempty",
        "",
        "open Classical",
        "",
    ]
    decls = _lean_signature_decls(closed, syms, names, native_equality=native_equality)
    if decls:
        lines += decls
        lines.append("")
    body = _lean_formula(closed, syms, vars_, names, native_equality=native_equality)
    if conjecture:
        lines.append(f"theorem goal : {body} := by")
        lines.extend(f"  {pl}" for pl in proof.split("\n"))
    else:
        lines.append(f"axiom goal : {body}")
    return "\n".join(lines) + "\n"


def to_lean_msfol(formula: Node, conjecture: bool = True, include_sort_facts: bool = True,
                  native_equality: bool = False, proof: str = "sorry") -> str:
    """Emit a **Lean 4** source for a *many-sorted* FOL ``formula`` via guard relativization.

    Each sort becomes a unary guard predicate and each sorted quantifier is
    relativized (``∀x:S φ ↦ ∀x (S(x) → φ)``, ``∃x:S φ ↦ ∃x (S(x) ∧ φ)``) by
    the toolkit's :func:`~unicode_fol_kit.fol.nodes.to_fol`; the resulting
    plain-FOL formula is then emitted with :func:`to_lean_fol` — exactly the
    same reduction :func:`~unicode_fol_kit.hol.classical.to_isabelle_msfol` /
    :func:`~unicode_fol_kit.hol.classical.to_thf_msfol` already use, so this
    adds no new semantics. With ``include_sort_facts=True`` (default) the
    sort-membership facts of any sorted constants are conjoined first. All
    sorts share the single Lean type ``Ind`` — the relativisation, not the
    type system, keeps the sorts apart; see the module docstring for why sort
    non-emptiness (as opposed to ``Ind`` non-emptiness) is a caller concern,
    not assumed here. See :func:`to_lean_fol` for ``native_equality`` / ``proof``.
    """
    return to_lean_fol(to_fol(formula, include_sort_facts=include_sort_facts),
                       conjecture=conjecture, native_equality=native_equality, proof=proof)


# ===========================================================================
# (B) Propositional modal K -> Lean 4
# ===========================================================================

_MODAL_K_ALLOWED = (Atom, Not, And, Or, Xor, Implies, Iff, Box, Diamond)
_MODAL_GROUND_TERM = (Constant, Number, Function)
_MODAL_RESERVED = frozenset({"World", "World_nonempty", "R", "goal"})


def _reject_non_propositional_modal(formula: Node) -> None:
    """Raise ``NotImplementedError`` naming the first node outside the
    propositional modal-K fragment: ``Box``/``Diamond`` + classical
    connectives over GROUND atoms only. A free/bound ``Variable`` (hence any
    ``Quantifier``), an agent-indexed modality (``Knows``/``Believes``/…), or
    a deontic/temporal operator is rejected — the same node-type gate
    :func:`~unicode_fol_kit.hol.isabelle_runner._is_alethic_propositional`
    uses for the analogous Isabelle-side check.
    """
    for n in formula.walk():
        if isinstance(n, _MODAL_K_ALLOWED) or isinstance(n, _MODAL_GROUND_TERM):
            continue
        raise NotImplementedError(
            f"to_lean_modal_k: {type(n).__name__} is outside the propositional "
            "modal-K fragment (Box/Diamond + not/and/or/xor/implies/iff over "
            "GROUND atoms only -- no quantifiers, free variables, agent-indexed "
            "modalities Knows/Believes, or deontic/temporal operators)."
        )


class _ModalAtomNames:
    """Map each DISTINCT ground atom (by its rendered Unicode key,
    ``atom.to_unicode_str()`` — the same key
    :func:`~unicode_fol_kit.semantics.kripke.satisfies_modal` uses) to a
    unique Lean identifier stem, exactly the way :class:`_SymbolResolver`
    de-collides FOL symbols: keyed on the ORIGINAL atom key, not the
    sanitised string, so two semantically distinct atoms that happen to
    sanitise to the same stem (``_sanitize`` is not injective — see its
    docstring) still get distinct identifiers instead of silently colliding.
    """

    def __init__(self):
        self._used: set = set()
        self._map: Dict[str, str] = {}

    def ident(self, atom_key: str) -> str:
        if atom_key in self._map:
            return self._map[atom_key]
        cand = dedupe(_sanitize(atom_key), self._used)
        self._map[atom_key] = cand
        return cand


def _lean_modal_body(node: Node, world: str, counter: List[int],
                     names: "_LeanNames", atoms: "_ModalAtomNames") -> str:
    """Render ``node``'s Kripke truth condition at the Lean world-variable ``world``.

    ``Box``/``Diamond`` allocate a FRESH bound-world name from ``counter``
    (a single, monotonically increasing, whole-formula counter — never reused
    across sibling branches either, so no nested scope can ever need to
    reason about whether reuse was safe), rendering the standard clauses
    ``∀ v, R w v → ⟦φ⟧v`` / ``∃ v, R w v ∧ ⟦φ⟧v``.
    """
    if isinstance(node, Atom):
        atom_key = node.to_unicode_str()
        ident = names.safe(("atom", atom_key), atoms.ident(atom_key))
        return f"({ident} {world})"
    if isinstance(node, Not):
        return f"(¬ {_lean_modal_body(node.formula, world, counter, names, atoms)})"
    if type(node) in _LEAN_BINOP:
        op = _LEAN_BINOP[type(node)]
        left = _lean_modal_body(node.left, world, counter, names, atoms)
        right = _lean_modal_body(node.right, world, counter, names, atoms)
        return f"({left} {op} {right})"
    if isinstance(node, Xor):
        left = _lean_modal_body(node.left, world, counter, names, atoms)
        right = _lean_modal_body(node.right, world, counter, names, atoms)
        return f"(¬ ({left} ↔ {right}))"
    if isinstance(node, Box):
        depth = counter[0]
        counter[0] += 1
        v = names.safe(("world", depth), f"w{depth}")
        inner = _lean_modal_body(node.formula, v, counter, names, atoms)
        return f"(∀ {v} : World, R {world} {v} → {inner})"
    if isinstance(node, Diamond):
        depth = counter[0]
        counter[0] += 1
        v = names.safe(("world", depth), f"w{depth}")
        inner = _lean_modal_body(node.formula, v, counter, names, atoms)
        return f"(∃ {v} : World, R {world} {v} ∧ {inner})"
    raise NotImplementedError(
        f"to_lean_modal_k: unsupported node {type(node).__name__} "
        "(unreachable if _reject_non_propositional_modal ran first)."
    )


def to_lean_modal_k(formula: Node, conjecture: bool = True, proof: str = "sorry") -> str:
    """Emit a **Lean 4** shallow embedding of a propositional modal-**K** ``formula``.

    Declares an uninterpreted, explicitly ``Nonempty`` Kripke world type
    ``World``, an UNCONSTRAINED accessibility relation ``R : World → World →
    Prop`` (frame K — no ``refl``/``trans``/... axioms), and a ``World → Prop``
    valuation ``axiom`` for every distinct ground atom in ``formula``. The
    goal is the formula's validity — true at every world, over any ``R`` and
    any valuation satisfying just those types — ``theorem goal : ∀ w, ⟦formula⟧w
    := by`` / ``  <proof>`` (default ``proof="sorry"``, so the file always
    elaborates without claiming a proof). ``proof`` is the tactic block body
    (no leading ``by``), see :func:`to_lean_fol`. With ``conjecture=False``,
    emits ``axiom goal : ∀ w, ⟦formula⟧w`` instead (no proof needed).

    Only the propositional fragment is supported: ``Box``/``Diamond`` plus the
    classical connectives over GROUND atoms (no quantifiers, agent-indexed
    modalities, or deontic/temporal operators) — anything else raises
    ``NotImplementedError`` naming the construct (see module docstring for
    the two-way validation of this encoding against
    :func:`~unicode_fol_kit.semantics.kripke.satisfies_modal`).

    This function only emits the file; it does not run Lean — see
    :func:`check_theory` / :func:`lean_decide_modal_k` for the optional live tier.
    """
    _reject_non_propositional_modal(formula)
    names = _LeanNames(_MODAL_RESERVED)
    atoms = _ModalAtomNames()

    seen: List[str] = []
    seen_set = set()
    for n in formula.walk():
        if isinstance(n, Atom):
            key = n.to_unicode_str()
            if key not in seen_set:
                seen_set.add(key)
                seen.append(key)

    lines = [
        "-- Propositional modal K embedded into Lean 4 core (no Mathlib): a shallow",
        "-- Kripke embedding faithful to",
        "-- unicode_fol_kit.semantics.kripke.satisfies_modal restricted to the",
        "-- propositional fragment, over frame K (R is UNCONSTRAINED -- no frame",
        "-- conditions). World is EXPLICITLY NONEMPTY, same reasoning as `Ind` in",
        "-- the classical FOL export (see hol.lean's module docstring).",
        "",
        "axiom World : Type",
        "axiom World_nonempty : Nonempty World",
        "instance : Nonempty World := World_nonempty",
        "",
        "open Classical",
        "",
        "axiom R : World → World → Prop",
        "",
    ]
    decls = [f"axiom {names.safe(('atom', key), atoms.ident(key))} : World → Prop"
            for key in seen]
    if decls:
        lines += decls
        lines.append("")

    counter = [1]
    w0 = names.safe(("world", 0), "w0")
    body = _lean_modal_body(formula, w0, counter, names, atoms)
    if conjecture:
        lines.append(f"theorem goal : ∀ {w0} : World, {body} := by")
        lines.extend(f"  {pl}" for pl in proof.split("\n"))
    else:
        lines.append(f"axiom goal : ∀ {w0} : World, {body}")
    return "\n".join(lines) + "\n"


# ===========================================================================
# (C) Optional LIVE tier: elaborate / prove through a local Lean 4 toolchain
# ===========================================================================

class LeanNotAvailable(RuntimeError):
    """Raised when a Lean 4 install is required but none could be located."""


@dataclass(frozen=True)
class LeanInstall:
    """A located Lean 4 installation."""

    lean_exe: str                   # path to the `lean` binary itself
    home: str                       # its containing toolchain/bin directory
    version: Optional[str] = None

    def __str__(self) -> str:
        return f"Lean({self.version or '?'} at {self.lean_exe})"


def _lean_version(exe: str) -> Optional[str]:
    """Return ``lean --version``'s version number, or ``None`` if it fails."""
    try:
        proc = subprocess.run(
            [exe, "--version"], capture_output=True, text=True,
            encoding="utf-8", errors="replace", timeout=10,
        )
    except Exception:
        return None
    if proc.returncode != 0:
        return None
    m = re.search(r"\d+\.\d+\.\d+", proc.stdout or "")
    return m.group(0) if m else (proc.stdout or "").strip() or None


def _validate_lean(path: Optional[str]) -> Optional[LeanInstall]:
    """Turn a candidate path (a `lean` executable, or a dir containing one,
    directly or under `bin/`) into a :class:`LeanInstall`, or ``None``."""
    if not path:
        return None
    ext = ".exe" if os.name == "nt" else ""
    candidates = [path] if os.path.isfile(path) else [
        os.path.join(path, "lean" + ext),
        os.path.join(path, "bin", "lean" + ext),
    ]
    for exe in candidates:
        if os.path.isfile(exe):
            exe = os.path.abspath(exe)
            home = os.path.dirname(exe)
            return LeanInstall(lean_exe=exe, home=home, version=_lean_version(exe))
    return None


_FIND_CACHE: dict = {}


def find_lean(lean_home: Optional[str] = None, *, use_cache: bool = True) -> Optional[LeanInstall]:
    """Locate a Lean 4 installation, or return ``None`` if none is found.

    Search order: ``lean_home`` argument (a `lean` executable, or a directory
    containing one directly or under ``bin/``) -> env ``UFK_LEAN_HOME`` ->
    ``lean`` on ``PATH`` -> the standard ``elan`` bin directory
    ``~/.elan/bin`` (found even when ``elan-init`` was run with
    ``--no-modify-path``, i.e. nothing was put on ``PATH``). The result is
    cached (keyed by the explicit argument); pass ``use_cache=False`` to
    force a fresh lookup.
    """
    key = lean_home or ""
    if use_cache and key in _FIND_CACHE:
        return _FIND_CACHE[key]

    candidates: List[str] = []
    if lean_home:
        candidates.append(lean_home)
    v = os.environ.get("UFK_LEAN_HOME")
    if v:
        candidates.append(v)
    exe = shutil.which("lean")
    if exe:
        candidates.append(exe)
    ext = ".exe" if os.name == "nt" else ""
    candidates.append(os.path.join(os.path.expanduser("~"), ".elan", "bin", "lean" + ext))

    found: Optional[LeanInstall] = None
    seen = set()
    for c in candidates:
        ac = os.path.abspath(c) if c else c
        if ac in seen:
            continue
        seen.add(ac)
        inst = _validate_lean(c)
        if inst:
            found = inst
            break
    if use_cache:
        _FIND_CACHE[key] = found
    return found


def lean_available(lean_home: Optional[str] = None) -> bool:
    """``True`` iff a Lean 4 installation can be located (cheap; cached)."""
    return find_lean(lean_home) is not None


_SORRY_RE = re.compile(r"declaration uses[^\n]*sorry")


@dataclass
class LeanBuildResult:
    """Outcome of elaborating one self-contained ``.lean`` file.

    ``ok`` is ``True`` iff ``lean`` exits 0 — the file **elaborates** (every
    declaration type-checks), which is true for a ``sorry``-closed goal too.
    ``uses_sorry`` is set when the (successful) elaboration warned that a
    declaration used ``sorry`` — Lean's own signal that a "proof" is not one.
    :attr:`proved` (and truthiness) is the honest, stronger claim: elaborates
    AND is genuinely sorry-free.
    """

    ok: bool
    exit_code: int
    output: str
    theory_name: str
    elapsed: float
    uses_sorry: bool = False

    @property
    def proved(self) -> bool:
        return self.ok and not self.uses_sorry

    def __bool__(self) -> bool:
        return self.proved


def check_theory(lean_source: str, theory_name: str, *,
                 install: Optional[LeanInstall] = None,
                 timeout: float = 120.0,
                 keep: bool = False) -> LeanBuildResult:
    """Elaborate one self-contained Lean 4 source file and report the outcome.

    Writes ``lean_source`` to ``<theory_name>.lean`` in a scratch directory
    and runs bare ``lean <file>.lean`` on it (no ``lakefile``/project needed:
    the classical-FOL and modal-K fragments this module emits use only Lean 4
    core + ``Classical``, confirmed by hand against a real toolchain — see
    module docstring). ``ok`` is ``True`` iff the process exits 0.

    Args:
        lean_source: the full file text (as :func:`to_lean_fol` et al. emit).
        theory_name: the file's base name (without ``.lean``) — also used as
            a scratch-directory-local label.
        install: a :class:`LeanInstall`; located via :func:`find_lean` when
            ``None``.
        timeout: wall-clock subprocess timeout, in seconds.
        keep: keep the scratch directory (for debugging) instead of deleting it.

    Raises:
        LeanNotAvailable: if no Lean 4 installation can be located.
    """
    install = install or find_lean()
    if install is None:
        raise LeanNotAvailable(
            "No Lean 4 installation found. Set UFK_LEAN_HOME, put `lean` on PATH, "
            "or install elan (https://leanprover-community.github.io/get_started.html) "
            "with `elan-init --no-modify-path -y --default-toolchain stable`.")

    work = tempfile.mkdtemp(prefix="ufk_lean_")
    try:
        path = os.path.join(work, theory_name + ".lean")
        with open(path, "w", encoding="utf-8") as f:
            f.write(lean_source)
        t0 = time.perf_counter()
        try:
            proc = subprocess.run(
                [install.lean_exe, path], capture_output=True, text=True,
                encoding="utf-8", errors="replace", timeout=timeout, cwd=work,
            )
            code = proc.returncode
            output = (proc.stdout or "") + (proc.stderr or "")
        except subprocess.TimeoutExpired as e:
            out = (e.stdout or "") + (e.stderr or "")
            if isinstance(out, bytes):
                out = out.decode("utf-8", "replace")
            code, output = 124, out + f"\n[runner] wall-clock timeout after {timeout}s\n"
        elapsed = time.perf_counter() - t0
        return LeanBuildResult(
            ok=(code == 0), exit_code=code, output=output, theory_name=theory_name,
            elapsed=elapsed, uses_sorry=bool(_SORRY_RE.search(output)),
        )
    finally:
        if not keep:
            shutil.rmtree(work, ignore_errors=True)


# --------------------------------------------------------------------------- #
# Deciding validity through Lean: a small, honest tactic battery.
# --------------------------------------------------------------------------- #

VALID = "valid"
UNKNOWN = "unknown"

# `decide` is Lean 4 core (only closes a goal with a synthesizable Decidable
# instance -- the axiom-based embeddings above are intentionally NOT
# decidable, see module docstring). `tauto` / `aesop` are MATHLIB tactics:
# without Mathlib installed they fail to PARSE ("unknown tactic"), which
# check_theory reports as ok=False like any other failed attempt -- the
# battery just moves on, never a crash, never a false VALID.
DEFAULT_METHODS: Tuple[str, ...] = ("decide", "tauto", "aesop")


@dataclass
class LeanVerdict:
    """Result of trying to prove a formula's validity through a Lean tactic battery.

    ``status`` is ``"valid"`` (some method closed the goal with a genuinely
    sorry-free proof) or ``"unknown"`` (no method in the battery did, within
    budget) — there is no ``"invalid"`` here (see module docstring): this
    battery can certify a proof but not construct a countermodel, so
    "unknown" is the only honest outcome for a formula it cannot close,
    valid or not.
    """

    status: str
    method: Optional[str] = None
    output: str = ""
    elapsed: float = 0.0

    @property
    def is_valid(self) -> bool:
        return self.status == VALID

    @property
    def is_unknown(self) -> bool:
        return self.status == UNKNOWN

    def __bool__(self) -> bool:
        return self.status == VALID

    def __str__(self) -> str:
        extra = f" (by {self.method})" if self.status == VALID and self.method else ""
        return f"LeanVerdict[{self.status}{extra}]"


def _run_battery(emit, methods: Sequence[str], timeout: float,
                 install: Optional[LeanInstall]) -> LeanVerdict:
    install = install or find_lean()
    if install is None:
        raise LeanNotAvailable(
            "No Lean 4 installation found. Set UFK_LEAN_HOME, put `lean` on PATH, "
            "or install elan (https://leanprover-community.github.io/get_started.html).")
    for m in methods:
        tok = "G" + uuid.uuid4().hex[:8]
        src = emit(proof=m)
        r = check_theory(src, tok, install=install, timeout=timeout)
        if r.proved:
            return LeanVerdict(status=VALID, method=m, output=r.output, elapsed=r.elapsed)
    return LeanVerdict(status=UNKNOWN)


def lean_decide_fol(
    formula: Node, *,
    msfol: bool = False,
    native_equality: bool = False,
    methods: Sequence[str] = DEFAULT_METHODS,
    timeout: float = 60.0,
    install: Optional[LeanInstall] = None,
) -> LeanVerdict:
    """Try to prove a classical FOL (or MSFOL) formula's validity via a Lean tactic battery.

    Emits :func:`to_lean_fol` (or :func:`to_lean_msfol` when ``msfol=True``)
    once per method in ``methods``, each time with that method as the tactic
    (``proof=method``), and returns the first genuinely sorry-free success as
    :data:`VALID` — or :data:`UNKNOWN` if none of them close it
    (see :class:`LeanVerdict` and the module docstring for why there is no
    ``INVALID`` outcome, and why ``UNKNOWN`` is the expected result in a
    Mathlib-free environment for most nontrivial formulas).

    Args:
        formula: the FOL AST node.
        msfol: emit the many-sorted embedding instead of plain FOL.
        native_equality: render ``=`` / ``≠`` as Lean identity instead of the
            uninterpreted ``feq`` / ``fneq``.
        methods / timeout / install: as for :func:`check_theory`; ``methods``
            defaults to :data:`DEFAULT_METHODS`.

    Raises:
        LeanNotAvailable: if no Lean 4 installation can be located.
    """
    emit_fn = to_lean_msfol if msfol else to_lean_fol

    def emit(proof: str) -> str:
        return emit_fn(formula, native_equality=native_equality, proof=proof)

    return _run_battery(emit, methods, timeout, install)


def lean_decide_modal_k(
    formula: Node, *,
    methods: Sequence[str] = DEFAULT_METHODS,
    timeout: float = 60.0,
    install: Optional[LeanInstall] = None,
) -> LeanVerdict:
    """Try to prove a propositional modal-K formula's validity via a Lean tactic battery.

    Emits :func:`to_lean_modal_k` once per method in ``methods`` and returns
    the first genuinely sorry-free success as :data:`VALID`, else
    :data:`UNKNOWN` — exactly like :func:`lean_decide_fol` (see there, and
    the module docstring, for why there is no ``INVALID`` outcome).

    Args:
        formula: the modal AST node (propositional fragment only — see
            :func:`to_lean_modal_k`).
        methods / timeout / install: as for :func:`lean_decide_fol`.

    Raises:
        LeanNotAvailable: if no Lean 4 installation can be located.
        NotImplementedError: propagated from :func:`to_lean_modal_k` for a
            construct outside the propositional modal-K fragment.
    """
    def emit(proof: str) -> str:
        return to_lean_modal_k(formula, proof=proof)

    return _run_battery(emit, methods, timeout, install)
