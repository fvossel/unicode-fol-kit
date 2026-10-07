r"""Free logic → HOL export: TPTP **THF** problems and Isabelle/HOL theories.

Free logic (:mod:`unicode_logic_kit.semantics.free_logic`) drops classical FOL's
assumption that every term denotes an *existing* individual: quantifiers range
over an *inner* domain of existing objects, while a constant or function term may
denote an *outer* (merely possible) object, or fail to denote at all. This module
embeds that into HOL the same way :mod:`unicode_logic_kit.hol.classical` embeds
classical MSFOL — by GUARD-RELATIVIZATION — using **two** uninterpreted unary
guard predicates over a single flat individual type ``e``:

* ``D(t)`` — "``t`` denotes" (some object of the outer domain);
* ``E!(t)`` — "``t`` exists" (an object of the INNER domain; ``E!`` is strictly
  narrower than ``D``, tied together by the axiom ``E!(x) → D(x)``).

The translation, matching :func:`~unicode_logic_kit.semantics.free_logic.free_satisfies`
clause by clause:

* an ordinary atom ``P(t1, …, tn)`` becomes ``D*(t1) ∧ … ∧ D*(tn) ∧ P(t1, …, tn)``
  (mirrors ``_atom``'s "non-denoting ⇒ false" reading — a real free-logic
  ``NOT``, so this is NOT the same as classically negating the un-guarded atom).
  ``D*`` applies ``D`` to the term AND to every compound subterm of it,
  ``D*(f(s)) = D*(s) ∧ D(f(s))``: ``free_logic._term_value`` makes ``f(s)``
  non-denoting whenever ``s`` is, while a HOL function is total and could map a
  non-denoting argument's carrier value into ``D``;
* the object-language existence predicate ``E!(t)`` — the SAME predicate
  :data:`~unicode_logic_kit.semantics.free_logic._EXISTS_PRED` names — is emitted
  as the guard predicate itself, guarded only by ``D*`` of the proper subterms
  of ``t`` (bare for a variable or constant: with the tie ``E!(x) → D(x)`` it
  already reads "``t`` denotes AND is existing");
* ``=`` is native HOL identity under the same guard,
  ``s = t ↦ D*(s) ∧ D*(t) ∧ s = t``; under ``policy="positive"`` a *self*-identity
  atom ``t = t`` (the SAME term written twice) is exempted from the guard and
  emitted bare (mirrors ``_atom``'s ``policy == "positive"`` carve-out for the
  non-denoting branch). ``≠`` is translated as the negation of the (possibly
  exempted) ``=`` translation, matching ``_atom``'s own ``eq`` / ``not eq``
  symmetry between the two;
* a quantifier is relativized to ``E!``: ``∀x φ ↦ ∀x. E!(x) → φ``,
  ``∃x φ ↦ ∃x. E!(x) ∧ φ`` — the same shape
  :func:`~unicode_logic_kit.hol.classical`'s MSFOL sort-relativization uses, with
  ``E!`` playing the role of the sort guard.

The tie ``E!(x) → D(x)`` is the ONLY background fact. There is deliberately no
``∃x. E!(x)``: an empty inner domain is a legitimate free-logic model
(:func:`~unicode_logic_kit.semantics.free_logic.free_is_valid` searches it by
default), so ``(∀x P(x)) → ∃x P(x)`` must come out invalid here as well. The tie
is a THF ``axiom`` and, in Isabelle, a **premise of the goal**, never a
persistent ``axiomatization`` fact: exactly like
:mod:`~unicode_logic_kit.hol.isabelle_conditional`'s ``nested Sel`` premise, this
lets nitpick construct ``D``/``E!`` itself when searching for a countermodel and
certify it as *genuine* — an ``axiomatization`` would downgrade that to
``quasi_genuine`` (nitpick cannot verify an axiomatised fact's consistency) and
lose the refutation half of the decision procedure.

**Why the embedding is faithful in both directions.** A :class:`FreeModel`
becomes a HOL model over ``outer ∪ {⊥}``: ``D`` is ``outer``, ``E!`` is
``existing``, and a non-denoting constant as well as every undefined or
``⊥``-involving function value is ``⊥``; then ``D*(t)`` holds exactly when ``t``
denotes, and the guarded formula has ``free_holds``'s truth value. Conversely a
HOL model gives a :class:`FreeModel` with ``outer = D`` (plus one fresh
non-existing object if ``D`` is empty — no formula can observe it),
``existing = E!`` (inside ``D`` by the tie), a constant denoting its HOL value iff
that value lies in ``D``, and a function table defined exactly where the
arguments and the value lie in ``D``; by induction ``D*(t)`` holds iff ``t``
denotes there, with the same value. So a HOL proof certifies a free-logic
validity, and a genuine HOL countermodel is a free-logic countermodel.

**Equality.** ``=`` is the target format's own identity (THF's infix
``( S = T )``, Isabelle's polymorphic ``(s = t)``), never an uninterpreted
``feq`` predicate: ``free_logic._atom`` compares the referents of two denoting
terms by identity, and the ``D*`` guard already covers every non-denoting case.
An uninterpreted ``feq`` would let nitpick certify a "countermodel" to
``∀x ∀y ((x = y ∧ P(x)) → P(y))``, which is free-logically valid. This departs
on purpose from :mod:`~unicode_logic_kit.hol.classical`'s default export, whose
documented reading of ``=`` is an uninterpreted predicate unless
``native_equality=True``; the order glyphs ``< > ≤ ≥`` stay uninterpreted
predicates here, as they are ordinary predicates to ``free_holds``.

**Scope.** Classical connectives (``¬ ∧ ∨ ⊕ → ↔``), quantifiers, and atoms over
variable / constant / number / function terms only — exactly the fragment
:func:`~unicode_logic_kit.semantics.free_logic.free_satisfies` interprets. Modal,
second-order, Łukasiewicz, substructural and lambda nodes are outside free
logic's own scope and raise ``NotImplementedError`` by name, never silently
approximated.

**``policy="supervaluation"``.** Refused with ``NotImplementedError`` from every
entry point in this module. Supervaluationist truth is a property of a whole
MODEL's set of truth-value GAPS (true under every classical completion of that
specific model — see the ``semantics.free_logic`` module docstring), not a fact
derivable from a single formula's guarded translation the way negative/positive
are: encoding it soundly would need second-order quantification over per-model
gap assignments, a different and much larger undertaking this module does not
fold in. Use :func:`~unicode_logic_kit.semantics.free_logic.free_holds` with
``policy="supervaluation"`` directly instead.

**Honesty / scope.** This module only *emits* problems and theories; it does
**not** run Leo-III, Satallax, Vampire, Isabelle, or Sledgehammer. The embedded
logic is first-order, so it is semi-decidable only, same as
:mod:`~unicode_logic_kit.hol.classical`.

Public API: :func:`to_thf_free`, :func:`to_isabelle_free`, :func:`free_theory`.
"""

from typing import Dict, List, Optional, Tuple

from ..fol._fol_nodes import constant_name_to_ascii
from ..fol._numeral_symbols import numerals_as_constants, prefixed_numeral_name
from ..fol._symbol_names import dedupe
from ..fol._truth_constants import truth_value
from ..fol.nodes import (
    Node, Variable, Constant, Number, Function,
    Atom, Not, And, Or, Xor, Implies, Iff, Quantifier,
)
from .classical import _refuse_open_assertion

#: The object-language existence predicate — the SAME name
#: :mod:`~unicode_logic_kit.semantics.free_logic` reserves for it
#: (``_EXISTS_PRED``) and this module's own quantifier/E!-guard.
_EXISTS_PRED = "E!"

#: This module's own denotation guard. ``semantics.free_logic`` has no surface
#: syntax for it, and — UNLIKE ``_EXISTS_PRED``/``"E!"`` — no special meaning
#: for it AT ALL: it is purely an artefact of this HOL translation, invisible
#: to :func:`~unicode_logic_kit.semantics.free_logic.free_holds`. Named ``"D!"``
#: (bang-suffixed, matching ``_EXISTS_PRED``'s own convention), NOT bare
#: ``"D"``: a user formula plausibly has its OWN ordinary predicate named a
#: single letter like ``D`` (e.g. "Dog"/"Drinks" abbreviated), and that must
#: stay a distinct, un-guarded symbol rather than being silently reinterpreted
#: as this guard. A formula that itself uses the reserved ``"D!"`` name
#: (unreachable from the parser, but constructible directly as an AST) is
#: REFUSED with a ``ValueError`` by :func:`_guard_atom`: to ``free_holds`` such
#: an atom is an ordinary predicate, so merging it with the guard would
#: silently change its meaning.
_DENOTES_PRED = "D!"

# Comparison glyphs and the two guard predicates get valid, collision-priority
# THF/Isabelle identifiers (the SAME flt/fgt/fle/fge stems as classical.py's
# _PRED_ALIAS, extended with the guard predicates' own stems). "=" is absent on
# purpose: it is always printed as native identity, and "≠" is rewritten to
# the negation of "=" before printing (see the module docstring's Equality).
_PRED_ALIAS = {
    "<": "flt", ">": "fgt", "≤": "fle", "≥": "fge",
    _DENOTES_PRED: "denotes", _EXISTS_PRED: "existsBang",
}

_FORALL = "∀"
_EXISTS = "∃"

_POLICIES = ("negative", "positive", "supervaluation")


def _check_policy(policy: str, who: str) -> None:
    """Validate ``policy``; refuse ``"supervaluation"`` loudly (see module docstring)."""
    if policy == "supervaluation":
        raise NotImplementedError(
            f"{who}: policy='supervaluation' has no guarded-translation reading. "
            "Supervaluationist truth is a property of a MODEL's set of gap atoms "
            "(true under every classical completion of THAT model), not a fact "
            "derivable from a single formula's guarded translation the way "
            "negative/positive are -- encoding it soundly would need second-order "
            "quantification over per-model gap assignments. Use "
            "semantics.free_logic.free_holds(..., policy='supervaluation') instead.")
    if policy not in _POLICIES:
        raise ValueError(
            f"{who}: unknown policy {policy!r} (negative / positive; "
            "supervaluation is refused with NotImplementedError, see above).")


# ===========================================================================
# The guard rewrite: free-logic AST -> classical FOL AST over D / E!
# ===========================================================================

def _denotes(term: Node) -> Node:
    """``D*(t)`` — ``t`` denotes: ``D`` of ``t`` and of every compound subterm.

    ``D*(f(s1, …, sn)) = D*(s1) ∧ … ∧ D*(sn) ∧ D(f(s1, …, sn))``, mirroring
    ``free_logic._term_value``: a function term is non-denoting as soon as one
    argument is, whatever the (total) HOL function does with that argument's
    carrier value. A variable, constant or number is guarded by ``D`` alone.
    """
    guard: Node = Atom(_DENOTES_PRED, [term])
    if isinstance(term, Function):
        for arg in reversed(term.args):
            guard = And(_denotes(arg), guard)
    return guard


def _is_identity(node: Node) -> bool:
    """True for an ``s = t`` atom, which both printers render as native identity.

    See the module docstring's **Equality** section: identity of referents is
    what ``free_logic._atom`` computes once both sides denote, and the ``D*``
    guard handles every non-denoting case.
    """
    return isinstance(node, Atom) and node.predicate == "=" and len(node.args) == 2


def _guard_atom(atom: Atom, policy: str) -> Node:
    """Translate one atom per the module docstring's clause-by-clause table."""
    if atom.predicate == _DENOTES_PRED:
        raise ValueError(
            f"hol.free: {_DENOTES_PRED!r} is reserved for the denotation guard of "
            "this embedding; to free_holds it would be an ordinary predicate, so "
            "rename that predicate.")
    if atom.predicate == _EXISTS_PRED and len(atom.args) == 1:
        # E! is genuinely the free-logic existence predicate (free_holds's own
        # _EXISTS_PRED special case): E!(t) is true iff t denotes an existing
        # object. With the tie E!(x) -> D(x), only the PROPER subterms of t
        # still need their D* guard.
        term = atom.args[0]
        guarded: Node = atom
        if isinstance(term, Function):
            for arg in reversed(term.args):
                guarded = And(_denotes(arg), guarded)
        return guarded
    if atom.predicate == "≠" and len(atom.args) == 2:
        # _atom's own eq/not-eq symmetry: "≠" is always the negation of what
        # "=" would return for the SAME arguments (both policies, both the
        # denoting and non-denoting branches) — see the module docstring.
        return Not(_guard_atom(Atom("=", atom.args), policy))
    if (atom.predicate == "=" and len(atom.args) == 2 and policy == "positive"
            and atom.args[0] == atom.args[1]):
        # Positive free logic: self-identity (the literal SAME term twice)
        # holds unconditionally -- _atom's policy == "positive" carve-out. No
        # D-guard is added; the printers render it as native identity, which
        # is reflexively true.
        return atom
    if not atom.args:
        return atom                        # nothing to guard
    guarded: Node = atom
    for term in reversed(atom.args):
        guarded = And(_denotes(term), guarded)
    return guarded


def _guard(node: Node, policy: str) -> Node:
    """Recursively translate ``node`` into the guarded classical FOL AST.

    Reused, unchanged, by both :func:`to_thf_free` and :func:`to_isabelle_free`
    (and, through them, :func:`free_theory`) — a single guard rewrite that both
    printers render, so the two formats can never drift on what "guarded" means.
    """
    if isinstance(node, Atom):
        return _guard_atom(node, policy)
    if isinstance(node, Not):
        return Not(_guard(node.formula, policy))
    if isinstance(node, And):
        return And(_guard(node.left, policy), _guard(node.right, policy))
    if isinstance(node, Or):
        return Or(_guard(node.left, policy), _guard(node.right, policy))
    if isinstance(node, Xor):
        return Xor(_guard(node.left, policy), _guard(node.right, policy))
    if isinstance(node, Implies):
        return Implies(_guard(node.left, policy), _guard(node.right, policy))
    if isinstance(node, Iff):
        return Iff(_guard(node.left, policy), _guard(node.right, policy))
    if isinstance(node, Quantifier):
        body = _guard(node.formula, policy)
        exists_here = Atom(_EXISTS_PRED, [node.variable])
        if node.type in (_FORALL, "forall"):
            return Quantifier(_FORALL, node.variable, Implies(exists_here, body))
        if node.type in (_EXISTS, "exists"):
            return Quantifier(_EXISTS, node.variable, And(exists_here, body))
        raise ValueError(f"hol.free: unknown quantifier type {node.type!r}.")
    raise NotImplementedError(
        f"hol.free: {type(node).__name__} is outside the free-logic fragment this "
        "export covers -- classical connectives (not/and/or/xor/implies/iff), "
        "quantifiers, and atoms over variable/constant/number/function terms "
        "only, matching semantics.free_logic.free_satisfies. Modal / second-order "
        "/ Łukasiewicz / substructural / lambda nodes have no free-logic reading "
        "here."
    )


def _free_variables(formula: Node) -> List[str]:
    """Names of variables occurring free in ``formula`` (first-occurrence order).

    ``Quantifier`` binds its variable; everything else is structural. Mirrors
    :func:`unicode_logic_kit.hol.classical._free_variables`, restricted to the
    node types this module's guard rewrite supports.
    """
    out: List[str] = []
    seen = set()

    def rec(node: Node, bound: frozenset) -> None:
        if isinstance(node, Variable):
            if node.name not in bound and node.name not in seen:
                seen.add(node.name)
                out.append(node.name)
            return
        if isinstance(node, Quantifier):
            rec(node.formula, bound | {node.variable.name})
            return
        for child in node._child_nodes():
            rec(child, bound)

    rec(formula, frozenset())
    return out


def _close(formula: Node) -> Node:
    """Universally close every free variable of ``formula`` (deterministic order).

    Mirrors :func:`unicode_logic_kit.hol.classical.to_thf_fol`'s own closure step:
    TPTP/Isabelle formula roles do not admit free variables, and closing BEFORE
    :func:`_guard` runs means the closure-introduced quantifiers get the SAME
    ``E!``-relativization as every other quantifier in the formula.
    """
    closed = formula
    for name in reversed(_free_variables(formula)):
        closed = Quantifier(_FORALL, Variable(name), closed)
    return closed


# ===========================================================================
# Shared: name sanitisation and signature extraction
# ===========================================================================

def _sanitize(name: str) -> str:
    """Lower-case-initial ASCII alnum/underscore functor stem for THF/Isabelle.

    Structurally identical to
    :func:`unicode_logic_kit.hol.classical._sanitize` (see there for the full
    rationale): equality/comparison glyphs and the two guard predicates map
    through ``_PRED_ALIAS`` first; every other name is transliterated to ASCII
    via :func:`~unicode_logic_kit.fol._fol_nodes.constant_name_to_ascii`, filtered
    to alnum-or-underscore, and lower-cased at the initial character (THF/
    Isabelle both read an upper-case initial as a VARIABLE, not a constant).
    De-collision across distinct source symbols is :class:`_SymbolResolver`'s
    job, not this function's — never emit its output directly for a
    declaration or a usage.
    """
    if name in _PRED_ALIAS:
        return _PRED_ALIAS[name]
    ascii_name = constant_name_to_ascii(name)
    safe = "".join(c if (c.isalnum() or c == "_") else "_" for c in ascii_name)
    if not safe:
        return "p"
    if safe[0].isdigit():
        safe = "p" + safe
    return safe[:1].lower() + safe[1:]


def _signature(formula: Node):
    """Collect ``(preds, funcs, consts)`` with arities from the GUARDED ``formula``.

    Same shape as :func:`unicode_logic_kit.hol.classical._signature`. ``D`` and
    ``E!`` are always FORCED into ``preds`` (arity 1) regardless of whether they
    happen to occur in this particular formula, because the tie axiom
    (``E!(x) -> D(x)``) references both of them unconditionally — see
    :func:`to_thf_free` / :func:`to_isabelle_free`. Identity atoms are native
    and need no declaration.
    """
    preds, funcs, consts = set(), set(), set()
    for n in formula.walk():
        if isinstance(n, Atom):
            if not _is_identity(n) and truth_value(n) is None:
                preds.add((n.predicate, len(n.args)))
        elif isinstance(n, Function):
            funcs.add((n.name, len(n.args)))
        elif isinstance(n, Constant):
            consts.add(n.name)
        elif isinstance(n, Number):
            consts.add("n" + str(n.value))
    preds |= {(_DENOTES_PRED, 1), (_EXISTS_PRED, 1)}
    return preds, funcs, consts


# ===========================================================================
# Global symbol resolver — DISTINCT source symbols map to DISTINCT identifiers
# ===========================================================================

_CAT_PRED = "pred"
_CAT_FUNC = "func"
_CAT_CONST = "const"


class _SymbolResolver:
    """Assign a UNIQUE, valid emitted identifier to every source symbol.

    Structurally identical to
    :class:`unicode_logic_kit.hol.classical._SymbolResolver` (see there for the
    full rationale): keyed by ``(category, raw_name, arity)``, so a predicate
    used at two arities — or a predicate/function/constant sharing a raw name —
    gets distinct identifiers. The ``_PRED_ALIAS`` targets (``flt``/``fgt``/…
    and ``D``/``E!``'s own ``denotes``/``existsBang`` stems) are assigned FIRST,
    so they claim their natural stem and a colliding user symbol (e.g. a
    predicate literally named ``D``) is de-collided away from them instead of
    the other way round.
    """

    def __init__(self, formula: Node):
        self._used = set()
        self._map: Dict[Tuple[str, str, int], str] = {}
        preds, funcs, consts = _signature(formula)
        for name, arity in sorted(preds):
            if name in _PRED_ALIAS:
                self._assign(_CAT_PRED, name, arity)
        for name, arity in sorted(preds):
            if name not in _PRED_ALIAS:
                self._assign(_CAT_PRED, name, arity)
        for name, arity in sorted(funcs):
            self._assign(_CAT_FUNC, name, arity)
        for name in sorted(consts):
            self._assign(_CAT_CONST, name, 0)

    def _assign(self, category: str, raw: str, arity: int) -> str:
        key = (category, raw, arity)
        if key in self._map:
            return self._map[key]
        cand = dedupe(_sanitize(raw), self._used)
        self._map[key] = cand
        return cand

    def name(self, category: str, raw: str, arity: int) -> str:
        """Return the unique emitted identifier for ``(category, raw, arity)``."""
        key = (category, raw, arity)
        if key not in self._map:
            return self._assign(category, raw, arity)
        return self._map[key]


class _VarResolver:
    """Map DISTINCT bound/free variable names to DISTINCT emitted variable tokens.

    Identical to :class:`unicode_logic_kit.hol.classical._VarResolver`: THF
    upper-cases variable tokens, so two source names differing only by case
    would otherwise collide on one token. ``used`` is the set of tokens a variable
    must not take (shared, not copied): the Isabelle export passes the tokens of the
    theory's constants, functions and predicates, because a binder shadows a
    constant of its own name inside its scope.
    """

    def __init__(self, render, used=None):
        self._render = render
        self._used = set() if used is None else used
        self._map: Dict[str, str] = {}

    def token(self, raw: str) -> str:
        if raw in self._map:
            return self._map[raw]
        cand = dedupe(self._render(raw), self._used)
        self._map[raw] = cand
        return cand


# ===========================================================================
# (A) TPTP THF export
# ===========================================================================

def _thf_term(node: Node, syms: "_SymbolResolver", vars_: "_VarResolver") -> str:
    """Render an individual (``$i``) term in THF applicative (``@``) form."""
    if isinstance(node, Variable):
        return vars_.token(node.name)
    if isinstance(node, Constant):
        return syms.name(_CAT_CONST, node.name, 0)
    if isinstance(node, Number):
        return syms.name(_CAT_CONST, "n" + str(node.value), 0)
    if isinstance(node, Function):
        head = syms.name(_CAT_FUNC, node.name, len(node.args))
        return "( " + " @ ".join([head] + [_thf_term(a, syms, vars_) for a in node.args]) + " )"
    raise NotImplementedError(
        f"to_thf_free: unsupported term {type(node).__name__} (free-logic terms: "
        "variable / constant / number / function only)."
    )


def _thf_formula(node: Node, syms: "_SymbolResolver", vars_: "_VarResolver") -> str:
    """Render the GUARDED formula as a THF ``$o`` term (classical connectives only)."""
    def f(n):
        return _thf_formula(n, syms, vars_)
    if isinstance(node, Atom):
        if truth_value(node) is not None:
            return "$true" if truth_value(node) else "$false"
        if _is_identity(node):
            # Native THF identity (see the module docstring's Equality section).
            left = _thf_term(node.args[0], syms, vars_)
            right = _thf_term(node.args[1], syms, vars_)
            return f"( {left} = {right} )"
        head = syms.name(_CAT_PRED, node.predicate, len(node.args))
        if not node.args:
            return head
        return "( " + " @ ".join([head] + [_thf_term(a, syms, vars_) for a in node.args]) + " )"
    if isinstance(node, Not):
        return f"( ~ {f(node.formula)} )"
    if isinstance(node, And):
        return f"( {f(node.left)} & {f(node.right)} )"
    if isinstance(node, Or):
        return f"( {f(node.left)} | {f(node.right)} )"
    if isinstance(node, Implies):
        return f"( {f(node.left)} => {f(node.right)} )"
    if isinstance(node, Iff):
        return f"( {f(node.left)} <=> {f(node.right)} )"
    if isinstance(node, Xor):
        return f"( {f(node.left)} <~> {f(node.right)} )"
    if isinstance(node, Quantifier):
        x = vars_.token(node.variable.name)
        binder = "!" if node.type in (_FORALL, "forall") else "?"
        return f"( {binder} [{x}: $i] : {f(node.formula)} )"
    raise NotImplementedError(
        f"to_thf_free: {type(node).__name__} should not occur in the guarded AST "
        "this printer renders."
    )


def _thf_signature_decls(formula: Node, syms: "_SymbolResolver") -> List[str]:
    """Type declarations for every predicate / function / constant, ``D``/``E!`` included."""
    preds, funcs, consts = _signature(formula)
    decls: List[str] = []
    for name, arity in sorted(preds):
        ident = syms.name(_CAT_PRED, name, arity)
        typ = " > ".join(["$i"] * arity + ["$o"]) if arity else "$o"
        decls.append(f"thf({ident}_decl, type, ( {ident} : ( {typ} ) )).")
    for name, arity in sorted(funcs):
        ident = syms.name(_CAT_FUNC, name, arity)
        typ = " > ".join(["$i"] * (arity + 1))
        decls.append(f"thf({ident}_decl, type, ( {ident} : ( {typ} ) )).")
    for name in sorted(consts):
        ident = syms.name(_CAT_CONST, name, 0)
        decls.append(f"thf({ident}_decl, type, ( {ident} : $i )).")
    return decls


def to_thf_free(formula: Node, *, policy: str = "negative", conjecture: bool = True) -> str:
    """Emit a complete TPTP **THF** problem for a free-logic ``formula``.

    Guards every atom with ``D`` and every quantifier with ``E!`` (see the
    module docstring), then declares a typed THF constant for every predicate /
    function / constant in the GUARDED signature (``D``/``E!`` always included),
    plus the ``E!(x) -> D(x)`` tie as an ``axiom`` (no nonempty-existence fact —
    an empty inner domain is a free-logic model), and the guarded translation
    itself as the ``conjecture`` (default) or an ``axiom``.

    Args:
        formula: the free-logic AST node (classical connectives / quantifiers /
            atoms — see the module docstring for the exact fragment).
        policy: ``"negative"`` (default) or ``"positive"`` — see
            :mod:`~unicode_logic_kit.semantics.free_logic`.
            ``"supervaluation"`` raises ``NotImplementedError``.
        conjecture: emit the goal as ``conjecture`` (default) or ``axiom``. A free
            variable is a parameter: one unknown individual that exists. For a
            conjecture that is the formula closed universally under the ``E!``
            guard, which is what is written. For an axiom it is not (``∀x P(x)``
            says more than ``P(x)``), so an asserted formula with a free variable
            is refused by name.

    Raises:
        NotImplementedError: for ``policy="supervaluation"``, for a node
            outside the free-logic fragment (modal / second-order /
            Łukasiewicz / substructural / lambda), or for ``conjecture=False``
            with a formula that has a free variable.
        ValueError: for any other unknown ``policy``.
    """
    _check_policy(policy, "to_thf_free")
    # A numeral is a constant identified by its value (1 and 1.0 are one), named ``n1``:
    # a user constant spelled like it is refused, not merged with it.
    [formula], _ = numerals_as_constants([formula], where="to_thf_free",
                                         spell=prefixed_numeral_name)
    _refuse_open_assertion(formula, conjecture, "to_thf_free")
    guarded = _guard(_close(formula), policy)
    role = "conjecture" if conjecture else "axiom"
    syms = _SymbolResolver(guarded)
    vars_ = _VarResolver(lambda raw: _sanitize(raw).upper())
    d_name = syms.name(_CAT_PRED, _DENOTES_PRED, 1)
    e_name = syms.name(_CAT_PRED, _EXISTS_PRED, 1)
    lines = [
        "% Free logic embedded into THF via denotation/existence guards.",
        f"% D(t): 't denotes'; {e_name}(t): 't exists' (E! implies D). policy={policy!r}.",
    ]
    lines += _thf_signature_decls(guarded, syms)
    lines.append(f"thf(free_tie, axiom, "
                 f"( ! [X: $i] : ( ( {e_name} @ X ) => ( {d_name} @ X ) ) )).")
    lines.append(f"thf(goal, {role}, {_thf_formula(guarded, syms, vars_)}).")
    return "\n".join(lines) + "\n"


# ===========================================================================
# (B) Isabelle/HOL export
# ===========================================================================

_ISA_BINOP = {And: "\\<and>", Or: "\\<or>", Implies: "\\<longrightarrow>",
              Iff: "\\<longleftrightarrow>"}


def _isa_term(node: Node, syms: "_SymbolResolver", vars_: "_VarResolver") -> str:
    """Render an individual term in Isabelle/HOL term syntax (curried application)."""
    if isinstance(node, Variable):
        return vars_.token(node.name)
    if isinstance(node, Constant):
        return syms.name(_CAT_CONST, node.name, 0)
    if isinstance(node, Number):
        return syms.name(_CAT_CONST, "n" + str(node.value), 0)
    if isinstance(node, Function):
        head = syms.name(_CAT_FUNC, node.name, len(node.args))
        return "(" + " ".join([head] + [_isa_term(a, syms, vars_) for a in node.args]) + ")"
    raise NotImplementedError(
        f"to_isabelle_free: unsupported term {type(node).__name__} (free-logic "
        "terms: variable / constant / number / function only)."
    )


def _isa_formula(node: Node, syms: "_SymbolResolver", vars_: "_VarResolver") -> str:
    """Render the GUARDED formula in Isabelle/HOL syntax (classical connectives only)."""
    def g(n):
        return _isa_formula(n, syms, vars_)
    if isinstance(node, Atom):
        if truth_value(node) is not None:
            return "True" if truth_value(node) else "False"
        if _is_identity(node):
            # Native Isabelle identity (see the module docstring's Equality section).
            left = _isa_term(node.args[0], syms, vars_)
            right = _isa_term(node.args[1], syms, vars_)
            return f"({left} = {right})"
        head = syms.name(_CAT_PRED, node.predicate, len(node.args))
        if not node.args:
            return head
        return "(" + " ".join([head] + [_isa_term(a, syms, vars_) for a in node.args]) + ")"
    if isinstance(node, Not):
        return f"(\\<not> {g(node.formula)})"
    if type(node) in _ISA_BINOP:
        op = _ISA_BINOP[type(node)]
        return f"({g(node.left)} {op} {g(node.right)})"
    if isinstance(node, Xor):
        inner = f"({g(node.left)} \\<longleftrightarrow> {g(node.right)})"
        return f"(\\<not> {inner})"
    if isinstance(node, Quantifier):
        binder = "\\<forall>" if node.type in (_FORALL, "forall") else "\\<exists>"
        return f"({binder} {vars_.token(node.variable.name)}. {g(node.formula)})"
    raise NotImplementedError(
        f"to_isabelle_free: {type(node).__name__} should not occur in the guarded "
        "AST this printer renders."
    )


def _isa_consts_block(formula: Node, syms: "_SymbolResolver") -> List[str]:
    """``consts`` declarations for every predicate / function / constant, ``D``/``E!`` included.

    Individuals live in a single uninterpreted HOL type ``e`` (the "outer
    domain" of the module docstring — existing or merely possible).
    """
    preds, funcs, consts = _signature(formula)
    lines: List[str] = []
    arrow = " \\<Rightarrow> "
    for name, arity in sorted(preds):
        ident = syms.name(_CAT_PRED, name, arity)
        typ = arrow.join(["e"] * arity + ["bool"]) if arity else "bool"
        lines.append(f'consts {ident} :: "{typ}"')
    for name, arity in sorted(funcs):
        ident = syms.name(_CAT_FUNC, name, arity)
        typ = arrow.join(["e"] * (arity + 1))
        lines.append(f'consts {ident} :: "{typ}"')
    for name in sorted(consts):
        ident = syms.name(_CAT_CONST, name, 0)
        lines.append(f'consts {ident} :: "e"')
    return lines


def to_isabelle_free(formula: Node, *, policy: str = "negative",
                     theory_name: str = "Free_Export", lemma_name: str = "goal",
                     proof: str = "oops") -> str:
    r"""Emit a loadable **Isabelle/HOL** theory with the guarded ``formula`` as a lemma.

    The theory declares a single uninterpreted individual type ``e`` (the outer
    domain — existing or merely possible) and a ``consts`` entry for every
    predicate / function / constant in the GUARDED signature (``D``/``E!``
    always included, see the module docstring), then states
    ``lemma <lemma_name>: "<E!->D tie> \<Longrightarrow> <guarded formula>"`` —
    the tie is a PREMISE of the goal, not ``axiomatization``, so nitpick can
    construct ``D``/``E!`` itself and certify a countermodel as genuine (mirrors
    :mod:`~unicode_logic_kit.hol.isabelle_conditional`'s ``nested Sel`` premise).

    Args:
        formula: the free-logic AST node.
        policy: ``"negative"`` (default) or ``"positive"``.
            ``"supervaluation"`` raises ``NotImplementedError``.
        theory_name: the Isabelle theory identifier.
        lemma_name: the lemma identifier.
        proof: the proof text under the lemma; defaults to ``"oops"`` (state,
            don't discharge — this function does not run Isabelle). Since the
            premises are stated with the bare ``P1 \<Longrightarrow> P2 \<Longrightarrow> Q``
            lemma syntax (no ``assumes``/``shows``), a proof method sees them as
            an ordinary implication goal — no ``using`` clause is required to
            reach them.

    Raises:
        NotImplementedError: for ``policy="supervaluation"``, for a node
            outside the free-logic fragment, or for a constant or function that is spelled
            like a numeral of the formula (``Number(1)`` next to ``Constant('n1')``): a
            numeral is a constant of its own, named ``n1`` here, and the two would be one
            symbol of the theory, so the writer refuses to merge them.
        ValueError: for any other unknown ``policy``, or for a numeral that is ``inf``,
            ``-inf`` or ``nan``.
    """
    _check_policy(policy, "to_isabelle_free")
    # A numeral is a constant identified by its value (1 and 1.0 are one), named ``n1``:
    # a user constant spelled like it is refused, not merged with it.
    [formula], _ = numerals_as_constants([formula], where="to_isabelle_free",
                                         spell=prefixed_numeral_name)
    guarded = _guard(_close(formula), policy)
    syms = _SymbolResolver(guarded)
    vars_ = _VarResolver(_sanitize, used=syms._used)
    d_name = syms.name(_CAT_PRED, _DENOTES_PRED, 1)
    e_name = syms.name(_CAT_PRED, _EXISTS_PRED, 1)
    tie = f"(\\<forall>x. {e_name} x \\<longrightarrow> {d_name} x)"
    lines = [
        f"theory {theory_name}",
        "  imports Main",
        "begin",
        "",
        "(* Free logic embedded into Isabelle/HOL over an uninterpreted individual",
        "   type e (existing or merely possible), guarded by D (denotes) and",
        f"   {e_name} (exists; implies D). policy={policy!r}.",
        "   The E!->D tie is a PREMISE of the goal, not `axiomatization`, so nitpick",
        "   constructs D/E! itself and can certify a countermodel as genuine (mirrors",
        "   hol.isabelle_conditional's `nested`). No nonempty-existence fact: an empty",
        "   inner domain is a free-logic model. '=' is HOL identity under the D guard. *)",
        "",
        "typedecl e  \\<comment> \\<open>outer domain: existing or merely possible\\<close>",
    ]
    lines += _isa_consts_block(guarded, syms)
    lines.append("")
    lines.append(f'lemma {lemma_name}: "{tie} \\<Longrightarrow> '
                 f'{_isa_formula(guarded, syms, vars_)}"')
    lines.append(f"  {proof}")
    lines.append("")
    lines.append("end")
    return "\n".join(lines) + "\n"


def free_theory(formula: Node, *, policy: str = "negative",
                theory_name: str = "FreeDecide", lemma_name: str = "goal",
                proof: Optional[str] = None) -> str:
    """Emit a self-contained theory asserting ``formula``'s free-logic validity.

    A thin wrapper around :func:`to_isabelle_free`, named and keyword-shaped
    like
    :func:`~unicode_logic_kit.hol.isabelle_conditional.isabelle_conditional_theory`
    for :mod:`~unicode_logic_kit.hol.isabelle_runner`'s prove/refute two-step
    protocol (:func:`~unicode_logic_kit.hol.isabelle_runner.isabelle_decide_free`):
    ``proof`` defaults to ``"oops"`` when omitted (state, don't discharge), and
    ``theory_name`` / ``lemma_name`` default to values distinct from
    :func:`to_isabelle_free`'s own so both can be called back to back in one
    script without a duplicate-theory-name collision.

    Raises:
        NotImplementedError: for ``policy="supervaluation"``, for a node
            outside the free-logic fragment, or for a numeral next to a constant or
            function spelled like it (see :func:`to_isabelle_free`).
        ValueError: for any other unknown ``policy``, or for a numeral that is
            ``inf``, ``-inf`` or ``nan``.
    """
    return to_isabelle_free(formula, policy=policy, theory_name=theory_name,
                            lemma_name=lemma_name,
                            proof=proof if proof is not None else "oops")
