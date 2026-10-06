"""MiniZinc/CP finite-domain refutation search — the second finite-domain backend.

:class:`MinizincBackend` decides ``premises ⊨ φ`` the same way
:class:`~unicode_fol_kit.atp.clingo_backend.ClingoBackend` does (built
alongside this module, not in it): both ground ``premises ∧ ¬φ`` over a
bounded domain ``0 … size-1`` and search for a satisfying assignment through
:mod:`~unicode_fol_kit.atp.finite_domain`'s shared problem/verification
layer. A model at some size REFUTES ``φ``; no model up to ``max_size``
is UNKNOWN/``"bound_hit"`` — see :mod:`atp.finite_domain`'s module docstring
for the one rule neither backend may soften: **this search never returns
PROVED**. Every reconstructed countermodel is re-checked by
:func:`~unicode_fol_kit.atp.finite_domain.verify_model` before it is allowed
to leave :meth:`MinizincBackend.decide` as REFUTED — and what
:mod:`atp.finite_domain`'s module docstring used to call a "Known
verification gap" for ``Cardinality``/``Function`` is CLOSED for both now,
the same way, in two steps. ``verify_model``'s own evaluator counts
``Cardinality`` comparisons arithmetically, so the counting fragment is
CLOSED end to end: a REFUTED verdict on e.g. ``|{x : P(x)}| > |{y : Q(y)}|``
carries a countermodel this backend has genuinely re-verified, not one that
downgrades to ERROR/``"infra"`` for want of a checker. ``Function`` is
CLOSED too, by the identical mechanism rather than by staying refused:
:func:`~unicode_fol_kit.atp.finite_domain.fragment_check` — consulted by
:func:`to_minizinc` before it emits a single declaration — now ADMITS a
``Function`` node generally (a *sorted* ``FunctionDecl`` stays refused, but
separately — see
:mod:`~unicode_fol_kit.atp.finite_domain`'s "Sorted function symbols"
section, not this gate), and ``verify_model``'s evaluator now reads
``f(t1,...,tk)`` off the SAME ``(name, arity+1)`` total-relation extension
:func:`~unicode_fol_kit.atp.finite_domain.structure_from_solution` already
reconstructs, so a function-bearing REFUTED verdict is genuinely
re-verified too. This module's OWN function-encoding machinery — the array
declarations in :func:`to_minizinc`, :func:`_term`'s ``Function`` branch,
:func:`_atoms_from_solution`'s function-decoding loop — is consequently
REACHABLE from :meth:`MinizincBackend.decide` now, not merely kept in place
as a second line of defence — see "Encoding — arrays and generators" below,
which used to document this as dormant and now documents it as live.

Many-sorted input
-------------------
:meth:`MinizincBackend.decide` builds ``sentences = tuple(premises) +
(Not(formula),)`` and then, before ``Signature.from_formulas`` or
:func:`to_minizinc`'s own :func:`~unicode_fol_kit.atp.finite_domain.fragment_check`
call ever see it, runs the whole batch through
:func:`~unicode_fol_kit.atp.finite_domain.lower_msfol` — a no-op for every
plain-FOL caller, and for a many-sorted one a relativisation to classical
FOL (plus one non-emptiness sentence per distinct sort name) that needs no
support from this module's own renderer or output parser at all: a sort
name is, after lowering, an ordinary unary predicate like any other. See
:mod:`~unicode_fol_kit.atp.finite_domain`'s own "Many-sorted input" section
for the full design, including why the non-emptiness sentence is required
for soundness against :mod:`~unicode_fol_kit.semantics.modelfinder`, the
oracle this is differentially tested against (offline here, since MiniZinc
itself is not installed in this environment — see below).

External binary, not a Python package
--------------------------------------
The originating design note for this backend (§6) mentions ``pip install
minizinc`` — the *Python* MiniZinc bindings. This module does NOT use that
package. Per the task this module was built under, discovery instead follows
the exact convention :class:`~unicode_fol_kit.atp.protocol.Prover9Backend`
and :class:`~unicode_fol_kit.atp.protocol.VampireBackend` already use for
their own external binaries: ``$UFK_MINIZINC``, then ``PATH``
(:func:`_minizinc_binary`). The generated ``.mzn`` text is written to a temp
file and handed to the ``minizinc`` CLI directly via ``subprocess`` — one
less runtime dependency, and one fewer translation layer between this
module's own encoding and what actually gets solved. MiniZinc is NOT
installed in this repository's development environment and will not be, so
:meth:`MinizincBackend.decide`'s live subprocess path is exercised only
through :func:`minizinc_available` returning ``False`` here; what IS fully
exercised and pinned by fixtures is everything this module can control
without a solver: :func:`to_minizinc` (the renderer) and the output parser
(:func:`_parse_minizinc_solution` / :func:`_atoms_from_solution`) — the same
split :mod:`atp.eprover_backend` / :mod:`atp.twee_backend` use for tools this
environment cannot run either.

Encoding — arrays and generators, not the ASP boolean-relation reading
--------------------------------------------------------------------------
This section documents the renderer's OWN convention for a function symbol —
LIVE now, on every ordinary search that mentions one, per the module
docstring's opening: :func:`fragment_check` admits ``Function`` generally,
so :meth:`MinizincBackend.decide` reaches this code on a genuine
function-bearing sentence today, not merely on the hand-built-problem
second-line-of-defence case the sorted/arithmetic refusals below still
describe.
:mod:`atp.finite_domain`'s module docstring describes the shared "function =
total relation + functionality constraint" reconstruction that
:func:`~unicode_fol_kit.atp.finite_domain.structure_from_solution` expects
BACK from a solver (a ``(k+1)``-tuple per function atom). That is the shape
this module's OUTPUT must produce, not necessarily the shape its INPUT
encoding has to take to produce it — and for MiniZinc the natural CP
encoding of a function symbol ``f`` of arity ``k`` is
``array[DOM, …, DOM] of var DOM: f_name;`` (``k`` copies of ``DOM``): a
MiniZinc array is by construction both TOTAL (every index combination in its
declared index set has some value — there is no way to leave a cell
unassigned and still have a solution) and FUNCTIONAL (each cell holds
exactly one value), so it reaches the identical total-relation semantics the
ASP encoding reaches via an explicit boolean array plus an explicit
"exactly one true per input tuple" constraint, but through a solver-native
type rather than a constraint that would be redundant in this language —
exactly the reason CP is in this design at all (§11: "alldifferent for the
distinctness convention rather than the pairwise-≠ expansion"; the same
argument applies to functions, not just constants). A predicate ``p`` of
arity ``k`` is the boolean counterpart, ``array[DOM, …, DOM] of var bool:
p_name;``; a constant is ``var DOM: k_name;`` (the 0-ary case of the same
"exactly one value" reading, likewise needing no explicit "exactly one"
constraint because ``var DOM`` already ranges over exactly one value).
:func:`_atoms_from_solution` is what actually produces the ``(k+1)``-tuple
shape :func:`~unicode_fol_kit.atp.finite_domain.structure_from_solution`
requires, by pairing every ``DOM^k`` index tuple with the array's value
there — so the two modules' conventions meet at the atom boundary, not
inside the ``.mzn`` text itself.

Arithmetic function symbols (``+``, ``-``, ``*``, ``/``) are refused
------------------------------------------------------------------------
``+``/``-``/``*``/``/`` count as ``Function`` nodes, and
:func:`~unicode_fol_kit.atp.finite_domain.fragment_check` now ADMITS
``Function`` generally (see the module docstring's opening) — but these four
NAMES stay refused regardless, LIVE, on the exact path the rest of this
module's ``Function`` support now takes: :func:`_term`'s ``Function`` branch
checks ``node.name in _BUILTIN_ARITH_FUNCS`` before it ever consults
``ctx.functions``, so an arithmetic-operator sentence is stopped inside
:func:`to_minizinc`'s own rendering loop, ``NotImplementedError``, before a
single array is declared — no longer merely a second line of defence for a
hand-built problem :func:`fragment_check` never saw, now the FIRST and only
line of defence for these four names specifically (an ordinary declared
function ``f(x)`` no longer shares this fate — see "Encoding — arrays and
generators" above). This section states, and argues below, WHICH reading of
``+`` this module gives it now that ``Function`` support is no longer merely
hypothetical.
:meth:`~unicode_fol_kit.fol.nodes.Function.to_z3` treats ``+`` as an
UNINTERPRETED function symbol named ``"+"`` (``env.get_func(self.name,
len(self.args))`` — the same call for every function name; genuine
arithmetic only exists in the separate, unrelated
:mod:`~unicode_fol_kit.atp.z3_arith` pipeline), and
:meth:`~unicode_fol_kit.fol.signature.Signature.from_formulas` deliberately
EXCLUDES these four names from the ``functions`` section it builds (the
``_BUILTIN_FUNCS`` split, mirroring ``eval.validate``'s identical carve-out)
— so a :class:`~unicode_fol_kit.atp.finite_domain.FiniteDomainProblem`'s
auto-derived signature never declares an array for them. Two readings were
available here: (a) silently declare one anyway, duplicating a symbol the
signature layer deliberately keeps out of user vocabulary, or (b) give ``+``
literal MiniZinc integer-arithmetic semantics (tempting, since domain
individuals ARE the integers ``0 … n-1`` already) — but that would be a
DIFFERENT reading of the identical AST node than every other export in this
kit gives it, decided unilaterally inside one backend. Per the kit's own
discipline against exactly this kind of silent semantic substitution (see
e.g. :mod:`atp.finite_domain`'s ``all_different`` footnote), this module
instead REFUSES: :func:`_term` raises ``NotImplementedError`` for these four
names — reached LIVE now through :meth:`MinizincBackend.decide` whenever a
searched sentence names one of them, since :func:`fragment_check` no longer
stops a ``Function`` node on the way in; the caller sees the identical
``UNKNOWN``/``"unsupported"`` outcome either way, just raised one call
frame deeper than before, from inside :func:`to_minizinc`'s rendering loop
rather than at the gate — an honest gap either way, not a guess. (A
:class:`~unicode_fol_kit.fol.nodes.Number` is refused too, for its own reason —
see the next section.)

A ``Number`` is the bound of a count, never an individual
-----------------------------------------------------------
A numeral (:class:`~unicode_fol_kit.fol.nodes.Number`) has two readings in the
kit. On every route that was not asked for arithmetic it is a CONSTANT
identified by its value (``Number(1)`` and ``Number(1.0)`` are one node, one
constant; ``1 ≠ 2`` is not valid, because two constants may denote one
element), as :meth:`~unicode_fol_kit.fol.nodes.Number.to_z3` writes it. The
documented counting fragment gives it the other one: the number a cardinality
is compared with (``|{v : φ}| ≥ 3`` — a raw count, unrelated to any domain
individual). This backend's domain individuals are the integers ``0 … n-1``,
so the bare literal ``k`` would be a DOMAIN ELEMENT, the element number ``k``
(or no element at all when ``k`` is not below the size), and the kit's
numerals need not be that: ``(∀x ∀y x = y) → 1 = 2`` is valid (one element,
so ``1`` and ``2`` denote the same thing), and the index reading refuted it.

So a ``Number`` is read as a number ONLY as an operand of a comparison with a
:class:`~unicode_fol_kit.fol.nodes.Cardinality` (:func:`_number_int`: the
bound of the count, a float with a whole value being that integer). Anywhere
else — as a term of a predicate, of a function, of ``=``, or in a comparison
of numerals that has no cardinality in it — it is refused by name with
``NotImplementedError``, which :meth:`MinizincBackend.decide` reports as
``UNKNOWN``/``"unsupported"``: this backend has no symbol for a numeral, and
it never reads one as a domain index or as arithmetic. The same holds for a
comparison that sets a cardinality against a plain individual (the count
against the element number of a constant has no coherent reading). The
:class:`~unicode_fol_kit.atp.clingo_backend.ClingoBackend` draws the same line.

Identifier scheme — role-prefixed, ASCII-transliterated, collision-checked
--------------------------------------------------------------------------
Every declared symbol is rendered under a role prefix — predicate ``p_``,
function ``f_``, constant ``k_``, bound variable ``v_`` — rather than its
bare kit-level name, for two independent reasons. First, MiniZinc reserves a
long list of lower-case keywords (``output``, ``function``, ``predicate``,
``array``, ``where``, ``let``, …), and while this kit's own grammar (see
``fol/grammars/terminals.lark``) happens to keep bound VARIABLE names to a
single letter plus digits (so they can never collide with a multi-letter
keyword), it places NO such restriction on a function/constant NAME token —
a formula naming a function ``output`` would otherwise silently break the
renderer's own ``output`` item. Prefixing removes the possibility outright
rather than relying on the grammar's current shape staying that way forever.
Second, it keeps predicates, functions and constants in three textually
disjoint MiniZinc namespaces, matching how the kit's own
:class:`~unicode_fol_kit.fol.signature.Signature` already keeps them apart
conceptually. A predicate/function/constant/variable name may additionally be
non-ASCII (Greek, e.g. ``θ``; or any other script the widened FOL grammar now
accepts, e.g. ``świątek`` — MiniZinc identifiers are ASCII-only), so
:func:`_mzn_pred_name`, :func:`_mzn_func_name`, :func:`_mzn_const_name`, and
:func:`_mzn_var_name` all reuse the kit's own
:func:`~unicode_fol_kit.fol._fol_nodes.constant_name_to_ascii` (the same
transliteration :meth:`~unicode_fol_kit.fol.nodes.Constant.to_prover9` /
``to_tptp`` already use) rather than inventing a second one. That
transliteration is NOT injective in general (a literal ``c_theta`` and the
Greek ``θ`` both fold to ``theta``), so :func:`to_minizinc` runs the exact
same collision guard :func:`~unicode_fol_kit.atp._tptp_problem
.generate_tptp_problem` already runs for its own (different) folding
function, separately for the predicate, function, and constant namespaces
(NOT for the variable namespace — see :func:`_mzn_var_name`'s own docstring
for why not), refusing with ``NotImplementedError`` naming both colliding
kit-level names rather than silently merging two distinct symbols into one
MiniZinc identifier.

Output — a hand-written wire format, not ``--output-mode json``
---------------------------------------------------------------------
MiniZinc 2.5+ can auto-serialise a solution to JSON
(``--output-mode json``), and that would ordinarily be the easy choice. It
is deliberately NOT used here: its exact behaviour when a model has no
explicit ``output`` item — which decision variables get included, and in
what shape a multi-dimensional array is emitted — is a MiniZinc-VERSION
detail this repository has no installed binary to confirm against (see the
top of this docstring). Instead :func:`to_minizinc` writes its OWN ``output``
item using only ``show()`` and string concatenation — base-language MiniZinc
features stable across every 2.x release — that flattens every array
(predicate or function, any arity) to a ONE-DIMENSIONAL list via an explicit
index-generator comprehension (``[ f_name[i0,i1] | i0 in DOM, i1 in DOM ]``,
varying the LAST generator fastest — the same nesting order
:func:`itertools.product` produces in Python, which is what
:func:`_atoms_from_solution` uses to reverse the flattening), and tags each
line ``UFK <mzn_name> <arity> <show(...)>`` between ``UFK-SOLUTION-BEGIN`` /
``UFK-SOLUTION-END`` sentinels. The whole format is invented, owned, and
parsed by this module alone — nothing about it depends on a MiniZinc version
or an installed solver, so it can be pinned by hand-written fixtures
(:func:`_parse_minizinc_solution`) and reasoned through line by line without
ever running ``minizinc``.
"""

import itertools
import os
import shutil
import subprocess
import tempfile
import time
from dataclasses import dataclass
from typing import Callable, Dict, Iterable, List, Optional, Sequence, Tuple, Union

from ..fol._fol_nodes import constant_name_to_ascii
from ..fol.nodes import (
    Node, Variable, Constant, Number, Function,
    Atom, Not, And, Or, Xor, Implies, Iff, Contrast, Quantifier,
    Count, Cardinality,
)
from ..fol.signature import Signature
from ..fol._free_parameters import parameterize
from .finite_domain import (
    FiniteDomainProblem, fragment_check, free_variable_reason, lower_msfol,
    structure_from_solution, verify_model,
)
from .protocol import (
    BackendUnavailable, ERROR, ProverBackend, REFUTED, UNKNOWN, Verdict,
    _native_command_exists,
)

__all__ = ["MinizincBackend", "minizinc_available", "to_minizinc"]


# =============================================================================
# Binary discovery
# =============================================================================

def _minizinc_binary() -> Optional[str]:
    """Discover the ``minizinc`` CLI: ``$UFK_MINIZINC``, then ``PATH``.

    Mirrors :meth:`~unicode_fol_kit.atp.protocol.Prover9Backend._binary` /
    :meth:`~unicode_fol_kit.atp.protocol.VampireBackend._binary` exactly:
    the env var is read fresh on every call (never cached, so repointing it
    mid-process takes effect immediately) and there is no WSL bridging —
    unlike :mod:`atp.eprover_backend`'s Linux-only tools, MiniZinc ships
    native Windows/macOS/Linux installers, so there is no "only reachable
    inside WSL" case to handle here.
    """
    return os.environ.get("UFK_MINIZINC") or shutil.which("minizinc")


def minizinc_available() -> bool:
    """Pure discovery: is a ``minizinc`` binary reachable right now?

    Checks ``$UFK_MINIZINC`` then ``PATH`` (see :func:`_minizinc_binary`);
    never imports or spawns anything, so it is safe to call speculatively.
    """
    return _minizinc_binary() is not None


# =============================================================================
# Identifier scheme
# =============================================================================

def _mzn_pred_name(name: str) -> str:
    """Predicate ``name`` -> its MiniZinc identifier: ASCII-transliterated, then prefixed.

    Reuses :func:`~unicode_fol_kit.fol._fol_nodes.constant_name_to_ascii`, exactly
    like :func:`_mzn_const_name` — a predicate NAME token is not restricted to ASCII
    any more than a constant one is (see ``fol/grammars/terminals.lark``: PREDICATE
    admits any Unicode letter with ``str.isupper()``), and MiniZinc identifiers are
    ASCII-only, so a raw ``p_świątek`` would be as illegal as an untransliterated
    constant. See the module docstring's "Identifier scheme" section for why this can
    collide across two distinct kit-level names and why :func:`to_minizinc` checks for
    that separately (this function does not check on its own; it has no visibility
    into sibling predicates).
    """
    return f"p_{constant_name_to_ascii(name)}"


def _mzn_func_name(name: str) -> str:
    """Function ``name`` -> its MiniZinc identifier: ASCII-transliterated, then prefixed.

    Same reasoning and the same collision caveat as :func:`_mzn_pred_name` — see
    the module docstring's "Identifier scheme" section.
    """
    return f"f_{constant_name_to_ascii(name)}"


def _mzn_const_name(name: str) -> str:
    """Constant ``name`` -> its MiniZinc identifier: ASCII-transliterated, then prefixed.

    Reuses :func:`~unicode_fol_kit.fol._fol_nodes.constant_name_to_ascii` —
    see the module docstring's "Identifier scheme" section for why this can
    collide across two distinct kit-level names and why :func:`to_minizinc`
    checks for that separately (this function does not check on its own; it
    has no visibility into sibling constants).
    """
    return f"k_{constant_name_to_ascii(name)}"


def _mzn_var_name(name: str) -> str:
    """Bound variable ``name`` -> its MiniZinc identifier (see module docstring).

    ASCII-transliterated like the predicate/function/constant names above: the
    VARIABLE terminal (``fol/grammars/terminals.lark``) admits any Unicode letter,
    so a raw non-ASCII variable name (e.g. ``ą``) would otherwise reach the
    generated ``.mzn`` text verbatim as ``v_ą`` — not a legal MiniZinc identifier.
    Unlike predicates/functions/constants this is not run through a collision
    guard in :func:`to_minizinc`: a bound variable's MiniZinc name is used only
    locally, inside the one ``forall``/``exists``/comprehension generator that
    binds it (see ``_formula``/``_term``), never declared or looked up by a second
    call site the way a predicate/function/constant's identifier is, and the
    kit's VARIABLE terminal keeps a raw name to a single letter plus ASCII digits
    — too small a space for the escape-based transliteration below to plausibly
    collide two DISTINCT names inside one formula's nested binders.
    """
    return f"v_{constant_name_to_ascii(name)}"


# The four arithmetic operators are legal Function names, and fragment_check
# now admits Function generally (see the module docstring's opening) — but
# these four names are excluded from Signature.from_formulas's `functions`
# section (the `_BUILTIN_FUNCS` split) regardless, so _term checks this set
# BEFORE consulting ctx.functions and refuses them LIVE, reachable through
# decide() on an ordinary search now (see the module docstring's "Arithmetic
# function symbols" section) — this module still refuses to guess a reading
# for them on its own rather than pick one silently.
_BUILTIN_ARITH_FUNCS = frozenset({"+", "-", "*", "/"})

# The six built-in comparison predicates: never declared in a Signature
# (mirroring `_BUILTIN_PREDS` in fol.signature / eval.validate), always
# rendered as a direct MiniZinc infix comparison instead of an array lookup.
_COMPARISON_OPS: Dict[str, str] = {
    "=": "=", "≠": "!=", "<": "<", ">": ">", "≤": "<=", "≥": ">=",
}

_COUNT_OP_TO_MZN = {"ge": ">=", "le": "<=", "eq": "="}


def _number_int(node: Number) -> int:
    """Return the value of ``node``, the bound a cardinality is compared with, as a plain ``int``.

    Only :func:`_formula`'s comparison branch calls this, for the ``Number`` operand of a
    comparison with a :class:`~unicode_fol_kit.fol.nodes.Cardinality` (see the module
    docstring's "A ``Number`` is the bound of a count, never an individual" section). A
    :class:`~unicode_fol_kit.fol.nodes.Number` stores a float with a whole value as the
    integer it equals, so ``2.0`` is the bound ``2``; a count cannot equal ``2.5``, so a
    fractional ``Number`` — legal per the dataclass's own ``Union[int, float]`` type,
    unlike :class:`~unicode_fol_kit.fol.nodes.Count`'s own ``n`` field — has no reading
    and is refused rather than silently truncated.

    Raises:
        NotImplementedError: ``node.value`` is not a plain (non-bool) ``int``.
    """
    if isinstance(node.value, bool) or not isinstance(node.value, int):
        raise NotImplementedError(
            f"to_minizinc: Number({node.value!r}) is not an integer — a count |{{v : φ}}| "
            "is never equal to a fraction, so a comparison bound that is not an integer "
            "has no reading in a finite domain of individuals 0..n-1."
        )
    return node.value


# =============================================================================
# Rendering context
# =============================================================================

@dataclass(frozen=True)
class _Ctx:
    """The name maps a single :func:`to_minizinc` call threads through rendering.

    Built once per call from ``problem.signature`` (see :func:`to_minizinc`)
    so :func:`_formula` / :func:`_term` never recompute a prefix or re-run
    the constant collision check per node — every kit-level symbol name that
    can legally appear in ``problem.sentences`` (per
    :func:`~unicode_fol_kit.atp.finite_domain.fragment_check`, already
    consulted by :func:`to_minizinc` before this is built) has exactly one
    entry here.
    """

    predicates: Dict[str, str]
    functions: Dict[str, str]
    constants: Dict[str, str]


def _term(node: Node, ctx: _Ctx) -> str:
    """Render ``node`` as a MiniZinc ``int``-typed expression (a TERM position).

    Dispatches on node type; every branch either returns a self-contained
    expression string or raises ``NotImplementedError`` naming exactly why
    (an arithmetic function symbol, a ``Number`` used as an individual, an
    undeclared symbol, or a node type with no term-position reading at all — the last
    should be unreachable for a ``sentences`` tuple that already passed
    :func:`~unicode_fol_kit.atp.finite_domain.fragment_check`, but is
    checked explicitly rather than assumed).
    """
    if isinstance(node, Variable):
        return _mzn_var_name(node.name)
    if isinstance(node, Constant):
        mzn = ctx.constants.get(node.name)
        if mzn is None:
            raise NotImplementedError(
                f"to_minizinc: constant {node.name!r} is not declared in the "
                "problem's signature."
            )
        return mzn
    if isinstance(node, Number):
        raise NotImplementedError(
            f"to_minizinc: the numeral {node.value!r} is used as an individual. A numeral "
            "is a constant identified by its value (1 and 1.0 are one constant), and this "
            "backend has no symbol for it: it reads a number only as the bound a count "
            "|{v : φ}| is compared with, never as a domain element, because the index "
            "reading would make 1 and 2 two different elements that the kit's numerals need "
            "not be. Use a solver that reads numerals as constants (z3, the finite model "
            "finder), or name the individual with a constant."
        )
    if isinstance(node, Function):
        if node.name in _BUILTIN_ARITH_FUNCS:
            raise NotImplementedError(
                f"to_minizinc: the arithmetic function symbol {node.name!r} "
                "carries no declared arity/extension here — "
                "Signature.from_formulas excludes it as a built-in, and this "
                "backend refuses to guess between an uninterpreted-function "
                "reading and a literal-arithmetic one rather than picking "
                "either silently; see the module docstring."
            )
        mzn = ctx.functions.get(node.name)
        if mzn is None:
            raise NotImplementedError(
                f"to_minizinc: function {node.name!r} is not declared in the "
                "problem's signature."
            )
        if not node.args:
            return mzn
        args = ", ".join(_term(a, ctx) for a in node.args)
        return f"{mzn}[{args}]"
    if isinstance(node, Cardinality):
        var = _mzn_var_name(node.variable.name)
        body = _formula(node.formula, ctx)
        return f"sum({var} in DOM)(bool2int({body}))"
    raise NotImplementedError(
        f"to_minizinc: {type(node).__name__} has no term-position rendering."
    )


def _comparison_operands(atom: Atom, ctx: _Ctx) -> Tuple[str, str]:
    """Render the two operands of the comparison ``atom`` (``= ≠ < > ≤ ≥`` at arity 2).

    A comparison with a :class:`~unicode_fol_kit.fol.nodes.Cardinality` operand is a
    counting comparison: both operands are then counting terms, a ``Cardinality`` (its
    ``sum`` over the domain) or a ``Number`` (the bound, :func:`_number_int`). Any other
    comparison compares individuals, and a ``Number`` among them is refused by
    :func:`_term`.

    Raises:
        NotImplementedError: a numeral is compared with no cardinality in the comparison
            (a statement about constants, not about counts: ``1 = 2`` is not valid, and
            ``(∀x ∀y x = y) → 1 = 2`` is); a cardinality is compared with a plain
            individual (no coherent reading); or an operand is refused by :func:`_term` /
            :func:`_number_int`.
    """
    has_cardinality = any(isinstance(a, Cardinality) for a in atom.args)
    has_numeral = any(isinstance(a, Number) for a in atom.args)
    if not has_cardinality and not has_numeral:
        return _term(atom.args[0], ctx), _term(atom.args[1], ctx)
    if not has_cardinality:
        raise NotImplementedError(
            f"to_minizinc: {atom.predicate!r} compares a numeral without a cardinality. A numeral "
            "is a constant identified by its value, and nothing else is known about it, so such "
            "a comparison is a statement about constants ('1 ≠ 2' is not valid, "
            "'(∀x ∀y x = y) → 1 = 2' is), which this backend does not state: it reads a number "
            "only as the bound a count |{v : φ}| is compared with, and a refutation found under "
            "the index reading would be wrong for the constants. Use a solver that reads numerals "
            "as constants (z3, the finite model finder), or compare a cardinality."
        )
    if not all(isinstance(a, (Cardinality, Number)) for a in atom.args):
        raise NotImplementedError(
            f"to_minizinc: {atom.predicate!r} compares a cardinality against a plain "
            "individual-denoting term — both sides of a counting comparison must themselves be "
            "counting terms (a Cardinality or a Number)."
        )
    left, right = (str(_number_int(a)) if isinstance(a, Number) else _term(a, ctx) for a in atom.args)
    return left, right


def _formula(node: Node, ctx: _Ctx) -> str:
    """Render ``node`` as a MiniZinc ``bool``-typed expression (a FORMULA position).

    Mirrors :func:`_term`'s dispatch/refusal discipline; see that function's
    docstring for the shared conventions (undeclared symbols, unreachable
    node types).
    """
    if isinstance(node, Atom):
        if node.predicate in _COMPARISON_OPS:
            if len(node.args) != 2:
                raise NotImplementedError(
                    f"to_minizinc: comparison predicate {node.predicate!r} "
                    f"used with arity {len(node.args)}, expected 2."
                )
            left, right = _comparison_operands(node, ctx)
            return f"({left} {_COMPARISON_OPS[node.predicate]} {right})"
        mzn = ctx.predicates.get(node.predicate)
        if mzn is None:
            raise NotImplementedError(
                f"to_minizinc: predicate {node.predicate!r} is not declared "
                "in the problem's signature."
            )
        if not node.args:
            return mzn
        args = ", ".join(_term(a, ctx) for a in node.args)
        return f"{mzn}[{args}]"
    if isinstance(node, Not):
        return f"(not {_formula(node.formula, ctx)})"
    if isinstance(node, And):
        return f"({_formula(node.left, ctx)} /\\ {_formula(node.right, ctx)})"
    if isinstance(node, Or):
        return f"({_formula(node.left, ctx)} \\/ {_formula(node.right, ctx)})"
    if isinstance(node, Xor):
        return f"({_formula(node.left, ctx)} xor {_formula(node.right, ctx)})"
    if isinstance(node, Implies):
        return f"({_formula(node.left, ctx)} -> {_formula(node.right, ctx)})"
    if isinstance(node, Iff):
        return f"({_formula(node.left, ctx)} <-> {_formula(node.right, ctx)})"
    if isinstance(node, Contrast):
        # Truth-functionally And — see Contrast's own docstring in _fol_nodes.py.
        return f"({_formula(node.left, ctx)} /\\ {_formula(node.right, ctx)})"
    if isinstance(node, Quantifier):
        var = _mzn_var_name(node.variable.name)
        body = _formula(node.formula, ctx)
        if node.type in ("forall", "∀"):
            return f"forall({var} in DOM)({body})"
        if node.type in ("exists", "∃"):
            return f"exists({var} in DOM)({body})"
        raise NotImplementedError(f"to_minizinc: unknown quantifier type {node.type!r}.")
    if isinstance(node, Count):
        var = _mzn_var_name(node.variable.name)
        body = _formula(node.formula, ctx)
        count_expr = f"sum({var} in DOM)(bool2int({body}))"
        return f"({count_expr} {_COUNT_OP_TO_MZN[node.op]} {node.n.value})"
    raise NotImplementedError(
        f"to_minizinc: {type(node).__name__} has no formula-position "
        "rendering (fragment_check should have refused this before "
        "to_minizinc was reached)."
    )


# =============================================================================
# to_minizinc — the renderer
# =============================================================================

def _flatten_expr(mzn_name: str, arity: int) -> str:
    """Return a MiniZinc expression flattening ``mzn_name`` to one dimension.

    Arity 0 is the bare variable itself; arity >= 1 is an explicit
    index-generator comprehension ``[ mzn_name[i0, i1, …] | i0 in DOM, i1 in
    DOM, … ]`` that varies the LAST generator fastest — the same order
    :func:`itertools.product` iterates in Python, which is what
    :func:`_atoms_from_solution` relies on to invert this flattening. See the
    module docstring's "Output" section for why the ``output`` item is
    written this way instead of via ``--output-mode json``.
    """
    if arity == 0:
        return f"show({mzn_name})"
    idx_vars = [f"i{k}" for k in range(arity)]
    generators = ", ".join(f"{v} in DOM" for v in idx_vars)
    index = ", ".join(idx_vars)
    return f"show([{mzn_name}[{index}] | {generators}])"


def _mzn_names_or_raise(
    names: Iterable[str], namer: Callable[[str], str], kind: str,
) -> Dict[str, str]:
    """Map each raw ``name`` in ``names`` to ``namer(name)``, refusing a same-namespace
    collision (two distinct kit-level ``kind`` symbols transliterating to the same
    MiniZinc identifier).

    Shared by :func:`to_minizinc`'s predicate, function, and constant declaration
    loops — the SAME guard :func:`_mzn_const_name`'s docstring already described, now
    applied identically to all three namespaces since ``constant_name_to_ascii`` is
    reused (via :func:`_mzn_pred_name` / :func:`_mzn_func_name`) for predicate and
    function names too. Deliberately not applied to the variable namespace — see
    :func:`_mzn_var_name`'s own docstring for why a bound variable's MiniZinc name
    does not need this guard.
    """
    out: Dict[str, str] = {}
    seen: Dict[str, str] = {}
    for name in sorted(names):
        mzn = namer(name)
        prior = seen.get(mzn)
        if prior is not None and prior != name:
            # NotImplementedError, not ValueError: this mirrors
            # atp._tptp_problem.generate_tptp_problem's IDENTICAL collision
            # guard for the (differently-folded) TPTP export, which raises
            # the same type for the same reason -- an export whose folding
            # is not injective for this particular pair of names is an
            # EXPORT LIMITATION, not a malformed FiniteDomainProblem, and
            # using the same exception type lets MinizincBackend.decide's
            # existing "fragment this backend cannot encode" catch site
            # handle it without a second, redundant except clause.
            raise NotImplementedError(
                f"to_minizinc: distinct {kind}s {prior!r} and {name!r} "
                f"would both render as the MiniZinc identifier {mzn!r} "
                "(constant_name_to_ascii is not injective) — refusing to "
                "silently merge two distinct symbols; rename one of them "
                "before exporting this problem. Mirrors "
                "atp._tptp_problem.generate_tptp_problem's identical "
                "collision guard for the TPTP export."
            )
        seen[mzn] = name
        out[name] = mzn
    return out


def to_minizinc(problem: FiniteDomainProblem) -> str:
    """Render ``problem`` as a complete MiniZinc model — the text of an ``mzn`` file.

    The model declares ``DOM = 0..size-1``, one array (predicate/function) or
    scalar (constant) per declared symbol in ``problem.signature``, an
    ``alldifferent`` constraint over the constants iff ``problem.all_different``
    and at least one constant is declared, one ``constraint`` per sentence in
    ``problem.sentences``, ``solve satisfy;``, and a custom ``output`` item
    (see the module docstring's "Output" section) that
    :func:`_parse_minizinc_solution` / :func:`_atoms_from_solution` read back
    on the other side of a solver run. Deterministic: symbols are declared
    in sorted-name order within each section, so two calls on
    structurally-equal problems byte-for-byte agree — the property a
    checked-in fixture comparison in a test suite relies on.

    Args:
        problem: the search problem; ``problem.sentences`` must already pass
            :func:`~unicode_fol_kit.atp.finite_domain.fragment_check` (this
            function calls it itself, first, so a caller does not have to
            remember to).

    Returns:
        The model text, newline-terminated.

    Raises:
        TypeError: ``problem`` is not a
            :class:`~unicode_fol_kit.atp.finite_domain.FiniteDomainProblem`.
        NotImplementedError: ``problem.sentences`` fails
            :func:`~unicode_fol_kit.atp.finite_domain.fragment_check`; a
            sentence has a free variable
            (:func:`~unicode_fol_kit.atp.finite_domain.free_variable_reason`;
            :meth:`MinizincBackend.decide` replaces it by a parameter before
            it writes); a
            sentence uses a node this renderer itself cannot place (an
            arithmetic function symbol, a
            :class:`~unicode_fol_kit.fol.nodes.Number` that is not the bound of a
            comparison with a cardinality or is not an integer, or a symbol absent
            from ``problem.signature`` — see :func:`_term` / :func:`_formula`);
            or two distinct declared constants would transliterate to the
            same MiniZinc identifier (see the module docstring's "Identifier
            scheme" section — raised as ``NotImplementedError``, not
            ``ValueError``, to match
            :func:`~unicode_fol_kit.atp._tptp_problem.generate_tptp_problem`'s
            identical collision guard and so it is caught by the same
            "cannot encode this fragment" site in
            :meth:`MinizincBackend.decide`).
    """
    if not isinstance(problem, FiniteDomainProblem):
        raise TypeError(
            f"to_minizinc: expected a FiniteDomainProblem, got "
            f"{type(problem).__name__}."
        )
    reason = fragment_check(problem.sentences)
    if reason is None:
        # A free variable would be written as an identifier the model never declares.
        reason = free_variable_reason(problem.sentences)
    if reason is not None:
        raise NotImplementedError(f"to_minizinc: {reason}")

    sig = problem.signature

    pred_names = _mzn_names_or_raise(sig.predicates, _mzn_pred_name, "predicate")
    func_names = _mzn_names_or_raise(sig.functions, _mzn_func_name, "function")
    const_names = _mzn_names_or_raise(sig.constants, _mzn_const_name, "constant")

    needs_alldifferent = bool(problem.all_different and const_names)

    lines: List[str] = []
    if needs_alldifferent:
        lines.append('include "alldifferent.mzn";')
        lines.append("")
    lines.append(
        "% Generated by unicode_fol_kit.atp.minizinc_backend.to_minizinc --"
    )
    lines.append(
        f"% bounded refutation search, |D| = {problem.size}, "
        f"{len(problem.sentences)} sentence(s) to satisfy simultaneously."
    )
    lines.append(
        "% REFUTATION-ONLY: SATISFIABLE here witnesses a finite countermodel;"
    )
    lines.append(
        "% UNSATISFIABLE proves nothing about validity at a larger domain size."
    )
    lines.append("")
    lines.append(f"int: n = {problem.size};")
    lines.append("set of int: DOM = 0..n-1;")
    lines.append("")

    for name in sorted(sig.predicates):
        decl = sig.predicates[name]
        mzn = pred_names[name]
        if decl.arity == 0:
            lines.append(f"var bool: {mzn};")
        else:
            dims = ", ".join(["DOM"] * decl.arity)
            lines.append(f"array[{dims}] of var bool: {mzn};")
    if sig.predicates:
        lines.append("")

    for name in sorted(sig.functions):
        decl = sig.functions[name]
        mzn = func_names[name]
        if decl.arity == 0:
            lines.append(f"var DOM: {mzn};")
        else:
            dims = ", ".join(["DOM"] * decl.arity)
            lines.append(f"array[{dims}] of var DOM: {mzn};")
    if sig.functions:
        lines.append("")

    for name in sorted(const_names):
        lines.append(f"var DOM: {const_names[name]};")
    if const_names:
        lines.append("")

    if needs_alldifferent:
        names = [const_names[n] for n in sorted(const_names)]
        lines.append(f"constraint alldifferent([{', '.join(names)}]);")
        lines.append("")

    ctx = _Ctx(predicates=pred_names, functions=func_names, constants=const_names)
    for i, sentence in enumerate(problem.sentences, start=1):
        lines.append(f"constraint {_formula(sentence, ctx)}; % sentence {i}")
    lines.append("")
    lines.append("solve satisfy;")
    lines.append("")

    output_parts: List[str] = ['"UFK-SOLUTION-BEGIN\\n"']
    for name in sorted(sig.predicates):
        decl = sig.predicates[name]
        mzn = pred_names[name]
        expr = _flatten_expr(mzn, decl.arity)
        output_parts.append(f'"UFK {mzn} {decl.arity} " ++ {expr} ++ "\\n"')
    for name in sorted(sig.functions):
        decl = sig.functions[name]
        mzn = func_names[name]
        expr = _flatten_expr(mzn, decl.arity)
        output_parts.append(f'"UFK {mzn} {decl.arity} " ++ {expr} ++ "\\n"')
    for name in sorted(const_names):
        mzn = const_names[name]
        output_parts.append(f'"UFK {mzn} 0 " ++ show({mzn}) ++ "\\n"')
    output_parts.append('"UFK-SOLUTION-END\\n"')

    lines.append("output [")
    lines.append("  " + ",\n  ".join(output_parts))
    lines.append("];")
    lines.append("")

    return "\n".join(lines) + "\n"


# =============================================================================
# Output parsing — the other half of the fixture-testable pair
# =============================================================================

_MznValue = Union[bool, int, list]


def _parse_mzn_value(text: str) -> _MznValue:
    """Parse one ``show()``-rendered MiniZinc scalar or flat list.

    Handles exactly the three shapes :func:`to_minizinc`'s ``output`` item
    can ever produce: ``"true"``/``"false"`` (a bool scalar — a nullary
    predicate, or one entry of a flattened predicate array), a bare integer
    (an int scalar — a constant, a nullary function, or one entry of a
    flattened function array), or a bracketed comma-separated list of either
    (``"[true, false, true]"`` / ``"[0, 1, 1]"``) — the flattened form
    :func:`_flatten_expr` emits for arity >= 1. Never recurses into nested
    brackets: :func:`to_minizinc` never emits one (every array is flattened
    to exactly one dimension before ``show()`` sees it), so a nested bracket
    here would mean the text did not come from this module's own renderer.

    Raises:
        ValueError: ``text`` is not one of the three recognised shapes.
    """
    if text == "true":
        return True
    if text == "false":
        return False
    if text.startswith("[") and text.endswith("]"):
        inner = text[1:-1].strip()
        if not inner:
            return []
        return [_parse_mzn_value(part.strip()) for part in inner.split(",")]
    try:
        return int(text)
    except ValueError:
        raise ValueError(f"_parse_mzn_value: unrecognised MiniZinc literal {text!r}.")


_UFK_BEGIN = "UFK-SOLUTION-BEGIN"
_UFK_END = "UFK-SOLUTION-END"
_UFK_PREFIX = "UFK "


def _parse_minizinc_solution(stdout: str) -> Optional[Dict[str, _MznValue]]:
    """Extract this module's own UFK-tagged solution block from ``stdout``.

    Returns ``None`` when no ``UFK-SOLUTION-BEGIN`` / ``UFK-SOLUTION-END``
    pair is present at all — the caller's signal that ``minizinc`` did not
    reach the ``output`` item (an ``=====UNSATISFIABLE=====`` /
    ``=====UNKNOWN=====`` run, or an infra failure the caller checks for
    separately). Otherwise returns ``{mzn_name: parsed_value}`` for every
    ``UFK <mzn_name> <arity> <value>`` line between the sentinels (the
    ``<arity>`` field is not otherwise used here — :func:`_atoms_from_solution`
    already knows each symbol's arity from ``signature`` itself — but is kept
    in the wire format as a cheap, human-readable sanity anchor when reading
    a captured transcript by eye).

    Args:
        stdout: the ``minizinc`` subprocess's captured standard output.

    Returns:
        The parsed solution dict, or ``None`` if no solution block is present.
    """
    if _UFK_BEGIN not in stdout or _UFK_END not in stdout:
        return None
    block = stdout[stdout.index(_UFK_BEGIN):stdout.index(_UFK_END)]
    solution: Dict[str, _MznValue] = {}
    for line in block.splitlines():
        line = line.strip()
        if not line.startswith(_UFK_PREFIX):
            continue
        rest = line[len(_UFK_PREFIX):]
        mzn_name, _, tail = rest.partition(" ")
        _arity_str, _, value_str = tail.partition(" ")
        solution[mzn_name] = _parse_mzn_value(value_str.strip())
    return solution


def _atoms_from_solution(
    signature: Signature, solution: Dict[str, _MznValue], size: int,
) -> List[Tuple[str, Tuple[int, ...]]]:
    """Translate a parsed ``UFK`` solution dict into the shared atom shape.

    The counterpart of :func:`to_minizinc`'s declaration section: for every
    predicate/function/constant ``signature`` declares, looks up its MiniZinc
    identifier (via the same :func:`_mzn_pred_name` / :func:`_mzn_func_name`
    / :func:`_mzn_const_name` helpers :func:`to_minizinc` used, so the two
    directions cannot silently drift apart), and expands a flattened array
    value back into ``(index_tuple, value)`` pairs via
    ``itertools.product(range(size), repeat=arity)`` — the identical
    generator order :func:`_flatten_expr`'s comprehension emits in the
    ``.mzn`` text (last generator fastest), so the ``k``-th list entry lines
    up with the ``k``-th index tuple.

    Produces exactly the ``(symbol_name, args)`` pairs
    :func:`~unicode_fol_kit.atp.finite_domain.structure_from_solution`
    expects, INCLUDING the ``(k+1)``-tuple total-relation shape for a
    function of arity ``k`` — this function does the pairing;
    ``structure_from_solution`` does the functionality/totality validation
    (deliberately not duplicated here — see that function's own docstring).

    Args:
        signature: the problem's declared vocabulary.
        solution: the dict :func:`_parse_minizinc_solution` produced.
        size: the domain size the solution was searched at.

    Returns:
        The atom list, in predicate/function/constant, then sorted-name,
        order (order is not semantically significant to the caller, but
        deterministic order keeps this function's own tests reproducible).

    Raises:
        ValueError: a declared symbol's MiniZinc identifier is missing from
            ``solution``, or its value has the wrong shape (not a bool/list
            of bools for a predicate, not an int/list of ints for a
            function/constant, or a list of the wrong length for ``size``
            and the symbol's arity).
    """
    atoms: List[Tuple[str, Tuple[int, ...]]] = []

    def _expect(mzn_name: str) -> _MznValue:
        if mzn_name not in solution:
            raise ValueError(
                f"_atoms_from_solution: the minizinc solution is missing "
                f"{mzn_name!r} (declared by the problem's signature)."
            )
        return solution[mzn_name]

    for name in sorted(signature.predicates):
        decl = signature.predicates[name]
        mzn = _mzn_pred_name(name)
        value = _expect(mzn)
        if decl.arity == 0:
            if not isinstance(value, bool):
                raise ValueError(
                    f"_atoms_from_solution: predicate {name!r} (arity 0) "
                    f"expects a bool, got {value!r}."
                )
            if value:
                atoms.append((name, ()))
            continue
        if not isinstance(value, list):
            raise ValueError(
                f"_atoms_from_solution: predicate {name!r} (arity "
                f"{decl.arity}) expects a flat list, got {value!r}."
            )
        index_tuples = list(itertools.product(range(size), repeat=decl.arity))
        if len(value) != len(index_tuples):
            raise ValueError(
                f"_atoms_from_solution: predicate {name!r} expects "
                f"{len(index_tuples)} entries (size={size}, arity="
                f"{decl.arity}), got {len(value)}."
            )
        for idx_tuple, truth in zip(index_tuples, value):
            if not isinstance(truth, bool):
                raise ValueError(
                    f"_atoms_from_solution: predicate {name!r} entry "
                    f"{idx_tuple} expects a bool, got {truth!r}."
                )
            if truth:
                atoms.append((name, idx_tuple))

    for name in sorted(signature.functions):
        decl = signature.functions[name]
        mzn = _mzn_func_name(name)
        value = _expect(mzn)
        if decl.arity == 0:
            if not isinstance(value, int) or isinstance(value, bool):
                raise ValueError(
                    f"_atoms_from_solution: function {name!r} (arity 0) "
                    f"expects an int, got {value!r}."
                )
            atoms.append((name, (value,)))
            continue
        if not isinstance(value, list):
            raise ValueError(
                f"_atoms_from_solution: function {name!r} (arity "
                f"{decl.arity}) expects a flat list, got {value!r}."
            )
        index_tuples = list(itertools.product(range(size), repeat=decl.arity))
        if len(value) != len(index_tuples):
            raise ValueError(
                f"_atoms_from_solution: function {name!r} expects "
                f"{len(index_tuples)} entries (size={size}, arity="
                f"{decl.arity}), got {len(value)}."
            )
        for idx_tuple, result in zip(index_tuples, value):
            if not isinstance(result, int) or isinstance(result, bool):
                raise ValueError(
                    f"_atoms_from_solution: function {name!r} entry "
                    f"{idx_tuple} expects an int result, got {result!r}."
                )
            atoms.append((name, idx_tuple + (result,)))

    for name in sorted(signature.constants):
        mzn = _mzn_const_name(name)
        value = _expect(mzn)
        if not isinstance(value, int) or isinstance(value, bool):
            raise ValueError(
                f"_atoms_from_solution: constant {name!r} expects an int, "
                f"got {value!r}."
            )
        atoms.append((name, (value,)))

    return atoms


# =============================================================================
# Subprocess plumbing
# =============================================================================

def _environment_for(binary: str) -> Optional[Dict[str, str]]:
    """The environment to run ``binary`` in: the caller's, with the binary's own
    folder (and its ``bin`` subfolder) put first on ``PATH``.

    MiniZinc starts its solver as a second program (``bin/fzn-gecode``), and on
    Windows that program loads libraries that lie next to ``minizinc.exe``. An
    installer puts that folder on ``PATH``; a binary reached only through
    ``$UFK_MINIZINC`` has no such entry, and the bundled default solver then
    ends at once with ``=====ERROR=====`` and an empty error stream (measured
    with MiniZinc 2.8.4: Gecode fails that way, Chuffed does not). ``None``
    (inherit the environment unchanged) when ``binary`` is a bare command
    name, which the shell resolved through ``PATH`` already.
    """
    folder = os.path.dirname(binary)
    if not folder:
        return None
    env = dict(os.environ)
    own = [folder, os.path.join(folder, "bin")]
    env["PATH"] = os.pathsep.join(own + [env.get("PATH", "")])
    return env


def _run_minizinc(
    model_path: str, binary: str, solver: str, time_limit_ms: int,
) -> Tuple[str, str, bool]:
    """Run ``minizinc`` on ``model_path``; return ``(stdout, stderr, timed_out)``.

    ``--time-limit`` (milliseconds) is MiniZinc's OWN search budget, so a
    solver that hits it exits cleanly with ``=====UNKNOWN=====`` in its
    stdout rather than being killed — the Python-side ``subprocess.run``
    timeout is set ten seconds beyond that as a hard backstop against a
    solver that ignores its own budget (mirrors
    :mod:`atp.eprover_backend`'s ``_run_tptp_prover`` doing the identical
    thing for E's ``--cpu-limit``), not the primary timeout mechanism.
    """
    args = [binary, "--solver", solver, "--time-limit", str(time_limit_ms), model_path]
    try:
        result = subprocess.run(
            args, capture_output=True, text=True,
            timeout=(time_limit_ms / 1000.0) + 10,
            env=_environment_for(binary),
        )
        return result.stdout or "", result.stderr or "", False
    except subprocess.TimeoutExpired:
        return "", "", True


# =============================================================================
# MinizincBackend
# =============================================================================

class MinizincBackend(ProverBackend):
    """Bounded CP finite-domain refutation search via the ``minizinc`` CLI.

    Registry name ``"minizinc"``. Refutation-only, per the module docstring
    and :mod:`~unicode_fol_kit.atp.finite_domain`'s own "ONE RULE" — searches
    domain sizes ``1 … max_size`` in turn for a model of ``premises ∧ ¬φ``;
    the first one found is independently re-verified
    (:func:`~unicode_fol_kit.atp.finite_domain.verify_model`) and returned as
    REFUTED (or, if verification fails, ERROR/``"infra"`` — never a
    countermodel this module could not confirm itself). Exhausting every
    size without a model is UNKNOWN/``"bound_hit"``; running out of the
    ``timeout`` budget partway through the size sweep is UNKNOWN/``"timeout"``
    — the two are DELIBERATELY different ``reason`` values (see
    :mod:`~unicode_fol_kit.atp.protocol`'s module docstring on why
    ``bound_hit`` and ``timeout`` must never be conflated): only the former
    means "the whole search space up to max_size was actually covered".
    """

    name = "minizinc"
    logics = frozenset({"fol"})
    external = True

    def available(self) -> bool:
        """Pure discovery: see :func:`minizinc_available`."""
        return minizinc_available()

    def available_for(self, options: dict) -> bool:
        """Whether the binary the run will use is there: ``minizinc_path=`` when the
        call names one (it must resolve to something the run can start, as an explicit
        path or as a name on ``PATH``; on Windows the installed ``minizinc.exe`` may be
        named without its extension, as ``subprocess`` starts it), else the discovery
        of :func:`minizinc_available` (``$UFK_MINIZINC``, then ``PATH``).
        :meth:`decide` reads ``minizinc_path=`` before it looks anywhere else, so a
        call that names a working binary is answered even where nothing is
        discoverable, and a call that names a missing one is refused here, by name,
        instead of failing inside the run."""
        path = options.get("minizinc_path")
        if path:
            return _native_command_exists(path)
        return self.available()

    def decide(self, formula: Node, premises: Sequence[Node] = (),
               timeout: int = 10000, **options) -> Verdict:
        """Decide ``premises ⊨ formula`` by CP finite-domain refutation search.

        Args:
            formula: the goal.
            premises: entailment premises (validity search when empty). A
                free variable of the premises or the goal is a parameter:
                one unknown element, the same in all of them, as in
                ``ClingoBackend.decide``. With ``all_different=True`` such
                a problem is answered ``unknown`` / ``unsupported``.
            timeout: milliseconds, the TOTAL wall-clock budget across every
                domain size attempted (not per-size — a size that starts
                with little budget left gets little budget, and the search
                stops rather than overrunning; see the class docstring's
                ``bound_hit`` vs ``timeout`` distinction).
            **options: ``max_size`` (default ``4``, matching
                :class:`~unicode_fol_kit.atp.protocol.ModelFinderBackend`'s
                own default so a differential test between the two can use
                matching bounds out of the box) — the largest domain size
                tried; ``solver`` (default ``"gecode"``, MiniZinc's bundled
                default) — the ``--solver`` id passed to the CLI;
                ``all_different`` (default ``False``) — forwarded to
                :class:`~unicode_fol_kit.atp.finite_domain.FiniteDomainProblem`;
                ``minizinc_path`` overrides binary discovery (see
                :func:`_minizinc_binary`).

        Returns:
            A :class:`~unicode_fol_kit.atp.protocol.Verdict`. ``status`` is
            NEVER ``"proved"`` (see the class docstring). REFUTED carries
            ``countermodel = {"kind": "finite_structure", "data":
            structure.to_dict()}`` (round-trippable via
            :func:`~unicode_fol_kit.semantics.structures.structure_from_dict`
            — fixing the bare-``repr`` weakness
            :class:`~unicode_fol_kit.atp.protocol.ModelFinderBackend` has).

        Raises:
            BackendUnavailable: no ``minizinc`` binary is reachable (see
                :func:`_minizinc_binary`) — mirrors
                :class:`~unicode_fol_kit.atp.protocol.Prover9Backend` /
                :class:`~unicode_fol_kit.atp.protocol.VampireBackend`
                raising this directly from ``decide()`` as a defensive
                re-check, not only from :func:`~unicode_fol_kit.atp.protocol.run_backend`.
        """
        binary = options.pop("minizinc_path", None) or _minizinc_binary()
        if binary is None:
            raise BackendUnavailable(
                "minizinc: no binary found (set $UFK_MINIZINC or put "
                "'minizinc' on PATH) — see "
                "unicode_fol_kit/atp/minizinc_backend.py for the acquisition "
                "path."
            )
        max_size = options.pop("max_size", 4)
        solver = options.pop("solver", "gecode")
        all_different = options.pop("all_different", False)

        # A free variable is a parameter of the problem: one unknown element, the same in
        # the premises and the goal. Each is replaced here, in all of them together, by a
        # constant of its own name, and only then is the goal negated (¬∀x φ(x) is not
        # ∀x ¬φ(x)); a countermodel reports the element under the variable's name. No
        # premise is closed universally: P(x) does not entail P(alpha).
        try:
            read, parameters = parameterize(list(premises) + [formula], after_variables=True)
        except NotImplementedError as exc:
            return Verdict(UNKNOWN, self.name, reason="unsupported", detail=str(exc))
        if all_different and parameters:
            # The constants are pairwise distinct under this option, a parameter may equal
            # any of them, and the model states distinctness over every constant it declares.
            return Verdict(
                UNKNOWN, self.name, reason="unsupported",
                detail=("minizinc: all_different=True with the free variable"
                        f"{'s' if len(parameters) > 1 else ''} "
                        f"{', '.join(repr(name) for name in sorted(parameters))}: a parameter "
                        "is not one of the pairwise distinct constants, and this route cannot "
                        "leave it out of the distinctness constraint. Bind the variable or "
                        "drop all_different."))
        sentences: Tuple[Node, ...] = tuple(read[:-1]) + (Not(read[-1]),)
        # Many-sorted input is relativised to plain classical FOL HERE, once,
        # before Signature.from_formulas / to_minizinc's own fragment_check
        # call ever see it -- see finite_domain.lower_msfol's own docstring
        # and this module's "Many-sorted input" section. A no-op for every
        # unsorted-only caller (the pre-existing test suite): returns
        # `sentences` untouched when nothing sorted is present.
        sentences = lower_msfol(sentences)

        try:
            signature = Signature.from_formulas(sentences)
        except (TypeError, ValueError) as exc:
            return Verdict(UNKNOWN, self.name, reason="unsupported",
                           detail=f"could not derive a signature: {exc}")

        start = time.perf_counter()
        budget_s = max(0.001, timeout / 1000.0)

        for size in range(1, max_size + 1):
            elapsed = time.perf_counter() - start
            remaining_s = budget_s - elapsed
            if remaining_s <= 0:
                return Verdict(
                    UNKNOWN, self.name, reason="timeout", wall_time=elapsed,
                    detail=f"time budget exhausted before size {size} "
                           f"(max_size={max_size})",
                )

            try:
                problem = FiniteDomainProblem(
                    sentences, size, signature=signature,
                    all_different=all_different,
                )
            except (TypeError, ValueError) as exc:
                return Verdict(UNKNOWN, self.name, reason="unsupported",
                               wall_time=time.perf_counter() - start,
                               detail=str(exc))

            try:
                model_text = to_minizinc(problem)
            except NotImplementedError as exc:
                # The same NotImplementedError would recur at every size (it
                # depends only on `sentences`, never on `size`), so there is
                # no point looping further — return immediately.
                return Verdict(UNKNOWN, self.name, reason="unsupported",
                               wall_time=time.perf_counter() - start, detail=str(exc))

            time_limit_ms = max(1, int(remaining_s * 1000))
            tmp_path = None
            try:
                with tempfile.NamedTemporaryFile(
                    mode="w", suffix=".mzn", delete=False, encoding="utf-8",
                ) as tmp:
                    tmp.write(model_text)
                    tmp_path = tmp.name
                stdout, stderr, timed_out = _run_minizinc(
                    tmp_path, binary, solver, time_limit_ms)
            except OSError as exc:
                return Verdict(ERROR, self.name, reason="infra",
                               wall_time=time.perf_counter() - start,
                               detail=f"{type(exc).__name__}: {exc}")
            finally:
                if tmp_path is not None:
                    try:
                        os.unlink(tmp_path)
                    except OSError:
                        pass

            if timed_out:
                return Verdict(
                    UNKNOWN, self.name, reason="timeout",
                    wall_time=time.perf_counter() - start,
                    detail=f"minizinc did not finish size {size} within the "
                           "time budget",
                )
            if "=====UNSATISFIABLE=====" in stdout:
                continue
            if "=====UNKNOWN=====" in stdout:
                return Verdict(
                    UNKNOWN, self.name, reason="timeout",
                    wall_time=time.perf_counter() - start,
                    detail=f"minizinc's own --time-limit expired searching "
                           f"size {size} without determining satisfiability",
                )

            solution = _parse_minizinc_solution(stdout)
            if solution is None:
                return Verdict(
                    ERROR, self.name, reason="infra",
                    wall_time=time.perf_counter() - start,
                    detail="minizinc produced no recognised status or "
                           f"solution at size {size}: stdout="
                           f"{stdout[-500:]!r} stderr={stderr[-500:]!r}",
                )
            try:
                atoms = _atoms_from_solution(problem.signature, solution, size)
                structure = structure_from_solution(
                    problem.signature, atoms, size,
                    all_different=problem.all_different,
                )
            except (TypeError, ValueError) as exc:
                return Verdict(
                    ERROR, self.name, reason="infra",
                    wall_time=time.perf_counter() - start,
                    detail="could not reconstruct a structure from "
                           f"minizinc's solution: {exc}",
                )
            verify_reason = verify_model(structure, sentences)
            if verify_reason is not None:
                return Verdict(
                    ERROR, self.name, reason="infra",
                    wall_time=time.perf_counter() - start,
                    detail="minizinc reported a solution that failed "
                           "independent verification -- refusing to report "
                           f"REFUTED: {verify_reason}",
                )
            return Verdict(
                REFUTED, self.name, wall_time=time.perf_counter() - start,
                countermodel={"kind": "finite_structure", "data": structure.to_dict()},
                detail=f"finite countermodel of size {size} found by "
                       f"minizinc (solver={solver})",
            )

        return Verdict(
            UNKNOWN, self.name, reason="bound_hit",
            wall_time=time.perf_counter() - start,
            detail=f"no countermodel up to size {max_size}",
        )
