"""Entailment checking via the Prover9 theorem prover (LADR backend).

Builds a Prover9 ``.in`` file (``set(prolog_style_variables)``, one
``formulas(assumptions)`` list of premises, one ``formulas(goals)`` list
holding the conclusion) and looks for ``THEOREM PROVED`` in Prover9's stdout.

**ASCII/legality sanitisation (problem-level seam).** ``Node.to_prover9()``
renders a predicate/function name completely verbatim (no transliteration,
no case change at all) and a Constant name transliterated to ASCII
(:func:`~unicode_fol_kit.fol._fol_nodes.constant_name_to_ascii`) but without
fixing a digit-leading result (and, for a name Prover9 would read as a
variable, in double quotes: see the next section). Prover9's own reader grammar for a symbol
token is ``NAME: /[A-Za-z_][A-Za-z0-9_]*/`` (see
:data:`unicode_fol_kit.fol.prover9_input`'s ``NAME`` terminal) — a
non-ASCII character or a digit-leading name is not a legal token there at
all. Neither gap could be reached before the toolkit's own identifier
grammar was widened to accept Unicode letters and digit-leading names; both
can now. Exactly like :mod:`atp._tptp_problem`, the fix has to live at
problem level, not inside ``Node.to_prover9()`` itself (see that module's
docstring for the full reasoning — independent per-node renaming loses
injectivity and never reaches a caller that needs to invert it):
:func:`_sanitize_for_prover9` walks every premise and the conclusion
TOGETHER, replaces only the names that are not already Prover9-legal with
an ASCII, non-digit-leading, whole-problem-injective replacement, and
returns a :class:`Prover9NameMap` recording exactly what was renamed. An
already-legal name — including an upper-case-initial predicate WITH arguments,
the kit's own ``Human(x)`` convention — passes through completely unchanged,
with ONE exception, a symbol written in arity-0 position that Prover9 would read
as a variable (next section: a CONSTANT, and a NULLARY predicate), so this
sanitisation step never alters the output for a formula this module was already
exporting correctly. A name that is no word at all (a space, a dot, a hyphen, a
non-ASCII letter) is replaced by an ASCII word, each character that is no letter,
digit or underscore by the reversible escape ``uXXXX`` the transliteration of a
non-ASCII character uses; a name that begins with ``$`` is refused (below).

**One name, several symbols (the key is kind, name and arity).** Prover9 keeps ONE
symbol per spelling, and refuses a file that uses a spelling at two arities, or both
as a relation and as a function (measured on Prover9 2026-8A: ``The following symbols
are used with multiple arities: P/2, P/1`` and ``...used as both relation and function
symbols: p/0``). The kit keeps them apart: ``P(x)`` and ``P(x, y)`` are two predicates, a
nullary ``p`` a third, the constant ``p`` and the function ``p(x)`` two more, and a
sort ``S`` is the unary predicate ``S`` (ONE symbol, as everywhere in this kit). The
writer therefore keys every symbol on ``(kind, name, arity)`` (kind is ``"predicate"``
or ``"function"``; a constant is a function of arity 0, a proposition a predicate of
arity 0) and gives the FIRST symbol of a spelling that spelling, the second and every
later one a replacement that is no other symbol's spelling (``P`` at arity 2 becomes
``P2``, a numeric suffix as everywhere else). The map records each symbol
(:attr:`Prover9NameMap.symbols`); a name that has one symbol only is looked up as
before. The comparison symbols and the arithmetic operators written infix are no
symbols of this kind, and ``$true`` / ``$false`` as nullary atoms are Prover9's truth
constants ``$T`` and ``$F``.

**Numerals.** A numeral is an uninterpreted constant here, as it is for the Z3 route
(``Number.to_z3`` names it by its value, so ``⊢ 1 ≠ 2`` is not valid for Z3 and not
provable for Prover9: Prover9 has no arithmetic either). It is ONE constant per VALUE,
written in double quotes: ``Number(1)`` and ``Number(1.0)`` are equal nodes and are both
``"1"``, ``2.5`` is ``"2.5"`` and ``-1`` is ``"-1"`` (see
:meth:`~unicode_fol_kit.fol._fol_nodes.Number.to_prover9`), so ``P(1) ⊢ P(1.0)`` is
written ``P("1")`` and ``P("1")``. Every numeral is quoted, a non-negative integer too:
Mace4, which reads the same formula lists, takes a bare integer for a domain element of its
own and all of them for distinct elements (``1 != 2`` has no countermodel there), which the
kit's numerals are not; a quoted symbol is a plain constant for both programs. (Mace4 does not
read the whole file this writer writes: it stops at ``set(auto_denials)`` and at the
``clear(print_...)`` flags with "Flag not recognized", measured on Mace4 2026-8A. With those
lines left out, or with ``set(prolog_style_variables)`` alone before the lists, it reads the
problem and finds a countermodel of an invalid one. The kit has no Mace4 route.) A number and a
constant spelled like it (``Number(1)`` and ``Constant('1')``, ``Number(1.0)`` and
``Constant('1.0')``) are ONE symbol for Z3 and for the TPTP writers, so the pair is
refused by name here too.

**Upper-case constants (the variable rule).** Every file written here sets
``prolog_style_variables``, under which Prover9 reads a symbol in TERM position
as a VARIABLE iff it begins with an upper-case letter (LADR ``symbols.c``
``variable_name``: ``*s >= 'A' && *s <= 'Z'``; the manual: "If this flag is set,
variables in clauses start with (upper case) 'A' through 'Z'"). That applies to
every arity-0 symbol in term position, so a :class:`Constant` named ``Gaseous``
(an ontology individual looks exactly like that) written verbatim makes
``P(Gaseous)`` read as ``for all X, P(X)`` and the route prove non-theorems.
:func:`_sanitize_for_prover9` therefore treats such a constant as NOT legal and
renames it, like a non-ASCII name, to a lower-case-initial token that is
injective over the whole problem; the rename is recorded in
:attr:`Prover9NameMap.constants` (and mirrored in ``mapping`` when the name is
not also a predicate/function name). What is NOT renamed: a predicate or
function WITH arguments (``Human(x)``, ``Gaseous(c)`` -- the symbol is not a
constant term, only its arguments are read for variables), so the kit's
Capitalised predicate convention is untouched, and the same word may be a
predicate and a constant at once (an OWL pun: class ``Person`` and individual
``Person``) with the two getting different tokens. A leading underscore is
treated like an upper-case letter: the LADR source reads only ``A``..``Z`` and
``_x`` is a constant to Prover9 2026-8A (measured, with the flag and without it), and to this
kit's own Prover9 reader, but the Prolog convention reads it as a variable, and the rename is
harmless where Prover9 would not have needed it.

A bare NULLARY predicate is the same shape. LADR applies ``set_vars_recurse`` to
the atom term itself, and a nullary atom IS an arity-0 term, so an upper-case
``Rain`` is read as a variable too (measured on Prover9 2026-8A: the bare
``Rain & Wind`` is refused, "cannot be used as atomic formulas, because they are
variables"). It is renamed by the same mechanism as a constant, to a
lower-case-initial token that is injective over the whole problem and recorded in
:attr:`Prover9NameMap.nullary_predicates` (mirrored in ``mapping`` when the word
has no other role): ``Atom("Rain", [])`` is written ``rain``. A predicate WITH
arguments (``Rain(x)``) stays as it is. A nullary predicate and a constant of the
same spelling get two different tokens, because Prover9 keeps one symbol per
spelling and refuses a file in which it is both a proposition and a constant.

The single ``Constant.to_prover9()`` and ``Atom.to_prover9()`` cannot rename (they
have no view of the other formulas), so they write such a name in double quotes
instead, ``P("Gaseous")`` and ``"Rain"``: a double-quoted symbol is never a
variable in Prover9. This writer never reaches that branch, because after the
rename no constant or proposition is variable-shaped.

**``$``-words.** A name that begins with ``$`` (a predicate, a function, a constant
or a sort) is refused by name: Prover9 keeps those words for itself (``$T``, ``$F``,
``$ANSWER``), so a symbol spelled like one is not a name of the user's.

**The quantifier words.** ``all`` and ``exists`` are not names either. LADR reads
``exists(X) & ...`` as the quantifier ``exists X`` followed by a stray ``&`` (measured on
Prover9 2026-8A: it echoes ``(exists W exists W &(Q(c) & R(c)))`` and refuses the file with
``symbols used with multiple arities: &/1, &/2``), so a sort named ``exists`` (whose guard
atom is ``exists(X)``), or any predicate or function of that name, is not read as a symbol.
The writer renames such a symbol like one whose spelling is taken (``exists2``). The single
renderers write the word in double quotes. ``v``, the third identifier-shaped word of
Prover9's operator table, is read as an ordinary symbol in every position tried.

**Reserved words by arity.** Three more spellings are syntax to LADR or to a reader of its
files only at ONE number of arguments (measured on Prover9 2026-8A, with a sweep over
the words of its source): ``if`` with three arguments (LADR reads the first argument as a
formula, so ``(all W if(W, a, a))`` is refused and ``if(a, b, c)`` makes ``a`` a relation
symbol), ``end_of_list`` with none (the bare word ends a list) and ``formulas`` with one (it
is also the header of a list). The writer gives the symbol of such a name and arity a token
of its own and leaves the same word at another arity alone; the single renderers write it
in double quotes (:data:`~unicode_fol_kit.fol._fol_nodes._PROVER9_RESERVED_SYMBOLS`).

**Counting quantifiers.** ``∃≥n x φ`` is written as ``n`` distinct witnesses, which
need names. Every name the writer mints for one is fresh against EVERY name of the
whole problem, of every kind (predicate, function, constant, sort, variable), compared
case-folded because Prover9 writes a variable in upper case and reads ``X0`` and ``x0`` as
one (:func:`~unicode_fol_kit.fol._identifiers.symbol_names`), not only against the matrix it
expands, so that the expansion never rebinds a variable of the formula around it
(``(all X0 (A(X0) -> (exists X0 ...)))``).

**Re-bound binders.** LADR renames a variable that a quantifier binds inside the scope of a
quantifier of the same name (``(all W (all W P(W, x0)))``), to a symbol it picks itself,
the first of ``x0``, ``x1``, ... that is no variable in scope; it does not look at the
constants of the formula, so a constant ``x0`` is then bound by the quantifier (measured
on Prover9 2026-8A: that formula is clausified to ``P(A, A)``, and the premise
``∀w ∀w P(w, x0)`` proves ``P(alpha, alpha)``, which it does not entail). The writer
renames a binder that sits inside the scope of one of its own name itself, to a fresh variable
(:func:`_rename_rebound_binders`; names are compared as Prover9 reads them, in upper case),
so LADR has nothing to rename, and keeps the spellings LADR picks (``x`` or ``y`` followed
by digits, with no leading zero) away from the constants and propositions of the problem
(:data:`_LADR_MINTED_VARIABLE`: ``x0`` is written ``x0_``). Two quantifiers of one name that
are siblings are no re-binding, which was measured as well, and are written as they are. The
single ``Node.to_prover9()`` makes the same renaming of the node it writes, with this very
function (and the same counting witnesses), so the text it writes means the node as well.
The Skolem names LADR gives (``c1``, ``f1``, ...) skip every symbol the file has (measured:
a constant ``c1`` is left alone and the Skolem constant becomes ``c2``), so a user symbol of
that spelling keeps it.

**Free variables.** A free variable of a problem is a PARAMETER: one unknown element, the
same in every premise and in the conclusion, which is what Z3 and the tableau read and the
assignment-wise consequence relation of the textbooks (``P(x) ⊢ P(alpha)`` is not valid:
universe {0, 1}, ``x`` = 1, ``alpha`` = 0, ``P`` = {1}). Prover9 would close each formula
universally on its own (``P(X)`` is ``∀X P(X)``), which is another question and proves it. The
writer therefore replaces every free variable, problem-wide, by a constant of a name no other
symbol of the problem has (the variable's own name when it is free), written like every other
constant, and records it in :attr:`Prover9NameMap.free_variables` (variable name to token;
:meth:`Prover9NameMap.reverse` gives the variable's name back). The text written has no free
variable: its closure is the identity.

**Łukasiewicz connectives.** ``p ∨ ¬p`` with the weak disjunction and the Łukasiewicz negation
is the maximum of ``p`` and ``1 − p``, which is ``1/2`` at ``p = 1/2``: not valid, while its
classical image is. Their classical collapse is a different logic, so the writer refuses a
formula that holds one, by name, as a single ``Node.to_prover9()`` does (``to_fol`` collapses
explicitly, and the result is written as any classical formula).

There is currently no Prover9 "detailed" route reading a proof or
countermodel back out of Prover9's own output (:func:`check_logical_entailment`
and :class:`~unicode_fol_kit.atp.protocol.Prover9Backend` both report a bare
``bool``/PROVED-or-UNKNOWN verdict, nothing that carries a Prover9-chosen
symbol name back to the caller) — so there is no Rückweg to wire up here
today. :class:`Prover9NameMap` still exists and is still returned by
:func:`generate_prover9_input_with_mapping` (mirroring
:mod:`atp._tptp_problem`'s ``..._with_mapping``/plain-wrapper split) so a
future detailed route has the same reversible mapping available without
redesigning this module.

**A refused problem.** :func:`check_logical_entailment` returns ``False`` for
every run without a ``THEOREM PROVED`` line, and by default that includes a
problem Prover9 refused to read (its fatal-error exit, code 1 in the Prover9
manual) and a binary that could not be started (exit 127 "not found" or 126 "not
executable", which is what ``wsl.exe <path>`` reports for a path that does not
exist inside WSL). ``raise_on_rejection=True`` separates the two by raising
:class:`Prover9Rejected` with Prover9's own message;
:class:`~unicode_fol_kit.atp.protocol.Prover9Backend` passes it and reports
the refusal as an ERROR verdict rather than "found no proof". Prover9's output
is decoded as UTF-8 with undecodable bytes replaced: its fatal message quotes the
input around the error and can cut a multi-byte character in half, which must
reach the caller as a refusal with a message, not as a decoding error.

**Prover9 inside WSL.** ``use_wsl=True`` (the Prover9 backend reads it from the
``use_wsl`` option and ``$UFK_PROVER9_WSL=1``, the way the Vampire backend does)
runs ``wsl.exe <prover9_path> -f <file>``, where ``prover9_path`` is the path
INSIDE WSL and the Windows temp file is translated with ``wslpath``. The
translation happens before the timeout window opens: a slow ``wslpath`` is a
failure to start (``OSError``), never a Prover9 timeout. Prover9 never reads the
caller's standard input (``stdin`` is the null device): it reads the problem from
stdin when it is not given ``-f``, and would block on an inherited pipe.

**A run the kit stopped.** ``timeout`` (seconds, default 30) is the wall-clock
budget handed to the subprocess; by default a run it cuts off is ``False`` like
any run without a proof. ``raise_on_timeout=True`` separates it by raising
:class:`Prover9TimedOut`, which the backend reports as UNKNOWN / ``"timeout"``
(its own ``timeout`` argument, in milliseconds, is the budget) instead of "found
no proof". Prover9's own exit codes 2-7 stay "found no proof": the kit writes no
``max_seconds`` into the problem, so none of them is the kit's budget.

**Many-sorted (MSFOL) soundness.** A sort ``S`` is the extension of the unary
predicate ``S`` (one symbol), never empty, and a sorted constant ``c:S`` lies in
it. The writer LOWERS every sorted node first (the auto-reduction
``fol.nodes.to_fol``: ``∀x:S φ`` is ``∀x (S(x) → φ)``, ``c:S`` is the plain constant
``c``), which by itself says neither that the sort is non-empty nor that ``c`` is in
it, so it states both as their own extra lines in ``formulas(assumptions)`` —
alongside the premises, i.e. Prover9 may assume them freely, exactly what an
entailment's premise side means; never inside ``formulas(goals)``, and never folded into
``Node.to_prover9()`` itself, which stays polarity-blind:

* ``unicode_fol_kit.fol._msfl_nodes.nonempty_sort_axioms(premises +
  [conclusion])``: one ``∃x S(x)`` per sort;
* ``unicode_fol_kit.fol._msfl_nodes.sort_membership_axioms`` of the same sentences, one
  atom ``S(c)`` per sorted constant ``c:S``. A sorted and a plain constant of one
  name are one symbol and get one token; a constant with two sorts gets two atoms.
  Without them ``∀x:Human Mortal(x) ⊢ Mortal(socrates:Human)`` is not proved, because
  the plain text forgets that ``socrates`` is a ``Human``.

The lowered formulas and these axioms then go through :func:`_sanitize_for_prover9`
TOGETHER, so a sort name is a name like any other: ``S(x)`` in the guard of a
quantifier, in an axiom and in a plain atom ``S(c)`` is one symbol, a non-ASCII sort
is written under an ASCII replacement, a sort named like a constant of the problem
(``person`` and ``person``) gets the constant another token, and a predicate ``S`` of
another arity is another symbol. All of this is empty for an unsorted problem, so the
generated text is byte-identical to before.
"""

import os
import re
import subprocess
import tempfile
from dataclasses import dataclass, field, replace
from typing import Any, Dict, List, Tuple, cast

from ..fol._fol_nodes import (
    _PROVER9_QUANTIFIERS, _PROVER9_RESERVED_SYMBOLS, _number_text, _prover9_reads_as_variable,
)
from ..fol._identifiers import fresh_variables, symbol_names
from ..fol._msfl_nodes import (
    _LUK_NO_CLASSICAL_EXPORT, _SORTED_NODE_TYPES, LukEquivalence, LukImplication, LukNegation,
    SortedConstant, StrongConjunction, StrongDisjunction, WeakConjunction, WeakDisjunction,
    free_variables, nonempty_sort_axioms, sort_membership_axioms, substitute,
)
from ..fol._numeral_symbols import numeral_name
from ..fol._team_nodes import SlashedExists
from ..fol._tptp_symbols import check_variable_names, is_tptp_boolean_atom
from ..fol.nodes import (
    Atom, Constant, Contrast, Count, Function, Measure, Node, Number, And, Quantifier, Variable,
)
from ..fol.prover9_input import _RESERVED_SYMBOLS as _READER_RESERVED_SYMBOLS
from ._ascii_names import ascii_safe_base
from .vampire_entailment import _to_wsl_path

__all__ = ["check_logical_entailment", "Prover9NameMap", "Prover9Rejected",
           "Prover9TimedOut", "generate_prover9_input_with_mapping"]


# ---------------------------------------------------------------------------
# ASCII/legality sanitisation — see the module docstring.
# ---------------------------------------------------------------------------

#: The text the refusals of the writer start with.
_WRITER = "generate_prover9_input_with_mapping"

_PREDICATE = "predicate"
_FUNCTION = "function"

#: One symbol of a problem as the kit sees it: ``(kind, name, arity)``, kind being
#: ``"predicate"`` or ``"function"`` (a constant is a function of arity 0, a
#: proposition a predicate of arity 0, a sort the predicate of that name at arity 1).
Symbol = Tuple[str, str, int]

# A raw kit-level name that is ALREADY a legal Prover9 NAME token (matches
# fol/prover9_input.py's own ``NAME: /[A-Za-z_][A-Za-z0-9_]*/`` terminal) and
# is pure ASCII (Node.to_prover9 never transliterates a predicate/function
# name, only a Constant, and even that doesn't fix digit-leading — see the
# module docstring). Names the widened parser can now produce never contain
# anything outside unicode letters/digits/underscore/combining marks, so
# this is the exact complement of "needs a replacement".
_PROVER9_SAFE_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")

_NOT_A_WORD_CHARACTER = re.compile(r"[^A-Za-z0-9_]")


def _is_prover9_safe(name: str) -> bool:
    return bool(name) and name.isascii() and bool(_PROVER9_SAFE_RE.fullmatch(name))


#: The words LADR reads as SYNTAX and never as a name: the identifier-shaped
#: members of the reserved set the kit's own Prover9 reader keeps
#: (``fol.prover9_input._RESERVED_SYMBOLS``: ``all``, ``exists`` and the infix
#: operator ``v``; the rest of that set is punctuation, which no name can be).
#: A rename that lands on one of these is a text Prover9 rejects or reads as
#: something else -- ``Constant("All")`` lower-cases to ``all`` -- so the
#: renamer treats each as TAKEN and the new token gets its numeric suffix
#: (``all2``), like any other token that is already in use.
_PROVER9_KEYWORDS = frozenset(
    symbol for symbol in _READER_RESERVED_SYMBOLS if _PROVER9_SAFE_RE.fullmatch(symbol))


def _lowercase_initial(base: str) -> str:
    """Force a lowercase-initial result for a SYNTHESISED (previously
    illegal) name — never applied to an already-legal passthrough name, so
    this never touches the kit's own upper-case-initial predicate
    convention (see the module docstring's ``Atom("Rain", [])`` note).
    Lowercase-initial avoids Prover9's own ``prolog_style_variables``
    ambiguity (an upper-case- or underscore-initial symbol reads as a
    VARIABLE) for names this module is choosing fresh, rather than
    reproducing that ambiguity for brand-new tokens nobody has to preserve
    the case of.
    """
    if base and base[0] == "_":
        # An underscore-initial token is read as a variable too (module
        # docstring, "Upper-case constants").
        return "c" + base
    return base[0].lower() + base[1:] if base else base


def _ascii_token_base(name: str) -> str:
    """The word a name that is no legal token is replaced by (before the
    lower-casing and the numeric suffix): the name transliterated to ASCII with a
    non-digit start (:func:`~unicode_fol_kit.atp._ascii_names.ascii_safe_base`),
    then every character that is still no letter, digit or underscore (a space, a
    dot, a hyphen) as the reversible ``uXXXX`` escape that transliteration uses for
    a non-ASCII character."""
    return _NOT_A_WORD_CHARACTER.sub(lambda m: "u%04x" % ord(m.group()),
                                     ascii_safe_base(name, "s"))


#: The names LADR gives to the variables it renames itself: ``x0``, ``x1``, ... when it
#: clausifies a formula that binds a name inside the scope of a binder of the same name
#: (LADR's ``cnf.c``: ``unique_qvars`` and ``skolem``; the same source has ``y0``, ``y1``,
#: ... in its ``eliminate_rebinding``, which the clausification of a problem file was
#: measured not to reach). LADR picks the first such name that is no variable IN SCOPE, and
#: does not look at the constants of the formula, so a constant (or a proposition) spelled
#: like one is bound by the quantifier that took the name over (measured on Prover9
#: 2026-8A: ``(all W (all W P(W, x0)))`` is clausified to ``P(A, A)``, and so is the same
#: formula with a constant ``x1`` under three nested binders of one name). The writer never
#: leaves a binder inside the scope of one of the same name (:func:`_rename_rebound_binders`),
#: so LADR has nothing to rename; the spelling is kept away from the constants and
#: propositions of the problem all the same, so that no name of the user's is ever the one
#: LADR would choose. LADR counts from 0 and writes no leading zero. The Skolem names
#: LADR gives (``c1``, ``c2``, ... and ``f1``, ``f2``, ...) skip every symbol the file
#: already has, and are not a case of this (measured: a constant ``c1`` of the problem is
#: left alone and the Skolem constant becomes ``c2``).
_LADR_MINTED_VARIABLE = re.compile(r"[xy](?:0|[1-9][0-9]*)")


def _is_ladr_minted(name: str) -> bool:
    """Whether ``name`` is spelled like a variable LADR mints for itself
    (:data:`_LADR_MINTED_VARIABLE`)."""
    return _LADR_MINTED_VARIABLE.fullmatch(name) is not None


def _keeps_spelling(name: str, arity: int) -> bool:
    """Whether a symbol of this name and arity is written under its own name: it is
    a legal token, not an arity-0 symbol Prover9 would read as a variable, not an
    arity-0 symbol spelled like a variable LADR renames to (:data:`_LADR_MINTED_VARIABLE`),
    not a word reserved at this arity (:data:`_PROVER9_RESERVED_SYMBOLS`: ``if`` with three
    arguments, ``end_of_list`` with none, ``formulas`` with one), and not one of the
    quantifier words ``all`` and ``exists``, which LADR reads as a quantifier whenever the
    symbol stands first and is applied to a variable (so ``exists(X) & ...`` is no atom: the
    guard of a sort named ``exists`` is exactly that)."""
    return (_is_prover9_safe(name) and name not in _PROVER9_QUANTIFIERS
            and (name, arity) not in _PROVER9_RESERVED_SYMBOLS
            and not (arity == 0 and (_prover9_reads_as_variable(name) or _is_ladr_minted(name))))


def _reserve_token(base: str, used: set, arity: int) -> str:
    """The first token of ``base``, ``base2``, ``base3``, ... that is not in ``used`` and is
    no word reserved at this arity, reserved (the numeric-suffix scheme of
    :func:`~unicode_fol_kit.atp._ascii_names.reserve_rendered`), and, for a symbol of arity 0,
    is not spelled like a variable LADR renames to either (:data:`_LADR_MINTED_VARIABLE`).
    Such a base gets a trailing underscore first (``x0`` becomes ``x0_``, then ``x0_2``):
    every ``x`` or ``y`` followed by digits is that kind of name, so no numeric suffix
    could leave the family."""
    nullary = arity == 0
    if nullary and _is_ladr_minted(base):
        base += "_"
    candidate, index = base, 2
    while candidate in used or (candidate, arity) in _PROVER9_RESERVED_SYMBOLS:
        if nullary and base in ("x", "y"):
            base += "_"
            candidate = base
            continue
        candidate = f"{base}{index}"
        index += 1
    used.add(candidate)
    return candidate


def _symbol_what(kind: str, name: str, arity: int, sorts) -> str:
    """What a symbol is called in a refusal."""
    if kind == _PREDICATE and arity == 1 and name in sorts:
        return "the sort"
    if arity == 0:
        return "the proposition" if kind == _PREDICATE else "the constant"
    return "the predicate" if kind == _PREDICATE else "the function"


def _dollar_refusal(kind: str, name: str, arity: int, sorts) -> NotImplementedError:
    return NotImplementedError(
        f"{_WRITER}: {_symbol_what(kind, name, arity, sorts)} {name!r} is a '$'-word. "
        "Prover9 keeps the words that begin with '$' for itself (its truth constants are "
        "$T and $F, its answer literal $ANSWER), so a symbol spelled like that is not a "
        "name of the user's and would be read as one of those. The nullary atoms $true "
        "and $false are the truth constants and are written $T and $F; rename any other "
        "symbol before exporting this problem.")


def _comparison_refusal(name: str, arity: int) -> NotImplementedError:
    return NotImplementedError(
        f"{_WRITER}: the comparison {name!r} is written infix and takes exactly two "
        f"arguments, but it is applied to {arity}; Prover9 has no other reading of it. "
        "Rename the predicate before exporting this problem.")


def _numeral_clash_refusal(text: str, name: str) -> NotImplementedError:
    return NotImplementedError(
        f"{_WRITER}: the number {text} and the constant {name!r} are spelled alike: they "
        "are ONE symbol for the Z3 route (and the TPTP writers refuse the pair), and this "
        "writer would write them as two, a number as its value in double quotes and "
        "a constant renamed to a word, so the problem would not mean what the formulas "
        "say. Rename the constant before exporting this problem.")


@dataclass
class Prover9NameMap:
    """The renamings :func:`_sanitize_for_prover9` chose for one problem.

    The key of a symbol is ``(kind, name, arity)`` (see the module docstring):
    :attr:`symbols` maps every symbol of the problem to the token it is written
    as. Prover9 keeps ONE symbol per spelling, so the first symbol of a spelling
    keeps it and a later one with the same name (another arity, or a predicate
    next to a function or a constant) gets a token that no other symbol has. A
    SINGLE flat namespace across predicate/function/constant names (unlike
    :mod:`atp._tptp_problem`'s predicate-vs-term split): Prover9's own export
    never case-folds, so an already-legal name can never collide with another
    already-legal name the way TPTP's first-letter fold can, and being
    conservative about a SYNTHESISED replacement never colliding with ANY other
    name in the problem — predicate, function, or constant alike — costs nothing
    but an occasional extra numeric suffix. ``mapping`` is the original-kit-name ->
    token dict (for a name with several symbols, the token of the first one that was
    not renamed because of the variable rule); an original name that was already
    legal maps to itself.
    """

    mapping: Dict[str, str] = field(default_factory=dict)
    used: set = field(default_factory=set)
    #: Constants whose own name Prover9 would read as a VARIABLE (upper-case or
    #: underscore initial, see the module docstring), original name -> token.
    #: Kept apart from ``mapping`` because the same word can also be a
    #: predicate/function name, which is NOT renamed; ``mapping`` carries the
    #: same entry too whenever the word has no such second role.
    constants: Dict[str, str] = field(default_factory=dict)
    #: NULLARY predicates whose own name Prover9 would read as a VARIABLE (the
    #: same rule: an atom with no arguments is an arity-0 term), original name ->
    #: token. Kept apart from ``mapping`` and from ``constants`` for the same
    #: reason: ``Rain`` may also be a predicate WITH arguments (not renamed) and a
    #: constant (renamed to its own token); ``mapping`` carries the same entry
    #: whenever the word has no other role.
    nullary_predicates: Dict[str, str] = field(default_factory=dict)
    #: Every symbol of the problem, ``(kind, name, arity)`` -> the token it is
    #: written as, in the order the symbols were first met.
    symbols: Dict[Symbol, str] = field(default_factory=dict)
    #: Every numeral of the problem, the text of its value (``2.5``; ``1`` for both
    #: ``Number(1)`` and ``Number(1.0)``) -> the text it is written as (``'"2.5"'``).
    numerals: Dict[str, str] = field(default_factory=dict)
    #: Every FREE variable of the problem, its name -> the token of the constant it is
    #: written as (see the module docstring, "Free variables"). Empty for a problem
    #: whose formulas are all closed.
    free_variables: Dict[str, str] = field(default_factory=dict)
    _seen: Dict[Symbol, None] = field(default_factory=dict)
    _claimed: Dict[str, Symbol] = field(default_factory=dict)
    _numeral_texts: set = field(default_factory=set)
    _sorts: frozenset = frozenset()

    def collect_symbol(self, kind: str, name: str, arity: int) -> None:
        """First pass: register the symbol ``(kind, name, arity)``. A symbol that is
        written under its own name keeps it if no earlier symbol has it (order-independent
        for the renamed ones — see :class:`~atp._tptp_problem._Renamer`'s docstring: the
        name is reserved immediately, so that a synthesised token never takes it); a
        symbol of an already claimed spelling, an illegal name, or an arity-0 name that
        Prover9 would read as a variable waits for :meth:`finalize`.

        Raises:
            NotImplementedError: the name begins with ``$``."""
        if name.startswith("$"):
            raise _dollar_refusal(kind, name, arity, self._sorts)
        key = (kind, name, arity)
        if key in self._seen:
            return
        self._seen[key] = None
        if _keeps_spelling(name, arity) and name not in self._claimed:
            self._claimed[name] = key
            self.used.add(name)
            self.symbols[key] = name

    def collect_numeral(self, value) -> None:
        """First pass: register the numeral ``value`` (written as
        :meth:`~unicode_fol_kit.fol._fol_nodes.Number.to_prover9` writes it): one entry per
        VALUE, so ``1`` and ``1.0`` are one numeral. The texts a constant must not carry
        (they would be this symbol under another spelling) are the name of the value, the
        text the node prints and ``str`` of the value."""
        key = numeral_name(value)
        self._numeral_texts.update((key, _number_text(value), str(value)))
        self.numerals.setdefault(key, Number(value).to_prover9())

    def collect(self, name: str, constant: bool = False, nullary: bool = False) -> None:
        """First pass for ONE name: a constant (``constant=True``), a nullary
        predicate (``nullary=True``) or, by default, a predicate with arguments.
        :meth:`collect_symbol` is the form that carries the kind and the arity."""
        if constant:
            self.collect_symbol(_FUNCTION, name, 0)
        elif nullary:
            self.collect_symbol(_PREDICATE, name, 0)
        else:
            self.collect_symbol(_PREDICATE, name, 1)

    def reserve_sort(self, sort: str) -> None:
        """Keep every synthesised token off the name of a sort of the problem. A sort is
        the unary predicate of its name and is collected as that symbol, which reserves
        its name; this is for a caller that knows a sort name and not the atom."""
        if _is_prover9_safe(sort):
            self.used.add(sort)

    def finalize(self) -> None:
        """Second pass: give a token to every symbol that is not written under its own
        name, now that every legal name of the WHOLE problem is reserved (and the LADR
        keywords, which no name may be: :data:`_PROVER9_KEYWORDS`).

        Raises:
            NotImplementedError: a number and a constant are spelled alike."""
        for kind, name, arity in self._seen:
            if kind == _FUNCTION and arity == 0 and name in self._numeral_texts:
                raise _numeral_clash_refusal(name, name)
        self.used.update(_PROVER9_KEYWORDS)
        illegal: List[Symbol] = []
        variable_like: List[Symbol] = []
        nullary_like: List[Symbol] = []
        clashing: List[Symbol] = []
        for key in self._seen:
            if key in self.symbols:
                continue
            kind, name, arity = key
            if not _is_prover9_safe(name):
                illegal.append(key)
            elif arity == 0 and _prover9_reads_as_variable(name):
                (variable_like if kind == _FUNCTION else nullary_like).append(key)
            else:
                clashing.append(key)
        for key in illegal:
            self.symbols[key] = _reserve_token(
                _lowercase_initial(_ascii_token_base(key[1])), self.used, key[2])
        for key in variable_like + nullary_like:
            self.symbols[key] = _reserve_token(_lowercase_initial(key[1]), self.used, key[2])
        for key in clashing:
            self.symbols[key] = _reserve_token(key[1], self.used, key[2])
        # The views by name, in the order of first occurrence.
        first_plain: Dict[str, str] = {}
        first_any: Dict[str, str] = {}
        for key in self._seen:
            kind, name, arity = key
            token = self.symbols[key]
            first_any.setdefault(name, token)
            if arity == 0 and _is_prover9_safe(name) and _prover9_reads_as_variable(name):
                (self.constants if kind == _FUNCTION else self.nullary_predicates)[name] = token
            else:
                first_plain.setdefault(name, token)
        for name, token in first_any.items():
            self.mapping[name] = first_plain.get(name, token)

    def get(self, name: str) -> str:
        """The token for a predicate/function name (or a constant that needed
        no variable-rule rename): the first symbol of that name; see
        :meth:`get_symbol` for one of several."""
        return self.mapping[name]

    def get_symbol(self, kind: str, name: str, arity: int) -> str:
        """The token of the symbol ``(kind, name, arity)``."""
        return self.symbols[(kind, name, arity)]

    def get_constant(self, name: str) -> str:
        """The token for ``name`` in CONSTANT position (arity-0 term)."""
        return self.symbols[(_FUNCTION, name, 0)]

    def get_nullary(self, name: str) -> str:
        """The token for the predicate ``name`` written WITHOUT arguments."""
        return self.symbols[(_PREDICATE, name, 0)]

    def get_sort(self, sort: str) -> str:
        """The token for the sort ``sort``: its guard predicate, the unary predicate
        of that name."""
        return self.symbols[(_PREDICATE, sort, 1)]

    def reverse(self) -> Dict[str, str]:
        """Flat token -> original dict (Prover9 never case-folds, so the
        token stored in ``symbols`` is exactly what would come back from any
        future reader of Prover9's own output — no fold/cap asymmetry to
        account for, unlike TPTP's predicate namespace). Tokens are unique
        over the whole problem, so the symbols merge without a clash. The token
        of the constant a free variable was replaced by (:attr:`free_variables`) maps
        back to the NAME OF THE VARIABLE, which is what the caller wrote."""
        reverse = {token: name for (_kind, name, _arity), token in self.symbols.items()}
        reverse.update({token: name for name, token in self.free_variables.items()})
        return reverse


def _is_builtin_function(node: Function) -> bool:
    """Whether ``node`` is written with a notation of its own (``(a + b)``, ``-(a)``,
    ``-(a, b)``) rather than as a symbol of the problem."""
    return node.name in Function.INFIX_OPS and (
        len(node.args) == 2 or (node.name == "-" and len(node.args) == 1))


def _is_infix_atom(node: Atom) -> bool:
    return node.predicate in Atom.INFIX_PREDS_P9 and len(node.args) == 2


def _sanitize_node_for_prover9(node: Node, names: Prover9NameMap) -> Node:
    """Rebuild ``node`` with every non-Prover9-legal symbol name replaced.

    Mirrors :func:`atp._tptp_problem._sanitize_node_for_tptp`'s structural
    recursion (``Node.map_children`` for everything that is not itself an
    Atom/Function/Constant); an already-legal name comes back as the exact
    same string, so ``Node.to_prover9()`` on the result is byte-identical to
    ``Node.to_prover9()`` on the original wherever every name involved was
    already legal (R1).
    """
    if isinstance(node, Atom):
        if _is_infix_atom(node) or is_tptp_boolean_atom(node):
            pred = node.predicate
        else:
            pred = names.get_symbol(_PREDICATE, node.predicate, len(node.args))
        return Atom(pred, [_sanitize_node_for_prover9(a, names) for a in node.args])
    if isinstance(node, Function):
        if _is_builtin_function(node):
            name = node.name
        else:
            name = names.get_symbol(_FUNCTION, node.name, len(node.args))
        return Function(name, [_sanitize_node_for_prover9(a, names) for a in node.args])
    if isinstance(node, Constant):
        return Constant(names.get_constant(node.name))
    if isinstance(node, SortedConstant):
        # Renders as the plain Constant of the same name (to_fol), and is that
        # constant: it takes the same token, whatever the name (a variable-shaped,
        # non-ASCII or digit-leading name is renamed exactly like a plain constant),
        # so the premise occurrence and its membership atom are one symbol.
        return SortedConstant(names.get_constant(node.name), names.get_sort(node.sort))
    rebuilt = node.map_children(lambda c: _sanitize_node_for_prover9(c, names))
    if isinstance(node, _SORTED_NODE_TYPES):
        # The sort is the unary predicate of its name, one symbol with the guard it lowers to.
        return replace(cast(Any, rebuilt), sort=names.get_sort(node.sort))
    return rebuilt


def _collect_names_for_prover9(node: Node, names: Prover9NameMap) -> None:
    """First pass (see :meth:`Prover9NameMap.collect_symbol`): register every
    symbol ``node`` (and its descendants) uses, without rewriting anything yet."""
    for n in node.walk():
        if isinstance(n, Atom):
            if _is_infix_atom(n) or is_tptp_boolean_atom(n):
                continue
            if n.predicate in Atom.INFIX_PREDS_P9:
                raise _comparison_refusal(n.predicate, len(n.args))
            names.collect_symbol(_PREDICATE, n.predicate, len(n.args))
        elif isinstance(n, Function):
            if not _is_builtin_function(n):
                names.collect_symbol(_FUNCTION, n.name, len(n.args))
        elif isinstance(n, (Constant, SortedConstant)):
            names.collect_symbol(_FUNCTION, n.name, 0)
        elif isinstance(n, Number):
            names.collect_numeral(n.value)
        if isinstance(n, _SORTED_NODE_TYPES):
            names.collect_symbol(_PREDICATE, n.sort, 1)


def _sanitize_for_prover9(formulas: List[Node], sorts=()) -> Tuple[List[Node], Prover9NameMap]:
    """Sanitise every formula's predicate/function/constant names for Prover9.

    Returns ``(sanitised_formulas, mapping)`` — see the module docstring.
    The single namespace is shared across ALL of ``formulas``, so the same
    original name maps to the same token everywhere (R2), and a synthesised
    token can never collide with any name anywhere in the problem,
    regardless of where each one appears
    (:meth:`Prover9NameMap.collect_symbol`/:meth:`~Prover9NameMap.finalize`'s
    two-pass split — see :class:`atp._tptp_problem._Renamer`'s docstring for
    why a single combined pass would be order-dependent). ``sorts`` names the
    sorts of the problem, for the wording of a refusal only.
    """
    names = Prover9NameMap()
    names._sorts = frozenset(sorts)
    for f in formulas:
        _collect_names_for_prover9(f, names)
    names.finalize()
    sanitised = [_sanitize_node_for_prover9(f, names) for f in formulas]
    return sanitised, names


_LUKASIEWICZ_NODES = (WeakConjunction, WeakDisjunction, StrongConjunction, StrongDisjunction,
                      LukNegation, LukImplication, LukEquivalence)


def _refuse_lukasiewicz(formula: Node) -> None:
    """Refuse a formula that holds a Łukasiewicz connective, by name.

    Their classical collapse (``to_msfol``) is a different LOGIC, not a spelling of the
    same one: the weak disjunction ``p ∨ ¬p`` is the maximum of ``p`` and ``1 − p``, which is
    ``1/2`` at ``p = 1/2``, so it is not valid, while its classical image is. A single
    ``Node.to_prover9()`` refuses these nodes for that reason, and so does this writer.

    Raises:
        NotImplementedError: a Łukasiewicz node occurs in ``formula``.
    """
    for node in formula.walk():
        if isinstance(node, _LUKASIEWICZ_NODES):
            raise NotImplementedError(
                f"{_WRITER}: {type(node).__name__} — " + _LUK_NO_CLASSICAL_EXPORT)


def _fresh_constant_names(names, taken: set) -> Dict[str, str]:
    """For each variable name in ``names``, a constant name that is no name of ``taken``
    (compared case-folded; the names chosen are added to ``taken``): the variable's own
    name when it is free, else that name with ``_1``, ``_2``, ... appended."""
    chosen: Dict[str, str] = {}
    for name in names:
        candidate, index = name, 1
        while candidate.casefold() in taken:
            candidate = f"{name}_{index}"
            index += 1
        taken.add(candidate.casefold())
        chosen[name] = candidate
    return chosen


def _replace_free_variables(formulas: List[Node]) -> Tuple[List[Node], Dict[str, str]]:
    """``formulas`` with every free variable replaced, problem-wide, by a fresh constant.

    A free variable of a problem is a PARAMETER of it: one unknown element, the same in
    every premise and in the conclusion (the assignment-wise consequence relation:
    ``Γ ⊨ φ`` iff every structure AND assignment that satisfies ``Γ`` satisfies ``φ``), so
    ``P(x) ⊢ P(alpha)`` is not valid. Prover9 would read each formula on its own as closed
    universally (``P(X)`` is ``∀X P(X)``), which is another question; and
    ``Γ(x) ⊨ φ(x)`` assignment-wise holds iff ``Γ(c) ⊨ φ(c)`` for a constant ``c`` that no
    symbol of the problem is called. The constant of a free variable carries the variable's
    own name when no other symbol of the problem (of any kind, case-folded) has it.

    Returns the formulas and the variable name -> constant name table (the names are
    the kit's; the writer's own renaming of a constant applies to them afterwards, so a
    free variable ``X`` or ``x0`` is written as a constant Prover9 reads as one).
    """
    # A slashed quantifier has no classical export and is refused when it is written; a substitution
    # into its slash set would turn it into a plain quantifier first, so a formula that holds one is
    # left as it is.
    free_per_formula = [set() if any(isinstance(n, SlashedExists) for n in f.walk())
                        else {v.name for v in free_variables(f) if isinstance(v, Variable)}
                        for f in formulas]
    order: List[str] = []
    for formula, free in zip(formulas, free_per_formula):
        for node in formula.walk():
            if isinstance(node, Variable) and node.name in free and node.name not in order:
                order.append(node.name)
    if not order:
        return list(formulas), {}
    # The names that are taken are those of the problem without the free occurrences: a
    # free variable ``x`` is not a reason to call its own constant anything else.
    stand_in = Number(0)
    stripped = []
    for formula, free in zip(formulas, free_per_formula):
        for name in free:
            formula = substitute(formula, Variable(name), stand_in)
        stripped.append(formula)
    constants = _fresh_constant_names(order, set(symbol_names(*stripped, fold=str.casefold)))
    replaced = []
    for formula, free in zip(formulas, free_per_formula):
        for name in sorted(free):
            formula = substitute(formula, Variable(name), Constant(constants[name]))
        replaced.append(formula)
    return replaced, constants


def _rename_rebound_binders(node: Node, avoid: set, scope: frozenset = frozenset()) -> Node:
    """``node`` with every binder that sits inside the scope of a binder of the same name
    renamed to a fresh variable (alpha-conversion).

    LADR renames such a variable itself, to a symbol it chooses (``x0``, ``x1``, ...,
    :data:`_LADR_MINTED_VARIABLE`), and takes a constant of that spelling for it; a text
    in which no binder is re-bound leaves LADR nothing to choose. Names are compared as
    Prover9 reads them (the upper-case of a variable name is what is written). A binder
    whose name is not in the scope of another stays as it is, so the text of a formula
    without re-bound binders is the text it always was (two sibling quantifiers on one
    name are not re-bound: ``(all X P(X)) & (all X Q(X))``). The new name is one of
    ``avoid`` — every name of the whole problem, case-folded — and is added to it.

    ``scope`` is the set of upper-case names that already bind where ``node`` stands (the free
    variables of a formula that Prover9 closes universally). The traversal keeps its own stack
    and carries the renaming that holds below a renamed binder as a table (old name -> new name),
    which is what substituting into the body would do: a formula nested thousands of levels deep
    is renamed as readily as a shallow one, without the recursion limit. The fresh names are
    minted in the order of the text, outermost binder first, left to right.
    """
    results: List[Node] = []
    work: list = [("enter", node, scope, {})]
    while work:
        step = work.pop()
        if step[0] == "enter":
            _, current, in_scope, renames = step
            if isinstance(current, Quantifier):
                variable, below = current.variable, renames
                if variable.name.upper() in in_scope:
                    first = variable.name[:1].lower()
                    letter = first if first.isascii() and first.isalpha() else "x"
                    fresh = Variable(fresh_variables(1, letter=letter, avoid=avoid)[0])
                    avoid.add(fresh.name.casefold())
                    below = {**renames, variable.name: fresh.name}
                    variable = fresh
                work.append(("binder", current.type, variable))
                work.append(("enter", current.formula, in_scope | {variable.name.upper()}, below))
            elif isinstance(current, Variable):
                results.append(Variable(renames[current.name]) if current.name in renames else current)
            else:
                children = current._child_nodes()
                work.append(("rebuild", current, len(children)))
                work.extend(("enter", child, in_scope, renames) for child in reversed(children))
        elif step[0] == "binder":
            results.append(Quantifier(step[1], step[2], results.pop()))
        else:
            _, current, count = step
            rebuilt = iter(results[len(results) - count:])
            del results[len(results) - count:]
            results.append(current.map_children(lambda child: next(rebuilt)))
    return results[0]


def _expand_for_prover9(node: Node, avoid: set) -> Node:
    """The reduction :func:`~unicode_fol_kit.fol._msfl_nodes._reduce_nl_nodes` makes,
    with the counting witnesses minted fresh against ``avoid`` (every name of the whole
    problem, case-folded: Prover9 writes a variable in upper case, so ``X0`` and ``x0`` are
    one; the names minted are added to it), and a ``Measure`` as the binary function
    ``measure`` it is written as, so that it is a symbol of the problem like any other."""
    node = node.map_children(lambda c: _expand_for_prover9(c, avoid))
    if isinstance(node, Contrast):
        return And(node.left, node.right)
    if isinstance(node, Count):
        return node._expand(avoid)
    if isinstance(node, Measure):
        return Function("measure", (node.entity, node.dimension))
    return node


def _lower_for_prover9(node: Node, avoid: set) -> Node:
    """``node`` as plain first-order logic: ``to_fol``'s reduction (sorted quantifiers
    guarded, sorted constants plain), with the counting witnesses of
    :func:`_expand_for_prover9`. The sort facts are NOT part of it (they are the
    problem's own assumptions)."""
    return _expand_for_prover9(node.to_msfol()._relativize([]), avoid)


def generate_prover9_input_with_mapping(premises: List[Node], conclusion: Node
                                        ) -> Tuple[str, Prover9NameMap]:
    """Like :func:`_generate_prover9_input`, but also returns the
    :class:`Prover9NameMap` recording every ASCII-legality rename applied.

    No current caller in this module reads a Prover9-chosen symbol name back
    out of its output (see the module docstring), but this is the function
    a future "detailed" Prover9 route would call instead of
    :func:`_generate_prover9_input`, exactly the way
    :mod:`atp.vampire_entailment`'s detailed route uses
    :func:`atp._tptp_problem.generate_tptp_problem_with_mapping`.

    Raises:
        NotImplementedError: two variables of ONE formula that Prover9 reads as one
            (``x`` and ``X`` are both written ``X``: ``∀x ∃X R(x, X)`` would be
            ``(all X (exists X R(X, X)))``). The check is the one the TPTP writers
            use (:func:`unicode_fol_kit.fol._tptp_symbols.check_variable_names`), and
            it refuses every such pair of one formula, a harmless one too (two
            quantifiers side by side, ``(∀x P(x)) ∧ (∀X Q(X))``). A single
            ``Node.to_prover9()`` has no whole-problem view: it renames a binder inside
            the scope of another (``∀x ∃X R(x, X)`` is written ``(all X (exists X0 R(X, X0)))``),
            and refuses by name only the pairs that no renaming of a binder repairs.
            A symbol named with a ``$`` (Prover9's own words), a comparison symbol
            at other than two arguments, a number spelled like a constant of the
            problem, and a Łukasiewicz connective (it has no classical reading) are
            refused too (see the module docstring).

    A free variable of the problem is written as a constant, the same in every formula, and
    recorded in :attr:`Prover9NameMap.free_variables`; a binder inside the scope of a binder
    of its own name is renamed (see the module docstring).
    """
    originals = list(premises) + [conclusion]
    for formula in originals:
        _refuse_lukasiewicz(formula)
        check_variable_names(formula, where=_WRITER, subject="problem", dialect="prover9")

    # A free variable is one unknown element of the whole problem: a constant (see
    # _replace_free_variables), before anything else reads the formulas.
    originals, free_constants = _replace_free_variables(originals)

    # Sorted nodes are lowered FIRST: the guard images and the sort facts are plain
    # first-order sentences, and go through the same sanitiser as every other symbol.
    nonempty = list(nonempty_sort_axioms(*originals))
    membership = list(sort_membership_axioms(*originals))
    # Every name of the whole problem, of every kind, case-folded (Prover9 reads ``x0`` and
    # ``X0`` as one variable): what the witnesses of a counting quantifier and the fresh
    # binders below must differ from.
    avoid = set(symbol_names(*originals, *nonempty, *membership, fold=str.casefold))
    lowered = [_lower_for_prover9(f, avoid) for f in originals]
    # No binder may sit inside the scope of one of its own name (see _rename_rebound_binders).
    # The sort facts are one binder each and are written as they are.
    lowered = [_rename_rebound_binders(f, avoid) for f in lowered]
    sorts = {n.sort for f in originals for n in f.walk() if isinstance(n, _SORTED_NODE_TYPES)}
    sanitised, mapping = _sanitize_for_prover9(lowered + nonempty + membership, sorts=sorts)
    mapping.free_variables = {
        name: mapping.symbols[(_FUNCTION, constant, 0)]
        for name, constant in free_constants.items()
        if (_FUNCTION, constant, 0) in mapping.symbols}
    count = len(premises)
    sanitised_premises, sanitised_conclusion = sanitised[:count], sanitised[count]
    sanitised_nonempty = sanitised[count + 1:count + 1 + len(nonempty)]
    sanitised_membership = sanitised[count + 1 + len(nonempty):]

    lines = []
    lines.append("set(prolog_style_variables).")
    lines.append("set(auto_denials).")
    lines.append("clear(print_initial_clauses).")
    lines.append("clear(print_kept).")
    lines.append("clear(print_given).")
    lines.append("")

    lines.append("formulas(assumptions).")
    for premise in sanitised_premises:
        lines.append(f"  {premise.to_prover9()}.")
    # Many-sorted background facts — see the module docstring: non-emptiness of every
    # sort, and the membership S(c) of every sorted constant. Both are built from the
    # ORIGINAL sentences and sanitised with the rest, so the sort predicate and the
    # constant of each fact are the very tokens the premises use.
    for axiom in sanitised_nonempty:
        lines.append(f"  {axiom.to_prover9()}.")
    for fact in sanitised_membership:
        lines.append(f"  {fact.to_prover9()}.")
    lines.append("end_of_list.")
    lines.append("")

    lines.append("formulas(goals).")
    lines.append(f"  {sanitised_conclusion.to_prover9()}.")
    lines.append("end_of_list.")

    return "\n".join(lines), mapping


def _generate_prover9_input(premises: List[Node], conclusion: Node) -> str:
    """
    Generates a Prover9 input string from given premises and conclusion.

    Every predicate/function/constant name is first made Prover9-ASCII-legal
    (see the module docstring's sanitisation section) — a name that was
    already legal renders byte-identically to before that step existed.

    Args:
        premises (list[Node]): List of premise formulas in FOL.
        conclusion (Node): Conclusion formula in FOL.

    Returns:
        str: Formatted Prover9 input string.
    """
    text, _mapping = generate_prover9_input_with_mapping(premises, conclusion)
    return text


#: Prover9's documented exit code for "a fatal error occurred (the user's syntax
#: error, or Prover9's own bug)" -- LADR/Prover9 manual, "Exit codes". The other
#: codes are ordinary ends of a search: 2 the sos list ran empty, 3 max_megs,
#: 4 max_seconds, 5 max_given, 6 max_kept, 7 an action, and 0 a proof.
_PROVER9_FATAL_EXIT = 1

#: The shell's own exit codes for "the command was found but cannot run" (126)
#: and "no such command" (127). Prover9 never exits with them. Behind
#: ``wsl.exe <path> ...`` a path that does not exist inside WSL ends the run this
#: way, with the shell's message and no Prover9 output at all: that is a binary
#: that was never started, not a search that ended without a proof.
_SHELL_NOT_STARTED_EXITS = frozenset({126, 127})


class Prover9Rejected(RuntimeError):
    """Prover9 refused to read the problem (or died) instead of searching.

    Raised by :func:`check_logical_entailment` ONLY when called with
    ``raise_on_rejection=True``; the default keeps the historic contract of
    returning ``False``. ``returncode`` is Prover9's exit code and ``output``
    its own message (stderr, else stdout), so the caller can quote it.
    """

    def __init__(self, returncode: int, output: str):
        super().__init__(f"Prover9 exited with code {returncode}: {output.strip()[:300]}")
        self.returncode = returncode
        self.output = output


class Prover9TimedOut(RuntimeError):
    """The kit stopped Prover9 because its wall-clock budget ran out.

    Raised by :func:`check_logical_entailment` ONLY when called with
    ``raise_on_timeout=True``; the default keeps the historic contract of
    returning ``False``. ``timeout`` is the budget in seconds.
    """

    def __init__(self, timeout: float):
        super().__init__(f"Prover9 was stopped after its {timeout:g}-second budget "
                         "ran out; no proof was found in that time")
        self.timeout = timeout


def _prover9_rejected(returncode: int, stdout: str, stderr: str) -> bool:
    """True iff this exit is a refusal, not the end of a search: Prover9's
    fatal-error exit, or the shell's "cannot run the binary" exit (126, 127)."""
    return (returncode == _PROVER9_FATAL_EXIT or returncode in _SHELL_NOT_STARTED_EXITS
            or "Fatal error" in stdout or "Fatal error" in stderr)


def _prover9_command(prover9_path: str, problem_file: str, use_wsl: bool) -> list:
    """The command line that runs Prover9 on ``problem_file``.

    Natively ``[prover9_path, "-f", problem_file]``. With ``use_wsl`` it is
    ``["wsl.exe", prover9_path, "-f", <wslpath of problem_file>]``: the path of the
    binary is the one INSIDE WSL, and the Windows temp file is translated to its
    ``/mnt/...`` form so that the Linux Prover9 can read it. The translation runs a
    process of its own, and a timeout of THAT process is no Prover9 timeout, so the
    caller builds the command before it opens the Prover9 time window.

    Raises:
        OSError: ``wsl.exe`` cannot be started, does not answer, or cannot translate
            the path; the Prover9 backend reports it as an error verdict.
    """
    if not use_wsl:
        return [prover9_path, "-f", problem_file]
    try:
        wsl_file = _to_wsl_path(problem_file)
    except subprocess.TimeoutExpired:
        raise OSError("wslpath did not answer within its time limit while translating "
                      f"{problem_file!r}; is WSL available?") from None
    except RuntimeError as exc:
        raise OSError(str(exc)) from None
    return ["wsl.exe", prover9_path, "-f", wsl_file]


def _run_prover9(input: str, prover9_path: str, timeout: int = 30,
                 raise_on_rejection: bool = False,
                 raise_on_timeout: bool = False,
                 use_wsl: bool = False) -> bool:
    """Run the prover9 command line tool.

    ``raise_on_rejection=False`` (the default) is the historic contract: any
    run without a ``THEOREM PROVED`` line -- a search that ended without a
    proof, a timeout, AND a problem Prover9 refused to read -- is ``False``.
    With ``True`` the last of those raises :class:`Prover9Rejected` instead, so
    a caller that can report an ERROR does not mistake a refused problem for
    one that was searched and not proved; a binary that could not be started
    (the shell's exit 126 or 127) is such a refusal too. ``raise_on_timeout=True``
    does the same for a run the kit cut off after ``timeout`` seconds: it raises
    :class:`Prover9TimedOut` instead of reporting ``False``.

    ``use_wsl=True`` runs a Linux Prover9 through ``wsl.exe`` (see
    :func:`_prover9_command`). The problem file is written as UTF-8, Prover9 never
    sees the caller's standard input, and its output is decoded as UTF-8 with
    undecodable bytes replaced, because its fatal message can cut a multi-byte
    character of the input in half.
    """

    with tempfile.NamedTemporaryFile(mode='w', suffix='.in', delete=False,
                                     encoding='utf-8', newline='\n') as temp_file:
        temp_file.write(input)
        temp_filename = temp_file.name

    try:
        command = _prover9_command(prover9_path, temp_filename, use_wsl)
        result = subprocess.run(
            command,
            capture_output=True,
            text=True,
            encoding='utf-8',
            errors='replace',
            stdin=subprocess.DEVNULL,
            timeout=timeout
        )
        success = "THEOREM PROVED" in result.stdout
        if (not success and raise_on_rejection
                and _prover9_rejected(result.returncode, result.stdout or "",
                                      result.stderr or "")):
            raise Prover9Rejected(result.returncode,
                                  (result.stderr or "").strip() or (result.stdout or ""))
    except subprocess.TimeoutExpired:
        if raise_on_timeout:
            raise Prover9TimedOut(timeout) from None
        success = False
    finally:
        # Always remove the temp file, even when subprocess.run raises (e.g.
        # FileNotFoundError for a wrong prover9_path); the exception still
        # propagates to the caller.
        try:
            os.unlink(temp_filename)
        except OSError:
            pass

    return success


def check_logical_entailment(premises: list[Node], conclusion: Node, prover9_path: str,
                             raise_on_rejection: bool = False,
                             timeout: int = 30,
                             raise_on_timeout: bool = False,
                             use_wsl: bool = False) -> bool:
    """Checks if a conclusion entails from the defined premises by using prover9.

    ``False`` means "no proof was found" -- including, by default, a problem
    Prover9 refused to read and a run the kit stopped. ``raise_on_rejection=True``
    separates the first: a refused problem (Prover9's fatal-error exit, or a
    binary that could not be started) raises :class:`Prover9Rejected` carrying
    Prover9's own message, which is what
    :class:`~unicode_fol_kit.atp.protocol.Prover9Backend` reports as an ERROR
    verdict instead of an unknown that reads like a timeout.

    ``timeout`` is the wall-clock budget in SECONDS (default 30) the subprocess
    may use; ``raise_on_timeout=True`` separates a run cut off by it by raising
    :class:`Prover9TimedOut`, which the backend reports as UNKNOWN / ``"timeout"``.

    ``use_wsl=True`` runs a Linux Prover9 through ``wsl.exe``; ``prover9_path`` is
    then the path inside WSL (for example
    ``/mnt/d/prover9/Prover9-LADR-2026-8A/bin/prover9``). See :func:`_run_prover9`.
    """

    prover9_input = _generate_prover9_input(premises, conclusion)
    success = _run_prover9(prover9_input, prover9_path, timeout=timeout,
                           raise_on_rejection=raise_on_rejection,
                           raise_on_timeout=raise_on_timeout,
                           use_wsl=use_wsl)
    return success
