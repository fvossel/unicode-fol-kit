"""cvc5 as a second, independent SMT decision procedure for classical FOL.

cvc5 (BSD-3, https://cvc5.github.io) is a full SMT solver with its own
quantifier-instantiation engine (E-matching, enumerative and syntax-guided
instantiation, finite model finding), independent of and often complementary
to Z3's. This module wires it in as a :class:`~unicode_fol_kit.atp.protocol
.ProverBackend` (:class:`Cvc5Backend`, registry name ``"cvc5"``) using
exactly the same classical-FOL fragment Z3 decides in
:class:`unicode_fol_kit.atp.protocol.Z3Backend`: whatever ``Node.to_z3()``
can translate (uninterpreted sort + equality, no arithmetic — see
``fol/_fol_nodes.py``); substructural nodes (linear logic, Lambek calculus)
reject with ``NotImplementedError`` from ``to_z3()`` itself and are reported
UNKNOWN/``"unsupported"`` here, never guessed at.

Translation route — SMT-LIB2 text, not the pythonic term API
--------------------------------------------------------------
cvc5's Python API (1.3.x) builds terms through its own :class:`cvc5.Solver`
/ ``TermManager``, which do not accept Z3 expressions. Re-walking every kit
``Node`` a second time against cvc5's term constructors would duplicate the
entire ``to_z3`` translation and risk it drifting out of sync. Instead this
backend reuses ``to_z3()`` as already trusted by :class:`Z3Backend`, hands
the resulting Z3 expression to a throwaway ``z3.Solver`` for canonical
SMT-LIB2 serialisation (``Solver.to_smt2()`` — sorts, functions and the goal
all print correctly, including quantifiers), and replays that text into
cvc5 via ``cvc5.InputParser``. Each parsed command is invoked on the cvc5
solver immediately (the parser resolves later symbols against earlier
declarations, so streaming invocation is required — buffering all commands
before invoking any breaks the sort/symbol lookups); the ``(check-sat)``
command in the text is skipped and ``Solver.checkSat()`` is called directly
so a genuine :class:`cvc5.Result` (not a string) drives the verdict.

Validity is asked as an UNSAT question, mirroring Z3Backend: ``unsat`` on
``¬((⋀ premises) → φ)`` proves the entailment; ``sat`` produces a genuine
countermodel (a best-effort variable/function assignment read back off the
cvc5 model — one term at a time, so a model cvc5 cannot print for some
symbol does not blank out the whole witness); ``unknown`` is honestly
UNKNOWN, with ``reason="timeout"`` iff cvc5's own explanation says the time
budget (``tlimit-per`` and ``tlimit``, set from the ``timeout`` argument,
milliseconds) was the cause, else ``"incomplete"`` (quantified UF is
undecidable in general; cvc5 gave up without exhausting time or hitting a
bound it can name).

Optional dependency: this backend needs ``pip install cvc5`` (extra
``unicode-fol-kit[cvc5]``). :meth:`Cvc5Backend.available` is pure discovery
(``importlib.util.find_spec``, no import) so probing it never pays the
binding's load cost; ``cvc5`` itself is imported lazily inside ``decide()``.

**ASCII/legality sanitisation (problem-level seam) — narrower than TPTP's.**
``Node.to_z3()`` hands a symbol's name to Z3's Python API completely raw —
no transliteration, no fold — and that is FINE for Z3 itself: a Z3 symbol
name is an arbitrary Python string, not text that has to satisfy any
lexical grammar. The gap this module has is specifically in the SMT-LIB2
TEXT round trip described above (``Solver.to_smt2()`` -> ``InputParser``):
Z3's own ``to_smt2()`` already pipe-quotes (``|...|``) any name that is not
already a legal SMT-LIB2 ``simple_symbol`` — verified live, a non-ASCII
name such as ``świątek`` round-trips through it correctly ALREADY, with no
help from this module — except for the cases :func:`_is_smtlib_safe` lists: a
name that is pure ASCII, made only of ``simple_symbol``-legal characters, but
starts with a DIGIT (``2008SummerOlympics``) or reads as a numeral (``-1``);
a name that IS one of the SMT-LIB2 ``<reserved>`` words the readers treat
specially as syntax (``!``, ``_``, ``as``, ``exists``, ``forall``, ``let``,
``match``, ``par``); a name that begins with ``.`` or ``@`` (reserved for
the solver) or holds ``|``, ``\\`` or ``'`` (which Z3 prints in a form no
reader reads back); a name that is one of the names Z3's printer mints for a
shared sub-term (``$x24``, ``?x10``: :data:`_PRINTER_NAME`), because the
printer writes ``(let (($x24 ...)) ...)`` without looking at the symbols the
text declares and shadows a declared symbol of that spelling inside the ``let``
(the text then says another formula, and cvc5 ends the process on it);
and a name that is a symbol of an SMT-LIB theory
(:data:`_SMTLIB_THEORIES`), which cvc5 already knows with a fixed signature
under the logic ``ALL``. SMT-LIB2 v2.6's grammar (Sec. 3.1) lists five more
words as ``<reserved>`` (``BINARY``, ``DECIMAL``, ``HEXADECIMAL``,
``NUMERAL``, ``STRING``) but neither Z3's parser nor cvc5 special-cases any
of them when they appear as an ordinary declared symbol — verified live, in
every role this module can emit one (bare declaration, applied as a
predicate/function head, used as an argument) — so renaming them would
violate R1 below for no reason. SMT-LIB2's grammar requires a
``simple_symbol`` to start with a non-digit and to not BE a reserved word,
so a digit-leading name needs quoting and so do these, but Z3's serialiser
adds it for none of them — verified live: a function named ``let`` prints as
the undecorated head of ``(let x)``, which its OWN parser then reads as the
``let``-BINDING form, not an application of a symbol named ``let``. Either
way the resulting ``.smt2`` text fails to parse (``z3.parse_smt2_string``
raises; reproduced live for the digit-leading case, and feeding one such name
to this backend segfaults the whole process before :meth:`Cvc5Backend.decide`
ever gets to return an ERROR ``Verdict``, since a native crash is not a Python
exception ``decide()`` can catch). So, unlike :mod:`atp._tptp_problem` and
:mod:`atp.prover9_entailment` (which must fix BOTH non-ASCII and
digit-leading names — Vampire/E/Prover9 have no automatic quoting of their
own), :func:`_sanitize_for_smtlib` only ever touches a name that
:func:`_is_smtlib_safe` refuses; every other name, including every non-ASCII
one, is left completely untouched — touching one would change the export
for a name this backend already handles correctly today, which R1
forbids. The one thing that is renamed although the name is legal is the
SECOND symbol of a name — ``P`` at two arities, a predicate and a function of
one name — because two declarations of one name are an error to SMT-LIB and a
native crash in cvc5 (see :class:`SmtNameMap`), and a constant or a variable whose
name ends in a mark of the Z3 codec (``!v``, ``!c``: see :func:`_is_marked`), because
the reader of the text decodes such a symbol as another one. The sanitised goal's
``sat`` countermodel is translated back via :func:`_reverse_map_assignment` before it
reaches the caller, and the unsat core and the proof text via
:func:`_reverse_map_smtlib_text`, so a caller always sees the ORIGINAL kit-level
symbol name, never the synthesised token.

**One namespace.** In SMT-LIB text a bound variable, a predicate, a function and a
sort are ONE identifier when they are spelled alike, and cvc5 ends the process on
``(exists ((x0 S)) (x0 x0))`` instead of reporting a type error. So no name may be
minted AFTER the sanitiser has chosen its tokens: the counting quantifiers are
expanded and the sort axioms made before it runs (:func:`_lower_counting_for_smtlib`,
:func:`~unicode_fol_kit.fol._msfl_nodes.sort_axioms`), every witness is fresh against
every name of the whole problem, and the sanitiser then keeps every symbol of every
kind apart. The Z3 route needs none of this: its variables are the symbols ``x0!v``,
which no name of a problem is.
"""

import importlib.metadata
import importlib.util
import json
import re
import subprocess
import sys
import time
from dataclasses import dataclass, field, replace
from typing import Callable, Dict, List, Optional, Sequence, Tuple, cast

from ..fol._fol_nodes import numeral_constant_clash, numeral_key
from ..fol._identifiers import symbol_names
from ..fol._msfl_nodes import lower_counting, sort_axioms
from ..fol._tptp_symbols import is_tptp_boolean_atom as _is_tptp_boolean_atom
from ..fol.nodes import (
    Atom, Constant, Count, Function, Measure, Node, Number, Variable, And, Implies,
    SortedCardinality, SortedConstant, SortedCount, SortedQuantifier, Z3Env,
)
from ._ascii_names import ascii_safe_base, reserve_rendered
from .protocol import ProverBackend, Verdict, PROVED, REFUTED, UNKNOWN, ERROR
from .z3_models import declaration_keys, separate_variables

__all__ = ["Cvc5Backend"]


# ---------------------------------------------------------------------------
# ASCII/legality sanitisation — see the module docstring's sanitisation
# section for why this is narrower than atp._tptp_problem's / atp
# .prover9_entailment's (only digit-leading pure-ASCII names and SMT-LIB2's
# own reserved words are unsafe here; everything else, including every
# non-ASCII name, already round-trips correctly through Z3's own SMT-LIB2
# serialisation).
# ---------------------------------------------------------------------------

#: The EIGHT SMT-LIB2 <reserved> words that cannot be a declared name. Seven of
#: the thirteen the v2.6 grammar's Sec. 3.1 lists (``!``, ``_``, ``as``,
#: ``exists``, ``forall``, ``let``, ``match``) Z3's OWN parser treats as syntax
#: rather than an ordinary <symbol> — none of these is a legal plain <symbol>
#: when used as a declared name, even though nothing else about the string
#: looks illegal (no digit, no non-ASCII character, no special character Z3
#: would quote). Z3's own ``to_smt2()`` does not quote any of them either
#: (verified live: a function declared under the name ``let`` prints as the
#: undecorated head of ``(let x)``, which its own parser then reads as the
#: ``let``-BINDING form, not a call to a symbol named ``let``) — see the
#: module docstring. The eighth is ``par``, which Z3 round-trips but cvc5 reads
#: as the keyword of a parametric declaration: a constant or a function named
#: ``par`` ends the Python process with a native access violation (measured on
#: cvc5 1.3.4, in a child process). The other five <reserved> words
#: (``BINARY``, ``DECIMAL``, ``HEXADECIMAL``, ``NUMERAL``, ``STRING``) are
#: DELIBERATELY excluded: verified live that both Z3's parser and cvc5 accept
#: every one of them as a bare declaration, as an applied predicate/function
#: head, and as an argument — renaming them would be an unforced, undocumented
#: rename of a name this backend already handles correctly, which R1 (see the
#: module docstring) forbids.
_SMTLIB_RESERVED_WORDS = frozenset({
    "!", "_", "as", "exists", "forall", "let", "match", "par",
})

#: The function symbols of SMT-LIB's Core theory, which every logic has. This
#: kit reads a predicate or function of one of these names as an ordinary
#: UNINTERPRETED symbol over its one sort (that is what ``to_z3`` declares, and
#: Z3 accepts the declaration), but cvc5 already knows the name with a fixed
#: signature: a ``declare-fun`` of ``distinct`` / ``=>`` / ``xor`` is a parse
#: error, and one of ``not`` / ``and`` / ``or`` / ``ite`` / ``true`` / ``false``
#: ends the Python process with a native access violation (measured on cvc5
#: 1.3.4, each in a child process). So they are renamed like a reserved word.
#: ``=`` is in :data:`_SMTLIB_THEORIES` below but not here: ``Atom.to_z3`` maps
#: a binary ``=`` / ``≠`` atom to the native equality, so that one is never
#: declared; a CONSTANT or FUNCTION named ``=`` is, and is renamed.
_SMTLIB_CORE_SYMBOLS = frozenset({
    "true", "false", "not", "and", "or", "xor", "=>", "distinct", "ite",
})

#: The symbols the standard SMT-LIB theories declare, by theory (every symbol of
#: Core, Ints, Reals, Reals_Ints, ArraysEx, FixedSizeBitVectors, FloatingPoint
#: and Strings, sort names included), and then the further names cvc5 knows (the
#: groups that begin with ``cvc5``: every name that a measurement on cvc5 1.3.4
#: showed to be known, found by trying the candidates in a child process).
#:
#: This kit reads a predicate, a function or a constant of one of these names as
#: an ordinary UNINTERPRETED symbol over its one sort (that is what ``to_z3``
#: declares, and Z3 accepts every one of them), but under the logic ``ALL`` — and
#: for some of them under ``UF`` too — cvc5 already knows the name with a fixed
#: signature: ``declare-fun`` of it is a parse error or, for a function or a
#: constant, a native access violation that ends the Python process. A kit symbol
#: named like any of them is renamed under EVERY logic, so a caller's ``logic=``
#: never decides whether a name crashes. A name of the standard theories that cvc5
#: does not know (``Float16``, ``re.loop``) is renamed for nothing, which costs
#: nothing; a symbol that a later cvc5 adds is a name this table has to learn
#: (``tests/test_cvc5_theory_symbols.py`` runs every name of it through cvc5 under
#: ``ALL``, in a child process).
_SMTLIB_THEORIES: Dict[str, Tuple[str, ...]] = {
    "Core": ("Bool", "true", "false", "not", "=>", "and", "or", "xor", "=", "distinct", "ite"),
    "Ints": ("Int", "-", "+", "*", "div", "mod", "abs", "<=", "<", ">=", ">", "divisible"),
    "Reals": ("Real", "-", "+", "*", "/", "<=", "<", ">=", ">"),
    "Reals_Ints": ("to_real", "to_int", "is_int"),
    "ArraysEx": ("Array", "select", "store"),
    "FixedSizeBitVectors": (
        "BitVec", "concat", "extract", "bvnot", "bvneg", "bvand", "bvor", "bvxor", "bvnand",
        "bvnor", "bvxnor", "bvcomp", "bvadd", "bvsub", "bvmul", "bvudiv", "bvurem", "bvsdiv",
        "bvsrem", "bvsmod", "bvshl", "bvlshr", "bvashr", "bvult", "bvule", "bvugt", "bvuge",
        "bvslt", "bvsle", "bvsgt", "bvsge", "repeat", "zero_extend", "sign_extend",
        "rotate_left", "rotate_right", "bv2nat", "nat2bv", "int2bv", "ubv_to_int", "sbv_to_int",
        "int_to_bv", "bvnego", "bvuaddo", "bvsaddo", "bvumulo", "bvsmulo", "bvusubo", "bvssubo",
        "bvsdivo", "bvultbv", "bvsltbv", "bvite", "bvredor", "bvredand"),
    "FloatingPoint": (
        "Float16", "Float32", "Float64", "Float128", "FloatingPoint", "RoundingMode", "RNE",
        "RNA", "RTP", "RTN", "RTZ", "roundNearestTiesToEven", "roundNearestTiesToAway",
        "roundTowardPositive", "roundTowardNegative", "roundTowardZero", "fp", "fp.abs",
        "fp.neg", "fp.add", "fp.sub", "fp.mul", "fp.div", "fp.fma", "fp.sqrt", "fp.rem",
        "fp.roundToIntegral", "fp.min", "fp.max", "fp.leq", "fp.lt", "fp.geq", "fp.gt", "fp.eq",
        "fp.isNormal", "fp.isSubnormal", "fp.isZero", "fp.isInfinite", "fp.isNaN",
        "fp.isNegative", "fp.isPositive", "to_fp", "to_fp_unsigned", "fp.to_ubv", "fp.to_sbv",
        "fp.to_real", "+oo", "-oo", "+zero", "-zero", "NaN"),
    "Strings": (
        "String", "RegLan", "str.++", "str.len", "str.<", "str.<=", "str.at", "str.substr",
        "str.prefixof", "str.suffixof", "str.contains", "str.indexof", "str.replace",
        "str.replace_all", "str.replace_re", "str.replace_re_all", "str.is_digit",
        "str.to_code", "str.from_code", "str.to_int", "str.from_int", "str.in_re", "str.to_re",
        "re.none", "re.all", "re.allchar", "re.++", "re.union", "re.inter", "re.*", "re.+",
        "re.opt", "re.range", "re.comp", "re.diff", "re.loop", "re.^", "str.in.re", "str.to.re",
        "int.to.str", "str.to.int", "re.nostr", "str.lt", "str.leq"),
    "cvc5 strings": ("str.rev", "str.to_lower", "str.to_upper", "str.update", "str.indexof_re"),
    "cvc5 arithmetic": (
        "sin", "cos", "tan", "csc", "sec", "cot", "arcsin", "arccos", "arctan", "arccsc",
        "arcsec", "arccot", "exp", "sqrt", "real.pi", "int.pow2", "int.log2", "^", "/_total",
        "div_total", "mod_total", "piand"),
    "cvc5 arrays": ("eqrange",),
    "cvc5 sets and relations": (
        "set.empty", "set.universe", "set.singleton", "set.union", "set.inter", "set.minus",
        "set.subset", "set.member", "set.card", "set.insert", "set.complement", "set.choose",
        "set.is_singleton", "set.is_empty", "set.map", "set.filter", "set.all", "set.some",
        "set.fold", "set.comprehension", "rel.transpose", "rel.product", "rel.join",
        "rel.tclosure", "rel.iden", "rel.group", "rel.aggr", "rel.project", "rel.table_join",
        "rel.join_image"),
    "cvc5 bags and tables": (
        "bag", "bag.empty", "bag.union_max", "bag.union_disjoint", "bag.inter_min",
        "bag.difference_subtract", "bag.difference_remove", "bag.subbag", "bag.count",
        "bag.member", "bag.setof", "bag.card", "bag.choose", "bag.map", "bag.filter",
        "bag.all", "bag.some", "bag.fold", "bag.partition", "table.product", "table.project",
        "table.join", "table.group", "table.aggr"),
    "cvc5 sequences": (
        "seq.empty", "seq.unit", "seq.nth", "seq.len", "seq.++", "seq.update", "seq.at",
        "seq.extract", "seq.contains", "seq.indexof", "seq.replace", "seq.replace_all",
        "seq.rev", "seq.prefixof", "seq.suffixof"),
    "cvc5 tuples, nullables, finite fields, separation logic": (
        "tuple", "tuple.project", "tuple.unit", "nullable.some", "nullable.val",
        "nullable.is_null", "nullable.is_some", "nullable.null", "nullable.lift", "ff.add",
        "ff.mul", "ff.neg", "ff.bitsum", "sep", "pto", "wand", "sep.nil", "sep.emp"),
}

#: Every name of :data:`_SMTLIB_THEORIES`, flat.
_SMTLIB_THEORY_SYMBOLS = frozenset(
    name for names in _SMTLIB_THEORIES.values() for name in names)


#: The names Z3's SMT-LIB printer mints for the shared sub-terms of a formula: it writes
#: ``(let (($x24 (R c d))) ...)`` for a Boolean term and ``(let ((?x10 (g c))) ...)`` for any
#: other, the sign ``$`` or ``?``, the letter ``x`` and the number of the term in its own table
#: (measured over several hundred printed problems: no other name opens a ``let``). It does not
#: look at the symbols the text declares, so a declared symbol or a bound variable spelled alike
#: would be shadowed inside that ``let`` (the text then says another formula, or is ill-sorted, and
#: cvc5 ends its process on it). No symbol of a problem is spelled so (:func:`_is_smtlib_safe`),
#: and no token the sanitiser makes is: a token is a stem that :func:`_is_smtlib_safe` lets
#: through, or such a stem with a number appended
#: (:func:`~unicode_fol_kit.atp._ascii_names.reserve_rendered`), and a number turns into a printer
#: name only the stems ``$x`` and ``?x``. A symbol of that name is kept as it is (it is no printer
#: name) and every later symbol of the name gets the stem ``$x_<arity>``, so no renamed symbol has one
#: of them as its stem.
_PRINTER_NAME = re.compile(r"[$?]x[0-9]+")


def _is_smtlib_safe(name: str) -> bool:
    """Can a declared symbol of this name be handed to cvc5 as it is?

    Not when it is empty; not when it is one of the <reserved> words or the name
    of a symbol of an SMT-LIB theory (:data:`_SMTLIB_THEORY_SYMBOLS`); not when
    it begins with a digit (ASCII), with ``.`` or ``@`` (reserved for the solver
    in SMT-LIB), or with a minus sign and a digit (``-1``, which cvc5 reads as a
    numeral); not when it holds ``|``, ``\\`` or ``'``, which Z3 prints in a
    form no SMT-LIB reader reads back as the same symbol; not when it is a name
    Z3's printer gives a shared sub-term (``$x24``, ``?x10``: :data:`_PRINTER_NAME`).
    Every other name — a non-ASCII one, one with a space or a quote that Z3
    pipe-quotes correctly — is left as it is.
    """
    if not name:
        return False
    if (name in _SMTLIB_RESERVED_WORDS or name in _SMTLIB_CORE_SYMBOLS
            or name in _SMTLIB_THEORY_SYMBOLS):
        return False
    if name.isascii() and name[0].isdigit():
        return False
    if name[0] in ".@" or (name[0] == "-" and name[1:2].isdigit()):
        return False
    if _PRINTER_NAME.fullmatch(name):
        return False
    return not any(ch in name for ch in "|\\'")


_PLAIN_NUMERAL = re.compile(r"[0-9]+|[0-9]+(?:\.[0-9]+)?[eE][+-]?[0-9]+")


def _is_plain_numeral(text: str) -> bool:
    """Is the text of a numeral one that cvc5 takes as the symbol Z3 prints?

    Digits only (``12``), or digits with an exponent (``1e-07``, ``1.5e+16``,
    which is how Python writes a very small or a very large float). A decimal
    (``2.5``) or a negative number (``-1``) is not: cvc5 ends its process on a
    declaration of a symbol of that text, so such a numeral is renamed like any
    other digit-leading name.
    """
    return _PLAIN_NUMERAL.fullmatch(text) is not None


def _unquote_smtlib(s: str) -> str:
    """Strip an SMT-LIB2 ``|...|`` quoted-symbol wrapper, if present.

    A quoted symbol has no escape mechanism (the only characters forbidden
    INSIDE one are ``|`` and ``\\``, per the SMT-LIB2 spec), so stripping the
    outer pair is a lossless, exact inverse of the quoting Z3's ``to_smt2()``
    already applies to any name it did not consider a plain ``simple_symbol``
    (see the module docstring) — no unescaping needed, unlike a string
    literal.
    """
    if len(s) >= 2 and s[0] == "|" and s[-1] == "|":
        return s[1:-1]
    return s


#: The kinds of declared symbol. A constant is a function of no arguments; a
#: proposition (a predicate of no arguments) is a predicate; a variable is a symbol
#: of its own, apart from a constant of the same name.
_PREDICATE, _FUNCTION, _VARIABLE = "predicate", "function", "variable"


#: What the names of the constants and the variables that Z3 reads back end in (see
#: :func:`~unicode_fol_kit.fol._fol_nodes.kit_name_of_z3_symbol`): ``x!v`` is read as the
#: variable ``x``. No symbol of the text this module writes ends in one, so that the text
#: is read as the symbols it declares.
_Z3_SYMBOL_MARKS = ("!v", "!c")


def _is_marked(name: str, kind: str, arity: int) -> bool:
    """Is a symbol of this kind and name one that a reader of the text would decode?

    Only a nullary symbol of the one sort is (a constant, a function of no arguments, a
    variable), and only when its name ends in a mark of the Z3 codec (:data:`_Z3_SYMBOL_MARKS`).
    Such a symbol is renamed like an illegal name, and every token is made to end in
    neither mark, so that no declared symbol is read as another (``a!c`` as ``a``, a constant
    ``a!v`` as the variable ``a``) and none is spelled like what the environment writes for
    another (a constant ``a!v`` is the symbol ``a!v!c`` of Z3, the very name of a predicate
    that is called so).
    """
    return arity == 0 and kind in (_FUNCTION, _VARIABLE) and name.endswith(_Z3_SYMBOL_MARKS)


def _smtlib_token_base(name: str) -> str:
    """The stem of the token a symbol of ``name`` is renamed to.

    ASCII (non-ASCII characters are spelled as
    :func:`~atp._ascii_names.ascii_safe_base` does), with ``|``, ``\\`` and ``'``
    — which no SMT-LIB reader reads back as part of a symbol — spelled as
    ``uXXXX`` escapes too, and prefixed with ``n`` for as long as the result is
    still not a name :func:`_is_smtlib_safe` lets through (a reserved word, a
    theory symbol, a digit, ``.`` or ``@`` first, a minus and a digit, a name of
    Z3's printer). A stem that
    ends in a mark of the Z3 codec (:data:`_Z3_SYMBOL_MARKS`) gets an underscore
    appended, so that no token ends in one.
    """
    base = "".join(f"u{ord(ch):04x}" if ch in "|\\'" else ch
                   for ch in ascii_safe_base(name, "n"))
    while not _is_smtlib_safe(base):
        base = "n" + base
    while base.endswith(_Z3_SYMBOL_MARKS):
        base += "_"
    return base


@dataclass
class SmtNameMap:
    """The renamings :func:`_sanitize_many_for_smtlib` chose for one problem.

    **What is one symbol.** A symbol is ``(kind, name, arity)``: a predicate, a
    function (a constant is a function of no arguments) or a variable, its name,
    its number of arguments. The same name at two arities, as a predicate and as a
    function or constant, as a variable and as a constant, is two symbols —
    ``to_z3`` declares two, and so does every SMT-LIB text of them, where two
    declarations of one name are an error (cvc5 ends the Python process on it). The
    FIRST symbol of a name, in the order the problem presents them, keeps the name
    when the name is legal; every later symbol of that name gets a token of its
    own (``P_2``, ``a_0``), as does a symbol whose name is not legal. So a variable
    ``x`` and a constant ``x`` are written under two different tokens, and the
    quantifier of the one binds nothing of the other.

    A constant, a function of no arguments or a variable whose name ends in ``!v`` or
    ``!c`` is renamed too, and no token ends in either (:func:`_is_marked`): the
    reader of the text (:func:`~unicode_fol_kit.atp.z3_input.from_z3`) decodes such a
    symbol as a variable, or as another constant, so it never has to be one.

    ``mapping`` is the name → token table of the first symbol of each name,
    ``symbols`` the table of every symbol. A numeral is the symbol of the text of
    its value (:func:`~unicode_fol_kit.fol._fol_nodes.numeral_key`: ``Number(1)``
    and ``Number(1.0)`` are the constant ``1``): a numeral and a constant of one
    text are refused, as ``Z3Env`` refuses them.

    Built from the same :func:`~atp._ascii_names.ascii_safe_base` /
    :func:`~atp._ascii_names.reserve_rendered` primitives
    :mod:`atp._tptp_problem` and :mod:`atp.prover9_entailment` use, with
    SMT-LIB2's own legality test (:func:`_is_smtlib_safe`) and no render/fold
    step (SMT-LIB2 text is never case-folded, so the rendered form IS the raw
    token).
    """

    mapping: Dict[str, str] = field(default_factory=dict)
    used: set = field(default_factory=set)
    symbols: Dict[Tuple[str, str, int], str] = field(default_factory=dict)
    _pending: list = field(default_factory=list)
    _first: Dict[str, Tuple[str, str, int]] = field(default_factory=dict)
    _numerals: set = field(default_factory=set)
    _constants: set = field(default_factory=set)

    def collect(self, name: str, kind: str = _FUNCTION, arity: int = 0,
                numeral: bool = False) -> None:
        """First pass: register the symbol ``(kind, name, arity)``; an
        already-legal name of the first symbol of that name is reserved
        immediately (order-independent — see
        :class:`~atp._tptp_problem._Renamer`'s docstring for why collision
        avoidance for a synthesised name must not depend on processing
        order relative to an unrelated already-legal name).

        Raises:
            NotImplementedError: a numeral and a constant of the same text, which
                are one symbol (a variable of that text is another symbol).
        """
        if kind == _FUNCTION and arity == 0:
            (self._numerals if numeral else self._constants).add(name)
            if name in self._numerals and name in self._constants:
                numeral_constant_clash(name)
        key = (kind, name, arity)
        if key in self.symbols or key in self._pending:
            return
        if name not in self._first:
            self._first[name] = key
            # A numeral of plain digits (``1``) or of exponent form (``1e-07``,
            # ``1.5e+16``) is the one digit-leading name left as it is: Z3
            # pipe-quotes it correctly (``|1|``) and reads it back as the number.
            # The other numerals (``2.5``, ``-1``) are quoted in a form cvc5 reads
            # as a literal, and are renamed.
            if ((_is_smtlib_safe(name) and not _is_marked(name, kind, arity))
                    or (numeral and _is_plain_numeral(name))):
                self.used.add(name)
                self.mapping[name] = name
                self.symbols[key] = name
                return
        self._pending.append(key)

    def finalize(self) -> None:
        """Second pass: synthesise a token for every queued symbol — the
        symbols of an illegal name and every symbol after the first of one
        name — now that every already-legal name in the problem is reserved.

        :func:`~atp._ascii_names.ascii_safe_base` only prepends its prefix
        when the transliterated result is EMPTY or DIGIT-leading — a
        reserved word such as ``let`` is neither (it is already a plain
        ASCII, non-digit-leading string), so it comes back unchanged and
        would be reserved verbatim, defeating the whole point of queuing it.
        :func:`_smtlib_token_base` catches exactly that residual case. A
        symbol after the first of its name carries its arity in the token
        (``P_2``), so the tokens of one name read apart.
        """
        for key in self._pending:
            _, name, arity = key
            base = _smtlib_token_base(name)
            if self._first[name] == key:
                token = reserve_rendered(base, self.used)
                self.mapping[name] = token
            else:
                token = reserve_rendered(_smtlib_token_base(f"{base}_{arity}"), self.used)
            self.symbols[key] = token
        self._pending = []

    def get(self, name: str) -> str:
        """The token of the first symbol of ``name``."""
        return self.mapping[name]

    def symbol(self, kind: str, name: str, arity: int) -> str:
        """The token of the symbol ``(kind, name, arity)``."""
        return self.symbols[(kind, name, arity)]

    def reverse(self) -> Dict[str, str]:
        """Token → original name, for every symbol (a legal name maps to itself)."""
        return {token: key[1] for key, token in self.symbols.items()}

    def variable_tokens(self) -> frozenset:
        """The tokens that stand for a variable (not for a constant or a predicate)."""
        return frozenset(token for (kind, _, _), token in self.symbols.items() if kind == _VARIABLE)


#: The many-sorted nodes that bind a variable over a sort; each carries the sort
#: NAME in a ``sort`` field, and that name becomes the guard predicate of the
#: sort (the sort and the unary predicate of that name are one symbol).
_SORT_BINDERS = (SortedQuantifier, SortedCount, SortedCardinality)

#: The counting quantifiers. Their bound ``n`` is a :class:`~fol.nodes.Number`
#: that is a PARAMETER of the node (and must stay one: the node refuses anything
#: else), not a numeral that names a symbol; ``to_z3`` expands the quantifier to
#: distinct witnesses, in which no symbol of that text appears.
_COUNTING = (Count, SortedCount)


def _renamed_children(node: Node) -> List[Node]:
    """The children of ``node`` that name a symbol: every child, except the bound of a counting
    quantifier (a parameter of the node, no numeral of the problem)."""
    return [node.variable, node.formula] if isinstance(node, _COUNTING) else node._child_nodes()


def _symbol_nodes(node: Node):
    """Yield ``node`` and every descendant that can name a symbol, in pre-order:
    :meth:`~fol.nodes.Node.walk` without the bound of a counting quantifier.

    The walk keeps its own stack: the expansion of a counting quantifier (``∃≥500 x P(x)``) is
    five hundred quantifiers deep, and a walk that recurses on it runs out of the interpreter's
    recursion limit.
    """
    stack = [node]
    while stack:
        current = stack.pop()
        yield current
        stack.extend(reversed(_renamed_children(current)))


def _declares_no_symbol(atom: Atom) -> bool:
    """Is ``atom`` read by ``to_z3`` as something that declares no predicate?

    A BINARY ``=`` / ``≠`` is Z3's native (dis)equality, and ``$true`` /
    ``$false`` are the constants true and false; neither names a symbol. An
    ``=`` of three arguments is an ordinary uninterpreted predicate of that name.
    """
    if atom.predicate in ("=", "≠") and len(atom.args) == 2:
        return True
    return _is_tptp_boolean_atom(atom)


def _sanitize_node_for_smtlib(node: Node, names: SmtNameMap) -> Node:
    """Rebuild ``node`` with every illegal or shared symbol name replaced.

    Mirrors :func:`atp._tptp_problem._sanitize_node_for_tptp`'s structural
    recursion; a binary ``=``/``≠`` is excluded from renaming because
    :meth:`~fol.nodes.Atom.to_z3` maps it to Z3's native equality
    operators rather than an uninterpreted predicate — it is never an
    identifier to begin with.

    Every symbol is looked up by ``(kind, name, arity)`` (see
    :class:`SmtNameMap`): ``P(a)`` and ``P(a, b)`` get two tokens, a predicate
    and a function of one name two, a proposition and a constant two, a variable
    and a constant two. A numeral is rewritten to the constant of the token of its
    value's text, and a variable to the variable of its own token, so a variable named
    like a theory symbol (``select``) is renamed too.

    The many-sorted nodes are rewritten too, because ``to_z3()`` reduces them
    to plain symbols of the SAME names: a :class:`~fol.nodes.SortedConstant`
    ``c:S`` renders as the plain constant ``c`` (so it takes the token of a
    plain ``c`` anywhere else in the problem) and its sort ``S`` is the guard
    predicate ``S``, a unary predicate; a sorted quantifier, counting quantifier
    or cardinality names its sort the same way. A sort name that is not a legal
    SMT-LIB2 symbol (``2S``) would otherwise reach cvc5 unrenamed and end the
    process. A :class:`~fol.nodes.Measure` is the function ``measure`` of two
    arguments and is rewritten to it.

    The rewriting keeps its own stack (a node is rewritten after its children, once per node
    object), so a formula nested deeper than the interpreter's recursion limit is rewritten as
    readily as a shallow one: the expansion of a counting quantifier of bound 500 is five hundred
    quantifiers deep.
    """
    rewritten: Dict[int, Node] = {}

    def rebuilt(child: Node) -> Node:
        return rewritten[id(child)]

    stack: List[Tuple[Node, bool]] = [(node, False)]
    while stack:
        current, children_done = stack.pop()
        if id(current) in rewritten:
            continue
        children = _renamed_children(current)
        if children and not children_done:
            stack.append((current, True))
            stack.extend((child, False) for child in children)
            continue
        rewritten[id(current)] = _sanitize_one_node(current, names, rebuilt)
    return rewritten[id(node)]


def _sanitize_one_node(node: Node, names: SmtNameMap, recurse: Callable[[Node], Node]) -> Node:
    """:func:`_sanitize_node_for_smtlib` for ONE node, whose children are already rewritten:
    ``recurse(child)`` is the rewriting of a child."""
    if isinstance(node, Atom):
        if _declares_no_symbol(node):
            pred = node.predicate
        else:
            pred = names.symbol(_PREDICATE, node.predicate, len(node.args))
        return Atom(pred, tuple(recurse(a) for a in node.args))
    if isinstance(node, Function):
        return Function(names.symbol(_FUNCTION, node.name, len(node.args)),
                        tuple(recurse(a) for a in node.args))
    if isinstance(node, Constant):
        return Constant(names.symbol(_FUNCTION, node.name, 0))
    if isinstance(node, Variable):
        return Variable(names.symbol(_VARIABLE, node.name, 0))
    if isinstance(node, Number):
        return Constant(names.symbol(_FUNCTION, numeral_key(node.value), 0))
    if isinstance(node, Measure):
        return Function(names.symbol(_FUNCTION, "measure", 2),
                        (recurse(node.entity), recurse(node.dimension)))
    if isinstance(node, SortedConstant):
        return SortedConstant(names.symbol(_FUNCTION, node.name, 0),
                              names.symbol(_PREDICATE, node.sort, 1))
    if isinstance(node, Count):
        return replace(node, variable=cast(Variable, recurse(node.variable)),
                       formula=recurse(node.formula))
    if isinstance(node, SortedCount):
        return replace(node, variable=cast(Variable, recurse(node.variable)),
                       sort=names.symbol(_PREDICATE, node.sort, 1), formula=recurse(node.formula))
    if isinstance(node, _SORT_BINDERS):
        body = node.map_children(recurse)
        return replace(body, sort=names.symbol(_PREDICATE, node.sort, 1))
    return node.map_children(recurse)


def _collect_names_for_smtlib(node: Node, names: SmtNameMap) -> None:
    """First pass (see :meth:`SmtNameMap.collect`): register every
    symbol ``node`` uses, without rewriting anything yet: a predicate or a
    function at its arity, a constant, a variable (a symbol of its own), a numeral
    (the symbol of its value's text), the ``measure`` function a :class:`~fol.nodes.Measure`
    stands for. A sorted constant registers its constant name and its sort as a
    unary predicate (a sorted constant and a plain constant of one name are one
    symbol), and a sorted binder registers its sort. The bound of a counting
    quantifier is no numeral of the problem and is passed over
    (:func:`_symbol_nodes`)."""
    for n in _symbol_nodes(node):
        if isinstance(n, Atom):
            if not _declares_no_symbol(n):
                names.collect(n.predicate, _PREDICATE, len(n.args))
        elif isinstance(n, Function):
            names.collect(n.name, _FUNCTION, len(n.args))
        elif isinstance(n, Constant):
            names.collect(n.name, _FUNCTION, 0)
        elif isinstance(n, Variable):
            names.collect(n.name, _VARIABLE, 0)
        elif isinstance(n, Number):
            names.collect(numeral_key(n.value), _FUNCTION, 0, numeral=True)
        elif isinstance(n, Measure):
            names.collect("measure", _FUNCTION, 2)
        elif isinstance(n, SortedConstant):
            names.collect(n.name, _FUNCTION, 0)
            names.collect(n.sort, _PREDICATE, 1)
        elif isinstance(n, _SORT_BINDERS):
            names.collect(n.sort, _PREDICATE, 1)


def _sanitize_for_smtlib(node: Node) -> Tuple[Node, SmtNameMap]:
    """Sanitise ``node`` (the already-folded ``(∧ premises) → φ`` goal) for
    the SMT-LIB2 round trip. Returns ``(sanitised_node, mapping)`` — the
    two-pass collect-then-finalize split (see :class:`SmtNameMap`, mirroring
    :class:`atp._tptp_problem._Renamer`) means a synthesised digit-safe
    token can never collide with an already-legal name anywhere in
    ``node``, regardless of which one this walk reaches first.

    Single-node case, kept for the digit-leading/R1/R2/R5 regression tests
    that exercise it directly; :meth:`Cvc5Backend.decide` itself uses
    :func:`_sanitize_many_for_smtlib` (below) so premises stay SEPARATE
    SMT-LIB2 assertions rather than one folded implication — see that
    function's docstring for why.
    """
    names = SmtNameMap()
    _collect_names_for_smtlib(node, names)
    names.finalize()
    return _sanitize_node_for_smtlib(node, names), names


def _sanitize_many_for_smtlib(nodes: Sequence[Node]) -> Tuple[List[Node], SmtNameMap]:
    """Sanitise several nodes (this backend's premises, then the goal, in
    that order) against ONE SHARED name map, so a symbol used across
    several of them renames consistently — the same two-pass
    collect-then-finalize discipline as :func:`_sanitize_for_smtlib`
    (:class:`SmtNameMap`), just collected across the WHOLE list before any
    renaming is finalised, rather than over one already-folded node.

    :meth:`Cvc5Backend.decide` asserts each returned node as its OWN
    ``(assert ...)`` SMT-LIB2 command (see :meth:`Cvc5Backend._run`) instead
    of folding ``premises`` into one ``(∧ premises) → φ`` implication first
    (:func:`_implication` — still used by :func:`_sanitize_for_smtlib`'s own
    regression tests, unrelated to this path): cvc5's ``getUnsatCore()``
    reports relevance at the granularity of INDIVIDUAL top-level assertions,
    so a single folded assertion would always report as "the whole thing",
    a technically sound but useless certificate — the exact failure mode
    this module's own C12 test suite checks for. Logically this changes
    nothing (SMT solvers conjoin every assertion regardless of how many
    ``(assert ...)`` commands they arrived in), only the unsat-core
    bookkeeping's resolution.
    """
    names = SmtNameMap()
    for node in nodes:
        _collect_names_for_smtlib(node, names)
    names.finalize()
    return [_sanitize_node_for_smtlib(node, names) for node in nodes], names


#: The characters an SMT-LIB simple symbol is made of (SMT-LIB 2.6, section 3.1), besides letters and
#: digits. A token in a solver's text ends where the next character is none of them.
_SMTLIB_SYMBOL_CHARS = "~!@$%^&*_-+=<>.?/"


def _reverse_map_smtlib_text(text: str, reverse: Dict[str, str]) -> str:
    """Write the caller's names into ``text`` that a solver printed (a core term, a proof).

    Replaces every occurrence of a token of ``reverse`` (token → original name) that is a whole
    SMT-LIB symbol: not preceded and not followed by a character a simple symbol is made of
    (:data:`_SMTLIB_SYMBOL_CHARS`, letters and digits). A word boundary is not that test: a
    token such as ``n<`` or ``n+`` (the renaming of the theory symbols ``<`` and ``+``)
    ends in a character that is no word character, so there is no boundary after it and a
    ``\\b`` pattern never found it. The longest token is tried first, so a token that begins another is
    not matched short. A name that was left as it is needs no rewriting.

    A quoted symbol (``|is n<|``) is ONE symbol, whatever characters it holds: a token inside it is
    part of that other name and is left alone. A quoted symbol that is a token as a whole
    (``|n<|``, the same symbol as ``n<``) is rewritten as a whole, and stays quoted. A string literal
    and a comment are skipped the same way, so a ``|`` in one of them opens no quoted symbol.
    """
    tokens = {token: original for token, original in reverse.items() if token != original}
    if not tokens or not text:
        return text
    chars = "A-Za-z0-9" + "".join(re.escape(ch) for ch in _SMTLIB_SYMBOL_CHARS)
    pattern = re.compile(
        r"(?P<quoted>\|[^|\\]*\|)|(?P<string>\"(?:[^\"]|\"\")*\")|(?P<comment>;[^\n]*)"
        f"|(?<![{chars}])(?P<token>" + "|".join(re.escape(token) for token in sorted(tokens, key=len, reverse=True))
        + f")(?![{chars}])")

    def rewritten(match) -> str:
        token = match.group("token")
        if token is not None:
            return tokens[token]
        quoted = match.group("quoted")
        if quoted is not None and quoted[1:-1] in tokens:
            original = tokens[quoted[1:-1]]
            # a name that holds ``|`` or a backslash cannot be written inside a quoted symbol
            return original if any(ch in original for ch in "|\\") else f"|{original}|"
        return match.group(0)

    return pattern.sub(rewritten, text)


def _lower_counting_for_smtlib(nodes: Sequence[Node]) -> Tuple[List[Node], set]:
    """Lower every counting quantifier of ``nodes``, before the names of the problem are renamed.

    The text of this module has ONE namespace: a bound variable, a predicate, a function and a
    sort are one identifier when they are spelled alike (``(exists ((x0 S)) (x0 x0))``, which
    cvc5 turns into a native crash). A counting quantifier is expanded into witnesses that the
    translation to Z3 mints, after the sanitiser has chosen its tokens, so such a witness
    was no symbol the sanitiser had seen. So the counting quantifiers are expanded first, by
    :func:`~unicode_fol_kit.fol._msfl_nodes.lower_counting`, with every name of the whole
    problem to avoid; the witnesses are then variables of the problem, which the sanitiser
    keeps apart from every other symbol like any variable.

    Returns the lowered nodes and the set of every name of the problem, the witnesses
    included, for the caller to avoid in what else it mints (the sort axioms).
    """
    avoid = set(symbol_names(*nodes))
    return [lower_counting(node, avoid) for node in nodes], avoid


def _reverse_map_assignment(entries: Sequence[Tuple[str, int, str, str]],
                            reverse: Dict[str, str],
                            variables: frozenset = frozenset()) -> Dict[str, str]:
    """Translate a cvc5 ``sat`` model, one ``(declared_term_str, arity,
    range, value_str)`` entry per declaration, back to original kit-level names
    in ``{key: value}`` form.

    Every name AND value is first unquoted (:func:`_unquote_smtlib`) — cvc5's
    ``str(term)``/``str(value)`` reproduce whatever quoting the term's own
    declaration used, so a non-ASCII name that Z3 pipe-quoted on export (see
    the module docstring — already correct, never renamed by
    :func:`_sanitize_for_smtlib`) would otherwise reach the caller as
    ``"|świątek|"`` rather than the true original ``"świątek"``. After
    unquoting, a name found in ``reverse`` (a name this module DID rename) is
    translated back to its original; anything else — cvc5's own fresh
    model-value tokens (``"(as @S_0 S)"``, ``"(lambda (...) ...)"``, ...)
    included — passes through the unquoted form unchanged, since
    ``reverse.get(..., default)`` falls back to the unquoted string itself.

    The key of a symbol is its original name when no other declaration of the
    model has that name, and ``"name/arity"`` (``"name/arity:range"`` when that
    still does not tell two apart) when one name is declared more than once — one
    name at two arities, a function and a predicate of one name — as the Z3 route
    reports them (:func:`~unicode_fol_kit.atp.z3_models.declaration_keys`), so
    two symbols that this module renamed apart do not fold back into one entry.

    ``variables`` are the tokens that stand for a FREE variable (a declared symbol
    of the problem that is no constant; :meth:`SmtNameMap.variable_tokens`). A
    variable is reported under its own name, and as ``name!v`` when a constant of
    that name is declared too (:func:`~unicode_fol_kit.atp.z3_models.separate_variables`),
    so the constant keeps its plain name.
    """
    def original(text: str) -> str:
        return reverse.get(_unquote_smtlib(text), _unquote_smtlib(text))

    named = [(original(term), arity, range_text) for term, arity, range_text, _ in entries]
    is_variable = [_unquote_smtlib(term) in variables for term, _, _, _ in entries]
    keys = declaration_keys(separate_variables(named, is_variable))
    return {key: original(value) for key, (_, _, _, value) in zip(keys, entries)}


def _implication(formula: Node, premises: Sequence[Node]) -> Node:
    """Fold ``premises ⊨ φ`` into the single formula ``(∧ premises) → φ``.

    Reimplemented locally (rather than imported from
    :mod:`unicode_fol_kit.atp.protocol`) because the helper there is a
    private, unexported symbol — this module only imports protocol's public
    contract (:class:`ProverBackend`, :class:`Verdict`, the status
    constants).
    """
    premises = list(premises)
    if not premises:
        return formula
    conj = premises[0]
    for p in premises[1:]:
        conj = And(conj, p)
    return Implies(conj, formula)


def _timed(fn):
    """Run ``fn()`` returning ``(result, seconds)``."""
    start = time.perf_counter()
    result = fn()
    return result, time.perf_counter() - start


# ---------------------------------------------------------------------------
# Solver-version provenance (K1). cvc5 is a pip binding (``external = False``
# — see the class attribute below), not a spawned binary, so there is no
# ``--version`` subprocess to run and memoize the way
# ``atp.protocol._binary_version`` does for Vampire/Prover9/E/Zipperposition;
# the installed package's own distribution metadata is the analogous
# provenance, and it is exactly as immutable for the life of THIS process
# (the interpreter would have to restart to pick up a different install), so
# a one-slot memo is the same "ask once" discipline, just backed by
# ``importlib.metadata`` instead of a subprocess.
# ---------------------------------------------------------------------------

_VERSION_CACHE: Dict[str, Optional[str]] = {}


def _cvc5_package_version() -> Optional[str]:
    """The installed ``cvc5`` PyPI package's version, memoized process-wide.

    ``None`` when the package is not importable (mirrors
    :meth:`Cvc5Backend.available`) or its distribution metadata cannot be
    read for any reason (e.g. an editable/vendored install with no METADATA
    file) — best-effort provenance, never raises.
    """
    if "cvc5" in _VERSION_CACHE:
        return _VERSION_CACHE["cvc5"]
    version: Optional[str] = None
    if importlib.util.find_spec("cvc5") is not None:
        try:
            version = importlib.metadata.version("cvc5")
        except importlib.metadata.PackageNotFoundError:
            version = None
    _VERSION_CACHE["cvc5"] = version
    return version


# ---------------------------------------------------------------------------
# The Alethe proof text, in a child process.
#
# cvc5 1.3.4's proof PRINTER (``Solver.proofToString``) can end the calling
# process with a native access violation — e.g. ``∀x f(carl) = x ⊢ ∃w ∀x
# f(carl) = x`` — while ``checkSat``, ``getProof`` and ``getUnsatCore`` on the
# same solver are fine. A native crash is not a Python exception, so no
# ``try`` around the call can protect the caller. The verdict and the unsat core
# therefore never depend on it: the default path asks for neither a proof nor
# its text, and the text is produced only when the caller asks (``proof=True``),
# by a second solver run in a child interpreter with a time limit. A crash or a
# timeout there costs the text and nothing else, and the verdict says why.
# ---------------------------------------------------------------------------

#: Seconds the child interpreter may take on top of the solver's own time limit
#: (importing cvc5, printing the proof).
_PROOF_PROCESS_SLACK = 30.0

#: The child's time limit, in seconds, when the caller gave no time limit.
_PROOF_UNLIMITED_BUDGET = 60.0

#: What a PROVED verdict's proof says about its text when none was asked for.
_PROOF_NOT_REQUESTED = ("not requested: the Alethe text is produced only on request "
                        "(pass proof=True), in a child process")

#: The program the child interpreter runs. It reads one JSON object on stdin
#: (``smt2`` the problem, ``logic``, ``seed``, ``timeout`` in milliseconds) and
#: writes one JSON line on stdout. It imports nothing but ``cvc5``, so it runs the
#: same whatever the parent's ``sys.path`` is. The options are those of the
#: parent's solve plus the proofs; a solver that never reaches ``unsat`` here
#: (the time limit) reports that and no text.
_PROOF_CHILD_SOURCE = r"""
import json, sys
import cvc5

spec = json.loads(sys.stdin.read())
solver = cvc5.Solver()
solver.setLogic(spec["logic"])
solver.setOption("produce-models", "true")
solver.setOption("produce-proofs", "true")
solver.setOption("proof-format-mode", "alethe")
solver.setOption("produce-unsat-cores", "true")
solver.setOption("seed", str(spec["seed"]))
if spec["timeout"] and spec["timeout"] > 0:
    solver.setOption("tlimit", str(spec["timeout"]))
    solver.setOption("tlimit-per", str(spec["timeout"]))
parser = cvc5.InputParser(solver)
symbol_manager = parser.getSymbolManager()
parser.setStringInput(cvc5.InputLanguage.SMT_LIB_2_6, spec["smt2"], "cvc5_backend")
while True:
    command = parser.nextCommand()
    if command.isNull():
        break
    if command.getCommandName() == "check-sat":
        continue
    command.invoke(solver, symbol_manager)
result = solver.checkSat()
if not result.isUnsat():
    print(json.dumps({"ok": False, "why": "the proof run answered %s instead of unsat" % (result,)}))
    sys.exit(0)
raw = solver.proofToString(solver.getProof()[0])
print(json.dumps({"ok": True, "text": raw.decode("utf-8") if isinstance(raw, bytes) else raw}))
"""


def _alethe_text(smt2_text: str, logic: str, random_seed: int,
                 timeout: int) -> Tuple[Optional[str], Optional[str]]:
    """Ask a child interpreter for the Alethe proof of an unsatisfiable problem.

    Returns ``(text, None)``, or ``(None, reason)`` when there is no text: the
    child ended abnormally (cvc5's proof printer ending its process is the
    known case), ran past its time limit, could not be started, or did not reach
    ``unsat``. Never raises and never takes the calling process down; the
    caller's verdict and unsat core come from the main solve and are unaffected.

    The limit is the solver's own ``timeout`` (milliseconds) plus
    :data:`_PROOF_PROCESS_SLACK` seconds (:data:`_PROOF_UNLIMITED_BUDGET` plus
    the slack when there is no ``timeout``).
    """
    if not sys.executable:
        return None, "there is no Python interpreter to run the proof printer in"
    seconds = (timeout / 1000.0 if timeout and timeout > 0 else _PROOF_UNLIMITED_BUDGET)
    limit = seconds + _PROOF_PROCESS_SLACK
    spec = json.dumps({"smt2": smt2_text, "logic": logic, "seed": random_seed,
                       "timeout": timeout})
    try:
        done = subprocess.run([sys.executable, "-c", _PROOF_CHILD_SOURCE], input=spec,
                              capture_output=True, text=True, encoding="utf-8",
                              timeout=limit)
    except subprocess.TimeoutExpired:
        return None, (f"cvc5's proof run did not finish within {limit:g} s and was stopped; "
                      f"the verdict and the unsat core are from the main solve")
    except OSError as exc:
        return None, f"the proof run could not be started ({type(exc).__name__}: {exc})"
    if done.returncode != 0:
        return None, (f"cvc5's proof run ended abnormally (exit code {done.returncode}; its "
                      f"Alethe proof printer is known to end its process on some problems); "
                      f"the verdict and the unsat core are from the main solve")
    try:
        answer = json.loads(done.stdout.strip().splitlines()[-1])
    except (IndexError, ValueError):
        return None, "the proof run printed no answer"
    if not answer.get("ok"):
        return None, str(answer.get("why") or "the proof run gave no text")
    return answer["text"], None


class Cvc5Backend(ProverBackend):
    """Classical FOL/MSFOL via cvc5 — tri-state, with a model on refutation.

    Structurally the same contract as ``Z3Backend``: an entailment
    ``premises ⊨ formula`` is decided by asking whether the negated goal is
    UNSAT. ``proved`` and ``refuted`` are both fully trustworthy (cvc5's
    ``unsat``/``sat`` are sound and, on the quantifier-free fragment,
    complete); ``unknown`` only ever means cvc5's own instantiation search
    did not close the goal — never a silent downgrade of a real answer.

    Registered automatically: ``atp/protocol.py`` imports and registers this
    backend at the bottom of its own module, and its ``default_chain("fol")``
    inserts ``"cvc5"`` directly after ``"z3"`` whenever :meth:`available`
    is true — so on a machine with the optional ``cvc5`` extra installed, a
    plain ``prove()`` call runs cvc5 with zero caller action (see
    ``default_chain``'s docstring for why that one member is
    availability-dependent). This module itself never touches the registry.

    A PROVED verdict also carries a certificate in ``Verdict.proof``:
    ``{"kind": "cvc5_alethe", "text": <Alethe proof text or None>,
    "unsat_core": [<original-name term text>, ...]}``. The core is cvc5's own
    ``getUnsatCore`` on the per-call ``cvc5.Solver()`` this backend builds — no
    process-wide cvc5 setting is ever touched, mirroring ``Z3Backend``'s own
    per-``Solver`` discipline. ``unsat_core`` is SOUND (re-asserting just those
    terms is still unsat) but not necessarily MINIMAL — cvc5's core extraction
    is free to keep more than the smallest sufficient subset, exactly like
    ``Z3Backend``'s ``z3_unsat_core``. It also never contains one of the
    synthetic many-sorted axioms (non-emptiness and membership) described
    below — see :meth:`_run`'s docstring for how that exclusion is done, since this
    backend's SMT-LIB2-replay route has no ``assert_and_track``-style
    tagged boolean to lean on the way ``Z3Backend``'s own core does.
    ``unsat_core`` reading is best-effort (a format/version edge case degrades
    to ``[]`` rather than turning a sound PROVED verdict into an ERROR one), and
    it is reverse-mapped back to original kit-level symbol names before it
    reaches the caller — see :func:`_reverse_map_assignment` for the ``sat``
    branch's ``countermodel``.

    **The Alethe text is opt-in.** cvc5's proof printer can end the process
    (see the comment above :func:`_alethe_text`), so the text is produced only
    when asked for, ``decide(..., proof=True)``, and then by a second solver run
    in a child process with a time limit; the time of that run is part of the
    verdict's ``wall_time``. Without ``proof=True``, ``text`` is
    ``None`` and ``text_unavailable`` says so. With it, a crash or a timeout of
    the child leaves ``text`` ``None``, puts the reason in ``text_unavailable``
    and in the verdict's ``detail``, and leaves the PROVED verdict and the core
    exactly as they are.

    **Names.** A symbol is ``(kind, name, arity)``: one name at two arities, as a
    predicate and as a function or constant, is several symbols, each declared
    under a name of its own (two declarations of one name end cvc5's process),
    and a countermodel reports each under ``"name/arity"``. A kit symbol named
    like a symbol of a standard SMT-LIB theory (``+``, ``select``, ``str.len``,
    …) is renamed under every logic — see :data:`_SMTLIB_THEORIES`. The witnesses
    of a counting quantifier and of a sort's non-emptiness axiom are names of the
    problem like any other, fresh against every name of it (see the module
    docstring), so a predicate, a function, a constant or a sort called ``x0``
    never meets a witness. The countermodel, the unsat core and the proof text
    carry the caller's names.

    **Many-sorted (MSFOL) soundness.** A sorted quantifier/constant/count
    lowers to a plain unary predicate guard (the same relativisation
    :class:`Z3Backend` relies on), which by itself carries no guarantee that
    the guarded sort is non-empty or that a sorted constant ``c:S`` lies in
    ``S`` — and MSFOL, by convention, never gives a sort an empty universe and
    puts ``c`` in ``S`` (see the classical-reasoning guide's many-sorted
    section). :meth:`decide` closes both gaps exactly like
    :class:`Z3Backend` does: it adds
    ``unicode_fol_kit.fol._msfl_nodes.sort_axioms(*premises, formula)`` — one
    ``∃x S(x)`` per sort, one ``S(c)`` per sorted constant — as their own
    extra, UNNEGATED top-level assertions (one more ``(assert ...)`` command
    each, mirroring how every premise already gets its own — see
    :meth:`_run`'s docstring), never folded inside ``to_z3()`` itself. They
    are built from the SANITISED nodes (the ones that are actually
    translated), so a sort or a constant whose name had to be renamed to be a
    legal SMT-LIB2 symbol carries the same token in the fact as in the
    premises; the sanitiser renames sorts, sorted constants and the plain
    constants of the same name alike (see :func:`_sanitize_node_for_smtlib`).
    Empty for an unsorted query, so behaviour there is unchanged.
    """

    name = "cvc5"
    logics = frozenset({"fol"})
    external = False   # pip package (optional extra), not a spawned binary

    def available(self) -> bool:
        """Pure discovery: is the ``cvc5`` package importable? (No import.)"""
        return importlib.util.find_spec("cvc5") is not None

    def solver_version(self) -> Optional[str]:
        """The installed ``cvc5`` package's own distribution version
        (``importlib.metadata.version("cvc5")``), memoized process-wide —
        see :func:`_cvc5_package_version`. ``None`` when the package is not
        installed.
        """
        return _cvc5_package_version()

    def decide(self, formula: Node, premises: Sequence[Node] = (),
               timeout: int = 10000, **options) -> Verdict:
        """Decide ``premises ⊨ formula`` and return a :class:`Verdict`.

        Args:
            formula: the goal.
            premises: entailment premises (``⊨ formula`` when empty).
            timeout: milliseconds; forwarded to cvc5's ``tlimit-per`` (the
                limit of the one query this backend asks) AND ``tlimit``
                options -- ``tlimit`` alone was measured not to stop a
                non-terminating instantiation chain at all, so the per-query
                option is what makes the budget real (``0``/negative disables
                the limit, matching cvc5's own "unlimited" default).
            **options: ``logic`` overrides the SMT-LIB logic string handed
                to cvc5 (default ``"UF"`` — what any classical FOL/MSFOL
                fragment ``to_z3`` produces IS: a single uninterpreted sort
                with equality and uninterpreted functions/predicates, never
                arithmetic. It was ``"ALL"`` until 0.30.0, under which cvc5
                knows hundreds of theory symbols by name, and a predicate
                ``<`` or a function ``+`` / ``select`` / ``sin`` of this
                kit — uninterpreted here — ended the PROCESS with a native
                access violation. A kit symbol named like a symbol of an
                SMT-LIB theory is renamed whatever the logic — see
                :data:`_SMTLIB_THEORIES`); ``random_seed``
                overrides cvc5's search seed (default ``42``, for
                reproducible verdicts across runs); ``proof`` (default
                ``False``) asks for the Alethe proof text of a PROVED verdict,
                produced by a second solver run in a child process with a time
                limit (see the class docstring) — without it
                ``Verdict.proof["text"]`` is ``None``, and with it the time of
                that second run is part of ``Verdict.wall_time``.

        Returns:
            A :class:`Verdict` with ``status`` in
            ``{"proved", "refuted", "unknown", "error"}``. Never raises for
            an in-contract ``Node`` — an unsupported fragment (``to_z3``
            raising ``NotImplementedError``, e.g. linear-logic/Lambek nodes,
            or a numeral and a constant of one text, which are one symbol, or a
            counting quantifier of a bound above 500, which the refusal names)
            comes back UNKNOWN/``"unsupported"``; a counting bound up to 500 is
            expanded and asked (nothing here recurses on its nesting); a formula
            nested deeper than the interpreter's recursion limit comes back
            ERROR/``"infra"`` with a detail that starts ``RecursionError``
            (``api.prove`` runs such a formula where it can be read, and names
            the depth when it cannot); any failure in the
            SMT-LIB2 round trip through cvc5 itself comes back
            ERROR/``"infra"`` rather than propagating. A REFUTED verdict's
            ``countermodel["assignment"]`` names every symbol by its
            ORIGINAL kit-level name — see :func:`_reverse_map_assignment`
            and the module docstring's sanitisation section — never a
            digit-safe synthesised token, and never SMT-LIB2 ``|...|``
            quoting syntax wrapped around a non-ASCII one. A PROVED verdict
            whose proof text was asked for (``proof=True``) and could not be
            produced says why in ``detail`` and in ``proof["text_unavailable"]``.
        """
        premises = list(premises)
        try:
            problem = premises + [formula]
            # The counting quantifiers are expanded, and the sort axioms made, BEFORE the
            # sanitiser runs, so that every name of the text -- the witnesses of an
            # expansion and of a non-emptiness axiom too -- is a symbol the sanitiser has
            # seen and keeps apart from every other (one namespace in SMT-LIB text; a
            # bound variable spelled like a predicate ends cvc5's process). The axioms are
            # built from the formulas as written: the sanitiser renames them together with
            # the premises and the goal, so the sort guard and the constant of a
            # membership atom carry the tokens the premises use (see the class docstring's
            # many-sorted-soundness paragraph).
            lowered, avoid = _lower_counting_for_smtlib(problem)
            sort_facts = list(sort_axioms(*problem, avoid_names=avoid))
            sanitised_nodes, name_map = _sanitize_many_for_smtlib(lowered + sort_facts)
            sanitised_premises = sanitised_nodes[:len(premises)]
            sanitised_formula = sanitised_nodes[len(premises)]
            sanitised_facts = sanitised_nodes[len(premises) + 1:]
            # The sanitiser has given every variable and every constant a token of its
            # own, so the environment names a variable as it is named: the SMT-LIB text
            # then holds the tokens, which is what the countermodel is read back through.
            env = Z3Env(variables_apart=False)
            z3_premises = [p.to_z3(env) for p in sanitised_premises]
            z3_formula = sanitised_formula.to_z3(env)
            z3_sort_facts = [axiom.to_z3(env) for axiom in sanitised_facts]
        except NotImplementedError as exc:
            return Verdict(UNKNOWN, self.name, reason="unsupported",
                           solver_version=self.solver_version(), detail=str(exc))
        except RecursionError as exc:
            # a formula nested deeper than the interpreter's recursion limit: the dispatcher
            # (``api.prove``) names the depth for a verdict that starts like this one
            return Verdict(ERROR, self.name, reason="infra", solver_version=self.solver_version(),
                           detail=f"{type(exc).__name__}: {exc}")

        logic = options.pop("logic", "UF")
        random_seed = options.pop("random_seed", 42)
        want_proof = bool(options.pop("proof", False))
        # One importlib.metadata read, memoized process-wide (see
        # _cvc5_package_version) — cheap enough to call unconditionally on
        # every decide(), unlike the subprocess-spawning backends' own
        # solver_version() lookups.
        solver_version = self.solver_version()

        try:
            (kind, payload), elapsed = _timed(
                lambda: self._run(z3_formula, z3_premises, z3_sort_facts,
                                  timeout, logic, random_seed))
        except Exception as exc:   # noqa: BLE001 - cvc5/z3 raise plain RuntimeError/etc.
            return Verdict(ERROR, self.name, reason="infra",
                           solver_version=solver_version,
                           detail=f"{type(exc).__name__}: {exc}")

        if kind == "unsat":
            reverse = name_map.reverse()
            text: Optional[str] = None
            why: Optional[str] = _PROOF_NOT_REQUESTED
            detail: Optional[str] = None
            if want_proof:
                (text, why), proof_seconds = _timed(
                    lambda: _alethe_text(payload["smt2"], logic, random_seed, timeout))
                elapsed += proof_seconds
                if text is None:
                    detail = f"no Alethe proof text: {why}"
            proof = {
                "kind": "cvc5_alethe",
                "text": _reverse_map_smtlib_text(text, reverse) if text is not None else None,
                # An unsat CORE, per cvc5's own getUnsatCore() — sound
                # (re-asserting just these terms is still unsat) but not
                # necessarily MINIMAL, exactly like Z3Backend's core; see
                # this backend's class docstring.
                "unsat_core": [_reverse_map_smtlib_text(term, reverse)
                               for term in payload["unsat_core"]],
            }
            if text is None:
                proof["text_unavailable"] = why
            return Verdict(PROVED, self.name, wall_time=elapsed,
                           solver_version=solver_version, proof=proof, detail=detail)
        if kind == "sat":
            assignment = _reverse_map_assignment(payload, name_map.reverse(),
                                                 name_map.variable_tokens())
            return Verdict(REFUTED, self.name, wall_time=elapsed,
                           solver_version=solver_version,
                           countermodel={"kind": "cvc5_model", "assignment": assignment})
        # kind == "unknown"
        return Verdict(UNKNOWN, self.name, reason=payload["reason"], wall_time=elapsed,
                       solver_version=solver_version, detail=payload["detail"])

    @staticmethod
    def _run(z3_formula, z3_premises: Sequence, z3_sort_facts: Sequence, timeout: int,
             logic: str, random_seed: int):
        """Serialise ``z3_premises``/``z3_sort_facts``/``¬z3_formula`` to
        SMT-LIB2 and decide with cvc5.

        Each of ``z3_premises``, ``z3_sort_facts`` and ``Not(z3_formula)``
        becomes its OWN top-level Z3 ``.add()`` call, hence its OWN
        ``(assert ...)`` line in ``Solver.to_smt2()`` and its OWN
        ``assertFormula`` when replayed — see
        :func:`_sanitize_many_for_smtlib`'s docstring for why: cvc5's
        ``getUnsatCore()`` reports relevance per top-level assertion, so
        this is what lets it exclude an irrelevant premise instead of
        always naming "the whole conjoined problem". Logically identical to
        asserting one folded ``(∧ premises ∧ sort facts) → φ`` implication (a
        solver conjoins every assertion regardless of how many commands they
        arrived in) — this changes only the unsat-core bookkeeping.
        ``z3_premises`` are asserted FIRST, then ``z3_sort_facts`` (the
        non-emptiness of every sort AND the membership atom of every sorted
        constant, in one list), then the negated goal — :meth:`decide` keeps
        them as separate arguments (rather than one pre-concatenated list) so
        this method knows exactly which assertion INDICES are the synthetic
        sort facts once it needs to exclude them from the reported core below.
        The facts are asserted OUTSIDE the negated goal: a membership atom under
        the goal's negation would be one more thing to prove.

        Returns ``("unsat", payload)``, ``("sat", entries)``, or
        ``("unknown", {"reason": ..., "detail": ...})``. The ``unsat`` payload
        is ``{"unsat_core": [term_text, ...], "smt2": text}``: the core, and the
        SMT-LIB2 text of the problem, which is what the proof run of
        :func:`_alethe_text` needs. ``entries`` is one ``(declared_term_text,
        arity, range, value_text)`` per declared symbol, ``range`` being
        ``"Bool"`` for a predicate and ``"S"`` for a function or constant (what
        :func:`~unicode_fol_kit.atp.z3_models.declaration_keys` reads).
        Every string is still in cvc5's OWN (possibly sanitised) symbol names —
        :meth:`decide` reverse-maps it to original kit-level names; this method
        stays a pure cvc5-API wrapper.

        **No proof is built here.** ``produce-proofs`` is off: the verdict and
        the unsat core need none (``getUnsatCore`` works without it, measured),
        and the proof PRINTER can end the process (see :func:`_alethe_text`), so
        the Alethe text is produced elsewhere, in a child process, when asked
        for. Nothing this method calls is known to end the process.

        ``unsat_core`` NEVER contains one of ``z3_sort_facts`` — those are
        background MSFOL convention (every sort is non-empty, a sorted constant
        is in its sort), never one of the caller's own premises, mirroring how
        ``atp.protocol._z3_track_and_check`` asserts the identical axioms
        UNTRACKED so :class:`~unicode_fol_kit.atp.protocol.Z3Backend`'s own
        ``z3_unsat_core`` can never name them either (see that function's
        docstring). cvc5's SMT-LIB2-replay route here has no tagged-boolean
        ``assert_and_track`` equivalent to lean on, so exclusion instead
        matches each ``getUnsatCore()`` term against the sort-fact slice
        of ``solver.getAssertions()`` (the SAME solver, in the SAME order
        just asserted above) by cvc5 ``Term`` equality — robust to cvc5's
        own core/assertion printers disagreeing on whitespace, and exact
        unless a CALLER-supplied premise is itself syntactically identical
        to one of the synthetic facts (a premise that reads ``∃x (Ghost(x))``
        for a sort literally named ``Ghost``, or ``Human(socrates)`` for a
        constant ``socrates:Human`` — the latter is common), in which case that
        coincidental duplicate is absorbed into the background fact instead of
        being listed — harmless, since a premise that equals a background fact
        adds nothing to it, so the reported core together with the background
        facts is still unsat (``unsat_core`` is already documented as
        sound-but-not-necessarily-minimal).

        Core production is enabled unconditionally (per-``Solver``-instance
        only — this class never touches a process-wide cvc5 setting), but
        reading it back (:meth:`cvc5.Solver.getUnsatCore`/``getAssertions``) is
        best-effort: a failure there must not turn a genuinely sound ``unsat``
        result into anything but PROVED, so it degrades to an empty core
        rather than raising.
        """
        import cvc5
        from z3 import Solver as Z3Solver, Not as _ZNot

        z3_solver = Z3Solver()
        for z3_premise in z3_premises:
            z3_solver.add(z3_premise)
        for z3_axiom in z3_sort_facts:
            z3_solver.add(z3_axiom)
        z3_solver.add(_ZNot(z3_formula))
        smt2_text = z3_solver.to_smt2()

        solver = cvc5.Solver()
        solver.setLogic(logic)
        solver.setOption("produce-models", "true")
        solver.setOption("produce-unsat-cores", "true")
        solver.setOption("seed", str(random_seed))
        if timeout and timeout > 0:
            # BOTH options, because they do not bound the same thing. ``tlimit``
            # is the cumulative limit of the solver instance and ``tlimit-per``
            # the limit of ONE query; this method asks exactly one, so the two
            # are the same budget. Measured (cvc5 1.3.4) on a one-GCI
            # description-logic image -- ``∀x (OwlThing(x) → ∃y (r(x,y) ∧
            # C(y)))`` with ``r`` typed into OwlThing, whose instantiation chain
            # never ends: ``tlimit=3000`` alone never returned (a hard cap of
            # 60 s was hit, and the default prover chain with it), while
            # ``tlimit-per=3000`` came back ``unknown (TIMEOUT)`` after 3.09 s.
            # So the PER-QUERY option is the one that enforces the budget.
            solver.setOption("tlimit", str(timeout))
            solver.setOption("tlimit-per", str(timeout))

        parser = cvc5.InputParser(solver)
        symbol_manager = parser.getSymbolManager()
        parser.setStringInput(cvc5.InputLanguage.SMT_LIB_2_6, smt2_text, "cvc5_backend")

        while True:
            command = parser.nextCommand()
            if command.isNull():
                break
            # The (check-sat) command in the replayed text is skipped so we
            # get a real cvc5.Result from checkSat() below, not its stringified
            # form from Command.invoke().
            if command.getCommandName() == "check-sat":
                continue
            command.invoke(solver, symbol_manager)

        result = solver.checkSat()

        if result.isUnsat():
            try:
                core = solver.getUnsatCore()
                # solver.getAssertions() replays in the SAME order the three
                # groups were asserted above: z3_premises, then z3_sort_facts,
                # then Not(z3_formula) — slice out exactly the sort-fact
                # group so it can be excluded from the reported core by
                # cvc5 Term equality (see this method's docstring).
                assertions = solver.getAssertions()
                n_premises = len(z3_premises)
                fact_terms = list(assertions[n_premises:n_premises + len(z3_sort_facts)])
                core_terms = [str(term) for term in core if term not in fact_terms]
            except Exception:   # noqa: BLE001 - best-effort certificate, must not sink a sound PROVED verdict
                core_terms = []
            return "unsat", {"unsat_core": core_terms, "smt2": smt2_text}
        if result.isSat():
            entries = []
            for term in symbol_manager.getDeclaredTerms():
                try:
                    value = str(solver.getValue(term))
                    sort = term.getSort()
                    if sort.isFunction():
                        arity, codomain = sort.getFunctionArity(), sort.getFunctionCodomainSort()
                    else:
                        arity, codomain = 0, sort
                    entries.append((str(term), arity, "Bool" if codomain.isBoolean() else "S", value))
                except Exception:   # noqa: BLE001 - best-effort witness, one symbol must not blank out the rest
                    continue
            return "sat", entries

        explanation = result.getUnknownExplanation()
        reason = "timeout" if explanation == cvc5.UnknownExplanation.TIMEOUT else "incomplete"
        return "unknown", {"reason": reason, "detail": str(explanation)}
