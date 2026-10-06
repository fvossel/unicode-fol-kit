"""TPTP input: read TPTP ``fof`` / ``cnf`` formulas and whole problem files into the AST.

This is the inverse of :meth:`Node.to_tptp`. TPTP has a genuinely different surface
syntax from the toolkit's Unicode notation (the ``fof(name, role, formula).`` wrapper,
``! [X] : φ`` / ``? [X] : φ`` quantifiers, uppercase variables, lowercase
constants/functions/predicates, ``& | ~ => <=> <~>`` connectives, ``$less``/``$sum``
dollar-words), so it gets its own Lark grammar rather than the glyph-translation used
for LaTeX import.

Public API:

- :func:`parse_tptp_formula` — parse a single bare FOF/CNF formula into a :class:`Node`.
- :func:`parse_tptp` — parse a whole TPTP problem (one or more ``fof``/``cnf``
  statements) into a list of :class:`TptpFormula` ``(name, role, formula)`` records.
- :func:`load_tptp` — read a ``.p`` / ``.tptp`` file and :func:`parse_tptp` it.

Naming conventions (the exact inverse of :meth:`Node.to_tptp`): a TPTP **variable**
(uppercase) becomes a lowercase :class:`Variable`; a **predicate** (lowercase in TPTP)
is capitalised to match the toolkit's uppercase-predicate convention, so ``loves`` ↦
``Loves`` and ``p`` ↦ ``P``; **constants** and **functions** stay lowercase; ``=`` /
``!=`` map to the ``=`` / ``≠`` atoms; the comparison dollar-words ``$less`` /
``$greater`` / ``$lesseq`` / ``$greatereq`` map to the ``<`` / ``>`` / ``≤`` / ``≥``
atoms; and the arithmetic dollar-words ``$sum`` / ``$difference`` / ``$product`` /
``$quotient`` map to the ``+`` / ``-`` / ``*`` / ``/`` functions. ``$true`` / ``$false``
are imported as the nullary atoms ``$true`` / ``$false`` (the toolkit has no
boolean-constant node), which every route that decides or evaluates a formula reads
as TPTP's defined propositions — true and false — and the TPTP writers write back
verbatim.

A TPTP variable is case-sensitive and the kit variable is its lower-cased form, so
two variables that differ only by letter case (``Xa``, ``XA``) would become one
kit variable. Where that changes the formula — one is captured by the other's
quantifier, or both occur free in one formula — the reader REFUSES it by name,
naming both variables (``![Xa, XA]: p(Xa, XA)`` is not read as ``∀xa ∀xa
P(xa, xa)``); where each is bound by a quantifier of its own and they never meet
(``(![Xa]: p(Xa)) & (![XA]: q(XA))``) the reading is the same formula and is
unchanged. No renaming is invented: rename one of the two.

Single-quoted atoms (``'http___example_org_Thing'``) — the form OWL→FOL translators
emit for IRIs — are accepted as functor / predicate / constant names: the quotes are
stripped and the ``\\'`` / ``\\\\`` escapes unescaped. The resulting names may contain
characters that are not legal MSFLParser tokens, so call
:func:`unicode_fol_kit.fol.sanitize_names` before re-parsing the rendered Unicode.

Scope: the first-order ``fof`` fragment, ``cnf`` clauses, and TF0 (monomorphic
typed first-order) ``tff`` — see :func:`parse_tff_problem` below for the typed
half. ``include('path')`` / ``include('path', [name, ...])`` directives are
resolved by every file/load entry point (see "Includes" below); the optional
4th (``source``)/5th (``useful_info``) annotation fields of a statement parse
and are discarded. THF (higher-order TPTP), TF1 polymorphism (type
variables, ``!>``), and TPTP's built-in arithmetic sorts (``$int``/``$rat``/
``$real``) remain out of scope — each is refused LOUDLY, naming the
construct, rather than silently narrowed. THF and TF1 are refused BEFORE the
first-order grammar is tried, by the statement's kind and by the binder, so the
refusal does not depend on the rest of the text parsing: a problem with a ``thf(...)``
statement (a type declaration, an application ``p @ A``, whatever its body) is a
:class:`TptpParsingError` naming THF, and a text with the type binder ``!>`` or a
quantifier variable of type ``$tType`` (``![A: $tType]``) is an error naming TF1
polymorphism that is a :class:`TptpParsingError` and also a
:class:`NotImplementedError`. Comments and single-quoted atoms are taken out first,
so a ``thf(`` or a ``!>`` inside one is no statement and no binder. The arithmetic sorts
are refused by :class:`NotImplementedError` where a declaration or a quantifier names
one (see :func:`parse_tff_problem`'s docstring for exactly which constructs raise
where).

Includes
--------
:func:`parse_tptp`, :func:`parse_tptp_problem` and :func:`parse_tff_problem`
take an optional ``base_dir`` (the directory an ``include(...)`` inside
``text`` resolves relative to first) and ``search_paths`` (further roots
tried next, in order — the TPTP-library convention: ``include(
'Axioms/SET001+0.ax')`` is root-relative, not relative to whatever file
referred to it). ``os.environ["TPTP"]``, if set, is ALSO tried as a root,
after ``search_paths`` — the same convention external TPTP tooling uses to
locate the library. ``base_dir=None`` (the default) means "no including
file's directory is known": an ``include`` then raises
:class:`TptpParsingError` naming the directive rather than guessing, which
keeps every existing bare-text caller — :func:`parse_tptp_formula` included,
which never resolves includes at all, since a single bare formula has no
"including file" — byte-identical by default.

:func:`load_tptp`, :func:`load_tptp_problem` and :func:`load_tff_problem`
set ``base_dir`` to the loaded file's own directory automatically (so a
sibling include resolves with no extra argument) and seed cycle detection
with the loaded file's own path, so a chain that loops back to the very
file you started from is caught, not only a cycle confined to files reached
purely via nested includes. A selection list (``include('path', [name1,
name2])``) imports only those formulas, matched by their own TPTP statement
name, and refuses a name absent from the included file; a missing include
file names the path and every root tried; a circular include chain names
the whole chain. A selection list on a file that also declares TFF
vocabulary (a ``tff(name, type, ...).`` statement) is refused — see
:func:`parse_tff_problem`'s docstring.

TF0 (``tff``) reading, in brief
--------------------------------
:func:`parse_tptp` / :func:`parse_tptp_formula` / :func:`load_tptp` now also
accept ``tff(name, axiom|conjecture|..., <formula>).`` statements (typed
quantifiers ``! [X: sort] : φ`` / ``? [X: sort] : φ`` build
:class:`~unicode_fol_kit.fol.nodes.SortedQuantifier`; an untyped ``! [X] : φ``
still builds a plain :class:`~unicode_fol_kit.fol.nodes.Quantifier`, exactly
as before — this is purely additive). A ``tff(name, type, ...).`` TYPE
DECLARATION, however, has no ``TptpFormula`` shape to return (it declares
vocabulary, not a formula), so :func:`parse_tptp` refuses a problem
containing one, naming :func:`parse_tff_problem` as the function that reads
it: that function returns the declared
:class:`~unicode_fol_kit.fol.signature.Signature` ALONGSIDE the formulas,
and additionally promotes a plain :class:`~unicode_fol_kit.fol.nodes.Constant`
occurrence to a :class:`~unicode_fol_kit.fol.nodes.SortedConstant` wherever
that name was declared with a concrete (non-``$i``) sort — recovering the
same AST shape :func:`~unicode_fol_kit.atp.tptp_tff.generate_tff_problem`
started from, since a TFF formula BODY carries no inline sort annotation for
a constant occurrence (only a bound variable does; a constant's sort lives
solely in its separate ``type`` declaration).

Two parsers, LALR first and Earley as a fallback
------------------------------------------------
The grammar below is parsed by FOUR lark parsers: an LALR(1) pair (``file``
and ``formula`` start symbols) that is tried first, and the original Earley
pair that takes over whenever LALR raises ``UnexpectedInput``. The reason is
measured, not stylistic: on a real 1,367,212-byte, 4291-formula TPTP
translation of an ontology, ``load_tptp_problem`` took 68.3 s through Earley
and 1.7 s through LALR — and the two produce BYTE-IDENTICAL item lists for
all 4291 records. The cost is per formula (4.15 ms against 0.2 ms), not
superlinear in file size, and a ``cProfile`` run attributes 98 % of it to
lark's dynamic-lexer Earley chart, so this is the only lever that matters.

The fallback is what makes it risk-free, and only the PARSE step falls back:
if LALR refuses a text, Earley re-parses it and Earley raises, so no input
that parsed before stops parsing and every syntax-error message stays
byte-identical. The TRANSFORM step is never retried — the TF0-scope refusals
(``NotImplementedError`` for TF1/``$int``/``$rat``/``$real``, the
``ConflictingArityError`` path) come out of the shared transformer and are
identical either way, so a retry would only double the work.

The asymmetry that remains: LALR uses lark's contextual lexer and Earley the
dynamic one, so in principle LALR could ACCEPT a text Earley rejects, which
the fallback does not protect against. Every terminal here is disjoint by
first character (``VAR`` ``[A-Z]``, ``LOWER`` ``[a-z]``, ``SQ`` ``'``,
``DOLLARWORD`` ``$``, ``NUMBER`` a digit or ``-``) and every operator is a
literal string resolved by longest match, so a divergence would need a
GRAMMAR change to introduce. ``tests/test_tptp_input.py`` therefore keeps a
permanent parametrised agreement battery over both parsers, plus an explicit
assertion that the grammar still builds as LALR(1) — so a future grammar edit
that breaks the equivalence goes red instead of silently falling back to
Earley for every parse.
"""

import os
import re
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Tuple

from lark import Lark, Transformer, Tree
from lark.exceptions import UnexpectedInput, VisitError

from ._fol_nodes import _numeral_from_text
from .nodes import (
    Node, Variable, Constant, Number, Function,
    Atom, Not, And, Or, Xor, Implies, Iff, Quantifier,
    SortedQuantifier, SortedConstant,
)
from .naming import ParsingError
from .signature import Signature, PredicateDecl, FunctionDecl, ConstantDecl


class TptpParsingError(ParsingError):
    """A TPTP import failure, carrying a plain message.

    Subclasses :class:`ParsingError` (so ``except ParsingError`` still catches it)
    but takes a string instead of a Lark exception — the same pattern
    :class:`ConflictingArityError` uses.
    """

    def __init__(self, message: str):
        self.args = (message,)

    def __str__(self):
        return self.args[0]


class _Tf1PolymorphismError(TptpParsingError, NotImplementedError):
    """TF1 polymorphism (a type variable), refused by name.

    A :class:`TptpParsingError`, like every other refusal of a text this reader does not
    read, and also a :class:`NotImplementedError`, which is what the refusal of a TF1
    type declaration always was: a caller that catches either keeps catching it.
    """


_THF_REFUSAL = (
    "SYNTAX_ERROR: THF (higher-order TPTP) is out of scope for "
    "this reader; only fof, cnf, and tff (TF0, monomorphic) are "
    "supported."
)

_TF1_REFUSAL = (
    "TF0 reader: TF1 polymorphic types and type variables ('!> [...] : ...', "
    "'![A: $tType] : ...') are out of scope for this monomorphic TF0-only reader."
)


# Dollar-word predicate / function dictionaries — the inverse of the
# PREFIX_PREDS_TPTP / TPTP_ARITH_OPS tables in _fol_nodes.py.
_DOLLAR_PRED = {"$less": "<", "$greater": ">", "$lesseq": "≤", "$greatereq": "≥"}
_DOLLAR_FUNC = {"$sum": "+", "$difference": "-", "$product": "*", "$quotient": "/"}


@dataclass(frozen=True)
class TptpFormula:
    """One annotated TPTP statement: its ``name``, ``role``, and parsed ``formula``."""

    name: str
    role: str
    formula: Node


@dataclass(frozen=True)
class _IncludeDirective:
    """One parsed ``include('path').`` / ``include('path', [n1, n2]).`` directive.

    Internal only: ``file()`` (see :class:`_TptpTransformer`) returns these
    interleaved with :class:`TptpFormula` / TF0 declaration records in
    source order, and :func:`_resolve_includes` splices each one, in place,
    with the (recursively resolved) statements of the file it names, before
    any public function ever sees one. ``selection`` is ``None`` when no
    ``[...]`` name list was given (import everything from the included
    file), else the tuple of names to import selectively.
    """

    file_name: str
    selection: Optional[Tuple[str, ...]]


_GRAMMAR = r"""
file: (stmt | include_stmt)+
stmt: LOWER "(" fof_name "," LOWER "," formula ["," annotation_term ["," annotation_term]] ")" "."
    | LOWER "(" fof_name "," LOWER "," tff_type_decl ["," annotation_term ["," annotation_term]] ")" "."  -> stmt_type
fof_name: LOWER | NUMBER

// --- include directives: "include('path')." / "include('path', [n1,n2])." ---
// Resolved by _resolve_includes AFTER transforming (splicing in the named
// file's own statements), never during parsing -- see that function and the
// module docstring's "Includes" section.
include_stmt: "include" "(" (LOWER | SQ) ["," "[" name_list "]"] ")" "."
name_list: fof_name ("," fof_name)*

// --- the optional 4th (source) / 5th (useful_info) annotation fields ---
// Accepted syntactically and discarded -- see _TptpTransformer.stmt /
// .stmt_type. Not TPTP's full "general_term" grammar (no THF-shaped terms,
// no arithmetic expressions), just enough to admit the shapes real TPTP
// files use for these two fields: a functor application (`file(...)`,
// `inference(...)`), a bracketed list of either, or a bare atom/variable/
// number/quoted string.
annotation_term: LOWER "(" annotation_term_list ")"
                | "[" [annotation_term_list] "]"
                | LOWER
                | SQ
                | VAR
                | NUMBER
annotation_term_list: annotation_term ("," annotation_term)*

?formula: equiv
?equiv: imp
      | imp "<=>" imp   -> iff
      | imp "<~>" imp   -> xor
?imp: disj
    | disj "=>" imp     -> implies
    | disj "<=" imp     -> rev_implies
?disj: conj
     | disj "|" conj    -> or_
     | disj "~|" conj   -> nor
?conj: unary
     | conj "&" unary   -> and_
     | conj "~&" unary  -> nand
?unary: "~" unary       -> neg
      | "!" "[" varlist "]" ":" unary  -> forall
      | "?" "[" varlist "]" ":" unary  -> exists
      | "(" formula ")"
      | atom

// A TFF quantifier's variable may carry an explicit ":" sort. A plain,
// untyped "! [X] : ..." still round-trips (typed_var's optional sort is
// simply absent) -- shared unmodified by fof/cnf too, see module docstring.
varlist: typed_var ("," typed_var)*
typed_var: VAR (":" tff_atomic_type)?

?atom: term "=" term    -> equality
     | term "!=" term   -> disequality
     | DOLLARWORD "(" termlist ")"  -> dollar_atom
     | LOWER "(" termlist ")"       -> pred_app
     | SQ "(" termlist ")"          -> pred_app
     | DOLLARWORD                   -> bool_const
     | LOWER                        -> prop_atom
     | SQ                           -> prop_atom

?term: VAR                          -> var
     | DOLLARWORD "(" termlist ")"  -> dollar_func_app
     | LOWER "(" termlist ")"       -> func_app
     | SQ "(" termlist ")"          -> func_app
     | LOWER                        -> constant
     | SQ                           -> constant
     | NUMBER                       -> number

termlist: term ("," term)*

// --- TF0 type declarations: "tff(name, type, <tff_type_decl>)." ---
// (TF1 polymorphism and THF are NOT extensions of this: tff_poly_decl below
// always raises, and "thf(" is refused at the statement-keyword check —
// see the module docstring and _TptpTransformer.stmt_type/tff_poly_decl.)
tff_type_decl: (LOWER | SQ) ":" tff_top_type

?tff_top_type: DOLLAR_TTYPE                              -> tff_sort_decl
             | "!>" "[" tyvarlist "]" ":" tff_poly_monotype -> tff_poly_decl
             | tff_mapping_type                            -> tff_symbol_decl
             | tff_atomic_type                             -> tff_nullary_decl

tyvarlist: VAR ("," VAR)*

// The TF1 polymorphic body ("!> [A] : (A > A)" and similar) is parsed only
// so tff_poly_decl below can raise a NAMED refusal instead of a generic
// parse failure -- a type VARIABLE (VAR) is otherwise never a legal atomic
// type (see tff_atomic_type), so this sub-grammar is kept separate rather
// than widening the ordinary (monomorphic) one. Never given transformer
// methods: tff_poly_decl discards its children unconditionally.
?tff_poly_monotype: tff_poly_atomic_type
                   | "(" tff_poly_mapping_type ")"
tff_poly_mapping_type: tff_poly_domain ">" tff_poly_atomic_type
tff_poly_domain: tff_poly_atomic_type
               | "(" tff_poly_xprod ")"
tff_poly_xprod: tff_poly_atomic_type ("*" tff_poly_atomic_type)+
tff_poly_atomic_type: LOWER | SQ | DOLLARWORD | VAR

tff_mapping_type: tff_domain ">" tff_atomic_type
?tff_domain: tff_atomic_type          -> domain_single
           | "(" tff_xprod ")"        -> domain_prod
tff_xprod: tff_atomic_type ("*" tff_atomic_type)+

tff_atomic_type: LOWER      -> plain_type
                | SQ         -> plain_type
                | DOLLARWORD -> dollar_type

VAR: /[A-Z][A-Za-z0-9_]*/
LOWER: /[a-z][A-Za-z0-9_]*/
SQ: /'(\\.|[^'\\])*'/
DOLLARWORD: /\$[a-z_]+/
DOLLAR_TTYPE.2: "$tType"
NUMBER: /-?[0-9]+(\.[0-9]+)?/

%import common.WS
%ignore WS
%ignore /%[^\r\n]*/
%ignore /\/\*(.|\n)*?\*\//
"""


def _cap(name: str) -> str:
    """Capitalise the first letter (invert to_tptp's predicate lower-casing)."""
    return name[:1].upper() + name[1:] if name else name


def _functor_name(token) -> str:
    """Return the bare functor/constant name from a LOWER or single-quoted token.

    A TPTP **single-quoted atom** ``'…'`` is an arbitrary functor name (the form
    OWL→FOL dumps use for IRIs, e.g. ``'http___example_org_Thing'``). The
    surrounding quotes are stripped and the TPTP escapes ``\\'`` / ``\\\\`` are
    unescaped; a plain LOWER token is returned unchanged. The resulting name may
    contain characters (underscores, etc.) that are not legal MSFLParser tokens —
    use :func:`unicode_fol_kit.fol.sanitize_names` before re-parsing the rendered
    Unicode.
    """
    s = str(token)
    if len(s) >= 2 and s[0] == "'" and s[-1] == "'":
        return re.sub(r"\\(.)", r"\1", s[1:-1])
    return s


# =============================================================================
# TF0 type declarations: parsed shapes and atomic-type resolution
# =============================================================================

_ARITHMETIC_SORTS = frozenset({"$int", "$rat", "$real"})


@dataclass(frozen=True)
class _TffSortDecl:
    """A parsed ``tff(name, type, S: $tType).`` sort declaration."""

    name: str


@dataclass(frozen=True)
class _TffPredDecl:
    """A parsed predicate type declaration: name, and each argument's
    resolved sort (``None`` for ``$i``, else a capitalised kit-level sort
    name -- see :func:`_resolve_type_str`)."""

    name: str
    arg_sorts: Tuple[Optional[str], ...]


@dataclass(frozen=True)
class _TffFuncDecl:
    """A parsed function/constant type declaration (``arg_sorts == ()``
    means a 0-ary function, i.e. a constant, in :func:`parse_tff_problem`'s
    Signature assembly)."""

    name: str
    arg_sorts: Tuple[Optional[str], ...]
    result_sort: Optional[str]


def _resolve_type_str(type_str: str, *, context: str) -> Optional[str]:
    """Return the kit-level sort name for one TFF atomic-type string, or
    ``None`` for ``"$i"`` (TPTP's default individual type -- "no sort
    annotation needed", matching a plain unsorted :class:`Quantifier` /
    :class:`Constant`). ``context`` (e.g. ``"a quantified variable's"``,
    ``"an argument of 'p''s"``) is spliced into the error message naming
    WHERE the offending type was used.

    Raises:
        TptpParsingError: the type is ``"$o"`` (boolean may only appear as
            a PREDICATE's own overall result type -- never a variable's,
            argument's, or function-result type) or an unrecognised
            ``"$..."`` built-in.
        NotImplementedError: the type is ``"$int"``/``"$rat"``/``"$real"``
            -- TPTP's arithmetic sorts, out of scope for this TF0-only
            reader (see module docstring).
    """
    if type_str == "$i":
        return None
    if type_str == "$o":
        raise TptpParsingError(
            f"SYNTAX_ERROR: '$o' (boolean) cannot be {context} type -- only "
            "a predicate's own overall result may be $o."
        )
    if type_str in _ARITHMETIC_SORTS:
        raise NotImplementedError(
            f"TF0 reader: {context} type {type_str!r} needs TPTP's "
            "arithmetic sorts ($int/$rat/$real), which are out of scope for "
            "this TF0-only reader (see module docstring 'Scope')."
        )
    if type_str.startswith("$"):
        raise TptpParsingError(
            f"SYNTAX_ERROR: unsupported TPTP built-in type {type_str!r} as "
            f"{context} type."
        )
    return _cap(type_str)


class _TptpTransformer(Transformer):
    """Turn the Lark parse tree into the toolkit AST."""

    # --- whole-file / statements ---
    def file(self, items):
        return list(items)

    def stmt(self, items):
        keyword = str(items[0])
        if keyword == "thf":
            raise TptpParsingError(_THF_REFUSAL)
        if keyword not in ("fof", "cnf", "tff"):
            raise TptpParsingError(
                f"SYNTAX_ERROR: unsupported TPTP statement '{keyword}' "
                "(only fof, cnf, and tff are supported)."
            )
        name, role, formula = str(items[1]), str(items[2]), items[3]
        # items[4] / items[5]: the optional 4th (source) / 5th (useful_info)
        # annotation fields (None when absent -- see the grammar's
        # annotation_term rule). This reader models the statement's own
        # FORMULA, never its provenance/derivation metadata -- accepted
        # syntactically, discarded here.
        return TptpFormula(name, role, formula)

    def stmt_type(self, items):
        """A ``tff(name, type, <decl>).`` type-declaration statement.

        Returns one of :class:`_TffSortDecl` / :class:`_TffPredDecl` /
        :class:`_TffFuncDecl` — never a :class:`TptpFormula`, since a type
        declaration declares vocabulary, not a formula. Only
        :func:`parse_tff_problem` consumes these; :func:`parse_tptp` refuses
        a problem containing one (see that function). ``items[4]``/
        ``items[5]`` (the optional annotation fields) are discarded exactly
        like :meth:`stmt` discards them.
        """
        keyword, name, role, decl = str(items[0]), str(items[1]), str(items[2]), items[3]
        if keyword == "thf":
            raise TptpParsingError(_THF_REFUSAL)
        if keyword != "tff":
            raise TptpParsingError(
                f"SYNTAX_ERROR: a type declaration (role 'type') is only "
                f"valid inside a 'tff(...)' statement, got '{keyword}(...)'."
            )
        if role != "type":
            raise TptpParsingError(
                f"SYNTAX_ERROR: expected role 'type' for a TFF type "
                f"declaration, got {role!r}."
            )
        return decl

    def fof_name(self, items):
        return str(items[0])

    # --- include directives (spliced in by _resolve_includes, post-parse) ---
    def include_stmt(self, items):
        file_tok, names = items
        selection = tuple(names) if names is not None else None
        return _IncludeDirective(_functor_name(file_tok), selection)

    def name_list(self, items):
        return list(items)

    # --- connectives ---
    def iff(self, items):
        return Iff(items[0], items[1])

    def xor(self, items):
        return Xor(items[0], items[1])

    def implies(self, items):
        return Implies(items[0], items[1])

    def rev_implies(self, items):
        # TPTP  a <= b  means "a if b", i.e. b => a.
        return Implies(items[1], items[0])

    def or_(self, items):
        return Or(items[0], items[1])

    def nor(self, items):
        return Not(Or(items[0], items[1]))

    def and_(self, items):
        return And(items[0], items[1])

    def nand(self, items):
        return Not(And(items[0], items[1]))

    def neg(self, items):
        return Not(items[0])

    # --- quantifiers ---
    def forall(self, items):
        return self._quantify("∀", items[0], items[1])

    def exists(self, items):
        return self._quantify("∃", items[0], items[1])

    def _quantify(self, qtype, variables, body):
        # Each element of `variables` is either a plain Variable (untyped,
        # from a bare typed_var with no ":sort") or a (Variable, sort) pair
        # (typed_var's optional sort was present) -- see typed_var below.
        for var in reversed(variables):
            if isinstance(var, tuple):
                bound, sort = var
                body = SortedQuantifier(qtype, bound, sort, body)
            else:
                body = Quantifier(qtype, var, body)
        return body

    def varlist(self, items):
        return list(items)

    def typed_var(self, items):
        """One quantifier variable, optionally TFF-typed: ``X`` or ``X: sort``.

        Returns a bare :class:`Variable` (untyped -- matches fof/cnf's
        pre-existing behaviour exactly) when no ``: sort`` was given, or a
        ``(Variable, sort)`` pair when one was -- :meth:`_quantify` turns the
        pair into a :class:`SortedQuantifier` binder. ``$i`` resolves to
        "untyped" (a bare :class:`Variable`), matching TPTP's own "no type
        given" default; ``$o``/arithmetic sorts/``$tType`` are refused (see
        :func:`_resolve_type_str`).
        """
        if len(items) == 1:
            return Variable(str(items[0]).lower())
        var_tok, type_str = items
        sort = _resolve_type_str(type_str, context="a quantified variable's")
        var = Variable(str(var_tok).lower())
        return var if sort is None else (var, sort)

    # --- atoms ---
    def equality(self, items):
        return Atom("=", [items[0], items[1]])

    def disequality(self, items):
        return Atom("≠", [items[0], items[1]])

    def pred_app(self, items):
        return Atom(_cap(_functor_name(items[0])), items[1])

    def prop_atom(self, items):
        return Atom(_cap(_functor_name(items[0])), [])

    def dollar_atom(self, items):
        word = str(items[0])
        if word in _DOLLAR_PRED:
            return Atom(_DOLLAR_PRED[word], items[1])
        raise TptpParsingError(
            f"SYNTAX_ERROR: unsupported TPTP dollar-word predicate '{word}'."
        )

    def bool_const(self, items):
        word = str(items[0])
        if word in ("$true", "$false"):
            return Atom(word, [])
        raise TptpParsingError(
            f"SYNTAX_ERROR: unsupported TPTP dollar-word '{word}'."
        )

    # --- terms ---
    def var(self, items):
        return Variable(str(items[0]).lower())

    def constant(self, items):
        return Constant(_functor_name(items[0]))

    def number(self, items):
        return Number(_numeral_from_text(str(items[0])))

    def func_app(self, items):
        return Function(_functor_name(items[0]), items[1])

    def dollar_func_app(self, items):
        word = str(items[0])
        if word in _DOLLAR_FUNC:
            return Function(_DOLLAR_FUNC[word], items[1])
        raise TptpParsingError(
            f"SYNTAX_ERROR: unsupported TPTP dollar-word function '{word}'."
        )

    def termlist(self, items):
        return list(items)

    # --- TF0 type declarations ---
    def tff_type_decl(self, items):
        name_tok, shape_payload = items
        name = _functor_name(name_tok)
        shape, payload = shape_payload
        if shape == "sort":
            return _TffSortDecl(_cap(name))
        if shape == "nullary":
            if payload == "$o":
                return _TffPredDecl(_cap(name), ())
            return _TffFuncDecl(name, (), _resolve_type_str(payload, context="this symbol's"))
        if shape == "mapping":
            domain, result = payload
            arg_sorts = tuple(
                _resolve_type_str(t, context=f"an argument of {name!r}'s") for t in domain)
            if result == "$o":
                return _TffPredDecl(_cap(name), arg_sorts)
            return _TffFuncDecl(
                name, arg_sorts, _resolve_type_str(result, context=f"{name!r}'s result"))
        raise AssertionError(f"tff_type_decl: unreachable shape {shape!r}")  # pragma: no cover

    def tff_sort_decl(self, items):
        return ("sort", None)

    def tff_poly_decl(self, items):
        raise _Tf1PolymorphismError(_TF1_REFUSAL)

    def tff_symbol_decl(self, items):
        return ("mapping", items[0])

    def tff_nullary_decl(self, items):
        return ("nullary", items[0])

    def tff_mapping_type(self, items):
        domain, result = items
        return (domain, result)

    def domain_single(self, items):
        return (items[0],)

    def domain_prod(self, items):
        return items[0]

    def tff_xprod(self, items):
        return tuple(items)

    def plain_type(self, items):
        return _functor_name(items[0])

    def dollar_type(self, items):
        return str(items[0])


_FORMULA_PARSER = Lark(_GRAMMAR, start="formula", parser="earley")
_FILE_PARSER = Lark(_GRAMMAR, start="file", parser="earley")
# The LALR(1) twins, tried first -- see "Two parsers" in the module
# docstring. Construction costs +0.06 s at import for the pair (measured),
# against 45x on every non-trivial parse. lark raises GrammarError on any
# shift/reduce or reduce/reduce collision, so these two lines are themselves
# the assertion that the grammar above is LALR(1).
_FORMULA_PARSER_FAST = Lark(_GRAMMAR, start="formula", parser="lalr")
_FILE_PARSER_FAST = Lark(_GRAMMAR, start="file", parser="lalr")
_TRANSFORMER = _TptpTransformer()

#: A DOL ``logic <Name>.<Sublogic>`` line is what HETS puts in front of every
#: ``GET /theory`` rendering (``logic TPTP.FOF``, ``logic CASL.SulFOL=``,
#: ``logic OWL.NP-sROIQx-D|Literal|...``). It is not TPTP, and neither is the
#: CASL ``%{ ... }%`` block that follows it -- TPTP's only comment forms are
#: ``%`` to end-of-line and ``/* ... */``, both already in the grammar's
#: %ignore lines above. Detected here only so the refusal can NAME it and
#: point at the stripper; the grammar is deliberately NOT widened, because a
#: reader that treated ``%{ ... }%`` as a comment would accept a CASL theory,
#: ignore its whole body and return an EMPTY formula list -- a silent empty
#: answer to a wrong-translation request.
#:
#: The WHOLE first line must be ``logic`` plus ONE DOL logic reference
#: (:data:`_HETS_LOGIC_REFERENCE`): a logic NAME, which is an identifier
#: (``TPTP``, ``CASL``, ``SoftFOL``, ``HasCASL``, ``OWL`` ...), optionally
#: followed by ``.`` and a free-form sublogic. The first character of the word
#: after ``logic`` is therefore a LETTER, never an operator, so the guard
#: cannot fire on a legitimate formula that happens to use ``logic`` as a
#: predicate or constant name: ``logic & p``, ``logic &p``, ``logic|q``,
#: ``logic =a``, ``logic != b``, ``logic <=> q``, ``logic(X)`` all keep parsing
#: exactly as before. (An earlier test, ``logic`` plus any whitespace-free
#: word, refused ``logic &p`` and ``logic =a`` -- valid formulas that parsed
#: before the pointer existed.)
#:
#: On top of the shape, :func:`_parse` consults it only AFTER both parsers have
#: failed, so by construction no text that parses is ever refused here; the
#: shape is what keeps the pointer from naming the wrong cause for a text that
#: does not.
_HETS_LOGIC_REFERENCE = r"[A-Za-z][A-Za-z0-9_]*(?:\.\S*)?"
_HETS_THEORY_HEADER = re.compile(r"logic[ \t]+" + _HETS_LOGIC_REFERENCE + r"\Z")


def _refuse_hets_theory_header(text: str) -> None:
    """Refuse a HETS ``/theory`` rendering by name. Called by :func:`_parse`
    once the text has FAILED to parse, never before: a text that parses is not
    a Hets rendering, whatever its first line looks like."""
    stripped = text.lstrip()
    first_line = stripped.split("\n", 1)[0].rstrip()
    if not _HETS_THEORY_HEADER.fullmatch(first_line):
        return
    raise TptpParsingError(
        "SYNTAX_ERROR: this is not a TPTP problem but a Hets theory "
        f"rendering (it begins {first_line!r}; a '%{{ ... }}%' block is CASL "
        "comment syntax, not TPTP). Strip the header first with "
        "unicode_fol_kit.hets.strip_hets_theory_header(text), or fetch it "
        "already stripped with HetsClient.theory_tptp().")


#: What carries no syntax of its own in TPTP text: a single-quoted atom (its escapes as in the
#: grammar's ``SQ``), a ``%`` comment to the end of the line, a ``/* ... */`` block comment.
_QUOTED_OR_COMMENT = re.compile(r"'(?:\\.|[^'\\])*'|%[^\r\n]*|/\*.*?\*/", re.DOTALL)

#: A ``thf`` statement: the keyword opens the text or follows the ``.`` that ends the
#: statement before it. (A ``.`` elsewhere is the point of a numeral, and a digit follows it.)
_THF_STATEMENT = re.compile(r"(?:\A|\.)\s*thf\s*\(")

#: TF1 syntax: the type binder ``!>``, and a quantifier variable whose type is ``$tType``
#: (``![A: $tType]``). TF0 uses ``$tType`` only in ``name: $tType``, a lower-case name.
_TF1_SYNTAX = re.compile(r"!>|[\[,]\s*[A-Z][A-Za-z0-9_]*\s*:\s*\$tType")


def _refuse_out_of_scope_syntax(text: str, *, problem: bool) -> None:
    """Refuse THF and TF1 by name before the first-order grammar is tried.

    A THF statement has a body the first-order grammar cannot read (``p @ A``, a type
    declaration ``p : $i > $o``), and TF1 writes a type variable with ``!>`` or with a
    quantifier over ``$tType``; each ended in a syntax error that does not say what the
    text is. The statement's KIND and the binder are found in the text with comments and
    quoted atoms taken out, so neither a comment nor a quoted atom is ever refused, and
    the check does not depend on the body parsing.

    Args:
        text: the text about to be parsed.
        problem: whether ``text`` is a whole problem (statements). A bare formula has no
            statement keyword: ``thf(a)`` there is the atom ``Thf(a)``.

    Raises:
        TptpParsingError: ``text`` has a ``thf`` statement.
        _Tf1PolymorphismError: ``text`` uses ``!>`` or a ``$tType`` quantifier variable
            (a :class:`TptpParsingError` and a :class:`NotImplementedError`).
    """
    if "thf" not in text and "!>" not in text and "$tType" not in text:
        return
    code = _QUOTED_OR_COMMENT.sub(" ", text)
    if problem and _THF_STATEMENT.search(code):
        raise TptpParsingError(_THF_REFUSAL)
    if _TF1_SYNTAX.search(code):
        raise _Tf1PolymorphismError(_TF1_REFUSAL)


#: Parse-tree nodes whose ``VAR`` tokens are not variables of a formula: the
#: discarded 4th/5th annotation fields of a statement (an opaque term may carry
#: one), the statement's name, and the declarations that are not formulas.
_NOT_A_FORMULA = frozenset({
    "annotation_term", "annotation_term_list", "fof_name", "include_stmt",
    "name_list", "stmt_type",
})


def _refuse_merged_variables(tree) -> None:
    """Refuse, by name, a formula in which lower-casing turns two TPTP variables
    into one.

    :class:`_TptpTransformer` reads a TPTP variable as its lower-cased kit
    :class:`Variable`, and a TPTP variable is case-sensitive: ``Xa`` and ``XA``
    are two variables that both become ``xa``. Where that merges them the formula
    is read as a DIFFERENT formula (``![Xa, XA]: p(Xa, XA)`` as ``∀xa ∀xa
    P(xa, xa)``), and nothing said so. A kit variable here is a NAME, resolved to
    the nearest enclosing binder of that name; TPTP resolves an occurrence to the
    nearest enclosing binder of the EXACT spelling, or leaves it free. The two
    readings of an occurrence therefore differ exactly when

    * the nearest binder of the lower-cased name is not the nearest binder of the
      exact spelling (one variable is captured by another's quantifier, or a free
      variable by a binder), or
    * two spellings of one lower-cased name occur free in the same formula.

    Those are refused, naming both variables. Anything else reads as it always
    did, byte for byte: ``(![Xa]: p(Xa)) & (![XA]: q(XA))`` has two binders that
    never meet, so the kit's ``(∀xa P(xa)) ∧ (∀xa Q(xa))`` is the same formula.
    Each statement of a problem is checked on its own. No renaming is invented
    here: a formula that needs one is refused and the caller renames.
    """
    if tree.data == "file":
        roots = [child for child in tree.children
                 if isinstance(child, Tree) and child.data == "stmt"]
    else:
        roots = [tree]
    for root in roots:
        free: Dict[str, str] = {}          # lower-cased name -> first free spelling
        # (node, binders); binders is None or (spelling, enclosing binders)
        stack: List[Tuple[Any, Any]] = [(root, None)]
        while stack:
            node, binders = stack.pop()
            if not isinstance(node, Tree) or node.data in _NOT_A_FORMULA:
                continue
            if node.data == "var":
                _check_variable_occurrence(str(node.children[0]), binders, free)
            elif node.data in ("forall", "exists"):
                varlist, body = node.children
                for typed_var in varlist.children:
                    binders = (str(typed_var.children[0]), binders)
                stack.append((body, binders))
            else:
                for child in reversed(node.children):
                    stack.append((child, binders))


def _check_variable_occurrence(spelling: str, binders: Any, free: Dict[str, str]) -> None:
    """One occurrence of the TPTP variable ``spelling`` under ``binders`` — see
    :func:`_refuse_merged_variables`."""
    lowered = spelling.lower()
    exact = by_name = None
    scope = binders
    while scope is not None and (exact is None or by_name is None):
        if exact is None and scope[0] == spelling:
            exact = scope
        if by_name is None and scope[0].lower() == lowered:
            by_name = scope
        scope = scope[1]
    if by_name is not None and by_name is not exact:
        _refuse_variable_pair(by_name[0], spelling, lowered)
    if by_name is None:
        first = free.setdefault(lowered, spelling)
        if first != spelling:
            _refuse_variable_pair(first, spelling, lowered)


def _refuse_variable_pair(one: str, other: str, lowered: str) -> None:
    raise TptpParsingError(
        f"SYNTAX_ERROR: the TPTP variables {one!r} and {other!r} are different "
        f"variables that differ only by letter case, and this reader turns a "
        f"TPTP variable into a kit variable by lower-casing it: both would "
        f"become {lowered!r}, and the formula would be read with one variable "
        f"where TPTP has two. Rename one of them so that they differ by more "
        f"than letter case.")


def _parse(text: str, parser: Lark, what: str, *, fast: Optional[Lark] = None):
    """Parse + transform with unified error handling (unwrapping lark's VisitError).

    ``fast`` is the LALR(1) twin of ``parser``; it is tried first and Earley
    takes over on ``UnexpectedInput``, so no text that parsed before stops
    parsing and every syntax-error message is Earley's, unchanged. Only the
    PARSE is retried — see "Two parsers" in the module docstring.

    A HETS theory rendering is named only once BOTH parsers have refused the
    text (see :func:`_refuse_hets_theory_header`): the pointer replaces a syntax
    error with a better one, and can never turn a text that parses into a
    refusal.
    """
    _refuse_out_of_scope_syntax(text, problem=what == "problem")
    tree = None
    if fast is not None:
        try:
            tree = fast.parse(text)
        except UnexpectedInput:
            tree = None
    if tree is None:
        try:
            tree = parser.parse(text)
        except TptpParsingError:
            raise
        except Exception as exc:
            _refuse_hets_theory_header(text)
            raise TptpParsingError(
                f"SYNTAX_ERROR: could not parse TPTP {what}: {exc}")
    _refuse_merged_variables(tree)
    try:
        return _TRANSFORMER.transform(tree)
    except VisitError as exc:
        original = exc.orig_exc
        # NotImplementedError alongside ParsingError: the TF0-scope refusals
        # (TF1 polymorphism, $int/$rat/$real -- see _resolve_type_str /
        # tff_poly_decl) are meant to surface as NotImplementedError, not get
        # folded into a generic SYNTAX_ERROR string, so its type must survive
        # this unwrap exactly like ParsingError's already does.
        if isinstance(original, (ParsingError, NotImplementedError)):
            raise original
        raise TptpParsingError(f"SYNTAX_ERROR: in TPTP {what}: {original}")


# =============================================================================
# Include resolution — shared by parse_tptp / parse_tptp_problem /
# parse_tff_problem and their load_* siblings (see the module docstring's
# "Includes" section).
# =============================================================================

def _locate_include(file_name: str, base_dir: str, search_paths) -> str:
    """Resolve one ``include(file_name)`` directive to an existing file path.

    Tried in order: (1) ``base_dir/file_name`` (relative to the file
    containing the include directive itself), (2) each root in
    ``search_paths`` joined with ``file_name``, in order, then (3)
    ``os.environ["TPTP"]`` joined with ``file_name``, if that environment
    variable is set — the de facto TPTP-library convention (an include like
    ``include('Axioms/SET001+0.ax')`` is root-relative, not relative to
    whatever problem file referred to it).

    Raises:
        TptpParsingError: none of the tried candidates exist — names the
            include's path and every candidate location tried.
    """
    roots = [base_dir, *search_paths]
    tptp_env = os.environ.get("TPTP")
    if tptp_env:
        roots.append(tptp_env)
    tried = []
    for root in roots:
        candidate = os.path.join(root, file_name)
        tried.append(candidate)
        if os.path.isfile(candidate):
            return candidate
    raise TptpParsingError(
        f"SYNTAX_ERROR: include({file_name!r}) could not be found -- tried: "
        + ", ".join(repr(t) for t in tried) + "."
    )


def _apply_selection(items: list, selection: Tuple[str, ...], file_name: str) -> list:
    """Filter an included file's already-resolved ``items`` down to
    ``selection``, by each :class:`TptpFormula`'s own TPTP statement name,
    in the order ``selection`` names them (not the file's own order).

    Raises:
        TptpParsingError: ``items`` contains anything other than
            :class:`TptpFormula` records (a TF0 type declaration — its own
            statement name is not tracked separately from the symbol it
            declares, see :class:`_TffSortDecl`/:class:`_TffPredDecl`/
            :class:`_TffFuncDecl`, so a selection list cannot be matched
            against it), or ``selection`` names something absent from the
            included file.
    """
    non_formula = [item for item in items if not isinstance(item, TptpFormula)]
    if non_formula:
        raise TptpParsingError(
            f"SYNTAX_ERROR: include({file_name!r}, [...]) cannot use a "
            "selection list on a file that declares TFF vocabulary (a "
            "'tff(name, type, ...).' statement) -- its own statement name "
            "is not tracked separately from the symbol it declares, so a "
            "selection list cannot be matched against it; include the "
            "whole file (drop the selection list) instead."
        )
    by_name = {}
    for formula in items:
        by_name.setdefault(formula.name, formula)
    selected = []
    for name in selection:
        if name not in by_name:
            raise TptpParsingError(
                f"SYNTAX_ERROR: include({file_name!r}, [...]) selects "
                f"{name!r}, which is not a formula name in {file_name!r} "
                f"(available: {sorted(by_name)!r})."
            )
        selected.append(by_name[name])
    return selected


def _resolve_includes(items: list, base_dir: Optional[str], search_paths,
                       chain: Tuple[Tuple[str, str], ...]) -> list:
    """Recursively splice every :class:`_IncludeDirective` in ``items`` with
    the (itself include-resolved) statements of the file it names, in place
    — preserving surrounding statement order.

    ``chain`` is the tuple of ``(name_as_written, real_path)`` pairs for
    every include currently "open" (the stack of files that led here),
    used both to detect a cycle (a repeated ``real_path``) and to name the
    full trail in the resulting error. :func:`_load_and_resolve` seeds it
    with the loaded file's own path; a bare-text :func:`parse_tptp` call
    starts it empty.

    Raises:
        TptpParsingError: an include is encountered with ``base_dir=None``
            (no including file's directory is known — see the module
            docstring), the named file cannot be found (see
            :func:`_locate_include`), or the chain cycles back to a file
            already open.
    """
    resolved = []
    for item in items:
        if not isinstance(item, _IncludeDirective):
            resolved.append(item)
            continue
        if base_dir is None:
            raise TptpParsingError(
                f"SYNTAX_ERROR: include({item.file_name!r}) cannot be "
                "resolved -- no including file's directory is known "
                "(base_dir=None, the default, for bare text); read the "
                "problem via load_tptp / load_tptp_problem / "
                "load_tff_problem, or pass base_dir explicitly."
            )
        path = _locate_include(item.file_name, base_dir, search_paths)
        real = os.path.realpath(path)
        if any(real == seen_real for _seen_name, seen_real in chain):
            trail = " -> ".join(repr(name) for name, _real in chain)
            raise TptpParsingError(
                f"SYNTAX_ERROR: circular include: {trail} -> "
                f"{item.file_name!r}."
            )
        with open(path, "r", encoding="utf-8") as handle:
            sub_text = handle.read()
        sub_items = _parse(sub_text, _FILE_PARSER, "problem",
                           fast=_FILE_PARSER_FAST)
        sub_resolved = _resolve_includes(
            sub_items, os.path.dirname(path), search_paths,
            chain + ((item.file_name, real),))
        if item.selection is not None:
            sub_resolved = _apply_selection(sub_resolved, item.selection, item.file_name)
        resolved.extend(sub_resolved)
    return resolved


def _finalize_formulas(items: list) -> list:
    """Confirm every item in an include-resolved ``items`` list is a
    :class:`TptpFormula` — the shared tail of :func:`parse_tptp` /
    :func:`load_tptp` / :func:`parse_tptp_problem` / :func:`load_tptp_problem`,
    none of which can represent a TF0 type declaration."""
    for item in items:
        if not isinstance(item, TptpFormula):
            raise TptpParsingError(
                "SYNTAX_ERROR: this problem contains a TFF type declaration "
                "('tff(name, type, ...).'), which parse_tptp/load_tptp cannot "
                "represent as a TptpFormula — use parse_tff_problem() instead, "
                "which returns the declared Signature alongside the formulas."
            )
    return items


def _load_and_resolve(path: str, search_paths) -> Tuple[list, str]:
    """Read ``path``, parse it, and resolve its includes with the cycle
    ``chain`` (see :func:`_resolve_includes`) seeded by ``path`` itself —
    so a chain that loops back to the very file
    :func:`load_tptp`/:func:`load_tptp_problem`/:func:`load_tff_problem`
    started from is caught, not only a cycle confined to files reached
    purely via nested includes.

    Returns:
        ``(items, text)`` — ``items`` fully include-resolved (no
        :class:`_IncludeDirective` survives), ``text`` the loaded file's own
        raw contents (for :func:`load_tptp_problem`'s header scan, which
        reads only the top-level file's ``%`` comments, never an included
        file's).
    """
    real_path = os.path.realpath(path)
    with open(path, "r", encoding="utf-8") as handle:
        text = handle.read()
    items = _parse(text, _FILE_PARSER, "problem", fast=_FILE_PARSER_FAST)
    items = _resolve_includes(
        items, os.path.dirname(path), search_paths, ((path, real_path),))
    return items, text


def parse_tptp_formula(text: str) -> Node:
    """Parse a single bare TPTP FOF/CNF formula (no ``fof(...)`` wrapper) into a Node.

    Args:
        text: a TPTP formula, e.g. ``"![X]: (p(X) => q(X))"``.

    Returns:
        The formula as a toolkit :class:`Node`.

    Raises:
        ParsingError: if ``text`` is not a well-formed TPTP formula.
    """
    return _parse(text, _FORMULA_PARSER, "formula",
                  fast=_FORMULA_PARSER_FAST)


def parse_tptp(text: str, *, base_dir: Optional[str] = None, search_paths=()) -> list:
    """Parse a whole TPTP problem into a list of :class:`TptpFormula` records.

    Args:
        text: the contents of a TPTP problem — one or more ``fof(...)`` /
            ``cnf(...)`` / ``tff(...)`` statements, and/or ``include(...)``
            directives (``%`` line comments and ``/* */`` block comments are
            ignored). A ``tff`` AXIOM/CONJECTURE/... statement is accepted
            exactly like ``fof`` (its typed quantifiers build
            :class:`~unicode_fol_kit.fol.nodes.SortedQuantifier`), but a
            ``tff(name, type, ...).`` TYPE DECLARATION is not (see
            ``Raises`` below).
        base_dir: the directory an ``include(...)`` in ``text`` resolves
            relative to first. ``None`` (the default) means "no including
            file's directory is known" — an ``include`` then raises (see
            ``Raises``); :func:`load_tptp` sets this to the loaded file's
            own directory automatically. See the module docstring's
            "Includes" section for the full resolution order.
        search_paths: further roots tried, in order, after ``base_dir``,
            for an ``include`` not found relative to it (plus
            ``os.environ["TPTP"]``, if set) — see "Includes".

    Returns:
        A list of :class:`TptpFormula` ``(name, role, formula)`` in source
        order, with every ``include`` spliced in at its own position.

    Raises:
        ParsingError: if the text is not a well-formed TPTP problem, if it
            contains a ``tff(name, type, ...).`` type declaration — this
            function has no ``TptpFormula`` shape to return a type
            declaration as; use :func:`parse_tff_problem` instead, which
            returns the declared :class:`~unicode_fol_kit.fol.signature
            .Signature` alongside the formulas — or if an ``include``
            cannot be resolved (``base_dir=None``, a missing file, or a
            circular chain; see "Includes").
    """
    items = _parse(text, _FILE_PARSER, "problem", fast=_FILE_PARSER_FAST)
    items = _resolve_includes(items, base_dir, search_paths, ())
    return _finalize_formulas(items)


def load_tptp(path: str, *, search_paths=()) -> list:
    """Read a TPTP problem file and :func:`parse_tptp` its contents.

    Args:
        path: path to a ``.p`` / ``.tptp`` file. Every ``include(...)`` it
            contains resolves relative to ``path``'s own directory first
            (then ``search_paths`` — see :func:`parse_tptp`), and a cycle
            back to ``path`` itself is caught, not only one confined to
            files reached purely via nested includes.
        search_paths: see :func:`parse_tptp`.

    Returns:
        A list of :class:`TptpFormula` records.
    """
    items, _text = _load_and_resolve(path, search_paths)
    return _finalize_formulas(items)


def _conflict(kind: str, name: str, existing, new) -> TptpParsingError:
    return TptpParsingError(
        f"SYNTAX_ERROR: {kind} '{name}' is declared more than once with "
        f"different types ({existing!r} vs {new!r})."
    )


def _build_signature_and_formulas(items: list) -> Tuple[Signature, List[TptpFormula]]:
    """The shared, include-resolution-independent guts of
    :func:`parse_tff_problem` / :func:`load_tff_problem`: split an already
    include-resolved ``items`` list into a
    :class:`~unicode_fol_kit.fol.signature.Signature` and promoted formulas.
    See :func:`parse_tff_problem` for the full contract."""
    decls = [i for i in items if not isinstance(i, TptpFormula)]
    formulas = [i for i in items if isinstance(i, TptpFormula)]

    sorts: set = set()
    predicates: Dict[str, PredicateDecl] = {}
    functions: Dict[str, FunctionDecl] = {}
    constants: Dict[str, ConstantDecl] = {}
    const_sorts: Dict[str, str] = {}

    for d in decls:
        if isinstance(d, _TffSortDecl):
            sorts.add(d.name)
        elif isinstance(d, _TffPredDecl):
            new_decl = PredicateDecl(d.name, len(d.arg_sorts), d.arg_sorts)
            existing = predicates.get(d.name)
            if existing is not None and existing != new_decl:
                raise _conflict("predicate", d.name, existing, new_decl)
            predicates[d.name] = new_decl
        elif isinstance(d, _TffFuncDecl):
            if not d.arg_sorts:
                new_const = ConstantDecl(d.name, d.result_sort)
                existing_const = constants.get(d.name)
                if existing_const is not None and existing_const != new_const:
                    raise _conflict("constant", d.name, existing_const, new_const)
                constants[d.name] = new_const
                if d.result_sort is not None:
                    const_sorts[d.name] = d.result_sort
            else:
                new_func = FunctionDecl(d.name, len(d.arg_sorts), d.arg_sorts, d.result_sort)
                existing_func = functions.get(d.name)
                if existing_func is not None and existing_func != new_func:
                    raise _conflict("function", d.name, existing_func, new_func)
                functions[d.name] = new_func
        else:  # pragma: no cover -- file/stmt_type can only produce the three above
            raise AssertionError(f"parse_tff_problem: unreachable decl type {type(d).__name__!r}")

    for decl in predicates.values():
        sorts.update(s for s in decl.arg_sorts if s is not None)
    for decl in functions.values():
        sorts.update(s for s in decl.arg_sorts if s is not None)
        if decl.result_sort is not None:
            sorts.add(decl.result_sort)
    for decl in constants.values():
        if decl.sort is not None:
            sorts.add(decl.sort)
    for f in formulas:
        for n in f.formula.walk():
            if isinstance(n, SortedQuantifier):
                sorts.add(n.sort)

    signature = Signature(predicates=predicates, functions=functions,
                          constants=constants, sorts=frozenset(sorts))

    def _promote(node: Node) -> Node:
        node = node.map_children(_promote)
        if isinstance(node, Constant) and node.name in const_sorts:
            return SortedConstant(node.name, const_sorts[node.name])
        return node

    promoted = [TptpFormula(f.name, f.role, _promote(f.formula)) for f in formulas]
    return signature, promoted


def parse_tff_problem(
    text: str, *, base_dir: Optional[str] = None, search_paths=()
) -> Tuple[Signature, List[TptpFormula]]:
    """Parse a whole TF0 (monomorphic typed) TPTP ``tff`` problem.

    The typed sibling of :func:`parse_tptp`: reads every ``tff(name, type,
    ...).`` TYPE DECLARATION into a :class:`~unicode_fol_kit.fol.signature
    .Signature` (one entry per declared sort/predicate/function/constant —
    an argument or result type of ``$i`` resolves to ``None`` — "no concrete
    sort", TPTP's own default — everything else to the corresponding
    capitalised kit-level sort name), and every other statement
    (``axiom``/``conjecture``/...) into a :class:`TptpFormula` exactly like
    :func:`parse_tptp` does, EXTRA step: any bare
    :class:`~unicode_fol_kit.fol.nodes.Constant` occurrence in a formula
    whose name was declared with a concrete sort is promoted to a
    :class:`~unicode_fol_kit.fol.nodes.SortedConstant` — a TFF formula BODY
    carries no inline sort annotation for a constant (only a bound variable
    does, via ``X: sort``), so this is the only place that information can
    be recovered and reattached to the AST.

    ``include(...)`` directives are resolved exactly like :func:`parse_tptp`
    (splicing recursively, ``base_dir``/``search_paths`` work the same way —
    see the module docstring's "Includes" section) — WITH ONE RESTRICTION: a
    ``include('path', [name1, ...])`` selection list can only be applied to
    an included file that is itself pure ``fof``/``cnf``/``tff`` FORMULAS,
    never one that also declares TFF vocabulary (a ``tff(name, type,
    ...).`` statement) — a type declaration's own statement name is not
    tracked separately from the symbol it declares (see
    :class:`_TffSortDecl`/:class:`_TffPredDecl`/:class:`_TffFuncDecl`), so a
    selection list cannot be matched against it; that combination raises
    (see ``Raises``). A *whole-file* include (no selection list) always
    works, decls and formulas alike.

    Args:
        text: the contents of a TF0 TPTP problem — a mix of
            ``tff(name, type, Sym: Type).`` declarations,
            ``tff(name, axiom|conjecture|..., <formula>).`` statements, and
            ``include(...)`` directives (``fof``/``cnf`` statements may also
            appear; their formulas are included unchanged, exactly as
            :func:`parse_tptp` would read them).
        base_dir: see :func:`parse_tptp`; :func:`load_tff_problem` sets this
            automatically.
        search_paths: see :func:`parse_tptp`.

    Returns:
        ``(signature, formulas)`` — ``formulas`` in source order (type
        declarations are consumed into ``signature``, not returned as
        formulas). ``signature.sorts`` also includes every sort named by a
        :class:`~unicode_fol_kit.fol.nodes.SortedQuantifier` occurring in
        the formulas even if that sort was never separately declared with
        its own ``$tType`` statement (real TF0 files always do, but this
        keeps the reader lenient rather than dropping information).

    Raises:
        ParsingError: the text is not a well-formed TPTP problem, the same
            symbol is declared twice with two DIFFERENT types, or an
            ``include`` cannot be resolved (unresolvable path, circular
            chain, or a selection list combined with TFF vocabulary, all as
            described above).
        NotImplementedError: a type declaration uses TF1 polymorphism
            (``!> [...] : ...``) or one of TPTP's arithmetic sorts
            (``$int``/``$rat``/``$real``) — see :func:`_resolve_type_str` /
            ``_TptpTransformer.tff_poly_decl``.
    """
    items = _parse(text, _FILE_PARSER, "problem", fast=_FILE_PARSER_FAST)
    items = _resolve_includes(items, base_dir, search_paths, ())
    return _build_signature_and_formulas(items)


def load_tff_problem(path: str, *, search_paths=()) -> Tuple[Signature, List[TptpFormula]]:
    """Read a TF0 TPTP problem file and :func:`parse_tff_problem` its
    contents, resolving ``include(...)`` directives exactly like
    :func:`load_tptp` (``base_dir`` set to ``path``'s own directory, cycle
    detection seeded with ``path`` itself — see :func:`load_tptp`)."""
    items, _text = _load_and_resolve(path, search_paths)
    return _build_signature_and_formulas(items)


# ---------------------------------------------------------------------------
# TPTP header metadata
# ---------------------------------------------------------------------------
#
# TPTP problem files carry a standardised block of '%' comment lines near the top
# recording the file's provenance and, for problems drawn from the TPTP library,
# its ground-truth verdict and empirical difficulty rating, e.g.:
#
#     % File     : PUZ001-1 : TPTP v8.1.0. Released v1.0.0.
#     % Domain   : Puzzles
#     % Problem  : Dreadbury Mansion
#     % Status   : Theorem
#     % Rating   : 0.43 v8.1.0, 0.36 v7.4.0
#
# _GRAMMAR above ``%``-ignores every comment, so none of this ever reaches the Lark
# parser or the TptpFormula records built from it. The functions below recover it by
# a separate, deterministic line scan of the *raw* text, run independently of (and
# before) the grammar-based formula parse, then hand formula parsing off unchanged to
# :func:`parse_tptp` — this extends the module's contract rather than altering it (see
# the regression tests pinning parse_tptp / parse_tptp_formula / load_tptp / TptpFormula
# unchanged, in tests/test_tptp_header.py).

# A header field line: optional leading whitespace, '%', optional whitespace, one of
# the five recognised TPTP field names (matched case-sensitively, per the TPTP
# standard — a lowercase "% status : ..." line is not a field line), optional
# whitespace, ':', optional whitespace, then the rest of the line as the raw value.
_HEADER_FIELD_RE = re.compile(
    r"^\s*%\s*(File|Domain|Problem|Status|Rating)\s*:\s*(.*)$"
)
# The first float-looking token anywhere in a Rating value, e.g. "0.43" out of
# "0.43 v8.1.0, 0.36 v7.4.0" (a version tag like "v8.1.0" is not itself a match
# candidate since it lacks a leading digit, but even if it were, "0.43" still wins
# because re.search returns the leftmost match and it appears first in the string).
_RATING_RE = re.compile(r"[-+]?[0-9]+\.[0-9]+")


@dataclass(frozen=True)
class TptpHeader:
    """Metadata recovered from a TPTP problem file's ``%`` comment header.

    ``status`` / ``rating`` / ``domain`` / ``problem`` / ``file`` are ``None`` when
    the corresponding ``% <Field> : ...`` line is absent (or, for ``status``/
    ``rating``, present but unparseable — see :func:`_parse_tptp_header`).
    ``comments`` always holds *every* raw ``%`` line verbatim (stripped only of its
    trailing newline), in source order, so nothing is lost even for header lines this
    reader does not specifically interpret (``% Version``, ``% Refs``, banner lines
    of dashes, ...).
    """

    status: Optional[str]
    rating: Optional[float]
    domain: Optional[str]
    problem: Optional[str]
    file: Optional[str]
    comments: Tuple[str, ...]


@dataclass(frozen=True)
class TptpProblem:
    """A whole TPTP problem: its parsed ``formulas`` plus the recovered ``header``."""

    formulas: Tuple[TptpFormula, ...]
    header: TptpHeader


def _parse_tptp_header(text: str) -> TptpHeader:
    """Scan raw TPTP text for its ``%`` header block, independent of the grammar.

    Every line whose first non-whitespace character is ``%`` is collected verbatim
    (trailing newline stripped) into ``comments``, in source order. Among those, a
    line matching :data:`_HEADER_FIELD_RE` (``% <Field> : <value>``, field names
    matched case-sensitively, whitespace around ``%``/the field name/``:``
    unconstrained) populates the matching :class:`TptpHeader` attribute — the
    *first* occurrence of each field wins; later repeats of the same field are still
    recorded in ``comments`` but do not overwrite it.

    Field values are interpreted as follows:

    - ``Status``: the first whitespace-delimited token of the value (e.g.
      ``"Theorem"`` out of ``"Theorem"``, or ``"CounterSatisfiable"``), kept as a
      plain string — not validated against a fixed vocabulary. ``None`` if the value
      has no token (e.g. it is empty).
    - ``Rating``: the first float literal found anywhere in the value (e.g. ``0.43``
      out of ``"0.43 v8.1.0, 0.36 v7.4.0"``); ``None`` if none is found (e.g. the
      value is ``"?"``).
    - ``File`` / ``Domain`` / ``Problem``: the value, whitespace-trimmed, verbatim
      (further ``:`` characters inside the value, e.g. a ``File`` value's own
      ``name : version`` sub-structure, are kept as literal text).

    Args:
        text: the raw contents of a TPTP problem file (or any TPTP text).

    Returns:
        A :class:`TptpHeader`; every field is ``None`` and ``comments`` is ``()`` if
        the text has no ``%`` lines at all.
    """
    comments = []
    fields = {}
    for line in text.splitlines():
        if not line.lstrip().startswith("%"):
            continue
        comments.append(line)
        match = _HEADER_FIELD_RE.match(line)
        if not match:
            continue
        field, value = match.group(1), match.group(2)
        if field not in fields:
            fields[field] = value

    status_raw = fields.get("Status")
    status_tokens = status_raw.split() if status_raw is not None else []
    status = status_tokens[0] if status_tokens else None

    rating_raw = fields.get("Rating")
    rating_match = _RATING_RE.search(rating_raw) if rating_raw is not None else None
    rating = float(rating_match.group(0)) if rating_match else None

    domain = fields.get("Domain")
    problem = fields.get("Problem")
    file_ = fields.get("File")

    return TptpHeader(
        status=status,
        rating=rating,
        domain=domain.strip() if domain is not None else None,
        problem=problem.strip() if problem is not None else None,
        file=file_.strip() if file_ is not None else None,
        comments=tuple(comments),
    )


def parse_tptp_problem(
    text: str, *, base_dir: Optional[str] = None, search_paths=()
) -> TptpProblem:
    """Parse a whole TPTP problem into its formulas *and* its header metadata.

    Combines :func:`parse_tptp` (formula parsing, delegated to unchanged) with an
    independent raw-text scan for the standard ``%`` header block (see
    :func:`_parse_tptp_header`) — the two do not interact, so ``formulas`` here is
    exactly what :func:`parse_tptp` returns for the same ``text``/``base_dir``/
    ``search_paths`` (same order, same :class:`TptpFormula` records — every
    ``include`` spliced in), just wrapped in a tuple alongside the header.
    The header scan itself only ever reads ``text``'s OWN ``%`` lines, never
    an included file's.

    Args:
        text: the contents of a TPTP problem file.
        base_dir: see :func:`parse_tptp`; :func:`load_tptp_problem` sets
            this automatically.
        search_paths: see :func:`parse_tptp`.

    Returns:
        A :class:`TptpProblem` with ``formulas`` (in source order) and ``header``.

    Raises:
        ParsingError: if the text is not a well-formed TPTP problem, or an
            ``include`` cannot be resolved (same conditions as
            :func:`parse_tptp`; the header scan alone never raises).
    """
    return TptpProblem(
        formulas=tuple(parse_tptp(text, base_dir=base_dir, search_paths=search_paths)),
        header=_parse_tptp_header(text),
    )


def load_tptp_problem(path: str, *, search_paths=()) -> TptpProblem:
    """Read a TPTP problem file and :func:`parse_tptp_problem` its contents.

    Mirrors :func:`load_tptp`'s file handling (whole-file read, UTF-8,
    ``base_dir``/cycle-chain seeded from ``path`` itself — see
    :func:`load_tptp`).

    Args:
        path: path to a ``.p`` / ``.tptp`` file.
        search_paths: see :func:`parse_tptp`.

    Returns:
        A :class:`TptpProblem`.
    """
    items, text = _load_and_resolve(path, search_paths)
    return TptpProblem(
        formulas=tuple(_finalize_formulas(items)),
        header=_parse_tptp_header(text),
    )
