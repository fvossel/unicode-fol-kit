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
are imported as opaque nullary atoms (the toolkit has no boolean-constant node).

Single-quoted atoms (``'http___example_org_Thing'``) — the form OWL→FOL translators
emit for IRIs — are accepted as functor / predicate / constant names: the quotes are
stripped and the ``\\'`` / ``\\\\`` escapes unescaped. The resulting names may contain
characters that are not legal MSFLParser tokens, so call
:func:`unicode_fol_kit.fol.sanitize_names` before re-parsing the rendered Unicode.

Scope: the first-order ``fof`` fragment and ``cnf`` clauses. Typed (``tff``/``thf``)
formulas, ``include`` directives, and the optional 4th/5th annotation fields of a
statement are out of scope.
"""

import re
from dataclasses import dataclass
from typing import Optional, Tuple

from lark import Lark, Transformer
from lark.exceptions import VisitError

from .nodes import (
    Node, Variable, Constant, Number, Function,
    Atom, Not, And, Or, Xor, Implies, Iff, Quantifier,
)
from .naming import ParsingError


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


_GRAMMAR = r"""
file: stmt+
stmt: LOWER "(" fof_name "," LOWER "," formula ")" "."
fof_name: LOWER | NUMBER

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

varlist: VAR ("," VAR)*

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

VAR: /[A-Z][A-Za-z0-9_]*/
LOWER: /[a-z][A-Za-z0-9_]*/
SQ: /'(\\.|[^'\\])*'/
DOLLARWORD: /\$[a-z_]+/
NUMBER: /-?[0-9]+(\.[0-9]+)?/

%import common.WS
%ignore WS
%ignore /%[^\n]*/
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


class _TptpTransformer(Transformer):
    """Turn the Lark parse tree into the toolkit AST."""

    # --- whole-file / statements ---
    def file(self, items):
        return list(items)

    def stmt(self, items):
        keyword = str(items[0])
        if keyword not in ("fof", "cnf"):
            raise TptpParsingError(
                f"SYNTAX_ERROR: unsupported TPTP statement '{keyword}' "
                "(only fof and cnf are supported)."
            )
        name, role, formula = str(items[1]), str(items[2]), items[3]
        return TptpFormula(name, role, formula)

    def fof_name(self, items):
        return str(items[0])

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
        for var in reversed(variables):
            body = Quantifier(qtype, var, body)
        return body

    def varlist(self, items):
        return [Variable(str(tok).lower()) for tok in items]

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
        text = str(items[0])
        return Number(float(text) if "." in text else int(text))

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


_FORMULA_PARSER = Lark(_GRAMMAR, start="formula", parser="earley")
_FILE_PARSER = Lark(_GRAMMAR, start="file", parser="earley")
_TRANSFORMER = _TptpTransformer()


def _parse(text: str, parser: Lark, what: str):
    """Parse + transform with unified error handling (unwrapping lark's VisitError)."""
    try:
        tree = parser.parse(text)
    except TptpParsingError:
        raise
    except Exception as exc:
        raise TptpParsingError(f"SYNTAX_ERROR: could not parse TPTP {what}: {exc}")
    try:
        return _TRANSFORMER.transform(tree)
    except VisitError as exc:
        original = exc.orig_exc
        if isinstance(original, ParsingError):
            raise original
        raise TptpParsingError(f"SYNTAX_ERROR: in TPTP {what}: {original}")


def parse_tptp_formula(text: str) -> Node:
    """Parse a single bare TPTP FOF/CNF formula (no ``fof(...)`` wrapper) into a Node.

    Args:
        text: a TPTP formula, e.g. ``"![X]: (p(X) => q(X))"``.

    Returns:
        The formula as a toolkit :class:`Node`.

    Raises:
        ParsingError: if ``text`` is not a well-formed TPTP formula.
    """
    return _parse(text, _FORMULA_PARSER, "formula")


def parse_tptp(text: str) -> list:
    """Parse a whole TPTP problem into a list of :class:`TptpFormula` records.

    Args:
        text: the contents of a TPTP problem — one or more ``fof(...)`` / ``cnf(...)``
            statements (``%`` line comments and ``/* */`` block comments are ignored).

    Returns:
        A list of :class:`TptpFormula` ``(name, role, formula)`` in source order.

    Raises:
        ParsingError: if the text is not a well-formed TPTP problem.
    """
    return _parse(text, _FILE_PARSER, "problem")


def load_tptp(path: str) -> list:
    """Read a TPTP problem file and :func:`parse_tptp` its contents.

    Args:
        path: path to a ``.p`` / ``.tptp`` file.

    Returns:
        A list of :class:`TptpFormula` records.
    """
    with open(path, "r", encoding="utf-8") as handle:
        return parse_tptp(handle.read())


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


def parse_tptp_problem(text: str) -> TptpProblem:
    """Parse a whole TPTP problem into its formulas *and* its header metadata.

    Combines :func:`parse_tptp` (formula parsing, delegated to unchanged) with an
    independent raw-text scan for the standard ``%`` header block (see
    :func:`_parse_tptp_header`) — the two do not interact, so ``formulas`` here is
    exactly what :func:`parse_tptp` returns for the same ``text`` (same order, same
    :class:`TptpFormula` records), just wrapped in a tuple alongside the header.

    Args:
        text: the contents of a TPTP problem file.

    Returns:
        A :class:`TptpProblem` with ``formulas`` (in source order) and ``header``.

    Raises:
        ParsingError: if the text is not a well-formed TPTP problem (same conditions
            as :func:`parse_tptp`; the header scan alone never raises).
    """
    return TptpProblem(
        formulas=tuple(parse_tptp(text)),
        header=_parse_tptp_header(text),
    )


def load_tptp_problem(path: str) -> TptpProblem:
    """Read a TPTP problem file and :func:`parse_tptp_problem` its contents.

    Mirrors :func:`load_tptp`'s file handling (whole-file read, UTF-8).

    Args:
        path: path to a ``.p`` / ``.tptp`` file.

    Returns:
        A :class:`TptpProblem`.
    """
    with open(path, "r", encoding="utf-8") as handle:
        return parse_tptp_problem(handle.read())
