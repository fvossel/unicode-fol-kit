"""Prolog / Datalog clauses -> kit AST.

The missing leg of the importer family (TPTP, Prover9, SMT-LIB, LaTeX, CASL).
Its immediate use is reading back what a rule learner (an ILP system such as
Popper or Aleph, or a hand-written Prolog program) produced, so the result can
be checked against a structure, proved with, exported to TPTP, or compared
against a reference formula — instead of being eyeballed.

**Two readings, and the caller must choose.** A definite clause

    amide(A) :- carbon(C), nitrogen(N), single_bond(C, N), in(A, C).

says two different things depending on what you want from it:

``mode="clause"`` (default) — the standard logical reading of the clause:
every variable universally quantified over the whole implication,

    ∀a ∀c ∀n (Carbon(c) ∧ Nitrogen(n) ∧ Single_bond(c, n) ∧ In(a, c) → Amide(a))

``mode="body"`` — only the CONDITION, with the variables that occur solely in
the body existentially closed and the head's own variables left free:

    ∃c ∃n (Carbon(c) ∧ Nitrogen(n) ∧ Single_bond(c, n) ∧ In(a, c))

That second form is what a *class definition* is: the property a thing must
have, ready to model-check against one structure. The two are not the same
formula and this module will not guess which you meant — the same discipline
:func:`unicode_fol_kit.fol.tptp_repair.repair_tptp_formula` applies to a free
variable it could close two ways.

(Body-only variables are existentially closed in ``"body"`` mode and
universally closed in ``"clause"`` mode, and both are correct: for a variable
occurring only in the antecedent, ``∀x (P(x) → Q)`` and ``(∃x P(x)) → Q`` are
logically equivalent. ``"clause"`` mode emits the prenex form because that is
the shape every prover expects.)

**Negation as failure is not classical negation.** ``\\+ G`` succeeds when
Prolog fails to prove ``G``, which coincides with ``¬G`` only under the closed
world assumption on a stratified program. Reading it as ``¬`` silently would
turn "not derivable here" into "false everywhere", so it is REFUSED unless the
caller opts in with ``negation_as_failure="classical"`` and thereby states
that the assumption holds for their program.

**Naming is inverted on import**, exactly as in
:mod:`unicode_fol_kit.fol.tptp_input`: Prolog spells a predicate lower-case
and a variable upper-case, the kit does the opposite, so ``carbon(A)`` becomes
``Carbon(a)``. A quoted atom (``'1,2-diacyl'``) keeps its exact characters,
which may not be a legal kit token — run
:func:`unicode_fol_kit.fol.sanitize_names` over the result before rendering it
back to text, the same route the TPTP importer documents.

**The accepted fragment**, and nothing beyond it: facts, definite and normal
clauses, bodies joined by ``,`` and ``;``, ``\\+`` (opt-in), compound terms,
numbers, and the anonymous variable ``_`` (each occurrence a fresh variable).
Lists, operators (``is``, ``=..``, arithmetic comparison), the cut ``!``, and
if-then ``->`` are REFUSED with a message naming what was found — a parser
that quietly dropped a cut would change what the program means.
"""

import re
from typing import List, Optional, Tuple

from .naming import ParsingError
from .nodes import (
    Node, Variable, Constant, Number, Function, Atom, Not, And, Or, Implies,
    Quantifier, free_variables,
)

__all__ = [
    "PrologParsingError", "parse_prolog_clause", "parse_prolog_program",
    "load_prolog",
]


class PrologParsingError(ParsingError):
    """A Prolog import failure carrying a plain message (subclasses
    :class:`~unicode_fol_kit.fol.naming.ParsingError`, like every other
    importer's error type).

    The base class builds its message from a Lark exception; this importer has
    no Lark parser to hand one, so the constructor is overridden to take the
    message directly — the same shape
    :class:`~unicode_fol_kit.fol.prover9_input.Prover9ParsingError` uses, for
    the same reason.
    """

    def __init__(self, message: str):
        self.args = (message,)

    def __str__(self) -> str:
        return self.args[0]


#: Constructs this module refuses rather than approximates, mapped to the
#: reason. Each would change the meaning of a clause if silently dropped or
#: guessed at, which is the one thing an importer must never do.
_REFUSED = {
    "!": "the cut (!) — a control construct with no truth-conditional reading",
    "->": "if-then (->) — Prolog's is a committed choice, not material "
          "implication, and the two disagree when the condition fails",
    "is": "arithmetic evaluation (is) — a computation, not a relation",
    "=..": "the univ operator (=..) — term reflection has no first-order form",
}

_VAR_RE = re.compile(r"^(?:[A-Z_][A-Za-z0-9_]*)$")
_ATOM_RE = re.compile(r"^[a-z][A-Za-z0-9_]*$")
_NUMBER_RE = re.compile(r"^-?\d+(?:\.\d+)?$")


def _cap(name: str) -> str:
    """Capitalise the first character — the kit's predicate spelling.

    Mirrors :func:`unicode_fol_kit.fol.tptp_input._cap` rather than importing
    it, so the two importers' conventions are visibly the same rule and a
    change to either shows up as a failing round-trip test rather than as a
    silent divergence.
    """
    return name[:1].upper() + name[1:] if name else name


def _lower(name: str) -> str:
    """Lower-case the first character — the kit's variable spelling."""
    return name[:1].lower() + name[1:] if name else name


# ---------------------------------------------------------------------------
# Tokeniser / reader
# ---------------------------------------------------------------------------
#
# A hand-written reader rather than a Lark grammar, for one reason: Prolog's
# surface syntax is operator-driven and a grammar that accepted "enough of it"
# would accept operators this module has no reading for. Reading the exact
# fragment by hand makes every refusal explicit and located.

_TOKEN_RE = re.compile(r"""
    (?P<quoted>'(?:\\.|[^'\\])*')      # 'quoted atom'
  | (?P<neg>\\\+)                      # \+   (negation as failure)
  | (?P<neck>:-)                       # :-
  | (?P<arrow>->)                      # ->   (refused; tokenised so the
                                       #       refusal message can name it)
  | (?P<univ>=\.\.)                    # =..
  | (?P<punct>[(),.;\[\]|!])           # structural
  | (?P<name>[A-Za-z_][A-Za-z0-9_]*)   # atom or variable
  | (?P<number>-?\d+(?:\.\d+)?)        # number
  | (?P<other>\S)                      # anything else -> refused, located
""", re.VERBOSE)


class _Reader:
    """Position-tracking token cursor over one clause's text."""

    def __init__(self, text: str):
        self.text = text
        self.tokens: List[Tuple[str, str, int]] = []
        index = 0
        while index < len(text):
            if text[index] in " \t\r\n":
                index += 1
                continue
            if text[index] == "%":                      # line comment
                end = text.find("\n", index)
                index = len(text) if end < 0 else end + 1
                continue
            match = _TOKEN_RE.match(text, index)
            if match is None:                           # pragma: no cover
                raise PrologParsingError(
                    f"SYNTAX_ERROR: unreadable character at position {index}")
            kind = match.lastgroup
            self.tokens.append((kind, match.group(), match.start()))
            index = match.end()
        self.position = 0

    def peek(self) -> Optional[Tuple[str, str, int]]:
        return (self.tokens[self.position]
                if self.position < len(self.tokens) else None)

    def next(self) -> Tuple[str, str, int]:
        token = self.peek()
        if token is None:
            raise PrologParsingError(
                "SYNTAX_ERROR: the clause ended unexpectedly")
        self.position += 1
        return token

    def expect(self, value: str) -> Tuple[str, str, int]:
        token = self.next()
        if token[1] != value:
            raise PrologParsingError(
                f"SYNTAX_ERROR: expected {value!r} at position {token[2]}, "
                f"found {token[1]!r}")
        return token


def _unquote(text: str) -> str:
    """Strip a quoted atom's quotes and undo its escapes."""
    return re.sub(r"\\(.)", r"\1", text[1:-1])


class _Parser:
    """One clause, read with an explicit fresh-variable counter for ``_``."""

    def __init__(self, reader: _Reader, negation_as_failure: str):
        self.reader = reader
        self.negation_as_failure = negation_as_failure
        self._anonymous = 0

    # -- terms ---------------------------------------------------------------

    def term(self) -> Node:
        kind, value, position = self.reader.next()
        if value in _REFUSED:
            raise PrologParsingError(
                f"SYNTAX_ERROR: unsupported construct at position {position}: "
                f"{_REFUSED[value]}")
        if kind == "punct" and value == "[":
            raise PrologParsingError(
                f"SYNTAX_ERROR: list syntax at position {position} — this "
                "importer has no first-order reading for '.'/2 list terms; "
                "rewrite the clause without lists")
        if kind == "number":
            return Number(float(value) if "." in value else int(value))
        if kind == "quoted":
            name = _unquote(value)
            return self._compound_or_constant(name, quoted=True)
        if kind != "name":
            raise PrologParsingError(
                f"SYNTAX_ERROR: expected a term at position {position}, found "
                f"{value!r}")
        if value == "_":
            # Each anonymous variable is a DISTINCT fresh one; collapsing them
            # into a single '_' would equate positions Prolog keeps apart.
            self._anonymous += 1
            return Variable(f"_g{self._anonymous}")
        if _VAR_RE.match(value):
            return Variable(_lower(value))
        return self._compound_or_constant(value, quoted=False)

    def _compound_or_constant(self, name: str, *, quoted: bool) -> Node:
        token = self.reader.peek()
        if token is not None and token[1] == "(":
            self.reader.next()
            arguments = self._arguments()
            return Function(name, arguments)
        return Constant(name)

    def _arguments(self) -> List[Node]:
        arguments = [self.term()]
        while True:
            token = self.reader.next()
            if token[1] == ")":
                return arguments
            if token[1] != ",":
                raise PrologParsingError(
                    f"SYNTAX_ERROR: expected ',' or ')' at position "
                    f"{token[2]}, found {token[1]!r}")
            arguments.append(self.term())

    # -- literals and goals --------------------------------------------------

    def literal(self) -> Node:
        """One predicate application, as an :class:`Atom`."""
        kind, value, position = self.reader.next()
        if value in _REFUSED:
            raise PrologParsingError(
                f"SYNTAX_ERROR: unsupported construct at position {position}: "
                f"{_REFUSED[value]}")
        if kind == "quoted":
            name = _unquote(value)
        elif kind == "name" and not _VAR_RE.match(value):
            name = value
        else:
            raise PrologParsingError(
                f"SYNTAX_ERROR: expected a predicate name at position "
                f"{position}, found {value!r}" +
                (" — a variable cannot be a goal in this fragment"
                 if kind == "name" else ""))
        token = self.reader.peek()
        if token is None or token[1] != "(":
            return Atom(_cap(name), [])
        self.reader.next()
        return Atom(_cap(name), self._arguments())

    def goal(self) -> Node:
        token = self.reader.peek()
        if token is not None and token[0] == "neg":
            self.reader.next()
            if self.negation_as_failure != "classical":
                raise PrologParsingError(
                    f"SYNTAX_ERROR: negation as failure (\\+) at position "
                    f"{token[2]} — it means 'not derivable', which coincides "
                    "with classical ¬ only under the closed world assumption "
                    "on a stratified program. Pass "
                    "negation_as_failure='classical' to read it as ¬ and "
                    "assert that assumption, or rewrite the clause.")
            return Not(self.goal())
        if token is not None and token[1] == "(":
            self.reader.next()
            inner = self.disjunction()
            self.reader.expect(")")
            return inner
        return self.literal()

    def conjunction(self) -> Node:
        result = self.goal()
        while True:
            token = self.reader.peek()
            if token is None or token[1] != ",":
                return result
            self.reader.next()
            result = And(result, self.goal())

    def disjunction(self) -> Node:
        result = self.conjunction()
        while True:
            token = self.reader.peek()
            if token is None or token[1] != ";":
                return result
            self.reader.next()
            result = Or(result, self.conjunction())


def _close(formula: Node, variables, quantifier: str) -> Node:
    """Wrap ``formula`` in one quantifier per variable, alphabetically —
    order among quantifiers of the same kind never changes truth, so this is
    purely for deterministic output."""
    result = formula
    for variable in sorted(variables, key=lambda v: v.name, reverse=True):
        result = Quantifier(quantifier, variable, result)
    return result


def parse_prolog_clause(text: str, *, mode: str = "clause",
                        negation_as_failure: str = "refuse") -> Node:
    """Parse ONE Prolog clause (with or without the trailing ``.``).

    Args:
        text: a fact (``p(a).``) or a rule (``h(A) :- b1(A), b2(A).``).
        mode: ``"clause"`` for the standard logical reading (every variable
            universally quantified over the implication) or ``"body"`` for
            just the condition, with body-only variables existentially closed
            and the head's variables left free — see the module docstring for
            why this is the caller's choice and not a default.
        negation_as_failure: ``"refuse"`` (default) or ``"classical"`` to read
            ``\\+`` as ``¬``, asserting the closed world assumption holds.

    Returns:
        A :class:`~unicode_fol_kit.fol.nodes.Node`. A FACT returns its head
        atom, universally closed over its variables in ``"clause"`` mode and
        returned bare in ``"body"`` mode (a fact has no condition, and
        inventing ``⊤`` would be a formula the caller never wrote).

    Raises:
        ~unicode_fol_kit.fol.prolog_input.PrologParsingError: the text is
            outside the accepted fragment (see
            the module docstring), or ``mode``/``negation_as_failure`` is not
            one of the documented values.
    """
    if mode not in ("clause", "body"):
        raise PrologParsingError(
            f"parse_prolog_clause: unknown mode={mode!r}, expected 'clause' "
            "or 'body'")
    if negation_as_failure not in ("refuse", "classical"):
        raise PrologParsingError(
            "parse_prolog_clause: unknown negation_as_failure="
            f"{negation_as_failure!r}, expected 'refuse' or 'classical'")

    stripped = text.strip()
    if stripped.endswith("."):
        stripped = stripped[:-1]
    if not stripped.strip():
        raise PrologParsingError("SYNTAX_ERROR: empty clause")

    parser = _Parser(_Reader(stripped), negation_as_failure)
    head = parser.literal()

    token = parser.reader.peek()
    body: Optional[Node] = None
    if token is not None and token[0] == "neck":
        parser.reader.next()
        body = parser.disjunction()
    leftover = parser.reader.peek()
    if leftover is not None:
        # A refused OPERATOR shows up here rather than inside a goal (it sits
        # between two well-formed goals), so the documented reason has to be
        # consulted at this point too — otherwise `p :- q -> r.` would be
        # reported as a stray token instead of as if-then, and the reader
        # would go looking for a typo.
        if leftover[1] in _REFUSED:
            raise PrologParsingError(
                f"SYNTAX_ERROR: unsupported construct at position "
                f"{leftover[2]}: {_REFUSED[leftover[1]]}")
        raise PrologParsingError(
            f"SYNTAX_ERROR: unexpected {leftover[1]!r} at position "
            f"{leftover[2]} — one clause per call; use parse_prolog_program "
            "for a file")

    if body is None:
        if mode == "body":
            return head
        return _close(head, free_variables(head), "∀")

    if mode == "body":
        head_variables = free_variables(head)
        body_only = [v for v in free_variables(body) if v not in head_variables]
        return _close(body, body_only, "∃")
    return _close(Implies(body, head), free_variables(Implies(body, head)), "∀")


def parse_prolog_program(text: str, *, mode: str = "clause",
                         negation_as_failure: str = "refuse") -> List[Node]:
    """Parse every clause in ``text``, in order.

    Clauses are split on a ``.`` that ends a clause — a period followed by
    whitespace or end of input — so a decimal point inside a number and a
    period inside a quoted atom do not split anything.

    Several clauses sharing one head are ALTERNATIVES (Prolog tries them in
    turn), i.e. their bodies are implicitly disjoined. This function returns
    them separately and does NOT combine them: the disjunction only holds
    under the completion of the program, which is an assumption about the
    whole program rather than a fact about these clauses, and asserting it
    silently would strengthen what the caller wrote.

    Raises:
        ~unicode_fol_kit.fol.prolog_input.PrologParsingError: as
            :func:`parse_prolog_clause`, with the failing
            clause's text in the message.
    """
    clauses = []
    for chunk in _split_clauses(text):
        try:
            clauses.append(parse_prolog_clause(
                chunk, mode=mode, negation_as_failure=negation_as_failure))
        except PrologParsingError as exc:
            raise PrologParsingError(f"{exc} (in clause: {chunk.strip()!r})")
    return clauses


def _split_clauses(text: str) -> List[str]:
    """Clause-terminating periods only: not a decimal point, not inside a
    quoted atom, not inside a line comment."""
    chunks: List[str] = []
    current: List[str] = []
    index = 0
    in_quote = False
    while index < len(text):
        character = text[index]
        if in_quote:
            current.append(character)
            if character == "\\" and index + 1 < len(text):
                current.append(text[index + 1])
                index += 2
                continue
            if character == "'":
                in_quote = False
            index += 1
            continue
        if character == "'":
            in_quote = True
            current.append(character)
            index += 1
            continue
        if character == "%":
            end = text.find("\n", index)
            index = len(text) if end < 0 else end + 1
            continue
        if character == ".":
            following = text[index + 1] if index + 1 < len(text) else " "
            if following in " \t\r\n":
                chunk = "".join(current).strip()
                if chunk:
                    chunks.append(chunk)
                current = []
                index += 1
                continue
        current.append(character)
        index += 1
    tail = "".join(current).strip()
    if tail:
        chunks.append(tail)
    return chunks


def load_prolog(path: str, *, mode: str = "clause",
                negation_as_failure: str = "refuse") -> List[Node]:
    """Read a ``.pl`` file and parse every clause in it (see
    :func:`parse_prolog_program`)."""
    with open(path, encoding="utf-8") as handle:
        return parse_prolog_program(
            handle.read(), mode=mode, negation_as_failure=negation_as_failure)
