"""Read APE's DRS term into a faithful 1:1 object model — no interpretation.

APE prints its Discourse Representation Structure as one Prolog term::

    drs([A,B],[object(A,man,countable,na,eq,1)-1/2,predicate(B,wait,A)-1/3])

This module parses exactly that surface into frozen dataclasses and does
NOTHING else: no renaming, no dropping, no semantic choices. Interpretation —
which conditions the kit can carry, and as what — is
:mod:`unicode_fol_kit.ace.mapping`'s job, and keeping the two apart is what
makes the mapping's per-condition coverage report trustworthy: every condition
APE emitted is HERE, so a condition the report does not mention cannot exist.

The shape inventory below is measured, not copied from documentation — every
form appears in ``tests/fixtures/ape_5f4d535_corpus_v1.json``, recorded from
APE at the pinned commit over the kit's own 55-sentence corpus:

- atomic conditions ``functor(args)-S/T`` with a sentence/token index
  (``-1/2``; implicit conditions carry ``-1/''`` — an EMPTY token). Functors
  seen: ``object/6``, ``predicate/3..5``, ``property/3..4``, ``relation/3``,
  ``modifier_adv/3``, ``modifier_pp/3``, ``has_part/2``, ``query/2``,
  ``formula/3``.
- complex conditions, none of which carry an index: ``-(drs)`` negation,
  ``~(drs)`` negation as failure, ``=>(drs,drs)`` the duplex condition,
  ``v(drs,drs)`` disjunction, the four modal boxes ``must/can/should/may
  (drs)``, ``question(drs)``, ``command(drs)``.
- a plain Prolog LIST of conditions as itself a condition — APE's grouping
  for ``exactly``/``at most`` cardinalities (the group carries the maximality
  reading jointly, which is why it is not just conjunction and why
  :mod:`.mapping` refuses it until the Count route exists).
- terms: variables (``A``), lowercase atoms (``man``, ``eq``, ``na``,
  ``who``, ``comp_than``), integers (bare, as in ``eq,1``), and the wrapped
  values ``named('John')``, ``int(30)``, ``real(...)``, ``string('Johnny')``,
  ``expr(+,int(1),int(2))`` (arithmetic, nesting).

The parser is a hand-written tokenizer + recursive descent over THIS
inventory, generic enough that an unseen functor still parses (into
:class:`AceAtom` / :class:`AceTermApp`) rather than crashing — it becomes the
mapping layer's "not in the measured corpus" report row instead. A text that
is not even a well-formed term (truncated output, a changed APE) raises
:class:`AceDrsUnreadError` with position and context.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from typing import List, Optional, Tuple, Union

from .runner import AceError

__all__ = [
    "parse_ape_drs", "AceDrsUnreadError",
    "AceDrs", "AceVar", "AceNamed", "AceInt", "AceReal", "AceString",
    "AceExpr", "AceTermApp",
    "AceAtom", "AceNeg", "AceNaf", "AceImpl", "AceOr", "AceModal",
    "AceQuestion", "AceCommand", "AceCondList",
]


class AceDrsUnreadError(AceError):
    """APE's DRS text is not a term this reader understands — either not a
    well-formed Prolog term at all, or a structure outside every shape in
    the measured inventory (see the module docstring)."""


# ---------------------------------------------------------------------------
# Terms
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class AceVar:
    """A discourse referent as APE names it (``A``, ``B``, …). Kept verbatim;
    the kit-side renaming is the mapping layer's concern."""

    name: str

    def render(self) -> str:
        return self.name


@dataclass(frozen=True)
class AceNamed:
    """``named('John')`` — a proper name."""

    name: str

    def render(self) -> str:
        return f"named('{self.name}')"


@dataclass(frozen=True)
class AceInt:
    value: int

    def render(self) -> str:
        return f"int({self.value})"


@dataclass(frozen=True)
class AceReal:
    value: float

    def render(self) -> str:
        return f"real({self.value})"


@dataclass(frozen=True)
class AceString:
    value: str

    def render(self) -> str:
        return f"string('{self.value}')"


@dataclass(frozen=True)
class AceExpr:
    """``expr(+, int(1), int(2))`` — an arithmetic expression term."""

    op: str
    left: "AceTerm"
    right: "AceTerm"

    def render(self) -> str:
        return f"expr({self.op},{_render(self.left)},{_render(self.right)})"


@dataclass(frozen=True)
class AceTermApp:
    """A functored term outside the known wrappers — kept verbatim so an APE
    novelty surfaces in the coverage report instead of crashing the reader."""

    functor: str
    args: Tuple["AceTerm", ...]

    def render(self) -> str:
        return f"{self.functor}({','.join(_render(a) for a in self.args)})"


#: A term: a referent, a bare atom (str), or one of the wrapped values.
AceTerm = Union[AceVar, str, int, AceNamed, AceInt, AceReal, AceString,
                AceExpr, AceTermApp]


def _render(term: AceTerm) -> str:
    if isinstance(term, str):
        return term
    if isinstance(term, int):
        return str(term)
    return term.render()


# ---------------------------------------------------------------------------
# Conditions
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class AceAtom:
    """An atomic condition: ``functor(args)`` plus its sentence/token index.

    ``token`` is ``None`` for implicit conditions (APE prints ``-1/''`` for
    e.g. the group-membership ``has_part`` facts a coordination introduces).
    """

    functor: str
    args: Tuple[AceTerm, ...]
    sentence: Optional[int] = None
    token: Optional[int] = None

    def render(self) -> str:
        body = f"{self.functor}({','.join(_render(a) for a in self.args)})"
        if self.sentence is None:
            return body
        tok = self.token if self.token is not None else "''"
        return f"{body}-{self.sentence}/{tok}"


@dataclass(frozen=True)
class AceNeg:
    """``-(drs)`` — classical negation of a sub-box."""

    drs: "AceDrs"

    def render(self) -> str:
        return f"-({self.drs.render()})"


@dataclass(frozen=True)
class AceNaf:
    """``~(drs)`` — negation as failure ("it is not provable that")."""

    drs: "AceDrs"

    def render(self) -> str:
        return f"~({self.drs.render()})"


@dataclass(frozen=True)
class AceImpl:
    """``=>(drs,drs)`` — the duplex condition (every/no/if-then/each-of)."""

    antecedent: "AceDrs"
    consequent: "AceDrs"

    def render(self) -> str:
        return f"=>({self.antecedent.render()},{self.consequent.render()})"


@dataclass(frozen=True)
class AceOr:
    """``v(drs,drs)`` — disjunction of two sub-boxes."""

    left: "AceDrs"
    right: "AceDrs"

    def render(self) -> str:
        return f"v({self.left.render()},{self.right.render()})"


@dataclass(frozen=True)
class AceModal:
    """``must/can/should/may (drs)`` — one of ACE's four modal boxes."""

    modality: str
    drs: "AceDrs"

    def render(self) -> str:
        return f"{self.modality}({self.drs.render()})"


@dataclass(frozen=True)
class AceQuestion:
    """``question(drs)`` — an interrogative sentence's box."""

    drs: "AceDrs"

    def render(self) -> str:
        return f"question({self.drs.render()})"


@dataclass(frozen=True)
class AceCommand:
    """``command(drs)`` — an imperative sentence's box."""

    drs: "AceDrs"

    def render(self) -> str:
        return f"command({self.drs.render()})"


@dataclass(frozen=True)
class AceCondList:
    """A LIST of conditions as itself a condition — APE's joint grouping for
    ``exactly``/``at most`` cardinalities (see the module docstring)."""

    conditions: Tuple["AceCondition", ...]

    def render(self) -> str:
        return "[" + ",".join(c.render() for c in self.conditions) + "]"


AceCondition = Union[AceAtom, AceNeg, AceNaf, AceImpl, AceOr, AceModal,
                     AceQuestion, AceCommand, AceCondList]

#: Complex-condition functors, mapped to their dataclass. ``v`` is a plain
#: atom name in Prolog, so classification happens AFTER a generic parse: an
#: application is complex iff its functor is listed here AND every argument
#: is a DRS — ``v(A,B)`` with referent args would stay an ordinary AceAtom.
_COMPLEX = {
    "-": (AceNeg, 1), "~": (AceNaf, 1), "=>": (AceImpl, 2), "v": (AceOr, 2),
    "question": (AceQuestion, 1), "command": (AceCommand, 1),
    "must": (AceModal, 1), "can": (AceModal, 1), "should": (AceModal, 1),
    "may": (AceModal, 1),
}


@dataclass(frozen=True)
class AceDrs:
    """One box: declared referents plus conditions, verbatim from APE."""

    referents: Tuple[AceVar, ...]
    conditions: Tuple[AceCondition, ...]

    def render(self) -> str:
        refs = ",".join(v.name for v in self.referents)
        conds = ",".join(c.render() for c in self.conditions)
        return f"drs([{refs}],[{conds}])"

    def walk_conditions(self):
        """Every condition in the tree, pre-order — sub-boxes AND the inner
        conditions of a list condition included (a list's members are
        conditions in their own right; skipping them made the renamer's
        event detection blind to ``exactly``/``at most`` scopes)."""
        for cond in self.conditions:
            yield from _walk_condition(cond)

    def walk_boxes(self):
        """Every box in the tree, pre-order, this one first."""
        yield self
        for cond in self.conditions:
            for sub in _sub_boxes(cond):
                yield from sub.walk_boxes()


def _walk_condition(cond: "AceCondition"):
    yield cond
    if isinstance(cond, AceCondList):
        for inner in cond.conditions:
            yield from _walk_condition(inner)
    else:
        for sub in _sub_boxes(cond):
            yield from sub.walk_conditions()


def _sub_boxes(cond: AceCondition):
    if isinstance(cond, (AceNeg, AceNaf, AceModal, AceQuestion, AceCommand)):
        yield cond.drs
    elif isinstance(cond, AceImpl):
        yield cond.antecedent
        yield cond.consequent
    elif isinstance(cond, AceOr):
        yield cond.left
        yield cond.right
    elif isinstance(cond, AceCondList):
        for inner in cond.conditions:
            yield from _sub_boxes(inner)


# ---------------------------------------------------------------------------
# Tokenizer + recursive descent
# ---------------------------------------------------------------------------

_TOKEN = re.compile(r"""
    (?P<ws>\s+)
  | (?P<real>\d+\.\d+)
  | (?P<int>\d+)
  | (?P<var>[A-Z_][A-Za-z0-9_]*)
  | (?P<atom>[a-z][A-Za-z0-9_]*)
  | (?P<quoted>'(?:[^']|'')*')
  | (?P<symbol>=>|\\/|[-~=+*/^<>])
  | (?P<punct>[()\[\],|])
""", re.VERBOSE)


def _tokenize(text: str) -> List[Tuple[str, str, int]]:
    tokens = []
    pos = 0
    while pos < len(text):
        match = _TOKEN.match(text, pos)
        if match is None:
            raise AceDrsUnreadError(
                f"DRS reader: unexpected character {text[pos]!r} at offset "
                f"{pos} in {text[max(0, pos - 30):pos + 30]!r}")
        kind = match.lastgroup
        if kind != "ws":
            tokens.append((kind, match.group(), pos))
        pos = match.end()
    tokens.append(("end", "", pos))
    return tokens


class _Parser:
    def __init__(self, text: str):
        self.text = text
        self.tokens = _tokenize(text)
        self.i = 0

    # -- token plumbing ----------------------------------------------------
    def peek(self, ahead: int = 0) -> Tuple[str, str]:
        kind, value, _ = self.tokens[min(self.i + ahead, len(self.tokens) - 1)]
        return kind, value

    def take(self, kind: Optional[str] = None, value: Optional[str] = None):
        actual_kind, actual_value, pos = self.tokens[self.i]
        if ((kind is not None and actual_kind != kind)
                or (value is not None and actual_value != value)):
            want = value if value is not None else kind
            raise AceDrsUnreadError(
                f"DRS reader: expected {want!r}, found {actual_value!r} at "
                f"offset {pos} in {self.text[max(0, pos - 30):pos + 30]!r}")
        self.i += 1
        return actual_value

    # -- grammar -----------------------------------------------------------
    def parse(self) -> AceDrs:
        drs = self.drs()
        self.take("end")
        return drs

    def drs(self) -> AceDrs:
        self.take("atom", "drs")
        self.take("punct", "(")
        self.take("punct", "[")
        referents: List[AceVar] = []
        while self.peek() != ("punct", "]"):
            referents.append(AceVar(self.take("var")))
            if self.peek() == ("punct", ","):
                self.take()
        self.take("punct", "]")
        self.take("punct", ",")
        conditions = self.condition_list()
        self.take("punct", ")")
        return AceDrs(tuple(referents), tuple(conditions))

    def condition_list(self) -> List[AceCondition]:
        self.take("punct", "[")
        conditions: List[AceCondition] = []
        while self.peek() != ("punct", "]"):
            conditions.append(self.condition())
            if self.peek() == ("punct", ","):
                self.take()
        self.take("punct", "]")
        return conditions

    def condition(self) -> AceCondition:
        kind, value = self.peek()
        if (kind, value) == ("punct", "["):
            return AceCondList(tuple(self.condition_list()))
        if kind in ("atom", "symbol") and self.peek(1) == ("punct", "("):
            functor = self.take()
            args = self.application_args()
            complex_entry = _COMPLEX.get(functor)
            if (complex_entry is not None
                    and len(args) == complex_entry[1]
                    and all(isinstance(a, AceDrs) for a in args)):
                cls = complex_entry[0]
                if cls is AceModal:
                    return AceModal(functor, *args)
                return cls(*args)
            atom_args = tuple(a for a in args)
            sentence, token = self.optional_index()
            return AceAtom(functor, atom_args, sentence, token)
        raise AceDrsUnreadError(
            f"DRS reader: a condition cannot start with {value!r} "
            f"(offset {self.tokens[self.i][2]})")

    def application_args(self) -> List:
        """The argument list of ``functor(...)`` — each argument is a term,
        or a whole sub-``drs`` for the complex conditions."""
        self.take("punct", "(")
        args: List = []
        while self.peek() != ("punct", ")"):
            if self.peek() == ("atom", "drs") and self.peek(1) == ("punct", "("):
                args.append(self.drs())
            else:
                args.append(self.term())
            if self.peek() == ("punct", ","):
                self.take()
        self.take("punct", ")")
        return args

    def optional_index(self) -> Tuple[Optional[int], Optional[int]]:
        """``-S/T`` after an atomic condition; ``T`` may be ``''``."""
        if self.peek() != ("symbol", "-"):
            return None, None
        kind, _ = self.peek(1)
        if kind != "int":
            return None, None
        self.take("symbol", "-")
        sentence = int(self.take("int"))
        self.take("symbol", "/")
        kind, _ = self.peek()
        if kind == "int":
            return sentence, int(self.take("int"))
        quoted = self.take("quoted")
        if quoted != "''":
            raise AceDrsUnreadError(
                f"DRS reader: expected an integer or '' as token index, "
                f"found {quoted!r}")
        return sentence, None

    def term(self) -> AceTerm:
        kind, value = self.peek()
        if kind == "var":
            self.take()
            return AceVar(value)
        if kind == "int":
            self.take()
            return int(value)
        if kind == "real":
            self.take()
            return float(value)
        if kind == "quoted":
            self.take()
            return _unquote(value)
        if kind == "symbol":
            # `-` directly before a number is a sign; any symbol is
            # otherwise a bare symbolic atom (the operator argument of
            # ``expr(+,...)`` / ``formula(...,=,...)``).
            if value == "-" and self.peek(1)[0] in ("int", "real"):
                self.take()
                num_kind, num_value = self.peek()
                self.take()
                return (-int(num_value) if num_kind == "int"
                        else -float(num_value))
            self.take()
            return value
        if kind == "atom":
            self.take()
            if self.peek() == ("punct", "("):
                args = self.application_args()
                return _wrap_term(value, args, self.text)
            return value
        raise AceDrsUnreadError(
            f"DRS reader: a term cannot start with {value!r} "
            f"(offset {self.tokens[self.i][2]})")


def _unquote(quoted: str) -> str:
    return quoted[1:-1].replace("''", "'")


def _wrap_term(functor: str, args: List, text: str) -> AceTerm:
    """Specialize the wrapped-value terms; keep everything else verbatim."""
    if functor == "named" and len(args) == 1 and isinstance(args[0], str):
        return AceNamed(args[0])
    if functor == "int" and len(args) == 1 and isinstance(args[0], int):
        return AceInt(args[0])
    if functor == "real" and len(args) == 1 and isinstance(args[0], (int, float)):
        return AceReal(float(args[0]))
    if functor == "string" and len(args) == 1 and isinstance(args[0], str):
        return AceString(args[0])
    if functor == "expr" and len(args) == 3 and isinstance(args[0], str):
        return AceExpr(args[0], args[1], args[2])
    return AceTermApp(functor, tuple(args))


def parse_ape_drs(text: str) -> AceDrs:
    """APE's printed DRS term → the 1:1 object model (see module docstring).

    Raises :class:`AceDrsUnreadError` with offset and context on anything
    that is not a well-formed term of the measured inventory.
    """
    return _Parser(text.strip()).parse()
