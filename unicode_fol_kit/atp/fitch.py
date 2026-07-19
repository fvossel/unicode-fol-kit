"""Fitch-style natural deduction: proof objects and a sound proof *checker*.

Where :mod:`unicode_fol_kit.atp.resolution` answers *"is this entailment true?"*
with a single bool, this module checks a *human-written derivation*: a Fitch-style
natural-deduction proof with nested subproofs (hypothetical reasoning), per-line
justifications, and discharge rules. It is *sound* — ``check_proof`` returns True
only when every line genuinely follows from the cited material by the stated rule
and the proof's open assumptions really do entail its conclusion.

Two checking regimes share one proof representation:

- **Classical FOL / MSFOL** (``logic="fol"`` / ``"msfol"``) is checked by a
  *syntactic* rule table: each line's rule (``"∧I"``, ``"→E"``, ``"∀E"``, …) is
  verified by structural pattern-match over the frozen AST node classes, with
  discharge, citation-accessibility (the "Fitch bar"), and quantifier
  eigenvariable side-conditions enforced explicitly. This is the textbook
  Gentzen-NK calculus in Fitch/Jaśkowski boxed-subproof notation.

- **Non-classical** logics (``"K3"``, ``"LP"``) are checked *semantically*: the
  same proof structure (scope, discharge, accessibility) is verified, but each
  derived line is certified by the matching decision oracle — the open
  assumptions in scope must entail the line under that logic's consequence
  relation. This is sound by construction and, unlike a hand-rolled rule table,
  cannot accidentally license a classically-valid-but-non-classically-invalid
  step (LP rejects modus ponens and explosion; K3 has no logical truths).

Soundness design (the non-obvious parts):

- The *open-assumption set* — the undischarged hypotheses in scope at a line,
  including the proof's premises — is threaded to every rule. Discharge rules
  (``→I``/``¬I``/``∨E``/``∀I``/``∃E``) are correct *relative to those
  assumptions*, not to a local entailment between the cited lines, so that is
  what the checker and the cross-check oracle see.
- ``check_proof`` certifies a *sequent*: the proof's premises ⊢ its conclusion
  (the last top-level line). ``verify_proof`` returns that sequent plus the first
  failing line and reason.
- ⊥ is a first-class logical constant :data:`FALSUM`, NOT an ordinary atom, so
  ``⊥E`` (ex falso) and ``¬I`` are validated by the checker's own semantics and
  desugared to a genuine contradiction for the Z3 cross-check.
- Citation accessibility forbids reaching into an already-closed sibling subproof
  (a classic natural-deduction unsoundness): a line may cite an earlier line only
  if every subproof enclosing the cited line also encloses the citing line, and a
  whole subproof only once it has closed at an enclosing-or-equal level.

Public API: :class:`Justification`, :class:`Line`, :class:`Subproof`,
:class:`Proof`, :class:`ProofResult`, the authoring helpers :func:`premise`,
:func:`assume`, :func:`line`, :func:`flag` (the ∀I eigenvariable-box head), the
constant :data:`FALSUM`, the checkers :func:`check_proof` / :func:`verify_proof`,
and the renderers :func:`render_fitch` / :func:`render_latex_fitch`.
"""

from dataclasses import dataclass, replace
from functools import reduce
from typing import Callable, Dict, List, Optional, Tuple, Union

from ..fol.nodes import (
    Node, Atom, Not, And, Or, Implies, Iff, Quantifier,
    Variable, Constant, Number, Function,
    SortedQuantifier, SortedConstant, LambdaVar,
    Count, Cardinality, SortedCount, SortedCardinality, SlashedExists,
    Box, Diamond, Knows, Believes,
    Always, Eventually, Next, Until,
    Historically, Once, Previous, Since,
    Obligatory, Permitted,
    free_variables,
)
from ..fol._msfl_nodes import _rename, _fresh_name, subst_slash_set


# ---------------------------------------------------------------------------
# Falsum (⊥) as a logical constant
# ---------------------------------------------------------------------------
#
# ⊥ is represented by the reserved nullary atom Atom("⊥", ()) but is NOT treated
# as an ordinary predicate anywhere in the checker: is_falsum() recognises it, the
# ⊥I/⊥E/¬I/RAA rules give it its logical meaning, and _desugar_falsum() rewrites it
# to a genuine contradiction before the formula is handed to the Z3 cross-check
# (where a bare uninterpreted atom "⊥" would be satisfiable and silently break the
# soundness oracle). Using a reserved atom rather than a new Node subclass keeps it
# out of the renderers / parser / NODE_CLASSES — it only ever means "false" here.

_FALSUM_NAME = "⊥"
FALSUM: Atom = Atom(_FALSUM_NAME, ())

# A reserved propositional letter used only to desugar ⊥ into (p ∧ ¬p) for the
# classical oracle. Chosen so it cannot collide with a user predicate (uppercase
# rule requires PREDICATE start with A–Z; this name is not parseable, so it can
# only be introduced here).
_BOT_SENTINEL: Atom = Atom("⊥sentinel", ())
_BOT_CONTRADICTION: And = And(_BOT_SENTINEL, Not(_BOT_SENTINEL))


def is_falsum(node: Node) -> bool:
    """Return True iff ``node`` is the reserved falsum constant ⊥."""
    return isinstance(node, Atom) and node.predicate == _FALSUM_NAME and not node.args


def _desugar_falsum(node: Node) -> Node:
    """Rewrite every ⊥ occurrence to the contradiction (p ∧ ¬p).

    Used only to build the classical Z3 cross-check formula: ⊥ has no meaning to
    ``to_z3`` (it would become a satisfiable uninterpreted atom), so it is replaced
    by a genuinely unsatisfiable sentence that preserves the intended semantics of
    the ⊥-rules. The input is not mutated.
    """
    if is_falsum(node):
        return _BOT_CONTRADICTION
    return node.map_children(_desugar_falsum)


def _classical_valid(assumptions: List[Node], conclusion: Node) -> bool:
    """Return True iff ``assumptions`` classically entail ``conclusion`` (via Z3).

    Builds (a₁ ∧ … ∧ aₙ) → conclusion, desugars ⊥ to a genuine contradiction, and
    asks Z3 (which interprets ``=`` natively, unlike resolution). This is the
    soundness oracle for the equality rules and the test cross-checks.
    """
    from .z3_models import is_valid
    big = Implies(reduce(And, assumptions), conclusion) if assumptions else conclusion
    return is_valid(_desugar_falsum(big))


# ---------------------------------------------------------------------------
# Proof objects
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class Justification:
    """How a proof line was obtained: a rule tag plus the lines/subproofs it cites.

    ``rule`` is the canonical rule tag (e.g. ``"∧I"``, ``"→E"``, ``"Reit"``,
    ``"Premise"``, ``"Assume"``). ``cites`` is a tuple whose elements are either an
    ``int`` (a cited line number) or a ``(start, end)`` ``tuple`` (a cited subproof
    span, used by the discharge rules). ``extra`` carries rule-specific data, such
    as the instantiation term for ``∀E`` or the witness term for ``∃I``. The
    dataclass is frozen and hashable; all containers are coerced to tuples.
    """

    rule: str
    cites: Tuple[Union[int, Tuple[int, int]], ...] = ()
    extra: Tuple = ()

    def __post_init__(self):
        """Coerce ``cites``/``extra`` to tuples so the justification stays hashable."""
        object.__setattr__(self, "cites", tuple(
            tuple(c) if isinstance(c, (list, tuple)) else c for c in self.cites
        ))
        object.__setattr__(self, "extra", tuple(self.extra))

    def to_dict(self) -> dict:
        """Serialise to a JSON-compatible dict (terms in ``extra`` via Node.to_dict)."""
        return {
            "rule": self.rule,
            "cites": [list(c) if isinstance(c, tuple) else c for c in self.cites],
            "extra": [e.to_dict() if isinstance(e, Node) else e for e in self.extra],
        }

    @staticmethod
    def from_dict(d: dict) -> "Justification":
        """Deserialise a Justification produced by :meth:`to_dict`."""
        cites = tuple(tuple(c) if isinstance(c, list) else c for c in d.get("cites", ()))
        extra = tuple(
            Node.from_dict(e) if isinstance(e, dict) and "_type" in e else e
            for e in d.get("extra", ())
        )
        return Justification(d["rule"], cites, extra)


@dataclass(frozen=True)
class Line:
    """One numbered proof line: a formula and the justification that produced it."""

    number: int
    formula: Node
    justification: Justification

    def to_dict(self) -> dict:
        """Serialise to a JSON-compatible dict."""
        return {
            "_kind": "line",
            "number": self.number,
            "formula": self.formula.to_dict(),
            "justification": self.justification.to_dict(),
        }

    @staticmethod
    def from_dict(d: dict) -> "Line":
        """Deserialise a Line produced by :meth:`to_dict`."""
        return Line(d["number"], Node.from_dict(d["formula"]),
                    Justification.from_dict(d["justification"]))


@dataclass(frozen=True)
class Subproof:
    """A boxed subproof: an optional flagged assumption and a body of further steps.

    ``assumption`` is the boxed hypothesis (a :class:`Line` with rule ``"Assume"``)
    or ``None`` for a pure eigenvariable-introduction box (``∀I``). ``flag`` is the
    eigenvariable introduced by the box (``∀I`` / ``∃E``) or ``None``. ``body`` is
    the ordered tuple of inner steps (lines and nested subproofs). ``kind`` tags
    the box (``"flagged"`` for ordinary hypothetical subproofs; reserved for future
    strict/modal boxes). The subproof's *conclusion* — what discharge rules read —
    is the formula of its last body line.
    """

    assumption: Optional[Line]
    body: Tuple[Union[Line, "Subproof"], ...] = ()
    kind: str = "flagged"
    flag: Optional[Variable] = None

    def __post_init__(self):
        """Coerce ``body`` to a tuple so the subproof stays hashable."""
        object.__setattr__(self, "body", tuple(self.body))

    def to_dict(self) -> dict:
        """Serialise to a JSON-compatible dict."""
        return {
            "_kind": "subproof",
            "assumption": self.assumption.to_dict() if self.assumption is not None else None,
            "body": [s.to_dict() for s in self.body],
            "kind": self.kind,
            "flag": self.flag.to_dict() if self.flag is not None else None,
        }

    @staticmethod
    def from_dict(d: dict) -> "Subproof":
        """Deserialise a Subproof produced by :meth:`to_dict`."""
        assumption = Line.from_dict(d["assumption"]) if d.get("assumption") else None
        body = tuple(_step_from_dict(s) for s in d.get("body", ()))
        flag = Node.from_dict(d["flag"]) if d.get("flag") else None
        return Subproof(assumption, body, d.get("kind", "flagged"), flag)


def _step_from_dict(d: dict) -> Union[Line, Subproof]:
    """Deserialise a proof step (line or subproof) from its dict tag."""
    return Subproof.from_dict(d) if d.get("_kind") == "subproof" else Line.from_dict(d)


@dataclass(frozen=True)
class Proof:
    """A complete Fitch proof: premises, derivation steps, and the target logic.

    ``premises`` are the top-level undischarged assumptions (lines with rule
    ``"Premise"``). ``steps`` are the derivation (lines and subproofs). The proof's
    *conclusion* is the formula of the last top-level :class:`Line`. ``logic``
    selects the checking regime (``"fol"``/``"msfol"`` syntactic; ``"K3"``/``"LP"``
    semantic).
    """

    premises: Tuple[Line, ...] = ()
    steps: Tuple[Union[Line, Subproof], ...] = ()
    logic: str = "fol"

    def __post_init__(self):
        """Coerce ``premises``/``steps`` to tuples so the proof stays hashable."""
        object.__setattr__(self, "premises", tuple(self.premises))
        object.__setattr__(self, "steps", tuple(self.steps))

    def to_dict(self) -> dict:
        """Serialise the whole proof to a JSON-compatible dict."""
        return {
            "premises": [p.to_dict() for p in self.premises],
            "steps": [s.to_dict() for s in self.steps],
            "logic": self.logic,
        }

    @staticmethod
    def from_dict(d: dict) -> "Proof":
        """Deserialise a Proof produced by :meth:`to_dict`."""
        return Proof(
            tuple(Line.from_dict(p) for p in d.get("premises", ())),
            tuple(_step_from_dict(s) for s in d.get("steps", ())),
            d.get("logic", "fol"),
        )

    def to_fitch(self, ascii: bool = False) -> str:
        """Render the proof in Fitch notation (Unicode scope bars / ASCII fallback)."""
        return render_fitch(self, ascii=ascii)

    def to_latex_fitch(self) -> str:
        """Render the proof as a LaTeX Fitch derivation (array form, no extra package)."""
        return render_latex_fitch(self)


@dataclass(frozen=True)
class ProofResult:
    """The outcome of checking a proof.

    ``ok`` is True iff the proof is well-formed and every line is licensed.
    ``premises`` / ``conclusion`` report the certified sequent (premises ⊢
    conclusion). On failure, ``error_line`` and ``error`` name the first offending
    line and the reason.
    """

    ok: bool
    premises: Tuple[Node, ...]
    conclusion: Optional[Node]
    error_line: Optional[int]
    error: Optional[str]
    logic: str

    def __bool__(self) -> bool:
        """A ProofResult is truthy iff the proof checked out."""
        return self.ok


# ---------------------------------------------------------------------------
# Authoring helpers
# ---------------------------------------------------------------------------

def premise(number: int, formula: Node) -> Line:
    """Build a premise line (rule ``"Premise"``)."""
    return Line(number, formula, Justification("Premise"))


def assume(number: int, formula: Node) -> Line:
    """Build an assumption line (rule ``"Assume"``) for the head of a subproof."""
    return Line(number, formula, Justification("Assume"))


def line(number: int, formula: Node, rule: str, *cites, extra=()) -> Line:
    """Build a derived line citing ``*cites`` (ints for lines, ``(s, e)`` for subproofs)."""
    return Line(number, formula, Justification(rule, tuple(cites), tuple(extra)))


def flag(number: int, var: "Variable") -> Line:
    """Build a boxed-variable head line (rule ``"Flag"``) for a ∀I subproof.

    The line's formula is the eigenvariable itself; it is a scope marker, not a
    logical hypothesis. Pair it with ``Subproof(assumption=flag(n, e), …, flag=e)``.
    """
    return Line(number, var, Justification("Flag"))


# ---------------------------------------------------------------------------
# Indexing: flatten the proof, validate numbering, compute scope/visibility
# ---------------------------------------------------------------------------

_RESERVED_RULES = frozenset({"Premise", "Assume", "Flag"})


class _Rec:
    """A flattened line record (mutable: ``pos`` is filled during the linear pass)."""

    __slots__ = ("number", "formula", "just", "scope", "role", "pos")

    def __init__(self, number, formula, just, scope, role):
        self.number = number
        self.formula = formula
        self.just = just
        self.scope = scope          # tuple of enclosing subproof ids (outer→inner)
        self.role = role            # 'premise' | 'assume' | 'flag' | 'derived'
        self.pos = -1               # linear position, set by _index


class _SubRec:
    """A flattened subproof record used to resolve span citations and discharge."""

    __slots__ = ("sid", "scope", "start", "end", "assumption", "flag",
                 "conclusion", "kind")

    def __init__(self, sid, scope, start, end, assumption, flag, conclusion, kind):
        self.sid = sid
        self.scope = scope          # container scope (NOT including this subproof)
        self.start = start          # first line number in the box
        self.end = end              # last line number in the box
        self.assumption = assumption  # assumed formula or None
        self.flag = flag            # eigenvariable Variable or None
        self.conclusion = conclusion  # last body line's formula or None
        self.kind = kind


class _IndexError(Exception):
    """Raised for a structurally malformed proof (bad numbering, role clash)."""

    def __init__(self, number: Optional[int], message: str):
        super().__init__(message)
        self.number = number
        self.message = message


def _canon_q(node: Node) -> Node:
    """Canonicalise quantifier spellings ('forall'/'exists' → '∀'/'∃') throughout.

    ``Quantifier`` is a frozen dataclass keyed on the raw ``type`` string, so
    ``Quantifier('forall', …) != Quantifier('∀', …)``. Normalising every formula
    entering the checker to the glyph spelling keeps the structural ``==`` the rules
    rely on from falsely rejecting a valid proof that mixed the two spellings.
    """
    node = node.map_children(_canon_q)
    if isinstance(node, Quantifier) and node.type in ("forall", "exists"):
        return Quantifier("∀" if node.type == "forall" else "∃", node.variable, node.formula)
    if isinstance(node, SortedQuantifier) and node.type in ("forall", "exists"):
        return SortedQuantifier("∀" if node.type == "forall" else "∃",
                                node.variable, node.sort, node.formula)
    return node


def _index(proof: "Proof"):
    """Flatten ``proof`` into ordered line records + subproof records.

    Validates that line numbers are exactly 1..N in linear order (premises first,
    then each step in order, an assumption before its body). Returns
    ``(order, lines_by_number, subs_by_span, sub_by_sid)``. Raises
    :class:`_IndexError` on a structural defect.
    """
    order: List[_Rec] = []
    lines: Dict[int, _Rec] = {}
    subs_by_span: Dict[Tuple[int, int], _SubRec] = {}
    sub_by_sid: Dict[int, _SubRec] = {}
    sid_counter = [0]

    def add(rec: _Rec):
        if rec.number in lines:
            raise _IndexError(rec.number, f"duplicate line number {rec.number}")
        rec.pos = len(order)
        order.append(rec)
        lines[rec.number] = rec

    for pl in proof.premises:
        if not isinstance(pl, Line):
            raise _IndexError(None, "proof.premises must contain Line objects")
        add(_Rec(pl.number, _canon_q(pl.formula), pl.justification, (), "premise"))

    def walk(steps, scope) -> List[int]:
        nums: List[int] = []
        for st in steps:
            if isinstance(st, Line):
                add(_Rec(st.number, _canon_q(st.formula), st.justification, scope, "derived"))
                nums.append(st.number)
            elif isinstance(st, Subproof):
                sid = sid_counter[0]
                sid_counter[0] += 1
                inner = scope + (sid,)
                sp_nums: List[int] = []
                assum_formula = None
                if st.assumption is not None:
                    a = st.assumption
                    if not isinstance(a, Line):
                        raise _IndexError(None,
                            "a subproof assumption must be a Line "
                            "('Assume' hypothesis or 'Flag' boxed-variable head)")
                    # A 'Flag' head (rule == "Flag") introduces only the boxed
                    # eigenvariable — its formula is NOT a logical hypothesis (∀I).
                    # An 'Assume' head IS a hypothesis even when a flag is also set
                    # (∃E assumes φ(e) and flags e).
                    is_flag = a.justification.rule == "Flag"
                    role = "flag" if is_flag else "assume"
                    add(_Rec(a.number, _canon_q(a.formula), a.justification, inner, role))
                    sp_nums.append(a.number)
                    if not is_flag:
                        assum_formula = _canon_q(a.formula)
                else:
                    raise _IndexError(None,
                        "a subproof must carry an assumption Line (an 'Assume' "
                        "hypothesis, or a 'Flag' boxed-variable head for ∀I)")
                body_nums = walk(st.body, inner)
                sp_nums.extend(body_nums)
                if not sp_nums:
                    raise _IndexError(None, "a subproof must contain at least one line")
                start, end = min(sp_nums), max(sp_nums)
                conclusion = (_canon_q(st.body[-1].formula)
                              if st.body and isinstance(st.body[-1], Line) else None)
                rec = _SubRec(sid, scope, start, end, assum_formula, st.flag,
                              conclusion, st.kind)
                subs_by_span[(start, end)] = rec
                sub_by_sid[sid] = rec
                nums.extend(sp_nums)
            else:
                raise _IndexError(None, f"unexpected step {type(st).__name__}")
        return nums

    walk(proof.steps, ())

    # Numbering must be exactly 1..N in linear order.
    for expected, rec in enumerate(order, start=1):
        if rec.number != expected:
            raise _IndexError(rec.number,
                f"line numbers must be 1..N in order; expected {expected}, "
                f"got {rec.number}")

    return order, lines, subs_by_span, sub_by_sid


def _is_prefix(a: tuple, b: tuple) -> bool:
    """Return True iff tuple ``a`` is a (not necessarily proper) prefix of ``b``."""
    return len(a) <= len(b) and tuple(a) == tuple(b[:len(a)])


# ---------------------------------------------------------------------------
# Resolved citations
# ---------------------------------------------------------------------------

@dataclass
class _Ref:
    """A resolved, accessibility-checked citation handed to a rule checker."""

    kind: str                       # 'line' | 'subproof'
    formula: Optional[Node] = None  # line: the cited formula
    assumption: Optional[Node] = None   # subproof: assumed formula
    conclusion: Optional[Node] = None   # subproof: last body line formula
    flag: Optional[Variable] = None     # subproof: eigenvariable
    sp_kind: Optional[str] = None       # subproof: kind tag


def _resolve(tok, citing: _Rec, lines, subs_by_span):
    """Resolve one citation token against the Fitch accessibility relation.

    Returns ``(ref, None)`` on success or ``(None, reason)`` if the cited line /
    subproof does not exist, lies inside an already-closed box, or is not above the
    citing line.
    """
    if isinstance(tok, int):
        rec = lines.get(tok)
        if rec is None:
            return None, f"cites line {tok}, which does not exist"
        if not _is_prefix(rec.scope, citing.scope):
            return None, (f"line {tok} is not in scope at line {citing.number} "
                          f"(it lies inside a closed subproof)")
        if rec.pos >= citing.pos:
            return None, f"line {tok} is not above line {citing.number}"
        return _Ref("line", formula=rec.formula), None

    if isinstance(tok, tuple) and len(tok) == 2:
        span = (tok[0], tok[1])
        sp = subs_by_span.get(span)
        if sp is None:
            return None, f"cites subproof {span[0]}–{span[1]}, which does not exist"
        if not _is_prefix(sp.scope, citing.scope):
            return None, (f"subproof {span[0]}–{span[1]} is not in scope at "
                          f"line {citing.number}")
        end_rec = lines.get(sp.end)
        if end_rec is None or end_rec.pos >= citing.pos:
            return None, (f"subproof {span[0]}–{span[1]} is not closed above "
                          f"line {citing.number}")
        return _Ref("subproof", assumption=sp.assumption, conclusion=sp.conclusion,
                    flag=sp.flag, sp_kind=sp.kind), None

    return None, f"malformed citation {tok!r}"


# ---------------------------------------------------------------------------
# Classical rule table (propositional fragment)
# ---------------------------------------------------------------------------
#
# Each rule checker has signature (concl, refs, extra, open_assumptions) and
# returns None when the step is licensed, or an error string. All comparisons are
# structural == on frozen, hashable nodes. Dispatch is class-based (isinstance),
# never on the surface glyph.

RuleFn = Callable[[Node, List[_Ref], tuple, List[Node]], Optional[str]]


def _r_reit(concl, refs, extra, oa):
    """Reiteration: copy an in-scope earlier line."""
    if len(refs) != 1 or refs[0].kind != "line":
        return "Reit cites exactly one line"
    if refs[0].formula != concl:
        return "Reit: the conclusion must equal the cited line"
    return None


def _r_and_i(concl, refs, extra, oa):
    """∧I: from φ and ψ infer φ ∧ ψ (conjuncts in cited order)."""
    if not isinstance(concl, And):
        return "∧I must conclude a conjunction"
    if len(refs) != 2 or any(r.kind != "line" for r in refs):
        return "∧I cites two lines"
    if concl.left != refs[0].formula or concl.right != refs[1].formula:
        return "∧I: the conjuncts must equal the two cited lines, in order"
    return None


def _r_and_e(concl, refs, extra, oa):
    """∧E: from φ ∧ ψ infer φ (or ψ)."""
    if len(refs) != 1 or refs[0].kind != "line":
        return "∧E cites one line"
    src = refs[0].formula
    if not isinstance(src, And):
        return "∧E cites a conjunction"
    if concl != src.left and concl != src.right:
        return "∧E: the conclusion must be one of the conjuncts"
    return None


def _r_or_i(concl, refs, extra, oa):
    """∨I: from φ infer φ ∨ ψ (or ψ ∨ φ)."""
    if not isinstance(concl, Or):
        return "∨I must conclude a disjunction"
    if len(refs) != 1 or refs[0].kind != "line":
        return "∨I cites one line"
    src = refs[0].formula
    if concl.left != src and concl.right != src:
        return "∨I: the cited line must be one of the disjuncts"
    return None


def _r_or_e(concl, refs, extra, oa):
    """∨E: from φ ∨ ψ and subproofs [φ ⊢ χ], [ψ ⊢ χ] infer χ."""
    if len(refs) != 3:
        return "∨E cites a disjunction line and two subproofs"
    dis, s1, s2 = refs
    if dis.kind != "line" or not isinstance(dis.formula, Or):
        return "∨E: the first citation must be a disjunction line"
    if s1.kind != "subproof" or s2.kind != "subproof":
        return "∨E: the second and third citations must be subproofs"
    left, right = dis.formula.left, dis.formula.right
    if s1.assumption != left:
        return "∨E: the first subproof must assume the left disjunct"
    if s2.assumption != right:
        return "∨E: the second subproof must assume the right disjunct"
    if s1.conclusion != concl or s2.conclusion != concl:
        return "∨E: both subproofs must derive the conclusion"
    return None


def _r_imp_i(concl, refs, extra, oa):
    """→I: from a subproof [φ ⊢ ψ] infer φ → ψ (discharge φ)."""
    if not isinstance(concl, Implies):
        return "→I must conclude an implication"
    if len(refs) != 1 or refs[0].kind != "subproof":
        return "→I cites one subproof"
    s = refs[0]
    if s.assumption != concl.left:
        return "→I: the subproof's assumption must be the antecedent"
    if s.conclusion != concl.right:
        return "→I: the subproof's last line must be the consequent"
    return None


def _r_imp_e(concl, refs, extra, oa):
    """→E (modus ponens): from φ → ψ and φ infer ψ."""
    if len(refs) != 2 or any(r.kind != "line" for r in refs):
        return "→E cites two lines"
    f1, f2 = refs[0].formula, refs[1].formula
    for imp, ant in ((f1, f2), (f2, f1)):
        if isinstance(imp, Implies) and imp.left == ant and imp.right == concl:
            return None
    return "→E: needs an implication φ→ψ and its antecedent φ, concluding ψ"


def _r_iff_i(concl, refs, extra, oa):
    """↔I: from subproofs [φ ⊢ ψ] and [ψ ⊢ φ] infer φ ↔ ψ."""
    if not isinstance(concl, Iff):
        return "↔I must conclude a biconditional"
    if len(refs) != 2 or any(r.kind != "subproof" for r in refs):
        return "↔I cites two subproofs"
    s1, s2 = refs
    a, b = concl.left, concl.right
    forward = s1.assumption == a and s1.conclusion == b
    backward = s2.assumption == b and s2.conclusion == a
    forward2 = s2.assumption == a and s2.conclusion == b
    backward2 = s1.assumption == b and s1.conclusion == a
    if (forward and backward) or (forward2 and backward2):
        return None
    return "↔I: the subproofs must derive φ⊢ψ and ψ⊢φ"


def _r_iff_e(concl, refs, extra, oa):
    """↔E: from φ ↔ ψ and one side infer the other."""
    if len(refs) != 2 or any(r.kind != "line" for r in refs):
        return "↔E cites two lines"
    f1, f2 = refs[0].formula, refs[1].formula
    for bic, side in ((f1, f2), (f2, f1)):
        if isinstance(bic, Iff):
            if side == bic.left and concl == bic.right:
                return None
            if side == bic.right and concl == bic.left:
                return None
    return "↔E: needs a biconditional and one side, concluding the other"


def _r_bot_i(concl, refs, extra, oa):
    """⊥I: from φ and ¬φ infer ⊥."""
    if not is_falsum(concl):
        return "⊥I must conclude ⊥"
    if len(refs) != 2 or any(r.kind != "line" for r in refs):
        return "⊥I cites two lines"
    f1, f2 = refs[0].formula, refs[1].formula
    if f1 == Not(f2) or f2 == Not(f1):
        return None
    return "⊥I: the cited lines must be φ and ¬φ"


def _r_bot_e(concl, refs, extra, oa):
    """⊥E (ex falso quodlibet): from ⊥ infer anything."""
    if len(refs) != 1 or refs[0].kind != "line":
        return "⊥E cites one line"
    if not is_falsum(refs[0].formula):
        return "⊥E must cite a ⊥ line"
    return None


def _r_not_i(concl, refs, extra, oa):
    """¬I: from a subproof [φ ⊢ ⊥] infer ¬φ (discharge φ)."""
    if not isinstance(concl, Not):
        return "¬I must conclude a negation"
    if len(refs) != 1 or refs[0].kind != "subproof":
        return "¬I cites one subproof"
    s = refs[0]
    if s.assumption != concl.formula:
        return "¬I: the subproof must assume φ where the conclusion is ¬φ"
    if not is_falsum(s.conclusion):
        return "¬I: the subproof must derive ⊥"
    return None


def _r_raa(concl, refs, extra, oa):
    """RAA / proof by contradiction (classical): from [¬φ ⊢ ⊥] infer φ."""
    if len(refs) != 1 or refs[0].kind != "subproof":
        return "RAA cites one subproof"
    s = refs[0]
    if s.assumption != Not(concl):
        return "RAA: the subproof must assume ¬(conclusion)"
    if not is_falsum(s.conclusion):
        return "RAA: the subproof must derive ⊥"
    return None


def _r_dne(concl, refs, extra, oa):
    """¬E / double-negation elimination (classical): from ¬¬φ infer φ."""
    if len(refs) != 1 or refs[0].kind != "line":
        return "¬E cites one line"
    if refs[0].formula != Not(Not(concl)):
        return "¬E: the cited line must be ¬¬(conclusion)"
    return None


_PROP_RULES: Dict[str, RuleFn] = {
    "Reit": _r_reit,
    "∧I": _r_and_i, "∧E": _r_and_e,
    "∨I": _r_or_i, "∨E": _r_or_e,
    "→I": _r_imp_i, "→E": _r_imp_e,
    "↔I": _r_iff_i, "↔E": _r_iff_e,
    "⊥I": _r_bot_i, "⊥E": _r_bot_e,
    "¬I": _r_not_i, "RAA": _r_raa, "¬E": _r_dne,
}

# ---------------------------------------------------------------------------
# Quantifier machinery (capture-avoiding substitution + eigenvariable support)
# ---------------------------------------------------------------------------

def _q_kind(node: Node) -> Optional[str]:
    """Normalise an *unsorted* quantifier to '∀' / '∃', or None.

    Returns None for SortedQuantifier (the sorted-quantifier rules are not offered
    — sound sort-checking of instantiation terms needs a signature the kit does not
    carry) and for non-quantifier nodes, so sorted/structural nodes never match an
    unsorted FOL rule.
    """
    if isinstance(node, Quantifier):
        if node.type in ("forall", "∀"):
            return "∀"
        if node.type in ("exists", "∃"):
            return "∃"
    return None


def _is_term(node: Node) -> bool:
    """Return True iff ``node`` is a first-order term (a legal instantiation)."""
    return isinstance(node, (Variable, Constant, Number, Function, SortedConstant))


def _free_vars(node: Node) -> set:
    """Return the free logical Variable occurrences of ``node`` (LambdaVars dropped)."""
    return {v for v in free_variables(node) if isinstance(v, Variable)}


#: Node types that bind a logical ``Variable`` over a ``formula`` scope. Besides the
#: quantifiers this covers the counting quantifiers, the cardinality terms (and their
#: sorted variants) and the IF-logic slashed existential — they bind their variable
#: exactly as ∀/∃ do, so the shadowing and capture-avoidance rules below apply to them
#: unchanged. ``SlashedExists`` additionally carries a slash set that is NOT shadowed
#: by its own binder; :func:`subst_slash_set` rewrites it first. Kept in step with the
#: binder tuple in :func:`unicode_fol_kit.fol._msfl_nodes.free_variables`.
_VAR_BINDERS = (Quantifier, SortedQuantifier, Count, Cardinality,
                SortedCount, SortedCardinality, SlashedExists)


def _subst_var(formula: Node, var: Variable, replacement: Node) -> Node:
    """Capture-avoiding substitution of a *logical Variable* by a term.

    The kit's :func:`substitute` is written for ``LambdaVar`` targets and does not
    stop at a re-binding ``∀x`` / ``∃x`` inside the body, so it is unsound for
    substituting a logical ``Variable``. This implements the correct first-order
    substitution: occurrences of ``var`` bound by an inner quantifier are left
    untouched (shadowing), and a bound variable that would capture a free variable
    of ``replacement`` is α-renamed first (reusing the kit's ``_rename`` /
    ``_fresh_name``). The input is not mutated.
    """
    return _subst_var_inner(formula, var, replacement, _free_vars(replacement))


def _subst_var_inner(t: Node, var: Variable, repl: Node, fv: set) -> Node:
    """Recursive worker for :func:`_subst_var` (``fv`` = free vars of ``repl``)."""
    if t == var:
        return repl
    if isinstance(t, (Variable, Constant, Number, LambdaVar, SortedConstant)):
        return t
    if isinstance(t, _VAR_BINDERS):
        if isinstance(t, SlashedExists):
            # The slash set names ENCLOSING binders, so it is rewritten BEFORE the
            # shadowing check — it is not shadowed by this binder's own variable.
            # An emptied slash set degrades to a plain ∃, which re-enters below.
            rewritten = subst_slash_set(t, var, repl)
            if not isinstance(rewritten, SlashedExists):
                return _subst_var_inner(rewritten, var, repl, fv)
            t = rewritten
        if t.variable == var:
            return t  # var is re-bound here: occurrences below are shadowed
        bound = t.variable
        body = t.formula
        if bound in fv:
            # The binder would capture a free variable of the replacement; rename it.
            # Slash names are plain strings, so they are added explicitly — a fresh
            # name colliding with one would silently rewire the independence set.
            avoid = fv | _free_vars(body) | {var, bound}
            if isinstance(t, SlashedExists):
                avoid = avoid | {Variable(n) for n in t.slashed}
            fresh = Variable(_fresh_name(bound.name, avoid))
            body = _rename(body, bound, fresh)
            bound = fresh
        inner = _subst_var_inner(body, var, repl, fv)
        # Every binder in the family carries its binder in ``variable`` and its scope
        # in ``formula``; the remaining fields (∀/∃ type, sort, count op and n) are
        # untouched, so a field-wise replace rebuilds each shape uniformly.
        return replace(t, variable=bound, formula=inner)
    return t.map_children(lambda c: _subst_var_inner(c, var, repl, fv))


def _not_free_in_assumptions(e: Variable, oa: List[Node]) -> Optional[str]:
    """Return an error string if eigenvariable ``e`` is free in any open assumption."""
    for g in oa:
        if e in _free_vars(g):
            return (f"eigenvariable {e.name} occurs free in an undischarged "
                    f"assumption ({g.to_unicode_str()})")
    return None


# ---------------------------------------------------------------------------
# Quantifier rules (classical FOL)
# ---------------------------------------------------------------------------

def _r_forall_e(concl, refs, extra, oa):
    """∀E (universal instantiation): from ∀x φ infer φ[x:=t]."""
    if len(refs) != 1 or refs[0].kind != "line":
        return "∀E cites one line"
    src = refs[0].formula
    if _q_kind(src) != "∀":
        return "∀E must cite a universal ∀x φ"
    if len(extra) != 1 or not _is_term(extra[0]):
        return "∀E needs the instantiation term in justification extra"
    t = extra[0]
    if concl != _subst_var(src.formula, src.variable, t):
        return "∀E: the conclusion must be φ[x:=t] for the cited ∀x φ and term t"
    return None


def _r_forall_i(concl, refs, extra, oa):
    """∀I (universal generalization): from a box flagging e that derives φ(e) infer ∀x φ.

    Side condition: the eigenvariable e must not occur free in any undischarged
    assumption (nor, consequently, in the conclusion).
    """
    if _q_kind(concl) != "∀":
        return "∀I must conclude a universal ∀x φ"
    if len(refs) != 1 or refs[0].kind != "subproof":
        return "∀I cites one subproof"
    s = refs[0]
    e = s.flag
    if not isinstance(e, Variable):
        return "∀I: the subproof must flag an eigenvariable (a Flag head with flag=)"
    if s.assumption is not None:
        # The box must be a PURE eigenvariable box (a 'Flag' head), not one that
        # also discharged a hypothesis. Otherwise a hypothesis φ(e) mentioning the
        # eigenvariable would be invisible to the freshness check below (which runs
        # against the open assumptions OUTSIDE the box, where φ(e) is discharged),
        # unsoundly licensing e.g. ⊢ ∀x P(x) from a box assuming P(e).
        return ("∀I: the subproof must be a pure eigenvariable box (a Flag head), "
                "not one that discharges a hypothesis")
    if s.conclusion != _subst_var(concl.formula, concl.variable, e):
        return "∀I: the subproof must derive the body φ with the eigenvariable, φ(e)"
    err = _not_free_in_assumptions(e, oa)
    if err:
        return "∀I: " + err
    if e in _free_vars(concl):
        return f"∀I: eigenvariable {e.name} still occurs free in the conclusion"
    return None


def _r_exists_i(concl, refs, extra, oa):
    """∃I (existential generalization): from φ[x:=t] infer ∃x φ."""
    if _q_kind(concl) != "∃":
        return "∃I must conclude an existential ∃x φ"
    if len(refs) != 1 or refs[0].kind != "line":
        return "∃I cites one line"
    if len(extra) != 1 or not _is_term(extra[0]):
        return "∃I needs the witness term in justification extra"
    t = extra[0]
    if refs[0].formula != _subst_var(concl.formula, concl.variable, t):
        return "∃I: the cited line must be φ[x:=t] for the concluded ∃x φ and term t"
    return None


def _r_exists_e(concl, refs, extra, oa):
    """∃E (existential instantiation): from ∃x φ and a box [φ(e) ⊢ χ] infer χ.

    Side conditions: the eigenvariable e must not occur free in the conclusion χ,
    in the major premise ∃x φ, or in any undischarged assumption.
    """
    if len(refs) != 2:
        return "∃E cites an existential line and one subproof"
    ex, s = refs
    if ex.kind != "line" or _q_kind(ex.formula) != "∃":
        return "∃E: the first citation must be an existential ∃x φ"
    if s.kind != "subproof":
        return "∃E: the second citation must be a subproof"
    e = s.flag
    if not isinstance(e, Variable):
        return "∃E: the subproof must flag an eigenvariable"
    expected_assumption = _subst_var(ex.formula.formula, ex.formula.variable, e)
    if s.assumption != expected_assumption:
        return "∃E: the subproof must assume φ[x:=e] (the body with the eigenvariable)"
    if s.conclusion != concl:
        return "∃E: the subproof's last line must be the rule's conclusion"
    if e in _free_vars(concl):
        return f"∃E: eigenvariable {e.name} occurs free in the conclusion"
    if e in _free_vars(ex.formula):
        return f"∃E: eigenvariable {e.name} occurs free in the major premise ∃x φ"
    err = _not_free_in_assumptions(e, oa)
    if err:
        return "∃E: " + err
    return None


_QUANTIFIER_RULES: Dict[str, RuleFn] = {
    "∀E": _r_forall_e, "∀I": _r_forall_i,
    "∃I": _r_exists_i, "∃E": _r_exists_e,
}


# ---------------------------------------------------------------------------
# Equality rules (=I reflexivity, =E Leibniz substitution)
# ---------------------------------------------------------------------------
#
# The kit treats '=' as an ordinary uninterpreted Atom predicate everywhere else
# (resolution has no congruence), so a Fitch system with equality must add these
# rules explicitly. They are certified against Z3 (which interprets '=' natively),
# NOT resolution — exactly the divergence the design flags.

def _is_equality(node: Node) -> bool:
    """Return True iff ``node`` is an equality atom ``s = t``."""
    return isinstance(node, Atom) and node.predicate == "=" and len(node.args) == 2


def _r_eq_i(concl, refs, extra, oa):
    """=I (reflexivity): infer t = t from nothing."""
    if not _is_equality(concl):
        return "=I must conclude an equality t = t"
    if concl.args[0] != concl.args[1]:
        return "=I (reflexivity): the two sides must be the same term"
    return None


def _r_eq_e(concl, refs, extra, oa):
    """=E (Leibniz): from s = t and φ infer the result of replacing s by t in φ.

    Certified semantically against Z3 (cited equality and formula ⊨ conclusion);
    since '=' is uninterpreted to resolution, Z3 is the only sound oracle here.
    """
    if len(refs) != 2 or any(r.kind != "line" for r in refs):
        return "=E cites two lines (an equality and a formula)"
    eq = None
    phi = None
    for r in refs:
        if eq is None and _is_equality(r.formula):
            eq = r.formula
        else:
            phi = r.formula
    if eq is None or phi is None:
        return "=E: exactly one cited line must be an equality s = t"
    if not _classical_valid([eq, phi], concl):
        return "=E: the conclusion does not follow from the equality and the formula"
    return None


_EQUALITY_RULES: Dict[str, RuleFn] = {"=I": _r_eq_i, "=E": _r_eq_e}


# The classical rule table: propositional + quantifier + equality rules.
_CLASSICAL_RULES: Dict[str, RuleFn] = {
    **_PROP_RULES, **_QUANTIFIER_RULES, **_EQUALITY_RULES,
}


# ---------------------------------------------------------------------------
# The checker
# ---------------------------------------------------------------------------

_CLASSICAL_LOGICS = frozenset({"fol", "msfol", "classical", "prop"})


def _open_assumptions(rec: _Rec, sub_by_sid, premise_formulas) -> List[Node]:
    """Return the undischarged hypotheses in scope at ``rec`` (premises + enclosing)."""
    out = list(premise_formulas)
    for sid in rec.scope:
        sp = sub_by_sid.get(sid)
        if sp is not None and sp.assumption is not None:
            out.append(sp.assumption)
    return out


def _conclusion_of(proof: "Proof") -> Optional[Node]:
    """Return the formula of the last top-level line, or None if there is none."""
    if proof.steps and isinstance(proof.steps[-1], Line):
        return proof.steps[-1].formula
    return None


def verify_proof(proof: "Proof", logic: Optional[str] = None) -> ProofResult:
    """Check ``proof`` and return a :class:`ProofResult` (sequent + first error).

    ``logic`` overrides ``proof.logic`` if given. Classical logics (``"fol"`` /
    ``"msfol"``) are checked by the syntactic rule table; ``"K3"`` / ``"LP"`` are
    certified semantically against
    :func:`unicode_fol_kit.semantics.manyvalued.entails`; and the modal family
    (``"K"`` / ``"T"`` / ``"S4"`` / ``"S5"``) is certified against the standard
    translation to FOL plus the frame axioms, decided by Z3. The returned result
    names the certified sequent (premises ⊢ conclusion) and, on failure, the first
    offending line and the reason.
    """
    logic = (logic or proof.logic or "fol").strip()
    # Filter to Line premises so a malformed premise is reported by _index (below)
    # rather than crashing here on a missing .formula.
    premise_formulas = tuple(_canon_q(p.formula) for p in proof.premises if isinstance(p, Line))

    try:
        order, lines, subs_by_span, sub_by_sid = _index(proof)
    except _IndexError as e:
        return ProofResult(False, premise_formulas, _conclusion_of(proof),
                           e.number, e.message, logic)

    conclusion = _conclusion_of(proof)
    if conclusion is None:
        return ProofResult(False, premise_formulas, None, None,
                           "the proof has no top-level concluding line", logic)

    key = logic.lower()
    classical = key in _CLASSICAL_LOGICS
    semantic_checker = None
    if not classical:
        semantic_checker = _make_semantic_checker(logic)
        if semantic_checker is None:
            return ProofResult(False, premise_formulas, conclusion, None,
                               f"unknown logic {logic!r}", logic)

    for rec in order:
        # Premises / assumptions / flags are free; only sanity-check their tags.
        if rec.role in ("premise", "assume", "flag"):
            expected = {"premise": "Premise", "assume": "Assume", "flag": "Assume"}[rec.role]
            if rec.just.rule not in (expected, "Flag"):
                return ProofResult(False, premise_formulas, conclusion, rec.number,
                                   f"line {rec.number} should be justified "
                                   f"'{expected}', not {rec.just.rule!r}", logic)
            continue

        if rec.just.rule in _RESERVED_RULES:
            return ProofResult(False, premise_formulas, conclusion, rec.number,
                               f"line {rec.number} is a derivation step but uses "
                               f"the reserved justification {rec.just.rule!r}", logic)

        # Resolve and accessibility-check every citation. This runs for ALL
        # regimes — even the semantic (K3/LP) path rejects a citation that does not
        # exist or reaches into a closed sibling box; only the final *verdict* on a
        # line differs (the syntactic rule table vs. the open-assumption oracle).
        refs: List[_Ref] = []
        for tok in rec.just.cites:
            ref, err = _resolve(tok, rec, lines, subs_by_span)
            if err is not None:
                return ProofResult(False, premise_formulas, conclusion, rec.number,
                                   f"line {rec.number}: {err}", logic)
            refs.append(ref)

        oa = _open_assumptions(rec, sub_by_sid, premise_formulas)

        if classical:
            fn = _CLASSICAL_RULES.get(rec.just.rule)
            if fn is None:
                return ProofResult(False, premise_formulas, conclusion, rec.number,
                                   f"line {rec.number}: unknown rule "
                                   f"{rec.just.rule!r} for logic {logic!r}", logic)
            err = fn(rec.formula, refs, rec.just.extra, oa)
            if err is not None:
                return ProofResult(False, premise_formulas, conclusion, rec.number,
                                   f"line {rec.number}: {err}", logic)
        else:
            ok, reason = semantic_checker(oa, rec.formula)
            if not ok:
                return ProofResult(False, premise_formulas, conclusion, rec.number,
                                   f"line {rec.number}: {reason}", logic)

    return ProofResult(True, premise_formulas, conclusion, None, None, logic)


def check_proof(proof: "Proof", logic: Optional[str] = None) -> bool:
    """Return True iff ``proof`` is a valid Fitch derivation (sound).

    A thin bool wrapper over :func:`verify_proof`; use that for the failing line
    and reason.
    """
    return verify_proof(proof, logic).ok


# ---------------------------------------------------------------------------
# Semantic checkers for the non-classical logics (filled by later phases)
# ---------------------------------------------------------------------------

def _has_quantifier(node: Node) -> bool:
    """Return True iff a (first- or second-order) quantifier occurs anywhere in ``node``."""
    return any(isinstance(n, (Quantifier, SortedQuantifier)) for n in node.walk())


_MANYVALUED_LOGICS = {"k3": "K3", "lp": "LP"}


def _make_manyvalued_checker(canonical: str):
    """Return a K3/LP step certifier using ``manyvalued.entails`` as the oracle.

    Each derived line must be a ``canonical``-consequence of its open assumptions.
    ``entails`` enumerates all 3ⁿ assignments — complete and sound for the
    *propositional* fragment — so quantified input is rejected (a single
    finite-domain enumeration would not soundly certify a first-order step).
    """
    from ..semantics.manyvalued import entails

    def check(oa: List[Node], formula: Node):
        for node in (formula, *oa):
            if _has_quantifier(node):
                return (False,
                        f"{canonical} checking supports only the propositional "
                        f"fragment, but a quantifier is present")
        try:
            ok = entails(list(oa), formula, logic=canonical)
        except NotImplementedError as e:
            return False, f"{canonical}: {e}"
        except ValueError as e:
            return False, f"{canonical}: {e}"
        if not ok:
            return (False, f"the line is not a {canonical} consequence of its "
                           f"open assumptions")
        return True, None

    return check


# ---------------------------------------------------------------------------
# Modal family (alethic K/T/S4/S5, epistemic S5, doxastic KD45, deontic KD)
# ---------------------------------------------------------------------------
#
# Modal proofs are certified by *local consequence*: a derived line φ is licensed
# iff its open assumptions entail it at the current world in every model of the
# frame class. Brute Kripke-frame enumeration is neither practical (the frame
# space explodes) nor soundly boundable, so instead each obligation is reduced to
# classical FOL via the standard translation ST and the frame conditions are added
# as first-order axioms; Z3 then decides it. ``is_valid`` only ever returns True on
# a genuine ``unsat`` of the negation (a Z3 ``unknown`` ⇒ False), so this is
# sound: an accepted step is genuinely a local modal consequence.
#
# Local consequence validates the classical propositional rules, the deduction
# theorem (→I/¬I), every modal theorem of the system (the K/T/4/5/D axioms come out
# as zero-premise local validities, as does the necessitation of any theorem,
# e.g. ⊢ □(p∨¬p)), and the factivity discipline (Knows is reflexive ⇒ factive;
# Believes/Obligatory are non-reflexive ⇒ NOT factive). It deliberately does NOT
# license necessitation from a *contingent* assumption (φ ⊬ □φ) — there is no sound
# □I-by-strict-subproof over local consequence, and such a step is correctly
# rejected. Temporal operators (Always/Eventually/Next/Until) and quantified modal
# input are out of scope (no sound first-order rendering) and are rejected.

_MODAL_SYSTEMS = {"k": "K", "t": "T", "s4": "S4", "s5": "S5", "modal": "K"}

# Per frame class, the relational axioms its accessibility relation must satisfy.
_FRAME_AXIOMS = {
    "K": (),
    "T": ("refl",),
    "S4": ("refl", "trans"),
    "S5": ("refl", "trans", "sym"),
    "KD": ("serial",),          # deontic: serial, non-reflexive (no factivity)
    "KD45": ("serial", "trans", "eucl"),  # doxastic: belief, non-factive
}


def _ax_refl(R):
    x = Variable("wx")
    return Quantifier("∀", x, Atom(R, [x, x]))


def _ax_trans(R):
    x, y, z = Variable("wx"), Variable("wy"), Variable("wz")
    return Quantifier("∀", x, Quantifier("∀", y, Quantifier("∀", z,
        Implies(And(Atom(R, [x, y]), Atom(R, [y, z])), Atom(R, [x, z])))))


def _ax_sym(R):
    x, y = Variable("wx"), Variable("wy")
    return Quantifier("∀", x, Quantifier("∀", y,
        Implies(Atom(R, [x, y]), Atom(R, [y, x]))))


def _ax_eucl(R):
    x, y, z = Variable("wx"), Variable("wy"), Variable("wz")
    return Quantifier("∀", x, Quantifier("∀", y, Quantifier("∀", z,
        Implies(And(Atom(R, [x, y]), Atom(R, [x, z])), Atom(R, [y, z])))))


def _ax_serial(R):
    x, y = Variable("wx"), Variable("wy")
    return Quantifier("∀", x, Quantifier("∃", y, Atom(R, [x, y])))


_AX_BUILDERS = {
    "refl": _ax_refl, "trans": _ax_trans, "sym": _ax_sym,
    "eucl": _ax_eucl, "serial": _ax_serial,
}


def _collect_modal_frames(nodes, alethic_system):
    """Return ``({relation_name: frame_class}, unsupported_reason_or_None)``.

    Each modality contributes its accessibility relation and the frame class it is
    interpreted over: Box/Diamond use the alethic relation with the chosen system;
    Knows is S5 (factive knowledge); Believes is KD45 (consistent, introspective,
    non-factive belief); Obligatory/Permitted are KD (serial, non-factive). The
    relation-predicate names match the standard translation's fixed scheme.
    """
    frames: Dict[str, str] = {}
    unsupported = None
    for node in nodes:
        for n in node.walk():
            if isinstance(n, (Box, Diamond)):
                frames["R"] = alethic_system
            elif isinstance(n, Knows):
                frames["Rk_" + (getattr(n.agent, "name", None) or n.agent.to_unicode_str())] = "S5"
            elif isinstance(n, Believes):
                frames["Rb_" + (getattr(n.agent, "name", None) or n.agent.to_unicode_str())] = "KD45"
            elif isinstance(n, (Obligatory, Permitted)):
                frames["D"] = "KD"
            elif isinstance(n, (Always, Eventually, Next, Until,
                                Historically, Once, Previous, Since)):
                unsupported = "temporal operators (Always/Eventually/Next/Until and past-tense H/P/Y/Since)"
            elif isinstance(n, (Quantifier, SortedQuantifier)):
                unsupported = "quantifiers (first-order modal logic)"
    return frames, unsupported


def _make_modal_checker(alethic_system: str):
    """Return a modal step certifier for the given alethic frame class.

    Each step's obligation — frame axioms ∧ ST(open assumptions) → ST(line) — is
    decided by Z3. Knows/Believes/Obligatory carry their standard frame classes
    regardless of ``alethic_system``.
    """
    from .z3_models import is_valid

    def check(oa: List[Node], formula: Node):
        nodes = [formula, *oa]
        frames, unsupported = _collect_modal_frames(nodes, alethic_system)
        if unsupported:
            return False, f"modal checking does not support {unsupported}"
        # A user predicate sharing a name with an accessibility relation introduced
        # by the standard translation would conflate the two symbols in Z3 (and, at
        # a different arity, raise inside to_z3). Reject it with a clear message
        # rather than crash or risk a conflated verdict.
        for node in nodes:
            for n in node.walk():
                if isinstance(n, Atom) and n.predicate in frames:
                    return (False, f"predicate name {n.predicate!r} collides with a "
                                   f"modal accessibility relation in the standard "
                                   f"translation; rename it")
        axioms: List[Node] = []
        for rel, fclass in frames.items():
            for kind in _FRAME_AXIOMS[fclass]:
                axioms.append(_AX_BUILDERS[kind](rel))
        try:
            from ..fol.modal_translation import standard_translation
            st_concl = standard_translation(_desugar_falsum(formula), world="w")
            st_oa = [standard_translation(_desugar_falsum(g), world="w") for g in oa]
        except NotImplementedError as e:
            return False, f"modal: {e}"
        antecedents = axioms + st_oa
        obligation = (Implies(reduce(And, antecedents), st_concl)
                      if antecedents else st_concl)
        try:
            valid = is_valid(obligation)
        except Exception as e:  # noqa: BLE001 — never crash on a Z3 backend error
            return False, f"modal certification could not be decided ({e})"
        if valid:
            return True, None
        return (False, f"the line is not a local {alethic_system}-modal consequence "
                       f"of its open assumptions")

    return check


def _make_semantic_checker(logic: str):
    """Return a ``(open_assumptions, formula) -> (ok, reason)`` certifier, or None.

    ``"K3"``/``"LP"`` are certified against the three-valued decision procedure
    :func:`unicode_fol_kit.semantics.manyvalued.entails`. ``"K"``/``"T"``/``"S4"``/
    ``"S5"`` (and ``"modal"``) certify the modal family by standard translation to
    FOL plus frame axioms, decided by Z3. Returns None for an unrecognised logic.
    """
    key = logic.lower()
    if key in _MANYVALUED_LOGICS:
        return _make_manyvalued_checker(_MANYVALUED_LOGICS[key])
    if key in _MODAL_SYSTEMS:
        return _make_modal_checker(_MODAL_SYSTEMS[key])
    return None


# ---------------------------------------------------------------------------
# Rendering: Fitch notation (Unicode/ASCII) and LaTeX
# ---------------------------------------------------------------------------

def _fmt_cite(tok) -> str:
    """Format one citation token: a line number, or a ``start–end`` subproof span."""
    if isinstance(tok, tuple) and len(tok) == 2:
        return f"{tok[0]}–{tok[1]}"
    return str(tok)


def _just_text(just: "Justification") -> str:
    """Render a justification as ``rule cites [terms]`` (e.g. ``∀E 1 [socrates]``)."""
    parts = [just.rule]
    if just.cites:
        parts.append(", ".join(_fmt_cite(c) for c in just.cites))
    text = " ".join(parts)
    if just.extra:
        terms = ", ".join(e.to_unicode_str() if isinstance(e, Node) else str(e)
                          for e in just.extra)
        text += f" [{terms}]"
    return text


def _visual_rows(proof: "Proof") -> List[dict]:
    """Flatten the proof into ordered render rows (line rows and Fitch-bar rows).

    A ``line`` row carries its number, nesting depth, formula, and justification
    text; a ``bar`` row carries the depth at which the horizontal Fitch rule sits
    (under the premises, and under each subproof's assumption).
    """
    rows: List[dict] = []
    for pl in proof.premises:
        rows.append({"kind": "line", "number": pl.number, "depth": 0,
                     "formula": pl.formula, "just": _just_text(pl.justification)})
    if proof.premises and proof.steps:
        rows.append({"kind": "bar", "depth": 0})

    def walk(steps, depth):
        for st in steps:
            if isinstance(st, Line):
                rows.append({"kind": "line", "number": st.number, "depth": depth,
                             "formula": st.formula,
                             "just": _just_text(st.justification)})
            elif isinstance(st, Subproof) and st.assumption is not None:
                a = st.assumption
                rows.append({"kind": "line", "number": a.number, "depth": depth + 1,
                             "formula": a.formula,
                             "just": _just_text(a.justification)})
                rows.append({"kind": "bar", "depth": depth + 1})
                walk(st.body, depth + 1)

    walk(proof.steps, 0)
    return rows


def render_fitch(proof: "Proof", ascii: bool = False) -> str:
    """Render ``proof`` in classic Fitch notation as a multi-line string.

    A line-number gutter, one vertical scope bar per open subproof, a horizontal
    rule under the premises and under each assumption, and a right-hand
    justification column (``rule cites``). Pass ``ascii=True`` for an ASCII-only
    rendering (``|``/``+``/``-`` instead of ``│``/``├``/``─``).
    """
    vbar = "|" if ascii else "│"
    corner = "+" if ascii else "├"
    hbar = "-" if ascii else "─"

    rows = _visual_rows(proof)
    width = 1
    for r in rows:
        if r["kind"] == "line":
            r["ftext"] = r["formula"].to_unicode_str()
            width = max(width, len(str(r["number"])))

    left_of: Dict[int, str] = {}
    content_w = 0
    for i, r in enumerate(rows):
        if r["kind"] == "line":
            level = r["depth"] + 1
            left = f"{str(r['number']).rjust(width)} {(vbar + ' ') * level}"
            left_of[i] = left
            content_w = max(content_w, len(left) + len(r["ftext"]))

    out: List[str] = []
    for i, r in enumerate(rows):
        if r["kind"] == "line":
            body = left_of[i] + r["ftext"]
            if r["just"]:
                body += " " * (content_w - len(body) + 3) + r["just"]
            out.append(body.rstrip())
        else:
            level = r["depth"] + 1
            prefix = " " * (width + 1) + (vbar + " ") * (level - 1)
            out.append(prefix + corner + hbar * 6)
    return "\n".join(out)


_RULE_GLYPH_LATEX = {
    "∧": r"\land", "∨": r"\lor", "→": r"\rightarrow",
    "↔": r"\leftrightarrow", "¬": r"\lnot", "⊕": r"\oplus",
    "∀": r"\forall", "∃": r"\exists", "⊥": r"\bot",
    "–": "--",
}


def _latex_just(text: str) -> str:
    """Render a justification string for LaTeX, mapping operator glyphs to macros."""
    for glyph, macro in _RULE_GLYPH_LATEX.items():
        text = text.replace(glyph, f"${macro}$")
    return r"\text{" + text + "}"


def render_latex_fitch(proof: "Proof") -> str:
    """Render ``proof`` as a LaTeX ``array`` Fitch derivation (no external package).

    The number column is separated from the body by the main Fitch bar (the array
    ``|`` rule); each nested subproof adds a ``\\mid`` to its lines, and a
    ``\\cline{2-2}`` draws the horizontal rule under the premises and each
    assumption. Compiles with a unicode-aware engine (xelatex/lualatex) for the
    rendered formulas. The output is a stable, exact string (not re-parsed).
    """
    rows = _visual_rows(proof)
    out = [r"\[", r"\begin{array}{r|l@{\qquad}l}"]
    for r in rows:
        if r["kind"] == "line":
            bars = r"\mid " * r["depth"]
            out.append(f"{r['number']} & {bars}{r['formula'].to_latex()} & "
                       f"{_latex_just(r['just'])} \\\\")
        else:
            out.append(r"\cline{2-2}")
    out.append(r"\end{array}")
    out.append(r"\]")
    return "\n".join(out)
