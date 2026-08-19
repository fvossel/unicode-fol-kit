"""ACE text → ONE kit formula — including what a classical DRS cannot hold.

The DRS route (:func:`unicode_fol_kit.ace.mapping.ace_to_drs`) stops honestly
at modality and questions: the kit's classical DRS core has no place for
them. THIS route translates APE's DRS straight to a kit FORMULA, where the
kit does have places — the modal family for ACE's four modal boxes, and an
open formula for a wh-question:

- ``must`` → ``□`` (:class:`~unicode_fol_kit.fol._modal_nodes.Box`) —
  Attempto's reading: necessity;
- ``can`` → ``◇`` (:class:`~unicode_fol_kit.fol._modal_nodes.Diamond`) —
  possibility;
- ``should`` → ``Ⓞ`` (:class:`~unicode_fol_kit.fol._modal_nodes.Obligatory`)
  — recommendation, read deontically;
- ``may`` → ``Ⓟ`` (:class:`~unicode_fol_kit.fol._modal_nodes.Permitted`) —
  admissibility, read deontically.

The first two are alethic, the second two deontic — that split is a
DOCUMENTED CHOICE, not something ACE fixes: Attempto glosses ``should``/
``may`` as recommendation/admissibility, which is what the kit's deontic
operators mean, while ``must``/``can`` gloss as necessity/possibility. A
caller who wants "must" read as obligation can rewrite ``Box`` → ``Obligatory``
on the result; nothing here is lost, only labeled.

The translation is the standard Kamp/Reyle one — the same
:func:`unicode_fol_kit.drt.export.drs_to_fol` performs on the pure fragment,
extended pointwise at the box operators — and it REUSES the mapping module's
atomic-condition table and renamer, so both routes speak one vocabulary.
That overlap is pinned by a three-way differential in the tests: on every
corpus sentence the DRS route covers, this route's formula, the DRS route's
formula and Attempto's own TPTP are pairwise Z3-equivalent.

Questions come out as :class:`AceFormula` with a ``kind``:

- a wh-question ("Who waits?") yields an OPEN formula — the queried referent
  stays free, named in ``query_variables`` with its question word — so
  answering is model finding (``api.countermodel`` on the negation, or
  ``semantics``' model enumeration) rather than proof;
- a yes/no question ("Does John wait?") yields a closed formula and
  ``kind="yesno_question"`` — answering is an entailment check against
  whatever theory the caller holds. This is exactly the sentence the TPTP
  route refuses (APE renders it as a ``conjecture``, which ``ace_to_fol``
  must not flatten into an assertion); here the interrogative force survives
  in ``kind`` instead of being dropped.
- a question box mixed with assertions in one text raises: the merged box
  shares referents across both parts, and splitting them would either break
  the binding or quantify the premises into the question — split the TEXT.

Commands (``command``) and negation as failure (``~``) still raise
:class:`~unicode_fol_kit.ace.mapping.AceUnsupportedError`: the kit has no
imperative semantics, and ``~`` is not classical negation — those verdicts
are unchanged from the DRS route, and unchanged on purpose.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import List, Optional, Tuple

from ..drt.export import _CARD_TO_COUNT
from ..drt.nodes import is_referent
from ..fol.nodes import (
    And, Atom, Box, Constant, Count, Diamond, Function, Implies, Node, Not,
    Number, Obligatory, Or, Permitted, Quantifier, Variable,
)
from .drs_reader import (
    AceAtom, AceCommand, AceCondition, AceCondList, AceDrs, AceExpr, AceImpl,
    AceInt, AceModal, AceNaf, AceNamed, AceNeg, AceOr, AceQuestion, AceReal,
    AceVar, parse_ape_drs,
)
from .mapping import (
    AceUnsupportedError, ConditionReport, _ACE_OPS, _be_events_to_drop,
    _map_atom, _Renamer, _shell_render, _Unsupported,
)
from .runner import AceParseError, run_ape

__all__ = ["ace_to_formula", "ace_drs_to_formula", "AceFormula"]

_MODAL_NODES = {"must": Box, "can": Diamond, "should": Obligatory,
                "may": Permitted}


@dataclass(frozen=True)
class AceFormula:
    """What an ACE text says, as one kit formula plus its illocution.

    ``kind`` is ``"assertion"``, ``"wh_question"`` or ``"yesno_question"``.
    For a wh-question the formula is OPEN: each ``query_variables`` entry is
    ``(kit variable name, question word)`` — ``(("x1", "who"),)`` for "Who
    waits?" — and those variables are deliberately unquantified.
    ``modalities`` lists which of ACE's modal boxes occurred, in first-use
    order, so a caller can tell a plain formula from one that needs a modal
    backend without walking the tree."""

    formula: Node
    kind: str = "assertion"
    query_variables: Tuple[Tuple[str, str], ...] = ()
    modalities: Tuple[str, ...] = ()


class _Stop(Exception):
    """Internal: abort translation at the first unsupported condition."""

    def __init__(self, render: str, reason: str, milestone: str,
                 sentence=None, token=None):
        super().__init__(reason)
        self.row = ConditionReport(render, "unsupported", reason=reason,
                                   milestone=milestone, sentence=sentence,
                                   token=token)


class _Translator:
    def __init__(self, root: AceDrs):
        self.renamer = _Renamer(root)
        self.dropped = _be_events_to_drop(root)
        self.modalities: List[str] = []

    # -- pieces ------------------------------------------------------------
    def term(self, name: str) -> Node:
        return Variable(name) if is_referent(name) else Constant(name)

    def atom(self, cond: AceAtom) -> Node:
        if cond.functor == "formula":
            return self.arithmetic(cond)
        mapped = _map_atom(cond, self.renamer, self.dropped)
        if isinstance(mapped, _Unsupported):
            raise _Stop(cond.render(), mapped.reason, mapped.milestone,
                        cond.sentence, cond.token)
        kind = mapped[0]
        if kind == "eq":
            return Atom("=", (self.term(mapped[1]), self.term(mapped[2])))
        if kind == "pred":
            return Atom(mapped[1], tuple(self.term(a) for a in mapped[2]))
        if kind == "card":
            return self.card(mapped[1], mapped[2], mapped[3])
        if kind == "part":
            return Atom("Part_of", (self.term(mapped[1]),
                                    self.term(mapped[2])))
        # group_noun: |g| op n, every part a noun; the group referent stays
        # a term for the verb (ACE's collective reading), mirroring the
        # mapping route's Card + membership-duplex expansion.
        _, group, noun, op, count = mapped
        member = self.renamer.fresh("x")
        membership = Quantifier(
            "∀", Variable(member),
            Implies(Atom("Part_of", (Variable(member), self.term(group))),
                    Atom(noun, (Variable(member),))))
        return And(self.card(group, op, count), membership)

    def card(self, group: str, op: str, n: int) -> Node:
        """``|group| op n`` as the kit's counting quantifier over parts —
        the same lowering drt.export gives the Card condition."""
        count_op, shift = _CARD_TO_COUNT[op]
        counter = self.renamer.fresh("p")
        return Count(count_op, Number(n + shift), Variable(counter),
                     Atom("Part_of", (Variable(counter), self.term(group))))

    def arithmetic(self, cond: AceAtom) -> Node:
        """``formula(expr, op, expr)`` → a native kit comparison atom over
        Function/Number terms — ``1 + 2 = 3.`` becomes exactly what the
        kit's own parser produces for ``1 + 2 = 3``. The default FOL→z3
        route reads ``+`` as an UNINTERPRETED symbol; the decision procedure
        for this fragment is :func:`unicode_fol_kit.atp.z3_arith.is_valid_arith`
        (measured: it proves ``1+2=3`` and refutes ``1+2=4``; the default
        route proves neither)."""
        if len(cond.args) != 3 or not isinstance(cond.args[1], str):
            raise _Stop(cond.render(), "a formula condition outside the "
                        "measured shapes", "")
        left, op, right = cond.args
        if op not in ("=", "<", ">"):
            raise _Stop(cond.render(),
                        f"comparison operator {op!r} is not in the measured "
                        "corpus", "")
        return Atom(op, (self.arith_term(left, cond),
                         self.arith_term(right, cond)))

    def arith_term(self, term, cond: AceAtom) -> Node:
        if isinstance(term, AceInt):
            return Number(term.value)
        if isinstance(term, AceReal):
            return Number(term.value)
        if isinstance(term, AceExpr):
            if term.op not in ("+", "-", "*", "/"):
                raise _Stop(cond.render(),
                            f"arithmetic operator {term.op!r} is not in the "
                            "measured corpus", "")
            return Function(term.op, (self.arith_term(term.left, cond),
                                      self.arith_term(term.right, cond)))
        if isinstance(term, AceVar):
            return Variable(self.renamer.referent(term))
        if isinstance(term, AceNamed):
            return self.term(self.renamer.constant(term))
        raise _Stop(cond.render(), "an arithmetic term outside the measured "
                    "shapes", "")

    def conjoin(self, nodes: List[Node], box: AceDrs) -> Node:
        if not nodes:
            raise _Stop(box.render(), "an empty box (no conditions) is not "
                        "in the measured corpus", "")
        result = nodes[0]
        for node in nodes[1:]:
            result = And(result, node)
        return result

    def exists(self, box: AceDrs, body: Node) -> Node:
        for ref in reversed(self._box_refs(box)):
            body = Quantifier("∃", Variable(ref), body)
        return body

    def _box_refs(self, box: AceDrs) -> List[str]:
        return [self.renamer.referent(r) for r in box.referents
                if r.name not in self.dropped]

    # -- the standard translation, extended at the box operators -----------
    def box(self, box: AceDrs) -> Node:
        lists = [c for c in box.conditions if isinstance(c, AceCondList)]
        if lists:
            return self.box_with_lists(box, lists)
        return self.exists(box, self.conjoin(
            [self.condition(c) for c in box.conditions], box))

    def box_with_lists(self, box: AceDrs, lists) -> Node:
        """The counting reading of ``exactly``/``at most`` — APE's list
        condition, translated as a counting quantifier over INDIVIDUALS.

        "Exactly 2 dogs bark." arrives as ``[predicate(B,bark,A),
        object(A,dog,...,exactly,2)]`` inside ``drs([A,B], [ [...] ])``: the
        list marks that the cardinality is a MAXIMALITY claim over
        everything satisfying the scope, not the size of one witness group.
        First-order, that is ``∃=2 a (Dog(a) ∧ ∃b Bark(b, a))`` — count the
        individuals, distribute the scope over them. This is a DOCUMENTED
        SEMANTIC CHOICE: a collective reading of a maximality claim ("exactly
        2 men lift the table TOGETHER, and no other group does") is not
        first-order expressible, and the corpus scopes (bark, wait) are
        naturally distributive; the choice is stated here, in the guide and
        in the CHANGELOG rather than buried.

        Mechanics: the list's counted ``object`` names the count variable;
        the list's other conditions form the matrix; enclosing referents
        used ONLY inside the list (the scope's events) are ∃-bound INSIDE
        the matrix. A referent shared between the list and the rest of the
        box would make the rebinding change meaning — refused, unmeasured.
        """
        outside_vars: set = set()
        for cond in box.conditions:
            if not isinstance(cond, AceCondList):
                outside_vars |= _vars_of(cond)
        list_only: set = set()
        pieces: List[Node] = []
        for group in lists:
            counted = [c for c in group.conditions
                       if isinstance(c, AceAtom) and c.functor == "object"
                       and len(c.args) == 6 and c.args[4] in _ACE_OPS
                       and not (c.args[4] == "eq" and c.args[5] == 1)]
            if len(counted) != 1:
                raise _Stop("[…]", f"{len(counted)} counted objects in one "
                            "list condition — the measured corpus has "
                            "exactly one", "")
            obj = counted[0]
            ref, noun, _cls, _unit, op, count = obj.args
            if not isinstance(ref, AceVar) or ref.name in outside_vars:
                raise _Stop(obj.render(),
                            "the counted referent is shared with conditions "
                            "outside the list — rebinding it would change "
                            "their meaning", "")
            rest = [c for c in group.conditions if c is not obj]
            inner_vars = set()
            for c in rest:
                inner_vars |= _vars_of(c)
            inner_vars.discard(ref.name)
            shared = inner_vars & outside_vars
            if shared:
                raise _Stop("[…]",
                            f"referents {sorted(shared)!r} are used inside "
                            "AND outside the list condition — not in the "
                            "measured corpus", "")
            count_var = self.renamer.referent(ref)
            matrix_parts = [Atom(_kit_pred(noun), (Variable(count_var),))]
            matrix_parts += [self.condition(c) for c in rest]
            matrix: Node = matrix_parts[0]
            for part in matrix_parts[1:]:
                matrix = And(matrix, part)
            for inner in sorted(inner_vars):
                declared = [r for r in box.referents if r.name == inner]
                if declared:
                    matrix = Quantifier(
                        "∃", Variable(self.renamer.referent(declared[0])),
                        matrix)
            count_op, shift = _CARD_TO_COUNT[_ACE_OPS[op]]
            pieces.append(Count(count_op, Number(count + shift),
                                Variable(count_var), matrix))
            list_only |= inner_vars | {ref.name}
        other = [self.condition(c) for c in box.conditions
                 if not isinstance(c, AceCondList)]
        body = pieces[0]
        for piece in pieces[1:] + other:
            body = And(body, piece)
        remaining = AceDrs(
            tuple(r for r in box.referents if r.name not in list_only),
            ())
        return self.exists(remaining, body)

    def condition(self, cond: AceCondition) -> Node:
        if isinstance(cond, AceAtom):
            return self.atom(cond)
        if isinstance(cond, AceNeg):
            return Not(self.box(cond.drs))
        if isinstance(cond, AceImpl):
            # The duplex rule (donkey sentences): the antecedent's referents
            # go universal over the whole conditional — same construction as
            # drt.export.drs_to_fol.
            result = Implies(
                self.conjoin([self.condition(c)
                              for c in cond.antecedent.conditions],
                             cond.antecedent),
                self.box(cond.consequent))
            for ref in reversed(self._box_refs(cond.antecedent)):
                result = Quantifier("∀", Variable(ref), result)
            return result
        if isinstance(cond, AceOr):
            return Or(self.box(cond.left), self.box(cond.right))
        if isinstance(cond, AceModal):
            if cond.modality not in self.modalities:
                self.modalities.append(cond.modality)
            return _MODAL_NODES[cond.modality](self.box(cond.drs))
        if isinstance(cond, AceQuestion):
            raise _Stop("question(…)",
                        "a question box below the top level — the merged "
                        "text shares referents across assertion and "
                        "question; split the text", "")
        if isinstance(cond, AceCommand):
            raise _Stop("command(…)",
                        "an imperative: no command semantics decided", "")
        if isinstance(cond, AceNaf):
            raise _Stop("~(…)",
                        "negation as failure is not classical negation; "
                        "the non-monotonic route is undecided", "")
        if isinstance(cond, AceCondList):
            # Handled at the BOX level (see box()) because the counting
            # reading rebinds enclosing referents; reaching it here means
            # a list nested somewhere the corpus never produces one.
            raise _Stop("[…]", "a list condition below a box's top level "
                        "is not in the measured corpus", "")
        raise _Stop(_shell_render(cond), "not in the measured corpus", "")

    # -- questions at the top ----------------------------------------------
    def question(self, box: AceDrs) -> AceFormula:
        query_vars: List[Tuple[str, str]] = []
        plain: List[AceCondition] = []
        for cond in box.conditions:
            if isinstance(cond, AceAtom) and cond.functor == "query":
                if not (len(cond.args) == 2 and isinstance(cond.args[0], AceVar)
                        and isinstance(cond.args[1], str)):
                    raise _Stop(cond.render(), "a query condition outside "
                                "the measured shapes", "")
                query_vars.append((self.renamer.referent(cond.args[0]),
                                   cond.args[1]))
            else:
                plain.append(cond)
        body = self.conjoin([self.condition(c) for c in plain], box)
        queried = {name for name, _ in query_vars}
        for ref in reversed(self._box_refs(box)):
            if ref not in queried:  # the queried referents stay FREE
                body = Quantifier("∃", Variable(ref), body)
        if query_vars:
            return AceFormula(body, "wh_question", tuple(query_vars),
                              tuple(self.modalities))
        return AceFormula(body, "yesno_question", (),
                          tuple(self.modalities))


def _vars_of(cond) -> set:
    """Every APE variable name occurring anywhere in a condition."""
    names = set()
    stack = [cond]
    while stack:
        current = stack.pop()
        if isinstance(current, AceAtom):
            stack.extend(current.args)
        elif isinstance(current, AceVar):
            names.add(current.name)
        elif isinstance(current, AceCondList):
            stack.extend(current.conditions)
        elif isinstance(current, AceDrs):
            stack.extend(current.conditions)
            stack.extend(current.referents)
        elif isinstance(current, (AceNeg, AceNaf, AceModal, AceQuestion,
                                  AceCommand)):
            stack.append(current.drs)
        elif isinstance(current, AceImpl):
            stack.extend((current.antecedent, current.consequent))
        elif isinstance(current, AceOr):
            stack.extend((current.left, current.right))
        elif isinstance(current, AceExpr):
            stack.extend((current.left, current.right))
    return names


def _kit_pred(noun: str) -> str:
    from .mapping import _kit_predicate
    return _kit_predicate(noun)


def ace_drs_to_formula(ace_drs: AceDrs) -> AceFormula:
    """APE's DRS → :class:`AceFormula` — the pure function behind
    :func:`ace_to_formula`, offline-testable on recorded DRS terms."""
    translator = _Translator(ace_drs)
    questions = [c for c in ace_drs.conditions if isinstance(c, AceQuestion)]
    try:
        if questions:
            if len(questions) > 1 or len(ace_drs.conditions) > 1 \
                    or ace_drs.referents:
                raise _Stop("question(…)",
                            "a question mixed with assertions (or a second "
                            "question) in one text — the merged box shares "
                            "referents across the parts; split the text", "")
            return translator.question(questions[0].drs)
        formula = translator.box(ace_drs)
    except _Stop as stop:
        raise AceUnsupportedError(
            f"this route cannot carry the text — {stop.row.condition}: "
            f"{stop.row.reason}"
            + (f" [{stop.row.milestone}]" if stop.row.milestone else ""),
            (stop.row,)) from None
    return AceFormula(formula, "assertion", (), tuple(translator.modalities))


def ace_to_formula(text: str, *, ulex: Optional[str] = None,
                   guess: bool = False, timeout: float = 30.0) -> AceFormula:
    """ACE text → one kit formula with modality, questions and all.

    The union of what this and :func:`~unicode_fol_kit.ace.mapping.ace_to_drs`
    accept is deliberate: everything the DRS route carries, plus modal boxes
    and top-level questions. What neither carries — commands, negation as
    failure, real cardinalities, arithmetic — raises
    :class:`~unicode_fol_kit.ace.mapping.AceUnsupportedError` here too, with
    the same reasons and milestones.

    Raises:
        unicode_fol_kit.ace.runner.AceParseError: the text is not ACE.
        unicode_fol_kit.ace.mapping.AceUnsupportedError: see above.
        unicode_fol_kit.ace.runner.ApeUnavailableError: no APE binary
            reachable.
    """
    result = run_ape(text, ulex=ulex, guess=guess, timeout=timeout)
    if not result.accepted:
        first = result.error_messages[0]
        raise AceParseError(
            f"not ACE: {first.value!r}"
            + (f" (repair hint: {first.repair!r})" if first.repair else ""),
            result.error_messages)
    return ace_drs_to_formula(parse_ape_drs(result.drs))
