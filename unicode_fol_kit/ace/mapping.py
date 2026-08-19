"""ACE-DRS → kit DRS: the pure fragment, with a per-condition verdict.

The reader (:mod:`unicode_fol_kit.ace.drs_reader`) delivers APE's DRS
verbatim; this module decides, condition by condition, what the kit's
classical DRS core (:mod:`unicode_fol_kit.drt.nodes`: ``Pred``/``Eq``/
``Neg``/``Impl``/``Or``) can carry — and REFUSES the rest by name, with a
reason and the milestone that will change the verdict. A sentence maps
either completely or not at all: there is no partial DRS with conditions
silently dropped, because a DRS missing one condition of the original does
not mean "most of" the original — it means something else.

Vocabulary — what a mapped condition becomes
--------------------------------------------
Nouns, verbs, adjectives, adverbs and prepositions become kit predicates,
uppercased into the kit convention. Events stay, neo-Davidsonian::

    object(A,man,countable,na,eq,1)   ->  Man(x1)
    predicate(B,see,A,C)              ->  See(e1, x1, x2)
    modifier_pp(B,in,G)               ->  In(e1, x3)
    modifier_adv(B,loudly,pos)        ->  Loudly(e1)
    property(A,rich,pos)              ->  Rich(x1)
    property(A,tall,comp_than,B)      ->  Tall_comp_than(x1, x2)
    relation(A,of,B)                  ->  Of(x1, x2)
    has_part(G,named('John'))         ->  Part_of(john, g1)
    object(G,na,countable,na,eq,2)    ->  Card(g1, =, 2)
    object(G,man,countable,na,geq,3)  ->  Card(g1, >=, 3),
                                          [x2 | Part_of(x2, g1)] => [ | Man(x2)]

Since 0.24.0 the plural shapes land on the DRS core's ``Card``/``Part``
conditions: a coordination group contributes its cardinality, a counted
plural additionally distributes its noun over the members via a membership
duplex — while the group referent itself stays a term for the verb, which
is ACE's COLLECTIVE reading of the unmarked plural ("at least 3 men wait"
asserts a waiting group of >= 3 men, not three individual waits; "each of"
compiles to the duplex and distributes, exactly as APE hands it over).

A non-``pos`` degree is folded into the predicate NAME (``Tall_comp_than``)
rather than dropped — no morphology is attempted ("taller" is never
reconstructed from ``tall``), and the underscore forms are legal kit
predicates since 0.23.1. The copula follows Attempto's own reference
translation, measured on its TPTP output: ``predicate(B,be,X,Y)`` becomes
the EQUALITY ``X = Y`` and the be-event referent is dropped — but only when
that referent occurs nowhere else in the whole DRS; if something modifies
the be-event (nothing in the measured corpus does), the guard keeps it as a
``Be(e, x, y)`` predicate instead of silently orphaning the modifier.

Referents are renamed to the kit's convention by ROLE, in order of
declaration: events (first argument of a ``predicate`` condition) become
``e1, e2, …``, group referents (a ``na``-noun ``object`` or the whole of a
``has_part``) become ``g1, …``, everything else ``x1, …``. Proper names
become kit constants (``named('John')`` → ``john``); values become ``c_``
constants (``int(30)`` → ``c_30``, ``string('Johnny')`` → ``c_Johnny``) —
each table is deterministic, collision-checked, and returned on the result.

What is refused, and where it goes
-----------------------------------
- **modal boxes** — no modal conditions in a classical DRS → ACE-3, done:
  use :func:`unicode_fol_kit.ace.translate.ace_to_formula`;
- **question / query** — a question is not an assertion → likewise
  ``ace_to_formula``;
- **command** — no imperative semantics decided (no milestone: undecided);
- **~ (negation as failure)** — not classical negation (no milestone);
- **the [...] list condition** — the maximality reading of ``exactly``/``at
  most`` is a counting quantifier over a compound scope, a FORMULA-level
  construct → ``ace_to_formula`` carries it (the distributive counting
  reading, documented there);
- **formula / expr** — arithmetic terms have no place in a DRS condition's
  referent/constant arguments → ``ace_to_formula`` carries it.

Everything else unseen (a functor or arity outside the measured corpus)
is refused as exactly that — "not in the measured corpus" — rather than
guessed at.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple, Union

from ..drt.nodes import DRS, Condition, Eq, Impl, Neg, Or, Pred
from .drs_reader import (
    AceAtom, AceCommand, AceCondition, AceCondList, AceDrs, AceExpr, AceImpl,
    AceInt, AceModal, AceNaf, AceNamed, AceNeg, AceOr, AceQuestion, AceReal,
    AceString, AceTerm, AceTermApp, AceVar, parse_ape_drs,
)
from .runner import AceError, AceParseError, run_ape

__all__ = [
    "map_ace_drs", "ace_to_drs", "DrsMapping", "ConditionReport",
    "condition_statistics", "AceUnsupportedError",
]


class AceUnsupportedError(AceError):
    """The text is ACE, but at least one of its DRS conditions is outside
    what the requested route can carry. ``rows`` holds the FULL per-condition
    report — the unsupported entries name the reason and, where one exists,
    the milestone that will change the verdict."""

    def __init__(self, message: str, rows: Tuple["ConditionReport", ...]):
        super().__init__(message)
        self.rows = rows

    @property
    def unsupported(self) -> Tuple["ConditionReport", ...]:
        return tuple(r for r in self.rows if r.verdict == "unsupported")


@dataclass(frozen=True)
class ConditionReport:
    """One condition's verdict. ``condition`` is APE's own rendering (the
    sub-boxes of a complex condition elided to ``…`` — their conditions get
    rows of their own), ``target`` the kit rendering when mapped,
    ``reason``/``milestone`` the refusal when not. ``sentence``/``token``
    point back into the ACE text for atomic conditions; complex shells and
    implicit conditions carry ``None``."""

    condition: str
    verdict: str  # "mapped" | "unsupported"
    target: str = ""
    reason: str = ""
    milestone: str = ""
    sentence: Optional[int] = None
    token: Optional[int] = None


@dataclass(frozen=True)
class DrsMapping:
    """The result of :func:`map_ace_drs`.

    ``drs`` is the kit DRS when EVERY condition mapped (``complete``), else
    ``None`` — never a partial structure. ``rows`` is the per-condition
    report either way. ``referents`` and ``constants`` are the two renaming
    tables (APE's name / the source term's rendering → kit name), returned
    so a caller can trace any kit symbol back to its origin."""

    drs: Optional[DRS]
    rows: Tuple[ConditionReport, ...]
    referents: Dict[str, str]
    constants: Dict[str, str]

    @property
    def complete(self) -> bool:
        return self.drs is not None

    @property
    def unsupported(self) -> Tuple[ConditionReport, ...]:
        return tuple(r for r in self.rows if r.verdict == "unsupported")


def condition_statistics(mappings) -> Dict[Tuple[str, str, str], int]:
    """Aggregate report rows over many mappings — the ACE-5 data basis.

    Keys are ``(condition label, verdict, milestone)``; the label is the
    functor with arity for atoms (``object/6``) and the bare functor for
    complex shells. Feed it ``map_ace_drs`` results over a corpus and the
    counts say exactly which core extension pays for how many sentences.
    """
    counts: Dict[Tuple[str, str, str], int] = {}
    for mapping in mappings:
        for row in mapping.rows:
            key = (_row_label(row), row.verdict, row.milestone)
            counts[key] = counts.get(key, 0) + 1
    return counts


def _row_label(row: ConditionReport) -> str:
    # Strip the -S/T index an atomic render carries before reading the
    # arity off the argument list.
    body = re.sub(r"-\d+/(?:\d+|'')$", "", row.condition)
    head = body.split("(", 1)[0]
    if "…" in body or not body.endswith(")"):
        return head or body
    inner = body[len(head) + 1:-1]
    depth = 0
    arity = 1 if inner else 0
    for ch in inner:
        if ch in "([":
            depth += 1
        elif ch in ")]":
            depth -= 1
        elif ch == "," and depth == 0:
            arity += 1
    return f"{head}/{arity}"


# ---------------------------------------------------------------------------
# Renaming
# ---------------------------------------------------------------------------

_REFERENT_SHAPE = re.compile(r"^[a-z][0-9]*$")
_ALNUM = re.compile(r"[^a-zA-Z0-9]+")


def _named_constant(name: str) -> str:
    """The proper-name rule, shared with the differential's alignment side:
    ``John`` → ``john``; a name that would land in the kit's single-letter
    REFERENT namespace (``E1``) takes the explicit ``c_`` form instead."""
    base = _ALNUM.sub("", name)
    base = base[0].lower() + base[1:] if base else "name"
    if _REFERENT_SHAPE.match(base):
        base = "c_" + (_ALNUM.sub("", name) or "name")
    return base


class _Renamer:
    """Deterministic APE-name → kit-name tables for referents and constants.

    Role detection is a PRE-pass over the whole tree (an event referent is
    one that appears as the first argument of any ``predicate`` condition;
    a group referent as the ``na``-noun of an ``object`` or the whole of a
    ``has_part``), so a referent's kit name never depends on which condition
    happens to be visited first.
    """

    def __init__(self, root: AceDrs):
        events, groups = set(), set()
        for cond in root.walk_conditions():
            if not isinstance(cond, AceAtom):
                continue
            if cond.functor == "predicate" and cond.args and isinstance(
                    cond.args[0], AceVar):
                events.add(cond.args[0].name)
            if (cond.functor == "object" and len(cond.args) == 6
                    and isinstance(cond.args[0], AceVar)):
                _ref, noun, cls, _unit, op, count = cond.args
                # A coordination group (na-noun) or a counted plural — both
                # denote GROUPS, so both take g-names for traceability.
                if noun == "na" or (op in _ACE_OPS and cls != "mass"
                                    and not (op == "eq" and count == 1)):
                    groups.add(cond.args[0].name)
            if (cond.functor == "has_part" and cond.args
                    and isinstance(cond.args[0], AceVar)):
                groups.add(cond.args[0].name)
        self._events, self._groups = events, groups
        self.referents: Dict[str, str] = {}
        self.constants: Dict[str, str] = {}
        self._counters = {"e": 0, "g": 0, "x": 0}
        for box in root.walk_boxes():
            for ref in box.referents:
                self._assign(ref.name)

    def _assign(self, ape_name: str) -> None:
        if ape_name in self.referents:
            return
        prefix = ("e" if ape_name in self._events
                  else "g" if ape_name in self._groups else "x")
        self._counters[prefix] += 1
        self.referents[ape_name] = f"{prefix}{self._counters[prefix]}"

    def fresh(self, prefix: str = "x") -> str:
        """A synthetic referent no APE variable maps to — the member variable
        of a plural object's membership duplex, or a counting variable. Uses
        the same per-prefix counters as :meth:`_assign`, so synthetic and
        mapped names share one numbering and cannot collide."""
        self._counters[prefix] = self._counters.get(prefix, 0) + 1
        name = f"{prefix}{self._counters[prefix]}"
        while name in self.referents.values():
            self._counters[prefix] += 1
            name = f"{prefix}{self._counters[prefix]}"
        return name

    def referent(self, var: AceVar) -> str:
        if var.name not in self.referents:
            # A variable used but never declared would be an APE invariant
            # violation; name it visibly rather than crashing.
            self._assign(var.name)
        return self.referents[var.name]

    def constant(self, term: Union[AceNamed, AceInt, AceReal, AceString]) -> str:
        key = term.render()
        if key in self.constants:
            return self.constants[key]
        if isinstance(term, AceNamed):
            base = _named_constant(term.name)
        elif isinstance(term, AceInt):
            base = "c_" + (str(term.value) if term.value >= 0
                           else "m" + str(-term.value))
        elif isinstance(term, AceReal):
            base = "c_" + ("m" if term.value < 0 else "") + str(
                abs(term.value)).replace(".", "p")
        else:  # AceString
            cleaned = _ALNUM.sub("", term.value)
            base = "c_" + (cleaned if cleaned else "str")
        candidate, n = base, 1
        while candidate in self.constants.values():
            n += 1
            candidate = f"{base}{n}" if not base.startswith("c_") \
                else f"{base}x{n}"
        self.constants[key] = candidate
        return candidate


#: APE's cardinality operators in kit spelling (drt.CARD_OPS). ``na`` never
#: reaches this table (mass nouns are handled before it).
_ACE_OPS = {"eq": "=", "geq": ">=", "leq": "<=", "exactly": "=",
            "greater": ">", "less": "<"}


def _kit_predicate(name: str) -> str:
    """``man`` → ``Man``; anything non-alphanumeric becomes ``_`` (legal in
    kit predicates since 0.23.1, e.g. the chem vocabulary's Has_bond_to)."""
    cleaned = re.sub(r"[^a-zA-Z0-9_]+", "_", name).strip("_") or "P"
    return cleaned[0].upper() + cleaned[1:]


def _degree_name(base: str, degree: str) -> str:
    return _kit_predicate(base) if degree == "pos" \
        else f"{_kit_predicate(base)}_{degree}"


# ---------------------------------------------------------------------------
# Atomic-condition mapping (shared with the ACE-3 formula route)
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class _Unsupported:
    reason: str
    milestone: str = ""


#: ("pred", name, args) | ("eq", left, right) | _Unsupported. The tuple
#: forms carry STRINGS (kit referent/constant names) so both consumers —
#: drt conditions here, fol atoms in .translate — build their own nodes.
_Mapped = Union[Tuple[str, str, Tuple[str, ...]], Tuple[str, str, str],
                _Unsupported]


def _term_name(term: AceTerm, renamer: _Renamer) -> Union[str, _Unsupported]:
    if isinstance(term, AceVar):
        return renamer.referent(term)
    if isinstance(term, (AceNamed, AceInt, AceReal, AceString)):
        return renamer.constant(term)
    if isinstance(term, AceExpr):
        return _Unsupported("an arithmetic expression term", "ACE-4")
    if isinstance(term, AceTermApp):
        return _Unsupported(
            f"a {term.functor}/{len(term.args)} term not in the measured corpus")
    return _Unsupported(f"a bare atom {term!r} in referent position")


def _map_atom(cond: AceAtom, renamer: _Renamer,
              be_event_dropped: frozenset) -> _Mapped:
    """One atomic condition → its kit shape, or a named refusal.

    ``be_event_dropped`` is the set of be-event referents (APE names) whose
    equality translation drops them — computed once per DRS by the caller,
    because whether ``be`` may become ``=`` depends on the WHOLE tree (see
    the module docstring's copula paragraph).
    """
    f, args = cond.functor, cond.args

    if f == "object" and len(args) == 6:
        ref, noun, cls, _unit, op, count = args
        if not isinstance(ref, AceVar) or not isinstance(noun, str):
            return _Unsupported("an object condition with a non-atomic noun")
        if (op == "eq" and count == 1) or (cls == "mass" and op == "na"):
            return ("pred", _kit_predicate(noun), (renamer.referent(ref),))
        if op not in _ACE_OPS or not isinstance(count, int):
            return _Unsupported(
                f"a cardinality operator outside the measured corpus "
                f"({op!r} {count!r})")
        if noun == "na":
            # A coordination group ("John and Mary"): its members arrive as
            # has_part conditions; the object contributes ONLY |g| op n.
            return ("card", renamer.referent(ref), _ACE_OPS[op], count)
        # A counted plural ("at least 3 men"): |g| op n, every member a noun.
        # ACE reads the unmarked plural COLLECTIVELY, so the group referent
        # stays and the verb keeps applying to it — the box mapper expands
        # this into Card plus a membership duplex.
        return ("group_noun", renamer.referent(ref), _kit_predicate(noun),
                _ACE_OPS[op], count)

    if f == "predicate" and len(args) in (3, 4, 5):
        event, verb = args[0], args[1]
        if not isinstance(event, AceVar) or not isinstance(verb, str):
            return _Unsupported("a predicate condition with a non-atomic verb")
        if verb == "be" and len(args) == 4:
            if event.name in be_event_dropped:
                left = _term_name(args[2], renamer)
                right = _term_name(args[3], renamer)
                for side in (left, right):
                    if isinstance(side, _Unsupported):
                        return side
                return ("eq", left, right)
            # The be-event is itself talked about (modified) — keep it.
            # Not measured in the corpus; the guard exists so that if APE
            # ever produces it, the modifier keeps its subject instead of
            # dangling.
        participants: List[str] = [renamer.referent(event)]
        for arg in args[2:]:
            name = _term_name(arg, renamer)
            if isinstance(name, _Unsupported):
                return name
            participants.append(name)
        return ("pred", _kit_predicate(verb), tuple(participants))

    if f == "property" and len(args) in (3, 4):
        ref, adjective, degree = args[0], args[1], args[2]
        if (not isinstance(ref, AceVar) or not isinstance(adjective, str)
                or not isinstance(degree, str)):
            return _Unsupported("a property condition outside the measured shapes")
        names: List[str] = [renamer.referent(ref)]
        for extra in args[3:]:
            name = _term_name(extra, renamer)
            if isinstance(name, _Unsupported):
                return name
            names.append(name)
        return ("pred", _degree_name(adjective, degree), tuple(names))

    if f == "relation" and len(args) == 3 and args[1] == "of":
        left = _term_name(args[0], renamer)
        right = _term_name(args[2], renamer)
        for side in (left, right):
            if isinstance(side, _Unsupported):
                return side
        return ("pred", "Of", (left, right))

    if f == "modifier_adv" and len(args) == 3:
        event, adverb, degree = args
        if (not isinstance(event, AceVar) or not isinstance(adverb, str)
                or not isinstance(degree, str)):
            return _Unsupported("a modifier_adv outside the measured shapes")
        return ("pred", _degree_name(adverb, degree),
                (renamer.referent(event),))

    if f == "modifier_pp" and len(args) == 3:
        event, preposition, obj = args
        if not isinstance(event, AceVar) or not isinstance(preposition, str):
            return _Unsupported("a modifier_pp outside the measured shapes")
        name = _term_name(obj, renamer)
        if isinstance(name, _Unsupported):
            return name
        return ("pred", _kit_predicate(preposition),
                (renamer.referent(event), name))

    if f == "has_part" and len(args) == 2:
        # APE argument order is (group, member); the kit condition reads
        # Part(member, group).
        group, member = args
        if not isinstance(group, AceVar):
            return _Unsupported("a has_part whose group is not a referent")
        member_name = _term_name(member, renamer)
        if isinstance(member_name, _Unsupported):
            return member_name
        return ("part", member_name, renamer.referent(group))
    if f == "query":
        return _Unsupported(
            "an interrogative marker: a question is not an assertion — "
            "ace_to_formula carries it", "ACE-3")
    if f == "formula":
        return _Unsupported(
            "arithmetic terms have no place in a DRS condition's "
            "referent/constant arguments -- ace_to_formula carries it",
            "ACE-4")
    return _Unsupported(
        f"{f}/{len(args)} is not in the measured corpus")


def _be_events_to_drop(root: AceDrs) -> frozenset:
    """Referents of ``be`` events that occur NOWHERE besides their own
    condition — exactly those may be translated away into an equality."""
    occurrences: Dict[str, int] = {}
    be_events: List[str] = []
    for cond in root.walk_conditions():
        if not isinstance(cond, AceAtom):
            continue
        if (cond.functor == "predicate" and len(cond.args) == 4
                and cond.args[1] == "be" and isinstance(cond.args[0], AceVar)):
            be_events.append(cond.args[0].name)
        for arg in cond.args:
            if isinstance(arg, AceVar):
                occurrences[arg.name] = occurrences.get(arg.name, 0) + 1
    return frozenset(e for e in be_events if occurrences.get(e, 0) == 1)


# ---------------------------------------------------------------------------
# Box mapping
# ---------------------------------------------------------------------------

def _shell_render(cond: AceCondition) -> str:
    """A complex condition's row rendering: functor with boxes elided —
    the boxes' own conditions get rows of their own."""
    if isinstance(cond, AceImpl):
        return "=>(…)"
    if isinstance(cond, AceOr):
        return "v(…)"
    if isinstance(cond, AceNeg):
        return "-(…)"
    if isinstance(cond, AceNaf):
        return "~(…)"
    if isinstance(cond, AceModal):
        return f"{cond.modality}(…)"
    if isinstance(cond, AceQuestion):
        return "question(…)"
    if isinstance(cond, AceCommand):
        return "command(…)"
    return "[…]"


class _BoxMapper:
    def __init__(self, root: AceDrs):
        self.renamer = _Renamer(root)
        self.dropped = _be_events_to_drop(root)
        self.rows: List[ConditionReport] = []
        self.complete = True

    def map_box(self, box: AceDrs) -> Optional[DRS]:
        referents = tuple(
            self.renamer.referent(r) for r in box.referents
            if r.name not in self.dropped)
        conditions: List[Condition] = []
        for cond in box.conditions:
            conditions.extend(self.map_condition(cond))
        if not self.complete:
            return None
        return DRS(referents, tuple(conditions))

    def map_condition(self, cond: AceCondition) -> List[Condition]:
        if isinstance(cond, AceAtom):
            result = _map_atom(cond, self.renamer, self.dropped)
            if isinstance(result, _Unsupported):
                self.complete = False
                self.rows.append(ConditionReport(
                    cond.render(), "unsupported", reason=result.reason,
                    milestone=result.milestone, sentence=cond.sentence,
                    token=cond.token))
                return []
            targets = self._kit_conditions(result)
            self.rows.append(ConditionReport(
                cond.render(), "mapped",
                target=", ".join(c.to_box_notation() for c in targets),
                sentence=cond.sentence, token=cond.token))
            return targets
        if isinstance(cond, AceNeg):
            self.rows.append(ConditionReport("-(…)", "mapped", target="~[…]"))
            sub = self.map_box(cond.drs)
            return [Neg(sub)] if sub is not None else []
        if isinstance(cond, AceImpl):
            self.rows.append(ConditionReport("=>(…)", "mapped",
                                             target="[…] -> […]"))
            antecedent = self.map_box(cond.antecedent)
            consequent = self.map_box(cond.consequent)
            if antecedent is None or consequent is None:
                return []
            return [Impl(antecedent, consequent)]
        if isinstance(cond, AceOr):
            self.rows.append(ConditionReport("v(…)", "mapped",
                                             target="[…] ∨ […]"))
            left = self.map_box(cond.left)
            right = self.map_box(cond.right)
            if left is None or right is None:
                return []
            return [Or(left, right)]
        # Everything below is a named refusal at THIS route; sub-box
        # conditions still get their own rows so the report stays complete.
        self.complete = False
        reason, milestone = _complex_refusal(cond)
        self.rows.append(ConditionReport(
            _shell_render(cond), "unsupported", reason=reason,
            milestone=milestone))
        for sub in _iter_sub_boxes(cond):
            self.map_box(sub)
        return []

    def _kit_conditions(self, result) -> List[Condition]:
        """One mapped atom shape -> its kit condition(s). The plural object
        is the one shape that expands to TWO: ``Card`` plus the membership
        duplex distributing the noun over the parts (the group itself stays
        a term for the verb -- ACE reads the unmarked plural collectively)."""
        from ..drt.nodes import Card, Part

        kind = result[0]
        if kind == "eq":
            return [Eq(result[1], result[2])]
        if kind == "pred":
            return [Pred(result[1], result[2])]
        if kind == "card":
            return [Card(result[1], result[2], result[3])]
        if kind == "part":
            return [Part(result[1], result[2])]
        if kind == "group_noun":
            _, group, noun, op, count = result
            member = self.renamer.fresh("x")
            membership = Impl(DRS((member,), (Part(member, group),)),
                              DRS((), (Pred(noun, (member,)),)))
            return [Card(group, op, count), membership]
        raise AssertionError(f"unknown mapped shape {kind!r}")


def _complex_refusal(cond: AceCondition) -> Tuple[str, str]:
    if isinstance(cond, AceModal):
        return (f"a modal box ({cond.modality}): no modal conditions in a "
                "classical DRS — ace_to_formula carries it", "ACE-3")
    if isinstance(cond, AceQuestion):
        return ("a question is not an assertion — ace_to_formula carries it",
                "ACE-3")
    if isinstance(cond, AceCommand):
        return ("an imperative: no command semantics decided", "")
    if isinstance(cond, AceNaf):
        return ("negation as failure is not classical negation; the "
                "non-monotonic route is undecided", "")
    if isinstance(cond, AceCondList):
        return ("the maximality reading of exactly/at most needs a counting "
                "quantifier over a compound scope, which is a FORMULA-level "
                "construct -- ace_to_formula carries it", "ACE-4")
    return ("not in the measured corpus", "")


def _iter_sub_boxes(cond: AceCondition):
    from .drs_reader import _sub_boxes
    yield from _sub_boxes(cond)


def map_ace_drs(ace_drs: AceDrs) -> DrsMapping:
    """APE's DRS → :class:`DrsMapping` (kit DRS iff complete, report always).

    The returned kit DRS has passed :meth:`unicode_fol_kit.drt.nodes.DRS
    .validate` — the renamer assigns globally unique referent names, which
    is exactly the invariant the kit core demands.
    """
    mapper = _BoxMapper(ace_drs)
    drs = mapper.map_box(ace_drs)
    if drs is not None:
        drs.validate()
    return DrsMapping(drs=drs, rows=tuple(mapper.rows),
                      referents=dict(mapper.renamer.referents),
                      constants=dict(mapper.renamer.constants))


def ace_to_drs(text: str, *, ulex: Optional[str] = None, guess: bool = False,
               timeout: float = 30.0) -> DRS:
    """ACE text → kit DRS, via APE and :func:`map_ace_drs`.

    The whole text becomes ONE box (APE merges sentences and resolves
    cross-sentence anaphora before this module ever sees the DRS). Feed the
    result to :func:`unicode_fol_kit.drt.export.drs_to_fol` for FOL, or use
    :func:`unicode_fol_kit.ace.translate.ace_to_formula` directly when the
    text may contain modality or questions.

    Raises:
        unicode_fol_kit.ace.runner.AceParseError: the text is not ACE.
        unicode_fol_kit.ace.mapping.AceUnsupportedError: a condition is
            outside the classical DRS core; ``rows`` names every condition
            and the refusals' milestones.
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
    mapping = map_ace_drs(parse_ape_drs(result.drs))
    if not mapping.complete:
        problems = "; ".join(
            f"{r.condition}: {r.reason}"
            + (f" [{r.milestone}]" if r.milestone else "")
            for r in mapping.unsupported)
        raise AceUnsupportedError(
            f"the classical DRS core cannot carry this text — {problems}",
            mapping.rows)
    return mapping.drs
