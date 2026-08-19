"""Kit DRS → ACE text (``drs_to_ace``), with the round trip as the claim.

The reverse of :mod:`unicode_fol_kit.ace.mapping`: a DRS built from the
kit's condition inventory becomes an ACE text plus the user-lexicon entries
(APE ``-ulextext`` clauses) that make every content word parseable. The
correctness bar is NOT "natural English" — it is the machine-checked round
trip :func:`ace_round_trip`: the produced text, fed back through APE and
:func:`~unicode_fol_kit.ace.mapping.map_ace_drs`, must yield a DRS whose
:func:`~unicode_fol_kit.drt.export.drs_to_fol` is Z3-equivalent to the
input's. Everything below is in service of closing that loop, and the whole
mappable corpus closes it (pinned in ``tests/test_ace_verbalize.py``).

Design decisions, each probed against the live APE before being written:

- **Referent roles come from the kit's naming convention** — ``e*`` is an
  event, ``g*`` a group, everything else an individual. The mapping names
  referents this way by construction; hand-built DRSs must follow the same
  convention (an "event" named ``x1`` is refused for having no noun, not
  guessed at).
- **Every individual is introduced by a noun with a variable apposition**
  ("a man X1", "there is a man X1") and referenced as the bare variable
  afterwards. Appositions survive every embedding APE was probed with,
  while "there is … and …" under ``It is false that`` LOSES the second
  conjunct from the negation scope — which is why a multi-clause negated
  box is rewritten (below) rather than rendered as a conjunction.
- **The first unary condition over a referent is its noun; every further
  unary becomes a predicative clause** ("X1 is a rich."). Predicative
  indefinites come back as a fresh referent plus an equality — Z3-equal to
  the plain unary atom — and using ONE lexical category (noun) for every
  unary predicate avoids noun/adjective ambiguity in the generated
  lexicon. The only adjectives the generator emits are the comparatives
  (``Tall_comp_than`` → "taller than"), which have no noun form.
- **A negated box that needs more than one clause is rewritten**:
  ``¬∃R(C₁ ∧ … ∧ Cₙ)`` becomes ``∀R_front(C₁ ∧ … ∧ Cₙ₋₁ → ¬∃R_back Cₙ)``
  — an if-then whose consequent is a one-clause negation. The rewrite is a
  classical equivalence, and the round trip re-checks it per DRS.
- **Surface forms are mechanical and lexicon-defined, not English.** The
  third-person singular and the plural add ``s``/``es``/``ies``, the
  comparative adds ``er``/``r``/``ier``, underscores become hyphens
  (``Bond_to`` → the verb ``bond-to``). "3 mans" is deliberate: the
  emitted ``noun_pl(mans, man, neutr)`` entry DEFINES that surface, APE
  parses it, and the logical symbol underneath is exactly ``man``. No
  morphology is guessed; what the lexicon says is what the text uses.
- **Strict lower bounds only**: ``Card(g, <=, n)`` and ``Card(g, <, n)``
  are refused — probed: APE reads "at most"/"less than" as the maximality
  LIST condition (the distributive counting reading of the formula route),
  so no ACE surface maps back to a plain upper-bound ``Card`` and the DRS
  round trip cannot close. ``=``/``>=``/``>`` all close.

What is refused, by name (:class:`AceVerbalizationError`): a referent with
no noun, a value constant outside the right-hand side of an equality, a
constant or predicate whose name is not invertible (the surface must map
back to the SAME kit symbol through the mapping's own name rules — checked
programmatically per name, never assumed), binary predicates over
individuals other than ``Of``/``*_comp_than`` (an ACE verb always carries
an event, so a 2-place kit atom cannot survive the trip as a 2-place
atom), events used as participants, groups outside the three probed shapes
(counted plural, coordination, "each of"), and complex conditions nested
deeper than the probed fragment.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Set, Tuple

from ..drt.export import drs_to_fol
from ..drt.nodes import DRS, Card, Condition, Eq, Impl, Neg, Or, Part, Pred
from .mapping import _kit_predicate, _named_constant, ace_to_drs
from .runner import AceError

__all__ = ["drs_to_ace", "ace_round_trip", "AceText", "AceRoundTrip",
           "AceVerbalizationError"]


class AceVerbalizationError(AceError):
    """The DRS contains something no probed ACE surface maps back to."""


@dataclass(frozen=True)
class AceText:
    """The verbalization: ``text`` is the ACE sentences, ``ulex`` the APE
    user-lexicon clauses (``-ulextext`` format, one per line). The
    generator always supplies its content words rather than relying on
    APE's built-in lexicon; duplicates with built-ins are harmless
    (probed)."""

    text: str
    ulex: str

    def __str__(self) -> str:  # pragma: no cover — convenience
        return self.text


@dataclass(frozen=True)
class AceRoundTrip:
    """One closed (or failed) loop: DRS → ACE → APE → DRS, judged by Z3."""

    verbalization: AceText
    back: DRS
    equivalent: bool
    detail: str = ""


# ---------------------------------------------------------------------------
# Mechanical morphology — lexicon-defined, never guessed (module docstring)
# ---------------------------------------------------------------------------

def _s_form(base: str) -> str:
    if re.search(r"(?:[sxz]|ch|sh)$", base):
        return base + "es"
    if re.search(r"[^aeiou]y$", base):
        return base[:-1] + "ies"
    return base + "s"


def _er_form(base: str) -> str:
    if base.endswith("e"):
        return base + "r"
    if re.search(r"[^aeiou]y$", base):
        return base[:-1] + "ier"
    return base + "er"


_PLAIN_ATOM = re.compile(r"^[a-z][a-z0-9_]*$")


def _atom(s: str) -> str:
    """Quote a Prolog atom for a ulex clause when needed."""
    return s if _PLAIN_ATOM.match(s) else f"'{s}'"


def _vowel_start(word: str) -> bool:
    return bool(word) and word[0].lower() in "aeiou"


_COMP_SUFFIX = "_comp_than"
_REFERENT_RE = re.compile(r"^[a-z][0-9]*$")
_INT_CONST = re.compile(r"^c_(\d+)$")


def _is_event(name: str) -> bool:
    return bool(re.match(r"^e[0-9]*$", name))


def _is_group(name: str) -> bool:
    return bool(re.match(r"^g[0-9]*$", name))


# ---------------------------------------------------------------------------
# Lexicon collector
# ---------------------------------------------------------------------------

class _Lexicon:
    def __init__(self) -> None:
        self.entries: Set[str] = set()

    @staticmethod
    def _logical(kit_name: str) -> str:
        logical = kit_name[0].lower() + kit_name[1:]
        if _kit_predicate(logical) != kit_name:
            raise AceVerbalizationError(
                f"drs_to_ace: predicate {kit_name!r} is not invertible — "
                f"the round trip would rename it to "
                f"{_kit_predicate(logical)!r}")
        return logical

    @staticmethod
    def _surface(logical: str) -> str:
        return logical.replace("_", "-")

    def noun(self, kit_name: str, plural: bool = False) -> str:
        logical = self._logical(kit_name)
        base = self._surface(logical)
        if plural:
            form = _s_form(base)
            self.entries.add(
                f"noun_pl({_atom(form)}, {_atom(logical)}, neutr).")
            return form
        self.entries.add(f"noun_sg({_atom(base)}, {_atom(logical)}, neutr).")
        return base

    def verb(self, kit_name: str, participants: int, plural: bool) -> str:
        logical = self._logical(kit_name)
        base = self._surface(logical)
        kind = {1: "iv", 2: "tv", 3: "dv"}.get(participants)
        if kind is None:
            raise AceVerbalizationError(
                f"drs_to_ace: verb {kit_name!r} with {participants} "
                "participants — ACE verbs take one to three")
        prep = ", to" if kind == "dv" else ""
        form = base if plural else _s_form(base)
        mode = "infpl" if plural else "finsg"
        self.entries.add(
            f"{kind}_{mode}({_atom(form)}, {_atom(logical)}{prep}).")
        return form

    def comparative(self, kit_name: str) -> str:
        logical = self._logical(kit_name[:-len(_COMP_SUFFIX)])
        base = self._surface(logical)
        form = _er_form(base)
        self.entries.add(f"adj_itr({_atom(base)}, {_atom(logical)}).")
        self.entries.add(f"adj_itr_comp({_atom(form)}, {_atom(logical)}).")
        return form

    def adverb(self, kit_name: str) -> str:
        logical = self._logical(kit_name)
        base = self._surface(logical)
        self.entries.add(f"adv({_atom(base)}, {_atom(logical)}).")
        return base

    def preposition(self, kit_name: str) -> str:
        logical = self._logical(kit_name)
        base = self._surface(logical)
        self.entries.add(f"prep({_atom(base)}, {_atom(logical)}).")
        return base

    def proper_name(self, constant: str) -> str:
        surface = constant[0].upper() + constant[1:]
        if _named_constant(surface) != constant:
            raise AceVerbalizationError(
                f"drs_to_ace: constant {constant!r} is not invertible — "
                f"the round trip would rename it to "
                f"{_named_constant(surface)!r}")
        self.entries.add(
            f"pn_sg({_atom(surface)}, {_atom(surface)}, neutr).")
        return surface

    def text(self) -> str:
        return "\n".join(sorted(self.entries))


# ---------------------------------------------------------------------------
# Structure helpers
# ---------------------------------------------------------------------------

def _sub_boxes(cond: Condition) -> Tuple[DRS, ...]:
    if isinstance(cond, Neg):
        return (cond.drs,)
    if isinstance(cond, Impl):
        return (cond.antecedent, cond.consequent)
    if isinstance(cond, Or):
        return (cond.left, cond.right)
    return ()


def _cond_names(cond: Condition) -> Set[str]:
    """Every name (referent or constant) a condition touches, sub-boxes'
    FREE names included."""
    if isinstance(cond, Pred):
        return set(cond.args)
    if isinstance(cond, Eq):
        return {cond.a, cond.b}
    if isinstance(cond, Card):
        return {cond.ref}
    if isinstance(cond, Part):
        return {cond.member, cond.group}
    names: Set[str] = set()
    for box in _sub_boxes(cond):
        names |= _box_free_names(box)
    return names


def _box_free_names(box: DRS) -> Set[str]:
    names: Set[str] = set()
    for cond in box.conditions:
        names |= _cond_names(cond)
    return names - set(box.referents)


def _all_referents(box: DRS) -> Set[str]:
    refs = set(box.referents)
    for cond in box.conditions:
        for sub in _sub_boxes(cond):
            refs |= _all_referents(sub)
    return refs


def _membership_duplex(cond: Condition, group: str) -> Optional[str]:
    """The duplex variable if ``cond`` is ``[v | Part_of(v, g)] => …``."""
    if not isinstance(cond, Impl):
        return None
    ante = cond.antecedent
    if (len(ante.referents) == 1 and len(ante.conditions) == 1
            and isinstance(ante.conditions[0], Part)
            and ante.conditions[0].member == ante.referents[0]
            and ante.conditions[0].group == group):
        return ante.referents[0]
    return None


def _card_words(card: Card) -> str:
    if card.op == "=":
        return str(card.n)
    if card.op == ">=":
        return f"at least {card.n}"
    if card.op == ">":
        return f"more than {card.n}"
    # <=, <: probed — APE reads "at most"/"less than" as the maximality
    # list condition, so no surface maps back to a plain upper-bound Card.
    raise AceVerbalizationError(
        f"drs_to_ace: Card op {card.op!r} has no ACE surface that survives "
        "the DRS round trip — APE reads upper bounds as the maximality "
        "list, which is the formula route's counting reading")


# ---------------------------------------------------------------------------
# Per-referent state
# ---------------------------------------------------------------------------

@dataclass
class _Np:
    kind: str                      # "individual" | "plural" | "coord" | "each"
    noun: Optional[str] = None     # kit name of the introducing noun
    extras: List[str] = field(default_factory=list)
    of_target: Optional[str] = None
    card: Optional[Card] = None
    members: List[str] = field(default_factory=list)   # kit constants
    duplex: Optional[Impl] = None
    var: Optional[str] = None      # "X1" once realized
    introduced: bool = False


# ---------------------------------------------------------------------------
# The generator
# ---------------------------------------------------------------------------

def drs_to_ace(drs: DRS) -> AceText:
    """Verbalize a kit DRS as ACE text plus the lexicon that carries it.

    See the module docstring for the covered fragment and the refusals;
    :func:`ace_round_trip` is the live self-check that the text means what
    the DRS means.
    """
    drs.validate()
    v = _Verbalizer(drs)
    clauses = _box_clauses(drs, v, env={}, depth=0)
    sentences = [c[0].upper() + c[1:] + "." for c in clauses]
    return AceText(text=" ".join(sentences), ulex=v.lexicon.text())


class _Verbalizer:
    """Shared state across the recursion: lexicon, variable counter, the
    set of declared referent names (for the referent/constant split)."""

    def __init__(self, root: DRS):
        self.lexicon = _Lexicon()
        self._var_n = 0
        self.declared = {r for r in _all_referents(root)
                         if _REFERENT_RE.match(r)}

    def fresh_var(self) -> str:
        self._var_n += 1
        return f"X{self._var_n}"

    def is_ref(self, name: str) -> bool:
        return name in self.declared

    def constant_np(self, name: str) -> str:
        """A constant in NP (participant) position: proper names only."""
        if name.startswith("c_"):
            raise AceVerbalizationError(
                f"drs_to_ace: value constant {name!r} outside the "
                "right-hand side of an equality — no probed ACE surface "
                "puts a value in a participant position")
        return self.lexicon.proper_name(name)

    def constant_value(self, name: str) -> str:
        """A constant on the right of an equality: value or proper name."""
        m = _INT_CONST.match(name)
        if m:
            return m.group(1)
        if name.startswith("c_"):
            tail = name[2:]
            if re.match(r"^m\d", tail) or re.match(r"^\d+p\d", tail):
                raise AceVerbalizationError(
                    f"drs_to_ace: value constant {name!r} — negative and "
                    "real values are outside the measured corpus")
            # The string form: string('Tail') → c_Tail closes the loop
            # even when the constant was born as a protected proper name
            # (c_E1) — the renamer gives both the same kit spelling.
            return f'"{tail}"'
        return self.lexicon.proper_name(name)


def _box_clauses(box: DRS, v: _Verbalizer, env: Dict[str, _Np],
                 depth: int) -> List[str]:
    """One box → its clause list. ``env`` is MUTATED (introductions land in
    it); callers that need scope isolation pass a copy — see
    :func:`_complex_clause`, where an if-then shares one env between
    antecedent and consequent while or-branches and negations get copies.
    """
    preds = [c for c in box.conditions if isinstance(c, Pred)]
    eqs = [c for c in box.conditions if isinstance(c, Eq)]
    cards = [c for c in box.conditions if isinstance(c, Card)]
    parts = [c for c in box.conditions if isinstance(c, Part)]
    complexes = [c for c in box.conditions if isinstance(c, (Neg, Impl, Or))]

    events = [r for r in box.referents if _is_event(r)]
    groups = [r for r in box.referents if _is_group(r)]
    individuals = [r for r in box.referents
                   if not _is_event(r) and not _is_group(r)]

    # -- groups: classify each declared group into one of the three shapes
    consumed: Set[int] = set()
    for g in groups:
        g_cards = [c for c in cards if c.ref == g]
        g_parts = [p for p in parts if p.group == g]
        duplex = next((c for c in complexes
                       if _membership_duplex(c, g) is not None), None)
        if len(g_cards) != 1:
            raise AceVerbalizationError(
                f"drs_to_ace: group {g!r} needs exactly one Card condition")
        card = g_cards[0]
        np = _Np(kind="?", card=card)
        if duplex is not None:
            consumed.add(id(duplex))
            np.duplex = duplex
            dup_var = _membership_duplex(duplex, g)
            cons = duplex.consequent
            if (not g_parts and not cons.referents
                    and len(cons.conditions) == 1
                    and isinstance(cons.conditions[0], Pred)
                    and cons.conditions[0].args == (dup_var,)):
                np.kind = "plural"
                np.noun = cons.conditions[0].name
            elif g_parts:
                np.kind = "each"
                np.members = [p.member for p in g_parts]
            else:
                raise AceVerbalizationError(
                    f"drs_to_ace: group {g!r}: the membership duplex fits "
                    "neither the counted-plural nor the each-of shape")
        elif g_parts:
            np.kind = "coord"
            np.members = [p.member for p in g_parts]
        else:
            raise AceVerbalizationError(
                f"drs_to_ace: group {g!r} has neither members nor a "
                "membership duplex — no noun to verbalize")
        if np.kind in ("coord", "each"):
            if card.op != "=" or card.n != len(np.members):
                raise AceVerbalizationError(
                    f"drs_to_ace: group {g!r}: Card({g}, {card.op}, "
                    f"{card.n}) does not close over its "
                    f"{len(np.members)} listed members")
            if any(v.is_ref(m) for m in np.members):
                raise AceVerbalizationError(
                    f"drs_to_ace: group {g!r} lists a referent as member "
                    "— only constant members are in the measured fragment")
        env[g] = np
    for p in parts:
        if p.group not in env or env[p.group].kind not in ("coord", "each"):
            raise AceVerbalizationError(
                f"drs_to_ace: {p.to_box_notation()} outside a declared "
                "group's cluster")
    for c in cards:
        if c.ref not in env or env[c.ref].kind == "individual":
            raise AceVerbalizationError(
                f"drs_to_ace: {c.to_box_notation()} outside a declared "
                "group's cluster")

    # -- individuals: nouns, extras, of-attachments
    for r in individuals:
        unaries = [p for p in preds if p.args == (r,)]
        np = _Np(kind="individual")
        if unaries:
            np.noun = unaries[0].name
            np.extras = [p.name for p in unaries[1:]]
        env[r] = np
    for p in preds:
        if (p.name == "Of" and len(p.args) == 2
                and not _is_event(p.args[0])):
            anchor = p.args[0]
            if anchor not in env or env[anchor].kind != "individual" \
                    or env[anchor].introduced:
                raise AceVerbalizationError(
                    f"drs_to_ace: Of anchor {anchor!r} is not an "
                    "individual declared in the same box")
            if env[anchor].of_target is not None:
                raise AceVerbalizationError(
                    f"drs_to_ace: {anchor!r} carries more than one Of "
                    "relation — outside the measured fragment")
            env[anchor].of_target = p.args[1]
    # A noun-less individual can still ride on an equality: the mapping's
    # copula rule produces exactly this shape for comparatives —
    # Eq(john, x1) ∧ Tall_comp_than(x1, mary) — where x1 exists only to be
    # John. Alias it to the other side and CONSUME that equality (emitting
    # both the alias and the clause would be redundant but harmless; the
    # alias alone keeps the text one sentence).
    consumed_eqs: Set[int] = set()
    for r in individuals:
        if env[r].noun is not None:
            continue
        alias = None
        for eq in eqs:
            if id(eq) in consumed_eqs:
                continue
            other = eq.b if eq.a == r else eq.a if eq.b == r else None
            if other is None or other == r:
                continue
            if not v.is_ref(other) or env.get(other, _Np("?")).noun is not None:
                alias = other
                consumed_eqs.add(id(eq))
                break
        if alias is None:
            raise AceVerbalizationError(
                f"drs_to_ace: referent {r!r} has no noun (no unary "
                "condition) and no equality to ride on — nothing to "
                "introduce it with. Events must be named e*, groups g*.")
        env[r].kind = "alias"
        env[r].of_target = None
        env[r].noun = alias  # stores the aliased NAME, not a noun
        env[r].introduced = True

    # -- classify the event-anchored and remaining predicates
    verb_preds: Dict[str, List[Pred]] = {e: [] for e in events}
    comparatives: List[Pred] = []
    predicative_consts: List[Pred] = []
    for p in preds:
        if p.args and _is_event(p.args[0]):
            if p.args[0] not in verb_preds:
                raise AceVerbalizationError(
                    f"drs_to_ace: event {p.args[0]!r} is not declared in "
                    "the box of its verb")
            verb_preds[p.args[0]].append(p)
            continue
        if p.name.endswith(_COMP_SUFFIX) and len(p.args) == 2:
            comparatives.append(p)
            continue
        if p.name == "Of" and len(p.args) == 2:
            continue  # attached above
        if len(p.args) == 1 and not v.is_ref(p.args[0]):
            predicative_consts.append(p)   # Man(john) → "John is a man."
            continue
        if len(p.args) == 1:
            continue  # nouns/extras, consumed above
        raise AceVerbalizationError(
            f"drs_to_ace: {p.to_box_notation()} — a {len(p.args)}-place "
            "predicate over individuals has no event, and an ACE verb "
            "always carries one; only Of and *_comp_than survive the trip")
    for e in events:
        others = [c for c in box.conditions
                  if not (isinstance(c, Pred) and c.args
                          and c.args[0] == e)]
        if any(e in _cond_names(c) for c in others):
            raise AceVerbalizationError(
                f"drs_to_ace: event {e!r} used outside its own verb "
                "conditions — not in the measured fragment")
        if not any(len(p.args) >= 2 for p in verb_preds[e]):
            raise AceVerbalizationError(
                f"drs_to_ace: event {e!r} has no verb condition")

    # -- NP realization ----------------------------------------------------
    def np_first(r: str) -> str:
        np = env[r]
        np.var = v.fresh_var()
        np.introduced = True
        if np.kind == "plural":
            noun = v.lexicon.noun(np.noun, plural=True)
            return f"{_card_words(np.card)} {noun} {np.var}"
        noun = v.lexicon.noun(np.noun)
        det = "an" if _vowel_start(noun) else "a"
        words = [det, noun, np.var]
        if np.of_target is not None:
            words += ["of", np_use(np.of_target)]
        return " ".join(words)

    def np_use(name: str) -> str:
        if not v.is_ref(name):
            return v.constant_np(name)
        np = env.get(name)
        if np is None:
            raise AceVerbalizationError(
                f"drs_to_ace: referent {name!r} used but not accessible")
        if np.kind == "alias":
            return (np_use(np.noun) if v.is_ref(np.noun)
                    else v.constant_np(np.noun))
        if np.kind == "coord":
            if np.introduced:
                raise AceVerbalizationError(
                    "drs_to_ace: coordination group used more than once — "
                    "a repeated 'John and Mary' would denote a NEW group")
            np.introduced = True
            return " and ".join(v.constant_np(m) for m in np.members)
        if not np.introduced:
            return np_first(name)
        return np.var

    def is_plural_subject(name: str) -> bool:
        np = env.get(name)
        return np is not None and np.kind in ("plural", "coord")

    def verb_clause(e: str) -> str:
        ordered = verb_preds[e]
        verb = next(p for p in ordered if len(p.args) >= 2)
        participants = verb.args[1:]
        if len(participants) > 3:
            raise AceVerbalizationError(
                f"drs_to_ace: verb {verb.name!r} with {len(participants)} "
                "participants — ACE verbs take one to three")
        plural = is_plural_subject(participants[0])
        words = [np_use(participants[0]),
                 v.lexicon.verb(verb.name, len(participants), plural)]
        if len(participants) >= 2:
            words.append(np_use(participants[1]))
        if len(participants) == 3:
            words += ["to", np_use(participants[2])]
        for m in ordered:
            if m is verb:
                continue
            if len(m.args) == 1:
                words.append(v.lexicon.adverb(m.name))
            elif len(m.args) == 2:
                words += [v.lexicon.preposition(m.name), np_use(m.args[1])]
            else:
                raise AceVerbalizationError(
                    f"drs_to_ace: modifier {m.to_box_notation()} with "
                    f"{len(m.args) - 1} objects is not in the measured "
                    "fragment")
        return " ".join(words)

    # -- assemble the clause list -----------------------------------------
    clauses: List[str] = []

    # 1. plural groups always introduce first ("there are …")
    for g in groups:
        if env[g].kind == "plural":
            clauses.append("there are " + np_first(g))

    # 2. of-carrying individuals (and their referent targets) introduce
    #    before any use, target-first — "a dog X1 of X2" needs X2 known.
    def intro_of(r: str, visiting: Set[str]) -> None:
        np = env[r]
        if np.introduced:
            return
        if r in visiting:
            raise AceVerbalizationError(
                f"drs_to_ace: circular Of chain at {r!r}")
        visiting.add(r)
        target = np.of_target
        if target is not None and v.is_ref(target) \
                and env[target].kind == "individual":
            intro_of(target, visiting)
        clauses.append("there is " + np_first(r))

    for r in individuals:
        if env[r].of_target is not None:
            intro_of(r, set())

    # 3. verb clauses; an each-of group renders as one distributed clause
    for g in groups:
        if env[g].kind == "each":
            clauses.append(_each_of_clause(g, env[g], v))
            others = [c for c in box.conditions
                      if id(c) != id(env[g].duplex)
                      and not (isinstance(c, (Card, Part))
                               and g in _cond_names(c))]
            if any(g in _cond_names(c) for c in others):
                raise AceVerbalizationError(
                    f"drs_to_ace: each-of group {g!r} used outside its "
                    "own cluster — not in the measured fragment")
    for e in events:
        clauses.append(verb_clause(e))

    # 4. remaining introductions (referents used only in equalities,
    #    comparatives, sub-boxes — or not at all)
    for r in individuals:
        if not env[r].introduced:
            clauses.append("there is " + np_first(r))
    for g in groups:
        if env[g].kind == "coord" and not env[g].introduced:
            raise AceVerbalizationError(
                f"drs_to_ace: coordination group {g!r} is not the "
                "participant of any verb — nothing carries it")

    # 5. predicative clauses for extra unaries and constant facts
    for r in individuals:
        for extra in env[r].extras:
            noun = v.lexicon.noun(extra)
            det = "an" if _vowel_start(noun) else "a"
            clauses.append(f"{env[r].var} is {det} {noun}")
    for p in predicative_consts:
        noun = v.lexicon.noun(p.name)
        det = "an" if _vowel_start(noun) else "a"
        clauses.append(f"{v.constant_np(p.args[0])} is {det} {noun}")

    # 6. equalities and comparatives (every referent is introduced by now)
    def np_or_name(name: str) -> str:
        return np_use(name) if v.is_ref(name) else v.constant_np(name)

    for eq in eqs:
        if id(eq) in consumed_eqs:
            continue
        left, right = eq.a, eq.b
        if not v.is_ref(left) and v.is_ref(right):
            left, right = right, left   # values read best on the right
        right_text = (np_use(right) if v.is_ref(right)
                      else v.constant_value(right))
        clauses.append(f"{np_or_name(left)} is {right_text}")
    for p in comparatives:
        clauses.append(f"{np_or_name(p.args[0])} is "
                       f"{v.lexicon.comparative(p.name)} than "
                       f"{np_or_name(p.args[1])}")

    # 7. complex conditions
    for cond in complexes:
        if id(cond) in consumed:
            continue
        clauses.append(_complex_clause(cond, v, env, depth))

    if not clauses:
        raise AceVerbalizationError(
            "drs_to_ace: the box has no conditions to verbalize")
    return clauses


def _each_of_clause(g: str, np: _Np, v: _Verbalizer) -> str:
    """"each of John and Mary waits" — the duplex consequent as one clause
    whose subject is the spoken member list. The distributed box must hold
    exactly one verb over the member variable (plus event-anchored
    modifiers with constant objects) — anything else is refused."""
    dup_var = _membership_duplex(np.duplex, g)
    cons = np.duplex.consequent
    cons_events = [r for r in cons.referents if _is_event(r)]
    if len(cons_events) != 1 or len(cons.referents) != 1:
        raise AceVerbalizationError(
            f"drs_to_ace: each-of group {g!r}: the distributed box must "
            "declare exactly the verb's event")
    event = cons_events[0]
    if not all(isinstance(c, Pred) and c.args and c.args[0] == event
               for c in cons.conditions):
        raise AceVerbalizationError(
            f"drs_to_ace: each-of group {g!r}: the distributed box holds "
            "conditions beside its verb — not in the measured fragment")
    ordered = list(cons.conditions)
    verb = next((p for p in ordered if len(p.args) >= 2), None)
    if verb is None or verb.args[1] != dup_var:
        raise AceVerbalizationError(
            f"drs_to_ace: each-of group {g!r}: the distributed verb must "
            "take the member variable as its subject")
    words = ["each of",
             " and ".join(v.constant_np(m) for m in np.members),
             v.lexicon.verb(verb.name, len(verb.args) - 1, plural=False)]
    objects = list(verb.args[2:])
    if objects:
        words.append(v.constant_np(objects[0]))
    if len(objects) == 2:
        words += ["to", v.constant_np(objects[1])]
    for m in ordered:
        if m is verb:
            continue
        if len(m.args) == 1:
            words.append(v.lexicon.adverb(m.name))
        elif len(m.args) == 2:
            words += [v.lexicon.preposition(m.name),
                      v.constant_np(m.args[1])]
        else:
            raise AceVerbalizationError(
                f"drs_to_ace: each-of group {g!r}: modifier shape not in "
                "the measured fragment")
    np.introduced = True
    return " ".join(words)


def _complex_clause(cond: Condition, v: _Verbalizer, env: Dict[str, _Np],
                    depth: int) -> str:
    """One embedded box structure as ONE clause. Scope handling probed:
    an if-then SHARES one env copy between antecedent and consequent (the
    antecedent's referents stay visible after "then"), or-branches and
    negations are islands and get their own copies."""
    if depth > 1:
        raise AceVerbalizationError(
            "drs_to_ace: complex conditions nested deeper than the probed "
            "fragment (one embedded level)")
    if isinstance(cond, Neg):
        mark = v._var_n
        inner = _box_clauses(cond.drs, v, dict(env), depth + 1)
        if len(inner) == 1:
            return "it is false that " + inner[0]
        v._var_n = mark   # the discarded attempt must not burn variables
        return _rewrite_neg(cond, v, env, depth)
    if isinstance(cond, Impl):
        shared = dict(env)
        ante = _box_clauses(cond.antecedent, v, shared, depth + 1)
        cons = _box_clauses(cond.consequent, v, shared, depth + 1)
        return "if " + " and ".join(ante) + " then " + " and ".join(cons)
    if isinstance(cond, Or):
        left = _box_clauses(cond.left, v, dict(env), depth + 1)
        right = _box_clauses(cond.right, v, dict(env), depth + 1)
        return " and ".join(left) + " or " + " and ".join(right)
    raise AceVerbalizationError(
        f"drs_to_ace: condition {type(cond).__name__} is not verbalizable")


def _rewrite_neg(cond: Neg, v: _Verbalizer, env: Dict[str, _Np],
                 depth: int) -> str:
    """``¬∃R(C₁ ∧ … ∧ Cₙ)`` → "if C₁ … Cₙ₋₁ then it is false that Cₙ" —
    the probed way to keep every conjunct inside the negation's scope
    (a "that A and B" surface drops B out of the negation). The split is
    a classical equivalence; the round trip re-checks it per DRS."""
    box = cond.drs
    conds = list(box.conditions)
    back_i = None
    for i in range(len(conds) - 1, -1, -1):
        c = conds[i]
        if isinstance(c, (Card, Part)):
            continue   # group infrastructure must stay with its group
        if isinstance(c, Impl) and any(
                _membership_duplex(c, g) is not None
                for g in box.referents):
            continue
        back_i = i
        break
    if back_i is None:
        raise AceVerbalizationError(
            "drs_to_ace: negated box holds only group infrastructure — "
            "not in the measured fragment")
    back = conds[back_i]
    front = conds[:back_i] + conds[back_i + 1:]
    front_names: Set[str] = set()
    for c in front:
        front_names |= _cond_names(c)
    back_only = tuple(r for r in box.referents
                      if r in _cond_names(back) and r not in front_names)
    front_refs = tuple(r for r in box.referents if r not in back_only)
    rewritten = Impl(DRS(front_refs, tuple(front)),
                     DRS((), (Neg(DRS(back_only, (back,))),)))
    return _complex_clause(rewritten, v, env, depth)


# ---------------------------------------------------------------------------
# The self-check loop
# ---------------------------------------------------------------------------

def ace_round_trip(drs: DRS, *, timeout: float = 30.0) -> AceRoundTrip:
    """DRS → ACE → APE → DRS, judged by Z3 — the machine self-check.

    Needs a live APE (:func:`~unicode_fol_kit.ace.runner.ape_available`).
    Raises :class:`AceVerbalizationError` when the DRS is outside the
    verbalizable fragment, and propagates the mapping's own errors if the
    produced text comes back unmappable (which would be a generator bug —
    the tests keep that set empty over the whole mappable corpus).
    """
    from ..eval.equivalence import equivalent

    verbal = drs_to_ace(drs)
    back = ace_to_drs(verbal.text, ulex=verbal.ulex or None, timeout=timeout)
    ours = drs_to_fol(drs)
    theirs = drs_to_fol(back)
    result = equivalent(ours, theirs)
    detail = "" if result.equivalent else (
        f"forward: {ours.to_unicode_str()}  back: {theirs.to_unicode_str()}")
    return AceRoundTrip(verbalization=verbal, back=back,
                        equivalent=bool(result.equivalent), detail=detail)
