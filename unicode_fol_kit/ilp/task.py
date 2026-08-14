"""Building the ILP task: :class:`Example`, :class:`IlpTask`, and the emitter.

The three files Popper reads, from structures the kit already has:

``bk.pl``
    the background knowledge — one Prolog fact per tuple in a structure's
    extension, with individuals renamed so a name pins down its own example.
``exs.pl``
    ``pos(target(e)).`` / ``neg(target(e)).``, one line per example.
``bias.pl``
    ``head_pred`` / ``body_pred`` declarations plus the size bounds.

Every check that the EXAMPLES and the VOCABULARY can be encoded soundly runs in
:meth:`IlpTask.__post_init__` — before a file exists, so a task that has been
constructed is a task whose encoding has been checked. Two refusals necessarily
come later, because they are not about the encoding: materialising a computed
predicate is only costed when the facts are actually rendered, and a missing
parent directory is only knowable at :meth:`IlpTask.write`. Both leave nothing
behind. See the package docstring for what the encoding checks are and which
mistakes they were built from.

**Facts are the extension, exactly.** One Prolog fact per tuple, no
orientation guessed, nothing added. A symmetric relation (a chemical bond) is
stored symmetrically by
:func:`~unicode_fol_kit.chem.mol_to_structure` and therefore emitted in both
directions; an asymmetric one is emitted in the one direction it has. The
emitter has no opinion about which it is looking at, which is the only way it
can be right about both.

**Computed predicates are materialised.** A
:class:`~unicode_fol_kit.semantics.structures.FiniteStructure` may decide a
predicate by callable rather than by stored extension (``in_ring`` and friends
— see that module). Prolog needs facts, so the callable is asked about every
tuple. That costs ``|domain| ** arity`` calls, which is fine at arity 1–2 and
explosive above; the cost is checked against ``max_computed_tuples`` and
REFUSED rather than silently paid.
"""

import io
import os
import re
from dataclasses import dataclass, field
from itertools import product
from typing import (
    Dict, Iterable, List, Mapping, Optional, Sequence, Tuple, Union,
)

from ..semantics.structures import FiniteStructure

__all__ = [
    "IlpEncodingError", "Example", "IlpTask", "task_from_structures",
    "to_prolog_atom",
]

#: A Prolog atom: lower-case initial, then word characters. Quoted atoms
#: (``'1,2-diacyl'``) are deliberately NOT produced — a quoted name survives
#: into the learner's output and back through
#: :func:`~unicode_fol_kit.fol.parse_prolog_clause` as a token no kit grammar
#: accepts, so the caller is asked to rename instead.
#:
#: Matched with ``fullmatch``, never ``match``: Python's ``$`` also matches
#: immediately before a trailing newline, so ``"m1\n"`` would pass — and in
#: Prolog a newline is whitespace, which would make ``m1`` and ``m1\n`` ONE
#: atom while every uniqueness check here still saw two. That is exactly the
#: collision this module exists to prevent, arriving through the checker.
_PROLOG_ATOM_RE = re.compile(r"[a-z][A-Za-z0-9_]*")

#: The tail of an individual's name, after the example prefix has supplied a
#: legal initial character. Same ``fullmatch`` discipline.
_INDIVIDUAL_TAIL_RE = re.compile(r"[A-Za-z0-9_]+")

Key = Tuple[str, int]


class IlpEncodingError(ValueError):
    """A task that cannot be encoded soundly.

    Subclasses :class:`ValueError` so ``except ValueError`` still catches it,
    matching :func:`~unicode_fol_kit.eval.check_definitions`, which raises the
    same class for the same kind of problem: this is CONFIGURATION, not data.
    A campaign that cannot encode its task must stop, not emit rows.
    """


def to_prolog_atom(name: str) -> str:
    """The Prolog spelling of a kit name — first character folded down.

    Only the FIRST character, never the whole name: ``bSINGLE`` is already a
    legal Prolog atom and folding it to ``bsingle`` throws away a distinction
    ChemLog's vocabulary makes, which then cannot be restored on the way back
    (:func:`~unicode_fol_kit.fol.parse_prolog_clause` would return
    ``Bsingle``). The same rule, in the opposite direction, as
    :mod:`unicode_fol_kit.fol.prolog_input`.

    Raises:
        IlpEncodingError: the folded name is not a legal unquoted Prolog atom.

    Example:
        >>> from unicode_fol_kit.ilp import to_prolog_atom
        >>> to_prolog_atom("Amide"), to_prolog_atom("bSINGLE")
        ('amide', 'bSINGLE')
    """
    folded = name[:1].lower() + name[1:] if name else name
    if not _PROLOG_ATOM_RE.fullmatch(folded):
        raise IlpEncodingError(
            f"to_prolog_atom: {name!r} does not fold to a legal Prolog atom "
            f"(got {folded!r}; needs to match {_PROLOG_ATOM_RE.pattern}). "
            "Rename it — quoting would hide the problem until the learner's "
            "output came back unparseable.")
    return folded


@dataclass(frozen=True)
class Example:
    """One labelled structure: the thing the learner sees as ``pos``/``neg``.

    Args:
        id: names this example in the emitted Prolog. Folded to an atom by
            :func:`to_prolog_atom`, so ``"M1"`` and ``"m1"`` are the SAME
            example name and :class:`IlpTask` will refuse both at once.
        structure: what the background knowledge is read off.
        label: ``True`` for a positive example, ``False`` for a negative one.
        note: free text carried into the emitted files as a comment — a
            SMILES, an accession, whatever makes the facts readable next to
            their source. Never parsed.
    """

    id: str
    structure: FiniteStructure
    label: bool
    note: str = ""

    def __post_init__(self):
        to_prolog_atom(self.id)          # raises with a message if illegal
        if not isinstance(self.structure, FiniteStructure):
            raise IlpEncodingError(
                f"Example {self.id!r}: structure must be a FiniteStructure, "
                f"got {type(self.structure).__name__}")
        if any(character in self.note for character in "\n\r"):
            raise IlpEncodingError(
                f"Example {self.id!r}: note must be a single line — it is "
                "emitted as a Prolog comment, and a bare CR would put a CRLF "
                "into a file this module promises is LF-only")

    @property
    def atom(self) -> str:
        """The example's name as it appears in Prolog."""
        return to_prolog_atom(self.id)


def _comment(text: str) -> str:
    return f"% {text}"


@dataclass(frozen=True)
class IlpTask:
    """A complete ILP task, checked at construction and rendered on demand.

    Args:
        target: the predicate to be learned, arity 1 (its single argument is
            the example). Written ``amide`` or ``Amide`` — folded either way.
        examples: the labelled structures. At least one of each label: with no
            positives there is nothing to learn, and with no negatives the
            empty body is already a perfect hypothesis.
        body_predicates: the vocabulary offered to the learner, as
            ``(name, arity)`` pairs in the structures' own spelling. ``None``
            infers it from the structures — convenient, but every extra
            predicate multiplies the search space, so naming the handful you
            mean is usually the better task.
        membership: the ONE predicate carrying the example argument. Its facts
            say "this individual belongs to that example" and nothing else.
        max_vars, max_body, max_clauses: Popper's size bounds, emitted into
            ``bias.pl``.
        extra_bias: additional bias lines, verbatim, one per element (e.g.
            ``"enable_recursion."`` or a ``type`` declaration). Not validated
            — the learner is the authority on its own bias language.
        max_computed_tuples: refuse to materialise a computed predicate whose
            enumeration would cost more than this many calls.

    Raises:
        IlpEncodingError: any of the above is violated, or two
            ``(example, individual)`` pairs would produce the same Prolog
            constant.
    """

    target: str
    examples: Tuple[Example, ...]
    body_predicates: Optional[Tuple[Key, ...]] = None
    membership: str = "atom_in"
    max_vars: int = 6
    max_body: int = 8
    max_clauses: int = 1
    extra_bias: Tuple[str, ...] = ()
    max_computed_tuples: int = 100_000

    #: Set during validation: ``(name, arity)`` pairs an INFERRED vocabulary
    #: left out, with the reason. Empty when ``body_predicates`` was given.
    #: Not a constructor argument — it is a finding, not a setting.
    excluded_predicates: Tuple[Tuple[Key, str], ...] = field(
        default=(), compare=False, init=False)

    def __post_init__(self):
        object.__setattr__(self, "examples", tuple(self.examples))
        if isinstance(self.extra_bias, str):
            raise IlpEncodingError(
                "IlpTask: extra_bias must be a sequence of lines, not a "
                "single string — a string is iterable, so it would become one "
                "bias line per character")
        object.__setattr__(self, "extra_bias", tuple(self.extra_bias))
        to_prolog_atom(self.target)
        membership_atom = to_prolog_atom(self.membership)

        if not self.examples:
            raise IlpEncodingError("IlpTask: no examples")
        positives = [e for e in self.examples if e.label]
        negatives = [e for e in self.examples if not e.label]
        if not positives:
            raise IlpEncodingError(
                "IlpTask: no positive examples — there is nothing to learn")
        if not negatives:
            raise IlpEncodingError(
                "IlpTask: no negative examples — with none, the empty body is "
                "already a perfect hypothesis and any result would be "
                "vacuous. Add negatives, or use a different tool.")

        seen_ids: Dict[str, str] = {}
        for example in self.examples:
            atom = example.atom
            if atom in seen_ids:
                raise IlpEncodingError(
                    f"IlpTask: examples {seen_ids[atom]!r} and {example.id!r} "
                    f"both name the example {atom!r} in Prolog")
            seen_ids[atom] = example.id

        for bound, name in ((self.max_vars, "max_vars"),
                            (self.max_body, "max_body"),
                            (self.max_clauses, "max_clauses")):
            if not isinstance(bound, int) or bound < 1:
                raise IlpEncodingError(
                    f"IlpTask: {name} must be a positive integer, got {bound!r}")
        if not isinstance(self.max_computed_tuples, int) or \
                self.max_computed_tuples < 1:
            raise IlpEncodingError(
                "IlpTask: max_computed_tuples must be a positive integer, got "
                f"{self.max_computed_tuples!r}")

        if self.body_predicates is None:
            inferred, excluded = self._infer_vocabulary(membership_atom)
            object.__setattr__(self, "body_predicates", inferred)
            object.__setattr__(self, "excluded_predicates", excluded)
        else:
            object.__setattr__(
                self, "body_predicates",
                tuple(sorted({(str(n), int(a)) for n, a in self.body_predicates})))
            object.__setattr__(self, "excluded_predicates", ())

        functors: Dict[Key, str] = {}
        for name, arity in self.body_predicates:
            atom = to_prolog_atom(name)
            if arity >= 1:
                # Only the first character is folded, so `Ring/1` and `ring/1`
                # are two symbols and one Prolog predicate. Emitted, their
                # extensions would be unioned under that one functor —
                # background knowledge describing a relation that exists in no
                # structure. Same class of collision as two individuals
                # spelling one constant, and refused for the same reason.
                if functors.get((atom, arity), name) != name:
                    raise IlpEncodingError(
                        f"IlpTask: {functors[(atom, arity)]}/{arity} and "
                        f"{name}/{arity} both emit as {atom}/{arity}. Their "
                        "facts would be merged into one relation the "
                        "structures do not have — rename one of the "
                        "structure's symbols.")
                functors[(atom, arity)] = name
            if arity < 1:
                raise IlpEncodingError(
                    f"IlpTask: body predicate {name}/{arity} is 0-ary. A "
                    "0-ary fact carries no individual, so it cannot be "
                    "attached to one example — emitted, it would hold across "
                    "every example at once. Model it as a unary predicate of "
                    "the example's individuals instead.")
            if atom == membership_atom:
                raise IlpEncodingError(
                    f"IlpTask: {name}/{arity} collides with the membership "
                    f"predicate {membership_atom!r}. The example argument "
                    "must sit on exactly one predicate; rename either the "
                    "structure's symbol or membership=.")
            if not any(e.structure.interprets(name, arity)
                       for e in self.examples):
                raise IlpEncodingError(
                    f"IlpTask: body predicate {name}/{arity} is interpreted by "
                    "no example structure — every clause using it would be "
                    "unsatisfiable, so offering it can only waste search")

        self._individual_names()          # raises on a name collision

    # -- vocabulary ---------------------------------------------------------

    def _infer_vocabulary(self, membership_atom: str
                          ) -> Tuple[Tuple[Key, ...], Tuple[Tuple[Key, str], ...]]:
        """Every symbol the structures interpret, minus the ones that cannot
        be encoded soundly — each recorded with its reason rather than
        dropped silently."""
        symbols = sorted({key for e in self.examples
                          for key in e.structure.signature()})
        keep: List[Key] = []
        excluded: List[Tuple[Key, str]] = []
        for name, arity in symbols:
            if arity < 1:
                excluded.append(((name, arity),
                                 "0-ary: cannot be attached to one example"))
                continue
            try:
                atom = to_prolog_atom(name)
            except IlpEncodingError:
                excluded.append(((name, arity),
                                 "does not fold to a legal Prolog atom"))
                continue
            if atom == membership_atom:
                excluded.append(((name, arity),
                                 "collides with the membership predicate"))
                continue
            keep.append((name, arity))
        return tuple(keep), tuple(excluded)

    # -- naming -------------------------------------------------------------

    def individual_name(self, example: Example, individual: str) -> str:
        """The Prolog constant for ``individual`` inside ``example``.

        ``<example>_<individual>`` — the whole point of the module's first
        guarantee. Uniqueness of the result across the task is checked once,
        in the constructor.
        """
        if not _INDIVIDUAL_TAIL_RE.fullmatch(individual):
            raise IlpEncodingError(
                f"IlpTask: example {example.id!r} has an individual "
                f"{individual!r} that is not word characters — it cannot be "
                "part of an unquoted Prolog atom. Rename the structure's "
                "domain.")
        return f"{example.atom}_{individual}"

    def _individual_names(self) -> Dict[Tuple[str, str], str]:
        """``(example atom, individual) -> Prolog constant``, checked injective.

        Injective over EVERY constant the task will emit — the individuals and
        the example names together, because they share one namespace in the
        file. Both collisions are real and reachable:

        * example ``m1`` with individual ``a_b`` and example ``m1_a`` with
          individual ``b`` both spell ``m1_a_b``;
        * example ``m1`` with individual ``a`` spells ``m1_a``, which is also
          the name of an example called ``m1_a``.

        In either case a learner handed that file can join two examples
        through one constant — the exact failure the prefixing exists to
        prevent.
        """
        names: Dict[Tuple[str, str], str] = {}
        owners: Dict[str, str] = {
            example.atom: f"the example {example.id!r}"
            for example in self.examples
        }
        for example in self.examples:
            for individual in example.structure.domain:
                name = self.individual_name(example, individual)
                mine = f"individual {individual!r} of example {example.id!r}"
                if name in owners:
                    raise IlpEncodingError(
                        f"IlpTask: {mine} and {owners[name]} both spell "
                        f"{name!r} in Prolog. One constant for two things is "
                        "exactly what the example prefix exists to prevent — "
                        "rename an example.")
                owners[name] = mine
                names[(example.atom, individual)] = name
        return names

    # -- facts --------------------------------------------------------------

    def _rows(self, structure: FiniteStructure, name: str, arity: int
              ) -> List[Tuple[str, ...]]:
        """The extension of ``name/arity`` in ``structure``, sorted.

        Materialises a computed predicate by asking it about every tuple —
        the only thing Prolog can be given — after checking the cost.
        """
        key = (name, arity)
        if key in structure.extensions:
            return sorted(structure.extensions[key])
        cost = len(structure.domain) ** arity
        if cost > self.max_computed_tuples:
            raise IlpEncodingError(
                f"IlpTask: materialising the computed predicate {name}/{arity} "
                f"over a domain of {len(structure.domain)} would cost {cost} "
                f"calls, over max_computed_tuples={self.max_computed_tuples}. "
                "Raise the bound, or leave this predicate out of "
                "body_predicates.")
        decide = structure.computed[key]
        return sorted(tuple(t) for t in product(structure.domain, repeat=arity)
                      if decide(*t))

    # -- rendering ----------------------------------------------------------

    def background_text(self) -> str:
        """``bk.pl``: the membership facts and every background fact.

        Deterministic: examples in the order given, symbols sorted, tuples
        sorted. The same task renders byte-identically every time, so a task
        directory can be diffed and committed.
        """
        membership = to_prolog_atom(self.membership)
        lines: List[str] = [
            _comment(f"background knowledge for {to_prolog_atom(self.target)}/1"),
            _comment(f"{len(self.examples)} examples; the example argument "
                     f"lives on {membership}/2 alone"),
        ]
        for (name, arity), reason in self.excluded_predicates:
            lines.append(_comment(f"left out: {name}/{arity} — {reason}"))
        lines.append("")
        lines.append(f":- discontiguous {membership}/2.")
        for name, arity in self.body_predicates:
            lines.append(f":- discontiguous {to_prolog_atom(name)}/{arity}.")

        names = self._individual_names()
        for example in self.examples:
            label = "pos" if example.label else "neg"
            header = f"{example.atom} ({label})"
            if example.note:
                header += f": {example.note}"
            lines.append("")
            lines.append(_comment(header))
            for individual in example.structure.domain:
                constant = names[(example.atom, individual)]
                lines.append(f"{membership}({example.atom},{constant}).")
            for name, arity in self.body_predicates:
                if not example.structure.interprets(name, arity):
                    continue
                functor = to_prolog_atom(name)
                for row in self._rows(example.structure, name, arity):
                    args = ",".join(names[(example.atom, i)] for i in row)
                    lines.append(f"{functor}({args}).")
        return "\n".join(lines) + "\n"

    def examples_text(self) -> str:
        """``exs.pl``: one ``pos``/``neg`` line per example."""
        target = to_prolog_atom(self.target)
        lines = []
        for example in self.examples:
            label = "pos" if example.label else "neg"
            line = f"{label}({target}({example.atom}))."
            if example.note:
                line += f"  {_comment(example.note)}"
            lines.append(line)
        return "\n".join(lines) + "\n"

    def bias_text(self) -> str:
        """``bias.pl``: the head and body declarations plus the size bounds."""
        lines = [f"head_pred({to_prolog_atom(self.target)},1).",
                 f"body_pred({to_prolog_atom(self.membership)},2)."]
        for name, arity in self.body_predicates:
            lines.append(f"body_pred({to_prolog_atom(name)},{arity}).")
        lines += [f"max_vars({self.max_vars}).",
                  f"max_body({self.max_body}).",
                  f"max_clauses({self.max_clauses})."]
        lines += list(self.extra_bias)
        return "\n".join(lines) + "\n"

    def write(self, directory: str) -> Dict[str, str]:
        """Write ``bk.pl``, ``exs.pl`` and ``bias.pl`` into ``directory``.

        The directory itself is created; its PARENT must already exist, so a
        typo in a long path fails here instead of quietly building a new tree
        somewhere nobody will look. For the same reason all three files are
        RENDERED before the directory is created: a task whose rendering is
        refused (a computed predicate over ``max_computed_tuples``) leaves
        nothing behind at all.

        Files are written with ``\\n`` line endings on every platform — Prolog
        reads either, but a task directory that differs between Windows and
        Linux is a task directory that cannot be diffed.

        Returns:
            ``{"bk": path, "exs": path, "bias": path}``.
        """
        parent = os.path.dirname(os.path.abspath(directory))
        if not os.path.isdir(parent):
            raise IlpEncodingError(
                f"IlpTask.write: the parent directory {parent!r} does not "
                "exist")
        rendered = (("bk", self.background_text()),
                    ("exs", self.examples_text()),
                    ("bias", self.bias_text()))
        os.makedirs(directory, exist_ok=True)
        paths = {}
        for stem, text in rendered:
            path = os.path.join(directory, f"{stem}.pl")
            with io.open(path, "w", encoding="utf-8", newline="\n") as handle:
                handle.write(text)
            paths[stem] = path
        return paths

    # -- reading the answer back --------------------------------------------

    def read_clause(self, clause: str, **kwargs):
        """A learned clause as a formula, in THIS task's vocabulary.

        :func:`~unicode_fol_kit.ilp.clause_to_formula` with ``membership`` and
        ``predicates`` filled in from the task, so the predicate names come
        back exactly as they were emitted and the result can be evaluated
        against the very structures the task was built from.
        """
        from .readback import clause_to_formula

        return clause_to_formula(clause, membership=self.membership,
                                 predicates=self.body_predicates, **kwargs)

    def read_hypothesis(self, text: str, **kwargs):
        """Every clause of a learner's output, in THIS task's vocabulary.

        Like :meth:`read_clause`, and additionally checks that each clause
        defines this task's target. The clauses come back separately — see
        :func:`~unicode_fol_kit.ilp.hypothesis_to_formulas` for why they are
        not disjoined for you.
        """
        from .readback import hypothesis_to_formulas

        kwargs.setdefault("target", self.target)
        return hypothesis_to_formulas(text, membership=self.membership,
                                      predicates=self.body_predicates,
                                      **kwargs)

    # -- reporting ----------------------------------------------------------

    @property
    def counts(self) -> Dict[str, int]:
        """Sizes worth knowing before handing the task to a learner: how many
        examples of each label, and how many facts the learner will see."""
        facts = 0
        for example in self.examples:
            facts += len(example.structure.domain)          # membership
            for name, arity in self.body_predicates:
                if example.structure.interprets(name, arity):
                    facts += len(self._rows(example.structure, name, arity))
        return {
            "positive": sum(1 for e in self.examples if e.label),
            "negative": sum(1 for e in self.examples if not e.label),
            "predicates": len(self.body_predicates),
            "facts": facts,
        }


ExampleSpec = Union[
    Mapping[str, FiniteStructure],
    Sequence[Tuple[str, FiniteStructure]],
]


def _as_examples(spec: ExampleSpec, label: bool) -> List[Example]:
    items: Iterable[Tuple[str, FiniteStructure]]
    items = spec.items() if isinstance(spec, Mapping) else spec
    return [Example(str(key), structure, label) for key, structure in items]


def task_from_structures(target: str, positive: ExampleSpec,
                         negative: ExampleSpec, **kwargs) -> IlpTask:
    """An :class:`IlpTask` from two id→structure collections.

    A convenience over building :class:`Example` objects by hand; every
    keyword argument is passed straight through to :class:`IlpTask`, and every
    check happens there.

    Args:
        target: the predicate to learn.
        positive: ``{"m1": structure, …}`` or ``[("m1", structure), …]``.
        negative: the same, for the negative examples.
    """
    return IlpTask(target,
                   tuple(_as_examples(positive, True)
                         + _as_examples(negative, False)),
                   **kwargs)
