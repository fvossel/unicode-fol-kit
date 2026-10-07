"""What the whole-problem TPTP writers share: premise names and the entry point's name.

Every whole-problem writer (the ``fof`` writer in :mod:`~unicode_logic_kit.atp._tptp_problem`,
the TF0 writer in :mod:`~unicode_logic_kit.atp.tptp_tff` and the TFA writer in
:mod:`~unicode_logic_kit.atp._tff_problem`) writes one ``axiom`` line per premise. By default
the lines are called ``premise_1``, ``premise_2``, ... and ``premise_names=`` lets a caller
name them, so that what a prover prints about its proof (the axioms it used) can be read
as the caller's own names: a TPTP library problem keeps the names of its axioms, and an
application that holds its premises under identifiers wants them back.

**What is written.** A name is a TPTP ``<name>``: a lower-case word
(``[a-z][A-Za-z0-9_]*``) or an unsigned integer without leading zeros is written as it
is, and anything else is a single-quoted word in which ``\\`` and ``'`` are escaped
(``it's`` is written ``'it\\'s'``). A name that no TPTP name can spell is refused: the
empty name, a name with a control character (a line break would end the statement, and the
TPTP grammar of a quoted word has no spelling for a character below the space), and a
string that cannot be encoded as UTF-8 (a lone surrogate). A non-ASCII letter is written
as it is: Vampire and E read UTF-8 and print it back unchanged.

**What is checked.** The names are pairwise distinct AS WRITTEN, and each is distinct from
every name the writer generates for the other lines of the problem (the conjecture
``goal``, the non-emptiness line of a sort, the membership line of a sorted constant, the
type declarations). A clash is a ``ValueError`` that names both. A name that a prover's
OWN output uses for something else is refused too (:func:`prover_own_name`): Vampire prints
``unknown`` for an axiom whose name it does not know and numbers its statements ``f1``,
``f2``, ..., and E names the clauses it derives ``c_0_5`` and ``i_0_5``; a premise called
by one of these would be read back as another formula.

**What comes back.** The writer returns a
:class:`~unicode_logic_kit.atp._tptp_problem.TptpNameMap`, which records the premise names
in order (also the default ones) and the names and meaning of the background axioms the
writer added. :func:`axiom_leaf_label` and :func:`match_premise_label` read a prover's
printed axiom names against that record.

**What a prover prints.** Vampire echoes the name of an axiom only when asked
(``--output_axiom_names on``) and then in the second argument of the leaf's ``file(...)``
source; E prints the name as the statement name and in that argument too. Measured on
Vampire 5.0.1 and E 3.5.1: both print a quoted name back unchanged, except that E reads a
backslash followed by any character as one backslash, so an apostrophe in a name comes
back from E as a backslash (``it's`` is printed ``it\\s``). :func:`match_premise_label`
takes that into account when it is told the prover is E and refuses to choose between
two names that E would print alike.

**The entry point's name.** A refusal of a whole-problem writer starts with the name of the
function the caller called (:func:`refusals_speak_as`).
"""

import contextlib
import re
from typing import Dict, Iterable, Iterator, List, Optional, Sequence, Tuple

__all__: List[str] = []

#: A TPTP lower word, which is a name as it stands.
_LOWER_WORD = re.compile(r"[a-z][A-Za-z0-9_]*")

#: An unsigned integer without leading zeros, which is a TPTP name as it stands.
_INTEGER = re.compile(r"0|[1-9][0-9]*")


def default_premise_names(count: int) -> Tuple[str, ...]:
    """``premise_1`` ... ``premise_<count>``: the names every writer uses by default."""
    return tuple(f"premise_{i}" for i in range(1, count + 1))


def names_kwargs(premise_names: Optional[Sequence[str]]) -> Dict[str, Sequence[str]]:
    """``{"premise_names": premise_names}``, or ``{}`` when it is ``None``: a caller that
    forwards the argument to a writer it did not write passes it only when it was given."""
    return {} if premise_names is None else {"premise_names": premise_names}


def tptp_name_token(name: str) -> str:
    """The TPTP spelling of ``name`` (see the module docstring): the name itself when it
    is a lower word or an unsigned integer, otherwise a single-quoted word with ``\\`` and
    ``'`` escaped. ``name`` must be a name :func:`normalise_premise_names` accepts."""
    if _LOWER_WORD.fullmatch(name) or _INTEGER.fullmatch(name):
        return name
    return "'" + name.replace("\\", "\\\\").replace("'", "\\'") + "'"


def decode_tptp_name(token: str) -> str:
    """The text a TPTP name token stands for: a single-quoted word without its quotes and
    with ``\\\\`` read as ``\\`` and ``\\'`` as ``'``; any other token (a lower word, an
    integer) as it is. A backslash before any other character is kept as it is."""
    token = token.strip()
    if len(token) >= 2 and token[0] == "'" and token[-1] == "'":
        out: List[str] = []
        body = token[1:-1]
        i = 0
        while i < len(body):
            c = body[i]
            if c == "\\" and i + 1 < len(body) and body[i + 1] in ("\\", "'"):
                out.append(body[i + 1])
                i += 2
            else:
                out.append(c)
                i += 1
        return "".join(out)
    return token


#: Names a prover's output uses for something of its own, with what each is. Measured on
#: Vampire 5.0.1 and E 3.5.1: Vampire prints ``unknown`` as the name of an axiom it was not
#: told the name of, and names its statements ``f<k>`` (and the ``sat_conversion`` ones
#: ``s<k>``); E keeps the names of the problem's axioms and calls every clause it derives
#: ``c_<i>_<j>`` (``i_<i>_<j>`` in some of its strategies).
_PROVER_OWN_NAMES = (
    (re.compile(r"unknown"), "the word Vampire prints for an axiom whose name it does not know"),
    (re.compile(r"f[0-9]+"), "a name Vampire gives its own statements (f1, f2, ...)"),
    (re.compile(r"[ci]_[0-9]+_[0-9]+"), "a name E gives the clauses it derives (c_0_5, i_0_5)"),
)


def prover_own_name(name: str) -> Optional[str]:
    """What a prover uses ``name`` for in its own output (a sentence), or ``None`` when it is
    not a name the provers use: the name of a premise must not be one, because the premise
    that a proof's leaf is read as is decided by the name the prover prints for it."""
    for pattern, what in _PROVER_OWN_NAMES:
        if pattern.fullmatch(name):
            return what
    return None


def _unspellable(name: str) -> Optional[str]:
    """Why no TPTP name spells ``name``, or ``None`` when one does."""
    if name == "":
        return "it is empty"
    for ch in name:
        if ord(ch) < 0x20 or ord(ch) == 0x7F:
            return (f"it contains the control character U+{ord(ch):04X}, which a TPTP "
                    "quoted name cannot spell")
    try:
        name.encode("utf-8")
    except UnicodeEncodeError:
        return "it cannot be encoded as UTF-8 (it contains a lone surrogate)"
    return None


def normalise_premise_names(premise_names: Optional[Sequence[str]], count: int,
                            *, where: str) -> Tuple[str, ...]:
    """The names of ``count`` premises: ``premise_names`` checked, or the default ones.

    Raises:
        TypeError: ``premise_names`` is one string rather than a sequence of strings, or
            one of its entries is not a string.
        ValueError: it holds other than one name per premise, a name no TPTP name spells
            (see the module docstring), a name a prover uses in its own output
            (:func:`prover_own_name`), or two names that are the same as written.
    """
    if premise_names is None:
        return default_premise_names(count)
    if isinstance(premise_names, (str, bytes)):
        raise TypeError(
            f"{where}: premise_names is a sequence of strings, one per premise; got the "
            f"single {type(premise_names).__name__} {premise_names!r}")
    names = tuple(premise_names)
    for i, name in enumerate(names):
        if not isinstance(name, str):
            raise TypeError(
                f"{where}: premise_names[{i}] must be a string, got "
                f"{type(name).__name__} {name!r}")
    if len(names) != count:
        raise ValueError(
            f"{where}: premise_names must hold one name per premise, but there "
            f"{'is' if count == 1 else 'are'} {count} premise{'' if count == 1 else 's'} "
            f"and {len(names)} name{'' if len(names) == 1 else 's'}")
    written: Dict[str, int] = {}
    for i, name in enumerate(names):
        why = _unspellable(name)
        if why is not None:
            raise ValueError(f"{where}: premise_names[{i}] = {name!r} is not a premise "
                             f"name: {why}")
        own = prover_own_name(name)
        if own is not None:
            raise ValueError(
                f"{where}: premise_names[{i}] = {name!r} is {own}, so a proof that uses this "
                "premise could be read as using another; give the premise another name")
        token = tptp_name_token(name)
        if token in written:
            raise ValueError(
                f"{where}: premise_names[{written[token]}] and premise_names[{i}] are "
                f"both {name!r}, which is written {token}; premise names must be pairwise "
                "distinct as written")
        written[token] = i
    return names


def name_background_premises(premise_names: Sequence[str], given: int, total: int,
                             *, where: str) -> Tuple[str, ...]:
    """``premise_names`` for ``given`` premises, extended by one name for each of the
    ``total - given`` premises a caller's routine appended after them.

    The sentences a signature declares (``api.prove(signature=...)``) and the side axioms
    of a :class:`~unicode_logic_kit.logic.Sentence` follow the premises the caller passed.
    The caller names the premises it passed; the others are background, named
    ``background_<k>`` (``k`` from 1) by the writer, with ``_`` appended to a name that is
    already one of the caller's, as written. ``premise_names`` is checked as every writer
    checks it (:func:`normalise_premise_names`) against ``given``, and the message names
    ``where``.

    Raises:
        TypeError: ``premise_names`` is one string rather than a sequence of strings, or
            one of its entries is not a string.
        ValueError: it holds other than ``given`` names, a name no TPTP name spells, a name a
            prover uses in its own output (:func:`prover_own_name`), or two names that are the
            same as written.
    """
    names = normalise_premise_names(premise_names, given, where=where)
    taken = {tptp_name_token(name) for name in names}
    extended = list(names)
    for k in range(1, total - given + 1):
        candidate = f"background_{k}"
        while tptp_name_token(candidate) in taken:
            candidate += "_"
        taken.add(tptp_name_token(candidate))
        extended.append(candidate)
    return tuple(extended)


def check_against_generated(names: Sequence[str], generated: Iterable[Tuple[str, str]],
                            *, where: str) -> None:
    """Refuse a premise name that is one of the names the writer gives its own lines.

    ``generated`` holds ``(written name, what the writer uses it for)`` for every other
    line of the problem. Raises ``ValueError`` naming the premise and the line."""
    used = {tptp_name_token(name): i for i, name in enumerate(names)}
    for written, what in generated:
        i = used.get(written)
        if i is not None:
            raise ValueError(
                f"{where}: premise_names[{i}] = {names[i]!r} is the name the writer gives "
                f"{what} ({written}); give the premise another name")


def axiom_leaf_label(name_token: str, source_text: Optional[str]) -> str:
    """The name under which the problem called an axiom leaf of a proof, as printed.

    E names the statement after the axiom, and Vampire (asked for axiom names) puts the
    name in the second argument of the ``file(path, name)`` source of a leaf whose own
    name is its running number. A ``file(...)`` source that names nothing (Vampire without
    the option prints the word ``unknown``) leaves the statement's own name."""
    if source_text is not None and source_text.startswith("file(") and source_text.endswith(")"):
        from .tstp import _split_top_level
        fields = _split_top_level(source_text[len("file("):-1])
        if len(fields) >= 2 and fields[1].strip() not in ("", "unknown"):
            return decode_tptp_name(fields[1])
    return decode_tptp_name(name_token)


def _as_eprover_prints(name: str) -> str:
    """What E prints for the premise ``name``: it reads a backslash and the character after
    it as one backslash, so every apostrophe of the written name (``\\'``) is a backslash."""
    return name.replace("'", "\\")


def match_premise_label(label: str, names: Sequence[str],
                        *, eprover: bool = False) -> Optional[int]:
    """The 0-based index of the premise a printed axiom ``label`` names, or ``None``.

    ``label`` is the decoded name a prover printed (:func:`axiom_leaf_label`). With
    ``eprover=True`` the premise names are compared as E prints them (see the module
    docstring), and a label that two or more premises would be printed as is not matched
    (``None``): the proof does not say which of them it used."""
    if not eprover:
        for i, name in enumerate(names):
            if name == label:
                return i
        return None
    hits = [i for i, name in enumerate(names) if _as_eprover_prints(name) == label]
    return hits[0] if len(hits) == 1 else None


@contextlib.contextmanager
def refusals_speak_as(own: str, default: str) -> Iterator[None]:
    """Word the refusals raised inside the block as coming from ``own``.

    A writer's inner checks open their messages with the name of the writer function they
    were written for (``default``); a caller of another entry point over the same checks
    (``generate_tff_problem_with_mapping`` over the body of ``generate_tff_problem``) is
    told its own name instead. Only a message that opens with ``default`` and a colon is
    changed, so the message of a check of another layer (``Node.to_tptp: ...``) stays as
    it is; the exception keeps its class, its other arguments and its traceback."""
    try:
        yield
    except (NotImplementedError, ValueError) as exc:
        prefix = default + ":"
        if exc.args and isinstance(exc.args[0], str) and exc.args[0].startswith(prefix):
            exc.args = (own + exc.args[0][len(default):],) + exc.args[1:]
        raise
