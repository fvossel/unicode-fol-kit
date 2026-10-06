"""One TPTP word is one kit symbol: the shared collision check and the render guard.

``Node.to_tptp`` writes a predicate, function or constant under its kit name with
the FIRST character folded to lower-case (:func:`~unicode_fol_kit.fol._fol_nodes
.tptp_fold_first_letter`), so two DISTINCT kit names of one kind (``gaseous`` and
``Gaseous``; ``Foo`` and ``foo``; ``Bar`` and ``bar``) are written as one word.
Rendered inside one formula that turns a non-theorem into a tautology:
``p(gaseous) <=> p(Gaseous)`` is written ``(p(gaseous) <=> p(gaseous))``.

This module is the ONE implementation of the check that refuses it. Two callers
share it:

* the problem writers (:mod:`unicode_fol_kit.atp._tptp_problem` and the TFF
  writers), which check every premise and the conclusion TOGETHER through
  :func:`check_no_symbol_collisions`; and
* every ``Node.to_tptp()`` call, through the guard below, which checks the ONE
  formula it renders.

**What is refused.** Every case below is two kit symbols written as one word, or
a word no prover reads; the message names both symbols (or the one name) and the
word:

* two DISTINCT names of one namespace that fold to one word (the case above);
* an arithmetic or comparison symbol and a user symbol that is written like it:
  ``+`` is written ``$sum``, so a function that is itself named ``$sum`` is one
  word with it (``<`` is ``$less``, ``=`` is ``=``, and so on);
* a number and a constant spelled like it: ``Number(1)`` and ``Constant('1')`` are
  both written ``1``;
* two VARIABLES that are written as one TPTP variable. A variable is written as
  the upper-case of its name, so ``x`` and ``X`` (and ``ı`` and ``i``) are one
  variable and ``∀x ∃X R(x, X)`` would be written ``![X]: ?[X]: r(X,X)``. The
  scope of a variable is one formula, so the writers check this per formula;
* a predicate, function or constant name that is written as something that is not
  a TPTP word. An unquoted TPTP name is a lower-case letter followed by letters,
  digits and underscores (``has-part``, ``2008SummerOlympics``, ``_x`` and a
  non-ASCII predicate name are not), and the text of such a rendering is rejected
  by Vampire and by E. A name is refused, never written as it is. A name that is
  written with a leading ``$`` (``$foo``) is one of TPTP's OWN words, so it is
  refused as a RESERVED word, not as a malformed one. (The problem writers rewrite
  such a predicate, function or constant name and record the rewrite, and the
  replacement is chosen so that it equals no sort guard of the problem either, so
  a problem built by them meets this refusal only for a SORT name: the fof writer
  reads a sort as its guard predicate and does not rewrite it.)
* a variable that is written as something that is not a TPTP variable. A TPTP
  variable is an upper-case letter followed by letters, digits and underscores, and
  a variable is written as the upper-case of its name, so ``ä`` (written ``Ä``),
  ``x-1`` and ``1x`` have no rendering. A variable is BOUND, so the problem writers
  rename it to a fresh legal one without recording anything
  (:func:`legalise_variables`); a single formula has no map to hand back and
  refuses it by name.

**The two defined propositions.** ``$true`` and ``$false`` are TPTP's own
propositions, and this kit's reader (:mod:`unicode_fol_kit.fol.tptp_input`) reads
them as the NULLARY atoms ``Atom('$true')`` / ``Atom('$false')``
(:func:`is_tptp_boolean_atom`). They are not symbols of the user's: the single
formula writes them verbatim, the problem writers neither rewrite nor declare them,
and the checks here never count them. ``to_z3`` reads them as the constants true
and false, so that z3 and the TPTP provers answer the question the TPTP text asks.
Any OTHER ``$``-word, and ``$true`` itself WITH arguments, is refused as reserved.
The nullary atoms named like the glyphs ``⊤`` and ``⊥`` are the same two propositions
(:func:`truth_constant_word`): they are written as ``$true`` and ``$false``, never as
a letter.

**Namespaces.** Predicates are one namespace; functions, constants, numerals and
the arithmetic function words together are the other (a TPTP reader resolves a
bare identifier by its position, and this kit's own reader does); variables are a
third, checked per formula. Only two DISTINCT symbols inside the SAME namespace
that are written as one word are refused. A predicate and a function/constant that
share a word are not refused here (see the module docstring of
:mod:`unicode_fol_kit.atp._tptp_problem` for why the WRITERS rename the term
side instead): the text of one formula is unambiguous by position, and only a
writer can hand back the name map a caller needs to translate a proof back.

**A sort is the guard predicate of its name.** ``∀x:S φ`` is written
``![X]: (s(X) => φ)``: the kit's semantics of a sort is that predicate (it is what
``to_z3``, the fof writer and the Prover9 writer do), so the sort ``Foo`` and a
predicate ``foo`` are one word of the predicate namespace and are refused like any
other pair, and the sort ``Car`` next to the predicate ``Car`` is ONE symbol. The
TF0 writer cannot say that (it declares a type and a predicate), so it refuses a
sort and a predicate that share a word (:mod:`unicode_fol_kit.atp.tptp_tff`).

**The asymmetry is deliberate, for this release.** A name TPTP cannot spell, or
a predicate that clashes with a function/constant, is renamed by the writers and
recorded in the name map; two LEGAL names of one kind that fold together are
refused by name, never renamed. The same-kind refusal predates the name map and
is kept so that no existing caller silently receives a symbol renamed behind its
back; it is not a claim that the two situations differ in principle.

**The guard.** ``Node.to_tptp`` is implemented recursively in about seventy
places across the node families, and several families reduce before rendering
(a ``SortedQuantifier`` renders through a FOL reduction that introduces a sort
guard predicate; a ``Count`` renders through its distinct-witnesses expansion; a
``Measure`` writes the function ``measure``). A scan of the SOURCE tree would
miss every name a reduction introduces, so the guard records what is actually
RENDERED instead: while an outermost ``to_tptp`` call is running, every node
whose ``to_tptp`` is entered, at any depth, reports the symbol it writes
(:meth:`~unicode_fol_kit.fol._fol_nodes.Node._tptp_symbol`), and when the
outermost call returns the recorded symbols are checked once.

It is installed centrally. :meth:`Node.__init_subclass__
<unicode_fol_kit.fol._fol_nodes.Node.__init_subclass__>` replaces whatever
``to_tptp`` a new node class resolves to (its own, or one inherited from a mixin)
with a :class:`GuardedToTptp` descriptor, so no family edits its methods and a
future family is covered without anyone remembering to ask.

* **Only the outermost call scans.** A contextvar holds the log of the render in
  progress; a call that finds one is nested and only records. The contextvar is
  reset in a ``finally``, so a refusal, or a family's own ``NotImplementedError``
  (a modal node has no TPTP form), leaves the next call guarded again. A
  contextvar rather than a module global makes it safe across threads (a new
  thread starts with no render in progress) and across re-entrancy.
* **Nested calls cost no stack frame per level.** The descriptor's ``__get__``
  returns the ORIGINAL bound method while a render is in progress, so a recursive
  render has the stack depth it had before the guard existed plus ONE frame (the
  outermost call's wrapper) and none per level: a left-nested conjunction of about
  990 conjuncts still renders, one level fewer than without the guard (measured:
  992 and 991 against the interpreter's limit of 1000). A wrapper function on
  every level would double the frames per level. The guard is not free in time:
  every rendered node names its symbol once, which makes a render about 1.5 to 2
  times slower than the same render without the guard (measured on a left-nested
  chain of 800 conjuncts and on a balanced formula of 2048 leaves).
* **Byte-identical output.** The guard never touches the text: for a formula it
  accepts, the string returned is the string the unguarded method returned.
"""

import contextvars
import functools
import inspect
import re
import types
from typing import Any, Callable, Dict, Iterable, Iterator, List, Optional, Tuple

#: ``(namespace, rendered word, kit name, kind label)`` — one symbol a text
#: contains, which is what :func:`check_symbols` works on. ``namespace`` is
#: ``"predicate"``, ``"term"`` (functions, constants, numerals and the arithmetic
#: function words share it) or ``"variable"``. ``kind label`` says what the symbol
#: is: ``"predicate"``, ``"function"`` and ``"constant/function"`` are NAMES a
#: user chose; ``"reserved predicate"`` / ``"reserved function"`` are the
#: comparison and arithmetic symbols, which TPTP spells with a word of its own
#: (``<`` is ``$less``, ``+`` is ``$sum``); ``"numeral"`` is a number; ``"variable"``
#: is a variable.
Symbol = Tuple[str, str, str, str]

#: What a node reports it writes (``Node._tptp_symbol``): ``(resolver, kit
#: name)``. The hook runs once per node of every rendered formula, so it only
#: names the symbol; ``resolver(kit name)`` (the first-letter fold, the ASCII
#: transliteration) runs once per DISTINCT name, when the symbols are checked.
#: A resolver returns ``(namespace, word, kind label)``, optionally followed by
#: the name to show in a refusal when that is not the kit name itself (a number
#: shows the text it is written as), or ``None`` for a token that writes nothing.
Writes = Tuple[Callable[[Any], Optional[Tuple[str, ...]]], Any]

#: The kinds that are NAMES a user chose, which must be words TPTP reads.
_NAME_KINDS = frozenset({"predicate", "function", "constant/function"})

#: An unquoted TPTP variable: an upper-case letter, then letters, digits and
#: underscores (``upper_word`` of the TPTP grammar).
_LEGAL_VARIABLE = re.compile(r"[A-Z][A-Za-z0-9_]*")

#: TPTP's two DEFINED propositions, which the kit's own TPTP reader produces as
#: nullary atoms of exactly these names. See the module docstring.
TPTP_BOOLEAN_CONSTANTS = frozenset({"$true", "$false"})

#: The unicode glyphs of the same two constants, as the NAME of a nullary atom, and
#: the TPTP word each one stands for. ``Atom('⊤')`` prints as the glyph, the glyph
#: reads back as ``Atom('$true')``, and the two atoms are ONE constant on every
#: route: no route may read the glyph-named atom as a propositional letter.
TRUTH_GLYPH_ATOMS = {"⊤": "$true", "⊥": "$false"}


def truth_constant_word(atom) -> Optional[str]:
    """The TPTP word of the truth constant ``atom`` is, or ``None`` for any other atom.

    ``'$true'`` for the nullary atoms ``$true`` and ``⊤``, ``'$false'`` for the nullary
    atoms ``$false`` and ``⊥``. An atom WITH arguments is a user predicate that happens
    to be spelled like one of these names and is none of them.
    """
    if atom.args:
        return None
    if atom.predicate in TPTP_BOOLEAN_CONSTANTS:
        return atom.predicate
    return TRUTH_GLYPH_ATOMS.get(atom.predicate)


def is_tptp_boolean_atom(atom) -> bool:
    """Whether ``atom`` is one of the truth constants: the nullary atom ``$true`` or
    ``$false`` (the propositions TPTP itself defines) or the nullary atom named like
    one of the glyphs ``⊤`` / ``⊥`` (:data:`TRUTH_GLYPH_ATOMS`). None of these is a
    symbol of the user's. A name of these WITH arguments is a user predicate that
    happens to be spelled like a reserved word, and is not."""
    return truth_constant_word(atom) is not None

#: An unquoted TPTP predicate, function or constant: a lower-case letter, then
#: letters, digits and underscores (``lower_word`` of the TPTP grammar).
_LEGAL_WORD = re.compile(r"[a-z][A-Za-z0-9_]*")


# ---------------------------------------------------------------------------
# The check — one implementation, two callers.
# ---------------------------------------------------------------------------

def _label(kind: str) -> str:
    return "constant" if kind == "constant/function" else kind


def _describe(original: str, kind: str) -> str:
    if kind == "numeral":
        return f"the number {original}"
    if kind == "reserved predicate":
        return f"the comparison {original!r}"
    if kind == "reserved function":
        return f"the arithmetic function {original!r}"
    return f"the {_label(kind)} {original!r}"


def _why(first_kind: str, second_kind: str, dialect: str = "tptp") -> str:
    kinds = {first_kind, second_kind}
    if "variable" in kinds:
        if dialect == "prover9":
            return ("under prolog_style_variables a Prover9 variable is an "
                    "upper-case word, so Node.to_prover9 upper-cases a variable's name")
        return ("a TPTP variable is an upper-case word, so Node.to_tptp "
                "upper-cases a variable's name")
    if "numeral" in kinds:
        return "a number is written as its own text, which is also how a constant of that name is written"
    return ("TPTP spells that comparison or arithmetic symbol with a dollar-word "
            "of its own, which a symbol named like it would also be written as")


def _refusal(where: str, subject: str, first: Tuple[str, str],
             second: Tuple[str, str], rendered: str,
             dialect: str = "tptp") -> NotImplementedError:
    (prior, prior_kind), (original, kind) = first, second
    if prior_kind in _NAME_KINDS and kind in _NAME_KINDS:
        return NotImplementedError(
            f"{where}: distinct {kind} names {prior!r} and {original!r} would "
            f"both render as the TPTP identifier {rendered!r} (Node.to_tptp folds "
            "only the first character to lower-case, so it cannot tell these two "
            "apart) — refusing to silently merge two distinct symbols into one; "
            f"rename one of them before exporting this {subject}."
        )
    return NotImplementedError(
        f"{where}: {_describe(prior, prior_kind)} and {_describe(original, kind)} would "
        f"both render as the {'Prover9' if dialect == 'prover9' else 'TPTP'} identifier "
        f"{rendered!r} ({_why(prior_kind, kind, dialect)}) "
        "— refusing to silently merge two distinct symbols into one; "
        f"rename one of them before exporting this {subject}."
    )


def _illegal(where: str, subject: str, kind: str, original: str,
             rendered: str, *, sort: bool = False) -> NotImplementedError:
    remedy = (
        "rename it, or build the problem with generate_tptp_problem_with_mapping "
        "or generate_tff_problem_with_mapping, which write such a name under a "
        "legal replacement and return the map that undoes it"
        if subject == "formula" else
        "rename it (generate_tff_problem_with_mapping writes a sort under a legal "
        "replacement; the fof writer does not)")
    what = (f"the sort {original!r} (its guard predicate {rendered!r})" if sort
            else f"the {_label(kind)} name {original!r}")
    if rendered.startswith("$"):
        why = (f"which is a RESERVED TPTP word (every word that starts with '$' is "
               "TPTP's own: $true, $false, $sum, $less, the types $i and $o, and the "
               "'$$' system words; a prover reads it as that word or rejects it, so "
               "it can never name a symbol of the user's)")
    else:
        why = ("which is not a TPTP word (an unquoted TPTP name is a lower-case letter "
               "followed by letters, digits and underscores, and no prover reads any "
               "other)")
    return NotImplementedError(
        f"{where}: {what} would be written as {rendered!r}, "
        f"{why} — refusing to write text that is not TPTP; "
        f"{remedy}."
    )


def _illegal_variable(where: str, subject: str, original: str,
                      rendered: str) -> NotImplementedError:
    remedy = (
        "rename the variable, or build the problem with generate_tptp_problem_with_mapping, "
        "generate_tff_problem_with_mapping or generate_tff_arith_problem, which write a "
        "variable under a fresh legal name (a variable is bound, so nothing is recorded)"
        if subject == "formula" else
        "rename the variable")
    return NotImplementedError(
        f"{where}: the variable name {original!r} would be written as {rendered!r}, "
        "which is not a TPTP variable (an unquoted TPTP variable is an upper-case "
        "letter followed by letters, digits and underscores, and no prover reads any "
        "other; a variable is written as the upper-case of its name) — refusing to "
        f"write text that is not TPTP; {remedy}."
    )


def check_symbols(symbols: Iterable[Symbol], *, where: str, subject: str,
                  dialect: str = "tptp", sorts: Iterable[str] = ()) -> None:
    """Raise ``NotImplementedError`` if two DISTINCT kit symbols of one namespace
    are written as the same TPTP word, or if a name is written as a word that is
    not TPTP.

    ``symbols`` is every symbol the text contains, in the order they were met;
    the same kit name repeating (the ordinary case of one predicate used twice)
    is not a collision, and a function and a constant of one name are one symbol.
    The message names both kit symbols and the shared word; ``where`` prefixes it
    and ``subject`` ("problem" / "formula") ends it. Collisions are decided over
    every symbol first, then each written name must be a legal TPTP word and each
    written variable a legal TPTP variable, so the more specific refusal wins.

    ``dialect="prover9"`` asks for the collision check of the VARIABLES only, worded
    for Prover9 (the same ``upper-case of the name``), and none of the TPTP
    legality rules. ``sorts`` names the kit sorts of the problem: a predicate that
    is the guard of one is reported as that sort when its word is illegal.
    """
    seen: Dict[Tuple[str, str], Tuple[str, str]] = {}
    written: Dict[Tuple[str, str, str], str] = {}
    variables: Dict[Tuple[str, str], None] = {}
    for namespace, rendered, original, kind in symbols:
        key = (namespace, rendered)
        prior = seen.get(key)
        if prior is None:
            seen[key] = (original, kind)
        elif (prior[0], prior[1] == "numeral") != (original, kind == "numeral"):
            raise _refusal(where, subject, prior, (original, kind), rendered, dialect)
        if kind in _NAME_KINDS:
            written.setdefault((namespace, rendered, original), kind)
        elif kind == "variable":
            variables.setdefault((rendered, original))
    if dialect != "tptp":
        return
    sort_names = frozenset(sorts)
    for (namespace, rendered, original), kind in written.items():
        if not _LEGAL_WORD.fullmatch(rendered):
            raise _illegal(where, subject, kind, original, rendered,
                           sort=kind == "predicate" and original in sort_names)
    for rendered, original in variables:
        if not _LEGAL_VARIABLE.fullmatch(rendered):
            raise _illegal_variable(where, subject, original, rendered)


def _resolve(writes: Writes) -> Optional[Symbol]:
    resolver, name = writes
    found = resolver(name)
    if found is None:
        return None
    return (found[0], found[1], found[3] if len(found) > 3 else name, found[2])


def _symbols_of(formula) -> Iterator[Symbol]:
    for node in formula.walk():
        writes = node._tptp_symbol()
        if writes is not None:
            symbol = _resolve(writes)
            if symbol is not None:
                yield symbol


def check_no_symbol_collisions(formulas: Iterable, *, where: str,
                               subject: str = "problem",
                               sorts: Iterable[str] = ()) -> None:
    """:func:`check_symbols` over every node of every formula in ``formulas``,
    walked in pre-order — the whole-problem check of the writers.

    Predicates, functions, constants and numerals are one pool for the whole
    problem. A VARIABLE is scoped to its own formula (``∀x P(x)`` in one premise
    and ``∀X Q(X)`` in another are two quantifiers that bind separately), so the
    variables are checked once per formula. ``sorts`` is passed on to
    :func:`check_symbols`."""
    sorts = frozenset(sorts)

    def pooled() -> Iterator[Symbol]:
        for formula in formulas:
            variables: List[Symbol] = []
            for symbol in _symbols_of(formula):
                if symbol[0] == "variable":
                    variables.append(symbol)
                else:
                    yield symbol
            check_symbols(variables, where=where, subject=subject)
    check_symbols(pooled(), where=where, subject=subject, sorts=sorts)


def check_variable_names(formula, *, where: str, subject: str = "problem",
                         dialect: str = "tptp") -> None:
    """The variable part of :func:`check_no_symbol_collisions` for ONE formula:
    refuse two distinct variable names that are written as one TPTP variable
    (``x`` and ``X``), and a variable that is written as no TPTP variable at all.
    For a writer that renders a formula itself rather than through
    ``Node.to_tptp``, which runs this check on its own.

    ``dialect="prover9"`` is the same check for the Prover9 writer: Prover9 writes
    a variable as the upper-case of its name too, so ``x`` and ``X`` are one
    variable there as well; only the collision is refused (Prover9's own reading
    of a name is not the TPTP grammar)."""
    check_symbols((symbol for symbol in _symbols_of(formula) if symbol[0] == "variable"),
                  where=where, subject=subject, dialect=dialect)


def legalise_variables(formula):
    """``formula`` with every variable that has no TPTP spelling renamed to a fresh
    one; the very same object when there is none.

    A variable is written as the upper-case of its name, and a TPTP variable is an
    upper-case letter followed by letters, digits and underscores, so ``ä`` (written
    ``Ä``), ``x-1`` and ``1x`` cannot be written as they are. A variable is BOUND,
    which is why a writer may rename it without recording anything: the rename is
    alpha-conversion, applied to the binder and to every occurrence alike.

    * **per formula** — the scope of a variable is one formula, so the caller passes
      one formula at a time;
    * **injective** — distinct illegal names get distinct new names (``ä`` and ``Ä``
      stay two variables, which writing both as ``Ä`` would have made one);
    * **capture-free** — a new name is one of :func:`unicode_fol_kit.fol._identifiers
      .fresh_variables` (``x0``, ``x1``, ... written ``X0``, ``X1``, ...) that equals
      no variable of the formula *as written*: it avoids every name of the formula
      and the lower-case of every written form (``X0`` blocks ``x0``), so a legal
      variable is never taken over.

    Two LEGAL names that are written as one (``x`` and ``X``) are not touched; they
    are refused by :func:`check_variable_names`, as they always were."""
    from . import _identifiers
    from ._fol_nodes import Variable

    names: List[str] = []
    seen = set()
    for node in formula.walk():
        if isinstance(node, Variable) and node.name not in seen:
            seen.add(node.name)
            names.append(node.name)
    illegal = [n for n in names if not _LEGAL_VARIABLE.fullmatch(n.upper())]
    if not illegal:
        return formula
    avoid = set(_identifiers.variable_names(formula))
    avoid |= {n.upper().lower() for n in avoid}
    fresh = _identifiers.fresh_variables(len(illegal), letter="x", avoid=avoid)
    table = dict(zip(illegal, fresh))

    def rename(node):
        if isinstance(node, Variable):
            return Variable(table.get(node.name, node.name))
        return node.map_children(rename)

    return rename(formula)


# ---------------------------------------------------------------------------
# The guard — one scan per outermost ``to_tptp`` call.
# ---------------------------------------------------------------------------

class _RenderLog:
    """What one outermost render has written so far: every distinct
    ``(resolver, kit name)`` a node reported, in the order first met."""

    __slots__ = ("symbols",)

    def __init__(self) -> None:
        self.symbols: Dict[Writes, None] = {}

    def note(self, node) -> None:
        writes = node._tptp_symbol()
        if writes is not None:
            self.symbols.setdefault(writes)


#: The render in progress in THIS context (thread / task), or ``None``.
_RENDERING: "contextvars.ContextVar[Optional[_RenderLog]]" = contextvars.ContextVar(
    "unicode_fol_kit_tptp_render", default=None)


def _scan_rendered_symbols(log: _RenderLog) -> None:
    """The scan: called exactly once per outermost ``to_tptp`` call that
    returned a text. Looked up by name at call time so a test can count it."""
    resolved = (_resolve(writes) for writes in log.symbols)
    check_symbols((symbol for symbol in resolved if symbol is not None),
                  where="Node.to_tptp", subject="formula")


def _outermost(function: Callable) -> Callable:
    @functools.wraps(function)
    def to_tptp(node, *args, **kwargs):
        log = _RENDERING.get()
        if log is not None:                    # nested: record, do not scan
            log.note(node)
            return function(node, *args, **kwargs)
        log = _RenderLog()
        token = _RENDERING.set(log)
        try:
            log.note(node)
            text = function(node, *args, **kwargs)
        finally:
            _RENDERING.reset(token)
        _scan_rendered_symbols(log)
        return text
    return to_tptp


class GuardedToTptp:
    """The descriptor :func:`guard_class` puts in place of a ``to_tptp`` method.

    ``Class.to_tptp`` is the guarded plain function. ``node.to_tptp`` is the
    guarded bound method when no render is in progress, and the ORIGINAL bound
    method (after recording the node) when one is — which is what keeps a
    nested call from costing a stack frame. ``__wrapped__`` is the original
    function.
    """

    def __init__(self, function: Callable) -> None:
        for attribute in ("__module__", "__name__", "__qualname__", "__doc__"):
            setattr(self, attribute, getattr(function, attribute))
        self.__wrapped__ = function
        self._function = function
        self._guarded = _outermost(function)

    def __get__(self, node, owner=None):
        if node is None:
            return self._guarded
        log = _RENDERING.get()
        if log is None:
            return types.MethodType(self._guarded, node)
        # Nested: record what this node writes (``_RenderLog.note``, inlined —
        # this runs once per node of every rendered formula) and hand back the
        # ORIGINAL method.
        writes = node._tptp_symbol()
        if writes is not None:
            log.symbols.setdefault(writes)
        return types.MethodType(self._function, node)


def is_guarded(cls: type) -> bool:
    """Whether ``cls.to_tptp`` (resolved through the MRO, unbound) is guarded."""
    return isinstance(inspect.getattr_static(cls, "to_tptp", None), GuardedToTptp)


def guard_class(cls: type) -> None:
    """Make ``cls.to_tptp`` guarded, whatever it resolves to through the MRO.

    Called from ``Node.__init_subclass__`` for every node class, and once for
    ``Node`` itself. A ``to_tptp`` that is already guarded (inherited) is left
    alone; one inherited from a mixin is wrapped on ``cls``. A ``to_tptp`` that
    is not a plain function (a ``staticmethod``, a property) cannot be guarded
    and is refused at class-creation time rather than left as a hole.
    """
    current = inspect.getattr_static(cls, "to_tptp", None)
    if current is None or isinstance(current, GuardedToTptp):
        return
    if not isinstance(current, types.FunctionType):
        raise TypeError(
            f"{cls.__qualname__}.to_tptp is a {type(current).__name__}, not a plain "
            "method: the single-formula collision guard (fol/_tptp_symbols.py) "
            "can only wrap a plain method. Define to_tptp(self) as a regular "
            "method.")
    setattr(cls, "to_tptp", GuardedToTptp(current))
