"""Shared TPTP ``fof`` problem generation for the external TPTP-speaking backends.

:mod:`atp.vampire_entailment`, :mod:`atp.eprover_backend` (E and
Zipperposition), and :mod:`atp.twee_entailment` each build the IDENTICAL TPTP
problem shape from ``(premises, conclusion)``: one ``fof(premise_<i>, axiom,
...).`` line per premise (1-based) plus one ``fof(goal, conjecture, ...).``
line — three copies of the same seven lines that had already started to
drift apart in their docstrings. :func:`generate_tptp_problem` is the single
place that shape is written; the three backends' own ``_generate_*_input``
functions now delegate here (same name, same signature, same output — no
behaviour change for their callers or their tests).

**ASCII/legality sanitisation (problem-level seam).** ``Node.to_tptp()``
renders a predicate/function/constant name close to verbatim — only a
Constant is transliterated to ASCII (:func:`constant_name_to_ascii`), and
only the first character of any of the three is folded for TPTP's
lowercase-initial rule (:func:`tptp_fold_first_letter`). Neither step fixes
a DIGIT-LEADING name (``2008SummerOlympics`` stays digit-leading, which
TPTP's ``lower_word: [a-z][A-Za-z0-9_]*`` grammar forbids), nor an ASCII
character that is no word character at all (``has-part``, ``a.b``,
``owl:Thing``, ``$f``: Vampire reads ``has-part(X)`` as a parse error and E
stops at the ``-``), nor a leading underscore, and neither
``Atom.to_tptp`` nor ``Function.to_tptp`` transliterates non-ASCII at all —
gaps the toolkit's identifier grammar could not reach before it was widened
to accept Unicode letters and digit-leading names, but can now. Fixing
either INSIDE a node's own ``to_tptp()`` would be wrong: each node would
rename independently, two distinct kit-level names could collide on their
fix with no whole-problem view to catch it, and the rewrite could never
reach a caller that needs to translate a prover's answer back. So the fix
lives here instead, exactly where the pre-existing case-fold collision
guard below already lives: :func:`_sanitize_for_tptp` walks every premise
and the conclusion TOGETHER, replaces only the names that are not already
TPTP-legal (checked BEFORE any fold — see :func:`_is_tptp_safe`) with an
ASCII, letter-initial, whole-problem-injective replacement of ``[A-Za-z0-9_]``
only (every other character becomes the code-point escape ``uXXXX`` the
transliteration already uses: ``has-part`` is ``hasu002dpart``, see
:func:`~unicode_fol_kit.atp.tptp_tff._tptp_word_base`), and returns
a :class:`TptpNameMap` recording exactly what was renamed so a caller can
translate prover output back (:func:`apply_reverse_tptp`). A name that was
already TPTP-legal is returned completely untouched — the very same
``Node`` object, not a copy — so ``Node.to_tptp()``'s existing output for
every formula this module was already handling correctly is byte-identical
to before this sanitisation step existed.

**Soundness guard.** :meth:`~unicode_fol_kit.fol.nodes.Node.to_tptp` folds a
predicate/function/constant name for TPTP's lowercase-initial identifier rule
by lower-casing only its FIRST character (see
:func:`unicode_fol_kit.fol._fol_nodes.tptp_fold_first_letter`) — the exact
mirror of ``tptp_input.py``'s ``_cap()``, which capitalises only the first
character of a parsed predicate name on import. That fold is not injective by
itself: ``Foo`` and ``foo`` (or two constants, or two functions) still both
fold to ``foo``. The outermost ``to_tptp()`` call checks the ONE formula it
renders (it runs the very same check, :func:`unicode_fol_kit.fol._tptp_symbols
.check_symbols`), but it has no way to know whether some OTHER formula elsewhere
in the same problem folds to the same identifier, so the whole-problem check has
to happen here, where every premise and the conclusion are in view together. Two distinct kit-level names colliding on export would otherwise be
silently merged into ONE TPTP symbol — e.g. a premise ``Foo(a)`` and its
negation ``¬FOO(a)`` would both render as ``foo(a)``, making the exported
axiom set ``{foo(a), ~foo(a)}`` — internally CONTRADICTORY, so an external
prover proves any conjecture from it via ex falso quodlibet, a false
"Theorem" verdict for a query the premises never actually entail. Rather than
risk that, :func:`generate_tptp_problem` refuses with ``NotImplementedError``
naming both colliding kit-level names, mirroring
:func:`unicode_fol_kit.atp.tptp_ncl.to_tptp_ncl`'s own (separately
implemented, since NXF's modal connectives are outside ``to_tptp``'s
classical FOL fragment) collision guard for the NXF export path. This check
runs AFTER the ASCII sanitisation step above, over the sanitised formulas —
:func:`_sanitize_for_tptp` already avoids colliding with itself (a shared
reservation set covers both already-legal and newly-synthesised names in
each namespace), so in practice this guard only ever fires for the same
kind of pre-existing, already-legal-name case-fold collision it always did
(``Foo``/``foo``); it is not weakened or bypassed by the sanitisation step.

This check compares predicate names with predicate names and function/constant
names with function/constant names; it does not look across the two. Only two
DISTINCT names within the SAME kind colliding is refused here. Equality and
disequality (``=``, ``≠``) map to a fixed TPTP token (``=``, ``!=``), never through
the first-letter fold, so they cannot fold together with a NAME; they are no
identifier to begin with, so :func:`_sanitize_for_tptp` never offers them to the "is
this already legal?" test. The arithmetic comparisons and functions are a different
matter, see the next section. Variables are checked per formula (``x`` and ``X`` are
one TPTP variable, and the refusal says so).

**A numeral is a constant, and ``+ - * /  < > ≤ ≥`` are ordinary symbols.** The kit
reads a :class:`~unicode_fol_kit.fol.nodes.Number` on every route that was not asked
for arithmetic as a constant identified by its VALUE (``1``, ``1.0`` and ``01`` are
one constant) about which nothing else is known, the four operators as uninterpreted
function symbols and the four comparisons as uninterpreted predicates. TPTP says
otherwise for the text the single renderers write (``Number.to_tptp``: ``1`` is an
``$int``; ``$sum``, ``$less``, ... are arithmetic): measured on Vampire 5.0.1 and E
3.5.1, the text ``p(1)`` is a type error for a predicate over individuals, and
``1 != 2``, ``$less(1,2)`` and ``$sum(1,1) = 2`` are THEOREMS of the prover's
arithmetic that this reading does not have. So the problem writers
(:func:`generate_tptp_problem`, :func:`generate_tptp_problem_with_mapping`,
:func:`generate_tptp_problem_for_prover` and, for the typed route,
:func:`~unicode_fol_kit.atp.tptp_tff.generate_tff_problem`) write neither: a numeral
is written as the constant named by the numeral's value (``1`` and ``1.0`` are ``1``,
``2.5`` is ``2.5``; ``unicode_fol_kit.fol._numeral_symbols.numeral_name``), an
operator as an ordinary function or predicate of its own name, and the ordinary renamer
(:func:`_sanitize_for_tptp`) gives each of them a word of a prover's grammar (``1`` is
``n1``, ``+`` is ``u002b``, ``<`` is ``u003c``): collision-free against every other symbol
of the problem (one word per value, never the word of a user's symbol, a sort or a
predicate), recorded in the returned :class:`TptpNameMap` (``term`` and ``predicate`` for
the operators, ``term`` and ``numerals`` for the numerals), and read back through it
(:func:`apply_reverse_tptp` hands a proof's ``n1`` back as ``Number(1)`` and ``u002b`` as
``+``). A numeral is never a double-quoted distinct object either: TPTP makes those
pairwise distinct, and two numerals of different value may denote one element. A
``Constant`` (or ``SortedConstant`` or ``Function``) spelled like a numeral of the same
problem, ``Number(1)`` next to ``Constant('1')``, would be the same name and is refused by
name. The arithmetic reading is asked for by name and written elsewhere: the TFA writer
(:mod:`~unicode_fol_kit.atp._tff_problem`, the ``sort=`` option of the backends) keeps
``$sum``, ``$less`` and the number literals, typed ``$int`` or ``$real``.

**A predicate and a function/constant that fold to the SAME identifier.** An
earlier version of this module argued that a predicate ``Agent`` and a role
function ``agent`` (both ``agent``) are harmless because a TPTP reader
resolves a bare identifier by its syntactic position. That is false for the
provers this module feeds: Vampire 5.0.1 answers ``Non-boolean term
agent(X0) of sort $i is used in a formula context`` and E 3.5.1 stops with a
parse error on ``agent(agent(X))``, so the problem is rejected before any SZS
status exists (and "no answer" read as a verdict looks like "undecided"). A
reader MAY resolve by position — this kit's own reader
(:mod:`~unicode_fol_kit.fol.tptp_input`) does — but a prover is not obliged
to, so the problem text must not depend on it. The writer therefore renames
the TERM-side symbol, the function or constant, whenever its rendered name
equals a predicate's, whatever the arities (:func:`_separate_term_names`): the
predicate keeps its natural name, the term becomes ``<name>_term`` (a numeric
suffix is added if that is taken), and the pair is recorded in
:class:`TptpNameMap`, so :func:`apply_reverse_tptp` and
:meth:`TptpNameMap.reverse_rendered` restore the original. The rename is exact
— a symbol is only a name — and a problem without such a clash is rendered
byte-for-byte as before. The same-kind guard above has already run on the
ASCII-sanitised formulas by then, so a refusal for two LEGAL names of one kind
(``car``/``Car``) can never be dodged by this rename. The guard predicates a
many-sorted node lowers to (``S(x)`` for a sort ``S``) count as predicate
names for BOTH checks: the sort guard ``Foo`` of ``∀x:Foo P(x)`` in one premise
and a predicate ``foo`` of another are one TPTP word, which no walk of the
source trees would see, so the whole-problem check is fed the non-emptiness
axioms too (their atoms ARE the guard predicates, one per sort), exactly as the
single-formula guard sees them by recording what it renders. A
:class:`~unicode_fol_kit.fol.nodes.Measure` writes the function ``measure`` (it
is that symbol: ``to_z3`` declares ``measure/2`` for it), so it is renamed like
``Function('measure', ...)`` when a predicate is written ``measure`` too, and
:func:`apply_reverse_tptp` hands it back as that function.

Seven node classes write a predicate, function or constant name: ``Atom``,
``Function``, ``Constant`` and ``SortedConstant`` (the four the sanitiser walks),
``Measure`` (the function ``measure``), and ``SortedQuantifier`` / ``SortedCount``
(the guard predicate of their sort); ``Number`` writes a numeral and ``Variable``
a variable, and no other class writes a symbol. Every name writer is seen by the
same-kind check and by the cross-kind separation; ``tests/test_tptp_writer_names.py``
derives the list from the node classes themselves, so a class added later cannot
be missed.

**One predicate at two arities.** ``Zed(a)`` and ``Zed(a, b)`` are written as
``zed(a)`` and ``zed(a,b)``, which a prover reads as two symbols (``zed/1`` and
``zed/2``). So does the kit's z3 route across formulas (each formula is
translated in its own environment and z3 overloads a name by its arity), so the
two agree and the writer says nothing; the TF0 and TFA writers, which declare one
type per name, refuse it by name. (Inside ONE formula ``to_z3`` raises on such a
pair, where the writers write two symbols.)

**No conclusion.** ``conclusion=None`` writes no ``conjecture`` line, for a prover
that is asked whether the premises are satisfiable (Vampire: ``SZS status
Satisfiable`` or ``Unsatisfiable``). Every check, the cross-kind separation, the
non-emptiness axioms and the returned map work on the premises alone, in the
``fof``, TF0 and TFA writers alike.

That asymmetry — a name that is not TPTP-legal, or that clashes across kinds,
is renamed and recorded, while two legal names of one kind that fold together
are refused by name — is deliberate for this release. The same-kind refusal
predates the name map and is kept so that no existing caller silently receives
a renamed symbol; it is not a claim that the two cases differ in principle.

**A variable that has no TPTP spelling.** A variable is written as the upper-case
of its name, and a TPTP variable is an upper-case letter followed by letters, digits
and underscores, so ``ä`` (written ``Ä``), ``x-1`` and ``1x`` cannot be written as
they are, and every prover rejects the text. A variable is BOUND, so the writer
renames it without recording anything
(:func:`unicode_fol_kit.fol._tptp_symbols.legalise_variables`): per formula,
injectively (``ä`` and ``Ä`` stay two variables) and capture-free (the new name,
``x0``, ``x1``, ... minted through :mod:`unicode_fol_kit.fol._identifiers`, equals no
variable of the formula as written). A formula whose variables are all legal is
passed on as the very same object. The single ``Node.to_tptp`` has no map and
refuses such a variable by name.

**``$true`` and ``$false``.** TPTP defines these two propositions and this kit's
reader produces them as the nullary atoms ``Atom('$true')`` / ``Atom('$false')``, so
a problem read with :func:`~unicode_fol_kit.fol.tptp_input.parse_tptp` and written
back must keep them: they are written verbatim, never renamed, never declared (TF0,
TFA) and never counted by the collision checks, and ``to_z3`` reads them as true and
false so that z3 and the provers agree. Any other ``$``-word as a predicate,
function or constant name, and ``$true`` itself with arguments, is an ordinary user
name that is not a TPTP word, and the writers rewrite it like ``has-part``
(``$foo`` is ``u0024foo``).

**Many-sorted (MSFOL) soundness.** The kit has ONE universe; a sort ``S`` is the
extension of the unary predicate ``S`` (the sort and the predicate of that name
are one symbol) and is never empty; sorts may overlap; a sorted constant ``c:S``
is in ``S`` (and in every other sort it is written with); an unannotated constant,
an unsorted variable and the value of a function may be any element. A sorted
quantifier/constant/count lowers (via ``Node.to_tptp()``'s auto-reduction,
``fol.nodes.to_fol``) to a plain unary predicate guard, which by itself says
neither that the guarded sort is non-empty nor that a sorted constant is in its
sort. This ``fof`` builder is the route that asks that question for every sorted
problem: the backends' automatic mode (``tff=None``) tries the native typed route
(:func:`~unicode_fol_kit.atp.tptp_tff.generate_tff_problem`) first and falls back
to THIS writer when the typed text would ask another question, or the typed writer
does not cover a node of the problem that this one does (see that module's
docstring, and :func:`generate_tptp_problem_for_prover`), and a caller forcing
``tff=False``, or :mod:`atp.twee_entailment` (which has no typed route), reaches it
directly. So :func:`generate_tptp_problem_with_mapping` adds two kinds of background axiom
lines, both with the ``axiom`` role — an assumption the conjecture's refutation
search may use freely, exactly what an entailment's premise side means — never the
``conjecture`` role, and never folded into ``Node.to_tptp()`` itself, which stays
polarity-blind:

* one ``fof(nonempty_sort_<i>, axiom, ...).`` line per distinct sort name in
  ``premises``/``conclusion``
  (``unicode_fol_kit.fol._msfl_nodes.nonempty_sort_axioms``). Each axiom is rendered
  straight from ``Node.to_tptp()`` on the RAW kit-level sort name, bypassing
  :func:`_sanitize_for_tptp`'s renaming map entirely: a sorted node's own lazy
  ``to_fol`` reduction elsewhere in the SAME problem is equally unsanitised (see
  this module's own ASCII-legality section — sort names are a narrower, pre-existing
  gap this fix does not touch), so keeping the axiom unsanitised too is what keeps
  both talking about the identical predicate. A sort name that is not a TPTP word is
  therefore refused by name (the guard's legality check sees the predicate it is
  written as, and says it is the guard of the sort S), not rewritten: the TF0
  writer, which keeps sorts in a namespace of their own, rewrites such a sort. The
  guard names are RESERVED in the sanitiser (:func:`_sanitize_for_tptp`), so a
  predicate that has to be rewritten never lands on one: a sort ``Hasu002dpart``
  next to a predicate ``has-part`` (written ``hasu002dpart`` before the guard was
  reserved, which merged the two into one symbol) now gets ``Hasu002dpart2`` for
  the predicate.
* one ``fof(sort_member_<i>, axiom, S(c)).`` line per distinct sorted constant
  ``c:S`` (``unicode_fol_kit.fol._msfl_nodes.sort_membership_axioms``; a constant
  written with two sorts has two lines; in the order the pairs first occur). Unlike
  a sort name a CONSTANT is renamed on its way into the problem (``human:Human`` is
  written ``human_term`` because the sort guard is the word ``human``, ``9lives`` is
  ``n9lives``, ``sókrates`` is ``su00f3krates``), so these atoms are built from the
  formulas AS SANITISED AND SEPARATED, whose constants are the tokens the premises
  use; an atom built from the raw names would say ``human(human)`` about another
  symbol and silently do nothing. The sort is the raw sort name, as in the
  non-emptiness lines, and every constant is one of the formulas' own, so the
  returned name map covers what the lines write.

Both are empty for a problem without a sorted node (and the second for one without
a sorted constant), so the generated text is byte-identical to before for those.
"""

import re
from dataclasses import dataclass, field
from typing import Callable, Dict, FrozenSet, List, Optional, Sequence, Tuple, Union

from ..fol._fol_nodes import constant_name_to_ascii, tptp_fold_first_letter
from ..fol._msfl_nodes import nonempty_sort_axioms, sort_membership_axioms
from ..fol._numeral_symbols import numeral_value, numerals_as_constants
from ..fol._tptp_symbols import (
    check_no_symbol_collisions, is_tptp_boolean_atom, legalise_variables,
)
from ..fol.nodes import (
    Atom, Constant, Function, Measure, Node, Number, SortedConstant, Variable, free_variables,
)
from ._ascii_names import ascii_safe_base, reserve_rendered
from ._writer_support import (
    check_against_generated, normalise_premise_names, tptp_name_token,
)
# generate_tff_problem lives in tptp_tff.py (the native TF0/typed-TPTP
# writer, a sibling module rather than an addition to this fof-only one —
# see that module's docstring); re-exported here purely so a caller already
# depending on "the shared TPTP problem generator module" for the fof route
# finds the typed sibling at the same place, per the natural pairing with
# generate_tptp_problem above.
from .tptp_tff import (
    Tf0Refusal, generate_tff_problem, generate_tff_problem_with_mapping,
    problem_needs_tff, _separated_term_token, _tptp_word_base,
)

__all__ = ["generate_tptp_problem", "generate_tptp_problem_with_mapping",
           "generate_tptp_problem_for_prover", "TptpProblem",
           "TptpNameMap", "apply_reverse_tptp", "generate_tff_problem",
           "generate_tff_problem_with_mapping"]


# ---------------------------------------------------------------------------
# ASCII/legality sanitisation — see the module docstring's second section.
# ---------------------------------------------------------------------------

# A raw kit-level name that is ALREADY safe to hand to Node.to_tptp(): pure
# ASCII, letter-initial (so the fold turns it into a legal lower_word no
# matter its case), and containing only the characters lower_word allows
# after that. Names the widened parser can now produce never contain
# anything outside this (unicode letters/digits/underscore/combining marks
# only), so this is the exact complement of "needs a replacement".
_TPTP_SAFE_RE = re.compile(r"[A-Za-z][A-Za-z0-9_]*")


def _is_tptp_safe(name: str) -> bool:
    return bool(name) and name.isascii() and bool(_TPTP_SAFE_RE.fullmatch(name))


@dataclass
class _Renamer:
    """One symbol namespace's original->safe-token map, whole-problem-shared.

    Two passes, run over the WHOLE problem before any text is rendered:

    1. :meth:`collect` — called once per occurrence of every name in this
       namespace, in problem order. An already-legal name is reserved
       immediately and unconditionally (R1: it is never touched, so its
       reservation cannot depend on what else is in the problem); anything
       else is queued, deduplicated by first occurrence.
    2. :meth:`finalize` — synthesises a token for every queued name, each
       de-collided (:func:`reserve_rendered`) against ``used`` as it now
       stands: every already-legal name in the WHOLE problem, not just the
       ones that happened to appear earlier in iteration order.

    Doing this in one combined pass (synthesise-as-you-go) would make
    collision-avoidance depend on argument order: a synthesised name could
    legitimately claim a token that a DIFFERENT, already-legal name
    appearing LATER in the same problem also owns — since R1 forbids moving
    the legal name off of it, that is a genuine, unavoidable ambiguity, but
    one this two-pass split avoids ever manufacturing purely from processing
    order (R2: "two different names never collide" holds regardless of
    where in the problem each one appears). :meth:`get` is only valid after
    :meth:`finalize` — every name this namespace will ever be asked about
    must have gone through :meth:`collect` first.
    """

    prefix: str
    render: Callable[[str], str]
    case_fix: Callable[[str], str]
    mapping: Dict[str, str] = field(default_factory=dict)
    used: set = field(default_factory=set)
    _pending: List[str] = field(default_factory=list)

    def collect(self, name: str) -> None:
        if name in self.mapping or name in self._pending:
            return
        if _is_tptp_safe(name):
            self.used.add(self.render(name))
            self.mapping[name] = name
        else:
            self._pending.append(name)

    def finalize(self) -> None:
        for name in self._pending:
            base = self.case_fix(_tptp_word_base(name, self.prefix))
            token = reserve_rendered(base, self.used, self.render)
            self.mapping[name] = token
        self._pending = []

    def get(self, name: str) -> str:
        return self.mapping[name]


def _predicate_base_case(base: str) -> str:
    """Force uppercase-initial — the kit's own PREDICATE convention.

    Necessary for round-tripping, not merely stylistic: TPTP's own fold
    always lower-cases whatever we export, and ``tptp_input.py``'s ``_cap()``
    always UPPER-cases the first letter of whatever text a prover echoes
    back — regardless of what we originally exported. A synthesised
    predicate token therefore has to already BE upper-case-initial, or the
    reverse mapping (keyed by the token we chose) would never match what
    comes back from ``_cap()``. Function/constant names need no such fix:
    neither export nor import case-folds them at all (see
    :func:`_term_base_case`), so any ASCII letter-initial form round-trips
    verbatim.
    """
    return base[0].upper() + base[1:] if base else base


def _term_base_case(base: str) -> str:
    """Force lowercase-initial — the kit's own NAME (function/constant)
    convention, and, since neither export nor import case-folds a
    function/constant name at all, the form that makes ``render(candidate)
    == candidate`` (no fold vs. no-fold asymmetry to reverse)."""
    return base[0].lower() + base[1:] if base else base


@dataclass
class TptpNameMap:
    """The renamings :func:`_sanitize_for_tptp` chose for one problem.

    ``predicate`` and ``term`` are original-kit-name -> raw-token dicts (the
    exact string substituted into the sanitised AST, BEFORE ``Node.to_tptp``'s
    own fold) for the predicate namespace and the shared function/constant
    namespace respectively — mirroring the two-namespace split
    :func:`_check_no_symbol_collisions` already uses. An original name that
    was already TPTP-legal maps to itself (see :class:`_Renamer`), so
    :meth:`reverse` inverts cleanly even for untouched names.

    A function/constant whose rendered name equals a predicate's (the class
    ``Agent`` and the role function ``agent``) is recorded here too, under
    ``term``, mapped to its ``<name>_term`` replacement
    (:func:`_separate_term_names`); no token of ``term`` renders like any token
    of ``predicate``, so :meth:`reverse_rendered` never has to choose between
    the two kinds for one piece of prover text.

    A writer also records what it called its lines, which a symbol rename does not
    cover: ``premises`` holds the premise names in order (the names the caller gave with
    ``premise_names=``, or ``premise_1``, ``premise_2``, ... by default; empty for a map
    that no writer made) and ``background`` the axiom lines the writer added on its own
    as ``(name, meaning)`` pairs (the non-emptiness line of a sort and the membership
    line of a sorted constant). A reader of a prover's proof goes through them
    (:func:`~unicode_fol_kit.atp.tstp.relevant_premises_from_tstp`). They are not renames,
    so they take no part in ``==``: two maps are equal when they rename alike.

    A numeral is written as a constant (see the module docstring), so it is a ``term`` entry:
    its key is the name :func:`~unicode_fol_kit.fol._numeral_symbols.numeral_name` gives its
    value (``'1'``, ``'2.5'``) and its value the word it was written as. ``numerals`` holds
    those keys, which is what tells :func:`apply_reverse_tptp` that the word stands for a
    :class:`~unicode_fol_kit.fol.nodes.Number` and not for a constant spelled alike (a problem
    never has both: that is refused). The arithmetic operators are ``term`` entries (``'+'``)
    and ``predicate`` entries (``'<'``) like any other name when the writer wrote them as
    ordinary symbols.
    """

    predicate: Dict[str, str] = field(default_factory=dict)
    term: Dict[str, str] = field(default_factory=dict)
    premises: Tuple[str, ...] = field(default=(), compare=False)
    background: Tuple[Tuple[str, str], ...] = field(default=(), compare=False)
    numerals: FrozenSet[str] = field(default=frozenset())

    def reverse_numerals(self) -> Dict[str, Union[int, float]]:
        """Return ``{word: value}`` for every numeral the writer wrote: the word a prover's
        text has (the token the writer chose for it) and the value of the
        :class:`~unicode_fol_kit.fol.nodes.Number` it stands for."""
        return {token: numeral_value(name) for name, token in self.term.items()
                if name in self.numerals}

    def reverse(self) -> Tuple[Dict[str, str], Dict[str, str]]:
        """Return ``(predicate_reverse, term_reverse)``: token -> original.

        The token used as the reverse-dict KEY is exactly what a prover's
        own output re-parsed via :func:`~unicode_fol_kit.fol.tptp_input
        .parse_tptp_formula` produces for that symbol — see
        :func:`_predicate_base_case`/:func:`_term_base_case`'s docstrings for
        why that already equals the raw token stored in ``predicate``/
        ``term`` (no extra fold/cap step needed here). Use this for the
        STRUCTURED Rückweg (:func:`apply_reverse_tptp`, and anything that
        goes through it such as :func:`~unicode_fol_kit.atp.tstp
        .reverse_map_derivation`) — never for raw, un-parsed prover text; see
        :meth:`reverse_rendered` for that.
        """
        return ({v: k for k, v in self.predicate.items()},
                {v: k for k, v in self.term.items()})

    def reverse_rendered(self) -> Tuple[Dict[str, str], Dict[str, str]]:
        """Return ``(predicate_reverse, term_reverse)`` keyed by the
        RENDERED token — exactly the text ``Node.to_tptp()`` actually wrote
        into the generated problem, and therefore exactly what a prover
        echoes back UNPARSED (raw stdout, an SZS detail string, and similar
        free text — R3's "Erklärungstexte").

        :meth:`reverse` is keyed by the raw, pre-fold token instead, which is
        the right key for the STRUCTURED Rückweg (:func:`apply_reverse_tptp`
        re-parses a prover's TSTP text via
        :func:`~unicode_fol_kit.fol.tptp_input.parse_tptp_formula` first,
        which re-applies the kit's uppercase-initial predicate convention on
        import — see :func:`_predicate_base_case` — undoing the export-time
        fold before this mapping is ever consulted) but the WRONG key for
        free text that was never re-parsed: a synthesised or already-legal
        predicate token such as ``Human`` renders as ``human`` (only the
        first character is folded, :func:`tptp_fold_first_letter`), so raw
        prover stdout contains ``human``, not ``Human`` — a reverse dict
        keyed by ``Human`` never matches it, and the original name is never
        restored (this is exactly the bug this method fixes). Term
        (function/constant) tokens are unaffected in practice — they are
        already chosen/kept lowercase-initial (:func:`_term_base_case`), so
        rendering them again is a no-op — but this method renders them the
        same way regardless, so it stays correct even for a term name built
        directly (e.g. a bare ``Constant("Foo")``) outside the parser's own
        lowercase-initial NAME convention rather than assuming every caller
        went through it.

        Injective by construction: :class:`_Renamer` already de-collides
        every name in a namespace on its RENDERED form (:func:`reserve_rendered`,
        and the immediate ``self.used.add(self.render(name))`` for an
        already-legal name in :meth:`_Renamer.collect`) before assigning it a
        token, so two distinct original names can never render to the same
        text within one namespace — this dict can never silently drop or
        merge an entry.
        """
        pred_rendered = {tptp_fold_first_letter(v): k for k, v in self.predicate.items()}
        term_rendered = {tptp_fold_first_letter(constant_name_to_ascii(v)): k
                         for k, v in self.term.items()}
        return pred_rendered, term_rendered


def _is_fixed_atom(atom: Atom, uninterpreted_arithmetic: bool) -> bool:
    """Whether ``atom`` is written with a token of the TPTP language itself and so is never
    renamed: equality and disequality, ``$true`` / ``$false`` and, unless the problem reads
    the comparisons as ordinary predicates, ``<``, ``>``, ``≤`` and ``≥``."""
    return (atom.predicate in Atom.INFIX_PREDS_TPTP or is_tptp_boolean_atom(atom)
            or (not uninterpreted_arithmetic and atom.predicate in Atom.PREFIX_PREDS_TPTP))


def _is_fixed_function(function: Function, uninterpreted_arithmetic: bool) -> bool:
    """Whether ``function`` is written with a dollar-word of TPTP (``$sum``, ...) and so is
    never renamed: an arithmetic operator, unless the problem reads it as an ordinary
    function."""
    return not uninterpreted_arithmetic and function.name in Function.TPTP_ARITH_OPS


def _sanitize_node_for_tptp(node: Node, predicates: _Renamer, terms: _Renamer,
                            uninterpreted_arithmetic: bool = False) -> Node:
    """Rebuild ``node`` with every non-TPTP-legal symbol name replaced.

    Structural recursion via ``Node.map_children`` (see
    :mod:`fol.sanitize`'s ``_rewrite`` for the same pattern); an
    already-legal name comes back as the exact same string, so a node whose
    own name and every descendant's name were already legal is rebuilt with
    identical field values throughout — ``Node.to_tptp()`` on the result is
    therefore byte-identical to ``Node.to_tptp()`` on the original (R1).

    ``uninterpreted_arithmetic`` makes ``+ - * /`` and ``< > ≤ ≥`` names like any other
    (renamed to a word of a prover's grammar); without it they are left alone, to be written
    as TPTP's own ``$sum``, ``$less``, ... (the arithmetic reading).
    """
    if isinstance(node, Atom):
        if _is_fixed_atom(node, uninterpreted_arithmetic):
            pred = node.predicate
        else:
            pred = predicates.get(node.predicate)
        return Atom(pred, tuple(_sanitize_node_for_tptp(a, predicates, terms, uninterpreted_arithmetic)
                                for a in node.args))
    if isinstance(node, Function):
        if _is_fixed_function(node, uninterpreted_arithmetic):
            name = node.name
        else:
            name = terms.get(node.name)
        return Function(name, tuple(_sanitize_node_for_tptp(a, predicates, terms, uninterpreted_arithmetic)
                                    for a in node.args))
    if isinstance(node, Constant):
        return Constant(terms.get(node.name))
    if isinstance(node, SortedConstant):
        # Renders (via to_fol) as the plain Constant of the same name, so it
        # is the same symbol and must get the same token as that Constant.
        return SortedConstant(terms.get(node.name), node.sort)
    return node.map_children(
        lambda c: _sanitize_node_for_tptp(c, predicates, terms, uninterpreted_arithmetic))


def _collect_names_for_tptp(node: Node, predicates: _Renamer, terms: _Renamer,
                            uninterpreted_arithmetic: bool = False) -> None:
    """First pass (see :class:`_Renamer`): register every predicate/
    function/constant name ``node`` (and its descendants) uses, without
    rewriting anything yet."""
    for n in node.walk():
        if isinstance(n, Atom):
            if not _is_fixed_atom(n, uninterpreted_arithmetic):
                predicates.collect(n.predicate)
        elif isinstance(n, Function):
            if not _is_fixed_function(n, uninterpreted_arithmetic):
                terms.collect(n.name)
        elif isinstance(n, (Constant, SortedConstant)):
            terms.collect(n.name)


def _sanitize_for_tptp(formulas: List[Node],
                       sort_guards: Tuple[str, ...] = (),
                       *, uninterpreted_arithmetic: bool = False,
                       numerals: FrozenSet[str] = frozenset()) -> Tuple[List[Node], TptpNameMap]:
    """Sanitise every formula's predicate/function/constant names for TPTP.

    Returns ``(sanitised_formulas, mapping)`` — see the module docstring's
    ASCII-sanitisation section. Both namespaces (predicate; function+constant)
    are shared across ALL of ``formulas``, so the same original name maps to
    the same token everywhere (R2), and a synthesised token can never
    collide with any name anywhere in the problem, regardless of where each
    one appears (:class:`_Renamer`'s two-pass collect/finalize split).

    ``sort_guards`` are the kit names of the sorts of the problem, which the fof
    writer writes as predicates (the guard of a sort). They appear in no formula
    this function walks, yet their words are in the problem, so they are RESERVED
    in the predicate namespace: a token synthesised for a predicate that is not a
    TPTP word never equals one (``has-part`` next to the sort ``Hasu002dpart``
    becomes ``Hasu002dpart2``, not the sort's own word). Nothing is recorded in
    the map for a guard: it is not renamed.

    ``uninterpreted_arithmetic`` reads ``+ - * /`` and ``< > ≤ ≥`` as ordinary function and
    predicate names, renamed and recorded like any other; the default leaves them to be
    written as TPTP's own arithmetic words. ``numerals`` are the names of the constants that
    stand for numerals (:func:`~unicode_fol_kit.fol._numeral_symbols.numerals_as_constants`),
    which the returned map records as such.
    """
    predicates = _Renamer(prefix="p", render=tptp_fold_first_letter,
                         case_fix=_predicate_base_case)
    terms = _Renamer(prefix="n", case_fix=_term_base_case,
                     render=lambda n: tptp_fold_first_letter(constant_name_to_ascii(n)))
    for f in formulas:
        _collect_names_for_tptp(f, predicates, terms, uninterpreted_arithmetic)
    for guard in sort_guards:
        predicates.used.add(predicates.render(guard))
    predicates.finalize()
    terms.finalize()
    sanitised = [_sanitize_node_for_tptp(f, predicates, terms, uninterpreted_arithmetic)
                 for f in formulas]
    mapping = TptpNameMap(predicate=predicates.mapping, term=terms.mapping, numerals=numerals)
    return sanitised, mapping


def _rename_terms(node: Node, table: Dict[str, str]) -> Node:
    """Rebuild ``node`` with every function/constant name found in ``table``
    replaced by its value; predicates, variables and every other name stay.
    A node that carries no such name is rebuilt equal to the original.

    A :class:`~unicode_fol_kit.fol.nodes.Measure` writes the binary function
    ``measure`` (it is that very symbol: ``to_z3`` declares ``measure/2`` for it
    too), so it is renamed like ``Function('measure', ...)``, and when ``measure``
    is in ``table`` it is rebuilt as that function."""
    if isinstance(node, Atom):
        return Atom(node.predicate, tuple(_rename_terms(a, table) for a in node.args))
    if isinstance(node, Measure) and "measure" in table:
        return Function(table["measure"], (_rename_terms(node.entity, table),
                                           _rename_terms(node.dimension, table)))
    if isinstance(node, Function):
        name = node.name if node.name in Function.TPTP_ARITH_OPS else table.get(node.name, node.name)
        return Function(name, tuple(_rename_terms(a, table) for a in node.args))
    if isinstance(node, Constant):
        return Constant(table.get(node.name, node.name))
    if isinstance(node, SortedConstant):
        return SortedConstant(table.get(node.name, node.name), node.sort)
    return node.map_children(lambda c: _rename_terms(c, table))


def _separate_term_names(formulas: List[Node], mapping: TptpNameMap,
                         sort_names: Tuple[str, ...] = ()
                         ) -> Tuple[List[Node], TptpNameMap]:
    """Make the problem injective ACROSS kinds: no function/constant may render
    as the name of a predicate (see the module docstring's "A predicate and a
    function/constant that fold to the SAME identifier").

    ``formulas``/``mapping`` are :func:`_sanitize_for_tptp`'s output, already
    past :func:`_check_no_symbol_collisions`. Every function/constant token
    whose rendered name (the text ``Node.to_tptp`` writes) equals the rendered
    name of a predicate — or of a sort guard predicate named in
    ``sort_names`` — is replaced, in every formula, by a fresh token
    (:func:`~unicode_fol_kit.atp.tptp_tff._separated_term_token`:
    ``<name>_term`` plus a numeric suffix if taken) that equals no rendered
    predicate and no rendered term of the problem. The tokens are visited in
    sorted order, so the result depends only on WHICH symbols the problem
    contains, never on the order of its formulas or on any hash ordering.

    Returns ``(formulas, mapping)``; ``mapping.term`` maps each affected
    ORIGINAL kit name to its replacement, which is what lets
    :func:`apply_reverse_tptp` restore it. With nothing to separate the inputs
    are returned unchanged (the same objects), so the rendered text is
    byte-identical to what it was before this pass existed.
    """
    def render(token: str) -> str:
        return tptp_fold_first_letter(constant_name_to_ascii(token))

    predicate_names = {tptp_fold_first_letter(s) for s in sort_names}
    tokens = set()
    for formula in formulas:
        for node in formula.walk():
            if isinstance(node, Atom):
                if (node.predicate not in Atom.INFIX_PREDS_TPTP and node.predicate not in Atom.PREFIX_PREDS_TPTP
                        and not is_tptp_boolean_atom(node)):
                    predicate_names.add(tptp_fold_first_letter(node.predicate))
            elif isinstance(node, Function):
                if node.name not in Function.TPTP_ARITH_OPS:
                    tokens.add(node.name)
            elif isinstance(node, (Constant, SortedConstant)):
                tokens.add(node.name)
            elif isinstance(node, Measure):
                tokens.add("measure")      # the function a Measure node is written as
    clashing = sorted(t for t in tokens if render(t) in predicate_names)
    if not clashing:
        return formulas, mapping

    taken = predicate_names | {render(t) for t in tokens}
    replacement = {t: _separated_term_token(t, taken, render) for t in clashing}
    original_of = {token: original for original, token in mapping.term.items()}
    term = dict(mapping.term)
    for token, new in replacement.items():
        term[original_of.get(token, token)] = new
    separated = [_rename_terms(f, replacement) for f in formulas]
    return separated, TptpNameMap(predicate=dict(mapping.predicate), term=term,
                                  numerals=mapping.numerals)


def apply_reverse_tptp(node: Node, mapping: TptpNameMap) -> Node:
    """Translate a ``Node`` parsed from a TPTP-family prover's OWN output
    (e.g. one TSTP proof step) back to original kit-level names.

    Walks ``node`` exactly the way :func:`_sanitize_node_for_tptp` walked the
    export direction, looking up each predicate/function/constant name in
    ``mapping.reverse()``'s tables. A name the prover introduced itself (a
    Skolem constant, a CNF-clausification symbol — ``sK1``, ``esk1_0``, and
    similar) was never one of ours to begin with, so it has no entry in
    either table and is left exactly as the prover printed it, not guessed
    at or dropped. The word a numeral was written as comes back as the
    :class:`~unicode_fol_kit.fol.nodes.Number` of its value (``n1`` is ``Number(1)``), and the
    word of an operator written as an ordinary symbol as the operator (``u002b`` is ``+``).
    """
    pred_rev, term_rev = mapping.reverse()
    return _apply_reverse_tptp(node, pred_rev, term_rev, mapping.reverse_numerals())


def _apply_reverse_tptp(node: Node, pred_rev: Dict[str, str], term_rev: Dict[str, str],
                        numeral_rev: Optional[Dict[str, Union[int, float]]] = None) -> Node:
    numeral_rev = numeral_rev or {}
    if isinstance(node, Atom):
        if node.predicate in Atom.INFIX_PREDS_TPTP or node.predicate in Atom.PREFIX_PREDS_TPTP:
            pred = node.predicate
        else:
            pred = pred_rev.get(node.predicate, node.predicate)
        return Atom(pred, tuple(_apply_reverse_tptp(a, pred_rev, term_rev, numeral_rev)
                                for a in node.args))
    if isinstance(node, Function):
        # A parsed dollar-function statement (Vampire/E echoing $sum(...)
        # etc. back) already comes out of parse_tptp_formula with the
        # KIT-level operator name (tptp_input.py's dollar_func_app maps
        # "$sum" -> "+" before this function ever sees it) — the same
        # names Function.TPTP_ARITH_OPS is keyed by, not its dollar-word
        # values, so this mirrors the forward-direction check exactly.
        if node.name in Function.TPTP_ARITH_OPS:
            name = node.name
        else:
            name = term_rev.get(node.name, node.name)
        return Function(name, tuple(_apply_reverse_tptp(a, pred_rev, term_rev, numeral_rev)
                                    for a in node.args))
    if isinstance(node, Constant):
        if node.name in numeral_rev:
            return Number(numeral_rev[node.name])
        return Constant(term_rev.get(node.name, node.name))
    if isinstance(node, SortedConstant):
        return SortedConstant(term_rev.get(node.name, node.name), node.sort)
    return node.map_children(lambda c: _apply_reverse_tptp(c, pred_rev, term_rev, numeral_rev))


# ---------------------------------------------------------------------------
# Cross-formula case-fold collision guard (pre-existing; now runs on the
# ASCII-sanitised formulas — see the module docstring).
# ---------------------------------------------------------------------------

def _check_no_symbol_collisions(formulas: List[Node], *,
                                where: str = "generate_tptp_problem",
                                subject: str = "problem",
                                sorts: Tuple[str, ...] = ()) -> None:
    """Raise ``NotImplementedError`` if any two distinct predicate names, or
    any two distinct function/constant names, across ``formulas`` would fold
    to the same TPTP identifier under :meth:`Node.to_tptp` — see the module
    docstring. The check itself is
    :func:`unicode_fol_kit.fol._tptp_symbols.check_no_symbol_collisions`, the
    ONE implementation that the outermost ``Node.to_tptp()`` call also runs
    over the single formula it renders; here it runs over every premise and
    the conclusion TOGETHER, which no single formula's check can — plus, in
    :func:`generate_tptp_problem_with_mapping`, the non-emptiness axioms, whose
    atoms are the guard predicates the sorted nodes lower to.

    ``where`` and ``subject`` name the writer that is calling and what it was
    given, so a refusal says which entry point refused (the TFA writer and
    :func:`~unicode_fol_kit.atp.tstp.to_tstp` run this check too); ``sorts`` are
    the kit names of the sorts of the problem, so that the refusal of an illegal
    guard predicate says it is a sort.
    """
    check_no_symbol_collisions(formulas, where=where, subject=subject, sorts=sorts)


def generate_tptp_problem_with_mapping(premises: List[Node],
                                       conclusion: Optional[Node] = None,
                                       *, premise_names: Optional[Sequence[str]] = None
                                       ) -> Tuple[str, TptpNameMap]:
    """Like :func:`generate_tptp_problem`, but also returns the
    :class:`TptpNameMap` recording every rename it applied: the ASCII-legality
    ones and the function/constant renamed because its TPTP name equals a
    predicate's (see the module docstring), the premise names and the background
    axioms it added.

    ``conclusion=None`` writes a problem WITHOUT a conjecture, for a prover that
    is asked whether the premises are satisfiable (Vampire answers ``SZS status
    Satisfiable`` or ``Unsatisfiable``). Every check and rename below works on the
    premises alone, and the map is the map of the premises.

    ``premise_names`` names the premises' ``axiom`` lines: one string per premise,
    written as a TPTP name (a lower word or an integer as it is, anything else
    single-quoted with ``\\`` and ``'`` escaped), pairwise distinct as written and
    distinct from every name the writer gives its own lines (``goal``,
    ``nonempty_sort_<i>``, ``sort_member_<i>``). ``None`` keeps ``premise_<i>``. The
    names are recorded, in order and also when they are the default ones, in the
    returned map's ``premises``, and
    :func:`~unicode_fol_kit.atp.tstp.relevant_premises_from_tstp` reads a prover's
    proof back through them.

    A free variable in a premise or the conclusion is refused by name: a prover
    reads an unbound variable in a ``fof`` formula as a syntax error, and the answer
    must not depend on whether the problem has a sort.

    Raises:
        TypeError: ``premise_names`` is a single string, or holds a non-string.
        ValueError: ``premise_names`` has other than one name per premise, holds a
            name no TPTP name can spell (the empty name, a control character), two
            names that are the same as written, or a name the writer gives one of its
            own lines.
        NotImplementedError: as :func:`generate_tptp_problem`, and a free variable.

    This is the way to build a problem for a prover. Never assemble one by
    joining ``Node.to_tptp()`` strings: a single formula cannot know that two
    of its symbols fold to one TPTP word in ANOTHER formula, which is what the
    checks here are for.

    Callers that need to translate a prover's OWN output (a proof, a
    countermodel, an unsat core, ...) back to kit-level names — anything
    reading a TSTP derivation via :mod:`atp.tstp`, for instance — must use
    THIS function (not the plain :func:`generate_tptp_problem`) so they have
    the mapping :func:`apply_reverse_tptp` needs. A caller that only wants
    the problem text (nothing reads the answer's symbol names back) can keep
    using :func:`generate_tptp_problem`.
    """
    return _write_fof_problem(premises, conclusion, premise_names,
                              where="generate_tptp_problem_with_mapping")


def _refuse_free_variables(premises: List[Node], conclusion: Optional[Node],
                           *, where: str) -> None:
    """Refuse, by name, a premise or the conclusion with a free variable.

    A TPTP ``fof`` formula has no implicit closure for a prover to apply: Vampire stops
    with ``unquantified variable`` and E with ``Formula has free variables``, so the
    problem would come back as a prover's parse error, whether or not it uses a sort.
    The typed writers refuse a free variable too (:class:`~unicode_fol_kit.atp.tptp_tff
    .Tf0Refusal`, and ``ValueError`` in the TFA writer)."""
    for label, formula in ([(f"premise {i}", p) for i, p in enumerate(premises, start=1)]
                           + ([] if conclusion is None else [("the conclusion", conclusion)])):
        try:
            free = sorted({v.name for v in free_variables(formula) if isinstance(v, Variable)})
        except TypeError:
            continue                  # a node ``free_variables`` does not know: to_tptp refuses it
        if free:
            shown = ", ".join(repr(n) for n in free)
            raise NotImplementedError(
                f"{where}: free variable{'s' if len(free) > 1 else ''} {shown} in {label} — "
                "every variable of a TPTP formula must be bound, because a prover reads an "
                "unbound variable in a fof formula as a syntax error (Vampire: "
                "'unquantified variable', E: 'Formula has free variables') and this kit "
                "does not pick a closure for it. Bind the variable with a quantifier "
                "before writing the problem.")


def _nullary_functions_as_constants(formula: Node) -> Node:
    """``formula`` with every function of no arguments written as the constant of its name:
    TPTP has no empty argument list (``f()`` is no term, and Vampire stops with a parse
    error), and the kit defines a function of no arguments as the constant of its name
    (the TF0 and Prover9 writers write it that way too). A formula without one comes back
    as the very same object."""
    stack: List[Node] = [formula]
    while stack:
        node = stack.pop()
        if isinstance(node, Function) and not node.args:
            break
        stack.extend(node._child_nodes())
    else:
        return formula

    def rewrite(node: Node) -> Node:
        if isinstance(node, Function) and not node.args:
            return Constant(node.name)
        return node.map_children(rewrite)

    return rewrite(formula)


def _write_fof_problem(premises: Sequence[Node], conclusion: Optional[Node],
                       premise_names: Optional[Sequence[str]],
                       *, where: str) -> Tuple[str, TptpNameMap]:
    """The ``fof`` writer both :func:`generate_tptp_problem` and
    :func:`generate_tptp_problem_with_mapping` are; ``where`` is the name of the one
    that was called, which a refusal opens with."""
    premises = list(premises)
    names = normalise_premise_names(premise_names, len(premises), where=where)
    formulas = premises + ([] if conclusion is None else [conclusion])
    # A numeral is a constant (see the module docstring): written under the name of its
    # value, so that the renamer below gives it a word and the map reads it back.
    formulas, numerals = numerals_as_constants(formulas, where=where)
    formulas = [_nullary_functions_as_constants(f) for f in formulas]
    # Many-sorted non-emptiness axioms (see the module docstring) — computed
    # first because their sort guard predicates take part in the same-kind check
    # and in the cross-kind separation, exactly like a predicate written in the
    # source: ``∀x:Foo P(x)`` is written with the guard predicate ``Foo`` and the
    # axiom ``∃x Foo(x)``, which no walk of the SOURCE trees would otherwise see.
    # The sanitiser reserves them too, so that a predicate it has to rewrite never
    # lands on the word of a sort.
    sort_axioms = nonempty_sort_axioms(*formulas)
    sort_guards = tuple(a.predicate for ax in sort_axioms for a in ax.walk()
                        if isinstance(a, Atom))
    sanitised, mapping = _sanitize_for_tptp(formulas, sort_guards, uninterpreted_arithmetic=True,
                                            numerals=numerals)
    # A variable that has no TPTP spelling is renamed (per formula, no record).
    sanitised = [legalise_variables(f) for f in sanitised]
    _check_no_symbol_collisions(sanitised + list(sort_axioms), sorts=sort_guards, where=where)
    sanitised, mapping = _separate_term_names(sanitised, mapping, sort_guards)
    # A free variable is refused only after the symbol checks above, which a problem that
    # has both is refused for first (as it always was).
    _refuse_free_variables(premises, conclusion, where=where)
    sanitised_premises = sanitised if conclusion is None else sanitised[:-1]
    # The membership atoms come from the SANITISED formulas (see below); the same atoms
    # over the names as the caller wrote them say what each line means.
    membership = sort_membership_axioms(*sanitised)
    membership_meaning = [f"{a.args[0].name} is in the sort {a.predicate}"
                          for a in sort_membership_axioms(*formulas)]
    generated = ([] if conclusion is None else [("goal", "the conjecture")])
    generated += [(f"nonempty_sort_{i}", f"the non-emptiness axiom of the sort {sort!r}")
                  for i, sort in enumerate(sort_guards, start=1)]
    generated += [(f"sort_member_{i}", f"the membership axiom ({meaning})")
                  for i, meaning in enumerate(membership_meaning, start=1)]
    check_against_generated(names, generated, where=where)
    lines: List[str] = []
    for name, premise in zip(names, sanitised_premises):
        lines.append(f"fof({tptp_name_token(name)}, axiom, {premise.to_tptp()}).")
    # Many-sorted non-emptiness axioms — see the module docstring. Built
    # from the ORIGINAL (pre-sanitisation) premises/conclusion so each one
    # renders the exact raw sort-predicate name a sorted node's own lazy
    # to_tptp()/to_fol reduction emits elsewhere in this same problem.
    for i, axiom in enumerate(sort_axioms, start=1):
        lines.append(f"fof(nonempty_sort_{i}, axiom, {axiom.to_tptp()}).")
    # Sort membership of the sorted constants — the other half of the guard
    # reading (see the module docstring). Unlike the sort NAME, a constant is
    # renamed on its way into the problem (``human:Human`` is written
    # ``human_term``, ``9lives`` is ``n9lives``, ``sókrates`` is transliterated), so
    # the atoms are built from the formulas AS SANITISED AND SEPARATED, whose
    # constants are the very tokens the premises above use: an atom built from the
    # raw names would be about another symbol and silently do nothing. Every
    # constant of these atoms is one of the formulas' own, so the name map already
    # covers it.
    for i, atom in enumerate(membership, start=1):
        lines.append(f"fof(sort_member_{i}, axiom, {atom.to_tptp()}).")
    if conclusion is not None:
        lines.append(f"fof(goal, conjecture, {sanitised[-1].to_tptp()}).")
    mapping.premises = names
    mapping.background = tuple(
        [(f"nonempty_sort_{i}", f"the sort {sort} is not empty")
         for i, sort in enumerate(sort_guards, start=1)]
        + [(f"sort_member_{i}", meaning) for i, meaning in enumerate(membership_meaning, start=1)])
    return "\n".join(lines) + "\n", mapping


def generate_tptp_problem(premises: List[Node], conclusion: Optional[Node] = None,
                          *, premise_names: Optional[Sequence[str]] = None) -> str:
    """Build a TPTP ``fof`` problem string from premises and a conclusion.

    Each premise becomes ``fof(premise_<i>, axiom, <tptp>).`` (1-based) and
    the conclusion becomes ``fof(goal, conjecture, <tptp>).`` — or, with
    ``conclusion=None``, no conjecture line is written at all and the problem asks
    whether the premises are satisfiable. The bodies
    come from ``Node.to_tptp`` (variables upper-cased TPTP-style, predicate/
    function/constant names folded on their first character only — see the
    module docstring), after every name has been made TPTP-ASCII-legal (see
    the module docstring's sanitisation section) — a name that was already
    legal renders byte-identically to before that step existed. Shared
    verbatim by :mod:`atp.vampire_entailment`, :mod:`atp.eprover_backend`,
    and :mod:`atp.twee_entailment`.

    Before rendering, checks that the export stays injective across every
    premise and the conclusion TOGETHER — see the module docstring's
    soundness-guard section and :func:`_check_no_symbol_collisions` — and
    separates a function/constant from a predicate that would render as the
    same word (:func:`_separate_term_names`; the term becomes
    ``<name>_term``, which only :func:`generate_tptp_problem_with_mapping`
    reports back).

    A caller that also needs to translate a prover's response back to
    kit-level symbol names should call
    :func:`generate_tptp_problem_with_mapping` instead, which returns the
    same text plus the :class:`TptpNameMap` :func:`apply_reverse_tptp` needs.

    A numeral is written as a constant and ``+ - * /  < > ≤ ≥`` as ordinary symbols, each
    under a word of its own (see the module docstring): ``⊢ 1 ≠ 2`` is the problem
    ``n1 != n2``, which is not a theorem, and ``⊢ 1 + 1 = 2`` is ``u002b(n1,n1) = n2``.
    A function of no arguments is the constant of its name and is written as one
    (``p(fzero)``, never ``p(fzero())``: TPTP has no empty argument list).

    ``premise_names`` names the premises' lines instead of ``premise_<i>`` — see
    :func:`generate_tptp_problem_with_mapping`, which also records them. A free
    variable in a premise or the conclusion is refused.

    Raises:
        TypeError: ``premise_names`` is a single string, or holds a non-string.
        ValueError: ``premise_names`` has other than one name per premise, a name no
            TPTP name can spell, two names that are the same as written, or a name
            the writer gives one of its own lines (``goal``, ``nonempty_sort_<i>``,
            ``sort_member_<i>``).
        NotImplementedError: either (a) two distinct predicate names, or two
            distinct function/constant names, would render as the same TPTP
            identifier (the collision guard above; a sort counts as the
            predicate it is written as), or two LEGAL variables of one formula
            would render as one TPTP variable (``x`` and ``X``), or a sort name
            is not a TPTP word, or a constant, sorted constant or function is
            spelled like a numeral of the problem (``Number(1)`` next to
            ``Constant('1')``: one name would be two symbols), or (b) a premise or the
            conclusion contains a node outside the classical FOL fragment
            ``Node.to_tptp`` covers (modal / second-order / Łukasiewicz /
            lambda) — surfaced by ``to_tptp`` itself, unchanged from before
            this module existed.
    """
    text, _mapping = _write_fof_problem(premises, conclusion, premise_names,
                                        where="generate_tptp_problem")
    return text


@dataclass(frozen=True)
class TptpProblem:
    """A TPTP problem text with the record a backend needs to run and explain it.

    Fields:

    * ``text`` -- the problem, ``fof`` or ``tff``.
    * ``name_map`` -- the :class:`TptpNameMap` of the renames the writer applied.
    * ``dialect`` -- ``"fof"`` or ``"tff"``: which writer produced ``text``.
    * ``tff_refusal`` -- the typed writer's message when the automatic mode tried
      it, was refused, and wrote ``fof`` instead; ``None`` otherwise.
    """

    text: str
    name_map: TptpNameMap
    dialect: str
    tff_refusal: Optional[str] = None

    @property
    def fallback_note(self) -> Optional[str]:
        """The sentence a verdict's detail carries when the automatic mode fell back
        from the typed writer to ``fof`` (and why); ``None`` when it did not."""
        if self.tff_refusal is None:
            return None
        return ("the typed (TF0) writer refused this problem, so it was written as an "
                "untyped fof problem, which reads a sort as the unary predicate of its "
                "name and asserts that no sort is empty and that every sorted constant "
                f"is in its sort. The typed writer said: {self.tff_refusal}")


def generate_tptp_problem_for_prover(premises: List[Node],
                                     conclusion: Optional[Node] = None,
                                     *, tff: Optional[bool] = None,
                                     fof_writer: Optional[Callable[..., Tuple[str, TptpNameMap]]] = None,
                                     premise_names: Optional[Sequence[str]] = None
                                     ) -> TptpProblem:
    """The problem a TPTP prover is given for ``premises ⊨ conclusion``, in the
    dialect ``tff`` selects.

    * ``tff=False`` -- the ``fof`` writer
      (:func:`generate_tptp_problem_with_mapping`).
    * ``tff=True`` -- the typed TF0 writer
      (:func:`~unicode_fol_kit.atp.tptp_tff.generate_tff_problem_with_mapping`).
      What it refuses stays refused: :class:`~unicode_fol_kit.atp.tptp_tff.Tf0Refusal`
      (a ``ValueError`` and a ``NotImplementedError``) with its message, so a
      backend reports it as ``unknown`` / ``unsupported``.
    * ``tff=None`` -- the automatic mode: the typed writer when a sorted node
      occurs (:func:`~unicode_fol_kit.atp.tptp_tff.problem_needs_tff`), the ``fof``
      writer otherwise. EVERY refusal of the typed writer (a ``NotImplementedError``,
      which :class:`~unicode_fol_kit.atp.tptp_tff.Tf0Refusal` is a kind of) is
      answered with the ``fof`` problem: a problem whose typed text would not ask
      the kit's question (an unannotated constant or a function value that the type
      inference puts into a sort, an equation over an unsorted variable next to a
      sort, ...), and a node outside the typed writer's fragment that the ``fof``
      writer writes (a counting quantifier, ``Contrast``, ``Measure``). The result
      records that in ``tff_refusal``, and its ``fallback_note`` words it for a
      verdict's detail. A refusal of the ``fof`` writer itself
      (``NotImplementedError``) propagates, with the typed writer's refusal as its
      ``__cause__``.

    A node outside what BOTH writers cover raises ``NotImplementedError`` in every
    mode, as before.

    ``fof_writer`` is the function that writes the ``fof`` dialect, with the signature
    of :func:`generate_tptp_problem_with_mapping`, which is the default. A backend
    passes the name it has bound in its own module, so that the problem text a prover
    is given stays substitutable at the one place each backend reads it from. It is
    called with ``premise_names=`` only when the caller passed some.

    ``premise_names`` names the premises' lines in whichever dialect is written (see
    :func:`generate_tptp_problem_with_mapping`); the returned problem's ``name_map``
    records them. A refusal that is about the names (a ``ValueError`` or ``TypeError``
    that is no :class:`~unicode_fol_kit.atp.tptp_tff.Tf0Refusal`) is raised in every
    mode, and is not what the automatic mode falls back from.
    """
    premises = list(premises)
    refusal: Optional[str] = None
    typed_refusal: Optional[NotImplementedError] = None
    if tff is None:
        use_tff = problem_needs_tff(premises, conclusion)
    else:
        use_tff = tff
    if use_tff:
        try:
            text, mapping = generate_tff_problem_with_mapping(
                premises, conclusion, premise_names=premise_names)
        except NotImplementedError as exc:
            # ``Tf0Refusal`` is one, and so is the typed writer's refusal of a node
            # outside its fragment (``Count``, ``Contrast``, ``Measure``) that the
            # ``fof`` writer does write.
            if tff is not None:
                raise
            typed_refusal = exc
            refusal = str(exc)
        else:
            return TptpProblem(text, mapping, "tff")
    write_fof = generate_tptp_problem_with_mapping if fof_writer is None else fof_writer
    try:
        if premise_names is None:
            text, mapping = write_fof(premises, conclusion)
        else:
            text, mapping = write_fof(premises, conclusion, premise_names=premise_names)
    except NotImplementedError as exc:
        if typed_refusal is not None:
            raise exc from typed_refusal
        raise
    return TptpProblem(text, mapping, "fof", refusal)
