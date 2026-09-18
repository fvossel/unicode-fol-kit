"""Kit AST -> Prolog / Datalog clauses.

The missing return leg of :mod:`unicode_fol_kit.fol.prolog_input`: that module
reads a fact or a definite/normal clause into a kit formula; this module goes
back the other way, for a formula that was BUILT to look like one — a rule
mined from a structure, a hand-written class definition, or the classical
reading of a clause that came from somewhere else and needs to travel back out
as text a Prolog engine (or a rule learner such as Popper) can consume.

**Not a ``Node.to_prolog()`` method.** Every other exporter in this package
(``to_tptp``, ``to_prover9``, ``to_latex``, ``to_z3``) is a total syntactic
recursion: every node type has *some* rendering in the target syntax, so
spreading the method across every AST class is the natural shape. Prolog is
different — it can only express a narrow shape (a fact, or a single-headed
implication whose body combines facts with ``,``/``;``/opt-in ``\\+``), and
most formulas have **no** Prolog reading at all. A method on every node class
would need to raise from nearly every one of them; a single function that
inspects the *whole* clause shape up front and refuses by name is both more
honest about what this format can hold and mirrors how
:func:`~unicode_fol_kit.fol.prolog_input.parse_prolog_clause` reads it back in
one place rather than one grammar rule per node type.

**Equivalence-preserving by construction, not by clausification.** The
accepted fragment is the EXACT syntactic mirror of
:func:`~unicode_fol_kit.fol.prolog_input.parse_prolog_clause`'s ``mode="clause"``
reading:

- a bare (or ``∀``-closed) :class:`~unicode_fol_kit.fol.nodes.Atom` — a fact,
  ``pred(args).``;
- a (possibly ``∀``-prefixed)
  :class:`~unicode_fol_kit.fol.nodes.Implies`\\ ``(body, head)`` where ``head``
  is a single atom and ``body`` is built only from
  :class:`~unicode_fol_kit.fol.nodes.And`/:class:`~unicode_fol_kit.fol.nodes.Or`/
  :class:`~unicode_fol_kit.fol.nodes.Atom`/``Not(Atom)`` — ``Head :- Body.``.

Nothing else is rendered — it is REFUSED, by name, the same way
:func:`unicode_fol_kit.fol.normalforms._unsupported_hint` points a caller at
the right tool for a node the classical normal forms cannot take either. The
direct shape check ALONE is enough to refuse everything outside the fragment
soundly; :func:`~unicode_fol_kit.fol.normalforms.is_horn` is not used as a
gate on top of it (a formula using ``\\+`` classically is typically not even
a classical Horn clause — ``Q(x) ∧ ¬R(x) → P(x)`` clausifies to
``¬Q(x) ∨ R(x) ∨ P(x)``, two positive literals — so gating acceptance on
``is_horn`` would refuse exactly the clauses the negation-as-failure opt-in
below exists to allow). It is used for exactly one thing: when the direct
shape check has ALREADY failed (the formula is not directly a fact or a
``body → head`` implication), ``is_horn`` checks whether the formula's
skolemised/CNF clausal form would nonetheless be Horn, and if so the refusal
says so explicitly — because that is the dangerous NEAR MISS the original
version of this feature would have silently mis-rendered: skolemize is
satisfiability-, not equivalence-preserving (see
:mod:`unicode_fol_kit.fol.normalforms`'s own docstring), so a naive
"``is_horn(node)`` is True, so clausify and emit" exporter would have swapped
equivalence for mere equisatisfiability. That check can only ever ADD a more
specific reason to a refusal that was already happening — it never turns a
refusal into an acceptance.

**Negation as failure is opt-in, and is NOT classical negation** — the same
discipline the importer applies, inverted. ``Not(Atom)`` in the body only
renders as ``\\+ Atom`` when the caller passes
``negation_as_failure="classical"``; otherwise it is refused, naming the same
"closed world assumption" reason
:func:`~unicode_fol_kit.fol.prolog_input.parse_prolog_clause` gives on the way
in. Passing the opt-in makes the round trip syntactically faithful (the
emitted ``\\+`` reads back as the same ``Not(Atom)``), but it does **not**
make ``\\+`` and ``¬`` mean the same thing when the emitted program is
actually *run*: ``\\+ G`` succeeds whenever Prolog FAILS TO PROVE ``G``, which
agrees with ``¬G`` only when the program is COMPLETE for ``G`` — every ground
instance that is true (in whatever structure the program is meant to model)
is also derivable from the program. When the program is incomplete — some
true fact about ``G`` was never asserted — ``\\+ G`` succeeds where ``¬G`` is
in fact false. That disagreement (not a hypothetical: see
``tests/test_prolog_export.py::test_naf_disagrees_with_classical_negation_on_an_incomplete_program``,
which exhibits it with the kit's own resolution prover as the independent
oracle) is exactly why the opt-in exists rather than a silent default: passing
``negation_as_failure="classical"`` is the caller asserting that their program
is, or will be run as, complete for every negated predicate.

**Naming inverts the importer's fold exactly.** A predicate is folded to
Prolog's lower-case-initial spelling (only the FIRST character — mirroring
:func:`unicode_fol_kit.ilp.task.to_prolog_atom` and
:func:`unicode_fol_kit.fol.prolog_input._cap`/``_lower`` rather than importing
either, so a divergence between the three shows up as a failing round-trip
test instead of leaking silently); a name that does not fold back to the
EXACT original spelling (i.e. does not start with an upper-case letter — the
kit's own signal for predicate-hood, see
:mod:`unicode_fol_kit.fol._identifiers`) is refused rather than exported under
a spelling that would not read back to itself. A constant or function name is
emitted VERBATIM (the importer never folds one), quoted with Prolog's
``'...'`` syntax whenever it is not already a legal bare atom. Every variable
in a clause is renamed to a fresh, upper-case-initial Prolog spelling
(``V0``, ``V1``, ...) — the same convention
:meth:`~unicode_fol_kit.fol.nodes.Variable.to_prover9` uses under
``set(prolog_style_variables)`` — assigned in the SAME alphabetical order
:func:`~unicode_fol_kit.fol.prolog_input.parse_prolog_clause` itself closes
variables in, so the round trip lands on the identical quantifier nesting,
not merely an alpha-equivalent one. Prolog variable spelling is scoped to one
clause and carries no meaning beyond identity, so the original kit name is
never preserved (nor does it need to be).

**Numbers and zero-arity function terms are refused, not approximated,
when Prolog has no exact reading for them.** A :class:`Number` whose value
would print outside :func:`~unicode_fol_kit.fol.prolog_input.parse_prolog_clause`'s
numeral grammar — scientific notation for a very large/small float, or the
non-finite ``nan``/``inf``/``-inf`` — is refused rather than emitted as text
the importer cannot read back (``nan``/``inf`` are worse than a parse error:
they would silently reparse as a *different* node type, :class:`Constant`,
with no error at all). A zero-argument :class:`Function` is refused for the
same reason: Prolog syntax cannot write ``f()`` distinct from the bare atom
``f``, so it would reparse as a :class:`Constant`, not a :class:`Function` —
confirmed with the kit's own resolution prover that the two are not
logically equivalent.

Public API: :func:`formula_to_prolog_clause` (one clause) and
:func:`formula_to_prolog_program` (several, one per line, splitting a
top-level conjunction the way
:func:`~unicode_fol_kit.fol.prolog_input.parse_prolog_program` returns several
clauses rather than one).
"""

import re
from typing import Iterable, List, Union

from .nodes import (
    Node, Variable, Constant, Number, Function, Atom, Not, And, Or, Implies,
    Quantifier, free_variables,
)
from .normalforms import is_horn, _unsupported_hint

__all__ = [
    "PrologExportError", "formula_to_prolog_clause", "formula_to_prolog_program",
]

_FORALL = ("∀", "forall")

#: Mirrors :data:`unicode_fol_kit.fol.prolog_input._ATOM_RE` exactly (a legal
#: BARE Prolog atom) rather than importing it — the same "duplicate a tiny
#: naming rule so a divergence fails a test instead of leaking silently"
#: convention every importer/exporter pair in this package already follows
#: (see :func:`unicode_fol_kit.fol.prolog_input._cap`'s docstring).
_ATOM_RE = re.compile(r"^[a-z][A-Za-z0-9_]*$")

#: Mirrors :data:`unicode_fol_kit.fol.prolog_input._NUMBER_RE` exactly (the
#: only numeral shape ``parse_prolog_clause`` reads back — a plain, optionally
#: signed, optionally decimal literal; no exponent, no ``nan``/``inf``), same
#: duplicate-rather-than-import convention as ``_ATOM_RE`` above. Python's
#: ``str()`` of a :class:`~unicode_fol_kit.fol.nodes.Number`'s ``value`` falls
#: outside this grammar for very large/small floats (``str(1e20) ==
#: '1e+20'``) and for the non-finite floats ``nan``/``inf``/``-inf`` — those
#: are refused in :func:`_render_term` rather than emitted as text the kit's
#: own importer could not read back (or, worse for ``nan``/``inf``, would
#: silently read back as a *different* node type, :class:`Constant`, with no
#: error at all).
_NUMBER_RE = re.compile(r"^-?\d+(?:\.\d+)?$")


class PrologExportError(ValueError):
    """Raised when a formula has no sound Prolog clause reading.

    Not a :class:`~unicode_fol_kit.fol.naming.ParsingError` subclass — this
    module never parses anything; it is the exporter's own refusal, in the
    same spirit as :mod:`unicode_fol_kit.fol.casl_export`'s ``ValueError``
    exceptions and :class:`~unicode_fol_kit.fol.tptp_repair.TptpRepairError`.
    Every message names the offending construct or reason, never a bare "invalid
    formula".
    """


# ---------------------------------------------------------------------------
# Naming
# ---------------------------------------------------------------------------

def _quote_if_needed(text: str) -> str:
    """Return ``text`` bare if it is already a legal Prolog atom, else quoted.

    The escaping is the exact inverse of
    :func:`unicode_fol_kit.fol.prolog_input._unquote`: a backslash or a single
    quote inside the content is backslash-escaped, nothing else is touched.
    """
    if _ATOM_RE.fullmatch(text):
        return text
    escaped = text.replace("\\", "\\\\").replace("'", "\\'")
    return f"'{escaped}'"


def _predicate_text(name: str) -> str:
    """The Prolog spelling of a kit PREDICATE name — fold the first character
    down, then quote if the result is not a bare atom.

    :func:`~unicode_fol_kit.fol.prolog_input.parse_prolog_clause` folds a
    Prolog functor's first character UP to build a predicate name (``_cap``),
    on both the bare and the quoted route (see that module's docstring for
    why a quoted ``'1,2-diacyl'`` still "keeps its exact characters" despite
    the unconditional fold: ``_cap`` is a no-op on a non-letter first
    character). Inverting that fold is only sound when the kit's own name
    starts with the upper-case half of the SAME fold — i.e. when it is
    already a legal kit predicate spelling in the first place (the
    first-letter-is-upper-case convention every kit predicate is parsed
    under; see :mod:`unicode_fol_kit.fol._identifiers`). A name that does not
    satisfy this is refused rather than exported under a spelling that would
    not read back to itself.
    """
    folded = name[:1].lower() + name[1:] if name else name
    refolded = folded[:1].upper() + folded[1:] if folded else folded
    if refolded != name:
        raise PrologExportError(
            f"formula_to_prolog_clause: the predicate name {name!r} does not "
            "start with an upper-case letter, so it is not a legal kit "
            "predicate spelling in the first place (every kit predicate is "
            "parsed as starting upper-case — see "
            "unicode_fol_kit.fol._identifiers) and folding it to a Prolog "
            "functor would not read back to this exact name.")
    return _quote_if_needed(folded)


def _term_text(name: str) -> str:
    """The Prolog spelling of a kit CONSTANT or FUNCTION name — verbatim,
    quoted if it is not already a legal bare atom.

    Unlike a predicate, :func:`~unicode_fol_kit.fol.prolog_input.parse_prolog_clause`
    never folds a constant or function name's case (see its module
    docstring's naming section and ``tests/test_prolog_input.py``'s
    ``test_a_compound_term_becomes_a_function_not_a_predicate``), so no
    inversion is needed here — only quoting.
    """
    return _quote_if_needed(name)


def _variable_names(variables) -> dict:
    """``{kit Variable name -> fresh Prolog spelling}`` for one clause.

    Every variable becomes ``V0``, ``V1``, ... — upper-case-initial, the
    convention :meth:`~unicode_fol_kit.fol.nodes.Variable.to_prover9` also
    uses under ``set(prolog_style_variables)`` — assigned in the SAME
    alphabetical order (by the ORIGINAL kit name) that
    :func:`~unicode_fol_kit.fol.prolog_input.parse_prolog_clause`'s own
    ``_close`` helper uses to re-quantify them on the way back in. Because
    the fresh names are zero-padded to a common width, sorting them
    LEXICALLY (which is what ``_close`` does on re-import) reproduces this
    exact assignment order regardless of how many variables the clause has —
    so the round trip lands on the identical quantifier nesting, not merely
    an alpha-equivalent one.
    """
    ordered = sorted(variables, key=lambda v: v.name)
    width = max(1, len(str(max(len(ordered) - 1, 0))))
    return {v.name: f"V{i:0{width}d}" for i, v in enumerate(ordered)}


# ---------------------------------------------------------------------------
# Terms
# ---------------------------------------------------------------------------

def _render_term(node: Node, names: dict) -> str:
    if isinstance(node, Variable):
        try:
            return names[node.name]
        except KeyError:  # pragma: no cover — every free variable of the
            # clause is registered by the caller before rendering starts.
            raise PrologExportError(
                f"formula_to_prolog_clause: internal error — variable "
                f"{node.name!r} was not in the clause's own free-variable set")
    if isinstance(node, Constant):
        return _term_text(node.name)
    if isinstance(node, Number):
        text = str(node.value)
        if not _NUMBER_RE.fullmatch(text):
            raise PrologExportError(
                f"formula_to_prolog_clause: the number {node.value!r} would "
                f"render as {text!r}, which is outside "
                "parse_prolog_clause's numeral grammar (-?\\d+(\\.\\d+)?, no "
                "exponent, no nan/inf) and would not read back to this exact "
                "value — refused rather than emitted as text the kit's own "
                "importer could not parse (or, for nan/inf, would silently "
                "misread as a Constant instead of a Number)")
        return text
    if isinstance(node, Function):
        if not node.args:
            raise PrologExportError(
                f"formula_to_prolog_clause: {node.name!r} is a 0-arity "
                "Function term — Prolog syntax has no way to write 'f()' "
                "distinct from the bare atom 'f', so parse_prolog_clause "
                "would read the emitted text back as a Constant, not a "
                "Function (a genuine change of node type, not merely of "
                "spelling — the kit's own resolution prover confirms "
                "Atom('p', [Function('f', [])]) and Atom('p', "
                "[Constant('f')]) are not logically equivalent in either "
                "direction). Use Constant instead if a bare atom is what is "
                "meant.")
        args = ", ".join(_render_term(a, names) for a in node.args)
        return f"{_term_text(node.name)}({args})"
    raise PrologExportError(
        f"formula_to_prolog_clause: {type(node).__name__} has no Prolog term "
        f"reading{_unsupported_hint(node)}")


# ---------------------------------------------------------------------------
# Atoms (predicate applications)
# ---------------------------------------------------------------------------

def _check_not_comparison(atom: Atom) -> None:
    """Refuse ``=``/``≠``/``<``/``>``/``≤``/``≥`` — Prolog reads none of
    them (see :mod:`unicode_fol_kit.fol.prolog_input`'s module docstring:
    arithmetic comparison is one of the constructs it refuses on the way
    in), so there is no sound way back out either.
    """
    if atom.predicate in Atom.INFIX_PREDS_P9:
        raise PrologExportError(
            f"formula_to_prolog_clause: {atom.predicate!r} is a comparison/"
            "equality predicate — parse_prolog_clause has no reading for "
            "'=', '≠', '<', '>', '≤', or '≥' (they are not part of the "
            "accepted Prolog fragment on the way in either), so exporting it "
            "would not round trip")


def _render_atom(atom: Atom, names: dict) -> str:
    _check_not_comparison(atom)
    predicate = _predicate_text(atom.predicate)
    if not atom.args:
        return predicate
    args = ", ".join(_render_term(a, names) for a in atom.args)
    return f"{predicate}({args})"


# ---------------------------------------------------------------------------
# Bodies: And / Or / Atom / Not(Atom)
# ---------------------------------------------------------------------------

def _render_body(node: Node, names: dict, negation_as_failure: str) -> str:
    if isinstance(node, Atom):
        return _render_atom(node, names)
    if isinstance(node, Not):
        if negation_as_failure != "classical":
            raise PrologExportError(
                "formula_to_prolog_clause: the body contains classical "
                f"negation ({node.to_unicode_str()!r}), which has no sound "
                "'\\+' reading unless the caller asserts the closed world "
                "assumption holds for the program the clause will run in — "
                "pass negation_as_failure='classical' to opt in (see the "
                "module docstring for exactly when '\\+' and classical ¬ "
                "agree, and when they do not)")
        if not isinstance(node.formula, Atom):
            raise PrologExportError(
                "formula_to_prolog_clause: only '\\+' applied to a single "
                f"atom is exported; {type(node.formula).__name__} inside "
                f"'\\+' ({node.to_unicode_str()!r}) is outside the accepted "
                "fragment (parse_prolog_clause's own body grammar allows "
                "'\\+' to nest further, but this exporter deliberately "
                "narrows to '\\+ Atom' only)")
        return f"\\+ {_render_atom(node.formula, names)}"
    if isinstance(node, And):
        left = _render_body_operand(node.left, names, negation_as_failure, "and")
        right = _render_body_operand(node.right, names, negation_as_failure, "and")
        return f"{left}, {right}"
    if isinstance(node, Or):
        left = _render_body_operand(node.left, names, negation_as_failure, "or")
        right = _render_body_operand(node.right, names, negation_as_failure, "or")
        return f"{left} ; {right}"
    raise PrologExportError(
        f"formula_to_prolog_clause: {type(node).__name__} has no Prolog body "
        f"reading{_unsupported_hint(node)} — a body may only combine facts "
        "with ',' (∧), ';' (∨), and opt-in '\\+' (see the module docstring "
        "for the accepted fragment)")


def _render_body_operand(node: Node, names: dict, negation_as_failure: str,
                         parent: str) -> str:
    """Render one operand of And/Or, parenthesising only where Prolog's
    precedence (',' binds tighter than ';') would otherwise change the
    parse: an Or nested inside an And's operand position.

    Every other nesting (And-in-And, Or-in-Or, either under a parent Or, a
    bare Atom or '\\+ Atom' anywhere) already parses back to the intended
    shape without parentheses — and even where the exact associativity
    differs from the input tree, that difference is one
    :func:`unicode_fol_kit.eval.canonical.canonicalize` already quotients
    out (And/Or are flattened and re-sorted there), so it is never a
    round-trip risk.
    """
    text = _render_body(node, names, negation_as_failure)
    if parent == "and" and isinstance(node, Or):
        return f"({text})"
    return text


# ---------------------------------------------------------------------------
# Clauses
# ---------------------------------------------------------------------------

def _strip_foralls(node: Node) -> Node:
    """Peel off every leading ``∀`` and return the matrix underneath.

    The peeled variables are not inspected: whatever free variables remain
    in the matrix (whether they were bound here, were free in the input
    all along, or a caller's vacuous ``∀`` bound nothing at all) are exactly
    what :func:`~unicode_fol_kit.fol.prolog_input.parse_prolog_clause`
    re-quantifies on the way back in, so re-deriving them from the matrix
    itself — rather than trusting the caller's prefix — is what makes both
    a bare formula (``Implies(body, head)``, free variables and all) and an
    already ``∀``-closed one valid input.
    """
    matrix = node
    while isinstance(matrix, Quantifier) and matrix.type in _FORALL:
        matrix = matrix.formula
    return matrix


def formula_to_prolog_clause(node: Node, *, negation_as_failure: str = "refuse") -> str:
    """Render ``node`` as ONE Prolog clause: a fact or a definite/normal rule.

    The accepted fragment is the exact mirror of
    :func:`~unicode_fol_kit.fol.prolog_input.parse_prolog_clause`'s
    ``mode="clause"`` reading — see the module docstring. Anything else is
    refused, naming the construct.

    Args:
        node: a bare or ``∀``-closed :class:`~unicode_fol_kit.fol.nodes.Atom`
            (a fact), or a bare or ``∀``-closed
            :class:`~unicode_fol_kit.fol.nodes.Implies`\\ ``(body, head)``
            (a rule) whose ``head`` is a single atom and whose ``body`` is
            built from And/Or/Atom/``Not(Atom)`` only.
        negation_as_failure: ``"refuse"`` (default) — any ``Not`` in the body
            is refused — or ``"classical"`` to render ``Not(Atom)`` as
            ``\\+ Atom``, asserting that ``\\+`` and classical ¬ agree for
            this clause's program (see the module docstring for exactly
            when that holds).

    Returns:
        The clause text, ending in ``"."``.

    Raises:
        PrologExportError: ``node`` is outside the accepted fragment, its
            head has a variable not bound by its body (not range-restricted),
            a predicate/constant/function name cannot be rendered soundly, or
            ``negation_as_failure`` is not one of the documented values.

    Example:
        >>> from unicode_fol_kit.fol.nodes import Atom, Variable, Implies, Quantifier
        >>> from unicode_fol_kit.fol.prolog_export import formula_to_prolog_clause
        >>> x = Variable("x")
        >>> clause = Quantifier("∀", x, Implies(Atom("Human", [x]), Atom("Mortal", [x])))
        >>> formula_to_prolog_clause(clause)
        'mortal(V0) :- human(V0).'
    """
    if negation_as_failure not in ("refuse", "classical"):
        raise PrologExportError(
            "formula_to_prolog_clause: unknown negation_as_failure="
            f"{negation_as_failure!r}, expected 'refuse' or 'classical'")

    matrix = _strip_foralls(node)

    if isinstance(matrix, Atom):
        names = _variable_names(free_variables(matrix))
        return _render_atom(matrix, names) + "."

    if isinstance(matrix, Implies):
        body, head = matrix.left, matrix.right
        if not isinstance(head, Atom):
            raise PrologExportError(
                "formula_to_prolog_clause: the head of a rule must be a "
                f"single atom, got {type(head).__name__} "
                f"({head.to_unicode_str()!r}) — a disjunctive or otherwise "
                "compound head has no Prolog reading (a Prolog rule has "
                "exactly one head literal)")
        unbound = free_variables(head) - free_variables(body)
        if unbound:
            unbound_str = ", ".join(sorted(v.name for v in unbound))
            raise PrologExportError(
                f"formula_to_prolog_clause: the head variable(s) {unbound_str} "
                "do not occur in the body — a Prolog rule with an unbound "
                "head variable does not mean what the universally-quantified "
                "formula meant (Prolog would leave it ranging over every "
                "value at that argument position instead)")
        names = _variable_names(free_variables(matrix))
        body_text = _render_body(body, names, negation_as_failure)
        head_text = _render_atom(head, names)
        return f"{head_text} :- {body_text}."

    hint = _unsupported_hint(matrix)
    horn_note = ""
    try:
        if is_horn(node):
            horn_note = (
                " Note: is_horn(node) is True — the SKOLEMISED/CNF clausal "
                "form happens to be Horn — but skolemize() is "
                "satisfiability-preserving, not equivalence-preserving (see "
                "unicode_fol_kit.fol.normalforms's docstring), so emitting "
                "those clauses instead of this formula would silently swap "
                "equivalence for mere equisatisfiability. "
                "formula_to_prolog_clause only exports a formula that is "
                "DIRECTLY a fact or a possibly ∀-prefixed body → head "
                "implication; rewrite the formula into that shape by hand "
                "if it should be exported.")
    except Exception:
        pass
    raise PrologExportError(
        f"formula_to_prolog_clause: {type(matrix).__name__} "
        f"({node.to_unicode_str()!r}) has no Prolog clause reading{hint} — "
        "only a fact (a bare atom) or a definite/normal clause (a possibly "
        "∀-prefixed body → head implication) is exported; see the module "
        f"docstring for the accepted fragment.{horn_note}")


def _conjuncts(node: Node) -> List[Node]:
    """Flatten a top-level ``∧`` tree, left to right — the same shallow
    split :mod:`unicode_fol_kit.ilp.readback` and
    :mod:`unicode_fol_kit.fol.normalforms` each keep a private copy of
    rather than importing, so a change to the convention shows up as a
    failing test in each user instead of leaking silently."""
    if isinstance(node, And):
        return _conjuncts(node.left) + _conjuncts(node.right)
    return [node]


def formula_to_prolog_program(nodes_or_conjunction: Union[Node, Iterable[Node]],
                              *, negation_as_failure: str = "refuse") -> str:
    """Render several clauses as one Prolog program, one clause per line.

    Args:
        nodes_or_conjunction: either a single formula whose top level is an
            ``∧`` of several fact/rule-shaped conjuncts (split the same way
            :func:`~unicode_fol_kit.fol.prolog_input.parse_prolog_program`'s
            multi-clause reading returns them separately rather than
            disjoined), or any iterable of such formulas directly.
        negation_as_failure: forwarded to :func:`formula_to_prolog_clause`
            for every clause.

    Returns:
        The clauses' text, one per line, each ending in ``"."``.

    Raises:
        PrologExportError: as :func:`formula_to_prolog_clause`, for whichever
            clause fails first, with that clause's position and text appended
            — mirroring :func:`~unicode_fol_kit.fol.prolog_input.parse_prolog_program`'s
            own ``"(in clause: ...)"`` suffix on the way in, so a failure in a
            program of several clauses names which one, not just why.
    """
    clauses = (_conjuncts(nodes_or_conjunction) if isinstance(nodes_or_conjunction, Node)
              else list(nodes_or_conjunction))
    rendered = []
    for index, clause in enumerate(clauses):
        try:
            rendered.append(formula_to_prolog_clause(
                clause, negation_as_failure=negation_as_failure))
        except PrologExportError as exc:
            raise PrologExportError(
                f"{exc} (in clause {index + 1} of {len(clauses)}: "
                f"{clause.to_unicode_str()!r})")
    return "\n".join(rendered)
