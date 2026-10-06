r"""DOL (Distributed Ontology, Modelling and Specification Language) library
emission over CASL specs — a thin structuring layer built entirely on top of
:mod:`unicode_fol_kit.fol.casl_export`, never reimplementing it.

`DOL <https://ontohub.org/dol>`_ is CoFI/OntoHub's heterogeneous layer above
CASL (and OWL, and every other logic Hets understands): a ``library``
groups several named ``spec`` blocks and lets one spec build on another via
structuring (``spec B = A then ...``). :mod:`unicode_fol_kit.fol.casl_export`
already renders one classical/many-sorted FOL formula batch as one
self-contained ``spec ... end`` block; this module's only job is to emit
SEVERAL such blocks inside one ``library``/``logic CASL`` wrapper, with an
optional ``then``-extension between them. It does not add a single new
formula-rendering rule of its own — every axiom/conjecture line in the
output comes verbatim from :func:`~unicode_fol_kit.fol.casl_export.to_casl_spec`.

Scope: emission only — no ``parse_dol_library``
------------------------------------------------
This module is one-way, like :mod:`~unicode_fol_kit.fol.casl_export` before
it added an importer counterpart
(:mod:`unicode_fol_kit.fol.casl_import`) — going the other way (parsing a
full DOL library text, with its ``library``/``logic``/multi-``spec``/
``then`` structuring, back into per-spec ASTs) is a materially bigger
grammar than :func:`~unicode_fol_kit.fol.casl_import.parse_casl_spec`
already refuses to attempt for a SINGLE spec (see that module's own "Scope"
section — ``then``/``view``/structuring constructs are explicitly out of
its fragment). A ``parse_dol_library`` is future scope, not started here;
:func:`unicode_fol_kit.fol.casl_import.parse_casl_spec` remains usable
directly on any ONE ``spec ... end`` block sliced out of this module's own
output (see ``tests/test_dol.py``'s offline consistency check, which does
exactly that as an export/import round-trip sanity test).

Reuse strategy: cut ``to_casl_spec``'s own output, do not re-derive it
------------------------------------------------------------------------
:func:`to_dol_library` calls the PUBLIC
:func:`~unicode_fol_kit.fol.casl_export.to_casl_spec` once per
:class:`DolSpec` — never touching that module's private internals — and
then deterministically slices the BODY (the ``sorts``/``ops``/``preds``/
axiom lines) out of its result: ``to_casl_spec``'s own documented output
shape is always exactly one header line (``spec <NAME> =``), the body, and
one trailing ``end`` line (see that function's docstring), so
``body_text.split("\n")[1:-1]`` is exactly the body, verbatim, no matter how
many sorts/ops/preds/axiom lines it has. This module then re-wraps that same
body under EITHER the same plain header (no ``extends``) or a
``spec <name> = <extends> then`` header (with ``extends``) — see
:func:`_spec_block` for the one place this slice-and-rewrap happens, guarded
by an assertion that the expected header/footer shape actually held (so a
future change to ``to_casl_spec``'s own output shape fails LOUDLY here
rather than silently emitting a malformed library).

``extends`` and signature re-declaration — a deliberate, harmless
consequence of per-spec-independent inference
--------------------------------------------------------------------------
``to_casl_spec`` infers its ``sorts``/``ops``/``preds`` declarations from
ONLY the formulas passed to that one call — it has no notion of "these
symbols are already declared by the spec I ``then``-extend". So if spec
``B`` (``DolSpec(extends="A", ...)``) reuses a predicate or constant that
spec ``A`` already declared, ``B``'s own emitted block RE-DECLARES it too.
This is valid, unremarkable CASL: re-declaring an already-visible symbol
with an IDENTICAL profile (same arity/argument sorts/result sort) under
``then`` is a no-op in CASL's static semantics, not a conflict — Hets
accepts it. It only becomes a genuine problem if the SAME symbol name ends
up with two DIFFERENT profiles across ``A`` and ``B`` (e.g. different
``default_sort`` values producing different inferred sorts for the same
predicate) — that is a real modelling error on the caller's part, and
surfaces exactly the way any other CASL redeclaration conflict would (a
Hets-side parse/static-analysis error), not something this module tries to
pre-empt. Callers who want a shared vocabulary should keep every
:class:`DolSpec` in the same library on the same ``default_sort``.

A spec that extends another SEES the other's symbols without declaring them, and a bound
variable that is spelled like a visible symbol would be read as that variable. So a
bound variable of the extending spec is never given the spelling of a symbol of the
specs it extends (found through ``specs``, transitively): the extending spec's
``to_casl_spec`` call is given those names as ``visible_symbols`` and renames the
clashing binders, as it does for the spec's own symbols.

What is NOT re-checked here
------------------------------
* Referential integrity of ``extends``: this module does not verify that a
  ``DolSpec.extends`` name is itself a key of ``specs`` (or defined
  anywhere at all) — a library legitimately may extend a spec defined in
  ANOTHER library/import this module knows nothing about. That is the
  caller's responsibility; a dangling reference surfaces as a Hets-side
  error when the library is actually uploaded, not here.
* Formula validity: every :func:`~unicode_fol_kit.fol.casl_export.to_casl_spec`
  refusal (an out-of-fragment node, a free variable, a sort conflict, a
  reserved-word identifier, an empty axiom+conjecture batch, …) propagates
  through :func:`to_dol_library` UNCHANGED — this module adds no new
  formula-level validation of its own, by design (single source of truth).

Name validation
----------------
The library name and every ``DolSpec.extends`` target name are checked
against the same simple-CASL-identifier pattern and reserved-keyword list
:mod:`~unicode_fol_kit.fol.casl_export` checks ``spec_name`` against (a
small, independent literal copy of that list — the same "duplicate by
content, not by importing a private name" reasoning
:mod:`unicode_fol_kit.fol.signature` and
:mod:`unicode_fol_kit.fol.casl_import` give for their own copies). Each
:class:`DolSpec`'s own key in ``specs`` is NOT separately checked here — it
is passed straight through as ``spec_name`` to
:func:`~unicode_fol_kit.fol.casl_export.to_casl_spec`, which already
performs that exact check (:func:`~unicode_fol_kit.fol.casl_export._validate_spec_name`)
and raises ``ValueError`` itself; duplicating it here would just be a second
copy of the same regex answering the same question.
"""

from collections import OrderedDict
from dataclasses import dataclass, field
from typing import Optional, Sequence
import re

from ..fol.casl_export import to_casl_spec
from ..fol.nodes import Atom, Constant, Function, Node, SortedConstant, Variable
from ..fol._symbol_names import dedupe
from ..fol.qml import qml_validity_formula

__all__ = [
    "to_dol_library", "DolSpec",
    "to_dol_library_from_modal", "sanitize_modal_identifiers",
]


# Mirrors unicode_fol_kit.fol.casl_export._CASL_KEYWORDS /
# unicode_fol_kit.fol.casl_import._CASL_KEYWORDS — a small, independent
# literal copy (see the module docstring's "Name validation" section for why
# this is not an import of another module's private name).
_CASL_KEYWORDS = frozenset({
    "and", "arch", "as", "assoc", "axiom", "axioms", "closed", "comm", "def",
    "else", "end", "exists", "false", "fit", "forall", "free", "from",
    "generated", "get", "given", "hide", "idem", "if", "in", "lambda",
    "library", "local", "logic", "not", "op", "ops", "pred", "preds",
    "result", "reveal", "sort", "sorts", "spec", "then", "to", "true",
    "type", "types", "unit", "units", "var", "vars", "version", "view",
    "when", "with", "within",
})

_SIMPLE_ID_RE = re.compile(r"[A-Za-z][A-Za-z0-9_]*")


def _check_casl_word(name: str, kind: str) -> None:
    """Refuse ``name`` (a ``kind`` identifier) if it is not a simple CASL
    word, or collides with a CASL keyword — see the module docstring's
    "Name validation" section."""
    if not _SIMPLE_ID_RE.fullmatch(name):
        raise ValueError(
            f"hets.dol: {kind} {name!r} is not a simple CASL identifier "
            "matching [A-Za-z][A-Za-z0-9_]*."
        )
    if name in _CASL_KEYWORDS:
        raise ValueError(
            f"hets.dol: {kind} name '{name}' collides with the reserved "
            f"CASL keyword '{name}'."
        )


@dataclass
class DolSpec:
    """One ``spec`` block's worth of input to :func:`to_dol_library`.

    Args:
        axioms: the spec's own axioms (rendered as ``. <formula>`` lines,
            exactly as :func:`~unicode_fol_kit.fol.casl_export.to_casl_spec`
            would for a standalone spec).
        conjectures: the spec's own ``%implied`` goals. Defaults to empty —
            a spec that only extends another and adds axioms (no new goal)
            is common.
        extends: the name of another spec this one structurally extends via
            CASL's ``then`` — renders the header as
            ``spec <this_name> = <extends> then`` instead of plain
            ``spec <this_name> =``. ``None`` (the default) renders a plain,
            unstructured spec. Not checked for referential integrity against
            the other keys of the ``specs`` mapping passed to
            :func:`to_dol_library` — see that function's module-level
            docstring section "What is NOT re-checked here".
        default_sort: passed straight through to this spec's own
            :func:`~unicode_fol_kit.fol.casl_export.to_casl_spec` call —
            see that function's docstring for what it controls (the sort a
            plain, unsorted quantifier is declared at).
    """

    axioms: Sequence[Node]
    conjectures: Sequence[Node] = field(default_factory=tuple)
    extends: Optional[str] = None
    default_sort: str = "Thing"


def _names_of(spec: DolSpec) -> set:
    """Every symbol name of ``spec``'s own formulas: constants, functions, predicates, the
    sorts they write, and the spec's default sort (an over-approximation is harmless: the
    names only keep a bound variable away)."""
    names = {spec.default_sort}
    for formula in (*spec.axioms, *spec.conjectures):
        for node in formula.walk():
            if isinstance(node, (Constant, SortedConstant, Function)):
                names.add(node.name)
            elif isinstance(node, Atom):
                names.add(node.predicate)
            sort = getattr(node, "sort", None)
            if isinstance(sort, str):
                names.add(sort)
    return names


def _inherited_names(spec: DolSpec, specs: "OrderedDict[str, DolSpec]") -> frozenset:
    """The symbol names ``spec`` sees from the specs it extends (``then``), transitively.

    An extended spec that is not a key of ``specs`` is defined elsewhere and cannot be
    read here (see the module docstring's "What is NOT re-checked here")."""
    names: set = set()
    seen: set = set()
    parent = spec.extends
    while parent is not None and parent in specs and parent not in seen:
        seen.add(parent)
        names |= _names_of(specs[parent])
        parent = specs[parent].extends
    return frozenset(names)


def _spec_block(spec_name: str, spec: DolSpec, inherited: frozenset = frozenset()) -> str:
    """Render one ``spec <spec_name> = [<extends> then] ... end`` block by
    slicing the body out of a fresh :func:`~unicode_fol_kit.fol.casl_export.to_casl_spec`
    call — see the module docstring's "Reuse strategy" section. ``inherited`` are the
    symbol names the spec sees from the specs it extends: a bound variable is never
    given the spelling of one of them (``to_casl_spec``'s ``visible_symbols``)."""
    body_text = to_casl_spec(
        list(spec.axioms), conjectures=list(spec.conjectures),
        spec_name=spec_name, default_sort=spec.default_sort,
        visible_symbols=inherited,
    )
    body_lines = body_text.split("\n")
    expected_header = f"spec {spec_name} ="
    if len(body_lines) < 2 or body_lines[0] != expected_header or body_lines[-1] != "end":
        # Defensive: guards the slicing assumption above against a future
        # (unanticipated) change to to_casl_spec's output shape — fail
        # loudly here rather than silently emit a malformed library.
        raise AssertionError(
            "hets.dol: to_casl_spec's output shape did not match the "
            f"expected 'spec {spec_name} = ... end' envelope this module's "
            f"body-slicing logic assumes; got first line {body_lines[0]!r} "
            f"and last line {body_lines[-1]!r}."
        )
    body = body_lines[1:-1]

    if spec.extends is not None:
        _check_casl_word(spec.extends, "extends target name")
        header = f"spec {spec_name} = {spec.extends} then"
    else:
        header = expected_header

    return "\n".join([header, *body, "end"])


def to_dol_library(name: str, specs: "OrderedDict[str, DolSpec]") -> str:
    """Render ``specs`` as one DOL library: ``library <name>`` / ``logic
    CASL`` / one ``spec … end`` block per entry, in ``specs`` iteration
    order.

    Args:
        name: the library's own name — checked against the same simple-
            CASL-identifier + reserved-keyword rule as every other name
            this module or :mod:`~unicode_fol_kit.fol.casl_export` emits.
        specs: an ordered mapping from spec name to :class:`DolSpec`. Order
            matters for the emitted text (specs are written out in
            iteration order) and, practically, for validity: a
            ``DolSpec.extends`` reference should generally name a spec that
            appears EARLIER in this mapping (or is defined elsewhere), since
            CASL structuring is not mutually recursive — this module does
            not enforce that ordering itself (see the module docstring's
            "What is NOT re-checked here").

    Returns:
        The complete library text (no trailing newline, matching
        :func:`~unicode_fol_kit.fol.casl_export.to_casl_spec`'s own
        convention), ready to upload as a ``.dol`` file via
        :meth:`unicode_fol_kit.hets.HetsClient.upload`.

    Raises:
        ValueError: ``specs`` is empty; ``name`` or any
            ``DolSpec.extends`` value is not a simple CASL identifier or
            collides with a CASL keyword; or (propagated, unchanged) any
            :func:`~unicode_fol_kit.fol.casl_export.to_casl_spec` refusal
            for one of the individual specs (an out-of-fragment node, a
            free variable, a sort conflict, a bad ``spec_name``, an empty
            axiom+conjecture batch, …).
        NotImplementedError: propagated, unchanged, from
            :func:`~unicode_fol_kit.fol.casl_export.to_casl_spec` (a
            non-classical node in one of the specs' formulas).
    """
    _check_casl_word(name, "library name")
    if not specs:
        raise ValueError(
            "hets.dol: to_dol_library needs at least one spec in 'specs'; "
            "an empty library has nothing to structure."
        )

    lines = [f"library {name}", "logic CASL", ""]
    items = list(specs.items())
    for idx, (spec_name, spec) in enumerate(items):
        lines.append(_spec_block(spec_name, spec, _inherited_names(spec, specs)))
        if idx != len(items) - 1:
            lines.append("")
    return "\n".join(lines)


# =============================================================================
# Quantified modal logic -> CASL/DOL, over fol.qml's standard translation
# =============================================================================
#
# fol.qml.qml_validity_formula already lowers a modal formula to exactly the
# classical FOL fragment fol.casl_export accepts (see that function's own
# docstring) — this section's job is the ONE concrete gap between
# "qml_validity_formula's output" and "a formula to_casl_spec will actually
# accept", point (1); point (2) records the second place one might expect a
# gap, object identity, and why there is none:
#
# (1) Illegal identifiers. qml's own auto-generated fresh variables (the
# world variables _Fresh mints, e.g. "_w0", and the Geach axiom's own
# "_gz0"/"_gw"/"_gu"/"_gv"/"_gt", and the argument variables
# _signature_typing_facts mints for a function's typing fact, "_a0") start
# with an underscore, which is not a legal CASL SIMPLE-ID
# ([A-Za-z][A-Za-z0-9_]*) — casl_export's own honesty convention is to
# REFUSE a bad identifier rather than silently rename it (see its "Reserved
# words and identifier hygiene" docstring section), which is exactly right
# for a name the CALLER chose, but qml's fresh names are an internal
# implementation detail of the translation, not something a caller of this
# bridge ever typed — so THIS module fixes them before they ever reach
# casl_export, rather than asking every caller of qml_validity_formula to
# pre-empt a naming convention that is qml's own.
#
# (2) Object identity needs no help: it arrives binary and CASL-native.
# fol.qml's ``_st`` translates an identity atom ``a = b`` to the SAME binary
# ``a = b`` over the object terms, with NO world argument, and ``a ≠ b`` to
# ``¬(a = b)`` (see that module's "Equality is rigid" section). Identity does
# not vary by world, and the translation says so by not mentioning the world.
# That binary ``=`` is exactly CASL's own built-in equality — always two
# terms, rigid, never declared in ``preds`` — so fol.casl_export renders it
# infix (``a = b``), fol.casl_import parses it back to the identical Atom, and
# nothing in this module renames, aliases or special-cases it. The one other
# ``=`` atom a qml query can contain, the world identity ``w = v`` in qml's
# own temporal ``first_step`` axiom, is the same native symbol: it relates two
# worlds where a user equality relates objects, and what keeps the two kinds
# apart is the ``World``/``Object`` guards, not the symbol. ``≠`` never reaches
# this module at all, because qml has already written it as a negation of
# ``=``, which CASL renders like any other ``not``.
#
# So :func:`_rewrite_casl_names` leaves every ``=`` atom under its literal
# name and refuses every ``≠`` atom. Both matter only for a Node that did NOT
# come out of qml_validity_formula, i.e. one built by hand and handed to
# :func:`sanitize_modal_identifiers` directly (no text front-end of the kit
# parses to a non-binary ``=``/``≠``, and qml_validity_formula itself refuses
# one with a ValueError):
#
# * a ``=`` atom that is not binary is not CASL's identity and is not
#   renamed onto some uninterpreted predicate either: it is passed through
#   unchanged, so fol.casl_export's own exactly-two-terms check refuses it by
#   name (one refusal, one place);
# * a ``≠`` atom of ANY arity is refused here with :class:`NotImplementedError`:
#   CASL has no disequality, and the sanitiser renames identifiers, it does not
#   rewrite connectives, so the caller writes ``Not(Atom("=", ...))``.
#
# History, because the symbols below used to exist: fol.qml once appended the
# world to ``=`` like to any atom, which made it a ternary uninterpreted
# predicate, and this module aliased it to ``weq``/``wneq``. Both are gone
# together; an atom literally named ``weq`` is now an ordinary user predicate
# like any other.
#
# No change to fol.qml's or fol.casl_export's own logic: qml_validity_formula
# is called unmodified, casl_export's own exactly-2-ary "=" check is never
# touched, and the sanitised Node is handed to to_casl_spec via
# to_dol_library exactly as any other DolSpec's axioms/conjectures would be.


def _casl_sanitize_stem(name: str) -> str:
    """A best-effort CASL-legal *candidate* for ``name`` — not yet guaranteed
    unique (see :class:`_CaslIdentifierShim`, which wraps this in
    :func:`~unicode_fol_kit.fol._symbol_names.dedupe` against every other name
    already claimed in the same namespace, so injectivity is enforced exactly
    once, in one place).

    Strips every LEADING underscore first — the shape this shim was written for
    (see the section comment above): the fresh names
    :mod:`unicode_fol_kit.fol.qml` used to generate were ``_w0`` / ``_gz0`` /
    ``_a0``, each an ordinary, already-legal identifier once that convention is
    peeled off. Since 0.30.0 that module mints ``w0`` / ``v0`` style names
    instead (they have to be legal for the KIT's own parser too), so no CALLER
    in this repository still hands this function such a name — the rule stays
    for any other one that might. What is left over is then re-checked against
    CASL's own SIMPLE-ID grammar, and this is the part that is still reached:
    a candidate that does not start with an ASCII letter (all-underscore, or
    digit-leading) is prefixed with ``v``, and any remaining illegal character
    is folded to ``_`` — which is what happens to ``fol.qml``'s ``·`` mark on a
    user predicate named like one of its own relations (``R`` -> ``R·`` ->
    ``R_``), the one shape of illegal CASL identifier this route still emits.
    """
    candidate = name.lstrip("_") or "id"
    if not (candidate[0].isascii() and candidate[0].isalpha()):
        candidate = "v" + candidate
    return "".join(
        ch if (ch.isascii() and (ch.isalnum() or ch == "_")) else "_"
        for ch in candidate)


class _CaslIdentifierShim:
    """Per-formula, INJECTIVE renamer: maps every Variable / (Sorted)Constant-
    or-Function / Atom-predicate name onto a legal, unique CASL identifier,
    leaving every name that already qualifies untouched.

    Three separate TABLES, one per kind of symbol: ``variable`` (bound
    object/world variables), ``term`` (constants AND functions share ONE
    table here, mirroring
    :func:`~unicode_fol_kit.fol.casl_export.to_casl_spec`'s own merged
    ``ops`` declaration block and its ``_CONST_VS_FUNCTION`` dual-use
    refusal), and ``predicate`` (Atom predicate names). A name is mapped only
    within its own table, so a variable and a constant that already are legal
    keep their spelling even when it is the same one; the text then says the
    two apart by renaming the binder (see
    :func:`~unicode_fol_kit.fol.casl_export.to_casl_spec`). A name the shim
    MINTS, on the other hand, is drawn from ONE pool of taken spellings shared
    by the three tables and the sorts of the formula, because CASL writes all
    of them as one identifier: a renamed variable is never given the spelling
    of a constant, a function, a predicate or a sort. ``=`` is not in any
    of them: it is CASL's own native, rigid equality and not a declared
    symbol, so :func:`_rewrite_casl_names` keeps it under its literal name
    and it is never a simple identifier for :meth:`_seed` to claim; ``≠`` is
    refused there before it could be renamed. See the section comment above,
    point (2).

    TWO PASSES per namespace, in that order, is what makes this injective
    regardless of tree-walk order: :meth:`__init__` first walks the WHOLE
    formula and seeds every name that is ALREADY a legal CASL identifier —
    self-mapped, claimed in that namespace's ``used`` set — before any
    illegal name is resolved. Only then does :meth:`_resolve` compute a
    sanitised candidate for an illegal name and hand it to
    :func:`~unicode_fol_kit.fol._symbol_names.dedupe`, which appends a
    numeric suffix on any collision — including a collision with an
    ALREADY-legal name from the seeding pass. This order is load-bearing:
    the fresh variable ``_w0`` sanitises to the natural candidate ``w0`` via
    :func:`_casl_sanitize_stem`, and if the SAME formula also happens to
    bind a genuine, unrelated object variable literally named ``w0`` (an
    already-legal name — this is the exact collision batch note (3) asks to
    be tested), seeding it FIRST means ``_w0``'s candidate is found already
    taken and gets bumped to ``w0_2`` — two DISTINCT source names, two
    DISTINCT output names — rather than the two silently merging into one
    bound variable (a single-pass, seed-as-you-go walk could not guarantee
    this, since it would depend on which of the two names the tree happens
    to visit first).

    Deliberately narrow: an already-legal name that happens to collide with
    a CASL KEYWORD (e.g. a user constant literally named ``type``) is left
    untouched here and surfaces exactly as it always did — a loud
    :class:`ValueError` from :func:`~unicode_fol_kit.fol.casl_export.to_casl_spec`
    itself — because that is a naming choice the CALLER made, not qml's own
    fresh-name convention, and this shim exists to fix the latter, not to
    silently rename the former (see the section comment above).
    """

    def __init__(self, formula: Node):
        self._var, self._term, self._pred = {}, {}, {}
        # The three tables map names of three kinds, but CASL writes all of them as one
        # identifier, so the three kinds draw the names they mint from ONE set of taken
        # spellings: a minted name is fresh against every symbol of the formula, not
        # only against the other symbols of its own kind.
        taken: set = set()
        self._var_used = self._term_used = self._pred_used = taken
        for n in formula.walk():
            if isinstance(n, Variable):
                self._seed(self._var, self._var_used, n.name)
            elif isinstance(n, (Constant, SortedConstant, Function)):
                self._seed(self._term, self._term_used, n.name)
            elif isinstance(n, Atom):
                # '=' and '≠' are not simple identifiers, so _seed ignores them.
                self._seed(self._pred, self._pred_used, n.predicate)
            sort = getattr(n, "sort", None)
            if isinstance(sort, str):
                # a sort a node names is a spelling taken too (it has no table here)
                taken.add(sort)

    @staticmethod
    def _seed(table: dict, used: set, name: str) -> None:
        if name not in table and _SIMPLE_ID_RE.fullmatch(name):
            table[name] = name
            used.add(name)

    @staticmethod
    def _resolve(table: dict, used: set, name: str) -> str:
        if name in table:
            return table[name]
        result = dedupe(_casl_sanitize_stem(name), used)
        table[name] = result
        return result

    def variable(self, name: str) -> str:
        return self._resolve(self._var, self._var_used, name)

    def term(self, name: str) -> str:
        return self._resolve(self._term, self._term_used, name)

    def predicate(self, name: str) -> str:
        return self._resolve(self._pred, self._pred_used, name)


def _rewrite_casl_names(node: Node, shim: _CaslIdentifierShim) -> Node:
    """Rebuild ``node`` with every Variable / (Sorted)Constant / Function /
    Atom-predicate name replaced by ``shim``'s resolution of it.

    The five term/atom classes are handled explicitly (a name is a plain
    ``str`` field, so the generic structural recursion below would copy it
    verbatim rather than sanitise it); every other node — every connective
    and (Sorted)Quantifier — recurses via
    :meth:`~unicode_fol_kit.fol.nodes.Node.map_children`, the kit's shared
    structural-rewrite primitive, which already applies this same function to
    a Quantifier's bound ``variable`` field (a :class:`Variable`, handled by
    the explicit case above) alongside its ``formula`` — so a Quantifier
    needs no special case of its own here. A node type outside
    ``fol.casl_export``'s classical fragment (e.g. a raw :class:`Box` reaching
    this function directly, rather than through
    :func:`~unicode_fol_kit.fol.qml.qml_validity_formula` first) is passed
    through unchanged by that same generic recursion — this function performs
    no fragment check of its own; :func:`~unicode_fol_kit.fol.casl_export.to_casl_spec`
    still refuses it, by name, exactly as it always did.

    An Atom whose predicate is ``=`` or ``≠`` is never renamed (see the section
    comment above :func:`_casl_sanitize_stem`, point (2)): an ``=`` atom is
    CASL's own rigid identity and is kept under its literal name, whatever its
    arity (a non-binary one is refused downstream by
    :func:`~unicode_fol_kit.fol.casl_export.to_casl_spec`, by name, not
    relabelled here); a ``≠`` atom, which CASL has no rendering for at any
    arity and which ``fol.qml`` has already written as ``¬(=)`` before this
    function sees the formula, is refused with :class:`NotImplementedError`
    rather than relabelled onto an unrelated identifier — see that branch's own
    comment.
    """
    if isinstance(node, Variable):
        return Variable(shim.variable(node.name))
    if isinstance(node, SortedConstant):
        return SortedConstant(shim.term(node.name), node.sort)
    if isinstance(node, Constant):
        return Constant(shim.term(node.name))
    if isinstance(node, Function):
        return Function(shim.term(node.name),
                        tuple(_rewrite_casl_names(a, shim) for a in node.args))
    if isinstance(node, Atom):
        args = tuple(_rewrite_casl_names(a, shim) for a in node.args)
        if node.predicate == "=":
            # CASL's own built-in identity: not a declared symbol, nothing to
            # rename. A non-binary '=' (only reachable by hand-building the
            # Node; qml_validity_formula refuses one) is left as it is so that
            # fol.casl_export's exactly-two-terms check refuses it by name.
            return Atom("=", args)
        if node.predicate == "≠":
            # fol.casl_export has no rendering rule for "≠" at ANY arity (CASL
            # has no disequality connective), and fol.qml.qml_validity_formula
            # never leaves one in its output (it writes "≠" as "not (=)"), so a
            # "≠" atom reaches here only in a Node built by hand or parsed from
            # classical text and handed to sanitize_modal_identifiers directly,
            # which is documented as usable standalone. Falling through to the
            # ordinary predicate-renaming path below would silently relabel it
            # onto an arbitrary, unrelated legal identifier ('v_'), losing every
            # trace of "not equal" -- the silent approximation the project's own
            # refuse-loudly rule forbids. Refuse it instead, mirroring how
            # fol.casl_export.to_casl_spec already refuses the same atom when
            # handed it directly ("not a simple CASL identifier"), one layer
            # earlier and with a message that says what to write instead. This
            # sanitiser renames identifiers; it does not rewrite connectives.
            raise NotImplementedError(
                "hets.dol: sanitize_modal_identifiers cannot rename a '≠' atom "
                f"({node.to_unicode_str()}) -- CASL has no native disequality "
                "connective, so it would either become a meaningless renamed "
                "predicate (masking the lost 'not equal' meaning) or crash "
                "fol.casl_export's own identifier check. "
                "unicode_fol_kit.fol.qml.qml_validity_formula never leaves one "
                "in its output (it writes '≠' as 'not (=)' itself), so this "
                "atom did not arrive through it -- write "
                "'Not(Atom(\"=\", [a, b]))' instead of '≠' in the source formula."
            )
        return Atom(shim.predicate(node.predicate), args)
    return node.map_children(lambda c: _rewrite_casl_names(c, shim))


def sanitize_modal_identifiers(formula: Node) -> Node:
    """Return ``formula`` with every not-yet-legal CASL identifier — in
    practice, :mod:`unicode_fol_kit.fol.qml`'s own auto-generated fresh
    variables — renamed to a legal one, INJECTIVELY (two distinct source
    names never collapse onto one output name) and leaving every
    already-legal name untouched. Identity needs no renaming: a ``=`` atom is
    CASL's own native, rigid equality and is kept as it is (see the section
    comment above :func:`_casl_sanitize_stem`, point (2), for why that is also
    what ``fol.qml`` hands over). See :class:`_CaslIdentifierShim` for the exact
    algorithm and :func:`to_dol_library_from_modal`, which calls this
    automatically, for the intended entry point.

    Exposed publicly (rather than kept as a private helper of
    :func:`to_dol_library_from_modal`) so a caller can inspect the sanitised
    Node itself — e.g. to hand it to
    :func:`~unicode_fol_kit.fol.casl_export.formula_to_casl` /
    :func:`~unicode_fol_kit.fol.casl_export.to_casl_spec` directly instead of
    going through a whole DOL library, or to unit-test the renaming in
    isolation from CASL rendering.

    A caller who reaches this function directly, bypassing
    :func:`to_dol_library_from_modal` /
    :func:`~unicode_fol_kit.fol.qml.qml_validity_formula`, owns two details the
    translation would otherwise have settled: a ``≠`` atom must already be
    written ``Not(Atom("=", ...))``, because ``fol.qml`` does that rewrite and
    this function does not (it refuses a ``≠`` atom with
    :class:`NotImplementedError` instead of renaming it onto an unrelated
    identifier), and a ``=`` atom must be binary, because a non-binary one is
    passed through untouched for :func:`~unicode_fol_kit.fol.casl_export.to_casl_spec`
    to refuse.

    Raises:
        NotImplementedError: ``formula`` contains a ``≠`` atom, of any arity
            (CASL has no native rendering for it; ``fol.qml`` writes ``≠`` as
            the negation of ``=`` before a formula reaches this bridge).
    """
    return _rewrite_casl_names(formula, _CaslIdentifierShim(formula))


def to_dol_library_from_modal(
    formula: Node, *,
    mode: str = "constant", frame: str = "K", systems=None, bridges=None,
    temporal_closure: bool = True,
    spec_name: str = "ModalQuery", library_name: str = "ModalLib",
    default_sort: str = "Thing",
) -> str:
    """Render one quantified-modal-logic validity query as a complete DOL
    library, ready to upload to Hets — the official, tested composition of
    :func:`unicode_fol_kit.fol.qml.qml_validity_formula` (the modal-to-
    classical-FOL standard translation), :func:`sanitize_modal_identifiers`
    (the identifier fix the section comment above this class explains), and
    THIS module's own :func:`to_dol_library` / :class:`DolSpec` /
    :func:`~unicode_fol_kit.fol.casl_export.to_casl_spec` — no change to any
    of those three's own logic.

    Args:
        formula: the RAW modal formula (``Box``/``Diamond``/``Knows``/…,
            NOT yet translated) — the same argument
            :func:`~unicode_fol_kit.fol.qml.qml_is_valid` takes.
        mode, frame, systems, bridges, temporal_closure: forwarded verbatim to
            :func:`~unicode_fol_kit.fol.qml.qml_validity_formula` — see that
            function's and :func:`~unicode_fol_kit.fol.qml.qml_is_valid`'s own
            docstrings for what each selects (domain regime, alethic frame
            system, agent-indexed epistemic/doxastic systems, cross-family
            bridges, and the default-on temporal closure axioms).
        spec_name: the single emitted spec's name (one qml validity query is
            one self-contained CASL ``spec`` — there is nothing here to
            structure across several specs the way :func:`to_dol_library`'s
            general ``extends`` chaining supports).
        library_name: the DOL library's own name.
        default_sort: the ONE CASL sort the whole query is declared over —
            :func:`~unicode_fol_kit.fol.qml.qml_translate`'s embedding is
            SINGLE-sorted (worlds and objects share one FO sort, carved apart
            by the ``World``/``Object`` GUARD PREDICATES qml's own axioms
            assert — see ``fol.qml``'s module docstring), so there is no
            richer CASL sort structure to pass through here; this is exactly
            :func:`~unicode_fol_kit.fol.casl_export.to_casl_spec`'s own
            ``default_sort`` parameter, forwarded unchanged.

    The query is emitted as the spec's sole ``%implied`` CONJECTURE (no
    separate axioms — :func:`~unicode_fol_kit.fol.qml.qml_validity_formula`'s
    result is already the one closed implication ``⋀axioms ∧
    ⋀typing-facts → …`` in full), so ``client.prove(iri, spec_name)`` is what
    a caller runs against the uploaded library — the same shape
    ``tests/test_dol.py``'s own live tests already use.

    The translation binds world variables (``w``, ``v``, ``w0``, ...) and object variables
    (``x``, ...) of its own, and a user constant, function or predicate of the same
    spelling must not be read as one of them. :func:`~unicode_fol_kit.fol.casl_export.to_casl_spec`
    renames every bound variable that is spelled like a symbol of the spec, so the text
    reads back (through :func:`~unicode_fol_kit.fol.casl_import.parse_casl_spec`) as the
    translation up to the names of those variables, and a constant called ``w`` or ``w0``
    never changes the verdict.

    An object-language ``=`` atom in ``formula`` arrives from
    :func:`~unicode_fol_kit.fol.qml.qml_validity_formula` as the same binary
    identity over the object terms with no world argument (``≠`` as its
    negation), which is exactly CASL's own rigid, built-in ``=``: it is
    rendered infix, declared nowhere, and read back by
    :func:`~unicode_fol_kit.fol.casl_import.parse_casl_spec` as the identical
    atom. So identity is rigid on this route exactly as it is for
    :func:`~unicode_fol_kit.fol.qml.qml_is_valid` (``a = b → □(a = b)`` is a
    theorem here, in every frame), and the two routes agree on it. See the
    module-level section comment above :func:`_casl_sanitize_stem`, point (2).

    Raises:
        ValueError: any of :func:`~unicode_fol_kit.fol.qml.qml_axioms`'s /
            :func:`~unicode_fol_kit.fol.qml.qml_translate`'s own refusals
            (an unknown ``mode``/``frame``/``systems``/``bridges`` value, a
            frame requesting a bridge whose partner family the formula never
            mentions, or a ``=``/``≠`` atom that does not have exactly two
            terms), or (propagated, unchanged) any
            :func:`~unicode_fol_kit.fol.casl_export.to_casl_spec` /
            :func:`to_dol_library` refusal for ``spec_name`` / ``library_name``
            / ``default_sort``.
        NotImplementedError: ``frame`` needs a non-first-order condition
            (Löb/McKinsey/Grz — :func:`~unicode_fol_kit.fol.qml.qml_axioms`
            refuses those by name, pointing at the higher-order routes that
            DO carry them), or ``formula`` uses a construct
            :func:`~unicode_fol_kit.fol.qml.qml_translate` itself does not
            cover (``Until``/``Since``, the ``↓`` binder — see that module's
            own docstring for the exact scope: propositional + first-order
            modal, alethic/temporal/deontic/per-agent
            epistemic-doxastic/PAL).
    """
    node = qml_validity_formula(formula, mode=mode, frame=frame, systems=systems,
                                bridges=bridges, temporal_closure=temporal_closure)
    sanitized = sanitize_modal_identifiers(node)
    specs: "OrderedDict[str, DolSpec]" = OrderedDict()
    specs[spec_name] = DolSpec(axioms=[], conjectures=[sanitized],
                               default_sort=default_sort)
    return to_dol_library(library_name, specs)
