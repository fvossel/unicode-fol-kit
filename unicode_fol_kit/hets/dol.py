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

# The two equality-like predicates fol.qml's _st touches (see the section
# comment above, point (2)) and the fixed, informative stem each aliases to
# when _st has made it non-binary — "w" for "world-relativized", mirroring
# hol.isabelle_modal._PRED_ALIAS / hol.thf_modal's own "feq"/"fneq" aliasing
# of the identical predicates for the identical reason.
_EQUALITY_LIKE_PREDICATES = frozenset({"=", "≠"})
_EQ_ALIAS_STEM = {"=": "weq", "≠": "wneq"}


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


def _spec_block(spec_name: str, spec: DolSpec) -> str:
    """Render one ``spec <spec_name> = [<extends> then] ... end`` block by
    slicing the body out of a fresh :func:`~unicode_fol_kit.fol.casl_export.to_casl_spec`
    call — see the module docstring's "Reuse strategy" section."""
    body_text = to_casl_spec(
        list(spec.axioms), conjectures=list(spec.conjectures),
        spec_name=spec_name, default_sort=spec.default_sort,
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
        lines.append(_spec_block(spec_name, spec))
        if idx != len(items) - 1:
            lines.append("")
    return "\n".join(lines)


# =============================================================================
# Quantified modal logic -> CASL/DOL, over fol.qml's standard translation
# =============================================================================
#
# fol.qml.qml_validity_formula already lowers a modal formula to exactly the
# classical FOL fragment fol.casl_export accepts (see that function's own
# docstring) — this section's job is the TWO concrete gaps between
# "qml_validity_formula's output" and "a formula to_casl_spec will actually
# accept":
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
# (2) A world-relativized "=" / "≠" atom is not CASL's own binary identity.
# fol.qml's ``_st`` (unconditionally, by design — see that module's
# docstring) appends the current-world argument to EVERY atom it visits,
# including an object-language "=" or "≠" — so a genuinely binary user atom
# "a = b" comes out of qml_translate as a TERNARY atom ``=(a, b, w)``. That
# is not a spelling problem: CASL's own "=" is a FIXED, always-exactly-2-ary,
# RIGID built-in, while this atom denotes something else entirely — an
# uninterpreted, WORLD-RELATIVE relation, exactly the same non-rigid reading
# ``fol._fol_nodes.Atom.to_z3`` already gives it (only a genuinely 2-ary "="
# lowers to Z3's native equality; any other arity becomes an ordinary
# uninterpreted Z3 predicate named "=") and the same one
# ``semantics.kripke.satisfies_modal`` gives it (an Atom is looked up in the
# world's valuation like any other, with no special identity semantics) and
# the same one ``hol.isabelle_modal`` / ``hol.thf_modal`` give it (their own
# ``_PRED_ALIAS`` tables alias "="/"≠" to fresh, uninterpreted constant names
# — "feq"/"fneq" — for exactly this reason, in their own docstrings' words:
# "NOT primitive HOL `=`", "uninterpreted, world-relativized"). So THIS
# module follows the SAME, already-established kit-wide convention: a "="/"≠"
# atom that ``_st`` actually touched (arity != 2) is renamed to a fresh,
# legal, uninterpreted CASL predicate ("weq"/"wneq") by
# :meth:`_CaslIdentifierShim.equality_alias`, rather than being handed to
# CASL under the literal name "=" (which would crash casl_export's own
# arity-2 check). A genuinely 2-ary "=" atom (e.g. the WORLD identity
# ``w = v`` inside qml's own ``first_step`` axiom, or a user-formula equality
# that happened not to sit under any modal operator at all) is untouched by
# ``_st`` and is left exactly as CASL's own rigid "=" — see
# :func:`_rewrite_casl_names` for the arity-2 test that tells the two cases
# apart. A genuinely 2-ary "≠" is a THIRD case of its own: "≠" is never
# CASL-native at any arity (unlike "=", it has no fixed built-in meaning to
# fall back to at arity 2) and ``_st`` never produces one at arity 2 (a
# world-relativized "≠" is always 3-ary or more), so this case can only arise
# from a malformed pre-translation atom or a direct, non-modal call to
# :func:`sanitize_modal_identifiers` — it is refused loudly with
# :class:`NotImplementedError` (adversarial-review follow-up finding) rather
# than silently relabelled onto an arbitrary, unrelated legal identifier,
# which is what this module did before that follow-up review.
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

    Strips every LEADING underscore first — the one concrete shape this shim
    exists to fix (see the section comment above): every fresh name
    :mod:`unicode_fol_kit.fol.qml` itself ever generates is an ordinary,
    already-legal identifier once that convention is peeled off (``_w0`` ->
    ``w0``, ``_gz0`` -> ``gz0``, ``_a0`` -> ``a0``, …), so this one rule
    already fixes the measured blocker. What is left over is then
    defensively re-checked against CASL's own SIMPLE-ID grammar for any
    OTHER name this shim might be fed: a candidate that still does not start
    with an ASCII letter (all-underscore, or digit-leading) is prefixed with
    ``v``, and any remaining illegal character is folded to ``_``.
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

    Three separate namespaces, mirroring how CASL itself keeps these
    textually independent (a bound variable's occurrence is resolved by
    binding scope, not by clashing with an op/pred of the same spelling):
    ``variable`` (bound object/world variables), ``term`` (constants AND
    functions share ONE namespace here, mirroring
    :func:`~unicode_fol_kit.fol.casl_export.to_casl_spec`'s own merged
    ``ops`` declaration block and its ``_CONST_VS_FUNCTION`` dual-use
    refusal), and ``predicate`` (Atom predicate names; a GENUINELY BINARY
    ``=`` is never renamed — it is CASL's own native, rigid equality, not a
    declared symbol — but a ``=``/``≠`` atom of any OTHER arity, which only
    ever arises from ``fol.qml``'s ``_st`` world-relativizing an
    object-language equality/inequality, is not CASL's identity at all and
    IS renamed, through :meth:`equality_alias`, to a fresh uninterpreted
    predicate name shared by this namespace — see the section comment above
    point (2) for why, and :func:`_rewrite_casl_names` for where the arity
    check lives).

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
        self._var, self._var_used = {}, set()
        self._term, self._term_used = {}, set()
        self._pred, self._pred_used = {}, set()
        self._eq_alias: dict = {}  # (predicate, arity) -> resolved name; see equality_alias
        for n in formula.walk():
            if isinstance(n, Variable):
                self._seed(self._var, self._var_used, n.name)
            elif isinstance(n, (Constant, SortedConstant, Function)):
                self._seed(self._term, self._term_used, n.name)
            elif isinstance(n, Atom) and n.predicate not in _EQUALITY_LIKE_PREDICATES:
                self._seed(self._pred, self._pred_used, n.predicate)

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

    def equality_alias(self, predicate: str, arity: int) -> str:
        """Resolve a WORLD-RELATIVIZED ``=``/``≠`` atom (``arity != 2`` — see
        the section comment above point (2)) onto a legal, injective
        predicate name.

        Keyed by ``(predicate, arity)``, not by the plain predicate string
        :meth:`predicate` uses: every occurrence of the SAME
        ``(predicate, arity)`` pair within one formula denotes the SAME
        single uninterpreted relation (mirroring
        ``fol._fol_nodes.Z3Env.get_pred``'s own cache, keyed purely by name,
        which is exactly why every 3-ary ``=`` atom ``_st`` produces from one
        formula already collapses onto ONE Z3 predicate today — see
        ``Atom.to_z3``), so repeated calls for the same pair return the
        identical resolved name rather than minting a fresh one each time.

        Shares ``_pred_used`` (the SAME namespace :meth:`predicate` draws
        from — CASL has exactly one flat ``preds`` block, no separate
        "aliased" namespace) so a genuine user predicate that already
        happens to be spelled ``weq``/``wneq`` is never silently identified
        with this alias: that name is seeded into ``_pred_used`` by
        :meth:`__init__`'s ordinary whole-formula walk like any other
        already-legal predicate, so THIS alias is the one :func:`dedupe`
        bumps to ``weq_2`` on a collision, never the other way round.
        """
        key = (predicate, arity)
        if key in self._eq_alias:
            return self._eq_alias[key]
        stem = _EQ_ALIAS_STEM.get(predicate, "eqrel")
        result = dedupe(stem, self._pred_used)
        self._eq_alias[key] = result
        return result


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

    An Atom whose predicate is ``=``/``≠`` gets one of THREE treatments, by
    arity (see the section comment above point (2)): a genuinely 2-ary
    ``=`` is CASL's own rigid identity and is left under its literal name
    unconditionally; any OTHER arity of ``=``/``≠`` is what ``fol.qml``'s
    ``_st`` produces by appending a world argument to an object-language
    equality/inequality — not CASL's identity at all — and is renamed
    through :meth:`_CaslIdentifierShim.equality_alias` to a fresh,
    uninterpreted predicate exactly like any other symbol; a genuinely
    2-ary ``≠``, which CASL has no native rendering for at any arity and
    which ``_st`` never produces (a world-relativized ``≠`` is always 3-ary
    or more), is refused loudly with :class:`NotImplementedError` rather
    than silently relabelled onto an unrelated identifier — see that
    branch's own comment for why.
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
        if node.predicate in _EQUALITY_LIKE_PREDICATES and len(node.args) != 2:
            return Atom(shim.equality_alias(node.predicate, len(node.args)), args)
        if node.predicate == "=":
            return Atom("=", args)
        if node.predicate == "≠":
            # Adversarial-review finding (C6, follow-up): a genuinely 2-ary
            # "≠" reaches here UNTOUCHED by _st's world-relativization (which
            # always makes a "≠" it touches 3-ary or more — see the arity
            # check above) only via a malformed pre-translation atom (e.g. a
            # unary "≠") or a direct, non-modal call to this function on a
            # hand-built formula that never went through
            # fol.qml.qml_validity_formula at all — sanitize_modal_identifiers
            # is documented as usable standalone for exactly that. Before this
            # check, such an atom fell through to the ordinary
            # predicate-renaming path below and was silently relabelled onto
            # an arbitrary, unrelated legal identifier, losing every trace of
            # "not equal" — this violates the project's own refuse-loudly
            # rule just as much as approximating a fragment would, so it is
            # refused instead. fol.casl_export has no rendering rule for "≠"
            # at ANY arity (CASL has no native disequality connective) — a
            # genuinely 2-ary "≠" handed to
            # unicode_fol_kit.fol.casl_export.to_casl_spec directly, bypassing
            # this bridge, already refuses loudly today ("not a simple CASL
            # identifier"), so this mirrors that same refusal one layer
            # earlier, before the sanitiser can paper over it.
            raise NotImplementedError(
                "hets.dol: sanitize_modal_identifiers cannot rename a "
                "genuinely 2-ary '≠' atom -- CASL has no native disequality "
                "connective, at any arity, so this would either be a "
                "meaningless renamed predicate (masking the lost 'not "
                "equal' meaning) or crash fol.casl_export's own identifier "
                "check. This atom's arity was not changed by "
                "fol.qml's world-relativization (which always makes a "
                "world-relativized '≠' atom 3-ary or more), so it did not "
                "arrive through unicode_fol_kit.fol.qml.qml_validity_formula "
                "as intended -- write 'Not(Atom(\"=\", [a, b]))' instead of "
                "'≠' in the source formula, which world-relativizes and "
                "aliases (to 'weq') exactly like an ordinary '=' atom."
            )
        return Atom(shim.predicate(node.predicate), args)
    return node.map_children(lambda c: _rewrite_casl_names(c, shim))


def sanitize_modal_identifiers(formula: Node) -> Node:
    """Return ``formula`` with every not-yet-legal CASL identifier — in
    practice, :mod:`unicode_fol_kit.fol.qml`'s own auto-generated fresh
    variables — renamed to a legal one, INJECTIVELY (two distinct source
    names never collapse onto one output name) and leaving every
    already-legal name untouched; and every world-relativized ``=``/``≠``
    atom (arity != 2 — not CASL's own rigid, always-binary identity; see the
    section comment above :class:`_CaslIdentifierShim`, point (2)) renamed to
    a fresh, uninterpreted predicate the same way. See
    :class:`_CaslIdentifierShim` for the exact algorithm and
    :func:`to_dol_library_from_modal`, which calls this automatically, for
    the intended entry point.

    Exposed publicly (rather than kept as a private helper of
    :func:`to_dol_library_from_modal`) so a caller can inspect the sanitised
    Node itself — e.g. to hand it to
    :func:`~unicode_fol_kit.fol.casl_export.formula_to_casl` /
    :func:`~unicode_fol_kit.fol.casl_export.to_casl_spec` directly instead of
    going through a whole DOL library, or to unit-test the renaming in
    isolation from CASL rendering.

    A caller who reaches this function directly, bypassing
    :func:`to_dol_library_from_modal` /
    :func:`~unicode_fol_kit.fol.qml.qml_validity_formula` — e.g. to unit-test
    the renaming in isolation, as above — should pass a formula that has
    ALREADY been world-relativized by ``fol.qml``'s ``_st``, or else contains
    no ``=``/``≠`` atom of its own at all: a genuinely 2-ary ``≠`` atom that
    was never touched by world-relativization (only reachable this way, or
    via a malformed pre-translation atom, e.g. a unary ``≠``) is refused with
    :class:`NotImplementedError`, not silently renamed — see
    :func:`_rewrite_casl_names`'s own docstring and that branch's comment.

    Raises:
        NotImplementedError: ``formula`` contains a genuinely 2-ary ``≠``
            atom (CASL has no native rendering for ``≠`` at any arity, and
            world-relativization never produces one at arity 2).
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

    An object-language ``=``/``≠`` atom in ``formula`` is fully supported:
    :func:`sanitize_modal_identifiers` renames the world-relativized atom
    ``qml_translate`` produces for it to a fresh, uninterpreted CASL
    predicate (never CASL's own rigid, always-2-ary ``=``), matching how
    ``qml_is_valid``'s own Z3 check, ``satisfies_modal``, and
    ``hol.isabelle_modal``/``hol.thf_modal`` all already treat an
    object-language equality inside a modal context — see
    :mod:`unicode_fol_kit.hets.dol`'s own module-level section comment above
    :class:`_CaslIdentifierShim` for the full reasoning.

    Raises:
        ValueError: any of :func:`~unicode_fol_kit.fol.qml.qml_axioms`'s /
            :func:`~unicode_fol_kit.fol.qml.qml_translate`'s own refusals
            (an unknown ``mode``/``frame``/``systems``/``bridges`` value, or a
            frame requesting a bridge whose partner family the formula never
            mentions), or (propagated, unchanged) any
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
