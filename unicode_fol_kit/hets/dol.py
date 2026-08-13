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
from ..fol.nodes import Node

__all__ = ["to_dol_library", "DolSpec"]


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
    CASL`` / one ``spec ... end`` block per entry, in ``specs`` iteration
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
