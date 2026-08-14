"""A first-class, explicit ``Signature`` object: the kit's declared vocabulary.

A signature names what a formula is allowed to talk about — which predicate
symbols exist and at what arity, which functions, which constants, and (for
many-sorted formulas) which sorts and which argument/result positions are
typed. Today that vocabulary is checked in at least three independent, ad hoc
places:

* ``unicode_fol_kit.api.check(formula, signature={...})`` takes a LOOSE DICT
  (see "The api.check loose dict convention" below) and reports unknown
  symbols / arity mismatches with did-you-mean suggestions.
* ``unicode_fol_kit.eval.predicate_match`` extracts a per-namespace symbol
  INVENTORY (``(name, arity)`` sets for predicates/functions, a name set for
  constants) purely to realign two formulas' vocabularies against each other.
* ``unicode_fol_kit.fol.casl_export`` INFERS a signature (arities, and a
  per-argument-position sort via union-find) from a batch of formulas, purely
  as an internal step of emitting a CASL ``spec`` block.

Each of the three is correct for its own narrow purpose, but none of them is a
reusable, inspectable, first-class object — you cannot ask any of them "here
is a signature, does this OTHER formula conform to it", or serialise one to
disk, or merge two signatures from different sources. :class:`Signature` is
that missing object: predicates, functions, constants, and sorts as one
explicit, immutable value, with two ways to build one (from a dict, or by
inferring it from a batch of ASTs), a way to check an arbitrary formula
against it (:meth:`Signature.validate`), a way to combine two of them
(:meth:`Signature.merge`), and a stable JSON-compatible round-trip
(:meth:`Signature.to_dict` / :meth:`Signature.from_dict`).

DESIGN NOTE — the shared carrier, partially wired
---------------------------------------------------------
``api.check(formula, signature=Signature(...))`` IS wired: the facade
projects a :class:`Signature` onto its loose dict convention for the
classic unknown-symbol/arity diagnostics (keeping their did-you-mean
suggestions) and ADDITIONALLY reports this module's sort-mismatch messages
(``kind="sort_mismatch"`` entries) — see ``api.check``.
``predicate_match`` and ``casl_export`` still keep their own
independently-tested logic; rewriting them onto this carrier remains a
separate, deliberate step. The module stays self-contained and importable
on its own (``from unicode_fol_kit.fol.signature import Signature``).

The api.check loose dict convention (verified against unicode_fol_kit/api.py)
-------------------------------------------------------------------------------
``api.check``'s ``_signature_errors`` (api.py) reads a plain dict with up to
three OPTIONAL top-level keys — a key that is absent means that namespace is
UNCONSTRAINED (nothing is flagged unknown in it), not empty:

    {
        "predicates": {"Human": 1, "Mortal": 1},   # name -> arity ...
        "functions":  {"double": 1},                # ... or an iterable of
        "constants":  ["a", "b"],                    # allowed arities
    }

``predicates`` / ``functions`` map a name to EITHER a single ``int`` arity or
an iterable of allowed arities (``_signature_errors``'s ``allowed_arities``
helper does ``{value}`` for an int, ``set(value)`` otherwise); ``constants``
is a plain iterable of bare names. This is confirmed against
``tests/test_api.py`` (``test_check_signature_wrong_arity_and_suggestion``,
``test_check_passes_a_clean_sentence``), which construct exactly
``{"predicates": {"Human": 1, "Mortal": 1}, "constants": ["a", "b"]}``.
:meth:`Signature.from_dict` accepts this convention 1:1, EXCEPT for the
multi-arity-iterable case: ``api.check``'s dict describes a permissive
CONSTRAINT ("P may be used at arity 1 or 2"), whereas a ``Signature``
DECLARES what a symbol IS — it has no notion of "one of several arities". A
single-element iterable (``{"P": [1]}`` or ``{"P": {1}}``) is accepted as
just arity 1 (no information lost); an iterable naming more than one distinct
arity raises :class:`ValueError` naming the symbol and the arities, per the
kit's loud-refusal convention (see ``unicode_fol_kit.fol.casl_export``'s
arity-conflict checks for the same idea applied elsewhere).

The richer explicit dict form (what :meth:`Signature.to_dict` emits)
------------------------------------------------------------------------
:meth:`Signature.to_dict` always emits full-fidelity, self-describing JSON
(``json.dumps`` works directly on it) with a STABLE key order (sections in
declaration order, entries within a section sorted alphabetically by name —
independent of the ``Mapping``'s own internal order, so two signatures with
the same content always serialise byte-identically):

    {
        "predicates": {
            "Loves": {"arity": 2, "arg_sorts": ["Human", "Human"]},
            "Rain":  {"arity": 0, "arg_sorts": None},
        },
        "functions": {
            "fatherOf": {"arity": 1, "arg_sorts": ["Human"],
                         "result_sort": "Human"},
        },
        "constants": {"alice": "Human", "unsorted_thing": None},
        "sorts": ["Human"],
    }

:meth:`Signature.from_dict` recognises this rich per-entry shape (a ``dict``
with the required key ``"arity"`` for predicates/functions, an optional
``"arg_sorts"`` list, and — functions only — an optional ``"result_sort"``;
an unrecognised key inside such an entry, or a ``"result_sort"`` on a
PREDICATE entry, is refused with :class:`ValueError`) alongside the loose
convention above, distinguishing the two purely by the shape of each value
(``int``/iterable → loose; ``dict`` → rich). ``constants`` is rich when the
section itself is a ``dict`` (name -> sort-or-``None``) and loose when it is
a bare iterable of names (sort defaults to ``None`` for all of them). The
top-level ``"sorts"`` key (loose convention has none) supplies sort names not
otherwise implied by any declaration — e.g. a sort with no symbol
referencing it yet. Regardless of what ``"sorts"`` says, :attr:`Signature.sorts`
always also contains every sort mentioned by any ``arg_sorts`` / ``result_sort``
/ constant ``sort`` in the same dict — the two are unioned, never one silently
overriding the other. An unrecognised TOP-LEVEL key (a typo like
``"predicate"`` for ``"predicates"``) is refused rather than silently ignored.

``Signature`` constructed directly (the dataclass constructor, not
``from_dict``/``from_formulas``) does NOT perform this implied-sorts
derivation — ``sorts`` is then exactly what was passed in, verbatim
(frozenset-coerced). This keeps the plain constructor simple/predictable; the
two smart constructors below are where the derivation happens.

Signature.from_formulas — scope and what it deliberately does NOT infer
-----------------------------------------------------------------------
:meth:`Signature.from_formulas` walks a batch of ASTs and infers:

* every predicate's and every function's arity from how it is actually
  applied (an arity conflict ACROSS the batch — the same symbol used with two
  different argument counts somewhere in the batch — is refused with
  :class:`ValueError` naming the symbol and every arity seen);
* every constant's sort from its :class:`~unicode_fol_kit.fol.nodes.SortedConstant`
  occurrences (a plain, unsorted :class:`~unicode_fol_kit.fol.nodes.Constant`
  occurrence of the same name contributes no sort; a genuine conflict — the
  SAME constant name annotated with two different concrete sorts somewhere in
  the batch — is refused with :class:`ValueError`, the same spirit as the
  arity conflict above);
* the top-level :attr:`Signature.sorts` set, from every
  :class:`~unicode_fol_kit.fol.nodes.SortedQuantifier`'s and
  :class:`~unicode_fol_kit.fol.nodes.SortedConstant`'s own sort name (a plain,
  unsorted :class:`~unicode_fol_kit.fol.nodes.Quantifier` contributes nothing
  here — there is no ``default_sort`` concept in this module, unlike
  ``casl_export``);
* a name used BOTH as a bare constant (:class:`Constant` or
  :class:`SortedConstant`) and as a function application
  (:class:`~unicode_fol_kit.fol.nodes.Function`) anywhere in the batch is
  refused with :class:`ValueError` — mirroring
  ``unicode_fol_kit.fol.casl_export``'s identical refusal, for the identical
  reason: a signature declares at most one meaning per name per namespace,
  and "sometimes a ground term, sometimes an applied function" cannot be
  reconciled into one declaration.

It deliberately does **not** attempt ``casl_export``'s full per-ARGUMENT-POSITION
sort inference (the union-find over ``("pred"|"func", name, i)`` slots
propagating sort annotations through shared variables and equalities) — every
:class:`~unicode_fol_kit.fol.signature.PredicateDecl` / :class:`FunctionDecl`
built by ``from_formulas`` has ``arg_sorts=None`` (unsorted argument
positions), even when the formulas passed in would, under that fuller
algorithm, pin down concrete argument sorts. Duplicating that union-find here
would either diverge from ``casl_export``'s (already correct, already tested)
implementation or need to import its private internals; the task this module
was built for scopes ``from_formulas`` to arity + constant-sort + sort-name
inference only, leaving richer per-argument-position inference as a possible
FUTURE addition once/if a shared implementation is worth extracting. A
:class:`Signature` with unsorted argument positions is still fully usable —
``validate()`` simply never reports a sort mismatch on a position neither
side has pinned down (see below).

Signature.validate — violation vocabulary
------------------------------------------
:meth:`Signature.validate` walks a formula (recognising
:class:`~unicode_fol_kit.fol.nodes.Atom`,
:class:`~unicode_fol_kit.fol.nodes.Function`,
:class:`~unicode_fol_kit.fol.nodes.Constant`,
:class:`~unicode_fol_kit.fol.nodes.SortedConstant`,
:class:`~unicode_fol_kit.fol.nodes.Variable`,
:class:`~unicode_fol_kit.fol.nodes.Quantifier`, and
:class:`~unicode_fol_kit.fol.nodes.SortedQuantifier`; every OTHER node type —
modal/temporal operators, second-order quantifiers, Lambda/Application,
Count/Cardinality/Measure, the linear/Lambek/team-semantic connectives, …—
is transparently recursed into via the generic
:meth:`~unicode_fol_kit.fol.nodes.Node._child_nodes` traversal rather than
rejected, so an :class:`Atom` buried inside e.g. a modal box or a counting
quantifier is still checked; there is no ``casl_export``-style fragment
gate here) and returns a list of precise, human-readable violation strings —
one per OFFENDING OCCURRENCE (an undeclared symbol used twice in the formula
produces two separate messages, one per use site; this module never
deduplicates, so the length of the list is a genuine occurrence count, not
just a distinct-problem count). An empty list means the formula conforms.
Five violation shapes are produced, all following the pattern
``"<kind> '<symbol>' <detail>"``:

* ``undeclared predicate 'Foo' (arity 2)`` / ``undeclared function 'bar'
  (arity 1)`` / ``undeclared constant 'alice'`` — the symbol is not a key of
  the corresponding :attr:`Signature.predicates` / :attr:`functions` /
  :attr:`constants` mapping. The six comparison/equality predicates (``=``,
  ``≠``, ``<``, ``>``, ``≤``, ``≥``) and the four arithmetic functions (``+``,
  ``-``, ``*``, ``/``) are the kit's BUILT-IN operators, never user
  vocabulary (mirroring ``unicode_fol_kit.eval.validate``'s identical
  ``_BUILTIN_PREDS`` / ``_BUILTIN_FUNCS`` split — duplicated here as a
  small, independent, literal copy rather than an import, since this module
  is meant to become something ``eval.validate`` itself could eventually
  depend on, and depending the other way around would be backwards) — they
  are never flagged as undeclared, though their OWN arguments are still
  recursed into and checked.
* ``predicate 'Human' expects arity 1, used with arity 2`` / the ``function``
  equivalent — the symbol IS declared, but this occurrence's argument count
  does not match :attr:`PredicateDecl.arity` / :attr:`FunctionDecl.arity`.
* ``predicate 'Loves' argument 1 expects sort 'Human', got sort 'Animal'`` /
  the ``function`` equivalent — argument position ``i`` (1-based in the
  message) has a declared sort (``PredicateDecl.arg_sorts[i]`` /
  ``FunctionDecl.arg_sorts[i]``) that is not ``None``, AND the term actually
  passed there resolves to a DIFFERENT concrete sort (also not ``None``). A
  term's own concrete sort comes from: a :class:`Variable` bound by an
  enclosing :class:`SortedQuantifier` (that quantifier's sort; a plain
  :class:`Quantifier` or a free variable gives ``None`` — unknown, not a
  conflict); a :class:`SortedConstant`'s own inline sort annotation; a
  :class:`Constant`'s signature-declared :attr:`ConstantDecl.sort` (``None``
  if undeclared, or if declared unsorted); or a :class:`Function`
  application's declared :attr:`FunctionDecl.result_sort`. Per the task's
  own rule — repeated here because it is the crux of the whole check — **a
  ``None`` sort on EITHER side never conflicts**; only two BOTH-concrete,
  DIFFERENT sorts are a violation. This is a local, single-pass check (no
  union-find / propagation across the formula the way ``casl_export``'s sort
  inference does): it only ever compares a declared argument-position sort
  against whatever concrete sort the term passed there ALREADY carries by
  itself (from its own binder or its own signature entry), never propagates
  a sort backward onto an otherwise-unsorted variable.
* ``constant 'alice' is annotated sort 'Animal' here but declared sort
  'Human' in the signature`` — a :class:`SortedConstant` occurrence's own
  inline sort disagrees with that same name's :attr:`ConstantDecl.sort` in
  the signature (both concrete, both known, and different — the same "both
  sides concrete" rule as above, applied to a constant instead of an
  argument position).

Variables never need declaring (per the task's own framing) — a bare
:class:`Variable` is only ever looked up in the quantifier-scope environment
built while walking, never checked against :attr:`Signature.constants`; an
unbound (free) variable simply resolves to sort ``None`` and is silently
skipped, exactly like an unbound one under a plain :class:`Quantifier`.

Equality, immutability, and hashability
------------------------------------------
:class:`PredicateDecl` / :class:`FunctionDecl` / :class:`ConstantDecl` are
plain frozen dataclasses over only hashable fields (``str`` / ``int`` /
``Optional[str]`` / a coerced ``Tuple[Optional[str], ...]``), so they are
fully immutable AND hashable, and compare equal structurally.
:class:`Signature` itself is a frozen dataclass too (no attribute can be
reassigned after construction) whose three symbol-table fields are coerced
in ``__post_init__`` to :class:`types.MappingProxyType` (a read-only VIEW —
mutating the dict a caller originally passed in after construction does NOT
retroactively change the ``Signature``, since a fresh internal ``dict`` is
built and wrapped) and whose ``sorts`` field is coerced to a genuine
``frozenset``. Two ``Signature`` values compare equal iff every predicate,
function, constant, and sort matches — regardless of which constructor built
them (``from_dict``, ``from_formulas``, ``merge``, or the plain constructor
all funnel through the same ``__post_init__`` coercion, so construction path
never affects equality). ``Signature`` is NOT hashable, however (a
``MappingProxyType`` wrapping a ``dict`` is itself unhashable) — "frozen"
here means immutable-by-construction, not usable as a ``dict``/``set`` key.
"""

from dataclasses import dataclass, field, replace
from types import MappingProxyType
from typing import Dict, FrozenSet, Iterable, List, Mapping, Optional, Tuple

from .nodes import (
    Node, Atom, Function, Constant, SortedConstant, Variable,
    Quantifier, SortedQuantifier,
)

__all__ = ["Signature", "PredicateDecl", "FunctionDecl", "ConstantDecl"]


# Comparison/equality predicates and arithmetic functions are the kit's
# BUILT-IN operators, not user vocabulary that a Signature declares — see the
# module docstring's "violation vocabulary" section for why this is a small
# independent literal copy of unicode_fol_kit.eval.validate's identical sets
# rather than an import.
_BUILTIN_PREDS = frozenset({"=", "≠", "<", ">", "≤", "≥"})
_BUILTIN_FUNCS = frozenset({"+", "-", "*", "/"})


# =============================================================================
# Declaration dataclasses
# =============================================================================

def _require_arity(value, name: str, kind: str) -> int:
    """Return ``value`` coerced to a validated non-negative arity, or refuse.

    ``bool`` is explicitly rejected even though it is a ``int`` subclass in
    Python — an accidental ``True``/``False`` silently read as arity 1/0
    would be exactly the kind of silent-acceptance bug this kit's loud-
    refusal convention exists to catch.
    """
    if isinstance(value, bool) or not isinstance(value, int):
        raise TypeError(
            f"{kind} {name!r}: arity must be an int, got {type(value).__name__}."
        )
    if value < 0:
        raise ValueError(f"{kind} {name!r}: arity must be >= 0, got {value}.")
    return value


@dataclass(frozen=True)
class PredicateDecl:
    """A predicate symbol's declared shape.

    ``arg_sorts``, when given, must have exactly ``arity`` entries, each a
    sort name or ``None`` (that argument position's sort is left
    unconstrained — see the module docstring's "both sides concrete" rule).
    ``arg_sorts=None`` (the default) is the canonical "nothing declared"
    form for a fully unsorted predicate — NOT a tuple of ``arity`` ``None``
    entries;
    the two are equivalent to :meth:`Signature.validate` (neither ever
    conflicts with anything), but only the former is what
    :meth:`Signature.from_dict` / :meth:`Signature.from_formulas` produce.
    """

    name: str
    arity: int
    arg_sorts: Optional[Tuple[Optional[str], ...]] = None

    def __post_init__(self):
        object.__setattr__(
            self, "arity", _require_arity(self.arity, self.name, "PredicateDecl"))
        if self.arg_sorts is not None:
            coerced = tuple(self.arg_sorts)
            if len(coerced) != self.arity:
                raise ValueError(
                    f"PredicateDecl {self.name!r}: arg_sorts has {len(coerced)} "
                    f"entries but arity is {self.arity}."
                )
            object.__setattr__(self, "arg_sorts", coerced)


@dataclass(frozen=True)
class FunctionDecl:
    """A function symbol's declared shape: like :class:`PredicateDecl`, plus
    an optional ``result_sort`` for the sort of ``name(...)`` itself as a
    term (``None`` — the default — means the result sort is unconstrained)."""

    name: str
    arity: int
    arg_sorts: Optional[Tuple[Optional[str], ...]] = None
    result_sort: Optional[str] = None

    def __post_init__(self):
        object.__setattr__(
            self, "arity", _require_arity(self.arity, self.name, "FunctionDecl"))
        if self.arg_sorts is not None:
            coerced = tuple(self.arg_sorts)
            if len(coerced) != self.arity:
                raise ValueError(
                    f"FunctionDecl {self.name!r}: arg_sorts has {len(coerced)} "
                    f"entries but arity is {self.arity}."
                )
            object.__setattr__(self, "arg_sorts", coerced)
        if self.result_sort is not None and not isinstance(self.result_sort, str):
            raise TypeError(
                f"FunctionDecl {self.name!r}: result_sort must be a str or "
                f"None, got {type(self.result_sort).__name__}."
            )


@dataclass(frozen=True)
class ConstantDecl:
    """A constant symbol's declared shape: just a name and an optional sort
    (arity is implicitly 0 — a constant is never applied to arguments)."""

    name: str
    sort: Optional[str] = None

    def __post_init__(self):
        if self.sort is not None and not isinstance(self.sort, str):
            raise TypeError(
                f"ConstantDecl {self.name!r}: sort must be a str or None, "
                f"got {type(self.sort).__name__}."
            )


# =============================================================================
# Signature: the aggregate carrier
# =============================================================================

def _freeze_section(mapping, decl_cls, kind: str) -> Mapping:
    """Validate and wrap one symbol-table field as a read-only ``MappingProxyType``.

    Refuses (``TypeError``) a non-mapping input, a value of the wrong decl
    class, or (``ValueError``) a dict key that does not match that decl's own
    ``.name`` — the map key and the declaration's self-reported name must
    agree, or a lookup by key would silently return a decl that describes a
    DIFFERENT symbol.
    """
    if not isinstance(mapping, Mapping):
        raise TypeError(
            f"Signature: {kind}s must be a dict, got {type(mapping).__name__}."
        )
    out = {}
    for key, decl in mapping.items():
        if not isinstance(decl, decl_cls):
            raise TypeError(
                f"Signature: {kind} entry {key!r} must be a {decl_cls.__name__}, "
                f"got {type(decl).__name__}."
            )
        if decl.name != key:
            raise ValueError(
                f"Signature: {kind} dict key {key!r} does not match "
                f"{decl_cls.__name__}.name {decl.name!r}."
            )
        out[key] = decl
    return MappingProxyType(out)


@dataclass(frozen=True)
class Signature:
    """The kit's declared vocabulary: predicates, functions, constants, sorts.

    See the module docstring for the full account of every constructor and
    method below. All four fields default to empty (an "empty" signature
    declares NOTHING — every predicate/function/constant use in any formula
    is then reported as undeclared by :meth:`validate`; this is the strict,
    loud-refusal-by-default reading, not a permissive "anything goes" one).
    """

    predicates: Mapping[str, PredicateDecl] = field(default_factory=dict)
    functions: Mapping[str, FunctionDecl] = field(default_factory=dict)
    constants: Mapping[str, ConstantDecl] = field(default_factory=dict)
    sorts: FrozenSet[str] = field(default_factory=frozenset)

    def __post_init__(self):
        object.__setattr__(
            self, "predicates", _freeze_section(self.predicates, PredicateDecl, "predicate"))
        object.__setattr__(
            self, "functions", _freeze_section(self.functions, FunctionDecl, "function"))
        object.__setattr__(
            self, "constants", _freeze_section(self.constants, ConstantDecl, "constant"))
        object.__setattr__(self, "sorts", frozenset(self.sorts))

    # -------------------------------------------------------------------
    # Constructors
    # -------------------------------------------------------------------

    @staticmethod
    def from_dict(d: Mapping) -> "Signature":
        """Build a :class:`Signature` from a plain dict.

        Accepts both the ``api.check`` loose convention and the richer
        explicit form :meth:`to_dict` emits, per-section and per-entry — see
        the module docstring's "The api.check loose dict convention" and
        "The richer explicit dict form" sections for the exact shapes and
        the refusals (unknown top-level key, unknown key inside a rich
        entry, a multi-arity iterable naming more than one distinct arity,
        a wrong-typed value) this raises on.
        """
        if not isinstance(d, Mapping):
            raise TypeError(f"Signature.from_dict expects a dict, got {type(d).__name__}.")
        extra = set(d) - _ALLOWED_TOP_KEYS
        if extra:
            raise ValueError(
                f"Signature.from_dict: unexpected top-level key(s) {sorted(extra)} "
                f"(expected a subset of {sorted(_ALLOWED_TOP_KEYS)})."
            )
        predicates = _parse_symbol_section(
            d.get("predicates", {}), PredicateDecl, "predicate", has_result_sort=False)
        functions = _parse_symbol_section(
            d.get("functions", {}), FunctionDecl, "function", has_result_sort=True)
        constants = _parse_constants_section(d.get("constants", {}))

        declared_sorts = d.get("sorts", ())
        if not isinstance(declared_sorts, (list, tuple, set, frozenset)):
            raise TypeError(
                f"Signature.from_dict: 'sorts' must be an iterable of names, "
                f"got {type(declared_sorts).__name__}."
            )
        sorts = set(declared_sorts) | _implied_sorts(predicates, functions, constants)
        return Signature(predicates=predicates, functions=functions,
                         constants=constants, sorts=frozenset(sorts))

    @staticmethod
    def from_formulas(formulas: Iterable[Node]) -> "Signature":
        """Infer a :class:`Signature` from a batch of ASTs.

        See the module docstring's "Signature.from_formulas — scope and what
        it deliberately does NOT infer" section for exactly what this does
        (arities, constant sorts, the ``sorts`` set) and does not (per-
        argument-position sort inference) attempt, and for the two refusals
        (a cross-formula arity or constant-sort conflict; a name used both
        as a constant and as a function) it raises :class:`ValueError` on.
        """
        pred_arities: Dict[str, set] = {}
        func_arities: Dict[str, set] = {}
        const_sorts: Dict[str, set] = {}
        const_names: set = set()
        func_names: set = set()
        literal_sorts: set = set()

        def walk_formula(node: Node) -> None:
            if isinstance(node, Atom):
                if node.predicate not in _BUILTIN_PREDS:
                    pred_arities.setdefault(node.predicate, set()).add(len(node.args))
                for a in node.args:
                    walk_term(a)
                return
            if isinstance(node, SortedQuantifier):
                literal_sorts.add(node.sort)
                walk_formula(node.formula)
                return
            for child in node._child_nodes():
                walk_formula(child)

        def walk_term(node: Node) -> None:
            if isinstance(node, SortedConstant):
                const_names.add(node.name)
                const_sorts.setdefault(node.name, set()).add(node.sort)
                literal_sorts.add(node.sort)
                return
            if isinstance(node, Constant):
                const_names.add(node.name)
                return
            if isinstance(node, Function):
                if node.name not in _BUILTIN_FUNCS:
                    func_arities.setdefault(node.name, set()).add(len(node.args))
                    func_names.add(node.name)
                for a in node.args:
                    walk_term(a)
                return
            # TERM nodes that carry a genuine FORMULA field (the counting
            # comparisons' set builders): route it back through the formula
            # walker — otherwise every predicate used only inside a
            # |{v : …}| body would be invisible (review-confirmed gap).
            formula_field = getattr(node, "formula", None)
            if formula_field is not None:
                walk_formula(formula_field)
                for child in node._child_nodes():
                    if child is not formula_field:
                        walk_term(child)
                return
            for child in node._child_nodes():
                walk_term(child)

        for f in formulas:
            walk_formula(f)

        clash = const_names & func_names
        if clash:
            name = sorted(clash)[0]
            raise ValueError(
                f"Signature.from_formulas: {name!r} is used both as a constant "
                "and as a function across the given formulas — a Signature "
                "cannot declare one name in both namespaces from usage alone."
            )

        predicates = {}
        for name, arities in pred_arities.items():
            if len(arities) > 1:
                raise ValueError(
                    f"Signature.from_formulas: predicate {name!r} used with "
                    f"conflicting arities {tuple(sorted(arities))}."
                )
            predicates[name] = PredicateDecl(name, next(iter(arities)))

        functions = {}
        for name, arities in func_arities.items():
            if len(arities) > 1:
                raise ValueError(
                    f"Signature.from_formulas: function {name!r} used with "
                    f"conflicting arities {tuple(sorted(arities))}."
                )
            functions[name] = FunctionDecl(name, next(iter(arities)))

        constants = {}
        for name in const_names:
            seen = const_sorts.get(name, set())
            if len(seen) > 1:
                raise ValueError(
                    f"Signature.from_formulas: constant {name!r} used with "
                    f"conflicting sorts {tuple(sorted(seen))}."
                )
            constants[name] = ConstantDecl(name, next(iter(seen)) if seen else None)

        return Signature(predicates=predicates, functions=functions,
                         constants=constants, sorts=frozenset(literal_sorts))

    # -------------------------------------------------------------------
    # Serialisation
    # -------------------------------------------------------------------

    def to_dict(self) -> dict:
        """Render this signature as the rich, JSON-compatible, key-order-stable dict.

        See the module docstring's "The richer explicit dict form" section
        for the exact shape. ``Signature.from_dict(sig.to_dict())`` always
        reconstructs a :class:`Signature` equal to ``sig``.
        """
        predicates = {
            name: {
                "arity": decl.arity,
                "arg_sorts": list(decl.arg_sorts) if decl.arg_sorts is not None else None,
            }
            for name, decl in sorted(self.predicates.items())
        }
        functions = {
            name: {
                "arity": decl.arity,
                "arg_sorts": list(decl.arg_sorts) if decl.arg_sorts is not None else None,
                "result_sort": decl.result_sort,
            }
            for name, decl in sorted(self.functions.items())
        }
        constants = {name: decl.sort for name, decl in sorted(self.constants.items())}
        return {
            "predicates": predicates,
            "functions": functions,
            "constants": constants,
            "sorts": sorted(self.sorts),
        }

    # -------------------------------------------------------------------
    # Checking
    # -------------------------------------------------------------------

    def validate(self, formula: Node) -> List[str]:
        """Return the list of vocabulary violations ``formula`` commits against
        this signature; an empty list means ``formula`` conforms.

        See the module docstring's "Signature.validate — violation
        vocabulary" section for the exact message shapes and the walk's
        scope (which node types are specially recognised, and how every
        other node type is transparently recursed through rather than
        rejected).
        """
        violations: List[str] = []
        _walk_formula(formula, {}, self, violations)
        return violations

    # -------------------------------------------------------------------
    # Combining
    # -------------------------------------------------------------------

    def merge(self, other: "Signature") -> "Signature":
        """Return the union of ``self`` and ``other``.

        Every predicate/function/constant/sort present in either input is
        present in the result. A symbol declared by BOTH sides with
        DIFFERING declarations (different arity, ``arg_sorts``,
        ``result_sort``, or ``sort``) is a genuine conflict and raises
        :class:`ValueError` naming the symbol and both declarations; a
        symbol declared identically by both sides merges without complaint.
        Sorts merge with a plain set union (a bare sort NAME can never
        itself conflict with another).
        """
        predicates = _merge_section(self.predicates, other.predicates, "predicate")
        functions = _merge_section(self.functions, other.functions, "function")
        constants = _merge_section(self.constants, other.constants, "constant")
        return Signature(predicates=predicates, functions=functions,
                         constants=constants, sorts=self.sorts | other.sorts)


# =============================================================================
# from_dict helpers
# =============================================================================

_ALLOWED_TOP_KEYS = frozenset({"predicates", "functions", "constants", "sorts"})


def _parse_symbol_section(section, decl_cls, kind: str, has_result_sort: bool) -> dict:
    """Parse one ``predicates``/``functions`` section, loose OR rich per entry."""
    if not isinstance(section, Mapping):
        raise TypeError(
            f"Signature.from_dict: {kind}s section must be a dict, got "
            f"{type(section).__name__}."
        )
    allowed_keys = {"arity", "arg_sorts", "result_sort"} if has_result_sort \
        else {"arity", "arg_sorts"}
    out = {}
    for name, value in section.items():
        if isinstance(value, dict):
            if "arity" not in value:
                raise ValueError(
                    f"Signature.from_dict: {kind} {name!r} rich entry is "
                    "missing the required key 'arity'."
                )
            extra = set(value) - allowed_keys
            if extra:
                raise ValueError(
                    f"Signature.from_dict: {kind} {name!r} entry has "
                    f"unexpected key(s) {sorted(extra)}."
                )
            arity = _require_arity(value["arity"], name, kind)
            raw_arg_sorts = value.get("arg_sorts")
            arg_sorts = tuple(raw_arg_sorts) if raw_arg_sorts is not None else None
            result_sort = value.get("result_sort") if has_result_sort else None
        elif isinstance(value, (list, tuple, set, frozenset)):
            arities = sorted({_require_arity(v, name, kind) for v in value})
            if not arities:
                raise ValueError(
                    f"Signature.from_dict: {kind} {name!r} has an empty arity set."
                )
            if len(arities) > 1:
                raise ValueError(
                    f"Signature.from_dict: {kind} {name!r} lists multiple "
                    f"allowed arities {tuple(arities)} — a Signature declares "
                    "exactly one arity per symbol (api.check's multi-arity "
                    "CONSTRAINT has no Signature DECLARATION equivalent)."
                )
            arity = arities[0]
            arg_sorts = None
            result_sort = None
        else:
            arity = _require_arity(value, name, kind)
            arg_sorts = None
            result_sort = None
        kwargs = {"name": name, "arity": arity, "arg_sorts": arg_sorts}
        if has_result_sort:
            kwargs["result_sort"] = result_sort
        out[name] = decl_cls(**kwargs)
    return out


def _parse_constants_section(section) -> dict:
    """Parse the ``constants`` section: a dict (rich, name -> sort-or-None)
    or a bare iterable of names (loose, every constant unsorted)."""
    if isinstance(section, Mapping):
        out = {}
        for name, sort in section.items():
            out[name] = ConstantDecl(name, sort)
        return out
    if isinstance(section, (list, tuple, set, frozenset)):
        out = {}
        for name in section:
            if not isinstance(name, str):
                raise TypeError(
                    f"Signature.from_dict: constants entries must be strings, "
                    f"got {type(name).__name__}."
                )
            out[name] = ConstantDecl(name, None)
        return out
    raise TypeError(
        f"Signature.from_dict: constants section must be a dict or an "
        f"iterable of names, got {type(section).__name__}."
    )


def _implied_sorts(predicates: dict, functions: dict, constants: dict) -> set:
    """Every sort name mentioned by any parsed decl's arg_sorts/result_sort/sort."""
    sorts = set()
    for decl in predicates.values():
        if decl.arg_sorts:
            sorts.update(s for s in decl.arg_sorts if s is not None)
    for decl in functions.values():
        if decl.arg_sorts:
            sorts.update(s for s in decl.arg_sorts if s is not None)
        if decl.result_sort is not None:
            sorts.add(decl.result_sort)
    for decl in constants.values():
        if decl.sort is not None:
            sorts.add(decl.sort)
    return sorts


# =============================================================================
# merge helper
# =============================================================================

def _normalized_decl(decl):
    """A decl with vacuous sort annotations folded away, for comparison.

    ``arg_sorts=None`` and ``arg_sorts=(None,) * arity`` are behaviourally
    identical to :meth:`Signature.validate` (neither ever conflicts with
    anything), so :func:`_merge_section` must treat them as the SAME
    declaration — plain dataclass equality does not (review-confirmed:
    ``from_dict({'arg_sorts': [None]})`` vs a bare decl raised a spurious
    merge conflict).
    """
    arg_sorts = getattr(decl, "arg_sorts", None)
    if arg_sorts is not None and all(s is None for s in arg_sorts):
        decl = replace(decl, arg_sorts=None)
    return decl


def _merge_section(a: Mapping, b: Mapping, kind: str) -> dict:
    out = dict(a)
    for name, decl in b.items():
        if name in out and _normalized_decl(out[name]) != _normalized_decl(decl):
            raise ValueError(
                f"Signature.merge: conflicting {kind} declaration for "
                f"{name!r}: {out[name]!r} vs {decl!r}."
            )
        out.setdefault(name, decl)
    return out


# =============================================================================
# validate() helpers — a single-pass, generically-recursive walk
# =============================================================================

def _walk_formula(node: Node, env: Dict[str, Optional[str]], sig: Signature,
                  violations: List[str]) -> None:
    """Walk a formula node, threading the sorted-variable environment.

    Recognises :class:`Atom` (checked via :func:`_check_atom`),
    :class:`SortedQuantifier` and :class:`Quantifier` (both extend ``env``
    for their body — sorted with a concrete sort, plain with ``None``,
    correctly shadowing an outer binding of the same variable name); every
    other node type is transparently recursed into via
    ``node._child_nodes()`` with the SAME ``env`` — this is what lets an
    ``Atom`` nested under a modal/temporal/counting/… node still get
    checked, without this module needing to know about every node class in
    the kit.
    """
    if isinstance(node, Atom):
        _check_atom(node, env, sig, violations)
        return
    if isinstance(node, SortedQuantifier):
        new_env = dict(env)
        new_env[node.variable.name] = node.sort
        _walk_formula(node.formula, new_env, sig, violations)
        return
    if isinstance(node, Quantifier):
        new_env = dict(env)
        new_env[node.variable.name] = None
        _walk_formula(node.formula, new_env, sig, violations)
        return
    for child in node._child_nodes():
        _walk_formula(child, env, sig, violations)


def _check_atom(node: Atom, env: Dict[str, Optional[str]], sig: Signature,
                violations: List[str]) -> None:
    """Check one Atom occurrence: declaredness, arity, and per-argument sort."""
    arity = len(node.args)
    if node.predicate in _BUILTIN_PREDS:
        for arg in node.args:
            _term_sort(arg, env, sig, violations)
        return
    decl = sig.predicates.get(node.predicate)
    if decl is None:
        violations.append(f"undeclared predicate '{node.predicate}' (arity {arity})")
        for arg in node.args:
            _term_sort(arg, env, sig, violations)
        return
    if decl.arity != arity:
        violations.append(
            f"predicate '{node.predicate}' expects arity {decl.arity}, used "
            f"with arity {arity}"
        )
    for i, arg in enumerate(node.args):
        arg_sort = _term_sort(arg, env, sig, violations)
        if decl.arg_sorts is not None and i < len(decl.arg_sorts):
            declared = decl.arg_sorts[i]
            if declared is not None and arg_sort is not None and declared != arg_sort:
                violations.append(
                    f"predicate '{node.predicate}' argument {i + 1} expects "
                    f"sort '{declared}', got sort '{arg_sort}'"
                )


def _term_sort(node: Node, env: Dict[str, Optional[str]], sig: Signature,
               violations: List[str]) -> Optional[str]:
    """Check one term occurrence and return its resolved concrete sort (or
    ``None`` if unknown/unsorted) — see the module docstring for the rules
    determining a term's concrete sort per node kind."""
    if isinstance(node, Variable):
        return env.get(node.name)
    if isinstance(node, SortedConstant):
        decl = sig.constants.get(node.name)
        if decl is None:
            violations.append(f"undeclared constant '{node.name}'")
        elif decl.sort is not None and decl.sort != node.sort:
            violations.append(
                f"constant '{node.name}' is annotated sort '{node.sort}' "
                f"here but declared sort '{decl.sort}' in the signature"
            )
        return node.sort
    if isinstance(node, Constant):
        decl = sig.constants.get(node.name)
        if decl is None:
            violations.append(f"undeclared constant '{node.name}'")
            return None
        return decl.sort
    if isinstance(node, Function):
        arity = len(node.args)
        if node.name in _BUILTIN_FUNCS:
            for arg in node.args:
                _term_sort(arg, env, sig, violations)
            return None
        decl = sig.functions.get(node.name)
        if decl is None:
            violations.append(f"undeclared function '{node.name}' (arity {arity})")
            for arg in node.args:
                _term_sort(arg, env, sig, violations)
            return None
        if decl.arity != arity:
            violations.append(
                f"function '{node.name}' expects arity {decl.arity}, used "
                f"with arity {arity}"
            )
        for i, arg in enumerate(node.args):
            arg_sort = _term_sort(arg, env, sig, violations)
            if decl.arg_sorts is not None and i < len(decl.arg_sorts):
                declared = decl.arg_sorts[i]
                if declared is not None and arg_sort is not None and declared != arg_sort:
                    violations.append(
                        f"function '{node.name}' argument {i + 1} expects "
                        f"sort '{declared}', got sort '{arg_sort}'"
                    )
        return decl.result_sort
    # A TERM node with a genuine FORMULA field (Cardinality/SortedCardinality
    # set builders): the buried Atoms must go back through the FORMULA
    # walker or they escape declaredness/arity/sort checking entirely
    # (review-confirmed: '|{v : Votes(x, v)}| > …' validated as clean
    # against a Signature declaring Votes at the wrong arity).
    formula_field = getattr(node, "formula", None)
    if formula_field is not None:
        _walk_formula(formula_field, env, sig, violations)
        for child in node._child_nodes():
            if child is not formula_field:
                _term_sort(child, env, sig, violations)
        return None
    for child in node._child_nodes():
        _term_sort(child, env, sig, violations)
    return None
