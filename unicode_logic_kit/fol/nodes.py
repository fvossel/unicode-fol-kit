"""Public re-export hub for all AST node classes and utilities.

Classical FOL definitions live in _fol_nodes.py.
MSFL extension (sorted quantifiers/constants, Łukasiewicz operators, to_fol) lives in _msfl_nodes.py.

STABLE PUBLIC API
------------------
Two things exported from this module are STABLE PUBLIC API, in the sense
that a downstream consumer is meant to build directly on them rather than
reaching past them into the modules underneath (``_fol_nodes.py``,
``_msfl_nodes.py``, …, all underscore-prefixed precisely because THEY are
not the contract):

  * every node class's CONSTRUCTOR — ``Variable``, ``Constant``, ``Number``,
    ``Function``, ``Atom``, ``Not``, ``And``, ``Or``, ``Xor``, ``Implies``,
    ``Iff``, ``Quantifier``, ``Count``, ``Measure``, ``Cardinality``,
    ``Contrast``, and every MSFL/modal/hybrid/team/linear/lambek/
    second-order class re-exported below — meaning field names, field
    order, and what a positional or keyword argument means;
  * ``Node.to_unicode_str()``, meaning both that it renders a parseable
    Unicode formula string, and that the string it renders parses back
    (via the matching ``MSFLParser`` mode) to a structurally equal node —
    the roundtrip guarantee documented on ``to_unicode_str`` itself and
    exercised by the FOL-fragment roundtrip test suite. A constant whose name
    does not read back as that constant when written bare (``k2`` is a
    variable, ``Alice`` a predicate, ``G-910`` no term) is written in single
    quotes, ``'k2'``, so that the text reads back for every constant that has
    a text; a constant that reads back bare (``socrates``) is written as it
    always was.

A consumer that builds nodes by calling these constructors directly and
serialises them back to text via ``to_unicode_str`` — the way a mutation-
search loop assembling candidate formulas and shipping them across a
process boundary would — is standing on committed API, not on an
implementation detail that happens to work today.

What "stable" commits this kit to: a node class is not renamed, its
dataclass fields are not reordered or reinterpreted, and ``to_unicode_str``'s
grammar does not change in a way that breaks the roundtrip for an existing
node shape, without that change being called out explicitly in
``CHANGELOG.md`` — never folded silently into an unrelated change. This
project is pre-1.0 (see ``CHANGELOG.md``'s header: "a minor release MAY
contain breaking changes"), so a break is not impossible — but for these
names it is never an accident. ``Node.__eq__`` / ``__hash__`` / ``repr`` /
``to_dict`` / ``from_dict`` are part of the same commitment: unchanged for
every node already registered in ``NODE_CLASSES``.

What it does NOT commit to: anything not re-exported here or in
``fol/__init__.py``'s ``__all__`` — internal helpers, the exact
``_child_nodes()``/``map_children`` traversal order, or any
underscore-prefixed name in any ``_*_nodes.py`` module. The separate, PATH
convention ``replace_at``/``node_at``/``fol.spans.traverse`` agree on
(``_child_nodes()`` order, except a ``Quantifier``'s bound variable is
excluded — see ``_fol_nodes.py``'s "Public tree editing" section and
``fol/spans.py``'s module docstring) is its own narrower commitment, scoped
to those three functions.
"""

from ._fol_nodes import (
    Z3Env,
    Node,
    Variable, Constant, Number, Function,
    Atom, Not, And, Or, Xor, Implies, Iff, Quantifier,
    Count, Measure, Cardinality, Contrast,
    NODE_CLASSES,
    FOLTransformer,
    node_at, replace_at,
)
from ._msfl_nodes import (
    SortedQuantifier, SortedConstant,
    SortedCount, SortedCardinality,
    WeakConjunction, WeakDisjunction,
    StrongConjunction, StrongDisjunction,
    LukNegation, LukImplication, LukEquivalence,
    LambdaVar, Lambda, Application,
    free_variables,
    substitute, beta_reduce, ReductionLimitError,
    eta_reduce, beta_eta_normalize,
    resolve_lambda_scope,
    to_fol,
    nonempty_sort_axioms,
    sort_membership_axioms,
    sort_axioms,
    subsort_axioms,
    signature_axioms,
)
from ._modal_nodes import (
    Box, Diamond, Knows, Believes, Says, Wants,
    EverybodyKnows, DistributedKnowledge, CommonKnowledge,
    Always, Eventually, Next, Until,
    Historically, Once, Previous, Since,
    Obligatory, Permitted,
    Would, Might,
    Announce, AnnounceDiamond,
)
from ._so_nodes import SecondOrderQuantifier
from ._hybrid_nodes import Nominal, At, Down
from ._team_nodes import Dependence, SlashedExists
from ._linear_nodes import (
    Tensor, With, OPlus, LinearImplies, OfCourse, One, Top, Zero,
)
from ._lambek_nodes import Product, Under, Over
# Imported LAST: _ho_nodes clones the modal and second-order parser
# registrations into the two third-order grammar modes, so every module
# that registers an operator for those modes -- _hybrid_nodes included --
# has to have run first.
from ._ho_nodes import (
    PredicateTerm, Signatures, analyse_signatures, MixedSlotError, NestedPropertySlotError,
    _clone_parser_ops,
)
# PARSER_OPS/ParserOp/parser_ops_for_mode: needed below by
# _clone_parser_ops_sorted, the exclusion-aware sibling of _ho_nodes'
# _clone_parser_ops that assembles the two new SORTED+modal/second-order
# grammar modes (see that function's docstring for why plain _clone_parser_ops
# is not enough here).
from ._fol_nodes import PARSER_OPS, ParserOp, parser_ops_for_mode

# The two third-order grammar modes are their base modes' operator sets over a
# widened argument layer, so they are assembled by CLONING rather than by
# re-registering ~40 operators that would then drift. It happens here, and
# happens last, because it can only be correct once every module that registers
# an operator for "modal" or "second_order" has been imported -- which, at this
# point in this file, they all have.
_clone_parser_ops("third_order", ["second_order"])
_clone_parser_ops("third_order_modal", ["modal", "second_order"])


# =========================
# many_sorted + modal / second_order grammar modes (C3)
# =========================
#
# "modal_sorted" (MSFLParser(modal=True, many_sorted=True)) and "so_sorted"
# (MSFLParser(second_order=True, many_sorted=True)) are assembled the same
# CLONING way the third-order modes above are -- but plain _clone_parser_ops
# is not quite enough here, for a reason the third-order clones never hit:
# "modal" and "second_order" each register the UNSORTED individual quantifier
# (Quantifier, rule alias "quantifier_") and the unsorted counting quantifier
# (Count, "count_"), while "msfol" registers the SORTED equivalents
# (SortedQuantifier "sorted_quantifier_", SortedCount "sorted_count_") under
# DIFFERENT rule aliases / grammar fragments. _clone_parser_ops's dedup key is
# (level, rule_alias, grammar, only_name) -- since the sorted and unsorted
# forms differ on every one of those, a bare clone of ["modal", "msfol"]
# would keep BOTH, so ``MSFLParser(modal=True, many_sorted=True)`` would
# accept an UNSORTED ``∀x P(x)`` right alongside ``∀x:S P(x)`` -- silently
# reintroducing the unsorted quantifier many_sorted is supposed to forbid
# (exactly like plain "msfol" forbids it today). _clone_parser_ops_sorted
# below is _ho_nodes._clone_parser_ops with one addition: ops whose rule_alias
# names an unsorted binder are skipped, so the sorted mode ends up with
# EXACTLY "msfol"'s quantifier/count/constant/cardinality forms plus every
# modal / second-order operator, and nothing double-registered (the classical
# connectives and Contrast register identically -- same level/rule_alias/
# grammar/only_name -- for "modal"/"second_order" and "msfol", so the
# ordinary dedup already collapses those to one copy each).
_UNSORTED_BINDER_ALIASES = frozenset({"quantifier_", "count_"})


def _clone_parser_ops_sorted(target: str, sources) -> None:
    """Like ``_ho_nodes._clone_parser_ops(target, sources)``, but never clones
    an unsorted quantifier/counting-quantifier binding (see the module comment
    above). ``sources`` should list the SORTED source mode ("msfol") before
    the modal/second-order one, so a genuine grammar conflict — should one
    ever appear — is reported against the sorted form's own shape first;
    today no such conflict exists, since every non-binder op the two source
    modes share registers identically and is deduped as usual.
    """
    seen = set()
    for source in sources:
        for op in parser_ops_for_mode(source):
            if op.rule_alias in _UNSORTED_BINDER_ALIASES:
                continue
            key = (op.level, op.rule_alias, op.grammar, op.only_name)
            if key in seen:
                continue
            seen.add(key)
            PARSER_OPS.append(ParserOp(
                target, op.level, op.terminal_name, op.terminal_def,
                op.grammar, op.rule_alias, op.transform, op.node_class,
                op.only_name))


_clone_parser_ops_sorted("modal_sorted", ["msfol", "modal"])
_clone_parser_ops_sorted("so_sorted", ["msfol", "second_order"])

# build_grammar (fol/_fol_nodes.py) also needs two pieces of per-mode
# configuration that are NOT operator-specific and therefore not covered by
# PARSER_OPS cloning above: whether SORT is a recognised terminal / bare
# constants must carry a sort annotation (_SORTED_MODES), and the terminal
# import list (_MODE_TERMINAL_IMPORTS, indexed with `[mode]` -- a missing key
# is a hard KeyError). Both live in fol/_fol_nodes.py, which this change does
# not own/edit; they are extended here, at runtime, the same way
# _clone_parser_ops_sorted above extends PARSER_OPS (another registry that
# also lives in _fol_nodes.py) -- module-level registries, not the module's
# own source, so this is additive rather than a hack around ownership. Every
# other mode-keyed dict build_grammar reads (_MODE_TERM_EXTRA,
# _MODE_ATOM_ARGS, _MODE_ATOM_EXTRA) is read with ``.get(mode, default)``, so
# the two sorted modes correctly fall back to "no extra term form" / "plain
# termlist" / "no extra atom form" without needing an entry.
from . import _fol_nodes as _fn  # noqa: E402  (after the registrations above)

_fn._SORTED_MODES = _fn._SORTED_MODES | {"modal_sorted", "so_sorted"}
_fn._MODE_TERMINAL_IMPORTS.setdefault("modal_sorted", _fn._MODE_TERMINAL_IMPORTS["modal"])
_fn._MODE_TERMINAL_IMPORTS.setdefault("so_sorted", _fn._MODE_TERMINAL_IMPORTS["second_order"])


# =========================
# The other classical combinations of order, modal operators and sorts
# =========================
#
# Three things are chosen independently of each other in a classical mode: the
# order (first, second, third), whether the modal family is there, and whether
# the individual binders and constants carry sorts. That is twelve modes, and
# the eight above and in _fol_nodes.py leave four: second order with the modal
# family ("second_order_modal"), the same over sorted individuals
# ("second_order_modal_sorted"), and third order over sorted individuals, without
# and with the modal family ("third_order_sorted", "third_order_modal_sorted").
#
# Each is cloned from the same sources as its neighbours, so it accepts what
# they accept and nothing of its own:
#   - "second_order_modal" has the operators of "third_order_modal" and the plain
#     argument layer (``termlist``), so a predicate name in argument position
#     stays the syntax error it is at second order;
#   - a sorted mode takes "msfol" first and drops the unsorted binders, like
#     "modal_sorted" and "so_sorted";
#   - a third-order mode takes the argument layer of "third_order" (``hoarglist``).
# The predicate quantifier is unsorted in every one of them: ``∀P`` ranges over
# the relations on the whole domain, and a sort restricts an individual binder.
_clone_parser_ops("second_order_modal", ["modal", "second_order"])
_clone_parser_ops_sorted("second_order_modal_sorted", ["msfol", "modal", "second_order"])
_clone_parser_ops_sorted("third_order_sorted", ["msfol", "second_order"])
_clone_parser_ops_sorted("third_order_modal_sorted", ["msfol", "modal", "second_order"])

for _mode in ("second_order_modal", "second_order_modal_sorted",
              "third_order_sorted", "third_order_modal_sorted"):
    _fn._MODE_TERMINAL_IMPORTS.setdefault(_mode, _fn._MODE_TERMINAL_IMPORTS["second_order"])
_fn._SORTED_MODES = _fn._SORTED_MODES | {
    "second_order_modal_sorted", "third_order_sorted", "third_order_modal_sorted"}
# The measure and cardinality terms of the unsorted classical modes; a sorted mode
# built by cloning has none, like "modal_sorted" and "so_sorted".
_fn._MODE_TERM_EXTRA.setdefault("second_order_modal", _fn._TERM_EXTRA_CLASSICAL)
for _mode in ("third_order_sorted", "third_order_modal_sorted"):
    _fn._MODE_ATOM_ARGS.setdefault(_mode, "hoarglist")
    _fn._MODE_ATOM_EXTRA.setdefault(_mode, _fn._ATOM_EXTRA_THIRD_ORDER)
del _mode

__all__ = [
    "Z3Env",
    "Node",
    "Variable", "Constant", "Number", "Function",
    "Atom", "Not", "And", "Or", "Xor", "Implies", "Iff", "Quantifier",
    "Count", "Measure", "Cardinality", "Contrast",
    "NODE_CLASSES",
    "FOLTransformer",
    "node_at", "replace_at",
    "SortedQuantifier", "SortedConstant",
    "SortedCount", "SortedCardinality",
    "Nominal", "At", "Down",
    "Dependence", "SlashedExists",
    "Tensor", "With", "OPlus", "LinearImplies", "OfCourse", "One", "Top", "Zero",
    "Product", "Under", "Over",
    "WeakConjunction", "WeakDisjunction",
    "StrongConjunction", "StrongDisjunction",
    "LukNegation", "LukImplication", "LukEquivalence",
    "LambdaVar", "Lambda", "Application",
    "Box", "Diamond", "Knows", "Believes", "Says", "Wants",
    "EverybodyKnows", "DistributedKnowledge", "CommonKnowledge",
    "Always", "Eventually", "Next", "Until",
    "Historically", "Once", "Previous", "Since",
    "Obligatory", "Permitted",
    "Would", "Might",
    "SecondOrderQuantifier",
    "PredicateTerm", "Signatures", "analyse_signatures", "MixedSlotError", "NestedPropertySlotError",
    "free_variables",
    "substitute", "beta_reduce", "ReductionLimitError",
    "eta_reduce", "beta_eta_normalize",
    "resolve_lambda_scope",
    "to_fol",
    "nonempty_sort_axioms",
    "sort_membership_axioms",
    "sort_axioms",
    "subsort_axioms",
    "signature_axioms",
]
