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
    exercised by the FOL-fragment roundtrip test suite.

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
)
from ._modal_nodes import (
    Box, Diamond, Knows, Believes, Says, Wants,
    Always, Eventually, Next, Until,
    Historically, Once, Previous, Since,
    Obligatory, Permitted,
    Would, Might,
    Announce, AnnounceDiamond,
)
from ._so_nodes import SecondOrderQuantifier
from ._hybrid_nodes import Nominal, At
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
    PredicateTerm, Signatures, analyse_signatures, MixedSlotError,
    _clone_parser_ops,
)

# The two third-order grammar modes are their base modes' operator sets over a
# widened argument layer, so they are assembled by CLONING rather than by
# re-registering ~40 operators that would then drift. It happens here, and
# happens last, because it can only be correct once every module that registers
# an operator for "modal" or "second_order" has been imported -- which, at this
# point in this file, they all have.
_clone_parser_ops("third_order", ["second_order"])
_clone_parser_ops("third_order_modal", ["modal", "second_order"])

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
    "Nominal", "At",
    "Dependence", "SlashedExists",
    "Tensor", "With", "OPlus", "LinearImplies", "OfCourse", "One", "Top", "Zero",
    "Product", "Under", "Over",
    "WeakConjunction", "WeakDisjunction",
    "StrongConjunction", "StrongDisjunction",
    "LukNegation", "LukImplication", "LukEquivalence",
    "LambdaVar", "Lambda", "Application",
    "Box", "Diamond", "Knows", "Believes", "Says", "Wants",
    "Always", "Eventually", "Next", "Until",
    "Historically", "Once", "Previous", "Since",
    "Obligatory", "Permitted",
    "Would", "Might",
    "SecondOrderQuantifier",
    "PredicateTerm", "Signatures", "analyse_signatures", "MixedSlotError",
    "free_variables",
    "substitute", "beta_reduce", "ReductionLimitError",
    "eta_reduce", "beta_eta_normalize",
    "resolve_lambda_scope",
    "to_fol",
]
