"""Shared "out-of-scope node" rejection helpers for the modal v1 back-ends.

Both the Kripke evaluator (:mod:`kripke`) and the standard translation
(:mod:`..fol.modal_translation`) interpret only the **propositional / ground**
modal fragment in v1. First-order quantifiers, Łukasiewicz (fuzzy) operators,
and lambda-calculus nodes are out of scope and are rejected uniformly here with
a clear NotImplementedError, so the message wording stays consistent across the
two modules.

An **equality atom** (``a = b`` / ``a ≠ b``) is out of scope for every route
that has no TERM semantics, and :func:`reject_equality` is the one place that
says so: a propositional route reads an atom as a world-relative proposition
keyed by its rendered form, so ``=`` could only be an uninterpreted relation
there, and silently treating identity as one is the kind of approximation this
kit refuses. The propositional modal tableau (:mod:`..atp.modal_tableau`) and the
intuitionistic GMT embedding (:mod:`..hol.intuitionistic`) share it; the message
is parameterised by the route it speaks for.
"""

from typing import NoReturn, TypeGuard

from ..fol.nodes import Atom, Node
from ..fol._msfl_nodes import (
    LukNegation, WeakConjunction, WeakDisjunction,
    StrongConjunction, StrongDisjunction,
    LukImplication, LukEquivalence,
    LambdaVar, Lambda, Application,
)

# Łukasiewicz (fuzzy) node types — no two-valued modal interpretation in v1.
FUZZY_TYPES = (
    LukNegation, WeakConjunction, WeakDisjunction,
    StrongConjunction, StrongDisjunction,
    LukImplication, LukEquivalence,
)

# Lambda-calculus node types — must be eliminated before any modal back-end.
LAMBDA_TYPES = (LambdaVar, Lambda, Application)


def reject_quantifier(formula: Node, caller: str) -> NoReturn:
    """Reject a (sorted) quantifier: v1 modal logic is propositional / ground."""
    raise NotImplementedError(
        f"{caller}: {type(formula).__name__} is not supported — v1 modal logic "
        "is propositional / ground; first-order (quantified) modal logic is "
        "future work."
    )


def reject_fuzzy(formula: Node, caller: str) -> NoReturn:
    """Reject a Łukasiewicz node: modal v1 is two-valued, not fuzzy."""
    raise NotImplementedError(
        f"{caller}: Łukasiewicz node {type(formula).__name__} is not supported — "
        "modal v1 is two-valued; fuzzy modal logic is future work."
    )


def reject_lambda(formula: Node, caller: str) -> NoReturn:
    """Reject a lambda node: beta-reduce / lambda-eliminate before modal work."""
    raise NotImplementedError(
        f"{caller}: lambda node {type(formula).__name__} is not supported — "
        "beta-reduce and lambda-eliminate the formula first."
    )


#: The two spellings the kit gives identity atoms (``a = b`` parses to
#: ``Atom("=", (a, b))``, ``a ≠ b`` to ``Atom("≠", (a, b))``). Refused by NAME,
#: whatever the arity: a propositional route has no term semantics to give either
#: of them a meaning, so the arity of the atom does not matter to the refusal.
EQUALITY_PREDICATES = ("=", "≠")

#: How the Kripke evaluator reads an atom, and so why it cannot read identity.
_KRIPKE_ROUTE = "the propositional Kripke evaluator"
_KRIPKE_ATOM_READING = ("an atom is looked up by its rendered key in a world's "
                        "valuation")

#: What goes wrong if the route reads the atom anyway. The default is the
#: propositional routes': they key an atom by its rendered form, so identity
#: becomes an unconstrained letter. A route whose failure is a DIFFERENT one
#: passes its own ``consequence`` — identity at a property type, for instance,
#: is not an unconstrained letter but a question with several answers.
_KRIPKE_CONSEQUENCE = ("so it would read the identity as an uninterpreted "
                       "proposition and answer wrongly, e.g. 'a = a' false")

#: Where identity IS decided: the first-order modal embedding, which reads ``=`` as
#: RIGID identity over the object domain (``fol.qml``'s "Equality is rigid").
_QML_POINTER = ("Decide equality with unicode_fol_kit.fol.qml.qml_is_valid "
                "(quantified modal logic, where '=' is rigid identity over the "
                "object domain) or another first-order route, not here.")


def is_equality_atom(node: Node) -> TypeGuard[Atom]:
    """True iff ``node`` is an equality / disequality atom (``=`` / ``≠``).

    A ``TypeGuard`` rather than a plain ``bool`` so a caller that has checked
    it may read ``.predicate`` without a second ``isinstance``: the one place
    that decides what counts as identity stays this function.
    """
    return isinstance(node, Atom) and node.predicate in EQUALITY_PREDICATES


def reject_equality(node: Node, caller: str, route: str = _KRIPKE_ROUTE, *,
                    atom_reading: str = _KRIPKE_ATOM_READING,
                    consequence: str = _KRIPKE_CONSEQUENCE,
                    instead: str = _QML_POINTER) -> None:
    """Refuse, by name, ``node`` if it is an equality / disequality atom.

    Same shape as :func:`reject_fuzzy` / :func:`reject_lambda` (a
    ``NotImplementedError`` that starts ``"<caller>: …"`` and says what to use
    instead), but CHECK-AND-RAISE rather than raise-only: a caller applies it to
    EVERY node of the formula and it returns ``None`` on anything that is not an
    identity atom. See :func:`reject_equality_in` for the whole-tree form.

    It is never left to evaluation reaching an ``Atom``. A lazy check would be
    skipped wherever a route short-circuits or is vacuous — a dead end under a
    ``□``, a branch that closes on an unrelated contradiction, an ``∨`` whose left
    side already holds — and the verdict would then not have looked at the atom at
    all. Scan the whole tree at the entry point instead.

    ``route`` names the route the refusal speaks for (it completes "equality is not
    interpreted by …"), ``atom_reading`` says in a clause how that route reads an
    atom (why it cannot read identity), ``consequence`` says what goes wrong if it
    reads the atom anyway, and ``instead`` is the sentence that points elsewhere.
    The defaults are the Kripke evaluator's, so a caller that passes only ``node``
    and ``caller`` gets exactly its message. ``consequence`` is separate from
    ``atom_reading`` because the two are not the same claim: a propositional route
    reads an atom by its rendered key AND therefore gets 'a = a' false, while a
    route refusing identity at a PROPERTY type would not get that wrong — it has
    no single right answer to give.
    """
    if not is_equality_atom(node):
        return
    kind = "equality" if node.predicate == "=" else "disequality"
    raise NotImplementedError(
        f"{caller}: the {kind} atom {node.to_unicode_str()!r} "
        f"({node.predicate!r}) is refused by name — equality is not "
        f"interpreted by {route}. It has no term "
        f"semantics ({atom_reading}), {consequence}. "
        f"{instead}"
    )


def reject_equality_in(formula: Node, caller: str, route: str = _KRIPKE_ROUTE, *,
                       atom_reading: str = _KRIPKE_ATOM_READING,
                       consequence: str = _KRIPKE_CONSEQUENCE,
                       instead: str = _QML_POINTER) -> None:
    """:func:`reject_equality` on every node of ``formula`` (whole-tree scan).

    ``Node.walk`` is generic over the node's fields, so the scan reaches into
    every operator's sub-formula — the body of a modality, both sides of a
    connective, a quantifier's matrix, an announcement and its body, the group
    and agent terms — without this module naming any of them.
    """
    for node in formula.walk():
        reject_equality(node, caller, route, atom_reading=atom_reading,
                        consequence=consequence, instead=instead)
