"""Third-order AST: a predicate standing in ARGUMENT position, and its typing.

Second-order syntax lets a predicate variable be *bound* (``∀P φ``); it still
only ever appears as the HEAD of an application, ``P(x)``. Third-order syntax
adds the one thing that is genuinely a level up: a predicate whose ARGUMENT is
itself a predicate — ``Positive(G)``, ``Essence(G, x)``,
``Positive(λx. ¬G(x))``. No amount of extra quantification reaches that; it is a
change to the argument layer, which is why it needs its own node
(:class:`PredicateTerm`), its own grammar modes (``third_order`` /
``third_order_modal``, see ``_MODE_ATOM_ARGS`` in ``_fol_nodes.py``) and its own
typing pass (:func:`analyse_signatures`).

**The node.** ``PredicateTerm(name)`` is a leaf that occupies an argument slot
and denotes the property/relation the name stands for — not a truth value. It is
deliberately *not* an ``Atom`` with zero arguments: ``P`` as a nullary atom is a
proposition, ``PredicateTerm("P")`` is the predicate itself, and conflating them
is exactly the type error the third order exists to make visible. Its ``name``
field is spelled like ``Variable.name`` / ``Constant.name`` / ``LambdaVar.name``
so the shared term renderers reach it by the same path.

Every first-order back-end refuses it, for the same reason
``SecondOrderQuantifier`` does: a property argument has no first-order or
SMT-LIB reading. The HOL exporters are where it goes
(:mod:`unicode_fol_kit.hol.thirdorder`,
:mod:`unicode_fol_kit.hol.ho_modal`).

**The typing pass.** A predicate's argument slots are not annotated in the
surface syntax, so what each slot holds — an individual, or a property of arity
k — is *inferred*, and the inference has to run over a whole theory rather than
one formula: ``Positive(Phi)`` alone says nothing about Phi's arity, while
``Positive(G)`` together with ``G(x)`` elsewhere in the same axiom set fixes it
at 1. :func:`analyse_signatures` takes any number of formulas and returns one
:class:`Signatures` for all of them: it collects the constraints (an application
fixes its head's arity; a λ-argument fixes its slot's arity by binder depth; a
PredicateTerm links its own arity to its slot's) and closes them under
propagation until nothing moves.

Two ways that can fail, both raised rather than papered over: a predicate applied
at two different arities (``ConflictingArityError``, shared with the second-order
inference), and a slot used once for an individual and once for a property
(:class:`MixedSlotError`).

One way it can be *underdetermined*: a slot no evidence ever reaches — e.g.
``∀Phi (Positive(Phi) → □Positive(Phi))`` read entirely on its own, where Phi is
never applied and shares its slot with nothing that is. Such a slot defaults to
a property of arity **1**, because argument position is what makes it a property
slot at all and 1 is the only reading on which the formula says what it is
plainly meant to say; arity 0 would silently retype it as a predicate over
PROPOSITIONS. The default is recorded in :attr:`Signatures.defaulted` so a
caller that would rather refuse than guess can see exactly which slots were
guessed — the HOL exporters print them as a comment in the emitted theory.
"""

from dataclasses import dataclass
from typing import Dict, FrozenSet, List, Sequence, Set, Tuple

from ._fol_nodes import (
    Node, Z3Env, NODE_CLASSES, Atom, PARSER_OPS, ParserOp, parser_ops_for_mode,
)
from ._so_nodes import (
    SecondOrderQuantifier, ConflictingArityError, _infer_so_arity,
)
from .naming import ParsingError


_NO_EXPORT = (
    "A predicate in argument position (third order) has no first-order or "
    "SMT-LIB reading: its argument denotes a PROPERTY, not an individual. Use "
    "the HOL exporters (hol.thirdorder / hol.ho_modal) instead."
)


@dataclass(frozen=True)
class PredicateTerm(Node):
    """A predicate name occupying an argument slot — the third-order term.

    ``name`` is the predicate's name as written. The node denotes the property
    (or relation) itself, so it is a TERM, not a formula: ``Positive(G)``
    parses to ``Atom("Positive", [PredicateTerm("G")])``, whereas ``Positive``
    applied to the *proposition* G would be ``Atom("Positive", [Atom("G", [])])``.

    The node carries no arity of its own. What arity the property has is a
    property of the whole theory, not of this occurrence, and is answered by
    :func:`analyse_signatures`.
    """

    name: str

    def _tree_parts(self):
        """Return the ``PredicateTerm: G`` label and no children (it is a leaf)."""
        return f"PredicateTerm: {self.name}", []

    def to_dict(self):
        """Serialise to dict with type tag and predicate name."""
        return {"_type": "PredicateTerm", "name": self.name}

    @staticmethod
    def from_dict(d):
        """Deserialise a PredicateTerm from a dict produced by to_dict."""
        return PredicateTerm(d["name"])

    def to_z3(self, env: Z3Env = None):
        """Reject Z3 export: a property argument is not SMT-expressible."""
        raise NotImplementedError(_NO_EXPORT)

    def to_prover9(self) -> str:
        """Reject Prover9 export: a property argument is not first-order."""
        raise NotImplementedError(_NO_EXPORT)

    def to_tptp(self) -> str:
        """Reject TPTP (FOF) export: a property argument is not first-order."""
        raise NotImplementedError(_NO_EXPORT)


NODE_CLASSES.update({"PredicateTerm": PredicateTerm})


# =========================
# Signature inference
# =========================


class MixedSlotError(ParsingError):
    """Raised when one argument slot is used for both an individual and a property.

    ``Loves(x, y)`` and ``Loves(x, G)`` cannot both be right: the second slot
    would have to hold an individual and a property at once. Subclasses
    ParsingError so a caller catching the parser's error type also catches this.
    """

    def __init__(self, predicate: str, position: int):
        message = (
            f"TYPE_ERROR: argument slot {position} of '{predicate}' is used "
            f"both for an individual and for a predicate; a slot holds one or "
            f"the other, not both."
        )
        self.args = (message,)

    def __str__(self):
        return self.args[0]


#: What one argument slot holds. ``"i"`` is an individual; ``("p", k)`` is a
#: property/relation of arity ``k``.
INDIVIDUAL = "i"


@dataclass(frozen=True)
class Signatures:
    """The result of :func:`analyse_signatures` over one or more formulas.

    ``arity`` maps every predicate NAME that is applied (or reached by
    propagation) to its arity. ``slots`` maps a predicate name to its argument
    signature — a tuple with one entry per position, each either
    :data:`INDIVIDUAL` or ``("p", k)`` for a property of arity ``k``.
    ``defaulted`` names the ``(predicate, position)`` pairs whose property arity
    no evidence fixed and which therefore defaulted to 1.
    """

    arity: Dict[str, int]
    slots: Dict[str, Tuple[object, ...]]
    defaulted: FrozenSet[Tuple[str, int]]

    def is_third_order(self) -> bool:
        """True iff some predicate takes a property argument (i.e. the theory really is third order)."""
        return any(s != INDIVIDUAL for sig in self.slots.values() for s in sig)

    def property_slots(self) -> List[Tuple[str, int, int]]:
        """Return ``(predicate, position, arity)`` for every property-holding slot, sorted."""
        out = []
        for pred in sorted(self.slots):
            for pos, kind in enumerate(self.slots[pred]):
                if kind != INDIVIDUAL:
                    out.append((pred, pos, kind[1]))
        return out


def _lambda_depth(node: Node) -> int:
    """Return how many leading λ binders ``node`` has (0 if it is not a Lambda).

    ``λx. λy. φ`` is a binary relation, so its depth IS the arity of the
    property it denotes. Imported lazily: Lambda lives in _msfl_nodes, which
    imports this module's dependencies rather than the other way round.
    """
    from ._msfl_nodes import Lambda
    depth = 0
    while isinstance(node, Lambda):
        depth += 1
        node = node.body
    return depth


def analyse_signatures(formulas: Sequence[Node]) -> Signatures:
    """Infer every predicate's arity and argument signature across ``formulas``.

    Runs over the formulas TOGETHER, because that is the scope on which the
    answer is determined: ``Positive(Phi)`` in one axiom and ``Phi(x)`` in
    another jointly fix Phi's arity at 1, and neither does so alone.

    Raises ConflictingArityError if a predicate is applied at two arities, and
    :class:`MixedSlotError` if one slot holds an individual in one place and a
    property in another. A property slot that no evidence reaches defaults to
    arity 1 and is listed in the result's ``defaulted`` — see this module's
    docstring for why 1 and not 0.
    """
    app_arity: Dict[str, Set[int]] = {}
    # slot_kind[(pred, pos)] is INDIVIDUAL, or ("p", None) until its arity is known.
    slot_kind: Dict[Tuple[str, int], object] = {}
    # Which predicate NAMES occupy which slots (a slot may be occupied by several).
    slot_occupants: Dict[Tuple[str, int], Set[str]] = {}
    # Property arities pinned directly by a λ-argument's binder depth.
    slot_lambda_arity: Dict[Tuple[str, int], Set[int]] = {}

    def note_slot(pred: str, pos: int, kind: object) -> None:
        prev = slot_kind.get((pred, pos))
        if prev is None:
            slot_kind[(pred, pos)] = kind
            return
        prev_is_prop = prev != INDIVIDUAL
        now_is_prop = kind != INDIVIDUAL
        if prev_is_prop != now_is_prop:
            raise MixedSlotError(pred, pos)

    def visit(node: Node) -> None:
        if isinstance(node, Atom):
            app_arity.setdefault(node.predicate, set()).add(len(node.args))
            for pos, arg in enumerate(node.args):
                if isinstance(arg, PredicateTerm):
                    note_slot(node.predicate, pos, ("p", None))
                    slot_occupants.setdefault((node.predicate, pos), set()).add(arg.name)
                elif _lambda_depth(arg) > 0:
                    note_slot(node.predicate, pos, ("p", None))
                    slot_lambda_arity.setdefault((node.predicate, pos), set()).add(
                        _lambda_depth(arg))
                else:
                    note_slot(node.predicate, pos, INDIVIDUAL)
        for child in node._child_nodes():
            visit(child)

    for formula in formulas:
        visit(formula)

    # An application fixes its head's arity outright; two different arities for
    # one name is the same error the second-order inference already raises.
    arity: Dict[str, int] = {}
    for pred, arities in app_arity.items():
        if len(arities) > 1:
            raise ConflictingArityError(pred, sorted(arities))
        arity[pred] = next(iter(arities))

    # A λ-argument pins its slot's arity directly.
    slot_arity: Dict[Tuple[str, int], int] = {}
    for slot, depths in slot_lambda_arity.items():
        if len(depths) > 1:
            raise ConflictingArityError(f"{slot[0]}[{slot[1]}]", sorted(depths))
        slot_arity[slot] = next(iter(depths))

    # Close under propagation: a known predicate arity fixes every slot it sits
    # in, and a known slot arity fixes every predicate sitting in it.
    changed = True
    while changed:
        changed = False
        for slot, occupants in slot_occupants.items():
            known = {arity[p] for p in occupants if p in arity}
            if slot in slot_arity:
                known.add(slot_arity[slot])
            if len(known) > 1:
                raise ConflictingArityError(f"{slot[0]}[{slot[1]}]", sorted(known))
            if not known:
                continue
            value = next(iter(known))
            if slot_arity.get(slot) != value:
                slot_arity[slot] = value
                changed = True
            for p in occupants:
                if arity.get(p) != value:
                    if p in arity:
                        raise ConflictingArityError(p, sorted({arity[p], value}))
                    arity[p] = value
                    changed = True

    # Whatever propagation never reached is a property slot with no evidence.
    defaulted: Set[Tuple[str, int]] = set()
    for slot, kind in slot_kind.items():
        if kind == INDIVIDUAL:
            continue
        if slot not in slot_arity:
            slot_arity[slot] = 1
            defaulted.add(slot)
            for p in slot_occupants.get(slot, ()):
                arity.setdefault(p, 1)

    slots: Dict[str, Tuple[object, ...]] = {}
    for pred, n in arity.items():
        sig = []
        for pos in range(n):
            kind = slot_kind.get((pred, pos), INDIVIDUAL)
            sig.append(INDIVIDUAL if kind == INDIVIDUAL
                       else ("p", slot_arity[(pred, pos)]))
        slots[pred] = tuple(sig)

    return Signatures(arity, slots, frozenset(defaulted))


def has_property_argument(node: Node) -> bool:
    """True iff some predicate application in ``node`` has a property argument.

    That is the syntactic marker of third order — a PredicateTerm or a
    λ-abstraction sitting in an argument slot. Used to keep the second-order
    path exactly as it was: a formula without one is answered by the cheaper
    application-scan, unchanged, and pays nothing for the richer inference.
    """
    if isinstance(node, Atom):
        for arg in node.args:
            if isinstance(arg, PredicateTerm) or _lambda_depth(arg) > 0:
                return True
    return any(has_property_argument(child) for child in node._child_nodes())


def infer_bound_arity(body: Node, predname: str) -> int:
    """Infer a third-order-bound predicate variable's arity from ``body``.

    The third-order counterpart of ``_so_nodes._infer_so_arity``: it answers the
    same question, but has one more source of evidence to consult, because in a
    third-order formula ``predname`` may never be applied at all and still be a
    property — ``∀Phi (Positive(Phi) → □Positive(Phi))``. Delegates to
    :func:`analyse_signatures`, whose propagation covers both cases; falls back
    to 0 for a name that genuinely occurs nowhere, matching the second-order
    reading of an unapplied predicate variable as propositional.

    A body with no property argument at all IS a second-order body, and is sent
    straight to ``_infer_so_arity`` — same answer, same cost, and the
    second-order mode's behaviour is then unchanged by construction rather than
    by inspection.

    Shadowing follows ``_infer_so_arity``: an inner binder over the SAME name
    starts a fresh binding, so its scope is cut out before the analysis.
    """
    if not has_property_argument(body):
        return _infer_so_arity(body, predname)
    pruned = _prune_shadowed(body, predname)
    signatures = analyse_signatures([pruned])
    return signatures.arity.get(predname, 0)


def _prune_shadowed(node: Node, predname: str) -> Node:
    """Replace every subformula that rebinds ``predname`` with a constant-true stand-in.

    The inner binder's scope must not contribute evidence about the OUTER
    binding, so it is cut away before the signature analysis runs. The stand-in
    is a zero-argument atom under a reserved name that no source formula can
    spell (it contains a space), so it cannot collide with a real predicate.
    """
    if isinstance(node, SecondOrderQuantifier) and node.predicate == predname:
        return Atom("shadowed scope", [])
    return node.map_children(lambda child: _prune_shadowed(child, predname))


# =========================
# Grammar-mode assembly
# =========================
#
# The two third-order modes are not a new operator set — they are an EXISTING
# operator set over the widened argument layer. ``third_order`` is the
# second-order mode's operators; ``third_order_modal`` is those plus the whole
# modal family. Rather than re-registering ~40 ParserOps (which would drift the
# moment an operator is added to one mode and not the other), each is CLONED
# from its sources, so the third-order modes accept exactly what their base
# modes accept, by construction. ``tests/test_third_order.py`` pins that
# correspondence.


def _clone_parser_ops(target: str, sources: Sequence[str]) -> List[ParserOp]:
    """Register into ``target`` a copy of every ParserOp of the ``sources``, deduped.

    Two source modes overlap (the classical connectives and the first-order
    quantifier are registered for both ``modal`` and ``second_order``); an
    operator is taken from whichever source names it first and skipped
    afterwards, keyed on the parse-level identity that matters —
    ``(level, rule_alias, grammar, only_name)``. Appends to PARSER_OPS and
    returns what was appended.
    """
    seen = set()
    added: List[ParserOp] = []
    for source in sources:
        for op in parser_ops_for_mode(source):
            key = (op.level, op.rule_alias, op.grammar, op.only_name)
            if key in seen:
                continue
            seen.add(key)
            clone = ParserOp(target, op.level, op.terminal_name, op.terminal_def,
                             op.grammar, op.rule_alias, op.transform,
                             op.node_class, op.only_name)
            PARSER_OPS.append(clone)
            added.append(clone)
    return added


# NOT called here. Cloning has to happen after EVERY module that registers an
# operator for a source mode has run -- _hybrid_nodes registers @i / nominals
# for "modal" and is imported after this module's own dependencies -- so the
# call site is nodes.py, which is the one place that controls that order.
