"""Align APE's reified TPTP vocabulary onto the mapping's — differential glue.

The ACE-2 correctness argument is a differential: for every corpus sentence
that BOTH routes cover, the kit-DRS route's FOL
(:func:`unicode_fol_kit.drt.export.drs_to_fol` over
:func:`unicode_fol_kit.ace.mapping.map_ace_drs`) must be Z3-equivalent to
Attempto's own reference translation (the TPTP output, read by
:func:`unicode_fol_kit.fol.tptp_input.parse_tptp`). The two sides speak
different dialects of the same signature — APE reifies what the mapping
names::

    Predicate2(e, see, s, o)        vs.   See(e, s, o)
    Property1(a, rich, pos)         vs.   Rich(a)
    Property2(a, tall, comp_than, m) vs.  Tall_comp_than(a, m)
    Relation(a, of, b)              vs.   Of(a, b)
    Modifier_adv(e, loudly, pos)    vs.   Loudly(e)
    Object(a, water, mass, na, na, na) vs. Water(a)
    'John', 30, string('Johnny')    vs.   john, c_30, c_Johnny

This module rewrites the APE side into the mapping side, atom by atom, with
the SAME name rules the mapping uses (imported from it, not re-implemented),
so the differential compares semantics rather than spelling. It is private
test machinery in package form: the rewrite rules are themselves a claim
about the correspondence, and the differential is what checks that claim —
a wrong rule here makes sentences INequivalent and the test loud, never the
other way around. Anything outside the measured inventory raises.
"""

from __future__ import annotations

from typing import List

from ..fol.nodes import (
    And, Atom, Constant, Function, Implies, Node, Not, Number, Or, Quantifier,
    Variable,
)
from .mapping import _degree_name, _kit_predicate, _named_constant

__all__ = ["align_ape_tptp_formula", "conjoin"]


def conjoin(formulas: List[Node]) -> Node:
    """One formula per sentence → one formula per text (∧-fold)."""
    if not formulas:
        raise ValueError("conjoin: no formulas")
    result = formulas[0]
    for f in formulas[1:]:
        result = And(result, f)
    return result


def align_ape_tptp_formula(formula: Node) -> Node:
    """Rewrite one parsed APE-TPTP formula into the mapping vocabulary."""
    return _align(formula)


def _align(node: Node) -> Node:
    if isinstance(node, Quantifier):
        return Quantifier(node.type, node.variable, _align(node.formula))
    if isinstance(node, And):
        return And(_align(node.left), _align(node.right))
    if isinstance(node, Or):
        return Or(_align(node.left), _align(node.right))
    if isinstance(node, Implies):
        return Implies(_align(node.left), _align(node.right))
    if isinstance(node, Not):
        return Not(_align(node.formula))
    if isinstance(node, Atom):
        return _align_atom(node)
    raise NotImplementedError(
        f"APE TPTP alignment: {type(node).__name__} is not in the measured "
        "inventory of APE outputs")


def _atom_name(term: Node, what: str) -> str:
    if isinstance(term, Constant):
        return term.name
    raise NotImplementedError(
        f"APE TPTP alignment: expected a constant {what}, got "
        f"{type(term).__name__}")


def _align_atom(atom: Atom) -> Atom:
    p, args = atom.predicate, atom.args
    if p in ("Predicate1", "Predicate2", "Predicate3") and len(args) >= 3:
        verb = _atom_name(args[1], "verb")
        participants = tuple(_align_term(a) for a in (args[0],) + args[2:])
        return Atom(_kit_predicate(verb), participants)
    if p in ("Property1", "Property2") and len(args) >= 3:
        adjective = _atom_name(args[1], "adjective")
        degree = _atom_name(args[2], "degree")
        rest = tuple(_align_term(a) for a in (args[0],) + args[3:])
        return Atom(_degree_name(adjective, degree), rest)
    if p == "Relation" and len(args) == 3:
        middle = _atom_name(args[1], "relation kind")
        if middle != "of":
            raise NotImplementedError(
                f"APE TPTP alignment: relation kind {middle!r} not measured")
        return Atom("Of", (_align_term(args[0]), _align_term(args[2])))
    if p == "Modifier_adv" and len(args) == 3:
        adverb = _atom_name(args[1], "adverb")
        degree = _atom_name(args[2], "degree")
        return Atom(_degree_name(adverb, degree), (_align_term(args[0]),))
    if p == "Modifier_pp" and len(args) == 3:
        preposition = _atom_name(args[1], "preposition")
        return Atom(_kit_predicate(preposition),
                    (_align_term(args[0]), _align_term(args[2])))
    if p == "Object" and len(args) == 6:
        noun = _atom_name(args[1], "noun")
        return Atom(_kit_predicate(noun), (_align_term(args[0]),))
    # Everything else — the prettified unary nouns (Man, Dog), equality —
    # already speaks the mapping vocabulary up to its TERMS.
    return Atom(p, tuple(_align_term(a) for a in args))


def _align_term(term: Node) -> Node:
    if isinstance(term, Variable):
        return term
    if isinstance(term, Constant):
        return Constant(_named_constant(term.name))
    if isinstance(term, Number):
        value = term.value
        if isinstance(value, int) or value == int(value):
            text = str(int(value)) if value >= 0 else "m" + str(-int(value))
        else:
            text = ("m" if value < 0 else "") + str(abs(value)).replace(".", "p")
        return Constant("c_" + text)
    if isinstance(term, Function) and term.name == "string" and len(term.args) == 1:
        inner = term.args[0]
        if isinstance(inner, Constant):
            cleaned = "".join(ch for ch in inner.name if ch.isalnum())
            return Constant("c_" + (cleaned if cleaned else "str"))
    raise NotImplementedError(
        f"APE TPTP alignment: term {type(term).__name__} is not in the "
        "measured inventory")
