"""The two truth constants ``$true`` and ``$false``, as every route reads them.

TPTP defines two propositions of its own, ``$true`` and ``$false``, and this kit
reads them (:mod:`unicode_fol_kit.fol.tptp_input`, the SMT-LIB reader, the QMLTP
reader) as the NULLARY atoms ``Atom('$true')`` / ``Atom('$false')``. They are the
constants truth and falsity, not propositional letters of the user's:

* a classical route reads them as true and false (``$false ⊢ P`` is valid,
  ``⊢ $true`` is valid, ``⊢ $false`` is not, ``$true ⊢ P`` is not);
* a modal route reads them the same at every world, an intuitionistic route
  forces ``$true`` at every world and ``$false`` at none, a many-valued route
  gives them the top and the bottom value of the matrix;
* a logic that has no agreed reading of them refuses them BY NAME, through
  :func:`refuse_truth_constants` (relevant logic has two truths and two falsities,
  linear logic has an additive and a multiplicative unit of each, the Lambek
  calculus has no propositional constants at all).

The unicode glyphs are ``⊤`` and ``⊥`` (LaTeX ``\\top`` / ``\\bot``); every unicode
grammar mode that has propositional atoms reads them back to these two atoms. A
nullary atom that is merely NAMED like a glyph (``Atom('⊥', ())``, which prints as
``⊥`` exactly like ``Atom('$false', ())`` does, and which reads back as
``$false``) is the same constant: one glyph has one meaning, so no route reads
either atom as a propositional letter. ``$true`` / ``⊤`` WITH arguments is an
ordinary (if oddly spelled) user predicate and is neither constant:
:func:`truth_value` answers ``None`` for it.

This module only RECOGNISES the constants. It builds no formula and has no
dependency on any route, so every evaluator and prover can import it.
"""

from typing import Iterable, Optional, Tuple

from ._fol_nodes import Atom, Node
from ._tptp_symbols import truth_constant_word

__all__ = [
    "TRUE_PREDICATE", "FALSE_PREDICATE", "TRUE", "FALSE",
    "truth_value", "is_true_constant", "is_false_constant", "is_truth_constant",
    "truth_constants_in", "refuse_truth_constants",
]

#: The predicate names of the two constants, as the TPTP reader spells them.
TRUE_PREDICATE = "$true"
FALSE_PREDICATE = "$false"

#: The two constants as nodes.
TRUE: Atom = Atom(TRUE_PREDICATE, ())
FALSE: Atom = Atom(FALSE_PREDICATE, ())


def truth_value(node: Node) -> Optional[bool]:
    """``True`` for the nullary atoms ``$true`` and ``⊤``, ``False`` for ``$false`` and
    ``⊥``, else ``None``.

    ``None`` also for these names WITH arguments (a user predicate that
    happens to be spelled like a reserved word) and for every node that is not an
    atom, so ``truth_value(node) is None`` reads "an ordinary node".
    """
    if isinstance(node, Atom):
        word = truth_constant_word(node)
        if word is not None:
            return word == TRUE_PREDICATE
    return None


def is_true_constant(node: Node) -> bool:
    """Whether ``node`` is the truth constant true: the nullary atom ``$true`` or ``⊤``."""
    return truth_value(node) is True


def is_false_constant(node: Node) -> bool:
    """Whether ``node`` is the falsity constant: the nullary atom ``$false`` or ``⊥``."""
    return truth_value(node) is False


def is_truth_constant(node: Node) -> bool:
    """Whether ``node`` is one of the two truth constants."""
    return truth_value(node) is not None


def truth_constants_in(formulas: Iterable[Node]) -> Tuple[Atom, ...]:
    """The distinct truth constants occurring anywhere in ``formulas``, in order.

    Each constant is listed once, as its first occurrence: ``$false`` and ``⊥`` are
    one constant, so a formula that holds both lists the one that comes first.
    """
    seen = []
    values = []
    for formula in formulas:
        for node in formula.walk():
            value = truth_value(node)
            if value is not None and value not in values:
                values.append(value)
                seen.append(node)
    return tuple(seen)


def refuse_truth_constants(formulas: Iterable[Node], route: str, why: str,
                           error: type = NotImplementedError) -> None:
    """Raise ``error`` naming ``route`` if ``formulas`` use a truth constant.

    For a route whose logic has no agreed reading of ``$true`` / ``$false``. The
    message names the route, the constant, and ``why`` the logic has no reading, so
    the refusal is a statement and not a guess. ``error`` is the exception class the
    route already uses for input it does not support (``NotImplementedError`` unless
    the route says otherwise). Returns ``None`` when the formulas use neither
    constant.
    """
    found = truth_constants_in(formulas)
    if not found:
        return
    names = " and ".join(a.predicate for a in found)
    raise error(
        f"{route}: the truth constant {names} has no agreed reading here ({why}); "
        "this route refuses it by name rather than read it as a propositional "
        "letter. Write the formula without the constant, or decide it in a logic "
        "that has one (classical, intuitionistic, modal, K3 / LP / FDE, fuzzy).")
