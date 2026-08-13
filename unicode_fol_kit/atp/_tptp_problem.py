"""Shared TPTP ``fof`` problem generation for the external TPTP-speaking backends.

:mod:`atp.vampire_entailment`, :mod:`atp.eprover_backend` (E and
Zipperposition), and :mod:`atp.twee_entailment` each build the IDENTICAL TPTP
problem shape from ``(premises, conclusion)``: one ``fof(premise_<i>, axiom,
...).`` line per premise (1-based) plus one ``fof(goal, conjecture, ...).``
line — three copies of the same seven lines that had already started to
drift apart in their docstrings. :func:`generate_tptp_problem` is the single
place that shape is written; the three backends' own ``_generate_*_input``
functions now delegate here (same name, same signature, same output — no
behaviour change for their callers or their tests).

**Soundness guard.** :meth:`~unicode_fol_kit.fol.nodes.Node.to_tptp` folds a
predicate/function/constant name for TPTP's lowercase-initial identifier rule
by lower-casing only its FIRST character (see
:func:`unicode_fol_kit.fol._fol_nodes.tptp_fold_first_letter`) — the exact
mirror of ``tptp_input.py``'s ``_cap()``, which capitalises only the first
character of a parsed predicate name on import. That fold is not injective by
itself: ``Foo`` and ``foo`` (or two constants, or two functions) still both
fold to ``foo``. A single node's ``to_tptp()`` has no way to know whether some
OTHER node elsewhere in the same problem folds to the same identifier, so the
check has to happen here, where every premise and the conclusion are in view
together. Two distinct kit-level names colliding on export would otherwise be
silently merged into ONE TPTP symbol — e.g. a premise ``Foo(a)`` and its
negation ``¬FOO(a)`` would both render as ``foo(a)``, making the exported
axiom set ``{foo(a), ~foo(a)}`` — internally CONTRADICTORY, so an external
prover proves any conjecture from it via ex falso quodlibet, a false
"Theorem" verdict for a query the premises never actually entail. Rather than
risk that, :func:`generate_tptp_problem` refuses with ``NotImplementedError``
naming both colliding kit-level names, mirroring
:func:`unicode_fol_kit.atp.tptp_ncl.to_tptp_ncl`'s own (separately
implemented, since NXF's modal connectives are outside ``to_tptp``'s
classical FOL fragment) collision guard for the NXF export path.

Predicate names and function/constant names are checked as two SEPARATE
namespaces (mirroring how a TPTP-reading prover resolves a bare identifier by
its syntactic position — formula position is a predicate, term position is a
function/constant — rather than by a single shared symbol table), so a
predicate and a function/constant folding to the same string is not itself
flagged; only two DISTINCT names within the SAME namespace colliding is. The
equality/disequality/arithmetic-comparison predicates (``=``, ``≠``, ``<``,
``>``, ``≤``, ``≥``) and the arithmetic functions (``+``, ``-``, ``*``, ``/``)
are excluded from the check entirely — each maps individually and
injectively to a fixed TPTP token (``=``, ``!=``, ``$less``, ``$sum``, ...),
never through the first-letter fold, so they cannot participate in a folding
collision.
"""

from typing import Dict, List

from ..fol._fol_nodes import constant_name_to_ascii, tptp_fold_first_letter
from ..fol.nodes import Atom, Constant, Function, Node

__all__ = ["generate_tptp_problem"]


def _check_symbol_name(seen: Dict[str, str], rendered: str, original: str, kind: str) -> None:
    """Record ``original -> rendered`` in ``seen``, or raise if it collides.

    ``seen`` maps a rendered TPTP identifier to the ONE original kit-level
    name already observed to fold to it; a second, DIFFERENT original name
    folding to the same rendered identifier is the collision this guards
    against (the same original name repeating — the ordinary case of one
    predicate/function/constant used more than once — is not a collision).
    """
    prior = seen.get(rendered)
    if prior is None:
        seen[rendered] = original
    elif prior != original:
        raise NotImplementedError(
            f"generate_tptp_problem: distinct {kind} names {prior!r} and "
            f"{original!r} would both render as the TPTP identifier "
            f"{rendered!r} (Node.to_tptp folds only the first character to "
            "lower-case, so it cannot tell these two apart) — refusing to "
            "silently merge two distinct symbols into one; rename one of "
            "them before exporting this problem."
        )


def _check_no_symbol_collisions(formulas: List[Node]) -> None:
    """Raise ``NotImplementedError`` if any two distinct predicate names, or
    any two distinct function/constant names, across ``formulas`` would fold
    to the same TPTP identifier under :meth:`Node.to_tptp` — see the module
    docstring for why this cannot be checked inside a single node's
    ``to_tptp()`` and must happen once all of a problem's formulas are known.
    """
    predicates_seen: Dict[str, str] = {}
    terms_seen: Dict[str, str] = {}  # Function and Constant share one namespace
    for formula in formulas:
        for node in formula.walk():
            if isinstance(node, Atom):
                if node.predicate in Atom.INFIX_PREDS_TPTP or node.predicate in Atom.PREFIX_PREDS_TPTP:
                    continue
                rendered = tptp_fold_first_letter(node.predicate)
                _check_symbol_name(predicates_seen, rendered, node.predicate, "predicate")
            elif isinstance(node, Function):
                if node.name in Function.TPTP_ARITH_OPS:
                    continue
                rendered = tptp_fold_first_letter(node.name)
                _check_symbol_name(terms_seen, rendered, node.name, "function")
            elif isinstance(node, Constant):
                rendered = tptp_fold_first_letter(constant_name_to_ascii(node.name))
                _check_symbol_name(terms_seen, rendered, node.name, "constant/function")


def generate_tptp_problem(premises: List[Node], conclusion: Node) -> str:
    """Build a TPTP ``fof`` problem string from premises and a conclusion.

    Each premise becomes ``fof(premise_<i>, axiom, <tptp>).`` (1-based) and
    the conclusion becomes ``fof(goal, conjecture, <tptp>).``. The bodies
    come from ``Node.to_tptp`` (variables upper-cased TPTP-style, predicate/
    function/constant names folded on their first character only — see the
    module docstring). Shared verbatim by :mod:`atp.vampire_entailment`,
    :mod:`atp.eprover_backend`, and :mod:`atp.twee_entailment`.

    Before rendering, checks that the export stays injective across every
    premise and the conclusion TOGETHER — see the module docstring's
    soundness-guard section and :func:`_check_no_symbol_collisions`.

    Raises:
        NotImplementedError: either (a) two distinct predicate names, or two
            distinct function/constant names, would render as the same TPTP
            identifier (the collision guard above), or (b) a premise or the
            conclusion contains a node outside the classical FOL fragment
            ``Node.to_tptp`` covers (modal / second-order / Łukasiewicz /
            lambda) — surfaced by ``to_tptp`` itself, unchanged from before
            this module existed.
    """
    _check_no_symbol_collisions(list(premises) + [conclusion])
    lines: List[str] = []
    for i, premise in enumerate(premises, start=1):
        lines.append(f"fof(premise_{i}, axiom, {premise.to_tptp()}).")
    lines.append(f"fof(goal, conjecture, {conclusion.to_tptp()}).")
    return "\n".join(lines) + "\n"
