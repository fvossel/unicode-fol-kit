"""ChemLog TPTP ↔ kit AST — the name bridge between the two halves.

ChemLog's axioms and the FOL definitions LLMs generate for chemical classes
are written in TPTP, where a predicate is LOWERCASE (``c(Ac)``, ``bDOUBLE``)
and a variable is UPPERCASE. The kit's own convention is the exact inverse,
so :func:`unicode_fol_kit.fol.tptp_input.parse_tptp_formula` capitalises
every predicate on import: ``c/1`` arrives as ``C/1``, ``bSINGLE/2`` as
``BSINGLE/2``.

That is correct and injective, but it means a formula imported from TPTP
does NOT line up with the structure :func:`unicode_fol_kit.chem.mol_to_structure`
builds, which carries ChemLog's own lowercase spelling — evaluation then
fails loudly with an uninterpreted symbol rather than silently, which is
right, but useless. This module closes the gap explicitly: it renames the
chemical vocabulary back to its ChemLog spelling after import, and forward
again before export.

**The renaming is checked for injectivity, not assumed.** Two distinct
ChemLog names that capitalise to the same kit name would silently merge two
predicates into one — the classic non-injective-lowercasing soundness bug
this kit has been bitten by before (see ``atp/tptp_ncl``'s collision check).
:data:`KIT_TO_CHEMLOG` is therefore built once at import time and the
construction raises if the mapping is not a bijection on the known
vocabulary.

Symbols OUTSIDE the chemical vocabulary — the class predicates themselves
(``amideBond``, ``carboxylicAcid``) and any auxiliary predicate a generator
invents — are deliberately left in the kit's capitalised form. They have no
ChemLog spelling to restore, the capitalisation is injective on them too,
and inventing a round-trip for them would be guessing at a convention the
source never stated.
"""

from typing import Dict, Optional, Tuple

from ..fol.nodes import Node
from ..fol.tptp_input import parse_tptp_formula
from .signature import CHEMLOG_SIGNATURE

__all__ = [
    "CHEMLOG_TO_KIT", "KIT_TO_CHEMLOG",
    "parse_chemlog_tptp", "to_kit_names", "to_chemlog_names",
]


def _kit_spelling(name: str) -> str:
    """How :func:`parse_tptp_formula` will render the TPTP name ``name``.

    The importer upper-cases the first character and leaves the rest alone;
    this mirrors that rule rather than importing the parser's private helper,
    so a change there surfaces as a failing round-trip test instead of a
    silent divergence.
    """
    return name[:1].upper() + name[1:] if name else name


def _build_maps() -> Tuple[Dict[str, str], Dict[str, str]]:
    """The chemical vocabulary's forward and inverse name maps.

    What the injectivity check below protects against, precisely: it checks
    injectivity under :func:`_kit_spelling` — capitalise the FIRST character
    only, leave the rest exactly as-is — because that is the ONE
    transformation this module's own round trip ever applies: the TPTP
    importer (:func:`~unicode_fol_kit.fol.tptp_input.parse_tptp_formula`)
    capitalises a parsed predicate's first character on the way IN, and
    :data:`KIT_TO_CHEMLOG`/:func:`to_chemlog_names` invert exactly that on
    the way back out. Two ChemLog names differing only in a case change
    AFTER their first character (there happen to be none in the current
    35-predicate vocabulary, but nothing stops a future addition from
    introducing one) would collide under this fold and are refused here
    rather than silently merged.

    This check does NOT protect against a DIFFERENT, unrelated collision:
    a renderer that folds a kit-capitalised name back to TPTP text by
    lowercasing the WHOLE string rather than just its first character (see
    :func:`to_kit_names`'s own docstring) can make two DISTINCT
    kit-spelled names collapse to the SAME TPTP text on export — that is a
    problem for whatever renders TPTP text to catch (a case-preserving
    renderer, or a dedicated export-time collision guard), not something
    this module's own import-direction check can see, since this module
    only ever renames an already-parsed AST and never itself serialises one
    to TPTP text.

    Raises:
        ValueError: two ChemLog names share a kit spelling — the mapping
            would not be invertible and evaluation could silently conflate
            two predicates.
    """
    forward: Dict[str, str] = {}
    inverse: Dict[str, str] = {}
    names = (list(CHEMLOG_SIGNATURE.predicates)
             + list(CHEMLOG_SIGNATURE.functions)
             + sorted(CHEMLOG_SIGNATURE.constants))
    for name in names:
        kit = _kit_spelling(name)
        if kit in inverse and inverse[kit] != name:
            raise ValueError(
                "chem.interop: the chemical vocabulary is not injective under "
                f"the TPTP importer's capitalisation — {name!r} and "
                f"{inverse[kit]!r} both become {kit!r}; a formula using them "
                "could not be mapped back unambiguously")
        forward[name] = kit
        inverse[kit] = name
    return forward, inverse


#: ChemLog spelling -> the spelling the kit's TPTP importer produces.
CHEMLOG_TO_KIT, KIT_TO_CHEMLOG = _build_maps()


def _rename(node: Node, mapping: Dict[str, str]) -> Node:
    """Rename predicate/function symbols throughout ``node`` by ``mapping``.

    Symbols absent from ``mapping`` are left untouched — that is what keeps
    class and auxiliary predicates alone (see the module docstring).
    """
    from ..fol.nodes import Atom, Function
    from dataclasses import replace as _replace

    def walk(current: Node) -> Node:
        if isinstance(current, Atom):
            renamed = mapping.get(current.predicate, current.predicate)
            return _replace(current,
                            predicate=renamed,
                            args=tuple(walk(a) for a in current.args))
        if isinstance(current, Function):
            renamed = mapping.get(current.name, current.name)
            return _replace(current, name=renamed,
                            args=tuple(walk(a) for a in current.args))
        return current.map_children(walk)

    return walk(node)


def to_chemlog_names(formula: Node) -> Node:
    """Rename a kit-side formula's chemical symbols to ChemLog spelling.

    Apply to anything that came through the TPTP importer before evaluating
    it against a :func:`~unicode_fol_kit.chem.mol_to_structure` structure.
    """
    return _rename(formula, KIT_TO_CHEMLOG)


def to_kit_names(formula: Node) -> Node:
    """The inverse of :func:`to_chemlog_names` — ChemLog spelling to kit spelling.

    Apply before handing a structure-side formula to a route that expects the
    kit's own capitalised naming convention. The unicode renderer
    (:meth:`~unicode_fol_kit.fol.nodes.Node.to_unicode_str`) is always a safe
    destination — it renders whatever name is on the node verbatim.

    A route that re-renders the result to TPTP TEXT (e.g. for a prover
    backend) is a DIFFERENT case and is safe only if that renderer restores
    a mixed-case ChemLog name exactly, by folding just the first character
    back to lower case the way :func:`_kit_spelling` folded it up — not by
    lowercasing the name's ENTIRE string, which corrupts a ChemLog name that
    has further uppercase letters after the first one (``bSINGLE`` would
    come back as ``bsingle``, a different, uninterpreted symbol). Whether a
    given TPTP renderer does this correctly is that renderer's own
    contract, not something this function can guarantee on its caller's
    behalf — check it explicitly before trusting a
    ``to_kit_names`` → (render to TPTP) round trip for chemical vocabulary,
    the same way :func:`unicode_fol_kit.mcp.chem_tools.simplify_definition`
    does by using a case-preserving renderer rather than assuming any
    TPTP-rendering route is automatically safe.
    """
    return _rename(formula, CHEMLOG_TO_KIT)


def parse_chemlog_tptp(text: str, *, repair: bool = True) -> Node:
    """Parse ChemLog-style TPTP into an AST that matches molecule structures.

    Parses ``text`` as a bare TPTP formula and renames the chemical
    vocabulary back to its ChemLog spelling, so the result can be evaluated
    directly against :func:`unicode_fol_kit.chem.mol_to_structure` output.

    ``repair=True`` (the default) first runs
    :func:`unicode_fol_kit.fol.repair_tptp_formula`, which absorbs the
    documented syntax failure modes of LLM-generated chemical FOL —
    unbracketed biconditionals and predicate names that need quoting — so a
    formula that a stricter parser would have rejected outright still
    arrives. Free variables are REPORTED by that layer, never silently
    bound: a definition written as ``className(X) <=> …`` is a semantic
    error only its author can resolve.

    Raises:
        ValueError: the text does not parse even after repair.
    """
    if repair:
        from ..fol.tptp_repair import repair_tptp_formula

        result = repair_tptp_formula(text)
        if result.ok and result.formula is not None:
            return to_chemlog_names(result.formula)
    return to_chemlog_names(parse_tptp_formula(text))
