"""Export to TPTP's Non-Classical Logic dialect (NXF) for the mono-modal alethic fragment.

TPTP's *classical* ``fof``/``tff`` syntax (:meth:`Node.to_tptp`) has no way to say
"this problem is modal" — a non-classical prover needs a companion **logic
specification** naming the logic and its parameters, plus new connective syntax
for the modal operators themselves. That companion dialect is **NXF**
("Non-Classical TFF"), defined by Steen & Sutcliffe's TPTP-World infrastructure
for non-classical logics. This module renders one Unicode-kit modal formula as a
complete, self-contained NXF problem: a ``logic`` role statement, one type
declaration per propositional letter, and a ``conjecture`` role statement.

Sources (verified against primary/gold material BEFORE writing a line of this
module — see the individual choices below for what each one settled):

* Steen & Sutcliffe, "TPTP World Infrastructure for Non-classical Logics"
  (arXiv:2508.09318, fetched 2026-08-12) — the logic-specification shape
  ``tff(name, logic, $modal == [ $domains == ..., $designation == ...,
  $terms == ..., $modalities == ... ] ).`` with those four EXACT key names;
  the long-form connective application ``{connective_name} @ (arg1, ..., argn)``
  (so ``{$box} @ (p)`` / ``{$dia} @ (p)``); and the SHORT forms for the
  unparameterised unary modal connectives, ``[.]`` for box and ``<.>`` for
  diamond, used exactly like a classical prefix connective.
* ``github.com/TPTPWorld/NonClassicalLogic`` (cloned locally to read full,
  real, prover-exercised ``.p`` files rather than a paper's abbreviated
  excerpts):
    - ``LogicSpecifications/CorrectSpecifications.p`` — confirms the four-key
      logic-spec form is accepted verbatim (``$domains == $constant,
      $designation == $rigid, $terms == $local/$global,
      $modalities == $modal_system_S5``), and that ``$modal_system_S5`` /
      ``$modal_axiom_K`` / ``$modal_axiom_T`` / ``$modal_axiom_5`` are the
      literal system/axiom names.
    - ``ProblemBuilding/Archive/ClaudiaNalon/IJCAR2022-TPTP/k45_branch_p/
      k45_branch_p.0001.p`` (a real K45 benchmark, i.e. actually fed to
      provers) — THE model this module follows for the PROPOSITIONAL modal
      fragment: a purely propositional problem needs only
      ``tff(name,logic, $modal == [ $modalities == $modal_system_K45 ] ).``
      (``$domains``/``$designation``/``$terms`` are omitted — they govern
      quantification and individual terms, moot with none present), one
      ``tff(<p>_decl,type,<p>: $o).`` per propositional letter (confirming
      NXF/NTF is still a *typed* TFF dialect — untyped ``fof``-style bare
      atoms are not accepted), and the short-form connectives used as plain
      prefix operators: ``[.] z100`` (atomic operand, no parens), ``<.> [.]
      y100`` (chained prefix operators, no parens between them), ``[.] ( ...
      )`` (parenthesised only when the operand is itself a binary-connective
      formula) — i.e. ``[.]``/``<.>`` sit in the grammar at exactly the same
      position ``~`` does, which is also the ``fof``/``tff`` grammar's own
      documented behaviour (see :mod:`fol.tptp_input`'s ``?unary: "~" unary |
      ...`` rule) and is what :func:`to_tptp_ncl` relies on below.
    - ``SampleProblems/PUZ087_1.p`` — a ``$epistemic_modal`` problem using the
      INDEXED long form ``{$knows(#agent)} @ (...)``, confirming that a
      future multi-modal export (Knows/Believes/... — explicitly out of scope
      here) would need the long, not short, connective form.
* ``fol/_modal_nodes.py`` — confirms ``Box``/``Diamond`` (and every other
  modal-family node) reject the classical ``to_tptp()`` outright, so this
  module cannot delegate to ``Node.to_tptp`` for a formula containing one and
  must render the propositional connectives itself (mirroring their existing
  ``to_tptp`` shape exactly — see :func:`_render`).
* ``fol/tptp_input.py`` / ``fol/_fol_nodes.py::Atom.to_tptp`` — the kit's
  existing name convention (predicate names lower-cased, a 0-ary atom is a
  bare lower-case identifier) is reused verbatim via ``Atom.to_tptp()`` for
  every propositional letter, rather than re-implementing it here.

Scope — deliberately narrow, and narrowed FURTHER than the task's own
fallback ("start propositional, reject quantifiers as a documented
extension") once the fragment was pinned down against the sources above:

* Supported: :class:`~fol.nodes.Box`, :class:`~fol.nodes.Diamond`,
  :class:`~fol.nodes.Not`, :class:`~fol.nodes.And`, :class:`~fol.nodes.Or`,
  :class:`~fol.nodes.Implies`, :class:`~fol.nodes.Iff`, over **0-ary**
  :class:`~fol.nodes.Atom` nodes (propositional letters) — the mono-modal
  ALETHIC fragment (the frame system is K/T/S4/S5; no other modal family).
* NOT supported, each raising :class:`NotImplementedError` with a message
  naming the reason (never a silently weaker translation):
    - Quantifiers (:class:`Quantifier`/``SortedQuantifier``) — the NXF
      quantified fragment needs ``$domains``/``$designation``/``$terms`` to
      be semantically meaningful and needs typed INDIVIDUAL terms (a ``$i``
      or user sort per constant, per :samp:`PUZ087_1.p`'s ``wiseman: $tType``
      pattern) — a real but separate extension, deferred rather than guessed.
    - Non-nullary atoms (``P(x)``) — same reason: they need individual-term
      typing this module does not attempt yet.
    - Every other modal family (epistemic ``Knows``/``Believes``, doxastic,
      temporal, deontic, counterfactual, PAL) — each needs the INDEXED
      long-form connective (:samp:`PUZ087_1.p`'s ``{{$knows(#a)}} @ (...)``),
      a distinct multi-modal logic spec, and per-family semantics; a
      follow-up, not guessed here.
    - Any frame other than K/T/S4/S5 (:class:`ValueError`, not
      ``NotImplementedError`` — this is a caller input error, not a missing
      feature: the four systems are exactly the ones :func:`modal_prove`
      elsewhere in this kit already knows how to reason about).
"""

from typing import Dict

from ..fol.nodes import Atom, And, Box, Diamond, Iff, Implies, Node, Not, Or

__all__ = ["to_tptp_ncl"]

# The frame names this kit's OWN modal tableau (atp.modal_tableau) already
# reasons about (K/T/S4/S5) map onto the literal $modal_system_<X> tokens
# confirmed by LogicSpecifications/CorrectSpecifications.p and
# k45_branch_p.0001.p (which additionally confirms $modal_system_K45 exists,
# i.e. the naming scheme generalises — but only K/T/S4/S5 are wired up here,
# matching the frames the rest of this kit's modal backends support).
_FRAME_TO_SYSTEM: Dict[str, str] = {
    "K": "$modal_system_K",
    "T": "$modal_system_T",
    "S4": "$modal_system_S4",
    "S5": "$modal_system_S5",
}

# $domains values, confirmed by CorrectSpecifications.p's $domains ==
# $constant / [$constant, plushie == $varying] examples and the arXiv
# infrastructure paper's enumeration of $constant/$varying/$cumulative/
# $decreasing. Only the bare (non-per-type) form is exposed here — a
# per-type domain list is part of the quantified-fragment extension this
# module does not implement (see module docstring).
_DOMAIN_WORDS: Dict[str, str] = {
    "constant": "$constant",
    "varying": "$varying",
    "cumulative": "$cumulative",
    "decreasing": "$decreasing",
}

_UNSUPPORTED_ATOM = (
    "to_tptp_ncl: non-nullary atom {atom!r} (e.g. P(x)) is outside this exporter's "
    "PROPOSITIONAL fragment — individual terms need their own $i/$tType typing "
    "(see PUZ087_1.p's 'wiseman: $tType' pattern), which this module does not "
    "attempt yet (see module docstring 'Scope'). Only 0-ary atoms (propositional "
    "letters) are supported in this release."
)

_UNSUPPORTED_NODE = (
    "to_tptp_ncl: {name} is outside the supported mono-modal alethic PROPOSITIONAL "
    "fragment (Box/Diamond/¬/∧/∨/→/↔ over 0-ary atoms). "
    "Quantifiers, non-nullary atoms, and every other modal family (epistemic "
    "Knows/Believes, doxastic, temporal, deontic, counterfactual, PAL) are "
    "documented, not-yet-implemented extensions — see module docstring 'Scope'."
)


def _render(node: Node) -> str:
    """Render one node of the supported fragment as an NXF formula string.

    Mirrors the shape :meth:`Node.to_tptp` already uses for the classical
    connectives (``~(...)``, ``(l & r)``, ``(l | r)``, ``(l => r)``,
    ``(l <=> r)`` — see ``fol/_fol_nodes.py``), and extends it with the two
    NXF short-form modal prefix connectives, ``[.]``/``<.>`` (see module
    docstring). Every branch's own output is already a self-delimited
    ``unary`` production (a bare atom, a ``~(...)``-wrapped formula, a fully
    parenthesised binary formula, or ``[.]``/``<.>`` applied to one of
    those), so nesting one under another NEVER needs extra wrapping
    parentheses — exactly how the classical grammar's own ``~`` nests
    (confirmed against ``fol/tptp_input.py``'s ``?unary: "~" unary | ...``
    rule) and how ``k45_branch_p.0001.p`` chains ``<.> [.] y100`` with no
    parentheses between the two prefix operators.

    Raises:
        NotImplementedError: ``node`` (or a descendant) is outside the
            supported fragment — a non-nullary atom, a quantifier, or any
            modal-family node other than Box/Diamond.
    """
    if isinstance(node, Atom):
        if node.args:
            raise NotImplementedError(_UNSUPPORTED_ATOM.format(atom=node))
        return node.to_tptp()
    if isinstance(node, Not):
        return f"~({_render(node.formula)})"
    if isinstance(node, And):
        return f"({_render(node.left)} & {_render(node.right)})"
    if isinstance(node, Or):
        return f"({_render(node.left)} | {_render(node.right)})"
    if isinstance(node, Implies):
        return f"({_render(node.left)} => {_render(node.right)})"
    if isinstance(node, Iff):
        return f"({_render(node.left)} <=> {_render(node.right)})"
    if isinstance(node, Box):
        return f"[.] {_render(node.formula)}"
    if isinstance(node, Diamond):
        return f"<.> {_render(node.formula)}"
    raise NotImplementedError(_UNSUPPORTED_NODE.format(name=type(node).__name__))


def to_tptp_ncl(formula: Node, *, frame: str = "K", domains: str = "constant",
                conjecture_name: str = "c") -> str:
    """Render ``formula`` as a complete NXF (TPTP Non-Classical Logic) problem.

    Covers the mono-modal ALETHIC PROPOSITIONAL fragment: Box/Diamond over
    ``¬``/``∧``/``∨``/``→``/``↔`` and 0-ary atoms
    (propositional letters). See the module docstring for the verified
    syntax sources and the exact scope boundary (quantifiers, non-nullary
    atoms, and non-alethic modal families are documented, not-yet-implemented
    extensions, not silently mistranslated).

    The emitted problem is three parts, in order:

    1. A ``logic`` role statement fixing the four NXF modal parameters —
       ``$domains``/``$designation``/``$terms`` are emitted in the full form
       confirmed by ``LogicSpecifications/CorrectSpecifications.p`` even
       though they are semantically inert without quantifiers/individual
       terms in THIS fragment, so the emitted spec stays forward-compatible
       with a future quantified extension without changing shape.
       ``$designation`` is fixed to ``$rigid`` and ``$terms`` to ``$global``
       — the only combination this fragment (no individual terms at all)
       needs; ``$flexible``/``$local`` are not exposed as they would only
       matter once individual terms exist.
    2. One ``type`` statement per DISTINCT propositional letter appearing in
       ``formula`` (in first-occurrence pre-order, for a deterministic,
       readable rendering), each declaring it ``$o`` (TPTP's builtin boolean
       type) — required because NXF/NTF is a typed (TFF-based) dialect;
       an undeclared bare atom is not accepted (confirmed by every example
       in ``k45_branch_p.0001.p``, which declares every one of its 15
       propositional letters before using them).
    3. One ``conjecture`` role statement holding the translated ``formula``.

    Args:
        formula: a modal formula built from Box/Diamond/Not/And/Or/Implies/
            Iff over 0-ary Atom nodes (the supported fragment — see module
            docstring). Typically the result of folding
            ``premises ⊨ conclusion`` into ``(∧premises) →
            conclusion`` first (:func:`atp.leo3_backend`'s
            ``decide()`` does this), since NXF has no separate premise list —
            one conjecture is the whole problem.
        frame: the alethic modal system — one of ``"K"``, ``"T"``, ``"S4"``,
            ``"S5"`` (:class:`ValueError` listing the valid names otherwise).
        domains: the NXF ``$domains`` value — one of ``"constant"``,
            ``"varying"``, ``"cumulative"``, ``"decreasing"``
            (:class:`ValueError` listing the valid names otherwise). Emitted
            for forward-compatibility (see point 1 above); inert in this
            propositional fragment.
        conjecture_name: the TPTP statement name used for the ``conjecture``
            role formula; the ``logic`` role statement is named
            ``<conjecture_name>_logic``.

    Returns:
        The complete NXF problem text, newline-terminated, ready to write to
        a ``.p`` file for an NXF-aware prover (e.g. Leo-III via
        :class:`atp.leo3_backend.Leo3Backend`).

    Raises:
        ValueError: ``frame`` or ``domains`` is not one of the recognised
            values.
        NotImplementedError: ``formula`` (or a descendant) is outside the
            supported fragment — see :func:`_render`.
    """
    if frame not in _FRAME_TO_SYSTEM:
        raise ValueError(
            f"to_tptp_ncl: unknown frame {frame!r} (use one of {sorted(_FRAME_TO_SYSTEM)})")
    if domains not in _DOMAIN_WORDS:
        raise ValueError(
            f"to_tptp_ncl: unknown domains {domains!r} (use one of {sorted(_DOMAIN_WORDS)})")

    # _render walks the WHOLE tree and raises before anything is emitted if
    # any node is outside the supported fragment (including a non-nullary
    # atom nested anywhere), so by the time this returns every Atom reached
    # below is guaranteed 0-ary.
    body = _render(formula)

    # TPTP identifiers are lower-cased by Atom.to_tptp(), which is NOT
    # injective on the kit's predicate names (``Px`` and ``PX`` both render
    # as ``px``). Silently aliasing two distinct letters would make an
    # invalid formula like ``Px → PX`` export as the tautology
    # ``(px => px)`` — a soundness hole for any prover consuming the file —
    # so a collision refuses the export instead.
    letters = []
    seen = {}
    for node in formula.walk():
        if isinstance(node, Atom):
            name = node.to_tptp()
            if name in seen:
                if seen[name] != node.predicate:
                    raise NotImplementedError(
                        f"to_tptp_ncl: distinct propositional letters "
                        f"{seen[name]!r} and {node.predicate!r} would both "
                        f"render as the NXF identifier {name!r} (TPTP "
                        "lower-cases atom names) — refusing to alias them; "
                        "rename one of the atoms so the export stays "
                        "faithful.")
            else:
                seen[name] = node.predicate
                letters.append(name)

    lines = [
        f"tff({conjecture_name}_logic,logic,",
        "    $modal ==",
        f"      [ $domains == {_DOMAIN_WORDS[domains]},",
        "        $designation == $rigid,",
        "        $terms == $global,",
        f"        $modalities == {_FRAME_TO_SYSTEM[frame]} ] ).",
        "",
    ]
    for name in letters:
        lines.append(f"tff({name}_decl,type,")
        lines.append(f"    {name}: $o ).")
        lines.append("")
    lines.append(f"tff({conjecture_name},conjecture,")
    lines.append(f"    {body} ).")
    return "\n".join(lines) + "\n"
