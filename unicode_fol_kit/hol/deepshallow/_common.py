r"""Shared scaffolding for the deep / maximal-shallow / minimal-shallow embeddings.

This subpackage reproduces, per non-classical object logic, the three faithful
HOL embeddings of Benzmüller, *Faithful Logic Embeddings in HOL — Deep and
Shallow* (arXiv:2502.19311v3) and the **machine-checked faithfulness proofs**
between them:

- a **deep** embedding (the object syntax as an Isabelle ``datatype`` with a
  recursive ``primrec`` truth predicate ``truthD``), enabling reasoning *about*
  the object logic (induction over formula structure, meta-theorems);
- a **maximal (heavyweight) shallow** embedding (formulas as predicates with
  *every* semantic parameter explicit, ``... \<Rightarrow> w \<Rightarrow> bool``);
- a **minimal (lightweight) shallow** embedding (the accessibility structure and
  valuation fixed as metalogical ``consts``, formulas as ``w \<Rightarrow> bool``) — the
  variant the paper found automates best, and the style of the toolkit's existing
  :mod:`unicode_fol_kit.hol.isabelle_modal` decision path;
- and the ``primrec`` mappings ``dpToMax`` / ``dpToMin`` plus the theorems
  ``faithful1a/1b`` (deep \<leftrightarrow> maximal), ``faithful2/3`` (deep/maximal
  \<leftrightarrow> minimal in the fixed model) and ``sound_min``, each closed by a
  one-line ``induct`` proof.

The toolkit only *emits* these theories. With a local Isabelle/HOL they are
**machine-verified** end to end via
:func:`unicode_fol_kit.hol.isabelle_runner.check_theory` (exit 0 \<Longrightarrow>
Isabelle's kernel discharged every ``induct`` proof); this is what the
Isabelle-gated tests assert. Without Isabelle, the emitted text still has a fixed,
tested structure. The stack targets the **propositional / schematic** fragment,
where induction over the syntax datatype applies; the *quantified* decision path
stays in :mod:`unicode_fol_kit.hol.isabelle_modal`.
"""

from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple, Type

from unicode_fol_kit.fol.nodes import Node, Atom, Iff, Xor, Variable, Quantifier


def sanitize_atom(name: str) -> str:
    """Turn a propositional-atom label into a legal lowercase Isabelle constant id.

    Distinct atoms get distinct ``consts`` of the shared signature type ``s``; the
    resolver (:class:`AtomConsts`) keeps the mapping injective so two source atoms
    that sanitise alike do not collapse.
    """
    out = "".join(c if (c.isalnum() or c == "_") else "_" for c in str(name))
    if not out:
        out = "p"
    if not (out[0].isalpha() or out[0] == "_"):
        out = "p_" + out
    return "p_" + out if not out.startswith("p_") else out


@dataclass
class AtomConsts:
    """Injective map from propositional-atom label to an Isabelle ``s`` constant.

    Encoders call :meth:`name` while walking a formula; :meth:`decls` then yields the
    ``consts NAME :: "s"`` declarations for exactly the atoms that occurred.
    """

    _by_label: Dict[str, str] = field(default_factory=dict)
    _used: set = field(default_factory=set)

    def name(self, label: str) -> str:
        """The constant naming propositional atom ``label`` (stable, de-collided)."""
        if label in self._by_label:
            return self._by_label[label]
        base = sanitize_atom(label)
        cand, k = base, 1
        while cand in self._used:
            k += 1
            cand = f"{base}_{k}"
        self._by_label[label] = cand
        self._used.add(cand)
        return cand

    def decls(self, typ: str = "s") -> List[str]:
        """``consts`` lines for every atom constant handed out (sorted, stable).

        ``typ`` is the Isabelle type ascribed to each constant. It defaults to the
        signature type ``s`` the deep embeddings index their valuation by; a shallow
        decision theory that has no separate valuation passes the world-predicate
        type instead.
        """
        return [f'consts {c} :: "{typ}"' for c in sorted(self._by_label.values())]


def theory_name_ok(name: str) -> bool:
    """True if ``name`` is a legal Isabelle theory identifier (letters/digits/_)."""
    return bool(name) and name[0].isalpha() and all(
        c.isalnum() or c == "_" for c in name)


def _atom_is_propositional(node: Atom) -> bool:
    """True unless an argument carries a :class:`Variable` (⇒ genuinely first-order)."""
    return not any(isinstance(n, Variable) for a in node.args for n in a.walk())


def encode_deep(formula: Node, atoms: AtomConsts,
                ctors: Dict[Type[Node], Tuple[str, int]], *,
                logic: str, allow_xor: bool = True) -> str:
    r"""Encode a **propositional** formula as a deep datatype term.

    Shared by the per-logic encoders. ``ctors`` maps a toolkit node type to its deep
    constructor name and arity (1 ⇒ ``.formula`` child, 2 ⇒ ``.left`` / ``.right``);
    each distinct ground atom becomes an ``s`` constant collected into ``atoms``.
    ``Xor`` desugars to ``NegD (IffD ...)`` when ``allow_xor``. Raises
    :class:`NotImplementedError` on a quantifier, a free variable, or any node type
    absent from ``ctors`` — the deep embedding is propositional.
    """
    if isinstance(formula, Atom):
        if not _atom_is_propositional(formula):
            raise NotImplementedError(
                f"{logic}: atom with a free variable is first-order; the deep "
                "embedding is propositional.")
        return f"(Atm {atoms.name(formula.to_unicode_str())})"
    if isinstance(formula, (Quantifier, Variable)):
        raise NotImplementedError(
            f"{logic}: quantifiers/variables are first-order; the deep embedding is "
            "propositional.")
    if isinstance(formula, Xor):
        if not (allow_xor and Iff in ctors):
            raise NotImplementedError(f"{logic}: Xor is not supported.")
        left = encode_deep(formula.left, atoms, ctors, logic=logic, allow_xor=allow_xor)
        right = encode_deep(formula.right, atoms, ctors, logic=logic, allow_xor=allow_xor)
        return f"(NegD (IffD {left} {right}))"
    spec = ctors.get(type(formula))
    if spec is None:
        if type(formula).__name__ == "Nominal":
            raise NotImplementedError(
                f"{logic}: a bare lowercase name parses as a hybrid-logic NOMINAL in "
                "modal mode, not a propositional atom. Write atoms as 0-ary predicates "
                "(e.g. P()) or build Atom nodes directly.")
        raise NotImplementedError(
            f"{logic}: unsupported node type {type(formula).__name__} "
            "(the deep embedding covers the propositional fragment only). For "
            "the full modal family — epistemic/doxastic/assertive/bouletic, "
            "deontic, temporal incl. Until/Since, hybrid — use "
            "hol.isabelle_modal.to_isabelle_modal / isabelle_decide_modal or "
            "hol.thf_modal.to_thf_modal_full instead.")
    name, arity = spec
    if arity == 1:
        inner = encode_deep(formula.formula, atoms, ctors, logic=logic, allow_xor=allow_xor)
        return f"({name} {inner})"
    left = encode_deep(formula.left, atoms, ctors, logic=logic, allow_xor=allow_xor)
    right = encode_deep(formula.right, atoms, ctors, logic=logic, allow_xor=allow_xor)
    return f"({name} {left} {right})"


def wrap_theory(theory_name: str, body: str, extra: str = "") -> str:
    """Wrap a verified theory ``body`` in ``theory <name> imports Main begin ... end``."""
    if not theory_name_ok(theory_name):
        raise ValueError(f"illegal theory name {theory_name!r}.")
    parts = [f"theory {theory_name}", "  imports Main", "begin", "", body, ""]
    if extra:
        parts.append(extra)
    parts.append("end")
    return "\n".join(parts) + "\n"


def formula_section(term: str, atoms: AtomConsts, datatype: str) -> str:
    """The ``consts`` + ``definition example`` block grounding a concrete formula."""
    lines = ["", "section \\<open>A concrete embedded formula\\<close>", ""]
    lines += atoms.decls()
    lines.append(f'definition example :: {datatype} where "example = {term}"')
    return "\n".join(lines)
