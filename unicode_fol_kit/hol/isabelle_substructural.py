r"""Isabelle/HOL export for ILL and Lambek-calculus derivations — proof by REPLAY.

Unlike the *shallow* semantical embeddings elsewhere in :mod:`unicode_fol_kit.hol`
(e.g. :mod:`~unicode_fol_kit.hol.isabelle_modal`), this module needs no semantics at
all. :mod:`unicode_fol_kit.atp.linear` (ILL) and :mod:`unicode_fol_kit.atp.lambek` (the
Lambek calculus L) are already **complete, sound, cut-free sequent-calculus decision
procedures**: a formula's :class:`~unicode_fol_kit.atp.linear.ILLDerivation` /
:class:`~unicode_fol_kit.atp.lambek.LambekDerivation` tree, once found, already *is* a
complete proof — Isabelle only needs to be shown, at every node, which rule fired and
why its premises license its conclusion. So this module:

1. **Deep-embeds** the formula grammar as an Isabelle ``datatype`` (``ill`` / ``lam``,
   one constructor per connective, prefixed ``I``/``L`` to dodge any clash with an
   existing HOL identifier — mirroring the ``tv = tT | tB | tF`` prefixing convention
   in :mod:`~unicode_fol_kit.hol.manyvalued`);
2. Defines the sequent-calculus derivability judgement **1:1** as an
   ``inductive derivable`` predicate, one intro rule per rule of the Python calculus,
   each named after and transcribed verbatim from the corresponding ``_r_*`` checker
   in :mod:`~unicode_fol_kit.atp.linear` / :mod:`~unicode_fol_kit.atp.lambek`;
3. States the queried sequent as a ``lemma`` and **replays** the Python-found
   derivation tree as an explicit, fully mechanical Isar proof — a ``have`` step per
   tree node, closed by exactly the rule that node used (``by (rule <IntroName>)``,
   ``using`` the already-established premise facts). No search, no automation beyond
   the purely computational bookkeeping described next: the *replay itself* is the
   proof.

ILL's antecedent: ``list``, not ``multiset`` — and why
--------------------------------------------------------
ILL's antecedent Γ is mathematically a **multiset** (:mod:`atp.linear`'s own
docstring says so, and the natural Isabelle rendering is
``inductive derivable :: "ill multiset ⇒ ill ⇒ bool"`` after
``imports "HOL-Library.Multiset"``). This module does **not** do that, for a concrete,
checkable reason: the theories it emits are built and checked with
:func:`unicode_fol_kit.hol.isabelle_runner.check_theory`, whose scratch session ROOT is
fixed as ``session S = HOL + ... theories <name>`` — it extends only the base ``HOL``
session, with no ``sessions "HOL-Library"`` dependency declaration, so
``imports "HOL-Library.Multiset"`` fails to resolve (confirmed empirically: Isabelle
reports *"Bad import of theory 'HOL-Library.Multiset': need to include sessions
'HOL-Library' in ROOT"*). Since ``check_theory`` is used exactly as instructed and
lives outside this module, this module instead represents Γ as an ``ill list`` and
makes the ONE structural fact a multiset gets "for free" — exchange, i.e. every
reordering of Γ is derivability-preserving — an **explicit extra intro rule**,
``Exch``. This is mathematically exact: "multiset" and "list quotiented by the
transitive closure of adjacent transpositions" are the same equivalence, so
``derivable`` here decides *exactly* the same relation as the Python ``Counter``-based
:func:`~unicode_fol_kit.atp.linear.ill_prove` — it is simply not literally typed as
``multiset``. Every place the replay needs two lists that are the same multiset in a
different order (which happens often — Python's own antecedent tuples are sorted by
render text, not by proof structure) it emits an explicit, finite chain of ``Exch``
applications computed by an adjacent-transposition sort (see ``_reorder_swaps``),
never asking ``simp``/``auto`` to guess a permutation. The Lambek side needs no such
device: L's antecedent genuinely IS an ordered list (no exchange), so
``lam list`` is the literally correct type, ``imports Main`` alone suffices, and the
replay never reorders anything — only re-associates ``@``, always by a trivial,
fully mechanical ``simp`` step (pure ground computation, since every list involved is,
by construction, fully concrete).

Public API
----------
:func:`to_isabelle_ill` / :func:`to_isabelle_lambek` (run the Python prover
internally, raise ``ValueError`` if the sequent is not derivable) and
:func:`ill_derivation_theory` / :func:`lambek_derivation_theory` (take an
already-found — and checker-validated — derivation object directly).
"""

from collections import Counter
from typing import Iterable, List, Optional, Sequence, Tuple

from ..fol.nodes import (
    Node, Atom, Tensor, With, OPlus, LinearImplies, OfCourse, One,
    Product, Under, Over,
)
from ..fol._linear_nodes import Top, Zero
from ..atp.linear import (
    ILLDerivation, ILLSequent, ill_prove, check_ill_proof,
)
from ..atp.lambek import (
    LambekDerivation, LambekSequent, lambek_prove, check_lambek_proof,
)

__all__ = [
    "to_isabelle_ill", "ill_derivation_theory",
    "to_isabelle_lambek", "lambek_derivation_theory",
]


# =============================================================================
# Shared low-level helpers: Isabelle string literals, name bookkeeping.
# =============================================================================

def _isa_str(s: str) -> str:
    """Render a Python string as an Isabelle ``string`` literal ``''...''``.

    ILL/Lambek atoms in this kit are propositional letters / atomic categories
    (``A``, ``NP``, ...); their rendered text never legitimately contains a
    single quote, so — rather than silently mis-escaping — an embedded ``'``
    is rejected outright with a message pointing at why.
    """
    if "'" in s:
        raise NotImplementedError(
            f"to_isabelle_ill/to_isabelle_lambek: atom text {s!r} contains a "
            "single quote, which the Isabelle string-literal encoding used "
            "here does not escape; rename the atom.")
    return "''" + s + "''"


class _Emitter:
    """Accumulates the Isar proof-script lines of one lemma and hands out
    fresh, collision-free fact names (``h1``, ``h2``, ...)."""

    def __init__(self):
        self.lines: List[str] = []
        self._n = 0

    def fresh(self) -> str:
        self._n += 1
        return f"h{self._n}"

    def have(self, stmt: str, using: Sequence[str], method: str) -> str:
        """Emit ``have hN: "stmt" using f1 f2 ... by (method)`` and return hN."""
        name = self.fresh()
        using_clause = f"using {' '.join(using)} " if using else ""
        self.lines.append(f'  have {name}: "{stmt}"\n    {using_clause}by {method}')
        return name


# =============================================================================
# The general list-reordering primitive (ILL only — see the module docstring).
# =============================================================================

def _reorder_swaps(src: Sequence[Node], dst: Sequence[Node]) -> List[int]:
    """Adjacent-transposition sequence turning ``src`` into ``dst`` (same multiset).

    Returns a list of positions ``k`` (swap ``cur[k]``/``cur[k+1]``), to be applied
    to ``src`` **in order**, ending at ``dst``. Standard selection-style algorithm:
    for each target position ``i`` (left to right), find the first not-yet-placed
    occurrence of ``dst[i]`` at or after ``i`` and bubble it left into place —
    O(n^2) swaps worst case, ample for the antecedents this module handles.
    """
    cur = list(src)
    n = len(cur)
    swaps: List[int] = []
    for i in range(n):
        if cur[i] == dst[i]:
            continue
        j = i + 1
        while cur[j] != dst[i]:
            j += 1
        while j > i:
            swaps.append(j - 1)
            cur[j - 1], cur[j] = cur[j], cur[j - 1]
            j -= 1
    assert cur == list(dst), "internal error: _reorder_swaps did not reach dst"
    return swaps


def _remove_one(lst: List[Node], value: Node) -> List[Node]:
    """Return ``lst`` with the first element equal to ``value`` deleted."""
    out = list(lst)
    for i, x in enumerate(out):
        if x == value:
            del out[i]
            return out
    raise AssertionError(f"internal error: {value!r} not found in {lst!r}")


def _counter_diff(a: Sequence[Node], b: Sequence[Node]) -> Counter:
    """``Counter(a) - Counter(b)``, positive entries only (what ``a`` has extra)."""
    c = Counter(a)
    c.subtract(Counter(b))
    return Counter({k: v for k, v in c.items() if v > 0})


def _the_one(c: Counter) -> Node:
    """Return the single key of a one-entry-count-1 Counter (asserts the shape)."""
    assert len(c) == 1 and next(iter(c.values())) == 1, f"internal error: not a singleton diff: {c!r}"
    return next(iter(c))


# =============================================================================
# ILL: deep embedding.
# =============================================================================

ILL_DATATYPE = (
    "datatype ill = IAtom string | ITensor ill ill | IWith ill ill | IOPlus ill ill "
    "| ILImp ill ill | IBang ill | IOne | ITop | IZero"
)

# One entry per Isabelle intro rule, in emission order. 19 mirror the 19 rules of
# atp.linear._ILL_RULES one-for-one (named identically up to Isabelle-legal
# spelling — see _ILL_RULE_TO_ISA); "Exch" is the one addition, the explicit
# structural rule that stands in for "antecedent is a multiset" (see the module
# docstring). 20 rules total.
_ILL_INTROS: List[Tuple[str, str]] = [
    ("Ax", 'derivable [A] A'),
    ("Exch", 'derivable (G1 @ [B, A] @ G2) C \\<Longrightarrow> derivable (G1 @ [A, B] @ G2) C'),
    ("OneR", 'derivable [] IOne'),
    ("OneL", 'derivable G C \\<Longrightarrow> derivable (G @ [IOne]) C'),
    ("TensorL", 'derivable (G @ [A, B]) C \\<Longrightarrow> derivable (G @ [ITensor A B]) C'),
    ("TensorR", 'derivable G A \\<Longrightarrow> derivable D B \\<Longrightarrow> derivable (G @ D) (ITensor A B)'),
    ("LImpL", 'derivable G A \\<Longrightarrow> derivable (D @ [B]) C \\<Longrightarrow> '
               'derivable (G @ D @ [ILImp A B]) C'),
    ("LImpR", 'derivable (G @ [A]) B \\<Longrightarrow> derivable G (ILImp A B)'),
    ("WithL1", 'derivable (G @ [A]) C \\<Longrightarrow> derivable (G @ [IWith A B]) C'),
    ("WithL2", 'derivable (G @ [B]) C \\<Longrightarrow> derivable (G @ [IWith A B]) C'),
    ("WithR", 'derivable G A \\<Longrightarrow> derivable G B \\<Longrightarrow> derivable G (IWith A B)'),
    ("OPlusL", 'derivable (G @ [A]) C \\<Longrightarrow> derivable (G @ [B]) C \\<Longrightarrow> '
                'derivable (G @ [IOPlus A B]) C'),
    ("OPlusR1", 'derivable G A \\<Longrightarrow> derivable G (IOPlus A B)'),
    ("OPlusR2", 'derivable G B \\<Longrightarrow> derivable G (IOPlus A B)'),
    ("BangW", 'derivable G C \\<Longrightarrow> derivable (G @ [IBang A]) C'),
    ("BangC", 'derivable (G @ [IBang A, IBang A]) C \\<Longrightarrow> derivable (G @ [IBang A]) C'),
    ("BangD", 'derivable (G @ [A]) C \\<Longrightarrow> derivable (G @ [IBang A]) C'),
    ("BangP", 'derivable (map IBang G0) A \\<Longrightarrow> derivable (map IBang G0) (IBang A)'),
    ("TopR", 'derivable G ITop'),
    ("ZeroL", 'derivable (G @ [IZero]) C'),
]

# Python atp.linear rule name -> Isabelle intro name (Exch has no Python
# counterpart — see the module docstring).
_ILL_RULE_TO_ISA = {
    "Ax": "Ax", "1R": "OneR", "1L": "OneL",
    "⊗L": "TensorL", "⊗R": "TensorR",
    "⊸L": "LImpL", "⊸R": "LImpR",
    "&L1": "WithL1", "&L2": "WithL2", "&R": "WithR",
    "⊕L": "OPlusL", "⊕R1": "OPlusR1", "⊕R2": "OPlusR2",
    "!W": "BangW", "!C": "BangC", "!D": "BangD", "!P": "BangP",
    "⊤R": "TopR", "0L": "ZeroL",
}


def _lift_ill(node: Node) -> str:
    """Lift an ILL formula to its ``ill``-datatype Isabelle term."""
    if isinstance(node, Atom):
        return f"(IAtom {_isa_str(node.to_unicode_str())})"
    if isinstance(node, Tensor):
        return f"(ITensor {_lift_ill(node.left)} {_lift_ill(node.right)})"
    if isinstance(node, With):
        return f"(IWith {_lift_ill(node.left)} {_lift_ill(node.right)})"
    if isinstance(node, OPlus):
        return f"(IOPlus {_lift_ill(node.left)} {_lift_ill(node.right)})"
    if isinstance(node, LinearImplies):
        return f"(ILImp {_lift_ill(node.left)} {_lift_ill(node.right)})"
    if isinstance(node, OfCourse):
        return f"(IBang {_lift_ill(node.formula)})"
    if isinstance(node, One):
        return "IOne"
    if isinstance(node, Top):
        return "ITop"
    if isinstance(node, Zero):
        return "IZero"
    raise NotImplementedError(f"to_isabelle_ill: unsupported node {type(node).__name__}.")


def _flat_ill(nodes: Sequence[Node]) -> str:
    """Bracket-list Isabelle text for a list of ILL formulas, e.g. ``[A, B]``."""
    if not nodes:
        return "[]"
    return "[" + ", ".join(_lift_ill(n) for n in nodes) + "]"


# ---------------------------------------------------------------------------
# ILL replay engine.
# ---------------------------------------------------------------------------
#
# Contract of _emit_ill(d, emitter) -> (fact_name, antecedent_list): fact_name
# names a fact, already emitted into emitter.lines, whose statement is EXACTLY
# "derivable <_flat_ill(antecedent_list)> <_lift_ill(d.conclusion.succedent)>".
# antecedent_list is SOME list of Node with that multiset (not necessarily
# d.conclusion.antecedent's own order — this module never needs to match that
# specific order, only to be internally consistent; see the module docstring).

def _reorder_bridge(fact: str, src: List[Node], dst: List[Node],
                    succ_isa: str, emitter: _Emitter) -> str:
    """Reshape a flat fact for ``src`` into one for ``dst`` (same multiset), via an
    explicit ``Exch`` chain. Returns ``fact`` unchanged if ``src == dst`` already."""
    if src == dst:
        return fact
    cur = list(src)
    cur_fact = fact
    for k in _reorder_swaps(src, dst):
        x, y = cur[k], cur[k + 1]
        g1, g2 = cur[:k], cur[k + 2:]
        decomp_before = f"{_flat_ill(g1)} @ {_flat_ill([x, y])} @ {_flat_ill(g2)}"
        h_shaped = emitter.have(
            f'derivable ({decomp_before}) {succ_isa}', [cur_fact], "simp")
        decomp_after = f"{_flat_ill(g1)} @ {_flat_ill([y, x])} @ {_flat_ill(g2)}"
        h_swapped = emitter.have(
            f'derivable ({decomp_after}) {succ_isa}', [h_shaped], "(rule Exch)")
        cur[k], cur[k + 1] = y, x
        cur_fact = emitter.have(
            f'derivable {_flat_ill(cur)} {succ_isa}', [h_swapped], "simp")
    assert cur == dst
    return cur_fact


def _decompose(fact: str, full: List[Node], pieces: List[List[Node]],
               succ_isa: str, emitter: _Emitter) -> str:
    """Reshape a flat fact for ``full`` (== the concatenation of ``pieces``) into
    an explicit ``@``-joined form matching ``pieces`` — a pure re-association
    (never a reorder), always closed by a trivial ground ``simp``."""
    text = " @ ".join(_flat_ill(p) for p in pieces) if pieces else "[]"
    flat_text = _flat_ill(full)
    if text == flat_text:
        return fact
    return emitter.have(f'derivable ({text}) {succ_isa}', [fact], "simp")


def _emit_ill(d: ILLDerivation, emitter: _Emitter) -> Tuple[str, List[Node]]:
    """Recursively replay one ILL derivation node; see the contract above."""
    succ_isa = _lift_ill(d.conclusion.succedent)
    rule = d.rule

    if rule == "Ax":
        lst = [d.conclusion.antecedent[0]]
        fact = emitter.have(f'derivable {_flat_ill(lst)} {succ_isa}', [], "(rule Ax)")
        return fact, lst

    if rule == "1R":
        fact = emitter.have(f'derivable [] {succ_isa}', [], "(rule OneR)")
        return fact, []

    if rule == "⊤R":
        lst = list(d.conclusion.antecedent)
        fact = emitter.have(f'derivable {_flat_ill(lst)} {succ_isa}', [], "(rule TopR)")
        return fact, lst

    if rule == "0L":
        lst_all = list(d.conclusion.antecedent)
        idx = next(i for i, x in enumerate(lst_all) if isinstance(x, Zero))
        rest = lst_all[:idx] + lst_all[idx + 1:]
        target = rest + [lst_all[idx]]
        stmt = f'({_flat_ill(rest)} @ {_flat_ill([lst_all[idx]])}) {succ_isa}'
        fact = emitter.have(f'derivable {stmt}', [], "(rule ZeroL)")
        return fact, target

    # --- single-premise rules -------------------------------------------------
    if rule in ("1L", "⊗L", "⊸R", "&L1", "&L2", "!W", "!C", "!D"):
        child = d.premises[0]
        cfact, clist = _emit_ill(child, emitter)
        csucc = _lift_ill(child.conclusion.succedent)

        if rule == "1L":
            extract, tail = [], [One()]
        elif rule == "⊗L":
            compound = _the_one(_counter_diff(d.conclusion.antecedent, clist))
            extract, tail = [compound.left, compound.right], [compound]
        elif rule == "⊸R":
            a = _the_one(_counter_diff(clist, d.conclusion.antecedent))
            extract, tail = [a], []
        elif rule in ("&L1", "&L2"):
            compound = _the_one(_counter_diff(d.conclusion.antecedent, clist))
            extract = [compound.left if rule == "&L1" else compound.right]
            tail = [compound]
        elif rule == "!W":
            compound = _the_one(_counter_diff(d.conclusion.antecedent, clist))
            extract, tail = [], [compound]
        elif rule == "!C":
            compound = _the_one(_counter_diff(clist, d.conclusion.antecedent))
            extract, tail = [compound, compound], [compound]
        else:  # "!D"
            compound = _the_one(_counter_diff(d.conclusion.antecedent, clist))
            extract, tail = [compound.formula], [compound]

        rest = list(clist)
        for v in extract:
            rest = _remove_one(rest, v)
        target = rest + extract
        flat_fact = _reorder_bridge(cfact, clist, target, csucc, emitter)
        if extract:
            # This rule's Isabelle premise pattern needs "G @ [extracted...]" —
            # reshape into that explicit decomposition.
            premise_fact = _decompose(flat_fact, target, [rest, extract], csucc, emitter)
        else:
            # 1L / !W: the premise pattern is bare "G" (no tail at all — the new
            # formula is added only in the CONCLUSION) — flat_fact (== rest,
            # nothing was extracted) is already exactly that; no reshape needed.
            premise_fact = flat_fact

        concl_list = rest + tail
        concl_stmt = f'({_flat_ill(rest)} @ {_flat_ill(tail)}) {succ_isa}'
        isa_rule = _ILL_RULE_TO_ISA[rule]
        hraw = emitter.have(f'derivable {concl_stmt}', [premise_fact], f"(rule {isa_rule})")
        # hraw's antecedent is the DECOMPOSED "rest @ tail" (or, for LImpR/⊸R
        # where tail == [], "rest @ []"); flatten to the plain bracket-list form
        # every _emit_ill caller expects (a pure ground computation, always
        # simp-provable — never a reorder).
        hflat = emitter.have(f'derivable {_flat_ill(concl_list)} {succ_isa}', [hraw], "simp")
        return hflat, concl_list

    # --- BangP (its own shape: image over the SAME antecedent) --------------
    if rule == "!P":
        child = d.premises[0]
        cfact, clist = _emit_ill(child, emitter)
        csucc = _lift_ill(child.conclusion.succedent)
        g0 = [f.formula for f in clist]  # every element of clist is OfCourse(...)
        map_text = f"map IBang {_flat_ill(g0)}"
        h_mapshape = emitter.have(f'derivable ({map_text}) {csucc}', [cfact], "simp")
        hraw = emitter.have(f'derivable ({map_text}) {succ_isa}', [h_mapshape],
                            "(rule BangP)")
        hflat = emitter.have(f'derivable {_flat_ill(clist)} {succ_isa}', [hraw], "simp")
        return hflat, list(clist)

    # --- two-premise rules ----------------------------------------------------
    if rule == "⊗R":
        c0, c1 = d.premises
        f0, l0 = _emit_ill(c0, emitter)
        f1, l1 = _emit_ill(c1, emitter)
        target = l0 + l1
        stmt = f'({_flat_ill(l0)} @ {_flat_ill(l1)}) {succ_isa}'
        hraw = emitter.have(f'derivable {stmt}', [f0, f1], "(rule TensorR)")
        hflat = emitter.have(f'derivable {_flat_ill(target)} {succ_isa}', [hraw], "simp")
        return hflat, target

    if rule == "&R":
        c0, c1 = d.premises
        f0, l0 = _emit_ill(c0, emitter)
        f1, l1 = _emit_ill(c1, emitter)
        csucc1 = _lift_ill(c1.conclusion.succedent)
        f1m = _reorder_bridge(f1, l1, l0, csucc1, emitter)
        stmt = f'derivable {_flat_ill(l0)} {succ_isa}'
        hraw = emitter.have(stmt, [f0, f1m], "(rule WithR)")
        return hraw, l0

    if rule in ("⊕R1", "⊕R2"):
        child = d.premises[0]
        cfact, clist = _emit_ill(child, emitter)
        stmt = f'derivable {_flat_ill(clist)} {succ_isa}'
        isa_rule = "OPlusR1" if rule == "⊕R1" else "OPlusR2"
        hraw = emitter.have(stmt, [cfact], f"(rule {isa_rule})")
        return hraw, list(clist)

    if rule == "⊸L":
        c0, c1 = d.premises  # c0: Γ⊢A ; c1: Δ,B⊢C
        f0, l0 = _emit_ill(c0, emitter)
        f1, l1 = _emit_ill(c1, emitter)
        csucc1 = _lift_ill(c1.conclusion.succedent)
        b = _the_one(_counter_diff(l1, d.conclusion.antecedent))
        d1 = list(l1)
        d1 = _remove_one(d1, b)
        target1 = d1 + [b]
        flat1 = _reorder_bridge(f1, l1, target1, csucc1, emitter)
        premise1 = _decompose(flat1, target1, [d1, [b]], csucc1, emitter)
        compound = _the_one(_counter_diff(d.conclusion.antecedent, l0 + d1))
        concl_list = l0 + d1 + [compound]
        stmt = (f'derivable ({_flat_ill(l0)} @ {_flat_ill(d1)} @ {_flat_ill([compound])}) '
                f'{succ_isa}')
        hraw = emitter.have(stmt, [f0, premise1], "(rule LImpL)")
        hflat = emitter.have(f'derivable {_flat_ill(concl_list)} {succ_isa}', [hraw], "simp")
        return hflat, concl_list

    if rule == "⊕L":
        c0, c1 = d.premises  # c0: Γ,A⊢C ; c1: Γ,B⊢C
        f0, l0 = _emit_ill(c0, emitter)
        f1, l1 = _emit_ill(c1, emitter)
        csucc0 = _lift_ill(c0.conclusion.succedent)
        csucc1 = _lift_ill(c1.conclusion.succedent)
        a = _the_one(_counter_diff(l0, d.conclusion.antecedent))
        b = _the_one(_counter_diff(l1, d.conclusion.antecedent))
        rest0 = _remove_one(list(l0), a)
        rest1 = _remove_one(list(l1), b)
        target0 = rest0 + [a]
        flat0 = _reorder_bridge(f0, l0, target0, csucc0, emitter)
        premise0 = _decompose(flat0, target0, [rest0, [a]], csucc0, emitter)
        # Reconcile rest1 (proving Γ,B⊢C) to rest0's chosen order for Γ.
        target1 = rest0 + [b]
        flat1_native = rest1 + [b]
        flat1 = _reorder_bridge(f1, l1, flat1_native, csucc1, emitter)
        flat1 = _reorder_bridge(flat1, flat1_native, target1, csucc1, emitter)
        premise1 = _decompose(flat1, target1, [rest0, [b]], csucc1, emitter)
        compound = _the_one(_counter_diff(d.conclusion.antecedent, rest0))
        concl_list = rest0 + [compound]
        stmt = f'derivable ({_flat_ill(rest0)} @ {_flat_ill([compound])}) {succ_isa}'
        hraw = emitter.have(stmt, [premise0, premise1], "(rule OPlusL)")
        hflat = emitter.have(f'derivable {_flat_ill(concl_list)} {succ_isa}', [hraw], "simp")
        return hflat, concl_list

    raise NotImplementedError(f"to_isabelle_ill: unsupported derivation rule {rule!r}.")


# ---------------------------------------------------------------------------
# ILL public API.
# ---------------------------------------------------------------------------

def ill_derivation_theory(derivation: ILLDerivation,
                          theory_name: str = "ILLDerivation") -> str:
    """Emit a complete, loadable Isabelle/HOL theory replaying an already-found
    (and checker-validated) :class:`~unicode_fol_kit.atp.linear.ILLDerivation`.

    The returned theory: declares the deep-embedded ``ill`` datatype, defines
    ``derivable`` as an ``inductive`` predicate with one intro rule per rule of
    the Python calculus PLUS ``Exch`` (see the module docstring), states the
    derivation's end-sequent as ``lemma ill_goal`` with its antecedent in the
    ORIGINAL order recorded on ``derivation.conclusion`` (a final ``Exch``
    chain re-orders the replay's own working order to match it), and proves it
    by replaying ``derivation`` node-for-node — one ``have`` per tree node,
    closed by exactly the rule that node used.

    Raises:
        ValueError: if ``derivation`` does not check
            (:func:`~unicode_fol_kit.atp.linear.check_ill_proof`) — there is
            nothing sound to replay.
    """
    if not check_ill_proof(derivation):
        raise ValueError(
            "ill_derivation_theory: the given ILLDerivation does not check "
            "(unicode_fol_kit.check_ill_proof / verify_ill_proof rejects it) "
            "— use ill_prove/ill_derivable to find a valid derivation first.")

    emitter = _Emitter()
    root_fact, root_list = _emit_ill(derivation, emitter)
    wanted = list(derivation.conclusion.antecedent)
    succ_isa = _lift_ill(derivation.conclusion.succedent)
    final_fact = _reorder_bridge(root_fact, root_list, wanted, succ_isa, emitter)

    lines: List[str] = []
    lines.append(f"theory {theory_name}")
    lines.append("  imports Main")
    lines.append("begin")
    lines.append("")
    lines.append("(* Deep embedding + derivation REPLAY of an ILL sequent. The toolkit's own")
    lines.append("   cut-free search (unicode_fol_kit.ill_prove) already found this proof; this")
    lines.append("   theory transcribes it into Isabelle, one intro rule per tree node -- no")
    lines.append("   automation searches for the proof. See the module docstring of")
    lines.append("   unicode_fol_kit.hol.isabelle_substructural for why the antecedent is an")
    lines.append("   \"ill list\" with an explicit Exch rule rather than \"ill multiset\". *)")
    lines.append(f"(* Sequent: {derivation.conclusion} *)")
    lines.append("")
    lines.append(ILL_DATATYPE)
    lines.append("")
    lines.append("inductive derivable :: \"ill list \\<Rightarrow> ill \\<Rightarrow> bool\" where")
    for i, (name, body) in enumerate(_ILL_INTROS):
        prefix = "  " if i == 0 else "| "
        lines.append(f"{prefix}{name}: \"{body}\"")
    lines.append("")
    lines.append(f'lemma ill_goal: "derivable {_flat_ill(wanted)} {succ_isa}"')
    lines.append("proof -")
    lines.extend(emitter.lines)
    lines.append(f"  show ?thesis using {final_fact} by simp")
    lines.append("qed")
    lines.append("")
    lines.append("end")
    return "\n".join(lines) + "\n"


def to_isabelle_ill(premises: Iterable[Node], goal: Node,
                    theory_name: str = "ILLDerivation",
                    max_depth: Optional[int] = None,
                    max_steps: int = 200000) -> str:
    """Run :func:`~unicode_fol_kit.atp.linear.ill_prove` on ``premises ⊢ goal`` and,
    if derivable, emit a complete Isabelle/HOL theory that replays the proof
    (see :func:`ill_derivation_theory`).

    Raises:
        ValueError: if the sequent is not (found) derivable — an underivable
            sequent has no derivation to replay; use ``ill_prove`` /
            ``ill_derivable`` directly first to investigate why (for a
            ``!``-sequent, ``None`` may mean only "not found within the
            default search bound" — see :func:`~unicode_fol_kit.atp.linear.ill_prove`).
    """
    ants = list(premises)
    derivation = ill_prove(ants, goal, max_depth=max_depth, max_steps=max_steps)
    if derivation is None:
        raise ValueError(
            f"to_isabelle_ill: {ILLSequent(tuple(ants), goal)} was not found "
            "derivable by ill_prove — there is no derivation to replay. Call "
            "unicode_fol_kit.ill_prove / ill_derivable first (with an explicit "
            "max_depth for a !-sequent if needed) to confirm derivability.")
    return ill_derivation_theory(derivation, theory_name=theory_name)


# =============================================================================
# Lambek calculus L: deep embedding.
# =============================================================================
#
# L's antecedent is genuinely ORDERED (no exchange), so "lam list" is the
# literally correct type — no Exch-style device is needed here, and the
# replay never reorders anything: every list constructed below is either the
# direct concatenation of already-known sub-lists, or a known list split at a
# known index (found by comparing a conclusion's antecedent tuple against its
# premises' — see _find_split_left / _find_split_right), so the only "bridge"
# ever needed is a pure "@"-re-association, always closed by a trivial,
# fully-ground `simp` (never a permutation).

LAMBEK_DATATYPE = "datatype lam = LAtom string | LProduct lam lam | LUnder lam lam | LOver lam lam"

# One entry per Isabelle intro rule; 7 total, 1:1 with atp.lambek's 7 rules
# (Ax, •L, •R, \L, \R, /L, /R — see _LAMBEK_RULE_TO_ISA). Unlike ILL, nothing
# extra is added: L's list type needs no structural-rule stand-in.
_LAMBEK_INTROS: List[Tuple[str, str]] = [
    ("Ax", 'derivable [A] A'),
    ("ProdL", 'derivable (G1 @ [A, B] @ G2) C \\<Longrightarrow> derivable (G1 @ [LProduct A B] @ G2) C'),
    ("ProdR", 'derivable G A \\<Longrightarrow> derivable D B \\<Longrightarrow> derivable (G @ D) (LProduct A B)'),
    ("UnderL", 'G \\<noteq> [] \\<Longrightarrow> derivable G A \\<Longrightarrow> derivable (D1 @ [B] @ D2) C \\<Longrightarrow> '
                'derivable (D1 @ G @ [LUnder A B] @ D2) C'),
    ("UnderR", 'G \\<noteq> [] \\<Longrightarrow> derivable (A # G) B \\<Longrightarrow> derivable G (LUnder A B)'),
    ("OverL", 'G \\<noteq> [] \\<Longrightarrow> derivable G A \\<Longrightarrow> derivable (D1 @ [B] @ D2) C \\<Longrightarrow> '
              'derivable (D1 @ [LOver B A] @ G @ D2) C'),
    ("OverR", 'G \\<noteq> [] \\<Longrightarrow> derivable (G @ [A]) B \\<Longrightarrow> derivable G (LOver B A)'),
]

_LAMBEK_RULE_TO_ISA = {
    "Ax": "Ax", "•L": "ProdL", "•R": "ProdR",
    "\\L": "UnderL", "\\R": "UnderR", "/L": "OverL", "/R": "OverR",
}


def _lift_lambek(node: Node) -> str:
    """Lift a Lambek type/formula to its ``lam``-datatype Isabelle term."""
    if isinstance(node, Atom):
        return f"(LAtom {_isa_str(node.to_unicode_str())})"
    if isinstance(node, Product):
        return f"(LProduct {_lift_lambek(node.left)} {_lift_lambek(node.right)})"
    if isinstance(node, Under):
        return f"(LUnder {_lift_lambek(node.left)} {_lift_lambek(node.right)})"
    if isinstance(node, Over):
        return f"(LOver {_lift_lambek(node.left)} {_lift_lambek(node.right)})"
    raise NotImplementedError(f"to_isabelle_lambek: unsupported node {type(node).__name__}.")


def _flat_lambek(nodes: Sequence[Node]) -> str:
    """Bracket-list Isabelle text for a list of Lambek types, e.g. ``[A, B]``."""
    if not nodes:
        return "[]"
    return "[" + ", ".join(_lift_lambek(n) for n in nodes) + "]"


# ---------------------------------------------------------------------------
# Lambek replay engine.
# ---------------------------------------------------------------------------
#
# Contract of _emit_lambek(d, emitter) -> fact_name: fact_name names a fact,
# already emitted into emitter.lines, whose statement is EXACTLY
# "derivable <_flat_lambek(d.conclusion.antecedent)> <_lift_lambek(d.conclusion.succedent)>"
# — i.e. (unlike ILL) always in EXACTLY d.conclusion.antecedent's own order,
# since that order is already the semantically correct one and there is
# nothing to reorder to.

def _nonempty(flat_text: str, emitter: _Emitter) -> str:
    """Emit (and return the fact name for) ``<flat_text> \\<noteq> []``.

    Used for the ``Γ ≠ []`` side condition of UnderL/UnderR/OverL/OverR
    (Lambek's restriction). ``flat_text`` is always a concrete, nonempty
    bracket-list literal here (guaranteed by
    :func:`~unicode_fol_kit.atp.lambek.check_lambek_proof`, which every
    derivation this module replays has already passed), so this is always a
    trivial, purely computational ``simp``.
    """
    return emitter.have(f'{flat_text} \\<noteq> []', [], "simp")


def _lcp_len(a: Sequence, b: Sequence) -> int:
    """Length of the longest common prefix of ``a`` and ``b``."""
    n = 0
    while n < len(a) and n < len(b) and a[n] == b[n]:
        n += 1
    return n


def _emit_lambek(d: LambekDerivation, emitter: _Emitter) -> str:
    """Recursively replay one Lambek derivation node; see the contract above."""
    concl_list = list(d.conclusion.antecedent)
    succ_isa = _lift_lambek(d.conclusion.succedent)
    rule = d.rule

    if rule == "Ax":
        return emitter.have(f'derivable {_flat_lambek(concl_list)} {succ_isa}', [], "(rule Ax)")

    if rule == "•L":
        child = d.premises[0]
        cfact = _emit_lambek(child, emitter)
        clist = list(child.conclusion.antecedent)
        i = _lcp_len(clist, concl_list)  # concl_list[i] is the Product; clist[i:i+2] = (A, B)
        g1, g2 = concl_list[:i], concl_list[i + 1:]
        a, b = clist[i], clist[i + 1]
        decomp = f"{_flat_lambek(g1)} @ {_flat_lambek([a, b])} @ {_flat_lambek(g2)}"
        premise = emitter.have(f'derivable ({decomp}) {succ_isa}', [cfact], "simp")
        concl_stmt = (f"derivable ({_flat_lambek(g1)} @ {_flat_lambek([concl_list[i]])} @ "
                     f"{_flat_lambek(g2)}) {succ_isa}")
        hraw = emitter.have(concl_stmt, [premise], "(rule ProdL)")
        return emitter.have(f'derivable {_flat_lambek(concl_list)} {succ_isa}', [hraw], "simp")

    if rule == "•R":
        c0, c1 = d.premises
        f0 = _emit_lambek(c0, emitter)
        f1 = _emit_lambek(c1, emitter)
        l0, l1 = list(c0.conclusion.antecedent), list(c1.conclusion.antecedent)
        stmt = f'derivable ({_flat_lambek(l0)} @ {_flat_lambek(l1)}) {succ_isa}'
        hraw = emitter.have(stmt, [f0, f1], "(rule ProdR)")
        return emitter.have(f'derivable {_flat_lambek(concl_list)} {succ_isa}', [hraw], "simp")

    if rule == "\\R":
        child = d.premises[0]
        cfact = _emit_lambek(child, emitter)
        csucc = _lift_lambek(child.conclusion.succedent)  # the INNER succedent B, not A\B
        clist = list(child.conclusion.antecedent)  # clist == [A] + concl_list
        a = clist[0]
        stmt = f'derivable ({_flat_lambek([a])} @ {_flat_lambek(concl_list)}) {csucc}'
        premise = emitter.have(stmt, [cfact], "simp")
        nonempty = _nonempty(_flat_lambek(concl_list), emitter)
        concl_stmt = f'derivable {_flat_lambek(concl_list)} {succ_isa}'
        return emitter.have(concl_stmt, [nonempty, premise], "(rule UnderR)")

    if rule == "/R":
        child = d.premises[0]
        cfact = _emit_lambek(child, emitter)
        csucc = _lift_lambek(child.conclusion.succedent)  # the INNER succedent B, not B/A
        clist = list(child.conclusion.antecedent)  # clist == concl_list + [A]
        a = clist[-1]
        stmt = f'derivable ({_flat_lambek(concl_list)} @ {_flat_lambek([a])}) {csucc}'
        premise = emitter.have(stmt, [cfact], "simp")
        nonempty = _nonempty(_flat_lambek(concl_list), emitter)
        concl_stmt = f'derivable {_flat_lambek(concl_list)} {succ_isa}'
        return emitter.have(concl_stmt, [nonempty, premise], "(rule OverR)")

    if rule == "\\L":
        p_arg, p_main = d.premises
        f_arg = _emit_lambek(p_arg, emitter)
        f_main = _emit_lambek(p_main, emitter)
        gamma = list(p_arg.conclusion.antecedent)
        main_list = list(p_main.conclusion.antecedent)  # D1 + [B] + D2
        d1, d2, compound = _find_split_under(concl_list, main_list, gamma,
                                             p_arg.conclusion.succedent)
        main_stmt = (f'derivable ({_flat_lambek(d1)} @ {_flat_lambek([compound.right])} @ '
                    f'{_flat_lambek(d2)}) {succ_isa}')
        main_shaped = emitter.have(main_stmt, [f_main], "simp")
        nonempty = _nonempty(_flat_lambek(gamma), emitter)
        concl_stmt = (f'derivable ({_flat_lambek(d1)} @ {_flat_lambek(gamma)} @ '
                     f'{_flat_lambek([compound])} @ {_flat_lambek(d2)}) {succ_isa}')
        hraw = emitter.have(concl_stmt, [nonempty, f_arg, main_shaped], "(rule UnderL)")
        return emitter.have(f'derivable {_flat_lambek(concl_list)} {succ_isa}', [hraw], "simp")

    if rule == "/L":
        p_arg, p_main = d.premises
        f_arg = _emit_lambek(p_arg, emitter)
        f_main = _emit_lambek(p_main, emitter)
        gamma = list(p_arg.conclusion.antecedent)
        main_list = list(p_main.conclusion.antecedent)  # D1 + [B] + D2
        d1, d2, compound = _find_split_over(concl_list, main_list, gamma,
                                            p_arg.conclusion.succedent)
        main_stmt = (f'derivable ({_flat_lambek(d1)} @ {_flat_lambek([compound.left])} @ '
                    f'{_flat_lambek(d2)}) {succ_isa}')
        main_shaped = emitter.have(main_stmt, [f_main], "simp")
        nonempty = _nonempty(_flat_lambek(gamma), emitter)
        concl_stmt = (f'derivable ({_flat_lambek(d1)} @ {_flat_lambek([compound])} @ '
                     f'{_flat_lambek(gamma)} @ {_flat_lambek(d2)}) {succ_isa}')
        hraw = emitter.have(concl_stmt, [nonempty, f_arg, main_shaped], "(rule OverL)")
        return emitter.have(f'derivable {_flat_lambek(concl_list)} {succ_isa}', [hraw], "simp")

    raise NotImplementedError(f"to_isabelle_lambek: unsupported derivation rule {rule!r}.")


def _find_split_under(concl_list: List[Node], main_list: List[Node], gamma: List[Node],
                      a_formula: Node) -> Tuple[List[Node], List[Node], Under]:
    """``\\L``: find ``(D1, D2, compound)`` with ``concl_list == D1+gamma+[compound]+D2``,
    ``main_list == D1+[compound.right]+D2``, ``compound`` an ``Under`` with
    ``compound.left == a_formula``. Exists and is unique for a valid derivation."""
    n = len(gamma)
    for k in range(0, len(concl_list) - n):
        if concl_list[k:k + n] != gamma:
            continue
        pos = k + n
        if pos >= len(concl_list):
            continue
        compound = concl_list[pos]
        if not isinstance(compound, Under) or compound.left != a_formula:
            continue
        d1, d2 = concl_list[:k], concl_list[pos + 1:]
        if main_list == d1 + [compound.right] + d2:
            return list(d1), list(d2), compound
    raise AssertionError("internal error: no consistent \\L split found")


def _find_split_over(concl_list: List[Node], main_list: List[Node], gamma: List[Node],
                     a_formula: Node) -> Tuple[List[Node], List[Node], Over]:
    """``/L``: find ``(D1, D2, compound)`` with ``concl_list == D1+[compound]+gamma+D2``,
    ``main_list == D1+[compound.left]+D2``, ``compound`` an ``Over`` with
    ``compound.right == a_formula``. Exists and is unique for a valid derivation."""
    n = len(gamma)
    for k in range(0, len(concl_list)):
        compound = concl_list[k]
        if not isinstance(compound, Over) or compound.right != a_formula:
            continue
        gstart = k + 1
        if concl_list[gstart:gstart + n] != gamma:
            continue
        d1, d2 = concl_list[:k], concl_list[gstart + n:]
        if main_list == d1 + [compound.left] + d2:
            return list(d1), list(d2), compound
    raise AssertionError("internal error: no consistent /L split found")


# ---------------------------------------------------------------------------
# Lambek public API.
# ---------------------------------------------------------------------------

def lambek_derivation_theory(derivation: LambekDerivation,
                             theory_name: str = "LambekDerivation") -> str:
    """Emit a complete, loadable Isabelle/HOL theory replaying an already-found
    (and checker-validated) :class:`~unicode_fol_kit.atp.lambek.LambekDerivation`.

    Same shape as :func:`ill_derivation_theory`: deep-embeds the Lambek type
    grammar as ``datatype lam``, defines ``derivable :: "lam list ⇒ lam ⇒ bool"``
    inductively — the **ordered** antecedent (a plain ``list``, no exchange
    rule) is the entire point of the Lambek calculus, unlike ILL's list+Exch
    workaround (see the module docstring) — and replays ``derivation`` node by
    node.

    Raises:
        ValueError: if ``derivation`` does not check
            (:func:`~unicode_fol_kit.atp.lambek.check_lambek_proof`).
    """
    if not check_lambek_proof(derivation):
        raise ValueError(
            "lambek_derivation_theory: the given LambekDerivation does not "
            "check (unicode_fol_kit.check_lambek_proof / verify_lambek_proof "
            "rejects it) — use lambek_prove/lambek_derivable to find a valid "
            "derivation first.")

    emitter = _Emitter()
    root_fact = _emit_lambek(derivation, emitter)
    wanted = list(derivation.conclusion.antecedent)
    succ_isa = _lift_lambek(derivation.conclusion.succedent)

    lines: List[str] = []
    lines.append(f"theory {theory_name}")
    lines.append("  imports Main")
    lines.append("begin")
    lines.append("")
    lines.append("(* Deep embedding + derivation REPLAY of a Lambek-calculus (L) sequent. The")
    lines.append("   toolkit's own decision procedure (unicode_fol_kit.lambek_prove) already")
    lines.append("   found this proof; this theory transcribes it into Isabelle, one intro rule")
    lines.append("   per tree node -- no automation searches for the proof. The antecedent is a")
    lines.append("   plain \"lam list\": order is the whole point of L, so unlike the ILL export")
    lines.append("   there is no exchange rule at all. *)")
    lines.append(f"(* Sequent: {derivation.conclusion} *)")
    lines.append("")
    lines.append(LAMBEK_DATATYPE)
    lines.append("")
    lines.append("inductive derivable :: \"lam list \\<Rightarrow> lam \\<Rightarrow> bool\" where")
    for i, (name, body) in enumerate(_LAMBEK_INTROS):
        prefix = "  " if i == 0 else "| "
        lines.append(f"{prefix}{name}: \"{body}\"")
    lines.append("")
    lines.append(f'lemma lambek_goal: "derivable {_flat_lambek(wanted)} {succ_isa}"')
    lines.append("proof -")
    lines.extend(emitter.lines)
    lines.append(f"  show ?thesis using {root_fact} by simp")
    lines.append("qed")
    lines.append("")
    lines.append("end")
    return "\n".join(lines) + "\n"


def to_isabelle_lambek(sequence: Iterable[Node], goal: Node,
                       theory_name: str = "LambekDerivation") -> str:
    """Run :func:`~unicode_fol_kit.atp.lambek.lambek_prove` on ``sequence ⊢ goal`` and,
    if derivable, emit a complete Isabelle/HOL theory that replays the proof
    (see :func:`lambek_derivation_theory`).

    Raises:
        ValueError: if the sequent is not derivable in L (a decision
            procedure, so this is a genuine refutation — see
            :func:`~unicode_fol_kit.atp.lambek.lambek_prove`).
        ValueError: (propagated from ``lambek_prove``) if ``sequence`` is empty
            — L requires a nonempty antecedent.
    """
    seq = list(sequence)
    derivation = lambek_prove(seq, goal)
    if derivation is None:
        raise ValueError(
            f"to_isabelle_lambek: {LambekSequent(tuple(seq), goal)} is not "
            "derivable in L (lambek_prove is a decision procedure — this is "
            "a genuine refutation) — there is no derivation to replay.")
    return lambek_derivation_theory(derivation, theory_name=theory_name)
