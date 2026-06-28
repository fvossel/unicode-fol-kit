"""Three-valued (Kleene K3 / Priest LP) propositional logic -> HOL export.

A many-valued *shallow semantical embedding* (SSE) in the Benzmueller/Steen
style: the three Kleene truth values are reified as a three-element HOL type,
the connectives are defined as total functions over that type matching the
**strong-Kleene** truth tables, and *validity* is "the formula's value is
**designated** under every valuation". The designated set is the single knob
distinguishing the two logics:

    K3 (strong Kleene)  designates {T}
    LP (Priest)         designates {T, B}      (B = "both"/paradoxical)

so the same connective tables yield the headline contrasts. The most-quoted
slogans need care, and were verified against the toolkit's own evaluator:

* The law of excluded middle ``P ∨ ¬P`` is **K3-invalid** but **LP-valid**.
* In fact K3 has **no valid formulas at all**: assigning every atom B makes any
  formula evaluate to B, which is not K3-designated — so even ``P → P`` and the
  explosion-as-an-implication ``(P ∧ ¬P) → Q`` are K3-invalid. LP, designating
  B, validates every classical tautology.
* The real **paraconsistency** split is about *entailment*, not validity:
  ``[P, ¬P] ⊨ Q`` holds in K3 (vacuously) but FAILS in LP. The
  ``*_entailment`` exports capture this; the validity exports capture the rest.

This module is the HOL/THF *partner* of the toolkit's own decision procedure
:mod:`unicode_fol_kit.semantics.manyvalued` (``kleene_value`` / ``is_valid`` over
the chain ``{0.0, 0.5, 1.0}`` with ``DESIGNATED = {K3:{1.0}, LP:{0.5,1.0}}``).
The emitted truth tables are byte-for-byte the same truth functions; the test
suite cross-checks the emitted semantics against that evaluator on a battery.

Truth-value reification.  We declare an uninterpreted HOL base type ``tv`` with
three named constants ``tT`` (true), ``tB`` (both/undefined), ``tF`` (false),
plus axioms that they are pairwise distinct and **exhaust** ``tv``
(``! [X] : (X = tT | X = tB | X = tF)``). That makes ``tv`` a genuine
3-element type, so a higher-order ATP (Leo-III / Satallax) or Isabelle can
finitely enumerate every valuation. Propositional letters become
``! [P_p: tv] : ...`` -bound valuation variables; ``eval`` of the formula is a
``tv``-valued term built from the connective functions; the conjecture is
``! [valuation] : des @ eval(formula)``, which is a **Theorem** exactly when the
formula is K3/LP-valid (under the chosen ``system``).

Honesty / scope.  The toolkit *emits* a problem/theory; it does **not** run
Leo-III, Satallax, Isabelle, or Sledgehammer. Propositional K3 and LP are
**decidable** (finite truth tables), so the emitted problem is in principle
fully dischargeable by any sound+complete HOL prover (and the cross-check here
*does* decide it via the toolkit's own enumerator). This module covers the
**propositional** fragment only: quantifiers and all modal / Łukasiewicz /
sorted / lambda nodes are out of scope and raise ``NotImplementedError`` —
exactly the nodes ``kleene_value`` itself rejects, plus ``Quantifier`` (a
first-order three-valued validity problem is not a finite truth table and is
not handled by this propositional export).

Public API: :func:`to_thf_k3lp`, :func:`to_isabelle_k3lp`,
:func:`to_thf_k3lp_entailment`, :func:`to_isabelle_k3lp_entailment`,
and the constant :data:`SYSTEMS`.
"""

from typing import List

from ..fol.nodes import (
    Node, Atom, Not, And, Or, Xor, Implies, Iff, Quantifier,
    Variable, Constant, Number, Function,
)

# The two systems and their designated-value sets, kept in lock-step with
# unicode_fol_kit.semantics.manyvalued.DESIGNATED. K3 designates only "true";
# LP designates "true" and "both".
SYSTEMS = ("K3", "LP")


def _check_system(system: str) -> str:
    if system not in SYSTEMS:
        raise ValueError(
            f"Unknown three-valued system {system!r}; choose one of {list(SYSTEMS)} "
            "(K3 designates {T}; LP designates {T, B})."
        )
    return system


def _check_propositional(formula: Node) -> None:
    """Reject any node outside the propositional {¬,∧,∨,⊕,→,↔} fragment.

    Recurses the *connective* structure only, treating an ``Atom`` as a leaf:
    an atom's term arguments (Variable/Constant/Number/Function — e.g. the ``a``
    in ``P(a)``) are legitimate and are not inspected; an atom is just a key into
    the valuation.

    Mirrors the rejection surface of ``kleene_value`` (Łukasiewicz / sorted /
    lambda / modal nodes have no strong-Kleene reading) and additionally rejects
    ``Quantifier`` and bare terms: this export is the *propositional* K3/LP
    embedding, whose validity is a finite truth table. A quantified three-valued
    validity problem is not handled here.
    """
    if isinstance(formula, Atom):
        return
    if isinstance(formula, Not):
        _check_propositional(formula.formula)
        return
    if isinstance(formula, (And, Or, Xor, Implies, Iff)):
        _check_propositional(formula.left)
        _check_propositional(formula.right)
        return
    if isinstance(formula, Quantifier):
        raise NotImplementedError(
            "to_*_k3lp: Quantifier is outside the propositional K3/LP export; "
            "three-valued first-order validity is not a finite truth table. "
            "Use unicode_fol_kit.semantics.manyvalued.is_valid with a domain instead."
        )
    if isinstance(formula, (Variable, Constant, Number, Function)):
        raise NotImplementedError(
            f"to_*_k3lp: {type(formula).__name__} is a term, not a propositional formula."
        )
    raise NotImplementedError(
        f"to_*_k3lp: {type(formula).__name__} is not in the propositional K3/LP "
        "fragment {¬, ∧, ∨, ⊕, →, ↔}; this export has no three-valued reading "
        "for it (see unicode_fol_kit.semantics.manyvalued for the supported nodes)."
    )


# ---------------------------------------------------------------------------
# Atom keys -> THF / Isabelle valuation-variable names
# ---------------------------------------------------------------------------
#
# An *atom* of the propositional formula is keyed by its canonical
# ``to_unicode_str()`` rendering — EXACTLY the key the toolkit's evaluator uses
# (``valuation[atom.to_unicode_str()]``). Distinct atoms become distinct
# universally-quantified ``tv`` valuation variables.

def _atom_keys(formula: Node) -> List[str]:
    """Distinct atom keys (canonical ``to_unicode_str``) in first-seen order."""
    keys: List[str] = []
    seen = set()
    for atom in formula.atoms():
        key = atom.to_unicode_str()
        if key not in seen:
            seen.add(key)
            keys.append(key)
    return keys


def _safe_name(key: str) -> str:
    """Turn an atom key into a safe alnum/underscore suffix for a variable name."""
    return "".join(c if (c.isalnum() or c == "_") else "_" for c in key)


def _assign_var_names(keys: List[str]) -> dict:
    """Map each atom key to a distinct uppercase THF/Isabelle variable name.

    ``P(a)`` -> ``V_P_A`` etc.; on a collision after sanitisation a numeric
    suffix is appended so distinct atoms never share a valuation variable.
    """
    names_by_key = {}
    used = set()
    for key in keys:
        base = "V_" + _safe_name(key)
        base = base.upper()
        name = base
        i = 0
        while name in used:
            i += 1
            name = f"{base}_{i}"
        used.add(name)
        names_by_key[key] = name
    return names_by_key


# ===========================================================================
# (A) THF export
# ===========================================================================
#
# Type tv with three exhaustive, pairwise-distinct constants; connective
# functions matching the strong-Kleene tables; a parameterised ``des``.

# Strong-Kleene tables, emitted as one ground equation per truth-table cell over
# the THREE constants. Order on tv: tF < tB < tT (mirrors 0.0 < 0.5 < 1.0).
#   neg: 1 - x          -> tT|->tF, tB|->tB, tF|->tT
#   and: min            ;  or: max
#   imp: max(1-a, b)    ;  iff: min(a->b, b->a)
#   xor: min(max(a,b), 1-min(a,b))
# The cell values are computed in Python from EXACTLY the toolkit's strong-Kleene
# arithmetic (see _neg / _binop below), so the emitted tables cannot drift from
# unicode_fol_kit.semantics.manyvalued — the test suite cross-checks every cell.

# tv constants in increasing order, paired with the toolkit's float chain.
_TV = [("tF", 0.0), ("tB", 0.5), ("tT", 1.0)]
_FLOAT_TO_TV = {v: name for name, v in _TV}
_VALUES = (0.0, 0.5, 1.0)


def _designated_floats(system: str):
    """The designated truth-value set as floats (mirrors manyvalued.DESIGNATED)."""
    return {1.0} if system == "K3" else {1.0, 0.5}


def _eval_float(node: Node, asg: dict) -> float:
    """Strong-Kleene value of a propositional ``node`` under a float valuation.

    Uses the SAME ``_neg``/``_binop`` arithmetic that generates the emitted
    tables, so a validity decision taken here is exactly the one the emitted
    problem encodes. Used only to choose, at emit time, whether the Isabelle
    lemma should assert validity or its refutation (keeping the theory loadable).
    """
    if isinstance(node, Atom):
        return asg[node.to_unicode_str()]
    if isinstance(node, Not):
        return _neg(_eval_float(node.formula, asg))
    binmap = {And: "kand", Or: "kor", Xor: "kxor", Implies: "kimp", Iff: "kiff"}
    for cls, fn in binmap.items():
        if isinstance(node, cls):
            return _binop(fn, _eval_float(node.left, asg),
                          _eval_float(node.right, asg))
    raise NotImplementedError(type(node).__name__)


def _is_valid_internal(formula: Node, system: str) -> bool:
    """Decide K3/LP validity of ``formula`` via the embedded tables (emit-time)."""
    from itertools import product as _product
    designated = _designated_floats(system)
    keys = _atom_keys(formula)
    for combo in _product(_VALUES, repeat=len(keys)):
        if _eval_float(formula, dict(zip(keys, combo))) not in designated:
            return False
    return True


def _entails_internal(premises, conclusion, system: str) -> bool:
    """Decide K3/LP entailment via the embedded tables (emit-time)."""
    from itertools import product as _product
    designated = _designated_floats(system)
    keys: List[str] = []
    seen = set()
    for f in [*premises, conclusion]:
        for k in _atom_keys(f):
            if k not in seen:
                seen.add(k)
                keys.append(k)
    for combo in _product(_VALUES, repeat=len(keys)):
        asg = dict(zip(keys, combo))
        if all(_eval_float(p, asg) in designated for p in premises):
            if _eval_float(conclusion, asg) not in designated:
                return False
    return True


def _neg(a: float) -> float:
    return 1.0 - a


def _binop(name: str, a: float, b: float) -> float:
    if name == "kand":
        return min(a, b)
    if name == "kor":
        return max(a, b)
    if name == "kimp":
        return max(1.0 - a, b)
    if name == "kiff":
        return min(max(1.0 - a, b), max(1.0 - b, a))
    if name == "kxor":
        return min(max(a, b), 1.0 - min(a, b))
    raise AssertionError(name)


_THF_BINOPS = ("kand", "kor", "kimp", "kiff", "kxor")

# The connectives are pinned by one ground equation per truth-table cell (3 for
# the unary kneg, 9 for each binary op) rather than a `$ite` lambda: ground
# equations over the three distinct constants are the most portable THF idiom
# and need no conditional/`$ite` support from the prover. With tv_distinct and
# tv_exhaust, these equations TOTALLY determine each function on tv.


def _thf_neg_axioms() -> List[str]:
    """One THF equation per cell of the unary kneg table."""
    lines = []
    for name, v in _TV:
        out = _FLOAT_TO_TV[_neg(v)]
        lines.append(
            f"thf(kneg_{name}, axiom, ( ( kneg @ {name} ) = {out} )).")
    return lines


def _thf_binop_axioms(name: str) -> List[str]:
    """One THF equation per cell of a binary connective's 9-cell table."""
    lines = []
    for an, av in _TV:
        for bn, bv in _TV:
            out = _FLOAT_TO_TV[_binop(name, av, bv)]
            lines.append(
                f"thf({name}_{an}_{bn}, axiom, "
                f"( ( {name} @ {an} @ {bn} ) = {out} )).")
    return lines


def _thf_designated_axiom(system: str) -> str:
    """The ``des : tv > $o`` predicate fixing the designated set for ``system``."""
    if system == "K3":
        body = "( D = tT )"
    else:  # LP
        body = "( ( D = tT ) | ( D = tB ) )"
    return f"thf(des_def, definition, ( des = ( ^ [D: tv] : {body} ) ))."


_THF_TV_PREAMBLE = """\
thf(tv_type, type, ( tv : $tType )).
thf(tT_decl, type, ( tT : tv )).
thf(tB_decl, type, ( tB : tv )).
thf(tF_decl, type, ( tF : tv )).
thf(des_decl, type, ( des : ( tv > $o ) )).
thf(kneg_decl, type, ( kneg : ( tv > tv ) )).
thf(kand_decl, type, ( kand : ( tv > tv > tv ) )).
thf(kor_decl, type, ( kor : ( tv > tv > tv ) )).
thf(kimp_decl, type, ( kimp : ( tv > tv > tv ) )).
thf(kiff_decl, type, ( kiff : ( tv > tv > tv ) )).
thf(kxor_decl, type, ( kxor : ( tv > tv > tv ) )).
thf(tv_distinct, axiom, ( ( tT != tB ) & ( tT != tF ) & ( tB != tF ) )).
thf(tv_exhaust, axiom, ( ! [X: tv] : ( ( X = tT ) | ( X = tB ) | ( X = tF ) ) )).\
"""


def _thf_eval(node: Node, names_by_key: dict) -> str:
    """Render the formula as a ``tv``-valued THF term using the connective fns."""
    if isinstance(node, Atom):
        return names_by_key[node.to_unicode_str()]
    if isinstance(node, Not):
        return f"( kneg @ {_thf_eval(node.formula, names_by_key)} )"
    binmap = {And: "kand", Or: "kor", Xor: "kxor", Implies: "kimp", Iff: "kiff"}
    for cls, fn in binmap.items():
        if isinstance(node, cls):
            return (f"( {fn} @ {_thf_eval(node.left, names_by_key)} "
                    f"@ {_thf_eval(node.right, names_by_key)} )")
    raise NotImplementedError(
        f"to_thf_k3lp: unsupported node {type(node).__name__}.")


def to_thf_k3lp(formula: Node, system: str = "K3") -> str:
    """Emit a complete THF problem whose theorem-hood is K3/LP validity of ``formula``.

    Builds a self-contained TPTP **THF** problem: a 3-element truth-value type
    ``tv`` (constants ``tT``/``tB``/``tF``, distinctness + exhaustiveness
    axioms), the strong-Kleene connective functions ``kneg``/``kand``/``kor``/
    ``kimp``/``kiff``/``kxor`` defined by full case analysis, the designated
    predicate ``des`` (``{T}`` for K3, ``{T, B}`` for LP), and the conjecture
    ``! [valuation] : des @ ⟨formula⟩`` where each propositional atom is a
    universally-quantified ``tv`` valuation variable. The conjecture is a
    **Theorem** iff ``formula`` is valid in ``system``.

    Propositional fragment only (``¬ ∧ ∨ ⊕ → ↔``); a ``Quantifier`` or any
    modal/Łukasiewicz/sorted/lambda node raises ``NotImplementedError``.

    Note: the toolkit emits this problem; it does **not** run a prover.
    Propositional K3/LP are decidable, so a sound+complete HOL ATP (Leo-III,
    Satallax) can discharge it.
    """
    _check_system(system)
    _check_propositional(formula)
    keys = _atom_keys(formula)
    names_by_key = _assign_var_names(keys)

    lines = [
        f"% Strong-Kleene three-valued SSE of a propositional formula (system={system}).",
        f"% Designated set: {'{T}' if system == 'K3' else '{T, B}'}. "
        "Conjecture is 'Theorem' iff the formula is valid in this system.",
        f"% Formula: {formula.to_unicode_str()}",
        _THF_TV_PREAMBLE,
    ]
    lines += _thf_neg_axioms()
    for op in _THF_BINOPS:
        lines += _thf_binop_axioms(op)
    lines.append(_thf_designated_axiom(system))

    body = _thf_eval(formula, names_by_key)
    if keys:
        binder = ", ".join(f"{names_by_key[k]}: tv" for k in keys)
        conj = f"! [{binder}] : ( des @ {body} )"
    else:
        conj = f"( des @ {body} )"
    lines.append(f"thf(goal, conjecture, ( {conj} )).")
    return "\n".join(lines) + "\n"


def to_thf_k3lp_entailment(premises, conclusion, system: str = "K3") -> str:
    """Emit a THF problem whose theorem-hood is the K3/LP *entailment* of ``conclusion`` by ``premises``.

    Designation-preserving entailment: ``premises ⊨ conclusion`` iff every
    valuation that designates **all** premises also designates the conclusion.
    The conjecture is ``! [valuation] : ( (des p1 & ... & des pn) => des c )``.

    This is where K3 and LP diverge: the explosion ``[P, ¬P] ⊨ Q`` is a
    **Theorem** under K3 (vacuously — P and ¬P are never jointly designated) but
    **not** under LP (at P = B the premises are designated yet Q may be F), so LP
    is paraconsistent. Mirrors
    :func:`unicode_fol_kit.semantics.manyvalued.entails`.

    Same propositional fragment and rejection surface as :func:`to_thf_k3lp`.
    """
    _check_system(system)
    premises = list(premises)
    for f in premises:
        _check_propositional(f)
    _check_propositional(conclusion)

    keys: List[str] = []
    seen = set()
    for f in [*premises, conclusion]:
        for k in _atom_keys(f):
            if k not in seen:
                seen.add(k)
                keys.append(k)
    names_by_key = _assign_var_names(keys)

    lines = [
        f"% Strong-Kleene three-valued entailment (system={system}).",
        f"% Designated set: {'{T}' if system == 'K3' else '{T, B}'}. "
        "Conjecture is 'Theorem' iff the premises entail the conclusion.",
        "% Premises: " + ("; ".join(p.to_unicode_str() for p in premises) or "(none)"),
        f"% Conclusion: {conclusion.to_unicode_str()}",
        _THF_TV_PREAMBLE,
    ]
    lines += _thf_neg_axioms()
    for op in _THF_BINOPS:
        lines += _thf_binop_axioms(op)
    lines.append(_thf_designated_axiom(system))

    concl = f"( des @ {_thf_eval(conclusion, names_by_key)} )"
    if premises:
        prem = " & ".join(f"( des @ {_thf_eval(p, names_by_key)} )" for p in premises)
        matrix = f"( ( {prem} ) => {concl} )"
    else:
        matrix = concl
    if keys:
        binder = ", ".join(f"{names_by_key[k]}: tv" for k in keys)
        conj = f"! [{binder}] : {matrix}"
    else:
        conj = matrix
    lines.append(f"thf(goal, conjecture, ( {conj} )).")
    return "\n".join(lines) + "\n"


# ===========================================================================
# (B) Isabelle/HOL export
# ===========================================================================
#
# A self-contained, loadable theory: a datatype with three constructors,
# primrec/definitions for the connectives matching the strong-Kleene tables,
# the designated predicate, and a lemma that is provable iff the formula is
# K3/LP-valid. Discharge with ``by eval`` / ``by (cases ...)`` / Sledgehammer.

_ISA_DATATYPE = "datatype tv = tT | tB | tF"


def _isa_neg_def() -> str:
    eqs = []
    for name, v in _TV:
        eqs.append(f'  "kneg {name} = {_FLOAT_TO_TV[_neg(v)]}"')
    return "fun kneg :: \"tv \\<Rightarrow> tv\" where\n" + " |\n".join(eqs)


def _isa_binop_def(name: str, isa_name: str) -> str:
    eqs = []
    for an, av in _TV:
        for bn, bv in _TV:
            out = _FLOAT_TO_TV[_binop(name, av, bv)]
            eqs.append(f'  "{isa_name} {an} {bn} = {out}"')
    return (f"fun {isa_name} :: \"tv \\<Rightarrow> tv \\<Rightarrow> tv\" where\n"
            + " |\n".join(eqs))


_ISA_BINOPS = [
    ("kand", "kand"), ("kor", "kor"), ("kimp", "kimp"),
    ("kiff", "kiff"), ("kxor", "kxor"),
]


def _isa_designated_def(system: str) -> str:
    if system == "K3":
        rhs = "(d = tT)"
    else:
        rhs = "(d = tT \\<or> d = tB)"
    return ("definition des :: \"tv \\<Rightarrow> bool\" where\n"
            f"  \"des d \\<equiv> {rhs}\"")


def _isa_eval(node: Node, names_by_key: dict) -> str:
    if isinstance(node, Atom):
        return names_by_key[node.to_unicode_str()].lower()
    if isinstance(node, Not):
        return f"(kneg {_isa_eval(node.formula, names_by_key)})"
    binmap = {And: "kand", Or: "kor", Xor: "kxor", Implies: "kimp", Iff: "kiff"}
    for cls, fn in binmap.items():
        if isinstance(node, cls):
            return (f"({fn} {_isa_eval(node.left, names_by_key)} "
                    f"{_isa_eval(node.right, names_by_key)})")
    raise NotImplementedError(
        f"to_isabelle_k3lp: unsupported node {type(node).__name__}.")


def _isa_prelude(theory_name: str, system: str, header_comments: List[str]) -> List[str]:
    """The shared theory header: datatype, connective funs, des definition.

    Returns the lines from ``theory ... begin`` down to (and including) the
    ``des`` definition; the caller appends its lemma(s) and the final ``end``.
    """
    parts = [
        f"theory {theory_name}",
        "  imports Main",
        "begin",
        "",
    ]
    parts += header_comments
    parts += ["", _ISA_DATATYPE, "", _isa_neg_def(), ""]
    for name, isa_name in _ISA_BINOPS:
        parts.append(_isa_binop_def(name, isa_name))
        parts.append("")
    parts.append(_isa_designated_def(system))
    parts.append("")
    return parts


def _isa_forall_proof(isa_vars: List[str]) -> str:
    """Discharge ``\\<forall>vars. des (...)`` by exhausting the finite ``tv`` cases.

    ``simp`` cannot reduce ``kneg v`` / ``kor v ...`` while ``v`` is an abstract
    variable, so a bare ``by (simp add: des_def)`` fails (e.g. on the LP-valid
    ``p \\<or> \\<not>p``). Splitting every quantified variable into its three
    constructors first makes each leaf ground, and ``simp_all`` then evaluates the
    ``fun`` tables.
    """
    if not isa_vars:
        return "  by (simp add: des_def)"
    cases = "; ".join(f"case_tac {v}" for v in isa_vars)
    return ("  apply (intro allI)\n"
            f"  apply ({cases})\n"
            "  by (simp_all add: des_def)")


def _isa_exists_proof(witness: List[str]) -> str:
    """Discharge ``\\<exists>vars. \\<not> des (...)`` by supplying the witness.

    ``witness`` is the counter-valuation (a ``tv`` constructor per quantified
    variable, in binder order) computed at emit time; each ``rule exI`` instantiates
    one existential, then ``simp`` evaluates the now-ground body.
    """
    if not witness:
        return "  by (simp add: des_def)"
    exs = ", ".join(f"rule exI[where x={w}]" for w in witness)
    return f"  by ({exs}, simp add: des_def)"


def _falsifying_assignment(formula: Node, system: str, keys: List[str]):
    """A ``tv``-name valuation (in ``keys`` order) making ``formula`` non-designated."""
    from itertools import product as _product
    designated = _designated_floats(system)
    for combo in _product(_VALUES, repeat=len(keys)):
        if _eval_float(formula, dict(zip(keys, combo))) not in designated:
            return [_FLOAT_TO_TV[v] for v in combo]
    return None


def _entailment_countermodel(premises, conclusion, system: str, keys: List[str]):
    """A ``tv``-name valuation designating all premises but not the conclusion."""
    from itertools import product as _product
    designated = _designated_floats(system)
    for combo in _product(_VALUES, repeat=len(keys)):
        asg = dict(zip(keys, combo))
        if (all(_eval_float(p, asg) in designated for p in premises)
                and _eval_float(conclusion, asg) not in designated):
            return [_FLOAT_TO_TV[v] for v in combo]
    return None


def to_isabelle_k3lp(formula: Node, system: str = "K3") -> str:
    """Emit a complete, loadable Isabelle/HOL theory text for K3/LP validity.

    Produces a ``theory ... begin ... end`` snippet: a three-constructor
    ``datatype tv = tT | tB | tF``, ``fun`` definitions of the strong-Kleene
    connectives, the ``des`` designated predicate (``{T}`` for K3, ``{T, B}``
    for LP), and a ``lemma`` that **always loads**:

      * if ``formula`` is valid in ``system``, the lemma is
        ``\\<forall> valuation. des (⟨formula⟩)`` (the validity statement);
      * if it is **invalid**, the lemma is the *refutation*
        ``\\<exists> valuation. \\<not> des (⟨formula⟩)`` (which then holds).

    Either way the lemma encodes the validity verdict and is **discharged by a real
    proof** that Isabelle accepts: the ``\\<forall>`` form by exhausting each
    quantified variable's three ``tv`` constructors (``case_tac`` + ``simp_all``,
    since ``simp`` alone cannot reduce ``kneg v`` while ``v`` is abstract — e.g. the
    LP-valid ``p \\<or> \\<not>p``); the ``\\<exists>`` refutation form by supplying
    the counter-valuation as ``rule exI`` witnesses (computed at emit time) and then
    ``simp``. The verdict itself is computed at emit time from the embedded tables
    (``_is_valid_internal``), which the tests pin to ``manyvalued.is_valid``. A
    leading comment states the verdict so the reader knows which form was emitted.

    Propositional fragment only; ``Quantifier`` / modal / Łukasiewicz / sorted /
    lambda nodes raise ``NotImplementedError``.

    Note: the toolkit emits the theory; it does **not** run Isabelle. The
    cross-check against the toolkit's own decision procedure lives in the tests.
    """
    _check_system(system)
    _check_propositional(formula)
    keys = _atom_keys(formula)
    names_by_key = _assign_var_names(keys)
    isa_vars = [names_by_key[k].lower() for k in keys]

    valid = _is_valid_internal(formula, system)
    body = _isa_eval(formula, names_by_key)
    if keys:
        binder = " ".join(isa_vars)
        if valid:
            lemma = f"  \"\\<forall>{binder}. des ({body})\""
            proof = _isa_forall_proof(isa_vars)
        else:
            lemma = f"  \"\\<exists>{binder}. \\<not> des ({body})\""
            proof = _isa_exists_proof(_falsifying_assignment(formula, system, keys))
    else:
        lemma = f"  \"des ({body})\"" if valid else f"  \"\\<not> des ({body})\""
        proof = "  by (simp add: des_def)"

    verdict = "VALID" if valid else "INVALID (lemma is the refutation)"
    header = [
        f"(* Strong-Kleene three-valued SSE of a propositional formula. system={system}. *)",
        f"(* Designated set: {'{T}' if system == 'K3' else '{T, B}'}. "
        f"Verdict: {verdict}. *)",
        f"(* Formula: {formula.to_unicode_str()} *)",
    ]
    parts = _isa_prelude("K3LP_Validity", system, header)
    parts.append("lemma k3lp_validity:")
    parts.append(lemma)
    parts.append(proof)
    parts.append("")
    parts.append("end")
    return "\n".join(parts) + "\n"


def to_isabelle_k3lp_entailment(premises, conclusion, system: str = "K3") -> str:
    """Emit a loadable Isabelle/HOL theory whose lemma is the K3/LP entailment.

    Emits a lemma that **always loads**, mirroring
    :func:`unicode_fol_kit.semantics.manyvalued.entails`:

      * if ``premises ⊨ conclusion`` in ``system``, the lemma is
        ``\\<forall> valuation. (des p1 \\<and> ... ) \\<longrightarrow> des c``;
      * otherwise it is the countermodel statement
        ``\\<exists> valuation. (des p1 \\<and> ... ) \\<and> \\<not> des c``.

    The K3/LP split shows up here — explosion ``[P, ¬P] ⊨ Q`` is valid under K3
    (so the first form) but invalid under LP (so the countermodel form). The
    verdict is computed at emit time from the embedded tables.

    Same propositional fragment and rejection surface as :func:`to_isabelle_k3lp`.
    """
    _check_system(system)
    premises = list(premises)
    for f in premises:
        _check_propositional(f)
    _check_propositional(conclusion)

    keys: List[str] = []
    seen = set()
    for f in [*premises, conclusion]:
        for k in _atom_keys(f):
            if k not in seen:
                seen.add(k)
                keys.append(k)
    names_by_key = _assign_var_names(keys)
    isa_vars = [names_by_key[k].lower() for k in keys]

    valid = _entails_internal(premises, conclusion, system)
    concl = f"des ({_isa_eval(conclusion, names_by_key)})"
    if premises:
        prem = " \\<and> ".join(
            f"des ({_isa_eval(p, names_by_key)})" for p in premises)
        if valid:
            matrix = f"({prem}) \\<longrightarrow> {concl}"
        else:
            matrix = f"({prem}) \\<and> \\<not> {concl}"
    else:
        matrix = concl if valid else f"\\<not> {concl}"
    if keys:
        binder = " ".join(isa_vars)
        q = "\\<forall>" if valid else "\\<exists>"
        lemma = f"  \"{q}{binder}. {matrix}\""
        if valid:
            proof = _isa_forall_proof(isa_vars)
        else:
            proof = _isa_exists_proof(
                _entailment_countermodel(premises, conclusion, system, keys))
    else:
        lemma = f"  \"{matrix}\""
        proof = "  by (simp add: des_def)"

    verdict = "ENTAILS" if valid else "DOES NOT ENTAIL (lemma is a countermodel)"
    header = [
        f"(* Strong-Kleene three-valued entailment. system={system}. *)",
        f"(* Designated set: {'{T}' if system == 'K3' else '{T, B}'}. "
        f"Verdict: {verdict}. *)",
        "(* Premises: " + ("; ".join(p.to_unicode_str() for p in premises) or "(none)") + " *)",
        f"(* Conclusion: {conclusion.to_unicode_str()} *)",
    ]
    parts = _isa_prelude("K3LP_Entailment", system, header)
    parts.append("lemma k3lp_entailment:")
    parts.append(lemma)
    parts.append(proof)
    parts.append("")
    parts.append("end")
    return "\n".join(parts) + "\n"
