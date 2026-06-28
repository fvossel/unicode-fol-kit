"""Intuitionistic propositional logic → HOL, via the Gödel–McKinsey–Tarski (GMT)
box-translation into modal **S4** composed with the alethic shallow embedding.

Intuitionistic propositional logic (IPL) has no truth-functional semantics, but
Gödel (1933) and McKinsey–Tarski (1948) showed it embeds *faithfully* into the
modal logic **S4**: a propositional formula ``A`` is intuitionistically valid iff
its box-translation ``T(A)`` is S4-valid. The translation prefixes ``□`` exactly
where the intuitionistic clauses quantify over future worlds:

    T(p)      = □p                 (atoms are "stable" — forced henceforth)
    T(¬A)     = □¬T(A)
    T(A ∧ B)  = T(A) ∧ T(B)
    T(A ∨ B)  = T(A) ∨ T(B)
    T(A → B)  = □(T(A) → T(B))

(``A ↔ B`` and ``A ⊕ B`` are first expanded to their ∧/∨/→/¬ definitions —
matching the very clauses :meth:`IntKripkeModel.forces` uses — and then translated.)

FALSUM. The textbook GMT rule is ``T(⊥)=⊥`` with ``⊥`` a *genuine* logical constant.
This toolkit, however, has **no primitive propositional falsum**: the reserved atom
``"⊥"`` (``unicode_fol_kit.atp.fitch.FALSUM``) is, for the intuitionistic Kripke
evaluator :func:`unicode_fol_kit.semantics.intuitionistic.int_valid`, an *ordinary
propositional variable* (its forcing clause is the plain atom clause — ``int_valid``
has no ⊥-is-false rule; e.g. ``⊥→p`` and ``¬⊥`` both come out invalid). To stay
**faithful to** ``int_valid`` — the ground truth this module cross-checks against —
the box-translation here treats ``⊥`` like any other atom: ``T(⊥)=□⊥``. If you want
the textbook *genuine-falsum* reading instead, rewrite ⊥ to a contradiction
(``p ∧ ¬p``) before translating, exactly as the Fitch checker's ``_desugar_falsum``
does for its classical oracle. See :func:`gmt_translate` and the ``caveats``.

The resulting S4 modal formula is handed to the existing alethic SSE
(:mod:`unicode_fol_kit.fol.qml`) with an **S4 frame** (reflexive + transitive),
so the emitted THF problem / Isabelle theory is a *Theorem* exactly when the
original formula is intuitionistically valid. The accessibility relation ``r`` of
S4 is precisely the intuitionistic "≥" pre-order, and the GMT box mirrors the
"for every later world" quantifier of the ``→``/``¬`` forcing clauses; this is why
``p ∨ ¬p``, ``¬¬p → p`` and Peirce's law come out **non-theorems**, while
``p → ¬¬p`` and the constructive tautologies are theorems.

HONESTY. This module only *emits* a HOL problem/theory; it does not run Isabelle,
Leo-III, Satallax or Sledgehammer. IPL is decidable (finite model property —
which is what :func:`unicode_fol_kit.semantics.intuitionistic.int_valid` exploits),
and propositional S4 is decidable, so a HOL prover *can* discharge every emitted
conjecture; but the SSE target is full HOL, whose theorem-hood is only
semi-decidable, so an external prover may time out. The cross-checking function
:func:`gmt_validity_matches_int_valid` does not need an external prover: it compares
:func:`int_valid` against the toolkit's *own* S4-validity of the translation
(:func:`unicode_fol_kit.fol.qml.qml_is_valid` under an S4 frame, decided by Z3 — the
fragment is propositional, hence decidable), so the GMT correctness claim is verified
end-to-end inside the toolkit.

Public API: :func:`gmt_translate`, :func:`to_thf_intuitionistic`,
:func:`to_isabelle_intuitionistic`, :func:`gmt_is_s4_valid`,
:func:`gmt_validity_matches_int_valid`.
"""

from unicode_fol_kit.fol.nodes import (
    Node, Atom, Not, And, Or, Xor, Implies, Iff,
    Box, Quantifier, SortedQuantifier,
)
from unicode_fol_kit.fol._so_nodes import SecondOrderQuantifier
from unicode_fol_kit.fol.qml import to_thf_modal


def _check_propositional(formula: Node) -> None:
    """Raise ValueError if ``formula`` is not propositional (quantifiers are out of scope).

    Mirrors :func:`unicode_fol_kit.semantics.intuitionistic._check_propositional`:
    the GMT embedding here is for *propositional* IPL, whose decidability the
    cross-check relies on. (Quantified IPL needs varying first-order domains.)
    """
    for node in formula.walk():
        if isinstance(node, (Quantifier, SortedQuantifier, SecondOrderQuantifier)):
            raise ValueError(
                "intuitionistic GMT: only propositional formulas are supported "
                "(quantified intuitionistic logic needs varying domains, out of scope)."
            )


def gmt_translate(formula: Node) -> Node:
    """Return the Gödel–McKinsey–Tarski box-translation ``T(formula)`` (a modal S4 Node).

    The result is a classical modal formula built from :class:`Box`, the Boolean
    connectives and the original atoms; it is S4-valid iff ``formula`` is
    intuitionistically valid. ``↔`` and ``⊕`` are expanded to their ∧/∨/→/¬
    definitions before translation, matching the intuitionistic forcing clauses.
    The reserved atom ``⊥`` is treated as an ordinary atom (``T(⊥)=□⊥``) to stay
    faithful to :func:`int_valid`; see the module docstring's FALSUM note.
    """
    _check_propositional(formula)
    return _gmt(formula)


def _gmt(f: Node) -> Node:
    """Core box-translation recursion (no validation; see :func:`gmt_translate`)."""
    if isinstance(f, Atom):
        return Box(f)                      # T(p) = □p  (⊥ is an ordinary atom here)
    if isinstance(f, Not):
        return Box(Not(_gmt(f.formula)))   # T(¬A) = □¬T(A)
    if isinstance(f, And):
        return And(_gmt(f.left), _gmt(f.right))         # T(A∧B) = T(A)∧T(B)
    if isinstance(f, Or):
        return Or(_gmt(f.left), _gmt(f.right))          # T(A∨B) = T(A)∨T(B)
    if isinstance(f, Implies):
        return Box(Implies(_gmt(f.left), _gmt(f.right)))  # T(A→B) = □(T(A)→T(B))
    if isinstance(f, Iff):
        # A↔B ≡ (A→B)∧(B→A) — exactly the intuitionistic forcing clause for ↔.
        return _gmt(And(Implies(f.left, f.right), Implies(f.right, f.left)))
    if isinstance(f, Xor):
        # A⊕B ≡ (A∨B)∧¬(A∧B) — the intuitionistic forcing clause for ⊕.
        a, b = f.left, f.right
        return _gmt(And(Or(a, b), Not(And(a, b))))
    raise NotImplementedError(
        f"intuitionistic GMT: unsupported node {type(f).__name__} "
        "(propositional ∧/∨/→/¬/↔/⊕/⊥ and atoms only)."
    )


def to_thf_intuitionistic(formula: Node) -> str:
    """Emit a Benzmüller-style TPTP **THF** problem whose theorem-hood ≡ IPL-validity.

    Box-translates ``formula`` (GMT) into modal S4 and embeds the result with the
    alethic shallow embedding under an S4 frame (reflexive + transitive). The
    conjecture ``mvalid @ ⟨T(formula)⟩`` is a *Theorem* (dischargeable by a HOL ATP
    such as Leo-III / Satallax) iff ``formula`` is intuitionistically valid.

    The toolkit only *emits* the problem; it does not run the prover.
    """
    return to_thf_modal(gmt_translate(formula), mode="constant", frame="S4")


# --- Isabelle/HOL rendering of the GMT-translated S4 modal formula -----------
#
# A complete, *loadable* theory (not the alethic-fragment skeleton in qml.py,
# which leaves the lemma inside a comment and defines only mnot/mbox/mvalid).
# Worlds are an opaque type ``i``; a modal proposition is ``i ⇒ bool``; the
# operators are the standard Benzmüller-style lifted abbreviations and the frame
# is fixed to S4 (``r`` reflexive + transitive) via a locale-free axiomatization
# discharged inside the lemma's assumptions, so the theory is self-contained and
# Sledgehammer/auto can attack the goal directly.

_ISA_PROP = "\\<Rightarrow>"
_ISA_NOT = "\\<^bold>\\<not>"
_ISA_AND = "\\<^bold>\\<and>"
_ISA_OR = "\\<^bold>\\<or>"
_ISA_IMP = "\\<^bold>\\<rightarrow>"
_ISA_BOX = "\\<^bold>\\<box>"


# Aliases for reserved/symbolic atoms whose char-by-char sanitisation would otherwise
# collapse to the bare reserved token '_' (Isabelle's wildcard — a theory using it as a
# consts name will NOT load) and merge distinct atoms (⊥/⊤/=/≠ all → '_'). Each alias is
# a distinct, valid lowercase identifier. (The THF path aliases these separately.)
_ISA_ATOM_ALIASES = {"⊥": "bottom", "⊤": "top", "=": "feq", "≠": "fneq"}

# Identifiers the emitted theory already uses structurally: the world type ``i``, the
# accessibility relation ``r`` and the free variables ``w``/``v``/``u`` of its frame
# axioms (``r_refl: "r w w"``, ``r_trans: "r w v ⟹ r v u ⟹ r w u"``), and the lifted
# operator names. An atom predicate that sanitised to one of these would emit a SECOND
# ``consts`` with that name (a duplicate-constant clash that Isabelle rejects — so the
# theory would not load even for a valid formula, e.g. the atom ``r`` in ``r → r``), or
# make the frame axioms ill-typed (an atom ``w`` shadowing the type-``i`` bound var).
# A colliding atom is de-collided with the ``p_`` prefix (a trailing ``_`` would be a
# *bad* Isabelle identifier).
_ISA_RESERVED = frozenset({
    "i", "r", "w", "v", "u",
    "mnot", "mand", "mor", "mimp", "mbox", "mvalid",
})


def _isa_atom_name(name: str) -> str:
    """A safe, *distinct* Isabelle constant name for an atom predicate.

    Distinct source atoms must map to distinct legal identifiers. Reserved/symbolic
    atoms (⊥, ⊤, =, ≠) are aliased to dedicated lowercase ids; everything else is
    sanitised char-by-char (alnum/underscore), a ``p_`` prefix is prepended when the
    result is empty, is the bare reserved ``_`` token, or starts with ``_`` (all of
    which are illegal or reserved as a bare Isabelle constant name), and a name that
    would collide with a structural identifier of the theory (the relation ``r``, an
    axiom variable ``w``/``v``/``u``, the world type ``i``, a lifted operator) is
    de-collided with the ``p_`` prefix (``r`` → ``p_r``).
    """
    if name in _ISA_ATOM_ALIASES:
        return _ISA_ATOM_ALIASES[name]
    safe = "".join(c if (c.isalnum() or c == "_") else "_" for c in name)
    if not safe or safe[0] == "_" or not safe[0].isalpha():
        safe = "p_" + safe
    if safe in _ISA_RESERVED:
        safe = "p_" + safe          # p_r / p_w / … (a trailing '_' is a bad Isabelle id)
    return safe


def _isa_atoms(formula: Node):
    """Distinct atom predicate names in ``formula`` (each a propositional letter)."""
    out, seen = [], set()
    for n in formula.walk():
        if isinstance(n, Atom) and n.predicate not in seen:
            seen.add(n.predicate)
            out.append(n.predicate)
    return out


def _isa_render(node: Node) -> str:
    """Render a GMT-translated S4 modal Node in Isabelle bold-operator syntax."""
    if isinstance(node, Atom):
        return _isa_atom_name(node.predicate)
    if isinstance(node, Not):
        return f"({_ISA_NOT}{_isa_render(node.formula)})"
    if isinstance(node, And):
        return f"({_isa_render(node.left)} {_ISA_AND} {_isa_render(node.right)})"
    if isinstance(node, Or):
        return f"({_isa_render(node.left)} {_ISA_OR} {_isa_render(node.right)})"
    if isinstance(node, Implies):
        return f"({_isa_render(node.left)} {_ISA_IMP} {_isa_render(node.right)})"
    if isinstance(node, Box):
        return f"({_ISA_BOX}{_isa_render(node.formula)})"
    # GMT output only ever contains Atom/Not/And/Or/Implies/Box.
    raise NotImplementedError(
        f"to_isabelle_intuitionistic: unexpected node {type(node).__name__} "
        "in the S4 translation."
    )


def to_isabelle_intuitionistic(formula: Node, theory_name: str = "IPL_GMT") -> str:
    """Emit a complete, loadable **Isabelle/HOL** theory whose lemma ≡ IPL-validity.

    Box-translates ``formula`` (GMT) into modal S4, then writes a self-contained
    theory: worlds as a type ``i``; an accessibility relation ``r`` fixed to be
    reflexive + transitive (the **S4** frame); the lifted modal operators as
    abbreviations; the atoms as ``consts``; and the embedded formula as a genuine
    ``lemma`` (``\\<lfloor> T(formula) \\<rfloor>``). The lemma is a theorem iff
    ``formula`` is intuitionistically valid (Gödel–McKinsey–Tarski).

    The proof is emitted **verdict-dependently** from the module's *decidable* S4
    oracle :func:`gmt_is_s4_valid` (Z3 on the GMT→S4 translation, decisive on this
    propositional fragment): when the formula is valid the theory carries a real,
    Isabelle-checked proof (``using r_refl r_trans by (metis … | meson … | blast |
    auto)`` — the S4 frame facts must be in scope, a bare ``axiomatization`` fact is
    not in the default claset); when it is not valid the lemma is left ``oops`` (no
    proof exists; see
    :func:`~unicode_fol_kit.semantics.intuitionistic.int_countermodel`). The decision
    deliberately does **not** use ``int_valid``'s default 3-world bound, which is
    incomplete (IPL's finite-model bound grows with the formula).

    Unlike :func:`unicode_fol_kit.fol.qml.to_isabelle_modal` (an alethic skeleton
    that puts the lemma in a comment and defines only ``mnot``/``mbox``/``mvalid``),
    this emits the full operator set and frame axioms, so the theory loads as-is.
    The toolkit only *emits* the theory; it does not run Isabelle.
    """
    s4 = gmt_translate(formula)
    # Decide validity with the module's own DECIDABLE S4 oracle (Z3 on the GMT→S4
    # translation), NOT int_valid's bounded Kripke search: int_valid defaults to a
    # 3-world bound, but IPL's finite-model-property bound grows with the formula, so
    # int_valid can wrongly call a non-theorem valid — e.g. (p→q)∨(q→r)∨(r→p) is
    # IPL-INVALID but needs 4 worlds to refute — which would emit a real proof for a
    # NON-theorem that then fails to build. gmt_is_s4_valid is decisive on this
    # propositional S4 fragment, so the emitted proof is sound by construction.
    valid = gmt_is_s4_valid(formula)
    atoms = _isa_atoms(s4)
    R = "\\<Rightarrow>"
    lines = [
        f"theory {theory_name}",
        "  imports Main",
        "begin",
        "",
        "(* Goedel--McKinsey--Tarski embedding of intuitionistic propositional logic *)",
        "(* into modal S4, then the Benzmueller shallow embedding into HOL.          *)",
        f"(* Original IPL formula:  {formula.to_unicode_str()} *)",
        "(* The lemma is a theorem iff the formula is intuitionistically valid.      *)",
        "",
        "typedecl i  \\<comment> \\<open>the type of worlds (Kripke stages)\\<close>",
        "",
        "consts r :: \"i \\<Rightarrow> i \\<Rightarrow> bool\"  \\<comment> \\<open>accessibility (the intuitionistic \\<open>\\<le>\\<close>)\\<close>",
        "",
        "axiomatization where",
        "  r_refl:  \"r w w\" and",
        "  r_trans: \"r w v \\<Longrightarrow> r v u \\<Longrightarrow> r w u\"",
        "",
        "type_synonym \\<sigma> = \"i \\<Rightarrow> bool\"  \\<comment> \\<open>a modal proposition\\<close>",
        "",
        f"abbreviation mnot :: \"\\<sigma> {R} \\<sigma>\" (\"{_ISA_NOT}_\" [52] 53)",
        "  where \"" + _ISA_NOT + "\\<phi> \\<equiv> \\<lambda>w. \\<not> \\<phi> w\"",
        f"abbreviation mand :: \"\\<sigma> {R} \\<sigma> {R} \\<sigma>\" (infixr \"{_ISA_AND}\" 51)",
        "  where \"\\<phi> " + _ISA_AND + " \\<psi> \\<equiv> \\<lambda>w. \\<phi> w \\<and> \\<psi> w\"",
        f"abbreviation mor :: \"\\<sigma> {R} \\<sigma> {R} \\<sigma>\" (infixr \"{_ISA_OR}\" 50)",
        "  where \"\\<phi> " + _ISA_OR + " \\<psi> \\<equiv> \\<lambda>w. \\<phi> w \\<or> \\<psi> w\"",
        f"abbreviation mimp :: \"\\<sigma> {R} \\<sigma> {R} \\<sigma>\" (infixr \"{_ISA_IMP}\" 49)",
        "  where \"\\<phi> " + _ISA_IMP + " \\<psi> \\<equiv> \\<lambda>w. \\<phi> w \\<longrightarrow> \\<psi> w\"",
        f"abbreviation mbox :: \"\\<sigma> {R} \\<sigma>\" (\"{_ISA_BOX}_\" [52] 53)",
        "  where \"" + _ISA_BOX + "\\<phi> \\<equiv> \\<lambda>w. \\<forall>v. r w v \\<longrightarrow> \\<phi> v\"",
        "abbreviation mvalid :: \"\\<sigma> \\<Rightarrow> bool\" (\"\\<lfloor>_\\<rfloor>\")",
        "  where \"\\<lfloor>\\<phi>\\<rfloor> \\<equiv> \\<forall>w. \\<phi> w\"",
        "",
    ]
    for a in atoms:
        lines.append(f"consts {_isa_atom_name(a)} :: \"\\<sigma>\"")
    lines.append("")
    lines.append("lemma gmt_goal: \"\\<lfloor> " + _isa_render(s4) + " \\<rfloor>\"")
    if valid:
        # A real, Isabelle-checked proof. The S4 frame facts must be brought into
        # scope (a bare `axiomatization` fact is not in the default claset), then a
        # small method battery closes the GMT goal.
        lines.append("  using r_refl r_trans")
        lines.append("  by (metis r_refl r_trans | meson r_refl r_trans | blast | auto)")
    else:
        lines.append("  \\<comment> \\<open>NOT intuitionistically valid: no proof exists "
                     "(see int_countermodel for a Kripke counter-model)\\<close>")
        lines.append("  oops")
    lines.append("")
    lines.append("end")
    return "\n".join(lines) + "\n"


def gmt_is_s4_valid(formula: Node, timeout: int = 10000) -> bool:
    """Return True iff the GMT translation ``T(formula)`` is **S4-valid**.

    Decided *inside the toolkit* by handing the modal S4 translation to the alethic
    shallow embedding under an S4 frame (reflexive + transitive) and discharging it
    with Z3 (propositional S4 is decidable — there are no object quantifiers, so the
    embedding is decidable here). By the GMT theorem this is True iff ``formula`` is
    intuitionistically valid; :func:`gmt_validity_matches_int_valid` uses it as an
    independent check of :func:`int_valid` that does not need an external HOL prover.
    Note ``qml_is_valid`` is sound but bounded-incomplete in general; on this
    propositional S4 fragment it is decisive, which the test battery pins down.
    """
    from unicode_fol_kit.fol.qml import qml_is_valid
    return qml_is_valid(gmt_translate(formula), mode="constant", frame="S4", timeout=timeout)


def gmt_validity_matches_int_valid(formula: Node, max_worlds: int = 3,
                                   timeout: int = 10000) -> bool:
    """True iff the S4-validity of ``T(formula)`` agrees with :func:`int_valid`.

    The GMT-correctness oracle: returns True when the GMT→S4 embedding pronounces
    exactly the same verdict as the toolkit's native intuitionistic decision
    procedure. (A green result is the faithfulness witness; it does not by itself
    say whether ``formula`` is valid — call :func:`int_valid` for that.)
    """
    from unicode_fol_kit.semantics.intuitionistic import int_valid
    return gmt_is_s4_valid(formula, timeout=timeout) == int_valid(formula, max_worlds=max_worlds)
