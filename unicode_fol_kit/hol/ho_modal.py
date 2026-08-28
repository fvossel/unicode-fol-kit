r"""Third-order MODAL logic → HOL: the shallow embedding, worlds made explicit.

Third-order modal logic is where a formula can say ``Positive(G)`` — a predicate
of a PROPERTY — inside a ``□``. Nothing first-order carries it and no
propositional modal calculus reaches it, but a higher-order prover does, through
the same shallow (Benzmüller-style) embedding the rest of this package uses: a
proposition is not a truth value but a FUNCTION FROM WORLDS to truth values, and
every connective is lifted to act pointwise on those functions. The modal
operators then become ordinary quantifiers over the accessibility relation, and
what a HOL prover sees is plain higher-order logic.

The three levels get three types::

    i                       individuals
    world                   worlds
    sigma = world => bool   propositions   (a "truth value" per world)
    i => sigma              properties     (the third order's argument type)
    (i => sigma) => sigma   predicates OF properties  -- e.g. Positive

and the lifted vocabulary is emitted as Isabelle ``abbreviation``\ s rather than
``definition``\ s **on purpose**: an abbreviation is unfolded by the parser, so
`blast`/`metis`/`auto` see through the embedding to plain HOL without being told
to unfold anything. A ``definition`` would hide the goal behind a constant and
turn every proof into an unfolding exercise.

``mall`` / ``mex`` are polymorphic (``('a => sigma) => sigma``), so ONE pair of
binders serves individual quantification and property quantification alike —
which is the embedding's own reason for existing: the object logic's orders are
distinguished by the TYPE at the binder, not by separate machinery.

**What this module emits, and what it does not.** It emits a self-contained
Isabelle theory (or a THF problem) — types, lifted vocabulary, the frame axioms
for the chosen system, the signature read off the formulas, the axioms, and the
goals with whatever proof text the caller supplies. It does not run a prover;
:func:`unicode_fol_kit.hol.isabelle_runner.check_theory` does that.

**Fragment.** Alethic ``□`` / ``◇`` only. The parser's third-order modal mode
accepts the whole modal family it inherits (epistemic, doxastic, deontic,
temporal, hybrid), because it is the same AST; this embedding refuses every
other family BY NAME rather than dropping it, since a silently ignored ``K_a``
would produce a theory that proves something other than what was asked. The
multi-family embeddings are :mod:`unicode_fol_kit.hol.thf_modal` and
:mod:`unicode_fol_kit.hol.isabelle_modal` — first-order, which is exactly the
trade.

**Domains.** Quantification is possibilist/constant-domain: ``mall`` ranges over
all of ``i`` at every world. That is the setting Gödel's ontological argument is
stated in, and an actualist reading would need an ``existsAt`` guard this module
deliberately does not invent for you.
"""

from dataclasses import dataclass
from typing import Dict, List, Optional, Sequence

from ..fol.nodes import (
    Node, Atom, Not, And, Or, Xor, Implies, Iff, Quantifier,
    SecondOrderQuantifier, PredicateTerm,
    Variable, Constant, Function, LambdaVar, Lambda,
    Box, Diamond,
    analyse_signatures,
)
from ..fol._ho_nodes import INDIVIDUAL
from ..fol.frames import FRAMES, resolve_frame, UnsupportedFrameCondition
from ._ho_common import (
    UnsupportedHigherOrderNode, EQUALITY,
    peel_lambdas, rename_apart, bound_pred_names, atom_predicates,
    function_symbols, free_individuals,
)


# Isabelle's ASCII escapes, spelled once.
_ALL = r"\<forall>"
_EX = r"\<exists>"
_AND = r"\<and>"
_OR = r"\<or>"
_IMP = r"\<longrightarrow>"
_NOT = r"\<not>"
_LAM = r"\<lambda>"
_FUN = r"\<Rightarrow>"
_EQUIV = r"\<equiv>"
_NEQ = r"\<noteq>"


# --------------------------------------------------------------------------
# The lifted vocabulary
# --------------------------------------------------------------------------

_DEFINITIONS = [
    'typedecl i  \\<comment> \\<open>individuals\\<close>',
    'typedecl world  \\<comment> \\<open>worlds\\<close>',
    f'type_synonym sigma = "world {_FUN} bool"'
    '  \\<comment> \\<open>a proposition: one truth value per world\\<close>',
    '',
    f'consts R :: "world {_FUN} world {_FUN} bool"'
    '  \\<comment> \\<open>accessibility\\<close>',
    '',
    '\\<comment> \\<open>Abbreviations, not definitions: the automation must see '
    'THROUGH the embedding.\\<close>',
    f'abbreviation mnot :: "sigma {_FUN} sigma"'
    f' where "mnot p {_EQUIV} {_LAM}v. {_NOT} p v"',
    f'abbreviation mand :: "sigma {_FUN} sigma {_FUN} sigma"'
    f' where "mand p q {_EQUIV} {_LAM}v. p v {_AND} q v"',
    f'abbreviation mor :: "sigma {_FUN} sigma {_FUN} sigma"'
    f' where "mor p q {_EQUIV} {_LAM}v. p v {_OR} q v"',
    f'abbreviation mimp :: "sigma {_FUN} sigma {_FUN} sigma"'
    f' where "mimp p q {_EQUIV} {_LAM}v. p v {_IMP} q v"',
    f'abbreviation miff :: "sigma {_FUN} sigma {_FUN} sigma"'
    f' where "miff p q {_EQUIV} {_LAM}v. p v = q v"',
    f'abbreviation mxor :: "sigma {_FUN} sigma {_FUN} sigma"'
    f' where "mxor p q {_EQUIV} {_LAM}v. p v {_NEQ} q v"',
    f'abbreviation mbox :: "sigma {_FUN} sigma"'
    f' where "mbox p {_EQUIV} {_LAM}v. {_ALL}u. R v u {_IMP} p u"',
    f'abbreviation mdia :: "sigma {_FUN} sigma"'
    f' where "mdia p {_EQUIV} {_LAM}v. {_EX}u. R v u {_AND} p u"',
    f'abbreviation mall :: "(\'a {_FUN} sigma) {_FUN} sigma"'
    f' where "mall P {_EQUIV} {_LAM}v. {_ALL}x. P x v"',
    f'abbreviation mex :: "(\'a {_FUN} sigma) {_FUN} sigma"'
    f' where "mex P {_EQUIV} {_LAM}v. {_EX}x. P x v"',
    f'abbreviation mvalid :: "sigma {_FUN} bool"'
    f' where "mvalid p {_EQUIV} {_ALL}v. p v"',
]


def ho_modal_definitions() -> str:
    """Return the Isabelle preamble: the three types, ``R``, and the lifted vocabulary.

    Emitted verbatim by :func:`isabelle_ho_modal_theory`; exposed separately so a
    caller writing its own theory around the same embedding can reuse exactly
    the vocabulary the kit's emitted goals are stated in.
    """
    return "\n".join(_DEFINITIONS)


# Frame condition -> its Isabelle axiom over R, universally quantified so the
# axiom is a schema about R and cannot be narrowed by a constant that happens to
# share a variable's name (see hol/isabelle_modal.py's note on that trap).
_FRAME_AXIOMS = {
    "refl": f'"{_ALL}x. R x x"',
    "sym": f'"{_ALL}x y. R x y {_IMP} R y x"',
    "trans": f'"{_ALL}x y z. R x y {_IMP} R y z {_IMP} R x z"',
    "serial": f'"{_ALL}x. {_EX}y. R x y"',
    "eucl": f'"{_ALL}x y z. R x y {_IMP} R x z {_IMP} R y z"',
    "directed": f'"{_ALL}x y z. R x y {_IMP} R x z {_IMP} ({_EX}u. R y u {_AND} R z u)"',
    "connected": f'"{_ALL}x y z. R x y {_IMP} R x z {_IMP} (R y z {_OR} R z y)"',
    "functional": f'"{_ALL}x y z. R x y {_IMP} R x z {_IMP} y = z"',
    "dense": f'"{_ALL}x y. R x y {_IMP} ({_EX}z. R x z {_AND} R z y)"',
    "shift_refl": f'"{_ALL}x y. R x y {_IMP} R y y"',
    "empty": f'"{_ALL}x y. {_NOT} R x y"',
}


def _frame_axiom_lines(frame: str) -> List[str]:
    """Return the ``axiomatization`` lines constraining ``R`` for ``frame``.

    Reads :data:`unicode_fol_kit.fol.frames.FRAMES` like every other modal route
    in the kit, so a system means the same thing here as it does there. A
    condition with no first-order definition (Löb, McKinsey, Grz) is refused
    rather than approximated: this embedding constrains ``R`` alone, and those
    three are schemas over PROPOSITIONS — carry them with
    :func:`unicode_fol_kit.hol.isabelle_modal.to_isabelle_modal`, which states
    them as schemas.
    """
    conditions = resolve_frame(frame)
    lines = []
    for condition in conditions:
        if condition not in _FRAME_AXIOMS:
            raise UnsupportedFrameCondition(
                f"ho_modal: frame condition {condition!r} (system {frame!r}) has no "
                f"first-order axiom over R; this embedding constrains R alone. "
                f"hol.isabelle_modal.to_isabelle_modal states it as a schema over "
                f"propositions instead."
            )
        lines.append(f'axiomatization where R_{condition}: {_FRAME_AXIOMS[condition]}')
    return lines


# --------------------------------------------------------------------------
# Isabelle rendering
# --------------------------------------------------------------------------


def _prop_type(arity: int) -> str:
    """Return the Isabelle type of a property of ``arity`` arguments: ``i => … => sigma``."""
    return "".join(f"i {_FUN} " for _ in range(arity)) + "sigma"


def _isa_arg(node: Node, bound_arity: Dict[str, int],
             display: Dict[str, str]) -> str:
    """Render a node standing in ARGUMENT position — an individual or a property."""
    if isinstance(node, (Variable, LambdaVar, Constant)):
        return node.name
    if isinstance(node, PredicateTerm):
        return display.get(node.name, node.name)
    if isinstance(node, Lambda):
        names, body = peel_lambdas(node)
        binders = " ".join(f"{_LAM}{n}::i." for n in names)
        return f"({binders} {_isa_sigma(body, bound_arity, display)})"
    if isinstance(node, Function):
        args = " ".join(_isa_arg(a, bound_arity, display) for a in node.args)
        return f"({node.name} {args})" if args else node.name
    raise UnsupportedHigherOrderNode(
        f"ho_modal: {type(node).__name__} cannot stand in argument position; an "
        f"argument is an individual term, a predicate name, or a λ-abstraction."
    )


_BINARY_ISA = {And: "mand", Or: "mor", Implies: "mimp", Iff: "miff", Xor: "mxor"}


def _isa_sigma(node: Node, bound_arity: Dict[str, int],
               display: Dict[str, str]) -> str:
    """Render ``node`` as an Isabelle term of type ``sigma`` (a world-indexed proposition)."""
    if isinstance(node, Not):
        return f"(mnot {_isa_sigma(node.formula, bound_arity, display)})"
    op = _BINARY_ISA.get(type(node))
    if op is not None:
        left = _isa_sigma(node.left, bound_arity, display)
        right = _isa_sigma(node.right, bound_arity, display)
        return f"({op} {left} {right})"
    if isinstance(node, Box):
        return f"(mbox {_isa_sigma(node.formula, bound_arity, display)})"
    if isinstance(node, Diamond):
        return f"(mdia {_isa_sigma(node.formula, bound_arity, display)})"
    if isinstance(node, Quantifier):
        binder = "mall" if node.type == "∀" else "mex"
        body = _isa_sigma(node.formula, bound_arity, display)
        return f"({binder} ({_LAM}{node.variable.name}::i. {body}))"
    if isinstance(node, SecondOrderQuantifier):
        binder = "mall" if node.type == "∀" else "mex"
        arity = bound_arity.get(node.predicate, node.arity)
        name = display.get(node.predicate, node.predicate)
        body = _isa_sigma(node.formula, bound_arity, display)
        return (f"({binder} ({_LAM}{name}::{_prop_type(arity)}. {body}))")
    if isinstance(node, Atom):
        name = EQUALITY.get(node.predicate, node.predicate)
        name = display.get(name, name)
        if not node.args:
            return name
        args = " ".join(_isa_arg(a, bound_arity, display) for a in node.args)
        return f"({name} {args})"
    raise UnsupportedHigherOrderNode(
        f"ho_modal: no reading for {type(node).__name__}. This embedding covers "
        f"the ALETHIC fragment (□ ◇) over third-order syntax; the epistemic, "
        f"doxastic, deontic, temporal and hybrid families the parser also accepts "
        f"are carried by hol.thf_modal / hol.isabelle_modal (first-order)."
    )


def _signature_lines(formulas: Sequence[Node]):
    """Return the ``consts`` declarations for every free symbol, and the analysis behind them.

    The analysis runs over the formulas TOGETHER (with bound predicate variables
    renamed apart first), because that is the scope on which a free predicate's
    argument types are determined: ``Positive(G)`` in one axiom and ``G(x)`` in
    another jointly say that ``Positive`` takes a property of arity 1.
    """
    apart, display = rename_apart(formulas)
    signatures = analyse_signatures(apart)
    bound = set()
    for formula in apart:
        bound |= bound_pred_names(formula)

    lines: List[str] = []
    for pred in sorted(signatures.slots):
        if pred in bound or pred in EQUALITY.values() or pred in EQUALITY:
            continue
        parts = []
        for kind in signatures.slots[pred]:
            parts.append("i" if kind == INDIVIDUAL else f"({_prop_type(kind[1])})")
        arrow = "".join(f"{p} {_FUN} " for p in parts)
        lines.append(f'consts {pred} :: "{arrow}sigma"')

    # Free individual symbols: a bare NAME parses to a Constant, and a variable
    # left unbound by any quantifier denotes a particular individual too. Both
    # are individuals of type i.
    individuals = sorted(free_individuals(apart))
    for name in individuals:
        lines.append(f'consts {name} :: "i"')

    # Comparison predicates actually used, as world-relativised relations.
    used_eq = sorted({EQUALITY[p] for f in apart for p in atom_predicates(f)
                      if p in EQUALITY})
    for name in used_eq:
        lines.append(f'consts {name} :: "i {_FUN} i {_FUN} sigma"')

    # Function symbols in term position.
    for name, arity in sorted(function_symbols(apart).items()):
        arrow = "".join(f"i {_FUN} " for _ in range(arity))
        lines.append(f'consts {name} :: "{arrow}i"')
    return lines, signatures, apart, display


# --------------------------------------------------------------------------
# Theory assembly
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class HoAxiom:
    """One named axiom of an emitted theory.

    ``comment`` is printed above it, so a theory can carry the argument's own
    numbering (``A1``, ``D2``, …) and say what each line is meant to assert.
    """

    name: str
    formula: Node
    comment: str = ""


@dataclass(frozen=True)
class HoGoal:
    """One named goal, with the proof text to attempt it with.

    ``proof`` is Isabelle proof text (``by blast``, ``using A1 A2 by metis``,
    ``nitpick [expect = genuine]``, …). The kit does not invent proofs: what is
    written here is what the theory will try. ``oops`` leaves the goal
    explicitly unproved, which is what :func:`to_isabelle_ho_modal` emits when
    no proof is supplied.

    A goal is stated EITHER as a ``formula`` of the object logic — asserted
    valid, i.e. ``mvalid φ`` — OR, for the one thing the object logic cannot
    say about itself, as a raw Isabelle ``statement`` such as ``"False"``. That
    second form is what lets a theory record that an axiom set is INCONSISTENT:
    "these axioms prove falsity" is a claim about the theory, not a formula in
    it. Exactly one of the two must be given.
    """

    name: str
    formula: Optional[Node] = None
    proof: str = "oops"
    comment: str = ""
    kind: str = "theorem"
    statement: Optional[str] = None

    def __post_init__(self):
        """Reject a goal that states nothing, or states itself twice over."""
        if (self.formula is None) == (self.statement is None):
            raise ValueError(
                f"HoGoal({self.name!r}): give exactly one of formula= (an object-logic "
                f"formula, asserted valid) or statement= (a raw Isabelle proposition)."
            )


def isabelle_ho_modal_theory(name: str,
                             axioms: Sequence[HoAxiom] = (),
                             goals: Sequence[HoGoal] = (),
                             frame: str = "K",
                             preamble: Sequence[str] = ()) -> str:
    """Emit a complete Isabelle theory for a third-order modal axiom set and its goals.

    ``axioms`` are asserted as ``axiomatization where <name>: "mvalid φ"`` — valid at
    every world, which is what an axiom of the object logic means. ``goals`` are
    stated the same way and followed by their own proof text.

    ``frame`` names a system from :data:`unicode_fol_kit.fol.frames.FRAMES` and
    constrains ``R`` accordingly; ``"K"`` leaves ``R`` arbitrary. ``preamble``
    lines are inserted after the vocabulary and before the axioms, for anything
    the caller wants to add in Isabelle's own syntax.

    The signature is read off the axioms and goals together, so a symbol used in
    a goal but not in any axiom is still declared. Property-argument slots whose
    arity nothing in the theory determines are reported as a comment rather than
    silently defaulted — see :mod:`unicode_fol_kit.fol._ho_nodes`.
    """
    if frame not in FRAMES:
        raise ValueError(
            f"isabelle_ho_modal_theory: unknown frame {frame!r}; "
            f"known systems are {sorted(FRAMES)}."
        )
    # A goal stated raw (statement=) contributes no formula to type-check.
    typed_goals = [g for g in goals if g.formula is not None]
    formulas = [a.formula for a in axioms] + [g.formula for g in typed_goals]
    signature, signatures, apart, display = _signature_lines(formulas)
    # Arities come from the theory-wide analysis, not from each node's own
    # parse-time field: a binder whose arity only the OTHER axioms determine is
    # exactly the case a per-formula answer gets wrong.
    bound_arity = signatures.arity
    axiom_bodies = apart[:len(axioms)]
    typed_bodies = dict(zip((g.name for g in typed_goals), apart[len(axioms):]))

    lines = [
        "(* Third-order modal logic in HOL: shallow (Benzmuller-style) embedding. *)",
        f"(* Frame: {frame}. Constant domains. Alethic fragment. *)",
        f"theory {name}",
        "  imports Main",
        "begin",
        "",
        ho_modal_definitions(),
        "",
    ]
    frame_lines = _frame_axiom_lines(frame)
    if frame_lines:
        lines.append(f"\\<comment> \\<open>frame conditions for {frame}\\<close>")
        lines += frame_lines
        lines.append("")
    if signature:
        lines += signature
        lines.append("")
    if signatures.defaulted:
        pairs = ", ".join(f"{p}[{i}]" for p, i in sorted(signatures.defaulted))
        lines.append(
            f"\\<comment> \\<open>arity defaulted to 1 (nothing in the theory "
            f"fixes it): {pairs}\\<close>")
        lines.append("")
    lines += list(preamble)
    if preamble:
        lines.append("")

    for axiom, renamed in zip(axioms, axiom_bodies):
        if axiom.comment:
            lines.append(f"\\<comment> \\<open>{axiom.comment}\\<close>")
        body = _isa_sigma(renamed, bound_arity, display)
        lines.append(f'axiomatization where {axiom.name}: "mvalid {body}"')
    if axioms:
        lines.append("")

    for goal in goals:
        if goal.comment:
            lines.append(f"\\<comment> \\<open>{goal.comment}\\<close>")
        if goal.statement is not None:
            proposition = goal.statement
        else:
            body = _isa_sigma(typed_bodies[goal.name], bound_arity, display)
            proposition = f"mvalid {body}"
        lines.append(f'{goal.kind} {goal.name}: "{proposition}"')
        lines.append(f"  {goal.proof}")
        lines.append("")

    lines.append("end")
    return "\n".join(lines) + "\n"


def to_isabelle_ho_modal(formula: Node, name: str = "HO_Modal_Goal",
                         frame: str = "K", proof: Optional[str] = None) -> str:
    """Emit a theory whose single goal is ``formula``, valid on every world.

    The one-formula convenience over :func:`isabelle_ho_modal_theory`. Without a
    ``proof`` the goal is left ``oops`` — the kit states the problem, it does not
    invent a proof for it.
    """
    goal = HoGoal("goal", formula, proof or "oops")
    return isabelle_ho_modal_theory(name, (), (goal,), frame=frame)


# --------------------------------------------------------------------------
# THF
# --------------------------------------------------------------------------

_THF_PRELUDE = [
    "% Third-order modal logic in THF: shallow (Benzmuller-style) embedding.",
    "% mu = worlds; $i = individuals; (mu > $o) = propositions;",
    "% ($i > mu > $o) = properties; (($i > mu > $o) > mu > $o) = predicates of properties.",
    "thf(mu_type, type, ( mu : $tType )).",
    "thf(r_type, type, ( r : mu > mu > $o )).",
    "thf(mnot_type, type, ( mnot : ( mu > $o ) > mu > $o )).",
    "thf(mnot_def, definition, ( mnot = ( ^ [P: mu > $o, W: mu] : ( ~ ( P @ W ) ) ) )).",
    "thf(mand_type, type, ( mand : ( mu > $o ) > ( mu > $o ) > mu > $o )).",
    "thf(mand_def, definition, ( mand = ( ^ [P: mu > $o, Q: mu > $o, W: mu] : "
    "( ( P @ W ) & ( Q @ W ) ) ) )).",
    "thf(mor_type, type, ( mor : ( mu > $o ) > ( mu > $o ) > mu > $o )).",
    "thf(mor_def, definition, ( mor = ( ^ [P: mu > $o, Q: mu > $o, W: mu] : "
    "( ( P @ W ) | ( Q @ W ) ) ) )).",
    "thf(mimp_type, type, ( mimp : ( mu > $o ) > ( mu > $o ) > mu > $o )).",
    "thf(mimp_def, definition, ( mimp = ( ^ [P: mu > $o, Q: mu > $o, W: mu] : "
    "( ( P @ W ) => ( Q @ W ) ) ) )).",
    "thf(miff_type, type, ( miff : ( mu > $o ) > ( mu > $o ) > mu > $o )).",
    "thf(miff_def, definition, ( miff = ( ^ [P: mu > $o, Q: mu > $o, W: mu] : "
    "( ( P @ W ) <=> ( Q @ W ) ) ) )).",
    "thf(mbox_type, type, ( mbox : ( mu > $o ) > mu > $o )).",
    "thf(mbox_def, definition, ( mbox = ( ^ [P: mu > $o, W: mu] : "
    "( ! [V: mu] : ( ( r @ W @ V ) => ( P @ V ) ) ) ) )).",
    "thf(mdia_type, type, ( mdia : ( mu > $o ) > mu > $o )).",
    "thf(mdia_def, definition, ( mdia = ( ^ [P: mu > $o, W: mu] : "
    "( ? [V: mu] : ( ( r @ W @ V ) & ( P @ V ) ) ) ) )).",
    "thf(mvalid_type, type, ( mvalid : ( mu > $o ) > $o )).",
    "thf(mvalid_def, definition, ( mvalid = "
    "( ^ [P: mu > $o] : ( ! [W: mu] : ( P @ W ) ) ) )).",
]

_THF_FRAME = {
    "refl": "( ! [W: mu] : ( r @ W @ W ) )",
    "sym": "( ! [W: mu, V: mu] : ( ( r @ W @ V ) => ( r @ V @ W ) ) )",
    "trans": "( ! [W: mu, V: mu, U: mu] : ( ( ( r @ W @ V ) & ( r @ V @ U ) ) "
             "=> ( r @ W @ U ) ) )",
    "serial": "( ! [W: mu] : ( ? [V: mu] : ( r @ W @ V ) ) )",
    "eucl": "( ! [W: mu, V: mu, U: mu] : ( ( ( r @ W @ V ) & ( r @ W @ U ) ) "
            "=> ( r @ V @ U ) ) )",
    "directed": "( ! [W: mu, V: mu, U: mu] : ( ( ( r @ W @ V ) & ( r @ W @ U ) ) "
                "=> ( ? [Z: mu] : ( ( r @ V @ Z ) & ( r @ U @ Z ) ) ) ) )",
    "connected": "( ! [W: mu, V: mu, U: mu] : ( ( ( r @ W @ V ) & ( r @ W @ U ) ) "
                 "=> ( ( r @ V @ U ) | ( r @ U @ V ) ) ) )",
    "functional": "( ! [W: mu, V: mu, U: mu] : ( ( ( r @ W @ V ) & ( r @ W @ U ) ) "
                  "=> ( V = U ) ) )",
    "dense": "( ! [W: mu, V: mu] : ( ( r @ W @ V ) "
             "=> ( ? [U: mu] : ( ( r @ W @ U ) & ( r @ U @ V ) ) ) ) )",
    "shift_refl": "( ! [W: mu, V: mu] : ( ( r @ W @ V ) => ( r @ V @ V ) ) )",
    "empty": "( ! [W: mu, V: mu] : ( ~ ( r @ W @ V ) ) )",
}


def _thf_type(kind) -> str:
    """Return the THF type of an argument slot: ``$i`` or a property type."""
    if kind == INDIVIDUAL:
        return "$i"
    return "( " + " > ".join(["$i"] * kind[1] + ["mu", "$o"]) + " )"


def _thf_arg(node: Node, upper: Dict[str, str], display: Dict[str, str],
             depth: int) -> str:
    """Render an argument-position node in THF — an individual or a property."""
    if isinstance(node, (Variable, LambdaVar, Constant)):
        return upper.get(node.name, node.name)
    if isinstance(node, PredicateTerm):
        return upper.get(node.name, display.get(node.name, node.name))
    if isinstance(node, Lambda):
        names, body = peel_lambdas(node)
        fresh = dict(upper)
        for n in names:
            fresh[n] = n.upper() + "_V"
        world = f"W{depth}"
        binders = ", ".join(f"{fresh[n]}: $i" for n in names)
        return (f"( ^ [{binders}, {world}: mu] : "
                f"( {_thf(body, fresh, display, depth + 1)} @ {world} ) )")
    if isinstance(node, Function):
        args = " @ ".join(_thf_arg(a, upper, display, depth) for a in node.args)
        return f"( {node.name} @ {args} )" if node.args else node.name
    raise UnsupportedHigherOrderNode(
        f"ho_modal: {type(node).__name__} cannot stand in argument position.")


_BINARY_THF = {And: "mand", Or: "mor", Implies: "mimp", Iff: "miff"}


def _thf(node: Node, upper: Dict[str, str], display: Dict[str, str],
         depth: int = 0) -> str:
    """Render ``node`` as a THF term of type ``mu > $o``.

    ``depth`` numbers the world binders this rendering introduces (``W0``,
    ``W1``, …). Shadowing would be sound — each application picks up its own
    innermost binder — but a distinct name per level is what makes the emitted
    problem readable, and readable is what gets a mis-embedding noticed.
    """
    if isinstance(node, Not):
        return f"( mnot @ {_thf(node.formula, upper, display, depth)} )"
    op = _BINARY_THF.get(type(node))
    if op is not None:
        left = _thf(node.left, upper, display, depth)
        right = _thf(node.right, upper, display, depth)
        return f"( {op} @ {left} @ {right} )"
    if isinstance(node, Box):
        return f"( mbox @ {_thf(node.formula, upper, display, depth)} )"
    if isinstance(node, Diamond):
        return f"( mdia @ {_thf(node.formula, upper, display, depth)} )"
    if isinstance(node, Quantifier):
        var = node.variable.name.upper() + "_V"
        fresh = dict(upper, **{node.variable.name: var})
        quant = "!" if node.type == "∀" else "?"
        world = f"W{depth}"
        return (f"( ^ [{world}: mu] : ( {quant} [{var}: $i] : "
                f"( {_thf(node.formula, fresh, display, depth + 1)} @ {world} ) ) )")
    if isinstance(node, SecondOrderQuantifier):
        var = display.get(node.predicate, node.predicate).upper() + "_P"
        fresh = dict(upper, **{node.predicate: var})
        quant = "!" if node.type == "∀" else "?"
        ptype = " > ".join(["$i"] * node.arity + ["mu", "$o"])
        world = f"W{depth}"
        return (f"( ^ [{world}: mu] : ( {quant} [{var}: {ptype}] : "
                f"( {_thf(node.formula, fresh, display, depth + 1)} @ {world} ) ) )")
    if isinstance(node, Atom):
        name = EQUALITY.get(node.predicate, node.predicate)
        name = upper.get(node.predicate, display.get(name, name))
        if not node.args:
            return name
        args = " @ ".join(_thf_arg(a, upper, display, depth) for a in node.args)
        return f"( {name} @ {args} )"
    raise UnsupportedHigherOrderNode(
        f"ho_modal: no THF reading for {type(node).__name__}; this embedding "
        f"covers the alethic fragment (\u25a1 \u25c7) over third-order syntax.")


def to_thf_ho_modal(formula: Node, frame: str = "K",
                    axioms: Sequence[HoAxiom] = ()) -> str:
    """Emit a THF (TH0) problem: ``axioms`` as hypotheses, ``formula`` as the conjecture.

    The THF counterpart of :func:`isabelle_ho_modal_theory`, for a higher-order
    ATP (Leo-III, Satallax) rather than Isabelle. Same embedding, same fragment,
    same refusals; the toolkit emits the problem and does not run a prover.
    """
    if frame not in FRAMES:
        raise ValueError(f"to_thf_ho_modal: unknown frame {frame!r}.")
    formulas = [a.formula for a in axioms] + [formula]
    apart, display = rename_apart(formulas)
    signatures = analyse_signatures(apart)
    bound = set()
    for f in apart:
        bound |= bound_pred_names(f)

    lines = list(_THF_PRELUDE)
    for pred in sorted(signatures.slots):
        if pred in bound or pred in EQUALITY:
            continue
        parts = [_thf_type(k) for k in signatures.slots[pred]]
        thf_type = " > ".join(parts + ["mu", "$o"]) if parts else "mu > $o"
        lines.append(f"thf({pred}_type, type, ( {pred} : {thf_type} )).")
    for name in sorted(free_individuals(apart)):
        lines.append(f"thf({name}_type, type, ( {name} : $i )).")
    for name, arity in sorted(function_symbols(apart).items()):
        ftype = " > ".join(["$i"] * (arity + 1))
        lines.append(f"thf({name}_type, type, ( {name} : {ftype} )).")

    for condition in resolve_frame(frame):
        if condition not in _THF_FRAME:
            raise UnsupportedFrameCondition(
                f"to_thf_ho_modal: frame condition {condition!r} (system "
                f"{frame!r}) has no first-order axiom over r.")
        lines.append(f"thf(frame_{condition}, axiom, {_THF_FRAME[condition]}).")

    for axiom, renamed in zip(axioms, apart):
        lines.append(f"thf({axiom.name}, axiom, ( mvalid @ "
                     f"{_thf(renamed, {}, display)} )).")
    lines.append(f"thf(goal, conjecture, "
                 f"( mvalid @ {_thf(apart[-1], {}, display)} )).")
    return "\n".join(lines) + "\n"
