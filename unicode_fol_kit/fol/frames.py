"""Modal frame conditions and the named axioms they correspond to.

The kit reasons about modality on six routes — the standard translation
(:mod:`unicode_fol_kit.fol.qml`), a labelled tableau
(:mod:`unicode_fol_kit.atp.modal_tableau`), finite-frame enumeration
(:mod:`unicode_fol_kit.atp.kripke_enum`), natural deduction
(:mod:`unicode_fol_kit.atp.fitch`), the hybrid translation
(:mod:`unicode_fol_kit.fol.modal_translation`) and the higher-order
embeddings (:mod:`unicode_fol_kit.hol.isabelle_modal`,
:mod:`unicode_fol_kit.hol.thf_modal`). Each used to keep its OWN copy of the
frame table, which is how a route silently ended up understanding fewer
systems than its neighbour. This module is the single source of truth they
all read: what a named system consists of, what each condition means, and —
the part that makes it checkable — the modal axiom each condition
corresponds to.

The correspondence is not decoration. ``tests/test_modal_frames.py``
BRUTE-FORCES it: for every first-order condition here, over every frame on
up to three worlds and every valuation, "the axiom is valid on this frame"
and "the frame satisfies this condition" must agree. A wrong entry in this
module therefore fails a test rather than quietly teaching one route a
different modal logic than another.

The Geach family
-----------------
Most named conditions are instances of ONE schema. With the Scott–Lemmon
(Geach) coordinates ``G(m, n, r, s)``::

    axiom      ◇^m □^n p → □^r ◇^s p
    condition  ∀w,u,v (w R^m u ∧ w R^r v → ∃t (u R^n t ∧ v R^s t))

reflexivity is ``G(0,1,0,0)``, transitivity ``G(0,1,2,0)``, symmetry
``G(0,0,1,1)``, seriality ``G(0,1,0,1)``, euclideanness ``G(1,0,1,1)``,
directedness ``G(1,1,1,1)``, partial functionality ``G(1,0,1,0)`` and
density ``G(0,2,1,0)``. The named conditions keep their own hand-written
axioms (readable, and unchanged since before this module existed), and a
test proves each equivalent to the Geach-generated one — so the unification
is machine-checked rather than asserted in a comment.

``G(m,n,r,s)`` is also accepted directly as a frame name, which is what
makes the infinite family reachable without inventing a name per instance::

    qml_is_valid(formula, frame="G(1,1,1,1)")     # ≡ frame=".2"-style

What is NOT first-order definable
----------------------------------
Three named axioms have no first-order frame condition at all: Löb
(``□(□p→p)→□p``, the GL system), McKinsey (``□◇p→◇□p``, S4.1) and
Grzegorczyk (``□(□(p→□p)→p)→p``, Grz). They are marked
``first_order=False`` and carried ONLY by the higher-order routes, which
assert the schema itself, quantified over propositions. Every first-order
route refuses them by name — the boundary is stated, never approximated.
"""

from typing import Callable, Dict, FrozenSet, Iterable, Optional, Tuple

from .nodes import (
    And, Atom, Box, Diamond, Implies, Node, Not, Or, Quantifier, Variable,
)

__all__ = [
    "FrameCondition", "FRAME_CONDITIONS", "FRAMES", "GeachSpec",
    "resolve_frame", "parse_geach", "geach_axiom", "modal_axiom",
    "MODAL_AXIOMS", "holds_on_finite_frame", "is_first_order",
    "UnsupportedFrameCondition", "unguarded_frame_axiom",
    "require_supported", "AXIOM_ALIASES",
]


class UnsupportedFrameCondition(NotImplementedError):
    """A route was handed a frame condition it cannot express soundly.

    Raised instead of ignoring the condition — a route that silently drops
    "directed" from ``S4.2`` would report countermodels that the frame
    class excludes, which is exactly the failure this exception exists to
    make impossible.
    """


# ---------------------------------------------------------------------------
# The Geach / Scott–Lemmon family
# ---------------------------------------------------------------------------

class GeachSpec(tuple):
    """The four Scott–Lemmon coordinates ``(m, n, r, s)`` of ``◇^m □^n p →
    □^r ◇^s p``."""

    __slots__ = ()

    def __new__(cls, m: int, n: int, r: int, s: int):
        for value in (m, n, r, s):
            if not isinstance(value, int) or isinstance(value, bool) or value < 0:
                raise ValueError(
                    f"GeachSpec: coordinates must be non-negative ints, got "
                    f"{(m, n, r, s)!r}")
        return super().__new__(cls, (m, n, r, s))

    @property
    def m(self) -> int:
        return self[0]

    @property
    def n(self) -> int:
        return self[1]

    @property
    def r(self) -> int:
        return self[2]

    @property
    def s(self) -> int:
        return self[3]

    def __repr__(self) -> str:                       # pragma: no cover - repr
        return f"G({self.m},{self.n},{self.r},{self.s})"


def parse_geach(name: str) -> Optional[GeachSpec]:
    """``"G(1,1,1,1)"`` → :class:`GeachSpec`; ``None`` if ``name`` is not one.

    Accepts the condition spelling ``"geach:1,1,1,1"`` too — that is how a
    Geach condition travels inside a frame's condition tuple, so every route
    can keep treating conditions as plain strings.
    """
    text = name.strip()
    if text.startswith("geach:"):
        body = text[len("geach:"):]
    elif text.startswith("G(") and text.endswith(")"):
        body = text[2:-1]
    else:
        return None
    parts = [p.strip() for p in body.split(",")]
    if len(parts) != 4 or not all(p.isdigit() for p in parts):
        raise ValueError(
            f"frames: {name!r} is not a Geach spec — expected G(m,n,r,s) with "
            "four non-negative integers, e.g. G(1,1,1,1)")
    return GeachSpec(*(int(p) for p in parts))


def geach_condition_name(spec: GeachSpec) -> str:
    """The condition string a frame table stores for ``spec``."""
    return f"geach:{spec.m},{spec.n},{spec.r},{spec.s}"


def _iterate(op, times: int, formula: Node) -> Node:
    for _ in range(times):
        formula = op(formula)
    return formula


def geach_axiom(spec: GeachSpec, atom: str = "P") -> Node:
    """The modal schema ``◇^m □^n p → □^r ◇^s p`` for ``spec``."""
    p = Atom(atom, ())
    left = _iterate(Diamond, spec.m, _iterate(Box, spec.n, p))
    right = _iterate(Box, spec.r, _iterate(Diamond, spec.s, p))
    return Implies(left, right)


# ---------------------------------------------------------------------------
# Named axioms
# ---------------------------------------------------------------------------

def _p(name: str = "P") -> Node:
    return Atom(name, ())


#: Axiom name → builder of its modal schema over propositional letters.
#: Two-letter schemas take both names; the rest ignore the second.
MODAL_AXIOMS: Dict[str, Callable[..., Node]] = {
    # The Geach instances (their frame conditions are in FRAME_CONDITIONS).
    "T": lambda p="P", q="Q": Implies(Box(_p(p)), _p(p)),
    "D": lambda p="P", q="Q": Implies(Box(_p(p)), Diamond(_p(p))),
    "B": lambda p="P", q="Q": Implies(_p(p), Box(Diamond(_p(p)))),
    "4": lambda p="P", q="Q": Implies(Box(_p(p)), Box(Box(_p(p)))),
    "5": lambda p="P", q="Q": Implies(Diamond(_p(p)), Box(Diamond(_p(p)))),
    "CD": lambda p="P", q="Q": Implies(Diamond(_p(p)), Box(_p(p))),
    "C4": lambda p="P", q="Q": Implies(Box(Box(_p(p))), Box(_p(p))),
    ".2": lambda p="P", q="Q": Implies(Diamond(Box(_p(p))), Box(Diamond(_p(p)))),
    # Not Geach instances, but still first-order.
    ".3": lambda p="P", q="Q": Or(Box(Implies(Box(_p(p)), _p(q))),
                                  Box(Implies(Box(_p(q)), _p(p)))),
    "Mshift": lambda p="P", q="Q": Box(Implies(Box(_p(p)), _p(p))),
    "Ver": lambda p="P", q="Q": Box(_p(p)),
    # No first-order frame condition exists for these three.
    "McKinsey": lambda p="P", q="Q": Implies(Box(Diamond(_p(p))),
                                             Diamond(Box(_p(p)))),
    "Loeb": lambda p="P", q="Q": Implies(Box(Implies(Box(_p(p)), _p(p))),
                                         Box(_p(p))),
    "Grz": lambda p="P", q="Q": Implies(
        Box(Implies(Box(Implies(_p(p), Box(_p(p)))), _p(p))), _p(p)),
    # Theorems of every normal modal logic — no frame condition, listed so a
    # caller can ask for the formula and check that the kit validates it.
    "K": lambda p="P", q="Q": Implies(Box(Implies(_p(p), _p(q))),
                                      Implies(Box(_p(p)), Box(_p(q)))),
    "N": lambda p="P", q="Q": Box(Or(_p(p), Not(_p(p)))),
    "P": lambda p="P", q="Q": Not(Box(And(_p(p), Not(_p(p))))),
}

#: The alternative names the literature uses, mapped onto this module's.
#: ``M`` is deliberately NOT accepted for ``T``: this module uses ``Mshift``
#: for the shift-reflexivity axiom ``□(□p→p)``, and one letter cannot mean
#: both without inviting exactly the mistake a frame table must not make.
AXIOM_ALIASES: Dict[str, str] = {
    "G": ".2", "G1": ".2", "C": ".2",          # ◇□p → □◇p, one axiom
    "H": ".3",                                  # □(□p→q) ∨ □(□q→p)
    "Q": "C4",                                  # □□p → □p, one axiom
    "W": "Loeb",                                # □(□p→p) → □p, one axiom
    "L": "Loeb",
    "Alt1": "CD", "Alt3": "CD",                 # ◇p→□p, ◇p∧◇q→◇(p∧q)
    "Alt2": "Mshift",                           # ◇p→◇(p∧◇p)
    "Dense": "C4", "Density": "C4",
    ".1": "McKinsey",
    "Grzegorczyk": "Grz",
}


def modal_axiom(name: str, p: str = "P", q: str = "Q") -> Node:
    """The modal schema of a named axiom, over the given letters.

    Accepts the aliases the literature uses (:data:`AXIOM_ALIASES`), so
    ``modal_axiom("W")`` and ``modal_axiom("Loeb")`` build the same formula.
    """
    key = AXIOM_ALIASES.get(name, name)
    if key not in MODAL_AXIOMS:
        raise ValueError(
            f"frames: unknown modal axiom {name!r} (use one of "
            f"{sorted(MODAL_AXIOMS)} or an alias {sorted(AXIOM_ALIASES)})")
    return MODAL_AXIOMS[key](p, q)


# ---------------------------------------------------------------------------
# Frame conditions
# ---------------------------------------------------------------------------

class FrameCondition(tuple):
    """One frame condition: what it is called, what it means, which axiom it
    corresponds to, and whether it is first-order definable at all."""

    __slots__ = ()

    def __new__(cls, name: str, axiom: str, description: str,
                geach: Optional[GeachSpec] = None, first_order: bool = True):
        return super().__new__(cls, (name, axiom, description, geach,
                                     first_order))

    name = property(lambda self: self[0])
    axiom = property(lambda self: self[1])
    description = property(lambda self: self[2])
    geach = property(lambda self: self[3])
    first_order = property(lambda self: self[4])


#: Condition name → :class:`FrameCondition`. The ``geach`` coordinates are
#: checked against the hand-written axiom by the test suite.
FRAME_CONDITIONS: Dict[str, FrameCondition] = {
    "refl": FrameCondition(
        "refl", "T", "∀w Rww — reflexive", GeachSpec(0, 1, 0, 0)),
    "trans": FrameCondition(
        "trans", "4", "∀w,v,u (Rwv ∧ Rvu → Rwu) — transitive",
        GeachSpec(0, 1, 2, 0)),
    "sym": FrameCondition(
        "sym", "B", "∀w,v (Rwv → Rvw) — symmetric", GeachSpec(0, 0, 1, 1)),
    "serial": FrameCondition(
        "serial", "D", "∀w ∃v Rwv — serial", GeachSpec(0, 1, 0, 1)),
    "eucl": FrameCondition(
        "eucl", "5", "∀w,v,u (Rwv ∧ Rwu → Rvu) — euclidean",
        GeachSpec(1, 0, 1, 1)),
    "directed": FrameCondition(
        "directed", ".2",
        "∀w,v,u (Rwv ∧ Rwu → ∃t (Rvt ∧ Rut)) — directed / convergent",
        GeachSpec(1, 1, 1, 1)),
    "functional": FrameCondition(
        "functional", "CD",
        "∀w,v,u (Rwv ∧ Rwu → v = u) — partially functional (at most one "
        "successor)", GeachSpec(1, 0, 1, 0)),
    "dense": FrameCondition(
        "dense", "C4", "∀w,v (Rwv → ∃u (Rwu ∧ Ruv)) — dense",
        GeachSpec(0, 2, 1, 0)),
    "connected": FrameCondition(
        "connected", ".3",
        "∀w,v,u (Rwv ∧ Rwu → Rvu ∨ Ruv) — connected / no branching to the "
        "right. Note there is deliberately NO 'or v = u' escape: that weaker "
        "condition belongs to the OTHER common .3 formulation "
        "(◇p ∧ ◇q → ◇(p ∧ ◇q) ∨ ◇(q ∧ ◇p)); for the □(□p→q) ∨ □(□q→p) form "
        "used here the exact correspondent needs Rvv when v = u, and the "
        "brute-force correspondence test confirms it on every frame up to "
        "three worlds. Over reflexive frames the two coincide"),
    "shift_refl": FrameCondition(
        "shift_refl", "Mshift",
        "∀w,v (Rwv → Rvv) — shift-reflexive (every accessible world is "
        "reflexive; the axiom □(□p→p), also reached by ◇p→◇(p∧◇p))"),
    "empty": FrameCondition(
        "empty", "Ver", "∀w,v ¬Rwv — no accessible worlds at all (the Verum "
        "system, where □p holds vacuously)"),
    # Not first-order definable: carried only by the higher-order routes.
    "loeb": FrameCondition(
        "loeb", "Loeb",
        "Gödel–Löb provability: transitive + converse well-founded — NOT "
        "first-order definable; the higher-order routes assert the Löb schema "
        "itself",
        first_order=False),
    "mckinsey": FrameCondition(
        "mckinsey", "McKinsey",
        "NOT first-order definable; the higher-order routes assert the "
        "McKinsey schema □◇p → ◇□p itself", first_order=False),
    "grz": FrameCondition(
        "grz", "Grz",
        "reflexive + transitive + no infinite ascending chains of distinct "
        "worlds — NOT first-order definable; the higher-order routes assert "
        "the Grzegorczyk schema itself", first_order=False),
}


def is_first_order(condition: str) -> bool:
    """Whether ``condition`` has a first-order frame condition at all."""
    if parse_geach(condition) is not None:
        return True
    spec = FRAME_CONDITIONS.get(condition)
    if spec is None:
        raise ValueError(f"frames: unknown frame condition {condition!r}")
    return spec.first_order


# ---------------------------------------------------------------------------
# Named systems
# ---------------------------------------------------------------------------

#: System name → its frame conditions. ``D`` and ``KD`` (and ``B`` /
#: ``KTB``) are the same system under both spellings the literature uses.
FRAMES: Dict[str, Tuple[str, ...]] = {
    "K": (),
    "D": ("serial",),
    "KD": ("serial",),
    "T": ("refl",),
    "KB": ("sym",),
    "B": ("refl", "sym"),                       # Brouwer, K + T + B
    "KTB": ("refl", "sym"),
    "K4": ("trans",),
    "K5": ("eucl",),
    "K45": ("trans", "eucl"),
    "KD4": ("serial", "trans"),
    "KD5": ("serial", "eucl"),
    "KD45": ("serial", "trans", "eucl"),
    "S4": ("refl", "trans"),
    "S5": ("refl", "trans", "sym"),
    "S4.1": ("refl", "trans", "mckinsey"),      # + McKinsey (HOL routes only)
    "S4.2": ("refl", "trans", "directed"),      # convergent (.2)
    "S4.3": ("refl", "trans", "connected"),     # no-branching (.3)
    "KCD": ("functional",),                     # ◇p → □p
    "KC4": ("dense",),                          # □□p → □p
    "KShift": ("shift_refl",),                  # □(□p → p)
    "Ver": ("empty",),                          # □p — the Verum system
    "GL": ("trans", "loeb"),                    # HOL routes only
    "Grz": ("refl", "trans", "grz"),            # HOL routes only
}


def resolve_frame(frame: str) -> Tuple[str, ...]:
    """The conditions of a named system, or of a ``G(m,n,r,s)`` spec.

    (Named ``resolve_frame`` rather than the more obvious
    ``frame_conditions``: that would collide with the
    :data:`FRAME_CONDITIONS` registry on a case-insensitive filesystem —
    Sphinx writes one stub file per documented name, and the two would
    overwrite each other on Windows.)

    Raises:
        ValueError: ``frame`` is neither a known system name nor a
            well-formed Geach spec — the message lists what is available.
    """
    spec = parse_geach(frame)
    if spec is not None:
        return (geach_condition_name(spec),)
    if frame not in FRAMES:
        raise ValueError(
            f"unknown frame {frame!r} (use one of {sorted(FRAMES)}, or a "
            "Scott–Lemmon spec like 'G(1,1,1,1)')")
    return FRAMES[frame]


def require_supported(route: str, conditions: Iterable[str],
                      supported: Iterable[str], *, hint: str = "") -> None:
    """Refuse, by name, any condition a route cannot express soundly.

    The alternative — ignoring it — would make the route answer about a
    LARGER frame class than the caller asked for, i.e. report countermodels
    that the named system excludes. Every route calls this instead.
    """
    allowed = set(supported)
    for condition in conditions:
        if condition in allowed:
            continue
        if parse_geach(condition) is not None and "geach" in allowed:
            continue
        spec = FRAME_CONDITIONS.get(condition)
        what = spec.description if spec is not None else condition
        raise UnsupportedFrameCondition(
            f"{route}: the frame condition {condition!r} ({what}) is not "
            f"expressible here." + (f" {hint}" if hint else ""))


# ---------------------------------------------------------------------------
# Finite frames — the checker the enumerator and the tests share
# ---------------------------------------------------------------------------

def _steps(edges: FrozenSet[Tuple[int, int]], n: int,
           k: int) -> FrozenSet[Tuple[int, int]]:
    """``R^k`` over ``range(n)``: pairs joined by a path of EXACTLY ``k``
    edges (``R^0`` is the identity)."""
    reachable = {(w, w) for w in range(n)}
    for _ in range(k):
        reachable = {(w, v) for (w, mid) in reachable
                     for (mid2, v) in edges if mid == mid2}
    return frozenset(reachable)


def holds_on_finite_frame(condition: str, edges: FrozenSet[Tuple[int, int]],
                          n: int) -> bool:
    """Does the finite frame ``(range(n), edges)`` satisfy ``condition``?

    Every FIRST-ORDER condition in :data:`FRAME_CONDITIONS` is decided here,
    Geach specs included. The three non-first-order conditions raise
    :class:`UnsupportedFrameCondition`: they are not conditions on a frame's
    relation that a finite check could settle, and pretending otherwise is
    exactly the silent-approximation failure this module exists to prevent.
    """
    spec = parse_geach(condition)
    if spec is None:
        entry = FRAME_CONDITIONS.get(condition)
        if entry is None:
            raise ValueError(f"frames: unknown frame condition {condition!r}")
        if not entry.first_order:
            raise UnsupportedFrameCondition(
                f"frames: {condition!r} ({entry.description}) is not a "
                "first-order frame condition, so no finite frame check "
                "decides it")
        if entry.geach is None:
            return _named_holds(condition, edges, n)
        spec = entry.geach
    from_u = _steps(edges, n, spec.n)
    from_v = _steps(edges, n, spec.s)
    left = _steps(edges, n, spec.m)
    right = _steps(edges, n, spec.r)
    for (w, u) in left:
        for (w2, v) in right:
            if w != w2:
                continue
            if not any((u, t) in from_u and (v, t) in from_v
                       for t in range(n)):
                return False
    return True


def _named_holds(condition: str, edges: FrozenSet[Tuple[int, int]],
                 n: int) -> bool:
    """The first-order conditions that are not Geach instances."""
    if condition == "connected":
        return all(not ((w, v) in edges and (w, u) in edges)
                   or (v, u) in edges or (u, v) in edges
                   for w in range(n) for v in range(n) for u in range(n))
    if condition == "shift_refl":
        return all((v, v) in edges for (_w, v) in edges)
    if condition == "empty":
        return not edges
    raise ValueError(f"frames: unknown frame condition {condition!r}")


# ---------------------------------------------------------------------------
# One first-order emitter for the routes that need no world guard
# ---------------------------------------------------------------------------

_FORALL, _EXISTS = "∀", "∃"


def unguarded_frame_axiom(condition: str, relation: str = "R", *,
                          prefix: str = "_fw") -> Node:
    """The first-order frame axiom of ``condition`` over ``relation``.

    Written WITHOUT a sort guard, which is what the natural-deduction route
    (:mod:`unicode_fol_kit.atp.fitch`) and the hybrid translation
    (:mod:`unicode_fol_kit.fol.modal_translation`) need — both quantify over
    worlds only. The quantified-modal route
    (:mod:`unicode_fol_kit.fol.qml`) keeps its own ``World``-guarded
    emitters, because there worlds and objects share one domain.

    The axiom is closed over its own bound variables (named with ``prefix``),
    so it can never capture anything in the formula it is conjoined with.

    Raises:
        UnsupportedFrameCondition: ``condition`` has no first-order frame
            condition (Löb, McKinsey, Grz).
        ValueError: ``condition`` is not a known condition at all.
    """
    w, u, v, s = (Variable(f"{prefix}0"), Variable(f"{prefix}1"),
                  Variable(f"{prefix}2"), Variable(f"{prefix}3"))
    R = lambda a, b: Atom(relation, (a, b))
    fa = lambda var, body: Quantifier(_FORALL, var, body)
    ex = lambda var, body: Quantifier(_EXISTS, var, body)

    spec = parse_geach(condition)
    if spec is None:
        entry = FRAME_CONDITIONS.get(condition)
        if entry is None:
            raise ValueError(f"frames: unknown frame condition {condition!r}")
        if not entry.first_order:
            raise UnsupportedFrameCondition(
                f"frames: {condition!r} ({entry.description}) has no "
                "first-order frame axiom")
        if condition == "refl":
            return fa(w, R(w, w))
        if condition == "trans":
            return fa(w, fa(u, fa(v, Implies(And(R(w, u), R(u, v)), R(w, v)))))
        if condition == "sym":
            return fa(w, fa(u, Implies(R(w, u), R(u, w))))
        if condition == "serial":
            return fa(w, ex(u, R(w, u)))
        if condition == "eucl":
            return fa(w, fa(u, fa(v, Implies(And(R(w, u), R(w, v)), R(u, v)))))
        if condition == "directed":
            return fa(w, fa(u, fa(v, Implies(
                And(R(w, u), R(w, v)), ex(s, And(R(u, s), R(v, s)))))))
        if condition == "connected":
            return fa(w, fa(u, fa(v, Implies(
                And(R(w, u), R(w, v)), Or(R(u, v), R(v, u))))))
        if condition == "functional":
            return fa(w, fa(u, fa(v, Implies(
                And(R(w, u), R(w, v)), Atom("=", (u, v))))))
        if condition == "dense":
            return fa(w, fa(u, Implies(R(w, u), ex(v, And(R(w, v), R(v, u))))))
        if condition == "shift_refl":
            return fa(w, fa(u, Implies(R(w, u), R(u, u))))
        if condition == "empty":
            return fa(w, fa(u, Not(R(w, u))))
        raise ValueError(               # pragma: no cover - registry drift
            f"frames: {condition!r} is registered but has no axiom builder")

    counter = [0]

    def path(a, b, k):
        if k == 0:
            return Atom("=", (a, b))
        previous, mids, conj = a, [], None
        for _ in range(k - 1):
            z = Variable(f"{prefix}z{counter[0]}")
            counter[0] += 1
            mids.append(z)
            step = R(previous, z)
            conj = step if conj is None else And(conj, step)
            previous = z
        body = R(previous, b)
        if conj is not None:
            body = And(conj, body)
        for z in reversed(mids):
            body = ex(z, body)
        return body

    body = Implies(And(path(w, u, spec.m), path(w, v, spec.r)),
                   ex(s, And(path(u, s, spec.n), path(v, s, spec.s))))
    for var in (v, u, w):
        body = fa(var, body)
    return body
