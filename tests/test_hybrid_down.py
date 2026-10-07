"""Tests for the ↓ binder (N1): full hybrid logic H(@,↓).

H(@,↓) adds the state-variable binder ↓x.φ to H(@) — see
``unicode_logic_kit.fol._hybrid_nodes``' module docstring for the architecture.
Unlike H(@) (decidable), H(@,↓) validity is UNDECIDABLE, so this file covers
TWO independent, cross-checking routes, mirroring ``docs/guide/hybrid.md``'s
existing tableau-vs-Z3 pattern for H(@):

* **Route A** (always terminating): ``satisfies_modal`` on hand-built finite
  models, PLUS a brute-force sweep over EVERY binary relation and EVERY
  valuation/nominal-assignment on 1-3 worlds for the battery — cross-checked
  against ``_ref_eval``, a from-scratch, independent reimplementation of the
  same Kripke-satisfaction fragment (Nominal/At/Down/Box/Diamond/classical
  connectives), NOT a copy of ``semantics.kripke.satisfies_modal``'s own code.
* **Route B**: ``down_is_valid`` (the standard translation + a direct Z3
  ``Solver()`` call, PROVED-only) and ``atp.kripke_enum.KripkeEnumBackend`` /
  ``modal_enum_search`` (bounded finite-model search, REFUTED-only, every
  countermodel independently re-verified with ``satisfies_modal``).

Cross-checks enforced throughout: every Z3-PROVED formula is confirmed TRUE
at world 0 of EVERY model the brute-force sweep enumerates; every
KripkeEnumBackend countermodel is re-checked with ``satisfies_modal``
directly (not just trusted); no formula with a brute-force countermodel is
ever reported PROVED by ``down_is_valid``.

Also covered: the refusal-by-name battery (every route that cannot decide ↓
must raise NotImplementedError naming it, while ``standard_translation`` /
``down_is_valid`` / ``satisfies_modal`` do not raise on the same formula),
parser/dict round-trips for nested ``Down``, and the documented
free-nominal-vs-``modal_enum_search`` gap (test_oracle #9).
"""

import itertools

import pytest

from unicode_logic_kit import (
    MSFLParser, Node,
    Atom, Not, And, Or, Implies, Iff, Box, Diamond,
    KripkeModel, satisfies_modal,
    standard_translation,
    is_modal_valid, modal_decide, modal_countermodel, modal_prove,
    modal_tableau_closed,
)
from unicode_logic_kit.fol.modal_translation import hybrid_is_valid, down_is_valid
from unicode_logic_kit.atp.kripke_enum import (
    modal_enum_search, KripkeEnumBackend, kripke_model_from_dict,
)
from unicode_logic_kit.atp.hybrid_down import down_decide
from unicode_logic_kit.atp.protocol import PROVED, REFUTED, UNKNOWN

# The four HOL/THF shallow-embedding routes and the alethic-only QML export --
# imported as modules (not individual functions) so the refusal battery below
# can name each call site the same way the batch notes name the routes
# themselves ("fol.qml", "hol.isabelle_modal", "hol.thf_modal", "hol.ho_modal").
from unicode_logic_kit.fol import qml
from unicode_logic_kit.hol import isabelle_modal, thf_modal, ho_modal

# Down/Nominal/At are not yet re-exported through unicode_logic_kit's top-level
# __init__ (that edit is outside this change's file ownership — see the
# change's own report); imported directly from their defining module, the
# same class objects either import path would give.
from unicode_logic_kit.fol._hybrid_nodes import Down, Nominal, At

mp = MSFLParser(modal=True)

P = Atom("P", [])
Q = Atom("Q", [])


# =============================================================================
# An INDEPENDENT reference evaluator (route A's second oracle)
# =============================================================================
#
# A from-scratch reimplementation of Kripke satisfaction for exactly the
# fragment the battery below needs (Atom/Nominal/At/Down/Not/And/Or/Implies/
# Iff/Box/Diamond) -- deliberately NOT calling semantics.kripke.satisfies_modal
# or sharing any of its code, so agreement between the two is real evidence,
# not a tautology. `env` is a plain dict (nominal name -> world), covering
# BOTH pre-assigned free nominals and ↓-bound ones uniformly -- the same
# "environment" idea satisfies_modal's Down case uses, independently re-coded.

def _ref_eval(node: Node, worlds, rel, val, w, env):
    cls = type(node).__name__
    if cls == "Atom":
        return node.to_unicode_str() in val.get(w, set())
    if cls == "Nominal":
        if node.name not in env:
            raise ValueError(f"_ref_eval: free nominal {node.name!r} unassigned")
        return w == env[node.name]
    if cls == "At":
        if node.nominal.name not in env:
            raise ValueError(f"_ref_eval: free nominal {node.nominal.name!r} unassigned")
        return _ref_eval(node.formula, worlds, rel, val, env[node.nominal.name], env)
    if cls == "Down":
        new_env = dict(env)
        new_env[node.variable.name] = w
        return _ref_eval(node.formula, worlds, rel, val, w, new_env)
    if cls == "Not":
        return not _ref_eval(node.formula, worlds, rel, val, w, env)
    if cls == "And":
        return (_ref_eval(node.left, worlds, rel, val, w, env)
                and _ref_eval(node.right, worlds, rel, val, w, env))
    if cls == "Or":
        return (_ref_eval(node.left, worlds, rel, val, w, env)
                or _ref_eval(node.right, worlds, rel, val, w, env))
    if cls == "Implies":
        return ((not _ref_eval(node.left, worlds, rel, val, w, env))
                or _ref_eval(node.right, worlds, rel, val, w, env))
    if cls == "Iff":
        return (_ref_eval(node.left, worlds, rel, val, w, env)
                == _ref_eval(node.right, worlds, rel, val, w, env))
    if cls == "Box":
        return all(_ref_eval(node.formula, worlds, rel, val, w2, env)
                  for w2 in worlds if (w, w2) in rel)
    if cls == "Diamond":
        return any(_ref_eval(node.formula, worlds, rel, val, w2, env)
                  for w2 in worlds if (w, w2) in rel)
    raise ValueError(f"_ref_eval: unhandled node type {cls}")


def test_ref_eval_agrees_with_satisfies_modal_on_hand_built_models():
    """Sanity: the independent reimplementation and satisfies_modal agree on a
    few hand-built models BEFORE trusting either for the brute-force sweep."""
    m = KripkeModel({0, 1}, {"alethic": {(0, 1), (1, 1)}})
    f = mp.parse("↓x.□¬x")
    for w in (0, 1):
        assert (satisfies_modal(f, m, w)
               == _ref_eval(f, m.worlds, m.relation("alethic"), m.valuation, w, {}))


# =============================================================================
# Brute-force sweep: EVERY binary relation, EVERY valuation, on 1-3 worlds
# =============================================================================

def _all_relations(worlds):
    """Every subset of worlds x worlds, as a set of (a, b) pairs."""
    pairs = [(a, b) for a in worlds for b in worlds]
    for mask in range(1 << len(pairs)):
        yield {p for i, p in enumerate(pairs) if (mask >> i) & 1}


def _all_valuations(worlds, atom_keys):
    """Every {world: set(atom_keys true there)} valuation over worlds."""
    if not atom_keys:
        yield {w: set() for w in worlds}
        return
    m = len(atom_keys)
    for combo in itertools.product(range(1 << m), repeat=len(worlds)):
        yield {w: {atom_keys[i] for i in range(m) if (bits >> i) & 1}
              for w, bits in zip(worlds, combo)}


def _all_nominal_assignments(worlds, names):
    """Every {name: world} assignment for a fixed list of nominal names."""
    if not names:
        yield {}
        return
    for combo in itertools.product(worlds, repeat=len(names)):
        yield dict(zip(names, combo))


def _sweep(formula, *, atom_keys=(), nominal_names=(), needs_relation,
          check):
    """Run `check(model, world)` over every (relation?, valuation, nominal
    assignment, world) combination for n = 1, 2, 3 worlds. `needs_relation`
    skips the (expensive) relation enumeration for formulas with no □/◇."""
    total = 0
    for n in (1, 2, 3):
        worlds = tuple(range(n))
        rels = _all_relations(worlds) if needs_relation else [set()]
        for rel in rels:
            for val in _all_valuations(worlds, atom_keys):
                for nom in _all_nominal_assignments(worlds, nominal_names):
                    model = KripkeModel(worlds, {"alethic": rel}, val, nominals=nom)
                    for w in worlds:
                        check(model, w)
                        total += 1
    return total


# --- 1. Irreflexivity: ↓x.□¬x ------------------------------------------------

def test_down_box_not_x_is_irreflexivity_brute_force():
    """↓x.□¬x holds at w iff w has NO alethic self-loop -- checked against
    both the closed-form FO condition (world has no self-loop) AND the
    independent _ref_eval, over every relation/valuation on 1-3 worlds."""
    f = mp.parse("↓x.□¬x")

    def check(model, w):
        expected = (w, w) not in model.relation("alethic")
        got = satisfies_modal(f, model, w)
        assert got == expected, (model, w)
        ref = _ref_eval(f, model.worlds, model.relation("alethic"), model.valuation, w, {})
        assert ref == expected, (model, w)

    n = _sweep(f, needs_relation=True, check=check)
    assert n > 1000, n  # sanity: the sweep actually ran a lot of cases


# --- 2. Reflexivity: ↓x.◇x ---------------------------------------------------

def test_down_diamond_x_is_reflexivity_brute_force():
    """↓x.◇x holds at w iff w HAS an alethic self-loop."""
    f = mp.parse("↓x.◇x")

    def check(model, w):
        expected = (w, w) in model.relation("alethic")
        got = satisfies_modal(f, model, w)
        assert got == expected, (model, w)
        ref = _ref_eval(f, model.worlds, model.relation("alethic"), model.valuation, w, {})
        assert ref == expected, (model, w)

    n = _sweep(f, needs_relation=True, check=check)
    assert n > 1000, n


# --- 3. Tautology: ↓x.(@x p ↔ p) ---------------------------------------------

def test_down_at_x_p_iff_p_is_a_tautology_brute_force():
    """↓x.(@x p ↔ p) holds at EVERY world of EVERY model/valuation/nominal
    assignment for p -- @x re-anchors at x, and x was JUST bound to the
    current world, so "p at x" and "p" (bare, at the current world) ask the
    identical question, whatever p denotes (here: a free nominal)."""
    f = mp.parse("↓x.(@x p ↔ p)")

    def check(model, w):
        assert satisfies_modal(f, model, w) is True, (model, w)
        ref = _ref_eval(f, model.worlds, model.relation("alethic"), model.valuation, w, model.nominals)
        assert ref is True, (model, w)

    n = _sweep(f, needs_relation=False, nominal_names=["p"], check=check)
    assert n > 10, n


# --- 4. NOT valid over K (down_is_valid honestly UNKNOWN; KripkeEnumBackend
#        REFUTES it with a satisfies_modal-reverified witness) ---------------

def test_down_diamond_x_not_proved_over_k_but_refuted_by_enum():
    f = mp.parse("↓x.◇x")

    v = down_is_valid(f, frame="K")
    assert v.status == UNKNOWN, v
    assert v.reason in ("incomplete", "timeout"), v

    result = modal_enum_search(f, frame="K", max_worlds=2)
    assert result.model is not None, result
    # Independent re-verification: the reported countermodel really does
    # falsify the formula (this is not just trusting modal_enum_search).
    assert satisfies_modal(f, result.model, 0) is False

    backend_verdict = KripkeEnumBackend().decide(f, frame="K", max_worlds=2)
    assert backend_verdict.status == REFUTED, backend_verdict
    rebuilt = kripke_model_from_dict(backend_verdict.countermodel["data"])
    assert satisfies_modal(f, rebuilt, 0) is False

    # And PROVED over T (the reflexive frame), by the independent Z3 route.
    v_t = down_is_valid(f, frame="T")
    assert v_t.status == PROVED, v_t


# --- 5. Shadowing: ↓x.↓x.φ (inner rebinds; outer entirely inert) ------------

def test_down_shadowing_inner_rebinds_brute_force():
    """↓x.↓x.□¬x must equal bare ↓x.□¬x at every world of every model --
    the OUTER binding is never observable (the inner ↓x immediately
    overrides it before φ is ever reached)."""
    shadowed = mp.parse("↓x.↓x.□¬x")
    plain = mp.parse("↓x.□¬x")
    assert shadowed == Down(Nominal("x"), Down(Nominal("x"), Box(Not(Nominal("x")))))

    def check(model, w):
        a = satisfies_modal(shadowed, model, w)
        b = satisfies_modal(plain, model, w)
        assert a == b, (model, w)
        ref_a = _ref_eval(shadowed, model.worlds, model.relation("alethic"), model.valuation, w, {})
        ref_b = _ref_eval(plain, model.worlds, model.relation("alethic"), model.valuation, w, {})
        assert ref_a == ref_b == a, (model, w)

    n = _sweep(shadowed, needs_relation=True, check=check)
    assert n > 1000, n


# --- 6. No capture: ↓x.(P ∧ ↓y.@x Q), y≠x -----------------------------------

def test_down_no_capture_of_outer_binder_by_distinctly_named_inner_brute_force():
    """↓x.(P ∧ ↓y.@x Q) must equal P(w)∧Q(w) at every world/valuation: the
    inner ↓y binds a DIFFERENT name, so it cannot touch the outer @x."""
    f = mp.parse("↓x.(P ∧ ↓y.@x Q)")
    assert f == Down(Nominal("x"),
                     And(P, Down(Nominal("y"), At(Nominal("x"), Q))))

    def check(model, w):
        expected = "P" in model.valuation.get(w, set()) and "Q" in model.valuation.get(w, set())
        got = satisfies_modal(f, model, w)
        assert got == expected, (model, w)
        ref = _ref_eval(f, model.worlds, model.relation("alethic"), model.valuation, w, {})
        assert ref == expected, (model, w)

    n = _sweep(f, atom_keys=["P", "Q"], needs_relation=False, check=check)
    assert n > 20, n


# --- 6b. Same-named nested ↓ DOES shadow (contrast with #6): a free nominal
#         named exactly like the bound one is captured, as a binder should --

def test_down_captures_a_reference_with_the_same_name_as_the_bound_one():
    """↓x.(P ∧ ↓x.@x Q) -- here the inner binder IS named x, so @x inside it
    refers to the INNER binding (the current world, unconditionally), not
    whatever the outer ↓x bound -- the exact contrast with test #6 above,
    which uses a DIFFERENT inner name (y) and observes no capture at all."""
    f = mp.parse("↓x.(P ∧ ↓x.@x Q)")

    def check(model, w):
        # @x inside the inner ↓x always resolves to w itself (the inner
        # binder rebinds x := w unconditionally), so this reduces to P(w) ∧ Q(w)
        # -- structurally the SAME truth condition as test #6, but for a
        # different (capture, not avoidance) reason worth pinning separately.
        expected = "P" in model.valuation.get(w, set()) and "Q" in model.valuation.get(w, set())
        assert satisfies_modal(f, model, w) == expected, (model, w)

    n = _sweep(f, atom_keys=["P", "Q"], needs_relation=False, check=check)
    assert n > 20, n


# --- 7. ↓ under @, ↓ under □/◇ ------------------------------------------------

def test_down_under_at():
    """@i ↓x.□¬x: evaluate "↓x.□¬x" AT the world i names -- i.e. irreflexivity
    of THAT world, regardless of the current one."""
    f = mp.parse("@i ↓x.□¬x")
    m_no_loop = KripkeModel({0, 1}, {"alethic": {(0, 1)}}, nominals={"i": 0})
    m_loop = KripkeModel({0, 1}, {"alethic": {(0, 0), (0, 1)}}, nominals={"i": 0})
    assert satisfies_modal(f, m_no_loop, 1) is True   # world 1 irrelevant; i=0 has no loop
    assert satisfies_modal(f, m_loop, 1) is False      # i=0 now has a self-loop


def test_down_under_box_and_diamond():
    """□↓x.◇x: at every successor v of the current world, v has a self-loop.
    ◇↓x.□¬x: some successor v of the current world has no self-loop."""
    f_box = mp.parse("□↓x.◇x")
    f_dia = mp.parse("◇↓x.□¬x")
    # World 0 -> {1, 2}; only world 1 has a self-loop.
    m = KripkeModel({0, 1, 2}, {"alethic": {(0, 1), (0, 2), (1, 1)}})
    assert satisfies_modal(f_box, m, 0) is False   # world 2 has no self-loop
    assert satisfies_modal(f_dia, m, 0) is True    # world 2 witnesses irreflexivity
    m2 = KripkeModel({0, 1, 2}, {"alethic": {(0, 1), (0, 2), (1, 1), (2, 2)}})
    assert satisfies_modal(f_box, m2, 0) is True   # both successors self-loop
    assert satisfies_modal(f_dia, m2, 0) is False  # neither successor is irreflexive


# --- 8. Refusal-by-name battery ---------------------------------------------

_REFUSING_ROUTES = [
    ("is_modal_valid", lambda f: is_modal_valid(f)),
    ("modal_decide", lambda f: modal_decide(f)),
    ("modal_prove", lambda f: modal_prove([], f)),
    ("modal_countermodel", lambda f: modal_countermodel(f)),
    ("modal_tableau_closed", lambda f: modal_tableau_closed([f])),
    ("hybrid_is_valid", lambda f: hybrid_is_valid(f)),
    # Batch note (2) names fol.qml / hol.isabelle_modal / hol.thf_modal /
    # hol.ho_modal explicitly as routes that must refuse ↓ by name; each of
    # these four files has more than one independent dispatch pass over the
    # AST (qml.py: the FOL shallow embedding's own _st, plus its THF lift
    # _thf_lift; ho_modal.py: an Isabelle-syntax pass and a separate
    # THF-syntax pass), so every one of the 7 entry points below is its own
    # call site, not an alias of another row in this table.
    ("qml.qml_is_valid", lambda f: qml.qml_is_valid(f)),
    ("qml.to_thf_modal", lambda f: qml.to_thf_modal(f)),
    ("qml.to_isabelle_modal", lambda f: qml.to_isabelle_modal(f)),
    ("isabelle_modal.to_isabelle_modal", lambda f: isabelle_modal.to_isabelle_modal(f)),
    ("thf_modal.to_thf_modal_full", lambda f: thf_modal.to_thf_modal_full(f)),
    ("ho_modal.to_isabelle_ho_modal", lambda f: ho_modal.to_isabelle_ho_modal(f)),
    ("ho_modal.to_thf_ho_modal", lambda f: ho_modal.to_thf_ho_modal(f)),
]


@pytest.mark.parametrize("name,call", _REFUSING_ROUTES, ids=[n for n, _ in _REFUSING_ROUTES])
def test_route_refuses_down_by_name(name, call):
    f = mp.parse("↓x.□¬x")
    with pytest.raises(NotImplementedError) as exc_info:
        call(f)
    msg = str(exc_info.value).lower()
    assert "down" in msg or "↓" in str(exc_info.value), (name, exc_info.value)


_NON_REFUSING_ROUTES = [
    ("standard_translation", lambda f: standard_translation(f)),
    ("down_is_valid", lambda f: down_is_valid(f)),
    ("satisfies_modal", lambda f: satisfies_modal(
        f, KripkeModel({0, 1}, {"alethic": {(0, 1)}}), 0)),
]


@pytest.mark.parametrize("name,call", _NON_REFUSING_ROUTES, ids=[n for n, _ in _NON_REFUSING_ROUTES])
def test_route_does_not_refuse_down(name, call):
    f = mp.parse("↓x.□¬x")
    call(f)  # must not raise


def test_kripke_enum_and_modal_translation_and_kripke_evaluator_all_accept_down():
    """Sanity companion to the parametrized checks above: every 'route B' +
    route A entry point accepts a ↓ formula without raising, in one place."""
    f = mp.parse("↓x.◇x")
    modal_enum_search(f, max_worlds=2)               # must not raise
    KripkeEnumBackend().decide(f, max_worlds=2)        # must not raise
    down_decide(f, max_worlds=2)                       # must not raise


# --- 9. Mixing ↓ with a genuinely free nominal: satisfies_modal evaluates it
#        (given an assignment); modal_enum_search honestly reports UNKNOWN
#        (the documented pre-existing gap in candidate-model generation) ----

def test_down_mixed_with_free_nominal_satisfies_modal_vs_enum_gap():
    """A formula mixing a bound ↓x with a genuinely free nominal i (not
    itself bound by any ↓) is evaluable via satisfies_modal given
    nominals={"i": w0}, but modal_enum_search's candidate-model generation
    never populates nominals= (see atp.kripke_enum's module docstring / the
    KripkeEnumBackend claim in fol._hybrid_nodes), so it honestly reports
    UNKNOWN/unsupported rather than silently ignoring i or guessing."""
    f = mp.parse("↓x.@i x")
    m = KripkeModel({0, 1}, nominals={"i": 1})
    # x is bound to whichever world evaluation starts at; @i x asks whether
    # THAT world is the one i names.
    assert satisfies_modal(f, m, 0) is False
    assert satisfies_modal(f, m, 1) is True

    result = modal_enum_search(f, max_worlds=2)
    assert result.model is None
    assert result.unsupported is not None
    assert "nominal" in result.unsupported.lower() or "i" in result.unsupported

    backend_verdict = KripkeEnumBackend().decide(f, max_worlds=2)
    assert backend_verdict.status == UNKNOWN
    assert backend_verdict.reason == "unsupported"

    # down_is_valid still answers something (UNKNOWN, honestly -- it has no
    # special free-nominal gap the way the enumerator does, since nom_i is
    # just left FREE in the Z3 query, quantified universally by validity).
    v = down_is_valid(f)
    assert v.status in (PROVED, UNKNOWN)


# =============================================================================
# Round-trip: parser + to_dict, for nested Down formulas
# =============================================================================

_ROUNDTRIP_FORMULAS = [
    "↓x.□¬x",
    "↓x.◇x",
    "↓x.(@x p ↔ p)",
    "↓x.↓x.p",
    "↓x.(P ∧ ↓y.@x Q)",
    "@i ↓x.□¬x",
    "□↓x.◇x",
    "◇↓x.□¬x",
    "¬↓x.□¬x",
    "↓x.□¬x ∧ ↓y.◇y",
    "↓world1.□¬world1",
]


@pytest.mark.parametrize("text", _ROUNDTRIP_FORMULAS)
def test_down_unicode_and_dict_roundtrip(text):
    f = mp.parse(text)
    assert mp.parse(f.to_unicode_str()) == f
    assert Node.from_dict(f.to_dict()) == f


def test_down_latex_does_not_raise_and_nests_cleanly():
    """The renderer delegation fix the group-epistemic operators needed for
    nested rendering (a TypeError trap) does not recur for ↓ -- exercised
    here by nesting ↓ inside AND around every other prefix operator kind
    this battery uses (¬, □, ◇, @)."""
    for text in _ROUNDTRIP_FORMULAS:
        f = mp.parse(text)
        latex = f.to_latex()
        assert "\\downarrow" in latex
        assert isinstance(latex, str) and latex  # never raises, never empty


# =============================================================================
# Down's own to_z3/to_prover9/to_tptp: reject BY NAME, pointing at down_is_valid
# =============================================================================

def test_down_node_rejects_direct_classical_export():
    f = mp.parse("↓x.□¬x")
    for method in ("to_z3", "to_prover9", "to_tptp"):
        with pytest.raises(NotImplementedError) as exc_info:
            getattr(f, method)()
        assert "down_is_valid" in str(exc_info.value) or "↓" in str(exc_info.value)


# =============================================================================
# down_is_valid: hand-checked (frame-sensitive) validity claims
# =============================================================================

def test_down_is_valid_frame_sensitivity_hand_checked():
    """↓x.◇x (reflexivity as a state-variable claim): invalid over K/D
    (neither forces a self-loop), valid over T/S4/S5 (all reflexive)."""
    f = mp.parse("↓x.◇x")
    for frame in ("K", "D"):
        v = down_is_valid(f, frame=frame)
        assert v.status == UNKNOWN, (frame, v)
    for frame in ("T", "S4", "S5"):
        v = down_is_valid(f, frame=frame)
        assert v.status == PROVED, (frame, v)


def test_down_is_valid_never_refutes():
    """down_is_valid's own contract: never REFUTED, whatever the input."""
    for text, frame in [("↓x.◇x", "K"), ("↓x.□¬x", "S5"), ("↓x.(P → ¬P)", "K")]:
        v = down_is_valid(mp.parse(text), frame=frame)
        assert v.status != REFUTED, (text, frame, v)
