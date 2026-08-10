"""Cross-family ``bridges=`` axioms in the two HOL routes, and the tableau's refusal.

``frame=`` and ``systems=`` each constrain ONE accessibility relation. A *bridge*
relates two relations of DIFFERENT modal families, so it is a separate, opt-in
option. Three exist:

    knowledge_implies_belief   K_a φ → B_a φ     rb ⊆ rk                 (rb_in_rk)
    sincerity                  Say_a φ → B_a φ   rb ⊆ rs                 (rb_in_rs)
    ought_implies_can          Oφ → ◇φ           ∀w ∃v. d w v ∧ r w v    (d_meets_r)

These tests are STRING-LEVEL by design, so they run on every machine whether or not
Isabelle is installed (they carry no ``isabelle_live`` marker and spawn no build).
What is checked here is that the right axiom text is emitted (and only when asked
for), that the axiom's NAME reaches ``modal_axiom_names`` and therefore the emitted
``using ... by ...`` proof, that the two HOL routes carry the same registry, and
that the modal tableau refuses the option instead of silently deciding the
bridge-free logic. Whether the emitted Isabelle syntax actually loads is a question
only a live Isabelle can answer — that is the ``isabelle_live`` suites' job.

The one thing measured rather than asserted from the literature is the LOGIC: a
brute-force sweep over every frame on ≤ 2 worlds against ``satisfies_modal`` confirms
each condition is the *exact* correspondent of its schema — sufficient AND not
over-strong — and in particular that the folklore ``d ⊆ r`` is the wrong axiom for
ought-implies-can (it fails to validate ``Oφ → ◇φ`` on its own and, with seriality,
over-validates ``□φ → Oφ``).
"""

import itertools

import pytest

from unicode_fol_kit.hol.isabelle_modal import (
    BRIDGES, to_isabelle_modal, isabelle_modal_theory, modal_axiom_names,
    _BRIDGES as _ISA_BRIDGES,
)
from unicode_fol_kit.hol.thf_modal import (
    to_thf_modal_full, thf_full_frame_axioms, _THF_BRIDGE_LINES,
)
from unicode_fol_kit.atp import modal_tableau as mt

from unicode_fol_kit.fol.nodes import (
    Atom, And, Implies, Box, Diamond, Knows, Believes, Says, Obligatory,
    Permitted, Constant,
)
from unicode_fol_kit.semantics.kripke import KripkeModel, satisfies_modal


P = Atom("P", [])
AG = Constant("agent1")

# One formula per bridge, stating BOTH of its families so the bridge is emittable.
KB = Implies(Knows(AG, P), Believes(AG, P))            # epistemic + doxastic
SB = Implies(Says(AG, P), Believes(AG, P))             # assertive + doxastic
OC = Implies(Obligatory(P), Diamond(P))                # deontic + alethic
ALL_THREE = And(KB, And(SB, OC))

# The exact Isabelle axiom text each bridge must emit.
ISA_LINE = {
    "knowledge_implies_belief":
        'axiomatization where rb_in_rk: '
        '"\\<And>a w v. rb a w v \\<Longrightarrow> rk a w v"',
    "sincerity":
        'axiomatization where rb_in_rs: '
        '"\\<And>a w v. rb a w v \\<Longrightarrow> rs a w v"',
    "ought_implies_can":
        'axiomatization where d_meets_r: '
        '"\\<And>w. \\<exists>v. d w v \\<and> r w v"',
}
FACT_NAME = {"knowledge_implies_belief": "rb_in_rk",
             "sincerity": "rb_in_rs",
             "ought_implies_can": "d_meets_r"}
FORMULA = {"knowledge_implies_belief": KB, "sincerity": SB, "ought_implies_can": OC}


# --------------------------------------------------------------------------- #
# Isabelle route: emitted iff requested.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("name", BRIDGES)
def test_isabelle_bridge_axiom_emitted_when_requested(name):
    thy = to_isabelle_modal(FORMULA[name], bridges=[name])
    assert ISA_LINE[name] in thy, thy


@pytest.mark.parametrize("name", BRIDGES)
def test_isabelle_bridge_axiom_absent_by_default(name):
    """Bridges are OFF unless asked for — the default logic must not shift."""
    thy = to_isabelle_modal(FORMULA[name])
    assert FACT_NAME[name] not in thy, thy
    assert ISA_LINE[name] not in thy


@pytest.mark.parametrize("name", BRIDGES)
def test_isabelle_bridge_axiom_absent_when_another_is_requested(name):
    """Requesting one bridge must not drag the others in."""
    other = next(n for n in BRIDGES if n != name)
    thy = to_isabelle_modal(ALL_THREE, bridges=[other])
    assert FACT_NAME[name] not in thy or name == other


def test_isabelle_all_three_bridges_at_once():
    thy = to_isabelle_modal(ALL_THREE, bridges=list(BRIDGES))
    for name in BRIDGES:
        assert ISA_LINE[name] in thy, name


# --------------------------------------------------------------------------- #
# The ``using <axioms> by <tactic>`` contract: the proof must SEE the fact.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("name", BRIDGES)
def test_modal_axiom_names_reports_the_bridge_fact(name):
    names = modal_axiom_names(FORMULA[name], bridges=[name])
    assert FACT_NAME[name] in names, names


@pytest.mark.parametrize("name", BRIDGES)
def test_by_tactic_proof_uses_the_bridge_fact(name):
    """An axiomatization fact is not in the default claset: without ``using`` the
    ``by blast`` could not discharge a bridge-dependent validity at all."""
    thy = to_isabelle_modal(FORMULA[name], tactic="blast", bridges=[name])
    using = [ln for ln in thy.splitlines() if ln.startswith("  using ")]
    assert len(using) == 1, thy
    assert FACT_NAME[name] in using[0], using


def test_bridges_default_leaves_axiom_names_unchanged():
    """Regression pin for the exact-list assertions elsewhere in the suite: the
    bridge block is APPENDED, so bridges=None changes neither content nor order."""
    assert modal_axiom_names(Box(P), frame="S4") == ["r_refl", "r_trans"]
    assert modal_axiom_names(Box(P), frame="S4", bridges=None) == ["r_refl", "r_trans"]
    assert modal_axiom_names(OC, frame="K") == ["d_serial"]
    # The bridge is appended AFTER the pre-existing axioms, never interleaved.
    assert modal_axiom_names(OC, frame="K", bridges=["ought_implies_can"]) == [
        "d_serial", "d_meets_r"]


def test_emission_order_is_registry_order_not_caller_order():
    """Deterministic output: a set's iteration order must not reach the theory."""
    a = modal_axiom_names(ALL_THREE, bridges=list(BRIDGES))
    b = modal_axiom_names(ALL_THREE, bridges=list(reversed(list(BRIDGES))))
    c = modal_axiom_names(ALL_THREE, bridges=set(BRIDGES))
    assert a == b == c
    assert a == ["d_serial", "rb_in_rk", "rb_in_rs", "d_meets_r"]


# --------------------------------------------------------------------------- #
# ought_implies_can must stay the MEET condition, never the ``d ⊆ r`` inclusion.
# --------------------------------------------------------------------------- #

def test_d_meets_r_is_existential_not_an_inclusion():
    """Shape pin against a future "simplification" of d_meets_r into ``d ⊆ r``.

    Measured (see test_measured_correspondents_are_exact): ``d ⊆ r`` does not
    validate ``Oφ → ◇φ`` at all, and ``d ⊆ r`` + seriality additionally validates
    the strictly stronger ``□φ → Oφ`` that no caller asked for.
    """
    thy = to_isabelle_modal(OC, bridges=["ought_implies_can"])
    assert "\\<exists>v. d w v \\<and> r w v" in thy
    assert "d w v \\<Longrightarrow> r w v" not in thy


def test_thf_d_meets_r_is_existential_not_an_inclusion():
    thf = to_thf_modal_full(OC, bridges=["ought_implies_can"])
    assert "? [V: mu] : ( ( d @ W @ V ) & ( r @ W @ V ) )" in thf
    assert "( d @ W @ V ) => ( r @ W @ V )" not in thf


# --------------------------------------------------------------------------- #
# Refusals: a bridge whose partner family is absent, unknown names, bare strings.
# --------------------------------------------------------------------------- #

# (bridge, a formula mentioning only ONE of its two families, the missing operator)
MISSING_CASES = [
    ("knowledge_implies_belief", Knows(AG, P), "Believes"),
    ("knowledge_implies_belief", Believes(AG, P), "Knows"),
    ("sincerity", Says(AG, P), "Believes"),
    ("sincerity", Believes(AG, P), "Says"),
    ("ought_implies_can", Obligatory(P), "□/◇"),
    ("ought_implies_can", Box(P), "Obligatory/Permitted"),
]


@pytest.mark.parametrize("name,formula,missing", MISSING_CASES)
def test_isabelle_missing_family_raises(name, formula, missing):
    """Never silently skipped (weaker logic) and never silently declared (stronger)."""
    with pytest.raises(ValueError) as exc:
        to_isabelle_modal(formula, bridges=[name])
    msg = str(exc.value)
    assert name in msg and missing in msg
    assert "weaker logic" in msg


@pytest.mark.parametrize("name,formula,missing", MISSING_CASES)
def test_thf_missing_family_raises(name, formula, missing):
    """The THF route declares every relation, so the axiom WOULD be well-formed —
    it still refuses, because emitting it would make the two HOL routes disagree."""
    with pytest.raises(ValueError) as exc:
        to_thf_modal_full(formula, bridges=[name])
    msg = str(exc.value)
    assert name in msg and missing in msg
    assert "disagree" in msg


@pytest.mark.parametrize("emit", [to_isabelle_modal, to_thf_modal_full])
def test_bare_string_rejected(emit):
    """``bridges="sincerity"`` would otherwise iterate characters."""
    with pytest.raises(ValueError, match="not a single string"):
        emit(SB, bridges="sincerity")


@pytest.mark.parametrize("emit", [to_isabelle_modal, to_thf_modal_full])
def test_unknown_bridge_name_rejected(emit):
    with pytest.raises(ValueError) as exc:
        emit(ALL_THREE, bridges=["knowledge_belief"])
    msg = str(exc.value)
    assert "unknown bridge" in msg
    for name in BRIDGES:
        assert name in msg          # the message lists the valid names


def test_unknown_bridge_rejected_in_the_inspection_helper():
    with pytest.raises(ValueError, match="unknown bridge"):
        thf_full_frame_axioms(bridges=["nope"])
    with pytest.raises(ValueError, match="not a single string"):
        thf_full_frame_axioms(bridges="sincerity")


def test_modal_axiom_names_refuses_too():
    """The runner's ``using`` list must not disagree with the emitted theory."""
    with pytest.raises(ValueError):
        modal_axiom_names(Box(P), bridges=["ought_implies_can"])


# --------------------------------------------------------------------------- #
# THF route.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("name", BRIDGES)
def test_thf_bridge_axiom_emitted_when_requested(name):
    thf = to_thf_modal_full(FORMULA[name], bridges=[name])
    for line in _THF_BRIDGE_LINES[name]:
        assert line in thf, thf


@pytest.mark.parametrize("name", BRIDGES)
def test_thf_bridge_axiom_absent_by_default(name):
    thf = to_thf_modal_full(FORMULA[name])
    assert f"thf({FACT_NAME[name]}," not in thf


def test_thf_frame_axioms_helper_lists_bridges_unconditionally():
    """The helper takes no formula, so — exactly as it already does for systems=
    and d_serial — it emits every requested bridge without a family check."""
    base = thf_full_frame_axioms()
    with_all = thf_full_frame_axioms(bridges=list(BRIDGES))
    for name in BRIDGES:
        for line in _THF_BRIDGE_LINES[name]:
            assert line not in base
            assert line in with_all
    # appended at the END, so existing membership-style assertions are unaffected
    assert with_all[:len(base)] == base


def test_thf_problem_stays_well_formed_with_all_bridges():
    thf = to_thf_modal_full(ALL_THREE, frame="T", bridges=list(BRIDGES))
    for line in thf.splitlines():
        if line.startswith("thf("):
            assert line.rstrip().endswith(")."), line
        assert line.count("(") == line.count(")"), line


# --------------------------------------------------------------------------- #
# Cross-route parity — the test that stops the two HOL routes drifting apart.
# --------------------------------------------------------------------------- #

def test_bridge_registries_agree_across_routes():
    assert set(_THF_BRIDGE_LINES) == set(_ISA_BRIDGES) == set(BRIDGES)
    assert tuple(_THF_BRIDGE_LINES) == tuple(_ISA_BRIDGES), "emission order differs"


def test_bridge_fact_names_are_shared_verbatim():
    """A single ``grep rb_in_rk`` must find both routes."""
    for name in BRIDGES:
        fact = FACT_NAME[name]
        assert fact in " ".join(_ISA_BRIDGES[name]["lines"])
        assert f"thf({fact}," in " ".join(_THF_BRIDGE_LINES[name])


def test_required_families_are_shared():
    """Both routes must refuse on exactly the same formulas."""
    for name in BRIDGES:
        fams = {fam for fam, _op in _ISA_BRIDGES[name]["needs"]}
        for f in fams:
            # every required family is one the THF route also tracks
            assert f in ("alethic", "epistemic", "doxastic", "assertive",
                         "bouletic", "deontic"), (name, f)


def test_structural_invariants_of_a_bridge_carrying_theory():
    thy = isabelle_modal_theory(ALL_THREE, frame="T", theory_name="Br",
                                bridges=list(BRIDGES))
    assert thy.startswith("theory Br")
    assert thy.rstrip().endswith("end")
    depth = 0
    for ch in thy:
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
            assert depth >= 0
    assert depth == 0
    assert thy.count('"') % 2 == 0
    assert thy.count("\\<open>") == thy.count("\\<close>")


# --------------------------------------------------------------------------- #
# The modal tableau refuses the option (it has no cross-relation rule).
# --------------------------------------------------------------------------- #

_ENTRY_POINTS = [
    (mt.modal_tableau_closed, ([KB],)),
    (mt.is_modal_valid, (KB,)),
    (mt.modal_prove, ([], KB)),
    (mt.modal_countermodel, (KB,)),
    (mt.modal_decide, (KB,)),
]


@pytest.mark.parametrize("fn,args", _ENTRY_POINTS)
@pytest.mark.parametrize("name", BRIDGES)
def test_tableau_refuses_every_bridge_on_every_entry_point(fn, args, name):
    with pytest.raises(NotImplementedError) as exc:
        fn(*args, bridges=[name])
    msg = str(exc.value)
    assert name in msg
    # names the routes that CAN express it (the existing guard style in that file)
    assert "qml_is_valid" in msg
    assert "to_isabelle_modal" in msg
    assert "to_thf_modal_full" in msg


def test_tableau_refuses_a_bare_string_bridge_too():
    with pytest.raises(NotImplementedError, match="sincerity"):
        mt.modal_decide(SB, bridges="sincerity")


@pytest.mark.parametrize("fn,args", _ENTRY_POINTS)
def test_tableau_unaffected_when_no_bridge_is_requested(fn, args):
    """bridges=None / [] must be a pure no-op, not a new failure mode."""
    fn(*args)
    fn(*args, bridges=None)
    fn(*args, bridges=[])


def test_tableau_still_decides_the_bridge_free_logic():
    """Sanity: without a bridge, K_a P → B_a P is genuinely invalid — which is
    exactly why silently ignoring bridges= would be a wrong answer, not a harmless
    one."""
    assert mt.modal_decide(KB) == "invalid"
    assert mt.modal_decide(SB) == "invalid"
    assert mt.modal_decide(OC, systems={"deontic": "KD"}) == "invalid"


# --------------------------------------------------------------------------- #
# MEASURED: each condition is the EXACT correspondent of its schema.
# --------------------------------------------------------------------------- #

def _all_relations(worlds):
    pairs = [(w, v) for w in worlds for v in worlds]
    for k in range(len(pairs) + 1):
        for combo in itertools.combinations(pairs, k):
            yield frozenset(combo)


def _frames(n, relnames):
    """Every frame on ``n`` worlds over ``relnames``, with every valuation of P."""
    worlds = list(range(n))
    rels = list(_all_relations(worlds))
    for choice in itertools.product(rels, repeat=len(relnames)):
        for bits in itertools.product([0, 1], repeat=n):
            val = {w: ({"P"} if bits[w] else set()) for w in worlds}
            yield KripkeModel(worlds, dict(zip(relnames, choice)), val)


def _valid_under(formula, relnames, condition, nmax=2):
    """True iff ``formula`` holds at every world of every frame meeting ``condition``."""
    for n in range(1, nmax + 1):
        for m in _frames(n, relnames):
            if not condition(m):
                continue
            for w in m.worlds:
                if not satisfies_modal(formula, m, w):
                    return False
    return True


def _edges(m, name):
    return set(m.relations.get(name, frozenset()))


def _included(src, dst):
    return lambda m: _edges(m, src) <= _edges(m, dst)


def _meets(m):
    d, r = _edges(m, "deontic"), _edges(m, "alethic")
    return all(any((w, v) in d and (w, v) in r for v in m.worlds) for w in m.worlds)


def _serial(name):
    return lambda m: all(any((w, v) in _edges(m, name) for v in m.worlds)
                         for w in m.worlds)


_ANY = lambda m: True
_EPI = ["K:agent1", "B:agent1"]
_ASS = ["Say:agent1", "B:agent1"]
_DEO = ["deontic", "alethic"]


def test_inclusion_bridges_are_exact_correspondents():
    """Sufficient AND not over-strong AND not vacuous — for both inclusions."""
    rb_in_rk = _included("B:agent1", "K:agent1")
    assert _valid_under(KB, _EPI, rb_in_rk)                       # sufficient
    assert not _valid_under(Implies(Believes(AG, P), Knows(AG, P)),
                            _EPI, rb_in_rk)                       # not over-strong
    assert not _valid_under(KB, _EPI, _ANY)                       # not vacuous

    rb_in_rs = _included("B:agent1", "Say:agent1")
    assert _valid_under(SB, _ASS, rb_in_rs)
    assert not _valid_under(Implies(Believes(AG, P), Says(AG, P)), _ASS, rb_in_rs)
    assert not _valid_under(SB, _ASS, _ANY)


def test_d_meets_r_is_the_right_ought_implies_can_condition():
    assert _valid_under(OC, _DEO, _meets)
    # ...and does NOT drag in "whatever is necessary is obligatory".
    assert not _valid_under(Implies(Box(P), Obligatory(P)), _DEO, _meets)
    assert not _valid_under(OC, _DEO, _ANY)


def test_the_d_subset_r_trap_is_measured_not_folklore():
    """Why the emitted axiom is NOT the frequently quoted inclusion ``d ⊆ r``."""
    d_in_r = _included("deontic", "alethic")
    # (a) on its own it does not validate ought-implies-can at all,
    assert not _valid_under(OC, _DEO, d_in_r)
    # (b) with seriality it does — but then it ALSO validates the strictly
    #     stronger □φ → Oφ, which the caller never requested,
    both = lambda m: d_in_r(m) and _serial("deontic")(m)
    assert _valid_under(OC, _DEO, both)
    assert _valid_under(Implies(Box(P), Obligatory(P)), _DEO, d_in_r)
    # (c) while the emitted meet condition subsumes d-seriality by itself.
    assert _valid_under(Implies(Obligatory(P), Diamond(P)), _DEO, _meets)


def test_names_match_the_qml_route():
    """The option names must be identical across every route that offers bridges."""
    from unicode_fol_kit.fol.qml import QML_BRIDGES
    assert set(QML_BRIDGES) == set(BRIDGES)


def test_qml_and_hol_agree_on_ought_implies_can_strength():
    """One option name, one logic — on the FO route as well as the HOL ones.

    ``fol.qml`` used to realise ``ought_implies_can`` as the inclusion ``D ⊆ R``,
    which (measured in ``test_the_d_subset_r_trap_is_measured_not_folklore``)
    additionally validates ``□φ → Oφ`` and ``Pφ → ◇φ``. It now emits the same exact
    correspondent the HOL routes do, so all three routes decide the same three
    principles the same way. Asserted against the Kripke oracle AND against qml's
    own verdicts, because the two registries are deliberately separate modules.
    """
    from unicode_fol_kit.fol.qml import QML_BRIDGES, qml_is_valid
    assert QML_BRIDGES["ought_implies_can"]["fact"] == "d_meets_r"
    artifact = Implies(Box(P), Obligatory(P))
    permission = Implies(Permitted(P), Diamond(P))
    d_in_r = _included("deontic", "alethic")
    # the oracle: the inclusion over-validates where the meet condition does not.
    assert _valid_under(artifact, _DEO, d_in_r) is True
    assert _valid_under(artifact, _DEO, _meets) is False
    assert _valid_under(permission, _DEO, _meets) is False
    # ...and qml now answers for the meet condition's model class.
    assert qml_is_valid(OC, bridges=["ought_implies_can"]) is True
    for f in (artifact, permission):
        assert qml_is_valid(f, bridges=["ought_implies_can"], timeout=1000) is False


def test_d_meets_r_entails_alethic_seriality():
    """The reason a missing family RAISES instead of declaring the relation anyway:
    d_meets_r is not conservative on the alethic logic the caller did select."""
    assert _valid_under(Diamond(Implies(P, P)), _DEO, _meets)     # ◇⊤, i.e. r serial
    assert not _valid_under(Diamond(Implies(P, P)), _DEO, _ANY)
