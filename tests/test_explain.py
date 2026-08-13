"""Tests for unicode_fol_kit.eval.explain.explain_countermodel.

Every expected string below is hand-derived from the semantics of the model it
describes (see each test's docstring for the derivation) — nothing here is a
snapshot of whatever the function happened to produce.
"""

import pytest

from unicode_fol_kit.eval.explain import explain_countermodel
from unicode_fol_kit.semantics.kripke import KripkeModel
from unicode_fol_kit.semantics.tarski import Structure
from unicode_fol_kit.semantics.modelfinder import find_countermodel
from unicode_fol_kit.fol.nodes import Atom, Box, Implies, Quantifier, Variable

P = Atom("P", [])


# ---------------------------------------------------------------------------
# KripkeModel: the chain that refutes axiom 4 (□p → □□p) in plain K
# ---------------------------------------------------------------------------

def _axiom4_countermodel():
    """Chain 0→1→2 (non-transitive: no 0→2 edge), P true only at world 1.

    Successors(0) = {1}, successors(1) = {2}, successors(2) = {}.
    - □P @0 = P@1 = True (1 is the only successor of 0, and P holds there).
    - □P @1 = P@2 = False (2 is the only successor of 1, and P fails there).
    - □□P @0 = □P holds at every successor of 0, i.e. at 1 = (□P @1) = False.
    So □P→□□P (axiom 4) is True→False = False at world 0: axiom 4 fails on a
    frame that is not transitive, exactly as K4 predicts.
    """
    return KripkeModel(
        worlds={0, 1, 2},
        relations={"alethic": {(0, 1), (1, 2)}},
        valuation={1: {"P"}},
    )


def test_kripke_countermodel_reports_worlds_edge_valuation_and_failure():
    """All four hand-derived facts appear verbatim in the explanation."""
    model = _axiom4_countermodel()
    axiom4 = Implies(Box(P), Box(Box(P)))
    text = explain_countermodel(model, axiom4)

    assert "3 possible worlds" in text          # world count = |{0,1,2}|
    assert "0 → 1" in text                      # a concrete edge of "alethic"
    assert "At world 1, the atom P is true." in text   # the one valuation fact
    assert "At world 0 the formula fails." in text     # axiom 4 is False @0
    assert text.count(".") >= 4                # at least 4 sentences landed


def test_kripke_no_relations_states_absence_explicitly():
    """A relation-free model gets an explicit 'no edges' sentence, not silence."""
    model = KripkeModel(worlds={0, 1}, valuation={0: {"P"}})
    text = explain_countermodel(model)
    assert "no accessibility edges" in text
    assert "2 possible worlds" in text


def test_kripke_formula_true_at_world_0_omits_fails_sentence():
    """□p→□□p on a model where it actually HOLDS at 0 must not claim failure.

    Reflexive-transitive single world {0} with a self-loop and P true there:
    □P@0 = P@0 = True; □□P@0 = □P@0 = True (only successor of 0 is 0 itself).
    True→True = True, so the formula does NOT fail at world 0 and the
    "fails" sentence must be absent.
    """
    model = KripkeModel(worlds={0}, relations={"alethic": {(0, 0)}},
                        valuation={0: {"P"}})
    axiom4 = Implies(Box(P), Box(Box(P)))
    text = explain_countermodel(model, axiom4)
    assert "the formula fails" not in text


def test_kripke_unevaluable_formula_omits_fails_sentence_instead_of_crashing():
    """A quantified formula raises NotImplementedError inside satisfies_modal;
    explain_countermodel must swallow that (per its honesty-note contract) and
    simply omit the fails sentence rather than propagate the crash."""
    model = KripkeModel(worlds={0})
    unevaluable = Quantifier("∀", Variable("x"), Atom("P", [Variable("x")]))
    text = explain_countermodel(model, unevaluable)  # must not raise
    assert "the formula fails" not in text


def test_kripke_max_sentences_caps_output_to_the_priority_prefix():
    """max_sentences=1 keeps exactly the (always-first) world-count sentence."""
    model = _axiom4_countermodel()
    axiom4 = Implies(Box(P), Box(Box(P)))
    text = explain_countermodel(model, axiom4, max_sentences=1)
    assert text == "The countermodel has 3 possible worlds."


def test_kripke_explanation_is_deterministic():
    """Two calls on the identical model+formula return byte-identical strings."""
    model = _axiom4_countermodel()
    axiom4 = Implies(Box(P), Box(Box(P)))
    first = explain_countermodel(model, axiom4)
    second = explain_countermodel(model, axiom4)
    assert first == second


# ---------------------------------------------------------------------------
# Structure: a real countermodel from find_countermodel(∀x P(x))
# ---------------------------------------------------------------------------

def test_structure_countermodel_from_modelfinder():
    """find_countermodel(∀x P(x)) must return a 1-element domain with P empty.

    The search tries domain size k=1 first, and for a single unary predicate
    over a 1-element domain the FIRST interpretation the enumerator tries sets
    P's extension to the empty set (P(0) = False) — which already witnesses
    ¬∀x P(x), so the search stops there without ever trying k=1/P=True or any
    larger domain. Hence: domain = (0,), P/1 holds for nothing.
    """
    formula = Quantifier("∀", Variable("x"), Atom("P", [Variable("x")]))
    structure = find_countermodel([], formula)
    assert isinstance(structure, Structure)
    assert structure.domain == (0,)
    assert structure.predicates[("P", 1)] == set()

    text = explain_countermodel(structure)
    assert "The domain has 1 individual: 0." in text
    assert "The predicate P/1 holds for no tuples." in text


def test_structure_reports_constant_denotation_and_nonempty_predicate():
    """Hand-built structure: domain {0,1}, constant a=0, P true only at 1."""
    structure = Structure(
        domain=[0, 1],
        constants={"a": 0},
        predicates={("P", 1): {(1,)}},
    )
    text = explain_countermodel(structure)
    assert "The domain has 2 individuals: 0, 1." in text
    assert "a denotes 0" in text
    assert "The predicate P/1 holds for: (1)." in text


def test_structure_explanation_is_deterministic():
    formula = Quantifier("∀", Variable("x"), Atom("P", [Variable("x")]))
    structure = find_countermodel([], formula)
    first = explain_countermodel(structure)
    second = explain_countermodel(structure)
    assert first == second


# ---------------------------------------------------------------------------
# Z3-style assignment dict (bare, and wrapped as a "z3_model" witness)
# ---------------------------------------------------------------------------

def test_z3_bare_assignment_enumerates_sorted_by_name():
    """{'x': '2', 'P': 'True'} must list P before x (sorted) with '... := ...'."""
    assignment = {"x": "2", "P": "True"}
    text = explain_countermodel(assignment)
    assert "P := True" in text
    assert "x := 2" in text
    assert text.index("P := True") < text.index("x := 2")   # P sorts before x
    assert "Under the assignment" in text


def test_z3_model_witness_dict_matches_bare_assignment():
    """The Verdict-layer {'kind': 'z3_model', 'assignment': {...}} shape must
    explain identically to passing the bare assignment dict directly — the
    kind wrapper is routing, not a change of meaning."""
    assignment = {"x": "2", "P": "True"}
    bare = explain_countermodel(assignment)
    wrapped = explain_countermodel({"kind": "z3_model", "assignment": assignment})
    assert bare == wrapped


def test_z3_assignment_explanation_is_deterministic_regardless_of_dict_order():
    """Two dicts with the same entries in different insertion order must still
    produce the identical explanation, since assignments are sorted by name."""
    a = {"x": "2", "P": "True"}
    b = {"P": "True", "x": "2"}
    assert explain_countermodel(a) == explain_countermodel(b)


# ---------------------------------------------------------------------------
# Repr-only witness dicts (kripke / finite_structure / nitpick / ...)
# ---------------------------------------------------------------------------

def test_repr_only_witness_frames_the_repr_without_pretending_it_is_structured():
    witness = {"kind": "kripke", "repr": "KripkeModel(worlds={0, 1}, ...)"}
    text = explain_countermodel(witness)
    assert "kripke" in text
    assert "not a structured payload" in text
    assert "KripkeModel(worlds={0, 1}, ...)" in text


def test_repr_only_witness_handles_any_kind_name():
    """A kind the module has never heard of (e.g. Isabelle's 'nitpick') still
    gets the same honest repr-framing rather than an error."""
    witness = {"kind": "nitpick", "repr": "Nitpick found a counterexample: ..."}
    text = explain_countermodel(witness)
    assert "nitpick" in text
    assert "Nitpick found a counterexample" in text


# ---------------------------------------------------------------------------
# Error contract for unrecognised input
# ---------------------------------------------------------------------------

def test_malformed_kind_dict_raises_value_error():
    """A dict with a 'kind' but neither a usable 'assignment' nor a 'repr' has
    nothing to explain, and must fail loudly rather than emit a blank guess."""
    with pytest.raises(ValueError):
        explain_countermodel({"kind": "z3_model"})


def test_unsupported_type_raises_type_error():
    with pytest.raises(TypeError):
        explain_countermodel(42)
