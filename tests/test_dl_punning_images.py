r"""One name as a class, an object property and an individual; and the checks across boxes.

OWL 2 DL lets one IRI be a class, an object property and an individual at once
("punning"); only an object property that is also a data property, and a class that
is also a datatype, are forbidden. The first-order image writes a class as a unary
predicate, an object property as a binary predicate and an individual as a constant,
so ``A`` used as all three is THREE symbols: ``A(x)``, ``A(x, y)`` and the constant
``A``. Nothing is conflated, and nothing is refused.

Hand-derived knowledge bases (``A``, ``B``, ``C`` classes, ``p`` and ``A`` also roles
and individuals):

* K1. TBox ``A ⊑ ∃A.B``, ABox ``A : A``. Image ``∀x (A(x) → ∃y (A(x, y) ∧ B(y))) ∧
  A(A)``.

  - ``A : ∃A.B`` is ENTAILED: ``A(A)`` puts the element ``A`` in the class, the
    inclusion then gives it an ``A``-successor in ``B``.
  - ``A : B`` is NOT entailed. Countermodel, domain ``{0, 1}``, constant ``A = 0``,
    ``A/1 = {0}``, ``A/2 = {(0, 1)}``, ``B = {1}``: the inclusion holds at ``0``
    (successor ``1``, in ``B``) and vacuously at ``1`` (not in ``A/1``), ``A(A)`` is
    ``A(0)``, true; ``B(A)`` is ``B(0)``, false.

* K2. TBox ``∃p.⊤ ⊑ C``, ABox ``(p, q) : p``. Image ``∀x (∃y (p(x, y) ∧ y = y) →
  C(x)) ∧ p(p, q)``.

  - ``p : C`` is ENTAILED: ``p(p, q)`` gives the element ``p`` a ``p``-successor.
  - ``q : C`` is NOT entailed. Countermodel, domain ``{0, 1}``, ``p = 0``, ``q = 1``,
    ``p/2 = {(0, 1)}``, ``C = {0}``: the inclusion holds at ``0`` (successor ``1``)
    and at ``1`` (no successor), ``p(p, q)`` is ``p(0, 1)``, ``C(q)`` is ``C(1)``,
    false.
"""

import itertools
import shutil
import subprocess

import pytest

import unicode_logic_kit.dl as dl
from unicode_logic_kit import api
from unicode_logic_kit.dl.datatypes import Datatype, UnsupportedDatatypeError
from unicode_logic_kit.fol.nodes import And as FAnd, Atom, Constant
from unicode_logic_kit.semantics.tarski import Structure, satisfies

A, B, C = dl.Atomic("A"), dl.Atomic("B"), dl.Atomic("C")
INT = Datatype("xsd:integer")
TIMEOUT_MS = 30000


def _k1():
    return (dl.TBox().add(A, dl.Exists("A", B)), dl.ABox().assert_concept("A", A))


def _k2():
    return (dl.TBox().add(dl.Exists("p", dl.Top()), C), dl.ABox().assert_role("p", "q", "p"))


#: (name, knowledge base, [(individual, concept, entailed)]) — see the module docstring.
KNOWLEDGE_BASES = [
    ("class-role-individual", _k1, [("A", dl.Exists("A", B), True), ("A", B, False)]),
    ("role-individual", _k2, [("p", C, True), ("q", C, False)]),
]
CASES = [(name, make, individual, concept, entailed)
         for name, make, questions in KNOWLEDGE_BASES
         for individual, concept, entailed in questions]
CASE_IDS = [f"{name}-{individual}-{'entailed' if entailed else 'not-entailed'}"
            for name, _make, individual, _concept, entailed in CASES]


def _bundle(make, concept):
    tbox, abox = make()
    return dl.kb_to_fol(tbox, abox, query=[concept])


def _symbols(node):
    """``(predicate, arity)`` of every non-comparison atom, and every constant name."""
    predicates = {(n.predicate, len(n.args)) for n in node.walk()
                  if isinstance(n, Atom) and n.predicate not in ("=", "≠")}
    constants = {n.name for n in node.walk() if isinstance(n, Constant)}
    return predicates, constants


# --------------------------------------------------------------------------- #
# The image: three symbols, the same in every box-wise function.
# --------------------------------------------------------------------------- #

def test_the_image_of_a_name_used_as_class_property_and_individual_is_three_symbols():
    tbox, abox = _k1()
    kb = dl.kb_to_fol(tbox, abox)
    assert len(kb.premises) == 1
    predicates, constants = _symbols(kb.formula)
    assert predicates == {("A", 1), ("A", 2), ("B", 1)}
    assert constants == {"A"}
    assert kb.formula.to_unicode_str() == "∀x (A(x) → ∃x0 (A(x, x0) ∧ B(x0))) ∧ A('A')"


def test_the_box_by_box_images_are_the_images_of_the_whole():
    tbox, abox = _k1()
    tbox.add_transitive_role("A")
    kb = dl.kb_to_fol(tbox, abox)
    gcis = dl.tbox_to_fol(tbox, concept_inclusions_only=True)
    assert kb.formula == FAnd(gcis, dl.abox_to_fol(abox))
    assert FAnd(kb.tbox, kb.abox) == kb.formula
    # the role box is the only place the binary A is the whole formula
    assert _symbols(dl.rbox_to_fol(tbox)) == ({("A", 2)}, set())
    assert dl.rbox_to_fol(tbox) == kb.rbox_axioms[0]
    assert _symbols(gcis) == ({("A", 1), ("A", 2), ("B", 1)}, set())
    assert _symbols(dl.abox_to_fol(abox)) == ({("A", 1)}, {"A"})


def test_a_class_that_puns_a_data_property_is_two_symbols_too():
    # OWL 2 DL forbids an object property that is a data property, and a class that
    # is a datatype; a class and a data property of one name are allowed.
    tbox = dl.TBox().add(A, B).add_data_property_range("A", INT)
    kb = dl.kb_to_fol(tbox, dl.ABox().assert_concept("A", A))
    predicates = set()
    for premise in kb.premises:
        predicates |= _symbols(premise)[0]
    assert {("A", 1), ("A", 2)} <= predicates


# --------------------------------------------------------------------------- #
# The answers, from the definition, not from a prover.
# --------------------------------------------------------------------------- #

def _countermodel(case):
    if case == "class-role-individual":
        return Structure((0, 1), constants={"A": 0},
                         predicates={("A", 1): {(0,)}, ("A", 2): {(0, 1)}, ("B", 1): {(1,)}})
    return Structure((0, 1), constants={"p": 0, "q": 1},
                     predicates={("p", 2): {(0, 1)}, ("C", 1): {(0,)}})


NOT_ENTAILED = [case for case in CASES if not case[4]]


@pytest.mark.parametrize("name, make, individual, concept, entailed", NOT_ENTAILED,
                         ids=[f"{case[0]}-{case[2]}" for case in NOT_ENTAILED])
def test_the_hand_built_countermodel_separates_what_is_not_entailed(
        name, make, individual, concept, entailed):
    kb = _bundle(make, concept)
    model = _countermodel(name)
    assert all(satisfies(premise, model) for premise in kb.premises)
    assert satisfies(kb.instance_goal(individual, concept), model) is False


@pytest.mark.parametrize("name, make, individual, concept, entailed", CASES, ids=CASE_IDS)
def test_no_structure_of_up_to_two_elements_contradicts_the_derivation(
        name, make, individual, concept, entailed):
    # Every structure over a domain of one and of two elements for the symbols of the
    # image (512 + 8 for K1, 256 + 4 for K2): a model of the premises falsifies the
    # goal exactly when the goal is not entailed. A bounded check, for the cases the
    # derivation says are entailed (no countermodel of this size) and for the ones it
    # says are not (the countermodel above is one of them).
    kb = _bundle(make, concept)
    goal = kb.instance_goal(individual, concept)
    constants = ["A"] if name == "class-role-individual" else ["p", "q"]
    predicates = ([("A", 1), ("A", 2), ("B", 1)] if name == "class-role-individual"
                  else [("p", 2), ("C", 1)])
    found = False
    for size in (1, 2):
        domain = tuple(range(size))
        extensions = [[frozenset(subset) for subset in _subsets(list(itertools.product(domain, repeat=arity)))]
                      for _name, arity in predicates]
        for values in itertools.product(domain, repeat=len(constants)):
            for chosen in itertools.product(*extensions):
                model = Structure(domain, constants=dict(zip(constants, values)),
                                  predicates={key: set(ext) for key, ext in zip(predicates, chosen)})
                if all(satisfies(p, model) for p in kb.premises) and not satisfies(goal, model):
                    found = True
    assert found is (not entailed)


def _subsets(items):
    for mask in range(1 << len(items)):
        yield [item for bit, item in enumerate(items) if mask >> bit & 1]


# --------------------------------------------------------------------------- #
# The answers of the routes.
# --------------------------------------------------------------------------- #

def _vampire_route():
    """``"native"``, ``"wsl"`` or ``None``: where a Vampire binary is reachable."""
    if shutil.which("vampire"):
        return "native"
    try:
        probe = subprocess.run(["wsl.exe", "vampire", "--version"], capture_output=True,
                               text=True, timeout=30)
        if probe.returncode == 0 and "Vampire" in probe.stdout:
            return "wsl"
    except Exception:                              # noqa: BLE001 — any failure means "absent"
        pass
    return None


_VAMPIRE = _vampire_route()


def _eprover_ready():
    from unicode_logic_kit.atp import eprover_available
    return eprover_available() is True


def _status(backend, make, individual, concept):
    kb = _bundle(make, concept)
    return api.prove(kb.instance_goal(individual, concept), kb.premises,
                     backends=[backend], timeout=TIMEOUT_MS)


@pytest.mark.skipif(_VAMPIRE is None, reason="no Vampire reachable (PATH, or 'wsl vampire')")
@pytest.mark.parametrize("name, make, individual, concept, entailed", CASES, ids=CASE_IDS)
def test_the_tptp_route_answers_a_punned_knowledge_base_as_derived(
        monkeypatch, name, make, individual, concept, entailed):
    # fof writes A/1, A/2 and the constant as three symbols, so Vampire is asked the
    # question of the derivation above and not a conflated one.
    monkeypatch.setenv("UFK_VAMPIRE", "vampire")
    monkeypatch.setenv("UFK_VAMPIRE_WSL", "1" if _VAMPIRE == "wsl" else "0")
    verdict = _status("vampire", make, individual, concept)
    assert verdict.status == ("proved" if entailed else "refuted"), (verdict.status, verdict.detail)


@pytest.mark.skipif(not _eprover_ready(), reason="no eprover reachable (PATH, WSL, $UFK_EPROVER_CMD)")
@pytest.mark.parametrize("name, make, individual, concept, entailed", CASES, ids=CASE_IDS)
def test_the_e_route_answers_a_punned_knowledge_base_as_derived(
        name, make, individual, concept, entailed):
    verdict = _status("eprover", make, individual, concept)
    assert verdict.status == ("proved" if entailed else "refuted"), (verdict.status, verdict.detail)


@pytest.mark.parametrize("name, make, individual, concept, entailed", CASES, ids=CASE_IDS)
def test_the_z3_route_answers_a_punned_knowledge_base_as_derived(
        name, make, individual, concept, entailed):
    # RED while the Z3 conversion declares one symbol per NAME: K1 has the name A at
    # two arities and Z3 raises "index out of bounds" (the verdict is an error). K2
    # puns a role and an individual, which have no arity clash, and passes. It is
    # green once the conversion keys its declarations on (kind, name, arity), as the
    # TPTP writers and the model finder already do.
    verdict = _status("z3", make, individual, concept)
    assert verdict.status == ("proved" if entailed else "refuted"), (verdict.status, verdict.detail)


def test_the_model_finder_reports_each_symbol_of_a_punned_name_under_its_own_arity():
    tbox, abox = _k1()
    kb = dl.kb_to_fol(tbox, abox, query=[B])
    verdict = api.prove(kb.instance_goal("A", B), kb.premises, backends=["modelfinder"],
                        timeout=TIMEOUT_MS)
    assert verdict.status == "refuted"
    shown = verdict.countermodel["repr"]
    assert "('A', 1)" in shown and "('A', 2)" in shown and "'A': " in shown


# --------------------------------------------------------------------------- #
# check_kb_names: the check kb_to_fol runs, over boxes rendered apart.
# --------------------------------------------------------------------------- #

def _role_and_data_property():
    """``P`` the data property of one TBox and the object property of an ABox."""
    tbox = dl.TBox().add_data_property_range("P", INT)
    abox = dl.ABox().assert_role("a", "b", "P")
    return tbox, abox


def test_each_box_call_sees_one_kind_and_only_the_whole_sees_the_clash():
    tbox, abox = _role_and_data_property()
    # hand-derived: databox_to_fol sees P only as a data property, abox_to_fol only
    # as an object property, so each is accepted ...
    data_image = dl.databox_to_fol(tbox)
    role_image = dl.abox_to_fol(abox)
    # ... and both write it as the same binary atom, so their conjunction is one
    # predicate P(·, ·) of two kinds
    assert _symbols(data_image)[0] & _symbols(role_image)[0] == {("P", 2)}
    with pytest.raises(UnsupportedDatatypeError, match="'P'"):
        dl.kb_to_fol(tbox, abox)


def test_check_kb_names_runs_that_check_over_the_boxes_given_apart():
    tbox, abox = _role_and_data_property()
    with pytest.raises(UnsupportedDatatypeError) as info:
        dl.check_kb_names(tbox, abox)
    message = str(info.value)
    assert message.startswith("dl.check_kb_names:")
    assert "'P'" in message and "object property" in message and "data property" in message
    assert "OWL 2 DL" in message and "Rename" in message


def test_check_kb_names_sees_a_clash_between_two_tboxes():
    roles = dl.TBox().add_transitive_role("P")
    data = dl.TBox().add_data_property_range("P", INT)
    dl.rbox_to_fol(roles)               # each is accepted on its own
    dl.databox_to_fol(data)
    with pytest.raises(UnsupportedDatatypeError, match="'P'"):
        dl.check_kb_names(roles, data)


def test_check_kb_names_sees_a_class_that_is_a_datatype_in_another_box():
    abox = dl.ABox().assert_concept("a", dl.Atomic("Digit"))
    tbox = dl.TBox().add_datatype_definition("Digit", INT)
    dl.abox_to_fol(abox)
    dl.databox_to_fol(tbox)
    with pytest.raises(UnsupportedDatatypeError) as info:
        dl.check_kb_names(abox, tbox)
    assert "'Digit'" in str(info.value) and "class" in str(info.value) and "datatype" in str(info.value)


def test_check_kb_names_accepts_the_punning_owl_2_dl_allows_across_boxes():
    # a class, an object property and an individual of one name, in three pieces
    classes = dl.TBox().add(A, B)
    roles = dl.TBox().add_transitive_role("A")
    individuals = dl.ABox().assert_concept("A", B)
    assert dl.check_kb_names(classes, roles, individuals) is None


def test_check_kb_names_takes_a_bundle_for_the_boxes_it_was_built_from():
    tbox, abox = _role_and_data_property()
    roles = dl.kb_to_fol(dl.TBox().add_transitive_role("P"), None)
    data = dl.kb_to_fol(tbox, None)
    with pytest.raises(UnsupportedDatatypeError, match="'P'"):
        dl.check_kb_names(roles, data)
    with pytest.raises(UnsupportedDatatypeError, match="'P'"):
        dl.check_kb_names(roles, tbox)           # a bundle and a box mix
    assert dl.check_kb_names(roles) is None


def test_check_kb_names_agrees_with_kb_to_fol_on_the_whole():
    cases = [
        (dl.TBox().add_functional_data_property("P").add(A, dl.Exists("P", B)), dl.ABox(), True),
        (dl.TBox().add(dl.Atomic("Digit"), A).add_datatype_definition("Digit", INT), dl.ABox(), True),
        (dl.TBox().add_data_property_range("d", INT).add(A, dl.Exists("r", B)),
         dl.ABox().assert_role("a", "b", "r"), False),
        (dl.TBox().add(dl.Atomic("OwlData"), A).add_data_property_range("d", INT), dl.ABox(), True),
    ]
    for tbox, abox, refused in cases:
        if refused:
            with pytest.raises(UnsupportedDatatypeError):
                dl.kb_to_fol(tbox, abox)
            with pytest.raises(UnsupportedDatatypeError):
                dl.check_kb_names(tbox, abox)
        else:
            dl.kb_to_fol(tbox, abox)
            assert dl.check_kb_names(tbox, abox) is None


def test_check_kb_names_extends_the_vocabulary_by_the_query_concepts():
    tbox = dl.TBox().add_transitive_role("P")
    assert dl.check_kb_names(tbox) is None
    with pytest.raises(UnsupportedDatatypeError, match="'P'"):
        dl.check_kb_names(tbox, query=[dl.DataExists("P", INT)])


def test_check_kb_names_refuses_a_reserved_name_and_an_unknown_separation():
    tbox = dl.TBox().add(dl.Atomic("OwlData"), A).add_data_property_range("d", INT)
    with pytest.raises(UnsupportedDatatypeError, match="OwlData"):
        dl.check_kb_names(tbox)
    with pytest.raises(UnsupportedDatatypeError, match="separation"):
        dl.check_kb_names(tbox, separation="bogus")


def test_check_kb_names_refuses_a_formula_by_name_and_says_what_to_pass():
    _tbox, abox = _role_and_data_property()
    with pytest.raises(TypeError) as info:
        dl.check_kb_names(dl.abox_to_fol(abox))
    message = str(info.value)
    assert "formula" in message and "TBox" in message and "ABox" in message
    with pytest.raises(TypeError, match="TBox, ABox or KnowledgeBaseFOL"):
        dl.check_kb_names("P")


def test_check_kb_names_refuses_a_bundle_that_does_not_record_its_vocabulary():
    bundle = dl.KnowledgeBaseFOL(formula=dl.abox_to_fol(dl.ABox()), side_axioms=(),
                                 tbox=dl.tbox_to_fol(dl.TBox()), abox=dl.abox_to_fol(dl.ABox()))
    with pytest.raises(ValueError, match="not built by dl.kb_to_fol"):
        dl.check_kb_names(bundle)


def test_check_kb_names_with_nothing_to_check_is_accepted():
    assert dl.check_kb_names() is None
    assert dl.check_kb_names(dl.TBox(), dl.ABox()) is None
