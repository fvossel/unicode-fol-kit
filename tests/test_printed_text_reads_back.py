r"""Every generator that mints a bound variable must print text this kit can read.

The kit's VARIABLE terminal is **one term-valued letter followed by ASCII digits**
(:func:`unicode_logic_kit.fol._identifiers.variable_pattern`) — no underscore, no
prefix. Several translations used to mint names outside that shape, so the kit
printed formulas its own :func:`unicode_logic_kit.api.parse_any` rejected:

====================================  =====================================
generator                             the name it minted before 0.30.0
====================================  =====================================
``fol.frames.unguarded_frame_axiom``  ``_fw0`` / ``_hw0``
``fol.modal_translation``             ``_hw0``
``fol._msfl_nodes``                   ``_msfol_<Sort>_witness``
``fol.qml`` (worlds, Geach, fallback) ``_w0`` / ``_gz0`` / ``_gw`` / ``_world0``
``dl.translate``                      ``x_1`` / ``alice_1``
====================================  =====================================

Each one was a formula that could be computed and printed but not handed back to
``api.prove`` as text — which is exactly how a translation reaches the MCP tools,
the CLI and a DOL/CASL export. The fix was to route every one of them through
:func:`unicode_logic_kit.fol._identifiers.fresh_variables`.

This file is the gate that keeps them fixed, and it is deliberately NOT a list of
the five names above: each case runs the generator, prints the result, parses the
text back and compares the two formulas up to a renaming of bound variables. A
future generator that invents its own naming convention fails here without anyone
remembering to add it to a list of forbidden prefixes.

What is deliberately NOT asserted: a name the CALLER supplied that has no text in
this grammar. Three such limits are left, each a property of the caller's
vocabulary and none of the translation, and each has its own case below:

* a role spelled in lower case. ``concept_to_fol`` on an OWL-style role
  ``hasChild`` prints ``hasChild(x, x0)``, and a predicate must start upper-case
  in this grammar; a predicate has no quoted form, and silently rewriting the
  name would break the correspondence between the DL and the FOL symbol;
* a TPTP variable with an underscore (``VAR_gn_x1``). The VARIABLE terminal is one
  letter and digits, and a variable has no quoted form;
* the name of a built-in datatype (``xsd:integer``): it is a predicate of the data
  image, and a colon is no part of a predicate name.

For all three the route that never goes through text is the one to use, since the
nodes reach ``api.prove``, ``to_z3`` and ``to_tptp`` as ASTs; ``sanitize_names``
is the route to text, because it rewrites a name to one the grammar reads and
keeps the mapping back.

An INDIVIDUAL is not a limit any more. A constant of any name has a text: the
printer writes it bare when the bare word reads back as that constant and in
single quotes otherwise, so ``Alice`` prints ``'Alice'``, the individual ``x0``
prints ``'x0'``, and the literal ``"abc"^^xsd:string`` prints
``'"abc"^^xsd:string'``. Until 0.30.0 these were limits of the property: an
upper-case individual (the OWL case: in OEO 2.13.0 every individual is CamelCase)
printed bare and was re-read as a predicate term in argument position
(``Person(Alice)``, a different formula) or did not parse at all in equality
position (``Alice ≠ Bob``); one spelled like a variable was re-read as a free
variable; and a literal that is no number was no term at all. Every one of them
has a case below that prints the nodes, reads the text back and compares the two
formulas up to a renaming of bound variables. The text of 0.30.0 (every constant
by its bare name, which :func:`unicode_logic_kit.fol._msfl_nodes.key_text` still
writes) is kept in one control case, because that is what shows that the check can
fail on these constants.

Quoting a constant is not a licence to capture, though, and the nodes do not rely
on it: what the translation always owes the caller's individuals is that no
QUANTIFIER binds one. A bound variable steps over every individual's name
(``∃R.{x} ⊑ A`` prints ``∀x0 (R(x0, 'x') → A(x0))``, not the capturing
``∀x (R(x, x) → A(x))`` it printed until 0.30.0, which was a wrong ANSWER and not a
spelling), because in a text with ONE namespace (SMT-LIB, TPTP, Prover9) a
variable and a constant of one spelling still meet.
``test_an_individual_named_like_a_bound_prefix_variable_reads_back_and_is_not_captured``
states both halves; the answers are pinned in ``tests/test_dl_binder_capture.py``.

An individual stands in EQUALITY position (``abox_to_fol`` of an ``assert_same`` or
an ``assert_distinct``, or a ``Nominal``) or in ARGUMENT position (a role
assertion, or a ``HasValue`` image), and each has its own case. The domain and
range images mention no individual at all and read back whatever the vocabulary;
that contrast is asserted too, because it keeps the three limits above precise
rather than a blanket "OWL names do not read back".
"""

import pytest

from unicode_logic_kit import MSFLParser, api
from unicode_logic_kit.atp.tstp_check import _formula_alpha_equal
from unicode_logic_kit.comorphism import DEFAULT_REGISTRY
from unicode_logic_kit.fol._identifiers import variable_names, variable_pattern
from unicode_logic_kit.fol._msfl_nodes import key_text, nonempty_sort_axioms
from unicode_logic_kit.fol.frames import unguarded_frame_axiom
from unicode_logic_kit.fol.modal_translation import frame_axioms, standard_translation
from unicode_logic_kit.fol.nodes import (
    Always, Atom, Box, Constant, Diamond, Eventually, Implies, Knows, Next,
    Obligatory, Permitted, Quantifier, Variable,
)
from unicode_logic_kit.fol.qml import (
    qml_axioms, qml_translate, qml_validity_formula,
)
import re

import unicode_logic_kit.dl as dl

MODAL = MSFLParser(modal=True)
SORTED = MSFLParser(many_sorted=True)
FOLP = MSFLParser()


# --------------------------------------------------------------------------- #
# The property, once.
# --------------------------------------------------------------------------- #

def _reads_back(node, text=None):
    """``(parsed_ok, alpha_equal, text, result)`` for the text ``node`` prints as,
    or for ``text`` when a caller names the text to read instead (the control case
    reads the text of 0.30.0)."""
    if text is None:
        text = node.to_unicode_str()
    result = api.parse_any(text)
    if not result.ok:
        return False, False, text, result
    return True, _formula_alpha_equal(node, result.formula), text, result


def assert_reads_back(node, what, text=None):
    ok, same, text, result = _reads_back(node, text)
    assert ok, f"{what}: the kit printed text it cannot parse: {text!r} ({result.errors})"
    assert same, f"{what}: the text parsed, but as a DIFFERENT formula: {text!r}"


def names_of(node, class_name):
    """The names of the nodes of one class (``"Constant"``, ``"Variable"``,
    ``"PredicateTerm"``) in a formula, as a set."""
    return {t.name for t in node.walk() if type(t).__name__ == class_name}


def assert_every_bound_name_is_legal(node, what):
    """Separately from parsing: every variable name matches the terminal.

    Parsing can succeed for the wrong reason — an illegal variable name may lex
    as something else entirely (a constant, a predicate) and give a formula that
    is still alpha-equal by accident of the comparison. This is the direct check.
    """
    pattern = re.compile(variable_pattern())
    for name in variable_names(node):
        assert pattern.fullmatch(name), f"{what}: {name!r} is no VARIABLE of this kit"


def test_the_two_checks_really_reject_the_names_this_file_exists_for():
    """The control: both helpers above must FAIL on the old shapes.

    Without this, a helper that silently passed everything would make every
    test below green and the gate worthless. Each node here is hand-built in
    exactly the shape the generator named in the module docstring used to
    produce, and each must be rejected — once by the parser, once by the
    terminal check.
    """
    w = Variable("_hw0")
    frame_axiom = Quantifier("∀", w, Atom("R", (w, w)))                 # ∀_hw0 R(_hw0, _hw0)
    witness = Variable("_msfol_Human_witness")
    nonempty = Quantifier("∃", witness, Atom("Human", (witness,)))
    restriction = Variable("x_1")
    dl_shape = Quantifier("∃", restriction,                             # ∃x_1 (R(x, x_1) ∧ …)
                          Atom("R", (Variable("x"), restriction)))
    for node, shape in ((frame_axiom, "_hw0"), (nonempty, "_msfol_Human_witness"),
                        (dl_shape, "x_1")):
        assert not api.parse_any(node.to_unicode_str()).ok, shape
        with pytest.raises(AssertionError):
            assert_reads_back(node, shape)
        with pytest.raises(AssertionError):
            assert_every_bound_name_is_legal(node, shape)
    # and a legal one passes both, so the helpers are not simply always failing
    legal = Quantifier("∀", Variable("v0"), Atom("R", (Variable("v0"), Variable("v0"))))
    assert_reads_back(legal, "control")
    assert_every_bound_name_is_legal(legal, "control")


# --------------------------------------------------------------------------- #
# The generators.
# --------------------------------------------------------------------------- #

_FRAME_CONDITIONS = ["refl", "trans", "sym", "serial", "eucl", "dense",
                     "directed", "connected", "functional", "shift_refl"]


@pytest.mark.parametrize("condition", _FRAME_CONDITIONS)
def test_an_unguarded_frame_axiom_reads_back(condition):
    axiom = unguarded_frame_axiom(condition, "R")
    assert_reads_back(axiom, f"unguarded_frame_axiom({condition!r})")
    assert_every_bound_name_is_legal(axiom, f"unguarded_frame_axiom({condition!r})")


def test_an_illegal_prefix_for_a_frame_axiom_is_refused_by_name():
    # The guard that keeps the shape: the prefix has to be a legal VARIABLE on
    # its own, because prefix + digits is what the axiom prints.
    with pytest.raises(ValueError, match="not a legal variable name"):
        unguarded_frame_axiom("refl", "R", prefix="_fw")


_MODAL_FORMULAS = [
    ("alethic", "□(P) → ◇(P)"),
    ("temporal", "Ⓖ(P) → P"),
    ("next", "Ⓝ(P) → Ⓖ(P)"),
    ("deontic", "Ⓞ(P) → Ⓟ(P)"),
    ("epistemic", "K_alice(P) → P"),
    ("mixed", "□(Ⓖ(P)) → Ⓞ(K_alice(P))"),
]


@pytest.mark.parametrize("name, source", _MODAL_FORMULAS)
def test_the_frame_axioms_of_a_modal_formula_read_back(name, source):
    formula = MODAL.parse(source)
    for axiom in frame_axioms(formula, "S4"):
        assert_reads_back(axiom, f"frame_axioms({name})")
        assert_every_bound_name_is_legal(axiom, f"frame_axioms({name})")


@pytest.mark.parametrize("name, source", _MODAL_FORMULAS)
def test_the_standard_translation_reads_back(name, source):
    image = standard_translation(MODAL.parse(source))
    assert_reads_back(image, f"standard_translation({name})")
    assert_every_bound_name_is_legal(image, f"standard_translation({name})")


_SORTED_FORMULAS = [
    "(∀x:Human M(x)) → ∃x:Human M(x)",
    "∀x0:Human (∃x1:Dog R(x0, x1))",
    "Human(alice:Human) ∧ ∀y:Dog D(y)",
]


@pytest.mark.parametrize("source", _SORTED_FORMULAS)
def test_the_non_emptiness_axioms_read_back(source):
    formula = SORTED.parse(source)
    axioms = nonempty_sort_axioms(formula)
    assert axioms, source
    for axiom in axioms:
        assert_reads_back(axiom, f"nonempty_sort_axioms({source!r})")
        assert_every_bound_name_is_legal(axiom, f"nonempty_sort_axioms({source!r})")


def test_a_non_emptiness_witness_avoids_the_names_the_input_uses():
    # Not a parsing question: the axioms are closed, so a clash could capture
    # nothing — but printed NEXT TO the sentences they are asserted alongside
    # they have to be readable as what they are, and reusing a bound name of the
    # input would read as if they talked about it.
    formula = SORTED.parse("∀x0:Human (∃x1:Dog R(x0, x1))")
    minted = set()
    for axiom in nonempty_sort_axioms(formula):
        minted |= variable_names(axiom)
    assert minted and not (minted & variable_names(formula))


_QML_MODES = ["constant", "varying", "increasing", "possibilist"]
_QML_FRAMES = ["K", "T", "S4", "S5", "KD45", "G(1,1,1,1)", "G(2,1,1,1)"]


@pytest.mark.parametrize("frame", _QML_FRAMES)
def test_a_qml_validity_formula_reads_back(frame):
    # One formula, every frame: the Geach frames are the ones that pull in
    # _geach_axiom's own bound worlds on top of the translation's.
    x = Variable("x")
    formula = Quantifier("∀", x, Implies(Box(Atom("A", [x])), Atom("A", [x])))
    node = qml_validity_formula(formula, mode="constant", frame=frame)
    assert_reads_back(node, f"qml_validity_formula(frame={frame!r})")
    assert_every_bound_name_is_legal(node, f"qml_validity_formula(frame={frame!r})")


@pytest.mark.parametrize("mode", _QML_MODES)
@pytest.mark.parametrize("name, source", _MODAL_FORMULAS)
def test_a_qml_translation_and_its_axioms_read_back(mode, name, source):
    formula = MODAL.parse(source)
    image = qml_translate(formula, mode=mode)
    assert_reads_back(image, f"qml_translate({name}, {mode})")
    assert_every_bound_name_is_legal(image, f"qml_translate({name}, {mode})")
    for axiom in qml_axioms(formula=formula, mode=mode):
        assert_reads_back(axiom, f"qml_axioms({name}, {mode})")
        assert_every_bound_name_is_legal(axiom, f"qml_axioms({name}, {mode})")


def test_a_qml_world_variable_steps_over_an_object_variable_of_the_same_name():
    # 'w0' is a legal OBJECT variable, and it is the name the world minter would
    # otherwise take first; taking it would let the object quantifier capture the
    # box's world. The minter is seeded with the formula's own names.
    w0 = Variable("w0")
    formula = Quantifier("∀", w0, Implies(Box(Atom("A", [w0])), Atom("A", [w0])))
    image = qml_translate(formula, mode="constant")
    assert_reads_back(image, "qml_translate(object variable named w0)")
    assert {"w0", "w1"} <= variable_names(image)


_CONCEPTS = [
    ("exists", dl.Exists("R", dl.Atomic("D"))),
    ("forall", dl.ForAll("R", dl.Atomic("D"))),
    ("nested", dl.Exists("R", dl.ForAll("S", dl.Atomic("A")))),
    ("siblings", dl.And(dl.Exists("R", dl.Atomic("A")), dl.Exists("R", dl.Atomic("B")))),
    ("atleast", dl.AtLeast(2, "R", dl.Atomic("A"))),
    ("atmost", dl.AtMost(1, "R", dl.Top())),
    ("nominal", dl.Exists("R", dl.And(dl.Nominal("alice"), dl.Atomic("A")))),
    # A value restriction mints NO variable of its own (its image is the ground
    # atom R(x, alice)), which is exactly why it belongs here: the property this
    # file holds is about what the GENERATOR prints, and a generator that prints
    # a constant has to print one the parser reads. A lower-case individual, which
    # prints bare; the individuals that print in quotes have their own cases
    # further down.
    ("hasvalue", dl.HasValue("R", "alice")),
    ("hasvalue-nested", dl.Exists("S", dl.And(dl.Atomic("A"),
                                              dl.HasValue("R", "alice")))),
]


@pytest.mark.parametrize("name, concept", _CONCEPTS)
def test_a_concept_translation_reads_back(name, concept):
    image = dl.concept_to_fol(concept, "x")
    assert_reads_back(image, f"concept_to_fol({name})")
    assert_every_bound_name_is_legal(image, f"concept_to_fol({name})")


@pytest.mark.parametrize("name, concept", _CONCEPTS)
def test_a_subsumption_translation_reads_back(name, concept):
    image = dl.subsumption_to_fol(concept, dl.Atomic("C"), "x")
    assert_reads_back(image, f"subsumption_to_fol({name})")
    assert_every_bound_name_is_legal(image, f"subsumption_to_fol({name})")


def test_an_abox_translation_reads_back():
    abox = (dl.ABox()
            .assert_concept("alice", dl.Exists("R", dl.Atomic("D")))
            .assert_role("alice", "bob", "R")
            .assert_distinct("alice", "bob"))
    image = dl.abox_to_fol(abox)
    assert_reads_back(image, "abox_to_fol")
    assert_every_bound_name_is_legal(image, "abox_to_fol")


def test_a_knowledge_base_translation_reads_back():
    tbox = dl.TBox().add(dl.Atomic("A"), dl.Exists("R", dl.Atomic("B")))
    abox = dl.ABox().assert_concept("alice", dl.Atomic("A"))
    kb = dl.kb_to_fol(tbox, abox)
    assert_reads_back(kb.formula, "kb_to_fol().formula")
    assert_every_bound_name_is_legal(kb.formula, "kb_to_fol().formula")
    for axiom in kb.axioms:
        assert_reads_back(axiom, "kb_to_fol().axioms")


@pytest.mark.parametrize("name, build", [
    ("nothing at all", lambda: dl.kb_to_fol()),
    ("an empty TBox and ABox", lambda: dl.kb_to_fol(dl.TBox(), dl.ABox())),
    # The case that was broken until 0.30.0 and that nothing here exercised: a
    # knowledge base whose only content is a role box has NO concept inclusions
    # and NO assertions, so `formula` is the "no constraint" tautology and the
    # content is all in `axioms`. It printed `_ = _`, which api.parse_any
    # rejects outright. 150 of the 3636 OEO axioms this kit accepts are exactly
    # this shape.
    ("a role box and nothing else",
     lambda: dl.kb_to_fol(dl.TBox().add_role_inclusion("R", "S").add_transitive_role("S"))),
], ids=["empty", "empty-boxes", "rbox-only"])
def test_the_no_constraint_tautology_reads_back(name, build):
    kb = build()
    for part, what in ((kb.formula, "formula"), (kb.tbox, "tbox"), (kb.abox, "abox")):
        assert_reads_back(part, f"kb_to_fol({name}).{what}")
    for axiom in kb.axioms:
        assert_reads_back(axiom, f"kb_to_fol({name}).axioms")


def _full_role_box():
    """A TBox carrying ONE axiom of every role-box kind the kit has."""
    return (dl.TBox()
            .add_role_inclusion("R", "S")
            .add_role_inclusion("A1", dl.InverseRole("A2"))
            .add_transitive_role("S")
            .add_disjoint_roles("D1", "D2")
            .add_asymmetric_role("Asym")
            .add_irreflexive_role("Irr")
            .add_functional_role("Func")
            .add_inverse_roles("P1", "Q1")
            .add_symmetric_role("Sym")
            .add_reflexive_role("Refl")
            .add_inverse_functional_role("InvFunc")
            .add_role_chain(("C1", "C2"), "C3")
            .add_role_chain(("E1", "E2", "E3", "E4"), "E5"))


def test_every_role_box_axiom_image_reads_back():
    # One case per generator, as the 0.30.0 property requires: everything the
    # kit PRINTS must read back, and the re-parse must be the same formula up
    # to bound-variable renaming. The two- and three-variable images bind only
    # x, y, z; a chain longer than three mints the rest through
    # fol._identifiers.fresh_variables, which is the only reason a generated
    # name is involved here at all.
    kb = dl.kb_to_fol(_full_role_box())
    assert len(kb.side_axioms) == 13
    for side in kb.side_axioms:
        assert_reads_back(side.formula, f"kb_to_fol(role box).{side.kind}")
        assert_every_bound_name_is_legal(side.formula,
                                         f"kb_to_fol(role box).{side.kind}")
    # the conjoined view too -- rbox_to_fol is a public entry point of its own
    whole = dl.rbox_to_fol(_full_role_box())
    assert_reads_back(whole, "rbox_to_fol(role box)")
    assert_every_bound_name_is_legal(whole, "rbox_to_fol(role box)")


def test_an_upper_case_individual_reads_back_in_quotes():
    # The kit's CONSTANT/NAME terminals are lower-case, so the bare word `Alice`
    # is no constant of this grammar -- and it is the OWL case: every individual
    # in a real ontology (OEO 2.13.0: all of them) is CamelCase. The printer
    # writes the constant in single quotes, `Person('Alice')`, and the quoted
    # name is the constant of exactly that name, so the individual keeps the
    # name the ontology gives it and the text reads back as the formula it was.
    abox = dl.ABox().assert_concept("Alice", dl.Atomic("Person"))
    image = dl.abox_to_fol(abox)
    assert_every_bound_name_is_legal(image, "abox_to_fol(upper-case individual)")
    assert image.to_unicode_str() == "Person('Alice')"
    assert_reads_back(image, "abox_to_fol(upper-case individual)")
    parsed = api.parse_any(image.to_unicode_str())
    assert names_of(parsed.formula, "Constant") == {"Alice"}
    assert names_of(parsed.formula, "PredicateTerm") == set()      # not a predicate term
    assert names_of(image, "Constant") == {"Alice"}
    # A distinctness assertion over such names reads back too ...
    distinct = dl.abox_to_fol(dl.ABox().assert_distinct("Alice", "Bob"))
    assert distinct.to_unicode_str() == "'Alice' ≠ 'Bob'"
    assert_reads_back(distinct, "abox_to_fol(upper-case distinctness)")
    # ... and the text says what the nodes say: two names may denote one element,
    # so the assertion is not valid, whichever way it reaches the prover.
    assert api.prove(distinct, [], timeout=10000).status == "refuted"
    assert api.prove(api.parse_any(distinct.to_unicode_str()).formula, [],
                     timeout=10000).status == "refuted"
    # The lower-case spelling of the same assertions prints bare and reads back.
    lower = dl.abox_to_fol(dl.ABox().assert_concept("alice", dl.Atomic("Person")))
    assert lower.to_unicode_str() == "Person(alice)"
    assert_reads_back(lower, "abox_to_fol(lower-case individual)")
    lower_distinct = dl.abox_to_fol(dl.ABox().assert_distinct("alice", "bob"))
    assert lower_distinct.to_unicode_str() == "alice ≠ bob"
    assert_reads_back(lower_distinct, "abox_to_fol(lower-case distinctness)")


def test_an_upper_case_individual_in_an_equality_reads_back():
    # `assert_same` renders the EQUALITY atom. Before quoting, its text read
    # `Alice` as a predicate and then found `=`, so it did not parse at all;
    # now both sides are constants and the atom is an equation between them.
    image = dl.abox_to_fol(dl.ABox().assert_same("Alice", "Bob"))
    assert_every_bound_name_is_legal(image, "abox_to_fol(assert_same)")
    assert image.to_unicode_str() == "'Alice' = 'Bob'"
    assert_reads_back(image, "abox_to_fol(assert_same)")
    parsed = api.parse_any(image.to_unicode_str())
    assert names_of(parsed.formula, "Constant") == {"Alice", "Bob"}
    # Alice = Bob is SATISFIABLE (two names may denote one element), so it is
    # refutable rather than provable, through the nodes and through the text.
    assert api.prove(image, [], timeout=10000).status == "refuted"
    assert api.prove(parsed.formula, [], timeout=10000).status == "refuted"
    # ... and the lower-case spelling reads back, bare.
    lower = dl.abox_to_fol(dl.ABox().assert_same("alice", "bob"))
    assert lower.to_unicode_str() == "alice = bob"
    assert_reads_back(lower, "abox_to_fol(lower-case sameness)")


def test_an_upper_case_individual_in_an_argument_reads_back():
    # The ARGUMENT position: a role assertion, a HasValue image, a nominal. Every
    # one of the 98 ObjectHasValue fillers in OEO 2.13.0 is CamelCase, so this is
    # the universal case for a real ontology rather than an edge case. Until
    # 0.30.0 this text parsed, as a formula in which the filler was a predicate
    # term -- the dangerous half of the old limit, since nothing refused it.
    image = dl.concept_to_fol(dl.HasValue("HasStateOfMatter", "Liquid"))
    assert_every_bound_name_is_legal(image, "concept_to_fol(HasValue)")
    assert image.to_unicode_str() == "HasStateOfMatter(x, 'Liquid')"
    assert_reads_back(image, "concept_to_fol(HasValue)")
    parsed = api.parse_any(image.to_unicode_str())
    assert names_of(parsed.formula, "Constant") == {"Liquid"}
    assert names_of(parsed.formula, "PredicateTerm") == set()
    # The nominal rewrite of the same axiom, which did not parse at all before:
    # `x0 = Liquid` read `Liquid` as a predicate and then found the `=`.
    rewrite = dl.subsumption_to_fol(
        dl.Atomic("Sirup"), dl.Exists("HasStateOfMatter", dl.Nominal("Liquid")))
    assert rewrite.to_unicode_str() == (
        "∀x (Sirup(x) → ∃x0 (HasStateOfMatter(x, x0) ∧ x0 = 'Liquid'))")
    assert_reads_back(rewrite, "subsumption_to_fol(nominal)")
    # ... and a NEGATIVE role assertion over such names is the same story.
    negative = dl.abox_to_fol(dl.ABox().assert_negative_role(
        "MMRSectorM", "GovRegSectorDivision", "IsDefinedBy"))
    assert negative.to_unicode_str() == "¬IsDefinedBy('MMRSectorM', 'GovRegSectorDivision')"
    assert_reads_back(negative, "abox_to_fol(negative role assertion)")


def test_control_the_text_of_0_30_0_did_not_read_back_as_the_individual():
    # The check above must be able to fail. `key_text` writes every constant by
    # its bare name, which is exactly what the printer wrote until 0.30.0, and
    # for these constants that text is not the formula: `Person(Alice)` parses,
    # with the individual read as a predicate term; the equality, the nominal
    # rewrite and the individual that looks like a variable either do not parse
    # or come back as a free variable. Each text below is written out by hand.
    argument = dl.abox_to_fol(dl.ABox().assert_concept("Alice", dl.Atomic("Person")))
    assert key_text(argument) == "Person(Alice)"
    with pytest.raises(AssertionError, match="DIFFERENT formula"):
        assert_reads_back(argument, "the text of 0.30.0", text=key_text(argument))
    parsed = api.parse_any("Person(Alice)")
    assert names_of(parsed.formula, "PredicateTerm") == {"Alice"}
    assert names_of(parsed.formula, "Constant") == set()
    #
    equality = dl.abox_to_fol(dl.ABox().assert_same("Alice", "Bob"))
    assert key_text(equality) == "Alice = Bob"
    with pytest.raises(AssertionError, match="cannot parse"):
        assert_reads_back(equality, "the text of 0.30.0", text=key_text(equality))
    #
    rewrite = dl.subsumption_to_fol(
        dl.Atomic("Sirup"), dl.Exists("HasStateOfMatter", dl.Nominal("Liquid")))
    assert key_text(rewrite) == "∀x (Sirup(x) → ∃x0 (HasStateOfMatter(x, x0) ∧ x0 = Liquid))"
    assert not api.parse_any(key_text(rewrite)).ok
    #
    like_a_variable = dl.subsumption_to_fol(dl.HasValue("R", "x"), dl.Atomic("A"))
    assert key_text(like_a_variable) == "∀x0 (R(x0, x) → A(x0))"
    with pytest.raises(AssertionError, match="DIFFERENT formula"):
        assert_reads_back(like_a_variable, "the text of 0.30.0",
                          text=key_text(like_a_variable))
    assert names_of(api.parse_any("∀x0 (R(x0, x) → A(x0))").formula, "Variable") == {"x0", "x"}


def test_the_domain_and_range_images_read_back_whatever_the_vocabulary():
    # The contrast that keeps the limits of the module docstring precise: a
    # domain or range image contains NO individual and every role and class name
    # is upper-case, so it reads back cleanly with an OWL-style CamelCase
    # vocabulary throughout. 218 of OEO's axioms are this shape.
    tbox = (dl.TBox()
            .add_role_domain("Covers", dl.Atomic("Study"))
            .add_role_range("HasUnit", dl.Atomic("Unit")))
    for axiom in dl.kb_to_fol(tbox).axioms:
        assert_reads_back(axiom, "rbox_to_fol(domain/range)")
        assert_every_bound_name_is_legal(axiom, "rbox_to_fol(domain/range)")


def test_an_individual_spelled_like_a_variable_reads_back_in_quotes():
    # A Nominal becomes a Constant, and a one-letter-plus-digits name is what the
    # grammar's VARIABLE terminal takes, so the bare text `x0` would be a free
    # variable. The printer writes the constant `'x0'`, which reads back as the
    # individual. What the translation owes the individual besides is not to
    # capture it: the bound variable steps over the nominal's name, so the
    # existential binds x1 and not x0.
    concept = dl.Exists("R", dl.And(dl.Nominal("x0"), dl.Atomic("A")))
    image = dl.concept_to_fol(concept, "x")
    assert_every_bound_name_is_legal(image, "concept_to_fol(individual named x0)")
    assert image.variable == Variable("x1")          # x0 was stepped over
    assert names_of(image.formula, "Constant") == {"x0"}
    assert image.to_unicode_str() == "∃x1 (R(x, x1) ∧ (x1 = 'x0' ∧ A(x1)))"
    assert_reads_back(image, "concept_to_fol(individual named x0)")
    parsed = api.parse_any(image.to_unicode_str())
    assert names_of(parsed.formula, "Constant") == {"x0"}
    assert names_of(parsed.formula, "Variable") == {"x", "x1"}      # x0 is no variable


def test_an_individual_named_like_a_bound_prefix_variable_reads_back_and_is_not_captured():
    # One concrete case, for the GCI  ∃r.{x} ⊑ A  over an individual called x --
    # the name of the GCI's own prefix variable.
    #
    # The prefix variable used to be the fixed letter x, so the image printed
    # `∀x (R(x, x) → A(x))` -- a different sentence, whose NODES conflated the
    # bound variable and the constant (the same Z3 constant), so api.prove called
    # a consistent knowledge base inconsistent. That was a wrong ANSWER, not a
    # spelling, and it is fixed in the nodes AND in the text: the bound variable
    # steps over the individual, `∀x0 (R(x0, 'x') → A(x0))`, derived by hand from
    # "the first free x-name after the individual x". The step stays although the
    # text could now tell `x` from `'x'`: a text with one namespace (SMT-LIB,
    # TPTP, Prover9) cannot, and a binder that left the individual's name alone
    # would capture it there. tests/test_dl_binder_capture.py pins the answers;
    # this pins what the text says. (The role is upper-case: a lower-case one is
    # the limit tested below.)
    image = dl.subsumption_to_fol(dl.HasValue("R", "x"), dl.Atomic("A"))
    assert image.to_unicode_str() == "∀x0 (R(x0, 'x') → A(x0))"
    assert set(variable_names(image)) == {"x0"}               # x is NOT a binder
    assert names_of(image, "Constant") == {"x"}
    #
    # The one-letter CONSTANT prints in quotes, so the text reads back as the
    # formula: the individual x is the constant it was, and no free variable x
    # appears.
    assert_reads_back(image, "subsumption_to_fol(individual named x)")
    parsed = api.parse_any(image.to_unicode_str())
    assert names_of(parsed.formula, "Constant") == {"x"}
    assert names_of(parsed.formula, "Variable") == {"x0"}
    # An upper-case individual (the OWL case) is quoted too, and needs no step:
    # x is a free name here.
    capital = dl.subsumption_to_fol(dl.HasValue("R", "X"), dl.Atomic("A"))
    assert capital.to_unicode_str() == "∀x (R(x, 'X') → A(x))"
    assert_reads_back(capital, "subsumption_to_fol(individual named X)")


def test_a_caller_supplied_lower_case_role_is_the_documented_limit():
    # The minted variable is legal; the ROLE name is the caller's and is printed
    # unchanged, and a predicate must start upper-case in this grammar. So this
    # text does not read back, and that is a property of the vocabulary, not of
    # the translation — see the module docstring.
    image = dl.concept_to_fol(dl.Exists("hasChild", dl.Atomic("Doctor")), "x")
    assert_every_bound_name_is_legal(image, "concept_to_fol(lower-case role)")
    assert not api.parse_any(image.to_unicode_str()).ok
    upper = dl.concept_to_fol(dl.Exists("HasChild", dl.Atomic("Doctor")), "x")
    assert_reads_back(upper, "concept_to_fol(upper-case role)")


# --------------------------------------------------------------------------- #
# Through the registry, which is how the typed surface reaches these.
# --------------------------------------------------------------------------- #

_REGISTRY_CASES = [
    ("modal", "fol", lambda: MODAL.parse("□(Ⓖ(P)) → Ⓞ(P)")),
    ("qml", "fol", lambda: MODAL.parse("□(P) → ◇(P)")),
    ("msfol", "fol", lambda: SORTED.parse("(∀x:Human M(x)) → ∃x:Human M(x)")),
    ("alc", "fol", lambda: dl.Exists("R", dl.ForAll("S", dl.Atomic("A")))),
]


@pytest.mark.parametrize("source, target, build", _REGISTRY_CASES,
                         ids=[f"{s}_to_{t}" for s, t, _ in _REGISTRY_CASES])
def test_a_registry_translation_and_its_axioms_read_back(source, target, build):
    result = DEFAULT_REGISTRY.translate(build(), source, target)
    assert_reads_back(result.result, f"{source} -> {target} image")
    assert_every_bound_name_is_legal(result.result, f"{source} -> {target} image")
    for axiom in result.axioms:
        assert_reads_back(axiom, f"{source} -> {target} axiom")
        assert_every_bound_name_is_legal(axiom, f"{source} -> {target} axiom")


# --------------------------------------------------------------------------- #
# A documented limit: a variable name IMPORTED from a TPTP file. The Hets
# route (OWL to CASL to TPTP) is what makes a real TPTP translation of an
# ontology reachable at all.
# --------------------------------------------------------------------------- #

def test_an_imported_tptp_variable_with_an_underscore_is_a_documented_limit():
    # tptp_input's reader lower-cases a TPTP VAR to get a kit Variable
    # (_TptpTransformer.var: `Variable(str(items[0]).lower())`). That is right
    # for TPTP's own `X`/`X1`, but the kit's VARIABLE terminal is ONE
    # term-valued letter followed by ASCII digits, so a TPTP variable carrying
    # an underscore -- which is legal TPTP, and which Hets' OWL->CASL->TPTP
    # output uses universally (`VAR_gn_x1`) -- becomes a kit variable the kit's
    # own parser rejects.
    #
    # This is a property of the reader, not of the translations in this file:
    # measured identical before 0.30.0, where `parse_tptp` already produced
    # `Variable('var_gn_x1')`. It is documented rather than fixed because
    # renaming an imported bound variable would change the AST of every TPTP
    # import, and the ASTs are exactly what `atp.tstp_check` and the TPTP
    # round-trip tests compare -- including this release's own guarantee that
    # the LALR and Earley paths produce IDENTICAL formulas for all 4291
    # formulas of a real translation.
    #
    # The route that does not go through text is the one to use, exactly as for
    # the lower-case role above: a TptpFormula's `.formula` reaches
    # api.prove / to_z3 / to_tptp as an AST, where a bound variable's spelling
    # is irrelevant. A variable has no quoted form (only a constant has), so
    # nothing in the text can keep the name.
    # Imported where it is used, as the other readers of TPTP below are.
    from unicode_logic_kit.fol.tptp_input import parse_tptp

    formulas = parse_tptp("fof(a, axiom, ! [VAR_gn_x1] : pred_p(VAR_gn_x1)).")
    image = formulas[0].formula
    assert image.variable == Variable("var_gn_x1")
    text = image.to_unicode_str()
    assert text == "∀var_gn_x1 Pred_p(var_gn_x1)"
    assert not api.parse_any(text).ok            # the TEXT is not legal
    # ... and the direct check names the offending variable, so this limit
    # cannot be mistaken for "the parse happened to succeed".
    with pytest.raises(AssertionError, match="is no VARIABLE of this kit"):
        assert_every_bound_name_is_legal(image, "parse_tptp(VAR_gn_x1)")
    # The AST route is unaffected: the same formula is a non-theorem Z3 can
    # answer about, through the nodes rather than through text.
    assert api.prove(image, [], timeout=10000).status == "refuted"
    # TPTP's own variable spellings DO read back, so this is a limit of
    # underscored names, not of the importer.
    for source in ("fof(a, axiom, ! [X] : p1(X)).",
                   "fof(a, axiom, ? [X1] : p1(X1)).",
                   "fof(a, axiom, ! [X] : (p1(X) => q1(X)))."):
        node = parse_tptp(source)[0].formula
        assert_every_bound_name_is_legal(node, f"parse_tptp({source!r})")
        assert_reads_back(node, f"parse_tptp({source!r})")


# --------------------------------------------------------------------------- #
# The data layer. Every generator of the data image gets a case here: the
# data-range translation (reached through the concept images), the data box,
# the sort axioms, a literal's term, and the NUMBER terminal that a negative
# literal needed.
# --------------------------------------------------------------------------- #

from unicode_logic_kit.dl.datatypes import Literal as _Literal          # noqa: E402
from unicode_logic_kit.fol.nodes import Function, Number                 # noqa: E402
from unicode_logic_kit.fol.sanitize import sanitize_names                # noqa: E402

_DIGIT = dl.Datatype("Digit")
_ANY = dl.Datatype("rdfs:Literal")


def _integer(value) -> "_Literal":
    return _Literal(str(value), "xsd:integer")


# User-defined datatype names and numeric literals: the vocabulary that reads
# back. A built-in datatype's name (`xsd:integer`) is not a legal PREDICATE of
# this grammar -- the documented limit tested below.
_DATA_CONCEPTS = [
    ("exists", dl.DataExists("HasAmount", _DIGIT)),
    ("forall", dl.DataForAll("HasAmount", _DIGIT)),
    ("forall-top", dl.DataForAll("HasAmount", _ANY)),
    ("hasvalue", dl.DataHasValue("HasAmount", _integer(4))),
    ("hasvalue-negative", dl.DataHasValue("HasAmount", _integer(-3))),
    ("hasvalue-decimal", dl.DataHasValue("HasAmount", _Literal("-1.5", "xsd:decimal"))),
    ("atleast", dl.DataAtLeast(2, "HasAmount", dl.DataComplementOf(_DIGIT))),
    ("atmost", dl.DataAtMost(1, "HasAmount", dl.DataIntersectionOf((
        _DIGIT, dl.DataComplementOf(dl.DataOneOf((_integer(0),))))))),
    ("enumeration", dl.DataExists("HasAmount", dl.DataOneOf((_integer(1), _integer(-2))))),
    ("union", dl.DataExists("HasAmount", dl.DataUnionOf((
        _DIGIT, dl.DataOneOf((_integer(7),)))))),
    ("nested", dl.Exists("R", dl.And(dl.Atomic("A"), dl.DataExists("HasAmount", _DIGIT)))),
]


@pytest.mark.parametrize("name, concept", _DATA_CONCEPTS)
def test_a_data_concept_translation_reads_back(name, concept):
    image = dl.concept_to_fol(concept, "x")
    assert_reads_back(image, f"concept_to_fol({name})")
    assert_every_bound_name_is_legal(image, f"concept_to_fol({name})")


@pytest.mark.parametrize("name, concept", _DATA_CONCEPTS)
def test_a_data_subsumption_translation_reads_back(name, concept):
    for object_sort in (False, True):
        image = dl.subsumption_to_fol(concept, dl.Atomic("C"), "x", object_sort=object_sort)
        assert_reads_back(image, f"subsumption_to_fol({name}, object_sort={object_sort})")
        assert_every_bound_name_is_legal(image, f"subsumption_to_fol({name})")


def _prefixed_names(node):
    """The PREDICATE names in ``node`` that carry a prefix colon (``xsd:integer``)
    -- the one thing in the data image that is not legal text. A CONSTANT with a
    colon in its name (the literal ``"abc"^^xsd:string``) is not one: it is
    written in quotes and reads back."""
    names = set()
    for part in node.walk():
        name = getattr(part, "predicate", None)
        if isinstance(name, str) and ":" in name:
            names.add(name)
    return names


def assert_reads_back_modulo_datatype_names(node, what):
    """``node`` reads back -- or, when it mentions a built-in datatype by its
    prefixed name (the documented limit tested below), it does NOT read back as
    written but DOES once ``sanitize_names`` has rewritten the names. Either way
    the property holds; the second branch is also asserted to be the limit and
    not something else, by requiring the offending name to be a built-in."""
    prefixed = _prefixed_names(node)
    if not prefixed:
        assert_reads_back(node, what)
        assert_every_bound_name_is_legal(node, what)
        return
    for name in prefixed:
        assert name.split(":")[0] in ("xsd", "rdf", "rdfs", "owl"), (
            f"{what}: {name!r} is not a built-in datatype name")
    assert not api.parse_any(node.to_unicode_str()).ok, what
    sanitized, _mapping = sanitize_names(node)
    assert_reads_back(sanitized, f"sanitize_names({what})")
    assert_every_bound_name_is_legal(sanitized, f"sanitize_names({what})")


def _readable_data_knowledge_base():
    """One axiom of every data kind, in a vocabulary that reads back."""
    tbox = (dl.TBox()
            .add(dl.Atomic("A"), dl.DataHasValue("HasAmount", _integer(-3)))
            .add_data_property_inclusion("HasYear", "HasAmount")
            .add_disjoint_data_properties("HasAmount", "HasName")
            .add_functional_data_property("HasAmount")
            .add_data_property_domain("HasAmount", dl.Atomic("Report"))
            .add_data_property_range("HasAmount", _DIGIT)
            .add_datatype_definition("Digit", dl.DataOneOf((_integer(-1), _integer(2)))))
    abox = (dl.ABox().assert_data("alice", "HasAmount", _integer(400))
            .assert_negative_data("alice", "HasAmount", _integer(-401))
            .assert_concept("alice", dl.DataExists("HasAmount", _DIGIT)))
    return tbox, abox


def test_a_data_knowledge_base_translation_reads_back():
    tbox, abox = _readable_data_knowledge_base()
    kb = dl.kb_to_fol(tbox, abox)
    assert kb.separation == "two-sorted"
    assert_reads_back(kb.formula, "kb_to_fol(data).formula")
    assert_every_bound_name_is_legal(kb.formula, "kb_to_fol(data).formula")
    for part, what in ((kb.tbox, "tbox"), (kb.abox, "abox")):
        assert_reads_back(part, f"kb_to_fol(data).{what}")
    kinds = {side.kind for side in kb.side_axioms}
    # the kinds that matter: the data box, the separation, the typing, the
    # lattice, the literals
    assert {"SubDataPropertyOf", "DisjointDataProperties", "FunctionalDataProperty",
            "DataPropertyDomain", "DataPropertyRange", "DatatypeDefinition",
            "DomainSeparation", "DomainNonEmptiness", "DataPropertyTyping",
            "IndividualTyping", "DatatypeGuard", "LiteralTyping",
            "LiteralDistinctness"} <= kinds
    # Every numeric literal is typed xsd:integer, so the datatype facts (the
    # guard, the literal typing) NAME that built-in datatype: the documented
    # limit, repaired by sanitize_names. Everything else reads back as printed.
    spelled_out = set()
    for side in kb.side_axioms:
        assert_reads_back_modulo_datatype_names(side.formula, f"kb_to_fol(data).{side.kind}")
        if _prefixed_names(side.formula):
            spelled_out.add(side.kind)
    assert spelled_out == {"DatatypeGuard", "LiteralTyping"}


@pytest.mark.parametrize("separation", ["two-sorted", "data-lattice", "none"])
def test_the_data_box_and_the_sort_axioms_read_back_in_every_mode(separation):
    tbox, abox = _readable_data_knowledge_base()
    whole = dl.databox_to_fol(tbox)
    assert_reads_back(whole, "databox_to_fol")
    assert_every_bound_name_is_legal(whole, "databox_to_fol")
    for side in dl.data_sort_axioms(tbox, abox, separation=separation):
        assert_reads_back_modulo_datatype_names(
            side.formula, f"data_sort_axioms({separation}).{side.kind}")


def test_a_data_assertion_reads_back_and_a_literal_is_not_an_individual():
    abox = (dl.ABox().assert_data("alice", "HasAmount", _integer(400))
            .assert_negative_data("alice", "HasAmount", _integer(401)))
    image = dl.abox_to_fol(abox)
    assert image.to_unicode_str() == "HasAmount(alice, 400) ∧ ¬HasAmount(alice, 401)"
    assert_reads_back(image, "abox_to_fol(data)")
    # the literal is a NUMBER in the parsed formula, not a constant or a predicate
    parsed = api.parse_any(image.to_unicode_str())
    assert {t.value for t in parsed.formula.walk() if isinstance(t, Number)} == {400, 401}


# -- the NUMBER terminal: a negative literal prints AND reads back ---------------

@pytest.mark.parametrize("node", [
    Atom("P", (Number(-3),)),
    Atom("P", (Number(-1.5),)),
    Atom("P", (Variable("x"), Number(-3))),
    Atom("<", (Variable("x"), Number(-3))),
    Atom("=", (Number(-3), Number(-3))),
    Atom("P", (Function("-", (Variable("x"), Number(-3))),)),     # x - -3
    Atom("P", (Function("+", (Variable("x"), Number(-3))),)),
    Atom("P", (Function("*", (Number(-2), Variable("x"))),)),
    Atom("P", (Function("-", (Number(5), Number(3))),)),         # 5 - 3: still a subtraction
], ids=["neg-int", "neg-decimal", "neg-arg", "neg-comparison", "neg-equality",
        "minus-neg", "plus-neg", "neg-times", "plain-subtraction"])
def test_a_negative_number_reads_back(node):
    assert_reads_back(node, "Number(-3) in a term")


def test_a_negative_number_is_one_token_and_a_binary_minus_is_still_a_minus():
    # The NUMBER terminal accepts a leading '-'. That must not eat the binary
    # minus: after an operand the only token that can follow is MINUS, so
    # `x-3`, `x -3` and `x - 3` are all the subtraction of 3 from x ...
    subtraction = Function("-", (Variable("x"), Number(3)))
    for text in ("P(x - 3)", "P(x-3)", "P(x -3)", "P(x- 3)"):
        parsed = api.parse_any(text)
        assert parsed.ok, text
        assert [a for a in parsed.formula.walk() if isinstance(a, Function)] == [subtraction], text
    # ... `x - -3` is the subtraction of the NUMBER -3 ...
    parsed = api.parse_any("P(x - -3)")
    assert parsed.ok
    assert [a for a in parsed.formula.walk() if isinstance(a, Function)] == [
        Function("-", (Variable("x"), Number(-3)))]
    # ... and `-3` where a term starts is the number.
    assert api.parse_any("P(-3)").formula == Atom("P", (Number(-3),))
    assert api.parse_any("P(x,-3)").formula == Atom("P", (Variable("x"), Number(-3)))
    assert api.parse_any("x<-3").formula == Atom("<", (Variable("x"), Number(-3)))


def test_a_negative_count_bound_is_still_refused_by_name():
    # `∃≥-2 x P(x)` now LEXES (the bound is a NUMBER with a sign) and the count
    # rule refuses it: a count is a non-negative integer.
    parsed = api.parse_any("∃≥-2 x P(x)")
    assert not parsed.ok
    assert any("non-negative integer" in e["message"] for e in parsed.errors), parsed.errors
    assert api.parse_any("∃≥2 x P(x)").ok


def test_a_negative_number_prints_as_text_the_parser_accepts():
    # The control for the group above: Number(-3) prints as `P(-3)`, which the
    # parser rejected ("Unexpected character '-'") until the NUMBER terminal took
    # a sign. If that text ever stops parsing, the widening has been undone.
    text = Atom("P", (Number(-3),)).to_unicode_str()
    assert text == "P(-3)"
    assert api.parse_any(text).ok


# -- the documented limit of the data layer's printed text ---------------------------

def test_a_built_in_datatype_name_is_a_documented_limit():
    # `xsd:integer` is the name OWL 2 gives the datatype, and a colon is no part
    # of a PREDICATE in this grammar, so a data image over a built-in datatype
    # prints text the kit cannot read back -- exactly as `concept_to_fol` of
    # Atomic('xsd:string') always did. The name is the caller's vocabulary (it IS
    # the datatype's name, so renaming it silently would break the correspondence
    # between the OWL datatype and the FOL symbol), and the image is a node tree
    # that api.prove, to_z3 and to_tptp take as it stands.
    tbox = dl.TBox().add_data_property_range("HasAmount", dl.Datatype("xsd:integer"))
    abox = dl.ABox().assert_data("alice", "HasAmount", _integer(3))
    kb = dl.kb_to_fol(tbox, abox)
    range_axiom = kb.axioms_of_kind("DataPropertyRange")[0]
    assert range_axiom.to_unicode_str() == "∀x ∀v (HasAmount(x, v) → xsd:integer(v))"
    assert_every_bound_name_is_legal(range_axiom, "databox_to_fol(xsd:integer)")
    assert not api.parse_any(range_axiom.to_unicode_str()).ok      # the TEXT is not legal
    # The AST route is unaffected: the same premises prove the consequence.
    goal = dl.datarange_to_fol(dl.Datatype("xsd:integer"), Number(3))
    assert api.prove(goal, list(kb.premises), timeout=10000).status == "proved"
    # The route to TEXT is the kit's own sanitiser, which rewrites the name to a
    # legal token and keeps a mapping back; the result reads back in full.
    sanitized, mapping = sanitize_names(range_axiom)
    assert sanitized.to_unicode_str() == "∀x ∀v (HasAmount(x, v) → Xsdinteger(v))"
    assert_reads_back(sanitized, "sanitize_names(databox image)")
    for side in kb.side_axioms:
        assert_reads_back(sanitize_names(side.formula)[0], f"sanitized {side.kind}")


def test_a_non_numeric_literal_is_a_constant_named_by_its_owl_text():
    # An exact number is a NUMBER and reads back bare. Every other literal is a
    # CONSTANT named by its own OWL text (`"abc"^^xsd:string`), which is no NAME
    # of this grammar. It is written in quotes, and the quoted name is that text:
    # the double quotes, the carets and the colon are all allowed between the
    # single quotes. Until 0.30.0 this text did not parse at all.
    abox = dl.ABox().assert_data("alice", "HasLabel", _Literal("abc"))
    image = dl.abox_to_fol(abox)
    assert image.to_unicode_str() == """HasLabel(alice, '"abc"^^xsd:string')"""
    assert_reads_back(image, "abox_to_fol(string literal)")
    assert names_of(image, "Constant") == {'"abc"^^xsd:string', "alice"}
    assert names_of(api.parse_any(image.to_unicode_str()).formula, "Constant") == {
        '"abc"^^xsd:string', "alice"}
    # The text of 0.30.0 is the control: the same literal by its bare name does
    # not parse.
    assert key_text(image) == 'HasLabel(alice, "abc"^^xsd:string)'
    assert not api.parse_any(key_text(image)).ok
    # A single quote inside the lexical form is written as a backslash and a
    # quote between the single quotes (the OWL text itself does not escape it).
    apostrophe = dl.abox_to_fol(dl.ABox().assert_data("alice", "HasLabel", _Literal("it's")))
    assert apostrophe.to_unicode_str() == """HasLabel(alice, '"it\\'s"^^xsd:string')"""
    assert_reads_back(apostrophe, "abox_to_fol(string literal with an apostrophe)")
    assert names_of(apostrophe, "Constant") == {'"it\'s"^^xsd:string', "alice"}
    # The sanitiser is the other route to text for the ASCII targets: it still
    # gives the name a spelling those targets take, and the result reads back.
    sanitized, _ = sanitize_names(image)
    assert_reads_back(sanitized, "sanitize_names(string literal)")
    # and the AST route gives the same answer as the text
    assert api.prove(image, [], timeout=10000).status == "refuted"
    assert api.prove(api.parse_any(image.to_unicode_str()).formula, [],
                     timeout=10000).status == "refuted"


def test_an_upper_case_individual_in_a_data_assertion_reads_back():
    # The ARGUMENT position for the data layer: `HasNumber('LowElectricityGridVoltageLevel', 400)`.
    # In OEO 2.13.0 every individual is CamelCase, so this is the universal case
    # for a real ontology. Until 0.30.0 the text parsed and read the individual
    # back as a predicate term, which is a different formula.
    abox = dl.ABox().assert_data("LowElectricityGridVoltageLevel", "HasNumber", _integer(400))
    image = dl.abox_to_fol(abox)
    assert image.to_unicode_str() == "HasNumber('LowElectricityGridVoltageLevel', 400)"
    assert_every_bound_name_is_legal(image, "abox_to_fol(upper-case data individual)")
    assert_reads_back(image, "abox_to_fol(upper-case data individual)")
    parsed = api.parse_any(image.to_unicode_str())
    assert names_of(parsed.formula, "Constant") == {"LowElectricityGridVoltageLevel"}
    assert names_of(parsed.formula, "PredicateTerm") == set()
    assert {t.value for t in parsed.formula.walk() if isinstance(t, Number)} == {400}
    assert names_of(image, "Constant") == {"LowElectricityGridVoltageLevel"}
    # The lower-case spelling of the same assertion reads back in full, bare, and so
    # does the contrast case with NO individual at all: a data-property RANGE.
    assert_reads_back(dl.abox_to_fol(dl.ABox().assert_data("alice", "HasNumber", _integer(400))),
                      "abox_to_fol(lower-case data individual)")
    ranged = dl.kb_to_fol(dl.TBox().add_data_property_range("HasNumber", _DIGIT)).axioms_of_kind(
        "DataPropertyRange")[0]
    assert_reads_back(ranged, "databox_to_fol(range, CamelCase vocabulary)")


# --------------------------------------------------------------------------- #
# drt.export: the "no constraint" tautology of an empty box.
# --------------------------------------------------------------------------- #

def _empty_box_drs_cases():
    # Imported where it is used, like the TPTP reader above.
    from unicode_logic_kit.drt.nodes import DRS, Impl, Neg, Or, Pred

    empty = DRS(referents=(), conditions=())
    dog = DRS(referents=("x",), conditions=(Pred("Dog", ("x",)),))
    return [
        # DRS(referents=(), conditions=()) is the case that printed `_ = _`.
        ("an empty DRS", empty, "proved"),
        ("referents and no conditions", DRS(referents=("x",), conditions=()), "proved"),
        ("a negated empty box", DRS(referents=(), conditions=(Neg(empty),)), "refuted"),
        # An implication whose antecedent has no condition conjoins the
        # tautology DIRECTLY into the antecedent: (⊤ → ∃x Dog(x)).
        ("an empty antecedent", DRS(referents=(), conditions=(Impl(empty, dog),)), "refuted"),
        ("a disjunction of empty boxes", DRS(referents=(), conditions=(Or(empty, empty),)), "proved"),
    ]


@pytest.mark.parametrize("name, drs, expected", [(n, d, e) for n, d, e in _empty_box_drs_cases()],
                         ids=[n for n, _, _ in _empty_box_drs_cases()])
def test_an_empty_boxs_translation_reads_back(name, drs, expected):
    from unicode_logic_kit.drt.export import drs_to_fol

    image = drs_to_fol(drs)
    assert_reads_back(image, f"drs_to_fol({name})")
    assert_every_bound_name_is_legal(image, f"drs_to_fol({name})")
    # Semantics, derived by hand from the standard translation: an empty box is
    # the empty conjunction (valid), ∃x of it is valid (the domain is
    # non-empty), ¬ of it is unsatisfiable (so NOT valid), (⊤ → ∃x Dog(x)) is
    # not valid, and ⊤ ∨ ⊤ is valid. The text must say the same as the AST.
    assert api.prove(image).status == expected
    assert api.prove(api.parse_any(image.to_unicode_str()).formula).status == expected


def test_the_old_empty_box_tautology_is_rejected_by_the_parser():
    # The control, as for the shapes at the top of this file: the spelling
    # drs_to_fol used until 0.30.0 (a constant called `_`) is text the kit's
    # own parser rejects, so this gate would have caught it.
    assert not api.parse_any("_ = _").ok


# --------------------------------------------------------------------------- #
# fol.Number: a float prints in positional notation and reads back EXACTLY.
#
# Python's str(1e-07) is '1e-07'. The NUMBER terminal of every reader of this kit
# is -?[0-9]+(\.[0-9]+)? (no exponent), so the unicode reader read 'P(1e-07)' as
# the subtraction 1e minus 07 (a DIFFERENT formula) and 'P(1.5e-05)' did not
# parse at all. Every textual renderer of Number (unicode, LaTeX, TPTP, Prover9)
# now prints the float in plain positional notation, built from the digits of
# repr(value) with decimal arithmetic (never a rounding format), so that
# float(text) == value exactly; an int and an ordinary decimal print as before.
# --------------------------------------------------------------------------- #

# (value, the text it must print as). Every expected text is derived by hand from
# the value, not from the code: the digits of the value, the decimal point where
# the exponent puts it, and a trailing '.0' when no fractional digit is left, so
# that a float still reads back as a float.
_EXPONENT_FLOATS = [
    # 1e-07 = 0.0000001: the single digit 1 sits at the 7th decimal place.
    (1e-07, "0.0000001"),
    # 1.5e-05 = 0.000015: 1.5 shifted five places right of the point.
    (1.5e-05, "0.000015"),
    (-1e-07, "-0.0000001"),
    # The smallest positive double: one digit 5 at the 324th decimal place.
    (5e-324, "0." + "0" * 323 + "5"),
]

# A float with a whole value is stored as the integer it equals (a value has one spelling), so a
# float that Python prints with an exponent at the large end (``1e+16``) is an integer in the node
# and prints as the integer's digits, with no point: the NUMBER terminal reads it back as an int.
# (value, the text it must print as), derived by hand from the value.
_LARGE_FLOATS = [
    # 1e16 is a 1 followed by 16 zeros.
    (1e16, "10000000000000000"),
    # 1.5e22 = 15 followed by 21 zeros (exactly a double: 15 * 10**21, and 3 * 5**22 < 2**53).
    (1.5e22, "15" + "0" * 21),
    # repr(123456789012345678.0) is 1.2345678901234568e+17: seventeen digits
    # 12345678901234568, so 18 integer digits; the double is exactly that integer (a multiple of 16).
    (123456789012345678.0, "123456789012345680"),
    # 10**23 is not a double (5**23 > 2**53): the nearest one is 2980232238769531 * 2**25, which is
    # 10**23 - 8388608 = 99999999999999991611392, and that is the integer the node holds.
    (1e23, "99999999999999991611392"),
]


def _number_atom(value):
    from unicode_logic_kit.fol.nodes import Number

    return Atom("P", [Number(value)])


def _prover9_text(value, text):
    """The double-quoted symbol Prover9 gets for the numeral whose printed text is ``text``: the
    very same text. A numeral is ONE symbol per value and a value has one spelling, so there is
    no second text for it (a float with a whole value is the integer it equals in the node, and
    ``text`` is already that integer's digits)."""
    return '"' + text + '"'


@pytest.mark.parametrize("value, text", _EXPONENT_FLOATS + _LARGE_FLOATS,
                         ids=[repr(v) for v, _ in _EXPONENT_FLOATS + _LARGE_FLOATS])
def test_a_float_in_exponent_form_prints_positional_in_every_text_renderer(value, text):
    atom = _number_atom(value)
    assert atom.to_unicode_str() == f"P({text})"
    assert atom.to_latex() == f"P({text})"
    # Prover9 reads a numeral in double quotes (bare, the "." of a decimal ends the statement),
    # one symbol per VALUE: the text every other renderer prints.
    assert atom.to_prover9() == f"P({_prover9_text(value, text)})"
    assert atom.to_tptp() == f"p({text})"
    # The number itself, in the two renderers that print a Number node alone.
    assert atom.args[0].to_prover9() == _prover9_text(value, text)
    assert atom.args[0].to_tptp() == text


@pytest.mark.parametrize("value, text", _LARGE_FLOATS, ids=[repr(v) for v, _ in _LARGE_FLOATS])
def test_a_float_that_is_a_whole_number_is_stored_as_the_integer_it_equals(value, text):
    from unicode_logic_kit.fol.nodes import Number

    node = Number(value)
    assert isinstance(node.value, int) and node.value == int(text) and node.value == value
    assert node == Number(int(text)) and repr(node) == f"Number(value={text})"


# The smallest positive double has one significant digit, but below the smallest normal double
# (2.2250738585072014e-308) the doubles thin out: ``4e-324`` is the same double, so the text does not
# tell which numeral it was and the readers refuse it (see ``test_decimal_reading_exact.py``).
_READABLE_EXPONENT_FLOATS = [(v, t) for v, t in _EXPONENT_FLOATS if abs(v) >= 2.2250738585072014e-308]


@pytest.mark.parametrize("value, text", _READABLE_EXPONENT_FLOATS,
                         ids=[repr(v) for v, _ in _READABLE_EXPONENT_FLOATS])
def test_the_positional_text_reads_back_as_the_same_float_in_every_reader(value, text):
    from unicode_logic_kit.fol.nodes import Number
    from unicode_logic_kit.fol.prover9_input import parse_prover9
    from unicode_logic_kit.fol.tptp_input import parse_tptp

    assert float(text) == value
    expected = Number(value)

    unicode_back = FOLP.parse(f"P({text})")
    assert unicode_back.args == (expected,)
    assert isinstance(unicode_back.args[0].value, float)       # still a float, not an int
    assert api.parse_any(f"P({text})").formula.args == (expected,)
    assert parse_prover9(f"P({text})").args == (expected,)
    [tptp] = parse_tptp(f"fof(a, axiom, p({text})).\n")
    assert tptp.formula.args == (expected,)


def test_the_text_of_the_smallest_double_is_refused_by_every_reader():
    from unicode_logic_kit.fol.naming import ParsingError
    from unicode_logic_kit.fol.prover9_input import parse_prover9
    from unicode_logic_kit.fol.tptp_input import parse_tptp

    text = "0." + "0" * 323 + "5"
    assert float(text) == float("0." + "0" * 323 + "4") == 5e-324      # one double for two decimals
    for read in (lambda: FOLP.parse(f"P({text})"), lambda: parse_prover9(f"P({text})"),
                 lambda: parse_tptp(f"fof(a, axiom, p({text})).\n")):
        with pytest.raises((ParsingError, ValueError), match="close to zero"):
            read()


@pytest.mark.parametrize("value, text", _LARGE_FLOATS, ids=[repr(v) for v, _ in _LARGE_FLOATS])
def test_the_integer_text_of_a_large_float_reads_back_as_the_same_numeral_in_every_reader(value, text):
    from unicode_logic_kit.fol.nodes import Number
    from unicode_logic_kit.fol.prover9_input import parse_prover9
    from unicode_logic_kit.fol.tptp_input import parse_tptp

    assert int(text) == value
    expected = Number(value)

    unicode_back = FOLP.parse(f"P({text})")
    assert unicode_back.args == (expected,)
    assert isinstance(unicode_back.args[0].value, int)         # the integer the float is
    assert api.parse_any(f"P({text})").formula.args == (expected,)
    assert parse_prover9(f'P("{text}")').args == (expected,)
    [tptp] = parse_tptp(f"fof(a, axiom, p({text})).\n")
    assert tptp.formula.args == (expected,)
    # and the float's own spelling, with the point, is the same numeral too
    assert FOLP.parse(f"P({text}.0)").args == (expected,)


def test_the_old_exponent_text_was_not_the_number_it_printed():
    # The control: this is what the renderers used to print and why it is wrong.
    from unicode_logic_kit.fol.nodes import Function, Number

    assert FOLP.parse("P(1e-07)").args[0] == Function("-", [Constant("1e"), Number(7)])
    assert not api.parse_any("P(1.5e-05)").ok


# Ints and ordinary decimals print exactly as Python's own str() always printed
# them: a repr with no exponent is already positional and is left alone.
_UNCHANGED = [
    (3, "3"), (-3, "-3"), (0, "0"), (2.5, "2.5"), (-2.5, "-2.5"), (0.1, "0.1"),
    (0.0001, "0.0001"), (12345.678, "12345.678"), (10 ** 20, "100000000000000000000"),
]

# A float with a whole value is the integer it equals (``Number(100.0)`` IS ``Number(100)``), so it
# prints as that integer's digits: 100.0 as ``100``, minus zero as ``0`` (it equals zero), and 1e15,
# the largest power of ten Python still prints positionally, as 1 followed by fifteen zeros. Before a
# value had one spelling these printed ``100.0``, ``-0.0`` and ``1000000000000000.0``, a second text
# for the numerals ``100``, ``0`` and ``1000000000000000``.
_WHOLE_FLOATS = [(100.0, "100"), (-0.0, "0"), (1e15, "1000000000000000")]


@pytest.mark.parametrize("value, text", _UNCHANGED + _WHOLE_FLOATS,
                         ids=[repr(v) for v, _ in _UNCHANGED + _WHOLE_FLOATS])
def test_an_int_and_an_ordinary_decimal_print_exactly_as_before(value, text):
    atom = _number_atom(value)
    assert atom.to_unicode_str() == f"P({text})"
    assert atom.to_latex() == f"P({text})"
    # Prover9: every numeral is a double-quoted symbol (bare "-3" is the function - applied to 3,
    # the "." of "2.5" ends the statement, and Mace4 reads a bare integer as a domain element of
    # its own), one per value: the text printed here.
    assert atom.to_prover9() == f"P({_prover9_text(value, text)})"
    assert atom.to_tptp() == f"p({text})"


def test_every_finite_double_prints_a_text_that_reads_back_to_exactly_itself():
    # Exactness is a property of the value, so it is checked on values nobody
    # picked: random 64-bit patterns (every exponent from subnormal to huge) and
    # log-uniform magnitudes. float() of the printed text must be the SAME double
    # (== is exact for floats), and the text must be an instance of the grammar's
    # NUMBER terminal: no exponent, digits, and a point with digits on both sides
    # exactly when the value has a fractional part. A float with a whole value (every
    # double of magnitude 2**53 or more, and the zeros) is the integer it equals in
    # the node, so its text is that integer's digits with no point.
    import random
    import struct

    from unicode_logic_kit.fol.nodes import Number

    with_point = re.compile(r"-?[0-9]+\.[0-9]+")
    rng = random.Random(20261004)
    values = []
    while len(values) < 4000:
        v = struct.unpack("<d", struct.pack("<Q", rng.getrandbits(64)))[0]
        if v == v and v not in (float("inf"), float("-inf")):
            values.append(v)
    values += [rng.choice((-1, 1)) * 10.0 ** rng.uniform(-30, 30) for _ in range(2000)]
    for v in values:
        text = Number(v).to_tptp()
        if v == int(v):
            assert text == str(int(v)), (v, text)
            assert Number(v).value == int(v) and isinstance(Number(v).value, int)
        else:
            assert with_point.fullmatch(text), (v, text)
        assert float(text) == v, (v, text)
        # Prover9 reads the number in double quotes, one symbol per value: the text printed above.
        assert Number(v).to_prover9() == f'"{text}"'
        assert _number_atom(v).to_unicode_str() == f"P({text})"
    # The reader reads back every double whose text has at most 15 significant digits (two different
    # decimals that short are never one double) and refuses, by name, a text with more: two decimals of
    # 16 or 17 digits can be one double, so the text does not tell which numeral it was.
    from unicode_logic_kit.fol.naming import ParsingError

    for v in values[:150] + [0.1, 2.5, 1e-07, 3.14159265358979, 12345.678, -1.5e-05]:
        whole, _, fraction = Number(v).to_tptp().lstrip("-").partition(".")
        significant = len((whole + fraction.rstrip("0")).lstrip("0")) if fraction else 0
        if significant > 15:
            with pytest.raises(ParsingError, match="significant digits"):
                FOLP.parse(_number_atom(v).to_unicode_str())
        else:
            assert FOLP.parse(_number_atom(v).to_unicode_str()).args == (Number(v),), v


@pytest.mark.parametrize("value", [float("inf"), float("-inf"), float("nan")])
def test_a_non_finite_float_is_refused_by_name_not_printed_as_a_word(value):
    # No syntax of the kit has a literal for it, and the word would read back as
    # a CONSTANT called inf/nan: P(inf) is P applied to a constant, not to a number.
    atom = _number_atom(value)
    for render in (atom.to_unicode_str, atom.to_latex, atom.to_prover9, atom.to_tptp):
        with pytest.raises(ValueError, match="has no literal"):
            render()
    assert FOLP.parse("P(inf)").args == (Constant("inf"),)


def test_smtlib_still_reads_back_for_ints_and_exponent_floats():
    # SMT-LIB goes through to_z3 (a Number is a symbol of the uninterpreted sort
    # named by its text) and Z3's own serialiser, which quotes |1e-07| and |3|.
    # Those read back and are pinned here (green before and after the fix; the
    # renderer was not touched). NOT covered: a negative number or a decimal
    # point (-3, 2.5), which Z3's serialiser leaves unquoted so the text is not
    # SMT-LIB at all -- a separate, older limit of atp.z3_input.
    import z3

    from unicode_logic_kit.atp.z3_input import from_z3

    for value in (3, 1e-07, 1.5e-05, 1e16):
        atom = _number_atom(value)
        [assertion] = z3.parse_smt2_string(atom.to_smtlib())
        assert from_z3(assertion) == atom, value
