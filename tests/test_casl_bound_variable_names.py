"""A bound variable and a symbol of the same name, in the CASL and DOL text.

CASL writes a bound variable, a constant (a 0-ary operation) and a predicate as one
identifier, compared exactly, and inside a quantifier the name of its variable is the
variable. ``forall w : Thing . (P(w) => Q(w))`` next to ``ops w : Thing`` therefore says
nothing about a constant ``w``, whatever the formula was: the exporter wrote that text for
``∀w (P(w) → Q(c))`` with ``c = Constant("w")``, and the text reads back as a different
formula. The DOL route through ``qml`` mints its own world variables (``w``, ``v``, ``x``,
``t``, ``w0``, ...) and put a user constant of the same spelling under one of them.

The contract, derived from how the text is read: a bound variable that is spelled like ANY
symbol of the whole specification (a constant, a function, a predicate or a sort of any
axiom or conjecture, the default sort, a symbol the spec sees from outside) is renamed to a
fresh variable name, in its quantifier and in every occurrence it binds; names are compared
exactly; text without a clash is unchanged; and the text reads back, through the kit's own
``parse_casl_spec``, as the formula up to the names of the renamed variables.
"""
import random
import re
from collections import OrderedDict

import pytest

from _bound_names import same_up_to_bound_names
from unicode_fol_kit import api
from unicode_fol_kit.fol.casl_export import formula_to_casl, to_casl_spec
from unicode_fol_kit.fol.casl_import import parse_casl_spec
from unicode_fol_kit.fol.nodes import (
    And, Atom, Box, Constant, Function, Iff, Implies, Not, Or, Quantifier, Variable,
)
from unicode_fol_kit.fol.qml import qml_is_valid, qml_validity_formula
from unicode_fol_kit.hets.dol import (
    DolSpec, sanitize_modal_identifiers, to_dol_library, to_dol_library_from_modal,
)

_FORALL, _EXISTS = "∀", "∃"


def _p(*terms):
    return Atom("P", list(terms))


def _q(*terms):
    return Atom("Q", list(terms))


def _read_axioms(text):
    return parse_casl_spec(text).axioms


def _spec_of(library_text):
    """The one spec of a one-spec DOL library, as text ``parse_casl_spec`` reads."""
    return "\n".join(library_text.split("\n")[3:])


# ---------------------------------------------------------------------------
# The reported capture
# ---------------------------------------------------------------------------

def test_a_bound_variable_spelled_like_a_constant_is_not_that_constant():
    """∀w (P(w) → Q(c)) with c the CONSTANT w.

    Hand-derivation: the spec declares the operation ``w`` (the constant) and the
    predicates ``P`` and ``Q``. In ``forall w : Thing . (P(w) => Q(w))`` both arguments
    are the variable, so the constant must not be written under the binder's name. The
    binder gets another name ``v``, and the text reads back as ∀v (P(v) → Q(w)) with
    ``Q`` applied to the constant."""
    w = Variable("w")
    f = Quantifier(_FORALL, w, Implies(_p(w), _q(Constant("w"))))
    text = to_casl_spec([f], spec_name="T")
    assert "ops w : Thing" in text
    [read] = _read_axioms(text)
    assert isinstance(read, Quantifier) and read.type == _FORALL
    bound = read.variable.name
    assert bound != "w"
    assert read == Quantifier(
        _FORALL, Variable(bound), Implies(_p(Variable(bound)), _q(Constant("w"))))


def test_formula_to_casl_keeps_the_binder_away_from_the_constant_too():
    """The bare text for hand-written CASL has the same capture, and the same repair:
    ``forall v : Thing . (P(v) => Q(w))`` for some variable name ``v`` other than ``w``."""
    w = Variable("w")
    f = Quantifier(_FORALL, w, Implies(_p(w), _q(Constant("w"))))
    text = formula_to_casl(f)
    match = re.fullmatch(r"forall (\w+) : Thing \. \(P\(\1\) => Q\(w\)\)", text)
    assert match, text
    assert match.group(1) != "w"


def test_names_are_compared_exactly_so_a_constant_W_does_not_clash_with_a_variable_w():
    """CASL identifiers are case-sensitive and the kit's reader reads ``w`` and ``W`` as
    two names, so nothing is renamed and the text is exactly what the rules give:
    sorts, the operation ``W``, the predicates alphabetically, the quantifier with its
    body parenthesised."""
    w = Variable("w")
    f = Quantifier(_FORALL, w, Implies(_p(w), _q(Constant("W"))))
    text = to_casl_spec([f], spec_name="T")
    assert text == (
        "spec T =\n"
        "  sorts Thing\n"
        "  ops W : Thing\n"
        "  preds P : Thing;\n"
        "        Q : Thing\n"
        "  . forall w : Thing . (P(w) => Q(W))\n"
        "end")
    assert _read_axioms(text) == (f,)


def test_the_symbols_of_the_whole_spec_count_not_only_those_under_the_binder():
    """The operation ``w`` is declared for the whole spec, in the second axiom. A binder
    ``w`` of the FIRST axiom, which never mentions the constant, would still make every
    bare ``w`` ambiguous between the variable and the declared operation, so it is
    renamed as well: the first axiom reads back as ∀v P(v) and the second is untouched."""
    first = Quantifier(_FORALL, Variable("w"), _p(Variable("w")))
    second = _q(Constant("w"))
    text = to_casl_spec([first, second], spec_name="T")
    one, two = _read_axioms(text)
    assert one.variable.name != "w"
    assert one == Quantifier(_FORALL, one.variable, _p(one.variable))
    assert two == second


def test_conjectures_and_axioms_share_one_set_of_symbols():
    """A constant ``w`` in a CONJECTURE keeps the binder of an AXIOM away from the name."""
    axiom = Quantifier(_EXISTS, Variable("w"), _p(Variable("w")))
    conjecture = _q(Constant("w"))
    spec = parse_casl_spec(to_casl_spec([axiom], conjectures=[conjecture], spec_name="T"))
    [read] = spec.axioms
    assert read.variable.name != "w"
    assert spec.conjectures == (conjecture,)


def test_every_clashing_binder_is_renamed_and_each_occurrence_follows_its_own_binder():
    """∀w (P(w) ∧ ∃w Q(w)) beside the constant w: two binders of one name, one outside the
    other. Both are renamed, and the inner Q is still bound by the INNER one: compared up
    to bound names with the original, an occurrence bound by the wrong binder is a
    different formula (its distance to the binder differs)."""
    f = Quantifier(_FORALL, Variable("w"), And(
        _p(Variable("w")), Quantifier(_EXISTS, Variable("w"), _q(Variable("w")))))
    [read, _] = _read_axioms(to_casl_spec([f, _p(Constant("w"))], spec_name="T"))
    assert same_up_to_bound_names(read, f)
    assert read.variable.name != "w" and read.formula.right.variable.name != "w"


def test_a_new_name_is_fresh_against_the_names_inside_the_scope():
    """∀w ∀w0 (R(w, w0) ∧ Q(c)) with c the constant w. The outer binder must not become
    ``w0``: that would be captured by the inner binder of that name. Neither of the two
    binders may be ``w`` after the rename, and they stay two different variables."""
    r = Atom("R", [Variable("w"), Variable("w0")])
    f = Quantifier(_FORALL, Variable("w"), Quantifier(
        _FORALL, Variable("w0"), And(r, _q(Constant("w")))))
    [read] = _read_axioms(to_casl_spec([f], spec_name="T"))
    outer, inner = read.variable.name, read.formula.variable.name
    assert outer != "w" and outer != inner
    assert same_up_to_bound_names(read, f)


def test_text_without_a_clash_is_unchanged_and_shadowing_still_reads_back():
    """∀x (P(x) ∧ ∃x Q(x)): no symbol is called ``x``. Nothing is renamed; the inner
    binder shadows the outer as in the kit's own reading, and the text reads back as the
    very same formula."""
    f = Quantifier(_FORALL, Variable("x"), And(
        _p(Variable("x")), Quantifier(_EXISTS, Variable("x"), _q(Variable("x")))))
    text = to_casl_spec([f], spec_name="T")
    assert ". forall x : Thing . (P(x) /\\ (exists x : Thing . Q(x)))" in text
    assert _read_axioms(text) == (f,)


@pytest.mark.parametrize("make", [
    # a binder spelled like a predicate
    lambda x: (Quantifier(_FORALL, x, Atom("x", [x])), "predicate x"),
    # a binder spelled like a function
    lambda x: (Quantifier(_FORALL, x, _p(Function("x", [x]))), "function x"),
    # no symbol of the spec is spelled like the binder
    lambda x: (And(Quantifier(_FORALL, x, _p(x)), _p(Constant("c"))), "no clash"),
], ids=["predicate", "function", "none"])
def test_a_binder_spelled_like_any_kind_of_symbol_is_renamed_and_reads_back(make):
    """The name is taken by a predicate or a function of the spec: the binder is renamed
    (the kinds are one namespace in the text); a spec with no such symbol is left alone.
    In every case the text reads back as the formula up to the bound names."""
    x = Variable("x")
    f, label = make(x)
    text = to_casl_spec([f], spec_name="T")
    [read] = _read_axioms(text)
    assert same_up_to_bound_names(read, f), label
    declared = parse_casl_spec(text).signature
    taken = set(declared.predicates) | set(declared.functions) | set(declared.constants)
    bound = {node.variable.name for node in read.walk() if isinstance(node, Quantifier)}
    assert not bound & taken, label
    assert (read == f) == (label == "no clash")


def test_visible_symbols_keep_a_binder_away_from_names_the_spec_does_not_declare():
    """``visible_symbols`` are names the text meets without declaring them (the symbols of
    a spec it extends, of the hand-written CASL a bare formula is embedded in). ∀x P(x)
    with ``x`` visible has a binder that is not ``x``; with a visible name that is not
    the binder's nothing changes."""
    f = Quantifier(_FORALL, Variable("x"), _p(Variable("x")))
    plain = to_casl_spec([f], spec_name="T")
    assert to_casl_spec([f], spec_name="T", visible_symbols=["y"]) == plain
    renamed = to_casl_spec([f], spec_name="T", visible_symbols=["x"])
    [read] = _read_axioms(renamed)
    assert read.variable.name != "x" and same_up_to_bound_names(read, f)
    assert formula_to_casl(f) == "forall x : Thing . P(x)"
    bare = formula_to_casl(f, visible_symbols=["x"])
    match = re.fullmatch(r"forall (\w+) : Thing \. P\(\1\)", bare)
    assert match and match.group(1) != "x"


# ---------------------------------------------------------------------------
# The round trip, on random formulas whose names collide on purpose
# ---------------------------------------------------------------------------

_CONSTANTS = ("c", "w", "x", "y")
_VARIABLES = ("w", "x", "y", "z")
_PREDICATES = {"P": 1, "Q": 2, "x": 1, "R": 0}      # a predicate spelled like a variable
_FUNCTIONS = {"f": 1, "z": 1}                        # a function spelled like a variable


def _term(rng, depth, scope):
    roll = rng.random()
    if scope and roll < 0.5:
        return Variable(rng.choice(scope))
    if depth > 0 and roll < 0.7:
        return Function(rng.choice(sorted(_FUNCTIONS)), [_term(rng, depth - 1, scope)])
    return Constant(rng.choice(_CONSTANTS))


def _formula(rng, depth, scope):
    roll = rng.random()
    if depth == 0 or roll < 0.3:
        if rng.random() < 0.2:
            return Atom("=", [_term(rng, 1, scope), _term(rng, 1, scope)])
        name = rng.choice(sorted(_PREDICATES))
        return Atom(name, [_term(rng, 1, scope) for _ in range(_PREDICATES[name])])
    if roll < 0.4:
        return Not(_formula(rng, depth - 1, scope))
    if roll < 0.7:
        connective = rng.choice([And, Or, Implies, Iff])
        return connective(_formula(rng, depth - 1, scope), _formula(rng, depth - 1, scope))
    name = rng.choice(_VARIABLES)
    return Quantifier(rng.choice([_FORALL, _EXISTS]), Variable(name),
                      _formula(rng, depth - 1, scope + [name]))


def test_random_formulas_read_back_as_themselves_up_to_the_renamed_binders():
    """2000 closed formulas over a pool of colliding names: constants c, w, x, y,
    variables w, x, y, z, a predicate x beside the variable x, a function z beside the
    variable z. No name is used as a constant and as a function, no predicate at two
    arities and there is one sort, so the exporter accepts every one of them; its text
    reads back through ``parse_casl_spec`` as the formula up to the names of its bound
    variables, and as the very same formula when no binder was spelled like a symbol of
    the spec. The text never binds a variable that is spelled like a declared operation,
    predicate or sort."""
    rng = random.Random(20260)
    exact = renamed = 0
    for _ in range(2000):
        f = _formula(rng, 4, [])
        text = to_casl_spec([f], spec_name="T")
        spec = parse_casl_spec(text)
        [read] = spec.axioms
        assert same_up_to_bound_names(read, f), (f.to_unicode_str(), text)
        declared = (set(spec.signature.predicates) | set(spec.signature.functions)
                    | set(spec.signature.constants) | set(spec.signature.sorts))
        bound = {node.variable.name for node in read.walk() if isinstance(node, Quantifier)}
        assert not bound & declared, (f.to_unicode_str(), text)
        symbols = {n.name for n in f.walk() if isinstance(n, (Constant, Function))}
        symbols |= {n.predicate for n in f.walk() if isinstance(n, Atom) and n.predicate != "="}
        if {n.variable.name for n in f.walk() if isinstance(n, Quantifier)} & symbols:
            renamed += 1
        else:
            exact += 1
            assert read == f, (f.to_unicode_str(), text)
    # the pool does produce both kinds of formula, so neither branch is vacuous
    assert exact > 200 and renamed > 200


# ---------------------------------------------------------------------------
# The DOL library
# ---------------------------------------------------------------------------

def _modal_conjecture(text):
    return parse_casl_spec(_spec_of(text)).conjectures[0]


@pytest.mark.parametrize("name", ["w", "v", "x", "t", "u", "a", "w0"])
def test_a_user_constant_spelled_like_a_world_variable_does_not_change_the_query(name):
    """□R(c) → R(c) under T, c the constant ``name`` (the world variables qml mints are
    ``w``, ``v``, ``x``, ``t``, ``w0``, ...). The library text reads back as the very
    translation qml hands over, up to the bound names, and Z3 proves it exactly when
    ``qml_is_valid`` says the modal formula is valid (it is: the T-schema)."""
    c = Constant(name)
    f = Implies(Box(Atom("R", [c])), Atom("R", [c]))
    library = to_dol_library_from_modal(f, frame="T", spec_name="S", library_name="L")
    read = _modal_conjecture(library)
    expected = sanitize_modal_identifiers(qml_validity_formula(f, frame="T"))
    assert same_up_to_bound_names(read, expected)
    assert qml_is_valid(f, frame="T") is True
    assert api.prove(read, [], backends=["z3"], timeout=8000).status == "proved"


@pytest.mark.parametrize("name", ["w", "x", "w0"])
def test_a_user_constant_spelled_like_a_world_variable_keeps_an_invalid_query_invalid(name):
    """R(c) → □R(c) is invalid under T (a successor world may differ in R): the text of
    the library is refuted, as ``qml_is_valid`` says."""
    c = Constant(name)
    f = Implies(Atom("R", [c]), Box(Atom("R", [c])))
    library = to_dol_library_from_modal(f, frame="T", spec_name="S", library_name="L")
    assert qml_is_valid(f, frame="T") is False
    assert api.prove(_modal_conjecture(library), [], backends=["z3"],
                     timeout=8000).status == "refuted"


def test_a_spec_that_extends_another_keeps_its_binders_away_from_the_symbols_it_inherits():
    """Spec A declares the constant ``c``; spec B extends A with ``∀c Q(c)`` and never
    mentions the constant itself. B sees ``c`` through ``then``, so its binder is renamed
    (also through a chain A <- B <- C); a spec that extends nothing keeps its binder."""
    bound = Quantifier(_FORALL, Variable("c"), _q(Variable("c")))
    specs = OrderedDict()
    specs["A"] = DolSpec(axioms=[_p(Constant("c"))])
    specs["B"] = DolSpec(axioms=[bound], extends="A")
    specs["C"] = DolSpec(axioms=[bound], extends="B")
    specs["D"] = DolSpec(axioms=[bound])
    text = to_dol_library("Lib", specs)
    blocks = {name: block for name, block in
              ((m.group(1), m.group(0)) for m in re.finditer(r"spec (\w+) =.*?\nend", text, re.S))}
    for name in "BC":
        match = re.search(r"forall (\w+) : Thing \. Q\(\1\)", blocks[name])
        assert match and match.group(1) != "c", (name, blocks[name])
    assert "forall c : Thing . Q(c)" in blocks["D"]


def test_the_names_the_sanitiser_mints_are_fresh_against_every_kind_of_symbol():
    """A world variable ``_w0`` that the sanitiser has to rename (a leading underscore is no
    CASL identifier) and a user constant ``w0``: the variable is given a spelling that
    is neither, so it does not meet the constant even before the exporter looks at
    the text."""
    formula = Quantifier(_FORALL, Variable("_w0"), _p(Variable("_w0"), Constant("w0")))
    clean = sanitize_modal_identifiers(formula)
    assert clean.variable.name not in ("_w0", "w0")
    assert clean == Quantifier(_FORALL, clean.variable, _p(clean.variable, Constant("w0")))
