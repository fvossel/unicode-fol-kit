"""The TPTP reader never reads two TPTP variables as one.

A TPTP variable is case-sensitive; the kit variable the reader builds is its
LOWER-CASED form. So ``Xa`` and ``XA`` are two TPTP variables that become the one
kit variable ``xa``. Until 0.30.0 ``![Xa, XA]: p(Xa, XA)`` was read, with no
word, as ``∀xa ∀xa P(xa, xa)`` -- a different formula.

The semantic clause, stated once (it is TPTP's own scoping rule): an occurrence
of a variable is bound by the NEAREST enclosing quantifier that binds that exact
spelling, and is free if there is none; a kit variable is a NAME, bound by the
nearest enclosing quantifier of that name. The reading is faithful iff, for every
occurrence, those two resolve to the same binder, and no two spellings of one
lower-cased name occur free in one formula. The reader refuses a formula that
breaks it, naming both variables, and reads every other formula as it always did.

Hand-derived cases first, then a seeded random test whose oracle is the clause
above applied to the GENERATOR's own tree -- it shares no code with the reader.
"""

import random

import pytest

from unicode_fol_kit.fol.nodes import And, Atom, Constant, Not, Or, Quantifier, Variable
from unicode_fol_kit.fol.tptp_input import TptpParsingError, parse_tptp, parse_tptp_formula


def _xa(name="xa"):
    return Variable(name)


def _p(*names):
    return Atom("P", [Variable(n) for n in names])


# --------------------------------------------------------------------------- #
# Refused: the kit reading is a DIFFERENT formula, and both variables are named.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("text, names", [
    # Two binders of one list. TPTP: Xa and XA are two variables. Kit: the second
    # binder (XA -> xa) is nested inside the first, so the occurrence of Xa is
    # captured by it: ∀xa ∀xa P(xa, xa) has ONE variable where TPTP has two.
    ("![Xa, XA]: p(Xa, XA)", ("Xa", "XA")),
    ("?[Xa, XA]: p(Xa, XA)", ("Xa", "XA")),
    # Nested quantifiers: the occurrence of Xa is under XA's binder.
    ("![Xa]: ![XA]: (p(Xa) & q(XA))", ("Xa", "XA")),
    # Captured by the INNER binder although the inner one is vacuous for TPTP.
    ("![XA]: ![Xa]: p(XA)", ("Xa", "XA")),
    # A free variable captured by a binder of the other spelling: Xa is free in
    # TPTP, but under ![XA] the kit reads it as XA's variable.
    ("![XA]: p(Xa, XA)", ("Xa", "XA")),
    ("![Xa]: p(XA)", ("Xa", "XA")),
    # Two free variables (a bare formula or a cnf clause): two implicit
    # universals in TPTP, one variable here.
    ("p(Xa, XA)", ("Xa", "XA")),
    ("(p(Xa) | q(XA))", ("Xa", "XA")),
    # A typed binder list, as TFF writes it.
    ("![Xa: $i, XA: $i]: p(Xa, XA)", ("Xa", "XA")),
])
def test_two_variables_the_kit_would_merge_are_refused_by_name(text, names):
    with pytest.raises(TptpParsingError) as caught:
        parse_tptp_formula(text)
    message = str(caught.value)
    assert message.startswith("SYNTAX_ERROR")
    for name in names:
        assert repr(name) in message, (text, message)
    assert "lower-casing" in message and "Rename one of them" in message


@pytest.mark.parametrize("statement", [
    "cnf(c, axiom, p(Xa, XA)).",
    "cnf(c, axiom, (p(Xa) | q(XA))).",
    "fof(f, axiom, ![Xa, XA]: p(Xa, XA)).",
])
def test_the_statement_readers_refuse_it_too(statement):
    with pytest.raises(TptpParsingError, match="'Xa'.*'XA'|'XA'.*'Xa'"):
        parse_tptp(statement)


def test_each_statement_of_a_problem_is_checked_on_its_own():
    # Xa in the first statement and XA in the second are different formulas'
    # variables: nothing merges them. Within ONE statement they would.
    problem = "fof(a, axiom, ![Xa]: p(Xa)).\nfof(b, axiom, ![XA]: q(XA))."
    assert [f.formula for f in parse_tptp(problem)] == [
        Quantifier("∀", _xa(), _p("xa")),
        Quantifier("∀", _xa(), Atom("Q", [_xa()])),
    ]
    bad = "fof(a, axiom, ![Xa]: p(Xa)).\nfof(b, axiom, ![Xa, XA]: q(Xa, XA))."
    with pytest.raises(TptpParsingError, match="'Xa'.*'XA'|'XA'.*'Xa'"):
        parse_tptp(bad)


# --------------------------------------------------------------------------- #
# Read exactly as before: lower-casing merges nothing that TPTP keeps apart.
# --------------------------------------------------------------------------- #

def test_binders_that_never_meet_read_unchanged():
    # Each ![..] binds only its own body: (∀xa P(xa)) ∧ (∀xa Q(xa)) is this formula.
    assert parse_tptp_formula("(![Xa]: p(Xa)) & (![XA]: q(XA))") == And(
        Quantifier("∀", _xa(), _p("xa")), Quantifier("∀", _xa(), Atom("Q", [_xa()])))
    # The inner binder shadows xa only inside its own body, where only XA occurs.
    assert parse_tptp_formula("![Xa]: (p(Xa) & ![XA]: q(XA))") == Quantifier(
        "∀", _xa(), And(_p("xa"), Quantifier("∀", _xa(), Atom("Q", [_xa()]))))
    # Free Xa lies outside the scope of the binder XA.
    assert parse_tptp_formula("p(Xa) & ![XA]: q(XA)") == And(
        _p("xa"), Quantifier("∀", _xa(), Atom("Q", [_xa()])))
    # The occurrence XA is bound by the INNER binder in TPTP and in the kit alike.
    assert parse_tptp_formula("![Xa]: ![XA]: p(XA)") == Quantifier(
        "∀", _xa(), Quantifier("∀", _xa(), _p("xa")))


def test_ordinary_formulas_read_unchanged():
    assert parse_tptp_formula("![X, Y]: p(X, Y)") == Quantifier(
        "∀", Variable("x"), Quantifier("∀", Variable("y"), _p("x", "y")))
    assert parse_tptp_formula("![Xa]: p(Xa, Xa)") == Quantifier("∀", _xa(), _p("xa", "xa"))
    # a constant spelled like a variable's lower-cased form is not a variable
    assert parse_tptp_formula("![X]: p(X, x1)") == Quantifier(
        "∀", Variable("x"), Atom("P", [Variable("x"), Constant("x1")]))


def test_a_variable_in_a_discarded_annotation_field_is_not_a_variable_of_the_formula():
    # The 4th/5th fields of a statement are parsed and thrown away; an opaque term
    # there may carry a VAR. It cannot merge anything: it is not read at all.
    problem = "fof(a, axiom, ![Xa]: p(Xa), file(f, XA), [Xa, XA])."
    [only] = parse_tptp(problem)
    assert only.formula == Quantifier("∀", _xa(), _p("xa"))


# --------------------------------------------------------------------------- #
# A seeded random test, against an oracle that shares nothing with the reader.
# --------------------------------------------------------------------------- #

_SPELLINGS = ("Xa", "XA", "Y")


def _generate(rng: random.Random, depth: int):
    """A random formula tree over the connectives and quantifiers, with variable
    spellings drawn from a pool in which ``Xa`` and ``XA`` collide."""
    kinds = ["atom"] if depth == 0 else ["atom", "and", "or", "not", "forall", "exists"]
    kind = rng.choice(kinds)
    if kind == "atom":
        return ("atom", rng.choice(("p", "q")),
                tuple(rng.choice(_SPELLINGS) for _ in range(rng.choice((1, 2)))))
    if kind in ("and", "or"):
        return (kind, _generate(rng, depth - 1), _generate(rng, depth - 1))
    if kind == "not":
        return ("not", _generate(rng, depth - 1))
    binders = tuple(rng.choice(_SPELLINGS) for _ in range(rng.choice((1, 2))))
    return (kind, binders, _generate(rng, depth - 1))


def _text(tree) -> str:
    kind = tree[0]
    if kind == "atom":
        return f"{tree[1]}({', '.join(tree[2])})"
    if kind in ("and", "or"):
        return f"({_text(tree[1])} {'&' if kind == 'and' else '|'} {_text(tree[2])})"
    if kind == "not":
        return f"~{_text(tree[1])}"
    mark = "!" if kind == "forall" else "?"
    return f"({mark}[{', '.join(tree[1])}]: {_text(tree[2])})"


def _canon(tree, scope, key, frees):
    """De Bruijn form of a generator tree. ``key`` maps a spelling to the name a
    binder is looked up by: the identity for TPTP's scoping, ``str.lower`` for the
    kit's. A bound occurrence is the distance to its binder; a free one is the
    number of its variable in order of first appearance (``frees`` maps a free
    variable's key to that number), so two forms are equal exactly when they are the
    same formula up to renaming of variables."""
    kind = tree[0]
    if kind == "atom":
        def occurrence(spelling):
            for distance, bound in enumerate(reversed(scope)):
                if bound == key(spelling):
                    return ("bound", distance)
            return ("free", frees.setdefault(key(spelling), len(frees)))
        return ("atom", tree[1], tuple(occurrence(s) for s in tree[2]))
    if kind in ("and", "or"):
        return (kind, _canon(tree[1], scope, key, frees), _canon(tree[2], scope, key, frees))
    if kind == "not":
        return ("not", _canon(tree[1], scope, key, frees))
    inner = list(scope)
    for spelling in tree[1]:
        inner.append(key(spelling))
    form = _canon(tree[2], tuple(inner), key, frees)
    for _ in tree[1]:
        form = (kind, form)                      # one quantifier per binder, outermost first
    return form


def _canon_ast(node, scope, frees):
    """De Bruijn form of the READER's AST (kit scoping: a variable is a name)."""
    if isinstance(node, Atom):
        def occurrence(variable):
            for distance, bound in enumerate(reversed(scope)):
                if bound == variable.name:
                    return ("bound", distance)
            return ("free", frees.setdefault(variable.name, len(frees)))
        return ("atom", node.predicate.lower(), tuple(occurrence(a) for a in node.args))
    if isinstance(node, And):
        return ("and", _canon_ast(node.left, scope, frees), _canon_ast(node.right, scope, frees))
    if isinstance(node, Or):
        return ("or", _canon_ast(node.left, scope, frees), _canon_ast(node.right, scope, frees))
    if isinstance(node, Not):
        return ("not", _canon_ast(node.formula, scope, frees))
    assert isinstance(node, Quantifier), node
    kind = "forall" if node.type == "∀" else "exists"
    return (kind, _canon_ast(node.formula, scope + (node.variable.name,), frees))


def test_the_reader_refuses_exactly_the_formulas_it_would_misread():
    rng = random.Random(20261004)
    refused = accepted = 0
    for _ in range(1500):
        tree = _generate(rng, depth=rng.choice((2, 3)))
        text = _text(tree)
        intended = _canon(tree, (), lambda s: s, {})          # TPTP: the exact spelling
        as_the_kit_reads_it = _canon(tree, (), str.lower, {})  # kit: the lower-cased name
        try:
            node = parse_tptp_formula(text)
        except TptpParsingError as exc:
            assert "differ only by letter case" in str(exc), (text, str(exc)[:120])
            # Justified: lower-casing really changes this formula ...
            assert intended != as_the_kit_reads_it, f"over-refused: {text}"
            refused += 1
            continue
        # ... and everything else is read, and read as the TPTP formula.
        assert intended == as_the_kit_reads_it, f"misread without a word: {text}"
        assert _canon_ast(node, (), {}) == intended, text
        accepted += 1
    # The generator reaches both outcomes often enough to mean something.
    assert refused > 100 and accepted > 100, (refused, accepted)
