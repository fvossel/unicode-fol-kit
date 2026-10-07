"""Tests for C49: applying newly-declared Prover9 ``op(precedence, type, symbol)``
operators (unicode_logic_kit.fol.prover9_input).

Every expected tree below is worked out BY HAND with the standard
precedence-climbing algorithm against Prover9's own default operator table
(cited, with the exact numbers, in prover9_input.py's module docstring and
``_DEFAULT_OPS`` — the manual's "Clauses and Formulas" / parsing-declarations
page, mirroring ``declare_standard_parse_types()`` in the Prover9/LADR source),
never captured from a run of this reader. A live Prover9 binary is not there on
every machine (``Prover9Backend().available()`` below says whether this one has
one, through ``$UFK_PROVER9`` and, for a binary inside WSL, ``$UFK_PROVER9_WSL=1``;
the same fallback convention ``test_prover9_entailment.py``'s module docstring
already establishes: "wo ein externes Werkzeug fehlt, ist der kit-eigene Leser
der Prüfstein" — where an external tool is missing, the kit's own reader is
the touchstone) — so the independent second route used throughout is the
kit's OWN semantic validity checker (:func:`unicode_logic_kit.is_valid`, Z3
under the hood: a wholly separate subsystem from the Lark grammar under test)
rather than a live differential against Prover9 itself. One test (marked
``live_prover9``, skip-gated, never required) instead runs a real Prover9
binary when one happens to be available.
"""

import random
from dataclasses import dataclass

import pytest

from unicode_logic_kit import is_valid
from unicode_logic_kit.atp.protocol import Prover9Backend
from unicode_logic_kit.fol.nodes import (
    Atom, Not, And, Or, Implies, Iff, Quantifier, Variable, Constant, Function, Number,
)
from unicode_logic_kit.fol.prover9_input import (
    parse_prover9, parse_prover9_problem, Prover9ParsingError,
)

_prover9 = Prover9Backend()
live_prover9 = pytest.mark.skipif(
    not _prover9.available(),
    reason="no Prover9 binary found ($UFK_PROVER9, with $UFK_PROVER9_WSL=1 for a path inside "
           "WSL, or PATH) -- this test is optional")


# ---------------------------------------------------------------------------
# Regression: the pre-C49 behaviour for a declaration this reader cannot (or
# does not need to) apply must not change. The primary such test already
# lives in tests/test_importers.py::test_prover9_problem_skips_op_directive_and_keeps_decimals
# ("op(800, infix, foo)." must stay silently inert) and is intentionally left
# untouched there; it is re-checked here for one extra pairing to make the
# scope explicit.
# ---------------------------------------------------------------------------

def test_unused_op_declaration_stays_inert():
    recs = parse_prover9_problem(
        "set(prolog_style_variables).\nop(800, infix, foo).\nlt(x, 3.14).")
    assert len(recs) == 1
    assert recs[0].formula == Atom("lt", [Constant("x"), Number(3.14)])


# ---------------------------------------------------------------------------
# Hand-checked atom-tier (Atom-producing) operators
# ---------------------------------------------------------------------------

def test_atom_tier_infix_operator_applied():
    # op(650, infix, "before"): 650 sits strictly between Prover9's arithmetic
    # tier (500) and its comparison tier (700) -- a precedence no built-in
    # occupies -- so "before" becomes a new, non-associative (Prover9 "infix" =
    # Prolog xfx) atom-level relation, exactly like the built-in comparisons.
    # By hand, precedence-climbing "all X all Y (X before Y -> -(Y before X))"
    # against {->: loosest, then -, then "before" tightest among these}:
    #   all X ( all Y ( (X before Y) -> -( (Y before X) ) ) )
    text = 'op(650, infix, "before").\nall X all Y (X before Y -> -(Y before X)).'
    recs = parse_prover9_problem(text)
    assert len(recs) == 1
    x, y = Variable("x"), Variable("y")
    expected = Quantifier("∀", x, Quantifier("∀", y,
        Implies(Atom("before", [x, y]), Not(Atom("before", [y, x])))))
    assert recs[0].formula == expected

    # Second, independent route: this is not just SOME tree that happened to
    # parse -- paired with the fact "a before b", it Z3-proves "-(b before a)"
    # -- i.e. the parsed structure really does encode asymmetry (a wholly
    # different subsystem, Z3, confirming the SAME semantic content the
    # grammar produced), not merely resemble it syntactically.
    a, b = Constant("a"), Constant("b")
    fact = Atom("before", [a, b])
    assert is_valid(Implies(And(expected, fact), Not(Atom("before", [b, a]))))


@pytest.mark.parametrize("op_type,expected_builder", [
    # xfy (right-associative): "a seq b seq c" groups as seq(a, seq(b, c)).
    ("infix_right", lambda a, b, c: Atom("seq", [a, Atom("seq", [b, c])])),
    # yfx (left-associative): "a seq b seq c" groups as seq(seq(a, b), c).
    ("infix_left", lambda a, b, c: Atom("seq", [Atom("seq", [a, b]), c])),
])
def test_atom_tier_associativity_hand_derived(op_type, expected_builder):
    a, b, c = Constant("a"), Constant("b"), Constant("c")
    recs = parse_prover9_problem(f"op(600, {op_type}, seq).\na seq b seq c.")
    assert recs[0].formula == expected_builder(a, b, c)


def test_atom_tier_plain_infix_does_not_chain():
    # xfx (Prover9's "infix", non-associative): BOTH operands of a plain infix
    # operator need strictly lower precedence than the operator itself, so a
    # bare 3-way chain has no parse without explicit parentheses -- exactly
    # the manual's documented xfx semantics, and exactly how the kit's own
    # built-in comparisons (also "infix") already behave (`a < b < c` is not
    # a formula in this grammar either). The single non-recursive rule this
    # reader splices in for "infix" reproduces that directly: there is no
    # grammar path that consumes two "seq" tokens at once.
    with pytest.raises(Prover9ParsingError):
        parse_prover9_problem("op(600, infix, seq).\na seq b seq c.")
    # A single use (one occurrence, not a chain) still parses.
    recs = parse_prover9_problem("op(600, infix, seq).\na seq b.")
    assert recs[0].formula == Atom("seq", [Constant("a"), Constant("b")])


# ---------------------------------------------------------------------------
# Regression (adversarial review of C49): an op() symbol containing an
# uppercase letter is accepted by this reader's own validator
# (_P9_BARE_SYMBOL_RE, and real Prover9 places no case restriction on
# operator names either) and falls inside a supported splice window here, so
# it must be APPLIED like any other identifier-shaped symbol, not crash Lark's
# own grammar construction. Root cause: the generated Lark RULE/alias names
# used to splice op.symbol itself into an f-string (e.g. "atom_chain_Before");
# Lark's grammar meta-language requires a RULE/alias identifier to start with
# a lowercase letter and never contain an uppercase one (an uppercase-leading
# token is read as a TERMINAL reference instead), so building the grammar
# text raised an uncaught lark.exceptions.UnexpectedToken -- a bare Lark
# internals leak, not a targeted Prover9ParsingError, for a symbol shape this
# reader's own validator otherwise accepts. _build_custom_grammar now names
# generated rules/aliases from a per-bucket numeric index instead, so the
# real symbol only ever appears inside a quoted string literal.
# ---------------------------------------------------------------------------

def test_atom_tier_uppercase_symbol_applied():
    # "Before" (leading uppercase) at precedence 650 -- the exact placement
    # already hand-checked for lowercase "before" in
    # test_atom_tier_infix_operator_applied above, just pinning the symbol
    # shape that used to crash. By hand, precedence-climbing
    # "all X all Y (X Before Y -> -(Y Before X))" against the identical
    # operator table used for the lowercase case:
    #   all X ( all Y ( (X Before Y) -> -( (Y Before X) ) ) )
    text = 'op(650, infix, "Before").\nall X all Y (X Before Y -> -(Y Before X)).'
    recs = parse_prover9_problem(text)
    assert len(recs) == 1
    x, y = Variable("x"), Variable("y")
    expected = Quantifier("∀", x, Quantifier("∀", y,
        Implies(Atom("Before", [x, y]), Not(Atom("Before", [y, x])))))
    assert recs[0].formula == expected

    # Second, independent route, mirroring test_atom_tier_infix_operator_applied's
    # differential exactly (this test exists ONLY to pin the uppercase symbol
    # shape, so it reuses that test's already hand-checked oracle rather than
    # inventing a new one). This is genuinely content-dependent, unlike a
    # content-blind propositional-tautology check (see the adversarial-review
    # regression note above): "fact" and the goal atom are INDEPENDENT ground
    # terms, not extracted from "expected" itself, so Z3 can only derive
    # "-(b Before a)" by actually performing the universal instantiation
    # X := a, Y := b against "expected"'s own quantified structure -- which
    # requires "expected" to really be the asymmetry axiom over the SPECIFIC
    # predicate name "Before" with arguments in the parsed order. A parse bug
    # that used a different predicate name, dropped the negation, or nested
    # the quantifiers/arguments differently would make this entailment
    # UNPROVABLE (Z3 would find a countermodel), unlike a tautology that
    # holds regardless of the predicate's identity or shape.
    a, b = Constant("a"), Constant("b")
    fact = Atom("Before", [a, b])
    assert is_valid(Implies(And(expected, fact), Not(Atom("Before", [b, a]))))


def test_op_symbol_bare_single_uppercase_letter_applied():
    # A single bare uppercase letter, "X" -- the exact symbol from the
    # adversarial review's reproduction -- is itself identifier-shaped
    # (matches the grammar's own NAME terminal) and must be applied, not
    # crash: op(650, infix, "X"). declared, then used as "a X b".
    recs = parse_prover9_problem('op(650, infix, "X").\na X b.')
    assert recs[0].formula == Atom("X", [Constant("a"), Constant("b")])


def test_term_tier_mixed_case_infix_prefix_postfix_applied():
    a, b, c, x = Constant("a"), Constant("b"), Constant("c"), Constant("x")
    # These files say which names are variables: without the flag Prover9 reads ``x`` as a
    # variable (names that begin with u to z), and the constant these texts mean is ``x``.
    flag = "set(prolog_style_variables).\n"
    # myOp (camelCase) as a term-tier infix operator -- same placement/shape
    # as the lowercase "o" hand-check above.
    infix = parse_prover9_problem(flag + 'op(450, infix_left, "myOp").\nf(a myOp b) = c.')[0].formula
    assert infix == Atom("=", [Function("f", [Function("myOp", [a, b])]), c])
    # Neg (leading uppercase) as a term-tier prefix operator.
    prefix = parse_prover9_problem(flag + 'op(150, prefix, "Neg").\n(Neg x) = x.')[0].formula
    assert prefix == Atom("=", [Function("Neg", [x]), x])
    # Prime (leading uppercase) as a term-tier postfix operator.
    postfix = parse_prover9_problem(flag + 'op(150, postfix, "Prime").\n(x Prime) = x.')[0].formula
    assert postfix == Atom("=", [Function("Prime", [x]), x])


def test_prover9_op_round_trip_random_uppercase_symbols():
    # A deterministic companion to test_prover9_op_round_trip_random that
    # ALWAYS uses an uppercase-leading or camelCase symbol -- that fuzzer's
    # own alphabet (f"cust{i}") is entirely lowercase-prefixed and so never
    # exercised the crash fixed above, despite running 300 random cases.
    rng = random.Random(20260919)
    shapes = ["Cust{0}", "cUST{0}", "Custom{0}Op", "X{0}"]
    for i in range(40):
        sym = rng.choice(shapes).format(i)
        kind = rng.choice(["atom_infix", "term_infix", "term_prefix"])
        if kind == "atom_infix":
            op_type = rng.choice(["infix", "infix_left", "infix_right"])
            prec = rng.choice(_ATOM_TIER_PRECS)
        elif kind == "term_infix":
            op_type = rng.choice(["infix", "infix_left", "infix_right"])
            prec = rng.choice(_TERM_TIER_PRECS)
        else:
            op_type = rng.choice(["prefix", "prefix_paren"])
            prec = rng.choice(_TERM_TIER_PRECS)
        custom = _CustomTestOp(sym, kind, op_type)
        formula = _rand_formula_with_custom(rng, rng.randint(1, 3), custom, forced=True)
        text = _to_text(formula, custom)

        parsed = parse_prover9(text, custom_ops=[(prec, op_type, sym)])
        assert parsed == formula, f"{text!r} -> {parsed} != {formula}"

        text2 = parsed.to_prover9()
        reparsed = parse_prover9(text2)
        assert _same_formula(reparsed, parsed), f"{text2!r} -> {reparsed} != {parsed}"


# ---------------------------------------------------------------------------
# Hand-checked term-tier (Function-producing) operators
# ---------------------------------------------------------------------------

def test_term_tier_infix_operator_applied():
    # op(450, infix_left, "o"): 450 sits strictly between the "*" tier (400 in
    # this reader's own product level) and the "+" tier (500), so "o" becomes
    # a new Function-producing operator, its operands taken from the atomic
    # (unit_term) level -- by hand, "f(a o b) = c" is f( (a o b) ) = c, i.e.
    # equality of f(o(a, b)) and c.
    recs = parse_prover9_problem("op(450, infix_left, \"o\").\nf(a o b) = c.")
    a, b, c = Constant("a"), Constant("b"), Constant("c")
    expected = Atom("=", [Function("f", [Function("o", [a, b])]), c])
    assert recs[0].formula == expected

    # Second, independent route: an INDEPENDENTLY hand-built axiom -- "for
    # every X, f(X o b) = c implies g(X)" -- together with "expected" (the
    # actual parsed tree) entails "g(a)" ONLY if "expected" really is
    # f(o(a, b)) = c with the operands nested and ordered exactly as the
    # axiom's own X-slot requires; a parse that instead produced o(b, a),
    # applied "o" outside "f", or swapped "f"/"o" would leave "expected"
    # unable to instantiate the axiom's X := a case (o is an uninterpreted
    # function, so Z3 is free to pick a model where the mismatched term
    # differs from f(a o b)), so no such proof would exist -- unlike a
    # content-blind tautology (see the adversarial-review regression note),
    # this genuinely depends on the term's internal structure.
    x = Variable("x")
    axiom = Quantifier("∀", x, Implies(
        Atom("=", [Function("f", [Function("o", [x, b])]), c]), Atom("g", [x])))
    assert is_valid(Implies(And(axiom, expected), Atom("g", [a])))


def test_term_tier_left_vs_right_associativity_hand_derived():
    a, b, c = Constant("a"), Constant("b"), Constant("c")
    left = parse_prover9_problem("op(450, infix_left, o).\n(a o b o c) = a.")[0].formula
    assert left == Atom("=", [Function("o", [Function("o", [a, b]), c]), a])
    right = parse_prover9_problem("op(450, infix_right, o).\n(a o b o c) = a.")[0].formula
    assert right == Atom("=", [Function("o", [a, Function("o", [b, c])]), a])


def test_term_tier_prefix_and_postfix_applied():
    x = Constant("x")
    # The files set the flag: without it Prover9 reads ``x`` as a variable, and these texts mean the constant.
    flag = "set(prolog_style_variables).\n"
    prefix = parse_prover9_problem(flag + "op(150, prefix, negsym).\n(negsym x) = x.")[0].formula
    assert prefix == Atom("=", [Function("negsym", [x]), x])
    postfix = parse_prover9_problem(flag + "op(150, postfix, primed).\n(x primed) = x.")[0].formula
    assert postfix == Atom("=", [Function("primed", [x]), x])
    # fy-style self-chaining is accepted (see the module docstring's deviation
    # note: this reader does not distinguish fy from fx self-chaining).
    double = parse_prover9_problem(flag + "op(150, prefix, negsym).\n(negsym negsym x) = x.")[0].formula
    assert double == Atom("=", [Function("negsym", [Function("negsym", [x])]), x])


def test_op_symbol_list_declares_several_operators_at_once():
    # op(precedence, type, [s1, s2]) declares BOTH symbols with the same
    # precedence/type in one directive (Prover9's own list form).
    recs = parse_prover9_problem(
        'op(450, infix_left, [o, p]).\n(a o b) = (a p b).')
    a, b = Constant("a"), Constant("b")
    assert recs[0].formula == Atom(
        "=", [Function("o", [a, b]), Function("p", [a, b])])


# ---------------------------------------------------------------------------
# Refusals: redeclaring a built-in, and malformed op() directives
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("directive,symbol", [
    ('op(500, infix, "+").', "+"),          # real Prover9 precedence for +
    ('op(700, infix, "=").', "="),          # real Prover9 precedence for =
    ('op(780, infix_right, "&").', "&"),    # real Prover9 precedence for &
    ('op(350, prefix, "-").', "-"),         # real Prover9 precedence for -
    ('op(999, infix, "+").', "+"),          # even at a DIFFERENT precedence
])
def test_redeclaring_a_builtin_is_refused_by_name(directive, symbol):
    with pytest.raises(Prover9ParsingError) as exc:
        parse_prover9_problem(directive)
    assert symbol in str(exc.value)
    assert "redeclaring built-in" in str(exc.value)


def test_redeclaring_an_already_declared_custom_operator_is_refused():
    with pytest.raises(Prover9ParsingError) as exc:
        parse_prover9_problem("op(400, infix, foo).\nop(410, infix_left, foo).")
    assert "foo" in str(exc.value)


@pytest.mark.parametrize("directive", [
    "op(400, infix, x, y).",     # wrong arity (4 top-level arguments)
    "op(400, infix).",           # wrong arity (2 arguments, and type != ordinary)
    "op(infix, x).",             # Prover9's 2-arg ordinary-only shorthand: unsupported here
    "op(abc, infix, x).",        # non-integer precedence
    "op(400, weird, x).",        # unknown type keyword
    "op(400, infix, ++).",       # symbolic (non-identifier) new symbol: unsupported
    "op(400, infix, []).",       # empty symbol list
    "op(0, infix, x).",          # precedence out of Prover9's 1-998 range
    "op(999999, infix, x).",     # precedence out of Prover9's 1-998 range
])
def test_malformed_op_directive_is_refused(directive):
    with pytest.raises(Prover9ParsingError):
        parse_prover9_problem(directive)


# ---------------------------------------------------------------------------
# Placements Prover9 itself would not accept from this reader: not a hard
# error at declaration time (that would break e.g. the regression above),
# but never applied either -- using such an operator fails, loudly, at the
# point of use instead.
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("directive", [
    'op(700, infix, "mid").',        # ties the comparison tier exactly
    'op(780, infix_right, "mid").',  # ties the '&' connective tier exactly
    'op(760, infix, "mid").',        # in the (unsupported) connective-adjacent gap
    'op(650, prefix, "mid").',       # prefix declared at an atom-tier precedence
])
def test_unsupported_placement_left_inert_not_refused(directive):
    # The bare declaration is accepted...
    recs = parse_prover9_problem(directive)
    assert recs == []
    # ...but a formula that actually tries to USE "mid" as an operator still
    # fails to parse -- loudly, just at that later point, exactly as it did
    # before this feature existed (an unrecognised bare name).
    with pytest.raises(Prover9ParsingError):
        parse_prover9_problem(directive + "\na mid b.")


def test_ordinary_type_is_inert_but_still_blocks_redeclaration():
    recs = parse_prover9_problem("op(400, ordinary, foo).\nfoo(a).")
    assert recs[0].formula == Atom("foo", [Constant("a")])
    with pytest.raises(Prover9ParsingError):
        parse_prover9_problem("op(400, ordinary, foo).\nop(410, infix, foo).")


# ---------------------------------------------------------------------------
# Positional scoping: a declaration only affects formulas that follow it.
# ---------------------------------------------------------------------------

def test_op_directive_only_affects_later_formulas():
    with pytest.raises(Prover9ParsingError):
        # "before" used ahead of its own declaration: an ordinary undeclared
        # name, not an operator -- the same generic syntax error as always.
        parse_prover9_problem("X before Y.\nop(650, infix, before).")
    # Declared first, then used: applies. (The file sets the flag: without it ``X`` and ``Y`` are
    # constants, which is what Prover9 reads.)
    recs = parse_prover9_problem("set(prolog_style_variables).\nop(650, infix, before).\nX before Y.")
    assert recs[0].formula == Atom("before", [Variable("x"), Variable("y")])


def test_parse_prover9_accepts_custom_ops_directly():
    # parse_prover9_problem threads this automatically; a single formula can
    # also be parsed directly against previously-declared operators.
    node = parse_prover9("X before Y", custom_ops=[(650, "infix", "before")])
    assert node == Atom("before", [Variable("x"), Variable("y")])


# ---------------------------------------------------------------------------
# Round trip: parse with declared ops -> kit Node -> to_prover9() -> re-parse
# gives an equal Node; every previously-accepted Prover9 input still parses
# byte-identically (the empty-custom_ops fast path is untouched -- see
# tests/test_importers.py's whole Prover9 section, re-run unmodified).
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class _CustomTestOp:
    symbol: str
    kind: str    # "atom_infix" | "term_infix" | "term_prefix"
    op_type: str


_ORD_PREDS = (("P", 1), ("Q", 2), ("Big", 0))
_CONSTS = ("a", "b", "c")
_VARS = ("x", "y", "z")


def _rand_ordinary_atom(rng):
    name, arity = rng.choice(_ORD_PREDS)
    return Atom(name, [Constant(rng.choice(_CONSTS)) for _ in range(arity)])


def _make_custom_leaf(rng, custom):
    l, r = Constant(rng.choice(_CONSTS)), Constant(rng.choice(_CONSTS))
    if custom.kind == "atom_infix":
        return Atom(custom.symbol, [l, r])
    if custom.kind == "term_infix":
        return Atom("=", [Function(custom.symbol, [l, r]), Constant(rng.choice(_CONSTS))])
    return Atom("=", [Function(custom.symbol, [l]), Constant(rng.choice(_CONSTS))])


def _rand_formula_with_custom(rng, depth, custom, forced):
    """A random formula over And/Or/Not/Implies/Iff/quantifiers and ordinary
    atoms that is GUARANTEED to contain exactly one use of ``custom``
    somewhere (``forced`` is threaded down exactly one branch at each step)."""
    if depth <= 0 or rng.random() < 0.3:
        return _make_custom_leaf(rng, custom) if forced else _rand_ordinary_atom(rng)
    kind = rng.choice(["not", "and", "or", "imp", "iff", "all", "ex"])
    if kind == "not":
        return Not(_rand_formula_with_custom(rng, depth - 1, custom, forced))
    if kind in ("all", "ex"):
        var = rng.choice(_VARS)
        q = "∀" if kind == "all" else "∃"
        return Quantifier(q, Variable(var),
                           _rand_formula_with_custom(rng, depth - 1, custom, forced))
    cls = {"and": And, "or": Or, "imp": Implies, "iff": Iff}[kind]
    side = rng.choice([0, 1])
    left = _rand_formula_with_custom(rng, depth - 1, custom, forced and side == 0)
    right = _rand_formula_with_custom(rng, depth - 1, custom, forced and side == 1)
    return cls(left, right)


def _term_text(node, custom):
    if isinstance(node, Variable):
        return node.name.upper()
    if isinstance(node, Constant):
        return node.name
    if isinstance(node, Function) and node.name == custom.symbol:
        if custom.kind == "term_infix":
            l, r = node.args
            return f"({_term_text(l, custom)} {custom.symbol} {_term_text(r, custom)})"
        (x,) = node.args
        return f"({custom.symbol} {_term_text(x, custom)})"
    return f"{node.name}(" + ", ".join(_term_text(a, custom) for a in node.args) + ")"


def _to_text(node, custom):
    """Render ``node`` as Prover9 text: the DECLARED infix/prefix surface
    syntax for the leaf built by ``_make_custom_leaf``, ordinary syntax
    otherwise. Every connective/quantifier is fully parenthesised, so this
    helper never has to reason about precedence itself."""
    if isinstance(node, Quantifier):
        q = "all" if node.type == "∀" else "exists"
        return f"({q} {node.variable.name.upper()} {_to_text(node.formula, custom)})"
    if isinstance(node, Not):
        return f"(-{_to_text(node.formula, custom)})"
    if isinstance(node, And):
        return f"({_to_text(node.left, custom)} & {_to_text(node.right, custom)})"
    if isinstance(node, Or):
        return f"({_to_text(node.left, custom)} | {_to_text(node.right, custom)})"
    if isinstance(node, Implies):
        return f"({_to_text(node.left, custom)} -> {_to_text(node.right, custom)})"
    if isinstance(node, Iff):
        return f"({_to_text(node.left, custom)} <-> {_to_text(node.right, custom)})"
    # Atom
    if custom.kind == "atom_infix" and node.predicate == custom.symbol:
        l, r = node.args
        return f"({_term_text(l, custom)} {custom.symbol} {_term_text(r, custom)})"
    if node.predicate == "=" and len(node.args) == 2:
        l, r = node.args
        return f"({_term_text(l, custom)} = {_term_text(r, custom)})"
    if not node.args:
        return node.predicate
    return f"{node.predicate}(" + ", ".join(_term_text(a, custom) for a in node.args) + ")"


_ATOM_TIER_PRECS = (501, 550, 600, 650, 699, 710, 740)
_TERM_TIER_PRECS = (1, 50, 120, 200, 260, 290, 310, 330, 360, 400, 490, 499)


def _re_binds_a_name(node, enclosing=frozenset()):
    """Whether a binder of the formula sits inside the scope of a binder of the same name."""
    if isinstance(node, Quantifier):
        if node.variable.name in enclosing:
            return True
        enclosing = enclosing | {node.variable.name}
    return any(_re_binds_a_name(child, enclosing) for child in node._child_nodes())


def _bound_names_by_depth(node, scope=()):
    """``node`` with every bound variable named by the depth of its binder: two formulas that differ only in
    the names of their bound variables have one such form."""
    if isinstance(node, Quantifier):
        name = f"#{len(scope)}"
        return Quantifier(node.type, Variable(name),
                          _bound_names_by_depth(node.formula, scope + ((node.variable.name, name),)))
    if isinstance(node, Variable):
        for original, bound in reversed(scope):
            if original == node.name:
                return Variable(bound)
        return node
    return node.map_children(lambda child: _bound_names_by_depth(child, scope))


def _same_formula(read, original):
    """Equal, or equal up to the names of the bound variables when the formula re-binds a name: the text of
    such a formula is written under a fresh variable for the inner binder, so that Prover9 renames nothing."""
    if _re_binds_a_name(original):
        return _bound_names_by_depth(read) == _bound_names_by_depth(original)
    return read == original


def test_prover9_op_round_trip_random():
    rng = random.Random(20260918)
    for i in range(300):
        kind = rng.choice(["atom_infix", "term_infix", "term_prefix"])
        sym = f"cust{i}"
        if kind == "atom_infix":
            op_type = rng.choice(["infix", "infix_left", "infix_right"])
            prec = rng.choice(_ATOM_TIER_PRECS)
        elif kind == "term_infix":
            op_type = rng.choice(["infix", "infix_left", "infix_right"])
            prec = rng.choice(_TERM_TIER_PRECS)
        else:
            op_type = rng.choice(["prefix", "prefix_paren"])
            prec = rng.choice(_TERM_TIER_PRECS)
        custom = _CustomTestOp(sym, kind, op_type)
        formula = _rand_formula_with_custom(rng, rng.randint(1, 3), custom, forced=True)
        text = _to_text(formula, custom)

        parsed = parse_prover9(text, custom_ops=[(prec, op_type, sym)])
        assert parsed == formula, f"{text!r} -> {parsed} != {formula}"

        # to_prover9() has no notion of op() declarations at all -- it always
        # renders an unknown predicate/function in ordinary prefix/functor
        # form -- so the re-parse below needs no custom_ops.
        text2 = parsed.to_prover9()
        reparsed = parse_prover9(text2)
        assert _same_formula(reparsed, parsed), f"{text2!r} -> {reparsed} != {parsed}"


def test_prover9_op_problem_round_trip_random():
    # Same property, driven through the whole-file reader (op(...) directive
    # + formulas(...) block), matching test_prover9_problem_round_trip_random's
    # existing shape.
    rng = random.Random(7)
    for i in range(60):
        sym = f"pcust{i}"
        prec = rng.choice(_ATOM_TIER_PRECS)
        op_type = rng.choice(["infix", "infix_left", "infix_right"])
        custom = _CustomTestOp(sym, "atom_infix", op_type)
        formula = _rand_formula_with_custom(rng, rng.randint(1, 2), custom, forced=True)
        text = _to_text(formula, custom)
        problem = f'op({prec}, {op_type}, {sym}).\nformulas(sos).\n  {text}.\nend_of_list.\n'
        recs = parse_prover9_problem(problem)
        assert len(recs) == 1 and recs[0].role == "sos"
        assert recs[0].formula == formula, text


# ---------------------------------------------------------------------------
# Optional live check against a real Prover9 binary (never required).
# ---------------------------------------------------------------------------

@live_prover9
def test_prover9_accepts_our_op_declaration_live():
    """When a real Prover9 binary IS available, confirm it accepts exactly the
    op() declaration this reader assumes (a "before" relation at precedence
    650, a free precedence no Prover9 built-in occupies) by running a real,
    trivially-provable problem through it end to end."""
    problem = (
        "set(prolog_style_variables).\n"
        "op(650, infix, before).\n"
        "formulas(sos).\n"
        "  all X all Y (X before Y -> -(Y before X)).\n"
        "  a before b.\n"
        "end_of_list.\n"
        "formulas(goals).\n"
        "  -(b before a).\n"
        "end_of_list.\n"
    )
    # Through the kit's own runner, which drives a binary inside WSL when
    # $UFK_PROVER9_WSL=1 (a raw subprocess call with a Windows path could not), and
    # raises Prover9Rejected, with Prover9's own message, if it refuses the file.
    from unicode_logic_kit.atp.prover9_entailment import _run_prover9
    assert _run_prover9(problem, _prover9._binary(), timeout=30, raise_on_rejection=True,
                        use_wsl=_prover9._uses_wsl()) is True
