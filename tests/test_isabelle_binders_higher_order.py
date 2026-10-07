"""The Isabelle texts of the second order, the third order and the third-order modal embedding keep
every binder off the symbols of the theory.

An Isabelle binder ``\\<forall>x::i.`` shadows a constant ``x`` inside its scope, so a binder spelled like a
declared constant, function, predicate or lifted operator captures it: ``∀x P(x, c_x)`` written as
``\\<forall>x::i. (p x x)`` is the formula ``∀x P(x, x)``. The writers print the names of the source, so each
binder is printed under its own name unless a symbol of the theory has that name, and then under
``name_2``. Isabelle is not run here: the checks are on the text.

Two kinds of check. The hand-derived texts pin the names. The generated formulas check, with a small
parser of the text that is independent of the writers, that

* no binder is spelled like a symbol the text declares, and
* every occurrence of a name inside a binder's scope is bound by the binder the SOURCE meant: the text
  has the same binding structure as the text of the same formula with every binder renamed to a name no
  symbol has.
"""

import random
import re

import pytest

from unicode_logic_kit.fol.nodes import (
    And, Atom, Box, Cardinality, Constant, Function, Implies, Lambda, LambdaVar, Number,
    PredicateTerm, Quantifier, SecondOrderQuantifier, Variable,
)
from unicode_logic_kit.fol._hybrid_nodes import At
from unicode_logic_kit.hol.ho_modal import to_isabelle_ho_modal
from unicode_logic_kit.hol.secondorder import to_isabelle_so
from unicode_logic_kit.hol.thirdorder import to_isabelle_to

V, C = Variable, Constant


def P(*terms):
    return Atom("P", list(terms))


# --------------------------------------------------------------------------- #
# hand-derived texts
# --------------------------------------------------------------------------- #

def test_second_order_binder_is_renamed_off_a_constant_of_its_spelling():
    # ∀x P(x, c_x): the predicate functor is p, the constant is x, so the binder is x_2
    text = to_isabelle_so(Quantifier("∀", V("x"), P(V("x"), C("x"))))
    assert 'consts x :: "i"' in text
    assert 'lemma "(\\<forall>x_2::i. (p x_2 x))"' in text


def test_second_order_predicate_binder_is_renamed_off_a_constant_of_its_spelling():
    # ∃p/1 p(c_p): the bound predicate is applied to the constant p
    formula = SecondOrderQuantifier("∃", "p", 1, Atom("p", [C("p")]))
    text = to_isabelle_so(formula)
    assert 'consts p :: "i"' in text
    assert 'lemma "(\\<exists>p_2::i \\<Rightarrow> bool. (p_2 p))"' in text


def test_second_order_cardinality_variable_is_renamed_off_a_constant_of_its_spelling():
    count = Cardinality(V("x"), P(V("x")))
    formula = And(Atom("=", [count, Number(2)]), Atom("Q", [C("x")]))
    text = to_isabelle_so(formula)
    assert "(card {x_2. (p x_2)})" in text
    assert 'consts x :: "i"' in text


@pytest.mark.parametrize("name", ["card", "True", "False"])
def test_second_order_binder_is_renamed_off_the_names_the_text_itself_uses(name):
    text = to_isabelle_so(Quantifier("∀", V(name), P(V(name))))
    assert f"\\<forall>{name}_2::i." in text and f"(p {name}_2)" in text


def test_second_order_text_without_a_clash_is_as_before():
    assert 'lemma "(\\<forall>x::i. (p x))"' in to_isabelle_so(Quantifier("∀", V("x"), P(V("x"))))
    nested = Quantifier("∀", V("x"), Quantifier("∃", V("x"), P(V("x"))))
    assert 'lemma "(\\<forall>x::i. (\\<exists>x::i. (p x)))"' in to_isabelle_so(nested)


def test_second_order_variable_and_predicate_variable_of_one_name_are_two_binders():
    # ∃p ∀p p(p): the predicate binder and the object binder are told apart
    formula = SecondOrderQuantifier("∃", "p", 1, Quantifier("∀", V("p"), Atom("p", [V("p")])))
    text = to_isabelle_so(formula)
    assert 'lemma "(\\<exists>p::i \\<Rightarrow> bool. (\\<forall>p_2::i. (p p_2)))"' in text


def test_third_order_binder_is_renamed_off_a_constant_of_its_spelling():
    text = to_isabelle_to(Quantifier("∀", V("x"), P(V("x"), C("x"))))
    assert 'consts x :: "i"' in text
    assert 'lemma "(\\<forall>x_2::i. (P x_2 x))"' in text


def test_third_order_lambda_parameter_is_renamed_off_a_constant_of_its_spelling():
    # Pos(λx. G(x)) next to the constant x
    abstraction = Lambda(LambdaVar("x"), Atom("G", [LambdaVar("x")]))
    formula = And(Atom("Pos", [abstraction]), Atom("Q", [C("x")]))
    text = to_isabelle_to(formula)
    assert "(Pos (\\<lambda>x_2::i. (G x_2)))" in text
    assert 'consts x :: "i"' in text


def test_third_order_bound_predicate_is_renamed_off_a_constant_of_its_spelling():
    formula = SecondOrderQuantifier("∃", "G", 1, And(Atom("G", [C("G")]), Atom("Pos", [PredicateTerm("G")])))
    text = to_isabelle_to(formula)
    assert 'consts G :: "i"' in text
    assert "\\<exists>G_2::i \\<Rightarrow> bool." in text and "(G_2 G)" in text


def test_third_order_text_without_a_clash_is_as_before():
    text = to_isabelle_to(Quantifier("∀", V("y"), P(V("y"), C("x"))))
    assert 'lemma "(\\<forall>y::i. (P y x))"' in text


def test_modal_binder_is_renamed_off_a_constant_of_its_spelling():
    text = to_isabelle_ho_modal(Box(Quantifier("∀", V("x"), P(V("x"), C("x")))))
    assert 'consts x :: "i"' in text
    assert 'theorem goal: "mvalid (mbox (mall (\\<lambda>x_2::i. (P x_2 x))))"' in text


def test_modal_binder_is_renamed_off_a_lifted_operator():
    # mall and mand are constants of the embedding; a binder of their name would capture them
    text = to_isabelle_ho_modal(Quantifier("∀", V("mand"), P(V("mand"), V("mand"))))
    assert "(mall (\\<lambda>mand_2::i. (P mand_2 mand_2)))" in text


def test_modal_world_binder_of_an_at_formula_is_anonymous():
    # @_i P(v): the world binder used to be called v and captured the constant v
    text = to_isabelle_ho_modal(At("i", P(C("v"))))
    assert 'consts v :: "i"' in text
    assert 'theorem goal: "mvalid (\\<lambda>_. (P v) nom_i)"' in text


def test_modal_text_without_a_clash_is_as_before():
    text = to_isabelle_ho_modal(Quantifier("∀", V("y"), P(V("y"), C("x"))))
    assert "(mall (\\<lambda>y::i. (P y x)))" in text


# --------------------------------------------------------------------------- #
# generated formulas, checked by a parser of the text
# --------------------------------------------------------------------------- #

TOKEN = re.compile(r"\\<[A-Za-z]+>|[A-Za-z][A-Za-z0-9_']*|::|\S")
IDENTIFIER = re.compile(r"[A-Za-z][A-Za-z0-9_']*\Z")
#: the words that open a binder; ``\<setbinder>`` stands for the ``{`` of ``card {x. …}`` once
#: :func:`_set_binders_as_quantifiers` has rewritten it
QUANTIFIER_WORDS = {"\\<forall>", "\\<exists>", "\\<lambda>", "\\<setbinder>"}
#: the names the text itself gives a meaning to
BUILT_IN = {"card", "True", "False"}


def _declared(text):
    names = set()
    for line in text.splitlines():
        match = re.match(r"\s*(?:consts|abbreviation)\s+([A-Za-z][A-Za-z0-9_']*)", line)
        if match:
            names.add(match.group(1))
    return names


def _goal_lines(text):
    return [line for line in text.splitlines()
            if line.lstrip().startswith(("lemma", "theorem")) or "axiomatization where assumption" in line]


def _binders_and_canonical(line):
    """The binder names of a goal line, and the line with every bound occurrence replaced by the
    ordinal of its binder. A binder is ``<q>NAME::TYPE.`` or the set comprehension ``{NAME.``; its
    scope is the parenthesis or brace it stands in."""
    tokens = TOKEN.findall(line)
    out, binders, stack, ordinal = [], [], [], 0
    depth = 0
    i = 0
    while i < len(tokens):
        token = tokens[i]
        if token in "({":
            depth += 1
            out.append(token)
        elif token in ")}":
            while stack and stack[-1][0] >= depth:
                stack.pop()
            depth -= 1
            out.append(token)
        elif token in QUANTIFIER_WORDS and i + 2 < len(tokens) and tokens[i + 2] == "::":
            name = tokens[i + 1]
            j = i + 3
            while tokens[j] != ".":
                j += 1
            binders.append(name)
            stack.append((depth, name, ordinal))
            out.append(f"{token}<{ordinal}>.")
            ordinal += 1
            i = j
        elif token == "\\<lambda>" and i + 1 < len(tokens) and tokens[i + 1] == "_":
            out.append("\\<lambda>_")       # the anonymous world binder: nothing is bound by it
            i += 1
        elif IDENTIFIER.match(token):
            bound = [entry for entry in stack if entry[1] == token]
            out.append(f"<{bound[-1][2]}>" if bound else token)
        else:
            out.append(token)
        i += 1
    return binders, " ".join(out)


def _set_binders_as_quantifiers(line):
    """``card {x. body}`` has a binder the quantifier syntax does not show: rewrite ``{NAME.`` as a
    quantifier-like binder so :func:`_binders_and_canonical` can read it."""
    return re.sub(r"\{([A-Za-z][A-Za-z0-9_']*)\.", r"{ \\<setbinder>\1::i.", line)


def _analyse(text):
    binders, canonical = [], []
    for line in _goal_lines(text):
        found, canon = _binders_and_canonical(_set_binders_as_quantifiers(line))
        binders += found
        canonical.append(canon)
    return binders, "\n".join(canonical)


BINDER_NAMES = ["x", "w", "v", "u", "P", "Q", "f", "card", "True", "mall", "mand", "R", "p"]
CONSTANT_NAMES = ["x", "w", "v", "u", "c"]


def _gen_term(rng, scope, depth=0):
    options = ["const"] + (["var"] * 3 if scope else []) + (["fun"] if depth == 0 else [])
    kind = rng.choice(options)
    if kind == "var":
        return ("var", rng.choice(scope))
    if kind == "fun":
        return ("fun", "f", _gen_term(rng, scope, 1))
    return ("const", rng.choice(CONSTANT_NAMES))


def _gen(rng, depth, scope, preds, allow_second_order, allow_card):
    if depth == 0 or rng.random() < 0.3:
        heads = [name for name in preds]
        if heads and rng.random() < 0.5:
            return ("batom", rng.choice(heads), _gen_term(rng, scope))
        free_pred = rng.choice(["P", "Q"])
        return ("atom", free_pred, _gen_term(rng, scope))
    kinds = ["all", "ex", "and", "imp", "not"]
    if allow_second_order:
        kinds += ["so"]
    if allow_card:
        kinds += ["card"]
    kind = rng.choice(kinds)
    if kind in ("all", "ex"):
        name = rng.choice(BINDER_NAMES)
        return (kind, name, _gen(rng, depth - 1, scope + [name], preds, allow_second_order, allow_card))
    if kind == "so":
        # a predicate variable never takes the name of a free predicate (the second-order writer
        # reads such a name as bound everywhere)
        name = rng.choice([n for n in BINDER_NAMES if n not in ("P", "Q")])
        return (kind, name, _gen(rng, depth - 1, scope, preds + [name], allow_second_order, allow_card))
    if kind == "card":
        name = rng.choice(BINDER_NAMES)
        return ("card", name, _gen(rng, depth - 1, scope + [name], preds, allow_second_order, False),
                rng.choice([1, 2]))
    if kind == "not":
        return ("not", _gen(rng, depth - 1, scope, preds, allow_second_order, allow_card))
    return (kind, _gen(rng, depth - 1, scope, preds, allow_second_order, allow_card),
            _gen(rng, depth - 1, scope, preds, allow_second_order, allow_card))


def _build_term(tree, rename):
    kind = tree[0]
    if kind == "var":
        return V(rename.get(("var", tree[1]), tree[1]))
    if kind == "fun":
        return Function(tree[1], [_build_term(tree[2], rename)])
    return C(tree[1])


def _build(tree, rename, counter, fresh):
    """The node of ``tree``. With ``fresh`` every binder gets a name of its own (``b0``, ``b1``,
    …) that no symbol has; ``rename`` maps the names in scope to the names they currently have."""
    kind = tree[0]
    if kind == "atom":
        return Atom(tree[1], [_build_term(tree[2], rename)])
    if kind == "batom":
        return Atom(rename.get(("pred", tree[1]), tree[1]), [_build_term(tree[2], rename)])
    if kind == "not":
        from unicode_logic_kit.fol.nodes import Not
        return Not(_build(tree[1], rename, counter, fresh))
    if kind in ("and", "imp"):
        cls = And if kind == "and" else Implies
        return cls(_build(tree[1], rename, counter, fresh), _build(tree[2], rename, counter, fresh))
    name = tree[1]
    if fresh:
        counter[0] += 1
        new = f"b{counter[0]}"
    else:
        new = name
    scoped = dict(rename)
    if kind in ("all", "ex"):
        scoped[("var", name)] = new
        return Quantifier("∀" if kind == "all" else "∃", V(new), _build(tree[2], scoped, counter, fresh))
    if kind == "so":
        scoped[("pred", name)] = new
        return SecondOrderQuantifier("∃", new, 1, _build(tree[2], scoped, counter, fresh))
    scoped[("var", name)] = new
    count = Cardinality(V(new), _build(tree[2], scoped, counter, fresh))
    return Atom("=", [count, Number(tree[3])])


def _generated(count, seed, **options):
    rng = random.Random(seed)
    return [_gen(rng, 3, [], [], **options) for _ in range(count)]


SECOND_ORDER_TREES = _generated(60, 1, allow_second_order=True, allow_card=True)
OBJECT_TREES = _generated(60, 2, allow_second_order=False, allow_card=False)
MODAL_TREES = _generated(40, 3, allow_second_order=True, allow_card=False)


def _check(writer, trees, what):
    clashes = 0
    for tree in trees:
        original = writer(_build(tree, {}, [0], fresh=False))
        renamed = writer(_build(tree, {}, [0], fresh=True))
        binders, canonical = _analyse(original)
        _, canonical_renamed = _analyse(renamed)
        taken = _declared(original) | BUILT_IN
        assert not (set(binders) & taken), (tree, sorted(set(binders) & taken), original)
        assert canonical == canonical_renamed, (tree, original, renamed)
        if any(re.search(r"_\d+\Z", name) for name in binders):
            clashes += 1
    # the generator does produce clashes, so the comparison above is not vacuous
    assert clashes >= 5, what


def test_second_order_binders_keep_clear_of_declared_names_and_bind_as_the_source_does():
    _check(to_isabelle_so, SECOND_ORDER_TREES, "second order")


def test_third_order_binders_keep_clear_of_declared_names_and_bind_as_the_source_does():
    _check(to_isabelle_to, OBJECT_TREES, "third order")


def test_modal_binders_keep_clear_of_declared_names_and_bind_as_the_source_does():
    _check(lambda f: to_isabelle_ho_modal(Box(f)), MODAL_TREES, "third-order modal")
