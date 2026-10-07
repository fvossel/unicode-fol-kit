r"""What ``Node.to_prover9()`` (the single renderer: the command line and the MCP ``render`` tool call it)
owes the text it writes: text that means the node.

Prover9 reads the NAMES of a text, so two things make it read another formula than the node:

**A binder inside the scope of a binder of its own name.** LADR renames the inner variable to a symbol
it picks itself, the first of ``x0``, ``x1``, ... that is no variable in scope, and does not look at the
constants of the formula (measured on Prover9 2026-8A: ``(all W (all W P(W, x0)))`` is clausified to
``P(A, A)``). The node ``∀w ∀w P(w, x0)``, whose ``x0`` is a constant, says ``∀e P(e, x0)``, and
``P(alpha, alpha)`` does NOT follow from it (universe {0, 1}, x0 = 0, alpha = 1, P = {(0, 0), (1, 0)}),
while the text with the capture does entail it. The free variables of a node count as binders of the
scope, because Prover9 closes a formula universally.

**A counting witness that is a variable of the formula in another case.** Prover9 writes a variable in upper
case, so a witness named ``x0`` and a variable named ``X0`` are ONE variable there. ``∀X0 ∃≥2 x R(x, X0)``
says that every element has at least two ``R``-predecessors; with ``R = {(0, 0), (1, 0)}`` on the universe
{0, 1, 2} (``alpha`` = 0, ``beta`` = 1) element 1 has none, so ``∃≥2`` of it is not entailed by
``R(alpha, alpha), R(beta, alpha), alpha ≠ beta``, while the capturing text ``(all X0 (exists X0 (exists X1
...)))`` is entailed.

The problem writer makes the same preparation of every formula of a problem, with the same functions, so
the single renderer and the writer write the same text for a formula the writer has nothing else to rename in.
The live tests run the real Prover9 where there is one and skip, with a reason, where there is none.
"""

import os
import random
import re
import threading

import pytest

from unicode_logic_kit.atp.prover9_entailment import _run_prover9, generate_prover9_input_with_mapping
from unicode_logic_kit.atp.protocol import Prover9Backend
from unicode_logic_kit.fol import _fol_nodes
from unicode_logic_kit.fol._msfl_nodes import SortedConstant, SortedCount, SortedQuantifier
from unicode_logic_kit.fol.nodes import (
    And, Atom, Constant, Contrast, Count, Function, Iff, Implies, Not, Number, Or, Quantifier, Variable, Xor,
)
from unicode_logic_kit.fol.prover9_input import parse_prover9

w, x, y, z = Variable("w"), Variable("x"), Variable("y"), Variable("z")
alpha, beta = Constant("alpha"), Constant("beta")


def P(*args):
    return Atom("P", list(args))


def R(*args):
    return Atom("R", list(args))


def FA(variable, body):
    return Quantifier("∀", variable, body)


def EX(variable, body):
    return Quantifier("∃", variable, body)


def _binder_names_in_scope_twice(text):
    """The variables a text binds INSIDE the scope of a binder of the same spelling (every quantifier of the
    renderer is written ``(all V ...)`` and its scope is that parenthesis)."""
    found, open_scopes = [], []
    for token in re.finditer(r"\(\s*(all|exists)\s+([A-Za-z_][A-Za-z0-9_]*)|\(|\)", text):
        if token.group(0) == ")":
            open_scopes.pop()
        elif token.group(1):
            name = token.group(2)
            if any(name == scope for scope in open_scopes):
                found.append(name)
            open_scopes.append(name)
        else:
            open_scopes.append(None)
    return found


# --------------------------------------------------------------------------- #
# A binder inside the scope of a binder of its own name.
# --------------------------------------------------------------------------- #

_X0 = Constant("x0")


def test_a_re_bound_binder_is_written_under_a_fresh_variable():
    node = FA(w, FA(w, P(w, _X0)))
    text = node.to_prover9()
    assert _binder_names_in_scope_twice(text) == []
    # the inner binder took a name no symbol of the node has, and the constant is written as it is
    assert text == "(all W (all W0 P(W0, x0)))"


def test_the_text_of_a_re_bound_binder_reads_back_as_the_same_formula_up_to_the_name_of_the_binder():
    node = FA(w, FA(w, P(w, _X0)))
    read = parse_prover9(node.to_prover9())
    inner = read.formula
    assert isinstance(read, Quantifier) and isinstance(inner, Quantifier)
    assert read.variable != inner.variable
    assert inner.formula == P(inner.variable, _X0)


@pytest.mark.parametrize("node, expected", [
    (FA(w, FA(w, FA(w, P(w, Constant("x1"))))), "(all W (all W0 (all W1 P(W1, x1))))"),
    (EX(w, EX(w, P(w, _X0))), "(exists W (exists W0 P(W0, x0)))"),
    (FA(w, EX(w, P(w, _X0))), "(all W (exists W0 P(W0, x0)))"),
    (FA(w, And(P(w, _X0), EX(w, R(w, w)))), "(all W (P(W, x0) & (exists W0 R(W0, W0))))"),
    (FA(w, FA(Variable("W"), P(w, Variable("W")))), None),      # w and W: one variable to Prover9
], ids=["three deep", "exists over exists", "forall over exists", "inner binder after a use", "w and W"])
def test_every_kind_of_re_binding_is_renamed(node, expected):
    text = node.to_prover9()
    assert _binder_names_in_scope_twice(text) == []
    if expected is not None:
        assert text == expected


def test_sibling_binders_of_one_name_are_no_re_binding_and_are_written_as_they_are():
    node = And(FA(x, P(x)), FA(x, Atom("Q", [x])))
    assert node.to_prover9() == "((all X P(X)) & (all X Q(X)))"


def test_a_free_variable_counts_as_a_binder_of_the_scope_because_prover9_closes_the_formula():
    # P(X) & (all X Q(X)) is read as all X (P(X) & (all X Q(X))): the inner binder re-binds.
    node = And(P(x), FA(x, Atom("Q", [x])))
    assert node.to_prover9() == "(P(X) & (all X0 Q(X0)))"
    # a free variable of another name is no reason to rename
    assert And(P(y), FA(x, Atom("Q", [x]))).to_prover9() == "(P(Y) & (all X Q(X)))"


_BIG_X = Variable("X")


@pytest.mark.parametrize("node", [
    FA(_BIG_X, P(x)),                                   # the free x is bound by the text: (all X P(X))
    FA(_BIG_X, And(P(x), Atom("Q", [_BIG_X]))),
    EX(x, And(Atom("Q", [x]), FA(y, R(Variable("Y"), x)))),      # Y is free inside the binder of y
    And(P(x), Atom("Q", [_BIG_X])),                     # two parameters, one variable in the text
    Implies(P(x), EX(y, R(Variable("Y")))),
])
def test_two_variables_that_no_renaming_of_a_binder_tells_apart_are_refused_by_name(node):
    # Hand-derived for FA(X, P(x)): the formula says P of the parameter x (the quantifier binds nothing); the
    # text (all X P(X)) says that every element has P, which is another formula (P = {x} on {x, other}).
    with pytest.raises(NotImplementedError, match=r"Node\.to_prover9.*would both render as the Prover9 identifier"):
        node.to_prover9()


def test_the_refusal_of_two_merged_variables_names_both_spellings():
    with pytest.raises(NotImplementedError) as caught:
        And(P(x), Atom("Q", [_BIG_X])).to_prover9()
    assert "'x'" in str(caught.value) and "'X'" in str(caught.value)


def test_two_variables_that_differ_in_case_and_are_bound_apart_are_written_as_they_are():
    # the scopes are two siblings, so the text binds each of them to its own quantifier
    assert And(FA(x, P(x)), FA(_BIG_X, Atom("Q", [_BIG_X]))).to_prover9() == "((all X P(X)) & (all X Q(X)))"
    # a free variable and a binder of another name that is not the same variable in the text
    assert And(P(x), FA(y, Atom("Q", [y]))).to_prover9() == "(P(X) & (all Y Q(Y)))"


def test_a_free_variable_and_a_binder_of_one_upper_case_name_are_written_with_the_binder_renamed():
    # P(x) & ∀X Q(X): the text P(X) & (all X Q(X)) is closed as all X (...) and its inner X would be renamed by
    # Prover9 to x0 (or the like), so the binder is given a name of its own now: nothing is merged
    assert And(P(x), FA(_BIG_X, Atom("Q", [_BIG_X]))).to_prover9() == "(P(X) & (all X0 Q(X0)))"


@pytest.mark.parametrize("name", ["x-1", "1x", "x'", "x.y", "x y", ""])
def test_a_variable_that_is_no_word_prover9_reads_is_refused_by_name(name):
    # (all X-1 P(X-1)) is not a quantifier over a variable called X-1: Prover9 reads X - 1, an operator, and the
    # kit's own reader cannot read the text. The node is refused before text is written, by the single renderer
    # and by the problem writer alike.
    node = FA(Variable(name), P(Variable(name)))
    with pytest.raises(NotImplementedError, match="no word Prover9 reads"):
        node.to_prover9()
    with pytest.raises(NotImplementedError, match="no word Prover9 reads"):
        generate_prover9_input_with_mapping([node], P(alpha))


def test_the_binder_of_a_sorted_quantifier_is_prepared_too():
    node = SortedQuantifier("∀", x, "S", FA(x, P(x, _X0)))
    text = node.to_prover9()
    assert _binder_names_in_scope_twice(text) == []
    assert text == "(all X (S(X) -> (all X1 P(X1, x0))))"


def test_a_formula_with_no_re_bound_binder_is_written_exactly_as_before():
    assert FA(x, P(x, alpha)).to_prover9() == "(all X P(X, alpha))"
    assert And(FA(x, P(x)), Not(EX(y, Atom("Q", [y])))).to_prover9() == "((all X P(X)) & -((exists Y Q(Y))))"
    assert Implies(P(alpha), Or(P(beta), Xor(P(alpha), P(beta)))).to_prover9() == \
        "(P(alpha) -> (P(beta) | ((P(alpha) | P(beta)) & -((P(alpha)) & (P(beta))))))"
    assert Contrast(P(alpha), Iff(P(beta), P(alpha))).to_prover9() == "(P(alpha) & (P(beta) <-> P(alpha)))"


# --------------------------------------------------------------------------- #
# The counting witnesses.
# --------------------------------------------------------------------------- #

def test_a_witness_is_not_a_variable_of_the_formula_that_differs_only_in_case():
    node = FA(Variable("X0"), Count("ge", Number(2), x, R(x, Variable("X0"))))
    text = node.to_prover9()
    assert text == "(all X0 (exists X1 (exists X2 ((R(X1, X0) & R(X2, X0)) & (X1 != X2)))))"
    assert _binder_names_in_scope_twice(text) == []


def test_a_free_variable_of_the_counted_formula_is_not_captured_by_a_witness():
    # the free variable X0 of the matrix: the witnesses are X1 and X2
    node = Count("ge", Number(2), x, R(x, Variable("X0")))
    assert node.to_prover9() == "(exists X1 (exists X2 ((R(X1, X0) & R(X2, X0)) & (X1 != X2))))"
    # the same with the variable in lower case: a witness x0 would be X0 in the text
    node = Count("ge", Number(2), x, R(x, Variable("x0")))
    assert node.to_prover9() == "(exists X1 (exists X2 ((R(X1, X0) & R(X2, X0)) & (X1 != X2))))"


def test_a_sorted_count_is_prepared_with_the_names_of_the_whole_formula():
    node = SortedQuantifier("∀", Variable("X1"), "S", SortedCount("ge", Number(2), x, "S", R(x, Variable("X1"))))
    text = node.to_prover9()
    assert _binder_names_in_scope_twice(text) == []
    assert "X1" in text and text.count("exists") == 2


def test_the_counting_witnesses_of_two_counts_in_one_formula_are_not_one_variable():
    node = And(Count("ge", Number(2), x, P(x)), Count("ge", Number(2), x, Atom("Q", [x])))
    text = node.to_prover9()
    # every name that is minted is added to the names to avoid, so the second count gets other witnesses
    # than the first (as in the problem writer), not that it would have to: each has its own scope
    assert text == ("((exists X0 (exists X1 ((P(X0) & P(X1)) & (X0 != X1)))) & "
                    "(exists X2 (exists X3 ((Q(X2) & Q(X3)) & (X2 != X3)))))")


# --------------------------------------------------------------------------- #
# One implementation: the single renderer and the problem writer write the same text.
# --------------------------------------------------------------------------- #

_VARIABLES = ["x", "y", "x0"]
_CONSTANTS = ["a", "b", "d1", "c2"]      # no x<k> or y<k>: the writer renames those, a single node leaves them
_PREDICATES = [("P", 1), ("Q", 2), ("R", 1)]    # one arity each: the writer renames a second arity, a single node cannot


def _random_term(rng, scope):
    if scope and rng.random() < 0.6:
        return Variable(rng.choice(scope))
    return Constant(rng.choice(_CONSTANTS))


def _random_formula(rng, depth, scope):
    roll = rng.random()
    if depth <= 0 or roll < 0.2:
        name, arity = rng.choice(_PREDICATES)
        return Atom(name, [_random_term(rng, scope) for _ in range(arity)])
    if roll < 0.4:
        return Not(_random_formula(rng, depth - 1, scope))
    if roll < 0.65:
        return rng.choice((And, Or, Implies, Iff))(_random_formula(rng, depth - 1, scope),
                                                   _random_formula(rng, depth - 1, scope))
    name = rng.choice(_VARIABLES)
    if roll < 0.9:
        return Quantifier(rng.choice("∀∃"), Variable(name), _random_formula(rng, depth - 1, scope + [name]))
    return Count(rng.choice(["ge", "le", "eq"]), Number(rng.randint(0, 3)), Variable(name),
                 _random_formula(rng, depth - 1, scope + [name]))


def _writer_text_of_the_premise(node):
    text, _ = generate_prover9_input_with_mapping([node], Atom("Goal", []))
    lines = [line.strip() for line in text.splitlines()]
    return lines[lines.index("formulas(assumptions).") + 1].rstrip(".")


def _re_binds(node, enclosing=frozenset()):
    """Whether a formula binds a name inside the scope of a binder of the same name (names as Prover9 reads them)."""
    if isinstance(node, (Quantifier, Count)):
        name = node.variable.name.upper()
        return name in enclosing or _re_binds(node.formula, enclosing | {name})
    return any(_re_binds(child, enclosing) for child in node._child_nodes())


def test_the_single_renderer_and_the_problem_writer_write_the_same_text_for_a_closed_formula():
    rng = random.Random(20261105)
    compared = re_bound = counted = 0
    for _ in range(600):
        node = _random_formula(rng, rng.randint(2, 5), [])
        text = node.to_prover9()
        assert text == _writer_text_of_the_premise(node), node.to_unicode_str()
        compared += 1
        re_bound += _re_binds(node)
        counted += any(isinstance(n, Count) for n in node.walk())
        assert _binder_names_in_scope_twice(text) == [], text
    # the generator really meets re-bound binders and counting quantifiers
    assert compared == 600 and re_bound > 100 and counted > 50


# --------------------------------------------------------------------------- #
# The preparation runs once, for the outermost call.
# --------------------------------------------------------------------------- #

def test_the_preparation_runs_once_for_the_outermost_call_and_not_for_the_nodes_nested_in_it(monkeypatch):
    calls = []
    original = _fol_nodes._prover9_prepared

    def counting(node):
        calls.append(type(node).__name__)
        return original(node)

    monkeypatch.setattr(_fol_nodes, "_prover9_prepared", counting)
    node = FA(w, And(FA(w, P(w, _X0)), Not(EX(x, And(R(x, w), FA(x, P(x)))))))
    text = node.to_prover9()
    assert calls == ["Quantifier"] and _binder_names_in_scope_twice(text) == []
    calls.clear()
    P(alpha).to_prover9()
    Not(P(alpha)).to_prover9()
    assert calls == ["Not"]               # an atom is no entry; a formula with no binder is returned as it is


def test_the_method_is_still_a_function_of_the_node_on_the_class_and_keeps_its_documentation():
    node = FA(x, P(x))
    assert Quantifier.to_prover9(node) == node.to_prover9() == "(all X P(X))"
    assert "fresh variable" in " ".join((Quantifier.to_prover9.__doc__ or "").split())
    assert "witnesses" in " ".join((Count.to_prover9.__doc__ or "").split())
    assert "fresh variable" in " ".join((node.to_prover9.__doc__ or "").split())      # on the instance, too


def test_two_threads_render_two_formulas_at_once_without_one_seeing_the_other():
    results = {}

    def render(key, node):
        results[key] = [node.to_prover9() for _ in range(50)]

    first = FA(w, FA(w, P(w, _X0)))
    second = Count("ge", Number(2), x, R(x, Variable("X0")))
    threads = [threading.Thread(target=render, args=("a", first)), threading.Thread(target=render, args=("b", second))]
    for thread in threads:
        thread.start()
    for thread in threads:
        thread.join()
    assert set(results["a"]) == {"(all W (all W0 P(W0, x0)))"}
    assert set(results["b"]) == {"(exists X1 (exists X2 ((R(X1, X0) & R(X2, X0)) & (X1 != X2))))"}


def test_a_formula_nested_deeper_than_a_few_hundred_levels_with_no_re_binding_is_written_as_deep_as_before():
    node = P(alpha)
    for index in range(400):
        node = Not(node)
    assert node.to_prover9().count("-(") == 400
    node = P(alpha)
    for index in range(150):
        node = And(P(alpha), Not(node))
    assert node.to_prover9().count("&") == 150


def test_a_deep_chain_of_re_bound_binders_is_prepared():
    node = P(w, _X0)
    for _ in range(120):
        node = FA(w, node)
    text = node.to_prover9()
    assert _binder_names_in_scope_twice(text) == [] and text.count("(all ") == 120


# --------------------------------------------------------------------------- #
# The renaming is the definition: alpha-conversion by substitution, outermost binder first.
# --------------------------------------------------------------------------- #

def _renaming_by_substitution(node, avoid, scope=frozenset()):
    """The definition of the renaming, written the plain way: a binder inside the scope of a binder of its
    own name (names compared in upper case) is given a fresh variable and the body is renamed by substitution,
    then the body is read the same way. Recursive and eager, which is why it is the oracle and not the code."""
    from unicode_logic_kit.fol._identifiers import fresh_variables
    from unicode_logic_kit.fol._msfl_nodes import _rename
    if isinstance(node, Quantifier):
        variable, body = node.variable, node.formula
        if variable.name.upper() in scope:
            first = variable.name[:1].lower()
            letter = first if first.isascii() and first.isalpha() else "x"
            fresh = Variable(fresh_variables(1, letter=letter, avoid=avoid)[0])
            avoid.add(fresh.name.casefold())
            body = _rename(body, variable, fresh)
            variable = fresh
        return Quantifier(node.type, variable,
                          _renaming_by_substitution(body, avoid, scope | {variable.name.upper()}))
    return node.map_children(lambda child: _renaming_by_substitution(child, avoid, scope))


def test_the_renaming_of_the_code_is_the_renaming_by_substitution():
    from unicode_logic_kit.atp.prover9_entailment import _rename_rebound_binders
    from unicode_logic_kit.fol._identifiers import symbol_names
    rng = random.Random(20261106)
    names = ["x", "y", "w", "X", "W", "x0", "y1", "xa"]

    def formula(depth, scope):
        roll = rng.random()
        if depth <= 0 or roll < 0.2:
            terms = [Variable(rng.choice(scope)) if scope and rng.random() < 0.7 else Constant(rng.choice(["a", "x0", "w0"]))
                     for _ in range(rng.randint(1, 2))]
            return Atom(rng.choice(["P", "R"]), terms)
        if roll < 0.35:
            return Not(formula(depth - 1, scope))
        if roll < 0.6:
            return rng.choice((And, Or, Implies))(formula(depth - 1, scope), formula(depth - 1, scope))
        name = rng.choice(names)
        return Quantifier(rng.choice("∀∃"), Variable(name), formula(depth - 1, scope + [name]))

    changed = 0
    for _ in range(800):
        node = formula(rng.randint(2, 6), [])
        seeded = frozenset(rng.sample(["X", "Y", "W0"], rng.randint(0, 2)))
        first, second = set(symbol_names(node, fold=str.casefold)), set(symbol_names(node, fold=str.casefold))
        got = _rename_rebound_binders(node, first, seeded)
        want = _renaming_by_substitution(node, second, seeded)
        assert got == want, (node.to_unicode_str(), sorted(seeded))
        assert first == second
        changed += got != node
    assert changed > 200


def test_a_chain_of_thousands_of_re_bound_binders_is_renamed_without_the_recursion_limit():
    from unicode_logic_kit.atp.prover9_entailment import _rename_rebound_binders
    from unicode_logic_kit.fol._identifiers import symbol_names
    node = P(w, _X0)
    for _ in range(3000):
        node = FA(w, And(Atom("Q", [w]), node))
    renamed = _rename_rebound_binders(node, set(symbol_names(node, fold=str.casefold)))
    binders = []
    while isinstance(renamed, Quantifier):
        binders.append(renamed.variable.name)
        renamed = renamed.formula.right
    assert len(binders) == 3000 and len(set(binders)) == 3000 and binders[0] == "w"


# --------------------------------------------------------------------------- #
# The MCP tool and the command line call the same method.
# --------------------------------------------------------------------------- #

def test_the_mcp_render_tool_writes_a_re_bound_binder_under_a_fresh_variable():
    from unicode_logic_kit.mcp import server
    rendered = server.render("![W]: ![W]: p(W, x0)", to="prover9", dialect="tptp_bare")
    assert rendered["ok"] is True
    assert rendered["rendered"] == "(all W (all W0 P(W0, x0)))"


# --------------------------------------------------------------------------- #
# Against the real Prover9.
# --------------------------------------------------------------------------- #

_BINARY = Prover9Backend._binary()
live = pytest.mark.skipif(
    _BINARY is None,
    reason="no Prover9 binary: set $UFK_PROVER9 (a path inside WSL with $UFK_PROVER9_WSL=1) or "
           "put 'prover9' on PATH; the offline tests above carry the claim")


def _file(premises, goal):
    return ("set(prolog_style_variables).\nclear(print_initial_clauses).\nclear(print_kept).\nclear(print_given).\n"
            "formulas(assumptions).\n" + "".join(f"  {p}.\n" for p in premises)
            + "end_of_list.\nformulas(goals).\n  " + goal + ".\nend_of_list.\n")


def _proved(text):
    return _run_prover9(text, _BINARY, timeout=30, raise_on_rejection=True,
                        use_wsl=os.environ.get("UFK_PROVER9_WSL") == "1")


@live
def test_live_the_single_rendered_re_bound_binder_does_not_entail_what_the_formula_does_not():
    premise = FA(w, FA(w, P(w, _X0))).to_prover9()
    # universe {0, 1}, x0 = 0, alpha = 1, P = {(0, 0), (1, 0)}: the premise holds, P(alpha, alpha) does not
    assert _proved(_file([premise], P(alpha, alpha).to_prover9())) is False
    # the instance the premise does say
    assert _proved(_file([premise], P(alpha, _X0).to_prover9())) is True


@live
def test_live_a_free_variable_and_a_binder_of_one_name_do_not_capture_a_constant():
    # Prover9 closes Q(W, x0) & (all W P(W, x0)) universally and renames the inner W to x0 (measured: the text
    # with the capture proves P(alpha, alpha)), which is the constant x0 here. The node does not entail it
    # (universe {0, 1}, x0 = 0, alpha = 1, Q everything, P = {(0, 0), (1, 0)}); its text must not either.
    node = And(Atom("Q", [w, _X0]), FA(w, P(w, _X0)))
    assert node.to_prover9() == "(Q(W, x0) & (all W0 P(W0, x0)))"
    assert _proved(_file([node.to_prover9()], P(alpha, alpha).to_prover9())) is False
    assert _proved(_file(["(Q(W, x0) & (all W P(W, x0)))"], P(alpha, alpha).to_prover9())) is True    # the capture


@live
def test_live_the_single_rendered_counting_quantifier_does_not_entail_what_the_formula_does_not():
    aa, bb = Constant("aa"), Constant("bb")
    premises = [R(aa, aa).to_prover9(), R(bb, aa).to_prover9(), Not(Atom("=", [aa, bb])).to_prover9()]
    goal = FA(Variable("X0"), Count("ge", Number(2), x, R(x, Variable("X0")))).to_prover9()
    # universe {0, 1, 2}, aa = 0, bb = 1, R = {(0, 0), (1, 0)}: element 1 has no R-predecessor
    assert _proved(_file(premises, goal)) is False
    # the valid instance: aa has the predecessors aa and bb
    assert _proved(_file(premises, Count("ge", Number(2), x, R(x, aa)).to_prover9())) is True
