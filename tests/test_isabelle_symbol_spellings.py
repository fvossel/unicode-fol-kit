r"""An Isabelle theory keeps a binder and a free axiom variable apart from the user's symbols.

In Isabelle a name declared by ``consts`` is a constant inside a term, a ``\<lambda>`` or ``\<forall>``
binder of the same name SHADOWS it in its scope, and a free variable of an ``axiomatization``
is generalised only if no constant of that name is declared. So, read as text:

* ``∀x P(x, c)`` with the constant ``c`` spelled ``x`` must not be written ``(\<forall> x. (p x x))``:
  that is ``∀x P(x, x)``, a different sentence.
* ``const_dom: "existsAt x w"`` states that EVERY object exists at every world. With
  ``consts x :: "e"`` declared it states that the one constant ``x`` does; the constant-domain
  regime is no longer stated, and a theorem of it (the Barcan formula) loses its proof.
* ``sort_member0: "human w w"`` with ``consts w :: "e"`` is ill-typed (``w`` is the world).

The theory is only TEXT here (no Isabelle is run). Each test reads the text the way Isabelle does
and compares the names that a binder or a free axiom variable has with the declared constants.
"""

import re

from unicode_fol_kit.fol.nodes import (
    Always, And, At, Atom, Believes, Box, Constant, Diamond, Eventually, Function, Historically,
    Implies, Knows, Next, Nominal, Obligatory, Once, Permitted, Previous, Quantifier, Says, Since,
    SortedConstant, SortedQuantifier, Until, Variable, Wants,
)
from unicode_fol_kit.hol import isabelle_modal
from unicode_fol_kit.hol.classical import to_isabelle_fol, to_isabelle_msfol
from unicode_fol_kit.hol.isabelle_modal import to_isabelle_modal

_MACRO = re.compile(r"\\<[A-Za-z^]+>")


def forall(var, body):
    return Quantifier("∀", Variable(var), body)


def exists(var, body):
    return Quantifier("∃", Variable(var), body)


def P(*terms):
    return Atom("P", list(terms))


def declared(text):
    """The names ``consts`` declares."""
    return re.findall(r"^consts (\w+) ::", text, re.M)


def user_declared(text):
    """The declared names that are the user's: not the relations and operators of the embedding."""
    return set(declared(text)) - isabelle_modal._RESERVED


def bound_names(text):
    r"""The names bound by ``\<lambda>``, ``\<forall>`` and ``\<exists>`` in the goal of the theory."""
    goal = "\n".join(line for line in text.splitlines()
                     if line.startswith(("lemma", "  using", "  by")))
    return (re.findall(r"\\<lambda>(\w+)\.", goal)
            + re.findall(r"\\<(?:forall|exists)> (\w+)\.", goal))


def one_letter_names(line):
    return set(re.findall(r"\b[a-z]\b", _MACRO.sub(" ", line)))


def axiom_letters(text):
    """The one-letter names the ``axiomatization`` lines mention."""
    letters = set()
    for line in text.splitlines():
        if line.startswith("axiomatization"):
            letters |= one_letter_names(line)
    return letters


def fixed_letters(text):
    """The one-letter names of every axiom and of every introduction rule of an inductive predicate."""
    letters = axiom_letters(text)
    for line in text.splitlines():
        if line.startswith(("inductive", "  for ", "  muntil_", "| muntil_", "  msince_",
                            "| msince_")):
            letters |= one_letter_names(line)
    return letters


# --------------------------------------------------------------------------- #
# the modal theory
# --------------------------------------------------------------------------- #

def test_a_binder_is_not_spelled_like_a_constant_of_the_modal_theory():
    # ∀x P(x, c) with the constant c spelled x, inside □
    thy = to_isabelle_modal(Box(forall("x", P(Variable("x"), Constant("x")))))
    match = re.search(r"\(\\<lambda>(\w+)\. \(p (\w+) (\w+)\)\)", thy)
    assert match, thy
    binder, first, second = match.groups()
    assert first == binder                                # the first argument is the variable
    assert second in declared(thy) and second != binder   # the second is the constant, not captured
    assert not set(bound_names(thy)) & set(declared(thy))


def test_a_predicate_or_a_function_spelled_like_a_variable_is_not_captured_either():
    # the predicate P is ``p``; the variable is ``p``: ∀p P(p)
    thy = to_isabelle_modal(Box(forall("p", P(Variable("p")))))
    assert not set(bound_names(thy)) & set(declared(thy))
    # a function spelled f next to the variable f: ∀f P(f, f(k))
    thy = to_isabelle_modal(Box(forall("f", P(Variable("f"), Function("f", [Constant("k")])))))
    assert not set(bound_names(thy)) & set(declared(thy))


def test_the_free_variable_of_the_domain_axiom_is_not_a_declared_constant():
    # (◇∃y P(y) → ∃y ◇P(y)) ∧ (Q(c) → Q(c)) with the constant c spelled x, constant domains
    barcan = Implies(Diamond(exists("y", P(Variable("y")))),
                     exists("y", Diamond(P(Variable("y")))))
    formula = And(barcan, Implies(Atom("Q", [Constant("x")]), Atom("Q", [Constant("x")])))
    thy = to_isabelle_modal(formula, mode="constant")
    assert any("const_dom" in line for line in thy.splitlines())
    assert "x" in axiom_letters(thy)                      # the line does say existsAt x w
    assert not axiom_letters(thy) & user_declared(thy)


def test_a_sort_fact_names_the_world_and_the_constant_apart():
    # □Human(w:Human): the sorted constant is spelled w, and so is the world of the facts
    thy = to_isabelle_modal(Box(Atom("Human", [SortedConstant("w", "Human")])))
    assert not axiom_letters(thy) & user_declared(thy)
    member = re.search(r'sort_member0: "(\w+) (\w+) w"', thy)
    assert member and member.group(2) in declared(thy) and member.group(2) != "w"
    assert re.search(r'consts (\w+) :: "e"', thy).group(1) == member.group(2)


def test_the_world_binder_of_an_at_is_anonymous_so_a_variable_called_w_is_not_captured():
    # ∀w @i P(w): the object variable w is bound OUTSIDE the @; a named world binder
    # ``\<lambda>w.`` around the body would capture it
    thy = to_isabelle_modal(forall("w", At("ii", P(Variable("w")))))
    assert re.search(r"\(\\<lambda>_\. \(p w\) nom_\w+\)", thy), thy
    assert "\\<lambda>w. (p w)" not in thy


def test_a_binder_never_has_the_name_of_a_lifted_operator():
    thy = to_isabelle_modal(Box(forall("mnot", P(Variable("mnot")))))
    binder = re.search(r"\(mforall \(\\<lambda>(\w+)\.", thy).group(1)
    assert binder not in {n for n in isabelle_modal._RESERVED if len(n) > 2}


def test_symbols_that_no_axiom_reads_keep_their_natural_spelling():
    # a formula without a modality, quantifier or sort has no axiom: ``a`` and ``w`` stay
    thy = to_isabelle_modal(Atom("P", [Constant("a"), Constant("w")]))
    assert {"a", "w"} <= set(declared(thy))
    # and the usual variable x of a quantifier is still ``x``
    thy = to_isabelle_modal(Box(forall("x", P(Variable("x")))))
    assert bound_names(thy) == ["x"]


def test_every_user_symbol_spelled_like_an_axiom_variable_gets_another_name():
    # six constants spelled like the free variables of the axioms of the theory that
    # contains them: the frame, the agent relation, the domain regime and the until
    # introduction rules all mention one-letter names
    names = ["a", "u", "v", "w", "x", "z"]
    args = [Constant(name) for name in names]
    formula = And(Knows(Constant("a"), Atom("Q", args[1:])),
                  And(Box(exists("y", P(Variable("y")))),
                      Until(Atom("Q", args[1:]), P(Constant("v")))))
    thy = to_isabelle_modal(formula, frame="S5", systems={"epistemic": "S5"})
    constants = re.findall(r'^consts (\w+) :: "e"$', thy, re.M)
    assert len(constants) == 6                            # the six constants are all declared
    assert not fixed_letters(thy) & user_declared(thy)
    # the theory's lines do mention a, u, v, w and x, and no constant is spelled so; ``z``
    # occurs in no line of this theory (a frame S5 has no density axiom), so it keeps its name
    assert {"a", "u", "v", "w", "x"} <= fixed_letters(thy)
    assert "z" not in fixed_letters(thy) and "z" in constants


def test_no_axiom_or_inductive_line_of_any_theory_mentions_a_declared_name_as_a_variable():
    # A formula that uses every operator, with six constants spelled like the one-letter
    # names the fixed lines are known to use, in every frame and every domain regime: no
    # one-letter name of an axiom or of an introduction rule is a name the theory declares.
    # The reservation reads the text of the axioms, so a line added to the module is covered;
    # this walks the text of the whole module's output and fails if one escapes.
    x = Variable("x")
    atom = P(Constant("cc"))
    spelled = Atom("Q", [Constant(name) for name in "auvwxz"])
    everything = And(spelled, And(Box(atom), Knows(Constant("agentone"), atom)))
    for operator in (Believes, Says, Wants):
        everything = And(everything, operator(Constant("agentone"), atom))
    for operator in (Diamond, Obligatory, Permitted, Always, Eventually, Next, Historically,
                     Once, Previous):
        everything = And(everything, operator(atom))
    everything = And(everything, And(Until(atom, atom), Since(atom, atom)))
    everything = And(everything, And(At("ii", Nominal("jj")), Quantifier("∀", x, Box(P(x)))))
    everything = And(everything, Box(Atom("Sorty", [SortedConstant("sc", "Sorty")])))
    everything = And(everything, SortedQuantifier("∀", x, "Sorty", Box(P(x))))
    seen = set()
    for frame in isabelle_modal._FRAMES:
        for mode in ("constant", "possibilist", "varying", "increasing", "decreasing"):
            thy = to_isabelle_modal(everything, mode=mode, frame=frame)
            letters = fixed_letters(thy)
            seen |= letters
            assert not letters & user_declared(thy), (frame, mode)
    assert {"w", "v", "x"} <= seen, seen                  # the scan did read the axioms


# --------------------------------------------------------------------------- #
# the classical theory (the many-sorted one is the same writer)
# --------------------------------------------------------------------------- #

def test_a_binder_is_not_spelled_like_a_constant_of_the_classical_theory():
    # ∀x P(x, c), the constant c spelled x
    for write in (to_isabelle_fol, to_isabelle_msfol):
        thy = write(forall("x", P(Variable("x"), Constant("x"))))
        match = re.search(r"\(\\<forall> (\w+)\. \(p (\w+) (\w+)\)\)", thy)
        assert match, thy
        binder, first, second = match.groups()
        assert first == binder
        assert second in declared(thy) and second != binder
        assert not set(bound_names(thy)) & set(declared(thy))


def test_a_variable_spelled_like_a_predicate_or_a_function_is_not_captured():
    for formula in (forall("p", P(Variable("p"))),                  # the predicate P is ``p``
                    forall("f", P(Variable("f"), Function("f", [Constant("k")])))):
        thy = to_isabelle_fol(formula)
        assert not set(bound_names(thy)) & set(declared(thy)), thy


def test_the_sort_facts_of_the_many_sorted_theory_do_not_capture_a_constant():
    # ∀x:S P(x, c) with a constant c spelled x: the non-emptiness fact ``∃x. s x`` binds an
    # x of its own, which must not be the constant
    formula = And(SortedQuantifier("∀", Variable("x"), "S", P(Variable("x"), Constant("x"))),
                  Atom("R", [SortedConstant("k", "S")]))
    thy = to_isabelle_msfol(formula)
    assert "\\<exists>" in thy                                   # the sort fact is there
    assert not set(bound_names(thy)) & set(declared(thy)), thy


def test_without_a_clash_the_text_is_what_it_always_was():
    thy = to_isabelle_fol(forall("x", Atom("P", [Variable("x")])))
    assert "(\\<forall> x. (p x))" in thy
