r"""The second- and third-order writers keep a constant apart from every variable, and write a
constant of any name.

A constant is a particular individual that its name stands for. A free variable is a PARAMETER of
the problem: one unknown element, the same in every formula (``fol/_free_parameters.py``). So
``P(x)`` with a free ``x`` and ``P('x')`` are two statements and ``P(x) ⊢ P('x')`` is not valid, and
``∀x P(x, 'x')`` says that ``P`` holds of every element and the element ``x``: it is not
``∀x P(x, x)``. A quoted constant makes both texts writable, so the writers must tell the two apart
in the output:

* a constant is never looked up among the bound variables: no binder, of any name, captures it;
* a free variable and a constant of one spelling are two symbols, declared one after the other,
  the variable first under the plain name and the constant under the next free one (``x`` and
  ``x_2``);
* a constant of ANY name has an identifier that the target reads as one token, and two constants
  never share one, nor does a constant share one with a variable, a function or a predicate.

The public writers are ``to_thf_to`` / ``to_isabelle_to`` (third order), ``to_thf_ho_modal`` /
``to_isabelle_ho_modal`` / ``isabelle_ho_modal_theory`` (third-order modal) and ``to_thf_so`` /
``to_isabelle_so`` (second order). Every expected text below is worked out from the definition of
the writer, by hand, and written as a literal:

* THF writers: a symbol is written as its stem, an ASCII lower word (a non-ASCII character is
  ``uXXXX`` or the name of a Greek letter, any other character that is not a letter, a digit or an
  underscore is ``_``, a ``p`` goes in front of a leading digit or underscore, the first letter is
  lower case), and two symbols with one stem get ``_2``, ``_3``, ... in the order the declarations
  are written (predicates, individuals sorted by name, functions); a bound variable is the
  upper-case stem with ``_V`` (``X_V``; second order ``X``), so it can never be spelled like a
  symbol.
* Isabelle, third order: a name that is an Isabelle identifier (an ASCII letter, then ASCII
  letters, digits, ``_`` and ``'``) is written as it is, any other name as its stem; identifiers
  claim their spelling first, then the others, each group in the order predicates, functions, free
  variables and constants (by name). A binder is written under its own name unless a declared
  symbol has that name, and then under ``name_2``.
* Isabelle, second order: every name is written as its stem.

Where a live prover is reachable the THF text is also given to Vampire, which reads THF.
"""

import os
import random
import re
import shutil
import subprocess
from typing import Callable, NamedTuple

import pytest

from unicode_logic_kit import MSFLParser
from unicode_logic_kit.atp.vampire_entailment import _spawn_vampire
from unicode_logic_kit.fol.nodes import And, Atom, Constant, Number, Variable
from unicode_logic_kit.hol._ho_common import IsabelleNames, UnsupportedHigherOrderNode, functor_stem
from unicode_logic_kit.hol.ho_modal import (
    HoAxiom, HoGoal, isabelle_ho_modal_theory, to_isabelle_ho_modal, to_thf_ho_modal,
)
from unicode_logic_kit.hol.secondorder import to_isabelle_so, to_thf_so
from unicode_logic_kit.hol.thirdorder import to_isabelle_to, to_thf_to

TO = MSFLParser(third_order=True)
TOM = MSFLParser(third_order=True, modal=True)
SO = MSFLParser(second_order=True)

#: The lexical rule of a TPTP constant (``lower_word``), of a TPTP variable, and of an Isabelle identifier.
THF_WORD = re.compile(r"[a-z][A-Za-z0-9_]*")
THF_VARIABLE = re.compile(r"[A-Z][A-Za-z0-9_]*")
ISABELLE_IDENTIFIER = re.compile(r"[A-Za-z][A-Za-z0-9_']*")


class Writer(NamedTuple):
    """One public writer and the shape of the text it writes."""

    id: str
    parser: MSFLParser
    write: Callable
    thf: bool
    preds: tuple                    # the tokens of the predicates P and Q
    decl: Callable[[str], str]      # the line that declares the individual ``tok``
    atom: Callable                  # the text of an atom: (predicate token, [argument tokens])
    conj: Callable                  # the text of a conjunction of two formulas
    goal: Callable[[str], str]      # the line that states the formula ``body``


def _thf_atom(pred, args):
    return "( " + " @ ".join([pred] + list(args)) + " )"


def _isa_atom(pred, args):
    return "(" + " ".join([pred] + list(args)) + ")"


def _type_line(tok):
    return f"thf({tok}_type, type, ( {tok} : $i ))."


def _decl_line(tok):
    return f"thf({tok}_decl, type, ( {tok} : $i ))."


def _consts_line(tok):
    return f'consts {tok} :: "i"'


WRITERS = [
    Writer("thf_to", TO, to_thf_to, True, ("p", "q"), _type_line, _thf_atom,
           lambda a, b: f"( {a} & {b} )", lambda b: f"thf(goal, conjecture, ( {b} ))."),
    Writer("isa_to", TO, to_isabelle_to, False, ("P", "Q"), _consts_line, _isa_atom,
           lambda a, b: rf"({a} \<and> {b})", lambda b: f'lemma "{b}"'),
    Writer("thf_ho_modal", TOM, to_thf_ho_modal, True, ("p", "q"), _type_line, _thf_atom,
           lambda a, b: f"( mand @ {a} @ {b} )", lambda b: f"thf(goal, conjecture, ( mvalid @ {b} ))."),
    Writer("isa_ho_modal", TOM, to_isabelle_ho_modal, False, ("P", "Q"), _consts_line, _isa_atom,
           lambda a, b: f"(mand {a} {b})", lambda b: f'theorem goal: "mvalid {b}"'),
    Writer("thf_so", SO, to_thf_so, True, ("p", "q"), _decl_line, _thf_atom,
           lambda a, b: f"( {a} & {b} )", lambda b: f"thf(goal, conjecture, ( {b} ))."),
    Writer("isa_so", SO, to_isabelle_so, False, ("p", "q"), _consts_line, _isa_atom,
           lambda a, b: rf"({a} \<and> {b})", lambda b: f'lemma "{b}"'),
]
BY_ID = {w.id: w for w in WRITERS}
IDS = [w.id for w in WRITERS]


def lines_of(writer, text):
    return writer.write(writer.parser.parse(text)).splitlines()


def quoted(name):
    """The text of the quoted constant ``name``: ``'`` is written ``\\'`` and ``\\`` is ``\\\\``."""
    return "'" + name.replace("\\", "\\\\").replace("'", "\\'") + "'"


# --------------------------------------------------------------------------- #
# ∀x P(x, 'x') is not ∀x P(x, x): no binder captures a constant
# --------------------------------------------------------------------------- #

#: writer -> (the line of ∀x P(x, kk), the line of ∀x P(x, 'x'), the declaration of the constant,
#: with the token as ``{}``)
CAPTURE = {
    # ! [X_V: $i] : ( p @ X_V @ kk ): the bound variable is X_V, the constant is the lower word x
    "thf_to": ("thf(goal, conjecture, ( ( ! [X_V: $i] : ( p @ X_V @ kk ) ) )).",
               "thf(goal, conjecture, ( ( ! [X_V: $i] : ( p @ X_V @ x ) ) )).",
               "thf({0}_type, type, ( {0} : $i ))."),
    # a binder is written under its own name unless a declared symbol has it: x is declared, so x_2
    "isa_to": (r'lemma "(\<forall>x::i. (P x kk))"',
               r'lemma "(\<forall>x_2::i. (P x_2 x))"', 'consts {0} :: "i"'),
    "thf_ho_modal": (
        "thf(goal, conjecture, ( mvalid @ ( ^ [W0: mu] : ( ! [X_V: $i] : ( ( p @ X_V @ kk ) @ W0 ) ) ) )).",
        "thf(goal, conjecture, ( mvalid @ ( ^ [W0: mu] : ( ! [X_V: $i] : ( ( p @ X_V @ x ) @ W0 ) ) ) )).",
        "thf({0}_type, type, ( {0} : $i ))."),
    "isa_ho_modal": (r'theorem goal: "mvalid (mall (\<lambda>x::i. (P x kk)))"',
                     r'theorem goal: "mvalid (mall (\<lambda>x_2::i. (P x_2 x)))"', 'consts {0} :: "i"'),
    # the second order's bound variable is the upper-case X, which the lower word x never meets
    "thf_so": ("thf(goal, conjecture, ( ( ! [X: $i] : ( p @ X @ kk ) ) )).",
               "thf(goal, conjecture, ( ( ! [X: $i] : ( p @ X @ x ) ) )).",
               "thf({0}_decl, type, ( {0} : $i ))."),
    "isa_so": (r'lemma "(\<forall>x::i. (p x kk))"',
               r'lemma "(\<forall>x_2::i. (p x_2 x))"', 'consts {0} :: "i"'),
}


@pytest.mark.parametrize("wid", IDS)
def test_a_bound_variable_does_not_capture_the_constant_of_its_spelling(wid):
    writer = BY_ID[wid]
    twin_line, quoted_line, declaration = CAPTURE[wid]
    twin = lines_of(writer, "∀x P(x, kk)")
    constant = lines_of(writer, "∀x P(x, 'x')")
    assert twin_line in twin
    assert quoted_line in constant
    assert declaration.format("kk") in twin
    assert declaration.format("x") in constant            # the constant x is a symbol of the problem


@pytest.mark.parametrize("wid", ["thf_to", "thf_ho_modal", "thf_so"])
def test_the_thf_text_of_the_quoted_constant_is_the_twin_with_one_token_replaced(wid):
    """∀x P(x, 'x') is ∀x P(x, kk) with the token x for the token kk, and nothing else changed."""
    writer = BY_ID[wid]
    twin = writer.write(writer.parser.parse("∀x P(x, kk)"))
    constant = writer.write(writer.parser.parse("∀x P(x, 'x')"))
    assert "kk" in twin and constant == twin.replace("kk", "x")


def argument_tokens(writer, text):
    """The two arguments of the atom ``P(·, ·)`` of the goal, as the text of the target writes them."""
    goal = next(line for line in text.splitlines() if line.startswith(("thf(goal", "lemma", "theorem")))
    if writer.thf:
        return re.search(r"\( [pq] @ (\S+) @ (\S+) \)", goal).groups()
    return re.search(r"\([Pp] ([^\s()]+) ([^\s()]+)\)", goal).groups()


def binders_and_symbols(writer, text):
    """``(the names the text binds, the names it declares as individuals)``."""
    if writer.thf:
        return (set(re.findall(r"[!?] \[(\w+): ", text)), set(re.findall(r"\( (\w+) : \$i \)", text)))
    return (set(re.findall(r"<(?:forall|exists|lambda)>(\w+)::", text)),
            set(re.findall(r'^consts (\S+) :: "i"$', text, re.M)))


@pytest.mark.parametrize("wid", IDS)
def test_in_the_text_the_bound_variable_and_the_constant_are_two_different_tokens(wid):
    """Read the text the way a prover does: the first argument of ∀x P(x, 'x') is the variable the
    quantifier binds, the second is the constant the text declares, and they are not one token."""
    writer = BY_ID[wid]
    text = writer.write(writer.parser.parse("∀x P(x, 'x')"))
    bound, declared = binders_and_symbols(writer, text)
    variable, constant = argument_tokens(writer, text)
    assert variable in bound and constant in declared
    assert variable != constant and not bound & declared
    if writer.thf:
        assert THF_VARIABLE.fullmatch(variable) and THF_WORD.fullmatch(constant)


def test_the_capture_check_can_fail():
    """The old text of ∀x P(x, 'x') used the bound variable for the constant."""
    writer = BY_ID["thf_to"]
    old = ("thf(p_type, type, ( p : $i > $i > $o )).\nthf(x_type, type, ( x : $i )).\n"
           "thf(goal, conjecture, ( ( ! [X_V: $i] : ( p @ X_V @ X_V ) ) )).\n")
    bound, declared = binders_and_symbols(writer, old)
    variable, constant = argument_tokens(writer, old)
    assert variable == constant and constant not in declared      # which is what the check above refuses


@pytest.mark.parametrize("wid", ["thf_to", "thf_ho_modal"])
def test_a_lambda_parameter_and_a_nested_binder_do_not_capture_a_constant(wid):
    writer = BY_ID[wid]
    inner = {"thf_to": "( pos @ ( ^ [X_V: $i] : ( g @ X_V @ x ) ) )",
             "thf_ho_modal": "( pos @ ( ^ [X_V: $i, W0: mu] : ( ( g @ X_V @ x ) @ W0 ) ) )"}[wid]
    assert writer.goal(inner) in lines_of(writer, "Pos(λx. G(x, 'x'))")
    # a second binder of one name is a second token, and the constant is the lower word still
    nested = {"thf_to": "( ! [X_V: $i] : ( ! [X_V2: $i] : ( p @ X_V2 @ x ) ) )",
              "thf_ho_modal": "( ^ [W0: mu] : ( ! [X_V: $i] : ( ( ^ [W1: mu] : ( ! [X_V2: $i] : "
                              "( ( p @ X_V2 @ x ) @ W1 ) ) ) @ W0 ) ) )"}[wid]
    assert writer.goal(nested) in lines_of(writer, "∀x ∀x P(x, 'x')")


@pytest.mark.parametrize("wid", ["isa_to", "isa_ho_modal"])
def test_an_isabelle_lambda_parameter_does_not_capture_a_constant(wid):
    writer = BY_ID[wid]
    body = r"(Pos (\<lambda>x_2::i. (G x_2 x)))"
    assert writer.goal(body) in lines_of(writer, "Pos(λx. G(x, 'x'))")


@pytest.mark.parametrize("wid", ["thf_to", "isa_to", "thf_ho_modal", "isa_ho_modal"])
def test_a_bound_predicate_variable_does_not_capture_the_constant_of_its_spelling(wid):
    writer = BY_ID[wid]
    expected = {
        "thf_to": "thf(goal, conjecture, ( ( ! [P_P: $i > $o] : ( q @ P_P @ p ) ) )).",
        "isa_to": r'lemma "(\<forall>P_2::i \<Rightarrow> bool. (Q P_2 P))"',
        "thf_ho_modal": "thf(goal, conjecture, ( mvalid @ ( ^ [W0: mu] : ( ! [P_P: $i > mu > $o] : "
                        "( ( q @ P_P @ p ) @ W0 ) ) ) )).",
        "isa_ho_modal": r'theorem goal: "mvalid (mall (\<lambda>P_2::i \<Rightarrow> sigma. (Q P_2 P)))"',
    }[wid]
    assert expected in lines_of(writer, "∀P Q(P, 'P')")


# --------------------------------------------------------------------------- #
# P(x) with a free x and P('x') are two statements: two declared symbols
# --------------------------------------------------------------------------- #

#: writer -> (the two declaration lines, in this order; the line of P(x) ∧ Q('x'); the line of
#: P('x') ∧ Q(x)). The free variable is declared first and keeps the plain name.
PAIR = {
    "thf_to": (["thf(x_type, type, ( x : $i )).", "thf(x_2_type, type, ( x_2 : $i ))."],
               "thf(goal, conjecture, ( ( ( p @ x ) & ( q @ x_2 ) ) )).",
               "thf(goal, conjecture, ( ( ( p @ x_2 ) & ( q @ x ) ) ))."),
    "isa_to": (['consts x :: "i"', 'consts x_2 :: "i"'],
               r'lemma "((P x) \<and> (Q x_2))"', r'lemma "((P x_2) \<and> (Q x))"'),
    "thf_ho_modal": (["thf(x_type, type, ( x : $i )).", "thf(x_2_type, type, ( x_2 : $i ))."],
                     "thf(goal, conjecture, ( mvalid @ ( mand @ ( p @ x ) @ ( q @ x_2 ) ) )).",
                     "thf(goal, conjecture, ( mvalid @ ( mand @ ( p @ x_2 ) @ ( q @ x ) ) ))."),
    "isa_ho_modal": (['consts x :: "i"', 'consts x_2 :: "i"'],
                     'theorem goal: "mvalid (mand (P x) (Q x_2))"',
                     'theorem goal: "mvalid (mand (P x_2) (Q x))"'),
    "thf_so": (["thf(x_decl, type, ( x : $i )).", "thf(x_2_decl, type, ( x_2 : $i ))."],
               "thf(goal, conjecture, ( ( ( p @ x ) & ( q @ x_2 ) ) )).",
               "thf(goal, conjecture, ( ( ( p @ x_2 ) & ( q @ x ) ) ))."),
    "isa_so": (['consts x :: "i"', 'consts x_2 :: "i"'],
               r'lemma "((p x) \<and> (q x_2))"', r'lemma "((p x_2) \<and> (q x))"'),
}


@pytest.mark.parametrize("wid", IDS)
def test_a_free_variable_and_a_constant_of_one_spelling_are_two_declared_symbols(wid):
    writer = BY_ID[wid]
    declarations, variable_first, constant_first = PAIR[wid]
    text = lines_of(writer, "P(x) ∧ Q('x')")
    assert [text.count(line) for line in declarations] == [1, 1]       # each once
    assert text.index(declarations[0]) < text.index(declarations[1])   # the variable first
    assert variable_first in text
    # the two keep their names whichever of them comes first in the formula
    mirror = lines_of(writer, "P('x') ∧ Q(x)")
    assert [mirror.count(line) for line in declarations] == [1, 1]
    assert constant_first in mirror


#: P(x) ∧ ∀x Q(x, 'x'): a free x, a bound x and a constant 'x' are three symbols, three tokens.
THREE = {
    "thf_to": "thf(goal, conjecture, ( ( ( p @ x ) & ( ! [X_V: $i] : ( q @ X_V @ x_2 ) ) ) )).",
    # x and x_2 are declared, so the binder is the next name, x_3
    "isa_to": r'lemma "((P x) \<and> (\<forall>x_3::i. (Q x_3 x_2)))"',
    "thf_ho_modal": "thf(goal, conjecture, ( mvalid @ ( mand @ ( p @ x ) @ ( ^ [W0: mu] : "
                    "( ! [X_V: $i] : ( ( q @ X_V @ x_2 ) @ W0 ) ) ) ) )).",
    "isa_ho_modal": r'theorem goal: "mvalid (mand (P x) (mall (\<lambda>x_3::i. (Q x_3 x_2))))"',
    "thf_so": "thf(goal, conjecture, ( ( ( p @ x ) & ( ! [X: $i] : ( q @ X @ x_2 ) ) ) )).",
    "isa_so": r'lemma "((p x) \<and> (\<forall>x_3::i. (q x_3 x_2)))"',
}


@pytest.mark.parametrize("wid", IDS)
def test_a_free_variable_a_bound_variable_and_a_constant_of_one_spelling_are_three_symbols(wid):
    assert THREE[wid] in lines_of(BY_ID[wid], "P(x) ∧ ∀x Q(x, 'x')")


def test_a_declaration_check_that_can_fail():
    """The old text declared one symbol for the two."""
    old = ["thf(x_type, type, ( x : $i )).", "thf(goal, conjecture, ( ( ( p @ x ) & ( q @ x ) ) ))."]
    assert [old.count(line) for line in PAIR["thf_to"][0]] != [1, 1]


def test_the_assumption_and_the_goal_of_one_problem_use_the_two_symbols_consistently():
    """P(x) ⊢ P('x'): the premise is about the parameter, the conclusion about the constant."""
    premise, conclusion = TO.parse("P(x)"), TO.parse("P('x')")
    thf = to_thf_to(conclusion, assumptions=[premise]).splitlines()
    assert "thf(assumption1, axiom, ( ( p @ x ) ))." in thf
    assert "thf(goal, conjecture, ( ( p @ x_2 ) ))." in thf
    isabelle = to_isabelle_to(conclusion, assumptions=[premise]).splitlines()
    assert r'axiomatization where assumption1: "(P x)"' in isabelle
    assert r'lemma "(P x_2)"' in isabelle

    premise, conclusion = TOM.parse("P(x)"), TOM.parse("P('x')")
    thf = to_thf_ho_modal(conclusion, axioms=[HoAxiom("a1", premise)]).splitlines()
    assert "thf(a1, axiom, ( mvalid @ ( p @ x ) ))." in thf
    assert "thf(goal, conjecture, ( mvalid @ ( p @ x_2 ) ))." in thf
    theory = isabelle_ho_modal_theory("T", [HoAxiom("a1", premise)], [HoGoal("g", conclusion)]).splitlines()
    assert 'axiomatization where a1: "mvalid (P x)"' in theory
    assert 'theorem g: "mvalid (P x_2)"' in theory
    assert 'consts x :: "i"' in theory and 'consts x_2 :: "i"' in theory


# --------------------------------------------------------------------------- #
# A constant of any name has an identifier of the target
# --------------------------------------------------------------------------- #

#: (name, the THF token, the Isabelle token of the third order, the Isabelle token of the second order)
SHAPES = [
    ("a", "a", "a", "a"),                                   # one letter
    ("socrates", "socrates", "socrates", "socrates"),       # a plain word is its own identifier
    ("k2", "k2", "k2", "k2"),
    ("x_1", "x_1", "x_1", "x_1"),
    ("Alice", "alice", "Alice", "alice"),                   # upper-case first: a THF constant is a lower word
    ("John Doe", "john_Doe", "john_Doe", "john_Doe"),       # a space
    ("G-910", "g_910", "g_910", "g_910"),                   # punctuation
    ("C++", "c__", "c__", "c__"),
    ("it's", "it_s", "it's", "it_s"),                       # an apostrophe: an Isabelle identifier has one
    ("2008SummerOlympics", "p2008SummerOlympics", "p2008SummerOlympics", "p2008SummerOlympics"),   # digit-led
    ("1", "p1", "p1", "p1"),                                # numeral-shaped
    ("-3", "p_3", "p_3", "p_3"),
    ("θ", "theta", "theta", "theta"),                       # non-ASCII: a Greek letter by its name
    ("świątek", "u015bwiu0105tek", "u015bwiu0105tek", "u015bwiu0105tek"),   # ś is U+015B, ą is U+0105
    ("_sk0", "p_sk0", "p_sk0", "p_sk0"),                    # an underscore first is no lower word
]


@pytest.mark.parametrize("wid", IDS)
@pytest.mark.parametrize("shape", SHAPES, ids=[s[0] for s in SHAPES])
def test_a_constant_of_any_name_is_declared_and_used_under_a_legal_identifier(wid, shape):
    name, thf_token, third_order_token, second_order_token = shape
    writer = BY_ID[wid]
    token = {"thf_to": thf_token, "thf_ho_modal": thf_token, "thf_so": thf_token,
             "isa_to": third_order_token, "isa_ho_modal": third_order_token,
             "isa_so": second_order_token}[wid]
    text = lines_of(writer, f"P({quoted(name)})")
    assert writer.decl(token) in text
    assert writer.goal(writer.atom(writer.preds[0], [token])) in text
    # the rule of the target, written out here and not read from the kit
    assert (THF_WORD if writer.thf else ISABELLE_IDENTIFIER).fullmatch(token)


@pytest.mark.parametrize("wid", IDS)
def test_a_plain_word_is_written_as_before_next_to_a_variable_of_another_spelling(wid):
    """The declarations are in the order of the sorted names: the constant socrates, then the variable x."""
    writer = BY_ID[wid]
    text = lines_of(writer, "P(socrates, x)")
    assert writer.goal(writer.atom(writer.preds[0], ["socrates", "x"])) in text
    assert text.index(writer.decl("socrates")) < text.index(writer.decl("x"))
    assert text.count(writer.decl("x")) == 1


# --------------------------------------------------------------------------- #
# Two symbols never share an identifier
# --------------------------------------------------------------------------- #

#: the text, and the tokens of its two individuals in the order the formula names them, per writer.
#: 'a b' and a_b have one stem; 'Alice' and alice one lower word; '1' and p1 one stem; 'G-910'
#: and G910 do not collide (the stems keep the punctuation as an underscore).
INJECTIVE = {
    "a b / a_b": ("P('a b') ∧ Q(a_b)", {
        # the names are claimed in sorted order: 'a b' before a_b
        "thf_to": ("a_b", "a_b_2"), "thf_ho_modal": ("a_b", "a_b_2"), "thf_so": ("a_b", "a_b_2"),
        # the identifier a_b keeps its spelling, the name with a space is the one pushed aside
        "isa_to": ("a_b_2", "a_b"), "isa_ho_modal": ("a_b_2", "a_b"), "isa_so": ("a_b", "a_b_2")}),
    "Alice / alice": ("P('Alice') ∧ Q(alice)", {
        "thf_to": ("alice", "alice_2"), "thf_ho_modal": ("alice", "alice_2"), "thf_so": ("alice", "alice_2"),
        "isa_to": ("Alice", "alice"), "isa_ho_modal": ("Alice", "alice"), "isa_so": ("alice", "alice_2")}),
    "G-910 / G910": ("P('G-910') ∧ Q('G910')", {
        "thf_to": ("g_910", "g910"), "thf_ho_modal": ("g_910", "g910"), "thf_so": ("g_910", "g910"),
        "isa_to": ("g_910", "G910"), "isa_ho_modal": ("g_910", "G910"), "isa_so": ("g_910", "g910")}),
    "1 / p1": ("P('1') ∧ Q('p1')", {
        "thf_to": ("p1", "p1_2"), "thf_ho_modal": ("p1", "p1_2"), "thf_so": ("p1", "p1_2"),
        "isa_to": ("p1_2", "p1"), "isa_ho_modal": ("p1_2", "p1"), "isa_so": ("p1", "p1_2")}),
}


@pytest.mark.parametrize("wid", IDS)
@pytest.mark.parametrize("case", sorted(INJECTIVE))
def test_two_constants_whose_names_collapse_under_a_naive_sanitiser_get_two_tokens(wid, case):
    text, tokens = INJECTIVE[case]
    first, second = tokens[wid]
    writer = BY_ID[wid]
    lines = lines_of(writer, text)
    assert first != second
    assert writer.decl(first) in lines and writer.decl(second) in lines
    both = writer.conj(writer.atom(writer.preds[0], [first]), writer.atom(writer.preds[1], [second]))
    assert writer.goal(both) in lines


#: A constant spelled like a predicate and like a function: three symbols, three tokens.
KINDS = {
    "predicate": ("P('P')", {
        "thf_to": ["thf(p_type, type, ( p : $i > $o )).", "thf(p_2_type, type, ( p_2 : $i )).",
                   "thf(goal, conjecture, ( ( p @ p_2 ) ))."],
        "isa_to": ['consts P :: "i \\<Rightarrow> bool"', 'consts P_2 :: "i"', 'lemma "(P P_2)"'],
        "thf_ho_modal": ["thf(p_type, type, ( p : $i > mu > $o )).", "thf(p_2_type, type, ( p_2 : $i )).",
                         "thf(goal, conjecture, ( mvalid @ ( p @ p_2 ) ))."],
        "isa_ho_modal": ['consts P :: "i \\<Rightarrow> sigma"', 'consts P_2 :: "i"',
                         'theorem goal: "mvalid (P P_2)"'],
        "thf_so": ["thf(p_decl, type, ( p : ( $i > $o ) )).", "thf(p_2_decl, type, ( p_2 : $i )).",
                   "thf(goal, conjecture, ( ( p @ p_2 ) ))."],
        "isa_so": ['consts p_2 :: "i"', 'consts p :: "i \\<Rightarrow> bool"', 'lemma "(p p_2)"']}),
    "function": ("P(ff(ff))", {
        "thf_to": ["thf(ff_type, type, ( ff : $i )).", "thf(ff_2_type, type, ( ff_2 : $i > $i )).",
                   "thf(goal, conjecture, ( ( p @ ( ff_2 @ ff ) ) ))."],
        "isa_to": ['consts ff_2 :: "i"', 'consts ff :: "i \\<Rightarrow> i"', 'lemma "(P (ff ff_2))"'],
        "thf_ho_modal": ["thf(ff_type, type, ( ff : $i )).", "thf(ff_2_type, type, ( ff_2 : $i > $i )).",
                         "thf(goal, conjecture, ( mvalid @ ( p @ ( ff_2 @ ff ) ) ))."],
        "isa_ho_modal": ['consts ff_2 :: "i"', 'consts ff :: "i \\<Rightarrow> i"',
                         'theorem goal: "mvalid (P (ff ff_2))"'],
        "thf_so": ["thf(ff_decl, type, ( ff : $i )).", "thf(ff_2_decl, type, ( ff_2 : ( $i > $i ) )).",
                   "thf(goal, conjecture, ( ( p @ ( ff_2 @ ff ) ) ))."],
        "isa_so": ['consts ff :: "i"', 'consts ff_2 :: "i \\<Rightarrow> i"', 'lemma "(p (ff_2 ff))"']}),
}


@pytest.mark.parametrize("wid", IDS)
@pytest.mark.parametrize("kind", sorted(KINDS))
def test_a_constant_never_shares_a_token_with_a_predicate_or_a_function(wid, kind):
    text, per_writer = KINDS[kind]
    expected = per_writer[wid]
    lines = lines_of(BY_ID[wid], text)
    for line in expected:
        assert line in lines, line
    positions = [lines.index(line) for line in expected]
    assert positions == sorted(positions)                    # declared in the order the writer states


def test_a_constant_never_takes_a_name_of_the_isabelle_embedding():
    """R is the accessibility relation, mall the lifted quantifier, Rk a relation of K_a, nom_i the
    world of the nominal i: a constant of such a name is pushed to the next free one."""
    writer = BY_ID["isa_ho_modal"]
    lines = lines_of(writer, "P('R') ∧ Q('mall') ∧ K_a P('Rk')")
    for line in ('consts R_2 :: "i"', 'consts mall_2 :: "i"', 'consts Rk_2 :: "i"'):
        assert line in lines
    assert 'theorem goal: "mvalid (mand (mand (P R_2) (Q mall_2)) (mknows a (P Rk_2)))"' in lines
    hybrid = lines_of(writer, "@i R('nom_i')")
    assert 'consts nom_i_2 :: "i"' in hybrid
    assert r'theorem goal: "mvalid (\<lambda>_. (R_2 nom_i_2) nom_i)"' in hybrid       # R_2: the predicate R too


def test_a_constant_never_takes_a_name_of_the_thf_embedding():
    """r is the accessibility relation and rk the relation of K_a; mall is nothing in THF."""
    lines = lines_of(BY_ID["thf_ho_modal"], "P('R') ∧ Q('mall') ∧ K_a P('Rk')")
    assert ("thf(goal, conjecture, ( mvalid @ ( mand @ ( mand @ ( p @ r_2 ) @ ( q @ mall ) ) @ "
            "( mknows @ a @ ( p @ rk_2 ) ) ) )).") in lines


def check_tokens(writer, text, count):
    """``text`` declares ``count`` individuals under ``count`` different tokens, each a legal
    identifier of the target, and the one atom of the goal names exactly those tokens."""
    lines = text.splitlines()
    if writer.thf:
        declared = [m.group(1) for line in lines
                    for m in [re.fullmatch(r"thf\(\w+, type, \( (\w+) : \$i \)\)\.", line)] if m]
        goal = next(line for line in lines if line.startswith("thf(goal"))
        arguments = re.search(r"\( [pq] @ (.*?) \)", goal.replace("mvalid @ ", "")).group(1).split(" @ ")
        legal = THF_WORD
    else:
        declared = re.findall(r'^consts (\S+) :: "i"$', text, re.M)
        goal = next(line for line in lines if line.startswith(("lemma", "theorem")))
        arguments = re.search(r"\([Pp] (.*?)\)", goal).group(1).split(" ")
        legal = ISABELLE_IDENTIFIER
    assert len(declared) == count and len(set(declared)) == count, declared
    assert len(arguments) == count and len(set(arguments)) == count, arguments
    assert set(declared) == set(arguments)
    assert all(legal.fullmatch(token) for token in declared), declared


@pytest.mark.parametrize("wid", IDS)
def test_many_constants_of_many_shapes_get_as_many_tokens(wid):
    names = [s[0] for s in SHAPES] + ["a b", "a_b", "alice", "G910", "p1", "John_Doe", "theta", "p_sk0", "u03b8"]
    assert len(set(names)) == len(names) == 24
    writer = BY_ID[wid]
    check_tokens(writer, writer.write(Atom("P", [Constant(n) for n in names])), 24)


@pytest.mark.parametrize("name", [3, None, ("a",)], ids=["int", "None", "tuple"])
@pytest.mark.parametrize("wid", IDS)
def test_a_constant_whose_name_is_not_a_string_is_refused_by_name(wid, name):
    writer = BY_ID[wid]
    with pytest.raises(TypeError, match="the name of a constant must be a string"):
        writer.write(Atom("P", [Constant(name)]))


def test_the_token_check_can_fail():
    """Two constants under one token, and a token the target does not read as one, are caught."""
    thf = BY_ID["thf_to"]
    isabelle = BY_ID["isa_to"]
    collapsed = ("thf(a_b_type, type, ( a_b : $i )).\nthf(a_b_type, type, ( a_b : $i )).\n"
                 "thf(goal, conjecture, ( ( p @ a_b @ a_b ) )).\n")
    with pytest.raises(AssertionError):
        check_tokens(thf, collapsed, 2)
    illegal = 'consts G-910 :: "i"\nconsts x :: "i"\nlemma "(P G-910 x)"\n'
    with pytest.raises(AssertionError):
        check_tokens(isabelle, illegal, 2)


@pytest.mark.parametrize("seed", range(6))
@pytest.mark.parametrize("wid", IDS)
def test_random_names_get_distinct_legal_identifiers(wid, seed):
    rng = random.Random(seed)
    alphabet = ["a", "B", "c", "_", "1", "'", "\\", " ", "-", "θ", "λ", "ś", "(", ",", "+", "x"]
    names = set()
    while len(names) < 12:
        names.add("".join(rng.choice(alphabet) for _ in range(rng.randint(1, 6))))
    writer = BY_ID[wid]
    check_tokens(writer, writer.write(Atom("P", [Constant(n) for n in sorted(names)])), 12)


# --------------------------------------------------------------------------- #
# A numeral and a constant spelled alike
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("wid", ["thf_to", "isa_to", "thf_ho_modal", "isa_ho_modal"])
def test_the_third_order_writers_refuse_a_numeral_by_name_and_write_the_constant_of_its_spelling(wid):
    writer = BY_ID[wid]
    with pytest.raises(UnsupportedHigherOrderNode, match="Number"):
        writer.write(writer.parser.parse("P(1) ∧ Q('1')"))
    assert writer.decl("p1") in lines_of(writer, "Q('1')")


@pytest.mark.parametrize("wid", ["thf_so", "isa_so"])
def test_the_second_order_writers_refuse_a_numeral_next_to_the_constant_of_its_spelling(wid):
    writer = BY_ID[wid]
    with pytest.raises(NotImplementedError, match=r"the number 1 and the constant '1'"):
        writer.write(writer.parser.parse("P(1) ∧ Q('1')"))
    with pytest.raises(NotImplementedError, match=r"the number 1 and the constant '1'"):
        writer.write(And(Atom("P", [Number(1)]), Atom("Q", [Constant("1")])))
    assert writer.decl("p1") in lines_of(writer, "Q('1')")          # alone, the constant has its token


@pytest.mark.parametrize("wid", ["thf_so", "isa_so"])
def test_a_free_variable_spelled_like_the_constant_of_a_numeral_is_still_refused(wid):
    writer = BY_ID[wid]
    with pytest.raises(NotImplementedError, match="free object variable 'n1'"):
        writer.write(And(Atom("P", [Variable("n1")]), Atom("Q", [Number(1)])))


# --------------------------------------------------------------------------- #
# The name helpers
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("name, stem", [
    ("socrates", "socrates"), ("Alice", "alice"), ("G-910", "g_910"), ("2008x", "p2008x"),
    ("_sk0", "p_sk0"), ("-3", "p_3"), ("θ", "theta"), ("", "p"),
])
def test_the_stem_of_a_name_is_an_ascii_lower_word(name, stem):
    assert functor_stem(name) == stem
    assert THF_WORD.fullmatch(stem)


def test_isabelle_names_give_an_identifier_its_own_spelling_before_a_name_that_sanitises_onto_it():
    names = IsabelleNames()
    names.claim([("constant", "a b"), ("constant", "a_b")])
    assert names.symbol("constant", "a_b") == "a_b" and names.symbol("constant", "a b") == "a_b_2"
    assert names.symbol("predicate", "a_b") == "a_b_3"           # a third symbol, a third name


def test_isabelle_names_keep_off_what_the_text_already_means():
    names = IsabelleNames(["True", "R"])
    assert names.symbol("constant", "True") == "True_2" and names.symbol("function", "R") == "R_2"


# --------------------------------------------------------------------------- #
# Live: Vampire reads THF
# --------------------------------------------------------------------------- #

def _vampire():
    """``(path, use_wsl)`` of a Vampire this test can run, or None."""
    path = os.environ.get("UFK_VAMPIRE") or shutil.which("vampire")
    if path:
        use_wsl = os.environ.get("UFK_VAMPIRE_WSL") == "1"
        probe = (["wsl.exe"] if use_wsl else []) + [path, "--version"]
    else:
        path, use_wsl, probe = "vampire", True, ["wsl.exe", "vampire", "--version"]
    try:
        result = subprocess.run(probe, capture_output=True, text=True, timeout=30)
    except Exception:  # noqa: BLE001 - any failure means "not available"
        return None
    return (path, use_wsl) if result.returncode == 0 and "Vampire" in result.stdout else None


_VAMPIRE = _vampire()
needs_vampire = pytest.mark.skipif(_VAMPIRE is None, reason="no Vampire reachable (PATH, $UFK_VAMPIRE, or 'wsl vampire')")


def szs_status(problem, seconds=20):
    """The SZS status Vampire prints for the THF ``problem``; ``none`` when it prints none (a
    higher-order non-theorem ends at the time limit)."""
    path, use_wsl = _VAMPIRE
    out, _timed_out = _spawn_vampire(problem, path, timeout=seconds + 30, use_wsl=use_wsl,
                                     extra_args=("-t", str(seconds)))
    assert "parse error" not in out and "User error" not in out, out[-2000:]
    match = re.search(r"SZS status (\w+)", out)
    return match.group(1) if match else "none"


def third_order_problem(premise, conclusion):
    return to_thf_to(TO.parse(conclusion), assumptions=[TO.parse(premise)])


@needs_vampire
def test_vampire_does_not_prove_p_of_alpha_alpha_from_p_of_every_element_and_the_constant_x():
    # ∀x P(x, x) would give P(alpha, alpha); ∀x P(x, 'x') says P(e, x) for every e, and alpha is not x
    assert szs_status(third_order_problem("∀x P(x, 'x')", "P(alpha, alpha)")) != "Theorem"


@needs_vampire
def test_vampire_proves_the_instance_of_the_quantifier_at_a_constant():
    assert szs_status(third_order_problem("∀x P(x, 'x')", "P(alpha, 'x')")) == "Theorem"


@needs_vampire
def test_vampire_does_not_prove_the_constant_from_the_parameter():
    assert szs_status(third_order_problem("P(x)", "P('x')")) != "Theorem"


@needs_vampire
def test_vampire_proves_a_statement_about_one_symbol_from_itself():
    assert szs_status(third_order_problem("P('x')", "P('x')")) == "Theorem"
    assert szs_status(third_order_problem("P(x)", "P(x)")) == "Theorem"


@needs_vampire
def test_vampire_does_not_prove_the_constant_from_the_parameter_in_the_modal_embedding():
    problem = to_thf_ho_modal(TOM.parse("P('x')"), axioms=[HoAxiom("a1", TOM.parse("P(x)"))])
    assert szs_status(problem) != "Theorem"
    same = to_thf_ho_modal(TOM.parse("P('x')"), axioms=[HoAxiom("a1", TOM.parse("P('x')"))])
    assert szs_status(same) == "Theorem"


@needs_vampire
def test_vampire_decides_the_second_order_pair_the_same_way():
    assert szs_status(to_thf_so(SO.parse("(∀x P(x, 'x')) → P(alpha, 'x')"))) == "Theorem"
    assert szs_status(to_thf_so(SO.parse("P(x) → P('x')"))) != "Theorem"
