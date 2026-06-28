"""to_english now paraphrases the non-classical operators instead of dumping glyphs.

In particular the fuzzy strong/weak/Łukasiewicz connectives are named so they do not
masquerade as their classical look-alikes, and the modal / temporal / epistemic /
deontic / second-order operators read as English. The naming-error 'mixing' hint also
has explicit modal / second-order entries.
"""

import pytest

from unicode_fol_kit.fol.nodes import (
    Atom, Box, Diamond, Knows, Believes, Obligatory, Permitted,
    Always, Eventually, Next, Until, Historically, Once, Previous, Since,
    StrongConjunction, WeakConjunction, StrongDisjunction, WeakDisjunction,
    LukNegation, LukImplication, LukEquivalence,
)
from unicode_fol_kit.fol._so_nodes import SecondOrderQuantifier
from unicode_fol_kit.fol.verbalize import to_english
from unicode_fol_kit.fol.naming import _MIXING_INFO

p, q = Atom("p", ()), Atom("q", ())


@pytest.mark.parametrize("node, fragment", [
    (Box(p), "necessarily"),
    (Diamond(p), "possibly"),
    (Knows("a", p), "knows that"),
    (Believes("a", p), "believes that"),
    (Obligatory(p), "obligatory"),
    (Permitted(p), "permitted"),
    (Always(p), "always be the case"),
    (Eventually(p), "eventually be the case"),
    (Next(p), "next moment"),
    (Until(p, q), "until"),
    (Historically(p), "has always been"),
    (Once(p), "was once the case"),
    (Previous(p), "previous moment"),
    (Since(p, q), "since"),
])
def test_modal_temporal_verbalisation(node, fragment):
    assert fragment in to_english(node)


def test_fuzzy_operators_are_distinguished_from_classical():
    # Strong vs weak vs Łukasiewicz must not read like plain "and"/"or"/"if".
    assert "strongly" in to_english(StrongConjunction(p, q))
    assert "weakly" in to_english(WeakConjunction(p, q))
    assert "strongly" in to_english(StrongDisjunction(p, q))
    assert "weakly" in to_english(WeakDisjunction(p, q))
    assert "fuzzily" in to_english(LukNegation(p))
    assert "fuzzily" in to_english(LukImplication(p, q))
    assert "fuzzily equivalent" in to_english(LukEquivalence(p, q))


def test_second_order_verbalisation():
    node = SecondOrderQuantifier("∀", "P", 1, Atom("P", [Atom("c", ())]))
    text = to_english(node)
    assert "predicate P" in text and "every" in text


def test_mixing_info_has_modal_and_so_keys():
    assert "modal" in _MIXING_INFO and "so" in _MIXING_INFO
    # The classical connective set is what the modal/so same-level group forbids mixing.
    assert _MIXING_INFO["modal"][0] == {"∧", "∨", "⊕"}
    assert _MIXING_INFO["so"][0] == {"∧", "∨", "⊕"}
