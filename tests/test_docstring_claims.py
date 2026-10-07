"""Documentation claims that were true once and are not.

A doc claim is checked against the behaviour it describes, not only against its
wording, so each test below pairs the false sentence's ABSENCE with the true one's
PRESENCE and with the behaviour the true one describes.

``dl.concepts`` said a value restriction (``ObjectHasValue``, ``HasValue``)
is "the one piece of O the in-house tableau does decide" and referred to "the
tableau's value-rule". Since 0.30.0 the tableau REFUSES it by name: a value
restriction is a nominal in disguise, and an in-house value rule is unsound under
subset blocking (see "Value restrictions (ObjectHasValue)" in ``dl.tableau``).
The first-order image and the external reasoner decide it.
"""

import pathlib

import pytest

import unicode_logic_kit
import unicode_logic_kit.dl as dl
from unicode_logic_kit.dl import concepts, tableau

_SOURCE_ROOT = pathlib.Path(unicode_logic_kit.__file__).resolve().parent

#: Wordings of the false claim. Matched case-insensitively with whitespace
#: collapsed, so a re-wrapped line does not escape the check.
_FALSE_CLAIMS = (
    "the one piece of **o**",
    "the one piece of o the in-house tableau",
    "in-house tableau does decide",
    "tableau's value-rule",
    "tableau's value rule",
    "decidable in house",
    "decides in house",
    "inside the fragment the in-house tableau decides",
)


def _flat(text: str) -> str:
    return " ".join(text.split()).lower()


def test_the_tableau_refuses_a_value_restriction_by_name():
    # The behaviour the docstrings now describe: a refusal naming the construct,
    # for the bare concept and for the same concept inside a TBox.
    value = dl.HasValue("r", "a")
    with pytest.raises(dl.UnsupportedConceptError, match="ObjectHasValue"):
        dl.concept_satisfiable(value)
    with pytest.raises(dl.UnsupportedConceptError, match="ObjectHasValue"):
        dl.concept_satisfiable(dl.Atomic("A"), dl.TBox().add(dl.Atomic("A"), value))
    # ... while nnf passes it through, as the docstrings still say.
    assert dl.nnf(value) == value
    assert dl.nnf(dl.Not(value)) == dl.Not(value)


@pytest.mark.parametrize("where, text", [
    ("the dl.concepts module docstring", concepts.__doc__),
    ("the HasValue class docstring", concepts.HasValue.__doc__),
])
def test_the_concepts_docstrings_do_not_say_the_tableau_decides_a_value_restriction(where, text):
    flat = _flat(text)
    for claim in _FALSE_CLAIMS:
        assert claim not in flat, f"{where} still says {claim!r}"
    # The true statement is there instead: refused by name, a nominal in disguise,
    # decided by the FOL image and the external reasoner.
    assert "nominal in disguise" in flat, where
    assert "refuses it by name" in flat, where
    assert "dl.external_*" in text, where
    assert "kb_to_fol" in text, where


def test_the_section_the_docstrings_point_to_exists():
    assert "Value restrictions (ObjectHasValue)" in tableau.__doc__
    assert "UnsupportedConceptError" in tableau.__doc__


def test_no_source_file_claims_the_tableau_decides_a_value_restriction():
    offenders = []
    for path in sorted(_SOURCE_ROOT.rglob("*.py")):
        flat = _flat(path.read_text(encoding="utf-8", errors="replace"))
        for claim in _FALSE_CLAIMS:
            if claim in flat:
                offenders.append((path.relative_to(_SOURCE_ROOT).as_posix(), claim))
    assert not offenders, offenders


# --------------------------------------------------------------------------- #
# The TF0 route keeps its name map, so reading a prover's output back to
# kit-level names is NOT a non-goal any more.
# --------------------------------------------------------------------------- #

def test_the_tf0_writer_returns_a_real_name_map_and_it_reverses_a_renamed_symbol():
    # Behaviour first. Hand-derived: the constant θ is not TPTP-legal, so the
    # writer transliterates it to ``theta`` and records that; the predicate
    # Mortal folds its first letter to ``mortal``. A text a prover echoes from the
    # problem, ``mortal(theta)``, therefore reads ``Mortal(θ)`` in kit-level names.
    from unicode_logic_kit.atp._tptp_problem import TptpNameMap, apply_reverse_tptp
    from unicode_logic_kit.atp.tptp_tff import generate_tff_problem_with_mapping
    from unicode_logic_kit.fol.nodes import Atom, SortedConstant
    from unicode_logic_kit import MSFLParser

    premise = MSFLParser(many_sorted=True).parse("∀x:Human Mortal(x)")
    conclusion = Atom("Mortal", [SortedConstant("θ", "Human")])
    text, name_map = generate_tff_problem_with_mapping([premise], conclusion)
    assert text.startswith("tff(") and "theta" in text
    assert isinstance(name_map, TptpNameMap)
    assert name_map.term == {"θ": "theta"}
    pred_rev, term_rev = name_map.reverse_rendered()
    assert term_rev["theta"] == "θ" and pred_rev["mortal"] == "Mortal"
    # ... and the sort name is NOT in the map (documented: sorts are excluded).
    assert "human" not in term_rev and "Human" not in name_map.predicate
    assert callable(apply_reverse_tptp)


@pytest.mark.parametrize("module", ["atp/_tff_problem.py", "atp/tptp_tff.py"])
def test_no_docstring_calls_the_tf0_reverse_mapping_an_explicit_non_goal(module):
    flat = _flat((_SOURCE_ROOT / module).read_text(encoding="utf-8"))
    for stale in ("returns no mapping at all",
                  "reading its proof output back to kit-level names is an explicit non-goal",
                  "whose name_map is unconditionally none"):
        assert stale not in flat, f"{module} still says {stale!r}"
    if module == "atp/_tff_problem.py":
        # The true statement stands in its place.
        assert "generate_tff_problem_with_mapping" in flat
        assert "sort names are the one thing that route leaves out of its map" in flat
