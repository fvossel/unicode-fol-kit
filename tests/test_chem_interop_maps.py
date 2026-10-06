"""The name maps of ``chem.interop`` and what their docstring says about the vocabulary.

``_build_maps`` is documented with the size of the vocabulary it maps and with the case in
which two names would collide. Both statements are checked against the code, so neither can
go stale again: the number is read out of the docstring and compared with the signature, and
the collision rule is derived from the one transformation the maps apply.
"""
import re

from unicode_fol_kit import chem
from unicode_fol_kit.chem import interop


def test_the_docstring_names_the_size_of_the_vocabulary_it_maps():
    """The vocabulary is the 40 predicates of the signature (no function or constant
    symbols), and each of them has one entry in each map."""
    signature = chem.CHEMLOG_SIGNATURE
    assert not signature.functions and not signature.constants
    assert len(chem.CHEMLOG_TO_KIT) == len(chem.KIT_TO_CHEMLOG) == len(signature.predicates)
    stated = re.findall(r"(\d+) predicates", " ".join(interop._build_maps.__doc__.split()))
    assert stated == [str(len(signature.predicates))]


def test_two_names_collide_only_when_they_differ_in_the_case_of_the_first_character():
    """The kit spelling capitalises the first character and leaves the rest alone.
    Hand-derived: ``atom`` and ``Atom`` both become ``Atom``; ``isA`` and ``isa`` become
    ``IsA`` and ``Isa``, two names. The docstring said the reverse."""
    spelling = interop._kit_spelling
    assert spelling("atom") == spelling("Atom") == "Atom"
    assert spelling("isA") == "IsA" and spelling("isa") == "Isa"
    doc = " ".join(interop._build_maps.__doc__.split())
    assert "FIRST character" in doc and "AFTER their first character" not in doc


def test_no_two_chemical_names_share_a_kit_spelling():
    names = list(chem.CHEMLOG_SIGNATURE.predicates)
    assert len({interop._kit_spelling(name) for name in names}) == len(names)
