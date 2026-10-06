r"""What Mace4 reads of the file the Prover9 writer writes.

The writer's module docstring says that Mace4 reads the FORMULA LISTS of the file, not the whole of it: the
file starts with ``set(auto_denials)`` and three ``clear(print_...)`` flags that Prover9 knows and Mace4 does
not ("Fatal error: Flag not recognized", measured on Mace4 2026-8A). With those lines left out, or with only
``set(prolog_style_variables)`` before the lists, Mace4 reads the problem and finds a countermodel of an
invalid one. The kit has no Mace4 route; these tests keep the statement true. They run the real Mace4, the
one next to the Prover9 binary of ``$UFK_PROVER9`` (inside WSL with ``$UFK_PROVER9_WSL=1``), and skip, with a
reason, where there is none.

The numerals are written in double quotes because Mace4 reads a bare integer as a domain element of its own,
all of them pairwise distinct: ``1 != 2`` has no countermodel at any size it searches, while the quoted
``"1" != "2"`` is an ordinary pair of constants that may denote one element.
"""

import os
import subprocess
import tempfile

import pytest

from unicode_fol_kit.atp.prover9_entailment import _prover9_command, generate_prover9_input_with_mapping
from unicode_fol_kit.atp.protocol import Prover9Backend
from unicode_fol_kit.fol.nodes import Atom, Constant


def _mace4_path():
    prover9 = Prover9Backend._binary()
    if prover9 is None or not prover9.endswith("prover9"):
        return None
    return prover9[: -len("prover9")] + "mace4"


_MACE4 = _mace4_path()
live = pytest.mark.skipif(
    _MACE4 is None,
    reason="no Mace4 binary: it is looked for next to the Prover9 of $UFK_PROVER9 "
           "(a path inside WSL with $UFK_PROVER9_WSL=1)")


def _mace4(text):
    """``(exit code, output)`` of Mace4 on ``text``; the test is skipped where Mace4 cannot be started."""
    with tempfile.NamedTemporaryFile("w", suffix=".in", delete=False, encoding="utf-8", newline="\n") as handle:
        handle.write(text)
        path = handle.name
    try:
        command = _prover9_command(_MACE4, path, os.environ.get("UFK_PROVER9_WSL") == "1")
        run = subprocess.run(command, capture_output=True, text=True, encoding="utf-8", errors="replace",
                             stdin=subprocess.DEVNULL, timeout=120)
    finally:
        os.unlink(path)
    if run.returncode in (126, 127):
        pytest.skip("Mace4 could not be started next to the Prover9 binary")
    return run.returncode, run.stdout + run.stderr


def _writer_file(premise, conclusion):
    text, _ = generate_prover9_input_with_mapping([premise], conclusion)
    return text


def _only_the_lists(text, keep=()):
    """``text`` without the ``set`` and ``clear`` lines that Mace4 does not know (the ones in ``keep`` stay)."""
    return "\n".join(line for line in text.splitlines()
                     if not line.startswith(("set(", "clear(")) or line in keep)


_ALPHA, _BETA = Constant("alpha"), Constant("beta")


def test_the_documentation_of_the_writer_says_that_mace4_reads_the_lists_and_not_the_flags():
    from unicode_fol_kit.atp import prover9_entailment
    documentation = " ".join(prover9_entailment.__doc__.split())
    assert "Mace4, which reads the same file" not in documentation
    assert "Mace4 does not read the whole file this writer writes" in documentation
    assert "set(auto_denials)" in documentation and "Flag not recognized" in documentation


@live
def test_mace4_stops_at_the_flags_the_writer_sets_before_the_lists():
    text = _writer_file(Atom("P", [_ALPHA]), Atom("P", [_BETA]))
    code, output = _mace4(text)
    assert code == 1 and "Flag not recognized" in output
    # the flags are the cause, one at a time as well as together
    for flag in ("set(auto_denials).", "clear(print_initial_clauses).", "clear(print_kept).", "clear(print_given)."):
        code, output = _mace4(_only_the_lists(text, keep=(flag,)))
        assert code == 1 and "Flag not recognized" in output, flag


@live
def test_mace4_reads_the_formula_lists_and_finds_a_countermodel_of_an_invalid_problem():
    # P(alpha) does not entail P(beta): P = {alpha} on two elements, beta the other one
    text = _writer_file(Atom("P", [_ALPHA]), Atom("P", [_BETA]))
    for kept in ((), ("set(prolog_style_variables).",)):
        code, output = _mace4(_only_the_lists(text, keep=kept))
        assert code == 0 and output.count("interpretation(") == 1, (kept, output[-300:])


@live
def test_mace4_reads_a_bare_integer_as_a_distinct_element_and_a_quoted_one_as_a_constant():
    bound = "assign(end_size, 6).\nassign(max_seconds, 30).\n"
    bare = bound + "formulas(goals).\n  1 != 2.\nend_of_list.\n"
    quoted = bound + 'formulas(goals).\n  "1" != "2".\nend_of_list.\n'
    code, output = _mace4(bare)
    assert code == 2 and "interpretation(" not in output          # no countermodel at any size up to 6
    code, output = _mace4(quoted)
    assert code == 0 and "interpretation(" in output               # "1" and "2" may denote one element
