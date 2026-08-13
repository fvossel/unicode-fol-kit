"""Tests for the NXF export (atp.tptp_ncl) and the Leo-III backend (atp.leo3_backend).

The golden-text export tests are hand-checked against the verified NXF syntax
sources cited in ``atp/tptp_ncl.py``'s module docstring (Steen & Sutcliffe's
TPTP-World infrastructure paper, and the real, prover-exercised ``.p`` files
from ``github.com/TPTPWorld/NonClassicalLogic`` — most directly
``k45_branch_p.0001.p``, which is the shape every line below is checked
against) — NOT snapshots of whatever the code happens to emit.

No local Leo-III install exists on this machine (``$UFK_LEO3`` unset), so
every backend test below except the final skipped one exercises discovery
logic and the pure-Python problem-generation/error-mapping path with no
subprocess ever spawned; the final test documents and (when a real Leo-III
IS available) runs the actual integration path.
"""

import os
import subprocess

import pytest

from unicode_fol_kit.fol.nodes import (
    Atom, Not, And, Or, Implies, Iff, Box, Diamond, Knows, Quantifier, Variable,
)
from unicode_fol_kit.atp.protocol import PROVED, UNKNOWN, BackendUnavailable
from unicode_fol_kit.atp.tptp_ncl import to_tptp_ncl
from unicode_fol_kit.atp.leo3_backend import Leo3Backend

p, q = Atom("p", ()), Atom("q", ())


# ---------------------------------------------------------------------------
# Golden-text export tests
# ---------------------------------------------------------------------------

def test_k_axiom_export_in_k():
    """□(p→q)→(□p→□q) — the K distribution axiom — exported for frame K.

    Hand-derived against the module's OWN rendering rules (see
    ``atp/tptp_ncl.py::_render`` docstring), each individually checked
    against the sources:

    * the logic-spec block's 4-key shape and exact literal text
      (``$domains == $constant, $designation == $rigid, $terms == $global,
      $modalities == $modal_system_K``) is the form confirmed verbatim by
      ``LogicSpecifications/CorrectSpecifications.p``'s ``simple_s5``/
      ``quantification`` blocks (same 4 keys, same ``==``/``,``/``]``
      punctuation), with ``$modal_system_K`` in place of ``_S5`` — ``_K`` is
      the literal system name ``k45_branch_p.0001.p`` builds on
      (``$modal_system_K45``, i.e. ``K`` + axioms; ``K`` alone is the same
      family's base name).
    * one ``tff(p_decl,type,p: $o).``/``tff(q_decl,type,q: $o).`` per
      propositional letter, in first-occurrence order (p before q, matching
      the formula's own left-to-right occurrence) — the exact shape
      ``k45_branch_p.0001.p`` uses for every one of its 15 propositional
      letters (``tff(p0_decl,type, p0: $o ).``).
    * ``[.]`` applied directly to an atom needs no parens (``[.] p``); applied
      to a compound (p => q) it wraps that compound's own already-
      parenthesised rendering with no EXTRA parens, since ``(p => q)`` is
      already a self-delimited ``unary`` production — mirrors
      ``k45_branch_p.0001.p``'s ``<.> [.] y100`` (chained prefix connectives,
      no parens between them) and ``fol/tptp_input.py``'s ``?unary: "~" unary
      | ...`` grammar rule that ``[.]``/``<.>`` are confirmed to occupy the
      same slot as.
    * the classical connectives ``&``/``=>`` render exactly as
      ``Node.to_tptp`` already does for And/Implies (``(l & r)``/
      ``(l => r)``) — reused, not reinvented (see module docstring).
    """
    formula = Implies(Box(Implies(p, q)), Implies(Box(p), Box(q)))
    text = to_tptp_ncl(formula, frame="K", conjecture_name="k_axiom")

    expected = (
        "tff(k_axiom_logic,logic,\n"
        "    $modal ==\n"
        "      [ $domains == $constant,\n"
        "        $designation == $rigid,\n"
        "        $terms == $global,\n"
        "        $modalities == $modal_system_K ] ).\n"
        "\n"
        "tff(p_decl,type,\n"
        "    p: $o ).\n"
        "\n"
        "tff(q_decl,type,\n"
        "    q: $o ).\n"
        "\n"
        "tff(k_axiom,conjecture,\n"
        "    ([.] (p => q) => ([.] p => [.] q)) ).\n"
    )
    assert text == expected


def test_diamond_export_in_s4():
    """◇p exported for frame S4 — the minimal single-atom, single-operator case.

    Hand-checked: logic spec carries ``$modal_system_S4`` (the literal name
    confirmed by the infrastructure paper's system enumeration); one type
    declaration for ``p``; the conjecture body is ``<.> p`` — the diamond
    short form applied directly to an atom needs no parens, exactly as
    ``k45_branch_p.0001.p``'s ``<.> [.] y100`` applies ``<.>`` directly to a
    following prefix-op chain with no parenthesis.
    """
    text = to_tptp_ncl(Diamond(p), frame="S4", conjecture_name="poss_p")

    expected = (
        "tff(poss_p_logic,logic,\n"
        "    $modal ==\n"
        "      [ $domains == $constant,\n"
        "        $designation == $rigid,\n"
        "        $terms == $global,\n"
        "        $modalities == $modal_system_S4 ] ).\n"
        "\n"
        "tff(p_decl,type,\n"
        "    p: $o ).\n"
        "\n"
        "tff(poss_p,conjecture,\n"
        "    <.> p ).\n"
    )
    assert text == expected


@pytest.mark.parametrize("frame,system", [
    ("K", "$modal_system_K"),
    ("T", "$modal_system_T"),
    ("S4", "$modal_system_S4"),
    ("S5", "$modal_system_S5"),
])
def test_logic_spec_line_per_frame(frame, system):
    """Each of the four frames this kit's OWN modal tableau supports (K/T/S4/S5)
    maps to its literal ``$modal_system_<X>`` token, one-to-one, with no
    surprise renaming — all four names are individually confirmed present
    (as literal tokens) in ``LogicSpecifications/CorrectSpecifications.p``
    and/or ``k45_branch_p.0001.p``'s corpus of ``$modal_system_*`` uses.
    """
    text = to_tptp_ncl(Box(p), frame=frame)
    assert f"$modalities == {system} ] )." in text


def test_repeated_atom_gets_one_type_declaration():
    """p ∧ p uses the SAME propositional letter twice — the type-declaration
    loop dedupes by first occurrence, so exactly ONE ``p: $o`` statement is
    emitted, not two (a duplicate ``type`` statement for the same name is
    rejected by TPTP-family parsers as a re-declaration)."""
    text = to_tptp_ncl(And(p, p))
    assert text.count(",type,") == 1
    assert text.count("p: $o") == 1


# ---------------------------------------------------------------------------
# Error contracts
# ---------------------------------------------------------------------------

def test_unknown_frame_raises_value_error():
    with pytest.raises(ValueError, match="frame"):
        to_tptp_ncl(Box(p), frame="B")  # B is a real modal system elsewhere, but
                                         # not one this exporter is wired for


def test_unknown_domains_raises_value_error():
    with pytest.raises(ValueError, match="domains"):
        to_tptp_ncl(Box(p), domains="nonsense")


def test_quantifier_raises_not_implemented():
    """A quantified modal formula is a documented, not-yet-implemented extension
    (see module docstring 'Scope') — never silently dropped or mistranslated."""
    formula = Box(Quantifier("forall", Variable("x"), Atom("P", (Variable("x"),))))
    with pytest.raises(NotImplementedError):
        to_tptp_ncl(formula)


def test_non_alethic_modal_family_raises_not_implemented():
    """Knows_a (epistemic) is out of scope: it needs the INDEXED long-form
    connective ({$knows(#a)} @ (...), confirmed by PUZ087_1.p), not the
    unindexed short form [.]/<.> this exporter emits."""
    formula = Knows("alice", p)
    with pytest.raises(NotImplementedError):
        to_tptp_ncl(formula)


def test_non_nullary_atom_raises_not_implemented():
    """P(a) needs individual-term typing ($i/$tType) this exporter does not
    attempt yet — see module docstring 'Scope'."""
    from unicode_fol_kit.fol.nodes import Constant
    formula = Box(Atom("P", (Constant("a"),)))
    with pytest.raises(NotImplementedError):
        to_tptp_ncl(formula)


# ---------------------------------------------------------------------------
# Leo3Backend: discovery (no binary, no subprocess)
# ---------------------------------------------------------------------------

def test_leo3_unavailable_without_env_or_java(monkeypatch):
    monkeypatch.delenv("UFK_LEO3", raising=False)
    monkeypatch.setattr("shutil.which", lambda name: None)
    assert Leo3Backend().available() is False


def test_leo3_unavailable_with_env_but_no_java(monkeypatch, tmp_path):
    fake_jar = tmp_path / "leo3.jar"
    monkeypatch.setenv("UFK_LEO3", str(fake_jar))
    monkeypatch.setattr("shutil.which", lambda name: None)
    assert Leo3Backend().available() is False


def test_leo3_unavailable_with_java_but_no_env(monkeypatch):
    monkeypatch.delenv("UFK_LEO3", raising=False)
    monkeypatch.setattr("shutil.which", lambda name: "/usr/bin/java" if name == "java" else None)
    assert Leo3Backend().available() is False


def test_leo3_available_with_both(monkeypatch, tmp_path):
    fake_jar = tmp_path / "leo3.jar"
    monkeypatch.setenv("UFK_LEO3", str(fake_jar))
    monkeypatch.setattr("shutil.which", lambda name: "/usr/bin/java" if name == "java" else None)
    assert Leo3Backend().available() is True


def test_leo3_decide_raises_backend_unavailable(monkeypatch):
    """decide() re-checks discovery itself (in case it is called directly,
    bypassing atp.protocol.run_backend's own availability gate) and raises
    BackendUnavailable rather than letting a bare FileNotFoundError escape."""
    monkeypatch.delenv("UFK_LEO3", raising=False)
    with pytest.raises(BackendUnavailable):
        Leo3Backend().decide(Box(p))


def test_leo3_decide_unsupported_fragment_never_spawns_subprocess(monkeypatch, tmp_path):
    """A formula outside to_tptp_ncl's fragment (here: epistemic Knows) comes
    back UNKNOWN/unsupported WITHOUT ever calling subprocess.run — the NXF
    translation failure is caught before any process is spawned."""
    fake_jar = tmp_path / "leo3.jar"
    monkeypatch.setenv("UFK_LEO3", str(fake_jar))
    monkeypatch.setattr("shutil.which", lambda name: "/usr/bin/java" if name == "java" else None)

    def _boom(*a, **kw):
        raise AssertionError("subprocess.run must not be called for an unsupported formula")
    monkeypatch.setattr(subprocess, "run", _boom)

    verdict = Leo3Backend().decide(Knows("alice", p))
    assert verdict.status == UNKNOWN
    assert verdict.reason == "unsupported"
    assert verdict.logic == "modal"


def test_leo3_decide_no_szs_line_is_error(monkeypatch, tmp_path):
    """Output with no '% SZS status' line at all is an infrastructure surprise
    (ERROR/infra), not a decided UNKNOWN — Leo-III printed SOMETHING, just not
    in the expected form (e.g. a CLI usage error)."""
    fake_jar = tmp_path / "leo3.jar"
    monkeypatch.setenv("UFK_LEO3", str(fake_jar))
    monkeypatch.setattr("shutil.which", lambda name: "/usr/bin/java" if name == "java" else None)

    class _FakeResult:
        stdout = "usage: leo3 <file> [options]\n"
        stderr = ""
    monkeypatch.setattr(subprocess, "run", lambda *a, **kw: _FakeResult())

    verdict = Leo3Backend().decide(Box(p))
    assert verdict.status == "error"
    assert verdict.reason == "infra"
    assert "usage" in verdict.detail


def test_leo3_decide_theorem_is_proved(monkeypatch, tmp_path):
    """A canned 'SZS status Theorem' output maps to PROVED via the shared
    atp.tstp reader with query='conjecture' (the problem carries exactly one
    conjecture-role formula, never a bare clause set) — pins the wiring
    between this backend and atp.tstp without needing a real prover."""
    fake_jar = tmp_path / "leo3.jar"
    monkeypatch.setenv("UFK_LEO3", str(fake_jar))
    monkeypatch.setattr("shutil.which", lambda name: "/usr/bin/java" if name == "java" else None)

    class _FakeResult:
        stdout = "% SZS status Theorem for problem\n"
        stderr = ""
    monkeypatch.setattr(subprocess, "run", lambda *a, **kw: _FakeResult())

    verdict = Leo3Backend().decide(Implies(Box(Implies(p, q)), Implies(Box(p), Box(q))))
    assert verdict.status == PROVED
    assert verdict.szs_status == "Theorem"
    assert verdict.logic == "modal"


def test_leo3_decide_uses_jar_invocation(monkeypatch, tmp_path):
    """$UFK_LEO3 ending in .jar is invoked as `java -jar <jar> <file> -t <sec>`."""
    fake_jar = tmp_path / "leo3.jar"
    monkeypatch.setenv("UFK_LEO3", str(fake_jar))
    monkeypatch.setattr("shutil.which", lambda name: "/usr/bin/java" if name == "java" else None)

    captured = {}

    class _FakeResult:
        stdout = "% SZS status Theorem for problem\n"
        stderr = ""

    def _fake_run(command, **kw):
        captured["command"] = command
        return _FakeResult()
    monkeypatch.setattr(subprocess, "run", _fake_run)

    Leo3Backend().decide(Box(p), timeout=5000)
    command = captured["command"]
    assert command[0] == "/usr/bin/java"
    assert command[1] == "-jar"
    assert command[2] == str(fake_jar)
    assert command[4] == "-t"
    assert command[5] == "5"  # 5000ms -> 5s


def test_leo3_decide_uses_wrapper_invocation_when_not_jar(monkeypatch, tmp_path):
    """$UFK_LEO3 NOT ending in .jar is invoked directly (no `java -jar` prefix)
    — the 'executable wrapper' discovery path."""
    fake_wrapper = tmp_path / "leo3"
    monkeypatch.setenv("UFK_LEO3", str(fake_wrapper))
    monkeypatch.setattr("shutil.which", lambda name: "/usr/bin/java" if name == "java" else None)

    captured = {}

    class _FakeResult:
        stdout = "% SZS status Theorem for problem\n"
        stderr = ""

    def _fake_run(command, **kw):
        captured["command"] = command
        return _FakeResult()
    monkeypatch.setattr(subprocess, "run", _fake_run)

    Leo3Backend().decide(Box(p))
    command = captured["command"]
    assert command[0] == str(fake_wrapper)
    assert "-jar" not in command


# ---------------------------------------------------------------------------
# Live integration test: skipped unless a real Leo-III is configured.
# ---------------------------------------------------------------------------

@pytest.mark.skipif(
    not os.environ.get("UFK_LEO3"),
    reason="no local Leo-III: set $UFK_LEO3 to a leo3.jar path or wrapper to run this")
def test_leo3_live_k_axiom_is_theorem():
    """The K axiom, □(p→q)→(□p→□q), is a theorem of every normal modal logic
    (in particular K itself) — this is the canonical smoke test for an
    NXF-speaking prover's modal mode actually working end to end."""
    formula = Implies(Box(Implies(p, q)), Implies(Box(p), Box(q)))
    verdict = Leo3Backend().decide(formula, frame="K")
    assert verdict.status == PROVED, verdict.detail


def test_to_tptp_ncl_refuses_case_colliding_letters():
    """Soundness guard (found by adversarial review): Atom.to_tptp folds only
    an atom identifier's FIRST character to lower-case (not the whole
    string — see fol/_fol_nodes.py's tptp_fold_first_letter), so the
    DISTINCT kit letters 'Px' and 'px' still both render as 'px' — the
    genuinely INVALID formula Px → px would silently export as the
    tautology (px => px) and any NXF prover would 'prove' it. The export
    must refuse instead of aliasing.

    Built directly via the ``Atom`` constructor rather than
    ``MSFLParser().parse(...)``: the Unicode grammar's PREDICATE token
    forces every parsed atom name to start upper-case
    (``[A-Z][a-zA-Z0-9]*``), so two parser-produced atoms can never collide
    under a first-letter-only fold — only a directly-constructed atom name
    (as e.g. :mod:`unicode_fol_kit.chem.mol` builds, bypassing the grammar)
    can start lower-case and reproduce the collision.
    """
    from unicode_fol_kit.atp.tptp_ncl import to_tptp_ncl
    from unicode_fol_kit.fol.nodes import Atom as _Atom, Implies as _Implies

    px_upper = _Atom("Px", ())
    px_lower = _Atom("px", ())
    assert px_upper != px_lower                      # genuinely distinct atoms
    assert px_upper.to_tptp() == px_lower.to_tptp() == "px"  # both fold to 'px'
    with pytest.raises(NotImplementedError, match="alias"):
        to_tptp_ncl(_Implies(px_upper, px_lower))
