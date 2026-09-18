"""Aleph-specific tests for :mod:`unicode_fol_kit.ilp`.

Two kinds of check, kept separate from ``tests/test_ilp.py`` because they are
about the SECOND emission path (:meth:`IlpTask.aleph_bias_text`,
:meth:`IlpTask.aleph_examples_text`, :meth:`IlpTask.write_aleph`) rather than
the encoding checks both paths share:

* an independent-route differential check — re-parse the ``.f``/``.n`` bare
  atoms with the kit's own
  :func:`~unicode_fol_kit.fol.prolog_input.parse_prolog_program` and confirm
  the ``(example, label)`` set it reads back matches ``examples_text()``'s
  ``pos``/``neg`` content exactly. Fast, network-free, needs no Aleph
  installation. The golden-string tests for the exact bias/example TEXT
  ``aleph_bias_text()``/``aleph_examples_text()``/``write_aleph()`` emit live
  in ``tests/test_ilp.py``, next to Popper's ``bias_text()``/``write()``
  tests they mirror.
* an actual live Aleph run (:func:`test_a_real_aleph_learns_the_target_clause`
  below), SKIPPED rather than failed when no Aleph is reachable. It exists to
  answer a question the golden-string tests cannot: does Aleph's
  ``+type``/``-type`` binding actually need a declared ``example/1`` or
  ``individual/1`` type predicate to be satisfiable, or does it bind purely
  from resolving the real background predicates during saturation? Verified
  by hand against the SWI-Prolog ``aleph`` pack's ``aleph_orig.pl`` while
  building this module: the emitted ``.b``/``.f``/``.n`` triple loads and
  ``induce`` learns the intended clause with NO type facts of either kind —
  see :meth:`IlpTask.aleph_bias_text`'s docstring for why the emitter
  therefore does not emit any.
"""

import os
import re
import shutil
import subprocess

import pytest

from unicode_fol_kit.fol.nodes import Atom, Constant, Function
from unicode_fol_kit.fol.prolog_input import parse_prolog_program
from unicode_fol_kit.ilp import Example, IlpTask, to_prolog_atom
from unicode_fol_kit.semantics import FiniteStructure


# ---------------------------------------------------------------------------
# Fixtures — a small amide/acid skeleton, hand-built (independent of
# tests/test_ilp.py's own fixtures, deliberately not imported from there so
# this file's expectations are checkable on their own).
# ---------------------------------------------------------------------------

def _amide(name):
    """A molecule with a nitrogen — every individual named ``<name>_*``."""
    return FiniteStructure(
        domain=(f"{name}_c1", f"{name}_o1", f"{name}_n1"),
        extensions={
            ("c", 1): [(f"{name}_c1",)], ("o", 1): [(f"{name}_o1",)],
            ("n", 1): [(f"{name}_n1",)],
            ("bDOUBLE", 2): [(f"{name}_c1", f"{name}_o1"),
                             (f"{name}_o1", f"{name}_c1")],
            ("bSINGLE", 2): [(f"{name}_c1", f"{name}_n1"),
                             (f"{name}_n1", f"{name}_c1")],
        })


def _acid(name):
    """The same skeleton with a second oxygen where the nitrogen was — no
    ``n`` fact at all, which is exactly the property that separates the two
    classes and the property the learned clause below is checked against."""
    return FiniteStructure(
        domain=(f"{name}_c1", f"{name}_o1", f"{name}_o2"),
        extensions={
            ("c", 1): [(f"{name}_c1",)],
            ("o", 1): [(f"{name}_o1",), (f"{name}_o2",)], ("n", 1): [],
            ("bDOUBLE", 2): [(f"{name}_c1", f"{name}_o1"),
                             (f"{name}_o1", f"{name}_c1")],
            ("bSINGLE", 2): [(f"{name}_c1", f"{name}_o2"),
                             (f"{name}_o2", f"{name}_c1")],
        })


def a_task(**kwargs):
    return IlpTask(
        "amide",
        [Example("m1", _amide("m1"), True), Example("m2", _acid("m2"), False)],
        **kwargs)


def a_four_example_task():
    """Two positives, two negatives — small enough for Aleph's default search
    to finish instantly, but with more than one positive so the trivial
    single-fact "clause" (``amide(m1).``, 0 body literals) cannot cover every
    positive by itself and Aleph is forced to generalise. See the live test
    below for why one example of each label is not enough."""
    return IlpTask(
        "amide",
        [Example("m1", _amide("m1"), True), Example("m3", _amide("m3"), True),
         Example("m2", _acid("m2"), False), Example("m4", _acid("m4"), False)])


# ---------------------------------------------------------------------------
# Independent-route differential check — no Aleph needed.
# ---------------------------------------------------------------------------

def _capitalized(name):
    """Mirror ``prolog_input``'s own naming inversion for a top-level clause
    predicate — "Prolog spells a predicate lower-case ... the kit does the
    opposite" (that module's docstring) — so ``amide(m1).`` parses back as
    ``Atom("Amide", ...)``. Only the OUTERMOST predicate of a parsed clause is
    inverted this way; a compound term used as an argument (``target(m1)``
    nested inside ``pos(target(m1))``) is plain uninterpreted data and keeps
    its Prolog spelling exactly — see the two functions below, which rely on
    that asymmetry to reach the SAME example name from both files."""
    return name[:1].upper() + name[1:] if name else name


def _term_name(node):
    """The bare name of a :class:`Constant` argument — the example name,
    however it got there (a top-level :class:`Atom` argument in the ``.f``/
    ``.n`` files, or nested one level inside a :class:`Function` argument in
    ``pos(target(m1))``)."""
    assert isinstance(node, Constant), f"expected a constant, got {node!r}"
    return node.name


def _aleph_pairs(task):
    """``{(example atom, label), ...}`` read back from
    :meth:`IlpTask.aleph_examples_text` by PARSING it with
    :func:`~unicode_fol_kit.fol.parse_prolog_program` — comment-aware, so the
    trailing ``% note`` this method may append is dropped exactly as a real
    Prolog reader would drop it, never string-matched against."""
    pairs = set()
    for label in (True, False):
        for parsed in parse_prolog_program(task.aleph_examples_text(label)):
            assert isinstance(parsed, Atom), f"not a fact: {parsed!r}"
            assert parsed.predicate == _capitalized(to_prolog_atom(task.target))
            assert len(parsed.args) == 1
            pairs.add((_term_name(parsed.args[0]), label))
    return pairs


def _popper_pairs(task):
    """``{(example atom, label), ...}`` read back from
    :meth:`IlpTask.examples_text` the same way — by parsing the
    ``pos(target(e))``/``neg(target(e))`` wrapper, not by string-matching
    it. ``target(e)`` sits one argument position deep, so it comes back as an
    uninverted :class:`Function` (see :func:`_capitalized`), not an
    :class:`Atom`."""
    pairs = set()
    for parsed in parse_prolog_program(task.examples_text()):
        assert isinstance(parsed, Atom)
        assert parsed.predicate in ("Pos", "Neg")
        assert len(parsed.args) == 1
        inner = parsed.args[0]
        assert isinstance(inner, Function), f"expected a compound, got {inner!r}"
        assert inner.name == to_prolog_atom(task.target)
        assert len(inner.args) == 1
        pairs.add((_term_name(inner.args[0]), parsed.predicate == "Pos"))
    return pairs


def test_aleph_and_popper_example_files_describe_the_same_labelled_set():
    """Two independently-written renderings (:meth:`IlpTask.aleph_examples_text`
    bare-atom/.f/.n and :meth:`IlpTask.examples_text` pos()/neg()) of ONE
    :class:`IlpTask`, each re-parsed by the kit's own reader rather than
    string-compared: if they described different (example, label) sets, one
    emitter would be wrong and this catches it independently of both."""
    task = a_task()

    assert _aleph_pairs(task) == _popper_pairs(task) == {
        ("m1", True), ("m2", False)}


def test_aleph_and_popper_agree_with_notes_present_too():
    task = IlpTask("amide", [Example("m1", _amide("m1"), True, "note one"),
                             Example("m2", _acid("m2"), False, "note two")])

    assert _aleph_pairs(task) == _popper_pairs(task) == {
        ("m1", True), ("m2", False)}


# ---------------------------------------------------------------------------
# Live Aleph — skipped, not failed, when no Aleph is reachable. Never
# installs anything itself (no network access from inside a test), and never
# runs under `-n`/xdist since it shells out to a real subprocess.
# ---------------------------------------------------------------------------

_ALEPH_PROBE_GOAL = (
    "(exists_source(library(aleph_orig)) -> halt(0) ; halt(1))."
)


def _to_wsl_path(windows_path):
    """``C:\\foo\\bar`` -> ``/mnt/c/foo/bar`` — the standard WSL mount
    convention (matches ``wslpath -u`` for an ordinary drive-letter path;
    this test never sees a UNC path, so the simpler hand-rolled version is
    enough)."""
    drive, rest = os.path.splitdrive(os.path.abspath(windows_path))
    return "/mnt/" + drive[0].lower() + rest.replace("\\", "/")


def _run_swipl(kind, goal, cwd=None, timeout=20):
    """Run one SWI-Prolog ``goal`` (a full ``catch((...), E, ...)`` string,
    without the ``-g``/quoting) either ``"native"`` or through ``"wsl"``.

    Both branches end up running the EXACT same one-argv-element shape,
    ``swipl -g "<goal>" -t 'halt(1)'`` — for ``"wsl"`` handed to
    ``wsl.exe -- bash -c`` as a single string, never as several separate argv
    elements. That single-string discipline matters: Windows' own argv-to-
    command-line join (done once by :mod:`subprocess` before ``wsl.exe`` ever
    sees the parentheses in ``goal``) does not preserve shell-special
    characters across the WSL interop boundary reliably when the goal is
    passed as several argv elements — confirmed by hand while building this
    test, where the multi-argv form failed with a bash syntax error on the
    literal ``(`` before a single Prolog goal was ever reached.

    ``cwd``, if given, is a Windows path (this test's own ``tmp_path``);
    translated to its WSL mount point for the ``"wsl"`` branch, passed to
    :func:`subprocess.run` unchanged for ``"native"``.
    """
    script = f"swipl -g \"{goal}\" -t 'halt(1)'"
    if kind == "native":
        return subprocess.run(["swipl", "-g", goal, "-t", "halt(1)"], cwd=cwd,
                              capture_output=True, text=True, timeout=timeout)
    wsl_exe = shutil.which("wsl.exe") or shutil.which("wsl") or "wsl"
    if cwd is not None:
        script = f"cd '{_to_wsl_path(cwd)}' && {script}"
    return subprocess.run([wsl_exe, "--", "bash", "-c", script],
                          capture_output=True, text=True, timeout=timeout)


def _detect_aleph():
    """``"native"`` or ``"wsl"``, whichever can run SWI-Prolog with the
    classic ``aleph_orig`` library already installed — or ``None`` if
    neither can.

    Each candidate is probed once, with a short timeout, and this NEVER
    installs anything: ``pack_install`` is never called here, only an
    ALREADY-installed pack is looked for, so this stays network-free exactly
    like every other live-tool probe in this suite (``isabelle_available``,
    ``hets_available``). Tried native first, then through WSL (this kit's own
    dev host has SWI-Prolog only inside WSL)."""
    for kind in ("native", "wsl"):
        if kind == "wsl" and not (shutil.which("wsl.exe") or shutil.which("wsl")):
            continue
        try:
            result = _run_swipl(kind, _ALEPH_PROBE_GOAL)
        except (OSError, subprocess.TimeoutExpired):
            continue
        if result.returncode == 0:
            return kind
    return None


_ALEPH_KIND = _detect_aleph()


@pytest.mark.skipif(_ALEPH_KIND is None,
                    reason="no SWI-Prolog + aleph pack found (native or WSL)")
def test_a_real_aleph_learns_the_target_clause(tmp_path):
    """Write a real task with :meth:`IlpTask.write_aleph`, hand it to a real
    Aleph, and check the learned theory contains the ONE literal that
    actually separates the classes in :func:`a_four_example_task` (``n/1`` —
    every positive has a nitrogen, no negative does).

    Also the check for the batch note's open question: this task's bias
    (``aleph_bias_text()``) declares no ``example/1`` or ``individual/1``
    type fact anywhere, and Aleph is run with NOTHING added to the emitted
    ``.b`` file beyond what :meth:`IlpTask.write_aleph` itself writes. If
    Aleph's ``+type``/``-type`` annotations silently needed such facts to
    bind at all, ``induce`` would find no literals to add and would fall back
    to the trivial per-example clause covering only ONE positive — which is
    exactly what a smaller, one-positive version of this same task was
    observed to do by hand while building this test, making it a real
    (not hypothetical) failure mode to guard against.
    """
    task = a_four_example_task()
    directory = tmp_path / "amide"
    task.write_aleph(str(directory))

    goal = ("catch((consult(library(aleph_orig)), read_all(task), induce, "
            "halt), E, (print_message(error, E), halt(1)))")
    result = _run_swipl(_ALEPH_KIND, goal, cwd=str(directory), timeout=60)

    assert result.returncode == 0, (
        f"Aleph exited {result.returncode}\nstdout:\n{result.stdout}\n"
        f"stderr:\n{result.stderr}")
    assert "Accuracy = 1" in result.stdout, result.stdout
    assert re.search(r"\bn\(\s*[A-Z]\w*\s*\)", result.stdout), (
        "expected the learned theory to mention n/1 — the one predicate "
        f"separating the two classes:\n{result.stdout}")
