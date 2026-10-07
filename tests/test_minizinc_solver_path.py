"""The MiniZinc CLI is run with its own folder on ``PATH``.

MiniZinc starts its solver as a second program, and on Windows that program
loads libraries lying next to ``minizinc.exe``. A binary named only through
``$UFK_MINIZINC`` -- not installed on ``PATH`` -- then failed with
``=====ERROR=====`` and an empty error stream on the bundled default solver
(measured with MiniZinc 2.8.4 and Gecode; Chuffed worked), which the backend
reported as an infrastructure error for every problem.
"""

import os

from unicode_logic_kit.atp import minizinc_backend as mb


def test_a_bare_command_name_inherits_the_environment_unchanged():
    assert mb._environment_for("minizinc") is None


def test_a_binary_given_by_path_gets_its_folder_and_its_bin_folder_first(monkeypatch):
    monkeypatch.setenv("PATH", os.pathsep.join(["first", "second"]))
    binary = os.path.join("opt", "MiniZinc", "minizinc.exe")
    env = mb._environment_for(binary)
    folder = os.path.join("opt", "MiniZinc")
    assert env["PATH"].split(os.pathsep) == [folder, os.path.join(folder, "bin"), "first", "second"]


def test_the_rest_of_the_environment_is_the_callers(monkeypatch):
    monkeypatch.setenv("UFK_SOME_SETTING", "kept")
    env = mb._environment_for(os.path.join("opt", "MiniZinc", "minizinc"))
    assert env["UFK_SOME_SETTING"] == "kept"
    assert set(os.environ) <= set(env)


def test_the_runner_hands_that_environment_to_the_process(monkeypatch):
    seen = {}

    class _Done:
        stdout, stderr = "=====UNSATISFIABLE=====\n", ""

    def fake_run(args, **kwargs):
        seen["args"], seen["env"] = list(args), kwargs.get("env")
        return _Done()

    monkeypatch.setattr(mb.subprocess, "run", fake_run)
    binary = os.path.join("opt", "MiniZinc", "minizinc.exe")
    stdout, stderr, timed_out = mb._run_minizinc("model.mzn", binary, "gecode", 1000)
    assert (stdout, stderr, timed_out) == ("=====UNSATISFIABLE=====\n", "", False)
    assert seen["args"][0] == binary
    assert seen["env"]["PATH"].split(os.pathsep)[0] == os.path.join("opt", "MiniZinc")

    mb._run_minizinc("model.mzn", "minizinc", "gecode", 1000)
    assert seen["env"] is None
