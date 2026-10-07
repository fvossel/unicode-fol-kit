"""The distribution of the former name forwards ``unicode_fol_kit`` to ``unicode_logic_kit``.

The package was renamed in 0.31.0. ``unicode-fol-kit`` 0.31.0 (the directory
``unicode-fol-kit/`` of this repository) holds one module, which binds the old
import name to the package of the new name. Each case below runs in a fresh
interpreter, because the forwarder installs a finder and binds module names for
the whole process; the interpreter gets the directory of the forwarding
distribution on its path, which is what installing it does.

The expected values are derived by hand: the forwarder executes no code under
the old name, so every object reached through ``unicode_fol_kit`` has to BE the
object of ``unicode_logic_kit``, whichever name was imported first.
"""

import os
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
FORWARDER = ROOT / "unicode-fol-kit"


def _environment():
    env = dict(os.environ)
    inherited = [env["PYTHONPATH"]] if env.get("PYTHONPATH") else []
    env["PYTHONPATH"] = os.pathsep.join([str(FORWARDER), str(ROOT)] + inherited)
    env["PYTHONIOENCODING"] = "utf-8"
    return env


def _python(*arguments):
    """Run the interpreter with ``arguments``; stdin is empty."""
    return subprocess.run(
        [sys.executable, *arguments], env=_environment(), capture_output=True,
        stdin=subprocess.DEVNULL, timeout=300, encoding="utf-8")


def _lines(code):
    """The lines a snippet prints in a fresh interpreter."""
    done = _python("-c", code)
    assert done.returncode == 0, done.stderr
    return done.stdout.splitlines()


def test_the_old_name_is_bound_to_the_package_of_the_new_name():
    assert _lines(
        "import warnings\n"
        "warnings.simplefilter('ignore')\n"
        "import unicode_fol_kit\n"
        "import unicode_logic_kit\n"
        "print(unicode_fol_kit is unicode_logic_kit)\n"
        "print(unicode_fol_kit.__name__)\n"
        "print(unicode_fol_kit.__version__ == unicode_logic_kit.__version__)\n"
    ) == ["True", "unicode_logic_kit", "True"]


def test_the_import_warns_once_and_points_at_the_importing_line():
    # stacklevel=2 over the frames of the import system: the warning belongs to
    # the file that wrote ``import unicode_fol_kit``, here the -c string.
    assert _lines(
        "import warnings\n"
        "with warnings.catch_warnings(record=True) as caught:\n"
        "    warnings.simplefilter('always')\n"
        "    import unicode_fol_kit\n"
        "    import unicode_fol_kit.fol.nodes\n"
        "    from unicode_fol_kit import api\n"
        "ours = [w for w in caught if 'renamed to unicode_logic_kit' in str(w.message)]\n"
        "print(len(ours))\n"
        "print(ours[0].category.__name__)\n"
        "print(ours[0].filename)\n"
    ) == ["1", "DeprecationWarning", "<string>"]


@pytest.mark.parametrize("first, second", [
    ("unicode_fol_kit", "unicode_logic_kit"),
    ("unicode_logic_kit", "unicode_fol_kit"),
])
def test_a_submodule_is_one_object_under_both_names_in_either_order(first, second):
    assert _lines(
        "import sys, warnings\n"
        "warnings.simplefilter('ignore')\n"
        f"import {first}.semantics.kripke as one\n"
        f"import {second}.semantics.kripke as two\n"
        "print(one is two)\n"
        "print(sys.modules['unicode_fol_kit.semantics.kripke']\n"
        "      is sys.modules['unicode_logic_kit.semantics.kripke'])\n"
        "print(one.__name__)\n"
    ) == ["True", "True", "unicode_logic_kit.semantics.kripke"]


def test_a_class_is_one_class_under_both_names():
    # An isinstance check across the two names holds, because there is one class.
    assert _lines(
        "import warnings\n"
        "warnings.simplefilter('ignore')\n"
        "from unicode_fol_kit.fol.nodes import Constant as old\n"
        "from unicode_logic_kit.fol.nodes import Constant as new\n"
        "from unicode_fol_kit import Constant as top\n"
        "print(old is new, top is new)\n"
        "print(isinstance(old('a'), new))\n"
        "print(old.__module__.split('.')[0])\n"
    ) == ["True True", "True", "unicode_logic_kit"]


def test_no_module_is_executed_a_second_time_under_the_old_name():
    # Every module registered under an old key is the module of the new name.
    assert _lines(
        "import sys, warnings\n"
        "warnings.simplefilter('ignore')\n"
        "import unicode_fol_kit.atp.resolution\n"
        "from unicode_fol_kit.semantics import modelfinder\n"
        "old = {key: module for key, module in sys.modules.items()\n"
        "       if key.split('.')[0] == 'unicode_fol_kit'}\n"
        "print(len(old) >= 4)\n"
        "print(sorted({module.__name__.split('.')[0] for module in old.values()}))\n"
        "print(all(sys.modules['unicode_logic_kit' + key[len('unicode_fol_kit'):]] is module\n"
        "          for key, module in old.items()))\n"
    ) == ["True", "['unicode_logic_kit']", "True"]


def test_a_module_the_new_package_does_not_have_is_not_found_under_the_old_name():
    assert _lines(
        "import warnings\n"
        "warnings.simplefilter('ignore')\n"
        "try:\n"
        "    import unicode_fol_kit.no_such_module\n"
        "except ModuleNotFoundError as error:\n"
        "    print(error.name)\n"
    ) == ["unicode_fol_kit.no_such_module"]


def test_an_object_pickled_under_the_old_name_loads_as_the_same_class():
    # The pickle is written out by hand in protocol 0: the global
    # unicode_fol_kit.fol._fol_nodes.Constant applied to the tuple ('socrates',).
    assert _lines(
        "import pickle, warnings\n"
        "warnings.simplefilter('ignore')\n"
        "loaded = pickle.loads(\n"
        "    b'cunicode_fol_kit.fol._fol_nodes\\nConstant\\n(Vsocrates\\ntR.')\n"
        "from unicode_logic_kit import Constant\n"
        "print(type(loaded) is Constant)\n"
        "print(loaded == Constant('socrates'))\n"
    ) == ["True", "True"]


def test_the_command_line_runs_under_the_old_module_name():
    old = _python("-m", "unicode_fol_kit", "∀x (P(x) → Q(x))", "--to", "unicode")
    new = _python("-m", "unicode_logic_kit", "∀x (P(x) → Q(x))", "--to", "unicode")
    assert old.returncode == 0, old.stderr
    assert old.stdout.splitlines() == ["∀x (P(x) → Q(x))"]
    assert old.stdout == new.stdout


def test_a_subcommand_runs_under_the_old_module_name():
    # `prove` exits 0 for a proved conclusion.
    old = _python("-m", "unicode_fol_kit", "prove", "Q", "--premise", "P",
                  "--premise", "P → Q")
    new = _python("-m", "unicode_logic_kit", "prove", "Q", "--premise", "P",
                  "--premise", "P → Q")
    assert old.returncode == 0, old.stderr
    # The lines after the first report the backend and the wall time of the run.
    assert old.stdout.splitlines()[0] == "status: proved"
    assert new.stdout.splitlines()[0] == "status: proved"


def test_the_mcp_server_module_runs_under_the_old_module_name():
    # With stdin at end of file the server has nothing to serve. Whatever the
    # module of the new name does then (it ends, or it reports that the mcp
    # package is missing), the module of the old name does the same, and it does
    # not fail to be found.
    old = _python("-m", "unicode_fol_kit.mcp")
    new = _python("-m", "unicode_logic_kit.mcp")
    assert old.returncode == new.returncode, old.stderr
    assert "No module named unicode_fol_kit" not in old.stderr
    assert "No code object available" not in old.stderr


def test_the_forwarding_distribution_mirrors_every_extra_and_ships_only_the_forwarder():
    tomllib = pytest.importorskip("tomllib")  # Python 3.11 and later
    with open(ROOT / "pyproject.toml", "rb") as handle:
        new = tomllib.load(handle)
    with open(FORWARDER / "pyproject.toml", "rb") as handle:
        old = tomllib.load(handle)

    assert new["project"]["name"] == "unicode-logic-kit"
    assert old["project"]["name"] == "unicode-fol-kit"
    assert old["project"]["dependencies"] == ["unicode-logic-kit>=0.31.0"]

    extras = new["project"]["optional-dependencies"]
    assert old["project"]["optional-dependencies"] == {
        name: [f"unicode-logic-kit[{name}]>=0.31.0"] for name in extras}

    # The forwarder belongs to the old distribution alone. If the new wheel
    # shipped it too, upgrading unicode-fol-kit would delete it: pip installs
    # the dependency first and then removes the files of the version it replaces.
    assert new["tool"]["hatch"]["build"]["targets"]["wheel"]["packages"] == ["unicode_logic_kit"]
    assert old["tool"]["hatch"]["build"]["targets"]["wheel"]["packages"] == ["unicode_fol_kit"]
    assert sorted(path.name for path in (FORWARDER / "unicode_fol_kit").iterdir()
                  if path.name != "__pycache__") == ["__init__.py"]
