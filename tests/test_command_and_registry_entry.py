"""The command ``unicode-logic-kit``, its ``mcp`` subcommand, and ``server.json``.

An MCP registry client starts a server of a PyPI package with ``uvx``: the runtime
arguments of the registry entry, then ``<identifier>@<version>``, then the package
arguments. ``uvx`` runs the executable that has the name of the package. So three things
have to agree, and these tests hold them together:

- the distribution declares a command of its own name (``[project.scripts]``), which is
  the command line of the package;
- ``mcp`` as the first argument of that command starts the server on stdio;
- ``server.json`` names that package, that version, the extra the server needs and that
  argument, and its name is the one the README carries for the registry.
"""

import json
import re
import sys
from pathlib import Path

import pytest

import unicode_logic_kit
from unicode_logic_kit import __main__ as command_line
from unicode_logic_kit.__main__ import main
from unicode_logic_kit.mcp import server as mcp_server

ROOT = Path(__file__).resolve().parent.parent
PYPROJECT = (ROOT / "pyproject.toml").read_text(encoding="utf-8")
ENTRY = json.loads((ROOT / "server.json").read_text(encoding="utf-8"))
PACKAGE = ENTRY["packages"][0]

HINT = ("unicode_logic_kit.mcp needs the MCP SDK: pip install 'unicode-logic-kit[mcp]' "
        "(or: pip install 'mcp>=2.0')")


def declared(key):
    """The value of ``key = "..."`` in pyproject.toml (the first one, the project table's)."""
    return re.search(rf'^{re.escape(key)} = "([^"]+)"', PYPROJECT, re.M).group(1)


# ---------------------------------------------------------------------------
# The command
# ---------------------------------------------------------------------------

def test_the_distribution_declares_a_command_of_its_own_name():
    scripts = PYPROJECT.split("[project.scripts]")[1].split("\n[")[0]
    entries = dict(re.findall(r'^([A-Za-z0-9_.-]+) = "([^"]+)"', scripts, re.M))
    assert entries == {"unicode-logic-kit": "unicode_logic_kit.__main__:main"}
    assert declared("name") == "unicode-logic-kit"
    assert command_line.main is main


class Recorder:
    """Stands for the server: records how it is run."""

    def __init__(self):
        self.runs = []

    def run(self, transport):
        self.runs.append(transport)


def test_mcp_builds_the_server_and_serves_on_stdio(monkeypatch):
    built = Recorder()
    monkeypatch.setattr(mcp_server, "create_server", lambda: built)
    assert main(["mcp"]) == 0
    assert built.runs == ["stdio"]


def test_without_the_sdk_mcp_prints_the_install_hint_and_exits_3(monkeypatch, capsys):
    # A missing package and one blocked in sys.modules raise the same ImportError.
    monkeypatch.setitem(sys.modules, "mcp", None)
    monkeypatch.setitem(sys.modules, "mcp.server", None)
    assert main(["mcp"]) == 3
    captured = capsys.readouterr()
    assert captured.out == ""
    assert captured.err == f"mcp: {HINT}\n"


def test_an_import_error_while_serving_is_not_reported_as_a_missing_sdk(monkeypatch):
    class Broken:
        def run(self, transport):
            raise ImportError("a module the running server needs")

    monkeypatch.setattr(mcp_server, "create_server", Broken)
    with pytest.raises(ImportError, match="the running server needs"):
        main(["mcp"])


def test_mcp_takes_no_further_argument(monkeypatch, capsys):
    monkeypatch.setattr(mcp_server, "create_server", Recorder)
    with pytest.raises(SystemExit) as stopped:
        main(["mcp", "extra"])
    assert stopped.value.code == 2
    assert "unrecognized arguments: extra" in capsys.readouterr().err


def test_mcp_help_names_the_server_and_the_extra(capsys):
    with pytest.raises(SystemExit) as stopped:
        main(["mcp", "--help"])
    assert stopped.value.code == 0
    text = " ".join(capsys.readouterr().out.split())
    assert "Model Context Protocol server on stdio" in text
    assert "[mcp]" in text


def test_the_other_first_arguments_go_where_they_went(monkeypatch, capsys):
    monkeypatch.setattr(mcp_server, "create_server",
                        lambda: pytest.fail("the server was started"))
    assert main(["equiv", "P → Q", "¬P ∨ Q"]) == 0
    assert "equivalent: True" in capsys.readouterr().out
    assert main(["∀x P(x)", "--to", "latex"]) == 0
    assert capsys.readouterr().out.strip() == "\\forall x\\, P(x)"


def test_the_server_reports_the_version_of_the_package():
    pytest.importorskip("mcp")
    built = mcp_server.create_server()
    assert built.name == "unicode-logic-kit"
    assert built.version == unicode_logic_kit.__version__


# ---------------------------------------------------------------------------
# server.json
# ---------------------------------------------------------------------------

def test_the_entry_has_the_name_the_readme_carries():
    readme = (ROOT / "README.md").read_text(encoding="utf-8")
    names = re.findall(r"mcp-name: (\S+)", readme)
    assert names == ["io.github.fvossel/unicode-logic-kit"]
    assert ENTRY["name"] == names[0]
    # The registry's own rule for a name: one slash between a namespace and a server name.
    assert re.fullmatch(r"[a-zA-Z0-9.-]+/[a-zA-Z0-9._-]+", ENTRY["name"])


def test_the_entry_names_this_package_at_this_version():
    version = unicode_logic_kit.__version__
    assert ENTRY["version"] == version
    assert PACKAGE["registryType"] == "pypi"
    assert PACKAGE["identifier"] == declared("name")
    assert PACKAGE["version"] == version
    assert PACKAGE["transport"] == {"type": "stdio"}
    assert len(ENTRY["packages"]) == 1


def test_the_description_fits_the_registry():
    assert 1 <= len(ENTRY["description"]) <= 100


def client_command(package):
    """The command line a registry client builds for a PyPI package.

    The runtime, its arguments (a named one as name and value), the package at its
    version, the package arguments.
    """
    args = []
    for argument in package.get("runtimeArguments", ()):
        assert argument["type"] == "named"
        args += [argument["name"], argument["value"]]
    args.append(f"{package['identifier']}@{package['version']}")
    for argument in package.get("packageArguments", ()):
        assert argument["type"] == "positional"
        args.append(argument["value"])
    return [package["runtimeHint"]] + args


def test_a_client_builds_the_command_that_starts_the_server():
    version = unicode_logic_kit.__version__
    assert client_command(PACKAGE) == [
        "uvx",
        "--python", ">=3.10",
        "--with", f"unicode-logic-kit[mcp]=={version}",
        f"unicode-logic-kit@{version}",
        "mcp",
    ]


def test_the_runtime_arguments_say_what_the_project_declares():
    # The interpreter the entry asks for is the one the package requires, and the extra it
    # asks for is an extra of the package.
    assert declared("requires-python") == ">=3.10"
    extras = PYPROJECT.split("[project.optional-dependencies]")[1].split("\n[")[0]
    assert re.search(r"^mcp = \[", extras, re.M)
