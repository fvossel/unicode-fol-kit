"""``tools/release_notes.py`` writes the text of a GitHub Release from the changelog.

The publish workflow calls it for the tag it publishes, before anything is
uploaded, so it is also the check that the tag, ``pyproject.toml`` and
``CHANGELOG.md`` describe one release. The changelogs below are written out by
hand, and so is each expected text.
"""

import importlib.util
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent

_spec = importlib.util.spec_from_file_location(
    "release_notes", ROOT / "tools" / "release_notes.py")
release_notes = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(release_notes)

PYPROJECT = (
    '[build-system]\n'
    'requires = ["hatchling"]\n'
    '\n'
    '[project]\n'
    'name = "some-kit"\n'
    'version = "0.3.0"\n'
    'authors = [\n'
    '    { name = "A. Author" },\n'
    ']\n'
    '\n'
    '[project.urls]\n'
    'version = "not this one"\n'
)

CHANGELOG = (
    "# Changelog\n"
    "\n"
    "## [0.3.0] - 2026-01-02\n"
    "\n"
    "The package has a new name.\n"
    "\n"
    "### `api` — one more verb\n"
    "\n"
    "It proves.\n"
    "\n"
    "### Fixed: a wrong verdict\n"
    "\n"
    "It was refuted.\n"
    "\n"
    "## [0.2.0] - 2025-12-01\n"
    "\n"
    "### Older heading\n"
    "\n"
    "Older text.\n"
)


def test_the_version_and_the_name_are_read_from_the_project_table_only():
    assert release_notes.declared(PYPROJECT, "version") == "0.3.0"
    assert release_notes.declared(PYPROJECT, "name") == "some-kit"


def test_a_tag_releases_the_declared_version_and_no_other():
    assert release_notes.version_of("v0.3.0", PYPROJECT) == "0.3.0"
    for tag in ("v0.2.0", "0.3.0", "v0.3.0rc1", "V0.3.0"):
        with pytest.raises(release_notes.ReleaseNotesError, match="'v0.3.0'"):
            release_notes.version_of(tag, PYPROJECT)


def test_a_section_runs_from_its_heading_to_the_next_release():
    assert release_notes.section(CHANGELOG, "0.3.0") == (
        "The package has a new name.\n"
        "\n"
        "### `api` — one more verb\n"
        "\n"
        "It proves.\n"
        "\n"
        "### Fixed: a wrong verdict\n"
        "\n"
        "It was refuted.")
    # The last section of the file runs to its end.
    assert release_notes.section(CHANGELOG, "0.2.0") == "### Older heading\n\nOlder text."


@pytest.mark.parametrize("line_end", ["\r\n", "\r"])
def test_a_section_reads_the_same_under_every_line_ending(line_end):
    converted = CHANGELOG.replace("\n", line_end)
    assert release_notes.section(converted, "0.3.0") == release_notes.section(CHANGELOG, "0.3.0")


def test_a_version_without_a_section_is_refused():
    with pytest.raises(release_notes.ReleaseNotesError, match=r"no section '## \[0.4.0\]'"):
        release_notes.section(CHANGELOG, "0.4.0")
    # 0.3 is not 0.3.0, and the dot of a version is not a wildcard.
    with pytest.raises(release_notes.ReleaseNotesError):
        release_notes.section(CHANGELOG, "0.3")
    with pytest.raises(release_notes.ReleaseNotesError):
        release_notes.section(CHANGELOG.replace("[0.3.0]", "[0x3x0]"), "0.3.0")


def test_a_short_section_is_the_release_text_as_it_stands():
    assert release_notes.notes(CHANGELOG, "0.3.0", package="some-kit",
                               repository="someone/some-kit") == (
        "The package has a new name.\n"
        "\n"
        "### `api` — one more verb\n"
        "\n"
        "It proves.\n"
        "\n"
        "### Fixed: a wrong verdict\n"
        "\n"
        "It was refuted.\n"
        "\n"
        "## Install\n"
        "\n"
        "```\n"
        "pip install some-kit==0.3.0\n"
        "```\n")


def test_a_long_section_is_given_as_its_opening_its_headings_and_a_link():
    # 2000 lines of 60 characters put the first theme alone past the limit of
    # 100 000 characters for a section that is used whole.
    filler = "\n".join("x" * 59 for _ in range(2000))
    long_changelog = CHANGELOG.replace("It proves.", filler)
    assert len(release_notes.section(long_changelog, "0.3.0")) > release_notes.FULL_TEXT_LIMIT

    assert release_notes.notes(long_changelog, "0.3.0", package="some-kit",
                               repository="someone/some-kit") == (
        "The package has a new name.\n"
        "\n"
        "## What is in this release\n"
        "\n"
        "- `api` — one more verb\n"
        "- Fixed: a wrong verdict\n"
        "\n"
        "The full notes are the section `[0.3.0]` of "
        "[CHANGELOG.md](https://github.com/someone/some-kit/blob/v0.3.0/CHANGELOG.md).\n"
        "\n"
        "## Install\n"
        "\n"
        "```\n"
        "pip install some-kit==0.3.0\n"
        "```\n")


def test_a_long_section_without_an_opening_starts_with_its_headings():
    filler = "\n".join("x" * 59 for _ in range(2000))
    long_changelog = CHANGELOG.replace("The package has a new name.\n\n", "").replace(
        "It proves.", filler)
    text = release_notes.notes(long_changelog, "0.3.0", package="some-kit",
                               repository="someone/some-kit")
    assert text.startswith("## What is in this release\n\n- `api` — one more verb\n")


def test_an_opening_that_cannot_fit_is_refused_rather_than_cut():
    opening = "\n".join("y" * 59 for _ in range(2200))        # 132 000 characters
    long_changelog = CHANGELOG.replace("The package has a new name.", opening)
    with pytest.raises(release_notes.ReleaseNotesError, match="GitHub takes 125000"):
        release_notes.notes(long_changelog, "0.3.0", package="some-kit",
                            repository="someone/some-kit")


def test_the_release_text_of_this_repository_fits_into_a_github_release():
    pyproject = (ROOT / "pyproject.toml").read_text(encoding="utf-8")
    changelog = (ROOT / "CHANGELOG.md").read_text(encoding="utf-8")
    version = release_notes.declared(pyproject, "version")
    package = release_notes.declared(pyproject, "name")

    assert release_notes.version_of("v" + version, pyproject) == version
    text = release_notes.notes(changelog, version, package=package,
                               repository="fvossel/unicode-logic-kit")
    assert len(text) <= release_notes.GITHUB_BODY_LIMIT
    assert text.endswith(f"pip install {package}=={version}\n```\n")


def test_the_command_reports_a_wrong_tag_on_standard_error_and_exits_1(capsys):
    assert release_notes.main(["v0.0.0-not-a-release"]) == 1
    captured = capsys.readouterr()
    assert captured.out == ""
    assert captured.err.startswith("release_notes: the tag 'v0.0.0-not-a-release'")
