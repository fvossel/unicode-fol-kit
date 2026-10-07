"""Write the text of a GitHub Release from the changelog section of a version.

usage: python tools/release_notes.py <tag> [--repository OWNER/NAME]

Prints Markdown to standard output. The publish workflow
(``.github/workflows/publish.yml``) calls it for the tag it publishes, so it is
also the check that the tag, ``pyproject.toml`` and ``CHANGELOG.md`` agree: the
tag has to be ``v`` + the version ``pyproject.toml`` declares, and the changelog
needs a section ``## [<version>] - <date>``. Either failing ends the run with
exit code 1 and one line on standard error, before anything is uploaded.

What the text holds depends on the size of the section, because GitHub refuses
a release body of more than 125 000 characters and a section of this changelog
can be twice that:

* a section of at most :data:`FULL_TEXT_LIMIT` characters is the release text,
  as it stands;
* a longer one is given as its opening paragraphs (whatever stands before the
  first ``###`` heading), the list of its ``###`` headings and a link to the
  changelog at the tag.

Both end with the install line for exactly this version.
"""

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

#: GitHub's limit for the body of a release, in characters.
GITHUB_BODY_LIMIT = 125_000

#: A section up to this size is used whole. The distance to the limit above is
#: room for the lines this module adds and for a character GitHub counts twice.
FULL_TEXT_LIMIT = 100_000


class ReleaseNotesError(Exception):
    """The tag, ``pyproject.toml`` and the changelog do not describe one release."""


def declared(pyproject_text: str, key: str) -> str:
    """The value of ``key = "..."`` in the ``[project]`` table of ``pyproject_text``."""
    table = re.search(r"^\[project\]\s*$(.*?)(?=^\[)", pyproject_text + "\n[", re.M | re.S)
    found = table and re.search(rf'^{re.escape(key)}\s*=\s*"([^"]+)"', table.group(1), re.M)
    if not found:
        raise ReleaseNotesError(f"pyproject.toml declares no {key} in its [project] table")
    return found.group(1)


def version_of(tag: str, pyproject_text: str) -> str:
    """The version that ``tag`` releases: ``tag`` without its ``v``.

    Raises:
        ReleaseNotesError: ``tag`` is not ``v`` + the version of ``pyproject_text``.
    """
    version = declared(pyproject_text, "version")
    if tag != "v" + version:
        raise ReleaseNotesError(
            f"the tag {tag!r} does not release what pyproject.toml declares: version "
            f"{version!r} is released by the tag 'v{version}'")
    return version


def section(changelog_text: str, version: str) -> str:
    """The body of the section ``## [version] - date``, without that heading line.

    The body runs up to the next ``## [`` heading or the end of the text, and is
    returned without blank lines around it. Line endings are read alike
    (``\\r\\n``, ``\\r``, ``\\n``) and come back as ``\\n``.

    Raises:
        ReleaseNotesError: the text has no section for ``version``.
    """
    text = changelog_text.replace("\r\n", "\n").replace("\r", "\n")
    heading = re.search(rf"^## \[{re.escape(version)}\][^\n]*\n", text, re.M)
    if not heading:
        raise ReleaseNotesError(f"CHANGELOG.md has no section '## [{version}]'")
    rest = text[heading.end():]
    following = re.search(r"^## \[", rest, re.M)
    return (rest[:following.start()] if following else rest).strip("\n")


def notes(changelog_text: str, version: str, *, package: str, repository: str) -> str:
    """The release text for ``version`` (see the module docstring for its two shapes)."""
    body = section(changelog_text, version)
    install = f"## Install\n\n```\npip install {package}=={version}\n```\n"
    if len(body) <= FULL_TEXT_LIMIT:
        return f"{body}\n\n{install}"

    first_heading = re.search(r"^### ", body, re.M)
    lead = body[:first_heading.start()].strip("\n") if first_heading else ""
    headings = re.findall(r"^### (.+)$", body, re.M)
    parts = []
    if lead:
        parts.append(lead)
    if headings:
        parts.append("## What is in this release\n\n" + "\n".join(f"- {line}" for line in headings))
    parts.append(
        f"The full notes are the section `[{version}]` of "
        f"[CHANGELOG.md](https://github.com/{repository}/blob/v{version}/CHANGELOG.md).")
    parts.append(install)
    text = "\n\n".join(parts)
    if len(text) > GITHUB_BODY_LIMIT:
        raise ReleaseNotesError(
            f"the release text for {version} has {len(text)} characters and GitHub takes "
            f"{GITHUB_BODY_LIMIT}: shorten what stands before the first '###' heading of "
            f"the section, or its headings")
    return text


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("tag", help="the tag that is released, e.g. v0.31.0")
    parser.add_argument("--repository", default="fvossel/unicode-logic-kit",
                        help="OWNER/NAME on GitHub, for the link to the changelog")
    arguments = parser.parse_args(argv)

    pyproject = (ROOT / "pyproject.toml").read_text(encoding="utf-8")
    changelog = (ROOT / "CHANGELOG.md").read_text(encoding="utf-8")
    try:
        version = version_of(arguments.tag, pyproject)
        text = notes(changelog, version, package=declared(pyproject, "name"),
                     repository=arguments.repository)
    except ReleaseNotesError as error:
        print(f"release_notes: {error}", file=sys.stderr)
        return 1
    sys.stdout.buffer.write(text.encode("utf-8"))
    return 0


if __name__ == "__main__":
    sys.exit(main())
