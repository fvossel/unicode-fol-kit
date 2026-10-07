"""Options of the test run that belong to this suite.

``--shard I/N`` runs the I-th of N parts of the suite. The parts are a partition
of the test FILES: a file belongs to exactly one part, decided by a hash of its
path, so the N runs together execute every test once and no run needs to know
what the others collected. CI uses it to run one platform's suite as three jobs
side by side (``.github/workflows/tests.yml``); a failed part is re-run alone.

Whole files are dealt out, never single tests, so a module-scoped fixture is
built in one part only and a file's tests keep the order they have in an
unsharded run.

The option acts twice. While pytest walks a directory, a test file of another
part is not collected at all (``pytest_ignore_collect``), so a part does not
import the two thirds of the suite it will not run. A file that is named on the
command line is collected whatever that hook says, so the tests of another part
are deselected again once collection is done (``pytest_collection_modifyitems``).
Both ask the same function, and the second alone already makes the parts a
partition.
"""

import hashlib

import pytest

#: Mixed into the hash that deals the files out. The value is chosen so that the
#: three parts CI runs take about the same time: measured on the suite of
#: 0.31.0 (3475 s of test time in 477 files), the parts are 1155 s, 1159 s and
#: 1160 s, where the unsalted hash gave 872 s, 1179 s and 1424 s. It has no
#: other meaning, and any value gives a correct partition; choose a new one when
#: the parts have drifted apart.
_SHARD_SALT = "88"


def pytest_addoption(parser):
    parser.addoption(
        "--shard", default=None, metavar="I/N",
        help="run only part I of N of the suite (test files are dealt out by a "
             "hash of their path; the N parts together are the whole suite)")


def _requested_shard(config):
    """``(index, count)`` for ``--shard index/count``, or ``None`` without the option."""
    text = config.getoption("--shard")
    if text is None:
        return None
    try:
        index, count = (int(part) for part in text.split("/"))
    except ValueError:
        raise pytest.UsageError(
            f"--shard {text!r}: expected I/N with two whole numbers, as in --shard 2/3") from None
    if count < 1 or not 1 <= index <= count:
        raise pytest.UsageError(
            f"--shard {text!r}: the part must be between 1 and the number of parts")
    return index, count


def _part_of(test_file: str, count: int) -> int:
    """The part, from 1 to ``count``, that the test file at ``test_file`` belongs to.

    ``test_file`` is the file half of a node id: relative to the root directory
    and written with forward slashes on every platform, so the same file is in
    the same part on Linux and on Windows.
    """
    digest = hashlib.sha256((_SHARD_SALT + test_file).encode("utf-8")).digest()
    return int.from_bytes(digest[:8], "big") % count + 1


def pytest_configure(config):
    _requested_shard(config)  # a malformed --shard ends the run before collection


def pytest_ignore_collect(collection_path, config):
    """Skip a test file of another part while a directory is walked.

    Returns ``True`` to skip and ``None`` to leave the decision to pytest. Only
    a Python test file under the root directory is ever skipped: a directory, a
    ``conftest.py`` or a helper module belongs to every part.
    """
    shard = _requested_shard(config)
    if shard is None or collection_path.suffix != ".py":
        return None
    name = collection_path.name
    if not (name.startswith("test_") or name.endswith("_test.py")):
        return None
    try:
        test_file = collection_path.relative_to(config.rootpath).as_posix()
    except ValueError:
        return None
    index, count = shard
    return True if _part_of(test_file, count) != index else None


def pytest_collection_modifyitems(config, items):
    shard = _requested_shard(config)
    if shard is None:
        return
    index, count = shard
    kept, dropped = [], []
    for item in items:
        test_file = item.nodeid.split("::", 1)[0]
        (kept if _part_of(test_file, count) == index else dropped).append(item)
    if dropped:
        config.hook.pytest_deselected(items=dropped)
        items[:] = kept
