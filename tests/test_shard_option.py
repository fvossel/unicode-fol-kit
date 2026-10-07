"""``--shard I/N`` deals the test files out into N parts that together are the suite.

CI runs one platform's suite as three jobs (``--shard 1/3``, ``2/3``, ``3/3``).
That is only sound if the parts are a partition: every test in exactly one of
them. The cases collect a handful of this suite's own files in a fresh pytest
process, once whole and once per part, and compare the node ids.
"""

import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent

# A fixed handful of files, so the collection takes seconds. Twelve files and
# three parts: the chance that a sound hash leaves one part empty is small, and
# the partition claim does not depend on it either way.
FILES = sorted(path.relative_to(ROOT).as_posix()
               for path in (ROOT / "tests").glob("test_s*.py"))[:12]


def _collect(*options):
    """The node ids pytest collects from FILES under ``options``, and its exit code."""
    done = subprocess.run(
        [sys.executable, "-m", "pytest", "--collect-only", "-q", "-p", "no:cacheprovider",
         *options, *FILES],
        cwd=ROOT, capture_output=True, encoding="utf-8", timeout=600)
    ids = [line for line in done.stdout.splitlines() if "::" in line]
    return ids, done


def test_the_parts_are_disjoint_and_together_the_whole_collection():
    whole, done = _collect()
    assert done.returncode == 0, done.stdout + done.stderr
    assert len(FILES) == 12 and whole

    parts = [_collect("--shard", f"{index}/3")[0] for index in (1, 2, 3)]

    assert sorted(parts[0] + parts[1] + parts[2]) == sorted(whole)
    assert len(set(parts[0]) | set(parts[1]) | set(parts[2])) == len(whole)   # no id twice


def test_a_file_is_never_split_between_two_parts():
    parts = [_collect("--shard", f"{index}/3")[0] for index in (1, 2, 3)]
    files = [{node_id.split("::", 1)[0] for node_id in part} for part in parts]
    assert not (files[0] & files[1] or files[0] & files[2] or files[1] & files[2])


def test_one_part_of_one_is_the_whole_collection():
    whole, _ = _collect()
    single, done = _collect("--shard", "1/1")
    assert done.returncode == 0, done.stdout + done.stderr
    assert single == whole


def test_the_order_inside_a_part_is_the_order_of_the_whole_collection():
    whole, _ = _collect()
    part, _ = _collect("--shard", "2/3")
    kept = set(part)
    assert part == [node_id for node_id in whole if node_id in kept]


def test_a_file_of_another_part_is_not_even_imported_when_a_directory_is_collected(tmp_path):
    # A directory of its own, with this suite's conftest.py and twelve tiny test
    # files. Each file prints a line when it is imported, so the output of a
    # collection shows which files that part touched at all.
    (tmp_path / "pytest.ini").write_text("[pytest]\n", encoding="utf-8")
    (tmp_path / "conftest.py").write_text(
        (ROOT / "tests" / "conftest.py").read_text(encoding="utf-8"), encoding="utf-8")
    names = [f"test_file_{number:02d}.py" for number in range(12)]
    for name in names:
        (tmp_path / name).write_text(
            f"print('IMPORTED {name}')\n\ndef test_one():\n    pass\n\ndef test_two():\n    pass\n",
            encoding="utf-8")

    def collect(*options):
        done = subprocess.run(
            [sys.executable, "-m", "pytest", "--collect-only", "-q", "-s",
             "-p", "no:cacheprovider", "--rootdir", str(tmp_path), *options, str(tmp_path)],
            cwd=tmp_path, capture_output=True, encoding="utf-8", timeout=600)
        lines = done.stdout.splitlines()
        imported = sorted(line.split()[1] for line in lines if line.startswith("IMPORTED "))
        ids = sorted(line for line in lines if "::" in line)
        return imported, ids

    imported_whole, ids_whole = collect()
    assert imported_whole == names                      # the unsharded run imports all twelve
    assert len(ids_whole) == 24

    parts = [collect("--shard", f"{index}/3") for index in (1, 2, 3)]
    # Every file is imported by exactly one part, and its two tests are in that part.
    assert sorted(parts[0][0] + parts[1][0] + parts[2][0]) == names
    assert sorted(parts[0][1] + parts[1][1] + parts[2][1]) == ids_whole
    for imported, ids in parts:
        assert sorted({node_id.split("::", 1)[0] for node_id in ids}) == imported


@pytest.mark.parametrize("value", ["0/3", "4/3", "3", "a/b", "1/0", "2/3/4"])
def test_a_malformed_shard_ends_the_run_with_a_usage_error(value):
    # Exit code 4 is pytest's "command line usage error".
    ids, done = _collect("--shard", value)
    assert done.returncode == 4, done.stdout + done.stderr
    assert "--shard" in done.stderr
    assert ids == []
