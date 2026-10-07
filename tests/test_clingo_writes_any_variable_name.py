"""The clingo encoder writes a variable of any name as an ASP variable of its own.

The VARIABLE terminal admits any Unicode letter, so ``∀é P(é)`` is a formula the
parser reads. The encoder wrote the variable ``"V" + name``, and ``Vé`` is no ASP
variable: clingo's parser was handed text it does not read, and the call ended
with an error of the decoder (``UnicodeDecodeError``) instead of a verdict. A
hand-built variable named ``x-1`` became ``Vx-1``, which ASP reads as the
arithmetic ``Vx - 1``.

An ASP variable is an upper-case letter followed by ASCII letters, digits and
underscores. A name of that alphabet that starts with a letter or digit keeps
``"V" + name``; any other name is written ``"V_" + code``, each character that is
no ASCII letter or digit as ``_<hex code point>_``. Every identifier and every
verdict below is worked out by hand.
"""

import itertools
import re
import subprocess
import sys

import pytest

from unicode_logic_kit import MSFLParser
from unicode_logic_kit.atp.clingo_backend import _AspEncoder, _EncodingError
from unicode_logic_kit.fol.nodes import Atom, Quantifier, Variable

ASP_VARIABLE = re.compile(r"[A-Z][A-Za-z0-9_]*\Z")
asp_var = _AspEncoder._asp_var


def parse(text):
    return MSFLParser().parse(text)


# ---------------------------------------------------------------------------
# The identifier
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("name, identifier", [
    # the names the grammar and the kit's own fresh variables give: unchanged
    ("x", "Vx"),
    ("x0", "Vx0"),
    ("x_0", "Vx_0"),
    ("X", "VX"),
    ("0", "V0"),
    # é is U+00E9, ж is U+0436, α is U+03B1
    ("é", "V__e9_"),
    ("ж", "V__436_"),
    ("α", "V__3b1_"),
    ("é0", "V__e9_0"),
    # a hyphen is U+002D, a space U+0020, an apostrophe U+0027
    ("x-1", "V_x_2d_1"),
    ("a b", "V_a_20_b"),
    ("x'", "V_x_27_"),
    # a leading underscore (U+005F) is not the plain form: "V_" opens the code
    ("_x", "V__5f_x"),
    ("_", "V__5f_"),
    ("", "V_"),
])
def test_the_asp_variable_of_a_name(name, identifier):
    assert asp_var(name) == identifier
    assert ASP_VARIABLE.match(identifier)


def test_a_plain_name_and_a_coded_name_never_share_a_variable():
    # "x_e9_" is a plain name, and its variable is not the one of "é" although the code of é
    # is the text "_e9_": the coded form has an underscore right after the V
    assert asp_var("x_e9_") == "Vx_e9_"
    assert asp_var("é") == "V__e9_"
    assert asp_var("_e9_") == "V__5f_e9_5f_"
    # the literal text of a code is a name too, and is coded again
    assert asp_var("_2d_") == "V__5f_2d_5f_"
    assert asp_var("-") == "V__2d_"


def test_every_short_name_gets_a_legal_variable_of_its_own():
    alphabet = ["a", "B", "1", "_", "-", "é", " ", "'"]
    names = [""] + ["".join(word) for length in (1, 2, 3)
                    for word in itertools.product(alphabet, repeat=length)]
    assert len(names) == 1 + 8 + 64 + 512
    written = {name: asp_var(name) for name in names}
    assert all(ASP_VARIABLE.match(identifier) for identifier in written.values())
    assert len(set(written.values())) == len(names)
    # none is a name the encoder mints itself (Cst<n>, Card<n>, Fn<n>)
    assert all(identifier.startswith("V") for identifier in written.values())


def test_control_the_old_rule_wrote_text_that_is_no_variable():
    old = lambda name: "V" + name
    assert not ASP_VARIABLE.match(old("é"))
    assert not ASP_VARIABLE.match(old("x-1"))
    # ... and a lossy rule (every other character as one underscore) would merge two names
    lossy = lambda name: "V" + re.sub(r"[^A-Za-z0-9_]", "_", name)
    assert lossy("x-1") == lossy("x 1") == lossy("x_1")
    assert len({asp_var("x-1"), asp_var("x 1"), asp_var("x_1")}) == 3


def test_a_name_that_is_no_string_is_refused():
    with pytest.raises(_EncodingError, match="not a string"):
        asp_var(7)


# ---------------------------------------------------------------------------
# The solver: a verdict, and the verdict of the ASCII twin
# ---------------------------------------------------------------------------
#
# Each problem runs in a child process: what is under test used to end the call
# from inside clingo's parser, and a child keeps that away from this process.

CHILD = r'''
import sys
from unicode_logic_kit import MSFLParser
from unicode_logic_kit.atp.protocol import get_backend
parse = MSFLParser().parse
goal, premises = parse(sys.argv[1]), [parse(text) for text in sys.argv[2:]]
verdict = get_backend("clingo").decide(goal, premises, timeout=20000)
print("VERDICT", verdict.status, verdict.reason)
'''


def decide_in_child(goal, premises):
    done = subprocess.run([sys.executable, "-X", "utf8", "-c", CHILD, goal, *premises],
                          capture_output=True, text=True, encoding="utf-8", timeout=180)
    lines = [line for line in done.stdout.splitlines() if line.startswith("VERDICT ")]
    assert lines, f"no verdict (exit {done.returncode}):\n{done.stderr[-1500:]}"
    return tuple(lines[-1].split()[1:])


# (goal, premises, the same with ASCII variable names, status)
#
# 1. ∃é P(é) does not give P(alice): the domain {0, 1} with alice = 0 and P = {1} makes the
#    premise true and the goal false. A model finder reports that: refuted.
# 2. ∀é P(é) gives P(alice) in every structure, so there is no countermodel of any size; a
#    finite model finder cannot prove, and says so: unknown.
# 3. ∀é ∃e R(é, e) does not give ∃e ∀é R(é, e): over {0, 1} with R the identity every
#    element has a partner (itself) and no element is the partner of both. Two binders, é
#    and e: if the two names were written as one ASP variable the premise would read
#    ∀e R(e, e), from which ∃e ∀é R(é, e) still does not follow over R = identity, so the
#    goal is turned around in 4 to make a merge visible.
# 4. ∀é ∀e R(é, e) gives R(alice, bob); with é and e merged the premise would be ∀e R(e, e),
#    which does not (R = identity, alice = 0, bob = 1): a merge would be reported as refuted.
PROBLEMS = [
    ("P(alice)", ["∃é P(é)"], ["∃x P(x)"], "refuted"),
    ("P(alice)", ["∀é P(é)"], ["∀x P(x)"], "unknown"),
    ("∃e ∀é R(é, e)", ["∀é ∃e R(é, e)"],
     ["∀x ∃e R(x, e)"], "refuted"),
    ("R(alice, bob)", ["∀é ∀e R(é, e)"], ["∀x ∀e R(x, e)"],
     "unknown"),
    ("P(alice)", ["∃ж P(ж)"], ["∃x P(x)"], "refuted"),
]


@pytest.mark.parametrize("goal, premises, twin_premises, status", PROBLEMS)
def test_a_problem_with_a_non_ascii_variable_gets_the_verdict_of_its_ascii_twin(
        goal, premises, twin_premises, status):
    pytest.importorskip("clingo")
    twin_goal = goal.replace("é", "x")
    answer = decide_in_child(goal, premises)
    twin = decide_in_child(twin_goal, twin_premises)
    assert answer[0] == status
    assert answer == twin
    if status == "unknown":
        assert answer[1] == "bound_hit"


def test_a_hand_built_variable_with_a_hyphen_is_a_variable_and_not_arithmetic():
    pytest.importorskip("clingo")
    from unicode_logic_kit.atp.protocol import get_backend
    odd = Variable("x-1")
    # ∃(x-1) P(x-1) does not give P(alice), as in problem 1 above
    premise = Quantifier("∃", odd, Atom("P", [odd]))
    verdict = get_backend("clingo").decide(parse("P(alice)"), [premise], timeout=20000)
    assert verdict.status == "refuted"
