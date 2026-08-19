"""The parse-error path must not rebuild lark's lexer, and must not run lark's
terminal-collision check.

Reported from a campaign that evaluates model-generated formulas next to vLLM:
a single failed parse took 185 s there and 13 ms here, same kit, same lark,
same Python. The only difference was that the package ``interegular`` happened
to be importable -- it arrives as a transitive dependency of vLLM via outlines,
so nobody installs it deliberately, and lark switches on a terminal-collision
check whenever it can import it (lark/lexer.py, ``if has_interegular:``).

Three things had to line up to make that ruinous, and the tests below pin down
the two the kit controls:

  * MSFL is parsed with parser="earley", so lark keeps no standing lexer and
    ``Lark.lex()`` builds a fresh ``BasicLexer`` on every call;
  * ``BasicLexer.__init__`` runs the collision check on construction;
  * the kit's identifier terminals are generated at import from the running
    interpreter's Unicode tables, and comparing every pair of same-priority
    ones takes minutes rather than milliseconds -- not because the patterns are
    long (the largest, NAME, is 4856 characters; the rest are 1.0 to 1.8 kB)
    but because interegular compares them by intersecting one finite automaton
    per pattern, and these range over most of the Unicode letter repertoire.

Failing parses are the NORMAL case when the input is model output, so this is
not a slow corner -- it is the corner that decides whether a batch job finishes.

The invariant tested is a call count, not a wall-clock number: "the collision
check never runs on the error path" is exactly what was wrong and is stable
across machines. Because that whole family of tests is only meaningful if the
probe fires at all, the first test proves the probe by showing lark's own route
DOES trip it. Without that, every assertion below would pass just as happily on
a kit where the bug was never fixed.
"""

import pytest

import lark.lexer
from lark import UnexpectedCharacters

from unicode_fol_kit import MSFLParser
from unicode_fol_kit.fol import naming
from unicode_fol_kit.fol.naming import NamingError, lex_for_message


# A formula that fails at the LEXER level: the second conjunction cannot follow
# a closing parenthesis inside a disjunction, so lark raises
# UnexpectedCharacters and the kit wraps it in a NamingError -- the path that
# has to re-lex the prefix.
BAD = "∀x (Child(x) ∨ Teenager(x) ∧ InClub(x) → Student(x))"


@pytest.fixture(autouse=True)
def collision_calls(monkeypatch):
    """Neutralise lark's terminal-collision check for every test in this
    module, and count how often it WOULD have run.

    Autouse, because several tests here deliberately call lark's own
    ``Lark.lex()`` -- the slow route -- to compare against, and the whole point
    of the module is that this route costs minutes wherever ``interegular`` is
    importable. Unpatched, ``test_tokens_match_larks_own_lexer`` alone makes
    1971 such calls; at the 185 s measured here that is over four days for one
    test, in exactly the environments this release exists for. Replacing the
    check with a counter cannot change any token compared below: it only ever
    raises (and only under ``strict``, which the kit never sets) or stays
    silent.

    ``raising=False`` on both patches: lark grew ``has_interegular`` after 1.1,
    and pyproject.toml allows ``lark>=1.1``, so on an older lark these names
    simply do not exist -- and there the check cannot run anyway.

    Clearing ``_ERROR_LEXERS`` per test keeps a process-global cache from
    carrying one test's monkeypatched state into the next; a stale entry there
    already made the postlex test pass for the wrong reason once.
    """
    calls = []
    monkeypatch.setattr(lark.lexer, "_check_regex_collisions",
                        lambda *a, **k: calls.append(1), raising=False)
    naming._ERROR_LEXERS.clear()
    return calls


@pytest.fixture
def collision_probe(collision_calls, monkeypatch):
    """The same counter, with ``has_interegular`` forced on.

    Forcing the flag is what makes the count independent of whether interegular
    is installed in the environment running the suite: it is a module-level
    global that ``BasicLexer.__init__`` reads at call time, so patching it puts
    the suite in the state the reporter's environment was in.
    """
    monkeypatch.setattr(lark.lexer, "has_interegular", True, raising=False)
    naming._ERROR_LEXERS.clear()
    return collision_calls


def test_the_probe_actually_fires_on_larks_own_route(collision_probe):
    """Proof that the probe measures something: lark's own ``Lark.lex`` -- the
    call the kit used to make -- trips the collision check, once per call.

    If lark ever stops building a lexer per call, or renames the check, this
    test fails and the two tests after it become vacuous rather than silently
    passing. That is the point of having it.
    """
    parser = MSFLParser().parser
    list(parser.lex("P(x)"))
    assert collision_probe, (
        "lark.lex did not trip the probe -- the collision-check tests below "
        "are no longer measuring anything")
    before = len(collision_probe)
    list(parser.lex("Q(x)"))
    assert len(collision_probe) > before, (
        "lark.lex tripped the check only once -- it no longer rebuilds the "
        "lexer per call, so the cost this module guards against has moved")


def test_failed_parse_never_runs_the_collision_check(collision_probe):
    """The whole bug, as one assertion."""
    parser = MSFLParser()
    for _ in range(5):
        with pytest.raises(NamingError):
            parser.parse(BAD)
    assert collision_probe == [], (
        f"the error path ran lark's collision check {len(collision_probe)} "
        f"time(s); on the reporter's grammar that is about three minutes each")


def test_error_lexer_is_built_once_per_parser(collision_probe):
    """Caching is the half of the fix that survives if lark ever makes the
    check unconditional: the cost would then be paid once per parser rather
    than once per failed formula."""
    parser = MSFLParser()
    with pytest.raises(NamingError):
        parser.parse(BAD)
    assert parser.parser in naming._ERROR_LEXERS
    first = naming._ERROR_LEXERS[parser.parser]
    for _ in range(3):
        with pytest.raises(NamingError):
            parser.parse(BAD)
    assert naming._ERROR_LEXERS[parser.parser] is first


# --- the fix is only allowed if the tokens are identical --------------------

# Valid formulas, malformed ones, and identifiers from every terminal class the
# generated grammar distinguishes -- including the caseless scripts and the
# Greek carve-out, where a shifted class boundary would be easiest to miss.
CORPUS = [
    "∀x (Human(x) → Mortal(x))",
    "P(x) ∧ Q(y)",
    "¬∃y Loves(y, socrates)",
    "Family_History(x)", "λx.P(x)", "α", "c_alpha",
    "c_świątek", "świątek", "Człowiek(x)",
    "x:Nat", "F(a, b, c) = 3", "P(x) ∧ Q(x) ∨ R(x)",
    "Foo(x) ^ Bar(x)", "Human$(x)", "∀x Human(x", "1 + 2 * 3", "", "   ",
    "语言(x)", "עברית", "Ⅳ", "Ⓐ",
    "\U0001d538(x)", "∀x:Person Nice(x)", "a≠b",
]
CORPUS += [s[:i] for s in CORPUS for i in range(1, len(s))]
CORPUS = sorted(set(CORPUS))

# Every distinct grammar the kit builds. The seven constructor flags have 128
# combinations but collapse onto nine parsers, and the count is asserted below
# so that a future flag silently widening (or collapsing) that set shows up
# here rather than leaving grammars untested.
FLAG_SETS = [{}, {"many_sorted": True}, {"fuzzy": True},
             {"many_sorted": True, "fuzzy": True}, {"modal": True},
             {"second_order": True}, {"dependence": True},
             {"linear": True}, {"lambek": True}]


def _outcome(fn):
    """Token tuples, or the failure, so the two routes are compared on both."""
    try:
        return ("ok", [(t.type, str(t), t.start_pos, t.end_pos) for t in fn()])
    except Exception as exc:              # noqa: BLE001 - compared, not handled
        return ("raised", type(exc).__name__, getattr(exc, "pos_in_stream", None))


def test_tokens_match_larks_own_lexer():
    """Skipping validation must not change what comes out.

    It cannot in principle -- validation checks that the GRAMMAR is well formed
    (regexes compile, no zero-width terminal, %ignore names defined) and only
    ever raises or stays silent -- but "cannot in principle" is how the
    underscore asymmetry in 0.23.0 got shipped, so it is checked against every
    distinct grammar the kit builds rather than argued.
    """
    seen, mismatches = set(), []
    for flags in FLAG_SETS:
        parser = MSFLParser(**flags).parser
        if id(parser) in seen:
            continue
        seen.add(id(parser))
        for text in CORPUS:
            lark_says = _outcome(lambda: list(parser.lex(text)))
            kit_says = _outcome(lambda: lex_for_message(parser, text))
            if lark_says != kit_says:
                mismatches.append((flags, text, lark_says, kit_says))
    assert len(seen) == 9, f"expected 9 distinct grammars, reached {len(seen)}"
    assert not mismatches, mismatches[:5]


# --- the fallback must stay a real fallback ---------------------------------

def test_fallback_produces_the_same_tokens(monkeypatch):
    """``lex_for_message`` drops back to ``parser.lex`` when lark's internals
    are not shaped as expected. Slow beats broken on a path that has already
    failed -- but only if the slow route still answers correctly."""
    parser = MSFLParser().parser
    fast = [(t.type, str(t)) for t in lex_for_message(parser, "Family_History(x)")]
    monkeypatch.setattr(naming, "_BasicLexer", None)
    naming._ERROR_LEXERS.clear()          # else the already-built lexer wins
    slow = [(t.type, str(t)) for t in lex_for_message(parser, "Family_History(x)")]
    assert fast == slow == [("PREDICATE", "Family_History"),
                            ("LPAR", "("), ("VARIABLE", "x"), ("RPAR", ")")]


def test_an_unlexable_text_does_not_fall_back(collision_probe, monkeypatch):
    """The failure mode that a broad ``except`` around the lexing would have
    created, and did in the first cut of this fix.

    ``UnexpectedCharacters`` raised by the text itself is not an infrastructure
    problem -- it is the answer. Catching it and retrying through
    ``parser.lex`` would rebuild lark's lexer and pay the collision check in
    full, for precisely the malformed inputs this module exists to make cheap,
    and then raise the same exception anyway.
    """
    parser = MSFLParser().parser
    calls = []
    real_lex = parser.lex
    monkeypatch.setattr(parser, "lex",
                        lambda *a, **k: (calls.append(1), real_lex(*a, **k))[1])
    for text in ["Human$", "$", "P(x) %", "∀x §"]:
        with pytest.raises(UnexpectedCharacters):
            lex_for_message(parser, text)
    assert calls == [], (
        f"an unlexable text fell back to parser.lex {len(calls)} time(s) -- "
        f"the slow route it exists to avoid")
    assert collision_probe == []


def test_a_grammar_lark_cannot_serve_is_only_attempted_once(monkeypatch):
    """The unavailable verdict is cached too. Retrying the construction on
    every failed formula would make an environment that needs the fallback pay
    for discovering that fact over and over."""
    parser = MSFLParser().parser
    naming._ERROR_LEXERS.clear()
    builds = []

    def exploding_lexer(conf):
        builds.append(1)
        raise RuntimeError("lark's internals moved")

    monkeypatch.setattr(naming, "_BasicLexer", exploding_lexer)
    for _ in range(4):
        assert [t.type for t in lex_for_message(parser, "P(x)")] == [
            "PREDICATE", "LPAR", "VARIABLE", "RPAR"]
    assert builds == [1], f"construction was retried {len(builds)} times"
    assert naming._ERROR_LEXERS[parser] is naming._UNAVAILABLE


def test_a_postlex_grammar_takes_the_fallback(monkeypatch):
    """The MSFL grammars declare no postlex, and reproducing lark's postlex
    stage by hand would be guesswork -- so a parser that has one must go the
    long way round rather than silently lose that stage.

    The stub drops the parentheses, which no real postlex would do; that is
    exactly why it makes a usable probe. If the fast path were taken despite
    postlex being set, the tokens would come back complete and the assertion
    would catch it -- rather than the test resting on a call counter alone.
    """
    class DroppingPostlex:
        always_accept = ()

        def __init__(self):
            self.used = False

        def process(self, stream):
            self.used = True
            return (t for t in stream if t.type not in ("LPAR", "RPAR"))

    parser = MSFLParser().parser
    postlex = DroppingPostlex()
    monkeypatch.setattr(parser.options, "postlex", postlex)
    # Without this the test passes for the wrong reason: _error_lexer consults
    # its cache BEFORE it looks at postlex, so a _UNAVAILABLE entry left by an
    # earlier test in this file sends the call down the fallback anyway. It did
    # exactly that until an audit deleted the postlex clause from naming.py and
    # the whole file still passed. (Clearing the cache is also what the autouse
    # fixture does; it is repeated here so the test does not silently depend on
    # a fixture it never names.)
    naming._ERROR_LEXERS.clear()
    assert [t.type for t in lex_for_message(parser, "P(x)")] == [
        "PREDICATE", "VARIABLE"]
    assert postlex.used, "postlex was set and the fast path ran anyway"


def test_an_unusable_parser_object_still_yields_a_message(monkeypatch):
    """``_ERROR_LEXERS`` is a WeakKeyDictionary, so it needs the parser to be
    hashable and weak-referenceable. A lark that grew ``__slots__`` without
    ``__weakref__`` -- an ordinary library change, not an internals rename --
    would make the LOOKUP raise TypeError, and with the lookup outside the
    guard that TypeError would surface in place of every syntax-error message.
    Simulated by making the cache itself refuse the key."""
    class HostileCache:
        def get(self, key):
            raise TypeError("cannot create weak reference to 'Lark' object")

        def __setitem__(self, key, value):
            raise TypeError("cannot create weak reference to 'Lark' object")

    monkeypatch.setattr(naming, "_ERROR_LEXERS", HostileCache())
    parser = MSFLParser()
    with pytest.raises(NamingError) as excinfo:
        parser.parse("Human$(x)")
    assert "Invalid predicate 'Human'" in str(excinfo.value)


# --- the message the whole detour exists for --------------------------------

@pytest.mark.parametrize("text, fragment", [
    ("Human$(x)", "Invalid predicate 'Human'"),
    ("∀x (P(x) ∨ Q(x) ∧ R(x))", "after closing parenthesis ')'"),
    ("Family_History$(x)", "Invalid predicate 'Family_History'"),
])
def test_message_still_names_the_token_in_front(text, fragment):
    """The reporter's first suggestion was to drop the re-lex entirely and read
    the position out of lark's exception. That would cost these messages: the
    Earley scanner leaves ``token_history`` at None, so the exception knows the
    offending character and nothing about the token before it. Naming that
    token is the reason NamingError exists -- a model reading the error in
    order to retry needs to know WHICH name was refused.
    """
    with pytest.raises(NamingError) as excinfo:
        MSFLParser().parse(text)
    assert fragment in str(excinfo.value)
