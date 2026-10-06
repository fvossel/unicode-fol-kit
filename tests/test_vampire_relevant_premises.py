"""Which premises a Vampire proof used, as the Vampire backend's verdict reports them.

Vampire prints ``unknown`` for the name of an axiom unless it is asked for the names
(``--output_axiom_names on``). The backend asks, names the premises' ``axiom`` lines
(``premise_<i>``, or ``premise_names=``), and reads the premises the proof's axiom leaves are
back through those names. A PROVED verdict carries the caller's premise indices in
``relevant_premises``, and its ``detail`` names the background facts of a sorted reading that
the proof used (the non-emptiness of a sort, the membership of a sorted constant), which are
not premises.

The replay tests below feed the backend what Vampire 5.0.1 printed for these problems (recorded
live, the path of the problem file shortened to ``x.p``) and check the verdict by hand:

* ``Cold, Rain → Wet, Rain ⊢ Wet``: the proof is modus ponens on the second and the third premise,
  so the indices are ``(1, 2)``, and the first premise is not used;
* ``⊢ ∃x:Human Human(x)`` is the non-emptiness of the sort ``Human`` and nothing else: no premise;
* ``∀x:Human Mortal(x) ⊢ Mortal(socrates:Human)`` needs the premise and the membership of the sorted
  constant in its sort (the background fact), so the indices are ``(1,)`` and the detail names it.
"""

import os
import shutil

import pytest

from unicode_fol_kit import api
from unicode_fol_kit.atp import protocol as _protocol
from unicode_fol_kit.atp import vampire_entailment as _ve
from unicode_fol_kit.atp.protocol import get_backend
from unicode_fol_kit.fol.nodes import Atom, Constant, Function, SortedQuantifier, Variable
from unicode_fol_kit.fol.signature import Signature


def parse(text):
    result = api.parse_any(text)
    assert result.ok, (text, result.errors)
    return result.formula


COLD, RULE, RAIN, WET = parse("Cold"), parse("Rain → Wet"), parse("Rain"), parse("Wet")
PREMISES = [COLD, RULE, RAIN]

#: Vampire 5.0.1 under ``--output_axiom_names on`` on ``premise_1 .. premise_3`` (cold, rain => wet, rain)
PROOF = r"""
% SZS status Theorem for x
% SZS output start Proof for x
fof(f2,axiom,(
  rain => wet),
  file('x.p',premise_2)).
fof(f3,axiom,(
  rain),
  file('x.p',premise_3)).
fof(f4,conjecture,(
  wet),
  file('x.p',goal)).
fof(f5,negated_conjecture,(
  ~wet),
  inference(negated_conjecture,[status(cth)],[f4])).
fof(f6,plain,(
  ~wet),
  inference(flattening,[],[f5])).
fof(f8,plain,(
  wet | ~rain),
  inference(ennf_transformation,[],[f2])).
fof(f9,plain,(
  wet | ~rain),
  inference(cnf_transformation,[],[f8])).
fof(f10,plain,(
  rain),
  inference(cnf_transformation,[],[f3])).
fof(f11,plain,(
  ~wet),
  inference(cnf_transformation,[],[f6])).
fof(f12,plain,(
  ~rain),
  inference(forward_subsumption_resolution,[],[f9,f11])).
fof(f13,plain,(
  $false),
  inference(forward_subsumption_resolution,[],[f12,f10])).
% SZS output end Proof for x
"""

#: the same problem with the premises named ``cold``, ``it's a rule`` and ``rain``
NAMES = ["cold", "it's a rule", "rain"]
PROOF_NAMED = PROOF.replace("premise_2", "'it\\'s a rule'").replace("premise_3", "rain")

#: the same proof, Vampire run WITHOUT the names: it prints the word ``unknown`` for each axiom
PROOF_UNNAMED = PROOF.replace("premise_2", "unknown").replace("premise_3", "unknown")

#: ``Cold ⊢ ∃x:Human Human(x)``: the proof uses ``nonempty_sort_1`` only
PROOF_SORT_ONLY = r"""
% SZS status Theorem for x
% SZS output start Proof for x
fof(f2,axiom,(
  ? [X0] : human(X0)),
  file('x.p',nonempty_sort_1)).
fof(f3,conjecture,(
  ? [X0] : (human(X0) & human(X0))),
  file('x.p',goal)).
fof(f4,negated_conjecture,(
  ~? [X0] : (human(X0) & human(X0))),
  inference(negated_conjecture,[status(cth)],[f3])).
fof(f6,plain,(
  ! [X0] : (~human(X0) | ~human(X0))),
  inference(ennf_transformation,[],[f4])).
fof(f7,plain,(
  ? [X0] : human(X0) => human(sK0)),
  introduced(definition,[],[skolem_symbol_introduction])).
fof(f8,plain,(
  human(sK0)),
  inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f2,f7])).
fof(f9,plain,(
  human(sK0)),
  inference(cnf_transformation,[],[f8])).
fof(f10,plain,(
  ( ! [X0] : (~human(X0) | ~human(X0)) )),
  inference(cnf_transformation,[],[f6])).
fof(f11,plain,(
  ( ! [X0] : (~human(X0)) )),
  inference(duplicate_literal_removal,[],[f10])).
fof(f12,plain,(
  $false),
  inference(forward_subsumption_resolution,[],[f9,f11])).
% SZS output end Proof for x
"""

#: ``Cold, ∀x:Human Mortal(x) ⊢ Mortal(socrates:Human)``, written as ``fof``: the proof uses ``premise_2``
#: and ``sort_member_1`` (``Human(socrates)``)
PROOF_PREMISE_AND_MEMBERSHIP = r"""
% SZS status Theorem for x
% SZS output start Proof for x
fof(f2,axiom,(
  ! [X0] : (human(X0) => mortal(X0))),
  file('x.p',premise_2)).
fof(f4,axiom,(
  human(socrates)),
  file('x.p',sort_member_1)).
fof(f5,conjecture,(
  mortal(socrates)),
  file('x.p',goal)).
fof(f6,negated_conjecture,(
  ~mortal(socrates)),
  inference(negated_conjecture,[status(cth)],[f5])).
fof(f7,plain,(
  ~mortal(socrates)),
  inference(flattening,[],[f6])).
fof(f9,plain,(
  ! [X0] : (mortal(X0) | ~human(X0))),
  inference(ennf_transformation,[],[f2])).
fof(f12,plain,(
  ( ! [X0] : (~human(X0) | mortal(X0)) )),
  inference(cnf_transformation,[],[f9])).
fof(f14,plain,(
  human(socrates)),
  inference(cnf_transformation,[],[f4])).
fof(f15,plain,(
  ~mortal(socrates)),
  inference(cnf_transformation,[],[f7])).
fof(f17,plain,(
  mortal(socrates)),
  inference(resolution,[],[f12,f14])).
fof(f18,plain,(
  $false),
  inference(forward_subsumption_resolution,[],[f17,f15])).
% SZS output end Proof for x
"""

NOT_A_THEOREM = """
% SZS status CounterSatisfiable for x
% SZS output start Saturation for x
% SZS output end Saturation for x
"""


class Spawn:
    """A replacement for the process Vampire runs in: answers with what it was told to, and records what it was asked."""

    def __init__(self, output):
        self.output = output
        self.calls = []

    def __call__(self, input_str, vampire_path, timeout=30, use_wsl=False, extra_args=()):
        self.calls.append({"input": input_str, "args": tuple(extra_args)})
        return self.output, False


@pytest.fixture()
def replay(monkeypatch):
    """``replay(output)`` makes Vampire print ``output`` and returns the recorder of what it was asked."""
    monkeypatch.setattr(_protocol, "_binary_version", lambda *a, **k: None)

    def install(output):
        spawn = Spawn(output)
        monkeypatch.setattr(_ve, "_spawn_vampire", spawn)
        return spawn
    return install


@pytest.fixture()
def placeholder_binary(tmp_path):
    """A file this host can start, named as ``vampire_path=`` where a call goes through ``api.prove``.

    The process is replaced by ``replay``, so the file never runs; but the gate of ``api.prove`` asks
    whether a native ``vampire_path=`` names a binary the host can start, and a name that is no file at
    all is refused there.
    """
    path = tmp_path / ("vampire-placeholder.exe" if os.name == "nt" else "vampire-placeholder")
    path.write_text("")
    path.chmod(0o755)
    return str(path)


def decide(goal, premises, **options):
    return get_backend("vampire").decide(goal, premises, timeout=5000, vampire_path="v", use_wsl=False,
                                         **options)


# ---------------------------------------------------------------------------
# What the verdict carries
# ---------------------------------------------------------------------------

def test_a_proved_verdict_carries_the_premises_the_proof_used(replay):
    spawn = replay(PROOF)
    verdict = decide(WET, PREMISES)
    assert verdict.status == "proved"
    assert verdict.relevant_premises == (1, 2)           # modus ponens on the second and third premise
    assert verdict.to_dict()["relevant_premises"] == [1, 2]
    assert "background" not in verdict.detail
    # the backend asked Vampire to print the names of the axioms of its proof, and named the premises
    assert spawn.calls[0]["args"] == ("--proof", "tptp", "--output_axiom_names", "on")
    assert "fof(premise_2, axiom, (rain => wet))." in spawn.calls[0]["input"]


def test_premise_names_name_the_axiom_lines_and_the_proof_is_read_by_them(replay):
    spawn = replay(PROOF_NAMED)
    verdict = decide(WET, PREMISES, premise_names=NAMES)
    assert verdict.status == "proved"
    assert verdict.relevant_premises == (1, 2)
    assert "fof('it\\'s a rule', axiom, (rain => wet))." in spawn.calls[0]["input"]
    assert "premise_2" not in spawn.calls[0]["input"]


def test_a_proof_that_uses_only_a_background_fact_reports_no_premise(replay):
    replay(PROOF_SORT_ONLY)
    verdict = decide(parse("∃x:Human Human(x)"), [COLD])
    assert verdict.status == "proved"
    assert verdict.relevant_premises == ()               # the sort's non-emptiness is the whole proof
    assert "the proof used the background facts of the sorted reading, which are not premises" in verdict.detail
    assert "nonempty_sort_1" in verdict.detail


def test_a_premise_and_a_background_fact_are_told_apart(replay):
    replay(PROOF_PREMISE_AND_MEMBERSHIP)
    verdict = decide(parse("Mortal(socrates:Human)"), [COLD, parse("∀x:Human Mortal(x)")], tff=False)
    assert verdict.status == "proved"
    assert verdict.relevant_premises == (1,)             # the universal premise; sort_member_1 is background
    assert "sort_member_1" in verdict.detail and "not premises" in verdict.detail


def test_a_proof_that_names_no_axiom_reports_none_never_a_guess(replay):
    replay(PROOF_UNNAMED)
    verdict = decide(WET, PREMISES)
    assert verdict.status == "proved"
    assert verdict.relevant_premises is None


def test_asking_for_no_names_leaves_the_command_line_and_the_report_as_before(replay):
    spawn = replay(PROOF_UNNAMED)
    verdict = decide(WET, PREMISES, axiom_names=False)
    assert verdict.status == "proved" and verdict.relevant_premises is None
    assert spawn.calls[0]["args"] == ("--proof", "tptp")
    # naming the premises asks for the names whatever axiom_names says
    spawn = replay(PROOF_NAMED)
    verdict = decide(WET, PREMISES, axiom_names=False, premise_names=NAMES)
    assert spawn.calls[0]["args"] == ("--proof", "tptp", "--output_axiom_names", "on")
    assert verdict.relevant_premises == (1, 2)


def test_a_verdict_that_is_not_proved_carries_no_premises(replay):
    replay(NOT_A_THEOREM)
    verdict = decide(WET, [COLD])
    assert verdict.status == "refuted"
    assert verdict.relevant_premises is None


def test_premise_names_of_the_wrong_number_are_refused_before_vampire_runs(replay):
    spawn = replay(PROOF)
    with pytest.raises(ValueError):
        decide(WET, PREMISES, premise_names=["only", "two"])
    assert spawn.calls == []


# ---------------------------------------------------------------------------
# Through api.prove
# ---------------------------------------------------------------------------

def test_api_prove_reports_the_premises_with_and_without_names_and_without_the_flag(
        replay, placeholder_binary):
    spawn = replay(PROOF)
    verdict = api.prove(WET, PREMISES, backends=["vampire"], vampire_path=placeholder_binary, use_wsl=False)
    assert verdict.relevant_premises == (1, 2)
    spawn = replay(PROOF_NAMED)
    verdict = api.prove(WET, PREMISES, backends=["vampire"], vampire_path=placeholder_binary, use_wsl=False,
                        premise_names=NAMES)
    assert verdict.relevant_premises == (1, 2)


def test_api_prove_does_not_run_vampire_a_second_time_for_relevant_premises(replay, placeholder_binary):
    spawn = replay(PROOF)
    verdict = api.prove(WET, PREMISES, backends=["vampire"], vampire_path=placeholder_binary, use_wsl=False,
                        relevant_premises=True)
    assert verdict.relevant_premises == (1, 2)
    assert len(spawn.calls) == 1


def test_api_prove_reports_indices_into_the_callers_premises_when_a_signature_adds_some(
        replay, placeholder_binary):
    # the signature declares the sort A, which adds ∃x A(x) after the caller's three premises; the
    # proof does not use it, and the indices stay indices into the caller's list
    replay(PROOF)
    signature = Signature.from_dict({"sorts": ["A"]})
    verdict = api.prove(WET, PREMISES, backends=["vampire"], vampire_path=placeholder_binary, use_wsl=False,
                        signature=signature)
    assert verdict.relevant_premises == (1, 2)


# ---------------------------------------------------------------------------
# A real Vampire
# ---------------------------------------------------------------------------

_NATIVE_VAMPIRE = shutil.which("vampire")
VAMPIRE = (dict(vampire_path=_NATIVE_VAMPIRE, use_wsl=False) if _NATIVE_VAMPIRE
           else dict(vampire_path="vampire", use_wsl=True))
live = pytest.mark.skipif(not get_backend("vampire").available_for(VAMPIRE),
                          reason="no Vampire reachable here")


@live
@pytest.mark.parametrize("names", [None, NAMES, ["it's cold 1", "if rain then wet", "ß ' \\ q"]],
                         ids=["default-names", "plain-names", "awkward-names"])
def test_live_vampire_reports_the_callers_premise_indices(names):
    options = dict(VAMPIRE)
    if names is not None:
        options["premise_names"] = names
    verdict = api.prove(WET, PREMISES, backends=["vampire"], timeout=30000, **options)
    assert verdict.status == "proved"
    assert verdict.relevant_premises == (1, 2)


@live
def test_live_vampire_reports_no_premise_for_a_proof_by_a_sort_axiom_alone():
    verdict = api.prove(parse("∃x:Human Human(x)"), [COLD], backends=["vampire"], timeout=30000, **VAMPIRE)
    assert verdict.status == "proved"
    assert verdict.relevant_premises == ()
    assert "nonempty_sort_1" in verdict.detail


@live
def test_live_background_note_comes_before_the_note_of_a_refused_typed_writer():
    # a problem the typed writer refuses is written as fof, the detail says so, and the facts the
    # proof used come first
    verdict = api.prove(parse("∃x:Human Human(x)"), [COLD], backends=["vampire"], timeout=30000, **VAMPIRE)
    assert verdict.status == "proved"
    assert "typed" in verdict.detail
    assert verdict.detail.index("background facts") < verdict.detail.index("typed")


@live
def test_live_vampire_names_the_background_fact_and_the_premise_of_a_sorted_proof():
    verdict = api.prove(parse("Mortal(socrates:Human)"), [COLD, parse("∀x:Human Mortal(x)")],
                        backends=["vampire"], timeout=30000, tff=False, **VAMPIRE)
    assert verdict.status == "proved"
    assert verdict.relevant_premises == (1,)
    assert "sort_member_1" in verdict.detail


@live
def test_live_vampire_through_a_signature_reports_only_the_callers_premises():
    # f: A → B and carl in A make ∃x:B x = f(carl) valid; the proof rests on the signature's sentences
    # alone, which are no premise of the caller's
    signature = Signature.from_dict({"functions": {"f": {"arity": 1, "arg_sorts": ["A"], "result_sort": "B"}},
                                     "constants": {"carl": "A"}, "sorts": ["A", "B"]})
    x = Variable("x")
    goal = SortedQuantifier("∃", x, "B", Atom("=", [x, Function("f", [Constant("carl")])]))
    verdict = api.prove(goal, [COLD], backends=["vampire"], timeout=30000, signature=signature, **VAMPIRE)
    assert verdict.status == "proved"
    assert verdict.relevant_premises == ()
