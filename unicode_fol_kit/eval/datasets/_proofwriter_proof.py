"""Grammar and parser for ProofWriter's own proof-annotation strings.

ProofWriter (see :mod:`.proofwriter`'s module docstring for the dataset
itself) ships two DIFFERENT proof-annotation fields, both in the SAME
``triple``/``rule``-reference notation, kept verbatim and UNPARSED by every
loader in :mod:`.proofwriter`:

* ``question["proofs"]`` (structured/hitachi-nlp mirror, one entry per
  question) — exactly ONE of two shapes:

  (a) a positive/negative DERIVATION: a proof forest over the theory's own
      named facts/rules. Leaves are bare ``tripleN`` references (a fact cited
      directly); ``(t1 t2 …) -> ruleN`` applies ``ruleN`` to a CONJUNCTION of
      antecedents, each ``ti`` itself either a bare ``tripleN`` leaf or a
      further derivation (in which case it is written parenthesised, as an
      ``Item``); `` OR `` at the top level separates ALTERNATIVE derivations
      of the same fact (a forest, not a single path). The WHOLE string is
      wrapped in exactly one more pair of parens than its content strictly
      needs (see :func:`parse_question_proof`'s docstring for the exact
      grammar, hand-derived from the fixture below).
  (b) for ``"Unknown"`` answers, a structurally DIFFERENT "deepest failure"
      witness: ``@N: <fact text>.[CWA. Example of deepest failure =
      (ruleK <- ruleJ <- … <- FAIL)]`` — a WALK-BACK chain of one or more
      candidate rules, each tried and abandoned because ITS body's own
      required atom was in turn undecidable (``ruleK`` is the rule whose
      head could have produced ``<fact text>``; a chain of length 1 is the
      common case, but real data goes up to at least 5 links deep — see
      :class:`FailWitness`) — or the base case
      ``@N: <fact text>.[CWA. Example of deepest failure = (FAIL)]`` (no
      candidate fact or rule head exists for ``<fact text>`` at all).

* ``"allProofs"`` (flat tasksource mirror, one string per THEORY, kept
  verbatim in ``meta["allProofs"]`` by :func:`~.proofwriter.load_proofwriter`
  and never otherwise touched) — a SEQUENCE of ``"@N: "``-headed sections
  (one per proof-depth stratum), each listing every fact derivable at that
  depth as ``"<fact text>.[<derivation>]"`` entries, space-separated. Every
  ``<derivation>`` observed here uses shape (a) above; shape (b) never
  appears in ``allProofs`` (it only lists facts that WERE derived, not
  questions that failed to derive).

Both fields are parsed by the SAME shape-(a) grammar
(:func:`_parse_derivation_string`); :func:`parse_question_proof` additionally
recognises shape (b), and :func:`parse_all_proofs` splits ``allProofs`` into
its per-depth sections before parsing each entry.

Grammar for shape (a), reverse-engineered here from the REAL fixture strings
in ``tests/fixtures/proofwriter_owa_mini.jsonl``/``proofwriter_cwa_mini.jsonl``
(every literal example in this docstring is copied verbatim from a fixture)
and confirmed against 390 additional real rows (5452 questions, every
published config) fetched from
``hitachi-nlp/proofwriter_processed_OWA`` (see ``check_gold_proof``'s test
coverage) — not guessed, worked out by matching parentheses one string at a
time::

    TopTerm ::= "(" OrExpr ")"          -- the whole annotation
    OrExpr  ::= Item ("OR" Item)*       -- a forest of alternative derivations
    Item    ::= LEAF | "NAF" | "(" Deriv ")"  -- LEAF/NAF bare, Deriv wrapped
    Deriv   ::= "(" Conj ")" "->" RULE  -- a rule applied to a conjunction
    Conj    ::= Item+                   -- one or more antecedents
    LEAF    ::= "triple" DIGIT+
    RULE    ::= "rule" DIGIT+

``NAF`` (a literal keyword, real CWA fixture
``tests/fixtures/proofwriter_cwa_mini.jsonl`` row ``RelNeg-CWA-D2-1420``
question ``Q4``: ``"[(((NAF) -> rule6))]"``) stands in for a ``tripleN``/
``ruleN`` reference at exactly one place: a rule's ``"~"``-polarity
(negation-as-failure) body condition the theory has no rule concluding the
negation of at all, so only the condition's plain ABSENCE justifies it, not
an explicit derivation — see :class:`Naf` and
:func:`.proofwriter.check_gold_proof`.

Worked examples (all four literally from the fixture, hand-parsed by
matching parens before this grammar was written down):

* ``"(triple6)"`` — TopTerm wraps a single bare LEAF: ``Leaf("triple6")``.
* ``"(((triple6) -> rule1))"`` — TopTerm wraps one Item, itself
  ``"(" Deriv ")"`` with ``Deriv = "(triple6) -> rule1"`` (Conj = one bare
  LEAF): ``Apply("rule1", And((Leaf("triple6"),)))``.
* ``"(((((triple6) -> rule1) triple5) -> rule3))"`` — the outer Deriv's Conj
  has TWO antecedents: the wrapped sub-derivation ``((triple6) -> rule1)``
  and the bare leaf ``triple5``:
  ``Apply("rule3", And((Apply("rule1", And((Leaf("triple6"),))), Leaf("triple5"))))``.
* ``"(triple1 OR ((triple2) -> rule1))"`` — an OrExpr with two alternatives,
  one bare LEAF and one wrapped Deriv:
  ``Or((Leaf("triple1"), Apply("rule1", And((Leaf("triple2"),)))))``.

An ``Or`` node is built only when there are two or more alternatives (a
single-alternative OrExpr collapses to that alternative directly, so the
tree never carries a spurious singleton ``Or``).
"""

import re
from dataclasses import dataclass
from typing import Dict, Tuple, Union

__all__ = [
    "Leaf", "Naf", "And", "Apply", "Or", "FailWitness", "ProofNode",
    "parse_question_proof", "parse_all_proofs",
]


# ---------------------------------------------------------------------------
# AST
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class Leaf:
    """A direct citation of one theory fact, e.g. ``Leaf("triple6")``."""
    ref: str


@dataclass(frozen=True)
class Naf:
    """One antecedent satisfied by NEGATION AS FAILURE, with no explicit
    fact/rule to cite: the literal ``"NAF"`` keyword real proofs use in
    place of a ``tripleN``/``ruleN`` reference for a ``"~"``-polarity body
    condition the theory has no rule concluding the negation of at all (so
    only its plain ABSENCE, not an explicit derivation, justifies it — see
    :func:`.proofwriter.check_gold_proof`'s docstring). Confirmed in the
    real ``AllenAI`` CWA fixture (``tests/fixtures/proofwriter_cwa_mini.jsonl``,
    row ``RelNeg-CWA-D2-1420``, question ``Q4``): ``"[(((NAF) -> rule6))]"``.
    A no-field marker — there is nothing else to record.
    """


@dataclass(frozen=True)
class And:
    """The conjunction of antecedents a rule application is over.

    ``parts`` is non-empty and ORDER-preserving (index ``i`` is the ``i``-th
    antecedent in the source string, matching the ``i``-th body literal of
    the corresponding rule — see :func:`.proofwriter._as_rule`).
    """
    parts: Tuple["ProofNode", ...]


@dataclass(frozen=True)
class Apply:
    """One rule application: ``rule`` (e.g. ``"rule3"``) applied to ``args``."""
    rule: str
    args: And


@dataclass(frozen=True)
class Or:
    """A forest of two or more ALTERNATIVE derivations of the same fact."""
    alts: Tuple["ProofNode", ...]


@dataclass(frozen=True)
class FailWitness:
    """The "deepest failure" witness ProofWriter records for an ``Unknown``
    answer: neither ``atom`` nor its negation could be derived, and this is
    ONE concrete reason why.

    ``rule_chain`` is the ordered walk-back of candidate rules the
    generator's search tried and abandoned: ``()`` for the bare ``(FAIL)``
    shape (no candidate fact or rule head existed for ``atom`` at all), or
    one-or-more rule names (e.g. ``("rule6", "rule2")`` for
    ``"(rule6 <- rule2 <- FAIL)"``) — ``rule_chain[0]`` is the rule whose
    HEAD could have produced ``atom``, ``rule_chain[1]`` is the rule that
    could have produced ITS unsatisfied body atom, and so on down to a final
    dead end. Confirmed against 300 real rows fetched from
    ``hitachi-nlp/proofwriter_processed_OWA`` (depth-0/1/2/3/5/NatLang) —
    the single-rule shape the fixture alone suggested is the ``len == 1``
    case of this more general chain, not the whole grammar.
    ``depth`` is the ``@N`` stratum the generator's search had reached.
    """
    atom: str
    rule_chain: Tuple[str, ...]
    depth: int


ProofNode = Union[Leaf, Naf, Apply, Or, FailWitness]


# ---------------------------------------------------------------------------
# Shape (a): the derivation-term grammar
# ---------------------------------------------------------------------------

_LEAF_RE = re.compile(r"triple\d+\Z")
_RULE_RE = re.compile(r"rule\d+\Z")
_TERM_TOKEN_RE = re.compile(r"\(|\)|->|OR|[A-Za-z][A-Za-z0-9]*")


def _tokenise_derivation(text: str) -> "list":
    tokens = _TERM_TOKEN_RE.findall(text)
    remainder = _TERM_TOKEN_RE.sub("", text).strip()
    if remainder:
        raise ValueError(
            f"proofwriter: unrecognised material {remainder!r} in proof "
            f"derivation {text!r} — outside the documented "
            "TopTerm/OrExpr/Item/Deriv/Conj grammar")
    return tokens


def _expect(tokens, pos, token, context):
    if pos >= len(tokens) or tokens[pos] != token:
        got = tokens[pos] if pos < len(tokens) else "<end>"
        raise ValueError(
            f"proofwriter: expected {token!r} {context}, got {got!r} in "
            f"proof derivation tokens {tokens!r}")


def _parse_item(tokens, pos):
    """``Item ::= LEAF | "NAF" | "(" Deriv ")"``."""
    if pos >= len(tokens):
        raise ValueError(
            f"proofwriter: proof derivation ends mid-item in {tokens!r}")
    token = tokens[pos]
    if token == "NAF":
        return Naf(), pos + 1
    if _LEAF_RE.match(token):
        return Leaf(token), pos + 1
    if token == "(":
        # This '(' is the Item's OWN wrapper -- Deriv has its own separate
        # leading '(' (for its Conj), consumed by _parse_deriv itself.
        node, pos = _parse_deriv(tokens, pos + 1)
        _expect(tokens, pos, ")", "to close an Item")
        return node, pos + 1
    if _RULE_RE.match(token):
        raise ValueError(
            f"proofwriter: rule reference {token!r} used where a fact/"
            f"derivation Item was expected in {tokens!r} — outside the "
            "documented grammar (a rule name only ever follows '->')")
    raise ValueError(
        f"proofwriter: {token!r} is not a well-formed Item (expected a "
        f"'tripleN' leaf or a parenthesised derivation) in {tokens!r}")


def _parse_deriv(tokens, pos):
    """``Deriv ::= "(" Conj ")" "->" RULE``, ``Conj ::= Item+``."""
    _expect(tokens, pos, "(", "to start a conjunction")
    pos += 1
    items = []
    while pos < len(tokens) and tokens[pos] != ")":
        item, pos = _parse_item(tokens, pos)
        items.append(item)
    if not items:
        raise ValueError(
            f"proofwriter: empty conjunction '()' in proof derivation "
            f"{tokens!r} — a rule application needs at least one antecedent")
    _expect(tokens, pos, ")", "to close a conjunction")
    pos += 1
    _expect(tokens, pos, "->", "after a conjunction")
    pos += 1
    if pos >= len(tokens) or not _RULE_RE.match(tokens[pos]):
        got = tokens[pos] if pos < len(tokens) else "<end>"
        raise ValueError(
            f"proofwriter: expected a 'ruleN' reference after '->', got "
            f"{got!r} in proof derivation {tokens!r}")
    rule = tokens[pos]
    return Apply(rule, And(tuple(items))), pos + 1


def _parse_or_expr(tokens, pos):
    """``OrExpr ::= Item ("OR" Item)*``."""
    alts = []
    item, pos = _parse_item(tokens, pos)
    alts.append(item)
    while pos < len(tokens) and tokens[pos] == "OR":
        pos += 1
        item, pos = _parse_item(tokens, pos)
        alts.append(item)
    if len(alts) == 1:
        return alts[0], pos
    return Or(tuple(alts)), pos


def _parse_derivation_string(text: str) -> "ProofNode":
    """``TopTerm ::= "(" OrExpr ")"`` over the WHOLE ``text``."""
    tokens = _tokenise_derivation(text)
    if not tokens:
        raise ValueError("proofwriter: empty proof derivation")
    _expect(tokens, 0, "(", "at the start of a proof derivation")
    node, pos = _parse_or_expr(tokens, 1)
    _expect(tokens, pos, ")", "to close the proof derivation")
    pos += 1
    if pos != len(tokens):
        raise ValueError(
            f"proofwriter: trailing tokens {tokens[pos:]!r} after a "
            f"complete proof derivation in {text!r}")
    return node


# ---------------------------------------------------------------------------
# Shape (b): the "deepest failure" witness
# ---------------------------------------------------------------------------

_FAIL_WITNESS_RE = re.compile(
    r"\A@(?P<depth>\d+):\s*(?P<atom>.+?)\.\[CWA\. Example of deepest "
    r"failure = \((?P<chain>(?:rule\d+ <- )*)FAIL\)\]\Z"
)
_CHAIN_RULE_RE = re.compile(r"rule\d+")


def _parse_fail_witness(text: str) -> "FailWitness":
    match = _FAIL_WITNESS_RE.match(text)
    if not match:
        raise ValueError(
            f"proofwriter: {text!r} starts with '@N:' but does not match "
            "the documented 'deepest failure' witness shape "
            "'@N: <fact>.[CWA. Example of deepest failure = "
            "(ruleK <- ruleJ <- … <- FAIL) | (FAIL)]'")
    chain = tuple(_CHAIN_RULE_RE.findall(match.group("chain")))
    return FailWitness(atom=match.group("atom"), rule_chain=chain,
                        depth=int(match.group("depth")))


# ---------------------------------------------------------------------------
# Public entry points
# ---------------------------------------------------------------------------

def parse_question_proof(text: str) -> "ProofNode":
    """One ``question["proofs"]`` string → a :data:`ProofNode`.

    Accepts both documented shapes: a bracketed derivation term (shape (a),
    → :class:`Leaf` / :class:`Apply` / :class:`Or`) and a bracketed "deepest
    failure" witness (shape (b), → :class:`FailWitness`). The distinguishing
    mark is the FIRST character inside the brackets: ``"@"`` selects shape
    (b), anything else shape (a) — exactly how the two shapes are told apart
    in the real data (a derivation never starts with ``"@"``, a witness
    always does).

    Args:
        text: the raw string, e.g. ``"[(triple6)]"`` or
            ``"[@0: Charlie is round.[CWA. Example of deepest failure = "
            "(FAIL)]]"``.

    Raises:
        ValueError: ``text`` is not wrapped in exactly one pair of ``[]``,
            its bracketed content matches neither documented shape, or it is
            the bare ``"[]"`` some hand-authored ``birds-electricity``/
            ``NatLang`` theories use for an ``"Unknown"`` question with NO
            recorded witness at all (confirmed against 30 real
            ``birds-electricity`` rows: 822 such cases, every one
            ``answer == "Unknown"`` — a real annotation shape, but one this
            grammar does not cover, so it is named and refused rather than
            silently treated as an empty derivation or a witness with no
            content). Every error names the unrecognised material or shape,
            never guesses.
    """
    if not (text.startswith("[") and text.endswith("]") and len(text) >= 2):
        raise ValueError(
            f"proofwriter: proof annotation {text!r} is not wrapped in "
            "'[...]' as every 'proofs' field value is in the fixtures "
            "checked here")
    inner = text[1:-1]
    if inner == "":
        raise ValueError(
            "proofwriter: proof annotation '[]' carries no derivation and "
            "no failure witness (seen in the hand-authored birds-electricity/"
            "NatLang configs for some 'Unknown' questions) — outside the "
            "documented derivation/failure-witness grammar; refusing rather "
            "than guessing at a reason")
    if inner.startswith("@"):
        return _parse_fail_witness(inner)
    return _parse_derivation_string(inner)


_SECTION_RE = re.compile(r"@(\d+):")
_ALLPROOFS_ENTRY_RE = re.compile(r"\s*(?P<text>.+?\.)\[(?P<term>[^\[\]]*)\]")


def parse_all_proofs(text: str) -> "Dict[int, Dict[str, ProofNode]]":
    """The theory-wide ``allProofs`` string → ``{depth: {fact_text: node}}``.

    ``allProofs`` (see :mod:`.proofwriter`'s module docstring — carried
    verbatim in ``meta["allProofs"]`` by :func:`~.proofwriter.load_proofwriter`
    and never otherwise parsed there) lists, for each proof-depth stratum
    ``@N``, every fact derivable at that depth as ``"<fact text>.[<term>]"``
    entries; every ``<term>`` observed here is shape (a) (see module
    docstring) — this function does not expect shape (b) inside ``allProofs``
    and raises if one is found (``allProofs`` only records SUCCESSFUL
    derivations, never failure witnesses).

    This is a STANDALONE parse: ``load_proofwriter`` generates no FOL for
    these theories (see its docstring's "Honesty" section), so there is
    nothing to cross-check an ``allProofs`` derivation against — unlike
    :func:`.proofwriter.check_gold_proof`, which verifies
    ``question["proofs"]`` from the structured route against the kit's own
    forward-chaining fixpoint.

    Raises:
        ValueError: ``text`` contains material outside the
            ``"@N: fact.[term] fact.[term] …"`` shape, naming the
            unrecognised fragment and its stratum.
    """
    result: "Dict[int, Dict[str, ProofNode]]" = {}
    sections = list(_SECTION_RE.finditer(text))
    if not sections:
        raise ValueError(
            f"proofwriter: allProofs string has no '@N:' section header at "
            f"all: {text!r}")
    for index, marker in enumerate(sections):
        depth = int(marker.group(1))
        start = marker.end()
        end = sections[index + 1].start() if index + 1 < len(sections) else len(text)
        section = text[start:end]
        entries: "Dict[str, ProofNode]" = {}
        pos = 0
        for entry in _ALLPROOFS_ENTRY_RE.finditer(section):
            if entry.start() != pos:
                raise ValueError(
                    f"proofwriter: unrecognised material "
                    f"{section[pos:entry.start()]!r} in allProofs @{depth} "
                    f"section {section!r}")
            fact_text = entry.group("text")
            term = entry.group("term")
            if term.strip().startswith("@"):
                raise ValueError(
                    f"proofwriter: allProofs entry for {fact_text!r} at "
                    f"@{depth} looks like a failure witness ({term!r}), "
                    "which allProofs is not documented to ever contain")
            entries[fact_text] = _parse_derivation_string(term)
            pos = entry.end()
        if section[pos:].strip():
            raise ValueError(
                f"proofwriter: unrecognised trailing material "
                f"{section[pos:]!r} in allProofs @{depth} section")
        result[depth] = entries
    return result
