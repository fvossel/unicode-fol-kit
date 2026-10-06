r"""Two routes, one verdict: the axiom-kind table made checkable.

The kit answers a question about a DL knowledge base two ways — the in-house
tableau (``dl.concept_satisfiable``/``dl.abox_consistent`` and everything that
reduces to them) and the FOL image (``dl.kb_to_fol`` handed to ``api.prove``).
They must never answer the same question differently, and the shape that
failure takes in practice is not a wrong rule: it is an axiom kind ONE route
knows about. The FOL route renders it, the tableau ignores it, and the two
disagree for a reason no test was looking at.

``dl.tableau._AXIOM_KINDS`` is the single table that makes that impossible to
do by accident: one row per axiom kind a ``TBox``/``ABox`` can hold, saying
what each route does with it. This file is the table's enforcement, and every
test here is parametrised over it, so a row added without a decision about
both routes goes red:

* ``test_every_tbox_and_abox_field_has_a_row`` — the meta-test. A field added
  to ``TBox`` or ``ABox`` with no row fails HERE, which is the mechanism that
  makes the policy un-forgettable.
* ``test_every_axiom_kind_has_hand_derived_test_data`` — the same guard for
  this file's own ``_CASES``: a row whose behaviour nobody wrote down is a row
  nothing below actually checks.
* ``test_builders_never_refuse`` — ``TBox.add_*``/``ABox.assert_*`` accept
  every kind. A builder that refuses cannot hold an ontology read from a file.
* ``test_the_tableau_claim_is_true`` / ``test_the_fol_claim_is_true`` — each
  row's two claims, against the real code.
* ``test_the_two_routes_agree`` — per kind, a hand-derived ENTAILMENT and its
  NON-entailment twin, each asked of both routes, asserting the two verdicts
  agree. This is the test the table exists for.
* ``test_the_shared_guard_is_reached_from_both_entry_points`` — the seam
  itself. With the kinds that exist today nothing is refused, so the guard is
  a no-op; this test makes a row refused and checks both entry points raise.
* ``test_every_refused_kind_is_refused_by_the_sweeps_with_nothing_to_sweep`` —
  the same guard from the entry points that can return without a single
  reduction (``realize``/``realize_all``/``instance_retrieval``/``classify``
  with an empty vocabulary or ABox), for EVERY refused row of the table.
* the consumer tests — ``dl.to_owl_functional``, ``hets.owl_backend``,
  ``mcp.server``'s row shapes and ``dl.owl_reasoner`` all read a ``TBox``
  field by field, and an oracle that silently drops an axiom agrees with the
  tableau for the WRONG reason, which is worse than disagreeing.

Every expected formula below is hand-derived from the OWL 2 direct semantics
and the standard translation, written out in the comment above it — never read
off what the code prints.
"""

import dataclasses
from typing import get_origin

import pytest

import unicode_fol_kit.dl as dl
from unicode_fol_kit import api
from unicode_fol_kit.dl import owl_reasoner as _owl_reasoner
from unicode_fol_kit.dl import tableau as _tableau
from unicode_fol_kit.dl.tableau import _AXIOM_KINDS, _AxiomKind
from unicode_fol_kit.fol.nodes import Not as FNot
from unicode_fol_kit.hets import owl_backend as _hets_owl
from unicode_fol_kit.mcp.server import _build_dl_abox, _build_dl_tbox

# A vocabulary whose every name reads back through api.parse_any: classes and
# roles upper-case (the kit's PREDICATE terminal), individuals lower-case (its
# NAME terminal). See tests/test_printed_text_reads_back.py for why that is a
# property of the VOCABULARY and not of the translation.
ALPHA, BETA, GAMMA = dl.Atomic("Alpha"), dl.Atomic("Beta"), dl.Atomic("Gamma")
PART, OVER = "HasPart", "Overlaps"
# The rest of the OWL 2 role box needs role names of its own, so each kind's
# sample TBox carries exactly ONE axiom and no accidental interaction.
SINK, SOURCE = "HasSink", "HasSource"
INPUT, CONN, STATE = "HasPhysicalInput", "IsConnectedTo", "HasState"
PARTOF = "PartOf"
ABOUT, COVERS, SHORT = "IsAbout", "Covers", "CoversShortcut"
# The data layer: two data properties, a user-defined datatype and the data
# domain. Upper-case so every image reads back through api.parse_any; a datatype
# of the OWL 2 map (`xsd:integer`) would print as a name the grammar cannot read,
# which is the documented limit tested in tests/test_printed_text_reads_back.py,
# so the samples use the user-defined `Digit` wherever the image is printed.
HA, HT = "HasAmount", "HasTotal"
DIGIT = dl.Datatype("Digit")
ANY = dl.Datatype("rdfs:Literal")


def _int(value) -> dl.Literal:
    return dl.Literal(str(value), "xsd:integer")

# Not a shrunken budget: a tiny timeout makes a backend answer "unknown", which
# several APIs report as "not valid" — so a non-entailment test with a 2 ms
# budget asserts nothing at all. Wider than the 10 s default, because this file
# asks ~30 questions and a slow machine must not turn an agreement into a
# disagreement.
TIMEOUT_MS = 30000


def _status(goal, premises) -> str:
    return api.prove(goal, list(premises), timeout=TIMEOUT_MS).status


# --------------------------------------------------------------------------- #
# Per-kind test data. One entry per row of _AXIOM_KINDS; the meta-test below
# fails if the two sets drift apart.
# --------------------------------------------------------------------------- #

@dataclasses.dataclass(frozen=True)
class _Question:
    """One question, with the answer derived by hand, to be asked of BOTH routes.

    ``form`` picks the pair of entry points:

    * ``"subsumes"`` — ``dl.subsumes(sub, sup, tbox)`` against
      ``api.prove(subsumption_to_fol(sub, sup), kb.tbox_premises)``.
    * ``"instance"`` — ``dl.instance_check(abox, ind, concept, tbox)`` against
      ``api.prove(abox_to_fol(ABox().assert_concept(ind, concept)), kb.premises)``.
    * ``"consistent"`` — ``dl.abox_consistent(abox, tbox)`` against
      ``api.prove(Not(kb.formula), kb.axioms)``.

    ``holds`` is the hand-derived answer; the FOL verdict that agrees with it
    is computed from ``form``, not listed, so the two cannot be written
    inconsistently.
    """

    label: str
    form: str
    build: object            # () -> (tbox|None, abox|None)
    query: tuple             # ("subsumes", sub, sup) / ("instance", ind, concept) / ()
    holds: bool


@dataclasses.dataclass(frozen=True)
class _Case:
    """Everything this file needs to know about one axiom kind."""

    sample: object           # () -> (tbox, abox), carrying exactly ONE axiom of the kind
    builder_args: tuple      # the arguments its builder method takes
    image: str               # the hand-derived FOL image of that one axiom
    mcp_tbox: object = None  # the MCP row list that expresses it, or None
    mcp_abox: object = None  # _build_dl_abox KWARGS for an ABox kind, or None
    questions: tuple = ()


def _tb(*calls):
    """A fresh TBox with ``calls`` applied — ``("add", (sub, sup))`` style."""
    def build():
        tbox = dl.TBox()
        for name, args in calls:
            getattr(tbox, name)(*args)
        return tbox
    return build


def _ab(*calls):
    """A fresh ABox with ``calls`` applied."""
    def build():
        abox = dl.ABox()
        for name, args in calls:
            getattr(abox, name)(*args)
        return abox
    return build


def _pair(tbox_build=None, abox_build=None):
    return lambda: (tbox_build() if tbox_build else None,
                    abox_build() if abox_build else None)


_CASES = {
    # OWL 2 direct semantics: SubClassOf(C D) holds iff C^I ⊆ D^I. The standard
    # translation of that inclusion is its universal closure, and π(Atomic A, x)
    # is the unary atom A(x) — so Alpha ⊑ Beta is ∀x (Alpha(x) → Beta(x)).
    "SubClassOf": _Case(
        sample=_pair(_tb(("add", (ALPHA, BETA)))),
        builder_args=(ALPHA, BETA),
        image="∀x (Alpha(x) → Beta(x))",
        mcp_tbox=[{"sub": "Alpha", "sup": "Beta"}],
        questions=(
            # ⊆ is transitive: Alpha ⊆ Beta ⊆ Gamma gives Alpha ⊆ Gamma in EVERY
            # model, so Alpha ⊑ Gamma is entailed.
            _Question("alpha-subsumed-by-gamma", "subsumes",
                      _pair(_tb(("add", (ALPHA, BETA)), ("add", (BETA, GAMMA)))),
                      ("subsumes", ALPHA, GAMMA), True),
            # The converse is not: take Alpha^I = Beta^I = ∅ and Gamma^I = {d}.
            # Both inclusions hold (∅ ⊆ ∅, ∅ ⊆ {d}); Gamma ⊆ Alpha does not.
            _Question("gamma-not-subsumed-by-alpha", "subsumes",
                      _pair(_tb(("add", (ALPHA, BETA)), ("add", (BETA, GAMMA)))),
                      ("subsumes", GAMMA, ALPHA), False),
        ),
    ),
    # EquivalentClasses(C D) holds iff C^I = D^I, i.e. iff BOTH inclusions hold;
    # TBox.add_equivalence stores exactly that pair, so the image is the two
    # universal closures conjoined.
    "EquivalentClasses": _Case(
        sample=_pair(_tb(("add_equivalence", (ALPHA, BETA)))),
        builder_args=(ALPHA, BETA),
        image="∀x (Alpha(x) → Beta(x)) ∧ ∀x (Beta(x) → Alpha(x))",
        mcp_tbox=[{"equiv": ["Alpha", "Beta"]}],
        questions=(
            # Gamma ⊆ Beta and Beta = Alpha give Gamma ⊆ Alpha — and this needs
            # the BACKWARD half of the equivalence, the one `add` alone would
            # not have stored.
            _Question("gamma-subsumed-by-alpha", "subsumes",
                      _pair(_tb(("add_equivalence", (ALPHA, BETA)), ("add", (GAMMA, BETA)))),
                      ("subsumes", GAMMA, ALPHA), True),
            # Not the converse: Alpha^I = Beta^I = {d}, Gamma^I = ∅ satisfies
            # both axioms, and Alpha ⊆ Gamma fails.
            _Question("alpha-not-subsumed-by-gamma", "subsumes",
                      _pair(_tb(("add_equivalence", (ALPHA, BETA)), ("add", (GAMMA, BETA)))),
                      ("subsumes", ALPHA, GAMMA), False),
        ),
    ),
    # SubObjectPropertyOf(P Q) holds iff P^I ⊆ Q^I as sets of PAIRS, so the
    # closure is over two variables: ∀x ∀y (P(x, y) → Q(x, y)).
    "SubObjectPropertyOf": _Case(
        sample=_pair(_tb(("add_role_inclusion", (PART, OVER)))),
        builder_args=(PART, OVER),
        image="∀x ∀y (HasPart(x, y) → Overlaps(x, y))",
        mcp_tbox=[{"subrole": "HasPart", "suprole": "Overlaps"}],
        questions=(
            # d ∈ Alpha gives some e with (d, e) ∈ HasPart and e ∈ Beta; the role
            # inclusion makes (d, e) ∈ Overlaps too, so d ∈ (∃Overlaps.Beta)^I.
            _Question("existential-rises-to-the-super-role", "subsumes",
                      _pair(_tb(("add", (ALPHA, dl.Exists(PART, BETA))),
                                ("add_role_inclusion", (PART, OVER)))),
                      ("subsumes", ALPHA, dl.Exists(OVER, BETA)), True),
            # Not into an unrelated class: domain {d, e}, Alpha = {d}, Beta = {e},
            # Gamma = ∅, HasPart = Overlaps = {(d, e)} satisfies both axioms, and
            # d has no Overlaps-successor in Gamma = ∅.
            _Question("but-not-into-an-unrelated-class", "subsumes",
                      _pair(_tb(("add", (ALPHA, dl.Exists(PART, BETA))),
                                ("add_role_inclusion", (PART, OVER)))),
                      ("subsumes", ALPHA, dl.Exists(OVER, GAMMA)), False),
        ),
    ),
    # TransitiveObjectProperty(P) holds iff P^I is transitive:
    # ∀x ∀y ∀z (P(x, y) ∧ P(y, z) → P(x, z)).
    "TransitiveObjectProperty": _Case(
        sample=_pair(_tb(("add_transitive_role", (PART,)))),
        builder_args=(PART,),
        image="∀x ∀y ∀z (HasPart(x, y) ∧ HasPart(y, z) → HasPart(x, z))",
        mcp_tbox=[{"transitive": "HasPart"}],
        questions=(
            # d ∈ Alpha gives (d, e), (e, f) ∈ HasPart with f ∈ Beta. Only
            # transitivity puts (d, f) in HasPart, which is what makes
            # d ∈ (∃HasPart.Beta)^I — without it, s = {(d, e), (e, f)} with
            # Beta = {f} is a counter-model.
            _Question("transitivity-shortens-the-chain", "subsumes",
                      _pair(_tb(("add", (ALPHA, dl.Exists(PART, dl.Exists(PART, BETA)))),
                                ("add_transitive_role", (PART,)))),
                      ("subsumes", ALPHA, dl.Exists(PART, BETA)), True),
            # Still nothing about an unrelated class: the transitive closure
            # {(d, e), (e, f), (d, f)} with Beta = {f}, Gamma = ∅ satisfies both
            # axioms and leaves d with no HasPart-successor in Gamma.
            _Question("but-not-into-an-unrelated-class", "subsumes",
                      _pair(_tb(("add", (ALPHA, dl.Exists(PART, dl.Exists(PART, BETA)))),
                                ("add_transitive_role", (PART,)))),
                      ("subsumes", ALPHA, dl.Exists(PART, GAMMA)), False),
        ),
    ),
    # DisjointObjectProperties(P Q) holds iff P^I ∩ Q^I = ∅ as sets of pairs,
    # so the closure is the negated conjunction over two variables:
    # ∀x ∀y ¬(P(x, y) ∧ Q(x, y)). Stored as SORTED pairs, all C(k, 2) of them
    # for a k-ary axiom — disjointness has no transitive shortcut.
    "DisjointObjectProperties": _Case(
        sample=_pair(_tb(("add_disjoint_roles", (SINK, SOURCE)))),
        builder_args=(SINK, SOURCE),
        image="∀x ∀y ¬(HasSink(x, y) ∧ HasSource(x, y))",
        mcp_tbox=[{"disjointroles": [SINK, SOURCE]}],
        questions=(
            # HasSink ⊑ HasSource makes every HasSink pair a HasSource pair too,
            # so such a pair is in BOTH — which disjointness forbids. Hence no
            # HasSink pair exists at all: ∃HasSink.⊤ is empty.
            _Question("hierarchy-plus-disjointness-empties-the-sub-role", "subsumes",
                      _pair(_tb(("add_role_inclusion", (SINK, SOURCE)),
                                ("add_disjoint_roles", (SINK, SOURCE)))),
                      ("subsumes", dl.Exists(SINK, dl.Top()), dl.Bottom()), True),
            # Disjointness ALONE empties nothing: domain {d, e} with
            # HasSink = {(d, e)} and HasSource = ∅ satisfies the axiom, and
            # d ∈ (∃HasSink.⊤)^I.
            _Question("disjointness-alone-empties-nothing", "subsumes",
                      _pair(_tb(("add_disjoint_roles", (SINK, SOURCE)))),
                      ("subsumes", dl.Exists(SINK, dl.Top()), dl.Bottom()), False),
        ),
    ),
    # AsymmetricObjectProperty(P): <x,y> ∈ P^I implies <y,x> ∉ P^I, i.e.
    # ∀x ∀y (P(x, y) → ¬P(y, x)). Note it ENTAILS irreflexivity — instantiate
    # y := x and read off ¬P(x, x).
    "AsymmetricObjectProperty": _Case(
        sample=_pair(_tb(("add_asymmetric_role", (INPUT,)))),
        builder_args=(INPUT,),
        image="∀x ∀y (HasPhysicalInput(x, y) → ¬HasPhysicalInput(y, x))",
        mcp_tbox=[{"asymmetric": INPUT}],
        questions=(
            # Both directions asserted: the axiom instantiated at
            # (alice, bob) forbids the second edge, so there is no model.
            _Question("a-two-cycle-has-no-model", "consistent",
                      _pair(_tb(("add_asymmetric_role", (INPUT,))),
                            _ab(("assert_role", ("alice", "bob", INPUT)),
                                ("assert_role", ("bob", "alice", INPUT)))),
                      (), False),
            # One edge is fine: HasPhysicalInput = {(alice, bob)} with
            # alice ≠ bob satisfies the axiom.
            _Question("one-edge-is-fine", "consistent",
                      _pair(_tb(("add_asymmetric_role", (INPUT,))),
                            _ab(("assert_role", ("alice", "bob", INPUT)))),
                      (), True),
        ),
    ),
    # IrreflexiveObjectProperty(P): <x,x> ∉ P^I for every x, i.e. ∀x ¬P(x, x)
    # — ONE variable and no second quantifier, the only role-box image in the
    # package that is not a two- or three-variable sentence.
    "IrreflexiveObjectProperty": _Case(
        sample=_pair(_tb(("add_irreflexive_role", (INPUT,)))),
        builder_args=(INPUT,),
        image="∀x ¬HasPhysicalInput(x, x)",
        mcp_tbox=[{"irreflexive": INPUT}],
        questions=(
            # The axiom at x := alice forbids the asserted self-loop outright.
            _Question("a-self-loop-has-no-model", "consistent",
                      _pair(_tb(("add_irreflexive_role", (INPUT,))),
                            _ab(("assert_role", ("alice", "alice", INPUT)))),
                      (), False),
            # An edge between two NAMES is fine — and stays fine without a
            # unique name assumption, because a model may read them apart:
            # Δ = {d, e}, alice = d, bob = e, HasPhysicalInput = {(d, e)}.
            _Question("an-edge-between-two-names-is-fine", "consistent",
                      _pair(_tb(("add_irreflexive_role", (INPUT,))),
                            _ab(("assert_role", ("alice", "bob", INPUT)))),
                      (), True),
        ),
    ),
    # FunctionalObjectProperty(P): P^I is functional, i.e.
    # ∀x ∀y ∀z (P(x, y) ∧ P(x, z) → y = z). Rendered as the direct-semantics
    # equality sentence rather than as the Count image of ≤1 P.⊤; the two are
    # interderivable, and the tableau uses the latter (see _new_branch).
    "FunctionalObjectProperty": _Case(
        sample=_pair(_tb(("add_functional_role", (STATE,)))),
        builder_args=(STATE,),
        image="∀x ∀y ∀z (HasState(x, y) ∧ HasState(x, z) → y = z)",
        mcp_tbox=[{"functional": STATE}],
        questions=(
            # d has a HasState-successor in Alpha and one in Beta;
            # functionality identifies them, so that single successor is in
            # BOTH — which is exactly ∃HasState.(Alpha ⊓ Beta).
            _Question("two-successors-must-be-one", "subsumes",
                      _pair(_tb(("add_functional_role", (STATE,)))),
                      ("subsumes", dl.And(dl.Exists(STATE, ALPHA), dl.Exists(STATE, BETA)),
                       dl.Exists(STATE, dl.And(ALPHA, BETA))), True),
            # But it says nothing about an unrelated class: Δ = {d, e},
            # HasState = {(d, e)}, Alpha = {e}, Beta = ∅ is functional, and
            # d has no HasState-successor in Beta.
            _Question("but-nothing-about-an-unrelated-class", "subsumes",
                      _pair(_tb(("add_functional_role", (STATE,)))),
                      ("subsumes", dl.Exists(STATE, ALPHA), dl.Exists(STATE, BETA)), False),
        ),
    ),
    # InverseObjectProperties(P Q) asserts (P)^OP = ((Q)^OP)^-, i.e.
    # <x,y> ∈ P^I iff <y,x> ∈ Q^I. ONE biconditional, not two inclusions: the
    # axiom is an EQUALITY of relations. REFUSED by the tableau (the I of SHIQ).
    "InverseObjectProperties": _Case(
        sample=_pair(_tb(("add_inverse_roles", (PARTOF, PART)))),
        builder_args=(PARTOF, PART),
        image="∀x ∀y (PartOf(x, y) ↔ HasPart(y, x))",
        mcp_tbox=[{"inverseroles": [PARTOF, PART]}],
        questions=(
            # PartOf(alice, bob) and the biconditional at (alice, bob) give
            # HasPart(bob, alice), so bob has a HasPart-successor.
            _Question("the-converse-edge-exists-at-the-other-end", "instance",
                      _pair(_tb(("add_inverse_roles", (PARTOF, PART))),
                            _ab(("assert_role", ("alice", "bob", PARTOF)))),
                      ("instance", "bob", dl.Exists(PART, dl.Top())), True),
            # Not at THIS end: Δ = {a, b}, PartOf = {(a, b)},
            # HasPart = {(b, a)} satisfies the axiom and leaves alice = a with
            # no outgoing HasPart edge.
            _Question("but-not-at-this-end", "instance",
                      _pair(_tb(("add_inverse_roles", (PARTOF, PART))),
                            _ab(("assert_role", ("alice", "bob", PARTOF)))),
                      ("instance", "alice", dl.Exists(PART, dl.Top())), False),
        ),
    ),
    # SymmetricObjectProperty(P): <x,y> ∈ P^I implies <y,x> ∈ P^I. The
    # implication, not a biconditional — the converse implication is the same
    # sentence with x and y renamed. REFUSED by the tableau: this IS P ⊑ P⁻.
    "SymmetricObjectProperty": _Case(
        sample=_pair(_tb(("add_symmetric_role", (CONN,)))),
        builder_args=(CONN,),
        image="∀x ∀y (IsConnectedTo(x, y) → IsConnectedTo(y, x))",
        mcp_tbox=[{"symmetric": CONN}],
        questions=(
            _Question("the-edge-runs-both-ways", "instance",
                      _pair(_tb(("add_symmetric_role", (CONN,))),
                            _ab(("assert_role", ("alice", "bob", CONN)))),
                      ("instance", "bob", dl.Exists(CONN, dl.Top())), True),
            # The converse edge lands on alice, and nothing puts alice in
            # Gamma: Gamma = ∅ is a model.
            _Question("and-carries-nothing-else", "instance",
                      _pair(_tb(("add_symmetric_role", (CONN,))),
                            _ab(("assert_role", ("alice", "bob", CONN)))),
                      ("instance", "bob", dl.Exists(CONN, GAMMA)), False),
        ),
    ),
    # ReflexiveObjectProperty(P): <x,x> ∈ P^I for every x of the (never empty)
    # domain, i.e. ∀x P(x, x). Unlike Asymmetric/Irreflexive this FORCES an
    # edge rather than forbidding one, which is why it is the expensive one.
    # REFUSED by the tableau (the counting side; see dl/tableau.py).
    "ReflexiveObjectProperty": _Case(
        sample=_pair(_tb(("add_reflexive_role", (OVER,)))),
        builder_args=(OVER,),
        image="∀x Overlaps(x, x)",
        mcp_tbox=[{"reflexive": OVER}],
        questions=(
            # x is its own Overlaps-neighbour, so ∀Overlaps.Alpha at x forces
            # Alpha onto x itself.
            _Question("a-value-restriction-falls-on-the-node-itself", "subsumes",
                      _pair(_tb(("add_reflexive_role", (OVER,)))),
                      ("subsumes", dl.ForAll(OVER, ALPHA), ALPHA), True),
            # Not the other way round: Δ = {d, e},
            # Overlaps = {(d, d), (e, e), (d, e)}, Alpha = {d} is reflexive, and
            # d ∈ Alpha has an Overlaps-successor e ∉ Alpha.
            _Question("not-the-other-way-round", "subsumes",
                      _pair(_tb(("add_reflexive_role", (OVER,)))),
                      ("subsumes", ALPHA, dl.ForAll(OVER, ALPHA)), False),
        ),
    ),
    # InverseFunctionalObjectProperty(P): ((P)^OP)^- is functional, i.e.
    # ∀x ∀y ∀z (P(y, x) ∧ P(z, x) → y = z). The argument order of the two body
    # atoms is the whole difference from FunctionalObjectProperty, and the whole
    # content of the axiom. REFUSED by the tableau: it is ≤1 P⁻.⊤.
    "InverseFunctionalObjectProperty": _Case(
        sample=_pair(_tb(("add_inverse_functional_role", (STATE,)))),
        builder_args=(STATE,),
        image="∀x ∀y ∀z (HasState(y, x) ∧ HasState(z, x) → y = z)",
        mcp_tbox=[{"inversefunctional": STATE}],
        questions=(
            # alice and bob are both HasState-predecessors of carol, so the
            # axiom identifies them — and they are FORCED distinct.
            _Question("two-distinct-predecessors-have-no-model", "consistent",
                      _pair(_tb(("add_inverse_functional_role", (STATE,))),
                            _ab(("assert_role", ("alice", "carol", STATE)),
                                ("assert_role", ("bob", "carol", STATE)),
                                ("assert_distinct", ("alice", "bob")))),
                      (), False),
            # Without the distinctness they simply merge: there is no unique
            # name assumption, so alice and bob may denote one element.
            _Question("without-the-distinctness-they-merge", "consistent",
                      _pair(_tb(("add_inverse_functional_role", (STATE,))),
                            _ab(("assert_role", ("alice", "carol", STATE)),
                                ("assert_role", ("bob", "carol", STATE)))),
                      (), True),
        ),
    ),
    # SubObjectPropertyOf(ObjectPropertyChain(P1 P2) Q) holds iff for every
    # y0, y1, y2 with <y0,y1> ∈ P1^I and <y1,y2> ∈ P2^I we have <y0,y2> ∈ Q^I:
    # ∀x ∀y ∀z (P1(x, y) ∧ P2(y, z) → Q(x, z)). The three variables are the
    # same ones transitivity uses, and transitivity IS the chain r ∘ r ⊑ r.
    # REFUSED by the tableau (the R of SROIQ; see dl/tableau.py for the rule
    # that would decide it and the regularity problem that defers it).
    "ObjectPropertyChain": _Case(
        sample=_pair(_tb(("add_role_chain", ((ABOUT, COVERS), SHORT)))),
        builder_args=((ABOUT, COVERS), SHORT),
        image="∀x ∀y ∀z (IsAbout(x, y) ∧ Covers(y, z) → CoversShortcut(x, z))",
        mcp_tbox=[{"chain": [ABOUT, COVERS], "suprole": SHORT}],
        questions=(
            # d —IsAbout→ e —Covers→ f is exactly the chain's antecedent, so
            # <d, f> ∈ CoversShortcut^I and d ∈ (∃CoversShortcut.⊤)^I.
            _Question("the-two-hop-path-is-a-super-role-edge", "subsumes",
                      _pair(_tb(("add_role_chain", ((ABOUT, COVERS), SHORT)))),
                      ("subsumes", dl.Exists(ABOUT, dl.Exists(COVERS, dl.Top())),
                       dl.Exists(SHORT, dl.Top())), True),
            # But into an unrelated class, no: the chain says where the edge
            # goes, not what is there — Gamma = ∅ is a model.
            _Question("but-not-into-an-unrelated-class", "subsumes",
                      _pair(_tb(("add_role_chain", ((ABOUT, COVERS), SHORT)))),
                      ("subsumes", dl.Exists(ABOUT, dl.Exists(COVERS, dl.Top())),
                       dl.Exists(SHORT, GAMMA)), False),
        ),
    ),
    # ClassAssertion(C a) holds iff a^I ∈ C^I, i.e. π(C, a) with the individual
    # as a CONSTANT: Alpha(alice).
    "ClassAssertion": _Case(
        sample=_pair(abox_build=_ab(("assert_concept", ("alice", ALPHA)))),
        builder_args=("alice", ALPHA),
        image="Alpha(alice)",
        mcp_abox={"concepts": [["alice", "Alpha"]]},
        questions=(
            # alice ∈ Alpha ⊆ Beta in every model, so alice : Beta is entailed.
            _Question("the-gci-classifies-the-individual", "instance",
                      _pair(_tb(("add", (ALPHA, BETA))),
                            _ab(("assert_concept", ("alice", ALPHA)))),
                      ("instance", "alice", BETA), True),
            # Open world: Alpha = Beta = {alice}, Gamma = ∅ is a model, so
            # alice : Gamma is not entailed (and not refuted either — it is
            # simply not known).
            _Question("but-not-an-unrelated-class", "instance",
                      _pair(_tb(("add", (ALPHA, BETA))),
                            _ab(("assert_concept", ("alice", ALPHA)))),
                      ("instance", "alice", GAMMA), False),
        ),
    ),
    # ObjectPropertyAssertion(P a b) holds iff (a^I, b^I) ∈ P^I: HasPart(alice, bob).
    "ObjectPropertyAssertion": _Case(
        sample=_pair(abox_build=_ab(("assert_role", ("alice", "bob", PART)))),
        builder_args=("alice", "bob", PART),
        image="HasPart(alice, bob)",
        mcp_abox={"roles": [["alice", "bob", "HasPart"]]},
        questions=(
            # alice ∈ Alpha ⊆ ∀HasPart.Beta and (alice, bob) ∈ HasPart force
            # bob ∈ Beta — the ∀-restriction travels along the asserted edge.
            _Question("the-value-restriction-travels-along-the-edge", "instance",
                      _pair(_tb(("add", (ALPHA, dl.ForAll(PART, BETA)))),
                            _ab(("assert_concept", ("alice", ALPHA)),
                                ("assert_role", ("alice", "bob", PART)))),
                      ("instance", "bob", BETA), True),
            # Nothing says bob ∈ Gamma: Alpha = {alice}, Beta = {bob}, Gamma = ∅,
            # HasPart = {(alice, bob)} is a model.
            _Question("but-carries-nothing-else", "instance",
                      _pair(_tb(("add", (ALPHA, dl.ForAll(PART, BETA)))),
                            _ab(("assert_concept", ("alice", ALPHA)),
                                ("assert_role", ("alice", "bob", PART)))),
                      ("instance", "bob", GAMMA), False),
        ),
    ),
    # DifferentIndividuals(a b) holds iff a^I ≠ b^I, which the kit renders as the
    # FOL atom a ≠ b directly. There is no unique name assumption, so this is the
    # only thing that ever forces two individuals apart.
    "DifferentIndividuals": _Case(
        sample=_pair(abox_build=_ab(("assert_distinct", ("alice", "bob")))),
        builder_args=("alice", "bob"),
        image="alice ≠ bob",
        mcp_abox={"distinct": [["alice", "bob"]]},
        questions=(
            # alice ∈ Alpha ⊆ ≤1 HasPart.⊤ allows at most one HasPart-successor,
            # but bob and carol are both successors and are FORCED distinct — so
            # there are two, and the knowledge base has no model.
            _Question("distinctness-breaks-the-at-most-one", "consistent",
                      _pair(_tb(("add", (ALPHA, dl.AtMost(1, PART, dl.Top())))),
                            _ab(("assert_concept", ("alice", ALPHA)),
                                ("assert_role", ("alice", "bob", PART)),
                                ("assert_role", ("alice", "carol", PART)),
                                ("assert_distinct", ("bob", "carol")))),
                      (), False),
            # Drop one of the two edges and the same distinctness is harmless:
            # alice has one successor, and carol need not be one at all.
            _Question("one-successor-and-the-same-distinctness-is-fine", "consistent",
                      _pair(_tb(("add", (ALPHA, dl.AtMost(1, PART, dl.Top())))),
                            _ab(("assert_concept", ("alice", ALPHA)),
                                ("assert_role", ("alice", "bob", PART)),
                                ("assert_distinct", ("bob", "carol")))),
                      (), True),
        ),
    ),
    # ObjectPropertyDomain(P C) is satisfied iff for all <x,y> in P^OP we have
    # x in C^C -- literally the two-variable closure
    # forall x forall y (P(x, y) -> pi(C, x)). The equivalent GCI
    # ExistsP.Top <= C would print the tautological `x0 = x0` filler the
    # requesting project complained about, so the image is the direct form and
    # the axiom is stored natively (dl.TBox.add_role_domain).
    "ObjectPropertyDomain": _Case(
        sample=_pair(_tb(("add_role_domain", (COVERS, ALPHA)))),
        builder_args=(COVERS, ALPHA),
        image="∀x ∀y (Covers(x, y) → Alpha(x))",
        mcp_tbox=[{"domainrole": COVERS, "domain": "Alpha"}],
        questions=(
            # d in (ExistsCovers.Top)^I gives some e with (d, e) in Covers; the
            # axiom instantiated at (d, e) puts d in Alpha. So the subsumption
            # holds in every model.
            _Question("a-covers-successor-forces-the-domain", "subsumes",
                      _pair(_tb(("add_role_domain", (COVERS, ALPHA)))),
                      ("subsumes", dl.Exists(COVERS, dl.Top()), ALPHA), True),
            # Nothing about an unrelated class: Delta = {d, e},
            # Covers = {(d, e)}, Alpha = {d}, Beta = {} satisfies the axiom and
            # leaves d outside Beta.
            _Question("but-not-an-unrelated-class", "subsumes",
                      _pair(_tb(("add_role_domain", (COVERS, ALPHA)))),
                      ("subsumes", dl.Exists(COVERS, dl.Top()), BETA), False),
        ),
    ),
    # ObjectPropertyRange(P C): for all <x,y> in P^OP, y in C^C. Same closure,
    # the filler translated at the SECOND variable -- which is the whole
    # difference from the domain axiom.
    "ObjectPropertyRange": _Case(
        sample=_pair(_tb(("add_role_range", (COVERS, ALPHA)))),
        builder_args=(COVERS, ALPHA),
        image="∀x ∀y (Covers(x, y) → Alpha(y))",
        mcp_tbox=[{"rangerole": COVERS, "range": "Alpha"}],
        questions=(
            # d in (ExistsCovers.Top)^I gives some e with (d, e) in Covers, and
            # the axiom puts THAT e in Alpha -- so the very successor d already
            # has is one in Alpha.
            _Question("every-covers-successor-is-in-the-range", "subsumes",
                      _pair(_tb(("add_role_range", (COVERS, ALPHA)))),
                      ("subsumes", dl.Exists(COVERS, dl.Top()),
                       dl.Exists(COVERS, ALPHA)), True),
            # Not into an unrelated class: Delta = {d, e}, Covers = {(d, e)},
            # Alpha = {e}, Beta = {} satisfies the axiom.
            _Question("but-not-an-unrelated-class", "subsumes",
                      _pair(_tb(("add_role_range", (COVERS, ALPHA)))),
                      ("subsumes", dl.Exists(COVERS, dl.Top()),
                       dl.Exists(COVERS, BETA)), False),
        ),
    ),
    # SameIndividual(a b) holds iff a^I = b^I, which the kit renders as the FOL
    # atom a = b directly -- the exact mirror of DifferentIndividuals' `!=`.
    # The tableau decides it by MERGING the two nodes before any rule runs.
    "SameIndividual": _Case(
        sample=_pair(abox_build=_ab(("assert_same", ("alice", "bob")))),
        builder_args=("alice", "bob"),
        image="alice = bob",
        mcp_abox={"same": [["alice", "bob"]]},
        questions=(
            # alice = bob and alice in Alpha give bob in Alpha in every model:
            # the two names denote ONE element, and it is in Alpha.
            _Question("sameness-carries-the-class-across", "instance",
                      _pair(abox_build=_ab(("assert_concept", ("alice", ALPHA)),
                                           ("assert_same", ("alice", "bob")))),
                      ("instance", "bob", ALPHA), True),
            # Open world as ever: Delta = {d}, alice = bob = d, Alpha = {d},
            # Gamma = {} is a model, so bob : Gamma is not entailed.
            _Question("but-not-an-unrelated-class", "instance",
                      _pair(abox_build=_ab(("assert_concept", ("alice", ALPHA)),
                                           ("assert_same", ("alice", "bob")))),
                      ("instance", "bob", GAMMA), False),
        ),
    ),
    # NegativeObjectPropertyAssertion(P a b) holds iff <a^I, b^I> is NOT in
    # P^OP: the ground literal ~P(a, b). Decided by a clash condition over the
    # branch's forbidden edges, closed under the role hierarchy.
    "NegativeObjectPropertyAssertion": _Case(
        sample=_pair(abox_build=_ab(("assert_negative_role",
                                     ("alice", "bob", PART)))),
        builder_args=("alice", "bob", PART),
        image="¬HasPart(alice, bob)",
        mcp_abox={"negative_roles": [["alice", "bob", PART]]},
        questions=(
            # HasPart(alice, bob) and ~HasPart(alice, bob) is a contradiction
            # whatever alice and bob denote.
            _Question("asserting-and-forbidding-one-edge-has-no-model",
                      "consistent",
                      _pair(abox_build=_ab(("assert_role", ("alice", "bob", PART)),
                                           ("assert_negative_role",
                                            ("alice", "bob", PART)))),
                      (), False),
            # A DIFFERENT edge is fine, and stays fine WITHOUT a unique name
            # assumption because a model may read the two names apart:
            # Delta = {d, e, f}, alice = d, carol = e, bob = f,
            # HasPart = {(d, e)} satisfies both assertions.
            _Question("an-edge-to-another-name-is-fine", "consistent",
                      _pair(abox_build=_ab(("assert_role", ("alice", "carol", PART)),
                                           ("assert_negative_role",
                                            ("alice", "bob", PART)))),
                      (), True),
        ),
    ),
    # ----- the data layer ---------------------------------------------------
    # The FOL image of every data kind is a *guarded one-sorted* theory: the
    # two-sorted discipline lives in side axioms (kb.premises carries them), so
    # these questions are asked of kb.premises/kb.axioms, never kb.formula alone.
    # The tableau has no data domain and REFUSES all eight kinds by name.
    #
    # SubDataPropertyOf(P Q): P^I ⊆ Q^I as sets of (individual, value) PAIRS,
    # so ∀x ∀v (P(x, v) → Q(x, v)).
    "SubDataPropertyOf": _Case(
        sample=_pair(_tb(("add_data_property_inclusion", (HA, HT)))),
        builder_args=(HA, HT),
        image="∀x ∀v (HasAmount(x, v) → HasTotal(x, v))",
        mcp_tbox=[{"subdata": HA, "supdata": HT}],
        questions=(
            # (alice, 1) ∈ HasAmount^I ⊆ HasTotal^I and 1 is a data value, so
            # alice has a HasTotal-value in the data domain in EVERY model.
            _Question("the-pair-travels-up", "instance",
                      _pair(_tb(("add_data_property_inclusion", (HA, HT))),
                            _ab(("assert_data", ("alice", HA, _int(1))))),
                      ("instance", "alice", dl.DataExists(HT, ANY)), True),
            # Not downwards: HasAmount = ∅, HasTotal = {(alice, 1)} satisfies the
            # inclusion and gives alice no HasAmount-value.
            _Question("but-not-down", "instance",
                      _pair(_tb(("add_data_property_inclusion", (HA, HT))),
                            _ab(("assert_data", ("alice", HT, _int(1))))),
                      ("instance", "alice", dl.DataExists(HA, ANY)), False),
        ),
    ),
    # DisjointDataProperties(P Q): no (individual, value) pair is in both.
    # Stored sorted ('HasAmount' < 'HasTotal'), every unordered pair.
    "DisjointDataProperties": _Case(
        sample=_pair(_tb(("add_disjoint_data_properties", (HA, HT)))),
        builder_args=(HA, HT),
        image="∀x ∀v ¬(HasAmount(x, v) ∧ HasTotal(x, v))",
        mcp_tbox=[{"disjointdata": [HA, HT]}],
        questions=(
            # (alice, 1) in both would be a pair in the intersection: no model.
            _Question("one-pair-in-both-has-no-model", "consistent",
                      _pair(_tb(("add_disjoint_data_properties", (HA, HT))),
                            _ab(("assert_data", ("alice", HA, _int(1))),
                                ("assert_data", ("alice", HT, _int(1))))),
                      (), False),
            # Two DIFFERENT values is fine: HasAmount = {(alice, 1)},
            # HasTotal = {(alice, 2)}.
            _Question("two-different-values-are-fine", "consistent",
                      _pair(_tb(("add_disjoint_data_properties", (HA, HT))),
                            _ab(("assert_data", ("alice", HA, _int(1))),
                                ("assert_data", ("alice", HT, _int(2))))),
                      (), True),
        ),
    ),
    # FunctionalDataProperty(P): at most one value per individual.
    "FunctionalDataProperty": _Case(
        sample=_pair(_tb(("add_functional_data_property", (HA,)))),
        builder_args=(HA,),
        image="∀x ∀v ∀w (HasAmount(x, v) ∧ HasAmount(x, w) → v = w)",
        mcp_tbox=[{"functionaldata": HA}],
        questions=(
            # 1 and 2 are two DIFFERENT data values, and a functional property
            # gives alice one: no model.
            _Question("two-values-have-no-model", "consistent",
                      _pair(_tb(("add_functional_data_property", (HA,))),
                            _ab(("assert_data", ("alice", HA, _int(1))),
                                ("assert_data", ("alice", HA, _int(2))))),
                      (), False),
            # One value is fine.
            _Question("one-value-is-fine", "consistent",
                      _pair(_tb(("add_functional_data_property", (HA,))),
                            _ab(("assert_data", ("alice", HA, _int(1))))),
                      (), True),
        ),
    ),
    # DataPropertyDomain(P C): every individual with a P-value is a C -- the
    # direct two-variable sentence.
    "DataPropertyDomain": _Case(
        sample=_pair(_tb(("add_data_property_domain", (HA, ALPHA)))),
        builder_args=(HA, ALPHA),
        image="∀x ∀v (HasAmount(x, v) → Alpha(x))",
        mcp_tbox=[{"domaindata": HA, "domain": "Alpha"}],
        questions=(
            # (alice, 1) ∈ HasAmount^I puts alice in Alpha, in every model.
            _Question("a-value-forces-the-domain", "instance",
                      _pair(_tb(("add_data_property_domain", (HA, ALPHA))),
                            _ab(("assert_data", ("alice", HA, _int(1))))),
                      ("instance", "alice", ALPHA), True),
            # Not into an unrelated class: Alpha = {alice}, Beta = ∅.
            _Question("but-not-an-unrelated-class", "instance",
                      _pair(_tb(("add_data_property_domain", (HA, ALPHA))),
                            _ab(("assert_data", ("alice", HA, _int(1))))),
                      ("instance", "alice", BETA), False),
        ),
    ),
    # DataPropertyRange(P DR): every P-value is in DR -- here the user-defined
    # datatype Digit, an ordinary unary predicate.
    "DataPropertyRange": _Case(
        sample=_pair(_tb(("add_data_property_range", (HA, DIGIT)))),
        builder_args=(HA, DIGIT),
        image="∀x ∀v (HasAmount(x, v) → Digit(v))",
        mcp_tbox=[{"rangedata": HA, "range": "Digit"}],
        questions=(
            # (alice, 1) ∈ HasAmount^I and the range put the value 1 in Digit,
            # so alice has a HasAmount-value in Digit.
            _Question("the-value-is-in-the-range", "instance",
                      _pair(_tb(("add_data_property_range", (HA, DIGIT))),
                            _ab(("assert_data", ("alice", HA, _int(1))))),
                      ("instance", "alice", dl.DataExists(HA, DIGIT)), True),
            # Nothing puts it in an unrelated datatype: Other = ∅ is a model.
            _Question("but-not-an-unrelated-datatype", "instance",
                      _pair(_tb(("add_data_property_range", (HA, DIGIT))),
                            _ab(("assert_data", ("alice", HA, _int(1))))),
                      ("instance", "alice", dl.DataExists(HA, dl.Datatype("Other"))), False),
        ),
    ),
    # DatatypeDefinition(DT DR): DT IS DR -- a biconditional. The sample uses an
    # enumeration so the image reads back; the facet form is pinned in
    # tests/test_dl_data.py.
    "DatatypeDefinition": _Case(
        sample=_pair(_tb(("add_datatype_definition",
                          ("Digit", dl.DataOneOf((_int(1), _int(2))))))),
        builder_args=("Digit", dl.DataOneOf((_int(1), _int(2)))),
        image="∀v (Digit(v) ↔ v = 1 ∨ v = 2)",
        mcp_tbox=[{"datatype": "Digit", "definition": "{1, 2}"}],
        questions=(
            # Digit = {1, 2} and every HasAmount-value is a Digit, so every
            # HasAmount-value of alice is 1 or 2 -- this needs the FORWARD half of
            # the definition (Digit ⊆ {1, 2}).
            _Question("a-digit-is-one-of-its-members", "instance",
                      _pair(_tb(("add_datatype_definition",
                                 ("Digit", dl.DataOneOf((_int(1), _int(2))))),
                                ("add_data_property_range", (HA, DIGIT))),
                            _ab(("assert_concept", ("alice", ALPHA)))),
                      ("instance", "alice",
                       dl.DataForAll(HA, dl.DataOneOf((_int(1), _int(2))))), True),
            # With Digit = {1, 2, 3} a HasAmount-value of alice may be 3:
            # HasAmount = {(alice, 3)} is a model that is not inside {1, 2}.
            _Question("but-not-a-wider-datatype", "instance",
                      _pair(_tb(("add_datatype_definition",
                                 ("Digit", dl.DataOneOf((_int(1), _int(2), _int(3))))),
                                ("add_data_property_range", (HA, DIGIT))),
                            _ab(("assert_concept", ("alice", ALPHA)))),
                      ("instance", "alice",
                       dl.DataForAll(HA, dl.DataOneOf((_int(1), _int(2))))), False),
        ),
    ),
    # DataPropertyAssertion(P a lt): (a^I, lt^D) ∈ P^I -- the ground atom with
    # the literal's TERM (the number 400) in the value position.
    "DataPropertyAssertion": _Case(
        sample=_pair(abox_build=_ab(("assert_data", ("alice", HA, _int(400))))),
        builder_args=("alice", HA, _int(400)),
        image="HasAmount(alice, 400)",
        mcp_abox={"data": [["alice", HA, '"400"^^xsd:integer']]},
        questions=(
            # DataHasValue(HasAmount 400) ⊑ Alpha and (alice, 400) ∈ HasAmount^I
            # put alice in Alpha, in every model.
            _Question("the-assertion-satisfies-a-value-restriction", "instance",
                      _pair(_tb(("add", (dl.DataHasValue(HA, _int(400)), ALPHA))),
                            _ab(("assert_data", ("alice", HA, _int(400))))),
                      ("instance", "alice", ALPHA), True),
            # 401 is not 400: HasAmount = {(alice, 401)}, Alpha = ∅ is a model.
            _Question("but-a-different-value-does-not", "instance",
                      _pair(_tb(("add", (dl.DataHasValue(HA, _int(400)), ALPHA))),
                            _ab(("assert_data", ("alice", HA, _int(401))))),
                      ("instance", "alice", ALPHA), False),
        ),
    ),
    # NegativeDataPropertyAssertion(P a lt): (a^I, lt^D) ∉ P^I -- the ground
    # literal ¬P(a, t).
    "NegativeDataPropertyAssertion": _Case(
        sample=_pair(abox_build=_ab(("assert_negative_data", ("alice", HA, _int(400))))),
        builder_args=("alice", HA, _int(400)),
        image="¬HasAmount(alice, 400)",
        mcp_abox={"negative_data": [["alice", HA, '"400"^^xsd:integer']]},
        questions=(
            # asserting and forbidding one pair is a contradiction
            _Question("asserting-and-forbidding-one-pair-has-no-model", "consistent",
                      _pair(abox_build=_ab(("assert_data", ("alice", HA, _int(400))),
                                           ("assert_negative_data", ("alice", HA, _int(400))))),
                      (), False),
            # another value is fine: HasAmount = {(alice, 401)}
            _Question("another-value-is-fine", "consistent",
                      _pair(abox_build=_ab(("assert_data", ("alice", HA, _int(401))),
                                           ("assert_negative_data", ("alice", HA, _int(400))))),
                      (), True),
        ),
    ),
}


def _rows():
    return tuple(_AXIOM_KINDS)


def _ids(rows):
    return [row.kind for row in rows]


_ROWS = _rows()
_ALL = pytest.mark.parametrize("row", _ROWS, ids=_ids(_ROWS))
_SUPPORTED = pytest.mark.parametrize(
    "row", [r for r in _ROWS if r.tableau != "refused"],
    ids=_ids([r for r in _ROWS if r.tableau != "refused"]))


# --------------------------------------------------------------------------- #
# The meta-tests: the table covers the classes, and this file covers the table.
# --------------------------------------------------------------------------- #

_CONTAINERS = (list, set, frozenset, dict, tuple)


def _axiom_container_fields(cls) -> set:
    """The dataclass fields of ``cls`` that HOLD axioms — every field whose type
    or default factory is a container.

    Deliberately shape-based rather than a list of names: a field added to
    ``TBox``/``ABox`` to store a new axiom kind is a container, and this is the
    only way the meta-test below notices it without anyone remembering to.
    """
    found = set()
    for f in dataclasses.fields(cls):
        if f.name.startswith("__"):
            continue
        if f.default_factory in _CONTAINERS or get_origin(f.type) in _CONTAINERS:
            found.add(f.name)
        elif isinstance(f.type, str) and f.type.split("[")[0].lower().lstrip("t.") in (
                "list", "set", "frozenset", "dict", "tuple"):
            found.add(f.name)          # a string annotation (PEP 563) spelling
    return found


def test_every_tbox_and_abox_field_has_a_row():
    """THE meta-test. Add a field to TBox or ABox without a row of
    ``_AXIOM_KINDS`` and this goes red — which is what stops a new axiom kind
    shipping with the tableau and the FOL route silently disagreeing about it.
    """
    declared = {("tbox", name) for name in _axiom_container_fields(dl.TBox)}
    declared |= {("abox", name) for name in _axiom_container_fields(dl.ABox)}
    tabled = {(row.holder, row.field) for row in _ROWS}
    assert declared, "no axiom-holding fields found at all — the scan is broken"
    assert tabled == declared, (
        "dl.tableau._AXIOM_KINDS and TBox/ABox disagree about which axiom kinds "
        f"exist. Fields with no row: {sorted(declared - tabled)}. Rows naming a "
        f"field that is gone: {sorted(tabled - declared)}. Every axiom kind needs "
        "a row saying what the TABLEAU does with it and what the FOL IMAGE does "
        "with it — see 'The axiom-kind table' in dl/tableau.py's module docstring.")


def test_every_axiom_kind_has_hand_derived_test_data():
    """A row nobody wrote test data for is a row nothing in this file checks."""
    assert set(_CASES) == {row.kind for row in _ROWS}, (
        "this file's _CASES and dl.tableau._AXIOM_KINDS disagree: "
        f"untested kinds {sorted({r.kind for r in _ROWS} - set(_CASES))}, "
        f"stale cases {sorted(set(_CASES) - {r.kind for r in _ROWS})}.")


def test_the_table_is_internally_consistent():
    """``_validate_axiom_kinds`` runs at import; prove it actually rejects
    something, so a typo'd column really is caught rather than merely checked
    by code that never fails.
    """
    broken = _ROWS + (_AxiomKind("Bogus", "tbox", "inclusions", "add",
                                 tableau="refuse",      # the typo
                                 fol="fol", part="concepts"),)
    with pytest.raises(ValueError, match="tableau 'refuse'"):
        _tableau._validate_axiom_kinds(broken)


def test_every_new_public_name_is_exported():
    """``tests/test_api_reference_complete.py`` only sees names that are already
    in ``dl.__all__``, so the export itself needs its own guard.
    """
    for name in ("SideAxiom", "UnsupportedAxiomError", "KnowledgeBaseFOL",
                 "kb_to_fol", "RoleBoxOmittedError", "RoleExpressionError"):
        assert name in dl.__all__, f"dl.__all__ is missing {name!r}"
        assert getattr(dl, name) is not None


# --------------------------------------------------------------------------- #
# Builders never refuse.
# --------------------------------------------------------------------------- #

@_ALL
def test_builders_never_refuse(row):
    """Every kind can be BUILT. A TBox is what a parser fills from a file, so a
    builder that refused a kind would make ``dl.parse_owl_functional`` unable to
    represent an ontology it is supposed to report on. The refusal belongs at
    query time and at render time; see the module docstring of dl/tableau.py.
    """
    holder = dl.TBox() if row.holder == "tbox" else dl.ABox()
    before = len(getattr(holder, row.field))
    returned = getattr(holder, row.builder)(*_CASES[row.kind].builder_args)
    assert returned is holder, f"{row.builder} must return self (chainable)"
    assert len(getattr(holder, row.field)) > before, (
        f"{row.builder} did not store anything in {row.holder}.{row.field}")


# --------------------------------------------------------------------------- #
# Claim (2) of each row: what the TABLEAU does with it.
# --------------------------------------------------------------------------- #

@_ALL
def test_the_tableau_claim_is_true(row):
    """``"internalised"``/``"rule"`` must give a verdict; ``"refused"`` must
    raise ``UnsupportedAxiomError`` naming the kind — from BOTH entry points.
    """
    tbox, abox = _CASES[row.kind].sample()
    if row.tableau == "refused":
        with pytest.raises(dl.UnsupportedAxiomError, match=row.kind):
            dl.abox_consistent(abox if abox is not None else dl.ABox(), tbox)
        if row.holder == "tbox":
            with pytest.raises(dl.UnsupportedAxiomError, match=row.kind):
                dl.concept_satisfiable(ALPHA, tbox)
        else:
            # An ABox kind is not something concept_satisfiable can see: it
            # takes a TBox and no ABox, so its answer is about the empty
            # terminology and is correct. (Until the data layer every refused
            # kind was a TBox kind, and this branch could not arise.)
            assert dl.concept_satisfiable(ALPHA, tbox) is True
        return
    assert dl.abox_consistent(abox if abox is not None else dl.ABox(), tbox) is True
    assert dl.concept_satisfiable(ALPHA, tbox) is True


_TBOX_DECIDED = [r for r in _ROWS if r.holder == "tbox" and r.layer == "object"
                 and r.tableau != "refused"]


@pytest.mark.parametrize("row", _TBOX_DECIDED, ids=_ids(_TBOX_DECIDED))
def test_the_internalised_label_means_a_concept_every_node_carries(row):
    """The word ``"internalised"`` is DEFINED by what the tableau does with the
    axiom: it is (equivalent to) a general concept inclusion, turned into a
    label concept that every node carries — which is what ``_new_branch`` hands
    ``_solve`` as ``tbox_concepts``. A ``"rule"`` kind adds NO such concept: it
    is decided by a completion rule or a clash condition over the edges.

    ``FunctionalObjectProperty`` was labelled ``"rule"`` while its own comment,
    ``_new_branch`` and the module docstring all said it is the GCI
    ``⊤ ⊑ ≤1 P.⊤``; ``ObjectPropertyDomain``/``Range`` are labelled
    ``"internalised"`` although ``TBox.internalized()`` deliberately leaves them
    out (``_new_branch`` adds them). Both facts are checked here against the
    code, for every undisputed row at once, so a row relabelled — or a kind
    decided by a different mechanism later — goes red.
    """
    tbox, _ = _CASES[row.kind].sample()
    _, label_concepts, _ = _tableau._new_branch(tbox)
    if row.tableau == "internalised":
        assert label_concepts, (
            f"{row.kind} is labelled 'internalised' but _new_branch puts no "
            "concept on any node for it")
    else:
        assert row.tableau == "rule"
        assert label_concepts == [], (
            f"{row.kind} is labelled 'rule' but _new_branch internalises it "
            f"as {[c.to_unicode() for c in label_concepts]}: that is an "
            "'internalised' kind")


def test_the_functional_row_says_internalised():
    # The one row that was wrong. Hand-derived: FunctionalObjectProperty(P) is
    # ⊤ ⊑ ≤1 P.⊤, a GCI, so no new rule — the ALCQ argument covers it.
    (row,) = [r for r in _ROWS if r.kind == "FunctionalObjectProperty"]
    assert row.tableau == "internalised"
    label = _tableau._new_branch(dl.TBox().add_functional_role("P"))[1]
    assert label == [dl.AtMost(1, "P", dl.Top())]


# --------------------------------------------------------------------------- #
# Claim (3)/(4) of each row: what the FOL IMAGE does with it, and where.
# --------------------------------------------------------------------------- #

def _image_of(row, kb):
    """The part of ``kb`` the row's ``part`` column says this kind lands in."""
    if row.part == "concepts":
        return kb.tbox
    if row.part == "assertions":
        return kb.abox
    if row.part == "side":
        rendered = kb.axioms_of_kind(row.kind)
        assert len(rendered) == 1, (
            f"{row.kind}: kb.axioms_of_kind gave {len(rendered)} axioms for a "
            "knowledge base carrying exactly one")
        return rendered[0]
    raise AssertionError(f"{row.kind}: part={row.part!r} has no image to check")


@_ALL
def test_the_fol_claim_is_true(row):
    """The FOL image of one axiom of this kind, against the string derived by
    hand from the OWL 2 direct semantics (see the comment above each case).
    """
    case = _CASES[row.kind]
    tbox, abox = case.sample()
    if row.fol == "two-sorted":
        # No row says "two-sorted" today. When one does, kb_to_fol must refuse
        # it by name and point at the two-sorted entry point -- a data axiom has
        # no one-sorted image, because OWL's object and data domains are
        # disjoint and a one-sorted image would be STRONGER than the ontology.
        omitted = getattr(dl, "DataAxiomsOmittedError", None)
        assert omitted is not None, (
            f"{row.kind} is fol='two-sorted', so dl must export "
            "DataAxiomsOmittedError for kb_to_fol to refuse it with")
        with pytest.raises(omitted, match=row.kind):
            dl.kb_to_fol(tbox, abox)
        return
    assert row.fol == "fol", f"{row.kind}: unhandled fol={row.fol!r}"
    kb = dl.kb_to_fol(tbox, abox)
    assert _image_of(row, kb).to_unicode_str() == case.image
    if row.part == "side":
        # The derived view must agree with the stored one, both ways round.
        assert case.image in [a.to_unicode_str() for a in kb.axioms]
        assert row.kind in {a.kind for a in kb.side_axioms}
    else:
        assert kb.axioms_of_kind(row.kind) == (), (
            f"{row.kind} is part={row.part!r}, so it must not also appear as a "
            "side axiom — one axiom rendered twice is one axiom asserted twice")


@_ALL
def test_the_fol_image_reads_back(row):
    """Everything the kit prints must read back — the 0.30.0 property, applied
    to each kind's own image.

    The DifferentIndividuals and ClassAssertion/ObjectPropertyAssertion images
    use LOWER-case individuals on purpose: an upper-case individual prints as
    itself and re-reads as a predicate, which is a documented limit of the
    vocabulary (see tests/test_printed_text_reads_back.py), not of the image.
    """
    if row.fol != "fol":
        pytest.skip(f"{row.kind} has no one-sorted image")
    tbox, abox = _CASES[row.kind].sample()
    node = _image_of(row, dl.kb_to_fol(tbox, abox))
    parsed = api.parse_any(node.to_unicode_str())
    assert parsed.ok, f"{row.kind}: printed text the kit cannot parse: {node.to_unicode_str()!r}"


@_ALL
def test_tbox_to_fol_refuses_exactly_what_it_does_not_render(row):
    """``tbox_to_fol`` renders the concept inclusions and nothing else, so a TBox
    carrying a SIDE axiom must raise rather than hand back a weaker theory.

    The condition is derived from the table (``TBox.has_side_axioms``), which is
    why this test can be parametrised over it at all: a hand-written ``or`` over
    two fields would return a tautology and raise NOTHING for a third.
    """
    if row.holder != "tbox":
        pytest.skip("an ABox kind: tbox_to_fol never sees it")
    tbox, _ = _CASES[row.kind].sample()
    if row.part == "side":
        with pytest.raises(dl.RoleBoxOmittedError) as info:
            dl.tbox_to_fol(tbox)
        message = str(info.value)
        assert row.kind in message, (
            f"the refusal must NAME the kind it is refusing; got {message!r}")
        for pointer in ("kb_to_fol", "rbox_to_fol", "concept_inclusions_only"):
            assert pointer in message
        # and the explicit opt-out still works
        dl.tbox_to_fol(tbox, concept_inclusions_only=True)
    else:
        dl.tbox_to_fol(tbox)              # rendered in full: nothing to refuse


# --------------------------------------------------------------------------- #
# THE test: the two routes agree, per kind, on a hand-derived pair.
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize(
    "row, question",
    [(row, q) for row in _ROWS for q in _CASES[row.kind].questions],
    ids=[f"{row.kind}-{q.label}" for row in _ROWS for q in _CASES[row.kind].questions])
def test_the_two_routes_agree(row, question):
    """One entailment and one non-entailment per kind, each asked of the tableau
    AND of ``api.prove`` over ``kb_to_fol``'s output, asserting the two agree.

    For a ``"refused"`` row, "agree" means something sharper and is the whole
    point of the policy: the FOL route must still give the hand-derived
    verdict, and the tableau must RAISE rather than answer. An answer either
    way would be the failure — if it answered the same, the refusal is
    pointless; if it answered differently, the two routes disagree; and the
    shape this actually took before 0.30.0 was the tableau reading the role box
    as atomic and quietly returning False for a subsumption the FOL image
    proves.

    ``"unknown"`` is a failure here, not a pass: first-order entailment with
    transitivity is only semi-decidable, so an undecided answer means the test
    measured nothing — which is why TIMEOUT_MS is generous rather than tight.
    """
    tbox, abox = question.build()
    kb = dl.kb_to_fol(tbox, abox)
    refused = row.tableau == "refused"
    if question.form == "subsumes":
        _, sub, sup = question.query
        ask = lambda: dl.subsumes(sub, sup, tbox)
        # A GOAL asked of a two-sorted image is relativised to the object domain
        # like its GCIs; for a knowledge base without a data layer this is False
        # and the goal is the plain one.
        status = _status(dl.subsumption_to_fol(
            sub, sup, object_sort=(kb.separation == "two-sorted")), kb.tbox_premises)
        wanted = "proved" if question.holds else "refuted"
    elif question.form == "instance":
        _, individual, concept = question.query
        ask = lambda: dl.instance_check(abox, individual, concept, tbox)
        goal = dl.abox_to_fol(dl.ABox().assert_concept(individual, concept))
        status = _status(goal, kb.premises)
        wanted = "proved" if question.holds else "refuted"
    else:
        assert question.form == "consistent", question.form
        ask = lambda: dl.abox_consistent(abox, tbox)
        status = _status(FNot(kb.formula), kb.axioms)
        wanted = "refuted" if question.holds else "proved"
    assert status == wanted, (
        f"{row.kind}/{question.label}: the FOL route said {status!r} where the "
        f"hand-derived answer is {question.holds} ({wanted!r})")
    if refused:
        with pytest.raises(dl.UnsupportedAxiomError, match=row.kind) as info:
            ask()
        message = str(info.value)
        for pointer in ("dl.owl_reasoner", "dl.kb_to_fol", "api.prove"):
            assert pointer in message, (
                f"{row.kind}: the refusal must point at {pointer}, so the "
                f"route that DOES answer is named; got {message!r}")
        return
    tableau_says = ask()
    assert tableau_says is question.holds, (
        f"{row.kind}/{question.label}: the TABLEAU said {tableau_says} where "
        f"the hand-derived answer is {question.holds}; the FOL route said "
        f"{status!r}, so the two routes answer the same question differently")


# --------------------------------------------------------------------------- #
# The seam itself: the shared guard, reached from both entry points.
# --------------------------------------------------------------------------- #

def _refusing(field: str):
    """``_AXIOM_KINDS`` with the row storing ``field`` turned ``"refused"``."""
    return tuple(
        dataclasses.replace(row, tableau="refused") if row.field == field else row
        for row in _ROWS)


@pytest.mark.parametrize("field, holder, build", [
    ("transitive_roles", "tbox",
     lambda: (dl.TBox().add_transitive_role(PART).add_transitive_role(OVER), dl.ABox())),
    ("distinct_assertions", "abox",
     lambda: (dl.TBox(), dl.ABox().assert_distinct("alice", "bob"))),
], ids=["a-tbox-kind", "an-abox-kind"])
def test_the_shared_guard_is_reached_from_both_entry_points(monkeypatch, field, holder, build):
    """With today's kinds nothing is ``"refused"``, so the guard is a no-op —
    which is correct, and is also why it needs a test that MAKES something
    refused. This is the red/green proof of the seam: remove
    ``_reject_role_box`` (the one caller of ``_reject_unsupported``, reached
    first from ``concept_satisfiable`` and ``abox_consistent``) from either of
    them and one half of this goes red.
    """
    patched = _refusing(field)
    monkeypatch.setattr(_tableau, "_AXIOM_KINDS", patched)
    tbox, abox = build()
    kind = next(r.kind for r in patched if r.field == field)
    count = len(getattr(tbox if holder == "tbox" else abox, field))

    with pytest.raises(dl.UnsupportedAxiomError) as from_abox:
        dl.abox_consistent(abox, tbox)
    message = str(from_abox.value)
    assert kind in message and f"x{count}" in message, (
        f"the refusal must name the kind AND its count; got {message!r}")
    for pointer in ("dl.owl_reasoner", "dl.kb_to_fol", "api.prove"):
        assert pointer in message, f"the refusal must point at {pointer}"

    if holder == "tbox":
        with pytest.raises(dl.UnsupportedAxiomError, match=kind):
            dl.concept_satisfiable(ALPHA, tbox)
        # and everything that reduces to the two inherits it, with no guard of
        # its own. Counted from the code, not from memory: _reject_unsupported
        # has ONE caller, _reject_role_box; that is called first by
        # concept_satisfiable, abox_consistent and classify, and by
        # _reject_inputs, which opens instance_retrieval, realize, realize_all
        # and classify. subsumes/equivalent/concept_unsatisfiable/
        # instance_check have no guard of their own.
        with pytest.raises(dl.UnsupportedAxiomError, match=kind):
            dl.subsumes(ALPHA, BETA, tbox)
    with pytest.raises(dl.UnsupportedAxiomError, match=kind):
        dl.instance_check(abox, "alice", ALPHA, tbox)


_REFUSED_ROWS = [r for r in _ROWS if r.tableau == "refused"]


@pytest.mark.parametrize("row", _REFUSED_ROWS, ids=_ids(_REFUSED_ROWS))
def test_every_refused_kind_is_refused_by_the_sweeps_with_nothing_to_sweep(row):
    """``realize`` with an empty vocabulary, ``realize_all`` and
    ``instance_retrieval`` on an empty ABox and ``classify`` with no names make
    no ``instance_check``/``subsumes`` call, so they reach the guard only
    because they run it themselves. Derived from the table: EVERY refused row,
    the data kinds included, must be refused by name from each of them — a
    knowledge base carrying it must not get a quiet ``[]``/``{}``/empty
    hierarchy where every other entry point raises. (The expected answer for
    each of those calls on a knowledge base of DECIDED kinds is an empty
    result, which is what makes a silent one indistinguishable from a verdict.)
    """
    tbox, abox = _CASES[row.kind].sample()
    abox = abox if abox is not None else dl.ABox()
    calls = [
        lambda: dl.realize(abox, "alice", [], tbox),
        lambda: dl.realize_all(abox, [], tbox),
    ]
    if row.holder == "tbox":
        # With the kind in the TBox and NOTHING in the ABox there is no
        # individual to sweep either.
        calls += [
            lambda: dl.realize(dl.ABox(), "alice", [], tbox),
            lambda: dl.realize_all(dl.ABox(), [ALPHA], tbox),
            lambda: dl.instance_retrieval(dl.ABox(), ALPHA, tbox),
            lambda: dl.classify(tbox),
        ]
    else:
        calls.append(lambda: dl.instance_retrieval(abox, ALPHA, tbox))
    for call in calls:
        with pytest.raises(dl.UnsupportedAxiomError, match=row.kind):
            call()


def test_the_derived_conditions_really_read_the_table(monkeypatch):
    """``TBox.has_side_axioms``, ``ABox.is_empty`` and the individual scan are
    DERIVED from ``_AXIOM_KINDS``, and this is what makes that claim checkable.

    With today's fields a hand-written condition and a derived one agree, so
    nothing distinguishes them — until a field is added, when the hand-written
    one loses it SILENTLY (a side axiom rendered as a tautology, an ABox half
    dropped from the formula, ``kb.individuals == ()`` for a knowledge base
    that names individuals). So the test changes the TABLE and checks the
    answers move with it. They cannot, if the conditions were spelled out over
    field names.
    """
    gci_only = dl.TBox().add(ALPHA, BETA)
    assert gci_only.has_side_axioms() is False
    monkeypatch.setattr(_tableau, "_AXIOM_KINDS", tuple(
        dataclasses.replace(row, part="side") if row.field == "inclusions" else row
        for row in _ROWS))
    assert gci_only.has_side_axioms() is True

    distinct_only = dl.ABox().assert_distinct("alice", "bob")
    assert distinct_only.is_empty() is False
    assert _tableau._abox_individual_names(distinct_only) == {"alice", "bob"}
    monkeypatch.setattr(_tableau, "_AXIOM_KINDS", tuple(
        row for row in _ROWS if row.field != "distinct_assertions"))
    assert distinct_only.is_empty() is True
    assert _tableau._abox_individual_names(distinct_only) == set()


def test_an_axiom_level_refusal_is_not_a_concept_level_one():
    """``UnsupportedAxiomError`` is deliberately NOT a subclass of
    ``UnsupportedConceptError``: a caller catching the concept-level refusal
    (a nominal, an inverse role — a different remedy) must not silently start
    swallowing axiom-level ones.
    """
    assert issubclass(dl.UnsupportedAxiomError, ValueError)
    assert not issubclass(dl.UnsupportedAxiomError, dl.UnsupportedConceptError)
    assert not issubclass(dl.UnsupportedConceptError, dl.UnsupportedAxiomError)


def test_which_kinds_are_refused_is_pinned():
    """WHICH kinds the in-house tableau refuses, as an explicit list. A future
    row's column must be a deliberate decision, recorded here, not a surprise —
    and a kind that silently BECOMES decided (or stops being) shows up as a
    diff on this list rather than as a verdict nobody checked.

    Every one of the first five is refused for a reason written out in
    dl/tableau.py's "The rest of the OWL 2 role box" section: the first four are
    the **I** of SHIQ or the counting interaction, the fifth the **R** of SROIQ.
    The other eight are the **D** of SROIQ(D): the in-house tableau has no data
    domain, and the FOL image answers them instead.
    """
    assert [r.kind for r in _ROWS if r.tableau == "refused"] == [
        "InverseObjectProperties",
        "SymmetricObjectProperty",
        "ReflexiveObjectProperty",
        "InverseFunctionalObjectProperty",
        "ObjectPropertyChain",
        "SubDataPropertyOf",
        "DisjointDataProperties",
        "FunctionalDataProperty",
        "DataPropertyDomain",
        "DataPropertyRange",
        "DatatypeDefinition",
        "DataPropertyAssertion",
        "NegativeDataPropertyAssertion",
    ]
    assert {r.kind for r in _ROWS if r.layer == "data"} == {
        "SubDataPropertyOf", "DisjointDataProperties", "FunctionalDataProperty",
        "DataPropertyDomain", "DataPropertyRange", "DatatypeDefinition",
        "DataPropertyAssertion", "NegativeDataPropertyAssertion"}
    # ... and every refused row carries its own remedy, not just the kind name.
    for row in _ROWS:
        if row.tableau == "refused":
            assert row.refusal_note, (
                f"{row.kind} is refused with no refusal_note: the shared guard "
                "names the kind for every row alike, so the per-construct "
                "remedy has nowhere else to live")


def test_the_guard_says_nothing_about_a_knowledge_base_of_decided_kinds():
    """The no-op case, pinned: a knowledge base using only kinds the tableau
    DECIDES raises nothing, so the guard never fires by accident.
    """
    tbox = dl.TBox().add(ALPHA, BETA).add_equivalence(BETA, GAMMA)
    tbox.add_role_inclusion(PART, OVER).add_transitive_role(OVER)
    tbox.add_disjoint_roles(SINK, SOURCE).add_asymmetric_role(INPUT)
    tbox.add_irreflexive_role(INPUT).add_functional_role(STATE)
    abox = dl.ABox().assert_concept("alice", ALPHA)
    abox.assert_role("alice", "bob", PART).assert_distinct("alice", "bob")
    assert _tableau._reject_unsupported(tbox, abox) is None
    assert dl.abox_consistent(abox, tbox) is True


# --------------------------------------------------------------------------- #
# The other consumers of the TBox/ABox shape. Each must RENDER the kind or
# refuse naming itself: an oracle that silently drops an axiom agrees with the
# tableau for the wrong reason, which is worse than disagreeing.
# --------------------------------------------------------------------------- #

def _shape(tbox, abox) -> dict:
    """Per-field axiom counts — a name-independent fingerprint, so a renderer
    that mangles names (both of the ones below do) is still comparable.
    """
    counts = {}
    for row in _ROWS:
        holder = tbox if row.holder == "tbox" else abox
        counts[(row.holder, row.field)] = len(getattr(holder, row.field))
    return counts


@_ALL
def test_the_owl_functional_writer_renders_every_axiom_kind(row):
    """``to_owl_functional`` is the dual of ``parse_owl_functional``: a kind the
    parser reads and the writer drops is a round-trip bug, so the check is the
    round trip itself, on the nose.
    """
    tbox, abox = _CASES[row.kind].sample()
    tbox, abox = tbox or dl.TBox(), abox or dl.ABox()
    text = dl.to_owl_functional(tbox, abox)
    assert dl.parse_owl_functional(text) == (tbox, abox), (
        f"to_owl_functional lost or changed a {row.kind} axiom:\n{text}")


@_ALL
def test_the_hets_owl_backend_renders_every_axiom_kind(row):
    """``hets.owl_backend._render_document`` feeds the kit's SECOND independent
    oracle (Hets/FaCT++ over Docker). It synthesises fresh names, so the check
    is the axiom SHAPE rather than the text — but a dropped axiom is a dropped
    axiom either way. No Docker needed: the renderer is a pure function.
    """
    tbox, abox = _CASES[row.kind].sample()
    tbox, abox = tbox or dl.TBox(), abox or dl.ABox()
    text = _hets_owl._render_document(tbox, abox)
    back = dl.parse_owl_functional(text)
    assert _shape(*back) == _shape(tbox, abox), (
        f"hets.owl_backend._render_document lost a {row.kind} axiom:\n{text}")


@_ALL
def test_the_mcp_dl_tools_can_express_every_axiom_kind(row):
    """The MCP description-logic tools build their TBox/ABox from JSON rows, and
    nothing in ``tests/test_mcp_stability.py`` fires when a kind has no row shape
    (its baselines are one-directional by design — a new tool and a new optional
    parameter both pass). Without this, the tools would answer a question about
    a knowledge base missing half its axioms.
    """
    case = _CASES[row.kind]
    tbox, abox = case.sample()
    tbox, abox = tbox or dl.TBox(), abox or dl.ABox()
    if row.holder == "tbox":
        assert case.mcp_tbox is not None, (
            f"{row.kind} has no MCP tbox row shape; add one to _build_dl_tbox")
        built, err = _build_dl_tbox(case.mcp_tbox, "alc")
        other = dl.ABox()
    else:
        assert case.mcp_abox is not None, (
            f"{row.kind} has no MCP abox argument; add one to _build_dl_abox")
        arguments = {"concepts": None, "roles": None, "distinct": None}
        arguments.update(case.mcp_abox)
        built, err = _build_dl_abox(syntax="alc", **arguments)
        other = dl.TBox()
    assert err is None, f"{row.kind}: the MCP builder refused its own row: {err}"
    got = (built, other) if row.holder == "tbox" else (other, built)
    assert _shape(*got) == _shape(tbox, abox), (
        f"the MCP row shape for {row.kind} did not build the axiom")


@pytest.mark.skipif(not _owl_reasoner.available(),
                    reason="owlready2 is not installed ([owl] extra)")
@pytest.mark.parametrize(
    "row, question",
    [pytest.param(row, q)
     for row in _ROWS for q in _CASES[row.kind].questions],
    ids=[f"{row.kind}-{q.label}" for row in _ROWS for q in _CASES[row.kind].questions])
def test_the_external_reasoner_agrees_on_every_axiom_kind(row, question):
    """``dl.external_*`` (owlready2 + HermiT) is the kit's other INDEPENDENT
    oracle, and ``_build_kb`` reads a TBox field by field. An agreement with the
    tableau is worthless if the oracle never saw the axiom, so the check is the
    same hand-derived pair, asked of HermiT.
    """
    tbox, abox = question.build()
    if row.layer == "data":
        # HermiT is not wired to the data layer: it REFUSES, by name, before any
        # JVM starts -- an oracle that silently dropped the axiom under test
        # would agree with everything. The FOL route (test_the_two_routes_agree)
        # carries the hand-derived verdict instead.
        with pytest.raises(dl.UnsupportedAxiomError, match="data-layer"):
            if question.form == "subsumes":
                _, sub, sup = question.query
                dl.external_subsumes(sub, sup, tbox)
            elif question.form == "instance":
                _, individual, concept = question.query
                dl.external_instance_check(abox, individual, concept, tbox)
            else:
                dl.external_abox_consistent(abox, tbox)
        return
    if question.form == "subsumes":
        _, sub, sup = question.query
        assert dl.external_subsumes(sub, sup, tbox) is question.holds
    elif question.form == "instance":
        _, individual, concept = question.query
        assert dl.external_instance_check(abox, individual, concept, tbox) is question.holds
    else:
        assert dl.external_abox_consistent(abox, tbox) is question.holds
