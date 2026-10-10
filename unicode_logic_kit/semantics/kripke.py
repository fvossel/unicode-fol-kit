"""Kripke (possible-worlds) semantics for the propositional modal fragment.

A :class:`KripkeModel` is a possible-worlds frame: a set of worlds, a family of
named accessibility relations between worlds, and a per-world valuation of the
ground atoms. :func:`satisfies_modal` computes the truth value of a modal
formula *at a world*, following the standard Kripke satisfaction relation.

Only the **propositional / ground** modal fragment is interpreted here (this is
v1): the modal operators wrap classical connectives and ground atoms. A ground
atom is identified by its key (:func:`~unicode_logic_kit.fol.atom_key`: the text it prints as,
with every constant written by its name, e.g. ``"P"`` or ``"Likes(a, b)"``, also where the
formula text writes the constant in quotes, ``Likes('a', 'b')``); a world's valuation
is the set of atom keys true there, and an atom whose key is written either way (its key or
its text as a formula, ``atom.to_unicode_str()``) is found, so a missing key is false.
Object quantifiers
(plain ``Quantifier`` and sorted ``SortedQuantifier``, see "Many-sorted formulas"
below) ARE interpreted, over per-world domains; Łukasiewicz operators and lambda nodes are rejected
with NotImplementedError — fuzzy modal logic is future work.

Many-sorted formulas: ``satisfies_modal`` relativizes the WHOLE input formula
ONCE, up front, before any dispatch — the same "relativize once, up front"
choice ``fol.qml.qml_translate`` / ``semantics.intuitionistic._prepare_many_sorted``
make and for the identical reason: a ``SortedConstant`` (``alice:Human``) can
occur anywhere in the formula, not only directly under a ``SortedQuantifier``,
so relativizing lazily (only when the recursive descent happens to walk into a
``SortedQuantifier`` node) would leave a bare sorted constant's ``:Sort``
suffix in place, and the valuation lookup for it would then silently miss.
Relativizing uses ``Node._relativize`` (the same reduction ``fol.to_fol``
uses): a ``SortedQuantifier`` (``∀x:S φ`` / ``∃x:S φ``) becomes a guarded plain
``Quantifier`` — ``∀x (S(x) → φ)`` / ``∃x (S(x) ∧ φ)`` — over the current
world's domain ``D_w``; a bare ``SortedConstant`` becomes a plain ``Constant``.
Two consequences of this reduction, both deliberate design choices, not gaps:

- **Sorts are world-relative, not rigid.** The sort guard ``S(x)`` is an
  ordinary atom, looked up in ``valuation`` exactly like any other atom, so an
  individual can be ``S`` at one world and not at another — the same
  "actualist" reading this module already gives the bare per-world domain
  ``D_w`` (see ``domains``/``domain_at`` above). A caller that wants a sort
  RIGID (the same extension at every world) states that itself, as an extra
  frame condition on the relation being evaluated over (e.g. asserting
  ``S(d) ↔ S'(d)`` between every pair of accessible worlds in the model it
  builds) — this evaluator does not assume or enforce it.
- **Non-emptiness is the caller's responsibility, exactly as it already is for
  the unsorted domain.** This evaluator never assumes a sort — or a bare
  per-world domain — is non-empty; ``∀x:S φ → ∃x:S φ`` can come out FALSE
  here if the model happens to make ``S`` empty at ``world``. The classical
  many-sorted routes (``api.prove`` et al.) instead ALWAYS assume every sort
  is non-empty, by adding ``fol.nonempty_sort_axioms`` as extra premises (see
  that function's docstring) — so a caller who wants THIS evaluator to agree
  with a classical MSFOL verdict on a modal-free sorted formula must build the
  ``KripkeModel`` so each mentioned sort's guard atom holds of at least one
  individual in ``D_w`` at every world that matters, the same way domains and
  valuations are already the caller's construction to get right. See
  ``tests/test_sorted_modal.py`` for a worked differential against
  ``api.prove`` built this way.
- **A sorted constant being in its sort is a property of the MODEL, too.**
  ``c:S`` denotes an element of ``S``, and a constant is a rigid designator, so
  in a legal model the guard atom ``S(c)`` is true at EVERY world — whatever the
  world's domain says about whether ``c`` exists there. The evaluator reads the
  guard from the valuation like any other atom and does not check it: in a model
  that leaves ``Human(socrates)`` out of some world's valuation,
  ``∀x:Human Mortal(x) → Mortal(socrates:Human)`` can be FALSE there, a model
  the many-sorted routes (``qml_is_valid``, ``api.prove``) never consider. The
  routes assert the fact as a background axiom (``fol.sort_membership_axioms``,
  lifted per world by ``fol.qml``) and an evaluator of ONE given model cannot, so
  a caller who compares this evaluator with them builds the model that way, or
  asks :func:`sorted_constant_violations` which worlds of a model fall short. A
  plain constant ``socrates`` has no sort, and nothing is asserted about it.

Equality is NOT interpreted. ``=`` and ``≠`` need a semantics of TERMS — what
``a`` and ``b`` denote, so that ``a = b`` can be decided as identity of those
denotations — and this evaluator has none: it never interprets a term, it looks
an atom up by its rendered key in a world's valuation set. Run on ``a = b`` that
lookup would silently read the identity as an uninterpreted proposition keyed
``"a = b"``, so ``a = a`` would come out FALSE unless a caller happened to
list it, and ``□(a = b) → a = b`` would be decided by the frame alone. The kit's
rule is that an unsupported fragment is refused loudly, never approximated, so
:func:`satisfies_modal` (and so :func:`ctl_ex` / :func:`ctl_af` / :func:`ctl_eg`
/ :func:`ctl_au`, and every evaluator built on it) raises ``NotImplementedError``
naming the atom as soon as ANY ``=`` / ``≠`` atom occurs ANYWHERE in the formula
— the check scans the whole tree before evaluating, because evaluating lazily
would let a short-circuit (``P ∨ a = b`` at a world where ``P`` holds), a
vacuous ``□`` at a dead end, or an empty domain skip the atom and return a verdict
that never looked at it. Decide identity with :func:`unicode_logic_kit.fol.qml.qml_is_valid`
(quantified modal logic, where ``=`` is rigid identity over the object domain) or
a first-order route; the other arithmetic comparisons (``<``, ``≤`` …) are
ordinary keyed atoms here, exactly as before.

Second-order quantifiers (``SecondOrderQuantifier``, ``∀P φ`` / ``∃P φ``) are
interpreted. A bound predicate is an INTENSION: it has an extension of its own at
each world, so ``∀P`` ranges over every way of making each ground atom headed by
``P`` true or false at each world. For a propositional ``P`` that is every set of
worlds, and the frame conditions of correspondence theory become formulas of the
object language: ``∀P (□P → P)`` is true at ``w`` exactly when ``w`` sees itself,
and ``∀P (□P → □□P)`` exactly when every world two steps from ``w`` is one step
from it. For a ``P`` with arguments the ground atoms are the instances of its
applications in the body. An argument bound by an object quantifier inside the
body ranges over the individuals of EVERY world's domain: a predicate quantifier
is not restricted to what exists at one world (``hol.ho_modal`` types a property
``i ⇒ σ`` in every domain regime, for the same reason). Any other argument is the
term as written.

The evaluation is the one ``Down`` uses below: the quantifier is decided by
evaluating its body in the models that differ from the given one in the valuation
of those atoms. So an inner binder of the same name shadows the outer one, and
every operator of this module, announcements and group knowledge included, reads
a bound predicate like any other atom. One quantifier costs
``2 ** (worlds * instances)`` evaluations of its body, and
:data:`MAX_PREDICATE_INTERPRETATIONS` refuses a larger one.

Two limits come from a term being its own name here (see "Equality is NOT
interpreted" above):

- Two different ground terms are two individuals. ``∃P (P(a) ∧ ¬P(b))`` is
  therefore true in every model of this module, although a model in which ``a``
  and ``b`` name one individual falsifies it. An evaluation of ONE given model is
  not affected; a search over models is, and
  :func:`~unicode_logic_kit.atp.kripke_enum.modal_enum_search` refuses a formula
  in which bound predicates are applied to two different terms.
- A predicate in ARGUMENT position (third order, ``Pos(P)``) is part of the
  written form of an atom and nothing more. Under a quantifier that binds it the
  atom would not follow the quantifier, so it is refused by name.

Relation-name convention (keys of :attr:`KripkeModel.relations`):

- ``"alethic"``        — the accessibility relation for Box □ / Diamond ◇.
- ``"K:" + agent``     — the epistemic relation for ``Knows(agent, …)``, and
                         also what ``EverybodyKnows``/``DistributedKnowledge``/
                         ``CommonKnowledge`` (group operators E_G/D_G/C_G, see
                         below) combine by union/intersection/reflexive-
                         transitive-closure — there is no separate relation
                         family for the group operators.
- ``"B:" + agent``     — the doxastic relation for ``Believes(agent, …)``.
- ``"Say:" + agent``   — the assertive relation for ``Says(agent, …)`` (non-factive).
- ``"Want:" + agent``  — the bouletic relation for ``Wants(agent, …)`` (non-veridical).
- ``"temporal"``       — the one-step successor relation for Next / Always /
                         Eventually / Until.
- ``"deontic"``        — the (serial) accessibility relation for Obligatory O /
                         Permitted P (Standard Deontic Logic, the system KD).

A missing relation denotes the empty relation; a missing world valuation denotes
the empty set (every atom false there). Inputs are never mutated: the closure
and path helpers build fresh sets.

Hybrid logic H(@) is interpreted through the optional ``nominals`` mapping
(name → world): ``Nominal(i)`` is true exactly at the world the assignment
names, and ``At(i, φ)`` evaluates φ *at* that world, wherever the evaluation
currently stands. A nominal without an assignment raises a ValueError naming
it (rather than silently defaulting), since a nominal must name exactly one
world for the hybrid semantics to make sense.

The ↓ binder (N1, full H(@,↓)) — ``Down(x, φ)`` (``↓x.φ``) — is interpreted
the same way, with no extra machinery: evaluating ``Down(x, φ)`` at world
``w`` locally REBINDS the nominal named ``x`` to ``w`` for the evaluation of
``φ`` (still at ``w``), by recursing with a model whose ``nominals`` mapping
is ``model.nominals`` overridden at key ``x``. Because that override is a
plain dict-key overwrite — not a textual rewrite of ``φ`` — the usual
name-scoping rules of a binder fall out automatically, with no separate
alpha-renaming/fresh-name step: a nested ``Down(x, …)`` inside ``φ`` overrides
the SAME key again for its own (deeper) scope, so it shadows the outer
binding exactly the way a nested ``∀x`` would (``↓x.↓x.φ`` behaves as bare
``φ``, the outer binding entirely inert); a DIFFERENTLY-named nested binder
``Down(y, …)`` with ``y ≠ x`` extends the dict at a different key and leaves
``x`` untouched, so it cannot capture an outer ``@x``/bare-``x`` occurrence
(``↓x.(P ∧ ↓y.@x Q)`` — the inner ``↓y`` cannot affect the outer ``@x``); and
because the rebound world ``w`` is fixed in the dict rather than tracked
positionally, an occurrence of ``x`` reached through a LATER modality (a
``Box``/``Diamond`` inside ``φ`` moving evaluation to some other world
``w2``) still resolves to the ORIGINAL ``w`` — the state variable, once
bound, is rigid for the rest of its scope, exactly like a nominal already is
(this is what makes ``↓x.□¬x`` the FO irreflexivity condition: for every
successor ``w2`` of ``w``, ``¬x`` means "``w2`` is not the world ``x``
names", i.e. not ``w`` itself).

H(@,↓) validity is UNDECIDABLE, but evaluation at a GIVEN finite model is not
touched by that — ``satisfies_modal`` decides ``Down`` exactly as it decides
every other construct here, so it remains the terminating, always-available
"route A" oracle for ↓ (hand-built models, and the brute-force battery in
``tests/test_hybrid_down.py``), and the oracle
:func:`~unicode_logic_kit.atp.kripke_enum.modal_enum_search`'s bounded search
re-verifies every countermodel it reports against. See
:mod:`unicode_logic_kit.fol._hybrid_nodes` (the ``Down`` node) and
:mod:`unicode_logic_kit.fol.modal_translation` (``down_is_valid``, the
Z3/PROVED-only "route B" half) for the rest of the architecture.

Group epistemic operators — ``EverybodyKnows`` (E_G φ), ``DistributedKnowledge``
(D_G φ), and ``CommonKnowledge`` (C_G φ), each carrying a ``group`` tuple of
agent terms (:mod:`unicode_logic_kit.fol._modal_nodes`, parsed from
``E_{a,b,…}``/``D_{a,b,…}``/``C_{a,b,…}`` surface syntax) — are THIN dispatches
into :mod:`unicode_logic_kit.semantics.action_models`'s
:func:`~unicode_logic_kit.semantics.action_models.everybody_knows` /
:func:`~unicode_logic_kit.semantics.action_models.distributed_knowledge_holds` /
:func:`~unicode_logic_kit.semantics.action_models.common_knowledge_holds`, which
implement the actual union/intersection/closure semantics over the group's
``"K:"+agent`` relations — this module owns none of that logic, only the
node-to-function wiring (see those functions' docstrings for the semantics,
including ``distributed_knowledge_holds``'s deliberately-different empty-group
convention: it RAISES rather than defaulting).

Public announcement logic (PAL) is interpreted directly — ``Announce`` (``[φ!]ψ``)
and ``AnnounceDiamond`` (``⟨φ!⟩ψ``) are the only two constructs here that do NOT
just recurse at a fixed world or along a fixed relation: they build the
φ-restricted model ``M|φ`` (:func:`unicode_logic_kit.semantics.dynamic_epistemic.announce`)
and evaluate ``ψ`` there. This is the ORACLE that
:func:`unicode_logic_kit.fol.pal.reduce_announcements` (a purely SYNTACTIC
elimination of Announce/AnnounceDiamond, sound only for the propositional-modal
fragment interpreted here) is differentially tested against.

Documented temporal semantics:

- ``Next φ``: φ holds at **all** immediate ``"temporal"``-successors of the
  current world. On a deterministic / linear frame (each world has at most one
  successor) this is exactly "φ at the unique next state"; on a branching frame
  it is read universally (the "for all next states" reading).
- ``Always φ`` (G): φ holds at every world reachable from the current world via
  the **reflexive-transitive** closure of ``"temporal"`` (the current world
  included).
- ``Eventually φ`` (F): φ holds at **some** such reachable world (current world
  included).
- ``Until(φ, ψ)``: there is a finite ``"temporal"`` path
  ``w0 → w1 → … → wn`` (n ≥ 0) starting at the current world with ψ true at
  ``wn`` and φ true at every earlier world ``w0 … w(n-1)``. This is the
  finite-reachability reading of strong Until; the search is depth-first with a
  visited guard so cycles in the frame terminate.

Next / Always / Eventually / Until above are all LINEAR-time: each has exactly
one path reading baked into its single AST node (no A/E path-quantifier prefix
exists anywhere in the AST). Branching-time CTL model checking —
:func:`ctl_ex`, :func:`ctl_af`, :func:`ctl_eg`, :func:`ctl_au` — adds the four
readings that baked-in choice leaves out (EX, the existential dual of Next's
universal reading; AF/EG, the forward/backward fixpoint pair that reachability
alone cannot compute; AU, the universal-path generalisation of Until) as plain
functions taking arbitrary :class:`~unicode_logic_kit.fol.nodes.Node`
subformulas, evaluated via :func:`satisfies_modal` — exactly the pattern
:func:`~unicode_logic_kit.semantics.action_models.common_knowledge_holds` and
:func:`~unicode_logic_kit.semantics.action_models.everybody_knows` already use,
not new dispatch branches on ``formula``'s type. See the CTL section near the
end of this module for the fixpoint algorithms and the deadlock convention.
"""

import shutil
import subprocess
from itertools import product
from typing import Any, Dict, FrozenSet, Iterable, Iterator, List, Mapping, Optional, Set, Tuple

from ..fol.nodes import (
    Node,
    Atom, Not, And, Or, Xor, Implies, Iff,
    Quantifier, SecondOrderQuantifier, PredicateTerm,
    Box, Diamond, Knows, Believes, Says, Wants,
    Always, Eventually, Next, Until,
    Historically, Once, Previous, Since,
    Obligatory, Permitted,
    Nominal, At, Down,
    Constant, Variable, substitute, sort_membership_axioms,
)
from ..fol._modal_nodes import (
    Announce, AnnounceDiamond,
    EverybodyKnows, DistributedKnowledge, CommonKnowledge,
)
from ..fol._atom_keys import atom_key, find_key, other_key
from ..fol._msfl_nodes import _SORTED_NODE_TYPES, key_text
from ..fol._truth_constants import truth_value as _truth_value
from ._modal_reject import (
    EQUALITY_PREDICATES, FUZZY_TYPES, LAMBDA_TYPES,
    reject_equality, reject_equality_in, reject_fuzzy, reject_lambda,
)

# Quantifier-type spellings used by the AST.
_FORALL = ("∀", "forall")
_EXISTS = ("∃", "exists")

# Relation-name prefixes / keys (kept here so the model and the standard
# translation stay in sync via documentation; the strings are the contract).
_ALETHIC = "alethic"
_TEMPORAL = "temporal"
_DEONTIC = "deontic"
_KNOWS_PREFIX = "K:"
_BELIEVES_PREFIX = "B:"
_SAYS_PREFIX = "Say:"
_WANTS_PREFIX = "Want:"


def _agent_key(agent: Node) -> str:
    """Relation-key suffix for an epistemic/doxastic agent term.

    The agent is a term (Variable or Constant). Object quantifiers ground a bound
    agent to a Constant before the modality is reached (``∀x (… → K_x φ)`` becomes
    ``K_<d> φ`` per individual ``d``), so this is the constant/variable name and the
    relation key matches the model's ``"K:"+name`` / ``"B:"+name`` convention. A term
    without a name of its own (a numeral) is keyed by its text with every constant
    written by its name, like an atom: a relation name is a key, not formula text.
    """
    return getattr(agent, "name", None) or key_text(agent)


World = Any
Edge = Tuple[World, World]


class KripkeModel:
    """A Kripke model: worlds, named accessibility relations, and a valuation.

    Args:
        worlds: an iterable of worlds (any hashable values). Stored as a frozen
            set; duplicates collapse.
        relations: maps a relation NAME (str) to a set of ``(w, w')`` edges.
            Recognised names: ``"alethic"`` (Box/Diamond), ``"K:"+agent``
            (Knows), ``"B:"+agent`` (Believes), ``"temporal"`` (Next / Always /
            Eventually / Until), ``"deontic"`` (Obligatory / Permitted; serial
            in Standard Deontic Logic). A missing name is the empty relation.
            Each edge set is copied into a frozen set.
        valuation: maps a world to the set of GROUND-ATOM KEYS true there, where
            a key is the text of the atom with every constant written by its name
            (e.g. ``"P"`` or ``"Likes(a, b)"``; :func:`~unicode_logic_kit.fol.atom_key`).
            The text of the atom as a formula, ``"Likes('a', 'b')"``, is read as the
            same key.
            A missing world maps to the empty set (every atom false there). Each
            entry is copied into a frozen set.
        nominals: maps a NOMINAL NAME (str) to the single world it names (the
            hybrid-logic assignment interpreting ``Nominal`` / ``At``). Defaults
            to empty. Every referenced world must be in ``worlds`` — a dangling
            assignment raises ValueError at construction time.

    All mappings default to empty, so ``KripkeModel({0, 1})`` is a valid
    (atom-free, relation-free) frame. The constructor copies every container, so
    later edits to the caller's structures never leak in.
    """

    def __init__(
        self,
        worlds: Iterable[World],
        relations: Optional[Mapping[str, Iterable[Edge]]] = None,
        valuation: Optional[Mapping[World, Iterable[str]]] = None,
        domains: Optional[Mapping[World, Iterable[Any]]] = None,
        domain: Optional[Iterable[Any]] = None,
        nominals: Optional[Mapping[str, World]] = None,
    ):
        """Build a Kripke model, copying every container so edits never leak in.

        ``domains`` maps each world to the set of individuals existing there (the
        per-world object domain ``D_w`` of quantified modal logic); ``domain`` is a
        shorthand for a **constant** domain (the same individuals at every world).
        Supplying either lets :func:`satisfies_modal` interpret object quantifiers
        (``∀x`` / ``∃x``) *actualistically* — at a world ``w`` they range over
        ``D_w`` — so the Barcan formulas come out valid or invalid according to how
        the domains vary. Omit both for the purely propositional fragment.

        ``nominals`` maps each hybrid nominal name to the ONE world it names;
        every referenced world must exist in ``worlds`` (checked here, so a
        dangling nominal fails fast instead of at evaluation time).
        """
        self.worlds: FrozenSet[World] = frozenset(worlds)
        self.relations: Dict[str, FrozenSet[Edge]] = {
            name: frozenset(edges) for name, edges in (relations or {}).items()
        }
        self.valuation: Dict[World, FrozenSet[str]] = {
            world: frozenset(keys) for world, keys in (valuation or {}).items()
        }
        if domains is not None:
            self.domains: Optional[Dict[World, FrozenSet[Any]]] = {
                world: frozenset(ind) for world, ind in domains.items()
            }
        elif domain is not None:
            const = frozenset(domain)
            self.domains = {world: const for world in self.worlds}
        else:
            self.domains = None
        self.nominals: Dict[str, World] = dict(nominals or {})
        for name, named in self.nominals.items():
            if named not in self.worlds:
                raise ValueError(
                    f"KripkeModel: nominal {name!r} is assigned to world "
                    f"{named!r}, which is not among the model's worlds."
                )

    def __repr__(self) -> str:
        """Show world count and the relation / valuation tables for inspection."""
        return (
            f"KripkeModel(worlds={set(self.worlds)!r}, "
            f"relations={ {k: set(v) for k, v in self.relations.items()} !r}, "
            f"valuation={ {k: set(v) for k, v in self.valuation.items()} !r})"
        )

    def relation(self, name: str) -> FrozenSet[Edge]:
        """Return the edge set of a named relation (empty if undeclared)."""
        return self.relations.get(name, frozenset())

    def successors(self, name: str, world: World) -> Set[World]:
        """Return the set of ``w'`` with ``(world, w')`` in the named relation."""
        return {w2 for (w1, w2) in self.relation(name) if w1 == world}

    def atoms_true_at(self, world: World) -> FrozenSet[str]:
        """Return the ground-atom keys true at ``world`` (empty if undeclared)."""
        return self.valuation.get(world, frozenset())

    def domain_at(self, world: World) -> FrozenSet[Any]:
        """Return the individuals existing at ``world`` (the object domain ``D_w``).

        Raises ValueError if the model carries no domains (a purely propositional
        model), since object quantifiers cannot then be interpreted.
        """
        if self.domains is None:
            raise ValueError(
                "satisfies_modal: this Kripke model has no object domains, so "
                "object quantifiers (∀x / ∃x) cannot be evaluated — build the model "
                "with domains={world: [...]} (varying) or domain=[...] (constant)."
            )
        return self.domains.get(world, frozenset())

    def to_dot(self, *, show_valuation: bool = True) -> str:
        """Render the model as a Graphviz DOT digraph string.

        Pure Python, no external dependency — mirrors the convention of
        :meth:`~unicode_logic_kit.fol._fol_nodes.Node.to_dot` (escape labels the
        same way; return the source text, never shell out). One node per world
        in :attr:`worlds`, declared in ``repr()`` order for determinism (worlds
        are "any hashable value", so a world is stringified defensively via
        ``repr()`` for the DOT node id and via ``str()`` for the visible
        label). When ``show_valuation`` is true (the default) each node's label
        gets a second line with the atoms :meth:`atoms_true_at` returns for
        that world plus any nominal name(s) (from :attr:`nominals`) pointing at
        it, prefixed ``@``; if the model carries object domains (see
        :meth:`domain_at`), a third line shows that world's domain.

        Every relation in :attr:`relations` contributes one edge per ``(w, w')``
        pair, labelled with the relation's own name — this is the one place a
        naive per-pair rendering would lose information, since a model can
        carry several named relations over the same world set at once (several
        agents' ``K:``/``B:`` relations, ``alethic``, ``temporal``, ``deontic``
        all coexisting); the relation-name label is what keeps them visually
        distinguishable instead of collapsing into indistinguishable arrows.
        Relations and, within each, their edges are emitted in sorted order too,
        so the whole output is deterministic and directly string-comparable.

        This is a read-only inspection method: it never touches model
        construction or :func:`satisfies_modal`.
        """
        def esc(text: str) -> str:
            """Escape backslash/quote/newline/CR for safe placement inside a
            double-quoted DOT string, on a single physical source line."""
            return (
                text.replace("\\", "\\\\")
                    .replace('"', '\\"')
                    .replace("\n", "\\n")
                    .replace("\r", "\\r")
            )

        def node_id(world: World) -> str:
            """The DOT node id for a world: its escaped ``repr()``."""
            return esc(repr(world))

        nominals_at: Dict[World, List[str]] = {}
        for name, named in self.nominals.items():
            nominals_at.setdefault(named, []).append(name)

        lines = ["digraph Kripke {", "  node [shape=box];"]
        for world in sorted(self.worlds, key=repr):
            label_lines = [esc(str(world))]
            if show_valuation:
                bits = sorted(self.atoms_true_at(world))
                bits += [f"@{n}" for n in sorted(nominals_at.get(world, []))]
                label_lines.append(esc(", ".join(bits)))
                if self.domains is not None:
                    dom = ", ".join(sorted(str(d) for d in self.domain_at(world)))
                    label_lines.append(esc(f"D = {{{dom}}}"))
            label = "\\n".join(label_lines)
            lines.append(f'  "{node_id(world)}" [label="{label}"];')

        for rel_name in sorted(self.relations):
            edges = sorted(
                self.relations[rel_name],
                key=lambda edge: (repr(edge[0]), repr(edge[1])),
            )
            rel_label = esc(rel_name)
            for source, target in edges:
                lines.append(
                    f'  "{node_id(source)}" -> "{node_id(target)}" '
                    f'[label="{rel_label}"];'
                )

        lines.append("}")
        return "\n".join(lines)

    def to_svg(self, *, dot_binary: Optional[str] = None) -> str:
        """Render the model to SVG by piping :meth:`to_dot` through Graphviz ``dot``.

        Resolves the binary via ``dot_binary`` or ``shutil.which("dot")`` and,
        if neither finds one, raises ``RuntimeError`` naming the missing tool
        and how to install it — the same shutil.which-gate-and-fail-loudly
        pattern already used for the optional external provers (eprover,
        minizinc, vampire, prover9, Isabelle) elsewhere in this kit: this never
        falls back to an approximate or partial rendering.

        Args:
            dot_binary: an explicit path to the ``dot`` executable, overriding
                ``PATH`` discovery.

        Raises:
            RuntimeError: no ``dot`` binary found, the given/discovered binary
                could not be executed, or the ``dot`` subprocess itself failed
                (its stderr is included in the message).
        """
        binary = dot_binary or shutil.which("dot")
        if binary is None:
            raise RuntimeError(
                "KripkeModel.to_svg: no Graphviz 'dot' binary found on PATH — "
                "install Graphviz (e.g. 'apt install graphviz', 'brew install "
                "graphviz', or see https://graphviz.org/download/) or pass "
                "to_svg(dot_binary=...) explicitly."
            )
        try:
            result = subprocess.run(
                [binary, "-Tsvg"],
                input=self.to_dot(),
                capture_output=True,
                text=True,
            )
        except OSError as exc:
            raise RuntimeError(
                f"KripkeModel.to_svg: could not run {binary!r} ({exc}) — is "
                "this a valid Graphviz 'dot' binary?"
            ) from exc
        if result.returncode != 0:
            raise RuntimeError(
                f"KripkeModel.to_svg: 'dot -Tsvg' failed (exit "
                f"{result.returncode}): {result.stderr.strip()}"
            )
        return result.stdout

    def _repr_svg_(self) -> Optional[str]:
        """IPython/Jupyter rich-display hook: render to SVG, or opt out quietly.

        Returns ``None`` (so the notebook falls back to the plain ``__repr__``
        text) instead of raising when Graphviz's ``dot`` binary — or the
        subprocess call to it — is not available, so merely inspecting a
        KripkeModel in a notebook without Graphviz installed never crashes the
        display machinery.
        """
        try:
            return self.to_svg()
        except RuntimeError:
            return None


def reflexive_transitive_closure(
    edges: Iterable[Edge],
    sources: Iterable[World],
) -> Set[World]:
    """Return every world reachable from ``sources`` along ``edges``, reflexively.

    The result contains each source world itself (reflexive) and every world
    reachable from a source by following one or more edges (transitive). A
    breadth-first walk with a visited set; the input edge collection is never
    mutated. Used by Always / Eventually over the ``"temporal"`` relation.
    """
    edge_set = set(edges)
    reachable: Set[World] = set()
    frontier = list(sources)
    while frontier:
        w = frontier.pop()
        if w in reachable:
            continue
        reachable.add(w)
        for (w1, w2) in edge_set:
            if w1 == w and w2 not in reachable:
                frontier.append(w2)
    return reachable


def _until_holds(
    left: Node,
    right: Node,
    model: KripkeModel,
    world: World,
) -> bool:
    """Decide ``Until(left, right)`` at ``world`` by finite-path search.

    Searches for a finite ``"temporal"`` path ``world = w0 → … → wn`` (n ≥ 0)
    with ``right`` true at ``wn`` and ``left`` true at every earlier ``wi``. A
    depth-first search guarded by a visited set: if ``right`` already holds we
    succeed immediately (n = 0); otherwise ``left`` must hold here and the
    search continues into the temporal successors. The visited guard makes the
    search terminate on cyclic frames.
    """
    edges = model.relation(_TEMPORAL)

    def search(w: World, visited: FrozenSet[World]) -> bool:
        """Return whether some path from ``w`` witnesses the Until."""
        if satisfies_modal(right, model, w):
            return True
        if not satisfies_modal(left, model, w):
            return False
        next_visited = visited | {w}
        for w2 in {b for (a, b) in edges if a == w}:
            if w2 not in next_visited and search(w2, next_visited):
                return True
        return False

    return search(world, frozenset())


def _predecessors(model: KripkeModel, name: str, world: World) -> Set[World]:
    """Return the set of ``w'`` with ``(w', world)`` in the named relation (its converse successors)."""
    return {w1 for (w1, w2) in model.relation(name) if w2 == world}


def _since_holds(
    left: Node,
    right: Node,
    model: KripkeModel,
    world: World,
) -> bool:
    """Decide ``Since(left, right)`` at ``world`` — the backward mirror of Until.

    Searches for a finite ``"temporal"`` path into the PAST
    ``world = w0 ← w1 ← … ← wn`` (each step ``(w(i+1), wi)`` a temporal edge, n ≥ 0)
    with ``right`` true at ``wn`` and ``left`` true at every later ``wi`` (i < n). A
    depth-first search guarded by a visited set, so cyclic frames terminate.
    """
    edges = model.relation(_TEMPORAL)

    def search(w: World, visited: FrozenSet[World]) -> bool:
        """Return whether some backward path from ``w`` witnesses the Since."""
        if satisfies_modal(right, model, w):
            return True
        if not satisfies_modal(left, model, w):
            return False
        next_visited = visited | {w}
        for w0 in {a for (a, b) in edges if b == w}:
            if w0 not in next_visited and search(w0, next_visited):
                return True
        return False

    return search(world, frozenset())


def _nominal_world(model: KripkeModel, name: str) -> World:
    """Return the world the nominal ``name`` names; raise if it is unassigned.

    A nominal must name exactly one world, so an assignment-free nominal is a
    modelling error — the ValueError names the offending nominal and shows the
    ``nominals=`` fix rather than silently picking a truth value.
    """
    if name not in model.nominals:
        raise ValueError(
            f"satisfies_modal: the nominal {name!r} has no world assignment in "
            f"this model — build the KripkeModel with nominals={{{name!r}: world}}."
        )
    return model.nominals[name]


#: Safety cap on one predicate quantifier in :func:`satisfies_modal`. ``∀P`` / ``∃P`` ranges
#: over every interpretation of ``P`` at every world: ``2 ** (worlds * instances)`` of them,
#: where the instances are the ground atoms headed by ``P`` that the body can reach. Past
#: this many the quantifier raises instead of running; raise this module attribute if you
#: really mean to enumerate more.
MAX_PREDICATE_INTERPRETATIONS = 1 << 20


def _bound_instances(node: SecondOrderQuantifier, model: KripkeModel) -> List[Atom]:
    """The ground atoms headed by the predicate ``node`` binds that its body can reach.

    An application of the bound predicate whose arguments are all terms as written
    (constants, or variables that no quantifier of the body binds) is one atom. An argument
    bound by an object quantifier INSIDE the body is a variable still: it is given every
    individual of every world's domain in turn, by the substitution
    :func:`satisfies_modal` itself makes when it reaches that quantifier, so the atoms listed
    here are exactly the atoms an evaluation can look up. The scope of an inner quantifier
    over the same predicate name is skipped, since its atoms are its own.

    Returned in the order of their keys, each key once.

    Raises:
        NotImplementedError: the bound predicate stands in ARGUMENT position (third order).
        ValueError: the bound predicate is applied at another arity than the quantifier
            states (a hand-built node; the parser infers the arity from the applications),
            or an argument is bound by an object quantifier and the model has no domains.
    """
    name = node.predicate
    individuals: List[Any] = []
    domains_read = False

    def every_individual() -> List[Any]:
        nonlocal domains_read
        if not domains_read:
            seen: Set[Any] = set()
            for w in model.worlds:
                seen |= model.domain_at(w)
            individuals.extend(sorted(seen, key=repr))
            domains_read = True
        return individuals

    found: Dict[str, Atom] = {}

    def visit(sub: Node, bound: Tuple[str, ...]) -> None:
        if isinstance(sub, SecondOrderQuantifier) and sub.predicate == name:
            return
        if isinstance(sub, PredicateTerm):
            if sub.name == name:
                raise NotImplementedError(
                    f"satisfies_modal: the predicate {name} is bound by "
                    f"{node.type}{name} and stands in argument position (third order). "
                    f"The Kripke evaluator reads an atom by its written form and has no "
                    f"reading of a property as an argument; export the formula with "
                    f"hol.ho_modal for a higher-order prover.")
            return
        if isinstance(sub, Atom) and sub.predicate == name:
            if len(sub.args) != node.arity:
                raise ValueError(
                    f"satisfies_modal: {node.type}{name} binds a predicate of arity "
                    f"{node.arity}, and its body applies {name} to {len(sub.args)} "
                    f"argument(s) in {sub.to_unicode_str()!r}. A bound predicate has one "
                    f"arity.")
            written = {v.name for v in sub.walk() if isinstance(v, Variable)}
            variables = [v for v in bound if v in written]
            assignments = product(every_individual(), repeat=len(variables)) if variables else [()]
            for values in assignments:
                instance: Node = sub
                for variable, individual in zip(variables, values):
                    instance = substitute(instance, Variable(variable), Constant(individual))
                assert isinstance(instance, Atom)
                found.setdefault(atom_key(instance), instance)
        if isinstance(sub, Quantifier):
            inner = bound if sub.variable.name in bound else bound + (sub.variable.name,)
            visit(sub.formula, inner)
            return
        for child in sub._child_nodes():
            visit(child, bound)

    visit(node.formula, ())
    return [found[key] for key in sorted(found)]


def _predicate_interpretations(node: SecondOrderQuantifier,
                               model: KripkeModel) -> Iterator[KripkeModel]:
    """Every model that differs from ``model`` only in what the predicate ``node`` binds is.

    A bound predicate is an intension: it has an extension at each world. So an
    interpretation settles, for every world and every atom of :func:`_bound_instances`,
    whether the atom is true there, and there are ``2 ** (worlds * instances)`` of them.
    Each is yielded as a model whose valuation says exactly that about those atoms (under
    either spelling of their key) and agrees with ``model`` on every other atom; frame,
    domains and nominals are ``model``'s. The order is fixed: worlds by ``repr``, atoms by
    key, one bit each.

    Raises:
        ValueError: more than :data:`MAX_PREDICATE_INTERPRETATIONS` interpretations.
    """
    instances = _bound_instances(node, model)
    worlds = sorted(model.worlds, key=repr)
    keys = [atom_key(atom) for atom in instances]
    spellings = set(keys)
    for atom in instances:
        other = other_key(atom)
        if other is not None:
            spellings.add(other)
    width = len(worlds) * len(keys)
    if (1 << width) > MAX_PREDICATE_INTERPRETATIONS:
        raise ValueError(
            f"satisfies_modal: the predicate quantifier {node.type}{node.predicate} ranges "
            f"over 2 ** ({len(worlds)} worlds * {len(keys)} atoms) = 2 ** {width} "
            f"interpretations, above MAX_PREDICATE_INTERPRETATIONS = "
            f"{MAX_PREDICATE_INTERPRETATIONS}. Shrink the model (or raise "
            f"kripke.MAX_PREDICATE_INTERPRETATIONS).")
    kept = {w: model.atoms_true_at(w) - spellings for w in worlds}
    per_world = (1 << len(keys)) - 1
    for mask in range(1 << width):
        valuation = {}
        for position, w in enumerate(worlds):
            bits = (mask >> (position * len(keys))) & per_world
            valuation[w] = kept[w] | {keys[i] for i in range(len(keys)) if (bits >> i) & 1}
        yield KripkeModel(model.worlds, model.relations, valuation,
                          domains=model.domains, nominals=model.nominals)


def satisfies_modal(formula: Node, model: KripkeModel, world: World) -> bool:
    """Return whether ``formula`` is true at ``world`` in the Kripke ``model``.

    The Kripke satisfaction relation for the propositional / ground modal
    fragment:

    - ``Atom`` — its Unicode key is in the world's valuation.
    - ``Nominal i`` — true iff ``world`` IS the world ``model.nominals[i]``
      names (a nominal holds at exactly one world).
    - ``At(i, φ)`` — φ holds at the world named ``i``, regardless of the
      current world (the hybrid satisfaction operator ``@i φ``).
    - ``Not / And / Or / Xor / Implies / Iff`` — the classical truth tables,
      recursing at the **same** world.
    - ``Box φ`` — φ holds at every ``"alethic"``-successor; ``Diamond φ`` — at
      some ``"alethic"``-successor.
    - ``Knows(a, φ)`` — φ holds at every ``"K:"+a``-successor (universal).
    - ``Believes(a, φ)`` — φ holds at every ``"B:"+a``-successor (universal).
    - ``EverybodyKnows(G, φ)`` (E_G φ) / ``DistributedKnowledge(G, φ)``
      (D_G φ) / ``CommonKnowledge(G, φ)`` (C_G φ) — dispatched to
      :func:`~unicode_logic_kit.semantics.action_models.everybody_knows` /
      :func:`~unicode_logic_kit.semantics.action_models.distributed_knowledge_holds`
      / :func:`~unicode_logic_kit.semantics.action_models.common_knowledge_holds`
      (see the module docstring).
    - ``Obligatory φ`` — φ holds at every ``"deontic"``-successor (universal);
      ``Permitted φ`` — at some ``"deontic"``-successor.
    - ``Next φ`` — φ holds at every immediate ``"temporal"``-successor.
    - ``Always φ`` / ``Eventually φ`` — φ holds at all / some worlds in the
      reflexive-transitive closure of ``"temporal"`` from ``world``.
    - ``Until(φ, ψ)`` — see :func:`_until_holds` (finite-path strong Until).
    - ``Announce(φ, ψ)`` (``[φ!]ψ``) — ``φ`` false at ``world`` makes this
      vacuously true; otherwise ``ψ`` must hold at ``world`` in the model
      restricted to the ``φ``-worlds (:func:`~unicode_logic_kit.semantics.dynamic_epistemic.announce`).
    - ``AnnounceDiamond(φ, ψ)`` (``⟨φ!⟩ψ``) — the dual: ``φ`` true at ``world``
      AND ``ψ`` holds at ``world`` in the ``φ``-restricted model.
    - ``SecondOrderQuantifier`` (``∀P φ`` / ``∃P φ``) — φ holds at ``world`` under
      every / some interpretation of ``P``, where an interpretation gives ``P`` an
      extension at EACH world (see the module docstring's "Second-order
      quantifiers" section).

    A many-sorted ``formula`` (``SortedQuantifier`` / ``SortedConstant``, ``∀x:S φ``
    / ``∃x:S φ`` / a bare ``alice:Human``) is relativized ONCE, here, before
    anything else runs — see the module docstring's "Many-sorted formulas"
    section for what that does and does not assume (world-relative, not rigid;
    non-empty only if the model says so; a sorted constant is in its sort only
    if the model puts ``S(c)`` in every world's valuation — see
    :func:`sorted_constant_violations`).

    Raises:
        NotImplementedError: on a Łukasiewicz node or a lambda node (checked
            BEFORE relativizing, since relativizing runs a whole-tree
            structural recursion that would otherwise reach one of these
            first and raise a less specific error), and on an equality /
            disequality atom (``=`` / ``≠``) anywhere in the formula — see the
            module docstring's "Equality is NOT interpreted" section. Also on a
            predicate that is bound by a ``∀P`` / ``∃P`` and stands in argument
            position (third order), and on a bound predicate that has the name
            of a sort of the formula.
        ValueError: on a predicate quantifier that would enumerate more than
            :data:`MAX_PREDICATE_INTERPRETATIONS` interpretations.
    """
    # --- many-sorted formulas: relativize the WHOLE formula once, here, before
    # any dispatch below — see the docstring above and the module docstring's
    # "Many-sorted formulas" section. Reject any Łukasiewicz / lambda node
    # FIRST, by walking the whole (pre-relativize) tree: Node._relativize is
    # an unconditional structural descent into every child (Node.map_children),
    # so if a fuzzy/lambda node sat anywhere in the formula -- not only at the
    # very top -- relativizing before this check would reach it first and
    # raise a generic RuntimeError ("call to_msfol() before _relativize")
    # instead of this function's own documented NotImplementedError contract
    # (see test_fuzzy_node_rejected / test_lambda_node_rejected). ---
    sorts: Set[str] = set()
    bound_predicates: Set[str] = set()
    for node in formula.walk():
        if isinstance(node, FUZZY_TYPES):
            reject_fuzzy(node, "satisfies_modal")
        if isinstance(node, LAMBDA_TYPES):
            reject_lambda(node, "satisfies_modal")
        # Equality has no interpretation here (module docstring); refuse it by
        # name from the WHOLE tree, up front, so no short-circuit or vacuous
        # branch can let an equality atom through unexamined.
        reject_equality(node, "satisfies_modal")
        if isinstance(node, _SORTED_NODE_TYPES):
            sorts.add(node.sort)
        elif isinstance(node, SecondOrderQuantifier):
            bound_predicates.add(node.predicate)
    # A sort and the unary predicate of its name are one symbol, and relativizing writes
    # the sort as that predicate: a quantifier over the name would capture the guard of
    # ``∀x:S`` and leave the sort itself unbound. Refused as the second-order search
    # (``semantics.secondorder``) refuses it.
    clash = sorted(sorts & bound_predicates)
    if clash:
        raise NotImplementedError(
            f"satisfies_modal: the predicate variable {clash[0]!r} that a second-order "
            f"quantifier binds has the name of a sort of the formula. A sort and the unary "
            f"predicate of its name are ONE symbol, so a quantifier over it would rebind "
            f"the predicate but not the sort; rename the bound predicate variable.")
    formula = formula._relativize([])

    # --- atomic ---
    if isinstance(formula, Atom):
        constant = _truth_value(formula)
        if constant is not None:
            return constant         # `$true` / `$false`: the same at every world
        # The key of the atom first, then its formula text: an element ``a`` of a domain is
        # substituted as ``Constant("a")``, which the formula text writes ``P('a')``, and the
        # valuation holds the key the user typed, ``P(a)``, or the text of the atom as a
        # formula, ``P('a')``, which the guide taught as the key of a hand-built atom.
        return find_key(model.atoms_true_at(world), formula) is not None

    # --- hybrid: a nominal is true exactly at the world it names; @ jumps there ---
    if isinstance(formula, Nominal):
        return world == _nominal_world(model, formula.name)
    if isinstance(formula, At):
        return satisfies_modal(formula.formula, model,
                               _nominal_world(model, formula.nominal.name))
    if isinstance(formula, Down):
        # ↓x.φ at world: locally rebind the nominal x to THIS world for φ's
        # evaluation (still at the same world) — see the module docstring's
        # "The ↓ binder" section for why this plain dict-override, with no
        # separate alpha-renaming step, already gets shadowing / no-capture /
        # rigidity right. KripkeModel's own constructor re-validates the
        # (harmless, since world ∈ model.worlds whenever a caller reached
        # here in the first place) new nominal assignment.
        rebound = KripkeModel(
            model.worlds, model.relations, model.valuation,
            domains=model.domains,
            nominals={**model.nominals, formula.variable.name: world},
        )
        return satisfies_modal(formula.formula, rebound, world)

    # --- classical connectives (recurse at the same world) ---
    if isinstance(formula, Not):
        return not satisfies_modal(formula.formula, model, world)
    if isinstance(formula, And):
        return (satisfies_modal(formula.left, model, world)
                and satisfies_modal(formula.right, model, world))
    if isinstance(formula, Or):
        return (satisfies_modal(formula.left, model, world)
                or satisfies_modal(formula.right, model, world))
    if isinstance(formula, Xor):
        return (satisfies_modal(formula.left, model, world)
                != satisfies_modal(formula.right, model, world))
    if isinstance(formula, Implies):
        return ((not satisfies_modal(formula.left, model, world))
                or satisfies_modal(formula.right, model, world))
    if isinstance(formula, Iff):
        return (satisfies_modal(formula.left, model, world)
                == satisfies_modal(formula.right, model, world))

    # --- alethic ---
    if isinstance(formula, Box):
        return all(
            satisfies_modal(formula.formula, model, w2)
            for w2 in model.successors(_ALETHIC, world)
        )
    if isinstance(formula, Diamond):
        return any(
            satisfies_modal(formula.formula, model, w2)
            for w2 in model.successors(_ALETHIC, world)
        )

    # --- epistemic / doxastic (both universal) ---
    if isinstance(formula, Knows):
        return all(
            satisfies_modal(formula.formula, model, w2)
            for w2 in model.successors(_KNOWS_PREFIX + _agent_key(formula.agent), world)
        )
    if isinstance(formula, Believes):
        return all(
            satisfies_modal(formula.formula, model, w2)
            for w2 in model.successors(_BELIEVES_PREFIX + _agent_key(formula.agent), world)
        )

    # --- group epistemic (everyone/distributed/common knowledge): thin
    # dispatch into semantics.action_models, exactly like Announce dispatches
    # into semantics.dynamic_epistemic.announce below. Lazy import: action_models
    # imports THIS module at load time (KripkeModel/satisfies_modal/
    # reflexive_transitive_closure), so a module-level import here would cycle. ---
    if isinstance(formula, EverybodyKnows):
        from .action_models import everybody_knows
        agents = [_agent_key(a) for a in formula.group]
        return everybody_knows(model, world, agents, formula.formula)
    if isinstance(formula, DistributedKnowledge):
        from .action_models import distributed_knowledge_holds
        agents = [_agent_key(a) for a in formula.group]
        return distributed_knowledge_holds(model, world, agents, formula.formula)
    if isinstance(formula, CommonKnowledge):
        from .action_models import common_knowledge_holds
        agents = [_agent_key(a) for a in formula.group]
        return common_knowledge_holds(model, world, agents, formula.formula)

    # --- assertive / bouletic (both universal K-modalities, no frame conditions:
    # Says is non-factive / non-doxastic, Wants is non-veridical) ---
    if isinstance(formula, Says):
        return all(
            satisfies_modal(formula.formula, model, w2)
            for w2 in model.successors(_SAYS_PREFIX + _agent_key(formula.agent), world)
        )
    if isinstance(formula, Wants):
        return all(
            satisfies_modal(formula.formula, model, w2)
            for w2 in model.successors(_WANTS_PREFIX + _agent_key(formula.agent), world)
        )

    # --- deontic (Standard Deontic Logic / KD over a serial "deontic" relation) ---
    if isinstance(formula, Obligatory):
        return all(
            satisfies_modal(formula.formula, model, w2)
            for w2 in model.successors(_DEONTIC, world)
        )
    if isinstance(formula, Permitted):
        return any(
            satisfies_modal(formula.formula, model, w2)
            for w2 in model.successors(_DEONTIC, world)
        )

    # --- temporal ---
    if isinstance(formula, Next):
        return all(
            satisfies_modal(formula.formula, model, w2)
            for w2 in model.successors(_TEMPORAL, world)
        )
    if isinstance(formula, Always):
        reachable = reflexive_transitive_closure(model.relation(_TEMPORAL), [world])
        return all(
            satisfies_modal(formula.formula, model, w2) for w2 in reachable
        )
    if isinstance(formula, Eventually):
        reachable = reflexive_transitive_closure(model.relation(_TEMPORAL), [world])
        return any(
            satisfies_modal(formula.formula, model, w2) for w2 in reachable
        )
    if isinstance(formula, Until):
        return _until_holds(formula.left, formula.right, model, world)

    # --- past tense (over the CONVERSE of the one-step "temporal" relation) ---
    if isinstance(formula, Previous):
        return all(
            satisfies_modal(formula.formula, model, w2)
            for w2 in _predecessors(model, _TEMPORAL, world)
        )
    if isinstance(formula, Historically):
        reverse = [(b, a) for (a, b) in model.relation(_TEMPORAL)]
        reachable = reflexive_transitive_closure(reverse, [world])
        return all(satisfies_modal(formula.formula, model, w2) for w2 in reachable)
    if isinstance(formula, Once):
        reverse = [(b, a) for (a, b) in model.relation(_TEMPORAL)]
        reachable = reflexive_transitive_closure(reverse, [world])
        return any(satisfies_modal(formula.formula, model, w2) for w2 in reachable)
    if isinstance(formula, Since):
        return _since_holds(formula.left, formula.right, model, world)

    # --- public announcement logic (PAL): a genuine MODEL UPDATE, not a fixed
    # accessibility relation — this is the ORACLE unicode_logic_kit.fol.pal
    # .reduce_announcements is differentially tested against (see that module's
    # docstring for the correctness argument relating the two). Both build the
    # restricted model M|announcement via
    # unicode_logic_kit.semantics.dynamic_epistemic.announce (imported lazily to
    # avoid a circular import: dynamic_epistemic imports THIS module at load
    # time) and recurse into ``formula.formula`` there, at the SAME world. ---
    if isinstance(formula, Announce):
        if not satisfies_modal(formula.announcement, model, world):
            return True  # untruthful announcement is not made: vacuously true
        from .dynamic_epistemic import announce  # lazy: avoid import cycle
        return satisfies_modal(formula.formula, announce(model, formula.announcement), world)
    if isinstance(formula, AnnounceDiamond):
        if not satisfies_modal(formula.announcement, model, world):
            return False  # dual of Announce: false whenever the announcement is
        from .dynamic_epistemic import announce  # lazy: avoid import cycle
        return satisfies_modal(formula.formula, announce(model, formula.announcement), world)

    # --- object quantifiers (actualist: range over the CURRENT world's domain D_w) ---
    if isinstance(formula, Quantifier):
        individuals = model.domain_at(world)
        instances = (
            satisfies_modal(substitute(formula.formula, formula.variable, Constant(d)),
                            model, world)
            for d in individuals
        )
        if formula.type in _FORALL:
            return all(instances)
        if formula.type in _EXISTS:
            return any(instances)
        raise ValueError(f"satisfies_modal: unknown quantifier type {formula.type!r}")

    # --- predicate quantifiers: the body in every model that reinterprets the bound
    # predicate (at every world), like ``Down`` reinterprets a nominal. The evaluation of
    # the body is this function's own, so an inner binder of the same name shadows this
    # one and every operator above reads a bound predicate like any other atom. ---
    if isinstance(formula, SecondOrderQuantifier):
        reinterpreted = _predicate_interpretations(formula, model)
        if formula.type in _FORALL:
            return all(satisfies_modal(formula.formula, m, world) for m in reinterpreted)
        if formula.type in _EXISTS:
            return any(satisfies_modal(formula.formula, m, world) for m in reinterpreted)
        raise ValueError(
            f"satisfies_modal: unknown predicate quantifier type {formula.type!r}")

    # NOTE: SortedQuantifier / SortedConstant never reach this dispatch chain --
    # the preamble above relativizes the whole formula before any isinstance
    # check runs, so by this point the tree contains only plain Quantifier /
    # Constant nodes (see the module docstring's "Many-sorted formulas"
    # section for what the guarded-Quantifier reduction does and does not
    # assume: world-relative sort guards, non-emptiness and the membership of a
    # sorted constant left to the caller).

    # Łukasiewicz / lambda nodes were already rejected in the preamble above
    # (deep scan, before relativizing); anything reaching here is a genuinely
    # unhandled node type.
    raise NotImplementedError(
        f"satisfies_modal: unsupported node type {type(formula).__name__}."
    )


def models_at(formula: Node, model: KripkeModel, world: World) -> bool:
    """Convenience alias for :func:`satisfies_modal` reading "model, world ⊨ φ"."""
    return satisfies_modal(formula, model, world)


def sorted_constant_violations(formula: Node,
                               model: KripkeModel) -> List[Tuple[str, str, World]]:
    """The worlds of ``model`` at which a sorted constant of ``formula`` is NOT in its sort.

    ``c:S`` denotes an element of ``S`` and a constant is a rigid designator, so a
    model is LEGAL for ``formula`` only if the guard atom ``S(c)`` is in the
    valuation of every world, for every distinct ``c:S`` of ``formula`` (see the
    module docstring: :func:`satisfies_modal` evaluates one given model and does
    not assert the fact itself). Pass the ORIGINAL formula — ``c:S`` is gone once
    the formula is relativized.

    Returns ``(constant, sort, world)`` triples, one per sorted constant and per
    world whose valuation lacks the key ``S(c)``, constants in first-occurrence
    order and worlds in ``repr`` order; ``[]`` means the model is legal for the
    formula's sorted constants (and trivially so for a formula without any).
    Non-emptiness of a sort is a different fact, left to the caller as before.
    """
    violations: List[Tuple[str, str, World]] = []
    worlds = sorted(model.worlds, key=repr)
    for atom in sort_membership_axioms(formula):
        # every member is the guard atom ``S(c)`` over the one constant ``c``
        assert isinstance(atom, Atom)
        constant = atom.args[0]
        assert isinstance(constant, Constant)
        for world in worlds:
            if find_key(model.atoms_true_at(world), atom) is None:
                violations.append((constant.name, atom.predicate, world))
    return violations


# ---------------------------------------------------------------------------
# CTL (branching-time) model checking: EX / AF / EG / AU
# ---------------------------------------------------------------------------
#
# Next / Always / Eventually / Until (documented above) are LINEAR-time
# operators, each with exactly one path reading baked into its own AST node
# (fol/_modal_nodes.py): Next and Always read universally (every successor /
# every reachable world), Eventually and Until existentially (some reachable
# world / some finite witnessing path). There is no A/E path-quantifier
# prefix anywhere in the AST, so the four functions below are plain
# functions — not new isinstance branches in satisfies_modal's dispatch —
# exactly like common_knowledge_holds / everybody_knows in
# semantics/action_models.py: arbitrary Node subformulas evaluated via
# satisfies_modal, no new AST node type and no grammar/parser change.
#
# - ctl_ex is the existential dual of the built-in (universal) Next: a plain
#   one-step modality, no fixpoint needed.
# - ctl_af/ctl_eg are the missing AF/EG dual pair. Note AF is NOT the same
#   computation as reflexive_transitive_closure: a world can satisfy "phi
#   holds on every path" without phi holding at every REACHABLE world (some
#   paths from it may loop back through phi-free territory before others
#   reach a phi-world), so a genuine forward least-fixpoint is needed, not a
#   closure/reachability walk.
# - ctl_au is the universal-path generalisation of the built-in (existential)
#   Until above.
#
# All three fixpoint functions (AF/EG/AU) quantify over the "temporal"
# relation RESTRICTED to model.worlds: their state space IS model.worlds, so
# an edge into a world outside it cannot be a step of the fixpoint — unlike
# Next/Always/Eventually/Until above, which follow model.successors() /
# model.relation() exactly as given, with no membership filter.
#
# Algorithm (standard CTL labelling via fixpoint iteration on the finite
# temporal relation restricted to model.worlds — Baier & Katoen, Principles of
# Model Checking, MIT Press 2008, §6.4; Clarke, Grumberg & Peled, Model
# Checking, MIT Press 1999, ch. 6): each iteration is monotone on the finite
# set model.worlds, so it reaches a fixpoint in at most |model.worlds| rounds.
# No external library and no Tarjan/SCC machinery is required for correctness
# (SCC detection would only be an internal optimisation, and none is used
# here).

def _ctl_temporal_successors(model: "KripkeModel", world: World) -> Set[World]:
    """Temporal successors of ``world`` that are themselves in ``model.worlds``.

    The CTL fixpoints below (:func:`ctl_af`, :func:`ctl_eg`, :func:`ctl_au`)
    iterate over ``model.worlds`` as their state space, so a temporal edge
    into a world outside it is not a step of any of those fixpoints — unlike
    ``Next``/``Always``/``Eventually``/``Until`` above, which follow
    ``model.successors``/``model.relation`` exactly as given, with no
    membership filter. :func:`ctl_ex` (the one CTL function below that is a
    plain one-step modality, not a path fixpoint) intentionally does NOT use
    this helper — see its own docstring.
    """
    return {w2 for w2 in model.successors(_TEMPORAL, world) if w2 in model.worlds}


def _require_total_temporal(model: "KripkeModel") -> None:
    """Raise ValueError unless every world of ``model.worlds`` has a temporal
    successor inside ``model.worlds``.

    ``ctl_af``/``ctl_eg``/``ctl_au`` quantify over INFINITE ``"temporal"``
    paths. A world with no successor inside ``model.worlds`` is a dead end no
    infinite path can pass through — treating it the way ``Next`` treats a
    dead end (AX-anything vacuously true) would silently make AF/EG/AU wrong
    there, exactly the kind of silent wrongness the kit's "refuse loudly,
    never approximate" rule exists to prevent (the same discipline
    ``product_update`` follows for a missing agent relation in
    ``action_models.py``). So instead of picking a convention, this requires
    the frame to be total on ``model.worlds`` and names the (deterministically
    first, by ``repr()``, so the message is reproducible) offending world.

    ``ctl_ex`` needs no such check — it is a genuine one-step modality, as
    vacuously-decided at a dead end as the existing universal ``Next``, see
    its own docstring.
    """
    dead_ends = sorted(
        (w for w in model.worlds if not _ctl_temporal_successors(model, w)),
        key=repr,
    )
    if dead_ends:
        raise ValueError(
            "ctl_af/ctl_eg/ctl_au: the \"temporal\" relation is not total on "
            f"model.worlds — world {dead_ends[0]!r} has no temporal successor "
            "inside model.worlds, so no infinite path passes through it. Add "
            "a temporal successor within model.worlds (a self-loop is the "
            "usual fix for a terminal/sink state) to make the frame total, "
            "or use ctl_ex there instead, which needs no totality."
        )


def ctl_ex(model: KripkeModel, world: World, formula: Node) -> bool:
    """Return whether EX φ ("some immediate successor satisfies φ") holds at ``world``.

    The existential dual of the kit's built-in ``Next`` (which reads its one
    AST node universally, i.e. AX — see the module docstring). A plain
    one-step modality: no fixpoint, and no totality requirement. Exactly like
    ``Next``, a world with no ``"temporal"``-successor is simply decided by
    the empty case — ``Next``'s empty ``all(...)`` is vacuously TRUE there,
    this function's empty ``any(...)`` is FALSE there — not an error.

    Also follows ``Next``'s convention of reading ``model.successors``
    UNFILTERED: a successor outside ``model.worlds`` is still a witness here
    (exactly as it is for ``Next``), unlike :func:`ctl_af`/:func:`ctl_eg`/
    :func:`ctl_au` below, which restrict to ``model.worlds`` because they run
    a fixpoint over it.

    Raises:
        NotImplementedError: an equality / disequality atom (``=`` / ``≠``)
            anywhere in ``formula`` — refused up front, so a world with no
            successor (where the ``any(...)`` below would never look at
            ``formula``) refuses it too; see the module docstring.
    """
    reject_equality_in(formula, "ctl_ex")
    return any(
        satisfies_modal(formula, model, w2)
        for w2 in model.successors(_TEMPORAL, world)
    )


def ctl_af(model: KripkeModel, world: World, formula: Node) -> bool:
    """Return whether AF φ ("φ eventually holds, on every path") holds at ``world``.

    The least fixpoint μZ. φ ∨ AX Z (Baier & Katoen §6.4), computed by
    forward iteration from Z = ∅: a world enters Z as soon as φ holds there,
    or every one of its ``model.worlds``-internal temporal successors is
    already in Z. Z grows monotonically on the finite set ``model.worlds``,
    so the loop reaches a fixpoint in at most ``|model.worlds|`` rounds.

    Raises:
        NotImplementedError: an equality / disequality atom (``=`` / ``≠``)
            anywhere in ``formula`` — see the module docstring.
        ValueError: the ``"temporal"`` relation is not total on
            ``model.worlds`` — see :func:`_require_total_temporal`. Without
            totality, "every successor of w is in Z" would hold vacuously at
            a dead end and silently pull dead ends into AF's least fixpoint
            for the wrong reason.
    """
    reject_equality_in(formula, "ctl_af")
    _require_total_temporal(model)
    phi_worlds = {w for w in model.worlds if satisfies_modal(formula, model, w)}
    z: Set[World] = set()
    while True:
        new_z = set(phi_worlds)
        for w in model.worlds:
            if w not in new_z and _ctl_temporal_successors(model, w) <= z:
                new_z.add(w)
        if new_z == z:
            return world in z
        z = new_z


def ctl_eg(model: KripkeModel, world: World, formula: Node) -> bool:
    """Return whether EG φ ("φ holds forever, on some path") holds at ``world``.

    The greatest fixpoint νZ. φ ∧ EX Z (Baier & Katoen §6.4), computed by
    shrinking from Z = {w : φ holds at w}: a world leaves Z as soon as NONE
    of its ``model.worlds``-internal temporal successors is still in Z. Z
    shrinks monotonically on the finite set ``model.worlds``, so the loop
    reaches a fixpoint in at most ``|model.worlds|`` rounds.

    Raises:
        ValueError: the ``"temporal"`` relation is not total on
            ``model.worlds`` — see :func:`_require_total_temporal`. This
            batch's deadlock convention requires totality uniformly across
            ``ctl_af``/``ctl_eg``/``ctl_au`` (even though EG's own greatest
            fixpoint would, left alone, correctly drop a dead end out of Z on
            its own on the first iteration): a dead end is a modelling error
            to be reported the same way by all three, not something EG alone
            quietly special-cases while its siblings refuse it.
        NotImplementedError: an equality / disequality atom (``=`` / ``≠``)
            anywhere in ``formula`` — see the module docstring.
    """
    reject_equality_in(formula, "ctl_eg")
    _require_total_temporal(model)
    z = {w for w in model.worlds if satisfies_modal(formula, model, w)}
    while True:
        new_z = {w for w in z if _ctl_temporal_successors(model, w) & z}
        if new_z == z:
            return world in z
        z = new_z


def ctl_au(model: KripkeModel, world: World, phi: Node, psi: Node) -> bool:
    """Return whether A[φ U ψ] ("φ holds until ψ, on every path") holds at ``world``.

    The universal-path generalisation of the kit's built-in (existential)
    ``Until`` above. The least fixpoint μZ. ψ ∨ (φ ∧ AX Z) (Baier & Katoen
    §6.4), computed by forward iteration from Z = ∅ exactly like
    :func:`ctl_af`: a world enters Z as soon as ψ holds there, or φ holds
    there AND every one of its ``model.worlds``-internal temporal successors
    is already in Z.

    Raises:
        NotImplementedError: an equality / disequality atom (``=`` / ``≠``)
            anywhere in ``phi`` or ``psi`` — see the module docstring.
        ValueError: the ``"temporal"`` relation is not total on
            ``model.worlds`` — see :func:`_require_total_temporal`.
    """
    reject_equality_in(phi, "ctl_au")
    reject_equality_in(psi, "ctl_au")
    _require_total_temporal(model)
    phi_worlds = {w for w in model.worlds if satisfies_modal(phi, model, w)}
    psi_worlds = {w for w in model.worlds if satisfies_modal(psi, model, w)}
    z: Set[World] = set()
    while True:
        new_z = set(psi_worlds)
        for w in model.worlds:
            if (w not in new_z and w in phi_worlds
                    and _ctl_temporal_successors(model, w) <= z):
                new_z.add(w)
        if new_z == z:
            return world in z
        z = new_z
