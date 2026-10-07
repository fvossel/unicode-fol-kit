"""Minimal models via ASP — clingo enumerates, the kit's own filter decides.

:func:`nonmonotonic.minimal_models <unicode_logic_kit.semantics.nonmonotonic.minimal_models>`
answers "which finite models are ≤-minimal" by brute force: enumerate every
interpretation of the signature over a domain, keep the ones that satisfy the
premises, then compare every survivor against every other survivor in its
fixed-part group. That comparison step is correct but the enumeration step is
not what an ASP solver is for — clingo already ships a search procedure that
prunes as it grounds instead of generating every candidate and checking it
afterward. This module keeps the (already correct, unmodified) comparison and
replaces only the enumeration: :func:`asp_minimal_models` grounds ``premises``
into an ASP program whose answer sets are *exactly* the models of a given
domain size, lets clingo enumerate those, and then hands the result to
nonmonotonic's own ``_circ_profile`` / ``_strictly_below`` / ``_fixed_key`` —
imported, not reimplemented — to pick out the minimal ones.

Why reuse rather than reimplement the filter
---------------------------------------------
A second, independently-written "is this model minimal" check would need to
agree with the first one for this module to be trustworthy, and disagreement
between two independent implementations of the same non-trivial comparison
(componentwise subset-or-equal with at least one strict subset, grouped by a
shared fixed part) is exactly the kind of bug this kit's differential-testing
discipline exists to catch — better to make it structurally impossible by
sharing the code. Importing the private ``_circ_profile`` / ``_strictly_below``
/ ``_fixed_key`` from :mod:`~unicode_logic_kit.semantics.nonmonotonic` (that
module is not modified here) means the two routes can only ever disagree about
*which models exist* (an enumeration bug), never about *which of them are
minimal* (a comparison bug) — the second class of disagreement is ruled out
by construction, not merely tested for.

Why not ``#minimize`` over the circumscribed predicates
----------------------------------------------------------
clingo's own optimisation directive would find the models with the fewest
TRUE atoms among the circumscribed predicates — CARDINALITY-minimal models.
Circumscription wants SUBSET-minimal models: ``{a}`` is more minimal than
``{a, b}`` even though both have "few" elements, and a set with 3 elements
distributed one way is not comparable by cardinality alone to a different
3-element set. The two orders coincide only when every minimal set has the
same size, which is not true in general (see the disjunctive-fact example in
this module's own verification below: ``P(a) ∨ P(b)`` has minimal models
``{a}`` and ``{b}``, both size 1, but a formula like ``P(a) ∨ (P(b) ∧ P(c))``
already breaks the coincidence). Substituting cardinality-minimality for
subset-minimality would be exactly the silent semantic swap this kit's other
non-monotonic-reasoning code refuses to make elsewhere, so it is refused here
too: this module enumerates ALL models and filters in Python with the real
predicate, never ``#minimize``.

``size`` is a single domain size, not a bound
------------------------------------------------
:func:`nonmonotonic.minimal_models <unicode_logic_kit.semantics.nonmonotonic.minimal_models>`
takes ``max_size`` and unions the minimal models found at every size from 1 up
to that bound (models at different sizes are never compared against each
other — see that function's own docstring). :func:`asp_minimal_models` here
takes a single ``size`` and grounds exactly once, at that size, because
grounding is the expensive step an ASP solver does per call and silently
regrounding ``size`` times to imitate ``max_size`` would hide that cost from
the caller. A caller who wants the union-over-sizes behaviour gets it by
calling this function in a loop and concatenating the results — one line at
the call site, versus a hidden cost inside every call otherwise. This is a
genuine, deliberate difference from ``minimal_models``'s parameter of a
similar name; the verification below accounts for it by comparing against
``minimal_models(..., max_size=size)`` FILTERED to the structures whose own
domain has exactly ``size`` elements, which — because sizes are never compared
across each other in that function either — is provably the same set a
hypothetical single-size ``minimal_models`` would have returned.

The ASP encoding
-------------------
For a fixed domain size ``n``, ``dom(0..n-1).`` names the individuals; every
declared predicate, function, and constant gets a free ASP choice (a function
of arity ``k`` as the standard *total relation*: ``1 { f(x̄, v) : dom(v) } 1``
per input tuple ``x̄``, which enforces functionality — at most one result —
and totality — at least one — in the same rule the way
:mod:`~unicode_logic_kit.atp.finite_domain`'s design note also describes it).
Each (sub)formula then gets its own auxiliary ASP atom, defined by rules that
mirror its connective: ``And`` needs one rule (a conjunction of positive
literals is what a rule body already is), ``Or``/``Xor``/``Implies``/``Iff``
need two rules each (one for each way to satisfy them — plain multi-rule
disjunction, no aggregate), ``Not`` is default negation over its
already-fully-defined child (safe precisely because the child's rules are
grounded, and hence decided, for every combination of its free variables
before the parent ever refers to it — the formula tree is a DAG with no
cycles through negation, so this is ordinary stratified Datalog negation, not
anything exotic). ``∃x φ`` is a projection: a rule whose body mentions ``x``
but whose head does not, so grounding produces "true for some x" for free —
no aggregate needed. ``∀x φ`` is rewritten to ``¬∃x ¬φ`` before encoding
rather than given its own bespoke aggregate rule, so its correctness rides on
the already-tested ``Not``/``∃`` encodings instead of a third, separately-
fallible implementation of the same quantifier alternation. ``Count`` (the
one place real counting is needed) is the one aggregate this module emits:
``#count{x : dom(x), φ(x)} <op> n``. Symbol names in the generated program
are never the FOL names themselves (``p0``, ``f0``, ``k0``, …, assigned by a
signature scan) — sidestepping both ASP's stricter identifier syntax
(FOL names may contain non-ASCII letters this kit deliberately allows
elsewhere) and any namespace collision between a predicate and a same-spelled
constant, which a flat ASP atom namespace would otherwise conflate.

Fragment supported here (deliberately narrower than
:func:`~unicode_logic_kit.atp.finite_domain.fragment_check`'s)
------------------------------------------------------------------
``Atom``, ``Not``, ``And``, ``Or``, ``Xor``, ``Implies``, ``Iff``,
``Quantifier`` (unsorted ``∀``/``∃`` only), ``Count``, over
``Variable``/``Constant``/``Number``/``Function`` terms — exactly the
fragment :mod:`~unicode_logic_kit.semantics.tarski` (via
:mod:`~unicode_logic_kit.semantics.modelfinder`) evaluates, because that
evaluator is this module's own verification oracle below: supporting a
construct here that the oracle cannot check would mean shipping an
un-cross-checked code path, which is what this whole module exists to avoid.
Two constructs :func:`~unicode_logic_kit.atp.finite_domain.fragment_check` DOES
admit are refused here for exactly that reason: ``Cardinality`` (the oracle's
:func:`~unicode_logic_kit.semantics.tarski.term_value` can evaluate it as a
term, but only inside an equality/order comparison whose VALUE is an
arithmetic integer, not a domain individual — plumbing that through this
module's term encoding, which only ever produces domain-individual variables,
is a distinct unit of work with its own risk of a subtly wrong aggregate,
and it is not needed for circumscription premises, which reason about
predicate extensions, not counts) and ``Contrast`` (the oracle does not
evaluate it at all — :func:`~unicode_logic_kit.semantics.tarski.satisfies` has
no case for it — so there is no oracle to verify against even if this module
encoded it). A sentence outside this fragment raises ``ValueError`` naming
the offending node type rather than silently mis-encoding it.

Public API: :func:`asp_minimal_models`, :func:`asp_find_model`.
"""

from itertools import product
from typing import Any, Dict, Iterable, List, Optional, Set, Tuple

from ..fol.nodes import (
    Node, Variable, Constant, Number, Function,
    Atom, Not, And, Or, Xor, Implies, Iff, Quantifier, Count,
    SecondOrderQuantifier,
)
from ..fol._fol_nodes import numeral_key
from ..fol._truth_constants import truth_value as _truth_value
from .tarski import Structure, _FORALL, _EXISTS, _ORDER_COMPARISONS, _ORDER_OPS, _is_number
from ..fol._free_parameters import parameterize
from .modelfinder import _Signature
from .nonmonotonic import _circ_profile, _strictly_below, _fixed_key

__all__ = ["asp_minimal_models", "asp_find_model", "asp_holds_so"]


# =============================================================================
# Fragment gate — see the module docstring's "Fragment supported here" section
# for what is admitted and, for the two admitted-elsewhere-but-not-here node
# types, exactly why.
# =============================================================================

_ALLOWED_FORMULA_TYPES = (Atom, Not, And, Or, Xor, Implies, Iff, Quantifier, Count)
_ALLOWED_TERM_TYPES = (Variable, Constant, Number, Function)


def _silent(code, message):
    """clingo logger that drops its info/warning chatter about the GENERATED program
    (e.g. "atom does not occur in any rule head" for an empty extension), the same
    choice atp.clingo_backend makes; real errors still raise from clingo itself."""


def _check_fragment(sentences: Iterable[Node]) -> None:
    """Raise ``ValueError`` at the first node outside this module's fragment.

    Walks every sentence pre-order (so a disallowed node nested inside an
    allowed one is still caught) and additionally rejects a ``Quantifier``
    whose ``type`` is neither an unsorted ``∀``/``forall`` nor an unsorted
    ``∃``/``exists`` spelling — the only two this module's encoder
    recognises (the same spellings :mod:`~unicode_logic_kit.semantics.tarski`
    recognises, imported from there rather than re-listed here so the two
    can never drift apart).

    Raises:
        ValueError: naming the first offending node type (or quantifier
            spelling) encountered, and — for a well-known excluded
            construct (``Cardinality``, ``Contrast``, the sorted family,
            …) — why it is excluded (see the module docstring).
    """
    for sentence in sentences:
        for node in sentence.walk():
            if isinstance(node, _ALLOWED_FORMULA_TYPES) or isinstance(node, _ALLOWED_TERM_TYPES):
                if isinstance(node, Quantifier) and node.type not in _FORALL and node.type not in _EXISTS:
                    raise ValueError(
                        f"asp_models: unknown quantifier spelling {node.type!r} — "
                        f"only unsorted {_FORALL + _EXISTS} are encodable here."
                    )
                continue
            raise ValueError(
                f"asp_models: {type(node).__name__} is not in the fragment this "
                "module encodes (unsorted classical FOL — Atom/Not/And/Or/Xor/"
                "Implies/Iff/Quantifier/Count over Variable/Constant/Number/"
                "Function terms; see the module docstring's 'Fragment supported "
                "here' section for why Cardinality/Contrast/the sorted and modal "
                "families are excluded)."
            )


# =============================================================================
# The ASP encoder
# =============================================================================

class _AspEncoder:
    """Translates closed FOL sentences into a clingo program, one call at a time.

    Every (sub)formula gets its own fresh auxiliary ASP atom (a Tseitin-style
    encoding — see the module docstring's "The ASP encoding" section for the
    per-connective rule shapes and why each is sound). State kept here is
    purely bookkeeping for that translation: the accumulated rule TEXT, fresh
    name counters, and the FOL-symbol-name -> ASP-identifier maps (so a FOL
    name containing non-ASCII characters, or one that collides with a FOL
    name in a *different* symbol class, never has to become a raw ASP
    identifier — see the module docstring).
    """

    def __init__(self, size: int):
        self.size = size
        self.rules: List[str] = []
        self._var_ctr = 0
        self._head_ctr = 0
        self.pred_asp: Dict[Tuple[str, int], str] = {}
        self.func_asp: Dict[Tuple[str, int], str] = {}
        self.const_asp: Dict[str, str] = {}

    def _fresh_var(self) -> str:
        self._var_ctr += 1
        return f"V{self._var_ctr}"

    def _fresh_head(self) -> str:
        self._head_ctr += 1
        return f"h{self._head_ctr}"

    # -- setup --------------------------------------------------------------

    def declare_signature(self, sig: "_Signature") -> None:
        """Assign a fresh, ASCII, collision-free ASP identifier to every symbol.

        Enumeration order is ``sorted(...)`` of each namespace, so this is
        deterministic given a signature — useful for reading generated
        programs back while debugging, though nothing downstream depends on
        the specific numbering.
        """
        for i, key in enumerate(sorted(sig.predicates)):
            self.pred_asp[key] = f"p{i}"
        for i, key in enumerate(sorted(sig.functions)):
            self.func_asp[key] = f"f{i}"
        for i, name in enumerate(sorted(sig.constants)):
            self.const_asp[name] = f"k{i}"

    def emit_base_facts(self) -> None:
        """Emit ``dom/1`` and the free choice for every declared symbol.

        A predicate of arity ``k`` gets an unconstrained choice over its
        ``domain**k`` possible tuples (arity 0 is a single choice atom, no
        domain conditions needed). A function or constant gets the "total
        relation" choice: for every input tuple (none, for a constant),
        ``1 { … } 1`` picks exactly one result — enforcing functionality
        (at most one) and totality (at least one) in the same rule, the same
        reading :mod:`~unicode_logic_kit.atp.finite_domain`'s design note
        describes for the sibling refutation backends.
        """
        self.rules.append(f"dom(0..{self.size - 1}).")
        for (name, arity), asp in self.pred_asp.items():
            if arity == 0:
                self.rules.append(f"{{{asp}}}.")
            else:
                xs = [f"X{i}" for i in range(arity)]
                conds = ", ".join(f"dom({x})" for x in xs)
                self.rules.append(f"{{{asp}({','.join(xs)}) : {conds}}}.")
        for (name, arity), asp in self.func_asp.items():
            v = "V"
            if arity == 0:
                self.rules.append(f"1 {{ {asp}({v}) : dom({v}) }} 1.")
            else:
                xs = [f"X{i}" for i in range(arity)]
                choice = f"1 {{ {asp}({','.join(xs + [v])}) : dom({v}) }} 1"
                body = ", ".join(f"dom({x})" for x in xs)
                self.rules.append(f"{choice} :- {body}.")
        for name, asp in self.const_asp.items():
            self.rules.append(f"1 {{ {asp}(V) : dom(V) }} 1.")

    def emit_fixed_facts(self, structure: Structure, index_of: Dict[Any, int],
                         free_predicates: Set[Tuple[str, int]]) -> None:
        """Emit ``dom/1``, plus GROUND facts pinning ``structure``'s fixed part.

        Sibling of :meth:`emit_base_facts`, used only by :func:`asp_holds_so`
        (``emit_base_facts`` itself is untouched, so :func:`asp_find_model` /
        :func:`asp_minimal_models` are unaffected). Every declared predicate
        named in ``free_predicates`` — the SO-quantifier-bound ones — gets
        exactly the same free choice rule ``emit_base_facts`` would give it
        (the quantifier itself needs no other encoding: see
        :func:`asp_holds_so`'s docstring). Every OTHER declared symbol
        (predicate, function, constant) is pinned EXACTLY to its
        interpretation in ``structure`` — ground facts, never a choice rule —
        translating ``structure``'s own (arbitrary, hashable) domain
        individuals to the ``0..size-1`` integers ``declare_signature``'s
        numbering assumes elsewhere via ``index_of``.

        One case is not "pin to the declared extension, or else empty": an
        order comparison (``< > ≤ ≥``) that ``structure`` declares NO
        extension for. :func:`~unicode_logic_kit.semantics.tarski._order_value`
        does not read that as empty (always false) — its third, lowest-
        priority reading is that the comparison still holds numerically
        between two operands that themselves evaluate to numbers (see that
        function's own docstring). Pinning such a predicate to the empty
        relation here would silently disagree with the very evaluator
        :func:`asp_holds_so` claims to match once the block's body compares
        two numeric domain individuals with no declared ``<``/etc.
        extension — see :meth:`_order_numeric_extension`, used below exactly
        where ``emit_base_facts`` has no analogous case (a fully free choice
        never needs this fallback).

        Args:
            structure: the structure whose fixed part is pinned.
            index_of: ``{domain individual: 0-based index}`` for every
                individual in ``structure.domain`` (``len(structure.domain)``
                must equal ``self.size``).
            free_predicates: the ``(name, arity)`` pairs to leave as a free
                choice instead of pinning (the SO-quantifier-bound ones).

        Raises:
            ValueError: a constant has no interpretation in ``structure``
                (and does not itself parse as a numeral, mirroring
                :func:`~unicode_logic_kit.semantics.tarski.term_value`'s own
                fallback), a function has no interpretation in ``structure``
                or is not TOTAL over its domain (an argument tuple with no
                value — this encoder's function encoding is the same
                "total relation" reading :func:`emit_base_facts`
                free-chooses, so a partial interpretation does not fit it),
                or a pinned value (from a predicate's declared extension, a
                function's arguments/result, or a constant) is not itself a
                member of ``structure.domain``. A declared PREDICATE with no
                interpretation in ``structure`` never raises here — it
                silently falls through to the empty relation (or, for an
                order comparison, to :meth:`_order_numeric_extension`'s
                numeric reading), the same "missing extension is the empty
                relation, hence false" fallback
                :func:`~unicode_logic_kit.semantics.tarski._atom_value` /
                :func:`~unicode_logic_kit.semantics.tarski._order_value`
                themselves document, not a gap.
        """
        self.rules.append(f"dom(0..{self.size - 1}).")

        for (name, arity), asp in self.pred_asp.items():
            if (name, arity) in free_predicates:
                if arity == 0:
                    self.rules.append(f"{{{asp}}}.")
                else:
                    xs = [f"X{i}" for i in range(arity)]
                    conds = ", ".join(f"dom({x})" for x in xs)
                    self.rules.append(f"{{{asp}({','.join(xs)}) : {conds}}}.")
                continue
            if arity == 0:
                if bool(structure.predicates.get((name, 0), False)):
                    self.rules.append(f"{asp}.")
                continue
            extension = structure.predicates.get((name, arity))
            if extension is None:
                extension = (self._order_numeric_extension(name, structure)
                            if arity == 2 and name in _ORDER_COMPARISONS else ())
            for tup in extension:
                idxs = [self._pin_value(v, index_of, "predicate", name) for v in tup]
                self.rules.append(f"{asp}({','.join(str(i) for i in idxs)}).")

        for (name, arity), asp in self.func_asp.items():
            # Functions are never second-order-bound (SecondOrderQuantifier
            # binds a PREDICATE name only — see the module docstring), so
            # every function declared here is pinned.
            key = (name, arity)
            if key not in structure.functions:
                raise ValueError(
                    f"asp_holds_so: function {name!r}/{arity} has no "
                    "interpretation in the given structure."
                )
            interp = structure.functions[key]
            for args in product(structure.domain, repeat=arity):
                if callable(interp):
                    value = interp(*args)
                else:
                    if args not in interp:
                        raise ValueError(
                            f"asp_holds_so: function {name!r}/{arity} is not "
                            f"total over the given structure's domain — "
                            f"undefined for arguments {args!r} (this "
                            "encoder's function encoding requires exactly "
                            "one result per input tuple, the same 'total "
                            "relation' reading emit_base_facts free-chooses)."
                        )
                    value = interp[args]
                idxs = [self._pin_value(a, index_of, "function", name) for a in args]
                idxs.append(self._pin_value(value, index_of, "function", name))
                self.rules.append(f"{asp}({','.join(str(i) for i in idxs)}).")

        for name, asp in self.const_asp.items():
            # Constants are never second-order-bound either.
            if name in structure.constants:
                value = structure.constants[name]
            else:
                # No override -- mirror tarski.term_value's own Number
                # fallback (a Number is scanned as a constant named by its
                # value, read as the literal itself unless overridden;
                # see modelfinder._Signature.scan / this module's own _term).
                try:
                    value = int(name)
                except ValueError:
                    raise ValueError(
                        f"asp_holds_so: constant {name!r} has no "
                        "interpretation in the given structure."
                    )
            idx = self._pin_value(value, index_of, "constant", name)
            self.rules.append(f"{asp}({idx}).")

    def _order_numeric_extension(self, name: str, structure: Structure) -> Set[Tuple[Any, Any]]:
        """The numeric-fallback extension of an order comparison ``structure``
        declares no extension for — mirrors
        :func:`~unicode_logic_kit.semantics.tarski._order_value`'s rule (3).

        Computed directly over ``structure.domain`` rather than over every
        term this encoder's callers might build: every term
        :meth:`emit_fixed_facts` ever pins (a constant, a function result, a
        quantified variable) is already required to be a member of
        ``structure.domain`` (:meth:`_pin_value` raises otherwise), so the
        domain's own individuals are exactly the ``(left, right)`` value
        pairs :func:`~unicode_logic_kit.semantics.tarski._order_value` would
        ever see for this predicate once no declared extension applies. A
        pair where either individual is not a number (:func:`~unicode_logic_kit.semantics.tarski._is_number`,
        which excludes ``bool``) is simply absent from the result — the same
        "anything else is false" fallback ``_order_value`` itself uses, not
        an error: a non-numeric domain is a legitimate case, not a gap.

        Returns:
            The set of ``(x, y)`` pairs of RAW domain individuals (not yet
            translated to ``dom/1`` indices — the caller does that via
            :meth:`_pin_value`, same as for a declared extension) for which
            ``name``'s numeric reading holds.
        """
        op = _ORDER_OPS[name]
        return {
            (x, y)
            for x in structure.domain
            for y in structure.domain
            if _is_number(x) and _is_number(y) and op(x, y)
        }

    def _pin_value(self, value: Any, index_of: Dict[Any, int], kind: str, name: str) -> int:
        """Translate one structure individual to its ``dom/1`` index, or raise."""
        if value not in index_of:
            raise ValueError(
                f"asp_holds_so: the given structure's {kind} {name!r} "
                f"produces the value {value!r}, which is not itself a member "
                "of the structure's own domain."
            )
        return index_of[value]

    # -- term evaluation ------------------------------------------------------

    def _term(self, term: Node, var_of: Dict[str, str], body: List[str]) -> str:
        """Return the ASP variable naming ``term``'s value, extending ``body``.

        A term is not a single ASP value the way it is a single Python value
        under :func:`~unicode_logic_kit.semantics.tarski.term_value` — every
        constant/function application here is itself a RELATION (the total-
        relation encoding), so evaluating a term means walking it and
        emitting one join literal per constant/function occurrence, each
        introducing a fresh ASP variable for its result. ``body`` is mutated
        in place (appended to) rather than returned and concatenated by every
        caller, since a term's evaluation is always exactly one ingredient of
        a larger rule body being built up alongside it.
        """
        if isinstance(term, Variable):
            if term.name not in var_of:
                raise ValueError(
                    f"asp_models: variable {term.name!r} is not bound by any "
                    "enclosing quantifier — a free variable must have been "
                    "replaced by a parameter constant (see _closed_sentences) "
                    "before encoding."
                )
            return var_of[term.name]
        if isinstance(term, Constant):
            v = self._fresh_var()
            body.append(f"{self.const_asp[term.name]}({v})")
            return v
        if isinstance(term, Number):
            # Mirrors _Signature.scan exactly: a Number is registered as a
            # constant named by its VALUE (numeral_key: 1 and 1.0 are '1'), NOT
            # pinned to its literal value — see modelfinder._Signature.scan and
            # tarski.term_value. Pinning it to the literal instead would look
            # more natural but would silently diverge from what the oracle this
            # module is verified against actually computes, breaking the one
            # invariant this module exists to protect.
            v = self._fresh_var()
            body.append(f"{self.const_asp[numeral_key(term.value)]}({v})")
            return v
        if isinstance(term, Function):
            arg_vars = [self._term(a, var_of, body) for a in term.args]
            v = self._fresh_var()
            key = (term.name, len(term.args))
            body.append(f"{self.func_asp[key]}({','.join(arg_vars + [v])})")
            return v
        raise ValueError(
            f"asp_models: {type(term).__name__} is not an encodable term "
            "(only Variable/Constant/Number/Function are)."
        )

    # -- formula encoding -----------------------------------------------------

    def encode(self, node: Node, var_of: Dict[str, str]) -> Tuple[str, List[str]]:
        """Emit rules defining ``node``'s truth; return ``(reference, free_names)``.

        ``reference`` is the ASP literal text a PARENT rule uses to mention
        this node's truth value (a bare head name if ``node`` is closed, or
        ``head(V1,…)`` over its free variables' current ASP names otherwise).
        ``free_names`` is the sorted list of ``node``'s free FOL variable
        names. ``var_of`` maps every FOL variable name currently in scope
        (bound by an enclosing quantifier already processed) to the ASP
        variable name standing for it — extended with a FRESH ASP name on
        entering a ``Quantifier``/``Count``, so a shadowed inner binder using
        the same FOL name as an outer one never captures the outer binding
        (mirrors :func:`~unicode_logic_kit.semantics.tarski._extend`'s
        dict-overwrite shadowing semantics, which is exactly as correct here
        as it is there for the same reason: assignment lookup is always the
        innermost binding).

        A ``∀`` quantifier is rewritten to ``¬∃¬`` and re-dispatched through
        this same method rather than given its own encoding — see the module
        docstring's "The ASP encoding" section for why.
        """
        if isinstance(node, Quantifier) and node.type in _FORALL:
            return self.encode(Not(Quantifier("∃", node.variable, Not(node.formula))), var_of)

        free_names = sorted(_free_var_names_local(node))
        head_args = [var_of[n] for n in free_names]
        head = self._fresh_head()
        head_ref = head if not head_args else f"{head}({','.join(head_args)})"
        dom_lits = [f"dom({v})" for v in head_args]

        if isinstance(node, Atom):
            self._encode_atom(node, var_of, head_ref, dom_lits)
        elif isinstance(node, Not):
            inner_ref, _ = self.encode(node.formula, var_of)
            self._rule(head_ref, dom_lits + [f"not {inner_ref}"])
        elif isinstance(node, And):
            l_ref, _ = self.encode(node.left, var_of)
            r_ref, _ = self.encode(node.right, var_of)
            self._rule(head_ref, dom_lits + [l_ref, r_ref])
        elif isinstance(node, Or):
            l_ref, _ = self.encode(node.left, var_of)
            r_ref, _ = self.encode(node.right, var_of)
            self._rule(head_ref, dom_lits + [l_ref])
            self._rule(head_ref, dom_lits + [r_ref])
        elif isinstance(node, Xor):
            l_ref, _ = self.encode(node.left, var_of)
            r_ref, _ = self.encode(node.right, var_of)
            self._rule(head_ref, dom_lits + [l_ref, f"not {r_ref}"])
            self._rule(head_ref, dom_lits + [r_ref, f"not {l_ref}"])
        elif isinstance(node, Implies):
            l_ref, _ = self.encode(node.left, var_of)
            r_ref, _ = self.encode(node.right, var_of)
            self._rule(head_ref, dom_lits + [f"not {l_ref}"])
            self._rule(head_ref, dom_lits + [r_ref])
        elif isinstance(node, Iff):
            l_ref, _ = self.encode(node.left, var_of)
            r_ref, _ = self.encode(node.right, var_of)
            self._rule(head_ref, dom_lits + [l_ref, r_ref])
            self._rule(head_ref, dom_lits + [f"not {l_ref}", f"not {r_ref}"])
        elif isinstance(node, Quantifier):  # node.type in _EXISTS, by elimination
            inner_var = self._fresh_var()
            var_of2 = dict(var_of)
            var_of2[node.variable.name] = inner_var
            inner_ref, _ = self.encode(node.formula, var_of2)
            self._rule(head_ref, dom_lits + [inner_ref])
        elif isinstance(node, Count):
            inner_var = self._fresh_var()
            var_of2 = dict(var_of)
            var_of2[node.variable.name] = inner_var
            inner_ref, _ = self.encode(node.formula, var_of2)
            op = {"ge": ">=", "le": "<=", "eq": "="}[node.op]
            agg = f"#count{{ {inner_var} : dom({inner_var}), {inner_ref} }} {op} {node.n.value}"
            self._rule(head_ref, dom_lits + [agg])
        else:
            raise ValueError(
                f"asp_models: {type(node).__name__} reached the encoder despite "
                "_check_fragment — this is an internal invariant violation, not "
                "a normal unsupported-fragment report."
            )

        return head_ref, free_names

    def _rule(self, head_ref: str, body: List[str]) -> None:
        """Append one ``head :- body`` rule (``body`` is always non-empty here)."""
        self.rules.append(f"{head_ref} :- {', '.join(body)}.")

    def _encode_atom(self, node: Atom, var_of: Dict[str, str], head_ref: str, dom_lits: List[str]) -> None:
        """Emit the rule(s) defining an ``Atom``'s auxiliary head atom.

        ``=``/``≠`` at arity 2 get the built-in identity reading (an ASP
        variable comparison, never a free-choice predicate); every other
        atom — including the order comparisons ``< > ≤ ≥``, which
        :func:`~unicode_logic_kit.semantics.modelfinder._Signature.scan`
        registers as ORDINARY predicates, not built-ins, exactly like
        :func:`~unicode_logic_kit.semantics.tarski._order_value`'s own
        "a declared extension wins" reading — is a free-choice predicate
        lookup, so no special-casing is needed for them here beyond what
        the general branch already does.
        """
        body: List[str] = list(dom_lits)
        constant = _truth_value(node)
        if constant is not None:
            # `$true` holds wherever the head is defined at all, `$false` nowhere: no
            # rule defines the head, so the solver reads it as false.
            if constant:
                if body:
                    self._rule(head_ref, body)
                else:
                    self.rules.append(f"{head_ref}.")
            return
        if node.predicate in ("=", "≠") and len(node.args) == 2:
            a = self._term(node.args[0], var_of, body)
            b = self._term(node.args[1], var_of, body)
            body.append(f"{a}{'=' if node.predicate == '=' else '!='}{b}")
            self._rule(head_ref, body)
            return
        arg_vars = [self._term(a, var_of, body) for a in node.args]
        key = (node.predicate, len(node.args))
        if key not in self.pred_asp:
            raise KeyError(
                f"asp_models: predicate {node.predicate!r}/{len(node.args)} is "
                "not in the scanned signature — internal invariant violation "
                "(every predicate an encoded sentence uses must have been "
                "scanned into the signature first)."
            )
        pred_lit = self.pred_asp[key] if not arg_vars else f"{self.pred_asp[key]}({','.join(arg_vars)})"
        body.append(pred_lit)
        self._rule(head_ref, body)


def _free_var_names_local(node: Node) -> Set[str]:
    """``_free_var_names(node)`` from modelfinder, at the default (empty) bound.

    A thin wrapper purely so every call site above reads as "the free
    variables of this node" without repeating the ``frozenset()`` default
    argument; kept local (not re-exported) since it is a one-line adapter,
    not a new piece of logic.
    """
    from .modelfinder import _free_var_names
    return _free_var_names(node)


# =============================================================================
# Model decoding — clingo's answer set back into modelfinder's own shape
# =============================================================================

def _decode_model(model, enc: "_AspEncoder", sig: "_Signature", size: int
                  ) -> Tuple[Dict[str, int], Dict[Tuple[str, int], dict], Dict[Tuple[str, int], set]]:
    """Turn one clingo answer set into ``(constants, functions, predicates)``.

    The exact shapes :func:`~unicode_logic_kit.semantics.modelfinder._interpretations`
    produces (domain individuals are the plain ints ``0..size-1``, NOT the
    strings :mod:`~unicode_logic_kit.semantics.structures.FiniteStructure` uses)
    — required for byte-identical comparison against
    :func:`~unicode_logic_kit.semantics.nonmonotonic.minimal_models`'s own
    output, and for feeding straight into ``_circ_profile``/``_fixed_key``.

    Raises:
        RuntimeError: a constant's choice rule produced a count of true
            atoms other than 1 in this answer set — the ``1 { … } 1`` choice
            rule :meth:`_AspEncoder.emit_base_facts` emits is supposed to
            make this impossible, so seeing it would mean the generated
            program itself is broken, not that the caller misused anything.
    """
    by_name: Dict[str, list] = {}
    for sym in model.symbols(atoms=True):
        by_name.setdefault(sym.name, []).append(sym)

    constants: Dict[str, int] = {}
    for name, asp in enc.const_asp.items():
        matches = by_name.get(asp, [])
        if len(matches) != 1:
            raise RuntimeError(
                f"asp_models: constant {name!r} ({asp}) has {len(matches)} "
                "true atoms in an answer set, expected exactly 1 — the "
                "'1 { … } 1' choice rule should make this impossible."
            )
        (arg,) = matches[0].arguments
        constants[name] = arg.number

    functions: Dict[Tuple[str, int], dict] = {}
    for (name, arity), asp in enc.func_asp.items():
        table: Dict[Tuple[int, ...], int] = {}
        for sym in by_name.get(asp, []):
            args = tuple(a.number for a in sym.arguments)
            table[args[:-1]] = args[-1]
        functions[(name, arity)] = table

    predicates: Dict[Tuple[str, int], set] = {}
    for (name, arity), asp in enc.pred_asp.items():
        predicates[(name, arity)] = {
            tuple(a.number for a in sym.arguments) for sym in by_name.get(asp, [])
        }

    return constants, functions, predicates


# =============================================================================
# Shared setup: signature scan + program assembly for both public functions
# =============================================================================

def _closed_sentences(premises: Iterable[Node]) -> List[Node]:
    """``premises`` with every free variable read as a PARAMETER of the problem.

    A free variable is one unknown element, the same in every premise: it is replaced,
    in all the premises together, by a constant of its own name
    (:func:`~unicode_logic_kit.fol._free_parameters.parameterize`), so ``P(x), ¬P(y)`` has a
    model (``x`` and ``y`` are two elements) and ``P(x), ¬P(x)`` has none. A premise is
    never closed universally: ``∀x P(x)`` is another premise than ``P(x)``. The structure
    a call returns interprets the parameter like any constant, ``constants['x']``.

    Raises:
        NotImplementedError: a free variable has the spelling of a constant of the
            premises (a structure holds one entry per name).
    """
    sentences, _ = parameterize(list(premises), after_variables=True)
    return sentences


def _build_program(sentences: List[Node], size: int) -> Tuple[str, "_AspEncoder", "_Signature"]:
    """Scan ``sentences`` for their signature and assemble the full ASP program.

    Shared by :func:`asp_find_model` and :func:`asp_minimal_models` — the
    only difference between the two callers is how many answer sets clingo
    is asked for, not how the program is built.

    Raises:
        TypeError: ``size`` is not a plain ``int``, or a member of
            ``sentences`` still has a free variable (an internal invariant —
            see :func:`_closed_sentences`, applied by both public callers
            before this function ever runs).
        ValueError: ``size < 1``, or a sentence uses a construct outside
            this module's fragment (see :func:`_check_fragment`).
    """
    if isinstance(size, bool) or not isinstance(size, int) or size < 1:
        raise ValueError(f"asp_models: size must be an int >= 1, got {size!r}.")
    _check_fragment(sentences)

    sig = _Signature()
    for s in sentences:
        sig.scan(s)

    enc = _AspEncoder(size)
    enc.declare_signature(sig)
    enc.emit_base_facts()
    for s in sentences:
        head_ref, free = enc.encode(s, {})
        if free:
            raise TypeError(
                f"asp_models: sentence {s.to_unicode_str()!r} still has free "
                f"variable(s) {free} after the parameters were substituted — internal "
                "invariant violation."
            )
        enc.rules.append(f":- not {head_ref}.")

    return "\n".join(enc.rules), enc, sig


# =============================================================================
# Public API
# =============================================================================

def asp_find_model(premises: Iterable[Node], size: int = 3) -> Optional[Structure]:
    """Return one finite :class:`~unicode_logic_kit.semantics.tarski.Structure`
    of exactly ``size`` individuals satisfying every one of ``premises``, or
    ``None``.

    The ASP analog of
    :func:`~unicode_logic_kit.semantics.modelfinder.find_model`, but grounded
    at exactly ``size`` rather than searching ``1 … max_size`` — see the
    module docstring's "``size`` is a single domain size, not a bound"
    section; a caller wanting the multi-size search calls this in a loop.

    Args:
        premises: the sentences to satisfy together. A free variable is a
            PARAMETER of the problem, one unknown element shared by every
            premise (:func:`_closed_sentences`), as in
            :func:`~unicode_logic_kit.semantics.modelfinder.find_model`:
            ``P(x), ¬P(y)`` has a model, ``P(x), ¬P(x)`` has none, and the
            returned structure reports the element under the variable's name,
            ``constants['x']``.
        size: the exact domain size to search, ``>= 1``.

    Returns:
        A structure over the domain ``0 … size-1`` satisfying every premise,
        or ``None`` if clingo finds the grounded program unsatisfiable at
        this size (NOT evidence of unsatisfiability at any other size, or of
        first-order unsatisfiability — the same one-sided-boundedness every
        finite-model search in this kit carries).

    Raises:
        ValueError: ``size < 1``, or a premise uses a construct outside this
            module's fragment (see the module docstring).
        NotImplementedError: a free variable has the spelling of a constant of
            the premises.
    """
    import clingo

    sentences = _closed_sentences(premises)
    program, enc, sig = _build_program(sentences, size)

    ctl = clingo.Control(["1"], logger=_silent)
    ctl.add("base", [], program)
    ctl.ground([("base", [])])

    with ctl.solve(yield_=True) as handle:
        for model in handle:
            constants, functions, predicates = _decode_model(model, enc, sig, size)
            return Structure(tuple(range(size)), constants=constants,
                             functions=functions, predicates=predicates)
    return None


def asp_minimal_models(premises: Iterable[Node], circumscribed: Optional[Set[str]] = None,
                       size: int = 3) -> List[Structure]:
    """Return the ≤-minimal finite models of ``premises`` at exactly ``size``.

    clingo enumerates EVERY model of the grounded ``premises`` at this
    domain size (the fragment gate, choice rules and per-connective encoding
    are described in the module docstring); this function then applies
    :mod:`~unicode_logic_kit.semantics.nonmonotonic`'s own, UNMODIFIED
    minimality filter (``_fixed_key`` groups models sharing a domain,
    constants, functions and every non-circumscribed predicate; within each
    group, ``_circ_profile``/``_strictly_below`` keep the ones no other group
    member's circumscribed-predicate extensions are a strict subset of) — the
    exact same filter
    :func:`~unicode_logic_kit.semantics.nonmonotonic.minimal_models` applies to
    its own, brute-force-enumerated candidates. See the module docstring's
    "Why reuse rather than reimplement the filter" section for why sharing
    this code, rather than writing a second copy of the same comparison, is
    what makes this function's answer trustworthy.

    Args:
        premises: the sentences every returned model satisfies. A free
            variable is a PARAMETER, one constant of its own name shared by
            every premise (:func:`_closed_sentences`), exactly as
            :func:`~unicode_logic_kit.semantics.nonmonotonic.minimal_models`
            reads it; the parameter belongs to the fixed part two models must
            share to be compared.
        circumscribed: the predicate NAMES to minimise (arity is whatever the
            premises use it at). ``None`` (the default) minimises every
            predicate the premises mention — the same default
            :func:`~unicode_logic_kit.semantics.nonmonotonic.minimal_models`
            uses, and the same "bare name, not a ``(name, arity)`` pair"
            convention (unlike
            :func:`~unicode_logic_kit.semantics.nonmonotonic.circumscription_formula`'s
            ``CircSpec``, which additionally accepts explicit arities — not
            needed here since every predicate this function can minimise
            was, by construction, already found by scanning ``premises``).
        size: the exact domain size to search, ``>= 1`` — see the module
            docstring's "``size`` is a single domain size, not a bound"
            section for how this differs from ``minimal_models``'s
            ``max_size``.

    Returns:
        Every ≤-minimal structure (see
        :func:`~unicode_logic_kit.semantics.nonmonotonic.minimal_models`'s own
        docstring for the exact ``≤`` relation) over the domain
        ``0 … size-1`` that satisfies every premise. Empty if no model
        exists at this size at all.

    Raises:
        ValueError: ``size < 1``, or a premise uses a construct outside this
            module's fragment (see the module docstring).
        NotImplementedError: a free variable has the spelling of a constant of
            the premises.
    """
    import clingo

    sentences = _closed_sentences(premises)
    program, enc, sig = _build_program(sentences, size)

    pred_sig = sorted(sig.predicates)
    circ = set(circumscribed) if circumscribed is not None else {n for n, _ in pred_sig}

    ctl = clingo.Control(["0"], logger=_silent)
    ctl.add("base", [], program)
    ctl.ground([("base", [])])

    found = []
    with ctl.solve(yield_=True) as handle:
        for model in handle:
            constants, functions, predicates = _decode_model(model, enc, sig, size)
            structure = Structure(tuple(range(size)), constants=constants,
                                  functions=functions, predicates=predicates)
            found.append((constants, functions, predicates, structure))

    # Group by fixed part (domain + constants + functions + non-circumscribed
    # predicate extensions); within each group keep only the models no other
    # member's circumscribed-predicate profile is strictly below — verbatim
    # the same grouping loop
    # :func:`~unicode_logic_kit.semantics.nonmonotonic.minimal_models` runs over
    # its OWN (brute-force-enumerated) `found`, so the two functions can only
    # ever disagree about which models were found, never about which of them
    # count as minimal.
    groups: Dict[tuple, list] = {}
    for entry in found:
        constants, functions, predicates, _ = entry
        key = _fixed_key(constants, functions, predicates, pred_sig, circ)
        profile = _circ_profile(predicates, pred_sig, circ)
        groups.setdefault(key, []).append((entry, profile))

    result: List[Structure] = []
    for grp in groups.values():
        for (entry, profile) in grp:
            if not any(_strictly_below(other, profile) for (e2, other) in grp if e2 is not entry):
                result.append(entry[3])
    return result


# =============================================================================
# Single-block second-order checking (roadmap C24): asp_holds_so
# =============================================================================
#
# secondorder.satisfies_so evaluates ∀P/∃P by brute-force enumeration of every
# relation of P's arity — 2 ** (n ** k), doubly exponential (see that module's
# docstring). The exact mechanism this module already uses for an ORDINARY
# predicate — "a free ASP choice, propagation-pruned by clingo instead of
# materialised in Python" (module docstring, "The ASP encoding") — applies
# just as well to a SECOND-ORDER-BOUND predicate, PROVIDED the quantifier
# nesting is simple enough that "propagation-pruned choice + one solve" is a
# SOUND reduction: a single leading block of SAME-polarity SecondOrderQuantifier
# occurrences (∃P1…∃Pk or ∀P1…∀Pk, nothing else of that kind anywhere in the
# sentence). One ∃-block is an ordinary satisfiability check (NP-flavoured,
# exactly what clingo solves). One ∀-block reduces to a single
# UNSAT-of-the-negation check (co-NP-flavoured — ask whether any answer set
# witnesses the negation; none existing means the block holds for every
# choice). Genuine ALTERNATION (∀P∃Q…) is a strictly harder complexity class
# (Σ2p/Π2p) that plain, non-disjunctive clingo choice rules do not capture
# soundly — see secondorder.py's own module docstring and roadmap C24's
# existing_coverage for the argument — so it is refused here, loudly, rather
# than silently mishandled.

def _so_quantifier_chain(sentence: Node) -> Tuple[Optional[str], List[SecondOrderQuantifier]]:
    """Validate ``sentence``'s SecondOrderQuantifier occurrences; return its block.

    Returns ``(None, [])`` if ``sentence`` has no SecondOrderQuantifier at all
    (a purely classical sentence — :func:`asp_holds_so` accepts this as the
    degenerate zero-quantifier case). Otherwise returns ``("forall" | "exists",
    chain)``, ``chain`` being the block's nodes in outer-to-inner order.

    "A single block" means every SecondOrderQuantifier occurrence in
    ``sentence`` — wherever it sits in the tree, including nested inside
    ordinary classical structure such as
    :func:`~unicode_logic_kit.semantics.nonmonotonic.circumscription_entails_so`'s
    ``Implies``/``And`` — is reachable from exactly ONE entry node by
    following ``.formula`` through SecondOrderQuantifier nodes ONLY, all of
    the SAME polarity, until reaching a body with no further
    SecondOrderQuantifier anywhere inside it. A second, unrelated occurrence
    (a sibling block, or one merely nested a connective away rather than
    directly wrapping the next) is rejected exactly like true alternation —
    both are outside the fragment :func:`asp_holds_so` soundly covers.

    Raises:
        ValueError: mixed ``∀``/``∃`` polarities, an unrecognised quantifier
            spelling, more than one entry point (disconnected or
            connective-separated occurrences), or a SecondOrderQuantifier
            nested inside the block's own innermost body — naming the
            offending sentence in every case.
    """
    all_so = [n for n in sentence.walk() if isinstance(n, SecondOrderQuantifier)]
    if not all_so:
        return None, []

    types = {n.type for n in all_so}
    forall_seen = types & set(_FORALL)
    exists_seen = types & set(_EXISTS)
    unknown = types - forall_seen - exists_seen
    if unknown:
        raise ValueError(
            f"asp_holds_so: unknown SecondOrderQuantifier type(s) {sorted(unknown)!r} "
            f"in {sentence.to_unicode_str()!r} — only unsorted "
            f"{_FORALL + _EXISTS} are supported here."
        )
    if forall_seen and exists_seen:
        raise ValueError(
            f"asp_holds_so: {sentence.to_unicode_str()!r} mixes ∀ and ∃ "
            "second-order quantifiers (alternation) — only a single leading "
            "block of the SAME polarity is supported here; use "
            "secondorder.satisfies_so for alternating second-order "
            "quantification."
        )
    block_type = "forall" if forall_seen else "exists"

    bodies_that_are_so = {
        id(n.formula) for n in all_so if isinstance(n.formula, SecondOrderQuantifier)
    }
    entry_points = [n for n in all_so if id(n) not in bodies_that_are_so]
    if len(entry_points) != 1:
        raise ValueError(
            f"asp_holds_so: {sentence.to_unicode_str()!r} has "
            f"{len(entry_points)} separate second-order-quantifier chains "
            "(nested through a non-quantifier connective, or genuinely "
            "scattered) — only a single leading block, with nothing else of "
            "its kind anywhere in the sentence, is supported here; use "
            "secondorder.satisfies_so instead."
        )

    chain: List[SecondOrderQuantifier] = []
    cur: Node = entry_points[0]
    while isinstance(cur, SecondOrderQuantifier):
        chain.append(cur)
        cur = cur.formula

    if any(isinstance(n, SecondOrderQuantifier) for n in cur.walk()):
        raise ValueError(
            f"asp_holds_so: a SecondOrderQuantifier is nested inside the "
            f"single block's own body in {sentence.to_unicode_str()!r} "
            "(quantifier alternation) — use secondorder.satisfies_so instead."
        )
    if len(chain) != len(all_so):
        raise ValueError(  # pragma: no cover - defensive; unreachable given the checks above
            f"asp_holds_so: the second-order quantifiers in "
            f"{sentence.to_unicode_str()!r} do not form a single connected "
            "chain — use secondorder.satisfies_so instead."
        )
    return block_type, chain


def _replace_so_block(node: Node, entry: SecondOrderQuantifier, replacement: Node) -> Node:
    """Rebuild ``node``, replacing the ONE occurrence ``entry`` (by identity) with ``replacement``.

    ``entry`` is found by object identity (``is``), not structural equality —
    the single node :func:`_so_quantifier_chain` identified as the block's
    entry point, wherever it sits in ``node``. Used to splice the block's own
    (already-computed) truth value back into the surrounding classical
    sentence — see :func:`asp_holds_so`.
    """
    if node is entry:
        return replacement
    return node.map_children(lambda c: _replace_so_block(c, entry, replacement))


def asp_holds_so(sentence: Node, structure: Structure) -> bool:
    """Whether ``structure`` satisfies second-order ``sentence`` (ASP-grounded).

    Mirrors :func:`~unicode_logic_kit.semantics.secondorder.holds`'s signature,
    and — on the fragment described below — its exact answer (verified
    differentially against ``secondorder.satisfies_so``/``holds`` in this
    module's test suite; see roadmap C24). Restricted to sentences whose
    :class:`~unicode_logic_kit.fol.nodes.SecondOrderQuantifier` occurrences form
    a SINGLE, contiguous, SAME-polarity block — see
    :func:`_so_quantifier_chain` for exactly what that means (the block need
    not be at ``sentence``'s outermost node: see
    :func:`~unicode_logic_kit.semantics.nonmonotonic.circumscription_entails_so`'s
    output, whose ``∀``-block sits inside an ``Implies``/``And``). A sentence
    with NO second-order quantifier at all is accepted too, checked as an
    ordinary closed classical formula against ``structure``.

    THE ENCODING is a TWO-STEP evaluation, not a single whole-sentence ASP
    solve — a single solve over the WHOLE sentence with the block's wrapper
    merely stripped is UNSOUND once the block sits in a position where sign
    matters (e.g. the ANTECEDENT of an ``Implies``, as
    ``circumscription_entails_so``'s own output does): negating the whole
    stripped sentence to test the ``∀`` case conflates the block's own
    polarity with the surrounding connective's, silently turning a nested
    ``∀`` into something that answers like an ``∃`` (caught by this module's
    own differential tests against ``satisfies_so`` — a hand-checked
    ``Implies(∀P(P(a)→Q(a)), Q(a))`` example disagreed before this two-step
    design). Instead:

    1. The block's OWN truth value is computed in ISOLATION: its innermost
       body (``chain[-1].formula`` — the part with no further
       ``SecondOrderQuantifier``) is ASP-encoded on its own — the SO-bound
       predicate name(s) get the ordinary free ASP choice any OTHER declared
       predicate gets (no per-node quantifier encoding is needed; see the
       module docstring's "The ASP encoding"), and every other symbol this
       body uses is PINNED to ``structure``'s own extension
       (:meth:`_AspEncoder.emit_fixed_facts`). One clingo solve then asks:
       for a ``∃``-block, is the body true in SOME answer set (SAT, ``:- not
       head.``); for a ``∀``-block, is the body's NEGATION true in NO answer
       set (UNSAT). This is exactly ``asp_find_model``'s own SAT-checking
       shape, just scoped to the block's body and a partly-pinned rather than
       fully-free signature.
    2. That single Boolean is spliced back into ``sentence`` in place of the
       block (:func:`_replace_so_block`, by object identity) as a fresh
       nullary atom whose extension in an EXTENDED copy of ``structure`` is
       exactly that Boolean, and the RESULT — an ordinary classical sentence,
       since the block is now just a 0-ary atom — is handed to
       :func:`~unicode_logic_kit.semantics.tarski.satisfies`, the real
       recursive Tarskian evaluator, which threads the surrounding
       ``Implies``/``And``/``Not``/… polarity correctly because it is not
       re-derived here, just reused.

    The block's own body may not have any free object variable — genuinely
    free in ``sentence`` (which must be closed) or bound by an object-level
    quantifier OUTSIDE the block — since step 1 evaluates it as a
    self-contained closed sentence; see the ``Raises`` section.

    Requires ``structure``'s functions the block's body uses to be
    interpreted TOTALLY over its own domain, matching this module's own
    "total relation" function encoding; see
    :meth:`_AspEncoder.emit_fixed_facts`.

    Args:
        sentence: a closed (no free object variable) second-order sentence,
            single-block as above; the block's own body must, once isolated,
            be within :func:`_check_fragment`'s classical fragment
            (``Atom``/``Not``/``And``/``Or``/``Xor``/``Implies``/``Iff``/
            ``Quantifier``/``Count`` over
            ``Variable``/``Constant``/``Number``/``Function`` terms; see the
            module docstring's "Fragment supported here" section) — the
            surrounding classical structure the block sits inside, if any,
            is evaluated by the FULL Tarskian evaluator instead (step 2
            above), so it is not limited to this narrower fragment.
        structure: the structure to check ``sentence`` against — an
            arbitrary :class:`~unicode_logic_kit.semantics.tarski.Structure`
            (any hashable domain, not necessarily the ``0..n-1`` integers
            :func:`asp_find_model`/:func:`asp_minimal_models` produce; this
            function builds its own index for the ASP encoding).

    Returns:
        Whether ``structure`` satisfies ``sentence``.

    Raises:
        ValueError: the SecondOrderQuantifier occurrences in ``sentence`` do
            not form a single same-polarity block (alternation, nesting,
            mixed polarity, or more than one chain — naming the offending
            sentence); the block's own body uses a construct outside
            :func:`_check_fragment`'s fragment, or has a free object variable
            (genuinely free in ``sentence``, or bound outside the block —
            either way, out of scope for the isolated per-block solve above);
            or a constant or function the block's body needs from
            ``structure`` has no interpretation there, a pinned value is not
            itself a member of ``structure``'s domain, or a function is not
            total over it — a declared PREDICATE with no interpretation
            never raises (see :meth:`_AspEncoder.emit_fixed_facts`'s own
            ``Raises``).
        ImportError: ``clingo`` (the optional ``asp`` extra) is not
            installed — never a silent fallback to the brute-force evaluator.
    """
    import clingo
    from .tarski import satisfies
    from ..atp.sequent import _all_pred_names, _fresh_pred_name

    block_type, chain = _so_quantifier_chain(sentence)

    if not chain:
        return satisfies(sentence, structure, {})

    entry = chain[0]
    body = chain[-1].formula
    _check_fragment([body])

    free_vars = _free_var_names_local(body)
    if free_vars:
        raise ValueError(
            f"asp_holds_so: the second-order block in {sentence.to_unicode_str()!r} "
            f"has free object variable(s) {sorted(free_vars)} in its own body "
            "— either genuinely free in `sentence` (which must be closed) or "
            "bound by an object-level quantifier OUTSIDE the block, neither "
            "of which this function's isolated per-block solve supports; use "
            "secondorder.satisfies_so instead."
        )

    so_names = {(n.predicate, n.arity) for n in chain}

    sig = _Signature()
    sig.scan(body)
    sig.predicates |= so_names  # a vacuously-quantified SO predicate still needs a choice

    index_of: Dict[Any, int] = {d: i for i, d in enumerate(structure.domain)}
    size = len(structure.domain)

    enc = _AspEncoder(size)
    enc.declare_signature(sig)
    enc.emit_fixed_facts(structure, index_of, so_names)

    target: Node = Not(body) if block_type == "forall" else body
    head_ref, _free = enc.encode(target, {})
    enc.rules.append(f":- not {head_ref}.")
    program = "\n".join(enc.rules)

    ctl = clingo.Control(["1"], logger=_silent)
    ctl.add("base", [], program)
    ctl.ground([("base", [])])

    found = False
    with ctl.solve(yield_=True) as handle:
        for _model in handle:
            found = True
            break

    block_value = (not found) if block_type == "forall" else found

    if entry is sentence:
        return block_value

    fresh_name = _fresh_pred_name("_so_block", _all_pred_names(sentence))
    substituted = _replace_so_block(sentence, entry, Atom(fresh_name, ()))
    ext_predicates = dict(structure.predicates)
    ext_predicates[(fresh_name, 0)] = block_value
    ext_structure = Structure(structure.domain, constants=structure.constants,
                              functions=structure.functions, predicates=ext_predicates,
                              sorts=structure.sorts)
    return satisfies(substituted, ext_structure, {})
