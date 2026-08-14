"""Tests for the ASP route to minimal models (semantics/asp_models.py).

Three properties matter here, and each gets its own section below:

1. **Differential agreement with** :func:`nonmonotonic.minimal_models
   <unicode_fol_kit.semantics.nonmonotonic.minimal_models>` — clingo's
   enumeration and the brute-force one must return the *same set* of minimal
   models on a shared premise set. ``minimal_models`` unions results across
   every domain size up to ``max_size`` (see its own docstring), while
   ``asp_minimal_models`` grounds at exactly one ``size``; the two are made
   comparable by filtering ``minimal_models``'s output down to the structures
   whose domain has exactly that size (valid because ``minimal_models`` never
   compares models across different domain sizes — see
   ``asp_models``'s "``size`` is a single domain size, not a bound" docstring
   section). Comparison is by a canonical, individual-labelling-stable key —
   both routes draw candidates from the identical domain representation
   (``tuple(range(size))``), so this is a same-population comparison, not an
   up-to-isomorphism one.
2. **Circumscription targets the NAMED predicate(s), not every predicate the
   premises mention.** A predicate left out of ``circumscribed`` is *fixed*
   (compared, not minimised) — its asserted value survives in every minimal
   model, and different-but-consistent values of it produce genuinely
   different (all retained) minimal models, rather than being collapsed to
   the smallest one the way a circumscribed predicate would be.
3. **Subset-minimality, not cardinality-minimality.** The module's own
   docstring names the risk directly: ``#minimize`` would keep only the
   models with the fewest true atoms among the circumscribed predicates, and
   that is a different (and wrong, for circumscription) order whenever a
   subset-incomparable pair has different sizes. ``P(a) ∨ (P(b) ∧ P(c))``
   with ``a, b, c`` pairwise distinct is exactly such a pair: ``P = {a}``
   (size 1) and ``P = {b, c}`` (size 2) are both subset-minimal (neither is a
   subset of the other, and neither can shrink further without breaking the
   disjunction), but a cardinality filter would keep only the size-1 answer.
   The test below pins that a size-2 extension is genuinely present in the
   output — the concrete, falsifiable difference between the two orders.

Every expected model set below was reasoned out by hand *before* running
either oracle (see the comment above each case), then cross-checked against
both :func:`asp_minimal_models` and :func:`minimal_models` — a
scratch-verification run (not committed) reproduced every count and
structure asserted here.
"""

from unicode_fol_kit.fol._fol_nodes import (
    Atom, And, Or, Not, Implies, Quantifier, Variable, Constant, Cardinality, Contrast,
)
from unicode_fol_kit.semantics.nonmonotonic import minimal_models
from unicode_fol_kit.semantics.asp_models import asp_minimal_models, asp_find_model
from unicode_fol_kit.semantics.tarski import Structure

A, B, C = Constant("a"), Constant("b"), Constant("c")
X = Variable("x")


def _canon(structure: Structure, pred_sig) -> tuple:
    """A hashable, order-independent fingerprint of ``structure`` over ``pred_sig``.

    Both :func:`asp_minimal_models` and ``minimal_models`` draw their
    candidates from the identical domain representation (``tuple(range(n))``
    individuals — see the module docstring), so structures from the two
    routes are directly comparable by value: no isomorphism search is
    needed, just turning each mutable dict/set into a hashable tuple so two
    structures with the same content compare equal regardless of which
    dict-iteration order produced them.
    """
    consts = tuple(sorted(structure.constants.items()))
    preds = tuple(sorted(
        (name, ar, frozenset(structure.predicates.get((name, ar), frozenset())))
        for (name, ar) in pred_sig
    ))
    return (structure.domain, consts, preds)


def _canon_set(structures, pred_sig):
    return {_canon(s, pred_sig) for s in structures}


def _mm_at_size(premises, circumscribed, size):
    """``minimal_models`` filtered to exactly ``size`` — see module docstring point 1."""
    return [s for s in minimal_models(premises, circumscribed=circumscribed, max_size=size)
            if len(s.domain) == size]


# =============================================================================
# 1. Differential agreement with nonmonotonic.minimal_models
# =============================================================================

class TestDifferentialAgainstMinimalModels:
    def test_disjunctive_fact_with_distinct_constants(self):
        # P(a) v P(b), a != b, size=2, circumscribe {P}.
        #
        # By hand: {a, b} must occupy the two domain individuals in one of
        # two ways (a=0,b=1 or a=1,b=0) -- two "constant groups". Within
        # EACH group, P must be non-empty (to satisfy the disjunction) and
        # subset-minimal, so P is a SINGLETON: {a's value} or {b's value}
        # (P = {a's value, b's value} satisfies the disjunction too but is
        # not minimal, since either singleton is already a proper subset
        # that still satisfies it). 2 constant groups x 2 minimal P choices
        # = 4 minimal models total.
        premises = [Or(Atom("P", (A,)), Atom("P", (B,))), Atom("≠", (A, B))]
        pred_sig = [("P", 1)]
        asp = asp_minimal_models(premises, circumscribed={"P"}, size=2)
        mm = _mm_at_size(premises, {"P"}, size=2)
        assert len(asp) == 4, f"expected 4 hand-derived minimal models, got {len(asp)}"
        assert _canon_set(asp, pred_sig) == _canon_set(mm, pred_sig)

    def test_universally_quantified_subsumption(self):
        # forall x (Q(x) -> P(x)), size=2, circumscribe {P}, Q left free
        # (present in the premise but not in `circumscribed`).
        #
        # By hand: the premise forces P superset-of-Q; minimising P (subject
        # to Q's already-fixed value in each group) forces P == Q EXACTLY --
        # dropping any element of P not forced by Q would still satisfy the
        # implication and is strictly smaller, so it is preferred. Q ranges
        # freely over the 4 subsets of a 2-element domain, and each is its
        # own fixed-part group (Q is not circumscribed) containing exactly
        # one minimal model (P = that same subset). 4 minimal models total,
        # each with P == Q.
        premises = [Quantifier("∀", X, Implies(Atom("Q", (X,)), Atom("P", (X,))))]
        pred_sig = [("P", 1), ("Q", 1)]
        asp = asp_minimal_models(premises, circumscribed={"P"}, size=2)
        mm = _mm_at_size(premises, {"P"}, size=2)
        assert len(asp) == 4, f"expected 4 hand-derived minimal models, got {len(asp)}"
        for s in asp:
            assert s.predicates.get(("P", 1), set()) == s.predicates.get(("Q", 1), set()), (
                "minimality should force P == Q exactly in every returned model"
            )
        assert _canon_set(asp, pred_sig) == _canon_set(mm, pred_sig)

    def test_empty_premises_minimise_to_the_empty_extension(self):
        # No premises at all, size=1, circumscribe {P}: nothing forces any
        # element into P, so the unique minimal extension is EMPTY -- the
        # same closed-world-assumption fact test_nonclassical.py's
        # test_closed_world_assumption pins via minimal_entails, checked
        # here directly against the model set.
        #
        # asp_minimal_models has no premises to scan a signature from, so P
        # is supplied via `extra_signature`-equivalent means: it must appear
        # in at least one premise for the encoder to know about it, so this
        # case instead asserts the WEAKER but still concrete fact that an
        # explicit tautology mentioning P (P(a) -> P(a)) forces nothing about
        # P's extension, and its unique minimal model still has P empty.
        premises = [Implies(Atom("P", (A,)), Atom("P", (A,)))]
        pred_sig = [("P", 1)]
        asp = asp_minimal_models(premises, circumscribed={"P"}, size=1)
        mm = _mm_at_size(premises, {"P"}, size=1)
        assert len(asp) == 1, f"expected exactly 1 minimal model, got {len(asp)}"
        assert asp[0].predicates.get(("P", 1), set()) == set()
        assert _canon_set(asp, pred_sig) == _canon_set(mm, pred_sig)

    def test_unsatisfiable_premises_yield_no_models_in_either_direction(self):
        # P(a) and not P(a) together are unsatisfiable at any size -- both
        # routes must agree on the empty list, not one erroring and the
        # other returning [].
        premises = [Atom("P", (A,)), Not(Atom("P", (A,)))]
        asp = asp_minimal_models(premises, circumscribed={"P"}, size=2)
        mm = _mm_at_size(premises, {"P"}, size=2)
        assert asp == [] and mm == []


# =============================================================================
# 2. Circumscription over a NAMED predicate: the un-named one is fixed
# =============================================================================

class TestCircumscriptionOverANamedPredicate:
    # Shared premises: P(a) and R(a), a single free constant `a`, size=2.
    # The individual NOT named by `a` is unconstrained by any premise, so
    # both P and R are free at that individual -- 4 raw candidates per
    # constant-assignment group (a=0 or a=1): P(other) x R(other), each in
    # {T, F}.
    _PREMISES = [Atom("P", (A,)), Atom("R", (A,))]

    def test_circumscribing_p_only_leaves_r_free_across_the_minimal_set(self):
        # circumscribed={"P"}: within EACH (a-value, R-extension) group, only
        # P is compared, and P(other)=F beats P(other)=T (strict subset,
        # same R) -- so P collapses to the singleton {a's value} in every
        # surviving model, but BOTH values of R(other) (True and False) each
        # give their own group with its own trivially-minimal survivor, so R
        # is NOT collapsed -- both R-extensions appear across the returned
        # set. 2 a-groups x 2 surviving R-values = 4 minimal models.
        asp = asp_minimal_models(self._PREMISES, circumscribed={"P"}, size=2)
        assert len(asp) == 4, f"expected 4 hand-derived minimal models, got {len(asp)}"
        for s in asp:
            a_val = s.constants["a"]
            assert s.predicates.get(("P", 1), set()) == {(a_val,)}, (
                "P (circumscribed) must collapse to exactly {a} in every minimal model"
            )
        r_extensions = {frozenset(s.predicates.get(("R", 1), set())) for s in asp}
        assert len(r_extensions) > 1, (
            "R (fixed, not circumscribed) must keep more than one distinct "
            "extension across the minimal-model set -- if it were being "
            "minimised too, only the smallest R-extension per group would survive"
        )
        mm = _mm_at_size(self._PREMISES, {"P"}, size=2)
        pred_sig = [("P", 1), ("R", 1)]
        assert _canon_set(asp, pred_sig) == _canon_set(mm, pred_sig)

    def test_circumscribing_both_collapses_r_too(self):
        # Same premises, circumscribed={"P", "R"} this time: now R is ALSO
        # minimised, so within each a-group only R(other)=F survives
        # (R = {a's value} exactly, same singleton-collapse argument as P
        # above) -- exactly 2 minimal models (one per a-value), each with
        # P == R == {a's value}. This is the direct contrast with the
        # previous test: changing ONLY the `circumscribed` argument (same
        # premises) changes which predicate collapses to a singleton.
        asp = asp_minimal_models(self._PREMISES, circumscribed={"P", "R"}, size=2)
        assert len(asp) == 2, f"expected 2 hand-derived minimal models, got {len(asp)}"
        for s in asp:
            a_val = s.constants["a"]
            assert s.predicates.get(("P", 1), set()) == {(a_val,)}
            assert s.predicates.get(("R", 1), set()) == {(a_val,)}
        mm = _mm_at_size(self._PREMISES, {"P", "R"}, size=2)
        pred_sig = [("P", 1), ("R", 1)]
        assert _canon_set(asp, pred_sig) == _canon_set(mm, pred_sig)

    def test_default_circumscribed_none_minimises_every_predicate(self):
        # circumscribed=None (the default) minimises EVERY predicate the
        # premises mention -- same collapse-to-singleton argument applied to
        # BOTH P and R at once, so this must match the explicit {"P", "R"}
        # case above exactly (same premises, same size).
        asp_default = asp_minimal_models(self._PREMISES, size=2)
        asp_explicit = asp_minimal_models(self._PREMISES, circumscribed={"P", "R"}, size=2)
        pred_sig = [("P", 1), ("R", 1)]
        assert _canon_set(asp_default, pred_sig) == _canon_set(asp_explicit, pred_sig)


# =============================================================================
# 3. Subset-minimal, not cardinality-minimal (the module's central claim)
# =============================================================================

class TestSubsetMinimalNotCardinalityMinimal:
    # P(a) v (P(b) and P(c)), a, b, c pairwise distinct, size=3 (forcing
    # {a, b, c} to occupy all three domain individuals, one each).
    #
    # By hand, within one fixed constant-assignment group: any P satisfying
    # the disjunction either contains a's value, or contains both b's and
    # c's values. The subset-minimal witnesses of the FIRST disjunct is
    # P = {a} (size 1); of the SECOND is P = {b, c} (size 2) -- and neither
    # is a subset of the other, so BOTH survive subset-minimality (nothing
    # else strictly below either of them also satisfies the premise: shrink
    # {a} and the disjunction breaks; shrink {b,c} to {b} or {c} alone and it
    # breaks too). A CARDINALITY filter would keep only the size-1 answer in
    # every group (1 < 2), discarding every size-2 witness outright -- so
    # "a size-2 extension is present in the output" is the concrete,
    # falsifiable difference between the two orders.
    #
    # 3! = 6 ways to assign {a, b, c} to the 3 domain individuals, x 2
    # minimal-P choices per assignment = 12 minimal models total.
    _PREMISES = [
        Or(Atom("P", (A,)), And(Atom("P", (B,)), Atom("P", (C,)))),
        Atom("≠", (A, B)), Atom("≠", (A, C)), Atom("≠", (B, C)),
    ]

    def test_both_a_singleton_and_a_pair_extension_survive(self):
        asp = asp_minimal_models(self._PREMISES, circumscribed={"P"}, size=3)
        assert len(asp) == 12, f"expected 12 hand-derived minimal models, got {len(asp)}"
        sizes = sorted(len(s.predicates.get(("P", 1), set())) for s in asp)
        assert sizes == [1] * 6 + [2] * 6, (
            "expected 6 singleton-P models and 6 pair-P models -- a "
            "cardinality-minimal filter would have kept ONLY the size-1 "
            "models (dropping every size-2 one), since 1 < 2 regardless of "
            "subset-incomparability"
        )

    def test_the_pair_extension_is_exactly_b_and_c_not_a(self):
        # Pin the SHAPE, not just the size: every size-2 survivor's P is
        # exactly {b's value, c's value} (never containing a's value) --
        # confirms this is genuinely the second disjunct's witness, not some
        # other coincidentally-size-2 set.
        asp = asp_minimal_models(self._PREMISES, circumscribed={"P"}, size=3)
        pair_models = [s for s in asp if len(s.predicates.get(("P", 1), set())) == 2]
        assert len(pair_models) == 6
        for s in pair_models:
            p_ext = s.predicates[("P", 1)]
            expected = {(s.constants["b"],), (s.constants["c"],)}
            got = {(x,) for (x,) in p_ext}
            assert got == expected
            assert (s.constants["a"],) not in p_ext

    def test_differential_against_minimal_models(self):
        pred_sig = [("P", 1)]
        asp = asp_minimal_models(self._PREMISES, circumscribed={"P"}, size=3)
        mm = _mm_at_size(self._PREMISES, {"P"}, size=3)
        assert _canon_set(asp, pred_sig) == _canon_set(mm, pred_sig)


# =============================================================================
# asp_find_model: single-witness sanity (not the module's main focus, but
# public API sharing _build_program with asp_minimal_models above).
# =============================================================================

class TestAspFindModel:
    def test_satisfiable_premise_returns_a_structure(self):
        s = asp_find_model([Atom("P", (A,))], size=1)
        assert isinstance(s, Structure)
        assert s.predicates.get(("P", 1), set()) == {(0,)}

    def test_unsatisfiable_premise_returns_none(self):
        # P(a) and not P(a): no structure of any size satisfies both.
        s = asp_find_model([Atom("P", (A,)), Not(Atom("P", (A,)))], size=2)
        assert s is None


# =============================================================================
# Fragment gate and size validation (the two ways to fail before solving).
# =============================================================================

class TestFragmentGateAndValidation:
    def test_cardinality_is_rejected_by_name(self):
        # Cardinality is admitted by atp.finite_domain.fragment_check but
        # deliberately excluded HERE (see the module docstring's "Fragment
        # supported here" section: tarski's evaluator, this module's own
        # verification oracle, cannot check a Cardinality-VALUED comparison
        # the way this module's term encoding would need to produce one).
        sentence = Atom("=", (A, Cardinality(X, Atom("P", (X,)))))
        try:
            asp_minimal_models([sentence], size=2)
        except ValueError as e:
            assert "Cardinality" in str(e)
        else:
            raise AssertionError("expected ValueError naming Cardinality")

    def test_contrast_is_rejected_by_name(self):
        # Contrast has no case in tarski.satisfies (this module's oracle),
        # so there is nothing to differentially verify it against even if it
        # were encoded -- see the module docstring.
        sentence = Contrast(Atom("P", (A,)), Atom("Q", (A,)))
        try:
            asp_minimal_models([sentence], size=2)
        except ValueError as e:
            assert "Contrast" in str(e)
        else:
            raise AssertionError("expected ValueError naming Contrast")

    def test_size_zero_rejected(self):
        try:
            asp_minimal_models([Atom("P", (A,))], size=0)
        except ValueError as e:
            assert "size" in str(e)
        else:
            raise AssertionError("expected ValueError for size=0")

    def test_size_must_be_a_plain_int_not_a_bool(self):
        # bool is a subclass of int in Python; `isinstance(size, bool)` is
        # checked explicitly ahead of `isinstance(size, int)` in _build_program
        # specifically to catch `size=True` (which would otherwise silently
        # ground a domain of size 1) -- pin that this guard is live.
        try:
            asp_minimal_models([Atom("P", (A,))], size=True)
        except ValueError as e:
            assert "size" in str(e)
        else:
            raise AssertionError("expected ValueError for size=True")
