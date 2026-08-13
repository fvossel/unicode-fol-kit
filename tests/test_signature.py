"""Tests for :mod:`unicode_fol_kit.fol.signature` (the first-class ``Signature``
vocabulary carrier: ``PredicateDecl`` / ``FunctionDecl`` / ``ConstantDecl`` and
the ``Signature`` class itself — ``from_dict`` / ``from_formulas`` / ``to_dict``
/ ``validate`` / ``merge``).

No snapshot tests: every expected value below is derived BY HAND against the
module's own documented rules (see ``unicode_fol_kit/fol/signature.py``'s
module docstring) in each test's own docstring — not by running the code and
copying its output. Formulas are built directly from the AST node
constructors (``Atom``, ``Function``, ``Constant``, ``SortedConstant``,
``Variable``, ``Quantifier``, ``SortedQuantifier``, …) rather than parsed from
Unicode surface syntax, for full control over exactly which node shapes are
exercised (mirroring ``tests/test_casl_export.py``'s own convention).
"""

import json

import pytest

from unicode_fol_kit.fol.nodes import (
    Variable, Constant, SortedConstant, Function, Number,
    Atom, Not, And, Implies, Quantifier, SortedQuantifier, Count,
)
from unicode_fol_kit.fol.signature import (
    Signature, PredicateDecl, FunctionDecl, ConstantDecl,
)


# =============================================================================
# Declaration dataclasses: construction-time validation
# =============================================================================

def test_predicate_decl_rejects_bad_arity():
    """PredicateDecl.arity must be a non-negative int; bool is excluded even
    though Python's bool is an int subclass (True/False silently read as 1/0
    is exactly the kind of accidental input the loud-refusal rule catches).
    """
    with pytest.raises(ValueError, match="arity must be >= 0"):
        PredicateDecl("P", -1)
    with pytest.raises(TypeError, match="arity must be an int"):
        PredicateDecl("P", True)
    with pytest.raises(TypeError, match="arity must be an int"):
        PredicateDecl("P", 1.0)
    # Valid construction: arity 0 is legal (a nullary predicate).
    assert PredicateDecl("Rain", 0).arity == 0


def test_predicate_decl_rejects_mismatched_arg_sorts_length():
    """arg_sorts, when given, must have exactly `arity` entries; a list is
    coerced to a tuple (so two decls built from a list vs. a tuple of the
    same sorts compare equal — dataclass eq compares the coerced tuple)."""
    with pytest.raises(ValueError, match="arg_sorts has 1 entries but arity is 2"):
        PredicateDecl("Loves", 2, ("Human",))
    from_list = PredicateDecl("Loves", 2, ["Human", "Human"])
    from_tuple = PredicateDecl("Loves", 2, ("Human", "Human"))
    assert from_list == from_tuple
    assert isinstance(from_list.arg_sorts, tuple)


def test_function_decl_rejects_bad_result_sort_type():
    """result_sort must be a str or None; anything else (e.g. an int) is
    refused loudly rather than silently stored as garbage metadata."""
    with pytest.raises(TypeError, match="result_sort must be a str or None"):
        FunctionDecl("fatherOf", 1, result_sort=42)
    # Default result_sort is None (unconstrained).
    assert FunctionDecl("fatherOf", 1).result_sort is None


def test_constant_decl_rejects_bad_sort_type():
    """ConstantDecl.sort must be a str or None."""
    with pytest.raises(TypeError, match="sort must be a str or None"):
        ConstantDecl("alice", 7)
    assert ConstantDecl("alice").sort is None


# =============================================================================
# Signature construction: key/value consistency
# =============================================================================

def test_signature_rejects_mismatched_key_and_wrong_decl_class():
    """The dict key under 'predicates'/'functions'/'constants' must equal the
    decl's own .name (else a lookup by key would silently return a decl
    describing a DIFFERENT symbol), and every value must be the matching decl
    class (a FunctionDecl is not a valid 'predicates' entry, for instance)."""
    with pytest.raises(ValueError, match=r"key 'Foo' does not match .*name 'Bar'"):
        Signature(predicates={"Foo": PredicateDecl("Bar", 1)})
    with pytest.raises(TypeError, match="must be a PredicateDecl"):
        Signature(predicates={"f": FunctionDecl("f", 1)})


# =============================================================================
# Signature.from_formulas
# =============================================================================

def test_from_formulas_hand_derived_msfol_example():
    """A small MSFOL example mixing sorted and unsorted vocabulary.

    Formulas:
      f1 = forall x:Human (Mortal(x) -> Loves(x, fatherOf(x)))
      f2 = Human(alice:Human)
      f3 = Rain()                              -- 0-ary, fully unsorted
      f4 = forall y (P(y) v not P(y))          -- PLAIN quantifier

    Hand-derivation:
      * predicates: Mortal/1, Loves/2 (from f1); Human/1 (from f2); Rain/0
        (from f3); P/1 (from f4). All arg_sorts=None (from_formulas never
        infers per-argument-position sorts — see the module docstring).
      * functions: fatherOf/1 (from f1), result_sort=None.
      * constants: alice, sort 'Human' (its one SortedConstant occurrence).
      * sorts: {'Human'} only — f1's SortedQuantifier and f2's SortedConstant
        both name 'Human'; f4's PLAIN Quantifier contributes NOTHING (there
        is no default_sort concept here, unlike casl_export).
    """
    x = Variable("x")
    y = Variable("y")
    f1 = SortedQuantifier(
        "∀", x, "Human",
        Implies(Atom("Mortal", [x]),
                Atom("Loves", [x, Function("fatherOf", [x])])))
    f2 = Atom("Human", [SortedConstant("alice", "Human")])
    f3 = Atom("Rain", [])
    f4 = Quantifier("∀", y, Not(Atom("P", [y])))  # simplified matrix, still P/1

    sig = Signature.from_formulas([f1, f2, f3, f4])

    assert dict(sig.predicates) == {
        "Mortal": PredicateDecl("Mortal", 1),
        "Loves": PredicateDecl("Loves", 2),
        "Human": PredicateDecl("Human", 1),
        "Rain": PredicateDecl("Rain", 0),
        "P": PredicateDecl("P", 1),
    }
    assert dict(sig.functions) == {"fatherOf": FunctionDecl("fatherOf", 1)}
    assert dict(sig.constants) == {"alice": ConstantDecl("alice", "Human")}
    assert sig.sorts == frozenset({"Human"})

    # The inferred signature is, by construction, conformant with every
    # formula it was inferred from.
    for f in (f1, f2, f3, f4):
        assert sig.validate(f) == []


def test_from_formulas_predicate_arity_conflict():
    """Q/1 in one formula and Q/2 in another, across the SAME batch, is an
    unsatisfiable single-arity declaration -> ValueError naming 'Q' and both
    arities (1, 2), sorted ascending."""
    g1 = Atom("Q", [Variable("x")])
    g2 = Atom("Q", [Variable("x"), Variable("y")])
    with pytest.raises(ValueError, match=r"predicate 'Q' used with conflicting arities \(1, 2\)"):
        Signature.from_formulas([g1, g2])


def test_from_formulas_function_arity_conflict():
    """Same idea as the predicate case, for a function symbol f/1 vs f/2."""
    h1 = Atom("R", [Function("f", [Variable("x")])])
    h2 = Atom("R", [Function("f", [Variable("x"), Variable("y")])])
    with pytest.raises(ValueError, match=r"function 'f' used with conflicting arities \(1, 2\)"):
        Signature.from_formulas([h1, h2])


def test_from_formulas_constant_vs_function_clash():
    """'alice' used as a bare Constant in one formula and as a Function
    application in another cannot be reconciled into one declaration."""
    k1 = Atom("S", [Constant("alice")])
    k2 = Atom("T", [Function("alice", [Variable("x")])])
    with pytest.raises(ValueError, match="'alice' is used both as a constant and as a function"):
        Signature.from_formulas([k1, k2])


def test_from_formulas_constant_sort_conflict():
    """'bob' annotated :Human in one formula and :Animal in another is a
    genuine sort conflict -> ValueError naming 'bob' and both sorts, sorted
    alphabetically ('Animal' < 'Human')."""
    m1 = Atom("U", [SortedConstant("bob", "Human")])
    m2 = Atom("V", [SortedConstant("bob", "Animal")])
    with pytest.raises(ValueError,
                       match=r"constant 'bob' used with conflicting sorts \('Animal', 'Human'\)"):
        Signature.from_formulas([m1, m2])


# =============================================================================
# Signature.from_dict — the api.check loose convention and the rich form
# =============================================================================

def test_from_dict_accepts_exact_api_check_loose_convention():
    """The exact dict shape unicode_fol_kit/api.py's _signature_errors reads
    and tests/test_api.py constructs (test_check_signature_wrong_arity_and_
    suggestion / test_check_passes_a_clean_sentence):

        {"predicates": {"Human": 1, "Mortal": 1}, "constants": ["a", "b"]}

    (predicates/functions: name -> int arity; constants: a bare iterable of
    names.) No 'functions' key at all is legal (an absent section, not an
    empty one — from_dict just treats it as {})."""
    d = {"predicates": {"Human": 1, "Mortal": 1}, "constants": ["a", "b"]}
    sig = Signature.from_dict(d)
    assert dict(sig.predicates) == {
        "Human": PredicateDecl("Human", 1), "Mortal": PredicateDecl("Mortal", 1),
    }
    assert dict(sig.functions) == {}
    assert dict(sig.constants) == {"a": ConstantDecl("a"), "b": ConstantDecl("b")}
    assert sig.sorts == frozenset()


def test_from_dict_loose_multi_arity_collapse_and_conflict():
    """api.check's loose convention also allows an ITERABLE of allowed
    arities per symbol (a permissive validation CONSTRAINT). A Signature
    declares exactly one arity per symbol, so: a single-element iterable
    ({1} or [1]) collapses losslessly to that one arity; an iterable naming
    MORE than one distinct arity cannot be represented and is refused."""
    sig = Signature.from_dict({"predicates": {"P": [2]}})
    assert dict(sig.predicates) == {"P": PredicateDecl("P", 2)}

    with pytest.raises(ValueError, match=r"lists multiple allowed arities \(1, 2\)"):
        Signature.from_dict({"predicates": {"P": {1, 2}}})


def test_from_dict_rich_form_with_sorts():
    """The rich per-entry dict form: {'arity':.., 'arg_sorts':.., (functions
    only) 'result_sort':..}; constants as a dict (name -> sort-or-None); plus
    an explicit top-level 'sorts' entry ('Robot') that no decl otherwise
    implies, unioned in alongside the sorts the decls themselves imply
    ('Human', from Loves' arg_sorts, fatherOf's arg_sorts/result_sort, and
    alice's own sort — all consistently 'Human' here)."""
    d = {
        "predicates": {"Loves": {"arity": 2, "arg_sorts": ["Human", "Human"]}},
        "functions": {"fatherOf": {"arity": 1, "arg_sorts": ["Human"],
                                    "result_sort": "Human"}},
        "constants": {"alice": "Human", "unsorted_thing": None},
        "sorts": ["Robot"],
    }
    sig = Signature.from_dict(d)
    assert sig.predicates["Loves"] == PredicateDecl("Loves", 2, ("Human", "Human"))
    assert sig.functions["fatherOf"] == FunctionDecl("fatherOf", 1, ("Human",), "Human")
    assert dict(sig.constants) == {
        "alice": ConstantDecl("alice", "Human"),
        "unsorted_thing": ConstantDecl("unsorted_thing", None),
    }
    assert sig.sorts == frozenset({"Human", "Robot"})


def test_from_dict_rejects_unknown_top_level_key():
    """A typo'd top-level key ('predicate' instead of 'predicates') is
    refused rather than silently ignored (which would make the whole section
    vanish without a trace)."""
    with pytest.raises(ValueError, match=r"unexpected top-level key\(s\) \['predicate'\]"):
        Signature.from_dict({"predicate": {"P": 1}})


def test_from_dict_rejects_unexpected_rich_entry_key():
    """A rich predicate entry with an unrecognised key (a typo, or 'result_
    sort' misapplied to a PREDICATE — only functions carry that field) is
    refused; a rich entry missing the required 'arity' key is refused too."""
    with pytest.raises(ValueError, match=r"unexpected key\(s\) \['result_sort'\]"):
        Signature.from_dict({"predicates": {"P": {"arity": 1, "result_sort": "Human"}}})
    with pytest.raises(ValueError, match="missing the required key 'arity'"):
        Signature.from_dict({"predicates": {"P": {"arg_sorts": [None]}}})


# =============================================================================
# to_dict / from_dict round trip
# =============================================================================

def test_to_dict_from_dict_round_trip_is_byte_stable():
    """A signature built via from_formulas serialises and deserialises back
    to an equal Signature, and to_dict's own output is deterministic (same
    dict, same JSON text) across repeated calls -- independent of Python's
    (unordered) internal dict/set iteration, because to_dict always sorts
    its entries by name."""
    x = Variable("x")
    f = SortedQuantifier("∀", x, "Human", Atom("Mortal", [x]))
    g = Atom("Human", [SortedConstant("alice", "Human")])
    sig = Signature.from_formulas([f, g])

    d1 = sig.to_dict()
    d2 = sig.to_dict()
    assert d1 == d2
    assert json.dumps(d1, sort_keys=False) == json.dumps(d2, sort_keys=False)

    round_tripped = Signature.from_dict(sig.to_dict())
    assert round_tripped == sig


def test_to_dict_from_dict_round_trip_preserves_unused_sort():
    """A sort present in Signature.sorts but not implied by ANY decl (a
    genuinely 'declared but unused' sort — e.g. one meant for a symbol not
    yet added) still round-trips, because to_dict emits the full sorts set
    explicitly and from_dict reads the 'sorts' key back."""
    sig = Signature(predicates={"P": PredicateDecl("P", 1)},
                    sorts=frozenset({"Human", "Unused"}))
    d = sig.to_dict()
    assert d["sorts"] == ["Human", "Unused"]
    assert Signature.from_dict(d) == sig


# =============================================================================
# Signature.validate
# =============================================================================

def test_validate_undeclared_predicate():
    """'a' IS declared as a constant, so the sole violation is the undeclared
    predicate 'Foo' -- constants are still recursed into and reported
    separately if THEY were undeclared, but here they are not."""
    sig = Signature(constants={"a": ConstantDecl("a")})
    f = Atom("Foo", [Constant("a")])
    assert sig.validate(f) == ["undeclared predicate 'Foo' (arity 1)"]


def test_validate_undeclared_function():
    """P/1 and constant 'a' are both declared; only the function 'bar' is
    not, so it is the sole violation."""
    sig = Signature(predicates={"P": PredicateDecl("P", 1)},
                    constants={"a": ConstantDecl("a")})
    f = Atom("P", [Function("bar", [Constant("a")])])
    assert sig.validate(f) == ["undeclared function 'bar' (arity 1)"]


def test_validate_undeclared_constant():
    """P/1 is declared; the constant 'a' passed to it is not."""
    sig = Signature(predicates={"P": PredicateDecl("P", 1)})
    f = Atom("P", [Constant("a")])
    assert sig.validate(f) == ["undeclared constant 'a'"]


def test_validate_arity_mismatch_predicate_and_function():
    """P declared arity 1, used with 2 constant args (both declared, so no
    extra 'undeclared constant' noise); separately, g declared arity 1, used
    with 2 args -- checked as two independent one-violation formulas."""
    sig = Signature(predicates={"P": PredicateDecl("P", 1)},
                    functions={"g": FunctionDecl("g", 1)},
                    constants={"a": ConstantDecl("a"), "b": ConstantDecl("b")})
    f_pred = Atom("P", [Constant("a"), Constant("b")])
    assert sig.validate(f_pred) == [
        "predicate 'P' expects arity 1, used with arity 2"
    ]
    f_func = Atom("P", [Function("g", [Constant("a"), Constant("b")])])
    assert sig.validate(f_func) == [
        "function 'g' expects arity 1, used with arity 2"
    ]


def test_validate_sort_mismatch_predicate_argument():
    """Loves declared (Human, Animal); x is bound :Human by the outer
    SortedQuantifier (matches argument 1, no violation) and y is bound
    :Robot by the inner one (declared argument 2 is 'Animal' -- BOTH sides
    concrete and different -> exactly one violation, on argument 2 only)."""
    sig = Signature(predicates={"Loves": PredicateDecl("Loves", 2, ("Human", "Animal"))})
    x, y = Variable("x"), Variable("y")
    f = SortedQuantifier("∀", x, "Human",
                         SortedQuantifier("∀", y, "Robot", Atom("Loves", [x, y])))
    assert sig.validate(f) == [
        "predicate 'Loves' argument 2 expects sort 'Animal', got sort 'Robot'"
    ]


def test_validate_sort_mismatch_sorted_constant_vs_declared():
    """'alice' is declared sort 'Human' in the signature but annotated
    :Robot at its use site -- both sides concrete, both different."""
    sig = Signature(predicates={"P": PredicateDecl("P", 1)},
                    constants={"alice": ConstantDecl("alice", "Human")})
    f = Atom("P", [SortedConstant("alice", "Robot")])
    assert sig.validate(f) == [
        "constant 'alice' is annotated sort 'Robot' here but declared sort "
        "'Human' in the signature"
    ]


def test_validate_clean_pass_conforms():
    """A signature that matches its formula exactly (arities, and the one
    concrete sort involved) produces zero violations."""
    sig = Signature(
        predicates={"Mortal": PredicateDecl("Mortal", 1, ("Human",))},
        constants={"alice": ConstantDecl("alice", "Human")})
    f = Atom("Mortal", [SortedConstant("alice", "Human")])
    assert sig.validate(f) == []


def test_validate_builtin_operators_never_flagged():
    """'=' and '+' are built-in operators, never user vocabulary that needs
    declaring -- but their OWN arguments are still recursed into and checked
    (both 'a' and 'b' are declared here, so nothing is flagged)."""
    sig = Signature(constants={"a": ConstantDecl("a", "Human"),
                               "b": ConstantDecl("b", "Human")})
    equality = Atom("=", [Constant("a"), Constant("b")])
    assert sig.validate(equality) == []

    sig2 = Signature(predicates={"P": PredicateDecl("P", 1)},
                     constants={"a": ConstantDecl("a"), "b": ConstantDecl("b")})
    arithmetic = Atom("P", [Function("+", [Constant("a"), Constant("b")])])
    assert sig2.validate(arithmetic) == []


def test_validate_recurses_through_unrecognised_node_types():
    """An empty Signature declares nothing. 'Foo'/'Bar' are undeclared and
    sit under Not/And (ordinary connectives) -- both are still found (two
    violations, one per occurrence). Separately, an Atom buried inside a
    Count node (a binder type this module does not special-case) is still
    reached via the generic _child_nodes() fallback, and Count's OWN bound
    variable 'z' produces no spurious violation (a bare Variable outside an
    Atom's arguments is never checked)."""
    sig = Signature()
    connective = Not(And(Atom("Foo", []), Atom("Bar", [])))
    assert sig.validate(connective) == [
        "undeclared predicate 'Foo' (arity 0)",
        "undeclared predicate 'Bar' (arity 0)",
    ]

    z = Variable("z")
    counting = Count("ge", Number(2), z, Atom("Foo", [z]))
    assert sig.validate(counting) == ["undeclared predicate 'Foo' (arity 1)"]


# =============================================================================
# Signature.merge
# =============================================================================

def test_merge_union_of_disjoint_signatures():
    """Two signatures with disjoint vocabularies merge into their union,
    with no conflicts to refuse."""
    sig_a = Signature(predicates={"P": PredicateDecl("P", 1)},
                      sorts=frozenset({"Human"}))
    sig_b = Signature(constants={"a": ConstantDecl("a")},
                      sorts=frozenset({"Animal"}))
    merged = sig_a.merge(sig_b)
    assert dict(merged.predicates) == {"P": PredicateDecl("P", 1)}
    assert dict(merged.constants) == {"a": ConstantDecl("a")}
    assert merged.sorts == frozenset({"Human", "Animal"})


def test_merge_identical_overlap_is_fine():
    """A symbol declared IDENTICALLY on both sides is not a conflict --
    the merge simply keeps it."""
    sig_a = Signature(predicates={"P": PredicateDecl("P", 1)})
    sig_b = Signature(predicates={"P": PredicateDecl("P", 1)},
                      constants={"a": ConstantDecl("a")})
    merged = sig_a.merge(sig_b)
    assert dict(merged.predicates) == {"P": PredicateDecl("P", 1)}
    assert dict(merged.constants) == {"a": ConstantDecl("a")}


def test_merge_conflicting_declaration_refused():
    """P/1 vs P/2 on the two sides cannot be reconciled -- ValueError naming
    the symbol and both declarations."""
    sig_a = Signature(predicates={"P": PredicateDecl("P", 1)})
    sig_b = Signature(predicates={"P": PredicateDecl("P", 2)})
    with pytest.raises(ValueError, match="conflicting predicate declaration for 'P'"):
        sig_a.merge(sig_b)


# =============================================================================
# Equality and hashability
# =============================================================================

def test_equality_across_construction_paths_and_not_hashable():
    """Two Signatures with the same content compare equal REGARDLESS of which
    constructor built them (from_dict vs. the plain dataclass constructor),
    a differently-declared Signature compares unequal, and (because the
    symbol tables are stored as MappingProxyType views over a dict, which
    Python's dict is never hashable) a Signature itself cannot be hashed."""
    via_from_dict = Signature.from_dict({"predicates": {"Human": 1}})
    via_constructor = Signature(predicates={"Human": PredicateDecl("Human", 1)})
    assert via_from_dict == via_constructor

    different = Signature(predicates={"Human": PredicateDecl("Human", 2)})
    assert via_from_dict != different

    with pytest.raises(TypeError, match="unhashable type"):
        hash(via_from_dict)


def test_api_check_accepts_a_signature_object():
    """Central integration: api.check(signature=Signature) projects the
    object onto the loose convention, so the structured did-you-mean
    diagnostics are byte-identical to the dict path. Hand-derived: Humann/1
    against a signature declaring Human/1 → one unknown_predicate error
    with suggestion 'Human'."""
    from unicode_fol_kit import api

    sig = Signature.from_dict({"predicates": {"Human": 1},
                               "constants": ["socrates"]})
    result = api.check("Humann(socrates)", signature=sig)
    assert result.ok is False
    (err,) = result.signature_errors
    assert err["kind"] == "unknown_predicate"
    assert err["symbol"] == "Humann"
    assert err["suggestion"] == "Human"
    dict_result = api.check("Humann(socrates)", signature={
        "predicates": {"Human": 1}, "constants": ["socrates"]})
    assert result.signature_errors == dict_result.signature_errors
