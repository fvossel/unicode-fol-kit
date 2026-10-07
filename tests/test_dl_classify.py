"""Tests for unicode_logic_kit.dl.classify (dl/classification.py): TBox classification as a pure reduction to
`subsumes`.

Hand-checked against small taxonomies worked out by hand (including the family
ontology already used in docs/guide/description-logic.md), plus a differential
cross-check that ties the aggregate `Classification.ancestors` structure directly
back to the already-trusted `dl.subsumes` primitive, rather than trusting the new
union-find / transitive-reduction code in isolation.
"""

import unicode_logic_kit.dl as dl


def _chain_taxonomy():
    # Animal > Mammal > Dog/Cat, Dog > Poodle.
    Animal, Mammal, Dog, Cat, Poodle = (
        dl.Atomic(n) for n in ("Animal", "Mammal", "Dog", "Cat", "Poodle")
    )
    t = (dl.TBox().add(Mammal, Animal).add(Dog, Mammal).add(Cat, Mammal).add(Poodle, Dog))
    return t


def test_chain_taxonomy_hasse_diagram():
    # Poodle's *direct* parent must be Dog only, never the transitively-implied
    # Mammal/Animal -- the one property a naive "dump every pairwise subsumes() hit"
    # implementation would get wrong.
    t = _chain_taxonomy()
    cl = dl.classify(t)
    assert cl.parents == {
        "Animal": frozenset(),
        "Mammal": frozenset({"Animal"}),
        "Dog": frozenset({"Mammal"}),
        "Cat": frozenset({"Mammal"}),
        "Poodle": frozenset({"Dog"}),
    }
    assert cl.children == {
        "Animal": frozenset({"Mammal"}),
        "Mammal": frozenset({"Dog", "Cat"}),
        "Dog": frozenset({"Poodle"}),
        "Cat": frozenset(),
        "Poodle": frozenset(),
    }
    # ancestors is the un-reduced transitive closure -- Poodle's ancestors include
    # Mammal and Animal even though they are not its direct parent.
    assert cl.ancestors["Poodle"] == frozenset({"Dog", "Mammal", "Animal"})
    assert cl.ancestors["Animal"] == frozenset()


def test_family_ontology_matches_guide():
    # The family ontology already worked out by hand in
    # docs/guide/description-logic.md: Mother/Father ⊑ Parent ⊑ Person, and the
    # sexes are disjoint (Male ⊑ ¬Female).
    Person, Male, Female = dl.Atomic("Person"), dl.Atomic("Male"), dl.Atomic("Female")
    Parent, Mother, Father = dl.Atomic("Parent"), dl.Atomic("Mother"), dl.Atomic("Father")
    t = (dl.TBox()
         .add_equivalence(Parent, dl.And(Person, dl.Exists("hasChild", Person)))
         .add_equivalence(Mother, dl.And(Parent, Female))
         .add_equivalence(Father, dl.And(Parent, Male))
         .add(Male, dl.Not(Female)))
    cl = dl.classify(t)
    assert cl.children["Person"] == frozenset({"Parent"})
    assert cl.children["Parent"] == frozenset({"Mother", "Father"})
    # Mother ≡ Parent ⊓ Female: both Parent and Female are direct (non-redundant)
    # parents, since neither subsumes the other.
    assert cl.parents["Mother"] == frozenset({"Parent", "Female"})
    assert cl.parents["Father"] == frozenset({"Parent", "Male"})


def test_equivalence_class_collapses_not_a_two_cycle():
    # Two GCIs forced by add_equivalence between two ATOMIC names (Bachelor,
    # UnmarriedMan) must collapse into one `equivalents` class rather than showing
    # up as a spurious 2-cycle Bachelor -> UnmarriedMan -> Bachelor in `parents`.
    #
    # Deviation from the build spec's own example `Bachelor ≡ Man ⊓ ¬Married`: its
    # right-hand side is a *compound* expression, not a second atomic name, so it
    # has nothing of its own to collapse with Bachelor -- classify() only tracks
    # named (Atomic) concepts, per the "named-concept subsumption hierarchy" the
    # spec itself asks for. This test instead uses two atomic names, which is the
    # case the equivalence-collapse logic actually has to get right.
    Bachelor = dl.Atomic("Bachelor")
    UnmarriedMan = dl.Atomic("UnmarriedMan")
    Man = dl.Atomic("Man")
    t = dl.TBox().add_equivalence(Bachelor, UnmarriedMan).add(Bachelor, Man)
    cl = dl.classify(t)
    assert cl.equivalents["Bachelor"] == frozenset({"Bachelor", "UnmarriedMan"})
    assert "UnmarriedMan" not in cl.parents        # not a key of its own; collapsed
    assert "UnmarriedMan" not in cl.children
    assert cl.parents["Bachelor"] == frozenset({"Man"})
    assert cl.children["Man"] == frozenset({"Bachelor"})
    assert "Bachelor" not in cl.ancestors["Bachelor"]   # no self-loop / 2-cycle


def test_ancestors_differential_against_subsumes():
    # Ties the aggregate `ancestors` structure directly back to the single-pair
    # `subsumes` primitive the project already trusts.
    t = _chain_taxonomy()
    cl = dl.classify(t)
    names = sorted(cl.ancestors)
    checked = 0
    for a in names:
        for b in names:
            if a == b:
                continue
            expected = dl.subsumes(dl.Atomic(a), dl.Atomic(b), t)
            assert (b in cl.ancestors[a]) == expected, (a, b)
            checked += 1
    assert checked == len(names) * (len(names) - 1) == 20


def test_hasse_property_no_shortcut_edges():
    # No `parents` edge a -> b is reachable via a second node c also a direct parent
    # of a: the returned graph really is transitively reduced. Checked on the chain
    # taxonomy above plus a random-ish 7-concept taxonomy (a "diamond" plus a spike).
    def assert_transitively_reduced(t):
        cl = dl.classify(t)
        for a, direct in cl.parents.items():
            for b in direct:
                for c in direct:
                    if c != b:
                        assert b not in cl.parents.get(c, frozenset()), (a, b, c)

    assert_transitively_reduced(_chain_taxonomy())

    A, B, C, D, E, F, G = (dl.Atomic(n) for n in "ABCDEFG")
    t2 = (dl.TBox()
          .add(B, A).add(C, A)          # B, C ⊑ A
          .add(D, B).add(D, C)          # D ⊑ B, D ⊑ C  (diamond under A)
          .add(E, D)                    # E ⊑ D
          .add(F, A).add(G, F))         # a separate spike F ⊑ A, G ⊑ F
    assert_transitively_reduced(t2)
    cl2 = dl.classify(t2)
    # D's direct parents are B and C only, never the transitively-implied A.
    assert cl2.parents["D"] == frozenset({"B", "C"})
    assert cl2.ancestors["D"] == frozenset({"A", "B", "C"})
    assert cl2.ancestors["E"] == frozenset({"A", "B", "C", "D"})


def test_isolated_and_extra_vocabulary_names():
    # `concepts` extends the vocabulary with a name that never appears in the TBox:
    # an isolated node, its own singleton equivalence class, no parents/children.
    A, B, Extra = dl.Atomic("A"), dl.Atomic("B"), dl.Atomic("Extra")
    t = dl.TBox().add(A, B)
    cl = dl.classify(t, concepts=[Extra])
    assert cl.equivalents["Extra"] == frozenset({"Extra"})
    assert cl.parents["Extra"] == frozenset()
    assert cl.children["Extra"] == frozenset()
    assert cl.ancestors["Extra"] == frozenset()
    assert "Extra" not in (cl.parents["A"] | cl.parents["B"])
    # without the `concepts` argument, Extra is invisible (not part of the TBox).
    assert "Extra" not in dl.classify(t).equivalents


def test_empty_tbox_classifies_nothing():
    cl = dl.classify(dl.TBox())
    assert cl.equivalents == {}
    assert cl.parents == {}
    assert cl.children == {}
    assert cl.ancestors == {}
