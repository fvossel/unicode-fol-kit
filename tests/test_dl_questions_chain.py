r"""``TBox.add_role_chain`` takes an ORDERED collection of role names.

The first version of the shape guard refused ANY input that is not a ``Sequence``, so a
generator or an iterator of role names — ordered, and accepted before the guard
existed — was refused with the false reason "an unordered collection has no
order to preserve". The guard exists for two inputs and refuses exactly those:

* a ``str`` or ``bytes`` is not a chain: ``tuple("rs")`` is ``("r", "s")``, so
  ``add_role_chain("rs", "t")`` stored two roles nobody named, and
  ``"PartOf"`` became six single-letter roles;
* a set-like collection (``set``, ``frozenset``, a dict's key view) has no order,
  and the order of a chain is its meaning.

Anything else iterable is read in order and stored as a ``tuple``; the length
(at least two) and the element types are checked on that tuple.
"""

import pytest

import unicode_fol_kit.dl as dl


def _generator():
    return (role for role in ("r", "s", "u"))


@pytest.mark.parametrize("make", [
    _generator,
    lambda: iter(["r", "s", "u"]),
    lambda: map(str, ["r", "s", "u"]),
    lambda: reversed(["u", "s", "r"]),
    lambda: ("r", "s", "u"),
    lambda: ["r", "s", "u"],
], ids=["generator", "iterator", "map", "reversed", "tuple", "list"])
def test_an_ordered_iterable_of_roles_is_a_chain_and_is_stored_in_order(make):
    # RED before for the generator, the iterator, map and reversed: refused as
    # "an unordered collection". Each yields r, s, u in that order.
    tbox = dl.TBox().add_role_chain(make(), "t")
    assert tbox.role_chains == [(("r", "s", "u"), "t")]
    # a generator is read ONCE: the stored chain is the tuple, not the exhausted
    # iterator, and its image is the one the tuple would give
    assert dl.rbox_to_fol(tbox) == dl.rbox_to_fol(dl.TBox().add_role_chain(("r", "s", "u"), "t"))


def test_the_image_of_a_chain_read_from_a_generator_is_hand_derived():
    # P1 ∘ P2 ∘ P3 ⊑ Q  holds iff for every y0 … y3 with <y0,y1> ∈ P1, <y1,y2> ∈
    # P2, <y2,y3> ∈ P3 we have <y0,y3> ∈ Q (OWL 2 direct semantics): the body is
    # the three step atoms, the head links the first variable to the last.
    # Four chain variables: x, y, z, then the next minted, x0.
    tbox = dl.TBox().add_role_chain((role for role in ("P1", "P2", "P3")), "Q")
    assert dl.rbox_to_fol(tbox).to_unicode_str() == (
        "∀x ∀y ∀z ∀x0 (P1(x, y) ∧ P2(y, z) ∧ P3(z, x0) → Q(x, x0))")


@pytest.mark.parametrize("chain, why", [
    ("rs", "CHARACTERS"),
    ("PartOf", "CHARACTERS"),
    (b"rs", "bytes"),
    ({"r", "s"}, "unordered"),
    (frozenset({"r", "s"}), "unordered"),
    ({"r": 1, "s": 2}.keys(), "unordered"),
    ({"r": 1, "s": 2}.items(), "unordered"),
], ids=["str", "str-word", "bytes", "set", "frozenset", "keys", "items"])
def test_a_string_and_a_set_are_refused_and_each_says_why(chain, why):
    with pytest.raises(dl.RoleExpressionError, match="SEQUENCE of role names") as info:
        dl.TBox().add_role_chain(chain, "t")
    assert why in str(info.value)


@pytest.mark.parametrize("chain", [3, None, 2.5, object()])
def test_a_non_collection_is_refused_without_the_false_reason(chain):
    with pytest.raises(dl.RoleExpressionError, match="SEQUENCE of role names") as info:
        dl.TBox().add_role_chain(chain, "t")
    assert "not a collection of role names" in str(info.value)
    assert "unordered" not in str(info.value)


def test_the_length_and_the_elements_of_a_materialised_chain_are_still_checked():
    with pytest.raises(dl.RoleExpressionError, match="at least 2"):
        dl.TBox().add_role_chain(iter(["r"]), "t")
    with pytest.raises(dl.RoleExpressionError, match="at least 2"):
        dl.TBox().add_role_chain((r for r in ()), "t")
    with pytest.raises(dl.RoleExpressionError, match="InverseRole"):
        dl.TBox().add_role_chain(iter([dl.InverseRole("r"), "s"]), "t")
    with pytest.raises(dl.RoleExpressionError, match="BUILT-IN"):
        dl.TBox().add_role_chain(iter(["owl:topObjectProperty", "s"]), "t")


def test_a_stored_chain_is_still_held_to_a_tuple_or_a_list():
    # The second line of defence (a TBox assembled by hand) does not consume a
    # stored iterator: there a chain must BE a tuple or a list.
    for stored in (iter(["r", "s"]), {"r", "s"}, "rs"):
        tbox = dl.TBox()
        tbox.role_chains.append((stored, "t"))
        with pytest.raises(dl.RoleExpressionError, match="SEQUENCE of role names"):
            dl.rbox_to_fol(tbox)
    tbox = dl.TBox()
    tbox.role_chains.append((["r", "s"], "t"))
    assert dl.rbox_to_fol(tbox).to_unicode_str() == "∀x ∀y ∀z (r(x, y) ∧ s(y, z) → t(x, z))"
