"""Tests for the NXF export (atp.tptp_ncl) and the Leo-III backend (atp.leo3_backend).

The golden-text export tests are hand-checked against the verified NXF syntax
sources cited in ``atp/tptp_ncl.py``'s module docstring (Steen & Sutcliffe's
TPTP-World infrastructure paper, and the real, prover-exercised ``.p`` files
from ``github.com/TPTPWorld/NonClassicalLogic`` — most directly
``k45_branch_p.0001.p``, which is the shape every line below is checked
against) — NOT snapshots of whatever the code happens to emit.

No local Leo-III install exists on this machine (``$UFK_LEO3`` unset), so
every backend test below except the final skipped one exercises discovery
logic and the pure-Python problem-generation/error-mapping path with no
subprocess ever spawned; the final test documents and (when a real Leo-III
IS available) runs the actual integration path.
"""

import os
import subprocess

import pytest

from unicode_fol_kit.fol.nodes import (
    Atom, Not, And, Or, Implies, Iff, Box, Diamond, Knows, Quantifier, Variable,
)
from unicode_fol_kit.atp.protocol import PROVED, REFUTED, UNKNOWN, BackendUnavailable
from unicode_fol_kit.atp.tptp_ncl import to_tptp_ncl
from unicode_fol_kit.atp.leo3_backend import Leo3Backend
from unicode_fol_kit.atp.kripke_enum import kripke_model_from_dict
from unicode_fol_kit.semantics.kripke import satisfies_modal

p, q = Atom("p", ()), Atom("q", ())


# ---------------------------------------------------------------------------
# Golden-text export tests
# ---------------------------------------------------------------------------

def test_k_axiom_export_in_k():
    """□(p→q)→(□p→□q) — the K distribution axiom — exported for frame K.

    Hand-derived against the module's OWN rendering rules (see
    ``atp/tptp_ncl.py::_render`` docstring), each individually checked
    against the sources:

    * the logic-spec block's 4-key shape and exact literal text
      (``$domains == $constant, $designation == $rigid, $terms == $global,
      $modalities == $modal_system_K``) is the form confirmed verbatim by
      ``LogicSpecifications/CorrectSpecifications.p``'s ``simple_s5``/
      ``quantification`` blocks (same 4 keys, same ``==``/``,``/``]``
      punctuation), with ``$modal_system_K`` in place of ``_S5`` — ``_K`` is
      the literal system name ``k45_branch_p.0001.p`` builds on
      (``$modal_system_K45``, i.e. ``K`` + axioms; ``K`` alone is the same
      family's base name).
    * one ``tff(p_decl,type,p: $o).``/``tff(q_decl,type,q: $o).`` per
      propositional letter, in first-occurrence order (p before q, matching
      the formula's own left-to-right occurrence) — the exact shape
      ``k45_branch_p.0001.p`` uses for every one of its 15 propositional
      letters (``tff(p0_decl,type, p0: $o ).``).
    * ``[.]`` applied directly to an atom needs no parens (``[.] p``); applied
      to a compound (p => q) it wraps that compound's own already-
      parenthesised rendering with no EXTRA parens, since ``(p => q)`` is
      already a self-delimited ``unary`` production — mirrors
      ``k45_branch_p.0001.p``'s ``<.> [.] y100`` (chained prefix connectives,
      no parens between them) and ``fol/tptp_input.py``'s ``?unary: "~" unary
      | ...`` grammar rule that ``[.]``/``<.>`` are confirmed to occupy the
      same slot as.
    * the classical connectives ``&``/``=>`` render exactly as
      ``Node.to_tptp`` already does for And/Implies (``(l & r)``/
      ``(l => r)``) — reused, not reinvented (see module docstring).
    """
    formula = Implies(Box(Implies(p, q)), Implies(Box(p), Box(q)))
    text = to_tptp_ncl(formula, frame="K", conjecture_name="k_axiom")

    expected = (
        "tff(k_axiom_logic,logic,\n"
        "    $modal ==\n"
        "      [ $domains == $constant,\n"
        "        $designation == $rigid,\n"
        "        $terms == $global,\n"
        "        $modalities == $modal_system_K ] ).\n"
        "\n"
        "tff(p_decl,type,\n"
        "    p: $o ).\n"
        "\n"
        "tff(q_decl,type,\n"
        "    q: $o ).\n"
        "\n"
        "tff(k_axiom,conjecture,\n"
        "    ([.] (p => q) => ([.] p => [.] q)) ).\n"
    )
    assert text == expected


def test_diamond_export_in_s4():
    """◇p exported for frame S4 — the minimal single-atom, single-operator case.

    Hand-checked: logic spec carries ``$modal_system_S4`` (the literal name
    confirmed by the infrastructure paper's system enumeration); one type
    declaration for ``p``; the conjecture body is ``<.> p`` — the diamond
    short form applied directly to an atom needs no parens, exactly as
    ``k45_branch_p.0001.p``'s ``<.> [.] y100`` applies ``<.>`` directly to a
    following prefix-op chain with no parenthesis.
    """
    text = to_tptp_ncl(Diamond(p), frame="S4", conjecture_name="poss_p")

    expected = (
        "tff(poss_p_logic,logic,\n"
        "    $modal ==\n"
        "      [ $domains == $constant,\n"
        "        $designation == $rigid,\n"
        "        $terms == $global,\n"
        "        $modalities == $modal_system_S4 ] ).\n"
        "\n"
        "tff(p_decl,type,\n"
        "    p: $o ).\n"
        "\n"
        "tff(poss_p,conjecture,\n"
        "    <.> p ).\n"
    )
    assert text == expected


@pytest.mark.parametrize("frame,system", [
    ("K", "$modal_system_K"),
    ("T", "$modal_system_T"),
    ("S4", "$modal_system_S4"),
    ("S5", "$modal_system_S5"),
    ("D", "$modal_system_D"),
])
def test_logic_spec_line_per_frame(frame, system):
    """Each of the five frames this kit's modal routes support (K/T/S4/S5 via
    atp.modal_tableau, D via fol.qml.qml_is_valid) maps to its literal
    ``$modal_system_<X>`` token, one-to-one, with no surprise renaming —
    every name is individually confirmed present (as a literal token) in the
    corpus's own CANONICAL sources (see ``atp/tptp_ncl.py``'s module
    docstring 'Sources' for exactly which file proves which token).

    ``"T"`` maps to ``$modal_system_T`` (reverted here, adversarial review;
    a since-reverted intermediate revision of this module briefly asserted
    ``$modal_system_M`` instead, on the strength of one archived/derived
    corpus file and a docstring claim -- never actually re-verified -- that
    a corpus-wide search for ``modal_system_T`` returned zero hits). Direct
    verification against the cited corpus
    (``github.com/TPTPWorld/NonClassicalLogic``) shows the opposite:
    ``Logics/LOG001_4.l`` (the corpus's own canonical modal-system
    DEFINITIONS file) defines ``$modal_system_T`` and never defines
    ``$modal_system_M`` anywhere; ``Tooling/generateSemantics.py`` (the
    corpus's own canonical semantics generator) lists exactly
    ``$modal_system_K``/``_T``/``_D``/``_S4``/``_S5`` as its
    ``all_modalities`` tuple; and every one of the eight canonical
    ``ProblemBuilding/QMLTP/SemanticSpecifications/t_*.p`` files reads
    ``$modalities == $modal_system_T``. ``$modal_system_M`` appears only as
    a usage inside ``ProblemBuilding/QMLTP/8_QMLTP``, which that directory's
    own README describes as "expanded versions of 7_QMLTP with all
    combinations of the specification parameters" (a derived/generated
    subtree referencing a token the corpus's own canonical definitions file
    never defines) -- not a legitimate alternate spelling. ``"D"`` is
    confirmed by ``ProblemBuilding/QMLTP/7_QMLTPTP/APM/APM002_1.p`` and the
    ``kd_branch_p/*.p`` family.
    """
    text = to_tptp_ncl(Box(p), frame=frame)
    assert f"$modalities == {system} ] )." in text


def test_d_frame_does_not_collide_with_qml_deontic_d():
    """fol.qml.py separately uses the relation name "D" for its DEONTIC
    accessibility relation (Obligatory/Permitted) -- an entirely different
    thing from this exporter's alethic "D" (seriality) frame. The two must
    never be confused in the exported TEXT: the emitted problem carries only
    the literal token ``$modal_system_D`` in the logic-spec line, never a
    bare relation symbol named "D" anywhere (this exporter has no relation
    symbols at all -- NXF's box/dia connectives are not rendered as an
    explicit accessibility relation the way fol.qml's shallow embedding
    renders R(w,v)), so there is no textual collision to guard against
    beyond the token itself being exactly ``$modal_system_D``."""
    text = to_tptp_ncl(Implies(Diamond(p), Implies(Box(Not(p)), Diamond(p))), frame="D")
    assert "$modalities == $modal_system_D ] )." in text
    # No bare, undeclared "D" relation symbol appears anywhere in the text.
    assert " D(" not in text and ",D," not in text and "\nD:" not in text


def test_repeated_atom_gets_one_type_declaration():
    """p ∧ p uses the SAME propositional letter twice — the type-declaration
    loop dedupes by first occurrence, so exactly ONE ``p: $o`` statement is
    emitted, not two (a duplicate ``type`` statement for the same name is
    rejected by TPTP-family parsers as a re-declaration)."""
    text = to_tptp_ncl(And(p, p))
    assert text.count(",type,") == 1
    assert text.count("p: $o") == 1


# ---------------------------------------------------------------------------
# Error contracts
# ---------------------------------------------------------------------------

def test_unknown_frame_raises_value_error():
    with pytest.raises(ValueError, match="frame"):
        to_tptp_ncl(Box(p), frame="B")  # B is a real modal system elsewhere, but
                                         # not one this exporter is wired for


def test_unknown_domains_raises_value_error():
    with pytest.raises(ValueError, match="domains"):
        to_tptp_ncl(Box(p), domains="nonsense")


def test_non_alethic_modal_family_raises_not_implemented():
    """Knows_a (epistemic) is out of scope: it needs the INDEXED long-form
    connective ({$knows(#a)} @ (...), confirmed by PUZ087_1.p), not the
    unindexed short form [.]/<.> this exporter emits."""
    formula = Knows("alice", p)
    with pytest.raises(NotImplementedError):
        to_tptp_ncl(formula)


def test_function_term_argument_raises_not_implemented():
    """P(f(x)) is out of scope: a genuine NXF function-SYMBOL type
    declaration was never confirmed against a real file (see module
    docstring 'Scope') -- refused by name rather than guessed."""
    from unicode_fol_kit.fol.nodes import Function
    formula = Box(Atom("P", (Function("f", (Variable("x"),)),)))
    with pytest.raises(NotImplementedError, match="function"):
        to_tptp_ncl(Quantifier("∀", Variable("x"), formula))


# ---------------------------------------------------------------------------
# Quantified fragment: native NXF quantifiers + non-nullary atoms (new in
# this release). Golden-text hand-checked against
# ProblemBuilding/QMLTP/7_QMLTPTP/SYM/SYM001_1.p and .../APM/APM002_1.p of
# the cloned github.com/TPTPWorld/NonClassicalLogic corpus -- see module
# docstring 'Sources'.
# ---------------------------------------------------------------------------

def test_barcan_scheme_export_matches_real_qmltp_translation():
    """Box-Barcan ∀x □f(x) → □∀x f(x), the exact formula QMLTP's SYM001+1.p
    states (see tests/test_qmltp_input.py, which reads that file), rendered
    with this exporter's default frame="K"/domains="constant". Hand-checked
    against the REAL professionally-produced NXF translation of the very
    same problem, ``ProblemBuilding/QMLTP/7_QMLTPTP/SYM/SYM001_1.p``:

        tff(k_constant_rigid,logic,
            $modal ==
              [ $domains == $constant, $designation == $rigid,
                $terms == $local, $modalities == $modal_system_K ] ).
        tff(f_decl,type, f: $i > $o ).
        tff(con,conjecture,
            ( ! [X: $i] : ( {$box} @ (f(X)) )
           => ( {$box} @ (! [X: $i] : f(X)) ) ) ).

    modulo two INTENTIONAL, already-verified differences from that file
    (not bugs): (1) this module uses the SHORT modal connective form
    ``[.]``/``<.>`` throughout (both are defined equivalent by the arXiv
    paper Sec. 5: ``{$box}@(p)`` can be written ``[.] p``), matching the
    EXISTING, already-tested propositional-fragment convention rather than
    switching forms only for the quantified case; (2) ``$terms == $global``
    rather than ``$local`` -- an existing, pre-this-release choice (see
    ``to_tptp_ncl``'s own docstring point 1), unrelated to the quantifier
    work here.
    """
    from unicode_fol_kit.fol.nodes import Quantifier as Q
    x = Variable("x")
    f = lambda t: Atom("F", [t])
    formula = Implies(Q("∀", x, Box(f(x))), Box(Q("∀", x, f(x))))

    text = to_tptp_ncl(formula, frame="K", conjecture_name="con")

    expected = (
        "tff(con_logic,logic,\n"
        "    $modal ==\n"
        "      [ $domains == $constant,\n"
        "        $designation == $rigid,\n"
        "        $terms == $global,\n"
        "        $modalities == $modal_system_K ] ).\n"
        "\n"
        "tff(f_decl,type,\n"
        "    f: $i > $o ).\n"
        "\n"
        "tff(con,conjecture,\n"
        "    (! [X: $i] : ([.] f(X)) => [.] ! [X: $i] : (f(X))) ).\n"
    )
    assert text == expected


def test_existential_quantifier_renders_question_mark():
    """? [X: $i] : (...) for ∃ -- the dual of the ! [X: $i] case above,
    hand-checked the same way (SYM003+1.p's own shape: ◇∃x f(x) → ∃x ◇f(x))."""
    from unicode_fol_kit.fol.nodes import Quantifier as Q
    x = Variable("x")
    f = lambda t: Atom("F", [t])
    formula = Implies(Diamond(Q("∃", x, f(x))), Q("∃", x, Diamond(f(x))))

    text = to_tptp_ncl(formula, conjecture_name="cbf")
    assert "(<.> ? [X: $i] : (f(X)) => ? [X: $i] : (<.> f(X)))" in text
    assert "tff(f_decl,type,\n    f: $i > $o ).\n" in text


def test_sorted_quantifier_declares_custom_tType_and_default_i_gets_none():
    """A SortedQuantifier's sort gets its own $tType declaration
    (tff(human_type,type, human: $tType ).), matching PUZ087_1.p's
    ``tff(agent_type,type,wiseman: $tType).`` pattern -- while a MIXED
    formula's untyped quantifier still uses $i with NO declaration for it
    (confirmed: TPTP's own built-in type, never user-declared -- see
    module docstring / _DEFAULT_SORT)."""
    from unicode_fol_kit.fol.nodes import SortedQuantifier
    x, y = Variable("x"), Variable("y")
    human_p = SortedQuantifier("∀", x, "Human", Atom("P", [x]))
    plain_q = Quantifier("∃", y, Atom("Q", [y]))
    formula = Box(Implies(human_p, plain_q))

    text = to_tptp_ncl(formula)

    assert "tff(human_type,type,\n    human: $tType ).\n" in text
    assert text.count("$tType") == 1  # only ONE $tType decl -- $i (the plain
                                        # quantifier's sort) never gets one
    assert "! [X: human] : (p(X))" in text
    assert "? [Y: $i] : (q(Y))" in text
    assert "tff(p_decl,type,\n    p: human > $o ).\n" in text
    assert "tff(q_decl,type,\n    q: $i > $o ).\n" in text


def test_free_constant_gets_explicit_declaration():
    """A free constant (not a quantified variable) is ALWAYS declared
    explicitly, even at the default sort $i -- confirmed by APM002_1.p's
    ``tff(a_decl,type, a: $i ).`` for its bare constants a/b/c. This is
    genuinely surprising if you only look at variables (which need no such
    separate declaration, the sort is inline in the quantifier) -- hence a
    dedicated hand-checked test rather than folding it into another one."""
    from unicode_fol_kit.fol.nodes import Constant
    a = Constant("a")
    formula = Box(Atom("P", [a]))

    text = to_tptp_ncl(formula, conjecture_name="c1")

    assert "tff(a_decl,type,\n    a: $i ).\n" in text
    assert "tff(p_decl,type,\n    p: $i > $o ).\n" in text
    assert "[.] p(a)" in text


def test_sorted_constant_gets_its_own_sort_declaration():
    """A SortedConstant gets declared at its OWN sort, and that sort itself
    gets a $tType declaration -- the term-level counterpart of
    test_sorted_quantifier_declares_custom_tType_and_default_i_gets_none,
    mirroring PUZ087_1.p's ``a: wiseman`` (a constant of a user sort)."""
    from unicode_fol_kit.fol.nodes import SortedConstant
    alice = SortedConstant("alice", "Human")
    formula = Box(Atom("P", [alice]))

    text = to_tptp_ncl(formula)

    assert "tff(human_type,type,\n    human: $tType ).\n" in text
    assert "tff(alice_decl,type,\n    alice: human ).\n" in text
    assert "[.] p(alice)" in text


def test_two_ary_predicate_declares_star_product_domain():
    """A 2-ary predicate's type is ``(s1 * s2) > $o`` -- the TFF product-type
    shape (fol/tptp_input.py's own ``tff_xprod`` grammar rule), hand-checked
    against a genuinely 2-ary atom over two DIFFERENT sorts."""
    from unicode_fol_kit.fol.nodes import SortedQuantifier
    x, y = Variable("x"), Variable("y")
    formula = Box(SortedQuantifier(
        "∀", x, "Person",
        SortedQuantifier("∃", y, "Place", Atom("Visits", [x, y]))))

    text = to_tptp_ncl(formula)
    assert "tff(visits_decl,type,\n    visits: (person * place) > $o ).\n" in text
    assert "! [X: person] : (? [Y: place] : (visits(X,Y)))" in text


def test_predicate_used_at_two_sorts_is_refused():
    """The SAME predicate name P applied once under sort Human and once
    under sort Animal is a genuine TPTP type conflict (one symbol, two
    incompatible declarations) -- refused rather than emitting two
    colliding tff(p_decl,...) statements."""
    from unicode_fol_kit.fol.nodes import SortedQuantifier
    x = Variable("x")
    formula = And(
        SortedQuantifier("∀", x, "Human", Atom("P", [x])),
        SortedQuantifier("∀", x, "Animal", Atom("P", [x])))
    with pytest.raises(NotImplementedError, match="different"):
        to_tptp_ncl(formula)


def test_sort_name_colliding_with_predicate_name_is_refused():
    """A sort and a predicate that fold to the SAME NXF identifier (TPTP's
    single flat lower_word namespace) would need the same name declared
    twice, at two different meanings ($tType vs. > $o) -- refused."""
    from unicode_fol_kit.fol.nodes import SortedQuantifier
    x = Variable("x")
    formula = SortedQuantifier("∀", x, "Foo", Atom("Foo", []))
    with pytest.raises(NotImplementedError, match="namespace"):
        to_tptp_ncl(formula)


def test_distinct_sort_names_folding_to_same_token_are_refused():
    """Soundness guard (found by adversarial review, mirroring the existing
    Px/px atom-collision guard -- test_to_tptp_ncl_refuses_case_colliding_letters
    -- for SORTS): tptp_fold_first_letter only lower-cases the FIRST
    character, so the two DISTINCT kit sort names 'Human' and 'human' both
    fold to the NXF identifier 'human'. Before this guard, the exporter
    silently merged them into ONE 'tff(human_type,type, human: $tType ).'
    declaration and typed BOTH predicates over that single merged sort --
    genuinely losing the fact that the source formula uses two different
    sorts. Reachable only via directly-constructed SortedQuantifier nodes
    (both of the kit's own parsers always capitalise a sort's first letter
    on import), the same reachability bar as the already-fixed atom case.
    """
    from unicode_fol_kit.fol.nodes import SortedQuantifier
    x, y = Variable("x"), Variable("y")
    formula = Box(And(
        SortedQuantifier("∀", x, "Human", Atom("P", [x])),
        SortedQuantifier("∀", y, "human", Atom("Q", [y]))))
    with pytest.raises(NotImplementedError, match="alias"):
        to_tptp_ncl(formula)


# ---------------------------------------------------------------------------
# Built-in atoms (=, ≠, <, >, ≤, ≥) and Number literals (found by adversarial
# review): native TFF/NXF types are disjoint with no subtyping/coercion, so
# equality/disequality needs both operands at ONE sort, and neither the
# arithmetic comparisons nor a bare Number literal can be expressed without
# an arithmetic sort ($int/$rat/$real) this exporter never declares --
# mirrors atp.tptp_tff's identical TF0-only refusal of the same constructs
# (see that module's _ARITH_OUT_OF_SCOPE / test_tptp_tff.py).
# ---------------------------------------------------------------------------

def test_cross_sort_equality_is_refused():
    """alice: Human = bob: $i (the DEFAULT sort) is meaningful under the
    kit's own guard-predicate SortedQuantifier semantics (both sides are
    just individuals of the one shared classical domain -- see
    fol._msfl_nodes.SortedQuantifier._relativize) but native TFF's '=' has
    NO subtyping/coercion between 'human' and '$i': a TFF-conformant type
    checker must reject 'alice = bob' if 'alice: human' and 'bob: $i'.
    Refused rather than emitting the type-incorrect problem."""
    from unicode_fol_kit.fol.nodes import Constant, SortedConstant
    formula = Box(Atom("=", [SortedConstant("alice", "Human"), Constant("bob")]))
    with pytest.raises(NotImplementedError, match="human.*\\$i|\\$i.*human"):
        to_tptp_ncl(formula)


def test_same_sort_equality_is_accepted():
    """The positive control for test_cross_sort_equality_is_refused: two
    SortedConstants at the SAME sort render exactly like any other equality
    -- infix '=', no separate type declaration for '=' itself, both
    constants declared at their shared sort 'human'. Hand-checked: this is
    a perfectly well-typed TFF equality (one shared declared type on both
    sides), so it must NOT be refused."""
    from unicode_fol_kit.fol.nodes import SortedConstant
    formula = Box(Atom("=", [SortedConstant("alice", "Human"), SortedConstant("bob", "Human")]))
    text = to_tptp_ncl(formula, conjecture_name="eq")
    assert "tff(human_type,type,\n    human: $tType ).\n" in text
    assert "tff(alice_decl,type,\n    alice: human ).\n" in text
    assert "tff(bob_decl,type,\n    bob: human ).\n" in text
    assert ",type,\n    = " not in text and "tff(eq_decl" not in text  # no decl for "="
    assert "[.] (alice = bob)" in text


@pytest.mark.parametrize("op", ["<", ">", "≤", "≥"])
def test_arithmetic_comparison_predicate_is_refused(op):
    """<, >, ≤, ≥ are TPTP's $less/$greater/$lesseq/$greatereq dollar-word
    predicates -- they need an arithmetic sort ($int/$rat/$real) that this
    exporter never declares (mirrors atp.tptp_tff's identical refusal of
    the same four predicates -- see that module's _ARITH_OUT_OF_SCOPE), so
    applying one to two $i-typed variables (as the previous version of this
    exporter silently did) would emit ill-typed NXF/TFF text: $greater
    needs $int/$rat/$real operands, not $i."""
    x, y = Variable("x"), Variable("y")
    formula = Quantifier("∀", x, Quantifier("∀", y, Box(Atom(op, [x, y]))))
    with pytest.raises(NotImplementedError, match="arithmetic"):
        to_tptp_ncl(formula)


def test_number_argument_is_refused():
    """A bare TPTP numeral (e.g. '42') is intrinsically typed to an
    arithmetic sort by the TPTP standard itself, never to $i -- the
    previous version of this exporter defaulted a Number argument to $i
    unconditionally, which is type-incorrect (a numeral is not an
    individual of the untyped sort). Refused rather than mistyped."""
    from unicode_fol_kit.fol.nodes import Number
    formula = Box(Atom("P", [Number(42)]))
    with pytest.raises(NotImplementedError, match="numeral"):
        to_tptp_ncl(formula)


def test_free_variable_is_refused():
    """A Variable with no enclosing Quantifier/SortedQuantifier (found by
    adversarial review) must be refused, not silently typed $i: the
    previous version of _term_sort defaulted an unbound Variable to $i via
    scope.get(term.name, _DEFAULT_SORT), so to_tptp_ncl(Atom("P",
    [Variable("x")])) returned successfully with a genuinely free 'X' in
    the conjecture body and NO declaration/binder anywhere in the text.
    That is not merely under-typed -- TPTP reads a free variable in a
    conjecture role as EXISTENTIALLY quantified (not universally, the
    reading a caller who forgot a binder would plausibly have intended),
    so the previous behaviour silently changed the meaning of the exported
    problem. Reproduces the reviewer's exact repro against the public
    entry point (empty initial scope)."""
    formula = Atom("P", [Variable("x")])
    with pytest.raises(NotImplementedError, match="x"):
        to_tptp_ncl(formula)


def test_free_variable_inside_bound_scope_of_a_different_variable_is_refused():
    """A quantifier binds ONLY its own variable -- a second, distinct free
    variable appearing in the same atom must still be refused even though
    the atom is nested under a Quantifier, because 'scope' only ever grows
    to include variables an ENCLOSING binder actually introduced (see
    _render's SortedQuantifier/Quantifier branch: new_scope adds exactly
    one name). Guards against a fix that accidentally treats "some scope is
    non-empty" as sufficient rather than checking the SPECIFIC variable."""
    x, y = Variable("x"), Variable("y")
    formula = Quantifier("∀", x, Box(Atom("R", [x, y])))
    with pytest.raises(NotImplementedError, match="y"):
        to_tptp_ncl(formula)


def test_free_variable_as_equality_operand_is_refused():
    """The same free-variable refusal must apply on the equality/disequality
    path (_term_sort is called directly on both operands in _render's
    equality branch, before the cross-sort check), not only on the general
    predicate-argument path -- otherwise 'x = a' with an unbound x would
    slip through as a same-sort ($i = $i) equality with a free variable
    still left in the emitted text."""
    from unicode_fol_kit.fol.nodes import Constant
    formula = Box(Atom("=", [Variable("x"), Constant("a")]))
    with pytest.raises(NotImplementedError, match="x"):
        to_tptp_ncl(formula)


def test_quantified_round_trips_through_tptp_input_formula_reader():
    """Faithfulness check: the NATIVE-quantifier/typed-atom fragment this
    release adds is, once the modal wrapper is stripped, exactly a plain
    TFF quantified formula -- fol.tptp_input's OWN reader (unrelated to
    this exporter, already independently tested) can parse the emitted
    conjecture body straight back out, and recover a formula EQUAL to the
    one this test started from. This is the round-trip the task batch
    notes ask for ('round trip through the kit's own NXF/TPTP reader where
    one exists') -- no reader for the MODAL extensions ([.]/<.> or a
    $modal logic-spec) exists anywhere in the kit, so this checks the
    quantifier/typed-atom half, which does have one.
    """
    from unicode_fol_kit.fol.nodes import SortedQuantifier
    from unicode_fol_kit.fol.tptp_input import parse_tptp_formula

    x, y = Variable("x"), Variable("y")
    original = SortedQuantifier(
        "∀", x, "Person",
        Implies(Atom("Happy", [x]),
                SortedQuantifier("∃", y, "Person", Atom("Knows", [x, y]))))

    text = to_tptp_ncl(original, conjecture_name="rt")
    # Extract the bare conjecture body (strip the "tff(rt,conjecture,\n    "
    # prefix and the " ).\n" suffix this exporter always emits).
    marker = "tff(rt,conjecture,\n    "
    assert text.endswith(" ).\n")
    body_text = text[text.index(marker) + len(marker):-len(" ).\n")]

    reparsed = parse_tptp_formula(body_text)
    assert reparsed == original


def test_function_free_equality_round_trips_and_excludes_from_decls():
    """Equality (=) is TPTP's own built-in infix predicate -- it must never
    get its own tff(..._decl,type,...) statement (that would be an illegal
    re-declaration of a built-in), while the CONSTANTS either side of it
    still get theirs, and equality's own inherited fol.tptp_input round
    trip (both are '=' -- the exact mirror of _fol_nodes.Atom's own
    to_tptp() equality handling) still works end to end."""
    from unicode_fol_kit.fol.nodes import Constant
    from unicode_fol_kit.fol.tptp_input import parse_tptp_formula

    a, b = Constant("a"), Constant("b")
    original = Box(Atom("=", [a, b]))

    text = to_tptp_ncl(original, conjecture_name="eq")
    assert ",type,\n    = " not in text and "tff(eq_decl" not in text  # no decl for "="
    assert "tff(a_decl,type,\n    a: $i ).\n" in text
    assert "tff(b_decl,type,\n    b: $i ).\n" in text

    marker = "tff(eq,conjecture,\n    "
    body_text = text[text.index(marker) + len(marker):-len(" ).\n")]
    # body_text is "[.] (a = b)" -- strip this exporter's own [.] short form
    # (fol.tptp_input has no reader for it) before round-tripping the
    # classical equality atom underneath.
    assert body_text.startswith("[.] ")
    reparsed = parse_tptp_formula(body_text[len("[.] "):])
    assert reparsed == Atom("=", [a, b])


# ---------------------------------------------------------------------------
# Leo3Backend: discovery (no binary, no subprocess)
# ---------------------------------------------------------------------------

def test_leo3_unavailable_without_env_or_java(monkeypatch):
    monkeypatch.delenv("UFK_LEO3", raising=False)
    monkeypatch.setattr("shutil.which", lambda name: None)
    assert Leo3Backend().available() is False


def test_leo3_unavailable_with_env_but_no_java(monkeypatch, tmp_path):
    fake_jar = tmp_path / "leo3.jar"
    monkeypatch.setenv("UFK_LEO3", str(fake_jar))
    monkeypatch.setattr("shutil.which", lambda name: None)
    assert Leo3Backend().available() is False


def test_leo3_unavailable_with_java_but_no_env(monkeypatch):
    monkeypatch.delenv("UFK_LEO3", raising=False)
    monkeypatch.setattr("shutil.which", lambda name: "/usr/bin/java" if name == "java" else None)
    assert Leo3Backend().available() is False


def test_leo3_available_with_both(monkeypatch, tmp_path):
    fake_jar = tmp_path / "leo3.jar"
    monkeypatch.setenv("UFK_LEO3", str(fake_jar))
    monkeypatch.setattr("shutil.which", lambda name: "/usr/bin/java" if name == "java" else None)
    assert Leo3Backend().available() is True


def test_leo3_decide_raises_backend_unavailable(monkeypatch):
    """decide() re-checks discovery itself (in case it is called directly,
    bypassing atp.protocol.run_backend's own availability gate) and raises
    BackendUnavailable rather than letting a bare FileNotFoundError escape."""
    monkeypatch.delenv("UFK_LEO3", raising=False)
    with pytest.raises(BackendUnavailable):
        Leo3Backend().decide(Box(p))


def test_leo3_decide_unsupported_fragment_never_spawns_subprocess(monkeypatch, tmp_path):
    """A formula outside to_tptp_ncl's fragment (here: epistemic Knows) comes
    back UNKNOWN/unsupported WITHOUT ever calling subprocess.run — the NXF
    translation failure is caught before any process is spawned."""
    fake_jar = tmp_path / "leo3.jar"
    monkeypatch.setenv("UFK_LEO3", str(fake_jar))
    monkeypatch.setattr("shutil.which", lambda name: "/usr/bin/java" if name == "java" else None)

    def _boom(*a, **kw):
        raise AssertionError("subprocess.run must not be called for an unsupported formula")
    monkeypatch.setattr(subprocess, "run", _boom)

    verdict = Leo3Backend().decide(Knows("alice", p))
    assert verdict.status == UNKNOWN
    assert verdict.reason == "unsupported"
    assert verdict.logic == "modal"


def test_leo3_decide_no_szs_line_is_error(monkeypatch, tmp_path):
    """Output with no '% SZS status' line at all is an infrastructure surprise
    (ERROR/infra), not a decided UNKNOWN — Leo-III printed SOMETHING, just not
    in the expected form (e.g. a CLI usage error)."""
    fake_jar = tmp_path / "leo3.jar"
    monkeypatch.setenv("UFK_LEO3", str(fake_jar))
    monkeypatch.setattr("shutil.which", lambda name: "/usr/bin/java" if name == "java" else None)

    class _FakeResult:
        stdout = "usage: leo3 <file> [options]\n"
        stderr = ""
    monkeypatch.setattr(subprocess, "run", lambda *a, **kw: _FakeResult())

    verdict = Leo3Backend().decide(Box(p))
    assert verdict.status == "error"
    assert verdict.reason == "infra"
    assert "usage" in verdict.detail


def test_leo3_decide_theorem_is_proved(monkeypatch, tmp_path):
    """A canned 'SZS status Theorem' output maps to PROVED via the shared
    atp.tstp reader with query='conjecture' (the problem carries exactly one
    conjecture-role formula, never a bare clause set) — pins the wiring
    between this backend and atp.tstp without needing a real prover."""
    fake_jar = tmp_path / "leo3.jar"
    monkeypatch.setenv("UFK_LEO3", str(fake_jar))
    monkeypatch.setattr("shutil.which", lambda name: "/usr/bin/java" if name == "java" else None)

    class _FakeResult:
        stdout = "% SZS status Theorem for problem\n"
        stderr = ""
    monkeypatch.setattr(subprocess, "run", lambda *a, **kw: _FakeResult())

    verdict = Leo3Backend().decide(Implies(Box(Implies(p, q)), Implies(Box(p), Box(q))))
    assert verdict.status == PROVED
    assert verdict.szs_status == "Theorem"
    assert verdict.logic == "modal"


def test_leo3_decide_uses_jar_invocation(monkeypatch, tmp_path):
    """$UFK_LEO3 ending in .jar is invoked as `java -jar <jar> <file> -t <sec>`.

    Stubs the K axiom (hand-checked K-valid: modal_decide(k_axiom, frame='K')
    == 'valid', same formula as test_theorem_confirmed_by_tableau_is_proved
    below) rather than a bare Box(p) — Box(p) is NOT K-valid, so since the
    mandatory modal-tableau cross-check (this module's docstring) the real
    tableau would refute a stubbed 'Theorem' for it and this test would
    silently exercise the SOUNDNESS ALARM branch instead of a plain PROVED,
    without either the command-shape assertions below or a status check
    noticing. The explicit status assertion guards against exactly that."""
    fake_jar = tmp_path / "leo3.jar"
    monkeypatch.setenv("UFK_LEO3", str(fake_jar))
    monkeypatch.setattr("shutil.which", lambda name: "/usr/bin/java" if name == "java" else None)

    captured = {}

    class _FakeResult:
        stdout = "% SZS status Theorem for problem\n"
        stderr = ""

    def _fake_run(command, **kw):
        captured["command"] = command
        return _FakeResult()
    monkeypatch.setattr(subprocess, "run", _fake_run)

    k_axiom = Implies(Box(Implies(p, q)), Implies(Box(p), Box(q)))
    verdict = Leo3Backend().decide(k_axiom, timeout=5000)
    assert verdict.status == PROVED
    command = captured["command"]
    assert command[0] == "/usr/bin/java"
    assert command[1] == "-jar"
    assert command[2] == str(fake_jar)
    assert command[4] == "-t"
    assert command[5] == "5"  # 5000ms -> 5s


def test_leo3_decide_uses_wrapper_invocation_when_not_jar(monkeypatch, tmp_path):
    """$UFK_LEO3 NOT ending in .jar is invoked directly (no `java -jar` prefix)
    — the 'executable wrapper' discovery path.

    Stubs the K axiom (hand-checked K-valid, see
    test_leo3_decide_uses_jar_invocation above for why not a bare Box(p))
    plus an explicit status assertion so the mandatory modal-tableau
    cross-check confirms rather than alarms here."""
    fake_wrapper = tmp_path / "leo3"
    monkeypatch.setenv("UFK_LEO3", str(fake_wrapper))
    monkeypatch.setattr("shutil.which", lambda name: "/usr/bin/java" if name == "java" else None)

    captured = {}

    class _FakeResult:
        stdout = "% SZS status Theorem for problem\n"
        stderr = ""

    def _fake_run(command, **kw):
        captured["command"] = command
        return _FakeResult()
    monkeypatch.setattr(subprocess, "run", _fake_run)

    k_axiom = Implies(Box(Implies(p, q)), Implies(Box(p), Box(q)))
    verdict = Leo3Backend().decide(k_axiom)
    assert verdict.status == PROVED
    command = captured["command"]
    assert command[0] == str(fake_wrapper)
    assert "-jar" not in command


# ---------------------------------------------------------------------------
# Leo3Backend: the mandatory modal-tableau cross-check (mirrors nanocop's
# soundness-alarm policy — see leo3_backend.py's module docstring). The
# real, in-kit modal-tableau backend runs for every case below (never
# mocked); only Leo-III's own subprocess output is stubbed.
# ---------------------------------------------------------------------------

@pytest.fixture()
def leo3_stub(monkeypatch, tmp_path):
    """Discovery satisfied + subprocess.run stubbed to return whatever SZS
    line the test puts in ``holder["stdout"]`` (default: 'Theorem')."""
    fake_jar = tmp_path / "leo3.jar"
    monkeypatch.setenv("UFK_LEO3", str(fake_jar))
    monkeypatch.setattr("shutil.which", lambda name: "/usr/bin/java" if name == "java" else None)

    holder = {"stdout": "% SZS status Theorem for problem\n", "stderr": ""}

    class _FakeResult:
        pass

    def _fake_run(*a, **kw):
        result = _FakeResult()
        result.stdout = holder["stdout"]
        result.stderr = holder["stderr"]
        return result
    monkeypatch.setattr(subprocess, "run", _fake_run)
    return holder


def test_theorem_confirmed_by_tableau_is_proved(leo3_stub):
    """The K axiom is genuinely K-valid (hand-checked: modal_decide(k_axiom,
    frame='K') == 'valid', see modal_tableau's own soundness/completeness
    for propositional K). Leo-III's stubbed 'Theorem' agrees with the REAL
    modal-tableau cross-check → PROVED, 'confirmed' recorded in detail."""
    formula = Implies(Box(Implies(p, q)), Implies(Box(p), Box(q)))
    verdict = Leo3Backend().decide(formula)  # default frame K
    assert verdict.status == PROVED
    assert "cross-check modal-tableau: confirmed" in verdict.detail
    assert verdict.countermodel is None


def test_theorem_contradicted_by_tableau_is_a_soundness_alarm(leo3_stub):
    """◇p → □p is NOT K-valid (hand-checked: a 2-successor branching world
    falsifies it — modal_decide(..., frame='K') == 'invalid', confirmed
    against the real tableau below). Forcing Leo-III to claim 'Theorem' for
    it must raise the soundness alarm rather than answer PROVED."""
    formula = Implies(Diamond(p), Box(p))
    verdict = Leo3Backend().decide(formula)  # default frame K
    assert verdict.status == "error"
    assert verdict.reason == "infra"
    assert "SOUNDNESS ALARM" in verdict.detail
    assert "leo3 says Theorem but modal-tableau" in verdict.detail


def test_nontheorem_contradicted_by_tableau_is_the_symmetric_alarm(leo3_stub):
    """◇□p → □p IS S5-valid (hand-checked: S5's modal reduction laws collapse
    any operator string to its last operator, so ◇□p ≡ □p there; confirmed
    against the real tableau: modal_decide(..., frame='S5') == 'valid').
    Forcing Leo-III to claim 'CounterSatisfiable' (Non-Theorem) for it must
    raise the SYMMETRIC alarm — the direction nanocop's undecidable FO
    fragment cannot build, but Leo-III's decidable propositional fragment
    can (modal-tableau fully decides it)."""
    leo3_stub["stdout"] = "% SZS status CounterSatisfiable for problem\n"
    formula = Implies(Diamond(Box(p)), Box(p))
    verdict = Leo3Backend().decide(formula, frame="S5")
    assert verdict.status == "error"
    assert verdict.reason == "infra"
    assert "SOUNDNESS ALARM" in verdict.detail
    assert "leo3 says Non-Theorem but modal-tableau" in verdict.detail


def test_nontheorem_confirmed_by_tableau_is_refuted_with_countermodel(leo3_stub):
    """□p → □□p (the 4 axiom) is NOT T-valid (hand-checked: T is reflexive
    but not transitive, so a 2-step non-transitive chain falsifies it;
    confirmed against the real tableau: modal_decide(..., frame='T') ==
    'invalid'). Leo-III's stubbed 'CounterSatisfiable' agrees → REFUTED,
    with the tableau's OWN verified Kripke witness attached as the
    certificate — independently re-checked here via satisfies_modal rather
    than trusted blind."""
    leo3_stub["stdout"] = "% SZS status CounterSatisfiable for problem\n"
    formula = Implies(Box(p), Box(Box(p)))
    verdict = Leo3Backend().decide(formula, frame="T")
    assert verdict.status == REFUTED
    assert "cross-check modal-tableau: confirmed" in verdict.detail
    assert verdict.countermodel is not None
    assert verdict.countermodel["kind"] == "kripke"

    model = kripke_model_from_dict(verdict.countermodel["data"])
    assert satisfies_modal(formula, model, 0) is False


def test_cross_check_infra_failure_does_not_mask_theorem(leo3_stub, monkeypatch):
    """The cross-check is best-effort infrastructure (mirrors nanocop's
    _cross_check docstring): if modal-tableau's OWN lookup blows up, that
    must not mask Leo-III's answer — only a genuine tableau DISAGREEMENT
    may. PROVED is kept, with 'inconclusive' (not 'confirmed') recorded."""
    import unicode_fol_kit.atp.protocol as protocol

    def _boom(name):
        raise RuntimeError("modal-tableau backend exploded")
    monkeypatch.setattr(protocol, "get_backend", _boom)

    formula = Implies(Box(Implies(p, q)), Implies(Box(p), Box(q)))
    verdict = Leo3Backend().decide(formula)
    assert verdict.status == PROVED
    assert "cross-check modal-tableau: inconclusive" in verdict.detail


def test_cross_check_skipped_for_unknown_leo3_verdict(leo3_stub):
    """An UNKNOWN/ERROR Leo-III verdict has nothing definitive to
    cross-check — no 'cross-check' text is added, matching nanocop's own
    'skip on UNKNOWN/ERROR' pattern."""
    leo3_stub["stdout"] = "usage: leo3 <file> [options]\n"
    verdict = Leo3Backend().decide(Box(p))
    assert verdict.status == "error"
    assert verdict.reason == "infra"
    assert "cross-check" not in (verdict.detail or "")


# ---------------------------------------------------------------------------
# Live integration test: skipped unless a real Leo-III is configured.
# ---------------------------------------------------------------------------

@pytest.mark.skipif(
    not os.environ.get("UFK_LEO3"),
    reason="no local Leo-III: set $UFK_LEO3 to a leo3.jar path or wrapper to run this")
def test_leo3_live_k_axiom_is_theorem():
    """The K axiom, □(p→q)→(□p→□q), is a theorem of every normal modal logic
    (in particular K itself) — this is the canonical smoke test for an
    NXF-speaking prover's modal mode actually working end to end."""
    formula = Implies(Box(Implies(p, q)), Implies(Box(p), Box(q)))
    verdict = Leo3Backend().decide(formula, frame="K")
    assert verdict.status == PROVED, verdict.detail


def test_to_tptp_ncl_refuses_case_colliding_letters():
    """Soundness guard (found by adversarial review): Atom.to_tptp folds only
    an atom identifier's FIRST character to lower-case (not the whole
    string — see fol/_fol_nodes.py's tptp_fold_first_letter), so the
    DISTINCT kit letters 'Px' and 'px' still both render as 'px' — the
    genuinely INVALID formula Px → px would silently export as the
    tautology (px => px) and any NXF prover would 'prove' it. The export
    must refuse instead of aliasing.

    Built directly via the ``Atom`` constructor rather than
    ``MSFLParser().parse(...)``: the Unicode grammar's PREDICATE token
    forces every parsed atom name to start upper-case
    (``[A-Z][a-zA-Z0-9]*``), so two parser-produced atoms can never collide
    under a first-letter-only fold — only a directly-constructed atom name
    (as e.g. :mod:`unicode_fol_kit.chem.mol` builds, bypassing the grammar)
    can start lower-case and reproduce the collision.
    """
    from unicode_fol_kit.atp.tptp_ncl import to_tptp_ncl
    from unicode_fol_kit.fol.nodes import Atom as _Atom, Implies as _Implies

    px_upper = _Atom("Px", ())
    px_lower = _Atom("px", ())
    assert px_upper != px_lower                      # genuinely distinct atoms
    assert px_upper.to_tptp() == px_lower.to_tptp() == "px"  # both fold to 'px'
    with pytest.raises(NotImplementedError, match="alias"):
        to_tptp_ncl(_Implies(px_upper, px_lower))
