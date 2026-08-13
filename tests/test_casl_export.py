"""Tests for :mod:`unicode_fol_kit.fol.casl_export` (CASL text emission for
classical FOL and many-sorted FOL).

No snapshot tests: every expected string below is derived BY HAND against the
module's stated emission rules (see its module docstring) in each test's own
docstring/comment — not by running the code and copying its output. Where a
formula is expressible in the kit's own Unicode syntax it is built with
:class:`~unicode_fol_kit.MSFLParser` (plain ``MSFLParser()`` for
unsorted-classical FOL, ``MSFLParser(many_sorted=True)`` for MSFOL — a
constant is UNSORTED (:class:`~unicode_fol_kit.fol.nodes.Constant`) only in
the former mode; the latter requires every constant to carry an explicit
``name:Sort`` annotation, producing :class:`SortedConstant`). Where no single
parser mode can produce the exact tree needed (mixing a many-sorted quantifier
with a deliberately UNSORTED constant in one formula, to demonstrate sort
inference actually inferring something rather than reading off an existing
annotation, or building a node from an out-of-fragment class), the AST is
built directly, per the task's own guidance.

Grammar facts relied on below (checked directly against
unicode_fol_kit/fol/grammars/terminals.lark and confirmed interactively):
  * VARIABLE is /[a-z][0-9]*/ — a single lowercase letter, optionally
    followed by digits (so 'a1' is a VARIABLE, not a constant name).
  * NAME (a bare constant/function identifier) needs at least two letters,
    so ordinary words like 'alice', 'socrates', 'mother' are constants/
    functions and single letters are always variables.
  * A quantifier's grammar production is '(FORALL|EXISTS) VARIABLE prefix',
    i.e. it binds only a 'prefix'-level body (an atom, a negation, another
    quantifier, or a PARENTHESISED formula) — so to make a quantifier scope
    over a connective in the *input* text, the connective must be written
    with explicit parens, e.g. '∀x:Person (Mortal(x) → …)'. (This is a fact
    about the kit's OWN input grammar, unrelated to how the CASL OUTPUT is
    parenthesised, which is governed entirely by casl_export's own rules.)
  * 'PREDICATE -> atom0_' is a direct grammar alternative, so a bare
    predicate name (e.g. 'Rain', 'P') parses as a 0-ary Atom.
"""

import pytest

from unicode_fol_kit import MSFLParser
from unicode_fol_kit.fol.casl_export import to_casl_spec, formula_to_casl
from unicode_fol_kit.fol.nodes import (
    Variable, Constant, SortedConstant, Function,
    Atom, Not, And, Or, Xor, Implies, Iff,
    Quantifier, SortedQuantifier,
    Box, Count, Number,
)

FOL = MSFLParser()               # unsorted classical FOL
MSFOL = MSFLParser(many_sorted=True)  # many-sorted FOL


# =============================================================================
# Golden full-spec tests
# =============================================================================

def test_golden_pure_fol_one_sort():
    """Pure (unsorted) classical FOL, default_sort left at its default
    'Thing'. Axioms: modus-ponens shape ∀x (Human(x) → Mortal(x)) plus the
    ground fact Human(socrates); conjecture: Mortal(socrates).

    Hand-derivation:
      * literal_sorts = {'Thing'} — the one plain (unsorted) ∀x contributes
        default_sort.
      * pred_arity: Human -> 1, Mortal -> 1. const_names = {'socrates'}.
      * Union-find: ('pred','Human',0) ~ x's slot 'Thing' (from the first
        axiom's own quantifier); ('pred','Mortal',0) ~ the SAME x's slot
        'Thing' (same axiom, same variable). 'Human(socrates)' unions
        ('pred','Human',0) with ('const','socrates'); the conjecture
        'Mortal(socrates)' unions ('pred','Mortal',0) with the SAME
        ('const','socrates') slot. All four slots end up in one class rooted
        at the concrete string 'Thing' (Human's/Mortal's arg-0 slots were
        already 'Thing' via x; socrates is unioned into that same class via
        both predicates) -> every declaration resolves to 'Thing'.
      * declared_sorts = {'Thing'} (also matches literal_sorts exactly here).
      * ops: only 'socrates : Thing' (alphabetically it's the only entry).
      * preds, alphabetical: 'Human : Thing' then 'Mortal : Thing' (H < M);
        block prefix '  preds ' is 8 chars, so the continuation line is
        indented 8 spaces.
      * Axiom 1's top node is a Quantifier whose body is an Implies (a binary
        connective) -> the body is wrapped: '(Human(x) => Mortal(x))'; each
        side of '=>' is a bare Atom.
      * Axiom 2 and the conjecture are bare atoms at the root -> no parens.
    """
    ax1 = FOL.parse("∀x (Human(x) → Mortal(x))")
    ax2 = FOL.parse("Human(socrates)")
    cj = FOL.parse("Mortal(socrates)")
    expected = (
        "spec KitExport =\n"
        "  sorts Thing\n"
        "  ops socrates : Thing\n"
        "  preds Human : Thing;\n"
        "        Mortal : Thing\n"
        "  . forall x : Thing . (Human(x) => Mortal(x))\n"
        "  . Human(socrates)\n"
        "  . Mortal(socrates) %implied\n"
        "end"
    )
    assert to_casl_spec([ax1, ax2], conjectures=[cj]) == expected


def test_golden_person_animal_msfol_worked_example():
    """The exact many-sorted worked example from the module's own emission
    spec: axiom ∀x:Person (Mortal(x) => ∃y:Animal Likes(x,y)), conjecture
    Mortal(socrates) with socrates a deliberately UNSORTED constant (built
    directly — many_sorted mode cannot parse a bare, unannotated 'socrates').

    Hand-derivation:
      * literal_sorts = {'Person', 'Animal'} (from the two SortedQuantifiers;
        default_sort 'Thing' is never touched since there is no plain
        Quantifier here).
      * pred_arity: Mortal -> 1, Likes -> 2. const_names = {'socrates'}.
      * Union-find: ('pred','Mortal',0) ~ x:Person (axiom's ∀); ('pred',
        'Likes',0) ~ x:Person, ('pred','Likes',1) ~ y:Animal (axiom's ∃).
        The conjecture unions ('pred','Mortal',0) with ('const','socrates'),
        so socrates lands in the SAME class as x, resolving to 'Person'.
      * declared_sorts = {'Animal','Person'} (alphabetical).
      * ops: single entry 'socrates : Person'.
      * preds, alphabetical: 'Likes : Person * Animal' (arg 0 = x = Person,
        arg 1 = y = Animal) then 'Mortal : Person' (L < M).
      * Axiom's root is SortedQuantifier(∀,x,Person, Implies(Mortal(x),
        SortedQuantifier(∃,y,Animal,Likes(x,y)))): root bare -> 'forall x :
        Person . ' + body. Body is an Implies -> quantifier-body rule wraps
        it: '(Mortal(x) => ...)'. Left operand of => is the Atom Mortal(x),
        bare. Right operand is a SortedQuantifier -> a quantifier used as a
        CONNECTIVE operand is wrapped: '(exists y : Animal . Likes(x, y))'.
        Inside that inner quantifier, its own body (Likes(x,y), an Atom)
        stays bare.
      * Conjecture 'Mortal(socrates)' is a bare Atom -> no parens, suffixed
        ' %implied'.
    """
    axiom = MSFOL.parse("∀x:Person (Mortal(x) → (∃y:Animal Likes(x, y)))")
    conjecture = Atom("Mortal", (Constant("socrates"),))
    expected = (
        "spec KitExport =\n"
        "  sorts Animal, Person\n"
        "  ops socrates : Person\n"
        "  preds Likes : Person * Animal;\n"
        "        Mortal : Person\n"
        "  . forall x : Person . (Mortal(x) => (exists y : Animal . Likes(x, y)))\n"
        "  . Mortal(socrates) %implied\n"
        "end"
    )
    assert to_casl_spec([axiom], conjectures=[conjecture]) == expected


def test_golden_empty_axioms_with_only_a_conjecture():
    """axioms=[] is legal as long as conjectures is non-empty. Conjecture:
    ∀x:Person Mortal(x).

    Hand-derivation: literal_sorts={'Person'}; pred_arity Mortal->1;
    ('pred','Mortal',0) ~ x:Person -> Mortal : Person. No ops (no constants/
    functions). No ' . ' axiom lines at all (axioms is empty) — just the one
    conjecture line, suffixed ' %implied'. Root is a SortedQuantifier whose
    body (Mortal(x), an Atom) stays bare -> no parens anywhere.
    """
    cj = MSFOL.parse("∀x:Person Mortal(x)")
    expected = (
        "spec KitExport =\n"
        "  sorts Person\n"
        "  preds Mortal : Person\n"
        "  . forall x : Person . Mortal(x) %implied\n"
        "end"
    )
    assert to_casl_spec([], conjectures=[cj]) == expected


def test_golden_zero_ary_predicate():
    """A single 0-ary predicate, built directly (Atom("Rain", ()) — the
    parser CAN produce this too via the atom0_ grammar alt, but the task
    explicitly calls out direct construction as the intended way to build a
    nullary atom, so it is used here to keep the test self-evidently exact).

    Hand-derivation: no constants, no functions, no quantifiers, and Rain's
    arity is 0 so it contributes no arg sorts -> declared_sorts is EMPTY ->
    the 'sorts' line is omitted entirely (sections appear only if non-empty).
    preds has one entry: 'Rain : ()' (0-ary type marker). The one axiom is
    the bare Atom 'Rain' (no args -> renders as the bare predicate name).
    """
    rain = Atom("Rain", ())
    expected = (
        "spec KitExport =\n"
        "  preds Rain : ()\n"
        "  . Rain\n"
        "end"
    )
    assert to_casl_spec([rain]) == expected


def test_determinism_two_calls_byte_identical():
    """Calling to_casl_spec twice on freshly-parsed, structurally-equal
    input must produce byte-identical text: every collection the emitter
    touches (declared_sorts, op_entries, pred_entries) is explicitly sorted
    before being joined, so there is no set/dict iteration-order
    nondeterminism to leak into the output.
    """
    def build():
        axiom = MSFOL.parse("∀x:Person (Mortal(x) → (∃y:Animal Likes(x, y)))")
        conjecture = Atom("Mortal", (Constant("socrates"),))
        return to_casl_spec([axiom], conjectures=[conjecture])

    assert build() == build()


# =============================================================================
# Sort inference
# =============================================================================

def test_bare_constant_sort_inferred_from_predicate_context():
    """A deliberately UNSORTED constant ('socrates', from plain FOL mode)
    gets its sort inferred purely from appearing in the SAME predicate
    argument position as a sorted variable in ANOTHER axiom — no direct sort
    annotation on socrates anywhere.

    Hand-derivation: axiom1 = ∀x:Person Mortal(x) unions ('pred','Mortal',0)
    with x's slot 'Person'. axiom2 = Mortal(socrates) (plain FOL, socrates
    an unsorted Constant) unions ('pred','Mortal',0) with ('const',
    'socrates'). Transitively, ('const','socrates') ~ 'Person' -> the ops
    entry is 'socrates : Person', and 'Person' also appears in the sorts
    line (already contributed literally by the SortedQuantifier).
    """
    ax1 = MSFOL.parse("∀x:Person Mortal(x)")
    ax2 = FOL.parse("Mortal(socrates)")
    expected = (
        "spec KitExport =\n"
        "  sorts Person\n"
        "  ops socrates : Person\n"
        "  preds Mortal : Person\n"
        "  . forall x : Person . Mortal(x)\n"
        "  . Mortal(socrates)\n"
        "end"
    )
    assert to_casl_spec([ax1, ax2]) == expected


def test_function_argument_and_result_sort_inferred_through_nesting():
    """mother(mother(x)) — the same unary function applied twice — should
    infer BOTH mother's argument sort and its RESULT sort as Person, purely
    from x:Person, by chaining through the function's own result slot.

    Hand-derivation: x:Person (from ∀x:Person). Innermost 'mother(x)':
    unions ('func','mother',0) with x's slot 'Person'; that call's own term
    slot is ('func_result','mother'). Outermost 'mother(mother(x))': unions
    ('func','mother',0) [SAME slot, same function/arity] with the inner
    call's slot ('func_result','mother'). So ('func','mother',0) is unioned
    with BOTH 'Person' (via x) and ('func_result','mother') (via the outer
    call) -> ('func_result','mother') ends up in the SAME class, resolving
    to 'Person' too. Finally 'Alive(mother(mother(x)))' unions
    ('pred','Alive',0) with ('func_result','mother') (the outermost call's
    own slot) -> Alive : Person.
    Declared sorts: just {'Person'}. ops: 'mother : Person -> Person' (one
    arg sort, so no '*', just '->'). preds: 'Alive : Person'.
    """
    ax = MSFOL.parse("∀x:Person Alive(mother(mother(x)))")
    expected = (
        "spec KitExport =\n"
        "  sorts Person\n"
        "  ops mother : Person -> Person\n"
        "  preds Alive : Person\n"
        "  . forall x : Person . Alive(mother(mother(x)))\n"
        "end"
    )
    assert to_casl_spec([ax]) == expected


def test_equality_driven_sort_inference():
    """A bare (unsorted) constant's sort is inferred purely through an
    EQUALITY with a sorted variable: ∀x:Person (x = alice). Built directly —
    no single parser mode can mix a sorted quantifier with a deliberately
    unsorted constant inside one formula (many_sorted mode requires every
    constant to carry its own explicit sort annotation).

    Hand-derivation: the equality atom unions x's slot ('Person') directly
    with ('const','alice') -> alice : Person. declared_sorts = {'Person'}
    (from the SortedQuantifier; also the resolved sort of every declared
    symbol here). No predicates at all (equality is not a user 'preds'
    entry — it is CASL's built-in '='). Root is the SortedQuantifier; its
    body is the equality Atom, which stays bare as a quantifier body (Atom
    never needs wrapping) -> 'forall x : Person . x = alice'.
    """
    formula = SortedQuantifier(
        "∀", Variable("x"), "Person",
        Atom("=", (Variable("x"), Constant("alice"))),
    )
    expected = (
        "spec KitExport =\n"
        "  sorts Person\n"
        "  ops alice : Person\n"
        "  . forall x : Person . x = alice\n"
        "end"
    )
    assert to_casl_spec([formula]) == expected


def test_sorted_constant_consistency_conflict():
    """The SAME constant name annotated with two different sorts across two
    axioms — 'alice:Human' in one, 'alice:Animal' in another — must be
    refused: a symbol has exactly one sort.

    Hand-derivation: axiom1 unions ('const','alice') with 'Human'; axiom2
    unions ('const','alice') with 'Animal'. After axiom1, find(('const',
    'alice')) == 'Human' (a concrete root). Processing axiom2's own
    SortedConstant union first unions ('const','alice') [root 'Human'] with
    'Animal' directly -> both roots are now concrete strings 'Human' !=
    'Animal' -> ValueError naming both.
    """
    ax1 = MSFOL.parse("P(alice:Human)")
    ax2 = MSFOL.parse("Q(alice:Animal)")
    with pytest.raises(ValueError, match="alice"):
        to_casl_spec([ax1, ax2])
    with pytest.raises(ValueError, match="'Human'"):
        to_casl_spec([ax1, ax2])
    with pytest.raises(ValueError, match="'Animal'"):
        to_casl_spec([ax1, ax2])


# =============================================================================
# Conflict / hygiene refusals
# =============================================================================

def test_two_different_sorts_on_one_predicate_position_conflict():
    """Predicate 'Mortal' used at argument 0 with sort Person in one axiom
    and sort Animal in another -> the two axioms disagree about Mortal's
    domain, an unsatisfiable constraint.

    Hand-derivation: ('pred','Mortal',0) is unioned with 'Person' (axiom 1),
    then with 'Animal' (axiom 2); both are already-concrete roots by the
    time the second union runs (axiom 1 fully resolved 'Mortal' arg 0 to
    'Person' first) -> conflict, naming 'Mortal' and both sorts.
    """
    ax1 = MSFOL.parse("∀x:Person Mortal(x)")
    ax2 = MSFOL.parse("∀y:Animal Mortal(y)")
    with pytest.raises(ValueError, match="Mortal"):
        to_casl_spec([ax1, ax2])


def test_predicate_arity_conflict():
    """Predicate 'P' used at arity 1 in one axiom and arity 2 in another —
    refused before any sort-inference union is even attempted for the
    second occurrence's arguments.
    """
    ax1 = FOL.parse("P(alice)")
    ax2 = FOL.parse("P(alice, bob)")
    with pytest.raises(ValueError, match="conflicting arities"):
        to_casl_spec([ax1, ax2])


def test_function_arity_conflict():
    """Function 'mother' applied to 1 argument in one axiom and 2 in
    another — the same arity-conflict check as predicates, on the function
    side.
    """
    ax1 = FOL.parse("∀x Q(mother(x))")
    ax2 = FOL.parse("∀x ∀y R(mother(x, y))")
    with pytest.raises(ValueError, match="conflicting arities"):
        to_casl_spec([ax1, ax2])


def test_constant_vs_function_name_conflict():
    """'alice' used as a bare 0-ary constant in one axiom and as a unary
    function 'alice(x)' in another — refused: this exporter declares at
    most one ops entry per name, and a constant/function clash cannot be
    reconciled into one.
    """
    ax1 = FOL.parse("P(alice)")
    ax2 = FOL.parse("∀x Q(alice(x))")
    with pytest.raises(ValueError, match="used both as a constant and as a function"):
        to_casl_spec([ax1, ax2])


def test_free_variable_refusal():
    """'Mortal(x)' as a whole formula has x free (never bound by any
    quantifier) -> CASL axioms must be closed, so this is refused.
    """
    ax = FOL.parse("Mortal(x)")
    with pytest.raises(ValueError, match="free variable 'x'"):
        to_casl_spec([ax])


def test_reserved_word_constant_refusal():
    """'axiom' is a CASL keyword; using it as a constant name ('Mortal
    (axiom)') must be refused."""
    ax = FOL.parse("Mortal(axiom)")
    with pytest.raises(ValueError, match="reserved CASL keyword 'axiom'"):
        to_casl_spec([ax])


def test_reserved_word_function_refusal():
    """'sort' is a CASL keyword; using it as a FUNCTION name ('P(sort(x))')
    must also be refused (the same check as the constant case, run against
    func_names instead of const_names)."""
    ax = FOL.parse("∀x P(sort(x))")
    with pytest.raises(ValueError, match="reserved CASL keyword 'sort'"):
        to_casl_spec([ax])


def test_spec_name_rejects_non_identifier():
    """spec_name must match [A-Za-z][A-Za-z0-9_]*; '2Bad' starts with a
    digit and is not a legal simple CASL identifier."""
    ax = Atom("P", ())
    with pytest.raises(ValueError, match="not a simple CASL identifier"):
        to_casl_spec([ax], spec_name="2Bad")


def test_spec_name_rejects_casl_keyword():
    """spec_name must not itself be a CASL keyword; 'sort' is one."""
    ax = Atom("P", ())
    with pytest.raises(ValueError, match="reserved CASL keyword 'sort'"):
        to_casl_spec([ax], spec_name="sort")


def test_to_casl_spec_requires_at_least_one_formula():
    """Both axioms and conjectures empty -> nothing to export -> refused."""
    with pytest.raises(ValueError, match="at least one axiom or conjecture"):
        to_casl_spec([])


# =============================================================================
# formula_to_casl: bare emission, Xor, and parenthesisation
# =============================================================================

def test_formula_to_casl_bare_atom():
    """A bare n-ary atom renders as 'Pred(arg1, arg2)' with a comma-space
    separator; a Constant/Variable term renders as its own name verbatim."""
    f = FOL.parse("P(alice, bob)")
    assert formula_to_casl(f) == "P(alice, bob)"


def test_formula_to_casl_not_of_atom_stays_bare():
    """Not applied to an atom stays bare: 'not P', no parens (the spec's
    explicit exception to the otherwise-blanket parenthesisation rule)."""
    f = FOL.parse("¬P")
    assert formula_to_casl(f) == "not P"


def test_formula_to_casl_not_of_compound_wraps_the_compound():
    """Not applied to a COMPOUND (here, And(P, Q)) wraps that compound in
    one pair of parens: 'not (P /\\ Q)' — i.e. the actual text 'not (P /\\ Q)'
    is 'not (P /\\ Q)' with CASL's own '/\\' token (one '/' then one '\\')."""
    f = Not(And(Atom("P", ()), Atom("Q", ())))
    assert formula_to_casl(f) == "not (P /\\ Q)"


def test_xor_emission_is_negated_iff():
    """Xor(P, Q) has no direct CASL operator, so it expands to the exact
    classical reading 'not (<a> <=> <b>)': P XOR Q is true exactly when P
    and Q disagree, i.e. exactly when 'P <=> Q' is false."""
    f = FOL.parse("P ⊕ Q")
    assert isinstance(f, Xor)
    assert formula_to_casl(f) == "not (P <=> Q)"


def test_formula_to_casl_blanket_wraps_every_nonroot_binary_connective():
    """(P \\/ Q) /\\ R: the left operand of the top-level And is itself a
    binary connective (Or) -> wrapped in parens even though '/\\' binds
    tighter than '\\/' in ordinary logic notation — this emitter does not
    rely on precedence at all, it parenthesises EVERY non-root binary
    connective, so the CASL reader never needs to know CASL's own junctor
    precedence to recover the intended tree. R (an atom) stays bare."""
    f = FOL.parse("(P ∨ Q) ∧ R")
    assert isinstance(f, And) and isinstance(f.left, Or)
    assert formula_to_casl(f) == "(P \\/ Q) /\\ R"


def test_formula_to_casl_equality_atom_stays_bare_as_connective_operand():
    """An equality atom behaves exactly like any other Atom as a connective
    operand: bare, no parens. '∀x ((x = alice) ∧ P(x))' — the quantifier's
    body (an And) is wrapped per the quantifier-body rule; inside it, both
    the equality atom and P(x) stay bare."""
    f = FOL.parse("∀x ((x = alice) ∧ P(x))")
    assert formula_to_casl(f) == "forall x : Thing . (x = alice /\\ P(x))"


def test_formula_to_casl_quantifier_as_connective_operand_is_wrapped():
    """A quantifier used as the RIGHT operand of Implies is wrapped in
    parens: 'Mortal(alice) => (exists y : Animal . Likes(alice, y))' —
    without the parens, CASL's maximal-right quantifier scope would swallow
    anything that might follow, so this emitter always delimits it
    explicitly. 'alice' is a ground SortedConstant (not a variable) so the
    formula is already closed without needing an outer quantifier — keeping
    the Implies itself as the formula's root, which is exactly what this
    test wants to exercise."""
    f = MSFOL.parse("Mortal(alice:Person) → (∃y:Animal Likes(alice:Person, y))")
    assert isinstance(f, Implies)
    assert (formula_to_casl(f)
            == "Mortal(alice) => (exists y : Animal . Likes(alice, y))")


def test_formula_to_casl_nested_quantifier_with_no_connective_stays_bare():
    """A quantifier used as the BODY of another quantifier (no connective in
    between) stays bare: no parens around the inner 'exists' — CASL
    quantifier scope already extends maximally right, so chaining binders
    is unambiguous without help."""
    f = MSFOL.parse("∀x:Person (∃y:Animal Likes(x, y))")
    assert isinstance(f, SortedQuantifier) and isinstance(f.formula, SortedQuantifier)
    assert (formula_to_casl(f)
            == "forall x : Person . exists y : Animal . Likes(x, y)")


def test_formula_to_casl_iff_and_implies_render_ascii_operators():
    """Iff renders as '<=>' and Implies as '=>', each operand a bare atom
    (both sides are 0-ary atoms here, so no extra parens anywhere)."""
    assert formula_to_casl(Iff(Atom("P", ()), Atom("Q", ()))) == "P <=> Q"
    assert formula_to_casl(Implies(Atom("P", ()), Atom("Q", ()))) == "P => Q"


def test_formula_to_casl_and_or_render_ascii_operators():
    """And renders as '/\\' and Or as '\\/' between two bare atoms."""
    assert formula_to_casl(And(Atom("P", ()), Atom("Q", ()))) == "P /\\ Q"
    assert formula_to_casl(Or(Atom("P", ()), Atom("Q", ()))) == "P \\/ Q"


def test_formula_to_casl_unsorted_quantifier_uses_default_sort():
    """A plain (unsorted) Quantifier's bound variable is declared at
    default_sort — 'Thing' unless overridden."""
    f = FOL.parse("∀x P(x)")
    assert isinstance(f, Quantifier)
    assert formula_to_casl(f) == "forall x : Thing . P(x)"
    assert formula_to_casl(f, default_sort="Entity") == "forall x : Entity . P(x)"


def test_formula_to_casl_sorted_quantifier_uses_its_own_sort():
    """A SortedQuantifier's bound variable is declared at its own literal
    sort, independent of default_sort."""
    f = MSFOL.parse("∃x:Animal P(x)")
    assert formula_to_casl(f, default_sort="Thing") == "exists x : Animal . P(x)"


def test_formula_to_casl_runs_the_same_validation_as_to_casl_spec():
    """formula_to_casl must run the SAME free-variable/reserved-word/sort-
    conflict checks as to_casl_spec, even though it does not need the
    resolved sorts to render bare text — the resulting text would not be
    valid CASL either way if left unchecked."""
    with pytest.raises(ValueError, match="free variable"):
        formula_to_casl(FOL.parse("Mortal(x)"))
    with pytest.raises(ValueError, match="reserved CASL keyword"):
        formula_to_casl(FOL.parse("Mortal(axiom)"))


# =============================================================================
# Out-of-fragment refusals
# =============================================================================

def test_notimplemented_for_modal_node():
    """A Box (□) node is outside the classical fragment -> NotImplementedError
    naming 'Box'."""
    f = Box(Atom("P", ()))
    with pytest.raises(NotImplementedError, match="Box"):
        formula_to_casl(f)


def test_notimplemented_for_count_node():
    """A Count (∃≥n) node is outside the classical fragment ->
    NotImplementedError naming 'Count'."""
    f = Count("ge", Number(2), Variable("x"), Atom("P", (Variable("x"),)))
    with pytest.raises(NotImplementedError, match="Count"):
        formula_to_casl(f)


def test_notimplemented_for_number_node_nested_in_a_function_argument():
    """A Number literal buried inside an otherwise-classical Function
    argument is still caught by the whole-tree fragment walk ->
    NotImplementedError naming 'Number' (CASL's basic library has no
    built-in numeric sort, so a bare numeral has nothing to be declared
    against)."""
    f = Atom("P", (Function("f", (Number(5),)),))
    with pytest.raises(NotImplementedError, match="Number"):
        formula_to_casl(f)


def test_notimplemented_also_applies_inside_to_casl_spec():
    """The same fragment check applies to to_casl_spec's axioms/conjectures,
    not just formula_to_casl."""
    f = Box(Atom("P", ()))
    with pytest.raises(NotImplementedError, match="Box"):
        to_casl_spec([f])


# ---------------------------------------------------------------------------
# Adversarial-review regressions (2026-08-12): reserved/malformed identifiers
# in EVERY emitted position, and 0-ary function reference syntax.
# ---------------------------------------------------------------------------

def test_keyword_predicate_name_is_refused():
    """Atom("axiom", ()) is constructible directly on the AST (no parser
    casing rule applies); emitting it produced a spec HETS 500s on
    (live-verified: 'unexpected keyword "axiom"'). Now refused loudly."""
    with pytest.raises(ValueError, match="predicate name 'axiom'"):
        to_casl_spec([Atom("axiom", ())])


def test_keyword_sort_name_is_refused():
    """SortedQuantifier's sort annotation is a raw string; the keyword
    'sort' as a sort name made HETS reject the spec (live-verified)."""
    formula = SortedQuantifier("∀", Variable("x"), "sort",
                               Atom("P", (Variable("x"),)))
    with pytest.raises(ValueError, match="sort name 'sort'"):
        to_casl_spec([formula])


def test_keyword_default_sort_is_refused():
    """default_sort is a caller-supplied raw string outside any grammar."""
    formula = Quantifier("∀", Variable("x"), Atom("P", (Variable("x"),)))
    with pytest.raises(ValueError, match="sort name 'pred'"):
        formula_to_casl(formula, default_sort="pred")


def test_malformed_identifier_is_refused_not_emitted():
    """A predicate name that is no CASL word at all ('foo bar') can only
    come from direct AST construction — refuse instead of emitting an
    unparseable spec."""
    with pytest.raises(ValueError, match="not a simple CASL identifier"):
        to_casl_spec([Atom("foo bar", ())])


def test_zero_ary_function_renders_bare_like_its_declaration():
    """A 0-ary operation is declared 'ops f : Thing' (constant-shaped), so
    a REFERENCE must be the bare name too — 'f()' is not CASL term syntax.
    Hand-derived: P(f) with f a 0-ary Function."""
    formula = Atom("P", (Function("f", ()),))
    assert formula_to_casl(formula) == "P(f)"


def test_default_sort_is_validated_even_without_any_quantifier():
    """Adversarial-review regression (Tier 3): with a quantifier-free axiom
    batch the union-find never binds default_sort into literal_sorts, yet
    sort_of()'s fallback still EMITS it in the `sorts` line — so a keyword
    default_sort must be refused up front, not slipped into the spec text.
    'forall' is a CASL keyword; the batch is a single 0-ary atom."""
    with pytest.raises(ValueError, match="reserved.*keyword|keyword"):
        to_casl_spec([Atom("Rain", ())], default_sort="forall")
    with pytest.raises(ValueError):
        to_casl_spec([Atom("Rain", ())], default_sort="not a word")
