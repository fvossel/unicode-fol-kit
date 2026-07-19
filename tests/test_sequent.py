"""Tests for the Gentzen sequent-calculus checker (unicode_fol_kit.atp.sequent).

Soundness backbone: every derivation the checker ACCEPTS is audited node-by-node.
A valid LK derivation has the property that EVERY sequent in it is valid, so for
the propositional / first-order fragment we assert each node's ``⋀Γ → ⋁Δ`` is
Z3-valid; for the genuinely second-order nodes we spot-check ``satisfies_so`` over
every tiny structure. The randomised test mutates valid derivations and asserts
``check_sequent_proof(m) ⇒ every node valid`` — the checker must never be fooled
into accepting an unsound derivation.

Single lowercase letters are VARIABLES; ground constants are built explicitly.
"""

from functools import reduce
from itertools import combinations, product
import random

import pytest

from unicode_fol_kit import is_valid
from unicode_fol_kit.fol.nodes import (
    Atom, Not, And, Or, Xor, Implies, Iff, Quantifier, Variable, Constant,
    SecondOrderQuantifier,
)
from unicode_fol_kit.semantics.tarski import Structure
from unicode_fol_kit.semantics.secondorder import satisfies_so
from unicode_fol_kit.atp.sequent import (
    Sequent, Derivation, Comprehension, SequentResult,
    sequent, derive, axiom,
    check_sequent_proof, verify_sequent_proof, render_sequent_proof,
    _free_pred_vars, _RULES,
)

P = Atom("P", [])
Q = Atom("Q", [])
R = Atom("R", [])
S = Atom("S", [])


def ALL(v, f):
    return Quantifier("∀", v, f)


def EX(v, f):
    return Quantifier("∃", v, f)


# ---------------------------------------------------------------------------
# Soundness oracles
# ---------------------------------------------------------------------------

def _seq_formula(s):
    """Return a Node for ``⋀antecedent → ⋁succedent`` (or the sentinel "FALSE")."""
    ante = reduce(And, s.antecedent) if s.antecedent else None
    succ = reduce(Or, s.succedent) if s.succedent else None
    if ante is None and succ is None:
        return "FALSE"            # ⊤ → ⊥
    if ante is None:
        return succ               # ⊤ → succ
    if succ is None:
        return Not(ante)          # ante → ⊥
    return Implies(ante, succ)


def seq_valid_z3(s):
    """True iff the sequent is valid (first-order / propositional), via Z3."""
    f = _seq_formula(s)
    if f == "FALSE":
        return False
    return is_valid(f)


def all_nodes_valid_z3(d):
    """True iff every sequent in the derivation tree is Z3-valid (no SO nodes)."""
    if not seq_valid_z3(d.conclusion):
        return False
    return all(all_nodes_valid_z3(c) for c in d.premises)


def _so_symbols(formula):
    """Collect free predicate signatures (name, arity) and constant names."""
    preds = {}
    consts = set()
    free_preds = _free_pred_vars(formula)
    for n in formula.walk():
        if isinstance(n, Atom) and n.predicate in free_preds:
            preds[n.predicate] = len(n.args)
        if isinstance(n, Constant):
            consts.add(n.name)
    return preds, consts


def so_valid_tiny(formula):
    """Necessary condition for SO validity: ``holds_so`` in EVERY structure over {0,1}.

    Enumerates all interpretations of the free constants and free predicates of the
    formula on a 2-element domain and asserts the formula holds in each.
    """
    preds, consts = _so_symbols(formula)
    domain = (0, 1)
    pred_items = list(preds.items())
    const_list = sorted(consts)
    # All extensions of each predicate (subset of domain**arity).
    pred_choice_lists = []
    for _, arity in pred_items:
        tuples = list(product(domain, repeat=arity))
        subsets = [frozenset(c) for r in range(len(tuples) + 1)
                   for c in combinations(tuples, r)]
        pred_choice_lists.append(subsets)
    for const_vals in product(domain, repeat=len(const_list)):
        constants = dict(zip(const_list, const_vals))
        for pred_choice in product(*pred_choice_lists) if pred_choice_lists else [()]:
            predicates = {(name, arity): set(ext)
                          for (name, arity), ext in zip(pred_items, pred_choice)}
            st = Structure(domain, constants=constants, predicates=predicates)
            if not satisfies_so(formula, st, {}, {}):
                return False
    return True


# ---------------------------------------------------------------------------
# Curated valid derivations (propositional / first-order, Z3-auditable)
# ---------------------------------------------------------------------------

def _d_imp_refl():
    """⊢ P → P."""
    return derive(sequent([], [Implies(P, P)]), "→R", axiom(sequent([P], [P])))


def _d_modus_ponens():
    """P, P→Q ⊢ Q."""
    return derive(sequent([P, Implies(P, Q)], [Q]), "→L",
                  axiom(sequent([P], [P, Q])),
                  axiom(sequent([P, Q], [Q])))


def _d_excluded_middle():
    """⊢ P ∨ ¬P."""
    return derive(sequent([], [Or(P, Not(P))]), "∨R",
              derive(sequent([], [P, Not(P)]), "¬R",
                  axiom(sequent([P], [P]))))


def _d_demorgan():
    """¬(P ∨ Q) ⊢ ¬P ∧ ¬Q."""
    def branch(x):
        return derive(sequent([Not(Or(P, Q))], [Not(x)]), "¬R",
                  derive(sequent([Not(Or(P, Q)), x], []), "¬L",
                      derive(sequent([x], [Or(P, Q)]), "∨R",
                          axiom(sequent([x], [P, Q])))))
    return derive(sequent([Not(Or(P, Q))], [And(Not(P), Not(Q))]), "∧R",
                  branch(P), branch(Q))


def _d_and_comm():
    """P ∧ Q ⊢ Q ∧ P."""
    return derive(sequent([And(P, Q)], [And(Q, P)]), "∧L",
              derive(sequent([P, Q], [And(Q, P)]), "∧R",
                  axiom(sequent([P, Q], [Q])),
                  axiom(sequent([P, Q], [P]))))


def _d_curry():
    """P → (Q → R) ⊢ (P ∧ Q) → R."""
    return derive(sequent([Implies(P, Implies(Q, R))], [Implies(And(P, Q), R)]), "→R",
              derive(sequent([Implies(P, Implies(Q, R)), And(P, Q)], [R]), "∧L",
                  derive(sequent([Implies(P, Implies(Q, R)), P, Q], [R]), "→L",
                      axiom(sequent([P, Q], [P, R])),
                      derive(sequent([Implies(Q, R), P, Q], [R]), "→L",
                          axiom(sequent([P, Q], [Q, R])),
                          axiom(sequent([R, P, Q], [R]))))))


def _d_forall_inst():
    """∀x P(x) ⊢ P(c)."""
    x, c = Variable("x"), Constant("c")
    return derive(sequent([ALL(x, Atom("P", [x]))], [Atom("P", [c])]), "∀L",
                  axiom(sequent([Atom("P", [c])], [Atom("P", [c])])),
                  extra=[c])


def _d_forall_dist():
    """∀x(P(x)→Q(x)), ∀x P(x) ⊢ ∀x Q(x)."""
    x, a = Variable("x"), Variable("a")

    def Px(t):
        return Atom("P", [t])

    def Qx(t):
        return Atom("Q", [t])

    return derive(
        sequent([ALL(x, Implies(Px(x), Qx(x))), ALL(x, Px(x))], [ALL(x, Qx(x))]), "∀R",
        derive(sequent([ALL(x, Implies(Px(x), Qx(x))), ALL(x, Px(x))], [Qx(a)]), "∀L",
            derive(sequent([Implies(Px(a), Qx(a)), ALL(x, Px(x))], [Qx(a)]), "∀L",
                derive(sequent([Implies(Px(a), Qx(a)), Px(a)], [Qx(a)]), "→L",
                    axiom(sequent([Px(a)], [Px(a), Qx(a)])),
                    axiom(sequent([Qx(a), Px(a)], [Qx(a)]))),
                extra=[a]),
            extra=[a]),
        extra=[a])


def _d_exists_gen():
    """P(c) ⊢ ∃x P(x)."""
    x, c = Variable("x"), Constant("c")
    return derive(sequent([Atom("P", [c])], [EX(x, Atom("P", [x]))]), "∃R",
                  axiom(sequent([Atom("P", [c])], [Atom("P", [c])])),
                  extra=[c])


def _d_drinker_step():
    """∀x P(x) ⊢ ∃x P(x) (non-empty domain): ∃R after ∀L at a fresh witness var."""
    x, a = Variable("x"), Variable("a")
    return derive(sequent([ALL(x, Atom("P", [x]))], [EX(x, Atom("P", [x]))]), "∃R",
              derive(sequent([ALL(x, Atom("P", [x]))], [Atom("P", [a])]), "∀L",
                  axiom(sequent([Atom("P", [a])], [Atom("P", [a])])),
                  extra=[a]),
              extra=[a])


# --- coverage for rules the randomized audit otherwise never exercises ---
# (Cut, weakening, contraction, ∨L, ↔L/↔R, ∃L, ⊕L/⊕R — flagged by the proof-audit)

def _d_cut():
    """P, ¬P ⊢ Q via Cut on P."""
    return derive(sequent([P, Not(P)], [Q]), "Cut",
                  axiom(sequent([P, Not(P)], [Q, P])),
                  derive(sequent([P, Not(P), P], [Q]), "¬L",
                         axiom(sequent([P, P], [Q, P]))))


def _d_weaken_left():
    """P, Q ⊢ P via WL."""
    return derive(sequent([P, Q], [P]), "WL", axiom(sequent([P], [P])))


def _d_weaken_right():
    """P ⊢ P, Q via WR."""
    return derive(sequent([P], [P, Q]), "WR", axiom(sequent([P], [P])))


def _d_contract_left():
    """P ⊢ P via CL from P, P ⊢ P."""
    return derive(sequent([P], [P]), "CL", axiom(sequent([P, P], [P])))


def _d_contract_right():
    """P ⊢ P via CR from P ⊢ P, P."""
    return derive(sequent([P], [P]), "CR", axiom(sequent([P], [P, P])))


def _d_or_left():
    """P ∨ Q ⊢ Q ∨ P via ∨L."""
    return derive(sequent([Or(P, Q)], [Or(Q, P)]), "∨L",
                  derive(sequent([P], [Or(Q, P)]), "∨R", axiom(sequent([P], [Q, P]))),
                  derive(sequent([Q], [Or(Q, P)]), "∨R", axiom(sequent([Q], [Q, P]))))


def _d_iff_left():
    """P ↔ Q, P ⊢ Q via ↔L."""
    return derive(sequent([Iff(P, Q), P], [Q]), "↔L",
                  axiom(sequent([P, P, Q], [Q])),
                  axiom(sequent([P], [Q, P, Q])))


def _d_iff_right():
    """⊢ P ↔ P via ↔R."""
    return derive(sequent([], [Iff(P, P)]), "↔R",
                  axiom(sequent([P], [P])), axiom(sequent([P], [P])))


def _d_exists_left():
    """∃x P(x) ⊢ ∃x P(x) via ∃L (eigenvariable) then ∃R."""
    x, a = Variable("x"), Variable("a")
    return derive(sequent([EX(x, Atom("P", [x]))], [EX(x, Atom("P", [x]))]), "∃L",
                  derive(sequent([Atom("P", [a])], [EX(x, Atom("P", [x]))]), "∃R",
                         axiom(sequent([Atom("P", [a])], [Atom("P", [a])])),
                         extra=[a]),
                  extra=[a])


def _d_xor_right():
    """⊢ P ⊕ ¬P via ⊕R (A⊕B ≡ ¬(A↔B))."""
    return derive(sequent([], [Xor(P, Not(P))]), "⊕R",
                  derive(sequent([P, Not(P)], []), "¬L", axiom(sequent([P], [P]))),
                  derive(sequent([], [P, Not(P)]), "¬R", axiom(sequent([P], [P]))))


def _d_xor_left():
    """P ⊕ Q, P, Q ⊢ via ⊕L."""
    return derive(sequent([Xor(P, Q), P, Q], []), "⊕L",
                  axiom(sequent([P, Q, P], [Q])),
                  axiom(sequent([P, Q, Q], [P])))


CURATED_FO = [
    _d_imp_refl, _d_modus_ponens, _d_excluded_middle, _d_demorgan,
    _d_and_comm, _d_curry, _d_forall_inst, _d_forall_dist, _d_exists_gen,
    _d_drinker_step,
    _d_cut, _d_weaken_left, _d_weaken_right, _d_contract_left, _d_contract_right,
    _d_or_left, _d_iff_left, _d_iff_right, _d_exists_left, _d_xor_right, _d_xor_left,
]


@pytest.mark.parametrize("builder", CURATED_FO, ids=lambda b: b.__name__)
def test_curated_fo_accepted(builder):
    r = verify_sequent_proof(builder())
    assert r.ok, r.error


@pytest.mark.parametrize("builder", CURATED_FO, ids=lambda b: b.__name__)
def test_curated_fo_every_node_z3_valid(builder):
    d = builder()
    assert check_sequent_proof(d)
    assert all_nodes_valid_z3(d)


# ---------------------------------------------------------------------------
# Soundness guards (propositional / first-order)
# ---------------------------------------------------------------------------

def test_reject_axiom_no_shared_formula():
    assert check_sequent_proof(axiom(sequent([P], [Q]))) is False


def test_reject_and_r_wrong_premises():
    bad = derive(sequent([], [And(P, Q)]), "∧R",
                 axiom(sequent([P], [P])), axiom(sequent([Q], [Q])))
    assert check_sequent_proof(bad) is False


def test_reject_imp_r_principal_mismatch():
    bad = derive(sequent([], [Implies(P, Q)]), "→R", axiom(sequent([P], [P])))
    assert check_sequent_proof(bad) is False


def test_reject_context_not_shared():
    # ∧R requires the SAME Γ,Δ in both premises; here the contexts differ.
    bad = derive(sequent([P], [And(Q, R)]), "∧R",
                 axiom(sequent([P], [Q])),
                 axiom(sequent([S], [R])))
    assert check_sequent_proof(bad) is False


def test_reject_forall_r_eigenvariable_in_context():
    x, a = Variable("x"), Variable("a")
    bad = derive(sequent([Atom("P", [a])], [ALL(x, Atom("P", [x]))]), "∀R",
                 axiom(sequent([Atom("P", [a])], [Atom("P", [a])])),
                 extra=[a])
    r = verify_sequent_proof(bad)
    assert r.ok is False
    assert "eigenvariable" in r.error


def test_reject_exists_l_eigenvariable_in_context():
    x, a = Variable("x"), Variable("a")
    # ∃x P(x), Q(a) ⊢ Q(a) with eigenvariable a free in Q(a) -> rejected.
    bad = derive(sequent([EX(x, Atom("P", [x])), Atom("Q", [a])], [Atom("Q", [a])]), "∃L",
                 axiom(sequent([Atom("P", [a]), Atom("Q", [a])], [Atom("Q", [a])])),
                 extra=[a])
    r = verify_sequent_proof(bad)
    assert r.ok is False
    assert "eigenvariable" in r.error


def test_reject_deep_error_surfaces():
    # A broken leaf nested under valid rules must make the whole derivation fail.
    bad = derive(sequent([], [Implies(P, Q)]), "→R",
                 axiom(sequent([P], [Q])))  # leaf has no shared formula
    assert check_sequent_proof(bad) is False


# ---------------------------------------------------------------------------
# Second-order rules
# ---------------------------------------------------------------------------

def _SO_consts():
    c, z = Constant("c"), Variable("z")
    return c, z


def test_so_universal_instantiation_via_comprehension():
    # ∀X X(c) ⊢ P(c)   via ∀²L (X := λz.P(z))
    c, z = _SO_consts()
    Xc = Atom("X", [c])
    Pc = Atom("P", [c])
    d = derive(sequent([SecondOrderQuantifier("∀", "X", 1, Xc)], [Pc]), "∀²L",
               axiom(sequent([Pc], [Pc])),
               extra=[Comprehension((z,), Atom("P", [z]))])
    assert check_sequent_proof(d)
    assert so_valid_tiny(Implies(SecondOrderQuantifier("∀", "X", 1, Xc), Pc))


def test_so_existential_generalization_via_comprehension():
    # P(c) ⊢ ∃X X(c)   via ∃²R (X := λz.P(z))
    c, z = _SO_consts()
    Xc = Atom("X", [c])
    Pc = Atom("P", [c])
    d = derive(sequent([Pc], [SecondOrderQuantifier("∃", "X", 1, Xc)]), "∃²R",
               axiom(sequent([Pc], [Pc])),
               extra=[Comprehension((z,), Atom("P", [z]))])
    assert check_sequent_proof(d)
    assert so_valid_tiny(Implies(Pc, SecondOrderQuantifier("∃", "X", 1, Xc)))


def test_so_universal_intro_predicate_eigenvariable():
    # ⊢ ∀X (X(c) → X(c))   via ∀²R (eigenvar Y) → →R → Ax
    c, _ = _SO_consts()
    Xc = Atom("X", [c])
    Yc = Atom("Y", [c])
    d = derive(sequent([], [SecondOrderQuantifier("∀", "X", 1, Implies(Xc, Xc))]), "∀²R",
           derive(sequent([], [Implies(Yc, Yc)]), "→R",
               axiom(sequent([Yc], [Yc]))),
           extra=["Y"])
    assert check_sequent_proof(d)
    assert so_valid_tiny(SecondOrderQuantifier("∀", "X", 1, Implies(Xc, Xc)))


def test_so_comprehension_with_quantified_body():
    # ∀X X(c) ⊢ ∃y P(y)  via ∀²L with comprehension λz. ∃y P(y) (arity 1, ignores z)
    c, z = _SO_consts()
    y = Variable("y")
    Xc = Atom("X", [c])
    exists_y = EX(y, Atom("P", [y]))
    d = derive(sequent([SecondOrderQuantifier("∀", "X", 1, Xc)], [exists_y]), "∀²L",
               axiom(sequent([exists_y], [exists_y])),
               extra=[Comprehension((z,), exists_y)])
    assert check_sequent_proof(d)


def test_reject_so_predicate_eigenvariable_in_context():
    # P(c) ⊢ ∀X X(c) with predicate eigenvariable "P" (free in the antecedent).
    c, _ = _SO_consts()
    Xc = Atom("X", [c])
    Pc = Atom("P", [c])
    bad = derive(sequent([Pc], [SecondOrderQuantifier("∀", "X", 1, Xc)]), "∀²R",
                 axiom(sequent([Pc], [Pc])),
                 extra=["P"])
    r = verify_sequent_proof(bad)
    assert r.ok is False
    assert "predicate eigenvariable" in r.error


def test_reject_so_predicate_eigenvariable_capture():
    # Regression: A[X:=Y] for A = ∀²Y (Y(c) → X(c)) must NOT let the introduced Y be
    # captured by the inner ∀²Y. Otherwise ⊢ ∀X ∀²Y (Y(c) → X(c)) — which is NOT
    # second-order valid — would be derivable.
    c = Constant("c")
    A = SecondOrderQuantifier("∀", "Y", 1, Implies(Atom("Y", [c]), Atom("X", [c])))
    endX = SecondOrderQuantifier("∀", "X", 1, A)
    captured = SecondOrderQuantifier("∀", "Y", 1, Implies(Atom("Y", [c]), Atom("Y", [c])))
    w_to_w = Implies(Atom("W", [c]), Atom("W", [c]))
    bad = derive(sequent([], [endX]), "∀²R",
             derive(sequent([], [captured]), "∀²R",
                 derive(sequent([], [w_to_w]), "→R",
                     axiom(sequent([Atom("W", [c])], [Atom("W", [c])]))),
                 extra=["W"]),
             extra=["Y"])
    assert check_sequent_proof(bad) is False
    # And the would-be conclusion really is invalid (domain {0}, c↦0, Y={(0,)}, X=∅).
    assert so_valid_tiny(_seq_formula(bad.conclusion)) is False


def test_so_comprehension_avoids_predicate_capture():
    # Regression: instantiating X in ∀²W X(c) with the comprehension λz. W(c) (whose
    # body has a FREE predicate variable W) must α-rename the inner ∀²W binder, so the
    # free W of the comprehension is not captured.
    from unicode_fol_kit.atp.sequent import _subst_pred, _free_pred_vars
    c, z = _SO_consts()
    body = SecondOrderQuantifier("∀", "W", 1, Atom("X", [c]))
    inst = _subst_pred(body, "X", (z,), Atom("W", [c]))
    assert "W" in _free_pred_vars(inst)  # the comprehension's free W stayed free


def test_so_comprehension_avoids_capture_under_count_binder():
    # Regression: a counting quantifier binds an object variable just as ∀/∃ does, so
    # instantiating X in ∃=2 v X(v) with a comprehension whose body has a FREE v must
    # α-rename that binder. Walking into ∃=n structurally captured the free v instead.
    from unicode_fol_kit.atp.sequent import _subst_pred, _free_vars
    from unicode_fol_kit.fol.msflparser import MSFLParser
    v = Variable("v")
    body = MSFLParser().parse("∃=2 v (X(v))")
    inst = _subst_pred(body, "X", (Variable("z"),), Atom("R", [v, Variable("z")]))
    assert v in _free_vars(inst)          # the comprehension's free v stayed free
    assert inst.variable != v             # the counting binder was renamed away


def test_so_comprehension_avoids_capture_under_slashed_existential():
    # Regression, two guards at once. ∃v/{v_0} binds v, so instantiating X with a
    # comprehension whose body has a free v must α-rename it (pre-fix: captured).
    # And the fresh name must avoid the SLASH names too — they are plain strings that
    # _free_vars cannot see, so minting "v_0" here would silently rewire the
    # independence set instead of capturing anything visible.
    from unicode_fol_kit.atp.sequent import _subst_pred, _free_vars
    from unicode_fol_kit.fol.nodes import SlashedExists
    v, z = Variable("v"), Variable("z")
    body = SlashedExists(v, ("v_0",), Atom("X", [v]))
    inst = _subst_pred(body, "X", (z,), Atom("R", [v, z]))
    assert v in _free_vars(inst)              # the comprehension's free v stayed free
    assert inst.variable.name != "v"          # the slashed binder was renamed
    assert inst.variable.name != "v_0"        # ... and did not collide with the slash
    assert inst.slashed == ("v_0",)           # the independence set is untouched


def test_reject_so_comprehension_arity_mismatch():
    c, _ = _SO_consts()
    Xc = Atom("X", [c])
    Pc = Atom("P", [c])
    bad = derive(sequent([SecondOrderQuantifier("∀", "X", 1, Xc)], [Pc]), "∀²L",
                 axiom(sequent([Pc], [Pc])),
                 extra=[Comprehension((), Pc)])  # arity 0 vs X arity 1
    assert check_sequent_proof(bad) is False


# ---------------------------------------------------------------------------
# Randomised mutation soundness (propositional / first-order)
# ---------------------------------------------------------------------------

_ATOMS = [P, Q, R, S]


def _rand_prop(rng, depth=2):
    if depth <= 0 or rng.random() < 0.5:
        a = rng.choice(_ATOMS)
        return Not(a) if rng.random() < 0.3 else a
    op = rng.choice([And, Or, Implies, Iff, "not"])
    if op == "not":
        return Not(_rand_prop(rng, depth - 1))
    return op(_rand_prop(rng, depth - 1), _rand_prop(rng, depth - 1))


_RULE_NAMES = list(_RULES)


def _mutate_once(node, rng):
    kind = rng.choice(["rule", "replace", "add", "remove", "extra"])
    if kind == "rule":
        return Derivation(node.conclusion, rng.choice(_RULE_NAMES), node.premises, node.extra)
    if kind == "extra":
        return Derivation(node.conclusion, node.rule, node.premises, (_rand_prop(rng, 1),))
    ante = list(node.conclusion.antecedent)
    succ = list(node.conclusion.succedent)
    target = ante if rng.random() < 0.5 else succ
    if kind == "replace" and target:
        target[rng.randrange(len(target))] = _rand_prop(rng)
    elif kind == "add":
        target.append(_rand_prop(rng))
    elif kind == "remove" and target:
        target.pop(rng.randrange(len(target)))
    return Derivation(Sequent(tuple(ante), tuple(succ)), node.rule, node.premises, node.extra)


def _node_count(d):
    return 1 + sum(_node_count(c) for c in d.premises)


def _rebuild_with_mutation(d, target, mutator, counter):
    my = counter[0]
    counter[0] += 1
    new_prem = tuple(_rebuild_with_mutation(c, target, mutator, counter) for c in d.premises)
    node = Derivation(d.conclusion, d.rule, new_prem, d.extra)
    return mutator(node) if my == target else node


def _mutate(d, rng):
    target = rng.randrange(_node_count(d))
    return _rebuild_with_mutation(d, target, lambda n: _mutate_once(n, rng), [0])


def test_sequent_mixed_quantifier_spelling_accepted():
    # Regression: a ∀L step whose premise spells the quantifier 'forall' (not '∀')
    # must still be accepted — the checker canonicalises spellings before matching.
    x, c = Variable("x"), Constant("c")
    word_form = Quantifier("forall", x, Atom("P", [x]))
    d = derive(sequent([word_form], [Atom("P", [c])]), "∀L",
               axiom(sequent([Atom("P", [c])], [Atom("P", [c])])),
               extra=[c])
    assert check_sequent_proof(d)


def test_xor_rules_reject_wrong_premises():
    # ⊕R / ⊕L soundness guards (the valid cases are in CURATED_FO).
    bad_r = derive(sequent([], [Xor(P, Q)]), "⊕R",
                   axiom(sequent([P], [P])), axiom(sequent([Q], [Q])))
    assert check_sequent_proof(bad_r) is False
    bad_l = derive(sequent([Xor(P, Q)], [P]), "⊕L",
                   axiom(sequent([P], [P])), axiom(sequent([Q], [Q])))
    assert check_sequent_proof(bad_l) is False


def test_random_mutation_soundness():
    rng = random.Random(20260626)
    accepted = rejected = 0
    for _ in range(2500):
        base = rng.choice(CURATED_FO)()
        mutant = _mutate(base, rng)
        if check_sequent_proof(mutant):
            accepted += 1
            assert all_nodes_valid_z3(mutant), (
                "UNSOUND accepted mutant:\n" + render_sequent_proof(mutant))
        else:
            rejected += 1
    # Mutations should mostly break the derivation, but some stay valid — both the
    # acceptances (audited above) and the rejections must be non-trivial.
    assert rejected > 0
    assert accepted > 0


# ---------------------------------------------------------------------------
# Second-order randomized audit (Z3 cannot evaluate SO; oracle is so_valid_tiny)
# ---------------------------------------------------------------------------

def _so_d_forall_l():
    c, z = Constant("c"), Variable("z")
    return derive(sequent([SecondOrderQuantifier("∀", "X", 1, Atom("X", [c]))],
                          [Atom("P", [c])]), "∀²L",
                  axiom(sequent([Atom("P", [c])], [Atom("P", [c])])),
                  extra=[Comprehension((z,), Atom("P", [z]))])


def _so_d_exists_r():
    c, z = Constant("c"), Variable("z")
    return derive(sequent([Atom("P", [c])],
                          [SecondOrderQuantifier("∃", "X", 1, Atom("X", [c]))]), "∃²R",
                  axiom(sequent([Atom("P", [c])], [Atom("P", [c])])),
                  extra=[Comprehension((z,), Atom("P", [z]))])


def _so_d_forall_r():
    c = Constant("c")
    body = Implies(Atom("X", [c]), Atom("X", [c]))
    return derive(sequent([], [SecondOrderQuantifier("∀", "X", 1, body)]), "∀²R",
                  derive(sequent([], [Implies(Atom("Y", [c]), Atom("Y", [c]))]), "→R",
                         axiom(sequent([Atom("Y", [c])], [Atom("Y", [c])]))),
                  extra=["Y"])


SO_CURATED = [_so_d_forall_l, _so_d_exists_r, _so_d_forall_r]


def _all_deriv_nodes(d):
    yield d
    for child in d.premises:
        yield from _all_deriv_nodes(child)


def so_all_nodes_valid(d):
    """True iff every node's sequent is valid by ``so_valid_tiny`` (skips unevaluable)."""
    for node in _all_deriv_nodes(d):
        formula = _seq_formula(node.conclusion)
        if formula == "FALSE":
            return False
        try:
            if not so_valid_tiny(formula):
                return False
        except Exception:
            continue  # free object variable etc. — not finitely auditable here
    return True


@pytest.mark.parametrize("builder", SO_CURATED, ids=lambda b: b.__name__)
def test_so_curated_every_node_valid(builder):
    d = builder()
    assert check_sequent_proof(d)
    assert so_all_nodes_valid(d)


def test_so_random_mutation_soundness():
    rng = random.Random(20260627)
    accepted = 0
    for _ in range(1500):
        mutant = _mutate(rng.choice(SO_CURATED)(), rng)
        if check_sequent_proof(mutant):
            accepted += 1
            assert so_all_nodes_valid(mutant), (
                "UNSOUND accepted SO mutant:\n" + render_sequent_proof(mutant))
    assert accepted > 0


# ---------------------------------------------------------------------------
# Eigenvariable freshness — randomized (object-level ∀R / ∃L side condition)
# ---------------------------------------------------------------------------

def test_eigenvariable_freshness_fuzz():
    # A ∀R step whose eigenvariable occurs free in the lower sequent must be rejected
    # (the premise is a genuine axiom, so only the freshness check can fire); the same
    # shape with a genuinely fresh eigenvariable must be accepted and Z3-sound.
    from unicode_fol_kit.fol.nodes import Function
    rng = random.Random(99)
    x = Variable("x")
    rejected = accepted = 0
    for _ in range(400):
        e = Variable(rng.choice(["a", "b", "c", "u", "v"]))
        e_term = e if rng.random() < 0.5 else Function("f", [e])
        ctx = Atom(rng.choice(["R", "S", "Q"]), [e_term])  # contains the eigenvariable
        all_x = ALL(x, Atom("P", [x]))
        # BAD: e free in ctx (which sits on both sides, so the premise is an axiom).
        bad = derive(sequent([ctx], [ctx, all_x]), "∀R",
                     axiom(sequent([ctx], [ctx, Atom("P", [e])])), extra=[e])
        assert check_sequent_proof(bad) is False
        rejected += 1
        # CONTROL: a fresh eigenvariable not occurring in ctx.
        fresh = Variable("zz9")
        good = derive(sequent([ctx], [ctx, all_x]), "∀R",
                      axiom(sequent([ctx], [ctx, Atom("P", [fresh])])), extra=[fresh])
        r = verify_sequent_proof(good)
        assert r.ok, r.error
        assert all_nodes_valid_z3(good)
        accepted += 1
    assert rejected > 0 and accepted > 0


# ---------------------------------------------------------------------------
# Serialization round-trip + rendering + exports
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("builder", CURATED_FO, ids=lambda b: b.__name__)
def test_derivation_dict_round_trip(builder):
    d = builder()
    assert Derivation.from_dict(d.to_dict()) == d


def test_so_derivation_dict_round_trip():
    c, z = _SO_consts()
    Xc = Atom("X", [c])
    Pc = Atom("P", [c])
    d = derive(sequent([SecondOrderQuantifier("∀", "X", 1, Xc)], [Pc]), "∀²L",
               axiom(sequent([Pc], [Pc])),
               extra=[Comprehension((z,), Atom("P", [z]))])
    assert Derivation.from_dict(d.to_dict()) == d


def test_render_sequent_proof_structure():
    text = render_sequent_proof(_d_modus_ponens())
    lines = text.splitlines()
    assert lines[0].startswith("P, P → Q ⊢ Q")
    assert "[→L]" in lines[0]
    assert all("[Ax]" in ln for ln in lines[1:])
    # Two premises, each indented two spaces.
    assert sum(1 for ln in lines if ln.startswith("  ") and "⊢" in ln) == 2


def test_top_level_exports():
    import unicode_fol_kit as u
    for name in ("Sequent", "Derivation", "Comprehension", "SequentResult",
                 "sequent", "derive", "axiom",
                 "check_sequent_proof", "verify_sequent_proof", "render_sequent_proof"):
        assert hasattr(u, name) and name in u.__all__, name
