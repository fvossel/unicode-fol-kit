# Further Non-Classical Logics

New in 0.9.0: four small semantic evaluators for logics that sit just outside classical FOL — free logic, public-announcement (dynamic epistemic) logic, counterfactual conditionals, and circumscriptive non-monotonic entailment. Each builds an AST with the node constructors from `unicode_fol_kit.fol.nodes` and evaluates it against an explicit, hand-built model.

## Free logic

Classical FOL assumes every term denotes an existing individual, so universal instantiation `∀x φ → φ(c)` and existential generalisation `φ(c) → ∃x φ` are valid. Free logic drops that assumption: quantifiers range only over an inner `existing` domain `E ⊆ outer`, while constants may denote a merely-possible object of the wider `outer` domain — or fail to denote at all. The existence predicate `E!(t)` says "`t` denotes an existing object", and the classical rules hold only in their guarded forms `(∀x φ ∧ E!(c)) → φ(c)`.

A `FreeModel` carries the `outer` tuple, the `existing` inner subset, a (possibly partial) constant/function interpretation — a name absent from `constants` is non-denoting — and predicate tables over `outer`. Two policies govern an atom containing a non-denoting term: `"negative"` (default) makes it simply false (so `t = t` also fails), while `"positive"` keeps self-identity `t = t` true for any term.

```python
from unicode_fol_kit.fol.nodes import Atom, Implies, Quantifier, Variable, Constant
from unicode_fol_kit.semantics.free_logic import FreeModel, free_holds

x, c = Variable("x"), Constant("c")
Px = lambda t: Atom("P", [t])
all_P = Quantifier("∀", x, Px(x))               # ∀x P(x)

# c denotes the non-existing object 1; the inner (existing) domain is {0}, with P(0).
m = FreeModel(outer=(0, 1), existing=frozenset({0}), constants={"c": 1},
              predicates={("P", 1): frozenset({(0,)})})

free_holds(all_P, m)                            # → True   (∀x P(x) over {0})
free_holds(Px(c), m)                            # → False  (c is non-existing)
free_holds(Implies(all_P, Px(c)), m)            # → False  (universal instantiation is invalid)
free_holds(Atom("E!", [c]), m)                  # → False  (c does not exist)
free_holds(Quantifier("∃", x, Atom("=", [x, c])), m)   # → False  (∃x(x=c): EG fails)
```

The negative/positive split shows up on a non-denoting constant (one absent from `constants`):

```python
m2 = FreeModel(outer=(0,), existing=frozenset({0}), constants={})
free_holds(Atom("=", [c, c]), m2, policy="positive")   # → True   (self-identity preserved)
free_holds(Atom("=", [c, c]), m2, policy="negative")   # → False  (a non-denoting term is nothing)
```

`free_satisfies(formula, model, assignment, policy)` is the open-formula form; `free_holds` is the convenience wrapper for a closed formula under the empty assignment.

## Public announcement / dynamic epistemic logic

Static epistemic logic (`Knows` over a `KripkeModel`) describes what agents know; public announcement logic (PAL) adds the dynamics. A truthful public announcement of `φ` removes every world where `φ` is false, so knowledge changes. `announce(model, φ)` returns that updated model — `M|φ`, with relations and valuation cut down to the surviving worlds — and the box / diamond operators evaluate `[φ!]ψ` and `⟨φ!⟩ψ` at a world:

```python
from unicode_fol_kit.fol.nodes import Atom, Not, And, Knows
from unicode_fol_kit.semantics.kripke import KripkeModel, satisfies_modal
from unicode_fol_kit.semantics.dynamic_epistemic import announce, box_announce, diamond_announce

p = Atom("p", ())
Kap = Knows("a", p)                              # K_a p
# Agent a cannot tell world 0 (where p holds) from world 1 (where it does not).
M = KripkeModel([0, 1], {"K:a": {(0, 0), (0, 1), (1, 0), (1, 1)}}, {0: {"p"}})

satisfies_modal(Kap, M, 0)                       # → False  (a does not yet know p)
box_announce(M, 0, p, Kap)                       # → True   (...but [p!] K_a p)

updated = announce(M, p)                         # M restricted to its p-worlds
1 in updated.worlds                              # → False  (world 1 was dropped)
satisfies_modal(Kap, updated, 0)                 # → True   (a now knows p)
```

`box_announce` is vacuously true when the announcement is false at the world (an untruthful announcement is not made); `diamond_announce` is its dual — true iff the announcement is truthful *and* the post-condition then holds. The Moore sentence `p ∧ ¬K_a p` is the classic self-refuting announcement: true before, but announcing it makes it false.

```python
moore = And(p, Not(Kap))                         # p ∧ ¬K_a p
satisfies_modal(moore, M, 0)                      # → True   (true before announcing)
diamond_announce(M, 0, moore, moore)              # → False  (...but false after announcing it)
box_announce(M, 0, moore, Kap)                    # → True   (announcing it makes a know p)
```

The relation key `"K:a"` is the epistemic accessibility relation for agent `a`; see {doc}`modal` for the full relation-name convention.

## Counterfactual conditionals

The material conditional gets counterfactuals wrong. `A □→ B` ("if A were the case, B would be") is evaluated over Lewis's system of spheres: each world carries a nested sequence of world-sets ordered innermost (closest) first, and `A □→ B` holds iff, in the smallest sphere that contains an `A`-world, every `A`-world is a `B`-world (vacuously true if no sphere holds an `A`-world). The "might" counterfactual `A ◇→ B` is the dual `¬(A □→ ¬B)`.

A `CounterfactualModel` takes the worlds, a `valuation` mapping each world to the set of atom keys (`atom.to_unicode_str()`) true there, and `spheres` mapping each world to its nested list of frozensets. A world omitted from `spheres` defaults to the single sphere `{w}`.

```python
from unicode_fol_kit.fol.nodes import Atom, Not, And
from unicode_fol_kit.semantics.conditional import CounterfactualModel, would, might

A, B, C = Atom("A", ()), Atom("B", ()), Atom("C", ())
# World 0 is actual; the closest A-world is 1 (A, B); a farther A∧C-world 2 has no B.
CF = CounterfactualModel(
    (0, 1, 2),
    {0: frozenset(), 1: frozenset({"A", "B"}), 2: frozenset({"A", "C"})},
    {0: [frozenset({0}), frozenset({0, 1}), frozenset({0, 1, 2})]},
)

would(CF, 0, A, B)                               # → True   (if A were, B would be)
would(CF, 0, A, Not(B))                          # → False
might(CF, 0, A, C)                               # → False  (the closest A-world, 1, is not C)
```

Antecedent strengthening fails — the hallmark non-monotonicity of counterfactuals. `A □→ B` can hold while `(A ∧ C) □→ B` does not, because narrowing the antecedent reaches into a more distant sphere:

```python
would(CF, 0, A, B)                               # → True
would(CF, 0, And(A, C), B)                       # → False  (the closest A∧C-world, 2, has no B)
```

Antecedents and consequents must be propositional (atoms and `¬ ∧ ∨ → ↔`); a quantifier or modal node raises `TypeError`.

## Circumscription / non-monotonic entailment

Classical entailment is monotonic: adding premises never retracts a conclusion. Circumscription (McCarthy) captures defeasible reasoning by believing only what holds in the minimal models of a theory — those making the circumscribed predicates as small as possible. `minimal_entails(premises, conclusion, circumscribed=…)` is `True` iff the conclusion holds in every ≤-minimal model. With `circumscribed=None` *all* predicates are minimised, giving closed-world-style semantics.

The search reuses the finite model finder, so it is **bounded** (domains up to `max_size`): `True` means minimal-model entailment over models within the bound, not a proof over all models.

```python
from unicode_fol_kit.fol.nodes import Atom, Not, Implies, Constant
from unicode_fol_kit.semantics.nonmonotonic import minimal_entails

a = Constant("a")
Pa, Qa = Atom("P", [a]), Atom("Q", [a])

# Nothing is asserted, so P is minimally empty: the closed-world ∅ ⊨_circ ¬P(a).
minimal_entails([], Not(Pa), circumscribed={"P"}, max_size=2)        # → True
```

The relation is genuinely non-monotonic — strengthening the premises can flip a `True` to `False`:

```python
# {P(a) → Q(a)} circumscriptively entails ¬Q(a), since Q is minimally empty...
minimal_entails([Implies(Pa, Qa)], Not(Qa),
                circumscribed={"P", "Q"}, max_size=2)                # → True
# ...but adding P(a) forces Q(a), retracting the conclusion.
minimal_entails([Implies(Pa, Qa), Pa], Not(Qa),
                circumscribed={"P", "Q"}, max_size=2)               # → False
```

`minimal_models(premises, circumscribed=…)` returns the underlying ≤-minimal `Structure`s if you want to inspect them directly.

## Out of scope

These four evaluators cover the non-classical neighbours the toolkit ships. Several others are deliberately **not** provided: relevant / relevance logic, hybrid logic (nominals and `@`), independence-friendly and dependence logic, and substructural logics (linear, the Lambek calculus, and friends). If you need one of those, the AST and the existing evaluators are a reasonable base to build on, but no first-class support exists today.
