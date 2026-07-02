# Further Non-Classical Logics

New in 0.9.0: four small semantic evaluators for logics that sit just outside classical FOL — free logic, public-announcement (dynamic epistemic) logic, counterfactual conditionals, and circumscriptive non-monotonic entailment. Each builds an AST with the node constructors from `unicode_fol_kit.fol.nodes` and evaluates it against an explicit, hand-built model.

## Free logic

Classical FOL assumes every term denotes an existing individual, so universal instantiation `∀x φ → φ(c)` and existential generalisation `φ(c) → ∃x φ` are valid. Free logic drops that assumption: quantifiers range only over an inner `existing` domain `E ⊆ outer`, while constants may denote a merely-possible object of the wider `outer` domain — or fail to denote at all. The existence predicate `E!(t)` says "`t` denotes an existing object", and the classical rules hold only in their guarded forms `(∀x φ ∧ E!(c)) → φ(c)`.

A `FreeModel` carries the `outer` tuple, the `existing` inner subset, a (possibly partial) constant/function interpretation — a name absent from `constants` is non-denoting — and predicate tables over `outer`. Two policies govern an atom containing a non-denoting term: `"negative"` (default) makes it simply false (so `t = t` also fails), while `"positive"` keeps self-identity `t = t` true for any term.

```python
from unicode_fol_kit.fol.nodes import Atom, And, Implies, Quantifier, Variable, Constant
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

`free_satisfies(formula, model, assignment, policy)` is the open-formula form; `free_holds` is the convenience wrapper for a closed formula under the empty assignment. Pass an `assignment` to evaluate a formula with free variables — note that a variable can be bound to a *non-existing* outer element, since the assignment is not restricted to the inner domain:

```python
from unicode_fol_kit.semantics.free_logic import free_satisfies

m_open = FreeModel(outer=(0, 1), existing=frozenset({0}),
                   predicates={("P", 1): frozenset({(1,)})})
free_satisfies(Px(x), m_open, {"x": 1})         # → True   (x ↦ 1, a merely-possible object in P)
free_satisfies(Px(x), m_open, {"x": 0})         # → False  (x ↦ 0, which is not in P)
```

An unknown policy is rejected up front:

```python
free_satisfies(Px(x), m_open, {"x": 1}, policy="supervaluation")   # raises ValueError: unknown policy
```

### Guarded inference rules are valid

Free logic keeps universal instantiation and existential generalisation in their *guarded* forms — `(∀x φ ∧ E!(c)) → φ(c)` and `(φ(c) ∧ E!(c)) → ∃x φ`. Both come out valid even on a model where the bare (unguarded) rules fail:

```python
guarded_ui = Implies(And(all_P, Atom("E!", [c])), Px(c))   # (∀x P(x) ∧ E!(c)) → P(c)
free_holds(guarded_ui, m)                       # → True   (the guard E!(c) is false, so the implication holds)

# A model where c denotes an *existing* P-object — now E!(c) is true and the rule fires.
m_ex = FreeModel(outer=(0, 1), existing=frozenset({0, 1}), constants={"c": 1},
                 predicates={("P", 1): frozenset({(1,)})})
free_holds(Atom("E!", [c]), m_ex)               # → True
free_holds(Px(c), m_ex)                          # → True
guarded_eg = Implies(And(Px(c), Atom("E!", [c])), Quantifier("∃", x, Px(x)))
free_holds(guarded_eg, m_ex)                    # → True   (guarded EG: P(c) ∧ E!(c) → ∃x P(x))
```

Without the guard, existential generalisation breaks when the witness does not exist — `P(c)` can be true while `∃x P(x)` is false:

```python
m_ng = FreeModel(outer=(0, 1), existing=frozenset({0}), constants={"c": 1},
                 predicates={("P", 1): frozenset({(1,)})})
free_holds(Px(c), m_ng)                          # → True   (c denotes 1, and 1 is a P)
free_holds(Quantifier("∃", x, Px(x)), m_ng)     # → False  (no *existing* object is a P)
free_holds(Implies(Px(c), Quantifier("∃", x, Px(x))), m_ng)   # → False  (unguarded EG fails)
```

### Partial functions: non-denoting function terms

A function term is non-denoting when any argument is non-denoting, or when the partial table has no entry for the argument tuple. A non-denoting function term then behaves exactly like a non-denoting constant — an ordinary predicate over it is false, and `E!` of it is false:

```python
from unicode_fol_kit.fol.nodes import Function

f_c = Function("f", [c])                          # f(c)
# f maps the existing object 0 to the merely-possible object 1.
m_fn = FreeModel(outer=(0, 1), existing=frozenset({0}), constants={"c": 0},
                 functions={("f", 1): {(0,): 1}},
                 predicates={("P", 1): frozenset({(0,)})})
free_holds(Atom("E!", [f_c]), m_fn)             # → False  (f(c) = 1, which does not exist)
free_holds(Px(f_c), m_fn)                        # → False  (1 ∉ P; and even non-denoting → false)

# A missing table entry makes the application non-denoting outright.
m_gap = FreeModel(outer=(0, 1), existing=frozenset({0, 1}), constants={"c": 0},
                  functions={("f", 1): {}})       # f has no value at 0
free_holds(Atom("P", [f_c]), m_gap)             # → False  (f(c) has no referent at all)
```

### Function composition and chained partial applications

Partial functions propagate non-denotation when composed. If `f(x)` is non-denoting, then any application of a second function to `f(x)` is also non-denoting, even if the second function itself is total on existing objects:

```python
g = lambda t: Function("g", [t])

# Build a model where f is defined but sends 0 to a non-existing object,
# and g is defined only on 1 (an existing object).
m_chain = FreeModel(
    outer=(0, 1, 2),
    existing=frozenset({0, 1}),
    constants={"c": 0},
    functions={
        ("f", 1): {(0,): 2},      # f(0) → 2 (merely-possible)
        ("g", 1): {(1,): 0}       # g defined only at 1 (existing)
    },
    predicates={("P", 1): frozenset({(0,), (1,), (2,)})}
)

# E!(f(c)) is false because f(c)=2, which does not exist
free_holds(Atom("E!", [f_c]), m_chain)          # → False
# So E!(g(f(c))) is also false — the innermost application is non-denoting
free_holds(Atom("E!", [g(f_c)]), m_chain)       # → False
# And P(g(f(c))) is false (non-denoting term in predicate)
free_holds(Atom("P", [g(f_c)]), m_chain)        # → False
```

### Quantifying over non-existing objects

Variables can range over the full outer domain (existing and merely-possible), independent of whether a particular binding refers to an existing object. This enables reasoning about generic properties of all objects, or specific exceptional cases:

```python
y = Variable("y")

# ∃y E!(y) — there exists some existing object
m_exist = FreeModel(outer=(0, 1), existing=frozenset({0}), constants={},
                    predicates={})
free_holds(Quantifier("∃", y, Atom("E!", [y])), m_exist)   # → True

# Quantify over outer domain; some quantified individuals do not exist
Fy = lambda: Atom("F", [y])
m_mixed = FreeModel(outer=(0, 1, 2), existing=frozenset({0, 1}),
                    constants={}, predicates={("F", 1): frozenset({(0,), (1,), (2,)})})
free_holds(Quantifier("∀", y, Fy()), m_mixed)    # → True  (all outer objects in F)
free_holds(Quantifier("∀", y, Atom("E!", [y])), m_mixed)   # → False (not all are existing)
```

### Large domains: outer vs existing

Real-world applications often have a small existential domain but large outer domain (representing possibilities, abstract entities, etc.):

```python
# A thousand possible worlds or entities, but only ten that actually exist
m_large = FreeModel(
    outer=tuple(range(1000)),
    existing=frozenset({0, 1, 2, 3, 4, 5, 6, 7, 8, 9}),
    constants={"actual": 0},
    predicates={("Real", 1): frozenset({(i,) for i in range(10)})}
)

free_holds(Quantifier("∀", y, Atom("Real", [y])), m_large)   # → False (many merely-possible objects)
free_holds(Atom("Real", [Constant("actual")]), m_large)      # → True
```

### The policy split on an ordinary predicate

The `"negative"`/`"positive"` distinction only ever changes the verdict on **self-identity** `t = t` of a non-denoting term; every *other* atom with a non-denoting term is false under both policies. Compare an ordinary predicate against identity for a non-denoting constant `k` (absent from `constants`):

```python
k = Constant("k")                                 # k is non-denoting in m below
m_k = FreeModel(outer=(0, 1), existing=frozenset({0}), constants={"c": 1},
                predicates={("P", 1): frozenset({(0,)})})

free_holds(Px(k), m_k, policy="negative")        # → False
free_holds(Px(k), m_k, policy="positive")        # → False  (ordinary predicates agree)
free_holds(Atom("=", [k, k]), m_k, policy="negative")    # → False  (nothing is self-identical)
free_holds(Atom("=", [k, k]), m_k, policy="positive")    # → True   (self-identity preserved)
```

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

### Inspecting the updated model

`announce` returns a brand-new `KripkeModel` (the inputs are never mutated); every relation and the valuation are cut down to the survivors, so you can inspect the result with the ordinary `KripkeModel` accessors:

```python
upd = announce(M, p)                              # M|p
sorted(upd.worlds)                               # → [0]              (world 1 dropped)
sorted(upd.relations["K:a"])                     # → [(0, 0)]         (edges to/from 1 gone)
sorted(upd.successors("K:a", 0))                 # → [0]              (a's only candidate is the actual world)
sorted(upd.atoms_true_at(0))                     # → ['p']            (valuation carried over)
```

Announcing a formula that is already established is idempotent — re-announcing `p` after `M|p` changes nothing:

```python
twice = announce(announce(M, p), p)
sorted(twice.worlds)                             # → [0]
```

### Box vs diamond: vacuity and duality

`box_announce` is the PAL box `[φ!]ψ`; `diamond_announce` is its dual `⟨φ!⟩ψ`. At a world where the announcement is **false**, an untruthful announcement is simply not made: the box is vacuously true and the diamond is false. World 1 above is a `¬p` world:

```python
satisfies_modal(p, M, 1)                          # → False  (p is false at world 1)
box_announce(M, 1, p, Not(Kap))                   # → True   ([p!]ψ vacuously, p not truthful here)
diamond_announce(M, 1, p, Kap)                    # → False  (⟨p!⟩ψ needs a truthful announcement)
```

The duality `⟨φ!⟩ψ ≡ φ ∧ ¬[φ!]¬ψ` holds pointwise:

```python
lhs = diamond_announce(M, 0, p, Kap)
rhs = satisfies_modal(p, M, 0) and not box_announce(M, 0, p, Not(Kap))
lhs == rhs                                        # → True
```

### A two-agent scenario

With two agents who each see a different fact, a public announcement can teach one agent something the other already knew. Four worlds enumerate the truth values of `p` and `q`; agent `a` can tell `q`'s value apart (so `a` knows `q`) and agent `b` can tell `p`'s value apart (so `b` knows `p`):

```python
q = Atom("q", ())
worlds = [0, 1, 2, 3]                             # 0={p,q} 1={p} 2={q} 3={}
val = {0: {"p", "q"}, 1: {"p"}, 2: {"q"}, 3: set()}
Ka = {(0, 0), (0, 2), (2, 0), (2, 2), (1, 1), (1, 3), (3, 1), (3, 3)}   # a confuses worlds that differ only in p
Kb = {(0, 0), (0, 1), (1, 0), (1, 1), (2, 2), (2, 3), (3, 2), (3, 3)}   # b confuses worlds that differ only in q
M2 = KripkeModel(worlds, {"K:a": Ka, "K:b": Kb}, val)

satisfies_modal(Knows("a", q), M2, 0)            # → True   (a already knows q)
satisfies_modal(Knows("a", p), M2, 0)            # → False  (a does not know p)
box_announce(M2, 0, q, Knows("a", p))            # → False  (announcing q does not tell a about p)
box_announce(M2, 0, p, Knows("a", p))            # → True   (...but announcing p does)
```

The relation key `"K:a"` is the epistemic accessibility relation for agent `a`; see {doc}`modal` for the full relation-name convention.

### Multi-agent knowledge updates and chain announcements

Public announcements compose: announcing one fact, then another, progressively constrains the shared model. A classic puzzle involves secret information revealed step by step:

```python
# Three agents; p and q are initially unknown to some
r = Atom("r", ())
worlds_3a = [0, 1, 2, 3]  # 0={p,q,r} 1={p,q} 2={p} 3={}
val_3a = {0: {"p", "q", "r"}, 1: {"p", "q"}, 2: {"p"}, 3: set()}

Ka_3a = {(0, 0), (0, 1), (1, 0), (1, 1), (2, 2), (3, 3)}   # a knows p
Kb_3a = {(0, 0), (0, 2), (2, 0), (2, 2), (1, 1), (3, 3)}   # b knows q
Kc_3a = {(0, 0), (0, 3), (3, 0), (3, 3), (1, 1), (2, 2)}   # c knows r

M_3a = KripkeModel(worlds_3a, {"K:a": Ka_3a, "K:b": Kb_3a, "K:c": Kc_3a}, val_3a)

# Before announcement
satisfies_modal(Knows("a", p), M_3a, 0)         # → True (a knows p)
satisfies_modal(Knows("b", q), M_3a, 0)         # → True (b knows q)
satisfies_modal(Knows("c", Not(r)), M_3a, 0)    # → False (c does not know ¬r)

# Announce p: worlds without p (1,3) are dropped
M_after_p = announce(M_3a, p)
sorted(M_after_p.worlds)                        # → [0, 2] (1, 3 removed)

# After announcing p, c learns something
satisfies_modal(Knows("c", Not(r)), M_after_p, 0)    # → True (now c knows ¬r)

# Announce q: further constrains the survivors
M_after_pq = announce(M_after_p, q)
sorted(M_after_pq.worlds)                       # → [0] (only 0 has both p and q)
```

### Vacuous announcements and untruthful scenarios

An announcement that is false at the current world does not occur; the model is unchanged in the PAL semantics. This is distinct from announcing its negation:

```python
# World 1 has only p, not q
satisfies_modal(q, M2, 1)                       # → False
# Announcing q (false here) is vacuous: the box is trivially true
box_announce(M2, 1, q, Not(Kap))                # → True
# But diamond (which requires the announcement to be truthful) is false
diamond_announce(M2, 1, q, Knows("a", q))       # → False

# Announcing ¬q (which IS true at 1) works normally
box_announce(M2, 1, Not(q), Knows("a", Not(q))) # → True (after dropping p-worlds)
```

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

### Complex sphere systems and multi-layer counterfactuals

More intricate models can represent graded similarity. A world\s sphere system is a nested list, so you can express "closest", "next-closest", and so on:

```python
A, B, C, D = Atom("A", ()), Atom("B", ()), Atom("C", ()), Atom("D", ())
# Rich structure: worlds at different layers of similarity
CF_layers = CounterfactualModel(
    (0, 1, 2, 3, 4),
    {
        0: frozenset(),           # actual world, no atoms true
        1: frozenset({"A", "B"}),
        2: frozenset({"A", "C"}),
        3: frozenset({"A", "D"}),
        4: frozenset({"B", "C", "D"})
    },
    {0: [
        frozenset({0}),                    # layer 0: only the actual world
        frozenset({0, 1}),                 # layer 1: actual + world 1
        frozenset({0, 1, 2}),              # layer 2: actual, 1, 2
        frozenset({0, 1, 2, 3}),           # layer 3: actual, 1, 2, 3
        frozenset({0, 1, 2, 3, 4})         # layer 4: all worlds
    ]}
)

# The closest A-world is 1 (in layer 1)
would(CF_layers, 0, A, B)                        # → True
# But if we look at the next layer of A-worlds (2 and 3), not all have B
would(CF_layers, 0, And(A, Not(B)), Not(C))      # → False

# "Might" allows any closest A-world to witness the consequent
might(CF_layers, 0, A, Or(B, Or(C, D)))              # → True
```

### Disjunctive antecedents and complex consequents

Counterfactuals work with propositional formulas of arbitrary complexity (¬, ∧, ∨, →, ↔). Test complex reasoning chains:

```python
E = Atom("E", ())
# (A ∨ D) □→ (B ∧ E): "if A or D were, then B and E would both be"
would(CF_layers, 0, Or(A, D), And(B, E))        # → False (world 1 is A but not E)
would(CF_layers, 0, Or(A, D), B)                # → False (world 3 is A but not B)

# Conditional consequent: (A → B) in the closest world
would(CF_layers, 0, A, Implies(Not(A), B))      # → True (1 has A and B, so the conditional holds)
```

Antecedent strengthening fails — the hallmark non-monotonicity of counterfactuals. `A □→ B` can hold while `(A ∧ C) □→ B` does not, because narrowing the antecedent reaches into a more distant sphere:

```python
would(CF, 0, A, B)                               # → True
would(CF, 0, And(A, C), B)                       # → False  (the closest A∧C-world, 2, has no B)
```

### "Would" vs "might"

`might` is defined as the dual `A ◇→ B ≡ ¬(A □→ ¬B)`. On the model above, the closest `A`-world (world 1) is a `B`-world but not a `C`-world, so "if A were, B might hold" but "if A were, C might hold" fails:

```python
might(CF, 0, A, B)                               # → True   (¬(A □→ ¬B): the closest A-world is B)
might(CF, 0, A, C)                               # → False  (the closest A-world, 1, is not C)
would(CF, 0, A, Not(B)) == (not might(CF, 0, A, B))   # → True   (would-not is exactly not-might)
```

A genuine tie inside one sphere — two equally-close `A`-worlds, one `B` and one not — separates "would" from "might": neither all nor none of the closest `A`-worlds are `B`:

```python
CF_tie = CounterfactualModel(
    (0, 1, 2),
    {0: frozenset(), 1: frozenset({"A", "B"}), 2: frozenset({"A"})},
    {0: [frozenset({0}), frozenset({0, 1, 2})]},   # 1 and 2 are equally close
)
would(CF_tie, 0, A, B)                           # → False  (world 2 is an A-world without B)
might(CF_tie, 0, A, B)                           # → True   (world 1 is an A-world with B)
```

### Vacuous truth and the default sphere

If **no** sphere of the world contains an `A`-world, `A □→ B` is vacuously true for *any* `B`, and the matching "might" is false:

```python
CF_vac = CounterfactualModel(
    (0, 1),
    {0: frozenset(), 1: frozenset({"B"})},         # no world makes A true
    {0: [frozenset({0}), frozenset({0, 1})]},
)
would(CF_vac, 0, A, B)                           # → True   (vacuous: no A-world anywhere)
would(CF_vac, 0, A, Not(B))                      # → True   (vacuous either way)
might(CF_vac, 0, A, B)                           # → False  (no A-world, so no "might")
```

A world omitted from `spheres` defaults to the single sphere `{w}`, so a one-world model evaluates the counterfactual at the world itself:

```python
CF_def = CounterfactualModel((0,), {0: frozenset({"A", "B"})}, {})   # spheres default to [{0}]
would(CF_def, 0, A, B)                           # → True   (0 is its own closest A-world, and B holds there)
```

Antecedents and consequents must be propositional (atoms and `¬ ∧ ∨ → ↔`); a quantifier or modal node raises `TypeError`:

```python
from unicode_fol_kit.fol.nodes import Quantifier, Variable
would(CF, 0, Quantifier("∀", Variable("x"), A), B)   # raises TypeError: must be propositional
```

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

### Inspecting the minimal models

`minimal_models(premises, circumscribed=…)` returns the underlying ≤-minimal `Structure`s so you can read off domains, constants and predicate extensions. For `{P(a) → Q(a)}` circumscribing both `P` and `Q`, the unique minimal model makes both predicates empty (vacuously satisfying the implication), which is exactly why `¬Q(a)` is entailed:

```python
from unicode_fol_kit.semantics.nonmonotonic import minimal_models

for struct in minimal_models([Implies(Pa, Qa)], circumscribed={"P", "Q"}, max_size=1):
    print(struct.domain, dict(struct.constants),
          {k: sorted(v) for k, v in struct.predicates.items()})
# → (0,) {'a': 0} {('P', 1): [], ('Q', 1): []}
```

### Closed-world reasoning (and the unique-names caveat)

Circumscribing a predicate makes it false of everything not forced true — the closed-world assumption. Assert `P(a)` and circumscribe `P`; then `P(a)` stays entailed but anything *not* asserted is minimally false. With `circumscribed=None` *every* predicate is minimised, so an empty theory entails `¬P(a)`:

```python
from unicode_fol_kit.fol.nodes import Or

minimal_entails([Pa], Pa, circumscribed={"P"}, max_size=2)           # → True   (asserted)
minimal_entails([], Not(Pa), circumscribed=None, max_size=2)         # → True   (closed-world: nothing is P)
```

A subtlety worth internalising: the search is over **bounded finite models with no unique-names assumption**, so two constants may denote the *same* object. Asserting `P(a)` does **not** by itself entail `¬P(b)` — there is a minimal model where `a` and `b` collapse to one `P`-object:

```python
b = Constant("b")
Pb = Atom("P", [b])
minimal_entails([Pa], Not(Pb), circumscribed={"P"}, max_size=2)      # → False  (a and b may coincide)
# Force them apart and the closed-world conclusion returns.
minimal_entails([Pa, Not(Atom("=", [a, b]))], Not(Pb),
                circumscribed={"P"}, max_size=2)                     # → True
```

### Disjunction splits into incomparable minima

A disjunctive premise has two minimal models (one for each disjunct), so neither disjunct is entailed on its own — but the disjunction is:

```python
minimal_entails([Or(Pa, Pb)], Pa, circumscribed={"P"}, max_size=2)          # → False
minimal_entails([Or(Pa, Pb)], Or(Pa, Pb), circumscribed={"P"}, max_size=2)  # → True
```

### Comparing minimal models across domain sizes

Minimal models are found independently at each domain size (1, 2, 3, …). Models are grouped by their "fixed part" — shared constants, functions, and non-circumscribed predicates — and only models that are minimal *within their group* are returned. This allows reasoning with a tight domain bound:

```python
c = Constant("c")
theory_ab = [Implies(Atom("P", [a]), Atom("P", [b])), Atom("P", [c])]

models_list = minimal_models(theory_ab, circumscribed={"P"}, max_size=2)
print(f"Number of minimal models: {len(models_list)}")
for i, m in enumerate(models_list):
    P_ext = sorted(m.predicates.get(("P", 1), set()))
    print(f"  Model {i}: domain {m.domain}, P = {P_ext}")
# → Number of minimal models: 4
#   Model 0: domain (0,), P = [(0,)]
#   Model 1: domain (0, 1), P = [(0,), (1,)]
#   ...etc
```

### Quantified rules and existential bases

Theories with quantified rules combine non-monotonicity with first-order quantification. A rule "all Ps are Qs" with P minimised can express defaults that are retracted as examples accumulate:

```python
Bird = lambda t: Atom("Bird", [t])
Flies = lambda t: Atom("Flies", [t])
Ab_flies = lambda t: Atom("Ab_flies", [t])

robin, ostrich = Constant("robin"), Constant("ostrich")

# Rule: birds fly unless abnormal; Robin is a bird
rules = [
    Quantifier("∀", x, Implies(And(Bird(x), Not(Ab_flies(x))), Flies(x))),
    Bird(robin),
    Bird(ostrich)
]

# By default (Ab_flies minimised), both fly
minimal_entails(rules, Flies(robin), circumscribed={"Ab_flies"}, max_size=2)   # → True
minimal_entails(rules, Flies(ostrich), circumscribed={"Ab_flies"}, max_size=2)  # → True

# Learn ostrich does not fly → mark it abnormal
rules_fact = rules + [Not(Flies(ostrich))]
minimal_entails(rules_fact, Flies(robin), circumscribed={"Ab_flies"}, max_size=2)   # → True
minimal_entails(rules_fact, Flies(ostrich), circumscribed={"Ab_flies"}, max_size=2)  # → False
```

### Default reasoning: assume-normal, then retract

The canonical use is an *abnormality* predicate `Ab`: circumscribe it to assume nothing is abnormal by default, and let new facts force exceptions. An empty theory assumes a fixed individual is normal; learning it is abnormal — directly, or via a rule like "penguins are abnormal" — retracts that conclusion:

```python
from unicode_fol_kit.fol.nodes import Quantifier, Variable

x, tweety = Variable("x"), Constant("tweety")
Ab = lambda t: Atom("Ab", [t])

# By default, assume tweety is normal (Ab minimised to empty).
minimal_entails([], Not(Ab(tweety)), circumscribed={"Ab"}, max_size=2)       # → True
# Learn it is abnormal → the default is retracted (non-monotonic).
minimal_entails([Ab(tweety)], Not(Ab(tweety)), circumscribed={"Ab"}, max_size=2)   # → False

# Or derive abnormality from a rule: penguins are abnormal, and tweety is a penguin.
penguins_abnormal = Quantifier("∀", x, Implies(Atom("Penguin", [x]), Ab(x)))
theory = [penguins_abnormal, Atom("Penguin", [tweety])]
minimal_entails(theory, Ab(tweety), circumscribed={"Ab"}, max_size=2)        # → True
minimal_entails(theory, Not(Ab(tweety)), circumscribed={"Ab"}, max_size=2)   # → False
```

```{note}
This is **parallel** circumscription: every named predicate is minimised on an equal footing, and the *non*-circumscribed predicates are held fixed (models are compared only when their fixed parts agree). It is **not** prioritised circumscription with *varied* predicates, so the textbook "Tweety the bird flies by default" pattern — which lets a derived `Flies` predicate float while `Ab` is minimised — is **not** captured: circumscribe the abnormality predicate(s) and reason about *them*, as above, rather than expecting a separate consequence predicate to be pinned for free.
```

## Further non-classical families

These four evaluators cover one cluster of non-classical neighbours. The families that used to be listed here as out of scope now have first-class support of their own: {doc}`relevant logic <relevant>` (Routley–Meyer semantics for the basic system B), {doc}`hybrid logic <hybrid>` (nominals and `@` in the modal mode), {doc}`dependence / IF logic <dependence>` (team semantics), and {doc}`substructural logics <substructural>` (intuitionistic linear logic and the Lambek calculus, each with a sequent prover).
