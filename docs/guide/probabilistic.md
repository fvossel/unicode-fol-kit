# Probabilistic logic

`unicode_fol_kit.prob` answers two different probabilistic questions, both
**exactly**: no sampling, no Monte Carlo, no approximation parameter. Results are
`fractions.Fraction`, so `1/3` is `1/3` and not `0.3333333333333333`.

The two questions are genuinely different, and picking the wrong one is the usual
source of confusion:

| Question | Module | Entry point |
|---|---|---|
| Premises constrain probabilities loosely. What can I *conclude*? | `prob.nilsson` | `entailment_bounds` |
| I have a generative program. What *is* the probability? | `prob.distribution` | `query` |

The first returns an interval, because the premises usually do not determine a
single number. The second returns one number, because the program does.

## Nilsson bounds: what the premises entail

A `ProbConstraint` is `lower ≤ P(formula) ≤ upper`, optionally conditional on
another formula. `entailment_bounds` returns the tightest interval for the
conclusion that every probability distribution consistent with the constraints
must respect.

```python
from fractions import Fraction
from unicode_fol_kit import MSFLParser
from unicode_fol_kit.prob import ProbConstraint, entailment_bounds

p = MSFLParser()
constraints = [
    ProbConstraint(p.parse("Rain"), Fraction(1, 2), Fraction(1, 2)),
    ProbConstraint(p.parse("Rain → Wet"), Fraction(9, 10), Fraction(1)),
]
bounds = entailment_bounds(constraints, p.parse("Wet"))
print(bounds.lower, bounds.upper)   # → 2/5 1
print(bounds.n_worlds)              # → 4
```

The lower bound is exactly what the premises force: `P(Wet) ≥ P(Rain) +
P(Rain → Wet) − 1 = 1/2 + 9/10 − 1 = 2/5`. The upper bound is 1 because nothing
in the premises stops it from raining-or-not and being wet anyway. An interval
this wide is not a weakness of the method — it is the honest content of the
premises, and a system that answered "0.45" would be inventing information.

`n_worlds` is the number of propositional valuations over the atoms involved:
the linear program has one variable per world, which is why `max_atoms` (12 by
default) is a real limit rather than a formality.

Constraints may be conditional:

```python
from fractions import Fraction
from unicode_fol_kit import MSFLParser
from unicode_fol_kit.prob import ProbConstraint, entailment_bounds

p = MSFLParser()
constraints = [
    ProbConstraint(p.parse("Wet"), Fraction(8, 10), Fraction(1),
                   given=p.parse("Rain")),          # P(Wet | Rain) ≥ 0.8
    ProbConstraint(p.parse("Rain"), Fraction(1, 2), Fraction(1, 2)),
]
b = entailment_bounds(constraints, p.parse("Wet"))
print(b.lower, b.upper)   # → 2/5 1
```

A constraint set that no distribution can satisfy is refused outright rather than
answered:

```python
from fractions import Fraction
from unicode_fol_kit import MSFLParser
from unicode_fol_kit.prob import ProbConstraint, entailment_bounds

p = MSFLParser()
try:
    entailment_bounds([ProbConstraint(p.parse("A"), Fraction(1), Fraction(1)),
                       ProbConstraint(p.parse("¬A"), Fraction(1), Fraction(1))],
                      p.parse("A"))
except ValueError as exc:
    print(str(exc)[:60])
# → entailment_bounds: probabilistically inconsistent — no proba
```

From inconsistent premises everything follows, so `[0, 1]` — or any other
interval — would be technically defensible and practically useless. The error is
the useful answer.

### A second, algorithm-only route: `strategy="column_generation"`

`entailment_bounds` takes a `strategy` keyword: `"direct"` (above, the default,
unchanged) or `"column_generation"` — a different ALGORITHM for the same exact
bounds, never a different answer:

```python
from fractions import Fraction
from unicode_fol_kit import MSFLParser
from unicode_fol_kit.prob import ProbConstraint, entailment_bounds

p = MSFLParser()
constraints = [
    ProbConstraint(p.parse("Rain"), Fraction(1, 2), Fraction(1, 2)),
    ProbConstraint(p.parse("Rain → Wet"), Fraction(9, 10), Fraction(1)),
]
bounds = entailment_bounds(constraints, p.parse("Wet"), strategy="column_generation")
print(bounds.lower, bounds.upper)   # → 2/5 1
```

Same `2/5 1` as `strategy="direct"` above — the two strategies must agree exactly
(`Fraction` equality, never a tolerance) on every problem either can answer, which
is what `tests/test_nilsson_colgen.py` checks directly, differentially, on a large
battery of cases. `"direct"` builds one probability variable per possible world
(`2^n`, hence `max_atoms`); `"column_generation"` never does — it grows a small
subset of worlds on demand, deciding which one to add next via an exact Z3
Boolean-SAT search over the `n` atoms directly (see
`unicode_fol_kit.prob._column_gen`'s module docstring for the algorithm and its
termination/optimality proof), so it can answer problems with far more than
`max_atoms` distinct atoms — its own brake is `max_columns` (500 by default)
instead:

```python
from fractions import Fraction
from unicode_fol_kit.fol.nodes import Atom, And
from unicode_fol_kit.prob import ProbConstraint, entailment_bounds

# 15 independent components, each 99% reliable on its own, no other
# constraint linking them: what is P(every one of them is up at once)?
k = 15
components = [Atom(f"Up{i}", ()) for i in range(k)]
constraints = [ProbConstraint.exact(components[i], Fraction(99, 100)) for i in range(k)]
all_up = components[0]
for c in components[1:]:
    all_up = And(all_up, c)

try:
    entailment_bounds(constraints, all_up)
except ValueError as exc:
    print(str(exc)[:58])
# → entailment_bounds: 15 distinct atoms exceeds max_atoms=12.

bounds = entailment_bounds(constraints, all_up, strategy="column_generation")
print(bounds.lower, bounds.upper)   # → 17/20 99/100
```

`99/100` is the trivial upper bound (`P(∧) ≤ min P(component)`, achieved by
correlating every failure into the same rare event). `17/20` is the Fréchet/
Bonferroni lower bound `max(0, k·p − (k−1)) = max(0, 15·0.99 − 14) = 0.85`: with
only 15 independent-looking marginals and nothing else constraining them, the
LP cannot rule out that the components' failures are spread out just enough to
cover every world at least once — an honest interval, not `0.99**15` (that
narrower number needs an INDEPENDENCE assumption `entailment_bounds` is
deliberately not told to make; `prob.distribution.query`, below, is the entry
point for when the premises really are "these facts are independent").

## Distribution semantics: what the program says

A `ProbProgram` is the ProbLog-style setup: independent Bernoulli facts, definite
rules, and optional hard facts. `query` sums the probabilities of the worlds in
which the goal holds.

```python
from fractions import Fraction
from unicode_fol_kit import MSFLParser
from unicode_fol_kit.prob import ProbFact, ProbProgram, query

p = MSFLParser()
program = ProbProgram(
    facts=[ProbFact(p.parse("Rain"), Fraction(3, 10)),
           ProbFact(p.parse("Sprinkler"), Fraction(1, 5))],
    rules=[p.parse("Rain → Wet"), p.parse("Sprinkler → Wet")],
)
print(query(program, p.parse("Wet")))          # → 11/25
print(float(query(program, p.parse("Wet"))))   # → 0.44
```

`11/25 = 0.44 = 1 − (1 − 3/10)(1 − 1/5)`: the two causes are independent, so the
probability of *neither* firing is the product, and `Wet` is everything else.
Note that this is a single number, not an interval — the program fixes the joint
distribution, whereas the Nilsson constraints above left it open.

`hard_facts` are certainties rather than probabilistic choices:

```python
from fractions import Fraction
from unicode_fol_kit import MSFLParser
from unicode_fol_kit.prob import ProbFact, ProbProgram, query

p = MSFLParser()
program = ProbProgram(facts=[ProbFact(p.parse("Rain"), Fraction(3, 10))],
                      rules=[p.parse("Rain → Wet")],
                      hard_facts=[p.parse("Sprinkler")])
print(query(program, p.parse("Sprinkler")))   # → 1
print(query(program, p.parse("Wet")))         # → 3/10
```

`Sprinkler` is certain, but no rule connects it to `Wet` in this program, so
`P(Wet)` is exactly `P(Rain)`. Rules are material implications over the sampled
world, not a licence to invent influence.

`max_choice_facts` (16 by default) bounds the enumeration for the same reason
`max_atoms` does above: the world set is exponential in the number of independent
choices, and an exact method has to say where it stops rather than quietly
switching to sampling.

### A second, compiled route: `method="compile"`

`query` takes a `method` keyword: `"enumerate"` (the default, described above,
unchanged) or `"compile"` — a different ALGORITHM for the same exact number,
never a different answer. Instead of summing `2^k` total choices, it builds one
shared Boolean-decision-diagram function per derivable atom and weighted-model-
counts a single composed result, so a program with many shared sub-derivations
can collapse to far fewer diagram nodes than choices:

```python
from fractions import Fraction
from unicode_fol_kit import MSFLParser
from unicode_fol_kit.prob import ProbFact, ProbProgram, query

p = MSFLParser()
program = ProbProgram(
    facts=[ProbFact(p.parse("Rain"), Fraction(3, 10)),
           ProbFact(p.parse("Sprinkler"), Fraction(1, 5))],
    rules=[p.parse("Rain → Wet"), p.parse("Sprinkler → Wet")],
)
print(query(program, p.parse("Wet"), method="compile"))   # → 11/25
```

Same `11/25` as `method="enumerate"` above — the two routes must agree exactly
(`Fraction` equality, never a tolerance) on every program either can answer;
that agreement is the whole point of having a second algorithm, and is what the
test suite checks directly. `method="compile"` is bounded by its own brake,
`max_bdd_nodes` (100 000 by default; `max_choice_facts` does not apply to it),
because weighted model counting is `#P`-hard — but for programs whose choices
share a lot of structure, `"compile"` can answer well past `max_choice_facts`
where `"enumerate"` would refuse outright:

```python
from fractions import Fraction
from unicode_fol_kit.fol.nodes import Atom, And, Implies
from unicode_fol_kit.prob import ProbFact, ProbProgram, query

# A chain of 20 independent facts, each gating the next: derivable only if
# EVERY fact fires, so P = p0 * p1 * ... * p19 exactly (product rule).
facts = [ProbFact(Atom(f"F{i}", ()), Fraction(1, 2)) for i in range(20)]
d = [Atom(f"D{i}", ()) for i in range(20)]
rules = [Implies(facts[0].atom, d[0])]
rules += [Implies(And(d[i - 1], facts[i].atom), d[i]) for i in range(1, 20)]
program = ProbProgram(facts=facts, rules=rules)

query(program, d[-1])                    # -> ValueError: 20 > max_choice_facts=16
query(program, d[-1], method="compile")  # -> 1/1048576  ( = (1/2)**20 )
```

## Over MCP

Both routes are exposed as MCP tools — `probability_bounds` and
`probability_query` — with the same exact semantics; see {doc}`mcp`.
