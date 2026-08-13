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

## Over MCP

Both routes are exposed as MCP tools — `probability_bounds` and
`probability_query` — with the same exact semantics; see {doc}`mcp`.
