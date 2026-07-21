# Dependence logic and IF logic (team semantics)

Dependence logic (Väänänen, *Dependence Logic*, 2007) and independence-friendly (IF) logic extend first-order logic with statements **about how values relate across many assignments at once**: "the value of `y` is a function of the value of `x`", or "a witness for `y` is chosen without seeing `x`". No single assignment can make such a statement true or false — so satisfaction is defined for a **team**, a *set* of assignments, and this page is about exactly that shift.

The toolkit's `dependence` parser mode (`MSFLParser(dependence=True)`) accepts literals, `∧`, the *splitting* `∨`, `∀`/`∃`, the **dependence atom** `=(t₁, …, tₙ)`, and the **slashed existential** `∃x/{y, …}`. There is deliberately no `→`/`↔` — they have no faithful team semantics in this fragment. Evaluation is Väänänen's *strict* team semantics over the same finite `Structure` the [Tarskian evaluator](classical-reasoning.md) uses:

| What | Function(s) | Module |
| --- | --- | --- |
| Team satisfaction `X ⊨ φ` | `team_satisfies(structure, team, formula)` | `unicode_fol_kit.semantics.team` |
| Sentence evaluation (team `{∅}`) | `team_models(structure, formula)` | `unicode_fol_kit.semantics.team` |

## Teams as information states

A team is a set of assignments — think of a **database table** whose columns are variables and whose rows are assignments. A team models an *information state*: the rows are the possibilities you cannot yet tell apart. First-order literals are **flat**: the team satisfies a literal iff every row does.

```python
from unicode_fol_kit import MSFLParser, Structure, team_satisfies

p = MSFLParser(dependence=True).parse

S = Structure(domain=[0, 1], predicates={("P", 1): {(0,)}})

team = [{"x": 0}, {"x": 1}]                  # two rows: x is undetermined

team_satisfies(S, team, p("P(x)"))           # → False  the row x=1 fails P
team_satisfies(S, team, p("¬P(x)"))          # → False  the row x=0 fails ¬P
team_satisfies(S, team, p("P(x) ∨ ¬P(x)"))   # → True   see "splitting ∨" below
```

Note the first two lines: on a mixed team, *neither* `P(x)` nor `¬P(x)` holds — team satisfaction is not two-valued, because a team can be genuinely undecided. Two boundary facts to keep in mind:

```python
team_satisfies(S, [], p("x ≠ x"))            # → True   the EMPTY team satisfies everything
team_satisfies(S, [{"x": 0}, {"x": 0}], p("=(x)"))   # → True   a team is a SET: duplicates collapse
```

The empty team is the information state with *no* remaining possibilities — every formula holds vacuously (the *empty-team property*). And every formula of dependence logic is **downward closed**: if `X ⊨ φ` then every subteam `Y ⊆ X` satisfies `φ` (Väänänen 2007, Prop. 3.10) — learning more never breaks what you knew.

## Dependence atoms are functional dependencies

The dependence atom `=(x, y)` says: **within this team, the value of `y` is a function of the value of `x`** — exactly a database *functional dependency* `x → y` on the table. With one argument, `=(x)` is the constancy atom: the `x` column holds a single value.

```python
# x determines y: the rows encode the function {0 ↦ 1, 1 ↦ 1}
team_satisfies(S, [{"x": 0, "y": 1}, {"x": 1, "y": 1}], p("=(x, y)"))  # → True

# x = 0 maps to two different y values — the dependency fails
team_satisfies(S, [{"x": 0, "y": 0}, {"x": 0, "y": 1}], p("=(x, y)"))  # → False

# constancy: =(x) fails when the column varies, holds when it does not
team_satisfies(S, [{"x": 0}, {"x": 1}], p("=(x)"))                     # → False
team_satisfies(S, [{"x": 1, "y": 0}, {"x": 1, "y": 1}], p("=(x)"))     # → True
```

Functional dependencies compose, just as in Armstrong's axioms: any team satisfying `=(x, y)` and `=(y, z)` satisfies `=(x, z)` (the test suite checks this exhaustively over all 256 teams on a two-element domain).

## The splitting disjunction

Team disjunction is not "one disjunct holds": `X ⊨ φ ∨ ψ` iff the team can be **split** into `X = Y ∪ Z` with `Y ⊨ φ` and `Z ⊨ ψ`. This is what made `P(x) ∨ ¬P(x)` true above — the team splits by `P`-membership. It also makes `∨` non-idempotent on dependence atoms:

```python
team = [{"x": 0}, {"x": 1}]
team_satisfies(S, team, p("=(x)"))           # → False
team_satisfies(S, team, p("=(x) ∨ =(x)"))    # → True   split into two constant halves!
```

`=(x) ∨ =(x)` says "the team is a union of two constant teams", i.e. the `x` column takes *at most two* values — a strictly weaker claim than `=(x)`. Counting continues by pigeonhole:

```python
S3 = Structure(domain=[0, 1, 2])
team3 = [{"x": 0}, {"x": 1}, {"x": 2}]
team_satisfies(S3, team3, p("=(x) ∨ =(x)"))          # → False  3 values, 2 constant parts
team_satisfies(S3, team3, p("=(x) ∨ =(x) ∨ =(x)"))   # → True
```

## Quantifiers, sentences, and the `|dom| = 1` example

A sentence is evaluated with `team_models`, starting from the team `{∅}` containing just the empty assignment (*not* the empty team — that one satisfies everything). `∀x` **duplicates** the team, extending every row with every domain element for `x`; `∃x` **supplements** it, choosing one witness per row (a function `F : X → dom`). Watch the dependence atom interact with `∃`:

```python
from unicode_fol_kit import team_models

S1 = Structure(domain=[0])
S2 = Structure(domain=[0, 1])

team_models(S2, p("∀x ∃y (y = x)"))            # → True   choose F(s) = s(x)
team_models(S2, p("∀x ∃y (=(y) ∧ y = x)"))     # → False
team_models(S1, p("∀x ∃y (=(y) ∧ y = x)"))     # → True   nothing left to vary
```

Worked through on `S2`: after `∀x` the team is `{{x↦0}, {x↦1}}`. Now `∃y` must pick a witness per row, but `=(y)` forces the *same* witness `c` for both rows, and `y = x` then demands `c = 0` **and** `c = 1`. So `∀x ∃y (=(y) ∧ y = x)` is true **iff the domain has exactly one element** — the dependence atom turned an always-true sentence into a domain-size probe.

## Slashed quantifiers and imperfect information

IF logic reaches the same effect through **imperfect information**: `∃y/{x} φ` chooses the witness for `y` *uniformly in* `x` — rows that agree on everything outside `{x, y}` must receive the same witness. Game-theoretically, the verifier picks `y` without being shown `x`:

```python
team_models(S2, p("∀x ∃y (y = x)"))        # → True
team_models(S2, p("∀x ∃y/{x} (y = x)"))    # → False  y may not look at x
team_models(S1, p("∀x ∃y/{x} (y = x)"))    # → True   with one element there is nothing to know
```

Uniformity forces a constant witness here: after `∀x`, the rows `{x↦0}` and `{x↦1}` agree on every variable outside `{x, y}` (vacuously — there are none), so `F` must be constant, which is exactly the `=(y)` sentence above. `∀x ∃y/{x} (y = x)` is true iff `|dom| = 1`.

The uniformity requirement is also exactly what makes **signalling** possible — an intermediate quantifier can leak the hidden variable back in:

```python
team_models(S2, p("∀x ∃z (z = x ∧ ∃y/{x} (y = x))"))   # → True   z signals x
```

Because `z = x`, the rows now *differ on `z`*, which is outside `{x, y}` — so the slashed witness may vary with `z`, hence effectively with `x`. This is the classic signalling phenomenon of IF logic: hiding `x` is worthless if a visible variable carries the same information.

## A genuine dependence sentence: the universal sink

On directed graphs (a binary `Edge` relation), the sentence

```text
∀x ∃y (=(y) ∧ Edge(x, y))
```

says: every vertex has an outgoing edge, **and the target is the same vertex for all of them** — i.e. some single vertex receives an edge from every vertex (a *universal sink*). The constancy atom upgrades the row-by-row witness of `∃y` into one global witness:

```python
SINK = Structure(
    domain=["a", "b", "c"],
    predicates={("Edge", 2): {("a", "c"), ("b", "c"), ("c", "c"), ("a", "b")}},
)
CYCLE = Structure(  # a → b → c → a: out-edges everywhere, no common target
    domain=["a", "b", "c"],
    predicates={("Edge", 2): {("a", "b"), ("b", "c"), ("c", "a")}},
)

sink = p("∀x ∃y (=(y) ∧ Edge(x, y))")
team_models(SINK, sink)                      # → True   every vertex points at c
team_models(CYCLE, sink)                     # → False

team_models(CYCLE, p("∀x ∃y Edge(x, y)"))    # → True   without =(y) the witness may vary
```

This particular pattern is still first-order expressible — `∀x ∃y (=(y) ∧ ψ)` says `∃y ∀x ψ` — which gives a nice differential check against the independent Tarskian evaluator:

```python
from unicode_fol_kit import models

fo = MSFLParser().parse("∃y ∀x Edge(x, y)")
(models(fo, SINK), models(fo, CYCLE))        # → (True, False) — agrees with team_models
```

In general, though, dependence atoms take you strictly beyond first-order logic: dependence logic has the full expressive power of existential second-order logic (Σ¹₁), so on finite structures it captures every NP graph property.

## Translating to existential second-order logic: `dependence_to_eso`

Väänänen's Σ¹₁ theorem is constructive: `dependence_to_eso(sentence)` realises the half that matters here, translating a dependence-logic sentence into a **classical** formula headed by existential second-order quantifiers — one `∃F` per Skolemised existential, `F` a fresh graph predicate playing the role of the witness function, plus the two first-order axioms making it total and functional. The result is an ordinary `Node` for `satisfies_so` / `hol.secondorder`, not a team-semantic object, so it is a genuine *alternative* evaluator to `team_models` rather than a wrapper around it:

```python
from unicode_fol_kit import MSFLParser, dependence_to_eso, Structure
from unicode_fol_kit.semantics.secondorder import holds
from unicode_fol_kit.semantics.team import team_models

dp = MSFLParser(dependence=True).parse
sink = dp("∀x ∃y (=(y) ∧ Edge(x, y))")        # the universal-sink sentence from above

eso = dependence_to_eso(sink)
eso.to_unicode_str()[:16]              # → '∃F_y (∃_F_y_y0 F'   (∃F, then its totality/functionality axioms, then the body)

# The two independent oracles agree on both structures from above:
holds(eso, SINK), team_models(SINK, sink)      # → (True, True)
holds(eso, CYCLE), team_models(CYCLE, sink)    # → (False, False)
```

**Only a documented fragment is covered** — this is a translation, not a general dependence-logic decision procedure. It faithfully handles plain first-order `∃` anywhere (ordinary Skolemisation), and a dependence-atom-guarded or slashed `∃` (the canonical Väänänen normal form `∃u(=(t̄,u) ∧ φ)`) **provided the sentence contains no `∨`** — team-semantic disjunction lets the team split into any partition, and once a dependence atom or slash is in play that split is exactly the source of dependence logic's extra power, so establishing a Skolem-normal-form equivalence for `∨` mixed with non-flat constructs is out of scope by design (the conservative choice: soundness over coverage). A "loose" dependence atom — one not a top-level conjunct of its own `∃`'s immediate body — and a shadowed variable name are both rejected too:

```python
loose = dp("∀x∃z(=(x,z) ∧ ∃y/{x}(=(z,y)))")    # the dependence atom guards z, not y
dependence_to_eso(loose)
# raises NotImplementedError: dependence_to_eso: the dependence atom '=(z, y)' does not
# guard its own existential. ... evaluate with team_satisfies / team_models instead.
```

Faithfulness is pinned by exhaustive structure-enumeration differentials against `team_models` over the covered fragment (the development process caught and fixed a real slashed-∃ scoping subtlety this way). Once translated, the sentence also feeds `hol.secondorder`'s Isabelle/THF exporters — a route to an unbounded proof attempt that `team_models`'s brute-force search cannot offer.

## The honest boundary

**Evaluation over finite structures only.** That Σ¹₁ expressive power has a hard flip side: the set of *valid* dependence-logic sentences is not recursively enumerable — not even arithmetical (Väänänen 2007, Ch. 6). No prover, tableau, or SMT export can exist for it, so the toolkit offers exactly what is decidable: brute-force model checking over finite structures. The witness searches are exponential; above a documented bound (`MAX_TEAM_SEARCH = 65536` candidates, i.e. domains up to 4 with teams up to 8 rows) they raise `ValueError` rather than hang.

The fragment boundaries are enforced with clear errors:

```python
p("=(x, y)").to_z3()          # raises NotImplementedError — no classical export exists
p("P ∧ Q → R")                # raises (parse error) — no → in the dependence mode
```

`team_satisfies` likewise rejects nodes outside the team fragment (`Implies`/`Iff` built programmatically, `¬` applied to anything but an atom, dual negation of `=(…)` or `∃x/{…}`, modal or fuzzy operators) with a `TypeError` naming the fragment. Contradictory-*looking* teams are not errors, though — they are information states, and the empty one satisfies everything.
