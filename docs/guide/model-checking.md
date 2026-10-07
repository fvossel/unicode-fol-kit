# Model checking: is this true *here*?

Most of this guide asks whether a formula is **valid** — true in every structure —
or whether a set of premises is satisfiable *somewhere*. This page asks the
opposite question: you already **have** a structure, and you want to know whether
a sentence holds *in it*.

That is model **checking**, not model **finding**, and the difference matters as
soon as the structure comes from real data. A molecule, a knowledge graph, a
parsed scene description — each is one concrete finite structure. Asking a model
*finder* to check it means asking a search procedure to rediscover something you
already know, which is why the natural-sounding route through a prover is orders
of magnitude slower than simply evaluating the formula.

```{note}
There are two structure classes in the kit and they answer different questions.
{class}`~unicode_logic_kit.semantics.tarski.Structure` (exported top-level as
`Structure`) is the general Tarskian model: functions, constants, every node type,
quantifiers iterating the whole domain. `FiniteStructure` — this page — is the
indexed relational one, built for large domains and formulas that mention only a
few individuals each. On the fragment both accept they agree; the model-checking
tests cross-check `evaluate_in_structure` against `tarski.satisfies` directly.
```

## Building a structure

A `FiniteStructure` is a domain plus extensions keyed by `(name, arity)`:

```python
from unicode_logic_kit import MSFLParser
from unicode_logic_kit.semantics import FiniteStructure, evaluate_in_structure

s = FiniteStructure(
    domain=("a1", "a2", "a3"),
    extensions={
        ("C", 1): frozenset([("a1",), ("a2",)]),
        ("O", 1): frozenset([("a3",)]),
        ("Bond", 2): frozenset([("a1", "a2"), ("a2", "a1"),
                                ("a2", "a3"), ("a3", "a2")]),
    },
)

p = MSFLParser()
print(evaluate_in_structure(p.parse("∃x (C(x) ∧ ∃y (O(y) ∧ Bond(x, y)))"), s))
# → True
print(evaluate_in_structure(p.parse("∀x (C(x) → ∃y (O(y) ∧ Bond(x, y)))"), s))
# → False
```

Note that `Bond` is listed in **both** directions. Extensions are exactly the
tuples you give: nothing is symmetrised, reflexive-closed or otherwise completed
behind your back.

`graph_to_structure` is the ergonomic constructor for the common case where the
data is a labelled graph — nodes carrying unary properties, edges carrying binary
relations:

```python
from unicode_logic_kit.semantics import graph_to_structure

s = graph_to_structure(
    nodes={"a1": ["C"], "a2": ["C"], "a3": ["O"]},
    edges={"Bond": [("a1", "a2"), ("a2", "a1"),
                    ("a2", "a3"), ("a3", "a2")]},
)
print(s.signature())              # → (('Bond', 2), ('C', 1), ('O', 1))
print(s.individuals_with("C"))    # → ('a1', 'a2')
print(s.neighbors("Bond", "a2"))  # → ('a1', 'a3')
```

`individuals_with` and `neighbors` are not conveniences — they are how the
evaluator avoids the whole domain. A quantifier whose variable is constrained by a
unary predicate draws its candidates from that predicate's extension, and one
constrained by a relation to an already-bound variable draws them from that
individual's neighbourhood. On a 40-atom molecule this is the difference between
scanning 40 candidates and scanning 3.

## An unknown symbol is an error, not `False`

```python
from unicode_logic_kit import MSFLParser
from unicode_logic_kit.semantics import graph_to_structure, evaluate_in_structure
from unicode_logic_kit.semantics import UninterpretedSymbol

s = graph_to_structure(nodes={"a1": ["C"]}, edges={})
try:
    evaluate_in_structure(MSFLParser().parse("∃x N(x)"), s)
except UninterpretedSymbol as exc:
    print(exc)
# → model_eval: predicate 'N'/1 is not interpreted by this structure
#   (known: ['C/1']).
```

This is deliberate. A structure is a *complete* description of its domain, so a
symbol it does not interpret is a bug in the query, not a fact about the world.
Reading it as `False` — the tempting default — turns a typo into a confident wrong
answer, and in a scoring run that wrong answer looks exactly like a correct
negative.

## Explanations, budgets and honest UNKNOWN

`evaluate_detailed` returns an `EvalResult` with the verdict plus what the
evaluator saw on the way:

```python
from unicode_logic_kit import MSFLParser
from unicode_logic_kit.semantics import graph_to_structure, evaluate_detailed

s = graph_to_structure(
    nodes={"a1": ["C"], "a2": ["C"], "a3": ["O"]},
    edges={"Bond": [("a1", "a2"), ("a2", "a1"),
                    ("a2", "a3"), ("a3", "a2")]},
)
p = MSFLParser()

good = evaluate_detailed(p.parse("∃x (C(x) ∧ ∃y (O(y) ∧ Bond(x, y)))"), s)
print(good.holds, good.witness)      # → True {'x': 'a2', 'y': 'a3'}

bad = evaluate_detailed(
    p.parse("∃x O(x) ∧ ∃x (O(x) ∧ ∃y (O(y) ∧ Bond(x, y)))"), s)
print(bad.holds)                              # → False
print(bad.failing_conjunct.to_unicode_str())  # → ∃x (O(x) ∧ ∃y (O(y) ∧ Bond(x, y)))
```

`witness` is only ever set when the answer is `True`, `failing_conjunct` only when
it is `False`; both are best-effort — a conjunction pins the conjunct that broke,
a bare universal can only point at itself.

A `budget` caps the number of evaluation steps. When it runs out the result is
`holds=None` with `exhausted=True` — UNKNOWN, never `False`:

```python
from unicode_logic_kit import MSFLParser
from unicode_logic_kit.semantics import graph_to_structure, evaluate_detailed

s = graph_to_structure(nodes={"a%d" % i: ["C"] for i in range(30)}, edges={})
r = evaluate_detailed(MSFLParser().parse("∀x ∀y (C(x) ∧ C(y))"), s, budget=20)
print(r.holds, r.exhausted)   # → None True
```

## Properties that are not first-order over the structure

Some properties are perfectly decidable **on** a finite structure yet not
definable in first-order logic over its relations — connectivity and ring
membership are the standard examples, both being transitive closures. A
*computed predicate* is a callable that decides such a symbol on demand. The
structure stays an ordinary finite structure; the callable is just a lazy
representation of an extension too large or too awkward to enumerate.

```python
from unicode_logic_kit import MSFLParser
from unicode_logic_kit.semantics import graph_to_structure, evaluate_in_structure

edges = [("a1", "a2"), ("a2", "a1"), ("a2", "a3"), ("a3", "a2")]
base = graph_to_structure(nodes={"a1": ["C"], "a2": ["C"], "a3": ["O"]},
                          edges={"Bond": edges})

def reaches(a, b):
    seen, todo = {a}, [a]
    while todo:
        cur = todo.pop()
        if cur == b:
            return True
        for nxt in base.neighbors("Bond", cur):
            if nxt not in seen:
                seen.add(nxt)
                todo.append(nxt)
    return False

s = graph_to_structure(nodes={"a1": ["C"], "a2": ["C"], "a3": ["O"]},
                       edges={"Bond": edges},
                       computed={("Reaches", 2): reaches})

print(s.signature())   # → (('Bond', 2), ('C', 1), ('O', 1), ('Reaches', 2))
print(evaluate_in_structure(MSFLParser().parse("∀x ∀y Reaches(x, y)"), s))
# → True
```

A symbol may be stored **or** computed, never both — the constructor rejects that
outright, because a structure that answers the same atom two ways is not a
structure. For the same reason `structure_from_dict` refuses to rebuild a
serialised structure unless you hand it back the callables: a `to_dict` round-trip
cannot carry code, and silently dropping the computed symbols would produce a
structure that answers a strictly smaller signature while looking complete.

## Molecules as structures

`unicode_logic_kit.chem` (install with the `[chem]` extra for RDKit) turns a SMILES
string into exactly such a structure: one individual per non-hydrogen atom,
element and charge and hydrogen count as unary predicates, bonds as binary
relations, plus ten computed predicates for the ring and connectivity properties.

```python
from unicode_logic_kit import chem
from unicode_logic_kit.semantics import evaluate_in_structure

ethanol = chem.mol_to_structure("CCO")
print(ethanol.domain)                  # → ('c1', 'c2', 'o1')
print(ethanol.individuals_with("c"))   # → ('c1', 'c2')

phi = chem.parse_chemlog_tptp("?[X,Y]: (c(X) & o(Y) & bond(X,Y))")
print(phi.to_unicode_str())            # → ∃x ∃y (c(x) ∧ o(y) ∧ bond(x, y))
print(evaluate_in_structure(phi, ethanol))   # → True
```

The individual names are *positional*, not chemical identities: `CCO` and `OCC`
describe the same molecule but hand `c1` to different atoms. Never carry a name
from one structure to another.

`parse_chemlog_tptp` does more than parse. TPTP inverts this kit's case
convention — `c(X)` there is predicate `c` applied to variable `X`, while the
kit's own unicode syntax wants `C(x)` — so an imported formula would arrive
speaking `C/1` while the structure speaks `c/1`, and every check would fail with
`UninterpretedSymbol`. The importer renames the chemical vocabulary back, and the
mapping's injectivity is checked when `chem.interop` is imported, since a
non-injective renaming would silently merge two predicates into one.

```python
from unicode_logic_kit import api, chem

phi = chem.parse_chemlog_tptp("?[X,Y]: (c(X) & o(Y) & bond(X,Y))")

# Rendered in ChemLog's own naming — which the kit's unicode dialect will NOT
# re-parse, because there a lowercase name cannot be a predicate:
print(api.parse_any(phi.to_unicode_str(), hint="fol").ok)          # → False

# to_kit_names moves it into the kit's convention, for display or re-parsing:
print(chem.to_kit_names(phi).to_unicode_str())
# → ∃x ∃y (C(x) ∧ O(y) ∧ Bond(x, y))
```

Keep the formula and the structure in the *same* naming. `to_kit_names` is for
rendering and for round-tripping through the unicode parser, not a step before
evaluation — `mol_to_structure` produces ChemLog (or paper) naming, and a
kit-named formula checked against it will correctly raise `UninterpretedSymbol`.

A worked check, on the ChemLog amide-bond pattern:

```python
from unicode_logic_kit import chem
from unicode_logic_kit.semantics import evaluate_in_structure

amide = chem.parse_chemlog_tptp(
    "?[C,O,N]: (c(C) & o(O) & n(N) & bDOUBLE(C,O) & bSINGLE(C,N))")

print(evaluate_in_structure(amide, chem.mol_to_structure("NCC(=O)NCC(=O)O")))
print(evaluate_in_structure(amide, chem.mol_to_structure("CCO")))
# → True
#   False
```

`chem.CHEMLOG_SIGNATURE` declares the same vocabulary as a
{class}`~unicode_logic_kit.fol.signature.Signature`, so `api.check` reports unknown
predicates and arity mistakes against it before anything is evaluated.

The element letters are `c`, `n`, `o`, `s`, `p`, `h` — ChemLog's own, its
published vocabulary being a peptide one — plus `f`, `cl`, `br`, `i`, `at`,
which the kit adds. An atom of any other element (a metal, say) is refused
with a `ValueError` naming it, rather than built without its type predicate.
The halogens are in the vocabulary because a ChEBI class such as
`organohalogenCompound` is *defined* by the halogen: without them
`mol_to_structure` rejects the molecule, and every such class is left
unanswerable rather than answered.

## Counting instead of enumerating

Machine-generated class definitions habitually express "at least six carbons" as
six existential quantifiers plus all fifteen pairwise inequalities. That formula
is correct and ruinously expensive. Two tools address it, and they take the
**original** formula — not each other's output.

`simplify_for_checking` drops inequalities that are redundant under the
`all_different` convention (separately introduced existential variables denote
distinct individuals), reporting each removal with its justification:

```python
from unicode_logic_kit import chem, simplify_for_checking

tptp = ("?[A,B,C,D,E,F]: (c(A) & c(B) & c(C) & c(D) & c(E) & c(F) & "
        "A!=B & A!=C & A!=D & A!=E & A!=F & B!=C & B!=D & B!=E & B!=F & "
        "C!=D & C!=E & C!=F & D!=E & D!=F & E!=F)")
phi = chem.parse_chemlog_tptp(tptp)

res = simplify_for_checking(phi, all_different=True)
print(res.changed, len(res.removed))          # → True 15
print(res.simplified.to_unicode_str())
# → ∃a ∃b ∃c ∃d ∃e ∃f (c(a) ∧ c(b) ∧ c(c) ∧ c(d) ∧ c(e) ∧ c(f))
```

`count_from_existential_chain` goes further where the formula is *exactly* the
count pattern — n existentials, one unary atom each with the same predicate, and
every pairwise inequality, nothing else — and rewrites it to the kit's counting
quantifier, whose bound stays symbolic:

```python
from unicode_logic_kit import chem, count_from_existential_chain

tptp = ("?[A,B,C,D,E,F]: (c(A) & c(B) & c(C) & c(D) & c(E) & c(F) & "
        "A!=B & A!=C & A!=D & A!=E & A!=F & B!=C & B!=D & B!=E & B!=F & "
        "C!=D & C!=E & C!=F & D!=E & D!=F & E!=F)")
counted = count_from_existential_chain(chem.parse_chemlog_tptp(tptp))
print(counted.to_unicode_str())   # → ∃≥6 a c(a)
```

Anything that is not exactly the pattern returns `None` rather than a guess — a
bond between two of the witnesses, a mismatched predicate, a missing pair.

What the two are worth, evaluated against hexane (`CCCCCC`), counting the steps
`evaluate_detailed` reports:

| formula | `all_different` | steps |
|---|---|---|
| as generated | `False` | 108979 |
| as generated | `True` | 139 |
| after `simplify_for_checking` | `True` | 49 |
| after `count_from_existential_chain` | — | 8 |

All four answer `True`. The counting quantifier does not need the convention at
all, because distinctness is part of what `∃≥6` *means*.

## Branching-time model checking: CTL over a `KripkeModel`

Everything above checks a formula against one *fixed* structure. A
`KripkeModel` (see {doc}`modal`) adds a *set of worlds* and a `"temporal"`
accessibility relation between them, so a formula can instead ask about the
system's possible **futures** — every run, or some run. `satisfies_modal`
already reads `Always`/`Eventually`/`Next`/`Until` off that relation, but each
of those has exactly one path reading baked into its own AST node (`Always`
universal-reachability, `Eventually` existential-reachability, and so on —
there is no A/E path-quantifier prefix anywhere in the grammar). CTL's other
four modalities — `ctl_ex`, `ctl_af`, `ctl_eg`, `ctl_au` — fill that in as
plain functions over `KripkeModel`, `Node` and `satisfies_modal`, not new
syntax:

```python
from unicode_logic_kit import KripkeModel, satisfies_modal, Atom, Not, And, Always
from unicode_logic_kit.semantics import ctl_ex, ctl_af, ctl_eg, ctl_au

crit1 = Atom("crit1", [])
crit2 = Atom("crit2", [])

# Worlds: 0 = idle, 1 = process 1's critical section, 2 = process 2's.
# Temporal edges: 0->1 (P1 may enter), 0->0 (idle may also stay idle forever),
# 1->2, 2->0 (round-robin back to idle). Every world has a successor.
mutex = KripkeModel(
    worlds={0, 1, 2},
    relations={"temporal": {(0, 1), (0, 0), (1, 2), (2, 0)}},
    valuation={1: {"crit1"}, 2: {"crit2"}},
)

print(satisfies_modal(Always(Not(And(crit1, crit2))), mutex, 0))  # → True
print(ctl_af(mutex, 0, crit1), ctl_af(mutex, 1, crit1), ctl_af(mutex, 2, crit1))
# → False True False
print(ctl_eg(mutex, 0, Not(crit1)), ctl_eg(mutex, 1, Not(crit1)))
# → True False
print(ctl_ex(mutex, 0, crit1), ctl_ex(mutex, 2, crit1))
# → True False
```

Mutual exclusion (`AG ¬(crit1 ∧ crit2)`, "never both critical at once") is
already expressible with the existing `Always` node, because AG *is* exactly
"true at every world reachable via the reflexive-transitive closure of
`\"temporal\"`" — no path enumeration needed, which is exactly what `Always`
already computes. `AF crit1` ("process 1 eventually enters, no matter what")
is different: it needs to hold on **every** infinite run, and the `0 → 0`
self-loop is an infinite run that never leaves `0` at all, so `AF crit1` is
false at world `0` and `2` (both can reach that stalling loop) and true only
at `1` (where `crit1` already holds). `EG ¬crit1` is the mirror question —
**some** run that never enters — and holds at `0` and `2` (the stall witnesses
it) but not at `1`, where `crit1` is already true right now. `EX crit1` only
looks one step ahead: `0`'s immediate successors are `{0, 1}` and `crit1`
holds at `1`, so it is true there and false at `1` and `2`, whose immediate
successors never have `crit1`.

`ctl_af`, `ctl_eg` and `ctl_au` quantify over *infinite* paths through
`"temporal"`, so they require the relation to be **total** on `model.worlds`
— every world needs at least one successor inside the world set, or there is
no infinite path through it to quantify over. A dead end raises `ValueError`
naming the offending world rather than silently making it vacuously true (the
same "refuse loudly instead of approximating" rule the kit applies
everywhere else):

```python
deadlock = KripkeModel(worlds={0, 1}, relations={"temporal": {(0, 1)}},
                       valuation={0: {"crit1"}})
ctl_af(deadlock, 0, crit1)
# raises ValueError: ctl_af/ctl_eg/ctl_au: the "temporal" relation is not total on
#   model.worlds — world 1 has no temporal successor inside model.worlds, ...
```

`ctl_ex` is the one exception: it is a plain one-step modality (the
existential dual of the kit's built-in, universally-read `Next`), so a
dead end simply makes it `False` there, exactly as a dead end already makes
`Next` vacuously `True` — no totality requirement, no error.

## Where to go next

- {doc}`batch-checking` — the same check over thousands of molecules, with a
  structure cache, a resumable JSONL log, and a failure that becomes a row
  instead of stopping the run.
- {doc}`verification` — checking the definitions themselves (satisfiable at all?
  circular? does the subclass entail the superclass?) rather than checking a
  structure against them.
- {doc}`classical-reasoning` — validity, entailment and model *finding*, when you
  do not have a structure in hand.
