# Finite-domain backends: deciding by counterexample

Every prover backend the kit shipped before this page worked by **exporting**:
translate the formula into Z3, Prover9, TPTP, SMT-LIB, and let an external
tool decide it there. That works for classical FOL, but two questions have no
export at all:

- **Counting.** `Count` (`∃≥n`/`∃≤n`/`∃=n`) and `Cardinality` (`|{v : φ}|` as a
  term) are genuinely second-order for a first-order *export* — `to_z3`,
  `to_prover9` and `to_tptp` all refuse a `Cardinality` comparison outright.
- **Minimal models.** `minimal_models` finds them by brute-force enumeration;
  `circumscription_entails_so` builds a second-order formula and hands it to
  a finite-model search. Neither uses the fact that enumerating-and-filtering
  minimal models is exactly what answer-set programming is *for*.

`ClingoBackend` and `MinizincBackend` close the first gap by grounding into a
real finite-domain solver instead of exporting; `semantics.asp_models`
closes the second by letting `clingo` enumerate natively. All three are new
in this release, and all three share one contract worth reading before
anything else on this page.

```{warning}
**These backends never prove anything. They only refute.** `decide(φ,
premises)` searches for a finite model of `premises ∧ ¬φ` at sizes `1 …
max_size`. Finding one *proves* `φ` invalid — `REFUTED` carries a genuine,
independently re-verified countermodel. **Finding none proves nothing**:
first-order logic has no finite model property, so "no countermodel up to
size `n`" is `UNKNOWN`/`"bound_hit"`, not evidence of validity. Neither
backend's `decide()` even imports `PROVED` from `atp.protocol` — a backend
that cannot name the symbol cannot accidentally return it. This is the same
discipline `ModelFinderBackend` and `KripkeEnumBackend` already follow; see
{doc}`classical-reasoning` for what search-to-a-bound backends can and
cannot tell you in general.
```

Four verdicts follow from that contract, and every example below is one of
them: `REFUTED` (a verified countermodel), `UNKNOWN`/`"bound_hit"` (no
countermodel up to `max_size`), `UNKNOWN`/`"unsupported"` (the formula is
outside the encodable fragment), `ERROR`/`"infra"` (grounding failed, or —
the one that matters most for correctness — a candidate countermodel could
not be independently confirmed).

## Why counting had no solver, concretely

`Cardinality` is genuinely second-order the moment you ask for a first-order
*export*:

```python
from unicode_fol_kit import MSFLParser

p = MSFLParser()
more_than_one = p.parse("|{v : Voted(candidate, v)}| > 1")
try:
    more_than_one.to_z3()
except NotImplementedError as exc:
    print(str(exc)[:70])
# → Cardinality terms (|{v : φ}|) denote set cardinality, a second-order n
```

`to_prover9` and `to_tptp` refuse it for the identical reason. But over a
*finite, already-fixed-size* structure, cardinality is just counting — the
`#count` aggregate ASP solvers ship with natively. `fragment_check`, the gate
both new backends share, draws that line explicitly:

```python
from unicode_fol_kit.atp import fragment_check
from unicode_fol_kit.fol.nodes import Atom, Constant, Box

print(fragment_check((more_than_one,)))    # → None: encodable here
modal = Box(Atom("P", [Constant("alice")]))
print(fragment_check((modal,)))
# → Box is not encodable: modal/temporal/epistemic/hybrid operators quantify over POSSIBLE WORLDS, not domain individuals — no finite-domain reading here; the modal family already has its own finite-model backend (kripke-enum)
```

`fragment_check` accepts unsorted classical FOL plus `Count`/`Cardinality`
and refuses everything else **by name** — modal operators (their own
`kripke-enum` backend already exists for exactly this), second-order
quantification, the sorted family, substructural connectives, and so on.
Refusing by name, not by silent mis-encoding, is what makes
`UNKNOWN`/`"unsupported"` mean something specific instead of "something went
wrong somewhere."

## The shared problem layer

Both backends encode the *same* `FiniteDomainProblem` — sentences to satisfy
together, a domain size, and a signature inferred (unless you supply one)
via `Signature.from_formulas`:

```python
from unicode_fol_kit.atp import FiniteDomainProblem
from unicode_fol_kit.fol.nodes import Atom, Variable

x = Variable("x")
problem = FiniteDomainProblem((Atom("Bird", [x]),), size=2)
print(sorted(problem.signature.predicates))   # → ['Bird']
print(problem.size, problem.all_different)    # → 2 False
```

This module never grounds anything itself — clingo and MiniZinc both ground
better than a hand-rolled loop would — so its job stops at three things: the
`fragment_check` gate above, `structure_from_solution` (turning a solver's
true atoms back into a `FiniteStructure`), and `verify_model`, the safety net
described next.

### The countermodel is checked before you ever see it

Every candidate countermodel is re-run through the kit's own
`evaluate_in_structure` against the refutation goal *before* a backend is
allowed to call it `REFUTED`. A model finder that hands back a structure
that does not actually satisfy the goal is worse than one that finds
nothing — this is what closes that possibility, structurally, not by
discipline alone. It also fixes a real, pre-existing weakness:
`ModelFinderBackend` reports `{"kind": "finite_structure", "repr":
repr(structure)}` — a Python repr no downstream consumer can parse. Both new
backends report `{"kind": "finite_structure", "data": structure.to_dict()}`
instead, round-trippable through `structure_from_dict` (see below).

The counting fragment sits fully inside that net now, not just the
classical-FOL fragment: `evaluate_in_structure` gained a reading for
`Cardinality` comparisons this release, so a `REFUTED` involving `|{v : φ}|`
is independently checked exactly like every other sentence on this page —
see "`Cardinality` comparisons: decided, and now independently checked"
below for the one caveat that remains.

## `ClingoBackend`

Dependency: `pip install unicode-fol-kit[asp]` (`clingo`, MIT-licensed, ships
its solver in the wheel — nothing external to find). `available()` is a pure
`importlib` check, so probing it never pays the load cost of actually
importing `clingo`.

```python
from unicode_fol_kit import ClingoBackend
from unicode_fol_kit.atp import clingo_available

print(clingo_available())
backend = ClingoBackend()
print(backend.name, sorted(backend.logics), backend.external, backend.available())
# → True
#   clingo ['fol'] False True
```

### A refuted entailment, with a countermodel you can round-trip

"Tweety is a bird" does not, by itself, entail "Tweety can fly" — the
smallest countermodel is the one-element domain where Tweety is a bird and
nothing can fly:

```python
bird = p.parse("Bird(tweety)")
canfly = p.parse("CanFly(tweety)")

v = backend.decide(canfly, [bird], max_size=3)
print(v.status, v.reason)          # → refuted None
print(v.countermodel)
# → {'kind': 'finite_structure', 'data': {'domain': ['0'], 'extensions': {'Bird/1': [['0']], 'CanFly/1': []}, 'computed': [], 'constants': {'tweety': '0'}}}
```

```python
from unicode_fol_kit.semantics import structure_from_dict

s = structure_from_dict(v.countermodel["data"])
print(s.domain, sorted(s.extensions[("Bird", 1)]), sorted(s.extensions[("CanFly", 1)]))
# → ('0',) [('0',)] []
```

### The one rule, in practice

A textbook-valid instance of modus ponens has no countermodel *at any size*
— so the honest answer is "none found up to the bound," never "proved":

```python
premise = p.parse("∀x (P(x) → Q(x))")
palice, qalice = p.parse("P(alice)"), p.parse("Q(alice)")

v2 = backend.decide(qalice, [premise, palice], max_size=4)
print(v2.status, v2.reason, bool(v2))
# → unknown bound_hit False
```

`bool(Verdict)` is `status == "proved"` — `False` here is the whole point:
a valid formula and an UNKNOWN-because-we-stopped-searching formula produce
the identical, honest verdict from a refutation-only search.

### The counting quantifier, closed: `Count`

"At least 2 individuals satisfy `P`" does not entail "at least 3" — obviously,
but now the kit can *decide* that instead of refusing to export it. `Count`
is fully supported by the independent checker, so this is REFUTED end to
end, no caveats:

```python
at_least_2, at_least_3 = p.parse("∃≥2 x P(x)"), p.parse("∃≥3 x P(x)")

v3 = backend.decide(at_least_3, [at_least_2], max_size=3)
print(v3.status, v3.reason, v3.detail)   # → refuted None None

s3 = structure_from_dict(v3.countermodel["data"])
print(s3.domain, sorted(s3.extensions[("P", 1)]))
# → ('0', '1') [('0',), ('1',)]
```

Both individuals satisfy `P`: exactly two, which is `≥ 2` (the premise) and
not `≥ 3` (the negated conclusion) — and a one-element domain cannot even
satisfy the premise, so this is the smallest countermodel there is.

### `Cardinality` comparisons: decided, and now independently checked

Until this release `Cardinality` sat in an odd spot: `fragment_check` already
admitted it into the encodable fragment (grounding and solving it was never
the problem — clingo's `#count` aggregate handles it natively, see
"Rendering the ASP program directly" below), but the independent checker
this module is *required* to call before it may say `REFUTED` —
`evaluate_in_structure` — had no reading for a `Cardinality` term at all. A
genuinely correct countermodel therefore came back "could not verify," and a
correct `REFUTED` was downgraded to `ERROR`/`"infra"`.

`semantics.model_eval` closes that gap directly: a comparison with at least
one numeric operand (`Cardinality` or `Number`) is now read arithmetically —
`|{v : φ}|` is *counted* over the domain, one budget tick per individual,
exactly the "counting is decidable on a finite structure" principle that
already made `Count` native above. Individual-denoting terms are untouched
by this — the two notions of "term value" (an individual, a count) are kept
apart and meet only in that one comparison branch. The practical
consequence: the same query that used to report the gap now reports the real
answer, verified, with no caveat attached:

```python
more_than_one_p = p.parse("|{v : P(v)}| > 1")

v4 = backend.decide(more_than_one_p, max_size=3)
print(v4.status, v4.reason, v4.detail)   # → refuted None None
print(v4.countermodel)
# → {'kind': 'finite_structure', 'data': {'domain': ['0'], 'extensions': {'P/1': []}, 'computed': [], 'constants': {}}}
```

`v4.detail` is `None` — no caveat; this `REFUTED` is exactly as trustworthy as
any other verdict on this page. (The witness itself is unexciting — nothing
forces `P` to hold anywhere, so the smallest countermodel is the empty
extension — the point is that verification now succeeds at all, not that the
witness is surprising.)

Comparing two *different* cardinalities — the shape of query this whole
design exists for — verifies exactly the same way, at `max_size=4`:

```python
two_counts = p.parse("|{x : P(x)}| > |{y : Q(y)}|")

v4b = backend.decide(two_counts, max_size=4)
print(v4b.status, v4b.reason, v4b.detail)   # → refuted None None
```

And the parity with `Count` above is not just thematic. Writing the identical
"at least 2 does not entail at least 3" claim through `Cardinality` syntax
instead of `Count` syntax reaches the identical two-element countermodel:

```python
at_least_2_card = p.parse("|{x : P(x)}| ≥ 2")
at_least_3_card = p.parse("|{x : P(x)}| ≥ 3")

v4c = backend.decide(at_least_3_card, [at_least_2_card], max_size=3)
print(v4c.status, v4c.reason, v4c.detail)   # → refuted None None

s4c = structure_from_dict(v4c.countermodel["data"])
print(s4c.domain, sorted(s4c.extensions[("P", 1)]))
# → ('0', '1') [('0',), ('1',)]
```

`Count` and `Cardinality` are two syntaxes for the same underlying notion — a
quantifier form and a term form — and now decide *and verify* identically, as
they should: the counting fragment this whole design exists to close is
closed end to end, not merely groundable.

### The one that remains: `Function`, refused up front

One node type still cannot come back `REFUTED` from either backend, and it is
refused at the gate rather than discovered later.

**`Function`** never reaches the checker. `fragment_check` refuses it BY NAME:
`FiniteStructure` has fields for a domain, predicate extensions, computed
relations and constants — no slot for a function interpretation — so a model
containing one could never be reconstructed and checked back, and this layer
does not hand out countermodels it cannot verify:

```python
has_function = p.parse("P(f(x))")

print(fragment_check((has_function,))[:95])
# → Function is not encodable: function symbols: a solver can find a model c

v7 = backend.decide(has_function, max_size=2)
print(v7.status, v7.reason)   # → unknown unsupported
```

The refusal fires straight from the fragment gate, before grounding, solving
or reconstruction is attempted — so there is no correct-but-unconfirmed
countermodel sitting around to apologise for. It is also a *stable* answer: an
`UNKNOWN`/`"unsupported"` will read the same on every machine and every run,
where an `ERROR`/`"infra"` reads like a transient fault and invites a retry
that can never succeed. Adding a function-interpretation slot to
`FiniteStructure` — so such a countermodel *could* be reconstructed and
verified — touches serialisation, the evaluator and every consumer of a
structure; separate, larger work, not attempted here.

**`Contrast` used to be listed here** as a second case: `fragment_check`
admitted it (truth-functionally `And`, so the encoders always handled it) while
`evaluate_in_structure` had no case for it, so a correct countermodel was
downgraded to `ERROR`/`"infra"`. That was an omission in the evaluator rather
than a boundary of this design — the node's own docstring says concession is a
discourse relation and every export treats it as `∧` — so the evaluator now
reads it that way and the case is closed:

```python
from unicode_fol_kit.fol.nodes import Contrast

contrast_ex = Contrast(palice, qalice)
print(fragment_check((contrast_ex,)))    # → None: encodable here

v8 = backend.decide(contrast_ex, max_size=2)
print(v8.status, v8.countermodel["kind"])   # → refuted finite_structure
```

The general lesson is worth stating, because it is the one this design got
wrong first: **the gate and the checker must admit the same fragment.** A
solver that decides something the kit cannot verify produces a feature that is
sound and useless — every answer correct, every answer discarded.

### Rendering the ASP program directly

`to_asp` is the pure-text half of this backend — no solver required, and
useful for reading exactly what gets grounded:

```python
from unicode_fol_kit.atp import to_asp

x = Variable("x")
print(to_asp(FiniteDomainProblem((Atom("Bird", [x]),), size=2)))
```

```text
% finite-domain refutation search: |D| = 2, 1 sentence(s)
dom(0..1).

{ pred0(X0) : dom(X0) }.

sat1(Vx) :- dom(Vx), pred0(Vx).
:- dom(Vx), not sat1(Vx).

#show.
#show pred0/1.
```

The free choice (`{ pred0(X0) : dom(X0) }`) is the countermodel search space
— any subset of the domain `Bird` could hold on; the trailing bare `#show.`
suppresses clingo's own "no `#show` present → show everything" default, so
internal `sat`/`dom` bookkeeping atoms never leak into a decoded model.

### Options

`decide(formula, premises=(), timeout=10000, **options)` — `timeout` is
milliseconds across the *whole* search, not per size. Backend-specific
options: `max_size` (default `6`) — the largest domain size tried;
`all_different` (default `False`) — every declared constant must denote a
distinct individual; `verify` (default `True`) — set `False` only to measure
verification overhead, never to silence a genuine mismatch (an unverified
countermodel is still marked as such in `Verdict.detail`, never silently).

## `MinizincBackend`

Same contract, same shared `atp.finite_domain` layer, a CP solver instead of
ASP. Dependency: a separate **MiniZinc ≥ 2.6 installation**, discovered via
`$UFK_MINIZINC` then `PATH` — the same convention `Prover9Backend` and
`VampireBackend` already use for their own external binaries. `pip install
unicode-fol-kit[cp]` installs the *Python* `minizinc` package, which this
backend does not use at all; it shells out to the `minizinc` CLI directly,
one fewer translation layer between what this module encodes and what
actually gets solved.

MiniZinc is not installed in this environment, so `available()` is honestly
`False` here — the same absent-tool handling `EProverBackend` and
`TweeBackend` already use elsewhere in the kit:

```python
from unicode_fol_kit import MinizincBackend
from unicode_fol_kit.atp import minizinc_available
from unicode_fol_kit.atp.protocol import BackendUnavailable

print(minizinc_available())
mb = MinizincBackend()
print(mb.name, sorted(mb.logics), mb.external, mb.available())
# → False
#   minizinc ['fol'] True False

try:
    mb.decide(canfly, [bird], max_size=2)
except BackendUnavailable as exc:
    print(str(exc)[:60])
# → minizinc: no binary found (set $UFK_MINIZINC or put 'minizin
```

`to_minizinc` (the renderer) needs no binary at all, so it runs for real even
here — the same `Bird`/`CanFly` problem as an `.mzn` file:

```python
from unicode_fol_kit.atp import to_minizinc

problem2 = FiniteDomainProblem((bird, canfly), size=2)
print(to_minizinc(problem2))
```

```text
% Generated by unicode_fol_kit.atp.minizinc_backend.to_minizinc --
% bounded refutation search, |D| = 2, 2 sentence(s) to satisfy simultaneously.
% REFUTATION-ONLY: SATISFIABLE here witnesses a finite countermodel;
% UNSATISFIABLE proves nothing about validity at a larger domain size.

int: n = 2;
set of int: DOM = 0..n-1;

array[DOM] of var bool: p_Bird;
array[DOM] of var bool: p_CanFly;

var DOM: k_tweety;

constraint p_Bird[k_tweety]; % sentence 1
constraint p_CanFly[k_tweety]; % sentence 2

solve satisfy;

output [
  "UFK-SOLUTION-BEGIN\n",
  "UFK p_Bird 1 " ++ show([p_Bird[i0] | i0 in DOM]) ++ "\n",
  "UFK p_CanFly 1 " ++ show([p_CanFly[i0] | i0 in DOM]) ++ "\n",
  "UFK k_tweety 0 " ++ show(k_tweety) ++ "\n",
  "UFK-SOLUTION-END\n"
];
```

A predicate becomes a boolean array; where the counting fragment earns CP
its place in this design is `Count`/`Cardinality`, rendered as
`sum(v in DOM)(bool2int(...))` rather than ASP's `#count`, and the
`all_different` convention becomes MiniZinc's own `alldifferent` global
constraint instead of the pairwise-`≠` expansion `simplify_for_checking`
would otherwise need (see {doc}`model-checking`'s counting section for how
expensive that expansion gets on real molecules).

With MiniZinc installed, everything else follows the same shape as
`ClingoBackend` — same `Verdict`, same countermodel format, same never-PROVED
contract:

```python
# doctest: +SKIP — needs a MiniZinc >= 2.6 installation on PATH
v = mb.decide(canfly, [bird], max_size=3, solver="gecode")
print(v.status, v.countermodel)
```

## Minimal models via ASP

`semantics.asp_models` is reached only by its own path — it is not
re-exported anywhere else, so `from unicode_fol_kit.semantics.asp_models
import asp_minimal_models, asp_find_model` is the way in. It answers the
same question `semantics.nonmonotonic.minimal_models` does
(see {doc}`nonclassical`'s circumscription section), by a different route:
instead of enumerating every interpretation in Python and filtering, it lets
`clingo` enumerate — ASP's native search — and hands the result to
`nonmonotonic`'s own, *unmodified* `_circ_profile`/`_strictly_below`
minimality predicate. The two routes can only ever disagree about which
models were *found* (an enumeration bug), never about which of them count
as *minimal* (a comparison bug), because they share that second half of the
code.

Reusing `nonclassical`'s own worked example — `P(a) → Q(a)`, circumscribing
both `P` and `Q`, has a unique minimal model where both predicates are
empty:

```python
from unicode_fol_kit.semantics.asp_models import asp_minimal_models
from unicode_fol_kit.semantics.nonmonotonic import minimal_models
from unicode_fol_kit.fol.nodes import Atom, Constant, Implies

a = Constant("a")
Pa, Qa = Atom("P", [a]), Atom("Q", [a])

models = asp_minimal_models([Implies(Pa, Qa)], circumscribed={"P", "Q"}, size=1)
for m in models:
    print(m.domain, dict(m.constants), {k: sorted(v) for k, v in m.predicates.items()})
# → (0,) {'a': 0} {('P', 1): [], ('Q', 1): []}
```

Same answer `minimal_models([Implies(Pa, Qa)], circumscribed={"P","Q"},
max_size=1)` finds — checked directly, not assumed:

```python
reference = [s for s in minimal_models([Implies(Pa, Qa)], circumscribed={"P", "Q"}, max_size=1)
            if len(s.domain) == 1]
print(len(reference) == len(models))    # → True
```

(Filtering the `minimal_models` result to `len(s.domain) == 1` is valid
because that function never compares models across different domain sizes —
see its own docstring — so this filtered set is provably what a
single-size search would have returned on its own.)

`asp_find_model` is the single-shot analogue, one model or `None`:

```python
from unicode_fol_kit.semantics.asp_models import asp_find_model

m1 = asp_find_model([p.parse("∃x P(x)")], size=2)
print(m1.domain, {k: sorted(v) for k, v in m1.predicates.items()})
# → (0, 1) {('P', 1): [(1,)]}

print(asp_find_model([p.parse("∀x P(x)"), p.parse("∀x ¬P(x)")], size=1))
# → None
```

```{note}
`size` here is a single, exact domain size — clingo grounds once, at that
size — **not** `minimal_models`'s `max_size`, which unions results across
every size from 1 up to the bound. A caller wanting that union behaviour
loops over sizes and concatenates; folding the loop into this function would
hide clingo's per-call grounding cost from the caller instead of making it
visible at the point where it is paid.
```

`asp_models` returns plain `tarski.Structure` objects (domain
`tuple(range(size))`, integer individuals) — the *same* type `minimal_models`
and `modelfinder.find_model` already return, not the string-domain
`FiniteStructure` `ClingoBackend`/`MinizincBackend` use above. Its fragment
is narrower than `fragment_check`'s, too, and for two different reasons.
`Contrast` is out because `tarski.satisfies` — this module's own verification
oracle — has no case for it at all, so there would be nothing to check the
encoding against. `Cardinality` is out despite the oracle handling it: routing
an arithmetic term value through an encoding that only ever produces
domain-individual variables is its own unit of work with its own risk of a
subtly wrong aggregate, and circumscription premises reason about predicate
extensions rather than counts, so it buys nothing here. Shipping an
un-cross-checked encoding path is exactly what this design avoids.

## Registered, but not in the default chain

Both backends register under `atp.protocol`'s registry (`"clingo"`,
`"minizinc"`), reachable by name through `get_backend`, `run_backend`, or
`portfolio_prove` — but neither joins `default_chain("fol")`:

```python
from unicode_fol_kit.atp import default_chain, available_backends

print(default_chain("fol"))
# → ('z3', 'cvc5', 'tableau', 'resolution', 'modelfinder')
print("clingo" in default_chain("fol"), "minizinc" in default_chain("fol"))
# → False False
print(available_backends("fol"))
# → ('clingo', 'cvc5', 'eprover', 'isabelle', 'modelfinder', 'resolution', 'tableau', 'twee', 'z3')
```

They fill the same role `modelfinder` already fills in that chain — bounded
finite-model search — and promoting a stronger implementation into the
default path is its own measured decision (the `cvc5` precedent: it only
joins the chain when installed), not a side effect of adding a backend. Until
that measurement happens, reach either backend by name: `ClingoBackend().decide(...)`
directly, `run_backend("clingo", formula, premises)`, or
`portfolio_prove(formula, premises, backends=["clingo"])` to race it against
others:

```python
from unicode_fol_kit import run_backend, portfolio_prove

v5 = run_backend("clingo", canfly, [bird], max_size=3)
print(v5.status, v5.backend)              # → refuted clingo
v6 = portfolio_prove(canfly, [bird], backends=["clingo"], max_size=3)
print(v6.status, v6.backend)              # → refuted clingo
```

## Where to go next

- {doc}`classical-reasoning` — the other bounded-search backend,
  `find_countermodel`/`ModelFinderBackend`, and what a search-to-a-bound
  verdict can and cannot tell you in general.
- {doc}`nonclassical` — `minimal_models`, `minimal_entails` and
  circumscription in full, including the closed-world and unique-names
  caveats `asp_minimal_models` inherits by sharing its filter.
- {doc}`model-checking` — why `Count` exists in the first place: counting
  quantifiers keep a bound *symbolic* instead of expanding into `n`
  existentials and `n(n-1)/2` inequalities.
