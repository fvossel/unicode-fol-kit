# The kit as an MCP server

`unicode_fol_kit.mcp` exposes the toolkit over the Model Context Protocol, so a
language model can parse, check, prove, translate and score formulas by calling
tools instead of by being told the grammar in its prompt. Install the extra and
run it on stdio — the transport MCP clients spawn:

```bash
pip install "unicode-fol-kit[mcp]"
```

```bash
python -m unicode_fol_kit.mcp
```

The design goal is narrow and worth stating, because it shapes every tool's
result shape: **a rejection must be actionable**. A generator that gets back
"syntax error" has to guess; one that gets back the error *plus the name of the
rule it violated* can look the rule up and fix it. That is why every failure
carries a `spec_topic` and why the grammar itself is served as a tool.

## The tools

| Group | Tools |
|---|---|
| Parse & inspect | `parse_formula`, `check_formula`, `detect_dialect`, `get_signature`, `normalize`, `render`, `verbalize` |
| Reason | `prove`, `find_countermodel`, `check_consistency`, `check_equivalence`, `truth_table` |
| Compare & score | `compare_formulas`, `score_batch` |
| Translate | `translate`, `list_translations`, `drs_to_fol` |
| Probability | `probability_bounds`, `probability_query` |
| Self-correction | `diagnose`, `repair_formula`, `get_syntax_spec` |
| Introspection | `list_backends` |
| Chemistry | `check_molecule`, `check_molecules`, `molecule_to_structure`, `explain_molecule_failure`, `simplify_definition`, `chemical_signature` |
| Description logic | `dl_concept_satisfiable`, `dl_subsumes`, `dl_equivalent`, `dl_abox_consistent`, `dl_instance_check`, `dl_instance_retrieval`, `dl_classify`, `dl_parse_manchester` |

Every tool takes formulas as plain text with the dialect auto-detected, and
returns structured JSON.

`get_signature` answers `{"ok": True, "signature": {...}}`; `check_formula` and
`diagnose` take that whole result, or just its `signature` value, as their
`signature`, to hold further generations to the same vocabulary (the loose form
`{"predicates": {"Human": 1}, "constants": ["socrates"]}` is read too). The truth
constants `⊤` / `⊥` are never reported as predicates or as unknown symbols, and a
malformed `signature` comes back as `{"error": ...}`.

A formula nested a few hundred levels deep is processed on a worker thread with a
larger stack. An answer nested more deeply than the MCP transport can write as JSON
(about 100 levels, as `parse_formula` gives for 100 quantifiers) is refused as
`{"error": {"type": "ValueError", ...}}` that names the depth; ask `render` for the
text form instead. A direct Python call of a tool function is not held to that limit.

```python
from unicode_fol_kit.mcp.server import prove

r = prove("Human(socrates) → Mortal(socrates)",
          ["∀x (Human(x) → Mortal(x))"])
print(r["status"], r["backend"], r["szs_status"])
# → proved z3 Theorem
```

(The tool functions are importable directly, which is what the examples on this
page do; under MCP the same functions are registered on the server.)

### Stability

Within a minor release line (0.N.x) a registered tool is never renamed or
removed, and its input schema only ever gains new *optional* parameters — an
existing parameter's name, type and required/optional flag are stable (see
`unicode_fol_kit/mcp/server.py`'s module docstring for the exact wording, and
`tests/test_mcp_stability.py` for the pinned baseline that enforces it). A
Python caller of {doc}`../api` can pin `unicode-fol-kit>=0.N,<0.N+1` and be
done; an MCP client talking JSON-RPC over stdio has no equivalent of a `pip`
pin for the session it opens, so the 0.N line itself — checked once at
connect time, e.g. against `list_tools()` — *is* its integration contract.
The comorphism registry behind `translate`/`list_translations` carries the
same guarantee: within a line, no edge is removed, renamed, or has its
source/target/lossy changed, only added (`unicode_fol_kit/comorphism.py`'s
docstring).

## Rendering into another syntax

`render(text, to=..., dialect=None)` reparses `text` and re-emits it in
another concrete syntax: `unicode` / `tptp` / `prover9` / `latex` / `smtlib`
(a standalone SMT-LIB2 problem — one `(assert ...)`, no premises through this
tool; see {doc}`interoperability` for the premises-taking free function) /
`casl` / `json` (the one target whose `rendered` is a dict, not a string) /
`english`. A family without the requested rendering surfaces its OWN
refusal — for `smtlib` this is `to_z3`'s, naming the construct:

```python
from unicode_fol_kit.mcp.server import render

print(render("P(a)", to="smtlib")["rendered"])
# → (set-logic ALL)
# → ; benchmark generated from python API
# → (set-info :status unknown)
# → (declare-sort S 0)
# → (declare-fun P (S) Bool)
# → (declare-fun a () S)
# → (assert
# →  (P a))
# → (check-sat)

result = render("∃P P(a)", to="smtlib", dialect="second_order")
print(result["error"]["type"], "SMT-LIB2 export is first-order only" in
      result["error"]["message"])
# → NotImplementedError True
```

## The self-correction loop

A failure comes back in a uniform shape: `ok`, the `argument` that failed, the
parser `errors`, and `spec_topic` — the section of the served grammar that
explains this class of failure.

```python
from unicode_fol_kit.mcp.server import prove

bad = prove("c(A1) ∧ o(A2)")      # TPTP naming inside unicode syntax
print(bad["ok"], bad["spec_topic"])
# → False naming
```

`get_syntax_spec` then serves that section:

```python
from unicode_fol_kit.mcp.server import get_syntax_spec

spec = get_syntax_spec("naming")
print(spec["ok"], len(spec["rules"]))       # → True 5
print(spec["rules"][1]["kind"], "—", spec["rules"][1]["shape"])
# → variable — one term-valued letter (any script, cased or caseless), then optional trailing digits
```

The nine topics are `overview`, `naming`, `dialects`, `operators`,
`quantifiers`, `counting`, `chemistry`, `description-logic` and `errors`. Each
carries prose rules *and* worked examples, and the examples are not decorative:
the test suite parses every one of them with the dialect the spec claims and
compares the rendering to what the spec advertises. A rule the parser does not
implement is a failing test rather than a surprise for whoever trusted the spec
at runtime. `description-logic`'s own examples are parsed with `dl.parse_concept`/
`dl.parse_manchester` rather than the FOL-family `api.parse_any` every other
topic's examples go through — a different input language needs the matching
parser, not the wrong one reused (see the "Description logic tools" section
below).

The routing is deliberately conservative but not naive. Parse failures produce
one message per candidate dialect, and the dialects that give up earliest are
often the majority, so the topic is chosen by weighing how *far* each dialect
read against how *many* agree:

```python
from unicode_fol_kit.mcp.server import prove

print(prove("A ∧ B ∨ C")["spec_topic"])    # → operators
print(prove("∀ P(x)")["spec_topic"])       # → quantifiers
print(prove("P(1@)")["spec_topic"])        # → naming
```

`A ∧ B ∨ C` is the case worth understanding, because the kit's unicode grammar
puts ∧, ∨ and ⊕ on **one** level and refuses to guess between `(A ∧ B) ∨ C` and
`A ∧ (B ∨ C)`. The parser stops on the ∨ with the predicate `B` in hand, so the
message mentions a predicate — but the fix is brackets, and the topic must be
`operators`. Routed to `naming`, a generator would rename a perfectly good
predicate and fail in exactly the same place.

`diagnose` packages one round of the loop: diagnostics, a one-line suggestion,
the topic, and whether the text converged.

```python
from unicode_fol_kit.mcp.server import diagnose

step = diagnose("A ∧ B ∨ C")
print(step["ok"], step["spec_topic"])       # → False operators
print(step["suggestion"][:64])
# → Fix the syntax: SYNTAX_ERROR: Unexpected character '∨' at positi
```

```python
from unicode_fol_kit.mcp.server import diagnose

step = diagnose("∀x (P(x) → Q(x))")
print(step["ok"], step["converged"])        # → True True
```

`diagnose` never rewrites the text itself: it diagnoses, and the caller
(typically the model) proposes the next candidate and calls again. Silently
repairing a formula would hide from an evaluation exactly the errors the
evaluation is measuring.

## Mechanical repair, where the answer is unique

`repair_formula` is the deliberate exception, and the boundary is drawn where
there is exactly one right answer. Two shapes qualify — both of them cost a
generation attempt for nothing otherwise:

- **A name no symbol class accepts**: a chemical name carrying digits, commas
  or hyphens. The kit's unicode syntax has no quoting mechanism, so the name is
  renamed to a legal predicate — and the original stays in `names`, so nothing
  about it is lost; it lives beside the formula instead of inside it. Pass a
  shared `NameMapping` (via `fol.repair_formula`) to keep one class named the
  same way across a whole run.
- **A free variable**: always reported, and closed on request
  (`close_free_variables=True`) — by dropping the argument where the formula is
  a `P(x) ↔ …` definition whose `x` never recurs on the right, else by
  universal closure.

```python
from unicode_fol_kit.mcp.server import repair_formula

fixed = repair_formula("∀x (1,2-diacyl(x) → Lipid(x))")
print(fixed["repaired_text"])
# → ∀x (P12diacyl(x) → Lipid(x))
print(fixed["names"])
# → [{'original': '1,2-diacyl', 'legal': 'P12diacyl'}]
```

Mixed connectives are not among them, and that is the point: `A ∧ B ∨ C` has
two readings, so bracketing it would be a guess dressed as a repair.

```python
from unicode_fol_kit.mcp.server import repair_formula

refused = repair_formula("A(x) ∧ B(x) ∨ C(x)")
print(refused["ok"], refused["issues"][0]["kind"], refused["spec_topic"])
# → False mixed_connectives operators
```

(For formulas written in TPTP rather than the kit's own syntax, the sibling
`fol.repair_tptp_formula` covers the same three failure classes with TPTP's own
answers — single-quoting instead of renaming, and explicit bracketing for
parsers that demand it.)

## Scoring a batch

`score_batch` compares generated formulas against references with several
measures at once, which matters because they disagree in informative ways:

```python
from unicode_fol_kit.mcp.server import score_batch

r = score_batch(["∀x (P(x) → Q(x))", "P(a) ∧ Q(a)"],
                ["∀y (P(y) → Q(y))", "Q(a) ∧ P(a)"])
print(r["exact_match"], r["equivalence_accuracy"])   # → 0.0 1.0
print(r["parse_failure_rate"], r["solver_unknown_rate"], r["n"])
# → 0.0 0.0 2
```

Exact match is 0 — one prediction renames the bound variable, the other reorders
a conjunction — while logical equivalence is 1. Both formulas are right. Reporting
only the first number would understate the system by 100%, and reporting only the
second would hide the cases where the solver returned unknown rather than
equal — hence `solver_unknown_rate` alongside it.

## Declared converses (argument-permutation bridges)

`compare_formulas` and `score_batch` both take an OPTIONAL `converses`
argument that bridges a declared argument-permutation relationship — e.g.
`LovedBy(x, y) ↔ Loves(y, x)` — that no *automatic* alignment is allowed to
guess (guessing converses from lexical similarity alone would just as
happily "forgive" a genuine subject/object-swap translation error; see
{mod}`unicode_fol_kit.eval.converses`'s module docstring for the full
reasoning). Only the SOLVER level of `equivalence` ever honours it, and the
result is tagged with its own `method_used` value,
`"solver_modulo_converses"`, so it never gets silently merged into a plain
`"solver"` verdict. Each declaration is
`{"a": [name, arity], "b": [name, arity], "permutation": [...]}`:

```python
from unicode_fol_kit.mcp.server import compare_formulas

r = compare_formulas(
    "Loves(alice, bob)", "LovedBy(bob, alice)",
    converses=[{"a": ["LovedBy", 2], "b": ["Loves", 2], "permutation": [1, 0]}])
print(r["equivalence"]["equivalent"], r["equivalence"]["method_used"])
print(r["converse_axioms_applied"])
# → True solver_modulo_converses
# → ['∀v0 ∀v1 (LovedBy(v0, v1) ↔ Loves(v1, v0))']
```

`converse_axioms_applied` lists the axioms that were actually built
(unicode-rendered), or is `None` when no `converses` were given.
`score_batch(..., converses=...)` forwards the same declarations to every
pair and, when non-empty, adds a seventh metric key,
`converse_matched_rate` — the fraction of pairs the solver proved
equivalent USING the declared axioms, kept separately visible from (and
subtractable out of) `equivalence_accuracy`, matching how
`solver_unknown_rate` already sits alongside it rather than folding in
silently.

A malformed declaration (a dict missing `"a"`/`"b"`/`"permutation"`) comes
back as the tool's top-level `{"error": {...}}` shape; a well-shaped but
semantically invalid one (mismatched arity, a non-permutation, a predicate
declared its own converse, …) instead lands inside `equivalence["error"]`,
since it is only caught once `equivalent()` tries to build the axioms.
A modal pair with a non-empty `converses` lands in the same
`equivalence["error"]` place, since no modal bridging route exists:

```python
r = compare_formulas(
    "□P", "□Q",
    converses=[{"a": ["P", 0], "b": ["Q", 0], "permutation": []}])
print(r["ok"], r["equivalence"])
# → True {'error': 'equivalent: converses is not supported for modal
#   formulas -- declared converse bridging axioms are only honoured by the
#   classical/MSFOL Z3 route'}
```

`score_batch` reports the same case as its own top-level `{"error": {...}}`
shape (a batch has no per-pair error slot to isolate it in).

## Probabilistic entailment

`probability_bounds(conclusion, constraints, max_atoms=12, dialect=None,
strategy="direct", max_columns=500)` returns the tightest `[lower, upper]`
bounds the `constraints` Nilsson-entail for `conclusion` — see
{doc}`probabilistic` for the semantics. `strategy` picks the solving
ALGORITHM only, never the answer: `"direct"` (the default) enumerates every
world and is capped by `max_atoms`; `"column_generation"` never
materialises that many worlds, so it can go past `max_atoms` (its own brake
is `max_columns`). Both land on the identical exact bounds:

```python
from unicode_fol_kit.mcp.server import probability_bounds

constraints = [{"formula": "A", "probability": "7/10"},
               {"formula": "A → B", "probability": "4/5"}]
direct = probability_bounds("B", constraints)
colgen = probability_bounds("B", constraints, strategy="column_generation")
print(direct["lower"], direct["upper"], colgen["lower"], colgen["upper"])
# → 1/2 4/5 1/2 4/5
```

The truth constants are not atoms here: `⊤` has probability 1 and `⊥` probability 0 in
`probability_bounds` and `probability_query`, and neither counts toward `max_atoms`.

## Chemistry tools

The chemistry group evaluates a definition against a real molecule; see
{doc}`model-checking` for the layer underneath.

```python
from unicode_fol_kit.mcp.chem_tools import check_molecule

r = check_molecule("?[X,Y]: (c(X) & o(Y) & bond(X,Y))", "CCO")
print(r["ok"], r["holds"], r["steps"])   # → True True 23
print(r["witness"])                      # → {'y': 'o1', 'x': 'c2'}
```

`ok` and `holds` are separate on purpose: `ok=False` means the *query* was
broken (a parse failure, an unknown predicate), `holds=False` means the query
was fine and the answer is no. Collapsing them would score a malformed
definition as a correct negative.

Batch form, plus the failure explanation:

```python
from unicode_fol_kit.mcp.chem_tools import check_molecules

amide = "?[C,O,N]: (c(C) & o(O) & n(N) & bDOUBLE(C,O) & bSINGLE(C,N))"
r = check_molecules(amide, ["NCC(=O)NCC(=O)O", "CCO"])
print([(e["smiles"], e["holds"]) for e in r["results"]])
# → [('NCC(=O)NCC(=O)O', True), ('CCO', False)]
```

```python
from unicode_fol_kit.mcp.chem_tools import explain_molecule_failure

e = explain_molecule_failure("?[X]: (n(X))", "CCO")
print(e["domain"], e["atoms_by_type"]["n"])
# → ['c1', 'c2', 'o1'] []
```

The explanation hands back the structure as the checker sees it — the domain, the
atoms by element, their properties and bonds — so that "why did this not match"
is answered with the data rather than with a verdict.

`simplify_definition` is the anti-bloat pass over MCP:

```python
from unicode_fol_kit.mcp.chem_tools import simplify_definition

s = simplify_definition("?[A,B]: (c(A) & c(B) & A!=B)")
print(s["before_unicode"])   # → ∃a ∃b (c(a) ∧ c(b) ∧ a ≠ b)
print(s["after_unicode"])    # → ∃a ∃b (c(a) ∧ c(b))
print(s["removed_count"])    # → 1
```

## Description logic tools

The `dl_*` group wires up `unicode_fol_kit.dl`'s ALCHQ tableau (concept
satisfiability, subsumption, ABox consistency, instance/realization queries,
TBox classification) — no new reasoning, purely MCP plumbing over what
{doc}`description-logic` already implements. Every tool takes concept TEXT,
not a full FOL formula: the ALC glyph syntax (`syntax="alc"`, the default —
`⊤ ⊥ ¬ ⊓ ⊔ ∃ ∀ ≥ ≤`) or the W3C OWL 2 Manchester Syntax (`syntax="manchester"`
— `and`/`or`/`not`/`some`/`only`/`min`/`max`/`exactly`). A TBox is passed as a
list of JSON rows — `{"sub": ..., "sup": ...}` (a GCI), `{"equiv": [...]}`, or
the RBox's `{"subrole": ..., "suprole": ...}` / `{"transitive": ...}` — never a
Python `TBox` object; an ABox is `concepts` (`[individual, concept_text]`
pairs), `roles` (`[a, b, role]` triples) and `distinct` (`[a, b]` pairs, for
`ABox.assert_distinct`).

```python
from unicode_fol_kit.mcp.server import dl_subsumes, dl_classify

tbox = [
    {"equiv": ["Parent", "Person ⊓ ∃hasChild.Person"]},
    {"equiv": ["Mother", "Parent ⊓ Female"]},
    {"equiv": ["Father", "Parent ⊓ Male"]},
    {"sub": "Male", "sup": "¬Female"},
]
print(dl_subsumes("Mother", "Parent", tbox=tbox)["subsumes"])   # → True

cl = dl_classify(tbox)
print(sorted(cl["children"]["Parent"]))                          # → ['Father', 'Mother']
```

`dl_parse_manchester(text, kind="concept"|"axiom"|"role_axiom")` reads OWL
tooling's own notation and reports the kit's unicode rendering alongside a
`to_manchester` round-trip:

```python
from unicode_fol_kit.mcp.server import dl_parse_manchester

r = dl_parse_manchester("hasChild some (Doctor and not Rich)")
print(r["concept_unicode"])
# → ∃hasChild.(Doctor ⊓ ¬Rich)
```

Errors follow the same two-shape convention as every other tool: a malformed
concept/Manchester TEXT (`ConceptSyntaxError`/`ManchesterSyntaxError` —
including a real Manchester construct outside ALCHQ, like `Self`/`inverse`/a
nominal, rejected by name) is the uniform `ok=False`/`argument`/`errors`/
`spec_topic="description-logic"` shape; a REASONING-level refusal —
a qualified number restriction on a non-simple (transitive, or
transitively-subsumed) role — is `NonSimpleRoleError`, a structured
`{"error": {...}}`, since the concept text itself parsed fine:

```python
from unicode_fol_kit.mcp.server import dl_concept_satisfiable

r = dl_concept_satisfiable("≥2 hasChild.Person", tbox=[{"transitive": "hasChild"}])
print(r["error"]["type"])
# → NonSimpleRoleError
```

A value restriction is a reasoning-level refusal too: `r value a` (Manchester) is read as
`∃r.{a}`, and every `dl_*` tool that reasons about it answers
`{"error": {"type": "UnsupportedConceptError", ...}}`, since the in-house tableau has no
rule for it.

The refusal of a printer or writer has the same shape, and is never an exception. The
tools that report a concept's text (`dl_concept_satisfiable`, `dl_subsumes`,
`dl_equivalent`, `dl_instance_check`, `dl_instance_retrieval`, `dl_parse_manchester`)
answer a concept whose glyph text would read back as another concept, such as a class
named `<A⊓B>`, with `{"error": {"type", "message"}}` before they reason:

```python
r = dl_concept_satisfiable("<A⊓B>", syntax="manchester")
print(list(r), r["error"]["type"], "reads back as" in r["error"]["message"])
# → ['error'] ValueError True
```

`get_syntax_spec("description-logic")` serves the concept-constructor table
(glyph and Manchester keyword side by side), the RBox/GCI axiom shapes, and
the exact TBox/ABox JSON row shapes above.

## Where to go next

- {doc}`syntax-reference` — the same grammar the spec tool serves, for human
  readers.
- {doc}`model-checking` — the chemistry tools' underlying layer.
- {doc}`probabilistic` — what `probability_bounds` and `probability_query` mean.
- {doc}`description-logic` — the `dl_*` tools' underlying ALCHQ tableau, in
  full: general TBoxes, role hierarchies and transitive roles, qualified
  number restrictions, instance/realization queries, and classification.
