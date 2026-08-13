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
| Self-correction | `diagnose`, `get_syntax_spec` |
| Introspection | `list_backends` |
| Chemistry | `check_molecule`, `check_molecules`, `molecule_to_structure`, `explain_molecule_failure`, `simplify_definition`, `chemical_signature` |

Every tool takes formulas as plain text with the dialect auto-detected, and
returns structured JSON.

```python
from unicode_fol_kit.mcp.server import prove

r = prove("Human(socrates) → Mortal(socrates)",
          ["∀x (Human(x) → Mortal(x))"])
print(r["status"], r["backend"], r["szs_status"])
# → proved z3 Theorem
```

(The tool functions are importable directly, which is what the examples on this
page do; under MCP the same functions are registered on the server.)

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
print(spec["ok"], len(spec["rules"]))       # → True 4
print(spec["rules"][0]["kind"], "—", spec["rules"][0]["shape"])
# → variable — one lowercase letter, optional digits
```

The eight topics are `overview`, `naming`, `dialects`, `operators`,
`quantifiers`, `counting`, `chemistry` and `errors`. Each carries prose rules
*and* worked examples, and the examples are not decorative: the test suite parses
every one of them with the dialect the spec claims and compares the rendering to
what the spec advertises. A rule the parser does not implement is a failing test
rather than a surprise for whoever trusted the spec at runtime.

The routing is deliberately conservative but not naive. Parse failures produce
one message per candidate dialect, and the dialects that give up earliest are
often the majority, so the topic is chosen by weighing how *far* each dialect
read against how *many* agree:

```python
from unicode_fol_kit.mcp.server import prove

print(prove("A ∧ B ∨ C")["spec_topic"])    # → operators
print(prove("∀ P(x)")["spec_topic"])       # → quantifiers
print(prove("P(1x)")["spec_topic"])        # → naming
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

The kit never rewrites the text itself. It diagnoses; the caller (typically the
model) proposes the next candidate and calls again. Silently repairing a formula
would hide from an evaluation exactly the errors the evaluation is measuring.

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

## Where to go next

- {doc}`syntax-reference` — the same grammar the spec tool serves, for human
  readers.
- {doc}`model-checking` — the chemistry tools' underlying layer.
- {doc}`probabilistic` — what `probability_bounds` and `probability_query` mean.
