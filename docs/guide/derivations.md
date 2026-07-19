# CCG derivation trees

`CCGDerivation` builds and renders **combinatory categorial grammar derivations** in
the spirit of ccg2lambda / depccg: a bottom-up composition tree whose nodes carry a
surface word, a CCG category, a combinator rule (`fa`, `ba`, `bx`, `conj`, `lex`,
`rp`, …), and the **lambda-term semantics** at that node. The semantics is genuinely
*composed*, not written by hand — `forward` and `backward` apply one child's term to
the other and reduce it with the toolkit's own [`beta_reduce`](parsing.md), so the
term at every node is the real beta-normal form.

## Building a derivation

Leaves carry a real toolkit lambda-term; the composing builders reduce the applied
term automatically:

```python
from unicode_fol_kit import CCGDerivation as D, MSFLParser, Constant

p = MSFLParser()

some    = D.leaf("Some", "NP/N", p.parse("(λG. λF. ∃x (G(x) ∧ F(x)))"))
woman   = D.leaf("woman", "N", p.parse("(λx. Woman(x))"))
subject = D.forward("NP", some, woman)          # fa: applies Some's term to woman's

ordered = D.leaf("ordered", r"(S\NP)/NP", p.parse("(λo. λx. Order(x, o))"))
tea     = D.leaf("tea", "N", Constant("tea"))
vp      = D.forward(r"S\NP", ordered, tea)      # fa

sentence = D.forward("S", subject, vp)          # the subject GQ applies to the VP
print(sentence.term.to_unicode_str())           # → ∃x (Woman(x) ∧ Order(x, tea))
```

The composed `sentence.term` is a normal toolkit `Node` — it round-trips, verbalizes
(`to_english`), and (once fully saturated, via `eliminate_lambdas`) exports to
Z3 / TPTP / Prover9 like any other formula.

The builders:

| Builder | Combinator | Semantics |
|---|---|---|
| `D.leaf(word, category, term)` | — | a lexical leaf |
| `D.forward(cat, functor, argument)` | `fa` (`X/Y  Y → X`) | `beta_reduce(functor argument)` |
| `D.backward(cat, argument, functor)` | `ba` (`Y  X\Y → X`) | `beta_reduce(functor argument)`; functor is the **right** child |
| `D.unary(rule, cat, child, term=…)` | `lex` / `rp` / type-change | `term` (defaults to the child's term) |
| `D.combine(rule, cat, children, term)` | any | an explicitly supplied term |

Pass `eta=True` to `forward` / `backward` to `beta_eta_normalize` instead (collapses
eta-redexes such as a predicate lift `λy. F(y) → F`).

## Rendering

Three renderers mirror the toolkit's `to_unicode_str` / `to_latex` / `tree_str` split.

`to_text()` draws a Unicode "prooftree" — premises above an inference bar, the
combinator at the bar's right end, then the category over the lambda-term:

```python
print(sentence.to_text())
```

```text
              Some                    woman                ordered         tea
              NP/N                      N                 (S\NP)/NP         N
λG. λF. ∃x (((G)(x)) ∧ ((F)(x)))   λx. Woman(x)      λo. λx. Order(x, o)   tea
─────────────────────────────────────────────── fa   ───────────────────────── fa
                       NP                                       S\NP
          λF. ∃x (Woman(x) ∧ ((F)(x)))                   λx. Order(x, tea)
───────────────────────────────────────────────────────────────────────────────── fa
                                        S
                          ∃x (Woman(x) ∧ Order(x, tea))
```

`to_latex()` emits a `bussproofs` proof tree (add `\usepackage{bussproofs}`); each
term is rendered via `Node.to_latex`. `to_html()` returns a self-contained,
theme-aware HTML page in the ccg2lambda idiom (category red, lambda-term blue,
combinator at the bar) — write it to a file and open it in a browser:

```python
open("deriv.html", "w", encoding="utf-8").write(sentence.to_html())
```

## Visualizing a beta-reduction

`reduction_derivation` turns a reduction path into a `CCGDerivation` chain, so a plain
lambda reduction can be drawn with the same renderers — the original term on top, each
`β` step below, the normal form at the bottom:

```python
from unicode_fol_kit import reduction_derivation, MSFLParser

print(reduction_derivation(MSFLParser().parse("(λx. Human(x))(alice)")).to_text())
```

```text
(λx. Human(x))(alice)
───────────────────── β
     Human(alice)
```

## Notes

- `CCGDerivation` is a frozen, hashable dataclass; the semantics is checked against the
  toolkit's `beta_reduce`, so a composed node's term is the genuine reduced meaning,
  not a label.
- `to_latex` supports 1–5 premises per step (bussproofs `UnaryInfC` … `QuinaryInfC`);
  a step with more children raises `ValueError` — use `to_text` / `to_html` instead.
- CCG *parsing* (word → category → derivation) is out of scope: you supply the
  categories and combinator structure; the toolkit composes and renders the semantics.
```
